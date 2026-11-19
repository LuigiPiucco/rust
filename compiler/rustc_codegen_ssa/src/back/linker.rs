use std::ffi::{OsStr, OsString};
use std::fs::{self, File};
use std::io::prelude::*;
use std::path::{Path, PathBuf};
use std::{env, iter, mem, str};

use find_msvc_tools;
use rustc_attr_ir::WindowsSubsystemKind;
use rustc_hir::def_id::{CrateNum, LOCAL_CRATE};
use rustc_middle::middle::dependency_format::Linkage;
use rustc_middle::middle::exported_symbols::{
    self, ExportedSymbol, SymbolExportInfo, SymbolExportKind, SymbolExportLevel,
};
use rustc_middle::ty::{SymbolName, TyCtxt};
use rustc_session::Session;
use rustc_session::config::{self, DebugInfo, LinkerPluginLto, Lto, OptLevel, Strip};
use rustc_span::bug;
use rustc_structures::CrateType;
use rustc_target::spec::{Arch, Cc, CfgAbi, LinkOutputKind, LinkerFlavor, Lld, Os};
use tracing::{debug, warn};

use super::command::Command;
use super::symbol_export;
use crate::back::link::{
    find_native_static_library, try_find_native_dynamic_library, try_find_native_static_library,
};
use crate::back::symbol_export::allocator_shim_symbols;
use crate::base::needs_allocator_shim_for_linking;
use crate::{SymbolExport, diagnostics};

#[cfg(test)]
mod tests;

/// Disables non-English messages from localized linkers.
/// Such messages may cause issues with text encoding on Windows (#35785)
/// and prevent inspection of linker output in case of errors, which we occasionally do.
/// This should be acceptable because other messages from rustc are in English anyway,
/// and may also be desirable to improve searchability of the linker diagnostics.
pub(crate) fn disable_localization(linker: &mut Command) {
    // No harm in setting both env vars simultaneously.
    // Unix-style linkers.
    linker.env("LC_ALL", "C");
    // MSVC's `link.exe`.
    linker.env("VSLANG", "1033");
}

/// The third parameter is for env vars, used on windows to set up the
/// path for MSVC to find its DLLs, and gcc to find its bundled
/// toolchain
pub(crate) fn get_linker<'a>(
    sess: &'a Session,
    linker: &Path,
    flavor: LinkerFlavor,
    self_contained: bool,
    target_cpu: &'a str,
    codegen_backend: &'static str,
) -> Box<dyn Linker + 'a> {
    let msvc_tool = find_msvc_tools::find_tool(sess.target.arch.desc(), "link.exe");

    // If our linker looks like a batch script on Windows then to execute this
    // we'll need to spawn `cmd` explicitly. This is primarily done to handle
    // emscripten where the linker is `emcc.bat` and needs to be spawned as
    // `cmd /c emcc.bat ...`.
    //
    // This worked historically but is needed manually since #42436 (regression
    // was tagged as #42791) and some more info can be found on #44443 for
    // emscripten itself.
    let mut cmd = match linker.to_str() {
        Some(linker) if cfg!(windows) && linker.ends_with(".bat") => Command::bat_script(linker),
        _ => match flavor {
            LinkerFlavor::Gnu(Cc::No, Lld::Yes)
            | LinkerFlavor::Darwin(Cc::No, Lld::Yes)
            | LinkerFlavor::WasmLld(Cc::No)
            | LinkerFlavor::Msvc(Lld::Yes) => Command::lld(linker, flavor.lld_flavor()),
            LinkerFlavor::Msvc(Lld::No)
                if sess.opts.cg.linker.is_none() && sess.target.linker.is_none() =>
            {
                Command::new(msvc_tool.as_ref().map_or(linker, |t| t.path()))
            }
            _ => Command::new(linker),
        },
    };

    // UWP apps have API restrictions enforced during Store submissions.
    // To comply with the Windows App Certification Kit,
    // MSVC needs to link with the Store versions of the runtime libraries (vcruntime, msvcrt, etc).
    let t = &sess.target;
    if matches!(flavor, LinkerFlavor::Msvc(..)) && t.cfg_abi == CfgAbi::Uwp {
        if let Some(ref tool) = msvc_tool {
            let original_path = tool.path();
            if let Some(root_lib_path) = original_path.ancestors().nth(4) {
                let arch = match t.arch {
                    Arch::X86_64 => Some("x64"),
                    Arch::X86 => Some("x86"),
                    Arch::AArch64 => Some("arm64"),
                    Arch::Arm => Some("arm"),
                    _ => None,
                };
                if let Some(ref a) = arch {
                    // FIXME: Move this to `fn linker_with_args`.
                    let mut arg = OsString::from("/LIBPATH:");
                    arg.push(format!("{}\\lib\\{}\\store", root_lib_path.display(), a));
                    cmd.arg(&arg);
                } else {
                    warn!("arch is not supported");
                }
            } else {
                warn!("MSVC root path lib location not found");
            }
        } else {
            warn!("link.exe not found");
        }
    }

    // The compiler's sysroot often has some bundled tools, so add it to the
    // PATH for the child.
    let mut new_path = sess.get_tools_search_paths(self_contained);
    let mut msvc_changed_path = false;
    if sess.target.is_like_msvc
        && let Some(ref tool) = msvc_tool
    {
        for (k, v) in tool.env() {
            if k == "PATH" {
                new_path.extend(env::split_paths(v));
                msvc_changed_path = true;
            } else {
                cmd.env(k, v);
            }
        }
    }

    if !msvc_changed_path && let Some(path) = env::var_os("PATH") {
        new_path.extend(env::split_paths(&path));
    }
    cmd.env("PATH", env::join_paths(new_path).unwrap());

    // FIXME: Move `/LIBPATH` addition for uwp targets from the linker construction
    // to the linker args construction.
    assert!(cmd.get_args().is_empty() || sess.target.cfg_abi == CfgAbi::Uwp);
    match flavor {
        LinkerFlavor::Unix(Cc::No) if sess.target.os == Os::Aix => {
            Box::new(AixLinker::new(cmd, sess)) as Box<dyn Linker>
        }
        LinkerFlavor::WasmLld(Cc::No) => Box::new(WasmLd::new(cmd, sess)) as Box<dyn Linker>,
        LinkerFlavor::Gnu(cc, _)
        | LinkerFlavor::Darwin(cc, _)
        | LinkerFlavor::WasmLld(cc)
        | LinkerFlavor::Unix(cc) => Box::new(GccLinker {
            cmd,
            sess,
            target_cpu,
            hinted_static: None,
            is_ld: cc == Cc::No,
            is_gnu: flavor.is_gnu(),
            uses_lld: flavor.uses_lld(),
            codegen_backend,
        }) as Box<dyn Linker>,
        LinkerFlavor::Msvc(..) => Box::new(MsvcLinker { cmd, sess }) as Box<dyn Linker>,
        LinkerFlavor::EmCc => Box::new(EmLinker { cmd, sess }) as Box<dyn Linker>,
        LinkerFlavor::Bpf => Box::new(BpfLinker { cmd, sess }) as Box<dyn Linker>,
        LinkerFlavor::Llbc => Box::new(LlbcLinker { cmd, sess }) as Box<dyn Linker>,
    }
}

// Note: Ideally neither these helper function, nor the macro-generated inherent methods below
// would exist, and these functions would live in `trait Linker`.
// Unfortunately, adding these functions to `trait Linker` make it `dyn`-incompatible.
// If the methods are added to the trait with `where Self: Sized` bounds, then even a separate
// implementation of them for `dyn Linker {}` wouldn't work due to a conflict with those
// uncallable methods in the trait.

/// Just pass the arguments to the linker as is.
/// It is assumed that they are correctly prepared in advance.
fn verbatim_args<L: Linker + ?Sized>(
    l: &mut L,
    args: impl IntoIterator<Item: AsRef<OsStr>>,
) -> &mut L {
    for arg in args {
        l.cmd().arg(arg);
    }
    l
}
/// Add underlying linker arguments to C compiler command, by wrapping them in
/// `-Wl` or `-Xlinker`.
fn convert_link_args_to_cc_args(cmd: &mut Command, args: impl IntoIterator<Item: AsRef<OsStr>>) {
    let mut combined_arg = OsString::from("-Wl");
    for arg in args {
        // If the argument itself contains a comma, we need to emit it
        // as `-Xlinker`, otherwise we can use `-Wl`.
        if arg.as_ref().as_encoded_bytes().contains(&b',') {
            // Emit current `-Wl` argument, if any has been built.
            if combined_arg != OsStr::new("-Wl") {
                cmd.arg(combined_arg);
                // Begin next `-Wl` argument.
                combined_arg = OsString::from("-Wl");
            }

            // Emit `-Xlinker` argument.
            cmd.arg("-Xlinker");
            cmd.arg(arg);
        } else {
            // Append to `-Wl` argument.
            combined_arg.push(",");
            combined_arg.push(arg);
        }
    }
    // Emit final `-Wl` argument.
    if combined_arg != OsStr::new("-Wl") {
        cmd.arg(combined_arg);
    }
}
/// Arguments for the underlying linker.
/// Add options to pass them through cc wrapper if `Linker` is a cc wrapper.
fn link_args<L: Linker + ?Sized>(l: &mut L, args: impl IntoIterator<Item: AsRef<OsStr>>) -> &mut L {
    if !l.is_cc() {
        verbatim_args(l, args);
    } else {
        convert_link_args_to_cc_args(l.cmd(), args);
    }
    l
}
/// Arguments for the cc wrapper specifically.
/// Check that it's indeed a cc wrapper and pass verbatim.
fn cc_args<L: Linker + ?Sized>(l: &mut L, args: impl IntoIterator<Item: AsRef<OsStr>>) -> &mut L {
    assert!(l.is_cc());
    verbatim_args(l, args)
}
/// Arguments supported by both underlying linker and cc wrapper, pass verbatim.
fn link_or_cc_args<L: Linker + ?Sized>(
    l: &mut L,
    args: impl IntoIterator<Item: AsRef<OsStr>>,
) -> &mut L {
    verbatim_args(l, args)
}

macro_rules! generate_arg_methods {
    ($($ty:ty)*) => { $(
        impl $ty {
            #[allow(unused)]
            pub(crate) fn verbatim_args(&mut self, args: impl IntoIterator<Item: AsRef<OsStr>>) -> &mut Self {
                verbatim_args(self, args)
            }
            #[allow(unused)]
            pub(crate) fn verbatim_arg(&mut self, arg: impl AsRef<OsStr>) -> &mut Self {
                verbatim_args(self, iter::once(arg))
            }
            #[allow(unused)]
            pub(crate) fn link_args(&mut self, args: impl IntoIterator<Item: AsRef<OsStr>>) -> &mut Self {
                link_args(self, args)
            }
            #[allow(unused)]
            pub(crate) fn link_arg(&mut self, arg: impl AsRef<OsStr>) -> &mut Self {
                link_args(self, iter::once(arg))
            }
            #[allow(unused)]
            pub(crate) fn cc_args(&mut self, args: impl IntoIterator<Item: AsRef<OsStr>>) -> &mut Self {
                cc_args(self, args)
            }
            #[allow(unused)]
            pub(crate) fn cc_arg(&mut self, arg: impl AsRef<OsStr>) -> &mut Self {
                cc_args(self, iter::once(arg))
            }
            #[allow(unused)]
            pub(crate) fn link_or_cc_args(&mut self, args: impl IntoIterator<Item: AsRef<OsStr>>) -> &mut Self {
                link_or_cc_args(self, args)
            }
            #[allow(unused)]
            pub(crate) fn link_or_cc_arg(&mut self, arg: impl AsRef<OsStr>) -> &mut Self {
                link_or_cc_args(self, iter::once(arg))
            }
        }
    )* }
}

generate_arg_methods! {
    GccLinker<'_>
    MsvcLinker<'_>
    EmLinker<'_>
    WasmLd<'_>
    AixLinker<'_>
    LlbcLinker<'_>
    BpfLinker<'_>
    dyn Linker + '_
}

/// Linker abstraction used by `back::link` to build up the command to invoke a
/// linker.
///
/// This trait is the total list of requirements needed by `back::link` and
/// represents the meaning of each option being passed down. This trait is then
/// used to dispatch on whether a GNU-like linker (generally `ld.exe`) or an
/// MSVC linker (e.g., `link.exe`) is being used.
pub(crate) trait Linker {
    fn cmd(&mut self) -> &mut Command;
    fn is_cc(&self) -> bool {
        false
    }
    fn set_output_kind(
        &mut self,
        output_kind: LinkOutputKind,
        crate_type: CrateType,
        out_filename: &Path,
    );
    fn link_dylib_by_name(&mut self, _name: &str, _verbatim: bool, _as_needed: bool) {
        bug!("dylib linked with unsupported linker")
    }
    fn link_dylib_by_path(&mut self, _path: &Path, _as_needed: bool) {
        bug!("dylib linked with unsupported linker")
    }
    fn link_framework_by_name(&mut self, _name: &str, _verbatim: bool, _as_needed: bool) {
        bug!("framework linked with unsupported linker")
    }
    fn link_staticlib_by_name(&mut self, name: &str, verbatim: bool, whole_archive: bool);
    fn link_staticlib_by_path(&mut self, path: &Path, whole_archive: bool);
    fn include_path(&mut self, path: &Path) {
        link_or_cc_args(link_or_cc_args(self, &["-L"]), &[path]);
    }
    fn framework_path(&mut self, _path: &Path) {
        bug!("framework path set with unsupported linker")
    }
    fn output_filename(&mut self, path: &Path) {
        link_or_cc_args(link_or_cc_args(self, &["-o"]), &[path]);
    }
    fn add_object(&mut self, path: &Path) {
        link_or_cc_args(self, &[path]);
    }
    fn gc_sections(&mut self, keep_metadata: bool);
    fn full_relro(&mut self);
    fn partial_relro(&mut self);
    fn no_relro(&mut self);
    fn optimize(&mut self);
    fn pgo_gen(&mut self);
    fn control_flow_guard(&mut self);
    fn ehcont_guard(&mut self);
    fn debuginfo(&mut self, strip: Strip, natvis_debugger_visualizers: &[PathBuf]);
    fn no_crt_objects(&mut self);
    fn no_default_libraries(&mut self);
    fn export_symbols(&mut self, tmpdir: &Path, crate_type: CrateType, symbols: &[SymbolExport]);
    fn windows_subsystem(&mut self, subsystem: WindowsSubsystemKind);
    fn linker_plugin_lto(&mut self);
    fn add_eh_frame_header(&mut self) {}
    fn add_no_exec(&mut self) {}
    fn add_as_needed(&mut self) {}
    fn reset_per_library_state(&mut self) {}
    fn enable_profiling(&mut self) {}
}

impl dyn Linker + '_ {
    pub(crate) fn take_cmd(&mut self) -> Command {
        mem::replace(self.cmd(), Command::new(""))
    }
}

struct GccLinker<'a> {
    cmd: Command,
    sess: &'a Session,
    target_cpu: &'a str,
    hinted_static: Option<bool>, // Keeps track of the current hinting mode.
    // Link as ld
    is_ld: bool,
    is_gnu: bool,
    uses_lld: bool,
    codegen_backend: &'static str,
}

impl<'a> GccLinker<'a> {
    fn takes_hints(&self) -> bool {
        // Really this function only returns true if the underlying linker
        // configured for a compiler is binutils `ld.bfd` and `ld.gold`. We
        // don't really have a foolproof way to detect that, so rule out some
        // platforms where currently this is guaranteed to *not* be the case:
        //
        // * On OSX they have their own linker, not binutils'
        // * For WebAssembly the only functional linker is LLD, which doesn't
        //   support hint flags
        !self.sess.target.is_like_darwin && !self.sess.target.is_like_wasm
    }

    // Some platforms take hints about whether a library is static or dynamic.
    // For those that support this, we ensure we pass the option if the library
    // was flagged "static" (most defaults are dynamic) to ensure that if
    // libfoo.a and libfoo.so both exist that the right one is chosen.
    fn hint_static(&mut self) {
        if !self.takes_hints() {
            return;
        }
        if self.hinted_static != Some(true) {
            self.link_arg("-Bstatic");
            self.hinted_static = Some(true);
        }
    }

    fn hint_dynamic(&mut self) {
        if !self.takes_hints() {
            return;
        }
        if self.hinted_static != Some(false) {
            self.link_arg("-Bdynamic");
            self.hinted_static = Some(false);
        }
    }

    fn push_linker_plugin_lto_args(&mut self, plugin_path: Option<&OsStr>) {
        if let Some(plugin_path) = plugin_path {
            let mut arg = OsString::from("-plugin=");
            arg.push(plugin_path);
            self.link_arg(&arg);
        }

        // The plugin has no distinct size setting: `s` and `z` both map to `O2`, as `More` does.
        let opt_level = match self.sess.opts.optimize {
            config::OptLevel::No => "O0",
            config::OptLevel::Less => "O1",
            config::OptLevel::More | config::OptLevel::Size | config::OptLevel::SizeMin => "O2",
            config::OptLevel::Aggressive => "O3",
        };

        if let Some(path) = &self.sess.opts.cg.profile_sample_use {
            self.link_arg(&format!("-plugin-opt=sample-profile={}", path.display()));
        };
        let prefix = if self.codegen_backend == "gcc" {
            // The GCC linker plugin requires a leading dash.
            "-"
        } else {
            ""
        };
        self.link_args(&[
            &format!("-plugin-opt={prefix}{opt_level}"),
            &format!("-plugin-opt={prefix}mcpu={}", self.target_cpu),
        ]);
    }

    fn build_dylib(&mut self, crate_type: CrateType, out_filename: &Path) {
        // On mac we need to tell the linker to let this library be rpathed
        if self.sess.target.is_like_darwin {
            if self.is_cc() {
                // `-dynamiclib` makes `cc` pass `-dylib` to the linker.
                self.cc_arg("-dynamiclib");
            } else {
                self.link_arg("-dylib");
                // Clang also sets `-dynamic`, but that's implied by `-dylib`, so unnecessary.
            }

            // Note that the `osx_rpath_install_name` option here is a hack
            // purely to support bootstrap right now, we should get a more
            // principled solution at some point to force the compiler to pass
            // the right `-Wl,-install_name` with an `@rpath` in it.
            if self.sess.opts.cg.rpath || self.sess.opts.unstable_opts.osx_rpath_install_name {
                let mut rpath = OsString::from("@rpath/");
                rpath.push(out_filename.file_name().unwrap());
                self.link_arg("-install_name").link_arg(rpath);
            }
        } else {
            self.link_or_cc_arg("-shared");
            if let Some(name) = out_filename.file_name() {
                if self.sess.target.is_like_windows {
                    // The output filename already contains `dll_suffix` so
                    // the resulting import library will have a name in the
                    // form of libfoo.dll.a
                    let (prefix, suffix) = self.sess.staticlib_components(false);
                    let mut implib_name = OsString::from(prefix);
                    implib_name.push(name);
                    implib_name.push(suffix);
                    let mut out_implib = OsString::from("--out-implib=");
                    out_implib.push(out_filename.with_file_name(implib_name));
                    self.link_arg(out_implib);
                } else if crate_type == CrateType::Dylib {
                    // When dylibs are linked by a full path this value will get into `DT_NEEDED`
                    // instead of the full path, so the library can be later found in some other
                    // location than that specific path.
                    let mut soname = OsString::from("-soname=");
                    soname.push(name);
                    self.link_arg(soname);
                }
            }
        }
    }

    fn with_as_needed(&mut self, as_needed: bool, f: impl FnOnce(&mut Self)) {
        if !as_needed {
            if self.sess.target.is_like_darwin {
                // FIXME(81490): ld64 doesn't support these flags but macOS 11
                // has -needed-l{} / -needed_library {}
                // but we have no way to detect that here.
                self.sess.dcx().emit_warn(diagnostics::Ld64UnimplementedModifier);
            } else if self.is_gnu && !self.sess.target.is_like_windows {
                self.link_arg("--no-as-needed");
            } else {
                self.sess.dcx().emit_warn(diagnostics::LinkerUnsupportedModifier);
            }
        }

        f(self);

        if !as_needed {
            if self.sess.target.is_like_darwin {
                // See above FIXME comment
            } else if self.is_gnu && !self.sess.target.is_like_windows {
                self.link_arg("--as-needed");
            }
        }
    }
}

impl<'a> Linker for GccLinker<'a> {
    fn cmd(&mut self) -> &mut Command {
        &mut self.cmd
    }

    fn is_cc(&self) -> bool {
        !self.is_ld
    }

    fn set_output_kind(
        &mut self,
        output_kind: LinkOutputKind,
        crate_type: CrateType,
        out_filename: &Path,
    ) {
        match output_kind {
            LinkOutputKind::DynamicNoPicExe => {
                // noop on windows w/ gcc, warning w/ clang
                if !self.is_ld && self.is_gnu && !self.sess.target.is_like_windows {
                    self.cc_arg("-no-pie");
                }
            }
            LinkOutputKind::DynamicPicExe => {
                // noop on windows w/ gcc & ld, error w/ lld
                if !self.sess.target.is_like_windows {
                    // `-pie` works for both gcc wrapper and ld.
                    self.link_or_cc_arg("-pie");
                }
            }
            LinkOutputKind::StaticNoPicExe => {
                // `-static` works for both gcc wrapper and ld.
                self.link_or_cc_arg("-static");
                // noop on windows w/ gcc, warning w/ clang
                if !self.is_ld && self.is_gnu && !self.sess.target.is_like_windows {
                    self.cc_arg("-no-pie");
                }
            }
            LinkOutputKind::StaticPicExe => {
                if !self.is_ld {
                    // Note that combination `-static -pie` doesn't work as expected
                    // for the gcc wrapper, `-static` in that case suppresses `-pie`.
                    self.cc_arg("-static-pie");
                } else {
                    // `--no-dynamic-linker` and `-z text` are not strictly necessary for producing
                    // a static pie, but currently passed because gcc and clang pass them.
                    // The former suppresses the `INTERP` ELF header specifying dynamic linker,
                    // which is otherwise implicitly injected by ld (but not lld).
                    // The latter doesn't change anything, only ensures that everything is pic.
                    self.link_args(&["-static", "-pie", "--no-dynamic-linker", "-z", "text"]);
                }
            }
            LinkOutputKind::DynamicDylib => self.build_dylib(crate_type, out_filename),
            LinkOutputKind::StaticDylib => {
                self.link_or_cc_arg("-static");
                self.build_dylib(crate_type, out_filename);
            }
            LinkOutputKind::WasiReactorExe => {
                self.link_args(&["--entry", "_initialize"]);
            }
        }

        // VxWorks compiler driver introduced `--static-crt` flag specifically for rustc,
        // it switches linking for libc and similar system libraries to static without using
        // any `#[link]` attributes in the `libc` crate, see #72782 for details.
        // FIXME: Switch to using `#[link]` attributes in the `libc` crate
        // similarly to other targets.
        if self.sess.target.os == Os::VxWorks
            && matches!(
                output_kind,
                LinkOutputKind::StaticNoPicExe
                    | LinkOutputKind::StaticPicExe
                    | LinkOutputKind::StaticDylib
            )
        {
            self.cc_arg("--static-crt");
        }

        // avr-none doesn't have default ISA, users must specify which specific
        // CPU (well, microcontroller) they are targetting using `-Ctarget-cpu`.
        //
        // Currently this makes sense only when using avr-gcc as a linker, since
        // it brings a couple of hand-written important intrinsics from libgcc.
        //
        // For experimentation, avr-ld is also allowed and the MCU
        // names are translated to its ISA identifiers, but note this
        // is somewhat broken given the absence of some libgcc
        // intrinsics. Additionally, using avr-ld directly means
        // symbols and conventions added by GCC (__vector_N and ISR
        // constructs, __*_REGION_LENGTH__, initialization code and
        // bss clearing, ...) won’t exist.
        if self.sess.target.arch == Arch::Avr && !self.uses_lld {
            if self.is_cc() {
                self.verbatim_arg(format!("-mmcu={}", self.target_cpu));
            } else {
                let Some(arch) = avr_arch_from_mcu(self.target_cpu) else {
                    self.sess.dcx().emit_fatal(diagnostics::CpuUnsupported {
                        target_cpu: self.target_cpu.into(),
                    });
                };
                self.verbatim_arg(format!("-m{}", arch));
            }
        }
    }

    fn link_dylib_by_name(&mut self, name: &str, verbatim: bool, as_needed: bool) {
        if self.sess.target.os == Os::Illumos && name == "c" {
            // libc will be added via late_link_args on illumos so that it will
            // appear last in the library search order.
            // FIXME: This should be replaced by a more complete and generic
            // mechanism for controlling the order of library arguments passed
            // to the linker.
            return;
        }
        self.hint_dynamic();
        self.with_as_needed(as_needed, |this| {
            let colon = if verbatim && this.is_gnu { ":" } else { "" };
            this.link_or_cc_arg(format!("-l{colon}{name}"));
        });
    }

    fn link_dylib_by_path(&mut self, path: &Path, as_needed: bool) {
        self.hint_dynamic();
        self.with_as_needed(as_needed, |this| {
            this.link_or_cc_arg(path);
        })
    }

    fn link_framework_by_name(&mut self, name: &str, _verbatim: bool, as_needed: bool) {
        self.hint_dynamic();
        if !as_needed {
            // FIXME(81490): ld64 as of macOS 11 supports the -needed_framework
            // flag but we have no way to detect that here.
            // self.link_or_cc_arg("-needed_framework").link_or_cc_arg(name);
            self.sess.dcx().emit_warn(diagnostics::Ld64UnimplementedModifier);
        }
        self.link_or_cc_args(&["-framework", name]);
    }

    fn link_staticlib_by_name(&mut self, name: &str, verbatim: bool, whole_archive: bool) {
        self.hint_static();
        let colon = if verbatim && self.is_gnu { ":" } else { "" };
        if !whole_archive {
            self.link_or_cc_arg(format!("-l{colon}{name}"));
        } else if self.sess.target.is_like_darwin {
            // -force_load is the macOS equivalent of --whole-archive, but it
            // involves passing the full path to the library to link.
            self.link_arg("-force_load");
            self.link_arg(find_native_static_library(name, verbatim, self.sess));
        } else {
            self.link_arg("--whole-archive")
                .link_or_cc_arg(format!("-l{colon}{name}"))
                .link_arg("--no-whole-archive");
        }
    }

    fn link_staticlib_by_path(&mut self, path: &Path, whole_archive: bool) {
        self.hint_static();
        if !whole_archive {
            self.link_or_cc_arg(path);
        } else if self.sess.target.is_like_darwin {
            self.link_arg("-force_load").link_arg(path);
        } else {
            self.link_arg("--whole-archive").link_arg(path).link_arg("--no-whole-archive");
        }
    }

    fn framework_path(&mut self, path: &Path) {
        self.link_or_cc_arg("-F").link_or_cc_arg(path);
    }
    fn full_relro(&mut self) {
        self.link_args(&["-z", "relro", "-z", "now"]);
    }
    fn partial_relro(&mut self) {
        self.link_args(&["-z", "relro"]);
    }
    fn no_relro(&mut self) {
        self.link_args(&["-z", "norelro"]);
    }

    fn gc_sections(&mut self, keep_metadata: bool) {
        // The dead_strip option to the linker specifies that functions and data
        // unreachable by the entry point will be removed. This is quite useful
        // with Rust's compilation model of compiling libraries at a time into
        // one object file. For example, this brings hello world from 1.7MB to
        // 458K.
        //
        // Note that this is done for both executables and dynamic libraries. We
        // won't get much benefit from dylibs because LLVM will have already
        // stripped away as much as it could. This has not been seen to impact
        // link times negatively.
        //
        // -dead_strip can't be part of the pre_link_args because it's also used
        // for partial linking when using multiple codegen units (-r). So we
        // insert it here.
        if self.sess.target.is_like_darwin {
            self.link_arg("-dead_strip");

        // If we're building a dylib, we don't use --gc-sections because LLVM
        // has already done the best it can do, and we also don't want to
        // eliminate the metadata. If we're building an executable, however,
        // --gc-sections drops the size of hello world from 1.8MB to 597K, a 67%
        // reduction.
        } else if (self.is_gnu || self.sess.target.is_like_wasm) && !keep_metadata {
            self.link_arg("--gc-sections");
        }
    }

    fn optimize(&mut self) {
        if !self.is_gnu && !self.sess.target.is_like_wasm {
            return;
        }

        // GNU-style linkers support optimization with -O. GNU ld doesn't
        // need a numeric argument, but other linkers do.
        if self.sess.optimization_objective() == config::OptimizationObjective::Speed {
            self.link_arg("-O1");
        }
    }

    fn pgo_gen(&mut self) {
        if !self.is_gnu {
            return;
        }

        // If we're doing PGO generation stuff and on a GNU-like linker, use the
        // "-u" flag to properly pull in the profiler runtime bits.
        //
        // This is because LLVM otherwise won't add the needed initialization
        // for us on Linux (though the extra flag should be harmless if it
        // does).
        //
        // See https://reviews.llvm.org/D14033 and https://reviews.llvm.org/D14030.
        //
        // Though it may be worth to try to revert those changes upstream, since
        // the overhead of the initialization should be minor.
        self.link_or_cc_args(&["-u", "__llvm_profile_runtime"]);
    }

    fn enable_profiling(&mut self) {
        // This flag is also used when linking to choose target specific
        // libraries needed to enable profiling.
        if !self.is_ld {
            self.cc_arg("-pg");
            // On windows-gnu targets, libgmon also needs to be linked, and this
            // requires readding libraries to satisfy its dependencies.
            if self.sess.target.is_like_windows {
                self.cc_arg("-lgmon");
                self.cc_arg("-lkernel32");
                self.cc_arg("-lmsvcrt");
            }
        }
    }

    fn control_flow_guard(&mut self) {}

    fn ehcont_guard(&mut self) {}

    fn debuginfo(&mut self, strip: Strip, _: &[PathBuf]) {
        // MacOS linker doesn't support stripping symbols directly anymore.
        if self.sess.target.is_like_darwin {
            return;
        }

        match strip {
            Strip::None => {}
            Strip::Debuginfo => {
                // The illumos linker does not support --strip-debug although
                // it does support --strip-all as a compatibility alias for -s.
                // The --strip-debug case is handled by running an external
                // `strip` utility as a separate step after linking.
                if !self.sess.target.is_like_solaris {
                    self.link_arg("--strip-debug");
                }
            }
            Strip::Symbols => {
                self.link_arg("--strip-all");
            }
        }
        match self.sess.opts.unstable_opts.debuginfo_compression {
            config::DebugInfoCompression::None => {}
            config::DebugInfoCompression::Zlib => {
                self.link_arg("--compress-debug-sections=zlib");
            }
            config::DebugInfoCompression::Zstd => {
                self.link_arg("--compress-debug-sections=zstd");
            }
        }
    }

    fn no_crt_objects(&mut self) {
        if !self.is_ld {
            self.cc_arg("-nostartfiles");
        }
    }

    fn no_default_libraries(&mut self) {
        if !self.is_ld {
            self.cc_arg("-nodefaultlibs");
        }
    }

    fn export_symbols(&mut self, tmpdir: &Path, crate_type: CrateType, symbols: &[SymbolExport]) {
        // Symbol visibility in object files typically takes care of this.
        if crate_type == CrateType::Executable {
            let should_export_executable_symbols =
                self.sess.opts.unstable_opts.export_executable_symbols;
            if self.sess.target.override_export_symbols.is_none()
                && !should_export_executable_symbols
            {
                return;
            }
        }

        // We manually create a list of exported symbols to ensure we don't expose any more.
        // The object files have far more public symbols than we actually want to export,
        // so we hide them all here.

        if !self.sess.target.limit_rdylib_exports {
            return;
        }

        let path = tmpdir.join(if self.sess.target.is_like_windows { "list.def" } else { "list" });
        debug!("EXPORTED SYMBOLS:");

        if self.sess.target.is_like_darwin {
            // Write a plain, newline-separated list of symbols
            let res = try {
                let mut f = File::create_buffered(&path)?;
                for sym in symbols {
                    debug!("  _{}", sym.name);
                    writeln!(f, "_{}", sym.name)?;
                }
            };
            if let Err(error) = res {
                self.sess.dcx().emit_fatal(diagnostics::LibDefWriteFailure { error });
            }
            self.link_arg("-exported_symbols_list").link_arg(path);
        } else if self.sess.target.is_like_windows {
            let res = try {
                let mut f = File::create_buffered(&path)?;

                // .def file similar to MSVC one but without LIBRARY section
                // because LD doesn't like when it's empty
                writeln!(f, "EXPORTS")?;
                for symbol in symbols {
                    let kind_marker =
                        if symbol.kind == SymbolExportKind::Data { " DATA" } else { "" };
                    debug!("  _{}", symbol.name);
                    // Quote the name in case it's reserved by linker in some way
                    // (this accounts for names with dots in particular).
                    writeln!(f, "  \"{}\"{kind_marker}", symbol.name)?;
                }
            };
            if let Err(error) = res {
                self.sess.dcx().emit_fatal(diagnostics::LibDefWriteFailure { error });
            }
            self.link_arg(path);
        } else if self.sess.target.is_like_wasm {
            self.link_arg("--no-export-dynamic");
            for sym in symbols {
                self.link_arg("--export").link_arg(&sym.name);
            }
        } else if crate_type == CrateType::Executable && !self.sess.target.is_like_solaris {
            let res = try {
                let mut f = File::create_buffered(&path)?;
                writeln!(f, "{{")?;
                for sym in symbols {
                    debug!("{}", sym.name);
                    writeln!(f, "  {};", sym.name)?;
                }
                writeln!(f, "}};")?;
            };
            if let Err(error) = res {
                self.sess.dcx().emit_fatal(diagnostics::VersionScriptWriteFailure { error });
            }
            self.link_arg("--dynamic-list").link_arg(path);
        } else {
            // Write an LD version script
            let res = try {
                let mut f = File::create_buffered(&path)?;
                writeln!(f, "{{")?;
                if !symbols.is_empty() {
                    writeln!(f, "  global:")?;
                    for sym in symbols {
                        debug!("    {};", sym.name);
                        writeln!(f, "    {};", sym.name)?;
                    }
                }
                writeln!(f, "\n  local:\n    *;\n}};")?;
            };
            if let Err(error) = res {
                self.sess.dcx().emit_fatal(diagnostics::VersionScriptWriteFailure { error });
            }
            if self.sess.target.is_like_solaris {
                self.link_arg("-M").link_arg(path);
            } else {
                let mut arg = OsString::from("--version-script=");
                arg.push(path);
                self.link_arg(arg).link_arg("--no-undefined-version");
            }
        }
    }

    fn windows_subsystem(&mut self, subsystem: WindowsSubsystemKind) {
        self.link_args(&["--subsystem", subsystem.as_str()]);
    }

    fn reset_per_library_state(&mut self) {
        self.hint_dynamic(); // Reset to default before returning the composed command line.
    }

    fn linker_plugin_lto(&mut self) {
        match self.sess.opts.cg.linker_plugin_lto {
            LinkerPluginLto::Disabled => {
                // GCC, when used as a linker, will perform LTO even without -flto when it sees
                // object files with the GCC IR (which can happen when using rustc_codegen_gcc).
                // Since the std is compiled with -Cembed-bitcode=yes, any program using the std
                // will have the linker do LTO.
                // So, we disable this with -fno-lto when linker plugin LTO is not requested.
                if self.is_cc() && self.codegen_backend == "gcc" {
                    self.cc_arg("-fno-lto");
                }
            }
            LinkerPluginLto::LinkerPluginAuto => {
                self.push_linker_plugin_lto_args(None);
            }
            LinkerPluginLto::LinkerPlugin(ref path) => {
                self.push_linker_plugin_lto_args(Some(path.as_os_str()));
            }
        }
    }

    // Add the `GNU_EH_FRAME` program header which is required to locate unwinding information.
    // Some versions of `gcc` add it implicitly, some (e.g. `musl-gcc`) don't,
    // so we just always add it.
    fn add_eh_frame_header(&mut self) {
        self.link_arg("--eh-frame-hdr");
    }

    fn add_no_exec(&mut self) {
        if self.sess.target.is_like_windows {
            self.link_arg("--nxcompat");
        } else if self.is_gnu {
            self.link_args(&["-z", "noexecstack"]);
        }
    }

    fn add_as_needed(&mut self) {
        if self.is_gnu && !self.sess.target.is_like_windows {
            self.link_arg("--as-needed");
        } else if self.sess.target.is_like_solaris {
            // -z ignore is the Solaris equivalent to the GNU ld --as-needed option
            self.link_args(&["-z", "ignore"]);
        }
    }
}

struct MsvcLinker<'a> {
    cmd: Command,
    sess: &'a Session,
}

impl<'a> Linker for MsvcLinker<'a> {
    fn cmd(&mut self) -> &mut Command {
        &mut self.cmd
    }

    fn set_output_kind(
        &mut self,
        output_kind: LinkOutputKind,
        _crate_type: CrateType,
        out_filename: &Path,
    ) {
        match output_kind {
            LinkOutputKind::DynamicNoPicExe
            | LinkOutputKind::DynamicPicExe
            | LinkOutputKind::StaticNoPicExe
            | LinkOutputKind::StaticPicExe => {}
            LinkOutputKind::DynamicDylib | LinkOutputKind::StaticDylib => {
                self.link_arg("/DLL");
                let mut arg: OsString = "/IMPLIB:".into();
                arg.push(out_filename.with_extension("dll.lib"));
                self.link_arg(arg);
            }
            LinkOutputKind::WasiReactorExe => {
                panic!("can't link as reactor on non-wasi target");
            }
        }
    }

    fn link_dylib_by_name(&mut self, name: &str, verbatim: bool, _as_needed: bool) {
        // On MSVC-like targets rustc supports import libraries using alternative naming
        // scheme (`libfoo.a`) unsupported by linker, search for such libraries manually.
        if let Some(path) = try_find_native_dynamic_library(self.sess, name, verbatim) {
            self.link_arg(path);
        } else {
            self.link_arg(format!("{}{}", name, if verbatim { "" } else { ".lib" }));
        }
    }

    fn link_dylib_by_path(&mut self, path: &Path, _as_needed: bool) {
        // When producing a dll, MSVC linker may not emit an implib file if the dll doesn't export
        // any symbols, so we skip linking if the implib file is not present.
        let implib_path = path.with_extension("dll.lib");
        if implib_path.exists() {
            self.link_or_cc_arg(implib_path);
        }
    }

    fn link_staticlib_by_name(&mut self, name: &str, verbatim: bool, whole_archive: bool) {
        // On MSVC-like targets rustc supports static libraries using alternative naming
        // scheme (`libfoo.a`) unsupported by linker, search for such libraries manually.
        if let Some(path) = try_find_native_static_library(self.sess, name, verbatim) {
            self.link_staticlib_by_path(&path, whole_archive);
        } else {
            let opts = if whole_archive { "/WHOLEARCHIVE:" } else { "" };
            let (prefix, suffix) = self.sess.staticlib_components(verbatim);
            self.link_arg(format!("{opts}{prefix}{name}{suffix}"));
        }
    }

    fn link_staticlib_by_path(&mut self, path: &Path, whole_archive: bool) {
        if !whole_archive {
            self.link_arg(path);
        } else {
            let mut arg = OsString::from("/WHOLEARCHIVE:");
            arg.push(path);
            self.link_arg(arg);
        }
    }

    fn gc_sections(&mut self, _keep_metadata: bool) {
        // MSVC's ICF (Identical COMDAT Folding) link optimization is
        // slow for Rust and thus we disable it by default when not in
        // optimization build.
        if self.sess.optimization_objective() != config::OptimizationObjective::None {
            self.link_arg("/OPT:REF,ICF");
        } else {
            // It is necessary to specify NOICF here, because /OPT:REF
            // implies ICF by default.
            self.link_arg("/OPT:REF,NOICF");
        }
    }

    fn full_relro(&mut self) {
        // noop
    }

    fn partial_relro(&mut self) {
        // noop
    }

    fn no_relro(&mut self) {
        // noop
    }

    fn no_crt_objects(&mut self) {
        // noop
    }

    fn no_default_libraries(&mut self) {
        self.link_arg("/NODEFAULTLIB");
    }

    fn include_path(&mut self, path: &Path) {
        let mut arg = OsString::from("/LIBPATH:");
        arg.push(path);
        self.link_arg(&arg);
    }

    fn output_filename(&mut self, path: &Path) {
        let mut arg = OsString::from("/OUT:");
        arg.push(path);
        self.link_arg(&arg);
    }

    fn optimize(&mut self) {
        // Needs more investigation of `/OPT` arguments
    }

    fn pgo_gen(&mut self) {
        // Nothing needed here.
    }

    fn control_flow_guard(&mut self) {
        self.link_arg("/guard:cf");
    }

    fn ehcont_guard(&mut self) {
        if self.sess.target.pointer_width == 64 {
            self.link_arg("/guard:ehcont");
        }
    }

    fn debuginfo(&mut self, _strip: Strip, natvis_debugger_visualizers: &[PathBuf]) {
        // This will cause the Microsoft linker to generate a PDB file
        // from the CodeView line tables in the object files.
        self.link_arg("/DEBUG");

        // Default to emitting only the file name of the PDB file into
        // the binary instead of the full path. Emitting the full path
        // may leak private information (such as user names).
        // See https://github.com/rust-lang/rust/issues/87825.
        //
        // This default behavior can be overridden by explicitly passing
        // `-Clink-arg=/PDBALTPATH:...` to rustc.
        self.link_arg("/PDBALTPATH:%_PDB%");

        // This will cause the Microsoft linker to embed .natvis info into the PDB file
        let natvis_dir_path = self.sess.opts.sysroot.path().join("lib\\rustlib\\etc");
        if let Ok(natvis_dir) = fs::read_dir(&natvis_dir_path) {
            for entry in natvis_dir {
                match entry {
                    Ok(entry) => {
                        let path = entry.path();
                        if path.extension() == Some("natvis".as_ref()) {
                            let mut arg = OsString::from("/NATVIS:");
                            arg.push(path);
                            self.link_arg(arg);
                        }
                    }
                    Err(error) => {
                        self.sess.dcx().emit_warn(diagnostics::NoNatvisDirectory { error });
                    }
                }
            }
        }

        // This will cause the Microsoft linker to embed .natvis info for all crates into the PDB file
        for path in natvis_debugger_visualizers {
            let mut arg = OsString::from("/NATVIS:");
            arg.push(path);
            self.link_arg(arg);
        }
    }

    fn export_symbols(&mut self, tmpdir: &Path, crate_type: CrateType, _symbols: &[SymbolExport]) {
        // We already add /EXPORT arguments to the .drectve section of symbols.o.
        // Keep passing an empty .def file: link.exe otherwise skips the import
        // library for DLLs with no exports.
        if crate_type == CrateType::Executable {
            let should_export_executable_symbols =
                self.sess.opts.unstable_opts.export_executable_symbols;
            if !should_export_executable_symbols {
                return;
            }
        }

        let path = tmpdir.join("lib.def");
        let res = try {
            let mut f = File::create_buffered(&path)?;
            writeln!(f, "LIBRARY")?;
            writeln!(f, "EXPORTS")?;
        };
        if let Err(error) = res {
            self.sess.dcx().emit_fatal(diagnostics::LibDefWriteFailure { error });
        }
        let mut arg = OsString::from("/DEF:");
        arg.push(path);
        self.link_arg(&arg);
    }

    fn windows_subsystem(&mut self, subsystem: WindowsSubsystemKind) {
        let subsystem = subsystem.as_str();
        self.link_arg(&format!("/SUBSYSTEM:{subsystem}"));

        // Windows has two subsystems we're interested in right now, the console
        // and windows subsystems. These both implicitly have different entry
        // points (starting symbols). The console entry point starts with
        // `mainCRTStartup` and the windows entry point starts with
        // `WinMainCRTStartup`. These entry points, defined in system libraries,
        // will then later probe for either `main` or `WinMain`, respectively to
        // start the application.
        //
        // In Rust we just always generate a `main` function so we want control
        // to always start there, so we force the entry point on the windows
        // subsystem to be `mainCRTStartup` to get everything booted up
        // correctly.
        //
        // For more information see RFC #1665
        if subsystem == "windows" {
            self.link_arg("/ENTRY:mainCRTStartup");
        }
    }

    fn linker_plugin_lto(&mut self) {
        // Do nothing
    }

    fn add_no_exec(&mut self) {
        self.link_arg("/NXCOMPAT");
    }
}

struct EmLinker<'a> {
    cmd: Command,
    sess: &'a Session,
}

impl<'a> Linker for EmLinker<'a> {
    fn cmd(&mut self) -> &mut Command {
        &mut self.cmd
    }

    fn is_cc(&self) -> bool {
        true
    }

    fn set_output_kind(
        &mut self,
        output_kind: LinkOutputKind,
        _crate_type: CrateType,
        _out_filename: &Path,
    ) {
        match output_kind {
            LinkOutputKind::DynamicNoPicExe | LinkOutputKind::DynamicPicExe => {
                self.cmd.arg("-sMAIN_MODULE=2");
            }
            LinkOutputKind::DynamicDylib | LinkOutputKind::StaticDylib => {
                self.cmd.arg("-sSIDE_MODULE=2");
            }
            // -fno-pie is the default on Emscripten.
            LinkOutputKind::StaticNoPicExe | LinkOutputKind::StaticPicExe => {}
            LinkOutputKind::WasiReactorExe => {
                unreachable!();
            }
        }
    }

    fn link_dylib_by_name(&mut self, name: &str, _verbatim: bool, _as_needed: bool) {
        // Emscripten always links statically
        self.link_or_cc_args(&["-l", name]);
    }

    fn link_dylib_by_path(&mut self, path: &Path, _as_needed: bool) {
        self.link_or_cc_arg(path);
    }

    fn link_staticlib_by_name(&mut self, name: &str, _verbatim: bool, _whole_archive: bool) {
        self.link_or_cc_args(&["-l", name]);
    }

    fn link_staticlib_by_path(&mut self, path: &Path, _whole_archive: bool) {
        self.link_or_cc_arg(path);
    }

    fn full_relro(&mut self) {
        // noop
    }

    fn partial_relro(&mut self) {
        // noop
    }

    fn no_relro(&mut self) {
        // noop
    }

    fn gc_sections(&mut self, _keep_metadata: bool) {
        // noop
    }

    fn optimize(&mut self) {
        // Emscripten performs own optimizations
        self.cc_arg(match self.sess.opts.optimize {
            OptLevel::No => "-O0",
            OptLevel::Less => "-O1",
            OptLevel::More => "-O2",
            OptLevel::Aggressive => "-O3",
            OptLevel::Size => "-Os",
            OptLevel::SizeMin => "-Oz",
        });
    }

    fn pgo_gen(&mut self) {
        // noop, but maybe we need something like the gnu linker?
    }

    fn control_flow_guard(&mut self) {}

    fn ehcont_guard(&mut self) {}

    fn debuginfo(&mut self, _strip: Strip, _: &[PathBuf]) {
        // Preserve names or generate source maps depending on debug info
        // For more information see https://emscripten.org/docs/tools_reference/emcc.html#emcc-g
        self.cc_arg(match self.sess.opts.debuginfo {
            DebugInfo::None => "-g0",
            DebugInfo::Limited | DebugInfo::LineTablesOnly | DebugInfo::LineDirectivesOnly => {
                "--profiling-funcs"
            }
            DebugInfo::Full => "-g",
        });
    }

    fn no_crt_objects(&mut self) {}

    fn no_default_libraries(&mut self) {
        self.cc_arg("-nodefaultlibs");
    }

    fn export_symbols(&mut self, _tmpdir: &Path, _crate_type: CrateType, symbols: &[SymbolExport]) {
        debug!("EXPORTED SYMBOLS:");

        self.cc_arg("-s");

        // Emscripten exposes the program entry point under the JS name `_main`
        // regardless of the underlying wasm symbol (which is `__main_argc_argv`
        // per the wasm C ABI in the tool-conventions BasicCABI spec), bridging
        // the two internally. So the entry symbol must be requested as `_main`
        // here rather than as a `_`-prefixed form of its wasm name.
        let entry_name = self.sess.target.entry_name.as_ref();
        let mut arg = OsString::from("EXPORTED_FUNCTIONS=");
        let encoded = serde_json::to_string(
            &symbols
                .iter()
                .map(|sym| {
                    if sym.name == entry_name {
                        "_main".to_owned()
                    } else {
                        "_".to_owned() + &sym.name
                    }
                })
                .collect::<Vec<_>>(),
        )
        .unwrap();
        debug!("{encoded}");

        arg.push(encoded);

        self.cc_arg(arg);
    }

    fn windows_subsystem(&mut self, _subsystem: WindowsSubsystemKind) {
        // noop
    }

    fn linker_plugin_lto(&mut self) {
        // Do nothing
    }
}

struct WasmLd<'a> {
    cmd: Command,
    sess: &'a Session,
}

impl<'a> WasmLd<'a> {
    fn new(cmd: Command, sess: &'a Session) -> WasmLd<'a> {
        WasmLd { cmd, sess }
    }
}

impl<'a> Linker for WasmLd<'a> {
    fn cmd(&mut self) -> &mut Command {
        &mut self.cmd
    }

    fn set_output_kind(
        &mut self,
        output_kind: LinkOutputKind,
        _crate_type: CrateType,
        _out_filename: &Path,
    ) {
        match output_kind {
            LinkOutputKind::DynamicNoPicExe
            | LinkOutputKind::DynamicPicExe
            | LinkOutputKind::StaticNoPicExe
            | LinkOutputKind::StaticPicExe => {}
            LinkOutputKind::DynamicDylib | LinkOutputKind::StaticDylib => {
                self.link_arg("--no-entry");
            }
            LinkOutputKind::WasiReactorExe => {
                self.link_args(&["--entry", "_initialize"]);
            }
        }
    }

    fn link_dylib_by_name(&mut self, name: &str, _verbatim: bool, _as_needed: bool) {
        self.link_or_cc_args(&["-l", name]);
    }

    fn link_dylib_by_path(&mut self, path: &Path, _as_needed: bool) {
        self.link_or_cc_arg(path);
    }

    fn link_staticlib_by_name(&mut self, name: &str, _verbatim: bool, whole_archive: bool) {
        if !whole_archive {
            self.link_or_cc_args(&["-l", name]);
        } else {
            self.link_arg("--whole-archive")
                .link_or_cc_args(&["-l", name])
                .link_arg("--no-whole-archive");
        }
    }

    fn link_staticlib_by_path(&mut self, path: &Path, whole_archive: bool) {
        if !whole_archive {
            self.link_or_cc_arg(path);
        } else {
            self.link_arg("--whole-archive").link_or_cc_arg(path).link_arg("--no-whole-archive");
        }
    }

    fn full_relro(&mut self) {}

    fn partial_relro(&mut self) {}

    fn no_relro(&mut self) {}

    fn gc_sections(&mut self, _keep_metadata: bool) {
        self.link_arg("--gc-sections");
    }

    fn optimize(&mut self) {
        // The -O flag is, as of late 2023, only used for merging of strings and debuginfo, and
        // only differentiates -O0 and -O1. It does not apply to LTO.
        self.link_arg(match self.sess.opts.optimize {
            OptLevel::No => "-O0",
            OptLevel::Less => "-O1",
            OptLevel::More => "-O2",
            OptLevel::Aggressive => "-O3",
            // Currently LLD doesn't support `Os` and `Oz`, so pass through `O2`
            // instead.
            OptLevel::Size => "-O2",
            OptLevel::SizeMin => "-O2",
        });
    }

    fn pgo_gen(&mut self) {}

    fn debuginfo(&mut self, strip: Strip, _: &[PathBuf]) {
        match strip {
            Strip::None => {}
            Strip::Debuginfo => {
                self.link_arg("--strip-debug");
            }
            Strip::Symbols => {
                self.link_arg("--strip-all");
            }
        }
    }

    fn control_flow_guard(&mut self) {}

    fn ehcont_guard(&mut self) {}

    fn no_crt_objects(&mut self) {}

    fn no_default_libraries(&mut self) {}

    fn export_symbols(&mut self, _tmpdir: &Path, _crate_type: CrateType, symbols: &[SymbolExport]) {
        for sym in symbols {
            self.link_args(&["--export", &sym.name]);
        }
    }

    fn windows_subsystem(&mut self, _subsystem: WindowsSubsystemKind) {}

    fn linker_plugin_lto(&mut self) {
        match self.sess.opts.cg.linker_plugin_lto {
            LinkerPluginLto::Disabled => {
                // Nothing to do
            }
            LinkerPluginLto::LinkerPluginAuto => {
                self.push_linker_plugin_lto_args();
            }
            LinkerPluginLto::LinkerPlugin(_) => {
                self.push_linker_plugin_lto_args();
            }
        }
    }
}

impl<'a> WasmLd<'a> {
    fn push_linker_plugin_lto_args(&mut self) {
        let opt_level = match self.sess.opts.optimize {
            config::OptLevel::No => "O0",
            config::OptLevel::Less => "O1",
            config::OptLevel::More => "O2",
            config::OptLevel::Aggressive => "O3",
            // wasm-ld only handles integer LTO opt levels. Use O2
            config::OptLevel::Size | config::OptLevel::SizeMin => "O2",
        };
        self.link_arg(&format!("--lto-{opt_level}"));
    }
}

/// Linker for AIX.
struct AixLinker<'a> {
    cmd: Command,
    sess: &'a Session,
    hinted_static: Option<bool>,
}

impl<'a> AixLinker<'a> {
    fn new(cmd: Command, sess: &'a Session) -> AixLinker<'a> {
        AixLinker { cmd, sess, hinted_static: None }
    }

    fn hint_static(&mut self) {
        if self.hinted_static != Some(true) {
            self.link_arg("-bstatic");
            self.hinted_static = Some(true);
        }
    }

    fn hint_dynamic(&mut self) {
        if self.hinted_static != Some(false) {
            self.link_arg("-bdynamic");
            self.hinted_static = Some(false);
        }
    }

    fn build_dylib(&mut self, _out_filename: &Path) {
        self.link_args(&["-bM:SRE", "-bnoentry"]);
        // FIXME: Use CreateExportList utility to create export list
        // and remove -bexpfull.
        self.link_arg("-bexpfull");
    }
}

impl<'a> Linker for AixLinker<'a> {
    fn cmd(&mut self) -> &mut Command {
        &mut self.cmd
    }

    fn set_output_kind(
        &mut self,
        output_kind: LinkOutputKind,
        _crate_type: CrateType,
        out_filename: &Path,
    ) {
        match output_kind {
            LinkOutputKind::DynamicDylib => {
                self.hint_dynamic();
                self.build_dylib(out_filename);
            }
            LinkOutputKind::StaticDylib => {
                self.hint_static();
                self.build_dylib(out_filename);
            }
            _ => {}
        }
    }

    fn link_dylib_by_name(&mut self, name: &str, verbatim: bool, _as_needed: bool) {
        self.hint_dynamic();
        self.link_or_cc_arg(if verbatim { String::from(name) } else { format!("-l{name}") });
    }

    fn link_dylib_by_path(&mut self, path: &Path, _as_needed: bool) {
        self.hint_dynamic();
        self.link_or_cc_arg(path);
    }

    fn link_staticlib_by_name(&mut self, name: &str, verbatim: bool, whole_archive: bool) {
        self.hint_static();
        if !whole_archive {
            self.link_or_cc_arg(if verbatim { String::from(name) } else { format!("-l{name}") });
        } else {
            let mut arg = OsString::from("-bkeepfile:");
            arg.push(find_native_static_library(name, verbatim, self.sess));
            self.link_or_cc_arg(arg);
        }
    }

    fn link_staticlib_by_path(&mut self, path: &Path, whole_archive: bool) {
        self.hint_static();
        if !whole_archive {
            self.link_or_cc_arg(path);
        } else {
            let mut arg = OsString::from("-bkeepfile:");
            arg.push(path);
            self.link_arg(arg);
        }
    }

    fn full_relro(&mut self) {}

    fn partial_relro(&mut self) {}

    fn no_relro(&mut self) {}

    fn gc_sections(&mut self, _keep_metadata: bool) {
        self.link_arg("-bgc");
    }

    fn optimize(&mut self) {}

    fn pgo_gen(&mut self) {
        self.link_arg("-bdbg:namedsects:ss");
        self.link_arg("-u");
        self.link_arg("__llvm_profile_runtime");
    }

    fn control_flow_guard(&mut self) {}

    fn ehcont_guard(&mut self) {}

    fn debuginfo(&mut self, _: Strip, _: &[PathBuf]) {}

    fn no_crt_objects(&mut self) {}

    fn no_default_libraries(&mut self) {}

    fn export_symbols(&mut self, tmpdir: &Path, _crate_type: CrateType, symbols: &[SymbolExport]) {
        let path = tmpdir.join("list.exp");
        let res = try {
            let mut f = File::create_buffered(&path)?;
            // FIXME: use llvm-nm to generate export list.
            for symbol in symbols {
                debug!("  _{}", symbol.name);
                writeln!(f, "  {}", symbol.name)?;
            }
        };
        if let Err(e) = res {
            self.sess.dcx().fatal(format!("failed to write export file: {e}"));
        }
        self.link_arg(format!("-bE:{}", path.to_str().unwrap()));
    }

    fn windows_subsystem(&mut self, _subsystem: WindowsSubsystemKind) {}

    fn reset_per_library_state(&mut self) {
        self.hint_dynamic();
    }

    fn linker_plugin_lto(&mut self) {}

    fn add_eh_frame_header(&mut self) {}

    fn add_no_exec(&mut self) {}

    fn add_as_needed(&mut self) {}
}

fn for_each_exported_symbols_include_dep<'tcx>(
    tcx: TyCtxt<'tcx>,
    crate_type: CrateType,
    mut callback: impl FnMut(ExportedSymbol<'tcx>, SymbolExportInfo, CrateNum),
) {
    let formats = tcx.dependency_formats(());
    let deps = &formats[&crate_type];

    for (cnum, dep_format) in deps.iter_enumerated() {
        // For each dependency that we are linking to statically ...
        if *dep_format == Linkage::Static {
            for &(symbol, info) in tcx.exported_non_generic_symbols(cnum).iter() {
                callback(symbol, info, cnum);
            }
            for &(symbol, info) in tcx.exported_generic_symbols(cnum).iter() {
                callback(symbol, info, cnum);
            }
        }
    }
}

fn symbol_export_from_exported_symbol<'tcx>(
    tcx: TyCtxt<'tcx>,
    symbol: ExportedSymbol<'tcx>,
    kind: SymbolExportKind,
    cnum: CrateNum,
) -> SymbolExport {
    let name = symbol_export::exporting_symbol_name_for_instance_in_crate(tcx, symbol, cnum);
    let link_name =
        symbol_export::linking_symbol_name_for_instance_in_crate(tcx, symbol, kind, cnum);
    SymbolExport::with_link_name(name, kind, link_name)
}

fn symbol_export_from_raw_name(
    tcx: TyCtxt<'_>,
    name: String,
    kind: SymbolExportKind,
) -> SymbolExport {
    let symbol = ExportedSymbol::NoDefId(SymbolName::new(tcx, &name));
    let link_name =
        symbol_export::linking_symbol_name_for_instance_in_crate(tcx, symbol, kind, LOCAL_CRATE);
    SymbolExport::with_link_name(name, kind, link_name)
}

pub(crate) fn exported_symbols(tcx: TyCtxt<'_>, crate_type: CrateType) -> Vec<SymbolExport> {
    if let Some(ref exports) = tcx.sess.target.override_export_symbols {
        return exports
            .iter()
            .map(|name| {
                symbol_export_from_raw_name(
                    tcx,
                    name.to_string(),
                    // FIXME use the correct export kind for this symbol. override_export_symbols
                    // can't directly specify the SymbolExportKind as it is defined in rustc_middle
                    // which rustc_target can't depend on.
                    SymbolExportKind::Text,
                )
            })
            .collect();
    }

    let mut symbols = if let CrateType::ProcMacro = crate_type {
        exported_symbols_for_proc_macro_crate(tcx)
    } else {
        exported_symbols_for_non_proc_macro(tcx, crate_type)
    };

    // Preserve the metadata symbol to ensure the metadata section doesn't get removed by the
    // linker. On wasm however the metadata is put in a custom section, to which symbols can't
    // refer, so there is no metadata symbol there. Luckily custom sections are always preserved by
    // the linker.
    if (crate_type == CrateType::Dylib || crate_type == CrateType::ProcMacro)
        && !tcx.sess.target.is_like_wasm
    {
        let metadata_symbol_name = exported_symbols::metadata_symbol_name(tcx);
        symbols.push(symbol_export_from_raw_name(
            tcx,
            metadata_symbol_name,
            SymbolExportKind::Data,
        ));
    }

    symbols
}

fn exported_symbols_for_non_proc_macro(
    tcx: TyCtxt<'_>,
    crate_type: CrateType,
) -> Vec<SymbolExport> {
    let mut symbols = Vec::new();
    let export_threshold = symbol_export::crates_export_threshold(&[crate_type]);
    for_each_exported_symbols_include_dep(tcx, crate_type, |symbol, info, cnum| {
        // Do not export mangled symbols from cdylibs and don't attempt to export compiler-builtins
        // from any dylib. The latter doesn't work anyway as we use hidden visibility for
        // compiler-builtins. Most linkers silently ignore it, but ld64 gives a warning.
        if info.level.is_below_threshold(export_threshold) && !tcx.is_compiler_builtins(cnum) {
            symbols.push(symbol_export_from_exported_symbol(tcx, symbol, info.kind, cnum));
            symbol_export::extend_exported_symbols(&mut symbols, tcx, symbol, cnum);
        }
    });

    // Mark allocator shim symbols as exported only if they were generated.
    if export_threshold == SymbolExportLevel::Rust
        && needs_allocator_shim_for_linking(tcx.dependency_formats(()), crate_type)
        && let Some(kind) = tcx.allocator_kind(())
    {
        symbols.extend(
            allocator_shim_symbols(tcx, kind)
                .map(|(name, kind)| symbol_export_from_raw_name(tcx, name, kind)),
        );
    }

    symbols
}

fn exported_symbols_for_proc_macro_crate(tcx: TyCtxt<'_>) -> Vec<SymbolExport> {
    // `exported_symbols` will be empty when !should_codegen.
    if !tcx.sess.opts.output_types.should_codegen() {
        return Vec::new();
    }

    let stable_crate_id = tcx.stable_crate_id(LOCAL_CRATE);
    let proc_macro_decls_name = rustc_session::generate_proc_macro_decls_symbol(stable_crate_id);

    vec![symbol_export_from_raw_name(tcx, proc_macro_decls_name, SymbolExportKind::Data)]
}

pub(crate) fn linked_symbols(
    tcx: TyCtxt<'_>,
    crate_type: CrateType,
) -> Vec<(String, SymbolExportKind)> {
    match crate_type {
        CrateType::Executable
        | CrateType::ProcMacro
        | CrateType::Cdylib
        | CrateType::Dylib
        | CrateType::Sdylib => (),
        CrateType::StaticLib | CrateType::Rlib => {
            // These are not linked, so no need to generate symbols.o for them.
            return Vec::new();
        }
    }

    match tcx.sess.lto() {
        Lto::No | Lto::ThinLocal => {}
        Lto::Thin | Lto::Fat => {
            // We really only need symbols from upstream rlibs to end up in the linked symbols list.
            // The rest are in separate object files which the linker will always link in and
            // doesn't have rules around the order in which they need to appear.
            // When doing LTO, some of the symbols in the linked symbols list happen to be
            // internalized by LTO, which then prevents referencing them from symbols.o. When doing
            // LTO, all object files that get linked in will be local object files rather than
            // pulled in from rlibs, so an empty linked symbols list works fine to avoid referencing
            // all those internalized symbols from symbols.o.
            return Vec::new();
        }
    }

    let mut symbols = Vec::new();

    let export_threshold = symbol_export::crates_export_threshold(&[crate_type]);
    for_each_exported_symbols_include_dep(tcx, crate_type, |symbol, info, cnum| {
        if info.level.is_below_threshold(export_threshold) && !tcx.is_compiler_builtins(cnum)
            || info.used
            || info.rustc_std_internal_symbol
        {
            symbols.push((
                symbol_export::linking_symbol_name_for_instance_in_crate(
                    tcx, symbol, info.kind, cnum,
                ),
                info.kind,
            ));
        }
    });

    symbols
}

/// The `self-contained` LLVM bitcode linker
struct LlbcLinker<'a> {
    cmd: Command,
    sess: &'a Session,
}

impl<'a> Linker for LlbcLinker<'a> {
    fn cmd(&mut self) -> &mut Command {
        &mut self.cmd
    }

    fn set_output_kind(
        &mut self,
        _output_kind: LinkOutputKind,
        _crate_type: CrateType,
        _out_filename: &Path,
    ) {
    }

    fn link_staticlib_by_name(&mut self, _name: &str, _verbatim: bool, _whole_archive: bool) {
        panic!("staticlibs not supported")
    }

    fn link_staticlib_by_path(&mut self, path: &Path, _whole_archive: bool) {
        self.link_or_cc_arg(path);
    }

    fn debuginfo(&mut self, strip: Strip, _: &[PathBuf]) {
        match strip {
            Strip::None => {
                self.link_arg("--debug");
            }
            Strip::Debuginfo | Strip::Symbols => {}
        }
    }

    fn optimize(&mut self) {
        self.link_arg(match self.sess.opts.optimize {
            OptLevel::No => "-O0",
            OptLevel::Less => "-O1",
            OptLevel::More => "-O2",
            OptLevel::Aggressive => "-O3",
            OptLevel::Size => "-Os",
            OptLevel::SizeMin => "-Oz",
        });
    }

    fn full_relro(&mut self) {}

    fn partial_relro(&mut self) {}

    fn no_relro(&mut self) {}

    fn gc_sections(&mut self, _keep_metadata: bool) {}

    fn pgo_gen(&mut self) {}

    fn no_crt_objects(&mut self) {}

    fn no_default_libraries(&mut self) {}

    fn control_flow_guard(&mut self) {}

    fn ehcont_guard(&mut self) {}

    fn export_symbols(&mut self, _tmpdir: &Path, _crate_type: CrateType, symbols: &[SymbolExport]) {
        match _crate_type {
            CrateType::Cdylib => {
                for sym in symbols {
                    self.link_args(&["--export-symbol", &sym.name]);
                }
            }
            _ => (),
        }
    }

    fn windows_subsystem(&mut self, _subsystem: WindowsSubsystemKind) {}

    fn linker_plugin_lto(&mut self) {}
}

struct BpfLinker<'a> {
    cmd: Command,
    sess: &'a Session,
}

impl<'a> Linker for BpfLinker<'a> {
    fn cmd(&mut self) -> &mut Command {
        &mut self.cmd
    }

    fn set_output_kind(
        &mut self,
        _output_kind: LinkOutputKind,
        _crate_type: CrateType,
        _out_filename: &Path,
    ) {
    }

    fn link_staticlib_by_name(&mut self, _name: &str, _verbatim: bool, _whole_archive: bool) {
        self.sess.dcx().emit_fatal(diagnostics::BpfStaticlibNotSupported)
    }

    fn link_staticlib_by_path(&mut self, path: &Path, _whole_archive: bool) {
        self.link_or_cc_arg(path);
    }

    fn debuginfo(&mut self, _strip: Strip, _: &[PathBuf]) {
        self.link_arg("--debug");
    }

    fn optimize(&mut self) {
        self.link_arg(match self.sess.opts.optimize {
            OptLevel::No => "-O0",
            OptLevel::Less => "-O1",
            OptLevel::More => "-O2",
            OptLevel::Aggressive => "-O3",
            OptLevel::Size => "-Os",
            OptLevel::SizeMin => "-Oz",
        });
    }

    fn full_relro(&mut self) {}

    fn partial_relro(&mut self) {}

    fn no_relro(&mut self) {}

    fn gc_sections(&mut self, _keep_metadata: bool) {}

    fn pgo_gen(&mut self) {}

    fn no_crt_objects(&mut self) {}

    fn no_default_libraries(&mut self) {}

    fn control_flow_guard(&mut self) {}

    fn ehcont_guard(&mut self) {}

    fn export_symbols(&mut self, tmpdir: &Path, _crate_type: CrateType, symbols: &[SymbolExport]) {
        let path = tmpdir.join("symbols");
        let res = try {
            let mut f = File::create_buffered(&path)?;
            for sym in symbols {
                writeln!(f, "{}", sym.name)?;
            }
        };
        if let Err(error) = res {
            self.sess.dcx().emit_fatal(diagnostics::SymbolFileWriteFailure { error });
        } else {
            self.link_arg("--export-symbols").link_arg(&path);
        }
    }

    fn windows_subsystem(&mut self, _subsystem: WindowsSubsystemKind) {}

    fn linker_plugin_lto(&mut self) {}
}

fn avr_arch_from_mcu(mcu: &'_ str) -> Option<&'static str> {
    // Assembler only.
    const AVR1: &'static str = "avr1";
    // Classic, <= 8K.
    const AVR2: &'static str = "avr2";
    // Classic + MOVW, <= 8K.
    const AVR25: &'static str = "avr25";
    // Classic, > 8K, <= 64K.
    const AVR3: &'static str = "avr3";
    // Classic, == 128K.
    const AVR31: &'static str = "avr31";
    // Classic + MOVW + JMP/CALL.
    const AVR35: &'static str = "avr35";
    // Enhanced, <= 8K.
    const AVR4: &'static str = "avr4";
    // Enhanced, > 8K, <= 64K.
    const AVR5: &'static str = "avr5";
    // Enhanced, == 128K.
    const AVR51: &'static str = "avr51";
    // 3-Byte PC.
    const AVR6: &'static str = "avr6";
    // Xmega, 16K <= Flash <= 64K, RAM <= 64K.
    const AVRXMEGA2: &'static str = "avrxmega2";
    // Xmega, Flash + RAM < 64K, flash visible in RAM address space */
    const AVRXMEGA3: &'static str = "avrxmega3";
    // Xmega, 64K < Flash <= 128K, RAM <= 64K.
    const AVRXMEGA4: &'static str = "avrxmega4";
    // Xmega, 64K < Flash <= 128K, RAM > 64K.
    const AVRXMEGA5: &'static str = "avrxmega5";
    // Xmega, 128K < Flash, RAM <= 64K.
    const AVRXMEGA6: &'static str = "avrxmega6";
    // Xmega, 128K < Flash, RAM > 64K RAM.
    const AVRXMEGA7: &'static str = "avrxmega7";
    // Tiny family.
    const AVRTINY: &'static str = "avrtiny";

    match mcu {
        "avr1" => Some(AVR1),
        "at90s1200" => Some(AVR1),
        "attiny11" => Some(AVR1),
        "attiny12" => Some(AVR1),
        "attiny15" => Some(AVR1),
        "attiny28" => Some(AVR1),
        "avr2" => Some(AVR2),
        "at90s2313" => Some(AVR2),
        "at90s2323" => Some(AVR2),
        "at90s2333" => Some(AVR2),
        "at90s2343" => Some(AVR2),
        "attiny22" => Some(AVR2),
        "attiny26" => Some(AVR2),
        "at90s4414" => Some(AVR2),
        "at90s4433" => Some(AVR2),
        "at90s4434" => Some(AVR2),
        "at90s8515" => Some(AVR2),
        "at90c8534" => Some(AVR2),
        "at90s8535" => Some(AVR2),
        "avr25" => Some(AVR25),
        "ata5272" => Some(AVR25),
        "ata6616c" => Some(AVR25),
        "attiny13" => Some(AVR25),
        "attiny13a" => Some(AVR25),
        "attiny2313" => Some(AVR25),
        "attiny2313a" => Some(AVR25),
        "attiny24" => Some(AVR25),
        "attiny24a" => Some(AVR25),
        "attiny4313" => Some(AVR25),
        "attiny44" => Some(AVR25),
        "attiny44a" => Some(AVR25),
        "attiny441" => Some(AVR25),
        "attiny84" => Some(AVR25),
        "attiny84a" => Some(AVR25),
        "attiny25" => Some(AVR25),
        "attiny45" => Some(AVR25),
        "attiny85" => Some(AVR25),
        "attiny261" => Some(AVR25),
        "attiny261a" => Some(AVR25),
        "attiny461" => Some(AVR25),
        "attiny461a" => Some(AVR25),
        "attiny861" => Some(AVR25),
        "attiny861a" => Some(AVR25),
        "attiny43u" => Some(AVR25),
        "attiny87" => Some(AVR25),
        "attiny48" => Some(AVR25),
        "attiny88" => Some(AVR25),
        "attiny828" => Some(AVR25),
        "attiny841" => Some(AVR25),
        "at86rf401" => Some(AVR25),
        "avr3" => Some(AVR3),
        "at43usb355" => Some(AVR3),
        "at76c711" => Some(AVR3),
        "avr31" => Some(AVR31),
        "atmega103" => Some(AVR31),
        "at43usb320" => Some(AVR31),
        "avr35" => Some(AVR35),
        "ata5505" => Some(AVR35),
        "ata6617c" => Some(AVR35),
        "ata664251" => Some(AVR35),
        "at90usb82" => Some(AVR35),
        "at90usb162" => Some(AVR35),
        "atmega8u2" => Some(AVR35),
        "atmega16u2" => Some(AVR35),
        "atmega32u2" => Some(AVR35),
        "attiny167" => Some(AVR35),
        "attiny1634" => Some(AVR35),
        "avr4" => Some(AVR4),
        "ata5795" => Some(AVR4),
        "ata6285" => Some(AVR4),
        "ata6286" => Some(AVR4),
        "ata6289" => Some(AVR4),
        "ata6612c" => Some(AVR4),
        "atmega8" => Some(AVR4),
        "atmega8a" => Some(AVR4),
        "atmega48" => Some(AVR4),
        "atmega48a" => Some(AVR4),
        "atmega48p" => Some(AVR4),
        "atmega48pa" => Some(AVR4),
        "atmega48pb" => Some(AVR4),
        "atmega88" => Some(AVR4),
        "atmega88a" => Some(AVR4),
        "atmega88p" => Some(AVR4),
        "atmega88pa" => Some(AVR4),
        "atmega88pb" => Some(AVR4),
        "atmega8515" => Some(AVR4),
        "atmega8535" => Some(AVR4),
        "atmega8hva" => Some(AVR4),
        "at90pwm1" => Some(AVR4),
        "at90pwm2" => Some(AVR4),
        "at90pwm2b" => Some(AVR4),
        "at90pwm3" => Some(AVR4),
        "at90pwm3b" => Some(AVR4),
        "at90pwm81" => Some(AVR4),
        "avr5" => Some(AVR5),
        "ata5700m322" => Some(AVR5),
        "ata5702m322" => Some(AVR5),
        "ata5782" => Some(AVR5),
        "ata5787" => Some(AVR5),
        "ata5790" => Some(AVR5),
        "ata5790n" => Some(AVR5),
        "ata5791" => Some(AVR5),
        "ata5831" => Some(AVR5),
        "ata5835" => Some(AVR5),
        "ata6613c" => Some(AVR5),
        "ata6614q" => Some(AVR5),
        "ata8210" => Some(AVR5),
        "ata8510" => Some(AVR5),
        "atmega16" => Some(AVR5),
        "atmega16a" => Some(AVR5),
        "atmega161" => Some(AVR5),
        "atmega162" => Some(AVR5),
        "atmega163" => Some(AVR5),
        "atmega164a" => Some(AVR5),
        "atmega164p" => Some(AVR5),
        "atmega164pa" => Some(AVR5),
        "atmega165" => Some(AVR5),
        "atmega165a" => Some(AVR5),
        "atmega165p" => Some(AVR5),
        "atmega165pa" => Some(AVR5),
        "atmega168" => Some(AVR5),
        "atmega168a" => Some(AVR5),
        "atmega168p" => Some(AVR5),
        "atmega168pa" => Some(AVR5),
        "atmega168pb" => Some(AVR5),
        "atmega169" => Some(AVR5),
        "atmega169a" => Some(AVR5),
        "atmega169p" => Some(AVR5),
        "atmega169pa" => Some(AVR5),
        "atmega16hvb" => Some(AVR5),
        "atmega16hvbrevb" => Some(AVR5),
        "atmega16m1" => Some(AVR5),
        "atmega16u4" => Some(AVR5),
        "atmega32a" => Some(AVR5),
        "atmega32" => Some(AVR5),
        "atmega323" => Some(AVR5),
        "atmega324a" => Some(AVR5),
        "atmega324p" => Some(AVR5),
        "atmega324pa" => Some(AVR5),
        "atmega324pb" => Some(AVR5),
        "atmega325" => Some(AVR5),
        "atmega325a" => Some(AVR5),
        "atmega325p" => Some(AVR5),
        "atmega325pa" => Some(AVR5),
        "atmega3250" => Some(AVR5),
        "atmega3250a" => Some(AVR5),
        "atmega3250p" => Some(AVR5),
        "atmega3250pa" => Some(AVR5),
        "atmega328" => Some(AVR5),
        "atmega328p" => Some(AVR5),
        "atmega328pb" => Some(AVR5),
        "atmega329" => Some(AVR5),
        "atmega329a" => Some(AVR5),
        "atmega329p" => Some(AVR5),
        "atmega329pa" => Some(AVR5),
        "atmega3290" => Some(AVR5),
        "atmega3290a" => Some(AVR5),
        "atmega3290p" => Some(AVR5),
        "atmega3290pa" => Some(AVR5),
        "atmega32c1" => Some(AVR5),
        "atmega32m1" => Some(AVR5),
        "atmega32u4" => Some(AVR5),
        "atmega32u6" => Some(AVR5),
        "atmega406" => Some(AVR5),
        "atmega64" => Some(AVR5),
        "atmega64a" => Some(AVR5),
        "atmega640" => Some(AVR5),
        "atmega644" => Some(AVR5),
        "atmega644a" => Some(AVR5),
        "atmega644p" => Some(AVR5),
        "atmega644pa" => Some(AVR5),
        "atmega645" => Some(AVR5),
        "atmega645a" => Some(AVR5),
        "atmega645p" => Some(AVR5),
        "atmega6450" => Some(AVR5),
        "atmega6450a" => Some(AVR5),
        "atmega6450p" => Some(AVR5),
        "atmega649" => Some(AVR5),
        "atmega649a" => Some(AVR5),
        "atmega649p" => Some(AVR5),
        "atmega6490" => Some(AVR5),
        "atmega16hva" => Some(AVR5),
        "atmega16hva2" => Some(AVR5),
        "atmega32hvb" => Some(AVR5),
        "atmega6490a" => Some(AVR5),
        "atmega6490p" => Some(AVR5),
        "atmega64c1" => Some(AVR5),
        "atmega64m1" => Some(AVR5),
        "atmega64hve" => Some(AVR5),
        "atmega64hve2" => Some(AVR5),
        "atmega64rfr2" => Some(AVR5),
        "atmega644rfr2" => Some(AVR5),
        "atmega32hvbrevb" => Some(AVR5),
        "at90can32" => Some(AVR5),
        "at90can64" => Some(AVR5),
        "at90pwm161" => Some(AVR5),
        "at90pwm216" => Some(AVR5),
        "at90pwm316" => Some(AVR5),
        "at90scr100" => Some(AVR5),
        "at90usb646" => Some(AVR5),
        "at90usb647" => Some(AVR5),
        "at94k" => Some(AVR5),
        "m3000" => Some(AVR5),
        "avr51" => Some(AVR51),
        "atmega128" => Some(AVR51),
        "atmega128a" => Some(AVR51),
        "atmega1280" => Some(AVR51),
        "atmega1281" => Some(AVR51),
        "atmega1284" => Some(AVR51),
        "atmega1284p" => Some(AVR51),
        "atmega128rfa1" => Some(AVR51),
        "atmega128rfr2" => Some(AVR51),
        "atmega1284rfr2" => Some(AVR51),
        "at90can128" => Some(AVR51),
        "at90usb1286" => Some(AVR51),
        "at90usb1287" => Some(AVR51),
        "avr6" => Some(AVR6),
        "atmega2560" => Some(AVR6),
        "atmega2561" => Some(AVR6),
        "atmega256rfr2" => Some(AVR6),
        "atmega2564rfr2" => Some(AVR6),
        "avrxmega2" => Some(AVRXMEGA2),
        "atxmega8e5" => Some(AVRXMEGA2),
        "atxmega16a4" => Some(AVRXMEGA2),
        "atxmega16d4" => Some(AVRXMEGA2),
        "atxmega16e5" => Some(AVRXMEGA2),
        "atxmega32a4" => Some(AVRXMEGA2),
        "atxmega32c3" => Some(AVRXMEGA2),
        "atxmega32d3" => Some(AVRXMEGA2),
        "atxmega32d4" => Some(AVRXMEGA2),
        "atxmega16a4u" => Some(AVRXMEGA2),
        "atxmega16c4" => Some(AVRXMEGA2),
        "atxmega32a4u" => Some(AVRXMEGA2),
        "atxmega32c4" => Some(AVRXMEGA2),
        "atxmega32e5" => Some(AVRXMEGA2),
        "avr64da28" => Some(AVRXMEGA2),
        "avr64da32" => Some(AVRXMEGA2),
        "avr64da48" => Some(AVRXMEGA2),
        "avr64da64" => Some(AVRXMEGA2),
        "avr64da28s" => Some(AVRXMEGA2),
        "avr64da32s" => Some(AVRXMEGA2),
        "avr64da48s" => Some(AVRXMEGA2),
        "avr64da64s" => Some(AVRXMEGA2),
        "avr64db28" => Some(AVRXMEGA2),
        "avr64db32" => Some(AVRXMEGA2),
        "avr64db48" => Some(AVRXMEGA2),
        "avr64db64" => Some(AVRXMEGA2),
        "avr64dd14" => Some(AVRXMEGA2),
        "avr64dd20" => Some(AVRXMEGA2),
        "avr64dd28" => Some(AVRXMEGA2),
        "avr64dd32" => Some(AVRXMEGA2),
        "avr64du28" => Some(AVRXMEGA2),
        "avr64du32" => Some(AVRXMEGA2),
        "avr64ea28" => Some(AVRXMEGA2),
        "avr64ea32" => Some(AVRXMEGA2),
        "avr64ea48" => Some(AVRXMEGA2),
        "avr64sd28" => Some(AVRXMEGA2),
        "avr64sd32" => Some(AVRXMEGA2),
        "avr64sd48" => Some(AVRXMEGA2),
        "avrxmega3" => Some(AVRXMEGA3),
        "attiny202" => Some(AVRXMEGA3),
        "attiny204" => Some(AVRXMEGA3),
        "attiny402" => Some(AVRXMEGA3),
        "attiny404" => Some(AVRXMEGA3),
        "attiny406" => Some(AVRXMEGA3),
        "attiny804" => Some(AVRXMEGA3),
        "attiny806" => Some(AVRXMEGA3),
        "attiny807" => Some(AVRXMEGA3),
        "attiny1604" => Some(AVRXMEGA3),
        "attiny1606" => Some(AVRXMEGA3),
        "attiny1607" => Some(AVRXMEGA3),
        "attiny212" => Some(AVRXMEGA3),
        "attiny214" => Some(AVRXMEGA3),
        "attiny412" => Some(AVRXMEGA3),
        "attiny414" => Some(AVRXMEGA3),
        "attiny416" => Some(AVRXMEGA3),
        "attiny416auto" => Some(AVRXMEGA3),
        "attiny417" => Some(AVRXMEGA3),
        "attiny814" => Some(AVRXMEGA3),
        "attiny816" => Some(AVRXMEGA3),
        "attiny817" => Some(AVRXMEGA3),
        "attiny1614" => Some(AVRXMEGA3),
        "attiny1616" => Some(AVRXMEGA3),
        "attiny1617" => Some(AVRXMEGA3),
        "attiny3214" => Some(AVRXMEGA3),
        "attiny3216" => Some(AVRXMEGA3),
        "attiny3217" => Some(AVRXMEGA3),
        "attiny424" => Some(AVRXMEGA3),
        "attiny426" => Some(AVRXMEGA3),
        "attiny427" => Some(AVRXMEGA3),
        "attiny824" => Some(AVRXMEGA3),
        "attiny826" => Some(AVRXMEGA3),
        "attiny827" => Some(AVRXMEGA3),
        "attiny1624" => Some(AVRXMEGA3),
        "attiny1626" => Some(AVRXMEGA3),
        "attiny1627" => Some(AVRXMEGA3),
        "attiny3224" => Some(AVRXMEGA3),
        "attiny3226" => Some(AVRXMEGA3),
        "attiny3227" => Some(AVRXMEGA3),
        "atmega808" => Some(AVRXMEGA3),
        "atmega809" => Some(AVRXMEGA3),
        "atmega1608" => Some(AVRXMEGA3),
        "atmega1609" => Some(AVRXMEGA3),
        "atmega3208" => Some(AVRXMEGA3),
        "atmega3209" => Some(AVRXMEGA3),
        "atmega4808" => Some(AVRXMEGA3),
        "atmega4809" => Some(AVRXMEGA3),
        "avr16dd14" => Some(AVRXMEGA3),
        "avr16dd20" => Some(AVRXMEGA3),
        "avr16dd28" => Some(AVRXMEGA3),
        "avr16dd32" => Some(AVRXMEGA3),
        "avr16du14" => Some(AVRXMEGA3),
        "avr16du20" => Some(AVRXMEGA3),
        "avr16du28" => Some(AVRXMEGA3),
        "avr16du32" => Some(AVRXMEGA3),
        "avr32da28" => Some(AVRXMEGA3),
        "avr32da32" => Some(AVRXMEGA3),
        "avr32da48" => Some(AVRXMEGA3),
        "avr32da28s" => Some(AVRXMEGA3),
        "avr32da32s" => Some(AVRXMEGA3),
        "avr32da48s" => Some(AVRXMEGA3),
        "avr32db28" => Some(AVRXMEGA3),
        "avr32db32" => Some(AVRXMEGA3),
        "avr32db48" => Some(AVRXMEGA3),
        "avr32dd14" => Some(AVRXMEGA3),
        "avr32dd20" => Some(AVRXMEGA3),
        "avr32dd28" => Some(AVRXMEGA3),
        "avr32dd32" => Some(AVRXMEGA3),
        "avr32du14" => Some(AVRXMEGA3),
        "avr32du20" => Some(AVRXMEGA3),
        "avr32du28" => Some(AVRXMEGA3),
        "avr32du32" => Some(AVRXMEGA3),
        "avr16eb14" => Some(AVRXMEGA3),
        "avr16eb20" => Some(AVRXMEGA3),
        "avr16eb28" => Some(AVRXMEGA3),
        "avr16eb32" => Some(AVRXMEGA3),
        "avr32eb14" => Some(AVRXMEGA3),
        "avr32eb20" => Some(AVRXMEGA3),
        "avr32eb28" => Some(AVRXMEGA3),
        "avr32eb32" => Some(AVRXMEGA3),
        "avr16ea28" => Some(AVRXMEGA3),
        "avr16ea32" => Some(AVRXMEGA3),
        "avr16ea48" => Some(AVRXMEGA3),
        "avr32ea28" => Some(AVRXMEGA3),
        "avr32ea32" => Some(AVRXMEGA3),
        "avr32ea48" => Some(AVRXMEGA3),
        "avr16la14" => Some(AVRXMEGA3),
        "avr16la20" => Some(AVRXMEGA3),
        "avr16la28" => Some(AVRXMEGA3),
        "avr16la32" => Some(AVRXMEGA3),
        "avr32la14" => Some(AVRXMEGA3),
        "avr32la20" => Some(AVRXMEGA3),
        "avr32la28" => Some(AVRXMEGA3),
        "avr32la32" => Some(AVRXMEGA3),
        "avr32sd20" => Some(AVRXMEGA3),
        "avr32sd28" => Some(AVRXMEGA3),
        "avr32sd32" => Some(AVRXMEGA3),
        "avrxmega4" => Some(AVRXMEGA4),
        "atxmega64a3" => Some(AVRXMEGA4),
        "atxmega64d3" => Some(AVRXMEGA4),
        "atxmega64a3u" => Some(AVRXMEGA4),
        "atxmega64a4u" => Some(AVRXMEGA4),
        "atxmega64b1" => Some(AVRXMEGA4),
        "atxmega64b3" => Some(AVRXMEGA4),
        "atxmega64c3" => Some(AVRXMEGA4),
        "atxmega64d4" => Some(AVRXMEGA4),
        "avr128da28" => Some(AVRXMEGA4),
        "avr128da32" => Some(AVRXMEGA4),
        "avr128da48" => Some(AVRXMEGA4),
        "avr128da64" => Some(AVRXMEGA4),
        "avr128da28s" => Some(AVRXMEGA4),
        "avr128da32s" => Some(AVRXMEGA4),
        "avr128da48s" => Some(AVRXMEGA4),
        "avr128da64s" => Some(AVRXMEGA4),
        "avr128db28" => Some(AVRXMEGA4),
        "avr128db32" => Some(AVRXMEGA4),
        "avr128db48" => Some(AVRXMEGA4),
        "avr128db64" => Some(AVRXMEGA4),
        "avrxmega5" => Some(AVRXMEGA5),
        "atxmega64a1" => Some(AVRXMEGA5),
        "atxmega64a1u" => Some(AVRXMEGA5),
        "avrxmega6" => Some(AVRXMEGA6),
        "atxmega128a3" => Some(AVRXMEGA6),
        "atxmega128d3" => Some(AVRXMEGA6),
        "atxmega192a3" => Some(AVRXMEGA6),
        "atxmega192d3" => Some(AVRXMEGA6),
        "atxmega256a3" => Some(AVRXMEGA6),
        "atxmega256a3b" => Some(AVRXMEGA6),
        "atxmega256a3bu" => Some(AVRXMEGA6),
        "atxmega256d3" => Some(AVRXMEGA6),
        "atxmega128a3u" => Some(AVRXMEGA6),
        "atxmega128b1" => Some(AVRXMEGA6),
        "atxmega128b3" => Some(AVRXMEGA6),
        "atxmega128c3" => Some(AVRXMEGA6),
        "atxmega128d4" => Some(AVRXMEGA6),
        "atxmega192a3u" => Some(AVRXMEGA6),
        "atxmega192c3" => Some(AVRXMEGA6),
        "atxmega256a3u" => Some(AVRXMEGA6),
        "atxmega256c3" => Some(AVRXMEGA6),
        "atxmega384c3" => Some(AVRXMEGA6),
        "atxmega384d3" => Some(AVRXMEGA6),
        "avrxmega7" => Some(AVRXMEGA7),
        "atxmega128a1" => Some(AVRXMEGA7),
        "atxmega128a1u" => Some(AVRXMEGA7),
        "atxmega128a4u" => Some(AVRXMEGA7),
        "avrtiny" => Some(AVRTINY),
        "attiny4" => Some(AVRTINY),
        "attiny5" => Some(AVRTINY),
        "attiny9" => Some(AVRTINY),
        "attiny10" => Some(AVRTINY),
        "attiny102" => Some(AVRTINY),
        "attiny104" => Some(AVRTINY),
        "attiny20" => Some(AVRTINY),
        "attiny40" => Some(AVRTINY),
        _ => None,
    }
}
