# ADR-0003: Runtime process-call audit (`PROCESS`), `Lean.manualRoot` exemption, and Lake boundary

## Status

Accepted

## Context

`lean-intent` promises that compiled library code calls none of the runtime functions `PROCESS` monitors (`processQueries`), except through `Lean.manualRoot`, the one exemption decided below: those that start a process, and those that tell a process its environment variables, executable path, working directory, home or temporary directory, user, hostname, or operating system. So a text the library computes takes nothing from those, given the assumption recorded below that no library text shows what `Lean.manualRoot` reads (`LEAN_MANUAL_ROOT`), and a checker that refuses a process start can call the library. The promise is not that the library is pure or reads nothing else: `PROCESS` monitors no filesystem function, and the library reads the filesystem, for example `IO.FS.realPath` and `System.FilePath.pathExists` in `LeanIntent/Render/Text.lean` (`realOLean?`, `leanLibDir`), which resolve Lean's own library directory from the process's search path.

## Decision

### Call-by-name compiled IR walk (`PROCESS` in `tools/check.lean`)

- After building all library modules, `checkProcess` collects every compiled declaration (`Lean.IR.findEnvDecl`) in the library modules as roots and performs a breadth-first traversal over `Lean.IR.collectUsedDecls` (which includes closures and initializers as Lean's C emitter collects them).
- The check fails closed rather than passing when:
  - the library holds no compiled code,
  - any reached declaration has no compiled IR to inspect,
  - any reached `.extern` declaration has an `.opaque` entry whose compiled code is not exported, or
  - any declaration in `boundQueries` is no longer bound to its expected C function symbol.

### Monitored C symbols and `boundQueries` canaries

- **`boundQueries`**: pairs all 14 monitored C runtime symbols with their Lean declarations so `checkProcess` runs an `IR.findEnvDecl` binding check on every entry of `processQueries` (importing `Std.Internal.UV.System` alongside the library modules): five in `Init` (`IO.Process.spawn` → `lean_io_process_spawn`, covering `IO.Process.output` and `IO.Process.run`; `IO.appPath` → `lean_io_app_path`; `IO.currentDir` → `lean_io_current_dir`; `IO.Process.getCurrentDir` → `lean_io_process_get_current_dir`; and `IO.getEnv` → `lean_io_getenv`) and nine in `Std.Internal.UV.System` (`Std.Internal.UV.System.exePath` → `lean_uv_exepath`, `Std.Internal.UV.System.cwd` → `lean_uv_cwd`, `Std.Internal.UV.System.osGetenv` → `lean_uv_os_getenv`, `Std.Internal.UV.System.osEnviron` → `lean_uv_os_environ`, `Std.Internal.UV.System.osHomedir` → `lean_uv_os_homedir`, `Std.Internal.UV.System.osTmpdir` → `lean_uv_os_tmpdir`, `Std.Internal.UV.System.osGetPasswd` → `lean_uv_os_get_passwd`, `Std.Internal.UV.System.osGetHostname` → `lean_uv_os_gethostname`, and `Std.Internal.UV.System.osUname` → `lean_uv_os_uname`).
- **`processQueries`, Lean version pin, and witness path reconstruction**: `processQueries` is `boundQueries.map (·.2)`, identified at Lean v4.35.0 and read again at v4.36.0 by searching every `extern` attribute for names containing `spawn`, `exec`, `fork`, `system`, `getenv`, `environ`, `app_path`, `exe`, `current_dir`, `cwd`, `homedir`, `tmpdir`, `passwd`, `hostname`, or `uname`. `checkProcess` also checks `Lean.versionString == testsLean` (`"4.36.0"`) so toolchain upgrades force re-auditing `Init` and `Std.Internal.UV.System` `extern` attributes, and bounds witness call-chain reconstruction (`path`) by `parent.size` (exact upper bound on any acyclic BFS path in `parent`) so complete chains from a library root declaration to an offending runtime call are never truncated.

### `notFollowed` TCB exemption (`Lean.manualRoot`)

- `checkProcess` exempts `Lean.manualRoot`, which reads `LEAN_MANUAL_ROOT` at startup solely to format Lean manual URLs in logged errors and docstrings (`Lean/DocString/Links.lean`, `Lean/Log.lean`), pulled in transitively through `Lean.logAt`. No library text prints those manual URLs.

### Lake boundary (`LeanIntent/Execution/Lake.lean`)

- `LeanIntent.Execution.lakeExecutables` consumes an already-loaded `Lake.Package` rather than invoking Lake or spawning a subprocess, reading `[[lean_exe]]` targets from Lake's own package structure (covering both `lakefile.toml` and `lakefile.lean`) while remaining compliant with `PROCESS`.

## Trusted base and consequences

- `PROCESS` follows calls by name in Lean IR; it cannot observe closures invoked indirectly through mutable references (such as Lean's elaborator tables) or project code executed while elaborating a term.
- Exempting `Lean.manualRoot` is a TCB assumption that no library output exposes `LEAN_MANUAL_ROOT`.
