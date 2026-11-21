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

- **`boundQueries`**: `IO.Process.spawn` (`lean_io_process_spawn`), `IO.appPath` (`lean_io_app_path`), `IO.currentDir` (`lean_io_current_dir`), `IO.Process.getCurrentDir` (`lean_io_process_get_current_dir`), and `IO.getEnv` (`lean_io_getenv`). In Lean's `Init`, `IO.Process.output` and `IO.Process.run` route through `IO.Process.spawn`, so checking `IO.Process.spawn` covers all three.
- **`processQueries`**: combines `boundQueries` with nine libuv C runtime functions from `Std.Internal.UV.System` (`lean_uv_exepath`, `lean_uv_cwd`, `lean_uv_os_getenv`, `lean_uv_os_environ`, `lean_uv_os_homedir`, `lean_uv_os_tmpdir`, `lean_uv_os_get_passwd`, `lean_uv_os_gethostname`, `lean_uv_os_uname`), identified at Lean v4.35.0 by searching every `extern` attribute for names containing `spawn`, `exec`, `fork`, `system`, `getenv`, `environ`, `app_path`, `exe`, `current_dir`, `cwd`, `homedir`, `tmpdir`, `passwd`, `hostname`, or `uname`. Adding runtime binding canaries / version pinning for these nine libuv symbols is tracked in #93; replacing the hardcoded 64-hop witness path loop in `checkProcess` with `parent.size` is tracked in #95.

### `notFollowed` TCB exemption (`Lean.manualRoot`)

- `checkProcess` exempts `Lean.manualRoot`, which reads `LEAN_MANUAL_ROOT` at startup solely to format Lean manual URLs in logged errors and docstrings (`Lean/DocString/Links.lean`, `Lean/Log.lean`), pulled in transitively through `Lean.logAt`. No library text prints those manual URLs.

### Lake boundary (`LeanIntent/Execution/Lake.lean`)

- `LeanIntent.Execution.lakeExecutables` consumes an already-loaded `Lake.Package` rather than invoking Lake or spawning a subprocess, reading `[[lean_exe]]` targets from Lake's own package structure (covering both `lakefile.toml` and `lakefile.lean`) while remaining compliant with `PROCESS`.

## Trusted base and consequences

- `PROCESS` follows calls by name in Lean IR; it cannot observe closures invoked indirectly through mutable references (such as Lean's elaborator tables) or project code executed while elaborating a term.
- Exempting `Lean.manualRoot` is a TCB assumption that no library output exposes `LEAN_MANUAL_ROOT`.
