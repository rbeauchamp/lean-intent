import Lake.Config.Package

/-!
# The executable targets a Lake package declares

`LeanIntent.Execution.Read.check` reads what each executable of a project runs, given the
executables by name and root module. This module reads them from the project's Lake configuration
through Lake's own types, so that a gate does not list them by hand: every `lean_exe` target the
package declares, `[[lean_exe]]` in `lakefile.toml` or `lean_exe` in `lakefile.lean`, by its name
and the root module Lake builds it from. The package is the one a gate loads with Lake's loader;
this module only reads its configuration, and starts no process.
-/

namespace LeanIntent.Execution

/-- **The executables `pkg` declares**: each `lean_exe` target of the package, by its name and its
root module, as Lake's configuration holds them (`Lake.Package.targetDecls`, of which
`Lake.ConfigDecl.leanExeConfig?` gives the executables' configurations, whose `root` defaults to the
target's name). -/
def lakeExecutables (pkg : _root_.Lake.Package) : Array (Lean.Name × Lean.Name) :=
  pkg.targetDecls.filterMap fun t => t.leanExeConfig?.map fun cfg => (t.name, cfg.root)

end LeanIntent.Execution
