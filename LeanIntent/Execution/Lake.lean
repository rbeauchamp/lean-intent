module

public import Lake.Config.Package

public section

namespace LeanIntent.Execution

@[expose] def lakeExecutables (pkg : _root_.Lake.Package) : Array (Lean.Name × Lean.Name) :=
  pkg.targetDecls.filterMap fun t => t.leanExeConfig?.map fun cfg => (t.name, cfg.root)

end LeanIntent.Execution
