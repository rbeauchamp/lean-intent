module

public import Lean

public section

namespace LeanIntent.Imported

open Lean

structure Stored where
  contains : Name → Bool
  moduleOf : Name → Option Name
  modules : Array (Name × Array Name)
  irDecl? : Name → Option IR.Decl
  constCount : Nat

def stored (root : Name) (opts : Options) : IO Stored := do
  let env ← importModules #[{ module := root }] opts
  return {
    contains := fun n => env.contains n
    moduleOf := fun n => (env.getModuleIdxFor? n).bind fun i =>
      env.header.modules[i.toNat]?.map (·.module)
    modules := env.header.modules.mapIdx fun i mod =>
      (mod.module, ((env.header.moduleData[i]?.map (·.imports)).getD #[]).map (·.module))
    irDecl? := fun n => IR.findEnvDecl env n
    constCount := env.const2ModIdx.size }

end LeanIntent.Imported
