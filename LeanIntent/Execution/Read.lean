module

public import Lean
public import LeanIntent.Execution
public import LeanIntent.Execution.Code
public import LeanIntent.Implementation.Read

public section

namespace LeanIntent.Execution.Read

open Lean Meta LeanIntent.Render LeanIntent.Confirmation.Read

/-- The name `e` reduces to, through the kernel: `Name.anonymous`, or `Name.str` or `Name.num`
applied to a name and a literal. An error when it reduces to anything else. -/
def nameLit (e : Expr) : MetaM Name :=
  go (2 ^ 64) e
where
  go : Nat → Expr → MetaM Name
    | 0, _ => throwError "name has more than 2 ^ 64 components"
    | fuel + 1, e => do
      let e ← readWhnf e
      match e with
      | .const ``Name.anonymous _ => return .anonymous
      | .app (.app (.const ``Name.str _) parent) s =>
        return .str (← go fuel parent) (← strLit s)
      | .app (.app (.const ``Name.num _) parent) n =>
        match ← readWhnf n with
        | .lit (.natVal k) => return .num (← go fuel parent) k
        | n' => throwError "expected a natural number literal, found{indentExpr n'}"
      | _ => throwError "expected a name, found{indentExpr e}"

/-- What the build shows of the value `decl`, a constant whose type reduces to `Runs d`: the
deliverable its type names, where that is a constant, and the executable it names. An error when
its value does not reduce to `Runs.mk`'s application, or the executable to a name. -/
def claimOf (decl : Name) : MetaM Claim := do
  let t ← readWhnf (← getConstInfo decl).type
  let .app (.app (.const ``Runs _) _) d := t
    | throwError "the type of {decl} is not `LeanIntent.Runs` applied to a deliverable"
  let args ← ctorArgs (← Confirmation.Read.constOf decl) ``Runs.mk 3
  let executable ← try nameLit args[2] catch e =>
    throwError "the executable {decl} names is not read as a name: {e.toMessageData}"
  return ⟨decl, Implementation.Read.constOf? d, executable⟩

/-- The values of `Runs d` the modules `mods` declare, as the build shows them. -/
def claims (mods : Array Name) : MetaM (Array Claim) := do
  (← declaredIn mods ``Runs).mapM claimOf

/-- The declarations the IR expression `e` calls (`IR.Expr.fap`) or makes a closure of
(`IR.Expr.pap`). -/
@[expose] def exprRefs : IR.Expr → List Name
  | .fap c _ | .pap c _ => [c]
  | .ctor .. | .reset .. | .reuse .. | .proj .. | .uproj .. | .sproj .. | .ap .. | .box ..
  | .unbox .. | .lit .. | .isShared .. => []

mutual

/-- The declarations the IR body `b` calls or makes a closure of, in each of its instructions, join
points and alternatives. -/
@[expose] def bodyRefs : IR.FnBody → List Name
  | .vdecl _ _ e b => exprRefs e ++ bodyRefs b
  | .jdecl _ _ v b => bodyRefs v ++ bodyRefs b
  | .set _ _ _ b | .setTag _ _ b | .uset _ _ _ b | .sset _ _ _ _ _ b | .inc _ _ _ _ b
  | .dec _ _ _ _ b | .del _ b => bodyRefs b
  | .case _ _ _ cs => altsRefs cs.toList
  | .ret _ | .jmp _ _ | .unreachable => []

@[expose] def altsRefs : List IR.Alt → List Name
  | [] => []
  | .ctor _ b :: rest | .default b :: rest => bodyRefs b ++ altsRefs rest

end

/-- The declarations that the IR the build stored for `n`, as Lean finds it (`IR.findEnvDecl`),
calls or makes a closure of: none where Lean finds no IR for `n`, or where its IR declares it
implemented in another language (`extern`). -/
@[expose] def irRefs (env : Environment) (n : Name) : List Name :=
  match IR.findEnvDecl env n with
  | some (.fdecl _ _ _ body _) => bodyRefs body
  | some (.extern ..) | none => []

/-- The modules of `env` whose imports reach the module `m`, `m` included: those whose code can
call a declaration of `m`. -/
@[expose] def importersOf (env : Environment) (m : Name) : Std.HashSet Name := Id.run do
  let mods := env.header.modules
  let mut importers : Std.HashMap Name (Array Name) := {}
  for h : i in [0:mods.size] do
    for imp in (env.header.moduleData[i]?.map (·.imports)).getD #[] do
      importers := importers.insert imp.module
        ((importers.getD imp.module #[]).push mods[i].module)
  let mut found : Std.HashSet Name := ({} : Std.HashSet Name).insert m
  let mut work := [m]
  for _ in [0 : mods.size + 1] do
    match work with
    | [] => break
    | n :: rest =>
      work := rest
      for next in importers.getD n #[] do
        unless found.contains next do
          found := found.insert next
          work := next :: work
  return found

/-- The module of `env` that `n` belongs to, where `env` imports it: the module that declares the
constant `n`, or, for a declaration the environment holds no constant of, the module whose IR holds
it. -/
@[expose] def importedModuleOf (env : Environment) (n : Name) : Option Name :=
  env.getModuleIdxFor? n |>.bind fun i => Confirmation.Read.moduleName? env.header i.toNat

def reachesIn (c : Implementation.Constant) : CoreM Bool := do
  let env ← getEnv
  unless importedModuleOf env c.name == some c.module do return false
  let up := importersOf env c.module
  let inCone (n : Name) : Bool := (importedModuleOf env n).any up.contains
  unless inCone `main do return false
  let code (n : Name) : List Name :=
    if n != c.name && isCompiledCodeOf (env.contains ·) c.name n && (IR.findEnvDecl env n).isSome
    then [c.name] else []
  let mut table : Std.HashMap Name (List Name) := {}
  let mut queued : Std.HashSet Name := ({} : Std.HashSet Name).insert `main
  let mut work := [`main]
  for _ in [0 : env.const2ModIdx.size + 1] do
    match work with
    | [] => break
    | n :: rest =>
      work := rest
      let refs := (irRefs env n ++ code n).filter inCone
      table := table.insert n refs
      let mut push : Array Name := #[]
      for r in refs do
        unless queued.contains r do
          queued := queued.insert r
          push := push.push r
      work := push.toList ++ work
  match reach (fun n => table.getD n []) `main c.name (table.size + 1) with
  | .reached => return true
  | .unreached => return false
  | .exhausted => throwError "`main` reaches more than {table.size + 1} declarations"

def executableIn (env : Environment) (name root : Name) (targets : List Implementation.Constant) :
    CoreM Executable := do
  let entry := env.contains `main
  let reached ← if entry then targets.filterM reachesIn else pure []
  return ⟨name, root, entry, reached⟩

/-- **What a gate reads**, from the finished build: the report on what the executables `exes`,
each given by its name and root module as the project's Lake configuration declares them, run of
the project whose modules are `mods`. It reads the deliverables and claims of those modules, the
implementations `Implementation.Read.check` reads of them, and, for each executable, the
environment Lean imports from its root module alone, in which it reads `main` and what `main`
reaches. Its findings are empty exactly when every claim holds (`Execution.findings_eq_nil_iff`). -/
def check (mods : Array Name) (exes : Array (Name × Name)) : MetaM Report := do
  let ds ← declaredIn mods ``Deliverable
  let implemented ← Implementation.Read.check mods
  let is := implemented.implementations.map fun (d, _, c) => (d, c)
  let as := implemented.awaiting.map (·.1)
  let cls ← claims mods
  let ctx ← readThe Core.Context
  let es ← exes.mapM fun (name, root) => do
    let targets := (cls.toList.filter (·.executable == name)).flatMap fun cl =>
      is.filterMap fun (d, c) => if cl.deliverable == some d then some c else none
    try
      let env ← importModules #[{ module := root }] (← getOptions)
      let (e, _) ← (executableIn env name root targets.eraseDups).run ctx { env }
      return e
    catch err =>
      throwError "the executable {name}, whose root module is {root}, cannot be read: \
        {err.toMessageData}"
  return report ds.toList is as es.toList cls.toList

end LeanIntent.Execution.Read
