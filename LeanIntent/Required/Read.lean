module

public import Lean
public import LeanIntent.Required
public import LeanIntent.Required.ModuleName
public import LeanIntent.Implementation.Read
public import LeanIntent.Loaded

public section

namespace LeanIntent.Required.Read

open Lean Meta LeanIntent.Render LeanIntent.Confirmation.Read LeanIntent.Implementation.Read

@[expose] def sameDeclaration (own held : ConstantInfo) : Bool :=
  own.levelParams == held.levelParams && own.type == held.type &&
    match own, held with
    | .defnInfo a, .defnInfo b => a.value == b.value
    | .opaqueInfo _, .opaqueInfo _ | .axiomInfo _, .axiomInfo _ => true
    | _, _ => false

def ownDeclaration (c : Name) : MetaM (Name × ConstantInfo) := asking do
  let env ← getEnv
  match env.getModuleIdxFor? c with
  | some idx =>
    let some m := Confirmation.Read.moduleName? env.header idx.toNat
      | throwError "the environment records no module of index {idx.toNat}, which declares {c}"
    match env.header.moduleData[idx.toNat]?.bind (·.constants.find? (·.name == c)) with
    | some own => return (m, own)
    | none =>
      throwError "the environment records {c} under the module {m}, which does not itself declare \
        it, so the module that declares it cannot be read"
  | none =>
    match env.constants.map₂.find? c with
    | some own => return (env.mainModule, own)
    | none =>
      throwError "the environment records {c} under no module, and the file being elaborated \
        does not declare it, so the module that declares it cannot be read"

def citedOf (e : Expr) : MetaM Cited := asking do
  let args ← ctorArgs e ``Proof.mk 2
  match constOf? args[1] with
  | none => return .term
  | some c =>
    let (m, own) ← ownDeclaration c
    match own with
    | .thmInfo _ =>
      let held ← getConstInfo c
      unless own.levelParams == held.levelParams && own.type == held.type do
        throwError "the module {m} declares the theorem {c} with another statement than the \
          environment holds for that name, so it is not read"
      return .thm ⟨m, c⟩
    | _ => return .other ⟨m, c⟩

def entryOf (decl : Implementation.Constant) : MetaM Entry := asking do
  let t ← readWhnf (← getConstInfo decl.name).type
  let .app (.app (.const ``Required _) _) d := t
    | throwError "the type of {decl.name} is not `LeanIntent.Required` applied to a deliverable"
  let args ← ctorArgs (← Confirmation.Read.constOf decl.name) ``Required.mk 4
  let theorems ← (← listElems args[2]).mapM citedOf
  return ⟨decl.name, decl.module, constOf? d, theorems.toList⟩

def declaredAnywhere (heads : Array Name) : MetaM (Array (Implementation.Constant × Name)) := asking do
  let env ← getEnv
  let read (ci : ConstantInfo) := ci matches .defnInfo _ | .opaqueInfo _ | .axiomInfo _
  let mut candidates : Array (Name × ConstantInfo) := #[]
  for h : i in [0:env.header.moduleData.size] do
    let some m := Confirmation.Read.moduleName? env.header i
      | throwError "the environment names no module of index {i}, whose declarations it holds"
    for ci in env.header.moduleData[i].constants do
      if read ci then candidates := candidates.push (m, ci)
  candidates := env.constants.map₂.foldl (init := candidates) fun acc _ ci =>
    if read ci then acc.push (env.mainModule, ci) else acc
  let mut found : Array (Implementation.Constant × Name) := #[]
  for (m, ci) in candidates do
    if let .const head _ := (← readWhnf ci.type).getAppFn then
      if heads.contains head then
        unless proofSafe ci do
          throwError "{ci.name} is unsafe or partial, so its proofs could prove anything, and it is \
            not read"
        unless (env.find? ci.name).any (sameDeclaration ci) do
          throwError "the module {m} declares {ci.name}, and the environment holds another \
            declaration of that name, so it is not read"
        found := found.push (⟨m, ci.name⟩, head)
  return found.qsort fun a b => Name.lt a.1.name b.1.name

def check (built : Array Name) : MetaM Report := asking do
  let env ← getEnv
  if env.header.isModule then
    throwError "the required-theorems check reads every declaration of every module imported, and \
      a `module` file need not import everything each module declares, so a value could go \
      unread: run the check from a file that is not a `module` file"
  for m in built do
    unless m == env.mainModule || (env.getModuleIdx? m).isSome do
      throwError "the module {m}, which the build lists, is not imported here, so what it declares \
        cannot be read"
  let found ← declaredAnywhere #[``Deliverable, ``Implementation, ``Required]
  let of (head : Name) := found.filterMap fun (c, h) => if h == head then some c else none
  let rs ← (of ``Required).mapM entryOf
  return report built.toList (of ``Deliverable).toList (of ``Implementation).toList rs.toList

@[expose] def queryModules (out : String) : Except String (Array Name) := do
  let mut mods : Array Name := #[]
  for line in out.splitOn "\n" do
    if line.trimAscii.isEmpty then continue
    let json ← Json.parse line
    let .arr items := json
      | throw s!"a line of Lake's output is not a JSON array of module names: {line}"
    for item in items do
      let .str s := item
        | throw s!"an entry of Lake's output is not a module name: {item.compress}"
      match moduleName? s with
      | some n => mods := mods.push n
      | none =>
        throw s!"the module name {s} is not of the form this check reads, which is dots between \
          parts that are each an ASCII letter followed by ASCII letters, digits, `_` or `'`, so it \
          is not read as any module: give the check the build's module names from Lake's own \
          values instead"
  if mods.isEmpty then
    throw "Lake's output lists no module, so no module is known to be built"
  return mods

end LeanIntent.Required.Read
