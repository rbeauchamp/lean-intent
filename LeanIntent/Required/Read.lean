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

def citedProof (e : Expr) : MetaM Cited := asking do
  match constOf? e with
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

def citedOf (e : Expr) : MetaM Cited := asking do
  let args ← ctorArgs e ``Proof.mk 2
  citedProof args[1]

def constantOf? (e : Expr) : MetaM (Option Implementation.Constant) := asking do
  match constOf? e with
  | none => return none
  | some c =>
    let (m, own) ← ownDeclaration c
    unless proofSafe own do
      throwError "{c} is unsafe or partial, so it is not read"
    let held ← getConstInfo c
    unless sameDeclaration own held do
      throwError "the module {m} declares {c}, and the environment holds another declaration of \
        that name, so it is not read"
    return some ⟨m, c⟩

def readO2Run (e : Expr) : MetaM O2RunEntry := asking do
  let e ← readWhnf e
  if e.isAppOfArity ``O2RunProof.proved 3 then
    let args ← ctorArgs e ``O2RunProof.proved 3
    return .proved (← citedProof args[2])
  else if e.isAppOfArity ``O2RunProof.deferred 4 then
    let args ← ctorArgs e ``O2RunProof.deferred 4
    let reason ← try strLit args[2] catch err =>
      throwError "the reason for deferring `O2Run` is not read as a string literal: \
        {err.toMessageData}"
    return .deferred reason
  else
    throwError "expected `LeanIntent.O2RunProof.proved` or `LeanIntent.O2RunProof.deferred`, \
      found{indentExpr e}"

def readDirection (e : Expr) : MetaM DirectionEntry := asking do
  let e ← readWhnf e
  if e.isAppOfArity ``ComparisonDirection.implies 4 then
    let args ← ctorArgs e ``ComparisonDirection.implies 4
    return .proved (← citedProof args[3])
  else if e.isAppOfArity ``ComparisonDirection.separates 5 then
    let args ← ctorArgs e ``ComparisonDirection.separates 5
    return .proved (← citedProof args[4])
  else if e.isAppOfArity ``ComparisonDirection.unproved 5 then
    let args ← ctorArgs e ``ComparisonDirection.unproved 5
    let reason ← try strLit args[3] catch err =>
      throwError "the reason for an unproved comparison direction is not read as a string literal: \
        {err.toMessageData}"
    return .unproved reason
  else
    throwError "expected a `LeanIntent.ComparisonDirection` constructor, found{indentExpr e}"

def readComparison (e : Expr) : MetaM ComparisonEntry := asking do
  let e ← readWhnf e
  if e.isAppOfArity ``BlindComparison.records 6 then
    let args ← ctorArgs e ``BlindComparison.records 6
    let blind ← constantOf? args[2]
    let fwd ← readDirection args[3]
    let bwd ← readDirection args[4]
    return .records blind fwd bwd
  else if e.isAppOfArity ``BlindComparison.cases 6 then
    let args ← ctorArgs e ``BlindComparison.cases 6
    let theorems ← (← listElems args[2]).mapM citedOf
    let reason ← try strLit args[3] catch err =>
      throwError "the reason for a concrete-cases comparison is not read as a string literal: \
        {err.toMessageData}"
    return .cases theorems.toList reason
  else
    throwError "expected `LeanIntent.BlindComparison.records` or `LeanIntent.BlindComparison.cases`, \
      found{indentExpr e}"

def deliverableEntryOf (c : Implementation.Constant) : MetaM DeliverableEntry := asking do
  let e ← readWhnf (← Confirmation.Read.constOf c.name)
  let record :=
    if e.isAppOfArity ``Deliverable.mk 5 then
      let args := e.getAppArgs
      if h : 1 < args.size then constOf? args[1] else none
    else none
  return ⟨c.module, c.name, record⟩

def implEntryOf (c : Implementation.Constant) : MetaM ImplEntry := asking do
  let t ← readWhnf (← getConstInfo c.name).type
  let deliverable := match t with
    | .app (.app (.const ``Implementation _) _) d => constOf? d
    | _ => none
  return ⟨c.module, c.name, deliverable⟩

def entryOf (decl : Implementation.Constant) : MetaM Entry := asking do
  let t ← readWhnf (← getConstInfo decl.name).type
  let .app (.app (.const ``Required _) _) d := t
    | throwError "the type of {decl.name} is not `LeanIntent.Required` applied to a deliverable"
  let args ← ctorArgs (← Confirmation.Read.constOf decl.name) ``Required.mk 10
  let o2 ← citedProof args[2]
  let o2Run ← readO2Run args[3]
  let o3 ← citedProof args[4]
  let o4 ← citedProof args[5]
  let o5 ← citedProof args[7]
  let comparison ← readComparison args[8]
  let additional ← (← listElems args[9]).mapM citedOf
  return ⟨decl.name, decl.module, constOf? d, o2, o2Run, o3, o4, o5, comparison, additional.toList⟩

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
  let ds ← (of ``Deliverable).mapM deliverableEntryOf
  let vs ← (of ``Implementation).mapM implEntryOf
  let rs ← (of ``Required).mapM entryOf
  return report built.toList ds.toList vs.toList rs.toList

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
