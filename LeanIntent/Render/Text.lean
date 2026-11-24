module

public import Lean
public import LeanIntent.Explain
public import LeanIntent.Print
public import LeanIntent.Print.Meaning
public import LeanIntent.Cone
public import LeanIntent.Generic
public import LeanIntent.Loaded

public section

namespace LeanIntent.Render

open Lean Meta Elab LeanIntent.Print
open LeanIntent.Cone (exprRefs)

@[expose] def explicitOnly : Expr → Bool
  | .forallE _ _ b bi => bi.isExplicit && explicitOnly b
  | _ => true

@[expose] def bareConsts (env : Environment) (_h : Loaded env) (c : Name) : Bool :=
  match env.find? c with
  | some ci => explicitOnly ci.type
  | none => false

@[expose] def holdsMatch (env : Environment) (_h : Loaded env) (e : Expr) : Bool :=
  (e.find? fun x => match x with | .const c _ => isMatcherCore env c | _ => false).isSome

@[expose] def equalModuloMatch (env : Environment) (h : Loaded env) : Expr → Expr → Bool
  | .app f1 a1, .app f2 a2 => equalModuloMatch env h f1 f2 && equalModuloMatch env h a1 a2
  | .lam _ t1 b1 bi1, .lam _ t2 b2 bi2 =>
    bi1 == bi2 && equalModuloMatch env h t1 t2 && equalModuloMatch env h b1 b2
  | .forallE _ t1 b1 bi1, .forallE _ t2 b2 bi2 =>
    bi1 == bi2 && equalModuloMatch env h t1 t2 && equalModuloMatch env h b1 b2
  | .letE _ t1 v1 b1 nd1, .letE _ t2 v2 b2 nd2 =>
    nd1 == nd2 && equalModuloMatch env h t1 t2 && equalModuloMatch env h v1 v2 &&
      equalModuloMatch env h b1 b2
  | .proj s1 i1 x1, .proj s2 i2 x2 => s1 == s2 && i1 == i2 && equalModuloMatch env h x1 x2
  | .const c1 us1, .const c2 us2 =>
    if c1 == c2 && us1 == us2 then true
    else isMatcherCore env c1 && isMatcherCore env c2 &&
      Kernel.isDefEqGuarded env {} (.const c1 us1) (.const c2 us2)
  | .bvar i1, .bvar i2 => i1 == i2
  | .fvar id1, .fvar id2 => id1 == id2
  | .sort l1, .sort l2 => l1 == l2
  | .lit l1, .lit l2 => l1 == l2
  | .mvar id1, .mvar id2 => id1 == id2
  | _, _ => false

def elaboratesTo (text : String) (e : Expr) (ns : Name := .anonymous)
    (allowMatch : Bool := false) : MetaM Bool := asking do
  match Parser.runParserCategory (← getEnv) `term text with
  | .error _ => return false
  | .ok stx =>
    let lvls := (collectLevelParams {} e).params.toList
    withoutModifyingState do
      try
        let e' ← withTheReader Core.Context
            (fun ctx => { ctx with currNamespace := ns, openDecls := [] }) do
          Term.TermElabM.run' <| Term.withLevelNames lvls <| Term.withoutErrToSorry do
            let e' ← Term.elabTerm stx none
            Term.synthesizeSyntheticMVarsNoPostponing
            instantiateMVars e'
        if e'.hasMVar then return false
        let e1 := eraseNames (eraseMData e')
        let e2 := eraseNames (eraseMData e)
        if e1.equal e2 then return true
        unless allowMatch do return false
        askingIn fun env h => do
          unless holdsMatch env h e do return false
          return equalModuloMatch env h e1 e2
      catch _ => return false

def printExact (e : Expr) : MetaM String := askingIn fun env h => do
  let e ← instantiateMVars e
  if e.hasFVar || e.hasMVar || e.hasLooseBVars then
    throwError "cannot print{indentExpr e}\nas it has free or meta variables"
  let ec := canon (constRoots e) [] (eraseMData e)
  let tokens := Parser.getTokenTable env
  let esc : String → Bool := fun s => (tokens.find? s).isSome
  for bare in [bareConsts env h, fun _ => false] do
    match print bare esc ec with
    | none =>
      throwError "cannot print{indentExpr e}\nthe printer refuses it: it holds a projection, \
        a universe metavariable, or a name it cannot write"
    | some text =>
      if ← elaboratesTo text ec then return text
  throwError "cannot print{indentExpr e}\nLean does not elaborate its printed form back to it"

inductive Form where
  | readable
  | exact
  deriving @[expose] BEq

@[expose] def baseOptions (o : Options) : Options :=
  let o := [(`pp.all, false), (`pp.notation, true), (`pp.explicit, false), (`pp.universes, false),
      (`pp.fullNames, false), (`pp.funBinderTypes, true), (`pp.piBinderTypes, true),
      (`pp.letVarTypes, true), (`pp.proofs, true), (`pp.deepTerms, true), (`pp.oneline, false),
      (`pp.mdata, false), (`pp.natLit, false), (`pp.numericTypes, false),
      (`pp.coercions, true), (`pp.fieldNotation, true), (`pp.structureInstances, true),
      (`pp.match, true), (`pp.beta, false), (`pp.tagAppFns, false), (`pp.exprSizes, false)].foldl
    (fun o (n, v) => o.setBool n v) o
  (o.set `pp.maxSteps (1000000 : Nat)).set `format.width (100 : Nat)

@[expose] def readableOptions : List (List (Name × Bool)) :=
  [[], [(`pp.numericTypes, true), (`pp.structureInstanceTypes, true)],
    [(`pp.numericTypes, true), (`pp.coercions, false), (`pp.fieldNotation, false),
      (`pp.structureInstances, false), (`pp.match, false)],
    [(`pp.explicit, true), (`pp.universes, true), (`pp.fieldNotation, false),
      (`pp.structureInstances, false), (`pp.match, false)]]

structure Reader where
  form : Form
  ns : Name := .anonymous
  params : Array Expr := #[]
  own : Array Bool
  notations : IO.Ref NameSet

def Reader.printClosed (R : Reader) (e : Expr) : MetaM String := asking do
  printExact (← mkLambdaFVars R.params e)

def Reader.foreignKinds (R : Reader) (stx : Syntax) : MetaM NameSet := asking do
  let env ← getEnv
  let mut found : NameSet := {}
  for s in stx.topDown do
    let k := s.getKind
    if env.contains k then
      match env.getModuleIdxFor? k with
      | some idx => unless R.own[idx.toNat]?.getD false do found := found.insert k
      | none => found := found.insert k
  return found

def Reader.delabWith (R : Reader) (extra : List (Name × Bool)) (e : Expr) :
    MetaM (String × NameSet) := asking do
  withOptions (fun o => extra.foldl (fun o (n, v) => o.setBool n v) (baseOptions o)) do
    withTheReader Core.Context (fun ctx => { ctx with currNamespace := R.ns, openDecls := [] }) do
      let lctx := (← getLCtx).sanitizeNames.run' { options := (← getOptions) }
      Meta.withLCtx' lctx do
        let stx ← PrettyPrinter.delab e
        let text := (← PrettyPrinter.ppTerm stx).pretty 100
        return (text, ← R.foreignKinds stx)

def fvarDecl (x : Expr) : MetaM LocalDecl := asking do
  let some id := x.fvarId?
    | throwError "expected local variable, found{indentExpr x}"
  id.getDecl

def Reader.print (R : Reader) (e : Expr) : MetaM String := asking do
  let e ← instantiateMVars e
  if e.hasMVar || e.hasLooseBVars || (e.hasFVar && R.params.isEmpty) then
    throwError "cannot print{indentExpr e}\nas it has free or meta variables"
  if R.form == .exact then return ← R.printClosed e
  let locals ← R.params.toList.filterMapM fun x => do
    let d ← fvarDecl x
    if e.containsFVar d.fvarId then return some d.userName else return none
  let ec := canon (constRoots e ++ locals) [] (eraseMData e)
  for extra in readableOptions do
    let attempt ← observing? (R.delabWith extra ec)
    if let some (text, kinds) := attempt then
      if ← elaboratesTo text ec R.ns (allowMatch := true) then
        R.notations.modify (kinds.foldl .insert ·)
        return text
  R.printClosed e

@[expose] def kernelReduction (env : Environment) (_h : Loaded env) (lctx : LocalContext) (e : Expr) :
    Except Kernel.Exception { result : Expr // Kernel.whnf env lctx e = .ok result } :=
  match Kernel.whnf env lctx e with
  | .ok result => .ok ⟨result, rfl⟩
  | .error ex => .error ex

theorem kernelReduction_result (env : Environment) (h : Loaded env) (lctx : LocalContext)
    (e : Expr) : (kernelReduction env h lctx e).map Subtype.val = Kernel.whnf env lctx e := by
  unfold kernelReduction
  generalize Kernel.whnf env lctx e = result
  cases result <;> rfl

@[expose] def kernelIsDefEq (env : Environment) (_h : Loaded env) (lctx : LocalContext) (a b : Expr) :
    Except Kernel.Exception { ok : Bool // Kernel.isDefEq env lctx a b = .ok ok } :=
  match Kernel.isDefEq env lctx a b with
  | .ok ok => .ok ⟨ok, rfl⟩
  | .error ex => .error ex

theorem kernelIsDefEq_result (env : Environment) (h : Loaded env) (lctx : LocalContext)
    (a b : Expr) : (kernelIsDefEq env h lctx a b).map Subtype.val = Kernel.isDefEq env lctx a b := by
  unfold kernelIsDefEq
  generalize Kernel.isDefEq env lctx a b = result
  cases result <;> rfl

def readWhnf (e : Expr) : MetaM Expr := askingIn fun env h => do
  match kernelReduction env h (← getLCtx) e with
  | .ok result => return result.val
  | .error _ => throwError "Lean's kernel could not reduce{indentExpr e}"

def ctorArgs (e : Expr) (ctor : Name) (n : Nat) : MetaM (Vector Expr n) := asking do
  let e ← readWhnf e
  unless e.isAppOfArity ctor n do
    throwError "expected {.ofConstName ctor} applied to {n} arguments, found{indentExpr e}"
  let args := e.getAppArgs
  if h : args.size = n then
    return ⟨args, h⟩
  throwError "expected {.ofConstName ctor} applied to {n} arguments, found {args.size}"

def listElems (e : Expr) : MetaM (Array Expr) := asking <|
  go (2 ^ 64) #[] e
where
  go (fuel : Nat) (acc : Array Expr) (e : Expr) : MetaM (Array Expr) := asking do
    match fuel with
    | 0 => throwError "list has more than 2 ^ 64 elements"
    | fuel + 1 =>
      let e ← readWhnf e
      match e with
      | .app (.app (.app (.const ``List.cons _) _) head) tail =>
        go fuel (acc.push head) tail
      | .app (.const ``List.nil _) _ => return acc
      | _ => throwError "expected a list, found{indentExpr e}"

def readNatBelow (bound : Nat) (e : Expr) : MetaM Nat := asking <|
  go (bound + 1) 0 e
where
  go (fuel acc : Nat) (e : Expr) : MetaM Nat := asking do
    match fuel with
    | 0 => throwError "expected a natural number below {bound}, found{indentExpr e}"
    | fuel + 1 =>
      match ← readWhnf e with
      | .lit (.natVal n) =>
        if acc + n < bound then return acc + n
        throwError "expected a natural number below {bound}, found {acc + n}"
      | .const ``Nat.zero _ =>
        if acc < bound then return acc
        throwError "expected a natural number below {bound}, found {acc}"
      | .app (.const ``Nat.succ _) prev =>
        if acc + 1 < bound then go fuel (acc + 1) prev
        else throwError "expected a natural number below {bound}, found at least {acc + 1}"
      | e => throwError "expected a natural number below {bound}, found{indentExpr e}"

def readByte (e : Expr) : MetaM UInt8 := asking do
  let u ← ctorArgs e ``UInt8.ofBitVec 1
  let bv ← ctorArgs u[0] ``BitVec.ofFin 2
  let fin ← ctorArgs bv[1] ``Fin.mk 3
  return UInt8.ofNat (← readNatBelow 256 fin[1])

def strLit (e : Expr) : MetaM String := askingIn fun env h => do
  match ← readWhnf e with
  | .lit (.strVal s) => return s
  | .app (.app (.const ``String.ofByteArray _) baExpr) _ =>
    let ba ← ctorArgs baExpr ``ByteArray.mk 1
    let arr ← ctorArgs ba[0] ``Array.mk 2
    let bytes ← (← listElems arr[1]).mapM readByte
    let some s := String.fromUTF8? (ByteArray.mk bytes)
      | throwError "expected a valid UTF-8 string, found{indentExpr e}"
    match kernelIsDefEq env h (← getLCtx) e (.lit (.strVal s)) with
    | .ok ⟨true, _⟩ => return s
    | .ok ⟨false, _⟩ =>
      throwError "Lean's kernel did not find{indentExpr e}\nequal to string literal {repr s}"
    | .error _ =>
      throwError "Lean's kernel could not check{indentExpr e}\nagainst string literal {repr s}"
  | e => throwError "expected a string literal, found{indentExpr e}"

def readGloss (e : Expr) : MetaM (Vector String 4) := asking do
  let parts ← (← ctorArgs e ``Gloss.mk 4).mapM strLit
  for (label, s) in #v["requires", "rules out", "still allows", "freedom"].zip parts do
    if s.trimAscii.isEmpty then throwError "the gloss's part on what it {label} is empty"
  return parts

def readIdent (e : Expr) : MetaM Ident := asking do
  let s ← strLit (← ctorArgs e ``Word.mk 3)[1]
  if h : s.toList ≠ [] ∧ s.toList.all identChar = true then return ⟨s, h⟩
  throwError "expected a name of the owners' log, found {repr s}"

def readVerdict (e : Expr) : MetaM Verdict := asking do
  let e ← readWhnf e
  if e.isConstOf ``Verdict.confirmed then return .confirmed
  if e.isConstOf ``Verdict.declined then return .declined
  throwError "expected a verdict, found{indentExpr e}"

def readAnswerer (e : Expr) : MetaM Answerer := asking do
  let e ← readWhnf e
  match e with
  | .app (.const ``Answerer.owner _) arg =>
    return .owner (← readIdent arg)
  | .app (.app (.app (.const ``Answerer.onBehalf _) a0) a1) a2 =>
    let reason ← strLit a2
    if reason.trimAscii.isEmpty then
      throwError "the decision on the owner's behalf by{indentExpr a0}\ngives no reason"
    return .onBehalf (← readIdent a0) (← readIdent a1) reason
  | _ => throwError "expected who gave an answer, found{indentExpr e}"

def readRestatement (e : Expr) : MetaM Restatement := asking do
  let e ← readWhnf e
  match e with
  | .const ``Restatement.unconfirmed _ => return .unconfirmed
  | .app (.const ``Restatement.confirmed _) arg => return .confirmed (← readIdent arg)
  | _ => throwError "expected whether a restatement is confirmed, found{indentExpr e}"

def readDerived (s : Restatement) : MetaM (Settled s) := asking <|
  match s with
  | .confirmed _ => pure .derived
  | .unconfirmed => throwError "a consequence of a record whose restatement no owner confirmed is \
      recorded as derived from it"

def readSettled (s : Restatement) (e : Expr) : MetaM (Settled s) := asking do
  let e ← readWhnf e
  match e with
  | .app (.app (.app (.const ``Settled.answered _) _) a1) a2 =>
    return .answered (← readAnswerer a1) (← readVerdict a2)
  | .app (.const ``Settled.fork _) _ => return .fork
  | .app (.const ``Settled.unsettled _) _ => return .unsettled
  | .app (.const ``Settled.derived _) _ => return ← readDerived s
  | _ => throwError "expected who settled a consequence, found{indentExpr e}"

@[expose] def fence (text : String) : String :=
  let longest := (text.toList.foldl (fun (run, best) c =>
    if c = '`' then (run + 1, max best (run + 1)) else (0, best)) (0, 0)).2
  String.ofList (List.replicate (max 3 (longest + 1)) '`')

@[expose] def code (text : String) : String :=
  let f := fence text
  s!"{f}lean\n{text}\n{f}\n"

@[expose] def statement (heading text : String) (gloss : Vector String 4) (settled : String := "") : String :=
  s!"### {heading}\n\n{code text}\n{settled}- **Requires:** {gloss[0]}\n\
    - **Rules out:** {gloss[1]}\n- **Still allows:** {gloss[2]}\n\
    - **Freedom O5 leaves:** {gloss[3]}\n\n"

@[expose] def leanRoots : List Name := [`Init, `Std, `Lean, `Lake]

@[expose] def isLeanOwn (lib : List String) (m : Name) (real? : Option System.FilePath) : Bool :=
  leanRoots.contains m.getRoot && real?.any fun p => lib.isPrefixOf p.components

theorem isLeanOwn_iff {lib : List String} {m : Name} {real? : Option System.FilePath} :
    isLeanOwn lib m real? = true ↔
      m.getRoot ∈ leanRoots ∧ ∃ p, real? = some p ∧ lib <+: p.components := by
  cases real? <;> simp [isLeanOwn]

def realOLean? (m : Name) : IO (Option System.FilePath) := do
  (← (← searchPathRef.get).findModuleWithExt "olean" m).mapM IO.FS.realPath

def leanLibDir : IO System.FilePath := do
  let refuse {α} (why : String) : IO α := throw <| IO.userError
    s!"cannot find Lean's own libraries from the search path: {why}. The process must set its search \
      path (Lean.initSearchPath, or Lean.searchPathRef) to the one it imports the project through"
  let some prelude ← realOLean? `Init.Prelude
    | refuse "it gives Init.Prelude no file"
  let some lib := prelude.parent >>= (·.parent)
    | refuse s!"{prelude} has no parent directory"
  for root in leanRoots do
    let file := modToFilePath lib root "olean"
    unless ← file.pathExists do
      refuse s!"{lib}, which holds Init.Prelude, has no {file.fileName.getD ""}"
    unless (← IO.FS.realPath file).parent == some lib do
      refuse s!"{file}, beside the Init.Prelude it gives, is a link to another directory"
  return lib

def leanOwnModules : MetaM (Array Bool) := asking do
  let lib := (← leanLibDir).components
  (← getEnv).header.modules.mapM fun imp => do
    let m := imp.module
    return isLeanOwn lib m (← if leanRoots.contains m.getRoot then realOLean? m else pure none)

@[expose] def stopAt (env : Environment) (own : Array Bool) (shown : NameSet) (c : Name) : Bool :=
  shown.contains c ||
    match env.getModuleIdxFor? c with
    | some idx => own[idx.toNat]?.getD false
    | none => false

@[expose] def univWords : List Name → String
  | [] => "no universe parameter"
  | [u] => s!"the universe parameter {u}"
  | us => s!"the universe parameters {", ".intercalate (us.map toString)}, in that order"

def printPart (R : Reader) (c : Name) (part : String) (e : Expr) : MetaM String := asking do
  try R.print e
  catch err => throwError "cannot print the {part} of {c}: {err.toMessageData}"

@[expose] def projShape : Expr → Option (Nat × Name × Nat)
  | .lam _ _ (.proj s i (.bvar 0)) _ => some (1, s, i)
  | .lam _ _ b _ => (projShape b).map fun (n, s, i) => (n + 1, s, i)
  | _ => none

@[expose] def lamSkel : Nat → Expr → Expr
  | 0, b => b
  | n + 1, b => .lam .anonymous (.sort .zero) (lamSkel n b) .default

@[expose] def eraseLams : Expr → Expr
  | .lam _ _ b _ => .lam .anonymous (.sort .zero) (eraseLams b) .default
  | e => e

theorem eraseLams_of_projShape {e : Expr} {n : Nat} {s : Name} {i : Nat}
    (h : projShape e = some (n, s, i)) : eraseLams e = lamSkel n (.proj s i (.bvar 0)) := by
  induction e generalizing n with
  | lam x t b bi _ ih =>
    unfold projShape at h
    split at h
    · rename_i heq
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Expr.lam.inj heq
      cases h
      rfl
    · rename_i heq
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Expr.lam.inj heq
      cases hb : projShape b with
      | none => simp [hb] at h
      | some d =>
        obtain ⟨m, s', i'⟩ := d
        simp only [hb, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        simp only [eraseLams, lamSkel, ih hb]
    · contradiction
  | _ => simp [projShape] at h

theorem projShape_determines {e₁ e₂ : Expr} {d : Nat × Name × Nat}
    (h₁ : projShape e₁ = some d) (h₂ : projShape e₂ = some d) : eraseLams e₁ = eraseLams e₂ := by
  obtain ⟨n, s, i⟩ := d
  rw [eraseLams_of_projShape h₁, eraseLams_of_projShape h₂]

@[expose] def projectionOf (lookup : Name → Option ConstantInfo) (v : DefinitionVal) :
    Option (Nat × Name × Nat) :=
  match projShape (eraseMData v.value) with
  | some (n, s, i) =>
    match lookup s with
    | some (.inductInfo iv) =>
      match iv.ctors, iv.all with
      | [k], [_] =>
        match lookup k with
        | some (.ctorInfo kv) =>
          if iv.numIndices = 0 ∧ i < kv.numFields then some (n, s, i) else none
        | _ => none
      | _, _ => none
    | _ => none
  | none => none

section Recursion

universe u v

theorem eq_of_recursion_eqn {α : Sort u} {β : α → Sort v} {r : α → α → Prop} (hr : WellFounded r)
    (F : (x : α) → ((y : α) → r y x → β y) → β x) {f g : (x : α) → β x}
    (hf : ∀ x, f x = F x fun y _ => f y) (hg : ∀ x, g x = F x fun y _ => g y) : f = g :=
  funext fun x => hr.induction (C := fun x => f x = g x) x fun x ih => by
    rw [hf x, hg x]
    congr 1
    funext y h
    exact ih y h

end Recursion

@[expose] def recursionKind (env : Environment) (_h : Loaded env) (c : Name) : Option Bool :=
  if (Elab.Structural.eqnInfoExt.find? env c).isSome then some true
  else if (Elab.WF.eqnInfoExt.find? env c).isSome then some false
  else none

@[expose] def unfoldsTo (c : Name) (us : List Level) : Nat → Expr → Bool
  | k, .forallE _ _ b _ => unfoldsTo c us (k + 1) b
  | k, .app (.app (.app (.const ``Eq _) _) lhs) _ =>
      lhs == mkAppN (.const c us) ((List.range k).reverse.map Expr.bvar).toArray
  | _, _ => false

private def importedModule? (env : Environment) (_h : Loaded env) (c : Name) :
    Option EffectiveImport :=
  (env.getModuleIdxFor? c).bind fun idx => env.header.modules[idx.toNat]?

private def throwUnexposedDef {α : Type} (c : Name) (isRec : Bool) : MetaM α :=
    askingIn fun env h => do
  let kind := if isRec then "a recursive definition" else "a definition"
  match importedModule? env h c with
  | some imp =>
    if env.header.isModule && !imp.isExported && isRec then
      throwError "cannot print {c}: its body is not exposed in {imp.module}, and its module \
        {imp.module} is imported without `public`; mark {c} with `@[expose]` in {imp.module}, \
        and in a `module` file use `public import {imp.module}` (or `public import` a module \
        that publicly re-exports it) when printing a recursive definition by its equation"
    else
      let extra := if isRec then " or equation" else ""
      throwError "cannot print {c}: it is {kind} whose body is not exposed in {imp.module}, \
        so Lean shows it as an axiom without its body{extra}; mark {c} with `@[expose]` in \
        {imp.module}"
  | none =>
    throwError "cannot print {c}: it is {kind} whose body is not exposed, so Lean shows it as \
      an axiom without its body; mark {c} with `@[expose]`"

def unfoldEqn (c : Name) (levels : List Name) : MetaM (Name × Expr) := askingIn fun env h => do
  if ((env.setExporting false).find? c) matches some (.axiomInfo _) && wasOriginallyDefn env c then
    throwUnexposedDef c (← isRecursiveDefinition c)
  if env.header.isModule then
    if let some imp := importedModule? env h c then
      unless imp.isExported do
        throwError "cannot print {c}: its module {imp.module} is imported without `public`; \
          in a `module` file, use `public import {imp.module}` (or `public import` a module \
          that publicly re-exports it)"
  let eq? ← try getUnfoldEqnFor? c (nonRec := false)
    catch err => throwError "cannot print {c}: Lean cannot state its equation: {err.toMessageData}"
  let some eq := eq?
    | throwError "cannot print {c}: Lean gives no equation that unfolds it"
  let some eci := ((← getEnv).setExporting false).find? eq
    | throwError "cannot print {c}: its equation {eq} has no declaration here"
  unless eci.levelParams == levels && unfoldsTo c (levels.map .param) 0 eci.type do
    throwError "cannot print {c}: its equation {eq} does not state its value at every argument"
  let axs ← collectAxioms eq
  unless axs.all LeanIntent.Cone.leanAxioms.contains do
    throwError "cannot print {c}: it or its equation {eq} rests on the axioms {axs.toList}, not \
      only on Lean's own, so its termination proof, if any, may not be one"
  return (eq, eci.type)

def declSection (R : Reader) (lookup : Name → Option ConstantInfo)
    (out : List (Name × ConstantInfo)) (eqns : NameMap (Name × Expr)) (c : Name)
    (ci : ConstantInfo) : MetaM (Option String) := asking do
  let has (n : Name) : Bool := out.any (·.1 == n)
  match ci with
  | .ctorInfo v =>
    unless has v.induct do throwError "cannot print {c}: its inductive type is not printed"
    return none
  | .recInfo v =>
    unless v.all.all has do throwError "cannot print {c}: its inductive types are not printed"
    return none
  | _ => pure ()
  let type ← printPart R c "type" ci.type
  let head (words : String) :=
    s!"### {c}\n\n{words}. It has {univWords ci.levelParams}. Its type:\n\n{code type}\n"
  match ci with
  | .ctorInfo _ | .recInfo _ => return none
  | .defnInfo v =>
    if let some (eq, t) := eqns.find? c then
      let rk ← askingIn fun env h => pure (recursionKind env h c)
      let (kind, shows, below) := if rk == some true then
          ("structural recursion", "", "at structural subterms of the arguments it recurses on")
        else ("well-founded recursion", "its termination proof shows that ",
          "at arguments below those on the left by a well-founded relation")
      return some (head s!"A definition by {kind}" ++ s!"Its value is not printed: Lean \
        compiles a definition by recursion into a term its syntax cannot write. In its place is \
        the equation Lean proves for it, `{eq}`, which Lean's kernel checked, stating its value at \
        every argument:\n\n{code (← printPart R c "equation" t)}\nThe equation determines {c}: Lean \
        accepts a definition by {kind} only when {shows}the right of the equation uses the values \
        of {c}, and of any function defined together with it, only {below}, so only one \
        function, or family of functions defined together, satisfies their equations. {c} and \
        its equation rest on no axiom but Lean's own.\n\n")
    match projectionOf lookup v with
    | some (n, s, i) =>
      return some (head s!"A function that reads a field of a structure: its value is `fun` over \
        its first {n} arguments and returns field number {i + 1}, counted after the parameters in \
        the type of {s}'s constructor, of its argument number {n}, a value of {s}")
    | none =>
      let value ← printPart R c "value" v.value
      return some (head "A definition" ++ s!"Its value:\n\n{code value}\n")
  | .thmInfo _ =>
    return some (head "A theorem, whose proof is not printed: any two proofs of a proposition are \
      equal by definitional proof irrelevance, so a term that uses it depends on nothing but its \
      statement")
  | .opaqueInfo _ =>
    return some (head "An opaque constant, whose value is not printed: Lean's kernel never unfolds \
      it, so a term that uses it depends on nothing but its type")
  | .axiomInfo v =>
    unless ← isProp v.type do
      if wasOriginallyDefn (← getEnv) c then
        throwUnexposedDef c (← isRecursiveDefinition c)
      throwError "cannot print {c}: it is an axiom whose type is not a proposition, whose meaning \
        is not all in its type; in a module of Lean's module system, Lean shows an imported \
        definition whose body is not exposed this way"
    return some (head "An axiom of a proposition: a term that uses it depends on nothing but its \
      statement, as for a theorem, which is how Lean's module system shows an imported theorem")
  | .quotInfo _ =>
    return some (head "A primitive of quotient types, which Lean's kernel defines")
  | .inductInfo v =>
    let words := if isStructure (← getEnv) c then "A structure: an inductive type with one \
        constructor, whose arguments after its parameters are the structure's fields, in order"
      else "An inductive type"
    let mut s := head words ++ s!"Of the arguments its type takes, the first {v.numParams} are \
      parameters and the other {v.numIndices} indices."
    if v.all.length > 1 then
      s := s ++ s!" It is declared in one block of mutually inductive types, \
        {", ".intercalate (v.all.map toString)}, each printed here."
    s := s ++ " Its recursor is the one Lean's kernel derives from this declaration."
    if v.ctors.isEmpty then return some (s ++ " It has no constructor.\n\n")
    s := s ++ " Its constructors, in order, each with its type:\n\n"
    for k in v.ctors do
      match lookup k with
      | some (.ctorInfo kv) => s := s ++ s!"#### {k}\n\n{code (← printPart R k "type" kv.type)}\n"
      | _ => throwError "cannot print {c}: its constructor {k} has no declaration here"
    return some s

@[expose] def toolchain : String :=
  s!"## Lean's own libraries\n\nThe declarations of Lean's own libraries (Init, Std, Lean and \
    Lake) are not printed: they are those of Lean {Lean.versionString}, commit {Lean.githash}, \
    which made this text. A declaration is counted as Lean's own when Lean found the module that \
    declares it in that release's library directory.\n"

def definitions (R : Reader) (roots : List Name) (shown : NameSet) : MetaM String := asking do
  let own := R.own
  let env₀ ← getEnv
  let limit := env₀.constants.map₂.foldl (fun k _ _ => k + 1) env₀.constants.map₁.size + 1
  let mut eqns : NameMap (Name × Expr) := {}
  for _ in [0 : limit] do
    let (out, todo) ← askingIn fun env h => do
      let lookup := fun c => (env.setExporting false).find? c
      let stop := stopAt env own shown
      let found := eqns
      let eqn := fun c => match found.find? c with
        | some (_, t) => .eqn t
        | none => if (recursionKind env h c).isSome then .typeOnly else .value
      let bound := env.constants.map₂.foldl (fun k _ _ => k + 1) env.constants.map₁.size + 1
      let out ← match meaning lookup eqn stop bound roots with
        | .ok out => pure out
        | .error (.unknown c) => throwError "cannot print {c}: it has no declaration here"
        | .error .fuel => throwError "cannot print the definitions: there are too many"
      let todo ← out.filterM fun (c, ci) => do
        if found.contains c then return false
        match ci with
        | .defnInfo _ => return (recursionKind env h c).isSome
        | .axiomInfo v =>
          if wasOriginallyDefn env c && (← isRecursiveDefinition c) then
            return !(← isProp v.type)
          else return false
        | _ => return false
      pure (out, todo)
    if todo.isEmpty then
      let env ← getEnv
      let lookup := fun c => (env.setExporting false).find? c
      let isLibrary (c : Name) : Bool := R.form == .readable &&
        match env.getModuleIdxFor? c with
        | some idx => (env.header.modules[idx.toNat]?.map (·.module.getRoot)) == some `LeanIntent
        | none => false
      let isGenerated (c : Name) : Bool := R.form == .readable &&
        (isMatcherCore env c || isCasesOnRecursor env c)
      let mut text := ""
      let mut generated := ""
      let mut library := ""
      for (c, ci) in out do
        if let some s ← declSection R lookup out eqns c ci then
          if isLibrary c then library := library ++ s
          else if isGenerated c then generated := generated ++ s
          else text := text ++ s
      let folded (heading words body : String) : String :=
        if body.isEmpty then "" else s!"## {heading}\n\n{words} They are folded, not left out.\n\n\
          <details>\n<summary>Each of them, printed in full</summary>\n\n{body}</details>\n\n"
      return text ++ folded "The code Lean generated for each `match`" "Lean compiles each `match` \
          into these; the definitions above show the `match` as Lean reads it." generated ++
        folded "lean-intent's own definitions" "These say what a record is and what it is to meet \
          one, the same in every rendering that reaches them." library
    for (c, ci) in todo do
      eqns := eqns.insert c (← unfoldEqn c ci.levelParams)
  throwError "cannot print the definitions: unfolding equations exceeded constant bound"

def kindWords (e : Expr) : MetaM (Expr × String) := asking do
  let kind ← readWhnf e
  if kind.isConstOf ``Consequence.Kind.entailment then
    return (kind, "an entailment: every subject that meets the record satisfies it")
  else if kind.isConstOf ``Consequence.Kind.possibility then
    return (kind, "a possibility: some subject that meets the record satisfies it")
  else throwError "expected the kind of a consequence, found{indentExpr kind}"

@[expose] def formWords (R : Reader) : String :=
  match R.form with
  | .exact => "Each statement is printed exactly: as Lean syntax that Lean elaborates back to the \
      term its kernel checks, binder names and metadata aside, from the root namespace with \
      nothing opened."
  | .readable =>
    let where_ := if R.ns.isAnonymous then "from the root namespace" else s!"in the namespace {R.ns}"
    s!"Each statement is printed with Lean's notation, leaving out what Lean infers: as Lean syntax \
      that Lean elaborates back to the term its kernel checks, binder names and metadata aside, \
      {where_} with nothing opened. Where Lean does not read a shorter print back, a more explicit \
      one is shown, and last the exact form, read from the root namespace with nothing opened."

@[expose] def instanceNote (f : Name) : String :=
  s!"These are the statements of {f} with its parameters replaced by these values, read from {f} \
    applied to them, and they speak of these values only. An obligation proved here shows only that \
    some parameter has it (`{``LeanIntent.Family.exists_of_at}`), a failure here refutes a generic \
    claim whose condition admits these values (`{``LeanIntent.Family.not_holdsWhere_of_at}`), and \
    an instance alone does not in general prove an obligation of a family: \
    `{``LeanIntent.Family.not_generic}` gives, for each, a family of which it holds at \
    one parameter and fails at another.\n\n"

def binderText (R : Reader) (x : Expr) : MetaM String := asking do
  let d ← fvarDecl x
  let type ← R.print d.type
  let (l, r) := match d.binderInfo with
    | .default => ("(", ")")
    | .implicit => ("{", "}")
    | .strictImplicit => ("⦃", "⦄")
    | .instImplicit => ("[", "]")
  let name := d.userName
  if d.binderInfo.isInstImplicit && name.hasMacroScopes then return s!"{l}{type}{r}"
  return s!"{l}{name.eraseMacroScopes} : {type}{r}"

def paramsPart (R : Reader) : MetaM String := asking do
  if R.params.isEmpty then return ""
  let lines ← R.params.mapM (binderText R)
  return s!"## Parameters\n\nThis record is generic. Every statement below is about every value \
    of these parameters, which appear in it as variables:\n\n{code ("\n".intercalate lines.toList)}\n"

inductive Statuses where
  | recorded
  | omitted
  | given (restatement : String) (consequences : Array String)

def recordPart (R : Reader) (exTerm : Expr) (note : String := "") (statuses : Statuses := .recorded) :
    MetaM (String × List Name × NameSet) := asking do
  let ex ← ctorArgs exTerm ``Explanation.mk 11
  let r ← ctorArgs ex[1] ``IntentRecord.mk 5
  let restatement ← readRestatement ex[6]
  let note := match ex[1].getAppFn with
    | .const f _ =>
      if note.isEmpty && R.form == Form.readable && R.params.isEmpty && ex[1].isApp &&
          f != ``IntentRecord.mk then instanceNote f else note
    | _ => note
  let confirmedPart (intro words : String) : String × String :=
    (s!" {intro}", s!"## Whether an owner confirmed this restatement\n\n{words}\n")
  let (standing, confirmed) := match statuses with
    | .recorded => confirmedPart "Who settled each thing is printed as this record holds it; \
        `LeanIntent.Trace` decides, from a project's owners' log, whether an answer's authority \
        traces back to a declared owner, and this document does not."
        (String.ofList restatement.words)
    | .omitted => ("", "")
    | .given words _ => confirmedPart "Who settled each thing is printed as the project's owners' \
        log holds it for this revision." words
  let mut doc := s!"# The intent record {← R.print ex[1]}\n\n{formWords R} The plain words after \
    it are written by a model and are trusted, not proved.{standing}\n\n{note}\
    {← paramsPart R}{confirmed}## Shape\n\n"
  let mut printed : Array Expr := #[ex[1]]
  for x in R.params do
    printed := printed.push (← fvarDecl x).type
  doc := doc ++ statement "The subject" (← R.print r[1]) (← readGloss ex[2])
  printed := printed.push r[1]
  for (title, items, glosses, ctor) in
      [("Domain hypotheses", r[2], ex[3], ``Clause.mk), ("Properties", r[3], ex[4], ``Clause.mk),
        ("Vocabulary", r[4], ex[5], ``Pred.mk)] do
    let items ← listElems items
    let glosses ← listElems glosses
    unless items.size == glosses.size do
      throwError "{title}: the record has {items.size} and the explanation {glosses.size} glosses"
    doc := doc ++ s!"## {title}\n\n"
    if items.isEmpty then doc := doc ++ "None.\n\n"
    for (item, gloss) in items.zip glosses do
      let a ← ctorArgs item ctor 3
      if ctor == ``Pred.mk then
        let heading := s!"{← strLit a[0]}, a predicate over `{← R.print a[1]}`"
        doc := doc ++ statement heading (← R.print a[2]) (← readGloss gloss)
        printed := printed ++ #[a[1], a[2]]
      else
        doc := doc ++ statement (← strLit a[1]) (← R.print a[2]) (← readGloss gloss)
        printed := printed.push a[2]
  doc := doc ++ match statuses with
    | .omitted => "## Consequences\n\n"
    | _ => "## Consequences, each with who settled it\n\n"
  let consequences ← listElems ex[7]
  if consequences.isEmpty then doc := doc ++ "None.\n\n"
  if let .given _ words := statuses then
    unless words.size == consequences.size do
      throwError "{consequences.size} consequences and words for {words.size}"
  for h : i in [:consequences.size] do
    let shown := consequences[i]
    let s ← ctorArgs shown ``Shown.mk 7
    let c ← ctorArgs s[3] ``Consequence.mk 4
    let (_, shownAs) ← kindWords c[2]
    let settled ← match statuses with
      | .recorded => pure s!"- **Settled:** {String.ofList (← readSettled restatement s[6]).words}"
      | .omitted => pure ""
      | .given _ words =>
        let some w := words[i]?
          | throwError "{consequences.size} consequences and words for {words.size}"
        pure s!"- **Settled:** {w}"
    doc := doc ++ statement s!"{← strLit c[1]}, {shownAs}" (← R.print c[3]) (← readGloss s[5])
      settled
    printed := printed.push c[3]
  let shown : NameSet := if let .const c _ := ex[1].getAppFn then ({} : NameSet).insert c else {}
  let roots := printed.toList.flatMap (exprRefs · []) ++ [``IntentRecord.Meets] ++
    if consequences.isEmpty then [] else [``Consequence.HoldsOf]
  return (doc, roots, shown)

def notationPart (R : Reader) : MetaM String := asking do
  let kinds := (← R.notations.get).toList
  if kinds.isEmpty then return ""
  let env ← getEnv
  let lines ← kinds.mapM fun k => do
    match env.getModuleIdxFor? k with
    | some idx =>
      let some md := env.header.modules[idx.toNat]?
        | throwError "unknown module index {idx.toNat} for notation {k}"
      return s!"- `{k}`, declared in {md.module}\n"
    | none => return s!"- `{k}`, declared in the file that made this text\n"
  return s!"## Notation from outside Lean's own libraries\n\nThe statements above use this notation, \
    whose declaration this text does not print. Lean read each statement back as the term its \
    kernel checks, so the notation changes nothing Lean checks; what it means to a reader is in its \
    source, and the exact form of this text (`#render_intent_exact`) prints each statement without \
    it.\n\n{String.join lines}\n"

def definitionsPart (R : Reader) (roots : List Name) (shown : NameSet) : MetaM String := asking do
  return s!"## Definitions the record's meaning reaches\n\nThese are not statements of the \
    record: each is a declaration that a statement above depends on, or that says what it is for \
    a subject to meet the record and for a consequence to hold of it as shown, with everything \
    those depend on in turn. Each is printed in full: its type, a definition's value, or for a \
    definition by structural or well-founded recursion the equation that determines it, and an \
    inductive type's constructors, which for a structure are its fields; a theorem's proof and an \
    opaque constant's value are not, since no term that uses them depends on more than their \
    types. Their plain words are those of the statements that use them.\n\n\
    {← definitions { R with params := #[] } roots shown}{← notationPart R}{toolchain}"

def newReader (decl : Name) (form : Form) (params : Array Expr := #[]) : MetaM Reader := asking do
  return { form, ns := if form == .exact then .anonymous else decl.getPrefix, params,
           own := ← leanOwnModules, notations := ← IO.mkRef {} }

def withExplanationTelescope {α : Type} (type : Expr) (k : Array Expr → Expr → MetaM α) :
    MetaM α := asking <|
  go (2 ^ 64) #[] type
where
  go (fuel : Nat) (acc : Array Expr) (e : Expr) : MetaM α := asking do
    match fuel with
    | 0 => throwError "explanation type has more than 2 ^ 64 nested forall telescopes"
    | fuel + 1 =>
      let e ← readWhnf e
      if e.isForall then
        forallTelescope e fun xs body =>
          go fuel (acc ++ xs) body
      else
        k acc e

def isExplanationType (type : Expr) : MetaM Bool := asking <|
  withExplanationTelescope type fun _ body =>
    pure (body.getAppFn.isConstOf ``Explanation)

def renderExplanation (decl : Name) (form : Form := .readable) (statuses : Statuses := .recorded) :
    MetaM String := asking do
  let ci ← getConstInfo decl
  let us := ci.levelParams.map Level.param
  let reader ← newReader decl form
  let (doc, roots, shown) ← withExplanationTelescope ci.type fun params body => do
    unless body.getAppFn.isConstOf ``Explanation do
      throwError "{decl} does not have an explanation type"
    recordPart { reader with params } (mkAppN (mkConst decl us) params) (statuses := statuses)
  return doc ++ (← definitionsPart reader roots shown)

def renderAt (decl : Name) (us : List Level) (args : Array Expr) : MetaM String := asking do
  let ci ← getConstInfo decl
  unless ← isExplanationType ci.type do
    throwError "{decl} does not have an explanation type"
  let reader ← newReader decl .readable
  let binders ← withExplanationTelescope (ci.type.instantiateLevelParams ci.levelParams us)
    fun params body => do
      unless body.getAppFn.isConstOf ``Explanation do
        throwError "{decl} does not have an explanation type"
      unless params.size == args.size do
        throwError "{decl} takes {params.size} parameters here, and was given {args.size}"
      params.mapM fun x => return (← fvarDecl x).userName.eraseMacroScopes
  let mut lines : Array String := #[]
  let mut roots : List Name := []
  for (name, a) in binders.zip args do
    let proof ← isProof a
    let term ← instantiateMVars (← if proof then inferType a else pure a)
    let printed ← reader.print term
    lines := lines.push <|
      if proof then s!"{name} : a proof of {printed}" else s!"{name} := {printed}"
    roots := exprRefs term roots
  let values := s!"## Representative values\n\nThis record is generic, and this text shows it at \
    these values of its parameters:\n\n{code ("\n".intercalate lines.toList)}\n{instanceNote decl}"
  let (doc, rootsDoc, shown) ← recordPart reader (mkAppN (mkConst decl us) args) values
  return doc ++ (← definitionsPart reader (rootsDoc ++ roots) shown)

def revisionText (decl : Name) : MetaM String := asking <|
  renderExplanation decl .exact .omitted

@[expose] def consequenceHeading : String := "# A consequence's predicate"

@[expose] def consequenceBody (predText defsText : String) : String :=
  consequenceHeading ++
    s!"\n\nPrinted exactly: as Lean syntax that Lean elaborates back \
    to the term its kernel checks, binder names and metadata aside, from the root namespace with \
    nothing opened.\n\n{code predText}\n## Definitions the predicate reaches\n\nEach \
    is printed in full, as in the rendering of a record, with what an answer to it asks of every \
    later revision (`LeanIntent.Answer.KeptBy`).\n\n\
    {defsText}{toolchain}"

theorem consequenceBody_prefix (predText defsText : String) :
    consequenceHeading.toList <+: (consequenceBody predText defsText).toList := by
  rw [consequenceBody, String.toList_append]
  exact List.prefix_append _ _

def consequenceTextVerified (pred : Expr) :
    MetaM { s : String // ∃ p d, s = consequenceBody p d } := asking do
  let p ← printExact pred
  let d ← definitions (← newReader .anonymous .exact) (exprRefs pred [] ++ [``Answer.KeptBy]) {}
  return ⟨consequenceBody p d, p, d, rfl⟩

def consequenceText (pred : Expr) : MetaM String := asking do
  return (← consequenceTextVerified pred).1

def answerText (ex : Name) (a : Expr) : MetaM String := asking do
  let exInfo ← getConstInfo ex
  unless ← isExplanationType exInfo.type do
    throwError "{ex} does not have an explanation type"
  let attributed ← ctorArgs a ``Attributed.mk 3
  let answerer ← readAnswerer attributed[2]
  let ans ← ctorArgs attributed[1] ``Answer.mk 3
  let c ← ctorArgs ans[1] ``Consequence.mk 4
  let .const _ aus := (← readWhnf attributed[1]).getAppFn
    | throwError "expected `Answer.mk` constant head"
  let .const _ cus := (← readWhnf ans[1]).getAppFn
    | throwError "expected `Consequence.mk` constant head"
  let nameStr ← strLit c[1]
  let name := Expr.lit (.strVal nameStr)
  let (kind, shownAs) ← kindWords c[2]
  let verdict ← readWhnf ans[2]
  let attribution := answerer.says (← readVerdict verdict)
  let term := mkApp3 (.const ``Answer.mk aus) ans[0]
    (mkApp4 (.const ``Consequence.mk cus) c[0] name kind c[3]) verdict
  let answer := s!"# {answerer.title}\n\n{String.ofList attribution}\nThe consequence \
    answered is {repr nameStr}, shown as {shownAs}. Who gave the answer is printed as this \
    record holds it; `LeanIntent.Trace` decides, from a project's owners' log, whether its \
    authority traces back to a declared owner, and this document does not. The answer, printed \
    exactly: as Lean syntax that Lean elaborates back to the term its kernel checks, binder names \
    and metadata aside, from the root namespace with nothing opened.\n\n\
    {code (← printExact term)}\n"
  let exConst := mkConst ex (exInfo.levelParams.map .param)
  let explained := s!"# The explanation it answers\n\nThe answer is given to the explanation \
    below, printed exactly, whose record and consequences follow as the exact form of its \
    rendering prints them.\n\n{code (← printExact exConst)}\n"
  let reader ← newReader ex .exact
  let (record, roots, shown) ← recordPart reader exConst
  return answer ++ explained ++ record ++ s!"## Definitions the answer and the record reach\n\n\
    These are not statements of the record or of the answer: each is a declaration that the \
    answer or a statement above depends on, or that says what it is for a subject to meet the \
    record, for a consequence to hold of it as shown, and what the answer asks of every later \
    revision of the record (`LeanIntent.Answer.KeptBy`), with everything those depend on in turn, \
    each printed in full as in the exact form of the rendering of a record.\n\n\
    {← definitions reader (roots ++ exprRefs term [] ++ [``Answer.KeptBy]) shown}{toolchain}"

def answerTexts (ex : Name) (e : Expr) : MetaM (Array String) := asking do
  (← listElems e).mapM (answerText ex)

end LeanIntent.Render
