import LeanIntent.Degenerate
import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util

/-!
# The codes of the types a project declares

A structure or inductive type the project declares gets its code from its declaration alone, by
`deriving LeanIntent.HasCode` on the declaration (or `deriving instance LeanIntent.HasCode for T`).
The handler below reads the declaration through Lean's environment, never through its source text,
and writes:

* the code `Ty.decl n ps r` (`instHasCodeT.code`): `n` the type's name, `ps` the chain of the codes
  of its type parameters, and `r` its *representation*: for each constructor in declaration order,
  the chain of its fields' codes in declaration order, each field paired with the chain after it and
  the last with the unit code; a type with one constructor is that chain, and one with several is
  the sum of the first constructor's chain and the representation of the rest;
* the isomorphism between the type and the representation (`instHasCodeT.iso`), which takes the
  `i`-th constructor applied to its fields to the `i`-th alternative of the sum holding each field
  carried through its own type's isomorphism, and back; Lean's kernel checks that each map undoes
  the other;
* the proof that the code stands for the type through that isomorphism (`instHasCodeT.stands`),
  through the private constructor of `Ty.Stands` that admits a declared type, which no other code of
  the library applies;
* the instance of `HasCode` that carries the three.

So a declared type's empty value is its first constructor applied to the empty values of its
fields, the class takes constants at each constructor applied to each combination of values of its
fields' parts, and its projections are the components of its fields when it has one constructor, as
`Ty.decl` delegates to its representation (`LeanIntent.Codes`) and `Ty.projs` descends into the
fields of a declaration with one constructor (`LeanIntent.Degenerate`). Nothing of it is chosen by
the record or by the instance's author.

The handler refuses, and so leaves not covered, every type it cannot represent this way: a recursive,
nested or mutual inductive type, an inductive family with indices, an unsafe type, a type with no
constructor (which has no empty value), a type that does not live in `Type`, a type with a parameter
that is not a type of `Type`, a constructor whose field depends on an earlier field, a field whose
type is not a type of `Type` (a proof field, say) or has no code, and a type that already has a code.
A type whose fields have no code yet gets one once its fields do.

What the handler's output rests on: that it reads the constructors and their fields in declaration
order, which is its own code below and not checked by Lean's kernel; and that no other code applies
the private constructor of `Ty.Stands`. Lean's privacy is a rule of name resolution, so the
`constructor` tactic, which applies a constructor without resolving its name, or a metaprogram that
builds the term directly, can still apply it.
-/

namespace LeanIntent.Declared

open Lean Elab Command Term Meta Parser.Term

/-- The chain of the codes `cs`: each paired with the chain after it, the last with the unit code. -/
def chainCode (cs : List Expr) : Expr :=
  cs.foldr (fun c acc => mkApp2 (mkConst ``Ty.prod) c acc) (mkConst ``Ty.unit)

/-- The representation of the constructors whose chains are `cs`, in order: the chain of the only
one, or the sum of the first and the representation of the rest. -/
def sumCode : List Expr → Expr
  | [] => mkConst ``Ty.unit
  | [c] => c
  | c :: cs => mkApp2 (mkConst ``Ty.sum) c (sumCode cs)

/-- The value of the chain whose fields are `vs`, as syntax. -/
def chainStx : List Term → TermElabM Term
  | [] => `(())
  | v :: vs => do `(Prod.mk $v $(← chainStx vs))

/-- The value `v` in the alternative `i` of `k`, as syntax. -/
def injStx (k i : Nat) (v : Term) : TermElabM Term := do
  if k == 1 then return v
  let mut t ← if i + 1 == k then pure v else `(Sum.inl $v)
  for _ in [0:i] do
    t ← `(Sum.inr $t)
  return t

/-- Why the declaration `indVal` cannot be represented, read from what Lean records of it. -/
def refusal? (indVal : InductiveVal) : Option String :=
  if indVal.isUnsafe then some "it is unsafe"
  else if indVal.all.length != 1 then some "it is one of mutually inductive types"
  else if indVal.numNested != 0 then some "it is a nested inductive type"
  else if indVal.isRec then some "it is recursive"
  else if indVal.numIndices != 0 then some "it is an inductive family with indices"
  else if indVal.ctors.isEmpty then some "it has no constructor, and so no empty value"
  else none

/-- One constructor, as the handler represents it: its name and its fields' names and types. -/
structure Ctor where
  name : Name
  fields : Array (Name × Expr)

/-- Whether `e`, a sort, is `Type`. -/
def isType0 (e : Expr) : MetaM Bool := do
  match ← whnf e with
  | .sort l => return l.normalize == Level.one
  | _ => return false

/-- Runs `k` on the binders `acc` followed by each type of `xs` with a local instance of `HasCode`
after it. -/
def withInsts {α : Type} : List Expr → Array Expr → (Array Expr → TermElabM α) → TermElabM α
  | [], acc, k => k acc
  | x :: xs, acc, k => do
    withLocalDecl (← mkFreshUserName `inst) .instImplicit (mkApp (mkConst ``HasCode) x)
      fun inst => withInsts xs (acc.push x |>.push inst) k

/-- Runs `k` on the parameters of the declaration `indVal` at level zero, each with a local instance
of `HasCode`, in the order of the generated binders (each parameter, then its instance), and on the
type applied to them; refuses a parameter that is not a type of `Type` or a type that does not live
in `Type`. -/
def withParams {α : Type} (indVal : InductiveVal)
    (k : Array Expr → Array Expr → Expr → TermElabM α) : TermElabM α := do
  let us := indVal.levelParams.map fun _ => Level.zero
  let type := indVal.type.instantiateLevelParams indVal.levelParams us
  forallBoundedTelescope type indVal.numParams fun xs body => do
    unless ← isType0 body do
      throwError "LeanIntent.HasCode: `{.ofConstName indVal.name}` is not covered: it does not live in `Type`"
    for x in xs do
      unless ← isType0 (← inferType x) do
        throwError "LeanIntent.HasCode: `{.ofConstName indVal.name}` is not covered: its parameter `{x}` is not a type of `Type`"
    withInsts xs.toList #[] fun binders => k xs binders (mkAppN (mkConst indVal.name us) xs)

/-- The constructors of `indVal` applied to the parameters `xs`, with their fields' names and types;
refuses a field that depends on an earlier one or whose type is not a type of `Type`. -/
def ctors (indVal : InductiveVal) (xs : Array Expr) : TermElabM (List Ctor) := do
  let us := indVal.levelParams.map fun _ => Level.zero
  indVal.ctors.mapM fun c => do
    let info ← getConstInfoCtor c
    let mut type ← instantiateForall (info.type.instantiateLevelParams info.levelParams us) xs
    let mut fields := #[]
    repeat
      match type with
      | .forallE n t b _ =>
        let t := t.cleanupAnnotations
        if b.hasLooseBVars then
          throwError "LeanIntent.HasCode: `{.ofConstName indVal.name}` is not covered: the type of a field after `{n}` of `{.ofConstName c}` depends on `{n}`"
        unless ← isType0 (← inferType t) do
          throwError "LeanIntent.HasCode: `{.ofConstName indVal.name}` is not covered: the field `{n}` of `{.ofConstName c}` has type `{t}`, which is not a type of `Type`"
        fields := fields.push (n, t)
        type := b
      | _ => break
    return { name := c, fields }

/-- The code of the declaration `indVal` with parameters `xs`, each with its instance of `HasCode` in
the local context: `Ty.decl` of its name, its parameters' chain and its representation. Refuses a
field whose type has no code. -/
def code (indVal : InductiveVal) (xs : Array Expr) (cs : List Ctor) : TermElabM Expr := do
  let codeOf (t : Expr) : TermElabM Expr := do
    let cls := mkApp (mkConst ``HasCode) t
    let some inst ← synthInstance? cls
      | throwError "LeanIntent.HasCode: `{.ofConstName indVal.name}` is not covered: the type `{t}` of one of its fields has no code; derive `LeanIntent.HasCode` for it first if the project declares it"
    return mkApp2 (mkConst ``HasCode.code) t inst
  let ps ← xs.toList.mapM codeOf
  let reps ← cs.mapM fun c => return chainCode (← c.fields.toList.mapM (codeOf ·.2))
  return mkApp3 (mkConst ``Ty.decl) (toExpr indVal.name) (chainCode ps) (sumCode reps)

/-- Adds the definition `name := fun binders => value` of type `∀ binders, type`. -/
def addFun (name : Name) (binders : Array Expr) (type value : Expr) (thm : Bool) : TermElabM Unit := do
  let type ← mkForallFVars binders type
  let value ← mkLambdaFVars binders value
  if thm then
    addDecl (.thmDecl { name, levelParams := [], type, value })
  else
    addAndCompile <| .defnDecl
      { name, levelParams := [], type, value, hints := .abbrev, safety := .safe }
    setReducibleAttribute name

/-- The constructor of `Ty.Stands` that admits a declared type. -/
def standsDecl : MetaM Name := do
  let info ← getConstInfoInduct ``Ty.Stands
  let some c := info.ctors.find? fun c => (privateToUserName? c).getD c == `LeanIntent.Ty.Stands.decl
    | throwError "LeanIntent.HasCode: `Ty.Stands` has no constructor `decl`"
  return c

/-- Writes the code, the isomorphism, the proof that the code stands for the type, and the instance
of `HasCode`, for the declaration named `declName`. -/
def mkHasCode (declName : Name) : CommandElabM Unit := do
  let indVal ← getConstInfoInduct declName
  if let some why := refusal? indVal then
    throwError "LeanIntent.HasCode: `{.ofConstName declName}` is not covered: {why}"
  let instName := (← getCurrNamespace) ++ (← liftTermElabM <| Deriving.mkInstName ``HasCode declName)
  let codeName := instName ++ `code
  let isoName := instName ++ `iso
  let standsName := instName ++ `stands
  -- The code, and the number of fields of each constructor.
  let shapes ← liftTermElabM <| withParams indVal fun xs binders tApp => do
    if (← synthInstance? (mkApp (mkConst ``HasCode) tApp)).isSome then
      throwError "LeanIntent.HasCode: `{.ofConstName declName}` already has a code"
    let cs ← ctors indVal xs
    addFun codeName binders (mkConst ``Ty) (← code indVal xs cs) false
    return cs.map fun c => (c.name, c.fields.size)
  -- The isomorphism, elaborated by Lean and checked by its kernel.
  let k := shapes.length
  let binderStx ← liftTermElabM <| (List.range indVal.numParams).toArray.mapM fun _ => do
    return (mkIdent (← mkFreshUserName `α), mkIdent (← mkFreshUserName `inst))
  let binders ← binderStx.flatMapM fun (a, i) => do
    return #[← `(bracketedBinderF| {$a : Type}), ← `(bracketedBinderF| [$i : LeanIntent.HasCode $a])]
  let args := binderStx.flatMap fun (a, i) => #[a, i]
  let tStx ← `(@$(mkCIdent declName) $(binderStx.map (·.1))*)
  let holes ← (List.range indVal.numParams).toArray.mapM fun _ => `(_)
  let (toAlts, invAlts, invToAlts, toInvAlts) ← liftTermElabM do
    let mut toAlts := #[]
    let mut invAlts := #[]
    let mut invToAlts := #[]
    let mut toInvAlts := #[]
    for h : i in [0:k] do
      let (c, m) := shapes[i]
      let vars ← (List.range m).mapM fun _ => return (⟨(mkIdent (← mkFreshUserName `x)).raw⟩ : Term)
      let ctorPat ← `(@$(mkCIdent c) $holes* $(vars.toArray)*)
      let repPat ← injStx k i (← chainStx vars)
      let toVal ← injStx k i (← chainStx (← vars.mapM fun x => `(LeanIntent.Iso.to LeanIntent.HasCode.iso $x)))
      let invVal ← `(@$(mkCIdent c) $holes* $(← vars.toArray.mapM fun x => `(LeanIntent.Iso.inv LeanIntent.HasCode.iso $x))*)
      let anon ← (List.range m).mapM fun _ => `(_)
      let ctorAnon ← `(@$(mkCIdent c) $holes* $(anon.toArray)*)
      let repAnon ← injStx k i (← chainStx anon)
      toAlts := toAlts.push (← `(matchAltExpr| | $ctorPat => $toVal))
      invAlts := invAlts.push (← `(matchAltExpr| | $repPat => $invVal))
      invToAlts := invToAlts.push (← `(matchAltExpr| | $ctorAnon =>
        by dsimp only; try simp only [LeanIntent.Iso.inv_to]))
      toInvAlts := toInvAlts.push (← `(matchAltExpr| | $repAnon =>
        by dsimp only; try simp only [LeanIntent.Iso.to_inv]))
    return (toAlts, invAlts, invToAlts, toInvAlts)
  elabCommand (← `(command|
    def $(mkIdent (`_root_ ++ isoName)) $binders* :
        LeanIntent.Iso $tStx (LeanIntent.Ty.denote (@$(mkCIdent codeName) $args*)) where
      to t := match t with $toAlts:matchAlt*
      inv r := match r with $invAlts:matchAlt*
      inv_to t := match t with $invToAlts:matchAlt*
      to_inv r := match r with $toInvAlts:matchAlt*))
  -- The proof that the code stands for the type through the isomorphism.
  let ctor ← liftTermElabM standsDecl
  liftTermElabM <| withParams indVal fun xs binders tApp => do
    let cs ← ctors indVal xs
    let codeE ← code indVal xs cs
    let codeApp := mkAppN (mkConst codeName) binders
    let isoApp := mkAppN (mkConst isoName) binders
    let some (_, ps, rep) := codeE.app3? ``Ty.decl
      | throwError "LeanIntent.HasCode: the code of `{.ofConstName declName}` is not a `Ty.decl`"
    addFun standsName binders (mkApp3 (mkConst ``Ty.Stands) tApp codeApp isoApp)
      (mkAppN (mkConst ctor) #[tApp, toExpr declName, ps, rep, isoApp]) true
  -- The instance.
  elabCommand (← `(command|
    instance $(mkIdent (`_root_ ++ instName)):ident $binders* : LeanIntent.HasCode $tStx :=
      ⟨@$(mkCIdent codeName) $args*, @$(mkCIdent isoName) $args*, @$(mkCIdent standsName) $args*⟩))

/-- The deriving handler of `HasCode`. -/
def handler (declNames : Array Name) : CommandElabM Bool := do
  unless ← declNames.allM isInductive do
    return false
  for n in declNames do
    mkHasCode n
  return true

initialize registerDerivingHandler ``HasCode handler

end LeanIntent.Declared
