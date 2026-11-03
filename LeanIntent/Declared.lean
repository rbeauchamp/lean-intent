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
fields' rules (`Ty.Small`), one by one or as one member, and its projections are the components of
its fields when it has one constructor, a function in a field included, as
`Ty.decl` delegates to its representation (`LeanIntent.Codes`) and `Ty.projs` descends into the
fields of a declaration with one constructor (`LeanIntent.Degenerate`). Nothing of it is chosen by
the record or by the instance's author.

A type that reaches itself through the fields of its constructors, directly, through a type its
nested occurrences make (such as `List T`), or through another type of its mutual declaration, is
recursive, and the handler reads it through Lean's recursor for it, whose motives are the types of
its *group* (those its declaration declares, then those its nested occurrences make) and whose
induction hypotheses mark the fields that hold a value of one of them, or a function to one. It
writes:

* the representation `Ty.mu b g r i` of the `i`-th type of the group (`instHasCodeT.base`,
  `instHasCodeT.group` and `instHasCodeT.refs`): `b` the representation, as above, of its
  constructors whose fields hold no value of a type of the group, in declaration order; `g` the chain
  of the group's types, each the chain of its other constructors in declaration order, each the chain
  of the chain of the codes of its fields that hold no value of the group and the chain of the codes
  of its recursive fields' arguments; and `r` the same chain with, for each constructor, the types of
  the group its recursive fields hold (`LeanIntent.Codes`);
* the map from each type of the group to its trees (`instHasCodeT.to0`, …), by structural recursion
  over the group, and the map back, the fold (`Ty.muFold`) of the map from base values
  (`instHasCodeT.baseInv`) and of the map from each other constructor (`instHasCodeT.alg`);
* the proofs that each map undoes the other (`instHasCodeT.invTo0`, …, `instHasCodeT.toInv`), by the
  same recursion, which Lean's kernel checks, and the isomorphism they make.

So a recursive type's empty value is its first base constructor applied to its fields' empty
values, the class takes constants at each base constructor applied to each combination of values of
its fields' rules, and it has no projection but the identity, as `Ty.projs` reaches into no field of
`Ty.mu`. The code, base and group are functions of the declaration alone, read in declaration order.

The handler refuses, and so leaves not covered, every type it cannot represent this way: a recursive
type each of whose constructors has a field that holds a value of a type of its group, for which the
rule above fixes no empty value, though it may have values (a rose tree whose only constructor holds
a list of trees, or the odd half of a mutual even and odd pair; extending the rule to such a type is
lean-intent #45), and one whose recursive constructors build only finitely many
values because a type of its group they need has none (`Ty.grows`); a recursive field that is a
function whose arguments depend on a field or on one another; a type whose values are
constrained by proofs, indices or value parameters (an inductive family with indices, a group with
a type nested through an inductive family with indices, a parameter that is not a type of `Type`, a
field that depends on an earlier field or whose type is not a type of `Type`, such as a proof), from
whose fields alone no empty value follows; an unsafe type; a type with no constructor, which has no
value; a type that does not live in `Type`; a field whose type has no code; and a type that already
has a code. A type whose fields have no code yet gets one once its fields do; a type of a mutual
declaration that does not reach itself is coded as a structure is, once the types of its fields
have codes.

What the handler's output rests on: that it reads the constructors and their fields in declaration
order, and for a recursive type its group and recursive fields from Lean's recursor, which is its own
code below and not checked by Lean's kernel; and that no other code applies the private constructor
of `Ty.Stands`. Lean's privacy is a rule of name resolution, so the
`constructor` tactic, which applies a constructor without resolving its name, or a metaprogram that
builds the term directly, can still apply it; no mechanism inside Lean's logic prevents this, since
the logic cannot refer to the constructors of an arbitrary type. An audit that re-derives each
declared type's code from the environment is lean-intent #24.
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

/-! ## Recursive, nested and mutual types -/

/-- One field of a constructor of a type of a recursive group, as the declaration's recursor presents
it: a field that holds no value of a type of the group, of type `type`, or a recursive field, which
holds a value of the group's `sort`-th type, or a function of arguments of the types `doms` to one. -/
inductive GField where
  | data (type : Expr)
  | ref (sort : Nat) (doms : Array Expr)

/-- Whether a field is recursive. -/
def GField.isRef : GField → Bool
  | .ref _ _ => true
  | .data _ => false

/-- One constructor of a type of a recursive group: its name, the number of parameters of the
declaration it belongs to, and its fields in declaration order. -/
structure GCtor where
  name : Name
  numParams : Nat
  fields : Array GField

/-- Whether no field of the constructor holds a value of a type of the group. -/
def GCtor.isBase (c : GCtor) : Bool := !c.fields.any GField.isRef

/-- The types of the group of the declaration `indVal`, with the parameters `xs`, and their
constructors, as the declaration's recursor presents them: one type for each motive of the recursor,
the types the declaration declares and then those its nested occurrences make, such as `List T`;
each constructor with the field each induction hypothesis is about marked recursive. Refuses a type
of the group with indices, a field that depends on an earlier field or whose type is not a type of
`Type`, and a recursive field that is a function whose arguments depend on a field or on one
another, or are not types of `Type`. -/
def readGroup (indVal : InductiveVal) (xs : Array Expr) : TermElabM (Array (Expr × Array GCtor)) := do
  let notCovered {α : Type} (why : MessageData) : TermElabM α :=
    throwError "LeanIntent.HasCode: `{.ofConstName indVal.name}` is not covered: {why}"
  let recVal ← getConstInfoRec (mkRecName indVal.name)
  let us := recVal.levelParams.map fun _ => Level.zero
  let type ← instantiateForall (recVal.type.instantiateLevelParams recVal.levelParams us) xs
  forallBoundedTelescope type recVal.numMotives fun motives rest => do
    let mut sorts : Array Expr := #[]
    for m in motives do
      let s ← forallTelescope (← inferType m) fun as _ => do
        unless as.size == 1 do
          notCovered m!"a type of its group, nested or declared, is an inductive family with indices"
        inferType as[0]!
      unless ← isType0 (← inferType s) do
        notCovered m!"the type `{s}` of its group does not live in `Type`"
      sorts := sorts.push s
    forallBoundedTelescope rest recVal.numMinors fun minors _ => do
      let mut ctors : Array (Array GCtor) := sorts.map fun _ => #[]
      for minor in minors do
        let (k, ctor) ← forallTelescope (← inferType minor) fun args concl => do
          let some k := motives.idxOf? concl.getAppFn
            | notCovered m!"a minor premise of its recursor is not about a motive"
          let .const cname _ := concl.appArg!.getAppFn
            | notCovered m!"a minor premise of its recursor is not about a constructor"
          let cinfo ← getConstInfoCtor cname
          let rule : RecursorRule := { ctor := cname, nfields := cinfo.numFields, rhs := default }
          let fs := args.extract 0 rule.nfields
          let mut refs : Array (Option (Nat × Array Expr)) := fs.map fun _ => none
          for ih in args.extract rule.nfields args.size do
            let (fi, r) ← forallTelescope (← inferType ih) fun ys body => do
              let some l := motives.idxOf? body.getAppFn
                | notCovered m!"an induction hypothesis of `{.ofConstName rule.ctor}` is not about a motive"
              let x := body.appArg!
              let some fi := fs.idxOf? x.getAppFn
                | notCovered m!"an induction hypothesis of `{.ofConstName rule.ctor}` is not about a field"
              unless x.getAppArgs == ys do
                notCovered m!"a recursive field of `{.ofConstName rule.ctor}` is not applied to its arguments"
              let dom ← ys.mapM fun y => inferType y
              if dom.any fun d => fs.any fun f => d.containsFVar f.fvarId! then
                notCovered m!"an argument of the field `{fs[fi]!}` of `{.ofConstName rule.ctor}` depends on a field"
              if dom.any fun d => ys.any fun y => d.containsFVar y.fvarId! then
                notCovered m!"an argument of the field `{fs[fi]!}` of `{.ofConstName rule.ctor}` depends on an earlier argument"
              for d in dom do
                unless ← isType0 (← inferType d) do
                  notCovered m!"an argument of the field `{fs[fi]!}` of `{.ofConstName rule.ctor}` is not a type of `Type`"
              return (fi, (l, dom))
            refs := refs.set! fi (some r)
          let mut fields := #[]
          for h : fi in [0:fs.size] do
            match refs[fi]! with
            | some (l, dom) => fields := fields.push (.ref l dom)
            | none =>
              let t := (← inferType fs[fi]).cleanupAnnotations
              if (fs.extract 0 fi).any fun f => t.containsFVar f.fvarId! then
                notCovered m!"the type of the field `{fs[fi]}` of `{.ofConstName rule.ctor}` depends on an earlier field"
              unless ← isType0 (← inferType t) do
                notCovered m!"the field `{fs[fi]}` of `{.ofConstName rule.ctor}` has type `{t}`, which is not a type of `Type`"
              fields := fields.push (.data t)
          return (k, { name := cname, numParams := cinfo.numParams, fields })
        ctors := ctors.modify k (·.push ctor)
      return sorts.zip ctors

/-- Whether the `i`-th type of the group reaches itself: `some true` when it is among the types of
the group that the recursive fields of its constructors hold, or that those of theirs hold, and so
on, and `some false` when it is not. Each type of the group enters the list still to follow at most
once, marked when it enters, and an index outside the group never enters, so the list is empty after
as many steps as the group has types; `none`, which the caller refuses, if it were not. -/
def reachesItself (group : Array (Expr × Array GCtor)) (i : Nat) : Option Bool := Id.run do
  let next (k : Nat) : List Nat := (group[k]?.map (·.2.toList)).getD [] |>.flatMap fun c =>
    c.fields.toList.filterMap fun | .ref l _ => some l | .data _ => none
  let mut seen : Array Bool := group.map fun _ => false
  let mut todo : List Nat := []
  for l in next i do
    if !(seen[l]?.getD true) then
      seen := seen.set! l true
      todo := l :: todo
  for _ in [0:group.size] do
    match todo with
    | [] => return some false
    | l :: rest =>
      if l == i then return some true
      todo := rest
      for m in next l do
        if !(seen[m]?.getD true) then
          seen := seen.set! m true
          todo := m :: todo
  return if todo.isEmpty then some false else none

/-- The code `Ty.decl n ps (Ty.mu b g r i)` of the `i`-th type of the recursive group `group`, as
its base `b`, data and arguments `g` and recursive fields `r`: `b` the representation of the
constructors of the `i`-th type whose fields hold no value of a type of the group, in declaration
order; `g` the chain of the group's types, each the chain of its other constructors, in declaration
order, each the chain of the chain of the codes of its fields that hold no value of a type of the
group and the chain of the codes of its recursive fields' arguments, in declaration order (the unit
code for a field that holds a value of the group, the argument's code for a function of one argument
and the chain of the arguments' codes for a function of several); `r` the same chain with each
constructor the chain of `ref l` for each recursive field, `l` the type of the group it holds.
Refuses a field or argument whose type has no code, a type with no constructor of the first kind,
and a type that does not grow (`Ty.grows`). -/
def recCode (indVal : InductiveVal) (group : Array (Expr × Array GCtor)) (i : Nat) :
    TermElabM (Expr × Expr × Expr) := do
  let codeOf (t : Expr) : TermElabM Expr := do
    let some inst ← synthInstance? (mkApp (mkConst ``HasCode) t)
      | throwError "LeanIntent.HasCode: `{.ofConstName indVal.name}` is not covered: the type `{t}` of one of its fields has no code; derive `LeanIntent.HasCode` for it first if the project declares it"
    return mkApp2 (mkConst ``HasCode.code) t inst
  let dataCodes (c : GCtor) : TermElabM (List Expr) :=
    c.fields.toList.filterMapM fun | .data t => some <$> codeOf t | .ref _ _ => pure none
  let domCodes (c : GCtor) : TermElabM (List Expr) :=
    c.fields.toList.filterMapM fun
      | .data _ => pure none
      | .ref _ doms => do
        match doms.toList with
        | [] => return some (mkConst ``Ty.unit)
        | [d] => return some (← codeOf d)
        | ds => return some (chainCode (← ds.mapM codeOf))
  let targets (c : GCtor) : List Expr :=
    c.fields.toList.filterMap fun
      | .data _ => none
      | .ref l _ => some (mkApp (mkConst ``Ty.ref) (toExpr l))
  let bases := group[i]!.2.toList.filter GCtor.isBase
  if bases.isEmpty then
    throwError "LeanIntent.HasCode: `{.ofConstName indVal.name}` is not covered: it is recursive and each of its constructors has a field that holds a value of a type of its group, so the rule of the degenerate class fixes no empty value for it"
  let b := sumCode (← bases.mapM fun c => return chainCode (← dataCodes c))
  let others : List (List GCtor) := group.toList.mapIdx fun k (entry : Expr × Array GCtor) =>
    if k == i then entry.2.toList.filter fun c => !c.isBase else entry.2.toList
  let g := chainCode (← others.mapM fun cs => return chainCode (← cs.mapM fun c => do
    return chainCode [chainCode (← dataCodes c), chainCode (← domCodes c)]))
  let r := chainCode (others.map fun cs => chainCode (cs.map fun c => chainCode (targets c)))
  unless ← isDefEq (mkApp2 (mkConst ``Ty.grows) r (toExpr i)) (toExpr true) do
    throwError "LeanIntent.HasCode: `{.ofConstName indVal.name}` is not covered: its recursive constructors do not build values of every depth, since a type of its group they need has no value"
  return (b, g, r)

/-- Writes the proof that the code `codeName` stands for the declaration `declName` through the
isomorphism `isoName`, through the private constructor of `Ty.Stands` that admits a declared type,
and the instance of `HasCode` that carries the three. -/
def mkStandsAndInstance (declName : Name) (indVal : InductiveVal) (instName codeName isoName standsName : Name)
    (binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) (args : Array Term) (tStx : Term) :
    CommandElabM Unit := do
  let ctor ← liftTermElabM standsDecl
  liftTermElabM <| withParams indVal fun _ binders tApp => do
    let codeE := (← getConstInfoDefn codeName).value.beta binders
    let codeApp := mkAppN (mkConst codeName) binders
    let isoApp := mkAppN (mkConst isoName) binders
    let some (_, ps, rep) := codeE.app3? ``Ty.decl
      | throwError "LeanIntent.HasCode: the code of `{.ofConstName declName}` is not a `Ty.decl`"
    addFun standsName binders (mkApp3 (mkConst ``Ty.Stands) tApp codeApp isoApp)
      (mkAppN (mkConst ctor) #[tApp, toExpr declName, ps, rep, isoApp]) true
  elabCommand (← `(command|
    instance $(mkIdent (`_root_ ++ instName)):ident $binders* : LeanIntent.HasCode $tStx :=
      ⟨@$(mkCIdent codeName) $args*, @$(mkCIdent isoName) $args*, @$(mkCIdent standsName) $args*⟩))

/-- Where a constructor of a recursive group goes in its code: the `ib`-th of the `kb` constructors of
the coded type whose fields hold no value of the group (its base), or the `c`-th constructor its type
lists in the group. -/
inductive Role where
  | base (ib kb : Nat)
  | node (c : Nat)

/-- A constructor of a recursive group as the syntax the handler writes needs it: its name, the
number of parameters of its declaration, for each field `none` when it holds no value of the group
and otherwise the type of the group it holds and whether it is a function, its place in the code,
and the number of its alternative in the match on its type. -/
structure CtorPlan where
  name : Name
  numParams : Nat
  fields : Array (Option (Nat × Nat))
  role : Role
  alt : Nat

/-- The syntax of the `q`-th item of the chain `d`. -/
def chainGet (d : Term) : Nat → TermElabM Term
  | 0 => `(Prod.fst $d)
  | q + 1 => do chainGet (← `(Prod.snd $d)) q

/-- The proof that the chain of the values `ps` proves equal, item by item, is equal to the chain
they are about: `Prod.ext` of each, ending with `rfl`. -/
def chainEq : List Term → TermElabM Term
  | [] => `(rfl)
  | p :: ps => do `(Prod.ext $p $(← chainEq ps))

/-- Writes the code, the isomorphism, the proof that the code stands for the type, and the instance
of `HasCode` for `declName`, the `i`-th type of a recursive group: the code `Ty.decl` of its name,
its parameters' codes and `Ty.mu` of the base and group `recCode` writes; the map from each type of
the group to its trees by structural recursion over the group (`to0`, `to1`, …); the map back, the
fold (`Ty.muFold`) of the map from base values (`baseInv`) and of the map from nodes (`alg`); and
the proofs, by the same recursion, that each map undoes the other, which Lean's kernel checks. -/
def mkRecHasCode (declName : Name) (indVal : InductiveVal) (i : Nat) : CommandElabM Unit := do
  let instName := (← getCurrNamespace) ++ (← liftTermElabM <| Deriving.mkInstName ``HasCode declName)
  let codeName := instName ++ `code
  let baseName := instName ++ `base
  let groupName := instName ++ `group
  let refsName := instName ++ `refs
  let sortName := instName ++ `sort
  let isoName := instName ++ `iso
  let standsName := instName ++ `stands
  let toName (k : Nat) := instName ++ Name.mkSimple s!"to{k}"
  let invToName (k : Nat) := instName ++ Name.mkSimple s!"invTo{k}"
  let baseInvName := instName ++ `baseInv
  let algName := instName ++ `alg
  let toGName := instName ++ `toG
  let toInvName := instName ++ `toInv
  -- The name relative to the current namespace, by which a function of a mutual block refers to
  -- another and a theorem to itself.
  let ns ← getCurrNamespace
  let rel (n : Name) : Lean.Ident := mkIdent (n.replacePrefix ns .anonymous)
  -- The code, the family of the group's types, and the plan of each type's constructors.
  let plans ← liftTermElabM <| withParams indVal fun xs binders tApp => do
    if (← synthInstance? (mkApp (mkConst ``HasCode) tApp)).isSome then
      throwError "LeanIntent.HasCode: `{.ofConstName declName}` already has a code"
    let group ← readGroup indVal xs
    let (b, g, r) ← recCode indVal group i
    let ps ← xs.toList.mapM fun x => do
      let some inst ← synthInstance? (mkApp (mkConst ``HasCode) x)
        | throwError "LeanIntent.HasCode: a parameter of `{.ofConstName declName}` has no code"
      return mkApp2 (mkConst ``HasCode.code) x inst
    addFun baseName binders (mkConst ``Ty) b false
    addFun groupName binders (mkConst ``Ty) g false
    addFun refsName #[] (mkConst ``Ty) r false
    let rep := mkApp4 (mkConst ``Ty.mu) (mkAppN (mkConst baseName) binders)
      (mkAppN (mkConst groupName) binders) (mkConst refsName) (toExpr i)
    addFun codeName binders (mkConst ``Ty) (mkApp3 (mkConst ``Ty.decl) (toExpr indVal.name)
      (chainCode ps) rep) false
    let fam ← withLocalDeclD `k (mkConst ``Nat) fun k => do
      let mut body := Lean.mkConst ``Empty
      for j in (List.range group.size).reverse do
        body ← mkAppOptM ``cond #[none, mkApp2 (mkConst ``Nat.beq) k (toExpr j), group[j]!.1, body]
      mkLambdaFVars #[k] body
    addFun sortName binders (← mkArrow (mkConst ``Nat) (mkSort Level.one)) fam false
    let kb := (group[i]!.2.filter GCtor.isBase).size
    return group.mapIdx fun k (entry : Expr × Array GCtor) => Id.run do
      let cs := entry.2
      let mut out : Array CtorPlan := #[]
      let mut nb := 0
      let mut nn := 0
      for h : p in [0:cs.size] do
        let c := cs[p]
        let role := if k == i && c.isBase then Role.base nb kb else Role.node nn
        if k == i && c.isBase then nb := nb + 1 else nn := nn + 1
        let fields : Array (Option (Nat × Nat)) := c.fields.map fun (f : GField) => match f with
          | GField.data _ => none
          | GField.ref l d => some (l, d.size)
        out := out.push ⟨c.name, c.numParams, fields, role, p + 1⟩
      return out
  let K := plans.size
  let nodes (k : Nat) : Nat := (plans[k]!.filter fun (c : CtorPlan) => c.role matches .node _).size
  let binderStx ← liftTermElabM <| (List.range indVal.numParams).toArray.mapM fun _ => do
    return (mkIdent (← mkFreshUserName `α), mkIdent (← mkFreshUserName `inst))
  let binders ← binderStx.flatMapM fun (a, i) => do
    return #[← `(bracketedBinderF| {$a : Type}), ← `(bracketedBinderF| [$i : LeanIntent.HasCode $a])]
  let args := binderStx.flatMap fun (a, i) => #[a, i]
  let tStx ← `(@$(mkCIdent declName) $(binderStx.map (·.1))*)
  let G ← `(@$(mkCIdent sortName) $args*)
  let B ← `(@$(mkCIdent baseName) $args*)
  let Gr ← `(@$(mkCIdent groupName) $args*)
  let R : Term := mkCIdent refsName
  let iq : Term := quote i
  let fold ← `(LeanIntent.Ty.muFold $G (@$(mkCIdent baseInvName) $args*) (@$(mkCIdent algName) $args*))
  let fin (n : Nat) : TermElabM Term := `(⟨$(quote n), of_decide_eq_true rfl⟩)
  -- The maps to the trees, their inverses' parts, and the proofs.
  let (toDefs, baseAlts, algAlts, invToDefs, toInvAlts) ← liftTermElabM do
    let mut toDefs := #[]
    let mut baseAlts := #[]
    let mut algAlts := #[]
    let mut invToDefs := #[]
    let mut toInvAlts := #[]
    for h : k in [0:K] do
      let mut toAlts := #[]
      let mut invToAlts := #[]
      for c in plans[k] do
        let holes ← (List.range c.numParams).toArray.mapM fun _ => `(_)
        let xs ← c.fields.mapM fun _ => return (mkIdent (← mkFreshUserName `x) : Term)
        let pat ← `(@$(mkCIdent c.name) $holes* $xs*)
        let datas := (c.fields.zip xs).filterMap fun (f, x) => if f.isNone then some x else none
        let refs := (c.fields.zip xs).filterMap fun (f, x) => f.map fun (l, arr) => (l, arr, x)
        let dataTo ← datas.toList.mapM fun x => `(LeanIntent.Iso.to LeanIntent.HasCode.iso $x)
        let ctorFn ← `(@$(mkCIdent c.name) $holes*)
        -- `to`: the tree of a value.
        let rhs ← match c.role with
          | .base ib kb => do `(LeanIntent.MuVal.base $(← injStx kb ib (← chainStx dataTo)))
          | .node cn => do
            let children ← if refs.isEmpty then `(fun e => e.elim0) else do
              let alts ← refs.mapIdxM fun r (l, n, x) => do
                let ys ← match n with
                  | 0 => pure #[]
                  | 1 => pure #[(mkIdent `y : Term)]
                  | n => (List.range n).toArray.mapM fun q => chainGet (mkIdent `y) q
                let call ← `($(rel (toName l)) ($x $ys*))
                `(matchAltExpr| | ⟨$(quote r), _⟩ => $call)
              if refs.any (·.2.1 > 0) then `(fun e $(mkIdent `y):ident => match e with $alts:matchAlt*)
              else `(fun e _ => match e with $alts:matchAlt*)
            `(LeanIntent.MuVal.node $(← fin cn) $(← chainStx dataTo) $children)
        toAlts := toAlts.push (← `(matchAltExpr| | $pat => $rhs))
        -- `inv_to`: the value back from its tree.
        let fieldPrfs ← (c.fields.zip xs).toList.mapM fun (f, x) => match f with
          | none => `(LeanIntent.Iso.inv_to LeanIntent.HasCode.iso $x)
          | some (l, n) => do
            let ys ← (List.range n).toArray.mapM fun _ => return (mkIdent (← mkFreshUserName `y) : Term)
            ys.foldrM (fun y p => `(funext fun $(⟨y.raw⟩):ident => $p)) (← `($(rel (invToName l)) ($x $ys*)))
        let prf ← match fieldPrfs with
          | [] => `(rfl)
          | p :: ps => ps.foldlM (fun acc q => `(congr $acc $q)) (← `(congrArg $ctorFn $p))
        invToAlts := invToAlts.push (← `(matchAltExpr| | $pat => by rw [$(mkCIdent (toName k)):ident]; exact $prf))
        -- `baseInv`, `alg` and `to_inv`.
        let eqLemma := mkIdent (`_root_ ++ toName k ++ Name.mkSimple s!"eq_{c.alt}")
        match c.role with
        | .base ib kb =>
          let ys ← datas.mapM fun _ => return (mkIdent (← mkFreshUserName `y) : Term)
          let invVal ← `(@$(mkCIdent c.name) $holes* $(← ys.mapM fun y => `(LeanIntent.Iso.inv LeanIntent.HasCode.iso $y))*)
          baseAlts := baseAlts.push (← `(matchAltExpr| | $(← injStx kb ib (← chainStx ys.toList)) => $invVal))
          let z := mkIdent `z
          let pz ← chainEq (← ys.toList.mapM fun y => `(LeanIntent.Iso.to_inv LeanIntent.HasCode.iso $y))
          toInvAlts := toInvAlts.push (← `(matchAltExpr| | _, LeanIntent.MuVal.base $(← injStx kb ib (← chainStx ys.toList)) =>
            ($eqLemma ..).trans (congrArg (fun $z => LeanIntent.MuVal.base $(← injStx kb ib z)) $pz)))
        | .node cn =>
          let d := mkIdent `d
          let ih := mkIdent `ih
          let mut q := 0
          let mut r := 0
          let mut algArgs := #[]
          for f in c.fields do
            match f with
            | none =>
              algArgs := algArgs.push (← `(LeanIntent.Iso.inv LeanIntent.HasCode.iso $(← chainGet d q)))
              q := q + 1
            | some (_, 0) =>
              algArgs := algArgs.push (← `($ih $(← fin r) ()))
              r := r + 1
            | some (_, 1) =>
              algArgs := algArgs.push (← `(fun y => $ih $(← fin r) y))
              r := r + 1
            | some (_, n) =>
              let ys ← (List.range n).toArray.mapM fun _ => return mkIdent (← mkFreshUserName `y)
              algArgs := algArgs.push (← `(fun $ys* => $ih $(← fin r) $(← chainStx (ys.toList.map fun y => ⟨y.raw⟩))))
              r := r + 1
          let dPat : Term ← if datas.isEmpty then `(_) else pure d
          let ihPat : Term ← if refs.isEmpty then `(_) else pure ih
          algAlts := algAlts.push (← `(matchAltExpr| | $(quote k), ⟨$(quote cn), _⟩, $dPat, $ihPat =>
            @$(mkCIdent c.name) $holes* $algArgs*))
          let pd ← chainEq (← (List.range datas.size).mapM fun q' => do
            `(LeanIntent.Iso.to_inv LeanIntent.HasCode.iso $(← chainGet d q')))
          let kk := mkIdent `kk
          let pk ← if refs.isEmpty then `(funext fun e => e.elim0) else do
            let alts ← refs.mapIdxM fun r _ => do
              `(matchAltExpr| | ⟨$(quote r), _⟩ => $(rel toInvName) ($kk $(← fin r) $(mkIdent `y)))
            `(funext fun e => funext fun $(mkIdent `y):ident => match e with $alts:matchAlt*)
          let kkPat : Term ← if refs.isEmpty then `(_) else pure kk
          toInvAlts := toInvAlts.push (← `(matchAltExpr| | $(quote k), LeanIntent.MuVal.node ⟨$(quote cn), _⟩ $dPat $kkPat =>
            ($eqLemma ..).trans (congr (congrArg (LeanIntent.MuVal.node _) $pd) $pk)))
      let n := nodes k
      if n > 0 then
        let nn := mkIdent `n
        let hh := mkIdent `h
        algAlts := algAlts.push (← `(matchAltExpr| | $(quote k), ⟨$nn + $(quote n), $hh⟩, _, _ =>
          absurd $hh (LeanIntent.Ty.not_add_lt $nn $(quote n))))
        toInvAlts := toInvAlts.push (← `(matchAltExpr| | $(quote k), LeanIntent.MuVal.node ⟨$nn + $(quote n), $hh⟩ _ _ =>
          absurd $hh (LeanIntent.Ty.not_add_lt $nn $(quote n))))
      else
        algAlts := algAlts.push (← `(matchAltExpr| | $(quote k), c, _, _ => c.elim0))
        toInvAlts := toInvAlts.push (← `(matchAltExpr| | $(quote k), LeanIntent.MuVal.node c _ _ => c.elim0))
      let x := mkIdent `x
      toDefs := toDefs.push (← `(command|
        def $(rel (toName k)) $binders* ($x : $G $(quote k)) :
            LeanIntent.Ty.MuOf $B $Gr $R $iq $(quote k) :=
          match $x:ident with $toAlts:matchAlt*))
      invToDefs := invToDefs.push (← `(command|
        theorem $(rel (invToName k)) $binders* ($x : $G $(quote k)) :
            $fold ($(mkCIdent (toName k)) $x) = $x :=
          match $x:ident with $invToAlts:matchAlt*))
    let nn := mkIdent `n
    algAlts := algAlts.push (← `(matchAltExpr| | $nn + $(quote K), c, _, _ => c.elim0))
    toInvAlts := toInvAlts.push (← `(matchAltExpr| | $nn + $(quote K), LeanIntent.MuVal.node c _ _ => c.elim0))
    return (toDefs, baseAlts, algAlts, invToDefs, toInvAlts)
  elabCommand (← `(command| mutual $toDefs:command* end))
  elabCommand (← `(command|
    def $(mkIdent (`_root_ ++ baseInvName)) $binders* (x : LeanIntent.Ty.denote $B) : $G $iq :=
      match x with $baseAlts:matchAlt*))
  elabCommand (← `(command|
    def $(mkIdent (`_root_ ++ algName)) $binders* : LeanIntent.Ty.MuAlg $Gr $R $iq $G :=
      fun j c d ih => match j, c, d, ih with $algAlts:matchAlt*))
  elabCommand (← `(command| mutual $invToDefs:command* end))
  let toGAlts ← liftTermElabM do
    let mut alts := #[]
    for k in [0:K] do
      alts := alts.push (← `(matchAltExpr| | $(quote k) => @$(mkCIdent (toName k)) $args*))
    alts.push <$> `(matchAltExpr| | _ + $(quote K) => fun e => nomatch e)
  elabCommand (← `(command|
    def $(mkIdent (`_root_ ++ toGName)) $binders* (k : Nat) : $G k → LeanIntent.Ty.MuOf $B $Gr $R $iq k :=
      match k with $toGAlts:matchAlt*))
  elabCommand (← `(command|
    theorem $(rel toInvName) $binders* {k : Nat} (v : LeanIntent.Ty.MuOf $B $Gr $R $iq k) :
        @$(mkCIdent toGName) $args* k ($fold v) = v :=
      match k, v with $toInvAlts:matchAlt*))
  elabCommand (← `(command|
    def $(mkIdent (`_root_ ++ isoName)) $binders* :
        LeanIntent.Iso $tStx (LeanIntent.Ty.denote (@$(mkCIdent codeName) $args*)) where
      to := @$(mkCIdent (toName i)) $args*
      inv := $fold
      inv_to := @$(mkCIdent (invToName i)) $args*
      to_inv := @$(mkCIdent toInvName) $args* $iq))
  mkStandsAndInstance declName indVal instName codeName isoName standsName binders args tStx

/-- Writes the code, the isomorphism, the proof that the code stands for the type, and the instance
of `HasCode`, for the declaration named `declName`. -/
def mkHasCode (declName : Name) : CommandElabM Unit := do
  let indVal ← getConstInfoInduct declName
  if let some why := refusal? indVal then
    throwError "LeanIntent.HasCode: `{.ofConstName declName}` is not covered: {why}"
  -- A type that reaches itself through the fields of its group's constructors is recursive.
  let i := indVal.all.idxOf declName
  let recursive ← liftTermElabM <| withParams indVal fun xs _ _ => do
    if indVal.isRec || indVal.numNested != 0 then
      let some r := reachesItself (← readGroup indVal xs) i
        | throwError "LeanIntent.HasCode: `{.ofConstName declName}` is not covered: whether it reaches itself through the fields of its group was not settled"
      return r
    return false
  if recursive then
    return ← mkRecHasCode declName indVal i
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
  mkStandsAndInstance declName indVal instName codeName isoName standsName binders
    (args.map fun a => ⟨a.raw⟩) tStx

/-- The deriving handler of `HasCode`. -/
def handler (declNames : Array Name) : CommandElabM Bool := do
  unless ← declNames.allM isInductive do
    return false
  for n in declNames do
    mkHasCode n
  return true

initialize registerDerivingHandler ``HasCode handler

end LeanIntent.Declared
