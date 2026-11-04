import LeanIntent.Degenerate
import LeanIntent.Cone
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
the logic cannot refer to the constructors of an arbitrary type. The audit of declared types' codes
(`LeanIntent.CodeAudit`) decides the second for a declaration: it reads every attestation the
declaration depends on with `checkAttestation`, which re-derives the code through `codeWith` and the
isomorphism by where it takes each constructor, and compares them by Lean's kernel; for a recursive
type, the code through `readGroup` and `recCode`, and the isomorphism by the equations its maps meet
at every constructor of the group (`checkRecMaps`). The handler runs
`checkAttestation` on what it writes and fails rather than write a code the audit would refuse, so
the two agree on every type the handler covers. The first stays trusted: the audit derives the code
through the same functions, not by a second reading of the declaration.
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

/-- The code of the declaration `indVal` with parameters `xs` and constructors `cs`: `Ty.decl` of
its name, its parameters' chain and its representation, where the code of each parameter, and then
of each constructor's fields in order, is `HasCode.code t i` for the instance `i` that `inst t` gives
for its type `t`. The handler takes each instance from Lean's instance resolution (`code`), and the
audit of an attestation (`checkAttestation`) from the attestation it reads. -/
def codeWith {m : Type → Type} [Monad m] (indVal : InductiveVal) (xs : Array Expr) (cs : List Ctor)
    (inst : Expr → m Expr) : m Expr := do
  let codeOf (t : Expr) : m Expr := return mkApp2 (mkConst ``HasCode.code) t (← inst t)
  let ps ← xs.toList.mapM codeOf
  let reps ← cs.mapM fun c => return chainCode (← c.fields.toList.mapM (codeOf ·.2))
  return mkApp3 (mkConst ``Ty.decl) (toExpr indVal.name) (chainCode ps) (sumCode reps)

/-- The code of the declaration `indVal` with parameters `xs`, each with its instance of `HasCode` in
the local context: `codeWith`, each instance found by Lean's instance resolution. Refuses a field
whose type has no code. -/
def code (indVal : InductiveVal) (xs : Array Expr) (cs : List Ctor) : TermElabM Expr :=
  codeWith indVal xs cs fun t => do
    let some inst ← synthInstance? (mkApp (mkConst ``HasCode) t)
      | throwError "LeanIntent.HasCode: `{.ofConstName indVal.name}` is not covered: the type `{t}` of one of its fields has no code; derive `LeanIntent.HasCode` for it first if the project declares it"
    return inst

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
Each field's and argument's code is the one `codeOf` gives for its type. Refuses a type with no
constructor of the first kind, and a type that does not grow (`Ty.grows`). -/
def recCodeWith {m : Type → Type} [Monad m] [MonadError m] [MonadEnv m] [MonadLCtx m]
    (indVal : InductiveVal) (group : Array (Expr × Array GCtor)) (i : Nat)
    (codeOf : Expr → m Expr) : m (Expr × Expr × Expr) := do
  let dataCodes (c : GCtor) : m (List Expr) :=
    c.fields.toList.filterMapM fun | .data t => some <$> codeOf t | .ref _ _ => pure none
  let domCodes (c : GCtor) : m (List Expr) :=
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
  -- `r` holds only numbers of types, so Lean's kernel decides whether the group grows.
  let grows := Kernel.isDefEq (← getEnv) (← getLCtx) (mkApp2 (mkConst ``Ty.grows) r (toExpr i))
    (toExpr true)
  unless grows matches .ok true do
    throwError "LeanIntent.HasCode: `{.ofConstName indVal.name}` is not covered: its recursive constructors do not build values of every depth, since a type of its group they need has no value"
  return (b, g, r)

/-- `recCodeWith` with the code of each field's type found by Lean's instance resolution, as the
handler writes it. Refuses a field or argument whose type has no code. -/
def recCode (indVal : InductiveVal) (group : Array (Expr × Array GCtor)) (i : Nat) :
    TermElabM (Expr × Expr × Expr) :=
  recCodeWith indVal group i fun t => do
    let some inst ← synthInstance? (mkApp (mkConst ``HasCode) t)
      | throwError "LeanIntent.HasCode: `{.ofConstName indVal.name}` is not covered: the type `{t}` of one of its fields has no code; derive `LeanIntent.HasCode` for it first if the project declares it"
    return mkApp2 (mkConst ``HasCode.code) t inst

/-! ## Reading an attestation -/

/-- The type a code denotes, `Ty.denote c`. -/
def denoteE (c : Expr) : Expr := mkApp (mkConst ``Ty.denote) c

/-- The type of the alternatives whose types are `ts`, nested as `sumCode` nests their codes. -/
def sumType : List Expr → Expr
  | [] => mkConst ``Unit
  | [t] => t
  | t :: ts => mkApp2 (mkConst ``Sum [Level.zero, Level.zero]) t (sumType ts)

/-- The value `v` in the alternative `i` of the alternatives whose types are `ts`, as `injStx` writes
it: itself when there is one alternative, and otherwise `Sum.inr` applied `i` times to `Sum.inl v`,
or to `v` itself in the last alternative. -/
def injExpr : List Expr → Nat → Expr → Expr
  | [], _, v | [_], _, v => v
  | t :: ts, 0, v => mkApp3 (mkConst ``Sum.inl [Level.zero, Level.zero]) t (sumType ts) v
  | t :: ts, i + 1, v =>
    mkApp3 (mkConst ``Sum.inr [Level.zero, Level.zero]) t (sumType ts) (injExpr ts i v)

/-- The value of the chain whose fields have the codes and values `fs`, in order, as `chainStx`
writes it: each value paired with the chain after it, and the last with the unit value. -/
def chainExpr : List (Expr × Expr) → Expr
  | [] => mkConst ``Unit.unit
  | (c, v) :: fs =>
    mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) (denoteE c)
      (denoteE (chainCode (fs.map (·.1)))) v (chainExpr fs)

/-- The inductive types `Ty` builds in: the head constant of `Ty.denote (c ?args)` for each
constructor `c` of `Ty`, and of `Atom.denote (k ?args)` for each constructor `k` of `Atom`, each
applied to fresh metavariables and put in weak head normal form, where that head is an inductive
type. The others are `decl` and `atom`, which denote what their arguments do and are stuck at a
metavariable, and `arrow`, which denotes a function type. The constructors are read from the
environment, so a constructor `Ty` gains is counted. -/
def builtinHeads : MetaM (Array Name) := do
  let mut heads := #[]
  for (ind, den) in [(``Ty, ``Ty.denote), (``Atom, ``Atom.denote)] do
    for c in (← getConstInfoInduct ind).ctors do
      let (args, _, _) ← forallMetaTelescope (← inferType (mkConst c))
      if let .const h _ := (← whnf (mkApp (mkConst den) (mkAppN (mkConst c) args))).getAppFn then
        if ← isInductive h then
          heads := heads.push h
  return heads

/-- Whether `f`, a map from the `i`-th type of the recursive group `group` (as `readGroup` reads it)
to that type's trees, is the map the handler writes, read constructor by constructor: `none` when
it is, and otherwise the reason it is not. Starting from `f` for the `i`-th type, it checks, for
every constructor of every type of the group the maps reach, that the map applied to the constructor
and its fields reduces, by Lean's `whnf` or else by its kernel, to a value that is, by Lean's kernel:

* for a base constructor of the `i`-th type, the base value holding the constructor's alternative
  of the base, with each field carried through its own type's isomorphism;
* for any other constructor, the node of that constructor, in the type's list, holding the chain
  of its other fields each so carried, whose child at each recursive field and position is the
  map of the type that field holds, applied to the field at that position, each argument carried
  back through its own type's isomorphism.

The map of a type other than the `i`-th is the one `candidate` gives, the handler's beside the
attestation where there is one, or else the one read from the first child of that type, and every
child of that type is checked against it. A candidate decides nothing by its name: only these
equations accept it. Maps that satisfy these equations for every constructor
are, by structural recursion over the group, the handler's maps, so an isomorphism with this forward
map is the handler's, its map back being that map's inverse. Each type of the group is read at most
once. -/
def checkRecMaps (group : Array (Expr × Array GCtor)) (i : Nat) (f : Expr)
    (instOf : Expr → MetaM (Option Expr)) (candidate : Nat → MetaM (Option Expr)) :
    MetaM (Option String) := do
  let kernelEq (a b : Expr) : MetaM Bool := do
    return Kernel.isDefEq (← getEnv) (← getLCtx) a b matches .ok true
  let codeOf (t inst : Expr) : Expr := mkApp2 (mkConst ``HasCode.code) t inst
  let carry (fn : Name) (t inst v : Expr) : Expr :=
    mkApp4 (mkConst fn) t (denoteE (codeOf t inst)) (mkApp2 (mkConst ``HasCode.iso) t inst) v
  -- The data part of a constructor's fields `xs`: each field that holds no value of the group, with
  -- its code and its value carried through its type's isomorphism.
  let dataParts (c : GCtor) (xs : Array Expr) : MetaM (Option (List (Expr × Expr))) := do
    let mut parts := #[]
    for (fld, x) in c.fields.zip xs do
      if let .data t := fld then
        let some inst ← instOf t | return none
        parts := parts.push (codeOf t inst, carry ``Iso.to t inst x)
    return some parts.toList
  -- The alternatives of the base: for each base constructor of the `i`-th type, its data chain.
  let mut baseAlts := #[]
  for c in group[i]!.2.filter GCtor.isBase do
    let mut codes := #[]
    for fld in c.fields do
      if let .data t := fld then
        let some inst ← instOf t | return some s!"the type `{t}` of a field of `{c.name}` has no code"
        codes := codes.push (codeOf t inst)
    baseAlts := baseAlts.push (denoteE (chainCode codes.toList))
  -- A map applied to a constructor, reduced to a base value or a node: by `whnf`, and where that
  -- stops short, as it can at a recursive field that is a function, by Lean's kernel.
  let reduce (e : Expr) : MetaM Expr := do
    let w ← whnf e
    if w.isAppOf ``MuVal.base || w.isAppOf ``MuVal.node then return w
    match Kernel.whnf (← getEnv) (← getLCtx) e with
    | .ok k => return k
    | .error _ => return w
  let mut maps : Array (Option Expr) := group.map fun _ => none
  maps := maps.set! i (some f)
  let mut todo : List Nat := [i]
  for _ in [0:group.size] do
    let k :: rest := todo | return none
    todo := rest
    let some F := maps[k]! | return some "a map of the group is missing"
    let (τ, cs) := group[k]!
    let .const tName tUs := τ.getAppFn | return some s!"`{τ}` is not an inductive type applied to its parameters"
    let _ := tName
    let mut nb := 0
    let mut nn := 0
    for c in cs do
      let isBase := k == i && c.isBase
      let types ← c.fields.mapM fun
        | .data t => pure t
        | .ref l doms => doms.foldrM (fun d acc => mkArrow d acc) group[l]!.1
      let outcome : Except String (Array (Nat × Expr)) ←
          withLocalDeclsDND (types.mapIdx fun j t => (Name.mkSimple s!"x{j}", t)) fun xs => do
        let lhs ← reduce (mkApp F (mkAppN (mkConst c.name tUs) (τ.getAppArgs ++ xs)))
        let some parts ← dataParts c xs | return .error s!"a field of `{c.name}` has no code"
        if isBase then
          unless lhs.isAppOfArity ``MuVal.base 8 do
            return .error s!"the map does not take `{c.name}` to a base value"
          unless ← kernelEq lhs.appArg! (injExpr baseAlts.toList nb (chainExpr parts)) do
            return .error s!"the map does not take `{c.name}` to base alternative {nb} holding its fields, each carried through its own type's isomorphism"
          return .ok #[]
        unless lhs.isAppOfArity ``MuVal.node 11 do
          return .error s!"the map does not take `{c.name}` to a node"
        let args := lhs.getAppArgs
        let (cE, d, kids) := (args[8]!, args[9]!, args[10]!)
        let some nE := (← whnf (← inferType cE)).app1? ``Fin
          | return .error s!"the node of `{c.name}` has no constructor number"
        unless ← kernelEq (mkApp2 (mkConst ``Fin.val) nE cE) (mkNatLit nn) do
          return .error s!"the map does not take `{c.name}` to the node of constructor {nn}"
        unless ← kernelEq d (chainExpr parts) do
          return .error s!"the node of `{c.name}` does not hold its other fields, each carried through its own type's isomorphism"
        -- Each recursive field's children: the map of its type at the field, its arguments carried back.
        let some aE := (← whnf (← inferType kids)).bindingDomain!.app1? ``Fin
          | return .error s!"the children of `{c.name}` are not numbered"
        let mut found := #[]
        let mut r := 0
        for (fld, x) in c.fields.zip xs do
          let .ref l doms := fld | continue
          -- `r < A`, proved by `decide` through `Nat.decLt`, built without instance resolution, which
          -- an environment imported without its extensions' state does not offer.
          let lt := mkApp4 (mkConst ``LT.lt [Level.zero]) (mkConst ``Nat) (mkConst ``instLTNat)
            (mkNatLit r) aE
          let h := mkApp3 (mkConst ``of_decide_eq_true) lt (mkApp2 (mkConst ``Nat.decLt) (mkNatLit r) aE)
            (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true))
          let pos := mkApp3 (mkConst ``Fin.mk) aE (mkNatLit r) h
          let yTy := (← whnf (← inferType (mkApp kids pos))).bindingDomain!
          let res : Except String (Option Expr) ← withLocalDeclD `y yTy fun y => do
            let mut argVals := #[]
            for h : q in [0:doms.size] do
              let d := doms[q]
              let some inst ← instOf d | return .error s!"an argument type of `{c.name}` has no code"
              let v ← if doms.size == 1 then pure y else do
                let mut v := y
                for _ in [0:q] do v ← mkAppM ``Prod.snd #[v]
                mkAppM ``Prod.fst #[v]
              argVals := argVals.push (carry ``Iso.inv d inst v)
            let arg := mkAppN x argVals
            let child ← whnfR (mkApp2 kids pos y)
            match maps[l]!, found.find? (·.1 == l) with
            | some G, _ | none, some (_, G) =>
              return if ← kernelEq child (mkApp G arg) then .ok none
                else .error s!"a child of `{c.name}` is not the map of its type at the field"
            | none, none =>
              if let some G ← candidate l then
                return if ← kernelEq child (mkApp G arg) then .ok (some G)
                  else .error s!"a child of `{c.name}` is not the map of its type at the field"
              unless child.isApp && (← kernelEq child.appArg! arg) do
                return .error s!"a child of `{c.name}` is not a map applied to the field"
              let G := child.appFn!
              if G.hasAnyFVar fun v => v == y.fvarId! || xs.any (·.fvarId! == v) then
                return .error s!"a child of `{c.name}` is not a map of its type"
              return .ok (some G)
          match res with
          | .error why => return .error why
          | .ok (some G) => found := found.push (l, G)
          | .ok none => pure ()
          r := r + 1
        return .ok found
      match outcome with
      | .error why => return some why
      | .ok found =>
        for (l, G) in found do
          if maps[l]!.isNone then
            maps := maps.set! l (some G)
            todo := todo ++ [l]
      if isBase then nb := nb + 1 else nn := nn + 1
  return if todo.isEmpty then none else some "the maps of the group were not all read"

/-- Whether the declaration `ci` is an attestation the handler writes, where `ctor` is the private
constructor of `Ty.Stands` that admits a declared type (`standsDecl`). It is one when `ci` is a
theorem whose statement does not name `ctor` and whose value names it once, as the whole value under
its `fun` binders, applied to a type, a name, a chain, a representation and an isomorphism, where:

* the type, put in weak head normal form, is `T as` for an inductive type `T` at universe level zero
  that the handler covers (`refusal?`, `withParams`, `ctors`), applied to its parameters `as`, and
  `T` is none of the types `Ty` builds in (`builtinHeads`), whose codes are not declarations' codes,
  so that no attestation gives such a type, or a type that reduces to one, a second code;
* the name, chain and representation are the code `codeWith` derives from `T`'s declaration at
  `as`, with some instance of `HasCode` for each parameter's and field's type;
* the isomorphism takes each constructor of `T`, applied to `as` and to its fields, to the
  alternative `injExpr` and `chainExpr` build, holding each field carried through the isomorphism of
  the instance whose code the representation holds for it.

Lean's unifier finds those instances, and Lean's kernel then decides each equality, the type, the
code and the image of every constructor, by its definitional equality. An isomorphism is fixed by
its forward map, since its map back is that map's inverse, so the map back is not compared. Returns
the type attested, printed, with `none` when the attestation is the handler's, or the reason it is
not. The type is `none` when the attestation is refused before its type is read. -/
def checkAttestation (ctor : Name) (ci : ConstantInfo) : MetaM (Option String × Option String) := do
  let .thmInfo v := ci | return (none, some "it is not a theorem")
  if (Cone.exprRefs v.type []).contains ctor then
    return (none, some "its statement names the constructor")
  unless (Cone.exprRefs v.value []).count ctor == 1 do
    return (none, some "its value does not name the constructor exactly once")
  lambdaTelescope v.value fun binders body => do
    unless body.isAppOfArity ctor 5 do
      return (none, some "its value is not one application of the constructor under `fun` binders")
    let #[α, n, ps, r, e] := body.getAppArgs | unreachable!
    let ty := toString (← ppExpr α)
    let fail (why : String) : MetaM (Option String × Option String) := return (some ty, some why)
    let α' ← whnf α
    let .const T us := α'.getAppFn | fail "the type is not an inductive type applied to its parameters"
    let some (.inductInfo indVal) := (← getEnv).find? T
      | fail "the type is not an inductive type applied to its parameters"
    if (← builtinHeads).contains T then
      return ← fail s!"`{T}` is a type `LeanIntent.Ty` builds in, whose code is not a declaration's"
    if let some why := refusal? indVal then
      return ← fail s!"the handler does not cover `{T}`: {why}"
    unless us.all (·.normalize == Level.zero) do
      return ← fail "the type is not taken at universe level zero"
    let as := α'.getAppArgs
    unless as.size == indVal.numParams do
      return ← fail "the type is not an inductive type applied to its parameters"
    try
      (withParams indVal fun xs _ _ => discard <| ctors indVal xs : TermElabM Unit).run'
    catch ex => return ← fail (← ex.toMessageData.toString)
    let kernelEq (a b : Expr) : MetaM Bool := do
      return Kernel.isDefEq (← getEnv) (← getLCtx) a b matches .ok true
    -- A recursive type: its code re-derived by the handler's own reading of its group, and the maps
    -- of its group read constructor by constructor (`checkRecMaps`).
    if indVal.isRec || indVal.numNested != 0 then
      let i := indVal.all.idxOf T
      -- The code of each field's and argument's type: one metavariable for each type, which Lean's
      -- unifier then finds in the attestation's code, as for `codeWith` below.
      let codeOf (t : Expr) : StateT (Array (Expr × Expr)) MetaM Expr := do
        if let some (_, inst) := (← get).find? (·.1 == t) then
          return mkApp2 (mkConst ``HasCode.code) t inst
        let inst ← mkFreshExprMVar (mkApp (mkConst ``HasCode) t)
        modify (·.push (t, inst))
        return mkApp2 (mkConst ``HasCode.code) t inst
      let read : Except String (Option (Array (Expr × Array GCtor) × Expr × Array (Expr × Expr))) ← try
          let group ← (readGroup indVal as : TermElabM _).run'
          match reachesItself group i with
          | none => pure (Except.error "whether it reaches itself through the fields of its group is not settled")
          | some false => pure (.ok none)
          | some true =>
            let ((b, g, refs, ps), insts) ← (do
                let (b, g, refs) ← recCodeWith indVal group i codeOf
                return (b, g, refs, ← as.toList.mapM codeOf)).run #[]
            pure (.ok (some (group, mkApp3 (mkConst ``Ty.decl) (toExpr indVal.name) (chainCode ps)
              (mkApp4 (mkConst ``Ty.mu) b g refs (toExpr i)), insts)))
        catch ex => pure (.error (← ex.toMessageData.toString))
      match read with
      | .error why => return ← fail why
      | .ok none => pure ()
      | .ok (some (group, derived, insts)) =>
        let given := mkApp3 (mkConst ``Ty.decl) n ps r
        unless ← isDefEq given derived do
          return ← fail "its code is not the one the declaration fixes"
        let derived ← instantiateMVars derived
        let insts ← insts.mapM fun (t, inst) => return (t, ← instantiateMVars inst)
        if derived.hasMVar || insts.any (·.2.hasMVar) then
          return ← fail "its code does not fix an instance of `HasCode` for each of its parts"
        unless ← kernelEq α (mkAppN (mkConst T us) as) do
          return ← fail "Lean's kernel does not find the type to be its declaration applied to its parameters"
        unless ← kernelEq given derived do
          return ← fail "Lean's kernel does not find its code to be the one the declaration fixes"
        let instOf (t : Expr) : MetaM (Option Expr) := return (insts.find? (·.1 == t)).map (·.2)
        -- A candidate for the map of another type of the group: the one the handler writes beside
        -- the attestation, applied to the same binders. Only its equations, checked below, decide.
        let candidate (l : Nat) : MetaM (Option Expr) := do
          let nm := ci.name.getPrefix ++ Name.mkSimple s!"to{l}"
          return if (← getEnv).contains nm then some (mkAppN (mkConst nm) binders) else none
        if let some why ← checkRecMaps group i (mkApp3 (mkConst ``Iso.to) α (denoteE given) e) instOf
            candidate then
          return ← fail s!"its isomorphism is not the handler's: {why}"
        return (some ty, none)
    let cs ← (ctors indVal as : TermElabM _).run'
    -- The code, with a metavariable for each instance, in the order `codeWith` asks for them.
    let (derived, insts) ← (codeWith indVal as cs fun t => do
      let i ← mkFreshExprMVar (mkApp (mkConst ``HasCode) t)
      modify (·.push i)
      return i : StateT (Array Expr) MetaM Expr).run #[]
    let given := mkApp3 (mkConst ``Ty.decl) n ps r
    unless ← isDefEq given derived do
      return ← fail "its code is not the one the declaration fixes"
    let derived ← instantiateMVars derived
    let insts ← insts.mapM instantiateMVars
    if derived.hasMVar || insts.any (·.hasMVar) then
      return ← fail "its code does not fix an instance of `HasCode` for each of its parts"
    let kernelEq (a b : Expr) : MetaM Bool := do
      return Kernel.isDefEq (← getEnv) (← getLCtx) a b matches .ok true
    unless ← kernelEq α (mkAppN (mkConst T us) as) do
      return ← fail "Lean's kernel does not find the type to be its declaration applied to its parameters"
    unless ← kernelEq given derived do
      return ← fail "Lean's kernel does not find its code to be the one the declaration fixes"
    -- Each constructor's fields, with the instance whose code the representation holds for each.
    let mut k := as.size
    let mut chains : Array (List (Name × Expr × Expr)) := #[]
    for c in cs do
      chains := chains.push <| (c.fields.toList.zip (insts.extract k (k + c.fields.size)).toList).map
        fun ((x, t), i) => (x, t, i)
      k := k + c.fields.size
    let codeOf (t i : Expr) : Expr := mkApp2 (mkConst ``HasCode.code) t i
    let alts := chains.toList.map fun fs => denoteE (chainCode (fs.map fun (_, t, i) => codeOf t i))
    for h : j in [0:cs.length] do
      let c := cs[j]
      let fs := chains[j]!
      let ok ← withLocalDeclsDND (fs.map fun (x, t, _) => (x, t)).toArray fun xs => do
        let lhs := mkApp4 (mkConst ``Iso.to) α (denoteE given) e
          (mkAppN (mkConst c.name us) (as ++ xs))
        let parts := (fs.zip xs.toList).map fun ((_, t, i), x) =>
          (codeOf t i, mkApp4 (mkConst ``Iso.to) t (denoteE (codeOf t i))
            (mkApp2 (mkConst ``HasCode.iso) t i) x)
        kernelEq lhs (injExpr alts j (chainExpr parts))
      unless ok do
        return ← fail s!"its isomorphism does not take `{c.name}` to alternative {j} holding its fields, each carried through its own type's isomorphism"
    return (some ty, none)

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
  -- The audit's reading of what the handler wrote, so that no type the handler covers gets a code
  -- the audit would refuse (`LeanIntent.CodeAudit`).
  let (_, why?) ← liftTermElabM <| checkAttestation ctor (← getConstInfo standsName)
  if let some why := why? then
    throwError "LeanIntent.HasCode: the code written for `{.ofConstName declName}` fails the audit of declared types' codes: {why}"

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
                let ys ← ys.mapM fun y => `(LeanIntent.Iso.inv LeanIntent.HasCode.iso $y)
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
            let ih ← `($(rel (invToName l)) ($x $ys*))
            -- Cancel argument transport inside this field; data fields keep their own inverse laws.
            let p ← if n == 0 then pure ih else
              `(by simp only [LeanIntent.Iso.inv_to] <;> exact $ih)
            ys.foldrM (fun y p => `(funext fun $(⟨y.raw⟩):ident => $p)) p
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
              algArgs := algArgs.push (← `(fun y => $ih $(← fin r)
                (LeanIntent.Iso.to LeanIntent.HasCode.iso y)))
              r := r + 1
            | some (_, n) =>
              let ys ← (List.range n).toArray.mapM fun _ => return mkIdent (← mkFreshUserName `y)
              let coded ← ys.toList.mapM fun y => `(LeanIntent.Iso.to LeanIntent.HasCode.iso $(⟨y.raw⟩):term)
              algArgs := algArgs.push (← `(fun $ys* => $ih $(← fin r) $(← chainStx coded)))
              r := r + 1
          let dPat : Term ← if datas.isEmpty then `(_) else pure d
          let ihPat : Term ← if refs.isEmpty then `(_) else pure ih
          algAlts := algAlts.push (← `(matchAltExpr| | $(quote k), ⟨$(quote cn), _⟩, $dPat, $ihPat =>
            @$(mkCIdent c.name) $holes* $algArgs*))
          let pd ← chainEq (← (List.range datas.size).mapM fun q' => do
            `(LeanIntent.Iso.to_inv LeanIntent.HasCode.iso $(← chainGet d q')))
          let kk := mkIdent `kk
          let pk ← if refs.isEmpty then `(funext fun e => e.elim0) else do
            let alts ← refs.mapIdxM fun r (_, n, _) => do
              let ih ← `($(rel toInvName) ($kk $(← fin r) $(mkIdent `y)))
              let p ← if n == 0 then pure ih else
                `(by simp only [LeanIntent.Iso.to_inv] <;> exact $ih)
              `(matchAltExpr| | ⟨$(quote r), _⟩ => $p)
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
