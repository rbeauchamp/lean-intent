module

public import LeanIntent.Cone
public import LeanIntent.Declared
public import LeanIntent.MachineDeclared
public import Lean.Util.CollectAxioms

/-!
# The audit of declared types' codes

A declared type's code and isomorphism are attested by the private constructor of `Ty.Stands` that
admits a declared type (`LeanIntent.Declared`). Lean's privacy binds names only: the `constructor`
tactic applies a constructor without resolving its name, so a hand-written instance of `HasCode`
completed by `by constructor` can pair a declared type with a code or isomorphism its author chose,
and change the degenerate class the owner is shown. The coverage of a structure a project declares
as a machine is attested the same way, by the private constructor of `Machine.Stands` that admits a
declared structure (`LeanIntent.MachineDeclared.Handler`), and a forged one would change the classes of a
type covered as a machine (`LeanIntent.Machines`). This module decides, from Lean's own
environment, that a declaration depends on no such attestation of either kind (`kinds`). It reads
the second kind wherever the environment declares `Machine.Stands`; an environment that does not,
such as that of modules that do not import `LeanIntent.Machines`, holds no attestation of that
kind, and the audit runs there on the first kind alone.

* **What a declaration depends on** (`DependsOn`): what cone exclusion follows (`Cone.RefersTo`),
  and also a theorem's proof and an opaque constant's value, where an attestation can be written.
  It holds everything Lean's `collectAxioms` follows at v4.35.0 (`Lean.Util.CollectAxioms`: a
  declaration's type, the value of a definition, theorem or opaque constant, and an inductive
  type's constructors). `depRefs` lists it (`mem_depRefs`).
* **Where an attestation can be** (`Follows`): a declaration whose module is the one that declares
  `Ty.Stands` or imports it, directly or through others, or that the environment's own module
  declares (`relevantIn`). Every other declaration was checked by Lean's kernel in an environment
  without `Ty.Stands`, and so without `Machine.Stands`, whose module imports it, so neither it nor
  anything it names can name either constructor, and what it names is not followed. It can still
  rest on an axiom, and prove `False` from `sorry` for a declaration that does name the
  constructor's type to use, so the axioms it rests on are those Lean's `collectAxioms` reports for
  it (`axiomsIn`), which for an imported declaration Lean computed when it exported the
  declaration's module.
* **The procedure** (`decide`): cone exclusion's closure (`Cone.exclude`) from a first declaration
  and a list of the rest, so that its scope is never empty, refusing at the first reached name that,
  in a module that can hold an attestation, names the constructor of a kind in its statement or
  value (`Applies`), unless it is one of the declarations Lean generates for that kind's inductive
  proposition (`generatedBy`) or an attestation that kind's reader, `Declared.checkAttestation` or
  `MachineDeclared.checkAttestation`, reads as the handler's (`Attestor`); at a reached name outside
  those modules that rests on an axiom other than Lean's three; at a reached name with no
  declaration; and at a reached axiom other than Lean's three. `decide_eq_none_iff` states what it
  decides, `verified_of_decide_eq_none` that an acceptance leaves no reached attestation unread, and
  `mem_leanAxioms_of_decide_eq_none` and `axioms_mem_leanAxioms_of_decide_eq_none` that it leaves no
  axiom but Lean's three.
* **In a Lean environment** (`audit`, `report`, `requireCodes`): `audit`, given a first
  declaration and a list of the rest as `decide` is, collects the reached declarations that name a
  kind's constructor, reads each with that kind's reader, names for each it refuses the type it
  attests and the instances of `HasCode`, `Covered` or `CoveredMachine` that depend on it, and then
  decides with
  `decide`, the verified attestations being those it read as the handler's. It returns that scope
  with what it found (`Outcome`), which `report` prints. `requireCodes c` audits `c` alone and
  throws an error that says why, unless the audit accepts it. No entry point can be given an empty
  scope, whose audit would accept anything; a caller whose scope comes from a search refuses when
  the search finds nothing, as `tools/codes.lean` does. Diagnostic types retain their enclosing
  binders as type families (`AttestedType`, `mem_attestedTypes`), rather than losing types that
  depend on a bound variable; Lean's pretty printer renders those families with binder types.
  Carrier recognition uses Lean's `isClass?`, as instance registration does, so reducible aliases
  of any of the three classes, including aliases hiding quantifiers, are recognized
  (`isCarrier_eq`).

A refused attestation is one of three kinds. A hand-written instance, or a proof Lean abstracts out
of one (`inst._proof_1`), that applies the constructor with a code or isomorphism other than the one
the handler derives, which is the forgery this audit exists for. An attestation that no instance
carries, which the audit refuses too, since a forged attestation is the only way to make a forged
instance and a declaration that holds one can hand it to any instance later. And a proof that
eliminates a `Ty.Stands` or `Machine.Stands` proof and names the constructor in what it builds,
which no declaration of the library does. An axiom other than Lean's three is refused because it can
state an attestation without naming the constructor: `sorryAx`, or `Lean.ofReduceBool` once compiled
code is made to return a false answer.

What the theorems do not reach, and what is trusted:

* That `Declared.checkAttestation` refuses every attestation whose type, code or isomorphism is not
  the one the handler derives from the type's declaration, including every attestation of a type
  `Ty` builds in, such as `Bool` or a definition that reduces to it, which already has a code the
  handler does not write (`Declared.builtinHeads`): argued from its code, which takes the
  derivation from the handler's own functions and leaves each equality to Lean's kernel. For a
  recursive type, the code is re-derived through the handler's own reading of its group and the
  isomorphism is read by what its maps reduce to at every constructor, by Lean's `whnf` or its
  kernel, which fixes them by structural recursion over the group (`Declared.checkRecMaps`). The
  handler runs it on what it writes and fails rather than write a code it refuses, so the two agree
  on every type the handler covers. That the handler reads the declaration in order stays trusted,
  as `LeanIntent.Declared.Handler` states: the audit derives the code through the same functions, not a
  second reading. Likewise that `MachineDeclared.checkAttestation` refuses every attestation whose
  type, input or output type or isomorphism is not the one the handler writes from the structure's
  declaration, `LeanIntent.Machine` itself included, which the library covers through the identity:
  argued from its code, which reads the fields' roles through the handler's own `readRoles` and
  leaves to Lean's kernel each equality, of the type, the input and output types and the image of
  the constructor applied to fields of the three roles, which fixes the isomorphism by the
  structure's eta rule.
* That a declaration whose dependencies name a constructor only in attestations and rest on no
  axiom but Lean's three proves `Ty.Stands` of a declared type's code, or `Machine.Stands` of a
  declared structure's isomorphism, only for a code and isomorphism equal to those of one of those
  attestations: argued from Lean's logic, in which the
  private constructor is the only rule that concludes it, and none of the three axioms proves a
  proposition without a proof of one equivalent to it.
* That the declarations Lean generates for `Ty.Stands` and `Machine.Stands` that name their
  constructors are those `generatedBy` lists, as observed of Lean v4.35.0. A release that generates
  another would make the audit refuse every declaration that reaches it, not accept one it should
  refuse.
* That a declaration in a module that does not import the one declaring `Ty.Stands` cannot name
  either constructor, and that no declaration of an environment that does not declare
  `Machine.Stands` names its constructor, where the audit does not read that kind (`kinds`), each
  of which follows from Lean's kernel checking each declaration in the environment of its module;
  that `collectAxioms` reports every axiom such a declaration rests on, as Lean's own
  audit of axioms; and that `Environment.find?` returns the declarations the kernel checked. In a
  module of Lean's module system an imported theorem is shown as an axiom, so the audit refuses
  there rather than accept a proof it cannot read; run it where every module is imported in full.
* That Lean's compiler runs these definitions as defined: the theorems are about the definitions.
* That Lean's `isClass?` recognizes class types: `isCarrier_eq` specifies the call and how its
  result selects carriers, not the correctness of Lean's reduction and class recognition.
-/

public section

namespace LeanIntent.CodeAudit

open Lean Meta LeanIntent.Cone

/-! ## What a declaration depends on -/

/-- A theorem's proof or an opaque constant's value, which `RefersTo` does not follow. -/
@[expose] def hidden? : ConstantInfo → Option Expr
  | .thmInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

/-- `DependsOn ci c`: the declaration `ci` refers to `c` (`RefersTo`), or it is a theorem whose
proof, or an opaque constant whose value, names `c` (`Mentions`). -/
@[expose] def DependsOn (ci : ConstantInfo) (c : Name) : Prop :=
  RefersTo ci c ∨ ∃ v, hidden? ci = some v ∧ Mentions c v

/-- The names `ci` depends on (`DependsOn`), each as often as it occurs. -/
@[expose] def depRefs (ci : ConstantInfo) : List Name :=
  declRefs ci ++ match hidden? ci with
    | some v => exprRefs v []
    | none => []

theorem mem_depRefs (ci : ConstantInfo) (c : Name) : c ∈ depRefs ci ↔ DependsOn ci c := by
  unfold depRefs DependsOn
  cases hidden? ci <;> simp [mem_declRefs, mem_exprRefs]

/-- `Follows relevant ci c`: the declaration `ci`, whose name `relevant` admits, depends on `c`. -/
@[expose] def Follows (relevant : Name → Bool) (ci : ConstantInfo) (c : Name) : Prop :=
  relevant ci.name = true ∧ DependsOn ci c

/-- The names `ci` depends on when `relevant` admits its name, and none otherwise. -/
@[expose] def follow (relevant : Name → Bool) (ci : ConstantInfo) : List Name :=
  if relevant ci.name then depRefs ci else []

theorem mem_follow (relevant : Name → Bool) (ci : ConstantInfo) (c : Name) :
    c ∈ follow relevant ci ↔ Follows relevant ci c := by
  unfold follow Follows
  split <;> simp_all [mem_depRefs]

/-! ## The procedure -/

/-- `Applies ctor ci`: the statement of `ci`, or the value of a definition, theorem or opaque
constant `ci`, names `ctor`. -/
@[expose] def Applies (ctor : Name) (ci : ConstantInfo) : Prop :=
  Mentions ctor ci.type ∨ ∃ v, ci.value? (allowOpaque := true) = some v ∧ Mentions ctor v

/-- Decides `Applies`. -/
@[expose] def applies (ctor : Name) (ci : ConstantInfo) : Bool :=
  (exprRefs ci.type []).contains ctor ||
    match ci.value? (allowOpaque := true) with
    | some v => (exprRefs v []).contains ctor
    | none => false

theorem applies_eq_true (ctor : Name) (ci : ConstantInfo) :
    applies ctor ci = true ↔ Applies ctor ci := by
  unfold applies Applies
  cases ci.value? (allowOpaque := true) <;> simp [mem_exprRefs]

/-- A kind of attestation, as the procedure reads it: the private constructor `ctor` that admits a
declared type, the declarations Lean generates for its inductive proposition, which name it
(`exempt`), and the attestations of it read as the handler's (`verified`). -/
structure Attestor where
  /-- The private constructor. -/
  ctor : Name
  /-- The declarations Lean generates for the constructor's inductive proposition. -/
  exempt : Name → Bool
  /-- The attestations read as the handler's. -/
  verified : Name → Bool

/-- A reached name the procedure refuses beyond those cone exclusion refuses. One that `relevant`
admits is refused as an attestation not read as the handler's: when its declaration names the
constructor of some kind of `kinds` (`applies`), that kind's `exempt` does not hold it, and that
kind's `verified` does not hold it. One that `relevant` does not admit, whose module cannot name a
constructor and whose dependencies are not followed, is refused when `axiomsOf` reports an axiom it
rests on other than Lean's three. -/
@[expose] def unattested (lookup : Name → Option ConstantInfo) (relevant : Name → Bool)
    (kinds : List Attestor) (axiomsOf : Name → Array Name) (c : Name) : Bool :=
  if relevant c then
    match lookup c with
    | some ci => kinds.any fun k => !k.exempt c && !k.verified c && applies k.ctor ci
    | none => false
  else (axiomsOf c).any fun a => !leanAxioms.contains a

/-- The procedure: cone exclusion's closure from `first :: rest`, a scope that is never empty,
following `Follows relevant`, refusing an unattested name (`unattested`), a name with no declaration
and an axiom other than Lean's three (`leanAxioms`), with fuel `2 ^ 64`, more than the declarations
that fit in a 64-bit address space. `none` when it accepts. -/
@[expose] def decide (lookup : Name → Option ConstantInfo) (relevant : Name → Bool) (kinds : List Attestor)
    (axiomsOf : Name → Array Name) (first : Name) (rest : List Name) : Option Refusal :=
  exclude lookup (follow relevant) (unattested lookup relevant kinds axiomsOf)
    leanAxioms (2 ^ 64) (first :: rest)

section Decides

variable {lookup : Name → Option ConstantInfo} {relevant : Name → Bool} {kinds : List Attestor}
  {axiomsOf : Name → Array Name} {first : Name} {rest : List Name}

/-- **What the procedure decides.** It accepts exactly when every name reached from `first :: rest`
through `Follows relevant` is not unattested, is declared and is no axiom but Lean's three, and at
most `2 ^ 64` names are reached. -/
theorem decide_eq_none_iff :
    decide lookup relevant kinds axiomsOf first rest = none ↔
      (∀ c, Reaches lookup (Follows relevant) (first :: rest) c →
        Admitted lookup (unattested lookup relevant kinds axiomsOf) leanAxioms c) ∧
      Within lookup (Follows relevant) (first :: rest) (2 ^ 64) :=
  exclude_eq_none_iff (mem_follow relevant) _

/-- **An acceptance leaves no attestation unread.** Every reached declaration that names the
constructor of a kind of `kinds`, in a module `relevant` admits and not that kind's `exempt`, is that
kind's `verified`. -/
theorem verified_of_decide_eq_none
    (h : decide lookup relevant kinds axiomsOf first rest = none)
    {c : Name} {ci : ConstantInfo} (hc : Reaches lookup (Follows relevant) (first :: rest) c)
    (hl : lookup c = some ci) (hr : relevant c = true) {k : Attestor} (hk : k ∈ kinds)
    (he : k.exempt c = false) (ha : Applies k.ctor ci) : k.verified c = true := by
  have hu := (decide_eq_none_iff.mp h).1 c hc |>.1
  simp only [unattested, hr, ↓reduceIte, hl, List.any_eq_false] at hu
  have := hu k hk
  simp_all [(applies_eq_true k.ctor ci).mpr ha]

/-- **An acceptance leaves no axiom but Lean's three behind a declaration it does not follow.**
Every reached name that `relevant` does not admit rests, by `axiomsOf`, on Lean's three axioms
alone. -/
theorem axioms_mem_leanAxioms_of_decide_eq_none
    (h : decide lookup relevant kinds axiomsOf first rest = none) {c : Name}
    (hc : Reaches lookup (Follows relevant) (first :: rest) c) (hr : relevant c = false) :
    ∀ a ∈ axiomsOf c, a ∈ leanAxioms := by
  intro a ha
  have hu := (decide_eq_none_iff.mp h).1 c hc |>.1
  simp only [unattested, hr, Bool.false_eq_true, ↓reduceIte] at hu
  have := Array.any_eq_false'.mp hu a ha
  simpa using this

/-- **An acceptance leaves no axiom but Lean's three.** -/
theorem mem_leanAxioms_of_decide_eq_none
    (h : decide lookup relevant kinds axiomsOf first rest = none) {c : Name}
    {ci : ConstantInfo} (hc : Reaches lookup (Follows relevant) (first :: rest) c)
    (hl : lookup c = some ci) (hax : ci.isAxiom = true) : c ∈ leanAxioms := by
  obtain ⟨-, ci', hl', hax'⟩ := (decide_eq_none_iff.mp h).1 c hc
  rw [hl] at hl'
  cases hl'
  exact hax' hax

end Decides

/-! ## The audit in a Lean environment -/

/-- The indices of the modules of `env` that are the module `m` or import it, directly or through
other modules, as `env`'s header records each module's imports. -/
@[expose] def importers (env : Environment) (m : ModuleIdx) : Std.HashSet Nat := Id.run do
  let mut importedBy : Std.HashMap Nat (Array Nat) := {}
  for h : i in [0:env.header.moduleData.size] do
    for imp in env.header.moduleData[i].imports do
      if let some j := env.getModuleIdx? imp.module then
        importedBy := importedBy.insert j.toNat ((importedBy.getD j.toNat #[]).push i)
  let mut found : Std.HashSet Nat := {}
  let mut work := [m.toNat]
  repeat
    match work with
    | [] => break
    | i :: rest =>
      work := rest
      unless found.contains i do
        found := found.insert i
        work := (importedBy.getD i #[]).toList ++ work
  return found

/-- Whether the declaration `c` of `env` can hold an attestation: its module is one of `mods`, or it
is a declaration of the module `env` is elaborating, which has no module index. -/
@[expose] def relevantIn (env : Environment) (mods : Std.HashSet Nat) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | some i => mods.contains i.toNat
  | none => true

/-- The declarations Lean v4.35.0 generates for the inductive proposition `stands` that name its
constructors in their statements or values: its recursor `stands.rec`, `stands.casesOn` and
`stands.recOn`, and, where its constructors take proofs of it, as those of `Ty.Stands` do and those
of `Machine.Stands` do not, the inductive type `stands.below` with its constructors, recursor and
`casesOn`. A declaration counts only when the module that declares `stands` declares it too, where
no other code can add one. -/
@[expose] def generatedBy (env : Environment) (stands : Name) (c : Name) : Bool :=
  (env.getModuleIdxFor? stands).isSome && env.getModuleIdxFor? c == env.getModuleIdxFor? stands &&
    (c == .str stands "rec" || c == .str stands "casesOn" || c == .str stands "recOn" ||
      (Name.str stands "below").isPrefixOf c)

/-- A monad holding an environment alone, in which Lean's `collectAxioms` runs without effects. -/
abbrev EnvM := StateM Environment

instance : MonadEnv EnvM where
  getEnv := get
  modifyEnv := modify

/-- The axioms that Lean's `collectAxioms` reports the declaration `c` of `env` rests on: for an
imported declaration, those Lean recorded when it exported the declaration's module. -/
@[expose] def axiomsIn (env : Environment) (c : Name) : Array Name :=
  (collectAxioms c : EnvM (Array Name)).run' env

/-- Whether Lean recognizes `ci` as an instance of `HasCode`, `Covered` or `CoveredMachine`, or a
function returning one. Use the same semantic class recognition as instance registration, including
its reducible unfolding and telescope traversal, rather than inspecting the type's written head. -/
def isCarrier (ci : ConstantInfo) : MetaM Bool := do
  let cls ← isClass? ci.type
  return cls == some ``HasCode || cls == some ``Covered || cls == some ``CoveredMachine

/-- Carrier selection asks Lean to recognize the declaration's full type and selects exactly
the three carrier classes. This specifies the request to Lean and the use of its result; Lean's
recognition itself remains trusted. The reporting traversal uses this operation directly. -/
theorem isCarrier_eq (ci : ConstantInfo) :
    isCarrier ci = (do
      let cls ← isClass? ci.type
      pure (Decidable.decide (cls = some ``HasCode ∨ cls = some ``Covered ∨
        cls = some ``CoveredMachine))) := by
  simp [isCarrier, Bool.beq_eq_decide_eq, Bool.or_assoc]

/-- `AttestedType ctor e α`: `α` is the first argument of an application of `ctor` in `e`,
abstracted over the binders enclosing that occurrence. Both `fun` and `∀` binders become `fun`
binders of the type family; a `let` retains its type and value. Thus `Wrap α` under a binder
`α : Type` is reported as `fun (α : Type) => Wrap α`, never dropped or left with a loose variable.
Metadata on the constructor does not change which constant it names. -/
@[expose] def AttestedType (ctor : Name) : Expr → Expr → Prop
  | .app f a, α =>
    (f.consumeMData.isConstOf ctor = true ∧ α = a) ∨
      AttestedType ctor f α ∨ AttestedType ctor a α
  | .lam n t b bi, α | .forallE n t b bi, α =>
    AttestedType ctor t α ∨ ∃ β, AttestedType ctor b β ∧ .lam n t β bi = α
  | .letE n t v b nd, α =>
    AttestedType ctor t α ∨ AttestedType ctor v α ∨
      ∃ β, AttestedType ctor b β ∧ .letE n t v β nd = α
  | .mdata _ b, α | .proj _ _ b, α => AttestedType ctor b α
  | .bvar _, _ | .fvar _, _ | .mvar _, _ | .sort _, _ | .const .., _ | .lit _, _ => False

/-- Every type attested in `e`, with its enclosing binders (`AttestedType`). Rebuilding the
binders preserves de Bruijn indices, including dependencies in binder types and let values.
The structural recursion visits every constructor of Lean's expression type. -/
@[expose] def attestedTypes (ctor : Name) : Expr → List Expr
  | .app f a =>
    (if f.consumeMData.isConstOf ctor then [a] else []) ++
      attestedTypes ctor f ++ attestedTypes ctor a
  | .lam n t b bi | .forallE n t b bi =>
    attestedTypes ctor t ++ (attestedTypes ctor b).map (fun α => .lam n t α bi)
  | .letE n t v b nd =>
    attestedTypes ctor t ++ attestedTypes ctor v ++
      (attestedTypes ctor b).map (fun α => .letE n t v α nd)
  | .mdata _ b | .proj _ _ b => attestedTypes ctor b
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const .. | .lit _ => []

/-- The diagnostic traversal retains exactly the attested types with their binder contexts,
for every expression, including occurrences under arbitrary nested binders. -/
theorem mem_attestedTypes {ctor : Name} {α : Expr} :
    (e : Expr) → (α ∈ attestedTypes ctor e ↔ AttestedType ctor e α)
  | .app f a => by
    by_cases h : f.consumeMData.isConstOf ctor = true <;>
      simp [attestedTypes, AttestedType, h, mem_attestedTypes f, mem_attestedTypes a]
  | .lam n t b bi => by
    simp [attestedTypes, AttestedType, mem_attestedTypes t, mem_attestedTypes b]
  | .forallE n t b bi => by
    simp [attestedTypes, AttestedType, mem_attestedTypes t, mem_attestedTypes b]
  | .letE n t v b nd => by
    simp [attestedTypes, AttestedType, mem_attestedTypes t, mem_attestedTypes v,
      mem_attestedTypes b]
  | .mdata _ b | .proj _ _ b => by simp [attestedTypes, AttestedType, mem_attestedTypes b]
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const .. | .lit _ => by
    simp [attestedTypes, AttestedType]

/-- Render a diagnostic type with its binder types, whether it is a type family extracted from
an attestation or an instance's full quantified declaration type. -/
def diagnosticType (α : Expr) : MetaM String := withOptions
    (fun o => ((o.setBool `pp.funBinderTypes true).setBool `pp.piBinderTypes true).setBool
      `pp.letVarTypes true) do
  return toString (← ppExpr α)

/-- A kind of attestation the audit reads in a Lean environment: the inductive proposition
`stands`, its private constructor `ctor` that admits a declared type, and the handler's reading of
an attestation of it (`check`), which returns the type attested, printed, and `none` when the
attestation is the handler's or the reason it is not. -/
structure Kind where
  /-- The inductive proposition. -/
  stands : Name
  /-- Its private constructor that admits a declared type. -/
  ctor : Name
  /-- The handler's reading of an attestation, given the constructor. -/
  check : Name → ConstantInfo → MetaM (Option String × Option String)

/-- The kinds of attestation the audit reads in the current environment: the code of a declared
type, through `Ty.Stands` and read by `Declared.checkAttestation`, and, where the environment
declares `Machine.Stands`, the coverage of a structure a project declares as a machine, through
`Machine.Stands` and read by `MachineDeclared.checkAttestation`.

An environment that does not declare `Machine.Stands` declares no constructor of it, and Lean's
kernel checked each of its declarations against the constants it declares, so none of them names
that constructor: leaving the kind out there leaves no attestation unread and refuses nothing the
audit must refuse, and the audit runs over modules that do not import `LeanIntent.Machines`. Where
a constant of that name is not the library's inductive proposition, `MachineDeclared.standsDecl`
throws an error. `LeanIntent.Machines`, which declares `Machine.Stands`, imports
`LeanIntent.Degenerate`, so every module that can name either constructor is one that can name the
first. -/
def kinds : MetaM (List Kind) := do
  let code : Kind := ⟨``Ty.Stands, ← Declared.standsDecl, Declared.checkAttestation⟩
  if (lookupIn (← getEnv) ``Machine.Stands).isNone then
    return [code]
  return [code,
    ⟨``Machine.Stands, ← MachineDeclared.standsDecl, MachineDeclared.checkAttestation⟩]

/-- An attestation the audit refuses: the declaration `decl` that holds it, the inductive
proposition `stands` whose constructor it applies, the types it applies the constructor to with
their enclosing binders (none only for an unapplied constructor), why it is not the handler's, and
the reached instances of `HasCode`, `Covered` or `CoveredMachine` that depend on `decl`, each paired
with its full quantified declaration type even if the constructor is unapplied. -/
structure Finding where
  decl : Name
  stands : Name
  type? : Option String
  why : String
  carriers : Array (Name × String)

/-- What an audit found: the declarations it audited, `first :: rest`, the attestations it
refuses, and the refusal of `decide`, if any, with, for a refusal at a name outside the modules
that can name a constructor, the axioms other than Lean's three that the name rests on, and for an
unattested name inside them, the inductive propositions whose constructors it names. -/
structure Outcome where
  first : Name
  rest : List Name
  findings : Array Finding
  refusal? : Option (Refusal × Option (Array Name) × List Name)

/-- The audit of the declarations `first :: rest` in the current environment, a scope that is never
empty. It runs in every environment that declares `Ty.Stands`, whether or not that environment
declares `Machine.Stands`, and throws an error in one that does not declare `Ty.Stands`. It collects
the reached declarations, through `Follows`, that name the private constructor of a kind of
attestation the environment declares (`kinds`) and are not among those Lean generates for that
kind's inductive proposition; reads each with that kind's `check`; and decides with `decide`, the
verified attestations of each kind being exactly those it read as the handler's. Returns the scope
with a finding for each attestation it refuses and the refusal of `decide` (`Outcome`).

Lean's limit on the steps a metaprogram takes (`maxHeartbeats`) applies to each reading of an
attestation and, for one the audit refuses, to the printing of the types it attests, to each test
of whether a declaration that depends on it is a carrier and to the printing of each carrier's
type, each counted from where it starts (`withCurrHeartbeats`), and not to the audit as a whole. The collection before them is no
elaboration: it takes steps in proportion to the declarations reached, with the library, and Lean
would count them against the first reading. -/
def audit (first : Name) (rest : List Name) : MetaM Outcome := do
  let env ← getEnv
  let ks ← kinds
  let some m := env.getModuleIdxFor? ``Ty.Stands
    | throwError "the audit of declared types' codes runs in a module that imports `LeanIntent.Degenerate`"
  let relevant := relevantIn env (importers env m)
  let lookup := lookupIn env
  -- The reached declarations, what each depends on, and those that name a constructor.
  let mut visited : Std.HashSet Name := {}
  let mut refs : Std.HashMap Name (List Name) := {}
  let mut candidates : Array (Name × ConstantInfo × Kind) := #[]
  let mut work := first :: rest
  repeat
    match work with
    | [] => break
    | c :: rest =>
      work := rest
      unless visited.contains c do
        visited := visited.insert c
        if let some ci := lookup c then
          let ds := follow relevant ci
          refs := refs.insert c ds
          work := ds ++ work
          if relevant c then
            for k in ks do
              if !generatedBy env k.stands c && applies k.ctor ci then
                candidates := candidates.push (c, ci, k)
  -- Each read as its kind's handler's, or refused.
  let mut verified : Std.HashMap Name (Std.HashSet Name) := {}
  let mut refused : Array (Name × Name × Option String × String) := #[]
  for (c, ci, k) in candidates do
    match ← withCurrHeartbeats (k.check k.ctor ci) with
    | (_, none) => verified := verified.insert k.ctor ((verified.getD k.ctor {}).insert c)
    | (_, some why) =>
      -- One diagnostic path for every refusal; no binder-dependent type can be discarded.
      let es := attestedTypes k.ctor ci.type ++ (match ci.value? (allowOpaque := true) with
        | some v => attestedTypes k.ctor v
        | none => [])
      let tys ← withCurrHeartbeats (es.toArray.mapM diagnosticType)
      let tys := tys.foldl (fun acc t => if acc.contains t then acc else acc.push t) #[]
      refused := refused.push
        (c, k.stands, if tys.isEmpty then none else some (", ".intercalate tys.toList), why)
  -- The reached declarations that depend on each refused one, for its carriers. They are read only
  -- for a refused attestation, so they are collected only when there is one. Each declaration
  -- counts once for each name it depends on, however often the name occurs in it, and joins that
  -- name's list at its head, which copies nothing, so collecting them takes time linear in the
  -- names the reached declarations depend on, as the traversal above does.
  let mut dependents : Std.HashMap Name (List Name) := {}
  unless refused.isEmpty do
    for (c, ds) in refs.toList do
      let mut once : Std.HashSet Name := {}
      for d in ds do
        unless once.contains d do
          once := once.insert d
          dependents := dependents.insert d (c :: dependents.getD d [])
  let mut findings := #[]
  for (c, stands, ty, why) in refused do
    let mut seen : Std.HashSet Name := {}
    let mut up := [c]
    repeat
      match up with
      | [] => break
      | d :: rest =>
        up := rest
        unless seen.contains d do
          seen := seen.insert d
          up := dependents.getD d [] ++ up
    let mut carriers := #[]
    for d in seen.toArray.qsort Name.lt do
      if let some ci := lookup d then
        if ← withCurrHeartbeats (isCarrier ci) then
          carriers := carriers.push (d, ← withCurrHeartbeats (diagnosticType ci.type))
    findings := findings.push { decl := c, stands, type? := ty, why, carriers }
  let attestors := ks.map fun k =>
    { ctor := k.ctor, exempt := generatedBy env k.stands,
      verified := fun c => (verified.getD k.ctor {}).contains c : Attestor }
  let refusal? := decide lookup relevant attestors (axiomsIn env) first rest
  -- A refusal at a name outside the modules that can name a constructor is for its axioms; one
  -- inside them is for the constructors it names.
  let outside (c : Name) : Option (Array Name) :=
    if relevant c then none else some ((axiomsIn env c).filter fun a => !leanAxioms.contains a)
  let named (c : Name) : List Name := match lookup c with
    | some ci => (ks.filter fun k => applies k.ctor ci).map (·.stands)
    | none => []
  let refusal? := refusal?.map fun r => match r with
    | .impl c => (r, outside c, named c)
    | _ => (r, none, [])
  return { first, rest, findings, refusal? }

/-- What the audit reports: a line for each finding, and one for the refusal of `decide` unless it
names a declaration a finding already names. Empty exactly when the audit accepts. -/
@[expose] def report (o : Outcome) : Array String :=
  let lines := o.findings.map fun f =>
    let carried := if f.carriers.isEmpty then
        "no instance of `LeanIntent.HasCode`, `LeanIntent.Covered` or `LeanIntent.CoveredMachine` declared among the dependencies depends on it"
      else s!"the instances that depend on it: {", ".intercalate (f.carriers.toList.map fun (c, ty) => s!"{c} : {ty}")}"
    let what := match f.type? with
      | some ty => s!"to the types (abstracted over their enclosing binders) {ty} with a code or isomorphism the deriving handler does not write from their declarations"
      | none => "in a form the deriving handler does not write"
    s!"{f.decl} applies the private constructor of `{f.stands}` {what}: {f.why}; {carried}"
  match o.refusal? with
  | none => lines
  | some (.impl c, some axs, _) =>
    let what := if axs == #[c] then s!"the axiom {c}" else s!"{c}, which rests on the axioms {axs.toList}"
    lines.push s!"a dependency is {what}, not among Lean's three (propext, Classical.choice, Quot.sound), which could prove an attestation without naming the constructor"
  | some (.impl c, none, stands) =>
    if o.findings.any (·.decl == c) then lines
    else
      let which := if stands.isEmpty then "a private constructor the audit reads"
        else s!"the private constructor of {", ".intercalate (stands.map fun n => s!"`{n}`")}"
      lines.push s!"{c} applies {which}, and the audit did not read it"
  | some (.unknown c, _, _) => lines.push s!"the audit reaches {c}, which has no declaration here"
  | some (.axiom c, _, _) => lines.push s!"a dependency rests on the axiom {c}, which is not one of Lean's three (propext, Classical.choice, Quot.sound) and could state an attestation without the constructor; in a module of Lean's module system an imported theorem is shown as an axiom"
  | some (.fuel, _, _) => lines.push "the dependencies number more than 2 ^ 64"

/-- Throws an error, saying why, unless the audit accepts the declaration `c`: unless no
declaration it depends on attests a declared type's code, or a declared structure's coverage as a
machine, other than as the deriving handler writes it from the type's declaration, and it rests on
no axiom but Lean's three. -/
def requireCodes (c : Name) : MetaM Unit := do
  let lines := report (← audit c [])
  unless lines.isEmpty do
    throwError "the audit of declared types' codes refuses {c}:\n{"\n".intercalate lines.toList}"

end LeanIntent.CodeAudit
