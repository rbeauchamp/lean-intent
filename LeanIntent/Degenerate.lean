import LeanIntent.Codes
import LeanIntent.Explain

/-!
# The degenerate subjects of a subject's type

A record can have a model, and so meet O2, and still be met by a subject that does nothing useful: a
sorting record that asks only for an ascending output is met by the function that returns the empty
list for every input. The degenerate check closes this gap with a closed class of
*degenerate subjects*, fixed by the subject's type and never chosen per record: each constant
function, the identity, the empty output and each projection. Each degenerate subject that meets
the record is reported as a possibility, "your specification allows this", to be confirmed or
declined: by the owner when it is a fork their intent does not settle that changes what they get,
and otherwise as a decision made on the owner's behalf.

## The class

The class covers a subject of type `a₁ → … → aₙ → b`, with `n ≥ 0`, whose argument types `aᵢ` and
output type `b` have codes in `Ty` (`LeanIntent.Codes`); with no argument it is a plain value. Its
code is a `Sig`. Its degenerate subjects (`Sig.degenerate`) are:

* the constant function at each value the rule `Ty.Small` admits: every value of `b` where `b` has
  finitely many, and where it has infinitely many, so that the constant functions are infinitely many
  too (`Sig.constants_infinite`), the values the rule fixes. Where they number at most `Ty.listBound`
  (`Ty.count`), each is a member (`Sig.const_mem_of_small`). Above it, however large `b` is, two
  members hold them all: the constant at `b`'s empty value, and `.others`, the rest as one member, on
  which one verdict states that some constant among them meets the record or that none does. So a
  check of `UInt64` proves one theorem about `2 ^ 64` functions and enumerates nothing, and leaves out
  no constant a listing would hold (`constant_covered`, `constant_covered_of_finite`). The empty
  output, the constant at `b`'s empty value, is always a member (`Sig.empty_output_mem`);
* each projection, the function that returns a component of type `b` of one of its arguments: the
  argument itself, a component of a pair inside it, a component of a field of a declared type with one
  constructor inside it, such as a structure, or a component of what a function inside it returns when
  applied to a source (`ArgProj`, `Sig.proj_mem`). A source is the empty value of the function's
  argument type, or a component of an argument reached without applying a function (`ArgSource`), so a
  function is applied one level deep and the projections are finitely many. The identity is the
  projection of a function of one argument onto that argument (`Sig.identity_mem`), and for a function
  taking a function, `fun f n => f n`.

`Sig.mem_degenerate_iff` states the membership of the class apart from the list that computes it,
and `Fn.apply_const` and `ArgProj.apply_fn` what a constant and a projection return, apart from how
each is built. No class is empty
(`Sig.degenerate_ne_nil`), so a record is never checked against nothing, and every class has at most
`Ty.listBound` members besides its projections (`Sig.length_degenerate_le`).

## The class of a record's type

A subject's code is computed from its type by Lean's instance resolution (`Covered`, built from
`HasCode`): `degenerate W` is the class of the type `W`, and has no record among its arguments, so
it is the same for every record about `W`. A function's code is its type's code flattened (`Sig.ofTy`),
so that a function returning a function is a function of more arguments, and no function is a plain
value, whose class would hold no projection. Each code carries the isomorphism through which it stands
for its type and the proof that both are those the library fixes (`Ty.Stands`, `Sig.Stands`): the
identity for a type built only from those `Ty` builds in, and for a type the project declares, the
code and isomorphism its deriving handler writes from the declaration, which rests on what
`LeanIntent.Declared` states. A subject is a value of `W`, carried back through that isomorphism from
a value of the output type or from a projection (`Degenerate.constantSubject`,
`Degenerate.projSubject`). A member stands for one such subject, or `.others` for many
(`Degenerate.Is`), so no function takes a member and returns one subject: `Degenerate.reading` reads
a member as the subject it names or as the group of other constants. A type with no code is
not covered: no `Covered W` instance exists, so Lean reports that it cannot synthesize one, and no
verdict about the class of `W` can be stated. Among such types are dependent functions, `Fin 0` and
`Fin n` for a variable `n`, and every type constrained by proofs, indices or value parameters other
than `Fin (n + 1)` and `BitVec w`.

## Verdicts

For a record `r` about `W`, `Verdicts r bs` states, for each member of the class in order, whether a
subject it stands for (`Degenerate.Is`) meets `r` (`Degenerate.Meets`): `true` that one does, `false`
that none does, as goals the agent proves (`verdicts`), so
each verdict is a theorem Lean's kernel checks, never the result of running code. The verdicts are
part of the theorem's statement, and a list of the wrong length is refused (`verdicts_correct`).
`metBy W bs` lists the members the verdicts say meet the record, which are exactly those that do
(`mem_metBy`). Mapped through `Degenerate.reading`, that list shows each subject it names, which meets
the record (`meets_of_subject_mem_metBy`), and shows the other constants as a group exactly when some
one of them meets it (`otherConstants_mem_metBy_iff`). `possibilities h`, from a proof `h : Verdicts r bs`, reports each as a
`Consequence` of kind possibility, the predicate that the subject is one the member stands for
(`Degenerate.consequence`), which holds of the record as it is shown (`possibilities_holdsOf`), so
it can be shown with the record (`LeanIntent.Shown`) and an answer to it stored and kept by
every later revision (`LeanIntent.Answers`). A report exists only for proved verdicts. A declined
one is kept by exactly the revisions that no subject of the member meets
(`Degenerate.declined_keptBy_iff`). Proved verdicts that report nothing refute every subject of every
member (`not_meets_of_metBy_eq_nil`).
-/

namespace LeanIntent

/-- The code of a subject's type: functions of the arguments `args`, in order, to `out`. With no
arguments it is the type `out` itself. -/
structure Sig where
  /-- The codes of the argument types. -/
  args : List Ty
  /-- The code of the output type. -/
  out : Ty
  deriving DecidableEq

namespace Sig

/-- Functions of the arguments `as`, in order, to values of `b`. -/
@[reducible] def Fn (b : Ty) : List Ty → Type
  | [] => b.denote
  | a :: as => a.denote → Fn b as

/-- The type a subject's code denotes, through which it stands for the subject's type. -/
@[reducible] def denote (σ : Sig) : Type := Fn σ.out σ.args

/-- A tuple of arguments of the types `as`. -/
@[reducible] def Args : List Ty → Type
  | [] => Unit
  | a :: as => a.denote × Args as

/-- A function applied to a tuple of its arguments. -/
def Fn.apply {b : Ty} : {as : List Ty} → Fn b as → Args as → b.denote
  | [], f, _ => f
  | _ :: _, f, xs => Fn.apply (f xs.1) xs.2

/-- The function of the arguments `as` that returns `v` whatever they are. -/
def Fn.const (b : Ty) (v : b.denote) : (as : List Ty) → Fn b as
  | [] => v
  | _ :: as => fun _ => Fn.const b v as

theorem Fn.apply_const {b : Ty} (v : b.denote) :
    (as : List Ty) → (xs : Args as) → (Fn.const b v as).apply xs = v
  | [], _ => rfl
  | _ :: as, xs => Fn.apply_const v as xs.2

/-- The function of the arguments `as` that returns what `g` returns of the tuple of them. -/
def Fn.curry (b : Ty) : (as : List Ty) → (Args as → b.denote) → Fn b as
  | [], g => g ()
  | _ :: as, g => fun x => Fn.curry b as fun xs => g (x, xs)

theorem Fn.apply_curry {b : Ty} : (as : List Ty) → (g : Args as → b.denote) → (xs : Args as) →
    (Fn.curry b as g).apply xs = g xs
  | [], _, () => rfl
  | _ :: as, g, (x, xs) => Fn.apply_curry as (fun ys => g (x, ys)) xs

/-- The code of a subject whose type has the code `t`: a function's argument followed by the
arguments of its result, down to a result that is not a function, so that a function returning a
function is a function of more arguments. -/
@[reducible] def ofTy : Ty → Sig
  | .arrow a b => ⟨a :: (ofTy b).args, (ofTy b).out⟩
  | .unit => ⟨[], .unit⟩
  | .bool => ⟨[], .bool⟩
  | .nat => ⟨[], .nat⟩
  | .int => ⟨[], .int⟩
  | .string => ⟨[], .string⟩
  | .list a => ⟨[], .list a⟩
  | .array a => ⟨[], .array a⟩
  | .option a => ⟨[], .option a⟩
  | .prod a b => ⟨[], .prod a b⟩
  | .sum a b => ⟨[], .sum a b⟩
  | .decl n ps r => ⟨[], .decl n ps r⟩
  | .fin n => ⟨[], .fin n⟩
  | .atom k => ⟨[], .atom k⟩

/-- A type's denotation and that of the subject's code `ofTy` computes from it are one type. -/
def flat : (t : Ty) → Iso t.denote (ofTy t).denote
  | .arrow a b => (Iso.refl a.denote).arrow (flat b)
  | .unit | .bool | .nat | .int | .string | .list _ | .array _ | .option _ | .prod _ _ | .sum _ _
  | .decl _ _ _ | .fin _ | .atom _ => Iso.refl _

/-- The output of a subject's code is never a function, so a code computed from a type holds every
argument a function takes, and with them its projections. -/
theorem out_ofTy_ne_arrow : (t : Ty) → (a b : Ty) → (ofTy t).out ≠ .arrow a b
  | .arrow _ r, a, b => out_ofTy_ne_arrow r a b
  | .unit, _, _ | .bool, _, _ | .nat, _, _ | .int, _, _ | .string, _, _ | .list _, _, _
  | .array _, _, _ | .option _, _, _ | .prod _ _, _, _ | .sum _ _, _, _ | .decl _ _ _, _, _
  | .fin _, _, _ | .atom _, _, _ => nofun

end Sig

open Sig

mutual

/-- A component of type `c` inside a value of type `t`: the value itself, a component of one side of
a pair, a component of a field of a declared type with one constructor, or a component of what a
function returns when applied to the argument a source `s : S a` gives. -/
inductive Ty.Proj (S : Ty → Type) : Ty → Ty → Type
  /-- The value itself. -/
  | self (t : Ty) : Ty.Proj S t t
  /-- A component of the left side of a pair. -/
  | fst {a c : Ty} (b : Ty) : Ty.Proj S a c → Ty.Proj S (.prod a b) c
  /-- A component of the right side of a pair. -/
  | snd {b c : Ty} (a : Ty) : Ty.Proj S b c → Ty.Proj S (.prod a b) c
  /-- A component of a field of a declared type whose representation is the chain of fields `r`. -/
  | field {r c : Ty} (n : Lean.Name) (ps : Ty) : Ty.FieldProj S r c → Ty.Proj S (.decl n ps r) c
  /-- A component of what a function returns on the argument the source `s` gives. -/
  | app {a b c : Ty} (s : S a) : Ty.Proj S b c → Ty.Proj S (.arrow a b) c

/-- A component of type `c` inside one field of a chain of fields `r`, the representation of a
declared type with one constructor: the fields, in order, each paired with the chain of the fields
after it, and the last with the unit type. The chain itself, or the rest of it after a field, is not
a component. -/
inductive Ty.FieldProj (S : Ty → Type) : Ty → Ty → Type
  /-- A component of the first field. -/
  | head {a c : Ty} (rest : Ty) : Ty.Proj S a c → Ty.FieldProj S (.prod a rest) c
  /-- A component of a later field. -/
  | tail {rest c : Ty} (a : Ty) : Ty.FieldProj S rest c → Ty.FieldProj S (.prod a rest) c

end

mutual

/-- The component a path selects, where `ev` gives the value of each source. -/
def Ty.Proj.get {S : Ty → Type} (ev : (a : Ty) → S a → a.denote) :
    {t c : Ty} → Ty.Proj S t c → t.denote → c.denote
  | _, _, .self _, x => x
  | _, _, .fst _ p, x => p.get ev x.1
  | _, _, .snd _ p, x => p.get ev x.2
  | _, _, .field _ _ q, x => q.get ev x
  | _, _, .app s p, f => p.get ev (f (ev _ s))

/-- The component a path into a field selects. -/
def Ty.FieldProj.get {S : Ty → Type} (ev : (a : Ty) → S a → a.denote) :
    {r c : Ty} → Ty.FieldProj S r c → r.denote → c.denote
  | _, _, .head _ p, x => p.get ev x.1
  | _, _, .tail _ q, x => q.get ev x.2

end

/-- The path to the value itself, between two equal codes. -/
def Ty.Proj.ofEq {S : Ty → Type} : {t c : Ty} → t = c → Ty.Proj S t c
  | _, _, rfl => .self _

/-- The paths to the value itself when `t` is `c`: one, or none. -/
def Ty.selfProjs {S : Ty → Type} (c t : Ty) : List (Ty.Proj S t c) :=
  if h : t = c then [.ofEq h] else []

mutual

/-- Every path to a component of type `c` inside a value of type `t`, each function on each source
`src` lists. -/
def Ty.projs {S : Ty → Type} (src : (a : Ty) → List (S a)) (c : Ty) :
    (t : Ty) → List (Ty.Proj S t c)
  | .prod a b =>
    Ty.selfProjs c (.prod a b) ++ (Ty.projs src c a).map (.fst b) ++ (Ty.projs src c b).map (.snd a)
  | .decl n ps r => Ty.selfProjs c (.decl n ps r) ++ (Ty.fieldProjs src c r).map (.field n ps)
  | .arrow a b =>
    Ty.selfProjs c (.arrow a b) ++ (src a).flatMap fun s => (Ty.projs src c b).map (.app s)
  | t => Ty.selfProjs c t

/-- Every path to a component of type `c` inside a field of the chain of fields `r`. -/
def Ty.fieldProjs {S : Ty → Type} (src : (a : Ty) → List (S a)) (c : Ty) :
    (r : Ty) → List (Ty.FieldProj S r c)
  | .prod a rest => (Ty.projs src c a).map (.head rest) ++ (Ty.fieldProjs src c rest).map (.tail a)
  | _ => []

end

theorem Ty.self_mem_selfProjs {S : Ty → Type} (t : Ty) :
    (Ty.Proj.self t : Ty.Proj S t t) ∈ Ty.selfProjs t t := by
  simp [Ty.selfProjs, Ty.Proj.ofEq]

mutual

/-- `projs` lists every path whose sources `src` lists. -/
theorem Ty.mem_projs {S : Ty → Type} {src : (a : Ty) → List (S a)} (hs : ∀ a (s : S a), s ∈ src a)
    {c : Ty} : {t : Ty} → (p : Ty.Proj S t c) → p ∈ Ty.projs src c t
  | _, .self t => by
      cases t <;> simp only [Ty.projs, List.mem_append] <;>
        first
        | exact Ty.self_mem_selfProjs _
        | exact .inl (.inl (Ty.self_mem_selfProjs _))
        | exact .inl (Ty.self_mem_selfProjs _)
  | _, .fst b p => by
      simp only [Ty.projs, List.mem_append, List.mem_map]
      exact .inl (.inr ⟨p, Ty.mem_projs hs p, rfl⟩)
  | _, .snd a p => by
      simp only [Ty.projs, List.mem_append, List.mem_map]
      exact .inr ⟨p, Ty.mem_projs hs p, rfl⟩
  | _, .field n ps q => by
      simp only [Ty.projs, List.mem_append, List.mem_map]
      exact .inr ⟨q, Ty.mem_fieldProjs hs q, rfl⟩
  | _, .app s p => by
      simp only [Ty.projs, List.mem_append, List.mem_flatMap, List.mem_map]
      exact .inr ⟨s, hs _ s, p, Ty.mem_projs hs p, rfl⟩

/-- `fieldProjs` lists every path into a field whose sources `src` lists. -/
theorem Ty.mem_fieldProjs {S : Ty → Type} {src : (a : Ty) → List (S a)}
    (hs : ∀ a (s : S a), s ∈ src a) {c : Ty} :
    {r : Ty} → (q : Ty.FieldProj S r c) → q ∈ Ty.fieldProjs src c r
  | _, .head rest p => by
      simp only [Ty.fieldProjs, List.mem_append, List.mem_map]
      exact .inl ⟨p, Ty.mem_projs hs p, rfl⟩
  | _, .tail a q => by
      simp only [Ty.fieldProjs, List.mem_append, List.mem_map]
      exact .inr ⟨q, Ty.mem_fieldProjs hs q, rfl⟩

end

/-- A path to a component of type `c` of one of the arguments `as`. -/
inductive ArgPath (S : Ty → Type) (c : Ty) : List Ty → Type
  /-- A component of the first argument. -/
  | here {a : Ty} {as : List Ty} : Ty.Proj S a c → ArgPath S c (a :: as)
  /-- A path into the arguments after the first. -/
  | there {a : Ty} {as : List Ty} : ArgPath S c as → ArgPath S c (a :: as)

namespace ArgPath

variable {S : Ty → Type} {c : Ty}

/-- The component a path selects from a tuple of arguments, where `ev` gives each source's value. -/
def read (ev : (a : Ty) → S a → a.denote) : {as : List Ty} → ArgPath S c as → Args as → c.denote
  | _ :: _, .here p, xs => p.get ev xs.1
  | _ :: _, .there q, xs => q.read ev xs.2

/-- Every path to a component of type `c` of the arguments `as`, whose sources `src` lists. -/
def all (src : (a : Ty) → List (S a)) (c : Ty) : (as : List Ty) → List (ArgPath S c as)
  | [] => []
  | a :: as => (Ty.projs src c a).map .here ++ (all src c as).map .there

/-- `all` lists every path whose sources `src` lists. -/
theorem mem_all {src : (a : Ty) → List (S a)} (hs : ∀ a (s : S a), s ∈ src a) :
    {as : List Ty} → (p : ArgPath S c as) → p ∈ all src c as
  | _ :: _, .here p => List.mem_append.mpr (.inl (List.mem_map.mpr ⟨p, Ty.mem_projs hs p, rfl⟩))
  | _ :: _, .there q => List.mem_append.mpr (.inr (List.mem_map.mpr ⟨q, mem_all hs q, rfl⟩))

end ArgPath

/-- The sources of a path that applies no function: there are none. -/
abbrev NoSource : Ty → Type := fun _ => Empty

/-- Where the argument of a function among the arguments `Γ` comes from, one level deep: the empty
value of its type, or a component of one of `Γ` reached without applying a function, so that the
paths of a function's arguments are finitely many. -/
abbrev ArgSource (Γ : List Ty) (a : Ty) : Type := Option (ArgPath NoSource a Γ)

namespace ArgSource

/-- The value a source gives on a tuple of arguments. -/
def val {Γ : List Ty} (xs : Args Γ) (a : Ty) : ArgSource Γ a → a.denote
  | none => a.empty
  | some p => p.read (fun _ s => nomatch s) xs

/-- Every source of a value of type `a` among the arguments `Γ`. -/
def all (Γ : List Ty) (a : Ty) : List (ArgSource Γ a) :=
  none :: (ArgPath.all (fun _ => []) a Γ).map some

/-- `all` lists every source. -/
theorem mem_all (Γ : List Ty) (a : Ty) : ∀ s : ArgSource Γ a, s ∈ all Γ a
  | none => List.mem_cons_self
  | some p => List.mem_cons_of_mem _
      (List.mem_map.mpr ⟨p, ArgPath.mem_all (fun _ s => nomatch s) p, rfl⟩)

end ArgSource

/-- A projection of functions of the arguments `as` to values of `c`: a component of type `c` of one
of the arguments, a function among them applied to the sources `ArgSource as` gives. -/
abbrev ArgProj (c : Ty) (as : List Ty) : Type := ArgPath (ArgSource as) c as

namespace ArgProj

variable {c : Ty}

/-- The component a projection selects from a tuple of arguments. -/
def read {as : List Ty} (p : ArgProj c as) (xs : Args as) : c.denote :=
  ArgPath.read (ArgSource.val xs) p xs

/-- A projection as a function of its arguments. -/
def fn {as : List Ty} (p : ArgProj c as) : Fn c as := Fn.curry c as p.read

/-- Every projection of functions of the arguments `as` to values of `c`. -/
def all (c : Ty) (as : List Ty) : List (ArgProj c as) := ArgPath.all (ArgSource.all as) c as

/-- `all` lists every projection. -/
theorem mem_all {as : List Ty} (p : ArgProj c as) : p ∈ all c as :=
  ArgPath.mem_all (ArgSource.mem_all as) p

/-- A projection, as a function, returns the component it selects. -/
theorem apply_fn {as : List Ty} (p : ArgProj c as) (xs : Args as) : p.fn.apply xs = p.read xs :=
  Fn.apply_curry as p.read xs

end ArgProj

/-- A degenerate subject of the type `σ` denotes, by its description: the constant function at a
value of the output type, a projection, or, as one member standing for many subjects, every constant
function at a value the class does not list one by one (`Sig.degenerate`). -/
inductive Degenerate (σ : Sig) where
  /-- The function that returns `v` whatever its arguments. -/
  | const (v : σ.out.denote)
  /-- The function that returns the component `p` selects. -/
  | proj (p : ArgProj σ.out σ.args)
  /-- Every constant function at a value of the output type's rule `Ty.Small` other than its empty
  value. -/
  | others

/-- The constant members of the class: the constant function at each value of the output type's part
where `count` is at most `Ty.listBound`; and otherwise the constant at its empty value, the empty
output, and all the other constants the rule `Ty.Small` admits as one member. -/
def Sig.constants (σ : Sig) : List (Degenerate σ) :=
  if σ.out.count ≤ Ty.listBound then σ.out.part.map .const else [.const σ.out.empty, .others]

/-- The degenerate subjects of the type `σ` denotes: its constant members, then each projection. -/
def Sig.degenerate (σ : Sig) : List (Degenerate σ) :=
  σ.constants ++ (ArgProj.all σ.out σ.args).map .proj

/-- A tuple of the empty values of the types `as`. -/
def Sig.Args.empty : (as : List Ty) → Args as
  | [] => ()
  | a :: as => (a.empty, Sig.Args.empty as)

namespace Sig

/-- The class, apart from the list that computes it: where the output type's `count` is at most
`Ty.listBound`, the constant function at each value the rule `Ty.Small` admits; above it, the constant
at the empty value and `.others`; and every projection. -/
theorem mem_degenerate_iff {σ : Sig} (d : Degenerate σ) :
    d ∈ σ.degenerate ↔
      (σ.out.count ≤ Ty.listBound ∧ ∃ v, d = .const v ∧ σ.out.Small v) ∨
      (Ty.listBound < σ.out.count ∧ (d = .const σ.out.empty ∨ d = .others)) ∨
      ∃ p, d = .proj p := by
  simp only [degenerate, constants, List.mem_append]
  by_cases h : σ.out.count ≤ Ty.listBound
  · simp only [h, ↓reduceIte, true_and, Nat.not_lt.mpr h, false_and, false_or, List.mem_map]
    constructor
    · rintro (⟨v, hv, rfl⟩ | ⟨p, _, rfl⟩)
      · exact .inl ⟨v, rfl, (Ty.mem_part_iff _ h v).mp hv⟩
      · exact .inr ⟨p, rfl⟩
    · rintro (⟨v, rfl, hv⟩ | ⟨p, rfl⟩)
      · exact .inl ⟨v, (Ty.mem_part_iff _ h v).mpr hv, rfl⟩
      · exact .inr ⟨p, ArgProj.mem_all p, rfl⟩
  · have h' := Nat.lt_of_not_le h
    simp only [h, ↓reduceIte, h', false_and, false_or, true_and, List.mem_cons, List.not_mem_nil,
      or_false, List.mem_map]
    constructor
    · rintro (h | ⟨p, _, rfl⟩)
      · exact .inl h
      · exact .inr ⟨p, rfl⟩
    · rintro (h | ⟨p, rfl⟩)
      · exact .inl h
      · exact .inr ⟨p, ArgProj.mem_all p, rfl⟩

/-- The empty output, the constant function at the output type's empty value, is in the class. -/
theorem empty_output_mem (σ : Sig) : Degenerate.const σ.out.empty ∈ σ.degenerate := by
  refine (mem_degenerate_iff _).mpr ?_
  by_cases h : σ.out.count ≤ Ty.listBound
  · exact .inl ⟨h, _, rfl, Ty.small_empty _⟩
  · exact .inr (.inl ⟨Nat.lt_of_not_le h, .inl rfl⟩)

/-- No class is empty. -/
theorem degenerate_ne_nil (σ : Sig) : σ.degenerate ≠ [] := List.ne_nil_of_mem (empty_output_mem σ)

/-- Where the output type's `count` is at most `Ty.listBound`, the constant function at each value the
rule `Ty.Small` admits is in the class. -/
theorem const_mem_of_small {σ : Sig} (hc : σ.out.count ≤ Ty.listBound) {v : σ.out.denote}
    (h : σ.out.Small v) : Degenerate.const v ∈ σ.degenerate :=
  (mem_degenerate_iff _).mpr (.inl ⟨hc, v, rfl, h⟩)

/-- Where the output type's `count` is above `Ty.listBound`, the other constants are a member. -/
theorem others_mem {σ : Sig} (hc : Ty.listBound < σ.out.count) : Degenerate.others ∈ σ.degenerate :=
  (mem_degenerate_iff _).mpr (.inr (.inl ⟨hc, .inr rfl⟩))

/-- Where the output type has finitely many values and its `count` is at most `Ty.listBound`, the
constant function at each is in the class. -/
theorem const_mem_of_finite {σ : Sig} (hc : σ.out.count ≤ Ty.listBound) (h : σ.out.finite = true)
    (v : σ.out.denote) : Degenerate.const v ∈ σ.degenerate :=
  const_mem_of_small hc (Ty.small_of_finite _ h v)

/-- Every projection is in the class. -/
theorem proj_mem {σ : Sig} (p : ArgProj σ.out σ.args) : Degenerate.proj p ∈ σ.degenerate :=
  (mem_degenerate_iff _).mpr (.inr (.inr ⟨p, rfl⟩))

/-- The class holds at most `Ty.listBound` constant members, whatever the output type, so the type's
own number of values never enters the size of a check. -/
theorem length_constants_le (σ : Sig) : σ.constants.length ≤ Ty.listBound := by
  unfold constants
  split
  · rename_i h
    simpa using Nat.le_trans (Ty.length_part_le σ.out) h
  · simp [Ty.listBound]

/-- The class has at most `Ty.listBound` members besides its projections. -/
theorem length_degenerate_le (σ : Sig) :
    σ.degenerate.length ≤ Ty.listBound + (ArgProj.all σ.out σ.args).length := by
  simp only [degenerate, List.length_append, List.length_map]
  exact Nat.add_le_add_right (length_constants_le σ) _

/-- The identity of a function of one argument to its own type is in the class. -/
theorem identity_mem (t : Ty) :
    ∃ p : ArgProj t [t], Degenerate.proj p ∈ (⟨[t], t⟩ : Sig).degenerate ∧ p.fn = fun x => x :=
  ⟨.here (.self t), proj_mem _, rfl⟩

/-- Where the output type has infinitely many values, so has the type infinitely many constant
functions: an injection from `Nat` to its subjects, each of which returns one value whatever its
arguments. The class then takes the constants only at the values `Ty.Small` admits. -/
theorem constants_infinite {σ : Sig} (h : σ.out.finite = false) :
    ∃ f : Nat → σ.denote, Function.Injective f ∧ ∀ n, ∃ v, ∀ xs, Fn.apply (f n) xs = v := by
  obtain ⟨g, hg⟩ := Ty.infinite σ.out h
  refine ⟨fun n => Fn.const σ.out (g n) σ.args, fun m n e => hg ?_,
    fun n => ⟨g n, Fn.apply_const (g n) σ.args⟩⟩
  have := congrArg (fun f => Fn.apply f (Args.empty σ.args)) e
  simpa only [Fn.apply_const] using this

end Sig

/-! ## The class of a record's type -/

/-- `t` is the code of `α`, and `e` the isomorphism through which `t` stands for `α`, as the library
fixes them. A code built only from the types `Ty` builds in stands for the type it denotes, through
the cast along their equality (`builtin`), so a type built only from them has one code, and its
isomorphism maps each value to itself. A code with a declared type inside stands for its type through
the isomorphisms of its parts, carried through the map of each type former, a function type's by
mapping its argument back and its result forth (`Iso.arrow`). A type the project
declares stands for itself through the code and isomorphism its declaration fixes: the last
constructor, which admits them, is private, and the deriving handler of `LeanIntent.Declared`, which
reads them from the declaration, is the only code of the library that applies it. Lean's privacy
binds names only, so that nothing else applies it is trusted (`LeanIntent.Declared`). -/
inductive Ty.Stands : (α : Type) → (t : Ty) → Iso α t.denote → Prop
  | builtin {α : Type} (t : Ty) (h : α = t.denote) : t.builtin = true → Ty.Stands α t (Iso.ofEq h)
  | list {α : Type} {t : Ty} {e : Iso α t.denote} :
      Ty.Stands α t e → Ty.Stands (List α) (.list t) e.list
  | array {α : Type} {t : Ty} {e : Iso α t.denote} :
      Ty.Stands α t e → Ty.Stands (Array α) (.array t) e.array
  | option {α : Type} {t : Ty} {e : Iso α t.denote} :
      Ty.Stands α t e → Ty.Stands (Option α) (.option t) e.option
  | prod {α β : Type} {a b : Ty} {e : Iso α a.denote} {f : Iso β b.denote} :
      Ty.Stands α a e → Ty.Stands β b f → Ty.Stands (α × β) (.prod a b) (e.prod f)
  | sum {α β : Type} {a b : Ty} {e : Iso α a.denote} {f : Iso β b.denote} :
      Ty.Stands α a e → Ty.Stands β b f → Ty.Stands (α ⊕ β) (.sum a b) (e.sum f)
  | arrow {α β : Type} {a b : Ty} {e : Iso α a.denote} {f : Iso β b.denote} :
      Ty.Stands α a e → Ty.Stands β b f → Ty.Stands (α → β) (.arrow a b) (e.arrow f)
  | private decl {α : Type} (n : Lean.Name) (ps r : Ty) (e : Iso α (Ty.decl n ps r).denote) :
      Ty.Stands α (.decl n ps r) e

/-- A code that denotes `α` itself, for a type built only from those `Ty` builds in, found by Lean's
instance resolution: one instance for each type former `Ty` has. Another instance for `α` would have
to prove its code's type equal to `α`. -/
class ExactCode (α : Type) where
  /-- The code. -/
  code : Ty
  /-- The code denotes `α`. -/
  denote_eq : α = code.denote
  /-- No declared type is inside the code. -/
  builtin : code.builtin = true

instance : ExactCode Unit := ⟨.unit, rfl, rfl⟩
instance : ExactCode Bool := ⟨.bool, rfl, rfl⟩
instance : ExactCode Nat := ⟨.nat, rfl, rfl⟩
instance : ExactCode Int := ⟨.int, rfl, rfl⟩
instance : ExactCode String := ⟨.string, rfl, rfl⟩
instance {n : Nat} : ExactCode (Fin (n + 1)) := ⟨.fin n, rfl, rfl⟩
instance : ExactCode Char := ⟨.atom .char, rfl, rfl⟩
instance : ExactCode UInt8 := ⟨.atom .uint8, rfl, rfl⟩
instance : ExactCode UInt16 := ⟨.atom .uint16, rfl, rfl⟩
instance : ExactCode UInt32 := ⟨.atom .uint32, rfl, rfl⟩
instance : ExactCode UInt64 := ⟨.atom .uint64, rfl, rfl⟩
instance : ExactCode USize := ⟨.atom .usize, rfl, rfl⟩
instance : ExactCode Int8 := ⟨.atom .int8, rfl, rfl⟩
instance : ExactCode Int16 := ⟨.atom .int16, rfl, rfl⟩
instance : ExactCode Int32 := ⟨.atom .int32, rfl, rfl⟩
instance : ExactCode Int64 := ⟨.atom .int64, rfl, rfl⟩
instance : ExactCode ISize := ⟨.atom .isize, rfl, rfl⟩
instance : ExactCode Float := ⟨.atom .float, rfl, rfl⟩
instance : ExactCode Float32 := ⟨.atom .float32, rfl, rfl⟩
instance {w : Nat} : ExactCode (BitVec w) := ⟨.atom (.bitVec w), rfl, rfl⟩

instance {α : Type} [h : ExactCode α] : ExactCode (List α) :=
  ⟨.list h.code, congrArg List h.denote_eq, h.builtin⟩

instance {α : Type} [h : ExactCode α] : ExactCode (Array α) :=
  ⟨.array h.code, congrArg Array h.denote_eq, h.builtin⟩

instance {α : Type} [h : ExactCode α] : ExactCode (Option α) :=
  ⟨.option h.code, congrArg Option h.denote_eq, h.builtin⟩

instance {α β : Type} [ha : ExactCode α] [hb : ExactCode β] : ExactCode (α × β) :=
  ⟨.prod ha.code hb.code, by
    show (α × β) = (ha.code.denote × hb.code.denote)
    rw [← ha.denote_eq, ← hb.denote_eq], by
    show (ha.code.builtin && hb.code.builtin) = true
    rw [ha.builtin, hb.builtin]; rfl⟩

instance {α β : Type} [ha : ExactCode α] [hb : ExactCode β] : ExactCode (α ⊕ β) :=
  ⟨.sum ha.code hb.code, by
    show (α ⊕ β) = (ha.code.denote ⊕ hb.code.denote)
    rw [← ha.denote_eq, ← hb.denote_eq], by
    show (ha.code.builtin && hb.code.builtin) = true
    rw [ha.builtin, hb.builtin]; rfl⟩

instance {α β : Type} [ha : ExactCode α] [hb : ExactCode β] : ExactCode (α → β) :=
  ⟨.arrow ha.code hb.code, by
    show (α → β) = (ha.code.denote → hb.code.denote)
    rw [← ha.denote_eq, ← hb.denote_eq], by
    show (ha.code.builtin && hb.code.builtin) = true
    rw [ha.builtin, hb.builtin]; rfl⟩

/-- A code for the type `α`, found by Lean's instance resolution, with the isomorphism through which
it stands for `α` and the proof that both are those the library fixes (`Ty.Stands`): the exact code
of a type built only from those `Ty` builds in, through the cast along their equality; the code of a
type former applied to types with a declared type inside, through the former's map; and the code of
a type the project declares, which its deriving handler (`LeanIntent.Declared`) writes. -/
class HasCode (α : Type) where
  /-- The code. -/
  code : Ty
  /-- The isomorphism through which the code stands for `α`. -/
  iso : Iso α code.denote
  /-- The code and the isomorphism are those the library fixes. -/
  stands : Ty.Stands α code iso

/-- A type built only from those `Ty` builds in, through its exact code. Tried first, so that such a
type's isomorphism maps each value to itself by definition. -/
instance (priority := high) {α : Type} [h : ExactCode α] : HasCode α :=
  ⟨h.code, Iso.ofEq h.denote_eq, .builtin h.code h.denote_eq h.builtin⟩

instance {α : Type} [h : HasCode α] : HasCode (List α) := ⟨.list h.code, h.iso.list, .list h.stands⟩

instance {α : Type} [h : HasCode α] : HasCode (Array α) :=
  ⟨.array h.code, h.iso.array, .array h.stands⟩

instance {α : Type} [h : HasCode α] : HasCode (Option α) :=
  ⟨.option h.code, h.iso.option, .option h.stands⟩

instance {α β : Type} [ha : HasCode α] [hb : HasCode β] : HasCode (α × β) :=
  ⟨.prod ha.code hb.code, ha.iso.prod hb.iso, .prod ha.stands hb.stands⟩

instance {α β : Type} [ha : HasCode α] [hb : HasCode β] : HasCode (α ⊕ β) :=
  ⟨.sum ha.code hb.code, ha.iso.sum hb.iso, .sum ha.stands hb.stands⟩

instance {α β : Type} [ha : HasCode α] [hb : HasCode β] : HasCode (α → β) :=
  ⟨.arrow ha.code hb.code, ha.iso.arrow hb.iso, .arrow ha.stands hb.stands⟩

/-- `σ` is the code of `W`, and `e` the isomorphism through which `σ` stands for `W`, as the library
fixes them: computed from the code of `W` by `Sig.ofTy`, so that a function has the flattened code and
no function type is a plain value, whose class would hold no projection. -/
inductive Sig.Stands : (W : Type) → (σ : Sig) → Iso W σ.denote → Prop
  | of {α : Type} {t : Ty} {e : Iso α t.denote} :
      Ty.Stands α t e → Sig.Stands α (Sig.ofTy t) (e.trans (Sig.flat t))

/-- A code that stands for a type has no function as its output: no instance can present a function
as a plain value, whose class would hold no projection. -/
theorem Sig.Stands.out_ne_arrow {W : Type} {σ : Sig} {e : Iso W σ.denote} (h : Sig.Stands W σ e)
    (a b : Ty) : σ.out ≠ .arrow a b := by
  cases h
  exact Sig.out_ofTy_ne_arrow _ a b

/-- The type `W` is covered by the degenerate class: the code of a function of coded argument types
to a coded output type, or of a plain value of a coded type, found by Lean's instance resolution
from `W` alone, with the isomorphism through which it stands for `W`. A type with no such code has
no instance, so Lean reports that it cannot synthesize `Covered W` and the class of `W` cannot be
named. -/
class Covered (W : Type) where
  /-- The code of `W`. -/
  sig : Sig
  /-- The isomorphism through which the code stands for `W`. -/
  iso : Iso W sig.denote
  /-- The code and the isomorphism are those the library fixes. -/
  stands : Sig.Stands W sig iso

/-- A type with a code is covered through the subject's code computed from it. -/
instance {α : Type} [h : HasCode α] : Covered α :=
  ⟨Sig.ofTy h.code, h.iso.trans (Sig.flat h.code), .of h.stands⟩

/-- The degenerate subjects of the type `W`, by their descriptions: the class of `W`'s code. It
takes no record, so it is the same for every record about `W`. -/
def degenerate (W : Type) [c : Covered W] : List (Degenerate c.sig) := c.sig.degenerate

/-- The constant subject of type `W` at the value `v`, carried back to `W` through the isomorphism by
which `W`'s code stands for `W`. It takes a value and no member, so it cannot be given a member
standing for many subjects. -/
def Degenerate.constantSubject {W : Type} [c : Covered W] (v : c.sig.out.denote) : W :=
  c.iso.inv (Fn.const c.sig.out v c.sig.args)

/-- The subject of type `W` that returns the component the path `p` selects, carried back to `W` as
`Degenerate.constantSubject` is. -/
def Degenerate.projSubject {W : Type} [c : Covered W] (p : ArgProj c.sig.out c.sig.args) : W :=
  c.iso.inv p.fn

/-- The constant subject is the constant function, carried to `W` through the isomorphism that
`Sig.Stands` fixes: for a type built only from those `Ty` builds in, the identity, so that no code can
mis-encode such a type; and for a type the project declares, the isomorphism its deriving handler
writes from the declaration (`LeanIntent.Declared`, which states what that rests on). -/
theorem Degenerate.iso_constantSubject {W : Type} [c : Covered W] (v : c.sig.out.denote) :
    c.iso.to (Degenerate.constantSubject v : W) = Fn.const c.sig.out v c.sig.args :=
  c.iso.to_inv _

/-- The projection subject is the projection, carried to `W` through the same isomorphism. -/
theorem Degenerate.iso_projSubject {W : Type} [c : Covered W] (p : ArgProj c.sig.out c.sig.args) :
    c.iso.to (Degenerate.projSubject p : W) = p.fn :=
  c.iso.to_inv _

/-- What a member of the class says of `W`'s subjects: the one subject it stands for, or that it
stands for the group of constants other than the one at the empty value. -/
inductive Degenerate.Reading (W : Type) where
  /-- The one subject the member stands for. -/
  | subject (w : W)
  /-- The group of constants `.others` stands for, of which it names none. -/
  | otherConstants

/-- A member of the class read as what it says of `W`'s subjects. It is total, so reading a list keeps
every member, a group among them. -/
def Degenerate.reading {W : Type} [c : Covered W] : Degenerate c.sig → Degenerate.Reading W
  | .const v => .subject (Degenerate.constantSubject v)
  | .proj p => .subject (Degenerate.projSubject p)
  | .others => .otherConstants

/-- No covered type's class is empty, so no record is checked against nothing. -/
theorem degenerate_ne_nil (W : Type) [Covered W] : degenerate W ≠ [] := Sig.degenerate_ne_nil _

/-! ## Verdicts -/

section Verdicts

variable {W : Type} [c : Covered W]

/-- `w` is a subject the description `d` stands for: for `.others`, the constant function at a value
of the rule `Ty.Small` other than the output type's empty value, and otherwise the one subject `d`
stands for. -/
def Degenerate.Is (d : Degenerate c.sig) (w : W) : Prop :=
  match d with
  | .const v => w = Degenerate.constantSubject v
  | .proj p => w = Degenerate.projSubject p
  | .others => ∃ v, c.sig.out.Small v ∧ v ≠ c.sig.out.empty ∧ w = Degenerate.constantSubject v

/-- A subject the description `d` stands for meets `r`. For a member standing for one subject this is
that subject meeting `r`; for `.others`, some constant among them does, which a proof states of all
of them at once, so that no value of the type is enumerated. -/
def Degenerate.Meets (d : Degenerate c.sig) (r : IntentRecord W) : Prop :=
  match d with
  | .const v => r.Meets (Degenerate.constantSubject v)
  | .proj p => r.Meets (Degenerate.projSubject p)
  | .others => ∃ w, (Degenerate.others : Degenerate c.sig).Is w ∧ r.Meets w

theorem Degenerate.meets_iff (d : Degenerate c.sig) (r : IntentRecord W) :
    d.Meets r ↔ ∃ w, d.Is w ∧ r.Meets w := by
  cases d with
  | const v =>
    refine ⟨fun h => ⟨_, rfl, h⟩, fun ⟨w, e, h⟩ => ?_⟩
    rwa [show w = Degenerate.constantSubject v from e] at h
  | proj p =>
    refine ⟨fun h => ⟨_, rfl, h⟩, fun ⟨w, e, h⟩ => ?_⟩
    rwa [show w = Degenerate.projSubject p from e] at h
  | others => exact Iff.rfl

/-- A reading that names a subject names the one subject the member stands for. -/
theorem Degenerate.is_of_reading_eq_subject {d : Degenerate c.sig} {w : W}
    (h : d.reading = .subject w) : d.Is w ∧ ∀ w', d.Is w' → w' = w := by
  cases d with
  | const v =>
    obtain rfl := Degenerate.Reading.subject.inj h
    exact ⟨rfl, fun _ e => e⟩
  | proj p =>
    obtain rfl := Degenerate.Reading.subject.inj h
    exact ⟨rfl, fun _ e => e⟩
  | others => exact Degenerate.Reading.noConfusion h

/-- The only member read as the group is `.others`. -/
theorem Degenerate.reading_eq_otherConstants_iff (d : Degenerate c.sig) :
    d.reading = (.otherConstants : Degenerate.Reading W) ↔ d = .others := by
  cases d <;> simp [Degenerate.reading]

/-- The goal that `b` is the verdict on the member `d` for `r`: that a subject of `d` meets `r` when
`b` is `true`, and that none does when `b` is `false`. -/
def verdictGoal (r : IntentRecord W) (d : Degenerate c.sig) : Bool → Prop
  | true => d.Meets r
  | false => ¬ d.Meets r

/-- The goals that `bs` are, in order, the verdicts on the members that the descriptions `ds` state,
and the goal `False` when the two lists differ in length. -/
def verdictGoals (r : IntentRecord W) : List (Degenerate c.sig) → List Bool → List Prop
  | [], [] => []
  | d :: ds, b :: bs => verdictGoal r d b :: verdictGoals r ds bs
  | _, _ => [False]

/-- The degenerate check's goals: that `bs` are, in order, the verdicts on the degenerate subjects
of `W` for `r`. -/
def verdicts (r : IntentRecord W) (bs : List Bool) : List Prop := verdictGoals r (degenerate W) bs

/-- `bs` are the verdicts, in order, on the degenerate subjects of `W` for `r`. -/
def Verdicts (r : IntentRecord W) (bs : List Bool) : Prop := Goals (verdicts r bs)

/-- What the degenerate check asks, written apart from its former: one verdict for each member of the
class, `true` exactly when a subject the member at the same position stands for meets the record. -/
def intendedVerdicts (r : IntentRecord W) (bs : List Bool) : Prop :=
  bs.length = (degenerate W).length ∧
    ∀ (i : Nat) (hb : i < bs.length) (hd : i < (degenerate W).length),
      (bs[i] = true ↔ ∃ w, (degenerate W)[i].Is w ∧ (∀ x ∈ r.dom, x.holds w) ∧
        ∀ p ∈ r.props, p.holds w)

theorem goals_verdictGoals (r : IntentRecord W) : (ds : List (Degenerate c.sig)) →
    (bs : List Bool) → (Goals (verdictGoals r ds bs) ↔ bs.length = ds.length ∧
      ∀ (i : Nat) (hb : i < bs.length) (hd : i < ds.length), (bs[i] = true ↔ ds[i].Meets r))
  | [], [] => by simp [verdictGoals, Goals]
  | [], _ :: _ => by simp [verdictGoals, Goals]
  | _ :: _, [] => by simp [verdictGoals, Goals]
  | d :: ds, b :: bs => by
      rw [verdictGoals, Goals, goals_verdictGoals r ds bs]
      constructor
      · rintro ⟨hv, hlen, hall⟩
        refine ⟨by simp [hlen], fun i hb hd => ?_⟩
        cases i with
        | zero => cases b <;> simpa [verdictGoal] using hv
        | succ i => simpa using hall i (by simpa using hb) (by simpa using hd)
      · rintro ⟨hlen, hall⟩
        refine ⟨?_, by simpa using hlen, fun i hb hd =>
          hall (i + 1) (Nat.succ_lt_succ hb) (Nat.succ_lt_succ hd)⟩
        have h0 := hall 0 (by simp) (by simp)
        cases b <;> simpa [verdictGoal] using h0

/-- The degenerate check's former states it. -/
theorem verdicts_correct (r : IntentRecord W) (bs : List Bool) :
    Verdicts r bs ↔ intendedVerdicts r bs := by
  rw [Verdicts, verdicts, goals_verdictGoals]
  simp only [intendedVerdicts, Degenerate.meets_iff, IntentRecord.Meets, IntentRecord.Dom,
    IntentRecord.Props]

/-- The descriptions among `ds` whose verdict in `bs` is `true`. -/
def metByGo : List (Degenerate c.sig) → List Bool → List (Degenerate c.sig)
  | d :: ds, true :: bs => d :: metByGo ds bs
  | _ :: ds, false :: bs => metByGo ds bs
  | _, _ => []

/-- The members of the class of `W` whose verdict in `bs` is that they meet the record. -/
def metBy (W : Type) [c : Covered W] (bs : List Bool) : List (Degenerate c.sig) :=
  metByGo (degenerate W) bs

theorem mem_metByGo (r : IntentRecord W) (d : Degenerate c.sig) : (ds : List (Degenerate c.sig)) →
    (bs : List Bool) → Goals (verdictGoals r ds bs) →
      (d ∈ metByGo ds bs ↔ d ∈ ds ∧ d.Meets r)
  | [], [], _ => by simp [metByGo]
  | [], _ :: _, h => absurd h (by simp [verdictGoals, Goals])
  | _ :: _, [], h => absurd h (by simp [verdictGoals, Goals])
  | d' :: ds, true :: bs, ⟨hv, h⟩ => by
      rw [metByGo, List.mem_cons, mem_metByGo r d ds bs h, List.mem_cons]
      constructor
      · rintro (rfl | ⟨hd, hm⟩)
        · exact ⟨.inl rfl, hv⟩
        · exact ⟨.inr hd, hm⟩
      · rintro ⟨rfl | hd, hm⟩
        · exact .inl rfl
        · exact .inr ⟨hd, hm⟩
  | d' :: ds, false :: bs, ⟨hv, h⟩ => by
      rw [metByGo, mem_metByGo r d ds bs h, List.mem_cons]
      constructor
      · rintro ⟨hd, hm⟩
        exact ⟨.inr hd, hm⟩
      · rintro ⟨rfl | hd, hm⟩
        · exact absurd hm hv
        · exact ⟨hd, hm⟩

/-- The members the verdicts report are exactly those a subject of which meets the record. -/
theorem mem_metBy {r : IntentRecord W} {bs : List Bool} (h : Verdicts r bs)
    (d : Degenerate c.sig) : d ∈ metBy W bs ↔ d ∈ degenerate W ∧ d.Meets r :=
  mem_metByGo r d _ bs h

/-- The verdicts report no member exactly when no subject of any member meets the record. -/
theorem metBy_eq_nil_iff {r : IntentRecord W} {bs : List Bool} (h : Verdicts r bs) :
    metBy W bs = [] ↔ ∀ d ∈ degenerate W, ¬ d.Meets r := by
  rw [List.eq_nil_iff_forall_not_mem]
  exact forall_congr' fun d => by rw [mem_metBy h]; exact not_and

/-- A subject named in the reading of what the proved verdicts report meets the record. -/
theorem meets_of_subject_mem_metBy {r : IntentRecord W} {bs : List Bool} (h : Verdicts r bs) {w : W}
    (hw : Degenerate.Reading.subject w ∈ (metBy W bs).map Degenerate.reading) : r.Meets w := by
  obtain ⟨d, hd, e⟩ := List.mem_map.mp hw
  obtain ⟨w', hi, hm⟩ := (d.meets_iff r).mp ((mem_metBy h d).mp hd).2
  rwa [(Degenerate.is_of_reading_eq_subject e).2 w' hi] at hm

/-- Under proved verdicts, the reading of what they report shows the group of other constants exactly
when the class holds that member and one of those constants meets the record, so a group that meets
it is never dropped from the reading, and one that does not is never shown. -/
theorem otherConstants_mem_metBy_iff {r : IntentRecord W} {bs : List Bool} (h : Verdicts r bs) :
    Degenerate.Reading.otherConstants ∈ (metBy W bs).map Degenerate.reading ↔
      Degenerate.others ∈ degenerate W ∧ ∃ v, c.sig.out.Small v ∧ v ≠ c.sig.out.empty ∧
        r.Meets (Degenerate.constantSubject v) := by
  constructor
  · intro hw
    obtain ⟨d, hd, e⟩ := List.mem_map.mp hw
    obtain rfl := (Degenerate.reading_eq_otherConstants_iff d).mp e
    obtain ⟨ho, w, ⟨v, hs, hn, rfl⟩, hm⟩ := (mem_metBy h _).mp hd
    exact ⟨ho, v, hs, hn, hm⟩
  · rintro ⟨ho, v, hs, hn, hm⟩
    exact List.mem_map.mpr ⟨.others, (mem_metBy h _).mpr ⟨ho, _, ⟨v, hs, hn, rfl⟩, hm⟩, rfl⟩

/-- Every constant function at a value of the rule `Ty.Small` is a subject of a member of the class,
however many values the output type has, so a class that lists its constants and one that does not
differ only in how many verdicts state them. -/
theorem constant_covered {v : c.sig.out.denote} (hv : c.sig.out.Small v) :
    ∃ d ∈ degenerate W, d.Is (Degenerate.constantSubject v) := by
  by_cases hc : c.sig.out.count ≤ Ty.listBound
  · exact ⟨.const v, Sig.const_mem_of_small hc hv, rfl⟩
  · by_cases he : v = c.sig.out.empty
    · subst he
      exact ⟨.const _, Sig.empty_output_mem _, rfl⟩
    · exact ⟨.others, Sig.others_mem (Nat.lt_of_not_le hc), v, hv, he, rfl⟩

/-- Where the output type has finitely many values, the constant function at every one of them is a
subject of a member of the class, whether or not they are listed. -/
theorem constant_covered_of_finite (h : c.sig.out.finite = true) (v : c.sig.out.denote) :
    ∃ d ∈ degenerate W, d.Is (Degenerate.constantSubject v) :=
  constant_covered (Ty.small_of_finite _ h v)

/-- Proved verdicts that report nothing refute every subject of every member: no constant the rule
`Ty.Small` admits, listed one by one or not, and no projection meets the record. -/
theorem not_meets_of_metBy_eq_nil {r : IntentRecord W} {bs : List Bool} (h : Verdicts r bs)
    (he : metBy W bs = []) {d : Degenerate c.sig} (hd : d ∈ degenerate W) {w : W} (hw : d.Is w) :
    ¬ r.Meets w :=
  fun hm => (metBy_eq_nil_iff h).mp he d hd ((d.meets_iff r).mpr ⟨w, hw, hm⟩)

/-- The name a degenerate subject's consequence is read by: what kind of member it is. -/
def Degenerate.name {σ : Sig} : Degenerate σ → String
  | .const _ => "the record allows a subject that returns one value whatever its arguments"
  | .proj _ => "the record allows a subject that returns one of its arguments, or a part of one"
  | .others => "the record allows a subject that returns one value whatever its arguments, at some \
      value other than the empty one"

/-- The consequence shown for a member of the class: the possibility that the subject is one the
member stands for. -/
def Degenerate.consequence (d : Degenerate c.sig) : Consequence W :=
  ⟨d.name, .possibility, d.Is⟩

/-- Declining a member's consequence is kept by exactly the revisions that no subject of the member
meets. -/
theorem Degenerate.declined_keptBy_iff (d : Degenerate c.sig) (r : IntentRecord W) :
    (Answer.mk d.consequence .declined).KeptBy r ↔ ¬ d.Meets r := by
  simp only [Answer.KeptBy, Degenerate.consequence, d.meets_iff]
  exact ⟨fun h ⟨w, hi, hm⟩ => h w hm hi, fun h w hm hi => h ⟨w, hi, hm⟩⟩

/-- The consequences reported: one for each member the proved verdicts `bs` say meets the record, in
order. It takes the proof of the verdicts, so no report exists for
verdicts that are not proved. -/
def possibilities {r : IntentRecord W} {bs : List Bool} (_ : Verdicts r bs) : List (Consequence W) :=
  (metBy W bs).map Degenerate.consequence

/-- Under proved verdicts, the reported consequences are exactly those of the members of the class
a subject of which meets the record. -/
theorem mem_possibilities {r : IntentRecord W} {bs : List Bool} (h : Verdicts r bs)
    (x : Consequence W) :
    x ∈ possibilities h ↔ ∃ d ∈ degenerate W, d.Meets r ∧ x = d.consequence := by
  simp only [possibilities, List.mem_map, mem_metBy h]
  exact ⟨fun ⟨d, ⟨hd, hm⟩, e⟩ => ⟨d, hd, hm, e.symm⟩, fun ⟨d, hd, hm, e⟩ => ⟨d, ⟨hd, hm⟩, e.symm⟩⟩

/-- Each reported consequence is a possibility that holds of the record as it is shown: a model of
the record satisfies it, the degenerate subject itself. -/
theorem possibilities_holdsOf {r : IntentRecord W} {bs : List Bool} (h : Verdicts r bs)
    (x : Consequence W) (hx : x ∈ possibilities h) : x.kind = .possibility ∧ x.HoldsOf r := by
  obtain ⟨d, _, hm, rfl⟩ := (mem_possibilities h x).mp hx
  obtain ⟨w, hi, hm⟩ := (d.meets_iff r).mp hm
  exact ⟨rfl, w, hm, hi⟩

end Verdicts

end LeanIntent
