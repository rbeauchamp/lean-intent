import LeanIntent.Codes
import LeanIntent.Explain

/-!
# The degenerate subjects of a subject's type

A record can have a model, and so meet O2, and still be met by a subject that does nothing useful: a
sorting record that asks only for an ascending output is met by the function that returns the empty
list for every input. The degenerate check closes this gap with a closed class of
*degenerate subjects*, fixed by the subject's type and never chosen per record: each constant
function, the identity, the empty output and each projection. Each degenerate subject that meets
the record is shown to the owner as a possibility, "your specification allows this", which the owner
confirms or declines.

## The class

The class covers a subject of type `a₁ → … → aₙ → b`, with `n ≥ 0`, whose argument types `aᵢ` and
output type `b` have codes in `Ty` (`LeanIntent.Codes`); with no argument it is a plain value. Its
code is a `Sig`. Its degenerate subjects (`Sig.degenerate`) are:

* the constant function at each value of `b`'s part, `Ty.part`: every value of `b` where `b` has
  finitely many (`Sig.const_mem_of_finite`), and where it has infinitely many, so that the constant
  functions are infinitely many too (`Sig.constants_infinite`), the values the rule `Ty.Small` fixes.
  Among them is the empty output, the constant at `b`'s empty value (`Sig.empty_output_mem`);
* each projection, the function that returns a component of type `b` of one of its arguments: the
  argument itself, a component of a pair inside it, or a component of a field of a declared type
  with one constructor inside it, such as a structure (`ArgProj`, `Sig.proj_mem`). The identity is
  the projection of a function of one argument onto that argument (`Sig.identity_mem`).

`Sig.mem_degenerate_iff` states the membership of the class apart from the list that computes it,
and `Degenerate.apply_fn` what each member returns, apart from how it is built. No class is empty
(`Sig.degenerate_ne_nil`), so a record is never checked against nothing.

## The class of a record's type

A subject's code is computed from its type by Lean's instance resolution (`Covered`, built from
`HasCode`): `degenerate W` is the class of the type `W`, and has no record among its arguments, so
it is the same for every record about `W`. Each code carries the isomorphism through which it stands
for its type and the proof that both are those the library fixes (`Ty.Stands`, `Sig.Stands`): the
identity for a type built only from those `Ty` builds in, and for a type the project declares, the
code and isomorphism its deriving handler writes from the declaration, which rests on what
`LeanIntent.Declared` states. Each
degenerate subject is a value of `W`, its member carried back through that isomorphism
(`Degenerate.subject`, `Degenerate.iso_subject`). A type with no code is not covered: no
`Covered W` instance exists, so Lean reports that it cannot synthesize one, and no verdict about the
class of `W` can be stated.

## Verdicts

For a record `r` about `W`, `Verdicts r bs` states, for each degenerate subject in order, whether it
meets `r`: `true` that it does, `false` that it does not, as goals the agent proves (`verdicts`), so
each verdict is a theorem Lean's kernel checks, never the result of running code. The verdicts are
part of the theorem's statement, and a list of the wrong length is refused (`verdicts_correct`).
`metBy W bs` lists the degenerate subjects the verdicts say meet the record, which are exactly those
that do (`mem_metBy`). `possibilities h`, from a proof `h : Verdicts r bs`, reports each as a
`Consequence` of kind possibility, the predicate that the subject is that degenerate subject
(`Degenerate.consequence`), which holds of the record as it is shown (`possibilities_holdsOf`), so
it can be shown to the owner (`LeanIntent.Shown`) and the owner's answer to it stored and kept by
every later revision (`LeanIntent.Answers`). A report exists only for proved verdicts. A declined
one is kept by exactly the revisions that the degenerate subject does not meet
(`Degenerate.declined_keptBy_iff`).
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

end Sig

open Sig

mutual

/-- A component of type `c` inside a value of type `t`: the value itself, a component of one side of
a pair, or a component of a field of a declared type with one constructor. -/
inductive Ty.Proj : Ty → Ty → Type
  /-- The value itself. -/
  | self (t : Ty) : Ty.Proj t t
  /-- A component of the left side of a pair. -/
  | fst {a c : Ty} (b : Ty) : Ty.Proj a c → Ty.Proj (.prod a b) c
  /-- A component of the right side of a pair. -/
  | snd {b c : Ty} (a : Ty) : Ty.Proj b c → Ty.Proj (.prod a b) c
  /-- A component of a field of a declared type whose representation is the chain of fields `r`. -/
  | field {r c : Ty} (n : Lean.Name) (ps : Ty) : Ty.FieldProj r c → Ty.Proj (.decl n ps r) c

/-- A component of type `c` inside one field of a chain of fields `r`, the representation of a
declared type with one constructor: the fields, in order, each paired with the chain of the fields
after it, and the last with the unit type. The chain itself, or the rest of it after a field, is not
a component. -/
inductive Ty.FieldProj : Ty → Ty → Type
  /-- A component of the first field. -/
  | head {a c : Ty} (rest : Ty) : Ty.Proj a c → Ty.FieldProj (.prod a rest) c
  /-- A component of a later field. -/
  | tail {rest c : Ty} (a : Ty) : Ty.FieldProj rest c → Ty.FieldProj (.prod a rest) c

end

mutual

/-- The component a path selects. -/
def Ty.Proj.get : {t c : Ty} → Ty.Proj t c → t.denote → c.denote
  | _, _, .self _, x => x
  | _, _, .fst _ p, x => p.get x.1
  | _, _, .snd _ p, x => p.get x.2
  | _, _, .field _ _ q, x => q.get x

/-- The component a path into a field selects. -/
def Ty.FieldProj.get : {r c : Ty} → Ty.FieldProj r c → r.denote → c.denote
  | _, _, .head _ p, x => p.get x.1
  | _, _, .tail _ q, x => q.get x.2

end

/-- The path to the value itself, between two equal codes. -/
def Ty.Proj.ofEq : {t c : Ty} → t = c → Ty.Proj t c
  | _, _, rfl => .self _

/-- The paths to the value itself when `t` is `c`: one, or none. -/
def Ty.selfProjs (c t : Ty) : List (Ty.Proj t c) := if h : t = c then [.ofEq h] else []

mutual

/-- Every path to a component of type `c` inside a value of type `t`. -/
def Ty.projs (c : Ty) : (t : Ty) → List (Ty.Proj t c)
  | .prod a b =>
    Ty.selfProjs c (.prod a b) ++ (Ty.projs c a).map (.fst b) ++ (Ty.projs c b).map (.snd a)
  | .decl n ps r => Ty.selfProjs c (.decl n ps r) ++ (Ty.fieldProjs c r).map (.field n ps)
  | t => Ty.selfProjs c t

/-- Every path to a component of type `c` inside a field of the chain of fields `r`. -/
def Ty.fieldProjs (c : Ty) : (r : Ty) → List (Ty.FieldProj r c)
  | .prod a rest => (Ty.projs c a).map (.head rest) ++ (Ty.fieldProjs c rest).map (.tail a)
  | _ => []

end

theorem Ty.self_mem_selfProjs (t : Ty) : Ty.Proj.self t ∈ Ty.selfProjs t t := by
  simp [Ty.selfProjs, Ty.Proj.ofEq]

mutual

/-- `projs` lists every path. -/
theorem Ty.mem_projs {c : Ty} : {t : Ty} → (p : Ty.Proj t c) → p ∈ Ty.projs c t
  | _, .self t => by
      cases t <;> simp only [Ty.projs, List.mem_append] <;>
        first
        | exact Ty.self_mem_selfProjs _
        | exact .inl (.inl (Ty.self_mem_selfProjs _))
        | exact .inl (Ty.self_mem_selfProjs _)
  | _, .fst b p => by
      simp only [Ty.projs, List.mem_append, List.mem_map]
      exact .inl (.inr ⟨p, Ty.mem_projs p, rfl⟩)
  | _, .snd a p => by
      simp only [Ty.projs, List.mem_append, List.mem_map]
      exact .inr ⟨p, Ty.mem_projs p, rfl⟩
  | _, .field n ps q => by
      simp only [Ty.projs, List.mem_append, List.mem_map]
      exact .inr ⟨q, Ty.mem_fieldProjs q, rfl⟩

/-- `fieldProjs` lists every path into a field. -/
theorem Ty.mem_fieldProjs {c : Ty} : {r : Ty} → (q : Ty.FieldProj r c) → q ∈ Ty.fieldProjs c r
  | _, .head rest p => by
      simp only [Ty.fieldProjs, List.mem_append, List.mem_map]
      exact .inl ⟨p, Ty.mem_projs p, rfl⟩
  | _, .tail a q => by
      simp only [Ty.fieldProjs, List.mem_append, List.mem_map]
      exact .inr ⟨q, Ty.mem_fieldProjs q, rfl⟩

end

/-- A projection of functions of the arguments `as` to values of `c`: a component of type `c` of one
of the arguments. -/
inductive ArgProj (c : Ty) : List Ty → Type
  /-- A component of the first argument. -/
  | here {a : Ty} {as : List Ty} : Ty.Proj a c → ArgProj c (a :: as)
  /-- A projection of the arguments after the first. -/
  | there {a : Ty} {as : List Ty} : ArgProj c as → ArgProj c (a :: as)

namespace ArgProj

variable {c : Ty}

/-- The component a projection selects from a tuple of arguments. -/
def read : {as : List Ty} → ArgProj c as → Args as → c.denote
  | _ :: _, .here p, xs => p.get xs.1
  | _ :: _, .there q, xs => q.read xs.2

/-- A projection as a function of its arguments. -/
def fn : {as : List Ty} → ArgProj c as → Fn c as
  | _ :: as, .here p => fun x => Fn.const c (p.get x) as
  | _ :: _, .there q => fun _ => q.fn

/-- Every projection of functions of the arguments `as` to values of `c`. -/
def all (c : Ty) : (as : List Ty) → List (ArgProj c as)
  | [] => []
  | a :: as => (Ty.projs c a).map .here ++ (all c as).map .there

/-- `all` lists every projection. -/
theorem mem_all : {as : List Ty} → (p : ArgProj c as) → p ∈ all c as
  | _ :: _, .here p => List.mem_append.mpr (.inl (List.mem_map.mpr ⟨p, Ty.mem_projs p, rfl⟩))
  | _ :: _, .there q => List.mem_append.mpr (.inr (List.mem_map.mpr ⟨q, mem_all q, rfl⟩))

/-- A projection, as a function, returns the component it selects. -/
theorem apply_fn : {as : List Ty} → (p : ArgProj c as) → (xs : Args as) → p.fn.apply xs = p.read xs
  | _ :: as, .here p, xs => Fn.apply_const (p.get xs.1) as xs.2
  | _ :: _, .there q, xs => apply_fn q xs.2

end ArgProj

/-- A degenerate subject of the type `σ` denotes, by its description: the constant function at a
value of the output type, or a projection. -/
inductive Degenerate (σ : Sig) where
  /-- The function that returns `v` whatever its arguments. -/
  | const (v : σ.out.denote)
  /-- The function that returns the component `p` selects. -/
  | proj (p : ArgProj σ.out σ.args)

/-- The degenerate subject a description stands for. -/
def Degenerate.fn {σ : Sig} : Degenerate σ → σ.denote
  | .const v => Fn.const σ.out v σ.args
  | .proj p => p.fn

/-- Each degenerate subject returns the value its description says: a constant its value, and a
projection the component it selects. -/
theorem Degenerate.apply_fn {σ : Sig} (d : Degenerate σ) (xs : Args σ.args) :
    d.fn.apply xs = match d with
      | .const v => v
      | .proj p => p.read xs := by
  cases d with
  | const v => exact Fn.apply_const v σ.args xs
  | proj p => exact ArgProj.apply_fn p xs

/-- The degenerate subjects of the type `σ` denotes: the constant function at each value of the
output type's part, the empty output among them, then each projection. -/
def Sig.degenerate (σ : Sig) : List (Degenerate σ) :=
  σ.out.part.map .const ++ (ArgProj.all σ.out σ.args).map .proj

/-- A tuple of the empty values of the types `as`. -/
def Sig.Args.empty : (as : List Ty) → Args as
  | [] => ()
  | a :: as => (a.empty, Sig.Args.empty as)

namespace Sig

/-- The class, apart from the list that computes it: the constant function at each value the rule
`Ty.Small` admits, and every projection. -/
theorem mem_degenerate_iff {σ : Sig} (d : Degenerate σ) :
    d ∈ σ.degenerate ↔ (∃ v, d = .const v ∧ σ.out.Small v) ∨ ∃ p, d = .proj p := by
  simp only [degenerate, List.mem_append, List.mem_map]
  constructor
  · rintro (⟨v, hv, rfl⟩ | ⟨p, _, rfl⟩)
    · exact .inl ⟨v, rfl, (Ty.mem_part_iff _ v).mp hv⟩
    · exact .inr ⟨p, rfl⟩
  · rintro (⟨v, rfl, hv⟩ | ⟨p, rfl⟩)
    · exact .inl ⟨v, (Ty.mem_part_iff _ v).mpr hv, rfl⟩
    · exact .inr ⟨p, ArgProj.mem_all p, rfl⟩

/-- The empty output, the constant function at the output type's empty value, is in the class. -/
theorem empty_output_mem (σ : Sig) : Degenerate.const σ.out.empty ∈ σ.degenerate :=
  (mem_degenerate_iff _).mpr (.inl ⟨_, rfl, Ty.small_empty _⟩)

/-- No class is empty. -/
theorem degenerate_ne_nil (σ : Sig) : σ.degenerate ≠ [] := List.ne_nil_of_mem (empty_output_mem σ)

/-- Where the output type has finitely many values, the constant function at each is in the
class. -/
theorem const_mem_of_finite {σ : Sig} (h : σ.out.finite = true) (v : σ.out.denote) :
    Degenerate.const v ∈ σ.degenerate :=
  (mem_degenerate_iff _).mpr (.inl ⟨v, rfl, Ty.small_of_finite _ h v⟩)

/-- Every projection is in the class. -/
theorem proj_mem {σ : Sig} (p : ArgProj σ.out σ.args) : Degenerate.proj p ∈ σ.degenerate :=
  (mem_degenerate_iff _).mpr (.inr ⟨p, rfl⟩)

/-- The identity of a function of one argument to its own type is in the class. -/
theorem identity_mem (t : Ty) :
    ∃ d ∈ (⟨[t], t⟩ : Sig).degenerate, d.fn = fun x => x :=
  ⟨.proj (.here (.self t)), proj_mem _, rfl⟩

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
the isomorphisms of its parts, carried through the map of each type former. A type the project
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

/-- `σ` is the code of `W`, and `e` the isomorphism through which `σ` stands for `W`, as the library
fixes them: a plain value's through its type's code (`Ty.Stands`), and a function's through its
argument type's and its result type's, the function carried by mapping its argument back and its
result forth (`Iso.arrow`). -/
inductive Sig.Stands : (W : Type) → (σ : Sig) → Iso W σ.denote → Prop
  | value {α : Type} {t : Ty} {e : Iso α t.denote} : Ty.Stands α t e → Sig.Stands α ⟨[], t⟩ e
  | arrow {α β : Type} {t : Ty} {σ : Sig} {e : Iso α t.denote} {f : Iso β σ.denote} :
      Ty.Stands α t e → Sig.Stands β σ f → Sig.Stands (α → β) ⟨t :: σ.args, σ.out⟩ (e.arrow f)

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

/-- A plain value of a coded type. -/
instance (priority := low) {α : Type} [h : HasCode α] : Covered α :=
  ⟨⟨[], h.code⟩, h.iso, .value h.stands⟩

/-- A function of a coded argument type to a covered type. -/
instance {α β : Type} [h : HasCode α] [c : Covered β] : Covered (α → β) :=
  ⟨⟨h.code :: c.sig.args, c.sig.out⟩, h.iso.arrow c.iso, .arrow h.stands c.stands⟩

/-- The degenerate subjects of the type `W`, by their descriptions: the class of `W`'s code. It
takes no record, so it is the same for every record about `W`. -/
def degenerate (W : Type) [c : Covered W] : List (Degenerate c.sig) := c.sig.degenerate

/-- The subject of type `W` a description stands for: the member, carried back to `W` through the
isomorphism by which `W`'s code stands for `W`. -/
def Degenerate.subject {W : Type} [c : Covered W] (d : Degenerate c.sig) : W := c.iso.inv d.fn

/-- The subject is the member itself, carried to `W` through the isomorphism that `Sig.Stands` fixes:
for a type built only from those `Ty` builds in, the identity, so that no code can mis-encode such a
type; and for a type the project declares, the isomorphism its deriving handler writes from the
declaration (`LeanIntent.Declared`, which states what that rests on). -/
theorem Degenerate.iso_subject {W : Type} [c : Covered W] (d : Degenerate c.sig) :
    c.iso.to d.subject = d.fn :=
  c.iso.to_inv d.fn

/-- No covered type's class is empty, so no record is checked against nothing. -/
theorem degenerate_ne_nil (W : Type) [Covered W] : degenerate W ≠ [] := Sig.degenerate_ne_nil _

/-! ## Verdicts -/

section Verdicts

variable {W : Type} [c : Covered W]

/-- The goal that `b` is the verdict on the subject `w` for `r`: that `w` meets `r` when `b` is
`true`, and that it does not when `b` is `false`. -/
def verdictGoal (r : IntentRecord W) (w : W) : Bool → Prop
  | true => r.Meets w
  | false => ¬ r.Meets w

/-- The goals that `bs` are, in order, the verdicts on the subjects that the descriptions `ds` stand
for, and the goal `False` when the two lists differ in length. -/
def verdictGoals (r : IntentRecord W) : List (Degenerate c.sig) → List Bool → List Prop
  | [], [] => []
  | d :: ds, b :: bs => verdictGoal r d.subject b :: verdictGoals r ds bs
  | _, _ => [False]

/-- The degenerate check's goals: that `bs` are, in order, the verdicts on the degenerate subjects
of `W` for `r`. -/
def verdicts (r : IntentRecord W) (bs : List Bool) : List Prop := verdictGoals r (degenerate W) bs

/-- `bs` are the verdicts, in order, on the degenerate subjects of `W` for `r`. -/
def Verdicts (r : IntentRecord W) (bs : List Bool) : Prop := Goals (verdicts r bs)

/-- What the degenerate check asks, written apart from its former: one verdict for each degenerate
subject, `true` exactly when the subject at the same position meets the record. -/
def intendedVerdicts (r : IntentRecord W) (bs : List Bool) : Prop :=
  bs.length = (degenerate W).length ∧
    ∀ (i : Nat) (hb : i < bs.length) (hd : i < (degenerate W).length),
      (bs[i] = true ↔ (∀ x ∈ r.dom, x.holds (degenerate W)[i].subject) ∧
        ∀ p ∈ r.props, p.holds (degenerate W)[i].subject)

theorem goals_verdictGoals (r : IntentRecord W) : (ds : List (Degenerate c.sig)) →
    (bs : List Bool) → (Goals (verdictGoals r ds bs) ↔ bs.length = ds.length ∧
      ∀ (i : Nat) (hb : i < bs.length) (hd : i < ds.length), (bs[i] = true ↔ r.Meets ds[i].subject))
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
  simp only [intendedVerdicts, IntentRecord.Meets, IntentRecord.Dom, IntentRecord.Props]

/-- The descriptions among `ds` whose verdict in `bs` is `true`. -/
def metByGo : List (Degenerate c.sig) → List Bool → List (Degenerate c.sig)
  | d :: ds, true :: bs => d :: metByGo ds bs
  | _ :: ds, false :: bs => metByGo ds bs
  | _, _ => []

/-- The degenerate subjects of `W` whose verdict in `bs` is that they meet the record. -/
def metBy (W : Type) [c : Covered W] (bs : List Bool) : List (Degenerate c.sig) :=
  metByGo (degenerate W) bs

theorem mem_metByGo (r : IntentRecord W) (d : Degenerate c.sig) : (ds : List (Degenerate c.sig)) →
    (bs : List Bool) → Goals (verdictGoals r ds bs) →
      (d ∈ metByGo ds bs ↔ d ∈ ds ∧ r.Meets d.subject)
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

/-- The degenerate subjects the verdicts report are exactly those that meet the record. -/
theorem mem_metBy {r : IntentRecord W} {bs : List Bool} (h : Verdicts r bs)
    (d : Degenerate c.sig) : d ∈ metBy W bs ↔ d ∈ degenerate W ∧ r.Meets d.subject :=
  mem_metByGo r d _ bs h

/-- The verdicts report no degenerate subject exactly when none meets the record. -/
theorem metBy_eq_nil_iff {r : IntentRecord W} {bs : List Bool} (h : Verdicts r bs) :
    metBy W bs = [] ↔ ∀ d ∈ degenerate W, ¬ r.Meets d.subject := by
  rw [List.eq_nil_iff_forall_not_mem]
  exact forall_congr' fun d => by rw [mem_metBy h]; exact not_and

/-- The name the owner reads a degenerate subject's consequence by: what kind of member it is. -/
def Degenerate.name {σ : Sig} : Degenerate σ → String
  | .const _ => "the record allows a subject that returns one value whatever its arguments"
  | .proj _ => "the record allows a subject that returns one of its arguments, or a part of one"

/-- The consequence shown to the owner for a degenerate subject: the possibility that the subject is
that degenerate subject. -/
def Degenerate.consequence (d : Degenerate c.sig) : Consequence W :=
  ⟨d.name, .possibility, fun w => w = d.subject⟩

/-- The owner's declining a degenerate subject's consequence is kept by exactly the revisions that
subject does not meet. -/
theorem Degenerate.declined_keptBy_iff (d : Degenerate c.sig) (r : IntentRecord W) :
    (Answer.mk d.consequence .declined).KeptBy r ↔ ¬ r.Meets d.subject := by
  simp only [Answer.KeptBy, Degenerate.consequence]
  exact ⟨fun h hm => h _ hm rfl, fun h w hm e => h (e ▸ hm)⟩

/-- The consequences reported to the owner: one for each degenerate subject the proved verdicts
`bs` say meets the record, in order. It takes the proof of the verdicts, so no report exists for
verdicts that are not proved. -/
def possibilities {r : IntentRecord W} {bs : List Bool} (_ : Verdicts r bs) : List (Consequence W) :=
  (metBy W bs).map Degenerate.consequence

/-- Under proved verdicts, the reported consequences are exactly those of the degenerate subjects
that meet the record. -/
theorem mem_possibilities {r : IntentRecord W} {bs : List Bool} (h : Verdicts r bs)
    (x : Consequence W) :
    x ∈ possibilities h ↔ ∃ d ∈ degenerate W, r.Meets d.subject ∧ x = d.consequence := by
  simp only [possibilities, List.mem_map, mem_metBy h]
  exact ⟨fun ⟨d, ⟨hd, hm⟩, e⟩ => ⟨d, hd, hm, e.symm⟩, fun ⟨d, hd, hm, e⟩ => ⟨d, ⟨hd, hm⟩, e.symm⟩⟩

/-- Each reported consequence is a possibility that holds of the record as it is shown: a model of
the record satisfies it, the degenerate subject itself. -/
theorem possibilities_holdsOf {r : IntentRecord W} {bs : List Bool} (h : Verdicts r bs)
    (x : Consequence W) (hx : x ∈ possibilities h) : x.kind = .possibility ∧ x.HoldsOf r := by
  obtain ⟨d, _, hm, rfl⟩ := (mem_possibilities h x).mp hx
  exact ⟨rfl, d.subject, hm, rfl⟩

end Verdicts

end LeanIntent
