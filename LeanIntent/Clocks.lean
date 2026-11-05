import LeanIntent.Declared

/-!
# The clocks inside a subject's arguments

A script of timed actions is a subject that reads its clock and not what it sees: a function of the
time alone. The trivial-witness check (`LeanIntent.TrivialWitnesses`) holds, for each clock its
class takes, the member that offers at each input a subject that reads only that clock. Lean's
logic cannot ask which part of an argument a project means as its clock, so this module fixes,
from a subject's code alone, the parts that can be one, and the one way a project declares a part
its clock where the code alone cannot tell.

## Clock parts

A *clock part* of a function's arguments (`ArgClock`) is a component of one argument, reached along
a path of the degenerate class that applies no function (`ArgPath` over `NoSource`): the argument
itself, a component of one side of a pair, or a component of a field of a declared type with one
constructor, such as a structure, each of any covered type; with a reading of that component
(`ClockRead`): its value, of its own type, or, for a list or an array, its length or size, a number.
`ArgClock.read` reads it from a tuple of arguments. A part that does not exist, such as the element
of a list, a side of a sum, a field of a type with several constructors, a field of a recursive,
nested or mutual type (whose representation is a `Ty.mu` or a `Ty.muAt`, not a chain of fields) or
what a function returns, has no such path, so Lean refuses to elaborate it and no declaration can
name it.
`ArgClock.all` lists every clock part (`ArgClock.mem_all`), from every component of each argument
(`Ty.components`, `Ty.mem_components`) and every reading of each (`ClockRead.all`,
`ClockRead.mem_all`).

## Which parts are clocks

* **By the subject's type alone**, each clock part whose reading does not determine the arguments:
  two tuples of arguments read the same there and differ (`ArgClock.determines_eq_false_iff`). A
  subject that reads only such a part does not read the rest of its arguments, a real restriction,
  as not reading one argument is. Where the part is in fact what the subject sees and the rest its
  clock, such a subject is one that ignores its clock, which the class holds for whole arguments
  already; a report of it is a true statement about the pair either way.
* **By the project's declaration**, each clock part that is a value of type `LeanIntent.Clock α`
  (`ArgClock.InClock`): a structure of one field, the tick, of any covered type `α`, which a project
  gives to the part of its subject's arguments it means as its clock. A part whose reading
  determines the arguments, such as the only argument of a policy of type `Nat → Act`, is all the
  subject has to read: every subject reads only it, so reading it as a clock makes every subject a
  script, and reading it as what the subject sees makes none. The type alone cannot tell the two
  apart, so it reads such a part as what the subject sees, and only the declaration, a policy of
  type `Clock Nat → Act`, reads it as a clock. The declaration is a part of the subject's type, so it
  is read wherever a pair about that type is stated, and is the same for every such pair. That it is
  a type, and not an instance or an attribute, is a choice of the agent that implemented it: an
  instance can sit in a module the verdicts do not import, or be passed for one pair.
* A value of type `LeanIntent.Clock α` in an argument where no clock part reaches, such as inside a
  list, an option, a sum, a declared type with several constructors, a recursive type or a
  function, is a declaration the class cannot read: `Ty.strayClock` finds it, and the trivial-witness
  check refuses every verdict about such a type rather than ignore the declaration. It looks only in
  the fields of values, never in a declared type's parameters, which hold no value except through
  the fields that use them.
-/

namespace LeanIntent

/-- A clock: the tick it reads, a value of `α`. A project gives this type to the part of its
subject's arguments that it means as the subject's clock, so that the trivial-witness check reads
that part as a clock even where it is all the subject has to read (`LeanIntent.ArgClock.InClock`).
-/
structure Clock (α : Type) where
  /-- The tick the clock reads. -/
  tick : α
  deriving DecidableEq, Repr, LeanIntent.HasCode

/-- The name `LeanIntent.Clock`'s code carries. -/
def Clock.codeName : Lean.Name := ``Clock

/-- `Clock α`'s code: its name, the chain of its one parameter, and the chain of its one field, both
`α`'s code. -/
theorem Clock.code_eq (α : Type) [HasCode α] :
    HasCode.code (Clock α) =
      .decl Clock.codeName (.prod (HasCode.code α) .unit) (.prod (HasCode.code α) .unit) :=
  rfl

/-! ## Clock parts -/

mutual

/-- Every component of a value of type `t` reached without applying a function, with its type: the
value itself, then the components of each side of a pair, or of each field of a declared type with
one constructor that is not recursive, nested or mutual, whose representation is a chain of fields. -/
def Ty.components : (t : Ty) → List (Σ c, Ty.Proj NoSource t c)
  | .prod a b =>
    ⟨_, .self (.prod a b)⟩ :: ((Ty.components a).map fun p => ⟨p.1, .fst b p.2⟩) ++
      (Ty.components b).map fun p => ⟨p.1, .snd a p.2⟩
  | .decl n ps r =>
    ⟨_, .self (.decl n ps r)⟩ :: (Ty.fieldComponents r).map fun p => ⟨p.1, .field n ps p.2⟩
  | t => [⟨t, .self t⟩]

/-- Every component inside a field of the chain of fields `r`, with its type. -/
def Ty.fieldComponents : (r : Ty) → List (Σ c, Ty.FieldProj NoSource r c)
  | .prod a rest =>
    ((Ty.components a).map fun p => ⟨p.1, .head rest p.2⟩) ++
      (Ty.fieldComponents rest).map fun p => ⟨p.1, .tail a p.2⟩
  | _ => []

end

mutual

/-- `components` lists every path that applies no function. -/
theorem Ty.mem_components : {t c : Ty} → (p : Ty.Proj NoSource t c) →
    (⟨c, p⟩ : Σ c, Ty.Proj NoSource t c) ∈ Ty.components t
  | _, _, .self t => by cases t <;> simp [Ty.components]
  | _, _, .fst b p => by
      simp only [Ty.components, List.cons_append, List.mem_cons, List.mem_append, List.mem_map]
      exact .inr (.inl ⟨_, Ty.mem_components p, rfl⟩)
  | _, _, .snd a p => by
      simp only [Ty.components, List.cons_append, List.mem_cons, List.mem_append, List.mem_map]
      exact .inr (.inr ⟨_, Ty.mem_components p, rfl⟩)
  | _, _, .field n ps q => by
      simp only [Ty.components, List.mem_cons, List.mem_map]
      exact .inr ⟨_, Ty.mem_fieldComponents q, rfl⟩
  | _, _, .app s _ => nomatch s

/-- `fieldComponents` lists every path into a field that applies no function. -/
theorem Ty.mem_fieldComponents : {r c : Ty} → (q : Ty.FieldProj NoSource r c) →
    (⟨c, q⟩ : Σ c, Ty.FieldProj NoSource r c) ∈ Ty.fieldComponents r
  | _, _, .head rest p => by
      simp only [Ty.fieldComponents, List.mem_append, List.mem_map]
      exact .inl ⟨_, Ty.mem_components p, rfl⟩
  | _, _, .tail a q => by
      simp only [Ty.fieldComponents, List.mem_append, List.mem_map]
      exact .inr ⟨_, Ty.mem_fieldComponents q, rfl⟩

end

/-- Every component of the arguments `as` reached without applying a function, with its type. -/
def ArgPath.components : (as : List Ty) → List (Σ c, ArgPath NoSource c as)
  | [] => []
  | a :: as =>
    ((Ty.components a).map fun p => ⟨p.1, .here p.2⟩) ++
      (ArgPath.components as).map fun p => ⟨p.1, .there p.2⟩

/-- `ArgPath.components` lists every path into the arguments that applies no function. -/
theorem ArgPath.mem_components {c : Ty} : {as : List Ty} → (p : ArgPath NoSource c as) →
    (⟨c, p⟩ : Σ c, ArgPath NoSource c as) ∈ ArgPath.components as
  | _ :: _, .here p =>
    List.mem_append.mpr (.inl (List.mem_map.mpr ⟨_, Ty.mem_components p, rfl⟩))
  | _ :: _, .there q =>
    List.mem_append.mpr (.inr (List.mem_map.mpr ⟨_, ArgPath.mem_components q, rfl⟩))

/-- How a clock reads a component of type `c`: its value, or the length of a list or the size of an
array. -/
inductive ClockRead : Ty → Type
  /-- The component's value, of its own type. -/
  | value (c : Ty) : ClockRead c
  /-- The length of a list. -/
  | length (a : Ty) : ClockRead (.list a)
  /-- The size of an array. -/
  | size (a : Ty) : ClockRead (.array a)

namespace ClockRead

/-- The code of what a reading reads: the component's own for its value, a number for a length or a
size. -/
abbrev out : {c : Ty} → ClockRead c → Ty
  | _, .value c => c
  | _, .length _ => .nat
  | _, .size _ => .nat

/-- What a reading reads from a component. -/
def read : {c : Ty} → (r : ClockRead c) → c.denote → r.out.denote
  | _, .value _, x => x
  | _, .length _, x => x.length
  | _, .size _, x => x.size

/-- Every reading of a component of type `c`. -/
def all : (c : Ty) → List (ClockRead c)
  | .list a => [.value _, .length a]
  | .array a => [.value _, .size a]
  | c => [.value c]

/-- `all` lists every reading. -/
theorem mem_all : {c : Ty} → (r : ClockRead c) → r ∈ all c
  | _, .value c => by cases c <;> simp [all]
  | _, .length _ => by simp [all]
  | _, .size _ => by simp [all]

end ClockRead

/-- A clock part of the arguments `as`: a component of one of them, reached without applying a
function, and a reading of it. -/
structure ArgClock (as : List Ty) where
  /-- The code of the component. -/
  comp : Ty
  /-- The path to the component. -/
  path : ArgPath NoSource comp as
  /-- How the clock reads the component. -/
  reading : ClockRead comp

namespace ArgClock

/-- The code of what a clock part reads. -/
abbrev out {as : List Ty} (k : ArgClock as) : Ty := k.reading.out

/-- What a clock part of the arguments reads from a tuple of them. -/
def read {as : List Ty} (k : ArgClock as) (xs : Sig.Args as) : k.out.denote :=
  k.reading.read (k.path.read (fun _ s => nomatch s) xs)

/-- Every clock part of the arguments `as`: each component of each argument, in order, with each of
its readings. -/
def all (as : List Ty) : List (ArgClock as) :=
  (ArgPath.components as).flatMap fun p => (ClockRead.all p.1).map fun r => ⟨p.1, p.2, r⟩

/-- `all` lists every clock part of the arguments. -/
theorem mem_all {as : List Ty} (k : ArgClock as) : k ∈ all as :=
  List.mem_flatMap.mpr ⟨⟨k.comp, k.path⟩, ArgPath.mem_components k.path,
    List.mem_map.mpr ⟨k.reading, ClockRead.mem_all k.reading, rfl⟩⟩

end ArgClock

/-! ## Parts whose reading determines the arguments -/

/-- A type has one value exactly when its code says so (`Ty.unique`). -/
theorem Ty.unique_iff (t : Ty) : t.unique = true ↔ ∀ x y : t.denote, x = y := by
  constructor
  · intro h x y
    rw [Ty.eq_empty_of_unique t h x, Ty.eq_empty_of_unique t h y]
  · intro h
    cases hu : t.unique
    · obtain ⟨x, y, hne⟩ := Ty.exists_ne t hu
      exact absurd (h x y) hne
    · rfl

/-- Reading the left side of pairs determines the pair exactly when it determines that side and the
right side has one value. -/
private theorem injective_fst_iff {α β γ : Type} (f : α → γ) (a₀ : α) (b₀ : β) :
    Function.Injective (fun p : α × β => f p.1) ↔ Function.Injective f ∧ ∀ x y : β, x = y := by
  constructor
  · intro h
    exact ⟨fun x y e => congrArg Prod.fst (@h (x, b₀) (y, b₀) e),
      fun x y => congrArg Prod.snd (@h (a₀, x) (a₀, y) rfl)⟩
  · rintro ⟨hf, hb⟩ ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ e
    exact Prod.ext (hf e) (hb y₁ y₂)

/-- Reading the right side of pairs determines the pair exactly when it determines that side and the
left side has one value. -/
private theorem injective_snd_iff {α β γ : Type} (f : β → γ) (a₀ : α) (b₀ : β) :
    Function.Injective (fun p : α × β => f p.2) ↔ Function.Injective f ∧ ∀ x y : α, x = y := by
  constructor
  · intro h
    exact ⟨fun x y e => congrArg Prod.snd (@h (a₀, x) (a₀, y) e),
      fun x y => congrArg Prod.fst (@h (x, b₀) (y, b₀) rfl)⟩
  · rintro ⟨hf, hb⟩ ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ e
    exact Prod.ext (hb x₁ x₂) (hf e)

/-- The length of a list determines it exactly when its elements have one value. -/
private theorem length_injective_iff {α : Type} :
    Function.Injective (List.length : List α → Nat) ↔ ∀ x y : α, x = y := by
  constructor
  · intro h x y
    exact List.cons.inj (@h [x] [y] rfl) |>.1
  · intro h l₁
    induction l₁ with
    | nil => intro l₂ e; cases l₂ with
      | nil => rfl
      | cons _ _ => exact absurd e (by simp)
    | cons x l ih => intro l₂ e; cases l₂ with
      | nil => exact absurd e (by simp)
      | cons y l' => rw [h x y, ih (by simpa using e)]

/-- The size of an array determines it exactly when its elements have one value. -/
private theorem size_injective_iff {α : Type} :
    Function.Injective (Array.size : Array α → Nat) ↔ ∀ x y : α, x = y := by
  constructor
  · intro h x y
    have e := congrArg Array.toList (@h #[x] #[y] rfl)
    exact List.cons.inj e |>.1
  · intro h a₁ a₂ e
    apply Array.toList_inj.mp
    apply length_injective_iff.mpr h
    simpa using e

namespace ClockRead

/-- Whether a reading determines the component: its value always, a list's length and an array's
size when the elements have one value. -/
def determines : {c : Ty} → ClockRead c → Bool
  | _, .value _ => true
  | _, .length a => a.unique
  | _, .size a => a.unique

/-- A reading determines the component exactly when `determines` says so. -/
theorem determines_iff : {c : Ty} → (r : ClockRead c) →
    (r.determines = true ↔ Function.Injective r.read)
  | _, .value _ => ⟨fun _ _ _ h => h, fun _ => rfl⟩
  | _, .length a => (Ty.unique_iff a).trans length_injective_iff.symm
  | _, .size a => (Ty.unique_iff a).trans size_injective_iff.symm

end ClockRead

/-- The tuples of the arguments `as` have one value exactly when each argument's type has one. -/
theorem Sig.args_unique_iff : (as : List Ty) →
    (as.all Ty.unique = true ↔ ∀ xs ys : Sig.Args as, xs = ys)
  | [] => ⟨fun _ _ _ => rfl, fun _ => rfl⟩
  | a :: as => by
      rw [List.all_cons, Bool.and_eq_true, Ty.unique_iff, Sig.args_unique_iff as]
      constructor
      · rintro ⟨ha, hs⟩ ⟨x, xs⟩ ⟨y, ys⟩
        rw [ha x y, hs xs ys]
      · intro h
        exact ⟨fun x y => congrArg Prod.fst (h (x, Sig.Args.empty as) (y, Sig.Args.empty as)),
          fun xs ys => congrArg Prod.snd (h (a.empty, xs) (a.empty, ys))⟩

/-- Reordering the three conditions a step along a path joins. -/
private theorem and_step_iff {p q r : Prop} : (p ∧ q) ∧ r ↔ (r ∧ p) ∧ q :=
  ⟨fun ⟨⟨hp, hq⟩, hr⟩ => ⟨⟨hr, hp⟩, hq⟩, fun ⟨⟨hr, hp⟩, hq⟩ => ⟨⟨hp, hq⟩, hr⟩⟩

mutual

/-- Whether the component a path selects determines the value: at each side of a pair, or each
field, the rest has one value. -/
def Ty.Proj.determines : {t c : Ty} → Ty.Proj NoSource t c → Bool
  | _, _, .self _ => true
  | _, _, .fst b p => b.unique && p.determines
  | _, _, .snd a p => a.unique && p.determines
  | _, _, .field _ _ q => q.determines
  | _, _, .app s _ => nomatch s

/-- Whether the component a path into a field selects determines the chain of fields. -/
def Ty.FieldProj.determines : {r c : Ty} → Ty.FieldProj NoSource r c → Bool
  | _, _, .head rest p => rest.unique && p.determines
  | _, _, .tail a q => a.unique && q.determines

end

mutual

/-- Reading `g` of the component a path selects determines the value exactly when the path's
`determines` says so and `g` determines the component. -/
theorem Ty.Proj.injective_iff {γ : Type} (ev : (a : Ty) → NoSource a → a.denote) :
    {t c : Ty} → (p : Ty.Proj NoSource t c) → (g : c.denote → γ) →
    (Function.Injective (fun x => g (p.get ev x)) ↔ p.determines = true ∧ Function.Injective g)
  | _, _, .self _, _ => ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩
  | _, _, @Ty.Proj.fst _ a _ b p, g => by
      rw [Ty.Proj.determines, Bool.and_eq_true, Ty.unique_iff]
      exact (injective_fst_iff (fun y => g (p.get ev y)) a.empty b.empty).trans
        ((and_congr (Ty.Proj.injective_iff ev p g) Iff.rfl).trans and_step_iff)
  | _, _, @Ty.Proj.snd _ b _ a p, g => by
      rw [Ty.Proj.determines, Bool.and_eq_true, Ty.unique_iff]
      exact (injective_snd_iff (fun y => g (p.get ev y)) a.empty b.empty).trans
        ((and_congr (Ty.Proj.injective_iff ev p g) Iff.rfl).trans and_step_iff)
  | _, _, .field _ _ q, g => Ty.FieldProj.injective_iff ev q g
  | _, _, .app s _, _ => nomatch s

/-- Reading `g` of the component a path into a field selects determines the chain of fields exactly
when the path's `determines` says so and `g` determines the component. -/
theorem Ty.FieldProj.injective_iff {γ : Type} (ev : (a : Ty) → NoSource a → a.denote) :
    {r c : Ty} → (q : Ty.FieldProj NoSource r c) → (g : c.denote → γ) →
    (Function.Injective (fun x => g (q.get ev x)) ↔ q.determines = true ∧ Function.Injective g)
  | _, _, @Ty.FieldProj.head _ a _ rest p, g => by
      rw [Ty.FieldProj.determines, Bool.and_eq_true, Ty.unique_iff]
      exact (injective_fst_iff (fun y => g (p.get ev y)) a.empty rest.empty).trans
        ((and_congr (Ty.Proj.injective_iff ev p g) Iff.rfl).trans and_step_iff)
  | _, _, @Ty.FieldProj.tail _ rest _ a q, g => by
      rw [Ty.FieldProj.determines, Bool.and_eq_true, Ty.unique_iff]
      exact (injective_snd_iff (fun y => g (q.get ev y)) a.empty rest.empty).trans
        ((and_congr (Ty.FieldProj.injective_iff ev q g) Iff.rfl).trans and_step_iff)

end

/-- Whether the component a path into the arguments selects determines the tuple of them: it
determines its argument, and every other argument's type has one value. -/
def ArgPath.determines {c : Ty} : {as : List Ty} → ArgPath NoSource c as → Bool
  | _ :: as, .here p => p.determines && as.all Ty.unique
  | a :: _, .there q => a.unique && q.determines

/-- Reading `g` of the component a path into the arguments selects determines the tuple of them
exactly when the path's `determines` says so and `g` determines the component. -/
theorem ArgPath.injective_iff {γ : Type} (ev : (a : Ty) → NoSource a → a.denote) {c : Ty} :
    {as : List Ty} → (p : ArgPath NoSource c as) → (g : c.denote → γ) →
    (Function.Injective (fun xs => g (p.read ev xs)) ↔ p.determines = true ∧ Function.Injective g)
  | a :: as, .here p, g => by
      rw [ArgPath.determines, Bool.and_eq_true, Sig.args_unique_iff as]
      exact (injective_fst_iff (fun y => g (p.get ev y)) a.empty (Sig.Args.empty as)).trans
        ((and_congr (Ty.Proj.injective_iff ev p g) Iff.rfl).trans
          ⟨fun ⟨⟨hp, hg⟩, hs⟩ => ⟨⟨hp, hs⟩, hg⟩, fun ⟨⟨hp, hs⟩, hg⟩ => ⟨⟨hp, hg⟩, hs⟩⟩)
  | a :: as, .there q, g => by
      rw [ArgPath.determines, Bool.and_eq_true, Ty.unique_iff]
      exact (injective_snd_iff (fun y => g (q.read ev y)) a.empty (Sig.Args.empty as)).trans
        ((and_congr (ArgPath.injective_iff ev q g) Iff.rfl).trans and_step_iff)

namespace ArgClock

/-- Whether a clock part's reading determines the tuple of arguments: its path selects a component
that determines them, and its reading determines that component. -/
def determines {as : List Ty} (k : ArgClock as) : Bool := k.path.determines && k.reading.determines

/-- A clock part's reading determines the arguments exactly when `determines` says so. -/
theorem determines_iff {as : List Ty} (k : ArgClock as) :
    k.determines = true ↔ Function.Injective k.read := by
  rw [determines, Bool.and_eq_true, ClockRead.determines_iff]
  exact (ArgPath.injective_iff _ k.path k.reading.read).symm

/-- A clock part's reading does not determine the arguments exactly when two tuples of them read
the same there and differ. -/
theorem determines_eq_false_iff {as : List Ty} (k : ArgClock as) :
    k.determines = false ↔ ∃ xs ys, xs ≠ ys ∧ k.read xs = k.read ys := by
  rw [← Bool.not_eq_true, determines_iff]
  constructor
  · intro h
    refine Classical.byContradiction fun hn => h fun xs ys e => ?_
    exact Classical.byContradiction fun hne => hn ⟨xs, ys, hne, e⟩
  · rintro ⟨xs, ys, hne, e⟩ h
    exact hne (h e)

end ArgClock

/-! ## The declaration -/

/-- Whether the code is that of a `LeanIntent.Clock α`: a declared type of the name its code
carries. -/
def Ty.isClock : Ty → Bool
  | .decl n _ _ => decide (n = Clock.codeName)
  | _ => false

/-- The code is that of a `LeanIntent.Clock α` exactly when `isClock` says so. -/
theorem Ty.isClock_iff (t : Ty) : t.isClock = true ↔ ∃ ps r, t = .decl Clock.codeName ps r := by
  cases t <;> simp [Ty.isClock]

namespace ArgClock

/-- The project declared the clock part `k` its subject's clock: `k` reads a component of type
`LeanIntent.Clock α` for some `α`, whose code is the declared type of the name `Clock.codeName`. -/
def InClock {as : List Ty} (k : ArgClock as) : Prop :=
  ∃ ps r, k.comp = .decl Clock.codeName ps r

instance {as : List Ty} (k : ArgClock as) : Decidable k.InClock :=
  decidable_of_iff _ (Ty.isClock_iff k.comp)

end ArgClock

/-- Whether a value of the code holds a `LeanIntent.Clock` anywhere: in a field of a declared type, or
the declared type itself. A declared type's parameters are not read: a parameter is part of a value
only through the fields that use it, which its representation holds. Its match has no catch-all
case, so a code former added to `Ty` must say whether it holds one. -/
def Ty.namesClock : Ty → Bool
  | .unit => false
  | .bool => false
  | .nat => false
  | .int => false
  | .string => false
  | .fin _ => false
  | .atom _ => false
  | .list a => a.namesClock
  | .array a => a.namesClock
  | .option a => a.namesClock
  | .prod a b => a.namesClock || b.namesClock
  | .sum a b => a.namesClock || b.namesClock
  | .arrow a b => a.namesClock || b.namesClock
  | .decl n _ r => decide (n = Clock.codeName) || r.namesClock
  | .ref _ => false
  | .mu b g r _ => b.namesClock || g.namesClock || r.namesClock
  | .muAt b g r _ _ => b.namesClock || g.namesClock || r.namesClock

mutual

/-- Whether a value of the code holds a `LeanIntent.Clock` where no clock part reaches it: inside a
list, an array, an option, a sum, a function, a declared type with several constructors, or a
recursive, nested or mutual type (a `Ty.mu` or a `Ty.muAt`). The clock parts reach through pairs
and the fields of every other declared type with one constructor, `LeanIntent.Clock` included, and
a `LeanIntent.Clock` they reach is a declaration the class reads. A parameter of a declared type is
not a part of its values except through the fields that hold it, which are read instead. -/
def Ty.strayClock : Ty → Bool
  | .prod a b => Ty.strayClock a || Ty.strayClock b
  | .decl _ _ r => Ty.fieldStrayClock r
  | t => t.namesClock

/-- Whether a chain of fields holds a `LeanIntent.Clock` where no clock part reaches it. A
representation that is not a chain, that of a type with several constructors or of a recursive,
nested or mutual type (a `Ty.mu` or a `Ty.muAt`), holds one wherever it names one. -/
def Ty.fieldStrayClock : Ty → Bool
  | .prod a rest => Ty.strayClock a || Ty.fieldStrayClock rest
  | r => r.namesClock

end

/-- Whether an argument of the type `σ` denotes holds a `LeanIntent.Clock` where no clock part
reaches it: a declaration of a clock that the trivial-witness check cannot read, so it refuses every
verdict about the type. -/
def Sig.strayClock (σ : Sig) : Bool := σ.args.any Ty.strayClock

/-! ## Scripts of timed actions -/

namespace Sig

/-- The function `f` of the arguments `as` reads only the clock part `k`: two tuples of arguments
that read the same there give the same value. -/
def Fn.ReadsOnly {b : Ty} {as : List Ty} (f : Fn b as) (k : ArgClock as) : Prop :=
  ∀ xs ys, k.read xs = k.read ys → f.apply xs = f.apply ys

/-- A function of the arguments is the function that returns what it returns on the tuple of them.
-/
theorem Fn.curry_apply {b : Ty} : (as : List Ty) → (f : Fn b as) → Fn.curry b as f.apply = f
  | [], _ => rfl
  | _ :: as, f => funext fun x => Fn.curry_apply as (f x)

/-- A constant function reads only any clock part. -/
theorem Fn.const_readsOnly {b : Ty} (v : b.denote) {as : List Ty} (k : ArgClock as) :
    (Fn.const b v as).ReadsOnly k := fun xs ys _ => by
  rw [Fn.apply_const, Fn.apply_const]

end Sig

namespace ArgClock

open Sig

/-- The script of timed actions that takes the action `s n` whenever the clock part `k` reads `n`,
as a function of the arguments. -/
def script {b : Ty} {as : List Ty} (k : ArgClock as) (s : k.out.denote → b.denote) : Fn b as :=
  Fn.curry b as fun xs => s (k.read xs)

/-- A script returns its action at the clock's reading. -/
theorem apply_script {b : Ty} {as : List Ty} (k : ArgClock as) (s : k.out.denote → b.denote)
    (xs : Args as) : (k.script s).apply xs = s (k.read xs) :=
  Fn.apply_curry as _ xs

/-- A function reads only the clock part `k` exactly when it is a script of timed actions on `k`: it
takes, whenever `k` reads `n`, one action fixed for `n`. -/
theorem readsOnly_iff_script {b : Ty} {as : List Ty} (k : ArgClock as) (f : Fn b as) :
    f.ReadsOnly k ↔ ∃ s : k.out.denote → b.denote, f = k.script s := by
  constructor
  · intro h
    let _ : Nonempty (Args as) := ⟨Args.empty as⟩
    refine ⟨fun n => f.apply (Classical.epsilon fun ys => k.read ys = n), ?_⟩
    rw [← Fn.curry_apply as f]
    unfold script
    congr 1
    funext xs
    rw [Fn.curry_apply as f]
    exact h _ _ (Classical.epsilon_spec (p := fun ys => k.read ys = k.read xs) ⟨xs, rfl⟩).symm
  · rintro ⟨s, rfl⟩ xs ys e
    rw [apply_script, apply_script, e]

end ArgClock

end LeanIntent
