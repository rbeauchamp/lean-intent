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

A *clock part* of a value of the type a code denotes (`Ty.ClockPart`) is a number (`Nat`), a
`Fin (n + 1)`, the length of a list or the size of an array, reached through the sides of pairs and
the fields of declared types with one constructor, such as structures (`Ty.FieldClockPart`), the
paths along which the degenerate class projects without applying a function; `ArgClock` is a clock
part of one of a function's arguments. Each is read as a number (`Ty.ClockPart.read`,
`ArgClock.read`). A part that does not exist, or is not of one of those kinds, such as a `Bool`, the
element of a list, a side of a sum or a field of a type with several constructors, has no value of
these types: Lean refuses to elaborate it, so no declaration can name it. `Ty.clockParts` and
`ArgClock.all` list every clock part (`Ty.mem_clockParts`, `ArgClock.mem_all`).

## Which parts are clocks

* **By the subject's type alone**, each clock part whose reading does not determine the arguments:
  two tuples of arguments read the same there and differ elsewhere
  (`ArgClock.determines_eq_false_iff`). A subject that reads only such a part does not read the rest
  of its arguments, a real restriction, as not reading one argument is. Where the part is in fact
  what the subject sees and the rest its clock, such a subject is one that ignores its clock, which
  the class holds for whole arguments already; a report of it is a true statement about the pair
  either way.
* **By the project's declaration**, each clock part that lies in a value of type `LeanIntent.Clock`
  (`ArgClock.InClock`): a structure of one number, the tick, which a project gives to the part of
  its subject's arguments it means as its clock. A part whose reading determines the arguments, such
  as the only argument of a policy of type `Nat → Act`, is all the subject has to read: every
  subject reads only it, so reading it as a clock makes every subject a script, and reading it as
  what the subject sees makes none. The type alone cannot tell the two apart, so it reads such a part
  as what the subject sees, and only the declaration, a policy of type `Clock → Act`, reads it as a
  clock. The declaration is a part of the subject's type, so it is read wherever a pair about that
  type is stated, and is the same for every such pair.
* A value of type `LeanIntent.Clock` in an argument where no clock part reaches, such as inside a
  list, an option, a sum, a declared type with several constructors or a function, is a declaration
  the class cannot read: `Ty.strayClock` finds it, and the trivial-witness check refuses every
  verdict about such a type rather than ignore the declaration.
-/

namespace LeanIntent

/-- A clock: the tick it reads, a number. A project gives this type to the part of its subject's
arguments that it means as the subject's clock, so that the trivial-witness check reads that part as
a clock even where it is all the subject has to read (`LeanIntent.ArgClock.InClock`). -/
structure Clock where
  /-- The tick the clock reads. -/
  tick : Nat
  deriving DecidableEq, Repr, LeanIntent.HasCode

/-- The name `LeanIntent.Clock`'s code carries. -/
def Clock.codeName : Lean.Name := ``Clock

/-- `Clock`'s code: its name, no parameter, and the chain of its one field, a number. -/
theorem Clock.code_eq : HasCode.code Clock = .decl Clock.codeName .unit (.prod .nat .unit) := rfl

/-! ## Clock parts -/

mutual

/-- A clock part of a value of type `t`: a number, a `Fin (n + 1)`, the length of a list or the size
of an array, reached through the sides of pairs and the fields of a declared type with one
constructor. -/
inductive Ty.ClockPart : Ty → Type
  /-- The value itself, a number. -/
  | nat : Ty.ClockPart .nat
  /-- The value itself, a `Fin (n + 1)`, read as its number. -/
  | fin (n : Nat) : Ty.ClockPart (.fin n)
  /-- The length of a list. -/
  | length (a : Ty) : Ty.ClockPart (.list a)
  /-- The size of an array. -/
  | size (a : Ty) : Ty.ClockPart (.array a)
  /-- A clock part of the left side of a pair. -/
  | fst {a : Ty} (b : Ty) : Ty.ClockPart a → Ty.ClockPart (.prod a b)
  /-- A clock part of the right side of a pair. -/
  | snd {b : Ty} (a : Ty) : Ty.ClockPart b → Ty.ClockPart (.prod a b)
  /-- A clock part of a field of a declared type whose representation is the chain of fields `r`. -/
  | field {r : Ty} (n : Lean.Name) (ps : Ty) : Ty.FieldClockPart r → Ty.ClockPart (.decl n ps r)

/-- A clock part inside one field of a chain of fields `r`, the representation of a declared type
with one constructor. -/
inductive Ty.FieldClockPart : Ty → Type
  /-- A clock part of the first field. -/
  | head {a : Ty} (rest : Ty) : Ty.ClockPart a → Ty.FieldClockPart (.prod a rest)
  /-- A clock part of a later field. -/
  | tail {rest : Ty} (a : Ty) : Ty.FieldClockPart rest → Ty.FieldClockPart (.prod a rest)

end

mutual

/-- The number a clock part reads from a value. -/
def Ty.ClockPart.read : {t : Ty} → Ty.ClockPart t → t.denote → Nat
  | _, .nat, x => x
  | _, .fin _, x => x.val
  | _, .length _, x => x.length
  | _, .size _, x => x.size
  | _, .fst _ k, x => k.read x.1
  | _, .snd _ k, x => k.read x.2
  | _, .field _ _ k, x => k.read x

/-- The number a clock part inside a field reads. -/
def Ty.FieldClockPart.read : {r : Ty} → Ty.FieldClockPart r → r.denote → Nat
  | _, .head _ k, x => k.read x.1
  | _, .tail _ k, x => k.read x.2

end

mutual

/-- Every clock part of a value of type `t`. -/
def Ty.clockParts : (t : Ty) → List (Ty.ClockPart t)
  | .nat => [.nat]
  | .fin n => [.fin n]
  | .list a => [.length a]
  | .array a => [.size a]
  | .prod a b => (Ty.clockParts a).map (.fst b) ++ (Ty.clockParts b).map (.snd a)
  | .decl n ps r => (Ty.fieldClockParts r).map (.field n ps)
  | _ => []

/-- Every clock part inside a field of the chain of fields `r`. -/
def Ty.fieldClockParts : (r : Ty) → List (Ty.FieldClockPart r)
  | .prod a rest => (Ty.clockParts a).map (.head rest) ++ (Ty.fieldClockParts rest).map (.tail a)
  | _ => []

end

mutual

/-- `clockParts` lists every clock part. -/
theorem Ty.mem_clockParts : {t : Ty} → (k : Ty.ClockPart t) → k ∈ Ty.clockParts t
  | _, .nat => by simp [Ty.clockParts]
  | _, .fin _ => by simp [Ty.clockParts]
  | _, .length _ => by simp [Ty.clockParts]
  | _, .size _ => by simp [Ty.clockParts]
  | _, .fst b k => by
      simp only [Ty.clockParts, List.mem_append, List.mem_map]
      exact .inl ⟨k, Ty.mem_clockParts k, rfl⟩
  | _, .snd a k => by
      simp only [Ty.clockParts, List.mem_append, List.mem_map]
      exact .inr ⟨k, Ty.mem_clockParts k, rfl⟩
  | _, .field n ps k => by
      simp only [Ty.clockParts, List.mem_map]
      exact ⟨k, Ty.mem_fieldClockParts k, rfl⟩

/-- `fieldClockParts` lists every clock part inside a field. -/
theorem Ty.mem_fieldClockParts : {r : Ty} → (k : Ty.FieldClockPart r) → k ∈ Ty.fieldClockParts r
  | _, .head rest k => by
      simp only [Ty.fieldClockParts, List.mem_append, List.mem_map]
      exact .inl ⟨k, Ty.mem_clockParts k, rfl⟩
  | _, .tail a k => by
      simp only [Ty.fieldClockParts, List.mem_append, List.mem_map]
      exact .inr ⟨k, Ty.mem_fieldClockParts k, rfl⟩

end

/-- A clock part of one of the arguments `as`. -/
inductive ArgClock : List Ty → Type
  /-- A clock part of the first argument. -/
  | here {a : Ty} {as : List Ty} : Ty.ClockPart a → ArgClock (a :: as)
  /-- A clock part of an argument after the first. -/
  | there {a : Ty} {as : List Ty} : ArgClock as → ArgClock (a :: as)

namespace ArgClock

/-- The number a clock part of the arguments reads from a tuple of them. -/
def read : {as : List Ty} → ArgClock as → Sig.Args as → Nat
  | _ :: _, .here k, xs => k.read xs.1
  | _ :: _, .there k, xs => k.read xs.2

/-- Every clock part of the arguments `as`. -/
def all : (as : List Ty) → List (ArgClock as)
  | [] => []
  | a :: as => (Ty.clockParts a).map .here ++ (all as).map .there

/-- `all` lists every clock part of the arguments. -/
theorem mem_all : {as : List Ty} → (k : ArgClock as) → k ∈ all as
  | _ :: _, .here k => List.mem_append.mpr (.inl (List.mem_map.mpr ⟨k, Ty.mem_clockParts k, rfl⟩))
  | _ :: _, .there k => List.mem_append.mpr (.inr (List.mem_map.mpr ⟨k, mem_all k, rfl⟩))

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

/-- Reading a number from the left side of pairs determines the pair exactly when it determines that
side and the right side has one value. -/
private theorem injective_fst_iff {α β : Type} (f : α → Nat) (a₀ : α) (b₀ : β) :
    Function.Injective (fun p : α × β => f p.1) ↔ Function.Injective f ∧ ∀ x y : β, x = y := by
  constructor
  · intro h
    exact ⟨fun x y e => congrArg Prod.fst (@h (x, b₀) (y, b₀) e),
      fun x y => congrArg Prod.snd (@h (a₀, x) (a₀, y) rfl)⟩
  · rintro ⟨hf, hb⟩ ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ e
    exact Prod.ext (hf e) (hb y₁ y₂)

/-- Reading a number from the right side of pairs determines the pair exactly when it determines
that side and the left side has one value. -/
private theorem injective_snd_iff {α β : Type} (f : β → Nat) (a₀ : α) (b₀ : β) :
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

mutual

/-- Whether a clock part's reading determines the value: a number and a `Fin (n + 1)` always, a
list's length and an array's size when the elements have one value, and a part of one side of a
pair, or of one field, when it determines that side or field and the rest has one value. -/
def Ty.ClockPart.determines : {t : Ty} → Ty.ClockPart t → Bool
  | _, .nat => true
  | _, .fin _ => true
  | _, .length a => a.unique
  | _, .size a => a.unique
  | _, .fst b k => b.unique && k.determines
  | _, .snd a k => a.unique && k.determines
  | _, .field _ _ k => k.determines

/-- Whether a clock part inside a field determines the chain of fields. -/
def Ty.FieldClockPart.determines : {r : Ty} → Ty.FieldClockPart r → Bool
  | _, .head rest k => rest.unique && k.determines
  | _, .tail a k => a.unique && k.determines

end

mutual

/-- A clock part's reading determines the value exactly when `determines` says so. -/
theorem Ty.ClockPart.determines_iff : {t : Ty} → (k : Ty.ClockPart t) →
    (k.determines = true ↔ Function.Injective k.read)
  | _, .nat => ⟨fun _ _ _ h => h, fun _ => rfl⟩
  | _, .fin _ => ⟨fun _ _ _ h => Fin.ext h, fun _ => rfl⟩
  | _, .length a => (Ty.unique_iff a).trans length_injective_iff.symm
  | _, .size a => (Ty.unique_iff a).trans size_injective_iff.symm
  | _, @Ty.ClockPart.fst a b k => by
      rw [Ty.ClockPart.determines, Bool.and_eq_true, Ty.unique_iff, Ty.ClockPart.determines_iff k]
      exact (and_comm).trans (injective_fst_iff k.read a.empty b.empty).symm
  | _, @Ty.ClockPart.snd b a k => by
      rw [Ty.ClockPart.determines, Bool.and_eq_true, Ty.unique_iff, Ty.ClockPart.determines_iff k]
      exact (and_comm).trans (injective_snd_iff k.read a.empty b.empty).symm
  | _, .field _ _ k => Ty.FieldClockPart.determines_iff k

/-- A clock part inside a field determines the chain of fields exactly when `determines` says so. -/
theorem Ty.FieldClockPart.determines_iff : {r : Ty} → (k : Ty.FieldClockPart r) →
    (k.determines = true ↔ Function.Injective k.read)
  | _, @Ty.FieldClockPart.head a rest k => by
      rw [Ty.FieldClockPart.determines, Bool.and_eq_true, Ty.unique_iff,
        Ty.ClockPart.determines_iff k]
      exact (and_comm).trans (injective_fst_iff k.read a.empty rest.empty).symm
  | _, @Ty.FieldClockPart.tail rest a k => by
      rw [Ty.FieldClockPart.determines, Bool.and_eq_true, Ty.unique_iff,
        Ty.FieldClockPart.determines_iff k]
      exact (and_comm).trans (injective_snd_iff k.read a.empty rest.empty).symm

end

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

namespace ArgClock

/-- Whether a clock part's reading determines the tuple of arguments: it determines its argument,
and every other argument's type has one value. -/
def determines : {as : List Ty} → ArgClock as → Bool
  | _ :: as, .here k => k.determines && as.all Ty.unique
  | a :: _, .there k => a.unique && k.determines

/-- A clock part's reading determines the arguments exactly when `determines` says so. -/
theorem determines_iff : {as : List Ty} → (k : ArgClock as) →
    (k.determines = true ↔ Function.Injective k.read)
  | a :: as, .here k => by
      rw [determines, Bool.and_eq_true, Ty.ClockPart.determines_iff k, Sig.args_unique_iff as]
      exact (injective_fst_iff k.read a.empty (Sig.Args.empty as)).symm
  | a :: as, .there k => by
      rw [determines, Bool.and_eq_true, Ty.unique_iff, determines_iff k]
      exact (and_comm).trans (injective_snd_iff k.read a.empty (Sig.Args.empty as)).symm

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

mutual

/-- The names of the declared types whose fields a clock part passes through, outermost first. -/
def Ty.ClockPart.names : {t : Ty} → Ty.ClockPart t → List Lean.Name
  | _, .nat => []
  | _, .fin _ => []
  | _, .length _ => []
  | _, .size _ => []
  | _, .fst _ k => k.names
  | _, .snd _ k => k.names
  | _, .field n _ k => n :: k.names

/-- The names of the declared types whose fields a clock part inside a field passes through. -/
def Ty.FieldClockPart.names : {r : Ty} → Ty.FieldClockPart r → List Lean.Name
  | _, .head _ k => k.names
  | _, .tail _ k => k.names

end

namespace ArgClock

/-- The names of the declared types whose fields a clock part of the arguments passes through. -/
def names : {as : List Ty} → ArgClock as → List Lean.Name
  | _ :: _, .here k => k.names
  | _ :: _, .there k => k.names

/-- The project declared the clock part `k` its subject's clock: `k` lies in a value of type
`LeanIntent.Clock`, whose code carries the name `Clock.codeName`. -/
def InClock {as : List Ty} (k : ArgClock as) : Prop := Clock.codeName ∈ k.names

instance {as : List Ty} (k : ArgClock as) : Decidable k.InClock :=
  inferInstanceAs (Decidable (Clock.codeName ∈ k.names))

end ArgClock

/-- Whether the code names `LeanIntent.Clock` anywhere, a parameter of a declared type included. Its
match has no catch-all case, so a code former added to `Ty` must say whether it holds one. -/
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
  | .decl n ps r => decide (n = Clock.codeName) || ps.namesClock || r.namesClock

mutual

/-- Whether a value of the code holds a `LeanIntent.Clock` where no clock part reaches it: inside a
list, an array, an option, a sum, a function, or a declared type with several constructors. The
clock parts reach through pairs and the fields of a declared type with one constructor, and a
`LeanIntent.Clock` they reach is a declaration the class reads. A parameter of a declared type is
not a part of its values except through the fields that hold it, which are read instead. -/
def Ty.strayClock : Ty → Bool
  | .prod a b => Ty.strayClock a || Ty.strayClock b
  | .decl n _ r => if n = Clock.codeName then false else Ty.fieldStrayClock r
  | t => t.namesClock

/-- Whether a chain of fields holds a `LeanIntent.Clock` where no clock part reaches it. A
representation that is not a chain, that of a type with several constructors, holds one wherever it
names one. -/
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
def script {b : Ty} {as : List Ty} (k : ArgClock as) (s : Nat → b.denote) : Fn b as :=
  Fn.curry b as fun xs => s (k.read xs)

/-- A script returns its action at the clock's reading. -/
theorem apply_script {b : Ty} {as : List Ty} (k : ArgClock as) (s : Nat → b.denote)
    (xs : Args as) : (k.script s).apply xs = s (k.read xs) :=
  Fn.apply_curry as _ xs

/-- A function reads only the clock part `k` exactly when it is a script of timed actions on `k`: it
takes, whenever `k` reads `n`, one action fixed for `n`. -/
theorem readsOnly_iff_script {b : Ty} {as : List Ty} (k : ArgClock as) (f : Fn b as) :
    f.ReadsOnly k ↔ ∃ s : Nat → b.denote, f = k.script s := by
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
