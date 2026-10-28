/-!
# The types the degenerate class covers

The degenerate subjects of an intent record are fixed by the subject's type alone: each constant
function, the identity, the empty output and each projection. Lean's logic cannot inspect a type, so
the class is computed from a *code* for the type: a value of the closed inductive type `Ty`, whose
denotation `Ty.denote` is the type. The codes are those of the unit type, `Bool`, `Nat`, `Int` and
`String`, and of lists, arrays, options, pairs and sums of coded types. `LeanIntent.Degenerate`
builds the class over functions of such types; a type with no code is not covered.

For each code this module computes:

* `Ty.empty`, the empty value of the type: zero, the empty string, list or array, `none`, `false`
  and the unit value, componentwise for a pair, and the left side's for a sum;
* `Ty.part`, the values at which the class takes constant subjects. `Ty.finite` decides whether the
  type has finitely many values: when it holds, `Ty.part` lists every value
  (`Ty.mem_part_of_finite`), and when it fails, the type has infinitely many (`Ty.infinite`). The
  rule that fixes the part is `Ty.Small`, which `Ty.part` computes (`Ty.mem_part_iff`): a number, a
  string, a list or an array contributes only its empty value; the unit type and `Bool` every value;
  and an option, a pair or a sum every value built from its components' parts. The rule is fixed
  here, with the class, so that no record chooses which constants it is checked against.
-/

namespace LeanIntent

/-- Codes of the first-order data types the degenerate class covers. -/
inductive Ty where
  | unit
  | bool
  | nat
  | int
  | string
  | list (a : Ty)
  | array (a : Ty)
  | option (a : Ty)
  | prod (a b : Ty)
  | sum (a b : Ty)
  deriving DecidableEq

namespace Ty

/-- The type a code stands for. It is reducible, so that Lean's simplifier sees the type through
the code. -/
@[reducible] def denote : Ty → Type
  | unit => Unit
  | bool => Bool
  | nat => Nat
  | int => Int
  | string => String
  | list a => List a.denote
  | array a => Array a.denote
  | option a => Option a.denote
  | prod a b => a.denote × b.denote
  | sum a b => a.denote ⊕ b.denote

/-- The empty value of a type: the value a subject that returns nothing returns. -/
def empty : (t : Ty) → t.denote
  | unit => ()
  | bool => false
  | nat => (0 : Nat)
  | int => (0 : Int)
  | string => ""
  | list a => ([] : List a.denote)
  | array a => (#[] : Array a.denote)
  | option a => (none : Option a.denote)
  | prod a b => ((a.empty, b.empty) : a.denote × b.denote)
  | sum a b => (.inl a.empty : a.denote ⊕ b.denote)

/-- The values at which the degenerate class takes constant subjects, as a list. -/
def part : (t : Ty) → List t.denote
  | unit => [()]
  | bool => [false, true]
  | nat => [(0 : Nat)]
  | int => [(0 : Int)]
  | string => [""]
  | list a => [([] : List a.denote)]
  | array a => [(#[] : Array a.denote)]
  | option a => (none : Option a.denote) :: a.part.map some
  | prod a b => a.part.flatMap fun x => b.part.map fun y => ((x, y) : a.denote × b.denote)
  | sum a b => a.part.map (Sum.inl (β := b.denote)) ++ b.part.map (Sum.inr (α := a.denote))

/-- The rule that fixes which values of a type the degenerate class takes constant subjects at,
written apart from `part`: a number, a string, a list or an array only at its empty value; the unit
type and `Bool` at every value; an option at `none` and at each value of its part under `some`; a
pair at each pair of values of its sides' parts; and a sum at each value of either side's part. -/
def Small : (t : Ty) → t.denote → Prop
  | unit, _ => True
  | bool, _ => True
  | nat, x => x = (0 : Nat)
  | int, x => x = (0 : Int)
  | string, x => x = ""
  | list a, x => x = ([] : List a.denote)
  | array a, x => x = (#[] : Array a.denote)
  | option a, x => x = (none : Option a.denote) ∨ ∃ y, x = some y ∧ a.Small y
  | prod a b, x => a.Small (x : a.denote × b.denote).1 ∧ b.Small (x : a.denote × b.denote).2
  | sum a b, x => (∃ y, x = (.inl y : a.denote ⊕ b.denote) ∧ a.Small y) ∨
      ∃ y, x = (.inr y : a.denote ⊕ b.denote) ∧ b.Small y

/-- Whether the type has finitely many values: the unit type and `Bool` do, numbers, strings, lists
and arrays do not, and an option, a pair or a sum does exactly when each of its components does. -/
def finite : Ty → Bool
  | unit => true
  | bool => true
  | nat => false
  | int => false
  | string => false
  | list _ => false
  | array _ => false
  | option a => a.finite
  | prod a b => a.finite && b.finite
  | sum a b => a.finite && b.finite

/-- `part` lists exactly the values the rule `Small` admits. -/
theorem mem_part_iff : (t : Ty) → (x : t.denote) → (x ∈ t.part ↔ t.Small x)
  | unit, x => by cases x; simp [part, Small]
  | bool, x => by cases x <;> simp [part, Small]
  | nat, x => by simp [part, Small]
  | int, x => by simp [part, Small]
  | string, x => by simp [part, Small]
  | list _, x => by simp [part, Small]
  | array _, x => by simp [part, Small]
  | option a, x => by
      cases x with
      | none => simp [part, Small]
      | some y => simp [part, Small, mem_part_iff a y]
  | prod a b, x => by
      obtain ⟨y, z⟩ := x
      simp [part, Small, mem_part_iff a y, mem_part_iff b z]
  | sum a b, x => by
      cases x with
      | inl y => simp [part, Small, mem_part_iff a y]
      | inr z => simp [part, Small, mem_part_iff b z]

/-- The rule admits the empty value of every type. -/
theorem small_empty : (t : Ty) → t.Small t.empty
  | unit => trivial
  | bool => trivial
  | nat => rfl
  | int => rfl
  | string => rfl
  | list _ => rfl
  | array _ => rfl
  | option _ => .inl rfl
  | prod a b => ⟨small_empty a, small_empty b⟩
  | sum a _ => .inl ⟨_, rfl, small_empty a⟩

/-- The empty value of every type is in its part. -/
theorem empty_mem_part (t : Ty) : t.empty ∈ t.part := (mem_part_iff t _).mpr (small_empty t)

/-- No type's part is empty. -/
theorem part_ne_nil (t : Ty) : t.part ≠ [] := List.ne_nil_of_mem (empty_mem_part t)

/-- The rule admits every value of a type with finitely many values. -/
theorem small_of_finite : (t : Ty) → t.finite = true → ∀ x, t.Small x
  | unit, _, _ => trivial
  | bool, _, _ => trivial
  | option a, h, x => by
      cases x with
      | none => exact .inl rfl
      | some y => exact .inr ⟨y, rfl, small_of_finite a h y⟩
  | prod a b, h, x => by
      simp only [finite, Bool.and_eq_true] at h
      exact ⟨small_of_finite a h.1 _, small_of_finite b h.2 _⟩
  | sum a b, h, x => by
      simp only [finite, Bool.and_eq_true] at h
      cases x with
      | inl y => exact .inl ⟨y, rfl, small_of_finite a h.1 y⟩
      | inr z => exact .inr ⟨z, rfl, small_of_finite b h.2 z⟩

/-- A type with finitely many values has every one in its part. -/
theorem mem_part_of_finite {t : Ty} (h : t.finite = true) (x : t.denote) : x ∈ t.part :=
  (mem_part_iff t x).mpr (small_of_finite t h x)

/-- A type for which `finite` fails has infinitely many values: an injection from `Nat`. -/
theorem infinite : (t : Ty) → t.finite = false → ∃ f : Nat → t.denote, Function.Injective f
  | nat, _ => ⟨fun n => (n : Nat), fun _ _ h => h⟩
  | int, _ => ⟨fun n => (Int.ofNat n : Int), fun _ _ h => Int.ofNat.inj h⟩
  | string, _ => ⟨fun n => ("".pushn 'a' n : String), fun m n h => by
      have := congrArg String.length h
      simpa [String.length_pushn] using this⟩
  | list a, _ => ⟨fun n => (List.replicate n a.empty : List a.denote), fun m n h => by
      have := congrArg List.length h
      simpa using this⟩
  | array a, _ => ⟨fun n => (Array.replicate n a.empty : Array a.denote), fun m n h => by
      have := congrArg Array.size h
      simpa using this⟩
  | option a, h => by
      obtain ⟨f, hf⟩ := infinite a h
      exact ⟨fun n => (some (f n) : Option a.denote), fun m n e => hf (Option.some.inj e)⟩
  | prod a b, h => by
      simp only [finite, Bool.and_eq_false_iff] at h
      rcases h with h | h
      · obtain ⟨f, hf⟩ := infinite a h
        exact ⟨fun n => ((f n, b.empty) : a.denote × b.denote),
          fun m n e => hf (congrArg Prod.fst e)⟩
      · obtain ⟨f, hf⟩ := infinite b h
        exact ⟨fun n => ((a.empty, f n) : a.denote × b.denote),
          fun m n e => hf (congrArg Prod.snd e)⟩
  | sum a b, h => by
      simp only [finite, Bool.and_eq_false_iff] at h
      rcases h with h | h
      · obtain ⟨f, hf⟩ := infinite a h
        exact ⟨fun n => (.inl (f n) : a.denote ⊕ b.denote), fun m n e => hf (Sum.inl.inj e)⟩
      · obtain ⟨f, hf⟩ := infinite b h
        exact ⟨fun n => (.inr (f n) : a.denote ⊕ b.denote), fun m n e => hf (Sum.inr.inj e)⟩

end Ty

end LeanIntent
