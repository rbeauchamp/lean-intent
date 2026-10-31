import LeanIntent.Declared

/-!
# Records about functions as arguments and inside data

A function among a subject's arguments is applied one level deep, to the empty value of its argument
type or to a component of an argument reached without applying a function. So a subject of type
`(Nat → Nat) → Nat → Nat` has the constant at zero, `f` at zero, `f` at its argument (the identity of
`Nat → Nat`, read with the function's own argument) and the projection onto that argument
(`apply_subjects`), and a record that asks the subject to apply its function is met by exactly one of
them (`applies_verdicts`). A function in a field of a declared type is reached through the field
(`handler_subjects`).

A function inside data is a value like any other: its empty value is the constant at its result's
empty value. It counts above `Ty.listBound`, so its values are not listed: where the output holds one,
the class has the constant at the empty value and the others as one member (`data_length`), among
which, where the function type has finitely many values, is each of them (`not_is_other`). The type
`Bool → Bool` has finitely many, `Nat → Unit` one, and `Nat → Bool` infinitely many (`bool_finite`,
`unit_finite`, `nat_infinite`). A list of functions has only the empty list as a constant, as any list
does (`list_subjects`).
-/

namespace LeanIntentExamples.HigherOrder

open LeanIntent

/-- The class of a function that takes a function and a number. -/
theorem apply_subjects :
    (degenerate ((Nat → Nat) → Nat → Nat)).map Degenerate.subject =
      [fun _ _ => 0, fun f _ => f 0, fun f n => f n, fun _ n => n] := rfl

/-- The subject applies its function to its argument. -/
def applies : IntentRecord ((Nat → Nat) → Nat → Nat) where
  shape := .function _ _
  dom := []
  props := [⟨"applies", fun g => ∀ f n, g f n = f n⟩]
  vocab := []

theorem applies_meets_iff (g : (Nat → Nat) → Nat → Nat) :
    applies.Meets g ↔ ∀ f n, g f n = f n :=
  ⟨fun h => h.2 _ (List.mem_singleton.mpr rfl), fun h =>
    ⟨fun _ h => (nomatch h), fun p hp => by
      rcases List.mem_singleton.mp hp with rfl
      exact h⟩⟩

/-- Only the member that applies the function to the argument meets `applies`. -/
theorem applies_verdicts : Verdicts applies [false, false, true, false] := by
  refine ⟨fun h => ?_, fun h => ?_, (applies_meets_iff _).mpr fun _ _ => rfl, fun h => ?_, trivial⟩
  · exact absurd ((applies_meets_iff _).mp h (fun _ => 1) 0) (by decide)
  · exact absurd ((applies_meets_iff _).mp h (fun n => n) 1) (by decide)
  · exact absurd ((applies_meets_iff _).mp h (fun _ => 1) 0) (by decide)

/-- A handler of numbers, with a limit. -/
structure Handler where
  /-- What it does. -/
  run : Nat → Nat
  /-- Its limit. -/
  limit : Nat
  deriving LeanIntent.HasCode

/-- The code of a declared type holds the code of the function in its field. -/
theorem handler_code :
    HasCode.code Handler =
      .decl ``Handler .unit (.prod (.arrow .nat .nat) (.prod .nat .unit)) := rfl

/-- The class reaches the function through its field and applies it to the empty value, to the
structure's other number and to the argument. -/
theorem handler_subjects :
    (degenerate (Handler → Nat → Nat)).map Degenerate.subject =
      [fun _ _ => 0, fun h _ => h.run 0, fun h _ => h.run h.limit, fun h n => h.run n,
        fun h _ => h.limit, fun _ n => n] := rfl

/-- A function inside the output has the constant at the empty value and the others, and no
projection, since no argument holds that output. -/
theorem data_length : (degenerate (Nat → (Bool → Bool) × Unit)).length = 2 := rfl

/-- The negation inside the output is among the others, though it is no constant function, since
`Bool → Bool` has finitely many values. -/
theorem not_is_other :
    (Degenerate.others : Degenerate (Covered.sig (W := Nat → (Bool → Bool) × Unit))).Is
      fun _ => (not, ()) :=
  ⟨(not, ()), ⟨.inl rfl, trivial⟩, fun e => by
    have h : true = false := congrFun (congrArg Prod.fst e) false
    exact absurd h (by decide), rfl⟩

theorem bool_finite : (Ty.arrow .bool .bool).finite = true := rfl

theorem unit_finite : (Ty.arrow .nat .unit).finite = true := rfl

theorem nat_infinite : (Ty.arrow .nat .bool).finite = false := rfl

/-- The class of a function of lists of functions: the empty list, and the identity. -/
theorem list_subjects :
    (degenerate (List (Nat → Nat) → List (Nat → Nat))).map Degenerate.subject =
      [fun _ => [], fun l => l] := rfl

end LeanIntentExamples.HigherOrder
