module

public import LeanIntent.Declared

public section

namespace LeanIntentExamples.HigherOrder

open LeanIntent

theorem apply_subjects :
    (degenerate ((Nat → Nat) → Nat → Nat)).map Degenerate.reading =
      [.subject fun _ _ => 0, .subject fun f _ => f 0, .subject fun f n => f n,
        .subject fun _ n => n] := rfl

@[expose] def applies : IntentRecord ((Nat → Nat) → Nat → Nat) where
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

theorem applies_verdicts : Verdicts applies [false, false, true, false] := by
  refine ⟨fun h => ?_, fun h => ?_, (applies_meets_iff _).mpr fun _ _ => rfl, fun h => ?_, trivial⟩
  · exact absurd ((applies_meets_iff _).mp h (fun _ => 1) 0) (by decide)
  · exact absurd ((applies_meets_iff _).mp h (fun n => n) 1) (by decide)
  · exact absurd ((applies_meets_iff _).mp h (fun _ => 1) 0) (by decide)

structure Handler where
  run : Nat → Nat
  limit : Nat
  deriving LeanIntent.HasCode

theorem handler_code :
    HasCode.code Handler =
      .decl ``Handler .unit (.prod (.arrow .nat .nat) (.prod .nat .unit)) := rfl

theorem handler_subjects :
    (degenerate (Handler → Nat → Nat)).map Degenerate.reading =
      [.subject fun _ _ => 0, .subject fun h _ => h.run 0, .subject fun h _ => h.run h.limit,
        .subject fun h n => h.run n, .subject fun h _ => h.limit, .subject fun _ n => n] := rfl

theorem data_length : (degenerate (Nat → (Bool → Bool) × Unit)).length = 2 := rfl

theorem not_is_other :
    (Degenerate.others : Degenerate (Covered.sig (W := Nat → (Bool → Bool) × Unit))).Is
      fun _ => (not, ()) :=
  ⟨(not, ()), ⟨.inl rfl, trivial⟩, fun e => by
    have h : true = false := congrFun (congrArg Prod.fst e) false
    exact absurd h (by decide), rfl⟩

theorem bool_finite : (Ty.arrow .bool .bool).finite = true := rfl

theorem unit_finite : (Ty.arrow .nat .unit).finite = true := rfl

theorem nat_infinite : (Ty.arrow .nat .bool).finite = false := rfl

theorem list_subjects :
    (degenerate (List (Nat → Nat) → List (Nat → Nat))).map Degenerate.reading =
      [.subject fun _ => [], .subject fun l => l] := rfl

end LeanIntentExamples.HigherOrder
