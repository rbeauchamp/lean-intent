module

public import LeanIntent.Declared

public section

namespace LeanIntentExamples.LargeFinite

open LeanIntent

abbrev Hash := UInt64 → UInt64 → UInt64 → UInt64

theorem hash_length : (degenerate Hash).length = 5 := rfl

theorem hash_subjects :
    (degenerate Hash).map Degenerate.reading =
      [.subject fun _ _ _ => 0, .otherConstants, .subject fun a _ _ => a, .subject fun _ b _ => b,
        .subject fun _ _ c => c] := rfl

theorem hash_constant_covered (v : UInt64) :
    ∃ d ∈ degenerate Hash, d.Is (fun _ _ _ => v) :=
  constant_covered_of_finite (W := Hash) rfl v

@[expose] def varies : IntentRecord Hash where
  shape := .function _ _
  dom := []
  props := [⟨"varies", fun f => ∃ a b c a' b' c', f a b c ≠ f a' b' c'⟩]
  vocab := []

theorem varies_refutes_const (v : UInt64) : ¬ varies.Meets (fun _ _ _ => v) := fun h => by
  obtain ⟨_, _, _, _, _, _, e⟩ := h.2 _ (List.mem_singleton.mpr rfl)
  exact e rfl

theorem varies_of (f : Hash) (a b c a' b' c' : UInt64) (e : f a b c ≠ f a' b' c') :
    varies.Meets f :=
  ⟨fun _ h => (nomatch h), fun p hp => by
    rcases List.mem_singleton.mp hp with rfl
    exact ⟨a, b, c, a', b', c', e⟩⟩

theorem varies_verdicts : Verdicts varies [false, false, true, true, true] := by
  refine ⟨varies_refutes_const 0, ?_, ?_, ?_, ?_, trivial⟩
  · rintro ⟨_, ⟨v, _, _, rfl⟩, h⟩
    exact varies_refutes_const v h
  · exact varies_of _ 0 0 0 1 0 0 UInt64.zero_ne_one
  · exact varies_of _ 0 0 0 0 1 0 UInt64.zero_ne_one
  · exact varies_of _ 0 0 0 0 0 1 UInt64.zero_ne_one

@[expose] def fortyTwo : IntentRecord Hash where
  shape := .function _ _
  dom := []
  props := [⟨"is 42", fun f => ∀ a b c, f a b c = 42⟩]
  vocab := []

theorem fortyTwo_meets_iff (f : Hash) : fortyTwo.Meets f ↔ ∀ a b c, f a b c = 42 :=
  ⟨fun h => h.2 _ (List.mem_singleton.mpr rfl), fun h =>
    ⟨fun _ h => (nomatch h), fun p hp => by
      rcases List.mem_singleton.mp hp with rfl
      exact h⟩⟩

theorem fortyTwo_verdicts : Verdicts fortyTwo [false, true, false, false, false] := by
  refine ⟨?_, ⟨_, ⟨(42 : UInt64), trivial, (by decide : (42 : UInt64) ≠ 0), rfl⟩, (fortyTwo_meets_iff _).mpr fun _ _ _ => rfl⟩,
    ?_, ?_, ?_, trivial⟩
  · exact fun h => absurd ((fortyTwo_meets_iff _).mp h 0 0 0) (by decide)
  · exact fun h => absurd ((fortyTwo_meets_iff _).mp h 0 0 0) (by decide)
  · exact fun h => absurd ((fortyTwo_meets_iff _).mp h 0 0 0) (by decide)
  · exact fun h => absurd ((fortyTwo_meets_iff _).mp h 0 0 0) (by decide)

theorem fortyTwo_possibilities :
    (possibilities fortyTwo_verdicts).map Consequence.holds =
      [(Degenerate.others : Degenerate (Covered.sig (W := Hash))).Is] := rfl

theorem fortyTwo_metBy :
    (metBy Hash [false, true, false, false, false]).map Degenerate.reading = [.otherConstants] := rfl

structure Clock where
  clock : UInt64
  dayLength : UInt64
  deriving LeanIntent.HasCode

theorem phase_subjects :
    (degenerate (Clock → Fin 8)).map Degenerate.reading =
      [.subject fun _ => 0, .subject fun _ => 1, .subject fun _ => 2, .subject fun _ => 3,
        .subject fun _ => 4, .subject fun _ => 5, .subject fun _ => 6, .subject fun _ => 7] := rfl

@[expose] def reachesAll : IntentRecord (Clock → Fin 8) where
  shape := .function _ _
  dom := []
  props := [⟨"reaches every phase", fun f => ∀ i, ∃ c, f c = i⟩]
  vocab := []

theorem reachesAll_refutes_const (v : Fin 8) : ¬ reachesAll.Meets (fun _ => v) := fun h => by
  have reach : ∀ i : Fin 8, v = i := fun i =>
    (h.2 _ (List.mem_singleton.mpr rfl) i).elim fun _ e => e
  exact absurd ((reach 0).symm.trans (reach 1)) (by decide)

theorem reachesAll_verdicts :
    Verdicts reachesAll [false, false, false, false, false, false, false, false] :=
  ⟨reachesAll_refutes_const _, reachesAll_refutes_const _, reachesAll_refutes_const _,
    reachesAll_refutes_const _, reachesAll_refutes_const _, reachesAll_refutes_const _,
    reachesAll_refutes_const _, reachesAll_refutes_const _, trivial⟩

set_option maxRecDepth 10000 in
theorem fin255_length : (degenerate (Unit → Fin 255)).length = 255 := rfl

theorem fin256_length : (degenerate (Unit → Fin 256)).length = 2 := rfl

theorem large_length : (degenerate (Unit → Fin 1000000000000)).length = 2 := rfl

theorem char_length : (degenerate (Char → Char)).length = 3 := rfl

theorem float_length : (degenerate (Float → Float)).length = 3 := rfl

structure Flags where
  (a b c d e f g h : Bool)
  deriving LeanIntent.HasCode

theorem flags_length : (degenerate Flags).length = 2 := rfl

theorem pair_length : (degenerate (UInt8 × Nat)).length = 2 := rfl

end LeanIntentExamples.LargeFinite
