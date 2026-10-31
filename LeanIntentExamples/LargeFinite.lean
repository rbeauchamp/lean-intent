import LeanIntent.Declared

/-!
# Records about finite types too large to enumerate

`UInt64 → UInt64 → UInt64 → UInt64`, the shape of a hash, has `2 ^ 64` constant functions. Its class
has five members: the constant at zero, all the other constants as one member, and the three
projections (`hash_length`, `hash_subjects`). The verdict on the other constants is one theorem about
all of them, so nothing enumerates the type: a record that asks the result to vary with the arguments
refutes them all at once and is met by each projection (`varies_verdicts`), and a record met only by
the constant at 42, a subject no fixed sample of values need contain, is reported through that member
(`fortyTwo_verdicts`, `fortyTwo_possibilities`), and read from the verdicts as that group, so it names
no subject the verdicts exclude (`fortyTwo_metBy`).

A function from a clock to `Fin 8`, with at most `Ty.listBound` values, has the constant at each of
the eight values and no projection, since no field has type `Fin 8` (`phase_subjects`); a record that
asks the function to reach every phase refutes all eight (`reachesAll_verdicts`).

The rule is one for every type: it counts the constants the class would list, not the type's name. So
`Fin 255` lists its values and `Fin 256` does not (`fin255_length`, `fin256_length`), and neither does
a structure of eight `Bool`s, which has 256 (`flags_length`).
-/

namespace LeanIntentExamples.LargeFinite

open LeanIntent

/-- The shape of a hash of three words. -/
abbrev Hash := UInt64 → UInt64 → UInt64 → UInt64

/-- The class of `Hash` has five members, whatever the number of values of `UInt64`. -/
theorem hash_length : (degenerate Hash).length = 5 := rfl

/-- Its members, read: the constant at zero, all the other constants as a group, and the
projections. -/
theorem hash_subjects :
    (degenerate Hash).map Degenerate.reading =
      [.subject fun _ _ _ => 0, .otherConstants, .subject fun a _ _ => a, .subject fun _ b _ => b,
        .subject fun _ _ c => c] := rfl

/-- Every one of the `2 ^ 64` constants is a subject of a member of the class. -/
theorem hash_constant_covered (v : UInt64) :
    ∃ d ∈ degenerate Hash, d.Is (fun _ _ _ => v) :=
  constant_covered_of_finite (W := Hash) rfl v

/-- The result varies with the arguments. -/
def varies : IntentRecord Hash where
  shape := .function _ _
  dom := []
  props := [⟨"varies", fun f => ∃ a b c a' b' c', f a b c ≠ f a' b' c'⟩]
  vocab := []

/-- No constant can vary. -/
theorem varies_refutes_const (v : UInt64) : ¬ varies.Meets (fun _ _ _ => v) := fun h => by
  obtain ⟨_, _, _, _, _, _, e⟩ := h.2 _ (List.mem_singleton.mpr rfl)
  exact e rfl

theorem varies_of (f : Hash) (a b c a' b' c' : UInt64) (e : f a b c ≠ f a' b' c') :
    varies.Meets f :=
  ⟨fun _ h => (nomatch h), fun p hp => by
    rcases List.mem_singleton.mp hp with rfl
    exact ⟨a, b, c, a', b', c', e⟩⟩

/-- The constants, all of them at once, do not meet `varies`, and each projection does. -/
theorem varies_verdicts : Verdicts varies [false, false, true, true, true] := by
  refine ⟨varies_refutes_const 0, ?_, ?_, ?_, ?_, trivial⟩
  · rintro ⟨_, ⟨v, _, _, rfl⟩, h⟩
    exact varies_refutes_const v h
  · exact varies_of _ 0 0 0 1 0 0 UInt64.zero_ne_one
  · exact varies_of _ 0 0 0 0 1 0 UInt64.zero_ne_one
  · exact varies_of _ 0 0 0 0 0 1 UInt64.zero_ne_one

/-- The result is always 42. -/
def fortyTwo : IntentRecord Hash where
  shape := .function _ _
  dom := []
  props := [⟨"is 42", fun f => ∀ a b c, f a b c = 42⟩]
  vocab := []

theorem fortyTwo_meets_iff (f : Hash) : fortyTwo.Meets f ↔ ∀ a b c, f a b c = 42 :=
  ⟨fun h => h.2 _ (List.mem_singleton.mpr rfl), fun h =>
    ⟨fun _ h => (nomatch h), fun p hp => by
      rcases List.mem_singleton.mp hp with rfl
      exact h⟩⟩

/-- Only the constant at 42 meets `fortyTwo`, and the member for the other constants reports it. -/
theorem fortyTwo_verdicts : Verdicts fortyTwo [false, true, false, false, false] := by
  refine ⟨?_, ⟨_, ⟨(42 : UInt64), trivial, (by decide : (42 : UInt64) ≠ 0), rfl⟩, (fortyTwo_meets_iff _).mpr fun _ _ _ => rfl⟩,
    ?_, ?_, ?_, trivial⟩
  · exact fun h => absurd ((fortyTwo_meets_iff _).mp h 0 0 0) (by decide)
  · exact fun h => absurd ((fortyTwo_meets_iff _).mp h 0 0 0) (by decide)
  · exact fun h => absurd ((fortyTwo_meets_iff _).mp h 0 0 0) (by decide)
  · exact fun h => absurd ((fortyTwo_meets_iff _).mp h 0 0 0) (by decide)

/-- The check reports one possibility, that the subject is one of the other constants, among which
is the constant at 42. -/
theorem fortyTwo_possibilities :
    (possibilities fortyTwo_verdicts).map Consequence.holds =
      [(Degenerate.others : Degenerate (Covered.sig (W := Hash))).Is] := rfl

/-- Read from the verdicts, what meets `fortyTwo` is the group of other constants, which holds the
constant at 42, and not the constant at zero. -/
theorem fortyTwo_metBy :
    (metBy Hash [false, true, false, false, false]).map Degenerate.reading = [.otherConstants] := rfl

/-- A clock and the length of its day. -/
structure Clock where
  /-- The steps since the start. -/
  clock : UInt64
  /-- The steps in a day. -/
  dayLength : UInt64
  deriving LeanIntent.HasCode

/-- The class of a function from clocks to phases: the constant at each phase, and no projection,
since no field has type `Fin 8`. -/
theorem phase_subjects :
    (degenerate (Clock → Fin 8)).map Degenerate.reading =
      [.subject fun _ => 0, .subject fun _ => 1, .subject fun _ => 2, .subject fun _ => 3,
        .subject fun _ => 4, .subject fun _ => 5, .subject fun _ => 6, .subject fun _ => 7] := rfl

/-- Every phase is reached. -/
def reachesAll : IntentRecord (Clock → Fin 8) where
  shape := .function _ _
  dom := []
  props := [⟨"reaches every phase", fun f => ∀ i, ∃ c, f c = i⟩]
  vocab := []

/-- A constant reaches only its own phase. -/
theorem reachesAll_refutes_const (v : Fin 8) : ¬ reachesAll.Meets (fun _ => v) := fun h => by
  have reach : ∀ i : Fin 8, v = i := fun i =>
    (h.2 _ (List.mem_singleton.mpr rfl) i).elim fun _ e => e
  exact absurd ((reach 0).symm.trans (reach 1)) (by decide)

/-- None of the eight constants meets `reachesAll`. -/
theorem reachesAll_verdicts :
    Verdicts reachesAll [false, false, false, false, false, false, false, false] :=
  ⟨reachesAll_refutes_const _, reachesAll_refutes_const _, reachesAll_refutes_const _,
    reachesAll_refutes_const _, reachesAll_refutes_const _, reachesAll_refutes_const _,
    reachesAll_refutes_const _, reachesAll_refutes_const _, trivial⟩

set_option maxRecDepth 10000 in
/-- `Fin 255` is listed: 255 constants. Computing a list this long goes deeper than Lean's default
limit on the elaborator's recursion. -/
theorem fin255_length : (degenerate (Unit → Fin 255)).length = 255 := rfl

/-- `Fin 256` is above the bound: the constant at zero and the others. -/
theorem fin256_length : (degenerate (Unit → Fin 256)).length = 2 := rfl

/-- However large the type. -/
theorem large_length : (degenerate (Unit → Fin 1000000000000)).length = 2 := rfl

/-- `Char`, with its identity. -/
theorem char_length : (degenerate (Char → Char)).length = 3 := rfl

/-- `Float`, with its identity. -/
theorem float_length : (degenerate (Float → Float)).length = 3 := rfl

/-- Eight flags, which have 256 values. -/
structure Flags where
  (a b c d e f g h : Bool)
  deriving LeanIntent.HasCode

/-- A declared type above the bound is checked as `Fin 256` is. -/
theorem flags_length : (degenerate Flags).length = 2 := rfl

/-- A pair of a large type with a number takes all of the first component, with zero. -/
theorem pair_length : (degenerate (UInt8 × Nat)).length = 2 := rfl

end LeanIntentExamples.LargeFinite
