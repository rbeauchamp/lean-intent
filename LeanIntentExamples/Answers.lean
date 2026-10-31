import LeanIntentExamples.Sorting

/-!
# The owner's answers about the sorting records, kept across revisions

Two consequences of the sorting records of `LeanIntentExamples.Sorting` have been answered, one by
the owner and one on the owner's behalf (`attributed`):

* shown for `sortedOnly`, "the record allows returning the empty list for every input", a
  possibility, which the owner declined (`emptyForEvery`);
* shown for `sorting`, "returning `[1, 2]` for input `[2, 1, 1]` is ruled out", an entailment,
  which the assistant `claude` confirmed under its delegation, as a decision on the owner's behalf
  (`rulesOutShort`).

`sorting` keeps both answers and is accepted (`sortingAccepted`), and so every accepted revision,
whatever it says, excludes the empty-list function (`accepted_excludes_nilSort`). A revision that
drops the rearrangement property, `sortedOnly` again, is refused (`sortedOnly_refused`), and it
breaks each answer by a witness: the empty-list function meets it, the opposite of the declined
possibility (`sortedOnly_breaks_emptyForEvery`), and so does the function returning `[1, 2]` for
every input, a countermodel to the confirmed entailment (`sortedOnly_breaks_rulesOutShort`). A
revision that renames the record's clauses and vocabulary and restates its two properties as one
keeps both answers, since the same functions meet it (`restatedAccepted`).
-/

namespace LeanIntentExamples.Answers

open LeanIntent LeanIntentExamples.Sorting

/-- Declined: the record allows returning the empty list for every input. Like `rulesOutShort`, its
predicate uses only Lean's own library, so no revision of this project changes what it says. -/
def emptyForEvery : Answer (List Int → List Int) where
  consequence :=
    ⟨"returning the empty list for every input", .possibility, fun f => f = fun _ => []⟩
  verdict := .declined

/-- Confirmed: the record rules out returning `[1, 2]` for input `[2, 1, 1]`. -/
def rulesOutShort : Answer (List Int → List Int) where
  consequence :=
    ⟨"returning [1, 2] for input [2, 1, 1] is ruled out", .entailment,
      fun f => f [2, 1, 1] ≠ [1, 2]⟩
  verdict := .confirmed

/-- The stored answers about the sorting record. -/
def answers : List (Answer (List Int → List Int)) := [emptyForEvery, rulesOutShort]

/-- The stored answers with who gave each: the owner's, and a decision on the owner's behalf. Whom
each names changes nothing a revision must keep. -/
def attributed : List (Attributed (List Int → List Int)) :=
  [⟨emptyForEvery, .owner (.of "richard")⟩,
   ⟨rulesOutShort, .onBehalf (.of "claude") (.of "assistant")
     "A rearrangement of [2, 1, 1] has three elements, which the owner's restatement requires."⟩]

/-! ## The corrected record keeps them -/

theorem sorting_keeps : Keeps sorting answers := by
  refine (keeps_iff _ _).mpr fun a ha => ?_
  rcases List.mem_cons.mp ha with rfl | ha
  · intro f hf (hnil : f = fun _ => [])
    subst hnil
    exact sorting_refutes_nilSort hf
  rcases List.mem_cons.mp ha with rfl | ha
  · intro f hf heq
    have h := ((sorting_meets.mp hf).2 [2, 1, 1]).length_eq
    rw [heq] at h
    exact absurd h (by decide)
  exact nomatch ha

/-- The corrected record, accepted under the stored answers. -/
def sortingAccepted : Accepted answers := ⟨sorting, sorting_keeps⟩

/-- Every accepted revision excludes the empty-list function, whatever its properties say. -/
theorem accepted_excludes_nilSort (x : Accepted answers) : ¬ x.record.Meets nilSort :=
  fun h => x.excluded (List.mem_cons_self ..) h rfl

/-! ## A revision that drops the rearrangement property is refused -/

/-- The empty-list function meets the revision without the rearrangement property: it keeps the
opposite of the declined possibility. -/
theorem sortedOnly_breaks_emptyForEvery : emptyForEvery.opposite.KeptBy sortedOnly :=
  ⟨nilSort, sortedOnly_meets_nilSort, rfl⟩

/-- The function returning `[1, 2]` for every input meets it too, and returns `[1, 2]` for
`[2, 1, 1]`: a countermodel to the confirmed entailment. -/
theorem sortedOnly_breaks_rulesOutShort : rulesOutShort.opposite.KeptBy sortedOnly :=
  ⟨fun _ => [1, 2], sortedOnly_meets.mpr fun _ => by unfold Sorted; decide, fun h => h rfl⟩

/-- The revision without the rearrangement property is refused, by the declined possibility. -/
theorem sortedOnly_refused : ¬ Keeps sortedOnly answers :=
  not_keeps_of_opposite (List.mem_cons_self ..) sortedOnly_breaks_emptyForEvery

/-- No accepted revision is that record. -/
theorem sortedOnly_not_accepted (x : Accepted answers) : x.record ≠ sortedOnly :=
  fun h => sortedOnly_refused (h ▸ x.keeps)

/-! ## A revision that renames and restates keeps them -/

/-- The corrected record with its clauses and vocabulary renamed, and its two properties stated as
one. -/
def sortingRestated : IntentRecord (List Int → List Int) where
  shape := .function _ _
  dom := []
  props := [⟨"ascending rearrangement", fun f => ∀ l, Sorted (f l) ∧ (f l).Perm l⟩]
  vocab := [⟨"Ascending", List Int, Sorted⟩,
    ⟨"Rearrangement", List Int × List Int, fun p => p.1.Perm p.2⟩]

theorem sortingRestated_meets {f : List Int → List Int} :
    sortingRestated.Meets f ↔ sorting.Meets f := by
  rw [sorting_meets]
  simp [IntentRecord.Meets, IntentRecord.Dom, IntentRecord.Props, sortingRestated, forall_and]

/-- The restated record keeps both answers, each proved again of it. -/
def restatedAccepted : Accepted answers :=
  ⟨sortingRestated, (keeps_congr answers fun _ => sortingRestated_meets).mpr sorting_keeps⟩

end LeanIntentExamples.Answers
