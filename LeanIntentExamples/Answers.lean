module

public import LeanIntentExamples.Sorting

public section

namespace LeanIntentExamples.Answers

open LeanIntent LeanIntentExamples.Sorting

@[expose] def emptyForEvery : Answer (List Int → List Int) where
  consequence :=
    ⟨"returning the empty list for every input", .possibility, fun f => f = fun _ => []⟩
  verdict := .declined

@[expose] def rulesOutShort : Answer (List Int → List Int) where
  consequence :=
    ⟨"returning [1, 2] for input [2, 1, 1] is ruled out", .entailment,
      fun f => f [2, 1, 1] ≠ [1, 2]⟩
  verdict := .confirmed

@[expose] def answers : List (Answer (List Int → List Int)) := [emptyForEvery, rulesOutShort]

@[expose] def attributed : List (Attributed (List Int → List Int)) :=
  [⟨emptyForEvery, .owner (.of "richard")⟩,
   ⟨rulesOutShort, .onBehalf (.of "claude") (.of "assistant")
     "A rearrangement of [2, 1, 1] has three elements, which the owner's restatement requires."⟩]

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

@[expose] def sortingAccepted : Accepted answers := ⟨sorting, sorting_keeps⟩

theorem accepted_excludes_nilSort (x : Accepted answers) : ¬ x.record.Meets nilSort :=
  fun h => x.excluded (List.mem_cons_self ..) h rfl

theorem sortedOnly_breaks_emptyForEvery : emptyForEvery.opposite.KeptBy sortedOnly :=
  ⟨nilSort, sortedOnly_meets_nilSort, rfl⟩

theorem sortedOnly_breaks_rulesOutShort : rulesOutShort.opposite.KeptBy sortedOnly :=
  ⟨fun _ => [1, 2], sortedOnly_meets.mpr fun _ => by unfold Sorted; decide, fun h => h rfl⟩

theorem sortedOnly_refused : ¬ Keeps sortedOnly answers :=
  not_keeps_of_opposite (List.mem_cons_self ..) sortedOnly_breaks_emptyForEvery

theorem sortedOnly_not_accepted (x : Accepted answers) : x.record ≠ sortedOnly :=
  fun h => sortedOnly_refused (h ▸ x.keeps)

@[expose] def sortingRestated : IntentRecord (List Int → List Int) where
  shape := .function _ _
  dom := []
  props := [⟨"ascending rearrangement", fun f => ∀ l, Sorted (f l) ∧ (f l).Perm l⟩]
  vocab := [⟨"Ascending", List Int, Sorted⟩,
    ⟨"Rearrangement", List Int × List Int, fun p => p.1.Perm p.2⟩]

theorem sortingRestated_meets {f : List Int → List Int} :
    sortingRestated.Meets f ↔ sorting.Meets f := by
  rw [sorting_meets]
  simp [IntentRecord.Meets, IntentRecord.Dom, IntentRecord.Props, sortingRestated, forall_and]

@[expose] def restatedAccepted : Accepted answers :=
  ⟨sortingRestated, (keeps_congr answers fun _ => sortingRestated_meets).mpr sorting_keeps⟩

end LeanIntentExamples.Answers
