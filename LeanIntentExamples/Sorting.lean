module

public import LeanIntent.Degenerate
public import LeanIntent.Refinement

public section

namespace LeanIntentExamples.Sorting

open LeanIntent

@[expose] def Sorted (l : List Int) : Prop := l.Pairwise (· ≤ ·)

@[expose] def sortedClause : Clause (List Int → List Int) := ⟨"sorted", fun f => ∀ l, Sorted (f l)⟩

@[expose] def permClause : Clause (List Int → List Int) := ⟨"rearranges", fun f => ∀ l, (f l).Perm l⟩

@[expose] def sortedPred : Pred := ⟨"Sorted", List Int, Sorted⟩

@[expose] def permPred : Pred := ⟨"Perm", List Int × List Int, fun p => p.1.Perm p.2⟩

@[expose] def sortedOnly : IntentRecord (List Int → List Int) where
  shape := .function _ _
  dom := []
  props := [sortedClause]
  vocab := [sortedPred]

@[expose] def sorting : IntentRecord (List Int → List Int) where
  shape := .function _ _
  dom := []
  props := [sortedClause, permClause]
  vocab := [sortedPred, permPred]

@[expose] def le (a b : Int) : Bool := decide (a ≤ b)

@[expose] def sort (l : List Int) : List Int := l.mergeSort le

@[expose] def nilSort (_ : List Int) : List Int := []

theorem sort_sorted (l : List Int) : Sorted (sort l) :=
  (List.pairwise_mergeSort (le := le)
    (fun a b c hab hbc => by simp only [le, decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [le, Bool.or_eq_true, decide_eq_true_eq]; omega) l).imp
    (fun h => by simpa [le] using h)

theorem sort_perm (l : List Int) : (sort l).Perm l := List.mergeSort_perm _ _

theorem sorted_perm_unique {xs ys zs : List Int} (hx : Sorted xs) (hy : Sorted ys)
    (px : xs.Perm zs) (py : ys.Perm zs) : xs = ys :=
  List.Perm.eq_of_pairwise (fun _ _ _ _ h1 h2 => Int.le_antisymm h1 h2) hx hy (px.trans py.symm)

theorem sort_ne_nilSort : sort ≠ nilSort := by
  intro h
  have := (sort_perm [0]).length_eq
  rw [h] at this
  simp [nilSort] at this

theorem sortedOnly_meets {f : List Int → List Int} :
    sortedOnly.Meets f ↔ ∀ l, Sorted (f l) := by
  simp [IntentRecord.Meets, IntentRecord.Dom, IntentRecord.Props, sortedOnly, sortedClause]

theorem sorting_meets {f : List Int → List Int} :
    sorting.Meets f ↔ (∀ l, Sorted (f l)) ∧ ∀ l, (f l).Perm l := by
  simp [IntentRecord.Meets, IntentRecord.Dom, IntentRecord.Props, sorting, sortedClause,
    permClause]

theorem sortedOnly_meets_nilSort : sortedOnly.Meets nilSort :=
  sortedOnly_meets.mpr fun _ => List.Pairwise.nil

theorem sortedOnly_meets_sort : sortedOnly.Meets sort :=
  sortedOnly_meets.mpr sort_sorted

theorem sortedOnly_not_o5_eq : ¬ O5 sortedOnly .eq :=
  not_o5_eq sortedOnly_meets_sort sortedOnly_meets_nilSort sort_ne_nilSort

theorem sortedOnly_o5_rel (R : (List Int → List Int) → (List Int → List Int) → Prop)
    (h : O5 sortedOnly (.rel R)) : R sort nilSort :=
  h.relates sortedOnly_meets_sort sortedOnly_meets_nilSort

theorem sortedOnly_o5_widest : O5 sortedOnly .widest := o5_widest _

theorem sorting_meets_sort : sorting.Meets sort :=
  sorting_meets.mpr ⟨sort_sorted, sort_perm⟩

theorem sorting_refutes_nilSort : ¬ sorting.Meets nilSort := fun h =>
  absurd ((sorting_meets.mp h).2 [0]).length_eq (by simp [nilSort])

theorem sorting_o1 :
    o1 sorting = [sortedClause.typed, permClause.typed, sortedPred.typed, permPred.typed] := rfl

theorem sorting_o2 : O2 sorting := by
  refine (o2_correct _).mpr ⟨⟨sort, fun _ h => nomatch h⟩, ?_⟩
  show ∀ p ∈ [sortedPred, permPred], ∃ a, p.holds a
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨[], List.Pairwise.nil⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨([], []), List.Perm.nil⟩
  exact nomatch hp

theorem sorting_o2Run : O2Run sorting := o2Run_of_meets sorting_meets_sort

theorem sorting_o3 : O3 sorting := by
  refine (o3_correct _).mpr ?_
  show ∀ p ∈ [sortedClause, permClause], ∃ w, ¬ p.holds w
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨fun _ => [1, 0], fun h =>
      absurd (List.rel_of_pairwise_cons (h []) (List.mem_singleton_self 0)) (by decide)⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨nilSort, fun h => absurd (h [0]).length_eq (by simp [nilSort])⟩
  exact nomatch hp

theorem sorting_o4 : O4 sorting := o4_function sorting rfl

theorem sorting_o5_eq : O5 sorting .eq := by
  refine (o5_correct _ _).mpr fun u v hu hv => ?_
  have hu' := sorting_meets.mp ⟨hu.1, hu.2⟩
  have hv' := sorting_meets.mp ⟨hv.1, hv.2⟩
  funext l
  exact sorted_perm_unique (hu'.1 l) (hv'.1 l) (hu'.2 l) (hv'.2 l)

theorem sorting_progress :
    (∀ g ∈ o1 sorting, Nonempty g.1) ∧ O2 sorting ∧ O3 sorting ∧ O4 sorting ∧
      O5 sorting .widest :=
  progress sorting ((o2_correct _).mp sorting_o2).1 ((o2_correct _).mp sorting_o2).2
    ((o3_correct _).mp sorting_o3) trivial (fun _ h => nomatch h)

theorem degenerate_subjects :
    (degenerate (List Int → List Int)).map Degenerate.reading =
      [.subject nilSort, .subject fun l => l] := rfl

theorem sortedOnly_verdicts : Verdicts sortedOnly [true, false] := by
  show sortedOnly.Meets nilSort ∧ ¬ sortedOnly.Meets (fun l => l) ∧ True
  refine ⟨sortedOnly_meets_nilSort, fun h => ?_, trivial⟩
  exact absurd (List.rel_of_pairwise_cons (sortedOnly_meets.mp h [1, 0])
    (List.mem_singleton_self 0)) (by decide)

theorem sortedOnly_metBy : (metBy (List Int → List Int) [true, false]).map Degenerate.reading =
    [.subject nilSort] := rfl

theorem sortedOnly_possibilities :
    (possibilities sortedOnly_verdicts).map Consequence.holds = [fun f => f = nilSort] := rfl

theorem sorting_keeps_declined :
    ∀ x ∈ possibilities sortedOnly_verdicts, (Answer.mk x .declined).KeptBy sorting := by
  intro x hx
  rcases List.mem_singleton.mp hx with rfl
  exact (Degenerate.declined_keptBy_iff _ _).mpr sorting_refutes_nilSort

theorem sorting_verdicts : Verdicts sorting [false, false] := by
  show ¬ sorting.Meets nilSort ∧ ¬ sorting.Meets (fun l => l) ∧ True
  refine ⟨sorting_refutes_nilSort, fun h => ?_, trivial⟩
  exact absurd (List.rel_of_pairwise_cons ((sorting_meets.mp h).1 [1, 0])
    (List.mem_singleton_self 0)) (by decide)

theorem sorting_metBy_nil : metBy (List Int → List Int) [false, false] = [] := rfl

@[expose] def contraDom : IntentRecord (List Int → List Int) where
  shape := .function _ _
  dom := [⟨"impossible", fun _ => False⟩]
  props := [sortedClause]
  vocab := [sortedPred]

theorem contraDom_not_o2 : ¬ O2 contraDom := fun h =>
  let ⟨⟨_, hw⟩, _⟩ := (o2_correct _).mp h
  hw _ (List.mem_singleton.mpr rfl)

@[expose] def anything : IntentRecord (List Int → List Int) where
  shape := .function _ _
  dom := []
  props := [⟨"anything", fun _ => True⟩]
  vocab := []

theorem anything_not_o3 : ¬ O3 anything := fun h =>
  let ⟨_, hw⟩ := (o3_correct _).mp h _ (List.mem_singleton.mpr rfl)
  hw trivial

@[expose] def ImplSpec (f : List Int → List Int) : Prop := ∀ l, f l = l.mergeSort le

theorem implSpec_refines : Refines sorting (fun f => f) ImplSpec := by
  intro f hf _
  have hfs : f = sort := funext hf
  subst hfs
  exact sorting_meets_sort.2

theorem sort_fulfils : sorting.Fulfilled sort := fulfils implSpec_refines fun _ => rfl

@[expose] def listFunctionShape : Gloss where
  requires := "The subject is a function from lists of integers to lists of integers."
  rulesOut := "Any subject of another kind, such as a step of a system with state."
  allows := "Every function of that type, until the properties narrow it."
  freedom := "None of its own: the shape fixes only what kind of thing the subject is."

@[expose] def sortedGloss : Gloss where
  requires := "For every input list, the output is in ascending order: each element is at most \
    every element after it."
  rulesOut := "Any function that, for some input, returns a list with an element greater than \
    one after it."
  allows := "Any function whose outputs are all in ascending order, whatever they hold, \
    including one that ignores its input, such as the function returning the empty list."
  freedom := "On its own it leaves the output's elements free: two functions that meet it may \
    return different sorted lists for the same input."

@[expose] def permGloss : Gloss where
  requires := "For every input list, the output holds exactly the input's elements, each as many \
    times as the input does, in some order."
  rulesOut := "Any function that drops, adds or changes an element, such as the function \
    returning the empty list."
  allows := "Any rearrangement of the input, in ascending order or not."
  freedom := "On its own it leaves the order free: two functions that meet it may order the \
    same input differently."

@[expose] def sortedPredGloss : Gloss where
  requires := "Sorted holds of a list when each of its elements is at most every element after it."
  rulesOut := "A list with an element greater than one after it, such as [1, 0]."
  allows := "The empty list, any list of one element, and lists with repeated elements."
  freedom := "None: it is a definition, which fixes which lists it holds of."

@[expose] def permPredGloss : Gloss where
  requires := "Perm holds of a pair of lists when the first is a rearrangement of the second: \
    the same elements, each as many times."
  rulesOut := "A pair whose lists differ in some element or in how many times it occurs, such \
    as ([0], [])."
  allows := "A pair of equal lists, and a pair of lists in different orders."
  freedom := "None: it is a definition, which fixes which pairs it holds of."

@[expose] def sortedOnlyExplained : Explanation sortedOnly where
  shape := listFunctionShape
  dom := []
  props := [sortedGloss]
  vocab := [sortedPredGloss]
  restatement := .unconfirmed
  consequences := [
    { consequence := ⟨"returning the empty list for every input", .possibility,
        fun f => f = nilSort⟩
      holds := show ∃ f, sortedOnly.Meets f ∧ f = nilSort from
        ⟨nilSort, sortedOnly_meets_nilSort, rfl⟩
      gloss :=
        { requires := "Nothing of a function: it states that some function meeting the record \
            returns the empty list for every input."
          rulesOut := "Nothing: it states what the record allows, not a further demand."
          allows := "The function that returns the empty list for every input, beside a real \
            sort."
          freedom := "The record does not fix the output: a sort and the empty-list function \
            both meet it. An owner who wanted a sort declines this consequence." }
      settled := .answered (.owner (.of "richard")) .declined }]

@[expose] def sortingExplained : Explanation sorting where
  shape := listFunctionShape
  dom := []
  props := [sortedGloss, permGloss]
  vocab := [sortedPredGloss, permPredGloss]
  restatement := .confirmed (.of "richard")
  consequences := [
    { consequence := ⟨"is not the function returning the empty list for every input",
        .entailment, fun f => f ≠ nilSort⟩
      holds := show ∀ f, sorting.Meets f → f ≠ nilSort from
        fun f hf h => sorting_refutes_nilSort (h ▸ hf)
      gloss :=
        { requires := "That every function meeting the record differs from the function \
            returning the empty list for every input."
          rulesOut := "The function returning the empty list, whose output for [0] is not a \
            rearrangement of [0]."
          allows := "Every function that meets the record."
          freedom := "None that this consequence adds." }
      settled := .derived },
    { consequence := ⟨"is Lean's merge sort", .entailment, fun f => f = sort⟩
      holds := show ∀ f, sorting.Meets f → f = sort from
        fun f hf => sorting_o5_eq.relates hf sorting_meets_sort
      gloss :=
        { requires := "That every function meeting the record returns, for every input, the \
            same output as Lean's merge sort: the record fixes the function completely."
          rulesOut := "Every function other than the sort, among them any that orders some \
            input differently or drops an element."
          allows := "Exactly one function, the one returning the ascending rearrangement of its \
            input."
          freedom := "None: obligation O5 holds with equality." }
      settled := .answered (.onBehalf (.of "agent") (.of "assistant")
        "The owner confirmed that the output is an ascending rearrangement of the input, which \
          leaves one such function.") .confirmed }]

end LeanIntentExamples.Sorting
