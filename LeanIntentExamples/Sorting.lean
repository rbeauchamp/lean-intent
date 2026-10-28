import LeanIntent

/-!
# A sorting function whose rearrangement property is forgotten

An owner asks for a function that sorts lists of integers into ascending order. The intent record
first written, `sortedOnly`, has one property, that every output is sorted, and forgets that the
output must be a rearrangement of the input. Before any code exists the obligations expose the
omission: the function returning the empty list meets `sortedOnly` beside a real sort, so
`sortedOnly` fails O5 with equality (`sortedOnly_not_o5_eq`), and any freedom that meets O5 relates
the sort to the empty-list function (`sortedOnly_o5_rel`), which is the freedom the owner would be
shown and decline. Only the widest freedom meets it (`sortedOnly_o5_widest`).

The corrected record, `sorting`, adds the rearrangement property. It meets O1 to O5, O5 with
equality since a sorted rearrangement of a list is unique, and it refutes the empty-list function
(`sorting_refutes_nilSort`), and it meets the premises of `progress` (`sorting_progress`). An
implementation specified by `ImplSpec` refines it, so the implementation `sort` fulfils the intent
by the refinement link (`sort_fulfils`).

The degenerate check finds the same omission from the subject's type alone: the degenerate subjects
of `List Int → List Int` are the function returning the empty list and the identity
(`degenerate_subjects`), the first meets `sortedOnly` and is reported as a possibility for the owner
(`sortedOnly_verdicts`, `sortedOnly_possibilities`), and neither meets `sorting`
(`sorting_verdicts`).

The obligations also refuse in the other direction: a record under a contradictory domain
hypothesis fails O2 (`contraDom_not_o2`), and a record whose property nothing fails fails O3
(`anything_not_o3`).
-/

namespace LeanIntentExamples.Sorting

open LeanIntent

/-- A list is in ascending order. -/
def Sorted (l : List Int) : Prop := l.Pairwise (· ≤ ·)

/-- Every output is in ascending order. -/
def sortedClause : Clause (List Int → List Int) := ⟨"sorted", fun f => ∀ l, Sorted (f l)⟩

/-- Every output is a rearrangement of its input. -/
def permClause : Clause (List Int → List Int) := ⟨"rearranges", fun f => ∀ l, (f l).Perm l⟩

/-- The vocabulary predicate `Sorted`. -/
def sortedPred : Pred := ⟨"Sorted", List Int, Sorted⟩

/-- The vocabulary predicate `Perm`, over pairs of lists. -/
def permPred : Pred := ⟨"Perm", List Int × List Int, fun p => p.1.Perm p.2⟩

/-- The record as first written: it forgets the rearrangement property. -/
def sortedOnly : IntentRecord (List Int → List Int) where
  shape := .function _ _
  dom := []
  props := [sortedClause]
  vocab := [sortedPred]

/-- The corrected record. -/
def sorting : IntentRecord (List Int → List Int) where
  shape := .function _ _
  dom := []
  props := [sortedClause, permClause]
  vocab := [sortedPred, permPred]

/-- The comparison the implementation sorts by. -/
def le (a b : Int) : Bool := decide (a ≤ b)

/-- An implementation: Lean's merge sort. -/
def sort (l : List Int) : List Int := l.mergeSort le

/-- The degenerate implementation that returns the empty list for every input. -/
def nilSort (_ : List Int) : List Int := []

theorem sort_sorted (l : List Int) : Sorted (sort l) :=
  (List.pairwise_mergeSort (le := le)
    (fun a b c hab hbc => by simp only [le, decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [le, Bool.or_eq_true, decide_eq_true_eq]; omega) l).imp
    (fun h => by simpa [le] using h)

theorem sort_perm (l : List Int) : (sort l).Perm l := List.mergeSort_perm _ _

/-- A sorted rearrangement of a list is unique. -/
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

/-! ## The record that forgets the rearrangement property -/

theorem sortedOnly_meets_nilSort : sortedOnly.Meets nilSort :=
  sortedOnly_meets.mpr fun _ => List.Pairwise.nil

theorem sortedOnly_meets_sort : sortedOnly.Meets sort :=
  sortedOnly_meets.mpr sort_sorted

/-- The record without the rearrangement property fails O5 with equality: the sort and the
function returning the empty list both meet it. -/
theorem sortedOnly_not_o5_eq : ¬ O5 sortedOnly .eq :=
  not_o5_eq sortedOnly_meets_sort sortedOnly_meets_nilSort sort_ne_nilSort

/-- Every freedom with which it meets O5 relates the sort to the empty-list function: that is the
freedom the owner is shown, and declines. -/
theorem sortedOnly_o5_rel (R : (List Int → List Int) → (List Int → List Int) → Prop)
    (h : O5 sortedOnly (.rel R)) : R sort nilSort :=
  h.relates sortedOnly_meets_sort sortedOnly_meets_nilSort

/-- It meets O5 only with a freedom that wide, such as the widest. -/
theorem sortedOnly_o5_widest : O5 sortedOnly .widest := o5_widest _

/-! ## The corrected record -/

theorem sorting_meets_sort : sorting.Meets sort :=
  sorting_meets.mpr ⟨sort_sorted, sort_perm⟩

/-- The corrected record refutes the empty-list function. -/
theorem sorting_refutes_nilSort : ¬ sorting.Meets nilSort := fun h =>
  absurd ((sorting_meets.mp h).2 [0]).length_eq (by simp [nilSort])

/-- O1's goals are the record's four statements with their types. -/
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

/-- The corrected record fixes the result completely: it meets O5 with equality. -/
theorem sorting_o5_eq : O5 sorting .eq := by
  refine (o5_correct _ _).mpr fun u v hu hv => ?_
  have hu' := sorting_meets.mp ⟨hu.1, hu.2⟩
  have hv' := sorting_meets.mp ⟨hv.1, hv.2⟩
  funext l
  exact sorted_perm_unique (hu'.1 l) (hv'.1 l) (hu'.2 l) (hv'.2 l)

/-- The corrected record meets the premises of `progress`, which passes it through O1 to O5. -/
theorem sorting_progress :
    (∀ g ∈ o1 sorting, Nonempty g.1) ∧ O2 sorting ∧ O3 sorting ∧ O4 sorting ∧
      O5 sorting .widest :=
  progress sorting ((o2_correct _).mp sorting_o2).1 ((o2_correct _).mp sorting_o2).2
    ((o3_correct _).mp sorting_o3) (fun _ h => nomatch h)

/-! ## The degenerate subjects -/

/-- The degenerate subjects of a function from lists of integers to lists of integers: the function
returning the empty list, since lists are infinitely many and the class takes a list constant only
at the empty list, and the identity, the one projection. -/
theorem degenerate_subjects :
    (degenerate (List Int → List Int)).map Degenerate.subject = [nilSort, fun l => l] := rfl

/-- The record that forgets the rearrangement property is met by the function returning the empty
list and not by the identity. -/
theorem sortedOnly_verdicts : Verdicts sortedOnly [true, false] := by
  show sortedOnly.Meets nilSort ∧ ¬ sortedOnly.Meets (fun l => l) ∧ True
  refine ⟨sortedOnly_meets_nilSort, fun h => ?_, trivial⟩
  exact absurd (List.rel_of_pairwise_cons (sortedOnly_meets.mp h [1, 0])
    (List.mem_singleton_self 0)) (by decide)

/-- So the check reports the function returning the empty list, as the possibility the owner is
shown: "your specification allows returning the empty list for every input". -/
theorem sortedOnly_metBy : (metBy (List Int → List Int) [true, false]).map Degenerate.subject =
    [nilSort] := rfl

theorem sortedOnly_possibilities :
    (possibilities sortedOnly_verdicts).map Possibility.holds = [fun f => f = nilSort] :=
  possibilities_holds sortedOnly_verdicts

/-- The corrected record is met by neither, so the check reports nothing. -/
theorem sorting_verdicts : Verdicts sorting [false, false] := by
  show ¬ sorting.Meets nilSort ∧ ¬ sorting.Meets (fun l => l) ∧ True
  refine ⟨sorting_refutes_nilSort, fun h => ?_, trivial⟩
  exact absurd (List.rel_of_pairwise_cons ((sorting_meets.mp h).1 [1, 0])
    (List.mem_singleton_self 0)) (by decide)

theorem sorting_metBy_nil : metBy (List Int → List Int) [false, false] = [] := rfl

/-! ## Records the obligations refuse -/

/-- The record under a domain hypothesis nothing satisfies. -/
def contraDom : IntentRecord (List Int → List Int) where
  shape := .function _ _
  dom := [⟨"impossible", fun _ => False⟩]
  props := [sortedClause]
  vocab := [sortedPred]

/-- A contradictory domain hypothesis fails O2, so the record cannot be met vacuously. -/
theorem contraDom_not_o2 : ¬ O2 contraDom := fun h =>
  let ⟨⟨_, hw⟩, _⟩ := (o2_correct _).mp h
  hw _ (List.mem_singleton.mpr rfl)

/-- The record whose one property every function meets. -/
def anything : IntentRecord (List Int → List Int) where
  shape := .function _ _
  dom := []
  props := [⟨"anything", fun _ => True⟩]
  vocab := []

/-- A property that nothing fails fails O3. -/
theorem anything_not_o3 : ¬ O3 anything := fun h =>
  let ⟨_, hw⟩ := (o3_correct _).mp h _ (List.mem_singleton.mpr rfl)
  hw trivial

/-! ## The chain to an implementation -/

/-- The implementation's specification, which states its code; below the intent record that is
harmless, since the link to the record is proved. -/
def ImplSpec (f : List Int → List Int) : Prop := ∀ l, f l = l.mergeSort le

theorem implSpec_refines : Refines sorting (fun f => f) ImplSpec := by
  intro f hf _
  have hfs : f = sort := funext hf
  subst hfs
  exact sorting_meets_sort.2

/-- The implementation fulfils the intent, by the refinement link. -/
theorem sort_fulfils : sorting.Fulfilled sort := fulfils implSpec_refines fun _ => rfl

end LeanIntentExamples.Sorting
