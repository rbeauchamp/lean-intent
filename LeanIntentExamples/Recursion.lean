module

public import LeanIntent.Explain

public section

namespace LeanIntentExamples.Recursion

open LeanIntent

@[expose] def digitSum (n : Nat) : Nat :=
  if n < 10 then n else n % 10 + digitSum (n / 10)
termination_by n
decreasing_by omega

@[expose] def total : List Nat → Nat
  | [] => 0
  | a :: as => a + total as

@[expose] def checkDigit (l : List Nat) : Nat :=
  let s := total (l.map digitSum)
  s % 10

@[expose] def checkClause : Clause (List Nat → Nat) :=
  ⟨"computes the check digit", fun f => ∀ l, f l = checkDigit l⟩

@[expose] def checkDigits : IntentRecord (List Nat → Nat) where
  shape := .function _ _
  dom := []
  props := [checkClause]
  vocab := []

theorem checkDigits_o5_eq : O5 checkDigits .eq := by
  refine (o5_correct _ _).mpr fun u v hu hv => ?_
  funext l
  exact (hu.2 _ (List.mem_singleton_self _) l).trans (hv.2 _ (List.mem_singleton_self _) l).symm

theorem checkDigits_lt_ten (f : List Nat → Nat) (hf : checkDigits.Meets f) (l : List Nat) :
    f l < 10 := by
  rw [hf.2 _ (List.mem_singleton_self _) l]
  exact Nat.mod_lt _ (by decide)

@[expose] def checkDigitsExplained : Explanation checkDigits where
  shape :=
    { requires := "The subject is a function from lists of natural numbers to natural numbers."
      rulesOut := "Any subject of another kind, such as a step of a system with state."
      allows := "Every function of that type, until the property narrows it."
      freedom := "None of its own: the shape fixes only what kind of thing the subject is." }
  dom := []
  props := [
    { requires := "For every list, the output is the list's check digit: the last decimal digit \
        of the sum, over the list's numbers, of the sum of each number's decimal digits."
      rulesOut := "Any function that returns another number for some list, such as one that \
        sums the numbers themselves rather than their digits."
      allows := "Exactly one function."
      freedom := "None: obligation O5 holds with equality." }]
  vocab := []
  restatement := .unconfirmed
  consequences := [
    { consequence := ⟨"returns a single digit", .entailment, fun f => ∀ l, f l < 10⟩
      holds := show ∀ f, checkDigits.Meets f → ∀ l, f l < 10 from checkDigits_lt_ten
      gloss :=
        { requires := "That every function meeting the record returns a number below ten for \
            every list."
          rulesOut := "Any function that returns ten or more for some list."
          allows := "Every function that meets the record."
          freedom := "None that this consequence adds." }
      settled := .unsettled }]

end LeanIntentExamples.Recursion
