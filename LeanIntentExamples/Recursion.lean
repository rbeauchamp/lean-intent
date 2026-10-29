import LeanIntent.Explain

/-!
# A record whose meaning reaches definitions by recursion and a `let`

The subject computes a check digit for a list of numbers, of type `List Nat → Nat`. The record
`checkDigits` asks that it return, for every list, the last decimal digit of the sum of the digit
sums of its numbers, as `checkDigit` computes it. The record fixes the function completely
(`checkDigits_o5_eq`), and every function that meets it returns a single digit, the consequence its
explanation shows the owner (`checkDigitsExplained`).

Its meaning reaches three definitions of this file, which its rendering prints in two ways:
`digitSum`, by well-founded recursion, and `total`, by structural recursion, each by its type and
the equation Lean proves for it, which determines it, since Lean compiles a definition by recursion
into a value its syntax cannot write; and `checkDigit`, whose value holds a `let`, by that value.
With `LeanIntent.Render` imported,

    #render_intent LeanIntentExamples.Recursion.checkDigitsExplained

shows the rendering.
-/

namespace LeanIntentExamples.Recursion

open LeanIntent

/-- The sum of the decimal digits of a number, by well-founded recursion on the number. -/
def digitSum (n : Nat) : Nat :=
  if n < 10 then n else n % 10 + digitSum (n / 10)
termination_by n
decreasing_by omega

/-- The sum of a list of numbers, by structural recursion on the list. -/
def total : List Nat → Nat
  | [] => 0
  | a :: as => a + total as

/-- The check digit of a list of numbers: the last decimal digit of the sum of their digit sums. -/
def checkDigit (l : List Nat) : Nat :=
  let s := total (l.map digitSum)
  s % 10

/-- The subject returns the check digit of every list. -/
def checkClause : Clause (List Nat → Nat) :=
  ⟨"computes the check digit", fun f => ∀ l, f l = checkDigit l⟩

/-- The record. -/
def checkDigits : IntentRecord (List Nat → Nat) where
  shape := .function _ _
  dom := []
  props := [checkClause]
  vocab := []

/-- The record fixes the function completely: it meets O5 with equality. -/
theorem checkDigits_o5_eq : O5 checkDigits .eq := by
  refine (o5_correct _ _).mpr fun u v hu hv => ?_
  funext l
  exact (hu.2 _ (List.mem_singleton_self _) l).trans (hv.2 _ (List.mem_singleton_self _) l).symm

/-- Every function that meets the record returns a single digit. -/
theorem checkDigits_lt_ten (f : List Nat → Nat) (hf : checkDigits.Meets f) (l : List Nat) :
    f l < 10 := by
  rw [hf.2 _ (List.mem_singleton_self _) l]
  exact Nat.mod_lt _ (by decide)

/-! ## The explanation for the owner -/

/-- The explanation of `checkDigits`: its shape and its property in plain words, and the
consequence that every function meeting it returns a single digit. -/
def checkDigitsExplained : Explanation checkDigits where
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
  consequences := [
    { consequence := ⟨"returns a single digit", .entailment, fun f => ∀ l, f l < 10⟩
      holds := show ∀ f, checkDigits.Meets f → ∀ l, f l < 10 from checkDigits_lt_ten
      gloss :=
        { requires := "That every function meeting the record returns a number below ten for \
            every list."
          rulesOut := "Any function that returns ten or more for some list."
          allows := "Every function that meets the record."
          freedom := "None that this consequence adds." } }]

end LeanIntentExamples.Recursion
