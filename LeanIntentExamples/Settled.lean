import LeanIntent.Settled

/-!
# What is printed about who settled each thing

The words of each status, in Lean's kernel: the owner's own answer, a decision made on the owner's
behalf, a consequence derived from the restatement the owner confirmed, a fork left to the owner and
a consequence nothing settled, with the words for a restatement confirmed and for one that is not.
A record whose restatement no owner confirmed cannot hold a derived consequence: `.derived` has no
type there, so writing it at `Settled .unconfirmed` fails to elaborate. `Authority.answerer` reads
the same answerer from the author of a statement of the owners' log.
-/

namespace LeanIntentExamples.Settled

open LeanIntent

/-- The owner, by name. -/
def richard : Ident := .of "richard"

/-- The delegate, by name, and its delegation. -/
def claude : Ident := .of "claude"
def assistant : Ident := .of "assistant"

theorem owner_confirmed :
    (Settled.answered (s := .unconfirmed) (.owner richard) .confirmed).words =
      chars!"Confirmed by the owner richard.\n" := by
  decide +kernel

theorem on_behalf_confirmed :
    (Settled.answered (s := .unconfirmed) (.onBehalf claude assistant "It follows.") .confirmed).words =
      chars!"Confirmed on the owner's behalf by claude, under the delegation assistant, for this reason: It follows.\n" := by
  decide +kernel

/-- A reason that claims the owner confirmed stays a reason: the words open with who answered. -/
theorem reason_claims_owner :
    ¬ Settled.Claim.ownerConfirmed.phrase <+:
      (Settled.answered (s := .unconfirmed)
        (.onBehalf claude assistant "Confirmed by the owner richard.") .confirmed).words :=
  (Settled.onBehalf_not_owners claude assistant _ .confirmed).1

theorem derived_words :
    (Settled.derived (owner := richard)).words =
      chars!"Derived from what the owner confirmed: it holds of the record as shown, and the owner richard confirmed the record's restatement; no one answered it.\n" := by
  decide +kernel

theorem fork_words :
    (Settled.fork (s := .unconfirmed)).words =
      chars!"A fork for the owner to decide: their intent does not settle it, and no answer is recorded.\n" := by
  decide +kernel

theorem unsettled_words :
    (Settled.unsettled (s := .unconfirmed)).words =
      chars!"Not settled: no answer is recorded, and nothing records that it follows from what the owner confirmed.\n" := by
  decide +kernel

theorem unconfirmed_words :
    Restatement.unconfirmed.words = chars!"No confirmation by an owner is recorded.\n" := by
  decide +kernel

theorem confirmed_words :
    (Restatement.confirmed richard).words = chars!"Confirmed by the owner richard.\n" := by
  decide +kernel

/-- The owners' log and these words name the same answerer. -/
theorem authority_owner : (Authority.mk richard none).answerer "" = .owner richard := rfl

theorem authority_delegate :
    (Authority.mk claude (some assistant)).answerer "It follows." =
      .onBehalf claude assistant "It follows." := rfl

end LeanIntentExamples.Settled
