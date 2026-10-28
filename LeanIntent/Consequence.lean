import LeanIntent.Record

/-!
# Consequences shown to the owner

The owner never reads an intent record's properties; they read its consequences, checked facts
about the record shown in plain words, and confirm or decline each. A consequence is of one of two
kinds: an *entailment*, a predicate on the subject that every model of the record meets, or a
*possibility*, a predicate on the subject that some model of the record meets, which the owner reads
as "your specification allows this".

This module defines the possibility, the kind the degenerate check reports (`LeanIntent.Degenerate`):
a predicate on the subject together with a model of the record that meets it. A degenerate subject
that meets the record is the possibility that the subject is that degenerate subject
(`Possibility.ofModel`). A possibility the owner declines is to be kept as a refutation that every
later revision of the record must carry, a proof that no model of the revision meets the predicate;
for `ofModel w`, that the revision is not met by `w`. Keeping each verdict across revisions,
rendering a consequence in plain words and recording the owner's verdict are separate issues of this
repository (lean-intent #3, #4 and #5).
-/

namespace LeanIntent

universe u

variable {W : Type u}

/-- A possibility of the record `r`: a predicate on its subject that a model of `r` meets. -/
structure Possibility (r : IntentRecord W) where
  /-- The predicate the owner is shown as allowed. -/
  holds : W → Prop
  /-- A model of the record that meets it. -/
  model : ∃ w, r.Meets w ∧ holds w

/-- The possibility that the subject is `w`, a model of `r`. -/
def Possibility.ofModel {r : IntentRecord W} (w : W) (h : r.Meets w) : Possibility r :=
  ⟨fun v => v = w, w, h, rfl⟩

end LeanIntent
