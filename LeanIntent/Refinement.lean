module

public import LeanIntent.Progress

public section

namespace LeanIntent

universe u v w

variable {W : Type u} {A : Sort v} {C : Sort w}

@[expose] def Refines (r : IntentRecord W) (m : A → W) (S : A → Prop) : Prop :=
  ∀ a, S a → r.Dom (m a) → r.Props (m a)

@[expose] def RefinesSpec (r : IntentRecord W) (m : A → W) (S : A → Prop) (n : C → A) (L : C → Prop) :
    Prop :=
  ∀ c, L c → r.Dom (m (n c)) → S (n c)

theorem fulfils {r : IntentRecord W} {m : A → W} {S : A → Prop} (hR : Refines r m S) {impl : A}
    (hS : S impl) : r.Fulfilled (m impl) :=
  hR impl hS

theorem Refines.meets {r : IntentRecord W} {m : A → W} {S : A → Prop} (hR : Refines r m S)
    {impl : A} (hS : S impl) (hd : r.Dom (m impl)) : r.Meets (m impl) :=
  ⟨hd, hR impl hS hd⟩

theorem Refines.comp {r : IntentRecord W} {m : A → W} {S : A → Prop} {n : C → A} {L : C → Prop}
    (hS : Refines r m S) (hL : RefinesSpec r m S n L) : Refines r (fun c => m (n c)) L :=
  fun c hc hd => hS (n c) (hL c hc hd) hd

theorem refines_id_iff {r : IntentRecord W} {S : W → Prop} :
    Refines r (fun w => w) S ↔ ∀ w, S w → r.Fulfilled w :=
  Iff.rfl

theorem refines_self (r : IntentRecord W) : Refines r (fun w => w) r.Props :=
  fun _ h _ => h

theorem Refines.determinate {r : IntentRecord W} {m : A → W} {S : A → Prop} (hR : Refines r m S)
    {R : Freedom W} (h5 : O5 r R) {a b : A} (ha : S a) (hb : S b) (hda : r.Dom (m a))
    (hdb : r.Dom (m b)) : R.relates r (m a) (m b) :=
  h5.relates ⟨hda, hR a ha hda⟩ ⟨hdb, hR b hb hdb⟩

theorem Refines.refutes {r : IntentRecord W} {m : A → W} {S : A → Prop} (hR : Refines r m S)
    {a : A} (hd : r.Dom (m a)) (hp : ¬ r.Props (m a)) : ¬ S a :=
  fun hs => hp (hR a hs hd)

theorem Refines.o2Run {r : IntentRecord W} {m : A → W} {S : A → Prop} (hR : Refines r m S)
    {impl : A} (hS : S impl) (hd : r.Dom (m impl)) : O2Run r :=
  o2Run_of_meets ⟨hd, hR impl hS hd⟩

end LeanIntent
