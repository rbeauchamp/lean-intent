module

public import LeanIntent.Pairs

public section

namespace LeanIntentExamples.Pairs

open LeanIntent

structure World where
  sight : Bool
  need : Bool

abbrev Agent := Bool → Bool

@[expose] def Reaches (a : Agent) (v : World) : Prop := a v.sight = v.need

@[expose] def Legible (v : World) : Prop := v.need = v.sight

@[expose] def Blind (a : Agent) : Prop := ∀ s t, a s = a t

@[expose] def reachesLegible : Clause Agent :=
  ⟨"reaches the goal of every legible world", fun a => ∀ v, Legible v → Reaches a v⟩

@[expose] def agent : IntentRecord Agent where
  shape := .function _ _
  dom := []
  props := [reachesLegible]
  vocab := [⟨"Legible", World, Legible⟩, ⟨"Reaches", Agent × World, fun p => Reaches p.1 p.2⟩]

@[expose] def perWorld : Pair Agent := ⟨World, Legible, fun v a => Reaches a v⟩

theorem perWorld_pairOf : agent.PairOf reachesLegible perWorld :=
  ⟨List.mem_singleton_self _, fun _ =>
    ⟨fun h v hv => h (fun _ hd => nomatch hd) v hv, fun h _ => h⟩⟩

theorem perWorld_blind : OPair perWorld Blind :=
  oPair_of ⟨⟨true, true⟩, rfl⟩ fun v _ =>
    ⟨fun _ => v.need, fun _ _ => rfl, rfl⟩

theorem legible_differ (a : Agent) (h : reachesLegible.holds a) : ¬ Blind a := fun hb => by
  have ht : a true = true := h ⟨true, true⟩ rfl
  have hf : a false = false := h ⟨false, false⟩ rfl
  rw [hb true false, hf] at ht
  exact Bool.false_ne_true ht

theorem whole_not_blind : ¬ OPair (Pair.whole agent reachesLegible) Blind := fun h => by
  obtain ⟨a, hb, hf⟩ := (oPair_whole_iff _ _ _).mp h
  exact legible_differ a (hf fun _ hd => nomatch hd) hb

theorem whole_any : OPair (Pair.whole agent reachesLegible) fun _ => True :=
  (oPair_whole_iff agent reachesLegible _).mpr ⟨fun s => s, trivial, fun _ _ hv => hv.symm⟩

theorem perWorld_not_whole :
    OPair perWorld Blind ∧ ¬ OPair (Pair.whole agent reachesLegible) Blind :=
  ⟨perWorld_blind, whole_not_blind⟩

theorem any_not_blind :
    OPair (Pair.whole agent reachesLegible) (fun _ => True) ∧
      ¬ OPair (Pair.whole agent reachesLegible) Blind :=
  ⟨whole_any, whole_not_blind⟩

@[expose] def reachesEvery : Clause Agent := ⟨"reaches the goal of every world", fun a => ∀ v, Reaches a v⟩

@[expose] def every : IntentRecord Agent where
  shape := .function _ _
  dom := []
  props := [reachesEvery]
  vocab := [⟨"Reaches", Agent × World, fun p => Reaches p.1 p.2⟩]

theorem seenAlike (a : Agent) : ¬ (Reaches a ⟨true, true⟩ ∧ Reaches a ⟨true, false⟩) :=
  fun ⟨ht, hf⟩ => Bool.false_ne_true (hf.symm.trans ht)

theorem every_not_oPair (C : Agent → Prop) : ¬ OPair (Pair.whole every reachesEvery) C :=
  not_oPair_of_unserved (x := PUnit.unit) trivial fun a _ h =>
    seenAlike a ⟨h (fun _ hd => nomatch hd) _, h (fun _ hd => nomatch hd) _⟩

@[expose] def everyPerWorld : Pair Agent := ⟨World, fun _ => True, fun v a => Reaches a v⟩

theorem everyPerWorld_blind : OPair everyPerWorld Blind :=
  oPair_of ⟨⟨true, true⟩, trivial⟩ fun v _ =>
    ⟨fun _ => v.need, fun _ _ => rfl, rfl⟩

end LeanIntentExamples.Pairs
