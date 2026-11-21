module

public import LeanIntent.Progress

public section

namespace LeanIntent

universe u v

abbrev Family (P : Sort v) (W : P → Type u) := (p : P) → IntentRecord (W p)

namespace Family

variable {P : Sort v} {W : P → Type u}

@[expose] def HoldsWhere (r : Family P W) (Good : P → Prop) (O : (p : P) → IntentRecord (W p) → Prop) : Prop :=
  ∀ p, Good p → O p (r p)

theorem HoldsWhere.at {r : Family P W} {Good : P → Prop} {O : (p : P) → IntentRecord (W p) → Prop}
    (h : HoldsWhere r Good O) {p : P} (hp : Good p) : O p (r p) := h p hp

theorem not_holdsWhere_of_at {r : Family P W} {Good : P → Prop}
    {O : (p : P) → IntentRecord (W p) → Prop} {p : P} (hp : Good p) (hn : ¬ O p (r p)) :
    ¬ HoldsWhere r Good O := fun h => hn (h p hp)

theorem exists_of_at {r : Family P W} {O : (p : P) → IntentRecord (W p) → Prop} {p : P}
    (h : O p (r p)) : ∃ p, O p (r p) := ⟨p, h⟩

theorem holdsWhere_of_empty (r : Family P W) {Good : P → Prop}
    (O : (p : P) → IntentRecord (W p) → Prop) (hg : ∀ p, ¬ Good p) : HoldsWhere r Good O :=
  fun p hp => absurd hp (hg p)

theorem not_vacuous {Good : P → Prop} {p : P} (hp : Good p) : ¬ ∀ p, ¬ Good p :=
  fun h => h p hp

theorem o2Run_along {r : Family P W} {p q : P} (φ : W p → W q)
    (hφ : ∀ w, (r p).Meets w → (r q).Meets (φ w)) (h : O2Run (r p)) : O2Run (r q) := by
  obtain ⟨w, hw⟩ := (goals_singleton _).mp h
  exact (goals_singleton _).mpr ⟨φ w, hφ w hw⟩

@[expose] def inhabitedRecord (A T : Type) (shape : Shape T) : IntentRecord T where
  shape := shape
  dom := []
  props := [⟨"the parameter has a value", fun _ => Nonempty A⟩]
  vocab := []

@[expose] def inhabitedValue : Family Type (fun _ => Unit) := fun A => inhabitedRecord A Unit (.value _)

@[expose] def inhabitedStep : Family Type (fun _ => Bool → Bool) := fun A => inhabitedRecord A _ (.step Bool)

@[expose] def inhabitedDom : Family Type (fun _ => Unit) := fun A =>
  ⟨.value _, [⟨"the parameter has a value", fun _ => Nonempty A⟩], [], []⟩

theorem not_generic :
    (O2 (inhabitedDom Unit) ∧ ¬ O2 (inhabitedDom Empty)) ∧
    (O2Run (inhabitedValue Unit) ∧ ¬ O2Run (inhabitedValue Empty)) ∧
    (O3 (inhabitedValue Empty) ∧ ¬ O3 (inhabitedValue Unit)) ∧
    (O4 (inhabitedStep Empty) ∧ ¬ O4 (inhabitedStep Unit)) ∧
    (O5 (inhabitedStep Empty) .eq ∧ ¬ O5 (inhabitedStep Unit) .eq) := by
  have none : ¬ Nonempty Empty := fun ⟨e⟩ => nomatch e
  have noMeet {T : Type} {s : Shape T} {w : T} : ¬ (inhabitedRecord Empty T s).Meets w :=
    fun h => none (h.2 _ (List.mem_singleton_self _))
  have meet {T : Type} {s : Shape T} {w : T} : (inhabitedRecord Unit T s).Meets w :=
    ⟨(fun _ hd => nomatch hd), fun p hp => by
      simp only [inhabitedRecord, List.mem_singleton] at hp
      subst hp
      exact ⟨()⟩⟩
  refine ⟨⟨(o2_correct _).mpr ⟨⟨(), fun d hd => ?_⟩, fun _ hp => nomatch hp⟩, fun h => ?_⟩,
    ⟨o2Run_of_meets (w := ()) meet, fun h => ?_⟩, ⟨(o3_correct _).mpr fun p hp => ?_, fun h => ?_⟩,
    ⟨?_, fun h => ?_⟩, ⟨?_, fun h => ?_⟩⟩
  · simp only [inhabitedDom, List.mem_singleton] at hd
    subst hd
    exact ⟨()⟩
  · obtain ⟨⟨w, hw⟩, -⟩ := (o2_correct _).mp h
    exact none (hw _ (List.mem_singleton_self _))
  · obtain ⟨w, hw⟩ := (goals_singleton _).mp h
    exact noMeet hw
  · simp only [inhabitedValue, inhabitedRecord, List.mem_singleton] at hp
    subst hp
    exact ⟨(), none⟩
  · obtain ⟨w, hw⟩ := (o3_correct _).mp h _ (List.mem_singleton_self _)
    exact hw ⟨()⟩
  · exact (goals_singleton _).mpr fun _ _ hm => noMeet hm
  · exact not_o4_of_idle (r := inhabitedStep Unit) (w := fun s => s) (fun _ => rfl) meet h
  · exact (goals_singleton _).mpr fun _ _ hu => absurd hu noMeet
  · exact not_o5_eq (u := fun s => s) (v := fun s => !s) meet meet
      (fun he => absurd (congrFun he true) (by decide)) h

end Family

end LeanIntent
