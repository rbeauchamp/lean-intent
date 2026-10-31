import LeanIntent.Progress

/-!
# Records generic in a world's types, and what an instance of one establishes

A record may be generic: a family of records, one for each value of its parameters, such as the types
a world is made of (`Family`). Checking or rendering such a record at representative parameters is
often what a project can afford, and an obligation of a generic record is usually proved only of
parameters with some witnesses (such as an action, different sights, energy amounts in order).

This module fixes what an instance says about the family, for every obligation, stated as a predicate
`O` on the record of each parameter, so that it holds of O2, O2 before running, O3, O4 and O5 alike:

* What is at an instance is the family's: `r p` is the family applied to `p`, so its statements are the
  family's with the parameters replaced, by the definition of application.
* The generic claim is `Family.HoldsWhere r Good O`: the obligation holds at every parameter that
  meets `Good`, the condition the obligation's witnesses state. It gives the obligation at each such
  instance (`Family.HoldsWhere.at`).
* A failure at an instance meeting `Good` refutes the generic claim (`Family.not_holdsWhere_of_at`).
* An instance alone establishes only that some parameter has the obligation
  (`Family.exists_of_at`), and that a generic claim is not vacuous when the instance meets `Good`
  (`Family.not_vacuous`), which a `Good` that no parameter meets would make it
  (`Family.holdsWhere_of_empty`).
* It does not establish the generic claim. `Family.not_generic` proves this for each obligation by a
  family whose obligation holds at one parameter and fails at another; only `Good` that holds of
  exactly that instance would make it enough, and a transfer along a map of models
  (`Family.o2Run_along`) is what carries a model of one instance to another parameter.

So a representative instance is a check that can find a counterexample and a reading aid, and alone
not in general a proof of the generic record.
-/

namespace LeanIntent

universe u v

/-- A record generic in its parameters, of type `P`: one record for each, about subjects of a type
that may depend on the parameter. -/
abbrev Family (P : Sort v) (W : P → Type u) := (p : P) → IntentRecord (W p)

namespace Family

variable {P : Sort v} {W : P → Type u}

/-- The generic claim for the obligation `O`: it holds of the record at every parameter that meets
`Good`. -/
def HoldsWhere (r : Family P W) (Good : P → Prop) (O : (p : P) → IntentRecord (W p) → Prop) : Prop :=
  ∀ p, Good p → O p (r p)

/-- The generic claim gives the obligation at every instance meeting its condition. -/
theorem HoldsWhere.at {r : Family P W} {Good : P → Prop} {O : (p : P) → IntentRecord (W p) → Prop}
    (h : HoldsWhere r Good O) {p : P} (hp : Good p) : O p (r p) := h p hp

/-- A failure at an instance meeting the condition refutes the generic claim: a representative
instance can find a counterexample. -/
theorem not_holdsWhere_of_at {r : Family P W} {Good : P → Prop}
    {O : (p : P) → IntentRecord (W p) → Prop} {p : P} (hp : Good p) (hn : ¬ O p (r p)) :
    ¬ HoldsWhere r Good O := fun h => hn (h p hp)

/-- The obligation at an instance establishes that some parameter has it, and nothing about any
other. -/
theorem exists_of_at {r : Family P W} {O : (p : P) → IntentRecord (W p) → Prop} {p : P}
    (h : O p (r p)) : ∃ p, O p (r p) := ⟨p, h⟩

/-- A condition no parameter meets makes the generic claim hold whatever the obligation, even one
nothing can meet: witness hypotheses that contradict each other prove nothing. -/
theorem holdsWhere_of_empty (r : Family P W) {Good : P → Prop}
    (O : (p : P) → IntentRecord (W p) → Prop) (hg : ∀ p, ¬ Good p) : HoldsWhere r Good O :=
  fun p hp => absurd hp (hg p)

/-- An instance meeting the condition shows that the condition can be met, so a generic claim under
it is not vacuous in the way `holdsWhere_of_empty` allows. -/
theorem not_vacuous {Good : P → Prop} {p : P} (hp : Good p) : ¬ ∀ p, ¬ Good p :=
  fun h => h p hp

/-- A model of one instance gives a model at another parameter along a map that keeps meeting the
record. This, and not the instance alone, is what carries a model across parameters. -/
theorem o2Run_along {r : Family P W} {p q : P} (φ : W p → W q)
    (hφ : ∀ w, (r p).Meets w → (r q).Meets (φ w)) (h : O2Run (r p)) : O2Run (r q) := by
  obtain ⟨w, hw⟩ := (goals_singleton _).mp h
  exact (goals_singleton _).mpr ⟨φ w, hφ w hw⟩

/-! ## An instance does not establish the generic claim -/

/-- A record that asks of a subject of type `T` that a type `A` has a value. -/
def inhabitedRecord (A T : Type) (shape : Shape T) : IntentRecord T where
  shape := shape
  dom := []
  props := [⟨"the parameter has a value", fun _ => Nonempty A⟩]
  vocab := []

/-- The family over types of `inhabitedRecord`, about a subject of the plain value `Unit`. -/
def inhabitedValue : Family Type (fun _ => Unit) := fun A => inhabitedRecord A Unit (.value _)

/-- The family over types of `inhabitedRecord`, about a step of a state of two values. -/
def inhabitedStep : Family Type (fun _ => Bool → Bool) := fun A => inhabitedRecord A _ (.step Bool)

/-- The family over types whose hypothesis asks that the type has a value. -/
def inhabitedDom : Family Type (fun _ => Unit) := fun A =>
  ⟨.value _, [⟨"the parameter has a value", fun _ => Nonempty A⟩], [], []⟩

/-- For each obligation, a family of which it holds at one parameter and fails at another, so none
holds of a family because it holds of an instance: O2, O2 before running, O3, O4 and O5 with
equality. -/
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
