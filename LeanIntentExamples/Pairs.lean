import LeanIntent.Pairs

/-!
# The pairs of an agent's property, and the class that must serve them

An agent sees one bit of its world and answers with one action; it reaches a world's goal when its
action is the one the world needs. The record asks that the agent reach the goal of every legible
world, one in which what the agent sees is the action it needs. Its one property gives two pairs:

* `perWorld`, whose input is a world, which the agent does not choose, admitted when legible;
* `Pair.whole`, whose only input is trivial and which asks one agent to reach the goal of every
  legible world.

Both are pairs of the property (`perWorld_pairOf`, `pairOf_whole`), and the obligation separates
them. Each legible world taken alone is reached by an agent that ignores what it sees, the constant
of the action that world needs, so `perWorld` meets the obligation in the class of such agents
(`perWorld_blind`): a claim that no agent ignoring what it sees can reach these goals is false of each
world, as a script timed in advance solves each feasible goal. No such agent reaches the goal of every
legible world, so the pair whose only input is trivial fails in that class (`whole_not_blind`) and
meets it in the class of all agents (`whole_any`). So the obligation of a finer pair does not give that
of the whole property (`perWorld_not_whole`), and the obligation in a wide class does not give it in a
narrower one (`any_not_blind`).

A record that asks the agent to reach the goal of every world has a precondition too wide for any
class: two worlds look alike and need opposite actions (`seenAlike`), so no agent serves the input of
its pair whose only input is trivial (`every_not_oPair`), although each world alone is still reached by
an agent that ignores what it sees (`everyPerWorld_blind`).
-/

namespace LeanIntentExamples.Pairs

open LeanIntent

/-- A world: what an agent sees in it, and the action that reaches its goal. -/
structure World where
  /-- What the agent sees. -/
  sight : Bool
  /-- The action that reaches the world's goal. -/
  need : Bool

/-- An agent: the action it takes on what it sees. -/
abbrev Agent := Bool → Bool

/-- The agent `a` reaches the goal of the world `v`. -/
def Reaches (a : Agent) (v : World) : Prop := a v.sight = v.need

/-- A legible world: what the agent sees there is the action it needs. -/
def Legible (v : World) : Prop := v.need = v.sight

/-- An agent that ignores what it sees, taking one action whatever it sees, as a script fixed in
advance does. -/
def Blind (a : Agent) : Prop := ∀ s t, a s = a t

/-- The property that the agent reaches the goal of every legible world. -/
def reachesLegible : Clause Agent :=
  ⟨"reaches the goal of every legible world", fun a => ∀ v, Legible v → Reaches a v⟩

/-- The record of an agent that reaches the goal of every legible world. -/
def agent : IntentRecord Agent where
  shape := .function _ _
  dom := []
  props := [reachesLegible]
  vocab := [⟨"Legible", World, Legible⟩, ⟨"Reaches", Agent × World, fun p => Reaches p.1 p.2⟩]

/-- The pair the property gives for each world: the input is the world, the precondition that it is
legible, and the postcondition that the agent reaches its goal. -/
def perWorld : Pair Agent := ⟨World, Legible, fun v a => Reaches a v⟩

/-- `perWorld` is a pair of the property. -/
theorem perWorld_pairOf : agent.PairOf reachesLegible perWorld :=
  ⟨List.mem_singleton_self _, fun _ =>
    ⟨fun h v hv => h (fun _ hd => nomatch hd) v hv, fun h _ => h⟩⟩

/-- Each legible world alone is reached by an agent that ignores what it sees: the per-world pair
meets the obligation in that class. -/
theorem perWorld_blind : OPair perWorld Blind :=
  oPair_of ⟨⟨true, true⟩, rfl, fun _ => false, nofun⟩ fun v _ =>
    ⟨fun _ => v.need, fun _ _ => rfl, rfl⟩

/-- The legible worlds that see `true` and `false` need different actions. -/
theorem legible_differ (a : Agent) (h : reachesLegible.holds a) : ¬ Blind a := fun hb => by
  have ht : a true = true := h ⟨true, true⟩ rfl
  have hf : a false = false := h ⟨false, false⟩ rfl
  rw [hb true false, hf] at ht
  exact Bool.false_ne_true ht

/-- No agent that ignores what it sees reaches the goal of every legible world. -/
theorem whole_not_blind : ¬ OPair (Pair.whole agent reachesLegible) Blind := fun h => by
  obtain ⟨_, a, hb, hf⟩ := (oPair_whole_iff _ _ _).mp h
  exact legible_differ a (hf fun _ hd => nomatch hd) hb

/-- The agent that does what it sees reaches the goal of every legible world, and the agent that
always answers `false` fails one: the whole property meets the obligation in the class of all agents. -/
theorem whole_any : OPair (Pair.whole agent reachesLegible) fun _ => True :=
  (oPair_whole_iff agent reachesLegible _).mpr
    ⟨⟨fun _ => false, fun _ hd => (nomatch hd), fun h => Bool.false_ne_true (h ⟨true, true⟩ rfl)⟩,
      fun s => s, trivial, fun _ _ hv => hv.symm⟩

/-- The obligation of the per-world pair does not give that of the whole property. -/
theorem perWorld_not_whole :
    OPair perWorld Blind ∧ ¬ OPair (Pair.whole agent reachesLegible) Blind :=
  ⟨perWorld_blind, whole_not_blind⟩

/-- The obligation in the class of all agents does not give it in a narrower class. -/
theorem any_not_blind :
    OPair (Pair.whole agent reachesLegible) (fun _ => True) ∧
      ¬ OPair (Pair.whole agent reachesLegible) Blind :=
  ⟨whole_any, whole_not_blind⟩

/-- The property that the agent reaches the goal of every world. -/
def reachesEvery : Clause Agent := ⟨"reaches the goal of every world", fun a => ∀ v, Reaches a v⟩

/-- The record of an agent that reaches the goal of every world. -/
def every : IntentRecord Agent where
  shape := .function _ _
  dom := []
  props := [reachesEvery]
  vocab := [⟨"Reaches", Agent × World, fun p => Reaches p.1 p.2⟩]

/-- Two worlds that an agent sees alike need opposite actions, so no agent reaches both goals. -/
theorem seenAlike (a : Agent) : ¬ (Reaches a ⟨true, true⟩ ∧ Reaches a ⟨true, false⟩) :=
  fun ⟨ht, hf⟩ => Bool.false_ne_true (hf.symm.trans ht)

/-- The precondition of every world is too wide for every class: no agent serves the only input of
the pair whose only input is trivial. -/
theorem every_not_oPair (C : Agent → Prop) : ¬ OPair (Pair.whole every reachesEvery) C :=
  not_oPair_of_unserved (x := PUnit.unit) trivial fun a _ h =>
    seenAlike a ⟨h (fun _ hd => nomatch hd) _, h (fun _ hd => nomatch hd) _⟩

/-- The pair of the record of every world whose input is the world. -/
def everyPerWorld : Pair Agent := ⟨World, fun _ => True, fun v a => Reaches a v⟩

/-- Each world alone is still reached by an agent that ignores what it sees. -/
theorem everyPerWorld_blind : OPair everyPerWorld Blind :=
  oPair_of ⟨⟨true, true⟩, trivial, fun _ => false, nofun⟩ fun v _ =>
    ⟨fun _ => v.need, fun _ _ => rfl, rfl⟩

end LeanIntentExamples.Pairs
