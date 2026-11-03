import LeanIntentExamples.Pairs
import LeanIntent.TrivialWitnesses

/-!
# The trivial witnesses of an agent's pairs

The agent of `LeanIntentExamples.Pairs` sees one bit and answers with one action, and its record
asks it to reach the goal of every legible world. Its subject type `Bool → Bool` takes one argument,
so its trivial witnesses are any subject, the table, and one subject of each degenerate member: the
constants at `false` and `true` and the identity (`agent_witnesses`, `agent_degenerate`).

The per-world pair meets the pair obligation in the class of agents that ignore what they see
(`perWorld_blind`), and the check reports why: the table meets it, since each legible world is
reached by the constant of the action that world needs, fixed to that world in advance
(`perWorld_witnesses`, `perWorld_table_reported`). So that pair's obligation is no evidence that the
agent uses what it sees. No constant meets the pair whose only input is trivial, one agent for every
legible world, and the table does not (`whole_witnesses`); the identity, the agent that does what it
sees, meets both, and each report names it.

An agent with a clock acts at two steps, each on what it sees there, and its record asks it to
follow every readable course, one in which what it sees at each step is the action it needs then.
Its subject type `Fin 2 → Bool → Bool` takes two arguments, so its class also holds, for each, the
member that does not read it (`clocked_witnesses`). Each readable course alone is followed by a
script of timed actions, which reads its clock and not what it sees, so the per-course pair is met
by the member that does not read the second argument (`perCourse_witnesses`), as a timed script
solves every feasible goal; no constant follows the course that needs `true` and then `false`, so
the table does not meet it. No timed script follows every readable course, so that member does not
meet the pair whose only input is trivial, while the agent that ignores its clock and does what it
sees does (`wholeCourse_witnesses`).
-/

namespace LeanIntentExamples.TrivialWitnesses

open LeanIntent LeanIntentExamples.Pairs

/-! ## An agent that sees one bit -/

/-- An agent of one argument has no member that does not read one argument: the constants hold it.
-/
theorem agent_witnesses :
    witnesses Agent = [.vacuous, .table] ++ (degenerate Agent).map .fixed := rfl

/-- The degenerate members of an agent: the constants at `false` and `true`, and the identity. -/
theorem agent_degenerate :
    (degenerate Agent).map Degenerate.reading =
      [.subject fun _ => false, .subject fun _ => true, .subject fun s => s] := rfl

/-- An agent ignores what it sees exactly when it is a constant subject. -/
theorem blind_iff_constant (a : Agent) : Blind a ↔ Witness.Constant a :=
  ⟨fun h => ⟨a false, funext fun s => h s false⟩, fun ⟨_, e⟩ _ _ => by subst e; rfl⟩

/-- The per-world pair is met by the table, since each legible world is reached by an agent that
ignores what it sees, and by the identity, and by no constant and not by every agent. -/
theorem perWorld_witnesses : WitnessVerdicts perWorld [false, true, false, false, true] := by
  refine ⟨fun h => ?_, ?_, fun ⟨_, e, h⟩ => ?_, fun ⟨_, e, h⟩ => ?_, ⟨_, rfl, fun v hv => hv.symm⟩,
    trivial⟩
  · exact Bool.false_ne_true (h (fun _ => false) ⟨true, true⟩ rfl)
  · exact ((Witness.oPair_constant_iff perWorld).mp
      (perWorld_blind.mono fun a h => (blind_iff_constant a).mp h)).2
  · subst e
    exact Bool.false_ne_true (h ⟨true, true⟩ rfl)
  · subst e
    exact Bool.false_ne_true (h ⟨false, false⟩ rfl).symm

/-- The check reports the table for the per-world pair. -/
theorem perWorld_table_reported :
    Witness.table ∈ reported Agent [false, true, false, false, true] :=
  (mem_reported perWorld_witnesses _).mpr ⟨Witness.table_mem, perWorld_witnesses.2.1⟩

/-- The pair whose only input is trivial is met by the identity alone: no constant reaches the goal
of every legible world. -/
theorem whole_witnesses :
    WitnessVerdicts (Pair.whole agent reachesLegible) [false, false, false, false, true] := by
  refine ⟨fun h => ?_, fun h => ?_, fun ⟨_, e, h⟩ => ?_, fun ⟨_, e, h⟩ => ?_,
    ⟨_, rfl, fun _ _ _ _ hv => hv.symm⟩, trivial⟩
  · exact Bool.false_ne_true
      (h (fun _ => false) PUnit.unit trivial (fun _ hd => nomatch hd) ⟨true, true⟩ rfl)
  · exact whole_not_blind
      (OPair.mono ((Witness.oPair_constant_iff _).mpr ⟨⟨PUnit.unit, trivial⟩, h⟩)
        fun a ha => (blind_iff_constant a).mpr ha)
  · subst e
    exact Bool.false_ne_true (h PUnit.unit trivial (fun _ hd => nomatch hd) ⟨true, true⟩ rfl)
  · subst e
    exact Bool.false_ne_true (h PUnit.unit trivial (fun _ hd => nomatch hd) ⟨false, false⟩ rfl).symm

/-! ## An agent with a clock -/

/-- A course of two steps: what the agent sees at each step, and the action that reaches its goal
then. -/
structure Course where
  /-- What the agent sees at each step. -/
  sight : Fin 2 → Bool
  /-- The action each step needs. -/
  need : Fin 2 → Bool

/-- An agent with a clock: the action it takes at each step on what it sees there. -/
abbrev Clocked := Fin 2 → Bool → Bool

/-- The agent `a` follows the course `v`: at each step, it takes the action that step needs. -/
def Follows (a : Clocked) (v : Course) : Prop := ∀ t, a t (v.sight t) = v.need t

/-- A readable course: what the agent sees at each step is the action it needs then. -/
def Readable (v : Course) : Prop := ∀ t, v.need t = v.sight t

/-- The property that the agent follows every readable course. -/
def followsReadable : Clause Clocked :=
  ⟨"follows every readable course", fun a => ∀ v, Readable v → Follows a v⟩

/-- The record of an agent with a clock that follows every readable course. -/
def clocked : IntentRecord Clocked where
  shape := .function _ _
  dom := []
  props := [followsReadable]
  vocab := [⟨"Readable", Course, Readable⟩, ⟨"Follows", Clocked × Course, fun p => Follows p.1 p.2⟩]

/-- The pair the property gives for each course. -/
def perCourse : Pair Clocked := ⟨Course, Readable, fun v a => Follows a v⟩

/-- `perCourse` is a pair of the property. -/
theorem perCourse_pairOf : clocked.PairOf followsReadable perCourse :=
  ⟨List.mem_singleton_self _, fun _ =>
    ⟨fun h v hv => h (fun _ hd => nomatch hd) v hv, fun h _ => h⟩⟩

/-- The class of an agent with a clock: any subject, the table, the members that do not read its
clock and what it sees, and one subject of each degenerate member. -/
theorem clocked_witnesses :
    witnesses Clocked =
      [.vacuous, .table, .blind ⟨0, by decide⟩, .blind ⟨1, by decide⟩] ++
        (degenerate Clocked).map .fixed :=
  rfl

/-- The degenerate members of an agent with a clock: the constants, and the agent that does what it
sees. -/
theorem clocked_degenerate :
    (degenerate Clocked).map Degenerate.reading =
      [.subject fun _ _ => false, .subject fun _ _ => true, .subject fun _ s => s] := rfl

/-- The course that needs `true` and then `false`, and shows it. -/
def zigzag : Course := ⟨fun t => t.val == 0, fun t => t.val == 0⟩

/-- The course that needs `true` at each step, and shows it. -/
def allTrue : Course := ⟨fun _ => true, fun _ => true⟩

/-- The course that needs `false` at each step, and shows it. -/
def allFalse : Course := ⟨fun _ => false, fun _ => false⟩

/-- No constant follows the course that needs `true` and then `false`. -/
theorem zigzag_not_constant {a : Clocked} (h : Witness.Constant a) : ¬ Follows a zigzag := by
  obtain ⟨v, rfl⟩ := h
  intro hf
  exact Bool.false_ne_true ((hf 1).symm.trans (hf 0))

/-- The per-course pair is met by the members that do not read the clock and that do not read what
the agent sees, the latter a script of timed actions fixed to each course, and by the agent that
does what it sees; not by the table, by a constant or by every agent. -/
theorem perCourse_witnesses :
    WitnessVerdicts perCourse [false, false, true, true, false, false, true] := by
  refine ⟨fun h => ?_, fun h => ?_,
    fun _ hv => ⟨fun _ s => s, fun _ _ => rfl, fun t => (hv t).symm⟩,
    fun v _ => ⟨fun t _ => v.need t, fun _ _ _ => rfl, fun _ => rfl⟩,
    fun ⟨_, e, h⟩ => ?_, fun ⟨_, e, h⟩ => ?_, ⟨_, rfl, fun _ hv t => (hv t).symm⟩, trivial⟩
  · exact Bool.false_ne_true (h (fun _ _ => false) allTrue (fun _ => rfl) 0)
  · obtain ⟨a, ha, hf⟩ := h zigzag fun _ => rfl
    exact zigzag_not_constant ha hf
  · subst e
    exact Bool.false_ne_true (h allTrue (fun _ => rfl) 0)
  · subst e
    exact Bool.false_ne_true (h allFalse (fun _ => rfl) 0).symm

/-- No agent that does not read what it sees follows every readable course: at the first step it
takes one action whether it sees `true` or `false`. -/
theorem timed_not_whole {a : Clocked} (hb : Witness.BlindTo 1 a)
    (h : ∀ v, Readable v → Follows a v) : False := by
  have e : a 0 true = a 0 false := hb (0 : Fin 2) true false
  have ht : a 0 true = true := h allTrue (fun _ => rfl) 0
  have hf : a 0 false = false := h allFalse (fun _ => rfl) 0
  exact Bool.false_ne_true (hf.symm.trans (e.symm.trans ht))

/-- The pair whose only input is trivial is met by the agent that ignores its clock and does what it
sees, and by no script of timed actions, table or constant. -/
theorem wholeCourse_witnesses :
    WitnessVerdicts (Pair.whole clocked followsReadable)
      [false, false, true, false, false, false, true] := by
  have hNoTimed : ¬ (Witness.blind ⟨1, by decide⟩ : Witness (Covered.sig (W := Clocked))).Meets
      (Pair.whole clocked followsReadable) := fun h => by
    obtain ⟨a, hb, hf⟩ := h PUnit.unit trivial
    exact timed_not_whole hb (hf fun _ hd => nomatch hd)
  refine ⟨fun h => ?_, fun h => hNoTimed (Witness.blind_meets_of_table _ h),
    fun _ _ => ⟨fun _ s => s, fun _ _ => rfl, fun _ v hv t => (hv t).symm⟩, hNoTimed,
    fun ⟨_, e, h⟩ => ?_, fun ⟨_, e, h⟩ => ?_, ⟨_, rfl, fun _ _ _ v hv t => (hv t).symm⟩, trivial⟩
  · exact Bool.false_ne_true
      (h (fun _ _ => false) PUnit.unit trivial (fun _ hd => nomatch hd) allTrue (fun _ => rfl) 0)
  · subst e
    exact Bool.false_ne_true
      (h PUnit.unit trivial (fun _ hd => nomatch hd) allTrue (fun _ => rfl) 0)
  · subst e
    exact Bool.false_ne_true
      (h PUnit.unit trivial (fun _ hd => nomatch hd) allFalse (fun _ => rfl) 0).symm

end LeanIntentExamples.TrivialWitnesses
