import LeanIntent.Pairs
import LeanIntent.Degenerate

/-!
# The trivial witnesses of a precondition-postcondition pair

The pair obligation (`LeanIntent.OPair`) asks that each input a pair's precondition admits be served
by some implementation, and it lets the implementation depend on the input. So a pair can meet it
through witnesses that do none of the work the pair is meant to ask for: an implementation fixed to
each input in advance, a table or a script of timed actions; one that ignores the input; and one
that meets the postcondition only because the precondition admits nothing or the postcondition holds
of every subject. This module gives each pair about a covered subject type a closed class of such
*trivial witnesses*, fixed by the pair's subject type and never chosen per pair, and a statement of
whether each meets the pair, so that one that does is reported rather than missed.

## The class

For a pair about subjects of a covered type `W` (`LeanIntent.Covered`), of code `a₁ → … → aₙ → b`,
the class (`witnesses W`) holds:

* `.vacuous`, any subject at all: it meets the pair exactly when every subject does
  (`Witness.vacuous_meets_iff`), which is when the precondition admits no input or the postcondition
  holds of every subject at each input the precondition admits (`Witness.vacuous_meets_iff_post`);
* `.table`, at each input, the constant function at a value fixed for that input in advance: it
  meets the pair exactly when some table from the pair's inputs to values of `b` does
  (`Witness.table_meets_iff`), and so whenever one constant function, at any value of `b`, meets it
  (`Witness.table_meets_of_met`). For a plain value, with no argument, every subject is a constant,
  so `.table` meets every pair that some value serves at each input;
* `.blind i`, for each argument position `i` of a function of at least two arguments, at each input
  a subject chosen for that input that does not read its argument at `i` (`Sig.Fn.Ignores`), as a
  script of timed actions reads its clock and not what it sees: it meets the pair exactly when such
  a strategy does (`Witness.blind_meets_iff`). A function of one argument that does not read it is a
  constant, which `.table` already holds;
* `.fixed d`, for each member `d` of the degenerate class of `W` (`LeanIntent.degenerate`), one
  subject `d` stands for at every input, so the same whatever the input: it meets the pair exactly
  when a subject of `d` meets it (`Witness.fixed_meets_iff`).

`Sig.mem_witnesses_iff` states the class apart from the list that computes it. `Pair.MetTrivially`
states, over strategies from the pair's inputs to subjects and apart from the class, that some
trivial witness meets the pair, and `metTrivially_iff` equates it with some member of the class
meeting it.

The class takes no pair and no other parameter, only `W` through its code, so it is the same for
every pair about `W` whatever the pair's input type, and the verdicts on every pair about `W` are
stated over that one class. The input type needs no code: the members chosen at each input quantify
over it, and no member is built from it. A subject type that is not covered has no `Covered`
instance, so Lean reports that it cannot synthesize one and no verdict about a pair of that type can
be stated.

## Verdicts

`WitnessVerdicts q bs` states, for each member in order, whether it meets the pair `q`: `true` that
it does, `false` that it does not, as goals the agent proves (`witnessVerdicts`), so each verdict is
a theorem Lean's kernel checks. A list of the wrong length is refused (`witnessVerdicts_correct`),
and a verdict of `false` on a member that meets the pair cannot be proved, so a meeting member is
never passed. `reported W bs` lists the members the verdicts say meet the pair, which under proved
verdicts are exactly those that do (`mem_reported`), and it is empty exactly when no trivial witness
meets the pair (`reported_eq_nil_iff`).

## What the class does not hold

* A witness that does not read a part of one argument, such as a field of a structure, one side of a
  pair or all of a history but its length, or a subject type whose only argument is a clock: the
  type does not say which part of an argument is what the subject sees (#46).
* A strategy that offers different kinds of degenerate subject at different inputs, such as the
  projection onto one argument at some inputs and onto another at others, unless every subject it
  offers is a constant or does not read one same argument.
* A member of its own for a constant the degenerate class does not list, offered at every input:
  `.table` reports such a constant (`Witness.table_meets_of_met`).
-/

namespace LeanIntent

open Sig

/-! ## Functions that do not read an argument -/

/-- The function `f` of the arguments `as` does not read its argument at position `i`, counted from
zero: at position zero, it is the same function of the arguments after it whatever that argument is;
at a later position, the function of the rest that each value of the first argument gives does not
read the argument at the position before. No function reads a position past its last argument. -/
def Sig.Fn.Ignores {b : Ty} : {as : List Ty} → Fn b as → Nat → Prop
  | [], _, _ => True
  | _ :: _, f, 0 => ∀ x y, f x = f y
  | _ :: _, f, i + 1 => ∀ x, Sig.Fn.Ignores (f x) i

/-- A constant function reads none of its arguments. -/
theorem Sig.Fn.const_ignores {b : Ty} (v : b.denote) :
    (as : List Ty) → (i : Nat) → (Fn.const b v as).Ignores i
  | [], _ => trivial
  | _ :: _, 0 => fun _ _ => rfl
  | _ :: as, i + 1 => fun _ => Sig.Fn.const_ignores v as i

/-! ## The class -/

/-- A trivial witness of a pair about subjects whose type has the code `σ`, by its description
(`Sig.witnesses`). -/
inductive Witness (σ : Sig) where
  /-- Any subject at all, which meets the pair only where every subject does. -/
  | vacuous
  /-- At each input, the constant function at a value fixed for that input in advance: a table, or a
  script that takes one action throughout. -/
  | table
  /-- At each input, a subject chosen for that input that does not read its argument at position
  `i`, as a script of timed actions reads its clock and not what it sees. -/
  | blind (i : Fin σ.args.length)
  /-- One subject the degenerate member `d` stands for, at every input, so the same whatever the
  input. -/
  | fixed (d : Degenerate σ)

namespace Sig

/-- The members that do not read one argument, at each input: one for each argument of a function of
at least two, and none otherwise, since a function of one argument that does not read it is a
constant, which `.table` holds. -/
def blinds (σ : Sig) : List (Witness σ) :=
  if 2 ≤ σ.args.length then (List.finRange σ.args.length).map .blind else []

/-- The trivial witnesses of a pair about subjects of the type `σ` denotes: any subject, a table,
the members that do not read one argument, and one degenerate subject at every input for each member
of the degenerate class. -/
def witnesses (σ : Sig) : List (Witness σ) :=
  .vacuous :: .table :: (σ.blinds ++ σ.degenerate.map .fixed)

/-- The class, apart from the list that computes it: any subject, a table, the member that does not
read the argument at each position of a function of at least two arguments, and one subject of each
member of the degenerate class. -/
theorem mem_witnesses_iff {σ : Sig} (t : Witness σ) :
    t ∈ σ.witnesses ↔
      t = .vacuous ∨ t = .table ∨ (2 ≤ σ.args.length ∧ ∃ i, t = .blind i) ∨
        ∃ d, d ∈ σ.degenerate ∧ t = .fixed d := by
  simp only [witnesses, blinds, List.mem_cons, List.mem_append, List.mem_map]
  by_cases h : 2 ≤ σ.args.length
  · simp only [h, ↓reduceIte, List.mem_map, List.mem_finRange, true_and]
    constructor
    · rintro (rfl | rfl | ⟨i, rfl⟩ | ⟨d, hd, rfl⟩)
      · exact .inl rfl
      · exact .inr (.inl rfl)
      · exact .inr (.inr (.inl ⟨i, rfl⟩))
      · exact .inr (.inr (.inr ⟨d, hd, rfl⟩))
    · rintro (rfl | rfl | ⟨i, rfl⟩ | ⟨d, hd, rfl⟩)
      · exact .inl rfl
      · exact .inr (.inl rfl)
      · exact .inr (.inr (.inl ⟨i, rfl⟩))
      · exact .inr (.inr (.inr ⟨d, hd, rfl⟩))
  · simp only [h, ↓reduceIte, List.not_mem_nil, false_or, false_and]
    constructor
    · rintro (rfl | rfl | ⟨d, hd, rfl⟩)
      · exact .inl rfl
      · exact .inr (.inl rfl)
      · exact .inr (.inr ⟨d, hd, rfl⟩)
    · rintro (rfl | rfl | ⟨d, hd, rfl⟩)
      · exact .inl rfl
      · exact .inr (.inl rfl)
      · exact .inr (.inr ⟨d, hd, rfl⟩)

/-- The class has two members, one for each argument of a function of at least two, and one for each
member of the degenerate class. -/
theorem length_witnesses (σ : Sig) :
    σ.witnesses.length =
      2 + (if 2 ≤ σ.args.length then σ.args.length else 0) + σ.degenerate.length := by
  by_cases h : 2 ≤ σ.args.length <;> simp [witnesses, blinds, h] <;> omega

end Sig

/-- The trivial witnesses of a pair about subjects of the type `W`, by their descriptions: the class
of `W`'s code. It takes no pair, so it is the same for every pair about `W`, whatever its input
type. -/
def witnesses (W : Type) [c : Covered W] : List (Witness c.sig) := c.sig.witnesses

/-! ## What a member meets -/

section Meets

variable {W : Type} [c : Covered W]

/-- `w` is a constant subject: the function that returns one value of the output type whatever its
arguments, carried back to `W` (`Degenerate.constantSubject`). For a plain value, every subject is
one. -/
def Witness.Constant (w : W) : Prop := ∃ v, w = Degenerate.constantSubject v

/-- `w` does not read its argument at position `i`: the function of `W`'s code that the isomorphism
through which the code stands for `W` takes it to does not read it (`Sig.Fn.Ignores`). The
isomorphism takes each argument through a bijection of its own type, so this is the subject itself
not reading that argument. -/
def Witness.BlindTo (i : Nat) (w : W) : Prop := (c.iso.to w).Ignores i

/-- The member `t` meets the pair `q`: for `.vacuous`, every subject meets it; for `.table`, at each
input the precondition admits a constant subject meets the postcondition; for `.blind i`, at each
such input a subject that does not read its argument at `i` does; and for `.fixed d`, one subject
`d` stands for meets the pair at every input. -/
def Witness.Meets (t : Witness c.sig) (q : Pair W) : Prop :=
  match t with
  | .vacuous => ∀ w, q.Met w
  | .table => ∀ x, q.pre x → ∃ w, Witness.Constant w ∧ q.post x w
  | .blind i => ∀ x, q.pre x → ∃ w, Witness.BlindTo i.val w ∧ q.post x w
  | .fixed d => ∃ w, d.Is w ∧ q.Met w

/-- A constant subject reads none of its arguments. -/
theorem Witness.blindTo_of_constant {w : W} (h : Witness.Constant w) (i : Nat) :
    Witness.BlindTo i w := by
  obtain ⟨v, rfl⟩ := h
  unfold Witness.BlindTo
  rw [Degenerate.iso_constantSubject]
  exact Sig.Fn.const_ignores v _ i

omit c in
/-- A choice, at each admitted input, of a subject with the property `P` that meets the
postcondition there is one strategy, which offers `w₀` at every other input. -/
private theorem strategy_of_served {q : Pair W} {P : W → Prop} {w₀ : W} (h₀ : P w₀)
    (h : ∀ x, q.pre x → ∃ w, P w ∧ q.post x w) :
    ∃ s : q.Input → W, (∀ x, P (s x)) ∧ ∀ x, q.pre x → q.post x (s x) := by
  have hc : ∀ x, ∃ w, P w ∧ (q.pre x → q.post x w) := fun x => by
    by_cases hx : q.pre x
    · obtain ⟨w, hw, hp⟩ := h x hx
      exact ⟨w, hw, fun _ => hp⟩
    · exact ⟨w₀, h₀, fun h' => absurd h' hx⟩
  obtain ⟨s, hs⟩ := Classical.axiomOfChoice hc
  exact ⟨s, fun x => (hs x).1, fun x => (hs x).2⟩

/-! ### Each member, over strategies -/

/-- `.vacuous` meets the pair exactly when every strategy does, whatever subject it offers at each
input. -/
theorem Witness.vacuous_meets_iff (q : Pair W) :
    (Witness.vacuous : Witness c.sig).Meets q ↔ ∀ s : q.Input → W, ∀ x, q.pre x → q.post x (s x) :=
  ⟨fun h s x hx => h (s x) x hx, fun h w x hx => h (fun _ => w) x hx⟩

/-- `.vacuous` meets the pair exactly when the postcondition holds of every subject at each input
the precondition admits. -/
theorem Witness.vacuous_meets_iff_post (q : Pair W) :
    (Witness.vacuous : Witness c.sig).Meets q ↔ ∀ x, q.pre x → ∀ w, q.post x w :=
  ⟨fun h x hx w => h w x hx, fun h w x hx => h x hx w⟩

/-- A precondition that admits no input makes `.vacuous` meet the pair. -/
theorem Witness.vacuous_meets_of_admits_nothing {q : Pair W} (h : ∀ x, ¬ q.pre x) :
    (Witness.vacuous : Witness c.sig).Meets q := fun _ x hx => absurd hx (h x)

/-- `.table` meets the pair exactly when some table from its inputs to values of the output type,
offering the constant function at the value it gives each input, does. -/
theorem Witness.table_meets_iff (q : Pair W) :
    (Witness.table : Witness c.sig).Meets q ↔
      ∃ tab : q.Input → c.sig.out.denote,
        ∀ x, q.pre x → q.post x (Degenerate.constantSubject (tab x)) := by
  constructor
  · intro h
    have hc : ∀ x, ∃ v : c.sig.out.denote,
        q.pre x → q.post x (Degenerate.constantSubject v) := fun x => by
      by_cases hx : q.pre x
      · obtain ⟨w, ⟨v, rfl⟩, hp⟩ := h x hx
        exact ⟨v, fun _ => hp⟩
      · exact ⟨c.sig.out.empty, fun h' => absurd h' hx⟩
    exact Classical.axiomOfChoice hc
  · rintro ⟨tab, h⟩ x hx
    exact ⟨_, ⟨tab x, rfl⟩, h x hx⟩

/-- `.blind i` meets the pair exactly when some strategy whose every subject does not read its
argument at `i` does. -/
theorem Witness.blind_meets_iff (q : Pair W) (i : Fin c.sig.args.length) :
    (Witness.blind i).Meets q ↔
      ∃ s : q.Input → W, (∀ x, Witness.BlindTo i.val (s x)) ∧ ∀ x, q.pre x → q.post x (s x) :=
  ⟨strategy_of_served (Witness.blindTo_of_constant ⟨c.sig.out.empty, rfl⟩ i.val),
    fun ⟨s, hs, h⟩ x hx => ⟨s x, hs x, h x hx⟩⟩

/-- `.fixed d` meets the pair exactly when one subject `d` stands for, offered at every input, does.
-/
theorem Witness.fixed_meets_iff (q : Pair W) (d : Degenerate c.sig) :
    (Witness.fixed d).Meets q ↔ ∃ w, d.Is w ∧ ∀ x, q.pre x → q.post x w := Iff.rfl

/-! ### The witnesses each member reports -/

/-- One constant function, at any value of the output type, that meets the pair makes `.table` meet
it, whether or not the degenerate class lists that constant. -/
theorem Witness.table_meets_of_met {q : Pair W} {v : c.sig.out.denote}
    (h : q.Met (Degenerate.constantSubject v)) : (Witness.table : Witness c.sig).Meets q :=
  fun x hx => ⟨_, ⟨v, rfl⟩, h x hx⟩

/-- Where every subject meets the pair, `.table` does. -/
theorem Witness.table_meets_of_vacuous {q : Pair W}
    (h : (Witness.vacuous : Witness c.sig).Meets q) : (Witness.table : Witness c.sig).Meets q :=
  Witness.table_meets_of_met (v := c.sig.out.empty) (h _)

/-- Where `.table` meets the pair, so does every member that does not read one argument, since a
constant reads none. -/
theorem Witness.blind_meets_of_table {q : Pair W} (i : Fin c.sig.args.length)
    (h : (Witness.table : Witness c.sig).Meets q) : (Witness.blind i).Meets q := fun x hx =>
  let ⟨w, hw, hp⟩ := h x hx
  ⟨w, Witness.blindTo_of_constant hw i.val, hp⟩

/-- One subject that does not read its argument at `i` and meets the pair makes `.blind i` meet it.
-/
theorem Witness.blind_meets_of_met {q : Pair W} {i : Fin c.sig.args.length} {w : W}
    (hb : Witness.BlindTo i.val w) (h : q.Met w) : (Witness.blind i).Meets q :=
  fun x hx => ⟨w, hb, h x hx⟩

/-- A subject of a degenerate member that meets the pair makes that member's `.fixed` meet it. -/
theorem Witness.fixed_meets_of_met {q : Pair W} {d : Degenerate c.sig} {w : W} (hi : d.Is w)
    (h : q.Met w) : (Witness.fixed d).Meets q := ⟨w, hi, h⟩

/-- The pair obligation in the class of constant subjects is the precondition admitting an input and
`.table` meeting the pair. -/
theorem Witness.oPair_constant_iff (q : Pair W) :
    OPair q Witness.Constant ↔ (∃ x, q.pre x) ∧ (Witness.table : Witness c.sig).Meets q := by
  obtain ⟨Input, pre, post⟩ := q
  rw [oPair_correct]
  exact Iff.rfl

/-- The pair obligation in the class of subjects that do not read the argument at `i` is the
precondition admitting an input and `.blind i` meeting the pair. -/
theorem Witness.oPair_blindTo_iff (q : Pair W) (i : Fin c.sig.args.length) :
    OPair q (Witness.BlindTo i.val) ↔ (∃ x, q.pre x) ∧ (Witness.blind i).Meets q := by
  obtain ⟨Input, pre, post⟩ := q
  rw [oPair_correct]
  exact Iff.rfl

/-- No member meets a pair with an admitted input that no subject serves, so none is met by every
pair. -/
theorem Witness.not_meets_of_unserved {q : Pair W} {x : q.Input} (hx : q.pre x)
    (h : ∀ w, ¬ q.post x w) : (t : Witness c.sig) → ¬ t.Meets q
  | .vacuous => fun hm => h _ (hm (Degenerate.constantSubject c.sig.out.empty) x hx)
  | .table => fun hm => let ⟨w, _, hp⟩ := hm x hx; h w hp
  | .blind _ => fun hm => let ⟨w, _, hp⟩ := hm x hx; h w hp
  | .fixed _ => fun ⟨w, _, hm⟩ => h w (hm x hx)

end Meets

/-! ## The class of a pair's subject type -/

section Class

variable {W : Type} [c : Covered W]

theorem Witness.vacuous_mem : (Witness.vacuous : Witness c.sig) ∈ witnesses W :=
  (Sig.mem_witnesses_iff _).mpr (.inl rfl)

theorem Witness.table_mem : (Witness.table : Witness c.sig) ∈ witnesses W :=
  (Sig.mem_witnesses_iff _).mpr (.inr (.inl rfl))

/-- For a function of at least two arguments, the member that does not read each one is in the
class. -/
theorem Witness.blind_mem (h : 2 ≤ c.sig.args.length) (i : Fin c.sig.args.length) :
    Witness.blind i ∈ witnesses W :=
  (Sig.mem_witnesses_iff _).mpr (.inr (.inr (.inl ⟨h, i, rfl⟩)))

/-- Each member of the degenerate class, offered at every input, is in the class. -/
theorem Witness.fixed_mem {d : Degenerate c.sig} (hd : d ∈ degenerate W) :
    Witness.fixed d ∈ witnesses W :=
  (Sig.mem_witnesses_iff _).mpr (.inr (.inr (.inr ⟨d, hd, rfl⟩)))

/-- No covered type's class is empty. -/
theorem witnesses_ne_nil (W : Type) [Covered W] : witnesses W ≠ [] :=
  List.ne_nil_of_mem Witness.vacuous_mem

/-- Some trivial witness meets the pair `q`, stated over strategies, each the subject offered at
every input, and apart from the class: every strategy meets it; a table from its inputs to values of
the output type, offering at each input the constant function at the value it gives, meets it; for a
function of at least two arguments, a strategy whose every subject does not read one same argument
meets it; or one subject of a member of the degenerate class, offered at every input, meets it. -/
def Pair.MetTrivially (q : Pair W) : Prop :=
  (∀ s : q.Input → W, ∀ x, q.pre x → q.post x (s x)) ∨
    (∃ tab : q.Input → c.sig.out.denote,
      ∀ x, q.pre x → q.post x (Degenerate.constantSubject (tab x))) ∨
    (2 ≤ c.sig.args.length ∧ ∃ i < c.sig.args.length, ∃ s : q.Input → W,
      (∀ x, Witness.BlindTo i (s x)) ∧ ∀ x, q.pre x → q.post x (s x)) ∨
    ∃ d ∈ degenerate W, ∃ w, d.Is w ∧ ∀ x, q.pre x → q.post x w

/-- The class lists every trivial witness: some trivial witness meets the pair exactly when some
member of the class does. -/
theorem metTrivially_iff (q : Pair W) : q.MetTrivially ↔ ∃ t ∈ witnesses W, t.Meets q := by
  constructor
  · rintro (h | h | ⟨hn, i, hi, h⟩ | ⟨d, hd, h⟩)
    · exact ⟨_, Witness.vacuous_mem, (Witness.vacuous_meets_iff q).mpr h⟩
    · exact ⟨_, Witness.table_mem, (Witness.table_meets_iff q).mpr h⟩
    · exact ⟨_, Witness.blind_mem hn ⟨i, hi⟩, (Witness.blind_meets_iff q ⟨i, hi⟩).mpr h⟩
    · exact ⟨_, Witness.fixed_mem hd, h⟩
  · rintro ⟨t, ht, hm⟩
    rcases (Sig.mem_witnesses_iff t).mp ht with rfl | rfl | ⟨hn, i, rfl⟩ | ⟨d, hd, rfl⟩
    · exact .inl ((Witness.vacuous_meets_iff q).mp hm)
    · exact .inr (.inl ((Witness.table_meets_iff q).mp hm))
    · exact .inr (.inr (.inl ⟨hn, i.val, i.isLt, (Witness.blind_meets_iff q i).mp hm⟩))
    · exact .inr (.inr (.inr ⟨d, hd, hm⟩))

end Class

/-! ## Verdicts -/

section Verdicts

variable {W : Type} [c : Covered W]

/-- The goal that `b` is the verdict on the member `t` for the pair `q`: that `t` meets `q` when `b`
is `true`, and that it does not when `b` is `false`. -/
def witnessGoal (q : Pair W) (t : Witness c.sig) : Bool → Prop
  | true => t.Meets q
  | false => ¬ t.Meets q

/-- The goals that `bs` are, in order, the verdicts on the members `ts` for `q`, and the goal
`False` when the two lists differ in length. -/
def witnessGoals (q : Pair W) : List (Witness c.sig) → List Bool → List Prop
  | [], [] => []
  | t :: ts, b :: bs => witnessGoal q t b :: witnessGoals q ts bs
  | _, _ => [False]

/-- The trivial-witness check's goals: that `bs` are, in order, the verdicts on the trivial
witnesses of `W` for the pair `q`. -/
def witnessVerdicts (q : Pair W) (bs : List Bool) : List Prop := witnessGoals q (witnesses W) bs

/-- `bs` are the verdicts, in order, on the trivial witnesses of `W` for the pair `q`. -/
def WitnessVerdicts (q : Pair W) (bs : List Bool) : Prop := Goals (witnessVerdicts q bs)

/-- What the trivial-witness check asks, written apart from its former: one verdict for each member
of the class, `true` exactly when the member at the same position meets the pair. -/
def intendedWitnessVerdicts (q : Pair W) (bs : List Bool) : Prop :=
  bs.length = (witnesses W).length ∧
    ∀ (i : Nat) (hb : i < bs.length) (hd : i < (witnesses W).length),
      (bs[i] = true ↔ (witnesses W)[i].Meets q)

theorem goals_witnessGoals (q : Pair W) : (ts : List (Witness c.sig)) → (bs : List Bool) →
    (Goals (witnessGoals q ts bs) ↔ bs.length = ts.length ∧
      ∀ (i : Nat) (hb : i < bs.length) (hd : i < ts.length), (bs[i] = true ↔ ts[i].Meets q))
  | [], [] => by simp [witnessGoals, Goals]
  | [], _ :: _ => by simp [witnessGoals, Goals]
  | _ :: _, [] => by simp [witnessGoals, Goals]
  | t :: ts, b :: bs => by
      rw [witnessGoals, Goals, goals_witnessGoals q ts bs]
      constructor
      · rintro ⟨hv, hlen, hall⟩
        refine ⟨by simp [hlen], fun i hb hd => ?_⟩
        cases i with
        | zero => cases b <;> simpa [witnessGoal] using hv
        | succ i => simpa using hall i (by simpa using hb) (by simpa using hd)
      · rintro ⟨hlen, hall⟩
        refine ⟨?_, by simpa using hlen, fun i hb hd =>
          hall (i + 1) (Nat.succ_lt_succ hb) (Nat.succ_lt_succ hd)⟩
        have h0 := hall 0 (by simp) (by simp)
        cases b <;> simpa [witnessGoal] using h0

/-- The trivial-witness check's former states it. -/
theorem witnessVerdicts_correct (q : Pair W) (bs : List Bool) :
    WitnessVerdicts q bs ↔ intendedWitnessVerdicts q bs := by
  rw [WitnessVerdicts, witnessVerdicts, goals_witnessGoals]
  rfl

/-- The members among `ts` whose verdict in `bs` is `true`. -/
def reportedGo {σ : Sig} : List (Witness σ) → List Bool → List (Witness σ)
  | t :: ts, true :: bs => t :: reportedGo ts bs
  | _ :: ts, false :: bs => reportedGo ts bs
  | _, _ => []

/-- The members of the class of `W` whose verdict in `bs` is that they meet the pair. -/
def reported (W : Type) [c : Covered W] (bs : List Bool) : List (Witness c.sig) :=
  reportedGo (witnesses W) bs

theorem mem_reportedGo (q : Pair W) (t : Witness c.sig) : (ts : List (Witness c.sig)) →
    (bs : List Bool) → Goals (witnessGoals q ts bs) →
      (t ∈ reportedGo ts bs ↔ t ∈ ts ∧ t.Meets q)
  | [], [], _ => by simp [reportedGo]
  | [], _ :: _, h => absurd h (by simp [witnessGoals, Goals])
  | _ :: _, [], h => absurd h (by simp [witnessGoals, Goals])
  | t' :: ts, true :: bs, ⟨hv, h⟩ => by
      rw [reportedGo, List.mem_cons, mem_reportedGo q t ts bs h, List.mem_cons]
      constructor
      · rintro (rfl | ⟨ht, hm⟩)
        · exact ⟨.inl rfl, hv⟩
        · exact ⟨.inr ht, hm⟩
      · rintro ⟨rfl | ht, hm⟩
        · exact .inl rfl
        · exact .inr ⟨ht, hm⟩
  | t' :: ts, false :: bs, ⟨hv, h⟩ => by
      rw [reportedGo, mem_reportedGo q t ts bs h, List.mem_cons]
      constructor
      · rintro ⟨ht, hm⟩
        exact ⟨.inr ht, hm⟩
      · rintro ⟨rfl | ht, hm⟩
        · exact absurd hm hv
        · exact ⟨ht, hm⟩

/-- Under proved verdicts, the members reported are exactly those that meet the pair. -/
theorem mem_reported {q : Pair W} {bs : List Bool} (h : WitnessVerdicts q bs) (t : Witness c.sig) :
    t ∈ reported W bs ↔ t ∈ witnesses W ∧ t.Meets q :=
  mem_reportedGo q t _ bs h

/-- Under proved verdicts, the report is empty exactly when no trivial witness meets the pair, so a
witness that meets it is never missed. -/
theorem reported_eq_nil_iff {q : Pair W} {bs : List Bool} (h : WitnessVerdicts q bs) :
    reported W bs = [] ↔ ¬ q.MetTrivially := by
  rw [List.eq_nil_iff_forall_not_mem, metTrivially_iff]
  constructor
  · rintro hn ⟨t, ht, hm⟩
    exact hn t ((mem_reported h t).mpr ⟨ht, hm⟩)
  · intro hn t ht
    exact hn ⟨t, (mem_reported h t).mp ht⟩

end Verdicts

end LeanIntent
