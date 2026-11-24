module

public import LeanIntent.Pairs
public import LeanIntent.Clocks

public section

namespace LeanIntent

open Sig

@[expose] def Sig.Fn.Ignores {b : Ty} : {as : List Ty} → Fn b as → Nat → Prop
  | [], _, _ => True
  | _ :: _, f, 0 => ∀ x y, f x = f y
  | _ :: _, f, i + 1 => ∀ x, Sig.Fn.Ignores (f x) i

theorem Sig.Fn.const_ignores {b : Ty} (v : b.denote) :
    (as : List Ty) → (i : Nat) → (Fn.const b v as).Ignores i
  | [], _ => trivial
  | _ :: _, 0 => fun _ _ => rfl
  | _ :: as, i + 1 => fun _ => Sig.Fn.const_ignores v as i

inductive Witness (σ : Sig) where
  | vacuous
  | table
  | blind (i : Fin σ.args.length)
  | fixed (d : Degenerate σ)
  | timed (k : ArgClock σ.args)

namespace Sig

@[expose] def blinds (σ : Sig) : List (Witness σ) :=
  if 2 ≤ σ.args.length then (List.finRange σ.args.length).map .blind else []

@[expose] def clocks (σ : Sig) : List (ArgClock σ.args) :=
  (ArgClock.all σ.args).filter fun k => !k.determines || decide k.InClock

@[expose] def timeds (σ : Sig) : List (Witness σ) := σ.clocks.map .timed

@[expose] def witnesses (σ : Sig) : List (Witness σ) :=
  .vacuous :: .table :: (σ.blinds ++ σ.degenerate.map .fixed ++ σ.timeds)

theorem mem_clocks_iff {σ : Sig} (k : ArgClock σ.args) :
    k ∈ σ.clocks ↔ (∃ xs ys, xs ≠ ys ∧ k.read xs = k.read ys) ∨ k.InClock := by
  simp only [clocks, List.mem_filter, ArgClock.mem_all, true_and, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_true_eq, ArgClock.determines_eq_false_iff]

theorem mem_blinds_iff {σ : Sig} (t : Witness σ) :
    t ∈ σ.blinds ↔ 2 ≤ σ.args.length ∧ ∃ i, t = .blind i := by
  unfold blinds
  by_cases h : 2 ≤ σ.args.length
  · simp only [h, ↓reduceIte, List.mem_map, List.mem_finRange, true_and]
    exact ⟨fun ⟨i, e⟩ => ⟨i, e.symm⟩, fun ⟨i, e⟩ => ⟨i, e.symm⟩⟩
  · simp [h]

theorem mem_timeds_iff {σ : Sig} (t : Witness σ) :
    t ∈ σ.timeds ↔
      ∃ k, ((∃ xs ys, xs ≠ ys ∧ k.read xs = k.read ys) ∨ k.InClock) ∧ t = .timed k := by
  simp only [timeds, List.mem_map, mem_clocks_iff]
  exact ⟨fun ⟨k, hk, e⟩ => ⟨k, hk, e.symm⟩, fun ⟨k, hk, e⟩ => ⟨k, hk, e.symm⟩⟩

theorem mem_witnesses_iff {σ : Sig} (t : Witness σ) :
    t ∈ σ.witnesses ↔
      t = .vacuous ∨ t = .table ∨ (2 ≤ σ.args.length ∧ ∃ i, t = .blind i) ∨
        (∃ d, d ∈ σ.degenerate ∧ t = .fixed d) ∨
        ∃ k, ((∃ xs ys, xs ≠ ys ∧ k.read xs = k.read ys) ∨ k.InClock) ∧ t = .timed k := by
  simp only [witnesses, List.mem_cons, List.mem_append, mem_blinds_iff, mem_timeds_iff,
    List.mem_map]
  constructor
  · rintro (h | h | (h | ⟨d, hd, rfl⟩) | h)
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr (.inl ⟨d, hd, rfl⟩)))
    · exact .inr (.inr (.inr (.inr h)))
  · rintro (h | h | h | ⟨d, hd, rfl⟩ | h)
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl (.inl h)))
    · exact .inr (.inr (.inl (.inr ⟨d, hd, rfl⟩)))
    · exact .inr (.inr (.inr h))

theorem length_witnesses (σ : Sig) :
    σ.witnesses.length =
      2 + (if 2 ≤ σ.args.length then σ.args.length else 0) + σ.degenerate.length +
        σ.clocks.length := by
  by_cases h : 2 ≤ σ.args.length <;> simp [witnesses, blinds, timeds, h] <;> omega

end Sig

@[expose] def witnesses (W : Type) [c : Covered W] : List (Witness c.sig) := c.sig.witnesses

section Meets

variable {W : Type} [c : Covered W]

@[expose] def Witness.Constant (w : W) : Prop := ∃ v, w = Degenerate.constantSubject v

@[expose] def Witness.BlindTo (i : Nat) (w : W) : Prop := (c.iso.to w).Ignores i

@[expose] def Witness.TimedBy (k : ArgClock c.sig.args) (w : W) : Prop := (c.iso.to w).ReadsOnly k

@[expose] def Witness.script (k : ArgClock c.sig.args) (s : k.Out → c.sig.out.denote) : W :=
  c.iso.inv (k.script s)

@[expose] def Witness.Meets (t : Witness c.sig) (q : Pair W) : Prop :=
  match t with
  | .vacuous => ∀ w, q.Met w
  | .table => ∀ x, q.pre x → ∃ w, Witness.Constant w ∧ q.post x w
  | .blind i => ∀ x, q.pre x → ∃ w, Witness.BlindTo i.val w ∧ q.post x w
  | .fixed d => ∃ w, d.Is w ∧ q.Met w
  | .timed k => ∀ x, q.pre x → ∃ w, Witness.TimedBy k w ∧ q.post x w

theorem Witness.timedBy_iff_script (k : ArgClock c.sig.args) (w : W) :
    Witness.TimedBy k w ↔ ∃ s, w = Witness.script k s := by
  unfold Witness.TimedBy Witness.script
  rw [ArgClock.readsOnly_iff_script]
  constructor
  · rintro ⟨s, e⟩
    exact ⟨s, by rw [← e, c.iso.inv_to]⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s, c.iso.to_inv _⟩

theorem Witness.timedBy_of_injective {k : ArgClock c.sig.args} (hk : Function.Injective k.read)
    (w : W) : Witness.TimedBy k w := fun xs ys e => by
  rw [hk e]

theorem Witness.timedBy_of_constant {w : W} (h : Witness.Constant w) (k : ArgClock c.sig.args) :
    Witness.TimedBy k w := by
  obtain ⟨v, rfl⟩ := h
  unfold Witness.TimedBy
  rw [Degenerate.iso_constantSubject]
  exact Sig.Fn.const_readsOnly v k

theorem Witness.blindTo_of_constant {w : W} (h : Witness.Constant w) (i : Nat) :
    Witness.BlindTo i w := by
  obtain ⟨v, rfl⟩ := h
  unfold Witness.BlindTo
  rw [Degenerate.iso_constantSubject]
  exact Sig.Fn.const_ignores v _ i

omit c in
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

theorem Witness.vacuous_meets_iff (q : Pair W) :
    (Witness.vacuous : Witness c.sig).Meets q ↔ ∀ s : q.Input → W, ∀ x, q.pre x → q.post x (s x) :=
  ⟨fun h s x hx => h (s x) x hx, fun h w x hx => h (fun _ => w) x hx⟩

theorem Witness.vacuous_meets_iff_post (q : Pair W) :
    (Witness.vacuous : Witness c.sig).Meets q ↔ ∀ x, q.pre x → ∀ w, q.post x w :=
  ⟨fun h x hx w => h w x hx, fun h w x hx => h x hx w⟩

theorem Witness.vacuous_meets_of_admits_nothing {q : Pair W} (h : ∀ x, ¬ q.pre x) :
    (Witness.vacuous : Witness c.sig).Meets q := fun _ x hx => absurd hx (h x)

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

theorem Witness.blind_meets_iff (q : Pair W) (i : Fin c.sig.args.length) :
    (Witness.blind i).Meets q ↔
      ∃ s : q.Input → W, (∀ x, Witness.BlindTo i.val (s x)) ∧ ∀ x, q.pre x → q.post x (s x) :=
  ⟨strategy_of_served (Witness.blindTo_of_constant ⟨c.sig.out.empty, rfl⟩ i.val),
    fun ⟨s, hs, h⟩ x hx => ⟨s x, hs x, h x hx⟩⟩

theorem Witness.fixed_meets_iff (q : Pair W) (d : Degenerate c.sig) :
    (Witness.fixed d).Meets q ↔ ∃ w, d.Is w ∧ ∀ x, q.pre x → q.post x w := Iff.rfl

theorem Witness.timed_meets_iff (q : Pair W) (k : ArgClock c.sig.args) :
    (Witness.timed k).Meets q ↔
      ∃ s : q.Input → W, (∀ x, Witness.TimedBy k (s x)) ∧ ∀ x, q.pre x → q.post x (s x) :=
  ⟨strategy_of_served (Witness.timedBy_of_constant ⟨c.sig.out.empty, rfl⟩ k),
    fun ⟨s, hs, h⟩ x hx => ⟨s x, hs x, h x hx⟩⟩

theorem Witness.timed_meets_iff_served (q : Pair W) {k : ArgClock c.sig.args}
    (hk : Function.Injective k.read) :
    (Witness.timed k).Meets q ↔ ∀ x, q.pre x → ∃ w, q.post x w :=
  ⟨fun h x hx => let ⟨w, _, hp⟩ := h x hx; ⟨w, hp⟩,
    fun h x hx => let ⟨w, hp⟩ := h x hx; ⟨w, Witness.timedBy_of_injective hk w, hp⟩⟩

theorem Witness.timed_meets_iff_script (q : Pair W) (k : ArgClock c.sig.args) :
    (Witness.timed k).Meets q ↔
      ∃ sc : q.Input → k.Out → c.sig.out.denote,
        ∀ x, q.pre x → q.post x (Witness.script k (sc x)) := by
  constructor
  · intro h
    have hc : ∀ x, ∃ f : k.Out → c.sig.out.denote,
        q.pre x → q.post x (Witness.script k f) :=
      fun x => by
        by_cases hx : q.pre x
        · obtain ⟨w, hw, hp⟩ := h x hx
          obtain ⟨f, rfl⟩ := (Witness.timedBy_iff_script k w).mp hw
          exact ⟨f, fun _ => hp⟩
        · exact ⟨fun _ => c.sig.out.empty, fun h' => absurd h' hx⟩
    exact Classical.axiomOfChoice hc
  · rintro ⟨sc, h⟩ x hx
    exact ⟨_, (Witness.timedBy_iff_script k _).mpr ⟨sc x, rfl⟩, h x hx⟩

theorem Witness.table_meets_of_met {q : Pair W} {v : c.sig.out.denote}
    (h : q.Met (Degenerate.constantSubject v)) : (Witness.table : Witness c.sig).Meets q :=
  fun x hx => ⟨_, ⟨v, rfl⟩, h x hx⟩

theorem Witness.table_meets_of_vacuous {q : Pair W}
    (h : (Witness.vacuous : Witness c.sig).Meets q) : (Witness.table : Witness c.sig).Meets q :=
  Witness.table_meets_of_met (v := c.sig.out.empty) (h _)

theorem Witness.blind_meets_of_table {q : Pair W} (i : Fin c.sig.args.length)
    (h : (Witness.table : Witness c.sig).Meets q) : (Witness.blind i).Meets q := fun x hx =>
  let ⟨w, hw, hp⟩ := h x hx
  ⟨w, Witness.blindTo_of_constant hw i.val, hp⟩

theorem Witness.blind_meets_of_met {q : Pair W} {i : Fin c.sig.args.length} {w : W}
    (hb : Witness.BlindTo i.val w) (h : q.Met w) : (Witness.blind i).Meets q :=
  fun x hx => ⟨w, hb, h x hx⟩

theorem Witness.fixed_meets_of_met {q : Pair W} {d : Degenerate c.sig} {w : W} (hi : d.Is w)
    (h : q.Met w) : (Witness.fixed d).Meets q := ⟨w, hi, h⟩

theorem Witness.timed_meets_of_table {q : Pair W} (k : ArgClock c.sig.args)
    (h : (Witness.table : Witness c.sig).Meets q) : (Witness.timed k).Meets q := fun x hx =>
  let ⟨w, hw, hp⟩ := h x hx
  ⟨w, Witness.timedBy_of_constant hw k, hp⟩

theorem Witness.timed_meets_of_met {q : Pair W} {k : ArgClock c.sig.args} {w : W}
    (hk : Witness.TimedBy k w) (h : q.Met w) : (Witness.timed k).Meets q :=
  fun x hx => ⟨w, hk, h x hx⟩

theorem Witness.oPair_constant_iff (q : Pair W) :
    OPair q Witness.Constant ↔ (∃ x, q.pre x) ∧ (Witness.table : Witness c.sig).Meets q := by
  obtain ⟨Input, pre, post⟩ := q
  rw [oPair_correct]
  exact Iff.rfl

theorem Witness.oPair_blindTo_iff (q : Pair W) (i : Fin c.sig.args.length) :
    OPair q (Witness.BlindTo i.val) ↔ (∃ x, q.pre x) ∧ (Witness.blind i).Meets q := by
  obtain ⟨Input, pre, post⟩ := q
  rw [oPair_correct]
  exact Iff.rfl

theorem Witness.oPair_timedBy_iff (q : Pair W) (k : ArgClock c.sig.args) :
    OPair q (Witness.TimedBy k) ↔ (∃ x, q.pre x) ∧ (Witness.timed k).Meets q := by
  obtain ⟨Input, pre, post⟩ := q
  rw [oPair_correct]
  exact Iff.rfl

theorem Witness.not_meets_of_unserved {q : Pair W} {x : q.Input} (hx : q.pre x)
    (h : ∀ w, ¬ q.post x w) : (t : Witness c.sig) → ¬ t.Meets q
  | .vacuous => fun hm => h _ (hm (Degenerate.constantSubject c.sig.out.empty) x hx)
  | .table => fun hm => let ⟨w, _, hp⟩ := hm x hx; h w hp
  | .blind _ => fun hm => let ⟨w, _, hp⟩ := hm x hx; h w hp
  | .fixed _ => fun ⟨w, _, hm⟩ => h w (hm x hx)
  | .timed _ => fun hm => let ⟨w, _, hp⟩ := hm x hx; h w hp

end Meets

section Class

variable {W : Type} [c : Covered W]

theorem Witness.vacuous_mem : (Witness.vacuous : Witness c.sig) ∈ witnesses W :=
  (Sig.mem_witnesses_iff _).mpr (.inl rfl)

theorem Witness.table_mem : (Witness.table : Witness c.sig) ∈ witnesses W :=
  (Sig.mem_witnesses_iff _).mpr (.inr (.inl rfl))

theorem Witness.blind_mem (h : 2 ≤ c.sig.args.length) (i : Fin c.sig.args.length) :
    Witness.blind i ∈ witnesses W :=
  (Sig.mem_witnesses_iff _).mpr (.inr (.inr (.inl ⟨h, i, rfl⟩)))

theorem Witness.fixed_mem {d : Degenerate c.sig} (hd : d ∈ degenerate W) :
    Witness.fixed d ∈ witnesses W :=
  (Sig.mem_witnesses_iff _).mpr (.inr (.inr (.inr (.inl ⟨d, hd, rfl⟩))))

theorem Witness.timed_mem {k : ArgClock c.sig.args}
    (hk : (∃ xs ys, xs ≠ ys ∧ k.read xs = k.read ys) ∨ k.InClock) :
    Witness.timed k ∈ witnesses W :=
  (Sig.mem_witnesses_iff _).mpr (.inr (.inr (.inr (.inr ⟨k, hk, rfl⟩))))

theorem witnesses_ne_nil (W : Type) [Covered W] : witnesses W ≠ [] :=
  List.ne_nil_of_mem Witness.vacuous_mem

@[expose] def Pair.MetTrivially (q : Pair W) : Prop :=
  (∀ s : q.Input → W, ∀ x, q.pre x → q.post x (s x)) ∨
    (∃ tab : q.Input → c.sig.out.denote,
      ∀ x, q.pre x → q.post x (Degenerate.constantSubject (tab x))) ∨
    (2 ≤ c.sig.args.length ∧ ∃ i < c.sig.args.length, ∃ s : q.Input → W,
      (∀ x, Witness.BlindTo i (s x)) ∧ ∀ x, q.pre x → q.post x (s x)) ∨
    (∃ d ∈ degenerate W, ∃ w, d.Is w ∧ ∀ x, q.pre x → q.post x w) ∨
    ∃ k : ArgClock c.sig.args, ((∃ xs ys, xs ≠ ys ∧ k.read xs = k.read ys) ∨ k.InClock) ∧
      ∃ sc : q.Input → k.Out → c.sig.out.denote,
        ∀ x, q.pre x → q.post x (Witness.script k (sc x))

theorem metTrivially_iff (q : Pair W) : q.MetTrivially ↔ ∃ t ∈ witnesses W, t.Meets q := by
  constructor
  · rintro (h | h | ⟨hn, i, hi, h⟩ | ⟨d, hd, h⟩ | ⟨k, hk, h⟩)
    · exact ⟨_, Witness.vacuous_mem, (Witness.vacuous_meets_iff q).mpr h⟩
    · exact ⟨_, Witness.table_mem, (Witness.table_meets_iff q).mpr h⟩
    · exact ⟨_, Witness.blind_mem hn ⟨i, hi⟩, (Witness.blind_meets_iff q ⟨i, hi⟩).mpr h⟩
    · exact ⟨_, Witness.fixed_mem hd, h⟩
    · exact ⟨_, Witness.timed_mem hk, (Witness.timed_meets_iff_script q k).mpr h⟩
  · rintro ⟨t, ht, hm⟩
    rcases (Sig.mem_witnesses_iff t).mp ht with
      rfl | rfl | ⟨hn, i, rfl⟩ | ⟨d, hd, rfl⟩ | ⟨k, hk, rfl⟩
    · exact .inl ((Witness.vacuous_meets_iff q).mp hm)
    · exact .inr (.inl ((Witness.table_meets_iff q).mp hm))
    · exact .inr (.inr (.inl ⟨hn, i.val, i.isLt, (Witness.blind_meets_iff q i).mp hm⟩))
    · exact .inr (.inr (.inr (.inl ⟨d, hd, hm⟩)))
    · exact .inr (.inr (.inr (.inr ⟨k, hk, (Witness.timed_meets_iff_script q k).mp hm⟩)))

end Class

section Verdicts

variable {W : Type} [c : Covered W]

@[expose] def witnessGoal (q : Pair W) (t : Witness c.sig) : Bool → Prop
  | true => t.Meets q
  | false => ¬ t.Meets q

@[expose] def witnessGoals (q : Pair W) : List (Witness c.sig) → List Bool → List Prop
  | [], [] => []
  | t :: ts, b :: bs => witnessGoal q t b :: witnessGoals q ts bs
  | _, _ => [False]

@[expose] def witnessVerdicts (q : Pair W) (bs : List Bool) : List Prop :=
  if c.sig.strayClock then [False] else witnessGoals q (witnesses W) bs

@[expose] def WitnessVerdicts (q : Pair W) (bs : List Bool) : Prop := Goals (witnessVerdicts q bs)

@[expose] def intendedWitnessVerdicts (q : Pair W) (bs : List Bool) : Prop :=
  c.sig.strayClock = false ∧ bs.length = (witnesses W).length ∧
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

theorem witnessVerdicts_correct (q : Pair W) (bs : List Bool) :
    WitnessVerdicts q bs ↔ intendedWitnessVerdicts q bs := by
  rw [WitnessVerdicts, witnessVerdicts, intendedWitnessVerdicts]
  cases h : c.sig.strayClock
  · simp only [Bool.false_eq_true, ↓reduceIte, true_and]
    exact goals_witnessGoals q _ bs
  · simp [Goals]

theorem not_witnessVerdicts_of_strayClock (h : c.sig.strayClock = true) (q : Pair W)
    (bs : List Bool) : ¬ WitnessVerdicts q bs := by
  rw [witnessVerdicts_correct]
  rintro ⟨hs, _⟩
  rw [h] at hs
  exact Bool.noConfusion hs

theorem timed_mem_of_namedClock {q : Pair W} {bs : List Bool} (h : WitnessVerdicts q bs)
    (i : Nat) (hi : i < c.sig.args.length) (o : Ty.NamedClock c.sig.args[i]) :
    ∃ (p : Σ p, Place.Path (.code c.sig.args[i]) p) (r : Place.ArgPath p.1 c.sig.args),
      o.path? = some p ∧ r.From p.2 i ∧ ArgClock.InClock ⟨p.1, r, .value⟩ ∧
        Witness.timed ⟨p.1, r, .value⟩ ∈ witnesses W := by
  obtain ⟨p, r, hp, hr, hk⟩ :=
    Sig.read_of_strayClock_eq_false ((witnessVerdicts_correct q bs).mp h).1 i hi o
  exact ⟨p, r, hp, hr, hk, Witness.timed_mem (.inr hk)⟩

theorem goals_of_witnessVerdicts {q : Pair W} {bs : List Bool} (h : WitnessVerdicts q bs) :
    Goals (witnessGoals q (witnesses W) bs) := by
  unfold WitnessVerdicts witnessVerdicts at h
  split at h
  · exact absurd h.1 id
  · exact h

@[expose] def reportedGo {σ : Sig} : List (Witness σ) → List Bool → List (Witness σ)
  | t :: ts, true :: bs => t :: reportedGo ts bs
  | _ :: ts, false :: bs => reportedGo ts bs
  | _, _ => []

@[expose] def reported (W : Type) [c : Covered W] (bs : List Bool) : List (Witness c.sig) :=
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

theorem mem_reported {q : Pair W} {bs : List Bool} (h : WitnessVerdicts q bs) (t : Witness c.sig) :
    t ∈ reported W bs ↔ t ∈ witnesses W ∧ t.Meets q :=
  mem_reportedGo q t _ bs (goals_of_witnessVerdicts h)

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
