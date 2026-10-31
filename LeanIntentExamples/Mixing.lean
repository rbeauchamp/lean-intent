import LeanIntent.Progress

/-!
# O2 before running, for a property over all 64-bit inputs

The record here is the shape the Acorn pilot wrote for a pair of hash functions on three 64-bit words
(rbeauchamp/acorn, `AcornVerif.Intent.Hash`): changing any one input always moves the spot, and no
fixed rule of reordering the inputs and shifting each by a fixed amount, by exclusive or or by
addition, keeps every spot. Proved of a real mixing function, the second property is a statement about
every one of 2^64 differences, which the pilot left open. Evaluating it is out of reach.

O2 before running does not ask that. It asks that the record has a model, and any model will do: one
built to make the proof short, not the mixing function the project runs. This file is the recipe
[the obligations' document](../docs/obligations.md) states, carried out:

1. Take a function that is linear in the shifts: `x₁ ^^^ x₂ ^^^ x₃` keeps a shift of two inputs
   by one amount, so it fails the record by exactly the shifts of the rules.
2. Break that symmetry at a few chosen words: `scramble` exchanges 0 with 1 and 2 with a word that
   differs for each input, and is otherwise the identity. An exchange of one pair alone would not
   do, since it commutes with exclusive or by the pair's difference; the two pairs have no common
   difference, and the second pair differs by input so that no reordering is a symmetry.
3. Separate the variables (`separate`): a sum of functions of one input each keeps its spot only if
   each input's own difference is constant, so every rule reduces to one statement about one input.
4. Reduce that statement to finitely many words by algebra, never by enumerating a 64-bit domain:
   for exclusive or (`rigid_flip`) the amount is one of two words; for addition (`rigid_add`) twice
   the amount is below 32, which leaves 32 words, each refuted by Lean's kernel at a few inputs
   (`table`).

`hashes_o2Run` is the result. It rests on Lean's axioms alone. Algebra reduces the quantified shift
domain to a finite check of 32 candidate additive shifts for each of nine pairs of places, rather
than enumerating all 64-bit words; the document states the bound it was measured under.

What this does not establish: that any function a project runs meets the record. `model` is no hash
function, and `hashes_o2Run` says only that the record does not contradict itself. Whether a real
mixing function meets it is a separate obligation of the implementation (`IntentRecord.Fulfilled`),
which this recipe leaves as open as it found it.
-/

namespace LeanIntentExamples.Mixing

open LeanIntent

/-! ## The record -/

/-- Three 64-bit inputs. -/
abbrev Inputs := UInt64 × UInt64 × UInt64

/-- The two hash functions, each taking three 64-bit inputs to a 64-bit spot. -/
structure Hashes where
  /-- The first function. -/
  hash2 : Inputs → UInt64
  /-- The second function. -/
  hash3 : Inputs → UInt64

/-- An order of three inputs: which input goes first, second and third. -/
inductive Order where
  /-- The inputs as given. -/
  | abc
  /-- The first two exchanged. -/
  | bac
  /-- The last two exchanged. -/
  | acb
  /-- The first and last exchanged. -/
  | cba
  /-- Each moved one place left. -/
  | bca
  /-- Each moved one place right. -/
  | cab

/-- The inputs put in the order `o`. -/
def Order.apply : Order → Inputs → Inputs
  | .abc, (a, b, c) => (a, b, c)
  | .bac, (a, b, c) => (b, a, c)
  | .acb, (a, b, c) => (a, c, b)
  | .cba, (a, b, c) => (c, b, a)
  | .bca, (a, b, c) => (b, c, a)
  | .cab, (a, b, c) => (c, a, b)

/-- The two ways a rule shifts each input by a fixed amount. -/
inductive Shift where
  /-- Flipping the bits set in the amount: exclusive or. -/
  | flip
  /-- Adding the amount, wrapping around at 2^64. -/
  | add

/-- One input shifted by `d`. -/
def Shift.apply : Shift → UInt64 → UInt64 → UInt64
  | .flip, x, d => x ^^^ d
  | .add, x, d => x + d

/-- A fixed rule: reorder the inputs, then shift each by its own fixed amount. -/
structure Rule where
  /-- The reordering. -/
  order : Order
  /-- How the amounts are applied. -/
  shift : Shift
  /-- The amounts, one for each input in its new place. -/
  amount : Inputs

/-- The inputs the rule `r` moves `x` to. -/
def Rule.apply (r : Rule) (x : Inputs) : Inputs :=
  let (a, b, c) := r.order.apply x
  (r.shift.apply a r.amount.1, r.shift.apply b r.amount.2.1, r.shift.apply c r.amount.2.2)

/-- The rule `r` moves inputs: it is not the rule that keeps the inputs in their given order and
shifts them by nothing. -/
def Rule.Moves (r : Rule) : Prop := ¬ (r.order = .abc ∧ r.amount = (0, 0, 0))

/-- Changing exactly one input of `f`, the others kept, always changes the spot. -/
def OneInputMoves (f : Inputs → UInt64) : Prop :=
  (∀ a a' b c, f (a, b, c) = f (a', b, c) → a = a') ∧
    (∀ a b b' c, f (a, b, c) = f (a, b', c) → b = b') ∧
    (∀ a b c c', f (a, b, c) = f (a, b, c') → c = c')

/-- No rule that moves inputs keeps the spot of every input of `f`. -/
def NoRuleKeepsSpots (f : Inputs → UInt64) : Prop :=
  ∀ r : Rule, r.Moves → ∃ x, f (r.apply x) ≠ f x

/-- The intent record of the two functions, a description made of functions with no state. -/
def hashes : IntentRecord Hashes where
  shape := .bundle (fun _ => ()) ⟨"hash2", Inputs, UInt64, fun w => w.hash2⟩
    [⟨"hash3", Inputs, UInt64, fun w => w.hash3⟩]
  dom := []
  props :=
    [⟨"changing any one input always moves the spot", fun w =>
        OneInputMoves w.hash2 ∧ OneInputMoves w.hash3⟩,
      ⟨"no fixed rule of reordering and shifting the inputs keeps every spot", fun w =>
        NoRuleKeepsSpots w.hash2 ∧ NoRuleKeepsSpots w.hash3⟩]
  vocab := [⟨"same spot", UInt64 × UInt64, fun p => p.1 = p.2⟩]

/-- A pair of functions meets the record exactly when each moves its spot on any one changed input
and no moving rule keeps every spot of either. -/
theorem hashes_meets {w : Hashes} :
    hashes.Meets w ↔ (OneInputMoves w.hash2 ∧ OneInputMoves w.hash3) ∧
      (NoRuleKeepsSpots w.hash2 ∧ NoRuleKeepsSpots w.hash3) := by
  constructor
  · intro h
    exact ⟨h.2 _ (List.mem_cons_self ..), h.2 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))⟩
  · intro ⟨h1, h2⟩
    refine ⟨(fun _ hd => nomatch hd), fun p hp => ?_⟩
    simp only [hashes, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact h1
    · exact h2

/-! ## The model -/

/-- The three places of the inputs, each scrambled differently. -/
inductive Place where
  | first
  | second
  | third
  deriving DecidableEq

/-- What tells the places apart: the difference of the second pair `scramble` exchanges. -/
def Place.mask : Place → UInt64
  | .first => 6
  | .second => 10
  | .third => 18

/-- What `scramble` flips in a word. -/
def kick (p : Place) (x : UInt64) : UInt64 :=
  if x = 0 ∨ x = 1 then 1 else if x = 2 ∨ x = 2 ^^^ p.mask then p.mask else 0

/-- The identity, except that 0 and 1 are exchanged, and 2 and `2 ^^^ p.mask`. -/
def scramble (p : Place) (x : UInt64) : UInt64 := x ^^^ kick p x

/-- A function of three inputs, one scrambled word for each. -/
def mix (x : Inputs) : UInt64 :=
  scramble .first x.1 ^^^ scramble .second x.2.1 ^^^ scramble .third x.2.2

/-- The model of the record. It is no hash function. -/
def model : Hashes := ⟨mix, mix⟩

/-! ## Exclusive or -/

theorem xor_left_comm' (a b c : UInt64) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← UInt64.xor_assoc, UInt64.xor_comm a b, UInt64.xor_assoc]

theorem xor_cancel_self (a b : UInt64) : a ^^^ (a ^^^ b) = b := by
  rw [← UInt64.xor_assoc, UInt64.xor_self, UInt64.zero_xor]

/-- Normalize sums of words under exclusive or, cancelling what occurs twice. -/
macro "xor_norm" : tactic =>
  `(tactic| simp only [UInt64.xor_assoc, UInt64.xor_comm, xor_left_comm', xor_cancel_self,
    UInt64.xor_self, UInt64.zero_xor, UInt64.xor_zero])

/-- The same, in a hypothesis. -/
macro "xor_norm_at " h:ident : tactic =>
  `(tactic| simp only [UInt64.xor_assoc, UInt64.xor_comm, xor_left_comm', xor_cancel_self,
    UInt64.xor_self, UInt64.zero_xor, UInt64.xor_zero] at $h:ident)

theorem xor_cancel_right {a b k : UInt64} (h : a ^^^ k = b ^^^ k) : a = b := by
  have := congrArg (· ^^^ k) h
  simpa [UInt64.xor_assoc] using this

theorem xor_cancel_left {a b k : UInt64} (h : k ^^^ a = k ^^^ b) : a = b := by
  have := congrArg (k ^^^ ·) h
  simpa only [xor_cancel_self] using this

theorem xor_lt_32 {a b : UInt64} (ha : a.toNat < 32) (hb : b.toNat < 32) : (a ^^^ b).toNat < 32 := by
  rw [UInt64.toNat_xor]
  exact Nat.xor_lt_two_pow (n := 5) ha hb

/-! ## `scramble` -/

/-- What `kick` flips and where: 1 at 0 and 1, the mask at the second pair, and nothing elsewhere. -/
theorem kick_cases (p : Place) (x : UInt64) :
    (kick p x = 1 ∧ (x = 0 ∨ x = 1)) ∨ (kick p x = p.mask ∧ (x = 2 ∨ x = 2 ^^^ p.mask)) ∨
      (kick p x = 0 ∧ ¬ (x = 0 ∨ x = 1) ∧ ¬ (x = 2 ∨ x = 2 ^^^ p.mask)) := by
  unfold kick
  by_cases h₁ : x = 0 ∨ x = 1
  · exact .inl ⟨ite_eq_left h₁, h₁⟩
  · by_cases h₂ : x = 2 ∨ x = 2 ^^^ p.mask
    · exact .inr (.inl ⟨by rw [ite_eq_right h₁, ite_eq_left h₂], h₂⟩)
    · exact .inr (.inr ⟨by rw [ite_eq_right h₁, ite_eq_right h₂], h₁, h₂⟩)

/-- What `kick` flips lies below 32. -/
theorem kick_lt (p : Place) (x : UInt64) : (kick p x).toNat < 32 := by
  rcases kick_cases p x with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> cases p <;> decide

/-- A word `kick` flips something in lies below 32. -/
theorem lt_of_kick_ne {p : Place} {x : UInt64} (hne : kick p x ≠ 0) : x.toNat < 32 := by
  rcases kick_cases p x with ⟨_, rfl | rfl⟩ | ⟨_, rfl | rfl⟩ | ⟨h, _⟩
  · decide
  · decide
  · decide
  · cases p <;> decide
  · exact absurd h hne

/-- `scramble` undoes itself. -/
theorem scramble_scramble (p : Place) (x : UInt64) : scramble p (scramble p x) = x := by
  rcases kick_cases p x with ⟨_, rfl | rfl⟩ | ⟨_, rfl | rfl⟩ | ⟨h, _, _⟩
  · cases p <;> decide
  · cases p <;> decide
  · cases p <;> decide
  · cases p <;> decide
  · unfold scramble
    rw [h, UInt64.xor_zero, h, UInt64.xor_zero]

/-- So `scramble` is injective. -/
theorem scramble_injective (p : Place) {x y : UInt64} (h : scramble p x = scramble p y) : x = y := by
  rw [← scramble_scramble p x, h, scramble_scramble]

/-! ## Separating the variables -/

/-- A sum of a function of one input and a rest that does not depend on it, equal on both sides:
the input's own difference is constant. -/
theorem separate {u v : UInt64 → UInt64} {k l : UInt64} (h : ∀ x, u x ^^^ k = v x ^^^ l)
    (x y : UInt64) : u x ^^^ v x = u y ^^^ v y := by
  have key : ∀ z, u z ^^^ v z = k ^^^ l := fun z => by
    have hz := congrArg (· ^^^ (v z ^^^ k)) (h z)
    xor_norm_at hz
    try xor_norm
    exact hz
  rw [key x, key y]

/-! ## One input's difference is constant only at no shift -/

/-- Under exclusive or, a difference that is constant means the same place and no shift. -/
theorem rigid_flip (i j : Place) (d : UInt64)
    (H : ∀ x y, scramble i (x ^^^ d) ^^^ scramble j x = scramble i (y ^^^ d) ^^^ scramble j y) :
    i = j ∧ d = 0 := by
  have H' : ∀ x y, kick i (x ^^^ d) ^^^ kick j x = kick i (y ^^^ d) ^^^ kick j y := fun x y => by
    have hx : scramble i (x ^^^ d) ^^^ scramble j x = d ^^^ (kick i (x ^^^ d) ^^^ kick j x) := by
      unfold scramble
      xor_norm
    have hy : scramble i (y ^^^ d) ^^^ scramble j y = d ^^^ (kick i (y ^^^ d) ^^^ kick j y) := by
      unfold scramble
      xor_norm
    exact xor_cancel_left (k := d) (hx.symm.trans ((H x y).trans hy))
  have fj : ∀ w : UInt64, (w = 1024 ∨ w = 1048576) → kick j w = 0 := by
    rintro w (rfl | rfl) <;> cases j <;> decide
  have hu := H' 1024 1048576
  rw [fj 1024 (.inl rfl), fj 1048576 (.inr rfl), UInt64.xor_zero, UInt64.xor_zero] at hu
  have hu0 : kick i (1024 ^^^ d) = 0 := by
    refine Classical.byContradiction fun hne => ?_
    have hlt := xor_lt_32 (lt_of_kick_ne hne) (lt_of_kick_ne (hu ▸ hne))
    have e : (1024 ^^^ d) ^^^ (1048576 ^^^ d) = (1024 ^^^ 1048576 : UInt64) := by xor_norm
    rw [e] at hlt
    exact absurd hlt (by decide)
  have hc : ∀ x, kick i (x ^^^ d) = kick j x := fun x => by
    have := H' x 1024
    rw [fj 1024 (.inl rfl), hu0, UInt64.xor_zero] at this
    have h' := congrArg (· ^^^ kick j x) this
    xor_norm_at h'
    try xor_norm
    exact h'
  have h0 := hc 0
  rw [UInt64.zero_xor] at h0
  have hd : d = 0 ∨ d = 1 := by
    rcases kick_cases i d with ⟨_, hx⟩ | ⟨h, _⟩ | ⟨h, _⟩
    · exact hx
    · rw [h] at h0
      exact absurd h0 (by cases i <;> cases j <;> decide)
    · rw [h] at h0
      exact absurd h0 (by cases j <;> decide)
  have h2 := hc 2
  rcases hd with rfl | rfl <;> revert h2 <;> cases i <;> cases j <;> decide

/-- The words whose double lies below 32. -/
def candidate (k : Fin 32) : UInt64 :=
  UInt64.ofNat (if k.val < 16 then k.val else 9223372036854775808 + k.val - 16)

/-- A word whose double lies below 32 is a candidate. -/
theorem exists_candidate {d : UInt64} (h : (d + d).toNat < 32) : ∃ k, d = candidate k := by
  have hd := d.toNat_lt
  rw [UInt64.toNat_add] at h
  by_cases hs : d.toNat < 16
  · refine ⟨⟨d.toNat, by omega⟩, ?_⟩
    show d = UInt64.ofNat (if d.toNat < 16 then d.toNat else _)
    rw [ite_eq_left hs, UInt64.ofNat_toNat]
  · refine ⟨⟨d.toNat - 9223372036854775808 + 16, by omega⟩, ?_⟩
    show d = UInt64.ofNat (if d.toNat - 9223372036854775808 + 16 < 16 then _ else
      9223372036854775808 + (d.toNat - 9223372036854775808 + 16) - 16)
    rw [ite_eq_right (by omega), show 9223372036854775808 + (d.toNat - 9223372036854775808 + 16) - 16 =
      d.toNat by omega, UInt64.ofNat_toNat]

/-- The inputs at which each candidate is refuted. -/
def probes : List UInt64 := [1, 2, 3, 4, 5, 8, 16, 1024]

/-- The difference at `x` of an input shifted by adding `d`. -/
def addDifference (i j : Place) (d x : UInt64) : UInt64 := scramble i (x + d) ^^^ scramble j x

/-- Lean's kernel refutes each candidate at the probes, for every pair of places, except no shift at
one place. These are 288 evaluations at a few words each. -/
theorem table (i j : Place) : ∀ k : Fin 32,
    (∀ x ∈ probes, addDifference i j (candidate k) x = addDifference i j (candidate k) 0) →
      i = j ∧ candidate k = 0 := by
  cases i <;> cases j <;> decide +kernel

/-- Under addition, a difference that is constant means the same place and no shift. -/
theorem rigid_add (i j : Place) (d : UInt64)
    (H : ∀ x y, scramble i (x + d) ^^^ scramble j x = scramble i (y + d) ^^^ scramble j y) :
    i = j ∧ d = 0 := by
  have h := H 0 d
  rw [UInt64.zero_add] at h
  have e : d + d = kick i d ^^^ (kick j 0 ^^^ (kick i (d + d) ^^^ kick j d)) := by
    have h' := congrArg (· ^^^ (d ^^^ (kick i (d + d) ^^^ kick j d))) h
    simp only [scramble] at h'
    xor_norm_at h'
    xor_norm
    exact h'.symm
  have hlt : (d + d).toNat < 32 := by
    rw [e]
    exact xor_lt_32 (kick_lt _ _) (xor_lt_32 (kick_lt _ _) (xor_lt_32 (kick_lt _ _) (kick_lt _ _)))
  obtain ⟨k, rfl⟩ := exists_candidate hlt
  exact table i j k fun x _ => H x 0

/-- For either shift, a difference that is constant means the same place and no shift. -/
theorem rigid (s : Shift) (i j : Place) (d : UInt64)
    (H : ∀ x y, scramble i (s.apply x d) ^^^ scramble j x =
      scramble i (s.apply y d) ^^^ scramble j y) : i = j ∧ d = 0 := by
  cases s
  · exact rigid_flip i j d H
  · exact rigid_add i j d H

/-! ## The model meets the record -/

/-- Changing any one input of `mix` moves its spot. -/
theorem mix_oneInputMoves : OneInputMoves mix :=
  ⟨fun _ _ _ _ h => scramble_injective .first (xor_cancel_right (xor_cancel_right h)),
    fun _ _ _ _ h => scramble_injective .second (xor_cancel_left (xor_cancel_right h)),
    fun _ _ _ _ h => scramble_injective .third (xor_cancel_left h)⟩

/-- No rule that moves inputs keeps every spot of `mix`: the input a reordering moves to another
place, or an amount that is not zero, has a difference that is not constant. -/
theorem mix_noRuleKeepsSpots : NoRuleKeepsSpots mix := by
  rintro ⟨o, s, d₁, d₂, d₃⟩ hm
  refine Classical.byContradiction fun hn => ?_
  have H : ∀ a b c, mix ((⟨o, s, (d₁, d₂, d₃)⟩ : Rule).apply (a, b, c)) = mix (a, b, c) :=
    fun a b c => Classical.byContradiction fun h => hn ⟨_, h⟩
  let S := scramble
  let σ := s.apply
  cases o with
  | abc =>
    have H' : ∀ a b c, S .first (σ a d₁) ^^^ S .second (σ b d₂) ^^^ S .third (σ c d₃) =
        S .first a ^^^ S .second b ^^^ S .third c := H
    have h₁ := (rigid s .first .first d₁ (separate (k := S .second (σ 0 d₂) ^^^ S .third (σ 0 d₃))
      (l := S .second 0 ^^^ S .third 0) fun x => by
        have := H' x 0 0; xor_norm_at this; try xor_norm
        exact this)).2
    have h₂ := (rigid s .second .second d₂ (separate (k := S .first (σ 0 d₁) ^^^ S .third (σ 0 d₃))
      (l := S .first 0 ^^^ S .third 0) fun x => by
        have := H' 0 x 0; xor_norm_at this; try xor_norm
        exact this)).2
    have h₃ := (rigid s .third .third d₃ (separate (k := S .first (σ 0 d₁) ^^^ S .second (σ 0 d₂))
      (l := S .first 0 ^^^ S .second 0) fun x => by
        have := H' 0 0 x; xor_norm_at this; try xor_norm
        exact this)).2
    subst h₁ h₂ h₃
    exact hm ⟨rfl, rfl⟩
  | bac =>
    have H' : ∀ a b c, S .first (σ b d₁) ^^^ S .second (σ a d₂) ^^^ S .third (σ c d₃) =
        S .first a ^^^ S .second b ^^^ S .third c := H
    exact absurd (rigid s .second .first d₂ (separate (k := S .first (σ 0 d₁) ^^^ S .third (σ 0 d₃))
      (l := S .second 0 ^^^ S .third 0) fun x => by
        have := H' x 0 0; xor_norm_at this; try xor_norm
        exact this)).1 (by decide)
  | acb =>
    have H' : ∀ a b c, S .first (σ a d₁) ^^^ S .second (σ c d₂) ^^^ S .third (σ b d₃) =
        S .first a ^^^ S .second b ^^^ S .third c := H
    exact absurd (rigid s .third .second d₃ (separate (k := S .first (σ 0 d₁) ^^^ S .second (σ 0 d₂))
      (l := S .first 0 ^^^ S .third 0) fun x => by
        have := H' 0 x 0; xor_norm_at this; try xor_norm
        exact this)).1 (by decide)
  | cba =>
    have H' : ∀ a b c, S .first (σ c d₁) ^^^ S .second (σ b d₂) ^^^ S .third (σ a d₃) =
        S .first a ^^^ S .second b ^^^ S .third c := H
    exact absurd (rigid s .third .first d₃ (separate (k := S .first (σ 0 d₁) ^^^ S .second (σ 0 d₂))
      (l := S .second 0 ^^^ S .third 0) fun x => by
        have := H' x 0 0; xor_norm_at this; try xor_norm
        exact this)).1 (by decide)
  | bca =>
    have H' : ∀ a b c, S .first (σ b d₁) ^^^ S .second (σ c d₂) ^^^ S .third (σ a d₃) =
        S .first a ^^^ S .second b ^^^ S .third c := H
    exact absurd (rigid s .third .first d₃ (separate (k := S .first (σ 0 d₁) ^^^ S .second (σ 0 d₂))
      (l := S .second 0 ^^^ S .third 0) fun x => by
        have := H' x 0 0; xor_norm_at this; try xor_norm
        exact this)).1 (by decide)
  | cab =>
    have H' : ∀ a b c, S .first (σ c d₁) ^^^ S .second (σ a d₂) ^^^ S .third (σ b d₃) =
        S .first a ^^^ S .second b ^^^ S .third c := H
    exact absurd (rigid s .second .first d₂ (separate (k := S .first (σ 0 d₁) ^^^ S .third (σ 0 d₃))
      (l := S .second 0 ^^^ S .third 0) fun x => by
        have := H' x 0 0; xor_norm_at this; try xor_norm
        exact this)).1 (by decide)

/-- **O2 before running**: the whole record has a model, for a property over every 64-bit input,
with no evaluation over that domain. -/
theorem hashes_o2Run : O2Run hashes :=
  o2Run_of_meets (w := model) (hashes_meets.mpr
    ⟨⟨mix_oneInputMoves, mix_oneInputMoves⟩, ⟨mix_noRuleKeepsSpots, mix_noRuleKeepsSpots⟩⟩)

/-! ## The other obligations -/

/-- The pair whose functions both send every input to spot 0. -/
def constantZero : Hashes := ⟨fun _ => 0, fun _ => 0⟩

/-- O2: the record has a model of its (empty) domain hypotheses and an instance of its one
vocabulary predicate. -/
theorem hashes_o2 : O2 hashes := by
  refine (o2_correct _).mpr ⟨⟨constantZero, fun _ h => nomatch h⟩, ?_⟩
  intro p hp
  simp only [hashes, List.mem_cons, List.not_mem_nil, or_false] at hp
  subst hp
  exact ⟨(0, 0), rfl⟩

/-- O3: each property fails of the pair that sends everything to spot 0. -/
theorem hashes_o3 : O3 hashes := by
  refine (o3_correct _).mpr fun p hp => ?_
  simp only [hashes, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨constantZero, fun h => absurd (h.1.1 0 1 0 0 rfl) (by decide)⟩
  · refine ⟨constantZero, fun h => ?_⟩
    obtain ⟨x, hx⟩ := h.1 ⟨.abc, .add, (1, 0, 0)⟩ (fun h => absurd (congrArg (·.1) h.2) (by decide))
    exact hx rfl

/-- O4: the two functions are the whole subject, each can be any function of its type, and a pair in
which either ignores its input fails the record. A pair with `constantZero`'s functions, which
declared as a plain value O4 would ask nothing about, is refused. -/
theorem hashes_o4 : O4 hashes := by
  refine o4_of_idle _ ⟨?_, ?_⟩ ?_
  · rintro ⟨a, b⟩ ⟨a', b'⟩ - h
    have h₁ := h ⟨"hash2", Inputs, UInt64, fun w => w.hash2⟩ (List.mem_cons_self ..)
    have h₂ := h ⟨"hash3", Inputs, UInt64, fun w => w.hash3⟩ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    cases h₁
    cases h₂
    rfl
  · intro m hm f
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact ⟨⟨f, fun _ => 0⟩, rfl⟩
    · exact ⟨⟨fun _ => 0, f⟩, rfl⟩
  · rintro w ⟨m, hm, hig⟩ hw
    obtain ⟨⟨h₂, h₃⟩, -⟩ := hashes_meets.mp hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact absurd (h₂.1 0 1 0 0 (hig _ _)) (by decide)
    · exact absurd (h₃.1 0 1 0 0 (hig _ _)) (by decide)

/-- O5 with the widest freedom, which every record meets. -/
theorem hashes_o5_widest : O5 hashes .widest := o5_widest _

end LeanIntentExamples.Mixing
