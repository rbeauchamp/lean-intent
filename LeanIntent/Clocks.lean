import LeanIntent.Declared

/-!
# The clocks inside a subject's arguments

A script of timed actions is a subject that reads its clock and not what it sees: a function of the
time alone. The trivial-witness check (`LeanIntent.TrivialWitnesses`) holds, for each clock its
class takes, the member that offers at each input a subject that reads only that clock. Lean's
logic cannot ask which part of an argument a project means as its clock, so this module fixes,
from a subject's code alone, the parts that can be one, and the one way a project declares a part
its clock where the code alone cannot tell.

## Clock parts

A *clock part* of a function's arguments (`ArgClock`) is a component of one argument reached
through its data, applying no function (`Place.ArgPath`, `Place.Path`, `Place.FieldPath`), with a
reading of it (`ClockRead`). A component lies at a *place* (`Place`): a value of a code, or a tree of
one type of a recursive group, the `l`-th, which may be one no code denotes, such as a type of the
group that does not grow. The components are the argument itself, a component of one side of a
pair, and a component of a field of a declared type whose values all have one shape, each of any
covered type:

* a chain of fields, the representation of a type with one constructor, such as a structure;
* a `Ty.mu` whose values are all base values, and a tree of the group's root with no other
  constructor, whose fields are those of the base's chain;
* a tree of a type of the group that is not the root and has one constructor, such as a rose tree
  `node (label : Nat) (kids : List Rose)`: the fields of its data, the chain of its fields that
  hold no value of the group (`Ty.ctorData`), and each child at a recursive field that holds a value
  of the group itself (whose arguments' code is the unit code), read whole as a tree of its own type
  and then by its own fields, by the same rule.

A component is read as its value, of its own type, or as a number: the length of a list, the size
of an array, or the length of a tree of a type of the group shaped as a list (`Ty.listShaped`,
`Ty.treeLen`): each of its constructors has at most one recursive field that holds the type itself,
some constructor has one, and the length counts the nodes along it, so that a type a project declares
with the shape of a list, as Lean's `List T` nested in a group is, has its length read too.
`ArgClock.read` reads a clock part from a tuple of arguments. A part that does not exist, such as the
element of a list, a side of a sum, a field of a type with several constructors (a type of a group
with base values and nodes, or with several constructors, included) or what a function returns (a
recursive field that holds a function included), has no such path, so Lean refuses to elaborate it
and no declaration can name it. `ArgClock.all` lists every clock part (`ArgClock.mem_all`), from
every component of each argument (`Ty.paths`, `Place.Path.mem_paths`) and every reading of each
(`ClockRead.all`, `ClockRead.mem_all`). The functions that list components (`Ty.paths`,
`Ty.fieldPaths`) match every code former with no catch-all case, so a former added to `Ty` must
state its components before the library builds.

A path into a group descends into a child only through a node of a type with one constructor, and
it descends at most as many times as the group has types (`r.items`), a bound its place carries,
so the components are finitely many whatever the code. The bound loses no component of a value: a
value is a finite tree, so a path that reached the same type of the group twice through such nodes
would give every value of that type a strictly smaller value of the same type below it, and such a
type has no value; the nodes such a path passes through are of distinct types, each listed in `r`,
since a type with a constructor is, so a path through a value has at most `r.items` of them.

## Which parts are clocks

* **By the subject's type alone**, each clock part whose reading does not determine the arguments:
  two tuples of arguments read the same there and differ (`ArgClock.determines_eq_false_iff`,
  `ArgClock.determines_iff`). Whether it does is decided from the codes, exactly: along the path,
  the rest of each pair, chain or node has one value, and the reading determines the component.
  For a tree, whether a type of the group has a value (`Ty.treeInh_iff`), has two
  (`Ty.treeMulti_iff`), and whether a tree's length determines it (`Ty.lenDet_iff`) are decided by
  rounds over the group's types, which settle within as many rounds as there are types to mark
  (`Ty.roundsOf_bound`). A rose tree's label does not determine the tree, so the class holds the
  script on it; the one field of a structure that holds an option of itself does.
  A subject that reads only such a part does not read the rest of its arguments, a real restriction,
  as not reading one argument is. Where the part is in fact what the subject sees and the rest its
  clock, such a subject is one that ignores its clock, which the class holds for whole arguments
  already; a report of it is a true statement about the pair either way.
* **By the project's declaration**, each clock part that is a value of type `LeanIntent.Clock α`
  (`ArgClock.InClock`): a structure of one field, the tick, of any covered type `α`, which a project
  gives to the part of its subject's arguments it means as its clock. A part whose reading
  determines the arguments, such as the only argument of a policy of type `Nat → Act`, is all the
  subject has to read: every subject reads only it, so reading it as a clock makes every subject a
  script, and reading it as what the subject sees makes none. The type alone cannot tell the two
  apart, so it reads such a part as what the subject sees, and only the declaration, a policy of
  type `Clock Nat → Act`, reads it as a clock. The declaration is a part of the subject's type, so it
  is read wherever a pair about that type is stated, and is the same for every such pair. That it is
  a type, and not an instance or an attribute, is a choice of the agent that implemented it: an
  instance can sit in a module the verdicts do not import, or be passed for one pair.
* A value of type `LeanIntent.Clock α` in an argument where no clock part reaches, such as inside a
  list, an option, a sum, a declared type with several constructors, a type of a recursive group
  whose values have several shapes, or a function, is a declaration the class cannot read:
  `Ty.strayClock` finds it, and the trivial-witness check refuses every verdict about such a type
  rather than ignore the declaration. One a clock part reaches, in the data of a node of one shape
  included, is a declaration the class reads. A recursive type with a value recurs through a type of
  its group whose values have several shapes, since a cycle of nodes of one shape holds no value, so
  its values also hold such a `LeanIntent.Clock` below the clock parts, in the values nested in them,
  and the check refuses the type for those. It looks only in the fields of values, never in a
  declared type's parameters, which hold no value except through the fields that use them. It finds
  a `LeanIntent.Clock` by the name its code carries, so a `LeanIntent.Clock T` that is itself a type
  of a recursive group, through a nested occurrence, which the codes name only by its number in the
  group, is neither read nor found.
-/

namespace LeanIntent

/-- A clock: the tick it reads, a value of `α`. A project gives this type to the part of its
subject's arguments that it means as the subject's clock, so that the trivial-witness check reads
that part as a clock even where it is all the subject has to read (`LeanIntent.ArgClock.InClock`).
-/
structure Clock (α : Type) where
  /-- The tick the clock reads. -/
  tick : α
  deriving DecidableEq, Repr, LeanIntent.HasCode

/-- The name `LeanIntent.Clock`'s code carries. -/
def Clock.codeName : Lean.Name := ``Clock

/-- `Clock α`'s code: its name, the chain of its one parameter, and the chain of its one field, both
`α`'s code. -/
theorem Clock.code_eq (α : Type) [HasCode α] :
    HasCode.code (Clock α) =
      .decl Clock.codeName (.prod (HasCode.code α) .unit) (.prod (HasCode.code α) .unit) :=
  rfl

/-- A type has one value exactly when its code says so (`Ty.unique`). -/
theorem Ty.unique_iff (t : Ty) : t.unique = true ↔ ∀ x y : t.denote, x = y := by
  constructor
  · intro h x y
    rw [Ty.eq_empty_of_unique t h x, Ty.eq_empty_of_unique t h y]
  · intro h
    cases hu : t.unique
    · obtain ⟨x, y, hne⟩ := Ty.exists_ne t hu
      exact absurd (h x y) hne
    · rfl

namespace Ty

/-! ## Rounds over the types of a group -/

/-- The marks of the numbers below `K` after `n` rounds of `F`, from none: in each round, a number
below `K` is marked when `F` marks it from the marks of the round before. -/
def roundsOf (K : Nat) (F : (Nat → Bool) → Nat → Bool) (n : Nat) : List Bool :=
  iter (fun h => (List.range K).map (F fun m => h.getD m false)) n (List.replicate K false)

/-- `F` marks more numbers from more marks. -/
def StepMono (F : (Nat → Bool) → Nat → Bool) : Prop :=
  ∀ P Q : Nat → Bool, (∀ m, P m = true → Q m = true) → ∀ m, F P m = true → F Q m = true

section Rounds

variable {K : Nat} {F : (Nat → Bool) → Nat → Bool}

theorem roundsOf_zero (m : Nat) : (roundsOf K F 0).getD m false = false :=
  getD_replicate_false K m

theorem roundsOf_succ (n m : Nat) : (roundsOf K F (n + 1)).getD m false =
    (decide (m < K) && F (fun m' => (roundsOf K F n).getD m' false) m) := by
  rw [roundsOf, iter_succ, getD_range_map]
  rfl

theorem roundsOf_mono (hF : StepMono F) : (n m : Nat) →
    (roundsOf K F n).getD m false = true → (roundsOf K F (n + 1)).getD m false = true
  | 0, m, h => by rw [roundsOf_zero] at h; exact absurd h Bool.false_ne_true
  | n + 1, m, h => by
    rw [roundsOf_succ] at h ⊢
    simp only [Bool.and_eq_true] at h ⊢
    exact ⟨h.1, hF _ _ (fun m' => roundsOf_mono hF n m') m h.2⟩

theorem roundsOf_lt : (n m : Nat) → (roundsOf K F n).getD m false = true → m < K
  | 0, m, h => by rw [roundsOf_zero] at h; exact absurd h Bool.false_ne_true
  | n + 1, m, h => by
    rw [roundsOf_succ] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1

theorem roundsOf_stable {n : Nat}
    (h : ∀ m, (roundsOf K F n).getD m false = (roundsOf K F (n + 1)).getD m false) :
    (k m : Nat) → (roundsOf K F (n + k)).getD m false = (roundsOf K F n).getD m false
  | 0, _ => rfl
  | k + 1, m => by
    rw [← Nat.add_assoc, roundsOf_succ]
    have e : (fun m' => (roundsOf K F (n + k)).getD m' false) =
        fun m' => (roundsOf K F n).getD m' false := funext fun m' => roundsOf_stable h k m'
    rw [e, h m, roundsOf_succ]

/-- How many numbers below `k` the marks `P` mark. -/
def countBelow (P : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k + 1 => countBelow P k + (if P k = true then 1 else 0)

theorem countBelow_le (P : Nat → Bool) : (k : Nat) → countBelow P k ≤ k
  | 0 => Nat.le_refl 0
  | k + 1 => by
    have := countBelow_le P k
    simp only [countBelow]
    split <;> omega

theorem countBelow_mono {P Q : Nat → Bool} (h : ∀ m, P m = true → Q m = true) :
    (k : Nat) → countBelow P k ≤ countBelow Q k
  | 0 => Nat.le_refl 0
  | k + 1 => by
    have := countBelow_mono h k
    simp only [countBelow]
    cases hp : P k
    · cases Q k <;> simp <;> omega
    · simp [h k hp]; omega

theorem countBelow_lt {P Q : Nat → Bool} (h : ∀ m, P m = true → Q m = true) {m : Nat}
    (hm : P m = false) (hq : Q m = true) : (k : Nat) → m < k → countBelow P k < countBelow Q k
  | 0, hk => absurd hk (Nat.not_lt_zero m)
  | k + 1, hk => by
    simp only [countBelow]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · have := countBelow_lt h hm hq k hk
      cases hp : P k
      · cases Q k <;> simp <;> omega
      · simp [h k hp]; omega
    · have := countBelow_mono h m
      simp [hm, hq]
      omega

/-- After as many rounds as there are numbers below `K`, one more round marks nothing more: the
marks only grow, and a round that marks nothing new is followed only by such rounds, so a round
that marks something new marks one more of the `K` numbers. -/
theorem roundsOf_bound (hF : StepMono F) {m : Nat}
    (h : (roundsOf K F (K + 1)).getD m false = true) : (roundsOf K F K).getD m false = true := by
  have key : ∀ n, (∃ k, k < n ∧ ∀ m, (roundsOf K F k).getD m false =
      (roundsOf K F (k + 1)).getD m false) ∨
      n ≤ countBelow (fun m => (roundsOf K F n).getD m false) K := by
    intro n
    induction n with
    | zero => exact .inr (Nat.zero_le _)
    | succ n ih =>
      rcases ih with ⟨k, hk, hs⟩ | hc
      · exact .inl ⟨k, Nat.lt_succ_of_lt hk, hs⟩
      · by_cases hs : ∀ m, (roundsOf K F n).getD m false = (roundsOf K F (n + 1)).getD m false
        · exact .inl ⟨n, Nat.lt_succ_self n, hs⟩
        · obtain ⟨m', hm'⟩ := Classical.not_forall.mp hs
          have hq : (roundsOf K F (n + 1)).getD m' false = true := by
            cases e : (roundsOf K F n).getD m' false
            · cases e' : (roundsOf K F (n + 1)).getD m' false
              · exact absurd (e.trans e'.symm) hm'
              · rfl
            · exact roundsOf_mono hF n m' e
          have hp : (roundsOf K F n).getD m' false = false := by
            cases e : (roundsOf K F n).getD m' false
            · rfl
            · exact absurd (e.trans (roundsOf_mono hF n m' e).symm) hm'
          have := countBelow_lt (fun m'' => roundsOf_mono hF n m'') hp hq K (roundsOf_lt _ _ hq)
          exact .inr (by omega)
  rcases key (K + 1) with ⟨k, hk, hs⟩ | hc
  · have e1 := roundsOf_stable hs (K + 1 - k) m
    have e2 := roundsOf_stable hs (K - k) m
    rw [show k + (K + 1 - k) = K + 1 by omega] at e1
    rw [show k + (K - k) = K by omega] at e2
    rw [e2, ← e1]
    exact h
  · exact absurd (countBelow_le (fun m => (roundsOf K F (K + 1)).getD m false) K) (by omega)

/-- The round `K` marks what `F` marks from it. -/
theorem roundsOf_fix (hF : StepMono F) {m : Nat} (hm : m < K)
    (h : F (fun m' => (roundsOf K F K).getD m' false) m = true) :
    (roundsOf K F K).getD m false = true := by
  apply roundsOf_bound hF
  rw [roundsOf_succ, h]
  simp [hm]

end Rounds

/-! ## The trees of a group -/

theorem item_of_items_le (t : Ty) (n : Nat) (h : t.items ≤ n) : t.item n = .unit := by
  induction t generalizing n with
  | prod a r _ ihr =>
    cases n with
    | zero => simp [items] at h
    | succ n => exact ihr n (by simp [items] at h; omega)
  | _ => rfl

/-- A type of a group with a constructor is listed in the chain `r`. -/
theorem lt_items_of_muN {r : Ty} {l : Nat} (h : 0 < r.muN l) : l < r.items := by
  refine Classical.byContradiction fun hn => ?_
  rw [muN, item_of_items_le r l (by omega)] at h
  exact absurd h (by simp [items])

theorem den_cons : (t : Ty) → (k : Nat) → (p : List Nat) → t.den (k :: p) = (t.item k).den p
  | prod _ _, 0, _ => rfl
  | prod _ b, n + 1, p => den_cons b n p
  | unit, _, _ | bool, _, _ | nat, _, _ | int, _, _ | string, _, _ | list _, _, _
  | array _, _, _ | option _, _, _ | sum _ _, _, _ | decl _ _ _, _, _ | fin _, _, _
  | atom _, _, _ | arrow _ _, _, _ | ref _, _, _ | mu _ _ _ _, _, _ | muAt _ _ _ _ _, _, _ => rfl

/-- The code of the fields of the `c`-th constructor of the `m`-th type of a group that hold no
value of the group, in the chain `g` of the group's data and arguments. -/
def ctorData (g : Ty) (m c : Nat) : Ty := ((g.item m).item c).item 0

/-- The code of the arguments of the `f`-th recursive field of the `c`-th constructor of the `m`-th
type of a group: the unit code for a field that holds a value of the group. -/
def ctorArg (g : Ty) (m c f : Nat) : Ty := (((g.item m).item c).item 1).item f

theorem den_data (g : Ty) (m c : Nat) : g.den [m, c, 0] = (g.ctorData m c).denote := by
  rw [den_cons, den_cons, den_cons]
  rfl

theorem den_arg (g : Ty) (m c f : Nat) : g.den [m, c, 1, f] = (g.ctorArg m c f).denote := by
  rw [den_cons, den_cons, den_cons, den_cons]
  rfl

/-- The numbers the decisions about a group's types mark: each type the chain `r` lists, and the
root `o`. -/
def groupBound (r : Ty) (o : Nat) : Nat := r.items + o + 1

/-- One round of finding the types of a group with a value: the root `o`, which has its base
values, and each type with a constructor whose recursive fields all hold types `h` marks. -/
def inhStep (r : Ty) (o : Nat) (h : Nat → Bool) (l : Nat) : Bool :=
  l == o || (List.range (r.muN l)).any fun c =>
    (List.range (r.muA l c)).all fun f => h (r.muS l c f)

theorem inhStep_mono (r : Ty) (o : Nat) : StepMono (inhStep r o) := by
  intro P Q hPQ l h
  simp only [inhStep, Bool.or_eq_true, beq_iff_eq, List.any_eq_true, List.all_eq_true,
    List.mem_range] at h ⊢
  rcases h with h | ⟨c, hc, hall⟩
  · exact .inl h
  · exact .inr ⟨c, hc, fun f hf => hPQ _ (hall f hf)⟩

/-- Whether the `l`-th type of the group whose recursive fields `r` lists, rooted at its `o`-th
type, has a value (`treeInh_iff`). -/
def treeInh (r : Ty) (o l : Nat) : Bool :=
  (roundsOf (groupBound r o) (inhStep r o) (groupBound r o)).getD l false

theorem rounds_inh_sound {b g r : Ty} {o : Nat} : (n l : Nat) →
    (roundsOf (groupBound r o) (inhStep r o) n).getD l false = true →
      Nonempty (muTy b g r o r.muN l)
  | 0, l, h => by rw [roundsOf_zero] at h; exact absurd h Bool.false_ne_true
  | n + 1, l, h => by
    rw [roundsOf_succ] at h
    simp only [inhStep, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
      List.all_eq_true, List.mem_range] at h
    rcases h.2 with rfl | ⟨c, hc, hall⟩
    · exact ⟨.base b.empty⟩
    · exact ⟨.node ⟨c, hc⟩ (g.denEmpty [l, c, 0]) fun f _ =>
        Classical.choice (rounds_inh_sound n _ (hall f f.2))⟩

theorem treeInh_of {b g r : Ty} {o l : Nat} (x : muTy b g r o r.muN l) : treeInh r o l = true := by
  induction x with
  | base _ =>
    apply roundsOf_fix (inhStep_mono r o) (by unfold groupBound; omega)
    simp [inhStep]
  | @node j c _ _ ih =>
    have hj := lt_items_of_muN (Nat.lt_of_le_of_lt (Nat.zero_le _) c.2)
    apply roundsOf_fix (inhStep_mono r o) (by unfold groupBound; omega)
    simp only [inhStep, Bool.or_eq_true, beq_iff_eq, List.any_eq_true, List.all_eq_true,
      List.mem_range]
    exact .inr ⟨c, c.2, fun f hf => ih ⟨f, hf⟩ (g.denEmpty _)⟩

/-- `treeInh` decides whether a type of the group has a value. -/
theorem treeInh_iff {b g r : Ty} {o l : Nat} :
    treeInh r o l = true ↔ Nonempty (muTy b g r o r.muN l) :=
  ⟨rounds_inh_sound _ l, fun ⟨x⟩ => treeInh_of x⟩

theorem two_of_filter {p : Nat → Bool} {n : Nat} (h : 2 ≤ ((List.range n).filter p).length) :
    ∃ a b, a < n ∧ b < n ∧ p a = true ∧ p b = true ∧ a ≠ b := by
  have hnd := List.Nodup.sublist (List.filter_sublist (p := p)) (List.nodup_range (n := n))
  match hl : (List.range n).filter p, h with
  | a :: b :: _, _ =>
    have ha : a ∈ (List.range n).filter p := by rw [hl]; exact List.mem_cons_self
    have hb : b ∈ (List.range n).filter p := by rw [hl]; simp
    rw [hl] at hnd
    simp only [List.mem_filter, List.mem_range] at ha hb
    exact ⟨a, b, ha.1, hb.1, ha.2, hb.2, fun e => (List.nodup_cons.mp hnd).1 (by simp [e])⟩

theorem filter_two {l : List Nat} {p : Nat → Bool} {a b : Nat} (ha : a ∈ l.filter p)
    (hb : b ∈ l.filter p) (hab : a ≠ b) : 2 ≤ (l.filter p).length := by
  match hl : l.filter p with
  | [] => rw [hl] at ha; exact absurd ha List.not_mem_nil
  | [x] =>
    rw [hl, List.mem_singleton] at ha hb
    exact absurd (ha.trans hb.symm) hab
  | _ :: _ :: _ => simp

/-- Whether the `c`-th constructor of the `m`-th type builds a value: each of its recursive fields
holds a type with one. -/
def ctorInh (r : Ty) (o m c : Nat) : Bool :=
  (List.range (r.muA m c)).all fun f => treeInh r o (r.muS m c f)

/-- The number of the kinds of value of the `m`-th type: its base values where it is the root, and
each constructor that builds a value. -/
def shapeCount (r : Ty) (o m : Nat) : Nat :=
  (if m = o then 1 else 0) + ((List.range (r.muN m)).filter (ctorInh r o m)).length

/-- One round of finding the types of a group with two values: each with two kinds of value, the
root where its base has two values, and each with a constructor that builds a value and whose other
fields have two values or one of whose recursive fields holds a type `h` marks. -/
def multiStep (b g r : Ty) (o : Nat) (h : Nat → Bool) (m : Nat) : Bool :=
  decide (2 ≤ shapeCount r o m) || (m == o && !b.unique) ||
    (List.range (r.muN m)).any fun c => ctorInh r o m c &&
      (!(g.ctorData m c).unique || (List.range (r.muA m c)).any fun f => h (r.muS m c f))

theorem multiStep_mono (b g r : Ty) (o : Nat) : StepMono (multiStep b g r o) := by
  intro P Q hPQ m h
  simp only [multiStep, Bool.or_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true] at h ⊢
  rcases h with h | ⟨c, hc, hi, h | ⟨f, hf, hp⟩⟩
  · exact .inl h
  · exact .inr ⟨c, hc, hi, .inl h⟩
  · exact .inr ⟨c, hc, hi, .inr ⟨f, hf, hPQ _ hp⟩⟩

/-- Whether the `m`-th type of the group with the base `b`, data and arguments `g` and recursive
fields `r`, rooted at its `o`-th type, has two values (`treeMulti_iff`). -/
def treeMulti (b g r : Ty) (o m : Nat) : Bool :=
  (roundsOf (groupBound r o) (multiStep b g r o) (groupBound r o)).getD m false

end Ty

namespace MuVal

variable {B : Type} {i : Nat} {N : Nat → Nat} {D : Nat → Nat → Type} {A : Nat → Nat → Nat}
  {P : Nat → Nat → Nat → Type} {S : Nat → Nat → Nat → Nat}

/-- The children `k` with those of the field `f₀` replaced by `u`. -/
def upd {j : Nat} {c : Nat}
    (k : (f : Fin (A j c)) → P j c f → MuVal B i N D A P S (S j c f)) (f₀ : Fin (A j c))
    (u : P j c f₀ → MuVal B i N D A P S (S j c f₀)) :
    (f : Fin (A j c)) → P j c f → MuVal B i N D A P S (S j c f) :=
  fun f => if h : f = f₀ then h ▸ u else k f

theorem upd_self {j c : Nat} (k : (f : Fin (A j c)) → P j c f → MuVal B i N D A P S (S j c f))
    (f₀ : Fin (A j c)) (u : P j c f₀ → MuVal B i N D A P S (S j c f₀)) : upd k f₀ u f₀ = u := by
  simp [upd]

theorem upd_ne {j c : Nat} (k : (f : Fin (A j c)) → P j c f → MuVal B i N D A P S (S j c f))
    {f₀ f : Fin (A j c)} (u : P j c f₀ → MuVal B i N D A P S (S j c f₀)) (h : f ≠ f₀) :
    upd k f₀ u f = k f := by
  simp [upd, h]

end MuVal

namespace Ty

theorem ctorInh_kids {b g r : Ty} {o m c : Nat} (h : ctorInh r o m c = true) :
    Nonempty ((f : Fin (r.muA m c)) → g.den [m, c, 1, f] → muTy b g r o r.muN (r.muS m c f)) := by
  simp only [ctorInh, List.all_eq_true, List.mem_range] at h
  exact ⟨fun f _ => Classical.choice (treeInh_iff.mp (h f f.2))⟩

theorem ctorInh_of_kids {b g r : Ty} {o m c : Nat}
    (k : (f : Fin (r.muA m c)) → g.den [m, c, 1, f] → muTy b g r o r.muN (r.muS m c f)) :
    ctorInh r o m c = true := by
  simp only [ctorInh, List.all_eq_true, List.mem_range]
  exact fun f hf => treeInh_of (k ⟨f, hf⟩ (g.denEmpty _))

theorem node_ne_of_ne {b g r : Ty} {o m : Nat} {c c' : Fin (r.muN m)} (hc : c ≠ c')
    {d : g.den [m, c, 0]} {d' : g.den [m, c', 0]}
    {k : (f : Fin (r.muA m c)) → g.den [m, c, 1, f] → muTy b g r o r.muN (r.muS m c f)}
    {k' : (f : Fin (r.muA m c')) → g.den [m, c', 1, f] → muTy b g r o r.muN (r.muS m c' f)} :
    (MuVal.node c d k : muTy b g r o r.muN m) ≠ MuVal.node c' d' k' :=
  fun e => hc (MuVal.node.inj e).1

theorem rounds_multi_sound {b g r : Ty} {o : Nat} : (n m : Nat) →
    (roundsOf (groupBound r o) (multiStep b g r o) n).getD m false = true →
      ∃ x y : muTy b g r o r.muN m, x ≠ y
  | 0, m, h => by rw [roundsOf_zero] at h; exact absurd h Bool.false_ne_true
  | n + 1, m, h => by
    rw [roundsOf_succ] at h
    simp only [multiStep, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
      decide_eq_true_eq, List.any_eq_true, List.mem_range] at h
    rcases h.2 with (h2 | ⟨rfl, hb⟩) | ⟨c, hc, hi, hd | ⟨f, hf, hm⟩⟩
    · unfold shapeCount at h2
      by_cases ho : m = o
      · subst ho
        simp only [↓reduceIte] at h2
        obtain ⟨c, hc⟩ := List.exists_mem_of_length_pos (by omega :
          0 < ((List.range (r.muN m)).filter (ctorInh r m m)).length)
        rw [List.mem_filter, List.mem_range] at hc
        obtain ⟨k⟩ := ctorInh_kids (b := b) (g := g) hc.2
        exact ⟨.base b.empty, .node ⟨c, hc.1⟩ (g.denEmpty _) k, fun e => by cases e⟩
      · simp only [ho, ↓reduceIte, Nat.zero_add] at h2
        obtain ⟨c, c', hc, hc', hi, hi', hne⟩ := two_of_filter h2
        obtain ⟨k⟩ := ctorInh_kids (b := b) (g := g) hi
        obtain ⟨k'⟩ := ctorInh_kids (b := b) (g := g) hi'
        exact ⟨.node ⟨c, hc⟩ (g.denEmpty _) k, .node ⟨c', hc'⟩ (g.denEmpty _) k',
          node_ne_of_ne fun e => hne (congrArg Fin.val e)⟩
    · obtain ⟨u, v, huv⟩ := exists_ne b hb
      exact ⟨.base u, .base v, fun e => huv (MuVal.base.inj e)⟩
    · obtain ⟨u, v, huv⟩ := exists_ne _ hd
      obtain ⟨k⟩ := ctorInh_kids (b := b) (g := g) hi
      refine ⟨.node ⟨c, hc⟩ (cast (den_data g m c).symm u) k,
        .node ⟨c, hc⟩ (cast (den_data g m c).symm v) k, fun e => huv ?_⟩
      have := eq_of_heq (MuVal.node.inj e).2.1
      have := congrArg (cast (den_data g m c)) this
      simpa [cast_cast] using this
    · obtain ⟨u, v, huv⟩ := rounds_multi_sound n _ hm
      obtain ⟨k⟩ := ctorInh_kids (b := b) (g := g) hi
      refine ⟨.node ⟨c, hc⟩ (g.denEmpty _) (MuVal.upd k ⟨f, hf⟩ fun _ => u),
        .node ⟨c, hc⟩ (g.denEmpty _) (MuVal.upd k ⟨f, hf⟩ fun _ => v), fun e => huv ?_⟩
      have := congrFun (congrFun (eq_of_heq (MuVal.node.inj e).2.2) ⟨f, hf⟩) (g.denEmpty _)
      simpa [MuVal.upd_self] using this

theorem not_unique_of_ne {t : Ty} {α : Type} (e : α = t.denote) {u v : α} (h : u ≠ v) :
    t.unique = false := by
  cases hu : t.unique
  · rfl
  · refine absurd ?_ h
    have := (unique_iff t).mp hu (cast e u) (cast e v)
    have := congrArg (cast e.symm) this
    simpa [cast_cast] using this

theorem treeMulti_of {b g r : Ty} {o m : Nat} (x : muTy b g r o r.muN m) :
    ∀ y, x ≠ y → treeMulti b g r o m = true := by
  induction x with
  | base u =>
    intro y hne
    apply roundsOf_fix (multiStep_mono b g r o) (by unfold groupBound; omega)
    cases y with
    | base v =>
      have hb : b.unique = false := not_unique_of_ne rfl fun e => hne (congrArg MuVal.base e)
      simp [multiStep, hb]
    | node c d k =>
      have hm : c.val ∈ (List.range (r.muN o)).filter (ctorInh r o o) :=
        List.mem_filter.mpr ⟨List.mem_range.mpr c.2, ctorInh_of_kids k⟩
      have := List.length_pos_of_mem hm
      have h2 : 2 ≤ shapeCount r o o := by unfold shapeCount; simp; omega
      simp [multiStep, h2]
  | @node j c d k ih =>
    intro y hne
    have hj := lt_items_of_muN (Nat.lt_of_le_of_lt (Nat.zero_le _) c.2)
    apply roundsOf_fix (multiStep_mono b g r o) (by unfold groupBound; omega)
    cases y with
    | base v =>
      have hm : c.val ∈ (List.range (r.muN o)).filter (ctorInh r o o) :=
        List.mem_filter.mpr ⟨List.mem_range.mpr c.2, ctorInh_of_kids k⟩
      have := List.length_pos_of_mem hm
      have h2 : 2 ≤ shapeCount r o o := by unfold shapeCount; simp; omega
      simp [multiStep, h2]
    | node c' d' k' =>
      by_cases hc : c = c'
      · subst hc
        by_cases hd : d = d'
        · subst hd
          have hk : ∃ f p, k f p ≠ k' f p := by
            refine Classical.byContradiction fun hn => hne ?_
            have : k = k' := funext fun f => funext fun p =>
              Classical.byContradiction fun h => hn ⟨f, p, h⟩
            rw [this]
          obtain ⟨f, p, hfp⟩ := hk
          have hf := ih f p _ hfp
          simp only [multiStep, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true,
            List.mem_range]
          exact .inr ⟨c, c.2, ctorInh_of_kids k, .inr ⟨f, f.2, hf⟩⟩
        · have hu : (g.ctorData j c).unique = false := not_unique_of_ne (den_data g j c) hd
          simp only [multiStep, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true,
            List.mem_range, Bool.not_eq_true']
          exact .inr ⟨c, c.2, ctorInh_of_kids k, .inl hu⟩
      · have h2 : 2 ≤ ((List.range (r.muN j)).filter (ctorInh r o j)).length :=
          filter_two (List.mem_filter.mpr ⟨List.mem_range.mpr c.2, ctorInh_of_kids k⟩)
            (List.mem_filter.mpr ⟨List.mem_range.mpr c'.2, ctorInh_of_kids k'⟩)
            fun e => hc (Fin.ext e)
        have h2' : 2 ≤ shapeCount r o j := by unfold shapeCount; omega
        simp [multiStep, h2']

/-- `treeMulti` decides whether a type of the group has two values. -/
theorem treeMulti_iff {b g r : Ty} {o m : Nat} :
    treeMulti b g r o m = true ↔ ∃ x y : muTy b g r o r.muN m, x ≠ y :=
  ⟨rounds_multi_sound _ m, fun ⟨x, y, h⟩ => treeMulti_of x y h⟩

/-- A type of the group has at most one value exactly when `treeMulti` says it has not two. -/
theorem treeMulti_eq_false_iff {b g r : Ty} {o m : Nat} :
    treeMulti b g r o m = false ↔ ∀ x y : muTy b g r o r.muN m, x = y := by
  rw [← Bool.not_eq_true, treeMulti_iff]
  exact ⟨fun h x y => Classical.byContradiction fun hn => h ⟨x, y, hn⟩,
    fun h ⟨x, y, hne⟩ => hne (h x y)⟩

end Ty

/-! ## Trees of a type whose values have one shape -/

namespace MuVal

variable {B : Type} {i : Nat} {N : Nat → Nat} {D : Nat → Nat → Type} {A : Nat → Nat → Nat}
  {P : Nat → Nat → Nat → Type} {S : Nat → Nat → Nat → Nat}

/-- The base value of a tree of a type with no other constructor. -/
def baseVal : {l : Nat} → N l = 0 → MuVal B i N D A P S l → B
  | _, _, .base x => x
  | _, h, .node c _ _ => (by have := c.2; omega : False).elim

/-- A tree of the root, where it has no other constructor, is its base value. -/
theorem base_baseVal (h : N i = 0) (x : MuVal B i N D A P S i) : .base (baseVal h x) = x := by
  cases x with
  | base _ => rfl
  | node c _ _ => exact (by have := c.2; omega : False).elim

/-- The data of a tree of a type that is not the root and has one constructor. -/
def nodeData : {l : Nat} → l ≠ i → N l = 1 → MuVal B i N D A P S l → D l 0
  | _, hl, _, .base _ => absurd rfl hl
  | _, _, _, .node ⟨0, _⟩ d _ => d
  | _, _, h, .node ⟨_ + 1, hc⟩ _ _ => absurd hc (by omega)

/-- The children of a tree of a type that is not the root and has one constructor. -/
def nodeKids : {l : Nat} → l ≠ i → N l = 1 → MuVal B i N D A P S l →
    (f : Fin (A l 0)) → P l 0 f → MuVal B i N D A P S (S l 0 f)
  | _, hl, _, .base _ => absurd rfl hl
  | _, _, _, .node ⟨0, _⟩ _ k => k
  | _, _, h, .node ⟨_ + 1, hc⟩ _ _ => absurd hc (by omega)

/-- The tree of the one constructor of a type, from its data and children. -/
def ofNode {l : Nat} (h : N l = 1) (d : D l 0)
    (k : (f : Fin (A l 0)) → P l 0 f → MuVal B i N D A P S (S l 0 f)) : MuVal B i N D A P S l :=
  .node ⟨0, by omega⟩ d k

theorem ofNode_eta {l : Nat} (hl : l ≠ i) (h : N l = 1) (x : MuVal B i N D A P S l) :
    ofNode h (nodeData hl h x) (nodeKids hl h x) = x := by
  cases x with
  | base _ => exact absurd rfl hl
  | node c d k =>
    rcases c with ⟨_ | c, hc⟩
    · rfl
    · exact absurd hc (by omega)

/-- Reading `H` of a tree's data determines the tree exactly when `H` determines the data and the
children have one value. -/
theorem injective_data_iff {γ : Type} {l : Nat} (hl : l ≠ i) (h : N l = 1)
    (x₀ : MuVal B i N D A P S l) (H : D l 0 → γ) :
    Function.Injective (fun x : MuVal B i N D A P S l => H (nodeData hl h x)) ↔
      Function.Injective H ∧
      ∀ k k' : (f : Fin (A l 0)) → P l 0 f → MuVal B i N D A P S (S l 0 f), k = k' := by
  constructor
  · intro hi
    exact ⟨fun d d' e => congrArg (nodeData hl h)
        (@hi (ofNode h d (nodeKids hl h x₀)) (ofNode h d' (nodeKids hl h x₀)) e),
      fun k k' => congrArg (nodeKids hl h)
        (@hi (ofNode h (nodeData hl h x₀) k) (ofNode h (nodeData hl h x₀) k') rfl)⟩
  · rintro ⟨hH, hk⟩ x y e
    rw [← ofNode_eta hl h x, ← ofNode_eta hl h y, hH e, hk (nodeKids hl h x) (nodeKids hl h y)]

/-- The children of a constructor have one value exactly when each field's type has one, where each
field has a position. -/
theorem kids_unique_iff {j c : Nat}
    (k₀ : (f : Fin (A j c)) → P j c f → MuVal B i N D A P S (S j c f))
    (pe : (f : Fin (A j c)) → P j c f) :
    (∀ k k' : (f : Fin (A j c)) → P j c f → MuVal B i N D A P S (S j c f), k = k') ↔
      ∀ f : Fin (A j c), ∀ u v : MuVal B i N D A P S (S j c f), u = v := by
  constructor
  · intro h f u v
    have := congrFun (congrFun (h (upd k₀ f fun _ => u) (upd k₀ f fun _ => v)) f) (pe f)
    simpa [upd_self] using this
  · intro h k k'
    exact funext fun f => funext fun _ => h f _ _

/-- Reading `H` of a tree's child at the field `f₀`, whose positions have one value, determines the
tree exactly when `H` determines the child, the data have one value, and so do the other fields'
types. -/
theorem injective_kid_iff {γ : Type} {l : Nat} (hl : l ≠ i) (h : N l = 1)
    (x₀ : MuVal B i N D A P S l) (pe : (f : Fin (A l 0)) → P l 0 f) (f₀ : Fin (A l 0))
    (hp : ∀ p p' : P l 0 f₀, p = p') (H : MuVal B i N D A P S (S l 0 f₀) → γ) :
    Function.Injective (fun x : MuVal B i N D A P S l => H (nodeKids hl h x f₀ (pe f₀))) ↔
      Function.Injective H ∧
      (∀ d d' : D l 0, d = d') ∧ ∀ f, f ≠ f₀ → ∀ u v : MuVal B i N D A P S (S l 0 f), u = v := by
  constructor
  · intro hi
    refine ⟨fun u v e => ?_, fun d d' => ?_, fun f hf u v => ?_⟩
    · have := @hi (ofNode h (nodeData hl h x₀) (upd (nodeKids hl h x₀) f₀ fun _ => u))
        (ofNode h (nodeData hl h x₀) (upd (nodeKids hl h x₀) f₀ fun _ => v))
        (by simpa [ofNode, nodeKids, upd_self] using e)
      have := congrArg (fun z => nodeKids hl h z f₀ (pe f₀)) this
      simpa [ofNode, nodeKids, upd_self] using this
    · exact congrArg (nodeData hl h)
        (@hi (ofNode h d (nodeKids hl h x₀)) (ofNode h d' (nodeKids hl h x₀)) rfl)
    · have := @hi (ofNode h (nodeData hl h x₀) (upd (nodeKids hl h x₀) f fun _ => u))
        (ofNode h (nodeData hl h x₀) (upd (nodeKids hl h x₀) f fun _ => v))
        (by simp [ofNode, nodeKids, upd_ne _ _ (Ne.symm hf)])
      have := congrArg (fun z => nodeKids hl h z f (pe f)) this
      simpa [ofNode, nodeKids, upd_self] using this
  · rintro ⟨hH, hd, hf⟩ x y e
    rw [← ofNode_eta hl h x, ← ofNode_eta hl h y, hd (nodeData hl h x) (nodeData hl h y)]
    congr 1
    funext f p
    by_cases e' : f = f₀
    · subst e'
      rw [hp p (pe f), hH e]
    · exact hf f e' _ _

end MuVal

namespace Ty

theorem unique_congr {α β : Type} (e : α = β) : (∀ x y : α, x = y) ↔ ∀ x y : β, x = y := by
  subst e
  exact Iff.rfl

theorem eqRec_inj {F : Nat → Type} {j j' : Nat} (e : j = j') {a b : F j}
    (h : (e ▸ a : F j') = e ▸ b) : a = b := by
  subst e
  exact h

/-! ## The length of a tree of a type shaped as a list -/

/-- The recursive fields of the `c`-th constructor of the `m`-th type that hold the `m`-th type
itself. -/
def selfFields (r : Ty) (m c : Nat) : List Nat :=
  (List.range (r.muA m c)).filter fun f => r.muS m c f == m

theorem lt_of_mem_selfFields {r : Ty} {m c f : Nat} (h : f ∈ r.selfFields m c) : f < r.muA m c :=
  List.mem_range.mp (List.mem_filter.mp h).1

theorem muS_of_mem_selfFields {r : Ty} {m c f : Nat} (h : f ∈ r.selfFields m c) :
    r.muS m c f = m := by
  simpa using (List.mem_filter.mp h).2

theorem mem_of_head? {l : List Nat} {f : Nat} (h : l.head? = some f) : f ∈ l := by
  obtain ⟨ys, rfl⟩ := List.head?_eq_some_iff.mp h
  exact List.mem_cons_self

/-- Whether the `m`-th type of a group is shaped as a list: each of its constructors has at most
one recursive field that holds the type itself, a value of it and not a function to one, and some
constructor has one. -/
def listShaped (g r : Ty) (m : Nat) : Bool :=
  ((List.range (r.muN m)).all fun c => decide ((r.selfFields m c).length ≤ 1) &&
    (r.selfFields m c).all fun f => g.ctorArg m c f == .unit) &&
  (List.range (r.muN m)).any fun c => !(r.selfFields m c).isEmpty

/-- The length of a tree: the number of nodes along the field of each node that holds a value of
its own type, so zero for a base value and for a node with no such field. -/
def treeLen {b g r : Ty} {o : Nat} : {j : Nat} → muTy b g r o r.muN j → Nat
  | _, .base _ => 0
  | j, .node c _ k =>
    match h : (r.selfFields j c).head? with
    | some f =>
      1 + treeLen (k ⟨f, lt_of_mem_selfFields (mem_of_head? h)⟩ (g.denEmpty [j, c, 1, f]))
    | none => 0

theorem treeLen_node_none {b g r : Ty} {o j : Nat} {c : Fin (r.muN j)} {d : g.den [j, c, 0]}
    {k : (f : Fin (r.muA j c)) → g.den [j, c, 1, f] → muTy b g r o r.muN (r.muS j c f)}
    (h : (r.selfFields j c).head? = none) :
    treeLen (.node c d k : muTy b g r o r.muN j) = 0 := by
  rw [treeLen]
  split
  · next f h' => rw [h] at h'; exact absurd h' (by simp)
  · rfl

theorem treeLen_node_some {b g r : Ty} {o j : Nat} {c : Fin (r.muN j)} {d : g.den [j, c, 0]}
    {k : (f : Fin (r.muA j c)) → g.den [j, c, 1, f] → muTy b g r o r.muN (r.muS j c f)} {f : Nat}
    (h : (r.selfFields j c).head? = some f) :
    treeLen (.node c d k : muTy b g r o r.muN j) =
      1 + treeLen (k ⟨f, lt_of_mem_selfFields (mem_of_head? h)⟩ (g.denEmpty [j, c, 1, f])) := by
  rw [treeLen]
  split
  · next f' h' =>
    rw [h] at h'
    cases h'
    rfl
  · next h' => rw [h] at h'; exact absurd h' (by simp)

theorem treeLen_eqRec {b g r : Ty} {o j j' : Nat} (e : j = j') (v : muTy b g r o r.muN j) :
    treeLen (e ▸ v : muTy b g r o r.muN j') = treeLen v := by
  subst e
  rfl

/-- Whether the `c`-th constructor of the `m`-th type builds a value of length zero: it builds a
value, and has no field that holds the type itself. -/
def zeroCtor (r : Ty) (o m c : Nat) : Bool := ctorInh r o m c && (r.selfFields m c).isEmpty

/-- Whether the `c`-th constructor of the `m`-th type builds a value one node longer than its child:
it builds a value, and has a field that holds the type itself. -/
def stepCtor (r : Ty) (o m c : Nat) : Bool := ctorInh r o m c && !(r.selfFields m c).isEmpty

/-- Whether the fields of the `c`-th constructor of the `m`-th type other than the recursive fields
`skip` have one value. -/
def restUnique (b g r : Ty) (o m c : Nat) (skip : List Nat) : Bool :=
  (g.ctorData m c).unique && (List.range (r.muA m c)).all fun f =>
    skip.contains f || !treeMulti b g r o (r.muS m c f)

theorem restUnique_iff {b g r : Ty} {o m c : Nat} {skip : List Nat} :
    restUnique b g r o m c skip = true ↔ (∀ d d' : g.den [m, c, 0], d = d') ∧
      ∀ f : Fin (r.muA m c), f.val ∉ skip → ∀ u v : muTy b g r o r.muN (r.muS m c f), u = v := by
  simp only [restUnique, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    List.contains_iff_mem, Bool.not_eq_true']
  rw [unique_congr (den_data g m c), ← unique_iff]
  apply and_congr Iff.rfl
  constructor
  · intro h f hf
    exact treeMulti_eq_false_iff.mp ((h f f.2).resolve_left hf)
  · intro h f hf
    by_cases hs : f ∈ skip
    · exact .inl hs
    · exact .inr (treeMulti_eq_false_iff.mpr (h ⟨f, hf⟩ hs))

/-- Whether the length of a tree of the `m`-th type determines the tree: the type has at most one
value of length zero, and its constructors build at most one kind of longer value, each fixed by its
child of its own type. -/
def lenDet (b g r : Ty) (o m : Nat) : Bool :=
  decide ((if m = o then 1 else 0) + ((List.range (r.muN m)).filter (zeroCtor r o m)).length ≤ 1) &&
    (m != o || b.unique) &&
    ((List.range (r.muN m)).all fun c => !zeroCtor r o m c || restUnique b g r o m c []) &&
    decide (((List.range (r.muN m)).filter (stepCtor r o m)).length ≤ 1) &&
    (List.range (r.muN m)).all fun c =>
      !stepCtor r o m c || restUnique b g r o m c (r.selfFields m c)

theorem filter_le_one {l : List Nat} {p : Nat → Bool} {a b : Nat} (h : (l.filter p).length ≤ 1)
    (ha : a ∈ l.filter p) (hb : b ∈ l.filter p) : a = b :=
  Classical.byContradiction fun hab => absurd (filter_two ha hb hab) (by omega)

theorem selfFields_eq {r : Ty} {m c f : Nat} (hle : (r.selfFields m c).length ≤ 1)
    (h : (r.selfFields m c).head? = some f) : r.selfFields m c = [f] := by
  obtain ⟨ys, e⟩ := List.head?_eq_some_iff.mp h
  rw [e] at hle ⊢
  cases ys with
  | nil => rfl
  | cons _ _ => simp at hle

theorem listShaped_le {g r : Ty} {m : Nat} (hs : listShaped g r m = true) {c : Nat}
    (hc : c < r.muN m) : (r.selfFields m c).length ≤ 1 := by
  simp only [listShaped, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at hs
  exact (hs.1 c hc).1

theorem listShaped_arg {g r : Ty} {m : Nat} (hs : listShaped g r m = true) {c : Nat}
    (hc : c < r.muN m) {f : Nat} (hf : f ∈ r.selfFields m c) : g.ctorArg m c f = .unit := by
  simp only [listShaped, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    beq_iff_eq] at hs
  exact (hs.1 c hc).2 f hf

theorem head?_none_of_len {b g r : Ty} {o j : Nat} {c : Fin (r.muN j)} {d : g.den [j, c, 0]}
    {k : (f : Fin (r.muA j c)) → g.den [j, c, 1, f] → muTy b g r o r.muN (r.muS j c f)}
    (h : treeLen (.node c d k : muTy b g r o r.muN j) = 0) : (r.selfFields j c).head? = none := by
  cases h' : (r.selfFields j c).head? with
  | none => rfl
  | some f => rw [treeLen_node_some h'] at h; omega

theorem head?_some_of_len {b g r : Ty} {o j n : Nat} {c : Fin (r.muN j)} {d : g.den [j, c, 0]}
    {k : (f : Fin (r.muA j c)) → g.den [j, c, 1, f] → muTy b g r o r.muN (r.muS j c f)}
    (h : treeLen (.node c d k : muTy b g r o r.muN j) = n + 1) :
    ∃ f, (r.selfFields j c).head? = some f := by
  cases h' : (r.selfFields j c).head? with
  | none => rw [treeLen_node_none h'] at h; omega
  | some f => exact ⟨f, rfl⟩

theorem isEmpty_false_of_head? {l : List Nat} {f : Nat} (h : l.head? = some f) :
    l.isEmpty = false := by
  cases l with
  | nil => simp at h
  | cons _ _ => rfl

theorem pos_unique {g : Ty} {m c f : Nat} (hu : g.ctorArg m c f = .unit) :
    ∀ p p' : g.den [m, c, 1, f], p = p' :=
  (unique_congr (den_arg g m c f)).mpr (by rw [hu]; exact fun _ _ => rfl)

/-- Where `lenDet` holds, the length of a tree of a list-shaped type determines it. -/
theorem treeLen_injective {b g r : Ty} {o m : Nat} (hs : listShaped g r m = true)
    (h : lenDet b g r o m = true) :
    Function.Injective (treeLen : muTy b g r o r.muN m → Nat) := by
  simp only [lenDet, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne, ne_eq,
    List.all_eq_true, List.mem_range, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨hz, hb⟩, hzr⟩, hst⟩, hsr⟩ := h
  have hz' : ((List.range (r.muN m)).filter (zeroCtor r o m)).length ≤ 1 := by
    split at hz <;> omega
  suffices key : ∀ n (x y : muTy b g r o r.muN m), treeLen x = n → treeLen y = n → x = y from
    fun x y e => key _ x y rfl e.symm
  intro n
  induction n with
  | zero =>
    intro x y hx hy
    cases x with
    | base u =>
      cases y with
      | base v => rw [(unique_iff b).mp (hb.resolve_left fun h => h rfl) u v]
      | node c' d' k' =>
        have hzc : zeroCtor r o o c' = true := by
          simp [zeroCtor, ctorInh_of_kids k', List.head?_eq_none_iff.mp (head?_none_of_len hy)]
        have := List.length_pos_of_mem (List.mem_filter.mpr ⟨List.mem_range.mpr c'.2, hzc⟩)
        simp at hz
        omega
    | node c d k =>
      cases y with
      | base v =>
        have hzc : zeroCtor r o o c = true := by
          simp [zeroCtor, ctorInh_of_kids k, List.head?_eq_none_iff.mp (head?_none_of_len hx)]
        have := List.length_pos_of_mem (List.mem_filter.mpr ⟨List.mem_range.mpr c.2, hzc⟩)
        simp at hz
        omega
      | node c' d' k' =>
        have hzc : zeroCtor r o m c = true := by
          simp [zeroCtor, ctorInh_of_kids k, List.head?_eq_none_iff.mp (head?_none_of_len hx)]
        have hzc' : zeroCtor r o m c' = true := by
          simp [zeroCtor, ctorInh_of_kids k', List.head?_eq_none_iff.mp (head?_none_of_len hy)]
        have hcc : c = c' := Fin.ext (filter_le_one hz'
          (List.mem_filter.mpr ⟨List.mem_range.mpr c.2, hzc⟩)
          (List.mem_filter.mpr ⟨List.mem_range.mpr c'.2, hzc'⟩))
        subst hcc
        obtain ⟨hd, hk⟩ := restUnique_iff.mp ((hzr c c.2).resolve_left (by simp [hzc]))
        rw [hd d d']
        congr 1
        funext f p
        exact hk f (by simp) _ _
  | succ n ih =>
    intro x y hx hy
    cases x with
    | base u => exact absurd hx (by simp [treeLen])
    | node c d k =>
      cases y with
      | base v => exact absurd hy (by simp [treeLen])
      | node c' d' k' =>
        obtain ⟨f, hf⟩ := head?_some_of_len hx
        obtain ⟨f', hf'⟩ := head?_some_of_len hy
        have hsc : stepCtor r o m c = true := by
          simp [stepCtor, ctorInh_of_kids k, isEmpty_false_of_head? hf]
        have hsc' : stepCtor r o m c' = true := by
          simp [stepCtor, ctorInh_of_kids k', isEmpty_false_of_head? hf']
        have hcc : c = c' := Fin.ext (filter_le_one hst
          (List.mem_filter.mpr ⟨List.mem_range.mpr c.2, hsc⟩)
          (List.mem_filter.mpr ⟨List.mem_range.mpr c'.2, hsc'⟩))
        subst hcc
        rw [hf] at hf'
        cases hf'
        rw [treeLen_node_some hf] at hx hy
        have hmem := mem_of_head? hf
        have hS := muS_of_mem_selfFields hmem
        have e := ih (hS ▸ k ⟨f, lt_of_mem_selfFields hmem⟩ (g.denEmpty [m, c, 1, f]))
          (hS ▸ k' ⟨f, lt_of_mem_selfFields hmem⟩ (g.denEmpty [m, c, 1, f]))
          (by rw [treeLen_eqRec]; omega) (by rw [treeLen_eqRec]; omega)
        have hkf := eqRec_inj (F := fun j => muTy b g r o r.muN j) hS e
        obtain ⟨hd, hk⟩ := restUnique_iff.mp ((hsr c c.2).resolve_left (by simp [hsc]))
        rw [hd d d']
        congr 1
        funext f'' p
        by_cases hff : f''.val = f
        · have : f'' = ⟨f, lt_of_mem_selfFields hmem⟩ := Fin.ext hff
          subst this
          rw [pos_unique (listShaped_arg hs c.2 hmem) p (g.denEmpty [m, c, 1, f])]
          exact hkf
        · exact hk f'' (by rw [selfFields_eq (listShaped_le hs c.2) hf]; simpa using hff) _ _

theorem head?_of_isEmpty_false {l : List Nat} (h : l.isEmpty = false) : ∃ f, l.head? = some f := by
  cases l with
  | nil => simp at h
  | cons f _ => exact ⟨f, rfl⟩

/-- Where the length of a tree of a list-shaped type that has a value determines it, `lenDet`
holds. -/
theorem lenDet_of_injective {b g r : Ty} {o m : Nat} (x₀ : muTy b g r o r.muN m)
    (hi : Function.Injective (treeLen : muTy b g r o r.muN m → Nat)) :
    lenDet b g r o m = true := by
  have lenZero : ∀ {c : Fin (r.muN m)} (d : g.den [m, c, 0])
      (k : (f : Fin (r.muA m c)) → g.den [m, c, 1, f] → muTy b g r o r.muN (r.muS m c f)),
      zeroCtor r o m c = true → treeLen (MuVal.node c d k : muTy b g r o r.muN m) = 0 := by
    intro c d k h
    simp only [zeroCtor, Bool.and_eq_true, List.isEmpty_iff] at h
    exact treeLen_node_none (by rw [h.2]; rfl)
  -- A node of a constructor with a field of its own type, holding `x₀` there.
  have stepNode : ∀ (c : Fin (r.muN m)), stepCtor r o m c = true → ∃ f, ∃ hf : f ∈ r.selfFields m c,
      (r.selfFields m c).head? = some f ∧
      ∃ k : (f : Fin (r.muA m c)) → g.den [m, c, 1, f] → muTy b g r o r.muN (r.muS m c f),
        k ⟨f, lt_of_mem_selfFields hf⟩ (g.denEmpty [m, c, 1, f]) =
          (muS_of_mem_selfFields hf).symm ▸ x₀ := by
    intro c h
    simp only [stepCtor, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨f, hf⟩ := head?_of_isEmpty_false h.2
    obtain ⟨k⟩ := ctorInh_kids (b := b) (g := g) h.1
    have hm := mem_of_head? hf
    exact ⟨f, hm, hf, MuVal.upd k ⟨f, lt_of_mem_selfFields hm⟩
      (fun _ => (muS_of_mem_selfFields hm).symm ▸ x₀), by rw [MuVal.upd_self]⟩
  simp only [lenDet, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne, ne_eq,
    List.all_eq_true, List.mem_range, Bool.not_eq_true']
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · refine Classical.byContradiction fun hn => ?_
    by_cases ho : m = o
    · subst ho
      simp only [↓reduceIte] at hn
      obtain ⟨c, hc⟩ := List.exists_mem_of_length_pos (by omega :
        0 < ((List.range (r.muN m)).filter (zeroCtor r m m)).length)
      rw [List.mem_filter, List.mem_range] at hc
      have hz := hc.2
      simp only [zeroCtor, Bool.and_eq_true] at hz
      obtain ⟨k⟩ := ctorInh_kids (b := b) (g := g) hz.1
      have := @hi (.base b.empty) (.node ⟨c, hc.1⟩ (g.denEmpty _) k)
        (by rw [lenZero _ _ hc.2]; rfl)
      cases this
    · simp only [ho, ↓reduceIte, Nat.zero_add] at hn
      obtain ⟨c, c', hc, hc', hz, hz', hne⟩ := two_of_filter (by omega :
        2 ≤ ((List.range (r.muN m)).filter (zeroCtor r o m)).length)
      have hz1 := hz
      have hz1' := hz'
      simp only [zeroCtor, Bool.and_eq_true] at hz1 hz1'
      obtain ⟨k⟩ := ctorInh_kids (b := b) (g := g) hz1.1
      obtain ⟨k'⟩ := ctorInh_kids (b := b) (g := g) hz1'.1
      have := @hi (.node ⟨c, hc⟩ (g.denEmpty _) k) (.node ⟨c', hc'⟩ (g.denEmpty _) k')
        (by rw [lenZero _ _ hz, lenZero _ _ hz'])
      exact hne (congrArg Fin.val (MuVal.node.inj this).1)
  · refine Classical.byContradiction fun hn => ?_
    simp only [not_or, Classical.not_not, Bool.not_eq_true] at hn
    obtain ⟨ho, hb⟩ := hn
    subst ho
    obtain ⟨u, v, huv⟩ := exists_ne b hb
    exact huv (MuVal.base.inj (@hi (.base u) (.base v) rfl))
  · intro c hc
    cases hz : zeroCtor r o m c
    · exact .inl rfl
    · refine .inr (restUnique_iff.mpr ⟨fun d d' => ?_, fun f _ u v => ?_⟩)
      · have hz1 := hz
        simp only [zeroCtor, Bool.and_eq_true] at hz1
        obtain ⟨k⟩ := ctorInh_kids (b := b) (g := g) hz1.1
        have := @hi (.node ⟨c, hc⟩ d k) (.node ⟨c, hc⟩ d' k)
          (by rw [lenZero _ _ hz, lenZero _ _ hz])
        exact eq_of_heq (MuVal.node.inj this).2.1
      · have hz1 := hz
        simp only [zeroCtor, Bool.and_eq_true] at hz1
        obtain ⟨k⟩ := ctorInh_kids (b := b) (g := g) hz1.1
        have := @hi (.node ⟨c, hc⟩ (g.denEmpty _) (MuVal.upd k f fun _ => u))
          (.node ⟨c, hc⟩ (g.denEmpty _) (MuVal.upd k f fun _ => v))
          (by rw [lenZero _ _ hz, lenZero _ _ hz])
        have := congrFun (congrFun (eq_of_heq (MuVal.node.inj this).2.2) f) (g.denEmpty _)
        simpa [MuVal.upd_self] using this
  · refine Classical.byContradiction fun hn => ?_
    obtain ⟨c, c', hc, hc', hs, hs', hne⟩ := two_of_filter (by omega :
      2 ≤ ((List.range (r.muN m)).filter (stepCtor r o m)).length)
    obtain ⟨f, hf, hh, k, hk⟩ := stepNode ⟨c, hc⟩ hs
    obtain ⟨f', hf', hh', k', hk'⟩ := stepNode ⟨c', hc'⟩ hs'
    have := @hi (.node ⟨c, hc⟩ (g.denEmpty _) k) (.node ⟨c', hc'⟩ (g.denEmpty _) k')
      (by rw [treeLen_node_some hh, treeLen_node_some hh', hk, hk', treeLen_eqRec, treeLen_eqRec])
    exact hne (congrArg Fin.val (MuVal.node.inj this).1)
  · intro c hc
    cases hs : stepCtor r o m c
    · exact .inl rfl
    · obtain ⟨f, hf, hh, k, hk⟩ := stepNode ⟨c, hc⟩ hs
      refine .inr (restUnique_iff.mpr ⟨fun d d' => ?_, fun f' hf' u v => ?_⟩)
      · have := @hi (.node ⟨c, hc⟩ d k) (.node ⟨c, hc⟩ d' k)
          (by rw [treeLen_node_some hh, treeLen_node_some hh])
        exact eq_of_heq (MuVal.node.inj this).2.1
      · have hne : (⟨f, lt_of_mem_selfFields hf⟩ : Fin (r.muA m c)) ≠ f' :=
          fun e => hf' (by rw [← e]; exact hf)
        have := @hi (.node ⟨c, hc⟩ (g.denEmpty _) (MuVal.upd k f' fun _ => u))
          (.node ⟨c, hc⟩ (g.denEmpty _) (MuVal.upd k f' fun _ => v))
          (by rw [treeLen_node_some hh, treeLen_node_some hh, MuVal.upd_ne _ _ hne,
            MuVal.upd_ne _ _ hne])
        have := congrFun (congrFun (eq_of_heq (MuVal.node.inj this).2.2) f') (g.denEmpty _)
        simpa [MuVal.upd_self] using this

/-- `lenDet` decides whether the length of a tree of a list-shaped type that has a value determines
the tree. -/
theorem lenDet_iff {b g r : Ty} {o m : Nat} (hs : listShaped g r m = true)
    (x₀ : muTy b g r o r.muN m) :
    lenDet b g r o m = true ↔ Function.Injective (treeLen : muTy b g r o r.muN m → Nat) :=
  ⟨treeLen_injective hs, lenDet_of_injective x₀⟩

end Ty

/-! ## Places and paths -/

/-- Where a component of an argument lies: a value of the code `t`, or a tree of the `l`-th type of
the group with the base `b`, data and arguments `g` and recursive fields `r`, rooted at its `o`-th
type, from which a path descends into at most `n` more children. -/
inductive Place where
  | code (t : Ty)
  | tree (b g r : Ty) (o l n : Nat)

/-- The type of the values at a place. -/
@[reducible] def Place.denote : Place → Type
  | .code t => t.denote
  | .tree b g r o l _ => Ty.muTy b g r o r.muN l

mutual

/-- A path from a value at the place `s` to a component of it at the place `p`, applying no
function: the value itself, a component of one side of a pair, a component of a field of a declared
type with one constructor, or, at a tree, a component of one of its fields. -/
inductive Place.Path : Place → Place → Type
  /-- The value itself. -/
  | self (p : Place) : Place.Path p p
  /-- A component of the left side of a pair. -/
  | fst {a : Ty} (b : Ty) {p : Place} : Place.Path (.code a) p → Place.Path (.code (.prod a b)) p
  /-- A component of the right side of a pair. -/
  | snd (a : Ty) {b : Ty} {p : Place} : Place.Path (.code b) p → Place.Path (.code (.prod a b)) p
  /-- A component of a field of a declared type whose representation is `r`. -/
  | field (n : Lean.Name) (ps : Ty) {r : Ty} {p : Place} :
      Place.FieldPath (.code r) p → Place.Path (.code (.decl n ps r)) p
  /-- A component of a field of a tree. -/
  | node {b g r : Ty} {o l n : Nat} {p : Place} :
      Place.FieldPath (.tree b g r o l n) p → Place.Path (.tree b g r o l n) p

/-- A path from a value at the place `s` into one of its fields, where every value at `s` has one
shape: a field of a chain of fields; a field of the base of a recursive type with no other
constructor; and, at a tree of a type that is not the root and has one constructor, a component of
its data or of its child at a recursive field that holds a value of the group, which may descend once
more. -/
inductive Place.FieldPath : Place → Place → Type
  /-- A component of the first field of a chain. -/
  | head {a : Ty} (rest : Ty) {p : Place} :
      Place.Path (.code a) p → Place.FieldPath (.code (.prod a rest)) p
  /-- A component of a later field of a chain. -/
  | tail (a : Ty) {rest : Ty} {p : Place} :
      Place.FieldPath (.code rest) p → Place.FieldPath (.code (.prod a rest)) p
  /-- A field of the base of a recursive type whose values are all base values. -/
  | mu {b g r : Ty} {i : Nat} {p : Place} : (bif r.grows i then r.muN i else 0) = 0 →
      Place.FieldPath (.code b) p → Place.FieldPath (.code (.mu b g r i)) p
  /-- A field of a tree of a recursive type without a base of its own. -/
  | muAt {b g r : Ty} {j i : Nat} {p : Place} : r.growsAt j i = true →
      Place.FieldPath (.tree b g r j i r.items) p → Place.FieldPath (.code (.muAt b g r j i)) p
  /-- A field of the base of the root, where it has no other constructor. -/
  | base {b g r : Ty} {o l n : Nat} {p : Place} : l = o → r.muN l = 0 →
      Place.FieldPath (.code b) p → Place.FieldPath (.tree b g r o l n) p
  /-- A field of the data of a type that is not the root and has one constructor. -/
  | data {b g r : Ty} {o l n : Nat} {p : Place} : l ≠ o → r.muN l = 1 →
      Place.FieldPath (.code (g.ctorData l 0)) p → Place.FieldPath (.tree b g r o l n) p
  /-- A component of the child at the recursive field `f` of a type that is not the root and has
  one constructor, where the field holds a value of the group. -/
  | kid {b g r : Ty} {o l n : Nat} {p : Place} (hl : l ≠ o) (h : r.muN l = 1)
      (f : Fin (r.muA l 0)) : g.ctorArg l 0 f = .unit →
      Place.Path (.tree b g r o (r.muS l 0 f) n) p → Place.FieldPath (.tree b g r o l (n + 1)) p

end

mutual

/-- The component a path selects. -/
def Place.Path.get : {s p : Place} → Place.Path s p → s.denote → p.denote
  | _, _, .self _, x => x
  | _, _, .fst _ q, x => q.get x.1
  | _, _, .snd _ q, x => q.get x.2
  | _, _, .field _ _ q, x => q.get x
  | _, _, .node q, x => q.get x

/-- The component a path into a field selects. -/
def Place.FieldPath.get : {s p : Place} → Place.FieldPath s p → s.denote → p.denote
  | _, _, .head _ q, x => q.get x.1
  | _, _, .tail _ q, x => q.get x.2
  | _, _, @Place.FieldPath.mu _ _ r i _ h q, x =>
    q.get (MuVal.baseVal (N := fun j => bif r.grows i then r.muN j else 0) (l := i) h x)
  | _, _, .muAt h q, x => q.get (cast (Ty.denote_muAt h) x)
  | _, _, .base _ h q, x => q.get (MuVal.baseVal h x)
  | _, _, @Place.FieldPath.data _ g _ _ l _ _ hl h q, x =>
    q.get (cast (Ty.den_data g l 0) (MuVal.nodeData hl h x))
  | _, _, @Place.FieldPath.kid _ g _ _ l _ _ hl h f _ q, x =>
    q.get (MuVal.nodeKids hl h x f (g.denEmpty [l, 0, 1, f]))

end

namespace Place

section Trees

variable (b g r : Ty) (o : Nat) (baseP : List (Σ p, FieldPath (.code b) p))
  (dataP : (l : Nat) → List (Σ p, FieldPath (.code (g.ctorData l 0)) p))

/-- The paths into the base of the root of a tree, where it has no other constructor. -/
def treeBasePaths (n l : Nat) : List (Σ p, FieldPath (.tree b g r o l n) p) :=
  if h : l = o ∧ r.muN l = 0 then baseP.map fun q => ⟨q.1, .base h.1 h.2 q.2⟩ else []

/-- The paths into the data of a tree of a type that is not the root and has one constructor. -/
def treeDataPaths (n l : Nat) : List (Σ p, FieldPath (.tree b g r o l n) p) :=
  if h : l ≠ o ∧ r.muN l = 1 then (dataP l).map fun q => ⟨q.1, .data h.1 h.2 q.2⟩ else []

/-- The paths into the children of a tree of a type that is not the root and has one constructor,
from the paths `kids m` into a tree of the `m`-th type. -/
def treeKidPaths (n l : Nat) (kids : (m : Nat) → List (Σ p, FieldPath (.tree b g r o m n) p)) :
    List (Σ p, FieldPath (.tree b g r o l (n + 1)) p) :=
  if h : l ≠ o ∧ r.muN l = 1 then
    (List.finRange (r.muA l 0)).flatMap fun (f : Fin (r.muA l 0)) =>
      if hu : g.ctorArg l 0 f.val = .unit then
        ((⟨_, .self _⟩ :: (kids (r.muS l 0 f.val)).map fun q => ⟨q.1, .node q.2⟩ :
          List (Σ p, Path (.tree b g r o (r.muS l 0 f.val) n) p))).map
            fun q => ⟨q.1, .kid h.1 h.2 f hu q.2⟩
      else []
  else []

/-- Every path into the fields of a tree of the `l`-th type that descends into at most `n`
children. -/
def treeFieldPaths : (n l : Nat) → List (Σ p, FieldPath (.tree b g r o l n) p)
  | 0, l => treeBasePaths b g r o baseP 0 l ++ treeDataPaths b g r o dataP 0 l
  | n + 1, l => treeBasePaths b g r o baseP (n + 1) l ++ treeDataPaths b g r o dataP (n + 1) l ++
      treeKidPaths b g r o n l fun m => treeFieldPaths n m

end Trees

end Place

mutual

/-- Every path from a value of the code `t`, applying no function. Its match has no catch-all case,
so a code former added to `Ty` must say what its values' components are. -/
def Ty.paths : (t : Ty) → List (Σ p, Place.Path (.code t) p)
  | .unit => [⟨_, .self _⟩]
  | .bool => [⟨_, .self _⟩]
  | .nat => [⟨_, .self _⟩]
  | .int => [⟨_, .self _⟩]
  | .string => [⟨_, .self _⟩]
  | .list _ => [⟨_, .self _⟩]
  | .array _ => [⟨_, .self _⟩]
  | .option _ => [⟨_, .self _⟩]
  | .prod a b => ⟨_, .self _⟩ :: ((Ty.paths a).map fun q => ⟨q.1, .fst b q.2⟩) ++
      (Ty.paths b).map fun q => ⟨q.1, .snd a q.2⟩
  | .sum _ _ => [⟨_, .self _⟩]
  | .decl n ps r => ⟨_, .self _⟩ :: (Ty.fieldPaths r).map fun q => ⟨q.1, .field n ps q.2⟩
  | .fin _ => [⟨_, .self _⟩]
  | .atom _ => [⟨_, .self _⟩]
  | .arrow _ _ => [⟨_, .self _⟩]
  | .ref _ => [⟨_, .self _⟩]
  | .mu _ _ _ _ => [⟨_, .self _⟩]
  | .muAt _ _ _ _ _ => [⟨_, .self _⟩]

/-- Every path into a field of a value of the representation `r`. Its match has no catch-all case,
so a code former added to `Ty` must say what its values' fields are. -/
def Ty.fieldPaths : (r : Ty) → List (Σ p, Place.FieldPath (.code r) p)
  | .prod a rest => ((Ty.paths a).map fun q => ⟨q.1, .head rest q.2⟩) ++
      (Ty.fieldPaths rest).map fun q => ⟨q.1, .tail a q.2⟩
  | .mu b _ r i =>
    if h : (bif r.grows i then r.muN i else 0) = 0 then
      (Ty.fieldPaths b).map fun q => ⟨q.1, .mu h q.2⟩
    else []
  | .muAt b g r j i =>
    if h : r.growsAt j i = true then
      (Place.treeFieldPaths b g r j (Ty.fieldPaths b) (fun l => Ty.dataPaths g l) r.items i).map
        fun q => ⟨q.1, .muAt h q.2⟩
    else []
  | .unit => []
  | .bool => []
  | .nat => []
  | .int => []
  | .string => []
  | .list _ => []
  | .array _ => []
  | .option _ => []
  | .sum _ _ => []
  | .decl _ _ _ => []
  | .fin _ => []
  | .atom _ => []
  | .arrow _ _ => []
  | .ref _ => []

/-- `fieldPaths` of the data of the `l`-th type's first constructor in the chain `g`
(`Ty.dataPaths_eq`), by recursion on `g`. -/
def Ty.dataPaths : (g : Ty) → (l : Nat) → List (Σ p, Place.FieldPath (.code (g.ctorData l 0)) p)
  | .prod t _, 0 => Ty.ctorPaths t
  | .prod _ rest, l + 1 => Ty.dataPaths rest l
  | .unit, _ => []
  | .bool, _ => []
  | .nat, _ => []
  | .int, _ => []
  | .string, _ => []
  | .list _, _ => []
  | .array _, _ => []
  | .option _, _ => []
  | .sum _ _, _ => []
  | .decl _ _ _, _ => []
  | .fin _, _ => []
  | .atom _, _ => []
  | .arrow _ _, _ => []
  | .ref _, _ => []
  | .mu _ _ _ _, _ => []
  | .muAt _ _ _ _ _, _ => []

/-- `fieldPaths` of the data of the first constructor in the chain `t` of a type's constructors. -/
def Ty.ctorPaths : (t : Ty) → List (Σ p, Place.FieldPath (.code ((t.item 0).item 0)) p)
  | .prod c _ => Ty.chainPaths c
  | .unit => []
  | .bool => []
  | .nat => []
  | .int => []
  | .string => []
  | .list _ => []
  | .array _ => []
  | .option _ => []
  | .sum _ _ => []
  | .decl _ _ _ => []
  | .fin _ => []
  | .atom _ => []
  | .arrow _ _ => []
  | .ref _ => []
  | .mu _ _ _ _ => []
  | .muAt _ _ _ _ _ => []

/-- `fieldPaths` of the first item of the chain `c`. -/
def Ty.chainPaths : (c : Ty) → List (Σ p, Place.FieldPath (.code (c.item 0)) p)
  | .prod d _ => Ty.fieldPaths d
  | .unit => []
  | .bool => []
  | .nat => []
  | .int => []
  | .string => []
  | .list _ => []
  | .array _ => []
  | .option _ => []
  | .sum _ _ => []
  | .decl _ _ _ => []
  | .fin _ => []
  | .atom _ => []
  | .arrow _ _ => []
  | .ref _ => []
  | .mu _ _ _ _ => []
  | .muAt _ _ _ _ _ => []

end

theorem Ty.dataPaths_eq (g : Ty) (l : Nat) :
    Ty.dataPaths g l = Ty.fieldPaths (g.ctorData l 0) := by
  induction g generalizing l with
  | prod t rest _ ihr =>
    cases l with
    | succ l => rw [Ty.dataPaths]; exact ihr l
    | zero =>
      rw [Ty.dataPaths]
      cases t with
      | prod c _ =>
        rw [Ty.ctorPaths]
        cases c <;> rw [Ty.chainPaths] <;> rfl
      | _ => rw [Ty.ctorPaths]; rfl
  | _ => rw [Ty.dataPaths]; rfl

namespace Place

/-- Every path from a value at a place. -/
def paths : (s : Place) → List (Σ p, Path s p)
  | .code t => Ty.paths t
  | .tree b g r o l n => ⟨_, .self _⟩ ::
      (treeFieldPaths b g r o (Ty.fieldPaths b) (fun l => Ty.dataPaths g l) n l).map
        fun q => ⟨q.1, .node q.2⟩

/-- Every path into a field of a value at a place. -/
def fieldPaths : (s : Place) → List (Σ p, FieldPath s p)
  | .code r => Ty.fieldPaths r
  | .tree b g r o l n => treeFieldPaths b g r o (Ty.fieldPaths b) (fun l => Ty.dataPaths g l) n l

end Place

theorem Place.treeFieldPaths_base {b g r : Ty} {o : Nat}
    {baseP : List (Σ p, Place.FieldPath (.code b) p)}
    {dataP : (l : Nat) → List (Σ p, Place.FieldPath (.code (g.ctorData l 0)) p)} {n l : Nat}
    {x : Σ p, Place.FieldPath (.tree b g r o l n) p}
    (h : x ∈ Place.treeBasePaths b g r o baseP n l ++ Place.treeDataPaths b g r o dataP n l) :
    x ∈ Place.treeFieldPaths b g r o baseP dataP n l := by
  cases n with
  | zero => exact h
  | succ n => exact List.mem_append_left _ h

mutual

/-- `Place.paths` lists every path. -/
theorem Place.Path.mem_paths : {s p : Place} → (q : Place.Path s p) →
    (⟨p, q⟩ : Σ p, Place.Path s p) ∈ s.paths
  | _, _, .self (.code t) => by cases t <;> simp [Place.paths, Ty.paths]
  | _, _, .self (.tree _ _ _ _ _ _) => by simp [Place.paths]
  | _, _, .fst b q => by
      simp only [Place.paths, Ty.paths, List.cons_append, List.mem_cons, List.mem_append,
        List.mem_map]
      exact .inr (.inl ⟨_, Place.Path.mem_paths q, rfl⟩)
  | _, _, .snd a q => by
      simp only [Place.paths, Ty.paths, List.cons_append, List.mem_cons, List.mem_append,
        List.mem_map]
      exact .inr (.inr ⟨_, Place.Path.mem_paths q, rfl⟩)
  | _, _, .field n ps q => by
      simp only [Place.paths, Ty.paths, List.mem_cons, List.mem_map]
      exact .inr ⟨_, Place.FieldPath.mem_fieldPaths q, rfl⟩
  | _, _, .node q => by
      simp only [Place.paths, List.mem_cons, List.mem_map]
      exact .inr ⟨_, Place.FieldPath.mem_fieldPaths q, rfl⟩

/-- `Place.fieldPaths` lists every path into a field. -/
theorem Place.FieldPath.mem_fieldPaths : {s p : Place} → (q : Place.FieldPath s p) →
    (⟨p, q⟩ : Σ p, Place.FieldPath s p) ∈ s.fieldPaths
  | _, _, .head rest q => by
      simp only [Place.fieldPaths, Ty.fieldPaths, List.mem_append, List.mem_map]
      exact .inl ⟨_, Place.Path.mem_paths q, rfl⟩
  | _, _, .tail a q => by
      simp only [Place.fieldPaths, Ty.fieldPaths, List.mem_append, List.mem_map]
      exact .inr ⟨_, Place.FieldPath.mem_fieldPaths q, rfl⟩
  | _, _, .mu h q => by
      simp only [Place.fieldPaths, Ty.fieldPaths, h, ↓reduceDIte, List.mem_map]
      exact ⟨_, Place.FieldPath.mem_fieldPaths q, rfl⟩
  | _, _, .muAt h q => by
      simp only [Place.fieldPaths, Ty.fieldPaths, h, ↓reduceDIte, List.mem_map]
      exact ⟨_, Place.FieldPath.mem_fieldPaths q, rfl⟩
  | _, _, .base hl h q => by
      apply Place.treeFieldPaths_base
      apply List.mem_append_left
      rw [Place.treeBasePaths, dite_eq_left ⟨hl, h⟩]
      exact List.mem_map.mpr ⟨_, Place.FieldPath.mem_fieldPaths q, rfl⟩
  | _, _, @Place.FieldPath.data _ g _ _ l _ _ hl h q => by
      apply Place.treeFieldPaths_base
      apply List.mem_append_right
      rw [Place.treeDataPaths, dite_eq_left ⟨hl, h⟩, Ty.dataPaths_eq]
      exact List.mem_map.mpr ⟨_, Place.FieldPath.mem_fieldPaths q, rfl⟩
  | _, _, .kid hl h f hu q => by
      simp only [Place.fieldPaths, Place.treeFieldPaths]
      apply List.mem_append_right
      rw [Place.treeKidPaths, dite_eq_left ⟨hl, h⟩]
      refine List.mem_flatMap.mpr ⟨f, List.mem_finRange f, ?_⟩
      rw [dite_eq_left hu]
      exact List.mem_map.mpr ⟨_, Place.Path.mem_paths q, rfl⟩

end

/-! ## Clock parts -/

/-- How a clock reads a component at the place `p`: its value, of its own type, or, as a number, the
length of a list, the size of an array, or the length of a tree of a type shaped as a list
(`Ty.listShaped`, `Ty.treeLen`). -/
inductive ClockRead : Place → Type
  /-- The component's value, of its own type. -/
  | value (p : Place) : ClockRead p
  /-- The length of a list. -/
  | length (a : Ty) : ClockRead (.code (.list a))
  /-- The size of an array. -/
  | size (a : Ty) : ClockRead (.code (.array a))
  /-- The length of a tree of a type of a group shaped as a list. -/
  | treeLength {b g r : Ty} {o l n : Nat} : g.listShaped r l = true → ClockRead (.tree b g r o l n)

namespace ClockRead

/-- The type of what a reading reads: the component's own for its value, a number otherwise. -/
@[reducible] def Out : {p : Place} → ClockRead p → Type
  | _, .value p => p.denote
  | _, .length _ => Nat
  | _, .size _ => Nat
  | _, .treeLength _ => Nat

/-- What a reading reads from a component. -/
def read : {p : Place} → (k : ClockRead p) → p.denote → k.Out
  | _, .value _, x => x
  | _, .length _, x => x.length
  | _, .size _, x => x.size
  | _, .treeLength _, x => Ty.treeLen x

/-- Every reading of a component at the place `p`. -/
def all : (p : Place) → List (ClockRead p)
  | .code (.list a) => [.value _, .length a]
  | .code (.array a) => [.value _, .size a]
  | .code t => [.value (.code t)]
  | .tree _ g r _ l _ => .value _ :: if h : g.listShaped r l = true then [.treeLength h] else []

/-- `all` lists every reading. -/
theorem mem_all : {p : Place} → (k : ClockRead p) → k ∈ all p
  | _, .value (.code c) => by cases c <;> simp [all]
  | _, .value (.tree _ _ _ _ _ _) => by simp [all]
  | _, .length _ => by simp [all]
  | _, .size _ => by simp [all]
  | _, .treeLength h => by simp [all, h]

end ClockRead

/-- A path to a component at the place `p` of one of the arguments `as`. -/
inductive Place.ArgPath (p : Place) : List Ty → Type
  /-- A component of the first argument. -/
  | here {a : Ty} {as : List Ty} : Place.Path (.code a) p → Place.ArgPath p (a :: as)
  /-- A path into the arguments after the first. -/
  | there {a : Ty} {as : List Ty} : Place.ArgPath p as → Place.ArgPath p (a :: as)

namespace Place.ArgPath

/-- The component a path selects from a tuple of arguments. -/
def read {p : Place} : {as : List Ty} → ArgPath p as → Sig.Args as → p.denote
  | _ :: _, .here q, xs => q.get xs.1
  | _ :: _, .there q, xs => q.read xs.2

/-- Every path into the arguments `as`. -/
def paths : (as : List Ty) → List (Σ p, ArgPath p as)
  | [] => []
  | a :: as => ((Ty.paths a).map fun q => ⟨q.1, .here q.2⟩) ++
      (paths as).map fun q => ⟨q.1, .there q.2⟩

/-- `paths` lists every path into the arguments. -/
theorem mem_paths {p : Place} : {as : List Ty} → (q : ArgPath p as) →
    (⟨p, q⟩ : Σ p, ArgPath p as) ∈ paths as
  | _ :: _, .here q =>
    List.mem_append.mpr (.inl (List.mem_map.mpr ⟨_, Place.Path.mem_paths q, rfl⟩))
  | _ :: _, .there q => List.mem_append.mpr (.inr (List.mem_map.mpr ⟨_, mem_paths q, rfl⟩))

end Place.ArgPath

/-- A clock part of the arguments `as`: a component of one of them, reached without applying a
function, and a reading of it. -/
structure ArgClock (as : List Ty) where
  /-- Where the component lies. -/
  place : Place
  /-- The path to the component. -/
  path : Place.ArgPath place as
  /-- How the clock reads the component. -/
  reading : ClockRead place

namespace ArgClock

/-- The type of what a clock part reads. -/
abbrev Out {as : List Ty} (k : ArgClock as) : Type := k.reading.Out

/-- What a clock part of the arguments reads from a tuple of them. -/
def read {as : List Ty} (k : ArgClock as) (xs : Sig.Args as) : k.Out :=
  k.reading.read (k.path.read xs)

/-- Every clock part of the arguments `as`: each component of each argument, in order, with each of
its readings. -/
def all (as : List Ty) : List (ArgClock as) :=
  (Place.ArgPath.paths as).flatMap fun p => (ClockRead.all p.1).map fun r => ⟨p.1, p.2, r⟩

/-- `all` lists every clock part of the arguments. -/
theorem mem_all {as : List Ty} (k : ArgClock as) : k ∈ all as :=
  List.mem_flatMap.mpr ⟨⟨k.place, k.path⟩, Place.ArgPath.mem_paths k.path,
    List.mem_map.mpr ⟨k.reading, ClockRead.mem_all k.reading, rfl⟩⟩

end ArgClock

/-! ## Parts whose reading determines the arguments -/

/-- Reading the left side of pairs determines the pair exactly when it determines that side and the
right side has one value. -/
private theorem injective_fst_iff {α β γ : Type} (f : α → γ) (a₀ : α) (b₀ : β) :
    Function.Injective (fun p : α × β => f p.1) ↔ Function.Injective f ∧ ∀ x y : β, x = y := by
  constructor
  · intro h
    exact ⟨fun x y e => congrArg Prod.fst (@h (x, b₀) (y, b₀) e),
      fun x y => congrArg Prod.snd (@h (a₀, x) (a₀, y) rfl)⟩
  · rintro ⟨hf, hb⟩ ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ e
    exact Prod.ext (hf e) (hb y₁ y₂)

/-- Reading the right side of pairs determines the pair exactly when it determines that side and the
left side has one value. -/
private theorem injective_snd_iff {α β γ : Type} (f : β → γ) (a₀ : α) (b₀ : β) :
    Function.Injective (fun p : α × β => f p.2) ↔ Function.Injective f ∧ ∀ x y : α, x = y := by
  constructor
  · intro h
    exact ⟨fun x y e => congrArg Prod.snd (@h (a₀, x) (a₀, y) e),
      fun x y => congrArg Prod.fst (@h (x, b₀) (y, b₀) rfl)⟩
  · rintro ⟨hf, hb⟩ ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ e
    exact Prod.ext (hb x₁ x₂) (hf e)

/-- The length of a list determines it exactly when its elements have one value. -/
private theorem length_injective_iff {α : Type} :
    Function.Injective (List.length : List α → Nat) ↔ ∀ x y : α, x = y := by
  constructor
  · intro h x y
    exact List.cons.inj (@h [x] [y] rfl) |>.1
  · intro h l₁
    induction l₁ with
    | nil => intro l₂ e; cases l₂ with
      | nil => rfl
      | cons _ _ => exact absurd e (by simp)
    | cons x l ih => intro l₂ e; cases l₂ with
      | nil => exact absurd e (by simp)
      | cons y l' => rw [h x y, ih (by simpa using e)]

/-- The size of an array determines it exactly when its elements have one value. -/
private theorem size_injective_iff {α : Type} :
    Function.Injective (Array.size : Array α → Nat) ↔ ∀ x y : α, x = y := by
  constructor
  · intro h x y
    have e := congrArg Array.toList (@h #[x] #[y] rfl)
    exact List.cons.inj e |>.1
  · intro h a₁ a₂ e
    apply Array.toList_inj.mp
    apply length_injective_iff.mpr h
    simpa using e

namespace ClockRead

/-- Whether a reading determines the component: its value always, a list's length and an array's
size when the elements have one value, and a tree's length when `Ty.lenDet` says so. -/
def determines : {p : Place} → ClockRead p → Bool
  | _, .value _ => true
  | _, .length a => a.unique
  | _, .size a => a.unique
  | _, @treeLength b g r o l _ _ => Ty.lenDet b g r o l

/-- A reading determines a component that has the value `x₀` exactly when `determines` says so. -/
theorem determines_iff : {p : Place} → (k : ClockRead p) → p.denote →
    (k.determines = true ↔ Function.Injective k.read)
  | _, .value _, _ => ⟨fun _ _ _ h => h, fun _ => rfl⟩
  | _, .length a, _ => (Ty.unique_iff a).trans length_injective_iff.symm
  | _, .size a, _ => (Ty.unique_iff a).trans size_injective_iff.symm
  | _, .treeLength h, x₀ => Ty.lenDet_iff h x₀

end ClockRead

/-- The tuples of the arguments `as` have one value exactly when each argument's type has one. -/
theorem Sig.args_unique_iff : (as : List Ty) →
    (as.all Ty.unique = true ↔ ∀ xs ys : Sig.Args as, xs = ys)
  | [] => ⟨fun _ _ _ => rfl, fun _ => rfl⟩
  | a :: as => by
      rw [List.all_cons, Bool.and_eq_true, Ty.unique_iff, Sig.args_unique_iff as]
      constructor
      · rintro ⟨ha, hs⟩ ⟨x, xs⟩ ⟨y, ys⟩
        rw [ha x y, hs xs ys]
      · intro h
        exact ⟨fun x y => congrArg Prod.fst (h (x, Sig.Args.empty as) (y, Sig.Args.empty as)),
          fun xs ys => congrArg Prod.snd (h (a.empty, xs) (a.empty, ys))⟩

/-- Reordering the three conditions a step along a path joins. -/
private theorem and_step_iff {p q r : Prop} : (p ∧ q) ∧ r ↔ (r ∧ p) ∧ q :=
  ⟨fun ⟨⟨hp, hq⟩, hr⟩ => ⟨⟨hr, hp⟩, hq⟩, fun ⟨⟨hr, hp⟩, hq⟩ => ⟨⟨hp, hq⟩, hr⟩⟩

/-- Reading `H` through a bijection `e` determines the value exactly when `H` determines its
image. -/
theorem injective_bij_iff {α β γ : Type} (e : α → β) (e' : β → α) (h1 : ∀ x, e' (e x) = x)
    (h2 : ∀ y, e (e' y) = y) (H : β → γ) :
    Function.Injective (fun x => H (e x)) ↔ Function.Injective H :=
  ⟨fun h y y' hy => by
      rw [← h2 y, ← h2 y', h (show H (e (e' y)) = H (e (e' y')) by rw [h2, h2]; exact hy)],
    fun h x x' hx => by rw [← h1 x, ← h1 x', h hx]⟩

theorem injective_cast_iff {α β γ : Type} (e : α = β) (H : β → γ) :
    Function.Injective (fun x => H (cast e x)) ↔ Function.Injective H := by
  subst e
  exact Iff.rfl

/-- The children of the one constructor of the `l`-th type other than at `skip` have one value
exactly when `treeMulti` says each of their types has not two. -/
theorem Ty.kids_all_iff {b g r : Ty} {o l : Nat} (skip : Nat → Bool) :
    ((List.range (r.muA l 0)).all fun f => skip f || !Ty.treeMulti b g r o (r.muS l 0 f)) = true ↔
      ∀ f : Fin (r.muA l 0), skip f = false →
        ∀ u v : Ty.muTy b g r o r.muN (r.muS l 0 f), u = v := by
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true']
  constructor
  · intro h f hf
    exact Ty.treeMulti_eq_false_iff.mp ((h f f.2).resolve_left (by simp [hf]))
  · intro h f hf
    cases hs : skip f
    · exact .inr (Ty.treeMulti_eq_false_iff.mpr (h ⟨f, hf⟩ hs))
    · exact .inl rfl

mutual

/-- Whether the component a path selects determines the value: at each side of a pair and each field
of a chain, the rest has one value; at the data of a tree, each child's type has one value; and at a
child, the data have one value and each other child's type has one. -/
def Place.Path.determines : {s p : Place} → Place.Path s p → Bool
  | _, _, .self _ => true
  | _, _, .fst b q => b.unique && q.determines
  | _, _, .snd a q => a.unique && q.determines
  | _, _, .field _ _ q => q.determines
  | _, _, .node q => q.determines

/-- Whether the component a path into a field selects determines the value. -/
def Place.FieldPath.determines : {s p : Place} → Place.FieldPath s p → Bool
  | _, _, .head rest q => rest.unique && q.determines
  | _, _, .tail a q => a.unique && q.determines
  | _, _, .mu _ q => q.determines
  | _, _, .muAt _ q => q.determines
  | _, _, .base _ _ q => q.determines
  | _, _, @Place.FieldPath.data b g r o l _ _ _ _ q =>
    ((List.range (r.muA l 0)).all fun f => !Ty.treeMulti b g r o (r.muS l 0 f)) && q.determines
  | _, _, @Place.FieldPath.kid b g r o l _ _ _ _ f _ q =>
    ((g.ctorData l 0).unique && (List.range (r.muA l 0)).all fun f' =>
      f' == f.val || !Ty.treeMulti b g r o (r.muS l 0 f')) && q.determines

end

mutual

/-- Reading `G` of the component a path selects determines a value that has `x₀` exactly when the
path's `determines` says so and `G` determines the component. -/
theorem Place.Path.injective_iff {γ : Type} : {s p : Place} → (q : Place.Path s p) →
    (x₀ : s.denote) → (G : p.denote → γ) →
    (Function.Injective (fun x => G (q.get x)) ↔ q.determines = true ∧ Function.Injective G)
  | _, _, .self _, _, _ => ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩
  | _, _, @Place.Path.fst a b _ q, x₀, G => by
      rw [Place.Path.determines, Bool.and_eq_true, Ty.unique_iff]
      exact (injective_fst_iff (fun y => G (q.get y)) x₀.1 x₀.2).trans
        ((and_congr (Place.Path.injective_iff q x₀.1 G) Iff.rfl).trans and_step_iff)
  | _, _, @Place.Path.snd b a _ q, x₀, G => by
      rw [Place.Path.determines, Bool.and_eq_true, Ty.unique_iff]
      exact (injective_snd_iff (fun y => G (q.get y)) x₀.1 x₀.2).trans
        ((and_congr (Place.Path.injective_iff q x₀.2 G) Iff.rfl).trans and_step_iff)
  | _, _, .field _ _ q, x₀, G => Place.FieldPath.injective_iff q x₀ G
  | _, _, .node q, x₀, G => Place.FieldPath.injective_iff q x₀ G

/-- Reading `G` of the component a path into a field selects determines a value that has `x₀`
exactly when the path's `determines` says so and `G` determines the component. -/
theorem Place.FieldPath.injective_iff {γ : Type} : {s p : Place} → (q : Place.FieldPath s p) →
    (x₀ : s.denote) → (G : p.denote → γ) →
    (Function.Injective (fun x => G (q.get x)) ↔ q.determines = true ∧ Function.Injective G)
  | _, _, @Place.FieldPath.head a _ rest q, x₀, G => by
      rw [Place.FieldPath.determines, Bool.and_eq_true, Ty.unique_iff]
      exact (injective_fst_iff (fun y => G (q.get y)) x₀.1 x₀.2).trans
        ((and_congr (Place.Path.injective_iff q x₀.1 G) Iff.rfl).trans and_step_iff)
  | _, _, @Place.FieldPath.tail rest _ a q, x₀, G => by
      rw [Place.FieldPath.determines, Bool.and_eq_true, Ty.unique_iff]
      exact (injective_snd_iff (fun y => G (q.get y)) x₀.1 x₀.2).trans
        ((and_congr (Place.FieldPath.injective_iff q x₀.2 G) Iff.rfl).trans and_step_iff)
  | _, _, @Place.FieldPath.mu _ _ r i _ h q, x₀, G => by
      rw [Place.FieldPath.determines]
      exact (injective_bij_iff
        (MuVal.baseVal (N := fun j => bif r.grows i then r.muN j else 0) (l := i) h) MuVal.base
        (MuVal.base_baseVal (N := fun j => bif r.grows i then r.muN j else 0) h) (fun _ => rfl)
        fun y => G (q.get y)).trans (Place.FieldPath.injective_iff q
          (MuVal.baseVal (N := fun j => bif r.grows i then r.muN j else 0) (l := i) h x₀) G)
  | _, _, .muAt h q, x₀, G => by
      rw [Place.FieldPath.determines]
      show Function.Injective (fun x => G (q.get (cast (Ty.denote_muAt h) x))) ↔ _
      exact (injective_cast_iff (Ty.denote_muAt h) fun y => G (q.get y)).trans
        (Place.FieldPath.injective_iff q (cast (Ty.denote_muAt h) x₀) G)
  | _, _, .base hl h q, x₀, G => by
      subst hl
      rw [Place.FieldPath.determines]
      show Function.Injective (fun x => G (q.get (MuVal.baseVal h x))) ↔ _
      exact (injective_bij_iff (MuVal.baseVal h) MuVal.base (MuVal.base_baseVal h) (fun _ => rfl)
        fun y => G (q.get y)).trans (Place.FieldPath.injective_iff q (MuVal.baseVal h x₀) G)
  | _, _, @Place.FieldPath.data b g r o l _ _ hl h q, x₀, G => by
      rw [Place.FieldPath.determines, Bool.and_eq_true]
      have hk := ((MuVal.kids_unique_iff (MuVal.nodeKids hl h x₀)
        fun f => g.denEmpty [l, 0, 1, f]).trans
          (⟨fun h f _ => h f, fun h f => h f rfl⟩ :
            _ ↔ ∀ f : Fin (r.muA l 0), false = false → _)).trans
        (Ty.kids_all_iff (b := b) (g := g) (r := r) (o := o) (l := l) fun _ => false).symm
      simp only [Bool.false_or] at hk
      show Function.Injective (fun x : Ty.muTy b g r o r.muN l =>
        G (q.get (cast (Ty.den_data g l 0) (MuVal.nodeData hl h x)))) ↔ _
      exact (MuVal.injective_data_iff hl h x₀ fun d => G (q.get (cast (Ty.den_data g l 0) d))).trans
        ((and_congr ((injective_cast_iff (Ty.den_data g l 0) fun y => G (q.get y)).trans
          (Place.FieldPath.injective_iff q
            (cast (Ty.den_data g l 0) (MuVal.nodeData hl h x₀)) G)) hk).trans and_step_iff)
  | _, _, @Place.FieldPath.kid b g r o l _ _ hl h f hu q, x₀, G => by
      rw [Place.FieldPath.determines, Bool.and_eq_true, Bool.and_eq_true, Ty.unique_iff,
        Ty.kids_all_iff (b := b) (o := o) fun f' => f' == f.val]
      show Function.Injective
        (fun x => G (q.get (MuVal.nodeKids hl h x f (g.denEmpty [l, 0, 1, f])))) ↔ _
      rw [MuVal.injective_kid_iff hl h x₀ (fun f => g.denEmpty [l, 0, 1, f]) f
        (Ty.pos_unique hu) fun y => G (q.get y),
        Place.Path.injective_iff q (MuVal.nodeKids hl h x₀ f (g.denEmpty [l, 0, 1, f])) G,
        Ty.unique_congr (Ty.den_data g l 0)]
      constructor
      · rintro ⟨⟨hq, hG⟩, hd, ho⟩
        exact ⟨⟨⟨hd, fun f' hf' => ho f' fun e => by simp [e] at hf'⟩, hq⟩, hG⟩
      · rintro ⟨⟨⟨hd, ho⟩, hq⟩, hG⟩
        exact ⟨⟨hq, hG⟩, hd, fun f' hf' => ho f' (by simpa [Fin.val_inj] using hf')⟩

end

namespace Place.ArgPath

/-- Whether the component a path into the arguments selects determines the tuple of them: it
determines its argument, and every other argument's type has one value. -/
def determines {p : Place} : {as : List Ty} → ArgPath p as → Bool
  | _ :: as, .here q => q.determines && as.all Ty.unique
  | a :: _, .there q => a.unique && q.determines

/-- Reading `G` of the component a path into the arguments selects determines the tuple of them
exactly when the path's `determines` says so and `G` determines the component. -/
theorem injective_iff {γ : Type} {p : Place} : {as : List Ty} → (q : ArgPath p as) →
    (G : p.denote → γ) →
    (Function.Injective (fun xs => G (q.read xs)) ↔ q.determines = true ∧ Function.Injective G)
  | a :: as, .here q, G => by
      rw [determines, Bool.and_eq_true, Sig.args_unique_iff as]
      exact (injective_fst_iff (fun y => G (q.get y)) a.empty (Sig.Args.empty as)).trans
        ((and_congr (Place.Path.injective_iff q a.empty G) Iff.rfl).trans
          ⟨fun ⟨⟨hp, hg⟩, hs⟩ => ⟨⟨hp, hs⟩, hg⟩, fun ⟨⟨hp, hs⟩, hg⟩ => ⟨⟨hp, hg⟩, hs⟩⟩)
  | a :: as, .there q, G => by
      rw [determines, Bool.and_eq_true, Ty.unique_iff]
      exact (injective_snd_iff (fun y => G (q.read y)) a.empty (Sig.Args.empty as)).trans
        ((and_congr (injective_iff q G) Iff.rfl).trans and_step_iff)

end Place.ArgPath

namespace ArgClock

/-- Whether a clock part's reading determines the tuple of arguments: its path selects a component
that determines them, and its reading determines that component. -/
def determines {as : List Ty} (k : ArgClock as) : Bool := k.path.determines && k.reading.determines

/-- A clock part's reading determines the arguments exactly when `determines` says so. -/
theorem determines_iff {as : List Ty} (k : ArgClock as) :
    k.determines = true ↔ Function.Injective k.read := by
  rw [determines, Bool.and_eq_true,
    ClockRead.determines_iff k.reading (k.path.read (Sig.Args.empty as))]
  exact (Place.ArgPath.injective_iff k.path k.reading.read).symm

/-- A clock part's reading does not determine the arguments exactly when two tuples of them read
the same there and differ. -/
theorem determines_eq_false_iff {as : List Ty} (k : ArgClock as) :
    k.determines = false ↔ ∃ xs ys, xs ≠ ys ∧ k.read xs = k.read ys := by
  rw [← Bool.not_eq_true, determines_iff]
  constructor
  · intro h
    refine Classical.byContradiction fun hn => h fun xs ys e => ?_
    exact Classical.byContradiction fun hne => hn ⟨xs, ys, hne, e⟩
  · rintro ⟨xs, ys, hne, e⟩ h
    exact hne (h e)

end ArgClock

/-! ## The declaration -/

/-- Whether the code is that of a `LeanIntent.Clock α`: a declared type of the name its code
carries. -/
def Ty.isClock : Ty → Bool
  | .decl n _ _ => decide (n = Clock.codeName)
  | _ => false

/-- The code is that of a `LeanIntent.Clock α` exactly when `isClock` says so. -/
theorem Ty.isClock_iff (t : Ty) : t.isClock = true ↔ ∃ ps r, t = .decl Clock.codeName ps r := by
  cases t <;> simp [Ty.isClock]

/-- Whether a place holds values of a `LeanIntent.Clock α`: a code that is one. A tree of a group
is not one, since `LeanIntent.Clock` is not recursive. -/
def Place.isClock : Place → Bool
  | .code t => t.isClock
  | .tree _ _ _ _ _ _ => false

/-- A place holds values of a `LeanIntent.Clock α` exactly when `isClock` says so. -/
theorem Place.isClock_iff (p : Place) :
    p.isClock = true ↔ ∃ ps r, p = .code (.decl Clock.codeName ps r) := by
  cases p with
  | code t => simp [Place.isClock, Ty.isClock_iff]
  | tree _ _ _ _ _ _ => simp [Place.isClock]

namespace ArgClock

/-- The project declared the clock part `k` its subject's clock: `k` reads a component of type
`LeanIntent.Clock α` for some `α`, whose code is the declared type of the name `Clock.codeName`. -/
def InClock {as : List Ty} (k : ArgClock as) : Prop :=
  ∃ ps r, k.place = .code (.decl Clock.codeName ps r)

instance {as : List Ty} (k : ArgClock as) : Decidable k.InClock :=
  decidable_of_iff _ (Place.isClock_iff k.place)

end ArgClock

/-- Whether a value of the code holds a `LeanIntent.Clock` anywhere: in a field of a declared type, or
the declared type itself. A declared type's parameters are not read: a parameter is part of a value
only through the fields that use it, which its representation holds. Its match has no catch-all
case, so a code former added to `Ty` must say whether it holds one. -/
def Ty.namesClock : Ty → Bool
  | .unit => false
  | .bool => false
  | .nat => false
  | .int => false
  | .string => false
  | .fin _ => false
  | .atom _ => false
  | .list a => a.namesClock
  | .array a => a.namesClock
  | .option a => a.namesClock
  | .prod a b => a.namesClock || b.namesClock
  | .sum a b => a.namesClock || b.namesClock
  | .arrow a b => a.namesClock || b.namesClock
  | .decl n _ r => decide (n = Clock.codeName) || r.namesClock
  | .ref _ => false
  | .mu b g r _ => b.namesClock || g.namesClock || r.namesClock
  | .muAt b g r _ _ => b.namesClock || g.namesClock || r.namesClock

/-- Whether a tree of the `l`-th type of the group with the base `b`, data and arguments `g` and
recursive fields `r`, rooted at its `o`-th type, holds a `LeanIntent.Clock` where no clock part
reaches it, given whether its base (`baseS`), the data of the first constructor of each type
(`dataS`) and each child of the `m`-th type (`kid m`) hold one so: where every value is a base value,
its base does; where every value is a node of one constructor, its data or a child does, a child at a
field that holds a function holding one wherever the field's arguments or the group name one; and
otherwise, one does wherever the group names one. -/
def Place.treeStrayAt (b g r : Ty) (o : Nat) (baseS : Bool) (dataS : Nat → Bool)
    (kid : Nat → Bool) (l : Nat) : Bool :=
  if l = o ∧ r.muN l = 0 then baseS
  else if l ≠ o ∧ r.muN l = 1 then
    dataS l || (List.range (r.muA l 0)).any fun f =>
      if g.ctorArg l 0 f = .unit then kid (r.muS l 0 f)
      else (g.ctorArg l 0 f).namesClock || b.namesClock || g.namesClock
  else b.namesClock || g.namesClock

/-- `treeStrayAt` for the clock parts that descend into at most `n` more children: past that bound,
a child holds one wherever the group names one. -/
def Place.treeStray (b g r : Ty) (o : Nat) (baseS : Bool) (dataS : Nat → Bool) :
    (n l : Nat) → Bool
  | 0, l => Place.treeStrayAt b g r o baseS dataS (fun _ => b.namesClock || g.namesClock) l
  | n + 1, l => Place.treeStrayAt b g r o baseS dataS (Place.treeStray b g r o baseS dataS n) l

mutual

/-- Whether a value of the code holds a `LeanIntent.Clock` where no clock part reaches it: inside a
list, an array, an option, a sum, a function, a declared type with several constructors, or a type
of a recursive group where its values have several shapes or past a child at a field that holds a
function. The clock parts reach through pairs and the fields of every declared type with one
constructor, `LeanIntent.Clock` included, and through the nodes of one shape of a recursive group,
and a `LeanIntent.Clock` they reach, there too, is a declaration the class reads; the values nested
in a recursive type's values through a type with several shapes hold it again where they do not
reach. A parameter of a declared type is not a part of its values except through the fields that
hold it, which are read instead. -/
def Ty.strayClock : Ty → Bool
  | .prod a b => Ty.strayClock a || Ty.strayClock b
  | .decl _ _ r => Ty.fieldStrayClock r
  | t => t.namesClock

/-- Whether a value of the representation `r` holds a `LeanIntent.Clock` where no clock part reaches
it: in a chain of fields, wherever a field does; in a recursive type, as `Place.treeStray` says,
from its base and the data of its constructors; and in any other representation, that of a type with
several constructors, wherever it names one. -/
def Ty.fieldStrayClock : Ty → Bool
  | .prod a rest => Ty.strayClock a || Ty.fieldStrayClock rest
  | .mu b g r i =>
    if (bif r.grows i then r.muN i else 0) = 0 then Ty.fieldStrayClock b
    else b.namesClock || g.namesClock || r.namesClock
  | .muAt b g r j i =>
    if r.growsAt j i = true then
      Place.treeStray b g r j (Ty.fieldStrayClock b) (fun l => Ty.dataStrayClock g l) r.items i
    else false
  | r => r.namesClock

/-- `fieldStrayClock` of the data of the `l`-th type's first constructor in the chain `g`, by
recursion on `g`. -/
def Ty.dataStrayClock : Ty → Nat → Bool
  | .prod t _, 0 => Ty.ctorStrayClock t
  | .prod _ rest, l + 1 => Ty.dataStrayClock rest l
  | _, _ => false

/-- `fieldStrayClock` of the data of the first constructor in the chain `t`. -/
def Ty.ctorStrayClock : Ty → Bool
  | .prod c _ => Ty.chainStrayClock c
  | _ => false

/-- `fieldStrayClock` of the first item of the chain `c`. -/
def Ty.chainStrayClock : Ty → Bool
  | .prod d _ => Ty.fieldStrayClock d
  | _ => false

end

/-- Whether an argument of the type `σ` denotes holds a `LeanIntent.Clock` where no clock part
reaches it: a declaration of a clock that the trivial-witness check cannot read, so it refuses every
verdict about the type. -/
def Sig.strayClock (σ : Sig) : Bool := σ.args.any Ty.strayClock

/-! ## Scripts of timed actions -/

namespace Sig

/-- The function `f` of the arguments `as` reads only the clock part `k`: two tuples of arguments
that read the same there give the same value. -/
def Fn.ReadsOnly {b : Ty} {as : List Ty} (f : Fn b as) (k : ArgClock as) : Prop :=
  ∀ xs ys, k.read xs = k.read ys → f.apply xs = f.apply ys

/-- A function of the arguments is the function that returns what it returns on the tuple of them.
-/
theorem Fn.curry_apply {b : Ty} : (as : List Ty) → (f : Fn b as) → Fn.curry b as f.apply = f
  | [], _ => rfl
  | _ :: as, f => funext fun x => Fn.curry_apply as (f x)

/-- A constant function reads only any clock part. -/
theorem Fn.const_readsOnly {b : Ty} (v : b.denote) {as : List Ty} (k : ArgClock as) :
    (Fn.const b v as).ReadsOnly k := fun xs ys _ => by
  rw [Fn.apply_const, Fn.apply_const]

end Sig

namespace ArgClock

open Sig

/-- The script of timed actions that takes the action `s n` whenever the clock part `k` reads `n`,
as a function of the arguments. -/
def script {b : Ty} {as : List Ty} (k : ArgClock as) (s : k.Out → b.denote) : Fn b as :=
  Fn.curry b as fun xs => s (k.read xs)

/-- A script returns its action at the clock's reading. -/
theorem apply_script {b : Ty} {as : List Ty} (k : ArgClock as) (s : k.Out → b.denote)
    (xs : Args as) : (k.script s).apply xs = s (k.read xs) :=
  Fn.apply_curry as _ xs

/-- A function reads only the clock part `k` exactly when it is a script of timed actions on `k`: it
takes, whenever `k` reads `n`, one action fixed for `n`. -/
theorem readsOnly_iff_script {b : Ty} {as : List Ty} (k : ArgClock as) (f : Fn b as) :
    f.ReadsOnly k ↔ ∃ s : k.Out → b.denote, f = k.script s := by
  constructor
  · intro h
    let _ : Nonempty (Args as) := ⟨Args.empty as⟩
    refine ⟨fun n => f.apply (Classical.epsilon fun ys => k.read ys = n), ?_⟩
    rw [← Fn.curry_apply as f]
    unfold script
    congr 1
    funext xs
    rw [Fn.curry_apply as f]
    exact h _ _ (Classical.epsilon_spec (p := fun ys => k.read ys = k.read xs) ⟨xs, rfl⟩).symm
  · rintro ⟨s, rfl⟩ xs ys e
    rw [apply_script, apply_script, e]

end ArgClock

end LeanIntent
