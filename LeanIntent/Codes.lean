/-!
# The types the degenerate class covers

The degenerate subjects of an intent record are fixed by the subject's type alone: each constant
function, the identity, the empty output and each projection. Lean's logic cannot inspect a type, so
the class is computed from a *code* for the type: a value of the closed inductive type `Ty`, whose
denotation `Ty.denote` is a type that stands for it through an isomorphism (`Iso`). The codes are
those of the unit type, `Bool`, `Nat`, `Int` and `String`, of `Fin (n + 1)` and the machine types
`Atom` names, of lists, arrays, options, pairs, sums and functions of coded types, each of which
denotes the type itself, and of the structures and inductive types a project declares (`Ty.decl`),
which `LeanIntent.Declared` writes from each declaration. `LeanIntent.Degenerate` builds the class
over functions of such types; a type with no code is not covered.

The code of a declared type, `Ty.decl n ps r`, holds its name `n`, the chain of the codes of its type
parameters `ps`, and its *representation* `r`: for each constructor in declaration order, the chain
of its fields' codes in declaration order, each field paired with the chain after it and the last
with the unit code; one constructor is represented by its chain, and several by the sum of the first
one's chain and the representation of the rest. It denotes its representation, and every rule below
is its representation's, so the class treats a declared type as the sum of its constructors' chains;
only its projections differ, which reach into its fields and not into the chain that holds them
(`LeanIntent.Degenerate`). Its name and parameters keep apart two declared types whose
representations are equal.

The representation of a recursive, nested or mutual type a project declares is `Ty.mu b g r i`, the
`i`-th type of its *group*: the types its declaration declares and those its nested occurrences make,
such as `List T`, as Lean's recursor for it lists them. Its *base* `b` is the representation, as
above, of its constructors whose fields hold no value of a type of the group, in declaration order.
`g` and `r` list the group's types, each with its other constructors in declaration order: in `g`
each constructor is the chain of the chain of the codes of its fields that hold no value of the group
and the chain of the codes of its recursive fields' arguments (the unit code for a field that holds a
value of the group itself, the argument's code for a function to one, and the chain of the arguments'
codes for a function of several); in `r` it is the chain of the types of the group its recursive
fields hold, `ref l` for the `l`-th. `r` holds only those numbers, never a field's code, so whether the
group grows (`Ty.grows`) evaluates alike whatever its type parameters are. It denotes the trees of
`MuVal`: a base value, or a constructor with the data of its other fields and a child at each position
of each recursive field, the positions being the values of the field's arguments. Where the group
does not grow, so that it may have finitely many values, it denotes its base values alone; the deriving
handler refuses such a type. `Ty.ref` denotes the unit type.

For each code this module computes:

* `Ty.empty`, the empty value of the type: zero, the empty string, list or array, `none`, `false`
  and the unit value, componentwise for a pair, the left side's for a sum, for a declared type, its
  first constructor applied to its fields' empty values, for a recursive one its first base
  constructor applied to its fields' empty values, zero for `Fin (n + 1)` and for a machine type, the
  character of code zero for `Char`, and for a function the constant function at the empty value of
  its result;
* `Ty.Small`, the rule that fixes the values at which the class takes constant subjects: a number, a
  string, a list or an array only its empty value; the unit type, `Bool`, `Fin (n + 1)` and a machine
  type every value; an option, a pair or a sum every value built from values its components' rules
  admit; a declared type each constructor applied to each combination of values its fields' rules
  admit, and a recursive one each of its base constructors so applied, by analogy with `List`, whose
  only constant is `[]`, and `Nat`, whose only constant is `0`; and a function type every function
  where it has finitely many, and otherwise the constant function at each value its result's rule
  admits. The rule is fixed here, with the class, so that no record chooses which constants it is
  checked against.
* `Ty.finite`, which decides whether the type has finitely many values: when it holds, a list holds
  every value (`Ty.exists_list_of_finite`) and the rule admits each (`Ty.small_of_finite`), and when
  it fails, the type has infinitely many (`Ty.infinite`). A function type has finitely many exactly
  when its result has one value (`Ty.unique`), or its argument and its result have finitely many. A
  recursive type whose group grows has infinitely many (`Ty.mu_infinite`): each type the narrowing
  in `Ty.grows` keeps has a constructor that holds one of them, so it has values of every depth.
* `Ty.count`, the number of constants the class would list one by one, and `Ty.part`, the list of
  them where `Ty.count` is at most `Ty.listBound`, 255 (`Ty.mem_part_iff`). A machine type and a
  function type count as above the bound whatever their values, a bit vector of any width included. So
  every type the rule admits too many values of to list, finite or not, is checked without listing
  them: `LeanIntent.Degenerate` takes its empty value alone and all the others as one member.
-/

namespace LeanIntent

/-- The machine types of Lean's core library the degenerate class covers, each with finitely many
values (`Atom.exists_list`). -/
inductive Atom where
  | char
  | uint8
  | uint16
  | uint32
  | uint64
  | usize
  | int8
  | int16
  | int32
  | int64
  | isize
  | float
  | float32
  | bitVec (w : Nat)
  deriving DecidableEq

namespace Atom

/-- The type an atom denotes. -/
@[reducible] def denote : Atom → Type
  | char => Char
  | uint8 => UInt8
  | uint16 => UInt16
  | uint32 => UInt32
  | uint64 => UInt64
  | usize => USize
  | int8 => Int8
  | int16 => Int16
  | int32 => Int32
  | int64 => Int64
  | isize => ISize
  | float => Float
  | float32 => Float32
  | bitVec w => BitVec w

/-- The empty value of a machine type: zero, for `Char` the character of code zero, and for `Float`
and `Float32` the value whose bits are all zero, positive zero. -/
def empty : (k : Atom) → k.denote
  | char => Char.ofNat 0
  | uint8 => (0 : UInt8)
  | uint16 => (0 : UInt16)
  | uint32 => (0 : UInt32)
  | uint64 => (0 : UInt64)
  | usize => (0 : USize)
  | int8 => (0 : Int8)
  | int16 => (0 : Int16)
  | int32 => (0 : Int32)
  | int64 => (0 : Int64)
  | isize => (0 : ISize)
  | float => Float.ofBits 0
  | float32 => Float32.ofBits 0
  | bitVec w => (0 : BitVec w)

/-- Whether the machine type has exactly one value: only a bit vector of width zero. -/
def unique : Atom → Bool
  | bitVec w => w == 0
  | _ => false

end Atom

/-- Codes of the data types and function types the degenerate class covers. -/
inductive Ty where
  | unit
  | bool
  | nat
  | int
  | string
  | list (a : Ty)
  | array (a : Ty)
  | option (a : Ty)
  | prod (a b : Ty)
  | sum (a b : Ty)
  /-- A type the project declares (`LeanIntent.Declared`): its name, the chain of the codes of its
  type parameters, and its representation, the code of its constructors and their fields in
  declaration order. -/
  | decl (name : Lean.Name) (params rep : Ty)
  /-- `Fin (n + 1)`, which has `n + 1` values. `Fin 0` has no value, so no code. -/
  | fin (n : Nat)
  /-- A machine type. -/
  | atom (k : Atom)
  /-- Functions from `a` to `b`. -/
  | arrow (a b : Ty)
  /-- In the recursive fields of a group (`mu`), the group's `l`-th type, which a field holds. It
  denotes the unit type. -/
  | ref (l : Nat)
  /-- The `i`-th type of a group of recursive, nested or mutual types a project declares
  (`LeanIntent.Declared`). `base` is the representation of the constructors of the `i`-th type whose
  fields hold no value of a type of the group, in declaration order. `group` is the chain of the
  group's types, each the chain of its other constructors in declaration order, each the chain of
  the chain of the codes of its fields that hold no value of the group and the chain of the codes of
  its recursive fields' arguments; `refs` is the same chain with each constructor the chain of the
  types of the group its recursive fields hold, as `ref l`. Its values are the trees `MuVal`
  builds. -/
  | mu (base group refs : Ty) (i : Nat)
  deriving DecidableEq

/-- The values of the `j`-th type of a recursive group, built from a base value `x : B` of its `i`-th
type, or from the constructor `c` of the `j`-th type (of `N j`) with the data `d` of its fields and,
for each of its `A j c` recursive fields `f`, a child at each position of `P j c f`, a value of the
group's `S j c f`-th type. A child is a smaller value, so every value is a well-founded tree: each path down from it through
its children is finite, though a node whose recursive field is a function can have infinitely many
children. -/
inductive MuVal (B : Type) (i : Nat) (N : Nat → Nat) (D : Nat → Nat → Type) (A : Nat → Nat → Nat)
    (P : Nat → Nat → Nat → Type) (S : Nat → Nat → Nat → Nat) : Nat → Type where
  /-- A value of the `i`-th type built by one of its constructors whose fields hold no value of the
  group. -/
  | base (x : B) : MuVal B i N D A P S i
  /-- A value built by the constructor `c` from its data and its children. -/
  | node {j : Nat} (c : Fin (N j)) (d : D j c)
      (k : (f : Fin (A j c)) → P j c f → MuVal B i N D A P S (S j c f)) : MuVal B i N D A P S j

namespace Ty

/-- The `n`-th item of the chain `prod a₀ (prod a₁ (… unit))`, and the unit code past its end. -/
def item : Ty → Nat → Ty
  | prod a _, 0 => a
  | prod _ r, n + 1 => item r n
  | _, _ => unit

/-- The number of items of a chain. -/
def items : Ty → Nat
  | prod _ r => items r + 1
  | _ => 0

/-- The type of the group a recursive field holds: `l` for `ref l`. -/
def refTarget : Ty → Nat
  | ref l => l
  | _ => 0

/-- The number of constructors of the `j`-th type of the group whose recursive fields `r` lists: the
chain of its types, each the chain of its constructors, each the chain of its recursive fields, a
field that holds a value of the group's `l`-th type, or a function to one, listed as `ref l`. -/
def muN (r : Ty) (j : Nat) : Nat := (r.item j).items

/-- The number of recursive fields of the `c`-th constructor of the `j`-th type. -/
def muA (r : Ty) (j c : Nat) : Nat := ((r.item j).item c).items

/-- The type of the group that the `f`-th recursive field of the `c`-th constructor of the `j`-th
type holds. -/
def muS (r : Ty) (j c f : Nat) : Nat := (((r.item j).item c).item f).refTarget

/-- `f` applied `n` times to `a`. -/
def iter (f : List Bool → List Bool) : Nat → List Bool → List Bool
  | 0, a => a
  | n + 1, a => iter f n (f a)

/-- One round of finding the types of the group whose recursive fields `r` lists that have a value,
from those `h` marks: the `i`-th type, which has its base values, and each type with a constructor
whose recursive fields all hold types `h` marks. -/
def inhabitedStep (r : Ty) (i : Nat) (h : List Bool) : List Bool :=
  (List.range r.items).map fun j =>
    j == i || (List.range (r.muN j)).any fun c =>
      (List.range (r.muA j c)).all fun f => h.getD (r.muS j c f) false

/-- The types of the group found to have a value, after as many rounds as the group has types and
one more. -/
def inhabited (r : Ty) (i : Nat) : List Bool :=
  iter (r.inhabitedStep i) (r.items + 1) (List.replicate r.items false)

/-- One round of narrowing the types `p` marks to those with a constructor whose recursive fields all
hold types `h` marks and one of which holds a type `p` marks. -/
def growsStep (r : Ty) (h p : List Bool) : List Bool :=
  (List.range r.items).map fun j =>
    p.getD j false && (List.range (r.muN j)).any fun c =>
      (List.range (r.muA j c)).all (fun f => h.getD (r.muS j c f) false) &&
        (List.range (r.muA j c)).any fun f => p.getD (r.muS j c f) false

/-- Whether the `i`-th type of the group whose recursive fields `r` lists has values of every depth:
the types found to have a value, narrowed as many rounds as the group has types and one more, are
unchanged by one more round and hold the `i`-th type. Each type they hold then has a constructor that
holds one of them inside a value of its own (`Ty.mu_infinite`). `r` holds only numbers of types, never
a field's code, so Lean evaluates it alike for every type parameter. -/
def grows (r : Ty) (i : Nat) : Bool :=
  let h := r.inhabited i
  let p := iter (r.growsStep h) (r.items + 1) h
  p.getD i false && r.growsStep h p == p

/-- The type a code denotes, at the path `p` into it: `den t []` is the type `t` denotes, and a path
`k :: p` into a chain is the path `p` into its `k`-th item. A group's type `mu b g r i` denotes the
trees of `MuVal` whose data are the types the chains of the constructors' other fields denote, at the
paths `[j, c, 0]` into `g`, and whose positions are the types of the recursive fields' arguments, at
the paths `[j, c, 1, f]`; where the group does not grow (`Ty.grows`), it has only its base values. -/
@[reducible] def den : Ty → List Nat → Type
  | unit, _ => Unit
  | bool, [] => Bool
  | nat, [] => Nat
  | int, [] => Int
  | string, [] => String
  | list a, [] => List (den a [])
  | array a, [] => Array (den a [])
  | option a, [] => Option (den a [])
  | prod a b, [] => den a [] × den b []
  | prod a _, 0 :: p => den a p
  | prod _ b, (n + 1) :: p => den b (n :: p)
  | sum a b, [] => den a [] ⊕ den b []
  | decl _ _ r, [] => den r []
  | fin n, [] => Fin (n + 1)
  | atom k, [] => k.denote
  | arrow a b, [] => den a [] → den b []
  | ref _, _ => Unit
  | mu b g r i, [] => MuVal (den b []) i (fun j => bif r.grows i then r.muN j else 0)
      (fun j c => den g [j, c, 0]) r.muA (fun j c f => den g [j, c, 1, f]) r.muS i
  | _, _ :: _ => Unit

/-- The type a code denotes: the type it stands for when it is built only from those `Ty` builds in,
and otherwise one isomorphic to it. It is reducible, so that Lean's simplifier sees the type through
the code. -/
@[reducible] def denote (t : Ty) : Type := t.den []

/-- The empty value of a type: the value a subject that returns nothing returns. -/
def empty : (t : Ty) → t.denote
  | unit => ()
  | bool => false
  | nat => (0 : Nat)
  | int => (0 : Int)
  | string => ""
  | list a => ([] : List a.denote)
  | array a => (#[] : Array a.denote)
  | option a => (none : Option a.denote)
  | prod a b => ((a.empty, b.empty) : a.denote × b.denote)
  | sum a b => (.inl a.empty : a.denote ⊕ b.denote)
  | decl _ _ r => r.empty
  | fin _ => (0 : Fin _)
  | atom k => k.empty
  | arrow _ b => fun _ => b.empty
  | ref _ => ()
  | mu b _ _ _ => .base b.empty

/-- The values the degenerate class takes constant subjects at one by one, as a list: every value
`Small` admits where `count` is at most `listBound` (`mem_part_iff`). A machine type or a function
type is above the bound, and lists only its empty value here. -/
def part : (t : Ty) → List t.denote
  | unit => [()]
  | bool => [false, true]
  | nat => [(0 : Nat)]
  | int => [(0 : Int)]
  | string => [""]
  | list a => [([] : List a.denote)]
  | array a => [(#[] : Array a.denote)]
  | option a => (none : Option a.denote) :: a.part.map some
  | prod a b => a.part.flatMap fun x => b.part.map fun y => ((x, y) : a.denote × b.denote)
  | sum a b => a.part.map (Sum.inl (β := b.denote)) ++ b.part.map (Sum.inr (α := a.denote))
  | decl _ _ r => r.part
  | fin n => List.finRange (n + 1)
  | atom k => [k.empty]
  | arrow _ b => [fun _ => b.empty]
  | ref _ => [()]
  | mu b _ _ _ => b.part.map .base

/-- Whether the type has exactly one value: the unit type, `Fin 1` and a bit vector of width zero; a
pair of two such types; a declared type whose representation is one; and a function to such a type. -/
def unique : Ty → Bool
  | unit => true
  | prod a b => a.unique && b.unique
  | decl _ _ r => r.unique
  | fin n => n == 0
  | atom k => k.unique
  | arrow _ b => b.unique
  | ref _ => true
  | mu b _ r i => !r.grows i && b.unique
  | _ => false

/-- Whether the type has finitely many values: the unit type, `Bool`, `Fin (n + 1)` and a machine
type do, numbers, strings, lists and arrays do not, an option, a pair or a sum does exactly when each
of its components does, and a function type exactly when its result has one value, or its argument
and its result have finitely many. -/
def finite : Ty → Bool
  | unit => true
  | bool => true
  | nat => false
  | int => false
  | string => false
  | list _ => false
  | array _ => false
  | option a => a.finite
  | prod a b => a.finite && b.finite
  | sum a b => a.finite && b.finite
  | decl _ _ r => r.finite
  | fin _ => true
  | atom _ => true
  | arrow a b => b.unique || (a.finite && b.finite)
  | ref _ => true
  | mu b _ r i => !r.grows i && b.finite

/-- The rule that fixes which values of a type the degenerate class takes constant subjects at,
written apart from `part`: a number, a string, a list or an array only at its empty value; the unit
type, `Bool`, `Fin (n + 1)` and a machine type at every value; an option at `none` and at each value
its component's rule admits under `some`; a pair at each pair of values its sides' rules admit; a
sum at each value either side's rule admits; a declared type as its representation; and a function
type at every function where it has finitely many, and otherwise at the constant function at each
value its result's rule admits. -/
def Small : (t : Ty) → t.denote → Prop
  | unit, _ => True
  | bool, _ => True
  | nat, x => x = (0 : Nat)
  | int, x => x = (0 : Int)
  | string, x => x = ""
  | list a, x => x = ([] : List a.denote)
  | array a, x => x = (#[] : Array a.denote)
  | option a, x => x = (none : Option a.denote) ∨ ∃ y, x = some y ∧ a.Small y
  | prod a b, x => a.Small (x : a.denote × b.denote).1 ∧ b.Small (x : a.denote × b.denote).2
  | sum a b, x => (∃ y, x = (.inl y : a.denote ⊕ b.denote) ∧ a.Small y) ∨
      ∃ y, x = (.inr y : a.denote ⊕ b.denote) ∧ b.Small y
  | decl _ _ r, x => r.Small x
  | fin _, _ => True
  | atom _, _ => True
  | arrow a b, f => (arrow a b).finite = true ∨ ∃ v, b.Small v ∧ f = fun _ => v
  | ref _, _ => True
  | mu b _ _ _, x => ∃ y, x = .base y ∧ b.Small y

/-- The largest number of constant subjects the class lists one by one, for one type. `UInt8`, the
smallest machine type the library's plan names too large to enumerate, has one value more, and a
type with no more values than this keeps the class it had when every finite type's values were
listed. -/
def listBound : Nat := 255

/-- The number of constants the class would list one by one: the length of `part`, and above
`listBound` for a machine type or a function type, which `part` does not list. -/
def count : Ty → Nat
  | unit => 1
  | bool => 2
  | nat => 1
  | int => 1
  | string => 1
  | list _ => 1
  | array _ => 1
  | option a => 1 + a.count
  | prod a b => a.count * b.count
  | sum a b => a.count + b.count
  | decl _ _ r => r.count
  | fin n => n + 1
  | atom _ => listBound + 1
  | arrow _ _ => listBound + 1
  | ref _ => 1
  | mu b _ _ _ => b.count

/-! ## The values of a recursive group -/

/-- A value of the type a code denotes at a path: the empty value of the code the path reaches. -/
def denEmpty : (t : Ty) → (p : List Nat) → t.den p
  | unit, _ => ()
  | prod a _, 0 :: p => denEmpty a p
  | prod _ b, (n + 1) :: p => denEmpty b (n :: p)
  | ref _, _ => ()
  | t, [] => t.empty
  | bool, _ :: _ | nat, _ :: _ | int, _ :: _ | string, _ :: _ | list _, _ :: _ | array _, _ :: _
  | option _, _ :: _ | sum _ _, _ :: _ | decl _ _ _, _ :: _ | fin _, _ :: _ | atom _, _ :: _
  | arrow _ _, _ :: _ | mu _ _ _ _, _ :: _ => ()

/-- The trees of the group with the base `b`, data and arguments `g` and recursive fields `r`, whose
types have the constructors `N` counts. -/
@[reducible] def muTy (b g r : Ty) (i : Nat) (N : Nat → Nat) : Nat → Type :=
  MuVal (b.den []) i N (fun j c => g.den [j, c, 0]) r.muA (fun j c f => g.den [j, c, 1, f]) r.muS

theorem getD_range_map (n j : Nat) (F : Nat → Bool) :
    ((List.range n).map F).getD j false = (decide (j < n) && F j) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : j < n
  · simp [h]
  · simp [h]

/-- Where the group does not grow, its `i`-th type has only its base values. -/
theorem eq_base_of_not_grows {b g r : Ty} {i : Nat} (h : r.grows i = false) (x : (mu b g r i).denote) :
    ∃ y, x = .base y := by
  cases x with
  | base y => exact ⟨y, rfl⟩
  | node c _ _ => exact absurd c.2 (by simp [h])

/-- A round of `inhabitedStep` marks only types with a value, given that `h` does. -/
theorem inhabitedStep_sound {b g r : Ty} {i : Nat} {h : List Bool}
    (hh : ∀ j, h.getD j false = true → Nonempty (muTy b g r i r.muN j)) (j : Nat)
    (hj : (r.inhabitedStep i h).getD j false = true) : Nonempty (muTy b g r i r.muN j) := by
  simp only [inhabitedStep, getD_range_map, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    beq_iff_eq, List.any_eq_true, List.mem_range, List.all_eq_true] at hj
  rcases hj.2 with rfl | ⟨c, hc, hall⟩
  · exact ⟨.base b.empty⟩
  · exact ⟨.node ⟨c, hc⟩ (g.denEmpty [j, c, 0]) fun f _ => Classical.choice (hh _ (hall f f.2))⟩

theorem iter_inhabitedStep_sound {b g r : Ty} {i : Nat} : (k : Nat) → (h : List Bool) →
    (∀ j, h.getD j false = true → Nonempty (muTy b g r i r.muN j)) → ∀ j,
      (iter (r.inhabitedStep i) k h).getD j false = true → Nonempty (muTy b g r i r.muN j)
  | 0, _, hh => hh
  | k + 1, _, hh => iter_inhabitedStep_sound k _ (inhabitedStep_sound hh)

/-- Each type `inhabited` marks has a value. -/
theorem inhabited_sound {b g r : Ty} {i j : Nat} (hj : (r.inhabited i).getD j false = true) :
    Nonempty (muTy b g r i r.muN j) :=
  iter_inhabitedStep_sound _ _ (fun j h => by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate] at h
    split at h <;> simp at h) j hj

/-- A sequence of values, the `m`-th of measure at least `m`, gives an injection from `Nat`. -/
theorem exists_injective_of_le {α : Type} (d : α → Nat) (v : Nat → α) (hv : ∀ m, m ≤ d (v m)) :
    ∃ f : Nat → α, Function.Injective f := by
  let bound : Nat → Nat := fun n => Nat.rec 0 (fun _ k => d (v k) + 1) n
  have hlt : ∀ m n, m < n → d (v (bound m)) < d (v (bound n)) := by
    intro m n hmn
    induction n with
    | zero => exact absurd hmn (Nat.not_lt_zero _)
    | succ n ih =>
      have hs : d (v (bound n)) < d (v (bound (n + 1))) := hv (d (v (bound n)) + 1)
      rcases Nat.lt_succ_iff_lt_or_eq.mp hmn with h | rfl
      · exact Nat.lt_trans (ih h) hs
      · exact hs
  refine ⟨fun n => v (bound n), fun m n e => ?_⟩
  rcases Nat.lt_trichotomy m n with h | h | h
  · exact absurd (congrArg d e) (Nat.ne_of_lt (hlt m n h))
  · exact h
  · exact absurd (congrArg d e) (Nat.ne_of_gt (hlt n m h))

/-- Where the group grows, its `i`-th type has infinitely many values: each type the narrowing in
`grows` keeps has a constructor with a recursive field that holds such a type, so a value of any
depth along those fields is built, and the depths give an injection from `Nat`. -/
theorem muTy_infinite {b g r : Ty} {i : Nat} (hg : r.grows i = true) :
    ∃ f : Nat → muTy b g r i r.muN i, Function.Injective f := by
  classical
  simp only [grows, Bool.and_eq_true, beq_iff_eq] at hg
  obtain ⟨hpi, hfix⟩ := hg
  generalize hp : iter (r.growsStep (r.inhabited i)) (r.items + 1) (r.inhabited i) = p at hpi hfix
  -- Each type `p` marks has a constructor whose recursive fields hold types with a value, one of
  -- them a type `p` marks.
  have hstep : ∀ j, p.getD j false = true → ∃ c, ∃ hc : c < r.muN j, ∃ f, ∃ hf : f < r.muA j c,
      p.getD (r.muS j c f) false = true ∧
        ∀ f' : Fin (r.muA j c), Nonempty (muTy b g r i r.muN (r.muS j c f')) := by
    intro j hj
    rw [← hfix] at hj
    simp only [growsStep, getD_range_map, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
      List.mem_range, List.all_eq_true] at hj
    obtain ⟨_, _, c, hc, hall, f, hf, hpf⟩ := hj
    exact ⟨c, hc, f, hf, hpf, fun f' => inhabited_sound (hall f' f'.2)⟩
  -- The chosen constructor and field of each type `p` marks, as numbers.
  let C : Nat → Nat := fun j => if hj : p.getD j false = true then (hstep j hj).choose else 0
  let F : Nat → Nat := fun j =>
    if hj : p.getD j false = true then (hstep j hj).choose_spec.choose_spec.choose else 0
  have hC : ∀ j (hj : p.getD j false = true), C j < r.muN j ∧ F j < r.muA j (C j) ∧
      p.getD (r.muS j (C j) (F j)) false = true ∧
        ∀ f' : Fin (r.muA j (C j)), Nonempty (muTy b g r i r.muN (r.muS j (C j) f')) := by
    intro j hj
    have eC : C j = (hstep j hj).choose := by simp only [C, hj, ↓reduceDIte]
    have eF : F j = (hstep j hj).choose_spec.choose_spec.choose := by
      simp only [F, hj, ↓reduceDIte]
    rw [eC, eF]
    exact ⟨(hstep j hj).choose_spec.choose, (hstep j hj).choose_spec.choose_spec.choose_spec.choose,
      (hstep j hj).choose_spec.choose_spec.choose_spec.choose_spec.1,
      (hstep j hj).choose_spec.choose_spec.choose_spec.choose_spec.2⟩
  -- The depth of a value along the chosen fields.
  let depth : {j : Nat} → muTy b g r i r.muN j → Nat := fun v =>
    MuVal.rec (motive := fun _ _ => Nat) (fun _ => 0)
      (fun {j} c _ _ ih => if h : c.val = C j ∧ F j < r.muA j c then
        1 + ih ⟨F j, h.2⟩ (g.denEmpty [j, c, 1, F j]) else 0) v
  let tr : {j j' : Nat} → j = j' → muTy b g r i r.muN j → muTy b g r i r.muN j' := fun e v => e ▸ v
  have depth_cast : ∀ {j j' : Nat} (e : j = j') (v : muTy b g r i r.muN j), depth (tr e v) = depth v := by
    intro j j' e v
    subst e
    rfl
  -- A value of each type `p` marks of depth at least `m`.
  let chain : (m : Nat) → (j : Nat) → p.getD j false = true → muTy b g r i r.muN j :=
    fun m => Nat.rec (fun j hj => .node ⟨C j, (hC j hj).1⟩ (g.denEmpty [j, C j, 0])
        fun f _ => Classical.choice ((hC j hj).2.2.2 f))
      (fun _ ih j hj => .node ⟨C j, (hC j hj).1⟩ (g.denEmpty [j, C j, 0]) fun f _ =>
        if hf : f.val = F j then
          tr (congrArg (r.muS j (C j)) hf).symm (ih _ (hC j hj).2.2.1)
        else Classical.choice ((hC j hj).2.2.2 f)) m
  have hdepth : ∀ m j (hj : p.getD j false = true), m ≤ depth (chain m j hj) := by
    intro m
    induction m with
    | zero => intro _ _; exact Nat.zero_le _
    | succ m ih =>
      intro j hj
      have h2 := (hC j hj).2.1
      show m + 1 ≤ (if h : C j = C j ∧ F j < r.muA j (C j) then 1 + depth (
        (if hf : F j = F j then tr (congrArg (r.muS j (C j)) hf).symm (chain m _ (hC j hj).2.2.1)
          else Classical.choice ((hC j hj).2.2.2 ⟨F j, h.2⟩))) else 0)
      rw [dite_eq_left ⟨rfl, h2⟩, dite_eq_left rfl]
      simp only [depth_cast]
      have := ih _ (hC j hj).2.2.1
      omega
  exact exists_injective_of_le depth (fun m => chain m i hpi) fun m => hdepth m i hpi

theorem muTy_infinite_of_eq {b g r : Ty} {i : Nat} {N : Nat → Nat} (e : N = r.muN)
    (h : ∃ f : Nat → muTy b g r i r.muN i, Function.Injective f) :
    ∃ f : Nat → muTy b g r i N i, Function.Injective f := by
  subst e
  exact h

/-- Where the group grows, its `i`-th type has infinitely many values (`muTy_infinite`). -/
theorem mu_infinite {b g r : Ty} {i : Nat} (h : r.grows i = true) :
    ∃ f : Nat → (mu b g r i).denote, Function.Injective f :=
  muTy_infinite_of_eq (funext fun j => by simp [h]) (muTy_infinite h)

theorem count_pos : (t : Ty) → 0 < t.count
  | unit | bool | nat | int | string | list _ | array _ | fin _ | atom _ | arrow _ _ | ref _ => by
      simp [count, listBound]
  | mu b _ _ _ => count_pos b
  | option a => by simp [count]; omega
  | prod a b => Nat.mul_pos (count_pos a) (count_pos b)
  | sum a b => Nat.add_pos_left (count_pos a) _
  | decl _ _ r => count_pos r

/-- Where `count` is at most `listBound`, `part` lists exactly the values the rule `Small` admits. -/
theorem mem_part_iff : (t : Ty) → t.count ≤ listBound → (x : t.denote) → (x ∈ t.part ↔ t.Small x)
  | unit, _, x => by cases x; simp [part, Small]
  | bool, _, x => by cases x <;> simp [part, Small]
  | nat, _, x => by simp [part, Small]
  | int, _, x => by simp [part, Small]
  | string, _, x => by simp [part, Small]
  | list _, _, x => by simp [part, Small]
  | array _, _, x => by simp [part, Small]
  | option a, h, x => by
      have ha : a.count ≤ listBound := by simp only [count] at h; omega
      cases x with
      | none => simp [part, Small]
      | some y => simp [part, Small, mem_part_iff a ha y]
  | prod a b, h, x => by
      simp only [count] at h
      have ha : a.count ≤ listBound :=
        Nat.le_trans (Nat.le_mul_of_pos_right _ (count_pos b)) h
      have hb : b.count ≤ listBound :=
        Nat.le_trans (Nat.le_mul_of_pos_left _ (count_pos a)) h
      obtain ⟨y, z⟩ := x
      simp [part, Small, mem_part_iff a ha y, mem_part_iff b hb z]
  | sum a b, h, x => by
      simp only [count] at h
      have ha : a.count ≤ listBound := by omega
      have hb : b.count ≤ listBound := by omega
      cases x with
      | inl y => simp [part, Small, mem_part_iff a ha y]
      | inr z => simp [part, Small, mem_part_iff b hb z]
  | decl _ _ r, h, x => mem_part_iff r h x
  | fin _, _, x => by simp [part, Small]
  | atom _, h, _ => absurd h (Nat.not_succ_le_self _)
  | arrow _ _, h, _ => absurd h (Nat.not_succ_le_self _)
  | ref _, _, x => by cases x; simp [part, Small]
  | mu b _ _ _, h, x => by
      simp only [part, Small, List.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, rfl, (mem_part_iff b h y).mp hy⟩
      · rintro ⟨y, rfl, hy⟩
        exact ⟨y, (mem_part_iff b h y).mpr hy, rfl⟩

theorem length_flatMap_map {α β γ : Type} (l : List α) (m : List β) (g : α → β → γ) :
    (l.flatMap fun x => m.map (g x)).length = l.length * m.length := by
  induction l with
  | nil => simp
  | cons x l ih => simp [List.flatMap_cons, ih, Nat.succ_mul, Nat.add_comm]

/-- `part` is no longer than `count`. -/
theorem length_part_le : (t : Ty) → t.part.length ≤ t.count
  | unit | bool | nat | int | string | list _ | array _ => by simp [part, count]
  | option a => by
      have := length_part_le a
      simp only [part, count, List.length_cons, List.length_map]
      omega
  | prod a b => by
      simp only [part, count, length_flatMap_map]
      exact Nat.mul_le_mul (length_part_le a) (length_part_le b)
  | sum a b => by
      simp only [part, count, List.length_append, List.length_map]
      exact Nat.add_le_add (length_part_le a) (length_part_le b)
  | decl _ _ r => length_part_le r
  | fin n => by simp [part, count]
  | atom _ | arrow _ _ => by simp [part, count, listBound]
  | ref _ => by simp [part, count]
  | mu b _ _ _ => by simpa [part, count] using length_part_le b

/-- The rule admits the empty value of every type. -/
theorem small_empty : (t : Ty) → t.Small t.empty
  | unit => trivial
  | bool => trivial
  | nat => rfl
  | int => rfl
  | string => rfl
  | list _ => rfl
  | array _ => rfl
  | option _ => .inl rfl
  | prod a b => ⟨small_empty a, small_empty b⟩
  | sum a _ => .inl ⟨_, rfl, small_empty a⟩
  | decl _ _ r => small_empty r
  | fin _ => trivial
  | atom _ => trivial
  | arrow _ b => .inr ⟨_, small_empty b, rfl⟩
  | ref _ => trivial
  | mu b _ _ _ => ⟨_, rfl, small_empty b⟩

/-- The empty value of every type is in its part. -/
theorem empty_mem_part : (t : Ty) → t.empty ∈ t.part
  | unit | bool | nat | int | string | list _ | array _ | atom _ | arrow _ _ => by
      simp [part, empty]
  | option a => by simp [part, empty]
  | prod a b => by
      simp only [part, empty, List.mem_flatMap, List.mem_map]
      exact ⟨_, empty_mem_part a, _, empty_mem_part b, rfl⟩
  | sum a _ => by
      simp only [part, empty, List.mem_append, List.mem_map]
      exact .inl ⟨_, empty_mem_part a, rfl⟩
  | decl _ _ r => empty_mem_part r
  | fin n => by simp [part]
  | ref _ => by simp [part, empty]
  | mu b _ _ _ => List.mem_map.mpr ⟨_, empty_mem_part b, rfl⟩

/-- No type's part is empty. -/
theorem part_ne_nil (t : Ty) : t.part ≠ [] := List.ne_nil_of_mem (empty_mem_part t)

/-- The rule admits every value of a type with finitely many values. -/
theorem small_of_finite : (t : Ty) → t.finite = true → ∀ x, t.Small x
  | unit, _, _ => trivial
  | bool, _, _ => trivial
  | option a, h, x => by
      cases x with
      | none => exact .inl rfl
      | some y => exact .inr ⟨y, rfl, small_of_finite a h y⟩
  | prod a b, h, x => by
      simp only [finite, Bool.and_eq_true] at h
      exact ⟨small_of_finite a h.1 _, small_of_finite b h.2 _⟩
  | sum a b, h, x => by
      simp only [finite, Bool.and_eq_true] at h
      cases x with
      | inl y => exact .inl ⟨y, rfl, small_of_finite a h.1 y⟩
      | inr z => exact .inr ⟨z, rfl, small_of_finite b h.2 z⟩
  | decl _ _ r, h, x => small_of_finite r h x
  | fin _, _, _ => trivial
  | atom _, _, _ => trivial
  | arrow _ _, h, _ => .inl h
  | ref _, _, _ => trivial
  | mu b g r i, h, x => by
      simp [finite] at h
      obtain ⟨y, rfl⟩ := eq_base_of_not_grows h.1 x
      exact ⟨y, rfl, small_of_finite b h.2 y⟩

/-- A type with finitely many values, no more than the class lists, has every one in its part. -/
theorem mem_part_of_finite {t : Ty} (hc : t.count ≤ listBound) (h : t.finite = true)
    (x : t.denote) : x ∈ t.part :=
  (mem_part_iff t hc x).mpr (small_of_finite t h x)

/-- A machine type other than a bit vector of width zero has two values. -/
theorem _root_.LeanIntent.Atom.exists_ne : (k : Atom) → k.unique = false → ∃ x y : k.denote, x ≠ y
  | .char, _ => ⟨Char.ofNat 0, Char.ofNat 1, by decide⟩
  | .uint8, _ => ⟨(0 : UInt8), (1 : UInt8), UInt8.zero_ne_one⟩
  | .uint16, _ => ⟨(0 : UInt16), (1 : UInt16), UInt16.zero_ne_one⟩
  | .uint32, _ => ⟨(0 : UInt32), (1 : UInt32), UInt32.zero_ne_one⟩
  | .uint64, _ => ⟨(0 : UInt64), (1 : UInt64), UInt64.zero_ne_one⟩
  | .usize, _ => ⟨(0 : USize), (1 : USize), USize.zero_ne_one⟩
  | .int8, _ => ⟨(0 : Int8), (1 : Int8), Int8.zero_ne_one⟩
  | .int16, _ => ⟨(0 : Int16), (1 : Int16), Int16.zero_ne_one⟩
  | .int32, _ => ⟨(0 : Int32), (1 : Int32), Int32.zero_ne_one⟩
  | .int64, _ => ⟨(0 : Int64), (1 : Int64), Int64.zero_ne_one⟩
  | .isize, _ => ⟨(0 : ISize), (1 : ISize), ISize.zero_ne_one⟩
  | .float, _ => ⟨Float.ofBits 0, Float.ofBits 1, by decide⟩
  | .float32, _ => ⟨Float32.ofBits 0, Float32.ofBits 1, by decide⟩
  | .bitVec 0, h => by simp [Atom.unique] at h
  | .bitVec (w + 1), _ => ⟨(0 : BitVec (w + 1)), (1 : BitVec (w + 1)), fun e => by
      have := congrArg BitVec.toNat e
      simp at this⟩

/-- A type that does not have exactly one value has two. -/
theorem exists_ne : (t : Ty) → t.unique = false → ∃ x y : t.denote, x ≠ y
  | bool, _ => ⟨false, true, by decide⟩
  | nat, _ => ⟨(0 : Nat), (1 : Nat), by decide⟩
  | int, _ => ⟨(0 : Int), (1 : Int), by decide⟩
  | string, _ => ⟨"", "a", by decide⟩
  | list a, _ => ⟨([] : List a.denote), [a.empty], by simp⟩
  | array a, _ => ⟨(#[] : Array a.denote), #[a.empty], by simp⟩
  | option a, _ => ⟨(none : Option a.denote), some a.empty, by simp⟩
  | prod a b, h => by
      simp only [unique, Bool.and_eq_false_iff] at h
      rcases h with h | h
      · obtain ⟨x, y, hxy⟩ := exists_ne a h
        exact ⟨((x, b.empty) : a.denote × b.denote), ((y, b.empty) : a.denote × b.denote),
          fun e => hxy (congrArg Prod.fst e)⟩
      · obtain ⟨x, y, hxy⟩ := exists_ne b h
        exact ⟨((a.empty, x) : a.denote × b.denote), ((a.empty, y) : a.denote × b.denote),
          fun e => hxy (congrArg Prod.snd e)⟩
  | sum a b, _ => ⟨(.inl a.empty : a.denote ⊕ b.denote), .inr b.empty, by simp⟩
  | decl _ _ r, h => exists_ne r h
  | fin 0, h => by simp [unique] at h
  | fin (n + 1), _ => ⟨(0 : Fin (n + 2)), (Fin.last (n + 1) : Fin (n + 2)), fun e => by
      have := congrArg Fin.val e
      simp at this⟩
  | atom k, h => k.exists_ne h
  | arrow a b, h => by
      obtain ⟨x, y, hxy⟩ := exists_ne b h
      exact ⟨fun _ => x, fun _ => y, fun e => hxy (congrFun e a.empty)⟩
  | mu b g r i, h => by
      cases hg : r.grows i
      · simp [unique, hg] at h
        obtain ⟨x, y, hxy⟩ := exists_ne b h
        exact ⟨.base x, .base y, fun e => hxy (MuVal.base.inj e)⟩
      · obtain ⟨f, hf⟩ := mu_infinite (b := b) hg
        exact ⟨f 0, f 1, fun e => absurd (hf e) (by decide)⟩

/-- A type for which `finite` fails has infinitely many values: an injection from `Nat`. -/
theorem infinite : (t : Ty) → t.finite = false → ∃ f : Nat → t.denote, Function.Injective f
  | nat, _ => ⟨fun n => (n : Nat), fun _ _ h => h⟩
  | int, _ => ⟨fun n => (Int.ofNat n : Int), fun _ _ h => Int.ofNat.inj h⟩
  | string, _ => ⟨fun n => ("".pushn 'a' n : String), fun m n h => by
      have := congrArg String.length h
      simpa [String.length_pushn] using this⟩
  | list a, _ => ⟨fun n => (List.replicate n a.empty : List a.denote), fun m n h => by
      have := congrArg List.length h
      simpa using this⟩
  | array a, _ => ⟨fun n => (Array.replicate n a.empty : Array a.denote), fun m n h => by
      have := congrArg Array.size h
      simpa using this⟩
  | option a, h => by
      obtain ⟨f, hf⟩ := infinite a h
      exact ⟨fun n => (some (f n) : Option a.denote), fun m n e => hf (Option.some.inj e)⟩
  | prod a b, h => by
      simp only [finite, Bool.and_eq_false_iff] at h
      rcases h with h | h
      · obtain ⟨f, hf⟩ := infinite a h
        exact ⟨fun n => ((f n, b.empty) : a.denote × b.denote),
          fun m n e => hf (congrArg Prod.fst e)⟩
      · obtain ⟨f, hf⟩ := infinite b h
        exact ⟨fun n => ((a.empty, f n) : a.denote × b.denote),
          fun m n e => hf (congrArg Prod.snd e)⟩
  | sum a b, h => by
      simp only [finite, Bool.and_eq_false_iff] at h
      rcases h with h | h
      · obtain ⟨f, hf⟩ := infinite a h
        exact ⟨fun n => (.inl (f n) : a.denote ⊕ b.denote), fun m n e => hf (Sum.inl.inj e)⟩
      · obtain ⟨f, hf⟩ := infinite b h
        exact ⟨fun n => (.inr (f n) : a.denote ⊕ b.denote), fun m n e => hf (Sum.inr.inj e)⟩
  | decl _ _ r, h => infinite r h
  | arrow a b, h => by
      simp only [finite, Bool.or_eq_false_iff, Bool.and_eq_false_iff] at h
      obtain ⟨hu, h⟩ := h
      rcases h with h | h
      · obtain ⟨g, hg⟩ := infinite a h
        obtain ⟨x, y, hxy⟩ := exists_ne b hu
        classical
        refine ⟨fun n z => if z = g n then y else x, fun m n e => ?_⟩
        have := congrFun e (g n)
        by_cases hmn : g n = g m
        · exact (hg hmn).symm
        · simp [hmn] at this
          exact absurd this hxy
      · obtain ⟨g, hg⟩ := infinite b h
        exact ⟨fun n _ => g n, fun m n e => hg (congrFun e a.empty)⟩
  | mu b g r i, h => by
      cases hg : r.grows i
      · simp [finite, hg] at h
        obtain ⟨f, hf⟩ := infinite b h
        exact ⟨fun n => .base (f n), fun m n e => hf (MuVal.base.inj e)⟩
      · exact mu_infinite hg

/-- A type with exactly one value has only its empty value. -/
theorem eq_empty_of_unique : (t : Ty) → t.unique = true → (x : t.denote) → x = t.empty
  | unit, _, _ => rfl
  | prod a b, h, x => by
      simp only [unique, Bool.and_eq_true] at h
      exact Prod.ext (eq_empty_of_unique a h.1 _) (eq_empty_of_unique b h.2 _)
  | decl _ _ r, h, x => eq_empty_of_unique r h x
  | fin 0, _, x => Subsingleton.elim (α := Fin 1) x _
  | fin (_ + 1), h, _ => by simp [unique] at h
  | atom (.bitVec 0), _, x => BitVec.eq_nil x
  | atom (.bitVec (_ + 1)), h, _ => by simp [unique, Atom.unique] at h
  | arrow _ b, h, f => funext fun x => eq_empty_of_unique b h (f x)
  | ref _, _, _ => rfl
  | mu b g r i, h, x => by
      simp [unique] at h
      obtain ⟨y, rfl⟩ := eq_base_of_not_grows h.1 x
      exact congrArg MuVal.base (eq_empty_of_unique b h.2 y)

/-- A type all of whose values `f` carries injectively into a list has a list of its values. -/
theorem exists_list_of_injective {α β : Type} (f : α → β) (hf : Function.Injective f)
    {l : List β} (hl : ∀ y, y ∈ l) : ∃ l' : List α, ∀ x, x ∈ l' := by
  classical
  refine ⟨l.filterMap fun y => if h : ∃ x, f x = y then some h.choose else none, fun x => ?_⟩
  refine List.mem_filterMap.mpr ⟨f x, hl _, ?_⟩
  have h : ∃ z, f z = f x := ⟨x, rfl⟩
  simp only [h, ↓reduceDIte]
  rw [hf h.choose_spec]

/-- Every function on a list of arguments, to values of a list, agrees on it with one of a list. -/
theorem exists_list_agreeing {α β : Type} (d : β) (bs : List β) (hb : ∀ y, y ∈ bs) (as : List α) :
    ∃ l : List (α → β), ∀ f : α → β, ∃ g ∈ l, ∀ x ∈ as, g x = f x := by
  classical
  induction as with
  | nil => exact ⟨[fun _ => d], fun _ => ⟨_, List.mem_singleton.mpr rfl, by simp⟩⟩
  | cons a as ih =>
    obtain ⟨l, hl⟩ := ih
    refine ⟨bs.flatMap fun v => l.map fun g z => if z = a then v else g z, fun f => ?_⟩
    obtain ⟨g, hg, hfg⟩ := hl f
    refine ⟨fun z => if z = a then f a else g z, ?_, fun x hx => ?_⟩
    · exact List.mem_flatMap.mpr ⟨f a, hb _, List.mem_map.mpr ⟨g, hg, rfl⟩⟩
    · by_cases hxa : x = a
      · simp [hxa]
      · simpa [hxa] using hfg x ((List.mem_cons.mp hx).resolve_left hxa)

/-- Every machine type has finitely many values. -/
theorem _root_.LeanIntent.Atom.exists_list : (k : Atom) → ∃ l : List k.denote, ∀ x, x ∈ l
  | .uint8 => exists_list_of_injective UInt8.toFin (fun _ _ e => UInt8.toFin_inj.mp e)
      (List.mem_finRange ·)
  | .uint16 => exists_list_of_injective UInt16.toFin (fun _ _ e => UInt16.toFin_inj.mp e)
      (List.mem_finRange ·)
  | .uint32 => exists_list_of_injective UInt32.toFin (fun _ _ e => UInt32.toFin_inj.mp e)
      (List.mem_finRange ·)
  | .uint64 => exists_list_of_injective UInt64.toFin (fun _ _ e => UInt64.toFin_inj.mp e)
      (List.mem_finRange ·)
  | .usize => exists_list_of_injective USize.toFin (fun _ _ e => USize.toFin_inj.mp e)
      (List.mem_finRange ·)
  | .bitVec _ => exists_list_of_injective BitVec.toFin (fun _ _ e => BitVec.toFin_inj.mp e)
      (List.mem_finRange ·)
  | .char => exists_list_of_injective (fun c => c.val.toFin)
      (fun _ _ e => Char.ext (UInt32.toFin_inj.mp e)) (List.mem_finRange ·)
  | .int8 => exists_list_of_injective (fun x => x.toUInt8.toFin)
      (fun _ _ e => congrArg Int8.ofUInt8 (UInt8.toFin_inj.mp e)) (List.mem_finRange ·)
  | .int16 => exists_list_of_injective (fun x => x.toUInt16.toFin)
      (fun _ _ e => congrArg Int16.ofUInt16 (UInt16.toFin_inj.mp e)) (List.mem_finRange ·)
  | .int32 => exists_list_of_injective (fun x => x.toUInt32.toFin)
      (fun _ _ e => congrArg Int32.ofUInt32 (UInt32.toFin_inj.mp e)) (List.mem_finRange ·)
  | .int64 => exists_list_of_injective (fun x => x.toUInt64.toFin)
      (fun _ _ e => congrArg Int64.ofUInt64 (UInt64.toFin_inj.mp e)) (List.mem_finRange ·)
  | .isize => exists_list_of_injective (fun x => x.toUSize.toFin)
      (fun _ _ e => congrArg ISize.ofUSize (USize.toFin_inj.mp e)) (List.mem_finRange ·)
  | .float => exists_list_of_injective (fun x => x.toModel.toBits.toFin)
      (fun ⟨⟨_, _⟩⟩ ⟨⟨_, _⟩⟩ e => by cases UInt64.toFin_inj.mp e; rfl) (List.mem_finRange ·)
  | .float32 => exists_list_of_injective (fun x => x.toModel.toBits.toFin)
      (fun ⟨⟨_, _⟩⟩ ⟨⟨_, _⟩⟩ e => by cases UInt32.toFin_inj.mp e; rfl) (List.mem_finRange ·)

/-- A type for which `finite` holds has finitely many values: a list holds every one. -/
theorem exists_list_of_finite : (t : Ty) → t.finite = true → ∃ l : List t.denote, ∀ x, x ∈ l
  | unit, _ => ⟨[()], fun _ => List.mem_singleton.mpr rfl⟩
  | bool, _ => ⟨[false, true], fun x => by cases x <;> simp⟩
  | option a, h => by
      obtain ⟨l, hl⟩ := exists_list_of_finite a h
      refine ⟨(none : Option a.denote) :: l.map some, fun x => ?_⟩
      cases x with
      | none => exact List.mem_cons_self
      | some y => exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨y, hl y, rfl⟩)
  | prod a b, h => by
      simp only [finite, Bool.and_eq_true] at h
      obtain ⟨l, hl⟩ := exists_list_of_finite a h.1
      obtain ⟨m, hm⟩ := exists_list_of_finite b h.2
      exact ⟨l.flatMap fun x => m.map fun y => ((x, y) : a.denote × b.denote), fun x =>
        List.mem_flatMap.mpr ⟨x.1, hl _, List.mem_map.mpr ⟨x.2, hm _, rfl⟩⟩⟩
  | sum a b, h => by
      simp only [finite, Bool.and_eq_true] at h
      obtain ⟨l, hl⟩ := exists_list_of_finite a h.1
      obtain ⟨m, hm⟩ := exists_list_of_finite b h.2
      refine ⟨l.map (Sum.inl (β := b.denote)) ++ m.map (Sum.inr (α := a.denote)), fun x => ?_⟩
      cases x with
      | inl y => exact List.mem_append.mpr (.inl (List.mem_map.mpr ⟨y, hl y, rfl⟩))
      | inr z => exact List.mem_append.mpr (.inr (List.mem_map.mpr ⟨z, hm z, rfl⟩))
  | decl _ _ r, h => exists_list_of_finite r h
  | fin _, _ => ⟨List.finRange _, List.mem_finRange⟩
  | ref _, _ => ⟨[()], fun _ => List.mem_singleton.mpr rfl⟩
  | mu b g r i, h => by
      simp [finite] at h
      obtain ⟨l, hl⟩ := exists_list_of_finite b h.2
      refine ⟨l.map .base, fun x => ?_⟩
      obtain ⟨y, rfl⟩ := eq_base_of_not_grows h.1 x
      exact List.mem_map.mpr ⟨y, hl y, rfl⟩
  | atom k, _ => k.exists_list
  | arrow a b, h => by
      simp only [finite, Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h with h | ⟨ha, hb⟩
      · exact ⟨[fun _ => b.empty], fun f => List.mem_singleton.mpr
          (funext fun x => eq_empty_of_unique b h (f x))⟩
      · obtain ⟨l, hl⟩ := exists_list_of_finite a ha
        obtain ⟨m, hm⟩ := exists_list_of_finite b hb
        obtain ⟨fs, hfs⟩ := exists_list_agreeing b.empty m hm l
        refine ⟨fs, fun f => ?_⟩
        obtain ⟨g, hg, hgf⟩ := hfs f
        rwa [show f = g from funext fun x => (hgf x (hl x)).symm]

/-- Whether the code is built only from the types `Ty` builds in, with no declared type inside: then
it denotes the type it stands for itself. -/
def builtin : Ty → Bool
  | unit => true
  | bool => true
  | nat => true
  | int => true
  | string => true
  | list a => a.builtin
  | array a => a.builtin
  | option a => a.builtin
  | prod a b => a.builtin && b.builtin
  | sum a b => a.builtin && b.builtin
  | decl _ _ _ => false
  | fin _ => true
  | atom _ => true
  | arrow a b => a.builtin && b.builtin
  | ref _ => false
  | mu _ _ _ _ => false

/-- The trees of the `k`-th type of the group with the base `b`, the data and arguments `g` and the
recursive fields `r`, of which `mu b g r i` denotes the `i`-th (`denote_mu`). -/
@[reducible] def MuOf (b g r : Ty) (i k : Nat) : Type :=
  muTy b g r i (fun j => bif r.grows i then r.muN j else 0) k

theorem denote_mu (b g r : Ty) (i : Nat) : (mu b g r i).denote = MuOf b g r i i := rfl

/-- A way to build a value of the `j`-th type of `G` from each constructor `c` of the group's `j`-th
type, with the data of its other fields and a value of `G` for each child. -/
@[reducible] def MuAlg (g r : Ty) (i : Nat) (G : Nat → Type) : Type :=
  (j : Nat) → (c : Fin (bif r.grows i then r.muN j else 0)) → g.den [j, c, 0] →
    ((f : Fin (r.muA j c)) → g.den [j, c, 1, f] → G (r.muS j c f)) → G j

/-- The fold of a tree of the group: `base` on a base value, and `alg` on a node, given the folds of
its children. The deriving handler of `LeanIntent.Declared` writes the map from a tree back to the
type a project declares as one. -/
def muFold {b g r : Ty} {i : Nat} (G : Nat → Type) (base : b.denote → G i) (alg : MuAlg g r i G) :
    {k : Nat} → MuOf b g r i k → G k
  | _, .base x => base x
  | _, .node c d k => alg _ c d fun f x => muFold G base alg (k f x)

/-- No number plus `k` is below `k`: the case of a constructor beyond those a type has. -/
theorem not_add_lt (n k : Nat) : ¬ n + k < k := by omega

end Ty

/-! ## Isomorphisms -/

/-- An isomorphism between `α` and `β`: a map each way, each undoing the other. A code stands for its
type through one (`LeanIntent.HasCode`). -/
structure Iso (α β : Type) where
  /-- The map from `α` to `β`. -/
  to : α → β
  /-- The map back. -/
  inv : β → α
  inv_to : ∀ x, inv (to x) = x
  to_inv : ∀ y, to (inv y) = y

namespace Iso

/-- The identity. -/
def refl (α : Type) : Iso α α := ⟨fun x => x, fun x => x, fun _ => rfl, fun _ => rfl⟩

/-- The isomorphism between equal types: each map is the cast along the equality, which Lean reduces
to the value itself wherever the two types are the same by definition. -/
def ofEq {α β : Type} (h : α = β) : Iso α β where
  to := cast h
  inv := cast h.symm
  inv_to x := by subst h; rfl
  to_inv y := by subst h; rfl

/-- One isomorphism after another. -/
def trans {α β γ : Type} (e : Iso α β) (f : Iso β γ) : Iso α γ where
  to x := f.to (e.to x)
  inv z := e.inv (f.inv z)
  inv_to x := by simp only [f.inv_to, e.inv_to]
  to_inv z := by simp only [e.to_inv, f.to_inv]

/-- Lists of isomorphic types, element by element. -/
def list {α β : Type} (e : Iso α β) : Iso (List α) (List β) where
  to := List.map e.to
  inv := List.map e.inv
  inv_to l := by induction l with
    | nil => rfl
    | cons x l ih => simp only [List.map_cons, e.inv_to, ih]
  to_inv l := by induction l with
    | nil => rfl
    | cons x l ih => simp only [List.map_cons, e.to_inv, ih]

/-- Arrays of isomorphic types, element by element. -/
def array {α β : Type} (e : Iso α β) : Iso (Array α) (Array β) where
  to := Array.map e.to
  inv := Array.map e.inv
  inv_to a := by rw [Array.map_map]; exact Array.map_id'' (fun x => e.inv_to x) a
  to_inv a := by rw [Array.map_map]; exact Array.map_id'' (fun x => e.to_inv x) a

/-- Options of isomorphic types. -/
def option {α β : Type} (e : Iso α β) : Iso (Option α) (Option β) where
  to := Option.map e.to
  inv := Option.map e.inv
  inv_to o := by cases o <;> simp only [Option.map_none, Option.map_some, e.inv_to]
  to_inv o := by cases o <;> simp only [Option.map_none, Option.map_some, e.to_inv]

/-- Pairs of isomorphic types, side by side. -/
def prod {α β γ δ : Type} (e : Iso α γ) (f : Iso β δ) : Iso (α × β) (γ × δ) where
  to x := (e.to x.1, f.to x.2)
  inv y := (e.inv y.1, f.inv y.2)
  inv_to x := by simp only [e.inv_to, f.inv_to]
  to_inv y := by simp only [e.to_inv, f.to_inv]

/-- Sums of isomorphic types, side by side. -/
def sum {α β γ δ : Type} (e : Iso α γ) (f : Iso β δ) : Iso (α ⊕ β) (γ ⊕ δ) where
  to := Sum.map e.to f.to
  inv := Sum.map e.inv f.inv
  inv_to x := by cases x <;> simp only [Sum.map_inl, Sum.map_inr, e.inv_to, f.inv_to]
  to_inv y := by cases y <;> simp only [Sum.map_inl, Sum.map_inr, e.to_inv, f.to_inv]

/-- Functions between isomorphic types: a function is carried by mapping its argument back and its
result forth. -/
def arrow {α β γ δ : Type} (e : Iso α γ) (f : Iso β δ) : Iso (α → β) (γ → δ) where
  to g := fun x => f.to (g (e.inv x))
  inv h := fun a => f.inv (h (e.to a))
  inv_to g := funext fun a => by simp only [e.inv_to, f.inv_to]
  to_inv h := funext fun x => by simp only [e.to_inv, f.to_inv]

end Iso

end LeanIntent
