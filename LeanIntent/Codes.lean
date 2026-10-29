/-!
# The types the degenerate class covers

The degenerate subjects of an intent record are fixed by the subject's type alone: each constant
function, the identity, the empty output and each projection. Lean's logic cannot inspect a type, so
the class is computed from a *code* for the type: a value of the closed inductive type `Ty`, whose
denotation `Ty.denote` is a type that stands for it through an isomorphism (`Iso`). The codes are
those of the unit type, `Bool`, `Nat`, `Int` and `String`, of lists, arrays, options, pairs and sums
of coded types, each of which denotes the type itself, and of the structures and inductive types a
project declares (`Ty.decl`), which `LeanIntent.Declared` writes from each declaration.
`LeanIntent.Degenerate` builds the class over functions of such types; a type with no code is not
covered.

The code of a declared type, `Ty.decl n ps r`, holds its name `n`, the chain of the codes of its type
parameters `ps`, and its *representation* `r`: for each constructor in declaration order, the chain
of its fields' codes in declaration order, each field paired with the chain after it and the last
with the unit code; one constructor is represented by its chain, and several by the sum of the first
one's chain and the representation of the rest. It denotes its representation, and every rule below
is its representation's, so the class treats a declared type as the sum of its constructors' chains;
only its projections differ, which reach into its fields and not into the chain that holds them
(`LeanIntent.Degenerate`). Its name and parameters keep apart two declared types whose
representations are equal.

For each code this module computes:

* `Ty.empty`, the empty value of the type: zero, the empty string, list or array, `none`, `false`
  and the unit value, componentwise for a pair, the left side's for a sum, and for a declared type,
  its first constructor applied to its fields' empty values;
* `Ty.part`, the values at which the class takes constant subjects. `Ty.finite` decides whether the
  type has finitely many values: when it holds, `Ty.part` lists every value
  (`Ty.mem_part_of_finite`), and when it fails, the type has infinitely many (`Ty.infinite`). The
  rule that fixes the part is `Ty.Small`, which `Ty.part` computes (`Ty.mem_part_iff`): a number, a
  string, a list or an array contributes only its empty value; the unit type and `Bool` every value;
  an option, a pair or a sum every value built from its components' parts; and a declared type each
  constructor applied to each combination of values of its fields' parts. The rule is fixed here,
  with the class, so that no record chooses which constants it is checked against.
-/

namespace LeanIntent

/-- Codes of the first-order data types the degenerate class covers. -/
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
  deriving DecidableEq

namespace Ty

/-- The type a code stands for. It is reducible, so that Lean's simplifier sees the type through
the code. -/
@[reducible] def denote : Ty → Type
  | unit => Unit
  | bool => Bool
  | nat => Nat
  | int => Int
  | string => String
  | list a => List a.denote
  | array a => Array a.denote
  | option a => Option a.denote
  | prod a b => a.denote × b.denote
  | sum a b => a.denote ⊕ b.denote
  | decl _ _ r => r.denote

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

/-- The values at which the degenerate class takes constant subjects, as a list. -/
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

/-- The rule that fixes which values of a type the degenerate class takes constant subjects at,
written apart from `part`: a number, a string, a list or an array only at its empty value; the unit
type and `Bool` at every value; an option at `none` and at each value of its part under `some`; a
pair at each pair of values of its sides' parts; and a sum at each value of either side's part. -/
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

/-- Whether the type has finitely many values: the unit type and `Bool` do, numbers, strings, lists
and arrays do not, and an option, a pair or a sum does exactly when each of its components does. -/
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

/-- `part` lists exactly the values the rule `Small` admits. -/
theorem mem_part_iff : (t : Ty) → (x : t.denote) → (x ∈ t.part ↔ t.Small x)
  | unit, x => by cases x; simp [part, Small]
  | bool, x => by cases x <;> simp [part, Small]
  | nat, x => by simp [part, Small]
  | int, x => by simp [part, Small]
  | string, x => by simp [part, Small]
  | list _, x => by simp [part, Small]
  | array _, x => by simp [part, Small]
  | option a, x => by
      cases x with
      | none => simp [part, Small]
      | some y => simp [part, Small, mem_part_iff a y]
  | prod a b, x => by
      obtain ⟨y, z⟩ := x
      simp [part, Small, mem_part_iff a y, mem_part_iff b z]
  | sum a b, x => by
      cases x with
      | inl y => simp [part, Small, mem_part_iff a y]
      | inr z => simp [part, Small, mem_part_iff b z]
  | decl _ _ r, x => mem_part_iff r x

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

/-- The empty value of every type is in its part. -/
theorem empty_mem_part (t : Ty) : t.empty ∈ t.part := (mem_part_iff t _).mpr (small_empty t)

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

/-- A type with finitely many values has every one in its part. -/
theorem mem_part_of_finite {t : Ty} (h : t.finite = true) (x : t.denote) : x ∈ t.part :=
  (mem_part_iff t x).mpr (small_of_finite t h x)

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
