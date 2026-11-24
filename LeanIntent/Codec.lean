module

public section

namespace LeanIntent

open Lean in
macro:max "chars!" s:str : term => do
  let cs : Array (TSyntax `term) :=
    s.getString.toList.toArray.map fun c => ⟨(Syntax.mkCharLit c).raw⟩
  `([$cs,*])

@[expose] def concealing (c : Char) : Bool :=
  let n := c.toNat
  n < 0x20 || (0x7F ≤ n && n < 0xA0) || n == 0x2028 || n == 0x2029 || n == 0x061C ||
    n == 0x200E || n == 0x200F || (0x202A ≤ n && n ≤ 0x202E) || (0x2066 ≤ n && n ≤ 0x2069)

@[expose] def Plain (l : List Char) : Prop := ∀ c ∈ l, c = '\n' ∨ concealing c = false

instance (l : List Char) : Decidable (Plain l) :=
  inferInstanceAs (Decidable (∀ c ∈ l, c = '\n' ∨ concealing c = false))

theorem plain_nil : Plain [] := by intro _ h; cases h

theorem plain_append {l l' : List Char} (h : Plain l) (h' : Plain l') : Plain (l ++ l') := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact h c hc
  · exact h' c hc

theorem plain_flatten {ls : List (List Char)} (h : ∀ l ∈ ls, Plain l) : Plain ls.flatten := by
  intro c hc
  obtain ⟨l, hl, hc⟩ := List.mem_flatten.mp hc
  exact h l hl c hc

@[expose] def stripPrefix : List Char → List Char → Option (List Char)
  | [], s => some s
  | c :: p, d :: s => if c = d then stripPrefix p s else none
  | _ :: _, [] => none

@[simp] theorem stripPrefix_append (p s : List Char) : stripPrefix p (p ++ s) = some s := by
  induction p with
  | nil => rfl
  | cons c p ih => simp [stripPrefix, ih]

@[expose] def Diverge : List Char → List Char → Bool
  | a :: k₁, b :: k₂ => a != b || Diverge k₁ k₂
  | _, _ => false

theorem stripPrefix_of_diverge {k₁ k₂ : List Char} (h : Diverge k₁ k₂ = true) (s : List Char) :
    stripPrefix k₁ (k₂ ++ s) = none := by
  induction k₁ generalizing k₂ with
  | nil => cases k₂ <;> simp [Diverge] at h
  | cons a k₁ ih =>
    cases k₂ with
    | nil => simp [Diverge] at h
    | cons b k₂ =>
      by_cases hab : a = b
      · subst hab
        simp only [Diverge, bne_self_eq_false, Bool.false_or] at h
        simp [stripPrefix, ih h]
      · simp [stripPrefix, hab]

structure Codec (α : Type) where
  print : α → List Char
  parse : List Char → Option (α × List Char)
  parse_print : ∀ a rest, parse (print a ++ rest) = some (a, rest)
  plain : ∀ a, Plain (print a)

namespace Codec

variable {α β : Type}

@[expose] def unit : Codec Unit where
  print _ := []
  parse s := some ((), s)
  parse_print _ _ := rfl
  plain _ := plain_nil

@[expose] def keyed (k : List Char) (hk : Plain k := by decide) (c : Codec α) : Codec α where
  print a := k ++ c.print a
  parse s := (stripPrefix k s).bind c.parse
  parse_print a rest := by simp [List.append_assoc, c.parse_print]
  plain a := plain_append hk (c.plain a)

@[expose] def seq (c₁ : Codec α) (c₂ : Codec β) : Codec (α × β) where
  print p := c₁.print p.1 ++ c₂.print p.2
  parse s := (c₁.parse s).bind fun (a, r) => (c₂.parse r).map fun (b, r') => ((a, b), r')
  parse_print p rest := by simp [List.append_assoc, c₁.parse_print, c₂.parse_print]
  plain p := plain_append (c₁.plain p.1) (c₂.plain p.2)

@[expose] def map (c : Codec β) (f : α → β) (g : β → Option α) (h : ∀ a, g (f a) = some a) : Codec α where
  print a := c.print (f a)
  parse s := (c.parse s).bind fun (b, r) => (g b).map (·, r)
  parse_print a rest := by simp [c.parse_print, h]
  plain a := c.plain (f a)

@[expose] def dep {γ : α → Type} (c : Codec α) (k : (a : α) → Codec (γ a)) : Codec ((a : α) × γ a) where
  print p := c.print p.1 ++ (k p.1).print p.2
  parse s := (c.parse s).bind fun (a, r) => ((k a).parse r).map fun (b, r') => (⟨a, b⟩, r')
  parse_print p rest := by simp [List.append_assoc, c.parse_print, (k p.1).parse_print]
  plain p := plain_append (c.plain p.1) ((k p.1).plain p.2)

theorem findSome?_of_unique {l : List α} {f : α → Option β} {a : α} {b : β} (ha : a ∈ l)
    (hb : f a = some b) (h : ∀ x ∈ l, x ≠ a → f x = none) : l.findSome? f = some b := by
  induction l with
  | nil => cases ha
  | cons x l ih =>
    by_cases hx : x = a
    · subst hx; simp [hb]
    · have hl : a ∈ l := (List.mem_cons.mp ha).resolve_left (Ne.symm hx)
      rw [List.findSome?_cons, h x List.mem_cons_self hx]
      exact ih hl fun y hy => h y (List.mem_cons_of_mem _ hy)

@[expose] def keywords [DecidableEq α] (kw : α → List Char) (all : List α) (complete : ∀ a, a ∈ all)
    (free : ∀ a ∈ all, ∀ b ∈ all, a ≠ b → Diverge (kw a) (kw b) = true)
    (plain : ∀ a, Plain (kw a)) : Codec α where
  print := kw
  parse s := all.findSome? fun a => (stripPrefix (kw a) s).map (a, ·)
  parse_print a rest := findSome?_of_unique (complete a) (by simp) fun x hx hxa => by
    simp [stripPrefix_of_diverge (free x hx a (complete a) hxa)]
  plain := plain

@[expose] def SumBody (α β : Type) : Bool → Type
  | false => α
  | true => β

@[expose] def sum (kl kr : List Char) (h : Diverge kl kr = true ∧ Diverge kr kl = true)
    (hl : Plain kl := by decide) (hr : Plain kr := by decide) (cl : Codec α) (cr : Codec β) :
    Codec (α ⊕ β) :=
  map ((keywords (fun b => if b then kr else kl) [false, true]
      (by intro b; cases b <;> simp)
      (by intro a _ b _ _; cases a <;> cases b <;> simp_all)
      (by intro b; cases b <;> simp [hl, hr])).dep
      (γ := SumBody α β) fun | false => cl | true => cr)
    (fun | .inl a => ⟨false, a⟩ | .inr b => ⟨true, b⟩)
    (fun | ⟨false, a⟩ => some (.inl a) | ⟨true, b⟩ => some (.inr b))
    (fun x => by cases x <;> rfl)

@[expose] def option (kNone kSome : List Char) (h : Diverge kNone kSome = true ∧ Diverge kSome kNone = true)
    (hn : Plain kNone := by decide) (hs : Plain kSome := by decide) (c : Codec α) :
    Codec (Option α) :=
  map (sum kNone kSome h hn hs unit c) (fun | .none => .inl () | .some a => .inr a)
    (fun | .inl _ => some none | .inr a => some (some a)) (fun o => by cases o <;> rfl)

@[expose] def read (c : Codec α) (s : List Char) : Option α :=
  match c.parse s with
  | .some (a, _) => if c.print a = s then .some a else .none
  | .none => .none

theorem read_eq_some_iff (c : Codec α) (s : List Char) (a : α) :
    c.read s = some a ↔ c.print a = s := by
  constructor
  · intro h
    unfold read at h
    split at h
    · split at h
      · cases h; assumption
      · cases h
    · cases h
  · rintro rfl
    have := c.parse_print a []
    simp only [List.append_nil] at this
    simp [read, this]

theorem read_print (c : Codec α) (a : α) : c.read (c.print a) = some a :=
  (c.read_eq_some_iff _ _).mpr rfl

theorem print_injective (c : Codec α) {a b : α} (h : c.print a = c.print b) : a = b := by
  have := c.read_print a
  rw [h, c.read_print b] at this
  exact (Option.some.inj this).symm

end Codec

end LeanIntent
