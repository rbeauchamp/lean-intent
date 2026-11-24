module

public import LeanIntent.Codes
public import LeanIntent.Explain

public section

namespace LeanIntent

structure Sig where
  args : List Ty
  out : Ty
  deriving @[expose] DecidableEq

namespace Sig

@[expose, reducible] def Fn (b : Ty) : List Ty → Type
  | [] => b.denote
  | a :: as => a.denote → Fn b as

@[expose, reducible] def denote (σ : Sig) : Type := Fn σ.out σ.args

@[expose, reducible] def Args : List Ty → Type
  | [] => Unit
  | a :: as => a.denote × Args as

@[expose] def Fn.apply {b : Ty} : {as : List Ty} → Fn b as → Args as → b.denote
  | [], f, _ => f
  | _ :: _, f, xs => Fn.apply (f xs.1) xs.2

@[expose] def Fn.const (b : Ty) (v : b.denote) : (as : List Ty) → Fn b as
  | [] => v
  | _ :: as => fun _ => Fn.const b v as

theorem Fn.apply_const {b : Ty} (v : b.denote) :
    (as : List Ty) → (xs : Args as) → (Fn.const b v as).apply xs = v
  | [], _ => rfl
  | _ :: as, xs => Fn.apply_const v as xs.2

@[expose] def Fn.curry (b : Ty) : (as : List Ty) → (Args as → b.denote) → Fn b as
  | [], g => g ()
  | _ :: as, g => fun x => Fn.curry b as fun xs => g (x, xs)

theorem Fn.apply_curry {b : Ty} : (as : List Ty) → (g : Args as → b.denote) → (xs : Args as) →
    (Fn.curry b as g).apply xs = g xs
  | [], _, () => rfl
  | _ :: as, g, (x, xs) => Fn.apply_curry as (fun ys => g (x, ys)) xs

@[expose, reducible] def ofTy : Ty → Sig
  | .arrow a b => ⟨a :: (ofTy b).args, (ofTy b).out⟩
  | .unit => ⟨[], .unit⟩
  | .bool => ⟨[], .bool⟩
  | .nat => ⟨[], .nat⟩
  | .int => ⟨[], .int⟩
  | .string => ⟨[], .string⟩
  | .list a => ⟨[], .list a⟩
  | .array a => ⟨[], .array a⟩
  | .option a => ⟨[], .option a⟩
  | .prod a b => ⟨[], .prod a b⟩
  | .sum a b => ⟨[], .sum a b⟩
  | .decl n ps r => ⟨[], .decl n ps r⟩
  | .fin n => ⟨[], .fin n⟩
  | .atom k => ⟨[], .atom k⟩
  | .ref l => ⟨[], .ref l⟩
  | .mu b g r i => ⟨[], .mu b g r i⟩
  | .muAt b g r j i => ⟨[], .muAt b g r j i⟩

@[expose] def flat : (t : Ty) → Iso t.denote (ofTy t).denote
  | .arrow a b => (Iso.refl a.denote).arrow (flat b)
  | .unit | .bool | .nat | .int | .string | .list _ | .array _ | .option _ | .prod _ _ | .sum _ _
  | .decl _ _ _ | .fin _ | .atom _ | .ref _ | .mu _ _ _ _ | .muAt _ _ _ _ _ => Iso.refl _

theorem out_ofTy_ne_arrow : (t : Ty) → (a b : Ty) → (ofTy t).out ≠ .arrow a b
  | .arrow _ r, a, b => out_ofTy_ne_arrow r a b
  | .unit, _, _ | .bool, _, _ | .nat, _, _ | .int, _, _ | .string, _, _ | .list _, _, _
  | .array _, _, _ | .option _, _, _ | .prod _ _, _, _ | .sum _ _, _, _ | .decl _ _ _, _, _
  | .fin _, _, _ | .atom _, _, _ | .ref _, _, _ | .mu _ _ _ _, _, _ | .muAt _ _ _ _ _, _, _ => nofun

end Sig

open Sig

mutual

inductive Ty.Proj (S : Ty → Type) : Ty → Ty → Type
  | self (t : Ty) : Ty.Proj S t t
  | fst {a c : Ty} (b : Ty) : Ty.Proj S a c → Ty.Proj S (.prod a b) c
  | snd {b c : Ty} (a : Ty) : Ty.Proj S b c → Ty.Proj S (.prod a b) c
  | field {r c : Ty} (n : Lean.Name) (ps : Ty) : Ty.FieldProj S r c → Ty.Proj S (.decl n ps r) c
  | app {a b c : Ty} (s : S a) : Ty.Proj S b c → Ty.Proj S (.arrow a b) c

inductive Ty.FieldProj (S : Ty → Type) : Ty → Ty → Type
  | head {a c : Ty} (rest : Ty) : Ty.Proj S a c → Ty.FieldProj S (.prod a rest) c
  | tail {rest c : Ty} (a : Ty) : Ty.FieldProj S rest c → Ty.FieldProj S (.prod a rest) c

end

mutual

@[expose] def Ty.Proj.get {S : Ty → Type} (ev : (a : Ty) → S a → a.denote) :
    {t c : Ty} → Ty.Proj S t c → t.denote → c.denote
  | _, _, .self _, x => x
  | _, _, .fst _ p, x => p.get ev x.1
  | _, _, .snd _ p, x => p.get ev x.2
  | _, _, .field _ _ q, x => q.get ev x
  | _, _, .app s p, f => p.get ev (f (ev _ s))

@[expose] def Ty.FieldProj.get {S : Ty → Type} (ev : (a : Ty) → S a → a.denote) :
    {r c : Ty} → Ty.FieldProj S r c → r.denote → c.denote
  | _, _, .head _ p, x => p.get ev x.1
  | _, _, .tail _ q, x => q.get ev x.2

end

@[expose] def Ty.Proj.ofEq {S : Ty → Type} : {t c : Ty} → t = c → Ty.Proj S t c
  | _, _, rfl => .self _

@[expose] def Ty.selfProjs {S : Ty → Type} (c t : Ty) : List (Ty.Proj S t c) :=
  if h : t = c then [.ofEq h] else []

mutual

@[expose] def Ty.projs {S : Ty → Type} (src : (a : Ty) → List (S a)) (c : Ty) :
    (t : Ty) → List (Ty.Proj S t c)
  | .prod a b =>
    Ty.selfProjs c (.prod a b) ++ (Ty.projs src c a).map (.fst b) ++ (Ty.projs src c b).map (.snd a)
  | .decl n ps r => Ty.selfProjs c (.decl n ps r) ++ (Ty.fieldProjs src c r).map (.field n ps)
  | .arrow a b =>
    Ty.selfProjs c (.arrow a b) ++ (src a).flatMap fun s => (Ty.projs src c b).map (.app s)
  | t => Ty.selfProjs c t

@[expose] def Ty.fieldProjs {S : Ty → Type} (src : (a : Ty) → List (S a)) (c : Ty) :
    (r : Ty) → List (Ty.FieldProj S r c)
  | .prod a rest => (Ty.projs src c a).map (.head rest) ++ (Ty.fieldProjs src c rest).map (.tail a)
  | _ => []

end

theorem Ty.self_mem_selfProjs {S : Ty → Type} (t : Ty) :
    (Ty.Proj.self t : Ty.Proj S t t) ∈ Ty.selfProjs t t := by
  simp [Ty.selfProjs, Ty.Proj.ofEq]

mutual

theorem Ty.mem_projs {S : Ty → Type} {src : (a : Ty) → List (S a)} (hs : ∀ a (s : S a), s ∈ src a)
    {c : Ty} : {t : Ty} → (p : Ty.Proj S t c) → p ∈ Ty.projs src c t
  | _, .self t => by
      cases t <;> simp only [Ty.projs, List.mem_append] <;>
        first
        | exact Ty.self_mem_selfProjs _
        | exact .inl (.inl (Ty.self_mem_selfProjs _))
        | exact .inl (Ty.self_mem_selfProjs _)
  | _, .fst b p => by
      simp only [Ty.projs, List.mem_append, List.mem_map]
      exact .inl (.inr ⟨p, Ty.mem_projs hs p, rfl⟩)
  | _, .snd a p => by
      simp only [Ty.projs, List.mem_append, List.mem_map]
      exact .inr ⟨p, Ty.mem_projs hs p, rfl⟩
  | _, .field n ps q => by
      simp only [Ty.projs, List.mem_append, List.mem_map]
      exact .inr ⟨q, Ty.mem_fieldProjs hs q, rfl⟩
  | _, .app s p => by
      simp only [Ty.projs, List.mem_append, List.mem_flatMap, List.mem_map]
      exact .inr ⟨s, hs _ s, p, Ty.mem_projs hs p, rfl⟩

theorem Ty.mem_fieldProjs {S : Ty → Type} {src : (a : Ty) → List (S a)}
    (hs : ∀ a (s : S a), s ∈ src a) {c : Ty} :
    {r : Ty} → (q : Ty.FieldProj S r c) → q ∈ Ty.fieldProjs src c r
  | _, .head rest p => by
      simp only [Ty.fieldProjs, List.mem_append, List.mem_map]
      exact .inl ⟨p, Ty.mem_projs hs p, rfl⟩
  | _, .tail a q => by
      simp only [Ty.fieldProjs, List.mem_append, List.mem_map]
      exact .inr ⟨q, Ty.mem_fieldProjs hs q, rfl⟩

end

inductive ArgPath (S : Ty → Type) (c : Ty) : List Ty → Type
  | here {a : Ty} {as : List Ty} : Ty.Proj S a c → ArgPath S c (a :: as)
  | there {a : Ty} {as : List Ty} : ArgPath S c as → ArgPath S c (a :: as)

namespace ArgPath

variable {S : Ty → Type} {c : Ty}

@[expose] def read (ev : (a : Ty) → S a → a.denote) : {as : List Ty} → ArgPath S c as → Args as → c.denote
  | _ :: _, .here p, xs => p.get ev xs.1
  | _ :: _, .there q, xs => q.read ev xs.2

@[expose] def all (src : (a : Ty) → List (S a)) (c : Ty) : (as : List Ty) → List (ArgPath S c as)
  | [] => []
  | a :: as => (Ty.projs src c a).map .here ++ (all src c as).map .there

theorem mem_all {src : (a : Ty) → List (S a)} (hs : ∀ a (s : S a), s ∈ src a) :
    {as : List Ty} → (p : ArgPath S c as) → p ∈ all src c as
  | _ :: _, .here p => List.mem_append.mpr (.inl (List.mem_map.mpr ⟨p, Ty.mem_projs hs p, rfl⟩))
  | _ :: _, .there q => List.mem_append.mpr (.inr (List.mem_map.mpr ⟨q, mem_all hs q, rfl⟩))

end ArgPath

abbrev NoSource : Ty → Type := fun _ => Empty

abbrev ArgSource (Γ : List Ty) (a : Ty) : Type := Option (ArgPath NoSource a Γ)

namespace ArgSource

@[expose] def val {Γ : List Ty} (xs : Args Γ) (a : Ty) : ArgSource Γ a → a.denote
  | none => a.empty
  | some p => p.read (fun _ s => nomatch s) xs

@[expose] def all (Γ : List Ty) (a : Ty) : List (ArgSource Γ a) :=
  none :: (ArgPath.all (fun _ => []) a Γ).map some

theorem mem_all (Γ : List Ty) (a : Ty) : ∀ s : ArgSource Γ a, s ∈ all Γ a
  | none => List.mem_cons_self
  | some p => List.mem_cons_of_mem _
      (List.mem_map.mpr ⟨p, ArgPath.mem_all (fun _ s => nomatch s) p, rfl⟩)

end ArgSource

abbrev ArgProj (c : Ty) (as : List Ty) : Type := ArgPath (ArgSource as) c as

namespace ArgProj

variable {c : Ty}

@[expose] def read {as : List Ty} (p : ArgProj c as) (xs : Args as) : c.denote :=
  ArgPath.read (ArgSource.val xs) p xs

@[expose] def fn {as : List Ty} (p : ArgProj c as) : Fn c as := Fn.curry c as p.read

@[expose] def all (c : Ty) (as : List Ty) : List (ArgProj c as) := ArgPath.all (ArgSource.all as) c as

theorem mem_all {as : List Ty} (p : ArgProj c as) : p ∈ all c as :=
  ArgPath.mem_all (ArgSource.mem_all as) p

theorem apply_fn {as : List Ty} (p : ArgProj c as) (xs : Args as) : p.fn.apply xs = p.read xs :=
  Fn.apply_curry as p.read xs

end ArgProj

inductive Degenerate (σ : Sig) where
  | const (v : σ.out.denote)
  | proj (p : ArgProj σ.out σ.args)
  | others

@[expose] def Sig.constants (σ : Sig) : List (Degenerate σ) :=
  if σ.out.count ≤ Ty.listBound then σ.out.part.map .const else [.const σ.out.empty, .others]

@[expose] def Sig.degenerate (σ : Sig) : List (Degenerate σ) :=
  σ.constants ++ (ArgProj.all σ.out σ.args).map .proj

@[expose] def Sig.Args.empty : (as : List Ty) → Args as
  | [] => ()
  | a :: as => (a.empty, Sig.Args.empty as)

namespace Sig

theorem mem_degenerate_iff {σ : Sig} (d : Degenerate σ) :
    d ∈ σ.degenerate ↔
      (σ.out.count ≤ Ty.listBound ∧ ∃ v, d = .const v ∧ σ.out.Small v) ∨
      (Ty.listBound < σ.out.count ∧ (d = .const σ.out.empty ∨ d = .others)) ∨
      ∃ p, d = .proj p := by
  simp only [degenerate, constants, List.mem_append]
  by_cases h : σ.out.count ≤ Ty.listBound
  · simp only [h, ↓reduceIte, true_and, Nat.not_lt.mpr h, false_and, false_or, List.mem_map]
    constructor
    · rintro (⟨v, hv, rfl⟩ | ⟨p, _, rfl⟩)
      · exact .inl ⟨v, rfl, (Ty.mem_part_iff _ h v).mp hv⟩
      · exact .inr ⟨p, rfl⟩
    · rintro (⟨v, rfl, hv⟩ | ⟨p, rfl⟩)
      · exact .inl ⟨v, (Ty.mem_part_iff _ h v).mpr hv, rfl⟩
      · exact .inr ⟨p, ArgProj.mem_all p, rfl⟩
  · have h' := Nat.lt_of_not_le h
    simp only [h, ↓reduceIte, h', false_and, false_or, true_and, List.mem_cons, List.not_mem_nil,
      or_false, List.mem_map]
    constructor
    · rintro (h | ⟨p, _, rfl⟩)
      · exact .inl h
      · exact .inr ⟨p, rfl⟩
    · rintro (h | ⟨p, rfl⟩)
      · exact .inl h
      · exact .inr ⟨p, ArgProj.mem_all p, rfl⟩

theorem empty_output_mem (σ : Sig) : Degenerate.const σ.out.empty ∈ σ.degenerate := by
  refine (mem_degenerate_iff _).mpr ?_
  by_cases h : σ.out.count ≤ Ty.listBound
  · exact .inl ⟨h, _, rfl, Ty.small_empty _⟩
  · exact .inr (.inl ⟨Nat.lt_of_not_le h, .inl rfl⟩)

theorem degenerate_ne_nil (σ : Sig) : σ.degenerate ≠ [] := List.ne_nil_of_mem (empty_output_mem σ)

theorem const_mem_of_small {σ : Sig} (hc : σ.out.count ≤ Ty.listBound) {v : σ.out.denote}
    (h : σ.out.Small v) : Degenerate.const v ∈ σ.degenerate :=
  (mem_degenerate_iff _).mpr (.inl ⟨hc, v, rfl, h⟩)

theorem others_mem {σ : Sig} (hc : Ty.listBound < σ.out.count) : Degenerate.others ∈ σ.degenerate :=
  (mem_degenerate_iff _).mpr (.inr (.inl ⟨hc, .inr rfl⟩))

theorem const_mem_of_finite {σ : Sig} (hc : σ.out.count ≤ Ty.listBound) (h : σ.out.finite = true)
    (v : σ.out.denote) : Degenerate.const v ∈ σ.degenerate :=
  const_mem_of_small hc (Ty.small_of_finite _ h v)

theorem proj_mem {σ : Sig} (p : ArgProj σ.out σ.args) : Degenerate.proj p ∈ σ.degenerate :=
  (mem_degenerate_iff _).mpr (.inr (.inr ⟨p, rfl⟩))

theorem length_constants_le (σ : Sig) : σ.constants.length ≤ Ty.listBound := by
  unfold constants
  split
  · rename_i h
    simpa using Nat.le_trans (Ty.length_part_le σ.out) h
  · simp [Ty.listBound]

theorem length_degenerate_le (σ : Sig) :
    σ.degenerate.length ≤ Ty.listBound + (ArgProj.all σ.out σ.args).length := by
  simp only [degenerate, List.length_append, List.length_map]
  exact Nat.add_le_add_right (length_constants_le σ) _

theorem identity_mem (t : Ty) :
    ∃ p : ArgProj t [t], Degenerate.proj p ∈ (⟨[t], t⟩ : Sig).degenerate ∧ p.fn = fun x => x :=
  ⟨.here (.self t), proj_mem _, rfl⟩

theorem constants_infinite {σ : Sig} (h : σ.out.finite = false) :
    ∃ f : Nat → σ.denote, Function.Injective f ∧ ∀ n, ∃ v, ∀ xs, Fn.apply (f n) xs = v := by
  obtain ⟨g, hg⟩ := Ty.infinite σ.out h
  refine ⟨fun n => Fn.const σ.out (g n) σ.args, fun m n e => hg ?_,
    fun n => ⟨g n, Fn.apply_const (g n) σ.args⟩⟩
  have := congrArg (fun f => Fn.apply f (Args.empty σ.args)) e
  simpa only [Fn.apply_const] using this

end Sig

inductive Ty.Stands : (α : Type) → (t : Ty) → Iso α t.denote → Prop
  | builtin {α : Type} (t : Ty) (h : α = t.denote) : t.builtin = true → Ty.Stands α t (Iso.ofEq h)
  | list {α : Type} {t : Ty} {e : Iso α t.denote} :
      Ty.Stands α t e → Ty.Stands (List α) (.list t) e.list
  | array {α : Type} {t : Ty} {e : Iso α t.denote} :
      Ty.Stands α t e → Ty.Stands (Array α) (.array t) e.array
  | option {α : Type} {t : Ty} {e : Iso α t.denote} :
      Ty.Stands α t e → Ty.Stands (Option α) (.option t) e.option
  | prod {α β : Type} {a b : Ty} {e : Iso α a.denote} {f : Iso β b.denote} :
      Ty.Stands α a e → Ty.Stands β b f → Ty.Stands (α × β) (.prod a b) (e.prod f)
  | sum {α β : Type} {a b : Ty} {e : Iso α a.denote} {f : Iso β b.denote} :
      Ty.Stands α a e → Ty.Stands β b f → Ty.Stands (α ⊕ β) (.sum a b) (e.sum f)
  | arrow {α β : Type} {a b : Ty} {e : Iso α a.denote} {f : Iso β b.denote} :
      Ty.Stands α a e → Ty.Stands β b f → Ty.Stands (α → β) (.arrow a b) (e.arrow f)
  | private decl {α : Type} (n : Lean.Name) (ps r : Ty) (e : Iso α (Ty.decl n ps r).denote) :
      Ty.Stands α (.decl n ps r) e

class ExactCode (α : Type) where
  code : Ty
  denote_eq : α = code.denote
  builtin : code.builtin = true

instance : ExactCode Unit := ⟨.unit, rfl, rfl⟩
instance : ExactCode Bool := ⟨.bool, rfl, rfl⟩
instance : ExactCode Nat := ⟨.nat, rfl, rfl⟩
instance : ExactCode Int := ⟨.int, rfl, rfl⟩
instance : ExactCode String := ⟨.string, rfl, rfl⟩
instance {n : Nat} : ExactCode (Fin (n + 1)) := ⟨.fin n, rfl, rfl⟩
instance : ExactCode Char := ⟨.atom .char, rfl, rfl⟩
instance : ExactCode UInt8 := ⟨.atom .uint8, rfl, rfl⟩
instance : ExactCode UInt16 := ⟨.atom .uint16, rfl, rfl⟩
instance : ExactCode UInt32 := ⟨.atom .uint32, rfl, rfl⟩
instance : ExactCode UInt64 := ⟨.atom .uint64, rfl, rfl⟩
instance : ExactCode USize := ⟨.atom .usize, rfl, rfl⟩
instance : ExactCode Int8 := ⟨.atom .int8, rfl, rfl⟩
instance : ExactCode Int16 := ⟨.atom .int16, rfl, rfl⟩
instance : ExactCode Int32 := ⟨.atom .int32, rfl, rfl⟩
instance : ExactCode Int64 := ⟨.atom .int64, rfl, rfl⟩
instance : ExactCode ISize := ⟨.atom .isize, rfl, rfl⟩
instance : ExactCode Float := ⟨.atom .float, rfl, rfl⟩
instance : ExactCode Float32 := ⟨.atom .float32, rfl, rfl⟩
instance {w : Nat} : ExactCode (BitVec w) := ⟨.atom (.bitVec w), rfl, rfl⟩

instance {α : Type} [h : ExactCode α] : ExactCode (List α) :=
  ⟨.list h.code, congrArg List h.denote_eq, h.builtin⟩

instance {α : Type} [h : ExactCode α] : ExactCode (Array α) :=
  ⟨.array h.code, congrArg Array h.denote_eq, h.builtin⟩

instance {α : Type} [h : ExactCode α] : ExactCode (Option α) :=
  ⟨.option h.code, congrArg Option h.denote_eq, h.builtin⟩

instance {α β : Type} [ha : ExactCode α] [hb : ExactCode β] : ExactCode (α × β) :=
  ⟨.prod ha.code hb.code, by
    show (α × β) = (ha.code.denote × hb.code.denote)
    rw [← ha.denote_eq, ← hb.denote_eq], by
    show (ha.code.builtin && hb.code.builtin) = true
    rw [ha.builtin, hb.builtin]; rfl⟩

instance {α β : Type} [ha : ExactCode α] [hb : ExactCode β] : ExactCode (α ⊕ β) :=
  ⟨.sum ha.code hb.code, by
    show (α ⊕ β) = (ha.code.denote ⊕ hb.code.denote)
    rw [← ha.denote_eq, ← hb.denote_eq], by
    show (ha.code.builtin && hb.code.builtin) = true
    rw [ha.builtin, hb.builtin]; rfl⟩

instance {α β : Type} [ha : ExactCode α] [hb : ExactCode β] : ExactCode (α → β) :=
  ⟨.arrow ha.code hb.code, by
    show (α → β) = (ha.code.denote → hb.code.denote)
    rw [← ha.denote_eq, ← hb.denote_eq], by
    show (ha.code.builtin && hb.code.builtin) = true
    rw [ha.builtin, hb.builtin]; rfl⟩

class HasCode (α : Type) where
  code : Ty
  iso : Iso α code.denote
  stands : Ty.Stands α code iso

instance (priority := high) {α : Type} [h : ExactCode α] : HasCode α :=
  ⟨h.code, Iso.ofEq h.denote_eq, .builtin h.code h.denote_eq h.builtin⟩

instance {α : Type} [h : HasCode α] : HasCode (List α) := ⟨.list h.code, h.iso.list, .list h.stands⟩

instance {α : Type} [h : HasCode α] : HasCode (Array α) :=
  ⟨.array h.code, h.iso.array, .array h.stands⟩

instance {α : Type} [h : HasCode α] : HasCode (Option α) :=
  ⟨.option h.code, h.iso.option, .option h.stands⟩

instance {α β : Type} [ha : HasCode α] [hb : HasCode β] : HasCode (α × β) :=
  ⟨.prod ha.code hb.code, ha.iso.prod hb.iso, .prod ha.stands hb.stands⟩

instance {α β : Type} [ha : HasCode α] [hb : HasCode β] : HasCode (α ⊕ β) :=
  ⟨.sum ha.code hb.code, ha.iso.sum hb.iso, .sum ha.stands hb.stands⟩

instance {α β : Type} [ha : HasCode α] [hb : HasCode β] : HasCode (α → β) :=
  ⟨.arrow ha.code hb.code, ha.iso.arrow hb.iso, .arrow ha.stands hb.stands⟩

inductive Sig.Stands : (W : Type) → (σ : Sig) → Iso W σ.denote → Prop
  | of {α : Type} {t : Ty} {e : Iso α t.denote} :
      Ty.Stands α t e → Sig.Stands α (Sig.ofTy t) (e.trans (Sig.flat t))

theorem Sig.Stands.out_ne_arrow {W : Type} {σ : Sig} {e : Iso W σ.denote} (h : Sig.Stands W σ e)
    (a b : Ty) : σ.out ≠ .arrow a b := by
  cases h
  exact Sig.out_ofTy_ne_arrow _ a b

class Covered (W : Type) where
  sig : Sig
  iso : Iso W sig.denote
  stands : Sig.Stands W sig iso

instance {α : Type} [h : HasCode α] : Covered α :=
  ⟨Sig.ofTy h.code, h.iso.trans (Sig.flat h.code), .of h.stands⟩

@[expose] def degenerate (W : Type) [c : Covered W] : List (Degenerate c.sig) := c.sig.degenerate

@[expose] def Degenerate.constantSubject {W : Type} [c : Covered W] (v : c.sig.out.denote) : W :=
  c.iso.inv (Fn.const c.sig.out v c.sig.args)

@[expose] def Degenerate.projSubject {W : Type} [c : Covered W] (p : ArgProj c.sig.out c.sig.args) : W :=
  c.iso.inv p.fn

theorem Degenerate.iso_constantSubject {W : Type} [c : Covered W] (v : c.sig.out.denote) :
    c.iso.to (Degenerate.constantSubject v : W) = Fn.const c.sig.out v c.sig.args :=
  c.iso.to_inv _

theorem Degenerate.iso_projSubject {W : Type} [c : Covered W] (p : ArgProj c.sig.out c.sig.args) :
    c.iso.to (Degenerate.projSubject p : W) = p.fn :=
  c.iso.to_inv _

inductive Degenerate.Reading (W : Type) where
  | subject (w : W)
  | otherConstants

@[expose] def Degenerate.reading {W : Type} [c : Covered W] : Degenerate c.sig → Degenerate.Reading W
  | .const v => .subject (Degenerate.constantSubject v)
  | .proj p => .subject (Degenerate.projSubject p)
  | .others => .otherConstants

theorem degenerate_ne_nil (W : Type) [Covered W] : degenerate W ≠ [] := Sig.degenerate_ne_nil _

section Verdicts

variable {W : Type} [c : Covered W]

@[expose] def Degenerate.Is (d : Degenerate c.sig) (w : W) : Prop :=
  match d with
  | .const v => w = Degenerate.constantSubject v
  | .proj p => w = Degenerate.projSubject p
  | .others => ∃ v, c.sig.out.Small v ∧ v ≠ c.sig.out.empty ∧ w = Degenerate.constantSubject v

@[expose] def Degenerate.Meets (d : Degenerate c.sig) (r : IntentRecord W) : Prop :=
  match d with
  | .const v => r.Meets (Degenerate.constantSubject v)
  | .proj p => r.Meets (Degenerate.projSubject p)
  | .others => ∃ w, (Degenerate.others : Degenerate c.sig).Is w ∧ r.Meets w

theorem Degenerate.meets_iff (d : Degenerate c.sig) (r : IntentRecord W) :
    d.Meets r ↔ ∃ w, d.Is w ∧ r.Meets w := by
  cases d with
  | const v =>
    refine ⟨fun h => ⟨_, rfl, h⟩, fun ⟨w, e, h⟩ => ?_⟩
    rwa [show w = Degenerate.constantSubject v from e] at h
  | proj p =>
    refine ⟨fun h => ⟨_, rfl, h⟩, fun ⟨w, e, h⟩ => ?_⟩
    rwa [show w = Degenerate.projSubject p from e] at h
  | others => exact Iff.rfl

theorem Degenerate.is_of_reading_eq_subject {d : Degenerate c.sig} {w : W}
    (h : d.reading = .subject w) : d.Is w ∧ ∀ w', d.Is w' → w' = w := by
  cases d with
  | const v =>
    obtain rfl := Degenerate.Reading.subject.inj h
    exact ⟨rfl, fun _ e => e⟩
  | proj p =>
    obtain rfl := Degenerate.Reading.subject.inj h
    exact ⟨rfl, fun _ e => e⟩
  | others => cases h

theorem Degenerate.reading_eq_otherConstants_iff (d : Degenerate c.sig) :
    d.reading = (.otherConstants : Degenerate.Reading W) ↔ d = .others := by
  cases d <;> simp [Degenerate.reading]

@[expose] def verdictGoal (r : IntentRecord W) (d : Degenerate c.sig) : Bool → Prop
  | true => d.Meets r
  | false => ¬ d.Meets r

@[expose] def verdictGoals (r : IntentRecord W) : List (Degenerate c.sig) → List Bool → List Prop
  | [], [] => []
  | d :: ds, b :: bs => verdictGoal r d b :: verdictGoals r ds bs
  | _, _ => [False]

@[expose] def verdicts (r : IntentRecord W) (bs : List Bool) : List Prop := verdictGoals r (degenerate W) bs

@[expose] def Verdicts (r : IntentRecord W) (bs : List Bool) : Prop := Goals (verdicts r bs)

@[expose] def intendedVerdicts (r : IntentRecord W) (bs : List Bool) : Prop :=
  bs.length = (degenerate W).length ∧
    ∀ (i : Nat) (hb : i < bs.length) (hd : i < (degenerate W).length),
      (bs[i] = true ↔ ∃ w, (degenerate W)[i].Is w ∧ (∀ x ∈ r.dom, x.holds w) ∧
        ∀ p ∈ r.props, p.holds w)

theorem goals_verdictGoals (r : IntentRecord W) : (ds : List (Degenerate c.sig)) →
    (bs : List Bool) → (Goals (verdictGoals r ds bs) ↔ bs.length = ds.length ∧
      ∀ (i : Nat) (hb : i < bs.length) (hd : i < ds.length), (bs[i] = true ↔ ds[i].Meets r))
  | [], [] => by simp [verdictGoals, Goals]
  | [], _ :: _ => by simp [verdictGoals, Goals]
  | _ :: _, [] => by simp [verdictGoals, Goals]
  | d :: ds, b :: bs => by
      rw [verdictGoals, Goals, goals_verdictGoals r ds bs]
      constructor
      · rintro ⟨hv, hlen, hall⟩
        refine ⟨by simp [hlen], fun i hb hd => ?_⟩
        cases i with
        | zero => cases b <;> simpa [verdictGoal] using hv
        | succ i => simpa using hall i (by simpa using hb) (by simpa using hd)
      · rintro ⟨hlen, hall⟩
        refine ⟨?_, by simpa using hlen, fun i hb hd =>
          hall (i + 1) (Nat.succ_lt_succ hb) (Nat.succ_lt_succ hd)⟩
        have h0 := hall 0 (by simp) (by simp)
        cases b <;> simpa [verdictGoal] using h0

theorem verdicts_correct (r : IntentRecord W) (bs : List Bool) :
    Verdicts r bs ↔ intendedVerdicts r bs := by
  rw [Verdicts, verdicts, goals_verdictGoals]
  simp only [intendedVerdicts, Degenerate.meets_iff, IntentRecord.Meets, IntentRecord.Dom,
    IntentRecord.Props]

@[expose] def metByGo : List (Degenerate c.sig) → List Bool → List (Degenerate c.sig)
  | d :: ds, true :: bs => d :: metByGo ds bs
  | _ :: ds, false :: bs => metByGo ds bs
  | _, _ => []

@[expose] def metBy (W : Type) [c : Covered W] (bs : List Bool) : List (Degenerate c.sig) :=
  metByGo (degenerate W) bs

theorem mem_metByGo (r : IntentRecord W) (d : Degenerate c.sig) : (ds : List (Degenerate c.sig)) →
    (bs : List Bool) → Goals (verdictGoals r ds bs) →
      (d ∈ metByGo ds bs ↔ d ∈ ds ∧ d.Meets r)
  | [], [], _ => by simp [metByGo]
  | [], _ :: _, h => absurd h (by simp [verdictGoals, Goals])
  | _ :: _, [], h => absurd h (by simp [verdictGoals, Goals])
  | d' :: ds, true :: bs, ⟨hv, h⟩ => by
      rw [metByGo, List.mem_cons, mem_metByGo r d ds bs h, List.mem_cons]
      constructor
      · rintro (rfl | ⟨hd, hm⟩)
        · exact ⟨.inl rfl, hv⟩
        · exact ⟨.inr hd, hm⟩
      · rintro ⟨rfl | hd, hm⟩
        · exact .inl rfl
        · exact .inr ⟨hd, hm⟩
  | d' :: ds, false :: bs, ⟨hv, h⟩ => by
      rw [metByGo, mem_metByGo r d ds bs h, List.mem_cons]
      constructor
      · rintro ⟨hd, hm⟩
        exact ⟨.inr hd, hm⟩
      · rintro ⟨rfl | hd, hm⟩
        · exact absurd hm hv
        · exact ⟨hd, hm⟩

theorem mem_metBy {r : IntentRecord W} {bs : List Bool} (h : Verdicts r bs)
    (d : Degenerate c.sig) : d ∈ metBy W bs ↔ d ∈ degenerate W ∧ d.Meets r :=
  mem_metByGo r d _ bs h

theorem metBy_eq_nil_iff {r : IntentRecord W} {bs : List Bool} (h : Verdicts r bs) :
    metBy W bs = [] ↔ ∀ d ∈ degenerate W, ¬ d.Meets r := by
  rw [List.eq_nil_iff_forall_not_mem]
  exact forall_congr' fun d => by rw [mem_metBy h]; exact not_and

theorem meets_of_subject_mem_metBy {r : IntentRecord W} {bs : List Bool} (h : Verdicts r bs) {w : W}
    (hw : Degenerate.Reading.subject w ∈ (metBy W bs).map Degenerate.reading) : r.Meets w := by
  obtain ⟨d, hd, e⟩ := List.mem_map.mp hw
  obtain ⟨w', hi, hm⟩ := (d.meets_iff r).mp ((mem_metBy h d).mp hd).2
  rwa [(Degenerate.is_of_reading_eq_subject e).2 w' hi] at hm

theorem otherConstants_mem_metBy_iff {r : IntentRecord W} {bs : List Bool} (h : Verdicts r bs) :
    Degenerate.Reading.otherConstants ∈ (metBy W bs).map Degenerate.reading ↔
      Degenerate.others ∈ degenerate W ∧ ∃ v, c.sig.out.Small v ∧ v ≠ c.sig.out.empty ∧
        r.Meets (Degenerate.constantSubject v) := by
  constructor
  · intro hw
    obtain ⟨d, hd, e⟩ := List.mem_map.mp hw
    obtain rfl := (Degenerate.reading_eq_otherConstants_iff d).mp e
    obtain ⟨ho, w, ⟨v, hs, hn, rfl⟩, hm⟩ := (mem_metBy h _).mp hd
    exact ⟨ho, v, hs, hn, hm⟩
  · rintro ⟨ho, v, hs, hn, hm⟩
    exact List.mem_map.mpr ⟨.others, (mem_metBy h _).mpr ⟨ho, _, ⟨v, hs, hn, rfl⟩, hm⟩, rfl⟩

theorem constant_covered {v : c.sig.out.denote} (hv : c.sig.out.Small v) :
    ∃ d ∈ degenerate W, d.Is (Degenerate.constantSubject v) := by
  by_cases hc : c.sig.out.count ≤ Ty.listBound
  · exact ⟨.const v, Sig.const_mem_of_small hc hv, rfl⟩
  · by_cases he : v = c.sig.out.empty
    · subst he
      exact ⟨.const _, Sig.empty_output_mem _, rfl⟩
    · exact ⟨.others, Sig.others_mem (Nat.lt_of_not_le hc), v, hv, he, rfl⟩

theorem constant_covered_of_finite (h : c.sig.out.finite = true) (v : c.sig.out.denote) :
    ∃ d ∈ degenerate W, d.Is (Degenerate.constantSubject v) :=
  constant_covered (Ty.small_of_finite _ h v)

theorem not_meets_of_metBy_eq_nil {r : IntentRecord W} {bs : List Bool} (h : Verdicts r bs)
    (he : metBy W bs = []) {d : Degenerate c.sig} (hd : d ∈ degenerate W) {w : W} (hw : d.Is w) :
    ¬ r.Meets w :=
  fun hm => (metBy_eq_nil_iff h).mp he d hd ((d.meets_iff r).mpr ⟨w, hw, hm⟩)

@[expose] def Degenerate.name {σ : Sig} : Degenerate σ → String
  | .const _ => "the record allows a subject that returns one value whatever its arguments"
  | .proj _ => "the record allows a subject that returns one of its arguments, what a function among \
      them returns, or a part of either"
  | .others => "the record allows a subject that returns one value whatever its arguments, at some \
      value other than the empty one"

@[expose] def Degenerate.consequence (d : Degenerate c.sig) : Consequence W :=
  ⟨d.name, .possibility, d.Is⟩

theorem Degenerate.declined_keptBy_iff (d : Degenerate c.sig) (r : IntentRecord W) :
    (Answer.mk d.consequence .declined).KeptBy r ↔ ¬ d.Meets r := by
  simp only [Answer.KeptBy, Degenerate.consequence, d.meets_iff]
  exact ⟨fun h ⟨w, hi, hm⟩ => h w hm hi, fun h w hm hi => h ⟨w, hi, hm⟩⟩

@[expose] def possibilities {r : IntentRecord W} {bs : List Bool} (_ : Verdicts r bs) : List (Consequence W) :=
  (metBy W bs).map Degenerate.consequence

theorem mem_possibilities {r : IntentRecord W} {bs : List Bool} (h : Verdicts r bs)
    (x : Consequence W) :
    x ∈ possibilities h ↔ ∃ d ∈ degenerate W, d.Meets r ∧ x = d.consequence := by
  simp only [possibilities, List.mem_map, mem_metBy h]
  exact ⟨fun ⟨d, ⟨hd, hm⟩, e⟩ => ⟨d, hd, hm, e.symm⟩, fun ⟨d, hd, hm, e⟩ => ⟨d, ⟨hd, hm⟩, e.symm⟩⟩

theorem possibilities_holdsOf {r : IntentRecord W} {bs : List Bool} (h : Verdicts r bs)
    (x : Consequence W) (hx : x ∈ possibilities h) : x.kind = .possibility ∧ x.HoldsOf r := by
  obtain ⟨d, _, hm, rfl⟩ := (mem_possibilities h x).mp hx
  obtain ⟨w, hi, hm⟩ := (d.meets_iff r).mp hm
  exact ⟨rfl, w, hm, hi⟩

end Verdicts

end LeanIntent
