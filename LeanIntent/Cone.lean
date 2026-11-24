module

public import Lean.CoreM
public import Std.Data.HashSet.Lemmas
public import LeanIntent.Loaded

public section

namespace LeanIntent.Cone

open Lean

@[expose] def Mentions (c : Name) : Expr → Prop
  | .const d _ => c = d
  | .proj s _ e => c = s ∨ Mentions c e
  | .lit (.natVal _) => c = ``Nat
  | .lit (.strVal _) => c = ``String
  | .app f a => Mentions c f ∨ Mentions c a
  | .lam _ t b _ => Mentions c t ∨ Mentions c b
  | .forallE _ t b _ => Mentions c t ∨ Mentions c b
  | .letE _ t v b _ => Mentions c t ∨ Mentions c v ∨ Mentions c b
  | .mdata _ e => Mentions c e
  | .bvar _ | .fvar _ | .mvar _ | .sort _ => False

@[expose] def exprRefs : Expr → List Name → List Name
  | .const c _, acc => c :: acc
  | .proj s _ e, acc => s :: exprRefs e acc
  | .lit (.natVal _), acc => ``Nat :: acc
  | .lit (.strVal _), acc => ``String :: acc
  | .app f a, acc => exprRefs f (exprRefs a acc)
  | .lam _ t b _, acc => exprRefs t (exprRefs b acc)
  | .forallE _ t b _, acc => exprRefs t (exprRefs b acc)
  | .letE _ t v b _, acc => exprRefs t (exprRefs v (exprRefs b acc))
  | .mdata _ e, acc => exprRefs e acc
  | .bvar _, acc | .fvar _, acc | .mvar _, acc | .sort _, acc => acc

theorem mem_exprRefs {c : Name} :
    (e : Expr) → (acc : List Name) → (c ∈ exprRefs e acc ↔ Mentions c e ∨ c ∈ acc)
  | .const d _, acc => by simp [exprRefs, Mentions]
  | .proj s _ e, acc => by simp [exprRefs, Mentions, mem_exprRefs e acc, or_assoc]
  | .lit (.natVal _), acc => by simp [exprRefs, Mentions]
  | .lit (.strVal _), acc => by simp [exprRefs, Mentions]
  | .app f a, acc => by simp [exprRefs, Mentions, mem_exprRefs f, mem_exprRefs a, or_assoc]
  | .lam _ t b _, acc => by simp [exprRefs, Mentions, mem_exprRefs t, mem_exprRefs b, or_assoc]
  | .forallE _ t b _, acc => by
    simp [exprRefs, Mentions, mem_exprRefs t, mem_exprRefs b, or_assoc]
  | .letE _ t v b _, acc => by
    simp [exprRefs, Mentions, mem_exprRefs t, mem_exprRefs v, mem_exprRefs b, or_assoc]
  | .mdata _ e, acc => by simp [exprRefs, Mentions, mem_exprRefs e]
  | .bvar _, acc | .fvar _, acc | .mvar _, acc | .sort _, acc => by simp [exprRefs, Mentions]

inductive Reaches (lookup : Name → Option ConstantInfo) (refers : ConstantInfo → Name → Prop)
    (roots : List Name) : Name → Prop where
  | root {c : Name} : c ∈ roots → Reaches lookup refers roots c
  | step {d c : Name} {ci : ConstantInfo} : Reaches lookup refers roots d → lookup d = some ci →
      refers ci c → Reaches lookup refers roots c

inductive Refusal where
  | impl (c : Name)
  | unknown (c : Name)
  | axiom (c : Name)
  | fuel
  deriving @[expose] Inhabited, Repr, @[expose] DecidableEq

@[expose] def Admitted (lookup : Name → Option ConstantInfo) (isImpl : Name → Bool) (axioms : List Name)
    (c : Name) : Prop :=
  isImpl c = false ∧ ∃ ci, lookup c = some ci ∧ (ci.isAxiom → c ∈ axioms)

@[expose] def visit (lookup : Name → Option ConstantInfo) (isImpl : Name → Bool) (axioms : List Name)
    (c : Name) : Except Refusal ConstantInfo :=
  if isImpl c then .error (.impl c) else
    match lookup c with
    | none => .error (.unknown c)
    | some ci => if ci.isAxiom && !axioms.contains c then .error (.axiom c) else .ok ci

@[expose] def nextNew (visited : Std.HashSet Name) : List Name → Option (Name × List Name)
  | [] => none
  | c :: rest => if visited.contains c then nextNew visited rest else some (c, rest)

@[expose] def explore (lookup : Name → Option ConstantInfo) (deps : ConstantInfo → List Name)
    (isImpl : Name → Bool) (axioms : List Name) :
    Nat → Std.HashSet Name → List Name → Option Refusal
  | fuel, visited, work =>
    match nextNew visited work with
    | none => none
    | some (c, rest) =>
      match visit lookup isImpl axioms c with
      | .error r => some r
      | .ok ci =>
        match fuel with
        | 0 => some .fuel
        | fuel + 1 => explore lookup deps isImpl axioms fuel (visited.insert c) (deps ci ++ rest)

@[expose] def exclude (lookup : Name → Option ConstantInfo) (deps : ConstantInfo → List Name)
    (isImpl : Name → Bool) (axioms : List Name) (fuel : Nat) (roots : List Name) :
    Option Refusal :=
  explore lookup deps isImpl axioms fuel ∅ roots

@[expose] def Within (lookup : Name → Option ConstantInfo) (refers : ConstantInfo → Name → Prop)
    (roots : List Name) (fuel : Nat) : Prop :=
  ∃ l : List Name, l.length ≤ fuel ∧ ∀ c, Reaches lookup refers roots c → c ∈ l

section Decides

variable {lookup : Name → Option ConstantInfo} {deps : ConstantInfo → List Name}
  {isImpl : Name → Bool} {axioms : List Name}

theorem visit_eq_ok {c : Name} {ci : ConstantInfo} :
    visit lookup isImpl axioms c = .ok ci ↔
      isImpl c = false ∧ lookup c = some ci ∧ (ci.isAxiom → c ∈ axioms) := by
  unfold visit
  cases hi : isImpl c <;> cases hl : lookup c <;> simp
  split <;> simp_all
  rintro rfl
  simp_all

theorem visit_ok_iff {c : Name} :
    (∃ ci, visit lookup isImpl axioms c = .ok ci) ↔ Admitted lookup isImpl axioms c := by
  simp only [visit_eq_ok, Admitted]
  exact ⟨fun ⟨ci, h1, h2, h3⟩ => ⟨h1, ci, h2, h3⟩, fun ⟨h1, ci, h2, h3⟩ => ⟨ci, h1, h2, h3⟩⟩

theorem nextNew_eq_none {V : Std.HashSet Name} :
    (W : List Name) → nextNew V W = none → ∀ w ∈ W, w ∈ V
  | [], _, w, hw => nomatch hw
  | c :: rest, h, w, hw => by
    unfold nextNew at h
    split at h
    · rename_i hc
      rcases List.mem_cons.mp hw with rfl | hw
      · exact Std.HashSet.contains_iff_mem.mp hc
      · exact nextNew_eq_none rest h w hw
    · exact absurd h (by simp)

theorem nextNew_eq_some {V : Std.HashSet Name} {c : Name} {rest : List Name} :
    (W : List Name) → nextNew V W = some (c, rest) →
      c ∈ W ∧ c ∉ V ∧ (∀ w ∈ rest, w ∈ W) ∧ ∀ w ∈ W, w ∈ V ∨ w = c ∨ w ∈ rest
  | [], h => nomatch h
  | d :: ds, h => by
    unfold nextNew at h
    split at h
    · rename_i hd
      obtain ⟨h1, h2, h3, h4⟩ := nextNew_eq_some ds h
      refine ⟨List.mem_cons_of_mem _ h1, h2, fun w hw => List.mem_cons_of_mem _ (h3 w hw), ?_⟩
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact .inl (Std.HashSet.contains_iff_mem.mp hd)
      · exact h4 w hw
    · rename_i hd
      cases h
      refine ⟨List.mem_cons_self, fun h => hd (Std.HashSet.contains_iff_mem.mpr h),
        fun w hw => List.mem_cons_of_mem _ hw, fun w hw => ?_⟩
      rcases List.mem_cons.mp hw with rfl | hw
      · exact .inr (.inl rfl)
      · exact .inr (.inr hw)

theorem size_lt_length {V : Std.HashSet Name} {c : Name} {l : List Name}
    (hV : ∀ v ∈ V, v ∈ l) (hc : c ∉ V) (hcl : c ∈ l) : V.size + 1 ≤ l.length := by
  have hnd : V.toList.Nodup :=
    Std.HashSet.distinct_toList.imp fun h e => by simp [e] at h
  have hnd' : (c :: V.toList).Nodup :=
    List.nodup_cons.mpr ⟨fun h => hc (Std.HashSet.mem_toList.mp h), hnd⟩
  have hsub : c :: V.toList ⊆ l := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hcl
    · exact hV x (Std.HashSet.mem_toList.mp hx)
  have := hnd'.length_le_of_subset hsub
  simpa [Std.HashSet.length_toList] using this

theorem mem_insert {V : Std.HashSet Name} {c v : Name} : v ∈ V.insert c ↔ v = c ∨ v ∈ V := by
  rw [Std.HashSet.mem_insert, beq_iff_eq, eq_comm]

theorem size_insert_of_not_mem {V : Std.HashSet Name} {c : Name} (hc : c ∉ V) :
    (V.insert c).size = V.size + 1 := by
  rw [Std.HashSet.size_insert, ite_eq_right_iff.mpr (fun h => absurd h hc)]

variable {refers : ConstantInfo → Name → Prop} {roots : List Name}

theorem explore_eq_none_closed (hdeps : ∀ ci c, c ∈ deps ci ↔ refers ci c) :
    (fuel : Nat) → (V : Std.HashSet Name) → (W : List Name) →
    (∀ v ∈ V, Admitted lookup isImpl axioms v ∧
      ∀ ci, lookup v = some ci → ∀ d, refers ci d → d ∈ V ∨ d ∈ W) →
    explore lookup deps isImpl axioms fuel V W = none →
    ∃ V' : Std.HashSet Name, V'.size ≤ V.size + fuel ∧ (∀ v ∈ V, v ∈ V') ∧ (∀ w ∈ W, w ∈ V') ∧
      ∀ v ∈ V', Admitted lookup isImpl axioms v ∧
        ∀ ci, lookup v = some ci → ∀ d, refers ci d → d ∈ V'
  | fuel, V, W, hInv, h => by
    unfold explore at h
    split at h
    · rename_i hn
      have hW := nextNew_eq_none W hn
      refine ⟨V, Nat.le_add_right _ _, fun v hv => hv, hW, fun v hv => ⟨(hInv v hv).1, ?_⟩⟩
      intro ci hci d hd
      rcases (hInv v hv).2 ci hci d hd with h | h
      · exact h
      · exact hW d h
    · rename_i c rest hn
      obtain ⟨-, hcV, -, hWsplit⟩ := nextNew_eq_some W hn
      split at h
      · exact nomatch h
      · rename_i ci hv
        obtain ⟨hi, hl, ha⟩ := visit_eq_ok.mp hv
        cases fuel with
        | zero => exact nomatch h
        | succ fuel =>
          have hInv' : ∀ v ∈ V.insert c, Admitted lookup isImpl axioms v ∧
              ∀ ci', lookup v = some ci' → ∀ d, refers ci' d →
                d ∈ V.insert c ∨ d ∈ deps ci ++ rest := by
            intro v hv
            rcases mem_insert.mp hv with rfl | hv
            · refine ⟨⟨hi, ci, hl, ha⟩, fun ci' hci' d hd => ?_⟩
              rw [hl] at hci'
              cases hci'
              exact .inr (List.mem_append_left _ ((hdeps _ _).mpr hd))
            · refine ⟨(hInv v hv).1, fun ci' hci' d hd => ?_⟩
              rcases (hInv v hv).2 ci' hci' d hd with h' | h'
              · exact .inl (mem_insert.mpr (.inr h'))
              · rcases hWsplit d h' with h'' | rfl | h''
                · exact .inl (mem_insert.mpr (.inr h''))
                · exact .inl (mem_insert.mpr (.inl rfl))
                · exact .inr (List.mem_append_right _ h'')
          obtain ⟨V', hsize, hVV, hWV, hcl⟩ :=
            explore_eq_none_closed hdeps fuel (V.insert c) (deps ci ++ rest) hInv' h
          refine ⟨V', ?_, fun v hv => hVV v (mem_insert.mpr (.inr hv)), ?_, hcl⟩
          · rw [size_insert_of_not_mem hcV] at hsize
            omega
          · intro w hw
            rcases hWsplit w hw with h' | rfl | h'
            · exact hVV w (mem_insert.mpr (.inr h'))
            · exact hVV w (mem_insert.mpr (.inl rfl))
            · exact hWV w (List.mem_append_right _ h')

theorem explore_eq_none_of (hdeps : ∀ ci c, c ∈ deps ci ↔ refers ci c)
    (hAll : ∀ c, Reaches lookup refers roots c → Admitted lookup isImpl axioms c)
    {l : List Name} (hl : ∀ c, Reaches lookup refers roots c → c ∈ l) :
    (fuel : Nat) → (V : Std.HashSet Name) → (W : List Name) →
    (∀ v ∈ V, Reaches lookup refers roots v) → (∀ w ∈ W, Reaches lookup refers roots w) →
    l.length ≤ V.size + fuel → explore lookup deps isImpl axioms fuel V W = none
  | fuel, V, W, hV, hW, hfuel => by
    unfold explore
    split
    · rfl
    · rename_i c rest hn
      obtain ⟨hcW, hcV, hrest, -⟩ := nextNew_eq_some W hn
      have hc := hW c hcW
      obtain ⟨hi, ci, hl', ha⟩ := hAll c hc
      have hv : visit lookup isImpl axioms c = .ok ci := visit_eq_ok.mpr ⟨hi, hl', ha⟩
      rw [hv]
      cases fuel with
      | zero =>
        have := size_lt_length (fun v hv' => hl v (hV v hv')) hcV (hl c hc)
        omega
      | succ fuel =>
        refine explore_eq_none_of hdeps hAll hl fuel (V.insert c) (deps ci ++ rest) ?_ ?_ ?_
        · intro v hv'
          rcases mem_insert.mp hv' with rfl | hv'
          · exact hc
          · exact hV v hv'
        · intro w hw
          rcases List.mem_append.mp hw with hw | hw
          · exact .step hc hl' ((hdeps _ _).mp hw)
          · exact hW w (hrest w hw)
        · rw [size_insert_of_not_mem hcV]
          omega

theorem exclude_eq_none_iff (hdeps : ∀ ci c, c ∈ deps ci ↔ refers ci c) (fuel : Nat) :
    exclude lookup deps isImpl axioms fuel roots = none ↔
      (∀ c, Reaches lookup refers roots c → Admitted lookup isImpl axioms c) ∧
        Within lookup refers roots fuel := by
  constructor
  · intro h
    obtain ⟨V, hsize, -, hroots, hcl⟩ := explore_eq_none_closed hdeps fuel ∅ roots
      (fun v hv => absurd hv Std.HashSet.not_mem_empty) h
    have hreach : ∀ c, Reaches lookup refers roots c → c ∈ V := by
      intro c hc
      induction hc with
      | root hr => exact hroots _ hr
      | step _ hd hr ih => exact (hcl _ ih).2 _ hd _ hr
    refine ⟨fun c hc => (hcl c (hreach c hc)).1, V.toList, ?_, fun c hc => ?_⟩
    · simpa [Std.HashSet.length_toList] using hsize
    · exact Std.HashSet.mem_toList.mpr (hreach c hc)
  · rintro ⟨hAll, l, hlen, hl⟩
    exact explore_eq_none_of hdeps hAll hl fuel ∅ roots
      (fun v hv => absurd hv Std.HashSet.not_mem_empty) (fun w hw => .root hw)
      (by simpa using hlen)

theorem exclude_ne_none_of_reaches (hdeps : ∀ ci c, c ∈ deps ci ↔ refers ci c) {fuel : Nat}
    {c : Name} (hc : Reaches lookup refers roots c) (hi : isImpl c = true) :
    exclude lookup deps isImpl axioms fuel roots ≠ none := by
  intro h
  have := (((exclude_eq_none_iff hdeps fuel).mp h).1 c hc).1
  simp_all

theorem visit_eq_error {c : Name} {r : Refusal} (h : visit lookup isImpl axioms c = .error r) :
    (r = .impl c ∧ isImpl c = true) ∨ (r = .unknown c ∧ lookup c = none) ∨
      (r = .axiom c ∧ c ∉ axioms ∧ ∃ ci, lookup c = some ci ∧ ci.isAxiom = true) := by
  unfold visit at h
  cases hi : isImpl c <;> cases hl : lookup c <;> simp_all
  rename_i ci
  split at h <;> simp_all

@[expose] def Refusal.Holds (lookup : Name → Option ConstantInfo) (refers : ConstantInfo → Name → Prop)
    (isImpl : Name → Bool) (axioms : List Name) (roots : List Name) (fuel : Nat) :
    Refusal → Prop
  | .impl c => Reaches lookup refers roots c ∧ isImpl c = true
  | .unknown c => Reaches lookup refers roots c ∧ lookup c = none
  | .axiom c => Reaches lookup refers roots c ∧ c ∉ axioms ∧
      ∃ ci, lookup c = some ci ∧ ci.isAxiom = true
  | .fuel => ¬ Within lookup refers roots fuel

theorem explore_eq_some (hdeps : ∀ ci c, c ∈ deps ci ↔ refers ci c) (fuel₀ : Nat) :
    (fuel : Nat) → (V : Std.HashSet Name) → (W : List Name) →
    (∀ v ∈ V, Reaches lookup refers roots v) → (∀ w ∈ W, Reaches lookup refers roots w) →
    V.size + fuel = fuel₀ → ∀ {r : Refusal}, explore lookup deps isImpl axioms fuel V W = some r →
    r.Holds lookup refers isImpl axioms roots fuel₀
  | fuel, V, W, hV, hW, hfuel, r, h => by
    unfold explore at h
    split at h
    · exact nomatch h
    · rename_i c rest hn
      obtain ⟨hcW, hcV, hrest, -⟩ := nextNew_eq_some W hn
      have hc := hW c hcW
      split at h
      · rename_i r' he
        cases h
        rcases visit_eq_error he with ⟨rfl, hi⟩ | ⟨rfl, hl⟩ | ⟨rfl, ha, hci⟩
        · exact ⟨hc, hi⟩
        · exact ⟨hc, hl⟩
        · exact ⟨hc, ha, hci⟩
      · rename_i ci hv
        obtain ⟨-, hl, -⟩ := visit_eq_ok.mp hv
        cases fuel with
        | zero =>
          cases h
          rintro ⟨l, hlen, hlc⟩
          have := size_lt_length (fun v hv' => hlc v (hV v hv')) hcV (hlc c hc)
          omega
        | succ fuel =>
          refine explore_eq_some hdeps fuel₀ fuel (V.insert c) (deps ci ++ rest) ?_ ?_ ?_ h
          · intro v hv'
            rcases mem_insert.mp hv' with rfl | hv'
            · exact hc
            · exact hV v hv'
          · intro w hw
            rcases List.mem_append.mp hw with hw | hw
            · exact .step hc hl ((hdeps _ _).mp hw)
            · exact hW w (hrest w hw)
          · rw [size_insert_of_not_mem hcV]
            omega

theorem exclude_eq_some (hdeps : ∀ ci c, c ∈ deps ci ↔ refers ci c) {fuel : Nat} {r : Refusal}
    (h : exclude lookup deps isImpl axioms fuel roots = some r) :
    r.Holds lookup refers isImpl axioms roots fuel :=
  explore_eq_some hdeps fuel fuel ∅ roots (fun v hv => absurd hv Std.HashSet.not_mem_empty)
    (fun w hw => .root hw) (by simp) h

end Decides

@[expose] def RefersTo : ConstantInfo → Name → Prop
  | .axiomInfo v, c => Mentions c v.type
  | .defnInfo v, c => Mentions c v.type ∨ Mentions c v.value
  | .thmInfo v, c => Mentions c v.type
  | .opaqueInfo v, c => Mentions c v.type
  | .quotInfo v, c => Mentions c v.type
  | .inductInfo v, c => Mentions c v.type ∨ c ∈ v.all ∨ c ∈ v.ctors ∨ c = mkRecName v.name ∨
      ∃ b ∈ v.all.head?, ∃ i < v.numNested, c = (mkRecName b).appendIndexAfter (i + 1)
  | .ctorInfo v, c => Mentions c v.type ∨ c = v.induct
  | .recInfo v, c => Mentions c v.type ∨ c ∈ v.all ∨ ∃ r ∈ v.rules, c = r.ctor ∨ Mentions c r.rhs

@[expose] def declRefs : ConstantInfo → List Name
  | .axiomInfo v => exprRefs v.type []
  | .defnInfo v => exprRefs v.type (exprRefs v.value [])
  | .thmInfo v => exprRefs v.type []
  | .opaqueInfo v => exprRefs v.type []
  | .quotInfo v => exprRefs v.type []
  | .inductInfo v => exprRefs v.type (v.all ++ v.ctors ++ mkRecName v.name ::
      v.all.head?.toList.flatMap fun b =>
        (List.range v.numNested).map fun i => (mkRecName b).appendIndexAfter (i + 1))
  | .ctorInfo v => exprRefs v.type [v.induct]
  | .recInfo v => exprRefs v.type (v.all ++ v.rules.flatMap fun r => r.ctor :: exprRefs r.rhs [])

theorem mem_declRefs (ci : ConstantInfo) (c : Name) : c ∈ declRefs ci ↔ RefersTo ci c := by
  cases ci <;> simp [declRefs, RefersTo, mem_exprRefs, eq_comm (a := c)]

@[expose] def leanAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

@[expose] def isImplDecl (impl : List Name) (c : Name) : Bool :=
  impl.any fun i => i.isPrefixOf c || i.isPrefixOf (privateToUserName c)

@[expose] def lookupIn (env : Environment) (c : Name) : Option ConstantInfo :=
  ((env.setExporting false).find? (skipRealize := true) c).orElse fun _ =>
    env.toKernelEnv.find? c

inductive Unchecked where
  | noImpl
  | implUnknown (i : Name)
  deriving @[expose] Inhabited, Repr, @[expose] DecidableEq

@[expose] def firstUnknown (env : Environment) : List Name → Option Name
  | [] => none
  | i :: is => if (lookupIn env i).isSome then firstUnknown env is else some i

@[expose] def checkRecord (env : Environment) (record : Name) (impl : List Name) :
    Except (Unchecked ⊕ Refusal) Unit :=
  if impl.isEmpty then .error (.inl .noImpl) else
    match firstUnknown env impl with
    | some i => .error (.inl (.implUnknown i))
    | none =>
      match exclude (lookupIn env) declRefs (isImplDecl impl) leanAxioms (2 ^ 64) [record] with
      | some r => .error (.inr r)
      | none => .ok ()

theorem firstUnknown_eq_none {env : Environment} :
    (impl : List Name) → (firstUnknown env impl = none ↔ ∀ i ∈ impl, (lookupIn env i).isSome)
  | [] => by simp [firstUnknown]
  | i :: is => by
    unfold firstUnknown
    split <;> simp_all [firstUnknown_eq_none is]

theorem checkRecord_eq_ok_iff (env : Environment) (record : Name) (impl : List Name) :
    checkRecord env record impl = .ok () ↔
      impl ≠ [] ∧ (∀ i ∈ impl, (lookupIn env i).isSome) ∧
      (∀ c, Reaches (lookupIn env) RefersTo [record] c →
        Admitted (lookupIn env) (isImplDecl impl) leanAxioms c) ∧
      Within (lookupIn env) RefersTo [record] (2 ^ 64) := by
  rw [← exclude_eq_none_iff (deps := declRefs) mem_declRefs, ← firstUnknown_eq_none]
  unfold checkRecord
  cases impl with
  | nil => simp
  | cons i is =>
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, ne_eq, reduceCtorEq,
      not_false_eq_true, true_and]
    split <;> rename_i h <;> rw [h] <;> simp
    split <;> simp_all

theorem checkRecord_ne_ok_of_reaches {env : Environment} {record c : Name} {impl : List Name}
    (hc : Reaches (lookupIn env) RefersTo [record] c) (hi : isImplDecl impl c = true) :
    checkRecord env record impl ≠ .ok () := by
  intro h
  have := (((checkRecord_eq_ok_iff env record impl).mp h).2.2.1 c hc).1
  simp_all

@[expose] def describe (record : Name) : Unchecked ⊕ Refusal → String
  | .inl .noImpl => "no declaration of the implementation is named, so nothing is excluded"
  | .inl (.implUnknown i) => s!"the implementation's name {i} has no declaration here"
  | .inr (.impl c) => s!"{record} depends on {c}, a declaration of the implementation"
  | .inr (.unknown c) => s!"{record} depends on {c}, which has no declaration here"
  | .inr (.axiom c) => s!"{record} depends on the axiom {c}, which is not one of Lean's three \
      (propext, Classical.choice, Quot.sound); in a module of Lean's module system an imported \
      theorem, or an imported definition whose body is not exposed, is shown as an axiom"
  | .inr .fuel => s!"{record} depends on more than 2 ^ 64 declarations"

def requireIndependent (record : Name) (impl : List Name) : CoreM Unit := asking do
  match checkRecord (← getEnv) record impl with
  | .ok () => pure ()
  | .error e => throwError "intent record refused: {describe record e}"

end LeanIntent.Cone
