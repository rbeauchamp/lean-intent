module

public import LeanIntent.Cone

public section

namespace LeanIntent.Print

open Lean (Name ConstantInfo Expr)
open LeanIntent.Cone (declRefs mem_declRefs exprRefs mem_exprRefs Mentions RefersTo)

@[expose] def refsVia (eqn : Name → Option Expr) (c : Name) : ConstantInfo → List Name
  | .defnInfo v =>
    match eqn c with
    | some t => exprRefs v.type (exprRefs t [])
    | none => declRefs (.defnInfo v)
  | ci => declRefs ci

theorem mem_refsVia_eqn {eqn : Name → Option Expr} {c k : Name} {v : Lean.DefinitionVal} {t : Expr}
    (h : eqn c = some t) : k ∈ refsVia eqn c (.defnInfo v) ↔ Mentions k v.type ∨ Mentions k t := by
  simp [refsVia, h, mem_exprRefs]

theorem refsVia_eq_declRefs {eqn : Name → Option Expr} {c : Name} {ci : ConstantInfo}
    (h : eqn c = none ∨ ∀ v, ci ≠ .defnInfo v) : refsVia eqn c ci = declRefs ci := by
  cases ci with
  | defnInfo v =>
    rcases h with h | h
    · simp [refsVia, h]
    · exact absurd rfl (h v)
  | _ => rfl

theorem mem_declRefs_ctor {eqn : Name → Option Expr} {c : Name} {v : Lean.InductiveVal} {k : Name}
    (h : k ∈ v.ctors) : k ∈ refsVia eqn c (.inductInfo v) :=
  (mem_declRefs (.inductInfo v) k).mpr (Or.inr (Or.inr (Or.inl h)))

theorem mem_declRefs_induct {eqn : Name → Option Expr} {c : Name} {v : Lean.ConstructorVal} :
    v.induct ∈ refsVia eqn c (.ctorInfo v) :=
  (mem_declRefs (.ctorInfo v) v.induct).mpr (Or.inr rfl)

theorem mem_declRefs_block {eqn : Name → Option Expr} {c : Name} {v : Lean.RecursorVal} {i : Name}
    (h : i ∈ v.all) : i ∈ refsVia eqn c (.recInfo v) :=
  (mem_declRefs (.recInfo v) i).mpr (Or.inr (Or.inl h))

inductive Reach (lookup : Name → Option ConstantInfo) (eqn : Name → Option Expr)
    (stop : Name → Bool) (roots : List Name) : Name → Prop where
  | root {c : Name} : c ∈ roots → stop c = false → Reach lookup eqn stop roots c
  | step {d c : Name} {ci : ConstantInfo} : Reach lookup eqn stop roots d → lookup d = some ci →
      c ∈ refsVia eqn d ci → stop c = false → Reach lookup eqn stop roots c

inductive Gap where
  | unknown (c : Name)
  | fuel
  deriving @[expose] Inhabited, Repr, @[expose] DecidableEq

@[expose] def collect (lookup : Name → Option ConstantInfo) (eqn : Name → Option Expr) (stop : Name → Bool) :
    Nat → List Name → List (Name × ConstantInfo) → Except Gap (List (Name × ConstantInfo))
  | 0, _, _ => .error .fuel
  | _ + 1, [], done => .ok done
  | f + 1, c :: work, done =>
    if stop c = true ∨ c ∈ done.map Prod.fst then collect lookup eqn stop f work done
    else
      match lookup c with
      | none => .error (.unknown c)
      | some ci => collect lookup eqn stop f (refsVia eqn c ci ++ work) ((c, ci) :: done)

@[expose] def meaning (lookup : Name → Option ConstantInfo) (eqn : Name → Option Expr) (stop : Name → Bool)
    (roots : List Name) : Except Gap (List (Name × ConstantInfo)) :=
  (collect lookup eqn stop (2 ^ 64) roots []).map List.reverse

section Proofs

variable {lookup : Name → Option ConstantInfo} {eqn : Name → Option Expr} {stop : Name → Bool}
  {roots : List Name}

structure Inv (lookup : Name → Option ConstantInfo) (eqn : Name → Option Expr) (stop : Name → Bool)
    (roots : List Name) (work : List Name) (done : List (Name × ConstantInfo)) : Prop where
  found : ∀ p ∈ done, lookup p.1 = some p.2
  reached : ∀ p ∈ done, Reach lookup eqn stop roots p.1
  pending : ∀ c ∈ work, stop c = false → Reach lookup eqn stop roots c
  closed : ∀ p ∈ done, ∀ c ∈ refsVia eqn p.1 p.2, stop c = false →
    c ∈ done.map Prod.fst ∨ c ∈ work

theorem collect_ok : (f : Nat) → {work : List Name} → {done out : List (Name × ConstantInfo)} →
    collect lookup eqn stop f work done = .ok out → Inv lookup eqn stop roots work done →
    Inv lookup eqn stop roots [] out ∧ (∀ c ∈ work, stop c = false → c ∈ out.map Prod.fst) ∧
      ∀ p ∈ done, p ∈ out
  | 0, _, _, _, h, _ => by simp [collect] at h
  | _ + 1, [], done, out, h, hi => by
    simp only [collect, Except.ok.injEq] at h
    subst h
    exact ⟨hi, by simp, fun _ hp => hp⟩
  | f + 1, c :: work, done, out, h, hi => by
    simp only [collect] at h
    split at h
    · next hskip =>
      have hi' : Inv lookup eqn stop roots work done :=
        { found := hi.found, reached := hi.reached
          pending := fun x hx => hi.pending x (List.mem_cons_of_mem _ hx)
          closed := fun p hp x hx hs => by
            rcases hi.closed p hp x hx hs with h | h
            · exact .inl h
            · rcases List.mem_cons.mp h with rfl | h
              · rcases hskip with h' | h'
                · simp [hs] at h'
                · exact .inl h'
              · exact .inr h }
      obtain ⟨ho, hw, hd⟩ := collect_ok f h hi'
      refine ⟨ho, fun x hx hs => ?_, hd⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · rcases hskip with h' | h'
        · simp [hs] at h'
        · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h'
          exact List.mem_map.mpr ⟨p, hd p hp, rfl⟩
      · exact hw x hx hs
    · next hskip =>
      have hs : stop c = false := by simpa using fun h => hskip (.inl h)
      split at h
      · simp at h
      · next ci hci =>
        have hc : Reach lookup eqn stop roots c := hi.pending c (List.mem_cons_self ..) hs
        have hi' : Inv lookup eqn stop roots (refsVia eqn c ci ++ work) ((c, ci) :: done) :=
          { found := fun p hp => by
              rcases List.mem_cons.mp hp with rfl | hp
              · exact hci
              · exact hi.found p hp
            reached := fun p hp => by
              rcases List.mem_cons.mp hp with rfl | hp
              · exact hc
              · exact hi.reached p hp
            pending := fun x hx hxs => by
              rcases List.mem_append.mp hx with hx | hx
              · exact .step hc hci hx hxs
              · exact hi.pending x (List.mem_cons_of_mem _ hx) hxs
            closed := fun p hp x hx hxs => by
              rcases List.mem_cons.mp hp with rfl | hp
              · exact .inr (List.mem_append_left _ hx)
              · rcases hi.closed p hp x hx hxs with h | h
                · exact .inl (List.mem_cons_of_mem _ h)
                · rcases List.mem_cons.mp h with rfl | h
                  · exact .inl (List.mem_cons_self ..)
                  · exact .inr (List.mem_append_right _ h) }
        obtain ⟨ho, hw, hd⟩ := collect_ok f h hi'
        refine ⟨ho, fun x hx hxs => ?_, fun p hp => hd p (List.mem_cons_of_mem _ hp)⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact List.mem_map.mpr ⟨_, hd _ (List.mem_cons_self ..), rfl⟩
        · exact hw x (List.mem_append_right _ hx) hxs

theorem collect_unknown : (f : Nat) → {work : List Name} → {done : List (Name × ConstantInfo)} →
    {c : Name} → collect lookup eqn stop f work done = .error (.unknown c) →
    Inv lookup eqn stop roots work done → Reach lookup eqn stop roots c ∧ lookup c = none
  | 0, _, _, _, h, _ => by simp [collect] at h
  | _ + 1, [], _, _, h, _ => by simp [collect] at h
  | f + 1, x :: work, done, c, h, hi => by
    simp only [collect] at h
    split at h
    · next hskip =>
      refine collect_unknown f h
        { found := hi.found, reached := hi.reached
          pending := fun y hy => hi.pending y (List.mem_cons_of_mem _ hy)
          closed := fun p hp y hy hs => by
            rcases hi.closed p hp y hy hs with h | h
            · exact .inl h
            · rcases List.mem_cons.mp h with rfl | h
              · rcases hskip with h' | h'
                · simp [hs] at h'
                · exact .inl h'
              · exact .inr h }
    · next hskip =>
      have hs : stop x = false := by simpa using fun h => hskip (.inl h)
      have hx : Reach lookup eqn stop roots x := hi.pending x (List.mem_cons_self ..) hs
      split at h
      · next hnone =>
        simp only [Except.error.injEq, Gap.unknown.injEq] at h
        subst h
        exact ⟨hx, hnone⟩
      · next ci hci =>
        refine collect_unknown f h
          { found := fun p hp => by
              rcases List.mem_cons.mp hp with rfl | hp
              · exact hci
              · exact hi.found p hp
            reached := fun p hp => by
              rcases List.mem_cons.mp hp with rfl | hp
              · exact hx
              · exact hi.reached p hp
            pending := fun y hy hys => by
              rcases List.mem_append.mp hy with hy | hy
              · exact .step hx hci hy hys
              · exact hi.pending y (List.mem_cons_of_mem _ hy) hys
            closed := fun p hp y hy hys => by
              rcases List.mem_cons.mp hp with rfl | hp
              · exact .inr (List.mem_append_left _ hy)
              · rcases hi.closed p hp y hy hys with h | h
                · exact .inl (List.mem_cons_of_mem _ h)
                · rcases List.mem_cons.mp h with rfl | h
                  · exact .inl (List.mem_cons_self ..)
                  · exact .inr (List.mem_append_right _ h) }

theorem inv_init : Inv lookup eqn stop roots roots [] where
  found := by simp
  reached := by simp
  pending := fun _ hc hs => .root hc hs
  closed := by simp

theorem meaning_ok {out : List (Name × ConstantInfo)} (h : meaning lookup eqn stop roots = .ok out) :
    (∀ p ∈ out, lookup p.1 = some p.2) ∧
      ∀ c, c ∈ out.map Prod.fst ↔ Reach lookup eqn stop roots c := by
  simp only [meaning] at h
  cases hc : collect lookup eqn stop (2 ^ 64) roots [] with
  | error e => simp [hc] at h; cases h
  | ok out' =>
    simp only [hc, Except.map, Except.ok.injEq] at h
    subst h
    obtain ⟨ho, hw, -⟩ := collect_ok (roots := roots) _ hc inv_init
    refine ⟨fun p hp => ho.found p (List.mem_reverse.mp hp), fun c => ?_⟩
    simp only [List.map_reverse, List.mem_reverse]
    refine ⟨fun hm => ?_, fun hr => ?_⟩
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
      exact ho.reached p hp
    · induction hr with
      | root hc hs => exact hw _ hc hs
      | step _ hd hc hs ih =>
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ih
        have := (ho.found p hp).symm.trans hd
        cases this
        simpa using ho.closed p hp _ hc hs

theorem meaning_unknown {c : Name} (h : meaning lookup eqn stop roots = .error (.unknown c)) :
    Reach lookup eqn stop roots c ∧ lookup c = none := by
  simp only [meaning] at h
  cases hc : collect lookup eqn stop (2 ^ 64) roots [] with
  | error e =>
    simp only [hc, Except.map, Except.error.injEq] at h
    subst h
    exact collect_unknown _ hc inv_init
  | ok _ => simp [hc, Except.map] at h

theorem reach_of_mem {out : List (Name × ConstantInfo)} (h : meaning lookup eqn stop roots = .ok out)
    {c : Name} {ci : ConstantInfo} (hp : (c, ci) ∈ out) :
    Reach lookup eqn stop roots c ∧ lookup c = some ci :=
  ⟨((meaning_ok h).2 c).mp (List.mem_map.mpr ⟨_, hp, rfl⟩), (meaning_ok h).1 _ hp⟩

theorem ctor_mem {out : List (Name × ConstantInfo)} (h : meaning lookup eqn stop roots = .ok out)
    {c k : Name} {v : Lean.InductiveVal} (hp : (c, .inductInfo v) ∈ out) (hk : k ∈ v.ctors)
    (hs : stop k = false) : k ∈ out.map Prod.fst :=
  let ⟨hr, hl⟩ := reach_of_mem h hp
  ((meaning_ok h).2 k).mpr (.step hr hl (mem_declRefs_ctor hk) hs)

theorem induct_mem {out : List (Name × ConstantInfo)} (h : meaning lookup eqn stop roots = .ok out)
    {c : Name} {v : Lean.ConstructorVal} (hp : (c, .ctorInfo v) ∈ out)
    (hs : stop v.induct = false) : v.induct ∈ out.map Prod.fst :=
  let ⟨hr, hl⟩ := reach_of_mem h hp
  ((meaning_ok h).2 _).mpr (.step hr hl mem_declRefs_induct hs)

theorem block_mem {out : List (Name × ConstantInfo)} (h : meaning lookup eqn stop roots = .ok out)
    {c i : Name} {v : Lean.RecursorVal} (hp : (c, .recInfo v) ∈ out) (hi : i ∈ v.all)
    (hs : stop i = false) : i ∈ out.map Prod.fst :=
  let ⟨hr, hl⟩ := reach_of_mem h hp
  ((meaning_ok h).2 i).mpr (.step hr hl (mem_declRefs_block hi) hs)

end Proofs

end LeanIntent.Print
