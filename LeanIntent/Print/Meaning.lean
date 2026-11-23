module

public import LeanIntent.Cone

public section

namespace LeanIntent.Print

open Lean (Name ConstantInfo Expr)
open LeanIntent.Cone (declRefs mem_declRefs exprRefs mem_exprRefs Mentions RefersTo)

inductive RefsMode where
  | value
  | eqn (e : Expr)
  | typeOnly

@[expose] def refsVia (eqn : Name → RefsMode) (c : Name) : ConstantInfo → List Name
  | .defnInfo v =>
    match eqn c with
    | .value => declRefs (.defnInfo v)
    | .eqn t => exprRefs v.type (exprRefs t [])
    | .typeOnly => exprRefs v.type []
  | ci => declRefs ci

theorem mem_refsVia_eqn {eqn : Name → RefsMode} {c k : Name} {v : Lean.DefinitionVal} {t : Expr}
    (h : eqn c = .eqn t) : k ∈ refsVia eqn c (.defnInfo v) ↔ Mentions k v.type ∨ Mentions k t := by
  simp [refsVia, h, mem_exprRefs]

theorem mem_refsVia_typeOnly {eqn : Name → RefsMode} {c k : Name} {v : Lean.DefinitionVal}
    (h : eqn c = .typeOnly) : k ∈ refsVia eqn c (.defnInfo v) ↔ Mentions k v.type := by
  simp [refsVia, h, mem_exprRefs]

theorem refsVia_eq_declRefs {eqn : Name → RefsMode} {c : Name} {ci : ConstantInfo}
    (h : eqn c = .value ∨ ∀ v, ci ≠ .defnInfo v) : refsVia eqn c ci = declRefs ci := by
  cases ci with
  | defnInfo v =>
    rcases h with h | h
    · simp [refsVia, h]
    · exact absurd rfl (h v)
  | _ => rfl

theorem mem_declRefs_ctor {eqn : Name → RefsMode} {c : Name} {v : Lean.InductiveVal} {k : Name}
    (h : k ∈ v.ctors) : k ∈ refsVia eqn c (.inductInfo v) :=
  (mem_declRefs (.inductInfo v) k).mpr (Or.inr (Or.inr (Or.inl h)))

theorem mem_declRefs_induct {eqn : Name → RefsMode} {c : Name} {v : Lean.ConstructorVal} :
    v.induct ∈ refsVia eqn c (.ctorInfo v) :=
  (mem_declRefs (.ctorInfo v) v.induct).mpr (Or.inr rfl)

theorem mem_declRefs_block {eqn : Name → RefsMode} {c : Name} {v : Lean.RecursorVal} {i : Name}
    (h : i ∈ v.all) : i ∈ refsVia eqn c (.recInfo v) :=
  (mem_declRefs (.recInfo v) i).mpr (Or.inr (Or.inl h))

inductive Reach (lookup : Name → Option ConstantInfo) (eqn : Name → RefsMode)
    (stop : Name → Bool) (roots : List Name) : Name → Prop where
  | root {c : Name} : c ∈ roots → stop c = false → Reach lookup eqn stop roots c
  | step {d c : Name} {ci : ConstantInfo} : Reach lookup eqn stop roots d → lookup d = some ci →
      c ∈ refsVia eqn d ci → stop c = false → Reach lookup eqn stop roots c

inductive Gap where
  | unknown (c : Name)
  | fuel
  deriving @[expose] Inhabited, Repr, @[expose] DecidableEq

@[expose] def nextActive (stop : Name → Bool) (visited : Std.HashSet Name) :
    List Name → Option (Name × List Name)
  | [] => none
  | c :: rest =>
    if stop c || visited.contains c then nextActive stop visited rest
    else some (c, rest)

@[expose] def collect (lookup : Name → Option ConstantInfo) (eqn : Name → RefsMode)
    (stop : Name → Bool) : Nat → Std.HashSet Name → List Name →
    List (Name × ConstantInfo) → Except Gap (List (Name × ConstantInfo))
  | fuel, visited, work, done =>
    match nextActive stop visited work with
    | none => .ok done
    | some (c, rest) =>
      match lookup c with
      | none => .error (.unknown c)
      | some ci =>
        match fuel with
        | 0 => .error .fuel
        | fuel + 1 =>
          collect lookup eqn stop fuel (visited.insert c) (refsVia eqn c ci ++ rest)
            ((c, ci) :: done)

@[expose] def meaning (lookup : Name → Option ConstantInfo) (eqn : Name → RefsMode)
    (stop : Name → Bool) (fuel : Nat) (roots : List Name) :
    Except Gap (List (Name × ConstantInfo)) :=
  (collect lookup eqn stop fuel ∅ roots []).map List.reverse

@[expose] def Within (lookup : Name → Option ConstantInfo) (eqn : Name → RefsMode)
    (stop : Name → Bool) (roots : List Name) (fuel : Nat) : Prop :=
  ∃ l : List Name, l.length ≤ fuel ∧ ∀ c, Reach lookup eqn stop roots c → c ∈ l

@[expose] def Gap.Holds (lookup : Name → Option ConstantInfo) (eqn : Name → RefsMode)
    (stop : Name → Bool) (roots : List Name) (fuel : Nat) : Gap → Prop
  | .unknown c => Reach lookup eqn stop roots c ∧ lookup c = none
  | .fuel => ¬ Within lookup eqn stop roots fuel

section Proofs

variable {lookup : Name → Option ConstantInfo} {eqn : Name → RefsMode} {stop : Name → Bool}
  {roots : List Name}

theorem nextActive_eq_none {V : Std.HashSet Name} :
    (W : List Name) → nextActive stop V W = none → ∀ w ∈ W, stop w = false → w ∈ V
  | [], _, w, hw, _ => nomatch hw
  | c :: rest, h, w, hw, hs => by
    unfold nextActive at h
    split at h
    · rename_i hc
      rcases List.mem_cons.mp hw with rfl | hw
      · simp only [Bool.or_eq_true, Std.HashSet.contains_iff_mem] at hc
        exact hc.elim (fun h1 => absurd hs (by simp [h1])) id
      · exact nextActive_eq_none rest h w hw hs
    · exact absurd h (by simp)

theorem nextActive_eq_some {V : Std.HashSet Name} {c : Name} {rest : List Name} :
    (W : List Name) → nextActive stop V W = some (c, rest) →
      c ∈ W ∧ stop c = false ∧ c ∉ V ∧ (∀ w ∈ rest, w ∈ W) ∧
        ∀ w ∈ W, stop w = true ∨ w ∈ V ∨ w = c ∨ w ∈ rest
  | [], h => nomatch h
  | d :: ds, h => by
    unfold nextActive at h
    split at h
    · rename_i hd
      obtain ⟨h1, h2, h3, h4, h5⟩ := nextActive_eq_some ds h
      refine ⟨List.mem_cons_of_mem _ h1, h2, h3, fun w hw => List.mem_cons_of_mem _ (h4 w hw), ?_⟩
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · simp only [Bool.or_eq_true, Std.HashSet.contains_iff_mem] at hd
        rcases hd with hst | hv
        · exact .inl hst
        · exact .inr (.inl hv)
      · exact h5 w hw
    · rename_i hd
      cases h
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, Std.HashSet.contains_iff_mem] at hd
      refine ⟨List.mem_cons_self .., hd.1, hd.2, fun w hw => List.mem_cons_of_mem _ hw, ?_⟩
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact .inr (.inr (.inl rfl))
      · exact .inr (.inr (.inr hw))

structure Inv (lookup : Name → Option ConstantInfo) (eqn : Name → RefsMode) (stop : Name → Bool)
    (roots : List Name) (V : Std.HashSet Name) (work : List Name)
    (done : List (Name × ConstantInfo)) : Prop where
  found : ∀ p ∈ done, lookup p.1 = some p.2
  reached : ∀ p ∈ done, Reach lookup eqn stop roots p.1
  visited_mem : ∀ v ∈ V, v ∈ done.map Prod.fst
  mem_visited : ∀ p ∈ done, p.1 ∈ V
  pending : ∀ c ∈ work, stop c = false → Reach lookup eqn stop roots c
  closed : ∀ p ∈ done, ∀ c ∈ refsVia eqn p.1 p.2, stop c = false →
    c ∈ done.map Prod.fst ∨ c ∈ work

theorem collect_ok : (f : Nat) → {V : Std.HashSet Name} → {work : List Name} →
    {done out : List (Name × ConstantInfo)} →
    collect lookup eqn stop f V work done = .ok out → Inv lookup eqn stop roots V work done →
    ∃ V' : Std.HashSet Name, Inv lookup eqn stop roots V' [] out ∧ V'.size ≤ V.size + f ∧
      (∀ c ∈ work, stop c = false → c ∈ out.map Prod.fst) ∧ ∀ p ∈ done, p ∈ out
  | f, V, work, done, out, h, hi => by
    unfold collect at h
    split at h
    · rename_i hn
      simp only [Except.ok.injEq] at h
      subst h
      have hW := nextActive_eq_none work hn
      refine ⟨V, { hi with pending := by simp, closed := fun p hp c hc hs => ?_ },
        Nat.le_add_right _ _, fun c hc hs => hi.visited_mem c (hW c hc hs), fun _ hp => hp⟩
      rcases hi.closed p hp c hc hs with h' | h'
      · exact .inl h'
      · exact .inl (hi.visited_mem c (hW c h' hs))
    · rename_i c rest hn
      obtain ⟨hcW, hsc, hcV, hrest, hsplit⟩ := nextActive_eq_some work hn
      split at h
      · simp at h
      · rename_i ci hci
        cases f with
        | zero => simp at h
        | succ f =>
          have hc : Reach lookup eqn stop roots c := hi.pending c hcW hsc
          have hi' : Inv lookup eqn stop roots (V.insert c) (refsVia eqn c ci ++ rest)
              ((c, ci) :: done) :=
            { found := fun p hp => by
                rcases List.mem_cons.mp hp with rfl | hp
                · exact hci
                · exact hi.found p hp
              reached := fun p hp => by
                rcases List.mem_cons.mp hp with rfl | hp
                · exact hc
                · exact hi.reached p hp
              visited_mem := fun v hv => by
                rcases Cone.mem_insert.mp hv with rfl | hv
                · exact List.mem_cons_self ..
                · exact List.mem_cons_of_mem _ (hi.visited_mem v hv)
              mem_visited := fun p hp => by
                rcases List.mem_cons.mp hp with rfl | hp
                · exact Cone.mem_insert.mpr (.inl rfl)
                · exact Cone.mem_insert.mpr (.inr (hi.mem_visited p hp))
              pending := fun x hx hxs => by
                rcases List.mem_append.mp hx with hx | hx
                · exact .step hc hci hx hxs
                · exact hi.pending x (hrest x hx) hxs
              closed := fun p hp x hx hxs => by
                rcases List.mem_cons.mp hp with rfl | hp
                · exact .inr (List.mem_append_left _ hx)
                · rcases hi.closed p hp x hx hxs with h' | h'
                  · exact .inl (List.mem_cons_of_mem _ h')
                  · rcases hsplit x h' with hst | hxv | rfl | hxr
                    · simp [hxs] at hst
                    · exact .inl (List.mem_cons_of_mem _ (hi.visited_mem x hxv))
                    · exact .inl (List.mem_cons_self ..)
                    · exact .inr (List.mem_append_right _ hxr) }
          obtain ⟨V', ho, hsize, hw, hd⟩ := collect_ok f h hi'
          refine ⟨V', ho, ?_, fun x hx hxs => ?_, fun p hp => hd p (List.mem_cons_of_mem _ hp)⟩
          · rw [Cone.size_insert_of_not_mem hcV] at hsize
            omega
          · rcases hsplit x hx with hst | hxv | rfl | hxr
            · simp [hxs] at hst
            · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (hi.visited_mem x hxv)
              exact List.mem_map.mpr ⟨p, hd p (List.mem_cons_of_mem _ hp), rfl⟩
            · exact List.mem_map.mpr ⟨_, hd _ (List.mem_cons_self ..), rfl⟩
            · exact hw x (List.mem_append_right _ hxr) hxs

theorem collect_error (fuel₀ : Nat) : (f : Nat) → (V : Std.HashSet Name) →
    (work : List Name) → (done : List (Name × ConstantInfo)) →
    (∀ v ∈ V, Reach lookup eqn stop roots v) →
    (∀ w ∈ work, stop w = false → Reach lookup eqn stop roots w) →
    V.size + f = fuel₀ → ∀ {g : Gap},
    collect lookup eqn stop f V work done = .error g →
    g.Holds lookup eqn stop roots fuel₀
  | f, V, work, done, hV, hW, hfuel, g, h => by
    unfold collect at h
    split at h
    · exact nomatch h
    · rename_i c rest hn
      obtain ⟨hcW, hsc, hcV, hrest, -⟩ := nextActive_eq_some work hn
      have hc : Reach lookup eqn stop roots c := hW c hcW hsc
      split at h
      · rename_i hnone
        cases h
        exact ⟨hc, hnone⟩
      · rename_i ci hci
        cases f with
        | zero =>
          cases h
          rintro ⟨l, hlen, hlc⟩
          have := Cone.size_lt_length (fun v hv => hlc v (hV v hv)) hcV (hlc c hc)
          omega
        | succ f =>
          refine collect_error fuel₀ f (V.insert c) (refsVia eqn c ci ++ rest) ((c, ci) :: done)
            ?_ ?_ ?_ h
          · intro v hv
            rcases Cone.mem_insert.mp hv with rfl | hv
            · exact hc
            · exact hV v hv
          · intro w hw hws
            rcases List.mem_append.mp hw with hw | hw
            · exact .step hc hci hw hws
            · exact hW w (hrest w hw) hws
          · rw [Cone.size_insert_of_not_mem hcV]
            omega

theorem collect_unknown : (f : Nat) → {V : Std.HashSet Name} → {work : List Name} →
    {done : List (Name × ConstantInfo)} → {c : Name} →
    collect lookup eqn stop f V work done = .error (.unknown c) →
    Inv lookup eqn stop roots V work done → Reach lookup eqn stop roots c ∧ lookup c = none := by
  intro f V work done c h hi
  exact collect_error (V.size + f) f V work done
    (fun v hv => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (hi.visited_mem v hv)
      exact hi.reached p hp)
    hi.pending rfl h

theorem inv_init : Inv lookup eqn stop roots ∅ roots [] where
  found := by simp
  reached := by simp
  visited_mem := fun _ h => absurd h Std.HashSet.not_mem_empty
  mem_visited := by simp
  pending := fun _ hc hs => .root hc hs
  closed := by simp

theorem meaning_ok {fuel : Nat} {out : List (Name × ConstantInfo)}
    (h : meaning lookup eqn stop fuel roots = .ok out) :
    (∀ p ∈ out, lookup p.1 = some p.2) ∧
      ∀ c, c ∈ out.map Prod.fst ↔ Reach lookup eqn stop roots c := by
  simp only [meaning] at h
  cases hc : collect lookup eqn stop fuel ∅ roots [] with
  | error e => simp [hc] at h; cases h
  | ok out' =>
    simp only [hc, Except.map, Except.ok.injEq] at h
    subst h
    obtain ⟨_, ho, -, hw, -⟩ := collect_ok (roots := roots) fuel hc inv_init
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

theorem meaning_within {fuel : Nat} {out : List (Name × ConstantInfo)}
    (h : meaning lookup eqn stop fuel roots = .ok out) :
    Within lookup eqn stop roots fuel := by
  have hm := (meaning_ok h).2
  simp only [meaning] at h
  cases hc : collect lookup eqn stop fuel ∅ roots [] with
  | error e => simp [hc] at h; cases h
  | ok out' =>
    simp only [hc, Except.map, Except.ok.injEq] at h
    subst h
    obtain ⟨V', ho, hsize, -, -⟩ := collect_ok (roots := roots) fuel hc inv_init
    have hreach : ∀ c, Reach lookup eqn stop roots c → c ∈ V' := by
      intro c hrc
      have hmem : c ∈ out'.reverse.map Prod.fst := (hm c).mpr hrc
      simp only [List.map_reverse, List.mem_reverse, List.mem_map] at hmem
      obtain ⟨p, hp, rfl⟩ := hmem
      exact ho.mem_visited p hp
    exact ⟨V'.toList, by simpa [Std.HashSet.length_toList] using hsize,
      fun c hrc => Std.HashSet.mem_toList.mpr (hreach c hrc)⟩

theorem meaning_error {fuel : Nat} {g : Gap}
    (h : meaning lookup eqn stop fuel roots = .error g) :
    g.Holds lookup eqn stop roots fuel := by
  simp only [meaning] at h
  cases hc : collect lookup eqn stop fuel ∅ roots [] with
  | error e =>
    simp only [hc, Except.map, Except.error.injEq] at h
    subst h
    exact collect_error fuel fuel ∅ roots [] (fun _ hv => absurd hv Std.HashSet.not_mem_empty)
      (fun _ hw hs => .root hw hs) (by simp) hc
  | ok _ => simp [hc, Except.map] at h

theorem meaning_unknown {fuel : Nat} {c : Name}
    (h : meaning lookup eqn stop fuel roots = .error (.unknown c)) :
    Reach lookup eqn stop roots c ∧ lookup c = none :=
  meaning_error h

theorem meaning_fuel {fuel : Nat}
    (h : meaning lookup eqn stop fuel roots = .error .fuel) :
    ¬ Within lookup eqn stop roots fuel :=
  meaning_error h

theorem meaning_ok_iff {fuel : Nat} :
    (∃ out, meaning lookup eqn stop fuel roots = .ok out) ↔
      (∀ c, Reach lookup eqn stop roots c → (lookup c).isSome) ∧
        Within lookup eqn stop roots fuel := by
  constructor
  · rintro ⟨out, h⟩
    refine ⟨fun c hc => ?_, meaning_within h⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (((meaning_ok h).2 c).mpr hc)
    simp [(meaning_ok h).1 p hp]
  · rintro ⟨hAll, hw⟩
    cases hm : meaning lookup eqn stop fuel roots with
    | ok out => exact ⟨out, rfl⟩
    | error g =>
      cases g with
      | unknown c =>
        obtain ⟨hc, hnone⟩ := meaning_unknown hm
        have hsome := hAll c hc
        simp [hnone] at hsome
      | fuel => exact absurd hw (meaning_fuel hm)

theorem reach_of_mem {fuel : Nat} {out : List (Name × ConstantInfo)}
    (h : meaning lookup eqn stop fuel roots = .ok out)
    {c : Name} {ci : ConstantInfo} (hp : (c, ci) ∈ out) :
    Reach lookup eqn stop roots c ∧ lookup c = some ci :=
  ⟨((meaning_ok h).2 c).mp (List.mem_map.mpr ⟨_, hp, rfl⟩), (meaning_ok h).1 _ hp⟩

theorem ctor_mem {fuel : Nat} {out : List (Name × ConstantInfo)}
    (h : meaning lookup eqn stop fuel roots = .ok out)
    {c k : Name} {v : Lean.InductiveVal} (hp : (c, .inductInfo v) ∈ out) (hk : k ∈ v.ctors)
    (hs : stop k = false) : k ∈ out.map Prod.fst :=
  let ⟨hr, hl⟩ := reach_of_mem h hp
  ((meaning_ok h).2 k).mpr (.step hr hl (mem_declRefs_ctor hk) hs)

theorem induct_mem {fuel : Nat} {out : List (Name × ConstantInfo)}
    (h : meaning lookup eqn stop fuel roots = .ok out)
    {c : Name} {v : Lean.ConstructorVal} (hp : (c, .ctorInfo v) ∈ out)
    (hs : stop v.induct = false) : v.induct ∈ out.map Prod.fst :=
  let ⟨hr, hl⟩ := reach_of_mem h hp
  ((meaning_ok h).2 _).mpr (.step hr hl mem_declRefs_induct hs)

theorem block_mem {fuel : Nat} {out : List (Name × ConstantInfo)}
    (h : meaning lookup eqn stop fuel roots = .ok out)
    {c i : Name} {v : Lean.RecursorVal} (hp : (c, .recInfo v) ∈ out) (hi : i ∈ v.all)
    (hs : stop i = false) : i ∈ out.map Prod.fst :=
  let ⟨hr, hl⟩ := reach_of_mem h hp
  ((meaning_ok h).2 i).mpr (.step hr hl (mem_declRefs_block hi) hs)

end Proofs

end LeanIntent.Print
