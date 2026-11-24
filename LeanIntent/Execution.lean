module

public import LeanIntent.Implementation
public import LeanIntent.Cone

public section

namespace LeanIntent

universe u

structure Runs {W : Type u} (d : Deliverable W) where
  executable : Lean.Name

namespace Execution

open Lean (Name)

inductive Reaches (refs : Name → List Name) (root : Name) : Name → Prop where
  | root : Reaches refs root root
  | step {c d : Name} : Reaches refs root c → d ∈ refs c → Reaches refs root d

inductive Outcome where
  | reached
  | unreached
  | exhausted
  deriving @[expose] DecidableEq, Repr

@[expose] def search (refs : Name → List Name) (target : Name) :
    Nat → Std.HashSet Name → List Name → Outcome
  | fuel, visited, work =>
    match Cone.nextNew visited work with
    | none => .unreached
    | some (c, rest) =>
      if c == target then .reached else
        match fuel with
        | 0 => .exhausted
        | fuel + 1 => search refs target fuel (visited.insert c) (refs c ++ rest)

@[expose] def reach (refs : Name → List Name) (root target : Name) (fuel : Nat) : Outcome :=
  search refs target fuel ∅ [root]

@[expose] def Within (refs : Name → List Name) (root : Name) (fuel : Nat) : Prop :=
  ∃ l : List Name, l.length ≤ fuel ∧ ∀ c, Reaches refs root c → c ∈ l

@[expose] def prune (refs : Name → List Name) (keep : Name → Bool) (c : Name) : List Name :=
  if keep c then refs c else []

section Reach

variable {refs : Name → List Name} {root target : Name}

theorem search_reached : (fuel : Nat) → (V : Std.HashSet Name) → (W : List Name) →
    (∀ w ∈ W, Reaches refs root w) → search refs target fuel V W = .reached →
    Reaches refs root target
  | fuel, V, W, hW, h => by
    unfold search at h
    split at h
    · exact nomatch h
    · rename_i c rest hn
      obtain ⟨hcW, -, hrest, -⟩ := Cone.nextNew_eq_some W hn
      split at h
      · rename_i hc
        exact (beq_iff_eq.mp hc) ▸ hW c hcW
      · cases fuel with
        | zero => exact nomatch h
        | succ fuel =>
          refine search_reached fuel _ _ (fun w hw => ?_) h
          rcases List.mem_append.mp hw with hw | hw
          · exact .step (hW c hcW) hw
          · exact hW w (hrest w hw)

theorem search_unreached : (fuel : Nat) → (V : Std.HashSet Name) → (W : List Name) →
    target ∉ V → (root ∈ V ∨ root ∈ W) → (∀ v ∈ V, ∀ d ∈ refs v, d ∈ V ∨ d ∈ W) →
    search refs target fuel V W = .unreached → ¬ Reaches refs root target
  | fuel, V, W, ht, hr, hcl, h => by
    unfold search at h
    split at h
    · rename_i hn
      have hW := Cone.nextNew_eq_none W hn
      have closed : ∀ c, Reaches refs root c → c ∈ V := by
        intro c hc
        induction hc with
        | root => exact hr.elim id (hW _)
        | step _ hd ih => exact (hcl _ ih _ hd).elim id (hW _)
      exact fun hreach => ht (closed _ hreach)
    · rename_i c rest hn
      obtain ⟨-, -, -, hWsplit⟩ := Cone.nextNew_eq_some W hn
      have hmove : ∀ w ∈ W, w ∈ V.insert c ∨ w ∈ refs c ++ rest := fun w hw =>
        match hWsplit w hw with
        | .inl h' => .inl (Cone.mem_insert.mpr (.inr h'))
        | .inr (.inl h') => .inl (Cone.mem_insert.mpr (.inl h'))
        | .inr (.inr h') => .inr (List.mem_append_right _ h')
      split at h
      · exact nomatch h
      · rename_i hct
        cases fuel with
        | zero => exact nomatch h
        | succ fuel =>
          refine search_unreached fuel (V.insert c) (refs c ++ rest) ?_ ?_ ?_ h
          · intro hm
            rcases Cone.mem_insert.mp hm with rfl | hm
            · exact hct (beq_self_eq_true _)
            · exact ht hm
          · rcases hr with hr | hr
            · exact .inl (Cone.mem_insert.mpr (.inr hr))
            · exact hmove _ hr
          · intro v hv d hd
            rcases Cone.mem_insert.mp hv with rfl | hv
            · exact .inr (List.mem_append_left _ hd)
            · rcases hcl v hv d hd with h' | h'
              · exact .inl (Cone.mem_insert.mpr (.inr h'))
              · exact hmove _ h'

theorem search_exhausted (fuel₀ : Nat) : (fuel : Nat) → (V : Std.HashSet Name) →
    (W : List Name) → (∀ v ∈ V, Reaches refs root v) → (∀ w ∈ W, Reaches refs root w) →
    V.size + fuel = fuel₀ → search refs target fuel V W = .exhausted → ¬ Within refs root fuel₀
  | fuel, V, W, hV, hW, hfuel, h => by
    unfold search at h
    split at h
    · exact nomatch h
    · rename_i c rest hn
      obtain ⟨hcW, hcV, hrest, -⟩ := Cone.nextNew_eq_some W hn
      have hc := hW c hcW
      split at h
      · exact nomatch h
      · cases fuel with
        | zero =>
          rintro ⟨l, hlen, hl⟩
          have := Cone.size_lt_length (fun v hv' => hl v (hV v hv')) hcV (hl c hc)
          omega
        | succ fuel =>
          refine search_exhausted fuel₀ fuel (V.insert c) (refs c ++ rest) ?_ ?_ ?_ h
          · intro v hv'
            rcases Cone.mem_insert.mp hv' with rfl | hv'
            · exact hc
            · exact hV v hv'
          · intro w hw
            rcases List.mem_append.mp hw with hw | hw
            · exact .step hc hw
            · exact hW w (hrest w hw)
          · rw [Cone.size_insert_of_not_mem hcV]
            omega

theorem reach_reached {fuel : Nat} (h : reach refs root target fuel = .reached) :
    Reaches refs root target :=
  search_reached fuel ∅ [root] (fun _ hw => List.mem_singleton.mp hw ▸ .root) h

theorem reach_unreached {fuel : Nat} (h : reach refs root target fuel = .unreached) :
    ¬ Reaches refs root target :=
  search_unreached fuel ∅ [root] Std.HashSet.not_mem_empty (.inr (List.mem_singleton_self _))
    (fun _ hv => absurd hv Std.HashSet.not_mem_empty) h

theorem reach_exhausted {fuel : Nat} (h : reach refs root target fuel = .exhausted) :
    ¬ Within refs root fuel :=
  search_exhausted fuel fuel ∅ [root] (fun _ hv => absurd hv Std.HashSet.not_mem_empty)
    (fun _ hw => List.mem_singleton.mp hw ▸ .root) (by simp) h

theorem reach_eq_reached_iff {fuel : Nat} (hw : Within refs root fuel) :
    reach refs root target fuel = .reached ↔ Reaches refs root target := by
  constructor
  · exact reach_reached
  · intro hr
    cases h : reach refs root target fuel with
    | reached => rfl
    | unreached => exact absurd hr (reach_unreached h)
    | exhausted => exact absurd hw (reach_exhausted h)

theorem reaches_prune_iff {keep : Name → Bool}
    (hkeep : ∀ c d, d ∈ refs c → keep d = true → keep c = true) (ht : keep target = true) :
    Reaches (prune refs keep) root target ↔ Reaches refs root target := by
  constructor
  · intro h
    clear ht
    induction h with
    | root => exact .root
    | step _ hd ih =>
      unfold prune at hd
      split at hd
      · exact .step ih hd
      · exact absurd hd List.not_mem_nil
  · intro h
    suffices ∀ c, Reaches refs root c → keep c = true → Reaches (prune refs keep) root c from
      this target h ht
    intro c hc
    induction hc with
    | root => exact fun _ => .root
    | step _ hd ih =>
      intro hk
      have hkc := hkeep _ _ hd hk
      exact .step (ih hkc) (by simp [prune, hkc, hd])

end Reach

open Implementation (Constant)

structure Executable where
  name : Name
  root : Name
  entry : Bool
  reaches : List Constant
  deriving @[expose] DecidableEq, Repr

structure Claim where
  name : Name
  deliverable : Option Name
  executable : Name
  deriving @[expose] DecidableEq, Repr

inductive Finding where
  | noDeliverable
  | untied (claim : Name)
  | unknownExecutable (claim : Name) (executable : Name)
  | noEntryPoint (executable : Name) (root : Name)
  | unimplemented (deliverable : Name) (executable : Name)
  | unreached (deliverable : Name) (executable : Name) (implementation : Constant)
  deriving @[expose] DecidableEq, Repr

@[expose] def named (es : List Executable) (x : Name) : List Executable :=
  es.filter (·.name == x)

@[expose] def implementationsOf (is : List (Name × Constant)) (d : Name) : List Constant :=
  is.filterMap fun p => if p.1 == d then some p.2 else none

@[expose] def missing (es : List Executable) (x : Name) (c : Constant) : List Executable :=
  (named es x).filter fun e => e.entry && !e.reaches.contains c

@[expose] def claimFindings (ds : List Name) (is : List (Name × Constant)) (as : List Name)
    (es : List Executable) (cl : Claim) : List Finding :=
  match cl.deliverable with
  | none => [.untied cl.name]
  | some d =>
    if d ∉ ds then [.untied cl.name]
    else if named es cl.executable = [] then [.unknownExecutable cl.name cl.executable]
    else if d ∈ as then []
    else if implementationsOf is d = [] then [.unimplemented d cl.executable]
    else (implementationsOf is d).flatMap fun c =>
      (missing es cl.executable c).map fun _ => .unreached d cl.executable c

@[expose] def exeFindings (e : Executable) : List Finding :=
  if e.entry then [] else [.noEntryPoint e.name e.root]

@[expose] def findings (ds : List Name) (is : List (Name × Constant)) (as : List Name)
    (es : List Executable) (cls : List Claim) : List Finding :=
  (if ds = [] then [.noDeliverable] else []) ++ es.flatMap exeFindings ++
    cls.flatMap (claimFindings ds is as es)

@[expose] def Accounted (ds : List Name) (is : List (Name × Constant)) (as : List Name)
    (es : List Executable) (cls : List Claim) : Prop :=
  ds ≠ [] ∧ (∀ e ∈ es, e.entry = true) ∧
    ∀ cl ∈ cls, ∃ d, cl.deliverable = some d ∧ d ∈ ds ∧ (∃ e ∈ es, e.name = cl.executable) ∧
      (d ∈ as ∨ ((∃ c, (d, c) ∈ is) ∧
        ∀ c, (d, c) ∈ is → ∀ e ∈ es, e.name = cl.executable → c ∈ e.reaches))

@[expose] def claimReached (ds : List Name) (is : List (Name × Constant)) (as : List Name)
    (es : List Executable) (cl : Claim) : List (Name × Name × Constant) :=
  match cl.deliverable with
  | none => []
  | some d =>
    if d ∈ ds ∧ d ∉ as then
      (implementationsOf is d).flatMap fun c =>
        ((named es cl.executable).filter fun e => e.entry && e.reaches.contains c).map
          fun _ => (d, cl.executable, c)
    else []

@[expose] def claimAwaiting (ds : List Name) (as : List Name) (cl : Claim) : Option (Name × Name) :=
  match cl.deliverable with
  | none => none
  | some d => if d ∈ ds ∧ d ∈ as then some (d, cl.executable) else none

structure Report where
  findings : List Finding
  reached : List (Name × Name × Constant)
  awaiting : List (Name × Name)
  notRun : List Name
  idle : List Name
  deriving Repr

@[expose] def report (ds : List Name) (is : List (Name × Constant)) (as : List Name)
    (es : List Executable) (cls : List Claim) : Report :=
  ⟨findings ds is as es cls, cls.flatMap (claimReached ds is as es),
    cls.filterMap (claimAwaiting ds as),
    ds.filter fun d => !cls.any (·.deliverable == some d),
    (es.filter fun e => !cls.any (·.executable == e.name)).map (·.name)⟩

section Decides

variable {ds : List Name} {is : List (Name × Constant)} {as : List Name} {es : List Executable}
  {cls : List Claim}

theorem mem_named {x : Name} {e : Executable} : e ∈ named es x ↔ e ∈ es ∧ e.name = x := by
  simp [named]

theorem named_eq_nil_iff {x : Name} : named es x = [] ↔ ¬ ∃ e ∈ es, e.name = x := by
  simp [named, List.filter_eq_nil_iff]

theorem mem_implementationsOf {d : Name} {c : Constant} :
    c ∈ implementationsOf is d ↔ (d, c) ∈ is := by
  simp only [implementationsOf, List.mem_filterMap]
  constructor
  · rintro ⟨⟨d', c'⟩, hp, h⟩
    by_cases hd : d' = d
    · subst hd
      simp only [beq_self_eq_true, ite_true, Option.some.injEq] at h
      exact h ▸ hp
    · simp [hd] at h
  · intro h
    exact ⟨(d, c), h, by simp⟩

theorem implementationsOf_eq_nil_iff {d : Name} :
    implementationsOf is d = [] ↔ ∀ c, (d, c) ∉ is := by
  rw [List.eq_nil_iff_forall_not_mem]
  exact forall_congr' fun _ => not_congr mem_implementationsOf

theorem missing_eq_nil_iff {x : Name} {c : Constant} :
    missing es x c = [] ↔ ∀ e ∈ es, e.name = x → e.entry = true → c ∈ e.reaches := by
  simp only [missing, List.filter_eq_nil_iff, mem_named, and_imp]
  refine forall_congr' fun e => forall_congr' fun _ => forall_congr' fun _ => ?_
  cases hen : e.entry <;> by_cases hc : c ∈ e.reaches <;> simp [hc]

theorem claimFindings_eq_nil_iff {cl : Claim} :
    claimFindings ds is as es cl = [] ↔
      ∃ d, cl.deliverable = some d ∧ d ∈ ds ∧ (∃ e ∈ es, e.name = cl.executable) ∧
        (d ∈ as ∨ ((∃ c, (d, c) ∈ is) ∧
          ∀ c, (d, c) ∈ is → ∀ e ∈ es, e.name = cl.executable → e.entry = true →
            c ∈ e.reaches)) := by
  unfold claimFindings
  cases hcl : cl.deliverable with
  | none => simp
  | some d =>
    simp only [Option.some.injEq, exists_eq_left']
    by_cases hd : d ∈ ds
    · simp only [hd, not_true_eq_false, ↓reduceIte, true_and]
      by_cases hx : named es cl.executable = []
      · simp only [hx, ↓reduceIte, reduceCtorEq, false_iff, not_and]
        exact fun h => absurd h (named_eq_nil_iff.mp hx)
      · have hx' : ∃ e ∈ es, e.name = cl.executable := by
          simpa [named_eq_nil_iff] using hx
        simp only [hx, ↓reduceIte, hx', true_and]
        by_cases ha : d ∈ as
        · simp [ha]
        · simp only [ha, ↓reduceIte, false_or]
          by_cases hi : implementationsOf is d = []
          · simp only [hi, ↓reduceIte, reduceCtorEq, false_iff, not_and]
            exact fun ⟨c, hc⟩ => absurd hc (implementationsOf_eq_nil_iff.mp hi c)
          · have hi' : ∃ c, (d, c) ∈ is := by
              simpa [implementationsOf_eq_nil_iff] using hi
            simp only [hi, ↓reduceIte, List.flatMap_eq_nil_iff, List.map_eq_nil_iff,
              missing_eq_nil_iff, mem_implementationsOf]
            exact ⟨fun h => ⟨hi', h⟩, fun h => h.2⟩
    · simp [hd]

theorem findings_eq_nil_iff : findings ds is as es cls = [] ↔ Accounted ds is as es cls := by
  have hexe : ∀ e : Executable, exeFindings e = [] ↔ e.entry = true := by
    intro e; unfold exeFindings; cases e.entry <;> simp
  unfold findings Accounted
  simp only [List.append_eq_nil_iff, List.flatMap_eq_nil_iff, claimFindings_eq_nil_iff, hexe]
  constructor
  · rintro ⟨⟨hds, hen⟩, hcl⟩
    refine ⟨by simpa using hds, hen, fun cl hc => ?_⟩
    obtain ⟨d, hdl, hd, hx, h⟩ := hcl cl hc
    exact ⟨d, hdl, hd, hx, h.imp id fun ⟨hi, hr⟩ =>
      ⟨hi, fun c hc e he hn => hr c hc e he hn (hen e he)⟩⟩
  · rintro ⟨hds, hen, hcl⟩
    refine ⟨⟨by simpa using hds, hen⟩, fun cl hc => ?_⟩
    obtain ⟨d, hdl, hd, hx, h⟩ := hcl cl hc
    exact ⟨d, hdl, hd, hx, h.imp id fun ⟨hi, hr⟩ => ⟨hi, fun c hc e he hn _ => hr c hc e he hn⟩⟩

@[expose] def Finding.Holds (ds : List Name) (is : List (Name × Constant)) (as : List Name)
    (es : List Executable) (cls : List Claim) : Finding → Prop
  | .noDeliverable => ds = []
  | .untied n => ∃ cl ∈ cls, cl.name = n ∧ ∀ d ∈ ds, cl.deliverable ≠ some d
  | .unknownExecutable n x => ∃ cl ∈ cls, cl.name = n ∧ cl.executable = x ∧ ∀ e ∈ es, e.name ≠ x
  | .noEntryPoint x r => ∃ e ∈ es, e.name = x ∧ e.root = r ∧ e.entry = false
  | .unimplemented d x =>
    ∃ cl ∈ cls, cl.deliverable = some d ∧ cl.executable = x ∧ d ∈ ds ∧ d ∉ as ∧ ∀ c, (d, c) ∉ is
  | .unreached d x c =>
    ∃ cl ∈ cls, cl.deliverable = some d ∧ cl.executable = x ∧ d ∈ ds ∧ d ∉ as ∧ (d, c) ∈ is ∧
      ∃ e ∈ es, e.name = x ∧ e.entry = true ∧ c ∉ e.reaches

theorem claimFindings_sound {cl : Claim} (hc : cl ∈ cls) {f : Finding}
    (hf : f ∈ claimFindings ds is as es cl) : f.Holds ds is as es cls := by
  unfold claimFindings at hf
  cases hcl : cl.deliverable with
  | none =>
    rw [hcl] at hf
    rw [List.mem_singleton.mp hf]
    exact ⟨cl, hc, rfl, fun d _ h => by simp [hcl] at h⟩
  | some d =>
    rw [hcl] at hf
    simp only at hf
    split at hf
    · rename_i hd
      rw [List.mem_singleton.mp hf]
      exact ⟨cl, hc, rfl, fun d' hd' h => hd (by rw [hcl] at h; cases h; exact hd')⟩
    · rename_i hd
      split at hf
      · rename_i hx
        rw [List.mem_singleton.mp hf]
        exact ⟨cl, hc, rfl, rfl, fun e he hn => named_eq_nil_iff.mp hx ⟨e, he, hn⟩⟩
      · split at hf
        · exact absurd hf List.not_mem_nil
        · rename_i ha
          split at hf
          · rename_i hi
            rw [List.mem_singleton.mp hf]
            exact ⟨cl, hc, hcl, rfl, Classical.not_not.mp hd, ha,
              implementationsOf_eq_nil_iff.mp hi⟩
          · simp only [List.mem_flatMap, List.mem_map] at hf
            obtain ⟨c, hci, e, he, rfl⟩ := hf
            simp only [missing, List.mem_filter, mem_named, Bool.and_eq_true,
              Bool.not_eq_true'] at he
            obtain ⟨⟨hes, hen⟩, hent, hr⟩ := he
            exact ⟨cl, hc, hcl, rfl, Classical.not_not.mp hd, ha, mem_implementationsOf.mp hci, e,
              hes, hen, hent, by simpa using hr⟩

theorem findings_sound {f : Finding} (hf : f ∈ findings ds is as es cls) :
    f.Holds ds is as es cls := by
  unfold findings at hf
  simp only [List.mem_append, List.mem_flatMap] at hf
  rcases hf with (hf | ⟨e, he, hf⟩) | ⟨cl, hc, hf⟩
  · split at hf
    · rename_i h
      rw [List.mem_singleton.mp hf]
      exact h
    · exact absurd hf List.not_mem_nil
  · unfold exeFindings at hf
    split at hf
    · exact absurd hf List.not_mem_nil
    · rename_i h
      rw [List.mem_singleton.mp hf]
      exact ⟨e, he, rfl, rfl, by simpa using h⟩
  · exact claimFindings_sound hc hf

theorem mem_reached {d x : Name} {c : Constant} :
    (d, x, c) ∈ (report ds is as es cls).reached ↔
      ∃ cl ∈ cls, cl.deliverable = some d ∧ cl.executable = x ∧ d ∈ ds ∧ d ∉ as ∧ (d, c) ∈ is ∧
        ∃ e ∈ es, e.name = x ∧ e.entry = true ∧ c ∈ e.reaches := by
  simp only [report, List.mem_flatMap]
  refine exists_congr fun cl => and_congr_right fun _ => ?_
  unfold claimReached
  cases hcl : cl.deliverable with
  | none => simp
  | some d' =>
    simp only [Option.some.injEq]
    split
    · rename_i h
      simp only [List.mem_flatMap, List.mem_map, List.mem_filter, mem_named, Bool.and_eq_true,
        List.contains_iff_mem, mem_implementationsOf, Prod.mk.injEq]
      constructor
      · rintro ⟨c', hc', e, ⟨⟨he, hn⟩, hen, hr⟩, rfl, rfl, rfl⟩
        exact ⟨rfl, rfl, h.1, h.2, hc', e, he, hn, hen, hr⟩
      · rintro ⟨rfl, rfl, -, -, hc', e, he, hn, hen, hr⟩
        exact ⟨c, hc', e, ⟨⟨he, hn⟩, hen, hr⟩, rfl, rfl, rfl⟩
    · rename_i h
      simp only [List.not_mem_nil, false_iff]
      rintro ⟨rfl, -, hd, ha, -⟩
      exact h ⟨hd, ha⟩

theorem mem_awaiting {d x : Name} :
    (d, x) ∈ (report ds is as es cls).awaiting ↔
      ∃ cl ∈ cls, cl.deliverable = some d ∧ cl.executable = x ∧ d ∈ ds ∧ d ∈ as := by
  simp only [report, List.mem_filterMap]
  refine exists_congr fun cl => and_congr_right fun _ => ?_
  unfold claimAwaiting
  cases cl.deliverable with
  | none => simp
  | some d' =>
    simp only [Option.some.injEq]
    split
    · rename_i h
      simp only [Option.some.injEq, Prod.mk.injEq]
      constructor
      · rintro ⟨rfl, rfl⟩
        exact ⟨rfl, rfl, h⟩
      · rintro ⟨rfl, rfl, -⟩
        exact ⟨rfl, rfl⟩
    · rename_i h
      simp only [reduceCtorEq, false_iff]
      rintro ⟨rfl, -, hd, ha⟩
      exact h ⟨hd, ha⟩

theorem mem_notRun {d : Name} :
    d ∈ (report ds is as es cls).notRun ↔ d ∈ ds ∧ ∀ cl ∈ cls, cl.deliverable ≠ some d := by
  simp [report]

theorem mem_idle {x : Name} :
    x ∈ (report ds is as es cls).idle ↔ ∃ e ∈ es, e.name = x ∧ ∀ cl ∈ cls, cl.executable ≠ x := by
  simp only [report, List.mem_map, List.mem_filter, Bool.not_eq_true', List.any_eq_false,
    beq_iff_eq]
  constructor
  · rintro ⟨e, ⟨he, hn⟩, rfl⟩
    exact ⟨e, he, rfl, fun cl hc h => hn cl hc h⟩
  · rintro ⟨e, he, rfl, hn⟩
    exact ⟨e, ⟨he, fun cl hc h => hn cl hc h⟩, rfl⟩

theorem listed_of_nil (h : findings ds is as es cls = []) {cl : Claim} (hc : cl ∈ cls) :
    ∃ d ∈ ds, cl.deliverable = some d ∧
      ((d ∈ as ∧ (d, cl.executable) ∈ (report ds is as es cls).awaiting) ∨
        (d ∉ as ∧
          ∀ c, (d, c) ∈ is → (d, cl.executable, c) ∈ (report ds is as es cls).reached)) := by
  obtain ⟨-, hen, hcl⟩ := findings_eq_nil_iff.mp h
  obtain ⟨d, hdl, hd, ⟨e, he, hn⟩, hr⟩ := hcl cl hc
  refine ⟨d, hd, hdl, ?_⟩
  by_cases ha : d ∈ as
  · exact .inl ⟨ha, mem_awaiting.mpr ⟨cl, hc, hdl, rfl, hd, ha⟩⟩
  · refine .inr ⟨ha, fun c hci => mem_reached.mpr ⟨cl, hc, hdl, rfl, hd, ha, hci, e, he, hn,
      hen e he, ?_⟩⟩
    rcases hr with hr | ⟨-, hr⟩
    · exact absurd hr ha
    · exact hr c hci e he hn

end Decides

end Execution

end LeanIntent
