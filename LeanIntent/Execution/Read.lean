module

public import Lean
public import Std.Data.HashMap.Lemmas
public import LeanIntent.Execution
public import LeanIntent.Execution.Code
public import LeanIntent.Implementation.Read
public import LeanIntent.Imported
public import LeanIntent.Loaded

public section

namespace LeanIntent.Execution.Read

open Lean Meta LeanIntent.Render LeanIntent.Confirmation.Read LeanIntent.Imported

def nameLit (e : Expr) : MetaM Name := asking <|
  go (2 ^ 64) e
where
  go (fuel : Nat) (e : Expr) : MetaM Name := asking do
    match fuel with
    | 0 => throwError "name has more than 2 ^ 64 components"
    | fuel + 1 =>
      let e ← readWhnf e
      match e with
      | .const ``Name.anonymous _ => return .anonymous
      | .app (.app (.const ``Name.str _) parent) s =>
        return .str (← go fuel parent) (← strLit s)
      | .app (.app (.const ``Name.num _) parent) n =>
        match ← readWhnf n with
        | .lit (.natVal k) => return .num (← go fuel parent) k
        | n' => throwError "expected a natural number literal, found{indentExpr n'}"
      | _ => throwError "expected a name, found{indentExpr e}"

def claimOf (decl : Name) : MetaM Claim := asking do
  let t ← readWhnf (← getConstInfo decl).type
  let .app (.app (.const ``Runs _) _) d := t
    | throwError "the type of {decl} is not `LeanIntent.Runs` applied to a deliverable"
  let args ← ctorArgs (← Confirmation.Read.constOf decl) ``Runs.mk 3
  let executable ← try nameLit args[2] catch e =>
    throwError "the executable {decl} names is not read as a name: {e.toMessageData}"
  return ⟨decl, Implementation.Read.constOf? d, executable⟩

def claims (mods : Array Name) : MetaM (Array Claim) := asking do
  (← declaredIn mods ``Runs).mapM claimOf

@[expose] def exprRefs : IR.Expr → List Name
  | .fap c _ | .pap c _ => [c]
  | .ctor .. | .reset .. | .reuse .. | .proj .. | .uproj .. | .sproj .. | .ap .. | .box ..
  | .unbox .. | .lit .. | .isShared .. => []

mutual

@[expose] def bodyRefs : IR.FnBody → List Name
  | .vdecl _ _ e b => exprRefs e ++ bodyRefs b
  | .jdecl _ _ v b => bodyRefs v ++ bodyRefs b
  | .set _ _ _ b | .setTag _ _ b | .uset _ _ _ b | .sset _ _ _ _ _ b | .inc _ _ _ _ b
  | .dec _ _ _ _ b | .del _ b => bodyRefs b
  | .case _ _ _ cs => altsRefs cs.toList
  | .ret _ | .jmp _ _ | .unreachable => []

@[expose] def altsRefs : List IR.Alt → List Name
  | [] => []
  | .ctor _ b :: rest | .default b :: rest => bodyRefs b ++ altsRefs rest

end

@[expose] def irRefs (s : Stored) (n : Name) : List Name :=
  match s.irDecl? n with
  | some (.fdecl _ _ _ body _) => bodyRefs body
  | some (.extern ..) | none => []

@[expose] def importersOf (s : Stored) (m : Name) : Std.HashSet Name := Id.run do
  let mods := s.modules
  let mut importers : Std.HashMap Name (Array Name) := {}
  for (modName, imports) in mods do
    for imp in imports do
      importers := importers.insert imp ((importers.getD imp #[]).push modName)
  let mut found : Std.HashSet Name := ({} : Std.HashSet Name).insert m
  let mut work := [m]
  for _ in [0 : mods.size + 1] do
    match work with
    | [] => break
    | n :: rest =>
      work := rest
      for next in importers.getD n #[] do
        unless found.contains next do
          found := found.insert next
          work := next :: work
  return found

@[expose] def pushNew (queued : Std.HashSet Name) (acc : List Name) :
    List Name → Std.HashSet Name × List Name
  | [] => (queued, acc)
  | r :: rs =>
    if queued.contains r then pushNew queued acc rs
    else pushNew (queued.insert r) (r :: acc) rs

@[expose] def buildTable (step : Name → List Name) :
    Nat → Std.HashSet Name → List Name → Std.HashMap Name (List Name) →
      Option (Std.HashMap Name (List Name))
  | _, _, [], table => some table
  | 0, _, _ :: _, _ => none
  | fuel + 1, queued, n :: rest, table =>
    let refs := step n
    let (queued', push) := pushNew queued [] refs
    buildTable step fuel queued' (push.reverse ++ rest) (table.insert n refs)

section Table

theorem mem_table_insert {m : Std.HashMap Name (List Name)} {k a : Name} {v : List Name} :
    a ∈ m.insert k v ↔ a = k ∨ a ∈ m := by
  rw [Std.HashMap.mem_insert, beq_iff_eq, eq_comm]

theorem pushNew_mem (queued : Std.HashSet Name) (acc rs : List Name) :
    (∀ x, x ∈ (pushNew queued acc rs).1 ↔ x ∈ queued ∨ x ∈ rs) ∧
      (∀ x, x ∈ (pushNew queued acc rs).2 ↔ x ∈ acc ∨ (x ∈ rs ∧ x ∉ queued)) := by
  induction rs generalizing queued acc with
  | nil => simp [pushNew]
  | cons r rs ih =>
    unfold pushNew
    split
    · rename_i hr
      have hq : r ∈ queued := Std.HashSet.contains_iff_mem.mp hr
      obtain ⟨h1, h2⟩ := ih queued acc
      refine ⟨fun x => (h1 x).trans ?_, fun x => (h2 x).trans ?_⟩
      · simp only [List.mem_cons]
        constructor
        · rintro (hx | hx)
          · exact .inl hx
          · exact .inr (.inr hx)
        · rintro (hx | rfl | hx)
          · exact .inl hx
          · exact .inl hq
          · exact .inr hx
      · simp only [List.mem_cons]
        constructor
        · rintro (hx | ⟨hx, hnq⟩)
          · exact .inl hx
          · exact .inr ⟨.inr hx, hnq⟩
        · rintro (hx | ⟨rfl | hx, hnq⟩)
          · exact .inl hx
          · exact absurd hq hnq
          · exact .inr ⟨hx, hnq⟩
    · rename_i hr
      have hnq : r ∉ queued := fun h => hr (Std.HashSet.contains_iff_mem.mpr h)
      obtain ⟨h1, h2⟩ := ih (queued.insert r) (r :: acc)
      refine ⟨fun x => (h1 x).trans ?_, fun x => (h2 x).trans ?_⟩
      · simp only [Cone.mem_insert, List.mem_cons]
        constructor
        · rintro ((rfl | hx) | hx)
          · exact .inr (.inl rfl)
          · exact .inl hx
          · exact .inr (.inr hx)
        · rintro (hx | rfl | hx)
          · exact .inl (.inr hx)
          · exact .inl (.inl rfl)
          · exact .inr hx
      · simp only [List.mem_cons, Cone.mem_insert, not_or]
        constructor
        · rintro ((rfl | hx) | ⟨hx, hne, hnqx⟩)
          · exact .inr ⟨.inl rfl, hnq⟩
          · exact .inl hx
          · exact .inr ⟨.inr hx, hnqx⟩
        · rintro (hx | ⟨rfl | hx, hnqx⟩)
          · exact .inl (.inr hx)
          · exact .inl (.inl rfl)
          · by_cases hxr : x = r
            · subst hxr; exact .inl (.inl rfl)
            · exact .inr ⟨hx, hxr, hnqx⟩

structure TableInv (step : Name → List Name) (root : Name) (queued : Std.HashSet Name)
    (work : List Name) (table : Std.HashMap Name (List Name)) : Prop where
  root_mem : root ∈ table ∨ root ∈ work
  queued_cov : ∀ q ∈ queued, q ∈ table ∨ q ∈ work
  table_eq : ∀ k ∈ table, table.getD k [] = step k
  table_closed : ∀ k ∈ table, ∀ r ∈ table.getD k [], r ∈ table ∨ r ∈ work
  table_reach : ∀ k ∈ table, Reaches step root k
  work_reach : ∀ w ∈ work, Reaches step root w

theorem tableInv_init (step : Name → List Name) (root : Name) :
    TableInv step root (({} : Std.HashSet Name).insert root) [root] {} where
  root_mem := .inr (List.mem_singleton_self _)
  queued_cov := fun q hq => by
    rcases Cone.mem_insert.mp hq with rfl | hq
    · exact .inr (List.mem_singleton_self _)
    · exact absurd hq Std.HashSet.not_mem_empty
  table_eq := fun _ h => absurd h (Std.HashMap.not_mem_of_isEmpty Std.HashMap.isEmpty_empty)
  table_closed := fun _ h => absurd h (Std.HashMap.not_mem_of_isEmpty Std.HashMap.isEmpty_empty)
  table_reach := fun _ h => absurd h (Std.HashMap.not_mem_of_isEmpty Std.HashMap.isEmpty_empty)
  work_reach := fun w hw => List.mem_singleton.mp hw ▸ .root

theorem buildTable_inv {step : Name → List Name} {root : Name} :
    (fuel : Nat) → {queued : Std.HashSet Name} → {work : List Name} →
    {table out : Std.HashMap Name (List Name)} →
    TableInv step root queued work table →
    buildTable step fuel queued work table = some out →
    ∃ queued', TableInv step root queued' [] out
  | fuel, queued, [], table, out, hInv, h => by
    cases fuel <;> simp [buildTable] at h <;> subst h <;> exact ⟨queued, hInv⟩
  | 0, _, _ :: _, _, _, _, h => by simp [buildTable] at h
  | fuel + 1, queued, n :: rest, table, out, hInv, h => by
    unfold buildTable at h
    dsimp only at h
    obtain ⟨hq1, hq2⟩ := pushNew_mem queued [] (step n)
    have hn : Reaches step root n := hInv.work_reach n (List.mem_cons_self ..)
    have hcov : ∀ q ∈ (pushNew queued [] (step n)).1,
        q ∈ table.insert n (step n) ∨ q ∈ (pushNew queued [] (step n)).2.reverse ++ rest := by
      intro q hq
      rcases (hq1 q).mp hq with hqq | hqr
      · rcases hInv.queued_cov q hqq with hqt | hqw
        · exact .inl (mem_table_insert.mpr (.inr hqt))
        · rcases List.mem_cons.mp hqw with rfl | hqw
          · exact .inl (mem_table_insert.mpr (.inl rfl))
          · exact .inr (List.mem_append_right _ hqw)
      · by_cases hqq : q ∈ queued
        · rcases hInv.queued_cov q hqq with hqt | hqw
          · exact .inl (mem_table_insert.mpr (.inr hqt))
          · rcases List.mem_cons.mp hqw with rfl | hqw
            · exact .inl (mem_table_insert.mpr (.inl rfl))
            · exact .inr (List.mem_append_right _ hqw)
        · exact .inr (List.mem_append_left _ (List.mem_reverse.mpr ((hq2 q).mpr (.inr ⟨hqr, hqq⟩))))
    have hInv' : TableInv step root (pushNew queued [] (step n)).1
        ((pushNew queued [] (step n)).2.reverse ++ rest) (table.insert n (step n)) :=
      { root_mem := by
          rcases hInv.root_mem with ht | hw
          · exact .inl (mem_table_insert.mpr (.inr ht))
          · rcases List.mem_cons.mp hw with rfl | hw
            · exact .inl (mem_table_insert.mpr (.inl rfl))
            · exact .inr (List.mem_append_right _ hw)
        queued_cov := hcov
        table_eq := fun k hk => by
          rw [Std.HashMap.getD_insert]
          split
          · rename_i heq
            rw [beq_iff_eq.mp heq]
          · rename_i hne
            have hkt : k ∈ table := by
              rcases mem_table_insert.mp hk with rfl | hkt
              · exact absurd (beq_self_eq_true _) hne
              · exact hkt
            exact hInv.table_eq k hkt
        table_closed := fun k hk r hr => by
          rw [Std.HashMap.getD_insert] at hr
          split at hr
          · exact hcov r ((hq1 r).mpr (.inr hr))
          · rename_i hne
            have hkt : k ∈ table := by
              rcases mem_table_insert.mp hk with rfl | hkt
              · exact absurd (beq_self_eq_true _) hne
              · exact hkt
            rcases hInv.table_closed k hkt r hr with hrt | hrw
            · exact .inl (mem_table_insert.mpr (.inr hrt))
            · rcases List.mem_cons.mp hrw with rfl | hrw
              · exact .inl (mem_table_insert.mpr (.inl rfl))
              · exact .inr (List.mem_append_right _ hrw)
        table_reach := fun k hk => by
          rcases mem_table_insert.mp hk with rfl | hk
          · exact hn
          · exact hInv.table_reach k hk
        work_reach := fun w hw => by
          rcases List.mem_append.mp hw with hw | hw
          · rcases (hq2 w).mp (List.mem_reverse.mp hw) with hnil | ⟨hwr, _⟩
            · exact nomatch hnil
            · exact .step hn hwr
          · exact hInv.work_reach w (List.mem_cons_of_mem _ hw) }
    exact buildTable_inv fuel hInv' h

theorem buildTable_mem_of_reaches {step : Name → List Name} {root : Name} {fuel : Nat}
    {out : Std.HashMap Name (List Name)}
    (h : buildTable step fuel (({} : Std.HashSet Name).insert root) [root] {} = some out)
    {c : Name} (hc : Reaches (fun n => out.getD n []) root c) : c ∈ out := by
  obtain ⟨_, hInv⟩ := buildTable_inv fuel (tableInv_init step root) h
  induction hc with
  | root => exact hInv.root_mem.elim id (fun h => nomatch h)
  | step _ hd ih => exact (hInv.table_closed _ ih _ hd).elim id (fun h => nomatch h)

theorem buildTable_within {step : Name → List Name} {root : Name} {fuel : Nat}
    {out : Std.HashMap Name (List Name)}
    (h : buildTable step fuel (({} : Std.HashSet Name).insert root) [root] {} = some out) :
    Within (fun n => out.getD n []) root out.size :=
  ⟨out.keys, by simp, fun c hc => Std.HashMap.mem_keys.mpr (buildTable_mem_of_reaches h hc)⟩

theorem buildTable_within_succ {step : Name → List Name} {root : Name} {fuel : Nat}
    {out : Std.HashMap Name (List Name)}
    (h : buildTable step fuel (({} : Std.HashSet Name).insert root) [root] {} = some out) :
    Within (fun n => out.getD n []) root (out.size + 1) :=
  let ⟨l, hlen, hl⟩ := buildTable_within h
  ⟨l, Nat.le_trans hlen (Nat.le_succ _), hl⟩

theorem buildTable_reaches_iff {step : Name → List Name} {root : Name} {fuel : Nat}
    {out : Std.HashMap Name (List Name)}
    (h : buildTable step fuel (({} : Std.HashSet Name).insert root) [root] {} = some out)
    {c : Name} : Reaches (fun n => out.getD n []) root c ↔ Reaches step root c := by
  obtain ⟨_, hInv⟩ := buildTable_inv fuel (tableInv_init step root) h
  constructor
  · intro hc
    induction hc with
    | root => exact .root
    | step _ hd ih =>
      rename_i d _ _
      by_cases hdm : d ∈ out
      · rw [hInv.table_eq d hdm] at hd
        exact .step ih hd
      · rw [Std.HashMap.getD_eq_fallback hdm] at hd
        exact absurd hd List.not_mem_nil
  · intro hc
    induction hc with
    | root => exact .root
    | step _ hd ih =>
      rename_i d _ _
      have hdm : d ∈ out := buildTable_mem_of_reaches h ih
      rw [← hInv.table_eq d hdm] at hd
      exact .step ih hd

theorem buildTable_reach_eq_reached_iff {step : Name → List Name} {root target : Name}
    {fuel : Nat} {out : Std.HashMap Name (List Name)}
    (h : buildTable step fuel (({} : Std.HashSet Name).insert root) [root] {} = some out) :
    reach (fun n => out.getD n []) root target (out.size + 1) = .reached ↔
      Reaches step root target :=
  (reach_eq_reached_iff (buildTable_within_succ h)).trans (buildTable_reaches_iff h)

theorem buildTable_reach_ne_exhausted {step : Name → List Name} {root target : Name}
    {fuel : Nat} {out : Std.HashMap Name (List Name)}
    (h : buildTable step fuel (({} : Std.HashSet Name).insert root) [root] {} = some out) :
    reach (fun n => out.getD n []) root target (out.size + 1) ≠ .exhausted :=
  fun hexh => absurd (buildTable_within_succ h) (reach_exhausted hexh)

end Table

@[expose] def reachesIn (s : Stored) (c : Implementation.Constant) : Except String Bool := do
  unless s.moduleOf c.name == some c.module do return false
  let up := importersOf s c.module
  let inCone (n : Name) : Bool := (s.moduleOf n).any up.contains
  unless inCone `main do return false
  let code (n : Name) : List Name :=
    if n != c.name && isCompiledCodeOf s.contains c.name n && (s.irDecl? n).isSome
    then [c.name] else []
  let step (n : Name) : List Name := (irRefs s n ++ code n).filter inCone
  let some table := buildTable step (s.constCount + 1)
      (({} : Std.HashSet Name).insert `main) [`main] {}
    | throw s!"`main` reaches more than {s.constCount + 1} declarations"
  return reach (fun n => table.getD n []) `main c.name (table.size + 1) == .reached

@[expose] def executableIn (s : Stored) (name root : Name) (targets : List Implementation.Constant) :
    Except String Executable := do
  let entry := s.contains `main
  let reached ← if entry then targets.filterM (reachesIn s) else pure []
  return ⟨name, root, entry, reached⟩

def check (mods : Array Name) (exes : Array (Name × Name)) : MetaM Report := asking do
  let ds ← declaredIn mods ``Deliverable
  let implemented ← Implementation.Read.check mods
  let is := implemented.implementations.map fun (d, _, c) => (d, c)
  let as := implemented.awaiting.map (·.1)
  let cls ← claims mods
  let es ← exes.mapM fun (name, root) => do
    let targets := (cls.toList.filter (·.executable == name)).flatMap fun cl =>
      is.filterMap fun (d, c) => if cl.deliverable == some d then some c else none
    try
      match executableIn (← stored root (← getOptions)) name root targets.eraseDups with
      | .ok e => return e
      | .error why => throwError "{why}"
    catch err =>
      throwError "the executable {name}, whose root module is {root}, cannot be read: \
        {err.toMessageData}"
  return report ds.toList is as es.toList cls.toList

end LeanIntent.Execution.Read
