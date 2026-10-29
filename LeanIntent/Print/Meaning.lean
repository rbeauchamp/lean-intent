import LeanIntent.Cone

/-!
# The declarations a term's meaning reaches

A term means what the declarations it names mean, and those mean what the declarations they name
mean in turn. `meaning lookup stop roots` collects the declarations reached from the names `roots`,
by following from each declaration every name it refers to, and stopping at the names `stop`
chooses. `LeanIntent.Render` prints every declaration it collects, so that what an owner reads of a
term reaches everything the term means.

What a declaration refers to is the relation of the cone that the check that a record does not
depend on its implementation follows (lean-intent #2), used here as that check defines it and not
restated: `LeanIntent.Cone.RefersTo`, whose names `LeanIntent.Cone.declRefs` lists
(`LeanIntent.Cone.mem_declRefs`). It is what can change what a term that names the declaration
means: the names its type mentions (`LeanIntent.Cone.Mentions`: as a constant, as the structure a
projection reads, or as the type Lean's kernel gives a literal); a definition's value; an inductive
type's mutual block, constructors and recursors, named as Lean names them; a constructor's
inductive type; and a recursor's block and rules. A theorem's proof and an opaque constant's value
are not followed: Lean's kernel never unfolds an opaque constant, and by definitional proof
irrelevance any two proofs of a proposition are equal, so neither changes what a term that names
the constant means. Nor is the mutual block of a definition, theorem or opaque constant, which
Lean's kernel does not read.

What is proved, for every lookup, every choice of names to stop at, and every list of roots:

* `meaning_ok`: when `meaning` returns a list of declarations, each is the one `lookup` finds under
  its name, and a name is in the list exactly when it is reached (`Reach`): a root, or a name a
  reached declaration refers to, that `stop` does not choose. So every name reached is collected,
  and nothing else is.
* `ctor_mem`, `induct_mem`, `block_mem`: in particular, the list holds every constructor of every
  inductive type it holds, the inductive type of every constructor it holds, and the block of every
  recursor it holds, except names `stop` chooses.
* `meaning_unknown`: when it refuses because a name has no declaration, that name is reached.

`meaning` also refuses when it would take more than `2 ^ 64` steps, more than the declarations that
fit in a 64-bit address space could ask of it, so it never returns a list it has not finished. That
`lookup` returns the declarations Lean's kernel checked is trusted with Lean; `LeanIntent.Render`
reads them with `Lean.Environment.find?`.
-/

namespace LeanIntent.Print

open Lean (Name ConstantInfo)
open LeanIntent.Cone (declRefs mem_declRefs)

theorem mem_declRefs_ctor {v : Lean.InductiveVal} {k : Name} (h : k ∈ v.ctors) :
    k ∈ declRefs (.inductInfo v) :=
  (mem_declRefs (.inductInfo v) k).mpr (Or.inr (Or.inr (Or.inl h)))

theorem mem_declRefs_induct {v : Lean.ConstructorVal} : v.induct ∈ declRefs (.ctorInfo v) :=
  (mem_declRefs (.ctorInfo v) v.induct).mpr (Or.inr rfl)

theorem mem_declRefs_block {v : Lean.RecursorVal} {i : Name} (h : i ∈ v.all) :
    i ∈ declRefs (.recInfo v) :=
  (mem_declRefs (.recInfo v) i).mpr (Or.inr (Or.inl h))

/-! ## The closure -/

/-- `Reach lookup stop roots c`: the name `c`, which `stop` does not choose, is one of `roots`, or
is referred to (`LeanIntent.Cone.declRefs`) by the declaration `lookup` finds under a name reached
before. -/
inductive Reach (lookup : Name → Option ConstantInfo) (stop : Name → Bool) (roots : List Name) :
    Name → Prop where
  | root {c : Name} : c ∈ roots → stop c = false → Reach lookup stop roots c
  | step {d c : Name} {ci : ConstantInfo} : Reach lookup stop roots d → lookup d = some ci →
      c ∈ declRefs ci → stop c = false → Reach lookup stop roots c

/-- Why `meaning` returns no declarations. -/
inductive Gap where
  /-- A reached name has no declaration. -/
  | unknown (c : Name)
  /-- More steps were needed than the fuel allows. -/
  | fuel
  deriving Inhabited, Repr, DecidableEq

/-- The closure: takes each name of `work` in turn, skips it when `stop` chooses it or `done`
already holds it, and otherwise adds its declaration to `done` and the names it refers to to
`work`. -/
def collect (lookup : Name → Option ConstantInfo) (stop : Name → Bool) :
    Nat → List Name → List (Name × ConstantInfo) → Except Gap (List (Name × ConstantInfo))
  | 0, _, _ => .error .fuel
  | _ + 1, [], done => .ok done
  | f + 1, c :: work, done =>
    if stop c = true ∨ c ∈ done.map Prod.fst then collect lookup stop f work done
    else
      match lookup c with
      | none => .error (.unknown c)
      | some ci => collect lookup stop f (declRefs ci ++ work) ((c, ci) :: done)

/-- The declarations reached from `roots`, in the order they are reached, each with its name; or
why there are none. -/
def meaning (lookup : Name → Option ConstantInfo) (stop : Name → Bool) (roots : List Name) :
    Except Gap (List (Name × ConstantInfo)) :=
  (collect lookup stop (2 ^ 64) roots []).map List.reverse

section Proofs

variable {lookup : Name → Option ConstantInfo} {stop : Name → Bool} {roots : List Name}

/-- What `collect` keeps true of the names still to take and the declarations already collected. -/
structure Inv (lookup : Name → Option ConstantInfo) (stop : Name → Bool) (roots : List Name)
    (work : List Name) (done : List (Name × ConstantInfo)) : Prop where
  found : ∀ p ∈ done, lookup p.1 = some p.2
  reached : ∀ p ∈ done, Reach lookup stop roots p.1
  pending : ∀ c ∈ work, stop c = false → Reach lookup stop roots c
  closed : ∀ p ∈ done, ∀ c ∈ declRefs p.2, stop c = false → c ∈ done.map Prod.fst ∨ c ∈ work

theorem collect_ok : (f : Nat) → {work : List Name} → {done out : List (Name × ConstantInfo)} →
    collect lookup stop f work done = .ok out → Inv lookup stop roots work done →
    Inv lookup stop roots [] out ∧ (∀ c ∈ work, stop c = false → c ∈ out.map Prod.fst) ∧
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
      have hi' : Inv lookup stop roots work done :=
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
        have hc : Reach lookup stop roots c := hi.pending c (List.mem_cons_self ..) hs
        have hi' : Inv lookup stop roots (declRefs ci ++ work) ((c, ci) :: done) :=
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
    {c : Name} → collect lookup stop f work done = .error (.unknown c) →
    Inv lookup stop roots work done → Reach lookup stop roots c ∧ lookup c = none
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
      have hx : Reach lookup stop roots x := hi.pending x (List.mem_cons_self ..) hs
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

theorem inv_init : Inv lookup stop roots roots [] where
  found := by simp
  reached := by simp
  pending := fun _ hc hs => .root hc hs
  closed := by simp

/-- **What `meaning` collects.** Each declaration it returns is the one `lookup` finds under its
name, and a name is among those it returns exactly when it is reached from `roots`. -/
theorem meaning_ok {out : List (Name × ConstantInfo)} (h : meaning lookup stop roots = .ok out) :
    (∀ p ∈ out, lookup p.1 = some p.2) ∧
      ∀ c, c ∈ out.map Prod.fst ↔ Reach lookup stop roots c := by
  simp only [meaning] at h
  cases hc : collect lookup stop (2 ^ 64) roots [] with
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

/-- A refusal for a name with no declaration names a reached name. -/
theorem meaning_unknown {c : Name} (h : meaning lookup stop roots = .error (.unknown c)) :
    Reach lookup stop roots c ∧ lookup c = none := by
  simp only [meaning] at h
  cases hc : collect lookup stop (2 ^ 64) roots [] with
  | error e =>
    simp only [hc, Except.map, Except.error.injEq] at h
    subst h
    exact collect_unknown _ hc inv_init
  | ok _ => simp [hc, Except.map] at h

theorem reach_of_mem {out : List (Name × ConstantInfo)} (h : meaning lookup stop roots = .ok out)
    {c : Name} {ci : ConstantInfo} (hp : (c, ci) ∈ out) :
    Reach lookup stop roots c ∧ lookup c = some ci :=
  ⟨((meaning_ok h).2 c).mp (List.mem_map.mpr ⟨_, hp, rfl⟩), (meaning_ok h).1 _ hp⟩

/-- Every constructor of an inductive type `meaning` returns is among the names it returns, unless
`stop` chooses it. -/
theorem ctor_mem {out : List (Name × ConstantInfo)} (h : meaning lookup stop roots = .ok out)
    {c k : Name} {v : Lean.InductiveVal} (hp : (c, .inductInfo v) ∈ out) (hk : k ∈ v.ctors)
    (hs : stop k = false) : k ∈ out.map Prod.fst :=
  let ⟨hr, hl⟩ := reach_of_mem h hp
  ((meaning_ok h).2 k).mpr (.step hr hl (mem_declRefs_ctor hk) hs)

/-- The inductive type of a constructor `meaning` returns is among the names it returns, unless
`stop` chooses it. -/
theorem induct_mem {out : List (Name × ConstantInfo)} (h : meaning lookup stop roots = .ok out)
    {c : Name} {v : Lean.ConstructorVal} (hp : (c, .ctorInfo v) ∈ out)
    (hs : stop v.induct = false) : v.induct ∈ out.map Prod.fst :=
  let ⟨hr, hl⟩ := reach_of_mem h hp
  ((meaning_ok h).2 _).mpr (.step hr hl mem_declRefs_induct hs)

/-- Every inductive type of the block of a recursor `meaning` returns is among the names it
returns, unless `stop` chooses it. -/
theorem block_mem {out : List (Name × ConstantInfo)} (h : meaning lookup stop roots = .ok out)
    {c i : Name} {v : Lean.RecursorVal} (hp : (c, .recInfo v) ∈ out) (hi : i ∈ v.all)
    (hs : stop i = false) : i ∈ out.map Prod.fst :=
  let ⟨hr, hl⟩ := reach_of_mem h hp
  ((meaning_ok h).2 i).mpr (.step hr hl (mem_declRefs_block hi) hs)

end Proofs

end LeanIntent.Print
