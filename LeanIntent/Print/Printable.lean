import LeanIntent.Print.RoundTrip

/-!
# The terms the printer prints

`Printable` states, apart from the printer, which terms it prints, and `pr_isSome_iff` proves that
the printer prints exactly those, at every precedence and for every choice of `bare`: it refuses
no term of the class, so it is not met by refusing everything, and prints none outside it.
-/

namespace LeanIntent.Print

open Lean (Name Level Expr Literal BinderInfo)

/-- A universe level the printer writes: built from `0`, successors, `max`, `imax` and parameters,
each parameter's name one component that can be written; no level metavariable. -/
inductive LevelOk : Level → Prop
  | zero : LevelOk .zero
  | succ {l : Level} : LevelOk l → LevelOk (.succ l)
  | max {a b : Level} : LevelOk a → LevelOk b → LevelOk (.max a b)
  | imax {a b : Level} : LevelOk a → LevelOk b → LevelOk (.imax a b)
  | param {n : Name} : atomOk n = true → LevelOk (.param n)

/-- The terms the printer prints, under the binders `sc`, innermost first: bound variables that
name their binder, with no binder of the same name between; constants with names whose components
are strings that can be written, at levels it writes; sorts; string and natural number literals;
applications; and `fun` and `∀` with binder names of one component that can be written, or a
`∀` with no binder name and the default annotation, written as an arrow. Free and meta variables,
`let`, metadata and projections are not among them. -/
inductive Printable : List Name → Expr → Prop
  | bvar {sc : List Name} {i : Nat} {n : Name} : sc[i]? = some n → atomOk n = true →
      lookup n sc = some i → Printable sc (.bvar i)
  | const {sc : List Name} {c : Name} {us : List Level} : nameOk c = true →
      (∀ u ∈ us, LevelOk u) → Printable sc (.const c us)
  | sort {sc : List Name} {l : Level} : LevelOk l → Printable sc (.sort l)
  | strLit {sc : List Name} {s : String} : Printable sc (.lit (.strVal s))
  | natLit {sc : List Name} {n : Nat} : Printable sc (.lit (.natVal n))
  | app {sc : List Name} {f a : Expr} : Printable sc f → Printable sc a → Printable sc (.app f a)
  | lam {sc : List Name} {n : Name} {t b : Expr} {bi : BinderInfo} : atomOk n = true →
      Printable sc t → Printable (n :: sc) b → Printable sc (.lam n t b bi)
  | arrow {sc : List Name} {t b : Expr} : Printable sc t → Printable (.anonymous :: sc) b →
      Printable sc (.forallE .anonymous t b .default)
  | pi {sc : List Name} {n : Name} {t b : Expr} {bi : BinderInfo} : atomOk n = true →
      Printable sc t → Printable (n :: sc) b → Printable sc (.forallE n t b bi)

theorem levelOk_of_natOf : {l : Level} → {k : Nat} → natOf l = some k → LevelOk l
  | .zero, _, _ => .zero
  | .succ l, k, h => by
    simp only [natOf, Option.map_eq_some_iff] at h
    obtain ⟨k', h', _⟩ := h
    exact .succ (levelOk_of_natOf h')
  | .max _ _, _, h | .imax _ _, _, h | .param _, _, h | .mvar _, _, h => by simp [natOf] at h

theorem prLevel_isSome_iff (l : Level) (atom : Bool) : (prLevel l atom).isSome ↔ LevelOk l := by
  induction l generalizing atom with
  | zero => simp [prLevel, LevelOk.zero]
  | succ l ih =>
    simp only [prLevel]
    split
    · next k hk => exact ⟨fun _ => .succ (levelOk_of_natOf hk), fun _ => rfl⟩
    · rw [Option.isSome_map, ih]
      exact ⟨.succ, fun h => by cases h; assumption⟩
  | max a b iha ihb | imax a b iha ihb =>
    simp only [prLevel, Option.bind_eq_bind]
    constructor
    · intro h
      cases ha : prLevel a true <;> cases hb : prLevel b true <;> simp [ha, hb] at h
      first
        | exact .max ((iha true).mp (by simp [ha])) ((ihb true).mp (by simp [hb]))
        | exact .imax ((iha true).mp (by simp [ha])) ((ihb true).mp (by simp [hb]))
    · intro h
      cases h
      next h1 h2 =>
        obtain ⟨ta, hta⟩ := Option.isSome_iff_exists.mp ((iha true).mpr h1)
        obtain ⟨tb, htb⟩ := Option.isSome_iff_exists.mp ((ihb true).mpr h2)
        simp [hta, htb]
  | param n =>
    simp only [prLevel]
    split
    · next h => exact ⟨fun _ => .param h, fun _ => rfl⟩
    · next h => exact ⟨fun h' => by simp at h', fun h' => by cases h'; simp_all⟩
  | mvar => exact ⟨fun h => by simp [prLevel] at h, fun h => by cases h⟩

theorem prLevels_isSome_iff : (us : List Level) → (prLevels us).isSome ↔ ∀ u ∈ us, LevelOk u
  | [] => by simp [prLevels]
  | [l] => by simp [prLevels, prLevel_isSome_iff]
  | l :: l' :: ls => by
    have ih := prLevels_isSome_iff (l' :: ls)
    have hl := prLevel_isSome_iff l false
    simp only [prLevels, Option.bind_eq_bind, List.forall_mem_cons] at ih ⊢
    constructor
    · intro h
      cases ht : prLevel l false <;> cases hr : prLevels (l' :: ls) <;> simp [ht, hr] at h
      exact ⟨hl.mp (by simp [ht]), (ih.mp (by simp [hr]))⟩
    · intro ⟨h1, h2⟩
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (hl.mpr h1)
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (ih.mpr h2)
      simp [ht, hr]

theorem prUnivs_isSome_iff (us : List Level) : (prUnivs us).isSome ↔ ∀ u ∈ us, LevelOk u := by
  cases us with
  | nil => simp [prUnivs]
  | cons u us => simp only [prUnivs, Option.isSome_map]; exact prLevels_isSome_iff _

theorem prSort_isSome_iff (l : Level) : (prSort l).isSome ↔ LevelOk l := by
  cases l with
  | zero => simp [prSort, LevelOk.zero]
  | succ l =>
    simp only [prSort]
    split
    · next h =>
      have : l = .zero := by cases l <;> simp_all [isZero]
      subst this; exact ⟨fun _ => .succ .zero, fun _ => rfl⟩
    · rw [Option.isSome_map, prLevel_isSome_iff]
      exact ⟨.succ, fun h => by cases h; assumption⟩
  | max | imax | param | mvar => simp only [prSort, Option.isSome_map]; exact prLevel_isSome_iff _ _

/-- The printer prints exactly the terms `Printable` admits, at every precedence. -/
theorem pr_isSome_iff (bare : Name → Bool) (e : Expr) :
    ∀ (sc : List Name) (p : Prec), (pr bare sc e p).isSome ↔ Printable sc e := by
  induction e with
  | bvar i =>
    intro sc p
    simp only [pr]
    split
    · next n hn =>
      split
      · next h =>
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        exact ⟨fun _ => .bvar hn h.1 h.2, fun _ => rfl⟩
      · next h =>
        refine ⟨fun h' => by simp at h', fun h' => ?_⟩
        cases h'
        next n' hn' hok hl => simp_all
    · next hn => exact ⟨fun h => by simp at h, fun h => by cases h; simp_all⟩
  | const c us =>
    intro sc p
    simp only [pr]
    split
    · next h =>
      rw [Option.isSome_map, prUnivs_isSome_iff]
      exact ⟨fun hu => .const h hu, fun h' => by cases h'; assumption⟩
    · next h => exact ⟨fun h' => by simp at h', fun h' => by cases h'; simp_all⟩
  | sort l =>
    intro sc p
    simp only [pr, Option.isSome_map, prSort_isSome_iff]
    exact ⟨.sort, fun h => by cases h; assumption⟩
  | lit l =>
    intro sc p
    cases l with
    | strVal s => exact ⟨fun _ => .strLit, fun _ => rfl⟩
    | natVal n => exact ⟨fun _ => .natLit, fun _ => rfl⟩
  | app f a ihf iha =>
    intro sc p
    simp only [pr, Option.bind_eq_bind]
    constructor
    · intro h
      cases hf : pr bare sc f .head <;> cases ha : pr bare sc a .arg <;> simp [hf, ha] at h
      exact .app ((ihf sc .head).mp (by simp [hf])) ((iha sc .arg).mp (by simp [ha]))
    · intro h
      cases h
      next h1 h2 =>
        obtain ⟨tf, hf⟩ := Option.isSome_iff_exists.mp ((ihf sc .head).mpr h1)
        obtain ⟨ta, ha⟩ := Option.isSome_iff_exists.mp ((iha sc .arg).mpr h2)
        simp [hf, ha]
  | lam n t b bi iht ihb =>
    intro sc p
    simp only [pr, Option.bind_eq_bind]
    split
    · next hn =>
      constructor
      · intro h
        cases ht : pr bare sc t .term <;> cases hb : pr bare (n :: sc) b .term <;> simp [ht, hb] at h
        exact .lam hn ((iht sc .term).mp (by simp [ht])) ((ihb (n :: sc) .term).mp (by simp [hb]))
      · intro h
        cases h
        next _ h1 h2 =>
          obtain ⟨tt, ht⟩ := Option.isSome_iff_exists.mp ((iht sc .term).mpr h1)
          obtain ⟨tb, hb⟩ := Option.isSome_iff_exists.mp ((ihb (n :: sc) .term).mpr h2)
          simp [ht, hb]
    · next hn => exact ⟨fun h => by simp at h, fun h => by cases h; simp_all⟩
  | forallE n t b bi iht ihb =>
    intro sc p
    simp only [pr, Option.bind_eq_bind]
    split
    · next ha =>
      have hn : n = .anonymous ∧ bi = .default := by
        cases n <;> cases bi <;> simp_all [isArrow]
      obtain ⟨rfl, rfl⟩ := hn
      constructor
      · intro h
        cases ht : pr bare sc t .simple <;> cases hb : pr bare (.anonymous :: sc) b .term <;>
          simp [ht, hb] at h
        exact .arrow ((iht sc .simple).mp (by simp [ht])) ((ihb _ .term).mp (by simp [hb]))
      · intro h
        cases h with
        | arrow h1 h2 =>
          obtain ⟨tt, ht⟩ := Option.isSome_iff_exists.mp ((iht sc .simple).mpr h1)
          obtain ⟨tb, hb⟩ := Option.isSome_iff_exists.mp ((ihb _ .term).mpr h2)
          simp [ht, hb]
        | pi hok _ _ => simp [atomOk] at hok
    · next ha =>
      split
      · next hn =>
        constructor
        · intro h
          cases ht : pr bare sc t .term <;> cases hb : pr bare (n :: sc) b .term <;>
            simp [ht, hb] at h
          exact .pi hn ((iht sc .term).mp (by simp [ht])) ((ihb (n :: sc) .term).mp (by simp [hb]))
        · intro h
          cases h with
          | arrow => simp [isArrow] at ha
          | pi _ h1 h2 =>
            obtain ⟨tt, ht⟩ := Option.isSome_iff_exists.mp ((iht sc .term).mpr h1)
            obtain ⟨tb, hb⟩ := Option.isSome_iff_exists.mp ((ihb _ .term).mpr h2)
            simp [ht, hb]
      · next hn =>
        refine ⟨fun h => by simp at h, fun h => ?_⟩
        cases h with
        | arrow => simp [isArrow] at ha
        | pi hok => simp_all
  | fvar | mvar | letE | mdata | proj =>
    intro sc p
    exact ⟨fun h => by simp [pr] at h, fun h => by cases h⟩

end LeanIntent.Print
