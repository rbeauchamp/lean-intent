import LeanIntent.Print.Term

/-!
# The printer's output parses back to the term it printed

`claims` proves that `psTerm` reads back, from the tokens `pr` writes for a term at the lowest
precedence, exactly that term, for every term, every scope and every choice of `bare` (`ClaimT`).
The proof is by induction on the term, with one claim per precedence (`ClaimA`, `ClaimH`,
`ClaimS` and `ClaimT`).
-/

namespace LeanIntent.Print

open Lean (Name Level Expr Literal BinderInfo)

/-! ## Levels -/

theorem levelOfNat_of_natOf : {l : Level} → {k : Nat} → natOf l = some k → levelOfNat k = l
  | .zero, k, h => by simp [natOf] at h; subst h; rfl
  | .succ l, k, h => by
    simp only [natOf, Option.map_eq_some_iff] at h
    obtain ⟨k', h', rfl⟩ := h
    simp [levelOfNat, levelOfNat_of_natOf h']
  | .max _ _, _, h | .imax _ _, _, h | .param _, _, h | .mvar _, _, h => by simp [natOf] at h

theorem paren_true (ts : List Tok) : paren true ts = .lparen :: ts ++ [.rparen] := rfl
theorem paren_false (ts : List Tok) : paren false ts = ts := rfl
theorem paren_false_eq : paren false = id := rfl

/-- A level at an atom's precedence starts with a numeral, an identifier or `(`. -/
theorem levelStart_prLevel {l : Level} {ts : List Tok} (h : prLevel l true = some ts)
    (rest : List Tok) : levelStart (ts ++ rest) = true := by
  cases l with
  | zero => simp [prLevel] at h; subst h; rfl
  | succ l =>
    simp only [prLevel] at h
    split at h
    · simp at h; subst h; rfl
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h; rfl
  | max a b | imax a b =>
    simp only [prLevel, Bind.bind, Option.bind] at h
    split at h <;> try simp at h
    split at h <;> simp at h; subst h; rfl
  | param n =>
    simp only [prLevel] at h
    split at h <;> simp at h; subst h; rfl
  | mvar => simp [prLevel] at h

theorem psLevel_default {f : Nat} {ts : List Tok} (h1 : ∀ r, ts ≠ .kwMax :: r)
    (h2 : ∀ r, ts ≠ .kwImax :: r) :
    psLevel (f + 1) ts = (psLevelAtom f ts).bind fun (a, ts) => levelTail a ts := by
  cases ts with
  | nil => rfl
  | cons t ts => cases t <;> first | rfl | simp_all

theorem levelTail_of {a : Level} {rest : List Tok} (h : rest.head? ≠ some .plus) :
    levelTail a rest = some (a, rest) := by
  cases rest with
  | nil => rfl
  | cons t r => cases t <;> simp_all [levelTail]

/-- `psLevel` reads a level that starts as an atom does through `psLevelAtom`. -/
theorem psLevel_of_atom {f : Nat} {ts : List Tok} (h : levelStart ts = true) :
    psLevel (f + 1) ts = (psLevelAtom f ts).bind fun (a, ts) => levelTail a ts :=
  psLevel_default (fun r he => by subst he; simp [levelStart] at h)
    (fun r he => by subst he; simp [levelStart] at h)

/-- Reading a level in parentheses at an atom's precedence, from reading it at the lowest. -/
theorem psLevelAtom_paren (l : Level) (ts : List Tok) (h : ∀ f, 2 * ts.length + 1 ≤ f → ∀ rest,
    rest.head? ≠ some .plus → psLevel f (ts ++ rest) = some (l, rest)) :
    ∀ f, 2 * (paren true ts).length ≤ f → ∀ rest,
      psLevelAtom f (paren true ts ++ rest) = some (l, rest) := by
  intro f hf rest
  obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp [paren_true] at hf; omega⟩
  simp only [paren_true, List.cons_append, List.append_assoc, List.nil_append, psLevelAtom]
  rw [h f (by simp [paren_true] at hf; omega) (.rparen :: rest) (by simp)]
  rfl

/-- Reading a level that is one token, a numeral or a parameter. -/
theorem psLevel_single (l : Level) (t : Tok) (ht : levelStart [t] = true)
    (h1 : ∀ rest, psLevelAtom 1 (t :: rest) = some (l, rest)) :
    (∀ f, 2 ≤ f → ∀ rest, psLevelAtom f (t :: rest) = some (l, rest)) ∧
    (∀ f, 3 ≤ f → ∀ rest, rest.head? ≠ some .plus → psLevel f (t :: rest) = some (l, rest)) := by
  have hat : ∀ f, 1 ≤ f → ∀ rest, psLevelAtom f (t :: rest) = some (l, rest) := by
    intro f hf rest
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    have := h1 rest
    cases t <;> simp_all [psLevelAtom, psLevel, levelStart]
  refine ⟨fun f hf => hat f (by omega), fun f hf rest hr => ?_⟩
  obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  rw [psLevel_of_atom (by cases t <;> simp_all [levelStart]), hat f (by omega) rest]
  exact levelTail_of hr

/-- Reading `max a b` or `imax a b` at the lowest precedence. -/
theorem psLevel_binary (l : Level) (k : Tok) (a b : Level) (ta tb : List Tok)
    (hk : ∀ f rest, psLevel (f + 1) (k :: rest) = (psLevelAtom f rest).bind fun (a', r) =>
      (psLevelAtom f r).bind fun (b', r) => some (if k = .kwMax then .max a' b' else .imax a' b', r))
    (ha : ∀ f, 2 * ta.length ≤ f → ∀ rest, psLevelAtom f (ta ++ rest) = some (a, rest))
    (hb : ∀ f, 2 * tb.length ≤ f → ∀ rest, psLevelAtom f (tb ++ rest) = some (b, rest))
    (hl : l = if k = .kwMax then .max a b else .imax a b) :
    ∀ f, 2 * (k :: ta ++ tb).length + 1 ≤ f → ∀ rest,
      psLevel f ((k :: ta ++ tb) ++ rest) = some (l, rest) := by
  intro f hf rest
  obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  simp only [List.length_cons, List.length_append] at hf
  simp only [List.cons_append, List.append_assoc]
  rw [hk]
  simp only [ha f (by omega), hb f (by omega), Option.bind_some, hl]

/-- `psLevelAtom` and `psLevel` read back what `prLevel` writes, at an atom's precedence before
anything, and otherwise before anything but `+`. -/
theorem psLevel_prLevel (l : Level) :
    (∀ ts, prLevel l true = some ts → ∀ f, 2 * ts.length ≤ f → ∀ rest,
      psLevelAtom f (ts ++ rest) = some (l, rest)) ∧
    (∀ ts, prLevel l false = some ts → ∀ f, 2 * ts.length + 1 ≤ f → ∀ rest,
      rest.head? ≠ some .plus → psLevel f (ts ++ rest) = some (l, rest)) := by
  induction l with
  | zero =>
    have := psLevel_single .zero (.num 0) rfl (fun _ => rfl)
    refine ⟨fun ts h => ?_, fun ts h => ?_⟩ <;> simp only [prLevel, Option.some.injEq] at h <;>
      subst h
    · exact this.1
    · exact this.2
  | succ l ih =>
    cases hk : natOf l with
    | some k =>
      have hl : levelOfNat (k + 1) = .succ l := by simp [levelOfNat, levelOfNat_of_natOf hk]
      have := psLevel_single (.succ l) (.num (k + 1)) rfl (fun _ => by simp [psLevelAtom, hl])
      refine ⟨fun ts h => ?_, fun ts h => ?_⟩ <;> simp only [prLevel, hk, Option.some.injEq] at h <;>
        subst h
      · exact this.1
      · exact this.2
    | none =>
      cases hl : prLevel l true with
      | none => simp [prLevel, hk, hl]
      | some tl =>
        have low : ∀ f, 2 * (tl ++ [Tok.plus, .num 1]).length + 1 ≤ f → ∀ rest,
            rest.head? ≠ some .plus →
            psLevel f ((tl ++ [Tok.plus, .num 1]) ++ rest) = some (.succ l, rest) := by
          intro f hf rest hr
          obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
          simp only [List.length_append, List.length_cons, List.length_nil] at hf
          simp only [List.append_assoc, List.cons_append, List.nil_append]
          rw [psLevel_of_atom (levelStart_prLevel hl _), ih.1 tl hl f (by omega)]
          rfl
        refine ⟨fun ts h => ?_, fun ts h => ?_⟩ <;>
          simp only [prLevel, hk, hl, Option.map_some, Option.some.injEq] at h <;> subst h
        · exact psLevelAtom_paren _ _ low
        · exact low
  | max a b iha ihb =>
    cases ha : prLevel a true with
    | none => simp [prLevel, ha]
    | some ta =>
      cases hb : prLevel b true with
      | none => simp [prLevel, ha, hb]
      | some tb =>
        have low := psLevel_binary _ .kwMax a b ta tb (fun _ _ => by simp [psLevel]) (iha.1 ta ha)
          (ihb.1 tb hb) rfl
        refine ⟨fun ts h => ?_, fun ts h => ?_⟩ <;>
          simp only [prLevel, ha, hb, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at h <;> subst h
        · exact psLevelAtom_paren _ _ fun f hf rest _ => low f hf rest
        · exact fun f hf rest _ => low f hf rest
  | imax a b iha ihb =>
    cases ha : prLevel a true with
    | none => simp [prLevel, ha]
    | some ta =>
      cases hb : prLevel b true with
      | none => simp [prLevel, ha, hb]
      | some tb =>
        have low := psLevel_binary _ .kwImax a b ta tb (fun _ _ => by simp [psLevel]) (iha.1 ta ha)
          (ihb.1 tb hb) rfl
        refine ⟨fun ts h => ?_, fun ts h => ?_⟩ <;>
          simp only [prLevel, ha, hb, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at h <;> subst h
        · exact psLevelAtom_paren _ _ fun f hf rest _ => low f hf rest
        · exact fun f hf rest _ => low f hf rest
  | param n =>
    have hp : prLevel (.param n) true = prLevel (.param n) false := rfl
    cases hn : atomOk n with
    | false => simp [prLevel, hn]
    | true =>
      have := psLevel_single (.param n) (.ident n) rfl (fun _ => rfl)
      refine ⟨fun ts h => ?_, fun ts h => ?_⟩ <;> simp only [prLevel, hn, ite_true,
        Option.some.injEq] at h <;> subst h
      · exact this.1
      · exact this.2
  | mvar => exact ⟨fun _ h => by simp [prLevel] at h, fun _ h => by simp [prLevel] at h⟩

theorem one_le_prLevel {l : Level} {atom : Bool} {ts : List Tok} (h : prLevel l atom = some ts) :
    1 ≤ ts.length := by
  cases l with
  | zero => simp [prLevel] at h; subst h; simp
  | succ l =>
    simp only [prLevel] at h
    split at h
    · simp at h; subst h; simp
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h; cases atom <;> simp [paren]
  | max a b | imax a b =>
    simp only [prLevel, Option.bind_eq_bind] at h
    cases ha : prLevel a true <;> cases hb : prLevel b true <;> simp [ha, hb] at h
    subst h
    cases atom <;> simp [paren]
  | param n => simp only [prLevel] at h; split at h <;> simp at h; subst h; simp
  | mvar => simp [prLevel] at h

theorem length_le_prLevels : (us : List Level) → (ts : List Tok) → prLevels us = some ts →
    us.length ≤ ts.length
  | [], _, _ => by simp
  | [l], ts, h => by simp only [prLevels] at h; have := one_le_prLevel h; simp; omega
  | l :: l' :: ls, ts, h => by
    simp only [prLevels, Option.bind_eq_bind] at h
    cases ht : prLevel l false <;> cases hr : prLevels (l' :: ls) <;> simp [ht, hr] at h
    subst h
    have h1 := length_le_prLevels (l' :: ls) _ hr
    have h2 := one_le_prLevel ht
    simp only [List.length_cons, List.length_append] at h1 h2 ⊢; omega

theorem psLevels_prLevels : (us : List Level) → us ≠ [] → (ts : List Tok) → prLevels us = some ts →
    (f : Nat) → us.length ≤ f → (rest : List Tok) →
    psLevels f (ts ++ .rbrace :: rest) = some (us, rest)
  | [], h, _, _, _, _, _ => absurd rfl h
  | [l], _, ts, h, f + 1, _, rest => by
    simp only [prLevels] at h
    simp only [psLevels, Option.bind_eq_bind]
    rw [(psLevel_prLevel l).2 ts h _ (by simp; omega) _ (by simp)]
    rfl
  | l :: l' :: ls, _, ts, h, f + 1, hf, rest => by
    simp only [prLevels, Option.bind_eq_bind] at h
    cases ht : prLevel l false <;> cases hr : prLevels (l' :: ls) <;> simp [ht, hr] at h
    subst h
    simp only [psLevels, Option.bind_eq_bind, List.append_assoc, List.cons_append]
    rw [(psLevel_prLevel l).2 _ ht _ (by simp; omega) _ (by simp)]
    simp only [Option.bind_some]
    rw [psLevels_prLevels (l' :: ls) (by simp) _ hr f (by simp at hf ⊢; omega) rest]
    rfl

/-- `psUnivs` reads back a constant's universe levels, before anything but `.{`. -/
theorem psUnivs_prUnivs {us : List Level} {ts : List Tok} (h : prUnivs us = some ts)
    (rest : List Tok) (hr : rest.head? ≠ some .dotBrace) : psUnivs (ts ++ rest) = some (us, rest) := by
  cases us with
  | nil =>
    simp only [prUnivs, Option.some.injEq] at h; subst h
    cases rest with
    | nil => rfl
    | cons t r => cases t <;> first | rfl | simp_all
  | cons u us =>
    simp only [prUnivs, Option.map_eq_some_iff] at h
    obtain ⟨t, ht, rfl⟩ := h
    simp only [List.cons_append, List.append_assoc, psUnivs]
    have := length_le_prLevels _ _ ht
    exact psLevels_prLevels (u :: us) (by simp) t ht _ (by simp at this ⊢; omega) rest

/-! ## Terms -/

/-- Whether `e` printed at `p` is in parentheses. -/
def needsParen : Expr → Prec → Bool
  | .app .., p => p.isArg
  | .sort l, p => !isZero l && p.tight
  | .lit (.natVal _), p => p.tight
  | .lam .., p | .forallE .., p => !p.isTerm
  | _, _ => false

/-- A term printed at any precedence is the term printed at the lowest, in parentheses where
`needsParen` says. -/
theorem pr_prec (bare : Name → Bool) (sc : List Name) (e : Expr) (p : Prec) :
    pr bare sc e p = (pr bare sc e .term).map (paren (needsParen e p)) := by
  cases e with
  | bvar i => simp only [pr, needsParen]; split <;> (try split) <;> simp [paren_false]
  | fvar | mvar | letE | mdata | proj => simp [pr]
  | const c us =>
    simp only [pr, needsParen]
    split
    · cases prUnivs us <;> simp [paren_false]
    · simp
  | sort l =>
    simp only [pr, needsParen, Option.map_map]
    cases prSort l <;> simp [Prec.tight, paren_false]
  | lit l =>
    cases l with
    | strVal s => simp [pr, needsParen, paren_false]
    | natVal n => simp [pr, needsParen, Prec.tight, paren_false]
  | app f a =>
    simp only [pr, needsParen, Option.bind_eq_bind]
    cases pr bare sc f .head <;> cases pr bare sc a .arg <;> simp [Prec.isArg, paren_false]
  | lam n t b bi =>
    simp only [pr, needsParen, Option.bind_eq_bind]
    split
    · cases pr bare sc t .term <;> cases pr bare (n :: sc) b .term <;>
        simp [Prec.isTerm, paren_false]
    · simp
  | forallE n t b bi =>
    simp only [pr, needsParen, Option.bind_eq_bind]
    split
    · cases pr bare sc t .simple <;> cases pr bare (n :: sc) b .term <;>
        simp [Prec.isTerm, paren_false]
    · split
      · cases pr bare sc t .term <;> cases pr bare (n :: sc) b .term <;>
          simp [Prec.isTerm, paren_false]
      · simp

/-- What may follow a term: nothing, or a closing bracket. -/
def FollowsTerm (rest : List Tok) : Prop :=
  ∀ t, rest.head? = some t → t = .rparen ∨ t = .rbrace ∨ t = .rbrack ∨ t = .rstrict

/-- What may follow a term before `→`: what may follow a term, or `→`. -/
def FollowsSimple (rest : List Tok) : Prop :=
  ∀ t, rest.head? = some t → t = .rparen ∨ t = .rbrace ∨ t = .rbrack ∨ t = .rstrict ∨ t = .arrow

/-- The application of `h` to the arguments `as`, in order. -/
def mkApps (h : Expr) (as : List Expr) : Expr := as.foldl .app h

/-- `ta` is an argument's tokens, which `psAtom` reads back as `a` before anything but `.{`. -/
def ArgOk (sc : List Name) (a : Expr) (ta : List Tok) : Prop :=
  atomStart ta = true ∧ ∀ rest, rest.head? ≠ some .dotBrace → ∀ f, 4 * ta.length + 1 ≤ f →
    psAtom f sc (ta ++ rest) = some (a, rest)

/-- Each argument of `as` has the tokens of `tas` in the same place, which `psAtom` reads back. -/
inductive ArgsOk (sc : List Name) : List Expr → List (List Tok) → Prop
  | nil : ArgsOk sc [] []
  | cons {a : Expr} {ta : List Tok} {as : List Expr} {tas : List (List Tok)} :
      ArgOk sc a ta → ArgsOk sc as tas → ArgsOk sc (a :: as) (ta :: tas)

theorem atomStart_append {ts : List Tok} (h : atomStart ts = true) (r : List Tok) :
    atomStart (ts ++ r) = true := by
  cases ts with
  | nil => simp [atomStart] at h
  | cons t ts => cases t <;> simp_all [atomStart]

theorem length_pos_of_atomStart {ts : List Tok} (h : atomStart ts = true) : 1 ≤ ts.length := by
  cases ts with
  | nil => simp [atomStart] at h
  | cons => simp

theorem noUniv_of_atomStart {ts : List Tok} (h : atomStart ts = true) :
    ts.head? ≠ some .dotBrace := by
  cases ts with
  | nil => simp [atomStart] at h
  | cons t ts => cases t <;> simp_all [atomStart]

theorem noUniv_flatten {sc : List Name} {as : List Expr} {tas : List (List Tok)}
    (h : ArgsOk sc as tas) {rest : List Tok} (hr : rest.head? ≠ some .dotBrace) :
    (tas.flatten ++ rest).head? ≠ some .dotBrace := by
  cases h with
  | nil => simpa using hr
  | @cons a ta as tas ha _ =>
    rw [List.flatten_cons, List.append_assoc]
    have := ha.1
    cases ta with
    | nil => simp [atomStart] at this
    | cons t ts => cases t <;> simp_all [atomStart]

theorem atomStart_false_of_follows {rest : List Tok} (h : FollowsSimple rest) :
    atomStart rest = false := by
  cases rest with
  | nil => rfl
  | cons t r =>
    rcases h t rfl with h | h | h | h | h <;> subst h <;> rfl

theorem noUniv_of_follows {rest : List Tok} (h : FollowsSimple rest) :
    rest.head? ≠ some .dotBrace := by
  cases rest with
  | nil => simp
  | cons t r => rcases h t rfl with h | h | h | h | h <;> subst h <;> simp

theorem followsSimple_of_term {rest : List Tok} (h : FollowsTerm rest) : FollowsSimple rest :=
  fun t ht => by rcases h t ht with h | h | h | h <;> simp [h]

theorem psTerm_kwFun (f : Nat) (sc : List Name) (ts : List Tok) :
    psTerm (f + 1) sc (.kwFun :: ts) = (psBinder f sc ts).bind fun (bi, n, t, ts) =>
      match ts with
      | .darrow :: ts => (psTerm f (n :: sc) ts).bind fun (b, ts) => some (.lam n t b bi, ts)
      | _ => none := rfl

theorem psTerm_pi (f : Nat) (sc : List Name) (ts : List Tok) :
    psTerm (f + 1) sc (.pi :: ts) = (psBinder f sc ts).bind fun (bi, n, t, ts) =>
      match ts with
      | .comma :: ts => (psTerm f (n :: sc) ts).bind fun (b, ts) => some (.forallE n t b bi, ts)
      | _ => none := rfl

theorem psBinder_eq (f : Nat) (sc : List Name) (o : Tok) (n : Name) (ts : List Tok) :
    psBinder (f + 1) sc (o :: .ident n :: .colon :: ts) =
      match opener o with
      | some bi => (psTerm f sc ts).bind fun (t, ts) =>
        match ts with
        | c :: ts => if c = closer bi then some (bi, n, t, ts) else none
        | [] => none
      | none => none := rfl

theorem psAtom_lparen (f : Nat) (sc : List Name) (ts : List Tok) :
    psAtom (f + 1) sc (.lparen :: ts) = (psTerm f sc ts).bind fun (e, ts) =>
      match ts with
      | .rparen :: ts => some (e, ts)
      | _ => none := rfl

theorem psTerm_default {f : Nat} {sc : List Name} {ts : List Tok} (h1 : ∀ r, ts ≠ .kwFun :: r)
    (h2 : ∀ r, ts ≠ .pi :: r) :
    psTerm (f + 1) sc ts = (psSimple f sc ts).bind fun (a, ts) =>
      match ts with
      | .arrow :: ts => (psTerm f (.anonymous :: sc) ts).bind fun (b, ts) =>
          some (.forallE .anonymous a b .default, ts)
      | ts => some (a, ts) := by
  cases ts with
  | nil => rfl
  | cons t ts => cases t <;> first | rfl | simp_all

theorem psSimple_default {f : Nat} {sc : List Name} {ts : List Tok} (h : atomStart ts = true) :
    psSimple (f + 1) sc ts = (psAtom f sc ts).bind fun (h, ts) => psArgs f sc h ts := by
  cases ts with
  | nil => simp [atomStart] at h
  | cons t ts => cases t <;> first | rfl | simp_all [atomStart]

/-- The arguments' loop reads back the arguments, before what cannot start one or `.{`. -/
theorem psArgs_loop {sc : List Name} {as : List Expr} {tas : List (List Tok)}
    (h : ArgsOk sc as tas) (g : Expr) (rest : List Tok)
    (hr : rest.head? ≠ some .dotBrace) (hs : atomStart rest = false) :
    ∀ f, 4 * tas.flatten.length + 2 ≤ f → psArgs f sc g (tas.flatten ++ rest) = some (mkApps g as, rest) := by
  induction h generalizing g with
  | nil =>
    intro f hf
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    simp [psArgs, hs, mkApps]
  | @cons a ta as tas ha _ ih =>
    intro f hf
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    have hlen := length_pos_of_atomStart ha.1
    simp only [List.flatten_cons, List.length_append] at hf
    rw [List.flatten_cons, List.append_assoc]
    simp only [psArgs, atomStart_append ha.1, ite_true, Option.bind_eq_bind]
    rw [ha.2 _ (noUniv_flatten ‹_› hr) f (by omega), Option.bind_some]
    exact ih (.app g a) f (by omega)

/-! ## The claims, at each precedence -/

/-- At an argument's precedence, `psAtom` reads `e` back. -/
def ClaimA (bare : Name → Bool) (sc : List Name) (e : Expr) : Prop :=
  ∀ ts, pr bare sc e .arg = some ts → ArgOk sc e ts

/-- At a function's precedence, `psSimple` reads back `e` applied to the arguments after it. -/
def ClaimH (bare : Name → Bool) (sc : List Name) (e : Expr) : Prop :=
  ∀ ts, pr bare sc e .head = some ts → ∀ as tas, ArgsOk sc as tas →
    ∀ rest, rest.head? ≠ some .dotBrace → atomStart rest = false →
    ∀ f, 4 * (ts.length + tas.flatten.length) + 2 ≤ f →
    psSimple f sc (ts ++ tas.flatten ++ rest) = some (mkApps e as, rest)

/-- Before `→`, `psSimple` reads `e` back. -/
def ClaimS (bare : Name → Bool) (sc : List Name) (e : Expr) : Prop :=
  ∀ ts, pr bare sc e .simple = some ts → ∀ rest, FollowsSimple rest → ∀ f, 4 * ts.length + 2 ≤ f →
    psSimple f sc (ts ++ rest) = some (e, rest)

/-- At the lowest precedence, `psTerm` reads `e` back. -/
def ClaimT (bare : Name → Bool) (sc : List Name) (e : Expr) : Prop :=
  ∀ ts, pr bare sc e .term = some ts → ∀ rest, FollowsTerm rest → ∀ f, 4 * ts.length + 3 ≤ f →
    psTerm f sc (ts ++ rest) = some (e, rest)

variable {bare : Name → Bool} {sc : List Name} {e : Expr}

theorem claimH_of_A (hpe : pr bare sc e .head = pr bare sc e .arg) (hA : ClaimA bare sc e) :
    ClaimH bare sc e := by
  intro ts hts as tas htas rest hr hs f hf
  rw [hpe] at hts
  have ha := hA ts hts
  obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  have hlen := length_pos_of_atomStart ha.1
  rw [List.append_assoc, psSimple_default (atomStart_append ha.1 _),
    ha.2 _ (noUniv_flatten htas hr) f (by omega), Option.bind_some]
  exact psArgs_loop htas e rest hr hs f (by omega)

theorem claimS_of_H (hpe : pr bare sc e .simple = pr bare sc e .head) (hH : ClaimH bare sc e) :
    ClaimS bare sc e := by
  intro ts hts rest hr f hf
  rw [hpe] at hts
  have := hH ts hts [] [] .nil rest (noUniv_of_follows hr) (atomStart_false_of_follows hr) f
    (by simpa using hf)
  simpa [mkApps] using this

theorem claimT_of_S (hpe : pr bare sc e .term = pr bare sc e .simple)
    (hhead : ∀ ts, pr bare sc e .term = some ts → ∃ t ts', ts = t :: ts' ∧ t ≠ .kwFun ∧ t ≠ .pi)
    (hS : ClaimS bare sc e) : ClaimT bare sc e := by
  intro ts hts rest hr f hf
  obtain ⟨t, ts', rfl, h1, h2⟩ := hhead _ hts
  rw [hpe] at hts
  obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  rw [psTerm_default (by simp [h1]) (by simp [h2]),
    hS _ hts rest (followsSimple_of_term hr) f (by omega), Option.bind_some]
  cases rest with
  | nil => rfl
  | cons u r => rcases hr u rfl with h | h | h | h <;> subst h <;> rfl

theorem claimA_of_T (hpe : pr bare sc e .arg = (pr bare sc e .term).map (paren true))
    (hT : ClaimT bare sc e) : ClaimA bare sc e := by
  intro ts hts
  rw [hpe, Option.map_eq_some_iff] at hts
  obtain ⟨ts₀, h₀, rfl⟩ := hts
  refine ⟨rfl, fun rest _ f hf => ?_⟩
  obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp [paren_true] at hf; omega⟩
  simp only [paren_true, List.cons_append, List.append_assoc, List.nil_append]
  rw [psAtom_lparen, hT ts₀ h₀ (.rparen :: rest) (fun t ht => by simp at ht; simp [← ht]) f
      (by simp [paren_true] at hf; omega),
    Option.bind_some]

/-- A term whose printed form is the same at every precedence: its claims follow from `psAtom`
reading it back. -/
theorem claims_of_atom (hp : ∀ p, pr bare sc e p = pr bare sc e .arg) (hA : ClaimA bare sc e) :
    ClaimA bare sc e ∧ ClaimH bare sc e ∧ ClaimS bare sc e ∧ ClaimT bare sc e := by
  have hH := claimH_of_A (hp .head) hA
  have hS := claimS_of_H ((hp .simple).trans (hp .head).symm) hH
  refine ⟨hA, hH, hS, claimT_of_S ((hp .term).trans (hp .simple).symm) ?_ hS⟩
  intro ts hts
  rw [hp] at hts
  have := (hA ts hts).1
  cases ts with
  | nil => simp [atomStart] at this
  | cons t ts => exact ⟨t, ts, rfl, by cases t <;> simp_all [atomStart]⟩

theorem opener_openTok (bi : BinderInfo) : opener (openTok bi) = some bi := by cases bi <;> rfl

theorem followsTerm_closer (bi : BinderInfo) (r : List Tok) : FollowsTerm (closer bi :: r) := by
  intro t ht; cases bi <;> simp_all [closer]

theorem followsTerm_rparen (r : List Tok) : FollowsTerm (.rparen :: r) := by
  intro t ht; simp_all

/-- `psTerm` reads back `fun` and `∀` with a named binder, from reading back its type and body. -/
theorem psTerm_binder {kw sep : Tok} (hkw : kw = .kwFun ∧ sep = .darrow ∨ kw = .pi ∧ sep = .comma)
    {n : Name} {t b : Expr} {bi : BinderInfo} {tt tb : List Tok} (hT : ClaimT bare sc t)
    (htt : pr bare sc t .term = some tt) (hB : ClaimT bare (n :: sc) b)
    (htb : pr bare (n :: sc) b .term = some tb) (rest : List Tok) (hr : FollowsTerm rest) (f : Nat)
    (hf : 4 * (kw :: binderToks bi n tt ++ sep :: tb).length + 3 ≤ f) :
    psTerm f sc ((kw :: binderToks bi n tt ++ sep :: tb) ++ rest) =
      some (if kw = .kwFun then .lam n t b bi else .forallE n t b bi, rest) := by
  obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 + 1 := ⟨f - 2, by omega⟩
  simp only [binderToks, List.length_cons, List.length_append, List.length_nil] at hf
  have hbinder : psBinder (f + 1) sc (binderToks bi n tt ++ sep :: tb ++ rest) =
      some (bi, n, t, sep :: tb ++ rest) := by
    simp only [binderToks, List.cons_append, List.append_assoc]
    rw [psBinder_eq, opener_openTok]
    simp only []
    rw [hT tt htt _ (followsTerm_closer bi _) f (by omega)]
    simp
  have hbody := hB tb htb rest hr (f + 1) (by omega)
  rcases hkw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [List.cons_append]
    rw [psTerm_kwFun]
    simp only [List.append_assoc, List.cons_append] at hbinder ⊢
    rw [hbinder]
    simp [hbody]
  · simp only [List.cons_append]
    rw [psTerm_pi]
    simp only [List.append_assoc, List.cons_append] at hbinder ⊢
    rw [hbinder]
    simp [hbody]

theorem pr_eq_of_needsParen {p q : Prec} (h : needsParen e p = needsParen e q) :
    pr bare sc e p = pr bare sc e q := by
  rw [pr_prec _ _ _ p, pr_prec _ _ _ q, h]

/-- At a function's or an argument's precedence, a printed term starts as an argument does. -/
theorem atomStart_pr (bare : Name → Bool) (e : Expr) :
    ∀ (sc : List Name) (p : Prec) {ts : List Tok}, p.tight = true → pr bare sc e p = some ts →
      atomStart ts = true := by
  induction e with
  | bvar i =>
    intro sc p ts _ h
    simp only [pr] at h
    split at h
    · split at h
      · simp at h; subst h; rfl
      · simp at h
    · simp at h
  | const c us =>
    intro sc p ts _ h
    simp only [pr] at h
    split at h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨u, _, rfl⟩ := h
      split <;> rfl
    · simp at h
  | sort l =>
    intro sc p ts hp h
    simp only [pr, Option.map_eq_some_iff, hp, Bool.and_true] at h
    obtain ⟨t, ht, rfl⟩ := h
    cases hz : isZero l
    · rfl
    · have : l = .zero := by cases l <;> simp_all [isZero]
      subst this
      simp [prSort] at ht; subst ht; rfl
  | lit l =>
    intro sc p ts hp h
    cases l <;> simp [pr, hp] at h <;> subst h <;> rfl
  | app f a ihf iha =>
    intro sc p ts hp h
    simp only [pr, Option.bind_eq_bind] at h
    cases htf : pr bare sc f .head <;> cases hta : pr bare sc a .arg <;> simp [htf, hta] at h
    subst h
    cases p
    · simp [Prec.tight] at hp
    · simp [Prec.tight] at hp
    · exact atomStart_append (ihf sc .head rfl htf) _
    · rfl
  | lam | forallE =>
    intro sc p ts hp h
    have hpt : (!p.isTerm) = true := by cases p <;> simp_all [Prec.tight, Prec.isTerm]
    rw [pr_prec] at h
    simp only [needsParen, hpt, Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h
    rfl
  | fvar | mvar | letE | mdata | proj => intro sc p ts _ h; simp [pr] at h

theorem atomStart_pr_head (bare : Name → Bool) (e : Expr) (sc : List Name) {ts : List Tok}
    (h : pr bare sc e .head = some ts) : atomStart ts = true :=
  atomStart_pr bare e sc .head rfl h

/-- Before `→`, a printed term starts with neither `fun` nor `∀`. -/
theorem head_pr_simple (bare : Name → Bool) (e : Expr) (sc : List Name) {ts : List Tok}
    (h : pr bare sc e .simple = some ts) : ∃ t ts', ts = t :: ts' ∧ t ≠ .kwFun ∧ t ≠ .pi := by
  have notStart : ∀ {ts : List Tok}, atomStart ts = true →
      ∃ t ts', ts = t :: ts' ∧ t ≠ .kwFun ∧ t ≠ .pi := by
    intro ts h
    cases ts with
    | nil => simp [atomStart] at h
    | cons t ts => exact ⟨t, ts, rfl, by cases t <;> simp_all [atomStart]⟩
  cases e with
  | app f a =>
    rw [pr_eq_of_needsParen (q := .head) (by simp [needsParen, Prec.isArg])] at h
    exact notStart (atomStart_pr_head bare _ sc h)
  | sort l =>
    simp only [pr, Prec.tight, Bool.and_false, paren_false, Option.map_eq_some_iff] at h
    obtain ⟨t, ht, rfl⟩ := h
    cases l with
    | zero => simp [prSort] at ht; subst ht; exact ⟨_, _, rfl, by simp, by simp⟩
    | succ l =>
      simp only [prSort] at ht
      split at ht
      · simp at ht; subst ht; exact ⟨_, _, rfl, by simp, by simp⟩
      · simp only [Option.map_eq_some_iff] at ht
        obtain ⟨_, _, rfl⟩ := ht; exact ⟨_, _, rfl, by simp, by simp⟩
    | max | imax | param | mvar =>
      simp only [prSort, Option.map_eq_some_iff] at ht
      obtain ⟨_, _, rfl⟩ := ht; exact ⟨_, _, rfl, by simp, by simp⟩
  | lit l =>
    cases l <;> simp [pr, Prec.tight, paren_false] at h <;> subst h <;>
      exact ⟨_, _, rfl, by simp, by simp⟩
  | bvar | const | lam | forallE | fvar | mvar | letE | mdata | proj =>
    rw [pr_eq_of_needsParen (q := .arg) (by simp [needsParen, Prec.isTerm])] at h
    exact notStart (atomStart_pr bare _ sc .arg rfl h)

/-- A binder form's claims follow from reading it back at the lowest precedence. -/
theorem claims_of_binder (hp : ∀ p, needsParen e p = (!p.isTerm)) (hT : ClaimT bare sc e) :
    ClaimA bare sc e ∧ ClaimH bare sc e ∧ ClaimS bare sc e ∧ ClaimT bare sc e := by
  have hA := claimA_of_T (by rw [pr_prec _ _ _ .arg, hp]; rfl) hT
  have hH := claimH_of_A (pr_eq_of_needsParen (by rw [hp, hp]; rfl)) hA
  exact ⟨hA, hH, claimS_of_H (pr_eq_of_needsParen (by rw [hp, hp]; rfl)) hH, hT⟩

theorem psSimple_kwType (f : Nat) (sc : List Name) (ts : List Tok) :
    psSimple (f + 1) sc (.kwType :: ts) =
      if levelStart ts then
        (psLevelAtom (2 * ts.length + 2) ts).map fun (l, ts) => (.sort (.succ l), ts)
      else some (.sort (.succ .zero), ts) := rfl

theorem psSimple_kwSort (f : Nat) (sc : List Name) (ts : List Tok) :
    psSimple (f + 1) sc (.kwSort :: ts) =
      (psLevelAtom (2 * ts.length + 2) ts).map fun (l, ts) => (.sort l, ts) := rfl

theorem pr_sort_eq {bare : Name → Bool} {sc : List Name} {l : Level} {p : Prec}
    (hz : isZero l = false) (hp : p.tight = false) : pr bare sc (.sort l) p = prSort l := by
  simp [pr, hz, hp, paren_false_eq]

theorem prSort_cases {l : Level} {ts : List Tok} (h : prSort l = some ts) :
    (l = .zero ∧ ts = [.kwProp]) ∨ (l = .succ .zero ∧ ts = [.kwType]) ∨
    (∃ l' tl, l = .succ l' ∧ prLevel l' true = some tl ∧ ts = .kwType :: tl) ∨
    (∃ tl, prLevel l true = some tl ∧ ts = .kwSort :: tl) := by
  cases l with
  | zero => simp [prSort] at h; exact .inl ⟨rfl, h.symm⟩
  | succ l' =>
    simp only [prSort] at h
    split at h
    · next h0 =>
      have : l' = .zero := by cases l' <;> simp_all [isZero]
      subst this
      simp at h
      exact .inr (.inl ⟨rfl, h.symm⟩)
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨tl, htl, rfl⟩ := h
      exact .inr (.inr (.inl ⟨l', tl, rfl, htl, rfl⟩))
  | max | imax | param | mvar =>
    simp only [prSort, Option.map_eq_some_iff] at h
    obtain ⟨tl, htl, rfl⟩ := h
    exact .inr (.inr (.inr ⟨tl, htl, rfl⟩))

/-- Every claim holds of every term, under every scope. -/
theorem claims (bare : Name → Bool) (e : Expr) : ∀ sc : List Name,
    ClaimA bare sc e ∧ ClaimH bare sc e ∧ ClaimS bare sc e ∧ ClaimT bare sc e := by
  induction e with
  | bvar i =>
    intro sc
    refine claims_of_atom (fun p => by simp [pr]) fun ts hts => ?_
    simp only [pr] at hts
    split at hts
    · next n hn =>
      split at hts
      · next hok =>
        simp only [Option.some.injEq] at hts; subst hts
        simp only [Bool.and_eq_true, beq_iff_eq] at hok
        refine ⟨rfl, fun rest _ f hf => ?_⟩
        obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
        simp [psAtom, hok.2]
      · simp at hts
    · simp at hts
  | const c us =>
    intro sc
    refine claims_of_atom (fun p => by simp [pr]) fun ts hts => ?_
    simp only [pr] at hts
    split at hts
    · simp only [Option.map_eq_some_iff] at hts
      obtain ⟨u, hu, rfl⟩ := hts
      split
      · next hb =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hb
        refine ⟨rfl, fun rest hr f hf => ?_⟩
        obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
        simp [psAtom, hb.2, psUnivs_prUnivs hu rest hr]
      · refine ⟨rfl, fun rest hr f hf => ?_⟩
        obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
        simp [psAtom, psUnivs_prUnivs hu rest hr]
    · simp at hts
  | sort l =>
    intro sc
    cases hz : isZero l with
    | true =>
      have hl : l = .zero := by cases l <;> simp_all [isZero]
      subst hl
      refine claims_of_atom (fun p => by simp [pr, isZero, prSort]) fun ts hts => ?_
      simp only [pr, prSort, isZero, Option.map_some, Bool.not_true, Bool.false_and, paren_false,
        Option.some.injEq] at hts
      subst hts
      refine ⟨rfl, fun rest _ f hf => ?_⟩
      obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      rfl
    | false =>
      have hS : ClaimS bare sc (.sort l) := by
        intro ts hts rest hr f hf
        rw [pr_sort_eq hz rfl] at hts
        obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
        rcases prSort_cases hts with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨l', tl, rfl, htl, rfl⟩ |
            ⟨tl, htl, rfl⟩
        · simp [isZero] at hz
        · have : levelStart rest = false := by
            cases rest with
            | nil => rfl
            | cons t r => rcases hr t rfl with h | h | h | h | h <;> subst h <;> rfl
          rw [List.cons_append, List.nil_append, psSimple_kwType]
          simp [this]
        · rw [List.cons_append, psSimple_kwType]
          simp only [levelStart_prLevel htl, ite_true]
          rw [(psLevel_prLevel l').1 tl htl _ (by simp; omega) rest]
          rfl
        · rw [List.cons_append, psSimple_kwSort, (psLevel_prLevel _).1 tl htl _ (by simp; omega) rest]
          rfl
      have hT := claimT_of_S (pr_eq_of_needsParen (by simp [needsParen, hz, Prec.tight]))
        (fun ts hts => by
          rw [pr_sort_eq hz rfl] at hts
          rcases prSort_cases hts with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨l', tl, rfl, htl, rfl⟩ |
              ⟨tl, htl, rfl⟩
          · simp [isZero] at hz
          all_goals exact ⟨_, _, rfl, by simp, by simp⟩) hS
      have hA := claimA_of_T (by rw [pr_prec _ _ _ .arg]; simp [needsParen, hz, Prec.tight]) hT
      exact ⟨hA, claimH_of_A (pr_eq_of_needsParen (by simp [needsParen, hz, Prec.tight])) hA, hS, hT⟩
  | lit l =>
    intro sc
    cases l with
    | strVal s =>
      refine claims_of_atom (fun p => by simp [pr]) fun ts hts => ?_
      simp only [pr, Option.some.injEq] at hts; subst hts
      refine ⟨rfl, fun rest _ f hf => ?_⟩
      obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      rfl
    | natVal n =>
      have hS : ClaimS bare sc (.lit (.natVal n)) := by
        intro ts hts rest hr f hf
        simp only [pr, Prec.tight, paren_false, Option.some.injEq] at hts; subst hts
        obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
        rfl
      have hT := claimT_of_S (pr_eq_of_needsParen (by simp [needsParen, Prec.tight]))
        (fun ts hts => by
          simp only [pr, Prec.tight, paren_false, Option.some.injEq] at hts; subst hts
          exact ⟨_, _, rfl, by simp, by simp⟩) hS
      have hA := claimA_of_T (by rw [pr_prec _ _ _ .arg]; simp [needsParen, Prec.tight]) hT
      exact ⟨hA, claimH_of_A (pr_eq_of_needsParen (by simp [needsParen, Prec.tight])) hA, hS, hT⟩
  | app f a ihf iha =>
    intro sc
    have hH : ClaimH bare sc (.app f a) := by
      intro ts hts as tas htas rest hr hs k hk
      simp only [pr, Option.bind_eq_bind] at hts
      cases htf : pr bare sc f .head <;> cases hta : pr bare sc a .arg <;>
        simp [htf, hta, paren_false, Prec.isArg] at hts
      subst hts
      rename_i tf ta
      have ha := (iha sc).1 ta hta
      have := (ihf sc).2.1 tf htf (a :: as) (ta :: tas) (.cons ha htas) rest hr hs k
        (by simp only [List.flatten_cons, List.length_append] at hk ⊢; omega)
      simpa [mkApps, List.append_assoc] using this
    have hS := claimS_of_H (pr_eq_of_needsParen (by simp [needsParen, Prec.isArg])) hH
    have hT := claimT_of_S (pr_eq_of_needsParen (by simp [needsParen, Prec.isArg]))
      (fun ts hts => head_pr_simple bare (.app f a) sc
        (by rw [pr_eq_of_needsParen (p := .simple) (q := .term) (by simp [needsParen, Prec.isArg])]
            exact hts)) hS
    have hA := claimA_of_T (by rw [pr_prec _ _ _ .arg]; simp [needsParen, Prec.isArg]) hT
    exact ⟨hA, hH, hS, hT⟩
  | lam n t b bi iht ihb =>
    intro sc
    have hT : ClaimT bare sc (.lam n t b bi) := by
      intro ts hts rest hr f hf
      simp only [pr, Option.bind_eq_bind] at hts
      split at hts
      · cases htt : pr bare sc t .term <;> cases htb : pr bare (n :: sc) b .term <;>
          simp [htt, htb, paren_false, Prec.isTerm] at hts
        subst hts
        rename_i tt tb
        have := psTerm_binder (.inl ⟨rfl, rfl⟩) ((iht sc).2.2.2) htt ((ihb (n :: sc)).2.2.2) htb
          rest hr f hf
        simpa using this
      · simp at hts
    exact claims_of_binder (fun p => by cases p <;> rfl) hT
  | forallE n t b bi iht ihb =>
    intro sc
    have hT : ClaimT bare sc (.forallE n t b bi) := by
      intro ts hts rest hr f hf
      simp only [pr, Option.bind_eq_bind] at hts
      split at hts
      · next harrow =>
        have hn : n = .anonymous ∧ bi = .default := by
          cases n <;> cases bi <;> simp_all [isArrow]
        obtain ⟨rfl, rfl⟩ := hn
        cases htt : pr bare sc t .simple <;> cases htb : pr bare (.anonymous :: sc) b .term <;>
          simp [htt, htb, paren_false, Prec.isTerm] at hts
        subst hts
        rename_i tt tb
        obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
        simp only [List.length_append, List.length_cons] at hf
        obtain ⟨t0, ts0, htt0, h1, h2⟩ := head_pr_simple bare t sc htt
        rw [List.append_assoc, psTerm_default (by simp [htt0, h1]) (by simp [htt0, h2]),
          (iht sc).2.2.1 tt htt _ (fun u hu => by simp at hu; simp [hu]) f (by omega),
          Option.bind_some]
        simp only [List.cons_append]
        rw [(ihb _).2.2.2 tb htb rest hr f (by omega)]
        rfl
      · split at hts
        · cases htt : pr bare sc t .term <;> cases htb : pr bare (n :: sc) b .term <;>
            simp [htt, htb, paren_false, Prec.isTerm] at hts
          subst hts
          rename_i tt tb
          have := psTerm_binder (.inr ⟨rfl, rfl⟩) ((iht sc).2.2.2) htt ((ihb (n :: sc)).2.2.2) htb
            rest hr f hf
          simpa using this
        · simp at hts
    exact claims_of_binder (fun p => by cases p <;> rfl) hT
  | fvar | mvar | letE | mdata | proj =>
    intro sc
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro ts hts <;> simp [pr] at hts

end LeanIntent.Print
