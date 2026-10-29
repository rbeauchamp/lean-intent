import LeanIntent.Print.Printable
import LeanIntent.Print.Canon

/-!
# An audited printer for Lean terms

`print` writes a Lean term as text in Lean's own syntax, and `parse` reads such text back. The
printer is audited: `parse_print` proves that `parse` reads back from every text `print` writes the
very term it printed, for every term, so two terms that print the same are equal
(`print_injective`), and what a reader is shown determines the term. `print_isSome_iff` proves which
terms it prints: exactly those `Printable` admits; it refuses every other term rather than printing
it lossily.

The grammar `parse` reads is the one `LeanIntent.Print.Term` describes, a closed subset of Lean's
syntax for terms, written with the tokens of `LeanIntent.Print.Token`. That Lean's own parser and
elaborator read the printed text as the same term is not a theorem here, since they are programs
outside this library; `LeanIntent.Render` checks it for each term it shows, and refuses to show a
term for which it fails.

`print` takes two choices, neither of which changes what `parse` reads back: `bare`, the constants
written without `@` when no binder in scope has their name, and `esc`, further name components to
write escaped between `«` and `»`, such as those that are tokens of the reader's grammar.
-/

namespace LeanIntent.Print

open Lean (Name Level Expr BinderInfo)

/-- `e` printed as text, or `none` when the printer refuses it. -/
def print (bare : Name → Bool) (esc : String → Bool) (e : Expr) : Option String :=
  (pr bare [] e .term).map fun ts => String.ofList (render esc ts)

/-- The term a text is, by the printer's grammar, or `none` when it is not one. -/
def parse (s : String) : Option Expr := do
  let ts ← lex s.toList
  let (e, rest) ← psTerm (4 * ts.length + 3) [] ts
  if rest.isEmpty then some e else none

/-! ## The printer writes only tokens the lexer reads back -/

/-- Every token of a list can be written and read back. -/
def WFs (ts : List Tok) : Prop := ∀ t ∈ ts, t.WF

theorem wfs_nil : WFs [] := fun _ h => nomatch h

theorem wfs_cons {t : Tok} {ts : List Tok} (h : t.WF) (hs : WFs ts) : WFs (t :: ts) := by
  intro u hu
  rcases List.mem_cons.mp hu with rfl | hu
  · exact h
  · exact hs u hu

theorem wfs_append {a b : List Tok} (ha : WFs a) (hb : WFs b) : WFs (a ++ b) := by
  intro t ht
  rcases List.mem_append.mp ht with h | h
  · exact ha t h
  · exact hb t h

theorem wfs_paren (b : Bool) {ts : List Tok} (h : WFs ts) : WFs (paren b ts) := by
  cases b
  · exact h
  · exact wfs_cons trivial (wfs_append h (wfs_cons trivial wfs_nil))

theorem wf_ident_of_atomOk {n : Name} (h : atomOk n = true) : (Tok.ident n).WF := by
  match n, h with
  | .str .anonymous s, h =>
    refine ⟨[s], rfl, by simp, fun s' hs' => ?_⟩
    simp only [List.mem_singleton] at hs'
    subst hs'
    simp only [atomOk, compOk, Bool.or_eq_true, Bool.not_eq_true'] at h
    rcases h with h | h
    · exact .inl h
    · exact .inr fun hm => by simp [hm] at h

theorem wf_ident_of_nameOk {n : Name} (h : nameOk n = true) : (Tok.ident n).WF := by
  unfold nameOk at h
  split at h
  · next ss hss =>
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
      List.all_eq_true] at h
    refine ⟨ss, hss, h.1, fun s hs => ?_⟩
    have := h.2 s hs
    simp only [compOk, Bool.or_eq_true, Bool.not_eq_true'] at this
    rcases this with h' | h'
    · exact .inl h'
    · exact .inr fun hm => by simp [hm] at h'
  · simp at h

theorem prLevel_wf (l : Level) (atom : Bool) {ts : List Tok} (h : prLevel l atom = some ts) :
    WFs ts := by
  induction l generalizing atom ts with
  | zero => simp [prLevel] at h; subst h; exact wfs_cons trivial wfs_nil
  | succ l ih =>
    simp only [prLevel] at h
    split at h
    · simp at h; subst h; exact wfs_cons trivial wfs_nil
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨t, ht, rfl⟩ := h
      exact wfs_paren _ (wfs_append (ih true ht) (wfs_cons trivial (wfs_cons trivial wfs_nil)))
  | max a b iha ihb | imax a b iha ihb =>
    simp only [prLevel, Option.bind_eq_bind] at h
    cases ha : prLevel a true <;> cases hb : prLevel b true <;> simp [ha, hb] at h
    subst h
    exact wfs_paren _ (wfs_cons trivial (wfs_append (iha true ha) (ihb true hb)))
  | param n =>
    simp only [prLevel] at h
    split at h
    · next hn => simp at h; subst h; exact wfs_cons (wf_ident_of_atomOk hn) wfs_nil
    · simp at h
  | mvar => simp [prLevel] at h

theorem prLevels_wf : (us : List Level) → {ts : List Tok} → prLevels us = some ts → WFs ts
  | [], _, h => by simp [prLevels] at h; subst h; exact wfs_nil
  | [l], _, h => prLevel_wf l false h
  | l :: l' :: ls, _, h => by
    simp only [prLevels, Option.bind_eq_bind] at h
    cases ht : prLevel l false <;> cases hr : prLevels (l' :: ls) <;> simp [ht, hr] at h
    subst h
    exact wfs_append (prLevel_wf l false ht) (wfs_cons trivial (prLevels_wf (l' :: ls) hr))

theorem prUnivs_wf {us : List Level} {ts : List Tok} (h : prUnivs us = some ts) : WFs ts := by
  cases us with
  | nil => simp [prUnivs] at h; subst h; exact wfs_nil
  | cons u us =>
    simp only [prUnivs, Option.map_eq_some_iff] at h
    obtain ⟨t, ht, rfl⟩ := h
    exact wfs_cons trivial (wfs_append (prLevels_wf _ ht) (wfs_cons trivial wfs_nil))

theorem binderToks_wf (bi : BinderInfo) {n : Name} (hn : atomOk n = true) {t : List Tok}
    (ht : WFs t) : WFs (binderToks bi n t) :=
  wfs_cons (by cases bi <;> trivial) (wfs_cons (wf_ident_of_atomOk hn)
    (wfs_cons trivial (wfs_append ht (wfs_cons (by cases bi <;> trivial) wfs_nil))))

/-- Every token the printer writes can be written and read back. -/
theorem pr_wf (bare : Name → Bool) (e : Expr) :
    ∀ (sc : List Name) (p : Prec) {ts : List Tok}, pr bare sc e p = some ts → WFs ts := by
  induction e with
  | bvar i =>
    intro sc p ts h
    simp only [pr] at h
    split at h
    · split at h
      · next hok =>
        simp only [Bool.and_eq_true] at hok
        simp at h; subst h; exact wfs_cons (wf_ident_of_atomOk hok.1) wfs_nil
      · simp at h
    · simp at h
  | const c us =>
    intro sc p ts h
    simp only [pr] at h
    split at h
    · next hc =>
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨u, hu, rfl⟩ := h
      split
      · exact wfs_cons (wf_ident_of_nameOk hc) (prUnivs_wf hu)
      · exact wfs_cons trivial (wfs_cons (wf_ident_of_nameOk hc) (prUnivs_wf hu))
    · simp at h
  | sort l =>
    intro sc p ts h
    simp only [pr, Option.map_eq_some_iff] at h
    obtain ⟨t, ht, rfl⟩ := h
    refine wfs_paren _ ?_
    cases l with
    | zero => simp [prSort] at ht; subst ht; exact wfs_cons trivial wfs_nil
    | succ l =>
      simp only [prSort] at ht
      split at ht
      · simp at ht; subst ht; exact wfs_cons trivial wfs_nil
      · simp only [Option.map_eq_some_iff] at ht
        obtain ⟨t', ht', rfl⟩ := ht
        exact wfs_cons trivial (prLevel_wf l true ht')
    | max | imax | param | mvar =>
      simp only [prSort, Option.map_eq_some_iff] at ht
      obtain ⟨t', ht', rfl⟩ := ht
      exact wfs_cons trivial (prLevel_wf _ true ht')
  | lit l =>
    intro sc p ts h
    cases l <;> simp [pr] at h <;> subst h
    · exact wfs_paren _ (wfs_cons trivial (wfs_cons trivial wfs_nil))
    · exact wfs_cons trivial wfs_nil
  | app f a ihf iha =>
    intro sc p ts h
    simp only [pr, Option.bind_eq_bind] at h
    cases hf : pr bare sc f .head <;> cases ha : pr bare sc a .arg <;> simp [hf, ha] at h
    subst h
    exact wfs_paren _ (wfs_append (ihf sc _ hf) (iha sc _ ha))
  | lam n t b bi iht ihb =>
    intro sc p ts h
    simp only [pr, Option.bind_eq_bind] at h
    split at h
    · next hn =>
      cases ht : pr bare sc t .term <;> cases hb : pr bare (n :: sc) b .term <;> simp [ht, hb] at h
      subst h
      exact wfs_paren _ (wfs_cons trivial (wfs_append (binderToks_wf bi hn (iht sc _ ht))
        (wfs_cons trivial (ihb _ _ hb))))
    · simp at h
  | forallE n t b bi iht ihb =>
    intro sc p ts h
    simp only [pr, Option.bind_eq_bind] at h
    split at h
    · cases ht : pr bare sc t .simple <;> cases hb : pr bare (n :: sc) b .term <;> simp [ht, hb] at h
      subst h
      exact wfs_paren _ (wfs_append (iht sc _ ht) (wfs_cons trivial (ihb _ _ hb)))
    · split at h
      · next hn =>
        cases ht : pr bare sc t .term <;> cases hb : pr bare (n :: sc) b .term <;>
          simp [ht, hb] at h
        subst h
        exact wfs_paren _ (wfs_cons trivial (wfs_append (binderToks_wf bi hn (iht sc _ ht))
          (wfs_cons trivial (ihb _ _ hb))))
      · simp at h
  | letE n t v b nd iht ihv ihb =>
    intro sc p ts h
    simp only [pr, Option.bind_eq_bind] at h
    split at h
    · next hn =>
      cases ht : pr bare sc t .term <;> cases hv : pr bare sc v .term <;>
        cases hb : pr bare (n :: sc) b .term <;> simp [ht, hv, hb] at h
      subst h
      refine wfs_paren _ ?_
      simp only [letToks, List.cons_append, List.append_assoc]
      exact wfs_cons (by cases nd <;> trivial) (wfs_cons (wf_ident_of_atomOk hn)
        (wfs_cons trivial (wfs_append (iht sc _ ht) (wfs_cons trivial
          (wfs_append (ihv sc _ hv) (wfs_cons trivial (ihb _ _ hb)))))))
    · simp at h
  | fvar | mvar | mdata | proj => intro sc p ts h; simp [pr] at h

/-! ## The round trip -/

/-- `parse` reads back from every text `print` writes the very term it printed. -/
theorem parse_print {bare : Name → Bool} {esc : String → Bool} {e : Expr} {s : String}
    (h : print bare esc e = some s) : parse s = some e := by
  simp only [print, Option.map_eq_some_iff] at h
  obtain ⟨ts, hts, rfl⟩ := h
  have hT := (claims bare e []).2.2.2 ts hts [] (fun _ h => by simp at h) (4 * ts.length + 3) (Nat.le_refl _)
  rw [List.append_nil] at hT
  simp [parse, String.toList_ofList, lex_render esc ts (pr_wf bare e [] .term hts), hT]

/-- Two terms that print as the same text are the same term, whatever the choices of either
print. -/
theorem print_injective {bare bare' : Name → Bool} {esc esc' : String → Bool} {e₁ e₂ : Expr}
    {s : String} (h₁ : print bare esc e₁ = some s) (h₂ : print bare' esc' e₂ = some s) :
    e₁ = e₂ := by
  have := (parse_print h₁).symm.trans (parse_print h₂)
  simpa using this

/-- The printer prints exactly the closed terms `Printable` admits. -/
theorem print_isSome_iff (bare : Name → Bool) (esc : String → Bool) (e : Expr) :
    (print bare esc e).isSome ↔ Printable [] e := by
  rw [print, Option.isSome_map]
  exact pr_isSome_iff bare e [] .term

end LeanIntent.Print
