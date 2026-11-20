module

public section

namespace LeanIntent.Execution

@[expose] def isCompiledCodeOf (isConst : Lean.Name → Bool) (c : Lean.Name) : Lean.Name → Bool
  | t@(.str p s) => t == c || (s == "_redArg" && !isConst t && isCompiledCodeOf isConst c p)
  | t => t == c

theorem isCompiledCodeOf_iff {isConst : Lean.Name → Bool} {c t : Lean.Name} :
    isCompiledCodeOf isConst c t = true ↔
      t = c ∨ ∃ p, t = .str p "_redArg" ∧ isConst t = false ∧ isCompiledCodeOf isConst c p = true := by
  cases t with
  | str p s =>
    simp only [isCompiledCodeOf, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, Bool.not_eq_true']
    constructor
    · rintro (h | ⟨⟨hs, hc⟩, hp⟩)
      · exact .inl h
      · exact .inr ⟨p, by rw [hs], hc, hp⟩
    · rintro (h | ⟨q, hq, hc, hp⟩)
      · exact .inl h
      · cases hq
        exact .inr ⟨⟨rfl, hc⟩, hp⟩
  | anonymous => simp [isCompiledCodeOf]
  | num p n => simp [isCompiledCodeOf]

theorem isCompiledCodeOf_const {isConst : Lean.Name → Bool} {c t : Lean.Name}
    (ht : isConst t = true) (hne : t ≠ c) : isCompiledCodeOf isConst c t = false := by
  cases h : isCompiledCodeOf isConst c t with
  | false => rfl
  | true =>
    rcases isCompiledCodeOf_iff.mp h with h | ⟨_, _, hc, _⟩
    · exact absurd h hne
    · rw [ht] at hc; cases hc

end LeanIntent.Execution
