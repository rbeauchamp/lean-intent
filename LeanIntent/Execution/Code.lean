/-!
# Which compiled declarations are an implementation's code

Lean's compiler makes declarations of its own from a constant's code, which the environment holds
no constant of. `LeanIntent.Execution.Read` counts exactly one kind of them as an implementation's
code: the copy that reduce-arity makes of it. Where a declaration `c` has a parameter its body does
not use, reduce-arity names a copy of `c`'s body over the parameters it uses `c._redArg`, the name
of `c` followed by the one component `_redArg`, and makes `c` a wrapper that calls it and that
every caller inlines (Lean v4.35.0, `Lean/Compiler/LCNF/ReduceArity.lean` 156-205, lines 172 and
197). Calling `c._redArg` runs `c`'s code, so a polymorphic implementation, or one taking a proof,
whose callers call only that copy, is reached through it. No other declaration the compiler makes is
counted. A closed term the compiler extracts from a declaration's code is shared with every later
declaration that holds the same term (`Lean/Compiler/LCNF/ExtractClosed.lean` 216-233), so reaching
it does not run that code. A lambda lifted out of it is reached only where the code was inlined, and
a specialization of it is a copy the compiler made at a caller, whose record of its origin Lean keeps
private to its compiler (`Lean/Compiler/LCNF/Specialize.lean` 30). A reach only through one of these
is refused, and `docs/execution.md` names the remedy for each.

`isCompiledCodeOf isConst c t` holds when `t` is `c`, or `t` is `p` followed by `_redArg`, `isConst`
refuses `t`, and `p` is compiled code of `c`. It is pure, so that the worked examples state it over
literal names, and `isCompiledCodeOf_iff` states it in other terms. The reader gives as `isConst`
whether its environment holds a constant of the name. A constant of the environment other than `c` is
never `c`'s compiled code (`isCompiledCodeOf_const`), so a project cannot make a constant of its
own count as the implementation by naming it like the compiler's copy.
-/

namespace LeanIntent.Execution

/-- `t` is the compiled code of `c`: it is `c`, or it is the name of a declaration that is,
followed by `_redArg`, and `isConst` refuses it. -/
def isCompiledCodeOf (isConst : Lean.Name → Bool) (c : Lean.Name) : Lean.Name → Bool
  | t@(.str p s) => t == c || (s == "_redArg" && !isConst t && isCompiledCodeOf isConst c p)
  | t => t == c

/-- **What counts as `c`'s compiled code**: `c`, and each name `p ++ _redArg` that `isConst`
refuses, where `p` is compiled code of `c`. -/
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

/-- A name that `isConst` accepts is the compiled code of `c` only when it is `c`. -/
theorem isCompiledCodeOf_const {isConst : Lean.Name → Bool} {c t : Lean.Name}
    (ht : isConst t = true) (hne : t ≠ c) : isCompiledCodeOf isConst c t = false := by
  cases h : isCompiledCodeOf isConst c t with
  | false => rfl
  | true =>
    rcases isCompiledCodeOf_iff.mp h with h | ⟨_, _, hc, _⟩
    · exact absurd h hne
    · rw [ht] at hc; cases hc

end LeanIntent.Execution
