/-!
# Which compiled declarations are an implementation's code

Lean's compiler makes declarations of its own from a constant's code, which the environment holds
no constant of, and names each after the declaration it was made from: the copy of `c` that
reduce-arity makes is `c._redArg`, the boxed variant of `c` is `c._boxed`, and a specialization of
`o` made while compiling `caller` is `o._at_.caller.spec_i`. `LeanIntent.Execution.Read` counts a
compiled declaration `t` as the compiled code of an implementation `c` by that naming, through the
two functions here, which are pure, so that the worked examples state them over literal names:

* `nearestConst isConst t`: the nearest proper prefix of `t` that `isConst` accepts;
* `isCompiledCodeOf isConst c t`: `t` is `c`, or `isConst` refuses `t` and the nearest proper prefix
  of `t` it accepts is `c`.

The reader gives as `isConst` whether its environment holds a constant of the name. A constant of
the environment other than `c` is never `c`'s compiled code (`isCompiledCodeOf_const`), so a project
cannot make a constant of its own count as the implementation by naming it after it. Why the naming
identifies what the compiler made, and what it leaves trusted, is set out in
`LeanIntent.Execution.Read`'s module comment and in `docs/execution.md`.
-/

namespace LeanIntent.Execution

/-- The nearest proper prefix of `t` that `isConst` accepts, or `none` when it accepts none. -/
def nearestConst (isConst : Lean.Name → Bool) : Lean.Name → Option Lean.Name
  | .anonymous => none
  | .str p _ | .num p _ => if isConst p then some p else nearestConst isConst p

/-- `t` is the compiled code of `c`: it is `c`, or `isConst` refuses it and the nearest proper
prefix of it that `isConst` accepts is `c`. -/
def isCompiledCodeOf (isConst : Lean.Name → Bool) (c t : Lean.Name) : Bool :=
  t == c || (!isConst t && nearestConst isConst t == some c)

/-- A name that `isConst` accepts is the compiled code of `c` only when it is `c`. -/
theorem isCompiledCodeOf_const {isConst : Lean.Name → Bool} {c t : Lean.Name}
    (ht : isConst t = true) (hne : t ≠ c) : isCompiledCodeOf isConst c t = false := by
  simp [isCompiledCodeOf, ht, hne]

end LeanIntent.Execution
