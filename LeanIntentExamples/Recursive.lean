import LeanIntent.Declared

/-!
# Records about recursive, nested and mutual types the project declares

A recursive type gets its code from its declaration, by `deriving LeanIntent.HasCode`, as a
structure does. The code of `Expr`, the arithmetic expressions, holds its constructor whose fields
hold no expression, `num`, as its base, and its other constructors, `add` and `neg`, each with its
recursive fields (`expr_code`); its isomorphism takes each expression to its tree and back,
and Lean's kernel checks that each map undoes the other.

The degenerate subjects follow from the declaration. A recursive type takes constants only at its
base constructors applied to the values their fields' rules admit, here `num 0`, which is also its
empty value (`expr_empty`, `expr_part`), and it has infinitely many values (`expr_infinite`). A
function from expressions to expressions has the constant at `num 0` and the identity
(`simplify_degenerate`): a record that asks a simplifier only to keep each expression's value is met
by the identity, the simplifier that does nothing, and the check reports it
(`keepsValue_verdicts`, `keepsValue_possibilities`).

A type nested through the type formers the class covers gets its code too: `Json`, whose arrays
hold `Json` values and whose objects pair strings with them, takes constants at `null` and `num 0`
(`json_degenerate`). So does a type with a parameter (`Tree`), a type with a function in a field
(`Term`), and one of mutually inductive types that has a constructor holding no value of its group
(`Even`, `even_degenerate`).
-/

namespace LeanIntentExamples.Recursive

open LeanIntent

/-- Arithmetic expressions over natural numbers. -/
inductive Expr where
  | num (n : Nat)
  | add (a b : Expr)
  | neg (a : Expr)
  deriving LeanIntent.HasCode

/-- The value of an expression, in the integers. -/
def Expr.eval : Expr → Int
  | .num n => n
  | .add a b => a.eval + b.eval
  | .neg a => - a.eval

/-! ## A code fixed by the declaration -/

/-- `Expr`'s code: its name, no parameter, its base, the chain of `num`'s field, its group's data and
arguments, one type whose other constructors are `add` and `neg`, each with no other field and with
the unit code for each of its recursive fields, two for `add` and one for `neg`, and the types of the
group those fields hold, each the group's only type. -/
theorem expr_code :
    HasCode.code Expr = .decl ``Expr .unit (.mu (.prod .nat .unit)
      (.prod (.prod (.prod .unit (.prod (.prod .unit (.prod .unit .unit)) .unit))
        (.prod (.prod .unit (.prod (.prod .unit .unit) .unit)) .unit)) .unit)
      (.prod (.prod (.prod (.ref 0) (.prod (.ref 0) .unit)) (.prod (.prod (.ref 0) .unit) .unit))
        .unit) 0) := rfl

/-- `Expr`'s empty value is `num 0`: its first base constructor applied to its field's empty
value. -/
theorem expr_empty : (HasCode.iso (α := Expr)).inv (HasCode.code Expr).empty = .num 0 := rfl

/-- The constants of `Expr`: `num 0` alone, since a number's rule admits only zero. -/
theorem expr_part : (HasCode.code Expr).part.map (HasCode.iso (α := Expr)).inv = [.num 0] := rfl

/-- `Expr` has infinitely many values. -/
theorem expr_infinite : (HasCode.code Expr).finite = false := rfl

/-! ## A simplifier -/

/-- The degenerate subjects of a function from expressions to expressions: the constant at `num 0`
and the identity. -/
theorem simplify_degenerate :
    (degenerate (Expr → Expr)).map Degenerate.reading =
      [.subject fun _ => .num 0, .subject fun e => e] := by
  show [Degenerate.Reading.subject fun _ => Expr.num 0,
    .subject fun e => (HasCode.iso (α := Expr)).inv ((HasCode.iso (α := Expr)).to e)] = _
  simp only [Iso.inv_to]

/-- The simplified expression has the value of the expression. -/
def keepsValue : IntentRecord (Expr → Expr) where
  shape := .function _ _
  dom := []
  props := [⟨"keeps the value", fun f => ∀ e, (f e).eval = e.eval⟩]
  vocab := []

/-- The identity meets `keepsValue`; the constant at `num 0` does not. -/
theorem keepsValue_verdicts : Verdicts keepsValue [false, true] := by
  show ¬ keepsValue.Meets (fun _ => .num 0) ∧
    keepsValue.Meets (fun e => (HasCode.iso (α := Expr)).inv ((HasCode.iso (α := Expr)).to e)) ∧ True
  refine ⟨fun h => ?_, ⟨fun _ h => (nomatch h), fun c hc => ?_⟩, trivial⟩
  · have := h.2 _ (List.mem_singleton.mpr rfl) (.num 1)
    simp [Expr.eval] at this
  · rcases List.mem_singleton.mp hc with rfl
    intro e
    simp only [Iso.inv_to]

/-- The check reports the identity: the record allows the simplifier that does nothing, to be
confirmed or declined. -/
theorem keepsValue_possibilities :
    (possibilities keepsValue_verdicts).map Consequence.holds =
      [fun f => f = fun e => (HasCode.iso (α := Expr)).inv ((HasCode.iso (α := Expr)).to e)] := rfl

/-! ## A nested type -/

/-- JSON values: arrays hold values, and objects pair strings with values. -/
inductive Json where
  | null
  | num (n : Nat)
  | arr (xs : Array Json)
  | obj (kvs : List (String × Json))
  deriving LeanIntent.HasCode

/-- The degenerate subjects of a function from JSON values to JSON values: the constants at its base
constructors, `null` and `num 0`, and the identity. -/
theorem json_degenerate :
    (degenerate (Json → Json)).map Degenerate.reading =
      [.subject fun _ => .null, .subject fun _ => .num 0, .subject fun j => j] := by
  show [Degenerate.Reading.subject fun _ => Json.null, .subject fun _ => Json.num 0,
    .subject fun j => (HasCode.iso (α := Json)).inv ((HasCode.iso (α := Json)).to j)] = _
  simp only [Iso.inv_to]

/-! ## A parameter, a function in a field, and mutual types -/

/-- Binary trees with a value at each node. -/
inductive Tree (α : Type) where
  | leaf
  | node (l : Tree α) (x : α) (r : Tree α)
  deriving LeanIntent.HasCode

/-- A function from trees of numbers to numbers has the constant at zero alone: a recursive type with
several constructors has no projection but the identity. -/
theorem tree_degenerate :
    (degenerate (Tree Nat → Nat)).map Degenerate.reading = [.subject fun _ => 0] := rfl

/-- Terms whose binder is a function to terms. -/
inductive Term where
  | var (n : Nat)
  | app (f : Term) (args : List Term)
  | lam (body : Nat → Term)
  deriving LeanIntent.HasCode

/-- The empty value of `Term` is `var 0`. -/
theorem term_empty : (HasCode.iso (α := Term)).inv (HasCode.code Term).empty = .var 0 := rfl

mutual
/-- The even numbers, in unary. -/
inductive Even where
  | zero
  | succ (o : Odd)
/-- The odd numbers, in unary. -/
inductive Odd where
  | succ (e : Even)
end

deriving instance LeanIntent.HasCode for Even

/-- A function from even numbers to even numbers has the constant at `zero` and the identity. -/
theorem even_degenerate :
    (degenerate (Even → Even)).map Degenerate.reading =
      [.subject fun _ => .zero, .subject fun e => e] := by
  show [Degenerate.Reading.subject fun _ => Even.zero,
    .subject fun e => (HasCode.iso (α := Even)).inv ((HasCode.iso (α := Even)).to e)] = _
  simp only [Iso.inv_to]

end LeanIntentExamples.Recursive
