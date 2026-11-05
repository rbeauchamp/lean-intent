import LeanIntent.Declared
import LeanIntentExamples.Recursive

/-!
# Records about recursive types without a base constructor

A recursive type each of whose constructors holds a value of a type of its group has no constructor
of its own whose fields hold none, so its empty value is built from those of the types its
constructors hold. The types of its group get their empty values in rounds: in the first, each type
with a constructor whose fields hold no value of the group, and in each later round each type with
a constructor whose recursive fields all hold types that got theirs in an earlier round. A type's
empty value is the first such constructor of its round, in declaration order, applied to its other
fields' empty values and to the empty values of the types its recursive fields hold
(`LeanIntent.Ty.IsMuEmpty`). Its code is `Ty.muAt`, whose trees take their base values from its
*root*, the first type of its group, in the order of Lean's recursor, that it reaches and that has
such a constructor (`rose_root`). The class takes its empty value as its only constant, and it has
no projection but the identity.

A rose tree, whose only constructor holds a list of trees, has the empty value `node 0 []`
(`rose_empty`, `rose_part`) and infinitely many values (`rose_infinite`); a directory, whose only
constructor holds an array of named directories, has `mk #[]` (`dir_empty`). The odd half of the
mutual even and odd pair of `LeanIntentExamples.Recursive` has `succ zero` (`odd_empty`), and a
structure whose only field is an option of itself has `⟨none⟩` (`link_empty`). The statements of a
small language, each of which holds an expression or statements, where an expression can hold a
block of statements, have `expr (lit 0)` (`stmt_empty`). A function from statements to statements
has the constant at `expr (lit 0)` and the identity (`optimize_degenerate`): a record that asks an
optimizer only to keep each statement's value is met by the identity, the optimizer that does
nothing, and the check reports it (`keepsValue_verdicts`, `keepsValue_possibilities`).

A type with no value has no code: the handler refuses `inductive Never | mk (n : Never)`, saying
that it has no value, since every code denotes a type with a value and Lean's kernel checks the
isomorphism between the code and the type.
-/

namespace LeanIntentExamples.WithoutBase

open LeanIntent

/-! ## A type nested through a list -/

/-- Rose trees: a label and a list of children. -/
inductive Rose where
  | node (label : Nat) (kids : List Rose)
  deriving LeanIntent.HasCode

/-- `Rose`'s group is `Rose` and `List Rose`, as Lean's recursor lists them, and its root is the
group's second type, `List Rose`, whose constructor `nil` holds no value of the group. -/
theorem rose_root : ∃ b g r, HasCode.code Rose = .decl ``Rose .unit (.muAt b g r 1 0) :=
  ⟨_, _, _, rfl⟩

/-- `Rose`'s empty value is `node 0 []`: its only constructor applied to the empty value of its
label and to that of its list of children, `[]`, which gets its own in the first round. -/
theorem rose_empty : (HasCode.iso (α := Rose)).inv (HasCode.code Rose).empty = .node 0 [] := rfl

/-- The constants of `Rose`: its empty value alone. -/
theorem rose_part : (HasCode.code Rose).part.map (HasCode.iso (α := Rose)).inv = [.node 0 []] :=
  rfl

/-- `Rose` has infinitely many values. -/
theorem rose_infinite : (HasCode.code Rose).finite = false := rfl

/-- Directories: an array of named directories. -/
inductive Dir where
  | mk (entries : Array (String × Dir))
  deriving LeanIntent.HasCode

/-- `Dir`'s empty value is `mk #[]`, its array of entries getting its own, `#[]`, from the empty
list. -/
theorem dir_empty : (HasCode.iso (α := Dir)).inv (HasCode.code Dir).empty = .mk #[] := rfl

/-! ## The odd half of a mutual pair, and a structure that holds an option of itself -/

deriving instance LeanIntent.HasCode for LeanIntentExamples.Recursive.Odd

/-- `Odd`'s empty value is `succ zero`: its root is `Even`, whose first constructor `zero` holds no
value of the group. -/
theorem odd_empty :
    (HasCode.iso (α := Recursive.Odd)).inv (HasCode.code Recursive.Odd).empty = .succ .zero := rfl

/-- A link to the next link, or to none. -/
structure Link where
  next : Option Link
  deriving LeanIntent.HasCode

/-- `Link`'s empty value is `⟨none⟩`. -/
theorem link_empty : (HasCode.iso (α := Link)).inv (HasCode.code Link).empty = ⟨none⟩ := rfl

/-! ## The statements of a small language -/

mutual
/-- Expressions: numbers, sums and blocks of statements. -/
inductive Expr where
  | lit (n : Nat)
  | add (a b : Expr)
  | block (s : Stmt)
/-- Statements: an expression, or one statement after another. -/
inductive Stmt where
  | seq (a b : Stmt)
  | expr (e : Expr)
end

deriving instance LeanIntent.HasCode for Stmt

mutual
/-- The value of an expression: a block's is that of its statements. -/
def Expr.eval : Expr → Nat
  | .lit n => n
  | .add a b => a.eval + b.eval
  | .block s => s.eval
/-- The value of a statement: that of its expression, or of the last of two statements. -/
def Stmt.eval : Stmt → Nat
  | .seq _ b => b.eval
  | .expr e => e.eval
end

/-- `Stmt`'s empty value is `expr (lit 0)`: `seq`, its first constructor, holds statements, which
get no empty value before `Stmt` does, and `expr` holds an expression, which gets `lit 0` in the
first round. -/
theorem stmt_empty : (HasCode.iso (α := Stmt)).inv (HasCode.code Stmt).empty = .expr (.lit 0) :=
  rfl

/-- The degenerate subjects of a function from statements to statements: the constant at
`expr (lit 0)` and the identity. -/
theorem optimize_degenerate :
    (degenerate (Stmt → Stmt)).map Degenerate.reading =
      [.subject fun _ => .expr (.lit 0), .subject fun s => s] := by
  show [Degenerate.Reading.subject fun _ => Stmt.expr (.lit 0),
    .subject fun s => (HasCode.iso (α := Stmt)).inv ((HasCode.iso (α := Stmt)).to s)] = _
  simp only [Iso.inv_to]

/-- The optimized statement has the value of the statement. -/
def keepsValue : IntentRecord (Stmt → Stmt) where
  shape := .function _ _
  dom := []
  props := [⟨"keeps the value", fun f => ∀ s, (f s).eval = s.eval⟩]
  vocab := []

/-- The identity meets `keepsValue`; the constant at `expr (lit 0)` does not. -/
theorem keepsValue_verdicts : Verdicts keepsValue [false, true] := by
  show ¬ keepsValue.Meets (fun _ => .expr (.lit 0)) ∧
    keepsValue.Meets (fun s => (HasCode.iso (α := Stmt)).inv ((HasCode.iso (α := Stmt)).to s)) ∧
      True
  refine ⟨fun h => ?_, ⟨fun _ h => (nomatch h), fun c hc => ?_⟩, trivial⟩
  · have := h.2 _ (List.mem_singleton.mpr rfl) (.expr (.lit 1))
    simp [Stmt.eval, Expr.eval] at this
  · rcases List.mem_singleton.mp hc with rfl
    intro s
    simp only [Iso.inv_to]

/-- The check reports the identity: the record allows the optimizer that does nothing, to be
confirmed or declined. -/
theorem keepsValue_possibilities :
    (possibilities keepsValue_verdicts).map Consequence.holds =
      [fun f => f = fun s => (HasCode.iso (α := Stmt)).inv ((HasCode.iso (α := Stmt)).to s)] := rfl

end LeanIntentExamples.WithoutBase
