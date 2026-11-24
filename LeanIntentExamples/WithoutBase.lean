module

public import LeanIntent.Declared
public import LeanIntentExamples.Recursive
import all Init.Prelude

public section

namespace LeanIntentExamples.WithoutBase

open LeanIntent

inductive Rose where
  | node (label : Nat) (kids : List Rose)
  deriving LeanIntent.HasCode

theorem rose_root : ∃ b g r, HasCode.code Rose = .decl ``Rose .unit (.muAt b g r 1 0) :=
  ⟨_, _, _, rfl⟩

theorem rose_empty : (HasCode.iso (α := Rose)).inv (HasCode.code Rose).empty = .node 0 [] := rfl

theorem rose_part : (HasCode.code Rose).part.map (HasCode.iso (α := Rose)).inv = [.node 0 []] :=
  rfl

theorem rose_infinite : (HasCode.code Rose).finite = false := rfl

inductive Dir where
  | mk (entries : Array (String × Dir))
  deriving LeanIntent.HasCode

theorem dir_empty : (HasCode.iso (α := Dir)).inv (HasCode.code Dir).empty = .mk #[] := rfl

deriving instance LeanIntent.HasCode for LeanIntentExamples.Recursive.Odd

theorem odd_empty :
    (HasCode.iso (α := Recursive.Odd)).inv (HasCode.code Recursive.Odd).empty = .succ .zero := rfl

structure Link where
  next : Option Link
  deriving LeanIntent.HasCode

theorem link_empty : (HasCode.iso (α := Link)).inv (HasCode.code Link).empty = ⟨none⟩ := rfl

mutual
inductive Expr where
  | lit (n : Nat)
  | add (a b : Expr)
  | block (s : Stmt)
inductive Stmt where
  | seq (a b : Stmt)
  | expr (e : Expr)
end

deriving instance LeanIntent.HasCode for Stmt

mutual
@[expose] def Expr.eval : Expr → Nat
  | .lit n => n
  | .add a b => a.eval + b.eval
  | .block s => s.eval
@[expose] def Stmt.eval : Stmt → Nat
  | .seq _ b => b.eval
  | .expr e => e.eval
end

theorem stmt_empty : (HasCode.iso (α := Stmt)).inv (HasCode.code Stmt).empty = .expr (.lit 0) :=
  rfl

theorem optimize_degenerate :
    (degenerate (Stmt → Stmt)).map Degenerate.reading =
      [.subject fun _ => .expr (.lit 0), .subject fun s => s] := by
  show [Degenerate.Reading.subject fun _ => Stmt.expr (.lit 0),
    .subject fun s => (HasCode.iso (α := Stmt)).inv ((HasCode.iso (α := Stmt)).to s)] = _
  simp only [Iso.inv_to]

@[expose] def keepsValue : IntentRecord (Stmt → Stmt) where
  shape := .function _ _
  dom := []
  props := [⟨"keeps the value", fun f => ∀ s, (f s).eval = s.eval⟩]
  vocab := []

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

theorem keepsValue_possibilities :
    (possibilities keepsValue_verdicts).map Consequence.holds =
      [fun f => f = fun s => (HasCode.iso (α := Stmt)).inv ((HasCode.iso (α := Stmt)).to s)] := by rfl

end LeanIntentExamples.WithoutBase
