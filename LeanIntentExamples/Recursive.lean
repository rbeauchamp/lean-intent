module

public import LeanIntent.Declared
import all Init.Prelude

public section

namespace LeanIntentExamples.Recursive

open LeanIntent

inductive Expr where
  | num (n : Nat)
  | add (a b : Expr)
  | neg (a : Expr)
  deriving LeanIntent.HasCode

@[expose] def Expr.eval : Expr → Int
  | .num n => n
  | .add a b => a.eval + b.eval
  | .neg a => - a.eval

theorem expr_code :
    HasCode.code Expr = .decl ``Expr .unit (.mu (.prod .nat .unit)
      (.prod (.prod (.prod .unit (.prod (.prod .unit (.prod .unit .unit)) .unit))
        (.prod (.prod .unit (.prod (.prod .unit .unit) .unit)) .unit)) .unit)
      (.prod (.prod (.prod (.ref 0) (.prod (.ref 0) .unit)) (.prod (.prod (.ref 0) .unit) .unit))
        .unit) 0) := rfl

theorem expr_empty : (HasCode.iso (α := Expr)).inv (HasCode.code Expr).empty = .num 0 := rfl

theorem expr_part : (HasCode.code Expr).part.map (HasCode.iso (α := Expr)).inv = [.num 0] := rfl

theorem expr_infinite : (HasCode.code Expr).finite = false := rfl

theorem simplify_degenerate :
    (degenerate (Expr → Expr)).map Degenerate.reading =
      [.subject fun _ => .num 0, .subject fun e => e] := by
  show [Degenerate.Reading.subject fun _ => Expr.num 0,
    .subject fun e => (HasCode.iso (α := Expr)).inv ((HasCode.iso (α := Expr)).to e)] = _
  simp only [Iso.inv_to]

@[expose] def keepsValue : IntentRecord (Expr → Expr) where
  shape := .function _ _
  dom := []
  props := [⟨"keeps the value", fun f => ∀ e, (f e).eval = e.eval⟩]
  vocab := []

theorem keepsValue_verdicts : Verdicts keepsValue [false, true] := by
  show ¬ keepsValue.Meets (fun _ => .num 0) ∧
    keepsValue.Meets (fun e => (HasCode.iso (α := Expr)).inv ((HasCode.iso (α := Expr)).to e)) ∧ True
  refine ⟨fun h => ?_, ⟨fun _ h => (nomatch h), fun c hc => ?_⟩, trivial⟩
  · have := h.2 _ (List.mem_singleton.mpr rfl) (.num 1)
    simp [Expr.eval] at this
  · rcases List.mem_singleton.mp hc with rfl
    intro e
    simp only [Iso.inv_to]

theorem keepsValue_possibilities :
    (possibilities keepsValue_verdicts).map Consequence.holds =
      [fun f => f = fun e => (HasCode.iso (α := Expr)).inv ((HasCode.iso (α := Expr)).to e)] := by rfl

inductive Json where
  | null
  | num (n : Nat)
  | arr (xs : Array Json)
  | obj (kvs : List (String × Json))
  deriving LeanIntent.HasCode

theorem json_degenerate :
    (degenerate (Json → Json)).map Degenerate.reading =
      [.subject fun _ => .null, .subject fun _ => .num 0, .subject fun j => j] := by
  show [Degenerate.Reading.subject fun _ => Json.null, .subject fun _ => Json.num 0,
    .subject fun j => (HasCode.iso (α := Json)).inv ((HasCode.iso (α := Json)).to j)] = _
  simp only [Iso.inv_to]

inductive Tree (α : Type) where
  | leaf
  | node (l : Tree α) (x : α) (r : Tree α)
  deriving LeanIntent.HasCode

theorem tree_degenerate :
    (degenerate (Tree Nat → Nat)).map Degenerate.reading = [.subject fun _ => 0] := rfl

inductive Term where
  | var (n : Nat)
  | app (f : Term) (args : List Term)
  | lam (body : Nat → Term)
  deriving LeanIntent.HasCode

theorem term_empty : (HasCode.iso (α := Term)).inv (HasCode.code Term).empty = .var 0 := rfl

mutual
inductive Even where
  | zero
  | succ (o : Odd)
inductive Odd where
  | succ (e : Even)
end

deriving instance LeanIntent.HasCode for Even

theorem even_degenerate :
    (degenerate (Even → Even)).map Degenerate.reading =
      [.subject fun _ => .zero, .subject fun e => e] := by
  show [Degenerate.Reading.subject fun _ => Even.zero,
    .subject fun e => (HasCode.iso (α := Even)).inv ((HasCode.iso (α := Even)).to e)] = _
  simp only [Iso.inv_to]

end LeanIntentExamples.Recursive
