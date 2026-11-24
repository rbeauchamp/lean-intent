module

public import LeanIntent.Declared
import all Init.Prelude

public section

namespace LeanIntentExamples.Declared

open LeanIntent

structure Point where
  x : Nat
  y : Nat
  deriving LeanIntent.HasCode

inductive Light where
  | red
  | amber
  | green
  deriving @[expose] DecidableEq, LeanIntent.HasCode

structure Pair (α : Type) where
  first : α
  second : α
  deriving LeanIntent.HasCode

structure Labelled where
  pos : Point
  light : Light
  deriving LeanIntent.HasCode

theorem point_code :
    HasCode.code Point = .decl ``Point .unit (.prod .nat (.prod .nat .unit)) := rfl

theorem point_iso (p : Point) : (HasCode.iso (α := Point)).to p = (p.x, p.y, ()) := rfl

theorem light_code :
    HasCode.code Light = .decl ``Light .unit (.sum .unit (.sum .unit .unit)) := rfl

theorem light_iso :
    [Light.red, .amber, .green].map (HasCode.iso (α := Light)).to =
      [.inl (), .inr (.inl ()), .inr (.inr ())] := rfl

theorem pair_code :
    HasCode.code (Pair Int) = .decl ``Pair (.prod .int .unit) (.prod .int (.prod .int .unit)) :=
  rfl

theorem labelled_code :
    HasCode.code Labelled =
      .decl ``Labelled .unit (.prod (HasCode.code Point) (.prod (HasCode.code Light) .unit)) :=
  rfl

theorem point_degenerate :
    (degenerate (Point → Nat)).map Degenerate.reading =
      [.subject fun _ => 0, .subject fun p => p.x, .subject fun p => p.y] :=
  rfl

@[expose] def atLeastX : IntentRecord (Point → Nat) where
  shape := .function _ _
  dom := []
  props := [⟨"at least the first coordinate", fun f => ∀ p, p.x ≤ f p⟩]
  vocab := []

theorem atLeastX_verdicts : Verdicts atLeastX [false, true, false] := by
  show ¬ atLeastX.Meets (fun _ => 0) ∧ atLeastX.Meets (fun p => p.x) ∧
    ¬ atLeastX.Meets (fun p => p.y) ∧ True
  refine ⟨fun h => ?_, ⟨fun _ h => (nomatch h), fun c hc => ?_⟩, fun h => ?_, trivial⟩
  · exact absurd (h.2 _ (List.mem_singleton.mpr rfl) ⟨1, 0⟩) (by decide)
  · rcases List.mem_singleton.mp hc with rfl
    exact fun p => Nat.le_refl p.x
  · exact absurd (h.2 _ (List.mem_singleton.mpr rfl) ⟨1, 0⟩) (by decide)

theorem atLeastX_possibilities :
    (possibilities atLeastX_verdicts).map Consequence.holds = [fun f => f = fun p => p.x] := rfl

theorem light_degenerate :
    (degenerate (Light → Light)).map Degenerate.reading =
      [.subject fun _ => .red, .subject fun _ => .amber, .subject fun _ => .green,
        .subject fun l => l] := by
  show [Degenerate.Reading.subject fun _ => Light.red, .subject fun _ => Light.amber,
    .subject fun _ => Light.green,
    .subject fun l => (HasCode.iso (α := Light)).inv ((HasCode.iso (α := Light)).to l)] = _
  simp only [Iso.inv_to]

@[expose] def afterGreen : IntentRecord (Light → Light) where
  shape := .function _ _
  dom := []
  props := [⟨"red follows green", fun f => f .green = .red⟩]
  vocab := []

theorem afterGreen_verdicts : Verdicts afterGreen [true, false, false, false] := by
  show afterGreen.Meets (fun _ => .red) ∧ ¬ afterGreen.Meets (fun _ => .amber) ∧
    ¬ afterGreen.Meets (fun _ => .green) ∧
    ¬ afterGreen.Meets (fun l => (HasCode.iso (α := Light)).inv ((HasCode.iso (α := Light)).to l)) ∧
    True
  refine ⟨⟨fun _ h => (nomatch h), fun c hc => ?_⟩, fun h => ?_, fun h => ?_, fun h => ?_, trivial⟩
  · rcases List.mem_singleton.mp hc with rfl
    rfl
  · exact absurd (h.2 _ (List.mem_singleton.mpr rfl)) (by decide)
  · exact absurd (h.2 _ (List.mem_singleton.mpr rfl)) (by decide)
  · exact absurd (h.2 _ (List.mem_singleton.mpr rfl)) (by decide)

theorem labelled_degenerate :
    (degenerate (Labelled → Nat)).map Degenerate.reading =
      [.subject fun _ => 0, .subject fun l => l.pos.x, .subject fun l => l.pos.y] :=
  rfl

private structure Reading where
  pos : Point
  value : Nat
  deriving LeanIntent.HasCode

private inductive Trail where
  | start
  | step (r : Reading) (rest : Trail)
  deriving LeanIntent.HasCode

private theorem reading_code :
    HasCode.code Reading = .decl ``Reading .unit (.prod (HasCode.code Point) (.prod .nat .unit)) :=
  rfl

private theorem trail_empty :
    (HasCode.iso (α := Trail)).inv (HasCode.code Trail).empty = .start := rfl

private theorem reading_degenerate :
    (degenerate (Reading → Nat)).map Degenerate.reading =
      [.subject fun _ => 0, .subject fun r => r.pos.x, .subject fun r => r.pos.y,
        .subject fun r => r.value] :=
  rfl

end LeanIntentExamples.Declared
