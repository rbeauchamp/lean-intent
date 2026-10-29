import LeanIntent

/-!
# Records about types the project declares

A project's own structures and inductive types get their codes from their declarations, by
`deriving LeanIntent.HasCode`. The code of `Point` is its name and its two fields, in order
(`point_code`), and its isomorphism takes a point to the pair of its coordinates (`point_iso`); the
code of `Light` is the sum of its three constructors, in order (`light_code`), and its isomorphism
takes each light to its alternative (`light_iso`). A parameter's code is part of the code
(`pair_code`), and a field of a declared type is coded by that type's code (`labelled_code`).

The degenerate subjects follow from the declarations. A function from points to numbers has the
constant at zero and the projections onto each coordinate (`point_degenerate`); a record that asks
only for a result at least the first coordinate is met by the projection onto it, and the check
reports it (`atLeastX_verdicts`, `atLeastX_possibilities`). A function from lights to lights has the
constant at each light, since `Light` has finitely many values, and the identity
(`light_degenerate`); a record that asks only that red follow green is met by the constant at red,
which the check reports (`afterGreen_verdicts`). The projections of a structure reach into the
fields of its fields (`labelled_degenerate`).
-/

namespace LeanIntentExamples.Declared

open LeanIntent

/-- A point of the plane with natural coordinates. -/
structure Point where
  /-- The first coordinate. -/
  x : Nat
  /-- The second coordinate. -/
  y : Nat
  deriving LeanIntent.HasCode

/-- The lights of a traffic signal. -/
inductive Light where
  | red
  | amber
  | green
  deriving DecidableEq, LeanIntent.HasCode

/-- Two values of one type. -/
structure Pair (α : Type) where
  /-- The first value. -/
  first : α
  /-- The second value. -/
  second : α
  deriving LeanIntent.HasCode

/-- A point with the light shown there. -/
structure Labelled where
  /-- Where. -/
  pos : Point
  /-- The light. -/
  light : Light
  deriving LeanIntent.HasCode

/-! ## Codes fixed by the declarations -/

/-- `Point`'s code: its name, no parameter, and the chain of its two fields of code `nat`. -/
theorem point_code :
    HasCode.code Point = .decl ``Point .unit (.prod .nat (.prod .nat .unit)) := rfl

/-- `Point`'s isomorphism takes a point to its coordinates, in the order of its fields. -/
theorem point_iso (p : Point) : (HasCode.iso (α := Point)).to p = (p.x, p.y, ()) := rfl

/-- `Light`'s code: the sum of its three constructors, in order, each with no field. -/
theorem light_code :
    HasCode.code Light = .decl ``Light .unit (.sum .unit (.sum .unit .unit)) := rfl

/-- `Light`'s isomorphism takes each light to its alternative, in the order of the constructors. -/
theorem light_iso :
    [Light.red, .amber, .green].map (HasCode.iso (α := Light)).to =
      [.inl (), .inr (.inl ()), .inr (.inr ())] := rfl

/-- The code of `Pair Int` holds the code of its parameter. -/
theorem pair_code :
    HasCode.code (Pair Int) = .decl ``Pair (.prod .int .unit) (.prod .int (.prod .int .unit)) :=
  rfl

/-- A field of a declared type is coded by that type's code. -/
theorem labelled_code :
    HasCode.code Labelled =
      .decl ``Labelled .unit (.prod (HasCode.code Point) (.prod (HasCode.code Light) .unit)) :=
  rfl

/-! ## A function of points -/

/-- The degenerate subjects of a function from points to numbers: the constant at zero, then the
projections onto the coordinates, in the order of the fields. -/
theorem point_degenerate :
    (degenerate (Point → Nat)).map Degenerate.subject = [fun _ => 0, fun p => p.x, fun p => p.y] :=
  rfl

/-- The result is at least the first coordinate. -/
def atLeastX : IntentRecord (Point → Nat) where
  shape := .function _ _
  dom := []
  props := [⟨"at least the first coordinate", fun f => ∀ p, p.x ≤ f p⟩]
  vocab := []

/-- The projection onto the first coordinate meets `atLeastX`; the constant at zero and the
projection onto the second do not. -/
theorem atLeastX_verdicts : Verdicts atLeastX [false, true, false] := by
  show ¬ atLeastX.Meets (fun _ => 0) ∧ atLeastX.Meets (fun p => p.x) ∧
    ¬ atLeastX.Meets (fun p => p.y) ∧ True
  refine ⟨fun h => ?_, ⟨fun _ h => (nomatch h), fun c hc => ?_⟩, fun h => ?_, trivial⟩
  · exact absurd (h.2 _ (List.mem_singleton.mpr rfl) ⟨1, 0⟩) (by decide)
  · rcases List.mem_singleton.mp hc with rfl
    exact fun p => Nat.le_refl p.x
  · exact absurd (h.2 _ (List.mem_singleton.mpr rfl) ⟨1, 0⟩) (by decide)

/-- The check reports the projection onto the first coordinate, for the owner to confirm or
decline. -/
theorem atLeastX_possibilities :
    (possibilities atLeastX_verdicts).map Consequence.holds = [fun f => f = fun p => p.x] := rfl

/-! ## A function of lights -/

/-- The degenerate subjects of a function from lights to lights: the constant at each light, in the
order of the constructors, and the identity. -/
theorem light_degenerate :
    (degenerate (Light → Light)).map Degenerate.subject =
      [fun _ => .red, fun _ => .amber, fun _ => .green, fun l => l] := by
  show [fun _ => Light.red, fun _ => Light.amber, fun _ => Light.green,
    fun l => (HasCode.iso (α := Light)).inv ((HasCode.iso (α := Light)).to l)] = _
  simp only [Iso.inv_to]

/-- Red follows green. -/
def afterGreen : IntentRecord (Light → Light) where
  shape := .function _ _
  dom := []
  props := [⟨"red follows green", fun f => f .green = .red⟩]
  vocab := []

/-- The constant at red meets `afterGreen`; the other constants and the identity do not. -/
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

/-! ## A structure with a field of a declared type -/

/-- The degenerate subjects of a function from labelled points to numbers: the constant at zero,
then the projections onto the coordinates of the point, reached through the field `pos`. -/
theorem labelled_degenerate :
    (degenerate (Labelled → Nat)).map Degenerate.subject =
      [fun _ => 0, fun l => l.pos.x, fun l => l.pos.y] :=
  rfl

end LeanIntentExamples.Declared
