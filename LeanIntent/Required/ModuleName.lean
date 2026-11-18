module

/-!
# The module a string names, read from a closed form of names

`LeanIntent.Required.Read.queryModules` reads the module names a project's build lists from what
Lake prints, each as a string Lean wrote for a name (`Lean.Name.toString`). That printing is not
one-to-one over all names: Lean writes a component that holds a dot between `«` and `»`, but writes
one that already holds `»` as it stands, so the name whose one component is the five characters
`«a.b»` and the name whose one component is `a.b` are both written `«a.b»`. A decoding that gave
either back for that string would count a module the build does not list as built, and the check
would pass under a success code. So this module decodes only a closed form of strings, and gives no
name for any other:

* **The closed form** (`isPart`): the string's stretches between its dots (`dotParts`) are each an
  ASCII letter followed by ASCII letters, digits, `_` or `'`.
* **The name** (`nameOf`): the one whose components are those stretches, in order, each a string
  component.
* **Distinct accepted strings give distinct names** (`moduleName?_inj`), and the name an accepted
  string gives has exactly the string's stretches as its components (`moduleName?_parts`).
* **Every other string is given no name**: an accepted string holds only dots, ASCII letters and
  digits, `_` and `'` (`moduleName?_chars`), so one that holds `«`, `»` or any other character is
  refused, and so is one with an empty stretch or a stretch that starts with a digit, `_` or `'`
  (`moduleName?_isPart`).

That the name given is the name Lean printed is argued from Lean's source at v4.35.0, not proved
here: `LeanIntent.Required.Read`'s module comment sets the argument out with the lines it reads.
-/

public section

namespace LeanIntent.Required

/-- The stretches of `cs` between its dots, in order: at least one, and an empty one wherever a dot
starts or ends `cs` or follows another. -/
@[expose] def dotParts : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    if c = '.' then [] :: dotParts cs
    else
      match dotParts cs with
      | [] => [[c]]
      | p :: ps => (c :: p) :: ps

/-- The lists `ps` with a dot between each two. -/
@[expose] def dotJoin : List (List Char) → List Char
  | [] => []
  | [p] => p
  | p :: q :: ps => p ++ '.' :: dotJoin (q :: ps)

theorem dotParts_ne_nil (cs : List Char) : dotParts cs ≠ [] := by
  cases cs with
  | nil => simp [dotParts]
  | cons c cs =>
    unfold dotParts
    split
    · simp
    · split <;> simp

/-- Joining a string's stretches with dots gives the string back, so the stretches determine it. -/
theorem dotJoin_dotParts (cs : List Char) : dotJoin (dotParts cs) = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    unfold dotParts
    split
    · rename_i hc
      match h : dotParts cs with
      | [] => exact absurd h (dotParts_ne_nil cs)
      | q :: ps => rw [h] at ih; simp [dotJoin, ih, hc]
    · match h : dotParts cs with
      | [] => exact absurd h (dotParts_ne_nil cs)
      | [p] => rw [h] at ih; simp_all [dotJoin]
      | p :: q :: ps => rw [h] at ih; simp only [dotJoin] at ih ⊢; simp [ih]

/-- Every character of `cs` is a dot or lies in one of its stretches. -/
theorem mem_dotParts {c : Char} {cs : List Char} (h : c ∈ cs) :
    c = '.' ∨ ∃ p ∈ dotParts cs, c ∈ p := by
  induction cs with
  | nil => simp at h
  | cons d cs ih =>
    unfold dotParts
    rcases List.mem_cons.mp h with rfl | h
    · split
      · rename_i hc; exact .inl hc
      · split <;> exact .inr ⟨_, List.mem_cons_self, List.mem_cons_self⟩
    · rcases ih h with hc | ⟨p, hp, hcp⟩
      · exact .inl hc
      · refine .inr ?_
        split
        · exact ⟨p, List.mem_cons_of_mem _ hp, hcp⟩
        · split
          · rename_i hnil; rw [hnil] at hp; simp at hp
          · rename_i q ps hq
            rw [hq] at hp
            rcases List.mem_cons.mp hp with rfl | hp
            · exact ⟨_, List.mem_cons_self, List.mem_cons_of_mem _ hcp⟩
            · exact ⟨p, List.mem_cons_of_mem _ hp, hcp⟩

/-- **A stretch of the closed form**: an ASCII letter, then ASCII letters, digits, `_` or `'`. -/
@[expose] def isPart : List Char → Bool
  | [] => false
  | c :: cs => c.isAlpha && cs.all fun c => c.isAlphanum || c == '_' || c == '\''

/-- The name whose components are the strings of `ps`, in order, each a string component. -/
@[expose] def nameOf (ps : List (List Char)) : Lean.Name :=
  ps.foldl (fun n p => .str n (String.ofList p)) .anonymous

/-- The string components of a name, in order, each as its characters; a numeric component gives
none. -/
@[expose] def partsOf : Lean.Name → List (List Char)
  | .anonymous => []
  | .str n s => partsOf n ++ [s.toList]
  | .num n _ => partsOf n

theorem partsOf_foldl (n : Lean.Name) (ps : List (List Char)) :
    partsOf (ps.foldl (fun n p => .str n (String.ofList p)) n) = partsOf n ++ ps := by
  induction ps generalizing n with
  | nil => simp
  | cons p ps ih => simp [ih, partsOf, String.toList_ofList]

/-- The name of `ps` has exactly `ps` as its components, so `ps` determines it and it `ps`. -/
theorem partsOf_nameOf (ps : List (List Char)) : partsOf (nameOf ps) = ps := by
  simp [nameOf, partsOf_foldl, partsOf]

/-- **The module a string names**, where the string is of the closed form: each stretch between
its dots is an ASCII letter followed by ASCII letters, digits, `_` or `'` (`isPart`), and the name
is the one whose components are those stretches (`nameOf`). Every other string names none. -/
@[expose] def moduleName? (s : String) : Option Lean.Name :=
  if (dotParts s.toList).all isPart then some (nameOf (dotParts s.toList)) else none

section

variable {s t : String} {n : Lean.Name}

/-- The name an accepted string gives has exactly the string's stretches as its components. -/
theorem moduleName?_parts (h : moduleName? s = some n) : partsOf n = dotParts s.toList := by
  unfold moduleName? at h
  split at h
  · rw [← Option.some.inj h, partsOf_nameOf]
  · exact absurd h (by simp)

/-- Each stretch of an accepted string is of the closed form. -/
theorem moduleName?_isPart (h : moduleName? s = some n) :
    ∀ p ∈ dotParts s.toList, isPart p = true := by
  unfold moduleName? at h
  split at h
  · rename_i hall; exact List.all_eq_true.mp hall
  · exact absurd h (by simp)

/-- **Distinct accepted strings give distinct names**: two strings the decoding gives one name for
are the same string, for every pair of strings. -/
theorem moduleName?_inj (hs : moduleName? s = some n) (ht : moduleName? t = some n) : s = t := by
  apply String.toList_injective
  rw [← dotJoin_dotParts s.toList, ← dotJoin_dotParts t.toList, ← moduleName?_parts hs,
    ← moduleName?_parts ht]

/-- **An accepted string holds only dots, ASCII letters and digits, `_` and `'`**, so a string
holding any other character, `«` and `»` among them, is given no name. -/
theorem moduleName?_chars (h : moduleName? s = some n) {c : Char} (hc : c ∈ s.toList) :
    c = '.' ∨ c.isAlphanum = true ∨ c = '_' ∨ c = '\'' := by
  rcases mem_dotParts hc with hd | ⟨p, hp, hcp⟩
  · exact .inl hd
  · have hpart := moduleName?_isPart h p hp
    match p, hpart, hcp with
    | d :: ds, hpart, hcp =>
      simp only [isPart, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at hpart
      rcases List.mem_cons.mp hcp with rfl | hcd
      · exact .inr (.inl (by simp [Char.isAlphanum, hpart.1]))
      · rcases hpart.2 c hcd with (ha | hu) | hq
        · exact .inr (.inl ha)
        · exact .inr (.inr (.inl hu))
        · exact .inr (.inr (.inr hq))

end

end LeanIntent.Required
