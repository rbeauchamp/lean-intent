module

public section

namespace LeanIntent.Required

@[expose] def dotParts : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    if c = '.' then [] :: dotParts cs
    else
      match dotParts cs with
      | [] => [[c]]
      | p :: ps => (c :: p) :: ps

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

@[expose] def isPart : List Char → Bool
  | [] => false
  | c :: cs => c.isAlpha && cs.all fun c => c.isAlphanum || c == '_' || c == '\''

@[expose] def nameOf (ps : List (List Char)) : Lean.Name :=
  ps.foldl (fun n p => .str n (String.ofList p)) .anonymous

@[expose] def partsOf : Lean.Name → List (List Char)
  | .anonymous => []
  | .str n s => partsOf n ++ [s.toList]
  | .num n _ => partsOf n

theorem partsOf_foldl (n : Lean.Name) (ps : List (List Char)) :
    partsOf (ps.foldl (fun n p => .str n (String.ofList p)) n) = partsOf n ++ ps := by
  induction ps generalizing n with
  | nil => simp
  | cons p ps ih => simp [ih, partsOf, String.toList_ofList]

theorem partsOf_nameOf (ps : List (List Char)) : partsOf (nameOf ps) = ps := by
  simp [nameOf, partsOf_foldl, partsOf]

@[expose] def moduleName? (s : String) : Option Lean.Name :=
  if (dotParts s.toList).all isPart then some (nameOf (dotParts s.toList)) else none

section

variable {s t : String} {n : Lean.Name}

theorem moduleName?_parts (h : moduleName? s = some n) : partsOf n = dotParts s.toList := by
  unfold moduleName? at h
  split at h
  · rw [← Option.some.inj h, partsOf_nameOf]
  · exact absurd h (by simp)

theorem moduleName?_isPart (h : moduleName? s = some n) :
    ∀ p ∈ dotParts s.toList, isPart p = true := by
  unfold moduleName? at h
  split at h
  · rename_i hall; exact List.all_eq_true.mp hall
  · exact absurd h (by simp)

theorem moduleName?_inj (hs : moduleName? s = some n) (ht : moduleName? t = some n) : s = t := by
  apply String.toList_injective
  rw [← dotJoin_dotParts s.toList, ← dotJoin_dotParts t.toList, ← moduleName?_parts hs,
    ← moduleName?_parts ht]

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
