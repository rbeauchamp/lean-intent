import LeanIntent.Codec

/-!
# The codecs of numbers, names and text

The leaves of a statement's grammar, each a `Codec` whose round trip and plain text are proved here
once:

* `Codec.nat`: a natural number in decimal, padded with zeros to a width, then a fixed character;
* `Codec.token`: a run of characters from a closed set, then a character outside it;
* `Codec.line`: any string on one line, with `\` written `\\` and each concealing character (and
  so every line break the string holds) written `\u` and four lowercase hexadecimal digits;
* `Codec.list`: a count, then that many values;
* `Codec.text`: any string, as its lines, each printed as `| ` and the line.
-/

namespace LeanIntent.Codec

variable {α : Type}

/-! ## Numbers -/

/-- The decimal digit of `k`, for `k < 10`. -/
def digitChar (k : Nat) : Char := Char.ofNat (48 + k)

/-- The value of a decimal digit. -/
def digitValue (c : Char) : Nat := c.toNat - 48

theorem digitChar_spec : ∀ k, k < 10 →
    (digitChar k).isDigit = true ∧ digitValue (digitChar k) = k ∧
      concealing (digitChar k) = false := by
  decide

/-- The decimal digits of `n`, least significant first, given at most `k` steps after the first;
`k ≥ n` steps always suffice. The recursion is on `k`, so Lean's kernel evaluates it. -/
def digitsRevUpTo : Nat → Nat → List Char
  | 0, n => [digitChar n]
  | k + 1, n => if n < 10 then [digitChar n] else digitChar (n % 10) :: digitsRevUpTo k (n / 10)

/-- The decimal digits of `n`, least significant first. -/
def digitsRev (n : Nat) : List Char := digitsRevUpTo n n

/-- The value of decimal digits listed least significant first. -/
def valueRev : List Char → Nat
  | [] => 0
  | d :: ds => valueRev ds * 10 + digitValue d

theorem digitsRevUpTo_spec : ∀ k n, n ≤ k →
    valueRev (digitsRevUpTo k n) = n ∧
      ∀ c ∈ digitsRevUpTo k n, c.isDigit = true ∧ concealing c = false
  | 0, n, _h => by
    obtain rfl : n = 0 := by omega
    have := digitChar_spec 0 (by decide)
    simp [digitsRevUpTo, valueRev, this]
  | k + 1, n, _h => by
    unfold digitsRevUpTo
    split
    · have := digitChar_spec n ‹_›
      simp [valueRev, this]
    · have hd := digitChar_spec (n % 10) (Nat.mod_lt _ (by decide))
      have ih := digitsRevUpTo_spec k (n / 10) (by omega)
      refine ⟨?_, ?_⟩
      · simp only [valueRev, ih.1, hd.2.1]; omega
      · intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact ⟨hd.1, hd.2.2⟩
        · exact ih.2 c hc

theorem digitsRev_spec (n : Nat) :
    valueRev (digitsRev n) = n ∧ ∀ c ∈ digitsRev n, c.isDigit = true ∧ concealing c = false :=
  digitsRevUpTo_spec n n (Nat.le_refl n)

/-- The decimal digits of `n`, most significant first, after enough zeros to make at least `w`. -/
def decimal (w n : Nat) : List Char :=
  List.replicate (w - (digitsRev n).length) '0' ++ (digitsRev n).reverse

theorem valueRev_append_zeros (l : List Char) (k : Nat) :
    valueRev (l ++ List.replicate k '0') = valueRev l := by
  induction l with
  | nil =>
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [List.nil_append, List.replicate_succ, valueRev] at ih ⊢
      rw [ih]; decide
  | cons d l ih => simp [valueRev, ih]

theorem decimal_spec (w n : Nat) :
    valueRev (decimal w n).reverse = n ∧
      ∀ c ∈ decimal w n, c.isDigit = true ∧ concealing c = false := by
  refine ⟨?_, ?_⟩
  · simp [decimal, valueRev_append_zeros, (digitsRev_spec n).1]
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · rw [List.eq_of_mem_replicate hc]; decide
    · exact (digitsRev_spec n).2 c (List.mem_reverse.mp hc)

/-- The longest prefix of the input whose characters `p` admits, and the rest. -/
def span (p : Char → Bool) : List Char → List Char × List Char
  | [] => ([], [])
  | c :: s => if p c then ((c :: (span p s).1), (span p s).2) else ([], c :: s)

theorem span_append (p : Char → Bool) {l : List Char} (hl : ∀ c ∈ l, p c = true) {t : Char}
    (ht : p t = false) (s : List Char) : span p (l ++ t :: s) = (l, t :: s) := by
  induction l with
  | nil => simp [span, ht]
  | cons c l ih =>
    simp [span, hl c List.mem_cons_self, ih fun d hd => hl d (List.mem_cons_of_mem _ hd)]

/-- A natural number in decimal, with zeros before it to make at least `w` digits, then `term`. -/
def nat (w : Nat) (term : Char) (ht : term.isDigit = false) (hp : Plain [term] := by decide) :
    Codec Nat where
  print n := decimal w n ++ [term]
  parse s := match span Char.isDigit s with
    | (ds, t :: r) => if t = term then some (valueRev ds.reverse, r) else none
    | (_, []) => none
  parse_print n rest := by
    simp [List.append_assoc,
      span_append Char.isDigit (fun c hc => ((decimal_spec w n).2 c hc).1) ht, (decimal_spec w n).1]
  plain n := plain_append (fun c hc => .inr ((decimal_spec w n).2 c hc).2) hp

/-! ## Lists -/

/-- `n` values of `c`, one after another. -/
def many (c : Codec α) : Nat → List Char → Option (List α × List Char)
  | 0, s => some ([], s)
  | n + 1, s => (c.parse s).bind fun (a, r) => (many c n r).map fun (as, r') => (a :: as, r')

theorem many_print (c : Codec α) (l : List α) (rest : List Char) :
    many c l.length ((l.map c.print).flatten ++ rest) = some (l, rest) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [many, List.append_assoc, c.parse_print, ih]

/-- A list: its length in decimal on a line of its own, then each value. -/
def list (c : Codec α) : Codec (List α) where
  print l := (nat 0 '\n' (by decide)).print l.length ++ (l.map c.print).flatten
  parse s := ((nat 0 '\n' (by decide)).parse s).bind fun (n, r) => many c n r
  parse_print l rest := by
    simp [List.append_assoc, (nat 0 '\n' (by decide)).parse_print, many_print]
  plain l := plain_append ((nat 0 '\n' (by decide)).plain _)
    (plain_flatten fun _ h => by obtain ⟨a, _, rfl⟩ := List.mem_map.mp h; exact c.plain a)

/-! ## Tokens -/

/-- A run of characters that `p` admits, then `term`, which `p` does not admit. -/
def token (p : Char → Bool) (term : Char) (ht : p term = false)
    (hp : ∀ c, p c = true → concealing c = false) (hterm : Plain [term] := by decide) :
    Codec {l : List Char // l.all p = true} where
  print l := l.1 ++ [term]
  parse s := match span p s with
    | (l, t :: r) => if h : t = term ∧ l.all p = true then some (⟨l, h.2⟩, r) else none
    | (_, []) => none
  parse_print l rest := by
    obtain ⟨l, hl⟩ := l
    have hl' : ∀ c ∈ l, p c = true := List.all_eq_true.mp hl
    simp [List.append_assoc, span_append p hl' ht, hl]
  plain l := plain_append (fun c hc => .inr (hp c (List.all_eq_true.mp l.2 c hc))) hterm

/-! ## Lines -/

/-- The lowercase hexadecimal digit of `k`, for `k < 16`. -/
def hexChar (k : Nat) : Char := if k < 10 then digitChar k else Char.ofNat (87 + k)

/-- The value of a lowercase hexadecimal digit. -/
def hexValue? (c : Char) : Option Nat :=
  if c.isDigit then some (digitValue c) else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 87) else none

theorem hexChar_spec :
    ∀ k, k < 16 → hexValue? (hexChar k) = some k ∧ concealing (hexChar k) = false := by
  decide

/-- The four lowercase hexadecimal digits of `n`, for `n < 0x10000`. -/
def hex4 (n : Nat) : List Char :=
  [hexChar (n / 4096 % 16), hexChar (n / 256 % 16), hexChar (n / 16 % 16), hexChar (n % 16)]

/-- The value of four hexadecimal digits. -/
def hexValue4? (a b d e : Char) : Option Nat := do
  pure ((← hexValue? a) * 4096 + (← hexValue? b) * 256 + (← hexValue? d) * 16 + (← hexValue? e))

theorem hexValue4?_hex4 {n : Nat} (h : n < 0x10000) :
    hexValue4? (hexChar (n / 4096 % 16)) (hexChar (n / 256 % 16)) (hexChar (n / 16 % 16))
      (hexChar (n % 16)) = some n := by
  simp [hexValue4?, (hexChar_spec _ (Nat.mod_lt _ (by decide : 16 > 0))).1] <;> omega

theorem lt_of_concealing {c : Char} (h : concealing c = true) : c.toNat < 0x10000 := by
  simp only [concealing, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  omega

/-- How `c` is written in a line: `\\` for `\`, `\u` and four hexadecimal digits for a concealing
character, and `c` itself otherwise. -/
def escapeChar (c : Char) : List Char :=
  if c = '\\' then ['\\', '\\'] else if concealing c then '\\' :: 'u' :: hex4 c.toNat else [c]

/-- `c` in front of the characters read so far. -/
def prepend (c : Char) : List Char × List Char → List Char × List Char := fun (l, r) => (c :: l, r)

/-- The characters of an escaped line up to its line feed, and the rest after it. -/
def unescape : List Char → Option (List Char × List Char)
  | [] => none
  | c :: s =>
    if c = '\n' then some ([], s)
    else if c = '\\' then
      match s with
      | x :: r =>
        if x = '\\' then (unescape r).map (prepend '\\')
        else if x = 'u' then
          match r with
          | a :: b :: d :: e :: r' =>
            (hexValue4? a b d e).bind fun n => (unescape r').map (prepend (Char.ofNat n))
          | _ => none
        else none
      | [] => none
    else (unescape s).map (prepend c)

theorem concealing_newline : concealing '\n' = true := by decide

theorem unescape_escape (l rest : List Char) :
    unescape (l.flatMap escapeChar ++ '\n' :: rest) = some (l, rest) := by
  induction l with
  | nil => rw [unescape.eq_def]; simp
  | cons c l ih =>
    simp only [List.flatMap_cons, List.append_assoc, escapeChar]
    by_cases hb : c = '\\'
    · subst hb
      simp only [↓reduceIte, List.cons_append, List.nil_append]
      rw [unescape.eq_def]
      simp [ih, prepend]
    · by_cases hc : concealing c = true
      · have hn := hexValue4?_hex4 (lt_of_concealing hc)
        simp [hb, hc, unescape, hex4, hn, ih, prepend]
      · have hnl : c ≠ '\n' := fun h => hc (h ▸ concealing_newline)
        simp only [hb, hc, ↓reduceIte]
        rw [unescape.eq_def]
        simp [hb, hnl, ih, prepend]

theorem plain_escapeChar (c : Char) : Plain (escapeChar c) := by
  unfold escapeChar
  split
  · decide
  · split
    · intro x hx
      simp only [hex4, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · decide
      · decide
      all_goals exact .inr (hexChar_spec _ (Nat.mod_lt _ (by decide))).2
    · intro x hx
      simp only [List.mem_singleton] at hx
      subst hx
      exact .inr (by simp_all)

theorem plain_escape (l : List Char) : Plain (l.flatMap escapeChar) := by
  induction l with
  | nil => exact plain_nil
  | cons c l ih => rw [List.flatMap_cons]; exact plain_append (plain_escapeChar c) ih

/-- Any string on one line: each character as `escapeChar` writes it, then a line feed. -/
def line : Codec String where
  print s := s.toList.flatMap escapeChar ++ ['\n']
  parse s := (unescape s).map fun (l, r) => (String.ofList l, r)
  parse_print s rest := by simp [List.append_assoc, unescape_escape, String.ofList_toList]
  plain s := plain_append (plain_escape _) (by decide)

/-! ## Text -/

/-- The lines of `s`: the runs of characters between its line feeds. -/
def splitLines : List Char → List (List Char)
  | [] => [[]]
  | c :: s =>
    if c = '\n' then [] :: splitLines s
    else match splitLines s with
      | l :: ls => (c :: l) :: ls
      | [] => [[c]]

/-- Lines joined by line feeds. -/
def joinLines : List (List Char) → List Char
  | [] => []
  | [l] => l
  | l :: l' :: ls => l ++ '\n' :: joinLines (l' :: ls)

theorem joinLines_splitLines (s : List Char) :
    joinLines (splitLines s) = s ∧ splitLines s ≠ [] := by
  induction s with
  | nil => simp [splitLines, joinLines]
  | cons c s ih =>
    obtain ⟨ih, hne⟩ := ih
    obtain ⟨l, ls, hs⟩ : ∃ l ls, splitLines s = l :: ls := by
      cases h : splitLines s with
      | nil => exact absurd h hne
      | cons l ls => exact ⟨l, ls, rfl⟩
    rw [hs] at ih
    by_cases hc : c = '\n'
    · subst hc; simp [splitLines, hs, joinLines, ih]
    · simp only [splitLines, hc, ↓reduceIte, hs]
      refine ⟨?_, by simp⟩
      cases ls with
      | nil => simp [joinLines] at ih ⊢; exact ih
      | cons l' ls => simp [joinLines] at ih ⊢; exact ih

/-- Any string, as the number of its lines on a line of its own, then each line as `| ` and the
line. A string with no line feed has one line, the empty string included. -/
def text : Codec String :=
  map (list (keyed chars!"| " (by decide) line))
    (fun s => (splitLines s.toList).map String.ofList)
    (fun ls => some (String.ofList (joinLines (ls.map String.toList))))
    (fun s => by
      simp [List.map_map, Function.comp_def, String.toList_ofList, (joinLines_splitLines _).1,
        String.ofList_toList])

end LeanIntent.Codec
