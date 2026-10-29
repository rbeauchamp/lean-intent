/-!
# The tokens of the printed form, their text, and a lexer that reads the text back

The printer of `LeanIntent.Print.Term` writes a Lean term as a list of tokens (`Tok`), and this
module writes the tokens as text (`render`) and reads the text back (`lex`). The text is Lean's
own surface syntax for terms, restricted to a closed set of forms:

* identifiers, written as Lean writes them: each component as it is when it is a valid identifier
  that is no keyword of the grammar, and otherwise between `«` and `»`;
* decimal numerals, and string literals with `\\`, `\"` and `\n` as their only escapes;
* the keywords `fun`, `let`, `have`, `Sort`, `Type`, `Prop`, `nat_lit`, `max` and `imax`;
* the symbols `( ) { } [ ] ⦃ ⦄ @ : := ; , => → ∀ .{ +`.

Tokens are separated by one space, except after an opening bracket, `@` or `.{`, and before a
closing bracket, `,`, `;` or `.{`, where they are written together, as Lean requires for `.{`.

`lex_render` proves that `lex` reads back every list of well-formed tokens (`Tok.WF`) that
`render` writes, for every predicate `esc` that chooses further components to write escaped. So
two lists of well-formed tokens that `render` writes the same are equal. The lexer reads an
identifier as Lean's own lexer does (`Lean.Parser.identFnAux` at the pinned release, with the
character classes `Lean.isIdFirst` and `Lean.isIdRest` that this module uses): a component is an
identifier character followed by a run of them, or an escaped run, and a `.` continues the
identifier only when an identifier character or `«` follows it. Lean's lexer also reads as a
keyword an identifier that its token table holds; the printer avoids that by writing escaped the
components `esc` chooses, such as the tokens of the reader's grammar.
-/

namespace LeanIntent.Print

open Lean (Name isIdFirst isIdRest)

/-- The tokens of the printed form. -/
inductive Tok where
  | lparen | rparen | lbrace | rbrace | lbrack | rbrack | lstrict | rstrict
  | atSign | colon | colonEq | semicolon | comma | darrow | arrow | pi | dotBrace | plus
  | kwFun | kwLet | kwHave | kwSort | kwType | kwProp | kwNatLit | kwMax | kwImax
  /-- An identifier, given as the name it denotes. -/
  | ident (n : Name)
  /-- A decimal numeral. -/
  | num (n : Nat)
  /-- A string literal. -/
  | str (s : String)
  deriving DecidableEq, Inhabited

/-- The keyword a run of characters is, if it is one. -/
def keyword : List Char → Option Tok
  | ['f', 'u', 'n'] => some .kwFun
  | ['l', 'e', 't'] => some .kwLet
  | ['h', 'a', 'v', 'e'] => some .kwHave
  | ['S', 'o', 'r', 't'] => some .kwSort
  | ['T', 'y', 'p', 'e'] => some .kwType
  | ['P', 'r', 'o', 'p'] => some .kwProp
  | ['n', 'a', 't', '_', 'l', 'i', 't'] => some .kwNatLit
  | ['m', 'a', 'x'] => some .kwMax
  | ['i', 'm', 'a', 'x'] => some .kwImax
  | _ => none

/-- A component written as it is: a valid identifier, by Lean's character classes, that is no
keyword. -/
def rawable (s : String) : Bool :=
  match s.toList with
  | c :: cs => isIdFirst c && cs.all isIdRest && (keyword (c :: cs)).isNone
  | [] => false

/-- A component's text: as it is when `rawable` and not chosen by `esc`, and otherwise escaped. -/
def compText (esc : String → Bool) (s : String) : List Char :=
  if rawable s && !esc s then s.toList else '«' :: s.toList ++ ['»']

/-- An identifier's text, from its components, leftmost first. -/
def identText (esc : String → Bool) : List String → List Char
  | [] => []
  | [s] => compText esc s
  | s :: ss => compText esc s ++ '.' :: identText esc ss

/-- The components of a name, leftmost first, when every one is a string. -/
def comps : Name → Option (List String)
  | .anonymous => some []
  | .str p s => (comps p).map (· ++ [s])
  | .num _ _ => none

/-- The name with the given components, leftmost first. -/
def ofComps (ss : List String) : Name := ss.foldl .str .anonymous

/-- The decimal digit for `d < 10`. -/
def digit (d : Nat) : Char := Char.ofNat (48 + d)

/-- The decimal numeral of `n`. -/
def decimal (n : Nat) : List Char :=
  if _h : n < 10 then [digit n] else decimal (n / 10) ++ [digit (n % 10)]
termination_by n
decreasing_by omega

/-- The number a run of decimal digits denotes. -/
def ofDecimal (cs : List Char) : Nat := cs.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0

/-- A string literal's contents with `\`, `"` and the newline escaped. -/
def escStr : List Char → List Char
  | [] => []
  | c :: cs =>
    (if c = '\\' then ['\\', '\\'] else if c = '"' then ['\\', '"']
      else if c = '\n' then ['\\', 'n'] else [c]) ++ escStr cs

/-- A token's text. -/
def Tok.text (esc : String → Bool) : Tok → List Char
  | .lparen => ['('] | .rparen => [')'] | .lbrace => ['{'] | .rbrace => ['}']
  | .lbrack => ['['] | .rbrack => [']'] | .lstrict => ['⦃'] | .rstrict => ['⦄']
  | .atSign => ['@'] | .colon => [':'] | .colonEq => [':', '='] | .semicolon => [';']
  | .comma => [','] | .darrow => ['=', '>']
  | .arrow => ['→'] | .pi => ['∀'] | .dotBrace => ['.', '{'] | .plus => ['+']
  | .kwFun => ['f', 'u', 'n'] | .kwLet => ['l', 'e', 't'] | .kwHave => ['h', 'a', 'v', 'e']
  | .kwSort => ['S', 'o', 'r', 't']
  | .kwType => ['T', 'y', 'p', 'e'] | .kwProp => ['P', 'r', 'o', 'p']
  | .kwNatLit => ['n', 'a', 't', '_', 'l', 'i', 't'] | .kwMax => ['m', 'a', 'x']
  | .kwImax => ['i', 'm', 'a', 'x']
  | .ident n => identText esc ((comps n).getD [])
  | .num n => decimal n
  | .str s => '"' :: escStr s.toList ++ ['"']

/-- A token can be written and read back: an identifier names a name whose components are all
strings, at least one, and each is `rawable` or holds no `»`. -/
def Tok.WF : Tok → Prop
  | .ident n => ∃ ss, comps n = some ss ∧ ss ≠ [] ∧ ∀ s ∈ ss, rawable s ∨ '»' ∉ s.toList
  | _ => True

/-- Whether two consecutive tokens are written together, with no space between them. -/
def glue : Tok → Tok → Bool
  | .lparen, _ | .lbrace, _ | .lbrack, _ | .lstrict, _ | .atSign, _ | .dotBrace, _ => true
  | _, .rparen | _, .rbrace | _, .rbrack | _, .rstrict | _, .comma | _, .semicolon
  | _, .dotBrace => true
  | _, _ => false

/-- The text of a list of tokens. -/
def render (esc : String → Bool) : List Tok → List Char
  | [] => []
  | [t] => t.text esc
  | t :: u :: ts => t.text esc ++ (if glue t u then [] else [' ']) ++ render esc (u :: ts)

/-! ## The lexer -/

/-- An escaped component's contents, read up to its closing `»`. -/
def lexEsc : List Char → Option (List Char × List Char)
  | [] => none
  | c :: cs => if c = '»' then some ([], cs) else (lexEsc cs).map fun (a, r) => (c :: a, r)

/-- The longest prefix of characters that satisfy `p`, and the rest. -/
def spanBy (p : Char → Bool) : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs => if p c then let (a, r) := spanBy p cs; (c :: a, r) else ([], c :: cs)

/-- One component of an identifier, and whether it was written as it is. -/
def lexComp : List Char → Option (String × Bool × List Char)
  | [] => none
  | c :: cs =>
    if c = '«' then (lexEsc cs).map fun (a, r) => (String.ofList a, false, r)
    else if isIdFirst c then
      let (a, r) := spanBy isIdRest cs
      some (String.ofList (c :: a), true, r)
    else none

/-- Whether a `.` at the start of the text continues an identifier, as in Lean's lexer
(`Lean.Parser.isIdCont`). -/
def continues : List Char → Bool
  | '.' :: c :: _ => isIdFirst c || c = '«'
  | _ => false

/-- The components of an identifier after those in `acc`, whether it is one component written as
it is, and the text after it. -/
def lexIdent : Nat → List String → List Char → Option (List String × Bool × List Char)
  | 0, _, _ => none
  | f + 1, acc, cs => do
    let (s, raw, r) ← lexComp cs
    if continues r then lexIdent f (acc ++ [s]) r.tail
    else some (acc ++ [s], raw && acc.isEmpty, r)

/-- A string literal's contents, read up to its closing `"`. -/
def lexStr : List Char → Option (List Char × List Char)
  | '"' :: r => some ([], r)
  | '\\' :: '\\' :: r => (lexStr r).map fun (a, r) => ('\\' :: a, r)
  | '\\' :: '"' :: r => (lexStr r).map fun (a, r) => ('"' :: a, r)
  | '\\' :: 'n' :: r => (lexStr r).map fun (a, r) => ('\n' :: a, r)
  | '\\' :: _ => none
  | c :: r => (lexStr r).map fun (a, r) => (c :: a, r)
  | [] => none

/-- The single-character symbols and their tokens. -/
def symbol : Char → Option Tok
  | '(' => some .lparen | ')' => some .rparen | '{' => some .lbrace | '}' => some .rbrace
  | '[' => some .lbrack | ']' => some .rbrack | '⦃' => some .lstrict | '⦄' => some .rstrict
  | '@' => some .atSign | ';' => some .semicolon | ',' => some .comma | '→' => some .arrow
  | '∀' => some .pi | '+' => some .plus
  | _ => none

/-- One token at the start of a text that does not start with a space. -/
def lexOne : List Char → Option (Tok × List Char)
  | [] => none
  | c :: cs =>
    if isIdFirst c || c = '«' then do
      let (ss, raw, r) ← lexIdent (c :: cs).length [] (c :: cs)
      match raw, ss with
      | true, [s] => some ((keyword s.toList).getD (.ident (ofComps ss)), r)
      | _, _ => some (.ident (ofComps ss), r)
    else if c.isDigit then
      let (ds, r) := spanBy Char.isDigit (c :: cs)
      some (.num (ofDecimal ds), r)
    else if c = '"' then (lexStr cs).map fun (a, r) => (.str (String.ofList a), r)
    else if c = '=' then
      match cs with
      | '>' :: r => some (.darrow, r)
      | _ => none
    else if c = '.' then
      match cs with
      | '{' :: r => some (.dotBrace, r)
      | _ => none
    else if c = ':' then
      match cs with
      | '=' :: r => some (.colonEq, r)
      | _ => some (.colon, cs)
    else (symbol c).map (·, cs)

/-- The tokens of a text, each after the spaces before it. -/
def lexAux : Nat → List Char → Option (List Tok)
  | 0, _ => none
  | f + 1, cs =>
    match cs.dropWhile (· = ' ') with
    | [] => some []
    | cs => do
      let (t, r) ← lexOne cs
      let ts ← lexAux f r
      some (t :: ts)

/-- The tokens of a text. -/
def lex (cs : List Char) : Option (List Tok) := lexAux (cs.length + 1) cs

/-! ## Reading back what is written -/

theorem ofComps_append (ss : List String) (s : String) :
    ofComps (ss ++ [s]) = .str (ofComps ss) s := by
  simp [ofComps, List.foldl_append]

theorem ofComps_of_comps : (n : Name) → {ss : List String} → comps n = some ss → ofComps ss = n
  | .anonymous, _, h => by simp [comps] at h; subst h; rfl
  | .str p s, ss, h => by
    simp only [comps, Option.map_eq_some_iff] at h
    obtain ⟨ss', h', rfl⟩ := h
    rw [ofComps_append, ofComps_of_comps p h']
  | .num _ _, _, h => by simp [comps] at h

theorem digit_isDigit {d : Nat} (h : d < 10) : (digit d).isDigit = true := by
  have : ∀ d, d < 10 → (digit d).isDigit = true := by decide
  exact this d h

theorem digit_toNat {d : Nat} (h : d < 10) : (digit d).toNat - 48 = d := by
  have : ∀ d, d < 10 → (digit d).toNat - 48 = d := by decide
  exact this d h

theorem decimal_isDigit (n : Nat) : ∀ c ∈ decimal n, c.isDigit = true := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [decimal]
    split
    · next h => simpa using digit_isDigit h
    · next h =>
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact ih (n / 10) (by omega) c hc
      · simp only [List.mem_singleton] at hc
        exact hc ▸ digit_isDigit (Nat.mod_lt _ (by omega))

theorem decimal_ne_nil (n : Nat) : decimal n ≠ [] := by
  rw [decimal]; split <;> simp

theorem ofDecimal_decimal (n : Nat) : ofDecimal (decimal n) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [decimal]
    split
    · next h => simp [ofDecimal, digit_toNat h]
    · next h =>
      have := ih (n / 10) (by omega)
      simp only [ofDecimal, List.foldl_append, List.foldl_cons, List.foldl_nil] at this ⊢
      rw [this, digit_toNat (Nat.mod_lt _ (by omega))]
      omega

theorem spanBy_append (p : Char → Bool) (cs rest : List Char) (hcs : ∀ c ∈ cs, p c = true)
    (hr : ∀ c, rest.head? = some c → p c = false) :
    spanBy p (cs ++ rest) = (cs, rest) := by
  induction cs with
  | nil =>
    cases rest with
    | nil => rfl
    | cons c r => simp [spanBy, hr c rfl]
  | cons c cs ih =>
    simp only [List.cons_append, spanBy, hcs c (List.mem_cons_self ..), ite_true]
    rw [ih (fun c h => hcs c (List.mem_cons_of_mem _ h))]

theorem lexStr_escStr (cs rest : List Char) : lexStr (escStr cs ++ '"' :: rest) = some (cs, rest) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [escStr]
    by_cases h1 : c = '\\'
    · subst h1; simp [lexStr, ih]
    by_cases h2 : c = '"'
    · subst h2; simp [lexStr, ih]
    by_cases h3 : c = '\n'
    · subst h3; simp [lexStr, ih]
    simp only [h1, h2, h3, ite_false, List.cons_append]
    rw [lexStr.eq_def]
    split <;> simp_all

theorem lexEsc_append (cs rest : List Char) (h : '»' ∉ cs) :
    lexEsc (cs ++ '»' :: rest) = some (cs, rest) := by
  induction cs with
  | nil => simp [lexEsc]
  | cons c cs ih =>
    simp only [List.mem_cons, not_or] at h
    simp [lexEsc, Ne.symm h.1, ih h.2]

theorem decimal_digits (n : Nat) : ∀ c ∈ decimal n, ∃ d, d < 10 ∧ c = digit d := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [decimal]
    split
    · next h => simp only [List.mem_singleton]; exact fun c hc => ⟨n, h, hc⟩
    · next h =>
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact ih (n / 10) (by omega) c hc
      · simp only [List.mem_singleton] at hc
        exact ⟨n % 10, Nat.mod_lt _ (by omega), hc⟩

theorem not_idFirst_of_mem_decimal {n : Nat} {c : Char} (h : c ∈ decimal n) :
    (isIdFirst c || c = '«') = false := by
  obtain ⟨d, hd, rfl⟩ := decimal_digits n c h
  have : ∀ d, d < 10 → (isIdFirst (digit d) || digit d = '«') = false := by decide
  exact this d hd

theorem not_endEscape_of_rawable {s : String} (h : rawable s = true) : '»' ∉ s.toList := by
  unfold rawable at h
  split at h
  · next c cs hs =>
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    rw [hs]
    intro hm
    rcases List.mem_cons.mp hm with he | he
    · subst he; exact absurd h.1.1 (by decide)
    · exact absurd (h.1.2 _ he) (by decide)
  · simp at h

/-- What may follow an identifier's text: no identifier character, and no `.` that continues the
identifier. -/
def Stop (rest : List Char) : Prop :=
  continues rest = false ∧ ∀ c, rest.head? = some c → isIdRest c = false

theorem compText_head (esc : String → Bool) (s : String) (_hs : rawable s ∨ '»' ∉ s.toList) :
    ∃ c cs, compText esc s = c :: cs ∧ (isIdFirst c || c = '«') = true := by
  unfold compText
  split
  · next h =>
    simp only [Bool.and_eq_true] at h
    have h1 := h.1
    unfold rawable at h1
    split at h1
    · next c cs hcs => exact ⟨c, cs, hcs, by simp_all⟩
    · simp at h1
  · exact ⟨'«', _, rfl, by decide⟩

theorem lexComp_compText (esc : String → Bool) (s : String) (hs : rawable s ∨ '»' ∉ s.toList)
    (rest : List Char) (hr : ∀ c, rest.head? = some c → isIdRest c = false) :
    lexComp (compText esc s ++ rest) = some (s, rawable s && !esc s, rest) := by
  unfold compText
  split
  · next h =>
    have h1 : rawable s = true := by simp_all
    have h1' := h1
    unfold rawable at h1'
    split at h1'
    · next c cs hcs =>
      simp only [Bool.and_eq_true, List.all_eq_true] at h1'
      have hc : c ≠ '«' := fun he => by subst he; exact absurd h1'.1.1 (by decide)
      rw [hcs]
      simp only [List.cons_append, lexComp, hc, ite_false, h1'.1.1, ite_true]
      rw [spanBy_append isIdRest cs rest h1'.1.2 hr, ← hcs, String.ofList_toList, h]
    · simp at h1'
  · next h =>
    have hm : '»' ∉ s.toList := by
      rcases hs with hs | hs
      · exact not_endEscape_of_rawable hs
      · exact hs
    simp only [List.cons_append, List.append_assoc, lexComp, ite_true,
      lexEsc_append _ _ hm, Option.map_some, String.ofList_toList]
    simp_all

/-- Whether the lexer reads an identifier of the components `ss` read after `acc` as one
component written as it is. -/
def identFlag (esc : String → Bool) (acc : List String) : List String → Bool
  | [s] => rawable s && !esc s && acc.isEmpty
  | _ => false

theorem lexIdent_identText (esc : String → Bool) (rest : List Char) (hr : Stop rest) :
    (ss : List String) → ss ≠ [] → (∀ s ∈ ss, rawable s ∨ '»' ∉ s.toList) →
    (f : Nat) → ss.length ≤ f → (acc : List String) →
    lexIdent f acc (identText esc ss ++ rest) = some (acc ++ ss, identFlag esc acc ss, rest)
  | [], h, _, _, _, _ => absurd rfl h
  | [s], _, hs, f + 1, _, acc => by
    have hs' := hs s (List.mem_singleton_self _)
    simp [identText, lexIdent, lexComp_compText esc s hs' rest hr.2, hr.1, identFlag, Bind.bind,
      Option.bind]
  | s :: s' :: ss, _, hs, f + 1, hf, acc => by
    have hs1 := hs s (List.mem_cons_self ..)
    obtain ⟨c, cs, hc, hcf⟩ := compText_head esc s' (hs s' (by simp))
    have hdot : ∀ c, ('.' :: (identText esc (s' :: ss) ++ rest)).head? = some c →
        isIdRest c = false := by
      intro c h; simp at h; subst h; decide
    have hcont : continues ('.' :: (identText esc (s' :: ss) ++ rest)) = true := by
      cases ss with
      | nil => simp only [identText, hc, List.cons_append, continues]; exact hcf
      | cons s'' ss => simp only [identText, hc, List.cons_append, continues]; exact hcf
    have ih := lexIdent_identText esc rest hr (s' :: ss) (by simp)
      (fun t ht => hs t (List.mem_cons_of_mem _ ht)) f (by simp at hf ⊢; omega) (acc ++ [s])
    have hflag : identFlag esc (acc ++ [s]) (s' :: ss) = identFlag esc acc (s :: s' :: ss) := by
      cases ss <;> simp [identFlag]
    simp only [identText, List.append_assoc, List.cons_append, lexIdent,
      lexComp_compText esc s hs1 _ hdot]
    simp only [Bind.bind, Option.bind]
    rw [hcont]
    simp only [ite_true, List.tail_cons]
    rw [ih, hflag]
    simp

theorem length_le_identText (esc : String → Bool) :
    (ss : List String) → ss.length ≤ (identText esc ss).length
  | [] => by simp [identText]
  | [s] => by
    simp only [identText, compText, List.length_singleton]
    split
    · next h =>
      simp only [Bool.and_eq_true] at h
      have h1 := h.1; unfold rawable at h1; split at h1
      · next c cs hcs => rw [hcs]; simp
      · simp at h1
    · simp
  | s :: s' :: ss => by
    have := length_le_identText esc (s' :: ss)
    simp only [identText, List.length_append, List.length_cons] at this ⊢
    omega

/-- What may follow a token's text so that the lexer reads the token and nothing more. -/
def StopTok : Tok → List Char → Prop
  | .ident _, r | .kwFun, r | .kwLet, r | .kwHave, r | .kwSort, r | .kwType, r | .kwProp, r
  | .kwNatLit, r | .kwMax, r | .kwImax, r => Stop r
  | .num _, r => ∀ c, r.head? = some c → c.isDigit = false
  | .colon, r => ∀ c, r.head? = some c → c ≠ '='
  | _, _ => True

theorem lexOne_keyword (c : Char) (cs rest : List Char) (k : Tok) (hc : isIdFirst c = true)
    (hcs : ∀ c ∈ cs, isIdRest c = true) (hk : keyword (c :: cs) = some k) (hr : Stop rest) :
    lexOne ((c :: cs) ++ rest) = some (k, rest) := by
  have hc' : c ≠ '«' := fun he => by subst he; exact absurd hc (by decide)
  simp only [List.cons_append, lexOne, hc, Bool.true_or, ite_true]
  rw [lexIdent.eq_def]
  simp only [List.length_cons, lexComp, hc', ite_false, hc, ite_true, spanBy_append isIdRest cs rest hcs hr.2]
  simp only [Bind.bind, Option.bind, hr.1, Bool.false_eq_true, ite_false, List.nil_append,
    List.isEmpty_nil, Bool.and_true, String.toList_ofList, hk, Option.getD_some]

theorem lexOne_symbol (c : Char) (rest : List Char) (t : Tok) (h : symbol c = some t)
    (h1 : isIdFirst c = false) (h2 : c ≠ '«') (h3 : c.isDigit = false) (h4 : c ≠ '"')
    (h5 : c ≠ '=') (h6 : c ≠ '.') (h7 : c ≠ ':') : lexOne (c :: rest) = some (t, rest) := by
  simp [lexOne, h1, h2, h3, h4, h5, h6, h7, h]

theorem lexOne_text (esc : String → Bool) (t : Tok) (hwf : t.WF) (rest : List Char)
    (hr : StopTok t rest) : lexOne (t.text esc ++ rest) = some (t, rest) := by
  cases t with
  | kwFun => exact lexOne_keyword 'f' _ rest _ (by decide) (by decide) rfl hr
  | kwLet => exact lexOne_keyword 'l' _ rest _ (by decide) (by decide) rfl hr
  | kwHave => exact lexOne_keyword 'h' _ rest _ (by decide) (by decide) rfl hr
  | kwSort => exact lexOne_keyword 'S' _ rest _ (by decide) (by decide) rfl hr
  | kwType => exact lexOne_keyword 'T' _ rest _ (by decide) (by decide) rfl hr
  | kwProp => exact lexOne_keyword 'P' _ rest _ (by decide) (by decide) rfl hr
  | kwNatLit => exact lexOne_keyword 'n' _ rest _ (by decide) (by decide) rfl hr
  | kwMax => exact lexOne_keyword 'm' _ rest _ (by decide) (by decide) rfl hr
  | kwImax => exact lexOne_keyword 'i' _ rest _ (by decide) (by decide) rfl hr
  | ident n =>
    obtain ⟨ss, hss, hne, hok⟩ := hwf
    simp only [Tok.text, hss, Option.getD_some]
    obtain ⟨c, cs, hc, hcf⟩ : ∃ c cs, identText esc ss = c :: cs ∧ (isIdFirst c || c = '«') = true := by
      cases ss with
      | nil => exact absurd rfl hne
      | cons s ss =>
        obtain ⟨c, cs, h, hf⟩ := compText_head esc s (hok s (List.mem_cons_self ..))
        cases ss with
        | nil => exact ⟨c, cs, by simp [identText, h], hf⟩
        | cons s' ss => exact ⟨c, cs ++ '.' :: identText esc (s' :: ss), by simp [identText, h], hf⟩
    have hlex := lexIdent_identText esc rest hr ss hne hok ((identText esc ss ++ rest).length)
      (by have := length_le_identText esc ss; simp; omega) []
    rw [hc] at hlex ⊢
    simp only [List.cons_append, lexOne, hcf, ite_true]
    simp only [List.cons_append] at hlex
    simp only [Bind.bind, Option.bind, hlex, List.nil_append]
    have hn := ofComps_of_comps n hss
    split
    · next s hraw =>
      simp only [identFlag, Bool.and_eq_true] at hraw
      have hk : keyword s.toList = none := by
        have h1 := hraw.1.1; unfold rawable at h1; split at h1
        · next c' cs' hcs' => rw [hcs']; simp_all
        · simp at h1
      simp_all
    · simp_all
  | num n =>
    obtain ⟨c, cs, hc⟩ : ∃ c cs, decimal n = c :: cs := by
      cases h : decimal n with
      | nil => exact absurd h (decimal_ne_nil n)
      | cons c cs => exact ⟨c, cs, rfl⟩
    have hcf := not_idFirst_of_mem_decimal (n := n) (c := c) (by rw [hc]; simp)
    have hcd := decimal_isDigit n c (by rw [hc]; simp)
    simp only [Tok.text]
    have hspan := spanBy_append Char.isDigit (decimal n) rest (decimal_isDigit n) hr
    rw [hc] at hspan ⊢
    simp only [List.cons_append, lexOne, hcf, Bool.false_eq_true, ite_false, hcd, ite_true]
    simp only [List.cons_append] at hspan
    rw [hspan, ← hc, ofDecimal_decimal]
  | str s =>
    simp only [Tok.text, List.cons_append, List.append_assoc]
    simp only [lexOne, lexStr_escStr]
    have h1 : isIdFirst '"' = false := by decide
    have h2 : Char.isDigit '"' = false := by decide
    simp [h1, h2, String.ofList_toList]
  | darrow =>
    have h : isIdFirst '=' = false ∧ Char.isDigit '=' = false := by decide
    simp [Tok.text, lexOne, h]
  | dotBrace =>
    have h : isIdFirst '.' = false ∧ Char.isDigit '.' = false := by decide
    simp [Tok.text, lexOne, h]
  | colonEq =>
    have h : isIdFirst ':' = false ∧ Char.isDigit ':' = false := by decide
    simp [Tok.text, lexOne, h]
  | colon =>
    have h : isIdFirst ':' = false ∧ Char.isDigit ':' = false := by decide
    simp only [Tok.text, List.cons_append, List.nil_append]
    cases rest with
    | nil => simp [lexOne, h]
    | cons c r =>
      have hc : c ≠ '=' := hr c rfl
      simp [lexOne, h, hc]
  | lparen | rparen | lbrace | rbrace | lbrack | rbrack | lstrict | rstrict | atSign | semicolon
  | comma | arrow | pi | plus =>
    exact lexOne_symbol _ _ _ rfl (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)

theorem text_head (esc : String → Bool) (t : Tok) (hwf : t.WF) :
    ∃ c cs, t.text esc = c :: cs ∧ c ≠ ' ' := by
  cases t with
  | ident n =>
    obtain ⟨ss, hss, hne, hok⟩ := hwf
    simp only [Tok.text, hss, Option.getD_some]
    cases ss with
    | nil => exact absurd rfl hne
    | cons s ss =>
      obtain ⟨c, cs, h, hf⟩ := compText_head esc s (hok s (List.mem_cons_self ..))
      have hc : c ≠ ' ' := fun he => by subst he; revert hf; decide
      cases ss with
      | nil => exact ⟨c, cs, by simp [identText, h], hc⟩
      | cons s' ss => exact ⟨c, cs ++ '.' :: identText esc (s' :: ss), by simp [identText, h], hc⟩
  | num n =>
    cases h : decimal n with
    | nil => exact absurd h (decimal_ne_nil n)
    | cons c cs =>
      refine ⟨c, cs, by simp [Tok.text, h], fun he => ?_⟩
      have := decimal_isDigit n c (by rw [h]; simp)
      subst he; revert this; decide
  | _ => exact ⟨_, _, rfl, by decide⟩

theorem render_cons (esc : String → Bool) (u : Tok) (ts : List Tok) :
    ∃ r, render esc (u :: ts) = u.text esc ++ r := by
  cases ts with
  | nil => exact ⟨[], by simp [render]⟩
  | cons v ts =>
    exact ⟨(if glue u v then [] else [' ']) ++ render esc (v :: ts), by simp only [render, List.append_assoc]⟩

/-- `glue t u` holds when `t` opens or `u` closes. -/
theorem glue_cases {t u : Tok} (h : glue t u = true) :
    (t = .lparen ∨ t = .lbrace ∨ t = .lbrack ∨ t = .lstrict ∨ t = .atSign ∨ t = .dotBrace) ∨
      (u = .rparen ∨ u = .rbrace ∨ u = .rbrack ∨ u = .rstrict ∨ u = .comma ∨ u = .semicolon ∨
        u = .dotBrace) := by
  cases t <;> cases u <;> simp_all [glue]

theorem stopTok_sep (esc : String → Bool) (t u : Tok) (ts : List Tok) :
    StopTok t ((if glue t u then [] else [' ']) ++ render esc (u :: ts)) := by
  split
  · next h =>
    obtain ⟨r, hr⟩ := render_cons esc u ts
    rw [List.nil_append, hr]
    rcases glue_cases h with h | h
    · rcases h with h | h | h | h | h | h <;> subst h <;> trivial
    · have key : Stop (u.text esc ++ r) ∧
          (∀ c, (u.text esc ++ r).head? = some c → c.isDigit = false) ∧
          ∀ c, (u.text esc ++ r).head? = some c → c ≠ '=' := by
        rcases h with h | h | h | h | h | h | h <;> subst h <;>
          refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp [Tok.text, continues] <;> decide
      cases t <;> first | exact key.1 | exact key.2.1 | exact key.2.2 | trivial
  · have key : Stop ([' '] ++ render esc (u :: ts)) ∧
        (∀ c, ([' '] ++ render esc (u :: ts)).head? = some c → c.isDigit = false) ∧
        ∀ c, ([' '] ++ render esc (u :: ts)).head? = some c → c ≠ '=' := by
      refine ⟨⟨by simp [continues], ?_⟩, ?_, ?_⟩ <;> simp <;> decide
    cases t <;> first | exact key.1 | exact key.2.1 | exact key.2.2 | trivial

theorem dropWhile_space (esc : String → Bool) (t : Tok) (hwf : t.WF) (r : List Char) :
    (t.text esc ++ r).dropWhile (· = ' ') = t.text esc ++ r := by
  obtain ⟨c, cs, h, hc⟩ := text_head esc t hwf
  rw [h]; simp [hc]

theorem lexAux_spaces (f : Nat) (sp r : List Char) (hsp : ∀ c ∈ sp, c = ' ') :
    lexAux f (sp ++ r) = lexAux f r := by
  cases f with
  | zero => rfl
  | succ f =>
    have : (sp ++ r).dropWhile (· = ' ') = r.dropWhile (· = ' ') := by
      induction sp with
      | nil => rfl
      | cons c sp ih =>
        rw [List.cons_append, List.dropWhile_cons_of_pos (by simp [hsp c (List.mem_cons_self ..)])]
        exact ih (fun c h => hsp c (List.mem_cons_of_mem _ h))
    simp only [lexAux, this]

theorem lexAux_render (esc : String → Bool) :
    (ts : List Tok) → (∀ t ∈ ts, t.WF) → (f : Nat) → ts.length < f →
    lexAux f (render esc ts) = some ts
  | [], _, f + 1, _ => by simp [render, lexAux]
  | [t], hwf, f + 1, hf => by
    have ht := hwf t (List.mem_singleton_self _)
    have h1 := lexOne_text esc t ht [] (by cases t <;> simp [StopTok, Stop, continues])
    rw [List.append_nil] at h1
    have h2 := dropWhile_space esc t ht []
    rw [List.append_nil] at h2
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    simp only [render, lexAux, h2]
    obtain ⟨c, cs, hc, _⟩ := text_head esc t ht
    rw [hc] at h1 ⊢
    simp [h1]
  | t :: u :: ts, hwf, f + 1, hf => by
    have ht := hwf t (List.mem_cons_self ..)
    have ih := lexAux_render esc (u :: ts) (fun v hv => hwf v (List.mem_cons_of_mem _ hv)) f
      (by simp at hf ⊢; omega)
    have h1 := lexOne_text esc t ht _ (stopTok_sep esc t u ts)
    obtain ⟨c, cs, hc, _⟩ := text_head esc t ht
    have hrest : lexAux f ((if glue t u then [] else [' ']) ++ render esc (u :: ts)) = some (u :: ts) := by
      rw [lexAux_spaces f _ _ (by split <;> simp)]; exact ih
    simp only [render, List.append_assoc]
    rw [lexAux.eq_def]
    simp only [dropWhile_space esc t ht]
    rw [hc] at h1 ⊢
    simp only [List.cons_append] at h1 ⊢
    simp [h1, hrest]

/-- The lexer reads back every list of well-formed tokens that `render` writes. -/
theorem lex_render (esc : String → Bool) (ts : List Tok) (hwf : ∀ t ∈ ts, t.WF) :
    lex (render esc ts) = some ts := by
  apply lexAux_render esc ts hwf
  suffices ts.length ≤ (render esc ts).length by omega
  induction ts with
  | nil => simp
  | cons t ts ih =>
    obtain ⟨c, cs, hc, _⟩ := text_head esc t (hwf t (List.mem_cons_self ..))
    cases ts with
    | nil => simp [render, hc]
    | cons u ts =>
      have := ih (fun v hv => hwf v (List.mem_cons_of_mem _ hv))
      simp only [render, List.length_append, List.length_cons, hc] at this ⊢
      omega

end LeanIntent.Print
