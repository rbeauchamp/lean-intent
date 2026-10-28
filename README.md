# lean-intent

A Lean library for writing what an owner wants as formal properties, and for checking that those properties are adequate, before any code is written.

A proof shows that code meets its specification, never that the specification says what its owner meant. A specification that misses the owner's intent is a bug of the same standing as code that misses its specification. This library gives a Lean project, and the coding assistant working in it, seven things:

- **An intent record** (`LeanIntent.IntentRecord`): named properties of one deliverable's subject, over a vocabulary of predicates, under named domain hypotheses, written before the implementation exists.
- **The adequacy obligations O1 to O5**, each computed from the record by a goal former whose correctness theorem is proved, so an assistant obtains each obligation from the library instead of writing a weaker one by hand: the record is well formed (O1), its hypotheses and then the whole record have a model (O2), each property can fail (O3), a subject that does nothing fails it (O4), and any two subjects that meet it are equal or differ only in a freedom the owner confirms (O5).
- **The degenerate-subject check** (`LeanIntent.degenerate`, `LeanIntent.Verdicts`): the degenerate subjects of the record's type (each constant function, the identity, the empty output and each projection), computed from the type alone and never chosen per record; for each, a proved verdict on whether it meets the record; and each that does reported as a possibility for the owner to confirm or decline.
- **A refinement link** (`LeanIntent.Refines`, `LeanIntent.fulfils`): a proof that the code meets its specification, and a proof that the specification refines the intent record, compose into a proof that the code fulfils the intent.
- **A rendering for the owner** (`LeanIntent.Render`): each statement of a record and each consequence shown to the owner printed exactly, by a printer proved to parse back what it prints, beside a plain-word explanation of what it requires, rules out, still allows, and the freedom it leaves. The owner confirms the record by reading it.
- **The owner's answers** (`LeanIntent.Answer`, `LeanIntent.Accepted`): each consequence of a record the owner confirms or declines stays a requirement of every later revision, and a revision that breaks one is refused, by the answer it breaks.
- **Cone exclusion** (`LeanIntent.Cone.checkRecord`): a decision procedure, with a theorem stating what it decides, that refuses an intent record whose meaning depends on a declaration of its implementation, read from Lean's own environment.

**Complete in this version:** the intent record, the five obligations with their goal formers and correctness theorems, the progress theorem (the obligations refuse no record with content), the degenerate-subject check with the theorems that fix its class, the refinement link with its transfer theorems, the audited printer and the rendering of records and their consequences, the owner's answers with the type of the revisions that keep them, cone exclusion with the theorem stating what it decides, and worked examples. Every claim the library makes about itself is a theorem Lean's kernel checks, resting only on Lean's own axioms, except the one the rendering checks each time it runs, that Lean reads each printed statement back as the term it is; the repository has no tests.

**Not yet built**, each a separate issue of this repository: recording the owner's confirmations so that only the owner can make them (#5), and extending the degenerate check to types the project declares, higher-order subjects and large finite types (#11). Until #5 lands, nothing in the library establishes that the owner made a stored answer, or confirmed a record or a freedom.

## Using it

The library depends on nothing beyond Lean's own libraries, and builds on the Lean release `lean-toolchain` names (`v4.35.0`). Add it to a Lake project's `lakefile.toml`:

```toml
[[require]]
name = "lean-intent"
git = "https://github.com/rbeauchamp/lean-intent"
rev = "main"
```

Then write the intent record for one function, before its code:

```lean
import LeanIntent
open LeanIntent

def Sorted (l : List Int) : Prop := l.Pairwise (· ≤ ·)

def sorting : IntentRecord (List Int → List Int) where
  shape := .function _ _
  dom := []
  props := [⟨"sorted", fun f => ∀ l, Sorted (f l)⟩, ⟨"rearranges", fun f => ∀ l, (f l).Perm l⟩]
  vocab := [⟨"Sorted", List Int, Sorted⟩, ⟨"Perm", List Int × List Int, fun p => p.1.Perm p.2⟩]
```

and prove its obligations: `O2 sorting`, `O2Run sorting`, `O3 sorting`, `O4 sorting` and `O5 sorting .eq`. Each `Oi r` is the conjunction of the goals its former computes (`o2 r` and the rest), and `oi_correct` turns it into the intended proposition, which is usually the easier form to prove. O1 holds of every record by construction (`o1_wellTyped`). Then state and prove the degenerate check's verdicts, `Verdicts sorting [false, false]`: neither the function returning the empty list nor the identity meets the corrected record. [`LeanIntentExamples/Sorting.lean`](LeanIntentExamples/Sorting.lean) does all of this, and then proves an implementation fulfils the record through the refinement link.

## Showing a record to its owner

The owner reads each statement of a record, and each consequence they are asked to confirm, in two forms side by side: printed exactly, and explained in plain words. An explanation (`LeanIntent.Explanation r`) gives the record `r` a gloss (`LeanIntent.Gloss`) for its shape and for each domain hypothesis, property and vocabulary predicate, and lists the consequences shown to the owner, the consequences the owner answers (`LeanIntent.Consequence`, below), each with a gloss and a proof that it holds of `r` as shown (`Consequence.HoldsOf`): every model satisfies an entailment, and some model a possibility. Its type requires a gloss for every statement, and that proof for every consequence, so no consequence is shown as entailed or as possible unless it is. A gloss has four parts: what the statement requires, what it rules out, what it still allows, and the freedom it leaves, the freedom obligation O5 shows the owner.

```lean
import LeanIntent.Render
import LeanIntentExamples.Sorting

#render_intent LeanIntentExamples.Sorting.sortingExplained
```

`#render_intent` shows the rendering, a Markdown document, and `LeanIntent.Render.renderExplanation` returns it as text. `LeanIntent.Render` imports all of Lean, so only the project or tool that renders needs it.

What the rendering establishes, and what it does not:

- **The printed form determines the term.** `LeanIntent.Print.print` writes a term in a closed subset of Lean's syntax for terms, and `LeanIntent.Print.parse_print` proves that `LeanIntent.Print.parse` reads back from every text it writes the very term it printed, for every term; so two terms that print the same are equal (`print_injective`). `print_isSome_iff` proves which terms it prints (`LeanIntent.Print.Printable`): closed terms built from bound variables, constants, sorts, string and natural number literals, applications, `fun` and `∀`, whose names it can write and whose bound variables no binder of the same name shadows. It refuses every other term, such as one holding a `let`, rather than print it lossily.
- **Lean reads it as that term.** Before a statement is shown, Lean's own parser and elaborator must read its printed text, in the root namespace with nothing opened, as the same term, binder names aside, which Lean's kernel ignores. This is checked for each statement shown, not proved for every term: Lean's elaborator is a program outside this library. A statement that fails it is refused, and with it the rendering.
- **Binder names are kept where they can be written.** A binder Lean named itself (`a✝`) cannot be written, and one that shadows another, or has the name of a constant's first component, would be misread; the rendering renames just those binders before printing (`LeanIntent.Print.canon`), which changes nothing but their names (`eraseNames_canon`), and a `∀` among them whose variable is unused becomes an arrow. So the printed text parses back to the statement up to those binders' names, which Lean's kernel ignores.
- **The plain words are trusted, not proved.** A gloss is written by a model; nothing checks that it says what the statement says. The exact statement beside it is what Lean checks, and the owner can read either.
- **Definitions.** The rendering also prints the definitions the statements use from outside Lean's own libraries and this one, with their types and values, so that a statement naming a project's predicate can be read to the end. They are not statements of the record and have no gloss of their own; one that cannot be printed is listed with a note saying so.

## The obligations

| Obligation | What it asks of a record `r` | Former and correctness theorem |
|---|---|---|
| O1, well formed | Every statement is a well-typed proposition. Its goal is a type: each statement paired with the type it is admitted at, which Lean's kernel checks when `r` is declared, so O1 holds by construction. | `o1`, `o1_correct`, `o1_wellTyped` |
| O2, satisfiable | At confirmation: a subject of which every domain hypothesis holds, and an instance of each vocabulary predicate. Before a deliverable runs: a subject that meets the whole record, which the deliverable supplies. | `o2`, `o2_correct`; `o2Run`, `o2Run_correct` |
| O3, refutable | Each property has a subject that fails it. | `o3`, `o3_correct` |
| O4, progress | By the subject's `Shape`: nothing of a plain value; totality of a function, which every Lean function has; and for a step of a system with state, that every step leaving the state unchanged fails the record. | `o4`, `o4_correct` |
| O5, determinate or confirmed freedom | Any two subjects that meet the record are equal (`.eq`), related by a relation the owner confirms (`.rel R`), or only both models (`.widest`), which every record meets, so O5 never refuses on its own: it makes the freedom a question for the owner. | `o5`, `o5_correct` |

Each correctness theorem equates the former's output with an intended proposition written by a direct match on the record, sharing no definition with the former or its helpers, for every record, so a former that stated `True`, a weaker proposition, or the obligation for one example only would fail it.

## The degenerate subjects

A record can have a model and still be met by a subject that does nothing useful: a sorting record that asks only for an ascending output is met by the function that returns the empty list. The degenerate check closes this with a closed class of degenerate subjects, fixed by the subject's type and never chosen per record. Here the class covers a subject of type `a₁ → … → aₙ → b`, a plain value when `n` is zero, whose argument and output types are built from `Unit`, `Bool`, `Nat`, `Int` and `String` by `List`, `Array`, `Option`, `×` and `⊕` (`LeanIntent.Ty`). Lean's instance resolution finds the type's code (`LeanIntent.Covered`); a type it finds none for, such as a structure the project declares, a dependent or higher-order function, or a type in a higher universe, is not covered, and Lean reports that it cannot synthesize `Covered`, so no verdict about it can be stated; wider coverage is #11. Because every `Covered W` carries a proof that its code stands for `W`, a code that mis-encodes its type cannot be given, and each degenerate subject is a value of `W` itself.

| Member | Which | Theorem |
|---|---|---|
| Constant functions | At every value of `b` when `b` has finitely many; otherwise, the constants being infinitely many, at the values the rule `Ty.Small` fixes: a number, string, list or array only at its empty value, the unit type and `Bool` at every value, and an option, pair or sum at each value built from its components' parts | `Sig.const_mem_of_finite`, `Sig.constants_infinite`, `Ty.mem_part_iff` |
| The empty output | The constant at `b`'s empty value, always a member | `Sig.empty_output_mem` |
| Projections | Each function returning a component of type `b` of one of its arguments: the argument itself, or a component of a pair inside it | `Sig.proj_mem` |
| The identity | The projection of a function of one argument to its own type | `Sig.identity_mem` |

`Sig.mem_degenerate_iff` states the class apart from the list that computes it, `Degenerate.apply_fn` what each member returns, and `degenerate_ne_nil` that no class is empty. `Verdicts r bs` is the check: its goals (`verdicts`) state, for each degenerate subject in order, that it meets `r` where `bs` says `true` and that it does not where `bs` says `false`, so every verdict is part of a theorem's statement and proved, and a list of the wrong length is refused (`verdicts_correct`). `metBy W bs` lists the subjects the verdicts report as meeting the record, exactly those that do (`mem_metBy`), and `possibilities h`, from a proof `h : Verdicts r bs`, reports each as a `Consequence` of kind possibility, the predicate that the subject is that degenerate subject, which holds of the record as shown (`mem_possibilities`, `possibilities_holdsOf`), so it can be shown to the owner with its gloss (`Shown`). A report exists only for proved verdicts. The owner's answer to it is stored and kept as every other answer is (below); a declined one is kept by exactly the revisions the degenerate subject does not meet (`Degenerate.declined_keptBy_iff`).

## The owner's answers

The owner validates a record by answering its consequences in plain words. A consequence (`Consequence`) is a named predicate on the record's subject, shown as an entailment, which every model of the record satisfies, or as a possibility, which some model satisfies, and the owner confirms or declines it (`Answer`). Every later revision `r` must keep each stored answer (`Answer.KeptBy`): the answer's unchanged predicate is applied to the subjects that meet `r`, under `r`'s domain hypotheses, never carried over as a fact proved about an earlier revision.

| Consequence | Confirmed: every later revision keeps | Declined: every later revision keeps |
|---|---|---|
| entailment `c` | a theorem: every model satisfies `c` | a countermodel: some model fails `c` |
| possibility `c` | a model that satisfies `c` | a refutation: no model satisfies `c` |

`kept r answers` computes one goal per stored answer, and `keeps_correct` fixes what they state, as the obligations' correctness theorems do. `Accepted answers` is the type of the revisions accepted under the stored answers: no value of it holds a revision that breaks one, and every revision that keeps them all is accepted (`accepted_iff`). A revision fails to keep the stored answers exactly when it keeps the opposite of one of them (`not_keeps_iff`), so every refusal names the answer it breaks and the witness that breaks it; answers that confirm and decline the same consequence refuse every revision until the owner retracts one (`not_keeps_of_conflict`). Whether a revision keeps them depends only on its models (`keeps_congr`): renaming its clauses or its vocabulary, or restating its properties with the same models, loses none, and a revision whose subject has another type cannot be accepted. A revision with no model at all keeps every confirmed entailment and declined possibility; `O2Run`, asked before a deliverable runs, refuses it.

A project keeps its answers by stating them over the record's subject type and declaring a value of `Accepted answers` for its current revision, as [`LeanIntentExamples/Answers.lean`](LeanIntentExamples/Answers.lean) does:

```lean
def answers : List (Answer (List Int → List Int)) :=
  [⟨⟨"returning the empty list for every input", .possibility, fun f => f = fun _ => []⟩, .declined⟩,
   ⟨⟨"returning [1, 2] for input [2, 1, 1] is ruled out", .entailment, fun f => f [2, 1, 1] ≠ [1, 2]⟩,
    .confirmed⟩]

def sortingAccepted : Accepted answers := ⟨sorting, sorting_keeps⟩
```

where `sorting_keeps : Keeps sorting answers` proves each answer of the current revision. A revision that breaks one leaves `sortingAccepted` without a proof of that answer's goal.

## Cone exclusion

A record written from the code proves nothing about intent: the property `fun f => f = impl` is met by `impl` whatever the owner meant. `LeanIntent.Cone.checkRecord env record impl` reads, from the environment `env`, the declarations that the meaning of the record declared as `record` depends on, transitively, and refuses the record when one of them is a declaration of the implementation: a name the list `impl` gives, or a declaration Lean names under one of them, as it names the auxiliary declarations it makes for a declaration `f` (`f.match_1`, `f._unary`, `f.eq_1`) and a `where` helper (`f.go`). A dependency reached through any declaration, an instance or an auxiliary declaration Lean generates included, is found. `LeanIntent.Cone.requireIndependent` runs the check in `CoreM` and throws an error that says why it refuses.

`checkRecord_eq_ok_iff` states what it decides, for every environment, record and implementation: it accepts exactly when `impl` names at least one declaration and every name it gives is declared, and every name reached from the record is no declaration of the implementation, is declared, and is no axiom other than those accepted (Lean's three by default), with at most `fuel` names reached. `exclude_eq_some` states that each refusal names a reached declaration, or that more than `fuel` names are reached.

It follows every declaration's type, every definition's value, and the mutual blocks, constructors and recursor rules of inductive types, but not a theorem's proof or an opaque constant's value: Lean's kernel never unfolds an opaque constant, and with definitional proof irrelevance any two proofs of a proposition are equal, so neither changes what the record means. It refuses rather than accepts when it cannot read the whole cone: a reached name with no declaration, or a reached axiom outside those accepted. In a module of Lean's module system, an imported theorem, and an imported definition whose body is not exposed, are shown as axioms, so run the check where every module is imported in full, such as in a file outside the module system. A property that restates the implementation's body without naming it passes the check; it reaches the owner as "the output is computed exactly as this expression", and noticing that is left to the owner's confirmation.

## Worked examples

- [`LeanIntentExamples/Sorting.lean`](LeanIntentExamples/Sorting.lean): a sorting record that forgets that the output is a rearrangement of the input fails O5, because the function returning the empty list meets it (`sortedOnly_not_o5_eq`); the corrected record meets O1 to O5, refutes that function, and is fulfilled by `List.mergeSort` through the refinement link. The degenerate check reports the empty-list function for the first record (`sortedOnly_verdicts`, `sortedOnly_possibilities`) and nothing for the corrected one (`sorting_verdicts`), which keeps the owner's declining it (`sorting_keeps_declined`). A contradictory domain hypothesis fails O2, and a property nothing fails fails O3. Both records are explained for their owner (`sortedOnlyExplained`, `sortingExplained`): shown the first, the owner declines its possibility that a function meeting it returns the empty list for every input.
- [`LeanIntentExamples/Counter.lean`](LeanIntentExamples/Counter.lean): a counter's step that may do nothing fails O4; one that must add one meets it. Declared with the wrong shape, as a plain value, the first record meets O4, yet the degenerate check still reports the step that does nothing (`neverDecreasesAsValue_verdicts`).
- [`LeanIntentExamples/Decision.lean`](LeanIntentExamples/Decision.lean): a procedure deciding evenness, `Nat → Bool`, whose output type has finitely many values, so the degenerate class holds the constant function at each; a record asking only for sound answers is met by the procedure that always answers `false`, which the check reports.
- [`LeanIntentExamples/Transfer.lean`](LeanIntentExamples/Transfer.lean): a refinement link carries the record's guarantees to the mapping's image, not to the implementations themselves.
- [`LeanIntentExamples/Answers.lean`](LeanIntentExamples/Answers.lean): the owner has declined the possibility of returning the empty list for every input and confirmed that returning `[1, 2]` for `[2, 1, 1]` is ruled out; the corrected sorting record keeps both and is accepted, so every accepted revision excludes the empty-list function; a revision that drops the rearrangement property is refused, breaking each answer by a witness; and a revision that renames the vocabulary and restates the two properties as one keeps both.
- [`LeanIntentExamples/Cone.lean`](LeanIntentExamples/Cone.lean): on a small environment written by hand, cone exclusion refuses a record that reaches the implementation through a helper (`cheat_refused`) and accepts one that does not (`honest_accepted`).

## What is trusted

- Lean, its kernel and its three axioms (`propext`, `Classical.choice`, `Quot.sound`).
- That a record's properties, domain hypotheses, vocabulary and shape say what the owner meant. This is the one link no proof reaches; the owner validates it by reading the record and answering its consequences, rendered by `LeanIntent.Render` and kept by `LeanIntent.Answers` (that only the owner can make a stored answer is #5).
- That a gloss says what its statement says. Glosses are written by a model and are not checked; the statement printed exactly beside each is.
- That Lean's parser and elaborator read every printed statement as the term it is: `LeanIntent.Render` checks this for each statement it shows, and no theorem states it for every term.
- That a record's shape is the one its subject has: a subject with state declared as a plain value is asked nothing by O4. The degenerate check, fixed by the subject's type rather than its declared shape, narrows this. For a covered step without output (`S → S`, `S → I → S`) the step that does nothing is a projection, so a record it meets reports it to the owner, though it does not refuse the record as O4 would. A step with output (`S → O × S`, `S → I → O × S`) does nothing by returning any output with the state unchanged. The class does not generally enumerate these state-preserving subjects, although some coincide with its constants or projections: for `Unit → Bool × Unit`, every constant preserves the state and is in the class. The shape therefore stays trusted.
- That the domain hypotheses are true of the world, which the owner confirms; a hypothesis that excludes the subject that does nothing, or all but one model, would make O4 or O5 hold vacuously, one that excludes a degenerate subject keeps the degenerate check from reporting it, and one that excludes the subject of a declined possibility keeps that answer vacuously.
- That a covered type has only the code the library's instances find for it, so that no record can be checked against a smaller class: another instance would have to prove its code's type equal to the type, and for two different codes that equates two different types, which Lean cannot prove without a further axiom. This is argued, not proved.
- That a constant function the class leaves out is not one the owner needed to see: where the output type has infinitely many values the class takes only the constants its rule fixes, so a record met by the function returning `[0]` for every input, and by no member, is not reported. No finite set of checked subjects closes this gap for every record; the freedom O5 shows the owner still spans it.
- That every record about a covered type has its verdicts stated, and every record about another type is checked by other means: Lean refuses to state verdicts about a type the class does not cover, but nothing in the library requires verdicts of a record, as nothing requires O1 to O5.
- That a stored answer's predicate still means what the owner confirmed. It is a Lean term, so a revision that changes the body of a definition it uses changes what it says without removing it; a predicate that uses only Lean's own library keeps its meaning while the Lean release does. That the owner made each stored answer, and the revision each applies to, is #5's.
- That a project checks its current revision against its stored answers, by declaring a value of `Accepted` for it under all of them; a project that declares none checks nothing.
- That a record was written before its implementation was read. That it does not depend on its implementation is decided by cone exclusion against the declarations the caller names; that those names, with the declarations Lean names under them, cover the implementation is trusted.
- That Lean's compiler runs cone exclusion as it is defined, and that `Environment.find?` returns the declarations Lean's kernel checked: cone exclusion's theorems are about its definitions.

## Checks

`tools/check.lean` is the repository's one check program. `lean --run tools/check.lean` builds the library with warnings as errors (a `sorry` is a warning), refuses a `lakefile.toml` that requires another package, and audits every declaration's axioms; `lean --run tools/check.lean --tests` lists the repository's tests, which must be none. Its module comment states what each rule decides and what it does not. lean-intent has no CI: the local no-mistakes validation is its merge gate, and its Test step runs both, failing when the listing prints anything (`commands.test` in `.no-mistakes.yaml`).

## Design

The obligations are Lean propositions about the record, and the store of statements is Lean's environment, in which a record, once declared, has a fixed value.
