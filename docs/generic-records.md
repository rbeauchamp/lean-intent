# Records generic in a world's types

**A record generic in its parameters** (`LeanIntent.Family`), such as the types a world is made of: what its obligations mean, what checking or rendering it at representative values establishes, and what it does not.

Modules: `LeanIntent/Generic.lean`, and `LeanIntent/Render.lean` for the rendering. Worked example: [`LeanIntentExamples/DayWorld.lean`](../LeanIntentExamples/DayWorld.lean).

**Complete in this version:** the link between a family and its instances, for every obligation, and the rendering of a generic explanation, in general and at representative values.

A generic record is a family of records, one for each value of its parameters. Its statements say nothing about how a world represents its types, which is what makes it the right record for a contract many worlds must meet. Two things then need saying that a record with no parameters does not raise: an obligation usually holds only where witnesses exist (a world with no situation may meet a record no function of which depends on a situation), and a proof or rendering at particular types is about those types.

## What an instance establishes

The generic claim for an obligation `O` is `Family.HoldsWhere r Good O`: it holds of the record at every parameter that meets `Good`, the condition its witnesses state. `O` is any predicate on the record of each parameter, so all of this holds of O2, O2 before running, O3, O4 and O5 alike.

| Claim | Theorem | Status |
|---|---|---|
| The statements of an instance are the family's with the parameters replaced | `r p` is the family applied to `p` | by definition |
| The generic claim gives the obligation at each instance meeting `Good` | `Family.HoldsWhere.at` | proved |
| A failure at an instance meeting `Good` refutes the generic claim | `Family.not_holdsWhere_of_at` | proved |
| The obligation at an instance shows only that some parameter has it | `Family.exists_of_at` | proved |
| A `Good` no parameter meets makes the generic claim hold of anything; an instance meeting `Good` shows it is not that | `Family.holdsWhere_of_empty`, `Family.not_vacuous` | proved |
| A model at one parameter gives a model at another along a map that keeps meeting the record | `Family.o2Run_along` | proved |
| **An obligation of a family does not in general follow from an instance** | `Family.not_generic`: for each of O2, O2 before running, O3, O4 and O5, a family of which it holds at one parameter and fails at another | proved |

So an instance can find a counterexample, can show that a condition can be met, and can be read; alone, it does not in general prove the generic record. In the worked example, O4 holds at the representative types (`rep_o4`) and fails at a world with no situation (`dayCycle_not_o4_without_a_situation`), so what is proved of the family is that it holds at every world with the witnesses (`family_o4`, `Good`), of which the representative world is one (`rep_good`).

## Rendering

A generic explanation is a constant whose type has binders before `Explanation r`, including any witnesses its consequences need. `#render_intent` lists those binders as the text's parameters and prints each statement with them free, so the rendering says what the record says, for every value. In the exact form each statement is closed over them with `fun`s.

`#render_intent_at e a₁ … aₙ` shows the same explanation at values, written as the arguments of an application of `e`: for instance the world's types at `Unit`, `Unit`, `Fin 4` and `Nat`. It reads each statement from `e` applied to those values, so no separate record is written that could differ from the generic one, and the text lists the values and says what they do not establish, naming the theorems above. A value that is a proof is shown by the proposition it proves. The definitions each listed value or proposition reaches are printed with the rest of the meaning.

An explanation declared at particular values and rendered with `#render_intent` says the same of them, whenever its record is a constant applied to arguments: the readable form then adds that note. A record written out at those values, not as a family applied to them, is simply a record, and nothing relates it to a family.

## What is trusted

- That the condition `Good` a project states is the one it means. A `Good` too narrow proves less than it seems to; `Family.not_vacuous` shows only that some parameter meets it, not that the parameters the project cares about do.
