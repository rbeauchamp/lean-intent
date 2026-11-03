# Precondition-postcondition pairs

**The pair obligation** (`LeanIntent.OPair`): for a precondition-postcondition pair of a record's property and a stated class of implementations, its precondition admits some input, and every input its precondition admits has an implementation in the class that meets its postcondition there. Its goal former's correctness theorem is proved for every pair and every class, so a project obtains the obligation from the library instead of writing a weaker one by hand. An admitted input that no implementation in the class can serve means the precondition is too wide for that class, and refutes the obligation.

Module: `LeanIntent/Pairs.lean`.

**Complete in this version:** the definition of a pair, the relation that makes a pair one of a record's property, the pair that every property has, the obligation with its former and correctness theorem, and the theorems below on its class and on what it does and does not establish.

## A pair

A property says something for each input. The input is whatever the implementation does not choose: an argument, a state, a world from a class. The precondition is what the record demands of that input, a domain hypothesis or a guard inside the property, `True` where it demands nothing. The postcondition is what the property then asks of the subject at that input. `Pair W` holds those three for subjects of type `W`: `Input`, `pre : Input → Prop` and `post : Input → W → Prop`. A subject meets the pair (`Pair.Met`) when it meets the postcondition at every input the precondition admits.

A pair is one of the property `c` of the record `r` (`r.PairOf c q`) when `c` is one of the record's properties and the pair says exactly what an implementation must prove of it: for every subject, `c` holds wherever the domain hypotheses do exactly when the subject meets the pair. Every property has such a pair, `Pair.whole r c`, whose only input is trivial and whose postcondition is the property under the domain hypotheses (`pairOf_whole`); so every property gives at least one pair, and a property of a value with no input gives one whose only input is trivial. A project states the finer pairs a property gives, each with the input the property's statement quantifies over, and proves each one a pair of the property.

## The obligation

`OPair q C` is the conjunction of the goals `oPair q C` computes, and `oPair_correct` equates it, for every pair and every class, with `intendedOPair q C`, written by a direct match on the pair and sharing no definition with the former or its helpers:

| Goal | What it asks | What refutes it |
|---|---|---|
| The precondition admits an input | Some input satisfies the precondition. | A precondition that admits no input, whatever the class (`not_oPair_of_admits_nothing`). |
| Every admitted input is served | For each input the precondition admits, some subject of the class `C` meets the postcondition there. | An admitted input that no subject of `C` serves (`not_oPair_of_unserved`): the precondition is too wide for `C`. |

The first goal is the method's "the precondition admits an input", so that a pair cannot pass because its precondition admits nothing. The second is the per-input statement itself. `oPair_of` builds the obligation from the two, and `OPair.admits` and `OPair.served` take them apart. Neither goal asks that some subject fail the postcondition. A pair whose precondition admits an input and whose postcondition every subject meets meets the obligation in every class that is not empty; that each property has a subject that fails it is O3, and whether a trivial witness meets a pair is the separate question below. This was decided on the owner's behalf, not by the owner, so that the obligation states what the method asks and no more.

**The class is a parameter.** `C : W → Prop` is a parameter of every statement, so the obligation claims nothing beyond the subjects `C` admits. It passes from a class to every wider one (`OPair.mono`) but not in general from a class to a narrower one (`LeanIntentExamples.Pairs.any_not_blind`), and no pair meets it in the empty class (`not_oPair_empty`). A class of implementations of another type `A`, read as subjects by `m : A → W` as in the refinement link, is the image `fun w => ∃ a, m a = w`.

## What the obligation establishes, and what it does not

- **One subject for the whole property.** The obligation of `Pair.whole r c` asks that a subject of the class fulfil the property wherever the domain hypotheses hold (`oPair_whole_iff`), and it gives the obligation of every pair of the property whose precondition admits an input (`OPair.of_whole`). The converse fails in general (`LeanIntentExamples.Pairs.perWorld_not_whole`).
- **Not that a pair asks for the work it is meant to.** The second goal lets the subject depend on the input, so a subject that fixes its answer to each input in advance, a table or a script, can serve every input. That no such trivial witness meets a pair is not checked by this library ([#41](https://github.com/rbeauchamp/lean-intent/issues/41)).
- **Not that a project's pair quantifies over what the property does.** `PairOf` checks what a pair says, not which input it is stated over. `Pair.selfNamed r c`, whose input names a subject and whose postcondition holds emptily of every other, is a pair of every property (`pairOf_selfNamed`), and it meets the obligation in every class with two different members, though no member may fulfil the property (`oPair_selfNamed`). `Pair.whole`, which no choice of input affects, is the form to prove where that matters.
- **Not that one subject meets every pair.** That is O2 before running (`O2Run`). A model of the record in the class serves every input each pair of its properties admits (`PairOf.served_of_meets`), so O2 before running, with its subject in the class, discharges the second goal of every pair; the pair obligation does not give O2 before running.

## Worked example

[`LeanIntentExamples/Pairs.lean`](../LeanIntentExamples/Pairs.lean): an agent sees one bit of its world and answers with one action, and the record asks it to reach the goal of every legible world, one in which what it sees is the action it needs. Its one property gives two pairs, the per-world pair `perWorld` and `Pair.whole`, both pairs of it (`perWorld_pairOf`, `pairOf_whole`). Each legible world alone is reached by an agent that ignores what it sees, as a script timed in advance solves each feasible goal, so `perWorld` meets the obligation in that class (`perWorld_blind`), and a claim that no such agent can reach these goals is false of each world. No agent that ignores what it sees reaches the goal of every legible world (`whole_not_blind`), while the agent that does what it sees does (`whole_any`). A second record, asking the agent to reach the goal of every world, is too wide for every class: two worlds look alike and need opposite actions, so no agent serves its whole pair (`every_not_oPair`), though each world alone is still reached by a script (`everyPerWorld_blind`).

## What is trusted

Besides [what the README lists](../README.md#what-is-trusted) and [what the intent record trusts](intent-record.md#what-is-trusted):

- That a project's pairs of a property are stated over the inputs the property speaks of, and that its implementation class is the one the record means: `PairOf` and the class parameter make each statement say exactly what is proved, but not that it was the pair or class worth proving.
- That a pair's precondition carries the guards the property places on its input: the first goal reads the precondition as stated, so a guard written inside the postcondition instead is not checked by it.
- That the domain hypotheses are facts of the world, as for every obligation: a pair says what the property says under them, so where a hypothesis mentions the subject, a subject of the class that fails it meets the postcondition of `Pair.whole` emptily.
