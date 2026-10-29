# The refinement link

**A refinement link** (`LeanIntent.Refines`, `LeanIntent.fulfils`): a proof that the code meets its specification, and a proof that the specification refines the intent record, compose into a proof that the code fulfils the intent.

Module: `LeanIntent/Refinement.lean`.

**Complete in this version:** the refinement link with its transfer theorems.

## Worked examples

- [`LeanIntentExamples/Transfer.lean`](../LeanIntentExamples/Transfer.lean): a refinement link carries the record's guarantees to the mapping's image, not to the implementations themselves.
- [`LeanIntentExamples/Sorting.lean`](../LeanIntentExamples/Sorting.lean), described with [the obligations](obligations.md#worked-examples): the corrected sorting record is fulfilled by `List.mergeSort` through the refinement link.

## What is trusted

The refinement link adds nothing to [what the README lists](../README.md#what-is-trusted).
