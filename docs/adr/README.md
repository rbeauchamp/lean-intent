# Architecture Decision Records

This directory holds Architecture Decision Records (ADRs) for `lean-intent`: non-obvious architectural, semantic, security, performance, and Trusted Computing Base (TCB) decisions that are not visible from reading Lean code alone.

Code comments in `.lean` files are banned under a downward-only per-file ratchet enforced by `tools/check.lean` (`NO-COMMENTS`; see [ADR-0004](0004-ratcheted-ban-on-lean-comments.md)). When removing comments from `.lean` files, non-obvious decisions that belong with the repository live here instead of in source comments.

## Index

| ADR | Title |
|---|---|
| [0001](0001-repository-checks-and-trusted-base.md) | Repository checks (`tools/check.lean`, `tools/codes.lean`) and trusted base |
| [0002](0002-test-listing-and-pinned-lean-tokens.md) | Test listing (`--tests`), subprocess isolation, and pinned Lean v4.36.0 token audit |
| [0003](0003-runtime-process-audit-and-exemptions.md) | Runtime process-call audit (`PROCESS`), `Lean.manualRoot` exemption, and Lake boundary |
| [0004](0004-ratcheted-ban-on-lean-comments.md) | Ratcheted ban on Lean comments (`NO-COMMENTS`) |
| [0005](0005-intent-records-refinement-and-answers-invariants.md) | Intent records, refinement transfer limits, answers independence, and cone examples |
| [0006](0006-declared-type-coding-and-code-audit-internals.md) | Declared-type coding, two-phase module split, handler internals, and code audit |
| [0007](0007-term-printing-rendering-and-meaning-closure.md) | Term printing, canonicalization, meaning closure, and rendering internals |
| [0008](0008-compiled-code-reachability-and-module-name-decoding.md) | Compiled-code `_redArg` allowlist and closed-form module-name decoding |
| [0009](0009-environment-extension-loading-and-reader-guards.md) | Environment-extension loading (`LOADED`), reader guards (`READERS`), and `Loaded`/`Stored` |
