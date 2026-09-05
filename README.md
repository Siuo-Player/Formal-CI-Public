# Formal-CI-Public

Minimal public execution infrastructure for the machine-checked formalisation of **AI-assisted constrained narrative exploration**.

## This repository is not the research ledger

Its authority is limited to:

```text
Lean source
→ declared formal statements
→ machine-check / CI execution
```

It is **not** authoritative for:

```text
scientific milestone count
research priority
publication claims
semantic fidelity
empirical usefulness
```

Those are controlled by `Siuo-Player-PROJECT-STUDIES` and, for curated publication claims, `Siuo-Player/Paper`.

## Continuation rule

Before adding a formal result, inspect the corresponding current-state and roadmap documents in the research repository. A PR here must identify:

```text
research obligation
classification
reused theorem/definition
new formal consequence
assumptions
negative tests
CI evidence
next gate
```

## Classification

Every PR is one of:

```text
MILESTONE
ADAPTER
INFRASTRUCTURE
NEGATIVE-RESULT
REWORK
REDUNDANT
```

Only `MILESTONE` changes the scientific frontier, and only after it is recorded in the research ledger.

## Current formal frontier

```text
ReachWithin
→ simple-witness reduction
→ n−1 finite boundary
→ concrete SearchState
→ actual expansion
→ coverage/exhaustion
→ FOUND soundness
→ PROVED_EMPTY soundness
→ UNKNOWN correctness
```

The central open obligation is to prove that the **actual search implementation** covers the semantically defined `ReachWithin` space up to the canonical finite boundary.

## Anti-inflation rule

Do not create standalone milestone PRs for:

```text
simple field projections
repeated arithmetic corollaries
trivial `Fin 0` / `Fin 1` cases
wrappers over an existing theorem
```

Group genuinely necessary helper lemmas into the owning proof/implementation tranche.

## Completeness rule

A result API or a boolean named `complete` is not a completeness proof.

The required logical chain is:

```text
ReachWithin
→ bounded simple witness
→ actual expansion relation
→ finite coverage
→ exhaustion
→ PROVED_EMPTY soundness
```

## CI interpretation

A green CI run means the checked Lean declarations are accepted by the configured toolchain. It does not establish that the formal model is faithful to unrestricted narrative semantics.

## Public-repository constraint

Keep this repository minimal. Do not import manuscript history, private research notes, experimental datasets, or unrelated analysis. Documentation here should explain executable scope and continuation constraints, not become a second research archive.
