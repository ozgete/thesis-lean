# thesis-lean

Lean 4 / Mathlib formalisation of selected results from the PhD thesis
*Heterogeneous Many-Server Queueing Systems: A Measure-Valued Approach*
(Özge Tekin, University of Edinburgh, 2026).

## Scope

- **Chapter 5, comparison layer.** Theorem 5.3.4(i), the lower bound in
  Corollary 5.3.6, Lemma 5.3.9.
- **Chapter 6, stationary chain.** Identities (6.2.2) to (6.2.4),
  Propositions 6.3.2 and 6.3.4, Theorems 6.3.5 and 6.3.6, Corollary 6.3.7,
  Proposition 6.4.1.

The process-level limit theorems are out of scope. The stationary density
(6.3.7) is taken as a definition.

## Status

Scaffold only. The map from Lean theorems to thesis numbers is added as the
development progresses.

## Building

```
lake exe cache get
lake build
```

Pinned to Mathlib `v4.36.0` (Lean `v4.36.0`).
