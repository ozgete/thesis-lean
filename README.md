# thesis-lean

Lean 4 / Mathlib formalisation of selected results from the PhD thesis
*Heterogeneous Many-Server Queueing Systems: A Measure-Valued Approach*
(Özge Tekin, University of Edinburgh, 2026).

## Status

**Stage 2 of 4: statements.** All definitions and theorem statements below
compile against Mathlib. Every proof is still `sorry`. The next stage fills in
the proofs.

## Scope

The process-level limit theorems are out of scope. The stationary density
(6.3.7) is taken as a definition, so the Chapter 6 results are statements about
that density.

## Map from the thesis to Lean

### Preliminaries (`ThesisLean/Preliminaries/Gronwall.lean`)

| Thesis | Lean name |
| --- | --- |
| Lemma 2.4.3 | `gronwall_integral`, `gronwall_integral_eq_zero` |

### Chapter 5 (`ThesisLean/Chapter5/Comparison.lean`)

| Thesis | Lean name |
| --- | --- |
| Theorem 5.3.4(i) | `mixture_coeff_ge_min`, `integral_id_mixture`, `mixture_first_moment_ge_min` |
| Corollary 5.3.6, lower bound | `first_moment_ge_of_ae_ge`, `first_moment_le_of_ae_le`, `mixture_first_moment_ge_of_ae_ge`, `first_moment_dirac` |
| Lemma 5.3.9 | `priority_diffusion_comparison`, `priority_diffusion_comparison_posPart` |
| Theorem 5.3.10, ordering step | `expectation_mono_of_pathwise_le` |

### Chapter 6

| Thesis | Lean name | File |
| --- | --- | --- |
| Assumption 6.1.1 | `RateBounds` | `Chapter6/Coefficients.lean` |
| (6.2.1) | `etaTB`, `isProbabilityMeasure_etaTB`, `first_moment_etaTB`, `first_moment_etaFSF` | `Chapter6/Coefficients.lean` |
| (6.2.2) | `kappaTB`, `kappaTB_eq` | `Chapter6/Coefficients.lean` |
| (6.2.3) | `coefficient_ordering`, `coefficient_ordering_essInf`, `kappaFSF_lt_kappaTB` | `Chapter6/Coefficients.lean` |
| (6.2.4) | `kappaTB_sub_kappaFSF` | `Chapter6/Coefficients.lean` |
| (6.3.7) to (6.3.9) | `potential`, `weight`, `partitionFn`, `density`, `weight_of_nonneg`, `weight_of_neg` | `Chapter6/Density.lean` |
| Proposition 6.3.1 | `integrable_weight`, `partitionFn_pos`, `density_pos`, `integral_density` | `Chapter6/Density.lean` |
| (6.3.12) to (6.3.15) | `nuPlus`, `sPlus`, `nuMinus`, `sMinus`, `zPlus`, `zMinus`, `rho`, `normD` | `Chapter6/Gaussian.lean` |
| Proposition 6.3.2 | `density_of_nonneg`, `density_of_neg`, `prob_queueing`, `prob_idleness` | `Chapter6/Gaussian.lean` |
| (6.3.23), (6.3.24) | `congestion`, `idleness` | `Chapter6/Density.lean` |
| Proposition 6.3.4 | `congestion_eq`, `idleness_eq` | `Chapter6/Gaussian.lean` |
| Theorem 6.3.5 | `congestion_pos`, `hasDerivAt_congestion`, `stationaryCov_pos`, `contDiff_congestion`, `strictAnti_congestion`, `tendsto_congestion_atTop`, `tendsto_congestion_atBot`, `congestion_isEquivalent_atBot` | `Chapter6/Monotonicity.lean` |
| Theorem 6.3.6 | `congestion_lt_of_kappa_lt` | `Chapter6/Monotonicity.lean` |
| Corollary 6.3.7 | `congestion_FSF_lt_TB` | `Chapter6/Monotonicity.lean` |
| (6.4.2), (6.4.3) | `targetSlack`, `existsUnique_slack`, `congestion_targetSlack`, `congestion_le_iff` | `Chapter6/Staffing.lean` |
| Proposition 6.4.1 | `targetSlack_lt_of_kappa_lt`, `targetSlack_FSF_lt_TB` | `Chapter6/Staffing.lean` |

## Notation

| Thesis | Lean |
| --- | --- |
| `λ̄` | `lam` |
| `κ_r` | `κ` |
| `K_r` | `potential` |
| `Z_r(b)`, with `C_r(b) = 1 / Z_r(b)` | `partitionFn` |
| `p_r(x; b)` | `density` |
| `M_r(b)`, `I_r(b)` | `congestion`, `idleness` |
| `φ`, `Φ`, `ϕ(x; ν, s)` | `stdNormalPDF`, `stdNormalCDF`, `normalPDF` |
| `D_r(b)`, `ρ_r(b)` | `normD`, `rho` |
| `b*_r(q)` | `targetSlack` |
| `μ̄_F`, `σ_F²` | `meanRate`, `varRate` |
| `x⁺`, `x⁻` | `x⁺`, `x⁻` |

## Building

```
lake exe cache get
lake build
```

Pinned to Mathlib `v4.36.0` (Lean `v4.36.0`). The GitHub Action builds on every
push and lists any remaining `sorry`.
