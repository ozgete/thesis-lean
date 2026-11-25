/-
Axiom audit. For every completed result, `#print axioms` lists the axioms that
its proof depends on. A complete proof depends only on the three standard
axioms of Lean and Mathlib, namely `propext`, `Classical.choice` and
`Quot.sound`. An incomplete proof would additionally list `sorryAx`.
The output appears in the build log.
-/
import ThesisLean.Preliminaries.Gronwall
import ThesisLean.Chapter5.Comparison
import ThesisLean.Chapter6.Coefficients

open ThesisLean ThesisLean.PoolPriority ThesisLean.CostOfFairness

-- Lemma 2.4.3
#print axioms gronwall_integral
#print axioms gronwall_integral_eq_zero

-- Theorem 5.3.4(i)
#print axioms mixture_coeff_ge_min
#print axioms integral_id_mixture
#print axioms mixture_first_moment_ge_min

-- Corollary 5.3.6, lower bound
#print axioms first_moment_ge_of_ae_ge
#print axioms first_moment_le_of_ae_le
#print axioms mixture_first_moment_ge_of_ae_ge
#print axioms first_moment_dirac

-- Lemma 5.3.9 and the ordering step of Theorem 5.3.10
#print axioms priority_diffusion_comparison
#print axioms priority_diffusion_comparison_posPart
#print axioms expectation_mono_of_pathwise_le

-- Section 6.2
#print axioms rateBounds_essential
#print axioms kappaFSF_pos
#print axioms isProbabilityMeasure_etaTB
#print axioms first_moment_etaTB
#print axioms first_moment_etaFSF
#print axioms kappaTB_eq
#print axioms coefficient_ordering
#print axioms kappaFSF_lt_kappaTB
#print axioms kappaTB_sub_kappaFSF
#print axioms kappaFSF_eq_kappaTB_of_degenerate
