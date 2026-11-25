/-
Thesis Section 6.2. Policy-dependent fairness coefficients.

The service-rate distribution is a probability measure `F` on `ℝ`.
Assumption 6.1.1 is the structure `RateBounds`.
-/
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Function.EssSup

open MeasureTheory ProbabilityTheory

namespace ThesisLean.CostOfFairness

/-- The mean service rate `μ̄_F = E[μ̃]` of (6.1.1). -/
noncomputable def meanRate (F : Measure ℝ) : ℝ := ∫ x, x ∂F

/-- The service-rate variance `σ_F² = Var(μ̃)` of (6.1.1). -/
noncomputable def varRate (F : Measure ℝ) : ℝ := variance (fun x : ℝ => x) F

/-- **Assumption 6.1.1.** The service rate lies in `[μmin, μmax]` almost surely,
with `0 < μmin`. -/
structure RateBounds (F : Measure ℝ) (μmin μmax : ℝ) : Prop where
  pos : 0 < μmin
  lower : ∀ᵐ x ∂F, μmin ≤ x
  upper : ∀ᵐ x ∂F, x ≤ μmax

/-- The fairness coefficient under totally blind routing, `κ_TB = E[μ̃²] / E[μ̃]`,
see (6.2.2). -/
noncomputable def kappaTB (F : Measure ℝ) : ℝ := (∫ x, x ^ 2 ∂F) / ∫ x, x ∂F

/-- The limiting fairness measure under totally blind routing in (6.2.1).
It is the size-biased version of `F`, with density `μ / μ̄_F` with respect to `F`. -/
noncomputable def etaTB (F : Measure ℝ) : Measure ℝ :=
  F.withDensity fun x => ENNReal.ofReal (x / meanRate F)

variable {F : Measure ℝ} [IsProbabilityMeasure F] {μmin μmax : ℝ}

/-- The size-biased measure `η_TB` is a probability measure. -/
theorem isProbabilityMeasure_etaTB (h : RateBounds F μmin μmax) :
    IsProbabilityMeasure (etaTB F) := by
  sorry

/-- `κ_TB = ⟨ι, η_TB⟩`. The fairness coefficient under totally blind routing is the
first moment of the size-biased measure. -/
theorem first_moment_etaTB (h : RateBounds F μmin μmax) :
    ∫ x, x ∂(etaTB F) = kappaTB F := by
  sorry

/-- `κ_FSF = ⟨ι, δ_{μmin}⟩ = μmin`, see (6.2.1) and (6.2.2). -/
theorem first_moment_etaFSF (μmin : ℝ) : ∫ x, x ∂(Measure.dirac μmin) = μmin := by
  sorry

/-- **Equation (6.2.2).** `κ_TB = μ̄_F + σ_F² / μ̄_F`. -/
theorem kappaTB_eq (h : RateBounds F μmin μmax) :
    kappaTB F = meanRate F + varRate F / meanRate F := by
  sorry

/-- **Equation (6.2.3).** If `F` is nondegenerate, then
`κ_FSF = μmin < μ̄_F < κ_TB ≤ μmax`. -/
theorem coefficient_ordering (h : RateBounds F μmin μmax) (hnd : 0 < varRate F) :
    μmin < meanRate F ∧ meanRate F < kappaTB F ∧ kappaTB F ≤ μmax := by
  sorry

/-- **Equation (6.2.3), consequence used in Corollary 6.3.7.** If `F` is
nondegenerate, then `κ_FSF < κ_TB`. -/
theorem kappaFSF_lt_kappaTB (h : RateBounds F μmin μmax) (hnd : 0 < varRate F) :
    μmin < kappaTB F := by
  sorry

/-- **Equation (6.2.3) with the essential infimum and supremum of (6.1.1).**
The ordering holds with `μmin = ess inf μ̃` and `μmax = ess sup μ̃`. -/
theorem coefficient_ordering_essInf (h : RateBounds F μmin μmax) (hnd : 0 < varRate F) :
    essInf (fun x : ℝ => x) F < meanRate F ∧ meanRate F < kappaTB F ∧
      kappaTB F ≤ essSup (fun x : ℝ => x) F := by
  sorry

/-- **Equation (6.2.4).** `κ_TB - κ_FSF = (μ̄_F - μmin) + σ_F² / μ̄_F`. -/
theorem kappaTB_sub_kappaFSF (h : RateBounds F μmin μmax) :
    kappaTB F - μmin = (meanRate F - μmin) + varRate F / meanRate F := by
  sorry

/-- If `F` is degenerate, then `κ_TB = μ̄_F`. -/
theorem kappaTB_eq_meanRate_of_degenerate (h : RateBounds F μmin μmax)
    (hd : varRate F = 0) : kappaTB F = meanRate F := by
  sorry

end ThesisLean.CostOfFairness
