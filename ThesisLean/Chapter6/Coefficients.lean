/-
Thesis Section 6.2. Policy-dependent fairness coefficients.

The service-rate distribution is a probability measure `F` on `ℝ`.
Following (6.1.1), `μmin` and `μmax` are the essential infimum and the essential
supremum of the service rate. They are `muMin F` and `muMax F` below.
Assumption 6.1.1 is the structure `RateBounds`. It records the existence of
constants `0 < lo ≤ hi < ∞` that bound the service rate almost surely. These
constants are used only to guarantee that `muMin F` is positive and `muMax F` is
finite. The policy-specific results are stated with `kappaFSF F = muMin F`.
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

/-- `μmin = ess inf μ̃` of (6.1.1). -/
noncomputable def muMin (F : Measure ℝ) : ℝ := essInf (fun x : ℝ => x) F

/-- `μmax = ess sup μ̃` of (6.1.1). -/
noncomputable def muMax (F : Measure ℝ) : ℝ := essSup (fun x : ℝ => x) F

/-- **Assumption 6.1.1.** There exist constants `0 < lo ≤ hi < ∞` such that the
service rate lies in `[lo, hi]` almost surely. -/
structure RateBounds (F : Measure ℝ) (lo hi : ℝ) : Prop where
  pos : 0 < lo
  lower : ∀ᵐ x ∂F, lo ≤ x
  upper : ∀ᵐ x ∂F, x ≤ hi

/-- The fairness coefficient under fastest-server-first routing,
`κ_FSF = μmin = ess inf μ̃`, see (6.2.2). -/
noncomputable def kappaFSF (F : Measure ℝ) : ℝ := muMin F

/-- The fairness coefficient under totally blind routing, `κ_TB = E[μ̃²] / E[μ̃]`,
see (6.2.2). -/
noncomputable def kappaTB (F : Measure ℝ) : ℝ := (∫ x, x ^ 2 ∂F) / ∫ x, x ∂F

/-- The limiting fairness measure under fastest-server-first routing in (6.2.1),
`η_FSF = δ_{μmin}`. -/
noncomputable def etaFSF (F : Measure ℝ) : Measure ℝ := Measure.dirac (muMin F)

/-- The limiting fairness measure under totally blind routing in (6.2.1).
It is the size-biased version of `F`, with density `μ / μ̄_F` with respect to `F`. -/
noncomputable def etaTB (F : Measure ℝ) : Measure ℝ :=
  F.withDensity fun x => ENNReal.ofReal (x / meanRate F)

variable {F : Measure ℝ} [IsProbabilityMeasure F] {lo hi : ℝ}

/-! ### The essential infimum and supremum -/

/-- Under Assumption 6.1.1, every almost-sure lower bound is at most `μmin`. -/
theorem le_muMin (h : RateBounds F lo hi) : lo ≤ muMin F := by
  sorry

/-- Under Assumption 6.1.1, `μmax` is at most every almost-sure upper bound. -/
theorem muMax_le (h : RateBounds F lo hi) : muMax F ≤ hi := by
  sorry

/-- Under Assumption 6.1.1, the service rate is at least `μmin` almost surely. -/
theorem ae_muMin_le (h : RateBounds F lo hi) : ∀ᵐ x ∂F, muMin F ≤ x := by
  sorry

/-- Under Assumption 6.1.1, the service rate is at most `μmax` almost surely. -/
theorem ae_le_muMax (h : RateBounds F lo hi) : ∀ᵐ x ∂F, x ≤ muMax F := by
  sorry

/-- Under Assumption 6.1.1, the bounds hold with the essential infimum and
supremum themselves. -/
theorem rateBounds_essential (h : RateBounds F lo hi) :
    RateBounds F (muMin F) (muMax F) := by
  sorry

/-- Under Assumption 6.1.1, `κ_FSF = μmin > 0`. -/
theorem kappaFSF_pos (h : RateBounds F lo hi) : 0 < kappaFSF F := by
  sorry

/-! ### Fairness measures and their first moments -/

/-- The size-biased measure `η_TB` is a probability measure. -/
theorem isProbabilityMeasure_etaTB (h : RateBounds F lo hi) :
    IsProbabilityMeasure (etaTB F) := by
  sorry

/-- `κ_TB = ⟨ι, η_TB⟩`. The fairness coefficient under totally blind routing is the
first moment of the size-biased measure. -/
theorem first_moment_etaTB (h : RateBounds F lo hi) :
    ∫ x, x ∂(etaTB F) = kappaTB F := by
  sorry

/-- `κ_FSF = ⟨ι, η_FSF⟩`. The fairness coefficient under fastest-server-first
routing is the first moment of the point mass at `μmin`. -/
theorem first_moment_etaFSF (F : Measure ℝ) : ∫ x, x ∂(etaFSF F) = kappaFSF F := by
  sorry

/-! ### Equations (6.2.2) to (6.2.4) -/

/-- **Equation (6.2.2).** `κ_TB = μ̄_F + σ_F² / μ̄_F`. -/
theorem kappaTB_eq (h : RateBounds F lo hi) :
    kappaTB F = meanRate F + varRate F / meanRate F := by
  sorry

/-- Auxiliary form of (6.2.3) for arbitrary almost-sure bounds. If `F` is
nondegenerate, then `lo < μ̄_F < κ_TB ≤ hi`. -/
theorem coefficient_ordering_of_bounds (h : RateBounds F lo hi) (hnd : 0 < varRate F) :
    lo < meanRate F ∧ meanRate F < kappaTB F ∧ kappaTB F ≤ hi := by
  sorry

/-- **Equation (6.2.3).** If `F` is nondegenerate, then
`κ_FSF = μmin < μ̄_F < κ_TB ≤ μmax`. -/
theorem coefficient_ordering (h : RateBounds F lo hi) (hnd : 0 < varRate F) :
    kappaFSF F < meanRate F ∧ meanRate F < kappaTB F ∧ kappaTB F ≤ muMax F := by
  sorry

/-- **Equation (6.2.3), consequence used in Corollary 6.3.7.** If `F` is
nondegenerate, then `κ_FSF < κ_TB`. -/
theorem kappaFSF_lt_kappaTB (h : RateBounds F lo hi) (hnd : 0 < varRate F) :
    kappaFSF F < kappaTB F := by
  sorry

/-- **Equation (6.2.4).** `κ_TB - κ_FSF = (μ̄_F - μmin) + σ_F² / μ̄_F`. -/
theorem kappaTB_sub_kappaFSF (h : RateBounds F lo hi) :
    kappaTB F - kappaFSF F = (meanRate F - muMin F) + varRate F / meanRate F := by
  sorry

/-- If `F` is degenerate, the two fairness coefficients coincide. -/
theorem kappaFSF_eq_kappaTB_of_degenerate (h : RateBounds F lo hi)
    (hd : varRate F = 0) : kappaFSF F = kappaTB F := by
  sorry

end ThesisLean.CostOfFairness
