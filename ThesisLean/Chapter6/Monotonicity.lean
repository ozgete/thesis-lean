/-
Thesis Section 6.3.4. Monotonicity of the stationary congestion measure in the
capacity slack and in the fairness coefficient.
-/
import ThesisLean.Chapter6.Gaussian
import ThesisLean.Chapter6.Coefficients
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Calculus.ContDiff.Basic

open MeasureTheory Set Filter Topology Asymptotics

namespace ThesisLean.CostOfFairness

variable {lam γ κ : ℝ}

/-! ### Theorem 6.3.5 -/

/-- **Theorem 6.3.5, range.** The stationary congestion measure is positive. -/
theorem congestion_pos (hlam : 0 < lam) (hγ : 0 < γ) (hκ : 0 < κ) (b : ℝ) :
    0 < congestion lam γ κ b := by
  sorry

/-- The stationary covariance `Cov_b(ξ_r⁺(∞), ξ_r(∞))` in (6.3.31). -/
noncomputable def stationaryCov (lam γ κ b : ℝ) : ℝ :=
  stationaryExpect lam γ κ b (fun x => x⁺ * x)
    - stationaryExpect lam γ κ b (fun x => x⁺) * stationaryExpect lam γ κ b (fun x => x)

/-- **Theorem 6.3.5, equation (6.3.31).**
`M_r'(b) = -(1 / λ̄) Cov_b(ξ_r⁺(∞), ξ_r(∞))`. -/
theorem hasDerivAt_congestion (hlam : 0 < lam) (hγ : 0 < γ) (hκ : 0 < κ) (b : ℝ) :
    HasDerivAt (fun b => congestion lam γ κ b) (-(1 / lam) * stationaryCov lam γ κ b) b := by
  sorry

/-- **Theorem 6.3.5, sign in (6.3.31).** The stationary covariance is positive. -/
theorem stationaryCov_pos (hlam : 0 < lam) (hγ : 0 < γ) (hκ : 0 < κ) (b : ℝ) :
    0 < stationaryCov lam γ κ b := by
  sorry

/-- **Theorem 6.3.5.** `M_r` is continuously differentiable. -/
theorem contDiff_congestion (hlam : 0 < lam) (hγ : 0 < γ) (hκ : 0 < κ) :
    ContDiff ℝ 1 (fun b => congestion lam γ κ b) := by
  sorry

/-- **Theorem 6.3.5.** `M_r` is strictly decreasing. -/
theorem strictAnti_congestion (hlam : 0 < lam) (hγ : 0 < γ) (hκ : 0 < κ) :
    StrictAnti (fun b => congestion lam γ κ b) := by
  sorry

/-- **Theorem 6.3.5, first limit in (6.3.32).** `M_r(b) → 0` as `b → ∞`. -/
theorem tendsto_congestion_atTop (hlam : 0 < lam) (hγ : 0 < γ) (hκ : 0 < κ) :
    Tendsto (fun b => congestion lam γ κ b) atTop (𝓝 0) := by
  sorry

/-- **Theorem 6.3.5, second limit in (6.3.32).** `M_r(b) → ∞` as `b → -∞`. -/
theorem tendsto_congestion_atBot (hlam : 0 < lam) (hγ : 0 < γ) (hκ : 0 < κ) :
    Tendsto (fun b => congestion lam γ κ b) atBot atTop := by
  sorry

/-- **Theorem 6.3.5, equation (6.3.33).** `M_r(b) ∼ -b / γ` as `b → -∞`. -/
theorem congestion_isEquivalent_atBot (hlam : 0 < lam) (hγ : 0 < γ) (hκ : 0 < κ) :
    (fun b => congestion lam γ κ b) ~[atBot] (fun b => -b / γ) := by
  sorry

/-! ### Theorem 6.3.6 and Corollary 6.3.7 -/

/-- **Theorem 6.3.6.** For fixed `b` and `γ > 0`, the stationary congestion
measure is strictly increasing in the fairness coefficient. -/
theorem congestion_lt_of_kappa_lt (hlam : 0 < lam) (hγ : 0 < γ) (b : ℝ) {κ₁ κ₂ : ℝ}
    (hκ₁ : 0 < κ₁) (h : κ₁ < κ₂) :
    congestion lam γ κ₁ b < congestion lam γ κ₂ b := by
  sorry

/-- **Corollary 6.3.7, equation (6.3.41).** If the service-rate distribution `F`
is nondegenerate, then `M_FSF(b) < M_TB(b)` for every `b`. Here
`κ_FSF = μmin = ess inf μ̃` and `κ_TB = E[μ̃²] / E[μ̃]`. -/
theorem congestion_FSF_lt_TB (hlam : 0 < lam) (hγ : 0 < γ) {F : Measure ℝ}
    [IsProbabilityMeasure F] {lo hi : ℝ} (hF : RateBounds F lo hi)
    (hnd : 0 < varRate F) (b : ℝ) :
    congestion lam γ (kappaFSF F) b < congestion lam γ (kappaTB F) b := by
  sorry

/-- **Corollary 6.3.7, degenerate case.** If `F` is degenerate, the two
stationary congestion measures are equal. -/
theorem congestion_FSF_eq_TB_of_degenerate {F : Measure ℝ} [IsProbabilityMeasure F]
    {lo hi : ℝ} (hF : RateBounds F lo hi) (hd : varRate F = 0) (lam γ b : ℝ) :
    congestion lam γ (kappaFSF F) b = congestion lam γ (kappaTB F) b := by
  sorry

end ThesisLean.CostOfFairness
