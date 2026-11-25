/-
Thesis Section 6.4.1. The capacity slack required for a congestion target.
-/
import ThesisLean.Chapter6.Monotonicity

open MeasureTheory Set

namespace ThesisLean.CostOfFairness

variable {lam γ κ : ℝ}

/-- **Equation (6.4.3).** The minimum capacity slack required to attain the
congestion target `q`, `b*_r(q) = inf {b : M_r(b) ≤ q}`. -/
noncomputable def targetSlack (lam γ κ q : ℝ) : ℝ :=
  sInf {b : ℝ | congestion lam γ κ b ≤ q}

/-- **Section 6.4.1, existence and uniqueness.** For every `q > 0` there is a
unique capacity slack `b` with `M_r(b) = q`. -/
theorem existsUnique_slack (hlam : 0 < lam) (hγ : 0 < γ) (hκ : 0 < κ) {q : ℝ}
    (hq : 0 < q) : ∃! b : ℝ, congestion lam γ κ b = q := by
  sorry

/-- **Equation (6.4.2).** `M_r(b*_r(q)) = q`. -/
theorem congestion_targetSlack (hlam : 0 < lam) (hγ : 0 < γ) (hκ : 0 < κ) {q : ℝ}
    (hq : 0 < q) : congestion lam γ κ (targetSlack lam γ κ q) = q := by
  sorry

/-- The target `M_r(b) ≤ q` holds exactly when `b ≥ b*_r(q)`. -/
theorem congestion_le_iff (hlam : 0 < lam) (hγ : 0 < γ) (hκ : 0 < κ) {q : ℝ}
    (hq : 0 < q) (b : ℝ) :
    congestion lam γ κ b ≤ q ↔ targetSlack lam γ κ q ≤ b := by
  sorry

/-- The required capacity slack is strictly increasing in the fairness
coefficient. -/
theorem targetSlack_lt_of_kappa_lt (hlam : 0 < lam) (hγ : 0 < γ) {κ₁ κ₂ q : ℝ}
    (hκ₁ : 0 < κ₁) (h : κ₁ < κ₂) (hq : 0 < q) :
    targetSlack lam γ κ₁ q < targetSlack lam γ κ₂ q := by
  sorry

/-- **Proposition 6.4.1, equation (6.4.4).** If the service-rate distribution `F`
is nondegenerate, then `b*_FSF(q) < b*_TB(q)` for every `q > 0`. Totally blind
routing requires strictly greater capacity slack than fastest-server-first
routing to attain the same congestion target. -/
theorem targetSlack_FSF_lt_TB (hlam : 0 < lam) (hγ : 0 < γ) {F : Measure ℝ}
    [IsProbabilityMeasure F] {μmin μmax : ℝ} (hF : RateBounds F μmin μmax)
    (hnd : 0 < varRate F) {q : ℝ} (hq : 0 < q) :
    targetSlack lam γ μmin q < targetSlack lam γ (kappaTB F) q := by
  sorry

end ThesisLean.CostOfFairness
