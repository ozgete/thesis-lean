/-
Thesis Section 6.3.1. The stationary density of the piecewise
Ornstein-Uhlenbeck diffusion.

The stationary density (6.3.7) is taken as a definition. The parameters are
`lam` for `λ̄`, the abandonment rate `γ`, the fairness coefficient `κ` for `κ_r`,
and the capacity slack `b`.
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory

namespace ThesisLean.CostOfFairness

/-- The function `K_r` of (6.3.8). It equals `γ x² / 2` for `x ≥ 0` and
`κ x² / 2` for `x < 0`. -/
noncomputable def potential (γ κ x : ℝ) : ℝ :=
  if 0 ≤ x then γ / 2 * x ^ 2 else κ / 2 * x ^ 2

/-- The unnormalised stationary density `exp(-(b x + K_r(x)) / λ̄)` of (6.3.7). -/
noncomputable def weight (lam γ κ b x : ℝ) : ℝ :=
  Real.exp (-(b * x + potential γ κ x) / lam)

/-- The normalising integral `Z_r(b) = ∫ exp(-(b x + K_r(x)) / λ̄) dx` of (6.3.36).
The constant `C_r(b)` of (6.3.7) is its reciprocal. -/
noncomputable def partitionFn (lam γ κ b : ℝ) : ℝ := ∫ x, weight lam γ κ b x

/-- **Equation (6.3.7).** The stationary density
`p_r(x; b) = C_r(b) exp(-(b x + K_r(x)) / λ̄)`. -/
noncomputable def density (lam γ κ b x : ℝ) : ℝ :=
  weight lam γ κ b x / partitionFn lam γ κ b

/-- The stationary expectation `E_b[h(ξ_r(∞))] = ∫ h(x) p_r(x; b) dx`. -/
noncomputable def stationaryExpect (lam γ κ b : ℝ) (h : ℝ → ℝ) : ℝ :=
  ∫ x, h x * density lam γ κ b x

/-- **Equation (6.3.23).** The stationary congestion measure
`M_r(b) = E[ξ_r⁺(∞; b)]`. -/
noncomputable def congestion (lam γ κ b : ℝ) : ℝ :=
  stationaryExpect lam γ κ b fun x => x⁺

/-- **Equation (6.3.24).** The stationary idleness measure
`I_r(b) = E[ξ_r⁻(∞; b)]`. -/
noncomputable def idleness (lam γ κ b : ℝ) : ℝ :=
  stationaryExpect lam γ κ b fun x => x⁻

variable {lam γ κ : ℝ}

/-- **Equation (6.3.9).** The two branches of the unnormalised density. -/
theorem weight_of_nonneg (lam γ κ b : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    weight lam γ κ b x = Real.exp (-(b * x) / lam - γ * x ^ 2 / (2 * lam)) := by
  sorry

/-- **Equation (6.3.9).** The two branches of the unnormalised density. -/
theorem weight_of_neg (lam γ κ b : ℝ) {x : ℝ} (hx : x < 0) :
    weight lam γ κ b x = Real.exp (-(b * x) / lam - κ * x ^ 2 / (2 * lam)) := by
  sorry

/-- **Proposition 6.3.1, integrability.** The unnormalised density has Gaussian
tails on both half-lines and is integrable. -/
theorem integrable_weight (hlam : 0 < lam) (hγ : 0 < γ) (hκ : 0 < κ) (b : ℝ) :
    Integrable (fun x => weight lam γ κ b x) := by
  sorry

/-- **Auxiliary result, polynomial moments.** The unnormalised density has finite
polynomial moments of every order. -/
theorem integrable_pow_mul_weight (hlam : 0 < lam) (hγ : 0 < γ) (hκ : 0 < κ) (b : ℝ)
    (n : ℕ) : Integrable (fun x => x ^ n * weight lam γ κ b x) := by
  sorry

/-- **Auxiliary result, absolute polynomial moments.** -/
theorem integrable_abs_pow_mul_weight (hlam : 0 < lam) (hγ : 0 < γ) (hκ : 0 < κ) (b : ℝ)
    (n : ℕ) : Integrable (fun x => |x| ^ n * weight lam γ κ b x) := by
  sorry

/-- The normalising integral is positive. -/
theorem partitionFn_pos (hlam : 0 < lam) (hγ : 0 < γ) (hκ : 0 < κ) (b : ℝ) :
    0 < partitionFn lam γ κ b := by
  sorry

/-- The stationary density is positive on the whole real line. -/
theorem density_pos (hlam : 0 < lam) (hγ : 0 < γ) (hκ : 0 < κ) (b x : ℝ) :
    0 < density lam γ κ b x := by
  sorry

/-- **Proposition 6.3.1, normalisation.** The stationary density integrates to one. -/
theorem integral_density (hlam : 0 < lam) (hγ : 0 < γ) (hκ : 0 < κ) (b : ℝ) :
    ∫ x, density lam γ κ b x = 1 := by
  sorry

/-- **Auxiliary result, polynomial moments.** The stationary distribution has
finite polynomial moments of every order. -/
theorem integrable_pow_mul_density (hlam : 0 < lam) (hγ : 0 < γ) (hκ : 0 < κ) (b : ℝ)
    (n : ℕ) : Integrable (fun x => x ^ n * density lam γ κ b x) := by
  sorry

/-- **Auxiliary result, functions of polynomial growth.** If `h` is measurable
and `|h x| ≤ C (1 + |x| ^ n)`, then `h` is integrable with respect to the
stationary distribution. This covers `x⁺`, `x⁻`, `x` and `x⁺ x`. -/
theorem integrable_mul_density_of_polyGrowth (hlam : 0 < lam) (hγ : 0 < γ) (hκ : 0 < κ)
    (b : ℝ) {h : ℝ → ℝ} (hmeas : Measurable h) {C : ℝ} {n : ℕ}
    (hbound : ∀ x, |h x| ≤ C * (1 + |x| ^ n)) :
    Integrable (fun x => h x * density lam γ κ b x) := by
  sorry

end ThesisLean.CostOfFairness
