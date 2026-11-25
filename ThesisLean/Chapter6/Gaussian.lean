/-
Thesis Sections 6.3.2 and 6.3.3. Two-sided truncated Gaussian representation
and the closed forms of the stationary congestion and idleness measures.
-/
import ThesisLean.Chapter6.Density

open MeasureTheory Set Real

namespace ThesisLean.CostOfFairness

/-- The standard normal density `φ`. -/
noncomputable def stdNormalPDF (x : ℝ) : ℝ := Real.exp (-x ^ 2 / 2) / √(2 * π)

/-- The standard normal distribution function `Φ`. -/
noncomputable def stdNormalCDF (x : ℝ) : ℝ := ∫ t in Iic x, stdNormalPDF t

/-- The density `ϕ(x; ν, s)` of a normal random variable with mean `ν` and
standard deviation `s`. -/
noncomputable def normalPDF (ν s x : ℝ) : ℝ := stdNormalPDF ((x - ν) / s) / s

/-- `ν₊ = -b / γ`, see (6.3.12). -/
noncomputable def nuPlus (γ b : ℝ) : ℝ := -b / γ

/-- `s₊ = √(λ̄ / γ)`, see (6.3.12). -/
noncomputable def sPlus (lam γ : ℝ) : ℝ := √(lam / γ)

/-- `ν_{r,-} = -b / κ_r`, see (6.3.12). -/
noncomputable def nuMinus (κ b : ℝ) : ℝ := -b / κ

/-- `s_{r,-} = √(λ̄ / κ_r)`, see (6.3.12). -/
noncomputable def sMinus (lam κ : ℝ) : ℝ := √(lam / κ)

/-- `z₊ = ν₊ / s₊ = -b / √(γ λ̄)`, see (6.3.13). -/
noncomputable def zPlus (lam γ b : ℝ) : ℝ := -b / √(γ * lam)

/-- `z_{r,-} = ν_{r,-} / s_{r,-} = -b / √(κ_r λ̄)`, see (6.3.13). -/
noncomputable def zMinus (lam κ b : ℝ) : ℝ := -b / √(κ * lam)

/-- **Equation (6.3.14).**
`ρ_r(b) = (s_{r,-} / s₊) exp((b² / (2 λ̄)) (1 / κ_r - 1 / γ))`. -/
noncomputable def rho (lam γ κ b : ℝ) : ℝ :=
  sMinus lam κ / sPlus lam γ * Real.exp (b ^ 2 / (2 * lam) * (1 / κ - 1 / γ))

/-- **Equation (6.3.15).** `D_r(b) = Φ(z₊) + ρ_r(b) Φ(-z_{r,-})`. -/
noncomputable def normD (lam γ κ b : ℝ) : ℝ :=
  stdNormalCDF (zPlus lam γ b) + rho lam γ κ b * stdNormalCDF (-zMinus lam κ b)

variable {lam γ κ : ℝ}

/-- `z₊ = ν₊ / s₊`, the first identity in (6.3.13). -/
theorem zPlus_eq (hlam : 0 < lam) (hγ : 0 < γ) (b : ℝ) :
    zPlus lam γ b = nuPlus γ b / sPlus lam γ := by
  sorry

/-- `z_{r,-} = ν_{r,-} / s_{r,-}`, the second identity in (6.3.13). -/
theorem zMinus_eq (hlam : 0 < lam) (hκ : 0 < κ) (b : ℝ) :
    zMinus lam κ b = nuMinus κ b / sMinus lam κ := by
  sorry

/-- The normalising quantity `D_r(b)` is positive. -/
theorem normD_pos (hlam : 0 < lam) (hγ : 0 < γ) (hκ : 0 < κ) (b : ℝ) :
    0 < normD lam γ κ b := by
  sorry

/-- **Proposition 6.3.2, positive branch of (6.3.16).** For `x ≥ 0`,
`p_r(x; b) = A_{r,+}(b) ϕ(x; ν₊, s₊)` with `A_{r,+}(b) = 1 / D_r(b)`. -/
theorem density_of_nonneg (hlam : 0 < lam) (hγ : 0 < γ) (hκ : 0 < κ) (b : ℝ) {x : ℝ}
    (hx : 0 ≤ x) :
    density lam γ κ b x
      = 1 / normD lam γ κ b * normalPDF (nuPlus γ b) (sPlus lam γ) x := by
  sorry

/-- **Proposition 6.3.2, negative branch of (6.3.16).** For `x < 0`,
`p_r(x; b) = A_{r,-}(b) ϕ(x; ν_{r,-}, s_{r,-})` with
`A_{r,-}(b) = ρ_r(b) / D_r(b)`. -/
theorem density_of_neg (hlam : 0 < lam) (hγ : 0 < γ) (hκ : 0 < κ) (b : ℝ) {x : ℝ}
    (hx : x < 0) :
    density lam γ κ b x
      = rho lam γ κ b / normD lam γ κ b * normalPDF (nuMinus κ b) (sMinus lam κ) x := by
  sorry

/-- **Proposition 6.3.2, first identity in (6.3.18).**
`P(ξ_r(∞) ≥ 0) = Φ(z₊) / D_r(b)`. -/
theorem prob_queueing (hlam : 0 < lam) (hγ : 0 < γ) (hκ : 0 < κ) (b : ℝ) :
    ∫ x in Ici (0 : ℝ), density lam γ κ b x
      = stdNormalCDF (zPlus lam γ b) / normD lam γ κ b := by
  sorry

/-- **Proposition 6.3.2, second identity in (6.3.18).**
`P(ξ_r(∞) < 0) = ρ_r(b) Φ(-z_{r,-}) / D_r(b)`. -/
theorem prob_idleness (hlam : 0 < lam) (hγ : 0 < γ) (hκ : 0 < κ) (b : ℝ) :
    ∫ x in Iio (0 : ℝ), density lam γ κ b x
      = rho lam γ κ b * stdNormalCDF (-zMinus lam κ b) / normD lam γ κ b := by
  sorry

/-- **Proposition 6.3.4, equation (6.3.25).**
`M_r(b) = s₊ [φ(z₊) + z₊ Φ(z₊)] / D_r(b)`. -/
theorem congestion_eq (hlam : 0 < lam) (hγ : 0 < γ) (hκ : 0 < κ) (b : ℝ) :
    congestion lam γ κ b
      = sPlus lam γ * (stdNormalPDF (zPlus lam γ b)
          + zPlus lam γ b * stdNormalCDF (zPlus lam γ b)) / normD lam γ κ b := by
  sorry

/-- **Proposition 6.3.4, equation (6.3.26).**
`I_r(b) = ρ_r(b) s_{r,-} [φ(z_{r,-}) - z_{r,-} Φ(-z_{r,-})] / D_r(b)`. -/
theorem idleness_eq (hlam : 0 < lam) (hγ : 0 < γ) (hκ : 0 < κ) (b : ℝ) :
    idleness lam γ κ b
      = rho lam γ κ b * sMinus lam κ * (stdNormalPDF (zMinus lam κ b)
          - zMinus lam κ b * stdNormalCDF (-zMinus lam κ b)) / normD lam γ κ b := by
  sorry

end ThesisLean.CostOfFairness
