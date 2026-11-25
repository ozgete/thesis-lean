/-
Thesis Section 2.4.4. Gronwall's inequality in integral form.
-/
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory Set

namespace ThesisLean

/-- **Lemma 2.4.3 (Gronwall's inequality).**
Let `g : [0, T] → ℝ₊` be bounded and measurable and suppose that
`g t ≤ ε + M ∫₀ᵗ g s ds` for all `t ∈ [0, T]`. Then `g t ≤ ε e^{M t}` on `[0, T]`. -/
theorem gronwall_integral {g : ℝ → ℝ} {T ε M C : ℝ} (hε : 0 ≤ ε) (hM : 0 ≤ M)
    (hg_meas : Measurable g)
    (hg_nonneg : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ g t)
    (hg_bdd : ∀ t ∈ Icc (0 : ℝ) T, g t ≤ C)
    (hg : ∀ t ∈ Icc (0 : ℝ) T, g t ≤ ε + M * ∫ s in (0 : ℝ)..t, g s) :
    ∀ t ∈ Icc (0 : ℝ) T, g t ≤ ε * Real.exp (M * t) := by
  sorry

/-- **Lemma 2.4.3, case `ε = 0`.** Under the same hypotheses with `ε = 0`,
the function `g` vanishes on `[0, T]`. -/
theorem gronwall_integral_eq_zero {g : ℝ → ℝ} {T M C : ℝ} (hM : 0 ≤ M)
    (hg_meas : Measurable g)
    (hg_nonneg : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ g t)
    (hg_bdd : ∀ t ∈ Icc (0 : ℝ) T, g t ≤ C)
    (hg : ∀ t ∈ Icc (0 : ℝ) T, g t ≤ M * ∫ s in (0 : ℝ)..t, g s) :
    ∀ t ∈ Icc (0 : ℝ) T, g t = 0 := by
  sorry

end ThesisLean
