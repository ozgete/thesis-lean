/-
Smoke test for the build pipeline. This file is replaced by the
Chapter 5 and Chapter 6 developments once the action is green.
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Probability.Distributions.Gaussian.Real

namespace ThesisLean

/-- The positive part `x⁺ = max x 0` is nondecreasing. -/
theorem posPart_mono {x y : ℝ} (h : x ≤ y) : max x 0 ≤ max y 0 :=
  max_le_max h le_rfl

end ThesisLean
