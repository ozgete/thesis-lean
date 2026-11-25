/-
Thesis Chapter 5, comparison layer.

* `mixture_coeff_ge_min`, `integral_id_mixture`, `mixture_first_moment_ge_min` :
  Theorem 5.3.4(i). The aggregate idleness coefficient is a weighted average of
  the pool coefficients and is therefore at least their minimum.
* `first_moment_ge_of_ae_ge`, `mixture_first_moment_ge_of_ae_ge`,
  `first_moment_dirac` : the lower bound `⟨ι, η⟩ ≥ μ` in Corollary 5.3.6 and
  the fact that a point mass at the lower bound attains it.
* `priority_diffusion_comparison` : Lemma 5.3.9, in pathwise form.
* `expectation_mono_of_pathwise_le` : the step from the pathwise ordering to the
  ordering of expectations of nondecreasing functions used in Theorem 5.3.10.
-/
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

open MeasureTheory Set
open scoped NNReal

namespace ThesisLean.PoolPriority

/-! ### Theorem 5.3.4(i): mixture bound -/

/-- **Theorem 5.3.4(i), algebraic core.** If `p` is a probability vector on the
finite set of pools `J` and `m j` is the idleness coefficient of pool `j`, then
`min_j m j ≤ ∑_j p j * m j`. -/
theorem mixture_coeff_ge_min {J : Type*} [Fintype J] [Nonempty J] (p m : J → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hsum : ∑ j, p j = 1) :
    Finset.univ.inf' Finset.univ_nonempty m ≤ ∑ j, p j * m j := by
  sorry

/-- The first moment of a finite mixture `∑_j p j • η j` is the mixture of the
first moments. This is the identity `⟨ι, η⟩ = ∑_j p j ⟨ι, η j⟩` behind the mixture
representation of the aggregate fairness measure. -/
theorem integral_id_mixture {J : Type*} [Fintype J] (p : J → ℝ≥0) (η : J → Measure ℝ)
    (hint : ∀ j, Integrable (fun x : ℝ => x) (η j)) :
    ∫ x, x ∂(∑ j, p j • η j) = ∑ j, (p j : ℝ) * ∫ x, x ∂(η j) := by
  sorry

/-- **Theorem 5.3.4(i).** The idleness coefficient of the aggregate fairness
measure `∑_j p j • η j` is at least the smallest pool coefficient. -/
theorem mixture_first_moment_ge_min {J : Type*} [Fintype J] [Nonempty J] (p : J → ℝ≥0)
    (η : J → Measure ℝ) (hint : ∀ j, Integrable (fun x : ℝ => x) (η j))
    (hsum : ∑ j, p j = 1) :
    Finset.univ.inf' Finset.univ_nonempty (fun j => ∫ x, x ∂(η j))
      ≤ ∫ x, x ∂(∑ j, p j • η j) := by
  sorry

/-! ### Corollary 5.3.6: lower bound on the idleness coefficient -/

/-- If a probability measure `η` on the service-rate domain is concentrated on
`[c, ∞)`, then its first moment is at least `c`. -/
theorem first_moment_ge_of_ae_ge {η : Measure ℝ} [IsProbabilityMeasure η] {c : ℝ}
    (hint : Integrable (fun x : ℝ => x) η) (h : ∀ᵐ x ∂η, c ≤ x) :
    c ≤ ∫ x, x ∂η := by
  sorry

/-- If a probability measure `η` on the service-rate domain is concentrated on
`(-∞, c]`, then its first moment is at most `c`. -/
theorem first_moment_le_of_ae_le {η : Measure ℝ} [IsProbabilityMeasure η] {c : ℝ}
    (hint : Integrable (fun x : ℝ => x) η) (h : ∀ᵐ x ∂η, x ≤ c) :
    ∫ x, x ∂η ≤ c := by
  sorry

/-- **Corollary 5.3.6, lower bound.** Suppose the fairness measure of pool `j` is a
probability measure concentrated on `[μmin j, ∞)`. Then the idleness coefficient
of every mixture of the pool fairness measures is at least `min_j μmin j`. -/
theorem mixture_first_moment_ge_of_ae_ge {J : Type*} [Fintype J] [Nonempty J]
    (p : J → ℝ≥0) (η : J → Measure ℝ) [∀ j, IsProbabilityMeasure (η j)] (μmin : J → ℝ)
    (hint : ∀ j, Integrable (fun x : ℝ => x) (η j))
    (hlower : ∀ j, ∀ᵐ x ∂(η j), μmin j ≤ x) (hsum : ∑ j, p j = 1) :
    Finset.univ.inf' Finset.univ_nonempty μmin ≤ ∫ x, x ∂(∑ j, p j • η j) := by
  sorry

/-- The point mass at `a` has first moment `a`. With `a = μmin`, this is the
fastest-server-first coefficient, which attains the lower bound. -/
theorem first_moment_dirac (a : ℝ) : ∫ x, x ∂(Measure.dirac a) = a := by
  sorry

/-! ### Lemma 5.3.9: comparison of priority diffusion limits -/

/-- **Lemma 5.3.9, pathwise form.** Let `0 ≤ m ≤ m'` and `γ ≥ 0`. Let `x` and
`x'` be continuous paths solving equation (5.3.9),
`ξ(t) = y(t) + m ∫₀ᵗ ξ⁻(s) ds - γ ∫₀ᵗ ξ⁺(s) ds`,
with coefficients `m` and `m'` and the same driving path
`y(t) = ξ₀ + b̂ t + √2 W(t)`. Then `x t ≤ x' t` for all `t ≥ 0`.

The driving path `y` is arbitrary, so the statement applies to every
realisation of `(ξ₀, b̂, W)`. -/
theorem priority_diffusion_comparison {m m' γ : ℝ} (hm : 0 ≤ m) (hmm' : m ≤ m')
    (hγ : 0 ≤ γ) {y x x' : ℝ → ℝ} (hx : Continuous x) (hx' : Continuous x')
    (hsol : ∀ t, 0 ≤ t →
      x t = y t + m * (∫ s in (0 : ℝ)..t, (x s)⁻) - γ * ∫ s in (0 : ℝ)..t, (x s)⁺)
    (hsol' : ∀ t, 0 ≤ t →
      x' t = y t + m' * (∫ s in (0 : ℝ)..t, (x' s)⁻) - γ * ∫ s in (0 : ℝ)..t, (x' s)⁺) :
    ∀ t, 0 ≤ t → x t ≤ x' t := by
  sorry

/-- **Lemma 5.3.9, queue length.** Under the hypotheses of
`priority_diffusion_comparison`, the positive parts are ordered in the same way. -/
theorem priority_diffusion_comparison_posPart {m m' γ : ℝ} (hm : 0 ≤ m) (hmm' : m ≤ m')
    (hγ : 0 ≤ γ) {y x x' : ℝ → ℝ} (hx : Continuous x) (hx' : Continuous x')
    (hsol : ∀ t, 0 ≤ t →
      x t = y t + m * (∫ s in (0 : ℝ)..t, (x s)⁻) - γ * ∫ s in (0 : ℝ)..t, (x s)⁺)
    (hsol' : ∀ t, 0 ≤ t →
      x' t = y t + m' * (∫ s in (0 : ℝ)..t, (x' s)⁻) - γ * ∫ s in (0 : ℝ)..t, (x' s)⁺) :
    ∀ t, 0 ≤ t → (x t)⁺ ≤ (x' t)⁺ := by
  sorry

/-- A pathwise ordering `X ≤ X'` gives `E[f(X)] ≤ E[f(X')]` for every
nondecreasing `f`. This is the step from Lemma 5.3.9 to the stochastic ordering
in Theorem 5.3.10. -/
theorem expectation_mono_of_pathwise_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X X' : Ω → ℝ} {f : ℝ → ℝ} (hf : Monotone f) (hle : ∀ᵐ ω ∂P, X ω ≤ X' ω)
    (hfX : Integrable (fun ω => f (X ω)) P) (hfX' : Integrable (fun ω => f (X' ω)) P) :
    ∫ ω, f (X ω) ∂P ≤ ∫ ω, f (X' ω) ∂P := by
  sorry

end ThesisLean.PoolPriority
