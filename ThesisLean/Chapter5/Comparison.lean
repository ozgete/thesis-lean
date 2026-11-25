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
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Algebra.Order.Group.PosPart
import Mathlib.MeasureTheory.Integral.Bochner.Basic
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
  have hle : ∀ j, Finset.univ.inf' Finset.univ_nonempty m ≤ m j :=
    fun j => Finset.inf'_le m (Finset.mem_univ j)
  calc Finset.univ.inf' Finset.univ_nonempty m
      = ∑ j, p j * Finset.univ.inf' Finset.univ_nonempty m := by
        rw [← Finset.sum_mul, hsum, one_mul]
    _ ≤ ∑ j, p j * m j :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hle j) (hp j)

/-- The first moment of a finite mixture `∑_j p j • η j` is the mixture of the
first moments. This is the identity `⟨ι, η⟩ = ∑_j p j ⟨ι, η j⟩` behind the mixture
representation of the aggregate fairness measure. -/
theorem integral_id_mixture {J : Type*} [Fintype J] (p : J → ℝ≥0) (η : J → Measure ℝ)
    (hint : ∀ j, Integrable (fun x : ℝ => x) (η j)) :
    ∫ x, x ∂(∑ j, p j • η j) = ∑ j, (p j : ℝ) * ∫ x, x ∂(η j) := by
  classical
  have key : ∀ s : Finset J, Integrable (fun x : ℝ => x) (∑ j ∈ s, p j • η j) ∧
      ∫ x, x ∂(∑ j ∈ s, p j • η j) = ∑ j ∈ s, (p j : ℝ) * ∫ x, x ∂(η j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      have ha' : Integrable (fun x : ℝ => x) (p a • η a) := (hint a).smul_measure_nnreal
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      refine ⟨ha'.add_measure ih.1, ?_⟩
      rw [integral_add_measure ha' ih.1, ih.2, integral_smul_nnreal_measure, NNReal.smul_def,
        smul_eq_mul]
  exact (key Finset.univ).2

/-- **Theorem 5.3.4(i).** The idleness coefficient of the aggregate fairness
measure `∑_j p j • η j` is at least the smallest pool coefficient. -/
theorem mixture_first_moment_ge_min {J : Type*} [Fintype J] [Nonempty J] (p : J → ℝ≥0)
    (η : J → Measure ℝ) (hint : ∀ j, Integrable (fun x : ℝ => x) (η j))
    (hsum : ∑ j, p j = 1) :
    Finset.univ.inf' Finset.univ_nonempty (fun j => ∫ x, x ∂(η j))
      ≤ ∫ x, x ∂(∑ j, p j • η j) := by
  rw [integral_id_mixture p η hint]
  refine mixture_coeff_ge_min (fun j => (p j : ℝ)) (fun j => ∫ x, x ∂(η j))
    (fun j => (p j).coe_nonneg) ?_
  exact_mod_cast hsum

/-! ### Corollary 5.3.6: lower bound on the idleness coefficient -/

/-- If a probability measure `η` on the service-rate domain is concentrated on
`[c, ∞)`, then its first moment is at least `c`. -/
theorem first_moment_ge_of_ae_ge {η : Measure ℝ} [IsProbabilityMeasure η] {c : ℝ}
    (hint : Integrable (fun x : ℝ => x) η) (h : ∀ᵐ x ∂η, c ≤ x) :
    c ≤ ∫ x, x ∂η := by
  have h1 : ∫ _x : ℝ, c ∂η = c := by simp
  calc c = ∫ _x : ℝ, c ∂η := h1.symm
    _ ≤ ∫ x, x ∂η := integral_mono_ae (integrable_const c) hint h

/-- If a probability measure `η` on the service-rate domain is concentrated on
`(-∞, c]`, then its first moment is at most `c`. -/
theorem first_moment_le_of_ae_le {η : Measure ℝ} [IsProbabilityMeasure η] {c : ℝ}
    (hint : Integrable (fun x : ℝ => x) η) (h : ∀ᵐ x ∂η, x ≤ c) :
    ∫ x, x ∂η ≤ c := by
  have h1 : ∫ _x : ℝ, c ∂η = c := by simp
  calc ∫ x, x ∂η ≤ ∫ _x : ℝ, c ∂η := integral_mono_ae hint (integrable_const c) h
    _ = c := h1

/-- **Corollary 5.3.6, lower bound.** Suppose the fairness measure of pool `j` is a
probability measure concentrated on `[μmin j, ∞)`. Then the idleness coefficient
of every mixture of the pool fairness measures is at least `min_j μmin j`. -/
theorem mixture_first_moment_ge_of_ae_ge {J : Type*} [Fintype J] [Nonempty J]
    (p : J → ℝ≥0) (η : J → Measure ℝ) [∀ j, IsProbabilityMeasure (η j)] (μmin : J → ℝ)
    (hint : ∀ j, Integrable (fun x : ℝ => x) (η j))
    (hlower : ∀ j, ∀ᵐ x ∂(η j), μmin j ≤ x) (hsum : ∑ j, p j = 1) :
    Finset.univ.inf' Finset.univ_nonempty μmin ≤ ∫ x, x ∂(∑ j, p j • η j) := by
  refine le_trans ?_ (mixture_first_moment_ge_min p η hint hsum)
  refine Finset.le_inf' _ _ fun j _ => ?_
  exact (Finset.inf'_le μmin (Finset.mem_univ j)).trans
    (first_moment_ge_of_ae_ge (hint j) (hlower j))

/-- The point mass at `a` has first moment `a`. With `a = μmin`, this is the
fastest-server-first coefficient, which attains the lower bound. -/
theorem first_moment_dirac (a : ℝ) : ∫ x, x ∂(Measure.dirac a) = a := by
  exact integral_dirac (fun x : ℝ => x) a

/-! ### Lemma 5.3.9: comparison of priority diffusion limits -/

private lemma continuous_posPart_comp {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous fun s => (f s)⁺ := by
  simp only [posPart_def]
  exact hf.sup continuous_const

private lemma continuous_negPart_comp {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous fun s => (f s)⁻ := by
  simp only [negPart_def]
  exact hf.neg.sup continuous_const

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
  -- `G` is the difference of the two drift integrals, so that `G t = x t - x' t` for `t ≥ 0`.
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ, G = fun t =>
      m * (∫ s in (0 : ℝ)..t, (x s)⁻) - γ * (∫ s in (0 : ℝ)..t, (x s)⁺)
        - (m' * (∫ s in (0 : ℝ)..t, (x' s)⁻) - γ * ∫ s in (0 : ℝ)..t, (x' s)⁺) := ⟨_, rfl⟩
  have hGd : ∀ t, HasDerivAt G
      (m * (x t)⁻ - γ * (x t)⁺ - (m' * (x' t)⁻ - γ * (x' t)⁺)) t := by
    intro t
    have h1 := ((continuous_negPart_comp hx).integral_hasStrictDerivAt 0 t).hasDerivAt
    have h2 := ((continuous_posPart_comp hx).integral_hasStrictDerivAt 0 t).hasDerivAt
    have h3 := ((continuous_negPart_comp hx').integral_hasStrictDerivAt 0 t).hasDerivAt
    have h4 := ((continuous_posPart_comp hx').integral_hasStrictDerivAt 0 t).hasDerivAt
    rw [hG]
    exact ((h1.const_mul m).fun_sub (h2.const_mul γ)).fun_sub
      ((h3.const_mul m').fun_sub (h4.const_mul γ))
  have hG0 : G 0 = 0 := by
    rw [hG]
    simp
  have hGx : ∀ t, 0 ≤ t → G t = x t - x' t := by
    intro t ht
    have e1 := hsol t ht
    have e2 := hsol' t ht
    rw [hG]
    linarith
  -- The drift of `G` is nonpositive wherever `x' t ≤ x t`.
  have hdrift : ∀ t, x' t ≤ x t →
      m * (x t)⁻ - γ * (x t)⁺ - (m' * (x' t)⁻ - γ * (x' t)⁺) ≤ 0 := by
    intro t hxx
    have h1 : (x t)⁻ ≤ (x' t)⁻ := negPart_anti hxx
    have h2 : (x' t)⁺ ≤ (x t)⁺ := posPart_mono hxx
    have h3 : 0 ≤ (x' t)⁻ := negPart_nonneg _
    nlinarith [mul_nonneg hm (sub_nonneg.2 h1), mul_nonneg (sub_nonneg.2 hmm') h3,
      mul_nonneg hγ (sub_nonneg.2 h2)]
  -- Fencing argument. For every `ε > 0`, `G` stays below the line `δ s + δ` on `[0, T]`.
  have hGle : ∀ T, 0 ≤ T → G T ≤ 0 := by
    intro T hT
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hT1 : 0 < T + 1 := by linarith
    have hne : T + 1 ≠ 0 := hT1.ne'
    obtain ⟨δ, hδ, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ δ * T + δ = ε :=
      ⟨ε / (T + 1), div_pos hε hT1, by field_simp⟩
    have hB : ∀ s : ℝ, HasDerivAt (fun s : ℝ => δ * s + δ) δ s := fun s => by
      have h := ((hasDerivAt_id s).const_mul δ).add_const δ
      simpa using h
    have key : ∀ ⦃t⦄, t ∈ Icc (0 : ℝ) T → G t ≤ δ * t + δ := by
      refine image_le_of_deriv_right_lt_deriv_boundary (f := G)
        (f' := fun t => m * (x t)⁻ - γ * (x t)⁺ - (m' * (x' t)⁻ - γ * (x' t)⁺))
        (B := fun s => δ * s + δ) (B' := fun _ => δ) ?_ ?_ ?_ hB ?_
      · exact fun t _ => (hGd t).continuousAt.continuousWithinAt
      · exact fun t _ => (hGd t).hasDerivWithinAt
      · show G 0 ≤ δ * 0 + δ
        rw [hG0]
        linarith
      · intro t ht heq
        have heq' : G t = δ * t + δ := heq
        have hpos : 0 < δ * t + δ := by nlinarith [mul_nonneg hδ.le ht.1]
        have hxx : x' t ≤ x t := by
          have := hGx t ht.1
          linarith
        show m * (x t)⁻ - γ * (x t)⁺ - (m' * (x' t)⁻ - γ * (x' t)⁺) < δ
        linarith [hdrift t hxx]
    have := key ⟨hT, le_rfl⟩
    linarith
  intro t ht
  have h := hGle t ht
  rw [hGx t ht] at h
  linarith

/-- **Lemma 5.3.9, queue length.** Under the hypotheses of
`priority_diffusion_comparison`, the positive parts are ordered in the same way. -/
theorem priority_diffusion_comparison_posPart {m m' γ : ℝ} (hm : 0 ≤ m) (hmm' : m ≤ m')
    (hγ : 0 ≤ γ) {y x x' : ℝ → ℝ} (hx : Continuous x) (hx' : Continuous x')
    (hsol : ∀ t, 0 ≤ t →
      x t = y t + m * (∫ s in (0 : ℝ)..t, (x s)⁻) - γ * ∫ s in (0 : ℝ)..t, (x s)⁺)
    (hsol' : ∀ t, 0 ≤ t →
      x' t = y t + m' * (∫ s in (0 : ℝ)..t, (x' s)⁻) - γ * ∫ s in (0 : ℝ)..t, (x' s)⁺) :
    ∀ t, 0 ≤ t → (x t)⁺ ≤ (x' t)⁺ := by
  exact fun t ht =>
    posPart_mono (priority_diffusion_comparison hm hmm' hγ hx hx' hsol hsol' t ht)

/-- A pathwise ordering `X ≤ X'` gives `E[f(X)] ≤ E[f(X')]` for every
nondecreasing `f`. This is the step from Lemma 5.3.9 to the stochastic ordering
in Theorem 5.3.10. -/
theorem expectation_mono_of_pathwise_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X X' : Ω → ℝ} {f : ℝ → ℝ} (hf : Monotone f) (hle : ∀ᵐ ω ∂P, X ω ≤ X' ω)
    (hfX : Integrable (fun ω => f (X ω)) P) (hfX' : Integrable (fun ω => f (X' ω)) P) :
    ∫ ω, f (X ω) ∂P ≤ ∫ ω, f (X' ω) ∂P := by
  exact integral_mono_ae hfX hfX' (hle.mono fun ω h => hf h)

end ThesisLean.PoolPriority
