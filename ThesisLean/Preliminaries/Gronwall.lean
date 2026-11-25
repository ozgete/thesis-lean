/-
Thesis Section 2.4.4. Gronwall's inequality in integral form.
-/
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence

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
  -- Truncate `g` outside `[0, T]`, so that it is bounded and integrable on every interval.
  obtain ⟨gt, hgt⟩ : ∃ gt : ℝ → ℝ, gt = (Icc (0 : ℝ) T).indicator g := ⟨_, rfl⟩
  have hgt_in : ∀ s ∈ Icc (0 : ℝ) T, gt s = g s := fun s hs => by
    rw [hgt]
    exact Set.indicator_of_mem hs g
  have hgt_out : ∀ s, s ∉ Icc (0 : ℝ) T → gt s = 0 := fun s hs => by
    rw [hgt]
    exact Set.indicator_of_notMem hs g
  have hgt_meas : Measurable gt := by
    rw [hgt]
    exact hg_meas.indicator measurableSet_Icc
  have hgt_nonneg : ∀ s, 0 ≤ gt s := fun s => by
    by_cases hs : s ∈ Icc (0 : ℝ) T
    · rw [hgt_in s hs]
      exact hg_nonneg s hs
    · rw [hgt_out s hs]
  have hgt_le : ∀ s, gt s ≤ max C 0 := fun s => by
    by_cases hs : s ∈ Icc (0 : ℝ) T
    · rw [hgt_in s hs]
      exact (hg_bdd s hs).trans (le_max_left _ _)
    · rw [hgt_out s hs]
      exact le_max_right _ _
  have hgt_int : ∀ a b : ℝ, IntervalIntegrable gt volume a b := fun a b =>
    (intervalIntegrable_const (c := max C 0)).mono_fun' hgt_meas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun s => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hgt_nonneg s)]
        exact hgt_le s)
  have hint_eq : ∀ r ∈ Icc (0 : ℝ) T,
      ∫ s in (0 : ℝ)..r, gt s = ∫ s in (0 : ℝ)..r, g s := by
    intro r hr
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hr.1] at hs
    exact hgt_in s ⟨hs.1, hs.2.trans hr.2⟩
  -- `u r = ε + M ∫₀ʳ g` is continuous, and `U r = ∫₀ʳ u` is continuously differentiable.
  have hv_cont : Continuous fun r => ∫ s in (0 : ℝ)..r, gt s :=
    intervalIntegral.continuous_primitive hgt_int 0
  obtain ⟨u, hu⟩ : ∃ u : ℝ → ℝ, u = fun r => ε + M * ∫ s in (0 : ℝ)..r, gt s := ⟨_, rfl⟩
  have hu_apply : ∀ r, u r = ε + M * ∫ s in (0 : ℝ)..r, gt s := fun r => by rw [hu]
  have hu_cont : Continuous u := by
    rw [hu]
    exact continuous_const.add (continuous_const.mul hv_cont)
  obtain ⟨U, hU⟩ : ∃ U : ℝ → ℝ, U = fun r => ∫ s in (0 : ℝ)..r, u s := ⟨_, rfl⟩
  have hU_apply : ∀ r, U r = ∫ s in (0 : ℝ)..r, u s := fun r => by rw [hU]
  have hUd : ∀ r, HasDerivAt U (u r) r := fun r => by
    rw [hU]
    exact (hu_cont.integral_hasStrictDerivAt 0 r).hasDerivAt
  have hv_nonneg : ∀ r, 0 ≤ r → 0 ≤ ∫ s in (0 : ℝ)..r, gt s := fun r hr =>
    intervalIntegral.integral_nonneg hr fun s _ => hgt_nonneg s
  have hu_nonneg : ∀ r, 0 ≤ r → 0 ≤ u r := fun r hr => by
    rw [hu_apply]
    exact add_nonneg hε (mul_nonneg hM (hv_nonneg r hr))
  have hU_nonneg : ∀ r, 0 ≤ r → 0 ≤ U r := fun r hr => by
    rw [hU_apply]
    exact intervalIntegral.integral_nonneg hr fun s hs => hu_nonneg s hs.1
  have hgt_le_u : ∀ r ∈ Icc (0 : ℝ) T, gt r ≤ u r := fun r hr => by
    have h1 := hg r hr
    rw [← hint_eq r hr] at h1
    rw [hgt_in r hr, hu_apply]
    exact h1
  have hv_le_U : ∀ r ∈ Icc (0 : ℝ) T, ∫ s in (0 : ℝ)..r, gt s ≤ U r := fun r hr => by
    rw [hU_apply]
    exact intervalIntegral.integral_mono_on hr.1 (hgt_int 0 r) (hu_cont.intervalIntegrable 0 r)
      fun s hs => hgt_le_u s ⟨hs.1, hs.2.trans hr.2⟩
  -- Differential form of Gronwall's inequality for `U`, since `U' = u ≤ ε + M U`.
  have hUbound : ∀ r ∈ Icc (0 : ℝ) T, ‖U r‖ ≤ gronwallBound 0 M ε (r - 0) := by
    refine norm_le_gronwallBound_of_norm_deriv_right_le (f := U) (f' := u)
      (fun r _ => (hUd r).continuousAt.continuousWithinAt)
      (fun r _ => (hUd r).hasDerivWithinAt) ?_ ?_
    · rw [hU_apply]
      simp
    · intro r hr
      have hr' : r ∈ Icc (0 : ℝ) T := ⟨hr.1, hr.2.le⟩
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hu_nonneg r hr.1),
        abs_of_nonneg (hU_nonneg r hr.1)]
      have h1 := hu_apply r
      have h2 := mul_le_mul_of_nonneg_left (hv_le_U r hr') hM
      linarith
  intro t ht
  have hUt := hUbound t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (hU_nonneg t ht.1), sub_zero] at hUt
  have h1 : g t ≤ ε + M * U t := by
    have h3 := hgt_le_u t ht
    rw [hgt_in t ht] at h3
    have h4 := hu_apply t
    have h5 := mul_le_mul_of_nonneg_left (hv_le_U t ht) hM
    linarith
  have h2 : ε + M * gronwallBound 0 M ε t = ε * Real.exp (M * t) := by
    by_cases hM0 : M = 0
    · rw [hM0]
      simp
    · have h6 : gronwallBound 0 M ε t
          = 0 * Real.exp (M * t) + ε / M * (Real.exp (M * t) - 1) := by
        rw [gronwallBound_of_K_ne_0 hM0]
      have h7 : M * (ε / M) = ε := by
        field_simp
      calc ε + M * gronwallBound 0 M ε t
          = ε + M * (ε / M) * (Real.exp (M * t) - 1) := by
            rw [h6]
            ring
        _ = ε * Real.exp (M * t) := by
            rw [h7]
            ring
  calc g t ≤ ε + M * U t := h1
    _ ≤ ε + M * gronwallBound 0 M ε t := by
        have h8 := mul_le_mul_of_nonneg_left hUt hM
        linarith
    _ = ε * Real.exp (M * t) := h2

/-- **Lemma 2.4.3, case `ε = 0`.** Under the same hypotheses with `ε = 0`,
the function `g` vanishes on `[0, T]`. -/
theorem gronwall_integral_eq_zero {g : ℝ → ℝ} {T M C : ℝ} (hM : 0 ≤ M)
    (hg_meas : Measurable g)
    (hg_nonneg : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ g t)
    (hg_bdd : ∀ t ∈ Icc (0 : ℝ) T, g t ≤ C)
    (hg : ∀ t ∈ Icc (0 : ℝ) T, g t ≤ M * ∫ s in (0 : ℝ)..t, g s) :
    ∀ t ∈ Icc (0 : ℝ) T, g t = 0 := by
  intro t ht
  have h := gronwall_integral (le_refl (0 : ℝ)) hM hg_meas hg_nonneg hg_bdd
    (fun s hs => by
      rw [zero_add]
      exact hg s hs) t ht
  rw [zero_mul] at h
  exact le_antisymm h (hg_nonneg t ht)

end ThesisLean
