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
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.EssSup

open MeasureTheory ProbabilityTheory Filter

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

/-! ### Auxiliary facts under Assumption 6.1.1 -/

private lemma aux_nonneg (h : RateBounds F lo hi) : ∀ᵐ x ∂F, 0 ≤ x := by
  filter_upwards [h.lower] with x hl
  exact h.pos.le.trans hl

private lemma aux_norm_le (h : RateBounds F lo hi) : ∀ᵐ x ∂F, ‖x‖ ≤ hi := by
  filter_upwards [h.lower, h.upper] with x hl hu
  rw [Real.norm_eq_abs, abs_of_nonneg (h.pos.le.trans hl)]
  exact hu

private lemma aux_integrable (h : RateBounds F lo hi) : Integrable (fun x : ℝ => x) F :=
  Integrable.of_bound measurable_id.aestronglyMeasurable hi (aux_norm_le h)

private lemma aux_memLp (h : RateBounds F lo hi) : MemLp (fun x : ℝ => x) 2 F :=
  MemLp.of_bound measurable_id.aestronglyMeasurable hi (aux_norm_le h)

private lemma aux_integrable_sq (h : RateBounds F lo hi) :
    Integrable (fun x : ℝ => x ^ 2) F := by
  refine Integrable.of_bound (measurable_id.pow_const 2).aestronglyMeasurable (hi ^ 2) ?_
  filter_upwards [h.lower, h.upper] with x hl hu
  have hx : 0 ≤ x := h.pos.le.trans hl
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hx 2)]
  exact pow_le_pow_left₀ hx hu 2

private lemma aux_lo_le_meanRate (h : RateBounds F lo hi) : lo ≤ meanRate F := by
  have h1 : ∫ _x : ℝ, lo ∂F = lo := by simp
  unfold meanRate
  calc lo = ∫ _x : ℝ, lo ∂F := h1.symm
    _ ≤ ∫ x, x ∂F := integral_mono_ae (integrable_const lo) (aux_integrable h) h.lower

private lemma aux_meanRate_pos (h : RateBounds F lo hi) : 0 < meanRate F :=
  h.pos.trans_le (aux_lo_le_meanRate h)

private lemma aux_bddAbove (h : RateBounds F lo hi) :
    IsBoundedUnder (· ≤ ·) (ae F) (fun x : ℝ => x) :=
  ⟨hi, eventually_map.2 h.upper⟩

private lemma aux_bddBelow (h : RateBounds F lo hi) :
    IsBoundedUnder (· ≥ ·) (ae F) (fun x : ℝ => x) :=
  ⟨lo, eventually_map.2 h.lower⟩

/-- `σ_F² = E[μ̃²] - μ̄_F²`. -/
private lemma aux_varRate_eq (h : RateBounds F lo hi) :
    varRate F = (∫ x, x ^ 2 ∂F) - meanRate F ^ 2 := by
  unfold varRate meanRate
  rw [variance_eq_sub (aux_memLp h)]
  rfl

/-! ### The essential infimum and supremum -/

/-- Under Assumption 6.1.1, every almost-sure lower bound is at most `μmin`. -/
theorem le_muMin (h : RateBounds F lo hi) : lo ≤ muMin F := by
  exact le_essInf_of_ae_le lo h.lower (aux_bddAbove h).isCoboundedUnder_ge

/-- Under Assumption 6.1.1, `μmax` is at most every almost-sure upper bound. -/
theorem muMax_le (h : RateBounds F lo hi) : muMax F ≤ hi := by
  exact essSup_le_of_ae_le hi h.upper (aux_bddBelow h).isCoboundedUnder_le

/-- Under Assumption 6.1.1, the service rate is at least `μmin` almost surely. -/
theorem ae_muMin_le (h : RateBounds F lo hi) : ∀ᵐ x ∂F, muMin F ≤ x := by
  exact ae_essInf_le (aux_bddBelow h)

/-- Under Assumption 6.1.1, the service rate is at most `μmax` almost surely. -/
theorem ae_le_muMax (h : RateBounds F lo hi) : ∀ᵐ x ∂F, x ≤ muMax F := by
  exact ae_le_essSup (aux_bddAbove h)

/-- Under Assumption 6.1.1, the bounds hold with the essential infimum and
supremum themselves. -/
theorem rateBounds_essential (h : RateBounds F lo hi) :
    RateBounds F (muMin F) (muMax F) := by
  exact ⟨h.pos.trans_le (le_muMin h), ae_muMin_le h, ae_le_muMax h⟩

/-- Under Assumption 6.1.1, `κ_FSF = μmin > 0`. -/
theorem kappaFSF_pos (h : RateBounds F lo hi) : 0 < kappaFSF F := by
  exact h.pos.trans_le (le_muMin h)

/-! ### Fairness measures and their first moments -/

/-- The size-biased measure `η_TB` is a probability measure. -/
theorem isProbabilityMeasure_etaTB (h : RateBounds F lo hi) :
    IsProbabilityMeasure (etaTB F) := by
  have hm := aux_meanRate_pos h
  have hint : Integrable (fun x : ℝ => x / meanRate F) F := (aux_integrable h).div_const _
  have hnn : 0 ≤ᵐ[F] fun x : ℝ => x / meanRate F := by
    filter_upwards [aux_nonneg h] with x hx
    exact div_nonneg hx hm.le
  have hone : ∫ x, x / meanRate F ∂F = 1 := by
    rw [integral_div]
    exact div_self hm.ne'
  refine ⟨?_⟩
  rw [etaTB, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint hnn, hone, ENNReal.ofReal_one]

/-- `κ_TB = ⟨ι, η_TB⟩`. The fairness coefficient under totally blind routing is the
first moment of the size-biased measure. -/
theorem first_moment_etaTB (h : RateBounds F lo hi) :
    ∫ x, x ∂(etaTB F) = kappaTB F := by
  have hm := aux_meanRate_pos h
  have hmeas : Measurable fun x : ℝ => ENNReal.ofReal (x / meanRate F) :=
    (measurable_id.div_const _).ennreal_ofReal
  have hcongr : (fun x : ℝ => (ENNReal.ofReal (x / meanRate F)).toReal • x)
      =ᵐ[F] fun x => x ^ 2 / meanRate F := by
    filter_upwards [aux_nonneg h] with x hx
    rw [ENNReal.toReal_ofReal (div_nonneg hx hm.le), smul_eq_mul]
    ring
  unfold etaTB
  rw [integral_withDensity_eq_integral_toReal_smul hmeas
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), integral_congr_ae hcongr, integral_div]
  rfl

/-- `κ_FSF = ⟨ι, η_FSF⟩`. The fairness coefficient under fastest-server-first
routing is the first moment of the point mass at `μmin`. -/
theorem first_moment_etaFSF (F : Measure ℝ) : ∫ x, x ∂(etaFSF F) = kappaFSF F := by
  exact integral_dirac (fun x : ℝ => x) (muMin F)

/-! ### Equations (6.2.2) to (6.2.4) -/

/-- **Equation (6.2.2).** `κ_TB = μ̄_F + σ_F² / μ̄_F`. -/
theorem kappaTB_eq (h : RateBounds F lo hi) :
    kappaTB F = meanRate F + varRate F / meanRate F := by
  have hm := aux_meanRate_pos h
  have h1 : ((∫ x, x ^ 2 ∂F) - meanRate F ^ 2) / meanRate F
      = (∫ x, x ^ 2 ∂F) / meanRate F - meanRate F := by
    rw [sub_div, pow_two, mul_div_assoc, div_self hm.ne', mul_one]
  rw [aux_varRate_eq h, h1]
  unfold kappaTB
  show (∫ x, x ^ 2 ∂F) / meanRate F = meanRate F + ((∫ x, x ^ 2 ∂F) / meanRate F - meanRate F)
  ring

/-- Auxiliary form of (6.2.3) for arbitrary almost-sure bounds. If `F` is
nondegenerate, then `lo < μ̄_F < κ_TB ≤ hi`. -/
theorem coefficient_ordering_of_bounds (h : RateBounds F lo hi) (hnd : 0 < varRate F) :
    lo < meanRate F ∧ meanRate F < kappaTB F ∧ kappaTB F ≤ hi := by
  have hm := aux_meanRate_pos h
  have hint := aux_integrable h
  refine ⟨?_, ?_, ?_⟩
  · -- `lo < μ̄_F`. Otherwise `μ̃ = lo` almost surely and the variance vanishes.
    rcases (aux_lo_le_meanRate h).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have hc : ∫ _x : ℝ, lo ∂F = lo := by simp
      have h0 : ∫ x, (x - lo) ∂F = 0 := by
        rw [integral_sub hint (integrable_const lo), hc]
        show meanRate F - lo = 0
        linarith
      have hnn : 0 ≤ᵐ[F] fun x : ℝ => x - lo := by
        filter_upwards [h.lower] with x hx
        exact sub_nonneg.2 hx
      have hae := (integral_eq_zero_iff_of_nonneg_ae hnn (hint.sub (integrable_const lo))).1 h0
      have hsqae : (fun x : ℝ => x ^ 2) =ᵐ[F] fun _ => lo ^ 2 := by
        filter_upwards [hae] with x hx
        have hx' : x - lo = 0 := hx
        have hx'' : x = lo := by linarith
        rw [hx'']
      have hc2 : ∫ _x : ℝ, lo ^ 2 ∂F = lo ^ 2 := by simp
      have hsq : ∫ x, x ^ 2 ∂F = lo ^ 2 := by
        rw [integral_congr_ae hsqae, hc2]
      have hv := aux_varRate_eq h
      rw [hsq, ← heq] at hv
      linarith
  · rw [kappaTB_eq h]
    have := div_pos hnd hm
    linarith
  · have hm' : 0 < ∫ x, x ∂F := hm
    unfold kappaTB
    rw [div_le_iff₀ hm']
    calc ∫ x, x ^ 2 ∂F ≤ ∫ x, hi * x ∂F :=
          integral_mono_ae (aux_integrable_sq h) (hint.const_mul hi) (by
            filter_upwards [aux_nonneg h, h.upper] with x hx hu
            nlinarith)
      _ = hi * ∫ x, x ∂F := integral_const_mul hi _

/-- **Equation (6.2.3).** If `F` is nondegenerate, then
`κ_FSF = μmin < μ̄_F < κ_TB ≤ μmax`. -/
theorem coefficient_ordering (h : RateBounds F lo hi) (hnd : 0 < varRate F) :
    kappaFSF F < meanRate F ∧ meanRate F < kappaTB F ∧ kappaTB F ≤ muMax F := by
  exact coefficient_ordering_of_bounds (rateBounds_essential h) hnd

/-- **Equation (6.2.3), consequence used in Corollary 6.3.7.** If `F` is
nondegenerate, then `κ_FSF < κ_TB`. -/
theorem kappaFSF_lt_kappaTB (h : RateBounds F lo hi) (hnd : 0 < varRate F) :
    kappaFSF F < kappaTB F := by
  exact (coefficient_ordering h hnd).1.trans (coefficient_ordering h hnd).2.1

/-- **Equation (6.2.4).** `κ_TB - κ_FSF = (μ̄_F - μmin) + σ_F² / μ̄_F`. -/
theorem kappaTB_sub_kappaFSF (h : RateBounds F lo hi) :
    kappaTB F - kappaFSF F = (meanRate F - muMin F) + varRate F / meanRate F := by
  rw [kappaTB_eq h]
  unfold kappaFSF
  ring

/-- If `F` is degenerate, the two fairness coefficients coincide. -/
theorem kappaFSF_eq_kappaTB_of_degenerate (h : RateBounds F lo hi)
    (hd : varRate F = 0) : kappaFSF F = kappaTB F := by
  have hae : (fun x : ℝ => x) =ᵐ[F] fun _ => meanRate F :=
    ae_eq_integral_of_variance_eq_zero (aux_memLp h) hd
  have h1 : kappaFSF F = meanRate F := by
    unfold kappaFSF muMin
    rw [essInf_congr_ae hae, essInf_const']
  rw [h1, kappaTB_eq h, hd, zero_div, add_zero]

end ThesisLean.CostOfFairness
