import ShenWork.Paper1.WholeLineWeightedRegularityWeightGap

open Filter MeasureTheory Real Set
open scoped RealInnerProductSpace

noncomputable section

namespace ShenWork.Paper1

/-!
# Weight-gap Holder families in whole-line `L2`

This file packages the scalar interpolation estimate from
`WholeLineWeightedRegularityWeightGap` as an honest
`WholeLineRealL2`-valued Holder trajectory.  It is the endpoint interface
consumed by the generator cancellation: no choice of pointwise dominator in
space is required.
-/

/-- Square-integrability of the exponential conjugate is exactly the
weighted square-integrability of the raw field. -/
theorem expWeighted_sq_integrable_of_weighted
    {eta : ℝ} {f : ℝ → ℝ}
    (hf : Integrable (fun x : ℝ =>
      Real.exp (2 * eta * x) * |f x| ^ 2)) :
    Integrable (fun x : ℝ => (Real.exp (eta * x) * f x) ^ 2) := by
  refine hf.congr (Eventually.of_forall fun x => ?_)
  change Real.exp (2 * eta * x) * |f x| ^ 2 =
    (Real.exp (eta * x) * f x) ^ 2
  rw [mul_pow, sq_abs]
  congr 1
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

/-- Canonical `L2` realization of a time-dependent exponentially weighted
field, with a quantitative Holder modulus obtained from a strict stronger
weight. -/
theorem exists_expWeightedL2_holder_of_weightGap
    {eta etaPlus alpha H K : ℝ}
    (heta : 0 < eta) (hgap : eta < etaPlus)
    (halpha : 0 < alpha) (hH : 0 ≤ H)
    {F : ℝ → ℝ → ℝ}
    (hF_meas : ∀ s, AEStronglyMeasurable (F s) volume)
    (hweak : ∀ s, Integrable (fun x : ℝ =>
      Real.exp (2 * eta * x) * |F s x| ^ 2))
    (hstrong : ∀ s,
      Integrable (fun x : ℝ =>
          Real.exp (2 * etaPlus * x) * |F s x| ^ 2) ∧
        (∫ x : ℝ,
          Real.exp (2 * etaPlus * x) * |F s x| ^ 2) ≤ K)
    (hsup : ∀ s t x, |F s x - F t x| ≤ H * |s - t| ^ alpha) :
    ∃ Z : ℝ → WholeLineRealL2,
      (∀ s, ((Z s : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        fun x => Real.exp (eta * x) * F s x) ∧
      ∀ s t, |s - t| ≤ 1 →
        ‖Z s - Z t‖ ≤
          Real.sqrt (H ^ 2 / (2 * eta) + 4 * K) *
            |s - t| ^ (alpha * (etaPlus - eta) / etaPlus) := by
  have hweighted_meas : ∀ s,
      AEStronglyMeasurable (fun x : ℝ => Real.exp (eta * x) * F s x)
        volume := by
    intro s
    exact ((Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).aestronglyMeasurable.mul
        (hF_meas s))
  have hweighted_sq : ∀ s,
      Integrable (fun x : ℝ => (Real.exp (eta * x) * F s x) ^ 2) :=
    fun s => expWeighted_sq_integrable_of_weighted (hweak s)
  let Z : ℝ → WholeLineRealL2 := fun s =>
    wholeLineRealL2OfSqIntegrable
      (fun x => Real.exp (eta * x) * F s x)
      (hweighted_meas s) (hweighted_sq s)
  have hrep : ∀ s, ((Z s : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
      fun x => Real.exp (eta * x) * F s x := by
    intro s
    exact wholeLineRealL2OfSqIntegrable_coe_ae
      _ (hweighted_meas s) (hweighted_sq s)
  refine ⟨Z, hrep, ?_⟩
  intro s t hdelta_one
  let theta : ℝ := alpha * (etaPlus - eta) / etaPlus
  let C : ℝ := H ^ 2 / (2 * eta) + 4 * K
  have htheta : 0 < theta := by
    dsimp only [theta]
    have hetaPlus : 0 < etaPlus := heta.trans hgap
    exact div_pos (mul_pos halpha (sub_pos.mpr hgap)) hetaPlus
  by_cases hst : s = t
  · subst t
    simp only [sub_self, norm_zero, abs_zero]
    rw [Real.zero_rpow (ne_of_gt htheta)]
    simp
  have hdelta : 0 < |s - t| := abs_pos.mpr (sub_ne_zero.mpr hst)
  have hgapData := weightedL2_holder_of_sup_holder_and_stronger_bound
    heta hgap halpha hH hF_meas hstrong hsup
    s t hdelta hdelta_one
  have hdiff_rep :
      (((Z s - Z t : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        fun x => Real.exp (eta * x) * (F s x - F t x)) := by
    filter_upwards [Lp.coeFn_sub (Z s) (Z t), hrep s, hrep t]
      with x hsub hs ht
    rw [hsub]
    change (Z s : ℝ → ℝ) x - (Z t : ℝ → ℝ) x = _
    rw [hs, ht]
    ring
  have hdiffIntegral :
      (∫ x : ℝ,
          (Real.exp (eta * x) * (F s x - F t x)) ^ 2) =
        ∫ x : ℝ,
          Real.exp (2 * eta * x) * |F s x - F t x| ^ 2 := by
    apply integral_congr_ae
    filter_upwards with x
    rw [mul_pow, sq_abs]
    congr 1
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hnormSq : ‖Z s - Z t‖ ^ 2 ≤
      C * |s - t| ^ (2 * theta) := by
    have hinner := wholeLineIntegral_mul_eq_inner_of_aeEq
      (Z s - Z t) (Z s - Z t) hdiff_rep hdiff_rep
    rw [real_inner_self_eq_norm_sq] at hinner
    have heqNorm : ‖Z s - Z t‖ ^ 2 =
        ∫ x : ℝ,
          (Real.exp (eta * x) * (F s x - F t x)) ^ 2 := by
      simpa only [pow_two] using hinner.symm
    rw [heqNorm, hdiffIntegral]
    simpa only [C, theta] using hgapData.2
  have hK : 0 ≤ K := by
    have hnonneg : 0 ≤ ∫ x : ℝ,
        Real.exp (2 * etaPlus * x) * |F 0 x| ^ 2 :=
      integral_nonneg fun x => by positivity
    exact hnonneg.trans (hstrong 0).2
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact add_nonneg
      (div_nonneg (sq_nonneg H) (by positivity))
      (mul_nonneg (by norm_num) hK)
  have hdeltaNonneg : 0 ≤ |s - t| := abs_nonneg _
  have htarget : 0 ≤ Real.sqrt C * |s - t| ^ theta :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hdeltaNonneg _)
  apply (sq_le_sq₀ (norm_nonneg _) htarget).mp
  calc
    ‖Z s - Z t‖ ^ 2 ≤ C * |s - t| ^ (2 * theta) := hnormSq
    _ = (Real.sqrt C * |s - t| ^ theta) ^ 2 := by
      rw [show 2 * theta = theta * 2 by ring,
        Real.rpow_mul hdeltaNonneg, Real.rpow_two,
        mul_pow, Real.sq_sqrt hC]

/-- A local power modulus on time differences gives a continuous
Banach-valued trajectory.  The unit-radius guard is exactly the one exported
by `exists_expWeightedL2_holder_of_weightGap`. -/
theorem continuous_of_local_rpow_holder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {theta C : ℝ} (htheta : 0 < theta)
    {Z : ℝ → E}
    (hholder : ∀ s t, |s - t| ≤ 1 →
      ‖Z s - Z t‖ ≤ C * |s - t| ^ theta) :
    Continuous Z := by
  rw [continuous_iff_continuousAt]
  intro t
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hmajorTendsto : Tendsto
      (fun s : ℝ => C * |s - t| ^ theta) (nhds t) (nhds 0) := by
    have hcont : Continuous (fun s : ℝ => C * |s - t| ^ theta) :=
      continuous_const.mul
        ((continuous_id.sub continuous_const).abs.rpow_const
          (fun _ => Or.inr htheta.le))
    have ht : Tendsto (fun s : ℝ => C * |s - t| ^ theta)
        (nhds t) (nhds (C * |t - t| ^ theta)) := hcont.continuousAt
    simpa only [sub_self, abs_zero, Real.zero_rpow (ne_of_gt htheta),
      mul_zero] using ht
  have hbound : ∀ᶠ s in nhds t,
      ‖Z s - Z t‖ ≤ C * |s - t| ^ theta := by
    filter_upwards [Metric.ball_mem_nhds t zero_lt_one] with s hs
    apply hholder s t
    have hs' : dist s t < 1 := by
      simpa only [Metric.mem_ball, dist_comm] using hs
    simpa only [Real.dist_eq] using hs'.le
  exact squeeze_zero'
    (Eventually.of_forall fun s => norm_nonneg (Z s - Z t))
    hbound hmajorTendsto

/-- The weight-gap construction together with its automatic continuity.
This is the endpoint package consumed by the concrete generator-cancellation
argument: the chosen `L2` trajectory has the prescribed representatives, is
continuous in time, and retains the quantitative local Holder modulus. -/
theorem exists_expWeightedL2_continuous_holder_of_weightGap
    {eta etaPlus alpha H K : ℝ}
    (heta : 0 < eta) (hgap : eta < etaPlus)
    (halpha : 0 < alpha) (hH : 0 ≤ H)
    {F : ℝ → ℝ → ℝ}
    (hF_meas : ∀ s, AEStronglyMeasurable (F s) volume)
    (hweak : ∀ s, Integrable (fun x : ℝ =>
      Real.exp (2 * eta * x) * |F s x| ^ 2))
    (hstrong : ∀ s,
      Integrable (fun x : ℝ =>
          Real.exp (2 * etaPlus * x) * |F s x| ^ 2) ∧
        (∫ x : ℝ,
          Real.exp (2 * etaPlus * x) * |F s x| ^ 2) ≤ K)
    (hsup : ∀ s t x, |F s x - F t x| ≤ H * |s - t| ^ alpha) :
    ∃ Z : ℝ → WholeLineRealL2,
      (∀ s, ((Z s : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        fun x => Real.exp (eta * x) * F s x) ∧
      Continuous Z ∧
      ∀ s t, |s - t| ≤ 1 →
        ‖Z s - Z t‖ ≤
          Real.sqrt (H ^ 2 / (2 * eta) + 4 * K) *
            |s - t| ^ (alpha * (etaPlus - eta) / etaPlus) := by
  obtain ⟨Z, hrep, hholder⟩ :=
    exists_expWeightedL2_holder_of_weightGap
      heta hgap halpha hH hF_meas hweak hstrong hsup
  have hetaPlus : 0 < etaPlus := heta.trans hgap
  have htheta : 0 < alpha * (etaPlus - eta) / etaPlus :=
    div_pos (mul_pos halpha (sub_pos.mpr hgap)) hetaPlus
  exact ⟨Z, hrep,
    continuous_of_local_rpow_holder htheta hholder, hholder⟩

section AxiomAudit

#print axioms expWeighted_sq_integrable_of_weighted
#print axioms exists_expWeightedL2_holder_of_weightGap
#print axioms continuous_of_local_rpow_holder
#print axioms exists_expWeightedL2_continuous_holder_of_weightGap

end AxiomAudit

end ShenWork.Paper1
