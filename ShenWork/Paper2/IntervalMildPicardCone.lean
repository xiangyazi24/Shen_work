/-
  Q1 cone invariance, step lemma (χ₀ = 0): the gradient mild map
  preserves the exponential cone around the heat profile.

  For χ₀ = 0 the mild map is `Φ(u₀, w)(t) = S(t)u₀ + ∫₀ᵗ S(t−s)L(w s) ds`.
  On the cone `0 ≤ w(s) ≤ e^{as}·S(s)f₀` (f₀ = continuous extension of u₀,
  `|w| ≤ Mw`), the logistic source is pinched:

    `−Ke·e^{as}·S(s)f₀ ≤ L(w s) ≤ a·e^{as}·S(s)f₀`  on `[0,1]`,
    `Ke := b·Mw^α`,

  and the Duhamel integral collapses through monotonicity + the
  Chapman–Kolmogorov law (`S(t−s)(c·S(s)f₀) = c·S(t)f₀`):

    `(1 − Ke·I(t))·S(t)f₀ ≤ Φ(u₀,w)(t) ≤ (1 + a·I(t))·S(t)f₀`,
    `I(t) := ∫₀ᵗ e^{as} ds`.

  Since `1 + a·I(t) = e^{at}`, the upper cone is EXACTLY invariant; the
  lower output `1 − Ke·I(t) ≥ ½` on a horizon δ(M) chosen with
  `Ke·I(δ) ≤ ½` — uniform over the datum class, with NO inf-threshold.
  This is the positivity engine replacing `corrections < inf u₀`.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.PDE.IntervalSemigroupConeAtoms
import ShenWork.Paper2.IntervalMildPicardThreshold

open MeasureTheory
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalFullKernelSpectralClean
open ShenWork.IntervalGradientDuhamelMap
open ShenWork.IntervalMildPicard
open ShenWork.IntervalMildPicardThreshold
open ShenWork.IntervalSemigroupComposition
open ShenWork.IntervalSemigroupConeAtoms

noncomputable section

namespace ShenWork.IntervalMildPicardCone

/-- The exponential-in-time envelope integral `I(t) = ∫₀ᵗ e^{as} ds`. -/
def envelopeIntegral (a t : ℝ) : ℝ := ∫ s in (0:ℝ)..t, Real.exp (a * s)

set_option maxHeartbeats 1600000 in
/-- **Cone preservation for the χ₀ = 0 mild map.**

If the trajectory `w` satisfies `0 ≤ w(s) ≤ e^{as}·S(s)f₀` on `(0, T]`
with `|w| ≤ Mw`, then

  `(1 − Ke·I(t))·S(t)f₀(x) ≤ Φ(u₀,w)(t,x) ≤ (1 + a·I(t))·S(t)f₀(x)`

for all `t ∈ (0, T]`, where `Ke ≥ b·Mw^α` and `I = envelopeIntegral a`.
`f₀` is any continuous, globally bounded function agreeing with the lift
of `u₀` on `[0,1]` with bounded cosine coefficients (e.g. the clipped
extension). -/
theorem cone_preserved
    (p : CM2Params) (hχ : p.χ₀ = 0)
    {u₀ : intervalDomainPoint → ℝ}
    {f₀ : ℝ → ℝ} (hf₀_cont : Continuous f₀)
    (hf₀_eq : ∀ y ∈ Set.Icc (0:ℝ) 1, intervalDomainLift u₀ y = f₀ y)
    {Mf₀ : ℝ} (hMf₀ : 0 ≤ Mf₀) (hf₀_bdd : ∀ y, |f₀ y| ≤ Mf₀)
    {Mc : ℝ} (hMc : ∀ n, |cosineCoeffs f₀ n| ≤ Mc)
    {T Ke Mw : ℝ} (hT : 0 < T) (hMw : 0 < Mw)
    (hKe_ge : p.b * Mw ^ p.α ≤ Ke)
    {w : ℝ → intervalDomainPoint → ℝ}
    (hw_meas : HasJointMeasurability w)
    (hw_bdd : ∀ s, 0 < s → s ≤ T → ∀ x, |w s x| ≤ Mw)
    (hcone_lo : ∀ s, 0 < s → s ≤ T → ∀ x : intervalDomainPoint, 0 ≤ w s x)
    (hcone_hi : ∀ s, 0 < s → s ≤ T → ∀ x : intervalDomainPoint,
      w s x ≤ Real.exp (p.a * s) * intervalFullSemigroupOperator s f₀ x.1) :
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      (1 - Ke * envelopeIntegral p.a t) *
          intervalFullSemigroupOperator t f₀ x.1
        ≤ intervalGradientDuhamelMap p u₀ w t x ∧
      intervalGradientDuhamelMap p u₀ w t x
        ≤ (1 + p.a * envelopeIntegral p.a t) *
          intervalFullSemigroupOperator t f₀ x.1 := by
  intro t ht htT x
  have hKe_nn : 0 ≤ Ke :=
    le_trans (mul_nonneg p.hb (Real.rpow_nonneg hMw.le _)) hKe_ge
  -- χ₀ = 0 kills the flux term.
  have hΦ_eq : intervalGradientDuhamelMap p u₀ w t x
      = intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
        + ∫ s in (0:ℝ)..t, intervalFullSemigroupOperator (t - s)
            (logisticLifted p (w s)) x.1 := by
    unfold intervalGradientDuhamelMap
    rw [hχ]
    ring
  -- Replace the lift by the continuous extension in the semigroup term.
  have hS_eq : intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
      = intervalFullSemigroupOperator t f₀ x.1 := by
    unfold intervalFullSemigroupOperator
    apply integral_congr_ae
    have hae : ∀ᵐ y ∂(intervalMeasure 1), y ∈ Set.Icc (0:ℝ) 1 := by
      simp only [ShenWork.IntervalDomain.intervalMeasure,
        ShenWork.IntervalDomain.intervalSet]
      exact (ae_restrict_iff' measurableSet_Icc).mpr
        (Filter.Eventually.of_forall fun y hy => hy)
    filter_upwards [hae] with y hy
    rw [hf₀_eq y hy]
  -- The cutoff logistic source.
  set C_L : ℝ := Mw * (p.a + p.b * Mw ^ p.α) with hC_L_def
  have hC_L_nn : 0 ≤ C_L :=
    mul_nonneg hMw.le (add_nonneg p.ha
      (mul_nonneg p.hb (Real.rpow_nonneg hMw.le _)))
  set r : ℝ → ℝ → ℝ := fun s y =>
    if 0 < s ∧ s ≤ T then logisticLifted p (w s) y else 0 with hr_def
  have hr_bdd : ∀ s y, |r s y| ≤ C_L := by
    intro s y
    simp only [hr_def]
    split_ifs with h
    · exact ShenWork.IntervalDomainExistence.intervalLogisticSource_lift_abs_bound
        p hMw (fun z => hw_bdd s h.1 h.2 z) y
    · simp; exact hC_L_nn
  have hr_meas : Measurable (Function.uncurry r) := by
    simpa [Function.uncurry] using
      logisticLifted_time_cutoff_measurable' (p := p) (T := T) hw_meas
  -- The Duhamel integrand agrees with the cutoff version on (0, t].
  have hV_eq : (∫ s in (0:ℝ)..t, intervalFullSemigroupOperator (t - s)
        (logisticLifted p (w s)) x.1)
      = ∫ s in (0:ℝ)..t, intervalFullSemigroupOperator (t - s) (r s) x.1 := by
    apply intervalIntegral.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro s hs
    rw [Set.uIoc_of_le ht.le] at hs
    simp only [hr_def, if_pos (And.intro hs.1 (hs.2.trans htT))]
  -- Integrability of the cutoff Duhamel integrand.
  have hint_V : IntervalIntegrable
      (fun s => intervalFullSemigroupOperator (t - s) (r s) x.1)
      volume 0 t :=
    ShenWork.IntervalDuhamelIntegrability.valueDuhamel_intervalIntegrable_of_joint_measurable
      ht hr_meas hC_L_nn hr_bdd x.1
  -- Boundedness/continuity facts for the comparison profiles.
  have hSf₀_cont : ∀ {s : ℝ}, 0 < s →
      Continuous (fun y => intervalFullSemigroupOperator s f₀ y) :=
    fun {s} hs =>
      (intervalFullSemigroupOperator_contDiff_two_clean hs hf₀_cont hMc).continuous
  have hSf₀_bdd : ∀ {s : ℝ}, 0 < s → ∀ y,
      |intervalFullSemigroupOperator s f₀ y| ≤ Mf₀ := fun {s} hs y =>
    intervalFullSemigroupOperator_Linfty_bound hs hMf₀ hf₀_bdd y
  -- AESM of the cutoff source slices.
  have hr_slice_meas : ∀ s, AEStronglyMeasurable (r s) (intervalMeasure 1) := by
    intro s
    have hm : Measurable (fun y : ℝ => r s y) :=
      hr_meas.comp (measurable_const.prodMk measurable_id)
    exact hm.aestronglyMeasurable
  -- Pointwise source pinch on [0,1], for 0 < s < t.
  have hsource_hi : ∀ s, 0 < s → s < t → ∀ y ∈ Set.Icc (0:ℝ) 1,
      r s y ≤ (p.a * Real.exp (p.a * s)) *
        intervalFullSemigroupOperator s f₀ y := by
    intro s hs hst y hy
    have hsT : s ≤ T := le_trans hst.le htT
    simp only [hr_def, if_pos (And.intro hs hsT)]
    have hz_nn : 0 ≤ w s ⟨y, hy⟩ := hcone_lo s hs hsT ⟨y, hy⟩
    have hz_hi : w s ⟨y, hy⟩ ≤ Real.exp (p.a * s) *
        intervalFullSemigroupOperator s f₀ y := hcone_hi s hs hsT ⟨y, hy⟩
    have hlift_eq : logisticLifted p (w s) y
        = w s ⟨y, hy⟩ * (p.a - p.b * (w s ⟨y, hy⟩) ^ p.α) := by
      simp [logisticLifted, ShenWork.IntervalDomainExistence.intervalLogisticSource,
        intervalDomainLift, hy]
    rw [hlift_eq]
    have h1 : w s ⟨y, hy⟩ * (p.a - p.b * (w s ⟨y, hy⟩) ^ p.α)
        ≤ p.a * w s ⟨y, hy⟩ := by
      have hsub : 0 ≤ p.b * (w s ⟨y, hy⟩) ^ p.α :=
        mul_nonneg p.hb (Real.rpow_nonneg hz_nn _)
      nlinarith [mul_nonneg hz_nn hsub]
    calc w s ⟨y, hy⟩ * (p.a - p.b * (w s ⟨y, hy⟩) ^ p.α)
        ≤ p.a * w s ⟨y, hy⟩ := h1
      _ ≤ p.a * (Real.exp (p.a * s) *
            intervalFullSemigroupOperator s f₀ y) :=
          mul_le_mul_of_nonneg_left hz_hi p.ha
      _ = (p.a * Real.exp (p.a * s)) *
            intervalFullSemigroupOperator s f₀ y := by ring
  have hsource_lo : ∀ s, 0 < s → s < t → ∀ y ∈ Set.Icc (0:ℝ) 1,
      (-(Ke * Real.exp (p.a * s))) *
        intervalFullSemigroupOperator s f₀ y ≤ r s y := by
    intro s hs hst y hy
    have hsT : s ≤ T := le_trans hst.le htT
    simp only [hr_def, if_pos (And.intro hs hsT)]
    have hz_nn : 0 ≤ w s ⟨y, hy⟩ := hcone_lo s hs hsT ⟨y, hy⟩
    have hz_hi : w s ⟨y, hy⟩ ≤ Real.exp (p.a * s) *
        intervalFullSemigroupOperator s f₀ y := hcone_hi s hs hsT ⟨y, hy⟩
    have hz_bdd : w s ⟨y, hy⟩ ≤ Mw := by
      have := hw_bdd s hs hsT ⟨y, hy⟩
      exact (abs_le.mp this).2
    have hlift_eq : logisticLifted p (w s) y
        = w s ⟨y, hy⟩ * (p.a - p.b * (w s ⟨y, hy⟩) ^ p.α) := by
      simp [logisticLifted, ShenWork.IntervalDomainExistence.intervalLogisticSource,
        intervalDomainLift, hy]
    rw [hlift_eq]
    -- L(z) ≥ −b·z^α·z ≥ −b·Mw^α·z ≥ −Ke·z ≥ −Ke·e^{as}·S(s)f₀(y).
    have hpow_le : (w s ⟨y, hy⟩) ^ p.α ≤ Mw ^ p.α :=
      Real.rpow_le_rpow hz_nn hz_bdd p.hα.le
    have h1 : -(Ke * w s ⟨y, hy⟩)
        ≤ w s ⟨y, hy⟩ * (p.a - p.b * (w s ⟨y, hy⟩) ^ p.α) := by
      have hb_pow_le : p.b * (w s ⟨y, hy⟩) ^ p.α ≤ Ke :=
        le_trans (mul_le_mul_of_nonneg_left hpow_le p.hb) hKe_ge
      have haz : 0 ≤ p.a * w s ⟨y, hy⟩ := mul_nonneg p.ha hz_nn
      nlinarith [mul_le_mul_of_nonneg_left hb_pow_le hz_nn]
    have h2 : -(Ke * (Real.exp (p.a * s) *
          intervalFullSemigroupOperator s f₀ y))
        ≤ -(Ke * w s ⟨y, hy⟩) := by
      have := mul_le_mul_of_nonneg_left hz_hi hKe_nn
      linarith
    calc (-(Ke * Real.exp (p.a * s))) *
          intervalFullSemigroupOperator s f₀ y
        = -(Ke * (Real.exp (p.a * s) *
            intervalFullSemigroupOperator s f₀ y)) := by ring
      _ ≤ -(Ke * w s ⟨y, hy⟩) := h2
      _ ≤ w s ⟨y, hy⟩ * (p.a - p.b * (w s ⟨y, hy⟩) ^ p.α) := h1
  -- Operator-level pinch for 0 < s < t (mono + composition collapse).
  have hop_hi : ∀ s, 0 < s → s < t →
      intervalFullSemigroupOperator (t - s) (r s) x.1
        ≤ (p.a * Real.exp (p.a * s)) *
          intervalFullSemigroupOperator t f₀ x.1 := by
    intro s hs hst
    have hts : 0 < t - s := sub_pos.mpr hst
    have hg_cont : Continuous (fun y => (p.a * Real.exp (p.a * s)) *
        intervalFullSemigroupOperator s f₀ y) :=
      Continuous.mul continuous_const (hSf₀_cont hs)
    have hg_meas : AEStronglyMeasurable
        (fun y => (p.a * Real.exp (p.a * s)) *
          intervalFullSemigroupOperator s f₀ y) (intervalMeasure 1) :=
      hg_cont.aestronglyMeasurable
    have hg_bdd : ∀ y, |(p.a * Real.exp (p.a * s)) *
        intervalFullSemigroupOperator s f₀ y|
        ≤ |p.a * Real.exp (p.a * s)| * Mf₀ := fun y => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hSf₀_bdd hs y) (abs_nonneg _)
    have hcmp := intervalFullSemigroupOperator_mono_of_le_on_Icc
      (g := fun y => (p.a * Real.exp (p.a * s)) *
        intervalFullSemigroupOperator s f₀ y)
      hts (hr_slice_meas s) hg_meas (hr_bdd s) hg_bdd
      (hsource_hi s hs hst) x.1
    calc intervalFullSemigroupOperator (t - s) (r s) x.1
        ≤ intervalFullSemigroupOperator (t - s)
            (fun y => (p.a * Real.exp (p.a * s)) *
              intervalFullSemigroupOperator s f₀ y) x.1 := hcmp
      _ = (p.a * Real.exp (p.a * s)) *
            intervalFullSemigroupOperator t f₀ x.1 :=
          intervalFullSemigroupOperator_comp_const_mul hs hst hf₀_cont hMc
            (p.a * Real.exp (p.a * s)) x.2
  have hop_lo : ∀ s, 0 < s → s < t →
      (-(Ke * Real.exp (p.a * s))) *
          intervalFullSemigroupOperator t f₀ x.1
        ≤ intervalFullSemigroupOperator (t - s) (r s) x.1 := by
    intro s hs hst
    have hts : 0 < t - s := sub_pos.mpr hst
    have hg_cont : Continuous (fun y => (-(Ke * Real.exp (p.a * s))) *
        intervalFullSemigroupOperator s f₀ y) :=
      Continuous.mul continuous_const (hSf₀_cont hs)
    have hg_meas : AEStronglyMeasurable
        (fun y => (-(Ke * Real.exp (p.a * s))) *
          intervalFullSemigroupOperator s f₀ y) (intervalMeasure 1) :=
      hg_cont.aestronglyMeasurable
    have hg_bdd : ∀ y, |(-(Ke * Real.exp (p.a * s))) *
        intervalFullSemigroupOperator s f₀ y|
        ≤ |(-(Ke * Real.exp (p.a * s)))| * Mf₀ := fun y => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hSf₀_bdd hs y) (abs_nonneg _)
    have hcmp := intervalFullSemigroupOperator_mono_of_le_on_Icc
      (f := fun y => (-(Ke * Real.exp (p.a * s))) *
        intervalFullSemigroupOperator s f₀ y)
      hts hg_meas (hr_slice_meas s) hg_bdd (hr_bdd s)
      (hsource_lo s hs hst) x.1
    calc (-(Ke * Real.exp (p.a * s))) *
          intervalFullSemigroupOperator t f₀ x.1
        = intervalFullSemigroupOperator (t - s)
            (fun y => (-(Ke * Real.exp (p.a * s))) *
              intervalFullSemigroupOperator s f₀ y) x.1 :=
          (intervalFullSemigroupOperator_comp_const_mul hs hst hf₀_cont hMc
            (-(Ke * Real.exp (p.a * s))) x.2).symm
      _ ≤ intervalFullSemigroupOperator (t - s) (r s) x.1 := hcmp
  -- Endpoint-avoiding a.e. filters.
  have hne0t : ∀ᵐ s : ℝ ∂volume, s ≠ 0 ∧ s ≠ t := by
    have h0 : ∀ᵐ s : ℝ ∂volume, s ≠ 0 := by
      rw [ae_iff]
      simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
    have h1 : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
      rw [ae_iff]
      simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
    filter_upwards [h0, h1] with s hs0 hst
    exact ⟨hs0, hst⟩
  -- Integrate the pinch.
  have hint_hi : IntervalIntegrable
      (fun s => (p.a * Real.exp (p.a * s)) *
        intervalFullSemigroupOperator t f₀ x.1) volume 0 t :=
    (Continuous.intervalIntegrable (by fun_prop) 0 t)
  have hint_lo : IntervalIntegrable
      (fun s => (-(Ke * Real.exp (p.a * s))) *
        intervalFullSemigroupOperator t f₀ x.1) volume 0 t :=
    (Continuous.intervalIntegrable (by fun_prop) 0 t)
  have hV_hi : (∫ s in (0:ℝ)..t,
        intervalFullSemigroupOperator (t - s) (r s) x.1)
      ≤ ∫ s in (0:ℝ)..t, (p.a * Real.exp (p.a * s)) *
          intervalFullSemigroupOperator t f₀ x.1 := by
    apply intervalIntegral.integral_mono_ae_restrict ht.le hint_V hint_hi
    refine (ae_restrict_iff' measurableSet_Icc).mpr ?_
    filter_upwards [hne0t] with s hsne hsI
    have hs0 : 0 < s := lt_of_le_of_ne hsI.1 (Ne.symm hsne.1)
    have hst : s < t := lt_of_le_of_ne hsI.2 hsne.2
    exact hop_hi s hs0 hst
  have hV_lo : (∫ s in (0:ℝ)..t, (-(Ke * Real.exp (p.a * s))) *
        intervalFullSemigroupOperator t f₀ x.1)
      ≤ ∫ s in (0:ℝ)..t,
          intervalFullSemigroupOperator (t - s) (r s) x.1 := by
    apply intervalIntegral.integral_mono_ae_restrict ht.le hint_lo hint_V
    refine (ae_restrict_iff' measurableSet_Icc).mpr ?_
    filter_upwards [hne0t] with s hsne hsI
    have hs0 : 0 < s := lt_of_le_of_ne hsI.1 (Ne.symm hsne.1)
    have hst : s < t := lt_of_le_of_ne hsI.2 hsne.2
    exact hop_lo s hs0 hst
  -- Evaluate the envelope integrals.
  have heval_hi : (∫ s in (0:ℝ)..t, (p.a * Real.exp (p.a * s)) *
        intervalFullSemigroupOperator t f₀ x.1)
      = (p.a * envelopeIntegral p.a t) *
        intervalFullSemigroupOperator t f₀ x.1 := by
    rw [show (fun s => (p.a * Real.exp (p.a * s)) *
        intervalFullSemigroupOperator t f₀ x.1)
      = fun s => (Real.exp (p.a * s)) *
          (p.a * intervalFullSemigroupOperator t f₀ x.1) from
      funext fun s => by ring]
    rw [intervalIntegral.integral_mul_const, envelopeIntegral]
    ring
  have heval_lo : (∫ s in (0:ℝ)..t, (-(Ke * Real.exp (p.a * s))) *
        intervalFullSemigroupOperator t f₀ x.1)
      = -((Ke * envelopeIntegral p.a t) *
        intervalFullSemigroupOperator t f₀ x.1) := by
    rw [show (fun s => (-(Ke * Real.exp (p.a * s))) *
        intervalFullSemigroupOperator t f₀ x.1)
      = fun s => (Real.exp (p.a * s)) *
          (-(Ke * intervalFullSemigroupOperator t f₀ x.1)) from
      funext fun s => by ring]
    rw [intervalIntegral.integral_mul_const, envelopeIntegral]
    ring
  -- Assemble.
  rw [hΦ_eq, hS_eq, hV_eq]
  constructor
  · have := hV_lo
    rw [heval_lo] at this
    nlinarith [this]
  · have := hV_hi
    rw [heval_hi] at this
    nlinarith [this]

end ShenWork.IntervalMildPicardCone
