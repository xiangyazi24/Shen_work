/-
  Q1 final assembly (χ₀ = 0): uniform-horizon Picard data with
  cone-derived strict positivity — hQuant's existence core with NO
  inf-threshold.

  The construction re-runs the Picard iteration at χ₀ = 0 (the flux
  term is identically zero, so only the value Duhamel survives) with a
  horizon `δ(p, M_in)` chosen datum-free from FOUR constraints:
  contraction `C_L·δ < 1`, ball `δ·C_L_val ≤ M/2`, `δ ≤ 1`, and the
  cone-smallness `Ke·I(δ) ≤ ½` (`I = envelopeIntegral p.a`).

  Positivity of the limit does NOT use `corrections < inf u₀`:
  the iterates stay in the exponential cone
  `0 ≤ uₙ ≤ e^{at}·S(t)f₀` (`cone_preserved`), every iterate `n ≥ 1`
  satisfies the lower output bound `(1 − Ke·I(t))·S(t)f₀ ≤ uₙ ≥ ½·S(t)f₀`,
  the bound passes to the pointwise limit, and `S(t)f₀ > 0` everywhere
  by the kernel strict positivity (`intervalFullSemigroupOperator_pos`)
  — valid for data that are merely nonnegative and positive SOMEWHERE
  (in particular for all PIDs, which may vanish on the boundary).

  Output: `coneGradientMildSolutionData_exists` — for χ₀ = 0 and every
  continuous nonnegative datum bounded by `M_in` and positive somewhere,
  a packaged `GradientMildSolutionData` with `D.T = δ(p, M_in)`.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalMildPicardCone

open MeasureTheory Set Filter
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalFullKernelSpectralClean
open ShenWork.IntervalGradientDuhamelMap
open ShenWork.IntervalMildPicard
open ShenWork.IntervalMildPicardThreshold
open ShenWork.IntervalMildPicardCone
open ShenWork.IntervalSemigroupComposition
open ShenWork.IntervalSemigroupConeAtoms

noncomputable section

namespace ShenWork.IntervalMildPicardConeData

/-! ## Envelope integral calculus -/

theorem envelopeIntegral_nonneg (a : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ envelopeIntegral a t := by
  rw [envelopeIntegral]
  exact intervalIntegral.integral_nonneg ht (fun s _ => (Real.exp_pos _).le)

theorem envelopeIntegral_mono (a : ℝ) {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    envelopeIntegral a t ≤ envelopeIntegral a T := by
  have hint1 : IntervalIntegrable (fun s => Real.exp (a * s)) volume 0 t :=
    Continuous.intervalIntegrable (by fun_prop) 0 t
  have hint2 : IntervalIntegrable (fun s => Real.exp (a * s)) volume t T :=
    Continuous.intervalIntegrable (by fun_prop) t T
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
  have htail : 0 ≤ ∫ s in t..T, Real.exp (a * s) :=
    intervalIntegral.integral_nonneg htT (fun s _ => (Real.exp_pos _).le)
  rw [envelopeIntegral, envelopeIntegral]
  linarith [hsplit]

theorem envelopeIntegral_le (a : ℝ) {t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    envelopeIntegral a t ≤ t * Real.exp (a * t) := by
  rw [envelopeIntegral]
  calc (∫ s in (0:ℝ)..t, Real.exp (a * s))
      ≤ ∫ _s in (0:ℝ)..t, Real.exp (a * t) := by
        apply intervalIntegral.integral_mono_on ht
          (Continuous.intervalIntegrable (by fun_prop) 0 t)
          intervalIntegrable_const
        intro s hs
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2 ha)
    _ = t * Real.exp (a * t) := by
        rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]

/-- FTC evaluation: `a·I(t) = e^{at} − 1`. -/
theorem mul_envelopeIntegral_eq (a t : ℝ) :
    a * envelopeIntegral a t = Real.exp (a * t) - 1 := by
  have hderiv : ∀ s ∈ Set.uIcc (0:ℝ) t,
      HasDerivAt (fun r => Real.exp (a * r)) (a * Real.exp (a * s)) s := by
    intro s _hs
    have h1 : HasDerivAt (fun r : ℝ => a * r) a s := by
      simpa using (hasDerivAt_id s).const_mul a
    have h2 := (Real.hasDerivAt_exp (a * s)).comp s h1
    simpa [mul_comm] using h2
  have hint : IntervalIntegrable (fun s => a * Real.exp (a * s)) volume 0 t :=
    Continuous.intervalIntegrable (by fun_prop) 0 t
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [envelopeIntegral, ← intervalIntegral.integral_const_mul]
  simpa using hftc

theorem one_add_mul_envelopeIntegral (a t : ℝ) :
    1 + a * envelopeIntegral a t = Real.exp (a * t) := by
  rw [mul_envelopeIntegral_eq]; ring

/-! ## The χ₀ = 0 uniform-horizon construction -/

set_option maxHeartbeats 3200000 in
/-- **Cone-uniform Picard data (χ₀ = 0), strengthened output.**  Same one
horizon `δ = δ(p, M_in) > 0` and same packaged `GradientMildSolutionData D`
as `coneGradientMildSolutionData_exists`, but ALSO returns the cone
construction's internal iterate slice-continuity bundle
`∀ n, HasContinuousSlices D.T (picardIter p u₀ n)` (the in-proof
`hcont_iterates`).  This is exactly the `hcont_iter` input that the
`Hres` producer `picardIterateResidualData_of_cone` needs — and which a
bare `GradientMildSolutionData` does not expose.

ADDITIVE: the plain `coneGradientMildSolutionData_exists` is re-derived from
this in one line below, so no consumer of the old shape changes.

NOTE (cross-file ask resolution).  The `Hres` producer's `hME`
(`MildExistenceData p u₀`) is NOT returned here, and is in fact NOT
cone-constructible: `MildExistenceData.hmapsTo_nn` / `hmapsTo_pos` are
universally quantified over ALL bounded-nonneg-continuous trajectories `w`,
and are FALSE in the threshold-free cone regime for boundary-vanishing data
(e.g. `w ≡ M` gives `L(w) = M(a − bM^α) < 0`, whose Duhamel correction
dominates `S(t)u₀(x)` near a boundary point where `u₀ → 0`; the strict
positivity of `S(t)u₀` is non-uniform in `t` and vanishes as `t → 0⁺`).
The threshold construction (`thresholdMildExistenceData_exists`) only proves
those fields under a uniform lower threshold `c ≤ u₀`, exactly what the cone
route drops.  Every OTHER `MildExistenceData` field IS cone-constructible
(verified): `hbase_ball/hbase_nonneg/hbase_cont` from the base semigroup,
`hmapsTo/hcont_preserved/hmeas_preserved` from the inline `*_proof` lemmas,
`hcontr` from `hcontr_proof` (with `K = C_L·T₀`), `hbase_diff/hbase_meas`
from the geometric/measurability data. -/
theorem coneGradientMildSolutionData_exists_with_data (p : CM2Params) (hχ : p.χ₀ = 0)
    {M_in : ℝ} (hM_in : 0 < M_in) (hα_ge : 1 ≤ p.α) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ u₀ : intervalDomainPoint → ℝ,
        Continuous u₀ →
        (∀ x, |u₀ x| ≤ M_in) →
        (∀ x, 0 ≤ u₀ x) →
        (∃ x₀, 0 < u₀ x₀) →
        ∃ D : GradientMildSolutionData p u₀,
          D.T = δ ∧ D.u = picardLimit p u₀ δ ∧
          (∀ n, HasContinuousSlices D.T (picardIter p u₀ n)) := by
  set M := 2 * max M_in 1 with hMdef
  have hM : 0 < M := by positivity
  have hM_ge_2 : (2 : ℝ) ≤ M := by
    have : (1 : ℝ) ≤ max M_in 1 := le_max_right M_in 1
    simp only [hMdef]; linarith
  -- Datum-free constants.
  obtain ⟨C_L, hC_L_pos, hC_L_lip⟩ :=
    ShenWork.IntervalLogisticLipschitz.intervalLogisticReaction_lipschitz_on_bounded
      p hα_ge hM
  set C_L_val := M * (p.a + p.b * M ^ p.α) with hCLval_def
  have hC_L_val_nn : (0 : ℝ) ≤ C_L_val :=
    mul_nonneg hM.le (add_nonneg p.ha
      (mul_nonneg p.hb (Real.rpow_nonneg hM.le _)))
  set Ke := p.b * M ^ p.α with hKe_def
  have hKe_nn : 0 ≤ Ke := mul_nonneg p.hb (Real.rpow_nonneg hM.le _)
  -- The horizon: δ = 1/(2·(C_L + C_L_val + Ke·e^a + 1)).
  set Dn := C_L + C_L_val + Ke * Real.exp p.a + 1 with hDn_def
  have hDn_pos : 0 < Dn := by
    have h1 : 0 ≤ Ke * Real.exp p.a := mul_nonneg hKe_nn (Real.exp_pos _).le
    simp only [hDn_def]; linarith [hC_L_pos, hC_L_val_nn]
  set T₀ := 1 / (2 * Dn) with hT₀_def
  have hT₀ : 0 < T₀ := by positivity
  have hT₀_le_half : T₀ ≤ 1 / 2 := by
    rw [hT₀_def]
    have hDn_ge_1 : 1 ≤ Dn := by
      have h1 : 0 ≤ Ke * Real.exp p.a := mul_nonneg hKe_nn (Real.exp_pos _).le
      simp only [hDn_def]; linarith [hC_L_pos.le, hC_L_val_nn]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hT₀_le_one : T₀ ≤ 1 := le_trans hT₀_le_half (by norm_num)
  have hK_lt : C_L * T₀ < 1 := by
    rw [hT₀_def, mul_one_div, div_lt_one (by linarith)]
    have h1 : 0 ≤ Ke * Real.exp p.a := mul_nonneg hKe_nn (Real.exp_pos _).le
    simp only [hDn_def]; linarith [hC_L_val_nn, hC_L_pos]
  have hK_nn : 0 ≤ C_L * T₀ := mul_nonneg hC_L_pos.le hT₀.le
  have hval_small : T₀ * C_L_val ≤ M / 2 := by
    have h1 : T₀ * C_L_val ≤ (1 / (2 * Dn)) * Dn := by
      rw [hT₀_def]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have h2 : 0 ≤ Ke * Real.exp p.a := mul_nonneg hKe_nn (Real.exp_pos _).le
      simp only [hDn_def]; linarith [hC_L_pos.le]
    have h2 : (1 / (2 * Dn)) * Dn = 1 / 2 := by field_simp
    rw [h2] at h1
    linarith
  have hcone_small : Ke * envelopeIntegral p.a T₀ ≤ 1 / 2 := by
    have hI_le : envelopeIntegral p.a T₀ ≤ T₀ * Real.exp p.a := by
      calc envelopeIntegral p.a T₀ ≤ T₀ * Real.exp (p.a * T₀) :=
            envelopeIntegral_le p.a p.ha hT₀.le
        _ ≤ T₀ * Real.exp p.a := by
            apply mul_le_mul_of_nonneg_left _ hT₀.le
            exact Real.exp_le_exp.mpr (by nlinarith [p.ha])
    have h1 : Ke * envelopeIntegral p.a T₀ ≤ Ke * (T₀ * Real.exp p.a) :=
      mul_le_mul_of_nonneg_left hI_le hKe_nn
    have h2 : Ke * (T₀ * Real.exp p.a) ≤ 1 / 2 := by
      have h3 : Ke * Real.exp p.a ≤ Dn := by
        simp only [hDn_def]; linarith [hC_L_pos.le, hC_L_val_nn]
      calc Ke * (T₀ * Real.exp p.a) = (Ke * Real.exp p.a) * T₀ := by ring
        _ ≤ Dn * T₀ := mul_le_mul_of_nonneg_right h3 hT₀.le
        _ = Dn * (1 / (2 * Dn)) := by rw [hT₀_def]
        _ = 1 / 2 := by field_simp
    linarith
  -- The datum-quantified part.
  refine ⟨T₀, hT₀, ?_⟩
  intro u₀ hu₀_cont hu₀_bound hu₀_nonneg hu₀_pos
  have hB_le : ∀ x, |u₀ x| ≤ M / 2 := by
    intro x
    calc |u₀ x| ≤ M_in := hu₀_bound x
      _ ≤ max M_in 1 := le_max_left M_in 1
      _ = M / 2 := by rw [hMdef]; ring
  have hbase_ball : ∀ T : ℝ, ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |picardIter p u₀ 0 t x| ≤ M := by
    intro T t ht _htT x
    exact ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound ht
      (by linarith : (0:ℝ) ≤ M)
      (fun y => by
        calc |intervalDomainLift u₀ y|
            ≤ M / 2 := by
              unfold intervalDomainLift
              split_ifs with hy
              · exact hB_le ⟨y, hy⟩
              · simp; linarith
            _ ≤ M := by linarith) x.1
  -- Step 1b: hbase_nonneg — S(t)u₀ ≥ 0 by semigroup positivity
  have hLift_nonneg : ∀ y, 0 ≤ intervalDomainLift u₀ y := by
    intro y; unfold intervalDomainLift; split_ifs with hy
    · exact hu₀_nonneg ⟨y, hy⟩
    · simp
  have hbase_nonneg : ∀ T : ℝ, ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      0 ≤ picardIter p u₀ 0 t x := by
    intro T t ht _htT x
    exact ShenWork.IntervalResolverPositivity.intervalFullSemigroupOperator_nonneg ht
      hLift_nonneg x.1
  -- The core mapsTo inequality:
  -- |χ₀|·C_grad·2√T₀·C_Q_unif + T₀·C_L_val ≤ A·√T₀ + B·T₀ < 1 ≤ M/2
  have hLift_le : ∀ y, |intervalDomainLift u₀ y| ≤ M / 2 := by
    intro y; unfold intervalDomainLift; split_ifs with hy
    · exact hB_le ⟨y, hy⟩
    · simp; linarith
  have hLift_le_M : ∀ y, |intervalDomainLift u₀ y| ≤ M :=
    fun y => (hLift_le y).trans (by linarith)
  have hLift_meas :=
    ShenWork.IntervalDuhamelIntegrability.intervalDomainLift_aestronglyMeasurable_of_continuous
      hu₀_cont
  -- Helper: semigroup of u₀ continuous (for subtype)
  have hSg_cont : ∀ t, 0 < t → Continuous
      (fun x : intervalDomainPoint =>
        intervalFullSemigroupOperator t
          (intervalDomainLift u₀) x.1) := by
    intro t ht
    exact (ShenWork.IntervalDuhamelIntegrability.intervalFullSemigroupOperator_continuous_of_bounded
        ht (by linarith : (0:ℝ) ≤ M) hLift_le_M
        hLift_meas).comp continuous_subtype_val
  -- Extract hmapsTo proof so it can be reused in hbase_diff
  -- The continuous extension f₀ and its facts.
  set f₀ : ℝ → ℝ := fun y => u₀ (unitClip y) with hf₀_def
  have hf₀_cont : Continuous f₀ := hu₀_cont.comp unitClip_continuous
  have hf₀_bdd : ∀ y, |f₀ y| ≤ M_in := fun y => hu₀_bound _
  have hf₀_nonneg : ∀ y, 0 ≤ f₀ y := fun y => hu₀_nonneg _
  have hf₀_eq : ∀ y ∈ Set.Icc (0:ℝ) 1, intervalDomainLift u₀ y = f₀ y := by
    intro y hy
    simp only [intervalDomainLift, dif_pos hy, hf₀_def, unitClip_of_mem hy]
  have hMc : ∀ n, |cosineCoeffs f₀ n| ≤ 2 * M_in :=
    ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
      hf₀_cont.continuousOn hM_in.le (fun y _ => hf₀_bdd y)
  -- Pointwise semigroup substitution S(t)(lift u₀) = S(t)f₀.
  have hS_eq : ∀ t (x : intervalDomainPoint),
      intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
        = intervalFullSemigroupOperator t f₀ x.1 := by
    intro t x
    unfold intervalFullSemigroupOperator
    apply integral_congr_ae
    have hae : ∀ᵐ y ∂(intervalMeasure 1), y ∈ Set.Icc (0:ℝ) 1 := by
      simp only [ShenWork.IntervalDomain.intervalMeasure,
        ShenWork.IntervalDomain.intervalSet]
      exact (ae_restrict_iff' measurableSet_Icc).mpr
        (Filter.Eventually.of_forall fun y hy => hy)
    filter_upwards [hae] with y hy
    rw [hf₀_eq y hy]
  -- S(t)f₀ is nonnegative everywhere.
  have hSf₀_nonneg : ∀ {t : ℝ}, 0 < t → ∀ y : ℝ,
      0 ≤ intervalFullSemigroupOperator t f₀ y := fun {t} ht y =>
    ShenWork.IntervalResolverPositivity.intervalFullSemigroupOperator_nonneg
      ht hf₀_nonneg y
  -- The χ₀ = 0 two-term form of the mild map.
  have hΦ_eq : ∀ (w : ℝ → intervalDomainPoint → ℝ) t (x : intervalDomainPoint),
      intervalGradientDuhamelMap p u₀ w t x
        = intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
          + ∫ s in (0:ℝ)..t, intervalFullSemigroupOperator (t - s)
              (logisticLifted p (w s)) x.1 := by
    intro w t x
    unfold intervalGradientDuhamelMap
    rw [hχ]
    ring
  -- Ball preservation (value Duhamel only).
  have hmapsTo_proof : ∀ (w : ℝ → intervalDomainPoint → ℝ),
      (∀ t, 0 < t → t ≤ T₀ → ∀ x, |w t x| ≤ M) →
      ∀ t, 0 < t → t ≤ T₀ → ∀ x : intervalDomainPoint,
        |intervalGradientDuhamelMap p u₀ w t x| ≤ M := by
    intro w hw_bound t ht htT x
    rw [hΦ_eq w t x]
    have hterm1 :
        |intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1| ≤ M / 2 :=
      ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
        ht (by linarith : (0:ℝ) ≤ M / 2) hLift_le x.1
    set r_val : ℝ → ℝ → ℝ := fun s y =>
      if 0 < s ∧ s ≤ T₀ then logisticLifted p (w s) y else 0 with hr_val_def
    have hr_val_bound : ∀ s y, |r_val s y| ≤ C_L_val := by
      intro s y; simp only [hr_val_def]
      split_ifs with h
      · exact ShenWork.IntervalDomainExistence.intervalLogisticSource_lift_abs_bound
          p hM (fun z => hw_bound s h.1 h.2 z) y
      · simp; exact hC_L_val_nn
    have hval_eq : (∫ s in (0:ℝ)..t,
          intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x.1)
        = ∫ s in (0:ℝ)..t,
          intervalFullSemigroupOperator (t - s) (r_val s) x.1 := by
      apply intervalIntegral.integral_congr_ae
      apply Filter.Eventually.of_forall
      intro s hs
      rw [Set.uIoc_of_le ht.le] at hs
      simp only [hr_val_def, if_pos (And.intro hs.1 (hs.2.trans htT))]
    have hterm3 : |(∫ s in (0:ℝ)..t,
        intervalFullSemigroupOperator (t - s)
          (logisticLifted p (w s)) x.1)| ≤ T₀ * C_L_val := by
      rw [hval_eq]
      exact ShenWork.IntervalDuhamelIntegrability.valueDuhamel_sup_bound_universal
        ht htT hC_L_val_nn hr_val_bound x.1
    have habs := abs_add_le
      (intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1)
      (∫ s in (0:ℝ)..t, intervalFullSemigroupOperator (t - s)
        (logisticLifted p (w s)) x.1)
    linarith
  -- Contraction (value Duhamel only; the flux term vanishes at χ₀ = 0).
  have hcontr_proof : ∀ (u w : ℝ → intervalDomainPoint → ℝ) (d : ℝ),
      (∀ t, 0 < t → t ≤ T₀ → ∀ x, |u t x| ≤ M) →
      (∀ t, 0 < t → t ≤ T₀ → ∀ x, 0 ≤ u t x) →
      (∀ t, 0 < t → t ≤ T₀ → ∀ x, |w t x| ≤ M) →
      (∀ t, 0 < t → t ≤ T₀ → ∀ x, 0 ≤ w t x) →
      HasContinuousSlices T₀ u →
      HasContinuousSlices T₀ w →
      HasJointMeasurability u →
      HasJointMeasurability w →
      (∀ t, 0 < t → t ≤ T₀ → ∀ x, |u t x - w t x| ≤ d) →
      ∀ t, 0 < t → t ≤ T₀ → ∀ x : intervalDomainPoint,
        |intervalGradientDuhamelMap p u₀ u t x
          - intervalGradientDuhamelMap p u₀ w t x| ≤ (C_L * T₀) * d := by
    intro u w d hu hu_nn hw hw_nn huc hwc hum hwm hd t ht htT x
    rw [hΦ_eq u t x, hΦ_eq w t x]
    set Vu := ∫ s in (0:ℝ)..t,
      intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x.1
    set Vw := ∫ s in (0:ℝ)..t,
      intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x.1
    have hcancel :
        (intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1 + Vu)
        - (intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1 + Vw)
        = Vu - Vw := by ring
    rw [hcancel]
    have hd_nn : 0 ≤ d := by
      have := hd t ht htT x
      exact le_trans (abs_nonneg _) this
    have hV : |Vu - Vw| ≤ T₀ * (C_L * d) := by
      -- Extended logistic sources (= original on (0,T₀], = 0 otherwise)
      set r_u : ℝ → ℝ → ℝ := fun s y =>
        if 0 < s ∧ s ≤ T₀ then logisticLifted p (u s) y else 0
      set r_w : ℝ → ℝ → ℝ := fun s y =>
        if 0 < s ∧ s ≤ T₀ then logisticLifted p (w s) y else 0
      -- Integral congr: Vu = ∫ with r_u
      have hVu_eq : Vu = ∫ s in (0:ℝ)..t,
          intervalFullSemigroupOperator (t - s) (r_u s) x.1 := by
        apply intervalIntegral.integral_congr_ae; apply Eventually.of_forall
        intro s hs; rw [Set.uIoc_of_le ht.le] at hs
        simp only [r_u, if_pos (And.intro hs.1 (hs.2.trans htT))]
      have hVw_eq : Vw = ∫ s in (0:ℝ)..t,
          intervalFullSemigroupOperator (t - s) (r_w s) x.1 := by
        apply intervalIntegral.integral_congr_ae; apply Eventually.of_forall
        intro s hs; rw [Set.uIoc_of_le ht.le] at hs
        simp only [r_w, if_pos (And.intro hs.1 (hs.2.trans htT))]
      rw [hVu_eq, hVw_eq]
      -- Source diff bound: |r_u s y - r_w s y| ≤ C_L · d
      have hr_diff_bound : ∀ s y, |r_u s y - r_w s y| ≤ C_L * d := by
        intro s y; simp only [r_u, r_w]
        split_ifs with h
        · -- s ∈ (0, T₀]: logistic Lipschitz
          unfold logisticLifted intervalDomainLift
            ShenWork.IntervalDomainExistence.intervalLogisticSource
          by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
          · -- y ∈ [0,1]: use hC_L_lip + hd
            simp only [dif_pos hy]
            have hu_s := hu s h.1 h.2 ⟨y, hy⟩
            have hw_s := hw s h.1 h.2 ⟨y, hy⟩
            have hd_s := hd s h.1 h.2 ⟨y, hy⟩
            calc |u s ⟨y, hy⟩ * (p.a - p.b * (u s ⟨y, hy⟩) ^ p.α)
                    - w s ⟨y, hy⟩ * (p.a - p.b * (w s ⟨y, hy⟩) ^ p.α)|
                ≤ C_L * |u s ⟨y, hy⟩ - w s ⟨y, hy⟩| :=
                  hC_L_lip _ _ hu_s hw_s
              _ ≤ C_L * d := mul_le_mul_of_nonneg_left hd_s hC_L_pos.le
          · -- y ∉ [0,1]: both lifts = 0
            simp only [dif_neg hy, sub_self, abs_zero]
            exact mul_nonneg hC_L_pos.le hd_nn
        · -- s ∉ (0, T₀]: 0 - 0 = 0
          simp; exact mul_nonneg hC_L_pos.le hd_nn
      -- Source spatial integrability (logistic of continuous bounded, or zero)
      have hr_u_int : ∀ s, Integrable (r_u s) (ShenWork.IntervalDomain.intervalMeasure 1) := by
        intro s; simp only [r_u]; split_ifs with h
        · exact ShenWork.IntervalDuhamelIntegrability.logisticLifted_integrable_of_continuous
            p (hu s h.1 h.2) hM.le (huc s h.1 h.2)
        · exact integrable_zero ℝ ℝ (ShenWork.IntervalDomain.intervalMeasure 1)
      have hr_w_int : ∀ s, Integrable (r_w s) (ShenWork.IntervalDomain.intervalMeasure 1) := by
        intro s; simp only [r_w]; split_ifs with h
        · exact ShenWork.IntervalDuhamelIntegrability.logisticLifted_integrable_of_continuous
            p (hw s h.1 h.2) hM.le (hwc s h.1 h.2)
        · exact integrable_zero ℝ ℝ (ShenWork.IntervalDomain.intervalMeasure 1)
      -- Source sup bounds
      have hr_u_bdd : ∀ s y, |r_u s y| ≤ C_L_val := by
        intro s y; simp only [r_u]; split_ifs with h
        · exact ShenWork.IntervalDomainExistence.intervalLogisticSource_lift_abs_bound
            p hM (hu s h.1 h.2) y
        · simp; exact hC_L_val_nn
      have hr_w_bdd : ∀ s y, |r_w s y| ≤ C_L_val := by
        intro s y; simp only [r_w]; split_ifs with h
        · exact ShenWork.IntervalDomainExistence.intervalLogisticSource_lift_abs_bound
            p hM (hw s h.1 h.2) y
        · simp; exact hC_L_val_nn
      have hCLd_nn : 0 ≤ C_L * d := mul_nonneg hC_L_pos.le hd_nn
      by_cases hint_u : IntervalIntegrable
          (fun s => intervalFullSemigroupOperator (t - s) (r_u s) x.1) volume 0 t
      · by_cases hint_w : IntervalIntegrable
            (fun s => intervalFullSemigroupOperator (t - s) (r_w s) x.1) volume 0 t
        · -- Both integrable: combine + per-slice bound + integrate
          rw [← intervalIntegral.integral_sub hint_u hint_w]
          have hptw : ∀ᵐ s ∂(volume.restrict (Set.Icc 0 t)),
              |intervalFullSemigroupOperator (t - s) (r_u s) x.1
                - intervalFullSemigroupOperator (t - s) (r_w s) x.1| ≤ C_L * d := by
            have hne : ∀ᵐ s ∂volume, s ≠ t := by
              rw [ae_iff]; simp only [not_not, Set.setOf_eq_eq_singleton]
              exact Real.volume_singleton
            refine (ae_restrict_iff' measurableSet_Icc).mpr ?_
            filter_upwards [hne] with s hs hs_mem
            have hst : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs_mem.2 hs)
            exact ShenWork.IntervalDuhamelIntegrability.intervalFullSemigroupOperator_diff_Linfty_of_integrable
              hst (hr_u_int s) (hr_w_int s) hC_L_val_nn (hr_u_bdd s) hC_L_val_nn
              (hr_w_bdd s) hCLd_nn (hr_diff_bound s) x.1
          calc |∫ s in (0:ℝ)..t, (intervalFullSemigroupOperator (t - s) (r_u s) x.1
                  - intervalFullSemigroupOperator (t - s) (r_w s) x.1)|
              ≤ ∫ s in (0:ℝ)..t, |intervalFullSemigroupOperator (t - s) (r_u s) x.1
                  - intervalFullSemigroupOperator (t - s) (r_w s) x.1| :=
                intervalIntegral.abs_integral_le_integral_abs ht.le
            _ ≤ ∫ s in (0:ℝ)..t, (C_L * d) :=
                intervalIntegral.integral_mono_ae_restrict ht.le
                  (hint_u.sub hint_w).abs intervalIntegrable_const hptw
            _ = t * (C_L * d) := by
                rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
            _ ≤ T₀ * (C_L * d) := by gcongr
        · -- w not integrable: derive contradiction from joint measurability
          -- r_w s y = if 0 < s ∧ s ≤ T₀ then logisticLifted p (w s) y else 0
          -- Measurability follows from hwm : HasJointMeasurability w
          exfalso; exact hint_w
            (ShenWork.IntervalDuhamelIntegrability.valueDuhamel_intervalIntegrable_of_joint_measurable
              ht (by
                show Measurable (fun p : ℝ × ℝ => r_w p.1 p.2)
                simp only [r_w]
                exact logisticLifted_time_cutoff_measurable' hwm) hC_L_val_nn
              (hr_w_bdd) x.1)
      · exfalso; exact hint_u
          (ShenWork.IntervalDuhamelIntegrability.valueDuhamel_intervalIntegrable_of_joint_measurable
            ht (by
              show Measurable (fun p : ℝ × ℝ => r_u p.1 p.2)
              simp only [r_u]
              exact logisticLifted_time_cutoff_measurable' hum) hC_L_val_nn
            (hr_u_bdd) x.1)
    calc |Vu - Vw| ≤ T₀ * (C_L * d) := hV
      _ = (C_L * T₀) * d := by ring
  -- Slice continuity preservation (value Duhamel only).
  have hcont_preserved_proof : ∀ (w : ℝ → intervalDomainPoint → ℝ),
      (∀ t, 0 < t → t ≤ T₀ → ∀ x, |w t x| ≤ M) →
      HasJointMeasurability w →
      HasContinuousSlices T₀
        (fun t x => intervalGradientDuhamelMap p u₀ w t x) := by
    intro w hw_bound hwm t ht htT
    have hL_bound : ∀ s, 0 < s → s ≤ T₀ → ∀ y : ℝ,
        |logisticLifted p (w s) y| ≤ C_L_val := by
      intro s hs hsT y
      exact ShenWork.IntervalDomainExistence.intervalLogisticSource_lift_abs_bound p hM
        (fun x => hw_bound s hs hsT x) y
    have hL_meas : Measurable (fun q : ℝ × ℝ => logisticLifted p (w q.1) q.2) :=
      logisticLifted_joint_measurable' (p := p) (u := w) hwm
    have hL_slice_meas : ∀ s,
        AEStronglyMeasurable (logisticLifted p (w s)) (intervalMeasure 1) := by
      intro s
      have hm : Measurable (fun y : ℝ => logisticLifted p (w s) y) :=
        hL_meas.comp (measurable_const.prodMk measurable_id)
      exact hm.aestronglyMeasurable
    have hne_t : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
      rw [ae_iff]
      simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
    have hL_joint_semigroup :
        Measurable (fun r : (ℝ × ℝ) × ℝ =>
          intervalFullSemigroupOperator (r.1.1 - r.2)
            (logisticLifted p (w r.2)) r.1.2) :=
      intervalFullSemigroupOperator_s_param_joint_measurable'
        (F := fun s => logisticLifted p (w s))
        (by simpa [Function.uncurry] using hL_meas)
    have hVal_cont : Continuous (fun x : intervalDomainPoint =>
        ∫ s in (0 : ℝ)..t,
          intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x.1) := by
      refine intervalIntegral.continuous_of_dominated_interval
        (μ := volume)
        (F := fun x : intervalDomainPoint => fun s : ℝ =>
          intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x.1)
        (bound := fun _ : ℝ => C_L_val)
        ?hVal_meas ?hVal_bound intervalIntegrable_const ?hVal_slice_cont
      · intro x
        have hmap : Measurable (fun s : ℝ => (((t, x.1), s) : (ℝ × ℝ) × ℝ)) :=
          measurable_const.prodMk measurable_id
        have hm : Measurable (fun s : ℝ =>
            intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x.1) :=
          hL_joint_semigroup.comp hmap
        exact hm.aestronglyMeasurable
      · intro x
        filter_upwards [hne_t] with s hsne hsI
        rw [Set.uIoc_of_le ht.le] at hsI
        have hst : s < t := lt_of_le_of_ne hsI.2 hsne
        have hts : 0 < t - s := sub_pos.mpr hst
        rw [Real.norm_eq_abs]
        exact ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
          hts hC_L_val_nn (hL_bound s hsI.1 (hsI.2.trans htT)) x.1
      · filter_upwards [hne_t] with s hsne hsI
        rw [Set.uIoc_of_le ht.le] at hsI
        have hst : s < t := lt_of_le_of_ne hsI.2 hsne
        have hts : 0 < t - s := sub_pos.mpr hst
        have hLs_bound : ∀ y : ℝ, |logisticLifted p (w s) y| ≤ C_L_val :=
          hL_bound s hsI.1 (hsI.2.trans htT)
        have hcont_real : Continuous (fun x : ℝ =>
            intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x) :=
          ShenWork.IntervalDuhamelIntegrability.intervalFullSemigroupOperator_continuous_of_bounded
            (t := t - s) (f := logisticLifted p (w s)) (M := C_L_val)
            hts hC_L_val_nn hLs_bound (hL_slice_meas s)
        exact hcont_real.comp continuous_subtype_val
    have hslice_eq : (fun x : intervalDomainPoint =>
        intervalGradientDuhamelMap p u₀ w t x)
        = fun x : intervalDomainPoint =>
            intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
              + ∫ s in (0:ℝ)..t,
                  intervalFullSemigroupOperator (t - s)
                    (logisticLifted p (w s)) x.1 :=
      funext (hΦ_eq w t)
    show Continuous (fun x : intervalDomainPoint =>
      intervalGradientDuhamelMap p u₀ w t x)
    rw [hslice_eq]
    exact (hSg_cont t ht).add hVal_cont
  -- Joint measurability preservation (value Duhamel only).
  have hmeas_preserved_proof : ∀ w, HasJointMeasurability w →
      HasJointMeasurability
        (fun t x => intervalGradientDuhamelMap p u₀ w t x) := by
    intro w hum
    have hSg_meas : Measurable (fun q : ℝ × ℝ =>
        intervalFullSemigroupOperator q.1 (intervalDomainLift u₀) q.2) :=
      intervalFullSemigroupOperator_joint_measurable'
        (intervalDomainLift_measurable_of_continuous' hu₀_cont)
    have hL_meas :
        Measurable (Function.uncurry (fun s y => logisticLifted p (w s) y)) := by
      simpa [Function.uncurry] using logisticLifted_joint_measurable' hum
    have hVal_integrand : Measurable (fun r : (ℝ × ℝ) × ℝ =>
        intervalFullSemigroupOperator (r.1.1 - r.2)
          (logisticLifted p (w r.2)) r.1.2) :=
      intervalFullSemigroupOperator_s_param_joint_measurable' hL_meas
    have hVal : Measurable (fun q : ℝ × ℝ =>
        ∫ s in (0 : ℝ)..q.1,
          intervalFullSemigroupOperator (q.1 - s)
            (logisticLifted p (w s)) q.2) :=
      variable_interval_integral_measurable' hVal_integrand
    have hinside : Measurable (fun q : ℝ × ℝ =>
        intervalFullSemigroupOperator q.1 (intervalDomainLift u₀) q.2
          + ∫ s in (0 : ℝ)..q.1,
            intervalFullSemigroupOperator (q.1 - s)
              (logisticLifted p (w s)) q.2) :=
      hSg_meas.add hVal
    have hfield :
        (fun q : ℝ × ℝ =>
          intervalDomainLift
            (fun x : intervalDomainPoint => intervalGradientDuhamelMap p u₀ w q.1 x)
            q.2) =
          fun q : ℝ × ℝ =>
            if q.2 ∈ Set.Icc (0 : ℝ) 1 then
              intervalFullSemigroupOperator q.1 (intervalDomainLift u₀) q.2
                + ∫ s in (0 : ℝ)..q.1,
                  intervalFullSemigroupOperator (q.1 - s)
                    (logisticLifted p (w s)) q.2
            else 0 := by
      funext q
      by_cases hy : q.2 ∈ Set.Icc (0 : ℝ) 1
      · simp [intervalDomainLift, intervalGradientDuhamelMap, hy, hχ]
      · simp [intervalDomainLift, hy]
    change Measurable (fun q : ℝ × ℝ =>
      intervalDomainLift
        (fun x : intervalDomainPoint => intervalGradientDuhamelMap p u₀ w q.1 x)
        q.2)
    rw [hfield]
    exact Measurable.ite (measurableSet_Icc.preimage measurable_snd)
      hinside measurable_const
  -- ## The cone induction over the iterates.
  have hiter : ∀ n : ℕ,
      (∀ t, 0 < t → t ≤ T₀ → ∀ x, |picardIter p u₀ n t x| ≤ M) ∧
      (∀ t, 0 < t → t ≤ T₀ → ∀ x, 0 ≤ picardIter p u₀ n t x) ∧
      HasContinuousSlices T₀ (picardIter p u₀ n) ∧
      HasJointMeasurability (picardIter p u₀ n) ∧
      (∀ t, 0 < t → t ≤ T₀ → ∀ x : intervalDomainPoint,
        picardIter p u₀ n t x ≤ Real.exp (p.a * t) *
          intervalFullSemigroupOperator t f₀ x.1) := by
    intro n
    induction n with
    | zero =>
      have hzero_eq : ∀ t (x : intervalDomainPoint),
          picardIter p u₀ 0 t x
            = intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1 :=
        fun t x => rfl
      refine ⟨fun t ht htT x => hbase_ball T₀ t ht htT x,
              fun t ht htT x => hbase_nonneg T₀ t ht htT x,
              fun t ht _htT => hSg_cont t ht,
              ?_, ?_⟩
      · -- base measurability
        have hSg_meas : Measurable (fun q : ℝ × ℝ =>
            intervalFullSemigroupOperator q.1 (intervalDomainLift u₀) q.2) :=
          intervalFullSemigroupOperator_joint_measurable'
            (intervalDomainLift_measurable_of_continuous' hu₀_cont)
        have hfield :
            (fun q : ℝ × ℝ => intervalDomainLift (picardIter p u₀ 0 q.1) q.2) =
              fun q : ℝ × ℝ =>
                if q.2 ∈ Set.Icc (0 : ℝ) 1 then
                  intervalFullSemigroupOperator q.1 (intervalDomainLift u₀) q.2
                else 0 := by
          funext q
          by_cases hy : q.2 ∈ Set.Icc (0 : ℝ) 1
          · simp [picardIter, intervalDomainLift, hy]
          · simp [picardIter, intervalDomainLift, hy]
        change Measurable (fun q : ℝ × ℝ =>
          intervalDomainLift (picardIter p u₀ 0 q.1) q.2)
        rw [hfield]
        exact Measurable.ite (measurableSet_Icc.preimage measurable_snd)
          hSg_meas measurable_const
      · -- base upper cone: S(t)f₀ ≤ e^{at}·S(t)f₀
        intro t ht _htT x
        rw [hzero_eq t x, hS_eq t x]
        have hexp_ge : (1:ℝ) ≤ Real.exp (p.a * t) := by
          have h1 := Real.add_one_le_exp (p.a * t)
          nlinarith [mul_nonneg p.ha ht.le]
        nlinarith [hSf₀_nonneg ht (x.1 : ℝ)]
    | succ n ih =>
      obtain ⟨ih_ball, ih_nn, ih_cont, ih_meas, ih_cone⟩ := ih
      -- The cone-preservation output for Φ(iterate n).
      have hcp := cone_preserved p hχ hf₀_cont hf₀_eq
        (le_of_lt hM_in) hf₀_bdd hMc hT₀ hM
        (le_of_eq hKe_def.symm) ih_meas ih_ball ih_nn ih_cone
      have hsucc_eq : picardIter p u₀ (n + 1)
          = fun t x => intervalGradientDuhamelMap p u₀ (picardIter p u₀ n) t x :=
        rfl
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · -- ball
        intro t ht htT x
        rw [hsucc_eq]
        exact hmapsTo_proof (picardIter p u₀ n) ih_ball t ht htT x
      · -- nonneg from the cone lower output
        intro t ht htT x
        rw [hsucc_eq]
        have hlow := (hcp t ht htT x).1
        have hfac : (0:ℝ) ≤ 1 - Ke * envelopeIntegral p.a t := by
          have hmono : envelopeIntegral p.a t ≤ envelopeIntegral p.a T₀ :=
            envelopeIntegral_mono p.a ht.le htT
          have h1 : Ke * envelopeIntegral p.a t
              ≤ Ke * envelopeIntegral p.a T₀ :=
            mul_le_mul_of_nonneg_left hmono hKe_nn
          linarith [hcone_small]
        have hS := hSf₀_nonneg ht (x.1 : ℝ)
        nlinarith
      · -- continuous slices
        rw [hsucc_eq]
        exact hcont_preserved_proof (picardIter p u₀ n) ih_ball ih_meas
      · -- joint measurability
        rw [hsucc_eq]
        exact hmeas_preserved_proof (picardIter p u₀ n) ih_meas
      · -- upper cone from the cone upper output + FTC
        intro t ht htT x
        rw [hsucc_eq]
        have hhi := (hcp t ht htT x).2
        rwa [one_add_mul_envelopeIntegral p.a t] at hhi
  have hball := fun n => (hiter n).1
  have hball_nn := fun n => (hiter n).2.1
  have hcont_iterates := fun n => (hiter n).2.2.1
  have hmeas_iterates := fun n => (hiter n).2.2.2.1
  have hcone_iterates := fun n => (hiter n).2.2.2.2
  -- Geometric convergence.
  have hC₀ : (0:ℝ) ≤ 2 * M := by linarith
  have hbase_diff : ∀ t, 0 < t → t ≤ T₀ → ∀ x : intervalDomainPoint,
      |picardIter p u₀ 1 t x - picardIter p u₀ 0 t x| ≤ 2 * M := by
    intro t ht htT x
    have hu0 : |picardIter p u₀ 0 t x| ≤ M := hbase_ball T₀ t ht htT x
    have hu1 : |picardIter p u₀ 1 t x| ≤ M := (hball 1) t ht htT x
    have htri : |picardIter p u₀ 1 t x - picardIter p u₀ 0 t x|
        ≤ |picardIter p u₀ 1 t x| + |picardIter p u₀ 0 t x| := by
      calc |picardIter p u₀ 1 t x - picardIter p u₀ 0 t x|
          = |picardIter p u₀ 1 t x + (-(picardIter p u₀ 0 t x))| := by ring_nf
        _ ≤ |picardIter p u₀ 1 t x| + |-(picardIter p u₀ 0 t x)| :=
            abs_add_le _ _
        _ = |picardIter p u₀ 1 t x| + |picardIter p u₀ 0 t x| := by
            rw [abs_neg]
    linarith
  have hgeom := picardIter_geometric p u₀ hK_nn hball hball_nn
    hcont_iterates hmeas_iterates hcontr_proof hC₀ hbase_diff
  -- Limit facts.
  have hcont_limit := picardLimit_hasContinuousSlices p u₀ hT₀ hK_lt hK_nn hC₀
    (fun n => hgeom n) hcont_iterates
  have hmeas_limit : HasJointMeasurability (picardLimit p u₀ T₀) := by
    set f_n : ℕ → ℝ × ℝ → ℝ := fun n q =>
      if 0 < q.1 ∧ q.1 ≤ T₀ then intervalDomainLift (picardIter p u₀ n q.1) q.2 else 0
    set g : ℝ × ℝ → ℝ := fun q => intervalDomainLift (picardLimit p u₀ T₀ q.1) q.2
    have hf_meas : ∀ n, Measurable (f_n n) := fun n => by
      apply Measurable.ite
      · exact measurableSet_Ioc.preimage measurable_fst
      · exact hmeas_iterates n
      · exact measurable_const
    have hlim : Filter.Tendsto f_n Filter.atTop (nhds g) := by
      rw [tendsto_pi_nhds]; intro q
      by_cases hq : 0 < q.1 ∧ q.1 ≤ T₀
      · simp only [f_n, if_pos hq, g]
        unfold picardLimit; simp only [if_pos hq]
        unfold intervalDomainLift
        by_cases hy : q.2 ∈ Set.Icc (0 : ℝ) 1
        · simp only [dif_pos hy]
          exact tendsto_nhds_limUnder
            (picardIter_pointwise_convergent p u₀ hK_lt hK_nn hC₀
              (fun n => hgeom n) q.1 hq.1 hq.2 ⟨q.2, hy⟩)
        · simp only [dif_neg hy]; exact tendsto_const_nhds
      · simp only [f_n, if_neg hq]
        have hg0 : g q = 0 := by
          simp only [g, picardLimit, if_neg hq, intervalDomainLift]
          split_ifs <;> rfl
        rw [hg0]; exact tendsto_const_nhds
    exact measurable_of_tendsto_metrizable hf_meas hlim
  -- Strict positivity of the limit from the cone.
  have hSf₀_pos : ∀ {t : ℝ}, 0 < t → ∀ x : intervalDomainPoint,
      0 < intervalFullSemigroupOperator t f₀ x.1 := by
    intro t ht x
    obtain ⟨x₀, hx₀⟩ := hu₀_pos
    have hf₀_pos_at : 0 < f₀ x₀.1 := by
      simp only [hf₀_def, unitClip_of_mem x₀.2]
      exact hx₀
    exact intervalFullSemigroupOperator_pos ht hf₀_cont.continuousOn
      (fun y _ => hf₀_nonneg y) x₀.2 hf₀_pos_at x.1
  have hpos_limit : ∀ t, 0 < t → t ≤ T₀ → ∀ x : intervalDomainPoint,
      0 < picardLimit p u₀ T₀ t x := by
    intro t ht htT x
    -- Every iterate n ≥ 1 satisfies the cone lower output bound.
    have hlow_iter : ∀ n : ℕ,
        (1 - Ke * envelopeIntegral p.a t) *
          intervalFullSemigroupOperator t f₀ x.1
          ≤ picardIter p u₀ (n + 1) t x := by
      intro n
      have hcp := cone_preserved p hχ hf₀_cont hf₀_eq
        (le_of_lt hM_in) hf₀_bdd hMc hT₀ hM
        (le_of_eq hKe_def.symm) (hmeas_iterates n) (hball n) (hball_nn n)
        (hcone_iterates n)
      exact (hcp t ht htT x).1
    have hconv : Filter.Tendsto (fun n => picardIter p u₀ n t x)
        Filter.atTop (nhds (picardLimit p u₀ T₀ t x)) := by
      unfold picardLimit
      rw [if_pos ⟨ht, htT⟩]
      exact tendsto_nhds_limUnder
        (picardIter_pointwise_convergent p u₀ hK_lt hK_nn hC₀
          (fun n => hgeom n) t ht htT x)
    have hlim_low : (1 - Ke * envelopeIntegral p.a t) *
        intervalFullSemigroupOperator t f₀ x.1
        ≤ picardLimit p u₀ T₀ t x := by
      apply ge_of_tendsto hconv
      rw [Filter.eventually_atTop]
      refine ⟨1, fun n hn => ?_⟩
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
      have h := hlow_iter m
      rwa [Nat.add_comm m 1] at h
    have hfac : (1:ℝ)/2 ≤ 1 - Ke * envelopeIntegral p.a t := by
      have hmono : envelopeIntegral p.a t ≤ envelopeIntegral p.a T₀ :=
        envelopeIntegral_mono p.a ht.le htT
      have h1 : Ke * envelopeIntegral p.a t
          ≤ Ke * envelopeIntegral p.a T₀ :=
        mul_le_mul_of_nonneg_left hmono hKe_nn
      linarith [hcone_small]
    have hS := hSf₀_pos ht x
    nlinarith
  -- Assemble the packaged record.
  refine ⟨{
    T := T₀
    hT := hT₀
    M := M
    hM := hM
    u := picardLimit p u₀ T₀
    hmild := picardLimit_is_mildSolution p u₀ hT₀ hK_lt hK_nn hC₀ hM
      (fun n => hgeom n) hball hball_nn hcont_iterates hcont_limit
      hmeas_iterates hmeas_limit hcontr_proof
    hbound := picardLimit_bounded p u₀ hK_lt hK_nn hC₀
      (fun n => hgeom n) hball
    hnonneg := picardLimit_nonneg p u₀ hK_lt hK_nn hC₀
      (fun n => hgeom n) hball_nn
    hpos := hpos_limit
    hcont := hcont_limit
    hmeas := hmeas_limit
  }, rfl, rfl, hcont_iterates⟩

/-- **Cone-uniform Picard data (χ₀ = 0)**: one horizon
`δ = δ(p, M_in) > 0` such that EVERY continuous nonnegative datum with
`|u₀| ≤ M_in` that is positive somewhere has a packaged Picard mild
solution on exactly `[0, δ]` — no positive lower threshold on the datum.
Positivity of the limit comes from the exponential cone invariance.

Thin projection of `coneGradientMildSolutionData_exists_with_data` (drops the
extra iterate slice-continuity bundle), kept so existing consumers are
unchanged. -/
theorem coneGradientMildSolutionData_exists (p : CM2Params) (hχ : p.χ₀ = 0)
    {M_in : ℝ} (hM_in : 0 < M_in) (hα_ge : 1 ≤ p.α) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ u₀ : intervalDomainPoint → ℝ,
        Continuous u₀ →
        (∀ x, |u₀ x| ≤ M_in) →
        (∀ x, 0 ≤ u₀ x) →
        (∃ x₀, 0 < u₀ x₀) →
        ∃ D : GradientMildSolutionData p u₀,
          D.T = δ ∧ D.u = picardLimit p u₀ δ := by
  obtain ⟨δ, hδ, h⟩ := coneGradientMildSolutionData_exists_with_data p hχ hM_in hα_ge
  refine ⟨δ, hδ, fun u₀ hc hb hnn hpos => ?_⟩
  obtain ⟨D, hDT, hDu, _hcont_iter⟩ := h u₀ hc hb hnn hpos
  exact ⟨D, hDT, hDu⟩

end ShenWork.IntervalMildPicardConeData
