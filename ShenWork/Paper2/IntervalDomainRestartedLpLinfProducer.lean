/-
Finite-Lp to Linf producer for Paper 2.  It uses the faithful physical
B-form restart, smooths the restart datum from Lp (never from a presumed
Linf bound), bounds the chemotaxis flux in Lp, and drops the favorable
logistic sink through heat-semigroup order preservation.
-/
import ShenWork.Paper2.IntervalDomainRestartedLpLinf
import ShenWork.Paper2.IntervalDomainMCriticalLinfBound
import ShenWork.Paper2.IntervalDomainMCriticalGlobalLpBootstrap

open MeasureTheory Set Filter Topology
open scoped Topology Interval ENNReal
open ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.Paper2.IntervalDomainRestartedLpLinfProducer

open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.Paper2.IntervalDomainRestartedLpLinf
open ShenWork.IntervalConjugateDuhamelMap
open ShenWork.IntervalNeumannFullKernel

theorem restartFluxM_lp_root_le_of_lp
    {p : CM2Params} {T a h s P C : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hh : 0 ≤ h) (hahT : a + h < T)
    (hm : p.m = 1) (hP : 1 < P) (hγP : p.γ ≤ P)
    (hpower : ∀ τ, 0 < τ → τ < T →
      intervalDomainM.integral (fun z => (u τ z) ^ P) ≤ C)
    (hs : s ∈ Icc (0 : ℝ) h) :
    (∫ y, ‖restartFluxM p a h u v s y‖ ^ P ∂ intervalMeasure 1) ^ (1 / P) ≤
      (2 * p.ν * (C + 1)) * (C + 1) ^ (1 / P) := by
  let τ : ℝ := a + s
  let G : ℝ := 2 * p.ν * (C + 1)
  have hτ0 : 0 < τ := by
    dsimp [τ]
    exact add_pos_of_pos_of_nonneg ha hs.1
  have hτT : τ < T := by
    dsimp [τ]
    exact lt_of_le_of_lt (by linarith [hs.2]) hahT
  have hpow := hpower τ hτ0 hτT
  have hC : 0 ≤ C := by
    have hnonneg : 0 ≤ intervalDomainM.integral (fun z => (u τ z) ^ P) := by
      change 0 ≤ intervalDomain.integral (fun z => (u τ z) ^ P)
      rw [ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation.intervalDomain_integral_rpow_eq_lift_integral]
      exact intervalIntegral.integral_nonneg (by norm_num) fun y hy =>
        Real.rpow_nonneg (solution_lift_pos_Icc hsol ⟨hτ0, hτT⟩ y (by
          simpa [Set.uIcc_of_le zero_le_one] using hy)).le P
    exact hnonneg.trans hpow
  have hG : 0 ≤ G := by
    dsimp [G]
    exact mul_nonneg (mul_nonneg (by norm_num) p.hν.le) (by linarith)
  have hpoint : ∀ y ∈ Icc (0 : ℝ) 1,
      |restartFluxM p a h u v s y| ≤ intervalDomainLift (u τ) y * G := by
    intro y hy
    have hu_pos : 0 < restartField a h u s y :=
      restartField_u_pos hsol ha hh hahT s y
    have hv_nonneg : 0 ≤ restartField a h v s y :=
      restartField_v_nonneg hsol ha hh hahT s y
    have hden : 1 ≤ (1 + restartField a h v s y) ^ p.β :=
      Real.one_le_rpow (by linarith) p.hβ
    have hgrad : |restartChemGrad p a h u v s y| ≤ G := by
      rw [restartChemGrad_eq_deriv hsol ha hh hahT hs hy]
      simpa [G, τ] using chemical_gradient_abs_le_of_lp
        hsol hτ0 hτT hy hγP hpow
    have hfield : restartField a h u s y = intervalDomainLift (u τ) y :=
      restartField_eq_physical hs hy
    unfold restartFluxM
    rw [abs_div, abs_mul, hm, Real.rpow_one, abs_of_pos hu_pos,
      abs_of_nonneg (Real.rpow_nonneg (by linarith) p.β), hfield]
    apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hden)).2
    have hu_nonneg : 0 ≤ intervalDomainLift (u τ) y := by
      rw [← hfield]
      exact hu_pos.le
    exact (mul_le_mul_of_nonneg_left hgrad hu_nonneg).trans
      (le_mul_of_one_le_right (mul_nonneg hu_nonneg hG) hden)
  have hflux_cont : Continuous (restartFluxM p a h u v s) :=
    (restartFluxM_continuous hsol ha hh hahT).uncurry_left s
  have hflux_int : Integrable
      (fun y => ‖restartFluxM p a h u v s y‖ ^ P) (intervalMeasure 1) := by
    simpa [intervalMeasure, intervalSet] using
      ((hflux_cont.norm.rpow_const (fun _ => Or.inr (by linarith : 0 ≤ P))).continuousOn.integrableOn_Icc)
  have huP_int : Integrable
      (fun y => (intervalDomainLift (u τ) y * G) ^ P) (intervalMeasure 1) := by
    have hc : ContinuousOn (fun y => (intervalDomainLift (u τ) y * G) ^ P)
        (Icc (0 : ℝ) 1) :=
      ((ShenWork.Paper2.IntervalDomainM.solution_lift_continuousOn_Icc
        hsol ⟨hτ0, hτT⟩).mul continuousOn_const).rpow_const
        (fun _ _ => Or.inr (by linarith : 0 ≤ P))
    simpa [intervalMeasure, intervalSet] using hc.integrableOn_Icc
  have hint :
      (∫ y, ‖restartFluxM p a h u v s y‖ ^ P ∂ intervalMeasure 1) ≤
        ∫ y, (intervalDomainLift (u τ) y * G) ^ P ∂ intervalMeasure 1 := by
    apply MeasureTheory.integral_mono_ae hflux_int huP_int
    refine (ae_restrict_iff' measurableSet_Icc).2
      (Filter.Eventually.of_forall fun y hy => ?_)
    exact Real.rpow_le_rpow (abs_nonneg _) (by
      simpa [Real.norm_eq_abs] using hpoint y hy) (by linarith : 0 ≤ P)
  have hsource :
      (∫ y, (intervalDomainLift (u τ) y * G) ^ P ∂ intervalMeasure 1) =
        G ^ P * intervalDomainM.integral (fun z => (u τ z) ^ P) := by
    rw [show (fun y => (intervalDomainLift (u τ) y * G) ^ P) =
        fun y => G ^ P * intervalDomainLift (u τ) y ^ P by
      funext y
      by_cases hy : y ∈ Icc (0 : ℝ) 1
      · rw [Real.mul_rpow
          (solution_lift_pos_Icc hsol ⟨hτ0, hτT⟩ y hy).le hG]
        ring
      · simp [intervalDomainLift, hy, Real.zero_rpow (by linarith : P ≠ 0)],
      MeasureTheory.integral_const_mul]
    congr 1
    rw [ShenWork.Paper2.IntervalConjugateKernelIBP.intervalMeasure_one_integral_eq_intervalIntegral]
    change (∫ y in (0 : ℝ)..1, intervalDomainLift (u τ) y ^ P) =
      intervalDomain.integral (fun z => (u τ z) ^ P)
    exact (ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation.intervalDomain_integral_rpow_eq_lift_integral).symm
  have htotal :
      (∫ y, ‖restartFluxM p a h u v s y‖ ^ P ∂ intervalMeasure 1) ≤
        G ^ P * (C + 1) := by
    calc
      _ ≤ ∫ y, (intervalDomainLift (u τ) y * G) ^ P ∂ intervalMeasure 1 := hint
      _ = G ^ P * intervalDomainM.integral (fun z => (u τ z) ^ P) := hsource
      _ ≤ G ^ P * C := mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hG P)
      _ ≤ G ^ P * (C + 1) := by
        gcongr
        linarith
  have hleft0 : 0 ≤
      ∫ y, ‖restartFluxM p a h u v s y‖ ^ P ∂ intervalMeasure 1 :=
    integral_nonneg fun y => Real.rpow_nonneg (norm_nonneg _) P
  have hroot := Real.rpow_le_rpow hleft0 htotal (by positivity : 0 ≤ 1 / P)
  have hcollapse : (G ^ P * (C + 1)) ^ (1 / P) =
      G * (C + 1) ^ (1 / P) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hG P) (by linarith : 0 ≤ C + 1),
      ← Real.rpow_mul hG]
    have he : P * (1 / P) = 1 := by field_simp [ne_of_gt (lt_trans zero_lt_one hP)]
    rw [he, Real.rpow_one]
  rw [hcollapse] at hroot
  simpa [G] using hroot

theorem restartChemDuhamelM_abs_le_of_lp
    {p : CM2Params} {T a h r P C : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hh : 0 ≤ h) (hahT : a + h < T)
    (hm : p.m = 1) (hP : 1 < P) (hγP : p.γ ≤ P)
    (hpower : ∀ τ, 0 < τ → τ < T →
      intervalDomainM.integral (fun z => (u τ z) ^ P) ≤ C)
    (hr : 0 < r) (hrh : r ≤ h) (hh1 : h ≤ 1)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    |restartChemDuhamelM p a h u v r x| ≤
      conjugateLpLinftyConstant P *
        ((2 * p.ν * (C + 1)) * (C + 1) ^ (1 / P)) *
        (r ^ (1 - conjugateLpLinftyTheta P) /
          (1 - conjugateLpLinftyTheta P)) := by
  let q : ℝ → ℝ → ℝ := restartFluxM p a h u v
  let K : ℝ := (2 * p.ν * (C + 1)) * (C + 1) ^ (1 / P)
  let B : ℝ := conjugateLpLinftyConstant P
  have hqcont : Continuous (Function.uncurry q) := by
    simpa [q] using restartFluxM_continuous hsol ha hh hahT
  obtain ⟨Cq, hCq, hqbound⟩ :=
    exists_restartFluxM_bound hsol ha hh hahT
  have hqint : ∀ s, Integrable (q s) (intervalMeasure 1) := by
    intro s
    exact intervalMeasure_integrable_of_abs_bound
      (hqcont.uncurry_left s).measurable.aestronglyMeasurable
      (by simpa [q] using hqbound s)
  have hqmem : ∀ s, MemLp (q s) (ENNReal.ofReal P) (intervalMeasure 1) := by
    intro s
    apply MemLp.of_bound (hqcont.uncurry_left s).aestronglyMeasurable Cq
    exact Filter.Eventually.of_forall fun y => by
      simpa [Real.norm_eq_abs, q] using hqbound s y
  have hwhole : IntervalIntegrable
      (fun s => intervalConjugateKernelOperator (r - s) (q s) x)
      volume 0 r :=
    ShenWork.IntervalConjugateChemFluxIntegrable.conjugateDuhamel_intervalIntegrable_of_measurable_bound
      hr hCq hqcont.measurable hqint (by simpa [q] using hqbound)
  have henv : IntervalIntegrable
      (fun s => B * K * (r - s) ^ (-conjugateLpLinftyTheta P))
      volume 0 r :=
    (intervalIntegrable_sub_rpow_neg_conjugateTheta hP).const_mul (B * K)
  have hne : ∀ᵐ s : ℝ ∂volume, s ≠ r := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
  have hae : (fun s =>
      |intervalConjugateKernelOperator (r - s) (q s) x|) ≤ᵐ[volume.restrict (Icc (0 : ℝ) r)]
      (fun s => B * K * (r - s) ^ (-conjugateLpLinftyTheta P)) := by
    refine (ae_restrict_iff' measurableSet_Icc).2 ?_
    filter_upwards [hne] with s hsr hs
    have hrs : 0 < r - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hsr)
    have hrs1 : r - s ≤ 1 := by linarith [hs.1, hrh, hh1]
    let R : ℝ := P / (P - 1)
    have hRP : R.HolderConjugate P :=
      (Real.HolderConjugate.conjExponent hP).symm
    have hs_h : s ∈ Icc (0 : ℝ) h := ⟨hs.1, hs.2.trans hrh⟩
    have hroot := restartFluxM_lp_root_le_of_lp hsol ha hh hahT hm hP hγP
      hpower hs_h
    have hroot' :
        (∫ y, ‖q s y‖ ^ P ∂ intervalMeasure 1) ^ (1 / P) ≤ K := by
      simpa [q, K] using hroot
    have hsmooth := intervalConjugateKernelOperator_abs_le_Lp_short
      hrs hrs1 hRP (hqcont.uncurry_left s) (hqint s) hCq
      (by simpa [q] using hqbound s) (hqmem s) hx
    exact hsmooth.trans (by
      calc
        conjugateLpLinftyConstant P *
            (r - s) ^ (-conjugateLpLinftyTheta P) *
              (∫ y, ‖q s y‖ ^ P ∂ intervalMeasure 1) ^ (1 / P) ≤
          conjugateLpLinftyConstant P *
            (r - s) ^ (-conjugateLpLinftyTheta P) * K :=
          mul_le_mul_of_nonneg_left hroot'
            (mul_nonneg (by
              dsimp [conjugateLpLinftyConstant]
              exact mul_nonneg
                (Real.rpow_nonneg
                  (mul_nonneg fullHeatShortConstant_nonneg
                    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)) _)
                (mul_nonneg ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
                  (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)))
              (Real.rpow_nonneg hrs.le _))
        _ = B * K * (r - s) ^ (-conjugateLpLinftyTheta P) := by
          dsimp [B]
          ring)
  unfold restartChemDuhamelM
  calc
    |∫ s in (0 : ℝ)..r,
        intervalConjugateKernelOperator (r - s) (q s) x| ≤
        ∫ s in (0 : ℝ)..r,
          |intervalConjugateKernelOperator (r - s) (q s) x| :=
      intervalIntegral.abs_integral_le_integral_abs hr.le
    _ ≤ ∫ s in (0 : ℝ)..r,
        B * K * (r - s) ^ (-conjugateLpLinftyTheta P) :=
      intervalIntegral.integral_mono_ae_restrict hr.le hwhole.abs henv hae
    _ = B * K *
        (r ^ (1 - conjugateLpLinftyTheta P) /
          (1 - conjugateLpLinftyTheta P)) := by
      rw [intervalIntegral.integral_const_mul,
        integral_sub_rpow_neg_conjugateTheta hP hr.le]
    _ = conjugateLpLinftyConstant P *
        ((2 * p.ν * (C + 1)) * (C + 1) ^ (1 / P)) *
        (r ^ (1 - conjugateLpLinftyTheta P) /
          (1 - conjugateLpLinftyTheta P)) := by
      rfl

theorem restartField_lp_root_le_of_lp
    {p : CM2Params} {T a h s P C : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hh : 0 ≤ h) (hahT : a + h < T)
    (hP : 1 < P)
    (hpower : ∀ τ, 0 < τ → τ < T →
      intervalDomainM.integral (fun z => (u τ z) ^ P) ≤ C)
    (hs : s ∈ Icc (0 : ℝ) h) :
    (∫ y, ‖restartField a h u s y‖ ^ P ∂ intervalMeasure 1) ^ (1 / P) ≤
      (C + 1) ^ (1 / P) := by
  let τ : ℝ := a + s
  have hτ0 : 0 < τ := by
    dsimp [τ]
    exact add_pos_of_pos_of_nonneg ha hs.1
  have hτT : τ < T := by
    dsimp [τ]
    exact lt_of_le_of_lt (by linarith [hs.2]) hahT
  have hpow := hpower τ hτ0 hτT
  have heq :
      (∫ y, ‖restartField a h u s y‖ ^ P ∂ intervalMeasure 1) =
        intervalDomainM.integral (fun z => (u τ z) ^ P) := by
    rw [ShenWork.Paper2.IntervalConjugateKernelIBP.intervalMeasure_one_integral_eq_intervalIntegral]
    change (∫ y in (0 : ℝ)..1, |restartField a h u s y| ^ P) =
      intervalDomain.integral (fun z => (u τ z) ^ P)
    rw [ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation.intervalDomain_integral_rpow_eq_lift_integral]
    apply intervalIntegral.integral_congr
    intro y hy
    have hyIcc : y ∈ Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le zero_le_one] using hy
    change |restartField a h u s y| ^ P = intervalDomainLift (u τ) y ^ P
    rw [restartField_eq_physical hs hyIcc,
      abs_of_pos (solution_lift_pos_Icc hsol ⟨hτ0, hτT⟩ y hyIcc)]
  have hleft0 : 0 ≤
      ∫ y, ‖restartField a h u s y‖ ^ P ∂ intervalMeasure 1 :=
    integral_nonneg fun y => Real.rpow_nonneg (norm_nonneg _) P
  have hC : 0 ≤ C := by
    rw [heq] at hleft0
    exact hleft0.trans hpow
  have htotal :
      (∫ y, ‖restartField a h u s y‖ ^ P ∂ intervalMeasure 1) ≤ C + 1 := by
    rw [heq]
    linarith
  exact Real.rpow_le_rpow hleft0 htotal (by positivity : 0 ≤ 1 / P)

theorem restartLogisticDuhamelM_le_of_lp
    {p : CM2Params} {T a h r P C : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hh : 0 ≤ h) (hahT : a + h < T)
    (hP : 1 < P)
    (hpower : ∀ τ, 0 < τ → τ < T →
      intervalDomainM.integral (fun z => (u τ z) ^ P) ≤ C)
    (hr : 0 < r) (hrh : r ≤ h) (hh1 : h ≤ 1) (x : ℝ) :
    restartLogisticDuhamelM p a h u r x ≤
      p.a * fullHeatShortConstant ^ (1 / P) * (C + 1) ^ (1 / P) *
        (r ^ (1 - 1 / (2 * P)) / (1 - 1 / (2 * P))) := by
  let w : ℝ → ℝ → ℝ := restartField a h u
  let ell : ℝ → ℝ → ℝ := restartLogisticM p a h u
  obtain ⟨Mw, hMw, hwbound⟩ :=
    exists_abs_bound_of_continuous_restart_clamp hh
      (restartField_continuous hsol ha hh hahT u (Or.inl rfl))
      (restartField_clamp hh u)
  obtain ⟨Cell, hCell, hellbound⟩ :=
    exists_restartLogisticM_bound hsol ha hh hahT
  have hwcont : Continuous (Function.uncurry w) := by
    simpa [w] using restartField_continuous hsol ha hh hahT u (Or.inl rfl)
  have hellcont : Continuous (Function.uncurry ell) := by
    simpa [ell] using restartLogisticM_continuous hsol ha hh hahT
  have hellint : IntervalIntegrable
      (fun s => intervalFullSemigroupOperator (r - s) (ell s) x)
      volume 0 r :=
    ShenWork.IntervalDuhamelIntegrability.valueDuhamel_intervalIntegrable_of_joint_measurable
      hr hellcont.measurable hCell (by simpa [ell] using hellbound) x
  have htheta : 1 / (2 * P) < 1 := by
    have : 2 < 2 * P := by linarith
    have hinv : 1 / (2 * P) < 1 / 2 :=
      one_div_lt_one_div_of_lt (by norm_num) this
    linarith
  have henv : IntervalIntegrable
      (fun s => p.a * fullHeatShortConstant ^ (1 / P) *
        (C + 1) ^ (1 / P) * (r - s) ^ (-(1 / (2 * P))))
      volume 0 r := by
    have h0 : IntervalIntegrable
        (fun z : ℝ => z ^ (-(1 / (2 * P)))) volume 0 r :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    simpa using (((h0.comp_sub_left r).symm).const_mul
      (p.a * fullHeatShortConstant ^ (1 / P) * (C + 1) ^ (1 / P)))
  have hne : ∀ᵐ s : ℝ ∂volume, s ≠ r := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
  have hae : (fun s => intervalFullSemigroupOperator (r - s) (ell s) x) ≤ᵐ[volume.restrict (Icc (0 : ℝ) r)]
      (fun s => p.a * fullHeatShortConstant ^ (1 / P) *
        (C + 1) ^ (1 / P) * (r - s) ^ (-(1 / (2 * P)))) := by
    refine (ae_restrict_iff' measurableSet_Icc).2 ?_
    filter_upwards [hne] with s hsr hs
    have hrs : 0 < r - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hsr)
    have hrs1 : r - s ≤ 1 := by linarith [hs.1, hrh, hh1]
    have hs_h : s ∈ Icc (0 : ℝ) h := ⟨hs.1, hs.2.trans hrh⟩
    have hell_le : ∀ y, ell s y ≤ p.a * w s y := by
      intro y
      have hu := restartField_u_pos hsol ha hh hahT s y
      have hdamp : 0 ≤ p.b * (w s y) ^ p.α := by
        dsimp [w]
        exact mul_nonneg p.hb (Real.rpow_nonneg hu.le _)
      dsimp [ell, restartLogisticM, w]
      nlinarith [p.ha]
    have hmono := ShenWork.IntervalSemigroupConeAtoms.intervalFullSemigroupOperator_mono_of_le
      hrs (hellcont.uncurry_left s).measurable.aestronglyMeasurable
      ((hwcont.uncurry_left s).const_mul p.a).measurable.aestronglyMeasurable
      (by simpa [ell] using hellbound s)
      (fun y => by
        rw [abs_mul, abs_of_nonneg p.ha]
        exact mul_le_mul_of_nonneg_left (hwbound s y) p.ha)
      hell_le x
    let R : ℝ := P / (P - 1)
    have hRP : R.HolderConjugate P :=
      (Real.HolderConjugate.conjExponent hP).symm
    have hwint : Integrable (w s) (intervalMeasure 1) :=
      intervalMeasure_integrable_of_abs_bound
        (hwcont.uncurry_left s).measurable.aestronglyMeasurable (hwbound s)
    have hwmem : MemLp (w s) (ENNReal.ofReal P) (intervalMeasure 1) := by
      apply MemLp.of_bound (hwcont.uncurry_left s).aestronglyMeasurable Mw
      exact Filter.Eventually.of_forall fun y => by
        simpa [Real.norm_eq_abs] using hwbound s y
    have hheat := intervalFullSemigroupOperator_abs_le_Lp_short
      hrs hrs1 hRP hwmem x
    have hroot := restartField_lp_root_le_of_lp hsol ha hh hahT hP hpower hs_h
    have hheat' : intervalFullSemigroupOperator (r - s) (w s) x ≤
        (fullHeatShortConstant * (r - s) ^ (-(1 / 2 : ℝ))) ^ (1 / P) *
          (C + 1) ^ (1 / P) := by
      exact (le_abs_self _).trans (hheat.trans
        (mul_le_mul_of_nonneg_left hroot
          (Real.rpow_nonneg
            (mul_nonneg fullHeatShortConstant_nonneg
              (Real.rpow_nonneg hrs.le _)) _)))
    have hfactor :
        (fullHeatShortConstant * (r - s) ^ (-(1 / 2 : ℝ))) ^ (1 / P) =
          fullHeatShortConstant ^ (1 / P) *
            (r - s) ^ (-(1 / (2 * P))) := by
      rw [Real.mul_rpow fullHeatShortConstant_nonneg
        (Real.rpow_nonneg hrs.le _), ← Real.rpow_mul hrs.le]
      congr 1
      field_simp [ne_of_gt (lt_trans zero_lt_one hP)]
    calc
      intervalFullSemigroupOperator (r - s) (ell s) x ≤
          intervalFullSemigroupOperator (r - s) (fun y => p.a * w s y) x := hmono
      _ = p.a * intervalFullSemigroupOperator (r - s) (w s) x := by
        exact ShenWork.IntervalSemigroupConeAtoms.intervalFullSemigroupOperator_const_mul
          (r - s) p.a (w s) x
      _ ≤ p.a * ((fullHeatShortConstant * (r - s) ^ (-(1 / 2 : ℝ))) ^ (1 / P) *
          (C + 1) ^ (1 / P)) := mul_le_mul_of_nonneg_left hheat' p.ha
      _ = p.a * fullHeatShortConstant ^ (1 / P) *
          (C + 1) ^ (1 / P) * (r - s) ^ (-(1 / (2 * P))) := by
        rw [hfactor]
        ring
  unfold restartLogisticDuhamelM
  calc
    (∫ s in (0 : ℝ)..r, intervalFullSemigroupOperator (r - s) (ell s) x) ≤
        ∫ s in (0 : ℝ)..r,
          p.a * fullHeatShortConstant ^ (1 / P) *
            (C + 1) ^ (1 / P) * (r - s) ^ (-(1 / (2 * P))) :=
      intervalIntegral.integral_mono_ae_restrict hr.le hellint henv hae
    _ = p.a * fullHeatShortConstant ^ (1 / P) * (C + 1) ^ (1 / P) *
        (r ^ (1 - 1 / (2 * P)) / (1 - 1 / (2 * P))) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_sub_left
          (fun z : ℝ => z ^ (-(1 / (2 * P)))) r]
      simp only [sub_self, sub_zero]
      rw [integral_rpow (Or.inl (by linarith)),
        show -(1 / (2 * P)) + 1 = 1 - 1 / (2 * P) by ring,
        Real.zero_rpow (by linarith), sub_zero]

theorem solutionLift_lp_root_le_of_lp
    {p : CM2Params} {T t P C : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) (hP : 1 < P)
    (hpow : intervalDomainM.integral (fun z => (u t z) ^ P) ≤ C) :
    (∫ y, ‖intervalDomainLift (u t) y‖ ^ P ∂ intervalMeasure 1) ^ (1 / P) ≤
      (C + 1) ^ (1 / P) := by
  have heq :
      (∫ y, ‖intervalDomainLift (u t) y‖ ^ P ∂ intervalMeasure 1) =
        intervalDomainM.integral (fun z => (u t z) ^ P) := by
    rw [ShenWork.Paper2.IntervalConjugateKernelIBP.intervalMeasure_one_integral_eq_intervalIntegral]
    change (∫ y in (0 : ℝ)..1, |intervalDomainLift (u t) y| ^ P) =
      intervalDomain.integral (fun z => (u t z) ^ P)
    rw [ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation.intervalDomain_integral_rpow_eq_lift_integral]
    apply intervalIntegral.integral_congr
    intro y hy
    have hyIcc : y ∈ Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le zero_le_one] using hy
    change |intervalDomainLift (u t) y| ^ P = intervalDomainLift (u t) y ^ P
    rw [abs_of_pos (solution_lift_pos_Icc hsol ⟨ht0, htT⟩ y hyIcc)]
  have hleft0 : 0 ≤
      ∫ y, ‖intervalDomainLift (u t) y‖ ^ P ∂ intervalMeasure 1 :=
    integral_nonneg fun y => Real.rpow_nonneg (norm_nonneg _) P
  have hC : 0 ≤ C := by
    rw [heq] at hleft0
    exact hleft0.trans hpow
  have htotal :
      (∫ y, ‖intervalDomainLift (u t) y‖ ^ P ∂ intervalMeasure 1) ≤ C + 1 := by
    rw [heq]
    linarith
  exact Real.rpow_le_rpow hleft0 htotal (by positivity : 0 ≤ 1 / P)

theorem solutionSlice_le_of_restart_affine_lp
    {p : CM2Params} {T a h r P C : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hh : 0 ≤ h) (hahT : a + h < T)
    (hm : p.m = 1) (hP : 1 < P) (hγP : p.γ ≤ P)
    (hpower : ∀ τ, 0 < τ → τ < T →
      intervalDomainM.integral (fun z => (u τ z) ^ P) ≤ C)
    (hr : 0 < r) (hrh : r ≤ h) (hh1 : h ≤ 1)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    intervalDomainLift (u (a + r)) x ≤
      (fullHeatShortConstant * r ^ (-(1 / 2 : ℝ))) ^ (1 / P) *
          (C + 1) ^ (1 / P) +
        |p.χ₀| *
          (conjugateLpLinftyConstant P *
            ((2 * p.ν * (C + 1)) * (C + 1) ^ (1 / P)) *
            (r ^ (1 - conjugateLpLinftyTheta P) /
              (1 - conjugateLpLinftyTheta P))) +
        p.a * fullHeatShortConstant ^ (1 / P) * (C + 1) ^ (1 / P) *
          (r ^ (1 - 1 / (2 * P)) / (1 - 1 / (2 * P))) := by
  have haT : a < T := by linarith
  have har0 : 0 < a + r := by linarith
  have harT : a + r < T := lt_of_le_of_lt (by linarith) hahT
  obtain ⟨M, hM, huM⟩ := exists_solutionLift_abs_bound hsol ⟨ha, haT⟩
  have hucont : AEStronglyMeasurable (intervalDomainLift (u a))
      (intervalMeasure 1) :=
    (ShenWork.Paper2.IntervalDomainM.solution_lift_continuousOn_Icc
      hsol ⟨ha, haT⟩).aestronglyMeasurable
      measurableSet_Icc
  have humem : MemLp (intervalDomainLift (u a)) (ENNReal.ofReal P)
      (intervalMeasure 1) := by
    apply MemLp.of_bound hucont M
    exact Filter.Eventually.of_forall fun y => by
      simpa [Real.norm_eq_abs] using huM y
  let R : ℝ := P / (P - 1)
  have hRP : R.HolderConjugate P :=
    (Real.HolderConjugate.conjExponent hP).symm
  have hroot0 := solutionLift_lp_root_le_of_lp hsol ha haT hP (hpower a ha haT)
  have hhom : ∀ y,
      |intervalFullSemigroupOperator r (intervalDomainLift (u a)) y| ≤
        (fullHeatShortConstant * r ^ (-(1 / 2 : ℝ))) ^ (1 / P) *
          (C + 1) ^ (1 / P) := by
    intro y
    have hhom0 := intervalFullSemigroupOperator_abs_le_Lp_short
      hr (hrh.trans hh1) hRP humem y
    exact hhom0.trans (mul_le_mul_of_nonneg_left hroot0
        (Real.rpow_nonneg
          (mul_nonneg fullHeatShortConstant_nonneg (Real.rpow_nonneg hr.le _)) _))
  have hchem : ∀ y ∈ Icc (0 : ℝ) 1,
      |restartChemDuhamelM p a h u v r y| ≤
        conjugateLpLinftyConstant P *
          ((2 * p.ν * (C + 1)) * (C + 1) ^ (1 / P)) *
          (r ^ (1 - conjugateLpLinftyTheta P) /
            (1 - conjugateLpLinftyTheta P)) := by
    intro y hy
    exact restartChemDuhamelM_abs_le_of_lp hsol ha hh hahT hm hP hγP
      hpower hr hrh hh1 hy
  have hlog : ∀ y, restartLogisticDuhamelM p a h u r y ≤
      p.a * fullHeatShortConstant ^ (1 / P) * (C + 1) ^ (1 / P) *
        (r ^ (1 - 1 / (2 * P)) / (1 - 1 / (2 * P))) := by
    intro y
    exact restartLogisticDuhamelM_le_of_lp hsol ha hh hahT hP hpower
      hr hrh hh1 y
  have hcand : ∀ y ∈ Icc (0 : ℝ) 1,
      faithfulRestartDuhamelM p a h u v r y ≤
      (fullHeatShortConstant * r ^ (-(1 / 2 : ℝ))) ^ (1 / P) *
          (C + 1) ^ (1 / P) +
        |p.χ₀| *
          (conjugateLpLinftyConstant P *
            ((2 * p.ν * (C + 1)) * (C + 1) ^ (1 / P)) *
            (r ^ (1 - conjugateLpLinftyTheta P) /
              (1 - conjugateLpLinftyTheta P))) +
        p.a * fullHeatShortConstant ^ (1 / P) * (C + 1) ^ (1 / P) *
          (r ^ (1 - 1 / (2 * P)) / (1 - 1 / (2 * P))) := by
    intro y hy
    unfold faithfulRestartDuhamelM
    have hχ : 0 ≤ |p.χ₀| := abs_nonneg _
    have hchemMul :
        -p.χ₀ * restartChemDuhamelM p a h u v r y ≤
          |p.χ₀| * |restartChemDuhamelM p a h u v r y| := by
      calc
        _ ≤ |-p.χ₀ * restartChemDuhamelM p a h u v r y| := le_abs_self _
        _ = |p.χ₀| * |restartChemDuhamelM p a h u v r y| := by
          rw [abs_mul, abs_neg]
    nlinarith [le_abs_self
      (intervalFullSemigroupOperator r (intervalDomainLift (u a)) y),
      hhom y, hlog y, mul_le_mul_of_nonneg_left (hchem y hy) hχ]
  have haeEq := faithfulRestartDuhamelM_ae_eq_solution hsol ha hh hahT hr hrh
  have haeLe : ∀ᵐ y ∂volume.restrict (Ioc (0 : ℝ) 1),
      intervalDomainLift (u (a + r)) y ≤
        (fullHeatShortConstant * r ^ (-(1 / 2 : ℝ))) ^ (1 / P) *
            (C + 1) ^ (1 / P) +
          |p.χ₀| *
            (conjugateLpLinftyConstant P *
              ((2 * p.ν * (C + 1)) * (C + 1) ^ (1 / P)) *
              (r ^ (1 - conjugateLpLinftyTheta P) /
                (1 - conjugateLpLinftyTheta P))) +
          p.a * fullHeatShortConstant ^ (1 / P) * (C + 1) ^ (1 / P) *
            (r ^ (1 - 1 / (2 * P)) / (1 - 1 / (2 * P))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc, haeEq] with y hyIoc hy
    rw [← hy]
    exact hcand y (Ioc_subset_Icc_self hyIoc)
  have hcont := ShenWork.Paper2.IntervalDomainM.solution_lift_continuousOn_Icc
    hsol ⟨har0, harT⟩
  exact continuousOn_le_of_ae_le_Ioc hcont haeLe x hx

theorem boundedBefore_of_lp_restarted_affine
    {p : CM2Params} {T P : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hm : p.m = 1) (hP : 1 < P) (hγP : p.γ ≤ P)
    (hLp : LpPowerBoundedBefore intervalDomainM P T u) :
    IsPaper2BoundedBefore intervalDomainM T u := by
  obtain ⟨C, hpower⟩ := hLp
  obtain ⟨δ, hδ, E, hE, hearly⟩ :=
    exists_initial_trace_pointwise_upper hu₀ hsol htrace
  let w : ℝ := min (δ / 4) (1 / 2)
  have hw : 0 < w := lt_min (div_pos hδ (by norm_num)) (by norm_num)
  have hw1 : w ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have h2wδ : 2 * w < δ := by
    have := min_le_left (δ / 4) (1 / 2)
    dsimp [w]
    linarith
  let R : ℝ :=
    (fullHeatShortConstant * w ^ (-(1 / 2 : ℝ))) ^ (1 / P) *
        (C + 1) ^ (1 / P) +
      |p.χ₀| *
        (conjugateLpLinftyConstant P *
          ((2 * p.ν * (C + 1)) * (C + 1) ^ (1 / P)) *
          (w ^ (1 - conjugateLpLinftyTheta P) /
            (1 - conjugateLpLinftyTheta P))) +
      p.a * fullHeatShortConstant ^ (1 / P) * (C + 1) ^ (1 / P) *
        (w ^ (1 - 1 / (2 * P)) / (1 - 1 / (2 * P)))
  refine ⟨max E R, ?_⟩
  intro t ht0 htT
  change intervalDomainSupNorm (u t) ≤ max E R
  unfold intervalDomainSupNorm
  apply csSup_le
  · let x₀ : intervalDomainPoint := ⟨0, ⟨le_rfl, zero_le_one⟩⟩
    exact ⟨|u t x₀|, ⟨x₀, rfl⟩⟩
  intro y hy
  obtain ⟨x, rfl⟩ := hy
  change |u t x| ≤ max E R
  rw [abs_of_pos (u_pos hsol ht0 htT x)]
  by_cases htEarly : t < 2 * w
  · exact (hearly t ht0 (htEarly.trans h2wδ) x).trans (le_max_left _ _)
  · have h2wt : 2 * w ≤ t := le_of_not_gt htEarly
    let a : ℝ := t - w
    have ha : 0 < a := by dsimp [a]; linarith
    have hahT : a + w < T := by dsimp [a]; simpa using htT
    have hslice := solutionSlice_le_of_restart_affine_lp
      hsol ha hw.le hahT hm hP hγP hpower hw le_rfl hw1 x.property
    have heq : intervalDomainLift (u (a + w)) x.1 = u t x := by
      dsimp [a]
      simp [intervalDomainLift, x.property]
    have hraw : u t x ≤ R := by
      rw [← heq]
      simpa [R] using hslice
    exact hraw.trans (le_max_right _ _)

theorem Proposition_2_5_intervalDomain_of_restarted_affine
    {p : CM2Params} (hm : p.m = 1) :
    Proposition_2_5 intervalDomain p := by
  intro u₀ hu₀ T hT u v hsol htrace P hthreshold hLp
  have hN1 : (1 : ℝ) ≤ p.N := by exact_mod_cast p.hN
  have hP : 1 < P := lt_of_le_of_lt hN1
    ((le_max_left (p.N : ℝ) (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ)))).trans_lt
      hthreshold)
  have hγN : p.γ ≤ p.γ * (p.N : ℝ) := by
    nlinarith [p.hγ, hN1]
  have hγNP : p.γ * (p.N : ℝ) < P :=
    ((le_max_right (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))).trans
      (le_max_right (p.N : ℝ)
        (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))))).trans_lt hthreshold
  have hγP : p.γ ≤ P := hγN.trans hγNP.le
  have hu₀M : PositiveInitialDatum intervalDomainM u₀ := by
    simpa [intervalDomainM, intervalDomain] using hu₀
  have htraceM : InitialTrace intervalDomainM u₀ u := by
    simpa [intervalDomainM, intervalDomain] using htrace
  have hLpM : LpPowerBoundedBefore intervalDomainM P T u := by
    simpa [intervalDomainM, intervalDomain] using hLp
  have hbM := boundedBefore_of_lp_restarted_affine hu₀M
    (classicalSolution_intervalDomainM_of_m_eq_one hm hsol) htraceM hm hP hγP hLpM
  simpa [IsPaper2BoundedBefore, intervalDomainM, intervalDomain] using hbM

theorem boundedGlobal_of_lp_restarted_affine
    {p : CM2Params} {P C : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomainM p u v)
    (hm : p.m = 1) (hP : 1 < P) (hγP : p.γ ≤ P)
    (hpower : ∀ t, 0 < t →
      intervalDomainM.integral (fun z => (u t z) ^ P) ≤ C) :
    IsPaper2Bounded intervalDomainM u := by
  let w : ℝ := 1 / 2
  have hw : 0 < w := by norm_num [w]
  have hw1 : w ≤ 1 := by norm_num [w]
  let R : ℝ :=
    (fullHeatShortConstant * w ^ (-(1 / 2 : ℝ))) ^ (1 / P) *
        (C + 1) ^ (1 / P) +
      |p.χ₀| *
        (conjugateLpLinftyConstant P *
          ((2 * p.ν * (C + 1)) * (C + 1) ^ (1 / P)) *
          (w ^ (1 - conjugateLpLinftyTheta P) /
            (1 - conjugateLpLinftyTheta P))) +
      p.a * fullHeatShortConstant ^ (1 / P) * (C + 1) ^ (1 / P) *
        (w ^ (1 - 1 / (2 * P)) / (1 - 1 / (2 * P)))
  apply IsPaper2Bounded.of_forall_ge_supNorm_le (T := 2 * w) (M := R)
  intro t ht
  let T : ℝ := t + 1
  let a : ℝ := t - w
  have hT : 0 < T := by dsimp [T]; linarith
  have ha : 0 < a := by dsimp [a]; linarith
  have hahT : a + w < T := by dsimp [a, T]; linarith
  have hsol : IsPaper2ClassicalSolution intervalDomainM p T u v :=
    hglobal.classical hT
  have hpowerT : ∀ τ, 0 < τ → τ < T →
      intervalDomainM.integral (fun z => (u τ z) ^ P) ≤ C :=
    fun τ hτ _ => hpower τ hτ
  change intervalDomainSupNorm (u t) ≤ R
  unfold intervalDomainSupNorm
  apply csSup_le
  · let x₀ : intervalDomainPoint := ⟨0, ⟨le_rfl, zero_le_one⟩⟩
    exact ⟨|u t x₀|, ⟨x₀, rfl⟩⟩
  intro y hy
  obtain ⟨x, rfl⟩ := hy
  change |u t x| ≤ R
  have ht0 : 0 < t := lt_of_lt_of_le (by linarith [hw]) ht
  have htT : t < T := by dsimp [T]; linarith
  rw [abs_of_pos (u_pos hsol ht0 htT x)]
  have hslice := solutionSlice_le_of_restart_affine_lp
    hsol ha hw.le hahT hm hP hγP hpowerT hw le_rfl hw1 x.property
  have heq : intervalDomainLift (u (a + w)) x.1 = u t x := by
    dsimp [a]
    simp [intervalDomainLift]
  rw [← heq]
  simpa [R] using hslice

theorem critical_bounded_global_positive_restarted_affine
    {p : CM2Params}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hguard : p.a = 0 ∨ 0 < p.b)
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomainM p u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hbeta : 1 ≤ p.β) (hm : p.m = 1)
    (hchi : 0 < p.χ₀) (hthreshold : p.χ₀ < chiBeta p) :
    IsPaper2Bounded intervalDomainM u := by
  obtain ⟨P, hPmax, C, hpower⟩ := exists_critical_lp_above_gamma_global
    hguard hu₀ hglobal htrace hbeta hm hchi hthreshold
  exact boundedGlobal_of_lp_restarted_affine hglobal hm
    (lt_of_le_of_lt (le_max_left _ _) hPmax)
    (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hPmax)) hpower

#print axioms restartFluxM_lp_root_le_of_lp
#print axioms restartChemDuhamelM_abs_le_of_lp
#print axioms restartLogisticDuhamelM_le_of_lp
#print axioms solutionSlice_le_of_restart_affine_lp
#print axioms boundedBefore_of_lp_restarted_affine
#print axioms Proposition_2_5_intervalDomain_of_restarted_affine
#print axioms boundedGlobal_of_lp_restarted_affine
#print axioms critical_bounded_global_positive_restarted_affine

end ShenWork.Paper2.IntervalDomainRestartedLpLinfProducer
