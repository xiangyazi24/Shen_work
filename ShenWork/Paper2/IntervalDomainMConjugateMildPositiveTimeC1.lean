/-
  Uniform positive-time C1 bounds for the faithful conjugate mild solution.

  The fixed-slice C1 theorem is upgraded to a whole strip `[tau,T]`.  The
  chemotaxis Duhamel estimate uses one Holder modulus beginning at `tau/2`
  and the explicit early/late bound from `IntervalConjugateDuhamelSpatialC1`.
-/
import ShenWork.Paper2.IntervalDomainMConjugateMildChemFluxC1
import ShenWork.Paper2.IntervalCompactSliceGradientBounds
import ShenWork.Paper2.IntervalConjugateSemigroupComposition
import ShenWork.Paper2.ChemMildHolderBootstrap
import ShenWork.Paper2.ChemMildC1etaUncond

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace ShenWork.Paper2

open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalNeumannFullKernel
  (intervalFullSemigroupOperator intervalNeumannFullKernel weightedHeatHessConst)
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateKernelOperator)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.Paper2.IntervalDomainMConjugateDuhamelMap
  (chemFluxMLifted chemFluxMLifted_abs_le_of_pos_slice
   chemFluxMLifted_uncurry_measurable chemFluxMLifted_integrable_of_pos_slice
   chemFluxMLifted_continuousOn_Icc_of_pos_slice
   chemFluxMLifted_continuous_of_pos_slice
   chemFluxMLifted_endpoint_zero chemFluxMLifted_endpoint_one)
open ShenWork.Paper2.IntervalDomainMConjugatePicardFloorInhabit
  (ConjugateMildSolutionDataM)
open ShenWork.IntervalPositiveFloorNonlinearLipschitz
  (powerLip powerLip_nonneg)

/-- The lifted chemotaxis flux is itself the zero extension of an interval
function, so its `deriv` is zero away from the open interval (including the two
endpoints, where a failed two-sided derivative is represented by zero). -/
theorem chemFluxMLifted_deriv_eq_zero_off_Ioo
    (p : CM2Params) (w : intervalDomainPoint → ℝ) {y : ℝ}
    (hy : y ∉ Set.Ioo (0 : ℝ) 1) :
    deriv (chemFluxMLifted p w) y = 0 := by
  let F : intervalDomainPoint → ℝ := fun x =>
    w x ^ p.m * resolverGradReal p w x.1 /
      (1 + intervalDomainLift
        (ShenWork.PDE.intervalNeumannResolverR p w) x.1) ^ p.β
  have hflux_eq : chemFluxMLifted p w = intervalDomainLift F := by
    funext z
    by_cases hz : z ∈ Set.Icc (0 : ℝ) 1
    · simp [chemFluxMLifted, F, intervalDomainLift, hz]
    · simp [chemFluxMLifted, intervalDomainLift, hz,
        Real.zero_rpow p.hm.ne']
  let Wconst : ℝ → intervalDomainPoint → ℝ := fun _ => F
  rcases lt_or_ge y 0 with hy0 | hy0
  · have hzero : deriv (intervalDomainLift (Wconst 0)) y = 0 := by
      simpa [Wconst] using
        (ShenWork.Paper2.CompactSliceGradientBounds.deriv_lift_eq_zero_on_Iio
          Wconst 0 hy0)
    simpa [hflux_eq, Wconst] using hzero
  rcases lt_or_ge 1 y with hy1 | hy1
  · have hzero : deriv (intervalDomainLift (Wconst 0)) y = 0 := by
      simpa [Wconst] using
        (ShenWork.Paper2.CompactSliceGradientBounds.deriv_lift_eq_zero_on_Ioi
          Wconst 0 hy1)
    simpa [hflux_eq, Wconst] using hzero
  rcases eq_or_lt_of_le hy0 with hy_eq | hy_pos
  · subst y
    have hzero : deriv (intervalDomainLift (Wconst 0)) 0 = 0 := by
      simpa [Wconst] using
        (ShenWork.Paper2.CompactSliceGradientBounds.deriv_lift_eq_zero_at_left
          Wconst 0)
    simpa [hflux_eq, Wconst] using hzero
  rcases eq_or_lt_of_le hy1 with hy_eq | hy_lt_one
  · subst y
    have hzero : deriv (intervalDomainLift (Wconst 0)) 1 = 0 := by
      simpa [Wconst] using
        (ShenWork.Paper2.CompactSliceGradientBounds.deriv_lift_eq_zero_at_right
          Wconst 0)
    simpa [hflux_eq, Wconst] using hzero
  · exact False.elim (hy ⟨hy_pos, hy_lt_one⟩)

/-- The derivative integral in the actual chemotaxis Duhamel leg is uniformly
bounded on every closed positive-time strip. -/
theorem conjugateMildM_chemDuhamel_deriv_positiveTime_uniformBound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {θ τ : ℝ} (hθ0 : 0 < θ) (hθhalf : θ < (1 / 2 : ℝ)) (hτ : 0 < τ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, τ ≤ t → t ≤ D.T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |∫ s in (0 : ℝ)..t, deriv
          (fun z : ℝ => intervalConjugateKernelOperator (t - s)
            (chemFluxMLifted p (D.u s)) z) x| ≤ C := by
  have hcM : D.c ≤ D.M := D.floor_le_bound
  set CQ : ℝ := D.M ^ p.m * (Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * D.M ^ p.γ))) with hCQ
  have hCQ_nn : 0 ≤ CQ := by
    rw [hCQ]
    exact mul_nonneg (Real.rpow_nonneg D.hM.le _)
      (mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (by norm_num)
          (mul_nonneg p.hν.le (Real.rpow_nonneg D.hM.le _))))
  set F : ℝ → ℝ → ℝ := fun s y =>
    if 0 < s ∧ s ≤ D.T then chemFluxMLifted p (D.u s) y else 0 with hF
  have hF_eq : ∀ {s : ℝ}, 0 < s → s ≤ D.T →
      F s = chemFluxMLifted p (D.u s) := by
    intro s hs0 hsT
    funext y
    simp [hF, hs0, hsT]
  have hF_bound : ∀ s y, |F s y| ≤ CQ := by
    intro s y
    simp only [hF]
    split_ifs with hs
    · rw [hCQ]
      exact chemFluxMLifted_abs_le_of_pos_slice p D.hc hcM
        (D.hbound s hs.1 hs.2) (D.hfloor s hs.1 hs.2)
          (D.hcont s hs.1 hs.2) y
    · simpa using hCQ_nn
  have hF_meas : Measurable (Function.uncurry F) := by
    have hbase := chemFluxMLifted_uncurry_measurable
      (p := p) (u := D.u) D.hmeas
    simp only [hF]
    refine Measurable.ite ?_ hbase measurable_const
    exact ((isOpen_Ioi.preimage continuous_fst).measurableSet).inter
      ((isClosed_Iic.preimage continuous_fst).measurableSet)
  have hF_int : ∀ s, Integrable (F s) (intervalMeasure 1) := by
    intro s
    simp only [hF]
    split_ifs with hs
    · exact chemFluxMLifted_integrable_of_pos_slice p D.hc hcM
        (D.hbound s hs.1 hs.2) (D.hfloor s hs.1 hs.2)
          (D.hcont s hs.1 hs.2)
    · simp
  have hτ2 : 0 < τ / 2 := by positivity
  obtain ⟨HQ, hHQ_nn, hQholder⟩ :=
    conjugateMildM_chemFlux_positiveTime_holder D hu₀ hu₀_meas
      hθ0 hθhalf hτ2
  have hF0 : ∀ s, F s 0 = 0 := by
    intro s
    simp only [hF]
    split_ifs
    · exact chemFluxMLifted_endpoint_zero p (D.u s)
    · rfl
  have hF1 : ∀ s, F s 1 = 0 := by
    intro s
    simp only [hF]
    split_ifs
    · exact chemFluxMLifted_endpoint_one p (D.u s)
    · rfl
  set Cmix : ℝ := 5 * Real.sqrt 2 / 2 with hCmix
  set Clate : ℝ := 2 * HQ * weightedHeatHessConst θ with hClate
  set C : ℝ :=
    Cmix * (τ / 2) ^ (-(1 : ℝ)) * CQ * D.T +
      Clate * (D.T ^ (θ / 2 : ℝ) / (θ / 2)) with hC
  have hCmix_nn : 0 ≤ Cmix := by rw [hCmix]; positivity
  have hClate_nn : 0 ≤ Clate := by
    rw [hClate]
    exact mul_nonneg (mul_nonneg (by norm_num) hHQ_nn)
      (ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst_nonneg θ)
  have hC_nn : 0 ≤ C := by
    rw [hC]
    exact add_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg hCmix_nn (Real.rpow_nonneg hτ2.le _)) hCQ_nn)
        D.hT.le)
      (mul_nonneg hClate_nn
        (div_nonneg (Real.rpow_nonneg D.hT.le _) (by linarith)))
  refine ⟨C, hC_nn, ?_⟩
  intro t hτt htT x hx
  have ht : 0 < t := lt_of_lt_of_le hτ hτt
  have ht2 : 0 < t / 2 := by positivity
  have hF_cont : ∀ s, t / 2 < s → s < t →
      ContinuousOn (F s) (Set.Icc (0 : ℝ) 1) := by
    intro s hs2 hst
    have hs0 : 0 < s := lt_trans ht2 hs2
    have hsT : s ≤ D.T := (le_of_lt hst).trans htT
    rw [hF_eq hs0 hsT]
    exact chemFluxMLifted_continuousOn_Icc_of_pos_slice p D.hc hcM
      (D.hbound s hs0 hsT) (D.hfloor s hs0 hsT) (D.hcont s hs0 hsT)
  have hF_holder : ∀ s, t / 2 < s → s < t →
      ∀ a b : ℝ, a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
        |F s a - F s b| ≤ HQ * |a - b| ^ θ := by
    intro s hs2 hst a b ha hb
    have hs0 : 0 < s := lt_trans ht2 hs2
    have hsT : s ≤ D.T := (le_of_lt hst).trans htT
    rw [hF_eq hs0 hsT]
    exact hQholder s ⟨by linarith [hτt], hsT⟩ a b ha hb
  have hraw :=
    ShenWork.IntervalNeumannFullKernel.intervalConjugateDuhamel_deriv_integral_abs_le_of_late_holder
      ht hθ0 (by linarith : θ < 1) hCQ_nn hHQ_nn hF_meas hF_int hF_bound
        hF_cont hF_holder hF0 hF1 x hx
  have hder_eq :
      (∫ s in (0 : ℝ)..t, deriv
        (fun z : ℝ => intervalConjugateKernelOperator (t - s)
          (chemFluxMLifted p (D.u s)) z) x) =
      ∫ s in (0 : ℝ)..t, deriv
        (fun z : ℝ => intervalConjugateKernelOperator (t - s) (F s) z) x := by
    apply intervalIntegral.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro s hs
    rw [Set.uIoc_of_le ht.le] at hs
    rw [hF_eq hs.1 (hs.2.trans htT)]
  rw [hder_eq]
  refine hraw.trans ?_
  have hpow_early :
      (t / 2) ^ (-(1 : ℝ)) ≤ (τ / 2) ^ (-(1 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hτ2 (by linarith) (by norm_num)
  have hA :
      Cmix * (t / 2) ^ (-(1 : ℝ)) * CQ ≤
        Cmix * (τ / 2) ^ (-(1 : ℝ)) * CQ := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow_early hCmix_nn) hCQ_nn
  have hearly :
      Cmix * (t / 2) ^ (-(1 : ℝ)) * CQ * t ≤
        Cmix * (τ / 2) ^ (-(1 : ℝ)) * CQ * D.T :=
    mul_le_mul hA htT ht.le
      (mul_nonneg (mul_nonneg hCmix_nn (Real.rpow_nonneg hτ2.le _)) hCQ_nn)
  have htpow : t ^ (θ / 2 : ℝ) ≤ D.T ^ (θ / 2 : ℝ) :=
    Real.rpow_le_rpow ht.le htT (by linarith)
  have hratio :
      t ^ (θ / 2 : ℝ) / (θ / 2) ≤
        D.T ^ (θ / 2 : ℝ) / (θ / 2) :=
    div_le_div_of_nonneg_right htpow (by linarith)
  have hlate :
      Clate * (t ^ (θ / 2 : ℝ) / (θ / 2)) ≤
        Clate * (D.T ^ (θ / 2 : ℝ) / (θ / 2)) :=
    mul_le_mul_of_nonneg_left hratio hClate_nn
  rw [← hCmix, ← hClate, hC]
  exact add_le_add hearly hlate

/-- The spatial derivative of the faithful mild solution is uniformly bounded
on every closed positive-time strip. -/
theorem conjugateMildM_intervalDomainLift_deriv_positiveTime_uniformBound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, τ ≤ t → t ≤ D.T →
      ∀ x ∈ Set.Ioo (0 : ℝ) 1,
        |deriv (intervalDomainLift (D.u t)) x| ≤ C := by
  obtain ⟨Cchem, hCchem, hchem_bound⟩ :=
    conjugateMildM_chemDuhamel_deriv_positiveTime_uniformBound
      D hu₀ hu₀_meas (θ := (1 / 4 : ℝ))
        (by norm_num) (by norm_num) hτ
  set Cinit : ℝ :=
    ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
      τ ^ (-(1 / 2) : ℝ) * D.M with hCinit
  set CL : ℝ := D.M * (p.a + p.b * D.M ^ p.α) with hCL
  set Creact : ℝ :=
    ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
      (2 * Real.sqrt D.T) * CL with hCreact
  set C : ℝ := Cinit + |p.χ₀| * Cchem + Creact with hC
  have hCinit_nn : 0 ≤ Cinit := by
    rw [hCinit]
    exact mul_nonneg
      (mul_nonneg
        ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
        (Real.rpow_nonneg hτ.le _)) D.hM.le
  have hCL_nn : 0 ≤ CL := by
    rw [hCL]
    exact mul_nonneg D.hM.le
      (add_nonneg p.ha (mul_nonneg p.hb (Real.rpow_nonneg D.hM.le _)))
  have hCreact_nn : 0 ≤ Creact := by
    rw [hCreact]
    exact mul_nonneg
      (mul_nonneg
        ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
        (mul_nonneg (by norm_num) (Real.sqrt_nonneg D.T))) hCL_nn
  have hC_nn : 0 ≤ C := by
    rw [hC]
    exact add_nonneg
      (add_nonneg hCinit_nn (mul_nonneg (abs_nonneg _) hCchem)) hCreact_nn
  refine ⟨C, hC_nn, ?_⟩
  intro t hτt htT x hx
  have ht : 0 < t := lt_of_lt_of_le hτ hτt
  have hwhole := conjugateMildM_intervalDomainLift_hasDerivAt_interior
    D hu₀ hu₀_meas (θ := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
      ht htT hx
  have hinit :=
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_hasDerivAt_fst
      ht hu₀_meas hu₀ x
  have hinit_raw :=
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_deriv_Linfty_pointwise_sqrt_t
      ht hu₀_meas hu₀ x
  rw [hinit.deriv] at hinit_raw
  have hpow : t ^ (-(1 / 2) : ℝ) ≤ τ ^ (-(1 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hτ hτt (by norm_num)
  have hinit_bound :
      |∫ y, deriv (fun z : ℝ => intervalNeumannFullKernel t z y) x *
          intervalDomainLift u₀ y ∂(intervalMeasure 1)| ≤ Cinit := by
    refine hinit_raw.trans ?_
    rw [hCinit]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow
        ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg)
      D.hM.le
  have hchem_bound_x := hchem_bound t hτt htT x (Set.Ioo_subset_Icc_self hx)
  have hreact_raw := conjugateMildM_logisticDuhamel_deriv_abs_le D ht htT (x := x)
  have hsqrt : Real.sqrt t ≤ Real.sqrt D.T := Real.sqrt_le_sqrt htT
  have hreact_bound :
      |∫ s in (0 : ℝ)..t, deriv
        (fun z : ℝ => intervalFullSemigroupOperator (t - s)
          (logisticLifted p (D.u s)) z) x| ≤ Creact := by
    refine hreact_raw.trans ?_
    rw [hCreact, hCL]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsqrt (by norm_num))
        ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg)
      hCL_nn
  rw [hwhole.deriv]
  calc
    |(∫ y, deriv (fun z : ℝ => intervalNeumannFullKernel t z y) x *
          intervalDomainLift u₀ y ∂(intervalMeasure 1))
        + (-p.χ₀) * (∫ s in (0 : ℝ)..t, deriv
            (fun z : ℝ => intervalConjugateKernelOperator (t - s)
              (chemFluxMLifted p (D.u s)) z) x)
        + ∫ s in (0 : ℝ)..t, deriv
            (fun z : ℝ => intervalFullSemigroupOperator (t - s)
              (logisticLifted p (D.u s)) z) x|
        ≤ |∫ y, deriv (fun z : ℝ => intervalNeumannFullKernel t z y) x *
              intervalDomainLift u₀ y ∂(intervalMeasure 1)|
          + |(-p.χ₀) * (∫ s in (0 : ℝ)..t, deriv
              (fun z : ℝ => intervalConjugateKernelOperator (t - s)
                (chemFluxMLifted p (D.u s)) z) x)|
          + |∫ s in (0 : ℝ)..t, deriv
              (fun z : ℝ => intervalFullSemigroupOperator (t - s)
                (logisticLifted p (D.u s)) z) x| := by
            linarith [abs_add_le
              ((∫ y, deriv (fun z : ℝ => intervalNeumannFullKernel t z y) x *
                intervalDomainLift u₀ y ∂(intervalMeasure 1)) +
                  (-p.χ₀) * (∫ s in (0 : ℝ)..t, deriv
                    (fun z : ℝ => intervalConjugateKernelOperator (t - s)
                      (chemFluxMLifted p (D.u s)) z) x))
              (∫ s in (0 : ℝ)..t, deriv
                (fun z : ℝ => intervalFullSemigroupOperator (t - s)
                  (logisticLifted p (D.u s)) z) x),
              abs_add_le
                (∫ y, deriv (fun z : ℝ => intervalNeumannFullKernel t z y) x *
                  intervalDomainLift u₀ y ∂(intervalMeasure 1))
                ((-p.χ₀) * (∫ s in (0 : ℝ)..t, deriv
                  (fun z : ℝ => intervalConjugateKernelOperator (t - s)
                    (chemFluxMLifted p (D.u s)) z) x))]
    _ ≤ Cinit + |p.χ₀| * Cchem + Creact := by
      rw [abs_mul, abs_neg]
      exact add_le_add (add_le_add hinit_bound
        (mul_le_mul_of_nonneg_left hchem_bound_x (abs_nonneg _))) hreact_bound
    _ = C := hC.symm

/-- The derivative of the actual chemotaxis flux is uniformly bounded on every
closed positive-time strip. -/
theorem conjugateMildM_chemFlux_deriv_positiveTime_uniformBound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, τ ≤ t → t ≤ D.T →
      ∀ x ∈ Set.Ioo (0 : ℝ) 1,
        |deriv (chemFluxMLifted p (D.u t)) x| ≤ C := by
  obtain ⟨CU, hCU, hUbound⟩ :=
    conjugateMildM_intervalDomainLift_deriv_positiveTime_uniformBound
      D hu₀ hu₀_meas hτ
  set G0 : ℝ := Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * D.M ^ p.γ)) with hG0
  set L0 : ℝ := ShenWork.IntervalResolverWeakBounds.resolverWeakLapBound p D.M
    with hL0
  have hcM : D.c ≤ D.M := D.floor_le_bound
  set Lm : ℝ := powerLip p.m D.c D.M with hLm
  set A : ℝ := D.M ^ p.m with hA
  set C : ℝ := (Lm * CU) * G0 + A * L0 + A * G0 * p.β * G0 with hC
  have hG0_nn : 0 ≤ G0 := by
    rw [hG0]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num)
        (mul_nonneg p.hν.le (Real.rpow_nonneg D.hM.le _)))
  have hL0_nn : 0 ≤ L0 := by
    rw [hL0, ShenWork.IntervalResolverWeakBounds.resolverWeakLapBound,
      ShenWork.IntervalResolverWeakBounds.resolverWeakValueBound]
    exact add_nonneg
      (mul_nonneg p.hμ.le
        (mul_nonneg (Real.sqrt_nonneg _)
          (mul_nonneg (by norm_num)
            (mul_nonneg p.hν.le (Real.rpow_nonneg D.hM.le _)))))
      (mul_nonneg p.hν.le (Real.rpow_nonneg D.hM.le _))
  have hLm_nn : 0 ≤ Lm := by
    rw [hLm]
    exact powerLip_nonneg p.hm D.hc hcM
  have hA_nn : 0 ≤ A := by
    rw [hA]
    exact Real.rpow_nonneg D.hM.le _
  have hC_nn : 0 ≤ C := by
    rw [hC]
    exact add_nonneg
      (add_nonneg (mul_nonneg (mul_nonneg hLm_nn hCU) hG0_nn)
        (mul_nonneg hA_nn hL0_nn))
      (mul_nonneg (mul_nonneg (mul_nonneg hA_nn hG0_nn) p.hβ) hG0_nn)
  refine ⟨C, hC_nn, ?_⟩
  intro t hτt htT x hx
  have ht : 0 < t := lt_of_lt_of_le hτ hτt
  let U : ℝ → ℝ := intervalDomainLift (D.u t)
  let G : ℝ → ℝ := resolverGradReal p (D.u t)
  let R : ℝ → ℝ :=
    intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p (D.u t))
  let W : ℝ → ℝ := fun z => (1 + R z) ^ (-p.β)
  have hxIcc := Set.Ioo_subset_Icc_self hx
  have hUcont : ContinuousOn U (Set.Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    have heq : Set.restrict (Set.Icc (0 : ℝ) 1) U = D.u t := by
      ext ⟨z, hz⟩
      simp [Set.restrict, U, intervalDomainLift, hz]
      rfl
    rw [heq]
    exact D.hcont t ht htT
  have hUraw := conjugateMildM_intervalDomainLift_hasDerivAt_interior
    D hu₀ hu₀_meas (θ := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
      ht htT hx
  have hU' : HasDerivAt U (deriv U x) x := by
    simpa [U] using hUraw.differentiableAt.hasDerivAt
  have hGraw :=
    ShenWork.IntervalResolverWeakBounds.resolverGradReal_hasDerivAt_physicalLap_of_continuousOn
      p hUcont (fun z hz => by
        have h := D.hc.le.trans (D.hfloor t ht htT ⟨z, hz⟩)
        simpa [U, intervalDomainLift, hz] using h) hx
  have hG' : HasDerivAt G (deriv G x) x := by
    simpa [G] using hGraw.differentiableAt.hasDerivAt
  have hR' : HasDerivAt R (G x) x := by
    simpa [R, G] using
      ShenWork.IntervalResolverWeakBounds.intervalNeumannResolverR_lift_hasDerivAt_resolverGradReal_of_continuousOn
        p hUcont hx
  have hR_nonneg : 0 ≤ R x := by
    have h := ShenWork.IntervalMildToClassical.mildChemical_nonneg
      (T := D.T) p (u := D.u)
        (fun s hs hsT y => D.hc.le.trans (D.hfloor s hs hsT y))
        D.hcont ht htT ⟨x, hxIcc⟩
    simpa [R, ShenWork.IntervalMildToClassical.mildChemicalConcentration,
      intervalDomainLift, hxIcc] using h
  have hW' : HasDerivAt W
      (G x * (-p.β) * (1 + R x) ^ (-p.β - 1)) x := by
    have hbase : HasDerivAt (fun z : ℝ => 1 + R z) (G x) x :=
      hR'.const_add 1
    simpa [W, sub_eq_add_neg] using
      hbase.rpow_const (p := -p.β) (Or.inl (by linarith : 1 + R x ≠ 0))
  have hUx_pos : 0 < U x := by
    simpa [U, intervalDomainLift, hxIcc] using
      D.hc.trans_le (D.hfloor t ht htT ⟨x, hxIcc⟩)
  have hUx_floor : D.c ≤ U x := by
    simpa [U, intervalDomainLift, hxIcc] using
      D.hfloor t ht htT ⟨x, hxIcc⟩
  have hUx_le : U x ≤ D.M := by
    simpa [U, intervalDomainLift, hxIcc] using
      (abs_le.mp (D.hbound t ht htT ⟨x, hxIcc⟩)).2
  have hUm' : HasDerivAt (fun z => U z ^ p.m)
      ((p.m * U x ^ (p.m - 1)) * deriv U x) x := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      hU'.rpow_const (p := p.m) (Or.inl hUx_pos.ne')
  have hprod := (hUm'.mul hG').mul hW'
  have hev : chemFluxMLifted p (D.u t) =ᶠ[𝓝 x]
      (fun z => U z ^ p.m * G z * W z) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with z hz
    have hzIcc := Set.Ioo_subset_Icc_self hz
    have hRz_nonneg : 0 ≤ R z := by
      have h := ShenWork.IntervalMildToClassical.mildChemical_nonneg
        (T := D.T) p (u := D.u)
          (fun s hs hsT y => D.hc.le.trans (D.hfloor s hs hsT y))
          D.hcont ht htT ⟨z, hzIcc⟩
      simpa [R, ShenWork.IntervalMildToClassical.mildChemicalConcentration,
        intervalDomainLift, hzIcc] using h
    unfold chemFluxMLifted
    rw [div_eq_mul_inv, ← Real.rpow_neg (by linarith : 0 ≤ 1 + R z)]
  have hflux := hev.hasDerivAt_iff.mpr hprod
  have hU_deriv : |deriv U x| ≤ CU := by
    simpa [U] using hUbound t hτt htT x hx
  have hpow_bound : U x ^ (p.m - 1) ≤
      D.c ^ (p.m - 1) + D.M ^ (p.m - 1) := by
    rcases le_or_gt 1 p.m with hm1 | hm1
    · have hmono : U x ^ (p.m - 1) ≤ D.M ^ (p.m - 1) :=
        Real.rpow_le_rpow hUx_pos.le hUx_le (by linarith)
      linarith [Real.rpow_nonneg D.hc.le (p.m - 1)]
    · have hmono : U x ^ (p.m - 1) ≤ D.c ^ (p.m - 1) :=
        Real.rpow_le_rpow_of_nonpos D.hc hUx_floor (by linarith)
      linarith [Real.rpow_nonneg D.hM.le (p.m - 1)]
  have hcoeff : |p.m * U x ^ (p.m - 1)| ≤ Lm := by
    rw [hLm, powerLip, abs_of_nonneg
      (mul_nonneg p.hm.le (Real.rpow_nonneg hUx_pos.le _))]
    exact mul_le_mul_of_nonneg_left hpow_bound p.hm.le
  have hUm_abs : |U x ^ p.m| ≤ A := by
    rw [abs_of_nonneg (Real.rpow_nonneg hUx_pos.le _), hA]
    exact Real.rpow_le_rpow hUx_pos.le hUx_le p.hm.le
  have hUm_deriv : |(p.m * U x ^ (p.m - 1)) * deriv U x| ≤ Lm * CU := by
    rw [abs_mul]
    exact mul_le_mul hcoeff hU_deriv (abs_nonneg _) hLm_nn
  simp only [abs_mul] at hUm_deriv
  have hG_abs : |G x| ≤ G0 := by
    rw [hG0]
    exact ShenWork.IntervalResolverWeakBounds.resolverGrad_sup_le_of_bounded
      p hUcont
        (fun z hz => by
          have h := D.hc.le.trans (D.hfloor t ht htT ⟨z, hz⟩)
          simpa [U, intervalDomainLift, hz] using h)
        (fun z hz => by
          have h := D.hbound t ht htT ⟨z, hz⟩
          simpa [U, intervalDomainLift, hz] using (abs_le.mp h).2)
        hxIcc
  have hG_deriv : |deriv G x| ≤ L0 := by
    rw [hL0]
    simpa [G] using
      ShenWork.IntervalResolverWeakBounds.deriv_resolverGradReal_abs_le_of_bounded
        p hUcont
          (fun z hz => by
            have h := D.hc.le.trans (D.hfloor t ht htT ⟨z, hz⟩)
            simpa [U, intervalDomainLift, hz] using h)
          (fun z hz => by
            have h := D.hbound t ht htT ⟨z, hz⟩
            simpa [U, intervalDomainLift, hz] using (abs_le.mp h).2)
          hx
  have hW_abs : |W x| ≤ 1 := by
    have hW_nn : 0 ≤ W x := Real.rpow_nonneg (by linarith : 0 ≤ 1 + R x) _
    rw [abs_of_nonneg hW_nn]
    dsimp [W]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith [p.hβ])
  have hW_deriv_abs :
      |G x * (-p.β) * (1 + R x) ^ (-p.β - 1)| ≤ p.β * G0 := by
    have hpow_nn : 0 ≤ (1 + R x) ^ (-p.β - 1) :=
      Real.rpow_nonneg (by linarith : 0 ≤ 1 + R x) _
    have hpow_le : (1 + R x) ^ (-p.β - 1) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith [p.hβ])
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg p.hβ, abs_of_nonneg hpow_nn]
    have hGpβ : |G x| * p.β ≤ G0 * p.β :=
      mul_le_mul_of_nonneg_right hG_abs p.hβ
    calc
      |G x| * p.β * (1 + R x) ^ (-p.β - 1)
          ≤ G0 * p.β * (1 + R x) ^ (-p.β - 1) :=
        mul_le_mul_of_nonneg_right hGpβ hpow_nn
      _ ≤ G0 * p.β * 1 :=
        mul_le_mul_of_nonneg_left hpow_le (mul_nonneg hG0_nn p.hβ)
      _ = p.β * G0 := by ring
  rw [hflux.deriv, hC]
  calc
    |(((p.m * U x ^ (p.m - 1)) * deriv U x) * G x +
          U x ^ p.m * deriv G x) * W x +
        U x ^ p.m * G x *
          (G x * (-p.β) * (1 + R x) ^ (-p.β - 1))|
      ≤ |(((p.m * U x ^ (p.m - 1)) * deriv U x) * G x +
            U x ^ p.m * deriv G x) * W x| +
          |U x ^ p.m * G x *
            (G x * (-p.β) * (1 + R x) ^ (-p.β - 1))| :=
        abs_add_le _ _
    _ ≤ ((Lm * CU) * G0 + A * L0) * 1 + A * G0 * (p.β * G0) := by
      have hsum : |((p.m * U x ^ (p.m - 1)) * deriv U x) * G x +
          U x ^ p.m * deriv G x| ≤ (Lm * CU) * G0 + A * L0 := by
        calc
          |((p.m * U x ^ (p.m - 1)) * deriv U x) * G x +
              U x ^ p.m * deriv G x|
              ≤ |((p.m * U x ^ (p.m - 1)) * deriv U x) * G x| +
                |U x ^ p.m * deriv G x| := abs_add_le _ _
          _ ≤ (Lm * CU) * G0 + A * L0 := by
            simp only [abs_mul]
            exact add_le_add
              (mul_le_mul hUm_deriv hG_abs (abs_nonneg _)
                (mul_nonneg hLm_nn hCU))
              (mul_le_mul hUm_abs hG_deriv (abs_nonneg _) hA_nn)
      have hsum_nn : 0 ≤ (Lm * CU) * G0 + A * L0 :=
        add_nonneg (mul_nonneg (mul_nonneg hLm_nn hCU) hG0_nn)
          (mul_nonneg hA_nn hL0_nn)
      have hUG_nn : 0 ≤ A * G0 := mul_nonneg hA_nn hG0_nn
      have hfirst :
          |(((p.m * U x ^ (p.m - 1)) * deriv U x) * G x +
              U x ^ p.m * deriv G x) * W x| ≤
            ((Lm * CU) * G0 + A * L0) * 1 := by
        rw [abs_mul]
        exact mul_le_mul hsum hW_abs (abs_nonneg _) hsum_nn
      have hUG : |U x ^ p.m| * |G x| ≤ A * G0 :=
        mul_le_mul hUm_abs hG_abs (abs_nonneg _) hA_nn
      have hsecond :
          |U x ^ p.m * G x *
              (G x * (-p.β) * (1 + R x) ^ (-p.β - 1))| ≤
            A * G0 * (p.β * G0) := by
        rw [abs_mul, abs_mul]
        exact mul_le_mul hUG hW_deriv_abs (abs_nonneg _) hUG_nn
      exact add_le_add hfirst hsecond
    _ = (Lm * CU) * G0 + A * L0 + A * G0 * p.β * G0 := by ring

/-- At each positive time, the spatial derivative of the actual chemotaxis
Duhamel leg is Holder on the open interval.  Early source times use the
conjugate semigroup split; late source times use the flux IBP identity and the
uniform positive-time flux-derivative bound. -/
theorem conjugateMildM_chemDuhamel_deriv_holder_interior
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {t eta : ℝ} (ht : 0 < t) (htT : t ≤ D.T)
    (heta0 : 0 < eta) (heta1 : eta < 1) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      ∀ y ∈ Set.Ioo (0 : ℝ) 1,
        |(∫ s in (0 : ℝ)..t, deriv
            (fun z : ℝ => intervalConjugateKernelOperator (t - s)
              (chemFluxMLifted p (D.u s)) z) x) -
          (∫ s in (0 : ℝ)..t, deriv
            (fun z : ℝ => intervalConjugateKernelOperator (t - s)
              (chemFluxMLifted p (D.u s)) z) y)| ≤
        H * |x - y| ^ eta := by
  have hcM : D.c ≤ D.M := D.floor_le_bound
  set CQ : ℝ := D.M ^ p.m * (Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * D.M ^ p.γ))) with hCQ
  have hCQ_nn : 0 ≤ CQ := by
    rw [hCQ]
    exact mul_nonneg (Real.rpow_nonneg D.hM.le _)
      (mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (by norm_num)
          (mul_nonneg p.hν.le (Real.rpow_nonneg D.hM.le _))))
  set F : ℝ → ℝ → ℝ := fun s z =>
    if 0 < s ∧ s ≤ D.T then chemFluxMLifted p (D.u s) z else 0 with hF
  have hF_eq : ∀ {s : ℝ}, 0 < s → s ≤ D.T →
      F s = chemFluxMLifted p (D.u s) := by
    intro s hs0 hsT
    funext z
    simp [hF, hs0, hsT]
  have hF_bound : ∀ s z, |F s z| ≤ CQ := by
    intro s z
    simp only [hF]
    split_ifs with hs
    · rw [hCQ]
      exact chemFluxMLifted_abs_le_of_pos_slice p D.hc hcM
        (D.hbound s hs.1 hs.2) (D.hfloor s hs.1 hs.2)
          (D.hcont s hs.1 hs.2) z
    · simpa using hCQ_nn
  have hF_meas : Measurable (Function.uncurry F) := by
    have hbase := chemFluxMLifted_uncurry_measurable
      (p := p) (u := D.u) D.hmeas
    simp only [hF]
    refine Measurable.ite ?_ hbase measurable_const
    exact ((isOpen_Ioi.preimage continuous_fst).measurableSet).inter
      ((isClosed_Iic.preimage continuous_fst).measurableSet)
  have hF_int : ∀ s, Integrable (F s) (intervalMeasure 1) := by
    intro s
    simp only [hF]
    split_ifs with hs
    · exact chemFluxMLifted_integrable_of_pos_slice p D.hc hcM
        (D.hbound s hs.1 hs.2) (D.hfloor s hs.1 hs.2)
          (D.hcont s hs.1 hs.2)
    · simp
  have ht2 : 0 < t / 2 := by positivity
  have ht4 : 0 < t / 4 := by positivity
  obtain ⟨HQ, hHQ_nn, hQholder⟩ :=
    conjugateMildM_chemFlux_positiveTime_holder D hu₀ hu₀_meas
      (θ := (1 / 4 : ℝ)) (by norm_num) (by norm_num) ht2
  obtain ⟨CQd, hCQd_nn, hQderiv_bound_strip⟩ :=
    conjugateMildM_chemFlux_deriv_positiveTime_uniformBound
      D hu₀ hu₀_meas ht2
  have hF_cont : ∀ s, t / 2 < s → s < t →
      ContinuousOn (F s) (Set.Icc (0 : ℝ) 1) := by
    intro s hs2 hst
    have hs0 : 0 < s := lt_trans ht2 hs2
    have hsT : s ≤ D.T := (le_of_lt hst).trans htT
    rw [hF_eq hs0 hsT]
    exact chemFluxMLifted_continuousOn_Icc_of_pos_slice p D.hc hcM
      (D.hbound s hs0 hsT) (D.hfloor s hs0 hsT) (D.hcont s hs0 hsT)
  have hF_holder : ∀ s, t / 2 < s → s < t →
      ∀ a b : ℝ, a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
        |F s a - F s b| ≤ HQ * |a - b| ^ (1 / 4 : ℝ) := by
    intro s hs2 hst a b ha hb
    have hs0 : 0 < s := lt_trans ht2 hs2
    have hsT : s ≤ D.T := (le_of_lt hst).trans htT
    rw [hF_eq hs0 hsT]
    exact hQholder s ⟨le_of_lt hs2, hsT⟩ a b ha hb
  have hF0 : ∀ s, F s 0 = 0 := by
    intro s
    simp only [hF]
    split_ifs
    · exact chemFluxMLifted_endpoint_zero p (D.u s)
    · rfl
  have hF1 : ∀ s, F s 1 = 0 := by
    intro s
    simp only [hF]
    split_ifs
    · exact chemFluxMLifted_endpoint_one p (D.u s)
    · rfl
  have hder_int : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      IntervalIntegrable
        (fun s : ℝ => deriv
          (fun z : ℝ => intervalConjugateKernelOperator (t - s) (F s) z) x)
        volume 0 t :=
    ShenWork.IntervalNeumannFullKernel.intervalConjugateDuhamel_deriv_intervalIntegrable_of_late_holder
      ht (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1)
        hCQ_nn hHQ_nn hF_meas hF_int hF_bound hF_cont hF_holder hF0 hF1
  set Aeta : ℝ := (2 : ℝ) ^ (1 - eta) *
    (secondDerivSmoothingConst ^ eta * gradSmoothingConst ^ (1 - eta)) with hAeta
  set Cearly : ℝ := Aeta * (t / 4) ^ (-((1 + eta) / 2) : ℝ) *
    (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
      (t / 4) ^ (-(1 / 2) : ℝ) * CQ) with hCearly
  set Clate : ℝ := Aeta * CQd with hClate
  set phi : ℝ → ℝ := fun s =>
    Cearly + Clate * (t - s) ^ (-((1 + eta) / 2) : ℝ) with hphi
  have hAeta_nn : 0 ≤ Aeta := by
    rw [hAeta]
    exact mul_nonneg
      (Real.rpow_nonneg (by norm_num) _)
      (mul_nonneg (Real.rpow_nonneg secondDerivSmoothingConst_nonneg _)
        (Real.rpow_nonneg gradSmoothingConst_nonneg _))
  have hCearly_nn : 0 ≤ Cearly := by
    rw [hCearly]
    exact mul_nonneg
      (mul_nonneg hAeta_nn (Real.rpow_nonneg ht4.le _))
      (mul_nonneg
        (mul_nonneg
          ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
          (Real.rpow_nonneg ht4.le _)) hCQ_nn)
  have hClate_nn : 0 ≤ Clate := mul_nonneg hAeta_nn hCQd_nn
  have hphi_int : IntervalIntegrable phi volume 0 t := by
    rw [hphi]
    have hc : IntervalIntegrable (fun _ : ℝ => Cearly) volume 0 t :=
      intervalIntegrable_const
    have hl := (duhamel_holder_gradTime_integrand_integrable ht heta0 heta1).const_mul
      Clate
    exact hc.add hl
  have hpoint : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ y ∈ Set.Ioo (0 : ℝ) 1,
        |deriv (fun z : ℝ => intervalConjugateKernelOperator (t - s) (F s) z) x -
          deriv (fun z : ℝ => intervalConjugateKernelOperator (t - s) (F s) z) y| ≤
            phi s * |x - y| ^ eta := by
    intro s hs x hx y hy
    have hsT : s ≤ D.T := (le_of_lt hs.2).trans htT
    have hFs_eq := hF_eq hs.1 hsT
    have hQcont : Continuous (F s) := by
      rw [hFs_eq]
      exact chemFluxMLifted_continuous_of_pos_slice p D.hc hcM
        (D.hbound s hs.1 hsT) (D.hfloor s hs.1 hsT) (D.hcont s hs.1 hsT)
    rcases le_or_gt s (t / 2) with hs_early | hs_late
    · have hlag : 0 < t - s := sub_pos.mpr hs.2
      have hhalfpos : 0 < (t - s) / 2 := by positivity
      have hraw := intervalConjugateKernelOperator_deriv_holder_of_split
        hlag heta0 heta1 hQcont (hF_int s) (hF_bound s) hx hy
      have hhalf_ge : t / 4 ≤ (t - s) / 2 := by linarith
      have hp1 :
          ((t - s) / 2) ^ (-((1 + eta) / 2) : ℝ) ≤
            (t / 4) ^ (-((1 + eta) / 2) : ℝ) :=
        Real.rpow_le_rpow_of_nonpos ht4 hhalf_ge (by linarith)
      have hp2 :
          ((t - s) / 2) ^ (-(1 / 2) : ℝ) ≤
            (t / 4) ^ (-(1 / 2) : ℝ) :=
        Real.rpow_le_rpow_of_nonpos ht4 hhalf_ge (by norm_num)
      have hgrad_nn :
          0 ≤ ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant :=
        ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
      have hinner :
          ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
              ((t - s) / 2) ^ (-(1 / 2) : ℝ) * CQ ≤
            ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
              (t / 4) ^ (-(1 / 2) : ℝ) * CQ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hp2 hgrad_nn) hCQ_nn
      have hcoef :
          Aeta * ((t - s) / 2) ^ (-((1 + eta) / 2) : ℝ) *
            (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
                ((t - s) / 2) ^ (-(1 / 2) : ℝ) * CQ) ≤ Cearly := by
        rw [hCearly]
        have hinner_nn :
            0 ≤ ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
              ((t - s) / 2) ^ (-(1 / 2) : ℝ) * CQ :=
          mul_nonneg
            (mul_nonneg hgrad_nn (Real.rpow_nonneg hhalfpos.le _)) hCQ_nn
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hp1 hAeta_nn) hinner
          hinner_nn
          (mul_nonneg hAeta_nn (Real.rpow_nonneg ht4.le _))
      have hearly := hraw.trans
        (mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (abs_nonneg _) _))
      rw [hphi]
      exact hearly.trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right
          (mul_nonneg hClate_nn (Real.rpow_nonneg (sub_nonneg.mpr hs.2.le) _)))
          (Real.rpow_nonneg (abs_nonneg _) _))
    · have hs2le : t / 2 ≤ s := le_of_lt hs_late
      have hQderiv : ∀ z ∈ Set.Ioo (0 : ℝ) 1,
          HasDerivAt (F s) (deriv (F s) z) z := by
        intro z hz
        rw [hFs_eq]
        exact (conjugateMildM_chemFlux_differentiableAt_interior
          D hu₀ hu₀_meas hs.1 hsT hz).hasDerivAt
      have hQderiv_int : IntervalIntegrable (deriv (F s)) volume 0 1 := by
        rw [hFs_eq]
        exact conjugateMildM_chemFlux_deriv_intervalIntegrable
          D hu₀ hu₀_meas hs.1 hsT
      have hQderiv_bound : ∀ z, |deriv (F s) z| ≤ CQd := by
        intro z
        rw [hFs_eq]
        by_cases hz : z ∈ Set.Ioo (0 : ℝ) 1
        · exact hQderiv_bound_strip s hs2le hsT z hz
        · rw [chemFluxMLifted_deriv_eq_zero_off_Ioo p (D.u s) hz, abs_zero]
          exact hCQd_nn
      have hraw := intervalConjugateKernelOperator_deriv_holder_of_deriv
        (sub_pos.mpr hs.2) heta0 heta1 hQcont hQderiv hQderiv_int
          (by
            rw [hFs_eq]
            exact chemFluxMLifted_endpoint_zero
              p (D.u s))
          (by
            rw [hFs_eq]
            exact chemFluxMLifted_endpoint_one
              p (D.u s))
          hQderiv_bound hx hy
      have hlate :
          |deriv (fun z : ℝ => intervalConjugateKernelOperator (t - s) (F s) z) x -
            deriv (fun z : ℝ => intervalConjugateKernelOperator (t - s) (F s) z) y| ≤
              Clate * (t - s) ^ (-((1 + eta) / 2) : ℝ) * |x - y| ^ eta := by
        rw [hClate, hAeta]
        convert hraw using 1 <;> ring
      rw [hphi]
      exact hlate.trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCearly_nn)
          (Real.rpow_nonneg (abs_nonneg _) _))
  set H : ℝ := ∫ s in (0 : ℝ)..t, phi s with hH
  have hH_nn : 0 ≤ H := by
    rw [hH]
    refine intervalIntegral.integral_nonneg ht.le (fun s hs => ?_)
    rw [hphi]
    exact add_nonneg hCearly_nn
      (mul_nonneg hClate_nn (Real.rpow_nonneg (by linarith [hs.2] : 0 ≤ t - s) _))
  refine ⟨H, hH_nn, ?_⟩
  intro x hx y hy
  have hbound_ae : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)),
      |deriv (fun z : ℝ => intervalConjugateKernelOperator (t - s) (F s) z) x -
        deriv (fun z : ℝ => intervalConjugateKernelOperator (t - s) (F s) z) y| ≤
          phi s * |x - y| ^ eta := by
    rw [ae_restrict_iff' measurableSet_Icc]
    have hne0 : ∀ᵐ s : ℝ ∂volume, s ≠ 0 := by
      rw [ae_iff]
      simp only [not_not, Set.setOf_eq_eq_singleton]
      exact Real.volume_singleton
    have hnet : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
      rw [ae_iff]
      simp only [not_not, Set.setOf_eq_eq_singleton]
      exact Real.volume_singleton
    filter_upwards [hne0, hnet] with s hs0 hst hs
    exact hpoint s ⟨lt_of_le_of_ne hs.1 hs0.symm, lt_of_le_of_ne hs.2 hst⟩
      x hx y hy
  have hholder := holder_of_duhamel_integral ht.le
    (hder_int x (Set.Ioo_subset_Icc_self hx))
    (hder_int y (Set.Ioo_subset_Icc_self hy)) hphi_int hbound_ae
  have hder_eq : ∀ z,
      (∫ s in (0 : ℝ)..t, deriv
        (fun w : ℝ => intervalConjugateKernelOperator (t - s)
          (chemFluxMLifted p (D.u s)) w) z) =
      ∫ s in (0 : ℝ)..t, deriv
        (fun w : ℝ => intervalConjugateKernelOperator (t - s) (F s) w) z := by
    intro z
    apply intervalIntegral.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro s hs
    rw [Set.uIoc_of_le ht.le] at hs
    rw [hF_eq hs.1 (hs.2.trans htT)]
  rw [hder_eq x, hder_eq y, hH]
  exact hholder

/-- On every closed positive-time strip, one Holder constant controls the
spatial derivative of the actual chemotaxis Duhamel leg. -/
theorem conjugateMildM_chemDuhamel_deriv_positiveTime_holder_uniform
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {τ eta : ℝ} (hτ : 0 < τ) (heta0 : 0 < eta) (heta1 : eta < 1) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ t, τ ≤ t → t ≤ D.T →
      ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ y ∈ Set.Ioo (0 : ℝ) 1,
        |(∫ s in (0 : ℝ)..t, deriv
            (fun z : ℝ => intervalConjugateKernelOperator (t - s)
              (chemFluxMLifted p (D.u s)) z) x) -
          (∫ s in (0 : ℝ)..t, deriv
            (fun z : ℝ => intervalConjugateKernelOperator (t - s)
              (chemFluxMLifted p (D.u s)) z) y)| ≤
        H * |x - y| ^ eta := by
  have hcM : D.c ≤ D.M := D.floor_le_bound
  set CQ : ℝ := D.M ^ p.m * (Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * D.M ^ p.γ))) with hCQ
  have hCQ_nn : 0 ≤ CQ := by
    rw [hCQ]
    exact mul_nonneg (Real.rpow_nonneg D.hM.le _)
      (mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (by norm_num)
          (mul_nonneg p.hν.le (Real.rpow_nonneg D.hM.le _))))
  set F : ℝ → ℝ → ℝ := fun s z =>
    if 0 < s ∧ s ≤ D.T then chemFluxMLifted p (D.u s) z else 0 with hF
  have hF_eq : ∀ {s : ℝ}, 0 < s → s ≤ D.T →
      F s = chemFluxMLifted p (D.u s) := by
    intro s hs0 hsT
    funext z
    simp [hF, hs0, hsT]
  have hF_bound : ∀ s z, |F s z| ≤ CQ := by
    intro s z
    simp only [hF]
    split_ifs with hs
    · rw [hCQ]
      exact chemFluxMLifted_abs_le_of_pos_slice p D.hc hcM
        (D.hbound s hs.1 hs.2) (D.hfloor s hs.1 hs.2)
          (D.hcont s hs.1 hs.2) z
    · simpa using hCQ_nn
  have hF_meas : Measurable (Function.uncurry F) := by
    have hbase := chemFluxMLifted_uncurry_measurable
      (p := p) (u := D.u) D.hmeas
    simp only [hF]
    refine Measurable.ite ?_ hbase measurable_const
    exact ((isOpen_Ioi.preimage continuous_fst).measurableSet).inter
      ((isClosed_Iic.preimage continuous_fst).measurableSet)
  have hF_int : ∀ s, Integrable (F s) (intervalMeasure 1) := by
    intro s
    simp only [hF]
    split_ifs with hs
    · exact chemFluxMLifted_integrable_of_pos_slice p D.hc hcM
        (D.hbound s hs.1 hs.2) (D.hfloor s hs.1 hs.2)
          (D.hcont s hs.1 hs.2)
    · simp
  have hτ2 : 0 < τ / 2 := by positivity
  have hτ4 : 0 < τ / 4 := by positivity
  obtain ⟨HQ, hHQ_nn, hQholder⟩ :=
    conjugateMildM_chemFlux_positiveTime_holder D hu₀ hu₀_meas
      (θ := (1 / 4 : ℝ)) (by norm_num) (by norm_num) hτ2
  obtain ⟨CQd, hCQd_nn, hQderiv_bound_strip⟩ :=
    conjugateMildM_chemFlux_deriv_positiveTime_uniformBound
      D hu₀ hu₀_meas hτ2
  have hF0 : ∀ s, F s 0 = 0 := by
    intro s
    simp only [hF]
    split_ifs
    · exact chemFluxMLifted_endpoint_zero p (D.u s)
    · rfl
  have hF1 : ∀ s, F s 1 = 0 := by
    intro s
    simp only [hF]
    split_ifs
    · exact chemFluxMLifted_endpoint_one p (D.u s)
    · rfl
  set Aeta : ℝ := (2 : ℝ) ^ (1 - eta) *
    (secondDerivSmoothingConst ^ eta * gradSmoothingConst ^ (1 - eta)) with hAeta
  set Cearly : ℝ := Aeta * (τ / 4) ^ (-((1 + eta) / 2) : ℝ) *
    (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
      (τ / 4) ^ (-(1 / 2) : ℝ) * CQ) with hCearly
  set Clate : ℝ := Aeta * CQd with hClate
  set UB : ℝ :=
    D.T ^ (-((1 + eta) / 2) + 1) / (-((1 + eta) / 2) + 1) with hUB
  set H : ℝ := Cearly * D.T + Clate * UB with hH
  have hAeta_nn : 0 ≤ Aeta := by
    rw [hAeta]
    exact mul_nonneg
      (Real.rpow_nonneg (by norm_num) _)
      (mul_nonneg (Real.rpow_nonneg secondDerivSmoothingConst_nonneg _)
        (Real.rpow_nonneg gradSmoothingConst_nonneg _))
  have hCearly_nn : 0 ≤ Cearly := by
    rw [hCearly]
    exact mul_nonneg
      (mul_nonneg hAeta_nn (Real.rpow_nonneg hτ4.le _))
      (mul_nonneg
        (mul_nonneg
          ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
          (Real.rpow_nonneg hτ4.le _)) hCQ_nn)
  have hClate_nn : 0 ≤ Clate := mul_nonneg hAeta_nn hCQd_nn
  have hUB_nn : 0 ≤ UB := by
    rw [hUB]
    exact div_nonneg (Real.rpow_nonneg D.hT.le _) (by linarith)
  have hH_nn : 0 ≤ H := by
    rw [hH]
    exact add_nonneg (mul_nonneg hCearly_nn D.hT.le)
      (mul_nonneg hClate_nn hUB_nn)
  refine ⟨H, hH_nn, ?_⟩
  intro t hτt htT x hx y hy
  have ht : 0 < t := lt_of_lt_of_le hτ hτt
  have hF_cont : ∀ s, t / 2 < s → s < t →
      ContinuousOn (F s) (Set.Icc (0 : ℝ) 1) := by
    intro s hs2 hst
    have hs0 : 0 < s := by linarith
    have hsT : s ≤ D.T := (le_of_lt hst).trans htT
    rw [hF_eq hs0 hsT]
    exact chemFluxMLifted_continuousOn_Icc_of_pos_slice p D.hc hcM
      (D.hbound s hs0 hsT) (D.hfloor s hs0 hsT) (D.hcont s hs0 hsT)
  have hF_holder : ∀ s, t / 2 < s → s < t →
      ∀ a b : ℝ, a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
        |F s a - F s b| ≤ HQ * |a - b| ^ (1 / 4 : ℝ) := by
    intro s hs2 hst a b ha hb
    have hs0 : 0 < s := by linarith
    have hsT : s ≤ D.T := (le_of_lt hst).trans htT
    rw [hF_eq hs0 hsT]
    exact hQholder s ⟨by linarith, hsT⟩ a b ha hb
  have hder_int : ∀ z ∈ Set.Icc (0 : ℝ) 1,
      IntervalIntegrable
        (fun s : ℝ => deriv
          (fun w : ℝ => intervalConjugateKernelOperator (t - s) (F s) w) z)
        volume 0 t :=
    ShenWork.IntervalNeumannFullKernel.intervalConjugateDuhamel_deriv_intervalIntegrable_of_late_holder
      ht (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1)
        hCQ_nn hHQ_nn hF_meas hF_int hF_bound hF_cont hF_holder hF0 hF1
  set phi : ℝ → ℝ := fun s =>
    Cearly + Clate * (t - s) ^ (-((1 + eta) / 2) : ℝ) with hphi
  have hphi_int : IntervalIntegrable phi volume 0 t := by
    rw [hphi]
    have hc : IntervalIntegrable (fun _ : ℝ => Cearly) volume 0 t :=
      intervalIntegrable_const
    have hl := (duhamel_holder_gradTime_integrand_integrable ht heta0 heta1).const_mul
      Clate
    exact hc.add hl
  have hpoint : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      ∀ a ∈ Set.Ioo (0 : ℝ) 1, ∀ b ∈ Set.Ioo (0 : ℝ) 1,
        |deriv (fun z : ℝ => intervalConjugateKernelOperator (t - s) (F s) z) a -
          deriv (fun z : ℝ => intervalConjugateKernelOperator (t - s) (F s) z) b| ≤
            phi s * |a - b| ^ eta := by
    intro s hs a ha b hb
    have hsT : s ≤ D.T := (le_of_lt hs.2).trans htT
    have hFs_eq := hF_eq hs.1 hsT
    have hQcont : Continuous (F s) := by
      rw [hFs_eq]
      exact chemFluxMLifted_continuous_of_pos_slice p D.hc hcM
        (D.hbound s hs.1 hsT) (D.hfloor s hs.1 hsT) (D.hcont s hs.1 hsT)
    rcases le_or_gt s (t / 2) with hs_early | hs_late
    · have hlag : 0 < t - s := sub_pos.mpr hs.2
      have hhalfpos : 0 < (t - s) / 2 := by positivity
      have hraw := intervalConjugateKernelOperator_deriv_holder_of_split
        hlag heta0 heta1 hQcont (hF_int s) (hF_bound s) ha hb
      have hhalf_ge : τ / 4 ≤ (t - s) / 2 := by linarith
      have hp1 :
          ((t - s) / 2) ^ (-((1 + eta) / 2) : ℝ) ≤
            (τ / 4) ^ (-((1 + eta) / 2) : ℝ) :=
        Real.rpow_le_rpow_of_nonpos hτ4 hhalf_ge (by linarith)
      have hp2 :
          ((t - s) / 2) ^ (-(1 / 2) : ℝ) ≤
            (τ / 4) ^ (-(1 / 2) : ℝ) :=
        Real.rpow_le_rpow_of_nonpos hτ4 hhalf_ge (by norm_num)
      have hgrad_nn :
          0 ≤ ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant :=
        ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
      have hinner :
          ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
              ((t - s) / 2) ^ (-(1 / 2) : ℝ) * CQ ≤
            ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
              (τ / 4) ^ (-(1 / 2) : ℝ) * CQ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hp2 hgrad_nn) hCQ_nn
      have hcoef :
          Aeta * ((t - s) / 2) ^ (-((1 + eta) / 2) : ℝ) *
            (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
                ((t - s) / 2) ^ (-(1 / 2) : ℝ) * CQ) ≤ Cearly := by
        rw [hCearly]
        have hinner_nn :
            0 ≤ ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
              ((t - s) / 2) ^ (-(1 / 2) : ℝ) * CQ :=
          mul_nonneg
            (mul_nonneg hgrad_nn (Real.rpow_nonneg hhalfpos.le _)) hCQ_nn
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hp1 hAeta_nn) hinner
          hinner_nn
          (mul_nonneg hAeta_nn (Real.rpow_nonneg hτ4.le _))
      have hearly := hraw.trans
        (mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (abs_nonneg _) _))
      rw [hphi]
      exact hearly.trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right
          (mul_nonneg hClate_nn (Real.rpow_nonneg (sub_nonneg.mpr hs.2.le) _)))
          (Real.rpow_nonneg (abs_nonneg _) _))
    · have hs2le : t / 2 ≤ s := le_of_lt hs_late
      have hQderiv : ∀ z ∈ Set.Ioo (0 : ℝ) 1,
          HasDerivAt (F s) (deriv (F s) z) z := by
        intro z hz
        rw [hFs_eq]
        exact (conjugateMildM_chemFlux_differentiableAt_interior
          D hu₀ hu₀_meas hs.1 hsT hz).hasDerivAt
      have hQderiv_int : IntervalIntegrable (deriv (F s)) volume 0 1 := by
        rw [hFs_eq]
        exact conjugateMildM_chemFlux_deriv_intervalIntegrable
          D hu₀ hu₀_meas hs.1 hsT
      have hQderiv_bound : ∀ z, |deriv (F s) z| ≤ CQd := by
        intro z
        rw [hFs_eq]
        by_cases hz : z ∈ Set.Ioo (0 : ℝ) 1
        · exact hQderiv_bound_strip s (by linarith) hsT z hz
        · rw [chemFluxMLifted_deriv_eq_zero_off_Ioo p (D.u s) hz, abs_zero]
          exact hCQd_nn
      have hraw := intervalConjugateKernelOperator_deriv_holder_of_deriv
        (sub_pos.mpr hs.2) heta0 heta1 hQcont hQderiv hQderiv_int
          (by
            rw [hFs_eq]
            exact chemFluxMLifted_endpoint_zero
              p (D.u s))
          (by
            rw [hFs_eq]
            exact chemFluxMLifted_endpoint_one
              p (D.u s))
          hQderiv_bound ha hb
      have hlate :
          |deriv (fun z : ℝ => intervalConjugateKernelOperator (t - s) (F s) z) a -
            deriv (fun z : ℝ => intervalConjugateKernelOperator (t - s) (F s) z) b| ≤
              Clate * (t - s) ^ (-((1 + eta) / 2) : ℝ) * |a - b| ^ eta := by
        rw [hClate, hAeta]
        convert hraw using 1 <;> ring
      rw [hphi]
      exact hlate.trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCearly_nn)
          (Real.rpow_nonneg (abs_nonneg _) _))
  have hbound_ae : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)),
      |deriv (fun z : ℝ => intervalConjugateKernelOperator (t - s) (F s) z) x -
        deriv (fun z : ℝ => intervalConjugateKernelOperator (t - s) (F s) z) y| ≤
          phi s * |x - y| ^ eta := by
    rw [ae_restrict_iff' measurableSet_Icc]
    have hne0 : ∀ᵐ s : ℝ ∂volume, s ≠ 0 := by
      rw [ae_iff]
      simp only [not_not, Set.setOf_eq_eq_singleton]
      exact Real.volume_singleton
    have hnet : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
      rw [ae_iff]
      simp only [not_not, Set.setOf_eq_eq_singleton]
      exact Real.volume_singleton
    filter_upwards [hne0, hnet] with s hs0 hst hs
    exact hpoint s ⟨lt_of_le_of_ne hs.1 hs0.symm, lt_of_le_of_ne hs.2 hst⟩
      x hx y hy
  have hholder := holder_of_duhamel_integral ht.le
    (hder_int x (Set.Ioo_subset_Icc_self hx))
    (hder_int y (Set.Ioo_subset_Icc_self hy)) hphi_int hbound_ae
  have hder_eq : ∀ z,
      (∫ s in (0 : ℝ)..t, deriv
        (fun w : ℝ => intervalConjugateKernelOperator (t - s)
          (chemFluxMLifted p (D.u s)) w) z) =
      ∫ s in (0 : ℝ)..t, deriv
        (fun w : ℝ => intervalConjugateKernelOperator (t - s) (F s) w) z := by
    intro z
    apply intervalIntegral.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro s hs
    rw [Set.uIoc_of_le ht.le] at hs
    rw [hF_eq hs.1 (hs.2.trans htT)]
  have hphi_le : (∫ s in (0 : ℝ)..t, phi s) ≤ H := by
    have hpow_int := duhamel_holder_gradTime_integrand_integrable ht heta0 heta1
    have heq :
        (∫ s in (0 : ℝ)..t, phi s) =
          Cearly * t + Clate *
            (∫ s in (0 : ℝ)..t, (t - s) ^ (-((1 + eta) / 2) : ℝ)) := by
      rw [hphi, intervalIntegral.integral_add intervalIntegrable_const
        (hpow_int.const_mul Clate), intervalIntegral.integral_const,
        intervalIntegral.integral_const_mul]
      simp only [smul_eq_mul]
      ring
    rw [heq, hH]
    exact add_le_add
      (mul_le_mul_of_nonneg_left htT hCearly_nn)
      (mul_le_mul_of_nonneg_left
        (by
          rw [hUB]
          exact duhamel_gradTime_integral_le ht.le htT heta1)
        hClate_nn)
  rw [hder_eq x, hder_eq y]
  exact hholder.trans
    (mul_le_mul_of_nonneg_right hphi_le (Real.rpow_nonneg (abs_nonneg _) _))

/-- Every positive-time faithful mild slice is spatially `C1,eta` on the open
interval: its actual interior derivative has a power Holder modulus. -/
theorem conjugateMildM_intervalDomainLift_deriv_holder_interior
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {t eta : ℝ} (ht : 0 < t) (htT : t ≤ D.T)
    (heta0 : 0 < eta) (heta1 : eta < 1) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      ∀ y ∈ Set.Ioo (0 : ℝ) 1,
        |deriv (intervalDomainLift (D.u t)) x -
          deriv (intervalDomainLift (D.u t)) y| ≤ H * |x - y| ^ eta := by
  obtain ⟨Hchem, hHchem_nn, hchem_holder⟩ :=
    conjugateMildM_chemDuhamel_deriv_holder_interior
      D hu₀ hu₀_meas ht htT heta0 heta1
  set CL : ℝ := D.M * (p.a + p.b * D.M ^ p.α) with hCL
  have hCL_nn : 0 ≤ CL := by
    rw [hCL]
    exact logisticCutoffSource_boundConst_nonneg (p := p) D.hM
  set Hinit : ℝ := initialValueLegDerivHolderConst t eta D.M with hHinit
  set Hreact : ℝ := reactionDerivLegHolderConst t eta CL with hHreact
  set H : ℝ := Hinit + |p.χ₀| * Hchem + Hreact with hH
  have hHinit_nn : 0 ≤ Hinit := by
    rw [hHinit]
    exact initialValueLegDerivHolderConst_nonneg ht D.hM.le
  have hHreact_nn : 0 ≤ Hreact := by
    rw [hHreact]
    exact reactionDerivLegHolderConst_nonneg ht hCL_nn
  have hH_nn : 0 ≤ H := by
    rw [hH]
    exact add_nonneg
      (add_nonneg hHinit_nn (mul_nonneg (abs_nonneg _) hHchem_nn)) hHreact_nn
  let I : ℝ → ℝ := fun x =>
    ∫ y, deriv (fun z : ℝ => intervalNeumannFullKernel t z y) x *
      intervalDomainLift u₀ y ∂(intervalMeasure 1)
  let Cleg : ℝ → ℝ := fun x =>
    ∫ s in (0 : ℝ)..t, deriv
      (fun z : ℝ => intervalConjugateKernelOperator (t - s)
        (chemFluxMLifted p (D.u s)) z) x
  let Rleg : ℝ → ℝ := fun x =>
    ∫ s in (0 : ℝ)..t, deriv
      (fun z : ℝ => intervalFullSemigroupOperator (t - s)
        (logisticLifted p (D.u s)) z) x
  have hwhole_deriv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      deriv (intervalDomainLift (D.u t)) x =
        I x + (-p.χ₀) * Cleg x + Rleg x := by
    intro x hx
    have hwhole := conjugateMildM_intervalDomainLift_hasDerivAt_interior
      D hu₀ hu₀_meas (θ := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
        ht htT hx
    simpa [I, Cleg, Rleg] using hwhole.deriv
  let L : ℝ → ℝ → ℝ := logisticCutoffSource p D.u D.T
  have hL_meas : Measurable (Function.uncurry L) := by
    simpa [L] using logisticCutoffSource_measurable
      (p := p) (u := D.u) (T := D.T) D.hmeas
  have hL_bound : ∀ s y, |L s y| ≤ CL := by
    intro s y
    dsimp [L]
    rw [hCL]
    exact logisticCutoffSource_bound (p := p) (u := D.u)
      (T := D.T) D.hM D.hbound s y
  have hreact_eq : ∀ x, reactionDerivLeg t L x = Rleg x := by
    intro x
    unfold reactionDerivLeg
    dsimp [Rleg]
    apply intervalIntegral.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro s hs
    rw [Set.uIoc_of_le ht.le] at hs
    have hsT : s ≤ D.T := hs.2.trans htT
    have heq : L s = logisticLifted p (D.u s) := by
      funext y
      simp [L, logisticCutoffSource, hs.1, hsT]
    rw [heq]
  refine ⟨H, hH_nn, ?_⟩
  intro x hx y hy
  have hxIcc := Set.Ioo_subset_Icc_self hx
  have hyIcc := Set.Ioo_subset_Icc_self hy
  have hsx :=
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_hasDerivAt_fst
      ht hu₀_meas hu₀ x
  have hsy :=
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_hasDerivAt_fst
      ht hu₀_meas hu₀ y
  have hsx_eq :
      deriv (fun z : ℝ => intervalFullSemigroupOperator t (intervalDomainLift u₀) z) x =
        I x := by
    simpa [I] using hsx.deriv
  have hsy_eq :
      deriv (fun z : ℝ => intervalFullSemigroupOperator t (intervalDomainLift u₀) z) y =
        I y := by
    simpa [I] using hsy.deriv
  have hinit_holder : |I x - I y| ≤ Hinit * |x - y| ^ eta := by
    have hraw := initialValueLeg_deriv_holder_Icc
      ht heta0 heta1 hu₀_meas hu₀ x hxIcc y hyIcc
    change
      |deriv (fun z : ℝ => intervalFullSemigroupOperator t
          (intervalDomainLift u₀) z) x -
        deriv (fun z : ℝ => intervalFullSemigroupOperator t
          (intervalDomainLift u₀) z) y| ≤
        initialValueLegDerivHolderConst t eta D.M * |x - y| ^ eta at hraw
    rw [hsx_eq, hsy_eq, ← hHinit] at hraw
    exact hraw
  have hreact_holder : |Rleg x - Rleg y| ≤ Hreact * |x - y| ^ eta := by
    have hraw := reactionDerivLeg_holder_Icc
      ht heta0 heta1 hL_meas hCL_nn hL_bound x hxIcc y hyIcc
    rw [hreact_eq x, hreact_eq y, ← hHreact] at hraw
    exact hraw
  have hchem := hchem_holder x hx y hy
  rw [hwhole_deriv x hx, hwhole_deriv y hy]
  calc
    |(I x + (-p.χ₀) * Cleg x + Rleg x) -
        (I y + (-p.χ₀) * Cleg y + Rleg y)|
        = |(I x - I y) + (-p.χ₀) * (Cleg x - Cleg y) +
            (Rleg x - Rleg y)| := by ring_nf
    _ ≤ |I x - I y| + |(-p.χ₀) * (Cleg x - Cleg y)| +
          |Rleg x - Rleg y| := by
        linarith [abs_add_le ((I x - I y) + (-p.χ₀) * (Cleg x - Cleg y))
          (Rleg x - Rleg y),
          abs_add_le (I x - I y) ((-p.χ₀) * (Cleg x - Cleg y))]
    _ ≤ Hinit * |x - y| ^ eta + |p.χ₀| * (Hchem * |x - y| ^ eta) +
          Hreact * |x - y| ^ eta := by
        rw [abs_mul, abs_neg]
        exact add_le_add (add_le_add hinit_holder
          (mul_le_mul_of_nonneg_left hchem (abs_nonneg _))) hreact_holder
    _ = H * |x - y| ^ eta := by rw [hH]; ring

/-- The actual spatial derivative has one power-Holder modulus on every closed
positive-time strip. -/
theorem conjugateMildM_intervalDomainLift_deriv_positiveTime_holder_uniform
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {τ eta : ℝ} (hτ : 0 < τ) (heta0 : 0 < eta) (heta1 : eta < 1) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ t, τ ≤ t → t ≤ D.T →
      ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ y ∈ Set.Ioo (0 : ℝ) 1,
        |deriv (intervalDomainLift (D.u t)) x -
          deriv (intervalDomainLift (D.u t)) y| ≤ H * |x - y| ^ eta := by
  obtain ⟨Hchem, hHchem_nn, hchem_holder⟩ :=
    conjugateMildM_chemDuhamel_deriv_positiveTime_holder_uniform
      D hu₀ hu₀_meas hτ heta0 heta1
  set CL : ℝ := D.M * (p.a + p.b * D.M ^ p.α) with hCL
  have hCL_nn : 0 ≤ CL := by
    rw [hCL]
    exact logisticCutoffSource_boundConst_nonneg (p := p) D.hM
  set Aeta : ℝ := (2 : ℝ) ^ (1 - eta) *
    (secondDerivSmoothingConst ^ eta * gradSmoothingConst ^ (1 - eta)) with hAeta
  set UB : ℝ :=
    D.T ^ (-((1 + eta) / 2) + 1) / (-((1 + eta) / 2) + 1) with hUB
  set Hinit : ℝ := Aeta * τ ^ (-((1 + eta) / 2) : ℝ) * D.M with hHinit
  set Hreact : ℝ := Aeta * CL * UB with hHreact
  set H : ℝ := Hinit + |p.χ₀| * Hchem + Hreact with hH
  have hAeta_nn : 0 ≤ Aeta := by
    rw [hAeta]
    exact mul_nonneg
      (Real.rpow_nonneg (by norm_num) _)
      (mul_nonneg (Real.rpow_nonneg secondDerivSmoothingConst_nonneg _)
        (Real.rpow_nonneg gradSmoothingConst_nonneg _))
  have hUB_nn : 0 ≤ UB := by
    rw [hUB]
    exact div_nonneg (Real.rpow_nonneg D.hT.le _) (by linarith)
  have hHinit_nn : 0 ≤ Hinit := by
    rw [hHinit]
    exact mul_nonneg
      (mul_nonneg hAeta_nn (Real.rpow_nonneg hτ.le _)) D.hM.le
  have hHreact_nn : 0 ≤ Hreact := by
    rw [hHreact]
    exact mul_nonneg (mul_nonneg hAeta_nn hCL_nn) hUB_nn
  have hH_nn : 0 ≤ H := by
    rw [hH]
    exact add_nonneg
      (add_nonneg hHinit_nn (mul_nonneg (abs_nonneg _) hHchem_nn)) hHreact_nn
  let L : ℝ → ℝ → ℝ := logisticCutoffSource p D.u D.T
  have hL_meas : Measurable (Function.uncurry L) := by
    simpa [L] using logisticCutoffSource_measurable
      (p := p) (u := D.u) (T := D.T) D.hmeas
  have hL_bound : ∀ s y, |L s y| ≤ CL := by
    intro s y
    dsimp [L]
    rw [hCL]
    exact logisticCutoffSource_bound (p := p) (u := D.u)
      (T := D.T) D.hM D.hbound s y
  refine ⟨H, hH_nn, ?_⟩
  intro t hτt htT x hx y hy
  have ht : 0 < t := lt_of_lt_of_le hτ hτt
  let I : ℝ → ℝ := fun z =>
    ∫ w, deriv (fun q : ℝ => intervalNeumannFullKernel t q w) z *
      intervalDomainLift u₀ w ∂(intervalMeasure 1)
  let Cleg : ℝ → ℝ := fun z =>
    ∫ s in (0 : ℝ)..t, deriv
      (fun w : ℝ => intervalConjugateKernelOperator (t - s)
        (chemFluxMLifted p (D.u s)) w) z
  let Rleg : ℝ → ℝ := fun z =>
    ∫ s in (0 : ℝ)..t, deriv
      (fun w : ℝ => intervalFullSemigroupOperator (t - s)
        (logisticLifted p (D.u s)) w) z
  have hwhole_deriv : ∀ z ∈ Set.Ioo (0 : ℝ) 1,
      deriv (intervalDomainLift (D.u t)) z =
        I z + (-p.χ₀) * Cleg z + Rleg z := by
    intro z hz
    have hwhole := conjugateMildM_intervalDomainLift_hasDerivAt_interior
      D hu₀ hu₀_meas (θ := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
        ht htT hz
    simpa [I, Cleg, Rleg] using hwhole.deriv
  have hreact_eq : ∀ z, reactionDerivLeg t L z = Rleg z := by
    intro z
    unfold reactionDerivLeg
    dsimp [Rleg]
    apply intervalIntegral.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro s hs
    rw [Set.uIoc_of_le ht.le] at hs
    have hsT : s ≤ D.T := hs.2.trans htT
    have heq : L s = logisticLifted p (D.u s) := by
      funext w
      simp [L, logisticCutoffSource, hs.1, hsT]
    rw [heq]
  have hxIcc := Set.Ioo_subset_Icc_self hx
  have hyIcc := Set.Ioo_subset_Icc_self hy
  have hsx :=
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_hasDerivAt_fst
      ht hu₀_meas hu₀ x
  have hsy :=
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_hasDerivAt_fst
      ht hu₀_meas hu₀ y
  have hsx_eq :
      deriv (fun z : ℝ => intervalFullSemigroupOperator t (intervalDomainLift u₀) z) x =
        I x := by
    simpa [I] using hsx.deriv
  have hsy_eq :
      deriv (fun z : ℝ => intervalFullSemigroupOperator t (intervalDomainLift u₀) z) y =
        I y := by
    simpa [I] using hsy.deriv
  have hinit_const_le :
      initialValueLegDerivHolderConst t eta D.M ≤ Hinit := by
    have hpow :
        t ^ (-((1 + eta) / 2) : ℝ) ≤
          τ ^ (-((1 + eta) / 2) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hτ hτt (by linarith)
    rw [initialValueLegDerivHolderConst, hHinit, hAeta]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow hAeta_nn) D.hM.le
  have hreact_const_le : reactionDerivLegHolderConst t eta CL ≤ Hreact := by
    have hpow_int := duhamel_holder_gradTime_integrand_integrable ht heta0 heta1
    have heq :
        reactionDerivLegHolderConst t eta CL =
          Aeta * CL *
            (∫ s in (0 : ℝ)..t, (t - s) ^ (-((1 + eta) / 2) : ℝ)) := by
      unfold reactionDerivLegHolderConst
      rw [show
          (fun s : ℝ => (2 : ℝ) ^ (1 - eta) *
              (secondDerivSmoothingConst ^ eta * gradSmoothingConst ^ (1 - eta)) *
                (t - s) ^ (-((1 + eta) / 2) : ℝ) * CL) =
            (fun s : ℝ => (Aeta * CL) *
              (t - s) ^ (-((1 + eta) / 2) : ℝ)) by
          funext s
          rw [hAeta]
          ring,
        intervalIntegral.integral_const_mul]
    rw [heq, hHreact]
    exact mul_le_mul_of_nonneg_left
      (by
        rw [hUB]
        exact duhamel_gradTime_integral_le ht.le htT heta1)
      (mul_nonneg hAeta_nn hCL_nn)
  have hinit_holder : |I x - I y| ≤ Hinit * |x - y| ^ eta := by
    have hraw := initialValueLeg_deriv_holder_Icc
      ht heta0 heta1 hu₀_meas hu₀ x hxIcc y hyIcc
    change
      |deriv (fun z : ℝ => intervalFullSemigroupOperator t
          (intervalDomainLift u₀) z) x -
        deriv (fun z : ℝ => intervalFullSemigroupOperator t
          (intervalDomainLift u₀) z) y| ≤
        initialValueLegDerivHolderConst t eta D.M * |x - y| ^ eta at hraw
    rw [hsx_eq, hsy_eq] at hraw
    exact hraw.trans
      (mul_le_mul_of_nonneg_right hinit_const_le
        (Real.rpow_nonneg (abs_nonneg _) _))
  have hreact_holder : |Rleg x - Rleg y| ≤ Hreact * |x - y| ^ eta := by
    have hraw := reactionDerivLeg_holder_Icc
      ht heta0 heta1 hL_meas hCL_nn hL_bound x hxIcc y hyIcc
    rw [hreact_eq x, hreact_eq y] at hraw
    exact hraw.trans
      (mul_le_mul_of_nonneg_right hreact_const_le
        (Real.rpow_nonneg (abs_nonneg _) _))
  have hchem := hchem_holder t hτt htT x hx y hy
  rw [hwhole_deriv x hx, hwhole_deriv y hy]
  calc
    |(I x + (-p.χ₀) * Cleg x + Rleg x) -
        (I y + (-p.χ₀) * Cleg y + Rleg y)|
        = |(I x - I y) + (-p.χ₀) * (Cleg x - Cleg y) +
            (Rleg x - Rleg y)| := by ring_nf
    _ ≤ |I x - I y| + |(-p.χ₀) * (Cleg x - Cleg y)| +
          |Rleg x - Rleg y| := by
        linarith [abs_add_le ((I x - I y) + (-p.χ₀) * (Cleg x - Cleg y))
          (Rleg x - Rleg y),
          abs_add_le (I x - I y) ((-p.χ₀) * (Cleg x - Cleg y))]
    _ ≤ Hinit * |x - y| ^ eta + |p.χ₀| * (Hchem * |x - y| ^ eta) +
          Hreact * |x - y| ^ eta := by
        rw [abs_mul, abs_neg]
        exact add_le_add (add_le_add hinit_holder
          (mul_le_mul_of_nonneg_left hchem (abs_nonneg _))) hreact_holder
    _ = H * |x - y| ^ eta := by rw [hH]; ring

end ShenWork.Paper2

#print axioms ShenWork.Paper2.conjugateMildM_chemFlux_deriv_positiveTime_uniformBound
#print axioms ShenWork.Paper2.conjugateMildM_intervalDomainLift_deriv_positiveTime_holder_uniform
