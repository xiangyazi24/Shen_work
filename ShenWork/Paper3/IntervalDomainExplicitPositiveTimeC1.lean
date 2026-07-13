/- Explicit, trajectory-independent positive-time C1 constants. -/
import ShenWork.Paper3.IntervalDomainExplicitPositiveTimeHolder

namespace ShenWork.Paper3

open MeasureTheory Filter Set Topology
open ShenWork.IntervalDomain
  (intervalMeasure intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel
  (intervalFullSemigroupOperator intervalNeumannFullKernel
    weightedHeatHessConst)
open ShenWork.IntervalGradientDuhamelMap
  (chemFluxLifted logisticLifted)
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateKernelOperator)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildSolutionData)
open ShenWork.HeatKernelGradientEstimates
  (heatGradientLinftyLinftyConstant heatGradientLinftyLinftyConstant_nonneg)
open ShenWork.Paper2

noncomputable section

/-- Explicit uniform bound for the differentiated chemotaxis Duhamel leg. -/
def paper3ChemDuhamelDerivPositiveTimeConstant
    (p : CM2Params) (M T theta tau : ℝ) : ℝ :=
  let CQ := M * (Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * M ^ p.γ)))
  let HQ := paper3ChemFluxPositiveTimeHolderConstant
    p M T theta (tau / 2)
  let Cmix := 5 * Real.sqrt 2 / 2
  let Clate := 2 * HQ * weightedHeatHessConst theta
  Cmix * (tau / 2) ^ (-(1 : ℝ)) * CQ * T +
    Clate * (T ^ (theta / 2 : ℝ) / (theta / 2))

theorem paper3ChemDuhamelDerivPositiveTimeConstant_nonneg
    (p : CM2Params) {M T theta tau : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (htheta0 : 0 < theta) (hthetaHalf : theta < 1 / 2)
    (htau : 0 < tau) :
    0 ≤ paper3ChemDuhamelDerivPositiveTimeConstant p M T theta tau := by
  let CQ := M * (Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * M ^ p.γ)))
  let HQ := paper3ChemFluxPositiveTimeHolderConstant
    p M T theta (tau / 2)
  let Cmix := 5 * Real.sqrt 2 / 2
  let Clate := 2 * HQ * weightedHeatHessConst theta
  have hCQ : 0 ≤ CQ := by
    dsimp [CQ]
    exact mul_nonneg hM (mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num)
        (mul_nonneg p.hν.le (Real.rpow_nonneg hM _))))
  have hHQ : 0 ≤ HQ := by
    simpa [HQ] using paper3ChemFluxPositiveTimeHolderConstant_nonneg
      p hM hT htheta0 hthetaHalf (by positivity : 0 < tau / 2)
  have hCmix : 0 ≤ Cmix := by dsimp [Cmix]; positivity
  have hClate : 0 ≤ Clate := by
    dsimp [Clate]
    exact mul_nonneg (mul_nonneg (by norm_num) hHQ)
      (ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst_nonneg theta)
  unfold paper3ChemDuhamelDerivPositiveTimeConstant
  dsimp only
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg (mul_nonneg hCmix
        (Real.rpow_nonneg (by positivity : 0 ≤ tau / 2) _)) hCQ) hT)
    (mul_nonneg hClate
      (div_nonneg (Real.rpow_nonneg hT _) (by linarith)))

/-- Explicit uniform differentiated-Duhamel estimate. -/
theorem conjugateMild_chemDuhamel_deriv_positiveTime_explicit
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionData p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {theta tau : ℝ} (htheta0 : 0 < theta)
    (hthetaHalf : theta < 1 / 2) (htau : 0 < tau) :
    ∀ t, tau ≤ t → t ≤ D.T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |∫ s in (0 : ℝ)..t, deriv
        (fun z : ℝ => intervalConjugateKernelOperator (t - s)
          (chemFluxLifted p (D.u s)) z) x| ≤
        paper3ChemDuhamelDerivPositiveTimeConstant
          p D.M D.T theta tau := by
  let CQ := D.M * (Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * D.M ^ p.γ)))
  let HQ := paper3ChemFluxPositiveTimeHolderConstant
    p D.M D.T theta (tau / 2)
  let F : ℝ → ℝ → ℝ := fun s y =>
    if 0 < s ∧ s ≤ D.T then chemFluxLifted p (D.u s) y else 0
  let Cmix := 5 * Real.sqrt 2 / 2
  let Clate := 2 * HQ * weightedHeatHessConst theta
  have hCQ : 0 ≤ CQ := by
    dsimp [CQ]
    exact mul_nonneg D.hM.le (mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num)
        (mul_nonneg p.hν.le (Real.rpow_nonneg D.hM.le _))))
  have hHQ : 0 ≤ HQ := by
    simpa [HQ] using paper3ChemFluxPositiveTimeHolderConstant_nonneg
      p D.hM.le D.hT.le htheta0 hthetaHalf
        (by positivity : 0 < tau / 2)
  have hCmix : 0 ≤ Cmix := by dsimp [Cmix]; positivity
  have hClate : 0 ≤ Clate := by
    dsimp [Clate]
    exact mul_nonneg (mul_nonneg (by norm_num) hHQ)
      (ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst_nonneg theta)
  have hFeq : ∀ {s : ℝ}, 0 < s → s ≤ D.T →
      F s = chemFluxLifted p (D.u s) := by
    intro s hs0 hsT
    funext y
    simp [F, hs0, hsT]
  have hFbound : ∀ s y, |F s y| ≤ CQ := by
    intro s y
    dsimp [F]
    split_ifs with hs
    · dsimp [CQ]
      exact ShenWork.IntervalConjugateChemFluxIntegrable.chemFluxLifted_sup_bound_of_ball
        p D.hM.le (D.hbound s hs.1 hs.2) (D.hnonneg s hs.1 hs.2)
          (D.hcont s hs.1 hs.2) y
    · simpa using hCQ
  have hFmeas : Measurable (Function.uncurry F) := by
    have hbase := ShenWork.Paper2.chemFluxLifted_uncurry_measurable
      (p := p) (u := D.u) D.hmeas
    dsimp [F]
    refine Measurable.ite ?_ hbase measurable_const
    exact ((isOpen_Ioi.preimage continuous_fst).measurableSet).inter
      ((isClosed_Iic.preimage continuous_fst).measurableSet)
  have hFint : ∀ s, Integrable (F s) (intervalMeasure 1) := by
    intro s
    dsimp [F]
    split_ifs with hs
    · exact ShenWork.IntervalDuhamelIntegrability.chemFluxLifted_integrable_of_continuous
        p (D.hbound s hs.1 hs.2) D.hM.le (D.hcont s hs.1 hs.2)
          (D.hnonneg s hs.1 hs.2)
    · simp
  have hF0 : ∀ s, F s 0 = 0 := by
    intro s
    dsimp [F]
    split_ifs
    · exact ShenWork.IntervalCoupledRegularityBootstrap.chemFluxLifted_endpoint_zero
        p (D.u s)
    · rfl
  have hF1 : ∀ s, F s 1 = 0 := by
    intro s
    dsimp [F]
    split_ifs
    · exact ShenWork.IntervalCoupledRegularityBootstrap.chemFluxLifted_endpoint_one
        p (D.u s)
    · rfl
  intro t htauT htT x hx
  have ht : 0 < t := lt_of_lt_of_le htau htauT
  have ht2 : 0 < t / 2 := by positivity
  have hFcont : ∀ s, t / 2 < s → s < t →
      ContinuousOn (F s) (Set.Icc (0 : ℝ) 1) := by
    intro s hs2 hst
    have hs0 : 0 < s := lt_trans ht2 hs2
    have hsT : s ≤ D.T := (le_of_lt hst).trans htT
    rw [hFeq hs0 hsT]
    exact (ShenWork.IntervalDuhamelIntegrability.chemFluxLifted_continuous_of_continuous
      p (D.hcont s hs0 hsT) (D.hnonneg s hs0 hsT)).continuousOn
  have hFholder : ∀ s, t / 2 < s → s < t →
      ∀ a b : ℝ, a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
      |F s a - F s b| ≤ HQ * |a - b| ^ theta := by
    intro s hs2 hst a b ha hb
    have hs0 : 0 < s := lt_trans ht2 hs2
    have hsT : s ≤ D.T := (le_of_lt hst).trans htT
    rw [hFeq hs0 hsT]
    simpa [HQ] using conjugateMild_chemFlux_positiveTime_holder_explicit
      D hu₀ hu₀_meas htheta0 hthetaHalf
        (by positivity : 0 < tau / 2) s
        ⟨by linarith [htauT], hsT⟩ a b ha hb
  have hraw :=
    ShenWork.IntervalNeumannFullKernel.intervalConjugateDuhamel_deriv_integral_abs_le_of_late_holder
      ht htheta0 (by linarith : theta < 1) hCQ hHQ hFmeas hFint hFbound
        hFcont hFholder hF0 hF1 x hx
  have heqDeriv :
      (∫ s in (0 : ℝ)..t, deriv
        (fun z : ℝ => intervalConjugateKernelOperator (t - s)
          (chemFluxLifted p (D.u s)) z) x) =
      ∫ s in (0 : ℝ)..t, deriv
        (fun z : ℝ => intervalConjugateKernelOperator (t - s)
          (F s) z) x := by
    apply intervalIntegral.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro s hs
    rw [Set.uIoc_of_le ht.le] at hs
    rw [hFeq hs.1 (hs.2.trans htT)]
  rw [heqDeriv]
  refine hraw.trans ?_
  have hpow : (t / 2) ^ (-(1 : ℝ)) ≤
      (tau / 2) ^ (-(1 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
  have hearly : Cmix * (t / 2) ^ (-(1 : ℝ)) * CQ * t ≤
      Cmix * (tau / 2) ^ (-(1 : ℝ)) * CQ * D.T := by
    have hA : Cmix * (t / 2) ^ (-(1 : ℝ)) * CQ ≤
        Cmix * (tau / 2) ^ (-(1 : ℝ)) * CQ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow hCmix) hCQ
    exact mul_le_mul hA htT ht.le
      (mul_nonneg (mul_nonneg hCmix
        (Real.rpow_nonneg (by positivity : 0 ≤ tau / 2) _)) hCQ)
  have htpow : t ^ (theta / 2 : ℝ) ≤ D.T ^ (theta / 2 : ℝ) :=
    Real.rpow_le_rpow ht.le htT (by linarith)
  have hlate : Clate * (t ^ (theta / 2 : ℝ) / (theta / 2)) ≤
      Clate * (D.T ^ (theta / 2 : ℝ) / (theta / 2)) :=
    mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right htpow (by linarith)) hClate
  unfold paper3ChemDuhamelDerivPositiveTimeConstant
  dsimp only
  exact add_le_add hearly hlate

/-- Explicit positive-time derivative bound for the mild state. -/
def paper3MildDerivPositiveTimeConstant
    (p : CM2Params) (M T tau : ℝ) : ℝ :=
  let Cchem := paper3ChemDuhamelDerivPositiveTimeConstant
    p M T (1 / 4) tau
  let Cinit := heatGradientLinftyLinftyConstant *
    tau ^ (-(1 / 2) : ℝ) * M
  let CL := M * (p.a + p.b * M ^ p.α)
  let Creact := heatGradientLinftyLinftyConstant *
    (2 * Real.sqrt T) * CL
  Cinit + |p.χ₀| * Cchem + Creact

theorem paper3MildDerivPositiveTimeConstant_nonneg
    (p : CM2Params) {M T tau : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (htau : 0 < tau) :
    0 ≤ paper3MildDerivPositiveTimeConstant p M T tau := by
  let Cchem := paper3ChemDuhamelDerivPositiveTimeConstant
    p M T (1 / 4) tau
  let Cinit := heatGradientLinftyLinftyConstant *
    tau ^ (-(1 / 2) : ℝ) * M
  let CL := M * (p.a + p.b * M ^ p.α)
  let Creact := heatGradientLinftyLinftyConstant *
    (2 * Real.sqrt T) * CL
  have hCchem : 0 ≤ Cchem := by
    simpa [Cchem] using paper3ChemDuhamelDerivPositiveTimeConstant_nonneg
      p hM hT (by norm_num) (by norm_num) htau
  have hCinit : 0 ≤ Cinit := by
    dsimp [Cinit]
    exact mul_nonneg
      (mul_nonneg heatGradientLinftyLinftyConstant_nonneg
        (Real.rpow_nonneg htau.le _)) hM
  have hCL : 0 ≤ CL := by
    dsimp [CL]
    exact mul_nonneg hM
      (add_nonneg p.ha (mul_nonneg p.hb (Real.rpow_nonneg hM _)))
  have hCreact : 0 ≤ Creact := by
    dsimp [Creact]
    exact mul_nonneg
      (mul_nonneg heatGradientLinftyLinftyConstant_nonneg
        (mul_nonneg (by norm_num) (Real.sqrt_nonneg T))) hCL
  unfold paper3MildDerivPositiveTimeConstant
  dsimp only
  exact add_nonneg (add_nonneg hCinit
    (mul_nonneg (abs_nonneg _) hCchem)) hCreact

theorem conjugateMild_intervalDomainLift_deriv_positiveTime_explicit
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionData p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {tau : ℝ} (htau : 0 < tau) :
    ∀ t, tau ≤ t → t ≤ D.T → ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      |deriv (intervalDomainLift (D.u t)) x| ≤
        paper3MildDerivPositiveTimeConstant p D.M D.T tau := by
  let Cchem := paper3ChemDuhamelDerivPositiveTimeConstant
    p D.M D.T (1 / 4) tau
  let Cinit := heatGradientLinftyLinftyConstant *
    tau ^ (-(1 / 2) : ℝ) * D.M
  let CL := D.M * (p.a + p.b * D.M ^ p.α)
  let Creact := heatGradientLinftyLinftyConstant *
    (2 * Real.sqrt D.T) * CL
  have hCchem : 0 ≤ Cchem := by
    simpa [Cchem] using paper3ChemDuhamelDerivPositiveTimeConstant_nonneg
      p D.hM.le D.hT.le (by norm_num) (by norm_num) htau
  have hCinit : 0 ≤ Cinit := by
    dsimp [Cinit]
    exact mul_nonneg
      (mul_nonneg heatGradientLinftyLinftyConstant_nonneg
        (Real.rpow_nonneg htau.le _)) D.hM.le
  have hCL : 0 ≤ CL := by
    dsimp [CL]
    exact mul_nonneg D.hM.le
      (add_nonneg p.ha (mul_nonneg p.hb
        (Real.rpow_nonneg D.hM.le _)))
  have hCreact : 0 ≤ Creact := by
    dsimp [Creact]
    exact mul_nonneg
      (mul_nonneg heatGradientLinftyLinftyConstant_nonneg
        (mul_nonneg (by norm_num) (Real.sqrt_nonneg D.T))) hCL
  intro t htauT htT x hx
  have ht : 0 < t := lt_of_lt_of_le htau htauT
  have hwhole := conjugateMild_intervalDomainLift_hasDerivAt_interior
    D hu₀ hu₀_meas (θ := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
      ht htT hx
  have hinit :=
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_hasDerivAt_fst
      ht hu₀_meas hu₀ x
  have hinitRaw :=
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_deriv_Linfty_pointwise_sqrt_t
      ht hu₀_meas hu₀ x
  rw [hinit.deriv] at hinitRaw
  have hpow : t ^ (-(1 / 2) : ℝ) ≤ tau ^ (-(1 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos htau htauT (by norm_num)
  have hinitBound :
      |∫ y, deriv (fun z : ℝ => intervalNeumannFullKernel t z y) x *
          intervalDomainLift u₀ y ∂(intervalMeasure 1)| ≤ Cinit := by
    refine hinitRaw.trans ?_
    dsimp [Cinit]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow
        heatGradientLinftyLinftyConstant_nonneg) D.hM.le
  have hchemBound :=
    conjugateMild_chemDuhamel_deriv_positiveTime_explicit
      D hu₀ hu₀_meas (theta := (1 / 4 : ℝ))
        (by norm_num) (by norm_num) htau t htauT htT x
          (Set.Ioo_subset_Icc_self hx)
  have hreactRaw := conjugateMild_logisticDuhamel_deriv_abs_le
    D ht htT (x := x)
  have hreactBound :
      |∫ s in (0 : ℝ)..t, deriv
        (fun z : ℝ => intervalFullSemigroupOperator (t - s)
          (logisticLifted p (D.u s)) z) x| ≤ Creact := by
    refine hreactRaw.trans ?_
    dsimp [Creact, CL]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt htT) (by norm_num))
        heatGradientLinftyLinftyConstant_nonneg) hCL
  rw [hwhole.deriv]
  have htri :
      |(∫ y, deriv (fun z : ℝ => intervalNeumannFullKernel t z y) x *
            intervalDomainLift u₀ y ∂(intervalMeasure 1)) +
          (-p.χ₀) * (∫ s in (0 : ℝ)..t, deriv
            (fun z : ℝ => intervalConjugateKernelOperator (t - s)
              (chemFluxLifted p (D.u s)) z) x) +
          ∫ s in (0 : ℝ)..t, deriv
            (fun z : ℝ => intervalFullSemigroupOperator (t - s)
              (logisticLifted p (D.u s)) z) x| ≤
        |∫ y, deriv (fun z : ℝ => intervalNeumannFullKernel t z y) x *
            intervalDomainLift u₀ y ∂(intervalMeasure 1)| +
          |(-p.χ₀) * (∫ s in (0 : ℝ)..t, deriv
            (fun z : ℝ => intervalConjugateKernelOperator (t - s)
              (chemFluxLifted p (D.u s)) z) x)| +
          |∫ s in (0 : ℝ)..t, deriv
            (fun z : ℝ => intervalFullSemigroupOperator (t - s)
              (logisticLifted p (D.u s)) z) x| := by
    refine (abs_add_le _ _).trans ?_
    gcongr
    exact abs_add_le _ _
  refine htri.trans ?_
  unfold paper3MildDerivPositiveTimeConstant
  dsimp only
  rw [abs_mul, abs_neg]
  exact add_le_add (add_le_add hinitBound
    (mul_le_mul_of_nonneg_left hchemBound (abs_nonneg _))) hreactBound

/-- Explicit uniform derivative bound for the physical eliminated flux. -/
def paper3ChemFluxDerivPositiveTimeConstant
    (p : CM2Params) (M T tau : ℝ) : ℝ :=
  let CU := paper3MildDerivPositiveTimeConstant p M T tau
  let G0 := Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * M ^ p.γ))
  let L0 := ShenWork.IntervalResolverWeakBounds.resolverWeakLapBound p M
  CU * G0 + M * L0 + M * G0 * p.β * G0

theorem paper3ChemFluxDerivPositiveTimeConstant_nonneg
    (p : CM2Params) {M T tau : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (htau : 0 < tau) :
    0 ≤ paper3ChemFluxDerivPositiveTimeConstant p M T tau := by
  let CU := paper3MildDerivPositiveTimeConstant p M T tau
  let G0 := Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * M ^ p.γ))
  let L0 := ShenWork.IntervalResolverWeakBounds.resolverWeakLapBound p M
  have hCU : 0 ≤ CU := by
    simpa [CU] using paper3MildDerivPositiveTimeConstant_nonneg
      p hM hT htau
  have hG0 : 0 ≤ G0 := by
    dsimp [G0]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num)
        (mul_nonneg p.hν.le (Real.rpow_nonneg hM _)))
  have hL0 : 0 ≤ L0 := by
    dsimp [L0, ShenWork.IntervalResolverWeakBounds.resolverWeakLapBound,
      ShenWork.IntervalResolverWeakBounds.resolverWeakValueBound]
    exact add_nonneg
      (mul_nonneg p.hμ.le
        (mul_nonneg (Real.sqrt_nonneg _)
          (mul_nonneg (by norm_num)
            (mul_nonneg p.hν.le (Real.rpow_nonneg hM _)))))
      (mul_nonneg p.hν.le (Real.rpow_nonneg hM _))
  unfold paper3ChemFluxDerivPositiveTimeConstant
  dsimp only
  exact add_nonneg (add_nonneg (mul_nonneg hCU hG0) (mul_nonneg hM hL0))
    (mul_nonneg (mul_nonneg (mul_nonneg hM hG0) p.hβ) hG0)

theorem conjugateMild_chemFlux_deriv_positiveTime_explicit
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionData p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {tau : ℝ} (htau : 0 < tau) :
    ∀ t, tau ≤ t → t ≤ D.T → ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      |deriv (chemFluxLifted p (D.u t)) x| ≤
        paper3ChemFluxDerivPositiveTimeConstant p D.M D.T tau := by
  let CU := paper3MildDerivPositiveTimeConstant p D.M D.T tau
  let G0 := Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * D.M ^ p.γ))
  let L0 := ShenWork.IntervalResolverWeakBounds.resolverWeakLapBound p D.M
  have hCU : 0 ≤ CU := by
    simpa [CU] using paper3MildDerivPositiveTimeConstant_nonneg
      p D.hM.le D.hT.le htau
  have hG0 : 0 ≤ G0 := by
    dsimp [G0]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num)
        (mul_nonneg p.hν.le (Real.rpow_nonneg D.hM.le _)))
  have hL0 : 0 ≤ L0 := by
    dsimp [L0, ShenWork.IntervalResolverWeakBounds.resolverWeakLapBound,
      ShenWork.IntervalResolverWeakBounds.resolverWeakValueBound]
    exact add_nonneg
      (mul_nonneg p.hμ.le
        (mul_nonneg (Real.sqrt_nonneg _)
          (mul_nonneg (by norm_num)
            (mul_nonneg p.hν.le (Real.rpow_nonneg D.hM.le _)))))
      (mul_nonneg p.hν.le (Real.rpow_nonneg D.hM.le _))
  intro t htauT htT x hx
  have ht : 0 < t := lt_of_lt_of_le htau htauT
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
  have hUraw := conjugateMild_intervalDomainLift_hasDerivAt_interior
    D hu₀ hu₀_meas (θ := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
      ht htT hx
  have hU' : HasDerivAt U (deriv U x) x := by
    simpa [U] using hUraw.differentiableAt.hasDerivAt
  have hGraw :=
    ShenWork.IntervalResolverWeakBounds.resolverGradReal_hasDerivAt_physicalLap_of_continuousOn
      p hUcont (fun z hz => by
        have h := D.hnonneg t ht htT ⟨z, hz⟩
        simpa [U, intervalDomainLift, hz] using h) hx
  have hG' : HasDerivAt G (deriv G x) x := by
    simpa [G] using hGraw.differentiableAt.hasDerivAt
  have hR' : HasDerivAt R (G x) x := by
    simpa [R, G] using
      ShenWork.IntervalResolverWeakBounds.intervalNeumannResolverR_lift_hasDerivAt_resolverGradReal_of_continuousOn
        p hUcont hx
  have hRnonneg : 0 ≤ R x := by
    have h := ShenWork.IntervalMildToClassical.mildChemical_nonneg
      (T := D.T) p (u := D.u) D.hnonneg D.hcont ht htT ⟨x, hxIcc⟩
    simpa [R, ShenWork.IntervalMildToClassical.mildChemicalConcentration,
      intervalDomainLift, hxIcc] using h
  have hW' : HasDerivAt W
      (G x * (-p.β) * (1 + R x) ^ (-p.β - 1)) x := by
    have hbase : HasDerivAt (fun z : ℝ => 1 + R z) (G x) x :=
      hR'.const_add 1
    simpa [W, sub_eq_add_neg] using
      hbase.rpow_const (p := -p.β) (Or.inl (by linarith : 1 + R x ≠ 0))
  have hprod := (hU'.mul hG').mul hW'
  have hev : chemFluxLifted p (D.u t) =ᶠ[𝓝 x]
      (fun z => U z * G z * W z) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with z hz
    have hzIcc := Set.Ioo_subset_Icc_self hz
    have hRz : 0 ≤ R z := by
      have h := ShenWork.IntervalMildToClassical.mildChemical_nonneg
        (T := D.T) p (u := D.u) D.hnonneg D.hcont ht htT ⟨z, hzIcc⟩
      simpa [R, ShenWork.IntervalMildToClassical.mildChemicalConcentration,
        intervalDomainLift, hzIcc] using h
    unfold chemFluxLifted
    rw [div_eq_mul_inv, ← Real.rpow_neg (by linarith : 0 ≤ 1 + R z)]
  have hflux := hev.hasDerivAt_iff.mpr hprod
  have hUabs : |U x| ≤ D.M := by
    simpa [U, intervalDomainLift, hxIcc] using D.hbound t ht htT ⟨x, hxIcc⟩
  have hUderiv : |deriv U x| ≤ CU := by
    simpa [U, CU] using
      conjugateMild_intervalDomainLift_deriv_positiveTime_explicit
        D hu₀ hu₀_meas htau t htauT htT x hx
  have hGabs : |G x| ≤ G0 := by
    dsimp [G0]
    exact ShenWork.IntervalResolverWeakBounds.resolverGrad_sup_le_of_bounded
      p hUcont
        (fun z hz => by
          have h := D.hnonneg t ht htT ⟨z, hz⟩
          simpa [U, intervalDomainLift, hz] using h)
        (fun z hz => by
          have h := D.hbound t ht htT ⟨z, hz⟩
          simpa [U, intervalDomainLift, hz] using (abs_le.mp h).2)
        hxIcc
  have hGderiv : |deriv G x| ≤ L0 := by
    dsimp [L0]
    simpa [G] using
      ShenWork.IntervalResolverWeakBounds.deriv_resolverGradReal_abs_le_of_bounded
        p hUcont
          (fun z hz => by
            have h := D.hnonneg t ht htT ⟨z, hz⟩
            simpa [U, intervalDomainLift, hz] using h)
          (fun z hz => by
            have h := D.hbound t ht htT ⟨z, hz⟩
            simpa [U, intervalDomainLift, hz] using (abs_le.mp h).2)
          hx
  have hWabs : |W x| ≤ 1 := by
    have hW0 : 0 ≤ W x := Real.rpow_nonneg (by linarith : 0 ≤ 1 + R x) _
    rw [abs_of_nonneg hW0]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith)
      (by linarith [p.hβ])
  have hWderiv :
      |G x * (-p.β) * (1 + R x) ^ (-p.β - 1)| ≤ p.β * G0 := by
    have hp0 : 0 ≤ (1 + R x) ^ (-p.β - 1) :=
      Real.rpow_nonneg (by linarith : 0 ≤ 1 + R x) _
    have hp1 : (1 + R x) ^ (-p.β - 1) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith)
        (by linarith [p.hβ])
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg p.hβ, abs_of_nonneg hp0]
    calc
      |G x| * p.β * (1 + R x) ^ (-p.β - 1) ≤
          G0 * p.β * (1 + R x) ^ (-p.β - 1) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hGabs p.hβ) hp0
      _ ≤ G0 * p.β * 1 :=
        mul_le_mul_of_nonneg_left hp1 (mul_nonneg hG0 p.hβ)
      _ = p.β * G0 := by ring
  rw [hflux.deriv]
  have hsum : |deriv U x * G x + U x * deriv G x| ≤
      CU * G0 + D.M * L0 := by
    calc
      _ ≤ |deriv U x * G x| + |U x * deriv G x| := abs_add_le _ _
      _ ≤ CU * G0 + D.M * L0 := by
        rw [abs_mul, abs_mul]
        exact add_le_add
          (mul_le_mul hUderiv hGabs (abs_nonneg _) hCU)
          (mul_le_mul hUabs hGderiv (abs_nonneg _) D.hM.le)
  have hfirst : |(deriv U x * G x + U x * deriv G x) * W x| ≤
      (CU * G0 + D.M * L0) * 1 := by
    rw [abs_mul]
    exact mul_le_mul hsum hWabs (abs_nonneg _)
      (add_nonneg (mul_nonneg hCU hG0) (mul_nonneg D.hM.le hL0))
  have hsecond :
      |U x * G x * (G x * (-p.β) * (1 + R x) ^ (-p.β - 1))| ≤
        D.M * G0 * (p.β * G0) := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul
      (mul_le_mul hUabs hGabs (abs_nonneg _) D.hM.le) hWderiv
      (abs_nonneg _) (mul_nonneg D.hM.le hG0)
  refine (abs_add_le _ _).trans ?_
  unfold paper3ChemFluxDerivPositiveTimeConstant
  dsimp only
  calc
    |(deriv U x * G x + U x * deriv G x) * W x| +
        |U x * G x * (G x * (-p.β) * (1 + R x) ^ (-p.β - 1))| ≤
      (CU * G0 + D.M * L0) * 1 + D.M * G0 * (p.β * G0) :=
        add_le_add hfirst hsecond
    _ = CU * G0 + D.M * L0 + D.M * G0 * p.β * G0 := by ring

#print axioms paper3ChemDuhamelDerivPositiveTimeConstant_nonneg
#print axioms conjugateMild_chemDuhamel_deriv_positiveTime_explicit
#print axioms paper3MildDerivPositiveTimeConstant_nonneg
#print axioms conjugateMild_intervalDomainLift_deriv_positiveTime_explicit
#print axioms paper3ChemFluxDerivPositiveTimeConstant_nonneg
#print axioms conjugateMild_chemFlux_deriv_positiveTime_explicit

end

end ShenWork.Paper3
