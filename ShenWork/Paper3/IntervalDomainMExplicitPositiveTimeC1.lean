/- Explicit, trajectory-independent positive-time C1 constants for the
faithful general-`m` conjugate mild solution. -/
import ShenWork.Paper2.IntervalDomainMConjugateMildPositiveTimeC1

namespace ShenWork.Paper3

open MeasureTheory Filter Set Topology
open ShenWork.IntervalDomain
  (intervalMeasure intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel
  (intervalFullSemigroupOperator intervalNeumannFullKernel weightedHeatHessConst)
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateKernelOperator)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.Paper2.IntervalDomainMConjugateDuhamelMap
  (chemFluxMLifted chemFlux_div_lipschitz_with_massLip
    chemFluxMLifted_abs_le_of_pos_slice
    chemFluxMLifted_uncurry_measurable chemFluxMLifted_integrable_of_pos_slice
    chemFluxMLifted_continuousOn_Icc_of_pos_slice
    chemFluxMLifted_endpoint_zero chemFluxMLifted_endpoint_one)
open ShenWork.Paper2.IntervalDomainMConjugatePicardFloorInhabit
  (ConjugateMildSolutionDataM)
open ShenWork.IntervalPositiveFloorNonlinearLipschitz
  (powerLip powerLip_nonneg)
open ShenWork.HeatKernelGradientEstimates
  (heatGradientLinftyLinftyConstant heatGradientLinftyLinftyConstant_nonneg)
open ShenWork.Paper2

noncomputable section

/-- The already-explicit faithful mild Holder constant is nonnegative under
the natural parameter restrictions. -/
theorem conjugateMildMHolderConstant_nonneg
    (p : CM2Params) {M T theta tau : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (htheta0 : 0 < theta) (htheta1 : theta < 1) (htau : 0 < tau) :
    0 ≤ conjugateMildMHolderConstant p M T theta tau := by
  let base : ℝ := (2 : ℝ) ^ (1 - theta) * gradSmoothingConst ^ theta
  let CL : ℝ := M * (p.a + p.b * M ^ p.α)
  let CQ : ℝ := M ^ p.m * (Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * M ^ p.γ)))
  let gbase : ℝ := (2 : ℝ) ^ (1 - theta) *
    ((5 * Real.sqrt 2 / 2) ^ theta *
      heatGradientLinftyLinftyConstant ^ (1 - theta))
  let UB_L : ℝ := T ^ (-(theta / 2) + 1) / (-(theta / 2) + 1)
  let UB_Q : ℝ := T ^ (-((1 + theta) / 2) + 1) /
    (-((1 + theta) / 2) + 1)
  have hbase : 0 ≤ base := by
    dsimp [base]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg gradSmoothingConst_nonneg _)
  have hCL : 0 ≤ CL := by
    dsimp [CL]
    exact mul_nonneg hM
      (add_nonneg p.ha (mul_nonneg p.hb (Real.rpow_nonneg hM _)))
  have hCQ : 0 ≤ CQ := by
    dsimp [CQ]
    exact mul_nonneg (Real.rpow_nonneg hM _)
      (mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (by norm_num)
          (mul_nonneg p.hν.le (Real.rpow_nonneg hM _))))
  have hgbase : 0 ≤ gbase := by
    dsimp [gbase]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (Real.rpow_nonneg heatGradientLinftyLinftyConstant_nonneg _))
  have hUBL : 0 ≤ UB_L := by
    dsimp [UB_L]
    exact div_nonneg (Real.rpow_nonneg hT _) (by linarith)
  have hUBQ : 0 ≤ UB_Q := by
    dsimp [UB_Q]
    exact div_nonneg (Real.rpow_nonneg hT _) (by linarith)
  unfold conjugateMildMHolderConstant
  dsimp only
  exact add_nonneg
    (add_nonneg
      (mul_nonneg (mul_nonneg hbase hM)
        (Real.rpow_nonneg htau.le _))
      (mul_nonneg (abs_nonneg _)
        (mul_nonneg (mul_nonneg hgbase hCQ) hUBQ)))
    (mul_nonneg (mul_nonneg hbase hCL) hUBL)

/-- Explicit Holder constant for the faithful nonlinear chemotaxis flux. -/
def paper3ChemFluxMPositiveTimeHolderConstant
    (p : CM2Params) (c M T theta tau : ℝ) : ℝ :=
  let Hu := conjugateMildMHolderConstant p M T theta tau
  let G := Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * M ^ p.γ))
  let Hg := (2 : ℝ) ^ (1 - theta) *
      Real.sqrt (∑' k : ℕ,
        (ShenWork.IntervalResolverWeakBounds.intervalNeumannResolverGradHolderWeight
          p theta k) ^ 2) * (2 * (p.ν * M ^ p.γ))
  let Lm := powerLip p.m c M
  let A := M ^ p.m
  (Lm * Hu) * G + A * Hg + A * G * p.β * G

theorem paper3ChemFluxMPositiveTimeHolderConstant_nonneg
    (p : CM2Params) {c M T theta tau : ℝ}
    (hc : 0 < c) (hcM : c ≤ M) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (htheta0 : 0 < theta) (hthetaHalf : theta < 1 / 2)
    (htau : 0 < tau) :
    0 ≤ paper3ChemFluxMPositiveTimeHolderConstant
      p c M T theta tau := by
  have htheta1 : theta < 1 := by linarith
  let Hu := conjugateMildMHolderConstant p M T theta tau
  let G := Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * M ^ p.γ))
  let Hg := (2 : ℝ) ^ (1 - theta) *
      Real.sqrt (∑' k : ℕ,
        (ShenWork.IntervalResolverWeakBounds.intervalNeumannResolverGradHolderWeight
          p theta k) ^ 2) * (2 * (p.ν * M ^ p.γ))
  let Lm := powerLip p.m c M
  let A := M ^ p.m
  have hHu : 0 ≤ Hu := by
    simpa [Hu] using conjugateMildMHolderConstant_nonneg
      p hM hT htheta0 htheta1 htau
  have hG : 0 ≤ G := by
    dsimp [G]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num)
        (mul_nonneg p.hν.le (Real.rpow_nonneg hM _)))
  have hHg : 0 ≤ Hg := by
    dsimp [Hg]
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (Real.sqrt_nonneg _))
      (mul_nonneg (by norm_num)
        (mul_nonneg p.hν.le (Real.rpow_nonneg hM _)))
  have hLm : 0 ≤ Lm := by
    dsimp [Lm]
    exact powerLip_nonneg p.hm hc hcM
  have hA : 0 ≤ A := by
    dsimp [A]
    exact Real.rpow_nonneg hM _
  unfold paper3ChemFluxMPositiveTimeHolderConstant
  dsimp only
  exact add_nonneg
    (add_nonneg (mul_nonneg (mul_nonneg hLm hHu) hG)
      (mul_nonneg hA hHg))
    (mul_nonneg (mul_nonneg (mul_nonneg hA hG) p.hβ) hG)

/-- Explicit, trajectory-independent Holder estimate for the faithful flux. -/
theorem conjugateMildM_chemFlux_positiveTime_holder_explicit
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {theta tau : ℝ} (htheta0 : 0 < theta)
    (hthetaHalf : theta < 1 / 2) (htau : 0 < tau) :
    ∀ s ∈ Set.Icc tau D.T, ∀ a b : ℝ,
      a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
      |chemFluxMLifted p (D.u s) a - chemFluxMLifted p (D.u s) b| ≤
        paper3ChemFluxMPositiveTimeHolderConstant
          p D.c D.M D.T theta tau * |a - b| ^ theta := by
  have htheta1 : theta < 1 := by linarith
  let Hu := conjugateMildMHolderConstant p D.M D.T theta tau
  let G := Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * D.M ^ p.γ))
  let Hg := (2 : ℝ) ^ (1 - theta) *
      Real.sqrt (∑' k : ℕ,
        (ShenWork.IntervalResolverWeakBounds.intervalNeumannResolverGradHolderWeight
          p theta k) ^ 2) * (2 * (p.ν * D.M ^ p.γ))
  let Lm := powerLip p.m D.c D.M
  let A := D.M ^ p.m
  have hHu_pack := conjugateMildM_positiveTime_holder_bound
    D hu₀ hu₀_meas htheta0 htheta1 htau
  have hHu : 0 ≤ Hu := by simpa [Hu] using hHu_pack.1
  have hu_holder := hHu_pack.2
  have hG : 0 ≤ G := by
    dsimp [G]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num)
        (mul_nonneg p.hν.le (Real.rpow_nonneg D.hM.le _)))
  have hHg : 0 ≤ Hg := by
    dsimp [Hg]
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (Real.sqrt_nonneg _))
      (mul_nonneg (by norm_num)
        (mul_nonneg p.hν.le (Real.rpow_nonneg D.hM.le _)))
  have hcM : D.c ≤ D.M := D.floor_le_bound
  have hLm : 0 ≤ Lm := by
    dsimp [Lm]
    exact powerLip_nonneg p.hm D.hc hcM
  have hA : 0 ≤ A := by
    dsimp [A]
    exact Real.rpow_nonneg D.hM.le _
  intro s hs a b ha hb
  have hs0 : 0 < s := lt_of_lt_of_le htau hs.1
  have hUcont : ContinuousOn (intervalDomainLift (D.u s))
      (Set.Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    have heq : Set.restrict (Set.Icc (0 : ℝ) 1)
        (intervalDomainLift (D.u s)) = D.u s := by
      ext ⟨y, hy⟩
      simp [Set.restrict, intervalDomainLift, hy]
      rfl
    rw [heq]
    exact D.hcont s hs0 hs.2
  have hlb : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ intervalDomainLift (D.u s) y := by
    intro y hy
    exact (by simpa [intervalDomainLift, hy] using
      D.hc.le.trans (D.hfloor s hs0 hs.2 ⟨y, hy⟩))
  have hub : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (D.u s) y ≤ D.M := by
    intro y hy
    have h := D.hbound s hs0 hs.2 ⟨y, hy⟩
    simpa [intervalDomainLift, hy] using (abs_le.mp h).2
  have hstrip : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (D.u s) y ∈ Set.Icc D.c D.M := by
    intro y hy
    exact ⟨by simpa [intervalDomainLift, hy] using
        D.hfloor s hs0 hs.2 ⟨y, hy⟩,
      hub y hy⟩
  have hg_bound : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |resolverGradReal p (D.u s) y| ≤ G := by
    intro y hy
    dsimp [G]
    exact ShenWork.IntervalResolverWeakBounds.resolverGrad_sup_le_of_bounded
      p hUcont hlb hub hy
  have hR_nonneg : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ intervalDomainLift
        (ShenWork.PDE.intervalNeumannResolverR p (D.u s)) y := by
    intro y hy
    have h := ShenWork.IntervalMildToClassical.mildChemical_nonneg
      (T := D.T) p (u := D.u)
        (fun t ht htT x => D.hc.le.trans (D.hfloor t ht htT x))
        D.hcont hs0 hs.2 ⟨y, hy⟩
    simpa [ShenWork.IntervalMildToClassical.mildChemicalConcentration,
      intervalDomainLift, hy] using h
  have hu_holder_lift : ∀ x y : ℝ,
      x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 →
      |intervalDomainLift (D.u s) x - intervalDomainLift (D.u s) y| ≤
        Hu * |x - y| ^ theta := by
    intro x y hx hy
    simpa [Hu, intervalDomainLift, hx, hy] using
      hu_holder s hs ⟨x, hx⟩ ⟨y, hy⟩
  have hg_holder : ∀ x y : ℝ,
      x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 →
      |resolverGradReal p (D.u s) x - resolverGradReal p (D.u s) y| ≤
        Hg * |x - y| ^ theta := by
    intro x y hx hy
    dsimp [Hg]
    exact ShenWork.IntervalResolverWeakBounds.resolverGradReal_holder_Icc_of_bounded_smallTheta
      p htheta0 hthetaHalf hUcont hlb hub hx hy
  have hR_holder : ∀ x y : ℝ,
      x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 →
      |intervalDomainLift
          (ShenWork.PDE.intervalNeumannResolverR p (D.u s)) x -
        intervalDomainLift
          (ShenWork.PDE.intervalNeumannResolverR p (D.u s)) y| ≤
        G * |x - y| ^ theta := by
    intro x y hx hy
    dsimp [G]
    exact ShenWork.IntervalResolverWeakBounds.intervalNeumannResolverR_lift_holder_Icc_of_bounded
      p htheta0 htheta1.le hUcont hlb hub hx hy
  have hmass :
      |intervalDomainLift (D.u s) a ^ p.m -
          intervalDomainLift (D.u s) b ^ p.m| ≤
        (Lm * Hu) * |a - b| ^ theta := by
    have hp := rpow_lipschitz_on_pos_Icc p.hm D.hc
      (hstrip a ha) (hstrip b hb)
    calc
      _ ≤ Lm * |intervalDomainLift (D.u s) a -
          intervalDomainLift (D.u s) b| := by simpa [Lm] using hp
      _ ≤ Lm * (Hu * |a - b| ^ theta) :=
        mul_le_mul_of_nonneg_left (hu_holder_lift a b ha hb) hLm
      _ = (Lm * Hu) * |a - b| ^ theta := by ring
  have hmass_b : |intervalDomainLift (D.u s) b ^ p.m| ≤ A := by
    rw [abs_of_nonneg (Real.rpow_nonneg (hlb b hb) _)]
    dsimp [A]
    exact Real.rpow_le_rpow (hlb b hb) (hub b hb) p.hm.le
  have hd : 0 ≤ |a - b| ^ theta := Real.rpow_nonneg (abs_nonneg _) _
  unfold paper3ChemFluxMPositiveTimeHolderConstant
  dsimp only
  exact chemFlux_div_lipschitz_with_massLip p.hβ hmass_b
    (hg_bound a ha) (hg_bound b hb) (hR_nonneg a ha) (hR_nonneg b hb)
    hmass (hg_holder a b ha hb) (hR_holder a b ha hb)
    hA hG (mul_nonneg hLm hHu) hHg hG hd

/-- Explicit uniform bound for the differentiated faithful chemotaxis
Duhamel leg. -/
def paper3ChemDuhamelMDerivPositiveTimeConstant
    (p : CM2Params) (c M T theta tau : ℝ) : ℝ :=
  let CQ := M ^ p.m * (Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * M ^ p.γ)))
  let HQ := paper3ChemFluxMPositiveTimeHolderConstant
    p c M T theta (tau / 2)
  let Cmix := 5 * Real.sqrt 2 / 2
  let Clate := 2 * HQ * weightedHeatHessConst theta
  Cmix * (tau / 2) ^ (-(1 : ℝ)) * CQ * T +
    Clate * (T ^ (theta / 2 : ℝ) / (theta / 2))

theorem paper3ChemDuhamelMDerivPositiveTimeConstant_nonneg
    (p : CM2Params) {c M T theta tau : ℝ}
    (hc : 0 < c) (hcM : c ≤ M) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (htheta0 : 0 < theta) (hthetaHalf : theta < 1 / 2)
    (htau : 0 < tau) :
    0 ≤ paper3ChemDuhamelMDerivPositiveTimeConstant
      p c M T theta tau := by
  let CQ := M ^ p.m * (Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * M ^ p.γ)))
  let HQ := paper3ChemFluxMPositiveTimeHolderConstant
    p c M T theta (tau / 2)
  let Cmix := 5 * Real.sqrt 2 / 2
  let Clate := 2 * HQ * weightedHeatHessConst theta
  have hCQ : 0 ≤ CQ := by
    dsimp [CQ]
    exact mul_nonneg (Real.rpow_nonneg hM _)
      (mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (by norm_num)
          (mul_nonneg p.hν.le (Real.rpow_nonneg hM _))))
  have hHQ : 0 ≤ HQ := by
    simpa [HQ] using paper3ChemFluxMPositiveTimeHolderConstant_nonneg
      p hc hcM hM hT htheta0 hthetaHalf
        (by positivity : 0 < tau / 2)
  have hCmix : 0 ≤ Cmix := by dsimp [Cmix]; positivity
  have hClate : 0 ≤ Clate := by
    dsimp [Clate]
    exact mul_nonneg (mul_nonneg (by norm_num) hHQ)
      (ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst_nonneg theta)
  unfold paper3ChemDuhamelMDerivPositiveTimeConstant
  dsimp only
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg (mul_nonneg hCmix
        (Real.rpow_nonneg (by positivity : 0 ≤ tau / 2) _)) hCQ) hT)
    (mul_nonneg hClate
      (div_nonneg (Real.rpow_nonneg hT _) (by linarith)))

/-- Explicit differentiated-Duhamel estimate, uniform over all trajectories
with the same floor, ceiling, and horizon. -/
theorem conjugateMildM_chemDuhamel_deriv_positiveTime_explicit
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {theta tau : ℝ} (htheta0 : 0 < theta)
    (hthetaHalf : theta < 1 / 2) (htau : 0 < tau) :
    ∀ t, tau ≤ t → t ≤ D.T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |∫ s in (0 : ℝ)..t, deriv
        (fun z : ℝ => intervalConjugateKernelOperator (t - s)
          (chemFluxMLifted p (D.u s)) z) x| ≤
        paper3ChemDuhamelMDerivPositiveTimeConstant
          p D.c D.M D.T theta tau := by
  have hcM : D.c ≤ D.M := D.floor_le_bound
  let CQ := D.M ^ p.m * (Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * D.M ^ p.γ)))
  let HQ := paper3ChemFluxMPositiveTimeHolderConstant
    p D.c D.M D.T theta (tau / 2)
  let F : ℝ → ℝ → ℝ := fun s y =>
    if 0 < s ∧ s ≤ D.T then chemFluxMLifted p (D.u s) y else 0
  let Cmix := 5 * Real.sqrt 2 / 2
  let Clate := 2 * HQ * weightedHeatHessConst theta
  have hCQ : 0 ≤ CQ := by
    dsimp [CQ]
    exact mul_nonneg (Real.rpow_nonneg D.hM.le _)
      (mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (by norm_num)
          (mul_nonneg p.hν.le (Real.rpow_nonneg D.hM.le _))))
  have hHQ : 0 ≤ HQ := by
    simpa [HQ] using paper3ChemFluxMPositiveTimeHolderConstant_nonneg
      p D.hc hcM D.hM.le D.hT.le htheta0 hthetaHalf
        (by positivity : 0 < tau / 2)
  have hCmix : 0 ≤ Cmix := by dsimp [Cmix]; positivity
  have hClate : 0 ≤ Clate := by
    dsimp [Clate]
    exact mul_nonneg (mul_nonneg (by norm_num) hHQ)
      (ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst_nonneg theta)
  have hFeq : ∀ {s : ℝ}, 0 < s → s ≤ D.T →
      F s = chemFluxMLifted p (D.u s) := by
    intro s hs0 hsT
    funext y
    simp [F, hs0, hsT]
  have hFbound : ∀ s y, |F s y| ≤ CQ := by
    intro s y
    dsimp [F]
    split_ifs with hs
    · dsimp [CQ]
      exact chemFluxMLifted_abs_le_of_pos_slice p D.hc hcM
        (D.hbound s hs.1 hs.2) (D.hfloor s hs.1 hs.2)
          (D.hcont s hs.1 hs.2) y
    · simpa using hCQ
  have hFmeas : Measurable (Function.uncurry F) := by
    have hbase := chemFluxMLifted_uncurry_measurable
      (p := p) (u := D.u) D.hmeas
    dsimp [F]
    refine Measurable.ite ?_ hbase measurable_const
    exact ((isOpen_Ioi.preimage continuous_fst).measurableSet).inter
      ((isClosed_Iic.preimage continuous_fst).measurableSet)
  have hFint : ∀ s, Integrable (F s) (intervalMeasure 1) := by
    intro s
    dsimp [F]
    split_ifs with hs
    · exact chemFluxMLifted_integrable_of_pos_slice p D.hc hcM
        (D.hbound s hs.1 hs.2) (D.hfloor s hs.1 hs.2)
          (D.hcont s hs.1 hs.2)
    · simp
  have hF0 : ∀ s, F s 0 = 0 := by
    intro s
    dsimp [F]
    split_ifs
    · exact chemFluxMLifted_endpoint_zero p (D.u s)
    · rfl
  have hF1 : ∀ s, F s 1 = 0 := by
    intro s
    dsimp [F]
    split_ifs
    · exact chemFluxMLifted_endpoint_one p (D.u s)
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
    exact chemFluxMLifted_continuousOn_Icc_of_pos_slice p D.hc hcM
      (D.hbound s hs0 hsT) (D.hfloor s hs0 hsT) (D.hcont s hs0 hsT)
  have hFholder : ∀ s, t / 2 < s → s < t →
      ∀ a b : ℝ, a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
      |F s a - F s b| ≤ HQ * |a - b| ^ theta := by
    intro s hs2 hst a b ha hb
    have hs0 : 0 < s := lt_trans ht2 hs2
    have hsT : s ≤ D.T := (le_of_lt hst).trans htT
    rw [hFeq hs0 hsT]
    simpa [HQ] using conjugateMildM_chemFlux_positiveTime_holder_explicit
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
          (chemFluxMLifted p (D.u s)) z) x) =
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
  unfold paper3ChemDuhamelMDerivPositiveTimeConstant
  dsimp only
  exact add_le_add hearly hlate

/-- Explicit positive-time derivative bound for the faithful mild state. -/
def paper3MildMDerivPositiveTimeConstant
    (p : CM2Params) (c M T tau : ℝ) : ℝ :=
  let Cchem := paper3ChemDuhamelMDerivPositiveTimeConstant
    p c M T (1 / 4) tau
  let Cinit := heatGradientLinftyLinftyConstant *
    tau ^ (-(1 / 2) : ℝ) * M
  let CL := M * (p.a + p.b * M ^ p.α)
  let Creact := heatGradientLinftyLinftyConstant *
    (2 * Real.sqrt T) * CL
  Cinit + |p.χ₀| * Cchem + Creact

theorem paper3MildMDerivPositiveTimeConstant_nonneg
    (p : CM2Params) {c M T tau : ℝ}
    (hc : 0 < c) (hcM : c ≤ M) (hM : 0 ≤ M)
    (hT : 0 ≤ T) (htau : 0 < tau) :
    0 ≤ paper3MildMDerivPositiveTimeConstant p c M T tau := by
  let Cchem := paper3ChemDuhamelMDerivPositiveTimeConstant
    p c M T (1 / 4) tau
  let Cinit := heatGradientLinftyLinftyConstant *
    tau ^ (-(1 / 2) : ℝ) * M
  let CL := M * (p.a + p.b * M ^ p.α)
  let Creact := heatGradientLinftyLinftyConstant *
    (2 * Real.sqrt T) * CL
  have hCchem : 0 ≤ Cchem := by
    simpa [Cchem] using paper3ChemDuhamelMDerivPositiveTimeConstant_nonneg
      p hc hcM hM hT (by norm_num) (by norm_num) htau
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
  unfold paper3MildMDerivPositiveTimeConstant
  dsimp only
  exact add_nonneg (add_nonneg hCinit
    (mul_nonneg (abs_nonneg _) hCchem)) hCreact

theorem conjugateMildM_intervalDomainLift_deriv_positiveTime_explicit
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {tau : ℝ} (htau : 0 < tau) :
    ∀ t, tau ≤ t → t ≤ D.T → ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      |deriv (intervalDomainLift (D.u t)) x| ≤
        paper3MildMDerivPositiveTimeConstant
          p D.c D.M D.T tau := by
  have hcM : D.c ≤ D.M := D.floor_le_bound
  let Cchem := paper3ChemDuhamelMDerivPositiveTimeConstant
    p D.c D.M D.T (1 / 4) tau
  let Cinit := heatGradientLinftyLinftyConstant *
    tau ^ (-(1 / 2) : ℝ) * D.M
  let CL := D.M * (p.a + p.b * D.M ^ p.α)
  let Creact := heatGradientLinftyLinftyConstant *
    (2 * Real.sqrt D.T) * CL
  have hCchem : 0 ≤ Cchem := by
    simpa [Cchem] using paper3ChemDuhamelMDerivPositiveTimeConstant_nonneg
      p D.hc hcM D.hM.le D.hT.le (by norm_num) (by norm_num) htau
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
  have hwhole := conjugateMildM_intervalDomainLift_hasDerivAt_interior
    D hu₀ hu₀_meas (θ := (1 / 4 : ℝ))
      (by norm_num) (by norm_num) ht htT hx
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
    conjugateMildM_chemDuhamel_deriv_positiveTime_explicit
      D hu₀ hu₀_meas (theta := (1 / 4 : ℝ))
        (by norm_num) (by norm_num) htau t htauT htT x
          (Set.Ioo_subset_Icc_self hx)
  have hreactRaw := conjugateMildM_logisticDuhamel_deriv_abs_le
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
              (chemFluxMLifted p (D.u s)) z) x) +
          ∫ s in (0 : ℝ)..t, deriv
            (fun z : ℝ => intervalFullSemigroupOperator (t - s)
              (logisticLifted p (D.u s)) z) x| ≤
        |∫ y, deriv (fun z : ℝ => intervalNeumannFullKernel t z y) x *
            intervalDomainLift u₀ y ∂(intervalMeasure 1)| +
          |(-p.χ₀) * (∫ s in (0 : ℝ)..t, deriv
            (fun z : ℝ => intervalConjugateKernelOperator (t - s)
              (chemFluxMLifted p (D.u s)) z) x)| +
          |∫ s in (0 : ℝ)..t, deriv
            (fun z : ℝ => intervalFullSemigroupOperator (t - s)
              (logisticLifted p (D.u s)) z) x| := by
    refine (abs_add_le _ _).trans ?_
    gcongr
    exact abs_add_le _ _
  refine htri.trans ?_
  unfold paper3MildMDerivPositiveTimeConstant
  dsimp only
  rw [abs_mul, abs_neg]
  exact add_le_add (add_le_add hinitBound
    (mul_le_mul_of_nonneg_left hchemBound (abs_nonneg _))) hreactBound

/-- Explicit uniform derivative bound for the faithful eliminated flux. -/
def paper3ChemFluxMDerivPositiveTimeConstant
    (p : CM2Params) (c M T tau : ℝ) : ℝ :=
  let CU := paper3MildMDerivPositiveTimeConstant p c M T tau
  let G0 := Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * M ^ p.γ))
  let L0 := ShenWork.IntervalResolverWeakBounds.resolverWeakLapBound p M
  let Lm := powerLip p.m c M
  let A := M ^ p.m
  (Lm * CU) * G0 + A * L0 + A * G0 * p.β * G0

theorem paper3ChemFluxMDerivPositiveTimeConstant_nonneg
    (p : CM2Params) {c M T tau : ℝ}
    (hc : 0 < c) (hcM : c ≤ M) (hM : 0 ≤ M)
    (hT : 0 ≤ T) (htau : 0 < tau) :
    0 ≤ paper3ChemFluxMDerivPositiveTimeConstant p c M T tau := by
  let CU := paper3MildMDerivPositiveTimeConstant p c M T tau
  let G0 := Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * M ^ p.γ))
  let L0 := ShenWork.IntervalResolverWeakBounds.resolverWeakLapBound p M
  let Lm := powerLip p.m c M
  let A := M ^ p.m
  have hCU : 0 ≤ CU := by
    simpa [CU] using paper3MildMDerivPositiveTimeConstant_nonneg
      p hc hcM hM hT htau
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
  have hLm : 0 ≤ Lm := by
    dsimp [Lm]
    exact powerLip_nonneg p.hm hc hcM
  have hA : 0 ≤ A := by
    dsimp [A]
    exact Real.rpow_nonneg hM _
  unfold paper3ChemFluxMDerivPositiveTimeConstant
  dsimp only
  exact add_nonneg
    (add_nonneg (mul_nonneg (mul_nonneg hLm hCU) hG0)
      (mul_nonneg hA hL0))
    (mul_nonneg (mul_nonneg (mul_nonneg hA hG0) p.hβ) hG0)

theorem conjugateMildM_chemFlux_deriv_positiveTime_explicit
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {tau : ℝ} (htau : 0 < tau) :
    ∀ t, tau ≤ t → t ≤ D.T → ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      |deriv (chemFluxMLifted p (D.u t)) x| ≤
        paper3ChemFluxMDerivPositiveTimeConstant
          p D.c D.M D.T tau := by
  let CU := paper3MildMDerivPositiveTimeConstant p D.c D.M D.T tau
  let G0 := Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * D.M ^ p.γ))
  let L0 := ShenWork.IntervalResolverWeakBounds.resolverWeakLapBound p D.M
  have hcM : D.c ≤ D.M := D.floor_le_bound
  let Lm := powerLip p.m D.c D.M
  let A := D.M ^ p.m
  have hCU : 0 ≤ CU := by
    simpa [CU] using paper3MildMDerivPositiveTimeConstant_nonneg
      p D.hc hcM D.hM.le D.hT.le htau
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
  have hLm : 0 ≤ Lm := by
    dsimp [Lm]
    exact powerLip_nonneg p.hm D.hc hcM
  have hA : 0 ≤ A := by
    dsimp [A]
    exact Real.rpow_nonneg D.hM.le _
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
  have hUraw := conjugateMildM_intervalDomainLift_hasDerivAt_interior
    D hu₀ hu₀_meas (θ := (1 / 4 : ℝ))
      (by norm_num) (by norm_num) ht htT hx
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
  have hRnonneg : 0 ≤ R x := by
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
  have hUxpos : 0 < U x := by
    simpa [U, intervalDomainLift, hxIcc] using
      D.hc.trans_le (D.hfloor t ht htT ⟨x, hxIcc⟩)
  have hUxfloor : D.c ≤ U x := by
    simpa [U, intervalDomainLift, hxIcc] using
      D.hfloor t ht htT ⟨x, hxIcc⟩
  have hUxle : U x ≤ D.M := by
    simpa [U, intervalDomainLift, hxIcc] using
      (abs_le.mp (D.hbound t ht htT ⟨x, hxIcc⟩)).2
  have hUm' : HasDerivAt (fun z => U z ^ p.m)
      ((p.m * U x ^ (p.m - 1)) * deriv U x) x := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      hU'.rpow_const (p := p.m) (Or.inl hUxpos.ne')
  have hprod := (hUm'.mul hG').mul hW'
  have hev : chemFluxMLifted p (D.u t) =ᶠ[nhds x]
      (fun z => U z ^ p.m * G z * W z) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with z hz
    have hzIcc := Set.Ioo_subset_Icc_self hz
    have hRz : 0 ≤ R z := by
      have h := ShenWork.IntervalMildToClassical.mildChemical_nonneg
        (T := D.T) p (u := D.u)
          (fun s hs hsT y => D.hc.le.trans (D.hfloor s hs hsT y))
          D.hcont ht htT ⟨z, hzIcc⟩
      simpa [R, ShenWork.IntervalMildToClassical.mildChemicalConcentration,
        intervalDomainLift, hzIcc] using h
    unfold chemFluxMLifted
    rw [div_eq_mul_inv, ← Real.rpow_neg (by linarith : 0 ≤ 1 + R z)]
  have hflux := hev.hasDerivAt_iff.mpr hprod
  have hUderiv : |deriv U x| ≤ CU := by
    simpa [U, CU] using
      conjugateMildM_intervalDomainLift_deriv_positiveTime_explicit
        D hu₀ hu₀_meas htau t htauT htT x hx
  have hpow : U x ^ (p.m - 1) ≤
      D.c ^ (p.m - 1) + D.M ^ (p.m - 1) := by
    rcases le_or_gt 1 p.m with hm1 | hm1
    · have hmono : U x ^ (p.m - 1) ≤ D.M ^ (p.m - 1) :=
        Real.rpow_le_rpow hUxpos.le hUxle (by linarith)
      linarith [Real.rpow_nonneg D.hc.le (p.m - 1)]
    · have hmono : U x ^ (p.m - 1) ≤ D.c ^ (p.m - 1) :=
        Real.rpow_le_rpow_of_nonpos D.hc hUxfloor (by linarith)
      linarith [Real.rpow_nonneg D.hM.le (p.m - 1)]
  have hcoeff : |p.m * U x ^ (p.m - 1)| ≤ Lm := by
    dsimp [Lm, powerLip]
    rw [abs_of_nonneg
      (mul_nonneg p.hm.le (Real.rpow_nonneg hUxpos.le _))]
    exact mul_le_mul_of_nonneg_left hpow p.hm.le
  have hUmabs : |U x ^ p.m| ≤ A := by
    rw [abs_of_nonneg (Real.rpow_nonneg hUxpos.le _)]
    dsimp [A]
    exact Real.rpow_le_rpow hUxpos.le hUxle p.hm.le
  have hUmderiv : |(p.m * U x ^ (p.m - 1)) * deriv U x| ≤ Lm * CU := by
    rw [abs_mul]
    exact mul_le_mul hcoeff hUderiv (abs_nonneg _) hLm
  simp only [abs_mul] at hUmderiv
  have hGabs : |G x| ≤ G0 := by
    dsimp [G0]
    exact ShenWork.IntervalResolverWeakBounds.resolverGrad_sup_le_of_bounded
      p hUcont
        (fun z hz => by
          have h := D.hc.le.trans (D.hfloor t ht htT ⟨z, hz⟩)
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
            have h := D.hc.le.trans (D.hfloor t ht htT ⟨z, hz⟩)
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
  have hsum :
      |((p.m * U x ^ (p.m - 1)) * deriv U x) * G x +
          U x ^ p.m * deriv G x| ≤ (Lm * CU) * G0 + A * L0 := by
    calc
      _ ≤ |((p.m * U x ^ (p.m - 1)) * deriv U x) * G x| +
          |U x ^ p.m * deriv G x| := abs_add_le _ _
      _ ≤ (Lm * CU) * G0 + A * L0 := by
        simp only [abs_mul]
        exact add_le_add
          (mul_le_mul hUmderiv hGabs (abs_nonneg _)
            (mul_nonneg hLm hCU))
          (mul_le_mul hUmabs hGderiv (abs_nonneg _) hA)
  have hfirst :
      |(((p.m * U x ^ (p.m - 1)) * deriv U x) * G x +
          U x ^ p.m * deriv G x) * W x| ≤
        ((Lm * CU) * G0 + A * L0) * 1 := by
    rw [abs_mul]
    exact mul_le_mul hsum hWabs (abs_nonneg _)
      (add_nonneg (mul_nonneg (mul_nonneg hLm hCU) hG0)
        (mul_nonneg hA hL0))
  have hsecond :
      |U x ^ p.m * G x *
          (G x * (-p.β) * (1 + R x) ^ (-p.β - 1))| ≤
        A * G0 * (p.β * G0) := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul
      (mul_le_mul hUmabs hGabs (abs_nonneg _) hA) hWderiv
      (abs_nonneg _) (mul_nonneg hA hG0)
  refine (abs_add_le _ _).trans ?_
  unfold paper3ChemFluxMDerivPositiveTimeConstant
  dsimp only
  calc
    |(((p.m * U x ^ (p.m - 1)) * deriv U x) * G x +
          U x ^ p.m * deriv G x) * W x| +
        |U x ^ p.m * G x *
          (G x * (-p.β) * (1 + R x) ^ (-p.β - 1))| ≤
      ((Lm * CU) * G0 + A * L0) * 1 + A * G0 * (p.β * G0) :=
        add_le_add hfirst hsecond
    _ = (Lm * CU) * G0 + A * L0 + A * G0 * p.β * G0 := by ring

#print axioms conjugateMildMHolderConstant_nonneg
#print axioms paper3ChemFluxMPositiveTimeHolderConstant_nonneg
#print axioms conjugateMildM_chemFlux_positiveTime_holder_explicit
#print axioms paper3ChemDuhamelMDerivPositiveTimeConstant_nonneg
#print axioms conjugateMildM_chemDuhamel_deriv_positiveTime_explicit
#print axioms paper3MildMDerivPositiveTimeConstant_nonneg
#print axioms conjugateMildM_intervalDomainLift_deriv_positiveTime_explicit
#print axioms paper3ChemFluxMDerivPositiveTimeConstant_nonneg
#print axioms conjugateMildM_chemFlux_deriv_positiveTime_explicit

end

end ShenWork.Paper3
