/- Uniform weak-sup bootstrap around a positive constant equilibrium. -/
import ShenWork.Paper3.IntervalDomainClassicalRestartPointwise
import ShenWork.Paper3.IntervalDomainConstantResolver
import ShenWork.Paper2.IntervalChiNegTruncatedRestartStrictPos
import ShenWork.Paper2.IntervalPositiveFloorConjugateContraction
import ShenWork.Paper2.IntervalDuhamelIntegrability
import ShenWork.PDE.IntervalFullKernelSecondDerivCtheta
import ShenWork.PDE.IntervalSemigroupC1ApproxIdentity
import ShenWork.PDE.RestartedMildSmoothing

namespace ShenWork.Paper3

open MeasureTheory Set Filter Topology
open scoped Topology Interval
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.IntervalGradientDuhamelMap
  (chemFluxLifted logisticLifted)
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateDuhamelMap)
open ShenWork.IntervalMildPicard
  (HasContinuousSlices HasJointMeasurability)
open ShenWork.IntervalNeumannFullKernel
  (intervalFullSemigroupOperator intervalFullSemigroupOperator_const)
open ShenWork.IntervalPositiveFloorNonlinearLipschitz
  (powerLip powerLip_nonneg logisticReaction_lipschitz_on_pos_Icc)
open ShenWork.IntervalPositiveFloorConjugateContraction
  (intervalConjugateDuhamelMap_diff_bound_of_positive_cone)
open ShenWork.HeatKernelGradientEstimates
  (heatGradientLinftyLinftyConstant heatGradientLinftyLinftyConstant_nonneg)
open ShenWork.PDE

noncomputable section

local instance : TopologicalSpace intervalDomain.Point :=
  inferInstanceAs (TopologicalSpace intervalDomainPoint)

/-- Fixed lower edge of the weak positive tube. -/
def intervalDomainWeakSupConeFloor (uStar : ℝ) : ℝ := uStar / 2

/-- Fixed upper edge of the weak positive tube. -/
def intervalDomainWeakSupConeCeiling (uStar : ℝ) : ℝ := 3 * uStar / 2

/-- Flux Lipschitz constant on the fixed weak positive tube. -/
def intervalDomainWeakSupChemLipschitzConstant
    (p : CM2Params) (uStar : ℝ) : ℝ :=
  let c := intervalDomainWeakSupConeFloor uStar
  let M := intervalDomainWeakSupConeCeiling uStar
  Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
      (2 * (p.ν * M ^ p.γ)) +
    M * (Real.sqrt (∑' k : ℕ,
      (intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * powerLip p.γ c M))) +
    M * (Real.sqrt (∑' k : ℕ,
      (intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * M ^ p.γ))) * p.β *
      (Real.sqrt (∑' k : ℕ,
        (intervalNeumannResolverWeight p k) ^ 2) *
          (2 * (p.ν * powerLip p.γ c M)))

/-- Short-window contraction coefficient for the weak B-form map. -/
def intervalDomainWeakSupContractionCoefficient
    (p : CM2Params) (uStar CL T : ℝ) : ℝ :=
  |p.χ₀| *
      (heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) *
        intervalDomainWeakSupChemLipschitzConstant p uStar) +
    T * CL

theorem intervalDomainWeakSupConeFloor_pos
    {uStar : ℝ} (huStar : 0 < uStar) :
    0 < intervalDomainWeakSupConeFloor uStar := by
  simp [intervalDomainWeakSupConeFloor]
  linarith

theorem intervalDomainWeakSupConeFloor_le_ceiling
    {uStar : ℝ} (huStar : 0 < uStar) :
    intervalDomainWeakSupConeFloor uStar ≤
      intervalDomainWeakSupConeCeiling uStar := by
  simp [intervalDomainWeakSupConeFloor, intervalDomainWeakSupConeCeiling]
  linarith

theorem intervalDomainWeakSupChemLipschitzConstant_nonneg
    (p : CM2Params) {uStar : ℝ} (huStar : 0 < uStar) :
    0 ≤ intervalDomainWeakSupChemLipschitzConstant p uStar := by
  let c := intervalDomainWeakSupConeFloor uStar
  let M := intervalDomainWeakSupConeCeiling uStar
  have hc : 0 < c := intervalDomainWeakSupConeFloor_pos huStar
  have hcM : c ≤ M := intervalDomainWeakSupConeFloor_le_ceiling huStar
  have hM : 0 < M := hc.trans_le hcM
  have hLip : 0 ≤ powerLip p.γ c M := powerLip_nonneg p.hγ hc hcM
  have hRG : 0 ≤ Real.sqrt (∑' k : ℕ,
      (intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * M ^ p.γ)) :=
    mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num)
        (mul_nonneg p.hν.le (Real.rpow_nonneg hM.le _)))
  have hRGL : 0 ≤ Real.sqrt (∑' k : ℕ,
      (intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * powerLip p.γ c M)) :=
    mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num) (mul_nonneg p.hν.le hLip))
  have hRV : 0 ≤ Real.sqrt (∑' k : ℕ,
      (intervalNeumannResolverWeight p k) ^ 2) *
        (2 * (p.ν * powerLip p.γ c M)) :=
    mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num) (mul_nonneg p.hν.le hLip))
  dsimp [intervalDomainWeakSupChemLipschitzConstant, c, M]
  exact add_nonneg (add_nonneg hRG (mul_nonneg hM.le hRGL))
    (mul_nonneg (mul_nonneg (mul_nonneg hM.le hRG) p.hβ) hRV)

/-- A datum-independent positive time on which the weak B-form contraction
coefficient is strictly below one quarter. -/
theorem exists_intervalDomainWeakSupContractionWindow
    (p : CM2Params) {uStar : ℝ} (huStar : 0 < uStar) :
    ∃ T > 0, ∃ CL > 0,
      (∀ r s : ℝ,
        |r| ≤ intervalDomainWeakSupConeCeiling uStar →
        |s| ≤ intervalDomainWeakSupConeCeiling uStar →
        |r * (p.a - p.b * r ^ p.α) -
          s * (p.a - p.b * s ^ p.α)| ≤ CL * |r - s|) ∧
      intervalDomainWeakSupContractionCoefficient p uStar CL T < 1 / 4 := by
  let CQ := intervalDomainWeakSupChemLipschitzConstant p uStar
  have hM : 0 < intervalDomainWeakSupConeCeiling uStar := by
    dsimp [intervalDomainWeakSupConeCeiling]
    linarith
  obtain ⟨CL, hCL, hCLlip⟩ :=
    ShenWork.IntervalDomainExistence.intervalLogisticSource_lipschitz p hM
  let A := |p.χ₀| * heatGradientLinftyLinftyConstant * 2 * CQ
  have hCQ : 0 ≤ CQ := by
    simpa [CQ] using intervalDomainWeakSupChemLipschitzConstant_nonneg p huStar
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (abs_nonneg _)
          heatGradientLinftyLinftyConstant_nonneg)
        (by norm_num)) hCQ
  obtain ⟨T, hT, hsmall⟩ :=
    exists_small_contraction_time_target hA hCL.le
      (by norm_num : (0 : ℝ) < 1 / 4)
  refine ⟨T, hT, CL, hCL, hCLlip, ?_⟩
  have heq : intervalDomainWeakSupContractionCoefficient p uStar CL T =
      A * Real.sqrt T + CL * T := by
    dsimp [intervalDomainWeakSupContractionCoefficient, A, CQ]
    ring
  rw [heq]
  simpa [mul_comm] using hsmall

/-- Spatial sup distance along a clamped positive-time restart. -/
def intervalDomainRestartSupDistance
    (a h uStar : ℝ) (u : ℝ → intervalDomainPoint → ℝ) (r : ℝ) : ℝ :=
  sSup ((fun y : ℝ => |restartField a h u r y - uStar|) ''
    Set.Icc (0 : ℝ) 1)

theorem intervalDomainRestartSupDistance_continuous
    {p : CM2Params} {T a h uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hh : 0 ≤ h) (hahT : a + h < T) :
    Continuous (intervalDomainRestartSupDistance a h uStar u) := by
  have hfield := restartField_continuous hsol ha hh hahT u (Or.inl rfl)
  unfold intervalDomainRestartSupDistance
  apply isCompact_Icc.continuous_sSup
  exact hfield.sub continuous_const |>.abs

theorem abs_restartField_sub_le_restartSupDistance
    {a h uStar r y : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (hcont : ContinuousOn
      (fun z : ℝ => |restartField a h u r z - uStar|)
      (Set.Icc (0 : ℝ) 1))
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |restartField a h u r y - uStar| ≤
      intervalDomainRestartSupDistance a h uStar u r := by
  have hbdd : BddAbove
      ((fun z : ℝ => |restartField a h u r z - uStar|) ''
        Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.bddAbove_image hcont
  unfold intervalDomainRestartSupDistance
  exact le_csSup hbdd ⟨y, hy, rfl⟩

theorem intervalDomainRestartSupDistance_nonneg
    (a h uStar : ℝ) (u : ℝ → intervalDomainPoint → ℝ) (r : ℝ)
    (hcont : ContinuousOn
      (fun z : ℝ => |restartField a h u r z - uStar|)
      (Set.Icc (0 : ℝ) 1)) :
    0 ≤ intervalDomainRestartSupDistance a h uStar u r := by
  exact (abs_nonneg (restartField a h u r 0 - uStar)).trans
    (abs_restartField_sub_le_restartSupDistance
      hcont
      (by norm_num : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1))

/-- The faithful chemotaxis flux vanishes on a constant density. -/
theorem chemFluxLifted_const_eq_zero
    (p : CM2Params) (uStar y : ℝ) :
    chemFluxLifted p (fun _ : intervalDomainPoint => uStar) y = 0 := by
  by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
  · unfold chemFluxLifted
    rw [resolverGradReal_eq p (fun _ : intervalDomainPoint => uStar) ⟨y, hy⟩,
      intervalNeumannResolverRGrad_const]
    simp
  · simp [chemFluxLifted, intervalDomainLift, hy]

/-- The logistic source vanishes on a constant equilibrium density. -/
theorem logisticLifted_const_eq_zero
    (p : CM2Params) {uStar vStar y : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar) :
    logisticLifted p (fun _ : intervalDomainPoint => uStar) y = 0 := by
  by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
  · simp [logisticLifted,
      ShenWork.IntervalDomainExistence.intervalLogisticSource,
      intervalDomainLift, hy, heq.reaction_eq_zero]
  · simp [logisticLifted, intervalDomainLift, hy]

/-- The weak B-form map fixes a positive constant equilibrium. -/
theorem intervalConjugateDuhamelMap_const_equilibrium
    (p : CM2Params) {uStar vStar t : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (ht : 0 < t) (x : intervalDomainPoint) :
    intervalConjugateDuhamelMap p
        (fun _ : intervalDomainPoint => uStar)
        (fun (_ : ℝ) (_ : intervalDomainPoint) => uStar) t x = uStar := by
  unfold intervalConjugateDuhamelMap
  have hhom : intervalFullSemigroupOperator t
      (intervalDomainLift (fun _ : intervalDomainPoint => uStar)) x.1 = uStar := by
    rw [ShenWork.IntervalSemigroupC1ApproxIdentity.intervalFullSemigroupOperator_congr_on_Icc
      (g := fun _ : ℝ => uStar)
      (fun y hy => by simp [intervalDomainLift, hy]) t x.1]
    exact intervalFullSemigroupOperator_const ht uStar x.1
  have hchem : ∀ s : ℝ,
      ShenWork.IntervalConjugateDuhamelMap.intervalConjugateKernelOperator
        (t - s)
        (chemFluxLifted p
          ((fun (_ : ℝ) (_ : intervalDomainPoint) => uStar) s)) x.1 = 0 := by
    intro s
    rw [show chemFluxLifted p
        ((fun (_ : ℝ) (_ : intervalDomainPoint) => uStar) s) = 0 from by
      funext y
      exact chemFluxLifted_const_eq_zero p uStar y]
    unfold ShenWork.IntervalConjugateDuhamelMap.intervalConjugateKernelOperator
    simp
  have hlog : ∀ s : ℝ,
      intervalFullSemigroupOperator (t - s)
        (logisticLifted p
          ((fun (_ : ℝ) (_ : intervalDomainPoint) => uStar) s)) x.1 = 0 := by
    intro s
    rw [show logisticLifted p
        ((fun (_ : ℝ) (_ : intervalDomainPoint) => uStar) s) = 0 from by
      funext y
      exact logisticLifted_const_eq_zero p heq]
    unfold intervalFullSemigroupOperator
    simp
  rw [hhom]
  simp_rw [hchem, hlog]
  simp

/-- Changing only the initial datum in the B-form map costs at most the
corresponding `L∞` distance; the nonlinear trajectory cancels exactly. -/
theorem intervalConjugateDuhamelMap_initialDatum_diff_le
    (p : CM2Params)
    {u₀ z₀ : intervalDomainPoint → ℝ}
    {w : ℝ → intervalDomainPoint → ℝ}
    {t d Mu Mz : ℝ}
    (ht : 0 < t) (hd : 0 ≤ d)
    (huInt : Integrable (intervalDomainLift u₀) (intervalMeasure 1))
    (hzInt : Integrable (intervalDomainLift z₀) (intervalMeasure 1))
    (hMu : 0 ≤ Mu) (huBound : ∀ y, |intervalDomainLift u₀ y| ≤ Mu)
    (hMz : 0 ≤ Mz) (hzBound : ∀ y, |intervalDomainLift z₀ y| ≤ Mz)
    (hdiff : ∀ y, |intervalDomainLift u₀ y - intervalDomainLift z₀ y| ≤ d)
    (x : intervalDomainPoint) :
    |intervalConjugateDuhamelMap p u₀ w t x -
      intervalConjugateDuhamelMap p z₀ w t x| ≤ d := by
  have hheat :=
    ShenWork.IntervalDuhamelIntegrability.intervalFullSemigroupOperator_diff_Linfty_of_integrable
      ht huInt hzInt hMu huBound hMz hzBound hd hdiff x.1
  calc
    |intervalConjugateDuhamelMap p u₀ w t x -
        intervalConjugateDuhamelMap p z₀ w t x| =
      |intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1 -
        intervalFullSemigroupOperator t (intervalDomainLift z₀) x.1| := by
          unfold intervalConjugateDuhamelMap
          congr 1
          ring
    _ ≤ d := hheat

/-- A uniform positive restart window attached to a weakly small orbit.  Its
packaged mild trajectory has fixed horizon and fixed positive-cone radius,
which is the input needed by the positive-time smoothing estimates. -/
structure IntervalDomainWeakSupRestartWindowData
    (p : CM2Params) (uStar T delta : ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) where
  a : ℝ
  a_pos : 0 < a
  a_le_quarter : a ≤ T / 4
  a_lt_half : a < T / 2
  mild : ShenWork.IntervalConjugatePicard.ConjugateMildSolutionData p (u a)
  mild_T : mild.T = T
  mild_M : mild.M = intervalDomainWeakSupConeCeiling uStar
  mild_u : mild.u = intervalDomainRestartTrajectory a T u
  close : ∀ r, 0 ≤ r → r ≤ T → ∀ x : intervalDomainPoint,
    |mild.u r x - uStar| ≤ 4 * delta

/-- The target absolute time `T` lies in the last half of the restarted mild
window and represents the original orbit exactly. -/
theorem IntervalDomainWeakSupRestartWindowData.target
    {p : CM2Params} {uStar T delta : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (D : IntervalDomainWeakSupRestartWindowData p uStar T delta u) :
    0 < T - D.a ∧ T / 2 < T - D.a ∧ T - D.a ≤ D.mild.T ∧
      D.mild.u (T - D.a) = u T := by
  have hT : 0 < T := by linarith [D.a_pos, D.a_lt_half]
  have hrmem : T - D.a ∈ Set.Icc (0 : ℝ) T := by
    constructor
    · linarith [D.a_le_quarter, hT]
    · linarith [D.a_pos]
  refine ⟨by linarith [D.a_lt_half], by linarith [D.a_lt_half], ?_, ?_⟩
  · rw [D.mild_T]
    exact hrmem.2
  · rw [D.mild_u, intervalDomainRestartTrajectory_eq hrmem]
    congr 1
    ring

/-- Weak-sup first-exit closure on a fixed contraction window lying strictly
inside a finite classical horizon. -/
theorem intervalDomainWeakSupRestartWindowData_of_contraction_of_solution
    (p : CM2Params) {uStar vStar T CL delta H : ℝ}
    (hm : p.m = 1)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hT : 0 < T) (hCL : 0 < CL)
    (hCLlip : ∀ r s : ℝ,
      |r| ≤ intervalDomainWeakSupConeCeiling uStar →
      |s| ≤ intervalDomainWeakSupConeCeiling uStar →
      |r * (p.a - p.b * r ^ p.α) -
        s * (p.a - p.b * s ^ p.α)| ≤ CL * |r - s|)
    (hcontract :
      intervalDomainWeakSupContractionCoefficient p uStar CL T < 1 / 4)
    (hdelta : 0 < delta) (hdeltaStar : delta ≤ uStar / 16)
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hclose : SupCloseToConstant intervalDomain u₀ uStar delta)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p H u v)
    (hHT : 5 * T / 4 < H)
    (htrace : InitialTrace intervalDomain u₀ u) :
    Nonempty (IntervalDomainWeakSupRestartWindowData
      p uStar T delta u) := by
  classical
  let c := intervalDomainWeakSupConeFloor uStar
  let M := intervalDomainWeakSupConeCeiling uStar
  let q := uStar / 2
  let CQ := intervalDomainWeakSupChemLipschitzConstant p uStar
  let K := intervalDomainWeakSupContractionCoefficient p uStar CL T
  let d0 := 2 * delta
  have huStar : 0 < uStar := heq.u_pos
  have hc : 0 < c := by simpa [c] using intervalDomainWeakSupConeFloor_pos huStar
  have hM : 0 < M := by
    dsimp [M, intervalDomainWeakSupConeCeiling]
    linarith
  have hcM : c ≤ M := by
    simpa [c, M] using intervalDomainWeakSupConeFloor_le_ceiling huStar
  have hq : 0 < q := by dsimp [q]; linarith
  have hCQ : 0 ≤ CQ := by
    simpa [CQ] using intervalDomainWeakSupChemLipschitzConstant_nonneg p huStar
  have hK : 0 ≤ K := by
    dsimp [K, intervalDomainWeakSupContractionCoefficient]
    exact add_nonneg
      (mul_nonneg (abs_nonneg _)
        (mul_nonneg
          (mul_nonneg heatGradientLinftyLinftyConstant_nonneg
            (mul_nonneg (by norm_num) (Real.sqrt_nonneg T))) hCQ))
      (mul_nonneg hT.le hCL.le)
  have hKquarter : K < 1 / 4 := by simpa [K] using hcontract
  have hd0 : 0 ≤ d0 := by dsimp [d0]; linarith
  have hd0q : d0 ≤ q / 4 := by
    dsimp [d0, q]
    linarith
  have hd0Star : d0 ≤ uStar / 8 := by
    dsimp [d0]
    linarith
  obtain ⟨eta, heta, htraceEta⟩ := htrace.eventually_small hdelta
  let a := min (eta / 2) (T / 4)
  have ha : 0 < a := by
    dsimp [a]
    exact lt_min (by linarith) (by linarith)
  have haEta : a < eta := by
    have : a ≤ eta / 2 := min_le_left _ _
    linarith
  have haHalf : a < T / 2 := by
    have : a ≤ T / 4 := min_le_right _ _
    linarith
  have haQuarter : a ≤ T / 4 := min_le_right _ _
  have haTH : a + T < H := by
    calc
      a + T ≤ T / 4 + T := by linarith [haQuarter]
      _ = 5 * T / 4 := by ring
      _ < H := hHT
  let hsolM := isPaper2ClassicalSolution_intervalDomainM_of_m_eq_one
    p hm hsol
  let w : ℝ → intervalDomainPoint → ℝ :=
    intervalDomainRestartTrajectory a T u
  let z : ℝ → intervalDomainPoint → ℝ :=
    fun _ _ => uStar
  have hwcontT : HasContinuousSlices T w := by
    simpa [w] using intervalDomainRestartTrajectory_hasContinuousSlices
      hsolM ha hT.le haTH
  have hwmeas : HasJointMeasurability w := by
    simpa [w] using intervalDomainRestartTrajectory_hasJointMeasurability
      hsolM ha hT.le haTH
  have hzcont : ∀ R : ℝ, HasContinuousSlices R z := by
    intro R _r _hr _hrR
    exact continuous_const
  have hzmeas : HasJointMeasurability z := by
    unfold HasJointMeasurability z
    simp only [intervalDomainLift]
    exact Measurable.ite (measurableSet_Icc.preimage measurable_snd)
      measurable_const measurable_const
  have huaTime : a ∈ Set.Ioo (0 : ℝ) H := by
    constructor
    · exact ha
    · linarith [haTH, hT]
  have huaCont : Continuous (u a) :=
    solutionSlice_continuous hsolM huaTime
  have hfield := restartField_continuous hsolM ha hT.le haTH u (Or.inl rfl)
  have hsizeCont : Continuous (intervalDomainRestartSupDistance a T uStar u) :=
    intervalDomainRestartSupDistance_continuous hsolM ha hT.le haTH
  have hsizePoint : ∀ r y, y ∈ Set.Icc (0 : ℝ) 1 →
      |restartField a T u r y - uStar| ≤
        intervalDomainRestartSupDistance a T uStar u r := by
    intro r y hy
    apply abs_restartField_sub_le_restartSupDistance
    · exact ((hfield.comp (continuous_const.prodMk continuous_id)).sub
          continuous_const).abs.continuousOn
    · exact hy
  have hu₀ConstBdd : BddAbove
      (Set.range (fun x : intervalDomainPoint => |(fun _ => uStar) x|)) :=
    ⟨|uStar|, by rintro _ ⟨x, rfl⟩; exact le_rfl⟩
  have hu₀DiffBdd : BddAbove
      (Set.range (fun x : intervalDomainPoint => |u₀ x - uStar|)) :=
    ShenWork.Paper2.BFormPositiveDatumNegPart.bddAbove_abs_sub_of_bddAbove_abs_restart
      hu₀.admissible.1 hu₀ConstBdd
  have hu₀Close : ∀ x : intervalDomainPoint, |u₀ x - uStar| < delta :=
    ShenWork.Paper2.BFormPositiveDatumNegPart.intervalDomain_pointwise_abs_lt_of_supNorm_lt_restart
      hu₀DiffBdd hclose.lt
  obtain ⟨Bu, hBu, huaBoundRaw⟩ :=
    exists_solutionLift_abs_bound hsolM huaTime
  have huaBdd : BddAbove
      (Set.range (fun x : intervalDomainPoint => |u a x|)) := by
    refine ⟨Bu, ?_⟩
    rintro _ ⟨x, rfl⟩
    have h := huaBoundRaw x.1
    simpa [intervalDomainLift, x.2] using h
  have huaDiffBdd : BddAbove
      (Set.range (fun x : intervalDomainPoint => |u a x - u₀ x|)) :=
    ShenWork.Paper2.BFormPositiveDatumNegPart.bddAbove_abs_sub_of_bddAbove_abs_restart
      huaBdd hu₀.admissible.1
  have huaTraceSup : intervalDomain.supNorm (fun x => u a x - u₀ x) < delta :=
    htraceEta a ha haEta
  have huaTrace : ∀ x : intervalDomainPoint, |u a x - u₀ x| < delta :=
    ShenWork.Paper2.BFormPositiveDatumNegPart.intervalDomain_pointwise_abs_lt_of_supNorm_lt_restart
      huaDiffBdd huaTraceSup
  have huaClose : ∀ x : intervalDomainPoint, |u a x - uStar| ≤ d0 := by
    intro x
    dsimp [d0]
    calc
      |u a x - uStar| =
          |(u a x - u₀ x) + (u₀ x - uStar)| := by ring_nf
      _ ≤ |u a x - u₀ x| + |u₀ x - uStar| := abs_add_le _ _
      _ ≤ 2 * delta := by
        linarith [huaTrace x, hu₀Close x]
  have hsizeZero : intervalDomainRestartSupDistance a T uStar u 0 ≤ d0 := by
    unfold intervalDomainRestartSupDistance
    apply csSup_le
    · refine ⟨|restartField a T u 0 0 - uStar|, ?_⟩
      exact ⟨0, (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1), rfl⟩
    · intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      change |restartField a T u 0 x - uStar| ≤ d0
      rw [restartField_eq_physical
        (by constructor <;> linarith [hT]) hx]
      simpa [intervalDomainLift, hx] using huaClose ⟨x, hx⟩
  have huaLiftClose : ∀ y,
      |intervalDomainLift (u a) y -
        intervalDomainLift (fun _ : intervalDomainPoint => uStar) y| ≤ d0 := by
    intro y
    by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
    · simpa [intervalDomainLift, hy] using huaClose ⟨y, hy⟩
    · simp [intervalDomainLift, hy, hd0]
  have huaLiftBound : ∀ y, |intervalDomainLift (u a) y| ≤ M := by
    intro y
    by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
    · have hcloseY := huaClose ⟨y, hy⟩
      have hupper : u a ⟨y, hy⟩ ≤ M := by
        rw [abs_le] at hcloseY
        dsimp [M, intervalDomainWeakSupConeCeiling]
        linarith [hcloseY.2, hd0Star]
      have hlower : 0 ≤ u a ⟨y, hy⟩ := by
        rw [abs_le] at hcloseY
        linarith [hcloseY.1, hd0Star, huStar]
      simpa [intervalDomainLift, hy, abs_of_nonneg hlower] using hupper
    · simp [intervalDomainLift, hy, hM.le]
  have hzLiftBound : ∀ y,
      |intervalDomainLift (fun _ : intervalDomainPoint => uStar) y| ≤ M := by
    intro y
    by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
    · simp [intervalDomainLift, hy, abs_of_pos huStar]
      dsimp [M, intervalDomainWeakSupConeCeiling]
      linarith
    · simp [intervalDomainLift, hy, hM.le]
  have huaLiftMeas : Measurable (intervalDomainLift (u a)) :=
    ShenWork.IntervalMildPicardThreshold.intervalDomainLift_measurable_of_continuous'
      huaCont
  have hzLiftMeas : Measurable
      (intervalDomainLift (fun _ : intervalDomainPoint => uStar)) :=
    ShenWork.IntervalMildPicardThreshold.intervalDomainLift_measurable_of_continuous'
      continuous_const
  have huaInt : Integrable (intervalDomainLift (u a)) (intervalMeasure 1) :=
    intervalMeasure_integrable_of_abs_bound
      huaLiftMeas.aestronglyMeasurable huaLiftBound
  have hzInt : Integrable
      (intervalDomainLift (fun _ : intervalDomainPoint => uStar))
      (intervalMeasure 1) :=
    intervalMeasure_integrable_of_abs_bound
      hzLiftMeas.aestronglyMeasurable hzLiftBound
  have hmapBound : ∀ R d : ℝ, 0 < R → R ≤ T → 0 ≤ d →
      (∀ tau, 0 < tau → tau ≤ R → ∀ x,
        |w tau x - uStar| ≤ q) →
      (∀ tau, 0 < tau → tau ≤ R → ∀ x,
        |w tau x - uStar| ≤ d) →
      ∀ s, 0 < s → s ≤ R → ∀ x,
        |w s x - uStar| ≤
          intervalDomainWeakSupContractionCoefficient p uStar CL R * d + d0 := by
    intro R d hR hRT hd hband hdist s hs hsR x
    have hRwcont : HasContinuousSlices R w := by
      intro tau htau htauR
      exact hwcontT tau htau (htauR.trans hRT)
    have hwBound : ∀ tau, 0 < tau → tau ≤ R → ∀ y, |w tau y| ≤ M := by
      intro tau htau htauR y
      have hb := hband tau htau htauR y
      have hab := abs_le.mp hb
      have hy0 : 0 ≤ w tau y := by
        dsimp [q, c, intervalDomainWeakSupConeFloor] at hab ⊢
        linarith
      rw [abs_of_nonneg hy0]
      dsimp [q, M, intervalDomainWeakSupConeCeiling] at hab ⊢
      linarith
    have hwFloor : ∀ tau, 0 < tau → tau ≤ R → ∀ y, c ≤ w tau y := by
      intro tau htau htauR y
      have hb := abs_le.mp (hband tau htau htauR y)
      dsimp [q, c, intervalDomainWeakSupConeFloor] at hb ⊢
      linarith
    have hzBound : ∀ tau, 0 < tau → tau ≤ R → ∀ y, |z tau y| ≤ M := by
      intro _ _ _ _
      dsimp [z, M, intervalDomainWeakSupConeCeiling]
      rw [abs_of_pos huStar]
      linarith
    have hzFloor : ∀ tau, 0 < tau → tau ≤ R → ∀ y, c ≤ z tau y := by
      intro _ _ _ _
      dsimp [z, c, intervalDomainWeakSupConeFloor]
      linarith
    have hnonlin := intervalConjugateDuhamelMap_diff_bound_of_positive_cone
      p (u₀ := u a) (T := R) (M := M) (c := c) (CQ := CQ) (CL := CL)
      (d := d) hR hM hc hcM (by rfl) hCL.le hCLlip
      hwBound hwFloor hzBound hzFloor hRwcont (hzcont R)
      hwmeas hzmeas hdist hs (hsR.trans le_rfl) x
    have hdatum := intervalConjugateDuhamelMap_initialDatum_diff_le
      p (u₀ := u a) (z₀ := fun _ : intervalDomainPoint => uStar)
      (w := z) hs hd0 huaInt hzInt hM.le huaLiftBound hM.le hzLiftBound
      huaLiftClose x
    have hactual := intervalDomain_classical_bform_restart_pointwise
      hsol hm ha hT.le haTH hs (hsR.trans hRT) x
    have hwEq : w s x = u (a + s) x := by
      exact congrFun (intervalDomainRestartTrajectory_eq
        (a := a) (h := T) (u := u) ⟨hs.le, hsR.trans hRT⟩) x
    have hconst := intervalConjugateDuhamelMap_const_equilibrium p heq hs x
    rw [hwEq, hactual]
    calc
      |intervalConjugateDuhamelMap p (u a) w s x - uStar| =
          |intervalConjugateDuhamelMap p (u a) w s x -
              intervalConjugateDuhamelMap p
                (fun _ : intervalDomainPoint => uStar) z s x| := by rw [hconst]
      _ ≤ |intervalConjugateDuhamelMap p (u a) w s x -
              intervalConjugateDuhamelMap p (u a) z s x| +
            |intervalConjugateDuhamelMap p (u a) z s x -
              intervalConjugateDuhamelMap p
                (fun _ : intervalDomainPoint => uStar) z s x| := abs_sub_le _ _ _
      _ ≤ intervalDomainWeakSupContractionCoefficient p uStar CL R * d + d0 :=
        add_le_add hnonlin hdatum
  have hcoeff_mono : ∀ R, 0 ≤ R → R ≤ T →
      intervalDomainWeakSupContractionCoefficient p uStar CL R ≤ K := by
    intro R hR hRT
    have hsqrt : Real.sqrt R ≤ Real.sqrt T := Real.sqrt_le_sqrt hRT
    dsimp [K, intervalDomainWeakSupContractionCoefficient]
    have hchem :
        heatGradientLinftyLinftyConstant * (2 * Real.sqrt R) * CQ ≤
          heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * CQ := by
      have htwo : 2 * Real.sqrt R ≤ 2 * Real.sqrt T :=
        mul_le_mul_of_nonneg_left hsqrt (by norm_num)
      have hchem1 := mul_le_mul_of_nonneg_left htwo
        heatGradientLinftyLinftyConstant_nonneg
      exact mul_le_mul_of_nonneg_right hchem1 hCQ
    have hchem' := mul_le_mul_of_nonneg_left hchem (abs_nonneg p.χ₀)
    have hlog := mul_le_mul_of_nonneg_right hRT hCL.le
    linarith
  have himprove : ∀ R, 0 ≤ R → R ≤ T →
      (∀ s, 0 ≤ s → s ≤ R →
        intervalDomainRestartSupDistance a T uStar u s ≤ q) →
      ∀ s, 0 ≤ s → s ≤ R →
        intervalDomainRestartSupDistance a T uStar u s ≤ q / 2 := by
    intro R hR hRT hprefix s hs hsR
    by_cases hR0 : R = 0
    · have hs0 : s = 0 := by linarith
      subst s
      exact hsizeZero.trans (hd0q.trans (by linarith))
    have hRpos : 0 < R := lt_of_le_of_ne hR (Ne.symm hR0)
    by_cases hs0eq : s = 0
    · subst s
      exact hsizeZero.trans (hd0q.trans (by linarith))
    have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0eq)
    have hband : ∀ tau, 0 < tau → tau ≤ R → ∀ x,
        |w tau x - uStar| ≤ q := by
      intro tau htau htauR x
      have hpt := hsizePoint tau x.1 x.2
      rw [restartField_eq_physical ⟨htau.le, htauR.trans hRT⟩ x.2] at hpt
      have hwEq := congrFun (intervalDomainRestartTrajectory_eq
        (a := a) (h := T) (u := u) ⟨htau.le, htauR.trans hRT⟩) x
      change |intervalDomainRestartTrajectory a T u tau x - uStar| ≤ q
      rw [hwEq]
      simpa [intervalDomainLift, x.2] using
        hpt.trans (hprefix tau htau.le htauR)
    have hptBound := hmapBound R q hRpos hRT hq.le hband hband s hspos hsR
    have hcoef := hcoeff_mono R hR hRT
    have htarget :
        intervalDomainWeakSupContractionCoefficient p uStar CL R * q + d0 ≤
          q / 2 := by
      have hcoefq := mul_le_mul_of_nonneg_right hcoef hq.le
      nlinarith [hKquarter, hd0q]
    unfold intervalDomainRestartSupDistance
    apply csSup_le
    · exact ⟨|restartField a T u s 0 - uStar|, ⟨0, by norm_num, rfl⟩⟩
    · intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      change |restartField a T u s x - uStar| ≤ q / 2
      rw [restartField_eq_physical ⟨hspos.le, hsR.trans hRT⟩ hx]
      have hptBound' := (hptBound ⟨x, hx⟩).trans htarget
      change |intervalDomainRestartTrajectory a T u s ⟨x, hx⟩ - uStar| ≤
        q / 2 at hptBound'
      rw [intervalDomainRestartTrajectory_eq
        (a := a) (h := T) (u := u) ⟨hspos.le, hsR.trans hRT⟩] at hptBound'
      simpa [intervalDomainLift, hx] using
        hptBound'
  have hsizeHalf : ∀ s, 0 ≤ s → s ≤ T →
      intervalDomainRestartSupDistance a T uStar u s ≤ q / 2 :=
    ShenWork.PDE.continuousPrefixBootstrap hsizeCont hT.le hq
      (hsizeZero.trans (hd0q.trans (by linarith))) himprove
  let Dmax := sSup
    (intervalDomainRestartSupDistance a T uStar u '' Set.Icc (0 : ℝ) T)
  have hDmaxBdd : BddAbove
      (intervalDomainRestartSupDistance a T uStar u '' Set.Icc (0 : ℝ) T) :=
    isCompact_Icc.bddAbove_image hsizeCont.continuousOn
  have hDmaxNonempty :
      (intervalDomainRestartSupDistance a T uStar u '' Set.Icc (0 : ℝ) T).Nonempty :=
    ⟨intervalDomainRestartSupDistance a T uStar u 0,
      ⟨0, ⟨le_rfl, hT.le⟩, rfl⟩⟩
  have hsizeDmax : ∀ s, 0 ≤ s → s ≤ T →
      intervalDomainRestartSupDistance a T uStar u s ≤ Dmax := by
    intro s hs hsT
    exact le_csSup hDmaxBdd ⟨s, ⟨hs, hsT⟩, rfl⟩
  have hDmax0 : 0 ≤ Dmax := by
    have hzeroNonneg : 0 ≤ intervalDomainRestartSupDistance a T uStar u 0 :=
      intervalDomainRestartSupDistance_nonneg a T uStar u 0
        (((hfield.comp (continuous_const.prodMk continuous_id)).sub
          continuous_const).abs.continuousOn)
    exact hzeroNonneg.trans (hsizeDmax 0 le_rfl hT.le)
  have hglobalBand : ∀ tau, 0 < tau → tau ≤ T → ∀ x,
      |w tau x - uStar| ≤ q := by
    intro tau htau htauT x
    have hpt := hsizePoint tau x.1 x.2
    rw [restartField_eq_physical ⟨htau.le, htauT⟩ x.2] at hpt
    have hwEq := congrFun (intervalDomainRestartTrajectory_eq
      (a := a) (h := T) (u := u) ⟨htau.le, htauT⟩) x
    change |intervalDomainRestartTrajectory a T u tau x - uStar| ≤ q
    rw [hwEq]
    simpa [intervalDomainLift, x.2] using
      hpt.trans ((hsizeHalf tau htau.le htauT).trans (by linarith))
  have hglobalD : ∀ tau, 0 < tau → tau ≤ T → ∀ x,
      |w tau x - uStar| ≤ Dmax := by
    intro tau htau htauT x
    have hpt := hsizePoint tau x.1 x.2
    rw [restartField_eq_physical ⟨htau.le, htauT⟩ x.2] at hpt
    have hwEq := congrFun (intervalDomainRestartTrajectory_eq
      (a := a) (h := T) (u := u) ⟨htau.le, htauT⟩) x
    change |intervalDomainRestartTrajectory a T u tau x - uStar| ≤ Dmax
    rw [hwEq]
    simpa [intervalDomainLift, x.2] using
      hpt.trans (hsizeDmax tau htau.le htauT)
  have hrefinedPoint : ∀ s, 0 < s → s ≤ T → ∀ x,
      |w s x - uStar| ≤ K * Dmax + d0 := by
    intro s hs hsT x
    have h := hmapBound T Dmax hT le_rfl hDmax0
      hglobalBand hglobalD s hs hsT x
    simpa [K] using h
  have hDmaxIneq : Dmax ≤ K * Dmax + d0 := by
    apply csSup_le hDmaxNonempty
    intro y hy
    rcases hy with ⟨s, hs, rfl⟩
    by_cases hs0 : s = 0
    · subst s
      exact hsizeZero.trans (by nlinarith [hK, hDmax0])
    have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
    unfold intervalDomainRestartSupDistance
    apply csSup_le
    · exact ⟨|restartField a T u s 0 - uStar|, ⟨0, by norm_num, rfl⟩⟩
    · intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      change |restartField a T u s x - uStar| ≤ K * Dmax + d0
      rw [restartField_eq_physical ⟨hspos.le, hs.2⟩ hx]
      have hrefined := hrefinedPoint s hspos hs.2 ⟨x, hx⟩
      change |intervalDomainRestartTrajectory a T u s ⟨x, hx⟩ - uStar| ≤
        K * Dmax + d0 at hrefined
      rw [intervalDomainRestartTrajectory_eq
        (a := a) (h := T) (u := u) ⟨hspos.le, hs.2⟩] at hrefined
      simpa [intervalDomainLift, hx] using
        hrefined
  have hDmaxLe : Dmax ≤ 2 * d0 := by
    nlinarith [hKquarter, hDmax0]
  have hcloseWindow : ∀ r, 0 ≤ r → r ≤ T → ∀ x,
      |w r x - uStar| ≤ 4 * delta := by
    intro r hr hrT x
    by_cases hrzero : r = 0
    · subst r
      have hw0 : w 0 x = u a x := by
        change intervalDomainRestartTrajectory a T u 0 x = u a x
        simpa using congrFun (intervalDomainRestartTrajectory_eq
          (a := a) (h := T) (u := u) ⟨le_rfl, hT.le⟩) x
      rw [hw0]
      exact (huaClose x).trans (by dsimp [d0]; linarith [hdelta])
    · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hrzero)
      have hd0eq : 2 * d0 = 4 * delta := by dsimp [d0]; ring
      exact (hglobalD r hrpos hrT x).trans (by rw [← hd0eq]; exact hDmaxLe)
  let D : ShenWork.IntervalConjugatePicard.ConjugateMildSolutionData p (u a) :=
    { T := T
      hT := hT
      M := M
      hM := hM
      u := w
      hmild := by
        intro r hr hrT x
        have hpoint := intervalDomain_classical_bform_restart_pointwise
          hsol hm ha hT.le haTH hr hrT x
        have hwEq : w r x = u (a + r) x :=
          congrFun (intervalDomainRestartTrajectory_eq
            (a := a) (h := T) (u := u) ⟨hr.le, hrT⟩) x
        rw [hwEq]
        exact hpoint
      hbound := by
        intro r hr hrT x
        have hb := abs_le.mp (hglobalBand r hr hrT x)
        have hx0 : 0 ≤ w r x := by
          dsimp [q] at hb
          linarith
        rw [abs_of_nonneg hx0]
        dsimp [q, M, intervalDomainWeakSupConeCeiling] at hb ⊢
        linarith
      hnonneg := by
        intro r hr hrT x
        have hb := abs_le.mp (hglobalBand r hr hrT x)
        dsimp [q] at hb
        linarith
      hpos := by
        intro r hr hrT x
        have hb := abs_le.mp (hglobalBand r hr hrT x)
        dsimp [q] at hb
        linarith
      hcont := hwcontT
      hmeas := hwmeas }
  exact ⟨{
    a := a
    a_pos := ha
    a_le_quarter := haQuarter
    a_lt_half := haHalf
    mild := D
    mild_T := rfl
    mild_M := rfl
    mild_u := rfl
    close := by simpa [D] using hcloseWindow
  }⟩

/-- Global-orbit wrapper around the finite-horizon weak restart theorem. -/
theorem intervalDomainWeakSupRestartWindowData_of_contraction
    (p : CM2Params) {uStar vStar T CL delta : ℝ}
    (hm : p.m = 1)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hT : 0 < T) (hCL : 0 < CL)
    (hCLlip : ∀ r s : ℝ,
      |r| ≤ intervalDomainWeakSupConeCeiling uStar →
      |s| ≤ intervalDomainWeakSupConeCeiling uStar →
      |r * (p.a - p.b * r ^ p.α) -
        s * (p.a - p.b * s ^ p.α)| ≤ CL * |r - s|)
    (hcontract :
      intervalDomainWeakSupContractionCoefficient p uStar CL T < 1 / 4)
    (hdelta : 0 < delta) (hdeltaStar : delta ≤ uStar / 16)
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hclose : SupCloseToConstant intervalDomain u₀ uStar delta)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain p u v)
    (htrace : InitialTrace intervalDomain u₀ u) :
    Nonempty (IntervalDomainWeakSupRestartWindowData
      p uStar T delta u) := by
  let H : ℝ := 2 * T + 1
  have hH : 0 < H := by dsimp [H]; linarith
  have hHT : 5 * T / 4 < H := by dsimp [H]; linarith
  exact intervalDomainWeakSupRestartWindowData_of_contraction_of_solution
    p hm heq hT hCL hCLlip hcontract hdelta hdeltaStar hu₀ hclose
      (hglobal H hH) hHT htrace

/-- Uniform weak-sup restart window, with the contraction time chosen only
from the equation and the equilibrium. -/
theorem exists_intervalDomainWeakSupRestartWindow
    (p : CM2Params) {uStar vStar : ℝ}
    (hm : p.m = 1)
    (heq : Paper3ConstantEquilibrium p uStar vStar) :
    ∃ T > 0, ∀ delta, 0 < delta → delta ≤ uStar / 16 →
      ∀ u₀ : intervalDomainPoint → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
        SupCloseToConstant intervalDomain u₀ uStar delta →
        ∀ u v : ℝ → intervalDomainPoint → ℝ,
          IsPaper2GlobalClassicalSolution intervalDomain p u v →
          InitialTrace intervalDomain u₀ u →
          Nonempty (IntervalDomainWeakSupRestartWindowData
            p uStar T delta u) := by
  obtain ⟨T, hT, CL, hCL, hCLlip, hcontract⟩ :=
    exists_intervalDomainWeakSupContractionWindow p heq.u_pos
  refine ⟨T, hT, ?_⟩
  intro delta hdelta hdeltaStar u₀ hu₀ hclose u v hglobal htrace
  exact intervalDomainWeakSupRestartWindowData_of_contraction
    p hm heq hT hCL hCLlip hcontract hdelta hdeltaStar
      hu₀ hclose hglobal htrace

#print axioms exists_intervalDomainWeakSupContractionWindow
#print axioms intervalDomainRestartSupDistance_continuous
#print axioms chemFluxLifted_const_eq_zero
#print axioms intervalConjugateDuhamelMap_const_equilibrium
#print axioms intervalConjugateDuhamelMap_initialDatum_diff_le
#print axioms IntervalDomainWeakSupRestartWindowData.target
#print axioms
  intervalDomainWeakSupRestartWindowData_of_contraction_of_solution
#print axioms intervalDomainWeakSupRestartWindowData_of_contraction
#print axioms exists_intervalDomainWeakSupRestartWindow

end

end ShenWork.Paper3
