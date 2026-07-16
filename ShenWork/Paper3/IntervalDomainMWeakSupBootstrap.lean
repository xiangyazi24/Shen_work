/- Faithful general-`m` weak-sup bootstrap around a positive equilibrium. -/
import ShenWork.Paper3.IntervalDomainWeakSupBootstrap
import ShenWork.Paper3.IntervalDomainConstantEquilibriumWitness
import ShenWork.Paper2.IntervalDomainMClassicalInitialOverlap
import ShenWork.Paper2.IntervalDomainMConjugatePicardFloorInhabit

namespace ShenWork.Paper3

open MeasureTheory Set Filter Topology
open scoped Topology Interval
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.Paper2.IntervalDomainMConjugateMapBounds
open ShenWork.Paper2.IntervalDomainMConjugatePicardFloorInhabit
open ShenWork.IntervalPositiveFloorNonlinearLipschitz
  (powerLip powerLip_nonneg logisticReaction_lipschitz_on_pos_Icc)
open ShenWork.HeatKernelGradientEstimates
  (heatGradientLinftyLinftyConstant heatGradientLinftyLinftyConstant_nonneg)
open ShenWork.PDE

noncomputable section

local instance intervalDomainMWeakSupBootstrapTopologicalSpace :
    TopologicalSpace intervalDomain.Point :=
  inferInstanceAs (TopologicalSpace intervalDomainPoint)

/-- Fixed lower edge of the faithful general-`m` weak positive tube. -/
def intervalDomainMWeakSupConeFloor (uStar : ℝ) : ℝ := uStar / 2

/-- Fixed upper edge of the faithful general-`m` weak positive tube. -/
def intervalDomainMWeakSupConeCeiling (uStar : ℝ) : ℝ := 3 * uStar / 2

/-- The genuine general-`m` flux Lipschitz constant on the fixed tube. -/
def intervalDomainMWeakSupChemLipschitzConstant
    (p : CM2Params) (uStar : ℝ) : ℝ :=
  chemFluxMLipschitzConstant p
    (intervalDomainMWeakSupConeFloor uStar)
    (intervalDomainMWeakSupConeCeiling uStar)

/-- Short-window contraction coefficient for the faithful general-`m` B-form. -/
def intervalDomainMWeakSupContractionCoefficient
    (p : CM2Params) (uStar CL T : ℝ) : ℝ :=
  |p.χ₀| *
      (heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) *
        intervalDomainMWeakSupChemLipschitzConstant p uStar) +
    T * CL

theorem intervalDomainMWeakSupConeFloor_pos
    {uStar : ℝ} (huStar : 0 < uStar) :
    0 < intervalDomainMWeakSupConeFloor uStar := by
  simp [intervalDomainMWeakSupConeFloor]
  linarith

theorem intervalDomainMWeakSupConeFloor_le_ceiling
    {uStar : ℝ} (huStar : 0 < uStar) :
    intervalDomainMWeakSupConeFloor uStar ≤
      intervalDomainMWeakSupConeCeiling uStar := by
  simp [intervalDomainMWeakSupConeFloor,
    intervalDomainMWeakSupConeCeiling]
  linarith

theorem intervalDomainMWeakSupChemLipschitzConstant_nonneg
    (p : CM2Params) {uStar : ℝ} (huStar : 0 < uStar) :
    0 ≤ intervalDomainMWeakSupChemLipschitzConstant p uStar := by
  exact chemFluxMLipschitzConstant_nonneg p
    (intervalDomainMWeakSupConeFloor_pos huStar)
    (intervalDomainMWeakSupConeFloor_le_ceiling huStar)

/-- The faithful fixed-tube contraction coefficient is monotone in time. -/
theorem intervalDomainMWeakSupContractionCoefficient_mono
    (p : CM2Params) {uStar CL T S : ℝ}
    (huStar : 0 < uStar) (hCL : 0 ≤ CL) (hTS : T ≤ S) :
    intervalDomainMWeakSupContractionCoefficient p uStar CL T ≤
      intervalDomainMWeakSupContractionCoefficient p uStar CL S := by
  have hCQ : 0 ≤ intervalDomainMWeakSupChemLipschitzConstant p uStar :=
    intervalDomainMWeakSupChemLipschitzConstant_nonneg p huStar
  have hsqrt : Real.sqrt T ≤ Real.sqrt S := Real.sqrt_le_sqrt hTS
  unfold intervalDomainMWeakSupContractionCoefficient
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply mul_le_mul_of_nonneg_right _ hCQ
    apply mul_le_mul_of_nonneg_left _ heatGradientLinftyLinftyConstant_nonneg
    exact mul_le_mul_of_nonneg_left hsqrt (by norm_num)
  · exact mul_le_mul_of_nonneg_right hTS hCL

/-- A datum-independent faithful contraction window. -/
theorem exists_intervalDomainMWeakSupContractionWindow
    (p : CM2Params) {uStar : ℝ} (huStar : 0 < uStar) :
    ∃ T > 0, ∃ CL > 0,
      (∀ r s : ℝ,
        |r| ≤ intervalDomainMWeakSupConeCeiling uStar →
        |s| ≤ intervalDomainMWeakSupConeCeiling uStar →
        |r * (p.a - p.b * r ^ p.α) -
          s * (p.a - p.b * s ^ p.α)| ≤ CL * |r - s|) ∧
      intervalDomainMWeakSupContractionCoefficient p uStar CL T < 1 / 4 := by
  let CQ := intervalDomainMWeakSupChemLipschitzConstant p uStar
  have hM : 0 < intervalDomainMWeakSupConeCeiling uStar := by
    dsimp [intervalDomainMWeakSupConeCeiling]
    linarith
  obtain ⟨CL, hCL, hCLlip⟩ :=
    ShenWork.IntervalDomainExistence.intervalLogisticSource_lipschitz p hM
  let A := |p.χ₀| * heatGradientLinftyLinftyConstant * 2 * CQ
  have hCQ : 0 ≤ CQ := by
    simpa [CQ] using
      intervalDomainMWeakSupChemLipschitzConstant_nonneg p huStar
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
  have heq : intervalDomainMWeakSupContractionCoefficient p uStar CL T =
      A * Real.sqrt T + CL * T := by
    dsimp [intervalDomainMWeakSupContractionCoefficient, A, CQ]
    ring
  rw [heq]
  simpa [mul_comm] using hsmall

/-- The faithful contraction window may be placed below any positive horizon. -/
theorem exists_intervalDomainMWeakSupContractionWindow_lt
    (p : CM2Params) {uStar H : ℝ} (huStar : 0 < uStar) (hH : 0 < H) :
    ∃ T > 0, T < H ∧ ∃ CL > 0,
      (∀ r s : ℝ,
        |r| ≤ intervalDomainMWeakSupConeCeiling uStar →
        |s| ≤ intervalDomainMWeakSupConeCeiling uStar →
        |r * (p.a - p.b * r ^ p.α) -
          s * (p.a - p.b * s ^ p.α)| ≤ CL * |r - s|) ∧
      intervalDomainMWeakSupContractionCoefficient p uStar CL T < 1 / 4 := by
  obtain ⟨S, hS, CL, hCL, hCLlip, hcontract⟩ :=
    exists_intervalDomainMWeakSupContractionWindow p huStar
  let T := min S (H / 2)
  have hT : 0 < T := by
    dsimp [T]
    exact lt_min hS (by linarith)
  have hTS : T ≤ S := by dsimp [T]; exact min_le_left _ _
  have hTH : T < H := by
    have : T ≤ H / 2 := by dsimp [T]; exact min_le_right _ _
    linarith
  refine ⟨T, hT, hTH, CL, hCL, hCLlip, ?_⟩
  exact lt_of_le_of_lt
    (intervalDomainMWeakSupContractionCoefficient_mono
      p huStar hCL.le hTS) hcontract

/-! ## The constant equilibrium is a faithful general-`m` solution -/

private theorem const_chemoM_interior
    (p : CM2Params) (cu cv : ℝ)
    {x : intervalDomainPoint} (hx : x.1 ∈ Set.Ioo (0 : ℝ) 1) :
    intervalDomainChemotaxisDivM p (fun _ => cu) (fun _ => cv) x = 0 := by
  unfold intervalDomainChemotaxisDivM
  have hloc : (fun y : ℝ =>
      (intervalDomainLift (fun _ : intervalDomainPoint => cu) y) ^ p.m *
        deriv (intervalDomainLift (fun _ : intervalDomainPoint => cv)) y /
        (1 + intervalDomainLift (fun _ : intervalDomainPoint => cv) y) ^ p.β)
      =ᶠ[𝓝 x.1] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    rw [lift_const_deriv_interior cv hy]
    ring
  rw [hloc.deriv_eq]
  simp

/-- A spatially homogeneous Paper-3 equilibrium is a faithful general-`m`
classical solution on every positive finite horizon. -/
theorem intervalDomainM_const_equilibrium_classical
    (p : CM2Params) {uStar vStar T : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar) (hT : 0 < T) :
    IsPaper2ClassicalSolution intervalDomainM p T
      (fun (_ : ℝ) (_ : intervalDomainPoint) => uStar)
      (fun (_ : ℝ) (_ : intervalDomainPoint) => vStar) := by
  refine IsPaper2ClassicalSolution.of_components hT
    (const_classicalRegularity _ _ T) ?_ ?_ ?_ ?_ ?_
  · intro t x _ _
    exact heq.u_pos
  · intro t x _ _
    exact heq.v_nonneg
  · intro t x _ _ hx
    have hxi : x.1 ∈ Set.Ioo (0 : ℝ) 1 := hx
    change deriv (fun _ : ℝ => uStar) t =
      intervalDomainLaplacian (fun _ => uStar) x -
        p.χ₀ * intervalDomainChemotaxisDivM p
          (fun _ => uStar) (fun _ => vStar) x +
        uStar * (p.a - p.b * uStar ^ p.α)
    rw [const_lap_interior uStar hxi,
      const_chemoM_interior p uStar vStar hxi,
      heq.reaction_eq_zero]
    simp
  · intro t x _ _ hx
    have hxi : x.1 ∈ Set.Ioo (0 : ℝ) 1 := hx
    change (0 : ℝ) =
      intervalDomainLaplacian (fun _ => vStar) x -
        p.μ * vStar + p.ν * uStar ^ p.γ
    rw [const_lap_interior vStar hxi]
    linarith [heq.elliptic_relation]
  · intro t x _ _ hx
    have hxb : x.1 = 0 ∨ x.1 = 1 := hx
    exact ⟨intervalDomainNormalDeriv_const_endpoint_zero _ hxb,
      intervalDomainNormalDeriv_const_endpoint_zero _ hxb⟩

/-- The same constant equilibrium is a faithful global classical solution. -/
theorem intervalDomainM_const_equilibrium_global
    (p : CM2Params) {uStar vStar : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar) :
    IsPaper2GlobalClassicalSolution intervalDomainM p
      (fun (_ : ℝ) (_ : intervalDomainPoint) => uStar)
      (fun (_ : ℝ) (_ : intervalDomainPoint) => vStar) := by
  intro T hT
  exact intervalDomainM_const_equilibrium_classical p heq hT

/-! ## Faithful weak-sup restart windows -/

/-- A fixed positive restart window for a faithful general-`m` orbit. -/
structure IntervalDomainMWeakSupRestartWindowData
    (p : CM2Params) (uStar T delta : ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) where
  a : ℝ
  a_pos : 0 < a
  a_le_quarter : a ≤ T / 4
  a_lt_half : a < T / 2
  mild : ConjugateMildSolutionDataM p (u a)
  mild_T : mild.T = T
  mild_M : mild.M = intervalDomainMWeakSupConeCeiling uStar
  mild_c : mild.c = intervalDomainMWeakSupConeFloor uStar
  mild_u : mild.u = classicalRestartTrajectoryM a T u
  close : ∀ r, 0 ≤ r → r ≤ T → ∀ x : intervalDomainPoint,
    |mild.u r x - uStar| ≤ 4 * delta

/-- The target absolute time lies in the last half of the faithful restart
window and is represented exactly by its mild trajectory. -/
theorem IntervalDomainMWeakSupRestartWindowData.target
    {p : CM2Params} {uStar T delta : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (D : IntervalDomainMWeakSupRestartWindowData p uStar T delta u) :
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
  · rw [D.mild_u, classicalRestartTrajectoryM_eq hrmem]
    congr 1
    ring

/-- Faithful general-`m` first-exit closure on a fixed contraction window
strictly inside a finite classical horizon. -/
theorem intervalDomainMWeakSupRestartWindowData_of_contraction_of_solution
    (p : CM2Params) {uStar vStar T CL delta H : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hT : 0 < T) (hCL : 0 < CL)
    (hCLlip : ∀ r s : ℝ,
      |r| ≤ intervalDomainMWeakSupConeCeiling uStar →
      |s| ≤ intervalDomainMWeakSupConeCeiling uStar →
      |r * (p.a - p.b * r ^ p.α) -
        s * (p.a - p.b * s ^ p.α)| ≤ CL * |r - s|)
    (hcontract :
      intervalDomainMWeakSupContractionCoefficient p uStar CL T < 1 / 4)
    (hdelta : 0 < delta) (hdeltaStar : delta ≤ uStar / 16)
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hclose : SupCloseToConstant intervalDomainM u₀ uStar delta)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p H u v)
    (hHT : 5 * T / 4 < H)
    (htrace : InitialTrace intervalDomainM u₀ u) :
    Nonempty (IntervalDomainMWeakSupRestartWindowData
      p uStar T delta u) := by
  classical
  let c := intervalDomainMWeakSupConeFloor uStar
  let M := intervalDomainMWeakSupConeCeiling uStar
  let q := uStar / 2
  let K := intervalDomainMWeakSupContractionCoefficient p uStar CL T
  let d0 := 2 * delta
  let uc : ℝ → intervalDomainPoint → ℝ := fun _ _ => uStar
  let vc : ℝ → intervalDomainPoint → ℝ := fun _ _ => vStar
  have huStar : 0 < uStar := heq.u_pos
  have hc : 0 < c := by
    simpa [c] using intervalDomainMWeakSupConeFloor_pos huStar
  have hcM : c ≤ M := by
    simpa [c, M] using intervalDomainMWeakSupConeFloor_le_ceiling huStar
  have hM : 0 < M := hc.trans_le hcM
  have hq : 0 < q := by dsimp [q]; linarith
  have hK : 0 ≤ K := by
    dsimp [K, intervalDomainMWeakSupContractionCoefficient]
    exact add_nonneg
      (mul_nonneg (abs_nonneg _)
        (mul_nonneg
          (mul_nonneg heatGradientLinftyLinftyConstant_nonneg
            (mul_nonneg (by norm_num) (Real.sqrt_nonneg T)))
          (intervalDomainMWeakSupChemLipschitzConstant_nonneg p huStar)))
      (mul_nonneg hT.le hCL.le)
  have hKquarter : K < 1 / 4 := by simpa [K] using hcontract
  have hd0 : 0 ≤ d0 := by dsimp [d0]; linarith
  have hd0q : d0 ≤ q / 4 := by
    dsimp [d0, q]
    linarith
  have hd0Star : d0 ≤ uStar / 8 := by
    dsimp [d0]
    linarith
  have hu₀Bdd : BddAbove
      (Set.range (fun x : intervalDomainPoint => |u₀ x|)) := by
    simpa [intervalDomainM] using hu₀.admissible.1
  obtain ⟨eta, heta, htraceEta⟩ :=
    intervalDomainM_initialTrace_pointwise_abs_lt_of_classical
      hsol htrace hu₀Bdd hdelta
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
  have hconstSol : IsPaper2ClassicalSolution intervalDomainM p H uc vc := by
    simpa [uc, vc] using intervalDomainM_const_equilibrium_classical p heq
      (lt_trans (by linarith [hT]) hHT)
  let w : ℝ → intervalDomainPoint → ℝ :=
    classicalRestartTrajectoryM a T u
  have hwcontT : ShenWork.IntervalMildPicard.HasContinuousSlices T w := by
    simpa [w] using classicalRestartTrajectoryM_hasContinuousSlices
      hsol ha hT.le haTH
  have hwmeas : ShenWork.IntervalMildPicard.HasJointMeasurability w := by
    simpa [w] using classicalRestartTrajectoryM_hasJointMeasurability
      hsol ha hT.le haTH
  have hfield := restartField_continuous hsol ha hT.le haTH u (Or.inl rfl)
  have hsizeCont : Continuous (intervalDomainRestartSupDistance a T uStar u) :=
    intervalDomainRestartSupDistance_continuous hsol ha hT.le haTH
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
    bddAbove_range_abs_diff_of_bddAbove hu₀Bdd hu₀ConstBdd
  have hu₀Close : ∀ x : intervalDomainPoint, |u₀ x - uStar| < delta := by
    intro x
    have hsup : intervalDomainSupNorm (fun y => u₀ y - uStar) < delta := by
      simpa [SupCloseToConstant, intervalDomainM] using hclose
    exact (le_csSup hu₀DiffBdd ⟨x, rfl⟩).trans_lt hsup
  have huaTrace : ∀ x : intervalDomainPoint, |u a x - u₀ x| < delta :=
    htraceEta a ha haEta
  have huaClose : ∀ x : intervalDomainPoint, |u a x - uStar| ≤ d0 := by
    intro x
    dsimp [d0]
    calc
      |u a x - uStar| = |(u a x - u₀ x) + (u₀ x - uStar)| := by ring_nf
      _ ≤ |u a x - u₀ x| + |u₀ x - uStar| := abs_add_le _ _
      _ ≤ 2 * delta := by linarith [huaTrace x, hu₀Close x]
  have hsizeZero : intervalDomainRestartSupDistance a T uStar u 0 ≤ d0 := by
    unfold intervalDomainRestartSupDistance
    apply csSup_le
    · exact ⟨|restartField a T u 0 0 - uStar|,
        ⟨0, (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1), rfl⟩⟩
    · intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      change |restartField a T u 0 x - uStar| ≤ d0
      rw [restartField_eq_physical (by constructor <;> linarith [hT]) hx]
      simpa [intervalDomainLift, hx] using huaClose ⟨x, hx⟩
  have hdiffOnPrefix : ∀ R, 0 < R → R ≤ T →
      (∀ s, 0 ≤ s → s ≤ R →
        intervalDomainRestartSupDistance a T uStar u s ≤ q) →
      ∀ s, 0 ≤ s → s ≤ R → ∀ x : intervalDomainPoint,
        |u (a + s) x - uStar| ≤
          d0 / (1 - intervalDomainMWeakSupContractionCoefficient
            p uStar CL R) := by
    intro R hR hRT hprefix
    let KR := intervalDomainMWeakSupContractionCoefficient p uStar CL R
    have haRH : a + R < H := by linarith [hRT, haTH]
    have htargetDist : ∀ s, 0 < s → s ≤ R → ∀ x : intervalDomainPoint,
        |u (a + s) x - uStar| ≤ q := by
      intro s hs hsR x
      have hp := hsizePoint s x.1 x.2
      rw [restartField_eq_physical ⟨hs.le, hsR.trans hRT⟩ x.2] at hp
      simpa [intervalDomainLift, x.2] using
        hp.trans (hprefix s hs.le hsR)
    have hub : ∀ s, 0 < s → s ≤ R → ∀ x,
        |classicalRestartTrajectoryM a R u s x| ≤ M := by
      intro s hs hsR x
      rw [classicalRestartTrajectoryM_eq ⟨hs.le, hsR⟩]
      calc
        |u (a + s) x| = |(u (a + s) x - uStar) + uStar| := by ring_nf
        _ ≤ |u (a + s) x - uStar| + |uStar| := abs_add_le _ _
        _ ≤ q + uStar := by
          rw [abs_of_pos huStar]
          exact add_le_add (htargetDist s hs hsR x) le_rfl
        _ = M := by
          dsimp [q, M, intervalDomainMWeakSupConeCeiling]
          ring
    have huf : ∀ s, 0 < s → s ≤ R → ∀ x,
        c ≤ classicalRestartTrajectoryM a R u s x := by
      intro s hs hsR x
      rw [classicalRestartTrajectoryM_eq ⟨hs.le, hsR⟩]
      have hd := abs_le.mp (htargetDist s hs hsR x)
      dsimp [q, c, intervalDomainMWeakSupConeFloor] at hd ⊢
      linarith
    have hcb : ∀ s, 0 < s → s ≤ R → ∀ x,
        |classicalRestartTrajectoryM a R uc s x| ≤ M := by
      intro s hs hsR x
      simp [uc, classicalRestartTrajectoryM, abs_of_pos huStar]
      dsimp [M, intervalDomainMWeakSupConeCeiling]
      linarith
    have hcf : ∀ s, 0 < s → s ≤ R → ∀ x,
        c ≤ classicalRestartTrajectoryM a R uc s x := by
      intro s hs hsR x
      simp [uc, classicalRestartTrajectoryM]
      dsimp [c, intervalDomainMWeakSupConeFloor]
      linarith
    have hKRle : KR ≤ K := by
      exact intervalDomainMWeakSupContractionCoefficient_mono
        p huStar hCL.le hRT
    have hKRlt : KR < 1 := lt_of_le_of_lt hKRle
      (lt_trans hKquarter (by norm_num))
    have hrestart := intervalDomainM_classical_restart_diff_bound
      (hsol₁ := hsol) (hsol₂ := hconstSol)
      ha hR haRH haRH hc hcM hCL.le hCLlip
      hub huf hcb hcf hd0 huaClose
      (by
        simpa [KR, intervalDomainMWeakSupContractionCoefficient,
          intervalDomainMWeakSupChemLipschitzConstant, c, M] using hKRlt)
    intro s hs hsR x
    have h := hrestart s hs hsR x
    simpa [uc, KR, intervalDomainMWeakSupContractionCoefficient,
      intervalDomainMWeakSupChemLipschitzConstant, c, M] using h
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
    let KR := intervalDomainMWeakSupContractionCoefficient p uStar CL R
    have hKRle : KR ≤ K :=
      intervalDomainMWeakSupContractionCoefficient_mono
        p huStar hCL.le hRT
    have hKRquarter : KR < 1 / 4 := hKRle.trans_lt hKquarter
    have hden : 0 < 1 - KR := by linarith
    have hquot : d0 / (1 - KR) ≤ q / 2 := by
      rw [div_le_iff₀ hden]
      nlinarith [hd0q, hq]
    have hdiff := hdiffOnPrefix R hRpos hRT hprefix s hs hsR
    unfold intervalDomainRestartSupDistance
    apply csSup_le
    · exact ⟨|restartField a T u s 0 - uStar|, ⟨0, by norm_num, rfl⟩⟩
    · intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      change |restartField a T u s x - uStar| ≤ q / 2
      rw [restartField_eq_physical ⟨hs, hsR.trans hRT⟩ hx]
      have hb := (hdiff ⟨x, hx⟩).trans hquot
      simpa [intervalDomainLift, hx, KR] using hb
  have hsizeHalf : ∀ s, 0 ≤ s → s ≤ T →
      intervalDomainRestartSupDistance a T uStar u s ≤ q / 2 :=
    ShenWork.PDE.continuousPrefixBootstrap hsizeCont hT.le hq
      (hsizeZero.trans (hd0q.trans (by linarith))) himprove
  have hprefixFull : ∀ s, 0 ≤ s → s ≤ T →
      intervalDomainRestartSupDistance a T uStar u s ≤ q := by
    intro s hs hsT
    exact (hsizeHalf s hs hsT).trans (by linarith [hq])
  have hdiffFull := hdiffOnPrefix T hT le_rfl hprefixFull
  have hdenK : 0 < 1 - K := by linarith [hKquarter]
  have hquot4 : d0 / (1 - K) ≤ 4 * delta := by
    rw [div_le_iff₀ hdenK]
    dsimp [d0]
    nlinarith [hKquarter, hdelta]
  have hcloseWindow : ∀ r, 0 ≤ r → r ≤ T → ∀ x,
      |w r x - uStar| ≤ 4 * delta := by
    intro r hr hrT x
    rw [show w r = u (a + r) from by
      exact classicalRestartTrajectoryM_eq ⟨hr, hrT⟩]
    exact (hdiffFull r hr hrT x).trans (by simpa [K] using hquot4)
  have hweakBand : ∀ r, 0 ≤ r → r ≤ T → ∀ x,
      |w r x - uStar| ≤ q / 2 := by
    intro r hr hrT x
    have hp := hsizePoint r x.1 x.2
    rw [restartField_eq_physical ⟨hr, hrT⟩ x.2] at hp
    change |classicalRestartTrajectoryM a T u r x - uStar| ≤ q / 2
    rw [classicalRestartTrajectoryM_eq ⟨hr, hrT⟩]
    simpa [intervalDomainLift, x.2] using
      hp.trans (hsizeHalf r hr hrT)
  let D : ConjugateMildSolutionDataM p (u a) :=
    { T := T
      hT := hT
      M := M
      hM := hM
      c := c
      hc := hc
      u := w
      hmild := by
        intro r hr hrT x
        have hpoint := intervalDomainM_classical_bform_restart_pointwise
          hsol ha hT.le haTH hr hrT x
        have hw : w r x = u (a + r) x := by
          simpa [w] using congrFun (classicalRestartTrajectoryM_eq
            (a := a) (h := T) (u := u) ⟨hr.le, hrT⟩) x
        rw [hw]
        exact hpoint
      hbound := by
        intro r hr hrT x
        calc
          |w r x| = |(w r x - uStar) + uStar| := by ring_nf
          _ ≤ |w r x - uStar| + |uStar| := abs_add_le _ _
          _ ≤ q / 2 + uStar := by
            rw [abs_of_pos huStar]
            exact add_le_add (hweakBand r hr.le hrT x) le_rfl
          _ ≤ M := by
            dsimp [q, M, intervalDomainMWeakSupConeCeiling]
            linarith
      hfloor := by
        intro r hr hrT x
        have hb := abs_le.mp (hweakBand r hr.le hrT x)
        dsimp [q, c, intervalDomainMWeakSupConeFloor] at hb ⊢
        linarith
      hcont := hwcontT
      hmeas := hwmeas
      datum_bound := by
        intro x
        calc
          |u a x| = |(u a x - uStar) + uStar| := by ring_nf
          _ ≤ |u a x - uStar| + |uStar| := abs_add_le _ _
          _ ≤ d0 + uStar := by
            rw [abs_of_pos huStar]
            exact add_le_add (huaClose x) le_rfl
          _ ≤ M := by
            dsimp [M, intervalDomainMWeakSupConeCeiling]
            linarith [hd0Star] }
  exact ⟨{
    a := a
    a_pos := ha
    a_le_quarter := haQuarter
    a_lt_half := haHalf
    mild := D
    mild_T := rfl
    mild_M := rfl
    mild_c := rfl
    mild_u := rfl
    close := by simpa [D] using hcloseWindow
  }⟩

/-- Global faithful-orbit wrapper around the finite-horizon theorem. -/
theorem intervalDomainMWeakSupRestartWindowData_of_contraction
    (p : CM2Params) {uStar vStar T CL delta : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hT : 0 < T) (hCL : 0 < CL)
    (hCLlip : ∀ r s : ℝ,
      |r| ≤ intervalDomainMWeakSupConeCeiling uStar →
      |s| ≤ intervalDomainMWeakSupConeCeiling uStar →
      |r * (p.a - p.b * r ^ p.α) -
        s * (p.a - p.b * s ^ p.α)| ≤ CL * |r - s|)
    (hcontract :
      intervalDomainMWeakSupContractionCoefficient p uStar CL T < 1 / 4)
    (hdelta : 0 < delta) (hdeltaStar : delta ≤ uStar / 16)
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hclose : SupCloseToConstant intervalDomainM u₀ uStar delta)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomainM p u v)
    (htrace : InitialTrace intervalDomainM u₀ u) :
    Nonempty (IntervalDomainMWeakSupRestartWindowData
      p uStar T delta u) := by
  let H : ℝ := 2 * T + 1
  have hH : 0 < H := by dsimp [H]; linarith
  have hHT : 5 * T / 4 < H := by dsimp [H]; linarith
  exact intervalDomainMWeakSupRestartWindowData_of_contraction_of_solution
    p heq hT hCL hCLlip hcontract hdelta hdeltaStar hu₀ hclose
      (hglobal H hH) hHT htrace

/-- Uniform faithful general-`m` weak-sup restart window, with lifespan chosen
only from the equation and the equilibrium. -/
theorem exists_intervalDomainMWeakSupRestartWindow
    (p : CM2Params) {uStar vStar : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar) :
    ∃ T > 0, ∀ delta, 0 < delta → delta ≤ uStar / 16 →
      ∀ u₀ : intervalDomainPoint → ℝ,
        PositiveInitialDatum intervalDomainM u₀ →
        SupCloseToConstant intervalDomainM u₀ uStar delta →
        ∀ u v : ℝ → intervalDomainPoint → ℝ,
          IsPaper2GlobalClassicalSolution intervalDomainM p u v →
          InitialTrace intervalDomainM u₀ u →
          Nonempty (IntervalDomainMWeakSupRestartWindowData
            p uStar T delta u) := by
  obtain ⟨T, hT, CL, hCL, hCLlip, hcontract⟩ :=
    exists_intervalDomainMWeakSupContractionWindow p heq.u_pos
  refine ⟨T, hT, ?_⟩
  intro delta hdelta hdeltaStar u₀ hu₀ hclose u v hglobal htrace
  exact intervalDomainMWeakSupRestartWindowData_of_contraction
    p heq hT hCL hCLlip hcontract hdelta hdeltaStar
      hu₀ hclose hglobal htrace

#print axioms intervalDomainMWeakSupConeFloor_pos
#print axioms intervalDomainMWeakSupConeFloor_le_ceiling
#print axioms intervalDomainMWeakSupChemLipschitzConstant_nonneg
#print axioms intervalDomainMWeakSupContractionCoefficient_mono
#print axioms exists_intervalDomainMWeakSupContractionWindow
#print axioms exists_intervalDomainMWeakSupContractionWindow_lt
#print axioms intervalDomainM_const_equilibrium_classical
#print axioms intervalDomainM_const_equilibrium_global
#print axioms IntervalDomainMWeakSupRestartWindowData.target
#print axioms
  intervalDomainMWeakSupRestartWindowData_of_contraction_of_solution
#print axioms intervalDomainMWeakSupRestartWindowData_of_contraction
#print axioms exists_intervalDomainMWeakSupRestartWindow

end

end ShenWork.Paper3
