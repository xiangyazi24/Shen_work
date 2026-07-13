/-
  Genuine whole-line fixed-source construction for one Paper-1 Rothe step.

  This combines the compact-open local source Schauder theorem with the
  tail-free clamp comparison.  No finite-cube approximate fixed point and no
  family-uniform left tail occur in the statement.
-/
import ShenWork.Paper1.WaveLocalSourceTrap
import ShenWork.Paper1.WavePaperRouteA

open Filter Topology MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

/-- A genuine fixed source together with the a-priori range of its Green
profile. -/
structure PaperLocalFixedStepData
    (p : CMParams) (c lam M κ Λ : ℝ) (u Z : ℝ → ℝ) where
  fixed : PaperStepFixedSourceCore p c lam M κ Λ u Z
  range : ∀ x, fixed.W x ∈ Set.Icc (0 : ℝ) (upperBarrier κ M x)

/-- The local source Schauder construction produces the exact genuine paper
source equation after the tail-free maximum principles deactivate the spatial
clamp. -/
theorem paperLocalFixedStepData_exists_of_trap
    (p : CMParams)
    {c lam M κ Λ B H : ℝ} {u Z : ℝ → ℝ}
    (hlam : 0 < lam)
    (hrpκ : κ < greenRootPlus c lam)
    (hrmκ : κ < -greenRootMinus c lam)
    (hκ : 0 < κ) (hM : 0 < M) (hB : 0 ≤ B)
    (hu : InMonotoneWaveTrapSet κ M u)
    (hZ : PaperIterateBase p c κ M u Z)
    (hsourceScalar :
      |(-p.χ * p.m)| * M ^ (p.m - 1) * M ^ p.γ *
            greenWeightedMass1 c lam κ * B
        + (1 + |p.χ| * M ^ (p.m - 1) * M ^ p.γ
            + M ^ p.α + |p.χ| * M ^ (p.m + p.γ - 1))
        + lam ≤ B)
    (hHolder :
      Classical.choose
        (paperFixedSourceMap_holder_kernel
          (p := p) (c := c) (lam := lam) (M := M) (κ := κ) (B := B)
          (u := u) (Z := Z)
          hlam hrpκ hrmκ hκ.le hM hB hu.trap hZ) ≤ H)
    (hbarrier : PaperUpperBarrierSuperScalarConditions p c κ M)
    (hΛ : Λ = 2 * (greenDelta c lam)⁻¹ * (B * M)) :
    ∃ d : PaperLocalFixedStepData p c lam M κ Λ u Z,
      PaperLocalHolderSourceBox κ M (paperWeightedHolderExponent p) B H
        d.fixed.R := by
  obtain ⟨R, hR, hRfix⟩ :=
    paperFixedSourceMap_exists_fixed_local_of_trap
      p (c := c) (lam := lam) (M := M) (κ := κ) (B := B) (H := H)
      (u := u) (Z := Z)
      hlam hrpκ hrmκ hκ.le hM hB hu hZ hsourceScalar hHolder
  have hIcc : ∀ x, greenConv c lam R x ∈
      Set.Icc (0 : ℝ) (upperBarrier κ M x) :=
    paperFixedSource_truncation_inactive_local_of_scalar
      (p := p) (c := c) (lam := lam) (M := M) (κ := κ)
      (u := u) (Z := Z) (R := R)
      hlam hκ hM hB hu hZ hbarrier hR hRfix
  have htrunc :
      paperFixedSourceMap p c lam M κ u Z R =
        paperStepSource p c lam u Z (fun x => greenConv c lam R x) :=
    paperStepSource_truncated_eq_paperStepSource_of_Icc
      (p := p) (c := c) (lam := lam) (M := M) (κ := κ)
      (u := u) (Z := Z) (R := R) hM.le hIcc
  have hsource :
      R = paperStepSource p c lam u Z (fun x => greenConv c lam R x) := by
    calc
      R = paperFixedSourceMap p c lam M κ u Z R := hRfix.symm
      _ = paperStepSource p c lam u Z (fun x => greenConv c lam R x) := htrunc
  have hRbound : ∀ y, |R y| ≤ B * M := by
    intro y
    calc
      |R y| ≤ B * upperBarrier κ M y := hR.bound y
      _ ≤ B * M :=
        mul_le_mul_of_nonneg_left (upperBarrier_le_M κ M y) hB
  let fixed : PaperStepFixedSourceCore p c lam M κ Λ u Z :=
    { R := R
      source_eq := hsource
      R_cont := hR.cont
      R_bound_const := B * M
      R_bound := hRbound
      R_bound_eq := hΛ }
  let d : PaperLocalFixedStepData p c lam M κ Λ u Z :=
    { fixed := fixed
      range := by
        intro x
        simpa [fixed, PaperStepFixedSourceCore.W] using hIcc x }
  exact ⟨d, by simpa [d, fixed] using hR⟩

namespace PaperLocalFixedStepData

theorem step_op
    {p : CMParams} {c lam M κ Λ : ℝ} {u Z : ℝ → ℝ}
    (hlam : 0 < lam) (d : PaperLocalFixedStepData p c lam M κ Λ u Z) :
    ∀ x, paperImplicitStepOp p c (1 / lam) u d.fixed.W x = Z x :=
  smooth_paperStep_step_op_of_core hlam d.fixed.analyticCore

theorem contDiff_two
    {p : CMParams} {c lam M κ Λ : ℝ} {u Z : ℝ → ℝ}
    (hlam : 0 < lam) (d : PaperLocalFixedStepData p c lam M κ Λ u Z) :
    ContDiff ℝ 2 d.fixed.W :=
  paperStep_contDiff_two_of_core hlam d.fixed.analyticCore

theorem deriv_le
    {p : CMParams} {c lam M κ Λ : ℝ} {u Z : ℝ → ℝ}
    (hlam : 0 < lam) (d : PaperLocalFixedStepData p c lam M κ Λ u Z) :
    ∀ x, |deriv d.fixed.W x| ≤ Λ :=
  (smooth_paperStep_basic_regular_of_core hlam d.fixed.analyticCore).2.2

end PaperLocalFixedStepData

/-- Build the actual Route-A orbit core from the no-tail local source Schauder
construction.  The Holder radius is selected separately for each genuine
regular iterate from the explicit kernel estimate; no shared exponential
left-rate of the parameter profile or of the orbit is assumed. -/
noncomputable def paperGreenStepInputRouteAOrbitCore_of_localFixedStep
    (p : CMParams)
    {c lam M κ Λ B : ℝ} {u : ℝ → ℝ}
    (hlam : 0 < lam)
    (hrpκ : κ < greenRootPlus c lam)
    (hrmκ : κ < -greenRootMinus c lam)
    (hκ : 0 < κ) (hM : 0 < M) (hB : 0 ≤ B)
    (hu : InMonotoneWaveTrapSet κ M u)
    (hsourceScalar :
      |(-p.χ * p.m)| * M ^ (p.m - 1) * M ^ p.γ *
            greenWeightedMass1 c lam κ * B
        + (1 + |p.χ| * M ^ (p.m - 1) * M ^ p.γ
            + M ^ p.α + |p.χ| * M ^ (p.m + p.γ - 1))
        + lam ≤ B)
    (hbarrier : PaperUpperBarrierSuperScalarConditions p c κ M)
    (hΛ : Λ = 2 * (greenDelta c lam)⁻¹ * (B * M))
    (hrest : ∀ Z : ℝ → ℝ, PaperIterateBase p c κ M u Z →
      ∀ fixed : PaperStepFixedSourceCore p c lam M κ Λ u Z,
        PaperStepOutputRouteAFixedRestData p c lam M κ Λ u Z fixed) :
    PaperGreenStepInputRouteAOrbitCore p c lam M κ Λ u where
  hlam := hlam
  basePaperSuper :=
    paperUpperBarrier_super_of_scalar hκ hbarrier hu
  produce_regular := by
    intro Z hZ
    let holderKernel :=
      paperFixedSourceMap_holder_kernel
        (p := p) (c := c) (lam := lam) (M := M) (κ := κ) (B := B)
        (u := u) (Z := Z)
        hlam hrpκ hrmκ hκ.le hM hB hu.trap hZ
    let H : ℝ := Classical.choose holderKernel
    let hex :=
      paperLocalFixedStepData_exists_of_trap
        p (c := c) (lam := lam) (M := M) (κ := κ) (Λ := Λ)
        (B := B) (H := H) (u := u) (Z := Z)
        hlam hrpκ hrmκ hκ hM hB hu hZ hsourceScalar le_rfl
        hbarrier hΛ
    let d := Classical.choose hex
    exact ⟨d.fixed.W, (hrest Z hZ d.fixed).toOutputRouteACore.2⟩

section AxiomAudit

#print axioms paperLocalFixedStepData_exists_of_trap
#print axioms PaperLocalFixedStepData.step_op
#print axioms PaperLocalFixedStepData.contDiff_two
#print axioms PaperLocalFixedStepData.deriv_le
#print axioms paperGreenStepInputRouteAOrbitCore_of_localFixedStep

end AxiomAudit

end ShenWork.Paper1
