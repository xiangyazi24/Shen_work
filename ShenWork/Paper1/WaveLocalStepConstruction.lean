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
    (p : CMParams) (c lam M κ Λ B : ℝ) (u Z : ℝ → ℝ) where
  fixed : PaperStepFixedSourceCore p c lam M κ Λ u Z
  range : ∀ x, fixed.W x ∈ Set.Icc (0 : ℝ) (upperBarrier κ M x)
  sourceWeightedBound :
    ∀ x, |fixed.R x| ≤ B * upperBarrier κ M x

/-- The local source Schauder construction produces the exact genuine paper
source equation after the tail-free maximum principles deactivate the spatial
clamp. -/
theorem paperLocalFixedStepData_exists_of_oldData
    (p : CMParams)
    {c lam M κ Λ B H : ℝ} {u Z : ℝ → ℝ}
    (hlam : 0 < lam)
    (hrpκ : κ < greenRootPlus c lam)
    (hrmκ : κ < -greenRootMinus c lam)
    (hκ : 0 < κ) (hM : 0 < M) (hB : 0 ≤ B)
    (hu : InMonotoneWaveTrapSet κ M u)
    (hZ : PaperFixedSourceOldData κ M Z)
    (hsourceScalar :
      |(-p.χ * p.m)| * M ^ (p.m - 1) * M ^ p.γ *
            greenWeightedMass1 c lam κ * B
        + (1 + |p.χ| * M ^ (p.m - 1) * M ^ p.γ
            + M ^ p.α + |p.χ| * M ^ (p.m + p.γ - 1))
        + lam ≤ B)
    (hHolder :
      Classical.choose
        (paperFixedSourceMap_holder_kernel_of_oldData
          (p := p) (c := c) (lam := lam) (M := M) (κ := κ) (B := B)
          (u := u) (Z := Z)
          hlam hrpκ hrmκ hκ.le hM hB hu.trap hZ) ≤ H)
    (hbarrier : PaperUpperBarrierSuperScalarConditions p c κ M)
    (hΛ : Λ = 2 * (greenDelta c lam)⁻¹ * (B * M)) :
    ∃ d : PaperLocalFixedStepData p c lam M κ Λ B u Z,
      PaperLocalHolderSourceBox κ M (paperWeightedHolderExponent p) B H
        d.fixed.R := by
  obtain ⟨R, hR, hRfix⟩ :=
    paperFixedSourceMap_exists_fixed_local_of_oldData
      p (c := c) (lam := lam) (M := M) (κ := κ) (B := B) (H := H)
      (u := u) (Z := Z)
      hlam hrpκ hrmκ hκ.le hM hB hu hZ hsourceScalar hHolder
  have hIcc : ∀ x, greenConv c lam R x ∈
      Set.Icc (0 : ℝ) (upperBarrier κ M x) :=
    paperFixedSource_truncation_inactive_local_of_oldData
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
  let d : PaperLocalFixedStepData p c lam M κ Λ B u Z :=
    { fixed := fixed
      range := by
        intro x
        simpa [fixed, PaperStepFixedSourceCore.W] using hIcc x
      sourceWeightedBound := by
        intro x
        simpa [fixed] using hR.bound x }
  exact ⟨d, by simpa [d, fixed] using hR⟩

/-- Backwards-compatible local-step constructor for a full Rothe old
iterate. -/
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
    ∃ d : PaperLocalFixedStepData p c lam M κ Λ B u Z,
      PaperLocalHolderSourceBox κ M (paperWeightedHolderExponent p) B H
        d.fixed.R := by
  let hZold := hZ.toFixedSourceOldData hκ.le hM.le
  apply paperLocalFixedStepData_exists_of_oldData
    p hlam hrpκ hrmκ hκ hM hB hu hZold hsourceScalar
  · simpa using hHolder
  · exact hbarrier
  · exact hΛ

namespace PaperLocalFixedStepData

/-- Uniform coefficient in the weighted Green derivative estimate.  It is
record-independent because the source Schauder construction now retains its
global weight `B` in the type of every local step. -/
def paperStepWeightedDerivCoeff (c lam κ B : ℝ) : ℝ :=
  (greenDelta c lam)⁻¹ *
    (greenRootPlus c lam *
        (B / (greenRootPlus c lam - κ)) +
      (-greenRootMinus c lam) *
        (B / (-(greenRootMinus c lam + κ))))

theorem step_op
    {p : CMParams} {c lam M κ Λ B : ℝ} {u Z : ℝ → ℝ}
    (hlam : 0 < lam) (d : PaperLocalFixedStepData p c lam M κ Λ B u Z) :
    ∀ x, paperImplicitStepOp p c (1 / lam) u d.fixed.W x = Z x :=
  smooth_paperStep_step_op_of_core hlam d.fixed.analyticCore

theorem contDiff_two
    {p : CMParams} {c lam M κ Λ B : ℝ} {u Z : ℝ → ℝ}
    (hlam : 0 < lam) (d : PaperLocalFixedStepData p c lam M κ Λ B u Z) :
    ContDiff ℝ 2 d.fixed.W :=
  paperStep_contDiff_two_of_core hlam d.fixed.analyticCore

theorem deriv_le
    {p : CMParams} {c lam M κ Λ B : ℝ} {u Z : ℝ → ℝ}
    (hlam : 0 < lam) (d : PaperLocalFixedStepData p c lam M κ Λ B u Z) :
    ∀ x, |deriv d.fixed.W x| ≤ Λ :=
  (smooth_paperStep_basic_regular_of_core hlam d.fixed.analyticCore).2.2

/-- Coefficient in the weighted Green derivative estimate. -/
def weightedDerivCoeff
    {p : CMParams} {M Λ B : ℝ} {u Z : ℝ → ℝ}
    (c lam κ : ℝ) (_d : PaperLocalFixedStepData p c lam M κ Λ B u Z) : ℝ :=
  paperStepWeightedDerivCoeff c lam κ B

theorem weightedDerivCoeff_nonneg
    {p : CMParams} {c lam M κ Λ B : ℝ} {u Z : ℝ → ℝ}
    (hlam : 0 < lam)
    (hrpκ : κ < greenRootPlus c lam)
    (hrmκ : κ < -greenRootMinus c lam)
    (hB : 0 ≤ B)
    (d : PaperLocalFixedStepData p c lam M κ Λ B u Z) :
    0 ≤ d.weightedDerivCoeff c lam κ := by
  unfold weightedDerivCoeff
  have hδ : 0 < greenDelta c lam := greenDelta_pos hlam
  have hrp : 0 < greenRootPlus c lam := greenRootPlus_pos hlam
  have hrm : greenRootMinus c lam < 0 := greenRootMinus_neg hlam
  have hdenp : 0 < greenRootPlus c lam - κ := by linarith
  have hdenm : 0 < -(greenRootMinus c lam + κ) := by linarith
  exact mul_nonneg (inv_nonneg.mpr hδ.le)
    (add_nonneg
      (mul_nonneg hrp.le (div_nonneg hB hdenp.le))
      (mul_nonneg (neg_nonneg.mpr hrm.le)
        (div_nonneg hB hdenm.le)))

/-- The fixed source's weighted box yields a derivative bound with the same
exponential upper barrier, rather than only a global constant. -/
theorem deriv_abs_le_weighted_barrier
    {p : CMParams} {c lam M κ Λ B : ℝ} {u Z : ℝ → ℝ}
    (hlam : 0 < lam)
    (hrpκ : κ < greenRootPlus c lam)
    (hrmκ : κ < -greenRootMinus c lam)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (d : PaperLocalFixedStepData p c lam M κ Λ B u Z) :
    ∀ x, |deriv d.fixed.W x| ≤
      d.weightedDerivCoeff c lam κ * upperBarrier κ M x := by
  intro x
  have hHi : ∀ t, IntegrableOn
      (gWeight (greenRootPlus c lam) d.fixed.R) (Set.Ioi t) :=
    fun t => gWeight_integrableOn_Ioi_of_bounded
      (greenRootPlus_pos (c := c) hlam) d.fixed.R_cont
      d.fixed.R_bound t
  have hLo : ∀ t, IntegrableOn
      (gWeight (greenRootMinus c lam) d.fixed.R) (Set.Iic t) :=
    fun t => gWeight_integrableOn_Iic_of_bounded
      (greenRootMinus_neg (c := c) hlam) d.fixed.R_cont
      d.fixed.R_bound t
  have hraw := deriv_greenConv_abs_le_upperBarrier_of_source_bound
    (c := c) (lam := lam) hlam hrpκ hrmκ hκ hM
      hB d.fixed.R_cont d.sourceWeightedBound hHi hLo x
  change |deriv (greenConv c lam d.fixed.R) x| ≤ _ at hraw
  change |deriv (greenConv c lam d.fixed.R) x| ≤ _
  calc
    |deriv (greenConv c lam d.fixed.R) x| ≤
        (greenDelta c lam)⁻¹ *
          (greenRootPlus c lam *
              (B * upperBarrier κ M x /
                (greenRootPlus c lam - κ)) +
            (-greenRootMinus c lam) *
              (B * upperBarrier κ M x /
                (-(greenRootMinus c lam + κ)))) := hraw
    _ = d.weightedDerivCoeff c lam κ * upperBarrier κ M x := by
      unfold weightedDerivCoeff paperStepWeightedDerivCoeff
      ring

end PaperLocalFixedStepData

/-- The two genuine order facts not supplied by the local source Schauder
construction itself.  They are the output of the parabolic comparison and
Route-A derivative maximum principles. -/
structure PaperLocalFixedStepRestData
    (p : CMParams) (c lam M κ Λ B : ℝ) (u Z : ℝ → ℝ)
    (d : PaperLocalFixedStepData p c lam M κ Λ B u Z) where
  le_old : ∀ x, d.fixed.W x ≤ Z x
  anti : Antitone d.fixed.W

/-- Per-orbit provider for the comparison and Route-A order facts left after
the local source construction has already proved the exact Green equation and
the pointwise range `0 ≤ W ≤ upperBarrier`. -/
def PaperLocalFixedStepRestProvider
    (p : CMParams) (c lam M κ Λ B : ℝ) (u : ℝ → ℝ) : Prop :=
  ∀ Z : ℝ → ℝ, PaperIterateBase p c κ M u Z →
    ∀ d : PaperLocalFixedStepData p c lam M κ Λ B u Z,
      PaperLocalFixedStepRestData p c lam M κ Λ B u Z d

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
    (hrest : PaperLocalFixedStepRestProvider p c lam M κ Λ B u) :
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
    let rest := hrest Z hZ d
    exact
      ⟨d.fixed.W,
        { analytic := d.fixed.analyticCore
          nonneg := fun x => (d.range x).1
          le_barrier := fun x => (d.range x).2
          le_old := rest.le_old
          anti := rest.anti }⟩

section AxiomAudit

#print axioms paperLocalFixedStepData_exists_of_oldData
#print axioms paperLocalFixedStepData_exists_of_trap
#print axioms PaperLocalFixedStepData.step_op
#print axioms PaperLocalFixedStepData.contDiff_two
#print axioms PaperLocalFixedStepData.deriv_le
#print axioms PaperLocalFixedStepData.weightedDerivCoeff_nonneg
#print axioms PaperLocalFixedStepData.deriv_abs_le_weighted_barrier
#print axioms paperGreenStepInputRouteAOrbitCore_of_localFixedStep

end AxiomAudit

end ShenWork.Paper1
