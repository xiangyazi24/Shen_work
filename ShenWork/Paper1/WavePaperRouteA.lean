/-
  ShenWork/Paper1/WavePaperRouteA.lean

  Route A for the paper-expanded step: monotone smoothing, the smooth
  derivative maximum-principle core, and the pointwise limit passage.

  This file deliberately does not use the older sliding wrappers as the
  antitonicity proof.  The smooth maximum principle below is driven by
  `q = W'` and the differentiated paper-expanded operator estimate.
-/
import ShenWork.Paper1.WavePaperRotheProducer
import ShenWork.Paper1.WaveApproxMaximum
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

open Filter Topology MeasureTheory Set Real ContinuousLinearMap
open scoped Convolution

noncomputable section

namespace ShenWork.Paper1

/-! ## Step A: nonnegative convolution kernels preserve antitonicity -/

/-- The Route-A mollification operator, written as Mathlib's convolution
`ρ ⋆ Z`.  For a bump family `ρ = ρ_ε`, this is `Z_ε = ρ_ε * Z`. -/
def mollify (ρ Z : ℝ → ℝ) : ℝ → ℝ :=
  ρ ⋆[lsmul ℝ ℝ, volume] Z

/-- Positivity of convolution with a nonnegative scalar kernel preserves
antitonicity.  The hypotheses are intentionally the exact analytic facts needed
by the Bochner integral: pointwise integrability of the convolution integrand
and pointwise nonnegativity of the kernel. -/
theorem mollify_antitone_of_nonneg_kernel
    {ρ Z : ℝ → ℝ}
    (hZ : Antitone Z)
    (hρ : ∀ t, 0 ≤ ρ t)
    (hint : ∀ x, Integrable (fun t => ρ t • Z (x - t)) volume) :
    Antitone (mollify ρ Z) := by
  intro x y hxy
  unfold mollify
  rw [convolution_lsmul, convolution_lsmul]
  refine integral_mono (hint y) (hint x) ?_
  intro t
  exact smul_le_smul_of_nonneg_left (hZ (by linarith : x - t ≤ y - t)) (hρ t)

/-- Route-A Step A in the form used downstream: the mollified old iterate is
antitone, hence its derivative is everywhere nonpositive. -/
theorem mollify_antitone
    {ρ Z : ℝ → ℝ}
    (hZ : Antitone Z)
    (hρ : ∀ t, 0 ≤ ρ t)
    (hint : ∀ x, Integrable (fun t => ρ t • Z (x - t)) volume) :
    Antitone (mollify ρ Z) ∧ ∀ x, deriv (mollify ρ Z) x ≤ 0 := by
  have hanti := mollify_antitone_of_nonneg_kernel (ρ := ρ) (Z := Z) hZ hρ hint
  exact ⟨hanti, fun x => hanti.deriv_nonpos⟩

/-- A normalized compactly supported smooth bump kernel gives a smooth
mollification of any locally integrable old iterate. -/
theorem mollify_contDiff_of_hasCompactSupport
    {ρ Z : ℝ → ℝ} {n : ℕ∞}
    (hρc : HasCompactSupport ρ)
    (hρs : ContDiff ℝ n ρ)
    (hZloc : LocallyIntegrable Z volume) :
    ContDiff ℝ n (mollify ρ Z) := by
  unfold mollify
  exact hρc.contDiff_convolution_left (L := lsmul ℝ ℝ) hρs hZloc

/-- Convolution against a nonnegative unit-mass kernel preserves boundedness. -/
theorem mollify_isBddFun_of_nonneg_kernel
    {ρ Z : ℝ → ℝ}
    (hZB : IsBddFun Z)
    (hρ : ∀ t, 0 ≤ ρ t)
    (hρint : Integrable ρ volume)
    (hρone : ∫ t, ρ t = 1)
    (hint : ∀ x, Integrable (fun t => ρ t • Z (x - t)) volume) :
    IsBddFun (mollify ρ Z) := by
  rcases hZB with ⟨B, hB⟩
  refine ⟨|B|, fun x => ?_⟩
  unfold mollify
  rw [convolution_lsmul]
  have hnorm_le :
      |∫ t, ρ t • Z (x - t)| ≤ ∫ t, |ρ t • Z (x - t)| := by
    simpa [Real.norm_eq_abs] using
      norm_integral_le_integral_norm (μ := volume)
        (fun t => ρ t • Z (x - t))
  have hbound_int : Integrable (fun t => |B| * ρ t) volume :=
    hρint.const_mul |B|
  have hmono :
      (∫ t, |ρ t • Z (x - t)|) ≤ ∫ t, |B| * ρ t := by
    refine integral_mono (hint x).norm hbound_int ?_
    intro t
    calc
      |ρ t • Z (x - t)| = ρ t * |Z (x - t)| := by
        simp [smul_eq_mul, abs_mul, abs_of_nonneg (hρ t)]
      _ ≤ ρ t * |B| :=
        mul_le_mul_of_nonneg_left
          (le_trans (hB (x - t)) (le_abs_self B)) (hρ t)
      _ = |B| * ρ t := by ring
  calc
    |∫ t, ρ t • Z (x - t)| ≤ ∫ t, |ρ t • Z (x - t)| := hnorm_le
    _ ≤ ∫ t, |B| * ρ t := hmono
    _ = |B| := by rw [integral_const_mul, hρone, mul_one]

/-- Bump-kernel mollification is a direct instance of `mollify_antitone`: the
kernel is nonnegative and compact support supplies the integrability of the
convolution integrand. -/
theorem bump_mollify_antitone
    (φ : ContDiffBump (0 : ℝ)) {Z : ℝ → ℝ}
    (hZ : Antitone Z) (hZloc : LocallyIntegrable Z volume) :
    Antitone (mollify (φ.normed volume) Z) ∧
      ∀ x, deriv (mollify (φ.normed volume) Z) x ≤ 0 := by
  refine mollify_antitone (ρ := φ.normed volume) (Z := Z) hZ
    (fun t => φ.nonneg_normed t) ?_
  have hconv : ConvolutionExists (φ.normed volume) Z (lsmul ℝ ℝ) volume :=
    φ.hasCompactSupport_normed.convolutionExists_left
      (L := lsmul ℝ ℝ) φ.continuous_normed hZloc
  exact hconv

/-- Smoothness of bump-kernel mollification. -/
theorem bump_mollify_contDiff
    (φ : ContDiffBump (0 : ℝ)) {Z : ℝ → ℝ} {n : ℕ∞}
    (hZloc : LocallyIntegrable Z volume) :
    ContDiff ℝ n (mollify (φ.normed volume) Z) := by
  exact mollify_contDiff_of_hasCompactSupport
    (ρ := φ.normed volume) (Z := Z) φ.hasCompactSupport_normed
    φ.contDiff_normed hZloc

/-- Bump-kernel mollification of a bounded profile is bounded. -/
theorem bump_mollify_isBddFun
    (φ : ContDiffBump (0 : ℝ)) {Z : ℝ → ℝ}
    (hZB : IsBddFun Z) (hZloc : LocallyIntegrable Z volume) :
    IsBddFun (mollify (φ.normed volume) Z) := by
  refine mollify_isBddFun_of_nonneg_kernel
    (ρ := φ.normed volume) (Z := Z) hZB
    (fun t => φ.nonneg_normed t) φ.integrable_normed
    φ.integral_normed ?_
  have hconv : ConvolutionExists (φ.normed volume) Z (lsmul ℝ ℝ) volume :=
    φ.hasCompactSupport_normed.convolutionExists_left
      (L := lsmul ℝ ℝ) φ.continuous_normed hZloc
  exact hconv

/-- Local-uniform/pointwise approximation supplied by Mathlib's normalized bump
convolution theorem, stated in the Route-A `mollify` notation. -/
theorem bump_mollify_tendsto_right_of_continuous
    {ι : Type*} {φ : ι → ContDiffBump (0 : ℝ)} {l : Filter ι}
    {Z : ℝ → ℝ}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (hZ : Continuous Z) (x₀ : ℝ) :
    Tendsto (fun i => mollify ((φ i).normed volume) Z x₀) l (𝓝 (Z x₀)) := by
  simpa [mollify] using
    ContDiffBump.convolution_tendsto_right_of_continuous
      (μ := volume) (φ := φ) (g := Z) hφ hZ x₀

/-! ## Step A' — finite tails for bounded antitone profiles -/

/-- A bump-mollified bounded antitone profile is antitone, smooth, and has
finite tail limits. -/
theorem bump_mollify_antitone_contDiff_tail_limits
    (φ : ContDiffBump (0 : ℝ)) {Z : ℝ → ℝ} {n : ℕ∞}
    (hZanti : Antitone Z) (hZB : IsBddFun Z)
    (hZloc : LocallyIntegrable Z volume) :
    (Antitone (mollify (φ.normed volume) Z) ∧
      ∀ x, deriv (mollify (φ.normed volume) Z) x ≤ 0) ∧
    ContDiff ℝ n (mollify (φ.normed volume) Z) ∧
    (∃ La : ℝ, Tendsto (mollify (φ.normed volume) Z) atBot (𝓝 La)) ∧
      ∃ Lb : ℝ, Tendsto (mollify (φ.normed volume) Z) atTop (𝓝 Lb) := by
  have hanti := bump_mollify_antitone φ hZanti hZloc
  have hsmooth : ContDiff ℝ n (mollify (φ.normed volume) Z) :=
    bump_mollify_contDiff φ hZloc
  have hbdd : IsBddFun (mollify (φ.normed volume) Z) :=
    bump_mollify_isBddFun φ hZB hZloc
  exact ⟨hanti, hsmooth,
    antitone_isBddFun_has_tail_limits hanti.1 hbdd⟩

/-! ## Step B: smooth paper step through the existing Green layer -/

/-- Route-A Step B: once the existing paper Green fixed-source layer provides a
`PaperStepAnalyticCore`, the paper-expanded implicit step equation follows from
the committed Green resolvent identity. -/
theorem smooth_paperStep_step_op_of_core
    {p : CMParams} {c lam M κ Λ : ℝ} {u Z W : ℝ → ℝ}
    (hlam : 0 < lam)
    (hc : PaperStepAnalyticCore p c lam M κ Λ u Z W) :
    ∀ x, paperImplicitStepOp p c (1 / lam) u W x = Z x := by
  exact paperStep_step_op (c := c) (lam := lam) hlam
    (paperStepAnalytic_of_core hlam hc)

/-- Differentiate the paper implicit-step identity.

This is the wiring lemma that turns the Green fixed-step equation
`W - (1 / lam) A(W) = Z` into the differentiated equation consumed by the
Route-A maximum principle. -/
theorem paperStep_stepDeriv_of_implicit
    {p : CMParams} {c lam : ℝ} {u Z W : ℝ → ℝ}
    (hstep : ∀ x, paperImplicitStepOp p c (1 / lam) u W x = Z x)
    (hWdiff : Differentiable ℝ W)
    (hAdiff : Differentiable ℝ (fun y => paperWaveOperator p c u W y)) :
    ∀ x,
      deriv W x - (1 / lam) *
          deriv (fun y => paperWaveOperator p c u W y) x = deriv Z x := by
  intro x
  let A : ℝ → ℝ := fun y => paperWaveOperator p c u W y
  have hfun : (fun y => W y - (1 / lam) * A y) = Z := by
    funext y
    simpa [paperImplicitStepOp_apply, A] using hstep y
  have hleft :
      deriv (fun y => W y - (1 / lam) * A y) x =
        deriv W x - (1 / lam) * deriv A x := by
    have hW' : HasDerivAt W (deriv W x) x := (hWdiff x).hasDerivAt
    have hA' : HasDerivAt (fun y => (1 / lam) * A y)
        ((1 / lam) * deriv A x) x :=
      (hAdiff x).hasDerivAt.const_mul (1 / lam)
    exact (hW'.sub hA').deriv
  calc
    deriv W x - (1 / lam) * deriv (fun y => paperWaveOperator p c u W y) x
        = deriv W x - (1 / lam) * deriv A x := rfl
    _ = deriv (fun y => W y - (1 / lam) * A y) x := hleft.symm
    _ = deriv Z x := by rw [hfun]

/-- Analytic regularity and the `C¹` bound supplied by the existing paper
Green layer.  Higher smoothness for a smooth fixed source is handled upstream;
Route A only needs this bridge to avoid using the older sliding monotonicity
wrappers. -/
theorem smooth_paperStep_basic_regular_of_core
    {p : CMParams} {c lam M κ Λ : ℝ} {u Z W : ℝ → ℝ}
    (hlam : 0 < lam)
    (hc : PaperStepAnalyticCore p c lam M κ Λ u Z W) :
    Continuous W ∧ Differentiable ℝ W ∧ ∀ x, |deriv W x| ≤ Λ := by
  let ha := paperStepAnalytic_of_core (c := c) (lam := lam) hlam hc
  exact ⟨paperStep_cont (c := c) (lam := lam) hlam ha,
    paperStep_diff (c := c) (lam := lam) hlam ha,
    paperStep_deriv_le (c := c) (lam := lam) hlam ha⟩

/-! ## Step C: derivative maximum principle for the smooth paper step -/

/-- The coefficient used in the Route-A quasi-monotone estimate.  This is the
expanded form of
`reactionLip(α,M) + a*m*M^(m-1)*(BV2+BV)`, split so Lean's linear arithmetic can
consume the two elliptic bounds separately. -/
def paperCmono (p : CMParams) (a M BV BV2 : ℝ) : ℝ :=
  reactionLip p.α M
    + a * p.m * M ^ (p.m - 1) * BV2
    + a * p.m * M ^ (p.m - 1) * BV

/-- Route-A local bookkeeping at a positive maximum of `q = W'`.

The fields are the paper-expanded differentiated operator, split into:

* `qSecond`, nonpositive at a maximum;
* `qSlope`, whose transport contribution vanishes at a maximum;
* genuinely good terms (`slopeQuad`, `vForcing`, `diagonal`) which are
  nonpositive for negative sensitivity and monotone elliptic signal;
* the three remaining `q`-coefficients, each bounded by the components of
  `paperCmono`.

This deliberately records the sign ledger, not the final maximum estimate. -/
structure PaperWaveOperatorPosMaxBookkeeping
    (p : CMParams) (c a M BV BV2 : ℝ) (u W : ℝ → ℝ) (x₀ : ℝ) where
  q : ℝ
  qSlope : ℝ
  qSecond : ℝ
  slopeQuad : ℝ
  transport : ℝ
  vForcing : ℝ
  diagonal : ℝ
  reactionCoeff : ℝ
  v2Coeff : ℝ
  vCoeff : ℝ
  q_eq : q = deriv W x₀
  paper_deriv :
    deriv (fun x => paperWaveOperator p c u W x) x₀ =
      qSecond + c * qSlope + slopeQuad + transport + vForcing + diagonal
        + (reactionCoeff + v2Coeff + vCoeff) * q
  qSlope_zero : qSlope = 0
  qSecond_nonpos : qSecond ≤ 0
  slopeQuad_nonpos : slopeQuad ≤ 0
  transport_zero : transport = 0
  vForcing_nonpos : vForcing ≤ 0
  diagonal_nonpos : diagonal ≤ 0
  reactionCoeff_le : reactionCoeff ≤ reactionLip p.α M
  v2Coeff_le : v2Coeff ≤ a * p.m * M ^ (p.m - 1) * BV2
  vCoeff_le : vCoeff ≤ a * p.m * M ^ (p.m - 1) * BV

private theorem paperWaveOperator_hasDerivAt_routeA
    {p : CMParams} {c a : ℝ} {u W : ℝ → ℝ} {x₀ : ℝ}
    (ha : a = -p.χ)
    (hW0 : HasDerivAt W (deriv W x₀) x₀)
    (hW1 : HasDerivAt (deriv W) (deriv (deriv W) x₀) x₀)
    (hW2 : HasDerivAt (iteratedDeriv 2 W) (deriv (deriv (deriv W)) x₀) x₀)
    (hV0 : HasDerivAt (frozenElliptic p u) (deriv (frozenElliptic p u) x₀) x₀)
    (hV1 : HasDerivAt (deriv (frozenElliptic p u))
      (deriv (deriv (frozenElliptic p u)) x₀) x₀)
    (hWpos : 0 < W x₀) :
    HasDerivAt (fun x => paperWaveOperator p c u W x)
      (deriv (deriv (deriv W)) x₀ + c * deriv (deriv W) x₀
        + a * p.m * (p.m - 1) * (W x₀) ^ (p.m - 2) * (deriv W x₀)^2 *
            deriv (frozenElliptic p u) x₀
        + a * p.m * (W x₀) ^ (p.m - 1) * deriv (frozenElliptic p u) x₀ *
            deriv (deriv W) x₀
        + a * (W x₀) ^ p.m * deriv (frozenElliptic p u) x₀
        - a * (p.m + p.γ) * (W x₀) ^ (p.m + p.γ - 1) * deriv W x₀
        + ((1 - (W x₀) ^ p.α - p.α * (W x₀ * (W x₀) ^ (p.α - 1)))
            + a * p.m * (W x₀) ^ (p.m - 1) *
                deriv (deriv (frozenElliptic p u)) x₀
            + a * p.m * (W x₀) ^ (p.m - 1) * frozenElliptic p u x₀) *
              deriv W x₀)
      x₀ := by
  let V := frozenElliptic p u
  have hpow_m1 := hW0.rpow_const (p := p.m - 1) (Or.inl hWpos.ne')
  have hpow_m := hW0.rpow_const (p := p.m) (Or.inl hWpos.ne')
  have hpow_mγ := hW0.rpow_const (p := p.m + p.γ) (Or.inl hWpos.ne')
  have hlin := hW2.fun_add (hW1.const_mul c)
  have hchem_core := (hpow_m1.fun_mul hV1).fun_mul hW1
  have hchem := hchem_core.const_mul (a * p.m)
  have hrxn : HasDerivAt (fun x => reactionFun p.α (W x))
      ((1 - (W x₀) ^ p.α - p.α * (W x₀ * (W x₀) ^ (p.α - 1))) *
        deriv W x₀) x₀ := by
    simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using
      (reactionFun_hasDerivAt p.α p.hα (W x₀)).comp x₀ hW0
  have hVterm_core := hpow_m.fun_mul hV0
  have hVterm := hVterm_core.const_mul a
  have hdiag := hpow_mγ.const_mul (-a)
  have htotal := ((((hlin.fun_add hchem).fun_add hrxn).fun_add hVterm).fun_add hdiag)
  have hWpos_ev : ∀ᶠ x in 𝓝 x₀, 0 < W x :=
    hW0.continuousAt.eventually (lt_mem_nhds hWpos)
  have heq : (fun x => paperWaveOperator p c u W x) =ᶠ[𝓝 x₀]
      (fun x => (((iteratedDeriv 2 W x + c * deriv W x)
        + a * p.m * ((W x) ^ (p.m - 1) * deriv V x * deriv W x))
        + reactionFun p.α (W x))
        + a * ((W x) ^ p.m * V x)
        + (-a) * (W x) ^ (p.m + p.γ)) := by
    filter_upwards [hWpos_ev] with x hxpos
    have hm_id : (W x) ^ (p.m - 1) * W x = (W x) ^ p.m := by
      rw [mul_comm]
      exact mul_rpow_sub_one p.m p.hm hxpos.le
    have hmg : 1 ≤ p.m + p.γ := by linarith [p.hm, p.hγ]
    have hmg_id : W x * (W x) ^ (p.m + p.γ - 1) = (W x) ^ (p.m + p.γ) :=
      mul_rpow_sub_one (p.m + p.γ) hmg hxpos.le
    unfold paperWaveOperator reactionFun
    simp only [V]
    rw [ha, ← hm_id, ← hmg_id]
    ring
  convert htotal.congr_of_eventuallyEq heq using 1
  · ring_nf

private theorem paperWaveOperator_posMax_value_pos
    {W : ℝ → ℝ} {M x₀ : ℝ}
    (hWrange : ∀ x, W x ∈ Set.Icc (0 : ℝ) M)
    (hqpos : 0 < deriv W x₀) :
    0 < W x₀ := by
  have hx0_nonneg : 0 ≤ W x₀ := (hWrange x₀).1
  by_contra hnot
  have hx0_zero : W x₀ = 0 := le_antisymm (le_of_not_gt hnot) hx0_nonneg
  have hmin_on : IsMinOn W Set.univ x₀ := by
    intro y _
    have hy_nonneg : 0 ≤ W y := (hWrange y).1
    rw [hx0_zero]
    exact hy_nonneg
  have hmin : IsLocalMin W x₀ := hmin_on.isLocalMin univ_mem
  have hzero : deriv W x₀ = 0 := hmin.deriv_eq_zero
  linarith

/-- Construct the Route-A local sign ledger for the paper-expanded wave operator
from the structural smoothness, range, elliptic monotonicity, and elliptic bounds.

No decomposition or sign field is carried: the derivative split is produced by
`HasDerivAt` product/chain rules, and every sign/bound is discharged from the
displayed structural assumptions. -/
def paperWaveOperator_posMax_bookkeeping_of_structural
    {p : CMParams} {c a M BV BV2 : ℝ} {u W : ℝ → ℝ} {x₀ : ℝ}
    (ha : a = -p.χ) (hχ : p.χ ≤ 0)
    (hWreg : ContDiff ℝ 3 W)
    (hVreg : ContDiff ℝ 2 (frozenElliptic p u))
    (hWrange : ∀ x, W x ∈ Set.Icc (0 : ℝ) M)
    (hVderiv_nonpos : ∀ x, deriv (frozenElliptic p u) x ≤ 0)
    (hVbound : ∀ x, |frozenElliptic p u x| ≤ BV)
    (hV2bound : ∀ x, |deriv (deriv (frozenElliptic p u)) x| ≤ BV2)
    (hmax : IsMaxOn (fun x => deriv W x) Set.univ x₀)
    (hqpos : 0 < deriv W x₀) :
    PaperWaveOperatorPosMaxBookkeeping p c a M BV BV2 u W x₀ := by
  have ha_nonneg : 0 ≤ a := by
    rw [ha]
    linarith
  have hWpos : 0 < W x₀ :=
    paperWaveOperator_posMax_value_pos (W := W) (M := M) hWrange hqpos
  have hW_nonneg : 0 ≤ W x₀ := hWpos.le
  have hW_le_M : W x₀ ≤ M := (hWrange x₀).2
  have hM_nonneg : 0 ≤ M := by linarith
  have hqSlope_zero : deriv (deriv W) x₀ = 0 := by
    exact (hmax.isLocalMax univ_mem).deriv_eq_zero
  have hqSecond_nonpos : deriv (deriv (deriv W)) x₀ ≤ 0 := by
    exact deriv_deriv_nonpos_of_isLocalMax (hmax.isLocalMax univ_mem)
      ((hWreg.continuous_deriv (by norm_num)).continuousAt)
  have hW0 : HasDerivAt W (deriv W x₀) x₀ :=
    (hWreg.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hW1 : HasDerivAt (deriv W) (deriv (deriv W) x₀) x₀ := by
    have h := (hWreg.differentiable_iteratedDeriv 1 (by norm_num)).differentiableAt.hasDerivAt
      (x := x₀)
    simpa [iteratedDeriv_one] using h
  have hW2 : HasDerivAt (iteratedDeriv 2 W) (deriv (deriv (deriv W)) x₀) x₀ := by
    have h := (hWreg.differentiable_iteratedDeriv 2 (by norm_num)).differentiableAt.hasDerivAt
      (x := x₀)
    simpa [iteratedDeriv_succ, iteratedDeriv_zero, iteratedDeriv_one] using h
  have hV0 : HasDerivAt (frozenElliptic p u) (deriv (frozenElliptic p u) x₀) x₀ :=
    (hVreg.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hV1 : HasDerivAt (deriv (frozenElliptic p u))
      (deriv (deriv (frozenElliptic p u)) x₀) x₀ := by
    have h := (hVreg.differentiable_iteratedDeriv 1 (by norm_num)).differentiableAt.hasDerivAt
      (x := x₀)
    simpa [iteratedDeriv_one] using h
  refine
    { q := deriv W x₀
      qSlope := deriv (deriv W) x₀
      qSecond := deriv (deriv (deriv W)) x₀
      slopeQuad :=
        a * p.m * (p.m - 1) * (W x₀) ^ (p.m - 2) * (deriv W x₀)^2 *
          deriv (frozenElliptic p u) x₀
      transport :=
        a * p.m * (W x₀) ^ (p.m - 1) * deriv (frozenElliptic p u) x₀ *
          deriv (deriv W) x₀
      vForcing := a * (W x₀) ^ p.m * deriv (frozenElliptic p u) x₀
      diagonal :=
        -a * (p.m + p.γ) * (W x₀) ^ (p.m + p.γ - 1) * deriv W x₀
      reactionCoeff :=
        1 - (W x₀) ^ p.α - p.α * (W x₀ * (W x₀) ^ (p.α - 1))
      v2Coeff :=
        a * p.m * (W x₀) ^ (p.m - 1) *
          deriv (deriv (frozenElliptic p u)) x₀
      vCoeff :=
        a * p.m * (W x₀) ^ (p.m - 1) * frozenElliptic p u x₀
      q_eq := rfl
      paper_deriv := ?_
      qSlope_zero := hqSlope_zero
      qSecond_nonpos := hqSecond_nonpos
      slopeQuad_nonpos := ?_
      transport_zero := ?_
      vForcing_nonpos := ?_
      diagonal_nonpos := ?_
      reactionCoeff_le := ?_
      v2Coeff_le := ?_
      vCoeff_le := ?_ }
  · have hderiv := (paperWaveOperator_hasDerivAt_routeA
      (p := p) (c := c) (a := a) (u := u) (W := W) (x₀ := x₀)
      ha hW0 hW1 hW2 hV0 hV1 hWpos).deriv
    convert hderiv using 1
    ring_nf
  · have hm0 : 0 ≤ p.m := by linarith [p.hm]
    have hm1 : 0 ≤ p.m - 1 := by linarith [p.hm]
    have hpow : 0 ≤ (W x₀) ^ (p.m - 2) := Real.rpow_nonneg hW_nonneg _
    have hq2 : 0 ≤ (deriv W x₀)^2 := sq_nonneg _
    have hcoef :
        0 ≤ a * p.m * (p.m - 1) * (W x₀) ^ (p.m - 2) * (deriv W x₀)^2 := by
      positivity
    exact mul_nonpos_of_nonneg_of_nonpos hcoef (hVderiv_nonpos x₀)
  · rw [hqSlope_zero]
    ring
  · have hpow : 0 ≤ (W x₀) ^ p.m := Real.rpow_nonneg hW_nonneg _
    have hcoef : 0 ≤ a * (W x₀) ^ p.m := by positivity
    exact mul_nonpos_of_nonneg_of_nonpos hcoef (hVderiv_nonpos x₀)
  · have hmg0 : 0 ≤ p.m + p.γ := by linarith [p.hm, p.hγ]
    have hpow : 0 ≤ (W x₀) ^ (p.m + p.γ - 1) := Real.rpow_nonneg hW_nonneg _
    have hcoef :
        0 ≤ a * (p.m + p.γ) * (W x₀) ^ (p.m + p.γ - 1) * deriv W x₀ := by
      positivity
    nlinarith
  · have hα0 : 0 ≤ p.α := by linarith [p.hα]
    have hα1 : 0 ≤ p.α + 1 := by linarith [p.hα]
    have hWα : 0 ≤ (W x₀) ^ p.α := Real.rpow_nonneg hW_nonneg _
    have hWαm1 : 0 ≤ (W x₀) ^ (p.α - 1) := Real.rpow_nonneg hW_nonneg _
    have hprod : 0 ≤ p.α * (W x₀ * (W x₀) ^ (p.α - 1)) := by positivity
    have hMα : 0 ≤ M ^ p.α := Real.rpow_nonneg hM_nonneg _
    unfold reactionLip
    nlinarith
  · have hpow_le :
        (W x₀) ^ (p.m - 1) ≤ M ^ (p.m - 1) :=
      Real.rpow_le_rpow hW_nonneg hW_le_M (by linarith [p.hm])
    have hm0 : 0 ≤ p.m := by linarith [p.hm]
    have hleft_nonneg : 0 ≤ a * p.m := mul_nonneg ha_nonneg hm0
    have hKle :
        a * p.m * (W x₀) ^ (p.m - 1) ≤ a * p.m * M ^ (p.m - 1) :=
      mul_le_mul_of_nonneg_left hpow_le hleft_nonneg
    have hDle : deriv (deriv (frozenElliptic p u)) x₀ ≤ BV2 :=
      le_trans (le_abs_self _) (hV2bound x₀)
    have hBV2_nonneg : 0 ≤ BV2 :=
      le_trans (abs_nonneg _) (hV2bound x₀)
    have hpow_nonneg : 0 ≤ (W x₀) ^ (p.m - 1) := Real.rpow_nonneg hW_nonneg _
    have hcoef_nonneg : 0 ≤ a * p.m * (W x₀) ^ (p.m - 1) := by positivity
    calc
      a * p.m * (W x₀) ^ (p.m - 1) * deriv (deriv (frozenElliptic p u)) x₀
          ≤ a * p.m * (W x₀) ^ (p.m - 1) * BV2 := by
            exact mul_le_mul_of_nonneg_left hDle hcoef_nonneg
      _ ≤ a * p.m * M ^ (p.m - 1) * BV2 := by
            exact mul_le_mul_of_nonneg_right hKle hBV2_nonneg
  · have hpow_le :
        (W x₀) ^ (p.m - 1) ≤ M ^ (p.m - 1) :=
      Real.rpow_le_rpow hW_nonneg hW_le_M (by linarith [p.hm])
    have hm0 : 0 ≤ p.m := by linarith [p.hm]
    have hleft_nonneg : 0 ≤ a * p.m := mul_nonneg ha_nonneg hm0
    have hKle :
        a * p.m * (W x₀) ^ (p.m - 1) ≤ a * p.m * M ^ (p.m - 1) :=
      mul_le_mul_of_nonneg_left hpow_le hleft_nonneg
    have hVle : frozenElliptic p u x₀ ≤ BV :=
      le_trans (le_abs_self _) (hVbound x₀)
    have hBV_nonneg : 0 ≤ BV :=
      le_trans (abs_nonneg _) (hVbound x₀)
    have hpow_nonneg : 0 ≤ (W x₀) ^ (p.m - 1) := Real.rpow_nonneg hW_nonneg _
    have hcoef_nonneg : 0 ≤ a * p.m * (W x₀) ^ (p.m - 1) := by positivity
    calc
      a * p.m * (W x₀) ^ (p.m - 1) * frozenElliptic p u x₀
          ≤ a * p.m * (W x₀) ^ (p.m - 1) * BV := by
            exact mul_le_mul_of_nonneg_left hVle hcoef_nonneg
      _ ≤ a * p.m * M ^ (p.m - 1) * BV := by
            exact mul_le_mul_of_nonneg_right hKle hBV_nonneg

/-- Algebraic core of the paper-expanded derivative estimate at a positive
maximum of `q = W'`.

The single carried equality is the paper expansion of
`deriv (paperWaveOperator p c u W) x₀`.  Everything after that is the
Route-A sign bookkeeping: second derivative nonpositive, first derivative
terms vanish, non-`q` forcing is nonpositive, and the remaining `q` coefficient
is bounded by `Cmono`. -/
theorem paperWaveOperator_deriv_at_pos_max_le_of_quasiMonotone
    {p : CMParams} {c Cmono : ℝ} {u W : ℝ → ℝ} {x₀ : ℝ}
    {q q' q'' forcing coeff : ℝ}
    (hq : q = deriv W x₀)
    (hpaper :
      deriv (fun x => paperWaveOperator p c u W x) x₀ =
        q'' + c * q' + forcing + coeff * q)
    (hqpos : 0 < q)
    (hq'_zero : q' = 0)
    (hq''_nonpos : q'' ≤ 0)
    (hforcing_nonpos : forcing ≤ 0)
    (hcoeff : coeff ≤ Cmono) :
    deriv (fun x => paperWaveOperator p c u W x) x₀
      ≤ Cmono * deriv W x₀ := by
  have hcoeff_mul : coeff * q ≤ Cmono * q :=
    mul_le_mul_of_nonneg_right hcoeff hqpos.le
  rw [hpaper, hq'_zero, ← hq]
  nlinarith

/-- Paper-expanded version of the previous estimate.

The differentiated paper operator is grouped as follows at a positive maximum
of `q = W'`:

* `q''` is nonpositive and `q'` vanishes;
* the transport/good forcing/diagonal terms are nonpositive;
* the only possibly positive terms are proportional to `q`, with coefficients
  bounded by the displayed `paperCmono`.

This is the Route-A Step-C sign ledger for the expanded diagonal
`a W^m (V - W^γ)`: the `V'` forcing and diagonal contribution are good, while
`reaction`, `V''`, and `V` are absorbed into `Cmono`. -/
theorem paperWaveOperator_deriv_at_pos_max_le_of_expanded_terms
    {p : CMParams} {c a M BV BV2 Cmono : ℝ} {u W : ℝ → ℝ} {x₀ : ℝ}
    {q q' q'' goodSlope goodTransport goodForcing goodDiagonal : ℝ}
    {reactionCoeff v2Coeff vCoeff : ℝ}
    (hq : q = deriv W x₀)
    (hpaper :
      deriv (fun x => paperWaveOperator p c u W x) x₀ =
        q'' + c * q' + goodSlope + goodTransport + goodForcing + goodDiagonal
          + (reactionCoeff + v2Coeff + vCoeff) * q)
    (hqpos : 0 < q)
    (hq'_zero : q' = 0)
    (hq''_nonpos : q'' ≤ 0)
    (hgoodSlope : goodSlope ≤ 0)
    (hgoodTransport : goodTransport ≤ 0)
    (hgoodForcing : goodForcing ≤ 0)
    (hgoodDiagonal : goodDiagonal ≤ 0)
    (hreaction : reactionCoeff ≤ reactionLip p.α M)
    (hV2 : v2Coeff ≤ a * p.m * M ^ (p.m - 1) * BV2)
    (hV : vCoeff ≤ a * p.m * M ^ (p.m - 1) * BV)
    (hCmono : paperCmono p a M BV BV2 ≤ Cmono) :
    deriv (fun x => paperWaveOperator p c u W x) x₀
      ≤ Cmono * deriv W x₀ := by
  refine paperWaveOperator_deriv_at_pos_max_le_of_quasiMonotone
    (p := p) (c := c) (Cmono := Cmono) (u := u) (W := W) (x₀ := x₀)
    (q := q) (q' := q') (q'' := q'')
    (forcing := goodSlope + goodTransport + goodForcing + goodDiagonal)
    (coeff := reactionCoeff + v2Coeff + vCoeff)
    hq ?_ hqpos hq'_zero hq''_nonpos ?_ ?_
  · simpa [add_assoc] using hpaper
  · nlinarith
  · unfold paperCmono at hCmono
    nlinarith

/-- Error-tolerant algebraic ledger at a penalized positive maximum of
`q = W'`.  The exact maximum identities `q' = 0`, `q'' ≤ 0`, and vanishing
transport are replaced by errors of size `eta`. -/
theorem paperWaveOperator_deriv_at_approx_pos_max_le_of_expanded_terms
    {p : CMParams} {c a M BV BV2 BVd Cmono eta : ℝ}
    {u W : ℝ → ℝ} {x₀ : ℝ}
    {q q' q'' goodSlope goodTransport goodForcing goodDiagonal : ℝ}
    {reactionCoeff v2Coeff vCoeff : ℝ}
    (hq : q = deriv W x₀)
    (hpaper :
      deriv (fun x => paperWaveOperator p c u W x) x₀ =
        q'' + c * q' + goodSlope + goodTransport + goodForcing + goodDiagonal
          + (reactionCoeff + v2Coeff + vCoeff) * q)
    (hqpos : 0 < q)
    (hq'_abs : |q'| ≤ eta)
    (hq''_le : q'' ≤ eta)
    (hgoodSlope : goodSlope ≤ 0)
    (hgoodTransport : goodTransport ≤
      a * p.m * M ^ (p.m - 1) * BVd * eta)
    (hgoodForcing : goodForcing ≤ 0)
    (hgoodDiagonal : goodDiagonal ≤ 0)
    (hreaction : reactionCoeff ≤ reactionLip p.α M)
    (hV2 : v2Coeff ≤ a * p.m * M ^ (p.m - 1) * BV2)
    (hV : vCoeff ≤ a * p.m * M ^ (p.m - 1) * BV)
    (hCmono : paperCmono p a M BV BV2 ≤ Cmono) :
    deriv (fun x => paperWaveOperator p c u W x) x₀ ≤
      Cmono * deriv W x₀ +
        (1 + |c| + a * p.m * M ^ (p.m - 1) * BVd) * eta := by
  have hcq : c * q' ≤ |c| * eta := by
    calc
      c * q' ≤ |c * q'| := le_abs_self _
      _ = |c| * |q'| := abs_mul _ _
      _ ≤ |c| * eta :=
        mul_le_mul_of_nonneg_left hq'_abs (abs_nonneg c)
  have hcoeff :
      reactionCoeff + v2Coeff + vCoeff ≤ Cmono := by
    unfold paperCmono at hCmono
    linarith
  have hcoeff_mul :
      (reactionCoeff + v2Coeff + vCoeff) * q ≤ Cmono * q :=
    mul_le_mul_of_nonneg_right hcoeff hqpos.le
  rw [hpaper, ← hq]
  nlinarith

/-- Structural realization of the approximate Route-A ledger. -/
theorem paperWaveOperator_deriv_at_approx_pos_max_le_of_structural
    {p : CMParams} {c a M BV BV2 BVd Cmono eta : ℝ}
    {u W : ℝ → ℝ} {x₀ : ℝ}
    (ha : a = -p.χ) (hχ : p.χ ≤ 0)
    (hWreg : ContDiff ℝ 3 W)
    (hVreg : ContDiff ℝ 2 (frozenElliptic p u))
    (hWrange : ∀ x, W x ∈ Set.Icc (0 : ℝ) M)
    (hVderiv_nonpos : ∀ x, deriv (frozenElliptic p u) x ≤ 0)
    (hVderiv_bound : ∀ x, |deriv (frozenElliptic p u) x| ≤ BVd)
    (hVbound : ∀ x, |frozenElliptic p u x| ≤ BV)
    (hV2bound : ∀ x, |deriv (deriv (frozenElliptic p u)) x| ≤ BV2)
    (hBVd : 0 ≤ BVd) (heta : 0 < eta)
    (hqpos : 0 < deriv W x₀)
    (hqSlope : |deriv (deriv W) x₀| < eta)
    (hqSecond : deriv (deriv (deriv W)) x₀ < eta)
    (hCmono : paperCmono p a M BV BV2 ≤ Cmono) :
    deriv (fun x => paperWaveOperator p c u W x) x₀ ≤
      Cmono * deriv W x₀ +
        (1 + |c| + a * p.m * M ^ (p.m - 1) * BVd) * eta := by
  have ha_nonneg : 0 ≤ a := by
    rw [ha]
    linarith
  have hWpos : 0 < W x₀ :=
    paperWaveOperator_posMax_value_pos (W := W) (M := M) hWrange hqpos
  have hW_nonneg : 0 ≤ W x₀ := hWpos.le
  have hW_le_M : W x₀ ≤ M := (hWrange x₀).2
  have hM_nonneg : 0 ≤ M := le_trans hW_nonneg hW_le_M
  have hW0 : HasDerivAt W (deriv W x₀) x₀ :=
    (hWreg.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hW1 : HasDerivAt (deriv W) (deriv (deriv W) x₀) x₀ := by
    have h := (hWreg.differentiable_iteratedDeriv 1 (by norm_num)).differentiableAt.hasDerivAt
      (x := x₀)
    simpa [iteratedDeriv_one] using h
  have hW2 : HasDerivAt (iteratedDeriv 2 W)
      (deriv (deriv (deriv W)) x₀) x₀ := by
    have h := (hWreg.differentiable_iteratedDeriv 2 (by norm_num)).differentiableAt.hasDerivAt
      (x := x₀)
    simpa [iteratedDeriv_succ, iteratedDeriv_zero, iteratedDeriv_one] using h
  have hV0 : HasDerivAt (frozenElliptic p u)
      (deriv (frozenElliptic p u) x₀) x₀ :=
    (hVreg.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hV1 : HasDerivAt (deriv (frozenElliptic p u))
      (deriv (deriv (frozenElliptic p u)) x₀) x₀ := by
    have h := (hVreg.differentiable_iteratedDeriv 1 (by norm_num)).differentiableAt.hasDerivAt
      (x := x₀)
    simpa [iteratedDeriv_one] using h
  let slopeQuad : ℝ :=
    a * p.m * (p.m - 1) * (W x₀) ^ (p.m - 2) * (deriv W x₀)^2 *
      deriv (frozenElliptic p u) x₀
  let transport : ℝ :=
    a * p.m * (W x₀) ^ (p.m - 1) * deriv (frozenElliptic p u) x₀ *
      deriv (deriv W) x₀
  let vForcing : ℝ :=
    a * (W x₀) ^ p.m * deriv (frozenElliptic p u) x₀
  let diagonal : ℝ :=
    -a * (p.m + p.γ) * (W x₀) ^ (p.m + p.γ - 1) * deriv W x₀
  let reactionCoeff : ℝ :=
    1 - (W x₀) ^ p.α - p.α * (W x₀ * (W x₀) ^ (p.α - 1))
  let v2Coeff : ℝ :=
    a * p.m * (W x₀) ^ (p.m - 1) *
      deriv (deriv (frozenElliptic p u)) x₀
  let vCoeff : ℝ :=
    a * p.m * (W x₀) ^ (p.m - 1) * frozenElliptic p u x₀
  have hpaper :
      deriv (fun x => paperWaveOperator p c u W x) x₀ =
        deriv (deriv (deriv W)) x₀ + c * deriv (deriv W) x₀ +
          slopeQuad + transport + vForcing + diagonal +
          (reactionCoeff + v2Coeff + vCoeff) * deriv W x₀ := by
    have hderiv := (paperWaveOperator_hasDerivAt_routeA
      (p := p) (c := c) (a := a) (u := u) (W := W) (x₀ := x₀)
      ha hW0 hW1 hW2 hV0 hV1 hWpos).deriv
    dsimp [slopeQuad, transport, vForcing, diagonal, reactionCoeff,
      v2Coeff, vCoeff]
    convert hderiv using 1 <;> ring_nf
  have hslope : slopeQuad ≤ 0 := by
    have hm0 : 0 ≤ p.m := by linarith [p.hm]
    have hm1 : 0 ≤ p.m - 1 := by linarith [p.hm]
    have hpow : 0 ≤ (W x₀) ^ (p.m - 2) := Real.rpow_nonneg hW_nonneg _
    have hq2 : 0 ≤ (deriv W x₀)^2 := sq_nonneg _
    have hcoef :
        0 ≤ a * p.m * (p.m - 1) * (W x₀) ^ (p.m - 2) *
          (deriv W x₀)^2 := by positivity
    dsimp [slopeQuad]
    exact mul_nonpos_of_nonneg_of_nonpos hcoef (hVderiv_nonpos x₀)
  have hpow_le :
      (W x₀) ^ (p.m - 1) ≤ M ^ (p.m - 1) :=
    Real.rpow_le_rpow hW_nonneg hW_le_M (sub_nonneg.mpr p.hm)
  have hm0 : 0 ≤ p.m := by linarith [p.hm]
  have hleft_nonneg : 0 ≤ a * p.m := mul_nonneg ha_nonneg hm0
  have hcoef_nonneg : 0 ≤ a * p.m * (W x₀) ^ (p.m - 1) := by positivity
  have hcoefM_nonneg : 0 ≤ a * p.m * M ^ (p.m - 1) := by positivity
  have hcoef_le :
      a * p.m * (W x₀) ^ (p.m - 1) ≤
        a * p.m * M ^ (p.m - 1) :=
    mul_le_mul_of_nonneg_left hpow_le hleft_nonneg
  have htransport : transport ≤
      a * p.m * M ^ (p.m - 1) * BVd * eta := by
    have hPV :
        a * p.m * (W x₀) ^ (p.m - 1) *
            |deriv (frozenElliptic p u) x₀| ≤
          a * p.m * M ^ (p.m - 1) * BVd :=
      mul_le_mul hcoef_le (hVderiv_bound x₀)
        (abs_nonneg _) hcoefM_nonneg
    have hprod :
        |a * p.m * (W x₀) ^ (p.m - 1) *
            deriv (frozenElliptic p u) x₀ * deriv (deriv W) x₀| ≤
          a * p.m * M ^ (p.m - 1) * BVd * eta := by
      rw [abs_mul, abs_mul, abs_of_nonneg hcoef_nonneg]
      exact mul_le_mul hPV hqSlope.le (abs_nonneg _)
        (mul_nonneg hcoefM_nonneg hBVd)
    exact (le_abs_self transport).trans (by simpa [transport] using hprod)
  have hvForcing : vForcing ≤ 0 := by
    have hpow : 0 ≤ (W x₀) ^ p.m := Real.rpow_nonneg hW_nonneg _
    have hcoef : 0 ≤ a * (W x₀) ^ p.m := by positivity
    dsimp [vForcing]
    exact mul_nonpos_of_nonneg_of_nonpos hcoef (hVderiv_nonpos x₀)
  have hdiagonal : diagonal ≤ 0 := by
    have hpow : 0 ≤ (W x₀) ^ (p.m + p.γ - 1) :=
      Real.rpow_nonneg hW_nonneg _
    have hcoef :
        0 ≤ a * (p.m + p.γ) * (W x₀) ^ (p.m + p.γ - 1) *
          deriv W x₀ := by
      have hmg : 0 ≤ p.m + p.γ := by linarith [p.hm, p.hγ]
      exact mul_nonneg
        (mul_nonneg (mul_nonneg ha_nonneg hmg) hpow) hqpos.le
    dsimp [diagonal]
    nlinarith
  have hreaction : reactionCoeff ≤ reactionLip p.α M := by
    have hWα : 0 ≤ (W x₀) ^ p.α := Real.rpow_nonneg hW_nonneg _
    have hWαm1 : 0 ≤ (W x₀) ^ (p.α - 1) := Real.rpow_nonneg hW_nonneg _
    have hα0 : 0 ≤ p.α := le_trans zero_le_one p.hα
    have hprod : 0 ≤ p.α * (W x₀ * (W x₀) ^ (p.α - 1)) :=
      mul_nonneg hα0 (mul_nonneg hW_nonneg hWαm1)
    have hMα : 0 ≤ M ^ p.α := Real.rpow_nonneg hM_nonneg _
    have hαplus : 0 ≤ p.α + 1 := by linarith [p.hα]
    have hMterm : 0 ≤ (p.α + 1) * M ^ p.α :=
      mul_nonneg hαplus hMα
    dsimp [reactionCoeff]
    unfold reactionLip
    nlinarith [hWα, hprod, hMterm]
  have hv2 : v2Coeff ≤ a * p.m * M ^ (p.m - 1) * BV2 := by
    have hDle : deriv (deriv (frozenElliptic p u)) x₀ ≤ BV2 :=
      le_trans (le_abs_self _) (hV2bound x₀)
    have hBV2_nonneg : 0 ≤ BV2 :=
      le_trans (abs_nonneg _) (hV2bound x₀)
    dsimp [v2Coeff]
    calc
      a * p.m * (W x₀) ^ (p.m - 1) *
          deriv (deriv (frozenElliptic p u)) x₀
          ≤ a * p.m * (W x₀) ^ (p.m - 1) * BV2 :=
        mul_le_mul_of_nonneg_left hDle hcoef_nonneg
      _ ≤ a * p.m * M ^ (p.m - 1) * BV2 :=
        mul_le_mul_of_nonneg_right hcoef_le hBV2_nonneg
  have hv : vCoeff ≤ a * p.m * M ^ (p.m - 1) * BV := by
    have hVle : frozenElliptic p u x₀ ≤ BV :=
      le_trans (le_abs_self _) (hVbound x₀)
    have hBV_nonneg : 0 ≤ BV := le_trans (abs_nonneg _) (hVbound x₀)
    dsimp [vCoeff]
    calc
      a * p.m * (W x₀) ^ (p.m - 1) * frozenElliptic p u x₀
          ≤ a * p.m * (W x₀) ^ (p.m - 1) * BV :=
        mul_le_mul_of_nonneg_left hVle hcoef_nonneg
      _ ≤ a * p.m * M ^ (p.m - 1) * BV :=
        mul_le_mul_of_nonneg_right hcoef_le hBV_nonneg
  exact paperWaveOperator_deriv_at_approx_pos_max_le_of_expanded_terms
    (p := p) (c := c) (a := a) (M := M) (BV := BV) (BV2 := BV2)
    (BVd := BVd) (Cmono := Cmono) (eta := eta)
    (u := u) (W := W) (x₀ := x₀)
    (q := deriv W x₀) (q' := deriv (deriv W) x₀)
    (q'' := deriv (deriv (deriv W)) x₀)
    (goodSlope := slopeQuad) (goodTransport := transport)
    (goodForcing := vForcing) (goodDiagonal := diagonal)
    (reactionCoeff := reactionCoeff) (v2Coeff := v2Coeff) (vCoeff := vCoeff)
    rfl hpaper hqpos hqSlope.le hqSecond.le hslope htransport
    hvForcing hdiagonal hreaction hv2 hv hCmono

/-- Tail-free differentiated maximum principle.  Boundedness of `q` replaces
both endpoint limits: a positive value produces penalized almost-maxima, while
the strict gap `Cmono < λ` absorbs their derivative errors. -/
theorem smooth_paperStep_deriv_nonpos_of_quasiMonotone_tailfree
    {p : CMParams} {c lam Cmono E Q : ℝ} {u Z W : ℝ → ℝ}
    (hlam : 0 < lam)
    (hsmall : (1 / lam) * Cmono < 1)
    (hE : 0 ≤ E)
    (hstep_deriv : ∀ x,
      deriv W x - (1 / lam) *
          deriv (fun y => paperWaveOperator p c u W y) x = deriv Z x)
    (hZderiv : ∀ x, deriv Z x ≤ 0)
    (hq2 : ContDiff ℝ 2 (fun x => deriv W x))
    (hqbound : ∀ x, |deriv W x| ≤ Q)
    (hmono_approx : ∀ eta, 0 < eta → ∀ x₀,
      0 < deriv W x₀ →
      |deriv (deriv W) x₀| < eta →
      deriv (deriv (deriv W)) x₀ < eta →
      deriv (fun x => paperWaveOperator p c u W x) x₀ ≤
        Cmono * deriv W x₀ + E * eta) :
    ∀ x, deriv W x ≤ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x₁, hx₁⟩ := hcon
  have hClam : Cmono < lam := by
    have hmul := mul_lt_mul_of_pos_left hsmall hlam
    have hlamne : lam ≠ 0 := ne_of_gt hlam
    field_simp [hlamne] at hmul
    linarith
  let eta : ℝ := (lam - Cmono) * deriv W x₁ / (4 * (E + 1))
  have heta : 0 < eta := by
    dsimp [eta]
    exact div_pos (mul_pos (sub_pos.mpr hClam) hx₁)
      (mul_pos (by norm_num) (by linarith))
  obtain ⟨x₀, hqvalue, hqSlope, hqSecond⟩ :=
    exists_approx_positive_max_deriv_data
      (f := fun x => deriv W x) (A := Q) (eta := eta) (x₁ := x₁)
      hq2 hqbound hx₁ heta
  have hqpos : 0 < deriv W x₀ := by
    linarith
  have hA := hmono_approx eta heta x₀ hqpos hqSlope hqSecond
  have hstep₀ := hstep_deriv x₀
  have hA_lower : lam * deriv W x₀ ≤
      deriv (fun x => paperWaveOperator p c u W x) x₀ := by
    have hdiv : deriv W x₀ ≤
        (1 / lam) * deriv (fun x => paperWaveOperator p c u W x) x₀ := by
      linarith [hZderiv x₀]
    have hmul := mul_le_mul_of_nonneg_left hdiv hlam.le
    have hlamne : lam ≠ 0 := ne_of_gt hlam
    calc
      lam * deriv W x₀ ≤ lam * ((1 / lam) *
          deriv (fun x => paperWaveOperator p c u W x) x₀) := hmul
      _ = deriv (fun x => paperWaveOperator p c u W x) x₀ := by
        field_simp [hlamne]
  have hEeta : E * eta < (lam - Cmono) * deriv W x₁ / 4 := by
    dsimp [eta]
    have hE1 : E < E + 1 := by linarith
    have hbase : 0 < (lam - Cmono) * deriv W x₁ :=
      mul_pos (sub_pos.mpr hClam) hx₁
    have hden : 0 < 4 * (E + 1) :=
      mul_pos (by norm_num) (by linarith)
    have hscaled : E * ((lam - Cmono) * deriv W x₁) <
        (E + 1) * ((lam - Cmono) * deriv W x₁) :=
      mul_lt_mul_of_pos_right hE1 hbase
    calc
      E * ((lam - Cmono) * deriv W x₁ / (4 * (E + 1))) =
          (E * ((lam - Cmono) * deriv W x₁)) / (4 * (E + 1)) := by ring
      _ < ((E + 1) * ((lam - Cmono) * deriv W x₁)) /
          (4 * (E + 1)) := (div_lt_div_iff_of_pos_right hden).2 hscaled
      _ = (lam - Cmono) * deriv W x₁ / 4 := by
        field_simp [ne_of_gt (show 0 < E + 1 by linarith)]
  have hqscaled :
      (lam - Cmono) * (deriv W x₁ / 2) <
        (lam - Cmono) * deriv W x₀ :=
    mul_lt_mul_of_pos_left hqvalue (sub_pos.mpr hClam)
  have hgap_le :
      (lam - Cmono) * deriv W x₀ ≤ E * eta := by
    linarith [hA_lower, hA]
  have hbase : 0 < (lam - Cmono) * deriv W x₁ :=
    mul_pos (sub_pos.mpr hClam) hx₁
  have hquarter :
      (lam - Cmono) * deriv W x₁ / 4 <
        (lam - Cmono) * (deriv W x₁ / 2) := by
    calc
      (lam - Cmono) * deriv W x₁ / 4 <
          (lam - Cmono) * deriv W x₁ / 2 := by linarith
      _ = (lam - Cmono) * (deriv W x₁ / 2) := by ring
  exact (not_lt_of_ge hgap_le)
    (lt_trans (lt_trans hEeta hquarter) hqscaled)

/-- The Route-A bookkeeping discharges the local operator-derivative estimate:
at a positive maximum of `q = W'`, the differentiated paper operator is bounded
above by `Cmono * q`. -/
theorem paperWaveOperator_deriv_at_pos_max_le_of_bookkeeping
    {p : CMParams} {c a M BV BV2 Cmono : ℝ} {u W : ℝ → ℝ} {x₀ : ℝ}
    (hCmono : paperCmono p a M BV BV2 ≤ Cmono)
    (hb : PaperWaveOperatorPosMaxBookkeeping p c a M BV BV2 u W x₀)
    (hqpos : 0 < deriv W x₀) :
    deriv (fun x => paperWaveOperator p c u W x) x₀
      ≤ Cmono * deriv W x₀ := by
  have hbqpos : 0 < hb.q := by
    rw [hb.q_eq]
    exact hqpos
  have htransport : hb.transport ≤ 0 := by
    rw [hb.transport_zero]
  exact paperWaveOperator_deriv_at_pos_max_le_of_expanded_terms
    (p := p) (c := c) (a := a) (M := M) (BV := BV) (BV2 := BV2)
    (Cmono := Cmono) (u := u) (W := W) (x₀ := x₀)
    (q := hb.q) (q' := hb.qSlope) (q'' := hb.qSecond)
    (goodSlope := hb.slopeQuad) (goodTransport := hb.transport)
    (goodForcing := hb.vForcing) (goodDiagonal := hb.diagonal)
    (reactionCoeff := hb.reactionCoeff) (v2Coeff := hb.v2Coeff)
    (vCoeff := hb.vCoeff)
    hb.q_eq hb.paper_deriv hbqpos hb.qSlope_zero hb.qSecond_nonpos
    hb.slopeQuad_nonpos htransport hb.vForcing_nonpos hb.diagonal_nonpos
    hb.reactionCoeff_le hb.v2Coeff_le hb.vCoeff_le hCmono

/-- Differentiated paper step maximum principle.  If `q = W'` had a positive
global maximum, the differentiated step equation
`q - (1/λ) A'(W) = Z'` would contradict `Z' ≤ 0` and
`(1/λ) Cmono < 1`. -/
theorem smooth_paperStep_deriv_nonpos_of_quasiMonotone
    {p : CMParams} {c lam Cmono : ℝ} {u Z W : ℝ → ℝ}
    {La Lb : ℝ}
    (hlam : 0 < lam)
    (hsmall : (1 / lam) * Cmono < 1)
    (hstep_deriv : ∀ x,
      deriv W x - (1 / lam) *
          deriv (fun y => paperWaveOperator p c u W y) x = deriv Z x)
    (hZderiv : ∀ x, deriv Z x ≤ 0)
    (hqcont : Continuous (fun x => deriv W x))
    (hbot : Tendsto (fun x => deriv W x) atBot (𝓝 La)) (hLa : La ≤ 0)
    (htop : Tendsto (fun x => deriv W x) atTop (𝓝 Lb)) (hLb : Lb ≤ 0)
    (hmono_bound : ∀ x₀,
      IsMaxOn (fun x => deriv W x) Set.univ x₀ →
        0 < deriv W x₀ →
          deriv (fun x => paperWaveOperator p c u W x) x₀
            ≤ Cmono * deriv W x₀) :
    ∀ x, deriv W x ≤ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x₁, hx₁⟩ := hcon
  obtain ⟨x₀, hmax, hqpos⟩ :=
    exists_isMaxOn_pos_of_tendsto_nonpos (φ := fun x => deriv W x)
      hqcont hbot hLa htop hLb hx₁
  have hA := hmono_bound x₀ hmax hqpos
  have hmul :
      (1 / lam) * deriv (fun y => paperWaveOperator p c u W y) x₀
        ≤ (1 / lam) * (Cmono * deriv W x₀) :=
    mul_le_mul_of_nonneg_left hA (one_div_pos.mpr hlam).le
  have hleft_nonpos :
      deriv W x₀ - (1 / lam) *
          deriv (fun y => paperWaveOperator p c u W y) x₀ ≤ 0 := by
    have hz := hZderiv x₀
    have hs := hstep_deriv x₀
    linarith
  have hlower :
      deriv W x₀ - (1 / lam) * (Cmono * deriv W x₀)
        ≤ deriv W x₀ - (1 / lam) *
          deriv (fun y => paperWaveOperator p c u W y) x₀ := by
    linarith
  have hcoef_pos : 0 < 1 - (1 / lam) * Cmono := by
    linarith
  have hstrict :
      0 < deriv W x₀ - (1 / lam) * (Cmono * deriv W x₀) := by
    nlinarith [mul_pos hcoef_pos hqpos]
  linarith

/-- Smooth paper-expanded implicit steps preserve antitonicity once the
differentiated quasi-monotone maximum estimate is supplied. -/
theorem smooth_paperStep_preserves_antitone_of_quasiMonotone
    {p : CMParams} {c lam Cmono : ℝ} {u Z W : ℝ → ℝ}
    {La Lb : ℝ}
    (hlam : 0 < lam)
    (hsmall : (1 / lam) * Cmono < 1)
    (hWdiff : Differentiable ℝ W)
    (hstep_deriv : ∀ x,
      deriv W x - (1 / lam) *
          deriv (fun y => paperWaveOperator p c u W y) x = deriv Z x)
    (hZderiv : ∀ x, deriv Z x ≤ 0)
    (hqcont : Continuous (fun x => deriv W x))
    (hbot : Tendsto (fun x => deriv W x) atBot (𝓝 La)) (hLa : La ≤ 0)
    (htop : Tendsto (fun x => deriv W x) atTop (𝓝 Lb)) (hLb : Lb ≤ 0)
    (hmono_bound : ∀ x₀,
      IsMaxOn (fun x => deriv W x) Set.univ x₀ →
        0 < deriv W x₀ →
          deriv (fun x => paperWaveOperator p c u W x) x₀
            ≤ Cmono * deriv W x₀) :
    Antitone W := by
  exact antitone_of_deriv_nonpos hWdiff
    (smooth_paperStep_deriv_nonpos_of_quasiMonotone
      (p := p) (c := c) (lam := lam) (Cmono := Cmono)
      (u := u) (Z := Z) (W := W) (La := La) (Lb := Lb)
      hlam hsmall hstep_deriv hZderiv hqcont hbot hLa htop hLb hmono_bound)

/-! ## Route-A paper producer interface, without shifted sliding data -/

/-- Route-A antitonicity data for one smooth paper-expanded step.

This replaces `PaperStepAntitoneData`: no shifted comparison residual is carried.
The data are exactly the differentiated step equation, the mollified-source
derivative sign, the derivative tails, and the local expanded sign ledger for
the differentiated paper operator. -/
structure PaperStepRouteAData
    (p : CMParams) (c lam Cmono : ℝ) (u Z W : ℝ → ℝ) where
  hsmall : (1 / lam) * Cmono < 1
  step_deriv : ∀ x,
    deriv W x - (1 / lam) *
        deriv (fun y => paperWaveOperator p c u W y) x = deriv Z x
  Z_deriv_nonpos : ∀ x, deriv Z x ≤ 0
  q_cont : Continuous (fun x => deriv W x)
  La : ℝ
  Lb : ℝ
  hbot : Tendsto (fun x => deriv W x) atBot (𝓝 La)
  hLa : La ≤ 0
  htop : Tendsto (fun x => deriv W x) atTop (𝓝 Lb)
  hLb : Lb ≤ 0
  a : ℝ
  M : ℝ
  BV : ℝ
  BV2 : ℝ
  Cmono_bound : paperCmono p a M BV BV2 ≤ Cmono
  bookkeeping : ∀ x₀,
    IsMaxOn (fun x => deriv W x) Set.univ x₀ →
      0 < deriv W x₀ →
        PaperWaveOperatorPosMaxBookkeeping p c a M BV BV2 u W x₀

/-- Structural producer for the Route-A derivative maximum-principle data.

The local bookkeeping field is constructed by
`paperWaveOperator_posMax_bookkeeping_of_structural`, so callers provide only
smoothness, range, elliptic monotonicity/bounds, the differentiated step equation,
source derivative sign, tails, and the scalar smallness bound. -/
def paperStepRouteAData_of_structural
    {p : CMParams} {c lam Cmono a M BV BV2 : ℝ} {u Z W : ℝ → ℝ}
    {La Lb : ℝ}
    (ha : a = -p.χ) (hχ : p.χ ≤ 0)
    (hWreg : ContDiff ℝ 3 W)
    (hVreg : ContDiff ℝ 2 (frozenElliptic p u))
    (hWrange : ∀ x, W x ∈ Set.Icc (0 : ℝ) M)
    (hVderiv_nonpos : ∀ x, deriv (frozenElliptic p u) x ≤ 0)
    (hVbound : ∀ x, |frozenElliptic p u x| ≤ BV)
    (hV2bound : ∀ x, |deriv (deriv (frozenElliptic p u)) x| ≤ BV2)
    (hsmall : (1 / lam) * Cmono < 1)
    (hstep_deriv : ∀ x,
      deriv W x - (1 / lam) *
          deriv (fun y => paperWaveOperator p c u W y) x = deriv Z x)
    (hZderiv : ∀ x, deriv Z x ≤ 0)
    (hbot : Tendsto (fun x => deriv W x) atBot (𝓝 La)) (hLa : La ≤ 0)
    (htop : Tendsto (fun x => deriv W x) atTop (𝓝 Lb)) (hLb : Lb ≤ 0)
    (hCmono : paperCmono p a M BV BV2 ≤ Cmono) :
    PaperStepRouteAData p c lam Cmono u Z W where
  hsmall := hsmall
  step_deriv := hstep_deriv
  Z_deriv_nonpos := hZderiv
  q_cont := hWreg.continuous_deriv (by norm_num)
  La := La
  Lb := Lb
  hbot := hbot
  hLa := hLa
  htop := htop
  hLb := hLb
  a := a
  M := M
  BV := BV
  BV2 := BV2
  Cmono_bound := hCmono
  bookkeeping := fun x₀ hmax hqpos =>
    paperWaveOperator_posMax_bookkeeping_of_structural
      (p := p) (c := c) (a := a) (M := M) (BV := BV) (BV2 := BV2)
      (u := u) (W := W) (x₀ := x₀)
      ha hχ hWreg hVreg hWrange hVderiv_nonpos hVbound hV2bound hmax hqpos

/-- Structural Route-A input with the differentiated step equation removed.

The producer obtains `step_deriv` by differentiating the implicit step equation
with `paperStep_stepDeriv_of_implicit`.  This structure deliberately does not
carry `C³ W` or derivative tails for the raw step; those data belong only to
smooth approximants. -/
structure PaperStepRouteAStructuralData
    (p : CMParams) (c lam Cmono : ℝ) (u Z W : ℝ → ℝ) where
  hsmall : (1 / lam) * Cmono < 1
  a : ℝ
  M : ℝ
  BV : ℝ
  BV2 : ℝ
  ha : a = -p.χ
  hχ : p.χ ≤ 0
  V_reg : ContDiff ℝ 2 (frozenElliptic p u)
  V_deriv_nonpos : ∀ x, deriv (frozenElliptic p u) x ≤ 0
  V_deriv_bound : ∀ x, |deriv (frozenElliptic p u) x| ≤ BV
  V_bound : ∀ x, |frozenElliptic p u x| ≤ BV
  V2_bound : ∀ x, |deriv (deriv (frozenElliptic p u)) x| ≤ BV2
  Cmono_bound : paperCmono p a M BV BV2 ≤ Cmono

/-- Fill the older Route-A data record from structural data and the implicit
step equation. -/
def PaperStepRouteAStructuralData.toRouteAData
    {p : CMParams} {c lam Cmono : ℝ} {u Z W : ℝ → ℝ}
    (hd : PaperStepRouteAStructuralData p c lam Cmono u Z W)
    {La Lb : ℝ}
    (hWreg : ContDiff ℝ 3 W)
    (hwave : Differentiable ℝ (fun y => paperWaveOperator p c u W y))
    (hWrange : ∀ x, W x ∈ Set.Icc (0 : ℝ) hd.M)
    (hstep : ∀ x, paperImplicitStepOp p c (1 / lam) u W x = Z x)
    (hZderiv : ∀ x, deriv Z x ≤ 0)
    (hbot : Tendsto (fun x => deriv W x) atBot (𝓝 La)) (hLa : La ≤ 0)
    (htop : Tendsto (fun x => deriv W x) atTop (𝓝 Lb)) (hLb : Lb ≤ 0) :
    PaperStepRouteAData p c lam Cmono u Z W :=
  paperStepRouteAData_of_structural
    (p := p) (c := c) (lam := lam) (Cmono := Cmono)
    (a := hd.a) (M := hd.M) (BV := hd.BV) (BV2 := hd.BV2)
    (u := u) (Z := Z) (W := W) (La := La) (Lb := Lb)
    hd.ha hd.hχ hWreg hd.V_reg hWrange hd.V_deriv_nonpos
    hd.V_bound hd.V2_bound hd.hsmall
    (paperStep_stepDeriv_of_implicit
      (p := p) (c := c) (lam := lam) (u := u) (Z := Z) (W := W)
      hstep (hWreg.differentiable (by norm_num)) hwave)
    hZderiv hbot hLa htop hLb hd.Cmono_bound

/-- One smooth paper step is antitone from Route-A derivative data. -/
theorem paperStep_antitone_by_routeA
    {p : CMParams} {c lam Cmono : ℝ} {u Z W : ℝ → ℝ}
    (hlam : 0 < lam)
    (hWdiff : Differentiable ℝ W)
    (hd : PaperStepRouteAData p c lam Cmono u Z W) :
    Antitone W := by
  have hmono : ∀ x₀,
      IsMaxOn (fun x => deriv W x) Set.univ x₀ →
        0 < deriv W x₀ →
          deriv (fun x => paperWaveOperator p c u W x) x₀
            ≤ Cmono * deriv W x₀ := by
    intro x₀ hxmax hqpos
    exact paperWaveOperator_deriv_at_pos_max_le_of_bookkeeping
      (p := p) (c := c) (a := hd.a) (M := hd.M) (BV := hd.BV)
      (BV2 := hd.BV2) (Cmono := Cmono) (u := u) (W := W) (x₀ := x₀)
      hd.Cmono_bound (hd.bookkeeping x₀ hxmax hqpos) hqpos
  exact smooth_paperStep_preserves_antitone_of_quasiMonotone
    (p := p) (c := c) (lam := lam) (Cmono := Cmono)
    (u := u) (Z := Z) (W := W) (La := hd.La) (Lb := hd.Lb)
    hlam hd.hsmall hWdiff hd.step_deriv hd.Z_deriv_nonpos
    hd.q_cont hd.hbot hd.hLa hd.htop hd.hLb hmono

/-- Smooth paper-expanded implicit steps preserve antitonicity from structural
Route-A hypotheses alone: no local sign ledger or derivative decomposition is
carried by the caller. -/
theorem paperStep_antitone_by_routeA_of_structural
    {p : CMParams} {c lam Cmono a M BV BV2 : ℝ} {u Z W : ℝ → ℝ}
    {La Lb : ℝ}
    (hlam : 0 < lam)
    (ha : a = -p.χ) (hχ : p.χ ≤ 0)
    (hWreg : ContDiff ℝ 3 W)
    (hVreg : ContDiff ℝ 2 (frozenElliptic p u))
    (hWrange : ∀ x, W x ∈ Set.Icc (0 : ℝ) M)
    (hVderiv_nonpos : ∀ x, deriv (frozenElliptic p u) x ≤ 0)
    (hVbound : ∀ x, |frozenElliptic p u x| ≤ BV)
    (hV2bound : ∀ x, |deriv (deriv (frozenElliptic p u)) x| ≤ BV2)
    (hsmall : (1 / lam) * Cmono < 1)
    (hstep_deriv : ∀ x,
      deriv W x - (1 / lam) *
          deriv (fun y => paperWaveOperator p c u W y) x = deriv Z x)
    (hZderiv : ∀ x, deriv Z x ≤ 0)
    (hbot : Tendsto (fun x => deriv W x) atBot (𝓝 La)) (hLa : La ≤ 0)
    (htop : Tendsto (fun x => deriv W x) atTop (𝓝 Lb)) (hLb : Lb ≤ 0)
    (hCmono : paperCmono p a M BV BV2 ≤ Cmono) :
    Antitone W := by
  exact paperStep_antitone_by_routeA
    (p := p) (c := c) (lam := lam) (Cmono := Cmono)
    (u := u) (Z := Z) (W := W) hlam
    (hWreg.differentiable (by norm_num))
    (paperStepRouteAData_of_structural
      (p := p) (c := c) (lam := lam) (Cmono := Cmono)
      (a := a) (M := M) (BV := BV) (BV2 := BV2)
      (u := u) (Z := Z) (W := W) (La := La) (Lb := Lb)
      ha hχ hWreg hVreg hWrange hVderiv_nonpos hVbound hV2bound
      hsmall hstep_deriv hZderiv hbot hLa htop hLb hCmono)

/-- Smooth paper-expanded implicit steps preserve antitonicity from structural
Route-A data plus the implicit step equation.  The differentiated step equation
is not a caller hypothesis. -/
theorem paperStep_antitone_by_routeA_of_structuralData
    {p : CMParams} {c lam Cmono : ℝ} {u Z W : ℝ → ℝ}
    {La Lb : ℝ}
    (hlam : 0 < lam)
    (hd : PaperStepRouteAStructuralData p c lam Cmono u Z W)
    (hWreg : ContDiff ℝ 3 W)
    (hwave : Differentiable ℝ (fun y => paperWaveOperator p c u W y))
    (hWrange : ∀ x, W x ∈ Set.Icc (0 : ℝ) hd.M)
    (hstep : ∀ x, paperImplicitStepOp p c (1 / lam) u W x = Z x)
    (hZderiv : ∀ x, deriv Z x ≤ 0)
    (hbot : Tendsto (fun x => deriv W x) atBot (𝓝 La)) (hLa : La ≤ 0)
    (htop : Tendsto (fun x => deriv W x) atTop (𝓝 Lb)) (hLb : Lb ≤ 0) :
    Antitone W := by
  exact paperStep_antitone_by_routeA
    (p := p) (c := c) (lam := lam) (Cmono := Cmono)
    (u := u) (Z := Z) (W := W) hlam
    (hWreg.differentiable (by norm_num))
    (hd.toRouteAData hWreg hwave hWrange hstep hZderiv hbot hLa htop hLb)

/-- Tail-free structural Route-A theorem.  It consumes only the global Green
derivative bound, not derivative limits at either endpoint. -/
theorem paperStep_antitone_by_routeA_of_structuralData_tailfree
    {p : CMParams} {c lam Cmono Q : ℝ} {u Z W : ℝ → ℝ}
    (hlam : 0 < lam)
    (hd : PaperStepRouteAStructuralData p c lam Cmono u Z W)
    (hWreg : ContDiff ℝ 3 W)
    (hwave : Differentiable ℝ (fun y => paperWaveOperator p c u W y))
    (hWrange : ∀ x, W x ∈ Set.Icc (0 : ℝ) hd.M)
    (hstep : ∀ x, paperImplicitStepOp p c (1 / lam) u W x = Z x)
    (hZderiv : ∀ x, deriv Z x ≤ 0)
    (hqbound : ∀ x, |deriv W x| ≤ Q) :
    Antitone W := by
  let E : ℝ := 1 + |c| + hd.a * p.m * hd.M ^ (p.m - 1) * hd.BV
  have ha0 : 0 ≤ hd.a := by
    rw [hd.ha]
    linarith [hd.hχ]
  have hM0 : 0 ≤ hd.M := le_trans (hWrange 0).1 (hWrange 0).2
  have hBV0 : 0 ≤ hd.BV :=
    le_trans (abs_nonneg (frozenElliptic p u 0)) (hd.V_bound 0)
  have hE : 0 ≤ E := by
    dsimp [E]
    have hm0 : 0 ≤ p.m := by linarith [p.hm]
    have hpow0 : 0 ≤ hd.M ^ (p.m - 1) := Real.rpow_nonneg hM0 _
    have hterm : 0 ≤ hd.a * p.m * hd.M ^ (p.m - 1) * hd.BV :=
      mul_nonneg (mul_nonneg (mul_nonneg ha0 hm0) hpow0) hBV0
    exact add_nonneg (add_nonneg zero_le_one (abs_nonneg c)) hterm
  have hq2 : ContDiff ℝ 2 (fun x => deriv W x) := by
    have hW3 : ContDiff ℝ ((2 : ℕ∞) + 1) W := by
      norm_num at hWreg ⊢
      exact hWreg
    exact (contDiff_succ_iff_deriv.mp hW3).2.2
  have hstep_deriv : ∀ x,
      deriv W x - (1 / lam) *
          deriv (fun y => paperWaveOperator p c u W y) x = deriv Z x :=
    paperStep_stepDeriv_of_implicit
      (p := p) (c := c) (lam := lam) (u := u) (Z := Z) (W := W)
      hstep (hWreg.differentiable (by norm_num)) hwave
  have hmono : ∀ eta, 0 < eta → ∀ x₀,
      0 < deriv W x₀ →
      |deriv (deriv W) x₀| < eta →
      deriv (deriv (deriv W)) x₀ < eta →
      deriv (fun x => paperWaveOperator p c u W x) x₀ ≤
        Cmono * deriv W x₀ + E * eta := by
    intro eta heta x₀ hqpos hqSlope hqSecond
    exact paperWaveOperator_deriv_at_approx_pos_max_le_of_structural
      (p := p) (c := c) (a := hd.a) (M := hd.M) (BV := hd.BV)
      (BV2 := hd.BV2) (BVd := hd.BV) (Cmono := Cmono) (eta := eta)
      (u := u) (W := W) (x₀ := x₀)
      hd.ha hd.hχ hWreg hd.V_reg hWrange hd.V_deriv_nonpos
      hd.V_deriv_bound hd.V_bound hd.V2_bound hBV0 heta hqpos
      hqSlope hqSecond hd.Cmono_bound
  have hqnonpos := smooth_paperStep_deriv_nonpos_of_quasiMonotone_tailfree
    (p := p) (c := c) (lam := lam) (Cmono := Cmono) (E := E) (Q := Q)
    (u := u) (Z := Z) (W := W)
    hlam hd.hsmall hE hstep_deriv hZderiv hq2 hqbound hmono
  exact antitone_of_deriv_nonpos
    (hWreg.differentiable (by norm_num)) hqnonpos

/-- Data for one smooth Route-A approximating paper step.

The raw `R` tails are deliberately not fields.  The structural source-tail data
records the bounded-antitone value-tail input used to derive those `R` tails;
the derivative tails are then supplied by the Green source-tail lemma in
`paperStep_deriv_tendsto_zero_of_core`. -/
structure PaperStepRouteASmoothApproximationData
    (p : CMParams) (c lam Cmono M κ Λ : ℝ) (u Z W : ℝ → ℝ) where
  analytic : PaperStepAnalyticCore p c lam M κ Λ u Z W
  routeA : PaperStepRouteAStructuralData p c lam Cmono u Z W
  W_reg : ContDiff ℝ 3 W
  wave_diff : Differentiable ℝ (fun y => paperWaveOperator p c u W y)
  W_range : ∀ x, W x ∈ Set.Icc (0 : ℝ) routeA.M
  Z_deriv_nonpos : ∀ x, deriv Z x ≤ 0

/-- Each smooth approximating paper step is antitone by Route A, not by a
carried monotonicity field. -/
theorem PaperStepRouteASmoothApproximationData.antitone
    {p : CMParams} {c lam Cmono M κ Λ : ℝ} {u Z W : ℝ → ℝ}
    (hlam : 0 < lam)
    (hd : PaperStepRouteASmoothApproximationData p c lam Cmono M κ Λ u Z W) :
    Antitone W := by
  have hstep : ∀ x, paperImplicitStepOp p c (1 / lam) u W x = Z x :=
    smooth_paperStep_step_op_of_core
      (p := p) (c := c) (lam := lam) (M := M) (κ := κ) (Λ := Λ)
      hlam hd.analytic
  have hqbound : ∀ x, |deriv W x| ≤ Λ :=
    (smooth_paperStep_basic_regular_of_core
      (c := c) (lam := lam) hlam hd.analytic).2.2
  exact paperStep_antitone_by_routeA_of_structuralData_tailfree
    (p := p) (c := c) (lam := lam) (Cmono := Cmono)
    (Q := Λ) (u := u) (Z := Z) (W := W)
    hlam hd.routeA hd.W_reg hd.wave_diff hd.W_range hstep hd.Z_deriv_nonpos
    hqbound

/-- Route-A mollification/approximant data for a raw paper step.

The raw step `W` is not required to be `C³`, and antitonicity of the approximants
is not carried.  The source approximants are recorded as bump mollifications; the
smooth paper-step data for `Wε n` are what prove eventual antitonicity. -/
structure PaperStepRouteAApproximationData
    (p : CMParams) (c lam Cmono M κ Λ : ℝ) (u Z W : ℝ → ℝ) where
  ρ : ℕ → ContDiffBump (0 : ℝ)
  Zε : ℕ → ℝ → ℝ
  Zε_eq : ∀ n, Zε n = mollify (((ρ n).normed volume)) Z
  Wε : ℕ → ℝ → ℝ
  smooth : ∀ n,
    PaperStepRouteASmoothApproximationData p c lam Cmono M κ Λ u (Zε n) (Wε n)
  pointwise_limit : ∀ x, Tendsto (fun n => Wε n x) atTop (𝓝 (W x))

/-- Eventual antitonicity of the approximants, proved from their smooth Route-A
data. -/
theorem PaperStepRouteAApproximationData.anti_eventually
    {p : CMParams} {c lam Cmono M κ Λ : ℝ} {u Z W : ℝ → ℝ}
    (hlam : 0 < lam)
    (hd : PaperStepRouteAApproximationData p c lam Cmono M κ Λ u Z W) :
    ∀ᶠ n in atTop, Antitone (hd.Wε n) := by
  exact Eventually.of_forall fun n => (hd.smooth n).antitone hlam

/-- Antitonicity of the raw step by the mollification-approximant route. -/
theorem paperStep_antitone_of_trap_via_mollification
    {p : CMParams} {c lam Cmono M κ Λ : ℝ} {u Z W : ℝ → ℝ}
    (hlam : 0 < lam)
    (hd : PaperStepRouteAApproximationData p c lam Cmono M κ Λ u Z W) :
    Antitone W := by
  intro x y hxy
  have hanti_eventually :=
    PaperStepRouteAApproximationData.anti_eventually
      (p := p) (c := c) (lam := lam) (Cmono := Cmono)
      (M := M) (κ := κ) (Λ := Λ) (u := u) (Z := Z) (W := W) hlam hd
  have hevent : ∀ᶠ n in atTop, hd.Wε n y ≤ hd.Wε n x := by
    filter_upwards [hanti_eventually] with n hn
    exact hn hxy
  exact le_of_tendsto_of_tendsto
    (hd.pointwise_limit y) (hd.pointwise_limit x) hevent

/-- A paper-step output core whose antitonicity is supplied by Route A rather
than the shifted sliding wrapper. -/
structure PaperStepOutputRouteACore
    (p : CMParams) (c lam M κ Λ : ℝ) (u Z W : ℝ → ℝ) where
  analytic : PaperStepAnalyticCore p c lam M κ Λ u Z W
  nonneg : ∀ x, 0 ≤ W x
  le_barrier : ∀ x, W x ≤ upperBarrier κ M x
  le_old : ∀ x, W x ≤ Z x
  anti : Antitone W

/-- The Schauder-side data needed to turn a fixed source into the Route-A paper
step output.  The `fixed` field supplies `W = greenConv R` and the analytic
core; the remaining fields are exactly the trap-barrier and Route-A payloads
consumed by `paperRotheStepProducer_of_routeA_greenCore`. -/
structure PaperStepOutputRouteAAssemblyData
    (p : CMParams) (c lam M κ Λ : ℝ) (u Z : ℝ → ℝ) where
  fixed : PaperStepFixedSourceCore p c lam M κ Λ u Z
  C_chem : ℝ
  lowerZero :
    PaperStepLowerData p c lam M C_chem u Z fixed.W (fun _ => 0)
  upperOld :
    PaperStepUpperData p c lam M C_chem u Z fixed.W Z
  upperBarrier :
    PaperStepUpperData p c lam M C_chem u Z fixed.W (upperBarrier κ M)
  Cmono : ℝ
  routeA : PaperStepRouteAStructuralData p c lam Cmono u Z fixed.W
  approx : PaperStepRouteAApproximationData p c lam Cmono M κ Λ u Z fixed.W

namespace PaperStepOutputRouteAAssemblyData

/-- Assemble the dependent output pair from fixed-source, barrier, and Route-A
data. -/
def toOutputRouteACore
    {p : CMParams} {c lam M κ Λ : ℝ} {u Z : ℝ → ℝ}
    (hlam : 0 < lam)
    (h : PaperStepOutputRouteAAssemblyData p c lam M κ Λ u Z) :
    Σ' W : ℝ → ℝ, PaperStepOutputRouteACore p c lam M κ Λ u Z W := by
  have hstep :
      ∀ x, paperImplicitStepOp p c (1 / lam) u h.fixed.W x = Z x :=
    smooth_paperStep_step_op_of_core hlam h.fixed.analyticCore
  exact
    ⟨h.fixed.W,
      { analytic := h.fixed.analyticCore
        nonneg := fun x =>
          paperStep_ge_lower (c := c) (lam := lam) hlam hstep h.lowerZero x
        le_barrier :=
          paperStep_le_upper
            (c := c) (lam := lam) hlam hstep h.upperBarrier
        le_old :=
          paperStep_le_upper (c := c) (lam := lam) hlam hstep h.upperOld
        anti :=
          paperStep_antitone_of_trap_via_mollification hlam h.approx }⟩

end PaperStepOutputRouteAAssemblyData

/-- Route-A assembly data once the fixed source has already been
constructed.  This separates the Schauder fixed-source step from the barrier and
Route-A payloads, so the fixed source can be supplied concretely by
`PaperStepFixedSourceExistsForSuperTrap`. -/
structure PaperStepOutputRouteAFixedRestData
    (p : CMParams) (c lam M κ Λ : ℝ) (u Z : ℝ → ℝ)
    (fixed : PaperStepFixedSourceCore p c lam M κ Λ u Z) where
  C_chem : ℝ
  lowerZero :
    PaperStepLowerData p c lam M C_chem u Z fixed.W (fun _ => 0)
  upperOld :
    PaperStepUpperData p c lam M C_chem u Z fixed.W Z
  upperBarrier :
    PaperStepUpperData p c lam M C_chem u Z fixed.W (upperBarrier κ M)
  Cmono : ℝ
  routeA : PaperStepRouteAStructuralData p c lam Cmono u Z fixed.W
  approx : PaperStepRouteAApproximationData p c lam Cmono M κ Λ u Z fixed.W

namespace PaperStepOutputRouteAFixedRestData

/-- Reattach the concrete fixed source to the Route-A payload. -/
def toAssemblyData
    {p : CMParams} {c lam M κ Λ : ℝ} {u Z : ℝ → ℝ}
    {fixed : PaperStepFixedSourceCore p c lam M κ Λ u Z}
    (h : PaperStepOutputRouteAFixedRestData p c lam M κ Λ u Z fixed) :
    PaperStepOutputRouteAAssemblyData p c lam M κ Λ u Z :=
  { fixed := fixed
    C_chem := h.C_chem
    lowerZero := h.lowerZero
    upperOld := h.upperOld
    upperBarrier := h.upperBarrier
    Cmono := h.Cmono
    routeA := h.routeA
    approx := h.approx }

/-- Assemble the dependent output pair after reattaching the fixed source. -/
def toOutputRouteACore
    {p : CMParams} {c lam M κ Λ : ℝ} {u Z : ℝ → ℝ}
    {fixed : PaperStepFixedSourceCore p c lam M κ Λ u Z}
    (hlam : 0 < lam)
    (h : PaperStepOutputRouteAFixedRestData p c lam M κ Λ u Z fixed) :
    Σ' W : ℝ → ℝ, PaperStepOutputRouteACore p c lam M κ Λ u Z W :=
  h.toAssemblyData.toOutputRouteACore hlam

end PaperStepOutputRouteAFixedRestData

/-- Per-`Z` assembly provider for the current Route-A Green core interface. -/
def PaperGreenStepInputRouteAAssemblyProvider
    (p : CMParams) (c lam M κ Λ : ℝ) (u : ℝ → ℝ) : Type :=
  ∀ Z : ℝ → ℝ, Continuous Z → Antitone Z → (∀ x, 0 ≤ Z x) →
    (∀ x, Z x ≤ upperBarrier κ M x) →
    (∀ x, paperWaveOperator p c u Z x ≤ 0) →
      PaperStepOutputRouteAAssemblyData p c lam M κ Λ u Z

/-- Per-`Z` Route-A data provider after the fixed source has been constructed
from the super-trap Schauder statement.  The old iterate's supersolution condition
is an explicit input; it is not derivable from the bare paper producer shape. -/
def PaperGreenStepInputRouteASuperRestProvider
    (p : CMParams) (c lam M κ Λ : ℝ) (u : ℝ → ℝ) : Type :=
  ∀ Z : ℝ → ℝ, (hZc : Continuous Z) → (hZa : Antitone Z) →
    (hZ0 : ∀ x, 0 ≤ Z x) →
    (hZB : ∀ x, Z x ≤ upperBarrier κ M x) →
    (hZsuper : ∀ x, paperWaveOperator p c u Z x ≤ 0) →
    (fixed : PaperStepFixedSourceCore p c lam M κ Λ u Z) →
      PaperStepOutputRouteAFixedRestData p c lam M κ Λ u Z fixed

/-- Per-step Green input using Route-A antitonicity data instead of
`PaperStepAntitoneData.shiftedOneSided`. -/
structure PaperGreenStepInputRouteACore
    (p : CMParams) (c lam M κ Λ : ℝ) (u : ℝ → ℝ) where
  hlam : 0 < lam
  basePaperSuper : ∀ x, paperWaveOperator p c u (upperBarrier κ M) x ≤ 0
  produce : ∀ Z : ℝ → ℝ, Continuous Z → Antitone Z → (∀ x, 0 ≤ Z x) →
      (∀ x, Z x ≤ upperBarrier κ M x) →
      (∀ x, paperWaveOperator p c u Z x ≤ 0) →
      Σ' W : ℝ → ℝ, PaperStepOutputRouteACore p c lam M κ Λ u Z W

/-- The exact Route-A interface consumed by the Rothe recursion.

Only iterates already carrying `PaperIterateBase` occur in the recursion.  In
particular this interface does not ask an arbitrary continuous trapped
supersolution to possess the `C²` and exponential-tail regularity needed by the
Green source box. -/
structure PaperGreenStepInputRouteAOrbitCore
    (p : CMParams) (c lam M κ Λ : ℝ) (u : ℝ → ℝ) where
  hlam : 0 < lam
  basePaperSuper : ∀ x, paperWaveOperator p c u (upperBarrier κ M) x ≤ 0
  produce_regular : ∀ Z : ℝ → ℝ, PaperIterateBase p c κ M u Z →
      Σ' W : ℝ → ℝ, PaperStepOutputRouteACore p c lam M κ Λ u Z W

/-- The legacy all-supertrap core supplies the smaller orbit-faithful core. -/
def PaperGreenStepInputRouteACore.toOrbitCore
    {p : CMParams} {c lam M κ Λ : ℝ} {u : ℝ → ℝ}
    (h : PaperGreenStepInputRouteACore p c lam M κ Λ u) :
    PaperGreenStepInputRouteAOrbitCore p c lam M κ Λ u where
  hlam := h.hlam
  basePaperSuper := h.basePaperSuper
  produce_regular := by
    intro Z hZ
    exact h.produce Z hZ.cont hZ.anti hZ.nonneg hZ.le_barrier hZ.paperSuper

/-- Route-A Green input with the super-trap precondition threaded into
`produce`.  This is the satisfiable interface for the Schauder fixed-source step:
the descent orbit supplies `F_u(Z) ≤ 0` inductively, while the bare
`PaperRotheStepProducer` interface does not carry it. -/
structure PaperGreenStepInputRouteASuperCore
    (p : CMParams) (c lam M κ Λ : ℝ) (u : ℝ → ℝ) where
  hlam : 0 < lam
  basePaperSuper : ∀ x, paperWaveOperator p c u (upperBarrier κ M) x ≤ 0
  produce : ∀ Z : ℝ → ℝ, Continuous Z → Antitone Z → (∀ x, 0 ≤ Z x) →
      (∀ x, Z x ≤ upperBarrier κ M x) →
      (∀ x, paperWaveOperator p c u Z x ≤ 0) →
      Σ' W : ℝ → ℝ, PaperStepOutputRouteACore p c lam M κ Λ u Z W

/-- Assemble a Route-A Green core once the fixed-source, barrier, and Route-A
payload has been supplied for each trapped old iterate. -/
def paperGreenStepInputRouteACore_of_assembly
    {p : CMParams} {c lam M κ Λ : ℝ} {u : ℝ → ℝ}
    (hlam : 0 < lam)
    (hbase : ∀ x, paperWaveOperator p c u (upperBarrier κ M) x ≤ 0)
    (hstep : PaperGreenStepInputRouteAAssemblyProvider p c lam M κ Λ u) :
    PaperGreenStepInputRouteACore p c lam M κ Λ u where
  hlam := hlam
  basePaperSuper := hbase
  produce := by
    intro Z hZc hZa hZ0 hZB hZsuper
    exact (hstep Z hZc hZa hZ0 hZB hZsuper).toOutputRouteACore hlam

/-- Assemble the super-core from a concrete super-trap fixed-source existence
statement plus the remaining Route-A data. -/
def paperGreenStepInputRouteASuperCore_of_fixedSource
    {p : CMParams} {c lam M κ Λ : ℝ} {u : ℝ → ℝ}
    (hu : InMonotoneWaveTrapSet κ M u)
    (hlam : 0 < lam)
    (hbase : ∀ x, paperWaveOperator p c u (upperBarrier κ M) x ≤ 0)
    (hfixed : PaperStepFixedSourceExistsForSuperTrap p c lam M κ Λ u)
    (hrest : PaperGreenStepInputRouteASuperRestProvider p c lam M κ Λ u) :
    PaperGreenStepInputRouteASuperCore p c lam M κ Λ u where
  hlam := hlam
  basePaperSuper := hbase
  produce := by
    intro Z hZc hZa hZ0 hZB hZsuper
    let fixed : PaperStepFixedSourceCore p c lam M κ Λ u Z :=
      PaperStepFixedSourceCore.of_existsForSuperTrap
        (p := p) (c := c) (lam := lam) (M := M) (κ := κ) (Λ := Λ)
        (u := u) (Z := Z) hfixed hu hZc hZa hZ0 hZB hZsuper
    exact (hrest Z hZc hZa hZ0 hZB hZsuper fixed).toOutputRouteACore hlam

/-- Forget the super-core to the existing Route-A core.

The two interfaces now have the same per-step supersolution input.  In
particular, the proof passed to `PaperGreenStepInputRouteACore.produce` is fed
directly to `hin.produce`; no separate all-trapped-profile supersolution
oracle is needed. -/
def paperGreenStepInputRouteACore_of_superCore
    {p : CMParams} {c lam M κ Λ : ℝ} {u : ℝ → ℝ}
    (hin : PaperGreenStepInputRouteASuperCore p c lam M κ Λ u) :
    PaperGreenStepInputRouteACore p c lam M κ Λ u where
  hlam := hin.hlam
  basePaperSuper := hin.basePaperSuper
  produce := by
    intro Z hZc hZa hZ0 hZB hZpaperSuper
    exact hin.produce Z hZc hZa hZ0 hZB hZpaperSuper

/-- Trap-indexed Route-A core from the concrete fixed-source provider.  The
old iterate's supersolution proof is threaded through the `produce` call and
used by the fixed-source existence theorem at that same iterate. -/
def paperGreenStepInputRouteACore_of_trap_fixedSource
    {p : CMParams} {c lam M κ Λ : ℝ} {u : ℝ → ℝ}
    (hu : InMonotoneWaveTrapSet κ M u)
    (hlam : 0 < lam)
    (hbase : ∀ x, paperWaveOperator p c u (upperBarrier κ M) x ≤ 0)
    (hfixed : PaperStepFixedSourceExistsForSuperTrap p c lam M κ Λ u)
    (hrest : PaperGreenStepInputRouteASuperRestProvider p c lam M κ Λ u) :
    PaperGreenStepInputRouteACore p c lam M κ Λ u :=
  paperGreenStepInputRouteACore_of_superCore
    (paperGreenStepInputRouteASuperCore_of_fixedSource
      (p := p) (c := c) (lam := lam) (M := M) (κ := κ) (Λ := Λ)
      (u := u) hu hlam hbase hfixed hrest)

/-- Trap-indexed Route-A core from the truncated source-box fixed-source route.

This is the wiring layer: the source-box fixed point first yields
`PaperStepFixedSourceExistsForSuperTrap` via
`PaperStepFixedSourceExistsForSuperTrap.of_truncated_sourceBox`, and the existing
Route-A fixed-source assembly then produces the Green core consumed by
`paperRotheStepProducer_of_routeA_greenCore`. -/
def paperGreenStepInputRouteACore_of_trap_truncatedSourceBox
    {p : CMParams} {c lam M κ Λ sigma aL C_u L_u : ℝ} {u : ℝ → ℝ}
    (hu : InMonotoneWaveTrapSet κ M u)
    (hu_rate : ExpLeftRate sigma aL C_u u L_u)
    (hlam : 0 < lam)
    (hbase : ∀ x, paperWaveOperator p c u (upperBarrier κ M) x ≤ 0)
    (hboxData : InMonotoneWaveTrapSet κ M u →
      ExpLeftRate sigma aL C_u u L_u →
      ∀ Z : ℝ → ℝ, Continuous Z → Antitone Z →
      (∀ x, 0 ≤ Z x) →
      (∀ x, Z x ≤ upperBarrier κ M x) →
      (∀ x, paperWaveOperator p c u Z x ≤ 0) →
        PaperTruncatedFixedSourceBoxData p c lam M κ Λ u Z)
    (hrest : PaperGreenStepInputRouteASuperRestProvider p c lam M κ Λ u) :
    PaperGreenStepInputRouteACore p c lam M κ Λ u :=
  paperGreenStepInputRouteACore_of_trap_fixedSource
    (p := p) (c := c) (lam := lam) (M := M) (κ := κ) (Λ := Λ)
    (u := u) hu hlam hbase
    (PaperStepFixedSourceExistsForSuperTrap.of_truncated_sourceBox
      (p := p) (c := c) (lam := lam) (M := M) (κ := κ) (Λ := Λ)
      (sigma := sigma) (aL := aL) (C_u := C_u) (L_u := L_u)
      (u := u) hu_rate hboxData)
    hrest

/-- Trap-indexed Route-A Green core assembly.

The trap hypothesis identifies the intended regime for the frozen profile `u`;
all analytic obligations still enter through the concrete per-step assembly
provider, so this theorem does not hide the Schauder fixed-source or barrier
comparison work. -/
def paperGreenStepInputRouteACore_of_trap
    {p : CMParams} {c lam M κ Λ : ℝ} {u : ℝ → ℝ}
    (_hu : InMonotoneWaveTrapSet κ M u)
    (hlam : 0 < lam)
    (hbase : ∀ x, paperWaveOperator p c u (upperBarrier κ M) x ≤ 0)
    (hstep : PaperGreenStepInputRouteAAssemblyProvider p c lam M κ Λ u) :
    PaperGreenStepInputRouteACore p c lam M κ Λ u :=
  paperGreenStepInputRouteACore_of_assembly (p := p) (c := c) (lam := lam)
    (M := M) (κ := κ) (Λ := Λ) (u := u) hlam hbase hstep

/-- Assemble the standard `PaperRotheStepProducer` from a Route-A Green core.
The `anti` field is produced by `paperStep_antitone_by_routeA`, not by
`paperStep_antitone_by_sliding`. -/
def paperRotheStepProducer_of_routeA_greenCore
    {p : CMParams} {c lam M κ Λ : ℝ} {u : ℝ → ℝ}
    (hin : PaperGreenStepInputRouteACore p c lam M κ Λ u) :
    PaperRotheStepProducer p c lam M κ Λ u where
  hlam := hin.hlam
  basePaperSuper := hin.basePaperSuper
  produce := by
    intro Z hZc hZa hZ0 hZB hZsuper
    obtain ⟨W, hout⟩ := hin.produce Z hZc hZa hZ0 hZB hZsuper
    have hstep : ∀ x, paperImplicitStepOp p c (1 / lam) u W x = Z x :=
      smooth_paperStep_step_op_of_core
        (p := p) (c := c) (lam := lam) (M := M) (κ := κ) (Λ := Λ)
        hin.hlam hout.analytic
    have hbasic :
        Continuous W ∧ Differentiable ℝ W ∧ ∀ x, |deriv W x| ≤ Λ :=
      smooth_paperStep_basic_regular_of_core
        (p := p) (c := c) (lam := lam) (M := M) (κ := κ) (Λ := Λ)
        hin.hlam hout.analytic
    refine ⟨W, ?_⟩
    exact
      { step_op := hstep
        cont := hbasic.1
        diff := hbasic.2.1
        contDiff2 :=
          paperStep_contDiff_two_of_core
            (p := p) (c := c) (lam := lam) (M := M) (κ := κ) (Λ := Λ)
            hin.hlam hout.analytic
        deriv_le := hbasic.2.2
        nonneg := hout.nonneg
        le_barrier := hout.le_barrier
        le_old := hout.le_old
        anti := hout.anti
        paperSuper :=
          paperWaveOperator_nonpos_of_implicitStep_le
            (p := p) (c := c) (lam := lam) hin.hlam hstep hout.le_old }
  produce_regular := by
    intro Z hZbase
    obtain ⟨W, hout⟩ :=
      hin.produce Z hZbase.cont hZbase.anti hZbase.nonneg
        hZbase.le_barrier hZbase.paperSuper
    have hstep : ∀ x, paperImplicitStepOp p c (1 / lam) u W x = Z x :=
      smooth_paperStep_step_op_of_core
        (p := p) (c := c) (lam := lam) (M := M) (κ := κ) (Λ := Λ)
        hin.hlam hout.analytic
    have hbasic :
        Continuous W ∧ Differentiable ℝ W ∧ ∀ x, |deriv W x| ≤ Λ :=
      smooth_paperStep_basic_regular_of_core
        (p := p) (c := c) (lam := lam) (M := M) (κ := κ) (Λ := Λ)
        hin.hlam hout.analytic
    refine ⟨W, ?_⟩
    exact
      { step_op := hstep
        cont := hbasic.1
        diff := hbasic.2.1
        contDiff2 :=
          paperStep_contDiff_two_of_core
            (p := p) (c := c) (lam := lam) (M := M) (κ := κ) (Λ := Λ)
            hin.hlam hout.analytic
        deriv_le := hbasic.2.2
        nonneg := hout.nonneg
        le_barrier := hout.le_barrier
        le_old := hout.le_old
        anti := hout.anti
        paperSuper :=
          paperWaveOperator_nonpos_of_implicitStep_le
            (p := p) (c := c) (lam := lam) hin.hlam hstep hout.le_old }

theorem paperRotheStepProducer_all_of_routeA_greenCore
    {p : CMParams} {c lam M κ Λ : ℝ}
    (hinput : ∀ u : ℝ → ℝ, PaperGreenStepInputRouteACore p c lam M κ Λ u) :
    ∀ u : ℝ → ℝ, PaperRotheStepProducer p c lam M κ Λ u :=
  fun u => paperRotheStepProducer_of_routeA_greenCore (hinput u)

/-- Route-A version of the per-step parabolic floor.

Unlike `PaperPerStepParabolicFloor`, this floor does not carry
`PaperStepAntitoneData` or an already-differentiated step equation.  Antitonicity
is produced by Route A from smooth approximants and the pointwise limit passage;
the raw step carries no `C³` or derivative-tail fields. -/
abbrev PaperPerStepParabolicFloorRouteA
    (p : CMParams) (c lam M κ Λ : ℝ) (u : ℝ → ℝ) : Type :=
  PaperGreenStepInputRouteACore p c lam M κ Λ u

/-- `PaperRotheStepProducer` from the Route-A per-step parabolic floor. -/
theorem paperRotheStepProducer_of_routeA_parabolicFloor
    {p : CMParams} {c lam M κ Λ : ℝ} {u : ℝ → ℝ}
    (hin : PaperPerStepParabolicFloorRouteA p c lam M κ Λ u) :
    PaperRotheStepProducer p c lam M κ Λ u :=
  paperRotheStepProducer_of_routeA_greenCore hin

/-- All paper-step producers from the Route-A per-step parabolic floor. -/
theorem paperRotheStepProducer_all_of_routeA_parabolicFloor
    {p : CMParams} {c lam M κ Λ : ℝ}
    (hfloor : ∀ u : ℝ → ℝ, PaperPerStepParabolicFloorRouteA p c lam M κ Λ u) :
    ∀ u : ℝ → ℝ, PaperRotheStepProducer p c lam M κ Λ u :=
  fun u => paperRotheStepProducer_of_routeA_parabolicFloor (hfloor u)

/-! ## Step D: pointwise limits of antitone approximating steps -/

/-- A pointwise limit of eventually antitone functions is antitone.  This is the
Route-A limit passage from `W_ε` to `W`; local uniform convergence is stronger
than the pointwise convergence used here. -/
theorem antitone_of_eventual_pointwise_limit
    {ι : Type*} {l : Filter ι} [NeBot l]
    {Wε : ι → ℝ → ℝ} {W : ℝ → ℝ}
    (hanti : ∀ᶠ ε in l, Antitone (Wε ε))
    (hlim : ∀ x, Tendsto (fun ε => Wε ε x) l (𝓝 (W x))) :
    Antitone W := by
  intro x y hxy
  have hevent : ∀ᶠ ε in l, Wε ε y ≤ Wε ε x := by
    filter_upwards [hanti] with ε hε
    exact hε hxy
  exact le_of_tendsto_of_tendsto (hlim y) (hlim x) hevent

/-- Route-A assembly of the smooth approximating paper steps: if the smooth
steps are antitone by the derivative maximum principle and converge pointwise,
then the limiting paper step is antitone. -/
theorem routeA_antitone_of_smooth_paper_steps
    {ι : Type*} {l : Filter ι} [NeBot l]
    {Wε : ι → ℝ → ℝ} {W : ℝ → ℝ}
    (hanti : ∀ᶠ ε in l, Antitone (Wε ε))
    (hlim : ∀ x, Tendsto (fun ε => Wε ε x) l (𝓝 (W x))) :
    Antitone W :=
  antitone_of_eventual_pointwise_limit hanti hlim

section AxiomAudit

#print axioms mollify_antitone_of_nonneg_kernel
#print axioms mollify_antitone
#print axioms mollify_isBddFun_of_nonneg_kernel
#print axioms bump_mollify_antitone
#print axioms bump_mollify_contDiff
#print axioms bump_mollify_isBddFun
#print axioms bump_mollify_tendsto_right_of_continuous
#print axioms antitone_isBddFun_tendsto_atTop
#print axioms antitone_isBddFun_tendsto_atBot
#print axioms antitone_isBddFun_has_tail_limits
#print axioms bump_mollify_antitone_contDiff_tail_limits
#print axioms smooth_paperStep_step_op_of_core
#print axioms paperStep_stepDeriv_of_implicit
#print axioms smooth_paperStep_basic_regular_of_core
#print axioms paperCmono
#print axioms PaperWaveOperatorPosMaxBookkeeping
#print axioms paperWaveOperator_posMax_bookkeeping_of_structural
#print axioms paperWaveOperator_deriv_at_pos_max_le_of_quasiMonotone
#print axioms paperWaveOperator_deriv_at_pos_max_le_of_expanded_terms
#print axioms paperWaveOperator_deriv_at_approx_pos_max_le_of_expanded_terms
#print axioms paperWaveOperator_deriv_at_approx_pos_max_le_of_structural
#print axioms paperWaveOperator_deriv_at_pos_max_le_of_bookkeeping
#print axioms smooth_paperStep_deriv_nonpos_of_quasiMonotone
#print axioms smooth_paperStep_deriv_nonpos_of_quasiMonotone_tailfree
#print axioms smooth_paperStep_preserves_antitone_of_quasiMonotone
#print axioms paperStepRouteAData_of_structural
#print axioms PaperStepRouteAStructuralData
#print axioms PaperStepRouteAStructuralData.toRouteAData
#print axioms paperStep_antitone_by_routeA
#print axioms paperStep_antitone_by_routeA_of_structural
#print axioms paperStep_antitone_by_routeA_of_structuralData
#print axioms paperStep_antitone_by_routeA_of_structuralData_tailfree
#print axioms PaperStepRouteAApproximationData
#print axioms paperStep_antitone_of_trap_via_mollification
#print axioms paperGreenStepInputRouteACore_of_trap_truncatedSourceBox
#print axioms paperRotheStepProducer_of_routeA_greenCore
#print axioms paperRotheStepProducer_all_of_routeA_greenCore
#print axioms PaperPerStepParabolicFloorRouteA
#print axioms paperRotheStepProducer_of_routeA_parabolicFloor
#print axioms paperRotheStepProducer_all_of_routeA_parabolicFloor
#print axioms antitone_of_eventual_pointwise_limit
#print axioms routeA_antitone_of_smooth_paper_steps

end AxiomAudit

end ShenWork.Paper1
