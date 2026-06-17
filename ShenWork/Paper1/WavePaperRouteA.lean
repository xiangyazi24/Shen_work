/-
  ShenWork/Paper1/WavePaperRouteA.lean

  Route A for the paper-expanded step: monotone smoothing, the smooth
  derivative maximum-principle core, and the pointwise limit passage.

  This file deliberately does not use the older sliding wrappers as the
  antitonicity proof.  The smooth maximum principle below is driven by
  `q = W'` and the differentiated paper-expanded operator estimate.
-/
import ShenWork.Paper1.WavePaperRotheProducer
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

/-! ## Step B: smooth paper step through the existing Green layer -/

/-- Route-A Step B: once the existing paper Green/Banach layer provides a
`PaperStepAnalyticCore`, the paper-expanded implicit step equation follows from
the committed Green resolvent identity. -/
theorem smooth_paperStep_step_op_of_core
    {p : CMParams} {c lam M κ Λ : ℝ} {u Z W : ℝ → ℝ}
    (hlam : 0 < lam)
    (hc : PaperStepAnalyticCore p c lam M κ Λ u Z W) :
    ∀ x, paperImplicitStepOp p c (1 / lam) u W x = Z x := by
  exact paperStep_step_op (c := c) (lam := lam) hlam
    (paperStepAnalytic_of_core hlam hc)

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
    (hmax_est : ∀ x₀,
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
  have hA := hmax_est x₀ hmax hqpos
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
    (hmax_est : ∀ x₀,
      IsMaxOn (fun x => deriv W x) Set.univ x₀ →
        0 < deriv W x₀ →
          deriv (fun x => paperWaveOperator p c u W x) x₀
            ≤ Cmono * deriv W x₀) :
    Antitone W := by
  exact antitone_of_deriv_nonpos hWdiff
    (smooth_paperStep_deriv_nonpos_of_quasiMonotone
      (p := p) (c := c) (lam := lam) (Cmono := Cmono)
      (u := u) (Z := Z) (W := W) (La := La) (Lb := Lb)
      hlam hsmall hstep_deriv hZderiv hqcont hbot hLa htop hLb hmax_est)

/-! ## Route-A paper producer interface, without shifted sliding data -/

/-- Route-A antitonicity data for one smooth paper-expanded step.

This replaces `PaperStepAntitoneData`: no shifted comparison residual is carried.
The data are exactly the differentiated step equation, the mollified-source
derivative sign, the derivative tails, and the `q`-maximum estimate. -/
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
  max_est : ∀ x₀,
    IsMaxOn (fun x => deriv W x) Set.univ x₀ →
      0 < deriv W x₀ →
        deriv (fun x => paperWaveOperator p c u W x) x₀
          ≤ Cmono * deriv W x₀

/-- One smooth paper step is antitone from Route-A derivative data. -/
theorem paperStep_antitone_by_routeA
    {p : CMParams} {c lam Cmono : ℝ} {u Z W : ℝ → ℝ}
    (hlam : 0 < lam)
    (hWdiff : Differentiable ℝ W)
    (hd : PaperStepRouteAData p c lam Cmono u Z W) :
    Antitone W := by
  exact smooth_paperStep_preserves_antitone_of_quasiMonotone
    (p := p) (c := c) (lam := lam) (Cmono := Cmono)
    (u := u) (Z := Z) (W := W) (La := hd.La) (Lb := hd.Lb)
    hlam hd.hsmall hWdiff hd.step_deriv hd.Z_deriv_nonpos
    hd.q_cont hd.hbot hd.hLa hd.htop hd.hLb hd.max_est

/-- A paper-step output core whose antitonicity is supplied by Route A rather
than the shifted sliding wrapper. -/
structure PaperStepOutputRouteACore
    (p : CMParams) (c lam M κ Λ : ℝ) (u Z W : ℝ → ℝ) where
  analytic : PaperStepAnalyticCore p c lam M κ Λ u Z W
  C_chem : ℝ
  lowerZero : PaperStepLowerData p c lam M C_chem u Z W (fun _ => 0)
  upperOld : PaperStepUpperData p c lam M C_chem u Z W Z
  upperBarrier :
    PaperStepUpperData p c lam M C_chem u Z W (upperBarrier κ M)
  Cmono : ℝ
  routeA : PaperStepRouteAData p c lam Cmono u Z W

/-- Per-step Green input using Route-A antitonicity data instead of
`PaperStepAntitoneData.shiftedOneSided`. -/
structure PaperGreenStepInputRouteACore
    (p : CMParams) (c lam M κ Λ : ℝ) (u : ℝ → ℝ) where
  hlam : 0 < lam
  produce : ∀ Z : ℝ → ℝ, Continuous Z → Antitone Z → (∀ x, 0 ≤ Z x) →
      (∀ x, Z x ≤ upperBarrier κ M x) →
      Σ' W : ℝ → ℝ, PaperStepOutputRouteACore p c lam M κ Λ u Z W

/-- Assemble the standard `PaperRotheStepProducer` from a Route-A Green core.
The `anti` field is produced by `paperStep_antitone_by_routeA`, not by
`paperStep_antitone_by_sliding`. -/
def paperRotheStepProducer_of_routeA_greenCore
    {p : CMParams} {c lam M κ Λ : ℝ} {u : ℝ → ℝ}
    (hin : PaperGreenStepInputRouteACore p c lam M κ Λ u) :
    PaperRotheStepProducer p c lam M κ Λ u where
  hlam := hin.hlam
  produce := by
    intro Z hZc hZa hZ0 hZB
    obtain ⟨W, hout⟩ := hin.produce Z hZc hZa hZ0 hZB
    have hstep : ∀ x, paperImplicitStepOp p c (1 / lam) u W x = Z x :=
      smooth_paperStep_step_op_of_core
        (p := p) (c := c) (lam := lam) (M := M) (κ := κ) (Λ := Λ)
        hin.hlam hout.analytic
    have hbasic :
        Continuous W ∧ Differentiable ℝ W ∧ ∀ x, |deriv W x| ≤ Λ :=
      smooth_paperStep_basic_regular_of_core
        (p := p) (c := c) (lam := lam) (M := M) (κ := κ) (Λ := Λ)
        hin.hlam hout.analytic
    have hnonneg : ∀ x, 0 ≤ W x := by
      have hle := paperStep_ge_lower
        (c := c) (lam := lam) hin.hlam hstep hout.lowerZero
      intro x
      exact hle x
    have hle_old : ∀ x, W x ≤ Z x :=
      paperStep_le_upper (c := c) (lam := lam) hin.hlam hstep hout.upperOld
    have hle_barrier : ∀ x, W x ≤ upperBarrier κ M x :=
      paperStep_le_upper
        (c := c) (lam := lam) hin.hlam hstep hout.upperBarrier
    refine ⟨W, ?_⟩
    exact
      { step_op := hstep
        cont := hbasic.1
        diff := hbasic.2.1
        deriv_le := hbasic.2.2
        nonneg := hnonneg
        le_barrier := hle_barrier
        le_old := hle_old
        anti := paperStep_antitone_by_routeA
          (p := p) (c := c) (lam := lam) (Cmono := hout.Cmono)
          (u := u) (Z := Z) (W := W) hin.hlam hbasic.2.1 hout.routeA }

theorem paperRotheStepProducer_all_of_routeA_greenCore
    {p : CMParams} {c lam M κ Λ : ℝ}
    (hinput : ∀ u : ℝ → ℝ, PaperGreenStepInputRouteACore p c lam M κ Λ u) :
    ∀ u : ℝ → ℝ, PaperRotheStepProducer p c lam M κ Λ u :=
  fun u => paperRotheStepProducer_of_routeA_greenCore (hinput u)

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
#print axioms bump_mollify_antitone
#print axioms bump_mollify_contDiff
#print axioms bump_mollify_tendsto_right_of_continuous
#print axioms smooth_paperStep_step_op_of_core
#print axioms smooth_paperStep_basic_regular_of_core
#print axioms paperCmono
#print axioms paperWaveOperator_deriv_at_pos_max_le_of_quasiMonotone
#print axioms paperWaveOperator_deriv_at_pos_max_le_of_expanded_terms
#print axioms smooth_paperStep_deriv_nonpos_of_quasiMonotone
#print axioms smooth_paperStep_preserves_antitone_of_quasiMonotone
#print axioms paperStep_antitone_by_routeA
#print axioms paperRotheStepProducer_of_routeA_greenCore
#print axioms paperRotheStepProducer_all_of_routeA_greenCore
#print axioms antitone_of_eventual_pointwise_limit
#print axioms routeA_antitone_of_smooth_paper_steps

end AxiomAudit

end ShenWork.Paper1
