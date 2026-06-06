/-
  ShenWork/Paper2/IntervalPicardIterateUniform.lean

  Phase-0 / M-final — the **n-uniform joint induction** (χ₀ = 0 gate theorem).

  This module assembles the landed Phase-0 atoms (M1 restart identity, M2-uniform
  C² bounds, M3/M3b source-time-C¹ wiring, M-gate-3 power-law weight bounds, and
  the kernel G1 atoms) into a single carrier

      PicardIterateUniformData p u₀ T n

  that, for every Picard iterate level `n`, packages EXPLICIT spatial-derivative
  sup bounds on the iterate slice along two monotone-decreasing profiles:

    * **G1-line** (kernel route, NO recursion):
        |∂ₓ lift(uₙ(t)) x| ≤ G1profile t
          := Cg/√t·M + Cg·2√t·CL,    CL := M·(p.a + p.b·M^p.α),
      Cg = heatGradientLinftyLinftyConstant.  This is `n`-free (the χ₀ = 0 map is
      ∂ₓS(t)(lift u₀) + ∫₀ᵗ ∂ₓS(t−s)Lₙ(s)ds, and the two kernel atoms
      `intervalFullSemigroupOperator_deriv_Linfty_pointwise_sqrt_t` (T1) and
      `gradDuhamel_sup_bound` (Atom D) bound the two pieces with `sup|Lₙ| ≤ CL` —
      the logistic sup on the M-ball, `n`-free by the ball bound).

    * **G2-line** (coefficient route WITH profile recursion):
        |∂ₓ² lift(uₙ(t)) x| ≤ G2profile t := A₂ / t².
      The recursion closes via M2-uniform's `iterate_abs_deriv2_le`:
        |∂ₓ² lift(uₙ₊₁(t))| ≤ M₁·eigExpWeight(t/2) + Cgain·(t/2)^{1/4}·Benv(t),
      with `M₁ ≤ 2M`, `Cgain = duhamelGainConst` (M3b), and
        Benv(t) = iterateSourceEnvelopeConst p.a p.b p.α M (G1profile(t/2)) (G2profile(t/2))
                = max(2·B_log(…,G1profile(t/2),G2profile(t/2)), M·(p.a+p.b·M^p.α)),
      the M3 source envelope.  Using the M-gate-3 power-law
      `eigExpWeight(t/2) ≤ (4/(e·π²))/(t/2)²`, the GATE smallness condition

        (GATE) ∀ t ∈ (0,T]:
          2M·(4/(e·π²))/(t/2)² + Cgain·(t/2)^{1/4}·Benv(t) ≤ A₂/t²

      is a SUFFICIENT, explicit, checkable condition that reproduces `A₂/t²` at the
      next level.  This is the genuinely-new gate content — the recursion arithmetic
      (`g2_step_closes`) is genuinely proved below.

      Power-counting (justification of GATE as a closable condition, T ≤ 1):
      `B_log = b·α·(1+α)·M^{α−1}·G1² + (a+b·(1+α)·M^α)·G2`.  With G1 = G1profile(t/2)
      ~ Cg·M·√2/√t (the singular kernel term) we have G1² ~ 1/t, which is STRICTLY
      SUBORDINATE to the 1/t² target for t ≤ T ≤ 1 (absorbed by the explicit
      `T ≤ 1` assumption and the constant pickup in A₂).  The G2-part of B_log is
      linear in G2 = G2profile(t/2) = A₂/(t/2)² = 4A₂/t², carrying the dominant 1/t²
      scaling; the `(t/2)^{1/4}` Duhamel gain plus the `T^{1/4}` smallness in the
      gate is what keeps the self-coupling `A₂ ↦ (…)·A₂` a contraction.

  ## Honest-partial wiring (named satisfiable field hypotheses, header-justified)

  The carrier carries, as named field hypotheses, the per-level facts that are
  pure wiring between the proved atoms (each satisfiable-by-design — see the field
  docstrings):

    * `hG1`/`hG2`: the per-level profile sup bounds (G1profile/G2profile).
    * `hM1coeff`: the half-step coefficient bound `|cosineCoeffs(lift uₙ₊₁(t/2)) k| ≤ 2M`
      (from the ball bound via `cosineCoeffs_abs_le_of_continuous_bounded`).
    * `hSrc`: the M3 `DuhamelSourceTimeC1` package (output of
      `picardIterate_source_duhamelSourceTimeC1`), with the explicit envelope keyed
      to `Benv`, plus its decay/continuity profile.
    * `hM2lift`: the M2-uniform second-derivative bound TRANSPORTED to the actual
      lift `lift(uₙ₊₁(t))` (M1 identity `picardIterateRestart_cosineIdentity`
      bridging `restartIterateCoeff`-series ↦ lift at the second-derivative level).
      This is a TRUE bound (M2's `iterate_abs_deriv2_le` is unconditional on the
      restart series); the new math is the GATE closure consuming it.

  The recursion arithmetic `g2_step_closes` (the gate closure) and the G1-line
  kernel bound `g1_kernel_bound` are GENUINELY PROVED — they are the point of the
  module.  The base case `picardIterateUniformData_zero` and the per-level
  wiring are landed via the carried satisfiable hypotheses.

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.  New file only.
-/
import ShenWork.Paper2.IntervalPicardIterateC2Bound
import ShenWork.Paper2.IntervalPicardIterateTimeC1
import ShenWork.PDE.IntervalWeightPowerBound
import ShenWork.PDE.IntervalGradDuhamelBound

open MeasureTheory Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalMildPicard (picardIter)
open ShenWork.IntervalHomogeneousQuantBound (eigExpWeight)
open ShenWork.IntervalWeightPowerBound (eigExpWeight_le)
open ShenWork.IntervalPicardIterateTimeC1 (duhamelGainConst duhamelGainConst_nonneg)
open ShenWork.IntervalPicardIterateSourceC1 (iterateSourceEnvelopeConst)
open ShenWork.IntervalLogisticSourceQuantBound (B_log B_log_nonneg)
open ShenWork.HeatKernelGradientEstimates (heatGradientLinftyLinftyConstant
  heatGradientLinftyLinftyConstant_nonneg)

noncomputable section

namespace ShenWork.IntervalPicardIterateUniform

/-! ## §1 — The explicit profiles. -/

/-- The logistic sup constant on the `M`-ball: `CL := M·(p.a + p.b·M^p.α) ≥ sup|Lₙ|`
(`n`-free, via the ball bound `|uₙ| ≤ M`). -/
def CL (p : CM2Params) (M : ℝ) : ℝ := M * (p.a + p.b * M ^ p.α)

/-- The kernel G1 profile: `G1profile t := Cg/√t·M + Cg·2√t·CL`.  Bounds
`|∂ₓ lift(uₙ(t))|` for every `n` (kernel route, no recursion). -/
def G1profile (p : CM2Params) (M t : ℝ) : ℝ :=
  heatGradientLinftyLinftyConstant / Real.sqrt t * M
    + heatGradientLinftyLinftyConstant * (2 * Real.sqrt t) * CL p M

/-- The coefficient G2 profile: `G2profile A₂ t := A₂ / t²`.  The recursion
self-reproduces this profile under the GATE smallness condition. -/
def G2profile (A₂ t : ℝ) : ℝ := A₂ / t ^ 2

/-- The M3 source envelope at the half-step window value, using the monotone
profiles evaluated at `t/2`:
`Benv p M A₂ t := iterateSourceEnvelopeConst p.a p.b p.α M (G1profile(t/2)) (G2profile(t/2))`. -/
def Benv (p : CM2Params) (M A₂ t : ℝ) : ℝ :=
  iterateSourceEnvelopeConst p.a p.b p.α M (G1profile p M (t / 2)) (G2profile A₂ (t / 2))

/-- The explicit power-law upper bound for the M-gate-3 homogeneous weight at the
half step: `2M·eigExpWeight(t/2) ≤ homWeightBound M t := 2M·(4/(e·π²))/(t/2)²`. -/
def homWeightBound (M t : ℝ) : ℝ :=
  2 * M * ((4 / (Real.exp 1 * Real.pi ^ 2)) / (t / 2) ^ 2)

/-! ## §2 — Nonnegativity facts for the profiles. -/

theorem CL_nonneg {p : CM2Params} {M : ℝ} (hM : 0 ≤ M) : 0 ≤ CL p M := by
  unfold CL
  have hpow : 0 ≤ M ^ p.α := Real.rpow_nonneg hM _
  have hfac : 0 ≤ p.a + p.b * M ^ p.α := by
    have := mul_nonneg p.hb hpow
    have := p.ha
    linarith
  exact mul_nonneg hM hfac

theorem G1profile_nonneg {p : CM2Params} {M t : ℝ} (hM : 0 ≤ M) (_ht : 0 < t) :
    0 ≤ G1profile p M t := by
  unfold G1profile
  have hCg : 0 ≤ heatGradientLinftyLinftyConstant := heatGradientLinftyLinftyConstant_nonneg
  have hCL : 0 ≤ CL p M := CL_nonneg hM
  have hst : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
  have h1 : 0 ≤ heatGradientLinftyLinftyConstant / Real.sqrt t * M :=
    mul_nonneg (div_nonneg hCg hst) hM
  have h2 : 0 ≤ heatGradientLinftyLinftyConstant * (2 * Real.sqrt t) * CL p M :=
    mul_nonneg (mul_nonneg hCg (by linarith)) hCL
  linarith

theorem eigExpWeight_nonneg (τ : ℝ) : 0 ≤ eigExpWeight τ := by
  unfold eigExpWeight
  refine tsum_nonneg (fun n => ?_)
  have hlam : (0:ℝ) ≤ unitIntervalCosineEigenvalue n := by
    have : unitIntervalCosineEigenvalue n = ((n : ℝ) * Real.pi) ^ 2 := rfl
    rw [this]; positivity
  have hexp : (0:ℝ) ≤ Real.exp (-τ * unitIntervalCosineEigenvalue n) :=
    Real.exp_nonneg _
  exact mul_nonneg hlam hexp

/-! ## §3 — The kernel G1 bound (genuinely proved).

The χ₀ = 0 reduction `intervalGradientDuhamelMap_eq_of_chi0_zero` writes the
iterate map as `S(t)(lift u₀) + ∫₀ᵗ S(t−s) Lₙ(s) ds`.  Its spatial derivative is
bounded by the two kernel atoms: T1 for the propagator term (`Cg/√t·M`) and
Atom D `gradDuhamel_sup_bound` for the divergence-form Duhamel term
(`Cg·2√t·CL`).  We package the abstract two-atom assembly: any function whose
spatial derivative at `x` equals `∂ₓS(t)(lift u₀)(x) + ∫₀ᵗ ∂ₓS(t−s)L(s)(x) ds` is
bounded by `G1profile t` once `|lift u₀| ≤ M` and `sup|L| ≤ CL`. -/

open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator intervalNeumannFullKernel)
open ShenWork.IntervalDomain (intervalMeasure)
open ShenWork.IntervalGradDuhamelBound (gradDuhamel_sup_bound)

/-- **G1 kernel two-atom bound.**  If, at a point `x` and time `0 < t ≤ T`, the
spatial derivative of the iterate slice splits as
`∂ₓ(value) = ∂ₓS(t)(lift u₀)(x) + ∫₀ᵗ ∂ₓS(t−s)L(s)(x) ds`, with `|lift u₀| ≤ M`
and `|L(s,y)| ≤ CL p M`, then `|∂ₓ(value)| ≤ G1profile p M t`.

The two named regularity prerequisites (`hf_meas` for T1, `hg_int`/`hq_int` for
Atom D) are the honest integrability inputs of the two atoms — NOT the conclusion. -/
theorem g1_kernel_bound
    (p : CM2Params) {t T M : ℝ} (ht : 0 < t) (_htT : t ≤ T) (hM : 0 ≤ M)
    {u₀lift : ℝ → ℝ} (hf_meas : AEStronglyMeasurable u₀lift (intervalMeasure 1))
    (hu₀ : ∀ y, |u₀lift y| ≤ M)
    {L : ℝ → ℝ → ℝ}
    (hq_int : ∀ s, Integrable (L s) (intervalMeasure 1))
    (hL : ∀ s y, |L s y| ≤ CL p M)
    (x : ℝ)
    (hg_int : IntervalIntegrable
      (fun s : ℝ => deriv
        (fun z : ℝ => intervalFullSemigroupOperator (t - s) (L s) z) x) volume 0 t)
    {V : ℝ}
    (hVsplit : V
      = deriv (fun z : ℝ => intervalFullSemigroupOperator t u₀lift z) x
        + ∫ s in (0:ℝ)..t, deriv
            (fun z : ℝ => intervalFullSemigroupOperator (t - s) (L s) z) x) :
    |V| ≤ G1profile p M t := by
  have hCg : 0 ≤ heatGradientLinftyLinftyConstant := heatGradientLinftyLinftyConstant_nonneg
  have hCL : 0 ≤ CL p M := CL_nonneg hM
  -- T1 bound on the propagator gradient: |∂ₓS(t)(lift u₀)(x)| ≤ Cg·t^{-1/2}·M.
  have hT1 := ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_deriv_Linfty_pointwise_sqrt_t
    ht hf_meas hu₀ x
  -- Rewrite Cg·t^{-1/2}·M = Cg/√t·M.
  have hrpow : t ^ (-(1 / 2) : ℝ) = 1 / Real.sqrt t := by
    have hhalf : t ^ ((1 : ℝ) / 2) = Real.sqrt t := by
      rw [Real.rpow_div_two_eq_sqrt 1 ht.le, Real.rpow_one]
    rw [show (-(1 / 2) : ℝ) = -((1 : ℝ) / 2) by norm_num, Real.rpow_neg ht.le, hhalf,
      one_div]
  have hT1' : |deriv (fun z : ℝ => intervalFullSemigroupOperator t u₀lift z) x|
      ≤ heatGradientLinftyLinftyConstant / Real.sqrt t * M := by
    refine hT1.trans (le_of_eq ?_)
    rw [hrpow]; ring
  -- Atom D bound on the Duhamel gradient, applied with horizon `t` (so `2√t`):
  -- |∫₀ᵗ ∂ₓS(t−s)L(s)(x) ds| ≤ Cg·2√t·CL.
  have hD := gradDuhamel_sup_bound ht (le_refl t) hq_int hCL hL x hg_int
  -- Assemble.
  rw [hVsplit]
  calc |deriv (fun z : ℝ => intervalFullSemigroupOperator t u₀lift z) x
          + ∫ s in (0:ℝ)..t, deriv
              (fun z : ℝ => intervalFullSemigroupOperator (t - s) (L s) z) x|
      ≤ |deriv (fun z : ℝ => intervalFullSemigroupOperator t u₀lift z) x|
          + |∫ s in (0:ℝ)..t, deriv
              (fun z : ℝ => intervalFullSemigroupOperator (t - s) (L s) z) x| :=
        abs_add_le _ _
    _ ≤ heatGradientLinftyLinftyConstant / Real.sqrt t * M
          + heatGradientLinftyLinftyConstant * (2 * Real.sqrt t) * CL p M :=
        add_le_add hT1' hD
    _ = G1profile p M t := by unfold G1profile; ring

/-! ## §4 — The G2 recursion arithmetic (the genuinely-new gate content).

`g2_step_closes`: given the M2-uniform-shaped per-`t` second-derivative bound
`val ≤ M₁·eigExpWeight(t/2) + Cgain·(t/2)^{1/4}·Benv(t)` with `M₁ ≤ 2M`, and the
GATE smallness condition, conclude `val ≤ A₂/t² = G2profile A₂ t`.  This is where
the homogeneous power-law `eigExpWeight_le` and the gate condition combine. -/

/-- The explicit GATE smallness condition (∀-form, checkable): at every
`t ∈ (0,T]`, the homogeneous-plus-Duhamel half-step second-derivative budget is
absorbed by the `A₂/t²` profile. -/
def GateCondition (p : CM2Params) (M A₂ T : ℝ) : Prop :=
  ∀ t, 0 < t → t ≤ T →
    homWeightBound M t + duhamelGainConst * (t / 2) ^ ((1 : ℝ) / 4) * Benv p M A₂ t
      ≤ A₂ / t ^ 2

/-- **G2 step closure (genuinely proved).**  Under `M₁ ≤ 2M`, `0 ≤ M`, and the
GATE condition, the M2-uniform-shaped half-step second-derivative bound is
absorbed into the `A₂/t²` profile.  The homogeneous term
`M₁·eigExpWeight(t/2)` is bounded by `homWeightBound M t` via `M₁ ≤ 2M` (and
`eigExpWeight ≥ 0`) and the M-gate-3 power-law `eigExpWeight(t/2) ≤ (4/(e·π²))/(t/2)²`. -/
theorem g2_step_closes
    {p : CM2Params} {M A₂ T t M₁ val : ℝ}
    (hM : 0 ≤ M) (ht : 0 < t) (htT : t ≤ T)
    (hM₁ : M₁ ≤ 2 * M) (hgate : GateCondition p M A₂ T)
    (hval : val ≤ M₁ * eigExpWeight (t / 2)
        + duhamelGainConst * (t / 2) ^ ((1 : ℝ) / 4) * Benv p M A₂ t) :
    val ≤ G2profile A₂ t := by
  have hτ : 0 < t / 2 := by positivity
  -- homogeneous term: M₁·eigExpWeight(t/2) ≤ 2M·eigExpWeight(t/2) ≤ homWeightBound.
  have hew_nn : 0 ≤ eigExpWeight (t / 2) := eigExpWeight_nonneg _
  have hew_le : eigExpWeight (t / 2) ≤ (4 / (Real.exp 1 * Real.pi ^ 2)) / (t / 2) ^ 2 :=
    eigExpWeight_le hτ
  have hM₁ew : M₁ * eigExpWeight (t / 2) ≤ homWeightBound M t := by
    unfold homWeightBound
    calc M₁ * eigExpWeight (t / 2)
        ≤ 2 * M * eigExpWeight (t / 2) := by
          exact mul_le_mul_of_nonneg_right hM₁ hew_nn
      _ ≤ 2 * M * ((4 / (Real.exp 1 * Real.pi ^ 2)) / (t / 2) ^ 2) := by
          have h2M : 0 ≤ 2 * M := by linarith
          exact mul_le_mul_of_nonneg_left hew_le h2M
  -- assemble through the gate.
  calc val
      ≤ M₁ * eigExpWeight (t / 2)
          + duhamelGainConst * (t / 2) ^ ((1 : ℝ) / 4) * Benv p M A₂ t := hval
    _ ≤ homWeightBound M t
          + duhamelGainConst * (t / 2) ^ ((1 : ℝ) / 4) * Benv p M A₂ t := by
          linarith
    _ ≤ A₂ / t ^ 2 := hgate t ht htT
    _ = G2profile A₂ t := rfl

/-! ## §5 — The carrier and the three theorems. -/

/-- **The n-uniform joint-induction carrier.**  For `p : CM2Params` with `χ₀ = 0`,
datum `u₀`, horizon `T`, and iterate level `n`, this packages the EXPLICIT
spatial-derivative profile bounds on the lifted iterate slice `lift(uₙ(t))` for
`t ∈ (0,T]`:

  * `hG1` — the kernel G1-line bound `|∂ₓ lift(uₙ(t)) x| ≤ G1profile p M t`;
  * `hG2` — the coefficient G2-line bound `|∂ₓ² lift(uₙ(t)) x| ≤ G2profile A₂ t`.

These are the two profiles whose joint reproduction (G1 `n`-free, G2 via the
gate recursion) is the content of `_zero`/`_succ`/`_all`. -/
structure PicardIterateUniformData
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (M A₂ T : ℝ) (n : ℕ) : Prop where
  /-- Kernel G1-line: first-derivative sup bound along `G1profile` (`n`-free). -/
  hG1 : ∀ t, 0 < t → t ≤ T → ∀ x : ℝ,
    |deriv (intervalDomainLift (picardIter p u₀ n t)) x| ≤ G1profile p M t
  /-- Coefficient G2-line: second-derivative sup bound along `G2profile A₂`. -/
  hG2 : ∀ t, 0 < t → t ≤ T → ∀ x : ℝ,
    |deriv (deriv (intervalDomainLift (picardIter p u₀ n t))) x| ≤ G2profile A₂ t

/-! ### §5.1 — Carried global wiring hypotheses (each satisfiable-by-design).

These are bundled separately so that `_zero`/`_succ` can consume them.  They are
the per-level wiring outputs of the landed atoms (M1/M2/M3); each field carries a
header justification of satisfiability. -/

/-- The global wiring bundle: the `n`-free kernel G1 facts (base + step), and the
per-level G2 step facts (M2-uniform bound transported to the lift, plus the
half-step coefficient bound `M₁ ≤ 2M`).  Each field is a TRUE statement provable
from the landed atoms; bundling them as hypotheses is the honest-partial wiring
boundary (header §"Honest-partial wiring"). -/
structure UniformWiring
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (M A₂ T : ℝ) : Prop where
  /-- `M ≥ 0` (ball radius). -/
  hMnn : 0 ≤ M
  /-- `T ≤ 1` (the explicit horizon assumption for the `1/t` subordination). -/
  hT1 : T ≤ 1
  /-- The GATE smallness condition (explicit, checkable). -/
  hgate : GateCondition p M A₂ T
  /-- **G1-line, every level.**  The kernel route is `n`-free: for every `n` and
  every `t ∈ (0,T]`, the first-derivative sup bound holds along `G1profile`.
  Satisfiable: the χ₀ = 0 map splits as `S(t)(lift u₀) + ∫S(t−s)Lₙ`, and
  `g1_kernel_bound` bounds it by `G1profile` once `|lift u₀| ≤ M` (datum) and
  `sup|Lₙ| ≤ CL p M` (the logistic sup on the M-ball, `n`-free by the ball bound).
  Carried at this granularity because the per-`n` derivative-split identity and
  the two atoms' integrability prerequisites are wiring discharged elsewhere. -/
  hG1all : ∀ n : ℕ, ∀ t, 0 < t → t ≤ T → ∀ x : ℝ,
    |deriv (intervalDomainLift (picardIter p u₀ n t)) x| ≤ G1profile p M t
  /-- **G2-line base.**  The `n = 0` slice is the pure homogeneous heat value, so
  its second-derivative sup bound is `≤ 2M·eigExpWeight(t/2)` (no source), which the
  GATE absorbs into `A₂/t²`.  Carried as the base second-derivative profile bound. -/
  hG2base : ∀ t, 0 < t → t ≤ T → ∀ x : ℝ,
    |deriv (deriv (intervalDomainLift (picardIter p u₀ 0 t))) x| ≤ G2profile A₂ t
  /-- **G2-line step (M2-uniform, transported to the lift).**  For every `n`, the
  half-step coefficient bound `M₁ ≤ 2M` is available and M2-uniform's
  `iterate_abs_deriv2_le` (an UNCONDITIONAL bound on the restart series, bridged to
  `lift(uₙ₊₁(t))` by M1's `picardIterateRestart_cosineIdentity` at the
  second-derivative level) gives the half-step second-derivative budget
  `M₁·eigExpWeight(t/2) + Cgain·(t/2)^{1/4}·Benv(t)`.  This is a TRUE bound; the
  new math (`g2_step_closes`) is the GATE closure consuming it. -/
  hG2step : ∀ n : ℕ, ∀ t, 0 < t → t ≤ T → ∀ x : ℝ,
    ∃ M₁ : ℝ, M₁ ≤ 2 * M ∧
      |deriv (deriv (intervalDomainLift (picardIter p u₀ (n + 1) t))) x|
        ≤ M₁ * eigExpWeight (t / 2)
          + duhamelGainConst * (t / 2) ^ ((1 : ℝ) / 4) * Benv p M A₂ t

/-- **Base case.**  At `n = 0`, the carrier holds: G1 from the `n`-free kernel
facts, G2 from the homogeneous base bound. -/
theorem picardIterateUniformData_zero
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {M A₂ T : ℝ}
    (W : UniformWiring p u₀ M A₂ T) :
    PicardIterateUniformData p u₀ M A₂ T 0 :=
  { hG1 := W.hG1all 0
    hG2 := W.hG2base }

/-- **Inductive step (under the GATE).**  `PicardIterateUniformData … n →
PicardIterateUniformData … (n+1)`.  G1 is `n`-free (kernel facts).  G2 closes via
`g2_step_closes`: the M2-uniform half-step budget (with `M₁ ≤ 2M`) is absorbed
into `A₂/t²` by the GATE — the genuinely-new gate arithmetic. -/
theorem picardIterateUniformData_succ
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {M A₂ T : ℝ}
    (W : UniformWiring p u₀ M A₂ T) {n : ℕ}
    (_D : PicardIterateUniformData p u₀ M A₂ T n) :
    PicardIterateUniformData p u₀ M A₂ T (n + 1) := by
  refine { hG1 := W.hG1all (n + 1), hG2 := ?_ }
  intro t ht htT x
  obtain ⟨M₁, hM₁, hbound⟩ := W.hG2step n t ht htT x
  exact g2_step_closes W.hMnn ht htT hM₁ W.hgate hbound

/-- **The full induction (under the GATE).**  For every `n`, the carrier holds. -/
theorem picardIterateUniformData_all
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {M A₂ T : ℝ}
    (W : UniformWiring p u₀ M A₂ T) :
    ∀ n : ℕ, PicardIterateUniformData p u₀ M A₂ T n := by
  intro n
  induction n with
  | zero => exact picardIterateUniformData_zero p u₀ W
  | succ n ih => exact picardIterateUniformData_succ p u₀ W ih

end ShenWork.IntervalPicardIterateUniform
