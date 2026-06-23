/-
  ShenWork/Paper1/RotheFloorResidualImpl.lean

  Attack atom #4 — producing `RotheFloorResidual p c lam M κ Λ u` (WaveRotheFloor.lean)
  for a trapped frozen profile `u`, by wiring the LANDED leaf pieces into the
  matching floor fields and isolating the genuinely-uncommitted analytic data.

  `RotheFloorResidual.produce` is, for every trapped antitone super-solution `Z`,
  a single flattened `Σ'`-tuple bundling the produced Green iterate `W`, its source
  `R`, the chem constant + smallness, the whole analytic ∧-chain (Green repr / conv
  form / source regularity / `step_op` / `step_eq` / lower trap), the two-sided
  tails for both barriers `Z` and `Ū`, the at-max `C²`/range data, and the two
  `RotheStepChemData` slots.  This file shows that — given exactly the per-`Z`
  genuinely-uncommitted analytic inputs (the flux-IBP step equation, the source
  identity/antitonicity, the source two-sided limits, the lower trap, the elliptic
  comparison signs, the at-max regularity) packaged as ONE precisely-named per-step
  data structure `RotheFloorStepData` — the ENTIRE tuple assembles unconditionally
  from the committed bricks.

  STRUCTURE (per the task's (i)/(ii)/(iii)):

  (i)  WIRE the landed parts.  Every tuple field that is a pure consequence of the
       bounded Green-source representation `W = greenConv c lam R` is discharged
       from the committed leaf bricks:
         - `green_repr`/`conv_form`            — `kernelConv_eq_greenConv` +
                                                  the two-sided conv integrabilities;
         - `R_cont`/`R_bound`/`R_hi`/`R_lo`/`R_int_trans` — the bounded-source bricks;
         - `step_op`                            — `frozenImplicitStepOp_of_greenConv_crossSource`
                                                  (the landed non-paper `step_op`);
         - the two-sided `W − Z` / `W − Ū` TAILS — `rotheStepTails_greenConv_of_barrier_limits`
                                                  / `…_upperBarrier` (GreenConvTails).

  (ii) ATTACK the genuinely-uncommitted fields by isolating them as the precisely-
       named inputs of `RotheFloorStepData`:
         - `step_eq : W = crossImplicitMap p c lam u Z W` — the realized flux IBP;
         - `Antitone R` — source antitonicity;
         - `hnonneg : 0 ≤ W` — the lower trap (resolvent positivity on `R ≥ 0`);
         - the elliptic comparison signs `Rbot·λ⁻¹ ≤ {M,Z(±∞)}`, `Rtop·λ⁻¹ ≤ {0,…}`;
         - the at-max `BC2`/`range` and the two `RotheStepChemData` packets.

  (iii) CARRY the irreducible rest precisely as `RotheFloorStepData` (per trapped
        `Z`) + the `baseSuper` whole-line super-barrier seed.  See the foot STALL.

  HONEST LABEL.  `RotheFloorResidual` is NOT produced unconditionally for an
  arbitrary trapped `u`: the per-`Z` flux-IBP step equation, the source
  antitonicity, the whole-line source limits, and the elliptic comparison signs are
  the genuinely-uncommitted §3.3 analytic content (no committed brick synthesizes
  them from the trap).  What IS unconditional here is the ASSEMBLY: every tuple
  field that follows from the bounded Green-source representation is wired from the
  landed bricks, so the residual is localized EXACTLY to `RotheFloorStepData`.

  HARD RULES: new file only; no sorry/admit/native_decide/axiom; Mathlib v4.29.1;
  lines ≤100.  §3.3 lower-pinned route only; non-circular.
-/
import ShenWork.Paper1.WaveRotheFloor
import ShenWork.Paper1.RotheStepOutputImpl
import ShenWork.Paper1.RotheMaxDataImpl
import ShenWork.Paper1.GreenConvTails
import ShenWork.Paper1.WavePaperStationaryFloor

open Filter Topology MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

set_option autoImplicit false

variable {c lam : ℝ}

/-! ## 1. The per-`Z` genuinely-uncommitted analytic data

`RotheFloorStepData p c lam M κ Λ u Z` carries, for ONE trapped antitone
super-solution `Z`, EXACTLY the analytic inputs the `RotheFloorResidual.produce`
tuple needs but the committed bricks cannot synthesize.  The produced iterate is
`W = greenConv c lam R`; `R = crossSource …` is the source identity.  Every field
is a genuine analytic obligation (never the tuple's conclusion). -/
structure RotheFloorStepData
    (p : CMParams) (c lam M κ Λ : ℝ) (u Z : ℝ → ℝ) where
  /-- The Green source `R`, the produced iterate being `W = greenConv c lam R`. -/
  R : ℝ → ℝ
  /-- Uniform source bound. -/
  B : ℝ
  /-- Chem residual constant. -/
  C_chem : ℝ
  /-- Source one-sided limit at `−∞`. -/
  Rbot : ℝ
  /-- Source one-sided limit at `+∞`. -/
  Rtop : ℝ
  /-- Source identity: `R = crossSource p lam u Z (greenConv c lam R)`. -/
  hR : R = crossSource p lam u Z (fun x => greenConv c lam R x)
  hRcont : Continuous R
  hRbd : ∀ y, |R y| ≤ B
  hΛ : Λ = 2 * (greenDelta c lam)⁻¹ * B
  hRanti : Antitone R
  hRbot : Tendsto R atBot (𝓝 Rbot)
  hRtop : Tendsto R atTop (𝓝 Rtop)
  /-- The realized flux-IBP step equation (genuinely uncommitted). -/
  hstep_eq : (fun x => greenConv c lam R x) = crossImplicitMap p c lam u Z
      (fun x => greenConv c lam R x)
  /-- The lower trap `0 ≤ W` (resolvent positivity on a nonnegative source). -/
  hnonneg : ∀ x, 0 ≤ greenConv c lam R x
  hCnn : 0 ≤ C_chem
  hCB : (1 / lam) * (reactionLip p.α M + C_chem) < 1
  /-- Descent-barrier endpoint limit at `−∞`. -/
  Zbot : ℝ
  /-- Descent-barrier endpoint limit at `+∞`. -/
  Ztop : ℝ
  hZcont : Continuous Z
  hZbotlim : Tendsto Z atBot (𝓝 Zbot)
  hZtoplim : Tendsto Z atTop (𝓝 Ztop)
  hZle_bot : Rbot * lam⁻¹ ≤ Zbot
  hZle_top : Rtop * lam⁻¹ ≤ Ztop
  /-- Upper-barrier endpoint orderings `Rbot·λ⁻¹ ≤ M`, `Rtop·λ⁻¹ ≤ 0`. -/
  hBle_bot : Rbot * lam⁻¹ ≤ M
  hBle_top : Rtop * lam⁻¹ ≤ 0
  /-- At-max `C²`/range + chem data for the descent barrier `Z`. -/
  hBC2Z : ∀ x₀, IsMaxOn (fun x => greenConv c lam R x - Z x) Set.univ x₀ →
    ContDiffAt ℝ 2 Z x₀
  hrangeZ : ∀ x₀, IsMaxOn (fun x => greenConv c lam R x - Z x) Set.univ x₀ →
    greenConv c lam R x₀ ∈ Set.Icc (0 : ℝ) M ∧ Z x₀ ∈ Set.Icc (0 : ℝ) M
  hchemZ : ∀ x₀, IsMaxOn (fun x => greenConv c lam R x - Z x) Set.univ x₀ →
    RotheStepChemData p u (fun x => greenConv c lam R x) Z C_chem x₀
  /-- At-max `C²`/range + chem data for the super-barrier `Ū`. -/
  hBC2B : ∀ x₀, IsMaxOn (fun x => greenConv c lam R x - upperBarrier κ M x)
      Set.univ x₀ → ContDiffAt ℝ 2 (upperBarrier κ M) x₀
  hrangeB : ∀ x₀, IsMaxOn (fun x => greenConv c lam R x - upperBarrier κ M x)
      Set.univ x₀ → greenConv c lam R x₀ ∈ Set.Icc (0 : ℝ) M ∧
      upperBarrier κ M x₀ ∈ Set.Icc (0 : ℝ) M
  hchemB : ∀ x₀, IsMaxOn (fun x => greenConv c lam R x - upperBarrier κ M x)
      Set.univ x₀ → RotheStepChemData p u (fun x => greenConv c lam R x)
      (upperBarrier κ M) C_chem x₀
  /-- The antitone data packet feeding `chemFlux_increment_bound` shifts. -/
  hanti : RotheStepAntitoneData p c lam M C_chem u Z (fun x => greenConv c lam R x)

/-! ## 2. Assembling the `produce` tuple for one `Z` from the data.

Every field of the flat `Σ'`-tuple is discharged: the Green-repr/conv-form/source
regularity/`step_op`/tails from the landed bricks; the genuinely-uncommitted
fields (`step_eq`, `Antitone R`, `nonneg`, comparison signs, at-max data) directly
from `RotheFloorStepData`. -/

/-- **Per-`Z` tuple assembler.**  Given `0 < lam`, the per-`Z` analytic data and
the trapped `Z` preconditions, produce the exact `RotheFloorResidual.produce`
`Σ'`-payload.  `W := greenConv c lam d.R`. -/
def rotheFloorResidual_produce_of_data
    {p : CMParams} {M κ Λ : ℝ} {u Z : ℝ → ℝ}
    (hlam : 0 < lam) (hκ : 0 < κ) (hM : 0 ≤ M)
    (d : RotheFloorStepData p c lam M κ Λ u Z)
    (hbase : ∀ x, frozenWaveOperator p c u (upperBarrier κ M) x ≤ 0)
    (hZsuper : ∀ x, frozenWaveOperator p c u Z x ≤ 0)
    (hZB : ∀ x, Z x ≤ upperBarrier κ M x) :
    Σ' (W : ℝ → ℝ) (R : ℝ → ℝ) (C_chem LaZ LbZ LaB LbB : ℝ),
      ((W = fun x => greenConv c lam R x) ∧
      (W = fun x => ∫ y, greenKernel c lam (x - y) * R y) ∧
      Continuous R ∧
      (∃ B : ℝ, (∀ y, |R y| ≤ B) ∧ Λ = 2 * (greenDelta c lam)⁻¹ * B) ∧
      (∀ x, IntegrableOn (gWeight (greenRootPlus c lam) R) (Ioi x)) ∧
      (∀ x, IntegrableOn (gWeight (greenRootMinus c lam) R) (Iic x)) ∧
      Antitone R ∧
      (∀ x, Integrable (fun t => greenKernel c lam (-t) * R (x + t))) ∧
      (∀ x, implicitStepOp p c (1 / lam) u W x = Z x) ∧
      (∀ x, 0 ≤ W x) ∧
      (W = crossImplicitMap p c lam u Z W) ∧
      (0 ≤ C_chem) ∧
      ((1 / lam) * (reactionLip p.α M + C_chem) < 1) ∧
      (∀ x, frozenWaveOperator p c u Z x ≤ 0) ∧
      (∀ x, Z x ≤ Z x) ∧
      Continuous (fun x => W x - Z x) ∧
      Tendsto (fun x => W x - Z x) atBot (𝓝 LaZ) ∧ (LaZ ≤ 0) ∧
      Tendsto (fun x => W x - Z x) atTop (𝓝 LbZ) ∧ (LbZ ≤ 0) ∧
      (∀ x₀, IsMaxOn (fun x => W x - Z x) Set.univ x₀ → ContDiffAt ℝ 2 Z x₀) ∧
      (∀ x₀, IsMaxOn (fun x => W x - Z x) Set.univ x₀ →
        W x₀ ∈ Set.Icc (0 : ℝ) M ∧ Z x₀ ∈ Set.Icc (0 : ℝ) M) ∧
      (∀ x, frozenWaveOperator p c u (upperBarrier κ M) x ≤ 0) ∧
      (∀ x, Z x ≤ upperBarrier κ M x) ∧
      Continuous (fun x => W x - upperBarrier κ M x) ∧
      Tendsto (fun x => W x - upperBarrier κ M x) atBot (𝓝 LaB) ∧ (LaB ≤ 0) ∧
      Tendsto (fun x => W x - upperBarrier κ M x) atTop (𝓝 LbB) ∧ (LbB ≤ 0) ∧
      (∀ x₀, IsMaxOn (fun x => W x - upperBarrier κ M x) Set.univ x₀ →
        ContDiffAt ℝ 2 (upperBarrier κ M) x₀) ∧
      (∀ x₀, IsMaxOn (fun x => W x - upperBarrier κ M x) Set.univ x₀ →
        W x₀ ∈ Set.Icc (0 : ℝ) M ∧ upperBarrier κ M x₀ ∈ Set.Icc (0 : ℝ) M)) ×'
      (RotheStepAntitoneData p c lam M C_chem u Z W ×'
      ((∀ x₀, IsMaxOn (fun x => W x - Z x) Set.univ x₀ →
          RotheStepChemData p u W Z C_chem x₀) ×'
        (∀ x₀, IsMaxOn (fun x => W x - upperBarrier κ M x) Set.univ x₀ →
          RotheStepChemData p u W (upperBarrier κ M) C_chem x₀))) := by
  -- source two-sided integrabilities from the uniform bound
  have hRhi : ∀ t, IntegrableOn (gWeight (greenRootPlus c lam) d.R) (Ioi t) :=
    fun t => gWeight_integrableOn_Ioi_of_bounded
      (greenRootPlus_pos (c := c) hlam) d.hRcont d.hRbd t
  have hRlo : ∀ t, IntegrableOn (gWeight (greenRootMinus c lam) d.R) (Iic t) :=
    fun t => gWeight_integrableOn_Iic_of_bounded
      (greenRootMinus_neg (c := c) hlam) d.hRcont d.hRbd t
  -- conv-form via the two-sided convolution integrabilities
  have hconv : (fun x => greenConv c lam d.R x)
      = fun x => ∫ y, greenKernel c lam (x - y) * d.R y := by
    funext x
    exact (kernelConv_eq_greenConv (c := c) (lam := lam) d.R x
      (greenKernel_const_sub_mul_integrableOn_Iic_of_bounded hlam d.hRcont d.hRbd x)
      (greenKernel_const_sub_mul_integrableOn_Ioi_of_bounded hlam d.hRcont d.hRbd x)).symm
  -- the landed non-paper `step_op`
  have hstepop : ∀ x, implicitStepOp p c (1 / lam) u (fun x => greenConv c lam d.R x) x
      = Z x :=
    frozenImplicitStepOp_of_greenConv_crossSource (c := c) (lam := lam) hlam d.hR rfl
      d.hRcont hRhi hRlo
  -- the two-sided tails for both barriers, from GreenConvTails
  have htailsZ : RotheStepTails (fun x => greenConv c lam d.R x) Z :=
    rotheStepTails_greenConv_of_barrier_limits (c := c) (lam := lam)
      hlam d.hRcont d.hRbd d.hRbot d.hRtop d.hZcont d.hZbotlim d.hZtoplim
      d.hZle_bot d.hZle_top
  have htailsB : RotheStepTails (fun x => greenConv c lam d.R x) (upperBarrier κ M) :=
    rotheStepTails_greenConv_upperBarrier (c := c) (lam := lam)
      hlam hκ hM d.hRcont d.hRbd d.hRbot d.hRtop d.hBle_bot d.hBle_top
  refine ⟨fun x => greenConv c lam d.R x, d.R, d.C_chem,
    htailsZ.La, htailsZ.Lb, htailsB.La, htailsB.Lb,
    ⟨rfl, hconv, d.hRcont, ⟨d.B, d.hRbd, d.hΛ⟩, hRhi, hRlo, d.hRanti,
      fun x => greenKernel_neg_mul_translate_integrable_of_bounded
        (c := c) (lam := lam) hlam d.hRcont d.hRbd x,
      hstepop, d.hnonneg, d.hstep_eq, d.hCnn, d.hCB,
      hZsuper, fun _ => le_refl _, htailsZ.φcont,
      htailsZ.hbot, htailsZ.hLa, htailsZ.htop, htailsZ.hLb, d.hBC2Z, d.hrangeZ,
      hbase, hZB, htailsB.φcont,
      htailsB.hbot, htailsB.hLa, htailsB.htop, htailsB.hLb, d.hBC2B, d.hrangeB⟩,
    d.hanti, d.hchemZ, d.hchemB⟩

/-! ## 3. Assembling `RotheFloorResidual` from the floor seed + per-`Z` data.

The whole floor is the seed `baseSuper` (the committed whole-line super-barrier on
`u`) plus a producer giving, for every trapped antitone super-solution `Z`, the
per-`Z` analytic data `RotheFloorStepData`.  The `produce` field then assembles the
tuple field-for-field via `rotheFloorResidual_produce_of_data`. -/

/-- **`rotheFloorResidual_of_data` — the floor from the seed + per-`Z` data.**
Given `0 < lam`, `0 < κ`, `0 ≤ M`, the whole-line super-barrier seed `hbase`, and a
producer of `RotheFloorStepData` for every trapped antitone super-solution `Z`,
assemble `RotheFloorResidual p c lam M κ Λ u`.  Non-circular: the per-`Z` data is
the genuinely-uncommitted analytic input, never the tuple's conclusion. -/
def rotheFloorResidual_of_data
    {p : CMParams} {M κ Λ : ℝ} {u : ℝ → ℝ}
    (hlam : 0 < lam) (hκ : 0 < κ) (hM : 0 ≤ M)
    (hbase : ∀ x, frozenWaveOperator p c u (upperBarrier κ M) x ≤ 0)
    (hdata : ∀ Z : ℝ → ℝ, Continuous Z → Antitone Z → (∀ x, 0 ≤ Z x) →
        (∀ x, Z x ≤ upperBarrier κ M x) → (∀ x, frozenWaveOperator p c u Z x ≤ 0) →
        RotheFloorStepData p c lam M κ Λ u Z) :
    RotheFloorResidual p c lam M κ Λ u where
  hlam := hlam
  hM := hM
  baseSuper := hbase
  produce := fun Z hZc hZa hZ0 hZB hZsuper =>
    rotheFloorResidual_produce_of_data hlam hκ hM (hdata Z hZc hZa hZ0 hZB hZsuper)
      hbase hZsuper hZB

/-- **`rotheStepFloor_of_data` — chain through to the per-step floor.**  Direct
composition `RotheFloorStepData producer → RotheFloorResidual → RotheStepFloor`. -/
def rotheStepFloor_of_data
    {p : CMParams} {M κ Λ : ℝ} {u : ℝ → ℝ}
    (hlam : 0 < lam) (hκ : 0 < κ) (hM : 0 ≤ M)
    (hbase : ∀ x, frozenWaveOperator p c u (upperBarrier κ M) x ≤ 0)
    (hdata : ∀ Z : ℝ → ℝ, Continuous Z → Antitone Z → (∀ x, 0 ≤ Z x) →
        (∀ x, Z x ≤ upperBarrier κ M x) → (∀ x, frozenWaveOperator p c u Z x ≤ 0) →
        RotheFloorStepData p c lam M κ Λ u Z) :
    RotheStepFloor p c lam M κ Λ u :=
  rotheStepFloor_of_residual (rotheFloorResidual_of_data hlam hκ hM hbase hdata)

/-
================================================================================
PRECISE STALL — closed unconditionally vs. carried, and exactly why.
================================================================================

WHAT IS ASSEMBLED UNCONDITIONALLY (no carried hypotheses beyond the per-`Z`
`RotheFloorStepData` and the whole-line super-barrier seed):

  * `rotheFloorResidual_produce_of_data` — the ENTIRE `RotheFloorResidual.produce`
    flat `Σ'`-tuple for one trapped antitone super-solution `Z`, with `W :=
    greenConv c lam d.R`.  Every field that is a consequence of the bounded
    Green-source representation is WIRED from the landed leaf bricks:
      - `green_repr`        := `rfl` (W defined as the Green conv);
      - `conv_form`         := `kernelConv_eq_greenConv` + the two-sided conv
                               integrabilities (`greenKernel_const_sub_mul_…`);
      - `R_cont`/`R_bound`/`R_hi`/`R_lo` := the bounded-source bricks
                               (`gWeight_integrableOn_{Ioi,Iic}_of_bounded`);
      - `R_int_trans`       := `greenKernel_neg_mul_translate_integrable_of_bounded`;
      - `step_op`           := the LANDED `frozenImplicitStepOp_of_greenConv_crossSource`;
      - the two-sided `W − Z` / `W − Ū` TAILS (φcont/La/Lb/hbot/hLa/htop/hLb)
                            := `rotheStepTails_greenConv_of_barrier_limits` /
                               `rotheStepTails_greenConv_upperBarrier` (GreenConvTails);
      - `Z ≤ Z`             := `le_refl`.

  * `rotheFloorResidual_of_data` — wraps the per-`Z` assembler into the full
    `RotheFloorResidual` structure, with `baseSuper` the committed whole-line
    super-barrier seed.

  * `rotheStepFloor_of_data` — chains to `RotheStepFloor` via the committed
    `rotheStepFloor_of_residual`.

  All three are axiom-clean (only the committed bricks, which are
  propext/Classical.choice/Quot.sound).

CARRIED (the genuinely-uncommitted §3.3 analytic content, isolated EXACTLY into the
per-`Z` `RotheFloorStepData`; NOT closeable from committed bricks here, NOT
vacuous, NOT over-strong, NOT the conclusion):

 (A) THE REALIZED FLUX-IBP STEP EQUATION `hstep_eq`:
       `greenConv c lam R = crossImplicitMap p c lam u Z (greenConv c lam R)`.
     This is the divergence-form output of the per-step solve.  Producing it from
     `crossStep_concrete_solution` (RotheStepProducerImpl.lean) routes through
     `crossStepSelfMap_apply_eq_crossImplicitMap` (WaveStepFluxId.lean:80), which
     carries ~14 per-`x` integrability/decay/folding hypotheses.  REAL ANALYTIC
     GAP (whole-line flux IBP), not circularity.

 (B) THE SOURCE IDENTITY + ANTITONICITY `hR` / `hRanti`:
       `R = crossSource p lam u Z (greenConv c lam R)`, `Antitone R`.
     The source-antitone content (the chemotaxis flux divergence is antitone on
     the lower-pinned orbit).  No committed brick gives `Antitone (crossSource …)`.
     REAL GAP.

 (C) THE WHOLE-LINE SOURCE LIMITS `hRbot`/`hRtop` (`R → Rbot`/`Rtop` at ∓∞) and the
     ELLIPTIC COMPARISON SIGNS `hZle_bot`/`hZle_top`/`hBle_bot`/`hBle_top`
     (`Rbot·λ⁻¹ ≤ {Zbot, M}`, `Rtop·λ⁻¹ ≤ {Ztop, 0}`).  The source has whole-line
     limits (Green decay) and they sit below the barrier endpoints — the §3.3
     ordering content.  The TAIL ASSEMBLY from these is wired (GreenConvTails); the
     limits/signs themselves are the carried orbit data.  REAL GAP.

 (D) THE LOWER TRAP `hnonneg` (`0 ≤ greenConv c lam R`): resolvent positivity on a
     nonnegative source; the at-max `BC2`/`range` regularity; and the two
     `RotheStepChemData` packets + `RotheStepAntitoneData`.  These are the at-max
     elliptic regularity/chem-residual data (the committed chem brick consumes
     them via `rotheStep_chem_bound`); carried verbatim per max point.

 (E) THE WHOLE-LINE SUPER-BARRIER SEED `hbase` (`F_u(Ū) ≤ 0`).  Discharged
     OUTRIGHT downstream by `whole_line_super_barrier` on the trapped `u` (see
     `rotheMaxData_barrier`, RotheMaxDataImpl.lean) — so it is NOT a genuine gap,
     only threaded here as the floor seed.

EXACT STALL LOCATION.  The single carried object is `RotheFloorStepData p c lam M
κ Λ u Z` — the `hdata` argument of `rotheFloorResidual_of_data`.  Its fields (A)–(D)
are the genuinely-uncommitted per-step flux-IBP / source-antitone / whole-line
Green-decay analytic data the task names.  MISSING LEMMA SIGNATURE (the smallest
closing step, were a trapped `u` fixed):
  `rotheFloorStepData_of_trap :
     InMonotoneWaveTrapSet κ M u → (per-step contraction smallness) →
     ∀ Z, (trapped antitone super-solution) → RotheFloorStepData p c lam M κ Λ u Z`,
whose proof must discharge (A) the flux IBP from
`crossStepSelfMap_apply_eq_crossImplicitMap` + the ~14 integrability hyps, (B) the
source antitonicity from the chemotaxis-flux sign on the orbit, (C) the Green-decay
limits + comparison signs, and (D) the at-max elliptic regularity.  This CONSUMES
the trap + the per-step solve; it does not re-assume `RotheFloorResidual`/
`RotheStepFloor` — no circularity.

HONEST LABEL: `RotheFloorResidual` is NOT produced unconditionally for an arbitrary
trapped `u`.  The ASSEMBLY (every tuple field following from the bounded
Green-source representation) IS unconditional and axiom-clean; the residual is
localized EXACTLY to the per-`Z` `RotheFloorStepData` (A)–(D).  No vacuity, no
over-strong hyps, no FALSE bare-trap, no circularity.
================================================================================
-/

section AxiomAudit
#print axioms rotheFloorResidual_produce_of_data
#print axioms rotheFloorResidual_of_data
#print axioms rotheStepFloor_of_data
end AxiomAudit

end ShenWork.Paper1
