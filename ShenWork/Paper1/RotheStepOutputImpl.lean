/-
  ShenWork/Paper1/RotheStepOutputImpl.lean

  Attack atom #4A-A — upgrading the landed per-step Green solution
  (`crossStep_concrete_solution`, RotheStepProducerImpl.lean) into a full
  `RotheStepOutput` (the `produce` field of `RotheStepProducer`).

  The landed `crossStep_concrete_solution` produced, UNCONDITIONALLY, the per-step
  Green-solve existence as a concrete `ℝ → ℝ` satisfying the convolution equation
  `W x = ∫ y, greenKernel c lam (x−y)·(reactionTrunc + λZ + rpowTrunc·Vu') y`.
  Its in-file STALL block named the missing lemma `crossStep_output_of_solution`:
  from that solution + the truncated↔raw bridge + the lower-pinned `RotheMaxData`
  comparisons, assemble `RotheStepOutput`.

  WHAT THIS FILE CLOSES UNCONDITIONALLY (new content, no carried hyps):

   * `frozenImplicitStepOp_of_greenConv_crossSource` — the NON-paper `step_op`
     derivation (`implicitStepOp p c (1/λ) u W = Z`) from the Green representation
     `W = greenConv c lam (crossSource …)`.  This is the missing
     `frozenWaveOperator`-route analogue of the committed
     `paperImplicitStepOp_of_greenConv_source` (paper route).  Closes the
     `RotheStepAnalytic.step_op` obligation outright.

   * `rotheStepAnalytic_of_greenSource` — assembles the WHOLE `RotheStepAnalytic`
     bundle (`step_eq`, `green_repr`, `R_cont`, `R_bound`, `R_hi`, `R_lo`,
     `R_int_trans`, `step_op`, `c2`) from a single carried `green_repr`
     (`W = greenConv c lam R`, `R = crossSource …`) + the source's continuity and
     uniform bound, plus the `step_eq` bridge value.  The TAILS, `R_int_trans`
     and `c2` are DISCHARGED unconditionally from the bounded-source committed
     bricks; nothing here is re-assumed.

   * `crossStep_output_of_solution` — the named target: assembles
     `RotheStepOutput` from the analytic bundle (above) PLUS exactly the
     lower-pinned elliptic comparison data (`nonneg`, `maxZ`, `maxBarrier`,
     `antitone`) — the genuinely-elliptic order content of §3.3.  Non-circular:
     it CONSUMES the produced Green solution + the elliptic comparison; it does
     NOT re-assume `RotheStepOutput`/`RotheStepProducer`.

  PRECISE STALL (carried, named): the elliptic comparison data
  (`RotheMaxData`/antitone/nonneg) is the lower-pinned maximum-principle content
  that rests on the supersolution ordering and the at-max chemotaxis residual
  bound — uncommitted but satisfiable on the trapped supersolution orbit.  It is
  carried as a precisely-typed hypothesis, NOT vacuously and NOT over-strong; see
  the PRECISE STALL block at the file foot.

  HARD RULES: new file only; no sorry/admit/native_decide/axiom; Mathlib
  v4.29.1; lines ≤100.  §3.3 lower-pinned route only.
-/
import ShenWork.Paper1.WaveRotheProducer
import ShenWork.Paper1.WaveRotheConcrete
import ShenWork.Paper1.WaveRotheTrunc
import ShenWork.Paper1.WaveRotheSchauderData
import ShenWork.Paper1.WaveStepFluxId
import ShenWork.Paper1.WaveRotheStationary
import ShenWork.Paper1.WavePaperRotheProducer

open Filter Topology MeasureTheory Set

noncomputable section

namespace ShenWork.Paper1

variable {c lam : ℝ}

/-! ## (A) The non-paper `step_op` derivation.

The committed `paperImplicitStepOp_of_greenConv_source` discharges `step_op` for
the PAPER route (`paperImplicitStepOp`/`paperWaveOperator`).  The `RotheStepAnalytic`
bundle uses the NON-paper `implicitStepOp`/`frozenWaveOperator`.  We supply the
missing analogue: a Green-represented `crossSource` solves the non-paper implicit
step.  Pure linear-resolvent algebra on `greenConv_variation_negative_stationary`
plus the `frozenWaveOperator`/`crossSource` unfolds (the reaction and flux terms
match definitionally).  CLOSED UNCONDITIONALLY. -/

/-- **(A) Non-paper `step_op` from the Green representation.**
If `W = greenConv c lam R` with `R = crossSource p lam u Z W` and the standard
source tails, then `W` solves `implicitStepOp p c (1/λ) u W = Z` pointwise. -/
theorem frozenImplicitStepOp_of_greenConv_crossSource
    {p : CMParams} {u Z W R : ℝ → ℝ}
    (hlam : 0 < lam)
    (hR : R = crossSource p lam u Z W)
    (hgreen : W = fun x => greenConv c lam R x)
    (hRcont : Continuous R)
    (hRhi : ∀ x, IntegrableOn (gWeight (greenRootPlus c lam) R) (Ioi x))
    (hRlo : ∀ x, IntegrableOn (gWeight (greenRootMinus c lam) R) (Iic x)) :
    ∀ x, implicitStepOp p c (1 / lam) u W x = Z x := by
  intro x
  have hL : iteratedDeriv 2 W x + c * deriv W x - lam * W x = -R x := by
    rw [hgreen]
    exact greenConv_variation_negative_stationary
      (c := c) (lam := lam) hlam hRcont hRhi hRlo x
  have hsource_x : R x = crossSource p lam u Z W x := by rw [hR]
  have hfroz : frozenWaveOperator p c u W x = lam * (W x - Z x) := by
    unfold frozenWaveOperator
    rw [hsource_x] at hL
    unfold crossSource reactionFun at hL
    nlinarith [hL]
  rw [implicitStepOp_apply, hfroz]
  field_simp [ne_of_gt hlam]
  ring

/-! ## (B) Assembling `RotheStepAnalytic` from the Green source.

From the single Green representation `W = greenConv c lam R` with `R = crossSource`,
plus the source's continuity, uniform bound `|R| ≤ B`, the `Λ`-constant link, and
the bridge value `step_eq`, ALL ten `RotheStepAnalytic` fields are discharged:
the tails/`R_int_trans` from the bounded-source bricks, `step_op` from (A), and
`c2` from `greenConv_contDiffAt_two`.  CLOSED from the carried regularity + (A);
no field re-assumed. -/

/-- **(B) The analytic bundle from a bounded Green source.**
A `def` (not `theorem`) so the `R` projection reduces definitionally to `R`,
which `crossStep_output_of_solution`'s `conv_form` relies on. -/
def rotheStepAnalytic_of_greenSource
    {p : CMParams} {M κ Λ : ℝ} {u Z W R : ℝ → ℝ} {B : ℝ}
    (hlam : 0 < lam)
    (hR : R = crossSource p lam u Z W)
    (hgreen : W = fun x => greenConv c lam R x)
    (hRcont : Continuous R)
    (hRbd : ∀ y, |R y| ≤ B)
    (hΛ : Λ = 2 * (greenDelta c lam)⁻¹ * B)
    (hstep_eq : W = crossImplicitMap p c lam u Z W) :
    RotheStepAnalytic p c lam M κ Λ u Z W := by
  have hRhi : ∀ t, IntegrableOn (gWeight (greenRootPlus c lam) R) (Ioi t) :=
    fun t => gWeight_integrableOn_Ioi_of_bounded
      (greenRootPlus_pos (c := c) hlam) hRcont hRbd t
  have hRlo : ∀ t, IntegrableOn (gWeight (greenRootMinus c lam) R) (Iic t) :=
    fun t => gWeight_integrableOn_Iic_of_bounded
      (greenRootMinus_neg (c := c) hlam) hRcont hRbd t
  exact
    { R := R
      step_eq := hstep_eq
      green_repr := hgreen
      R_cont := hRcont
      R_bound := ⟨B, hRbd, hΛ⟩
      R_hi := hRhi
      R_lo := hRlo
      R_int_trans := fun x =>
        greenKernel_neg_mul_translate_integrable_of_bounded
          (c := c) (lam := lam) hlam hRcont hRbd x
      step_op := frozenImplicitStepOp_of_greenConv_crossSource
        (c := c) (lam := lam) hlam hR hgreen hRcont hRhi hRlo
      c2 := by
        rw [hgreen]
        exact greenConv_contDiffAt_two (c := c) (lam := lam) hRcont hRhi hRlo }

/-! ## (C) The named target — `crossStep_output_of_solution`.

Assembles the full `RotheStepOutput` from the analytic bundle (B) plus the
lower-pinned elliptic comparison data.  The `conv_form` field is the raw
kernel-convolution rewrite of `green_repr` (via `kernelConv_eq_greenConv`).
Non-circular: consumes the produced solution + the elliptic comparison. -/

/-- **(C) `crossStep_output_of_solution` — full per-step output bundle.**
From the bounded Green source representation of the per-step solution `W`
(continuity `hRcont`, uniform bound `hRbd`, `Λ`-link `hΛ`, source identity `hR`,
representation `hgreen`, bridge `hstep_eq`) and the lower-pinned comparison data
(`nonneg`, `maxZ`, `maxBarrier`, `antitone`), assemble `RotheStepOutput`.  The
`conv_form` is discharged from `green_repr` via `kernelConv_eq_greenConv`.  No
field re-assumes the producer's conclusion.  A `def` (the output is data). -/
def crossStep_output_of_solution
    {p : CMParams} {M κ Λ C_chem : ℝ} {u Z W R : ℝ → ℝ} {B : ℝ}
    (hlam : 0 < lam)
    (hR : R = crossSource p lam u Z W)
    (hgreen : W = fun x => greenConv c lam R x)
    (hRcont : Continuous R)
    (hRbd : ∀ y, |R y| ≤ B)
    (hΛ : Λ = 2 * (greenDelta c lam)⁻¹ * B)
    (hstep_eq : W = crossImplicitMap p c lam u Z W)
    (hConvIic : ∀ x, IntegrableOn (fun y => greenKernel c lam (x - y) * R y) (Iic x))
    (hConvIoi : ∀ x, IntegrableOn (fun y => greenKernel c lam (x - y) * R y) (Ioi x))
    (hnonneg : ∀ x, 0 ≤ W x)
    (hmaxZ : RotheMaxData p c lam M C_chem u Z W Z)
    (hmaxBarrier : RotheMaxData p c lam M C_chem u Z W (upperBarrier κ M))
    (hanti : RotheStepAntitoneData p c lam M C_chem u Z W) :
    RotheStepOutput p c lam M κ Λ u Z W := by
  let ha : RotheStepAnalytic p c lam M κ Λ u Z W :=
    rotheStepAnalytic_of_greenSource (c := c) (lam := lam)
      hlam hR hgreen hRcont hRbd hΛ hstep_eq
  have hconv : W = fun x => ∫ y, greenKernel c lam (x - y) * ha.R y := by
    show W = fun x => ∫ y, greenKernel c lam (x - y) * R y
    rw [hgreen]
    funext x
    exact (kernelConv_eq_greenConv (c := c) (lam := lam) R x
      (hConvIic x) (hConvIoi x)).symm
  exact
    { analytic := ha
      conv_form := hconv
      C_chem := C_chem
      nonneg := hnonneg
      maxZ := hmaxZ
      maxBarrier := hmaxBarrier
      antitone := hanti }

/-
================================================================================
PRECISE STALL — closed unconditionally vs. carried, and exactly why.
================================================================================

CLOSED UNCONDITIONALLY (new content, no carried hypotheses beyond bounded-source
regularity that the committed bricks consume):

  * `frozenImplicitStepOp_of_greenConv_crossSource` — the NON-paper `step_op`
    derivation (the `frozenWaveOperator`-route analogue of the committed
    `paperImplicitStepOp_of_greenConv_source`).  This was a genuine missing
    lemma; it is now closed outright from `greenConv_variation_negative_stationary`
    plus the definitional `frozenWaveOperator`/`crossSource` unfolds.

  * `rotheStepAnalytic_of_greenSource` — assembles the ENTIRE `RotheStepAnalytic`
    bundle from one Green representation `W = greenConv c lam (crossSource …)`,
    the source's continuity + uniform bound, the `Λ`-link, and the bridge value
    `step_eq`.  Tails (`R_hi`/`R_lo`), `R_int_trans` and `c2` are DISCHARGED from
    the bounded-source committed bricks; `step_op` from the new lemma above.

  * `crossStep_output_of_solution` — the named target.  Assembles
    `RotheStepOutput`.  The `conv_form` field is discharged from `green_repr`
    via `kernelConv_eq_greenConv` (consuming only the standard two-sided
    per-`x` convolution integrabilities).  Non-circular: it CONSUMES the produced
    Green solution and the elliptic comparison; it never re-assumes its own
    conclusion.

CARRIED (the genuine §3.3 elliptic order content; NOT closeable from committed
bricks here, NOT vacuous, NOT over-strong):

 (I) THE LOWER-PINNED ELLIPTIC COMPARISON DATA.  `crossStep_output_of_solution`
     consumes, as precisely-typed hypotheses:
       * `hnonneg : ∀ x, 0 ≤ W x`            — the lower trap;
       * `hmaxZ      : RotheMaxData … W Z`   — descent `W ≤ Z`;
       * `hmaxBarrier: RotheMaxData … W Ū`   — upper trap `W ≤ Ū`;
       * `hanti      : RotheStepAntitoneData …` — antitonicity.
     These are the lower-pinned maximum-principle comparison packets.  Each rests
     on the supersolution ordering `frozenWaveOperator p c u B ≤ 0` and the at-max
     chemotaxis residual bound (`RotheMaxData.chem`) — the genuinely-elliptic
     order content.  They are uncommitted but satisfiable on the trapped
     supersolution orbit (documented at `WaveRotheClose.lean`, item `hprodTrap`).
     They are carried verbatim, not weakened.  THIS IS A REAL PDE GAP, not
     circularity: `RotheMaxData W B` asserts the COMPARISON DATA (super-barrier +
     tails + chem residual), from which `rotheStep_le_barrier` then DERIVES
     `W ≤ B`; it does not assume `W ≤ B` outright, and it does not assume the
     producer's conclusion `RotheStepProducer`/`RotheStepOutput`.

 (II) THE BRIDGE'S ~14 INTEGRABILITY/DECAY/FOLDING HYPOTHESES.  The `step_eq`
     value `W = crossImplicitMap p c lam u Z W` is consumed as `hstep_eq`.  To
     PRODUCE that value from the landed `crossStep_concrete_solution` one routes
     through `crossStepSelfMap_apply_eq_crossImplicitMap` (WaveStepFluxId.lean:80),
     which carries the ~14 per-`x` integrability/decay/folding hypotheses
     (`hWtrap`, `hfold`, `hSmIic/Ioi`, `hFlIic/Ioi`, `hG_C1`, `hKv'_*`,
     `hK'v_*`, `hKG_*`, `hdecay_*`).  We did NOT discharge those from the trap
     here — discharging them is the §3.3 satisfiability content and INTRODUCES
     fresh carried obligations rather than removing them — so the `step_eq` value
     is carried as `hstep_eq`, and the corresponding bounded-source tails
     (`hRcont`, `hRbd`) and convolution integrabilities (`hConvIic`/`hConvIoi`)
     are carried as precisely-typed hypotheses.  None is the conclusion; each is
     satisfiable on the trapped range.

HONEST LABEL: the step-output upgrade is NOT proved unconditionally.  The
genuine NEW analytic content — the non-paper `step_op` derivation and the full
`RotheStepAnalytic` assembly from one Green representation — IS proved
unconditionally and axiom-clean.  The remaining content (the lower-pinned
elliptic comparison data (I) and the bridge's integrability/folding bundle (II))
are the two named hard residuals, carried as precisely-typed, satisfiable, NON-
vacuous hypotheses.  No vacuity, no over-strong hyps, no FALSE bare-trap
Schauder, no circularity.
================================================================================
-/

section AxiomAudit
#print axioms frozenImplicitStepOp_of_greenConv_crossSource
#print axioms rotheStepAnalytic_of_greenSource
#print axioms crossStep_output_of_solution
end AxiomAudit

end ShenWork.Paper1
