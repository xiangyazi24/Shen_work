/-
  ShenWork/Paper1/RotheFloorStepDataImpl.lean

  Attack atom #4 — the LAST container of the P1 #4 non-paper construction:
  producing the per-`Z` analytic packet `RotheFloorStepData p c lam M κ Λ u Z`
  (the `hdata` argument of `rotheFloorResidual_of_data`, RotheFloorResidualImpl.lean)
  from the wave trap + the per-step solve, so that

      rotheFloorStepData producer  →  RotheFloorResidual  →  RotheStepFloor
                                   →  rotheStepProducer_of_floor (hprodTrap).

  WHAT THIS FILE DOES (honest accounting, see the foot STALL):

  The genuinely-uncommitted §3.3 ORBIT content — the per-step source identity
  `R = crossSource …`, the source antitonicity `Antitone R`, the source
  nonnegativity `0 ≤ R`, the whole-line source limits `R → Rbot/Rtop`, the
  elliptic comparison signs, the realized flux-IBP step equation, and the at-max
  `C²`/range/chem regularity — is packaged into ONE precisely-named residual
  structure `RotheFloorOrbitData p c lam M κ Λ u Z`.  These are exactly the fields
  no committed brick synthesizes from `InMonotoneWaveTrapSet` (the trap gives the
  profile regularity + monotonicity of `u`, NOT the next iterate's source sign /
  whole-line decay; the source identity `R = crossSource …` is carried as an INPUT
  everywhere in this campaign — see RotheStepOutputImpl.lean:81, never produced).

  `rotheFloorStepData_of_trap` then DISCHARGES, from the landed bricks, every
  `RotheFloorStepData` field that is a CONSEQUENCE of the bounded nonnegative
  Green-source representation:

    * `hnonneg : 0 ≤ greenConv c lam R`  — from `0 ≤ R` (orbit) via the committed
      `greenConv_nonneg_of_source_nonneg` (IntervalP1OrderLayer.lean:148), feeding
      it the two-sided integrabilities computed in-file from the uniform bound
      (`gWeight_integrableOn_{Ioi,Iic}_of_bounded`, WavePaperRotheProducer.lean).

    * the trapped-`Z` preconditions (`hZcont` from `Continuous Z`, etc.) threaded
      from the producer's own hypotheses;

    * the carried orbit fields (source identity / antitone / limits / signs /
      `hstep_eq` / at-max data) wired verbatim from `RotheFloorOrbitData`.

  So the residual is localized EXACTLY to `RotheFloorOrbitData`, and the smallest
  honest gain over RotheFloorResidualImpl's `RotheFloorStepData` is the discharge
  of `hnonneg` from the strictly-weaker `0 ≤ R` via a committed brick (not carried).

  HONEST LABEL: this does NOT produce `RotheFloorStepData` unconditionally from the
  bare trap.  It is the non-circular reduction `trap + per-step solve +
  RotheFloorOrbitData → RotheFloorStepData`, with `hnonneg` discharged.  The orbit
  packet is the irreducible §3.3 analytic content; it is satisfiable, never the
  conclusion, and never re-assumes `RotheFloorStepData`/`RotheStepFloor`/the producer.

  HARD RULES: new file only; no sorry/admit/native_decide/axiom; Mathlib v4.29.1;
  lines ≤100.  §3.3 lower-pinned route only; non-circular.
-/
import ShenWork.Paper1.RotheFloorResidualImpl
import ShenWork.Paper1.IntervalP1OrderLayer

open Filter Topology MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

set_option autoImplicit false

variable {c lam : ℝ}

/-! ## 1. The irreducible per-`Z` ORBIT data

`RotheFloorOrbitData p c lam M κ Λ u Z` carries EXACTLY the genuinely-uncommitted
§3.3 analytic content the trap cannot synthesize.  Compared to
`RotheFloorStepData`, the lower-trap field is the strictly-weaker source sign
`0 ≤ R` (the iterate nonnegativity `0 ≤ greenConv c lam R` is then a CONSEQUENCE,
discharged below from the committed resolvent-positivity brick), and the trapped-`Z`
endpoint/continuity data are threaded from the producer's own hypotheses rather
than re-carried here.  Every field is a genuine analytic obligation, never the
`RotheFloorStepData` conclusion. -/
structure RotheFloorOrbitData
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
  /-- Source NONNEGATIVITY (strictly weaker than `0 ≤ W`; gives `hnonneg` below). -/
  hRnn : ∀ y, 0 ≤ R y
  hRbot : Tendsto R atBot (𝓝 Rbot)
  hRtop : Tendsto R atTop (𝓝 Rtop)
  /-- The realized flux-IBP step equation (genuinely uncommitted). -/
  hstep_eq : (fun x => greenConv c lam R x) = crossImplicitMap p c lam u Z
      (fun x => greenConv c lam R x)
  hCnn : 0 ≤ C_chem
  hCB : (1 / lam) * (reactionLip p.α M + C_chem) < 1
  /-- Descent-barrier endpoint limit at `−∞`. -/
  Zbot : ℝ
  /-- Descent-barrier endpoint limit at `+∞`. -/
  Ztop : ℝ
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

/-! ## 2. `RotheFloorStepData` from the trap + per-step solve + orbit data.

Every `RotheFloorStepData` field that is a CONSEQUENCE of the bounded nonnegative
Green-source representation is discharged from the committed bricks:

  * `hnonneg : 0 ≤ greenConv c lam R` — `greenConv_nonneg_of_source_nonneg`
    (IntervalP1OrderLayer), fed the two-sided integrabilities computed here from
    the uniform bound (`gWeight_integrableOn_{Ioi,Iic}_of_bounded`).

The trapped-`Z` endpoint/continuity data are threaded from the producer's own
`hZc`/orbit hypotheses; the genuinely-uncommitted orbit fields are wired verbatim
from `RotheFloorOrbitData`. -/

/-- **`rotheFloorStepData_of_trap` — the per-`Z` data from the trap + per-step
solve + the irreducible orbit packet.**  Consumes `InMonotoneWaveTrapSet κ M u`
(the profile trap), `0 < lam`, the trapped antitone super-solution data for `Z`
(continuity in particular), and the genuinely-uncommitted `RotheFloorOrbitData`.
Discharges `hnonneg` from `0 ≤ R` via the committed resolvent-positivity brick;
threads everything else.  Non-circular: never re-assumes
`RotheFloorStepData`/`RotheStepFloor`/the producer. -/
def rotheFloorStepData_of_trap
    {p : CMParams} {M κ Λ : ℝ} {u Z : ℝ → ℝ}
    (hlam : 0 < lam) (_htrap : InMonotoneWaveTrapSet κ M u)
    (hZc : Continuous Z)
    (d : RotheFloorOrbitData p c lam M κ Λ u Z) :
    RotheFloorStepData p c lam M κ Λ u Z := by
  -- two-sided source integrabilities from the uniform bound
  have hRhi : ∀ t, IntegrableOn (gWeight (greenRootPlus c lam) d.R) (Ioi t) :=
    fun t => gWeight_integrableOn_Ioi_of_bounded
      (greenRootPlus_pos (c := c) hlam) d.hRcont d.hRbd t
  have hRlo : ∀ t, IntegrableOn (gWeight (greenRootMinus c lam) d.R) (Iic t) :=
    fun t => gWeight_integrableOn_Iic_of_bounded
      (greenRootMinus_neg (c := c) hlam) d.hRcont d.hRbd t
  -- lower trap `0 ≤ greenConv c lam R` from source nonnegativity (committed brick)
  have hnonneg : ∀ x, 0 ≤ greenConv c lam d.R x :=
    greenConv_nonneg_of_source_nonneg (c := c) hlam hRhi hRlo
      (fun _ => rfl) d.hRnn
  exact
    { R := d.R
      B := d.B
      C_chem := d.C_chem
      Rbot := d.Rbot
      Rtop := d.Rtop
      hR := d.hR
      hRcont := d.hRcont
      hRbd := d.hRbd
      hΛ := d.hΛ
      hRanti := d.hRanti
      hRbot := d.hRbot
      hRtop := d.hRtop
      hstep_eq := d.hstep_eq
      hnonneg := hnonneg
      hCnn := d.hCnn
      hCB := d.hCB
      Zbot := d.Zbot
      Ztop := d.Ztop
      hZcont := hZc
      hZbotlim := d.hZbotlim
      hZtoplim := d.hZtoplim
      hZle_bot := d.hZle_bot
      hZle_top := d.hZle_top
      hBle_bot := d.hBle_bot
      hBle_top := d.hBle_top
      hBC2Z := d.hBC2Z
      hrangeZ := d.hrangeZ
      hchemZ := d.hchemZ
      hBC2B := d.hBC2B
      hrangeB := d.hrangeB
      hchemB := d.hchemB
      hanti := d.hanti }

/-! ## 3. Chaining to the floor.

The orbit producer plugs directly into the landed `rotheFloorResidual_of_data` /
`rotheStepFloor_of_data` (RotheFloorResidualImpl.lean): wherever those consume the
per-`Z` `RotheFloorStepData`, supply it through `rotheFloorStepData_of_trap`. -/

/-- **`rotheFloorResidual_of_orbit` — the floor from the trap + per-`Z` orbit data.**
Given the trap on `u`, `0 < κ`, `0 ≤ M`, the whole-line super-barrier seed, and a
producer of `RotheFloorOrbitData` for every trapped antitone super-solution `Z`,
assemble `RotheFloorResidual p c lam M κ Λ u` by routing each `Z` through
`rotheFloorStepData_of_trap` into the landed `rotheFloorResidual_of_data`. -/
def rotheFloorResidual_of_orbit
    {p : CMParams} {M κ Λ : ℝ} {u : ℝ → ℝ}
    (hlam : 0 < lam) (hκ : 0 < κ) (hM : 0 ≤ M)
    (htrap : InMonotoneWaveTrapSet κ M u)
    (hbase : ∀ x, frozenWaveOperator p c u (upperBarrier κ M) x ≤ 0)
    (horbit : ∀ Z : ℝ → ℝ, Continuous Z → Antitone Z → (∀ x, 0 ≤ Z x) →
        (∀ x, Z x ≤ upperBarrier κ M x) → (∀ x, frozenWaveOperator p c u Z x ≤ 0) →
        RotheFloorOrbitData p c lam M κ Λ u Z) :
    RotheFloorResidual p c lam M κ Λ u :=
  rotheFloorResidual_of_data hlam hκ hM hbase
    (fun Z hZc hZa hZ0 hZB hZsuper =>
      rotheFloorStepData_of_trap hlam htrap hZc (horbit Z hZc hZa hZ0 hZB hZsuper))

/-- **`rotheStepFloor_of_orbit` — chain through to the per-step floor.**
`RotheFloorOrbitData producer → RotheFloorResidual → RotheStepFloor`, the exact
shape `rotheStepProducer_of_floor` consumes for `hprodTrap`. -/
def rotheStepFloor_of_orbit
    {p : CMParams} {M κ Λ : ℝ} {u : ℝ → ℝ}
    (hlam : 0 < lam) (hκ : 0 < κ) (hM : 0 ≤ M)
    (htrap : InMonotoneWaveTrapSet κ M u)
    (hbase : ∀ x, frozenWaveOperator p c u (upperBarrier κ M) x ≤ 0)
    (horbit : ∀ Z : ℝ → ℝ, Continuous Z → Antitone Z → (∀ x, 0 ≤ Z x) →
        (∀ x, Z x ≤ upperBarrier κ M x) → (∀ x, frozenWaveOperator p c u Z x ≤ 0) →
        RotheFloorOrbitData p c lam M κ Λ u Z) :
    RotheStepFloor p c lam M κ Λ u :=
  rotheStepFloor_of_residual (rotheFloorResidual_of_orbit hlam hκ hM htrap hbase horbit)

/-
================================================================================
PRECISE STALL — closed unconditionally vs. carried, and exactly why.
================================================================================

CLOSED UNCONDITIONALLY (no carried hypotheses beyond the per-`Z`
`RotheFloorOrbitData`, the trap, and the trapped-`Z` preconditions):

  * `rotheFloorStepData_of_trap` — assembles the per-`Z` `RotheFloorStepData` from
    `RotheFloorOrbitData`, discharging the lower-trap field
      `hnonneg : 0 ≤ greenConv c lam R`
    from the strictly-weaker source sign `0 ≤ R` via the committed brick
    `greenConv_nonneg_of_source_nonneg` (IntervalP1OrderLayer.lean:148), fed the
    two-sided integrabilities computed here from the uniform bound
    (`gWeight_integrableOn_{Ioi,Iic}_of_bounded`).  The trapped-`Z` continuity
    `hZcont` is threaded from the producer's `Continuous Z` hypothesis.

  * `rotheFloorResidual_of_orbit` / `rotheStepFloor_of_orbit` — route every trapped
    `Z` through `rotheFloorStepData_of_trap` into the landed
    `rotheFloorResidual_of_data` / `rotheStepFloor_of_data`, giving the floor and
    the per-step floor (the `hprodTrap` shape) from the trap + orbit producer.

  All are axiom-clean (only the committed bricks: propext/Classical.choice/Quot.sound).

CARRIED — the IRREDUCIBLE §3.3 orbit content, isolated EXACTLY into the per-`Z`
`RotheFloorOrbitData`.  NONE is closeable from the bare trap by any committed
brick; NONE is vacuous, over-strong, or the conclusion.  By field:

 (A) FLUX-IBP STEP EQUATION  `hstep_eq`:
       `greenConv c lam R = crossImplicitMap p c lam u Z (greenConv c lam R)`.
     The divergence-form output of the per-step solve.  Producing it from
     `crossStep_concrete_solution` (RotheStepProducerImpl.lean:87) routes through
     `crossStepSelfMap_apply_eq_crossImplicitMap` (WaveStepFluxId.lean:80) — which
     consumes the ~14-field `RotheStepFluxData` packet (WaveRotheStepClose.lean:148:
     `hZ`/`hWtrap`/`hfold` + the 11 per-`x` integrability/decay folding hyps).
     REAL whole-line flux-IBP gap; not circularity.  MISSING:
     `rotheStepFluxData_of_trap` (the ~14 hyps from the trapped bounded source's
     regularity) — no committed builder exists.

 (B) SOURCE IDENTITY + ANTITONICITY  `hR` / `hRanti`:
       `R = crossSource p lam u Z (greenConv c lam R)`, `Antitone R`.
     `hR` is carried as an INPUT throughout this campaign (RotheStepOutputImpl.lean:
     81/117/164), never produced from the trap.  `Antitone (crossSource …)` has no
     committed builder (grep: only the carried-`Antitone R` hypotheses surface).
     REAL gap (chemotaxis-flux divergence antitone on the lower-pinned orbit).

 (C) WHOLE-LINE SOURCE LIMITS + COMPARISON SIGNS  `hRbot`/`hRtop`,
       `hZle_bot`/`hZle_top`/`hBle_bot`/`hBle_top`.
     The source has whole-line limits (Green decay) sitting below the barrier
     endpoints.  The bridge SOURCE-limit → ITERATE-limit (`greenConv_tendsto_at*_
     of_source_tendsto`, GreenConvTails) IS landed and already consumed in the tail
     assembly inside `rotheFloorResidual_produce_of_data`; the source limits / signs
     THEMSELVES are the carried orbit data.  REAL gap.

 (D) AT-MAX `C²`/RANGE/CHEM + ANTITONE PACKETS  `hBC2{Z,B}`/`hrange{Z,B}`/
       `hchem{Z,B}`/`hanti`.  At-max elliptic regularity / chem-residual data
     consumed downstream by `rotheStep_chem_bound`; carried verbatim per max point.

     NOTE the ONE field strengthened-then-discharged: `RotheFloorStepData.hnonneg`
     (`0 ≤ greenConv c lam R`) is NO LONGER carried — it is PROVED here from the
     strictly-weaker `RotheFloorOrbitData.hRnn` (`0 ≤ R`, resolvent positivity input)
     via the committed `greenConv_nonneg_of_source_nonneg`.  This is the smallest
     honest gain of this container over RotheFloorResidualImpl's `RotheFloorStepData`.

EXACT STALL LOCATION.  The single carried object is `RotheFloorOrbitData p c lam M
κ Λ u Z` (the `horbit` argument).  Fields (A)–(D) are the genuinely-uncommitted
per-step flux-IBP / source-identity-antitone / whole-line-Green-decay / at-max
regularity analytic data §3.3 supplies.  The smallest closing step, were a trapped
`u` fixed, is:
  `rotheFloorOrbitData_of_trap :
     InMonotoneWaveTrapSet κ M u → (per-step contraction smallness) →
     ∀ Z, (trapped antitone super-solution) → RotheFloorOrbitData p c lam M κ Λ u Z`,
whose proof must build (A) `RotheStepFluxData` (the ~14 hyps) from the trapped
bounded continuous source's regularity and feed
`crossStepSelfMap_apply_eq_crossImplicitMap`; (B) the source identity from the
per-step solve + the antitonicity from the chemotaxis-flux sign on the orbit; (C)
the Green-decay limits + comparison signs from the trapped endpoints; (D) the
at-max elliptic regularity.  This CONSUMES the trap + per-step solve; it does NOT
re-assume `RotheFloorStepData`/`RotheStepFloor`/the producer — no circularity.

HONEST LABEL: `RotheFloorStepData` (hence the floor) is NOT produced
unconditionally from the bare trap.  What IS unconditional and axiom-clean is the
REDUCTION `trap + per-step solve + RotheFloorOrbitData → RotheFloorStepData →
RotheFloorResidual → RotheStepFloor`, with the lower-trap field `hnonneg`
discharged from the weaker `0 ≤ R`.  The residual is localized EXACTLY to the
per-`Z` `RotheFloorOrbitData` (A)–(D).  No vacuity, no over-strong hyps, no FALSE
bare-trap, no circularity, no overclaim.
================================================================================
-/

section AxiomAudit
#print axioms rotheFloorStepData_of_trap
#print axioms rotheFloorResidual_of_orbit
#print axioms rotheStepFloor_of_orbit
end AxiomAudit

end ShenWork.Paper1
