/-
  ShenWork/Paper1/RotheFloorOrbitDataImpl.lean

  Attack atom #4 — the LAST open object of the P1 #4 non-paper construction: the
  per-`Z` ORBIT packet `RotheFloorOrbitData p c lam M κ Λ u Z` (the `horbit`
  argument of `rotheFloorResidual_of_orbit`, RotheFloorStepDataImpl.lean), whose
  fields (A)–(D) are the genuinely-uncommitted §3.3 analysis:

    (A) flux-IBP step equation  `hstep_eq : greenConv c lam R = crossImplicitMap …`;
    (B) source identity + antitonicity  `hR : R = crossSource …` / `Antitone R`;
    (C) whole-line Green-decay source limits `Rbot/Rtop` + comparison signs;
    (D) at-max `C²`/range/chem regularity for `Z` and `Ū`, and the `hanti` packet.

  ──────────────────────────────────────────────────────────────────────────────
  HONEST ACCOUNTING — what this file discharges from LANDED machinery vs. carries.
  ──────────────────────────────────────────────────────────────────────────────

  GREP-GENERAL-BEFORE-SPECIAL findings (the campaign's prior "gaps" that were/were
  NOT stale), each verified against the actual repo:

  • (A)/(B)`hR`/(C)limits/(D)`hBC2Z`/`hrangeZ`/`hchem*`/`hanti`: NO landed builder
    for the PER-STEP (non-diagonal) profile triple `u, Z, W` distinct.  The landed
    source machinery in `WavePaperStationaryFloor`
    (`crossSource_tendsto_atBot_of_profile_tail_and_deriv_tail`:1118,
     `lowerPinned_crossSource_*`:1168) is the DIAGONAL stationary case
    `crossSource p lam U U U` (the fixed-point limit, single profile in all three
    slots).  It does NOT instantiate to `crossSource p lam u Z (greenConv …)`.
    `WaveRotheOrder.crossSource_le_barrierSource_pointwise`:166 gives a pointwise
    COMPARISON but only from a carried `RotheChemoMonotoneResidual` (itself the
    honest gap, WaveRotheOrder STALL NOTE).  `WaveStepFluxId`'s
    `crossStepSelfMap_apply_eq_crossImplicitMap`:80 yields (A) but only from the
    ~14-field `RotheStepFluxData` (`deriv (stepFlux p u W)` whole-line
    integrability/decay of the PRODUCED iterate) — NO landed
    `rotheStepFluxData_of_trap`.  These are genuinely irreducible: CARRIED.

  • (D) `hBC2B` (super-barrier at-max `C²`):  DISCHARGED, not carried.  The landed
    `upperBarrier_BC2_atMax_dischargeable` (WaveRotheResidualClose.lean:250)
    closes it from `0<κ`, `0<M`, and `Differentiable ℝ W`; `W = greenConv c lam R`
    is differentiable via the landed `greenConv_hasDerivAt` (WaveGreenIdentity.lean:
    139), fed the two-sided integrabilities computed here from the uniform source
    bound (`gWeight_integrableOn_{Ioi,Iic}_of_bounded`,
    WavePaperRotheProducer.lean:4303/4318).  This is a GENUINE analytic discharge:
    the max of `W − Ū` is never the kink (`maxSub_upperBarrier_ne_interface`), so
    `Ū` is `C²` there (`upperBarrier_contDiffAt_two_of_ne_interface`).  It is the
    SAME kind of single-field honest gain as `hnonneg` in RotheFloorStepDataImpl
    (where `0 ≤ W` was discharged from the weaker `0 ≤ R`): here `hBC2B` moves from
    carried INPUT (it is carried in RotheMaxDataImpl.lean:128 / the floor) to a
    DISCHARGED output.  NOT a rename — the orbit packet below has NO `hBC2B` field.

  • `hΛ`:  definitional binding `Λ = 2·(greenDelta c lam)⁻¹·B`, threaded.

  So this file is the NON-CIRCULAR reduction

      trap + per-step solve + `RotheFloorOrbitDataResidual`  →  `RotheFloorOrbitData`,

  with `hBC2B` discharged.  `RotheFloorOrbitDataResidual` is `RotheFloorOrbitData`
  MINUS the discharged `hBC2B`, i.e. it carries EXACTLY (A)+(B)+(C)+(D-minus-`hBC2B`):
  the per-step flux-IBP step eq, the source identity+antitone, the whole-line
  source limits+signs, and the at-max `Z`-side + chem + `hanti` data.  NONE is the
  conclusion; NONE is vacuous/over-strong; NONE is closeable from the bare trap.

  PRECISE CARRIED ANALYTIC LEMMAS still missing (file:line + verdict) at the foot.

  HARD RULES: new file only; no sorry/admit/native_decide/axiom; Mathlib v4.29.1;
  lines ≤100.  §3.3 lower-pinned; non-circular.
-/
import ShenWork.Paper1.RotheFloorResidualImpl
import ShenWork.Paper1.RotheFloorStepDataImpl
import ShenWork.Paper1.WaveRotheResidualClose

open Filter Topology MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

set_option autoImplicit false

variable {c lam : ℝ}

/-! ## 1. The reduced orbit residual — `RotheFloorOrbitData` minus the discharged
`hBC2B`.

Every field is a genuinely-uncommitted §3.3 obligation: the per-step flux-IBP step
equation (A), the source identity + antitonicity (B), the whole-line source limits
and comparison signs (C), and the at-max `C²`/range/chem data for `Z` plus the
`hanti` packet (D).  The ONE (D)-field NOT carried here is the super-barrier at-max
`C²` `hBC2B`, which is discharged below from the landed
`upperBarrier_BC2_atMax_dischargeable`. -/
structure RotheFloorOrbitDataResidual
    (p : CMParams) (c lam M κ Λ : ℝ) (u Z : ℝ → ℝ) where
  R : ℝ → ℝ
  B : ℝ
  C_chem : ℝ
  Rbot : ℝ
  Rtop : ℝ
  hR : R = crossSource p lam u Z (fun x => greenConv c lam R x)
  hRcont : Continuous R
  hRbd : ∀ y, |R y| ≤ B
  hΛ : Λ = 2 * (greenDelta c lam)⁻¹ * B
  hRanti : Antitone R
  hRnn : ∀ y, 0 ≤ R y
  hRbot : Tendsto R atBot (𝓝 Rbot)
  hRtop : Tendsto R atTop (𝓝 Rtop)
  hstep_eq : (fun x => greenConv c lam R x) = crossImplicitMap p c lam u Z
      (fun x => greenConv c lam R x)
  hCnn : 0 ≤ C_chem
  hCB : (1 / lam) * (reactionLip p.α M + C_chem) < 1
  Zbot : ℝ
  Ztop : ℝ
  hZbotlim : Tendsto Z atBot (𝓝 Zbot)
  hZtoplim : Tendsto Z atTop (𝓝 Ztop)
  hZle_bot : Rbot * lam⁻¹ ≤ Zbot
  hZle_top : Rtop * lam⁻¹ ≤ Ztop
  hBle_bot : Rbot * lam⁻¹ ≤ M
  hBle_top : Rtop * lam⁻¹ ≤ 0
  hBC2Z : ∀ x₀, IsMaxOn (fun x => greenConv c lam R x - Z x) Set.univ x₀ →
    ContDiffAt ℝ 2 Z x₀
  hrangeZ : ∀ x₀, IsMaxOn (fun x => greenConv c lam R x - Z x) Set.univ x₀ →
    greenConv c lam R x₀ ∈ Set.Icc (0 : ℝ) M ∧ Z x₀ ∈ Set.Icc (0 : ℝ) M
  hchemZ : ∀ x₀, IsMaxOn (fun x => greenConv c lam R x - Z x) Set.univ x₀ →
    RotheStepChemData p u (fun x => greenConv c lam R x) Z C_chem x₀
  hrangeB : ∀ x₀, IsMaxOn (fun x => greenConv c lam R x - upperBarrier κ M x)
      Set.univ x₀ → greenConv c lam R x₀ ∈ Set.Icc (0 : ℝ) M ∧
      upperBarrier κ M x₀ ∈ Set.Icc (0 : ℝ) M
  hchemB : ∀ x₀, IsMaxOn (fun x => greenConv c lam R x - upperBarrier κ M x)
      Set.univ x₀ → RotheStepChemData p u (fun x => greenConv c lam R x)
      (upperBarrier κ M) C_chem x₀
  hanti : RotheStepAntitoneData p c lam M C_chem u Z (fun x => greenConv c lam R x)

/-! ## 2. `RotheFloorOrbitData` from the trap + reduced residual, discharging `hBC2B`.

`hBC2B` is the super-barrier at-max `C²` field.  It is PROVED here from the landed
`upperBarrier_BC2_atMax_dischargeable`, which needs `0<κ`, `0<M`, and
`Differentiable ℝ (greenConv c lam R)`.  The differentiability is the landed
`greenConv_hasDerivAt`, fed the two-sided integrabilities computed in-file from the
uniform source bound `hRbd` (`gWeight_integrableOn_{Ioi,Iic}_of_bounded`). -/

/-- **`rotheFloorOrbitData_of_trap` — the per-`Z` orbit packet from the trap +
per-step solve + the reduced residual.**  Consumes `InMonotoneWaveTrapSet κ M u`
(the profile trap), `0 < lam`, `0 < κ`, `0 < M`, and the genuinely-uncommitted
`RotheFloorOrbitDataResidual` (carrying (A)+(B)+(C)+(D-minus-`hBC2B`)).  Discharges
`hBC2B` from the landed `upperBarrier_BC2_atMax_dischargeable` via the
differentiability of `W = greenConv c lam R`; threads the rest.  Non-circular:
never re-assumes `RotheFloorOrbitData`/`RotheFloorStepData`/`RotheStepFloor`/the
producer. -/
def rotheFloorOrbitData_of_trap
    {p : CMParams} {M κ Λ : ℝ} {u Z : ℝ → ℝ}
    (hlam : 0 < lam) (hκ : 0 < κ) (hMpos : 0 < M)
    (_htrap : InMonotoneWaveTrapSet κ M u)
    (d : RotheFloorOrbitDataResidual p c lam M κ Λ u Z) :
    RotheFloorOrbitData p c lam M κ Λ u Z := by
  -- two-sided source integrabilities from the uniform bound
  have hRhi : ∀ t, IntegrableOn (gWeight (greenRootPlus c lam) d.R) (Ioi t) :=
    fun t => gWeight_integrableOn_Ioi_of_bounded
      (greenRootPlus_pos (c := c) hlam) d.hRcont d.hRbd t
  have hRlo : ∀ t, IntegrableOn (gWeight (greenRootMinus c lam) d.R) (Iic t) :=
    fun t => gWeight_integrableOn_Iic_of_bounded
      (greenRootMinus_neg (c := c) hlam) d.hRcont d.hRbd t
  -- the produced iterate `W = greenConv c lam R` is differentiable (landed C¹)
  have hWdiff : Differentiable ℝ (fun x => greenConv c lam d.R x) := by
    intro x
    exact (greenConv_hasDerivAt (c := c) (lam := lam) d.hRcont hRhi hRlo x).differentiableAt
  -- DISCHARGE `hBC2B` from the landed at-max-`C²`-of-`Ū` brick (max never the kink)
  have hBC2B : ∀ x₀, IsMaxOn (fun x => greenConv c lam d.R x - upperBarrier κ M x)
      Set.univ x₀ → ContDiffAt ℝ 2 (upperBarrier κ M) x₀ :=
    upperBarrier_BC2_atMax_dischargeable (W := fun x => greenConv c lam d.R x)
      hκ hMpos hWdiff
  exact
    { R := d.R, B := d.B, C_chem := d.C_chem, Rbot := d.Rbot, Rtop := d.Rtop
      hR := d.hR, hRcont := d.hRcont, hRbd := d.hRbd, hΛ := d.hΛ
      hRanti := d.hRanti, hRnn := d.hRnn, hRbot := d.hRbot, hRtop := d.hRtop
      hstep_eq := d.hstep_eq, hCnn := d.hCnn, hCB := d.hCB
      Zbot := d.Zbot, Ztop := d.Ztop, hZbotlim := d.hZbotlim, hZtoplim := d.hZtoplim
      hZle_bot := d.hZle_bot, hZle_top := d.hZle_top
      hBle_bot := d.hBle_bot, hBle_top := d.hBle_top
      hBC2Z := d.hBC2Z, hrangeZ := d.hrangeZ, hchemZ := d.hchemZ
      hBC2B := hBC2B, hrangeB := d.hrangeB, hchemB := d.hchemB, hanti := d.hanti }

/-! ## 3. Chaining to the per-step floor and the producer.

Routing the reduced-residual producer through `rotheFloorOrbitData_of_trap` into
the landed `rotheStepFloor_of_orbit` (RotheFloorStepDataImpl.lean) gives the
`RotheStepFloor`, the exact shape `rotheStepProducer_of_floor` consumes for the
trapped producer `hprodTrap`. -/

/-- **`rotheStepFloor_of_orbitResidual` — the per-step floor from the trap + the
reduced orbit-residual producer.**  Each trapped antitone super-solution `Z` is
routed through `rotheFloorOrbitData_of_trap` (discharging `hBC2B`) into the landed
`rotheStepFloor_of_orbit`. -/
def rotheStepFloor_of_orbitResidual
    {p : CMParams} {M κ Λ : ℝ} {u : ℝ → ℝ}
    (hlam : 0 < lam) (hκ : 0 < κ) (hMpos : 0 < M)
    (htrap : InMonotoneWaveTrapSet κ M u)
    (hbase : ∀ x, frozenWaveOperator p c u (upperBarrier κ M) x ≤ 0)
    (hres : ∀ Z : ℝ → ℝ, Continuous Z → Antitone Z → (∀ x, 0 ≤ Z x) →
        (∀ x, Z x ≤ upperBarrier κ M x) → (∀ x, frozenWaveOperator p c u Z x ≤ 0) →
        RotheFloorOrbitDataResidual p c lam M κ Λ u Z) :
    RotheStepFloor p c lam M κ Λ u :=
  rotheStepFloor_of_orbit hlam hκ (le_of_lt hMpos) htrap hbase
    (fun Z hZc hZa hZ0 hZB hZsuper =>
      rotheFloorOrbitData_of_trap hlam hκ hMpos htrap (hres Z hZc hZa hZ0 hZB hZsuper))

/-- **`hprodTrap` — the trapped per-step producer from the reduced orbit residual.**
For every trapped profile `v`, supply the seed + reduced-residual producer to
`rotheStepFloor_of_orbitResidual` and feed the result to the landed
`rotheStepProducer_of_floor`.  This closes the producer obligation `hprodTrap`
(`RotheStepProducer` on the wave trap) modulo EXACTLY the reduced orbit residual. -/
theorem hprodTrap_of_orbitResidual
    {p : CMParams} {M κ Λ : ℝ}
    (hlam : 0 < lam) (hκ : 0 < κ) (hMpos : 0 < M)
    (hbase : ∀ v : ℝ → ℝ, InMonotoneWaveTrapSet κ M v →
      ∀ x, frozenWaveOperator p c v (upperBarrier κ M) x ≤ 0)
    (hres : ∀ v : ℝ → ℝ, InMonotoneWaveTrapSet κ M v →
      ∀ Z : ℝ → ℝ, Continuous Z → Antitone Z → (∀ x, 0 ≤ Z x) →
        (∀ x, Z x ≤ upperBarrier κ M x) → (∀ x, frozenWaveOperator p c v Z x ≤ 0) →
        RotheFloorOrbitDataResidual p c lam M κ Λ v Z) :
    ∀ u, InMonotoneWaveTrapSet κ M u → RotheStepProducer p c lam M κ Λ u :=
  rotheStepProducer_of_floor
    (fun v hv => rotheStepFloor_of_orbitResidual hlam hκ hMpos hv (hbase v hv) (hres v hv))

/-
================================================================================
PRECISE STALL — closed vs. carried, file:line + missing analytic lemma + verdict.
================================================================================

CLOSED UNCONDITIONALLY (axiom-clean, from LANDED bricks; not the conclusion):

  • `rotheFloorOrbitData_of_trap` — assembles `RotheFloorOrbitData` from the
    reduced residual, DISCHARGING the super-barrier at-max `C²` field
      `hBC2B : ∀ x₀, IsMaxOn (W − Ū) univ x₀ → ContDiffAt ℝ 2 Ū x₀`,  `W = greenConv c lam R`,
    from the landed `upperBarrier_BC2_atMax_dischargeable`
    (WaveRotheResidualClose.lean:250) — which feeds
    `maxSub_upperBarrier_ne_interface` (the max is never the kink `exp(−κx)=M`)
    into `upperBarrier_contDiffAt_two_of_ne_interface` (`Ū` is `C²` off the kink) —
    via the differentiability of `W` from the landed `greenConv_hasDerivAt`
    (WaveGreenIdentity.lean:139), fed the two-sided integrabilities computed here
    from `hRbd` (`gWeight_integrableOn_{Ioi,Iic}_of_bounded`,
    WavePaperRotheProducer.lean:4303/4318).  This is a GENUINE analytic gain: in
    the landed chain `hBC2B` is carried as an INPUT (RotheMaxDataImpl.lean:128;
    RotheFloorResidualImpl `RotheFloorStepData.hBC2B`); here it is an OUTPUT.  The
    reduced residual structure has NO `hBC2B` field — not a rename.

  • `rotheStepFloor_of_orbitResidual` / `hprodTrap_of_orbitResidual` — route every
    trapped `Z` through `rotheFloorOrbitData_of_trap` into the landed
    `rotheStepFloor_of_orbit` → `rotheStepProducer_of_floor`, giving the per-step
    floor and the trapped producer (`hprodTrap`) modulo EXACTLY the reduced
    residual.  hprodTrap CLOSES relative to `RotheFloorOrbitDataResidual`.

CARRIED — the genuinely irreducible §3.3 per-step analysis (NON-diagonal profile
triple `u, Z, W = greenConv c lam R` distinct).  Each names the SPECIFIC missing
analytic lemma, with the verdict that NO landed builder produces it for the
per-step case (only the DIAGONAL stationary `crossSource p lam U U U` is landed):

 (A) FLUX-IBP STEP EQUATION  `hstep_eq : greenConv c lam R = crossImplicitMap … `.
     MISSING: `rotheStepFluxData_of_trap` producing the ~14-field
     `RotheStepFluxData` (WaveRotheStepClose.lean:151) — the whole-line
     integrability/decay of `deriv (stepFlux p u W)` for the PRODUCED iterate
     `W` — to feed `crossStepSelfMap_apply_eq_crossImplicitMap`
     (WaveStepFluxId.lean:80).  VERDICT: real whole-line flux-IBP gap; `W'` enters
     via `(W^m·V')'`; no committed builder.  (`greenConvDeriv2` gives `W''`, but
     the per-tail `K'·stepFlux` integrability + `atBot/atTop` decay of the
     cross-frozen flux are uncommitted.)

 (B) SOURCE IDENTITY + ANTITONICITY  `hR` / `hRanti`.
     `hR : R = crossSource p lam u Z (greenConv c lam R)` is carried as an INPUT
     throughout (RotheStepOutputImpl.lean:81); if the producer DEFINES `R` as
     `crossSource …`, `hR` is `rfl`, but the producer here only yields the
     truncated bcf fixed point, not the crossSource form — carried.  MISSING:
     `crossSource_antitone_of_lowerPinned_orbit` (chemotaxis-flux divergence
     antitone on the lower-pinned orbit).  VERDICT: no committed builder; the
     landed `crossSource` tendsto/continuity is DIAGONAL-only
     (WavePaperStationaryFloor.lean:1118/1168, `crossSource p lam U U U`).

 (C) WHOLE-LINE SOURCE LIMITS + COMPARISON SIGNS  `hRbot`/`hRtop`,
     `hZle_*`/`hBle_*`.  MISSING: the PER-STEP
     `crossSource_tendsto_at{Bot,Top}` for `crossSource p lam u Z (greenConv …)`.
     VERDICT: only the DIAGONAL `crossSource p lam U U U` tendsto is landed
     (WavePaperStationaryFloor.lean:1118); it does NOT instantiate to distinct
     `u, Z, W`.  The SOURCE→ITERATE bridge (`greenConv_tendsto_at*_of_source_*`,
     GreenConvTails) IS landed and consumed in the floor tail assembly, but the
     SOURCE limits themselves are carried.

 (D) AT-MAX `Z`-SIDE `C²`/RANGE/CHEM + `hanti`  `hBC2Z`/`hrange{Z,B}`/`hchem{Z,B}`/
     `hanti`.  `hBC2Z` (descent-barrier at-max `C²`) is NOT dischargeable like
     `hBC2B`: `Z` is an arbitrary trapped antitone super-solution, not the explicit
     `Ū`, so no kink-avoidance brick applies — carried.  `hrange*`/`hchem*` are the
     at-max elliptic regularity / `chemFlux_increment_bound` inputs (consumed
     downstream by `rotheStep_chem_bound`); `hanti` is the shifted-step antitone
     packet (`RotheStepAntitoneData`, WaveRotheProducer.lean:142) — shifted step
     equations + whole-line shifted limits + one-sided shifted-max estimates of the
     PRODUCED iterate.  VERDICT: no committed builder; carried verbatim.

EXACT STALL LOCATION.  The single carried object is now
`RotheFloorOrbitDataResidual p c lam M κ Λ u Z` (= `RotheFloorOrbitData` minus the
discharged `hBC2B`).  The smallest remaining closing step is
  `rotheFloorOrbitDataResidual_of_trap :
     InMonotoneWaveTrapSet κ M u → (per-step contraction smallness) →
     ∀ Z, (trapped antitone super-solution) → RotheFloorOrbitDataResidual …`,
whose proof must build (A) `RotheStepFluxData` from the produced iterate's
cross-frozen-flux regularity, (B) the source identity from the per-step solve + the
chemotaxis-flux antitonicity on the orbit, (C) the per-step `crossSource` Green-
decay limits + endpoint signs, and (D) the `Z`-side at-max regularity + the shifted
antitone packet.  It CONSUMES the trap + per-step solve; it does NOT re-assume
`RotheFloorOrbitData`/`RotheFloorStepData`/`RotheStepFloor`/the producer — no
circularity.

HONEST LABEL.  This file does NOT produce `RotheFloorOrbitData` (hence the floor /
`hprodTrap`) unconditionally from the bare trap.  What IS unconditional and
axiom-clean is the REDUCTION
  `trap + per-step solve + RotheFloorOrbitDataResidual → RotheFloorOrbitData →
   RotheStepFloor → RotheStepProducer (hprodTrap)`,
with the super-barrier at-max `C²` field `hBC2B` DISCHARGED from the landed
`upperBarrier_BC2_atMax_dischargeable`.  The residual is localized EXACTLY to the
per-`Z` `RotheFloorOrbitDataResidual` (A)+(B)+(C)+(D-minus-`hBC2B`).  No vacuity, no
over-strong hyps, no FALSE bare-trap, no circularity, no overclaim, no repackaging
(the discharged `hBC2B` field is GONE from the carried structure, not renamed).
================================================================================
-/

section AxiomAudit
#print axioms rotheFloorOrbitData_of_trap
#print axioms rotheStepFloor_of_orbitResidual
#print axioms hprodTrap_of_orbitResidual
end AxiomAudit

end ShenWork.Paper1
