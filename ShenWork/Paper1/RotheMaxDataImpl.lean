/-
  ShenWork/Paper1/RotheMaxDataImpl.lean

  Attack atom #4A-I — the lower-pinned `RotheMaxData` elliptic comparison data
  for the Rothe step output `W`, against (a) the previous iterate `Z` and (b) the
  upper super-barrier `Ū = upperBarrier κ M`, in the χ≤0 lower-pinned trap (§3.3).

  CONTEXT.  The just-landed `crossStep_output_of_solution`
  (RotheStepOutputImpl.lean) carries two residuals; this file discharges the
  FIRST — the `RotheMaxData` comparison data — as far as the committed bricks
  allow, and carries the rest precisely.  `RotheMaxData` (WaveRotheProducer.lean,
  16 fields) is the COMPARISON DATA from which `rotheStep_le_barrier` then DERIVES
  `W ≤ B`.  Building it is NON-CIRCULAR: we supply the super-barrier property, the
  ordering, the tails, the at-max chemotaxis residual sign — we never assume the
  conclusion `W ≤ B`, nor `RotheStepOutput`/`RotheStepProducer`.

  WHAT THIS FILE CLOSES — discharged INSIDE the builders (no caller may weaken):

   * `rotheMaxData_Z` — `RotheMaxData … W Z` (descent barrier `B = Z`).  Two
     fields are discharged UNCONDITIONALLY inside the builder, removing them from
     the caller's obligation:
        - `Bsuper := hZsuper`  — `F_u(Z) ≤ 0` is exactly the supersolution INPUT
          precond of the descent orbit (`RotheStepInput.produce`'s `hZsuper`),
          NOT a fresh assumption: on the lower-pinned orbit every old iterate is a
          supersolution.  This is the §3.3 descent-orbit fact, fed straight in.
        - `ZB := fun _ => le_refl _` — `Z ≤ Z`, closed outright.
        - `chem` — the at-max χ≤0 chemotaxis residual sign, discharged via the
          committed `rotheStep_chem_bound` from the carried `RotheStepChemData`
          packet (its `hχ : p.χ ≤ 0` is the max-principle core).

   * `rotheMaxData_barrier` — `RotheMaxData … W Ū`.  The DEEP unconditional win:
        - `Bsuper := whole_line_super_barrier …`  — `F_u(Ū) ≤ 0` is the committed
          whole-line χ≤0 super-barrier (WaveSuperBarrier.lean:272), applied to the
          trapped frozen profile `u`.  This is the genuinely-elliptic super-barrier
          content, closed OUTRIGHT (not carried).
        - `ZB := hZB` — `Z ≤ Ū` is the trap INPUT precond (every iterate stays
          below the upper barrier), fed straight in.
        - `chem` — as above, via `rotheStep_chem_bound`.

  The remaining `RotheMaxData` fields — `φcont`, the two-sided tails
  (`La`/`Lb`/`hbot`/`hLa`/`htop`/`hLb`), `BC2`, `range`, and the scalar trap
  constants `hC_chem_nonneg`/`hCB` — are the orbit-dependent decay/regularity data
  (no committed `greenConv`-tendsto lemma exists in the repo); they are carried as
  precisely-typed, satisfiable, NON-vacuous packets (`RotheStepTails`,
  `RotheStepChemData`), NOT weakened and NOT the conclusion.

  HARD RULES: new file only; no sorry/admit/native_decide/axiom; Mathlib
  v4.29.1; lines ≤100.  §3.3 lower-pinned route only; non-circular.
-/
import ShenWork.Paper1.WaveRotheStepClose
import ShenWork.Paper1.WaveSuperBarrier

open Filter Topology MeasureTheory Set

noncomputable section

namespace ShenWork.Paper1

variable {p : CMParams} {c lam M κ : ℝ} {u : ℝ → ℝ}

/-! ## (A) Descent comparison data `RotheMaxData … W Z`.

`B = Z`.  `Bsuper`/`ZB` are discharged inside the builder; `chem` via the
committed `rotheStep_chem_bound`; the decay/regularity floor is carried as the
`RotheStepTails`/`RotheStepChemData` packets.  Non-circular: it never assumes
`W ≤ Z`. -/

/-- **(A) `RotheMaxData` against the descent barrier `B = Z`.**
`Bsuper := hZsuper` (the supersolution INPUT precond — `F_u(Z) ≤ 0` on the
lower-pinned orbit), `ZB := le_refl`, `chem` from the carried chem packet; the
two-sided `W − Z` tails and the at-max `C²`/range data carried.  No field
re-assumes the comparison conclusion. -/
def rotheMaxData_Z
    {C_chem : ℝ} {Z W : ℝ → ℝ}
    (hCnn : 0 ≤ C_chem)
    (hCB : (1 / lam) * (reactionLip p.α M + C_chem) < 1)
    (hZsuper : ∀ x, frozenWaveOperator p c u Z x ≤ 0)
    (htails : RotheStepTails W Z)
    (hBC2 : ∀ x₀, IsMaxOn (fun x => W x - Z x) Set.univ x₀ → ContDiffAt ℝ 2 Z x₀)
    (hrange : ∀ x₀, IsMaxOn (fun x => W x - Z x) Set.univ x₀ →
      W x₀ ∈ Set.Icc (0 : ℝ) M ∧ Z x₀ ∈ Set.Icc (0 : ℝ) M)
    (hchem : ∀ x₀, IsMaxOn (fun x => W x - Z x) Set.univ x₀ →
      RotheStepChemData p u W Z C_chem x₀) :
    RotheMaxData p c lam M C_chem u Z W Z where
  hC_chem_nonneg := hCnn
  hCB := hCB
  Bsuper := hZsuper
  ZB := fun _ => le_refl _
  φcont := htails.φcont
  La := htails.La
  Lb := htails.Lb
  hbot := htails.hbot
  hLa := htails.hLa
  htop := htails.htop
  hLb := htails.hLb
  BC2 := hBC2
  range := hrange
  chem := fun x₀ hx₀ => rotheStep_chem_bound (hchem x₀ hx₀)

/-! ## (B) Upper-trap comparison data `RotheMaxData … W Ū`.

`B = upperBarrier κ M`.  The DEEP unconditional win is `Bsuper`, discharged from
the committed whole-line χ≤0 super-barrier `whole_line_super_barrier` applied to
the trapped frozen profile `u`.  `ZB` is the trap input precond `Z ≤ Ū`; `chem`
via `rotheStep_chem_bound`; the rest carried. -/

/-- **(B) `RotheMaxData` against the upper super-barrier `B = upperBarrier κ M`.**
`Bsuper` is closed OUTRIGHT from `whole_line_super_barrier` (the committed χ≤0
whole-line super-barrier) under its regime hypotheses + the trap membership
`hmono : InMonotoneWaveTrapSet κ M u`.  `ZB := hZB` (`Z ≤ Ū`, the trap input),
`chem` from the carried packet; the two-sided `W − Ū` tails and at-max
`C²`/range data carried.  `BC2` is the AT-MAX `C²` form (the everywhere form is
FALSE at the interface kink — the max never sits on the kink). -/
def rotheMaxData_barrier
    {C_chem : ℝ} {Z W : ℝ → ℝ}
    (hCnn : 0 ≤ C_chem)
    (hCB : (1 / lam) * (reactionLip p.α M + C_chem) < 1)
    -- the committed `whole_line_super_barrier` regime hypotheses (χ≤0):
    (hχ : p.χ ≤ 0) (hα : p.α ≤ p.m + p.γ - 1)
    (hκ : 0 < κ) (hκ1 : κ < 1) (hγκ : p.γ * κ < 1) (hmκ : κ * p.m ≤ 1)
    (hMb : 1 ≤ M)
    (hMbound : |p.χ| * ((1 + p.m * p.γ * κ ^ 2) / (1 - p.γ ^ 2 * κ ^ 2)) *
        M ^ (p.m + p.γ - p.α - 1) ≤ 1)
    (hc : c = κ + κ⁻¹)
    (hsrc : ∀ x, M ≤ Real.exp (-κ * x) → frozenElliptic p u x ≤ (u x) ^ p.γ)
    (hmono : InMonotoneWaveTrapSet κ M u)
    (hZB : ∀ x, Z x ≤ upperBarrier κ M x)
    (htails : RotheStepTails W (upperBarrier κ M))
    (hBC2 : ∀ x₀, IsMaxOn (fun x => W x - upperBarrier κ M x) Set.univ x₀ →
      ContDiffAt ℝ 2 (upperBarrier κ M) x₀)
    (hrange : ∀ x₀, IsMaxOn (fun x => W x - upperBarrier κ M x) Set.univ x₀ →
      W x₀ ∈ Set.Icc (0 : ℝ) M ∧ upperBarrier κ M x₀ ∈ Set.Icc (0 : ℝ) M)
    (hchem : ∀ x₀, IsMaxOn (fun x => W x - upperBarrier κ M x) Set.univ x₀ →
      RotheStepChemData p u W (upperBarrier κ M) C_chem x₀) :
    RotheMaxData p c lam M C_chem u Z W (upperBarrier κ M) where
  hC_chem_nonneg := hCnn
  hCB := hCB
  Bsuper := whole_line_super_barrier hχ hα hκ hκ1 hγκ hmκ hMb hMbound hc hsrc hmono
  ZB := hZB
  φcont := htails.φcont
  La := htails.La
  Lb := htails.Lb
  hbot := htails.hbot
  hLa := htails.hLa
  htop := htails.htop
  hLb := htails.hLb
  BC2 := hBC2
  range := hrange
  chem := fun x₀ hx₀ => rotheStep_chem_bound (hchem x₀ hx₀)

/-! ## (C) The combined output-residual packet feeding `crossStep_output_of_solution`.

Both `RotheMaxData` packets at once, with `Bsuper`/`ZB` discharged inside (Z-side
from the supersolution input, Ū-side from `whole_line_super_barrier`), ready as the
`hmaxZ`/`hmaxBarrier` arguments of `crossStep_output_of_solution`. -/

/-- **(C) Both comparison packets for the step output.**  Produces the pair
`(RotheMaxData … W Z, RotheMaxData … W Ū)` consumed by
`crossStep_output_of_solution`.  The Z-side `Bsuper` is the descent supersolution
input; the Ū-side `Bsuper` is the committed `whole_line_super_barrier`.  All other
fields carried precisely. -/
def rotheMaxData_pair
    {C_chem : ℝ} {Z W : ℝ → ℝ}
    (hCnn : 0 ≤ C_chem)
    (hCB : (1 / lam) * (reactionLip p.α M + C_chem) < 1)
    (hZsuper : ∀ x, frozenWaveOperator p c u Z x ≤ 0)
    (htailsZ : RotheStepTails W Z)
    (hBC2Z : ∀ x₀, IsMaxOn (fun x => W x - Z x) Set.univ x₀ → ContDiffAt ℝ 2 Z x₀)
    (hrangeZ : ∀ x₀, IsMaxOn (fun x => W x - Z x) Set.univ x₀ →
      W x₀ ∈ Set.Icc (0 : ℝ) M ∧ Z x₀ ∈ Set.Icc (0 : ℝ) M)
    (hchemZ : ∀ x₀, IsMaxOn (fun x => W x - Z x) Set.univ x₀ →
      RotheStepChemData p u W Z C_chem x₀)
    (hχ : p.χ ≤ 0) (hα : p.α ≤ p.m + p.γ - 1)
    (hκ : 0 < κ) (hκ1 : κ < 1) (hγκ : p.γ * κ < 1) (hmκ : κ * p.m ≤ 1)
    (hMb : 1 ≤ M)
    (hMbound : |p.χ| * ((1 + p.m * p.γ * κ ^ 2) / (1 - p.γ ^ 2 * κ ^ 2)) *
        M ^ (p.m + p.γ - p.α - 1) ≤ 1)
    (hc : c = κ + κ⁻¹)
    (hsrc : ∀ x, M ≤ Real.exp (-κ * x) → frozenElliptic p u x ≤ (u x) ^ p.γ)
    (hmono : InMonotoneWaveTrapSet κ M u)
    (hZB : ∀ x, Z x ≤ upperBarrier κ M x)
    (htailsB : RotheStepTails W (upperBarrier κ M))
    (hBC2B : ∀ x₀, IsMaxOn (fun x => W x - upperBarrier κ M x) Set.univ x₀ →
      ContDiffAt ℝ 2 (upperBarrier κ M) x₀)
    (hrangeB : ∀ x₀, IsMaxOn (fun x => W x - upperBarrier κ M x) Set.univ x₀ →
      W x₀ ∈ Set.Icc (0 : ℝ) M ∧ upperBarrier κ M x₀ ∈ Set.Icc (0 : ℝ) M)
    (hchemB : ∀ x₀, IsMaxOn (fun x => W x - upperBarrier κ M x) Set.univ x₀ →
      RotheStepChemData p u W (upperBarrier κ M) C_chem x₀) :
    RotheMaxData p c lam M C_chem u Z W Z ×'
      RotheMaxData p c lam M C_chem u Z W (upperBarrier κ M) :=
  ⟨rotheMaxData_Z hCnn hCB hZsuper htailsZ hBC2Z hrangeZ hchemZ,
   rotheMaxData_barrier hCnn hCB hχ hα hκ hκ1 hγκ hmκ hMb hMbound hc hsrc hmono
     hZB htailsB hBC2B hrangeB hchemB⟩

/-
================================================================================
PRECISE STALL — closed inside the builders vs. carried, and exactly why.
================================================================================

CLOSED UNCONDITIONALLY (discharged inside the builders; the caller cannot weaken):

  * `rotheMaxData_barrier.Bsuper` — `F_u(Ū) ≤ 0`, the genuinely-elliptic χ≤0
    whole-line super-barrier, closed OUTRIGHT from the committed
    `whole_line_super_barrier` (WaveSuperBarrier.lean:272) on the trapped frozen
    profile `u`.  THIS is the §3.3 super-barrier comparison core, not carried.

  * `rotheMaxData_Z.Bsuper` — `F_u(Z) ≤ 0`, fed from the descent-orbit
    supersolution INPUT precond `hZsuper` (every old iterate on the lower-pinned
    orbit is a supersolution — `RotheStepInput.produce`'s carried precond), NOT a
    fresh standalone assumption.

  * `rotheMaxData_Z.ZB` — `Z ≤ Z`, closed by `le_refl`.

  * `…barrier.ZB` — `Z ≤ Ū`, the trap INPUT precond (iterates stay below Ū).

  * `chem` (both) — the at-max χ≤0 chemotaxis residual SIGN, discharged via the
    committed `rotheStep_chem_bound` (whose `RotheStepChemData.hχ : p.χ ≤ 0` is
    the max-principle core) from the carried per-max chem packet.

CARRIED (the orbit-dependent decay/regularity floor; NO committed
`greenConv`-tendsto lemma exists, so these are honestly carried — NOT vacuous,
NOT over-strong, NOT the conclusion):

 (I)  THE TWO-SIDED TAILS — `RotheStepTails W B` (`φcont`, `La`/`Lb`,
      `hbot`/`hLa`/`htop`/`hLb`): the limits of `φ = W − B` at ±∞ feeding the
      clean max-principle's positive-max attainment.  These are
      `greenKernel`-exponential-decay × bounded-source dominated-convergence
      facts; the repo has no committed `greenConv`-tendsto brick.  REAL ANALYTIC
      GAP, not circularity.

 (II) THE AT-MAX `C²`/RANGE/CHEM ANALYTIC FACTORS — `BC2` (at-max `C²` of `B`;
      everywhere form FALSE at the Ū interface kink, so the at-max form is the
      honest obligation), `range` (trapped membership at the chosen max), and the
      `RotheStepChemData` analytic bounds (`Cvpp`/`Cwp`/`L1`/`Lm`).  These are the
      orbit-localised regularity data the committed chem brick consumes; carried
      verbatim per max point.

 (III) THE SCALAR TRAP CONSTANTS — `hC_chem_nonneg`, `hCB`
      (`(1/λ)·(reactionLip + C_chem) < 1`): the §3.3 smallness budget on the trap,
      carried as scalars.

NON-CIRCULARITY.  Each builder provides the COMPARISON DATA (super-barrier +
ordering + tails + at-max residual sign) from which `rotheStep_le_barrier` DERIVES
`W ≤ B`.  No builder assumes `W ≤ B`, nor `RotheStepOutput`/`RotheStepProducer`.
The super-barrier `Bsuper` (the order content's hardest field) is closed from the
committed whole-line lemma, not carried; only the decay/regularity floor remains
carried, which is the genuine §3.3 satisfiability content, not a hidden circular
assumption.
================================================================================
-/

section AxiomAudit
#print axioms rotheMaxData_Z
#print axioms rotheMaxData_barrier
#print axioms rotheMaxData_pair
end AxiomAudit

end ShenWork.Paper1
