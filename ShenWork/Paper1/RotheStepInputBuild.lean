/-
  ShenWork/Paper1/RotheStepInputBuild.lean

  **P1 #4 — building `RotheStepInput`/`RotheStepProducer` (hprodTrap) via the
  LIVE producer route, with the two-sided max-principle tails DISCHARGED from
  the landed `GreenConvTails` bricks.**

  The committed `rotheStepProducer_of_floor` (WaveRotheStepClose.lean) already
  routes `RotheStepFloor → RotheStepInput → rotheStepProducer_of_input →
  RotheStepProducer` (the `hprodTrap` shape consumed by
  `b1_chiNeg_existence_clean`), and the chem sign rides the contact-point clean
  max principle inside `rotheStep_le_barrier` — NOT the global (★)
  quasi-monotonicity, which is redundant.

  This file TIGHTENS the carried surface: instead of carrying the two raw
  `RotheStepTails` packets per trapped `Z` (14 limit Prop-fields across the
  descent barrier `Z` and the super-barrier `Ū`), we carry only the SOURCE-side
  two-sided limits of the Green source `R` (`Rbot`/`Rtop`) and of the descent
  barrier `Z` (`Zbot`/`Ztop`), plus the genuine §3.3 ordering signs, and
  DISCHARGE both `RotheStepTails` packets internally via
  `rotheStepTails_greenConv_of_barrier_limits` /
  `rotheStepTails_greenConv_upperBarrier` (landed in `GreenConvTails`).

  The resulting `RotheStepInputBuild` floor is then assembled into the committed
  `RotheStepFloor`, fed to `rotheStepProducer_of_floor`, yielding the
  `hprodTrap`-shaped `∀ u, trap u → RotheStepProducer p c lam M κ Λ u`.

  HONEST ACCOUNTING.  `hprodTrap` is NOT unconditional for trapped `u`: the
  per-`Z` `produce` content (the Green source `R` + its bound/limits, the
  `step_eq` flux-IBP bridge `W = crossImplicitMap`, the differential `step_op`,
  the lower trap `nonneg`, the at-max `BC2`/`range`/`chem` elliptic packets and
  the antitone data) is genuinely carried — the landed #4-A/#4-I/GreenConvTails
  bricks are BUILDERS that consume exactly this per-`Z` data, with no landed
  lemma synthesizing it over all trapped `Z`.  What this file removes from the
  carried surface is precisely the tail/limit Prop-bundle, now discharged from
  the landed Green-convolution-tendsto bricks.  No existing file is edited; no
  `sorry`/`admit`/`native_decide`/custom axiom.
-/
import ShenWork.Paper1.WaveRotheStepClose
import ShenWork.Paper1.GreenConvTails

open Filter Topology MeasureTheory Real Set

set_option maxHeartbeats 1000000

noncomputable section

namespace ShenWork.Paper1

variable {p : CMParams} {c lam M κ Λ : ℝ} {u : ℝ → ℝ}

/-- The TIGHTENED per-step floor: identical to `RotheStepFloor` except the two
raw `RotheStepTails` packets are replaced by the SOURCE/barrier two-sided limit
scalars (`Rbot`/`Rtop`, `Zbot`/`Ztop`) plus the §3.3 ordering signs, from which
the tails are reconstructed by `GreenConvTails`.  Everything else (the Green
source rep, source regularity, `step_op`, `nonneg`, `step_eq` bridge, scalar
max-data fields, at-max `BC2`/`range`, antitone + chem data) is carried verbatim
— the irreducible per-`Z` content. -/
structure RotheStepInputBuild
    (p : CMParams) (c lam M κ Λ : ℝ) (u : ℝ → ℝ) where
  hlam : 0 < lam
  hM : 0 ≤ M
  hκ : 0 < κ
  baseSuper : ∀ x, frozenWaveOperator p c u (upperBarrier κ M) x ≤ 0
  produce : ∀ Z : ℝ → ℝ, Continuous Z → Antitone Z → (∀ x, 0 ≤ Z x) →
      (∀ x, Z x ≤ upperBarrier κ M x) →
      (∀ x, frozenWaveOperator p c u Z x ≤ 0) →
      Σ' (W : ℝ → ℝ) (R : ℝ → ℝ) (C_chem Rbot Rtop Zbot Ztop : ℝ),
        ((W = fun x => greenConv c lam R x) ∧
        (W = fun x => ∫ y, greenKernel c lam (x - y) * R y) ∧
        Continuous R ∧
        (∃ B : ℝ, (∀ y, |R y| ≤ B) ∧ Λ = 2 * (greenDelta c lam)⁻¹ * B) ∧
        (∀ x, IntegrableOn (gWeight (greenRootPlus c lam) R) (Ioi x)) ∧
        (∀ x, IntegrableOn (gWeight (greenRootMinus c lam) R) (Iic x)) ∧
        (∀ x, Integrable (fun t => greenKernel c lam (-t) * R (x + t))) ∧
        (∀ x, implicitStepOp p c (1 / lam) u W x = Z x) ∧
        (∀ x, 0 ≤ W x) ∧
        (W = crossImplicitMap p c lam u Z W) ∧
        (0 ≤ C_chem) ∧
        ((1 / lam) * (reactionLip p.α M + C_chem) < 1) ∧
        -- the two-sided source/barrier limits feeding GreenConvTails:
        Tendsto R atBot (𝓝 Rbot) ∧ Tendsto R atTop (𝓝 Rtop) ∧
        Continuous Z ∧
        Tendsto Z atBot (𝓝 Zbot) ∧ Tendsto Z atTop (𝓝 Ztop) ∧
        -- §3.3 ordering signs (descent barrier B = Z, super-barrier B = Ū):
        (Rbot * lam⁻¹ ≤ Zbot) ∧ (Rtop * lam⁻¹ ≤ Ztop) ∧
        (Rbot * lam⁻¹ ≤ M) ∧ (Rtop * lam⁻¹ ≤ 0) ∧
        -- the at-max C²/range scalar fields (descent barrier B = Z):
        (∀ x, frozenWaveOperator p c u Z x ≤ 0) ∧
        (∀ x, Z x ≤ Z x) ∧
        (∀ x₀, IsMaxOn (fun x => W x - Z x) Set.univ x₀ →
          ContDiffAt ℝ 2 Z x₀) ∧
        (∀ x₀, IsMaxOn (fun x => W x - Z x) Set.univ x₀ →
          W x₀ ∈ Set.Icc (0 : ℝ) M ∧ Z x₀ ∈ Set.Icc (0 : ℝ) M) ∧
        -- super-barrier B = Ū:
        (∀ x, frozenWaveOperator p c u (upperBarrier κ M) x ≤ 0) ∧
        (∀ x, Z x ≤ upperBarrier κ M x) ∧
        (∀ x₀, IsMaxOn (fun x => W x - upperBarrier κ M x) Set.univ x₀ →
          ContDiffAt ℝ 2 (upperBarrier κ M) x₀) ∧
        (∀ x₀, IsMaxOn (fun x => W x - upperBarrier κ M x) Set.univ x₀ →
          W x₀ ∈ Set.Icc (0 : ℝ) M ∧
            upperBarrier κ M x₀ ∈ Set.Icc (0 : ℝ) M)) ×'
        (RotheStepAntitoneData p c lam M C_chem u Z W ×'
        ((∀ x₀, IsMaxOn (fun x => W x - Z x) Set.univ x₀ →
            RotheStepChemData p u W Z C_chem x₀) ×'
          (∀ x₀, IsMaxOn (fun x => W x - upperBarrier κ M x) Set.univ x₀ →
            RotheStepChemData p u W (upperBarrier κ M) C_chem x₀)))

/-- **`rotheStepFloor_of_build` — discharge the tail packets via GreenConvTails.**
From the tightened `RotheStepInputBuild` (carrying source/barrier limits in place
of the raw `RotheStepTails`), assemble the committed `RotheStepFloor`: both
`RotheStepTails` packets (against `Z` and against `Ū`) are built internally by
`rotheStepTails_greenConv_of_barrier_limits` /
`rotheStepTails_greenConv_upperBarrier`, after rewriting `W = greenConv c lam R`.
Every other field is forwarded verbatim. -/
def rotheStepFloor_of_build
    (hb : RotheStepInputBuild p c lam M κ Λ u) :
    RotheStepFloor p c lam M κ Λ u where
  hlam := hb.hlam
  hM := hb.hM
  baseSuper := hb.baseSuper
  produce := by
    intro Z hZc hZa hZ0 hZB hZsuper
    obtain ⟨W, R, C_chem, Rbot, Rtop, Zbot, Ztop,
        ⟨hgr, hcf, hRc, hRb, hRhi, hRlo, hRint, hstepop, hnonneg,
          hstepeq, hCnn, hCB, hRbot, hRtop, _hZcont, hZbot, hZtop,
          hbotZ_le, htopZ_le, hbotB_le, htopB_le,
          hBsupZ, hZZ, hBC2Z, hrangeZ,
          hBsupB, hZleB, hBC2B, hrangeB⟩,
        hanti, hchemZ, hchemB⟩ :=
      hb.produce Z hZc hZa hZ0 hZB hZsuper
    -- the uniform source bound (extracted via choice; `hRb : ∃ B, …` is Prop):
    have hRbBound : ∀ y, |R y| ≤ hRb.choose := hRb.choose_spec.1
    -- tails vs descent barrier Z (arbitrary trapped antitone with limits):
    have htailsZ : RotheStepTails W Z := by
      rw [hgr]
      exact rotheStepTails_greenConv_of_barrier_limits (c := c) (lam := lam)
        hb.hlam hRc hRbBound hRbot hRtop hZc hZbot hZtop hbotZ_le htopZ_le
    -- tails vs super-barrier Ū:
    have htailsB : RotheStepTails W (upperBarrier κ M) := by
      rw [hgr]
      exact rotheStepTails_greenConv_upperBarrier (c := c) (lam := lam)
        hb.hlam hb.hκ hb.hM hRc hRbBound hRbot hRtop hbotB_le htopB_le
    refine ⟨W, R, C_chem,
      htailsZ.La, htailsZ.Lb, htailsB.La, htailsB.Lb,
      ⟨hgr, hcf, hRc, hRb, hRhi, hRlo, hRint, hstepop, hnonneg,
        hstepeq, hCnn, hCB,
        hBsupZ, hZZ, htailsZ.φcont, htailsZ.hbot, htailsZ.hLa,
        htailsZ.htop, htailsZ.hLb, hBC2Z, hrangeZ,
        hBsupB, hZleB, htailsB.φcont, htailsB.hbot, htailsB.hLa,
        htailsB.htop, htailsB.hLb, hBC2B, hrangeB⟩,
      hanti, hchemZ, hchemB⟩

/-- **`rotheStepProducer_of_build` — the `hprodTrap` shape from the tightened
floor.**  For every trapped profile `u`, the tightened per-step build yields
`RotheStepProducer p c lam M κ Λ u` — EXACTLY the `hprodTrap` field consumed by
`b1_chiNeg_existence_clean` → `construction_neg`.  The chem sign rides the
contact-point clean max principle inside `rotheStep_le_barrier` (the live
producer route), NOT the redundant global (★) quasi-monotonicity. -/
theorem rotheStepProducer_of_build
    (hbuildTrap : ∀ v, InMonotoneWaveTrapSet κ M v →
      RotheStepInputBuild p c lam M κ Λ v) :
    ∀ u, InMonotoneWaveTrapSet κ M u → RotheStepProducer p c lam M κ Λ u :=
  rotheStepProducer_of_floor (fun v hv => rotheStepFloor_of_build (hbuildTrap v hv))

section AxiomAudit
#print axioms rotheStepFloor_of_build
#print axioms rotheStepProducer_of_build

end AxiomAudit

end ShenWork.Paper1
