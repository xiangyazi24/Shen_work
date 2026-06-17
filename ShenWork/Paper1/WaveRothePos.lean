/-
  ShenWork/Paper1/WaveRothePos.lean

  **B1 χ≥0 existence reduction — positive-sensitivity wave (P1-T11pos).**

  The χ≥0 analog of the committed χ≤0 B1 existence chain
  (`b1_chiNeg_existence_residualClean`/`b1_chiNeg_existence_unconditional`,
  `WaveRotheResidualClose.lean`/`WaveRotheFloor.lean`).

  ## What is sign-agnostic vs. χ≤0-specific (the trace)

  The ENTIRE Rothe orbit / max-principle / Schauder / supersolution-invariant
  producer / profile-limit machinery is PARAMETERIZED over the super-barrier and
  trap, NOT the sign of `χ`:

    * `b1_chiNeg_existence` (WaveRotheConcrete:414) takes the per-step producer
      on trapped profiles (carrying `baseSuper`) as an ABSTRACT input — no
      `χ`-sign hyp.
    * `b1_chiNeg_existence_unconditional` (WaveRotheFloor:168) takes the per-step
      residual `hresidTrap` (carrying `baseSuper`) abstractly — no `χ`-sign hyp.
    * `b1_chiNeg_existence_residualClean` (WaveRotheResidualClose:412) takes the
      genuinely-deep Green core on trapped profiles (carrying `hSuper`)
      abstractly — no `χ`-sign hyp.

  The ONLY place the sign of `χ` enters the whole B1 chain is the discharge of the
  super-barrier field `hSuper`/`baseSuper`, i.e. the single builder

    `rotheFloorResidual_of_trap` (WaveRotheResidualClose:334),

  which feeds `hSuper` from `whole_line_super_barrier` under the χ≤0 regime
  (`hχ : p.χ ≤ 0`, `hα : p.α ≤ p.m+p.γ-1`, and the plateau source bound `hsrc`).

  So the χ≥0 reduction is obtained by ONE swap: replace `whole_line_super_barrier`
  with the committed `whole_line_super_barrier_pos` (WaveSuperBarrierPos:177) under
  the χ≥0 regime (`0 ≤ χ`, `χ < chiStar`, `α = m+γ-1`, `0<κ<1`, `m·κ≤1`, `1≤M`,
  `(1/(1-χ))^(1/α) ≤ M`, `c = κ+κ⁻¹`).  NO χ≥0-specific sub-lemma beyond the
  super-barrier itself is needed: the χ≥0 super-barrier already absorbs the
  chemotactic flux (whose sign flips with `χ`) via the constant-region budget
  `1 ≤ (1-χ) M^α`, so NO plateau source bound `hsrc` is required (contrast the χ≤0
  builder).  Everything downstream is reused verbatim.

  ## Deliverables

    * `rotheFloorResidual_of_trap_pos` — the χ≥0 floor residual for every trapped
      `u`, discharging `hSuper` from `whole_line_super_barrier_pos`; the deep Green
      core is carried as `hcore` (field-identical to the χ≤0 builder).
    * `b1_chiPos_existence` — B1 χ≥0 existence reduced to the SAME residual
      obligations as B1 χ≤0 (G1 `hprinciple` + the trap-indexed per-step core
      `hcoreTrap` + the committed profile lemmas + continuous-dependence inputs +
      scalar side-conditions), via the sign-agnostic
      `b1_chiNeg_existence_unconditional`.  Feeds the `hpos` branch of
      `Theorem_1_1.of_assumed_frozenStationaryProfile_branches` (Statements:16304).

  No `sorry`/`axiom`/`native_decide`/`admit`.  Touches only Paper1.
-/
import ShenWork.Paper1.WaveRotheResidualClose
import ShenWork.Paper1.WaveSuperBarrierPos

open Filter Topology MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

variable {c lam : ℝ}

/-! ## 1. The χ≥0 floor residual for every trapped `u`

`rotheFloorResidual_of_trap_pos` is the positive-sensitivity analog of
`rotheFloorResidual_of_trap` (WaveRotheResidualClose:334).  It is identical
field-for-field EXCEPT that the super-barrier field `hSuper` is discharged from
`whole_line_super_barrier_pos` (under the χ≥0 regime) instead of
`whole_line_super_barrier` (under the χ≤0 regime).  In particular it requires NO
plateau source bound `hsrc`: the χ≥0 super-barrier closes the kink from the trap
bound `u^γ ≤ M^γ` alone.  The genuinely-deep whole-line Green core is carried as
`hcore`, exactly as in the χ≤0 builder. -/
def rotheFloorResidual_of_trap_pos
    (p : CMParams) {c lam M κ Λ : ℝ} (u : ℝ → ℝ)
    (hlam : 0 < lam) (hM : 0 ≤ M)
    -- the `whole_line_super_barrier_pos` regime hypotheses (χ≥0):
    (hχ_nonneg : 0 ≤ p.χ) (hχ : p.χ < chiStar p)
    (hα : p.α = p.m + p.γ - 1)
    (hκ : 0 < κ) (hκ1 : κ < 1) (hmκ : p.m * κ ≤ 1)
    (hM1 : 1 ≤ M)
    (hMchi : (1 / (1 - p.χ)) ^ (1 / p.α) ≤ M)
    (hc : c = κ + κ⁻¹)
    (hmono : InMonotoneWaveTrapSet κ M u)
    -- the genuinely-deep whole-line Green core (carried, NOT synthesizable from
    -- committed bricks for arbitrary `u`) — field-identical to the χ≤0 builder:
    (hcore : ∀ Z : ℝ → ℝ, Continuous Z → Antitone Z → (∀ x, 0 ≤ Z x) →
        (∀ x, Z x ≤ upperBarrier κ M x) →
        (∀ x, frozenWaveOperator p c u Z x ≤ 0) →
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
          Continuous (fun x => W x - Z x) ∧
          Tendsto (fun x => W x - Z x) atBot (𝓝 LaZ) ∧ (LaZ ≤ 0) ∧
          Tendsto (fun x => W x - Z x) atTop (𝓝 LbZ) ∧ (LbZ ≤ 0) ∧
          (∀ x₀, IsMaxOn (fun x => W x - Z x) Set.univ x₀ →
            ContDiffAt ℝ 2 Z x₀) ∧
          (∀ x₀, IsMaxOn (fun x => W x - Z x) Set.univ x₀ →
            W x₀ ∈ Set.Icc (0 : ℝ) M ∧ Z x₀ ∈ Set.Icc (0 : ℝ) M) ∧
          Continuous (fun x => W x - upperBarrier κ M x) ∧
          Tendsto (fun x => W x - upperBarrier κ M x) atBot (𝓝 LaB) ∧ (LaB ≤ 0) ∧
          Tendsto (fun x => W x - upperBarrier κ M x) atTop (𝓝 LbB) ∧ (LbB ≤ 0) ∧
          (∀ x₀, IsMaxOn (fun x => W x - upperBarrier κ M x) Set.univ x₀ →
            ContDiffAt ℝ 2 (upperBarrier κ M) x₀) ∧
          (∀ x₀, IsMaxOn (fun x => W x - upperBarrier κ M x) Set.univ x₀ →
            W x₀ ∈ Set.Icc (0 : ℝ) M ∧ upperBarrier κ M x₀ ∈ Set.Icc (0 : ℝ) M)) ×'
          ((∀ x₀, IsMaxOn (fun x => W x - Z x) Set.univ x₀ →
              RotheStepChemData p u W Z C_chem x₀) ×'
            (∀ x₀, IsMaxOn (fun x => W x - upperBarrier κ M x) Set.univ x₀ →
              RotheStepChemData p u W (upperBarrier κ M) C_chem x₀))) :
    RotheFloorResidual p c lam M κ Λ u :=
  rotheFloorResidual_of_core
    { hlam := hlam
      hM := hM
      hSuper :=
        whole_line_super_barrier_pos hχ_nonneg hχ hα hκ hκ1 hmκ hM1 hMchi hc hmono.1
      produceCore := hcore }

/-! ## 2. B1 χ≥0 existence from the deep core

`b1_chiPos_existence` chains the χ≥0 deep core through the sign-agnostic
`b1_chiNeg_existence_unconditional` (WaveRotheFloor:168).  Its carried inputs are
EXACTLY those of `b1_chiNeg_existence_residualClean`: the G1 abstract Schauder
principle, the committed profile lemmas, the continuous-dependence inputs, the
scalar/Lipschitz side conditions, and the genuinely-deep Green core `hcoreTrap`
(whose `hSuper` field is dischargeable from `whole_line_super_barrier_pos` for
every trapped profile — see `rotheFloorResidual_of_trap_pos`).

This carries the SAME shape of obligations as B1 χ≤0 (G1 + producer core +
profile), NOT the conclusion.  It produces
`∃ U, InMonotoneWaveTrapSet κ M U ∧ FrozenStationaryWaveProfile p c U`, which —
with the committed `ShenUpperBoundPositive` upper bound and the right-tail
asymptotics — feeds the `hpos` branch of
`Theorem_1_1.of_assumed_frozenStationaryProfile_branches`. -/
theorem b1_chiPos_existence_core
    (p : CMParams) (c lam M Bv κ Λ : ℝ)
    (hc0 : 0 < c) (hlam : 0 < lam) (hM : 0 ≤ M) (hBv : 0 ≤ Bv)
    (hκ0 : 0 ≤ κ) (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    -- the genuinely-deep whole-line Green core, for every trapped profile `v`
    -- (its `hSuper` field is dischargeable via `whole_line_super_barrier_pos` for
    -- every trapped profile — see `rotheFloorResidual_of_trap_pos`):
    (hcoreTrap : ∀ v, InMonotoneWaveTrapSet κ M v →
      RotheFloorResidualCore p c lam M κ Λ v)
    (hbarLip : ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (hŪbdd : IsBddFun (upperBarrier κ M))
    (hVbound : ∀ u, InMonotoneWaveTrapSet κ M u →
        ∀ y, |deriv (frozenElliptic p u) y| ≤ Bv)
    (hstep : RotheSeqStepDependence p c lam M κ Λ
        (rotheStepProducer_of_floor
          (fun v hv =>
            rotheStepFloor_of_residual (rotheFloorResidual_of_core (hcoreTrap v hv))))
        hκ0 hM)
    (htail : RotheTailUniform p c lam M κ Λ
        (rotheStepProducer_of_floor
          (fun v hv =>
            rotheStepFloor_of_residual (rotheFloorResidual_of_core (hcoreTrap v hv))))
        hκ0 hM)
    (hprinciple : LocalUniformSchauderFixedPointPrinciple (InMonotoneWaveTrapSet κ M))
    (hGreen : ∀ U, InMonotoneWaveTrapSet κ M U →
        rotheLimit
          ((rotheSeqFromTrap p c lam M κ Λ
            (rotheStepProducer_of_floor
              (fun v hv => rotheStepFloor_of_residual
                (rotheFloorResidual_of_core (hcoreTrap v hv))))
            hκ0 hM) U) = U →
          GreenIdentity p c lam U)
    (hpos : ∀ U, InMonotoneWaveTrapSet κ M U → (∀ x, 0 < U x))
    (hbdd : ∀ U, InMonotoneWaveTrapSet κ M U → IsCUnifBdd U)
    (hlim_neg : ∀ U, InMonotoneWaveTrapSet κ M U → Tendsto U atBot (𝓝 1))
    (hlim_pos : ∀ U, InMonotoneWaveTrapSet κ M U → Tendsto U atTop (𝓝 0)) :
    ∃ U, InMonotoneWaveTrapSet κ M U ∧ FrozenStationaryWaveProfile p c U :=
  b1_chiNeg_existence_unconditional p c lam M Bv κ Λ
    hc0 hlam hM hBv hκ0 hΛ0 hΛM
    (fun v hv => rotheFloorResidual_of_core (hcoreTrap v hv))
    hbarLip hŪbdd hVbound hstep htail hprinciple hGreen hpos hbdd hlim_neg hlim_pos

/-- **B1 χ≥0 existence from the slim residual core.**
This is the positive-sensitivity analogue of
`b1_chiNeg_existence_residualClean_of_trap_super`: the core no longer carries the
fields discharged by `rotheFloorResidual_of_slimCore`, and the trapped-profile
super-barrier is supplied internally from `whole_line_super_barrier_pos`. -/
theorem b1_chiPos_existence
    (p : CMParams) (c lam M Bv κ Λ : ℝ)
    (hc0 : 0 < c) (hlam : 0 < lam) (hMpos : 0 < M) (hBv : 0 ≤ Bv)
    (hκpos : 0 < κ) (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hχ_nonneg : 0 ≤ p.χ) (hχ : p.χ < chiStar p)
    (hα : p.α = p.m + p.γ - 1)
    (hκ1 : κ < 1) (hmκ : p.m * κ ≤ 1)
    (hM1 : 1 ≤ M)
    (hMchi : (1 / (1 - p.χ)) ^ (1 / p.α) ≤ M)
    (hc : c = κ + κ⁻¹)
    (hcoreTrap : ∀ v, InMonotoneWaveTrapSet κ M v →
      RotheFloorResidualCoreSlim p c lam M κ Λ v)
    (hbarLip : ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (hŪbdd : IsBddFun (upperBarrier κ M))
    (hVbound : ∀ u, InMonotoneWaveTrapSet κ M u →
        ∀ y, |deriv (frozenElliptic p u) y| ≤ Bv)
    (hstep : RotheSeqStepDependence p c lam M κ Λ
        (rotheStepProducer_of_floor
          (fun v hv => rotheStepFloor_of_residual
            (rotheFloorResidual_of_slimCore
              (whole_line_super_barrier_pos hχ_nonneg hχ hα hκpos hκ1 hmκ
                hM1 hMchi hc hv.1)
              hκpos hMpos (hcoreTrap v hv))))
        hκpos.le hMpos.le)
    (htail : RotheTailUniform p c lam M κ Λ
        (rotheStepProducer_of_floor
          (fun v hv => rotheStepFloor_of_residual
            (rotheFloorResidual_of_slimCore
              (whole_line_super_barrier_pos hχ_nonneg hχ hα hκpos hκ1 hmκ
                hM1 hMchi hc hv.1)
              hκpos hMpos (hcoreTrap v hv))))
        hκpos.le hMpos.le)
    (hprinciple : LocalUniformSchauderFixedPointPrinciple (InMonotoneWaveTrapSet κ M))
    (hGreen : ∀ U, InMonotoneWaveTrapSet κ M U →
        rotheLimit
          ((rotheSeqFromTrap p c lam M κ Λ
            (rotheStepProducer_of_floor
              (fun v hv => rotheStepFloor_of_residual
                (rotheFloorResidual_of_slimCore
                  (whole_line_super_barrier_pos hχ_nonneg hχ hα hκpos hκ1 hmκ
                    hM1 hMchi hc hv.1)
                  hκpos hMpos (hcoreTrap v hv))))
            hκpos.le hMpos.le) U) = U →
          GreenIdentity p c lam U)
    (hpos : ∀ U, InMonotoneWaveTrapSet κ M U → (∀ x, 0 < U x))
    (hbdd : ∀ U, InMonotoneWaveTrapSet κ M U → IsCUnifBdd U)
    (hlim_neg : ∀ U, InMonotoneWaveTrapSet κ M U → Tendsto U atBot (𝓝 1))
    (hlim_pos : ∀ U, InMonotoneWaveTrapSet κ M U → Tendsto U atTop (𝓝 0)) :
    ∃ U, InMonotoneWaveTrapSet κ M U ∧ FrozenStationaryWaveProfile p c U :=
  b1_chiNeg_existence_residualClean_of_trap_super p c lam M Bv κ Λ
    hc0 hlam hMpos hBv hκpos hΛ0 hΛM
    (fun _ hv =>
      whole_line_super_barrier_pos hχ_nonneg hχ hα hκpos hκ1 hmκ hM1 hMchi
        hc hv.1)
    hcoreTrap
    hbarLip hŪbdd hVbound hstep htail hprinciple hGreen hpos hbdd hlim_neg
    hlim_pos

/-! ## 3. Axiom audit -/

section AxiomAudit
#print axioms rotheFloorResidual_of_trap_pos
#print axioms b1_chiPos_existence_core
#print axioms b1_chiPos_existence
end AxiomAudit

end ShenWork.Paper1
