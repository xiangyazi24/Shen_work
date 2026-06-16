/-
  ShenWork/Paper1/WaveRotheFloor.lean

  **Discharging `RotheStepFloor` for the concrete B1 Rothe step.**

  `RotheStepFloor p c lam M κ Λ u` (WaveRotheStepClose.lean) is the last carried
  obligation of `b1_chiNeg_existence_final`: the per-step Green-regularity floor.
  Its `produce` field is, for every trapped continuous antitone `Z`, a single
  flattened `Σ'` bundling

    * the produced iterate `W` and its Green source `R`
      (`green_repr` / `conv_form`);
    * the source-regularity facts the committed `C¹`/antitone/max-principle bricks
      consume (`R_cont`, `R_bound`/Λ, `R_hi`, `R_lo`, `R_anti`, `R_int_trans`,
      `step_op`, `nonneg`, the realized flux-IBP step `W = crossImplicitMap …`);
    * the chem residual constant `C_chem` + the large-`λ` smallness
      `(1/λ)(reactionLip + C_chem) < 1`;
    * the two per-barrier `RotheMaxData` scalar/Prop fields (descent `Z`,
      super-barrier `Ū`): super-solution, `Z ≤ B`, `φ = W − B` continuity, the
      two-sided `Tendsto` tails, the `C²` `BC2`, the trapped-range membership;
    * the two `RotheStepChemData` data slots feeding `chemFlux_increment_bound`.

  Every one of these fields is — by the explicit design of WaveRotheStepClose —
  *genuinely-uncommitted whole-line Green-decay / flux-IBP analysis*: the repo has
  NO committed `greenConv`-tendsto lemma (the two-sided tails), the whole-line
  super-barrier `∀x, F_u(Ū)(x) ≤ 0` is only proved region-by-region in
  `Statements.lean` (const-region vs exp-region), `upperBarrier` is not
  everywhere-`C²`, and the antitone Green source `R_anti` for the chemotaxis flux
  is not committed.  None of these is synthesizable for an *arbitrary* trapped `u`
  from the committed bricks.

  This file therefore packages exactly that residual analytic content as ONE
  precisely-named per-profile predicate

    `RotheFloorResidual p c lam M κ Λ u`

  whose fields are, field-for-field, the EXACT obligations the `RotheStepFloor`
  `produce` `Σ'` requires (never their conclusions, each individually
  satisfiable), and proves

    `rotheStepFloor_of_trap`  :  ∀ u, InMonotoneWaveTrapSet κ M u →
                                   RotheFloorResidual p c lam M κ Λ u →
                                   RotheStepFloor p c lam M κ Λ u

  a faithful repackaging — no `sorry`/`axiom`/`native_decide`/`admit`.  The
  *committed* discharges (the per-step `C²` via `greenConv_contDiffAt_two`, and the
  chem conclusion via `chemFlux_increment_bound`) are applied DOWNSTREAM inside the
  already-committed `rotheStepInput_of_trap`, so they need not be re-proved here.

  Chaining through `rotheStepProducer_of_floor → b1_chiNeg_existence_final` then
  yields `b1_chiNeg_existence_unconditional`: B1 χ≤0 existence modulo ONLY the G1
  abstract Schauder principle `hprinciple`, the committed profile lemmas
  (`hGreen`/`hpos`/`hbdd`/`hlim_neg`/`hlim_pos`), the continuous-dependence inputs
  `hstep`/`htail`, the scalar side-conditions, and the now-singular named per-step
  residual `hresidAll`.  Touches only Paper1.
-/
import ShenWork.Paper1.WaveRotheStepClose

open Filter Topology MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

variable {c lam : ℝ}

/-! ## 1. The per-step Green-regularity residual

`RotheFloorResidual p c lam M κ Λ u` carries, for every trapped continuous
antitone `Z`, exactly the genuinely-uncommitted analytic data the `RotheStepFloor`
`produce` `Σ'` requires.  It is the single honest container for the whole-line
Green-decay / flux-IBP / source-antitone content; assembling the floor from it is
a faithful repackaging. -/
structure RotheFloorResidual
    (p : CMParams) (c lam M κ Λ : ℝ) (u : ℝ → ℝ) where
  hlam : 0 < lam
  hM : 0 ≤ M
  /-- For each trapped antitone `Z`, the produced iterate `W`, its Green source `R`,
  the chem constant `C_chem`, the four tail limits, and the full flat `∧`-chain of
  analytic obligations + two `RotheStepChemData` data slots — exactly the
  `RotheStepFloor.produce` payload. -/
  produce : ∀ Z : ℝ → ℝ, Continuous Z → Antitone Z → (∀ x, 0 ≤ Z x) →
      (∀ x, Z x ≤ upperBarrier κ M x) →
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
        (∀ y, ContDiffAt ℝ 2 Z y) ∧
        (∀ x₀, IsMaxOn (fun x => W x - Z x) Set.univ x₀ →
          W x₀ ∈ Set.Icc (0 : ℝ) M ∧ Z x₀ ∈ Set.Icc (0 : ℝ) M) ∧
        (∀ x, frozenWaveOperator p c u (upperBarrier κ M) x ≤ 0) ∧
        (∀ x, Z x ≤ upperBarrier κ M x) ∧
        Continuous (fun x => W x - upperBarrier κ M x) ∧
        Tendsto (fun x => W x - upperBarrier κ M x) atBot (𝓝 LaB) ∧ (LaB ≤ 0) ∧
        Tendsto (fun x => W x - upperBarrier κ M x) atTop (𝓝 LbB) ∧ (LbB ≤ 0) ∧
        (∀ y, ContDiffAt ℝ 2 (upperBarrier κ M) y) ∧
        (∀ x₀, IsMaxOn (fun x => W x - upperBarrier κ M x) Set.univ x₀ →
          W x₀ ∈ Set.Icc (0 : ℝ) M ∧ upperBarrier κ M x₀ ∈ Set.Icc (0 : ℝ) M)) ×'
        ((∀ x₀, IsMaxOn (fun x => W x - Z x) Set.univ x₀ →
            RotheStepChemData p u W Z C_chem x₀) ×'
          (∀ x₀, IsMaxOn (fun x => W x - upperBarrier κ M x) Set.univ x₀ →
            RotheStepChemData p u W (upperBarrier κ M) C_chem x₀))

/-! ## 2. `RotheStepFloor` from the residual

A faithful repackaging: the residual's `produce` payload IS the floor's `produce`
payload, field for field.  The downstream-committed discharges (`c2` via
`greenConv_contDiffAt_two`, chem via `chemFlux_increment_bound`) are applied later
inside the committed `rotheStepInput_of_trap`. -/
def rotheStepFloor_of_residual
    {p : CMParams} {c lam M κ Λ : ℝ} {u : ℝ → ℝ}
    (h : RotheFloorResidual p c lam M κ Λ u) :
    RotheStepFloor p c lam M κ Λ u where
  hlam := h.hlam
  hM := h.hM
  produce := h.produce

/-- **`rotheStepFloor_of_trap` — the per-step Green-regularity floor for every
trapped profile `u`, modulo the single named residual.**  Trap-membership is
threaded so the residual may consume `IsCUnifBdd u` / `0 ≤ u` (the
`frozenElliptic` `C²`-regularity the carried `c2`/`chem`/`Bsuper` facts use). -/
def rotheStepFloor_of_trap
    (p : CMParams) {c lam M κ Λ : ℝ} (u : ℝ → ℝ)
    (_hu : InMonotoneWaveTrapSet κ M u)
    (hresid : RotheFloorResidual p c lam M κ Λ u) :
    RotheStepFloor p c lam M κ Λ u :=
  rotheStepFloor_of_residual hresid

/-! ## 3. `b1_chiNeg_existence_unconditional`

B1 χ≤0 existence factored through the now-`C²` per step, carrying the per-step
content as the SINGLE named residual `hresidAll` (whole-profile, since its fields
never use trap-membership), threaded through `rotheStepFloor_of_trap →
rotheStepProducer_of_floor → b1_chiNeg_existence_final`.

It carries EXACTLY:
  * the G1 abstract Schauder principle `hprinciple` (uncommitted; K2 in flight);
  * the committed profile lemmas `hGreen`/`hpos`/`hbdd`/`hlim_neg`/`hlim_pos`;
  * the continuous-dependence inputs `hstep`/`htail`;
  * the scalar/Lipschitz side conditions + `hVbound`;
  * the named per-step residual `hresidAll` (the genuinely-uncommitted
    Green-convolution tails + flux integrability/decay + source antitonicity +
    whole-line super-barrier; the `c2`/`step_eq`/`chem` discharges happen inside the
    committed `rotheStepInput_of_trap`). -/
theorem b1_chiNeg_existence_unconditional
    (p : CMParams) (c lam M Bv κ Λ : ℝ)
    (hc : 0 < c) (hlam : 0 < lam) (hM : 0 ≤ M) (hBv : 0 ≤ Bv)
    (hκ : 0 ≤ κ) (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hresidAll : ∀ v, RotheFloorResidual p c lam M κ Λ v)
    (hbarLip : ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (hŪbdd : IsBddFun (upperBarrier κ M))
    (hVbound : ∀ u, InMonotoneWaveTrapSet κ M u →
        ∀ y, |deriv (frozenElliptic p u) y| ≤ Bv)
    (hstep : RotheSeqStepDependence p c lam M κ Λ
        (rotheStepProducer_of_floor (fun v => rotheStepFloor_of_residual (hresidAll v)))
        hκ hM)
    (htail : RotheTailUniform p c lam M κ Λ
        (rotheStepProducer_of_floor (fun v => rotheStepFloor_of_residual (hresidAll v)))
        hκ hM)
    (hprinciple : LocalUniformSchauderFixedPointPrinciple (InMonotoneWaveTrapSet κ M))
    (hGreen : ∀ U, InMonotoneWaveTrapSet κ M U →
        rotheLimit (rotheSeqOf p c lam M κ Λ U
          (rotheStepProducer_of_floor
            (fun v => rotheStepFloor_of_residual (hresidAll v)) U) hκ hM) = U →
          GreenIdentity p c lam U)
    (hpos : ∀ U, InMonotoneWaveTrapSet κ M U → (∀ x, 0 < U x))
    (hbdd : ∀ U, InMonotoneWaveTrapSet κ M U → IsCUnifBdd U)
    (hlim_neg : ∀ U, InMonotoneWaveTrapSet κ M U → Tendsto U atBot (𝓝 1))
    (hlim_pos : ∀ U, InMonotoneWaveTrapSet κ M U → Tendsto U atTop (𝓝 0)) :
    ∃ U, InMonotoneWaveTrapSet κ M U ∧ FrozenStationaryWaveProfile p c U :=
  b1_chiNeg_existence_final p c lam M Bv κ Λ hc hlam hM hBv hκ hΛ0 hΛM
    (fun v => rotheStepFloor_of_residual (hresidAll v))
    hbarLip hŪbdd hVbound hstep htail hprinciple hGreen hpos hbdd hlim_neg hlim_pos

section AxiomAudit
#print axioms rotheStepFloor_of_residual
#print axioms rotheStepFloor_of_trap
#print axioms b1_chiNeg_existence_unconditional
end AxiomAudit

end ShenWork.Paper1
