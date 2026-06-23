/-
  ShenWork/Paper1/IntervalP1StepInputAssembly.lean

  P1 FINAL — assembling `RotheStepInput` from the per-step residual and feeding it
  through `admissible_closure` to discharge the `hin` floor over the admissible
  orbit.

  GOAL (task spec /tmp/shen_p1floor.md).  `admissible_closure`
  (IntervalP1AdmissibleClosure.lean) reduces `construction_neg`'s per-step producer,
  over the strengthened `AdmissibleZ` class, to the carried `hin : RotheStepInput`
  (the per-step analytic floor) plus the produced-source endpoint datum `hsrc`.
  This file CONSUMES the landed builders to DERIVE `RotheStepInput` for every
  trapped profile, and then runs `admissible_closure` to obtain the admissible
  step map — DERIVED modulo EXACTLY the per-`Z` residual + `hsrc`, nothing else.

  WHAT IS DERIVED (no re-proof; all from landed bricks).
    * `rotheStepInput_of_residualProvider` — `RotheStepInput p c lam M κ Λ u` for a
      trapped `u`, from the per-trapped-`Z` `RotheFloorOrbitDataResidual` provider,
      via the LANDED chain `rotheStepFloor_of_orbitResidual` (RotheFloorOrbitDataImpl)
      → `rotheStepInput_of_trap` (WaveRotheStepClose).
    * `admissibleStep_of_residualProvider` — the admissible-orbit step
      `AdmissibleZ u Z → Σ W, RotheStepOutput u Z W ×' AdmissibleZ u W`, from the
      derived `RotheStepInput` fed to the LANDED `admissible_closure`.  The `hin`
      floor in `admissible_closure` is DISCHARGED by the derived input; only the
      named per-`Z` residual + `hsrc` remain carried.

  WHAT IS CARRIED (the genuine per-step Cauchy frontier — NOT the conclusion).
    The per-trapped-`Z` `RotheFloorOrbitDataResidual` (RotheFloorOrbitDataImpl.lean:90):
    for the PRODUCED iterate `W = greenConv c lam R` it carries
      (A) the flux-IBP step equation `hstep_eq : W = crossImplicitMap p c lam u Z W`;
      (B) the UNTRUNCATED source identity `hR : R = crossSource p lam u Z W` and its
          antitonicity `hRanti`;
      (C) the per-step `crossSource` whole-line limits `hRbot`/`hRtop` and the
          endpoint comparison signs;
      (D) the descent-barrier (`Z`-side) at-max `C²`/range/chem packets and the
          shifted-step antitone packet `hanti`.
    These are EXACTLY the per-step analytic facts that the CLOSED concrete solve
    `crossStep_concrete_solution` (RotheStepProducerImpl.lean:87) does NOT give: its
    fixed point is for the TRUNCATED source `crossStepSourceConcrete`
    (`reactionTrunc`/`rpowTrunc` ∘ clampIcc M, with a pointwise `rpowTrunc(W)·Vu'`
    flux), whereas `crossSource` is the untruncated `reactionFun(W)+lam·Z −
    χ·∂ₓ(W^m·V_u')` (a derivative-of-product flux).  The two coincide only after
    (i) truncation removal on the trap `0 ≤ W ≤ M` and (ii) the whole-line flux IBP
    — neither of which the closed solve supplies, and neither of which the
    strengthened `AdmissibleZ Z` carries (it carries `Z`-side endpoint limits and
    at-max `C²`, whose PRODUCED-`W` analogs the closure already DERIVES from the
    Green representation; it does NOT carry the produced source `R = crossSource`).

  HONEST LABEL.  `RotheStepInput`/`construction_neg` is NOT unconditional from the
  bare trap.  What is unconditional and axiom-clean is the REDUCTION
    {trap + per-`Z` `RotheFloorOrbitDataResidual` provider} → `RotheStepInput`
      → (via `admissible_closure`, with `hsrc`) the admissible-orbit step.
  The carried object is precisely the (A)+(B)+(C)+(D) per-step residual; it is the
  P1 analog of the χ₀<0 local-existence frontier (the per-step Cauchy data for the
  produced iterate), NOT a disguised `construction_neg` conclusion.  No existing
  file is edited; no `sorry`/`admit`/`native_decide`/custom axiom.
-/
import ShenWork.Paper1.IntervalP1AdmissibleClosure
import ShenWork.Paper1.RotheFloorOrbitDataImpl
import ShenWork.Paper1.RotheStepProducerImpl

open Filter Topology MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

variable {p : CMParams} {c lam M κ Λ : ℝ} {u : ℝ → ℝ}

/-! ## 1. The per-step residual provider — the named frontier object.

`P1StepResidualProvider` packages, for a fixed trapped profile `u`, the
per-trapped-`Z` `RotheFloorOrbitDataResidual` — the genuinely-uncommitted per-step
analytic floor (A)+(B)+(C)+(D-minus-`hBC2B`) for the PRODUCED iterate
`W = greenConv c lam R`.  This is exactly the object isolated by the landed
`hprodTrap_of_orbitResidual` (RotheFloorOrbitDataImpl); we re-expose it here as the
single carried hypothesis of the P1 assembly.  It is `Type`-valued (the residual
`RotheFloorOrbitDataResidual` carries data, not a mere `Prop`). -/
def P1StepResidualProvider
    (p : CMParams) (c lam M κ Λ : ℝ) (u : ℝ → ℝ) : Type :=
  ∀ Z : ℝ → ℝ, Continuous Z → Antitone Z → (∀ x, 0 ≤ Z x) →
    (∀ x, Z x ≤ upperBarrier κ M x) → (∀ x, frozenWaveOperator p c u Z x ≤ 0) →
    RotheFloorOrbitDataResidual p c lam M κ Λ u Z

/-! ## 2. `RotheStepInput` DERIVED from the residual provider (landed chain). -/

/-- **`rotheStepInput_of_residualProvider` — the per-step input from the residual.**
For a trapped profile `u`, the per-`Z` `RotheFloorOrbitDataResidual` provider yields
`RotheStepInput p c lam M κ Λ u`, via the LANDED chain
`rotheStepFloor_of_orbitResidual` → `rotheStepInput_of_trap`.  Pure consumption of
landed builders; nothing re-proved. -/
def rotheStepInput_of_residualProvider
    (hlam : 0 < lam) (hκ : 0 < κ) (hMpos : 0 < M)
    (htrap : InMonotoneWaveTrapSet κ M u)
    (hbase : ∀ x, frozenWaveOperator p c u (upperBarrier κ M) x ≤ 0)
    (hres : P1StepResidualProvider p c lam M κ Λ u) :
    RotheStepInput p c lam M κ Λ u :=
  rotheStepInput_of_trap
    (rotheStepFloor_of_orbitResidual hlam hκ hMpos htrap hbase hres)

/-! ## 3. The admissible-orbit step, DERIVED via `admissible_closure`.

Feeding the derived `RotheStepInput` to the landed `admissible_closure` discharges
its `hin` floor.  For every admissible `Z` and the produced-source endpoint datum
`hsrc`, this yields the produced iterate `W` with its full `RotheStepOutput` AND the
preserved admissibility `AdmissibleZ u W` — the closure of the admissible orbit
under one Rothe step.  The ONLY carried inputs are the per-`Z` residual provider
`hres` and `hsrc` (the produced source's own endpoint limits, the genuine per-step
Cauchy datum); the admissible-step conclusion is otherwise DERIVED. -/

/-- **`admissibleStep_of_residualProvider` — one admissible Rothe step, derived.**
From the trap + the per-`Z` residual provider (deriving `RotheStepInput`) and the
admissible `Z` + the produced-source endpoint datum `hsrc`, `admissible_closure`
yields the produced `W`, its `RotheStepOutput`, and the preserved `AdmissibleZ u W`.
The `hin` floor of `admissible_closure` is DISCHARGED by the derived input. -/
def admissibleStep_of_residualProvider
    (hlam : 0 < lam) (hκ : 0 < κ) (hMpos : 0 < M)
    (htrap : InMonotoneWaveTrapSet κ M u)
    (hbase : ∀ x, frozenWaveOperator p c u (upperBarrier κ M) x ≤ 0)
    (hres : P1StepResidualProvider p c lam M κ Λ u)
    {Z : ℝ → ℝ} (hZ : AdmissibleZ p c κ M u Z)
    (hsrc : ∀ W : ℝ → ℝ, ∀ out : RotheStepOutput p c lam M κ Λ u Z W,
      ∃ Sb St : ℝ,
        Tendsto out.analytic.R atBot (𝓝 Sb) ∧ Tendsto out.analytic.R atTop (𝓝 St)) :
    Σ' W : ℝ → ℝ, RotheStepOutput p c lam M κ Λ u Z W ×' AdmissibleZ p c κ M u W :=
  admissible_closure
    (rotheStepInput_of_residualProvider hlam hκ hMpos htrap hbase hres) hZ hsrc

/-! ## 4. The producer over the admissible class, DERIVED.

The same derived `RotheStepInput` also yields `RotheStepProducer` via the landed
`rotheStepProducer_of_input` — the `hprodTrap` shape consumed downstream.  This
makes explicit that the SINGLE carried object closing the P1 floor is the per-`Z`
residual provider (and `hsrc` at the admissible-orbit level). -/

/-- **`rotheStepProducer_of_residualProvider` — the trapped producer, derived.**
For a trapped `u`, the residual provider yields `RotheStepProducer p c lam M κ Λ u`
through the derived `RotheStepInput`.  No re-proof; landed consumption only. -/
theorem rotheStepProducer_of_residualProvider
    (hlam : 0 < lam) (hκ : 0 < κ) (hMpos : 0 < M)
    (htrap : InMonotoneWaveTrapSet κ M u)
    (hbase : ∀ x, frozenWaveOperator p c u (upperBarrier κ M) x ≤ 0)
    (hres : P1StepResidualProvider p c lam M κ Λ u) :
    RotheStepProducer p c lam M κ Λ u :=
  rotheStepProducer_of_input
    (rotheStepInput_of_residualProvider hlam hκ hMpos htrap hbase hres)

/-! ## 5. The seed is an admissible orbit base.

The orbit base `Z = Ū = upperBarrier κ M` is admissible (landed
`upperBarrier_admissible`), so `admissibleStep_of_residualProvider` applies at the
base and the admissible orbit is non-vacuously inhabited.  We re-expose the base
admissibility specialized to the trapped profile, confirming the step map of §3 has
a genuine starting point (not the vacuous at-max dodge). -/

/-- **`base_admissible_seed` — the orbit base `Ū` is admissible.**
Specialization of the landed `upperBarrier_admissible`: the super-barrier seed +
its at-max `C²` discharge give `AdmissibleZ p c κ M u (upperBarrier κ M)`, the base
of the admissible orbit on which `admissibleStep_of_residualProvider` runs. -/
theorem base_admissible_seed
    (hκ : 0 < κ) (hM : 0 ≤ M)
    (hbase : ∀ x, frozenWaveOperator p c u (upperBarrier κ M) x ≤ 0)
    (hbc2 : ∀ W : ℝ → ℝ, ∀ x₀ : ℝ,
      IsMaxOn (fun x => W x - upperBarrier κ M x) Set.univ x₀ →
      ContDiffAt ℝ 2 (upperBarrier κ M) x₀) :
    AdmissibleZ p c κ M u (upperBarrier κ M) :=
  upperBarrier_admissible hκ hM hbase hbc2

/-! ## 6. Axiom audit -/

section AxiomAudit
#print axioms rotheStepInput_of_residualProvider
#print axioms admissibleStep_of_residualProvider
#print axioms rotheStepProducer_of_residualProvider
#print axioms base_admissible_seed
end AxiomAudit

end ShenWork.Paper1
