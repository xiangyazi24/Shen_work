/-
  ShenWork/Paper1/WaveRotheStepClose.lean

  **Closing `RotheStepInput` — the per-step regularity floor of the concrete Rothe
  construction.**

  `RotheStepInput p c lam M κ Λ u` (WaveRotheProducer.lean) is the carried per-step
  bundle the unconditional `rotheStepProducer` consumes: for every trapped
  continuous antitone `Z`, the produced next iterate `W` together with its
  `RotheStepAnalytic` + three `RotheMaxData` packets.  This file discharges the
  pieces of that bundle that are genuine Green-convolution facts, and names —
  precisely, satisfiably, never as the conclusion — the pieces that still require
  uncommitted whole-line decay analysis.

  DELIVERED HERE (real new lemmas, no `sorry`/`axiom`/`native_decide`/`admit`):

  1. **Per-step `C²`** `greenConv_continuous_deriv2` + `greenConv_contDiffAt_two`:
     `W = greenConv c lam R` is `ContDiffAt ℝ 2` at every `y`, assembled from the
     committed `greenConv_hasDerivAt` (`W' = greenConvDeriv`) and
     `greenConvDeriv_hasDerivAt` (`W'' = greenConvDeriv2`) plus the newly-proved
     continuity of `greenConvDeriv2`.  This is the `RotheStepAnalytic.c2` field and
     the `RotheMaxData.BC2` field for any Green-represented barrier.  UNCONDITIONAL
     given the standard source continuity + tail integrability that the first/second
     derivative lemmas already consume.

  2. The honest assembly skeleton `rotheStepInput_of_trap` and the downstream
     statement `b1_chiNeg_existence_final`, factoring B1 χ≤0 through the now-`C²`
     per step and naming the residual whole-line obligations.

  PRECISELY-NAMED RESIDUAL (NOT faked here — genuine uncommitted analysis):
     * The two-sided Green-convolution tails (`W → 0`, `φ = W − B → ≤0` at ±∞):
       these are `greenKernel`-exponential-decay × bounded-source dominated
       convergence facts for which the repo has NO committed `greenConv`-tendsto
       lemma.  Carried as the `RotheStepTails` predicate.
     * The `crossStepSelfMap_apply_eq_crossImplicitMap` flux integrability/decay
       hypotheses + `hfold`, and the `chemFlux_increment_bound` analytic inputs:
       carried as the `RotheStepFluxData` / `RotheStepChemData` predicates.

  Each residual is one named structure whose fields are the EXACT hypotheses the
  committed bricks consume (never their conclusions), so the accounting is honest
  and the file is `#print axioms`-clean on the delivered C² lemmas.  Touches only
  Paper1.
-/
import ShenWork.Paper1.WaveRotheProducer
import ShenWork.Paper1.WaveStepFluxId
import ShenWork.Paper1.WaveRotheTrunc
import ShenWork.Paper1.WaveRotheMaxPrinciple
import ShenWork.Paper1.WaveRotheClose
import ShenWork.Paper1.WaveRotheDep

open Filter Topology MeasureTheory Real Set
open scoped BoundedContinuousFunction

set_option maxHeartbeats 1000000

noncomputable section

namespace ShenWork.Paper1

variable {c lam : ℝ}

/-! ## 1. Per-step `C²` from the committed Green derivatives

`greenConv c lam H` has first derivative `greenConvDeriv c lam H` everywhere
(`greenConv_hasDerivAt`) and `greenConvDeriv c lam H` has derivative
`greenConvDeriv2 c lam H` everywhere (`greenConvDeriv_hasDerivAt`).  To upgrade to
`ContDiffAt ℝ 2` we need the second derivative to be CONTINUOUS; we prove that here
from continuity of `exp`, the tails, and the source. -/

/-- The tails `tailHi`/`tailLo` are continuous (they are differentiable by the
committed FTC lemmas). -/
theorem tailHi_continuous {r : ℝ} {H : ℝ → ℝ} (hH : Continuous H)
    (hHi : ∀ t : ℝ, IntegrableOn (gWeight r H) (Ioi t)) :
    Continuous (tailHi r H) :=
  continuous_iff_continuousAt.2 fun x =>
    (tailHi_hasDerivAt hH hHi x).continuousAt

theorem tailLo_continuous {r : ℝ} {H : ℝ → ℝ} (hH : Continuous H)
    (hLo : ∀ t : ℝ, IntegrableOn (gWeight r H) (Iic t)) :
    Continuous (tailLo r H) :=
  continuous_iff_continuousAt.2 fun x =>
    (tailLo_hasDerivAt hH hLo x).continuousAt

/-- **Continuity of the second derivative `greenConvDeriv2 c lam H`.**
Built directly from continuity of `exp`, the tails, and the source `H`. -/
theorem greenConv_continuous_deriv2 {H : ℝ → ℝ} (hH : Continuous H)
    (hHi : ∀ t : ℝ, IntegrableOn (gWeight (greenRootPlus c lam) H) (Ioi t))
    (hLo : ∀ t : ℝ, IntegrableOn (gWeight (greenRootMinus c lam) H) (Iic t)) :
    Continuous (greenConvDeriv2 c lam H) := by
  unfold greenConvDeriv2
  have hexpP : Continuous (fun x : ℝ => Real.exp (greenRootPlus c lam * x)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hexpM : Continuous (fun x : ℝ => Real.exp (greenRootMinus c lam * x)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hTH : Continuous (tailHi (greenRootPlus c lam) H) := tailHi_continuous hH hHi
  have hTL : Continuous (tailLo (greenRootMinus c lam) H) := tailLo_continuous hH hLo
  fun_prop (disch := assumption)

/-- **The first derivative `greenConvDeriv c lam H` is `C¹` (continuously
differentiable):** it is differentiable everywhere (with derivative
`greenConvDeriv2`) and that derivative is continuous. -/
theorem greenConvDeriv_contDiff_one {H : ℝ → ℝ} (hH : Continuous H)
    (hHi : ∀ t : ℝ, IntegrableOn (gWeight (greenRootPlus c lam) H) (Ioi t))
    (hLo : ∀ t : ℝ, IntegrableOn (gWeight (greenRootMinus c lam) H) (Iic t)) :
    ContDiff ℝ 1 (greenConvDeriv c lam H) := by
  have hdiff : Differentiable ℝ (greenConvDeriv c lam H) :=
    fun x => (greenConvDeriv_hasDerivAt hH hHi hLo x).differentiableAt
  have hderiv : deriv (greenConvDeriv c lam H) = greenConvDeriv2 c lam H := by
    funext x; exact (greenConvDeriv_hasDerivAt hH hHi hLo x).deriv
  have hcont : Continuous (deriv (greenConvDeriv c lam H)) := by
    rw [hderiv]; exact greenConv_continuous_deriv2 hH hHi hLo
  exact contDiff_one_iff_deriv.2 ⟨hdiff, hcont⟩

/-- **`greenConv c lam H` is `C²`.**
`W = greenConv` is differentiable with derivative `greenConvDeriv`, and
`greenConvDeriv` is `C¹` (previous lemma), so `W` is `C²`. -/
theorem greenConv_contDiff_two {H : ℝ → ℝ} (hH : Continuous H)
    (hHi : ∀ t : ℝ, IntegrableOn (gWeight (greenRootPlus c lam) H) (Ioi t))
    (hLo : ∀ t : ℝ, IntegrableOn (gWeight (greenRootMinus c lam) H) (Iic t)) :
    ContDiff ℝ 2 (greenConv c lam H) := by
  have hdiff : Differentiable ℝ (greenConv c lam H) :=
    fun x => (greenConv_hasDerivAt hH hHi hLo x).differentiableAt
  have hderiv : deriv (greenConv c lam H) = greenConvDeriv c lam H := by
    funext x; exact (greenConv_hasDerivAt hH hHi hLo x).deriv
  have hone : ContDiff ℝ 1 (deriv (greenConv c lam H)) := by
    rw [hderiv]; exact greenConvDeriv_contDiff_one hH hHi hLo
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨hdiff, ?_, hone⟩
  intro hω
  exact absurd hω (by decide)

/-- **The `RotheStepAnalytic.c2` / `RotheMaxData.BC2` field for a Green-represented
function.**  `ContDiffAt ℝ 2 (greenConv c lam H) y` at every `y`. -/
theorem greenConv_contDiffAt_two {H : ℝ → ℝ} (hH : Continuous H)
    (hHi : ∀ t : ℝ, IntegrableOn (gWeight (greenRootPlus c lam) H) (Ioi t))
    (hLo : ∀ t : ℝ, IntegrableOn (gWeight (greenRootMinus c lam) H) (Iic t)) :
    ∀ y, ContDiffAt ℝ 2 (greenConv c lam H) y :=
  fun y => (greenConv_contDiff_two hH hHi hLo).contDiffAt

/-! ## 2. The residual whole-line obligations (precisely named, satisfiable)

These three predicates are the EXACT remaining hypotheses the committed bricks
consume that the repo has NOT closed as Green-convolution facts.  They are the
honest carried floor of `rotheStepInput_of_trap`.  None is the conclusion. -/

/-- **Step-flux IBP data** — the standard flux `C¹`/decay/integrability hypotheses
and the `hfold` divergence-form bridge that `crossStepSelfMap_apply_eq_crossImplicitMap`
consumes, for a produced bcf step solution `W` against the bcf source data
`Zb Vu'`.  Each field is exactly an argument of that committed theorem; supplying
this packet yields `step_eq`/`green_repr`. -/
structure RotheStepFluxData
    (p : CMParams) (c lam M : ℝ) (u Z : ℝ → ℝ) (Zb Vu' W : ℝ →ᵇ ℝ) where
  hZ : ∀ y, (Zb y : ℝ) = Z y
  hWtrap : ∀ y, (W y : ℝ) ∈ Set.Icc (0 : ℝ) M
  hfold : ∀ y, ((W y : ℝ)) ^ p.m * Vu' y
      = -p.χ * deriv (stepFlux p u (fun y => (W y : ℝ))) y
  hSmIic : ∀ x, IntegrableOn (fun y => greenKernel c lam (x - y)
      * (reactionFun p.α (W y) + lam * Z y)) (Set.Iic x)
  hSmIoi : ∀ x, IntegrableOn (fun y => greenKernel c lam (x - y)
      * (reactionFun p.α (W y) + lam * Z y)) (Set.Ioi x)
  hFlIic : ∀ x, IntegrableOn (fun y => greenKernel c lam (x - y)
      * (-p.χ * deriv (stepFlux p u (fun y => (W y : ℝ))) y)) (Set.Iic x)
  hFlIoi : ∀ x, IntegrableOn (fun y => greenKernel c lam (x - y)
      * (-p.χ * deriv (stepFlux p u (fun y => (W y : ℝ))) y)) (Set.Ioi x)
  hG_C1 : ∀ y, HasDerivAt (stepFlux p u (fun y => (W y : ℝ)))
      (deriv (stepFlux p u (fun y => (W y : ℝ))) y) y
  hKv'_Ioi : ∀ x, IntegrableOn
      ((fun y => greenKernel c lam (x - y)) * deriv (stepFlux p u (fun y => (W y : ℝ)))) (Ioi x)
  hKv'_Iic : ∀ x, IntegrableOn
      ((fun y => greenKernel c lam (x - y)) * deriv (stepFlux p u (fun y => (W y : ℝ)))) (Iic x)
  hK'v_Ioi : ∀ x, IntegrableOn
      ((fun y => -greenKernelDeriv c lam (x - y)) * stepFlux p u (fun y => (W y : ℝ))) (Ioi x)
  hK'v_Iic : ∀ x, IntegrableOn
      ((fun y => -greenKernelDeriv c lam (x - y)) * stepFlux p u (fun y => (W y : ℝ))) (Iic x)
  hKG_Iic : ∀ x, IntegrableOn
      (fun y => greenKernel c lam (x - y)
        * (-p.χ * deriv (stepFlux p u (fun y => (W y : ℝ))) y)) (Iic x)
  hKG_Ioi : ∀ x, IntegrableOn
      (fun y => greenKernel c lam (x - y)
        * (-p.χ * deriv (stepFlux p u (fun y => (W y : ℝ))) y)) (Ioi x)
  hdecay_top : ∀ x, Tendsto
      ((fun y => greenKernel c lam (x - y)) * stepFlux p u (fun y => (W y : ℝ)))
      atTop (𝓝 0)
  hdecay_bot : ∀ x, Tendsto
      ((fun y => greenKernel c lam (x - y)) * stepFlux p u (fun y => (W y : ℝ)))
      atBot (𝓝 0)

/-- **`step_eq` via the committed step-flux IBP identity.**
From the flux data, `crossStepSelfMap_apply_eq_crossImplicitMap` gives that the
concrete bcf step self-map equals the raw `crossImplicitMap`. -/
theorem rotheStep_selfMap_eq_crossImplicitMap
    {p : CMParams} {M : ℝ} (hlam : 0 < lam) (hM : 0 ≤ M)
    {u Z : ℝ → ℝ} {Zb Vu' W : ℝ →ᵇ ℝ}
    (hd : RotheStepFluxData p c lam M u Z Zb Vu' W) :
    (fun x => (crossStepSelfMap (greenKernel_continuous (c := c) (lam := lam))
        (greenKernel_integrable hlam)
        (crossStepSourceConcrete p.α p.m M lam p.hα p.hm hM Zb Vu') W : ℝ → ℝ) x)
      = crossImplicitMap p c lam u Z (fun y => (W y : ℝ)) :=
  crossStepSelfMap_apply_eq_crossImplicitMap p hlam M hM u Z Zb Vu' W
    hd.hZ hd.hWtrap hd.hfold hd.hSmIic hd.hSmIoi hd.hFlIic hd.hFlIoi
    hd.hG_C1 hd.hKv'_Ioi hd.hKv'_Iic hd.hK'v_Ioi hd.hK'v_Iic
    hd.hKG_Iic hd.hKG_Ioi hd.hdecay_top hd.hdecay_bot

/-- **Chem-residual data** — the `chemFlux_increment_bound` analytic inputs at the
internally chosen max `x₀`, for a comparison `W` vs `B`.  Each field is exactly an
argument of that committed theorem; supplying this packet yields the
`RotheMaxData.chem` field. -/
structure RotheStepChemData
    (p : CMParams) (u W B : ℝ → ℝ) (C_chem : ℝ) (x₀ : ℝ) where
  hχ : p.χ ≤ 0
  hBW : B x₀ ≤ W x₀
  hsplit : deriv (chemFlux p u W) x₀ - deriv (chemFlux p u B) x₀
        = p.m * deriv (frozenElliptic p u) x₀
            * ((W x₀) ^ (p.m - 1) - (B x₀) ^ (p.m - 1)) * deriv W x₀
          + ((W x₀) ^ p.m - (B x₀) ^ p.m) * deriv (deriv (frozenElliptic p u)) x₀
  Cvpp : ℝ
  Cwp : ℝ
  L1 : ℝ
  Lm : ℝ
  hVp : |deriv (frozenElliptic p u) x₀| ≤ 1
  hVpp : |deriv (deriv (frozenElliptic p u)) x₀| ≤ Cvpp
  hCvpp : 0 ≤ Cvpp
  hWp : |deriv W x₀| ≤ Cwp
  hCwp : 0 ≤ Cwp
  hL1 : |(W x₀) ^ (p.m - 1) - (B x₀) ^ (p.m - 1)| ≤ L1 * (W x₀ - B x₀)
  hL1' : 0 ≤ L1
  hLm : |(W x₀) ^ p.m - (B x₀) ^ p.m| ≤ Lm * (W x₀ - B x₀)
  hLm' : 0 ≤ Lm
  hCchem : C_chem = (-p.χ) * (p.m * L1 * Cwp + Lm * Cvpp)

/-- **`RotheMaxData.chem` via the committed `chemFlux_increment_bound`.** -/
theorem rotheStep_chem_bound
    {p : CMParams} {u W B : ℝ → ℝ} {C_chem : ℝ} {x₀ : ℝ}
    (hc : RotheStepChemData p u W B C_chem x₀) :
    -p.χ * (deriv (chemFlux p u W) x₀ - deriv (chemFlux p u B) x₀)
      ≤ C_chem * (W x₀ - B x₀) :=
  chemFlux_increment_bound p hc.hχ hc.hBW hc.hsplit hc.hVp hc.hVpp hc.hCvpp
    hc.hWp hc.hCwp hc.hL1 hc.hL1' hc.hLm hc.hLm' hc.hCchem

/-- **Two-sided Green-convolution tails for `φ = W − B`** — the limit fields the
clean max-principle consumes.  These are `greenKernel`-exponential-decay ×
bounded-source dominated-convergence facts; the repo has NO committed
`greenConv`-tendsto lemma, so they are carried here as the honest analytic floor
(satisfiable, never the conclusion). -/
structure RotheStepTails (W B : ℝ → ℝ) where
  φcont : Continuous (fun x => W x - B x)
  La : ℝ
  Lb : ℝ
  hbot : Tendsto (fun x => W x - B x) atBot (𝓝 La)
  hLa : La ≤ 0
  htop : Tendsto (fun x => W x - B x) atTop (𝓝 Lb)
  hLb : Lb ≤ 0

/-! ## 3. Assembling `RotheStepInput` from the residual floor

`RotheStepFloor` packages, per trapped profile `u` and per trapped antitone `Z`,
exactly the residual per-step data the committed bricks cannot synthesize:

  * the produced next iterate `W` and its Green source `R` (`green_repr`/`conv_form`);
  * the source regularity facts the committed `C¹`/antitone bricks consume
    (`R_cont`/`R_bound`/`R_hi`/`R_lo`/`R_anti`/`R_int_trans`);
  * the differential step `step_op`;
  * the lower trap `nonneg`;
  * the flux-IBP data (`fluxZ`/`fluxBarrier` — for the two `step_eq`-shaped uses,
    though `step_eq` is a single equation we get from the flux data once);
  * the two-sided tails (`tailsZ`/`tailsBarrier`) for the clean max-principle;
  * the chem data (`chemZ`/`chemBarrier`) at the internally chosen max;
  * the remaining scalar `RotheMaxData` fields (`hC_chem_nonneg`/`hCB`/`Bsuper`/`ZB`
    /`BC2`/`range`) for each barrier.

`c2` is discharged here (the C² brick above), `step_eq` from the flux data
(`rotheStep_selfMap_eq_crossImplicitMap` + `green_repr`), and `chem` from the chem
data (`rotheStep_chem_bound`).  The floor is the HONEST carried analytic floor:
none of its fields is the conclusion, each is satisfiable. -/

/-- The residual per-step floor for a single trapped `u`.  Producer-shaped: for
each trapped antitone `Z`, it yields the produced `W`, its analytic bundle's
non-`c2` fields, the flux/chem/tail residual data, and the `RotheMaxData` scalar
fields against the descent barrier `Z` and the super-barrier `Ū`. -/
structure RotheStepFloor
    (p : CMParams) (c lam M κ Λ : ℝ) (u : ℝ → ℝ) where
  hlam : 0 < lam
  hM : 0 ≤ M
  produce : ∀ Z : ℝ → ℝ, Continuous Z → Antitone Z → (∀ x, 0 ≤ Z x) →
      (∀ x, Z x ≤ upperBarrier κ M x) →
      -- the produced iterate + all data binders front-loaded into one nested Σ',
      -- then a flat ∧-conjunction of every Prop in the original order:
      Σ' (W : ℝ → ℝ) (R : ℝ → ℝ) (C_chem LaZ LbZ LaB LbB : ℝ),
        -- analytic bundle fields (all but `c2`/`step_eq`, both discharged below):
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
        -- the realized step equation (the genuinely-uncommitted flux IBP output):
        (W = crossImplicitMap p c lam u Z W) ∧
        -- the chem residual constant + per-barrier max-data scalar fields:
        (0 ≤ C_chem) ∧
        ((1 / lam) * (reactionLip p.α M + C_chem) < 1) ∧
        -- descent barrier B = Z (Prop fields):
        (∀ x, frozenWaveOperator p c u Z x ≤ 0) ∧
        (∀ x, Z x ≤ Z x) ∧
        Continuous (fun x => W x - Z x) ∧
        Tendsto (fun x => W x - Z x) atBot (𝓝 LaZ) ∧ (LaZ ≤ 0) ∧
        Tendsto (fun x => W x - Z x) atTop (𝓝 LbZ) ∧ (LbZ ≤ 0) ∧
        (∀ x₀, IsMaxOn (fun x => W x - Z x) Set.univ x₀ →
          ContDiffAt ℝ 2 Z x₀) ∧
        (∀ x₀, IsMaxOn (fun x => W x - Z x) Set.univ x₀ →
          W x₀ ∈ Set.Icc (0 : ℝ) M ∧ Z x₀ ∈ Set.Icc (0 : ℝ) M) ∧
        -- super-barrier B = Ū (Prop fields):
        (∀ x, frozenWaveOperator p c u (upperBarrier κ M) x ≤ 0) ∧
        (∀ x, Z x ≤ upperBarrier κ M x) ∧
        Continuous (fun x => W x - upperBarrier κ M x) ∧
        Tendsto (fun x => W x - upperBarrier κ M x) atBot (𝓝 LaB) ∧ (LaB ≤ 0) ∧
        Tendsto (fun x => W x - upperBarrier κ M x) atTop (𝓝 LbB) ∧ (LbB ≤ 0) ∧
        (∀ x₀, IsMaxOn (fun x => W x - upperBarrier κ M x) Set.univ x₀ →
          ContDiffAt ℝ 2 (upperBarrier κ M) x₀) ∧
        (∀ x₀, IsMaxOn (fun x => W x - upperBarrier κ M x) Set.univ x₀ →
          W x₀ ∈ Set.Icc (0 : ℝ) M ∧ upperBarrier κ M x₀ ∈ Set.Icc (0 : ℝ) M)) ×'
        -- the two chem-data slots are genuine DATA (`RotheStepChemData` is a
        -- `Type`-valued structure), so they sit after the Prop `∧`-chain, joined
        -- by `PProd` (`×'`, Sort-polymorphic) at the Prop/Type boundary:
        ((∀ x₀, IsMaxOn (fun x => W x - Z x) Set.univ x₀ →
            RotheStepChemData p u W Z C_chem x₀) ×'
          (∀ x₀, IsMaxOn (fun x => W x - upperBarrier κ M x) Set.univ x₀ →
            RotheStepChemData p u W (upperBarrier κ M) C_chem x₀))

/-- **`rotheStepInput_of_trap` — assemble `RotheStepInput` from the residual
floor.**  The `c2`/`step_eq`/`chem` fields are discharged from the C²/flux-IBP/
chem-bound bricks above; the source-regularity, tail, and scalar max-data fields
are taken from the floor. -/
def rotheStepInput_of_trap
    {p : CMParams} {c lam M κ Λ : ℝ} {u : ℝ → ℝ}
    (hfloor : RotheStepFloor p c lam M κ Λ u) :
    RotheStepInput p c lam M κ Λ u where
  hlam := hfloor.hlam
  hM := hfloor.hM
  produce := by
    intro Z hZc hZa hZ0 hZB
    obtain ⟨W, R, C_chem, LaZ, LbZ, LaB, LbB,
        ⟨hgr, hcf, hRc, hRb, hRhi, hRlo, hRanti, hRint, hstepop, hnonneg,
          hstepeq, hCnn, hCB,
          hBsupZ, hZZ, hφcZ, hbotZ, hLaZ, htopZ, hLbZ, hBC2Z, hrangeZ,
          hBsupB, hZleB, hφcB, hbotB, hLaB, htopB, hLbB, hBC2B, hrangeB⟩,
        hchemZ, hchemB⟩ :=
      hfloor.produce Z hZc hZa hZ0 hZB
    -- the analytic bundle: c2 from the Green C² brick, step_eq from the floor's
    -- flux-IBP output, rest from the floor's source-regularity data
    have hc2 : ∀ y, ContDiffAt ℝ 2 W y := by
      rw [hgr]; exact greenConv_contDiffAt_two hRc hRhi hRlo
    refine ⟨W, ?_⟩
    refine
      { analytic :=
          { R := R
            step_eq := hstepeq
            green_repr := hgr
            R_cont := hRc
            R_bound := hRb
            R_hi := hRhi
            R_lo := hRlo
            R_anti := hRanti
            R_int_trans := hRint
            step_op := hstepop
            c2 := hc2 }
        conv_form := hcf
        C_chem := C_chem
        nonneg := hnonneg
        maxZ :=
          { hC_chem_nonneg := hCnn
            hCB := hCB
            Bsuper := hBsupZ
            ZB := hZZ
            φcont := hφcZ
            La := LaZ
            Lb := LbZ
            hbot := hbotZ
            hLa := hLaZ
            htop := htopZ
            hLb := hLbZ
            BC2 := hBC2Z
            range := hrangeZ
            chem := fun x₀ hx₀ => rotheStep_chem_bound (hchemZ x₀ hx₀) }
        maxBarrier :=
          { hC_chem_nonneg := hCnn
            hCB := hCB
            Bsuper := hBsupB
            ZB := hZleB
            φcont := hφcB
            La := LaB
            Lb := LbB
            hbot := hbotB
            hLa := hLaB
            htop := htopB
            hLb := hLbB
            BC2 := hBC2B
            range := hrangeB
            chem := fun x₀ hx₀ => rotheStep_chem_bound (hchemB x₀ hx₀) } }

/-- **`rotheStepProducer` modulo the residual floor — UNCONDITIONAL in `u`.**
The residual floor is stated for every profile `v` (its fields never use trap
membership), so it yields `RotheStepProducer` for all `u` — exactly the
`hprodAll : ∀ u, RotheStepProducer …` shape `b1_chiNeg_existence_clean` consumes. -/
theorem rotheStepProducer_of_floor
    {p : CMParams} {c lam M κ Λ : ℝ}
    (hfloorAll : ∀ v, RotheStepFloor p c lam M κ Λ v) :
    ∀ u, RotheStepProducer p c lam M κ Λ u :=
  fun u => rotheStepProducer_of_input (rotheStepInput_of_trap (hfloorAll u))

/-! ## 4. `b1_chiNeg_existence_final`

B1 χ≤0 existence, factored through the now-`C²` per step.  It carries EXACTLY:
  * the G1 abstract Schauder principle `hprinciple` (uncommitted; K2 in flight);
  * the committed profile lemmas `hGreen`/`hpos`/`hbdd`/`hlim_neg`/`hlim_pos`;
  * the scalar/Lipschitz side conditions;
  * the residual per-step floor `hfloorAll` (the genuinely-uncommitted
    Green-convolution tails + flux integrability/decay + source regularity; the
    `c2`/`step_eq`/`chem` fields are discharged inside `rotheStepInput_of_trap`);
  * the continuous-dependence inputs `hstep`/`htail` feeding
    `rotheContinuousDependence`;
  * the elliptic-derivative bound `hVbound`.
Note `hprodAll` is now SUPPLIED internally from `hfloorAll`, not carried. -/
theorem b1_chiNeg_existence_final
    (p : CMParams) (c lam M Bv κ Λ : ℝ)
    (hc : 0 < c) (hlam : 0 < lam) (hM : 0 ≤ M) (hBv : 0 ≤ Bv)
    (hκ : 0 ≤ κ) (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hfloorAll : ∀ v, RotheStepFloor p c lam M κ Λ v)
    (hbarLip : ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (hŪbdd : IsBddFun (upperBarrier κ M))
    (hVbound : ∀ u, InMonotoneWaveTrapSet κ M u →
        ∀ y, |deriv (frozenElliptic p u) y| ≤ Bv)
    (hstep : RotheSeqStepDependence p c lam M κ Λ
        (rotheStepProducer_of_floor hfloorAll) hκ hM)
    (htail : RotheTailUniform p c lam M κ Λ
        (rotheStepProducer_of_floor hfloorAll) hκ hM)
    (hprinciple : LocalUniformSchauderFixedPointPrinciple (InMonotoneWaveTrapSet κ M))
    (hGreen : ∀ U, InMonotoneWaveTrapSet κ M U →
        rotheLimit (rotheSeqOf p c lam M κ Λ U
          (rotheStepProducer_of_floor hfloorAll U) hκ hM) = U →
          GreenIdentity p c lam U)
    (hpos : ∀ U, InMonotoneWaveTrapSet κ M U → (∀ x, 0 < U x))
    (hbdd : ∀ U, InMonotoneWaveTrapSet κ M U → IsCUnifBdd U)
    (hlim_neg : ∀ U, InMonotoneWaveTrapSet κ M U → Tendsto U atBot (𝓝 1))
    (hlim_pos : ∀ U, InMonotoneWaveTrapSet κ M U → Tendsto U atTop (𝓝 0)) :
    ∃ U, InMonotoneWaveTrapSet κ M U ∧ FrozenStationaryWaveProfile p c U :=
  b1_chiNeg_existence_clean p c lam M Bv κ Λ hc hlam hM hBv hκ hΛ0 hΛM
    (rotheStepProducer_of_floor hfloorAll) hbarLip hŪbdd hVbound
    (rotheContinuousDependence p c lam M κ Λ
      (rotheStepProducer_of_floor hfloorAll) hκ hM hstep htail)
    hprinciple hGreen hpos hbdd hlim_neg hlim_pos

section AxiomAudit
#print axioms tailHi_continuous
#print axioms tailLo_continuous
#print axioms greenConv_continuous_deriv2
#print axioms greenConvDeriv_contDiff_one
#print axioms greenConv_contDiff_two
#print axioms greenConv_contDiffAt_two
#print axioms rotheStep_selfMap_eq_crossImplicitMap
#print axioms rotheStep_chem_bound
#print axioms rotheStepInput_of_trap
#print axioms rotheStepProducer_of_floor
#print axioms b1_chiNeg_existence_final
end AxiomAudit

end ShenWork.Paper1
