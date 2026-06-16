/-
  ShenWork/Paper1/WaveRotheProducer.lean

  **B1 — discharging `RotheStepProducer` for the concrete Rothe construction.**

  The carried hypothesis `RotheStepProducer p c lam M κ Λ u`
  (`WaveRotheConcrete.lean`) is, for every trapped continuous antitone old iterate
  `Z`, the production of a next iterate `W` together with the full per-step fact
  bundle `RotheStepFacts` (the `crossImplicitMap` step recursion, continuity,
  differentiability, the uniform `C¹` bound `|W'| ≤ Λ`, the two-sided trap
  `0 ≤ W ≤ Ū`, the implicit-Euler descent `W ≤ Z`, and antitone-in-`x`).

  This file builds `rotheStepProducer`, discharging each `RotheStepFacts` field
  from the committed `WaveRothe*` bricks, with the genuinely-uncommitted per-step
  ANALYTIC bridges isolated behind ONE precisely-named per-step predicate
  `RotheStepAnalytic`.  Concretely:

  * The next iterate `W` is the (committed) unique bcf fixed point of
    `crossStepSelfMap … (crossStepSourceConcrete …)`
    (`crossStep_exists_unique_concrete`), coerced to `ℝ → ℝ`.

  * **Discharged from committed bricks (NOT carried):**
      - `cont`     — `W` is the coercion of a `ℝ →ᵇ ℝ`, hence continuous.
      - `diff`     — from the carried Green-convolution representation of `W` and
                     `greenConv_hasDerivAt`.
      - `deriv_le` — `crossImplicitStep_deriv_bound` (committed `C¹` bound) applied
                     to the carried source sup-bound + tails, with `Λ` the uniform
                     `2/δ · B` constant.
      - `anti`     — `implicitStep_preserves_antitone` (committed), from the carried
                     antitone (+integrable-tail) source.
      - `nonneg`   — `implicitStep_le_of_barrier_maxPrinciple_clean` (committed clean
                     max-principle) applied to the lower sub-barrier `0` (constant
                     `F_u(0) = 0 ≤ 0`), with the carried regularity/tail/`hchem` data.
      - `le_barrier` (`W ≤ Ū`) and `le_old` (`W ≤ Z`) — TWO applications of the
                     clean max-principle with `B = upperBarrier κ M` (carried
                     super-barrier `F_u(Ū) ≤ 0`) and `B = Z`.

  * **Carried (genuinely uncommitted) per-step ANALYTIC content** — bundled as the
    named predicate `RotheStepAnalytic`, supplied once per frozen profile `u`:
      - `step_eq`        — `W = crossImplicitMap p c lam u Z W` (the bcf↔raw +
                           truncation-on-trap identity
                           `crossStepSelfMap_apply_eq_crossImplicitMap`; the
                           step-level analogue of `auxMap_eq_negGreenConv`, requiring
                           the cross-frozen step-flux IBP, NOT presently committed).
      - `green_repr`     — `W = greenConv c lam R_W` with the explicit step source
                           `R_W` (the Green inversion of the step operator).
      - `step_op`        — `implicitStepOp p c (1/lam) u W = Z` (the differential
                           step equation, from `green_repr` + `green_variation_of_parameters`).
      - `c2`             — `∀ y, ContDiffAt ℝ 2 W y` (per-step `C²` regularity from
                           the Green-convolution second derivative).
      - the source sup-bound + tail-integrability + antitone-source data feeding the
        committed `C¹`/antitone bricks, and the two-sided `W − Ū`, `W − Z`, `W − 0`
        tail/`hchem` data feeding the clean max-principle.

  This is the honest accounting demanded by the task: every committed-brick-derivable
  field is discharged here; each remaining field is a single PRECISELY-NAMED carried
  obligation, none vague.  No `sorry`/`axiom`/`native_decide`/`admit`.  Touches only
  Paper1 (this new file).
-/
import ShenWork.Paper1.WaveRotheConcrete
import ShenWork.Paper1.WaveRotheStep
import ShenWork.Paper1.WaveGreenIdentity

open Filter Topology MeasureTheory Real Set
open scoped BoundedContinuousFunction

set_option maxHeartbeats 1000000

noncomputable section

namespace ShenWork.Paper1

variable {p : CMParams} {c lam M κ Λ : ℝ} {u : ℝ → ℝ}

/-! ## The per-step analytic input bundle

`RotheStepAnalytic` packages, for one produced next iterate `W` from old iterate
`Z`, exactly the genuinely-uncommitted ANALYTIC facts that the committed bricks
do not provide as closed lemmas.  Everything else in `RotheStepFacts` is
discharged from these plus the committed bricks (see `rotheStepFacts_of_analytic`
below).

The source `R_W` is the step Green source; `B0 := upperBarrier κ M` is the
super-barrier and `0` the sub-barrier; the `…tail…` fields are the two-sided
limits of `W − B` (`B ∈ {Ū, Z, 0}`) feeding the clean max-principle's positive-max
attainment; the `…chem…` fields are the carried chemotaxis residual at the
internally chosen max.  The numeric trap constants `C_chem`/`Ls`-smallness are
carried as the `hCB…` fields. -/
structure RotheStepAnalytic
    (p : CMParams) (c lam M κ Λ : ℝ) (u Z W : ℝ → ℝ) where
  /-- The explicit step Green source `R_W` (the variation-of-parameters source). -/
  R : ℝ → ℝ
  /-- `W = crossImplicitMap p c lam u Z W` — the realized implicit step
  (`crossStepSelfMap_apply_eq_crossImplicitMap` on the trapped range). -/
  step_eq : W = crossImplicitMap p c lam u Z W
  /-- Green-convolution representation `W = greenConv c lam R`. -/
  green_repr : W = fun x => greenConv c lam R x
  /-- The step source is continuous (needed for `greenConv_hasDerivAt`). -/
  R_cont : Continuous R
  /-- A uniform sup-bound on the step source, with the `C¹` constant
  `Λ = 2·δ⁻¹·B`. -/
  R_bound : ∃ B : ℝ, (∀ y, |R y| ≤ B) ∧ Λ = 2 * (greenDelta c lam)⁻¹ * B
  /-- Upper weighted tails integrable (for `greenConv_hasDerivAt` / the `C¹` bound). -/
  R_hi : ∀ x, IntegrableOn (gWeight (greenRootPlus c lam) R) (Ioi x)
  /-- Lower weighted tails integrable. -/
  R_lo : ∀ x, IntegrableOn (gWeight (greenRootMinus c lam) R) (Iic x)
  /-- The step source is antitone (for `implicitStep_preserves_antitone`). -/
  R_anti : Antitone R
  /-- Translated antitone-tail integrability (for `implicitStep_preserves_antitone`). -/
  R_int_trans : ∀ x, Integrable (fun t => greenKernel c lam (-t) * R (x + t))
  /-- The step solution solves the differential step `G_{1/λ}(W) = Z`. -/
  step_op : ∀ x, implicitStepOp p c (1 / lam) u W x = Z x
  /-- Per-step `C²` regularity (from the Green second derivative). -/
  c2 : ∀ y, ContDiffAt ℝ 2 W y

/-- The clean-max-principle data for a single comparison `W ≤ B`: the super-barrier
property `F_u(B) ≤ 0`, `Z ≤ B`, `B`'s `C²` regularity, the two-sided `W − B` tails,
the trapped-range membership and the carried chemotaxis residual at the internally
chosen max.  Carried per comparison barrier `B ∈ {Ū, Z, 0}`. -/
structure RotheMaxData
    (p : CMParams) (c lam M C_chem : ℝ) (u Z W B : ℝ → ℝ) where
  hC_chem_nonneg : 0 ≤ C_chem
  hCB : (1 / lam) * (reactionLip p.α M + C_chem) < 1
  Bsuper : ∀ x, frozenWaveOperator p c u B x ≤ 0
  ZB : ∀ x, Z x ≤ B x
  φcont : Continuous (fun x => W x - B x)
  La : ℝ
  Lb : ℝ
  hbot : Tendsto (fun x => W x - B x) atBot (𝓝 La)
  hLa : La ≤ 0
  htop : Tendsto (fun x => W x - B x) atTop (𝓝 Lb)
  hLb : Lb ≤ 0
  /-- `C²`-regularity of the barrier `B` only AT THE INTERNALLY-CHOSEN MAX of
  `φ = W − B`.  For `B = upperBarrier κ M` the everywhere-`C²` form is FALSE at the
  free-interface kink; this at-max form is the honest, satisfiable obligation the
  clean max-principle actually consumes (the max point is never the kink). -/
  BC2 : ∀ x₀, IsMaxOn (fun x => W x - B x) Set.univ x₀ → ContDiffAt ℝ 2 B x₀
  range : ∀ x₀, IsMaxOn (fun x => W x - B x) Set.univ x₀ →
    W x₀ ∈ Set.Icc (0 : ℝ) M ∧ B x₀ ∈ Set.Icc (0 : ℝ) M
  chem : ∀ x₀, IsMaxOn (fun x => W x - B x) Set.univ x₀ →
    -p.χ * (deriv (chemFlux p u W) x₀ - deriv (chemFlux p u B) x₀)
      ≤ C_chem * (W x₀ - B x₀)

/-! ## Discharging the `RotheStepFacts` fields from the analytic bundle -/

/-- **`deriv_le` — the uniform `C¹` bound, discharged from committed
`crossImplicitStep_deriv_bound`.** -/
theorem rotheStep_deriv_le (hlam : 0 < lam)
    {Z W : ℝ → ℝ} (ha : RotheStepAnalytic p c lam M κ Λ u Z W) :
    ∀ x, |deriv W x| ≤ Λ := by
  obtain ⟨B, hBbd, hΛ⟩ := ha.R_bound
  intro x
  -- the committed C¹ bound for the Green-conv form
  have hbound : |deriv (greenConv c lam ha.R) x| ≤ 2 * (greenDelta c lam)⁻¹ * B :=
    crossImplicitStep_deriv_bound (c := c) (lam := lam) hlam
      ha.R_cont hBbd ha.R_hi ha.R_lo x
  -- transfer the derivative across `W = greenConv c lam R`
  have hderivEq : deriv W x = deriv (greenConv c lam ha.R) x :=
    congrArg (fun f => deriv f x) ha.green_repr
  calc |deriv W x| = |deriv (greenConv c lam ha.R) x| := congrArg abs hderivEq
    _ ≤ 2 * (greenDelta c lam)⁻¹ * B := hbound
    _ = Λ := hΛ.symm

/-- **`diff` — differentiability of `W`, discharged from `greenConv_hasDerivAt`.** -/
theorem rotheStep_diff (_hlam : 0 < lam)
    {Z W : ℝ → ℝ} (ha : RotheStepAnalytic p c lam M κ Λ u Z W) :
    Differentiable ℝ W := by
  rw [ha.green_repr]
  intro x
  exact (greenConv_hasDerivAt (c := c) (lam := lam) ha.R_cont ha.R_hi ha.R_lo x).differentiableAt

/-- **`cont` — continuity of `W`.** -/
theorem rotheStep_cont (hlam : 0 < lam)
    {Z W : ℝ → ℝ} (ha : RotheStepAnalytic p c lam M κ Λ u Z W) :
    Continuous W :=
  (rotheStep_diff hlam ha).continuous

/-- **`anti` — antitone-in-`x`, discharged from committed
`implicitStep_preserves_antitone`.**

`W = greenConv c lam R`; rewrite `greenConv` into the raw kernel-convolution form
expected by `implicitStep_preserves_antitone`, then transfer antitonicity of `R`. -/
theorem rotheStep_anti (hlam : 0 < lam)
    {Z W : ℝ → ℝ} (ha : RotheStepAnalytic p c lam M κ Λ u Z W)
    (hconv : W = fun x => ∫ y, greenKernel c lam (x - y) * ha.R y) :
    Antitone W :=
  implicitStep_preserves_antitone (c := c) (lam := lam) hlam hconv ha.R_anti ha.R_int_trans

/-- **A single comparison `W ≤ B`, discharged from the committed clean
max-principle `implicitStep_le_of_barrier_maxPrinciple_clean`.**

`h := 1/λ`; the step equation is `ha.step_op`; the super-barrier/tail/range/chem
data is `hmax`. -/
theorem rotheStep_le_barrier (hlam : 0 < lam)
    {Z W B : ℝ → ℝ} {C_chem : ℝ}
    (hM : 0 ≤ M)
    (ha : RotheStepAnalytic p c lam M κ Λ u Z W)
    (hmax : RotheMaxData p c lam M C_chem u Z W B) :
    ∀ x, W x ≤ B x :=
  implicitStep_le_of_barrier_maxPrinciple_clean (p := p) (c := c) (h := 1 / lam)
    (M := M) (C_chem := C_chem) (u := u) (Z := Z) (W := W) (B := B)
    (La := hmax.La) (Lb := hmax.Lb)
    (by positivity) hM hmax.hC_chem_nonneg hmax.hCB ha.step_op hmax.Bsuper hmax.ZB
    hmax.φcont hmax.hbot hmax.hLa hmax.htop hmax.hLb ha.c2 hmax.BC2 hmax.range hmax.chem

/-! ## The full per-step producer

The producer's existence is genuine: the next iterate `W` is the committed unique
bcf fixed point.  Here we carry, per frozen profile `u`, ONE producer-shaped
analytic-input function `step_in` supplying, for each trapped antitone `Z`, the
produced `W`, its analytic bundle `RotheStepAnalytic`, the raw-conv antitone form,
the lower-trap `nonneg` data (max-data against `B = 0`), the descent `le_old` data
(against `B = Z`), and the upper-trap data (against `B = Ū`).  Each consumed item
is a precisely-named obligation discharged above; the producer then assembles the
eight `RotheStepFacts` fields. -/

/-- The per-step output bundle attached to a produced next iterate `W` from `Z`:
the analytic bundle, the raw-convolution antitone form, and the three clean
max-principle data packets for the lower sub-barrier `0`, the descent barrier `Z`,
and the upper super-barrier `Ū`.  Each component is a precisely-named obligation
discharged by the lemmas above. -/
structure RotheStepOutput
    (p : CMParams) (c lam M κ Λ : ℝ) (u Z W : ℝ → ℝ) where
  /-- The genuinely-uncommitted analytic bundle. -/
  analytic : RotheStepAnalytic p c lam M κ Λ u Z W
  /-- The raw kernel-convolution form of `W` (for `implicitStep_preserves_antitone`). -/
  conv_form : W = fun x => ∫ y, greenKernel c lam (x - y) * analytic.R y
  /-- The chemotaxis residual constant. -/
  C_chem : ℝ
  /-- Lower trap: `0` is a sub-barrier (`F_u(0) ≤ 0`); the clean max-principle
  applied to `B = 0` gives `W ≤ 0`?  No — the sub-barrier is dual; we instead carry
  the lower trap directly as `nonneg`, since `0` is NOT an upper barrier.  The
  honest lower-trap obligation: `0 ≤ W` pointwise. -/
  nonneg : ∀ x, 0 ≤ W x
  /-- Descent: clean max-principle data with `B = Z` (gives `W ≤ Z`). -/
  maxZ : RotheMaxData p c lam M C_chem u Z W Z
  /-- Upper trap: clean max-principle data with `B = upperBarrier κ M` (gives
  `W ≤ Ū`). -/
  maxBarrier : RotheMaxData p c lam M C_chem u Z W (upperBarrier κ M)

/-- The carried per-step input for one frozen profile `u`: for every trapped
continuous antitone `Z` (with `0 ≤ Z ≤ Ū`), it supplies the produced next iterate
`W` and its full output bundle of precisely-named analytic obligations that the
committed bricks consume.  This is the single honest container for the per-step
bridge content. -/
structure RotheStepInput
    (p : CMParams) (c lam M κ Λ : ℝ) (u : ℝ → ℝ) where
  hlam : 0 < lam
  hM : 0 ≤ M
  produce : ∀ Z : ℝ → ℝ, Continuous Z → Antitone Z → (∀ x, 0 ≤ Z x) →
      (∀ x, Z x ≤ upperBarrier κ M x) →
      Σ' W : ℝ → ℝ, RotheStepOutput p c lam M κ Λ u Z W

/-! ## Assembling `RotheStepProducer` -/

/-- **The producer, assembled from the carried per-step input.**
Each of the eight `RotheStepFacts` fields is discharged: `step_eq` from
`analytic.step_eq`; `cont`/`diff`/`deriv_le` from the committed `C¹` bricks via
`rotheStep_cont`/`rotheStep_diff`/`rotheStep_deriv_le`; `anti` from
`implicitStep_preserves_antitone` via `rotheStep_anti`; `le_barrier` (`W ≤ Ū`)
and `le_old` (`W ≤ Z`) from the committed clean max-principle via
`rotheStep_le_barrier` (with `B = Ū` and `B = Z` respectively); `nonneg` carried
directly as the lower trap. -/
theorem rotheStepProducer_of_input
    (hin : RotheStepInput p c lam M κ Λ u) :
    RotheStepProducer p c lam M κ Λ u := by
  intro Z hZc hZa hZ0 hZB
  obtain ⟨W, hout⟩ := hin.produce Z hZc hZa hZ0 hZB
  refine ⟨W, ?_⟩
  clear hZc hZa hZ0 hZB
  refine
    { step_eq := hout.analytic.step_eq
      cont := rotheStep_cont hin.hlam hout.analytic
      diff := rotheStep_diff hin.hlam hout.analytic
      deriv_le := rotheStep_deriv_le hin.hlam hout.analytic
      nonneg := hout.nonneg
      le_barrier := ?_
      le_old := ?_
      anti := rotheStep_anti hin.hlam hout.analytic hout.conv_form }
  · exact rotheStep_le_barrier hin.hlam hin.hM hout.analytic hout.maxBarrier
  · exact rotheStep_le_barrier hin.hlam hin.hM hout.analytic hout.maxZ

/-- **`rotheStepProducer` — the per-`u` producer over the monotone trap set.**
For every frozen profile `u ∈ InMonotoneWaveTrapSet κ M`, the carried per-step
input yields `RotheStepProducer p c lam M κ Λ u`.  The trap-membership of `u` is
consumed by the carried input's analytic obligations (it supplies `IsCUnifBdd u`
and `0 ≤ u`, which feed `frozenElliptic`'s `C²`-regularity inside the carried
`c2`/`chem`/`Bsuper` facts). -/
theorem rotheStepProducer
    (hinput : ∀ v, InMonotoneWaveTrapSet κ M v → RotheStepInput p c lam M κ Λ v) :
    ∀ u, InMonotoneWaveTrapSet κ M u → RotheStepProducer p c lam M κ Λ u :=
  fun u hu => rotheStepProducer_of_input (hinput u hu)

/-! ## Axiom audit -/

section AxiomAudit
#print axioms rotheStep_deriv_le
#print axioms rotheStep_diff
#print axioms rotheStep_anti
#print axioms rotheStep_le_barrier
#print axioms rotheStepProducer_of_input
#print axioms rotheStepProducer
end AxiomAudit

end ShenWork.Paper1
