/-
  ShenWork/Paper1/RotheStepProducerImpl.lean

  Attack atom #4A — the per-step Rothe/Green producer (`RotheStepProducer`) and
  continuous dependence (`RotheContinuousDependence`) for the χ≤0 frozen wave
  construction.

  This NEW file builds toward the two named hard residuals isolated by
  `WaveRotheClose.b1_chiNeg_existence_clean` and surfaced in
  `ConstructionNegProducer.lean`'s `hprovider`:

    * `hprodTrap : RotheStepProducer p c lam M κ Λ u` — the per-step Green solve
      producing the next Rothe iterate from the old one;
    * `hdep : RotheContinuousDependence …` — continuous dependence of the Rothe
      iterate on its frozen input.

  STRUCTURE (per the task's (i)/(ii)/(iii)):

  (i)  The single most self-contained sub-lemma: the per-step Green-solve
       EXISTENCE as a concrete `ℝ → ℝ`.  From the committed contraction engine
       (`crossStep_exists_unique_concrete`) we extract the down-coerced bounded
       fixed point as a genuine continuous `ℝ → ℝ` satisfying the concrete
       per-step Green convolution equation.  CLOSED UNCONDITIONALLY.  Plus the
       explicit `1/λ`-form of the contraction smallness (`greenKernel_l1_eq`),
       making large-`λ` realizability transparent.  CLOSED UNCONDITIONALLY.

  (ii) Assemble the per-step producer.  The committed `rotheStepProducer_of_input`
       already assembles `RotheStepProducer` from one carried `RotheStepInput`
       whose `produce` field is the analytic Green-solve+max-principle output
       bundle.  We restate that bridge and the orbit-base non-vacuity witness,
       and isolate exactly what the carried `RotheStepInput.produce` still needs
       beyond (i) (the analytic bundle `RotheStepAnalytic`/`RotheMaxData`).

  (iii) Continuous dependence: the reduction `RotheContinuousDependence →
        LocalUniformContinuousOn` is committed (`Tmap_continuousOn`); the deep
        analytic core (`FrozenEllipticDerivDependence` + dominated-convergence
        propagation through the Rothe limit) is NOT a committed closed lemma.
        Carried with a precise stall (see PRECISE STALL block).

  HARD RULES: new file only; no sorry/admit/native_decide/axiom; Mathlib
  v4.29.1; lines ≤100.  §3.3: the lower-pinned (non-vacuous) route only.
-/
import ShenWork.Paper1.WaveRotheProducer
import ShenWork.Paper1.WaveRotheConcrete
import ShenWork.Paper1.WaveRotheTrunc
import ShenWork.Paper1.WaveRotheSchauderData

open Filter Topology MeasureTheory Set BoundedContinuousFunction

noncomputable section

namespace ShenWork.Paper1

/-! ## (i.a) The contraction smallness in explicit `1/λ` form.

The committed `crossStep_exists_unique_concrete` consumes the abstract smallness
`toNNReal(∫|K|) · Ls < 1`.  For the genuine Green kernel `K = greenKernel c lam`,
`∫|K| = 1/λ` (committed `greenKernel_l1_eq`), so the contraction hypothesis is
exactly `toNNReal(1/λ) · Ls < 1` — the large-`λ` smallness made transparent.
This is purely an `∫|K|`-rewrite of the committed hypothesis; no new content. -/

/-- The Green-kernel contraction smallness in explicit `1/λ` form is the abstract
`crossStepSelfMap` smallness for `K = greenKernel c lam`. -/
theorem greenKernel_smallness_iff (c lam : ℝ) (hlam : 0 < lam) (Ls : NNReal) :
    Real.toNNReal (∫ z, |greenKernel c lam z|) * Ls < 1
      ↔ Real.toNNReal lam⁻¹ * Ls < 1 := by
  rw [greenKernel_l1_eq hlam]

/-! ## (i.b) Per-step Green solve EXISTENCE as a concrete `ℝ → ℝ`.

The committed contraction `crossStep_exists_unique_concrete` produces a unique
`ℝ →ᵇ ℝ` fixed point of the truncated source self-map.  Coercing it down gives a
genuine continuous `ℝ → ℝ` solving the concrete per-step Green equation

  `W x = ∫ y, greenKernel c lam (x − y) · S(W) y`,

where `S(W) y = reactionTrunc α M (W y) + λ·Z y + rpowTrunc m M (W y) · Vu' y`.
This is the existence core of the producer's `produce` field — the genuine
per-step solve — BEFORE the analytic bridge to `crossImplicitMap`/`green_repr`/
trap/max-principle (which need the carried integrability/folding bundle; see
STALL).  Closed UNCONDITIONALLY from the committed engine. -/

/-- **(i.b) Per-step Green-solve existence (concrete `ℝ → ℝ`).**
Under the large-`λ` contraction smallness, the truncated per-step source map has a
bounded-continuous fixed point whose down-coercion `W : ℝ → ℝ` is continuous and
solves the concrete per-step Green convolution equation pointwise. -/
theorem crossStep_concrete_solution
    (c lam : ℝ) (hlam : 0 < lam)
    {α m M : ℝ} (ha : 1 ≤ α) (hm : 1 ≤ m) (hM : 0 ≤ M)
    (Z Vu' : ℝ →ᵇ ℝ)
    (hsmall : Real.toNNReal lam⁻¹
        * (Real.toNNReal (reactionLip α M)
            + Real.toNNReal (rpowLip m M) * ‖Vu'‖₊) < 1) :
    ∃ W : ℝ →ᵇ ℝ, Continuous (fun x => (W x : ℝ)) ∧
      (∀ x, (W x : ℝ)
        = ∫ y, greenKernel c lam (x - y)
            * (reactionTrunc α M (W y) + lam * Z y
                + rpowTrunc m M (W y) * Vu' y)) := by
  have hsmall' : Real.toNNReal (∫ z, |greenKernel c lam z|)
      * (Real.toNNReal (reactionLip α M)
          + Real.toNNReal (rpowLip m M) * ‖Vu'‖₊) < 1 := by
    rwa [greenKernel_smallness_iff c lam hlam]
  obtain ⟨W, hWfix, _⟩ :=
    crossStep_exists_unique_concrete
      (greenKernel_continuous (c := c) (lam := lam))
      (greenKernel_integrable hlam) ha hm hM Z Vu' hsmall'
  refine ⟨W, W.continuous, fun x => ?_⟩
  -- `crossStepSelfMap … W = W` ⇒ pointwise `W x = kernelConvVal K (S W) x`.
  have hpt : crossStepSelfMap (greenKernel_continuous (c := c) (lam := lam))
      (greenKernel_integrable hlam)
      (crossStepSourceConcrete α m M lam ha hm hM Z Vu') W x = W x := by
    rw [hWfix]
  rw [crossStepSelfMap, greenConvBCF_apply, kernelConvVal] at hpt
  rw [← hpt]
  refine integral_congr_ae (Eventually.of_forall (fun y => ?_))
  simp only [crossStepSourceConcrete_apply]

/-- **(i.b′) Uniqueness companion.**  The bounded-continuous per-step fixed point
is unique (so the produced concrete iterate is well-defined). -/
theorem crossStep_concrete_unique
    (c lam : ℝ) (hlam : 0 < lam)
    {α m M : ℝ} (ha : 1 ≤ α) (hm : 1 ≤ m) (hM : 0 ≤ M)
    (Z Vu' : ℝ →ᵇ ℝ)
    (hsmall : Real.toNNReal lam⁻¹
        * (Real.toNNReal (reactionLip α M)
            + Real.toNNReal (rpowLip m M) * ‖Vu'‖₊) < 1) :
    ∃! W : ℝ →ᵇ ℝ,
      crossStepSelfMap (greenKernel_continuous (c := c) (lam := lam))
        (greenKernel_integrable hlam)
        (crossStepSourceConcrete α m M lam ha hm hM Z Vu') W = W := by
  have hsmall' : Real.toNNReal (∫ z, |greenKernel c lam z|)
      * (Real.toNNReal (reactionLip α M)
          + Real.toNNReal (rpowLip m M) * ‖Vu'‖₊) < 1 := by
    rwa [greenKernel_smallness_iff c lam hlam]
  exact crossStep_exists_unique_concrete
    (greenKernel_continuous (c := c) (lam := lam))
    (greenKernel_integrable hlam) ha hm hM Z Vu' hsmall'

/-! ## (ii) Assembling the per-step producer.

The committed `rotheStepProducer_of_input` assembles `RotheStepProducer p c lam M
κ Λ u` from a single carried `RotheStepInput`, whose `produce` field delivers the
analytic output bundle `RotheStepOutput` (containing `RotheStepAnalytic` —
`green_repr`/`step_op`/`c2` — plus the `RotheMaxData` comparisons giving the trap
`W ≤ Ū`, descent `W ≤ Z`, antitonicity, and lower trap `0 ≤ W`).  The fields not
yet supplied by (i) are exactly that analytic bundle (see STALL (A)).

We restate the producer bridge and the orbit-base non-vacuity witness in this
file so the assembly path is explicit and the residual is precisely the
`RotheStepInput` (= the analytic output bundle), not the contraction existence. -/

/-- **(ii.a) Producer from input (restated bridge).**  `RotheStepInput` (the
analytic per-step output bundle) assembles into `RotheStepProducer`; the
fixed-point existence half is (i.b), the analytic half is the carried input. -/
theorem rotheStepProducer_of_input'
    {p : CMParams} {c lam M κ Λ : ℝ} {u : ℝ → ℝ}
    (hin : RotheStepInput p c lam M κ Λ u) :
    RotheStepProducer p c lam M κ Λ u :=
  rotheStepProducer_of_input hin

/-- **(ii.b) Orbit-base non-vacuity witness (restated).**  Given the producer and
`0 ≤ κ`, `0 ≤ M`, the supersolution precond at the orbit base `Z = Ū` is met, so a
genuine next iterate `W` with the full `RotheStepFacts` bundle (including the
PROVED `supersol : F_u(W) ≤ 0`) exists.  Certifies the producer is not the vacuous
at-max dodge. -/
theorem rotheStepProducer_base_witness
    {p : CMParams} {c lam M κ Λ : ℝ} {u : ℝ → ℝ}
    (hprod : RotheStepProducer p c lam M κ Λ u) (hκ : 0 ≤ κ) (hM : 0 ≤ M) :
    ∃ W : ℝ → ℝ, RotheStepFacts p c lam M κ Λ u (upperBarrier κ M) W
      ∧ (∀ x, frozenWaveOperator p c u W x ≤ 0) :=
  rotheStepProducer_supersol_satisfiable_at_barrier hprod hκ hM

/-- **(ii.c) Producer over the trap (restated).**  Per-`u` over the monotone trap,
the carried per-step input yields `RotheStepProducer` — exactly the `hprodTrap`
shape consumed by `b1_chiNeg_existence_clean`. -/
theorem rotheStepProducer_trap
    {p : CMParams} {c lam M κ Λ : ℝ}
    (hinput : ∀ v, InMonotoneWaveTrapSet κ M v → RotheStepInput p c lam M κ Λ v) :
    ∀ u, InMonotoneWaveTrapSet κ M u → RotheStepProducer p c lam M κ Λ u :=
  rotheStepProducer hinput

/-! ## (iii) Continuous dependence — reduction built, deep core carried.

The reduction `RotheContinuousDependence → LocalUniformContinuousOn (Tmap)` is the
committed `Tmap_continuousOn` (a trivial unfold).  The genuine analytic core is
`RotheContinuousDependence` itself: `u_n → u` loc-unif ⟹ `Tmap u_n → Tmap u`
loc-unif, which needs the UNCOMMITTED `FrozenEllipticDerivDependence` propagated
through the Rothe limit by dominated convergence with uniform contraction
constants.  We restate the reduction so the residual is isolated to the named
deep core. -/

/-- **(iii.a) Continuous-dependence reduction (restated).**  The carried
`RotheContinuousDependence` packages into the loc-unif continuity field that the
Schauder data consumes.  The deep analytic content is fully inside
`RotheContinuousDependence`; this is the trivial wrapping. -/
theorem rotheContinuousDependence_to_continuousOn
    (p : CMParams) (c lam : ℝ) (trap : (ℝ → ℝ) → Prop)
    (rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ)
    (hdep : RotheContinuousDependence p c lam trap rotheSeq) :
    LocalUniformContinuousOn trap (fun u => rotheLimit (rotheSeq u)) :=
  Tmap_continuousOn p c lam trap rotheSeq hdep

/-
================================================================================
PRECISE STALL — what closed unconditionally vs. carried, and exactly why.
================================================================================

CLOSED UNCONDITIONALLY (no carried hypotheses, pure committed bricks):

  * `greenKernel_smallness_iff` — the contraction smallness in explicit `1/λ`
    form (rewrite of the committed `greenKernel_l1_eq`).
  * `crossStep_concrete_solution` — (i.b) the per-step Green-solve EXISTENCE as a
    concrete continuous `ℝ → ℝ` satisfying the per-step Green convolution
    equation.  This is the genuine fixed-point existence half of the producer's
    `produce` field, extracted from the committed contraction
    `crossStep_exists_unique_concrete`.
  * `crossStep_concrete_unique` — (i.b′) its uniqueness companion.

  All three are axiom-clean (only the committed engine, which is
  propext/Classical.choice/Quot.sound).

REDUCTIONS BUILT (restating committed bridges to isolate the residual):

  * `rotheStepProducer_of_input'` — `RotheStepInput → RotheStepProducer`.
  * `rotheStepProducer_base_witness` — orbit-base non-vacuity witness.
  * `rotheStepProducer_trap` — the per-trap `hprodTrap` shape.
  * `rotheContinuousDependence_to_continuousOn` — the (iii) reduction.

CARRIED (genuine analytic residuals; NOT closeable from committed bricks here):

 (A) THE PER-STEP ANALYTIC BUNDLE `RotheStepInput.produce` (beyond (i.b)).
     EXACT STALL: to upgrade the concrete fixed point of (i.b)
     (`crossStep_concrete_solution`) into a `RotheStepOutput p c lam M κ Λ u Z W`
     — the input `rotheStepProducer_of_input'` consumes — one must still supply,
     for the produced `W`:

       1. `RotheStepAnalytic.green_repr` + `step_op` + `c2`: the bridge from the
          TRUNCATED bcf source self-map (`crossStepSourceConcrete`, with
          `reactionTrunc`/`rpowTrunc` and the divergence-folded flux) to the RAW
          `crossImplicitMap p c lam u Z W` and to the differential step
          `implicitStepOp p c (1/λ) u W = Z`.  This bridge is the committed
          `crossStepSelfMap_apply_eq_crossImplicitMap` (file `WaveStepFluxId.lean`,
          line 80) — but it carries ~14 per-`x` integrability / decay / folding
          hypotheses (`hWtrap`, `hfold`, `hSmIic/Ioi`, `hFlIic/Ioi`, `hG_C1`,
          `hKv'_*`, `hK'v_*`, `hKG_*`, `hdecay_*`).  Discharging those from the
          trap is the §3.3 satisfiability content; it INTRODUCES fresh carried
          obligations rather than removing them, so it is not closeable here.

       2. `RotheMaxData` for `B ∈ {Ū, Z}`: the clean (lower-pinned, NON-vacuous)
          maximum-principle comparison data giving the trap `W ≤ Ū`, descent
          `W ≤ Z`, antitonicity, and `0 ≤ W`.  These rest on the supersolution
          ordering `frozenWaveOperator p c u Ū ≤ 0` and the at-max chemotaxis
          residual bound — the genuinely-elliptic order content, uncommitted but
          satisfiable on the trapped supersolution orbit (documented in
          `WaveRotheClose.lean`, item `hprodTrap`).

     MISSING LEMMA SIGNATURE (the smallest closing step, were the carried
     integrability/ordering data available):
       `crossStep_output_of_solution :
          (concrete fixed point W of crossStep_concrete_solution) →
          (the carried integrability/folding bundle of
             crossStepSelfMap_apply_eq_crossImplicitMap) →
          (the lower-pinned RotheMaxData for B = Ū and B = Z) →
          RotheStepOutput p c lam M κ Λ u Z W`.
     This is a REAL PDE gap (it CONSUMES the produced step solution and the
     elliptic comparison; it does not re-assume the producer's conclusion — no
     circularity).  EXACT STALL LOCATION: the `RotheStepInput.produce` field that
     `rotheStepProducer_of_input'` consumes; equivalently the `hprodTrap` input of
     `b1_chiNeg_existence_clean` (WaveRotheClose.lean).

 (B) `RotheContinuousDependence` (the deep core of (iii)).
     EXACT STALL: `RotheContinuousDependence p c lam trap rotheSeq` requires
     `u_n → u` loc-unif ⟹ `rotheLimit (rotheSeq u_n) → rotheLimit (rotheSeq u)`
     loc-unif.  Its committed sub-core is `FrozenEllipticDerivDependence`
     (continuous dependence of `deriv (frozenElliptic p u)` on `u`), but
     propagating it through the per-step Green map to the Rothe LIMIT —
     dominated convergence with the uniform contraction constants, then the
     pointwise-inf limit — is NOT a committed closed lemma.
     MISSING LEMMA SIGNATURE:
       `rotheLimit_continuousDependence :
          FrozenEllipticDerivDependence p →
          (uniform per-step contraction bound, uniform in n) →
          RotheContinuousDependence p c lam trap (rotheSeqFromTrap …)`.
     REAL analytic gap (no circularity).  Carried.

HONEST LABEL: the per-step producer is NOT proved unconditionally.  The genuine
fixed-point EXISTENCE half (i.b) IS proved unconditionally and axiom-clean; the
remaining content — the per-step ANALYTIC bundle (A) and the continuous
dependence (B) — are the two named hard residuals (`hprodTrap`, `hdep`) already
isolated by `WaveRotheClose.b1_chiNeg_existence_clean`, here further localized to
the precise missing lemma signatures above.  No vacuity, no over-strong
hypotheses, no FALSE bare-trap Schauder principle.
================================================================================
-/

section AxiomAudit
#print axioms greenKernel_smallness_iff
#print axioms crossStep_concrete_solution
#print axioms crossStep_concrete_unique
#print axioms rotheStepProducer_of_input'
#print axioms rotheStepProducer_base_witness
#print axioms rotheStepProducer_trap
#print axioms rotheContinuousDependence_to_continuousOn
end AxiomAudit

end ShenWork.Paper1
