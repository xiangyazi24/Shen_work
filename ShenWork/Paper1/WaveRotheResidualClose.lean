/-
  ShenWork/Paper1/WaveRotheResidualClose.lean

  **Discharging the now-committed fields of the B1 `RotheFloorResidual`.**

  `RotheFloorResidual p c lam M κ Λ u` (WaveRotheFloor.lean) is the single named
  per-profile residual carried by `b1_chiNeg_existence_unconditional`.  Its
  `produce` `Σ'` payload bundles, for every trapped continuous antitone `Z`, the
  produced iterate `W`, its Green source `R`, the chem constant, the four tail
  limits, a flat `∧`-chain of analytic Props, and two `RotheStepChemData` slots.

  This file isolates the fields that are NOW dischargeable from committed bricks
  — chiefly the WHOLE-LINE super-barrier `frozenWaveOperator p c u Ū ≤ 0`, just
  committed as `whole_line_super_barrier` — and the two trivial fields
  (`Z ≤ Z`, `Z ≤ Ū`), and packages the genuinely-uncommitted whole-line Green
  data as ONE precisely-named per-profile core predicate `RotheFloorResidualCore`.

  ## Two genuinely-new committed lemmas delivered here

  The `RotheFloorResidual.produce` payload's super-barrier comparison `W ≤ Ū`
  flows through the clean max-principle, whose `BC2` field demands
  `∀ y, ContDiffAt ℝ 2 (upperBarrier κ M) y`.  But `upperBarrier κ M`
  has a CONCAVE CORNER at the free interface `exp(-κx) = M`
  (`not_differentiableAt_upperBarrier_of_interface`), so it is NOT `C²` there —
  the everywhere-`C²` field is literally FALSE under the kink regime.  The honest
  resolution (anticipated by the task) is that `BC2` is only ever consumed at the
  internally-chosen positive-max point of `φ = W − Ū`, and that max point cannot
  be the interface.  We prove BOTH halves here as genuine, axiom-clean lemmas:

    * `upperBarrier_contDiffAt_two_of_ne_interface` — `Ū` is `C²` at every NON-
      interface point (locally it is the constant `M` or `expDecay κ`, both `C²`);
    * `maxSub_upperBarrier_ne_interface` — at a local max of `φ = W − Ū` with `W`
      differentiable there, the point is NOT the interface (the corner of `−Ū`
      makes `φ` have an upward corner, killing the local max).

  Together these show the `BC2`-of-`Ū` obligation the max-principle actually needs
  (BC2 AT THE MAX) is dischargeable; the everywhere-`C²` field as literally
  written in the committed `RotheStepFloor`/`RotheFloorResidual` def is the one
  field that is genuinely false and is reported as a precise def-level defect (see
  the closing note).  Everything else in the payload that is NOT genuinely-deep
  whole-line Green analysis is discharged here.

  ## What is discharged vs. carried

  DISCHARGED here from committed bricks (no new hypotheses):
    * the super-barrier `frozenWaveOperator p c u Ū ≤ 0`     ← `whole_line_super_barrier`
    * `Z ≤ Z`                                                ← `le_refl`
    * `Z ≤ Ū`                                                ← the producer hypothesis `hZB`

  CARRIED as the precisely-named `RotheFloorResidualCore` (the genuinely-deep
  whole-line Green-convolution content the repo has NOT committed for arbitrary
  trapped `u`):
    * existence of `W`, `R` with `W = greenConv R`, the raw-conv form, `R`
      continuity / sup-bound / two-sided weighted-tail integrability / antitone /
      translated-tail integrability;
    * the differential step `implicitStepOp (1/λ) u W = Z` and the realized
      `W = crossImplicitMap`;
    * `0 ≤ W`, the chem constant + smallness, the two-sided `W − B` tails
      (`B ∈ {Z, Ū}`), the trapped-range max membership, and the two
      `RotheStepChemData`;
    * `C²`-of-`Z` (Green-represented, but the source-regularity is `Z`-specific
      and not committed), and the `BC2`-of-`Ū` AT THE MAX (here dischargeable, but
      the committed def asks for it EVERYWHERE — see the note).

  No proof holes, no extra logical assumptions, no `native_decide`.  Touches only Paper1.
-/
import ShenWork.Paper1.WaveRotheFloor
import ShenWork.Paper1.WaveSuperBarrier

open Filter Topology MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

variable {c lam : ℝ}

/-! ## 0. Bounded-source Green integrability closures

The source weighted tails and translated kernel integrability used by the Green
derivative/order bricks are not independent analytic payload: a continuous
bounded source is enough, because the committed Green roots have the correct
signs and `greenKernel` is `L¹`. -/

/-- A bounded continuous source has integrable upper weighted tails for every
positive exponential weight. -/
theorem rotheResidual_gWeight_integrableOn_Ioi_of_bounded {r B : ℝ} {H : ℝ → ℝ}
    (hr : 0 < r) (hH : Continuous H) (hB : ∀ y, |H y| ≤ B) :
    ∀ x, IntegrableOn (gWeight r H) (Ioi x) := by
  intro x
  have hbase : IntegrableOn (fun y : ℝ => Real.exp ((-r) * y)) (Ioi x) :=
    integrableOn_exp_mul_Ioi (a := -r) (by linarith) x
  have hbound : ∀ᵐ y ∂(volume.restrict (Ioi x)), ‖H y‖ ≤ B :=
    Eventually.of_forall (fun y => by simpa [Real.norm_eq_abs] using hB y)
  change Integrable (fun y : ℝ => Real.exp ((-r) * y) * H y)
    (volume.restrict (Ioi x))
  exact hbase.mul_bdd (c := B) hH.aestronglyMeasurable hbound

/-- A bounded continuous source has integrable lower weighted tails for every
negative exponential weight. -/
theorem rotheResidual_gWeight_integrableOn_Iic_of_bounded {r B : ℝ} {H : ℝ → ℝ}
    (hr : r < 0) (hH : Continuous H) (hB : ∀ y, |H y| ≤ B) :
    ∀ x, IntegrableOn (gWeight r H) (Iic x) := by
  intro x
  have hbase : IntegrableOn (fun y : ℝ => Real.exp ((-r) * y)) (Iic x) :=
    integrableOn_exp_mul_Iic (a := -r) (by linarith) x
  have hbound : ∀ᵐ y ∂(volume.restrict (Iic x)), ‖H y‖ ≤ B :=
    Eventually.of_forall (fun y => by simpa [Real.norm_eq_abs] using hB y)
  change Integrable (fun y : ℝ => Real.exp ((-r) * y) * H y)
    (volume.restrict (Iic x))
  exact hbase.mul_bdd (c := B) hH.aestronglyMeasurable hbound

/-- A bounded continuous source can be multiplied by any translate of the
committed `L¹` Green kernel. -/
theorem greenKernel_translated_integrable_of_bounded {c lam B : ℝ} {H : ℝ → ℝ}
    (hlam : 0 < lam) (hH : Continuous H) (hB : ∀ y, |H y| ≤ B) :
    ∀ x, Integrable (fun t => greenKernel c lam (-t) * H (x + t)) := by
  intro x
  have hK : Integrable (fun t : ℝ => greenKernel c lam (-t)) :=
    (greenKernel_integrable (c := c) hlam).comp_neg
  exact hK.mul_bdd
    ((hH.comp (continuous_const.add continuous_id)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t => by
      simpa [Real.norm_eq_abs] using hB (x + t))

/-! ## 1. `upperBarrier` is `C²` away from the free interface

At any point that is NOT the interface `exp(-κx) = M`, `upperBarrier κ M` is
locally either the constant `M` (constant region) or `expDecay κ` (exponential
region); both are `C²`, so `Ū` is `ContDiffAt ℝ 2` there. -/

/-- **`Ū` is `C²` at every non-interface point.**  If `exp(-κ x) ≠ M`, then
`upperBarrier κ M` is `ContDiffAt ℝ 2` at `x`. -/
theorem upperBarrier_contDiffAt_two_of_ne_interface {κ M x : ℝ}
    (hx : Real.exp (-κ * x) ≠ M) :
    ContDiffAt ℝ 2 (upperBarrier κ M) x := by
  rcases lt_trichotomy (Real.exp (-κ * x)) M with hlt | heq | hgt
  · -- exponential region: locally `Ū = expDecay κ`, which is C²
    have hEq : upperBarrier κ M =ᶠ[𝓝 x] expDecay κ :=
      upperBarrier_eventuallyEq_exp_of_lt hlt
    have hC2 : ContDiffAt ℝ 2 (expDecay κ) x := by
      have : ContDiff ℝ 2 (expDecay κ) := by
        unfold expDecay
        exact (Real.contDiff_exp).comp
          ((contDiff_const.mul contDiff_id).neg)
      exact this.contDiffAt
    exact hC2.congr_of_eventuallyEq hEq
  · exact absurd heq hx
  · -- constant region: locally `Ū = M`, which is C²
    have hEq : upperBarrier κ M =ᶠ[𝓝 x] (fun _ : ℝ => M) :=
      upperBarrier_eventuallyEq_const_of_lt hgt
    have hC2 : ContDiffAt ℝ 2 (fun _ : ℝ => M) x := contDiffAt_const
    exact hC2.congr_of_eventuallyEq hEq

/-! ## 2. A local max of `φ = W − Ū` cannot be at the interface

`upperBarrier` has a CONCAVE corner at the interface: left one-sided derivative
`0`, right one-sided derivative `-κM < 0`.  For differentiable `W`, `φ = W − Ū`
then has right one-sided derivative `W'(x) + κM` and left one-sided derivative
`W'(x)`.  At a local max, the right derivative is `≤ 0` and the left derivative is
`≥ 0`, forcing `κM ≤ -W'(x) ≤ 0`, contradicting `κM > 0`.  Hence the max point is
not the interface. -/

/-- **The positive-max of `φ = W − Ū` avoids the kink.**  If `W` is differentiable
at `x`, `φ = W − Ū` has a local max at `x`, `0 < κ` and `0 < M`, then
`exp(-κ x) ≠ M`. -/
theorem maxSub_upperBarrier_ne_interface {κ M : ℝ} {W : ℝ → ℝ} {x : ℝ}
    (hκ : 0 < κ) (hM : 0 < M)
    (hWdiff : DifferentiableAt ℝ W x)
    (hmax : IsLocalMax (fun y => W y - upperBarrier κ M y) x) :
    Real.exp (-κ * x) ≠ M := by
  intro hint
  set w' := deriv W x with hw'
  have hWhas : HasDerivAt W w' x := hWdiff.hasDerivAt
  -- `Ū` agrees with `expDecay κ` on a right neighbourhood within `Ici x`
  -- (on `Ici x` near `x` we have `y ≥ x`, so `exp(-κy) ≤ M`, hence `Ū = expDecay`).
  have hUx_exp : upperBarrier κ M x = expDecay κ x := by
    rw [upperBarrier_eq_exp_of_exp_le hint.le]; simp [expDecay]
  have hUx_M : upperBarrier κ M x = M := upperBarrier_eq_M_of_le_exp hint.ge
  have hEqR : upperBarrier κ M =ᶠ[𝓝[Set.Ici x] x] expDecay κ := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hyge : x ≤ y := hy
    have hyexp : Real.exp (-κ * y) ≤ M := by
      rw [← hint]; apply Real.exp_le_exp.mpr; nlinarith [hyge, hκ]
    rw [upperBarrier_eq_exp_of_exp_le hyexp]; simp [expDecay]
  have hEqL : upperBarrier κ M =ᶠ[𝓝[Set.Iic x] x] (fun _ : ℝ => M) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hyle : y ≤ x := hy
    have hyexp : M ≤ Real.exp (-κ * y) := by
      rw [← hint]; apply Real.exp_le_exp.mpr; nlinarith [hyle, hκ]
    rw [upperBarrier_eq_M_of_le_exp hyexp]
  -- one-sided derivatives of `Ū`: `-κM` on `Ici x`, `0` on `Iic x`
  have hŪhasR : HasDerivWithinAt (upperBarrier κ M) (-κ * M) (Set.Ici x) x := by
    have hbase : HasDerivWithinAt (expDecay κ) (-κ * expDecay κ x) (Set.Ici x) x :=
      (expDecay_hasDerivAt κ x).hasDerivWithinAt
    have hbase' : HasDerivWithinAt (expDecay κ) (-κ * M) (Set.Ici x) x := by
      have : expDecay κ x = M := by rw [← hUx_exp]; exact hUx_M
      rwa [this] at hbase
    exact hbase'.congr_of_eventuallyEq hEqR hUx_exp
  have hŪhasL : HasDerivWithinAt (upperBarrier κ M) (0 : ℝ) (Set.Iic x) x := by
    have hbase : HasDerivWithinAt (fun _ : ℝ => M) (0 : ℝ) (Set.Iic x) x :=
      (hasDerivWithinAt_const x (Set.Iic x) M)
    exact hbase.congr_of_eventuallyEq hEqL hUx_M
  -- one-sided derivatives of `φ = W − Ū`
  have hWR : HasDerivWithinAt W w' (Set.Ici x) x := hWhas.hasDerivWithinAt
  have hWL : HasDerivWithinAt W w' (Set.Iic x) x := hWhas.hasDerivWithinAt
  have hφR : HasDerivWithinAt (fun y => W y - upperBarrier κ M y)
      (w' - (-κ * M)) (Set.Ici x) x := hWR.sub hŪhasR
  have hφL : HasDerivWithinAt (fun y => W y - upperBarrier κ M y)
      (w' - 0) (Set.Iic x) x := hWL.sub hŪhasL
  -- local max on each side
  have hmaxR : IsLocalMaxOn (fun y => W y - upperBarrier κ M y) (Set.Ici x) x :=
    hmax.on (Set.Ici x)
  have hmaxL : IsLocalMaxOn (fun y => W y - upperBarrier κ M y) (Set.Iic x) x :=
    hmax.on (Set.Iic x)
  -- `1 ∈ posTangentConeAt (Ici x) x`, `-1 ∈ posTangentConeAt (Iic x) x`
  have h1R : (1 : ℝ) ∈ posTangentConeAt (Set.Ici x) x := by
    apply mem_posTangentConeAt_of_segment_subset
    intro z hz
    have hsub : segment ℝ x (x + 1) ⊆ Set.Icc x (x + 1) :=
      segment_subset_Icc (by linarith)
    exact (Set.mem_Icc.mp (hsub hz)).1
  have h1L : (-1 : ℝ) ∈ posTangentConeAt (Set.Iic x) x := by
    apply mem_posTangentConeAt_of_segment_subset
    intro z hz
    -- segment is symmetric: segment x (x + -1) = segment (x-1) x ⊆ Icc (x-1) x
    rw [segment_symm] at hz
    have hsub : segment ℝ (x + -1) x ⊆ Set.Icc (x + -1) x :=
      segment_subset_Icc (by linarith)
    exact (Set.mem_Icc.mp (hsub hz)).2
  -- fderiv sign at the local max
  have hRfderiv := hmaxR.hasFDerivWithinAt_nonpos hφR.hasFDerivWithinAt h1R
  have hLfderiv := hmaxL.hasFDerivWithinAt_nonpos hφL.hasFDerivWithinAt h1L
  -- the fderiv of a `HasDerivWithinAt`-function applied to `t` is
  -- `toSpanSingleton ℝ f' t = t • f'`
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, one_mul,
    neg_mul, sub_zero] at hRfderiv hLfderiv
  -- hRfderiv : (w' - (-κ*M)) ≤ 0 ;  hLfderiv : -w' ≤ 0  i.e.  0 ≤ w'
  have hκM : 0 < κ * M := mul_pos hκ hM
  nlinarith [hRfderiv, hLfderiv, hκM]

/-- **The super-barrier `BC2`-at-max field IS dischargeable — the defect is closed.**
This is the witness that the weakened (at-max) `BC2`-of-`Ū` obligation carried by
`RotheFloorResidualCore`/`RotheFloorResidual` is honestly SATISFIABLE (not vacuous):
given the produced iterate `W` differentiable at the chosen max (which the
Green-convolution iterate always is) and `0 < κ`, `0 < M`, at any point that IS an
`IsMaxOn`-max of `φ = W − Ū`, `Ū` is `C²` there.  Combines the two committed
enablers: `maxSub_upperBarrier_ne_interface` (the max is never the kink) feeds
`upperBarrier_contDiffAt_two_of_ne_interface` (`Ū` is `C²` off the kink). -/
theorem upperBarrier_BC2_atMax_dischargeable {κ M : ℝ} {W : ℝ → ℝ}
    (hκ : 0 < κ) (hM : 0 < M) (hWdiff : Differentiable ℝ W) :
    ∀ x₀, IsMaxOn (fun x => W x - upperBarrier κ M x) Set.univ x₀ →
      ContDiffAt ℝ 2 (upperBarrier κ M) x₀ := by
  intro x₀ hmax
  have hloc : IsLocalMax (fun x => W x - upperBarrier κ M x) x₀ :=
    hmax.isLocalMax Filter.univ_mem
  have hne : Real.exp (-κ * x₀) ≠ M :=
    maxSub_upperBarrier_ne_interface hκ hM (hWdiff x₀) hloc
  exact upperBarrier_contDiffAt_two_of_ne_interface hne

/-! ## 3. The genuinely-deep whole-line Green-convolution core (carried)

`RotheFloorResidualCore p c lam M κ Λ u` carries exactly the fields of the
`RotheFloorResidual.produce` payload that the repo has NOT committed for an
arbitrary trapped `u`: the existence + analysis of the iterate `W` and Green
source `R`, the two-sided tails, the chem data, the `C²`-of-`Z`, and (because the
committed def demands it everywhere) the `BC2`-of-`Ū`.  The super-barrier and the
two trivial order fields are NOT carried — they are discharged by the builder.

Concretely the core's `produce`, for each trapped antitone `Z`, yields the SAME
`Σ'` as the floor but with the super-barrier field `frozenWaveOperator p c u Ū ≤ 0`
REPLACED by `True` (discharged downstream) and `Z ≤ Z`, `Z ≤ Ū` likewise dropped.
For faithfulness with the existing `RotheFloorResidual` shape — whose payload has
those three fields inlined — we instead carry the FULL payload here and let the
builder simply re-export it; the genuinely-new content this file contributes is
the two `Ū` lemmas above plus the super-barrier wiring in §4. -/

/-- The carried genuinely-deep core.  Field-identical to `RotheFloorResidual` but
re-exported so the builder can substitute the now-committed super-barrier.  Its
`produce` is the floor payload MINUS the super-barrier obligation (carried as the
weaker hypothesis `hSuperFree`, supplied by the builder from
`whole_line_super_barrier`). -/
structure RotheFloorResidualCore
    (p : CMParams) (c lam M κ Λ : ℝ) (u : ℝ → ℝ) where
  hlam : 0 < lam
  hM : 0 ≤ M
  /-- The whole-line super-barrier for `Ū`, supplied to the core (the builder
  feeds it from `whole_line_super_barrier`). -/
  hSuper : ∀ x, frozenWaveOperator p c u (upperBarrier κ M) x ≤ 0
  /-- For each trapped antitone `Z`, the produced iterate `W`, its Green source
  `R`, the chem constant, the four tail limits, and the genuinely-deep analytic
  `∧`-chain + two `RotheStepChemData` slots — EVERY field of the floor payload
  EXCEPT the super-barrier obligation (which is `hSuper`) and the two trivial
  order fields (`Z ≤ Z`, `Z ≤ Ū`), which the builder supplies. -/
  produceCore : ∀ Z : ℝ → ℝ, Continuous Z → Antitone Z → (∀ x, 0 ≤ Z x) →
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
        -- the descent-barrier super-solution `F_u(Z) ≤ 0` (now the INPUT precond
        -- `hZsuper`; re-emitted here so the floor payload shape is preserved):
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
        (RotheStepAntitoneData p c lam M C_chem u Z W ×'
        ((∀ x₀, IsMaxOn (fun x => W x - Z x) Set.univ x₀ →
            RotheStepChemData p u W Z C_chem x₀) ×'
          (∀ x₀, IsMaxOn (fun x => W x - upperBarrier κ M x) Set.univ x₀ →
            RotheStepChemData p u W (upperBarrier κ M) C_chem x₀)))

/-! ## 4. `RotheFloorResidual` from the core + the committed super-barrier

The builder threads the core's deep payload into the floor `Σ'`, inserting the
super-barrier obligation from `hSuper` and the two trivial order fields
(`Z ≤ Z` by `le_refl`, `Z ≤ Ū` = the producer's `hZB`). -/

/-- **`rotheFloorResidual_of_core` — assemble the floor residual from the deep
core, discharging the now-committed super-barrier and the two trivial order
fields.** -/
def rotheFloorResidual_of_core
    {p : CMParams} {c lam M κ Λ : ℝ} {u : ℝ → ℝ}
    (h : RotheFloorResidualCore p c lam M κ Λ u) :
    RotheFloorResidual p c lam M κ Λ u where
  hlam := h.hlam
  hM := h.hM
  baseSuper := h.hSuper
  produce := by
    intro Z hZc hZa hZ0 hZB hZsuper
    obtain ⟨W, R, C_chem, LaZ, LbZ, LaB, LbB,
        ⟨hgr, hcf, hRc, hRb, hRhi, hRlo, hRanti, hRint, hstepop, hnonneg,
          hstepeq, hCnn, hCB, hBsupZ,
          hφcZ, hbotZ, hLaZ, htopZ, hLbZ, hBC2Z, hrangeZ,
          hφcB, hbotB, hLaB, htopB, hLbB, hBC2B, hrangeB⟩,
        hanti, hchemZ, hchemB⟩ :=
      h.produceCore Z hZc hZa hZ0 hZB hZsuper
    exact ⟨W, R, C_chem, LaZ, LbZ, LaB, LbB,
      ⟨hgr, hcf, hRc, hRb, hRhi, hRlo, hRanti, hRint, hstepop, hnonneg,
        hstepeq, hCnn, hCB,
        hBsupZ,                            -- F_u(Z) ≤ 0 (descent super-solution, carried)
        fun x => le_refl (Z x),            -- Z ≤ Z (trivial, discharged here)
        hφcZ, hbotZ, hLaZ, htopZ, hLbZ, hBC2Z, hrangeZ,
        h.hSuper,                          -- F_u(Ū) ≤ 0 (committed super-barrier)
        hZB,                               -- Z ≤ Ū (producer hypothesis, discharged here)
        hφcB, hbotB, hLaB, htopB, hLbB, hBC2B, hrangeB⟩,
      hanti, hchemZ, hchemB⟩

/-! ## 4a. A thinner core with the already-committed fields discharged

`RotheFloorResidualCoreSlim` removes the fields that are already forced by
committed Green-kernel decay/L¹ bricks and by trivial/max-principle bookkeeping:

* `F_u(Ū) ≤ 0` is supplied to the builder as `hSuper`;
* `F_u(Z) ≤ 0`, `Z ≤ Z`, and `Z ≤ Ū` are producer inputs/trivial;
* continuity of `W - Z` and `W - Ū` follows from the Green representation;
* the at-max `C²` field for `Ū` follows from
  `upperBarrier_BC2_atMax_dischargeable`.
* the source weighted tails and translated Green-kernel integrability follow
  from `R_cont`, `R_bound`, the signs of `greenRootPlus`/`greenRootMinus`, and
  the committed Green-kernel half-line/L¹ integrability bricks.

The remaining fields are the precise per-step analytic gaps: Green source
regularity/boundedness, the named source-antitonicity residual (not a consequence
of boundedness/L¹), the differential step, the named endpoint-asymptotic residual,
the `Z` at-max field, range data, and the two chem data slots. -/

/-- Named residual for the step source monotonicity.

This is not a consequence of `greenKernel` decay/L¹ data alone: decay controls
integrability of `Kλ * R`, while monotonicity is a property of the source `R`
itself. -/
structure RotheSlimSourceAntitone (R : ℝ → ℝ) : Prop where
  antitone : Antitone R

/-- Named residual for the two max-principle endpoint asymptotics left after the
Green integrability fields have been discharged.  These are the boundary
conditions for `W - Z` and `W - Ū`; bounded source plus Green `L¹` does not decide
their endpoint signs, so this is the precise carried tail information. -/
structure RotheSlimEndpointAsymptotics (κ M : ℝ) (W Z : ℝ → ℝ)
    (LaZ LbZ LaB LbB : ℝ) : Prop where
  hbotZ : Tendsto (fun x => W x - Z x) atBot (𝓝 LaZ)
  hLaZ : LaZ ≤ 0
  htopZ : Tendsto (fun x => W x - Z x) atTop (𝓝 LbZ)
  hLbZ : LbZ ≤ 0
  hbotB : Tendsto (fun x => W x - upperBarrier κ M x) atBot (𝓝 LaB)
  hLaB : LaB ≤ 0
  htopB : Tendsto (fun x => W x - upperBarrier κ M x) atTop (𝓝 LbB)
  hLbB : LbB ≤ 0

/-- Non-vacuity check for `RotheSlimSourceAntitone`: constant sources satisfy the
carried source-order residual. -/
theorem rotheSlimSourceAntitone_const (a : ℝ) :
    RotheSlimSourceAntitone (fun _ : ℝ => a) :=
  ⟨antitone_const⟩

/-- Bounded continuous sources need not be antitone; hence `Antitone R` cannot be
discharged from the bounded-source Green `L¹` hypotheses alone. -/
theorem bounded_continuous_source_not_forces_antitone :
    ∃ R : ℝ → ℝ, Continuous R ∧ (∃ B : ℝ, ∀ y, |R y| ≤ B) ∧ ¬ Antitone R := by
  refine ⟨Real.sin, Real.continuous_sin, ⟨1, fun y => Real.abs_sin_le_one y⟩, ?_⟩
  intro hanti
  have hle := hanti (show (0 : ℝ) ≤ Real.pi / 2 by positivity)
  rw [Real.sin_pi_div_two, Real.sin_zero] at hle
  norm_num at hle

/-- Non-vacuity check for `RotheSlimEndpointAsymptotics`: the exact barrier
profile has zero endpoint gaps against itself. -/
theorem rotheSlimEndpointAsymptotics_barrier (κ M : ℝ) :
    RotheSlimEndpointAsymptotics κ M (upperBarrier κ M) (upperBarrier κ M)
      0 0 0 0 := by
  refine ⟨?_, le_rfl, ?_, le_rfl, ?_, le_rfl, ?_, le_rfl⟩
  · simp
  · simp
  · simp
  · simp

/-- The genuinely remaining per-profile Green core after the committed/trivial
max-principle fields are discharged by `rotheFloorResidual_of_slimCore`. -/
structure RotheFloorResidualCoreSlim
    (p : CMParams) (c lam M κ Λ : ℝ) (u : ℝ → ℝ) where
  hlam : 0 < lam
  hM : 0 ≤ M
  produceCore : ∀ Z : ℝ → ℝ, Continuous Z → Antitone Z → (∀ x, 0 ≤ Z x) →
      (∀ x, Z x ≤ upperBarrier κ M x) →
      (∀ x, frozenWaveOperator p c u Z x ≤ 0) →
      Σ' (W : ℝ → ℝ) (R : ℝ → ℝ) (C_chem LaZ LbZ LaB LbB : ℝ),
        ((W = fun x => greenConv c lam R x) ∧
        (W = fun x => ∫ y, greenKernel c lam (x - y) * R y) ∧
        Continuous R ∧
        (∃ B : ℝ, (∀ y, |R y| ≤ B) ∧ Λ = 2 * (greenDelta c lam)⁻¹ * B) ∧
        RotheSlimSourceAntitone R ∧
        (∀ x, implicitStepOp p c (1 / lam) u W x = Z x) ∧
        (∀ x, 0 ≤ W x) ∧
        (W = crossImplicitMap p c lam u Z W) ∧
        (0 ≤ C_chem) ∧
        ((1 / lam) * (reactionLip p.α M + C_chem) < 1) ∧
        RotheSlimEndpointAsymptotics κ M W Z LaZ LbZ LaB LbB ∧
        (∀ x₀, IsMaxOn (fun x => W x - Z x) Set.univ x₀ →
          ContDiffAt ℝ 2 Z x₀) ∧
        (∀ x₀, IsMaxOn (fun x => W x - Z x) Set.univ x₀ →
          W x₀ ∈ Set.Icc (0 : ℝ) M ∧ Z x₀ ∈ Set.Icc (0 : ℝ) M) ∧
        (∀ x₀, IsMaxOn (fun x => W x - upperBarrier κ M x) Set.univ x₀ →
          W x₀ ∈ Set.Icc (0 : ℝ) M ∧ upperBarrier κ M x₀ ∈ Set.Icc (0 : ℝ) M)) ×'
        (RotheStepAntitoneData p c lam M C_chem u Z W ×'
        ((∀ x₀, IsMaxOn (fun x => W x - Z x) Set.univ x₀ →
            RotheStepChemData p u W Z C_chem x₀) ×'
          (∀ x₀, IsMaxOn (fun x => W x - upperBarrier κ M x) Set.univ x₀ →
            RotheStepChemData p u W (upperBarrier κ M) C_chem x₀)))

/-- Assemble the old residual floor from the thinner core, inserting the fields
that are already committed/trivial. -/
def rotheFloorResidual_of_slimCore
    {p : CMParams} {c lam M κ Λ : ℝ} {u : ℝ → ℝ}
    (hSuper : ∀ x, frozenWaveOperator p c u (upperBarrier κ M) x ≤ 0)
    (hκ : 0 < κ) (hMpos : 0 < M)
    (h : RotheFloorResidualCoreSlim p c lam M κ Λ u) :
    RotheFloorResidual p c lam M κ Λ u where
  hlam := h.hlam
  hM := h.hM
  baseSuper := hSuper
  produce := by
    intro Z hZc hZa hZ0 hZB hZsuper
    obtain ⟨W, R, C_chem, LaZ, LbZ, LaB, LbB,
        ⟨hgr, hcf, hRc, hRb, hRanti, hstepop, hnonneg,
          hstepeq, hCnn, hCB, htails, hBC2Z, hrangeZ, hrangeB⟩,
        hanti, hchemZ, hchemB⟩ :=
      h.produceCore Z hZc hZa hZ0 hZB hZsuper
    have hRhi : ∀ x, IntegrableOn (gWeight (greenRootPlus c lam) R) (Ioi x) := by
      rcases hRb with ⟨_B, hRbd, _hΛ⟩
      exact rotheResidual_gWeight_integrableOn_Ioi_of_bounded
        (greenRootPlus_pos (c := c) (lam := lam) h.hlam) hRc hRbd
    have hRlo : ∀ x, IntegrableOn (gWeight (greenRootMinus c lam) R) (Iic x) := by
      rcases hRb with ⟨_B, hRbd, _hΛ⟩
      exact rotheResidual_gWeight_integrableOn_Iic_of_bounded
        (greenRootMinus_neg (c := c) (lam := lam) h.hlam) hRc hRbd
    have hRint : ∀ x, Integrable (fun t => greenKernel c lam (-t) * R (x + t)) := by
      rcases hRb with ⟨_B, hRbd, _hΛ⟩
      exact greenKernel_translated_integrable_of_bounded
        (c := c) (lam := lam) h.hlam hRc hRbd
    have hWdiff : Differentiable ℝ W := by
      rw [hgr]
      intro x
      exact (greenConv_hasDerivAt (c := c) (lam := lam) hRc hRhi hRlo x).differentiableAt
    have hWcont : Continuous W := hWdiff.continuous
    have hφcZ : Continuous (fun x => W x - Z x) := hWcont.sub hZc
    have hφcB : Continuous (fun x => W x - upperBarrier κ M x) :=
      hWcont.sub (upperBarrier_continuous κ M)
    have hBC2B :
        ∀ x₀, IsMaxOn (fun x => W x - upperBarrier κ M x) Set.univ x₀ →
          ContDiffAt ℝ 2 (upperBarrier κ M) x₀ :=
      upperBarrier_BC2_atMax_dischargeable hκ hMpos hWdiff
    exact ⟨W, R, C_chem, LaZ, LbZ, LaB, LbB,
      ⟨hgr, hcf, hRc, hRb, hRhi, hRlo, hRanti.antitone, hRint, hstepop, hnonneg,
        hstepeq, hCnn, hCB,
        hZsuper, fun x => le_refl (Z x),
        hφcZ, htails.hbotZ, htails.hLaZ, htails.htopZ, htails.hLbZ, hBC2Z, hrangeZ,
        hSuper, hZB,
        hφcB, htails.hbotB, htails.hLaB, htails.htopB, htails.hLbB, hBC2B, hrangeB⟩,
      hanti, hchemZ, hchemB⟩

/-! ## 5. The trap-level residual + chaining to `b1_chiNeg_existence`

`rotheFloorResidual_of_trap` specializes `rotheFloorResidual_of_core` to a trapped
`u` by supplying the super-barrier field `hSuper` from the committed
`whole_line_super_barrier` (under its regime hypotheses).  The genuinely-deep
whole-line Green data is supplied by the carried `hcore` producer (the
`produceCore` field). -/

/-- **`rotheFloorResidual_of_trap` — the B1 floor residual for every trapped `u`,
modulo ONLY the genuinely-deep whole-line Green core.**  The super-barrier field
is discharged from `whole_line_super_barrier`; the deep Green data is carried as
`hcore`. -/
def rotheFloorResidual_of_trap
    (p : CMParams) {c lam M κ Λ : ℝ} (u : ℝ → ℝ)
    (hlam : 0 < lam) (hM : 0 ≤ M)
    -- the `whole_line_super_barrier` regime hypotheses:
    (hχ : p.χ ≤ 0) (hα : p.α ≤ p.m + p.γ - 1)
    (hκ : 0 < κ) (hκ1 : κ < 1) (hγκ : p.γ * κ < 1) (hmκ : κ * p.m ≤ 1)
    (hM1 : 1 ≤ M)
    (hMbound :
      |p.χ| * ((1 + p.m * p.γ * κ ^ 2) / (1 - p.γ ^ 2 * κ ^ 2)) *
        M ^ (p.m + p.γ - p.α - 1) ≤ 1)
    (hc : c = κ + κ⁻¹)
    (hsrc : ∀ x, M ≤ Real.exp (-κ * x) →
        frozenElliptic p u x ≤ (u x) ^ p.γ)
    (hmono : InMonotoneWaveTrapSet κ M u)
    -- the genuinely-deep whole-line Green core (carried, NOT synthesizable from
    -- committed bricks for arbitrary `u`):
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
          (RotheStepAntitoneData p c lam M C_chem u Z W ×'
          ((∀ x₀, IsMaxOn (fun x => W x - Z x) Set.univ x₀ →
              RotheStepChemData p u W Z C_chem x₀) ×'
            (∀ x₀, IsMaxOn (fun x => W x - upperBarrier κ M x) Set.univ x₀ →
              RotheStepChemData p u W (upperBarrier κ M) C_chem x₀)))) :
    RotheFloorResidual p c lam M κ Λ u :=
  rotheFloorResidual_of_core
    { hlam := hlam
      hM := hM
      hSuper :=
        whole_line_super_barrier hχ hα hκ hκ1 hγκ hmκ hM1 hMbound hc hsrc hmono
      produceCore := hcore }

/-! ## 6. B1 χ≤0 existence from the deep core

`b1_chiNeg_existence_residualCore` chains
`rotheFloorResidual_of_core → b1_chiNeg_existence_unconditional`: it carries the
genuinely-deep whole-line Green data as the trapped-profile core `hcoreTrap` and
otherwise carries EXACTLY what `b1_chiNeg_existence_unconditional` carries.

The super-barrier field is now part of the core as `RotheFloorResidualCore.hSuper`
— for the actual frozen profiles it is DISCHARGED via `whole_line_super_barrier`
(see `rotheFloorResidual_of_trap`); here it is threaded uniformly so the chain is a
faithful repackaging.  The remaining carried inputs are:

  * the G1 abstract Schauder principle `hprinciple`;
  * the committed profile lemmas `hGreen`/`hpos`/`hbdd`/`hlim_neg`/`hlim_pos`;
  * the continuous-dependence inputs `hstep`/`htail`;
  * the scalar/Lipschitz side conditions + `hVbound`;
  * the deep Green core `hcoreTrap` (whose `hSuper` field is dischargeable from
    `whole_line_super_barrier` for every trapped profile). -/
theorem b1_chiNeg_existence_residualCore
    (p : CMParams) (c lam M Bv κ Λ : ℝ)
    (hc0 : 0 < c) (hlam : 0 < lam) (hM : 0 ≤ M) (hBv : 0 ≤ Bv)
    (hκ0 : 0 ≤ κ) (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    -- the genuinely-deep whole-line Green core, for every trapped profile `v`
    -- (its `hSuper` field is dischargeable via `whole_line_super_barrier` for
    -- every trapped profile — see `rotheFloorResidual_of_trap`):
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

/-- **B1 χ≤0 existence from the slim residual core.**
Compared with `b1_chiNeg_existence_residualClean`, this version removes from the
per-profile core every field that the builder can supply from committed/trivial
facts: the base super-barrier, the input descent supersolution, the two order
fields, both continuity fields, and the at-max `C²` field for `Ū`.

The remaining `hstep`/`htail` hypotheses are exactly the step-selection
continuous-dependence and uniform Dini-tail gaps isolated in `WaveRotheDep`. -/
theorem b1_chiNeg_existence_residualClean_of_trap_super
    (p : CMParams) (c lam M Bv κ Λ : ℝ)
    (hc0 : 0 < c) (hlam : 0 < lam) (hMpos : 0 < M) (hBv : 0 ≤ Bv)
    (hκpos : 0 < κ) (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hSuperTrap : ∀ v, InMonotoneWaveTrapSet κ M v →
      ∀ x, frozenWaveOperator p c v (upperBarrier κ M) x ≤ 0)
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
              (hSuperTrap v hv) hκpos hMpos (hcoreTrap v hv))))
        hκpos.le hMpos.le)
    (htail : RotheTailUniform p c lam M κ Λ
        (rotheStepProducer_of_floor
          (fun v hv => rotheStepFloor_of_residual
            (rotheFloorResidual_of_slimCore
              (hSuperTrap v hv) hκpos hMpos (hcoreTrap v hv))))
        hκpos.le hMpos.le)
    (hprinciple : LocalUniformSchauderFixedPointPrinciple (InMonotoneWaveTrapSet κ M))
    (hGreen : ∀ U, InMonotoneWaveTrapSet κ M U →
        rotheLimit
          ((rotheSeqFromTrap p c lam M κ Λ
            (rotheStepProducer_of_floor
              (fun v hv => rotheStepFloor_of_residual
                (rotheFloorResidual_of_slimCore
                  (hSuperTrap v hv) hκpos hMpos (hcoreTrap v hv))))
            hκpos.le hMpos.le) U) = U →
          GreenIdentity p c lam U)
    (hpos : ∀ U, InMonotoneWaveTrapSet κ M U → (∀ x, 0 < U x))
    (hbdd : ∀ U, InMonotoneWaveTrapSet κ M U → IsCUnifBdd U)
    (hlim_neg : ∀ U, InMonotoneWaveTrapSet κ M U → Tendsto U atBot (𝓝 1))
    (hlim_pos : ∀ U, InMonotoneWaveTrapSet κ M U → Tendsto U atTop (𝓝 0)) :
    ∃ U, InMonotoneWaveTrapSet κ M U ∧ FrozenStationaryWaveProfile p c U :=
  b1_chiNeg_existence_unconditional p c lam M Bv κ Λ
    hc0 hlam hMpos.le hBv hκpos.le hΛ0 hΛM
    (fun v hv => rotheFloorResidual_of_slimCore
      (hSuperTrap v hv) hκpos hMpos (hcoreTrap v hv))
    hbarLip hŪbdd hVbound hstep htail hprinciple hGreen hpos hbdd hlim_neg hlim_pos

/-- **B1 χ≤0 existence from the slim residual core, with `Ū` super-barrier
discharged on trapped profiles.**

This is the χ≤0 wrapper around
`b1_chiNeg_existence_residualClean_of_trap_super`: it supplies the required
trap-indexed super-barrier from the committed `whole_line_super_barrier`.
The remaining `hstep`/`htail` hypotheses are still the precise selection and
uniform-tail gaps isolated in `WaveRotheDep`. -/
theorem b1_chiNeg_existence_residualClean
    (p : CMParams) (c lam M Bv κ Λ : ℝ)
    (hc0 : 0 < c) (hlam : 0 < lam) (hMpos : 0 < M) (hBv : 0 ≤ Bv)
    (hκpos : 0 < κ) (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hχ : p.χ ≤ 0) (hα : p.α ≤ p.m + p.γ - 1)
    (hκ1 : κ < 1) (hγκ : p.γ * κ < 1) (hmκ : κ * p.m ≤ 1)
    (hM1 : 1 ≤ M)
    (hMbound :
      |p.χ| * ((1 + p.m * p.γ * κ ^ 2) / (1 - p.γ ^ 2 * κ ^ 2)) *
        M ^ (p.m + p.γ - p.α - 1) ≤ 1)
    (hc : c = κ + κ⁻¹)
    (hsrcTrap : ∀ v, InMonotoneWaveTrapSet κ M v →
      ∀ x, M ≤ Real.exp (-κ * x) → frozenElliptic p v x ≤ (v x) ^ p.γ)
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
              (whole_line_super_barrier hχ hα hκpos hκ1 hγκ hmκ hM1 hMbound
                hc (hsrcTrap v hv) hv)
              hκpos hMpos (hcoreTrap v hv))))
        hκpos.le hMpos.le)
    (htail : RotheTailUniform p c lam M κ Λ
        (rotheStepProducer_of_floor
          (fun v hv => rotheStepFloor_of_residual
            (rotheFloorResidual_of_slimCore
              (whole_line_super_barrier hχ hα hκpos hκ1 hγκ hmκ hM1 hMbound
                hc (hsrcTrap v hv) hv)
              hκpos hMpos (hcoreTrap v hv))))
        hκpos.le hMpos.le)
    (hprinciple : LocalUniformSchauderFixedPointPrinciple (InMonotoneWaveTrapSet κ M))
    (hGreen : ∀ U, InMonotoneWaveTrapSet κ M U →
        rotheLimit
          ((rotheSeqFromTrap p c lam M κ Λ
            (rotheStepProducer_of_floor
              (fun v hv => rotheStepFloor_of_residual
                (rotheFloorResidual_of_slimCore
                  (whole_line_super_barrier hχ hα hκpos hκ1 hγκ hmκ hM1 hMbound
                    hc (hsrcTrap v hv) hv)
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
    (fun v hv =>
      whole_line_super_barrier hχ hα hκpos hκ1 hγκ hmκ hM1 hMbound hc
        (hsrcTrap v hv) hv)
    hcoreTrap hbarLip hŪbdd hVbound hstep htail hprinciple hGreen hpos hbdd
    hlim_neg hlim_pos

/-! ## 7. Axiom audit -/

section AxiomAudit
#print axioms rotheResidual_gWeight_integrableOn_Ioi_of_bounded
#print axioms rotheResidual_gWeight_integrableOn_Iic_of_bounded
#print axioms greenKernel_translated_integrable_of_bounded
#print axioms rotheSlimSourceAntitone_const
#print axioms bounded_continuous_source_not_forces_antitone
#print axioms rotheSlimEndpointAsymptotics_barrier
#print axioms upperBarrier_contDiffAt_two_of_ne_interface
#print axioms maxSub_upperBarrier_ne_interface
#print axioms upperBarrier_BC2_atMax_dischargeable
#print axioms rotheFloorResidual_of_core
#print axioms rotheFloorResidual_of_slimCore
#print axioms rotheFloorResidual_of_trap
#print axioms b1_chiNeg_existence_residualCore
#print axioms b1_chiNeg_existence_residualClean_of_trap_super
#print axioms b1_chiNeg_existence_residualClean
end AxiomAudit

end ShenWork.Paper1
