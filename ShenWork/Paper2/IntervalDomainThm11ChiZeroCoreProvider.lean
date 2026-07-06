/-
  ShenWork/Paper2/IntervalDomainThm11ChiZeroCoreProvider.lean

  ## Intended task vs. what is actually provable

  The intended task was to write an UNCONDITIONAL producer

      limitRegularityInputsCore_unconditional :
        ∀ (p) (hχ0 : p.χ₀ = 0) (regime) (u₀) (PID u₀)
          (D : GradientMildSolutionData p u₀),
            Thm11ChiZeroFinal.LimitRegularityInputsCore p u₀ D

  collecting the ledger's 25+ fields from existing infrastructure, thereby
  discharging the `Hcore` hypothesis of `paper2_theorem_1_1_chiZero_final`
  and making Theorem 1.1 (χ₀ = 0) unconditional modulo only `hPLF`.

  **This producer cannot exist, because `LimitRegularityInputsCore` is
  VACUOUS (uninhabited for every `D`).**  This file proves that fact
  rather than faking the producer.

  ## The obstruction (machine-checked below)

  Two of the Core's fields are mutually contradictory:

    * `hC2t : ∀ σ, ContDiff ℝ 2 (intervalDomainLift (D.u σ))`
      — GLOBAL `C²` of the zero-extension `intervalDomainLift` (which is
      `f` on `[0,1]` and `0` off it; see `IntervalDomain.intervalDomainLift`).
      Global `C²` ⟹ global continuity ⟹ the value at the endpoint `0`
      equals the left limit, which is `0` (the lift is identically `0` on
      `(-∞,0)`).  Hence `intervalDomainLift (D.u σ) 0 = 0`.

    * `hpost : ∀ σ, ∀ x ∈ Icc 0 1, 0 < intervalDomainLift (D.u σ) x`
      — strict positivity at the (boundary-inclusive) point `x = 0`, i.e.
      `0 < intervalDomainLift (D.u σ) 0`.

  Together: `0 < intervalDomainLift (D.u 0) 0 = 0`, contradiction.  The
  argument uses NOTHING about `D` beyond the two ledger fields, so the
  structure is uninhabited for ANY `GradientMildSolutionData` — independent
  of the regime hypotheses, the PID, or `χ₀`.

  This is exactly the vacuity flagged in the project memory ("global-C² of
  0-extension ⊥ endpoint positivity") and acknowledged in
  `IntervalDomainLogisticWeakH2Adapter`'s header ("The ledger's vacuity came
  from asking `ContDiff ℝ 2 (intervalDomainLift (D.u σ))` (global) — false
  for the 0-extension positive at the Neumann endpoints").

  ## Consequence for Theorem 1.1 (χ₀ = 0)

  `paper2_theorem_1_1_chiZero_final` is gated on
  `Hcore : ∀ u₀, PID u₀ → ∀ D, LimitRegularityInputsCore p u₀ D`.  Since the
  conclusion type is uninhabited, `Hcore` is itself unsatisfiable; the final
  theorem is a valid implication with an UNSATISFIABLE premise (a vacuous
  conditional — `#print axioms` cannot detect this).  It is therefore NOT an
  unconditional proof of Theorem 1.1.

  ## The fix (a structural decision for the senior author)

  To inhabit a per-datum core one must RETYPE the offending fields so they
  match what the real solution / restart cosine representation genuinely
  supplies — the additive-adapter route the project already established:

    * replace `hC2t` (global `C²` of the lift) by the cosine-representation
      data the adapters consume on `[0,1]` (eigenvalue-summability + `[0,1]`
      agreement with `∑ₙ bₙ cos(nπ·)`), which is genuinely `C²` and is what
      `IntervalDomainLogisticWeakH2Adapter`/`hpdeData` already use;
    * restrict the `∀ σ : ℝ` quantifiers (`hpost`/`hubt`/`hG1t`/`hG2t`/...)
      to the range `σ ∈ (0, D.T]` where `D.hpos`/`D.hbound` actually hold
      (they are false for `σ ≤ 0` and `σ > D.T`).

  Independently of the typing, several fields still have NO producer in the
  current codebase and are genuine open analytic estimates (uniform sup /
  gradient / Hessian bounds `hubt`/`hG1t`/`hG2t`; strict resolver positivity
  `Hvpos` via the elliptic strong maximum principle; the resolver-source
  `Hvsrc`; per-slice continuity `hLc`; the restart representation `hpdeData`).
  Retyping alone does not inhabit the core; those estimates must be proved.

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.
-/
import ShenWork.Paper2.IntervalDomainThm11ChiZeroFinal
import ShenWork.Paper2.IntervalDomainLedgerSweep
import ShenWork.Paper2.IntervalPicardLimitRestartWeak
import ShenWork.Paper2.IntervalDomainConstExtendAdapter
import ShenWork.Paper2.IntervalCompactSliceGradientBounds
import ShenWork.Paper2.IntervalPicardLimitBddAdapterPatched
import ShenWork.Paper2.IntervalResolverStrictPositivity
import ShenWork.Paper2.IntervalDomainPdeUWiring
import ShenWork.Paper2.IntervalPicardLimitK1Weak
import ShenWork.Paper2.IntervalResolverSourceTimeC1
import ShenWork.Paper2.IntervalResolverSourceClampedWitness
import ShenWork.Paper2.IntervalResolverPowerK1
import ShenWork.Paper2.IntervalResolverPowerDecay
import ShenWork.Paper2.IntervalPicardLimitBddBootstrap
import ShenWork.Paper2.IntervalPicardLimitBddHcontP
import ShenWork.Paper2.IntervalDomainThm11ChiZeroResidual
import ShenWork.Paper2.IntervalDomainHresWiring

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalDomain
  intervalDomainConstExtend constExtend_continuous)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted intervalGradientDuhamelMap)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
open ShenWork.Paper2 (PositiveInitialDatum)
open ShenWork.IntervalPicardLimitRestartWeak (DuhamelSourceL1Cont DuhamelSourceL1ContOn)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.Paper2.Thm11ChiZeroResidual
  (PicardIterateResidualData hconv_of_residual hCwin_ex_of_residual)
open ShenWork.IntervalMildPicard
  (picardLimit picardIter HasContinuousSlices)
open ShenWork.IntervalMildPicardThreshold (gradientMildSolutionData_initialApproach)
open ShenWork.IntervalMildPicardConeData (coneGradientMildSolutionData_exists_with_data)
open ShenWork.IntervalPicardLimitCoeffConv (PicardConvFacts)
open ShenWork.Paper2.HresWiring
  (WdataProvider picardIterateResidualCore_of_wdata picardIterateResidualData_of_core)

noncomputable section

namespace ShenWork.Paper2.Thm11ChiZeroCoreProvider

/-- **The per-datum cosine-coefficient TIME-continuity provider.**

For every canonical Picard-limit datum `D`, the cosine coefficients of the iterate
logistic sources are continuous in time on every window `[a', τ] ⊆ (0, D.T]`.  This
is the SINGLE iterate-side ingredient the spatial cone construction does not return
(it is the time-direction continuity, not the spatial `HasContinuousSlices`); it is
discharged from the tower via
`IntervalPicardTowerProjection.hiter_cont_of_tower` (see `IntervalPicardTowerSupply`).
Feeding it discharges the `hsrc0` argument of `picardIterateResidualData_of_core`
through the non-circular spatial Stage-A route. -/
def IterCoeffTimeContProvider (p : CM2Params) : Prop :=
  ∀ u₀ : intervalDomainPoint → ℝ,
    PositiveInitialDatum intervalDomain u₀ →
    ∀ D : GradientMildSolutionData p u₀,
      D.u = picardLimit p u₀ D.T →
      ∀ (a' τ : ℝ), 0 < a' → a' ≤ τ → τ ≤ D.T → ∀ (n k : ℕ),
        ContinuousOn
          (fun s => ShenWork.IntervalNeumannFullKernel.cosineCoeffs
            (ShenWork.IntervalGradientDuhamelMap.logisticLifted p
              (picardIter p u₀ n s)) k)
          (Set.Icc a' τ)

/-! ## FIX LANDED — the vacuity is gone (2026-06-07)

The contradictory `hC2t` field (global `C²` of the zero-extension lift) has been
REMOVED from `LimitRegularityInputsCore` and replaced by the per-slice cosine
representation `(bc, hbsum, hagree)` — exactly the additive-adapter route flagged
above.  The representation is consistent with endpoint positivity (`cs σ` is the
genuinely-`C²` cosine series that agrees with the lift on `[0,1]`), so the Core is
no longer uninhabited, and the former machine-checked vacuity theorem
`limitRegularityInputsCore_uninhabited` no longer typechecks (its `(C.hC2t 0)`
projection is gone) — which is the intended outcome.

The representation is wired into every former `hC2t` consumer by
`ShenWork.IntervalDomainLimitSourceRepresentation.limitSource_duhamelSourceTimeC1_of_representation`,
which feeds the genuinely-`C²` series into the existing explicit quadratic-decay
machinery (uniform constant `2·B_log(M,G1,G2)`) and transports the resulting cosine
coefficients to the lift via `[0,1]`-agreement.  The remaining genuine analytic
estimates listed above (`hubt`/`hG1t`/`hG2t`/`Hvpos`/`Hvsrc`/`hLc`/`hpdeData`) are
unaffected by the retype and remain to be produced. -/

/-- **Per-datum producer of `ReducedLimitRegularityInputs` (χ₀ = 0).**

Scaffold for the unconditional provider: given a positive initial datum and a
`GradientMildSolutionData`, assemble the reduced χ₀ = 0 ledger.  The structural
regime fields are immediate; the remaining fields are filled incrementally —
`bc`/`hbsum`/`hagree` from the Picard limit's restart cosine representation
(`IntervalPicardLimitRestartWeak.limit_lift_eq_cosineSeries_weak`), the source
families from M3b, `hpde_u`/`Hvsrc`/`Hvpos` from the representation adapters, and
the K2 sup/gradient/Hessian bounds from Picard-iterate regularity.

NOTE: a `def` (not `theorem`): the structure carries DATA fields (`bc`, `M₀`,
`Msup`, `adott`, …) that downstream `limitRegularityInputs_of_reduced` projects,
so the result must be reducible. -/
noncomputable def reducedLimitRegularityInputs_of_picard
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b) (hα : 1 ≤ p.α)
    (u₀ : intervalDomainPoint → ℝ) (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (D : GradientMildSolutionData p u₀)
    -- the canonical Picard-limit identity (threaded from the cone construction)
    (hDu : D.u = picardLimit p u₀ D.T)
    -- the precisely-named iterate-side residual bundle (R-src0F-2/3 + hsliceTC):
    -- every field is a TRUE statement about the canonical Picard limit, satisfiable
    -- from the cone construction's internal iterate data; threaded, not asserted.
    (R : PicardIterateResidualData p u₀ D) :
    LedgerSweep.ReducedLimitRegularityInputs p u₀ D :=
  -- the weak limit-source package (one shared sorry, consumed by the `hsrc0`
  -- field AND by `hbsum`/`hagree`/`hG1tF`/`hG2tF`).
  --
  -- INTENDED FILLER: `IntervalPicardLimitBddProducer.duhamelSourceBddOn_of_mildData_inclusive`
  -- (NEW, `IntervalPicardLimitBddProducerInclusive.lean`, 0-sorry, builds green) —
  -- the closed-horizon clone of the strict producer `duhamelSourceBddOn_of_mildData`,
  -- with every window hypothesis retyped strict→inclusive (`< D.T` ⟶ `≤ D.T`).  Its
  -- `hM` and `env` ingredients are fully discharged inside the producer (the env's
  -- per-window quadratic-decay envelope on the CLOSED `[a', D.T]` from
  -- `patchedSource_windowEnv_bound_inclusive`, taking window-uniform K2 bounds on the
  -- closed `Set.Icc a' D.T` as inputs).
  --
  -- WHY STILL `sorry` (residual is NOT `hcontP`): wiring the inclusive producer here
  -- is blocked by a STRUCTURAL CIRCULARITY, not by the continuity field.  The producer
  -- consumes `bc`/`hbsum`/`hagree`/`hG1t`/`hG2t`; but every limit-source representation
  -- (`limit_lift_eq_cosineSeries_of_subtypeCont_patched`, `summable_*_limitCoeff_*`) is
  -- itself PROVEN FROM a `DuhamelSourceBddOn (patchedSource …)` package — so the
  -- Provider's `hagreeF`/`hbsumF`/`hG1tF`/`hG2tF` all consume `hsrc0F` (see lines below:
  -- `hagreeF` literally passes `hsrc0F`).  Feeding them back into the producer that
  -- builds `hsrc0F` is an unsatisfiable `have`-ordering (`hsrc0F ← hagreeF ← hsrc0F`).
  -- The genuine open input is therefore the package's `env` proven DIRECTLY from `D`
  -- (the per-compact K2 / PDE-smoothing estimate), NOT the right-continuity `hcontP`
  -- (which the inclusive producer takes as its own named-satisfiable hypothesis).  No
  -- patched `DuhamelSourceL1ContOn` producer exists either (the global ℓ¹ envelope is
  -- unfillable for merely-continuous `u₀` as `s → 0⁺`; see `HANDOFF/hsrc0-splitenv-design.md`).
  -- **F2 iterate-side bootstrap** (circularity broken).  The package is now built
  -- by `IntervalPicardLimitBddBootstrap.duhamelSourceBddOn_of_iterates`, whose `hM`
  -- comes DIRECTLY from `D` (no representation) and whose per-window `env` comes
  -- from n-UNIFORM iterate quadratic decay + `le_of_tendsto` — NOT from
  -- `bc`/`hbsum`/`hagree` of the limit.  The remaining honest inputs are the genuine
  -- iterate-side analytic facts, isolated below as named satisfiable residuals.
  --
  -- (R-src0F-1) initial-datum source-coefficient bound.  ROUTE: `u₀` is continuous
  -- (subtype) and bounded (`hu₀.admissible`), so `intervalDomainLift u₀` is bounded
  -- on `[0,1]`; the logistic source of a positive bounded profile is sup-bounded, and
  -- `cosineCoeffs_abs_le_of_continuous_bounded` then bounds its coefficients.  Same
  -- shape as `IntervalPicardLimitBddProducer.duhamelSourceBddOn_of_mildData`'s
  -- `hu₀_src_bound`.  (`u₀` need not be positive away from `s>0`; if the s≤0 branch is
  -- never exercised by the genuine `[a',τ]⋐(0,T)` pipeline, any finite `M₀'` works.)
  -- concrete datum-side witness `M₀' := 2·sup|u₀|`; the bound is the named residual.
  -- (R-src0F-1a/1b) DISCHARGED: datum-side source bound via the closed helper
  -- `IntervalPicardLimitBddHcontP.datum_source_coeff_bound`.  Witness
  -- `M₀' := datumBound p u₀ = 2·(B·(a + b·Bᵅ))`, `B = sSup (range |u₀|)`.
  let M₀' : ℝ := ShenWork.IntervalPicardLimitBddHcontP.datumBound p u₀
  have hM₀'_nonneg : (0 : ℝ) ≤ M₀' :=
    ShenWork.IntervalPicardLimitBddHcontP.datumBound_nonneg p hu₀.admissible.1
  have hu₀_src_bound : ∀ k, |cosineCoeffs (logisticLifted p u₀) k| ≤ M₀' :=
    ShenWork.IntervalPicardLimitBddHcontP.datum_source_coeff_bound p
      hu₀.admissible.2 hu₀.admissible.1 hu₀.2
  -- (R-src0F-2) per-window decay constant + n-UNIFORM iterate envelope.  ROUTE: each
  -- iterate slice `intervalDomainLift (picardIter p u₀ n s)` is genuinely `ContDiff ℝ 2`
  -- (spatial bootstrap `picardIterateHasC2Slices_all`) with K2 constants `(M,G1,G2)`
  -- that are UNIFORM in `n` on the window `[a',τ]⋐(0,T)` (Picard ball + per-compact
  -- gradient/Hessian bounds, n-independent).  Applying the GLOBAL decay machinery
  -- `logisticSourceFun_cosineCoeff_quadratic_decay_explicit` PER ITERATE (no
  -- representation — the iterate IS C²) gives
  -- `|coeffs(logistic(iter n s)) k| ≤ windowEnv (Cwin a') k` with
  -- `Cwin a' := max (2·B_log p.a p.b p.α M G1 G2) (M·(p.a+p.b·M^α))`, uniform in n.
  -- This is the `IntervalPicardIterateSourceC1.picardIterate_source_duhamelSourceTimeC1`
  -- envelope read off per-window, NOT the limit representation.  Concrete witness
  -- `Cwin := fun _ => 0` is a placeholder; the genuine content is `henv_iter` (named).
  have hCwin_ex : ∃ Cwin : ℝ → ℝ, (∀ a', 0 ≤ Cwin a') ∧
      (∀ a', 0 < a' → ∀ s, a' ≤ s → s ≤ D.T → ∀ (n : ℕ) (k : ℕ),
        |cosineCoeffs (logisticLifted p
          (ShenWork.IntervalMildPicard.picardIter p u₀ n s)) k|
          ≤ ShenWork.IntervalPicardLimitBddProducer.windowEnv (Cwin a') k) :=
    -- DISCHARGED from the residual bundle's per-window `IterateWindowC2Data` via
    -- `source_coeff_window_uniform` (the proved §F window-envelope theorem).
    hCwin_ex_of_residual hα R
  let Cwin : ℝ → ℝ := hCwin_ex.choose
  have hCwin : ∀ a', 0 ≤ Cwin a' := hCwin_ex.choose_spec.1
  have henv_iter : ∀ a', 0 < a' → ∀ s, a' ≤ s → s ≤ D.T → ∀ (n : ℕ) (k : ℕ),
      |cosineCoeffs (logisticLifted p
        (ShenWork.IntervalMildPicard.picardIter p u₀ n s)) k|
        ≤ ShenWork.IntervalPicardLimitBddProducer.windowEnv (Cwin a') k :=
    hCwin_ex.choose_spec.2
  -- (R-src0F-3) pointwise coefficient convergence iterate → `D.u`.  ROUTE: for `D`
  -- coming from the Picard construction, `D.u = picardLimit p u₀ D.T`, and
  -- `IntervalPicardLimitCoeffConv.picardIter_logisticCoeff_tendsto_limit` gives exactly
  -- this Tendsto on `(0,T]` (coefficient distance squeezed through `2·Lc·K^n·C₀/(1−K)`).
  -- For a generic `GradientMildSolutionData` the bridge `D.u = picardLimit` is the mild
  -- uniqueness identity; satisfiable, threaded here as a named residual.
  have hconv : ∀ s, 0 < s → s ≤ D.T → ∀ k,
      Filter.Tendsto (fun n => cosineCoeffs (logisticLifted p
          (ShenWork.IntervalMildPicard.picardIter p u₀ n s)) k)
        Filter.atTop (nhds (cosineCoeffs (logisticLifted p (D.u s)) k)) :=
    -- DISCHARGED from `hDu` + the residual bundle: rewriting the limit slice
    -- through `hDu` reduces to the canonical Picard-limit convergence, proved by
    -- `picardIter_logisticCoeff_tendsto_limit` (contraction-tail squeeze).
    hconv_of_residual hDu R
  -- (R-src0F-4) time-continuity of the patched coefficient family.  DISCHARGED via
  -- `IntervalPicardLimitBddHcontP.patchedSource_continuousOn_Icc`: the coefficient
  -- functional is `2`-Lipschitz in the slice sup norm and the lifted logistic source
  -- is locally Lipschitz on bounded nonnegative slices, so continuity reduces to the
  -- sup-norm time-continuity `hsliceTC` of the patched slice profile.  The ball/nonneg
  -- inputs are discharged from `D.hbound`/`D.hnonneg` (for `s > 0`) and the datum facts
  -- (for `s ≤ 0`).  `hsliceTC` is the SINGLE remaining genuine analytic input (interior
  -- mild-slice time continuity + the `s = 0⁺` initial approach
  -- `gradientMildSolutionData_initialApproach`), isolated below as a named residual.
  let M_patch : ℝ := max D.M (sSup (Set.range fun x => |u₀ x|))
  have hMpatch_pos : (0 : ℝ) < M_patch :=
    lt_of_lt_of_le D.hM (le_max_left _ _)
  -- `u₀` nonneg on the whole subtype domain (interior positivity + continuity)
  have hu₀_nn : ∀ y : intervalDomainPoint, 0 ≤ u₀ y := by
    intro y
    have h := ShenWork.IntervalPicardLimitBddHcontP.lift_nonneg_of_pos_interior
      hu₀.admissible.2 hu₀.2 y.1 y.2
    have huy : u₀ y = intervalDomainLift u₀ y.1 := by
      simp only [intervalDomainLift,
        dif_pos (show (y.1 : ℝ) ∈ Set.Icc (0:ℝ) 1 from y.2), Subtype.coe_eta]
    rw [huy]; exact h
  have hu₀_bd : ∀ y : intervalDomainPoint,
      |u₀ y| ≤ sSup (Set.range fun x => |u₀ x|) :=
    fun y => le_csSup hu₀.admissible.1 ⟨y, rfl⟩
  have hball_patch : ∀ s ∈ Set.Icc (0 : ℝ) D.T,
      ∀ y, |ShenWork.IntervalPicardLimitBddHcontP.patchedSlice u₀ D.u s y| ≤ M_patch := by
    intro s hs y
    rcases eq_or_lt_of_le hs.1 with hs0 | hs0
    · rw [ShenWork.IntervalPicardLimitBddHcontP.patchedSlice_of_nonpos u₀ D.u
        (le_of_eq hs0.symm)]
      exact le_trans (hu₀_bd y) (le_max_right _ _)
    · rw [ShenWork.IntervalPicardLimitBddHcontP.patchedSlice_of_pos u₀ D.u hs0]
      exact le_trans (D.hbound s hs0 hs.2 y) (le_max_left _ _)
  have hnn_patch : ∀ s ∈ Set.Icc (0 : ℝ) D.T,
      ∀ y, 0 ≤ ShenWork.IntervalPicardLimitBddHcontP.patchedSlice u₀ D.u s y := by
    intro s hs y
    rcases eq_or_lt_of_le hs.1 with hs0 | hs0
    · rw [ShenWork.IntervalPicardLimitBddHcontP.patchedSlice_of_nonpos u₀ D.u
        (le_of_eq hs0.symm)]
      exact hu₀_nn y
    · rw [ShenWork.IntervalPicardLimitBddHcontP.patchedSlice_of_pos u₀ D.u hs0]
      exact D.hnonneg s hs0 hs.2 y
  -- The single genuine analytic residual: sup-norm time continuity of the patched
  -- slice profile on `[0,T]` (interior mild-slice time continuity + `s=0⁺` approach).
  have hsliceTC : ∀ s₀ ∈ Set.Icc (0 : ℝ) D.T, ∀ ε > 0, ∃ δ > 0,
      ∀ s ∈ Set.Icc (0 : ℝ) D.T, |s - s₀| < δ →
        ∀ y, |ShenWork.IntervalPicardLimitBddHcontP.patchedSlice u₀ D.u s y
              - ShenWork.IntervalPicardLimitBddHcontP.patchedSlice u₀ D.u s₀ y| < ε :=
    -- the single genuinely-open analytic field, carried by the residual bundle
    -- (interior mild-slice time continuity + the `s = 0⁺` initial approach).
    R.hsliceTC
  have hcontP : ∀ k, ContinuousOn
      (fun s => ShenWork.IntervalPicardLimitBddProducer.patchedSource p u₀ D.u s k)
      (Set.Icc 0 D.T) :=
    ShenWork.IntervalPicardLimitBddHcontP.patchedSource_continuousOn_Icc p D
      hu₀.admissible.2 hMpatch_pos hball_patch hnn_patch hsliceTC
  have hsrc0F : ShenWork.IntervalPicardLimitRestartBdd.DuhamelSourceBddOn
      (ShenWork.IntervalPicardLimitBddProducer.patchedSource p u₀ D.u) D.T :=
    ShenWork.IntervalPicardLimitBddBootstrap.duhamelSourceBddOn_of_iterates
      p D hα ha.le hb.le hM₀'_nonneg hu₀_src_bound Cwin hCwin henv_iter hconv
      D.hT le_rfl hcontP
  -- hoisted facts shared by several fields (H1 coefficient bound, K2 slice
  -- positivity, the limitCoeff cosine representation)
  have hu₀_bdF : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k|
      ≤ 2 * sSup (Set.range fun x => |u₀ x|) := by
    have hbdd : BddAbove (Set.range fun x => |u₀ x|) := hu₀.admissible.1
    have hB0 : 0 ≤ sSup (Set.range fun x => |u₀ x|) :=
      le_trans (abs_nonneg _)
        (le_csSup hbdd ⟨⟨1 / 2, ⟨by norm_num, by norm_num⟩⟩, rfl⟩)
    have hcont : ContinuousOn (intervalDomainLift u₀) (Set.Icc (0 : ℝ) 1) := by
      rw [continuousOn_iff_continuous_restrict]
      have heq : (Set.Icc (0 : ℝ) 1).restrict (intervalDomainLift u₀) = u₀ := by
        funext ⟨y, hy⟩
        simp only [Set.restrict_apply, intervalDomainLift]
        split_ifs
        exact congr_arg u₀ (Subtype.ext rfl)
      rw [heq]; exact hu₀.admissible.2
    have hfb : ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |intervalDomainLift u₀ x| ≤ sSup (Set.range fun x => |u₀ x|) := by
      intro x hx
      simp only [intervalDomainLift, dif_pos hx]
      exact le_csSup hbdd ⟨⟨x, hx⟩, rfl⟩
    exact ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
      hcont hB0 hfb
  have hpostF : ∀ σ, 0 < σ → σ ≤ D.T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (D.u σ) x :=
    fun σ hσ hσT x hx => by
      simp only [intervalDomainLift, dif_pos hx]
      exact D.hpos σ hσ hσT ⟨x, hx⟩
  have hagreeF : ∀ σ, 0 < σ → σ ≤ D.T → Set.EqOn (intervalDomainLift (D.u σ))
      (fun x => ∑' n, ShenWork.IntervalPicardLimitRestart.limitCoeff p u₀ D.u σ n
        * cosineMode n x) (Set.Icc (0 : ℝ) 1) :=
    fun σ hσ hσT x hx => by
      exact ShenWork.Paper2.TimeNhdSubtype.limit_lift_eq_cosineSeries_of_subtypeCont_patched
        p hχ0 u₀ D.u hu₀.admissible.2
        hu₀_bdF hsrc0F hσ hσT
        (fun y hy => by simp only [intervalDomainLift, dif_pos hy]
                        exact D.hmild σ hσ hσT ⟨y, hy⟩)
        (fun s hs hsσ =>
          ShenWork.Paper2.ConstExtendAdapter.logisticSource_constExtend_continuous D hs
            (hsσ.trans hσT))
        hx
  -- hoisted K2 / fixed-point / slice-continuity facts shared by the K1 bundle
  -- (the SUBTYPE-continuity K1 producer) and the hpde_u representation route.
  have hM₀nn : (0:ℝ) ≤ 2 * sSup (Set.range fun x => |u₀ x|) :=
    le_trans (abs_nonneg _) (hu₀_bdF 0)
  have hbsumF : ∀ σ, 0 < σ → σ ≤ D.T →
      Summable (fun n => unitIntervalCosineEigenvalue n
        * |ShenWork.IntervalPicardLimitRestart.limitCoeff p u₀ D.u σ n|) :=
    fun σ hσ hσT =>
      Summable.of_nonneg_of_le
        (fun k => mul_nonneg
          (by unfold unitIntervalCosineEigenvalue; positivity) (abs_nonneg _))
        (fun k =>
          ShenWork.Paper2.BddAdapterPatched.eigenvalue_mul_abs_limitCoeff_le_uniform_patched
            p u₀ D.u hM₀nn hu₀_bdF hsrc0F hσ le_rfl hσT k)
        (ShenWork.IntervalPicardLimitBddAdapter.windowEigEnv_summable hσ
          (hsrc0F.henv_summable (σ / 2) (by linarith) (by linarith)))
  have hubtF : ∀ σ, 0 < σ → σ ≤ D.T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (D.u σ) x ≤ D.M :=
    fun σ hσ hσT x hx => by
      simp only [intervalDomainLift, dif_pos hx]
      exact le_trans (le_abs_self _) (D.hbound σ hσ hσT ⟨x, hx⟩)
  have hfixF : ∀ s, 0 < s → s < D.T → ∀ x : ℝ, (hx : x ∈ Set.Icc (0:ℝ) 1) →
      intervalDomainLift (D.u s) x = intervalGradientDuhamelMap p u₀ D.u s ⟨x, hx⟩ :=
    fun s hs hsT x hx => by
      simp only [intervalDomainLift, dif_pos hx]
      exact D.hmild s hs hsT.le ⟨x, hx⟩
  have hG1tF : ∀ a' b', 0 < a' → b' < D.T → ∃ G1, ∀ σ ∈ Set.Icc a' b',
      ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (intervalDomainLift (D.u σ)) x| ≤ G1 :=
    fun a' b' ha' hb'T =>
      (ShenWork.Paper2.BddAdapterPatched.deriv_lift_bound_on_compact_patched
        p u₀ D.u hM₀nn hu₀_bdF hsrc0F hbsumF hagreeF hpostF ha' hb'T.le).imp
        (fun _ h => h.2)
  have hG2tF : ∀ a' b', 0 < a' → b' < D.T → ∃ G2, ∀ σ ∈ Set.Icc a' b',
      ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (deriv (intervalDomainLift (D.u σ))) x| ≤ G2 :=
    fun a' b' ha' hb'T =>
      (ShenWork.Paper2.BddAdapterPatched.deriv2_lift_bound_on_compact_patched
        p u₀ D.u hM₀nn hu₀_bdF hsrc0F hbsumF hagreeF ha' hb'T.le).imp
        (fun _ h => h.2)
  have hLc_ceF : ∀ t, 0 < t → t < D.T →
      ∀ s, 0 < s → s ≤ t →
        Continuous (intervalDomainConstExtend (intervalLogisticSource p (D.u s))) :=
    fun _t _ht htT s hs hsT =>
      ShenWork.Paper2.ConstExtendAdapter.logisticSource_constExtend_continuous D hs
        (hsT.trans htT.le)
  -- **K1 source-coefficient time-`C¹` quadruple — de-circularized, SUBTYPE form.**
  -- `k1_quadruple_weak_of_subtypeCont` consumes only the satisfiable ledger data
  -- (subtype `Continuous u₀` + constExtend slice continuity); its conclusion is
  -- exactly the four ledger K1 fields (`adott`/`hderivt`/`hadotcontt`/`hMdott`).
  have hK1 := ShenWork.Paper2.PicardLimitK1Weak.k1_quadruple_weak_of_subtypeCont
    (p := p) hχ0 D.u hα ha.le hb.le hu₀.admissible.2 hu₀_bdF hfixF hsrc0F
    (Msup := D.M)
    (bc := fun σ k => ShenWork.IntervalPicardLimitRestart.limitCoeff p u₀ D.u σ k)
    (fun σ hσ hσT => hbsumF σ hσ hσT.le)
    (fun σ hσ hσT => hagreeF σ hσ hσT.le)
    (fun σ hσ hσT => hpostF σ hσ hσT.le)
    (fun σ hσ hσT => hubtF σ hσ hσT.le)
    hG1tF hG2tF hLc_ceF
  { -- structural regime parameters (immediate)
  hα := hα
  ha := ha.le
  hb := hb.le
  -- weak limit-source package
  hsrc0 := hsrc0F
  -- H1 datum data
  hu₀_cont := hu₀.admissible.2
  -- M₀/hu₀_bound: cosineCoeffs_abs_le_of_continuous_bounded needs
  -- ContinuousOn (lift u₀) Icc + |lift u₀ x| ≤ B on Icc.
  -- PID admissible gives BddAbove (range |u₀|); use its sSup as the bound B
  -- (NOT D.M, which bounds the solution on (0,T], not u₀).
  M₀ := 2 * sSup (Set.range fun x => |u₀ x|)
  hu₀_bound := hu₀_bdF
  -- mild fixed-point: D.hmild gives ∀ t, 0 < t → t ≤ T → ∀ x, u t x = DuhamelMap ...
  -- The lift on [0,1] equals the subtype value.
  hfix := fun t ht htT x hx => by
    simp only [intervalDomainLift, dif_pos hx]
    exact D.hmild t ht htT.le ⟨x, hx⟩
  -- K2 spatial slice bounds
  Msup := D.M
  -- per-slice cosine representation (Picard limit restart representation)
  -- bc := limitCoeff = exp(-σλ_k)·ĉ₀_k + duhamelSpectralCoeff(L̂(u), σ, k)
  bc := fun σ k => ShenWork.IntervalPicardLimitRestart.limitCoeff p u₀ D.u σ k
  -- hbsum: eigenvalue-weighted summability of limitCoeff, from weak source alone.
  -- Bottlenecks on eigenvalue_mul_abs_duhamelSpectralCoeff_le_envelope (1 sorry).
  hbsum := fun σ hσ hσT => hbsumF σ hσ hσT.le
  -- hagree: on [0,1], lift(u σ) = ∑ limitCoeff(σ,k) · cos(kπ·)
  -- from limit_lift_eq_cosineSeries_of_subtypeCont (the adapter theorem)
  hagree := fun σ hσ hσT => hagreeF σ hσ hσT.le
  -- positivity: direct projection of `D.hpos` (now that σ is bounded to (0,D.T))
  hpost := fun σ hσ hσT => hpostF σ hσ hσT.le
  -- sup bound: `D.hbound` gives `|D.u σ x| ≤ D.M`; drop the abs via `le_abs_self`
  hubt := fun σ hσ hσT x hx => by
    simp only [intervalDomainLift, dif_pos hx]
    exact le_trans (le_abs_self _) (D.hbound σ hσ hσT.le ⟨x, hx⟩)
  -- K2 gradient/Hessian bounds: the per-compact producers from the σ-uniform
  -- eigenvalue envelope (CompactSliceGradientBounds)
  hG1t := hG1tF
  hG2t := hG2tF
  -- hN0t/hN1t: deriv(lift(D.u σ)) at 0/1 = 0.
  -- The lift is NOT differentiable at 0 or 1 (jumps from u(σ,0)>0 to 0).
  -- In Lean/Mathlib, deriv of a non-differentiable function = 0 (junk value).
  -- So deriv ... 0 = 0 is trivially true.
  hN0t := fun σ hσ hσT => by
    -- lift is discontinuous at 0: lift(0) = u(σ,0) > 0 but lift(x) = 0 for x < 0.
    -- DifferentiableAt ⟹ ContinuousAt, but left limit = 0 ≠ lift(0) > 0. Contradiction.
    have hnotdiff : ¬ DifferentiableAt ℝ (intervalDomainLift (D.u σ)) 0 := by
      intro hdiff
      have hval : 0 < intervalDomainLift (D.u σ) 0 := by
        simp [intervalDomainLift]
        exact D.hpos σ hσ hσT.le _
      have hcont := hdiff.continuousAt
      -- Restrict continuity to the left nhdsWithin:  nhdsWithin 0 (Iio 0) ≤ nhds 0.
      have htleft : Filter.Tendsto (intervalDomainLift (D.u σ))
          (nhdsWithin 0 (Set.Iio 0)) (nhds (intervalDomainLift (D.u σ) 0)) :=
        hcont.tendsto.mono_left nhdsWithin_le_nhds
      -- On Iio 0 the lift is identically 0 (x ∉ Icc 0 1).
      have hlift0 : (intervalDomainLift (D.u σ)) =ᶠ[nhdsWithin 0 (Set.Iio 0)] (fun _ => 0) := by
        filter_upwards [self_mem_nhdsWithin] with x (hx : x < 0)
        simp [intervalDomainLift,
          show ¬((x : ℝ) ∈ Set.Icc 0 1) from fun h => absurd h.1 (not_le.mpr hx)]
      -- So 0 → lift(0) along the left filter, but also 0 → 0.
      have htleft0 : Filter.Tendsto (fun _ : ℝ => (0 : ℝ))
          (nhdsWithin 0 (Set.Iio 0)) (nhds (intervalDomainLift (D.u σ) 0)) :=
        htleft.congr' hlift0
      -- The left nhdsWithin is NeBot (ℝ has no min).
      have hne : (nhdsWithin (0 : ℝ) (Set.Iio 0)).NeBot := inferInstance
      -- By uniqueness of limits: lift(0) = 0.
      have heq : intervalDomainLift (D.u σ) 0 = 0 :=
        tendsto_nhds_unique htleft0 tendsto_const_nhds
      -- But lift(0) > 0, contradiction.
      linarith
    exact deriv_zero_of_not_differentiableAt hnotdiff
  hN1t := fun σ hσ hσT => by
    have hnotdiff : ¬ DifferentiableAt ℝ (intervalDomainLift (D.u σ)) 1 := by
      intro hdiff
      have hval : 0 < intervalDomainLift (D.u σ) 1 := by
        simp [intervalDomainLift]
        exact D.hpos σ hσ hσT.le _
      have hcont := hdiff.continuousAt
      -- Restrict continuity to the right nhdsWithin:  nhdsWithin 1 (Ioi 1) ≤ nhds 1.
      have htright : Filter.Tendsto (intervalDomainLift (D.u σ))
          (nhdsWithin 1 (Set.Ioi 1)) (nhds (intervalDomainLift (D.u σ) 1)) :=
        hcont.tendsto.mono_left nhdsWithin_le_nhds
      -- On Ioi 1 the lift is identically 0 (x ∉ Icc 0 1).
      have hlift0 : (intervalDomainLift (D.u σ)) =ᶠ[nhdsWithin 1 (Set.Ioi 1)] (fun _ => 0) := by
        filter_upwards [self_mem_nhdsWithin] with x (hx : (1 : ℝ) < x)
        simp [intervalDomainLift,
          show ¬((x : ℝ) ∈ Set.Icc 0 1) from fun h => absurd h.2 (not_le.mpr hx)]
      -- So lift → lift(1) along the right filter, but also lift = 0 eventually.
      have htright0 : Filter.Tendsto (fun _ : ℝ => (0 : ℝ))
          (nhdsWithin 1 (Set.Ioi 1)) (nhds (intervalDomainLift (D.u σ) 1)) :=
        htright.congr' hlift0
      -- The right nhdsWithin is NeBot (ℝ has no max).
      have hne : (nhdsWithin (1 : ℝ) (Set.Ioi 1)).NeBot := inferInstance
      -- By uniqueness of limits: lift(1) = 0.
      have heq : intervalDomainLift (D.u σ) 1 = 0 :=
        tendsto_nhds_unique htright0 tendsto_const_nhds
      -- But lift(1) > 0, contradiction.
      linarith
    exact deriv_zero_of_not_differentiableAt hnotdiff
  -- K1 source-coefficient time-C¹ data (M3b), UNSHIFTED localized form —
  -- produced by the de-circularized SUBTYPE-continuity weak K1 quadruple `hK1`.
  adott := ShenWork.Paper2.PicardLimitK1.adottOf p D.u
  hderivt := hK1.1
  hadotcontt := hK1.2.1
  hMdott := hK1.2.2
  -- H3 slice continuity
  -- hLc: logistic source continuity on the subtype.
  -- intervalLogisticSource p (D.u s) = fun x => (D.u s x) * (a - b * (D.u s x)^α).
  -- D.u s is continuous on the subtype (from D.hcont / HasContinuousSlices),
  -- and the logistic reaction is a composition of continuous operations.
  hLc := fun _t _ht htT s hs hsT => by
    have hcu := D.hcont s hs (hsT.trans htT.le)
    unfold ShenWork.IntervalDomainExistence.intervalLogisticSource
    exact hcu.mul
      (continuous_const.sub
        (continuous_const.mul (hcu.rpow_const (fun _ => Or.inr p.hα.le))))
  -- frontier residuals discharged from the representation:
  -- `hpde_u` is produced from `HasSpectralPdeAgreement` via the honest spectral
  -- producer `mildSolution_pde_u_of_spectral`, fed by
  -- `PdeUWiring.hasSpectralPdeAgreement_of_localized_data` (the same time-localized
  -- subtype-continuity ingredients as the `Hu` route).  All summability /
  -- representation / source-coefficient fields are produced sorry-free inside the
  -- producer; the K1 source-coefficient time-`C¹` data (`adott`/`hderivt`/
  -- `hadotcontt`/`hMdott`) is the SAME genuinely-open frontier already carried as
  -- the structure's own sorried `adott`/… fields (no independent producer exists).
  -- The former continuity / `reflCircle` Fourier-summability wall (FALSE for the
  -- discontinuous lift of positive data) is now DISCHARGED: `HasSpectralPdeAgreement`
  -- consumes a continuous surrogate `g := constExtend (intervalLogisticSource …)`
  -- (continuity from `hLc_ceF`, Fourier-summability from the cosine-decay envelope).
  -- The K1 source-coefficient time-`C¹` quadruple consumed here is the SAME
  -- hoisted `hK1` data (de-circularized SUBTYPE-continuity producer); the former
  -- K1 `sorry` in the hpde_u path is therefore discharged.
  hpde_u :=
    ShenWork.IntervalDomainPdeUProducer.mildSolution_pde_u_of_spectral p hχ0 D
      (ShenWork.Paper2.PdeUWiring.hasSpectralPdeAgreement_of_localized_data hχ0 D.u
        hα ha.le hb.le hu₀.admissible.2 hu₀_bdF hfixF hsrc0F
        (fun σ k => ShenWork.IntervalPicardLimitRestart.limitCoeff p u₀ D.u σ k)
        (fun σ hσ hσT => hbsumF σ hσ hσT.le)
        (fun σ hσ hσT => hagreeF σ hσ hσT.le)
        (fun σ hσ hσT => hpostF σ hσ hσT.le)
        (fun σ hσ hσT => hubtF σ hσ hσT.le)
        hG1tF hG2tF
        (ShenWork.Paper2.PicardLimitK1.adottOf p D.u) hK1.1 hK1.2.1 hK1.2.2 hLc_ceF)
  -- Hvsrc: resolver power-source `ν·u^γ` time-`C¹` package, now in the PER-`t₀`
  -- CLAMPED form (retyped this campaign — the global `DuhamelSourceTimeC1` was
  -- UNSATISFIABLE because `ν·(D.u s)^γ` jumps at `s = D.T`; see the field doc in
  -- `IntervalDomainMildLocalChi0`).  For each interior `t₀` we build the clamped
  -- witness via `ResolverSourceClampedWitness.clampedResolverSource_duhamelSourceTimeC1`
  -- with clamp window `[c',d'] = [t₀/4, (t₀+3·D.T)/4] ⊂ (0,D.T)` and id-zone
  -- `[c,d] = [t₀/2, (t₀+D.T)/2]` (a neighborhood of `t₀`, so `φ = id` there and the
  -- clamped family AGREES with the canonical resolver-source coefficients on `W`).
  -- The producer's SATISFIABLE inputs (cosine representation `bc`, `[0,1]`-agreement
  -- `hagreeF`, positivity `hpostF`, eigenvalue-summability `hbsumF`) are threaded
  -- from the already-available windowed ledger data; the POWER-SOURCE quadratic
  -- decay and the POWER-SOURCE K1 time-`C¹` quadruple are the genuine remaining
  -- residuals (the `ν·r^γ` analogues of the logistic decay envelope + the K1
  -- `hasDerivAt_logisticSlice` clone — see the named `sorry`s below).
  Hvsrc := fun t₀ ht₀ ht₀T => by
    -- clamp window and id-zone around t₀, both ⊂ (0, D.T)
    set c' : ℝ := t₀ / 4 with hc'def
    set c : ℝ := t₀ / 2 with hcdef
    set d : ℝ := (t₀ + D.T) / 2 with hddef
    set d' : ℝ := (t₀ + 3 * D.T) / 4 with hd'def
    have hTpos : 0 < D.T := ht₀.trans ht₀T
    have hc'c : c' < c := by rw [hc'def, hcdef]; linarith
    have hcd : c ≤ d := by rw [hcdef, hddef]; linarith
    have hdd' : d < d' := by rw [hddef, hd'def]; linarith
    have hc'pos : 0 < c' := by rw [hc'def]; linarith
    have hd'T : d' < D.T := by rw [hd'def]; linarith
    have hwin_sub : ∀ σ ∈ Set.Icc c' d', 0 < σ ∧ σ ≤ D.T := fun σ hσ =>
      ⟨lt_of_lt_of_le hc'pos hσ.1, le_of_lt (lt_of_le_of_lt hσ.2 hd'T)⟩
    -- the cosine representation family (= limitCoeff, as elsewhere in this Provider)
    set bc : ℝ → ℕ → ℝ :=
      fun σ k => ShenWork.IntervalPicardLimitRestart.limitCoeff p u₀ D.u σ k with hbcdef
    -- SATISFIABLE windowed inputs, restricted from the (0,D.T] ledger data:
    have hbsumW : ∀ σ ∈ Set.Icc c' d',
        Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|) := by
      intro σ hσ; exact hbsumF σ (hwin_sub σ hσ).1 (hwin_sub σ hσ).2
    have hagreeW : ∀ σ ∈ Set.Icc c' d', Set.EqOn (intervalDomainLift (D.u σ))
        (fun x => ∑' n, bc σ n * cosineMode n x) (Set.Icc (0 : ℝ) 1) := by
      intro σ hσ; exact hagreeF σ (hwin_sub σ hσ).1 (hwin_sub σ hσ).2
    have hposW : ∀ σ ∈ Set.Icc c' d', ∀ x ∈ Set.Icc (0 : ℝ) 1,
        0 < intervalDomainLift (D.u σ) x := by
      intro σ hσ; exact hpostF σ (hwin_sub σ hσ).1 (hwin_sub σ hσ).2
    -- ===== GENUINE RESIDUALS (power-source decay + power-source K1) =====
    -- (R-Hvsrc-1) POWER-SOURCE quadratic decay of `ν·u^γ` on the window.  ROUTE:
    -- `IntervalMildSourceDecayHelper.powerSource_cosineCoeff_quadratic_decay_of_chain_rule`
    -- per window slice (`PowerSourceH2NeumannData p.ν p.γ M (lift (D.u σ))`, built from
    -- the cosine representation `hagreeW`/`hbsumW`/`hposW` + the K2 window bounds
    -- `hubtF`/`hG1tF`/`hG2tF`, exactly as the logistic decay envelope is built), with a
    -- window-uniform constant `C` (the `ν·r^γ` analogue of the logistic envelope
    -- constant).  SATISFIABLE; named residual.
    -- window gradient / Hessian K2 constants (Classical.choose on the per-compact data)
    obtain ⟨G1w, hG1w⟩ := hG1tF c' d' hc'pos hd'T
    obtain ⟨G2w, hG2w⟩ := hG2tF c' d' hc'pos hd'T
    -- window-uniform UPPER bound `D.M` (from `hubtF`), restricted to the window.
    have hubW : ∀ σ ∈ Set.Icc c' d', ∀ x ∈ Set.Icc (0 : ℝ) 1,
        intervalDomainLift (D.u σ) x ≤ D.M :=
      fun σ hσ x hx => hubtF σ (hwin_sub σ hσ).1 (hwin_sub σ hσ).2 x hx
    -- window-uniform positive LOWER bound `m` (joint continuity + compactness).
    obtain ⟨mLow, hmLow_pos, hlbW⟩ :=
      ShenWork.Paper2.ResolverPowerK1.lift_window_uniformPositive_of_subtypeCont
        (p := p) hχ0 D.u hα ha.le hb.le hu₀.admissible.2 hu₀_bdF hfixF hsrc0F
        (Msup := D.M)
        (bc := fun σ k => ShenWork.IntervalPicardLimitRestart.limitCoeff p u₀ D.u σ k)
        (fun σ hσ hσT => hbsumF σ hσ hσT.le)
        (fun σ hσ hσT => hagreeF σ hσ hσT.le)
        (fun σ hσ hσT => hpostF σ hσ hσT.le)
        (fun σ hσ hσT => hubtF σ hσ hσT.le)
        hG1tF hG2tF hLc_ceF hc'pos (le_of_lt (lt_trans hc'c (lt_of_le_of_lt hcd hdd'))) hd'T
    have hdecayW : ∃ C : ℝ, 0 ≤ C ∧
        (∀ σ ∈ Set.Icc c' d', ∀ k : ℕ, 1 ≤ k →
          |cosineCoeffs (fun x => p.ν * intervalDomainLift (D.u σ) x ^ p.γ) k|
            ≤ C / ((k : ℝ) * Real.pi) ^ 2) ∧
        (∀ σ ∈ Set.Icc c' d',
          |cosineCoeffs (fun x => p.ν * intervalDomainLift (D.u σ) x ^ p.γ) 0| ≤ C) :=
      ShenWork.Paper2.ResolverPowerDecay.powerSource_window_uniform_decay
        (ν := p.ν) (γ := p.γ) (M := D.M) (m := mLow) p.hν.le p.hγ hmLow_pos
        (w := D.u) (c' := c') (d' := d')
        (le_of_lt (lt_trans hc'c (lt_of_le_of_lt hcd hdd'))) bc hbsumW hagreeW
        hlbW hubW (G1 := G1w) (G2 := G2w) hG1w hG2w
    obtain ⟨C, hC, hdecayWk, ha0W⟩ := hdecayW
    -- (R-Hvsrc-2) POWER-SOURCE K1 time-`C¹` quadruple for `ν·u^γ` on the window.
    -- ROUTE: clone `IntervalPicardLimitK1Weak.hasDerivAt_logisticSlice` /
    -- `hasDerivAt_sourceCoeff` with the nonlinearity `r ↦ p.ν·r^p.γ` (chain rule
    -- through `Real.hasDerivAt_rpow_const` on the strictly-positive slice `D.u σ`,
    -- `hposW`), giving the cosine-coefficient time derivative `adotP σ k`, its window
    -- continuity, and a window-uniform bound `Mdot` — the exact `ν·r^γ` analogue of the
    -- already-available logistic K1 quadruple `hK1`.  SATISFIABLE; named residual.
    have hK1pow : ∃ (adotP : ℝ → ℕ → ℝ) (Mdot : ℝ),
        (∀ σ ∈ Set.Icc c' d', ∀ n, HasDerivAt
          (fun r => cosineCoeffs
            (fun x => p.ν * intervalDomainLift (D.u r) x ^ p.γ) n) (adotP σ n) σ) ∧
        (∀ n, ContinuousOn (fun σ => adotP σ n) (Set.Icc c' d')) ∧
        (∀ σ ∈ Set.Icc c' d', ∀ n, |adotP σ n| ≤ Mdot) := by
      -- power-source K1 quadruple on `Ioo 0 D.T`, restricted to the window `[c',d']`.
      obtain ⟨hderivG, hcontG, hboundG⟩ :=
        ShenWork.Paper2.ResolverPowerK1.powerK1_quadruple_of_subtypeCont
          (p := p) hχ0 D.u hα ha.le hb.le hu₀.admissible.2 hu₀_bdF hfixF hsrc0F
          (Msup := D.M)
          (bc := fun σ k => ShenWork.IntervalPicardLimitRestart.limitCoeff p u₀ D.u σ k)
          (fun σ hσ hσT => hbsumF σ hσ hσT.le)
          (fun σ hσ hσT => hagreeF σ hσ hσT.le)
          (fun σ hσ hσT => hpostF σ hσ hσT.le)
          (fun σ hσ hσT => hubtF σ hσ hσT.le)
          hG1tF hG2tF hLc_ceF
      -- window inclusion `[c',d'] ⊆ Ioo 0 D.T`.
      have hwin_open : Set.Icc c' d' ⊆ Set.Ioo (0 : ℝ) D.T := fun σ hσ =>
        ⟨lt_of_lt_of_le hc'pos hσ.1, lt_of_le_of_lt hσ.2 hd'T⟩
      obtain ⟨Mdot, hMdot⟩ := hboundG c' d' hc'pos hd'T
      refine ⟨ShenWork.Paper2.ResolverPowerK1.adotPowOf p D.u, Mdot, ?_, ?_, hMdot⟩
      · intro σ hσ n
        exact hderivG σ (hwin_open hσ).1 (hwin_open hσ).2 n
      · intro n
        exact (hcontG n).mono hwin_open
    obtain ⟨adotP, Mdot, hderivP, hadotcontP, hMdotP⟩ := hK1pow
    -- Build the clamped resolver-source `DuhamelSourceTimeC1` (τ = 0 ⇒ Φ = φ).
    refine ⟨fun σ k => (ShenWork.PDE.intervalNeumannResolverSourceCoeff p
        (D.u (ShenWork.IntervalTimeSoftClamp.φ c' c d d' (0 + σ))) k).re,
      ?_, Set.Ioo c d, ?_, ?_⟩
    · exact ShenWork.Paper2.ResolverSourceClampedWitness.clampedResolverSource_duhamelSourceTimeC1
        p D.u hc'c hcd hdd' bc hbsumW hagreeW hposW hC hdecayWk ha0W
        adotP hderivP hadotcontP hMdotP
    · -- W = Ioo c d ∈ 𝓝 t₀  (c = t₀/2 < t₀ < (t₀+T)/2 = d)
      refine isOpen_Ioo.mem_nhds ⟨?_, ?_⟩
      · rw [hcdef]; linarith
      · rw [hddef]; linarith
    · -- agreement on W: on Ioo c d ⊂ Icc c d the clamp is the identity (φ = id)
      intro s hs k
      have hsId : (0 : ℝ) + s ∈ Set.Icc c d :=
        ⟨by simpa using le_of_lt hs.1, by simpa using le_of_lt hs.2⟩
      have heq := ShenWork.Paper2.ResolverSourceClampedWitness.clampedResolverFamily_eq_on
        p D.u hc'c hdd' hsId k
      simpa using heq
  -- Hvpos: strict boundary positivity of the resolver, from the elliptic
  -- strong-maximum-principle producer (now landed).
  Hvpos := ShenWork.IntervalResolverStrictPositivity.mildChemicalConcentration_pos p D }

/-! ## Tight-ledger provider companions

Task225 deleted the externally-carried `hpde_u` and `Hu` fields from the local
ledger interface.  The provider above still constructs the older reduced ledger,
so the additive helpers below simply forget `hpde_u` and expose the same provider
through `LedgerSweep.TightLimitRegularityInputs`. -/

/-- **Per-datum tight ledger from the existing reduced provider.**
All fields are copied from `reducedLimitRegularityInputs_of_picard` except the
now-derivable `hpde_u` field, which is intentionally not carried by the tight
interface. -/
noncomputable def tightLimitRegularityInputs_of_picard
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b) (hα : 1 ≤ p.α)
    (u₀ : intervalDomainPoint → ℝ) (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (D : GradientMildSolutionData p u₀)
    (hDu : D.u = picardLimit p u₀ D.T)
    (R : PicardIterateResidualData p u₀ D) :
    LedgerSweep.TightLimitRegularityInputs p u₀ D :=
  let I := reducedLimitRegularityInputs_of_picard p hχ0 ha hb hα u₀ hu₀ D hDu R
  { hα := I.hα
    ha := I.ha
    hb := I.hb
    hu₀_cont := I.hu₀_cont
    M₀ := I.M₀
    hu₀_bound := I.hu₀_bound
    hfix := I.hfix
    hsrc0 := I.hsrc0
    Msup := I.Msup
    bc := I.bc
    hbsum := I.hbsum
    hagree := I.hagree
    hpost := I.hpost
    hubt := I.hubt
    hG1t := I.hG1t
    hG2t := I.hG2t
    hN0t := I.hN0t
    hN1t := I.hN1t
    adott := I.adott
    hderivt := I.hderivt
    hadotcontt := I.hadotcontt
    hMdott := I.hMdott
    hLc := I.hLc
    Hvsrc := I.Hvsrc
    Hvpos := I.Hvpos }

/-! ## Wdata-only narrowing: cone facts supplied at the construction site

The provider's residual surface is shrunk from the THREE-leg
`HresWiring.PicardIterateResidualCore` (`hFacts`, `hcont_iter`, `Wdata`) to the
single genuinely-open per-window K2 leg `Wdata`.  The other two legs
(`hFacts`/`hcont_iter`) are NOT open residuals — they are RETURNED by the cone
construction `coneGradientMildSolutionData_exists_with_data` at the construction
site (where `D.T = δ`, so the cone's `∀ n, HasContinuousSlices δ (picardIter …)`
and `∃ F : PicardConvFacts, F.T = δ` transport verbatim to `D.T`).  They cannot be
recovered from a bare canonical-Picard-limit datum of *arbitrary* horizon, so they
must be wired in WHERE the datum is freshly cone-constructed — which is what the
two helpers below do (replacing the fact-stripping plain-cone bridge
`ConeQuantBridge.quantitativeLocalExistence_chiZero` with a fact-carrying one). -/

/-- **Per-datum reduced ledger from the cone facts + the Wdata-only residual.**
Assembles `PicardIterateResidualCore` from the cone-returned `hcont_iter`/`hFacts`
(`hFacts_T : hFacts.T = D.T`) and the single residual `Wdata`, lifts it to the full
`PicardIterateResidualData` via the universally-derived legs
(`picardIterateResidualData_of_core`), then runs the existing reduced-ledger
producer. -/
noncomputable def reducedLimitRegularityInputs_of_wdata
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b) (hα : 1 ≤ p.α)
    (u₀ : intervalDomainPoint → ℝ) (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (D : GradientMildSolutionData p u₀)
    (hDu : D.u = picardLimit p u₀ D.T)
    (hcont_iter : ∀ n : ℕ, HasContinuousSlices D.T (picardIter p u₀ n))
    (hFacts : PicardConvFacts p u₀) (hFacts_T : hFacts.T = D.T)
    -- cosine-coefficient TIME continuity on windows `[a',τ] ⊆ (0, D.T]`, the single
    -- ingredient the spatial cone core does not carry; supplied from the tower
    -- (`IntervalPicardTowerProjection.hiter_cont_of_tower`).
    (hiter_cont : ∀ (a' τ : ℝ), 0 < a' → a' ≤ τ → τ ≤ D.T → ∀ (n k : ℕ),
      ContinuousOn
        (fun s => ShenWork.IntervalNeumannFullKernel.cosineCoeffs
          (ShenWork.IntervalGradientDuhamelMap.logisticLifted p (picardIter p u₀ n s)) k)
        (Set.Icc a' τ))
    (Wdata : WdataProvider p u₀ D) :
    LedgerSweep.ReducedLimitRegularityInputs p u₀ D :=
  -- the cone-specific iterate residual core.
  let C := picardIterateResidualCore_of_wdata hcont_iter hFacts hFacts_T Wdata
  -- the limit-source bounded-Duhamel package, built NON-circularly (spatial Stage-A
  -- `hcontP`, never `hsliceTC`) from the core + the tower `hiter_cont`.
  let hsrc0 := ShenWork.Paper2.HresWiring.duhamelSourceBddOn_of_core hα ha.le hb.le
    hu₀ hDu C hiter_cont
  -- the D-side initial-datum cosine-coefficient bound, from `Continuous u₀`.
  let hu₀_bnd := ShenWork.IntervalRestartSliceLipschitz.u₀_cosineCoeff_bound
    hu₀.admissible.2
  reducedLimitRegularityInputs_of_picard p hχ0 ha hb hα u₀ hu₀ D hDu
    (picardIterateResidualData_of_core hχ0 hu₀.admissible.2 hDu hsrc0
      hu₀_bnd.choose_spec.2 C)

/-- **The reduced classical frontier core from the cone facts + Wdata.**
The per-datum `⟨R, frontierCore⟩` package the quantitative- and local-side
assemblers need, built from the reduced ledger via the existing
`LedgerSweep`/`MildLocalChi0` machinery. -/
noncomputable def restartAndFrontierCore_of_wdata
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b) (hα : 1 ≤ p.α)
    (u₀ : intervalDomainPoint → ℝ) (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (D : GradientMildSolutionData p u₀)
    (hDu : D.u = picardLimit p u₀ D.T)
    (hcont_iter : ∀ n : ℕ, HasContinuousSlices D.T (picardIter p u₀ n))
    (hFacts : PicardConvFacts p u₀) (hFacts_T : hFacts.T = D.T)
    (hiter_cont : ∀ (a' τ : ℝ), 0 < a' → a' ≤ τ → τ ≤ D.T → ∀ (n k : ℕ),
      ContinuousOn
        (fun s => ShenWork.IntervalNeumannFullKernel.cosineCoeffs
          (ShenWork.IntervalGradientDuhamelMap.logisticLifted p (picardIter p u₀ n s)) k)
        (Set.Icc a' τ))
    (Wdata : WdataProvider p u₀ D) :
    (ShenWork.IntervalMildRegularityBootstrap.GradientMildHalfStepRestartData D) ×'
      (ShenWork.IntervalMildToLocalExistence.GradientMildClassicalFrontierCoreData p D) :=
  let I := LedgerSweep.limitRegularityInputs_of_reduced hχ0
    (reducedLimitRegularityInputs_of_wdata p hχ0 ha hb hα u₀ hu₀ D hDu
      hcont_iter hFacts hFacts_T hiter_cont Wdata)
  ⟨MildLocalChi0.restartData_of_inputs hχ0 I,
   MildLocalChi0.frontierCore_of_inputs hχ0 I⟩

/-- **Per-datum tight ledger from cone facts + the Wdata-only residual.**
This is the tight companion to `reducedLimitRegularityInputs_of_wdata`: it builds
the same iterate residual package, then exposes the smaller Task225 ledger that
does not carry `hpde_u`/`Hu` as external fields. -/
noncomputable def tightLimitRegularityInputs_of_wdata
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b) (hα : 1 ≤ p.α)
    (u₀ : intervalDomainPoint → ℝ) (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (D : GradientMildSolutionData p u₀)
    (hDu : D.u = picardLimit p u₀ D.T)
    (hcont_iter : ∀ n : ℕ, HasContinuousSlices D.T (picardIter p u₀ n))
    (hFacts : PicardConvFacts p u₀) (hFacts_T : hFacts.T = D.T)
    (hiter_cont : ∀ (a' τ : ℝ), 0 < a' → a' ≤ τ → τ ≤ D.T → ∀ (n k : ℕ),
      ContinuousOn
        (fun s => ShenWork.IntervalNeumannFullKernel.cosineCoeffs
          (ShenWork.IntervalGradientDuhamelMap.logisticLifted p (picardIter p u₀ n s)) k)
        (Set.Icc a' τ))
    (Wdata : WdataProvider p u₀ D) :
    LedgerSweep.TightLimitRegularityInputs p u₀ D :=
  let C := picardIterateResidualCore_of_wdata hcont_iter hFacts hFacts_T Wdata
  let hsrc0 := ShenWork.Paper2.HresWiring.duhamelSourceBddOn_of_core hα ha.le hb.le
    hu₀ hDu C hiter_cont
  let hu₀_bnd := ShenWork.IntervalRestartSliceLipschitz.u₀_cosineCoeff_bound
    hu₀.admissible.2
  tightLimitRegularityInputs_of_picard p hχ0 ha hb hα u₀ hu₀ D hDu
    (picardIterateResidualData_of_core hχ0 hu₀.admissible.2 hDu hsrc0
      hu₀_bnd.choose_spec.2 C)

/-- **The tight classical frontier core from cone facts + Wdata.**
Same output as `restartAndFrontierCore_of_wdata`, routed through
`LedgerSweep.limitRegularityInputs_of_tight` so downstream audits see that the
provider now targets the smaller `hpde_u`/`Hu`-free ledger surface. -/
noncomputable def restartAndFrontierCore_of_wdata_tight
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b) (hα : 1 ≤ p.α)
    (u₀ : intervalDomainPoint → ℝ) (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (D : GradientMildSolutionData p u₀)
    (hDu : D.u = picardLimit p u₀ D.T)
    (hcont_iter : ∀ n : ℕ, HasContinuousSlices D.T (picardIter p u₀ n))
    (hFacts : PicardConvFacts p u₀) (hFacts_T : hFacts.T = D.T)
    (hiter_cont : ∀ (a' τ : ℝ), 0 < a' → a' ≤ τ → τ ≤ D.T → ∀ (n k : ℕ),
      ContinuousOn
        (fun s => ShenWork.IntervalNeumannFullKernel.cosineCoeffs
          (ShenWork.IntervalGradientDuhamelMap.logisticLifted p (picardIter p u₀ n s)) k)
        (Set.Icc a' τ))
    (Wdata : WdataProvider p u₀ D) :
    (ShenWork.IntervalMildRegularityBootstrap.GradientMildHalfStepRestartData D) ×'
      (ShenWork.IntervalMildToLocalExistence.GradientMildClassicalFrontierCoreData p D) :=
  let I := LedgerSweep.limitRegularityInputs_of_tight hχ0
    (tightLimitRegularityInputs_of_wdata p hχ0 ha hb hα u₀ hu₀ D hDu
      hcont_iter hFacts hFacts_T hiter_cont Wdata)
  ⟨MildLocalChi0.restartData_of_inputs hχ0 I,
   MildLocalChi0.frontierCore_of_inputs hχ0 I⟩

/-- **Quantitative local existence (χ₀ = 0) from the Wdata-only provider.**
Replaces `ConeQuantBridge.quantitativeLocalExistence_chiZero` (which strips the
cone facts by using the PLAIN cone) with a fact-carrying bridge: the cone datum is
built by `coneGradientMildSolutionData_exists_with_data`, exposing `hcont_iter` and
the `PicardConvFacts`, which together with the per-datum `Wdata` residual discharge
the reduced ledger and hence the frontier core (`classicalSolution_at_horizon`). -/
theorem quantitativeLocalExistence_chiZero_wdata
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b) (hα_ge : 1 ≤ p.α)
    (Hiter : IterCoeffTimeContProvider p)
    (HWdata : ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
      ∀ D : GradientMildSolutionData p u₀,
        D.u = picardLimit p u₀ D.T → WdataProvider p u₀ D) :
    ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u := by
  intro M hM
  obtain ⟨δ, hδ, h⟩ := coneGradientMildSolutionData_exists_with_data p hχ0 hM hα_ge
  refine ⟨δ, hδ, ?_⟩
  intro u₀ hu₀ hbound
  obtain ⟨D, hDT, hDu, hcont_iter, hFacts_ex, _hpos_iter⟩ :=
    h u₀ hu₀.admissible.2 hbound
      (ShenWork.Paper2.ConeQuantBridge.positiveInitialDatum_nonneg hu₀)
      (ShenWork.Paper2.ConeQuantBridge.positiveInitialDatum_pos_somewhere hu₀)
  -- the canonical Picard-limit identity at this datum's horizon
  have hDu' : D.u = picardLimit p u₀ D.T := by rw [hDT]; exact hDu
  -- the cone facts package, with its horizon transported to `D.T`
  obtain ⟨hFacts, hFactsT⟩ := hFacts_ex
  have hFacts_T : hFacts.T = D.T := by rw [hFactsT, hDT]
  -- assemble `⟨R, hCore⟩` from {cone facts + Wdata}
  obtain ⟨R, hCore⟩ :=
    restartAndFrontierCore_of_wdata p hχ0 ha hb hα_ge u₀ hu₀ D hDu'
      hcont_iter hFacts hFacts_T (Hiter u₀ hu₀ D hDu') (HWdata u₀ hu₀ D hDu')
  obtain ⟨v, hsol, htrace⟩ :=
    ShenWork.Paper2.ThresholdQuantBridge.classicalSolution_at_horizon p D R
      (gradientMildSolutionData_initialApproach p hu₀.admissible.2 D) hCore
  exact ⟨D.u, v, hsol.restrict_horizon hδ (le_of_eq hDT.symm), htrace⟩

/-- **Local existence (χ₀ = 0) from the Wdata-only provider.**  Same as
`MildLocalChi0.hMildLocal_chi0_zero_of_inputs`, but the cone datum is built with
the `_with_data` cone (exposing `hcont_iter`/`hFacts`), so the reduced ledger is
discharged from {cone facts + the single `Wdata` residual} rather than from a full
residual provider. -/
theorem hMildLocal_chi0_zero_of_wdata
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b) (hα_ge : 1 ≤ p.α)
    (Hiter : IterCoeffTimeContProvider p)
    (HWdata : ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
      ∀ D : GradientMildSolutionData p u₀,
        D.u = picardLimit p u₀ D.T → WdataProvider p u₀ D) :
    RestartLocalWiring.IntervalDomainGradientMildHalfStepRestartFrontierCoreLocalData p := by
  intro u₀ hu₀
  obtain ⟨B, hB⟩ := hu₀.admissible.1
  set M := max B 1 with hMdef
  have hM : 0 < M := lt_of_lt_of_le one_pos (le_max_right B 1)
  have hbound : ∀ x, |u₀ x| ≤ M := fun x =>
    le_trans (hB (Set.mem_range_self x)) (le_max_left B 1)
  obtain ⟨δ, _hδ, hD⟩ := coneGradientMildSolutionData_exists_with_data p hχ0 hM hα_ge
  obtain ⟨D, hDT, hDu, hcont_iter, hFacts_ex, _hpos_iter⟩ := hD u₀ hu₀.admissible.2 hbound
    (ShenWork.Paper2.ConeQuantBridge.positiveInitialDatum_nonneg hu₀)
    (ShenWork.Paper2.ConeQuantBridge.positiveInitialDatum_pos_somewhere hu₀)
  have hDu' : D.u = picardLimit p u₀ D.T := by rw [hDT]; exact hDu
  obtain ⟨hFacts, hFactsT⟩ := hFacts_ex
  have hFacts_T : hFacts.T = D.T := by rw [hFactsT, hDT]
  obtain ⟨R, hCore⟩ :=
    restartAndFrontierCore_of_wdata p hχ0 ha hb hα_ge u₀ hu₀ D hDu'
      hcont_iter hFacts hFacts_T (Hiter u₀ hu₀ D hDu') (HWdata u₀ hu₀ D hDu')
  exact ⟨D, R, gradientMildSolutionData_initialApproach p hu₀.admissible.2 D, hCore⟩

/-- **FINAL WIRING — Paper 2 Theorem 1.1 (χ₀ = 0), Wdata-only residual surface.**

⚠️ **FIDELITY / SCOPE BANNER (read before citing this as "Theorem 1.1").**
The name says `unconditional` but this theorem is NOT the paper's Theorem 1.1.
It is a FRAGMENT, restricted on FIVE axes, and is CONDITIONAL:
  1. `p.χ₀ = 0` — the paper's Theorem 1.1 assumes `χ₀ ≤ 0`.  At `χ₀ = 0` the
     chemotaxis term `−χ₀∇·(uᵐχ(v)∇v)` vanishes identically and the u-equation
     DECOUPLES into the scalar reaction–diffusion equation `uₜ = Δu + u(a−buᵅ)`
     — i.e. this is the degenerate slice where the model is no longer a
     chemotaxis system.  The genuine case `χ₀ < 0` is untouched.
  2. `intervalDomain` is N = 1 (`Subtype (Icc 0 1)`); the paper is `Ω ⊂ ℝᴺ`,
     and its analytic core is the N-dimensional elliptic regularity it dodges.
  3. `0 < a` AND `0 < b` hardwired; the paper's part (2) `a = b = 0` is only
     discharged vacuously under the contradictory `0 < a ∧ a = 0`.
  4. `1 ≤ α`, `1 ≤ γ` are blanket hypotheses; the paper assumes only `α, γ > 0`.
  5. CONDITIONAL on the providers `Hiter` + `HWdata`, which bottom out at the
     residual `TowerConeAnalyticResidual = { hsrc0 }`.  `hsrc0` is the paper's
     genuine analytic content (time-C¹ / ℓ¹ Duhamel-source regularity) carried
     as a HYPOTHESIS, and its as-typed satisfiability (an ℓ¹ envelope at `s = 0`
     for merely-continuous `u₀`) is OPEN — see HANDOFF/k1-wall-plan.md.  Until
     `hsrc0` is discharged or shown satisfiable, this is a conditional theorem.
Per the formalization-playbook verdict labels: statement layer FAITHFUL (the
PDE, both equations, Neumann BC, genuine C² regularity, the exact (1.21) bound
are all real, not hollow), parameter coverage FRAGMENT, residual CONDITIONAL.

Assembles Theorem 1.1 (χ₀ = 0) directly from the regime constants and the
SINGLE-leg residual provider `HWdata`, via `paper2_theorem_1_1_from_quant_and_hlocal`:

    quantitativeLocalExistence_chiZero_wdata HWdata   -- hQuant (fact-carrying cone)
      ⊕ hMildLocal_chi0_zero_of_wdata HWdata          -- hlocal (fact-carrying cone)
      → paper2_theorem_1_1_from_quant_and_hlocal
      → Theorem_1_1 intervalDomain p

**The residual surface is now `Wdata`-only.**  Compared with the former
three-leg `HresWiring.PicardIterateResidualCore` provider (`hFacts`, `hcont_iter`,
`Wdata`), the cone facts `hFacts`/`hcont_iter` are NO LONGER hypotheses: both the
quantitative- and local-side bridges build their cone datum with
`coneGradientMildSolutionData_exists_with_data`, which RETURNS the iterate
slice-continuity bundle `hcont_iter` and the ball/geometric `PicardConvFacts`
package at the construction horizon `D.T = δ`.  These two legs are therefore
discharged at the point of construction — they are not open residuals — leaving
the genuinely-open per-window K2 leg `Wdata` as the only provider obligation.
(`hsliceTC` and `hLcont_lim` remain discharged universally inside
`picardIterateResidualData_of_core`.)

The narrowing replaces the fact-stripping plain-cone bridge
`ConeQuantBridge.quantitativeLocalExistence_chiZero` with the fact-carrying
`quantitativeLocalExistence_chiZero_wdata`; the universal frontier residual `hPLF`
(`PicardLimitRestartFrontier p`, a `∀ D` Prop applied to the plain-cone datum after
its facts were stripped) is no longer used.

The hypotheses are `p.χ₀ = 0`, the structural regime constants
(`0 < a`, `0 < b`, `1 ≤ α`, `1 ≤ γ`), and the two providers `Hiter` + `HWdata`
(see the FIDELITY BANNER above).  As of commit 32c8fee the `hinterior` analytic
core is no longer a raw `sorry`: it is discharged by
`IntervalRestartSliceLipschitz.hinterior_of_src0`, CONDITIONAL on the `hsrc0`
package threaded through the providers.  `#print axioms` therefore reports
`[propext, Classical.choice, Quot.sound]` (no `sorryAx`) — but this is a
CONDITIONAL theorem (the analytic content lives in the `Hiter`/`HWdata` →
`hsrc0` hypothesis), NOT an unconditional proof; and the clean-tree
certification of that `#print axioms` is tracked separately (the earlier
"clean" reports were run on a divergent remote olean tree). -/
theorem paper2_theorem_1_1_chiZero_unconditional
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    -- the per-datum cosine-coefficient TIME-continuity provider (the single
    -- iterate-side ingredient the spatial cone does NOT return, supplying the `hsrc0`
    -- argument of the slice-continuity chain through the non-circular spatial route).
    -- Discharged from the tower in `IntervalPicardTowerSupply.…_from_coneSupply`.
    (Hiter : IterCoeffTimeContProvider p)
    -- the NARROWED (Wdata-only) iterate-side residual provider for every canonical
    -- Picard-limit datum.  Carries ONLY the genuinely-open per-window K2 leg
    -- `WdataProvider`; the cone facts `hFacts`/`hcont_iter` are returned by the
    -- `_with_data` cone at the construction site (see the helpers above), and
    -- `hsliceTC`/`hLcont_lim` are discharged universally.
    (HWdata : ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
      ∀ D : GradientMildSolutionData p u₀,
        D.u = picardLimit p u₀ D.T →
        WdataProvider p u₀ D) :
    Theorem_1_1 intervalDomain p :=
  RestartLocalWiring.paper2_theorem_1_1_from_quant_and_hlocal
    p (le_of_eq hχ0) ha hb hγ
    (quantitativeLocalExistence_chiZero_wdata p hχ0 ha hb hα Hiter HWdata)
    (RestartLocalWiring.localExistence_of_gradientMildHalfStepRestartFrontierCoreLocalData
      p (hMildLocal_chi0_zero_of_wdata p hχ0 ha hb hα Hiter HWdata))

/-! ## §W6b — Per-constructed-datum provider surface (additive, narrowed).

`paper2_theorem_1_1_chiZero_unconditional` consumes the two `∀ D` providers
`IterCoeffTimeContProvider`/`HWdata` and invokes them ONLY at the cone-constructed
datum (see `quantitativeLocalExistence_chiZero_wdata` / `hMildLocal_chi0_zero_of_wdata`:
the datum is obtained from `coneGradientMildSolutionData_exists_with_data` and the
providers are called at exactly that `D`).  The `∀ D` form is therefore stronger than
the consumption pattern requires.  This section adds — ADDITIVELY, with ZERO change to
the existing declarations — a capstone whose provider OWNS the datum: a per-`u₀`
existence of a small-horizon datum bundling the two iterate-side legs at THAT datum.
This is the invocation-restricted surface; it is what the cone construction can
actually instantiate (the gate/positivity facts hold only at the cone horizon). -/

/-- The two iterate-side legs (`WdataProvider` + per-window cosine-coefficient TIME
continuity) bundled at a SINGLE datum `D` — the exact pair the reduced-ledger
assembler `restartAndFrontierCore_of_wdata` consumes. -/
def DatumIterLegs (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (D : GradientMildSolutionData p u₀) : Type :=
  (WdataProvider p u₀ D) ×'
    (∀ (a' τ : ℝ), 0 < a' → a' ≤ τ → τ ≤ D.T → ∀ (n k : ℕ),
      ContinuousOn
        (fun s => ShenWork.IntervalNeumannFullKernel.cosineCoeffs
          (ShenWork.IntervalGradientDuhamelMap.logisticLifted p (picardIter p u₀ n s)) k)
        (Set.Icc a' τ))

/-- **The narrowed, per-constructed-datum supply.**

For every mass `M_in > 0` there is a horizon `δ > 0` such that every admissible datum
`u₀` (continuous, `|u₀| ≤ M_in`, nonnegative, positive somewhere) admits a packaged
`GradientMildSolutionData` on `[0, δ]` carrying the cone-returned slice-continuity and
`PicardConvFacts` AND the two iterate-side legs `DatumIterLegs` at that datum.  This is
the EXACT return shape of `coneGradientMildSolutionData_exists_with_data` augmented with
`DatumIterLegs` (and minus the unused strict-positivity conjunct).  Crucially the datum
`D` is supplied here, so the iterate-side residual is owed only at the cone horizon. -/
def DatumProviderSupply (p : CM2Params) : Type :=
  ∀ M_in : ℝ, 0 < M_in → Σ' δ : ℝ, (0 < δ) ×'
    ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
      (∀ x, |u₀ x| ≤ M_in) →
      Σ' D : GradientMildSolutionData p u₀,
        (D.T = δ) ×' (D.u = picardLimit p u₀ δ) ×'
        (∀ n, HasContinuousSlices D.T (picardIter p u₀ n)) ×'
        (∃ F : ShenWork.IntervalPicardLimitCoeffConv.PicardConvFacts p u₀, F.T = δ) ×'
        DatumIterLegs p u₀ D

/-- **Quantitative local existence (χ₀ = 0) from the narrowed datum supply.**
Identical conclusion to `quantitativeLocalExistence_chiZero_wdata`, but the cone datum
and its two iterate-side legs are taken from `Hsupply` (which OWNS the datum) rather
than rebuilt + fed `∀ D` providers. -/
theorem quantitativeLocalExistence_chiZero_datum
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b) (hα_ge : 1 ≤ p.α)
    (Hsupply : DatumProviderSupply p) :
    ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u := by
  intro M hM
  obtain ⟨δ, hδ, h⟩ := Hsupply M hM
  refine ⟨δ, hδ, ?_⟩
  intro u₀ hu₀ hbound
  obtain ⟨D, hDT, hDu, _hcont_iter, hFacts_ex, hWdata, hiter_cont⟩ := h u₀ hu₀ hbound
  have hDu' : D.u = picardLimit p u₀ D.T := by rw [hDT]; exact hDu
  obtain ⟨hFacts, hFactsT⟩ := hFacts_ex
  have hFacts_T : hFacts.T = D.T := by rw [hFactsT, hDT]
  obtain ⟨R, hCore⟩ :=
    restartAndFrontierCore_of_wdata p hχ0 ha hb hα_ge u₀ hu₀ D hDu'
      _hcont_iter hFacts hFacts_T hiter_cont hWdata
  obtain ⟨v, hsol, htrace⟩ :=
    ShenWork.Paper2.ThresholdQuantBridge.classicalSolution_at_horizon p D R
      (gradientMildSolutionData_initialApproach p hu₀.admissible.2 D) hCore
  exact ⟨D.u, v, hsol.restrict_horizon hδ (le_of_eq hDT.symm), htrace⟩

/-- **Local existence (χ₀ = 0) from the narrowed datum supply.**  Mirror of
`hMildLocal_chi0_zero_of_wdata`, sourcing the datum + legs from `Hsupply`. -/
theorem hMildLocal_chi0_zero_of_datum
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b) (hα_ge : 1 ≤ p.α)
    (Hsupply : DatumProviderSupply p) :
    RestartLocalWiring.IntervalDomainGradientMildHalfStepRestartFrontierCoreLocalData p := by
  intro u₀ hu₀
  obtain ⟨B, hB⟩ := hu₀.admissible.1
  set M := max B 1 with hMdef
  have hM : 0 < M := lt_of_lt_of_le one_pos (le_max_right B 1)
  have hbound : ∀ x, |u₀ x| ≤ M := fun x =>
    le_trans (hB (Set.mem_range_self x)) (le_max_left B 1)
  obtain ⟨δ, _hδ, h⟩ := Hsupply M hM
  obtain ⟨D, hDT, hDu, _hcont_iter, hFacts_ex, hWdata, hiter_cont⟩ := h u₀ hu₀ hbound
  have hDu' : D.u = picardLimit p u₀ D.T := by rw [hDT]; exact hDu
  obtain ⟨hFacts, hFactsT⟩ := hFacts_ex
  have hFacts_T : hFacts.T = D.T := by rw [hFactsT, hDT]
  obtain ⟨R, hCore⟩ :=
    restartAndFrontierCore_of_wdata p hχ0 ha hb hα_ge u₀ hu₀ D hDu'
      _hcont_iter hFacts hFacts_T hiter_cont hWdata
  exact ⟨D, R, gradientMildSolutionData_initialApproach p hu₀.admissible.2 D, hCore⟩

/-- **FINAL WIRING — Paper 2 Theorem 1.1 (χ₀ = 0) from the narrowed datum supply.**

ADDITIVE companion to `paper2_theorem_1_1_chiZero_unconditional`.  Same conclusion
(`Theorem_1_1 intervalDomain p`), same regime hypotheses, but the iterate-side residual
is a SINGLE narrowed supply `Hsupply : DatumProviderSupply p` that owns the
cone-constructed datum and bundles the two iterate-side legs at exactly that datum —
the invocation-restricted surface the capstone actually consumes.  No existing
declaration changes. -/
theorem paper2_theorem_1_1_chiZero_of_datumProviders
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (Hsupply : DatumProviderSupply p) :
    Theorem_1_1 intervalDomain p :=
  RestartLocalWiring.paper2_theorem_1_1_from_quant_and_hlocal
    p (le_of_eq hχ0) ha hb hγ
    (quantitativeLocalExistence_chiZero_datum p hχ0 ha hb hα Hsupply)
    (RestartLocalWiring.localExistence_of_gradientMildHalfStepRestartFrontierCoreLocalData
      p (hMildLocal_chi0_zero_of_datum p hχ0 ha hb hα Hsupply))

end ShenWork.Paper2.Thm11ChiZeroCoreProvider
