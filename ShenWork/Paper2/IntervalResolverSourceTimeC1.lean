/-
  ShenWork/Paper2/IntervalResolverSourceTimeC1.lean

  **The `Hvsrc` ledger field — resolver power-source `ν·u^γ` time-`C¹` package:
  the would-be producer, and the global-quantifier retype finding.**

  ## What `Hvsrc` asks for

  `ReducedLimitRegularityInputs` (and the full `LimitRegularityInputs`) carry the
  field

      Hvsrc : DuhamelSourceTimeC1
        (fun s k => (intervalNeumannResolverSourceCoeff p (D.u s) k).re)

  i.e. the spectral-Duhamel time-`C¹` package for the cosine-coefficient family of
  the elliptic source `p.ν · u^γ`.  By
  `IntervalDomainLogisticWeakH2Adapter.resolverSourceCoeff_re_eq_cosineCoeffs`,
  `(intervalNeumannResolverSourceCoeff p u k).re = cosineCoeffs (ν·(lift u)^γ) k`,
  so this is the power-source analogue of the logistic `DuhamelSourceTimeC1`.

  ## The producer EXISTS — but it is GLOBAL-typed

  The representation-fed producer

      IntervalDomainLogisticWeakH2Adapter.resolverSource_duhamelSourceTimeC1_of_representation

  already discharges EXACTLY the `Hvsrc` shape from a per-slice cosine
  representation plus the power-source weak-H²/Neumann decay machinery
  (`powerSource_intervalWeakH2Neumann` / `intervalWeakH2Neumann_of_eigenvalue_summable`)
  and a `K1` time-`C¹` quadruple.  This file wraps it as
  `resolverSource_timeC1_of_global_representation`: GIVEN the GLOBAL
  representation/positivity/decay/`K1` inputs, the `Hvsrc` field is filled
  sorry-free.

  ## The obstruction — why the canonical family cannot feed it

  `DuhamelSourceTimeC1 a` has GLOBAL fields:

    * `hderiv      : ∀ s n,            HasDerivAt (fun r => a r n) (adot s n) s`
    * `henv_bound  : ∀ s, 0 ≤ s → ∀ n, |a s n| ≤ envelope n`
    * `hderivBound : ∀ s, 0 ≤ s → ∀ n, |adot s n| ≤ derivBound`

  For the canonical `D.u` (the Picard limit, `IntervalMildPicard.picardLimit`), the
  trajectory is the genuine solution ONLY on `(0, D.T]`; off that window the limit
  is the junk value `0` (`picardLimit … t x = 0` for `t ∉ (0,T]`).  Hence the
  source `s ↦ ν·(lift (D.u s))^γ` JUMPS at `s = D.T`: on `[0,1]` the slice
  `D.u D.T` is strictly positive (`D.hpos`), so its `0`-th cosine coefficient
  `∫₀¹ ν·(D.u D.T)^γ > 0`, whereas immediately past `D.T` the source collapses to
  `ν·0^γ = 0` (since `γ ≥ 1 > 0`), coefficient `0`.  The coefficient family
  `a s 0` therefore has a genuine discontinuity at `s = D.T`, so

      `hderiv` (differentiability of `a · 0` at `s = D.T`) is FALSE.

  The ledger supplies the representation/`K1`/`K2` data only on `(0, D.T)`; nothing
  controls `D.u` at `s ≥ D.T`, and for an arbitrary `D : GradientMildSolutionData`
  there is no producer of the global differentiability the structure demands.  The
  global inputs of `resolverSource_duhamelSourceTimeC1_of_representation`
  (`∀ σ` summability/agreement/positivity, `∀ σ, 0 ≤ σ` decay/derivative bounds,
  `∀ σ n` `HasDerivAt`) are thus UNFILLABLE for the canonical family.

  This is the SAME global-quantifier disease that the project already dissolved for
  the LOGISTIC source by retyping its global package
  `DuhamelSourceL1Cont` to the horizon-bounded `DuhamelSourceL1ContOn a T`
  (`IntervalPicardLimitRestartWeak`), whose `henv_bound`/`hcont` are required only
  on `[0, T]`.  The `Hvsrc` field never received the analogous `…On T` retype, so
  it remains the one field that is global-typed and therefore unsatisfiable for the
  canonical family.

  ## The retype the field needs (the finding)

  Note the downstream consumer chain reads the package only at INTERIOR times: the
  whole `HasResolverDirectSpectralData`/`resolverSeries_hasDerivAt_time` path
  (`IntervalResolverDirectTimeRegularity`) evaluates `src.adot`/the series and the
  `∀ᶠ`-agreement only for `t₀ ∈ Ioo 0 T`.  So the global typing of `Hvsrc` is
  STRICTLY STRONGER than what the consumer uses.  The faithful fix mirrors the
  logistic `…On T` retype:

    * introduce `DuhamelSourceTimeC1On a T` carrying
        `hderiv      : ∀ s ∈ Ioo 0 T, ∀ n, HasDerivAt (fun r => a r n) (adot s n) s`
        `hadotcont   : ∀ n, ContinuousOn (fun s => adot s n) (Ioo 0 T)`
        `henv_bound  : ∀ s, 0 ≤ s → s ≤ T → ∀ n, |a s n| ≤ envelope n`
        `hderivBound : ∀ s, 0 ≤ s → s ≤ T → ∀ n, |adot s n| ≤ derivBound`
      (all other fields as in `DuhamelSourceTimeC1`);
    * retype `Hvsrc : DuhamelSourceTimeC1On (…(D.u s)…) D.T`;
    * re-prove `resolverSeries_hasDerivAt_time` / `resolver_direct_*` over `Ioo 0 T`
      instead of `Ioi 0` (the proof already restricts to interior `t₀`; only the
      `hasDerivAt_tsum_of_isPreconnected` preconnected set must shrink from `Ioi 0`
      to `Ioo 0 T`), and feed the producer
      `resolverSource_duhamelSourceTimeC1_of_representation` with the WINDOWED ledger
      data via the soft-clamp transfer used by
      `ClampedSourceRepresentation.clampedSource_duhamelSourceTimeC1`.

  **UPDATE (retype LANDED).**  The `…On T` / per-`t₀` retype described above has now
  been executed across the consumer files: `HasResolverDirectSpectralData`
  (`IntervalResolverDirectTimeRegularity`) was retyped to the per-`t₀` existential
  (the `∃ a` moved INSIDE `∀ t₀`), the ledger `Hvsrc` field
  (`IntervalDomainMildLocalChi0` + `IntervalDomainLedgerSweep` +
  `IntervalDomainThm11ChiZeroFinal`) was retyped to a per-`t₀` CLAMPED witness
  (`∀ t₀, ∃ aC, ∃ _ : DuhamelSourceTimeC1 aC, ∃ W ∈ 𝓝 t₀, agreement-on-`W`), and the
  per-`t₀` packaging theorem `hasResolverDirectSpectralData_of_clamped_perT0` was
  added (`IntervalMildRegularityFrontierAssembly`).  The Provider's `Hvsrc` field is
  now FILLED via the soft-clamped resolver-source producer
  `ResolverSourceClampedWitness.clampedResolverSource_duhamelSourceTimeC1` (the
  `ν·u^γ` mirror of `ClampedSourceRepresentation.clampedSource_duhamelSourceTimeC1`),
  modulo two precisely-named power-source residuals (the `ν·r^γ` quadratic-decay
  envelope `R-Hvsrc-1` and the `ν·r^γ` K1 time-`C¹` quadruple `R-Hvsrc-2`).  The
  global producer below remains as the GLOBAL-input proof of fillability.

  No `sorry`/`admit`/custom `axiom`/`native_decide` in this file.
-/
import ShenWork.Paper2.IntervalDomainLogisticWeakH2Adapter
import ShenWork.Paper2.IntervalDomainClampedSourceRepresentation

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)

noncomputable section

namespace ShenWork.Paper2.ResolverSourceTimeC1

/-- **`Hvsrc` from a GLOBAL cosine representation.**

The would-be producer of the ledger's `Hvsrc` field: given the GLOBAL per-slice
cosine representation (`bc`, `hbsum`, `hagree`), boundary positivity (`hpos`), the
power-source quadratic decay (`hdecay`, `ha0`) and the `K1` time-`C¹` quadruple
(`hderiv`, `hadotcont`, `hMdot`) for the trajectory `w`, the resolver-source
spectral-Duhamel time-`C¹` package

    DuhamelSourceTimeC1 (fun s k => (intervalNeumannResolverSourceCoeff p (w s) k).re)

is produced sorry-free by the existing additive adapter
`IntervalDomainLogisticWeakH2Adapter.resolverSource_duhamelSourceTimeC1_of_representation`.

This is a thin re-export pinning down that the ledger field is FILLABLE — the only
gap is that the canonical `D.u` supplies these inputs on `(0, D.T)`, not globally
(see the file header for the precise obstruction and the `…On T` retype). -/
noncomputable def resolverSource_timeC1_of_global_representation
    (p : CM2Params) {w : ℝ → intervalDomainPoint → ℝ}
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ, Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagree : ∀ σ, Set.EqOn (intervalDomainLift (w σ))
        (fun x => ∑' n, bc σ n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    (hpos : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (w σ) x)
    {C : ℝ} (hC : 0 ≤ C)
    (hdecay : ∀ σ, 0 ≤ σ → ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs (fun x => p.ν * intervalDomainLift (w σ) x ^ p.γ) k|
        ≤ C / ((k : ℝ) * Real.pi) ^ 2)
    (ha0 : ∀ σ, 0 ≤ σ →
      |cosineCoeffs (fun x => p.ν * intervalDomainLift (w σ) x ^ p.γ) 0| ≤ C)
    {adot : ℝ → ℕ → ℝ}
    (hderiv : ∀ σ n, HasDerivAt
      (fun r => cosineCoeffs (fun x => p.ν * intervalDomainLift (w r) x ^ p.γ) n)
      (adot σ n) σ)
    (hadotcont : ∀ n, Continuous (fun σ => adot σ n))
    {Mdot : ℝ}
    (hMdot : ∀ σ, 0 ≤ σ → ∀ n, |adot σ n| ≤ Mdot) :
    DuhamelSourceTimeC1
      (fun s k => (ShenWork.PDE.intervalNeumannResolverSourceCoeff p (w s) k).re) :=
  ShenWork.IntervalDomainLogisticWeakH2Adapter.resolverSource_duhamelSourceTimeC1_of_representation
    p bc hbsum hagree hpos hC hdecay ha0 hderiv hadotcont hMdot

end ShenWork.Paper2.ResolverSourceTimeC1
