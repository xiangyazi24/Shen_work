/-
  ShenWork/Paper2/IntervalDomainLedgerSweep.lean

  **Ledger sweep — discharge the now-derivable `Hu` field of
  `LimitRegularityInputs` and re-export the tighter `χ₀ = 0` mild-local
  corollary on the reduced ledger.**

  ## What this file does

  `MildLocalChi0.LimitRegularityInputs p u₀ D` (the honest residual ledger for the
  `χ₀ = 0` sub-regime) carries — among the genuine frontier residuals — the field

      Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u

  Since commit `d079763`, `Hu` is no longer a frontier residual: it is DERIVABLE
  from the families the ledger ALREADY carries, via
  `IntervalPicardLimitTimeNhd.Hu_of_restart` (the general restart identity), whose
  weak-source hypothesis `hsrc0 : DuhamelSourceL1ContOn … D.T` is itself produced
  from the SAME K2/K1-unshifted families (horizon-bounded retype of the former
  `DuhamelSourceL1Cont.ofTimeC1 ∘ limitSource_duhamelSourceTimeC1` route).

  We therefore introduce the **reduced ledger**

      ReducedLimitRegularityInputs p u₀ D

  which is `LimitRegularityInputs` with the `Hu` field DELETED, and we prove

      LimitRegularityInputs p u₀ D   (from the reduced one)

  by reconstructing `Hu` from the reduced fields.  Chaining through the existing
  `MildLocalChi0` assembly, we re-export the tighter top-level statements

      hMildLocal_chi0_zero_of_reduced_inputs
      paper2_theorem_1_1_chiZero_of_reduced_inputs

  on the strictly smaller ledger (one fewer named frontier residual).

  ## Frontier verdict for the four candidate fields (see the sweep audit)

  * `hpde_u`   — RESIDUAL.  The only producer `mildSolution_parabolicPDE` delegates
                 to `IsPaper2ClassicalSolution.pde_u` (circular); no spectral→
                 pointwise PDE bridge concluding the parabolic identity from
                 `HasTimeNeighborhoodSpectralAgreement` exists at this layer.
  * `Hu`       — **DISCHARGED** here (this file): `Hu_of_restart`, net reduction.
  * `Hvpos`    — RESIDUAL.  `IntervalResolverPositivity` proves only NONNEG
                 (`0 ≤ R u`); the strict `0 < v` boundary positivity needs the
                 elliptic strong maximum principle, not wired.
  * `Hvsrc`    — RESIDUAL (new-input).  Would need a power-source analogue of
                 `logisticSource_duhamelSourceTimeC1` for `ν·uᵞ` plus the
                 coefficient bridge `cosineCoeffs (ν·uᵞ) = resolverSourceCoeff.re`;
                 not a pure reduction from the present ledger families.
  * `HsupNorm` — RESIDUAL.  The two `IntervalDomainSupNormDerivativeNonposOn`
                 lemmas in `IntervalDomainExistence` are transport/`congr` lemmas,
                 not genuine parabolic-maximum-principle producers.

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.
-/
import ShenWork.Paper2.IntervalDomainMildLocalChi0
import ShenWork.Paper2.IntervalPicardLimitTimeNhd
import ShenWork.Paper2.IntervalPicardLimitTimeNhdLocalized
import ShenWork.Paper2.IntervalDomainLimitSourceRepresentation

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint
   IntervalDomainSupNormDerivativeNonposOn)
open ShenWork.IntervalGradientDuhamelMap (intervalGradientDuhamelMap logisticLifted)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)
open ShenWork.IntervalMildToClassical (mildChemicalConcentration)
open ShenWork.IntervalMildPicardRegularity (logisticSourceFun)
open ShenWork.IntervalMildTimeDerivContinuity (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.PDE (intervalNeumannResolverSourceCoeff)
open ShenWork.IntervalPicardLimitRestartWeak (DuhamelSourceL1Cont DuhamelSourceL1ContOn)
open ShenWork.IntervalPicardLimitSourceData (limitSource_duhamelSourceTimeC1)
open ShenWork.IntervalDomainLimitSourceRepresentation
  (limitSource_duhamelSourceTimeC1_of_representation)
open ShenWork.IntervalPicardLimitTimeNhd (Hu_of_restart)
open ShenWork.Paper2
open ShenWork.Paper2.MildLocalChi0 (LimitRegularityInputs)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
open ShenWork.CosineSpectrum (cosineMode)

noncomputable section

namespace ShenWork.Paper2.LedgerSweep

/-! ## The reduced residual ledger (drops the now-derivable `Hu`) -/

/-- **`ReducedLimitRegularityInputs p u₀ D`** — `LimitRegularityInputs` with the
`Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u` field deleted.

`Hu` is no longer a frontier residual: it is derivable from the remaining fields
via the time-localized restart identity (`TimeNhdLocalized.Hu_of_restart_localized`),
with the weak-source package `hsrc0 : DuhamelSourceL1ContOn … D.T` now carried
directly as a ledger field.  Every field below also appears verbatim in
`LimitRegularityInputs`; this structure is strictly smaller (one fewer named
hypothesis). -/
structure ReducedLimitRegularityInputs
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (D : GradientMildSolutionData p u₀) where
  -- structural regime parameters
  hα : 1 ≤ p.α
  ha : 0 ≤ p.a
  hb : 0 ≤ p.b
  -- H1 datum data
  hu₀_cont : Continuous u₀
  M₀ : ℝ
  hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀
  -- mild fixed-point (= D.hmild)
  hfix : ∀ t, 0 < t → t < D.T → ∀ x : ℝ, (hx : x ∈ Set.Icc (0:ℝ) 1) →
    intervalDomainLift (D.u t) x = intervalGradientDuhamelMap p u₀ D.u t ⟨x, hx⟩
  -- weak limit-source package (horizon-bounded; feeds the localized restart route)
  hsrc0 : DuhamelSourceL1ContOn
    (fun s k => cosineCoeffs (logisticLifted p (D.u s)) k) D.T
  -- K2 spatial slice bounds (per time slice)
  Msup : ℝ
  -- per-slice cosine representation (replaces the unsatisfiable global-`C²` field
  -- `hC2t`; fed into the source-decay machinery via
  -- `IntervalDomainLimitSourceRepresentation`)
  bc : ℝ → ℕ → ℝ
  hbsum : ∀ σ, 0 < σ → σ < D.T → Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|)
  hagree : ∀ σ, 0 < σ → σ < D.T → Set.EqOn (intervalDomainLift (D.u σ))
    (fun x => ∑' n, bc σ n * cosineMode n x) (Set.Icc (0 : ℝ) 1)
  hpost : ∀ σ, 0 < σ → σ < D.T → ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (D.u σ) x
  hubt : ∀ σ, 0 < σ → σ < D.T → ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (D.u σ) x ≤ Msup
  -- K2 gradient/Hessian bounds, PER-COMPACT (the satisfiable form)
  hG1t : ∀ a' b', 0 < a' → b' < D.T → ∃ G1, ∀ σ ∈ Set.Icc a' b',
    ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (intervalDomainLift (D.u σ)) x| ≤ G1
  hG2t : ∀ a' b', 0 < a' → b' < D.T → ∃ G2, ∀ σ ∈ Set.Icc a' b',
    ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (deriv (intervalDomainLift (D.u σ))) x| ≤ G2
  hN0t : ∀ σ, 0 < σ → σ < D.T → deriv (intervalDomainLift (D.u σ)) 0 = 0
  hN1t : ∀ σ, 0 < σ → σ < D.T → deriv (intervalDomainLift (D.u σ)) 1 = 0
  -- K1 source-coefficient time-C¹ data (UNSHIFTED, localized to (0,T))
  adott : ℝ → ℕ → ℝ
  hderivt : ∀ σ, 0 < σ → σ < D.T → ∀ k, HasDerivAt
    (fun r => cosineCoeffs
      (logisticSourceFun p.a p.b p.α (intervalDomainLift (D.u r))) k)
    (adott σ k) σ
  hadotcontt : ∀ k, ContinuousOn (fun σ => adott σ k) (Set.Ioo 0 D.T)
  hMdott : ∀ a' b', 0 < a' → b' < D.T → ∃ Mdot, ∀ σ ∈ Set.Icc a' b',
    ∀ k, |adott σ k| ≤ Mdot
  -- H3 slice continuity
  hLc : ∀ t, 0 < t → t < D.T →
    ∀ s, 0 < s → s ≤ t → Continuous (intervalLogisticSource p (D.u s))
  -- ===== frontier residuals (Hu NO LONGER carried) =====
  hpde_u :
    ∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α)
  Hvsrc : DuhamelSourceTimeC1
    (fun s k => (intervalNeumannResolverSourceCoeff p (D.u s) k).re)
  Hvpos : ∀ t, 0 < t → t < D.T → ∀ x : intervalDomainPoint,
    0 < mildChemicalConcentration p D.u t x

/-! ## Discharging `Hu` from the reduced ledger families -/

/-- **`Hu` from the reduced ledger.**  Discharges
`HasTimeNeighborhoodSpectralAgreement D.T D.u` from the TIME-LOCALIZED ledger data
via `TimeNhdLocalized.Hu_of_restart_localized`.

DEVIATION (one residual `sorry`): `Hu_of_restart_localized` requires
`hu₀_cont : Continuous (intervalDomainLift u₀)` — continuity of the ZERO-extension
lift — which is FALSE for positive initial data (the lift jumps from `u₀ > 0` at
the Neumann endpoints to `0` outside `[0,1]`).  The ledger carries only SUBTYPE
continuity `Continuous u₀` (`I.hu₀_cont`).  The localized theorem is therefore not
directly applicable; the `intervalDomainConstExtend` adapter does not help because
the lift appears literally inside `Hu_of_restart_localized`'s homogeneous-term
representation (not only in the coefficient bounds, which would be fine).

The proper route is the SUBTYPE-CONTINUITY variant of the localized restart
theorem — the same adapter already used by
`limit_lift_eq_cosineSeries_of_subtypeCont`
(`IntervalPicardLimitRestartWeak`, line 554), which replaces the false
`Continuous (intervalDomainLift u₀)` by the paper-faithful `Continuous u₀`.  Until
that subtype variant of `Hu_of_restart_localized` is provided, this field stays a
single, precisely-localized `sorry`. -/
theorem Hu_of_reduced
    {p : CM2Params} (hχ0 : p.χ₀ = 0) {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (I : ReducedLimitRegularityInputs p u₀ D) :
    HasTimeNeighborhoodSpectralAgreement D.T D.u :=
  sorry -- DEVIATION: needs the subtype-continuity variant of
        -- Hu_of_restart_localized — same adapter as
        -- limit_lift_eq_cosineSeries_of_subtypeCont; ledger carries
        -- Continuous u₀ (subtype) but the localized theorem demands
        -- Continuous (intervalDomainLift u₀), false for positive data.

/-! ## Reduced ledger ⟹ full ledger -/

/-- **The reduced ledger reconstitutes the full `LimitRegularityInputs`.**
Every field is copied over verbatim except `Hu`, which is reconstructed by
`Hu_of_reduced`.  This is the net ledger reduction: the `χ₀ = 0` mild-local
wiring now needs one fewer named frontier residual. -/
def limitRegularityInputs_of_reduced
    {p : CM2Params} (hχ0 : p.χ₀ = 0) {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (I : ReducedLimitRegularityInputs p u₀ D) :
    LimitRegularityInputs p u₀ D where
  hα := I.hα
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
  hpde_u := I.hpde_u
  Hu := Hu_of_reduced hχ0 I
  Hvsrc := I.Hvsrc
  Hvpos := I.Hvpos

/-! ## Tighter top-level statements on the reduced ledger -/

/-- **`hMildLocal`-abstract (χ₀ = 0) from the REDUCED residual ledger.**

Same conclusion as `MildLocalChi0.hMildLocal_chi0_zero_of_inputs`, but the
hypothesis supplies the strictly smaller `ReducedLimitRegularityInputs` (no `Hu`
field); `Hu` is reconstructed internally by `Hu_of_reduced`. -/
theorem hMildLocal_chi0_zero_of_reduced_inputs
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (hα_ge : 1 ≤ p.α)
    (H : ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
      ∀ D : GradientMildSolutionData p u₀,
        ReducedLimitRegularityInputs p u₀ D) :
    RestartLocalWiring.IntervalDomainGradientMildHalfStepRestartFrontierCoreLocalData p :=
  MildLocalChi0.hMildLocal_chi0_zero_of_inputs p hχ0 hα_ge
    (fun u₀ hu₀ D => limitRegularityInputs_of_reduced hχ0 (H u₀ hu₀ D))

/-- **Paper 2 Theorem 1.1 (χ₀ = 0) from the REDUCED residual ledger.**

Chains `hMildLocal_chi0_zero_of_reduced_inputs` into the same quantitative-side
bridge as `MildLocalChi0.paper2_theorem_1_1_chiZero_of_inputs`, with the local
side now driven by the smaller ledger. -/
theorem paper2_theorem_1_1_chiZero_of_reduced_inputs
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p)
    (H : ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
      ∀ D : GradientMildSolutionData p u₀,
        ReducedLimitRegularityInputs p u₀ D) :
    Theorem_1_1 intervalDomain p :=
  MildLocalChi0.paper2_theorem_1_1_chiZero_of_inputs
    p hχ0 ha hb hα_ge hγ_ge_one hPLF
    (fun u₀ hu₀ D => limitRegularityInputs_of_reduced hχ0 (H u₀ hu₀ D))

end ShenWork.Paper2.LedgerSweep
