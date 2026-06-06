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
  weak-source hypothesis `hsrc0 : DuhamelSourceL1Cont …` is itself produced from
  the SAME K2/K1-unshifted families by
  `DuhamelSourceL1Cont.ofTimeC1 ∘ limitSource_duhamelSourceTimeC1`.

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
open ShenWork.IntervalPicardLimitRestartWeak (DuhamelSourceL1Cont)
open ShenWork.IntervalPicardLimitSourceData (limitSource_duhamelSourceTimeC1)
open ShenWork.IntervalPicardLimitTimeNhd (Hu_of_restart)
open ShenWork.Paper2
open ShenWork.Paper2.MildLocalChi0 (LimitRegularityInputs)

noncomputable section

namespace ShenWork.Paper2.LedgerSweep

/-! ## The reduced residual ledger (drops the now-derivable `Hu`) -/

/-- **`ReducedLimitRegularityInputs p u₀ D`** — `LimitRegularityInputs` with the
`Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u` field deleted.

`Hu` is no longer a frontier residual: it is derivable from the remaining fields
via the general restart identity (`Hu_of_restart`), with the weak-source package
`hsrc0` reconstructed from the K2/K1-unshifted families by
`DuhamelSourceL1Cont.ofTimeC1 ∘ limitSource_duhamelSourceTimeC1`.  Every field
below also appears verbatim in `LimitRegularityInputs`; this structure is strictly
smaller (one fewer named hypothesis). -/
structure ReducedLimitRegularityInputs
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (D : GradientMildSolutionData p u₀) where
  -- structural regime parameters
  hα : 1 ≤ p.α
  ha : 0 ≤ p.a
  hb : 0 ≤ p.b
  -- H1 datum data
  hu₀_cont : Continuous (intervalDomainLift u₀)
  M₀ : ℝ
  hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀
  -- mild fixed-point (= D.hmild)
  hfix : ∀ t, 0 < t → ∀ x : ℝ, (hx : x ∈ Set.Icc (0:ℝ) 1) →
    intervalDomainLift (D.u t) x = intervalGradientDuhamelMap p u₀ D.u t ⟨x, hx⟩
  -- K2 spatial slice bounds (per time slice)
  Msup : ℝ
  G1 : ℝ
  G2 : ℝ
  hC2t : ∀ σ, ContDiffOn ℝ 2 (intervalDomainLift (D.u σ)) (Set.Icc (0 : ℝ) 1)
  hpost : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (D.u σ) x
  hubt : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (D.u σ) x ≤ Msup
  hG1t : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
    |deriv (intervalDomainLift (D.u σ)) x| ≤ G1
  hG2t : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
    |deriv (deriv (intervalDomainLift (D.u σ))) x| ≤ G2
  hN0t : ∀ σ, deriv (intervalDomainLift (D.u σ)) 0 = 0
  hN1t : ∀ σ, deriv (intervalDomainLift (D.u σ)) 1 = 0
  -- K1 source-coefficient time-C¹ data (unshifted)
  adott : ℝ → ℕ → ℝ
  hderivt : ∀ σ k, HasDerivAt
    (fun r => cosineCoeffs
      (logisticSourceFun p.a p.b p.α (intervalDomainLift (D.u r))) k)
    (adott σ k) σ
  hadotcontt : ∀ k, Continuous (fun σ => adott σ k)
  Mdott : ℝ
  hMdott : ∀ σ, 0 ≤ σ → ∀ k, |adott σ k| ≤ Mdott
  -- K1 for the t/2-shifted source family
  adotS : ℝ → ℝ → ℕ → ℝ
  hderivS : ∀ t, ∀ σ k, HasDerivAt
    (fun r => cosineCoeffs
      (logisticSourceFun p.a p.b p.α (intervalDomainLift (D.u (t/2 + r)))) k)
    (adotS t σ k) σ
  hadotcontS : ∀ t, ∀ k, Continuous (fun σ => adotS t σ k)
  MdotS : ℝ
  hMdotS : ∀ t, ∀ σ, 0 ≤ σ → ∀ k, |adotS t σ k| ≤ MdotS
  -- H3 slice continuity
  hLc : ∀ t, 0 < t → t < D.T →
    ∀ s, 0 < s → s ≤ t → Continuous (logisticLifted p (D.u s))
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
  HsupNorm : IntervalDomainSupNormDerivativeNonposOn D.u (Set.Ioo (0 : ℝ) D.T)
  Hvpos : ∀ t, 0 < t → t < D.T → ∀ x : intervalDomainPoint,
    0 < mildChemicalConcentration p D.u t x

/-! ## Discharging `Hu` from the reduced ledger families -/

/-- **The weak limit source package from the reduced ledger.**  Build
`DuhamelSourceL1Cont (fun s k => cosineCoeffs (logisticLifted p (D.u s)) k)` from
the K2 slice bounds and the K1 unshifted source-coefficient time-`C¹` data via the
forgetful map `DuhamelSourceL1Cont.ofTimeC1` applied to
`limitSource_duhamelSourceTimeC1`.  No hypothesis beyond the reduced ledger. -/
def weakSource_of_reduced
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (I : ReducedLimitRegularityInputs p u₀ D) :
    DuhamelSourceL1Cont
      (fun s k => cosineCoeffs (logisticLifted p (D.u s)) k) :=
  DuhamelSourceL1Cont.ofTimeC1
    (limitSource_duhamelSourceTimeC1 p D.u I.hα I.ha I.hb
      I.hC2t I.hpost I.hubt I.hG1t I.hG2t I.hN0t I.hN1t
      I.adott I.hderivt I.hadotcontt I.hMdott)

/-- **`Hu` from the reduced ledger.**  Discharges
`HasTimeNeighborhoodSpectralAgreement D.T D.u` via `Hu_of_restart`, feeding the
weak-source package produced by `weakSource_of_reduced` and the remaining reduced
families (K2 slice bounds, the `t/2`-shifted K1 family, and the H3 slice
continuity). -/
theorem Hu_of_reduced
    {p : CM2Params} (hχ0 : p.χ₀ = 0) {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (I : ReducedLimitRegularityInputs p u₀ D) :
    HasTimeNeighborhoodSpectralAgreement D.T D.u :=
  Hu_of_restart hχ0 D.u I.hα I.ha I.hb I.hu₀_cont I.hu₀_bound I.hfix
    (weakSource_of_reduced I)
    I.hC2t I.hpost I.hubt I.hG1t I.hG2t I.hN0t I.hN1t
    I.adotS I.hderivS I.hadotcontS I.hMdotS I.hLc

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
  Msup := I.Msup
  G1 := I.G1
  G2 := I.G2
  hC2t := I.hC2t
  hpost := I.hpost
  hubt := I.hubt
  hG1t := I.hG1t
  hG2t := I.hG2t
  hN0t := I.hN0t
  hN1t := I.hN1t
  adott := I.adott
  hderivt := I.hderivt
  hadotcontt := I.hadotcontt
  Mdott := I.Mdott
  hMdott := I.hMdott
  adotS := I.adotS
  hderivS := I.hderivS
  hadotcontS := I.hadotcontS
  MdotS := I.MdotS
  hMdotS := I.hMdotS
  hLc := I.hLc
  hpde_u := I.hpde_u
  Hu := Hu_of_reduced hχ0 I
  Hvsrc := I.Hvsrc
  HsupNorm := I.HsupNorm
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
