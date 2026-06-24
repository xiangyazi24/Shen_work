/-
  ShenWork/Wiener/EWA/SourceFullCoeffSlabSummable.lean

  **χ₀<0 capstone — discharging the carried `hsumE` slab eigenvalue-ℓ¹
  hypothesis of `realSlice_classicalRegularity` from the landed atoms.**

  `realSlice_classicalRegularity` (`SourceClassicalRegularity.lean:120`) — the
  `classicalRegularity` feeder of `CoupledDuhamelReducedClassicalCore` for the EWA
  source-form slice `u := realSlice u_star` — carries, among its inputs, the
  *slab* eigenvalue-ℓ¹ summability of the full source coefficient:

  ```
  hsumE : ∀ t ∈ Set.Ioo (0 : ℝ) T,
    Summable (fun n => unitIntervalCosineEigenvalue n *
      |fullSourceCoeff p (realSlice u_star) u₀cos t n|)
  ```

  This file shows that `hsumE` is NOT an independent frontier input: it reduces,
  per interior time `t`, to exactly the data already carried elsewhere in
  `realSlice_reducedCore` plus the landed chemDiv eigenvalue-ℓ¹ capstone.  Two
  forms are provided.

  1. `fullSourceCoeff_eigenvalueSummable_slab_of_chemLeg` — the pure assembly
     bridge.  It consumes, BY NAME, the committed three-way assembler
     `ShenWork.EWA.fullSourceCoeff_eigenvalue_summable`
     (`SourceStrongSolution.lean:168`), feeding it for each `t ∈ (0,T)`:
       * the heat-datum bound `hu0bd` (already carried by `realSlice_reducedCore`),
       * the logistic `DuhamelSourceTimeC1` package `hlog` (already carried), and
       * the chemDiv-Duhamel leg eigenvalue-ℓ¹ summability `hchemLeg`, supplied
         per `t`.
     The result is precisely the `hsumE` shape.

  2. `fullSourceCoeff_eigenvalueSummable_slab_of_chemReg` — the same slab fact
     with the chemDiv leg DISCHARGED (not carried) at every interior `t` from the
     landed unconditional capstone via
     `ShenWork.EWA.chemDivDuhamel_eigenvalue_summable`
     (`SourceStrongSolution.lean:130`, a thin restatement of
     `chemDiv_eigenvalueSummableOn_uncond`, `ChemDivUncond.lean:187`).  Here the
     chemDiv regularity side-inputs (`hGcont`, the early-window spatial
     regularity `hM/hLiftCont/hLiftBd`, and the shifted A¹/eval-bridge package
     `Bv/hBv/.../h_flux_diff`) are taken at the slab horizon `T` and reused for
     every `t`; the time chooser `τ₀` is taken as `t/2` so `0 < τ₀ < t ≤ T`.

  Net effect: the carried `hsumE` of `realSlice_classicalRegularity` is replaced
  by inputs that are EITHER already carried elsewhere in the reduced-core
  assembly (`hu0bd`, `hlog`) OR are the standard chemDiv regularity package that
  the landed capstone already consumes — no new analytic frontier.

  Self-verified with `lake env lean` on this file only.

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.SourceStrongSolution

open scoped BigOperators
open ShenWork.GWA ShenWork.Wiener
open ShenWork.IntervalDuhamelClosedC2 (duhamelSpectralCoeff DuhamelSourceTimeC1)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledChemDivSourceLift coupledLogisticSourceCoeffs)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.PDE (intervalNeumannResolverCoeff)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted)

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-! ### Form 1 — the slab bridge from a per-time chemDiv leg. -/

/-- **Slab eigenvalue-ℓ¹ summability of `fullSourceCoeff` from the chemDiv leg.**

For every interior time `t ∈ (0,T)`, the heat-datum bound `hu0bd`, the logistic
`DuhamelSourceTimeC1` package `hlog`, and the chemDiv-Duhamel leg eigenvalue-ℓ¹
summability `hchemLeg t` assemble — via the committed three-way assembler
`fullSourceCoeff_eigenvalue_summable` — into the full source coefficient's
eigenvalue-ℓ¹ summability.  This is exactly the `hsumE` shape carried by
`realSlice_classicalRegularity`. -/
theorem fullSourceCoeff_eigenvalueSummable_slab_of_chemLeg
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ)
    {Mu0 : ℝ} (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hlog : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p u))
    (hchemLeg : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      Summable (fun n => unitIntervalCosineEigenvalue n *
        |duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t n|)) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T,
      Summable (fun n => unitIntervalCosineEigenvalue n *
        |fullSourceCoeff p u u₀cos t n|) := by
  intro t ht
  exact fullSourceCoeff_eigenvalue_summable p u u₀cos ht.1 hu0bd
    (hchemLeg t ht) hlog

/-! ### Form 2 — the slab fact with the chemDiv leg discharged from the capstone. -/

/-- **Slab eigenvalue-ℓ¹ summability of `fullSourceCoeff`, chemDiv leg discharged.**

The carried `hsumE` of `realSlice_classicalRegularity` is reduced to inputs that
are EITHER already carried elsewhere in `realSlice_reducedCore` (`hu0bd`, `hlog`)
OR are the standard chemDiv regularity package that the landed unconditional
capstone `chemDivDuhamel_eigenvalue_summable` already consumes.

For each interior time `t ∈ (0,T)` the chemDiv leg is discharged at the chooser
`τ₀ := t/2` (so `0 < τ₀ < t ≤ T`); the chemDiv regularity side-inputs
(`hGcont`, the early-window spatial regularity `hM/hLiftCont/hLiftBd`, and the
shifted A¹/eval-bridge package `Bv/hBv/…/h_flux_diff`) are stated at the slab
horizon `T` and reused for every interior time. -/
theorem fullSourceCoeff_eigenvalueSummable_slab_of_chemReg
    {μ ν γ : ℝ} (hμ : 0 < μ) (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ)
    {Mu0 : ℝ} (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hlog : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p u))
    -- chemDiv per-mode time-continuity:
    (hGcont : ∀ n, Continuous (fun s => coupledChemDivSourceCoeffs p u s n))
    -- chemDiv early-window spatial regularity (uniform over the whole slab):
    {M : ℝ} (hM : 0 ≤ M)
    (hLiftCont : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ContinuousOn (coupledChemDivSourceLift p u s) (Set.Icc (0 : ℝ) 1))
    (hLiftBd : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |coupledChemDivSourceLift p u s x| ≤ M)
    -- chemDiv shifted A¹/eval-bridge package (uniform over the slab via `τ₀ ≤ T`):
    (Bv : ℝ → ℕ → ℝ)
    (hBv : ∀ τ₀ : ℝ, 0 < τ₀ → τ₀ ≤ T →
      ∀ s k, |cosineCoeffs (intervalDomainLift ((fun s => u (s + τ₀)) s)) k| ≤ Bv τ₀ k)
    (hBvnn : ∀ τ₀ : ℝ, ∀ k, 0 ≤ Bv τ₀ k)
    (hBvsum : ∀ τ₀ : ℝ, Summable (fun k : ℕ => (1 + (k : ℝ)) * Bv τ₀ k))
    (hcont : ∀ τ₀ : ℝ, ∀ n : ℤ, Continuous (embedModeFun (fun s => u (s + τ₀)) n))
    (hgrad : ∀ τ₀ : ℝ, ∀ τ : TimeDom T, Summable fun k : ℕ =>
      |(intervalNeumannResolverCoeff p ((fun s => u (s + τ₀)) τ.1) k).re|
        * ((k : ℝ) * Real.pi))
    (h_flux_nbhd : ∀ τ₀ : ℝ, ∀ (hτ0 : 0 < τ₀) (hτT : τ₀ ≤ T),
      ∀ (τ : TimeDom T), ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      evalST τ (y : WA.Circ) (GWA.incl (by omega : (0:ℕ) ≤ 1)
        (chemFluxEWA μ ν p.β γ hμ
          (embedEWA (fun s => u (s + τ₀))
            (hBv τ₀ hτ0 hτT) (hBvnn τ₀) (hBvsum τ₀) (hcont τ₀))))
        = ((chemFluxLifted p ((fun s => u (s + τ₀)) τ.1) y : ℝ) : ℂ))
    (h_flux_diff : ∀ τ₀ : ℝ, ∀ (τ : TimeDom T), ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ (chemFluxLifted p ((fun s => u (s + τ₀)) τ.1)) x) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T,
      Summable (fun n => unitIntervalCosineEigenvalue n *
        |fullSourceCoeff p u u₀cos t n|) := by
  refine fullSourceCoeff_eigenvalueSummable_slab_of_chemLeg p u u₀cos hu0bd hlog ?_
  intro t ht
  -- chooser: `τ₀ = t/2`, giving `0 < τ₀ < t ≤ T`.
  have htlo : 0 < t := ht.1
  have hthi : t ≤ T := ht.2.le
  set τ₀ : ℝ := t / 2 with hτ₀def
  have hτ0 : 0 < τ₀ := by rw [hτ₀def]; linarith
  have hτt : τ₀ < t := by rw [hτ₀def]; linarith
  have hτT : τ₀ ≤ T := le_trans hτt.le hthi
  -- early-window spatial regularity restricted from the slab `Icc 0 T` to `Icc 0 τ₀`:
  have hLiftCont' : ∀ s ∈ Set.Icc (0 : ℝ) τ₀,
      ContinuousOn (coupledChemDivSourceLift p u s) (Set.Icc (0 : ℝ) 1) :=
    fun s hs => hLiftCont s ⟨hs.1, le_trans hs.2 hτT⟩
  have hLiftBd' : ∀ s ∈ Set.Icc (0 : ℝ) τ₀, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |coupledChemDivSourceLift p u s x| ≤ M :=
    fun s hs x hx => hLiftBd s ⟨hs.1, le_trans hs.2 hτT⟩ x hx
  exact chemDivDuhamel_eigenvalue_summable hμ p u htlo hthi hτ0 hτt hGcont hM
    hLiftCont' hLiftBd' (Bv τ₀) (hBv τ₀ hτ0 hτT) (hBvnn τ₀) (hBvsum τ₀)
    (hcont τ₀) (hgrad τ₀) (h_flux_nbhd τ₀ hτ0 hτT) (h_flux_diff τ₀)

end ShenWork.EWA

#print axioms ShenWork.EWA.fullSourceCoeff_eigenvalueSummable_slab_of_chemLeg
#print axioms ShenWork.EWA.fullSourceCoeff_eigenvalueSummable_slab_of_chemReg
