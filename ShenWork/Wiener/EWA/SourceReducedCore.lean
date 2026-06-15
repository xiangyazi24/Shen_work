/-
  ShenWork/Wiener/EWA/SourceReducedCore.lean

  **χ₀<0 capstone — the reduced coupled-Duhamel classical core and the local
  classical-existence package for the EWA source-form realized slice.**

  This file is the FINAL ASSEMBLY of the χ₀<0 EWA slice.  It plugs the four
  committed feeders for `u := realSlice u_star` into the GENERIC reduced core
  `CoupledDuhamelReducedClassicalCore` and then chains, through the committed
  reduced→full discharge and the regularity bootstrap, to the local-existence
  package
    `∃ u v, IsPaper2ClassicalSolution intervalDomain p T u v
            ∧ InitialTrace intervalDomain u₀ u`.

  The four feeders supply the four reduced-core fields:

  * `u_pos`              ← `realSlice_pos`              (SourcePositivity.lean)
  * `pde_u`             ← `fullSourceCoeff_pde_u`      (SourcePdeU.lean)
  * `classicalRegularity` ← `realSlice_classicalRegularity`
                                                       (SourceClassicalRegularity.lean)
  * `initialTrace`      ← `realSlice_initialTrace`     (SourceInitialTrace.lean)

  The reduced core's `classicalRegularity` field is stated with
  `coupledChemicalConcentration p (realSlice u_star)`, while the feeder produces
  it with `mildChemicalConcentration p (realSlice u_star)`; both unfold to
  `fun t => intervalNeumannResolverR p (realSlice u_star t)`, so they are
  DEFINITIONALLY equal and the feeder discharges the field directly.

  Every input the feeders carry — the slab `realizes`, the eigenvalue-ℓ¹
  summabilities, the chemDiv/logistic `DuhamelSourceTimeC1` packages, the
  spectral-inversion atoms feeding `pde_u`, the trace/defect atoms, the resolver
  endpoint/`Hv` atoms, and the heat-floor positivity atoms — is carried here as a
  NAMED hypothesis.  These are the honest χ₀<0 frontier.  The local-existence
  step additionally carries the positive-datum admissibility `hu₀` and the
  Duhamel fixed-point identity `hfp` for the realized slice.

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.SourcePositivity
import ShenWork.Wiener.EWA.SourcePdeU
import ShenWork.Wiener.EWA.SourceClassicalRegularity
import ShenWork.Wiener.EWA.SourceInitialTrace
import ShenWork.PDE.IntervalCoupledClassicalCoreDischarge

noncomputable section

namespace ShenWork.EWA

open ShenWork.GWA ShenWork.Wiener
open ShenWork.IntervalDomain
  (intervalDomainPoint intervalDomain intervalDomainLift)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalMildToClassical (mildChemicalConcentration)
open ShenWork.Paper2
  (SourceCoeffQuadraticDecay InitialTrace PositiveInitialDatum
    IsPaper2ClassicalSolution)
open ShenWork.IntervalResolverDirectTimeRegularity (HasResolverDirectSpectralData)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledLogisticSourceCoeffs
    coupledChemicalConcentration CoupledDuhamelReducedClassicalCore
    regularityBootstrap_of_coupledDuhamel_reducedClassicalCore)
open ShenWork.IntervalDomainExistence
  (RegularityBootstrap localExistence_of_fp_and_regularity
    intervalDuhamelOperator)

variable {T : ℝ}

/-! ### Defeq bridge: the two chemical-concentration fields coincide. -/

/-- `mildChemicalConcentration p u = coupledChemicalConcentration p u`: both
unfold to `fun t => intervalNeumannResolverR p (u t)`. -/
theorem mildChem_eq_coupledChem_fun (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) :
    mildChemicalConcentration p u = coupledChemicalConcentration p u := rfl

/-! ### PART 1a — the reduced coupled-Duhamel classical core. -/

/-- **The χ₀<0 reduced coupled-Duhamel classical core for the realized slice.**

For `u := realSlice u_star` the 4-field `CoupledDuhamelReducedClassicalCore`
holds, assembled from the four committed feeders.  All feeder inputs are carried
as named hypotheses (the honest χ₀<0 atoms). -/
theorem realSlice_reducedCore (p : CM2Params) (u_star : EWA T 1)
    (u₀ : intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ)
    {Mu0 : ℝ} (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    -- positivity (heat-floor) atoms:
    {u₀E : WA 1} {δ ρ : ℝ} (hδρ : 0 < δ - ρ)
    (hheat : UniformFloor (heatEWA (T := T) u₀E) δ)
    (hu_ball : u_star ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ)
    -- `pde_u` spectral-inversion atoms (per interior point, fed from `realizes`):
    (htime : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : intervalDomainPoint,
      x.1 ∈ Set.Ioo (0 : ℝ) 1 →
      intervalDomain.timeDeriv (realSlice u_star) t x
        = ∑' n, fullSourceCoeffDot p (realSlice u_star) u₀cos t n * cosineMode n x.1)
    (hlap : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : intervalDomainPoint,
      x.1 ∈ Set.Ioo (0 : ℝ) 1 →
      intervalDomain.laplacian (realSlice u_star t) x
        = ∑' n, (-(unitIntervalCosineEigenvalue n))
            * fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x.1)
    (hchemInv : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : intervalDomainPoint,
      x.1 ∈ Set.Ioo (0 : ℝ) 1 →
      (∑' n, coupledChemDivSourceCoeffs p (realSlice u_star) t n * cosineMode n x.1)
        = ShenWork.IntervalDomain.intervalDomainChemotaxisDiv p (realSlice u_star t)
            (coupledChemicalConcentration p (realSlice u_star) t) x)
    (hlogInv : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : intervalDomainPoint,
      x.1 ∈ Set.Ioo (0 : ℝ) 1 →
      (∑' n, coupledLogisticSourceCoeffs p (realSlice u_star) t n * cosineMode n x.1)
        = realSlice u_star t x
            * (p.a - p.b * (realSlice u_star t x) ^ p.α))
    (hsum_lap : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : intervalDomainPoint,
      x.1 ∈ Set.Ioo (0 : ℝ) 1 →
      Summable (fun n => unitIntervalCosineEigenvalue n
        * fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x.1))
    (hsum_chem : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : intervalDomainPoint,
      x.1 ∈ Set.Ioo (0 : ℝ) 1 →
      Summable (fun n =>
        coupledChemDivSourceCoeffs p (realSlice u_star) t n * cosineMode n x.1))
    (hsum_log : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : intervalDomainPoint,
      x.1 ∈ Set.Ioo (0 : ℝ) 1 →
      Summable (fun n =>
        coupledLogisticSourceCoeffs p (realSlice u_star) t n * cosineMode n x.1))
    -- classical-regularity atoms:
    (hchem : DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p (realSlice u_star)))
    (hlog : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p (realSlice u_star)))
    (hsumE : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      Summable (fun n => unitIntervalCosineEigenvalue n *
        |fullSourceCoeff p (realSlice u_star) u₀cos t n|))
    (hrealizes : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (realSlice u_star t) x
        = ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x)
    (htimeDeriv : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : intervalDomainPoint,
      deriv (fun s : ℝ => realSlice u_star s x) t
        = ∑' n, fullSourceCoeffDot p (realSlice u_star) u₀cos t n * cosineMode n x.1)
    (hdiffU : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : intervalDomainPoint,
      DifferentiableAt ℝ (fun s : ℝ => realSlice u_star s x) t)
    (huNE0 : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      intervalDomainLift (realSlice u_star t) 0 ≠ 0)
    (huNE1 : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      intervalDomainLift (realSlice u_star t) 1 ≠ 0)
    (hdecay : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      SourceCoeffQuadraticDecay p (realSlice u_star t))
    (Hv : HasResolverDirectSpectralData T
      (mildChemicalConcentration p (realSlice u_star)) p)
    (Hvpos : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : intervalDomainPoint,
      0 < mildChemicalConcentration p (realSlice u_star) t x)
    -- initial-trace atoms:
    (hT : (0 : ℝ) < T)
    (hu0cos : Summable (fun n => |u₀cos n|))
    (hrecon : ∀ x : intervalDomainPoint,
      u₀ x = ∑' n, u₀cos n * cosineMode n x.1)
    (hdefect : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      Summable (fun n =>
        |fullSourceCoeff p (realSlice u_star) u₀cos t n - u₀cos n|))
    (htrace : Filter.Tendsto
      (fun t => ∑' n,
        |fullSourceCoeff p (realSlice u_star) u₀cos t n - u₀cos n|)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) :
    CoupledDuhamelReducedClassicalCore p T u₀ (realSlice u_star) := by
  refine
    { u_pos := ?_
      pde_u := ?_
      classicalRegularity := ?_
      initialTrace := ?_ }
  · -- positivity from the heat floor on the ball
    intro t x ht htT
    exact realSlice_pos hδρ hheat hu_ball ⟨ht.le, htT.le⟩ x
  · -- pointwise χ₀<0 PDE from the spectral feeder, fed per interior point
    intro t x ht htT hx
    have hxIoo : x.1 ∈ Set.Ioo (0 : ℝ) 1 := hx
    have htIoo : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht, htT⟩
    have hpde := fullSourceCoeff_pde_u p (realSlice u_star) u₀cos hxIoo
      (htime t htIoo x hxIoo) (hlap t htIoo x hxIoo) (hchemInv t htIoo x hxIoo)
      (hlogInv t htIoo x hxIoo) (hsum_lap t htIoo x hxIoo)
      (hsum_chem t htIoo x hxIoo) (hsum_log t htIoo x hxIoo)
    -- the feeder concludes with `mildChemicalConcentration`; the reduced core
    -- needs `coupledChemicalConcentration` — these are definitionally equal.
    exact hpde
  · -- classical regularity; mild = coupled concentration definitionally
    exact realSlice_classicalRegularity p u_star u₀cos hu0bd hchem hlog hsumE
      hrealizes htimeDeriv hdiffU huNE0 huNE1 hdecay Hv Hvpos
  · -- initial trace
    exact realSlice_initialTrace p u_star u₀cos u₀ hT hu0cos hrecon hrealizes
      hdefect htrace

/-! ### PART 1b — the local classical-existence package. -/

/-- **The χ₀<0 local classical-existence package for the realized slice.**

Chaining the reduced core through the committed reduced→bootstrap discharge and
`localExistence_of_fp_and_regularity`, the realized slice launches a local
classical solution with the required initial trace.  The conclusion is the
continuation-horizon existence package `∃ Tmax > 0, …` — exactly the `hlocal`
shape consumed by the restart-and-glue wiring of the χ₀<0 headline.  In addition
to the reduced core's carried atoms, this carries the positive-datum
admissibility `hu₀` and the interval-Duhamel fixed-point identity `hfp` for the
realized slice. -/
theorem realSlice_localClassicalSolution (p : CM2Params) (u_star : EWA T 1)
    (u₀ : intervalDomainPoint → ℝ)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hfp : ∀ t x, 0 ≤ t → t ≤ T →
      realSlice u_star t x = intervalDuhamelOperator p u₀ (realSlice u_star) t x)
    (C : CoupledDuhamelReducedClassicalCore p T u₀ (realSlice u_star))
    (hT : (0 : ℝ) < T) :
    ∃ Tmax > 0, ∃ u v, IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u₀ u := by
  have hreg : RegularityBootstrap p T u₀ (realSlice u_star) :=
    regularityBootstrap_of_coupledDuhamel_reducedClassicalCore p C
  exact localExistence_of_fp_and_regularity p u₀ hu₀ hT hfp hreg

end ShenWork.EWA
