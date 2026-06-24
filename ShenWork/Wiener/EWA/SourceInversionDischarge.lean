/-
  ShenWork/Wiener/EWA/SourceInversionDischarge.lean

  **χ₀<0 — conditional discharge of the two source-inversion members
  `hchemInv` / `hlogInv` carried by `realSlice_reducedCore`
  (SourceReducedCore.lean:84).**

  The reduced core carries, per interior point, the two cosine-inversion
  identities

  * `hchemInv` : `∑ₙ coupledChemDivSourceCoeffs p u t n · cos = chemotaxis div`,
  * `hlogInv`  : `∑ₙ coupledLogisticSourceCoeffs p u t n · cos = logistic reaction`,

  for `u = realSlice u_star`.  The committed analytic primitives that produce
  them are `chemDiv_source_inversion` / `logistic_source_inversion`
  (SourceInversion.lean): EACH consumes a CONTINUOUS surrogate `g : ℝ → ℝ`
  agreeing on `[0,1]` with the (zero-extension) source lift, together with the
  `ℓ¹` `ℤ`-Fourier summability of `reflCircle g`.

  The source lift `coupledChemDivSourceLift` / `coupledLogisticSourceLift` is
  `intervalDomainLift (…)`, the ZERO-extension to `ℝ` — DISCONTINUOUS at the
  endpoints unless the boundary trace already vanishes — so the lift itself can
  NOT serve as the continuous surrogate.  The paper-faithful surrogate is the
  CONSTANT extension `intervalDomainConstExtend (…)` (globally continuous via
  `constExtend_continuous`, agreeing with the lift on `[0,1]` via
  `constExtend_eq_lift_on_Icc`).  Its `reflCircle` Fourier `ℓ¹` summability is
  the landed `C²`-Neumann embedding
  `hchemFourier_of_chemDiv_C2Neumann` (chem) /
  `fourierCoeff_reflCircle_summable_of_repr` (logistic).

  So this file lands the two CONDITIONAL discharges

    `realSlice_hchemInv_of_C2Neumann`,
    `realSlice_hlogInv_of_C2Neumann`,

  whose remaining hypotheses are EXACTLY the genuine analytic content the prior
  analysis flagged as NOT among the banked feeders of `realSlice_reducedCore`:
  the `C²`-Neumann regularity of the chem/log source slice (continuity of the
  slice + `C²` of its lift on `[0,1]` + vanishing one-sided endpoint derivative
  limits + homogeneous Neumann boundary data).  These are carried as named
  hypotheses — the honest χ₀<0 frontier — and never faked.

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.SourceInversion
import ShenWork.Paper2.IntervalBankChemDivFourier
import ShenWork.Paper2.IntervalDomainL2StaticVDifference

noncomputable section

namespace ShenWork.EWA

open Set Filter Topology
open ShenWork.IntervalDomain
  (intervalDomainPoint intervalDomainLift intervalDomainConstExtend
   intervalDomainChemotaxisDiv constExtend_eq_lift_on_Icc constExtend_continuous)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalCosineInversion (reflCircle)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledLogisticSourceLift coupledLogisticSourceCoeffs
   coupledChemDivSourceLift coupledChemDivSourceCoeffs
   coupledChemicalConcentration)

/-! ### `hchemInv` — chemotaxis-divergence inversion, via the constant-extension
surrogate and the landed `C²`-Neumann Fourier `ℓ¹` embedding. -/

/-- **`hchemInv` of the `pde_u` family, discharged from `C²`-Neumann data.**

For each interior time `t ∈ Ioo 0 T` the chemotaxis-divergence source slice
`x ↦ intervalDomainChemotaxisDiv p (u t) (coupledChemicalConcentration p u t) x`
is assumed `C²`-Neumann (continuity of the slice + `C²` of its zero-extension lift
on `[0,1]` + vanishing one-sided endpoint derivative limits + homogeneous Neumann
boundary data).  The constant extension of that slice is the continuous surrogate
`g`; it agrees with `coupledChemDivSourceLift p u t` on `[0,1]`
(`constExtend_eq_lift_on_Icc`) and its `reflCircle` Fourier coefficients are
`ℓ¹`-summable (`hchemFourier_of_chemDiv_C2Neumann`).  Feeding these to
`chemDiv_source_inversion` yields the inversion identity at every interior
point. -/
theorem realSlice_hchemInv_of_C2Neumann (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) {T : ℝ}
    (hcont : ∀ t ∈ Ioo (0 : ℝ) T,
      Continuous (fun x : intervalDomainPoint =>
        intervalDomainChemotaxisDiv p (u t) (coupledChemicalConcentration p u t) x))
    (hC2 : ∀ t ∈ Ioo (0 : ℝ) T,
      ContDiffOn ℝ 2
        (intervalDomainLift (fun x => intervalDomainChemotaxisDiv p (u t)
          (coupledChemicalConcentration p u t) x)) (Icc (0 : ℝ) 1))
    (htend0 : ∀ t ∈ Ioo (0 : ℝ) T,
      Tendsto (deriv (intervalDomainLift (fun x => intervalDomainChemotaxisDiv p (u t)
        (coupledChemicalConcentration p u t) x)))
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0))
    (htend1 : ∀ t ∈ Ioo (0 : ℝ) T,
      Tendsto (deriv (intervalDomainLift (fun x => intervalDomainChemotaxisDiv p (u t)
        (coupledChemicalConcentration p u t) x)))
        (nhdsWithin (1 : ℝ) (Iio 1)) (nhds 0))
    (hbc0 : ∀ t ∈ Ioo (0 : ℝ) T,
      deriv (intervalDomainLift (fun x => intervalDomainChemotaxisDiv p (u t)
        (coupledChemicalConcentration p u t) x)) 0 = 0)
    (hbc1 : ∀ t ∈ Ioo (0 : ℝ) T,
      deriv (intervalDomainLift (fun x => intervalDomainChemotaxisDiv p (u t)
        (coupledChemicalConcentration p u t) x)) 1 = 0) :
    ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : intervalDomainPoint,
      x.1 ∈ Ioo (0 : ℝ) 1 →
      (∑' n, coupledChemDivSourceCoeffs p u t n * cosineMode n x.1)
        = intervalDomainChemotaxisDiv p (u t)
            (coupledChemicalConcentration p u t) x := by
  intro t ht x hx
  set s : intervalDomainPoint → ℝ := fun y =>
    intervalDomainChemotaxisDiv p (u t) (coupledChemicalConcentration p u t) y with hs
  refine chemDiv_source_inversion p u t (intervalDomainConstExtend s)
    (constExtend_continuous (hcont t ht)) ?_ ?_ hx
  · -- surrogate agrees with the lift on `[0,1]` (lift defeq `coupledChemDivSourceLift`)
    intro y hy
    show intervalDomainConstExtend s y = coupledChemDivSourceLift p u t y
    exact constExtend_eq_lift_on_Icc hy
  · -- `ℓ¹` Fourier summability of `reflCircle` of the surrogate
    exact ShenWork.Paper2.BankChemDivFourier.hchemFourier_of_chemDiv_C2Neumann
      p (u t) (coupledChemicalConcentration p u t)
      (hcont t ht) (hC2 t ht) (htend0 t ht) (htend1 t ht) (hbc0 t ht) (hbc1 t ht)

/-! ### `hlogInv` — logistic inversion, via the constant-extension surrogate and
the landed `reflCircle` Fourier `ℓ¹` embedding from `C²`-Neumann data. -/

/-- **`hlogInv` of the `pde_u` family, discharged from `C²`-Neumann data.**

For each interior time `t ∈ Ioo 0 T` the logistic source slice
`intervalLogisticSource p (u t)` is assumed `C²`-Neumann (continuity + `C²` of its
zero-extension lift on `[0,1]` + vanishing one-sided endpoint derivative limits +
homogeneous Neumann boundary data).  The constant extension of that slice is the
continuous surrogate `g`; it agrees with `coupledLogisticSourceLift p u t` on
`[0,1]` (`constExtend_eq_lift_on_Icc`) and its `reflCircle` Fourier coefficients
are `ℓ¹`-summable (`fourierCoeff_reflCircle_summable_of_repr`).  Feeding these to
`logistic_source_inversion` yields the inversion identity at every interior
point. -/
theorem realSlice_hlogInv_of_C2Neumann (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) {T : ℝ}
    (hcont : ∀ t ∈ Ioo (0 : ℝ) T,
      Continuous (fun x : intervalDomainPoint => intervalLogisticSource p (u t) x))
    (hC2 : ∀ t ∈ Ioo (0 : ℝ) T,
      ContDiffOn ℝ 2
        (intervalDomainLift (intervalLogisticSource p (u t))) (Icc (0 : ℝ) 1))
    (htend0 : ∀ t ∈ Ioo (0 : ℝ) T,
      Tendsto (deriv (intervalDomainLift (intervalLogisticSource p (u t))))
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0))
    (htend1 : ∀ t ∈ Ioo (0 : ℝ) T,
      Tendsto (deriv (intervalDomainLift (intervalLogisticSource p (u t))))
        (nhdsWithin (1 : ℝ) (Iio 1)) (nhds 0))
    (hbc0 : ∀ t ∈ Ioo (0 : ℝ) T,
      deriv (intervalDomainLift (intervalLogisticSource p (u t))) 0 = 0)
    (hbc1 : ∀ t ∈ Ioo (0 : ℝ) T,
      deriv (intervalDomainLift (intervalLogisticSource p (u t))) 1 = 0) :
    ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : intervalDomainPoint,
      x.1 ∈ Ioo (0 : ℝ) 1 →
      (∑' n, coupledLogisticSourceCoeffs p u t n * cosineMode n x.1)
        = u t x * (p.a - p.b * (u t x) ^ p.α) := by
  intro t ht x hx
  set s : intervalDomainPoint → ℝ := intervalLogisticSource p (u t) with hs
  refine logistic_source_inversion p u t (intervalDomainConstExtend s)
    (constExtend_continuous (hcont t ht)) ?_ ?_ hx
  · -- surrogate agrees with the lift on `[0,1]` (lift defeq `coupledLogisticSourceLift`)
    intro y hy
    show intervalDomainConstExtend s y = coupledLogisticSourceLift p u t y
    exact constExtend_eq_lift_on_Icc hy
  · -- `ℓ¹` Fourier summability of `reflCircle` of the surrogate, from `C²`-Neumann
    refine ShenWork.Paper2.fourierCoeff_reflCircle_summable_of_repr
      (F := intervalDomainConstExtend s)
      (g := intervalDomainLift s)
      (constExtend_continuous (hcont t ht)) (hC2 t ht) ?_
      (htend0 t ht) (htend1 t ht) (hbc0 t ht) (hbc1 t ht)
    intro y hy
    exact constExtend_eq_lift_on_Icc hy

end ShenWork.EWA
