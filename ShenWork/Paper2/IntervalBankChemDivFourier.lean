/-
  Bank field 12 (`hchemFourier`) — absolute Fourier-coefficient summability of
  the chemotaxis-divergence source slice.

  Target shape (field 12 of `BFormBankedInputs`):
    `Summable (fun n : ℤ =>
        fourierCoeff (reflCircle
          (intervalDomainConstExtend
            (fun x => intervalDomainChemotaxisDiv p u v x))) n)`
  with `u = conjugatePicardLimit p u₀ DB.T t`,
       `v = coupledChemicalConcentration p (conjugatePicardLimit p u₀ DB.T) t`.

  Analytic route (verified): the source `S = (u^m (1+v)^{-β} v_x)_x` is the spatial
  divergence of a regular flux; with `u(t) ∈ H^σ` for `σ` large enough the chain
  `v ∈ H^{σ+2}`, `Q ∈ H^σ`, `S = Q_x ∈ H^{σ-1}` lands the slice in `C²` on `[0,1]`
  (Sobolev embedding `H^{5/2+} ↪ C²`).  The landed `ℓ¹` embedding
  `fourierCoeff_reflCircle_summable_of_repr` consumes exactly that `C²`-Neumann data
  of the lift plus continuity of the (constant-extended) representative, and returns
  the target `ℤ`-Fourier summability.

  This file lands the clean conditional lemma
    `hchemFourier_of_chemDiv_C2Neumann`
  whose hypotheses (continuity of the slice + `C²`/Neumann regularity of its lift on
  `[0,1]`) are precisely the analytic content of the source being `C²`.  The H²-to-C²
  regularity bootstrap of the Picard limit is the remaining sub-residual; see the
  report.  No `sorry`/`admit`/`native_decide`/custom axiom.
-/
import ShenWork.Paper2.IntervalDomainL2StaticVDifference
import ShenWork.Paper2.IntervalBFormSpectralHchem

open Set Filter Topology

noncomputable section

namespace ShenWork.Paper2.BankChemDivFourier

open ShenWork.IntervalDomain
  (intervalDomainPoint intervalDomainLift intervalDomainConstExtend
   intervalDomainChemotaxisDiv constExtend_eq_lift_on_Icc constExtend_continuous)
open ShenWork.IntervalCosineInversion (reflCircle)
open ShenWork.IntervalCoupledRegularityBootstrap (coupledChemicalConcentration)

/-- **Conditional `ℓ¹` Fourier summability of a chemotaxis-divergence slice.**

Given the chemotaxis-divergence slice `s x = intervalDomainChemotaxisDiv p u v x`
(a function `intervalDomainPoint → ℝ`), assume:

* `hcont` — `s` is continuous on the subtype (so its constant extension to `ℝ` is
  globally continuous);
* `hC2` — the lift of `s` to `ℝ` is `C²` on `[0,1]`;
* `htend0`/`htend1` — the one-sided derivative limits of the lift vanish at the
  endpoints `0` and `1`;
* `hbc0`/`hbc1` — the lift satisfies homogeneous Neumann boundary data
  (`deriv = 0` at the endpoints).

Then the `ℤ`-indexed even-reflection Fourier coefficients of the constant extension
of `s` are absolutely summable.  This is exactly field `12` (`hchemFourier`) of
`BFormBankedInputs` for a single time slice. -/
theorem hchemFourier_of_chemDiv_C2Neumann
    (p : CM2Params) (u v : intervalDomainPoint → ℝ)
    (hcont : Continuous (fun x : intervalDomainPoint =>
      intervalDomainChemotaxisDiv p u v x))
    (hC2 : ContDiffOn ℝ 2
      (intervalDomainLift (fun x => intervalDomainChemotaxisDiv p u v x))
      (Set.Icc (0 : ℝ) 1))
    (htend0 : Filter.Tendsto
      (deriv (intervalDomainLift (fun x => intervalDomainChemotaxisDiv p u v x)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (htend1 : Filter.Tendsto
      (deriv (intervalDomainLift (fun x => intervalDomainChemotaxisDiv p u v x)))
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0))
    (hbc0 : deriv
      (intervalDomainLift (fun x => intervalDomainChemotaxisDiv p u v x)) 0 = 0)
    (hbc1 : deriv
      (intervalDomainLift (fun x => intervalDomainChemotaxisDiv p u v x)) 1 = 0) :
    Summable (fun n : ℤ =>
      fourierCoeff
        (reflCircle
          (intervalDomainConstExtend
            (fun x : intervalDomainPoint =>
              intervalDomainChemotaxisDiv p u v x))) n) := by
  refine ShenWork.Paper2.fourierCoeff_reflCircle_summable_of_repr
    (F := intervalDomainConstExtend
      (fun x : intervalDomainPoint => intervalDomainChemotaxisDiv p u v x))
    (g := intervalDomainLift
      (fun x : intervalDomainPoint => intervalDomainChemotaxisDiv p u v x))
    (constExtend_continuous hcont) hC2 ?_ htend0 htend1 hbc0 hbc1
  intro x hx
  exact constExtend_eq_lift_on_Icc hx

/-- **Slice-level discharge of bank field `12` (`hchemFourier`) for the conjugate
Picard limit.**

Specialisation of `hchemFourier_of_chemDiv_C2Neumann` to the B-form data
`u = conjugatePicardLimit p u₀ DB.T t`,
`v = coupledChemicalConcentration p (conjugatePicardLimit p u₀ DB.T) t`.

The hypotheses are the `C²`-Neumann regularity of the chemotaxis-divergence slice of
the Picard limit at time `t`; the conclusion is exactly the per-`t` body of bank field
`12`.  Quantifying over `t ∈ (0,T)` and supplying these hypotheses from the regularity
frontier produces the full field. -/
theorem hchemFourier_slice_of_limit_C2Neumann
    (p : CM2Params) (limit : ℝ → intervalDomainPoint → ℝ) (t : ℝ)
    (hcont : Continuous (fun x : intervalDomainPoint =>
      intervalDomainChemotaxisDiv p (limit t)
        (coupledChemicalConcentration p limit t) x))
    (hC2 : ContDiffOn ℝ 2
      (intervalDomainLift (fun x => intervalDomainChemotaxisDiv p (limit t)
        (coupledChemicalConcentration p limit t) x))
      (Set.Icc (0 : ℝ) 1))
    (htend0 : Filter.Tendsto
      (deriv (intervalDomainLift (fun x => intervalDomainChemotaxisDiv p (limit t)
        (coupledChemicalConcentration p limit t) x)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (htend1 : Filter.Tendsto
      (deriv (intervalDomainLift (fun x => intervalDomainChemotaxisDiv p (limit t)
        (coupledChemicalConcentration p limit t) x)))
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0))
    (hbc0 : deriv (intervalDomainLift (fun x =>
      intervalDomainChemotaxisDiv p (limit t)
        (coupledChemicalConcentration p limit t) x)) 0 = 0)
    (hbc1 : deriv (intervalDomainLift (fun x =>
      intervalDomainChemotaxisDiv p (limit t)
        (coupledChemicalConcentration p limit t) x)) 1 = 0) :
    Summable (fun n : ℤ =>
      fourierCoeff
        (reflCircle
          (intervalDomainConstExtend
            (fun x : intervalDomainPoint =>
              intervalDomainChemotaxisDiv p (limit t)
                (coupledChemicalConcentration p limit t) x))) n) :=
  hchemFourier_of_chemDiv_C2Neumann p (limit t)
    (coupledChemicalConcentration p limit t)
    hcont hC2 htend0 htend1 hbc0 hbc1

end ShenWork.Paper2.BankChemDivFourier

#print axioms ShenWork.Paper2.BankChemDivFourier.hchemFourier_of_chemDiv_C2Neumann
#print axioms ShenWork.Paper2.BankChemDivFourier.hchemFourier_slice_of_limit_C2Neumann
