/-
  ShenWork/Wiener/EWA/SourcePdeU.lean

  **χ₀<0 pointwise classical PDE for the source-form mild solution `u`.**

  Mirrors the committed χ₀=0 core `ShenWork.IntervalDomainPdeUChiZero.hpde_u_core`
  but KEEPS the chemotaxis term (`p.χ₀ < 0`, not zero).  Assembled from:

  * (4e) the time-derivative series `∂ₜu = ∑ fullSourceCoeffDot·cos`;
  * (4d) the laplacian inversion `u_xx = ∑(−λₙ)·fullSourceCoeff·cos`;
  * (4b) the chemDiv cosine inversion `∑ chemCoeff·cos = chemotaxisDiv`;
  * (4c) the logistic cosine inversion `∑ logCoeff·cos = reaction`.

  The per-mode spectral ODE `fullSourceCoeff_spectral_ode` (committed) splits
  `fullSourceCoeffDot` into `−λₙ·fullSourceCoeff + ((−χ₀)·chemCoeff + logCoeff)`;
  the three tsums then split via `tsum_add`/`tsum_mul_left`, and the chemotaxis
  leg lands as `−χ₀·chemotaxisDiv` through the definitional bridges
  `intervalDomain.chemotaxisDiv = intervalDomainChemotaxisDiv` and
  `mildChemicalConcentration = coupledChemicalConcentration`.

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.SourceSpectralODE
import ShenWork.Wiener.EWA.SourceSpectralBridges
import ShenWork.Wiener.EWA.SourceInversion
import ShenWork.Paper2.IntervalDomainPdeUChiZero

noncomputable section

namespace ShenWork.EWA

open ShenWork.IntervalDomain
  (intervalDomainPoint intervalDomain intervalDomainChemotaxisDiv)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalMildToClassical (mildChemicalConcentration)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledLogisticSourceCoeffs coupledChemicalConcentration)

/-- **`mildChemicalConcentration = coupledChemicalConcentration` (defeq bridge).**
Both unfold to `intervalNeumannResolverR p (u t₀)`. -/
theorem mildChem_eq_coupledChem (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (t₀ : ℝ) :
    mildChemicalConcentration p u t₀ = coupledChemicalConcentration p u t₀ := rfl

/-- **`intervalDomain.chemotaxisDiv = intervalDomainChemotaxisDiv` (defeq bridge).**
The structure projection of `intervalDomain` is `intervalDomainChemotaxisDiv`. -/
theorem intervalDomain_chemotaxisDiv_eq :
    intervalDomain.chemotaxisDiv = intervalDomainChemotaxisDiv := rfl

/-- **χ₀<0 pointwise classical PDE for `u`.**  The mild-to-classical assembly:
`∂ₜu = u_xx − χ₀·chemotaxisDiv + reaction`, keeping the chemotaxis term.  The
five bridge conclusions (4b–4e) and the three split summabilities are carried;
a higher assembly discharges them. -/
theorem fullSourceCoeff_pde_u (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ)
    {t₀ : ℝ} {x : intervalDomainPoint} (hx : x.1 ∈ Set.Ioo (0 : ℝ) 1)
    (htime : intervalDomain.timeDeriv u t₀ x
        = ∑' n, fullSourceCoeffDot p u u₀cos t₀ n * cosineMode n x.1)
    (hlap : intervalDomain.laplacian (u t₀) x
        = ∑' n, (-(unitIntervalCosineEigenvalue n)) * fullSourceCoeff p u u₀cos t₀ n
            * cosineMode n x.1)
    (hchemInv : (∑' n, coupledChemDivSourceCoeffs p u t₀ n * cosineMode n x.1)
        = intervalDomainChemotaxisDiv p (u t₀) (coupledChemicalConcentration p u t₀) x)
    (hlogInv : (∑' n, coupledLogisticSourceCoeffs p u t₀ n * cosineMode n x.1)
        = u t₀ x * (p.a - p.b * (u t₀ x) ^ p.α))
    (hsum_lap : Summable (fun n => unitIntervalCosineEigenvalue n
        * fullSourceCoeff p u u₀cos t₀ n * cosineMode n x.1))
    (hsum_chem : Summable (fun n => coupledChemDivSourceCoeffs p u t₀ n * cosineMode n x.1))
    (hsum_log : Summable (fun n => coupledLogisticSourceCoeffs p u t₀ n * cosineMode n x.1)) :
    intervalDomain.timeDeriv u t₀ x
      = intervalDomain.laplacian (u t₀) x
        - p.χ₀ * intervalDomain.chemotaxisDiv p (u t₀)
            (mildChemicalConcentration p u t₀) x
        + u t₀ x * (p.a - p.b * (u t₀ x) ^ p.α) := by
  -- summand-wise rewrite of `fullSourceCoeffDot·cos` via the spectral ODE.
  have hlapN : Summable (fun n => (-(unitIntervalCosineEigenvalue n))
      * fullSourceCoeff p u u₀cos t₀ n * cosineMode n x.1) := by
    simpa [neg_mul] using hsum_lap.neg
  have hchemχ : Summable (fun n => (-p.χ₀) * (coupledChemDivSourceCoeffs p u t₀ n
      * cosineMode n x.1)) := hsum_chem.mul_left _
  -- split the time series into laplacian-leg + (−χ₀)·chem-leg + log-leg.
  have hsplit : (∑' n, fullSourceCoeffDot p u u₀cos t₀ n * cosineMode n x.1)
      = (∑' n, (-(unitIntervalCosineEigenvalue n)) * fullSourceCoeff p u u₀cos t₀ n
            * cosineMode n x.1)
        + (-p.χ₀) * (∑' n, coupledChemDivSourceCoeffs p u t₀ n * cosineMode n x.1)
        + (∑' n, coupledLogisticSourceCoeffs p u t₀ n * cosineMode n x.1) := by
    have hcong : (∑' n, fullSourceCoeffDot p u u₀cos t₀ n * cosineMode n x.1)
        = ∑' n, ((-(unitIntervalCosineEigenvalue n)) * fullSourceCoeff p u u₀cos t₀ n
              * cosineMode n x.1
            + (-p.χ₀) * (coupledChemDivSourceCoeffs p u t₀ n * cosineMode n x.1)
            + coupledLogisticSourceCoeffs p u t₀ n * cosineMode n x.1) :=
      tsum_congr (fun n => by rw [fullSourceCoeff_spectral_ode p u u₀cos t₀ n]; ring)
    rw [hcong, (hlapN.add hchemχ).tsum_add hsum_log, hlapN.tsum_add hchemχ,
        tsum_mul_left]
  rw [htime, hsplit, hlap, hchemInv, hlogInv,
      intervalDomain_chemotaxisDiv_eq, mildChem_eq_coupledChem]
  ring

end ShenWork.EWA
