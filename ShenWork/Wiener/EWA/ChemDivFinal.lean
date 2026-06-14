import ShenWork.Wiener.EWA.EmbedEWA
import ShenWork.Wiener.EWA.ChemDivEval
import ShenWork.Wiener.EWA.HCoeffDischarge
import ShenWork.Wiener.EWA.ChemDivTopLevel

/-!
# EWA final composition — chemotaxis-divergence eigenvalue-ℓ¹ summability from a solution

This file ASSEMBLES the four committed discharge bricks end-to-end into a single
final theorem stating that the chemotaxis-divergence eigenvalue-weighted ℓ¹
spectral summability holds, given the documented analytic inputs about the real
Neumann solution `u`.

The four bricks chained (all committed / green on `shen_C`):

1. `embedEWA u … : EWA T 1` — build the even-real Wiener-algebra element `U` from
   the solution's slice cosine coefficients (`EmbedEWA.lean`).  Its even-real
   parity is `embedEWA_evenReal` (the `hU` input of brick 3).
2. `evalST_chemDivEWA_eq_coupledChemDivSourceLift` — the chemDiv eval sublemma
   (`ChemDivEval.lean`): the Wiener synthesis of `chemDivEWA … U` equals the
   committed real lift `coupledChemDivSourceLift p u τ.1 x` on the interior
   `(0,1)`.  This produces the `h_eval` input of brick 3.
3. `chemDiv_coeff_bound_of_EWA` — the `h_coeff` discharge (`HCoeffDischarge.lean`):
   the source coefficient is dominated by the EWA `sourceEnvelope`.
4. `chemDiv_eigenvalueSummableOn_of_EWA` — the top-level eigenvalue-ℓ¹ theorem
   (`ChemDivTopLevel.lean`).

The genuine analytic inputs — the solution's A¹/weighted-ℓ¹ regularity, the
per-mode continuity, the committed cosine-series identity, the eval-bridge factor
realizations for `U = embedEWA u …` (gradient majorant / flux-value agreement /
flux differentiability), and the time-derivative (adot/B8) data — are taken as
EXPLICIT, NAMED hypotheses.  This is the honest final form: the Wiener algebra
REDUCES the chemDiv eigenvalue-ℓ¹ summability to exactly these standard inputs.

NO `sorry`, `axiom`, `native_decide`, or `admit`.
-/

open scoped BigOperators
open ShenWork.GWA ShenWork.Wiener
open ShenWork.EWA
open ShenWork.IntervalDuhamelSourceTimeC1On
open ShenWork.IntervalCoupledRegularityBootstrap
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.PDE (intervalNeumannResolverCoeff)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted)
open ShenWork.CosineSpectrum (cosineMode)

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-- **Final composed theorem.**

Given a real Neumann solution `u : ℝ → intervalDomainPoint → ℝ` together with the
documented analytic inputs (its A¹/weighted-ℓ¹ slice regularity, per-mode
continuity, the committed cosine-series identity, the eval-bridge factor
realizations for the even embedding `U = embedEWA u …`, and the chemDiv
time-derivative data), the eigenvalue-weighted Duhamel spectral coefficients of
the chemotaxis-divergence source are summable on the window at every interior
evaluation time `t ∈ (0, T]`.

The proof fixes `U := embedEWA u …` once and chains the four committed bricks:
`embedEWA_evenReal` (gives `hU`) → `evalST_chemDivEWA_eq_coupledChemDivSourceLift`
(gives `h_eval`) → `chemDiv_coeff_bound_of_EWA` (gives `h_coeff`) →
`chemDiv_eigenvalueSummableOn_of_EWA`. -/
theorem chemDiv_eigenvalueSummableOn_of_solution
    {μ ν γ : ℝ} (hμ : 0 < μ) (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ)
    {t : ℝ} (htlo : 0 < t) (hthi : t ≤ T)
    -- A¹/weighted-ℓ¹ regularity + per-mode continuity + cosine-series (embedEWA inputs):
    (Bv : ℕ → ℝ)
    (hBv : ∀ s k, |cosineCoeffs (intervalDomainLift (u s)) k| ≤ Bv k)
    (hBvnn : ∀ k, 0 ≤ Bv k)
    (hBvsum : Summable (fun k : ℕ => (1 + (k : ℝ)) * Bv k))
    (hcont : ∀ n : ℤ, Continuous (embedModeFun u n))
    -- the eval-bridge factor realizations for `U = embedEWA u …` (regularity inputs):
    (hgrad : ∀ τ : TimeDom T, Summable fun k : ℕ =>
      |(intervalNeumannResolverCoeff p (u τ.1) k).re| * ((k : ℝ) * Real.pi))
    (h_flux_nbhd : ∀ (τ : TimeDom T), ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      evalST τ (y : WA.Circ) (GWA.incl (by omega : (0:ℕ) ≤ 1)
        (chemFluxEWA μ ν p.β γ hμ (embedEWA u hBv hBvnn hBvsum hcont)))
        = ((chemFluxLifted p (u τ.1) y : ℝ) : ℂ))
    (h_flux_diff : ∀ (τ : TimeDom T), ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ (chemFluxLifted p (u τ.1)) x)
    -- the chemDiv time-derivative data (adot/B8):
    (adot : ℝ → ℕ → ℝ)
    (h_deriv : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n,
        HasDerivWithinAt (fun r => coupledChemDivSourceCoeffs p u r n)
          (adot s n) (Set.Icc 0 T) s)
    (h_adotcont : ∀ n, ContinuousOn (fun s => adot s n) (Set.Icc 0 T))
    (Mdot : ℝ)
    (h_Mdot : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n, |adot s n| ≤ Mdot) :
    Summable (fun n => unitIntervalCosineEigenvalue n *
      |∫ s in (0 : ℝ)..t,
        Real.exp (-(t - s) * unitIntervalCosineEigenvalue n)
          * coupledChemDivSourceCoeffs p u s n|) := by
  -- Fix the even-embedding Wiener-algebra element once.
  set U : EWA T 1 := embedEWA u hBv hBvnn hBvsum hcont with hU_def
  -- Brick 1: `U` is even-real.
  have hU : EvenRealEWA U := embedEWA_evenReal u hBv hBvnn hBvsum hcont
  -- Brick 2: the chemDiv eval realization on the interior, for every slice.
  have h_eval : ∀ (τ : TimeDom T) (x : ℝ), x ∈ Set.Ioo (0 : ℝ) 1 →
      evalST τ (x : WA.Circ) (chemDivEWA μ ν γ hμ p U)
        = ((coupledChemDivSourceLift p u τ.1 x : ℝ) : ℂ) := by
    intro τ x hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hx
    exact evalST_chemDivEWA_eq_coupledChemDivSourceLift hμ p u U τ x hx hxIcc
      (hgrad τ) (h_flux_nbhd τ) (h_flux_diff τ x hx)
  -- Brick 3: the value-envelope domination `h_coeff`.
  have h_coeff : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n,
      |coupledChemDivSourceCoeffs p u s n|
        ≤ sourceEnvelope (chemDivEWA μ ν γ hμ p U) n :=
    fun s hs n => chemDiv_coeff_bound_of_EWA hμ p u U hU h_eval s hs n
  -- Brick 4: the top-level eigenvalue-ℓ¹ summability.
  exact chemDiv_eigenvalueSummableOn_of_EWA hμ p u U htlo hthi
    h_coeff adot h_deriv h_adotcont Mdot h_Mdot

end ShenWork.EWA

#print axioms ShenWork.EWA.chemDiv_eigenvalueSummableOn_of_solution
