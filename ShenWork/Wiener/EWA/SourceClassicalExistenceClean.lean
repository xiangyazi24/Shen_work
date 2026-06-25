import ShenWork.Wiener.EWA.SourceRealizesClean
import ShenWork.Wiener.EWA.SourceClassicalExistence

/-!
# EWA capstone (χ₀<0) — `realizes`-DISCHARGED end-to-end spatial classical existence

This file composes the two committed capstones:

* `sourceClassical_spatial_existence_of_fixedPoint`
  (`SourceClassicalExistence.lean:247`) — concludes the χ₀<0 spatial classical slice
  but TAKES the cosine-series realization identity `realizes` as a hypothesis.
* `realizes_clean` (`SourceRealizesClean.lean:40`) — PROVES exactly that `realizes`
  identity for a Picard source-form fixed point `u_star`.

The composite `sourceClassical_spatial_existence_clean` has the SAME conclusion as
`sourceClassical_spatial_existence_of_fixedPoint`, but with the `realizes` hypothesis
REMOVED: it is supplied internally by `realizes_clean`.  The carried hypotheses are the
union of `realizes_clean`'s inputs (u₀-data, contraction package, realized-source atoms
about `u_star` directly — suffixed `_rc`) and the spatial existence's OTHER inputs
(capstone inputs about the SHIFTED EMBEDDED element — `hgrad`/`h_flux_nbhd`/`h_flux_diff`
about `embedEWA (fun s => realSlice u_star (s+τ₀)) …`, logistic-source package, datum
bound).  Pure mechanical pass-through; no new mathematics. -/

open scoped BigOperators
open Set Metric
open ShenWork.GWA ShenWork.Wiener
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted)
open ShenWork.PDE (intervalNeumannResolverCoeff)
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalDuhamelClosedC2 (duhamelSpectralCoeff DuhamelSourceTimeC1)
open ShenWork.IntervalCoupledRegularityBootstrap
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)

namespace ShenWork.EWA

variable {T : ℝ}

/-- **χ₀<0 spatial classical existence with `realizes` DISCHARGED.**

Same conclusion as `sourceClassical_spatial_existence_of_fixedPoint`, but the cosine-series
realization identity is no longer a hypothesis — it is produced internally from the Picard
fixed point via `realizes_clean`. -/
theorem sourceClassical_spatial_existence_clean
    {μ ν γ : ℝ} (hμ : 0 < μ) (p : CM2Params)
    (u_star : EWA T 1) (u₀cos : ℕ → ℝ)
    {t τ₀ : ℝ} (htlo : 0 < t) (hthi : t ≤ T) (hτ0 : 0 < τ₀) (hτt : τ₀ < t)
    -- realizes_clean's inputs (to derive `realizes`):
    (hsum : Summable (fun k => |u₀cos k|)) (hmem : MemW 1 (ofCosineCoeffs u₀cos))
    (hT : (0 : ℝ) ≤ T)
    (hfix : u_star = picardEWA p p.μ p.ν p.γ p.hμ hT
      (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1) u_star)
    {ρ L_Q L_G : ℝ} (hρ : 0 ≤ ρ)
    (hself : MapsTo
      (picardEWA p p.μ p.ν p.γ p.hμ hT (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1))
      (Metric.closedBall (heatEWA (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ)
      (Metric.closedBall (heatEWA (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ))
    (hLipQ : ∀ a ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ,
      ∀ b ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ,
      ‖chemFluxEWA p.μ p.ν p.β p.γ p.hμ a - chemFluxEWA p.μ p.ν p.β p.γ p.hμ b‖
        ≤ L_Q * ‖a - b‖)
    (hLipG : ∀ a ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ,
      ∀ b ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ,
      ‖growthEWA p.α p.a p.b a - growthEWA p.α p.a p.b b‖ ≤ L_G * ‖a - b‖)
    (hKnn : (0 : ℝ) ≤ |p.χ₀| * (C₀ * Real.sqrt T) * L_Q + L_G * T)
    (hK : |p.χ₀| * (C₀ * Real.sqrt T) * L_Q + L_G * T < 1)
    (hmem_star : u_star ∈ Metric.closedBall (heatEWA (T := T)
      (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ)
    (hgrad_rc : ∀ (τ : TimeDom T),
      Summable fun k : ℕ =>
        |(intervalNeumannResolverCoeff p (realSlice u_star τ.1) k).re| * ((k : ℝ) * Real.pi))
    (h_flux_nbhd_rc : ∀ (τ : TimeDom T), ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      evalST τ (y : WA.Circ) (GWA.incl (by omega : (0 : ℕ) ≤ 1)
        (chemFluxEWA p.μ p.ν p.β p.γ p.hμ u_star))
        = ((chemFluxLifted p (realSlice u_star τ.1) y : ℝ) : ℂ))
    (h_flux_diff_rc : ∀ (τ : TimeDom T), ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ (chemFluxLifted p (realSlice u_star τ.1)) x)
    (h_u : ∀ (τ : TimeDom T), ∀ x ∈ Set.Icc (0 : ℝ) 1,
      evalST τ x (GWA.incl (by omega : (0 : ℕ) ≤ 1) u_star)
        = (intervalDomainLift (realSlice u_star τ.1) x : ℂ))
    (h_uα : ∀ (τ : TimeDom T), ∀ x ∈ Set.Icc (0 : ℝ) 1,
      evalST τ x (GWA.incl (by omega : (0 : ℕ) ≤ 1) (realPowEWA u_star p.α))
        = ((intervalDomainLift (realSlice u_star τ.1) x ^ p.α : ℝ) : ℂ))
    (h_src_cont_log : ∀ (τ : TimeDom T), Continuous (wLog p u_star τ.1))
    -- the spatial-existence's OTHER inputs (NOT discharged by realizes_clean):
    {Mu0 : ℝ} (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hGcont : ∀ n,
      Continuous (fun s => coupledChemDivSourceCoeffs p (realSlice u_star) s n))
    {Mlift : ℝ} (hMlift : 0 ≤ Mlift)
    (hLiftCont : ∀ s ∈ Set.Icc (0 : ℝ) τ₀,
      ContinuousOn (coupledChemDivSourceLift p (realSlice u_star) s) (Set.Icc (0 : ℝ) 1))
    (hLiftBd : ∀ s ∈ Set.Icc (0 : ℝ) τ₀, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |coupledChemDivSourceLift p (realSlice u_star) s x| ≤ Mlift)
    (Bv : ℕ → ℝ)
    (hBv : ∀ s k,
      |cosineCoeffs (intervalDomainLift
        ((fun s => realSlice u_star (s + τ₀)) s)) k| ≤ Bv k)
    (hBvnn : ∀ k, 0 ≤ Bv k)
    (hBvsum : Summable (fun k : ℕ => (1 + (k : ℝ)) * Bv k))
    (hcont : ∀ n : ℤ,
      Continuous (embedModeFun (fun s => realSlice u_star (s + τ₀)) n))
    (hgrad : ∀ τ : TimeDom T, Summable fun k : ℕ =>
      |(intervalNeumannResolverCoeff p
          ((fun s => realSlice u_star (s + τ₀)) τ.1) k).re| * ((k : ℝ) * Real.pi))
    (h_flux_nbhd : ∀ (τ : TimeDom T), ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      evalST τ (y : WA.Circ) (GWA.incl (by omega : (0:ℕ) ≤ 1)
        (chemFluxEWA μ ν p.β γ hμ
          (embedEWA (fun s => realSlice u_star (s + τ₀)) hBv hBvnn hBvsum hcont)))
        = ((chemFluxLifted p ((fun s => realSlice u_star (s + τ₀)) τ.1) y : ℝ) : ℂ))
    (h_flux_diff : ∀ (τ : TimeDom T), ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ
        (chemFluxLifted p ((fun s => realSlice u_star (s + τ₀)) τ.1)) x)
    (logSrc : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p (realSlice u_star))) :
    ContDiff ℝ 2
        (fun x => ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x)
      ∧ deriv (fun x => ∑' n,
          fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x) 0 = 0
      ∧ deriv (fun x => ∑' n,
          fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x) 1 = 0
      ∧ ∀ x ∈ Set.Icc (0 : ℝ) 1,
          intervalDomainLift (realSlice u_star t) x
            = ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x := by
  have hreal := realizes_clean (T := T) p u₀cos hsum hmem hT u_star hfix hρ hself hLipQ
    hLipG hKnn hK hmem_star hgrad_rc h_flux_nbhd_rc h_flux_diff_rc h_u
    h_uα h_src_cont_log t htlo hthi
  exact sourceClassical_spatial_existence_of_fixedPoint (T := T) hμ p u_star u₀cos
    htlo hthi hτ0 hτt hu0bd hreal hGcont hMlift hLiftCont hLiftBd Bv hBv hBvnn hBvsum
    hcont hgrad h_flux_nbhd h_flux_diff logSrc

end ShenWork.EWA

#print axioms ShenWork.EWA.sourceClassical_spatial_existence_clean
