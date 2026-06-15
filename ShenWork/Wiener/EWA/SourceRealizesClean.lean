import ShenWork.Wiener.EWA.SourceRealizesRecords
import ShenWork.Wiener.EWA.SourceFixedPointParity

/-!
# EWA capstone (χ₀<0 Route A′) — the CLEAN `realizes` statement

This file is a pure pass-through.  It composes the four committed theorems

* `realizes_of_picardFixedPoint` (`SourceRealizesAssembly.lean`),
* `picardEWA_evenReal_fixedPoint` (`SourceFixedPointParity.lean`),
* `chemDiv_realizesOn`  (`SourceRealizesRecords.lean`),
* `logistic_realizesOn` (`SourceRealizesRecords.lean`),

so that the final `realizes` statement carries ONLY the fixed-point equation `hfix`,
the standard `u₀` heat-datum data (`hsum`/`hmem`/`hT`), the contraction data
(`hρ`/`hself`/`hLipQ`/`hLipG`/`hKnn`/`hK`/`hmem_star`), and the realized-source atoms
of the two committed eval bridges.  The `EvenRealEWA u_star` parity hypothesis and the
two `EWARealizesOn` records (plus their `hw` lift-matches) are DISCHARGED here.

NO `sorry`, `axiom`, `native_decide`, or `admit`.
-/

open scoped BigOperators
open Set Metric
open ShenWork.GWA ShenWork.Wiener
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted)
open ShenWork.PDE (intervalNeumannResolverCoeff)
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.CosineSpectrum (cosineMode)

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-- **The clean χ₀<0 `realizes` capstone.**  Pure composition of the four committed
theorems: the `realizes` cosine-series identity for a Picard fixed point `u_star`,
carrying only `u₀`-data, contraction data, and the realized-source analytic atoms. -/
theorem realizes_clean (p : CM2Params) (u₀cos : ℕ → ℝ)
    (hsum : Summable (fun k => |u₀cos k|)) (hmem : MemW 1 (ofCosineCoeffs u₀cos))
    (hT : (0 : ℝ) ≤ T)
    {ρ L_Q L_G : ℝ} (u_star : EWA T 1)
    (hfix : u_star = picardEWA p p.μ p.ν p.γ p.hμ hT
      (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1) u_star)
    -- contraction data (= picardEWA_evenReal_fixedPoint's hypotheses):
    (hρ : 0 ≤ ρ)
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
    -- realized-source atoms (= chemDiv_realizesOn / logistic_realizesOn's carried hyps):
    (hgrad : ∀ (τ : TimeDom T),
      Summable fun k : ℕ =>
        |(intervalNeumannResolverCoeff p (realSlice u_star τ.1) k).re| * ((k : ℝ) * Real.pi))
    (h_flux_nbhd : ∀ (τ : TimeDom T), ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      evalST τ (y : WA.Circ) (GWA.incl (by omega : (0 : ℕ) ≤ 1)
        (chemFluxEWA p.μ p.ν p.β p.γ p.hμ u_star))
        = ((chemFluxLifted p (realSlice u_star τ.1) y : ℝ) : ℂ))
    (h_flux_diff : ∀ (τ : TimeDom T), ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ (chemFluxLifted p (realSlice u_star τ.1)) x)
    (h_src_cont_chem : ∀ (τ : TimeDom T), Continuous (wChem p u_star τ.1))
    (h_u : ∀ (τ : TimeDom T), ∀ x ∈ Set.Icc (0 : ℝ) 1,
      evalST τ x (GWA.incl (by omega : (0 : ℕ) ≤ 1) u_star)
        = (intervalDomainLift (realSlice u_star τ.1) x : ℂ))
    (h_uα : ∀ (τ : TimeDom T), ∀ x ∈ Set.Icc (0 : ℝ) 1,
      evalST τ x (GWA.incl (by omega : (0 : ℕ) ≤ 1) (realPowEWA u_star p.α))
        = ((intervalDomainLift (realSlice u_star τ.1) x ^ p.α : ℝ) : ℂ))
    (h_src_cont_log : ∀ (τ : TimeDom T), Continuous (wLog p u_star τ.1))
    (t : ℝ) (htlo : 0 < t) (hthi : t ≤ T) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (realSlice u_star t) x
        = ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x := by
  have hER_star : EvenRealEWA u_star :=
    picardEWA_evenReal_fixedPoint p p.hμ hT u₀cos hmem hρ hself hLipQ hLipG hKnn hK
      u_star hmem_star hfix
  have H_chem := chemDiv_realizesOn p u_star hER_star hgrad h_flux_nbhd h_flux_diff
    h_src_cont_chem
  have H_log := logistic_realizesOn p u_star hER_star h_u h_uα h_src_cont_log
  exact realizes_of_picardFixedPoint p u₀cos hsum hmem hT u_star hfix hER_star
    (wChem p u_star) H_chem (wChem_lift_eq p u_star)
    (wLog p u_star) H_log (wLog_lift_eq p u_star) t htlo hthi

end ShenWork.EWA

#print axioms ShenWork.EWA.realizes_clean
