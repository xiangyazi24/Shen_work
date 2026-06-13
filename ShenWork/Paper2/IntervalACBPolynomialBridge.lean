import ShenWork.Paper2.IntervalACBPolynomialEnvelope
import ShenWork.Paper2.IntervalResolverSpectralAgreementC2CoeffFromK1

noncomputable section

namespace ShenWork.Paper2.ACBPolynomialBridge

open ShenWork.Paper2.PicardLimitK1 (LocalRestart)
open ShenWork.Paper2.PicardLimitK1C2Coeff (SourceC2CoeffFields)
open ShenWork.Paper2.ACBPolynomialEnvelope
open ShenWork.Paper2.ResolverSpectralAgreementC2CoeffFromK1
open ShenWork.IntervalResolverTimeRegularity (ResolverHasSpectralAgreement)
open ShenWork.IntervalResolverJointC2 (ResolverHasSpectralAgreementC2Coeff)

variable {p : CM2Params}
variable {u : ℝ → ShenWork.IntervalDomain.intervalDomainPoint → ℝ}
variable {T : ℝ}

/-- Route B local form: sixth-order shifted polynomial tails for raw `aC` and
`adot` provide the source-side C2 coefficient fields. -/
def localRestart_sourceFields_of_natShiftSix
    (L : LocalRestart p u T σ)
    {C Cdot : ℝ} (hC : 0 ≤ C) (hCdot : 0 ≤ Cdot)
    (ha : ∀ s, 0 ≤ s → ∀ n,
      |L.aC s n| ≤ C / ((n : ℝ) + 1) ^ (6 : ℕ))
    (hadot : ∀ s, 0 ≤ s → ∀ n,
      |L.srcC.adot s n| ≤ Cdot / ((n : ℝ) + 1) ^ (6 : ℕ)) :
    SourceC2CoeffFields L.srcC :=
  sourceC2CoeffFields_of_natShiftSix hC hCdot ha hadot

/-- Route B resolver form: polynomial tails for every K1 local restart close the
coefficient-level spectral agreement branch. -/
theorem resolverHasSpectralAgreementC2Coeff_of_natShiftSix
    (H : ResolverHasSpectralAgreement T u)
    (mkL : ∀ σ, 0 < σ → σ < T → LocalRestart p u T σ)
    (C Cdot : ℝ → ℝ) (hC : ∀ σ, 0 ≤ C σ)
    (hCdot : ∀ σ, 0 ≤ Cdot σ)
    (ha : ∀ σ (hσ0 : 0 < σ) (hσT : σ < T), ∀ s, 0 ≤ s → ∀ n,
      |(mkL σ hσ0 hσT).aC s n| ≤ C σ / ((n : ℝ) + 1) ^ (6 : ℕ))
    (hadot : ∀ σ (hσ0 : 0 < σ) (hσT : σ < T), ∀ s, 0 ≤ s → ∀ n,
      |(mkL σ hσ0 hσT).srcC.adot s n| ≤
        Cdot σ / ((n : ℝ) + 1) ^ (6 : ℕ)) :
    ResolverHasSpectralAgreementC2Coeff T u :=
  resolverHasSpectralAgreementC2Coeff_of_sourceFields H mkL
      (fun σ hσ0 hσT => by
        exact localRestart_sourceFields_of_natShiftSix
          (mkL σ hσ0 hσT) (hC σ) (hCdot σ)
          (ha σ hσ0 hσT) (hadot σ hσ0 hσT))

end ShenWork.Paper2.ACBPolynomialBridge
