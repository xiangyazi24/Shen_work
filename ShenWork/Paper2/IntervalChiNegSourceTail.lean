import ShenWork.Paper2.IntervalParabolicGainInduction
import ShenWork.Paper2.IntervalACBPolynomialBridge
import ShenWork.Paper2.IntervalCD6SpectralTail

noncomputable section

namespace ShenWork.Paper2.ChiNegSourceTail

open ShenWork.Paper2.PicardLimitK1 (LocalRestart)
open ShenWork.Paper2.ACBPolynomialBridge
open ShenWork.IntervalResolverTimeRegularity (ResolverHasSpectralAgreement)
open ShenWork.IntervalResolverJointC2 (ResolverHasSpectralAgreementC2Coeff)

variable {p : CM2Params}
variable {u : ℝ → ShenWork.IntervalDomain.intervalDomainPoint → ℝ}
variable {T σ : ℝ}

/-- Sixth-order shifted tails for the raw clamped source and its time derivative. -/
structure SourceTail6Fields
    (L : LocalRestart p u T σ) (C Cdot : ℝ) : Prop where
  hC : 0 ≤ C
  hCdot : 0 ≤ Cdot
  sourceTail :
    ∀ s, 0 ≤ s → ∀ n,
      |L.aC s n| ≤ C / ((n : ℝ) + 1) ^ (6 : ℕ)
  adotTail :
    ∀ s, 0 ≤ s → ∀ n,
      |L.srcC.adot s n| ≤ Cdot / ((n : ℝ) + 1) ^ (6 : ℕ)

/-- A sixth-order source tail gives the source fields consumed by ACB. -/
def SourceTail6Fields.toSourceFields
    {L : LocalRestart p u T σ} {C Cdot : ℝ}
    (H : SourceTail6Fields L C Cdot) :
    ShenWork.Paper2.PicardLimitK1C2Coeff.SourceC2CoeffFields L.srcC :=
  localRestart_sourceFields_of_natShiftSix
    L H.hC H.hCdot H.sourceTail H.adotTail

/-- Eigenvalue-cube tails imply the shifted sixth-order tails used by ACB. -/
structure SourceEigenCubeTailFields
    (L : LocalRestart p u T σ) (C0 C C0dot Cdot : ℝ) : Prop where
  hC : 0 ≤ max C0 (64 * C)
  hCdot : 0 ≤ max C0dot (64 * Cdot)
  sourceZero : ∀ s, 0 ≤ s → |L.aC s 0| ≤ C0
  sourceCube :
    ∀ s, 0 ≤ s → ∀ n, 1 ≤ n →
      unitIntervalCosineEigenvalue n ^ (3 : ℕ) * |L.aC s n| ≤ C
  adotZero : ∀ s, 0 ≤ s → |L.srcC.adot s 0| ≤ C0dot
  adotCube :
    ∀ s, 0 ≤ s → ∀ n, 1 ≤ n →
      unitIntervalCosineEigenvalue n ^ (3 : ℕ) *
        |L.srcC.adot s n| ≤ Cdot

/-- Eigenvalue-cube source tails give the source fields consumed by ACB. -/
def SourceEigenCubeTailFields.toSourceFields
    {L : LocalRestart p u T σ} {C0 C C0dot Cdot : ℝ}
    (H : SourceEigenCubeTailFields L C0 C C0dot Cdot) :
    ShenWork.Paper2.PicardLimitK1C2Coeff.SourceC2CoeffFields L.srcC :=
  ShenWork.Paper2.CD6SpectralTail.localRestart_sourceFields_of_eigenCube
    L H.hC H.hCdot H.sourceZero H.sourceCube H.adotZero H.adotCube

/-- The χ-negative resolver-C2 branch closes from raw sixth-order source tails. -/
theorem resolverHasSpectralAgreementC2Coeff_of_tail6
    (H : ResolverHasSpectralAgreement T u)
    (mkL : ∀ σ, 0 < σ → σ < T → LocalRestart p u T σ)
    (C Cdot : ℝ → ℝ)
    (hC : ∀ σ, 0 ≤ C σ)
    (hCdot : ∀ σ, 0 ≤ Cdot σ)
    (tail : ∀ σ (hσ0 : 0 < σ) (hσT : σ < T),
      SourceTail6Fields (mkL σ hσ0 hσT) (C σ) (Cdot σ)) :
    ResolverHasSpectralAgreementC2Coeff T u :=
  resolverHasSpectralAgreementC2Coeff_of_natShiftSix H mkL C Cdot hC hCdot
    (fun σ hσ0 hσT =>
      (tail σ hσ0 hσT).sourceTail)
    (fun σ hσ0 hσT =>
      (tail σ hσ0 hσT).adotTail)

/-- The χ-negative resolver-C2 branch also closes from eigenvalue-cube tails. -/
theorem resolverHasSpectralAgreementC2Coeff_of_eigenCubeTail
    (H : ResolverHasSpectralAgreement T u)
    (mkL : ∀ σ, 0 < σ → σ < T → LocalRestart p u T σ)
    (C0 C C0dot Cdot : ℝ → ℝ)
    (hC6 : ∀ σ, 0 ≤ max (C0 σ) (64 * C σ))
    (hCdot6 : ∀ σ, 0 ≤ max (C0dot σ) (64 * Cdot σ))
    (tail : ∀ σ (hσ0 : 0 < σ) (hσT : σ < T),
      SourceEigenCubeTailFields
        (mkL σ hσ0 hσT) (C0 σ) (C σ) (C0dot σ) (Cdot σ)) :
    ResolverHasSpectralAgreementC2Coeff T u :=
  resolverHasSpectralAgreementC2Coeff_of_tail6 H mkL
    (fun σ => max (C0 σ) (64 * C σ))
    (fun σ => max (C0dot σ) (64 * Cdot σ))
    hC6 hCdot6
    (fun σ hσ0 hσT =>
      { hC := (tail σ hσ0 hσT).hC
        hCdot := (tail σ hσ0 hσT).hCdot
        sourceTail := fun s hs n =>
          ShenWork.Paper2.CD6SpectralTail.natShiftSix_of_eigenCube_bound
            ((tail σ hσ0 hσT).sourceZero s hs)
            ((tail σ hσ0 hσT).sourceCube s hs) n
        adotTail := fun s hs n =>
          ShenWork.Paper2.CD6SpectralTail.natShiftSix_of_eigenCube_bound
            ((tail σ hσ0 hσT).adotZero s hs)
            ((tail σ hσ0 hσT).adotCube s hs) n })

end ShenWork.Paper2.ChiNegSourceTail
