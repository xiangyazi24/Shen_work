/-
  Cosine-coefficient realization and `ell^2` estimate for the logistic
  remainder after extracting the full zeroth-mode damping `-a*alpha`.
-/
import ShenWork.Paper3.IntervalDomainFullModeDuhamel
import ShenWork.Paper3.IntervalDomainEllipticRemainderCoeffs
import ShenWork.Paper2.IntervalDomainResolverStrictPos

namespace ShenWork.Paper3

open MeasureTheory Set Real
open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel

noncomputable section

/-- Physical pointwise logistic remainder profile. -/
def paper3IntervalLogisticRemainderProfile
    (p : CM2Params) (uStar : ℝ)
    (u : intervalDomainPoint → ℝ) (x : ℝ) : ℝ :=
  paper3LogisticRemainder p uStar (intervalDomainLift u x)

def paper3IntervalLogisticRemainderDifferenceProfile
    (p : CM2Params) (uStar : ℝ)
    (u₁ u₂ : intervalDomainPoint → ℝ) (x : ℝ) : ℝ :=
  paper3IntervalLogisticRemainderProfile p uStar u₁ x -
    paper3IntervalLogisticRemainderProfile p uStar u₂ x

/-- The modal logistic residual in the full Duhamel equation is exactly the
cosine coefficient of the pointwise Taylor remainder. -/
theorem paper3LogisticRemainderCoeffM_eq_cosine
    (p : CM2Params) (uStar : ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ) (k : ℕ)
    (hreact : IntervalIntegrable
      (fun x => paper3LogisticReaction p (intervalDomainLift (u t) x))
      volume 0 1)
    (hphi : IntervalIntegrable
      (paper3IntervalPerturbationProfile uStar (u t)) volume 0 1) :
    paper3LogisticRemainderCoeffM p uStar u t k =
      cosineCoeffs
        (paper3IntervalLogisticRemainderProfile p uStar (u t)) k := by
  let reactionProfile : ℝ → ℝ := fun x =>
    paper3LogisticReaction p (intervalDomainLift (u t) x)
  let phi : ℝ → ℝ := paper3IntervalPerturbationProfile uStar (u t)
  let linearProfile : ℝ → ℝ := fun x => p.a * p.α * phi x
  have hlinear : IntervalIntegrable linearProfile volume 0 1 :=
    hphi.const_mul (p.a * p.α)
  have hlogCoeff :
      cosineCoeffs (ShenWork.Paper2.IntervalDomainM.logisticLiftedM p (u t)) k =
        cosineCoeffs reactionProfile k := by
    apply paper3_cosineCoeffs_congr_on_Icc
    intro x hx
    have hx' : 0 ≤ x ∧ x ≤ 1 := hx
    simp [ShenWork.Paper2.IntervalDomainM.logisticLiftedM,
      reactionProfile, paper3LogisticReaction, intervalDomainLift, hx']
  have hpertCoeff :
      paper3PerturbationCoeffM u uStar t k = cosineCoeffs phi k := by
    rw [paper3PerturbationCoeffM]
    change cosineCoeffs (intervalDomainLift (u t)) k -
        paper3EquilibriumCosineCoeff uStar k = cosineCoeffs phi k
    have hconst :=
      ShenWork.IntervalDomainResolverStrictPos.cosineCoeffs_const uStar k
    unfold paper3EquilibriumCosineCoeff
    rw [← hconst]
    have hadd := cosineCoeffs_add_of_intervalIntegrable k hphi
      (intervalIntegrable_const : IntervalIntegrable
        (fun _ : ℝ => uStar) volume 0 1)
    have hsum :
        cosineCoeffs (fun x => phi x + uStar) k =
          cosineCoeffs phi k + cosineCoeffs (fun _ : ℝ => uStar) k := hadd
    have hpoint : ∀ x, phi x + uStar = intervalDomainLift (u t) x := by
      intro x
      simp [phi, paper3IntervalPerturbationProfile]
    rw [show cosineCoeffs (intervalDomainLift (u t)) k =
        cosineCoeffs (fun x => phi x + uStar) k by
      apply congrArg (fun f : ℝ → ℝ => cosineCoeffs f k)
      funext x
      exact (hpoint x).symm]
    rw [hsum]
    ring
  have hlinearCoeff :
      cosineCoeffs linearProfile k =
        p.a * p.α * cosineCoeffs phi k := by
    exact cosineCoeffs_const_mul_of_intervalIntegrable
      (p.a * p.α) k hphi
  have hadd := cosineCoeffs_add_of_intervalIntegrable k hreact hlinear
  rw [paper3LogisticRemainderCoeffM, hlogCoeff, hpertCoeff,
    ← hlinearCoeff, ← hadd]
  apply congrArg (fun f : ℝ → ℝ => cosineCoeffs f k)
  funext x
  simp [linearProfile, phi,
    paper3IntervalLogisticRemainderProfile,
    paper3LogisticRemainder, paper3IntervalPerturbationProfile]

/-- The logistic remainder coefficients have norm `O(M*L2(phi))` on the local
positive neighborhood. -/
theorem paper3IntervalLogisticRemainder_coeff_l2
    (p : CM2Params) {uStar vStar M : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hM : 0 ≤ M) (u : intervalDomainPoint → ℝ)
    (hu_near : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift u x ∈ Set.Icc (uStar / 2) (3 * uStar / 2))
    (hphi : MemLp (paper3IntervalPerturbationProfile uStar u) 2
      (intervalMeasure 1))
    (hrem_meas : AEStronglyMeasurable
      (paper3IntervalLogisticRemainderProfile p uStar u)
      (intervalMeasure 1))
    (hphi_sup : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |paper3IntervalPerturbationProfile uStar u x| ≤ M) :
    ∃ K > 0,
      Summable (fun n =>
        (cosineCoeffs
          (paper3IntervalLogisticRemainderProfile p uStar u) n) ^ 2) ∧
      Real.sqrt (∑' n,
        (cosineCoeffs
          (paper3IntervalLogisticRemainderProfile p uStar u) n) ^ 2) ≤
        2 * K * M *
          Real.sqrt (∫ x in (0 : ℝ)..1,
            (paper3IntervalPerturbationProfile uStar u x) ^ 2) := by
  rcases paper3LogisticReaction_quadratic_remainder p heq with
    ⟨K, hK, hquad⟩
  refine ⟨K, hK, ?_⟩
  have hpoint : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |paper3IntervalLogisticRemainderProfile p uStar u x| ≤
        (K * M) * |paper3IntervalPerturbationProfile uStar u x| := by
    intro x hx
    have hq := hquad (intervalDomainLift u x) (hu_near x hx)
    have hs := hphi_sup x hx
    dsimp [paper3IntervalLogisticRemainderProfile,
      paper3IntervalPerturbationProfile, paper3LogisticRemainder] at hq ⊢
    calc
      |paper3LogisticReaction p (intervalDomainLift u x) +
          p.a * p.α * (intervalDomainLift u x - uStar)| ≤
        K * |intervalDomainLift u x - uStar| ^ 2 := hq
      _ ≤ (K * M) * |intervalDomainLift u x - uStar| := by
        have hnonneg : 0 ≤ |intervalDomainLift u x - uStar| := abs_nonneg _
        have hprod : 0 ≤ K * |intervalDomainLift u x - uStar| *
            (M - |intervalDomainLift u x - uStar|) :=
          mul_nonneg (mul_nonneg hK.le hnonneg) (sub_nonneg.mpr hs)
        nlinarith
  simpa [mul_assoc] using
    (cosineCoeffs_l2_norm_le_of_pointwise_mul
      (B := K * M) (mul_nonneg hK.le hM) hphi hrem_meas hpoint)

/-- Polarized logistic coefficient estimate on the positive strong ball. -/
theorem paper3IntervalLogisticRemainder_difference_coeff_l2
    (p : CM2Params) {uStar vStar M₁ M₂ : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (u₁ u₂ : intervalDomainPoint → ℝ)
    (hu₁_near : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift u₁ x ∈ Set.Icc (uStar / 2) (3 * uStar / 2))
    (hu₂_near : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift u₂ x ∈ Set.Icc (uStar / 2) (3 * uStar / 2))
    (hdiff : MemLp (paper3IntervalPerturbationDifferenceProfile u₁ u₂) 2
      (intervalMeasure 1))
    (hrem_meas : AEStronglyMeasurable
      (paper3IntervalLogisticRemainderDifferenceProfile p uStar u₁ u₂)
      (intervalMeasure 1))
    (hphi₁_sup : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |paper3IntervalPerturbationProfile uStar u₁ x| ≤ M₁)
    (hphi₂_sup : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |paper3IntervalPerturbationProfile uStar u₂ x| ≤ M₂) :
    ∃ K > 0,
      Summable (fun n =>
        (cosineCoeffs
          (paper3IntervalLogisticRemainderDifferenceProfile
            p uStar u₁ u₂) n) ^ 2) ∧
      Real.sqrt (∑' n,
        (cosineCoeffs
          (paper3IntervalLogisticRemainderDifferenceProfile
            p uStar u₁ u₂) n) ^ 2) ≤
        2 * K * (M₁ + M₂) *
          Real.sqrt (∫ x in (0 : ℝ)..1,
            (paper3IntervalPerturbationDifferenceProfile u₁ u₂ x) ^ 2) := by
  rcases paper3LogisticRemainder_sub_local_lipschitz p heq with
    ⟨K, hK, hpolar⟩
  refine ⟨K, hK, ?_⟩
  have hpoint : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |paper3IntervalLogisticRemainderDifferenceProfile
          p uStar u₁ u₂ x| ≤
        (K * (M₁ + M₂)) *
          |paper3IntervalPerturbationDifferenceProfile u₁ u₂ x| := by
    intro x hx
    have hp := hpolar (intervalDomainLift u₁ x) (hu₁_near x hx)
      (intervalDomainLift u₂ x) (hu₂_near x hx)
    have h1 := hphi₁_sup x hx
    have h2 := hphi₂_sup x hx
    dsimp [paper3IntervalLogisticRemainderDifferenceProfile,
      paper3IntervalLogisticRemainderProfile,
      paper3IntervalPerturbationDifferenceProfile,
      paper3IntervalPerturbationProfile] at hp h1 h2 ⊢
    calc
      _ ≤ K * (|intervalDomainLift u₁ x - uStar| +
          |intervalDomainLift u₂ x - uStar|) *
            |intervalDomainLift u₁ x - intervalDomainLift u₂ x| := hp
      _ ≤ K * (M₁ + M₂) *
          |intervalDomainLift u₁ x - intervalDomainLift u₂ x| :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (add_le_add h1 h2) hK.le)
          (abs_nonneg _)
      _ = _ := by ring
  simpa [mul_assoc] using
    (cosineCoeffs_l2_norm_le_of_pointwise_mul
      (B := K * (M₁ + M₂))
      (mul_nonneg hK.le (add_nonneg hM₁ hM₂))
      hdiff hrem_meas hpoint)

#print axioms paper3LogisticRemainderCoeffM_eq_cosine
#print axioms paper3IntervalLogisticRemainder_coeff_l2
#print axioms paper3IntervalLogisticRemainder_difference_coeff_l2

end

end ShenWork.Paper3
