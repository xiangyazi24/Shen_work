/- Positive-time strong membership and time continuity for classical orbits. -/
import ShenWork.Paper3.IntervalDomainStrongDuhamel
import ShenWork.Paper2.IntervalChiNegH1ChemDivRepresentative
import ShenWork.Paper2.IntervalNeumannHeatGradientL2BrickB
import ShenWork.Paper2.IntervalChiNegH1EnergyDeriv
import ShenWork.Paper2.IntervalBankChemSliceFix

namespace ShenWork.Paper3

open MeasureTheory Set
open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.PDE
open ShenWork.PDE.FractionalPower
open ShenWork.Paper2.IntervalChiNegH1EnergyIdentity
open ShenWork.Paper2.IntervalChiNegH1LiftDeriv2Transfer
open ShenWork.Paper2.IntervalChiNegH1ChemDivRepresentative

noncomputable section

/-- For exponents at most one, the fractional Neumann weight is controlled by
the graph norm of the Laplacian. -/
theorem fractionalPowerEnergyTerm_le_graphEnergy
    {sigma : ℝ} (hsigma1 : sigma ≤ 1)
    (a b : ℕ → ℂ) (n : ℕ)
    (hrel : b n = -((neumannEigenvalue 1 n : ℝ) : ℂ) * a n) :
    fractionalPowerEnergyTerm 1 sigma a n ≤
      2 * ‖a n‖ ^ 2 + 2 * ‖b n‖ ^ 2 := by
  let lam := neumannEigenvalue 1 n
  have hlam0 : 0 ≤ lam := neumannEigenvalue_nonneg 1 n
  have hbase : 1 ≤ 1 + lam := by linarith
  have hexp : 2 * sigma ≤ (2 : ℝ) := by linarith
  have hweight : (1 + lam) ^ (2 * sigma) ≤ (1 + lam) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hbase hexp
  have hb : ‖b n‖ ^ 2 = lam ^ 2 * ‖a n‖ ^ 2 := by
    rw [hrel]
    simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg hlam0]
    ring
  have hgraph : (1 + lam) ^ (2 : ℝ) * ‖a n‖ ^ 2 ≤
      2 * ‖a n‖ ^ 2 + 2 * (lam ^ 2 * ‖a n‖ ^ 2) := by
    rw [Real.rpow_two]
    nlinarith [sq_nonneg (lam - 1), sq_nonneg ‖a n‖]
  unfold fractionalPowerEnergyTerm fractionalPowerWeight
  dsimp [lam] at hweight hb hgraph ⊢
  calc
    (1 + neumannEigenvalue 1 n) ^ (2 * sigma) * ‖a n‖ ^ 2 ≤
        (1 + neumannEigenvalue 1 n) ^ (2 : ℝ) * ‖a n‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hweight (sq_nonneg _)
    _ ≤ 2 * ‖a n‖ ^ 2 +
        2 * (neumannEigenvalue 1 n ^ 2 * ‖a n‖ ^ 2) := hgraph
    _ = 2 * ‖a n‖ ^ 2 + 2 * ‖b n‖ ^ 2 := by rw [hb]

/-- Square-summable coefficients and square-summable Laplacian coefficients
give membership in every fractional power below the full Laplacian domain. -/
theorem fractionalPowerEnergy_summable_of_graphCoeffs
    {sigma : ℝ} (hsigma1 : sigma ≤ 1)
    {a b : ℕ → ℂ}
    (ha : Summable fun n => ‖a n‖ ^ 2)
    (hb : Summable fun n => ‖b n‖ ^ 2)
    (hrel : ∀ n, b n = -((neumannEigenvalue 1 n : ℝ) : ℂ) * a n) :
    Summable fun n => fractionalPowerEnergyTerm 1 sigma a n := by
  apply Summable.of_nonneg_of_le
    (fun n => fractionalPowerEnergyTerm_nonneg 1 sigma a n)
    (fun n => fractionalPowerEnergyTerm_le_graphEnergy
      hsigma1 a b n (hrel n))
  exact (ha.mul_left 2).add (hb.mul_left 2)

theorem fractionalPowerEnergy_tsum_le_graphCoeffs
    {sigma : ℝ} (hsigma1 : sigma ≤ 1)
    {a b : ℕ → ℂ}
    (ha : Summable fun n => ‖a n‖ ^ 2)
    (hb : Summable fun n => ‖b n‖ ^ 2)
    (hrel : ∀ n, b n = -((neumannEigenvalue 1 n : ℝ) : ℂ) * a n) :
    (∑' n, fractionalPowerEnergyTerm 1 sigma a n) ≤
      2 * (∑' n, ‖a n‖ ^ 2) + 2 * (∑' n, ‖b n‖ ^ 2) := by
  have henergy := fractionalPowerEnergy_summable_of_graphCoeffs
    hsigma1 ha hb hrel
  have hmajor : Summable fun n =>
      2 * ‖a n‖ ^ 2 + 2 * ‖b n‖ ^ 2 :=
    (ha.mul_left 2).add (hb.mul_left 2)
  have hle := henergy.tsum_le_tsum
    (fun n => fractionalPowerEnergyTerm_le_graphEnergy
      hsigma1 a b n (hrel n)) hmajor
  rw [Summable.tsum_add (ha.mul_left 2) (hb.mul_left 2),
    ha.tsum_mul_left, hb.tsum_mul_left] at hle
  exact hle

/-- Endpoint-safe continuous representative of the physical second spatial
derivative on positive time slabs. -/
abbrev paper3UxxPhysicalRep (p : CM2Params)
    (u v : ℝ → intervalDomainPoint → ℝ) (t x : ℝ) : ℝ :=
  liftDeriv2PhysicalRHSWithChemRep p u
    (liftChemotaxisDivPhysicalRep p u v) t x

theorem paper3UxxPhysicalRep_continuousOn_strictSlab
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ}
    {T a b : ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    ContinuousOn (Function.uncurry (paper3UxxPhysicalRep p u v))
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) := by
  exact liftDeriv2PhysicalRHSWithChemRep_continuousOn_of_components
    (p := p) (u := u)
    (chemRep := liftChemotaxisDivPhysicalRep p u v)
    (s := Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)
    (liftTimeDeriv_continuousOn_strictSlab_of_classicalSolution
      hsol ha hab hbT)
    (liftChemotaxisDivPhysicalRep_continuousOn_strictSlab_of_classicalSolution
      hsol ha hab hbT)
    (logisticReaction_continuousOn_strictSlab_of_classicalSolution
      hsol ha hab hbT)

theorem paper3UxxPhysicalRep_eq_liftDeriv2_interior
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ}
    {T t x : ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    paper3UxxPhysicalRep p u v t x = liftDeriv2 u t x := by
  have hphys :=
    liftDeriv2_eq_liftDeriv2PhysicalRHS_interior_of_classicalSolution
      hsol ht hx
  have hchem :=
    lift_chemotaxisDiv_eq_liftChemotaxisDivPhysicalRep_interior
      hsol ht hx
  rw [hphys]
  simp [paper3UxxPhysicalRep, liftDeriv2PhysicalRHS,
    liftDeriv2PhysicalRHSWithChemRep, hchem]

/-- The endpoint-safe representative has the same Laplacian coefficient as
the physical slice, and hence is the spectral graph coefficient of the
perturbation. -/
theorem paper3UxxPhysicalRep_cosineCoeff_eq_graphCoeff
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ}
    {T t uStar : ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) (n : ℕ) :
    ((cosineCoeffs (paper3UxxPhysicalRep p u v t) n : ℝ) : ℂ) =
      -((neumannEigenvalue 1 n : ℝ) : ℂ) *
        intervalDomainPerturbationCosineCoeff uStar (u t) n := by
  have hC2 := (hsol.regularity.2.2.2.2.1 t ht).1.1
  have htend := (hsol.regularity.2.2.2.1 t ht).1
  have hbc := (hsol.regularity.2.2.2.2.1 t ht).1
  have hrep : cosineCoeffs (paper3UxxPhysicalRep p u v t) n =
      cosineCoeffs (fun x => liftDeriv2 u t x) n := by
    exact ShenWork.Paper2.BankChemSliceFix.cosineCoeffs_congr_on_Ioo
      (fun x hx => paper3UxxPhysicalRep_eq_liftDeriv2_interior hsol ht hx) n
  have hlap : cosineCoeffs (fun x => liftDeriv2 u t x) n =
      -(unitIntervalCosineEigenvalue n) * solutionCoeffM u t n := by
    simpa [liftDeriv2, solutionCoeffM] using
      ShenWork.Paper2.IntervalChiNegH1EnergyDeriv.lapCoeff_eq_neg_lam_coeff
        (u := u) (τ := t) n hC2 htend.1 htend.2 hbc.2.1 hbc.2.2
  have hlam : neumannEigenvalue 1 n = unitIntervalCosineEigenvalue n := by
    simp [neumannEigenvalue, unitIntervalCosineEigenvalue]
  have heqzero := unitIntervalCosineEigenvalue_mul_equilibriumCoeff uStar n
  have hphi : IntervalIntegrable
      (fun x => intervalDomainLift (u t) x - uStar) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact (hC2.continuousOn.sub continuousOn_const)
  have hpert := paper3PerturbationCoeffM_eq_cosineCoeff_sub_const
    (u := u) (t := t) (uStar := uStar) n hphi
  have hreal : cosineCoeffs (paper3UxxPhysicalRep p u v t) n =
      -neumannEigenvalue 1 n *
        cosineCoeffs (fun x => intervalDomainLift (u t) x - uStar) n := by
    calc
      cosineCoeffs (paper3UxxPhysicalRep p u v t) n =
          -unitIntervalCosineEigenvalue n * solutionCoeffM u t n := by
        rw [hrep, hlap]
      _ = -unitIntervalCosineEigenvalue n *
          paper3PerturbationCoeffM u uStar t n := by
        unfold paper3PerturbationCoeffM
        nlinarith
      _ = -neumannEigenvalue 1 n *
          cosineCoeffs (fun x => intervalDomainLift (u t) x - uStar) n := by
        rw [hlam, hpert]
  simpa [intervalDomainPerturbationCosineCoeff] using congrArg Complex.ofReal hreal

/-- Every positive classical slice belongs to `X_2^sigma` for `sigma ≤ 1`.
The proof uses the endpoint-safe physical representative of `u_xx`; endpoint
values are irrelevant to both its `L²` class and its cosine coefficients. -/
theorem intervalDomainX2SigmaPerturbation_of_classical_positive
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ}
    {T t sigma uStar : ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) (hsigma1 : sigma ≤ 1) :
    IntervalDomainX2SigmaPerturbation sigma uStar (u t) := by
  let phi : ℝ → ℝ := fun x => intervalDomainLift (u t) x - uStar
  let F : ℝ → ℝ := paper3UxxPhysicalRep p u v t
  have hphiCont : ContinuousOn phi (Set.Icc (0 : ℝ) 1) := by
    dsimp [phi]
    exact ((hsol.regularity.2.2.2.2.1 t ht).1.1.continuousOn).sub
      continuousOn_const
  have hFjoint := paper3UxxPhysicalRep_continuousOn_strictSlab
    hsol ht.1 le_rfl ht.2
  have hFCont : ContinuousOn F (Set.Icc (0 : ℝ) 1) := by
    have hpair : ContinuousOn (fun x : ℝ => ((t, x) : ℝ × ℝ))
        (Set.Icc (0 : ℝ) 1) :=
      continuousOn_const.prodMk continuousOn_id
    have hmaps : Set.MapsTo (fun x : ℝ => ((t, x) : ℝ × ℝ))
        (Set.Icc (0 : ℝ) 1)
        (Set.Icc t t ×ˢ Set.Icc (0 : ℝ) 1) := by
      intro x hx
      exact ⟨⟨le_rfl, le_rfl⟩, hx⟩
    simpa [F, Function.comp_def] using hFjoint.comp hpair hmaps
  have hphiLp : MemLp phi 2 (intervalMeasure 1) :=
    BFormPositiveDatumNegPart.memLp_two_of_continuousOn_Icc hphiCont
  have hFLp : MemLp F 2 (intervalMeasure 1) :=
    BFormPositiveDatumNegPart.memLp_two_of_continuousOn_Icc hFCont
  have hphiSumR :=
    (ShenWork.IntervalNHGBrickB.cosineCoeffs_l2_of_memLp hphiLp).1
  have hFSumR :=
    (ShenWork.IntervalNHGBrickB.cosineCoeffs_l2_of_memLp hFLp).1
  have hphiSum : Summable fun n =>
      ‖intervalDomainPerturbationCosineCoeff uStar (u t) n‖ ^ 2 := by
    simpa [intervalDomainPerturbationCosineCoeff, phi,
      Complex.norm_real, Real.norm_eq_abs, sq_abs] using hphiSumR
  have hFSum : Summable fun n =>
      ‖((cosineCoeffs F n : ℝ) : ℂ)‖ ^ 2 := by
    simpa [Complex.norm_real, Real.norm_eq_abs, sq_abs] using hFSumR
  exact fractionalPowerEnergy_summable_of_graphCoeffs hsigma1
    hphiSum hFSum (fun n => by
      simpa [F] using
        paper3UxxPhysicalRep_cosineCoeff_eq_graphCoeff
          (uStar := uStar) hsol ht n)

#print axioms fractionalPowerEnergyTerm_le_graphEnergy
#print axioms fractionalPowerEnergy_summable_of_graphCoeffs
#print axioms fractionalPowerEnergy_tsum_le_graphCoeffs
#print axioms paper3UxxPhysicalRep_continuousOn_strictSlab
#print axioms paper3UxxPhysicalRep_eq_liftDeriv2_interior
#print axioms paper3UxxPhysicalRep_cosineCoeff_eq_graphCoeff
#print axioms intervalDomainX2SigmaPerturbation_of_classical_positive

end

end ShenWork.Paper3
