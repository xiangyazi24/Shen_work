/- Strong fractional membership of every positive faithful general-`m` slice. -/
import ShenWork.Paper3.IntervalDomainStrongTimeContinuity
import ShenWork.Paper2.IntervalDomainMChemDivBoundaryLimit

namespace ShenWork.Paper3

open MeasureTheory Set
open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.Paper2.IntervalChiNegH1EnergyIdentity
open ShenWork.Paper2.IntervalChiNegH1LiftDeriv2Transfer
open ShenWork.Paper2.IntervalDomainMMinPersistence
open ShenWork.PDE.FractionalPower

noncomputable section

/-- Endpoint-safe representative of the faithful general-`m` population
Laplacian, obtained by solving the physical equation for `u_xx`. -/
abbrev paper3UxxPhysicalRepGeneralM (p : CM2Params)
    (u v : ℝ → intervalDomainPoint → ℝ) (t x : ℝ) : ℝ :=
  liftDeriv2PhysicalRHSWithChemRep p u
    (classicalChemDivMPhysicalRep p u v) t x

/-- At a fixed positive time the faithful physical Laplacian representative
is continuous on the closed spatial interval. -/
theorem paper3UxxPhysicalRepGeneralM_continuousOn_slice
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ}
    {T t : ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    ContinuousOn (paper3UxxPhysicalRepGeneralM p u v t)
      (Set.Icc (0 : ℝ) 1) := by
  let embed : ℝ → ℝ × ℝ := fun x => (t, x)
  have hembed : ContinuousOn embed (Set.Icc (0 : ℝ) 1) :=
    continuousOn_const.prodMk continuousOn_id
  have hmaps : Set.MapsTo embed (Set.Icc (0 : ℝ) 1)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
    intro x hx
    exact ⟨ht, hx⟩
  have htimeJoint := hsol.regularity.2.2.2.2.2.1.1
  have htime : ContinuousOn (fun x => liftTimeDeriv u t x)
      (Set.Icc (0 : ℝ) 1) := by
    simpa [embed, Function.comp_def, liftTimeDeriv] using
      htimeJoint.comp hembed hmaps
  have hchem : ContinuousOn (classicalChemDivMPhysicalRep p u v t)
      (Set.Icc (0 : ℝ) 1) :=
    classicalChemDivMPhysicalRep_continuousOn_Icc hsol ht.1 ht.2
  have hu : ContinuousOn (intervalDomainLift (u t))
      (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 t ht).1.1.continuousOn
  have hupos : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (u t) x := by
    intro x hx
    simpa [intervalDomainLift, hx] using
      hsol.u_pos' (x := (⟨x, hx⟩ : intervalDomainPoint)) ht.1 ht.2
  have hpow : ContinuousOn
      (fun x => intervalDomainLift (u t) x ^ p.α)
      (Set.Icc (0 : ℝ) 1) :=
    hu.rpow_const (fun x hx => Or.inl (hupos x hx).ne')
  have hreact : ContinuousOn
      (fun x => intervalDomainLift (u t) x *
        (p.a - p.b * intervalDomainLift (u t) x ^ p.α))
      (Set.Icc (0 : ℝ) 1) :=
    hu.mul (continuousOn_const.sub (continuousOn_const.mul hpow))
  simpa [paper3UxxPhysicalRepGeneralM,
    liftDeriv2PhysicalRHSWithChemRep] using
    (htime.add (hchem.const_mul p.χ₀)).sub hreact

/-- The faithful physical representative agrees with the literal second
spatial derivative throughout the open interval. -/
theorem paper3UxxPhysicalRepGeneralM_eq_liftDeriv2_interior
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ}
    {T t x : ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    paper3UxxPhysicalRepGeneralM p u v t x = liftDeriv2 u t x := by
  let xp : intervalDomainPoint := ⟨x, Set.Ioo_subset_Icc_self hx⟩
  have hpde := hsol.pde_u ht.1 ht.2
    (x := xp) (show xp ∈ intervalDomainM.inside from hx)
  have hchem := intervalDomainMChemotaxisDiv_eq_physicalRep_interior
    hsol ht.1 ht.2 hx
  have hchem' : intervalDomainM.chemotaxisDiv p (u t) (v t) xp =
      classicalChemDivMPhysicalRep p u v t x := by
    simpa [intervalDomainM, xp] using hchem
  have htime : intervalDomainM.timeDeriv u t xp = liftTimeDeriv u t x := by
    simp only [intervalDomainM]
    change deriv (fun s => u s xp) t =
      deriv (fun s => intervalDomainLift (u s) x) t
    congr 1
    funext s
    simp [intervalDomainLift, xp, Set.Ioo_subset_Icc_self hx]
  have hlap : intervalDomainM.laplacian (u t) xp = liftDeriv2 u t x := rfl
  have hlift : intervalDomainLift (u t) x = u t xp := by
    simp [intervalDomainLift, xp, Set.Ioo_subset_Icc_self hx]
  rw [htime, hlap] at hpde
  change liftTimeDeriv u t x +
      p.χ₀ * classicalChemDivMPhysicalRep p u v t x -
        intervalDomainLift (u t) x *
          (p.a - p.b * intervalDomainLift (u t) x ^ p.α) =
    liftDeriv2 u t x
  rw [hlift]
  rw [← hchem']
  linarith

/-- The endpoint-safe representative has the spectral graph coefficient of
the faithful perturbation slice. -/
theorem paper3UxxPhysicalRepGeneralM_cosineCoeff_eq_graphCoeff
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ}
    {T t uStar : ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) (n : ℕ) :
    ((cosineCoeffs (paper3UxxPhysicalRepGeneralM p u v t) n : ℝ) : ℂ) =
      -((neumannEigenvalue 1 n : ℝ) : ℂ) *
        intervalDomainPerturbationCosineCoeff uStar (u t) n := by
  have hC2 := (hsol.regularity.2.2.2.2.1 t ht).1.1
  have htend := (hsol.regularity.2.2.2.1 t ht).1
  have hbc := (hsol.regularity.2.2.2.2.1 t ht).1
  have hrep : cosineCoeffs (paper3UxxPhysicalRepGeneralM p u v t) n =
      cosineCoeffs (fun x => liftDeriv2 u t x) n := by
    exact ShenWork.Paper2.BankChemSliceFix.cosineCoeffs_congr_on_Ioo
      (fun x hx =>
        paper3UxxPhysicalRepGeneralM_eq_liftDeriv2_interior hsol ht hx) n
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
    exact hC2.continuousOn.sub continuousOn_const
  have hpert := paper3PerturbationCoeffM_eq_cosineCoeff_sub_const
    (u := u) (t := t) (uStar := uStar) n hphi
  have hreal : cosineCoeffs (paper3UxxPhysicalRepGeneralM p u v t) n =
      -neumannEigenvalue 1 n *
        cosineCoeffs (fun x => intervalDomainLift (u t) x - uStar) n := by
    calc
      cosineCoeffs (paper3UxxPhysicalRepGeneralM p u v t) n =
          -unitIntervalCosineEigenvalue n * solutionCoeffM u t n := by
        rw [hrep, hlap]
      _ = -unitIntervalCosineEigenvalue n *
          paper3PerturbationCoeffM u uStar t n := by
        unfold paper3PerturbationCoeffM
        nlinarith
      _ = -neumannEigenvalue 1 n *
          cosineCoeffs (fun x => intervalDomainLift (u t) x - uStar) n := by
        rw [hlam, hpert]
  simpa [intervalDomainPerturbationCosineCoeff] using
    congrArg Complex.ofReal hreal

/-- Every positive faithful classical slice belongs to `X_2^sigma` for
`sigma ≤ 1`; no restriction on `m` is used. -/
theorem intervalDomainMX2SigmaPerturbation_of_classical_positive
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ}
    {T t sigma uStar : ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) (hsigma1 : sigma ≤ 1) :
    IntervalDomainX2SigmaPerturbation sigma uStar (u t) := by
  let phi : ℝ → ℝ := fun x => intervalDomainLift (u t) x - uStar
  let F : ℝ → ℝ := paper3UxxPhysicalRepGeneralM p u v t
  have hphiCont : ContinuousOn phi (Set.Icc (0 : ℝ) 1) := by
    dsimp [phi]
    exact ((hsol.regularity.2.2.2.2.1 t ht).1.1.continuousOn).sub
      continuousOn_const
  have hFCont : ContinuousOn F (Set.Icc (0 : ℝ) 1) := by
    simpa [F] using paper3UxxPhysicalRepGeneralM_continuousOn_slice hsol ht
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
  have hFSum : Summable fun n => ‖((cosineCoeffs F n : ℝ) : ℂ)‖ ^ 2 := by
    simpa [Complex.norm_real, Real.norm_eq_abs, sq_abs] using hFSumR
  exact fractionalPowerEnergy_summable_of_graphCoeffs hsigma1
    hphiSum hFSum (fun n => by
      simpa [F] using
        paper3UxxPhysicalRepGeneralM_cosineCoeff_eq_graphCoeff
          (uStar := uStar) hsol ht n)

#print axioms paper3UxxPhysicalRepGeneralM_continuousOn_slice
#print axioms paper3UxxPhysicalRepGeneralM_eq_liftDeriv2_interior
#print axioms paper3UxxPhysicalRepGeneralM_cosineCoeff_eq_graphCoeff
#print axioms intervalDomainMX2SigmaPerturbation_of_classical_positive

end

end ShenWork.Paper3
