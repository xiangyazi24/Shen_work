/- Positive-time strong membership and time continuity for classical orbits. -/
import ShenWork.Paper3.IntervalDomainStrongDuhamel
import ShenWork.Paper2.IntervalChiNegH1ChemDivRepresentative
import ShenWork.Paper2.IntervalNeumannHeatGradientL2BrickB
import ShenWork.Paper2.IntervalChiNegH1EnergyDeriv
import ShenWork.Paper2.IntervalBankChemSliceFix

namespace ShenWork.Paper3

open MeasureTheory Set Filter
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

theorem paper3UxxPhysicalRep_continuousOn_slice
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ}
    {T t : ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    ContinuousOn (paper3UxxPhysicalRep p u v t)
      (Set.Icc (0 : ℝ) 1) := by
  have hjoint := paper3UxxPhysicalRep_continuousOn_strictSlab
    hsol ht.1 le_rfl ht.2
  exact hjoint.comp
    (continuousOn_const.prodMk continuousOn_id)
    (fun x hx => ⟨⟨le_rfl, le_rfl⟩, hx⟩)

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

set_option maxHeartbeats 800000 in
/-- Quantitative graph-norm continuity estimate.  If both the value slices and
the endpoint-safe `u_xx` representatives are uniformly `B`-close, then their
weighted coefficient vectors are `4B`-close in `X_2^sigma`. -/
theorem weightedPerturbationCoeff_sub_norm_le_of_value_uxx_bounds
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ}
    {T s t sigma uStar B : ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hs : s ∈ Set.Ioo (0 : ℝ) T) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hsigma1 : sigma ≤ 1) (hB : 0 ≤ B)
    (huBound : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |intervalDomainLift (u s) x - intervalDomainLift (u t) x| ≤ B)
    (huxxBound : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |paper3UxxPhysicalRep p u v s x -
        paper3UxxPhysicalRep p u v t x| ≤ B) :
    ‖weightedCoeffToLp 1 sigma
          (intervalDomainPerturbationCosineCoeff uStar (u s))
          (intervalDomainX2SigmaPerturbation_of_classical_positive
            hsol hs hsigma1) -
        weightedCoeffToLp 1 sigma
          (intervalDomainPerturbationCosineCoeff uStar (u t))
          (intervalDomainX2SigmaPerturbation_of_classical_positive
            hsol ht hsigma1)‖ ≤ 4 * B := by
  let phi : ℝ → ℝ := fun x =>
    intervalDomainLift (u s) x - intervalDomainLift (u t) x
  let F : ℝ → ℝ := fun x =>
    paper3UxxPhysicalRep p u v s x - paper3UxxPhysicalRep p u v t x
  let a : ℕ → ℂ := fun n => ((cosineCoeffs phi n : ℝ) : ℂ)
  let b : ℕ → ℂ := fun n => ((cosineCoeffs F n : ℝ) : ℂ)
  have huS : ContinuousOn (intervalDomainLift (u s)) (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 s hs).1.1.continuousOn
  have huT : ContinuousOn (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 t ht).1.1.continuousOn
  have hphiCont : ContinuousOn phi (Set.Icc (0 : ℝ) 1) := by
    simpa [phi] using huS.sub huT
  have hFS : ContinuousOn (paper3UxxPhysicalRep p u v s)
      (Set.Icc (0 : ℝ) 1) := paper3UxxPhysicalRep_continuousOn_slice hsol hs
  have hFT : ContinuousOn (paper3UxxPhysicalRep p u v t)
      (Set.Icc (0 : ℝ) 1) := paper3UxxPhysicalRep_continuousOn_slice hsol ht
  have hFCont : ContinuousOn F (Set.Icc (0 : ℝ) 1) := by
    simpa [F] using hFS.sub hFT
  have hphiData := cosineCoeffs_l2_norm_le_of_pointwise_abs_bound hB
    (hphiCont.aestronglyMeasurable measurableSet_Icc)
    (by simpa [phi] using huBound)
  have hFData := cosineCoeffs_l2_norm_le_of_pointwise_abs_bound hB
    (hFCont.aestronglyMeasurable measurableSet_Icc)
    (by simpa [F] using huxxBound)
  have ha : Summable fun n => ‖a n‖ ^ 2 := by
    simpa [a, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hphiData.1
  have hb : Summable fun n => ‖b n‖ ^ 2 := by
    simpa [b, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hFData.1
  have hphiSInt : IntervalIntegrable
      (fun x => intervalDomainLift (u s) x - uStar) volume 0 1 := by
    exact (huS.sub continuousOn_const).intervalIntegrable_of_Icc (by norm_num)
  have hphiTInt : IntervalIntegrable
      (fun x => intervalDomainLift (u t) x - uStar) volume 0 1 := by
    exact (huT.sub continuousOn_const).intervalIntegrable_of_Icc (by norm_num)
  have hphiCoeff : ∀ n,
      a n = intervalDomainPerturbationCosineCoeff uStar (u s) n -
        intervalDomainPerturbationCosineCoeff uStar (u t) n := by
    intro n
    have hsub := cosineCoeffs_sub_of_intervalIntegrable n hphiSInt hphiTInt
    have hcongr : cosineCoeffs phi n =
        cosineCoeffs (fun x =>
          (intervalDomainLift (u s) x - uStar) -
            (intervalDomainLift (u t) x - uStar)) n := by
      exact paper3_cosineCoeffs_congr_on_Icc (fun x _hx => by ring) n
    dsimp [a]
    rw [hcongr, hsub]
    simp [intervalDomainPerturbationCosineCoeff]
  have hFSInt : IntervalIntegrable (paper3UxxPhysicalRep p u v s)
      volume 0 1 := hFS.intervalIntegrable_of_Icc (by norm_num)
  have hFTInt : IntervalIntegrable (paper3UxxPhysicalRep p u v t)
      volume 0 1 := hFT.intervalIntegrable_of_Icc (by norm_num)
  have hFCoeff : ∀ n, b n =
      ((cosineCoeffs (paper3UxxPhysicalRep p u v s) n : ℝ) : ℂ) -
        ((cosineCoeffs (paper3UxxPhysicalRep p u v t) n : ℝ) : ℂ) := by
    intro n
    have hsub := cosineCoeffs_sub_of_intervalIntegrable n hFSInt hFTInt
    dsimp [b, F]
    rw [hsub]
    push_cast
    rfl
  have hrel : ∀ n, b n =
      -((neumannEigenvalue 1 n : ℝ) : ℂ) * a n := by
    intro n
    rw [hFCoeff n,
      paper3UxxPhysicalRep_cosineCoeff_eq_graphCoeff
        (uStar := uStar) hsol hs n,
      paper3UxxPhysicalRep_cosineCoeff_eq_graphCoeff
        (uStar := uStar) hsol ht n,
      hphiCoeff n]
    ring
  have hmem := fractionalPowerEnergy_summable_of_graphCoeffs
    hsigma1 ha hb hrel
  have henergy := fractionalPowerEnergy_tsum_le_graphCoeffs
    hsigma1 ha hb hrel
  let A : ℝ := ∑' n, ‖a n‖ ^ 2
  let D : ℝ := ∑' n, ‖b n‖ ^ 2
  have hA0 : 0 ≤ A := tsum_nonneg fun n => sq_nonneg ‖a n‖
  have hD0 : 0 ≤ D := tsum_nonneg fun n => sq_nonneg ‖b n‖
  have hAroot : Real.sqrt A ≤ 2 * B := by
    simpa [A, a, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hphiData.2
  have hDroot : Real.sqrt D ≤ 2 * B := by
    simpa [D, b, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hFData.2
  have hAle : A ≤ 4 * B ^ 2 := by
    have hsq := mul_self_le_mul_self (Real.sqrt_nonneg A) hAroot
    have hsqrt := Real.sq_sqrt hA0
    nlinarith [hsqrt]
  have hDle : D ≤ 4 * B ^ 2 := by
    have hsq := mul_self_le_mul_self (Real.sqrt_nonneg D) hDroot
    have hsqrt := Real.sq_sqrt hD0
    nlinarith [hsqrt]
  have henergy16 : (∑' n, fractionalPowerEnergyTerm 1 sigma a n) ≤
      16 * B ^ 2 := by
    dsimp [A, D] at hAle hDle
    exact henergy.trans (by nlinarith)
  have hvec :
      weightedCoeffToLp 1 sigma
          (intervalDomainPerturbationCosineCoeff uStar (u s))
          (intervalDomainX2SigmaPerturbation_of_classical_positive
            hsol hs hsigma1) -
        weightedCoeffToLp 1 sigma
          (intervalDomainPerturbationCosineCoeff uStar (u t))
          (intervalDomainX2SigmaPerturbation_of_classical_positive
            hsol ht hsigma1) =
      weightedCoeffToLp 1 sigma a hmem := by
    ext n
    change
      (((1 + neumannEigenvalue 1 n) ^ sigma : ℝ) : ℂ) *
          intervalDomainPerturbationCosineCoeff uStar (u s) n -
        (((1 + neumannEigenvalue 1 n) ^ sigma : ℝ) : ℂ) *
          intervalDomainPerturbationCosineCoeff uStar (u t) n =
        (((1 + neumannEigenvalue 1 n) ^ sigma : ℝ) : ℂ) * a n
    rw [hphiCoeff n]
    ring
  rw [hvec, norm_weightedCoeffToLp]
  rw [Real.sqrt_le_iff]
  refine ⟨mul_nonneg (by norm_num) hB, ?_⟩
  nlinarith

/-- Complete weighted coefficient trajectory, extended by zero outside the
positive classical time interval.  All later continuity statements restrict
back to strict positive slabs, so the extension values are immaterial. -/
def intervalDomainStrongCoeffTrajectory
    (p : CM2Params) (T sigma uStar : ℝ)
    (hsigma1 : sigma < 1)
    (u v : ℝ → intervalDomainPoint → ℝ)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (t : ℝ) : CoeffL2 :=
  if ht : t ∈ Set.Ioo (0 : ℝ) T then
    weightedCoeffToLp 1 sigma
      (intervalDomainPerturbationCosineCoeff uStar (u t))
      (intervalDomainX2SigmaPerturbation_of_classical_positive
        hsol ht hsigma1.le)
  else 0

@[simp] theorem intervalDomainStrongCoeffTrajectory_of_mem
    {p : CM2Params} {T sigma uStar t : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hsigma1 : sigma < 1) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    intervalDomainStrongCoeffTrajectory p T sigma uStar hsigma1 u v hsol t =
      weightedCoeffToLp 1 sigma
        (intervalDomainPerturbationCosineCoeff uStar (u t))
        (intervalDomainX2SigmaPerturbation_of_classical_positive
          hsol ht hsigma1.le) := by
  simp only [intervalDomainStrongCoeffTrajectory, dif_pos ht]

set_option maxHeartbeats 800000 in
/-- On every compact positive-time window, the physical perturbation is
continuous in the complete `X_2^sigma` coefficient realization. -/
theorem intervalDomainStrongCoeffTrajectory_continuousOn_strictSlab
    {p : CM2Params} {T sigma uStar a b : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (hsigma1 : sigma < 1) :
    ContinuousOn
      (intervalDomainStrongCoeffTrajectory p T sigma uStar hsigma1 u v hsol)
      (Set.Icc a b) := by
  let K : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hsub : K ⊆ Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1 := by
    intro z hz
    exact ⟨⟨lt_of_lt_of_le ha hz.1.1, lt_of_le_of_lt hz.1.2 hbT⟩, hz.2⟩
  have huJoint : ContinuousOn
      (Function.uncurry (fun r x => intervalDomainLift (u r) x)) K :=
    hsol.regularity.2.2.2.2.2.2.1.mono hsub
  have hFJoint : ContinuousOn
      (Function.uncurry (paper3UxxPhysicalRep p u v)) K := by
    simpa [K] using
      paper3UxxPhysicalRep_continuousOn_strictSlab hsol ha hab hbT
  have huUC : UniformContinuousOn
      (Function.uncurry (fun r x => intervalDomainLift (u r) x)) K :=
    hK.uniformContinuousOn_of_continuous huJoint
  have hFUC : UniformContinuousOn
      (Function.uncurry (paper3UxxPhysicalRep p u v)) K :=
    hK.uniformContinuousOn_of_continuous hFJoint
  rw [Metric.uniformContinuousOn_iff] at huUC hFUC
  rw [Metric.continuousOn_iff]
  intro t ht eps heps
  let eta : ℝ := eps / 5
  have heta : 0 < eta := by dsimp [eta]; linarith
  obtain ⟨δu, hδu, huMod⟩ := huUC eta heta
  obtain ⟨δF, hδF, hFMod⟩ := hFUC eta heta
  refine ⟨min δu δF, lt_min hδu hδF, ?_⟩
  intro s hs hst
  have htPos : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hbT⟩
  have hsPos : s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_of_lt_of_le ha hs.1, lt_of_le_of_lt hs.2 hbT⟩
  have hstu : dist s t < δu := lt_of_lt_of_le hst (min_le_left _ _)
  have hstF : dist s t < δF := lt_of_lt_of_le hst (min_le_right _ _)
  have huBound : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |intervalDomainLift (u s) x - intervalDomainLift (u t) x| ≤ eta := by
    intro x hx
    have hdist : dist ((s, x) : ℝ × ℝ) ((t, x) : ℝ × ℝ) < δu := by
      rw [Prod.dist_eq]
      simpa using hstu
    have h := huMod (s, x) ⟨hs, hx⟩ (t, x) ⟨ht, hx⟩ hdist
    simpa [Function.uncurry, Real.dist_eq] using h.le
  have huxxBound : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |paper3UxxPhysicalRep p u v s x -
        paper3UxxPhysicalRep p u v t x| ≤ eta := by
    intro x hx
    have hdist : dist ((s, x) : ℝ × ℝ) ((t, x) : ℝ × ℝ) < δF := by
      rw [Prod.dist_eq]
      simpa using hstF
    have h := hFMod (s, x) ⟨hs, hx⟩ (t, x) ⟨ht, hx⟩ hdist
    change dist (paper3UxxPhysicalRep p u v s x)
      (paper3UxxPhysicalRep p u v t x) < eta at h
    rw [Real.dist_eq] at h
    exact h.le
  rw [intervalDomainStrongCoeffTrajectory_of_mem hsol hsigma1 hsPos,
    intervalDomainStrongCoeffTrajectory_of_mem hsol hsigma1 htPos,
    dist_eq_norm]
  have hnorm := weightedPerturbationCoeff_sub_norm_le_of_value_uxx_bounds
    (uStar := uStar) hsol hsPos htPos hsigma1.le heta.le huBound huxxBound
  exact hnorm.trans_lt (by dsimp [eta]; linarith)

theorem intervalDomainX2SigmaDistance_continuousOn_strictSlab
    {p : CM2Params} {T sigma uStar a b : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (hsigma1 : sigma < 1) :
    ContinuousOn
      (fun t => intervalDomainX2SigmaDistance sigma uStar (u t))
      (Set.Icc a b) := by
  have hvec := intervalDomainStrongCoeffTrajectory_continuousOn_strictSlab
    (uStar := uStar) hsol ha hab hbT hsigma1
  have hnorm := continuous_norm.comp_continuousOn hvec
  refine hnorm.congr ?_
  intro t ht
  have htPos : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hbT⟩
  change intervalDomainX2SigmaDistance sigma uStar (u t) =
    ‖intervalDomainStrongCoeffTrajectory
      p T sigma uStar hsigma1 u v hsol t‖
  rw [intervalDomainStrongCoeffTrajectory_of_mem hsol hsigma1 htPos,
    norm_weightedCoeffToLp]
  rfl

theorem intervalDomainX2SigmaDistance_continuousOn_positive
    {p : CM2Params} {T sigma uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hsigma1 : sigma < 1) :
    ContinuousOn
      (fun t => intervalDomainX2SigmaDistance sigma uStar (u t))
      (Set.Ioo (0 : ℝ) T) := by
  intro t ht
  let a : ℝ := t / 2
  let b : ℝ := (t + T) / 2
  have ha : 0 < a := by dsimp [a]; linarith [ht.1]
  have hab : a ≤ b := by dsimp [a, b]; linarith [ht.1, ht.2]
  have hbT : b < T := by dsimp [b]; linarith [ht.2]
  have hat : a < t := by dsimp [a]; linarith [ht.1]
  have htb : t < b := by dsimp [b]; linarith [ht.2]
  have hslab := intervalDomainX2SigmaDistance_continuousOn_strictSlab
    (uStar := uStar) hsol ha hab hbT hsigma1
  have hatmem : Set.Icc a b ∈ nhds t := Icc_mem_nhds hat htb
  exact (hslab.continuousAt hatmem).continuousWithinAt

#print axioms fractionalPowerEnergyTerm_le_graphEnergy
#print axioms fractionalPowerEnergy_summable_of_graphCoeffs
#print axioms fractionalPowerEnergy_tsum_le_graphCoeffs
#print axioms paper3UxxPhysicalRep_continuousOn_strictSlab
#print axioms paper3UxxPhysicalRep_continuousOn_slice
#print axioms paper3UxxPhysicalRep_eq_liftDeriv2_interior
#print axioms paper3UxxPhysicalRep_cosineCoeff_eq_graphCoeff
#print axioms intervalDomainX2SigmaPerturbation_of_classical_positive
#print axioms weightedPerturbationCoeff_sub_norm_le_of_value_uxx_bounds
#print axioms intervalDomainStrongCoeffTrajectory_of_mem
#print axioms intervalDomainStrongCoeffTrajectory_continuousOn_strictSlab
#print axioms intervalDomainX2SigmaDistance_continuousOn_strictSlab
#print axioms intervalDomainX2SigmaDistance_continuousOn_positive

end

end ShenWork.Paper3
