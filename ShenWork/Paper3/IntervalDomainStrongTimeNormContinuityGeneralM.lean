/- Strong-norm time continuity for faithful general-`m` classical orbits. -/
import ShenWork.Paper3.IntervalDomainStrongTimeContinuityGeneralM
import ShenWork.Paper3.IntervalDomainStrongSliceMembershipGeneralM

namespace ShenWork.Paper3

open MeasureTheory Set
open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.Paper2.IntervalChiNegH1EnergyIdentity
open ShenWork.PDE
open ShenWork.PDE.FractionalPower
open ShenWork.PDE.SectorialOperator

noncomputable section

/-- Any continuous closed-interval representative of the faithful population
Laplacian has the spectral graph coefficient of the perturbation. -/
theorem paper3UxxSlabRep_cosineCoeff_eq_graphCoeff_generalM
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ}
    {T t uStar : ℝ} {F : ℝ → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hF_eq : ∀ x ∈ Set.Ioo (0 : ℝ) 1, F x = liftDeriv2 u t x)
    (n : ℕ) :
    ((cosineCoeffs F n : ℝ) : ℂ) =
      -((neumannEigenvalue 1 n : ℝ) : ℂ) *
        intervalDomainPerturbationCosineCoeff uStar (u t) n := by
  have hC2 := (hsol.regularity.2.2.2.2.1 t ht).1.1
  have htend := (hsol.regularity.2.2.2.1 t ht).1
  have hbc := (hsol.regularity.2.2.2.2.1 t ht).1
  have hrep : cosineCoeffs F n =
      cosineCoeffs (fun x => liftDeriv2 u t x) n :=
    ShenWork.Paper2.BankChemSliceFix.cosineCoeffs_congr_on_Ioo hF_eq n
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
  have hreal : cosineCoeffs F n =
      -neumannEigenvalue 1 n *
        cosineCoeffs (fun x => intervalDomainLift (u t) x - uStar) n := by
    calc
      cosineCoeffs F n =
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

set_option maxHeartbeats 800000 in
-- The graph-energy comparison unfolds two infinite coefficient sums.
/-- Graph-norm continuity estimate using any two continuous representatives
of the faithful population Laplacian. -/
theorem weightedPerturbationCoeff_sub_norm_le_of_value_uxx_bounds_generalM
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ}
    {T s t sigma uStar B : ℝ} {Fs Ft : ℝ → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hs : s ∈ Set.Ioo (0 : ℝ) T) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hsigma1 : sigma ≤ 1) (hB : 0 ≤ B)
    (hFsCont : ContinuousOn Fs (Set.Icc (0 : ℝ) 1))
    (hFtCont : ContinuousOn Ft (Set.Icc (0 : ℝ) 1))
    (hFsEq : ∀ x ∈ Set.Ioo (0 : ℝ) 1, Fs x = liftDeriv2 u s x)
    (hFtEq : ∀ x ∈ Set.Ioo (0 : ℝ) 1, Ft x = liftDeriv2 u t x)
    (huBound : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |intervalDomainLift (u s) x - intervalDomainLift (u t) x| ≤ B)
    (huxxBound : ∀ x ∈ Set.Icc (0 : ℝ) 1, |Fs x - Ft x| ≤ B) :
    ‖weightedCoeffToLp 1 sigma
          (intervalDomainPerturbationCosineCoeff uStar (u s))
          (intervalDomainMX2SigmaPerturbation_of_classical_positive
            hsol hs hsigma1) -
        weightedCoeffToLp 1 sigma
          (intervalDomainPerturbationCosineCoeff uStar (u t))
          (intervalDomainMX2SigmaPerturbation_of_classical_positive
            hsol ht hsigma1)‖ ≤ 4 * B := by
  let phi : ℝ → ℝ := fun x =>
    intervalDomainLift (u s) x - intervalDomainLift (u t) x
  let F : ℝ → ℝ := fun x => Fs x - Ft x
  let ac : ℕ → ℂ := fun n => ((cosineCoeffs phi n : ℝ) : ℂ)
  let bc : ℕ → ℂ := fun n => ((cosineCoeffs F n : ℝ) : ℂ)
  have huS : ContinuousOn (intervalDomainLift (u s)) (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 s hs).1.1.continuousOn
  have huT : ContinuousOn (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 t ht).1.1.continuousOn
  have hphiCont : ContinuousOn phi (Set.Icc (0 : ℝ) 1) := by
    simpa [phi] using huS.sub huT
  have hFCont : ContinuousOn F (Set.Icc (0 : ℝ) 1) := by
    simpa [F] using hFsCont.sub hFtCont
  have hphiData := cosineCoeffs_l2_norm_le_of_pointwise_abs_bound hB
    (hphiCont.aestronglyMeasurable measurableSet_Icc)
    (by simpa [phi] using huBound)
  have hFData := cosineCoeffs_l2_norm_le_of_pointwise_abs_bound hB
    (hFCont.aestronglyMeasurable measurableSet_Icc)
    (by simpa [F] using huxxBound)
  have ha : Summable fun n => ‖ac n‖ ^ 2 := by
    simpa [ac, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hphiData.1
  have hb : Summable fun n => ‖bc n‖ ^ 2 := by
    simpa [bc, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hFData.1
  have hphiSInt : IntervalIntegrable
      (fun x => intervalDomainLift (u s) x - uStar) volume 0 1 :=
    (huS.sub continuousOn_const).intervalIntegrable_of_Icc (by norm_num)
  have hphiTInt : IntervalIntegrable
      (fun x => intervalDomainLift (u t) x - uStar) volume 0 1 :=
    (huT.sub continuousOn_const).intervalIntegrable_of_Icc (by norm_num)
  have hphiCoeff : ∀ n,
      ac n = intervalDomainPerturbationCosineCoeff uStar (u s) n -
        intervalDomainPerturbationCosineCoeff uStar (u t) n := by
    intro n
    have hsub := cosineCoeffs_sub_of_intervalIntegrable n hphiSInt hphiTInt
    have hcongr : cosineCoeffs phi n =
        cosineCoeffs (fun x =>
          (intervalDomainLift (u s) x - uStar) -
            (intervalDomainLift (u t) x - uStar)) n :=
      paper3_cosineCoeffs_congr_on_Icc (fun x _hx => by ring) n
    dsimp [ac]
    rw [hcongr, hsub]
    simp [intervalDomainPerturbationCosineCoeff]
  have hFsInt : IntervalIntegrable Fs volume 0 1 :=
    hFsCont.intervalIntegrable_of_Icc (by norm_num)
  have hFtInt : IntervalIntegrable Ft volume 0 1 :=
    hFtCont.intervalIntegrable_of_Icc (by norm_num)
  have hFCoeff : ∀ n, bc n =
      ((cosineCoeffs Fs n : ℝ) : ℂ) -
        ((cosineCoeffs Ft n : ℝ) : ℂ) := by
    intro n
    have hsub := cosineCoeffs_sub_of_intervalIntegrable n hFsInt hFtInt
    dsimp [bc, F]
    rw [hsub]
    push_cast
    rfl
  have hrel : ∀ n, bc n =
      -((neumannEigenvalue 1 n : ℝ) : ℂ) * ac n := by
    intro n
    rw [hFCoeff n,
      paper3UxxSlabRep_cosineCoeff_eq_graphCoeff_generalM
        (uStar := uStar) hsol hs hFsEq n,
      paper3UxxSlabRep_cosineCoeff_eq_graphCoeff_generalM
        (uStar := uStar) hsol ht hFtEq n,
      hphiCoeff n]
    ring
  have hmem := fractionalPowerEnergy_summable_of_graphCoeffs
    hsigma1 ha hb hrel
  have henergy := fractionalPowerEnergy_tsum_le_graphCoeffs
    hsigma1 ha hb hrel
  let A : ℝ := ∑' n, ‖ac n‖ ^ 2
  let D : ℝ := ∑' n, ‖bc n‖ ^ 2
  have hA0 : 0 ≤ A := tsum_nonneg fun n => sq_nonneg ‖ac n‖
  have hD0 : 0 ≤ D := tsum_nonneg fun n => sq_nonneg ‖bc n‖
  have hAroot : Real.sqrt A ≤ 2 * B := by
    simpa [A, ac, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hphiData.2
  have hDroot : Real.sqrt D ≤ 2 * B := by
    simpa [D, bc, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hFData.2
  have hAle : A ≤ 4 * B ^ 2 := by
    have hsq := mul_self_le_mul_self (Real.sqrt_nonneg A) hAroot
    have hsqrt := Real.sq_sqrt hA0
    nlinarith [hsqrt]
  have hDle : D ≤ 4 * B ^ 2 := by
    have hsq := mul_self_le_mul_self (Real.sqrt_nonneg D) hDroot
    have hsqrt := Real.sq_sqrt hD0
    nlinarith [hsqrt]
  have henergy16 : (∑' n, fractionalPowerEnergyTerm 1 sigma ac n) ≤
      16 * B ^ 2 := by
    dsimp [A, D] at hAle hDle
    exact henergy.trans (by nlinarith)
  have hvec :
      weightedCoeffToLp 1 sigma
          (intervalDomainPerturbationCosineCoeff uStar (u s))
          (intervalDomainMX2SigmaPerturbation_of_classical_positive
            hsol hs hsigma1) -
        weightedCoeffToLp 1 sigma
          (intervalDomainPerturbationCosineCoeff uStar (u t))
          (intervalDomainMX2SigmaPerturbation_of_classical_positive
            hsol ht hsigma1) =
      weightedCoeffToLp 1 sigma ac hmem := by
    ext n
    change
      (((1 + neumannEigenvalue 1 n) ^ sigma : ℝ) : ℂ) *
          intervalDomainPerturbationCosineCoeff uStar (u s) n -
        (((1 + neumannEigenvalue 1 n) ^ sigma : ℝ) : ℂ) *
          intervalDomainPerturbationCosineCoeff uStar (u t) n =
        (((1 + neumannEigenvalue 1 n) ^ sigma : ℝ) : ℂ) * ac n
    rw [hphiCoeff n]
    ring
  rw [hvec, norm_weightedCoeffToLp]
  rw [Real.sqrt_le_iff]
  refine ⟨mul_nonneg (by norm_num) hB, ?_⟩
  nlinarith

/-- Complete strong coefficient trajectory for a faithful general-`m`
classical solution, extended by zero outside its positive lifespan. -/
def intervalDomainMStrongCoeffTrajectory
    (p : CM2Params) (T sigma uStar : ℝ)
    (hsigma1 : sigma < 1)
    (u v : ℝ → intervalDomainPoint → ℝ)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (t : ℝ) : CoeffL2 :=
  if ht : t ∈ Set.Ioo (0 : ℝ) T then
    weightedCoeffToLp 1 sigma
      (intervalDomainPerturbationCosineCoeff uStar (u t))
      (intervalDomainMX2SigmaPerturbation_of_classical_positive
        hsol ht hsigma1.le)
  else 0

@[simp] theorem intervalDomainMStrongCoeffTrajectory_of_mem
    {p : CM2Params} {T sigma uStar t : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hsigma1 : sigma < 1) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    intervalDomainMStrongCoeffTrajectory p T sigma uStar hsigma1 u v hsol t =
      weightedCoeffToLp 1 sigma
        (intervalDomainPerturbationCosineCoeff uStar (u t))
        (intervalDomainMX2SigmaPerturbation_of_classical_positive
          hsol ht hsigma1.le) := by
  simp only [intervalDomainMStrongCoeffTrajectory, dif_pos ht]

set_option maxHeartbeats 800000 in
-- Uniform-continuity moduli are transported through the full graph norm.
/-- On each compact positive-time slab the faithful general-`m` perturbation
is continuous in the complete `X_2^sigma` coefficient realization. -/
theorem intervalDomainMStrongCoeffTrajectory_continuousOn_strictSlab
    {p : CM2Params} {T sigma uStar a b : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (hsigma1 : sigma < 1) :
    ContinuousOn
      (intervalDomainMStrongCoeffTrajectory
        p T sigma uStar hsigma1 u v hsol) (Set.Icc a b) := by
  rcases exists_paper3UxxPhysicalRepGeneralM_continuousOn_strictSlab
      hsol ha hab hbT with ⟨F, hFJoint, hFEq⟩
  let K : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hsub : K ⊆ Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1 := by
    intro z hz
    exact ⟨⟨lt_of_lt_of_le ha hz.1.1, lt_of_le_of_lt hz.1.2 hbT⟩, hz.2⟩
  have huJoint : ContinuousOn
      (Function.uncurry (fun r x => intervalDomainLift (u r) x)) K :=
    hsol.regularity.2.2.2.2.2.2.1.mono hsub
  have huUC : UniformContinuousOn
      (Function.uncurry (fun r x => intervalDomainLift (u r) x)) K :=
    hK.uniformContinuousOn_of_continuous huJoint
  have hFUC : UniformContinuousOn (Function.uncurry F) K :=
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
      |F s x - F t x| ≤ eta := by
    intro x hx
    have hdist : dist ((s, x) : ℝ × ℝ) ((t, x) : ℝ × ℝ) < δF := by
      rw [Prod.dist_eq]
      simpa using hstF
    have h := hFMod (s, x) ⟨hs, hx⟩ (t, x) ⟨ht, hx⟩ hdist
    change dist (F s x) (F t x) < eta at h
    rw [Real.dist_eq] at h
    exact h.le
  have hFs : ContinuousOn (F s) (Set.Icc (0 : ℝ) 1) := by
    exact hFJoint.comp (continuousOn_const.prodMk continuousOn_id)
      (fun x hx => ⟨hs, hx⟩)
  have hFt : ContinuousOn (F t) (Set.Icc (0 : ℝ) 1) := by
    exact hFJoint.comp (continuousOn_const.prodMk continuousOn_id)
      (fun x hx => ⟨ht, hx⟩)
  rw [intervalDomainMStrongCoeffTrajectory_of_mem hsol hsigma1 hsPos,
    intervalDomainMStrongCoeffTrajectory_of_mem hsol hsigma1 htPos,
    dist_eq_norm]
  have hnorm := weightedPerturbationCoeff_sub_norm_le_of_value_uxx_bounds_generalM
    (uStar := uStar) hsol hsPos htPos hsigma1.le heta.le
      hFs hFt (hFEq s hs) (hFEq t ht) huBound huxxBound
  exact hnorm.trans_lt (by dsimp [eta]; linarith)

theorem intervalDomainMX2SigmaDistance_continuousOn_strictSlab
    {p : CM2Params} {T sigma uStar a b : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (hsigma1 : sigma < 1) :
    ContinuousOn (fun t => intervalDomainX2SigmaDistance sigma uStar (u t))
      (Set.Icc a b) := by
  have hvec := intervalDomainMStrongCoeffTrajectory_continuousOn_strictSlab
    (uStar := uStar) hsol ha hab hbT hsigma1
  have hnorm := continuous_norm.comp_continuousOn hvec
  refine hnorm.congr ?_
  intro t ht
  have htPos : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hbT⟩
  change intervalDomainX2SigmaDistance sigma uStar (u t) =
    ‖intervalDomainMStrongCoeffTrajectory
      p T sigma uStar hsigma1 u v hsol t‖
  rw [intervalDomainMStrongCoeffTrajectory_of_mem hsol hsigma1 htPos,
    norm_weightedCoeffToLp]
  rfl

theorem intervalDomainMX2SigmaDistance_continuousOn_positive
    {p : CM2Params} {T sigma uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hsigma1 : sigma < 1) :
    ContinuousOn (fun t => intervalDomainX2SigmaDistance sigma uStar (u t))
      (Set.Ioo (0 : ℝ) T) := by
  intro t ht
  let a : ℝ := t / 2
  let b : ℝ := (t + T) / 2
  have ha : 0 < a := by dsimp [a]; linarith [ht.1]
  have hab : a ≤ b := by dsimp [a, b]; linarith [ht.1, ht.2]
  have hbT : b < T := by dsimp [b]; linarith [ht.2]
  have hat : a < t := by dsimp [a]; linarith [ht.1]
  have htb : t < b := by dsimp [b]; linarith [ht.2]
  have hslab := intervalDomainMX2SigmaDistance_continuousOn_strictSlab
    (uStar := uStar) hsol ha hab hbT hsigma1
  have hatmem : Set.Icc a b ∈ nhds t := Icc_mem_nhds hat htb
  exact (hslab.continuousAt hatmem).continuousWithinAt

#print axioms paper3UxxSlabRep_cosineCoeff_eq_graphCoeff_generalM
#print axioms weightedPerturbationCoeff_sub_norm_le_of_value_uxx_bounds_generalM
#print axioms intervalDomainMStrongCoeffTrajectory_of_mem
#print axioms intervalDomainMStrongCoeffTrajectory_continuousOn_strictSlab
#print axioms intervalDomainMX2SigmaDistance_continuousOn_strictSlab
#print axioms intervalDomainMX2SigmaDistance_continuousOn_positive

end

end ShenWork.Paper3
