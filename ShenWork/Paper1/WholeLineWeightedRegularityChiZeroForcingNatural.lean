import ShenWork.Paper1.WholeLineWeightedRegularityForcingPowerHolderPhysicalWindow
import ShenWork.Paper1.Theorem12WeightedFiniteness

open Filter MeasureTheory Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Reaction-only exact-weight forcing at zero sensitivity

When `chi = 0`, the physical generator forcing contains only the logistic
reaction difference.  Consequently its exact-weight `L2` bounds and time
modulus use only the weighted population trajectory.  No signal trajectory,
flux derivative, or resolver cap is involved.
-/

/-- At zero sensitivity the physical generator forcing is exactly the
weighted logistic reaction difference. -/
theorem paper5WeightedGeneratorForcing_eq_weightedReactionDifference_of_chi_zero
    (p : CMParams) (hchi : p.χ = 0) (eta : ℝ)
    (u v : ℝ → ℝ → ℝ) (U V : ℝ → ℝ) (t x : ℝ) :
    paper5WeightedGeneratorForcing p eta u v U V t x =
      weightedReactionDifference p eta (u t) U x := by
  simp [paper5WeightedGeneratorForcing, weightedReactionDifference, hchi]

/-- Static exact-weight `L2` data for the zero-sensitivity physical forcing.
The bound is the ordinary bounded-set Lipschitz bound for the reaction map. -/
theorem paper5WeightedGeneratorForcing_chi_zero_l2_data
    (p : CMParams) (hchi : p.χ = 0) {M eta t : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hM : 0 ≤ M)
    (hu : IsCUnifBdd (u t)) (hU : IsCUnifBdd U)
    (huM : ∀ x, u t x ∈ Set.Icc (0 : ℝ) M)
    (hUM : ∀ x, U x ∈ Set.Icc (0 : ℝ) M)
    (hclose : Integrable (fun x : ℝ =>
      Real.exp (2 * eta * x) * |u t x - U x| ^ 2)) :
    Integrable (fun x : ℝ =>
        paper5WeightedGeneratorForcing p eta u v U V t x ^ 2) ∧
      (∫ x : ℝ, paper5WeightedGeneratorForcing p eta u v U V t x ^ 2) ≤
        reactionLip p.α M ^ 2 *
          ∫ x : ℝ, Real.exp (2 * eta * x) * |u t x - U x| ^ 2 := by
  simpa only [paper5WeightedGeneratorForcing_eq_weightedReactionDifference_of_chi_zero
    p hchi eta u v U V t] using
    (weighted_reaction_difference_L2eta_bounded
      p hM hu hU huM hUM hclose)

/-- The difference of two zero-sensitivity forcing slices is the weighted
reaction difference of the two population slices; the stationary wave term
cancels. -/
theorem paper5WeightedGeneratorForcing_sub_eq_weightedReactionDifference_of_chi_zero
    (p : CMParams) (hchi : p.χ = 0) (eta : ℝ)
    (u v : ℝ → ℝ → ℝ) (U V : ℝ → ℝ) (s t x : ℝ) :
    paper5WeightedGeneratorForcing p eta u v U V s x -
        paper5WeightedGeneratorForcing p eta u v U V t x =
      weightedReactionDifference p eta (u s) (u t) x := by
  rw [paper5WeightedGeneratorForcing_eq_weightedReactionDifference_of_chi_zero
      p hchi eta u v U V s,
    paper5WeightedGeneratorForcing_eq_weightedReactionDifference_of_chi_zero
      p hchi eta u v U V t]
  unfold weightedReactionDifference
  ring

/-- A weighted-population square modulus transfers directly to the physical
zero-sensitivity forcing. -/
theorem paper5WeightedGeneratorForcing_chi_zero_sub_l2_data
    (p : CMParams) (hchi : p.χ = 0) {M eta s t C rho : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hM : 0 ≤ M)
    (hus : IsCUnifBdd (u s)) (hut : IsCUnifBdd (u t))
    (husM : ∀ x, u s x ∈ Set.Icc (0 : ℝ) M)
    (hutM : ∀ x, u t x ∈ Set.Icc (0 : ℝ) M)
    (hWdiff : Integrable (fun x : ℝ =>
      (paper5WeightedPopulation eta u U s x -
        paper5WeightedPopulation eta u U t x) ^ 2))
    (hWbound : (∫ x : ℝ,
      (paper5WeightedPopulation eta u U s x -
        paper5WeightedPopulation eta u U t x) ^ 2) ≤ C * rho ^ 2) :
    Integrable (fun x : ℝ =>
      (paper5WeightedGeneratorForcing p eta u v U V s x -
        paper5WeightedGeneratorForcing p eta u v U V t x) ^ 2) ∧
      (∫ x : ℝ,
        (paper5WeightedGeneratorForcing p eta u v U V s x -
          paper5WeightedGeneratorForcing p eta u v U V t x) ^ 2) ≤
        reactionLip p.α M ^ 2 * (C * rho ^ 2) := by
  have hweight : ∀ x : ℝ,
      (paper5WeightedPopulation eta u U s x -
          paper5WeightedPopulation eta u U t x) ^ 2 =
        Real.exp (2 * eta * x) * |u s x - u t x| ^ 2 := by
    intro x
    unfold paper5WeightedPopulation
    rw [show
        Real.exp (eta * x) * (u s x - U x) -
            Real.exp (eta * x) * (u t x - U x) =
          Real.exp (eta * x) * (u s x - u t x) by ring,
      mul_pow, sq_abs]
    rw [show Real.exp (eta * x) ^ 2 = Real.exp (2 * eta * x) by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring]
  have hclose : Integrable (fun x : ℝ =>
      Real.exp (2 * eta * x) * |u s x - u t x| ^ 2) := by
    refine hWdiff.congr (Eventually.of_forall fun x => hweight x)
  have hraw := weighted_reaction_difference_L2eta_bounded
    p hM hus hut husM hutM hclose
  have hident : (∫ x : ℝ,
      Real.exp (2 * eta * x) * |u s x - u t x| ^ 2) =
      ∫ x : ℝ,
        (paper5WeightedPopulation eta u U s x -
          paper5WeightedPopulation eta u U t x) ^ 2 := by
    apply integral_congr_ae
    filter_upwards with x
    exact (hweight x).symm
  constructor
  · refine hraw.1.congr (Eventually.of_forall fun x => ?_)
    change weightedReactionDifference p eta (u s) (u t) x ^ 2 =
      (paper5WeightedGeneratorForcing p eta u v U V s x -
        paper5WeightedGeneratorForcing p eta u v U V t x) ^ 2
    rw [paper5WeightedGeneratorForcing_sub_eq_weightedReactionDifference_of_chi_zero
      p hchi eta u v U V s t x]
  · rw [show (∫ x : ℝ,
        (paper5WeightedGeneratorForcing p eta u v U V s x -
          paper5WeightedGeneratorForcing p eta u v U V t x) ^ 2) =
        ∫ x : ℝ, weightedReactionDifference p eta (u s) (u t) x ^ 2 by
      apply integral_congr_ae
      filter_upwards with x
      rw [paper5WeightedGeneratorForcing_sub_eq_weightedReactionDifference_of_chi_zero
        p hchi eta u v U V s t x]]
    calc
      _ ≤ reactionLip p.α M ^ 2 *
          ∫ x : ℝ, Real.exp (2 * eta * x) * |u s x - u t x| ^ 2 :=
        hraw.2
      _ = reactionLip p.α M ^ 2 *
          ∫ x : ℝ,
            (paper5WeightedPopulation eta u U s x -
              paper5WeightedPopulation eta u U t x) ^ 2 := by rw [hident]
      _ ≤ reactionLip p.α M ^ 2 * (C * rho ^ 2) := by
        gcongr

/-- At zero sensitivity, continuity of the two population profiles is enough
for strong measurability of the physical generator forcing.  In particular,
no regularity of either signal profile is used. -/
theorem paper5WeightedGeneratorForcing_chi_zero_aestronglyMeasurable
    (p : CMParams) (hchi : p.χ = 0) (eta : ℝ)
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ} {t : ℝ}
    (hu : IsCUnifBdd (u t)) (hU : IsCUnifBdd U) :
    AEStronglyMeasurable
      (paper5WeightedGeneratorForcing p eta u v U V t) volume := by
  have hru : Continuous (fun x => reactionFun p.α (u t x)) :=
    (continuous_reactionFun (zero_le_one.trans p.hα)).comp hu.1
  have hrU : Continuous (fun x => reactionFun p.α (U x)) :=
    (continuous_reactionFun (zero_le_one.trans p.hα)).comp hU.1
  have hexp : Continuous (fun x : ℝ => Real.exp (eta * x)) := by
    fun_prop
  have hreact : AEStronglyMeasurable
      (weightedReactionDifference p eta (u t) U) volume := by
    exact (hexp.mul (hru.sub hrU)).aestronglyMeasurable
  refine hreact.congr (Eventually.of_forall fun x => ?_)
  exact
    (paper5WeightedGeneratorForcing_eq_weightedReactionDifference_of_chi_zero
      p hchi eta u v U V t x).symm

/-- Natural positive-window forcing data for `chi = 0`.

The only time modulus assumed is the exact-weight population modulus.  The
result supplies, in one bundle, the uniform scalar `L2` estimate, a Holder
modulus and global continuity for the time-clamped canonical Hilbert
trajectory, and its almost-everywhere identification with the physical
forcing on the window.  These are precisely the forcing-side inputs of the
exact-generator restart window. -/
theorem
    exists_paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory_chi_zero_data
    (p : CMParams) (hchi : p.χ = 0)
    {M eta c a b theta EW HW : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hab : a ≤ b) (hM : 0 ≤ M) (htheta : 0 < theta)
    (huC : ∀ q ∈ Set.Icc a b, IsCUnifBdd (coMovingPath c u q))
    (hUC : IsCUnifBdd U)
    (huM : ∀ q ∈ Set.Icc a b, ∀ x,
      coMovingPath c u q x ∈ Set.Icc (0 : ℝ) M)
    (hUM : ∀ x, U x ∈ Set.Icc (0 : ℝ) M)
    (hclose : ∀ q ∈ Set.Icc a b, Integrable (fun x : ℝ =>
      Real.exp (2 * eta * x) * |coMovingPath c u q x - U x| ^ 2))
    (hclose_le : ∀ q ∈ Set.Icc a b,
      (∫ x : ℝ, Real.exp (2 * eta * x) *
        |coMovingPath c u q x - U x| ^ 2) ≤ EW ^ 2)
    (hWdiff : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
      Integrable (fun x : ℝ =>
        (paper5WeightedPopulation eta (coMovingPath c u) U s x -
          paper5WeightedPopulation eta (coMovingPath c u) U t x) ^ 2))
    (hWdiff_le : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
      (∫ x : ℝ,
        (paper5WeightedPopulation eta (coMovingPath c u) U s x -
          paper5WeightedPopulation eta (coMovingPath c u) U t x) ^ 2) ≤
        HW ^ 2 * (|s - t| ^ theta) ^ 2) :
    let F : ℝ → WholeLineRealL2 :=
      paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory
        p eta c u v U V hab
    ∃ H : ℝ, 0 ≤ H ∧
      (∀ q ∈ Set.Icc a b,
        Integrable (fun x : ℝ =>
          paper5WeightedGeneratorForcing p eta
            (coMovingPath c u) (coMovingPath c v) U V q x ^ 2) ∧
        (∫ x : ℝ, paper5WeightedGeneratorForcing p eta
          (coMovingPath c u) (coMovingPath c v) U V q x ^ 2) ≤
            reactionLip p.α M ^ 2 * EW ^ 2) ∧
      (∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
        ‖F s - F t‖ ≤ H * |s - t| ^ theta) ∧
      Continuous F ∧
      (∀ q ∈ Set.Icc a b,
        (((F q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
          paper5WeightedGeneratorForcing p eta
            (coMovingPath c u) (coMovingPath c v) U V q)) := by
  dsimp only
  let g : ℝ → ℝ → ℝ :=
    paper5WeightedGeneratorForcing p eta
      (coMovingPath c u) (coMovingPath c v) U V
  have hg_meas : ∀ q ∈ Set.Icc a b,
      AEStronglyMeasurable (g q) volume := by
    intro q hq
    exact paper5WeightedGeneratorForcing_chi_zero_aestronglyMeasurable
      p hchi eta (huC q hq) hUC
  have hg_data : ∀ q ∈ Set.Icc a b,
      Integrable (fun x : ℝ => g q x ^ 2) ∧
        (∫ x : ℝ, g q x ^ 2) ≤
          reactionLip p.α M ^ 2 * EW ^ 2 := by
    intro q hq
    have hraw := paper5WeightedGeneratorForcing_chi_zero_l2_data
      p hchi (u := coMovingPath c u) (v := coMovingPath c v)
        (U := U) (V := V) hM (huC q hq) hUC (huM q hq) hUM
        (hclose q hq)
    exact ⟨hraw.1, hraw.2.trans (by
      gcongr
      exact hclose_le q hq)⟩
  have hg_sq : ∀ q ∈ Set.Icc a b,
      Integrable (fun x : ℝ => g q x ^ 2) :=
    fun q hq => (hg_data q hq).1
  let C : ℝ := reactionLip p.α M ^ 2 * HW ^ 2
  let H : ℝ := Real.sqrt C
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hH : 0 ≤ H := Real.sqrt_nonneg _
  have hholder : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
      ‖wholeLineRealL2PositiveWindowTrajectory hab g s -
          wholeLineRealL2PositiveWindowTrajectory hab g t‖ ≤
        H * |s - t| ^ theta := by
    intro s hs t ht
    have hraw := paper5WeightedGeneratorForcing_chi_zero_sub_l2_data
      p hchi (u := coMovingPath c u) (v := coMovingPath c v)
        (U := U) (V := V) hM (huC s hs) (huC t ht)
        (huM s hs) (huM t ht)
        (hWdiff s hs t ht) (hWdiff_le s hs t ht)
    apply
      wholeLineRealL2PositiveWindowTrajectory_norm_sub_le_of_integral_sub_sq_le_modulus
        hab hg_meas hg_sq hs ht hC (Real.rpow_nonneg (abs_nonneg _) _)
    calc
      (∫ x : ℝ, (g s x - g t x) ^ 2) ≤
          reactionLip p.α M ^ 2 *
            (HW ^ 2 * (|s - t| ^ theta) ^ 2) := hraw.2
      _ = C * (|s - t| ^ theta) ^ 2 := by
        dsimp only [C]
        ring
  refine ⟨H, hH, hg_data, hholder, ?_, ?_⟩
  · exact wholeLineRealL2PositiveWindowTrajectory_continuous_of_holder
      hab htheta hH hholder
  · intro q hq
    exact wholeLineRealL2PositiveWindowTrajectory_coe_ae_of_mem
      hab hg_meas hg_sq hq

end ShenWork.Paper1

#print axioms
  ShenWork.Paper1.paper5WeightedGeneratorForcing_eq_weightedReactionDifference_of_chi_zero
#print axioms
  ShenWork.Paper1.paper5WeightedGeneratorForcing_chi_zero_l2_data
#print axioms
  ShenWork.Paper1.paper5WeightedGeneratorForcing_sub_eq_weightedReactionDifference_of_chi_zero
#print axioms
  ShenWork.Paper1.paper5WeightedGeneratorForcing_chi_zero_sub_l2_data
#print axioms
  ShenWork.Paper1.paper5WeightedGeneratorForcing_chi_zero_aestronglyMeasurable
#print axioms
  ShenWork.Paper1.exists_paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory_chi_zero_data
