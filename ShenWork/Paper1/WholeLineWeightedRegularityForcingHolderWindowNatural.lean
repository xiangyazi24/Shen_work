import ShenWork.Paper1.WholeLineWeightedRegularityForcingHolderExact
import ShenWork.Paper1.WholeLineWeightedRegularityForcingWindowNatural
import ShenWork.Paper1.WholeLineWeightedRegularityBUCTimeHolder
import ShenWork.Paper1.WholeLineWeightedRegularityPositiveWindowForcing

open Filter MeasureTheory Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Quantitative exact-weight forcing on a positive window

This file transfers the quantitative scalar forcing estimates to the
canonical time-clamped `L²(ℝ)` trajectory used on compact positive-time
windows.  All estimates remain at the exact exponential weight.
-/

/-- A scalar square-modulus estimate on the physical window is the
corresponding norm modulus for the canonical time-clamped `L²` trajectory.
-/
theorem wholeLineRealL2PositiveWindowTrajectory_norm_sub_le_of_integral_sub_sq_le_modulus
    {a b : ℝ} (hab : a ≤ b) {g : ℝ → ℝ → ℝ}
    (hg_meas : ∀ q ∈ Set.Icc a b,
      AEStronglyMeasurable (g q) volume)
    (hg_sq : ∀ q ∈ Set.Icc a b,
      Integrable (fun x : ℝ => g q x ^ 2) volume)
    {s t C rho : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b)
    (hC : 0 ≤ C) (hrho : 0 ≤ rho)
    (hbound : (∫ x : ℝ, (g s x - g t x) ^ 2) ≤ C * rho ^ 2) :
    ‖wholeLineRealL2PositiveWindowTrajectory hab g s -
        wholeLineRealL2PositiveWindowTrajectory hab g t‖ ≤
      Real.sqrt C * rho := by
  let tau : ℝ → ℝ := fun q => (Set.projIcc a b hab q : ℝ)
  let gc : ℝ → ℝ → ℝ := fun q => g (tau q)
  have htau_mem : ∀ q, tau q ∈ Set.Icc a b :=
    fun q => (Set.projIcc a b hab q).2
  have hgc_meas : ∀ q, AEStronglyMeasurable (gc q) volume :=
    fun q => hg_meas (tau q) (htau_mem q)
  have hgc_sq : ∀ q, Integrable (fun x : ℝ => gc q x ^ 2) volume :=
    fun q => hg_sq (tau q) (htau_mem q)
  have heq : wholeLineRealL2PositiveWindowTrajectory hab g =
      wholeLineRealL2Section gc hgc_meas hgc_sq := by
    funext q
    rw [wholeLineRealL2PositiveWindowTrajectory, wholeLineRealL2Total,
      dif_pos ⟨hgc_meas q, hgc_sq q⟩]
    rfl
  rw [heq]
  have htaus : tau s = s := by
    dsimp only [tau]
    exact congrArg Subtype.val (Set.projIcc_of_mem hab hs)
  have htaut : tau t = t := by
    dsimp only [tau]
    exact congrArg Subtype.val (Set.projIcc_of_mem hab ht)
  apply wholeLineRealL2Section_norm_sub_le_of_integral_sub_sq_le_modulus
    hgc_meas hgc_sq hC hrho
  simpa only [gc, htaus, htaut] using hbound

set_option maxHeartbeats 3000000 in
/-- Positive-window form of the exact-weight forcing estimate.  The common
modulus `rho` is deliberately abstract: in particular, no square-root time
modulus is asserted for subquadratic sensitivity exponents.  Only the final
forcing representatives are required to be square-integrable on the
physical window.  The signal difference moduli are produced internally by
the frozen resolver. -/
theorem
    paper5WeightedGeneratorForcingExpandedPositiveWindowL2Trajectory_norm_sub_le_of_population_H1_modulus
    (p : CMParams) {M eta a b s t rho : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    {K₁ K₂ K₃ K₄ KR D₁ D₂ DR : ℝ}
    {EW EWx EZ EZx HW HWx : ℝ}
    (hab : a ≤ b) (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b)
    (hM : 1 ≤ M) (heta : 0 < eta) (heta1 : eta < 1)
    (huC : ∀ q, IsCUnifBdd (u q))
    (huM : ∀ q x, u q x ∈ Set.Icc (0 : ℝ) M)
    (hvEq : ∀ q, v q = frozenElliptic p (u q))
    (hvDiff : ∀ q, Differentiable ℝ (v q))
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hK₃ : 0 ≤ K₃) (hK₄ : 0 ≤ K₄) (hKR : 0 ≤ KR)
    (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) (hDR : 0 ≤ DR)
    (hEW : 0 ≤ EW) (hEWx : 0 ≤ EWx)
    (hEZ : 0 ≤ EZ) (hEZx : 0 ≤ EZx)
    (hHW : 0 ≤ HW) (hHWx : 0 ≤ HWx) (hrho : 0 ≤ rho)
    (hB₁_bound : ∀ x, |paper5B1 p u v s x| ≤ K₁)
    (hB₁_diff : ∀ x,
      |paper5B1 p u v s x - paper5B1 p u v t x| ≤ D₁ * rho)
    (hB₂_bound : ∀ x,
      |paper5WeightedFluxPopulationCoefficient p eta u v U s x| ≤ K₂)
    (hB₂_diff : ∀ x,
      |paper5WeightedFluxPopulationCoefficient p eta u v U s x -
        paper5WeightedFluxPopulationCoefficient p eta u v U t x| ≤ D₂ * rho)
    (hB₃_bound : ∀ x, |paper5B3 p U x| ≤ K₃)
    (hB₄_bound : ∀ x,
      |paper5WeightedFluxSignalCoefficient p eta U x| ≤ K₄)
    (hR_bound : ∀ x, |1 - paper5A (1 + p.α) u U s x| ≤ KR)
    (hR_diff : ∀ x,
      |(1 - paper5A (1 + p.α) u U s x) -
        (1 - paper5A (1 + p.α) u U t x)| ≤ DR * rho)
    (hB₁_meas : ∀ q, AEStronglyMeasurable (paper5B1 p u v q) volume)
    (hB₂_meas : ∀ q, AEStronglyMeasurable
      (paper5WeightedFluxPopulationCoefficient p eta u v U q) volume)
    (hB₃_meas : AEStronglyMeasurable (paper5B3 p U) volume)
    (hB₄_meas : AEStronglyMeasurable
      (paper5WeightedFluxSignalCoefficient p eta U) volume)
    (hR_meas : ∀ q, AEStronglyMeasurable
      (fun x => 1 - paper5A (1 + p.α) u U q x) volume)
    (hW_meas : ∀ q, AEStronglyMeasurable
      (paper5WeightedPopulation eta u U q) volume)
    (hWx_meas : ∀ q, AEStronglyMeasurable
      (paper5WeightedPopulationX eta u U q) volume)
    (hZ_meas : ∀ q, AEStronglyMeasurable
      (paper5WeightedSignal eta v V q) volume)
    (hZx_meas : ∀ q, AEStronglyMeasurable
      (paper5WeightedSignalX eta v V q) volume)
    (hF_meas : ∀ q ∈ Set.Icc a b, AEStronglyMeasurable
      (paper5WeightedGeneratorForcingExpandedTrajectory p eta u v U
        (paper5WeightedPopulation eta u U)
        (paper5WeightedPopulationX eta u U)
        (paper5WeightedSignal eta v V)
        (paper5WeightedSignalX eta v V) q) volume)
    (hF_sq : ∀ q ∈ Set.Icc a b, Integrable (fun x =>
      paper5WeightedGeneratorForcingExpandedTrajectory p eta u v U
        (paper5WeightedPopulation eta u U)
        (paper5WeightedPopulationX eta u U)
        (paper5WeightedSignal eta v V)
        (paper5WeightedSignalX eta v V) q x ^ 2) volume)
    (hW_diff : Integrable (fun x =>
      (paper5WeightedPopulation eta u U s x -
        paper5WeightedPopulation eta u U t x) ^ 2) volume)
    (hWx_diff : Integrable (fun x =>
      (paper5WeightedPopulationX eta u U s x -
        paper5WeightedPopulationX eta u U t x) ^ 2) volume)
    (hW_t : Integrable (fun x => paper5WeightedPopulation eta u U t x ^ 2) volume)
    (hWx_t : Integrable (fun x => paper5WeightedPopulationX eta u U t x ^ 2) volume)
    (hZ_t : Integrable (fun x => paper5WeightedSignal eta v V t x ^ 2) volume)
    (hZx_t : Integrable (fun x => paper5WeightedSignalX eta v V t x ^ 2) volume)
    (hW_diff_bound : (∫ x : ℝ,
      (paper5WeightedPopulation eta u U s x -
        paper5WeightedPopulation eta u U t x) ^ 2) ≤ HW ^ 2 * rho ^ 2)
    (hWx_diff_bound : (∫ x : ℝ,
      (paper5WeightedPopulationX eta u U s x -
        paper5WeightedPopulationX eta u U t x) ^ 2) ≤ HWx ^ 2 * rho ^ 2)
    (hW_t_bound : (∫ x : ℝ,
      paper5WeightedPopulation eta u U t x ^ 2) ≤ EW ^ 2)
    (hWx_t_bound : (∫ x : ℝ,
      paper5WeightedPopulationX eta u U t x ^ 2) ≤ EWx ^ 2)
    (hZ_t_bound : (∫ x : ℝ,
      paper5WeightedSignal eta v V t x ^ 2) ≤ EZ ^ 2)
    (hZx_t_bound : (∫ x : ℝ,
      paper5WeightedSignalX eta v V t x ^ 2) ≤ EZx ^ 2) :
    let HZ := Real.sqrt (paper5WeightedResolverVFactor p M eta) * HW
    let HZx := Real.sqrt (paper5WeightedResolverVxFactor p M eta) * HW
    ‖wholeLineRealL2PositiveWindowTrajectory hab
          (paper5WeightedGeneratorForcingExpandedTrajectory p eta u v U
            (paper5WeightedPopulation eta u U)
            (paper5WeightedPopulationX eta u U)
            (paper5WeightedSignal eta v V)
            (paper5WeightedSignalX eta v V)) s -
        wholeLineRealL2PositiveWindowTrajectory hab
          (paper5WeightedGeneratorForcingExpandedTrajectory p eta u v U
            (paper5WeightedPopulation eta u U)
            (paper5WeightedPopulationX eta u U)
            (paper5WeightedSignal eta v V)
            (paper5WeightedSignalX eta v V)) t‖ ≤
      Real.sqrt (paper5WeightedGeneratorForcingHolderSquareConst p
        K₁ K₂ K₃ K₄ KR D₁ D₂ DR EWx EW HWx HW HZx HZ) * rho := by
  dsimp only
  let RV := paper5WeightedResolverVFactor p M eta
  let RVx := paper5WeightedResolverVxFactor p M eta
  let HZ := Real.sqrt RV * HW
  let HZx := Real.sqrt RVx * HW
  have hRV : 0 ≤ RV := by
    dsimp only [RV, paper5WeightedResolverVFactor]
    exact div_nonneg
      (mul_nonneg (sq_nonneg p.γ) (Real.rpow_nonneg (zero_le_one.trans hM) _))
      (sq_nonneg (1 - eta))
  have hetaSq : eta ^ 2 < 1 := by
    have hprod : 0 < (1 - eta) * (1 + eta) :=
      mul_pos (sub_pos.mpr heta1) (by linarith)
    nlinarith
  have hRVx : 0 ≤ RVx := by
    dsimp only [RVx, paper5WeightedResolverVxFactor]
    exact div_nonneg
      (mul_nonneg (sq_nonneg p.γ) (Real.rpow_nonneg (zero_le_one.trans hM) _))
      (sub_nonneg.mpr hetaSq.le)
  have hHZ : 0 ≤ HZ := mul_nonneg (Real.sqrt_nonneg _) hHW
  have hHZx : 0 ≤ HZx := mul_nonneg (Real.sqrt_nonneg _) hHW
  have hresolver := paper5WeightedSignal_sub_sq_data_of_population_modulus
    p (U := U) (V := V) hM heta heta1 huC huM hvEq hvDiff
      hHW hrho hW_diff hW_diff_bound
  have hZ_diff_bound : (∫ x : ℝ,
      (paper5WeightedSignal eta v V s x -
        paper5WeightedSignal eta v V t x) ^ 2) ≤ HZ ^ 2 * rho ^ 2 := by
    calc
      _ ≤ RV * HW ^ 2 * rho ^ 2 := by simpa only [RV] using hresolver.2.2.1
      _ = HZ ^ 2 * rho ^ 2 := by
        dsimp only [HZ]
        rw [mul_pow, Real.sq_sqrt hRV]
  have hZx_diff_bound : (∫ x : ℝ,
      (paper5WeightedSignalX eta v V s x -
        paper5WeightedSignalX eta v V t x) ^ 2) ≤ HZx ^ 2 * rho ^ 2 := by
    calc
      _ ≤ RVx * HW ^ 2 * rho ^ 2 := by simpa only [RVx] using hresolver.2.2.2
      _ = HZx ^ 2 * rho ^ 2 := by
        dsimp only [HZx]
        rw [mul_pow, Real.sq_sqrt hRVx]
  have hflux :=
    paper5WeightedFluxDerivativeExpandedTrajectory_sub_sq_data_of_modulus
      p eta hK₁ hK₂ hK₃ hK₄ hD₁ hD₂ hEW hEWx hEZ hEZx
        hHW hHWx hHZ hHZx hrho hB₁_bound hB₁_diff hB₂_bound hB₂_diff
        hB₃_bound hB₄_bound hB₁_meas hB₂_meas hB₃_meas hB₄_meas
        hW_meas hWx_meas hZ_meas hZx_meas hW_diff hWx_diff
        hresolver.1 hresolver.2.1 hW_t hWx_t hZ_t hZx_t
        hW_diff_bound hWx_diff_bound hZ_diff_bound hZx_diff_bound
        hW_t_bound hWx_t_bound hZ_t_bound hZx_t_bound
  have hreact :=
    paper5WeightedReactionExpandedTrajectory_sub_sq_data_of_modulus
      p hKR hDR hEW hHW hrho hR_bound hR_diff hR_meas hW_meas
        hW_diff hW_t hW_diff_bound hW_t_bound
  have hflux_meas : ∀ q, AEStronglyMeasurable
      (paper5WeightedFluxDerivativeExpandedTrajectory p eta u v U
        (paper5WeightedPopulation eta u U)
        (paper5WeightedPopulationX eta u U)
        (paper5WeightedSignal eta v V)
        (paper5WeightedSignalX eta v V) q) volume := by
    intro q
    exact paper5WeightedFluxDerivativeExpandedTrajectory_aestronglyMeasurable
      p eta q (hB₁_meas q) (hB₂_meas q) hB₃_meas hB₄_meas
        (hW_meas q) (hWx_meas q) (hZ_meas q) (hZx_meas q)
  have hreact_meas : ∀ q, AEStronglyMeasurable
      (paper5WeightedReactionExpandedTrajectory p u U
        (paper5WeightedPopulation eta u U) q) volume := by
    intro q
    exact paper5WeightedReactionExpandedTrajectory_aestronglyMeasurable
      p q (hR_meas q) (hW_meas q)
  let CF := paper5WeightedFluxHolderSquareConst
    K₁ K₂ K₃ K₄ D₁ D₂ EWx EW HWx HW HZx HZ
  let CR := paper5WeightedReactionHolderSquareConst KR DR EW HW
  let C := paper5WeightedGeneratorForcingHolderSquareConst p
    K₁ K₂ K₃ K₄ KR D₁ D₂ DR EWx EW HWx HW HZx HZ
  have hCF : 0 ≤ CF := by
    dsimp only [CF, paper5WeightedFluxHolderSquareConst]
    positivity
  have hCR : 0 ≤ CR := by
    dsimp only [CR, paper5WeightedReactionHolderSquareConst]
    positivity
  have hC : 0 ≤ C := by
    dsimp only [C, paper5WeightedGeneratorForcingHolderSquareConst]
    exact mul_nonneg (by norm_num)
      (add_nonneg (mul_nonneg (sq_nonneg p.χ) hCF) hCR)
  have hforcing :=
    paper5WeightedGeneratorForcingExpandedTrajectory_sub_sq_data_of_flux_reaction_modulus
      p eta hCF hCR hrho hflux_meas hreact_meas hflux.1 hreact.1
        (by simpa only [CF, paper5WeightedFluxHolderSquareConst] using hflux.2)
        (by simpa only [CR, paper5WeightedReactionHolderSquareConst] using hreact.2)
  apply wholeLineRealL2PositiveWindowTrajectory_norm_sub_le_of_integral_sub_sq_le_modulus
    hab hF_meas hF_sq hs ht hC hrho
  simpa only [C, paper5WeightedGeneratorForcingHolderSquareConst] using hforcing.2

section AxiomAudit

#print axioms
  wholeLineRealL2PositiveWindowTrajectory_norm_sub_le_of_integral_sub_sq_le_modulus
#print axioms
  paper5WeightedGeneratorForcingExpandedPositiveWindowL2Trajectory_norm_sub_le_of_population_H1_modulus

end AxiomAudit

end ShenWork.Paper1
