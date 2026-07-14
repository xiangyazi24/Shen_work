import ShenWork.Paper1.WholeLineCauchyDuhamel
import ShenWork.Paper1.WaveRotheTrunc

open Filter Topology MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Global truncations for the whole-line Cauchy map

The genuine nonlinearities are locally Lipschitz on a nonnegative bounded
strip.  Composing every population profile with `clampIcc M` turns them into
globally defined bounded Lipschitz sources.  The truncation is invisible once
the solution is shown to remain in `[0,M]`.
-/

/-- Pointwise projection of a profile onto the nonnegative strip `[0,M]`. -/
def wholeLineCauchyClampProfile (M : ℝ) (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  clampIcc M (u x)

theorem wholeLineCauchyClampProfile_mem_Icc
    {M : ℝ} (hM : 0 ≤ M) (u : ℝ → ℝ) (x : ℝ) :
    wholeLineCauchyClampProfile M u x ∈ Set.Icc (0 : ℝ) M :=
  clampIcc_mem_Icc hM (u x)

theorem wholeLineCauchyClampProfile_isCUnifBdd
    {M : ℝ} (hM : 0 ≤ M) {u : ℝ → ℝ} (hu : IsCUnifBdd u) :
    IsCUnifBdd (wholeLineCauchyClampProfile M u) := by
  refine ⟨(clampIcc_lipschitz M).continuous.comp hu.1, ⟨M, ?_⟩⟩
  intro x
  have hx := wholeLineCauchyClampProfile_mem_Icc hM u x
  simpa [abs_of_nonneg hx.1] using hx.2

theorem wholeLineCauchyClampProfile_diff_abs_le
    (M : ℝ) {u w : ℝ → ℝ} {D : ℝ}
    (hD : ∀ x, |u x - w x| ≤ D) (x : ℝ) :
    |wholeLineCauchyClampProfile M u x -
        wholeLineCauchyClampProfile M w x| ≤ D := by
  have hlip := (clampIcc_lipschitz M).dist_le_mul (u x) (w x)
  rw [NNReal.coe_one, one_mul, Real.dist_eq, Real.dist_eq] at hlip
  exact hlip.trans (hD x)

theorem wholeLineCauchyClampProfile_eq_of_mem_Icc
    {M : ℝ} (hM : 0 ≤ M) {u : ℝ → ℝ}
    (huM : ∀ x, u x ∈ Set.Icc (0 : ℝ) M) :
    wholeLineCauchyClampProfile M u = u := by
  funext x
  exact clampIcc_eqOn_Icc hM (huM x)

/-- Globally truncated chemotaxis flux. -/
def wholeLineCauchyTruncatedFlux
    (p : CMParams) (M : ℝ) (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  wholeLineChemotaxisFlux p (wholeLineCauchyClampProfile M u) x

theorem wholeLineCauchyTruncatedFlux_abs_le
    (p : CMParams) {M : ℝ} (hM : 0 ≤ M)
    {u : ℝ → ℝ} (hu : IsCUnifBdd u) (x : ℝ) :
    |wholeLineCauchyTruncatedFlux p M u x| ≤
      M ^ p.m * M ^ p.γ := by
  exact wholeLineChemotaxisFlux_abs_le p hM
    (wholeLineCauchyClampProfile_isCUnifBdd hM hu)
    (wholeLineCauchyClampProfile_mem_Icc hM u) x

theorem wholeLineCauchyTruncatedFlux_diff_abs_le
    (p : CMParams) {M D : ℝ} (hM : 0 ≤ M)
    {u w : ℝ → ℝ} (hu : IsCUnifBdd u) (hw : IsCUnifBdd w)
    (hD : ∀ x, |u x - w x| ≤ D) (x : ℝ) :
    |wholeLineCauchyTruncatedFlux p M u x -
        wholeLineCauchyTruncatedFlux p M w x| ≤
      wholeLineCauchyFluxLip p M * D := by
  simpa [wholeLineCauchyTruncatedFlux, wholeLineCauchyFluxLip] using
    wholeLineChemotaxisFlux_diff_abs_le p hM
      (wholeLineCauchyClampProfile_isCUnifBdd hM hu)
      (wholeLineCauchyClampProfile_isCUnifBdd hM hw)
      (wholeLineCauchyClampProfile_mem_Icc hM u)
      (wholeLineCauchyClampProfile_mem_Icc hM w)
      (wholeLineCauchyClampProfile_diff_abs_le M hD) x

theorem wholeLineCauchyTruncatedFlux_eq_of_mem_Icc
    (p : CMParams) {M : ℝ} (hM : 0 ≤ M) {u : ℝ → ℝ}
    (huM : ∀ x, u x ∈ Set.Icc (0 : ℝ) M) :
    wholeLineCauchyTruncatedFlux p M u = wholeLineChemotaxisFlux p u := by
  unfold wholeLineCauchyTruncatedFlux
  rw [wholeLineCauchyClampProfile_eq_of_mem_Icc hM huM]

/-- Globally truncated source paired with the shifted generator `Delta-I`. -/
def wholeLineCauchyTruncatedReaction
    (p : CMParams) (M : ℝ) (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  wholeLineCauchyShiftedReaction p (wholeLineCauchyClampProfile M u) x

theorem wholeLineCauchyTruncatedReaction_abs_le
    (p : CMParams) {M : ℝ} (hM : 0 ≤ M)
    (u : ℝ → ℝ) (x : ℝ) :
    |wholeLineCauchyTruncatedReaction p M u x| ≤
      M + M * (1 + M ^ p.α) := by
  exact wholeLineCauchyShiftedReaction_abs_le p hM
    (wholeLineCauchyClampProfile_mem_Icc hM u) x

theorem wholeLineCauchyTruncatedReaction_diff_abs_le
    (p : CMParams) {M D : ℝ} (hM : 0 ≤ M)
    {u w : ℝ → ℝ} (hD : ∀ x, |u x - w x| ≤ D) (x : ℝ) :
    |wholeLineCauchyTruncatedReaction p M u x -
        wholeLineCauchyTruncatedReaction p M w x| ≤
      (1 + reactionLip p.α M) * D := by
  exact wholeLineCauchyShiftedReaction_diff_abs_le p hM
    (wholeLineCauchyClampProfile_mem_Icc hM u)
    (wholeLineCauchyClampProfile_mem_Icc hM w)
    (wholeLineCauchyClampProfile_diff_abs_le M hD) x

theorem wholeLineCauchyTruncatedReaction_eq_of_mem_Icc
    (p : CMParams) {M : ℝ} (hM : 0 ≤ M) {u : ℝ → ℝ}
    (huM : ∀ x, u x ∈ Set.Icc (0 : ℝ) M) :
    wholeLineCauchyTruncatedReaction p M u =
      wholeLineCauchyShiftedReaction p u := by
  unfold wholeLineCauchyTruncatedReaction
  rw [wholeLineCauchyClampProfile_eq_of_mem_Icc hM huM]

/-- The corrected mild map with both nonlinear sources globally truncated. -/
def wholeLineCauchyTruncatedMildMap
    (p : CMParams) (M : ℝ) (u₀ : ℝ → ℝ)
    (U : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  wholeLineCauchyMildMap p u₀
    (fun s => wholeLineCauchyClampProfile M (U s)) t x

theorem wholeLineCauchyTruncatedMildMap_eq_of_mem_Icc
    (p : CMParams) {M : ℝ} (hM : 0 ≤ M) (u₀ : ℝ → ℝ)
    {U : ℝ → ℝ → ℝ}
    (hUM : ∀ s x, U s x ∈ Set.Icc (0 : ℝ) M) :
    wholeLineCauchyTruncatedMildMap p M u₀ U =
      wholeLineCauchyMildMap p u₀ U := by
  unfold wholeLineCauchyTruncatedMildMap
  have hprofiles :
      (fun s => wholeLineCauchyClampProfile M (U s)) = U := by
    funext s
    exact wholeLineCauchyClampProfile_eq_of_mem_Icc hM (hUM s)
  rw [hprofiles]

section WholeLineCauchyTruncationAxiomAudit

#print axioms wholeLineCauchyClampProfile_isCUnifBdd
#print axioms wholeLineCauchyClampProfile_diff_abs_le
#print axioms wholeLineCauchyTruncatedFlux_abs_le
#print axioms wholeLineCauchyTruncatedFlux_diff_abs_le
#print axioms wholeLineCauchyTruncatedReaction_abs_le
#print axioms wholeLineCauchyTruncatedReaction_diff_abs_le
#print axioms wholeLineCauchyTruncatedMildMap_eq_of_mem_Icc

end WholeLineCauchyTruncationAxiomAudit

end ShenWork.Paper1
