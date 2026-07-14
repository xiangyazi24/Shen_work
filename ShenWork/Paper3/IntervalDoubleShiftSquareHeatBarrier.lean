import ShenWork.Paper2.IntervalBFormSquareHeatT0RestartDerivativeData

open Set

noncomputable section

namespace ShenWork.Paper3

open ShenWork.Paper2.BFormPositiveDatumNegPart
open ShenWork.IntervalNeumannFullKernel

/-- Pull a physical-time field back so that heat time `δ` corresponds to the
physical anchor time `s`.  Keeping the two shifts independent avoids the
repository convention `S_N(0)f = 0` without moving the solution's restart
time. -/
def squareHeatAnchorPullback
    (s δ : ℝ) (F : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun r x => F (s - δ + r) x

theorem restartTimeShift_squareHeatAnchorPullback
    (s δ : ℝ) (F : ℝ → ℝ → ℝ) :
    restartTimeShift δ (squareHeatAnchorPullback s δ F) =
      restartTimeShift s F := by
  funext r x
  simp [restartTimeShift, squareHeatAnchorPullback]
  congr 1
  ring

/-- Lower square-heat barrier on a physical strip restarted at `s`, while the
semigroup is evaluated from an independent strictly positive heat time `δ`.

This is the reusable bridge needed by time-translate arguments: uniform
semigroup approximation may choose `δ` from the restart slice, whereas all
coefficient and solution hypotheses remain expressed at physical times
`s + r`. -/
theorem square_heat_hbarrier_of_independent_positive_heat_shift
    {L s δ A D M : ℝ} {f : ℝ → ℝ} {B C u : ℝ → ℝ → ℝ}
    (hδ : 0 < δ)
    (hf : Continuous f)
    {K : ℝ} (hK : ∀ n, |cosineCoeffs f n| ≤ K)
    (hl2 : Summable fun n : ℕ => (cosineCoeffs f n) ^ 2)
    (hL : 0 < L)
    (hcoeff :
      NeumannLinearDriftCoefficientsRegular L
        (restartTimeShift s B) (restartTimeShift s C))
    (hsuper :
      IsClassicalNeumannLinearDriftSuperSolution L
        (restartTimeShift s B) (restartTimeShift s C)
        (restartTimeShift s u))
    (hM : A ^ 2 / 2 + D ≤ M)
    (hB_bound :
      ∀ r x, 0 < r → r < L → x ∈ Set.Ioo (0 : ℝ) 1 →
        |B (s + r) x| ≤ A)
    (hC_neg_bound :
      ∀ r x, 0 < r → r < L → x ∈ Set.Ioo (0 : ℝ) 1 →
        -C (s + r) x ≤ D)
    (hinitial :
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        squareHeatBarrier M f δ x ≤ u s x) :
    ∀ r x, 0 < r → r < L → x ∈ Set.Icc (0 : ℝ) 1 →
      squareHeatBarrier M f (δ + r) x ≤ u (s + r) x := by
  let B' : ℝ → ℝ → ℝ := squareHeatAnchorPullback s δ B
  let C' : ℝ → ℝ → ℝ := squareHeatAnchorPullback s δ C
  let u' : ℝ → ℝ → ℝ := squareHeatAnchorPullback s δ u
  have hB_shift : restartTimeShift δ B' = restartTimeShift s B := by
    simpa [B'] using restartTimeShift_squareHeatAnchorPullback s δ B
  have hC_shift : restartTimeShift δ C' = restartTimeShift s C := by
    simpa [C'] using restartTimeShift_squareHeatAnchorPullback s δ C
  have hu_shift : restartTimeShift δ u' = restartTimeShift s u := by
    simpa [u'] using restartTimeShift_squareHeatAnchorPullback s δ u
  have hcoeff' :
      NeumannLinearDriftCoefficientsRegular L
        (restartTimeShift δ B') (restartTimeShift δ C') := by
    simpa [hB_shift, hC_shift] using hcoeff
  have hsuper' :
      IsClassicalNeumannLinearDriftSuperSolution L
        (restartTimeShift δ B') (restartTimeShift δ C')
        (restartTimeShift δ u') := by
    simpa [hB_shift, hC_shift, hu_shift] using hsuper
  have hB_bound' :
      ∀ r x, 0 < r → r < L → x ∈ Set.Ioo (0 : ℝ) 1 →
        |B' (δ + r) x| ≤ A := by
    intro r x hr0 hrL hx
    have htime : s - δ + (δ + r) = s + r := by ring
    simpa [B', squareHeatAnchorPullback, htime] using
      hB_bound r x hr0 hrL hx
  have hC_bound' :
      ∀ r x, 0 < r → r < L → x ∈ Set.Ioo (0 : ℝ) 1 →
        -C' (δ + r) x ≤ D := by
    intro r x hr0 hrL hx
    have htime : s - δ + (δ + r) = s + r := by ring
    simpa [C', squareHeatAnchorPullback, htime] using
      hC_neg_bound r x hr0 hrL hx
  have hinitial' :
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        squareHeatBarrier M f δ x ≤ u' δ x := by
    intro x hx
    simpa [u', squareHeatAnchorPullback] using hinitial x hx
  let H : SquareHeatRestartStripData L δ A D M f B' C' u' :=
    squareHeatRestartStripData_of_semigroup
      hδ hf hK hl2 hL hcoeff' hsuper' hM hB_bound' hC_bound' hinitial'
  intro r x hr0 hrL hx
  have hle := square_heat_hbarrier_via_t0_restart (H := H)
    r x hr0 hrL hx
  have htime : s - δ + (δ + r) = s + r := by ring
  simpa [u', squareHeatAnchorPullback, htime] using hle

end ShenWork.Paper3

#print axioms ShenWork.Paper3.square_heat_hbarrier_of_independent_positive_heat_shift
