import ShenWork.Paper1.WholeLineWeightedRegularityLinearSource
import ShenWork.Paper1.Theorem12EnergyProducer

open Filter MeasureTheory Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Concrete data for the weighted lower-order source

The energy calculation only needed a one-sided upper bound on the corrected
`J2` coefficient.  Parabolic `H2` regularity needs the complete lower-order
source in `L2`, and therefore needs an absolute bound.  This file supplies
that missing symmetric estimate and then combines it with the already-proved
weighted resolver data.
-/

/-- Explicit absolute budget for the corrected scalar coefficient. -/
def paper5CorrectedJ2AbsBound
    (p : CMParams) (eta c M B1 B2 : ℝ) : ℝ :=
  |eta ^ 2 - c * eta + 1| +
    (1 + p.α) * M ^ p.α +
    |p.χ| *
      ((2 * p.m + p.γ) * M ^ (p.m + p.γ - 1) +
        |eta| * B1 + B2)

theorem paper5CorrectedJ2AbsBound_nonneg
    (p : CMParams) {eta c M B1 B2 : ℝ}
    (hM : 0 ≤ M) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2) :
    0 ≤ paper5CorrectedJ2AbsBound p eta c M B1 B2 := by
  unfold paper5CorrectedJ2AbsBound
  have hpow_alpha : 0 ≤ M ^ p.α := Real.rpow_nonneg hM _
  have hpow_mgamma : 0 ≤ M ^ (p.m + p.γ - 1) :=
    Real.rpow_nonneg hM _
  have hma : 0 ≤ 1 + p.α := by linarith [p.hα]
  have hmg : 0 ≤ 2 * p.m + p.γ := by linarith [p.hm, p.hγ]
  exact add_nonneg
    (add_nonneg (abs_nonneg _) (mul_nonneg hma hpow_alpha))
    (mul_nonneg (abs_nonneg _)
      (add_nonneg
        (add_nonneg (mul_nonneg hmg hpow_mgamma)
          (mul_nonneg (abs_nonneg _) hB1)) hB2))

/-- Symmetric form of the corrected `J2` coefficient estimate. -/
theorem paper5CorrectedJ2Coefficient_abs_le
    (p : CMParams) {eta c M B1 B2 t x : ℝ}
    {u v : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hM : 0 ≤ M)
    (hu : u t x ∈ Set.Icc (0 : ℝ) M)
    (hU : U x ∈ Set.Icc (0 : ℝ) M)
    (hv : v t x ∈ Set.Icc (0 : ℝ) (M ^ p.γ))
    (hb1 : |paper5B1 p u v t x| ≤ B1)
    (hb2 : |paper5B2 p u v U t x| ≤ B2) :
    |paper5CorrectedJ2Coefficient p eta c u v U t x| ≤
      paper5CorrectedJ2AbsBound p eta c M B1 B2 := by
  have hA : |paper5A (1 + p.α) u U t x| ≤
      (1 + p.α) * M ^ p.α := by
    simpa [paper5A] using
      (paper5MeanCoefficient_abs_le
        (beta := 1 + p.α) (M := M) (s := u t x) (r := U x)
        (by linarith [p.hα]) hM hu hU)
  have hzero := paper5CorrectedChemZeroCoefficient_abs_le
    p hM hu hU hv
  have hetaB1 : |eta * paper5B1 p u v t x| ≤ |eta| * B1 := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hb1 (abs_nonneg eta)
  have hinner :
      |paper5CorrectedChemZeroCoefficient p u v U t x -
          eta * paper5B1 p u v t x + paper5B2 p u v U t x| ≤
        (2 * p.m + p.γ) * M ^ (p.m + p.γ - 1) +
          |eta| * B1 + B2 := by
    calc
      |paper5CorrectedChemZeroCoefficient p u v U t x -
          eta * paper5B1 p u v t x + paper5B2 p u v U t x| ≤
          |paper5CorrectedChemZeroCoefficient p u v U t x| +
            |eta * paper5B1 p u v t x| +
            |paper5B2 p u v U t x| := by
        calc
          |paper5CorrectedChemZeroCoefficient p u v U t x -
              eta * paper5B1 p u v t x + paper5B2 p u v U t x| ≤
              |paper5CorrectedChemZeroCoefficient p u v U t x -
                eta * paper5B1 p u v t x| +
                |paper5B2 p u v U t x| := abs_add_le _ _
          _ ≤ (|paper5CorrectedChemZeroCoefficient p u v U t x| +
                |eta * paper5B1 p u v t x|) +
                |paper5B2 p u v U t x| :=
            by
              have hab := abs_sub
                (paper5CorrectedChemZeroCoefficient p u v U t x)
                (eta * paper5B1 p u v t x)
              linarith
      _ ≤ (2 * p.m + p.γ) * M ^ (p.m + p.γ - 1) +
          |eta| * B1 + B2 := by linarith
  unfold paper5CorrectedJ2Coefficient paper5CorrectedJ2AbsBound
  calc
    |eta ^ 2 - c * eta + 1 - paper5A (1 + p.α) u U t x -
        p.χ *
          (paper5CorrectedChemZeroCoefficient p u v U t x -
            eta * paper5B1 p u v t x + paper5B2 p u v U t x)| ≤
        |eta ^ 2 - c * eta + 1| +
          |paper5A (1 + p.α) u U t x| +
          |p.χ| *
            |paper5CorrectedChemZeroCoefficient p u v U t x -
              eta * paper5B1 p u v t x + paper5B2 p u v U t x| := by
      calc
        |eta ^ 2 - c * eta + 1 - paper5A (1 + p.α) u U t x -
            p.χ *
              (paper5CorrectedChemZeroCoefficient p u v U t x -
                eta * paper5B1 p u v t x +
                  paper5B2 p u v U t x)| ≤
            |eta ^ 2 - c * eta + 1 -
                paper5A (1 + p.α) u U t x| +
              |p.χ *
                (paper5CorrectedChemZeroCoefficient p u v U t x -
                  eta * paper5B1 p u v t x +
                    paper5B2 p u v U t x)| := abs_sub _ _
        _ ≤ (|eta ^ 2 - c * eta + 1| +
              |paper5A (1 + p.α) u U t x|) +
              |p.χ| *
                |paper5CorrectedChemZeroCoefficient p u v U t x -
                  eta * paper5B1 p u v t x +
                    paper5B2 p u v U t x| := by
          rw [abs_mul]
          have hab := abs_sub (eta ^ 2 - c * eta + 1)
            (paper5A (1 + p.α) u U t x)
          linarith
    _ ≤ |eta ^ 2 - c * eta + 1| +
        (1 + p.α) * M ^ p.α +
        |p.χ| *
          ((2 * p.m + p.γ) * M ^ (p.m + p.γ - 1) +
            |eta| * B1 + B2) := by
      have hchi := mul_le_mul_of_nonneg_left hinner (abs_nonneg p.χ)
      linarith

/-- The lower-order source is in `L2` once the population has `H1` and the
elliptic signal is supplied by the concrete weighted resolver. -/
theorem paper5WeightedLowerOrderSource_sq_integrable_of_resolver_data
    (p : CMParams) {M eta c t B1 B2 B3 B4 : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hM : 1 ≤ M) (heta : 0 < eta) (heta_one : eta < 1)
    (hu : IsCUnifBdd (u t)) (hU : IsCUnifBdd U)
    (huM : ∀ x, u t x ∈ Set.Icc (0 : ℝ) M)
    (hUM : ∀ x, U x ∈ Set.Icc (0 : ℝ) M)
    (hvM : ∀ x, v t x ∈ Set.Icc (0 : ℝ) (M ^ p.γ))
    (hvEq : v t = frozenElliptic p (u t))
    (hVEq : V = frozenElliptic p U)
    (hvDiff : Differentiable ℝ (v t)) (hVDiff : Differentiable ℝ V)
    (hb1 : ∀ x, |paper5B1 p u v t x| ≤ B1)
    (hb2 : ∀ x, |paper5B2 p u v U t x| ≤ B2)
    (hb3 : ∀ x, |paper5B3 p U x| ≤ B3)
    (hb4 : ∀ x, |paper5B4 p U x| ≤ B4)
    (hsource_meas : AEStronglyMeasurable
      (paper5WeightedLowerOrderSource p eta c u v U
        (paper5WeightedPopulation eta u U t)
        (paper5WeightedPopulationX eta u U t)
        (paper5WeightedSignal eta v V t)
        (paper5WeightedSignalX eta v V t) t))
    (hclose : Integrable (fun x =>
      Real.exp (2 * eta * x) * |u t x - U x| ^ 2))
    (hWx2 : Integrable (fun x =>
      paper5WeightedPopulationX eta u U t x ^ 2)) :
    Integrable (fun x =>
      paper5WeightedLowerOrderSource p eta c u v U
        (paper5WeightedPopulation eta u U t)
        (paper5WeightedPopulationX eta u U t)
        (paper5WeightedSignal eta v V t)
        (paper5WeightedSignalX eta v V t) t x ^ 2) := by
  have hW2 : Integrable (fun x =>
      paper5WeightedPopulation eta u U t x ^ 2) := by
    refine hclose.congr (Eventually.of_forall fun x => ?_)
    unfold paper5WeightedPopulation
    change Real.exp (2 * eta * x) * |u t x - U x| ^ 2 =
      (Real.exp (eta * x) * (u t x - U x)) ^ 2
    rw [mul_pow, show Real.exp (eta * x) ^ 2 =
        Real.exp (2 * eta * x) by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring,
      sq_abs]
  have hraw := weighted_frozenElliptic_difference_l2_data p hM heta heta_one
    hU hu hUM huM hclose
  dsimp only at hraw
  have hZ :
      (fun x => Real.exp (eta * x) *
        (frozenElliptic p (u t) x - frozenElliptic p U x)) =
        paper5WeightedSignal eta v V t := by
    funext x
    simp only [paper5WeightedSignal]
    rw [hvEq, hVEq]
  have hZderiv :
      deriv (paper5WeightedSignal eta v V t) =
        paper5WeightedSignalX eta v V t := by
    funext x
    exact (paper5WeightedSignal_space_hasDerivAt
      (hvDiff x) (hVDiff x)).deriv
  have hZ2 : Integrable (fun x =>
      paper5WeightedSignal eta v V t x ^ 2) := by
    refine hraw.1.congr (Eventually.of_forall fun x => ?_)
    change (Real.exp (eta * x) *
      (frozenElliptic p (u t) x - frozenElliptic p U x)) ^ 2 =
        paper5WeightedSignal eta v V t x ^ 2
    rw [congrFun hZ x]
  have hZx2 : Integrable (fun x =>
      paper5WeightedSignalX eta v V t x ^ 2) := by
    have hx := hraw.2.1
    rw [hZ, hZderiv] at hx
    exact hx
  have hJ2 : ∀ x,
      |paper5CorrectedJ2Coefficient p eta c u v U t x| ≤
        paper5CorrectedJ2AbsBound p eta c M B1 B2 := by
    intro x
    exact paper5CorrectedJ2Coefficient_abs_le p
      (le_trans zero_le_one hM) (huM x) (hUM x)
      (hvM x) (hb1 x) (hb2 x)
  exact (paper5WeightedLowerOrderSource_sq_integrable_and_integral_le p
    hsource_meas hJ2 hb1 hb3 hb4 hW2 hWx2 hZ2 hZx2).1

section AxiomAudit

#print axioms paper5CorrectedJ2AbsBound_nonneg
#print axioms paper5CorrectedJ2Coefficient_abs_le
#print axioms paper5WeightedLowerOrderSource_sq_integrable_of_resolver_data

end AxiomAudit

end ShenWork.Paper1
