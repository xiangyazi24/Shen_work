import ShenWork.Paper2.IntervalConjugatePicard

open Filter Topology
open ShenWork.IntervalDomain (intervalDomainPoint)
open ShenWork.IntervalConjugateDuhamelMap
open ShenWork.IntervalMildPicard

noncomputable section

namespace ShenWork.IntervalConjugatePicard

/-- The B-form Picard fixed point is unique inside the ball/cone governed by
the contraction data in `ConjugateMildExistenceData`. -/
theorem intervalConjugateMildSolution_unique_of_data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀)
    {u : ℝ → intervalDomainPoint → ℝ}
    (hmild : IntervalConjugateMildSolution p D.T u₀ u)
    (hbound :
      ∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
        |u t x| ≤ D.M)
    (hnonneg :
      ∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
        0 ≤ u t x)
    (hcont : HasContinuousSlices D.T u)
    (hmeas : HasJointMeasurability u) :
    ∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
      u t x = conjugatePicardLimit p u₀ D.T t x := by
  let v : ℝ → intervalDomainPoint → ℝ := conjugatePicardLimit p u₀ D.T
  have hv_mild : IntervalConjugateMildSolution p D.T u₀ v := by
    simpa [v] using (conjugateMildSolutionData_of_data D).hmild
  have hv_bound :
      ∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
        |v t x| ≤ D.M := by
    intro t ht htT x
    simpa [v] using (conjugateMildSolutionData_of_data D).hbound t ht htT x
  have hv_nonneg :
      ∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
        0 ≤ v t x := by
    intro t ht htT x
    simpa [v] using (conjugateMildSolutionData_of_data D).hnonneg t ht htT x
  have hv_cont : HasContinuousSlices D.T v := by
    simpa [v] using (conjugateMildSolutionData_of_data D).hcont
  have hv_meas : HasJointMeasurability v := by
    simpa [v] using (conjugateMildSolutionData_of_data D).hmeas
  have hdiff :
      ∀ n : ℕ, ∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
        |u t x - v t x| ≤ D.K ^ n * (2 * D.M) := by
    intro n
    induction n with
    | zero =>
        intro t ht htT x
        have htri :
            |u t x - v t x| ≤ |u t x| + |v t x| := by
          simpa [sub_eq_add_neg, abs_neg] using
            (abs_add_le (u t x) (-(v t x)))
        calc
          |u t x - v t x| ≤ |u t x| + |v t x| := htri
          _ ≤ D.M + D.M := add_le_add (hbound t ht htT x) (hv_bound t ht htT x)
          _ = D.K ^ (0 : ℕ) * (2 * D.M) := by ring
    | succ n ih =>
        intro t ht htT x
        have hu_eq := hmild t ht htT x
        have hv_eq := hv_mild t ht htT x
        calc
          |u t x - v t x|
              =
            |intervalConjugateDuhamelMap p u₀ u t x
              - intervalConjugateDuhamelMap p u₀ v t x| := by
                rw [hu_eq, hv_eq]
          _ ≤ D.K * (D.K ^ n * (2 * D.M)) :=
            D.hcontr u v (D.K ^ n * (2 * D.M))
              hbound hnonneg hv_bound hv_nonneg
              hcont hv_cont hmeas hv_meas ih t ht htT x
          _ = D.K ^ (n + 1) * (2 * D.M) := by ring
  intro t ht htT x
  set a : ℝ := |u t x - v t x|
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact abs_nonneg _
  have htend :
      Tendsto (fun n : ℕ => D.K ^ n * (2 * D.M)) atTop (nhds 0) := by
    have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one D.hK_nn D.hK
    simpa [zero_mul] using hpow.mul_const (2 * D.M)
  have ha_le_zero : a ≤ 0 :=
    ge_of_tendsto htend
      (Eventually.of_forall fun n => by
        change |u t x - v t x| ≤ D.K ^ n * (2 * D.M)
        exact hdiff n t ht htT x)
  have ha_zero : a = 0 := le_antisymm ha_le_zero ha_nonneg
  have hsub : u t x - v t x = 0 := abs_eq_zero.mp ha_zero
  have heq : u t x = v t x := sub_eq_zero.mp hsub
  simpa [v] using heq

end ShenWork.IntervalConjugatePicard
