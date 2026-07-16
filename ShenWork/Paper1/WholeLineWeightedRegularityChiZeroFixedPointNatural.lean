import ShenWork.Paper1.WaveStabilityUpgrade
import ShenWork.Paper1.Theorem12CoordinateAudit

open Filter MeasureTheory Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Fixed-coordinate convergence from the co-moving weighted energy

The exponential weight degenerates at the moving left end, so weighted
`L^2` convergence cannot by itself give a uniform left-tail statement.  At
any fixed co-moving coordinate, however, the weight is uniformly positive on
a fixed neighborhood.  The eventual spatial modulus then converts a
pointwise discrepancy into a positive amount of weighted energy.

This is the boundary-value input for a later scalar KPP comparison on a left
half-line.  It contains no assertion about the far-left tail itself.
-/

private lemma interval_constant_integral_fixed
    {a b C : ℝ} (hab : a ≤ b) :
    ∫ _x : ℝ in Set.Icc a b, C = C * (b - a) := by
  simp [hab, mul_comm]

/-- Co-moving weighted `L^2` convergence plus the canonical eventual spatial
modulus implies uniform-in-late-time convergence at each fixed moving
coordinate. -/
theorem eventually_coMovingPath_close_at_fixed_of_weightedL2_of_spatialModulus
    {eta c : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (heta : 0 < eta)
    (hweighted : CoMovingWeightedL2Convergence eta c u U)
    (hmod : EventuallyUniformMovingFrameSpatialModulus 0
      (coMovingPath c u) U)
    (z : ℝ) :
    ∀ epsilon > 0, ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      |coMovingPath c u t z - U z| < epsilon := by
  intro epsilon hepsilon
  obtain ⟨delta, hdelta, Tmod, hmod_event⟩ :=
    hmod (epsilon / 2) (by positivity)
  let r : ℝ := delta / 2
  let C : ℝ := Real.exp (2 * eta * (z - r)) * (epsilon / 2) ^ 2
  let K : ℝ := C * (2 * r)
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hrdelta : r < delta := by
    dsimp [r]
    linarith
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hsmall : ∀ᶠ t in atTop,
      coMovingWeightedL2Energy eta c u U t < K :=
    hweighted.2 (Iio_mem_nhds hK)
  obtain ⟨Tenergy, henergy⟩ :=
    eventually_atTop.1 (hweighted.1.and hsmall)
  refine ⟨max Tmod Tenergy, ?_⟩
  intro t ht
  have htmod : Tmod ≤ t := (le_max_left _ _).trans ht
  have htenergy : Tenergy ≤ t := (le_max_right _ _).trans ht
  obtain ⟨hint, hsmall_t⟩ := henergy t htenergy
  by_contra hnot
  have hze : epsilon ≤ |coMovingPath c u t z - U z| :=
    le_of_not_gt hnot
  have hpointwise : ∀ y ∈ Set.Icc (z - r) (z + r),
      C ≤ Real.exp (2 * eta * y) *
        |coMovingPath c u t y - U y| ^ 2 := by
    intro y hy
    have hzy : |z - y| ≤ r := by
      rw [abs_le]
      constructor <;> linarith [hy.1, hy.2]
    have hnear := hmod_event t z y htmod (hzy.trans_lt hrdelta)
    have hnear' :
        |(coMovingPath c u t z - U z) -
            (coMovingPath c u t y - U y)| < epsilon / 2 := by
      simpa [movingFrameError] using hnear
    have htriangle :
        |coMovingPath c u t z - U z| ≤
          |(coMovingPath c u t z - U z) -
              (coMovingPath c u t y - U y)| +
            |coMovingPath c u t y - U y| := by
      calc
        |coMovingPath c u t z - U z| =
            |((coMovingPath c u t z - U z) -
                (coMovingPath c u t y - U y)) +
              (coMovingPath c u t y - U y)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    have hey : epsilon / 2 < |coMovingPath c u t y - U y| := by
      linarith
    have hybase : z - r ≤ y := hy.1
    have hweight :
        Real.exp (2 * eta * (z - r)) ≤ Real.exp (2 * eta * y) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left hybase (by positivity)
    have hsquare :
        (epsilon / 2) ^ 2 ≤ |coMovingPath c u t y - U y| ^ 2 := by
      nlinarith [abs_nonneg (coMovingPath c u t y - U y)]
    dsimp [C]
    exact mul_le_mul hweight hsquare (sq_nonneg _) (Real.exp_pos _).le
  have hconst_int :
      IntegrableOn (fun _y : ℝ => C) (Set.Icc (z - r) (z + r)) := by
    exact integrableOn_const (by simp [Real.volume_Icc])
  have hrestricted_int : IntegrableOn
      (fun y : ℝ => Real.exp (2 * eta * y) *
        |coMovingPath c u t y - U y| ^ 2)
      (Set.Icc (z - r) (z + r)) := hint.integrableOn
  have hlower_restricted :
      (∫ _y : ℝ in Set.Icc (z - r) (z + r), C) ≤
        ∫ y : ℝ in Set.Icc (z - r) (z + r),
          Real.exp (2 * eta * y) *
            |coMovingPath c u t y - U y| ^ 2 :=
    MeasureTheory.setIntegral_mono_on hconst_int hrestricted_int
      measurableSet_Icc hpointwise
  have hrestricted_global :
      (∫ y : ℝ in Set.Icc (z - r) (z + r),
          Real.exp (2 * eta * y) *
            |coMovingPath c u t y - U y| ^ 2) ≤
        coMovingWeightedL2Energy eta c u U t := by
    exact MeasureTheory.setIntegral_le_integral hint
      (Eventually.of_forall fun y =>
        mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
  have hinterval :
      (∫ _y : ℝ in Set.Icc (z - r) (z + r), C) = K := by
    rw [interval_constant_integral_fixed]
    · dsimp [K]
      ring
    · linarith
  rw [hinterval] at hlower_restricted
  exact (not_lt_of_ge (hlower_restricted.trans hrestricted_global)) hsmall_t

section AxiomAudit

#print axioms
  eventually_coMovingPath_close_at_fixed_of_weightedL2_of_spatialModulus

end AxiomAudit

end ShenWork.Paper1
