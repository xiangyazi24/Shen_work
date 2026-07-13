import ShenWork.Paper1.Lemma53Full

open Filter Topology MeasureTheory

noncomputable section

namespace ShenWork.Paper1

/-!
# From weighted `L²` decay to uniform moving-frame decay

The exponential weight used in Paper 1 loses control at the left end of the
line.  Consequently weighted `L²` convergence alone cannot imply uniform
convergence.  The two additional inputs below isolate exactly the Step 4
information used in Section 5: an eventual spatial modulus (from parabolic
smoothing/Morrey) and uniform convergence in the far-left moving frame (from
persistence and the left equilibrium).
-/

/-- The perturbation in the moving frame. -/
def movingFrameError (c : ℝ) (u : ℝ → ℝ → ℝ) (U : ℝ → ℝ)
    (t x : ℝ) : ℝ :=
  u t x - U (x - c * t)

/-- Eventually, the moving-frame perturbation has a spatial modulus that is
uniform in time.  This is the precise Morrey/equicontinuity input in Step 4. -/
def EventuallyUniformMovingFrameSpatialModulus
    (c : ℝ) (u : ℝ → ℝ → ℝ) (U : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∃ T : ℝ, ∀ t x y : ℝ,
    T ≤ t → |x - y| < δ →
      |movingFrameError c u U t x - movingFrameError c u U t y| < ε

/-- Uniform convergence of the perturbation at the far-left end of the
moving frame.  It supplies the localization that the right-growing
exponential weight cannot provide. -/
def UniformMovingFrameLeftTailConvergence
    (c : ℝ) (u : ℝ → ℝ → ℝ) (U : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ R T : ℝ, ∀ t x : ℝ,
    T ≤ t → x - c * t ≤ -R → |movingFrameError c u U t x| < ε

/-- Eventual integrability of the weighted perturbation energy.  This is
stated separately because the Bochner integral in Lean is zero for a
non-integrable integrand; a stability proof must rule out that vacuity. -/
def EventuallyIntegrableMovingFrameEnergy
    (η c : ℝ) (u : ℝ → ℝ → ℝ) (U : ℝ → ℝ) : Prop :=
  ∀ᶠ t in atTop,
    Integrable (fun x : ℝ =>
      Real.exp (2 * η * x) * |movingFrameError c u U t x| ^ 2)

theorem eventuallyUniformMovingFrameSpatialModulus_self
    (c : ℝ) (U : ℝ → ℝ) :
    EventuallyUniformMovingFrameSpatialModulus c
      (fun t x => U (x - c * t)) U := by
  intro ε hε
  refine ⟨1, zero_lt_one, 0, ?_⟩
  intro t x y _ht _hxy
  simpa [movingFrameError] using hε

theorem uniformMovingFrameLeftTailConvergence_self
    (c : ℝ) (U : ℝ → ℝ) :
    UniformMovingFrameLeftTailConvergence c
      (fun t x => U (x - c * t)) U := by
  intro ε hε
  refine ⟨0, 0, ?_⟩
  intro t x _ht _hx
  simpa [movingFrameError] using hε

theorem eventuallyIntegrableMovingFrameEnergy_self
    (η c : ℝ) (U : ℝ → ℝ) :
    EventuallyIntegrableMovingFrameEnergy η c
      (fun t x => U (x - c * t)) U := by
  exact Eventually.of_forall fun _t => by
    simp [movingFrameError]

private lemma interval_constant_integral
    {a b C : ℝ} (hab : a ≤ b) :
    ∫ _x : ℝ in Set.Icc a b, C = C * (b - a) := by
  simp [hab, mul_comm]

/-- Weighted `L²` convergence upgrades to uniform moving-frame convergence
once the two genuine Step 4 inputs are available.  The proof is quantitative:
any pointwise error at least `ε` creates, through the spatial modulus, a fixed
positive amount of weighted energy on a short interval.  The left-tail input
keeps that interval away from the degenerating end of the exponential
weight, contradicting weighted-energy decay. -/
theorem uniformMovingFrameConvergence_of_weightedL2_of_spatialModulus_of_leftTail
    {η c : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hη : 0 < η) (hc : 0 < c)
    (henergy_int : EventuallyIntegrableMovingFrameEnergy η c u U)
    (hweighted : WeightedL2MovingFrameConvergence η c u U)
    (hmod : EventuallyUniformMovingFrameSpatialModulus c u U)
    (hleft : UniformMovingFrameLeftTailConvergence c u U) :
    UniformMovingFrameConvergence c u U := by
  intro ε hε
  obtain ⟨δ, hδ, Tmod, hmod_event⟩ := hmod (ε / 2) (by positivity)
  obtain ⟨R, Tleft, hleft_event⟩ := hleft ε hε
  let r : ℝ := δ / 2
  let C : ℝ := Real.exp (2 * η * (-R - r)) * (ε / 2) ^ 2
  let K : ℝ := C * (2 * r)
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hrδ : r < δ := by
    dsimp [r]
    linarith
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hweighted' :
      Tendsto
        (fun t : ℝ => ∫ x : ℝ,
          Real.exp (2 * η * x) * |movingFrameError c u U t x| ^ 2)
        atTop (𝓝 0) := by
    simpa [WeightedL2MovingFrameConvergence, movingFrameError] using hweighted
  have hsmall : ∀ᶠ t in atTop,
      (∫ x : ℝ,
        Real.exp (2 * η * x) * |movingFrameError c u U t x| ^ 2) < K :=
    hweighted' (Iio_mem_nhds hK)
  obtain ⟨Tenergy, henergy⟩ :=
    (eventually_atTop.1 (henergy_int.and hsmall))
  refine ⟨max 0 (max Tmod (max Tleft Tenergy)), ?_⟩
  intro t x ht
  have ht0 : 0 ≤ t := le_trans (le_max_left _ _) ht
  have htmod : Tmod ≤ t :=
    le_trans (le_max_left Tmod (max Tleft Tenergy))
      (le_trans (le_max_right 0 _) ht)
  have htleft : Tleft ≤ t :=
    le_trans (le_trans (le_max_left Tleft Tenergy)
      (le_max_right Tmod _)) (le_trans (le_max_right 0 _) ht)
  have htenergy : Tenergy ≤ t :=
    le_trans (le_trans (le_max_right Tleft Tenergy)
      (le_max_right Tmod _)) (le_trans (le_max_right 0 _) ht)
  obtain ⟨hint, hsmall_t⟩ := henergy t htenergy
  by_contra hnot
  have hxe : ε ≤ |movingFrameError c u U t x| := le_of_not_gt hnot
  have hxframe : -R < x - c * t := by
    by_contra hnotframe
    have htail := hleft_event t x htleft (le_of_not_gt hnotframe)
    linarith
  have hct : 0 ≤ c * t := mul_nonneg hc.le ht0
  have hxbase : -R < x := by linarith
  have hpointwise : ∀ y ∈ Set.Icc (x - r) (x + r),
      C ≤ Real.exp (2 * η * y) * |movingFrameError c u U t y| ^ 2 := by
    intro y hy
    have hxy : |x - y| ≤ r := by
      rw [abs_le]
      constructor <;> linarith [hy.1, hy.2]
    have hnear := hmod_event t x y htmod (hxy.trans_lt hrδ)
    have htriangle :
        |movingFrameError c u U t x| ≤
          |movingFrameError c u U t x - movingFrameError c u U t y| +
            |movingFrameError c u U t y| := by
      calc
        |movingFrameError c u U t x| =
            |(movingFrameError c u U t x - movingFrameError c u U t y) +
              movingFrameError c u U t y| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    have hey : ε / 2 < |movingFrameError c u U t y| := by
      linarith
    have hybase : -R - r ≤ y := by
      linarith [hy.1]
    have hweight :
        Real.exp (2 * η * (-R - r)) ≤ Real.exp (2 * η * y) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left hybase (by positivity)
    have hsquare :
        (ε / 2) ^ 2 ≤ |movingFrameError c u U t y| ^ 2 := by
      nlinarith [abs_nonneg (movingFrameError c u U t y)]
    dsimp [C]
    exact mul_le_mul hweight hsquare (sq_nonneg _) (Real.exp_pos _).le
  have hconst_int : IntegrableOn (fun _y : ℝ => C) (Set.Icc (x - r) (x + r)) := by
    exact integrableOn_const (by simp [Real.volume_Icc])
  have hrestricted_int :
      IntegrableOn
        (fun y : ℝ =>
          Real.exp (2 * η * y) * |movingFrameError c u U t y| ^ 2)
        (Set.Icc (x - r) (x + r)) :=
    hint.integrableOn
  have hlower_restricted :
      (∫ _y : ℝ in Set.Icc (x - r) (x + r), C) ≤
        ∫ y : ℝ in Set.Icc (x - r) (x + r),
          Real.exp (2 * η * y) * |movingFrameError c u U t y| ^ 2 :=
    MeasureTheory.setIntegral_mono_on hconst_int hrestricted_int
      measurableSet_Icc hpointwise
  have hrestricted_global :
      (∫ y : ℝ in Set.Icc (x - r) (x + r),
          Real.exp (2 * η * y) * |movingFrameError c u U t y| ^ 2) ≤
        ∫ y : ℝ,
          Real.exp (2 * η * y) * |movingFrameError c u U t y| ^ 2 := by
    exact MeasureTheory.setIntegral_le_integral hint
      (Eventually.of_forall fun y =>
        mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
  have hinterval :
      (∫ _y : ℝ in Set.Icc (x - r) (x + r), C) = K := by
    rw [interval_constant_integral]
    · dsimp [K]
      ring
    · linarith
  rw [hinterval] at hlower_restricted
  exact (not_lt_of_ge (hlower_restricted.trans hrestricted_global)) hsmall_t

#print axioms uniformMovingFrameConvergence_of_weightedL2_of_spatialModulus_of_leftTail

end ShenWork.Paper1
