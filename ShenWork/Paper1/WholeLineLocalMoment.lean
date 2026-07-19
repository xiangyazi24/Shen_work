import ShenWork.Paper1.WholeLineLocalizingWeightSecond

/-!
# Translation-uniform weighted local moments on the whole line

For a bounded population on `ℝ`, the unweighted integral of a power need not
be finite.  The paper therefore uses the translated smooth weight
`localizingWeightAt κ x₀` and takes a supremum over its centre `x₀`.

This file defines that moment and its uniform envelope, proves integrability
and an explicit bound for bounded continuous slices, and supplies the
second-derivative estimate for the translated weight needed by weighted
integration by parts.
-/

open Filter MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

/-- The translated weighted `L^P` moment used in Paper 1, §3.1. -/
def wholeLineLocalLpMoment
    (P κ : ℝ) (u : ℝ → ℝ → ℝ) (t x₀ : ℝ) : ℝ :=
  ∫ x : ℝ, (u t x) ^ P * localizingWeightAt κ x₀ x

/-- A translation-uniform weighted local `L^P` bound on the time interval
`[0,T)`. -/
def UniformlyLocalLpBounded
    (P κ : ℝ) (u : ℝ → ℝ → ℝ) (T K : ℝ) : Prop :=
  ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x₀ : ℝ,
    wholeLineLocalLpMoment P κ u t x₀ ≤ K

/-! ## Integrability of the weight and of bounded slices -/

theorem continuous_localizingWeight : Continuous (localizingWeight κ) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact (hasDerivAt_localizingWeight κ x).continuousAt

theorem continuous_localizingWeightAt :
    Continuous (localizingWeightAt κ x₀) := by
  unfold localizingWeightAt
  exact continuous_localizingWeight.comp (continuous_id.sub continuous_const)

/-- The translated smooth weight is integrable for every positive decay
parameter. -/
theorem localizingWeightAt_integrable
    {κ : ℝ} (hκ : 0 < κ) (x₀ : ℝ) :
    Integrable (localizingWeightAt κ x₀) := by
  have hdom : Integrable (fun x : ℝ => Real.exp (-κ * |x₀ - x|)) :=
    kernel_exp_neg_mul_abs_integrable hκ x₀
  refine Integrable.mono' hdom continuous_localizingWeightAt.aestronglyMeasurable ?_
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_pos (localizingWeightAt_pos κ x₀ x)]
    simpa only [abs_sub_comm] using localizingWeight_le_exp_abs hκ.le (x - x₀)

/-- The mass of every translated smooth weight is bounded by the mass of the
Laplace kernel, uniformly in the centre. -/
theorem integral_localizingWeightAt_le_two_div
    {κ : ℝ} (hκ : 0 < κ) (x₀ : ℝ) :
    (∫ x : ℝ, localizingWeightAt κ x₀ x) ≤ 2 / κ := by
  have hw := localizingWeightAt_integrable hκ x₀
  have hdom : Integrable (fun x : ℝ => Real.exp (-κ * |x₀ - x|)) :=
    kernel_exp_neg_mul_abs_integrable hκ x₀
  have hle : (∫ x : ℝ, localizingWeightAt κ x₀ x) ≤
      ∫ x : ℝ, Real.exp (-κ * |x₀ - x|) := by
    apply integral_mono hw hdom
    intro x
    simpa only [abs_sub_comm] using localizingWeight_le_exp_abs hκ.le (x - x₀)
  exact hle.trans_eq (integral_exp_neg_mul_abs_sub hκ x₀)

/-- A bounded continuous slice has a finite weighted local moment. -/
theorem wholeLineLocalLpIntegrable_of_bounded
    {P κ M t x₀ : ℝ} {u : ℝ → ℝ → ℝ}
    (hP : 0 ≤ P) (hκ : 0 < κ)
    (hu_cont : Continuous (u t))
    (hu_bound : ∀ x : ℝ, |u t x| ≤ M) :
    Integrable (fun x : ℝ =>
      (u t x) ^ P * localizingWeightAt κ x₀ x) := by
  have hpow_cont : Continuous (fun x : ℝ => (u t x) ^ P) :=
    (Real.continuous_rpow_const hP).comp hu_cont
  have htarget_meas : AEStronglyMeasurable (fun x : ℝ =>
      (u t x) ^ P * localizingWeightAt κ x₀ x) :=
    (hpow_cont.mul continuous_localizingWeightAt).aestronglyMeasurable
  have hmajor : Integrable (fun x : ℝ =>
      M ^ P * localizingWeightAt κ x₀ x) :=
    (localizingWeightAt_integrable hκ x₀).const_mul (M ^ P)
  refine Integrable.mono' hmajor htarget_meas (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_pos (localizingWeightAt_pos κ x₀ x)]
  have hpow : |(u t x) ^ P| ≤ M ^ P :=
    (Real.abs_rpow_le_abs_rpow (u t x) P).trans
      (Real.rpow_le_rpow (abs_nonneg (u t x)) (hu_bound x) hP)
  exact mul_le_mul_of_nonneg_right hpow (localizingWeightAt_pos κ x₀ x).le

/-- Convenient specialization to the repository's bounded-continuous
predicate. -/
theorem wholeLineLocalLpIntegrable_of_isCUnifBdd
    {P κ t x₀ : ℝ} {u : ℝ → ℝ → ℝ}
    (hP : 0 ≤ P) (hκ : 0 < κ) (hu : IsCUnifBdd (u t)) :
    Integrable (fun x : ℝ =>
      (u t x) ^ P * localizingWeightAt κ x₀ x) := by
  rcases hu.2 with ⟨M, hM⟩
  exact wholeLineLocalLpIntegrable_of_bounded hP hκ hu.1 hM

/-- For a nonnegative population the local moment is nonnegative. -/
theorem wholeLineLocalLpMoment_nonneg
    {P κ t x₀ : ℝ} {u : ℝ → ℝ → ℝ}
    (hu : ∀ x : ℝ, 0 ≤ u t x) :
    0 ≤ wholeLineLocalLpMoment P κ u t x₀ := by
  unfold wholeLineLocalLpMoment
  exact integral_nonneg fun x =>
    mul_nonneg (Real.rpow_nonneg (hu x) P)
      (localizingWeightAt_pos κ x₀ x).le

/-- Explicit domination of a nonnegative bounded slice by the weighted
constant profile. -/
theorem wholeLineLocalLpMoment_le_weighted_bound
    {P κ M t x₀ : ℝ} {u : ℝ → ℝ → ℝ}
    (hP : 0 ≤ P) (hκ : 0 < κ)
    (hu_cont : Continuous (u t))
    (hu_nonneg : ∀ x : ℝ, 0 ≤ u t x)
    (hu_bound : ∀ x : ℝ, u t x ≤ M) :
    wholeLineLocalLpMoment P κ u t x₀ ≤
      M ^ P * ∫ x : ℝ, localizingWeightAt κ x₀ x := by
  have htarget := wholeLineLocalLpIntegrable_of_bounded (x₀ := x₀)
    hP hκ hu_cont (fun x => by
      rw [abs_of_nonneg (hu_nonneg x)]
      exact hu_bound x)
  have hmajor : Integrable (fun x : ℝ =>
      M ^ P * localizingWeightAt κ x₀ x) :=
    (localizingWeightAt_integrable hκ x₀).const_mul (M ^ P)
  unfold wholeLineLocalLpMoment
  rw [← integral_const_mul]
  apply integral_mono htarget hmajor
  intro x
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (hu_nonneg x) (hu_bound x) hP)
    (localizingWeightAt_pos κ x₀ x).le

/-- In particular, the moment has the translation-independent bound
`M^P * (2/κ)`. -/
theorem wholeLineLocalLpMoment_le_two_mul_div
    {P κ M t x₀ : ℝ} {u : ℝ → ℝ → ℝ}
    (hP : 0 ≤ P) (hκ : 0 < κ) (hM : 0 ≤ M)
    (hu_cont : Continuous (u t))
    (hu_nonneg : ∀ x : ℝ, 0 ≤ u t x)
    (hu_bound : ∀ x : ℝ, u t x ≤ M) :
    wholeLineLocalLpMoment P κ u t x₀ ≤ M ^ P * (2 / κ) := by
  refine (wholeLineLocalLpMoment_le_weighted_bound
    hP hκ hu_cont hu_nonneg hu_bound).trans ?_
  exact mul_le_mul_of_nonneg_left
    (integral_localizingWeightAt_le_two_div hκ x₀)
    (Real.rpow_nonneg hM P)

/-! ## Second derivative of the translated weight -/

/-- The displayed value of the second derivative. -/
def localizingWeightSecondDerivValue (κ x : ℝ) : ℝ :=
  (-κ * (1 / (regDist x) ^ 3) +
    κ ^ 2 * (x / regDist x) ^ 2) * localizingWeight κ x

theorem deriv_localizingWeight (κ x : ℝ) :
    deriv (localizingWeight κ) x =
      -κ * (x / regDist x) * localizingWeight κ x :=
  (hasDerivAt_localizingWeight κ x).deriv

/-- The committed derivative formula is also the derivative of the actual
`deriv` function, which is the interface required by whole-line IBP. -/
theorem hasDerivAt_deriv_localizingWeight_actual (κ x : ℝ) :
    HasDerivAt (deriv (localizingWeight κ))
      (localizingWeightSecondDerivValue κ x) x := by
  have hfun : deriv (localizingWeight κ) =
      fun y : ℝ => -κ * (y / regDist y) * localizingWeight κ y := by
    funext y
    exact deriv_localizingWeight κ y
  rw [hfun]
  simpa [localizingWeightSecondDerivValue] using
    hasDerivAt_deriv_localizingWeight κ x

theorem iteratedDeriv_two_localizingWeight (κ x : ℝ) :
    iteratedDeriv 2 (localizingWeight κ) x =
      localizingWeightSecondDerivValue κ x := by
  rw [show iteratedDeriv 2 (localizingWeight κ) x =
      deriv (deriv (localizingWeight κ)) x by
        simp [iteratedDeriv_succ, iteratedDeriv_zero]]
  exact (hasDerivAt_deriv_localizingWeight_actual κ x).deriv

theorem abs_iteratedDeriv_two_localizingWeight_le
    {κ : ℝ} (hκ : 0 ≤ κ) (x : ℝ) :
    |iteratedDeriv 2 (localizingWeight κ) x| ≤
      (κ + κ ^ 2) * localizingWeight κ x := by
  rw [iteratedDeriv_two_localizingWeight]
  exact abs_second_deriv_localizingWeight_le hκ x

/-- First derivative of the translated weight. -/
theorem hasDerivAt_localizingWeightAt (κ x₀ x : ℝ) :
    HasDerivAt (localizingWeightAt κ x₀)
      (-κ * ((x - x₀) / regDist (x - x₀)) *
        localizingWeightAt κ x₀ x) x := by
  have hshift : HasDerivAt (fun y : ℝ => y - x₀) 1 x := by
    simpa using (hasDerivAt_id x).sub_const x₀
  simpa [localizingWeightAt, Function.comp_def] using
    (hasDerivAt_localizingWeight κ (x - x₀)).comp x hshift

theorem deriv_localizingWeightAt (κ x₀ x : ℝ) :
    deriv (localizingWeightAt κ x₀) x =
      -κ * ((x - x₀) / regDist (x - x₀)) *
        localizingWeightAt κ x₀ x :=
  (hasDerivAt_localizingWeightAt κ x₀ x).deriv

theorem abs_deriv_localizingWeightAt_le
    {κ : ℝ} (hκ : 0 ≤ κ) (x₀ x : ℝ) :
    |deriv (localizingWeightAt κ x₀) x| ≤
      κ * localizingWeightAt κ x₀ x := by
  rw [deriv_localizingWeightAt]
  exact abs_deriv_localizingWeight_le hκ (x - x₀)

/-- Second derivative of the translated weight. -/
theorem hasDerivAt_localizingWeightAtDerivative (κ x₀ x : ℝ) :
    HasDerivAt
      (fun y : ℝ =>
        -κ * ((y - x₀) / regDist (y - x₀)) *
          localizingWeightAt κ x₀ y)
      ((-κ * (1 / (regDist (x - x₀)) ^ 3) +
          κ ^ 2 * ((x - x₀) / regDist (x - x₀)) ^ 2) *
        localizingWeightAt κ x₀ x) x := by
  have hshift : HasDerivAt (fun y : ℝ => y - x₀) 1 x := by
    simpa using (hasDerivAt_id x).sub_const x₀
  simpa [localizingWeightAt, Function.comp_def] using
    (hasDerivAt_deriv_localizingWeight κ (x - x₀)).comp x hshift

theorem hasDerivAt_deriv_localizingWeightAt_actual (κ x₀ x : ℝ) :
    HasDerivAt (deriv (localizingWeightAt κ x₀))
      (localizingWeightSecondDerivValue κ (x - x₀)) x := by
  have hfun : deriv (localizingWeightAt κ x₀) = fun y : ℝ =>
      -κ * ((y - x₀) / regDist (y - x₀)) *
        localizingWeightAt κ x₀ y := by
    funext y
    exact deriv_localizingWeightAt κ x₀ y
  rw [hfun]
  simpa [localizingWeightSecondDerivValue, localizingWeightAt] using
    hasDerivAt_localizingWeightAtDerivative κ x₀ x

theorem iteratedDeriv_two_localizingWeightAt (κ x₀ x : ℝ) :
    iteratedDeriv 2 (localizingWeightAt κ x₀) x =
      localizingWeightSecondDerivValue κ (x - x₀) := by
  have hcomp : localizingWeightAt κ x₀ =
      fun y : ℝ => localizingWeight κ (y - x₀) := rfl
  rw [hcomp, iteratedDeriv_comp_sub_const]
  exact iteratedDeriv_two_localizingWeight κ (x - x₀)

theorem abs_iteratedDeriv_two_localizingWeightAt_le
    {κ : ℝ} (hκ : 0 ≤ κ) (x₀ x : ℝ) :
    |iteratedDeriv 2 (localizingWeightAt κ x₀) x| ≤
      (κ + κ ^ 2) * localizingWeightAt κ x₀ x := by
  rw [iteratedDeriv_two_localizingWeightAt]
  simpa [localizingWeightSecondDerivValue, localizingWeightAt] using
    abs_second_deriv_localizingWeight_le hκ (x - x₀)

/-- The translated weight obeys the same second-derivative bound, uniformly
in its centre. -/
theorem abs_second_deriv_localizingWeightAt_le
    {κ : ℝ} (hκ : 0 ≤ κ) (x₀ x : ℝ) :
    |((-κ * (1 / (regDist (x - x₀)) ^ 3) +
        κ ^ 2 * ((x - x₀) / regDist (x - x₀)) ^ 2) *
      localizingWeightAt κ x₀ x)| ≤
      (κ + κ ^ 2) * localizingWeightAt κ x₀ x := by
  simpa [localizingWeightAt] using
    abs_second_deriv_localizingWeight_le hκ (x - x₀)

section AxiomAudit

#print axioms localizingWeightAt_integrable
#print axioms wholeLineLocalLpIntegrable_of_bounded
#print axioms wholeLineLocalLpMoment_le_two_mul_div
#print axioms abs_deriv_localizingWeightAt_le
#print axioms hasDerivAt_deriv_localizingWeightAt_actual
#print axioms abs_iteratedDeriv_two_localizingWeightAt_le

end AxiomAudit

end ShenWork.Paper1
