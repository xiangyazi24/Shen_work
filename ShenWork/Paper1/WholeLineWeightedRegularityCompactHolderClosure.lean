import ShenWork.Paper1.WholeLineWeightedRegularityForcingPowerHolderWindow

open Filter MeasureTheory Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Closing local square-root moduli on a compact window

The analytic semigroup estimates naturally control sufficiently close time
pairs.  Uniform boundedness controls the remaining pairs on a compact
window.  This file packages that elementary final step with one fixed
constant selected before the pair of times.
-/

/-- A local ordered square-root modulus and a uniform norm bound produce one
square-root Hölder constant for every pair in the closed window. -/
theorem exists_uniform_sqrt_holder_of_local_and_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b rho C B : ℝ} {Z : ℝ → E}
    (hrho : 0 < rho) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hbound : ∀ q ∈ Set.Icc a b, ‖Z q‖ ≤ B)
    (hlocal : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
      s < t → t - s ≤ rho →
        ‖Z t - Z s‖ ≤ C * Real.sqrt (t - s)) :
    ∃ H : ℝ, 0 ≤ H ∧
      ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
        ‖Z s - Z t‖ ≤ H * Real.sqrt |s - t| := by
  have hsqrtRho : 0 < Real.sqrt rho := Real.sqrt_pos.2 hrho
  let D : ℝ := 2 * B / Real.sqrt rho
  let H : ℝ := C + D
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  have hH : 0 ≤ H := add_nonneg hC hD
  refine ⟨H, hH, ?_⟩
  intro s hs t ht
  rcases lt_trichotomy s t with hst | rfl | hts
  · have hdiff : |s - t| = t - s := by
      rw [abs_of_nonpos (sub_nonpos.mpr hst.le)]
      ring
    rw [hdiff]
    by_cases hnear : t - s ≤ rho
    · have hraw := hlocal s hs t ht hst hnear
      rw [norm_sub_rev] at hraw
      exact hraw.trans (mul_le_mul_of_nonneg_right
        (show C ≤ H by dsimp only [H]; linarith [hD])
        (Real.sqrt_nonneg _))
    · have hfar : rho ≤ t - s := le_of_not_ge hnear
      have hsqrt_le : Real.sqrt rho ≤ Real.sqrt (t - s) :=
        Real.sqrt_le_sqrt hfar
      calc
        ‖Z s - Z t‖ ≤ ‖Z s‖ + ‖Z t‖ := norm_sub_le _ _
        _ ≤ B + B := add_le_add (hbound s hs) (hbound t ht)
        _ = D * Real.sqrt rho := by
          dsimp only [D]
          rw [div_mul_cancel₀ _ hsqrtRho.ne']
          ring
        _ ≤ D * Real.sqrt (t - s) :=
          mul_le_mul_of_nonneg_left hsqrt_le hD
        _ ≤ H * Real.sqrt (t - s) :=
          mul_le_mul_of_nonneg_right
            (show D ≤ H by dsimp only [H]; linarith [hC])
            (Real.sqrt_nonneg _)
  · simp only [sub_self, norm_zero, abs_zero, Real.sqrt_zero, mul_zero]
    norm_num
  · have hdiff : |s - t| = s - t := abs_of_pos (sub_pos.mpr hts)
    rw [hdiff]
    by_cases hnear : s - t ≤ rho
    · have hraw := hlocal t ht s hs hts hnear
      exact hraw.trans (mul_le_mul_of_nonneg_right
        (show C ≤ H by dsimp only [H]; linarith [hD])
        (Real.sqrt_nonneg _))
    · have hfar : rho ≤ s - t := le_of_not_ge hnear
      have hsqrt_le : Real.sqrt rho ≤ Real.sqrt (s - t) :=
        Real.sqrt_le_sqrt hfar
      calc
        ‖Z s - Z t‖ ≤ ‖Z s‖ + ‖Z t‖ := norm_sub_le _ _
        _ ≤ B + B := add_le_add (hbound s hs) (hbound t ht)
        _ = D * Real.sqrt rho := by
          dsimp only [D]
          rw [div_mul_cancel₀ _ hsqrtRho.ne']
          ring
        _ ≤ D * Real.sqrt (s - t) :=
          mul_le_mul_of_nonneg_left hsqrt_le hD
        _ ≤ H * Real.sqrt (s - t) :=
          mul_le_mul_of_nonneg_right
            (show D ≤ H by dsimp only [H]; linarith [hC])
            (Real.sqrt_nonneg _)

/-- On a unit-diameter window, a square-root modulus also gives the weaker
positive power used by the nonlinear forcing coefficients. -/
theorem uniform_forcingExponent_holder_of_sqrt_holder
    (p : CMParams) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b H : ℝ} {Z : ℝ → E}
    (hdiam : b - a ≤ 1) (hH : 0 ≤ H)
    (hsqrt : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
      ‖Z s - Z t‖ ≤ H * Real.sqrt |s - t|) :
    ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
      ‖Z s - Z t‖ ≤ H * |s - t| ^ paper5ForcingTimeExponent p := by
  intro s hs t ht
  have hd0 : 0 ≤ |s - t| := abs_nonneg _
  have hd1 : |s - t| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  calc
    ‖Z s - Z t‖ ≤ H * Real.sqrt |s - t| := hsqrt s hs t ht
    _ = H * |s - t| ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
    _ ≤ H * |s - t| ^ paper5ForcingTimeExponent p :=
      mul_le_mul_of_nonneg_left
        (rpow_half_le_rpow_forcingTimeExponent p hd0 hd1) hH

end ShenWork.Paper1

#print axioms
  ShenWork.Paper1.exists_uniform_sqrt_holder_of_local_and_bound
#print axioms
  ShenWork.Paper1.uniform_forcingExponent_holder_of_sqrt_holder
