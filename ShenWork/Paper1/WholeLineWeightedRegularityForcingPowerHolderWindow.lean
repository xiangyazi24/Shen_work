import ShenWork.Paper1.WholeLineWeightedRegularityForcingPowerHolderNatural

open Filter MeasureTheory Real Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# One Holder constant for a whole positive-time window

The pairwise forcing estimate is not enough for the Henry generator theorem:
that theorem needs one constant which controls every pair of times in a fixed
window.  Here all coefficient, profile, and energy moduli are quantified
before the time pair is introduced, so the final square-root constant is
chosen once and for all.
-/

/-- Canonical coefficient for the time modulus of `u^(m-1)`.  Unlike an
existential pairwise witness, this value depends only on the fixed window
bounds. -/
def paper5RpowSensitivityWindowConst
    (p : CMParams) (M Hu : ℝ) : ℝ :=
  if p.m = 1 then 0
  else if p.m < 2 then Hu ^ (p.m - 1)
  else (p.m - 1) * M ^ (p.m - 2) * Hu

theorem paper5RpowSensitivityWindowConst_nonneg
    (p : CMParams) {M Hu : ℝ} (hM : 0 ≤ M) (hHu : 0 ≤ Hu) :
    0 ≤ paper5RpowSensitivityWindowConst p M Hu := by
  unfold paper5RpowSensitivityWindowConst
  split_ifs with hm hm2
  · exact le_rfl
  · exact Real.rpow_nonneg hHu _
  · exact mul_nonneg
      (mul_nonneg (by linarith [p.hm]) (Real.rpow_nonneg hM _)) hHu

/-- Fixed-constant form of the power-sensitivity estimate. -/
theorem rpow_sensitivity_time_modulus_le_windowConst
    (p : CMParams) {M Hu d s t : ℝ} {u : ℝ → ℝ → ℝ}
    (hM : 0 ≤ M) (hHu : 0 ≤ Hu) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (huM : ∀ q x, u q x ∈ Set.Icc (0 : ℝ) M)
    (huHolder : ∀ x,
      |u s x - u t x| ≤ Hu * d ^ (1 / 2 : ℝ)) :
    ∀ x,
      |(u s x) ^ (p.m - 1) - (u t x) ^ (p.m - 1)| ≤
        paper5RpowSensitivityWindowConst p M Hu *
          d ^ paper5ForcingTimeExponent p := by
  by_cases hm : p.m = 1
  · intro x
    simp [paper5RpowSensitivityWindowConst, paper5ForcingTimeExponent, hm]
  · have hm1 : 1 < p.m := lt_of_le_of_ne p.hm (Ne.symm hm)
    by_cases hm2 : p.m < 2
    · intro x
      have hp := abs_nonneg_rpow_sub_rpow_le_abs_sub_rpow
        (a := u s x) (b := u t x) (q := p.m - 1)
          (huM s x).1 (huM t x).1 (by linarith) (by linarith)
      have hbase := Real.rpow_le_rpow (abs_nonneg _)
        (huHolder x) (by linarith : 0 ≤ p.m - 1)
      calc
        |(u s x) ^ (p.m - 1) - (u t x) ^ (p.m - 1)| ≤
            |u s x - u t x| ^ (p.m - 1) := hp
        _ ≤ (Hu * d ^ (1 / 2 : ℝ)) ^ (p.m - 1) := hbase
        _ = Hu ^ (p.m - 1) * d ^ ((p.m - 1) / 2) := by
          rw [Real.mul_rpow hHu (Real.rpow_nonneg hd0 _),
            ← Real.rpow_mul hd0]
          congr 1
          ring
        _ = paper5RpowSensitivityWindowConst p M Hu *
            d ^ paper5ForcingTimeExponent p := by
          simp only [paper5RpowSensitivityWindowConst,
            paper5ForcingTimeExponent, hm, hm2, if_false, if_true]
          rw [min_eq_right (by linarith : p.m - 1 ≤ 1)]
    · have hm2' : 2 ≤ p.m := le_of_not_gt hm2
      intro x
      have hp := abs_rpow_sub_rpow_le_of_mem_Icc
        (gamma := p.m - 1) (M := M) (by linarith) hM
          (huM s x) (huM t x)
      have hhalf := rpow_half_le_rpow_forcingTimeExponent p hd0 hd1
      calc
        |(u s x) ^ (p.m - 1) - (u t x) ^ (p.m - 1)| ≤
            (p.m - 1) * M ^ (p.m - 2) * |u s x - u t x| := by
          convert hp using 1 <;> ring
        _ ≤ (p.m - 1) * M ^ (p.m - 2) *
            (Hu * d ^ (1 / 2 : ℝ)) := by
          exact mul_le_mul_of_nonneg_left (huHolder x)
            (mul_nonneg (by linarith) (Real.rpow_nonneg hM _))
        _ ≤ paper5RpowSensitivityWindowConst p M Hu *
            d ^ paper5ForcingTimeExponent p := by
          simp only [paper5RpowSensitivityWindowConst, hm, hm2,
            if_false]
          have hcoef : 0 ≤ (p.m - 1) * M ^ (p.m - 2) * Hu := by
            exact mul_nonneg
              (mul_nonneg (by linarith) (Real.rpow_nonneg hM _)) hHu
          calc
            (p.m - 1) * M ^ (p.m - 2) *
                (Hu * d ^ (1 / 2 : ℝ)) =
              ((p.m - 1) * M ^ (p.m - 2) * Hu) *
                d ^ (1 / 2 : ℝ) := by ring
            _ ≤ ((p.m - 1) * M ^ (p.m - 2) * Hu) *
                d ^ paper5ForcingTimeExponent p :=
              mul_le_mul_of_nonneg_left hhalf hcoef

/-- Canonical coefficient for the time modulus of `paper5A p.m`. -/
def paper5ASensitivityWindowConst
    (p : CMParams) (M Hu : ℝ) : ℝ :=
  if p.m = 1 then 0
  else if p.m < 2 then p.m * Hu ^ (p.m - 1)
  else p.m * (p.m - 1) * M ^ (p.m - 2) * Hu

theorem paper5ASensitivityWindowConst_nonneg
    (p : CMParams) {M Hu : ℝ} (hM : 0 ≤ M) (hHu : 0 ≤ Hu) :
    0 ≤ paper5ASensitivityWindowConst p M Hu := by
  unfold paper5ASensitivityWindowConst
  split_ifs with hm hm2
  · exact le_rfl
  · exact mul_nonneg (by linarith [p.hm]) (Real.rpow_nonneg hHu _)
  · exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by linarith [p.hm]) (by linarith [p.hm]))
        (Real.rpow_nonneg hM _)) hHu

/-- Fixed-constant form of the `paper5A p.m` sensitivity estimate. -/
theorem paper5A_sensitivity_time_modulus_le_windowConst
    (p : CMParams) {M Hu d s t : ℝ}
    {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hM : 0 ≤ M) (hHu : 0 ≤ Hu) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (huM : ∀ q x, u q x ∈ Set.Icc (0 : ℝ) M)
    (hUM : ∀ x, U x ∈ Set.Icc (0 : ℝ) M)
    (huHolder : ∀ x,
      |u s x - u t x| ≤ Hu * d ^ (1 / 2 : ℝ)) :
    ∀ x,
      |paper5A p.m u U s x - paper5A p.m u U t x| ≤
        paper5ASensitivityWindowConst p M Hu *
          d ^ paper5ForcingTimeExponent p := by
  by_cases hm : p.m = 1
  · intro x
    simp [paper5ASensitivityWindowConst, paper5A, hm,
      paper5MeanCoefficient_one]
  · have hm1 : 1 < p.m := lt_of_le_of_ne p.hm (Ne.symm hm)
    by_cases hm2 : p.m < 2
    · intro x
      have hsec :=
        paper5MeanCoefficient_sub_abs_le_rpow_of_one_lt_of_lt_two
          hm1 hm2 hM (huM s x) (huM t x) (hUM x)
      have hbase := Real.rpow_le_rpow (abs_nonneg _)
        (huHolder x) (by linarith : 0 ≤ p.m - 1)
      change |paper5MeanCoefficient p.m (u s x) (U x) -
          paper5MeanCoefficient p.m (u t x) (U x)| ≤ _
      calc
        |paper5MeanCoefficient p.m (u s x) (U x) -
            paper5MeanCoefficient p.m (u t x) (U x)| ≤
            p.m * |u s x - u t x| ^ (p.m - 1) := hsec
        _ ≤ p.m * (Hu * d ^ (1 / 2 : ℝ)) ^ (p.m - 1) :=
          mul_le_mul_of_nonneg_left hbase (by linarith [p.hm])
        _ = p.m * (Hu ^ (p.m - 1) * d ^ ((p.m - 1) / 2)) := by
          rw [Real.mul_rpow hHu (Real.rpow_nonneg hd0 _),
            ← Real.rpow_mul hd0]
          congr 2
          ring
        _ = paper5ASensitivityWindowConst p M Hu *
            d ^ paper5ForcingTimeExponent p := by
          simp only [paper5ASensitivityWindowConst,
            paper5ForcingTimeExponent, hm, hm2, if_false, if_true]
          rw [min_eq_right (by linarith : p.m - 1 ≤ 1)]
          ring
    · have hm2' : 2 ≤ p.m := le_of_not_gt hm2
      intro x
      have hsec := paper5_four_profile_secant_difference_bound_of_two_le
        (m := p.m) (M := M) (a2 := u s x) (b2 := u t x)
          (a1 := U x) (b1 := U x) hm2' hM
          (huM s x) (huM t x) (hUM x) (hUM x)
      have hhalf := rpow_half_le_rpow_forcingTimeExponent p hd0 hd1
      change |paper5MeanCoefficient p.m (u s x) (U x) -
          paper5MeanCoefficient p.m (u t x) (U x)| ≤ _
      calc
        |paper5MeanCoefficient p.m (u s x) (U x) -
            paper5MeanCoefficient p.m (u t x) (U x)| ≤
            p.m * (p.m - 1) * M ^ (p.m - 2) *
              |u s x - u t x| := by simpa using hsec
        _ ≤ p.m * (p.m - 1) * M ^ (p.m - 2) *
            (Hu * d ^ (1 / 2 : ℝ)) := by
          exact mul_le_mul_of_nonneg_left (huHolder x)
            (mul_nonneg
              (mul_nonneg (by linarith [p.hm]) (by linarith))
              (Real.rpow_nonneg hM _))
        _ ≤ paper5ASensitivityWindowConst p M Hu *
            d ^ paper5ForcingTimeExponent p := by
          simp only [paper5ASensitivityWindowConst, hm, hm2, if_false]
          have hcoef :
              0 ≤ p.m * (p.m - 1) * M ^ (p.m - 2) * Hu := by
            exact mul_nonneg
              (mul_nonneg
                (mul_nonneg (by linarith [p.hm]) (by linarith))
                (Real.rpow_nonneg hM _)) hHu
          calc
            p.m * (p.m - 1) * M ^ (p.m - 2) *
                (Hu * d ^ (1 / 2 : ℝ)) =
              (p.m * (p.m - 1) * M ^ (p.m - 2) * Hu) *
                d ^ (1 / 2 : ℝ) := by ring
            _ ≤ (p.m * (p.m - 1) * M ^ (p.m - 2) * Hu) *
                d ^ paper5ForcingTimeExponent p :=
              mul_le_mul_of_nonneg_left hhalf hcoef

/-- Canonical window coefficient for the `b₁` time modulus. -/
def paper5B1TimeWindowConst
    (p : CMParams) (M Hu : ℝ) : ℝ :=
  p.m *
    (rpowLip p.γ M * Hu * M ^ (p.m - 1) +
      M ^ p.γ * paper5RpowSensitivityWindowConst p M Hu)

theorem paper5B1TimeWindowConst_nonneg
    (p : CMParams) {M Hu : ℝ} (hM : 0 ≤ M) (hHu : 0 ≤ Hu) :
    0 ≤ paper5B1TimeWindowConst p M Hu := by
  unfold paper5B1TimeWindowConst
  exact mul_nonneg (by linarith [p.hm])
    (add_nonneg
      (mul_nonneg
        (mul_nonneg (rpowLip_nonneg p.hγ hM) hHu)
        (Real.rpow_nonneg hM _))
      (mul_nonneg (Real.rpow_nonneg hM _)
        (paper5RpowSensitivityWindowConst_nonneg p hM hHu)))

/-- Fixed-constant `b₁` modulus for one pair of times. -/
theorem paper5B1_time_modulus_le_windowConst
    (p : CMParams) {M Hu d s t : ℝ}
    {u v : ℝ → ℝ → ℝ}
    (hM : 0 ≤ M) (hHu : 0 ≤ Hu) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (huC : ∀ q, IsCUnifBdd (u q))
    (huM : ∀ q x, u q x ∈ Set.Icc (0 : ℝ) M)
    (hvEq : ∀ q, v q = frozenElliptic p (u q))
    (huHolder : ∀ x,
      |u s x - u t x| ≤ Hu * d ^ (1 / 2 : ℝ)) :
    ∀ x,
      |paper5B1 p u v s x - paper5B1 p u v t x| ≤
        paper5B1TimeWindowConst p M Hu *
          d ^ paper5ForcingTimeExponent p := by
  let Cp := paper5RpowSensitivityWindowConst p M Hu
  let Lγ : ℝ := rpowLip p.γ M
  let rho : ℝ := d ^ paper5ForcingTimeExponent p
  have hCp : 0 ≤ Cp := by
    exact paper5RpowSensitivityWindowConst_nonneg p hM hHu
  have hp := rpow_sensitivity_time_modulus_le_windowConst
    p hM hHu hd0 hd1 huM huHolder
  have hLγ : 0 ≤ Lγ := rpowLip_nonneg p.hγ hM
  have hrho : 0 ≤ rho := Real.rpow_nonneg hd0 _
  have hhalf := rpow_half_le_rpow_forcingTimeExponent p hd0 hd1
  intro x
  have hvxDiff0 := frozenElliptic_deriv_diff_uniform_abs_le p hM
    (huC s) (huC t) (huM s) (huM t) huHolder x
  have hvxDiff : |deriv (v s) x - deriv (v t) x| ≤
      Lγ * Hu * rho := by
    rw [hvEq s, hvEq t]
    calc
      |deriv (frozenElliptic p (u s)) x -
          deriv (frozenElliptic p (u t)) x| ≤
          Lγ * (Hu * d ^ (1 / 2 : ℝ)) := by
        simpa only [Lγ] using hvxDiff0
      _ = (Lγ * Hu) * d ^ (1 / 2 : ℝ) := by ring
      _ ≤ (Lγ * Hu) * rho :=
        mul_le_mul_of_nonneg_left hhalf (mul_nonneg hLγ hHu)
      _ = Lγ * Hu * rho := by ring
  have hvxT : |deriv (v t) x| ≤ M ^ p.γ := by
    rw [hvEq t]
    exact frozenElliptic_deriv_abs_le_rpow_of_Icc p hM
      (huC t) (huM t) x
  have huPowS : |(u s x) ^ (p.m - 1)| ≤ M ^ (p.m - 1) := by
    rw [abs_of_nonneg (Real.rpow_nonneg (huM s x).1 _)]
    exact Real.rpow_le_rpow (huM s x).1 (huM s x).2
      (by linarith [p.hm])
  have hsplit :
      deriv (v s) x * (u s x) ^ (p.m - 1) -
          deriv (v t) x * (u t x) ^ (p.m - 1) =
        (deriv (v s) x - deriv (v t) x) *
            (u s x) ^ (p.m - 1) +
          deriv (v t) x *
            ((u s x) ^ (p.m - 1) - (u t x) ^ (p.m - 1)) := by
    ring
  unfold paper5B1
  rw [show p.m * deriv (v s) x * (u s x) ^ (p.m - 1) -
      p.m * deriv (v t) x * (u t x) ^ (p.m - 1) =
        p.m * (deriv (v s) x * (u s x) ^ (p.m - 1) -
          deriv (v t) x * (u t x) ^ (p.m - 1)) by ring,
    hsplit, abs_mul, abs_of_nonneg (by linarith [p.hm])]
  calc
    p.m * |(deriv (v s) x - deriv (v t) x) *
          (u s x) ^ (p.m - 1) +
        deriv (v t) x *
          ((u s x) ^ (p.m - 1) - (u t x) ^ (p.m - 1))| ≤
      p.m *
        (|deriv (v s) x - deriv (v t) x| *
            |(u s x) ^ (p.m - 1)| +
          |deriv (v t) x| *
            |(u s x) ^ (p.m - 1) - (u t x) ^ (p.m - 1)|) := by
      exact mul_le_mul_of_nonneg_left
        (by
          simpa only [abs_mul] using
            (abs_add_le
              ((deriv (v s) x - deriv (v t) x) *
                (u s x) ^ (p.m - 1))
              (deriv (v t) x *
                ((u s x) ^ (p.m - 1) - (u t x) ^ (p.m - 1)))))
        (by linarith [p.hm])
    _ ≤ p.m * ((Lγ * Hu * rho) * M ^ (p.m - 1) +
          M ^ p.γ * (Cp * rho)) := by
      have ht1 :
          |deriv (v s) x - deriv (v t) x| *
              |(u s x) ^ (p.m - 1)| ≤
            (Lγ * Hu * rho) * M ^ (p.m - 1) :=
        mul_le_mul hvxDiff huPowS (abs_nonneg _)
          (mul_nonneg (mul_nonneg hLγ hHu) hrho)
      have ht2 :
          |deriv (v t) x| *
              |(u s x) ^ (p.m - 1) - (u t x) ^ (p.m - 1)| ≤
            M ^ p.γ * (Cp * rho) := by
        exact mul_le_mul hvxT (by simpa only [Cp, rho] using hp x)
          (abs_nonneg _) (Real.rpow_nonneg hM _)
      exact mul_le_mul_of_nonneg_left (add_le_add ht1 ht2)
        (by linarith [p.hm])
    _ = paper5B1TimeWindowConst p M Hu *
        d ^ paper5ForcingTimeExponent p := by
      dsimp only [paper5B1TimeWindowConst, Cp, Lγ, rho]
      ring

/-- Canonical window coefficient for the reaction secant modulus. -/
def paper5ReactionTimeWindowConst
    (p : CMParams) (M Hu : ℝ) : ℝ :=
  (1 + p.α) * p.α * M ^ (p.α - 1) * Hu

theorem paper5ReactionTimeWindowConst_nonneg
    (p : CMParams) {M Hu : ℝ} (hM : 0 ≤ M) (hHu : 0 ≤ Hu) :
    0 ≤ paper5ReactionTimeWindowConst p M Hu := by
  unfold paper5ReactionTimeWindowConst
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (by linarith [p.hα]) (le_trans zero_le_one p.hα))
      (Real.rpow_nonneg hM _)) hHu

/-- Fixed-constant reaction coefficient modulus for one time pair. -/
theorem paper5ReactionCoefficient_time_modulus_le_windowConst
    (p : CMParams) {M Hu d s t : ℝ}
    {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hM : 0 ≤ M) (hHu : 0 ≤ Hu) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (huM : ∀ q x, u q x ∈ Set.Icc (0 : ℝ) M)
    (hUM : ∀ x, U x ∈ Set.Icc (0 : ℝ) M)
    (huHolder : ∀ x,
      |u s x - u t x| ≤ Hu * d ^ (1 / 2 : ℝ)) :
    ∀ x,
      |(1 - paper5A (1 + p.α) u U s x) -
        (1 - paper5A (1 + p.α) u U t x)| ≤
          paper5ReactionTimeWindowConst p M Hu *
            d ^ paper5ForcingTimeExponent p := by
  intro x
  have hsec :=
    paper5MeanCoefficient_sub_abs_le_forcingTimeExponent_of_two_le
      p (beta := 1 + p.α) (M := M) (Hu := Hu) (d := d)
        (s := u s x) (t := u t x) (r := U x)
        (by linarith [p.hα]) hM hHu hd0 hd1
        (huM s x) (huM t x) (hUM x) (huHolder x)
  unfold paper5A
  rw [show
      (1 - paper5MeanCoefficient (1 + p.α) (u s x) (U x)) -
          (1 - paper5MeanCoefficient (1 + p.α) (u t x) (U x)) =
        paper5MeanCoefficient (1 + p.α) (u t x) (U x) -
          paper5MeanCoefficient (1 + p.α) (u s x) (U x) by ring,
    abs_sub_comm]
  convert hsec using 1 <;>
    dsimp only [paper5ReactionTimeWindowConst] <;> ring

/-- Canonical window coefficient for the logarithmically regularized `b₂`
modulus. -/
def paper5B2TimeWindowConst
    (p : CMParams) (M Hu Blog : ℝ) : ℝ :=
  p.m * Blog *
    (rpowLip p.γ M * Hu * ((p.m + 1) * M ^ (p.m - 1)) +
      M ^ p.γ *
        (paper5ASensitivityWindowConst p M Hu +
          paper5RpowSensitivityWindowConst p M Hu))

theorem paper5B2TimeWindowConst_nonneg
    (p : CMParams) {M Hu Blog : ℝ}
    (hM : 0 ≤ M) (hHu : 0 ≤ Hu) (hBlog : 0 ≤ Blog) :
    0 ≤ paper5B2TimeWindowConst p M Hu Blog := by
  unfold paper5B2TimeWindowConst
  exact mul_nonneg (mul_nonneg (by linarith [p.hm]) hBlog)
    (add_nonneg
      (mul_nonneg
        (mul_nonneg (rpowLip_nonneg p.hγ hM) hHu)
        (mul_nonneg (by linarith [p.hm]) (Real.rpow_nonneg hM _)))
      (mul_nonneg (Real.rpow_nonneg hM _)
        (add_nonneg
          (paper5ASensitivityWindowConst_nonneg p hM hHu)
          (paper5RpowSensitivityWindowConst_nonneg p hM hHu))))

/-- Fixed-constant `b₂` modulus for one pair of times. -/
theorem paper5B2_time_modulus_le_windowConst
    (p : CMParams) {M Hu Blog d s t : ℝ}
    {u v : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hM : 0 ≤ M) (hHu : 0 ≤ Hu) (hBlog : 0 ≤ Blog)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (huC : ∀ q, IsCUnifBdd (u q))
    (huM : ∀ q x, u q x ∈ Set.Icc (0 : ℝ) M)
    (hUM : ∀ x, U x ∈ Set.Icc (0 : ℝ) M)
    (hUpos : ∀ x, 0 < U x)
    (hlog : ∀ x, |deriv U x / U x| ≤ Blog)
    (hvEq : ∀ q, v q = frozenElliptic p (u q))
    (huHolder : ∀ x,
      |u s x - u t x| ≤ Hu * d ^ (1 / 2 : ℝ)) :
    ∀ x,
      |paper5B2 p u v U s x - paper5B2 p u v U t x| ≤
        paper5B2TimeWindowConst p M Hu Blog *
          d ^ paper5ForcingTimeExponent p := by
  let CA := paper5ASensitivityWindowConst p M Hu
  let Cp := paper5RpowSensitivityWindowConst p M Hu
  let Lγ : ℝ := rpowLip p.γ M
  let Qmax : ℝ := (p.m + 1) * M ^ (p.m - 1)
  let rho : ℝ := d ^ paper5ForcingTimeExponent p
  have hCA : 0 ≤ CA := paper5ASensitivityWindowConst_nonneg p hM hHu
  have hCp : 0 ≤ Cp := paper5RpowSensitivityWindowConst_nonneg p hM hHu
  have hAdiff := paper5A_sensitivity_time_modulus_le_windowConst
    p hM hHu hd0 hd1 huM hUM huHolder
  have hpdiff := rpow_sensitivity_time_modulus_le_windowConst
    p hM hHu hd0 hd1 huM huHolder
  have hLγ : 0 ≤ Lγ := rpowLip_nonneg p.hγ hM
  have hQmax : 0 ≤ Qmax := by
    dsimp only [Qmax]
    exact mul_nonneg (by linarith [p.hm]) (Real.rpow_nonneg hM _)
  have hrho : 0 ≤ rho := Real.rpow_nonneg hd0 _
  have hhalf := rpow_half_le_rpow_forcingTimeExponent p hd0 hd1
  intro x
  let Q : ℝ → ℝ := fun q =>
    paper5A p.m u U q x - (u q x) ^ (p.m - 1)
  have hvxDiff0 := frozenElliptic_deriv_diff_uniform_abs_le p hM
    (huC s) (huC t) (huM s) (huM t) huHolder x
  have hvxDiff : |deriv (v s) x - deriv (v t) x| ≤
      Lγ * Hu * rho := by
    rw [hvEq s, hvEq t]
    calc
      |deriv (frozenElliptic p (u s)) x -
          deriv (frozenElliptic p (u t)) x| ≤
          Lγ * (Hu * d ^ (1 / 2 : ℝ)) := by
        simpa only [Lγ] using hvxDiff0
      _ = (Lγ * Hu) * d ^ (1 / 2 : ℝ) := by ring
      _ ≤ (Lγ * Hu) * rho :=
        mul_le_mul_of_nonneg_left hhalf (mul_nonneg hLγ hHu)
      _ = Lγ * Hu * rho := by ring
  have hvxT : |deriv (v t) x| ≤ M ^ p.γ := by
    rw [hvEq t]
    exact frozenElliptic_deriv_abs_le_rpow_of_Icc p hM
      (huC t) (huM t) x
  have hAS : |paper5A p.m u U s x| ≤
      p.m * M ^ (p.m - 1) :=
    paper5MeanCoefficient_abs_le p.hm hM (huM s x) (hUM x)
  have hpowS : |(u s x) ^ (p.m - 1)| ≤ M ^ (p.m - 1) := by
    rw [abs_of_nonneg (Real.rpow_nonneg (huM s x).1 _)]
    exact Real.rpow_le_rpow (huM s x).1 (huM s x).2
      (by linarith [p.hm])
  have hQS : |Q s| ≤ Qmax := by
    dsimp only [Q, Qmax]
    calc
      |paper5A p.m u U s x - (u s x) ^ (p.m - 1)| ≤
          |paper5A p.m u U s x| + |(u s x) ^ (p.m - 1)| :=
        abs_sub _ _
      _ ≤ p.m * M ^ (p.m - 1) + M ^ (p.m - 1) :=
        add_le_add hAS hpowS
      _ = (p.m + 1) * M ^ (p.m - 1) := by ring
  have hQdiff : |Q s - Q t| ≤ (CA + Cp) * rho := by
    dsimp only [Q]
    calc
      |(paper5A p.m u U s x - (u s x) ^ (p.m - 1)) -
          (paper5A p.m u U t x - (u t x) ^ (p.m - 1))| ≤
        |paper5A p.m u U s x - paper5A p.m u U t x| +
          |(u s x) ^ (p.m - 1) - (u t x) ^ (p.m - 1)| := by
        convert abs_sub
          (paper5A p.m u U s x - paper5A p.m u U t x)
          ((u s x) ^ (p.m - 1) - (u t x) ^ (p.m - 1)) using 1 <;>
            ring
      _ ≤ CA * rho + Cp * rho := by
        exact add_le_add
          (by simpa only [CA, rho] using hAdiff x)
          (by simpa only [Cp, rho] using hpdiff x)
      _ = (CA + Cp) * rho := by ring
  have hsRep := paper5B2_eq_logDerivative_mul_regular_difference
    p (u := u) (v := v) (U := U) (q := s) (x := x)
      (huM s x).1 (hUpos x)
  have htRep := paper5B2_eq_logDerivative_mul_regular_difference
    p (u := u) (v := v) (U := U) (q := t) (x := x)
      (huM t x).1 (hUpos x)
  rw [hsRep, htRep]
  have hsplit :
      deriv (v s) x * Q s - deriv (v t) x * Q t =
        (deriv (v s) x - deriv (v t) x) * Q s +
          deriv (v t) x * (Q s - Q t) := by ring
  rw [show
      p.m * (deriv U x / U x) * deriv (v s) x * Q s -
          p.m * (deriv U x / U x) * deriv (v t) x * Q t =
        (p.m * (deriv U x / U x)) *
          (deriv (v s) x * Q s - deriv (v t) x * Q t) by ring,
    hsplit, abs_mul]
  have hpLog : |p.m * (deriv U x / U x)| ≤ p.m * Blog := by
    rw [abs_mul, abs_of_nonneg (by linarith [p.hm])]
    exact mul_le_mul_of_nonneg_left (hlog x) (by linarith [p.hm])
  have hinner :
      |(deriv (v s) x - deriv (v t) x) * Q s +
          deriv (v t) x * (Q s - Q t)| ≤
        (Lγ * Hu * Qmax + M ^ p.γ * (CA + Cp)) * rho := by
    calc
      |(deriv (v s) x - deriv (v t) x) * Q s +
          deriv (v t) x * (Q s - Q t)| ≤
        |deriv (v s) x - deriv (v t) x| * |Q s| +
          |deriv (v t) x| * |Q s - Q t| := by
        simpa only [abs_mul] using abs_add_le
          ((deriv (v s) x - deriv (v t) x) * Q s)
          (deriv (v t) x * (Q s - Q t))
      _ ≤ (Lγ * Hu * rho) * Qmax +
          M ^ p.γ * ((CA + Cp) * rho) := by
        exact add_le_add
          (mul_le_mul hvxDiff hQS (abs_nonneg _)
            (mul_nonneg (mul_nonneg hLγ hHu) hrho))
          (mul_le_mul hvxT hQdiff (abs_nonneg _)
            (Real.rpow_nonneg hM _))
      _ = (Lγ * Hu * Qmax + M ^ p.γ * (CA + Cp)) * rho := by
        ring
  calc
    |p.m * (deriv U x / U x)| *
        |(deriv (v s) x - deriv (v t) x) * Q s +
          deriv (v t) x * (Q s - Q t)| ≤
      (p.m * Blog) *
        ((Lγ * Hu * Qmax + M ^ p.γ * (CA + Cp)) * rho) :=
      mul_le_mul hpLog hinner (abs_nonneg _)
        (mul_nonneg (by linarith [p.hm]) hBlog)
    _ = paper5B2TimeWindowConst p M Hu Blog *
        d ^ paper5ForcingTimeExponent p := by
      dsimp only [paper5B2TimeWindowConst, CA, Cp, Lγ, Qmax, rho]
      ring

/-- Canonical window coefficient for the corrected zero-order chemotaxis
term. -/
def paper5CorrectedChemZeroTimeWindowConst
    (p : CMParams) (M Hu : ℝ) : ℝ :=
  rpowLip p.γ M * Hu * (p.m * M ^ (p.m - 1)) +
    M ^ p.γ * paper5ASensitivityWindowConst p M Hu +
    (p.m + p.γ) * (p.m + p.γ - 1) *
      M ^ (p.m + p.γ - 2) * Hu

theorem paper5CorrectedChemZeroTimeWindowConst_nonneg
    (p : CMParams) {M Hu : ℝ} (hM : 0 ≤ M) (hHu : 0 ≤ Hu) :
    0 ≤ paper5CorrectedChemZeroTimeWindowConst p M Hu := by
  unfold paper5CorrectedChemZeroTimeWindowConst
  exact add_nonneg
    (add_nonneg
      (mul_nonneg
        (mul_nonneg (rpowLip_nonneg p.hγ hM) hHu)
        (mul_nonneg (by linarith [p.hm]) (Real.rpow_nonneg hM _)))
      (mul_nonneg (Real.rpow_nonneg hM _)
        (paper5ASensitivityWindowConst_nonneg p hM hHu)))
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (by linarith [p.hm, p.hγ])
          (by linarith [p.hm, p.hγ]))
        (Real.rpow_nonneg hM _)) hHu)

/-- Fixed-constant modulus for the corrected zero-order chemotaxis term. -/
theorem paper5CorrectedChemZeroCoefficient_time_modulus_le_windowConst
    (p : CMParams) {M Hu d s t : ℝ}
    {u v : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hM : 0 ≤ M) (hHu : 0 ≤ Hu) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (huC : ∀ q, IsCUnifBdd (u q))
    (huM : ∀ q x, u q x ∈ Set.Icc (0 : ℝ) M)
    (hUM : ∀ x, U x ∈ Set.Icc (0 : ℝ) M)
    (hvEq : ∀ q, v q = frozenElliptic p (u q))
    (huHolder : ∀ x,
      |u s x - u t x| ≤ Hu * d ^ (1 / 2 : ℝ)) :
    ∀ x,
      |paper5CorrectedChemZeroCoefficient p u v U s x -
          paper5CorrectedChemZeroCoefficient p u v U t x| ≤
        paper5CorrectedChemZeroTimeWindowConst p M Hu *
          d ^ paper5ForcingTimeExponent p := by
  let CA := paper5ASensitivityWindowConst p M Hu
  let Lγ : ℝ := rpowLip p.γ M
  let Cmg : ℝ := (p.m + p.γ) * (p.m + p.γ - 1) *
    M ^ (p.m + p.γ - 2) * Hu
  let rho : ℝ := d ^ paper5ForcingTimeExponent p
  have hCA : 0 ≤ CA := paper5ASensitivityWindowConst_nonneg p hM hHu
  have hAdiff := paper5A_sensitivity_time_modulus_le_windowConst
    p hM hHu hd0 hd1 huM hUM huHolder
  have hLγ : 0 ≤ Lγ := rpowLip_nonneg p.hγ hM
  have hCmg : 0 ≤ Cmg := by
    dsimp only [Cmg]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by linarith [p.hm, p.hγ])
          (by linarith [p.hm, p.hγ]))
        (Real.rpow_nonneg hM _)) hHu
  have hrho : 0 ≤ rho := Real.rpow_nonneg hd0 _
  have hhalf := rpow_half_le_rpow_forcingTimeExponent p hd0 hd1
  intro x
  have hvDiff0 := frozenElliptic_diff_uniform_abs_le p hM
    (huC s) (huC t) (huM s) (huM t) huHolder x
  have hvDiff : |v s x - v t x| ≤ Lγ * Hu * rho := by
    rw [hvEq s, hvEq t]
    calc
      |frozenElliptic p (u s) x - frozenElliptic p (u t) x| ≤
          Lγ * (Hu * d ^ (1 / 2 : ℝ)) := by
        simpa only [Lγ] using hvDiff0
      _ = (Lγ * Hu) * d ^ (1 / 2 : ℝ) := by ring
      _ ≤ (Lγ * Hu) * rho :=
        mul_le_mul_of_nonneg_left hhalf (mul_nonneg hLγ hHu)
      _ = Lγ * Hu * rho := by ring
  have hvT0 : 0 ≤ v t x := by
    rw [hvEq t]
    exact frozenElliptic_nonneg p (fun y => (huM t y).1) x
  have hvTle : v t x ≤ M ^ p.γ := by
    rw [hvEq t]
    exact frozenElliptic_le_of_rpow_le p (Real.rpow_nonneg hM _)
      (huC t).1 (fun y => (huM t y).1)
      (fun y => Real.rpow_le_rpow (huM t y).1 (huM t y).2
        (by linarith [p.hγ])) x
  have hvT : |v t x| ≤ M ^ p.γ := by
    rw [abs_of_nonneg hvT0]
    exact hvTle
  have hAS : |paper5A p.m u U s x| ≤
      p.m * M ^ (p.m - 1) :=
    paper5MeanCoefficient_abs_le p.hm hM (huM s x) (hUM x)
  have hAmgDiff :
      |paper5A (p.m + p.γ) u U s x -
          paper5A (p.m + p.γ) u U t x| ≤ Cmg * rho := by
    have hsec :=
      paper5MeanCoefficient_sub_abs_le_forcingTimeExponent_of_two_le
        p (beta := p.m + p.γ) (M := M) (Hu := Hu) (d := d)
          (s := u s x) (t := u t x) (r := U x)
          (by linarith [p.hm, p.hγ]) hM hHu hd0 hd1
          (huM s x) (huM t x) (hUM x) (huHolder x)
    simpa only [paper5A, Cmg, rho] using hsec
  unfold paper5CorrectedChemZeroCoefficient
  have hprodSplit :
      v s x * paper5A p.m u U s x -
          v t x * paper5A p.m u U t x =
        (v s x - v t x) * paper5A p.m u U s x +
          v t x * (paper5A p.m u U s x - paper5A p.m u U t x) := by
    ring
  rw [show
      (v s x * paper5A p.m u U s x - paper5A (p.m + p.γ) u U s x) -
          (v t x * paper5A p.m u U t x -
            paper5A (p.m + p.γ) u U t x) =
        (v s x * paper5A p.m u U s x -
          v t x * paper5A p.m u U t x) -
          (paper5A (p.m + p.γ) u U s x -
            paper5A (p.m + p.γ) u U t x) by ring,
    hprodSplit]
  calc
    |(v s x - v t x) * paper5A p.m u U s x +
        v t x * (paper5A p.m u U s x - paper5A p.m u U t x) -
        (paper5A (p.m + p.γ) u U s x -
          paper5A (p.m + p.γ) u U t x)| ≤
      |v s x - v t x| * |paper5A p.m u U s x| +
        |v t x| * |paper5A p.m u U s x - paper5A p.m u U t x| +
        |paper5A (p.m + p.γ) u U s x -
          paper5A (p.m + p.γ) u U t x| := by
      calc
        |(v s x - v t x) * paper5A p.m u U s x +
            v t x * (paper5A p.m u U s x - paper5A p.m u U t x) -
            (paper5A (p.m + p.γ) u U s x -
              paper5A (p.m + p.γ) u U t x)| ≤
          |(v s x - v t x) * paper5A p.m u U s x +
            v t x * (paper5A p.m u U s x - paper5A p.m u U t x)| +
            |paper5A (p.m + p.γ) u U s x -
              paper5A (p.m + p.γ) u U t x| := abs_sub _ _
        _ ≤ (|v s x - v t x| * |paper5A p.m u U s x| +
              |v t x| *
                |paper5A p.m u U s x - paper5A p.m u U t x|) +
            |paper5A (p.m + p.γ) u U s x -
              paper5A (p.m + p.γ) u U t x| := by
          gcongr
          simpa only [abs_mul] using abs_add_le
            ((v s x - v t x) * paper5A p.m u U s x)
            (v t x * (paper5A p.m u U s x - paper5A p.m u U t x))
    _ ≤ (Lγ * Hu * rho) * (p.m * M ^ (p.m - 1)) +
        M ^ p.γ * (CA * rho) + Cmg * rho := by
      exact add_le_add
        (add_le_add
          (mul_le_mul hvDiff hAS (abs_nonneg _)
            (mul_nonneg (mul_nonneg hLγ hHu) hrho))
          (mul_le_mul hvT (by simpa only [CA, rho] using hAdiff x)
            (abs_nonneg _) (Real.rpow_nonneg hM _)))
        hAmgDiff
    _ = paper5CorrectedChemZeroTimeWindowConst p M Hu *
        d ^ paper5ForcingTimeExponent p := by
      dsimp only [paper5CorrectedChemZeroTimeWindowConst, CA, Lγ, Cmg, rho]
      ring

/-- Canonical window coefficient for the complete dynamic coefficient
multiplying the weighted population. -/
def paper5WeightedFluxPopulationTimeWindowConst
    (p : CMParams) (M eta Hu Blog : ℝ) : ℝ :=
  paper5B2TimeWindowConst p M Hu Blog +
    paper5CorrectedChemZeroTimeWindowConst p M Hu +
    |eta| * paper5B1TimeWindowConst p M Hu

theorem paper5WeightedFluxPopulationTimeWindowConst_nonneg
    (p : CMParams) {M eta Hu Blog : ℝ}
    (hM : 0 ≤ M) (hHu : 0 ≤ Hu) (hBlog : 0 ≤ Blog) :
    0 ≤ paper5WeightedFluxPopulationTimeWindowConst p M eta Hu Blog := by
  unfold paper5WeightedFluxPopulationTimeWindowConst
  exact add_nonneg
    (add_nonneg
      (paper5B2TimeWindowConst_nonneg p hM hHu hBlog)
      (paper5CorrectedChemZeroTimeWindowConst_nonneg p hM hHu))
    (mul_nonneg (abs_nonneg _)
      (paper5B1TimeWindowConst_nonneg p hM hHu))

/-- Fixed-constant modulus for the complete population coefficient. -/
theorem paper5WeightedFluxPopulationCoefficient_time_modulus_le_windowConst
    (p : CMParams) {M eta Hu Blog d s t : ℝ}
    {u v : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hM : 0 ≤ M) (hHu : 0 ≤ Hu) (hBlog : 0 ≤ Blog)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (huC : ∀ q, IsCUnifBdd (u q))
    (huM : ∀ q x, u q x ∈ Set.Icc (0 : ℝ) M)
    (hUM : ∀ x, U x ∈ Set.Icc (0 : ℝ) M)
    (hUpos : ∀ x, 0 < U x)
    (hlog : ∀ x, |deriv U x / U x| ≤ Blog)
    (hvEq : ∀ q, v q = frozenElliptic p (u q))
    (huHolder : ∀ x,
      |u s x - u t x| ≤ Hu * d ^ (1 / 2 : ℝ)) :
    ∀ x,
      |paper5WeightedFluxPopulationCoefficient p eta u v U s x -
          paper5WeightedFluxPopulationCoefficient p eta u v U t x| ≤
        paper5WeightedFluxPopulationTimeWindowConst p M eta Hu Blog *
          d ^ paper5ForcingTimeExponent p := by
  let D1 := paper5B1TimeWindowConst p M Hu
  let DB2 := paper5B2TimeWindowConst p M Hu Blog
  let DC := paper5CorrectedChemZeroTimeWindowConst p M Hu
  let rho : ℝ := d ^ paper5ForcingTimeExponent p
  have hB1 := paper5B1_time_modulus_le_windowConst
    p hM hHu hd0 hd1 huC huM hvEq huHolder
  have hB2 := paper5B2_time_modulus_le_windowConst
    p hM hHu hBlog hd0 hd1 huC huM hUM hUpos hlog hvEq huHolder
  have hC := paper5CorrectedChemZeroCoefficient_time_modulus_le_windowConst
    p hM hHu hd0 hd1 huC huM hUM hvEq huHolder
  intro x
  unfold paper5WeightedFluxPopulationCoefficient
  rw [show
      (paper5B2 p u v U s x +
          paper5CorrectedChemZeroCoefficient p u v U s x -
          eta * paper5B1 p u v s x) -
        (paper5B2 p u v U t x +
          paper5CorrectedChemZeroCoefficient p u v U t x -
          eta * paper5B1 p u v t x) =
      (paper5B2 p u v U s x - paper5B2 p u v U t x) +
        (paper5CorrectedChemZeroCoefficient p u v U s x -
          paper5CorrectedChemZeroCoefficient p u v U t x) -
        eta * (paper5B1 p u v s x - paper5B1 p u v t x) by ring]
  calc
    |(paper5B2 p u v U s x - paper5B2 p u v U t x) +
        (paper5CorrectedChemZeroCoefficient p u v U s x -
          paper5CorrectedChemZeroCoefficient p u v U t x) -
        eta * (paper5B1 p u v s x - paper5B1 p u v t x)| ≤
      |paper5B2 p u v U s x - paper5B2 p u v U t x| +
        |paper5CorrectedChemZeroCoefficient p u v U s x -
          paper5CorrectedChemZeroCoefficient p u v U t x| +
        |eta| * |paper5B1 p u v s x - paper5B1 p u v t x| := by
      calc
        |(paper5B2 p u v U s x - paper5B2 p u v U t x) +
            (paper5CorrectedChemZeroCoefficient p u v U s x -
              paper5CorrectedChemZeroCoefficient p u v U t x) -
            eta * (paper5B1 p u v s x - paper5B1 p u v t x)| ≤
          |(paper5B2 p u v U s x - paper5B2 p u v U t x) +
            (paper5CorrectedChemZeroCoefficient p u v U s x -
              paper5CorrectedChemZeroCoefficient p u v U t x)| +
            |eta * (paper5B1 p u v s x - paper5B1 p u v t x)| :=
          abs_sub _ _
        _ ≤ (|paper5B2 p u v U s x - paper5B2 p u v U t x| +
              |paper5CorrectedChemZeroCoefficient p u v U s x -
                paper5CorrectedChemZeroCoefficient p u v U t x|) +
            |eta| * |paper5B1 p u v s x - paper5B1 p u v t x| := by
          gcongr
          · exact abs_add_le _ _
          · rw [abs_mul]
    _ ≤ DB2 * rho + DC * rho + |eta| * (D1 * rho) := by
      exact add_le_add
        (add_le_add
          (by simpa only [DB2, rho] using hB2 x)
          (by simpa only [DC, rho] using hC x))
        (mul_le_mul_of_nonneg_left
          (by simpa only [D1, rho] using hB1 x) (abs_nonneg eta))
    _ = paper5WeightedFluxPopulationTimeWindowConst p M eta Hu Blog *
        d ^ paper5ForcingTimeExponent p := by
      dsimp only [paper5WeightedFluxPopulationTimeWindowConst,
        D1, DB2, DC, rho]
      ring

/-- Any two times in a window of length at most one are at distance at most
one. -/
theorem abs_sub_le_one_of_mem_Icc_of_sub_le_one
    {a b s t : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b)
    (hdiam : b - a ≤ 1) :
    |s - t| ≤ 1 := by
  rw [abs_le]
  constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]

/-- One `b₁` modulus constant controls the whole unit-size window. -/
theorem paper5B1_time_modulus_uniform_window
    (p : CMParams) {M Hu a b : ℝ}
    {u v : ℝ → ℝ → ℝ}
    (hM : 0 ≤ M) (hHu : 0 ≤ Hu) (hdiam : b - a ≤ 1)
    (huC : ∀ q, IsCUnifBdd (u q))
    (huM : ∀ q x, u q x ∈ Set.Icc (0 : ℝ) M)
    (hvEq : ∀ q, v q = frozenElliptic p (u q))
    (huHolder : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, ∀ x,
      |u s x - u t x| ≤ Hu * |s - t| ^ (1 / 2 : ℝ)) :
    0 ≤ paper5B1TimeWindowConst p M Hu ∧
      ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, ∀ x,
      |paper5B1 p u v s x - paper5B1 p u v t x| ≤
        paper5B1TimeWindowConst p M Hu *
          |s - t| ^ paper5ForcingTimeExponent p := by
  refine ⟨paper5B1TimeWindowConst_nonneg p hM hHu, ?_⟩
  intro s hs t ht x
  exact paper5B1_time_modulus_le_windowConst p hM hHu
    (abs_nonneg _) (abs_sub_le_one_of_mem_Icc_of_sub_le_one hs ht hdiam)
    huC huM hvEq (huHolder s hs t ht) x

/-- One complete population-coefficient modulus controls the whole
unit-size window. -/
theorem paper5WeightedFluxPopulationCoefficient_time_modulus_uniform_window
    (p : CMParams) {M eta Hu Blog a b : ℝ}
    {u v : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hM : 0 ≤ M) (hHu : 0 ≤ Hu) (hBlog : 0 ≤ Blog)
    (hdiam : b - a ≤ 1)
    (huC : ∀ q, IsCUnifBdd (u q))
    (huM : ∀ q x, u q x ∈ Set.Icc (0 : ℝ) M)
    (hUM : ∀ x, U x ∈ Set.Icc (0 : ℝ) M)
    (hUpos : ∀ x, 0 < U x)
    (hlog : ∀ x, |deriv U x / U x| ≤ Blog)
    (hvEq : ∀ q, v q = frozenElliptic p (u q))
    (huHolder : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, ∀ x,
      |u s x - u t x| ≤ Hu * |s - t| ^ (1 / 2 : ℝ)) :
    0 ≤ paper5WeightedFluxPopulationTimeWindowConst p M eta Hu Blog ∧
      ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, ∀ x,
      |paper5WeightedFluxPopulationCoefficient p eta u v U s x -
          paper5WeightedFluxPopulationCoefficient p eta u v U t x| ≤
        paper5WeightedFluxPopulationTimeWindowConst p M eta Hu Blog *
          |s - t| ^ paper5ForcingTimeExponent p := by
  refine ⟨paper5WeightedFluxPopulationTimeWindowConst_nonneg
    p hM hHu hBlog, ?_⟩
  intro s hs t ht x
  exact paper5WeightedFluxPopulationCoefficient_time_modulus_le_windowConst
    p hM hHu hBlog (abs_nonneg _)
      (abs_sub_le_one_of_mem_Icc_of_sub_le_one hs ht hdiam)
      huC huM hUM hUpos hlog hvEq (huHolder s hs t ht) x

/-- One reaction-coefficient modulus controls the whole unit-size window. -/
theorem paper5ReactionCoefficient_time_modulus_uniform_window
    (p : CMParams) {M Hu a b : ℝ}
    {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hM : 0 ≤ M) (hHu : 0 ≤ Hu) (hdiam : b - a ≤ 1)
    (huM : ∀ q x, u q x ∈ Set.Icc (0 : ℝ) M)
    (hUM : ∀ x, U x ∈ Set.Icc (0 : ℝ) M)
    (huHolder : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, ∀ x,
      |u s x - u t x| ≤ Hu * |s - t| ^ (1 / 2 : ℝ)) :
    0 ≤ paper5ReactionTimeWindowConst p M Hu ∧
      ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, ∀ x,
      |(1 - paper5A (1 + p.α) u U s x) -
        (1 - paper5A (1 + p.α) u U t x)| ≤
          paper5ReactionTimeWindowConst p M Hu *
            |s - t| ^ paper5ForcingTimeExponent p := by
  refine ⟨paper5ReactionTimeWindowConst_nonneg p hM hHu, ?_⟩
  intro s hs t ht x
  exact paper5ReactionCoefficient_time_modulus_le_windowConst
    p hM hHu (abs_nonneg _)
      (abs_sub_le_one_of_mem_Icc_of_sub_le_one hs ht hdiam)
      huM hUM (huHolder s hs t ht) x

set_option maxHeartbeats 3000000 in
/-- Fixed-modulus positive-window forcing estimate.  In contrast with a
pairwise existential estimate, `D₁`, `D₂`, `DR`, and the resulting `H` are
fixed before `s` and `t` are quantified. -/
theorem
    exists_paper5WeightedGeneratorForcingExpandedPositiveWindowL2Trajectory_uniform_holder_of_uniform_moduli
    (p : CMParams) {M eta a b : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    {K₁ K₂ K₃ K₄ KR D₁ D₂ DR : ℝ}
    {EW EWx EZ EZx HW HWx : ℝ}
    (hab : a ≤ b)
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
    (hHW : 0 ≤ HW) (hHWx : 0 ≤ HWx)
    (hB₁_bound : ∀ q ∈ Set.Icc a b, ∀ x,
      |paper5B1 p u v q x| ≤ K₁)
    (hB₁_diff : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, ∀ x,
      |paper5B1 p u v s x - paper5B1 p u v t x| ≤
        D₁ * |s - t| ^ paper5ForcingTimeExponent p)
    (hB₂_bound : ∀ q ∈ Set.Icc a b, ∀ x,
      |paper5WeightedFluxPopulationCoefficient p eta u v U q x| ≤ K₂)
    (hB₂_diff : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, ∀ x,
      |paper5WeightedFluxPopulationCoefficient p eta u v U s x -
        paper5WeightedFluxPopulationCoefficient p eta u v U t x| ≤
          D₂ * |s - t| ^ paper5ForcingTimeExponent p)
    (hB₃_bound : ∀ x, |paper5B3 p U x| ≤ K₃)
    (hB₄_bound : ∀ x,
      |paper5WeightedFluxSignalCoefficient p eta U x| ≤ K₄)
    (hR_bound : ∀ q ∈ Set.Icc a b, ∀ x,
      |1 - paper5A (1 + p.α) u U q x| ≤ KR)
    (hR_diff : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, ∀ x,
      |(1 - paper5A (1 + p.α) u U s x) -
        (1 - paper5A (1 + p.α) u U t x)| ≤
          DR * |s - t| ^ paper5ForcingTimeExponent p)
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
    (hW_diff : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, Integrable (fun x =>
      (paper5WeightedPopulation eta u U s x -
        paper5WeightedPopulation eta u U t x) ^ 2) volume)
    (hWx_diff : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, Integrable (fun x =>
      (paper5WeightedPopulationX eta u U s x -
        paper5WeightedPopulationX eta u U t x) ^ 2) volume)
    (hW_sq : ∀ q ∈ Set.Icc a b, Integrable (fun x =>
      paper5WeightedPopulation eta u U q x ^ 2) volume)
    (hWx_sq : ∀ q ∈ Set.Icc a b, Integrable (fun x =>
      paper5WeightedPopulationX eta u U q x ^ 2) volume)
    (hZ_sq : ∀ q ∈ Set.Icc a b, Integrable (fun x =>
      paper5WeightedSignal eta v V q x ^ 2) volume)
    (hZx_sq : ∀ q ∈ Set.Icc a b, Integrable (fun x =>
      paper5WeightedSignalX eta v V q x ^ 2) volume)
    (hW_diff_bound : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
      (∫ x : ℝ, (paper5WeightedPopulation eta u U s x -
        paper5WeightedPopulation eta u U t x) ^ 2) ≤
        HW ^ 2 * (|s - t| ^ paper5ForcingTimeExponent p) ^ 2)
    (hWx_diff_bound : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
      (∫ x : ℝ, (paper5WeightedPopulationX eta u U s x -
        paper5WeightedPopulationX eta u U t x) ^ 2) ≤
        HWx ^ 2 * (|s - t| ^ paper5ForcingTimeExponent p) ^ 2)
    (hW_bound : ∀ q ∈ Set.Icc a b,
      (∫ x : ℝ, paper5WeightedPopulation eta u U q x ^ 2) ≤ EW ^ 2)
    (hWx_bound : ∀ q ∈ Set.Icc a b,
      (∫ x : ℝ, paper5WeightedPopulationX eta u U q x ^ 2) ≤ EWx ^ 2)
    (hZ_bound : ∀ q ∈ Set.Icc a b,
      (∫ x : ℝ, paper5WeightedSignal eta v V q x ^ 2) ≤ EZ ^ 2)
    (hZx_bound : ∀ q ∈ Set.Icc a b,
      (∫ x : ℝ, paper5WeightedSignalX eta v V q x ^ 2) ≤ EZx ^ 2) :
    ∃ H : ℝ, 0 ≤ H ∧
      ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
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
        H * |s - t| ^ paper5ForcingTimeExponent p := by
  let HZ := Real.sqrt (paper5WeightedResolverVFactor p M eta) * HW
  let HZx := Real.sqrt (paper5WeightedResolverVxFactor p M eta) * HW
  let H := Real.sqrt (paper5WeightedGeneratorForcingHolderSquareConst p
    K₁ K₂ K₃ K₄ KR D₁ D₂ DR EWx EW HWx HW HZx HZ)
  refine ⟨H, Real.sqrt_nonneg _, ?_⟩
  intro s hs t ht
  have hrho : 0 ≤ |s - t| ^ paper5ForcingTimeExponent p :=
    Real.rpow_nonneg (abs_nonneg _) _
  have hmain :=
    paper5WeightedGeneratorForcingExpandedPositiveWindowL2Trajectory_norm_sub_le_of_population_H1_modulus
      p hab hs ht hM heta heta1 huC huM hvEq hvDiff
        hK₁ hK₂ hK₃ hK₄ hKR hD₁ hD₂ hDR
        hEW hEWx hEZ hEZx hHW hHWx hrho
        (hB₁_bound s hs) (hB₁_diff s hs t ht)
        (hB₂_bound s hs) (hB₂_diff s hs t ht)
        hB₃_bound hB₄_bound (hR_bound s hs) (hR_diff s hs t ht)
        hB₁_meas hB₂_meas hB₃_meas hB₄_meas hR_meas
        hW_meas hWx_meas hZ_meas hZx_meas hF_meas hF_sq
        (hW_diff s hs t ht) (hWx_diff s hs t ht)
        (hW_sq t ht) (hWx_sq t ht) (hZ_sq t ht) (hZx_sq t ht)
        (hW_diff_bound s hs t ht) (hWx_diff_bound s hs t ht)
        (hW_bound t ht) (hWx_bound t ht) (hZ_bound t ht) (hZx_bound t ht)
  simpa only [H, HZ, HZx] using hmain

set_option maxHeartbeats 3000000 in
/-- Natural uniform-window Holder producer for the canonical exact-weight
forcing trajectory.  The three dynamic coefficient constants are explicit
functions of the fixed window data and are selected before the time pair;
the conclusion therefore supplies one Holder constant for the entire
window. -/
theorem
    exists_paper5WeightedGeneratorForcingExpandedPositiveWindowL2Trajectory_natural_uniform_holder
    (p : CMParams) {M eta a b Hu Blog : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    {K₁ K₂ K₃ K₄ KR : ℝ}
    {EW EWx EZ EZx HW HWx : ℝ}
    (hab : a ≤ b) (hdiam : b - a ≤ 1)
    (hM : 1 ≤ M) (heta : 0 < eta) (heta1 : eta < 1)
    (huC : ∀ q, IsCUnifBdd (u q))
    (huM : ∀ q x, u q x ∈ Set.Icc (0 : ℝ) M)
    (hUM : ∀ x, U x ∈ Set.Icc (0 : ℝ) M)
    (hUpos : ∀ x, 0 < U x)
    (hBlog : 0 ≤ Blog)
    (hlog : ∀ x, |deriv U x / U x| ≤ Blog)
    (hvEq : ∀ q, v q = frozenElliptic p (u q))
    (hvDiff : ∀ q, Differentiable ℝ (v q))
    (hHu : 0 ≤ Hu)
    (huHolder : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, ∀ x,
      |u s x - u t x| ≤ Hu * |s - t| ^ (1 / 2 : ℝ))
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hK₃ : 0 ≤ K₃) (hK₄ : 0 ≤ K₄) (hKR : 0 ≤ KR)
    (hEW : 0 ≤ EW) (hEWx : 0 ≤ EWx)
    (hEZ : 0 ≤ EZ) (hEZx : 0 ≤ EZx)
    (hHW : 0 ≤ HW) (hHWx : 0 ≤ HWx)
    (hB₁_bound : ∀ q ∈ Set.Icc a b, ∀ x,
      |paper5B1 p u v q x| ≤ K₁)
    (hB₂_bound : ∀ q ∈ Set.Icc a b, ∀ x,
      |paper5WeightedFluxPopulationCoefficient p eta u v U q x| ≤ K₂)
    (hB₃_bound : ∀ x, |paper5B3 p U x| ≤ K₃)
    (hB₄_bound : ∀ x,
      |paper5WeightedFluxSignalCoefficient p eta U x| ≤ K₄)
    (hR_bound : ∀ q ∈ Set.Icc a b, ∀ x,
      |1 - paper5A (1 + p.α) u U q x| ≤ KR)
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
    (hW_diff : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, Integrable (fun x =>
      (paper5WeightedPopulation eta u U s x -
        paper5WeightedPopulation eta u U t x) ^ 2) volume)
    (hWx_diff : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, Integrable (fun x =>
      (paper5WeightedPopulationX eta u U s x -
        paper5WeightedPopulationX eta u U t x) ^ 2) volume)
    (hW_sq : ∀ q ∈ Set.Icc a b, Integrable (fun x =>
      paper5WeightedPopulation eta u U q x ^ 2) volume)
    (hWx_sq : ∀ q ∈ Set.Icc a b, Integrable (fun x =>
      paper5WeightedPopulationX eta u U q x ^ 2) volume)
    (hZ_sq : ∀ q ∈ Set.Icc a b, Integrable (fun x =>
      paper5WeightedSignal eta v V q x ^ 2) volume)
    (hZx_sq : ∀ q ∈ Set.Icc a b, Integrable (fun x =>
      paper5WeightedSignalX eta v V q x ^ 2) volume)
    (hW_diff_bound : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
      (∫ x : ℝ, (paper5WeightedPopulation eta u U s x -
        paper5WeightedPopulation eta u U t x) ^ 2) ≤
        HW ^ 2 * (|s - t| ^ paper5ForcingTimeExponent p) ^ 2)
    (hWx_diff_bound : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
      (∫ x : ℝ, (paper5WeightedPopulationX eta u U s x -
        paper5WeightedPopulationX eta u U t x) ^ 2) ≤
        HWx ^ 2 * (|s - t| ^ paper5ForcingTimeExponent p) ^ 2)
    (hW_bound : ∀ q ∈ Set.Icc a b,
      (∫ x : ℝ, paper5WeightedPopulation eta u U q x ^ 2) ≤ EW ^ 2)
    (hWx_bound : ∀ q ∈ Set.Icc a b,
      (∫ x : ℝ, paper5WeightedPopulationX eta u U q x ^ 2) ≤ EWx ^ 2)
    (hZ_bound : ∀ q ∈ Set.Icc a b,
      (∫ x : ℝ, paper5WeightedSignal eta v V q x ^ 2) ≤ EZ ^ 2)
    (hZx_bound : ∀ q ∈ Set.Icc a b,
      (∫ x : ℝ, paper5WeightedSignalX eta v V q x ^ 2) ≤ EZx ^ 2) :
    ∃ H : ℝ, 0 ≤ H ∧
      ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
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
        H * |s - t| ^ paper5ForcingTimeExponent p := by
  let D₁ := paper5B1TimeWindowConst p M Hu
  let D₂ := paper5WeightedFluxPopulationTimeWindowConst p M eta Hu Blog
  let DR := paper5ReactionTimeWindowConst p M Hu
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hD₁_data := paper5B1_time_modulus_uniform_window
    p hM0 hHu hdiam huC huM hvEq huHolder
  have hD₂_data :=
    paper5WeightedFluxPopulationCoefficient_time_modulus_uniform_window
      (eta := eta) p hM0 hHu hBlog hdiam
        huC huM hUM hUpos hlog hvEq huHolder
  have hDR_data := paper5ReactionCoefficient_time_modulus_uniform_window
    p hM0 hHu hdiam huM hUM huHolder
  exact
    exists_paper5WeightedGeneratorForcingExpandedPositiveWindowL2Trajectory_uniform_holder_of_uniform_moduli
      p hab hM heta heta1 huC huM hvEq hvDiff
        hK₁ hK₂ hK₃ hK₄ hKR
        (by simpa only [D₁] using hD₁_data.1)
        (by simpa only [D₂] using hD₂_data.1)
        (by simpa only [DR] using hDR_data.1)
        hEW hEWx hEZ hEZx hHW hHWx
        hB₁_bound (by simpa only [D₁] using hD₁_data.2)
        hB₂_bound (by simpa only [D₂] using hD₂_data.2)
        hB₃_bound hB₄_bound hR_bound
        (by simpa only [DR] using hDR_data.2)
        hB₁_meas hB₂_meas hB₃_meas hB₄_meas hR_meas
        hW_meas hWx_meas hZ_meas hZx_meas hF_meas hF_sq
        hW_diff hWx_diff hW_sq hWx_sq hZ_sq hZx_sq
        hW_diff_bound hWx_diff_bound hW_bound hWx_bound hZ_bound hZx_bound

section AxiomAudit

#print axioms
  exists_paper5WeightedGeneratorForcingExpandedPositiveWindowL2Trajectory_uniform_holder_of_uniform_moduli
#print axioms paper5B1_time_modulus_uniform_window
#print axioms
  paper5WeightedFluxPopulationCoefficient_time_modulus_uniform_window
#print axioms paper5ReactionCoefficient_time_modulus_uniform_window
#print axioms
  exists_paper5WeightedGeneratorForcingExpandedPositiveWindowL2Trajectory_natural_uniform_holder

end AxiomAudit

end ShenWork.Paper1
