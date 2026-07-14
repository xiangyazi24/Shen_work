import ShenWork.Paper3.IntervalDomainMLinearCoefficients
import ShenWork.Paper2.IntervalBFormSquareHeatT0Restart

open Set Filter Topology

noncomputable section

namespace ShenWork.Paper3

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.Paper2.BFormPositiveDatumNegPart
open ShenWork.Paper2.IntervalDomainMMinPersistence
open ShenWork.MinPersistenceAtoms

def intervalDomainMLinearDriftBound (p : CM2Params) (M : ℝ) : ℝ :=
  |p.χ₀| * p.m * M ^ (p.m - 1) * (2 * (p.ν * M ^ p.γ))

def intervalDomainMLinearReactionBound (p : CM2Params) (M : ℝ) : ℝ :=
  let Q := 2 * (p.ν * M ^ p.γ)
  p.a + p.b * M ^ p.α +
    |p.χ₀| * M ^ (p.m - 1) * (Q + p.β * Q ^ 2)

theorem intervalDomainMLinearDriftBound_nonneg
    {p : CM2Params} {M : ℝ} (hm : 1 ≤ p.m) (hM : 0 ≤ M) :
    0 ≤ intervalDomainMLinearDriftBound p M := by
  unfold intervalDomainMLinearDriftBound
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (abs_nonneg _) (le_trans (by norm_num) hm))
      (Real.rpow_nonneg hM _))
    (mul_nonneg (by norm_num) (mul_nonneg p.hν.le (Real.rpow_nonneg hM _)))

theorem intervalDomainMLinearReactionBound_nonneg
    {p : CM2Params} {M : ℝ} (_hm : 1 ≤ p.m) (hM : 0 ≤ M) :
    0 ≤ intervalDomainMLinearReactionBound p M := by
  unfold intervalDomainMLinearReactionBound
  dsimp
  have hQ : 0 ≤ 2 * (p.ν * M ^ p.γ) :=
    mul_nonneg (by norm_num) (mul_nonneg p.hν.le (Real.rpow_nonneg hM _))
  exact add_nonneg
    (add_nonneg p.ha (mul_nonneg p.hb (Real.rpow_nonneg hM _)))
    (mul_nonneg
      (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hM _))
      (add_nonneg hQ (mul_nonneg p.hβ (sq_nonneg _))))

/-- Closed-interval elliptic gradient estimate extracted from a faithful
classical solution. -/
theorem intervalDomainM_classical_vx_abs_le_Icc
    {p : CM2Params} {T t M : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) (hM : 0 ≤ M)
    (hu_le : ∀ x : intervalDomainPoint, u t x ≤ M) :
    ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (v t)) y| ≤ 2 * (p.ν * M ^ p.γ) := by
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  obtain ⟨hOpen, _, _, hNeu, hClosed, _, _⟩ := hsol.regularity
  have hU2 := (hOpen t ht).1
  have hV2 := (hOpen t ht).2
  have hVcont := (hClosed t ht).2.1.continuousOn
  have hVnn : ∀ y, 0 ≤ intervalDomainLift (v t) y := by
    intro y
    unfold intervalDomainLift
    split_ifs
    · exact hsol.v_nonneg ht0 htT
    · exact le_rfl
  have hUnn : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      0 ≤ intervalDomainLift (u t) y := by
    intro y hy
    simp only [intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hy)]
    exact (hsol.u_pos' ht0 htT).le
  have hUle : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      intervalDomainLift (u t) y ≤ M := by
    intro y hy
    simpa [intervalDomainLift, Set.Ioo_subset_Icc_self hy] using
      hu_le ⟨y, Set.Ioo_subset_Icc_self hy⟩
  have hPDE : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      deriv (deriv (intervalDomainLift (v t))) y =
        p.μ * intervalDomainLift (v t) y -
          p.ν * intervalDomainLift (u t) y ^ p.γ := by
    intro y hy
    let X : intervalDomainPoint := ⟨y, Set.Ioo_subset_Icc_self hy⟩
    have hpde := hsol.pde_v ht0 htT (x := X) hy
    change 0 = deriv (deriv (intervalDomainLift (v t))) y -
      p.μ * v t X + p.ν * (u t X) ^ p.γ at hpde
    have hUv : intervalDomainLift (u t) y = u t X := by
      rw [intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hy)]
    have hVv : intervalDomainLift (v t) y = v t X := by
      rw [intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hy)]
    rw [hUv, hVv]
    linarith
  have hvb := v_slice_coeff_bounds (p := p) (u := u t) (v := v t)
    hM hV2 hVcont hVnn hUnn hUle hPDE (hNeu t ht).2.1 (hNeu t ht).2.2
  intro y hy
  rcases eq_or_lt_of_le hy.1 with rfl | hy0
  · rw [(hClosed t ht).2.2.1]
    have hQ : 0 ≤ 2 * (p.ν * M ^ p.γ) :=
      mul_nonneg (by norm_num)
        (mul_nonneg p.hν.le (Real.rpow_nonneg hM _))
    simpa using hQ
  rcases eq_or_lt_of_le hy.2 with rfl | hy1
  · rw [(hClosed t ht).2.2.2]
    have hQ : 0 ≤ 2 * (p.ν * M ^ p.γ) :=
      mul_nonneg (by norm_num)
        (mul_nonneg p.hν.le (Real.rpow_nonneg hM _))
    simpa using hQ
  exact hvb.1 y ⟨hy0, hy1⟩

/-- Pointwise coefficient bounds on the whole closed interval. -/
theorem intervalDomainM_classical_linearCoefficients_abs_le_Icc
    {p : CM2Params} {T t M : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hm : 1 ≤ p.m)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) (hM : 0 ≤ M)
    (hu_le : ∀ x : intervalDomainPoint, u t x ≤ M) :
    ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |intervalDomainMLinearDrift p u v t y| ≤
          intervalDomainMLinearDriftBound p M ∧
        |intervalDomainMLinearReaction p u v t y| ≤
          intervalDomainMLinearReactionBound p M := by
  intro y hy
  have hU0 : 0 ≤ intervalDomainLift (u t) y := by
    simpa [intervalDomainLift, hy] using
      (hsol.u_pos' (x := (⟨y, hy⟩ : intervalDomainPoint)) ht0 htT).le
  have hUM : intervalDomainLift (u t) y ≤ M := by
    simpa [intervalDomainLift, hy] using hu_le ⟨y, hy⟩
  have hV0 : 0 ≤ intervalDomainLift (v t) y := by
    simpa [intervalDomainLift, hy] using
      hsol.v_nonneg (x := (⟨y, hy⟩ : intervalDomainPoint)) ht0 htT
  have hVx := intervalDomainM_classical_vx_abs_le_Icc
    hsol ht0 htT hM hu_le y hy
  have hVxx := vReactionM_abs_le_Icc hsol ht0 htT hM hu_le y hy
  constructor
  · simpa [intervalDomainMLinearDriftBound] using
      intervalDomainMLinearDrift_abs_le hm hM hU0 hUM hV0 hVx
  · simpa [intervalDomainMLinearReactionBound] using
      intervalDomainMLinearReaction_abs_le hm hM hU0 hUM hV0 hVx hVxx

/-- The faithful classical solution supplies the full bounded coefficient
package on every positive physical strip with a common `u` ceiling. -/
theorem intervalDomainM_classical_linearCoefficientsRegular
    {p : CM2Params} {T s L M : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hm : 1 ≤ p.m)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hs : 0 < s) (_hL : 0 ≤ L) (hsLT : s + L < T) (hM : 0 ≤ M)
    (hu_le : ∀ r ∈ Set.Icc (0 : ℝ) L,
      ∀ x : intervalDomainPoint, u (s + r) x ≤ M) :
    NeumannLinearDriftCoefficientsRegular L
      (restartTimeShift s (intervalDomainMLinearDrift p u v))
      (restartTimeShift s (intervalDomainMLinearReaction p u v)) := by
  let A := intervalDomainMLinearDriftBound p M
  let D := intervalDomainMLinearReactionBound p M
  have hA : 0 ≤ A := intervalDomainMLinearDriftBound_nonneg hm hM
  have hD : 0 ≤ D := intervalDomainMLinearReactionBound_nonneg hm hM
  have hbounds : ∀ r ∈ Set.Icc (0 : ℝ) L, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |intervalDomainMLinearDrift p u v (s + r) x| ≤ A ∧
      |intervalDomainMLinearReaction p u v (s + r) x| ≤ D := by
    intro r hr x hx
    have ht0 : 0 < s + r := lt_of_lt_of_le hs (le_add_of_nonneg_right hr.1)
    have htT : s + r < T := by linarith [hr.2]
    simpa [A, D] using
      intervalDomainM_classical_linearCoefficients_abs_le_Icc
        hm hsol ht0 htT hM (hu_le r hr) x hx
  refine
    { drift_bounded := ⟨A, hA, ?_⟩
      reaction_bounded := ⟨D, hD, ?_⟩
      reaction_lipschitz := ⟨D, hD, ?_⟩ }
  · intro r hr x hx
    simpa [restartTimeShift] using (hbounds r hr x hx).1
  · intro r hr x hx
    simpa [restartTimeShift] using (hbounds r hr x hx).2
  · intro r x a b hr hx
    have hC := (hbounds r hr x hx).2
    simp only [restartTimeShift]
    rw [show intervalDomainMLinearReaction p u v (s + r) x * a -
        intervalDomainMLinearReaction p u v (s + r) x * b =
        intervalDomainMLinearReaction p u v (s + r) x * (a - b) by ring,
      abs_mul]
    exact mul_le_mul_of_nonneg_right hC (abs_nonneg _)

end ShenWork.Paper3

#print axioms ShenWork.Paper3.intervalDomainM_classical_vx_abs_le_Icc
#print axioms ShenWork.Paper3.intervalDomainM_classical_linearCoefficientsRegular
