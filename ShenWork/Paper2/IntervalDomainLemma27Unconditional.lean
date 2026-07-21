/-
  ShenWork/Paper2/IntervalDomainLemma27Unconditional.lean

  Paper 2 Lemma 2.7 on the concrete `intervalDomain`.

  MAIN FINDING.  The literal statement `Lemma_2_7 intervalDomain` — the damping
  differential inequality forcing a *uniform-on-(0,T)* Lᵖ bound for an
  ARBITRARY `u` — is FALSE.  The obstruction is exactly the one recorded in the
  docstring of `unitPointDomain.Lemma_2_7_from_continuous_bound`: the pointwise
  derivative inequality cannot prevent the Lᵖ mass from blowing up as `t → 0⁺`.

  Concretely, `u(t,x) = t⁻¹`, `pExp = 2`, `C₁ = C₂ = C₃ = 0`, `C₄ = 1`,
  `α = ε = 1`, `T = 1`:
    * `∫₀¹ (u t x)² dx = t⁻²` (the domain has total measure 1),
    * `deriv (t ↦ t⁻²) = -2 t⁻³ ≤ -t⁻³ = -∫₀¹ (u t x)³ dx`, so the damping
      inequality holds on all of `(0,1)`,
    * yet `t⁻² → ∞` as `t → 0⁺`, so no uniform bound exists.

  This is NOT a defect of the fake-integral abstract counterexample
  (`not_forall_Lemma_2_7`): it is a genuine counterexample on the honest
  Lebesgue integral of the unit interval.  See `not_Lemma_2_7_intervalDomain`.

  The paper-faithful, TRUE form adds continuity of the Lᵖ-power map on the
  CLOSED interval `[0,T]` (which a classical solution with a continuous initial
  trace enjoys, its Lᵖ mass tending to `∫ u₀ᵖ < ∞` as `t → 0⁺`).  From closed
  continuity the extreme value theorem gives the uniform bound directly — the
  damping/Jensen machinery is not even needed once the endpoint is controlled.
  See `Lemma_2_7_intervalDomain_from_continuous_bound`.

  NEW FILE — no edits to existing files.
-/
import ShenWork.Paper2.Statements

open ShenWork.IntervalDomain
open MeasureTheory Set
open scoped Topology

noncomputable section

namespace ShenWork.Paper2.IntervalDomainLemma27Unconditional

/-! ### Elementary integral facts on the unit interval -/

/-- The unit-interval integral of a constant function equals that constant
(the domain has total measure `1`). -/
theorem intervalDomainIntegral_const (c : ℝ) :
    intervalDomainIntegral (fun _ => c) = c := by
  unfold intervalDomainIntegral
  rw [intervalIntegral.integral_congr (g := fun _ => c) ?_]
  · simp
  · intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    simp [intervalDomainLift, hx]

/-! ### The refuting datum -/

/-- The counterexample datum: `u(t,x) = t⁻¹`, constant in space. -/
def cexU : ℝ → intervalDomain.Point → ℝ := fun t _ => t⁻¹

/-- Every power-integral of the datum collapses to a scalar power of `t⁻¹`,
because the datum is spatially constant and the domain has measure `1`. -/
theorem cexU_integral (t r : ℝ) :
    intervalDomain.integral (fun x => (cexU t x) ^ r) = (t⁻¹) ^ r := by
  change intervalDomainIntegral (fun _ => (t⁻¹) ^ r) = (t⁻¹) ^ r
  exact intervalDomainIntegral_const _

/-- The Lᵖ mass map `τ ↦ ∫₀¹ (cexU τ)² = (τ⁻¹)²` has derivative `-2 t⁻³` at
every `t ≠ 0`. -/
theorem cexU_massDeriv {t : ℝ} (ht0 : 0 < t) :
    deriv (fun τ => intervalDomain.integral (fun x => (cexU τ x) ^ (2 : ℝ))) t =
      2 * (t⁻¹) ^ (2 - 1) * (-(t ^ 2)⁻¹) := by
  have ht_ne : t ≠ 0 := ne_of_gt ht0
  have hfun :
      (fun τ => intervalDomain.integral (fun x => (cexU τ x) ^ (2 : ℝ))) =
        (fun τ => (τ⁻¹) ^ (2 : ℕ)) := by
    funext τ
    rw [cexU_integral]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hfun]
  exact ((hasDerivAt_inv ht_ne).pow 2).deriv

/-- **Paper 2 Lemma 2.7 is FALSE on `intervalDomain`.**

The concrete datum `u(t,x) = t⁻¹` with `pExp = 2`, `C₁=C₂=C₃=0`, `C₄=1`,
`α=ε=1`, `T=1` satisfies the damping differential inequality on all of `(0,1)`
but has an Lᵖ mass `t⁻²` that is unbounded as `t → 0⁺`. -/
theorem not_Lemma_2_7_intervalDomain : ¬ Lemma_2_7 intervalDomain := by
  intro h
  -- Instantiate the universal statement at the refuting datum.
  have hbound :
      LpPowerBoundedBefore intervalDomain 2 1 cexU :=
    h cexU 1 2 0 0 0 1 1 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (le_rfl) ?_
  · -- Refute the uniform bound: `(t⁻¹)² = t⁻²` is unbounded near `0`.
    rcases hbound with ⟨C, hC⟩
    set R : ℝ := max 2 (C + 1) with hR
    have hR2 : (2 : ℝ) ≤ R := le_max_left _ _
    have hRpos : 0 < R := by linarith
    have hRC : C < R := lt_of_lt_of_le (by linarith : C < C + 1) (le_max_right _ _)
    -- choose the time `t = R⁻¹ ∈ (0,1)`.
    have ht0 : 0 < R⁻¹ := inv_pos.mpr hRpos
    have ht1 : R⁻¹ < 1 := by
      rw [inv_lt_one_iff₀]; right; linarith
    have hle := hC R⁻¹ ht0 ht1
    rw [cexU_integral, inv_inv] at hle
    -- `hle : R ^ (2:ℝ) ≤ C`, but `R ^ 2 ≥ R > C`.
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hle
    have hRsq : R < R ^ 2 := by nlinarith
    linarith
  · -- The damping differential inequality holds on `(0,1)`.
    intro t ht0 ht1
    -- `pExp + α - ε = 2`, `pExp + α = 3`; the `C₃` term drops (`C₃ = 0`).
    have hmass := cexU_massDeriv ht0
    have ht_ne : t ≠ 0 := ne_of_gt ht0
    -- Right-hand side: `- ∫₀¹ (cexU t)³ = -(t⁻¹)³`.
    have hcube : intervalDomain.integral (fun x => (cexU t x) ^ (2 + 1 : ℝ)) =
        (t⁻¹) ^ (3 : ℕ) := by
      rw [show (2 + 1 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, cexU_integral,
        Real.rpow_natCast]
    -- Assemble.
    simp only [zero_mul, add_zero, one_mul]
    rw [hmass, hcube]
    -- `2 * t⁻¹ * (-(t²)⁻¹) ≤ -(t⁻¹)³`, i.e. `-2 (t⁻¹)³ ≤ -(t⁻¹)³`.
    have hinv_pos : 0 < t⁻¹ := inv_pos.mpr ht0
    have hkey : 2 * (t⁻¹) ^ (2 - 1) * (-(t ^ 2)⁻¹) = -2 * (t⁻¹) ^ (3 : ℕ) := by
      rw [show (2 - 1 : ℕ) = 1 by norm_num, pow_one, ← inv_pow]
      ring
    rw [hkey]
    have hcube_pos : 0 ≤ (t⁻¹) ^ (3 : ℕ) := by positivity
    nlinarith [hcube_pos]

/-! ### The paper-faithful (true) form -/

/-- **Paper 2 Lemma 2.7 on `intervalDomain`, faithful form.**

Adding continuity of the Lᵖ-power mass map on the CLOSED interval `[0,T]`
(equivalently: the Lᵖ mass has a finite limit as `t → 0⁺`, as a classical
solution with continuous initial trace does), the uniform bound follows from
the extreme value theorem on the compact `[0,T]`.  The damping differential
inequality is then vestigial (it appears as an unused hypothesis, kept for
statement fidelity), exactly as in `unitPointDomain.Lemma_2_7_from_continuous_bound`. -/
theorem Lemma_2_7_intervalDomain_from_continuous_bound
    (u : ℝ → intervalDomain.Point → ℝ)
    (T pExp C1 C2 C3 C4 eps alpha : ℝ)
    (hT : 0 < T) (_hpExp : 1 < pExp)
    (_hC1 : 0 ≤ C1) (_hC2 : 0 ≤ C2) (_hC3 : 0 ≤ C3) (_hC4 : 0 < C4)
    (_heps : 0 < eps) (_heps_le : eps ≤ alpha)
    (hcont :
      ContinuousOn
        (fun t => intervalDomain.integral (fun x => (u t x) ^ pExp))
        (Set.Icc 0 T))
    (_hineq : ∀ t, 0 < t → t < T →
      deriv (fun τ => intervalDomain.integral (fun x => (u τ x) ^ pExp)) t +
          C3 * intervalDomain.integral
            (fun x => (u t x) ^ (pExp + alpha - eps)) ≤
        C1 + C2 * intervalDomain.integral (fun x => (u t x) ^ pExp) -
          C4 * intervalDomain.integral (fun x => (u t x) ^ (pExp + alpha))) :
    LpPowerBoundedBefore intervalDomain pExp T u := by
  have hne : (Set.Icc (0 : ℝ) T).Nonempty := ⟨0, Set.left_mem_Icc.mpr hT.le⟩
  obtain ⟨t₀, ht₀, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hcont
  refine ⟨intervalDomain.integral (fun x => (u t₀ x) ^ pExp), ?_⟩
  intro t ht_pos ht_lt
  have ht_mem : t ∈ Set.Icc (0 : ℝ) T := ⟨ht_pos.le, ht_lt.le⟩
  exact hmax ht_mem

end ShenWork.Paper2.IntervalDomainLemma27Unconditional
