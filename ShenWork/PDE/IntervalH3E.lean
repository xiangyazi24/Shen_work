import ShenWork.PDE.IntervalDuhamelSourceTimeC2Coeff
import ShenWork.Paper2.IntervalChiNegResolverC2HeatFactor
import ShenWork.Paper2.IntervalChiNegResolverC2RestartAudit

/-!
Lane H3E audit module.

This file keeps the route-(ii) heat-factor audit and the route-(i) third
spatial heat-tail estimate at a narrow integration surface.
-/

namespace ShenWork

namespace PDE

noncomputable section

def unitIntervalCosineHeatThirdPointWeight
    (t x : ℝ) (n : ℕ) : ℝ :=
  -unitIntervalCosineEigenvalue n *
    unitIntervalCosineHeatGradientPointWeight t x n

def unitIntervalCosineHeatCubeTail (t : ℝ) (n : ℕ) : ℝ :=
  unitIntervalCosineEigenvalue n *
    (unitIntervalCosineEigenvalue n *
      (unitIntervalCosineEigenvalue n *
        Real.exp (-t * unitIntervalCosineEigenvalue n)))

theorem h3e_route_i_cube_tail_summable {t : ℝ} (ht : 0 < t) :
    Summable (fun n => unitIntervalCosineHeatCubeTail t n) := by
  simpa [unitIntervalCosineHeatCubeTail] using
    ShenWork.IntervalResolverSpectralTimeC2.eigenvalue_cube_mul_exp_summable ht

theorem h3e_route_i_third_weight_abs_le_cube_tail
    (t x : ℝ) (n : ℕ) :
    |unitIntervalCosineHeatThirdPointWeight t x n| ≤
      unitIntervalCosineHeatCubeTail t n := by
  by_cases hn : n = 0
  · subst n
    simp [unitIntervalCosineHeatThirdPointWeight,
      unitIntervalCosineHeatCubeTail, unitIntervalCosineEigenvalue,
      unitIntervalCosineHeatGradientPointWeight]
  · have hnpos_real : 0 < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hn
    have hn_ge_one : (1 : ℝ) ≤ n := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
    have hpi_ge_one : (1 : ℝ) ≤ Real.pi := by
      linarith [Real.pi_gt_three]
    let freq : ℝ := (n : ℝ) * Real.pi
    let lam : ℝ := unitIntervalCosineEigenvalue n
    have hfreq_nonneg : 0 ≤ freq := by
      dsimp [freq]
      positivity
    have hfreq_ge_one : (1 : ℝ) ≤ freq := by
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ (n : ℝ) * Real.pi :=
          mul_le_mul hn_ge_one hpi_ge_one (by norm_num)
            (by exact_mod_cast Nat.zero_le n)
        _ = freq := rfl
    have hfreq_cube_le : freq ^ 3 ≤ freq ^ 6 := by
      have hcube_nonneg : 0 ≤ freq ^ 3 := pow_nonneg hfreq_nonneg 3
      have hcube_ge_one : (1 : ℝ) ≤ freq ^ 3 :=
        one_le_pow₀ hfreq_ge_one
      calc freq ^ 3 = freq ^ 3 * 1 := by ring
        _ ≤ freq ^ 3 * freq ^ 3 :=
          mul_le_mul_of_nonneg_left hcube_ge_one hcube_nonneg
        _ = freq ^ 6 := by ring
    have hlam_eq : lam = freq ^ 2 := by
      dsimp [lam, freq, unitIntervalCosineEigenvalue]
    have hlam_nonneg : 0 ≤ lam := by
      rw [hlam_eq]
      positivity
    have hgrad_abs :
        |unitIntervalCosineHeatGradientPointWeight t x n| ≤
          freq * Real.exp (-t * lam) := by
      dsimp [unitIntervalCosineHeatGradientPointWeight, lam, freq]
      rw [abs_mul, abs_mul, abs_neg,
        abs_of_nonneg (Real.exp_nonneg _),
        abs_of_nonneg hfreq_nonneg]
      calc Real.exp (-t * unitIntervalCosineEigenvalue n) *
            (freq * |Real.sin (freq * x)|)
          ≤ Real.exp (-t * unitIntervalCosineEigenvalue n) *
              (freq * 1) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _)
                hfreq_nonneg)
              (Real.exp_nonneg _)
        _ = freq * Real.exp (-t * lam) := by
            dsimp [lam]
            ring
    have hthird_abs :
        |unitIntervalCosineHeatThirdPointWeight t x n| ≤
          lam * (freq * Real.exp (-t * lam)) := by
      dsimp [unitIntervalCosineHeatThirdPointWeight, lam]
      rw [abs_mul, abs_neg, abs_of_nonneg hlam_nonneg]
      exact mul_le_mul_of_nonneg_left hgrad_abs hlam_nonneg
    calc |unitIntervalCosineHeatThirdPointWeight t x n|
        ≤ lam * (freq * Real.exp (-t * lam)) := hthird_abs
      _ = freq ^ 3 * Real.exp (-t * lam) := by
          rw [hlam_eq]
          ring
      _ ≤ freq ^ 6 * Real.exp (-t * lam) :=
          mul_le_mul_of_nonneg_right hfreq_cube_le (Real.exp_nonneg _)
      _ = unitIntervalCosineHeatCubeTail t n := by
          have hcube_eq :
              unitIntervalCosineHeatCubeTail t n =
                freq ^ 6 * Real.exp (-t * lam) := by
            dsimp [unitIntervalCosineHeatCubeTail, lam]
            have heig_eq :
                unitIntervalCosineEigenvalue n = freq ^ 2 := by
              simpa [lam] using hlam_eq
            rw [heig_eq]
            ring_nf
          rw [hcube_eq]

theorem h3e_route_i_third_terms_summable_of_bounded
    {t M : ℝ} (ht : 0 < t) {a : ℕ → ℝ}
    (hM : ∀ n, |a n| ≤ M) (x : ℝ) :
    Summable
      (fun n => unitIntervalCosineHeatThirdPointWeight t x n * a n) := by
  refine Summable.of_norm_bounded
    ((h3e_route_i_cube_tail_summable ht).mul_right M) ?_
  intro n
  have htail_nonneg : 0 ≤ unitIntervalCosineHeatCubeTail t n := by
    have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
      dsimp [unitIntervalCosineEigenvalue]
      exact sq_nonneg ((n : ℝ) * Real.pi)
    dsimp [unitIntervalCosineHeatCubeTail]
    exact mul_nonneg hlam
      (mul_nonneg hlam (mul_nonneg hlam (Real.exp_nonneg _)))
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul
    (h3e_route_i_third_weight_abs_le_cube_tail t x n)
    (hM n) (abs_nonneg _) htail_nonneg

def h3e_route_ii_heat_factor_fields
    {ε M : ℝ} {a₀ : ℕ → ℝ} (hε : 0 < ε) (hM : 0 ≤ M)
    (ha₀ : ∀ n, |a₀ n| ≤ M) :
    ShenWork.Paper2.PicardLimitK1C2Coeff.SourceC2CoeffFields
      (ShenWork.Paper2.PicardLimitK1C2Heat.shiftedHeatCoeff_timeC1
        hε hM ha₀) :=
  ShenWork.Paper2.ChiNegResolverC2HeatFactor.sourceC2CoeffFields_of_heatFactor
    hε hM ha₀

theorem h3e_route_ii_target_shift_pos
    {p : CM2Params}
    {u : ℝ → ShenWork.IntervalDomain.intervalDomainPoint → ℝ}
    {T σ : ℝ}
    (L : ShenWork.Paper2.PicardLimitK1.LocalRestart p u T σ) :
    0 < σ - L.τ :=
  ShenWork.Paper2.ChiNegResolverC2RestartAudit.localRestart_target_shift_pos
    L

theorem h3e_route_ii_source_fields_target_raw_aC
    {p : CM2Params}
    {u : ℝ → ShenWork.IntervalDomain.intervalDomainPoint → ℝ}
    {T σ : ℝ}
    (L : ShenWork.Paper2.PicardLimitK1.LocalRestart p u T σ)
    (F : ShenWork.Paper2.PicardLimitK1C2Coeff.SourceC2CoeffFields L.srcC) :
    (ShenWork.Paper2.PicardLimitK1C2Coeff.LocalRestartC2.ofSourceFields
      L F).srcC2.toTimeC1 = L.srcC :=
  ShenWork.Paper2.ChiNegResolverC2RestartAudit.ofSourceFields_targets_raw_aC
    L F

end

end PDE

end ShenWork
