import ShenWork.PaperOne.WholeLineMildMap
import ShenWork.Paper2.IntervalDomainL2UniquenessCertificate

open MeasureTheory
noncomputable section
namespace ShenWork.PaperOne
def wholeLineUpperExcessEnergy (U : ℝ → ℝ → ℝ) (hi t : ℝ) : ℝ :=
  ∫ x : ℝ, (max (U t x - hi) 0) ^ 2
def wholeLineLowerDeficitEnergy (U : ℝ → ℝ → ℝ) (lo t : ℝ) : ℝ :=
  ∫ x : ℝ, (max (lo - U t x) 0) ^ 2
theorem wholeLineReaction_const_nonpos_of_one_le (p : CMParams) {c : ℝ}
    (hc : 1 ≤ c) : wholeLineReaction p (fun _ : ℝ => c) 0 ≤ 0 := by
  have hpow : 1 ≤ c ^ p.α := Real.one_le_rpow hc (by linarith [p.hα])
  have hfac : 1 - c ^ p.α ≤ 0 := sub_nonpos.mpr hpow
  simpa [wholeLineReaction] using mul_nonpos_of_nonneg_of_nonpos (le_trans zero_le_one hc) hfac
theorem wholeLineReaction_const_nonneg_of_Icc
    (p : CMParams) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    0 ≤ wholeLineReaction p (fun _ : ℝ => c) 0 := by
  have hpow : c ^ p.α ≤ 1 := Real.rpow_le_one hc0 hc1 (by linarith [p.hα])
  have hfac : 0 ≤ 1 - c ^ p.α := sub_nonneg.mpr hpow
  simpa [wholeLineReaction] using mul_nonneg hc0 hfac
theorem wholeLineFlux_const_eq_zero (p : CMParams) {c : ℝ}
    (hc0 : 0 ≤ c) (x : ℝ) : wholeLineFlux p (fun _ : ℝ => c) x = 0 := by
  have hcγ : 0 ≤ c ^ p.γ := Real.rpow_nonneg hc0 _
  have hres : wholeLineResolvent (fun _ : ℝ => c ^ p.γ) = fun _ : ℝ => c ^ p.γ := by
    funext z
    rw [wholeLineResolvent_eq_Psi]
    exact Psi_const hcγ z
  unfold wholeLineFlux
  change c ^ p.m * deriv (wholeLineResolvent (fun _ : ℝ => c ^ p.γ)) x = 0
  rw [hres]
  simp
structure WholeLineBarrierEnergyFrontier (E : ℝ → ℝ) (T : ℝ) where
  Eprime : ℝ → ℝ
  K : ℝ
  K_nonneg : 0 ≤ K
  nonneg : ∀ t, 0 < t → t < T → 0 ≤ E t
  cont : ∀ s t, 0 < s → s ≤ t → t < T → ContinuousOn E (Set.Icc s t)
  diffIneq : ∀ t, 0 < t → t < T →
    HasDerivWithinAt E (Eprime t) (Set.Ici t) t ∧ Eprime t ≤ K * E t
  initial_vanishes : ∀ ε > 0, ∃ δ > 0, ∀ s, 0 < s → s < δ → s < T → E s < ε
theorem wholeLineBarrierEnergy_eq_zero {E : ℝ → ℝ} {T t : ℝ}
    (H : WholeLineBarrierEnergyFrontier E T) (ht0 : 0 < t) (htT : t < T) : E t = 0 := by
  have hEt_nonneg : 0 ≤ E t := H.nonneg t ht0 htT
  by_cases hEt_zero : E t = 0
  · exact hEt_zero
  have hEt_pos : 0 < E t := lt_of_le_of_ne hEt_nonneg (Ne.symm hEt_zero)
  have hExp_pos : 0 < Real.exp (H.K * t) := Real.exp_pos _
  set ε : ℝ := E t / (2 * Real.exp (H.K * t)) with hε
  have hε_pos : 0 < ε := div_pos hEt_pos (mul_pos (by norm_num) hExp_pos)
  obtain ⟨δ, hδ_pos, hδ⟩ := H.initial_vanishes ε hε_pos
  set s : ℝ := min (δ / 2) (t / 2) with hs
  have hs_pos : 0 < s := lt_min (by linarith) (by linarith)
  have hs_lt_δ : s < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hs_lt_t : s < t := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hs_le_t : s ≤ t := le_of_lt hs_lt_t
  have hsT : s < T := lt_trans hs_lt_t htT
  have hEs_nonneg : 0 ≤ E s := H.nonneg s hs_pos hsT
  have hEs_lt : E s < ε := hδ s hs_pos hs_lt_δ hsT
  have hEt_le : E t ≤ E s * Real.exp (H.K * (t - s)) := by
    refine ShenWork.Paper2.intervalDomainL2_gronwall_exp_of_diffIneq
      (E' := H.Eprime) hs_le_t (H.cont s t hs_pos hs_le_t htT) ?_ ?_
    · intro τ hτ
      exact (H.diffIneq τ (lt_of_lt_of_le hs_pos hτ.1) (lt_trans hτ.2 htT)).1
    · intro τ hτ
      exact (H.diffIneq τ (lt_of_lt_of_le hs_pos hτ.1) (lt_trans hτ.2 htT)).2
  have hExp_le : Real.exp (H.K * (t - s)) ≤ Real.exp (H.K * t) := by
    exact Real.exp_le_exp.mpr (by nlinarith [H.K_nonneg, hs_pos])
  have hEt_le' : E t ≤ E s * Real.exp (H.K * t) :=
    le_trans hEt_le (mul_le_mul_of_nonneg_left hExp_le hEs_nonneg)
  have hmul_lt : E s * Real.exp (H.K * t) < ε * Real.exp (H.K * t) :=
    mul_lt_mul_of_pos_right hEs_lt hExp_pos
  have hε_mul : ε * Real.exp (H.K * t) = E t / 2 := by
    rw [hε]; field_simp [ne_of_gt hExp_pos]
  linarith
structure WholeLineConstantBarrierEnergyMethod
    (p : CMParams) (T : ℝ) (u0 : ℝ → ℝ) (U V : ℝ → ℝ → ℝ) (lo hi : ℝ) where
  solution : IsClassicalSolution p T U V
  upper : WholeLineBarrierEnergyFrontier (wholeLineUpperExcessEnergy U hi) T
  lower : WholeLineBarrierEnergyFrontier (wholeLineLowerDeficitEnergy U lo) T
  upper_zero_controls : ∀ t, 0 < t → t < T →
    wholeLineUpperExcessEnergy U hi t = 0 → ∀ x, U t x ≤ hi
  lower_zero_controls : ∀ t, 0 < t → t < T →
    wholeLineLowerDeficitEnergy U lo t = 0 → ∀ x, lo ≤ U t x
theorem wholeLine_constantBarrier_trapping_via_energy
    {p : CMParams} {T : ℝ} {u0 : ℝ → ℝ} {U V : ℝ → ℝ → ℝ} {lo hi : ℝ}
    (_hχ : p.χ ≤ 0) (_hlo0 : 0 ≤ lo) (_hlo1 : lo ≤ 1) (_hhi1 : 1 ≤ hi)
    (_hu0lo : ∀ x, lo ≤ u0 x) (_hu0hi : ∀ x, u0 x ≤ hi)
    (H : WholeLineConstantBarrierEnergyMethod p T u0 U V lo hi) :
    ∀ t, 0 < t → t < T → ∀ x, lo ≤ U t x ∧ U t x ≤ hi := by
  intro t ht0 htT x
  have hupper := wholeLineBarrierEnergy_eq_zero H.upper ht0 htT
  have hlower := wholeLineBarrierEnergy_eq_zero H.lower ht0 htT
  exact ⟨H.lower_zero_controls t ht0 htT hlower x,
    H.upper_zero_controls t ht0 htT hupper x⟩
#print axioms wholeLine_constantBarrier_trapping_via_energy
end ShenWork.PaperOne
