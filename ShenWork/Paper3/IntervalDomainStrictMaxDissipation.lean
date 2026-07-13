import ShenWork.Paper3.IntervalDomainStrictMaxInterior
import ShenWork.Paper3.IntervalDomainStrictMaxBoundaryLeft
import ShenWork.Paper3.IntervalDomainStrictMaxBoundaryRight

open ShenWork.IntervalDomain ShenWork.Paper2
open Set

namespace ShenWork.Paper3

noncomputable section

/-- The strict signal term is retained at every spatial argmax, including both
Neumann boundary points. -/
theorem intervalDomain_max_point_strict_signal
    {p : CM2Params} {T t q : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    {x : intervalDomainPoint}
    (hχ : p.χ₀ ≤ 0)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hmax : ∀ y, u t y ≤ u t x)
    (hsignal : q ≤
      p.ν * (intervalDomainLift (u t) x.1) ^ p.γ / p.μ -
        intervalDomainLift (v t) x.1) :
    intervalDomain.timeDeriv u t x ≤
      intervalDomainLift (u t) x.1 *
          (p.a - p.b * (intervalDomainLift (u t) x.1) ^ p.α) +
        p.χ₀ *
          (intervalDomainLift (u t) x.1 *
            ((1 + intervalDomainLift (v t) x.1) ^ (-p.β) * (p.μ * q))) := by
  rcases lt_or_eq_of_le x.2.1 with h0 | h0
  · rcases lt_or_eq_of_le x.2.2 with h1 | h1
    · exact intervalDomain_interior_max_point_strict_signal
        hχ hsol ht0 htT ⟨h0, h1⟩ hmax hsignal
    · have hx11 : x.1 = 1 := h1
      have hmaxlift : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
          intervalDomainLift (u t) y ≤ intervalDomainLift (u t) 1 := by
        intro y hy
        have hlift1 : intervalDomainLift (u t) 1 = u t x := by
          rw [intervalDomainLift,
            dif_pos (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 from
              ⟨zero_le_one, le_rfl⟩)]
          exact congrArg (u t) (Subtype.ext hx11.symm)
        rw [hlift1, intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hy)]
        exact hmax _
      have hs1 : q ≤ p.ν * (intervalDomainLift (u t) 1) ^ p.γ / p.μ -
          intervalDomainLift (v t) 1 := by simpa [hx11] using hsignal
      have hbmr := intervalDomain_boundary_max_point_right_strict_signal
        hχ hsol ht0 htT hmaxlift hs1
      have htd : intervalDomain.timeDeriv u t x =
          deriv (fun r => intervalDomainLift (u r) 1) t := by
        show deriv (fun s => u s x) t =
          deriv (fun r => intervalDomainLift (u r) 1) t
        congr 1
        funext r
        rw [intervalDomainLift,
          dif_pos (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 from
            ⟨zero_le_one, le_rfl⟩)]
        exact (congrArg (u r) (Subtype.ext hx11.symm)).symm
      rw [hx11, htd]
      exact hbmr
  · have hx10 : x.1 = 0 := h0.symm
    have hmaxlift : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
        intervalDomainLift (u t) y ≤ intervalDomainLift (u t) 0 := by
      intro y hy
      have hlift0 : intervalDomainLift (u t) 0 = u t x := by
        rw [intervalDomainLift,
          dif_pos (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 from
            ⟨le_rfl, zero_le_one⟩)]
        exact congrArg (u t) (Subtype.ext hx10.symm)
      rw [hlift0, intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hy)]
      exact hmax _
    have hs0 : q ≤ p.ν * (intervalDomainLift (u t) 0) ^ p.γ / p.μ -
        intervalDomainLift (v t) 0 := by simpa [hx10] using hsignal
    have hbml := intervalDomain_boundary_max_point_left_strict_signal
      hχ hsol ht0 htT hmaxlift hs0
    have htd : intervalDomain.timeDeriv u t x =
        deriv (fun r => intervalDomainLift (u r) 0) t := by
      show deriv (fun s => u s x) t =
        deriv (fun r => intervalDomainLift (u r) 0) t
      congr 1
      funext r
      rw [intervalDomainLift,
        dif_pos (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 from
          ⟨le_rfl, zero_le_one⟩)]
      exact (congrArg (u r) (Subtype.ext hx10.symm)).symm
    rw [hx10, htd]
    exact hbml

/-- Uniform positive dissipation constant for the repulsive minimal model on
a maximum window bounded by `B`. -/
def intervalDomainMinimalMaxDissipationConstant
    (p : CM2Params) (uStar d B : ℝ) : ℝ :=
  (-p.χ₀) *
    ((uStar + d) *
      (1 + p.ν * B ^ p.γ / p.μ) ^ (-p.β) *
      (p.μ * intervalDomainSignalGapConstant p uStar d))

theorem intervalDomainMinimalMaxDissipationConstant_pos
    (p : CM2Params) {uStar d B : ℝ}
    (hχ : p.χ₀ < 0) (huStar : 0 < uStar) (hd : 0 < d)
    (hB : uStar + d ≤ B) :
    0 < intervalDomainMinimalMaxDissipationConstant p uStar d B := by
  have hbase : 0 < 1 + p.ν * B ^ p.γ / p.μ := by
    have hB0 : 0 ≤ B := le_trans (by linarith) hB
    have : 0 ≤ p.ν * B ^ p.γ / p.μ :=
      div_nonneg (mul_nonneg p.hν.le (Real.rpow_nonneg hB0 _)) p.hμ.le
    linarith
  unfold intervalDomainMinimalMaxDissipationConstant
  exact mul_pos (neg_pos.mpr hχ)
    (mul_pos
      (mul_pos (by linarith)
        (Real.rpow_pos_of_pos hbase _))
      (mul_pos p.hμ (intervalDomainSignalGapConstant_pos p huStar hd)))

/-- At every spatial argmax of a mass-constrained solution of the minimal
model with strictly repulsive sensitivity, any fixed excess `d` above the
mean forces a uniform negative time slope. -/
theorem intervalDomain_minimal_argmax_uniform_strict_slope
    {p : CM2Params} {T t uStar d B : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    {x : intervalDomainPoint}
    (ha : p.a = 0) (hb : p.b = 0) (hχ : p.χ₀ < 0)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (huStar : 0 < uStar) (hd : 0 < d)
    (hmass : intervalDomain.integral (u t) = uStar)
    (hmax : ∀ y, u t y ≤ u t x)
    (hMgap : uStar + d ≤ intervalDomainLift (u t) x.1)
    (hMB : intervalDomainLift (u t) x.1 ≤ B) :
    intervalDomain.timeDeriv u t x ≤
      -intervalDomainMinimalMaxDissipationConstant p uStar d B := by
  let M : ℝ := intervalDomainLift (u t) x.1
  have hliftx : intervalDomainLift (u t) x.1 = u t x := by
    simp only [intervalDomainLift]
    exact (dif_pos x.2).trans
      (congrArg (u t) (Subtype.coe_eta x x.2))
  have hvliftx : intervalDomainLift (v t) x.1 = v t x := by
    simp only [intervalDomainLift]
    exact (dif_pos x.2).trans
      (congrArg (v t) (Subtype.coe_eta x x.2))
  have hupper : ∀ z : intervalDomainPoint, u t z ≤ M := by
    intro z
    dsimp [M]
    rw [hliftx]
    exact hmax z
  have hsignalAll := intervalDomain_solution_signalGapConstant_le
    p hsol ⟨ht0, htT⟩ huStar hd hmass hupper hMgap
  have hsignal := hsignalAll x.1 x.2
  have hslope := intervalDomain_max_point_strict_signal
    hχ.le hsol ht0 htT hmax hsignal
  have hqpos := intervalDomainSignalGapConstant_pos p huStar hd
  have hMpos : 0 < M := lt_of_lt_of_le (by linarith) hMgap
  have hBnonneg : 0 ≤ B := le_trans hMpos.le hMB
  have hMpow : M ^ p.γ ≤ B ^ p.γ :=
    Real.rpow_le_rpow hMpos.le hMB p.hγ.le
  have hv_nonneg : 0 ≤ intervalDomainLift (v t) x.1 := by
    rw [hvliftx]
    exact hsol.v_nonneg ht0 htT
  have hv_upper : intervalDomainLift (v t) x.1 ≤
      p.ν * B ^ p.γ / p.μ := by
    have hsignal0 : 0 ≤ p.ν * M ^ p.γ / p.μ -
        intervalDomainLift (v t) x.1 := le_trans hqpos.le hsignal
    have hmul : p.ν * M ^ p.γ ≤ p.ν * B ^ p.γ :=
      mul_le_mul_of_nonneg_left hMpow p.hν.le
    have hdiv : p.ν * M ^ p.γ / p.μ ≤
        p.ν * B ^ p.γ / p.μ :=
      div_le_div_of_nonneg_right hmul p.hμ.le
    linarith
  have hbaseV : 0 < 1 + intervalDomainLift (v t) x.1 := by linarith
  have hbase_le : 1 + intervalDomainLift (v t) x.1 ≤
      1 + p.ν * B ^ p.γ / p.μ := by linarith
  have hrpow :
      (1 + p.ν * B ^ p.γ / p.μ) ^ (-p.β) ≤
        (1 + intervalDomainLift (v t) x.1) ^ (-p.β) :=
    Real.rpow_le_rpow_of_nonpos hbaseV hbase_le (neg_nonpos.mpr p.hβ)
  have hfactor :
      (uStar + d) * (1 + p.ν * B ^ p.γ / p.μ) ^ (-p.β) ≤
        M * (1 + intervalDomainLift (v t) x.1) ^ (-p.β) := by
    exact mul_le_mul hMgap hrpow
      (Real.rpow_pos_of_pos (lt_of_lt_of_le hbaseV hbase_le) _).le hMpos.le
  have hμq : 0 ≤ p.μ * intervalDomainSignalGapConstant p uStar d :=
    (mul_pos p.hμ hqpos).le
  have hactual :
      (uStar + d) * (1 + p.ν * B ^ p.γ / p.μ) ^ (-p.β) *
          (p.μ * intervalDomainSignalGapConstant p uStar d) ≤
        M * (1 + intervalDomainLift (v t) x.1) ^ (-p.β) *
          (p.μ * intervalDomainSignalGapConstant p uStar d) :=
    mul_le_mul_of_nonneg_right hfactor hμq
  have hχmul := mul_le_mul_of_nonpos_left hactual hχ.le
  rw [ha, hb] at hslope
  simp only [zero_mul, sub_zero, mul_zero] at hslope
  dsimp [M] at hactual hχmul
  unfold intervalDomainMinimalMaxDissipationConstant
  nlinarith

#print axioms intervalDomain_max_point_strict_signal
#print axioms intervalDomainMinimalMaxDissipationConstant_pos
#print axioms intervalDomain_minimal_argmax_uniform_strict_slope

end

end ShenWork.Paper3
