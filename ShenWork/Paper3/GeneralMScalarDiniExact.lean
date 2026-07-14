import ShenWork.Paper3.GeneralMScalarDiniComparison

open Filter Topology
open ShenWork.Paper2

namespace ShenWork.Paper3

noncomputable section

def generalMScalarDelta (p : CM2Params) : ℝ := min (p.m - 1) p.α

def generalMScalarLossCoeff (p : CM2Params) : ℝ :=
  p.b + generalMChemLoss p

def generalMScalarThreshold (p : CM2Params) : ℝ :=
  (min 1 (p.a / generalMScalarLossCoeff p)) ^
    (1 / generalMScalarDelta p)

theorem generalMScalarDelta_pos {p : CM2Params} (hm : 1 < p.m) :
    0 < generalMScalarDelta p := by
  exact lt_min (sub_pos.mpr hm) p.hα

theorem generalMScalar_inv_delta {p : CM2Params} (hm : 1 < p.m) :
    1 / generalMScalarDelta p =
      max (1 / (p.m - 1)) (1 / p.α) := by
  by_cases hle : p.m - 1 ≤ p.α
  · have hinv : 1 / p.α ≤ 1 / (p.m - 1) :=
      one_div_le_one_div_of_le (sub_pos.mpr hm) hle
    rw [generalMScalarDelta, min_eq_left hle, max_eq_left hinv]
  · have hle' : p.α ≤ p.m - 1 := le_of_not_ge hle
    have hinv : 1 / (p.m - 1) ≤ 1 / p.α :=
      one_div_le_one_div_of_le p.hα hle'
    rw [generalMScalarDelta, min_eq_right hle', max_eq_right hinv]

theorem generalMScalarThreshold_eq_theorem21Part3LowerU
    {p : CM2Params} (hm : 1 < p.m) :
    generalMScalarThreshold p = theorem21Part3LowerU p := by
  rw [generalMScalarThreshold, theorem21Part3LowerU,
    generalMScalarLossCoeff, generalMScalar_inv_delta hm]
  rfl

theorem generalMScalarLossCoeff_pos
    {p : CM2Params} (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hβ : 1 ≤ p.β) :
    0 < generalMScalarLossCoeff p := by
  have hTheta : 0 < Theta_beta (p.β - 1) :=
    Theta_beta_pos_of_nonneg (by linarith)
  have hC : 0 < generalMChemLoss p := by
    exact mul_pos (mul_pos hχ0 p.hμ) hTheta
  exact add_pos hb hC

theorem generalM_logistic_dominates_single_power_on_unit
    {p : CM2Params} (hm : 1 < p.m) (hχ0 : 0 < p.χ₀)
    (hβ : 1 ≤ p.β) {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) :
    p.a * y - generalMScalarLossCoeff p *
        y ^ (1 + generalMScalarDelta p) ≤
      generalMLogisticRhs p y := by
  have hδα : generalMScalarDelta p ≤ p.α := min_le_right _ _
  have hδm : generalMScalarDelta p ≤ p.m - 1 := min_le_left _ _
  have hpowα : y ^ (1 + p.α) ≤ y ^ (1 + generalMScalarDelta p) :=
    Real.rpow_le_rpow_of_exponent_ge hy hy1 (by linarith)
  have hpowm : y ^ p.m ≤ y ^ (1 + generalMScalarDelta p) :=
    Real.rpow_le_rpow_of_exponent_ge hy hy1 (by linarith)
  have hTheta : 0 < Theta_beta (p.β - 1) :=
    Theta_beta_pos_of_nonneg (by linarith)
  have hC : 0 ≤ generalMChemLoss p :=
    (mul_pos (mul_pos hχ0 p.hμ) hTheta).le
  have hbpow := mul_le_mul_of_nonneg_left hpowα p.hb
  have hCpow := mul_le_mul_of_nonneg_left hpowm hC
  simp only [generalMScalarLossCoeff, generalMLogisticRhs] at ⊢
  nlinarith

/-- Exact liminf threshold for the faithful two-loss scalar minimum equation. -/
theorem generalM_liminf_ge_of_RightLowerDiniGE
    {p : CM2Params} {z : ℝ → ℝ} {T0 : ℝ}
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : 1 < p.m) (hβ : 1 ≤ p.β)
    (hcont : ∀ T, T0 ≤ T → ContinuousOn z (Set.Icc T0 T))
    (hD : RightLowerDiniGE z (generalMLogisticRhs p) (Set.Ioi 0))
    (hT0 : 0 < T0) (hz0 : 0 < z T0)
    (hcobdd : IsCoboundedUnder GE.ge atTop z) :
    theorem21Part3LowerU p ≤ Filter.liminf z atTop := by
  let d : ℝ := generalMScalarDelta p
  let B : ℝ := generalMScalarLossCoeff p
  let s : ℝ := min 1 (p.a / B)
  let θ : ℝ := s ^ (1 / d)
  have hd : 0 < d := by simpa [d] using generalMScalarDelta_pos hm
  have hB : 0 < B := by
    simpa [B] using generalMScalarLossCoeff_pos hb hχ0 hβ
  have hs : 0 < s := by
    exact lt_min zero_lt_one (div_pos ha hB)
  have hs1 : s ≤ 1 := min_le_left _ _
  have hsratio : s ≤ p.a / B := min_le_right _ _
  have hθ : 0 < θ := Real.rpow_pos_of_pos hs _
  have hθ1 : θ ≤ 1 := by
    have h := Real.rpow_le_rpow hs.le hs1 (one_div_nonneg.mpr hd.le)
    simpa [θ] using h
  have hθpow : θ ^ d = s := by
    dsimp [θ]
    rw [← Real.rpow_mul hs.le, one_div_mul_cancel (ne_of_gt hd),
      Real.rpow_one]
  have hsubthreshold : ∀ ell : ℝ, 0 < ell → ell < θ →
      ell ≤ Filter.liminf z atTop := by
    intro ell hell hellθ
    have hell1 : ell ≤ 1 := (le_of_lt hellθ).trans hθ1
    have hellpow : ell ^ d < s := by
      have h := Real.rpow_lt_rpow hell.le hellθ hd
      rwa [hθpow] at h
    have hBs_le_a : B * s ≤ p.a := by
      have hmul := mul_le_mul_of_nonneg_left hsratio hB.le
      have hcancel : B * (p.a / B) = p.a := by
        field_simp [ne_of_gt hB]
      rwa [hcancel] at hmul
    have hBell_lt_a : B * ell ^ d < p.a := by
      have hmul := mul_lt_mul_of_pos_left hellpow hB
      exact hmul.trans_le hBs_le_a
    let q : CM2Params :=
      { N := p.N, hN := p.hN, α := d, γ := p.γ, m := p.m,
        μ := p.μ, ν := p.ν, χ₀ := p.χ₀, a := p.a, b := B, β := p.β,
        hα := hd, hγ := p.hγ, hm := p.hm, hμ := p.hμ, hν := p.hν,
        ha := ha.le, hb := hB.le, hβ := p.hβ }
    let qell : CM2Params :=
      { N := p.N, hN := p.hN, α := d, γ := p.γ, m := p.m,
        μ := p.μ, ν := p.ν, χ₀ := p.χ₀,
        a := B * ell ^ d, b := B, β := p.β,
        hα := hd, hγ := p.hγ, hm := p.hm, hμ := p.hμ, hν := p.hν,
        ha := (mul_pos hB (Real.rpow_pos_of_pos hell _)).le,
        hb := hB.le, hβ := p.hβ }
    let eta : ℝ := p.a - B * ell ^ d
    have heta : 0 < eta := by dsimp [eta]; linarith
    have hqella : 0 < qell.a := by
      dsimp [qell]
      exact mul_pos hB (Real.rpow_pos_of_pos hell _)
    have hqellb : 0 < qell.b := by simpa [qell] using hB
    have hcarry : (qell.a / qell.b) ^ (1 / qell.α) = ell := by
      have hdiv : qell.a / qell.b = ell ^ d := by
        dsimp [qell]
        field_simp [ne_of_gt hB]
      rw [hdiv]
      change (ell ^ d) ^ (1 / d) = ell
      rw [← Real.rpow_mul hell.le, one_div, mul_inv_cancel₀ (ne_of_gt hd),
        Real.rpow_one]
    let y0 : ℝ := min (z T0) ell
    have hy0 : 0 < y0 := lt_min hz0 hell
    have hy0le : y0 ≤ (qell.a / qell.b) ^ (1 / qell.α) := by
      rw [hcarry]
      exact min_le_right _ _
    have hinit : y0 ≤ z T0 := min_le_left _ _
    have hlocal : ∀ y, 0 < y → y ≤ 1 →
        q.a * y - q.b * y ^ (1 + q.α) ≤ generalMLogisticRhs p y := by
      intro y hy hyone
      simpa [q, d, B] using
        generalM_logistic_dominates_single_power_on_unit hm hχ0 hβ hy hyone
    have hlim := local_logistic_liminf_ge_of_RightLowerDiniGE
      (q := q) (qη := qell) (z := z) (F := generalMLogisticRhs p)
      (η := eta) (y0 := y0) (T0 := T0)
      hqella hqellb heta (by simp [qell, q, eta])
      (by simp [qell, q]) (by simp [qell, q])
      (by rw [hcarry]; exact hell1) hy0 hy0le hlocal hcont hD hT0 hinit hcobdd
    rwa [hcarry] at hlim
  have hθlim : θ ≤ Filter.liminf z atTop := by
    refine le_of_forall_pos_le_add ?_
    intro eps heps
    let r : ℝ := min (θ / 2) (eps / 2)
    let ell : ℝ := θ - r
    have hr : 0 < r := by simp [r, hθ, heps]
    have hrθ : r ≤ θ / 2 := min_le_left _ _
    have hreps : r ≤ eps / 2 := min_le_right _ _
    have hell : 0 < ell := by dsimp [ell]; linarith
    have hellθ : ell < θ := by dsimp [ell]; linarith
    have hle := hsubthreshold ell hell hellθ
    dsimp [ell] at hle
    linarith
  have hthreshold : generalMScalarThreshold p = θ := by
    rfl
  rw [← generalMScalarThreshold_eq_theorem21Part3LowerU hm, hthreshold]
  exact hθlim

end

end ShenWork.Paper3

#print axioms ShenWork.Paper3.generalMScalar_inv_delta
#print axioms ShenWork.Paper3.generalM_logistic_dominates_single_power_on_unit
#print axioms ShenWork.Paper3.generalM_liminf_ge_of_RightLowerDiniGE
