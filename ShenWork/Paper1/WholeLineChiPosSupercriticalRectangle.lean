import ShenWork.Paper1.WholeLineChiPosEquilibriumDescent
import ShenWork.Paper1.WholeLineChiPosRectangleSqueeze
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Supercritical positive-sensitivity rectangle squeeze

The supercritical floor residual is not globally antitone below one.  Its
only possible non-antitone part lies below an explicit threshold, where a
positive reserve bounds the residual from below.  Rectangles carry the sharp
equilibrium height bound needed to keep this reserve positive.
-/

open Filter Topology Set Real Function

noncomputable section

namespace ShenWork.Paper1

/-- The exponent `q = m + γ - 1` appearing in the chemotactic power. -/
def chiPosSupercriticalQ (p : CMParams) : ℝ := p.m + p.γ - 1

/-- The positive exponent gap `α - q`. -/
def chiPosSupercriticalD (p : CMParams) : ℝ :=
  p.α - chiPosSupercriticalQ p

/-- The point above which the supercritical floor residual is strictly
decreasing. -/
def chiPosSupercriticalFloorThreshold (p : CMParams) : ℝ :=
  (p.χ * chiPosSupercriticalQ p / p.α) ^
    (1 / chiPosSupercriticalD p)

/-- Uniform lower reserve for the floor residual below its monotonicity
threshold. -/
def chiPosSupercriticalFloorReserve (p : CMParams) (M : ℝ) : ℝ :=
  1 - p.χ * M ^ p.γ

theorem chiPosSupercriticalQ_pos (p : CMParams) :
    0 < chiPosSupercriticalQ p := by
  unfold chiPosSupercriticalQ
  linarith [p.hm, p.hγ]

theorem chiPosSupercriticalD_pos
    {p : CMParams} (hsuper : p.m + p.γ - 1 < p.α) :
    0 < chiPosSupercriticalD p := by
  unfold chiPosSupercriticalD chiPosSupercriticalQ
  linarith

theorem chiPosSupercriticalFloorThreshold_pos
    {p : CMParams} (hχ : 0 < p.χ) :
    0 < chiPosSupercriticalFloorThreshold p := by
  unfold chiPosSupercriticalFloorThreshold
  have hq := chiPosSupercriticalQ_pos p
  have hα : 0 < p.α := zero_lt_one.trans_le p.hα
  exact Real.rpow_pos_of_pos (div_pos (mul_pos hχ hq) hα)
    (1 / chiPosSupercriticalD p)

theorem chiPosSupercriticalFloorThreshold_rpow_d
    {p : CMParams} (hχ : 0 < p.χ)
    (hsuper : p.m + p.γ - 1 < p.α) :
    chiPosSupercriticalFloorThreshold p ^ chiPosSupercriticalD p =
      p.χ * chiPosSupercriticalQ p / p.α := by
  have hbase : 0 ≤ p.χ * chiPosSupercriticalQ p / p.α := by
    exact div_nonneg (mul_nonneg hχ.le (chiPosSupercriticalQ_pos p).le)
      (zero_le_one.trans p.hα)
  have hd := chiPosSupercriticalD_pos hsuper
  unfold chiPosSupercriticalFloorThreshold
  rw [one_div, Real.rpow_inv_rpow hbase hd.ne']

theorem chiPosSupercriticalFloorThreshold_lt_one
    {p : CMParams} (hχ : 0 < p.χ) (hχhalf : p.χ < 1 / 2)
    (hsuper : p.m + p.γ - 1 < p.α) :
    chiPosSupercriticalFloorThreshold p < 1 := by
  have hq : 0 < chiPosSupercriticalQ p := chiPosSupercriticalQ_pos p
  have hα : 0 < p.α := zero_lt_one.trans_le p.hα
  have hqα : chiPosSupercriticalQ p < p.α := by
    simpa [chiPosSupercriticalQ] using hsuper
  have hbase0 : 0 ≤ p.χ * chiPosSupercriticalQ p / p.α := by
    positivity
  have hbaseχ : p.χ * chiPosSupercriticalQ p / p.α < p.χ := by
    rw [div_lt_iff₀ hα]
    nlinarith
  have hbase1 : p.χ * chiPosSupercriticalQ p / p.α < 1 :=
    hbaseχ.trans (by linarith)
  exact Real.rpow_lt_one hbase0 hbase1
    (one_div_pos.mpr (chiPosSupercriticalD_pos hsuper))

/-- General expansion of the floor residual into the three relevant powers. -/
theorem chiPosFloorGap_supercritical_expansion
    (p : CMParams) {M x : ℝ} (hx : 0 < x) :
    chiPosFloorGap p M x =
      1 - x ^ p.α - p.χ * M ^ p.γ * x ^ (p.m - 1) +
        p.χ * x ^ chiPosSupercriticalQ p := by
  have hpow : x ^ (p.m - 1) * x ^ p.γ =
      x ^ chiPosSupercriticalQ p := by
    rw [← Real.rpow_add hx]
    congr 1
    unfold chiPosSupercriticalQ
    ring
  unfold chiPosFloorGap
  rw [mul_sub, hpow]
  ring

/-- General expansion of the ceiling residual into the three relevant powers. -/
theorem chiPosCeilingGap_supercritical_expansion
    (p : CMParams) {ell x : ℝ} (hx : 0 < x) :
    chiPosCeilingGap p ell x =
      x ^ p.α - 1 - p.χ * x ^ chiPosSupercriticalQ p +
        p.χ * ell ^ p.γ * x ^ (p.m - 1) := by
  have hpow : x ^ (p.m - 1) * x ^ p.γ =
      x ^ chiPosSupercriticalQ p := by
    rw [← Real.rpow_add hx]
    congr 1
    unfold chiPosSupercriticalQ
    ring
  unfold chiPosCeilingGap
  rw [mul_sub, hpow]
  ring

/-- The sharp equilibrium height bound makes the below-threshold floor
reserve positive. -/
theorem chiPosSupercriticalFloorReserve_pos
    {p : CMParams} (hχ0 : 0 ≤ p.χ) (hχhalf : p.χ < 1 / 2)
    (hsuper : p.m + p.γ - 1 < p.α)
    {M : ℝ} (hM1 : 1 ≤ M) (hMα : M ^ p.α < 2) :
    0 < chiPosSupercriticalFloorReserve p M := by
  have hγα : p.γ ≤ p.α := by
    linarith [p.hm]
  have hMγα : M ^ p.γ ≤ M ^ p.α :=
    Real.rpow_le_rpow_of_exponent_le hM1 hγα
  unfold chiPosSupercriticalFloorReserve
  nlinarith [mul_nonneg hχ0 (Real.rpow_nonneg (zero_le_one.trans hM1) p.γ)]

/-- Below the monotonicity threshold the floor residual is strictly larger
than its reserve. -/
theorem chiPosSupercriticalFloorReserve_lt_gap
    {p : CMParams} (hχ : 0 < p.χ) (hχhalf : p.χ < 1 / 2)
    (hsuper : p.m + p.γ - 1 < p.α)
    {M x : ℝ} (hM0 : 0 ≤ M) (hx : 0 < x)
    (hxθ : x ≤ chiPosSupercriticalFloorThreshold p) :
    chiPosSupercriticalFloorReserve p M < chiPosFloorGap p M x := by
  let q : ℝ := chiPosSupercriticalQ p
  let d : ℝ := chiPosSupercriticalD p
  let θ : ℝ := chiPosSupercriticalFloorThreshold p
  have hθ1 : θ < 1 := by
    exact chiPosSupercriticalFloorThreshold_lt_one hχ hχhalf hsuper
  have hx1 : x < 1 := hxθ.trans_lt hθ1
  have hs0 : (0 : ℝ) ≤ p.m - 1 := sub_nonneg.mpr p.hm
  have hxs1 : x ^ (p.m - 1) ≤ 1 := by
    simpa only [Real.one_rpow] using
      Real.rpow_le_rpow hx.le hx1.le hs0
  have hd : 0 < d := chiPosSupercriticalD_pos hsuper
  have hxdθ : x ^ d ≤ θ ^ d :=
    Real.rpow_le_rpow hx.le hxθ hd.le
  have hθd : θ ^ d = p.χ * q / p.α := by
    simpa [θ, d, q] using
      chiPosSupercriticalFloorThreshold_rpow_d hχ hsuper
  have hqα : q < p.α := by
    simpa [q, chiPosSupercriticalQ] using hsuper
  have hα : 0 < p.α := zero_lt_one.trans_le p.hα
  have hθdχ : θ ^ d < p.χ := by
    rw [hθd, div_lt_iff₀ hα]
    nlinarith
  have hxdχ : x ^ d < p.χ := hxdθ.trans_lt hθdχ
  have hq0 : 0 < q := by simpa [q] using chiPosSupercriticalQ_pos p
  have hxq : 0 < x ^ q := Real.rpow_pos_of_pos hx q
  have hMγ : 0 ≤ M ^ p.γ := Real.rpow_nonneg hM0 p.γ
  have hsplit : x ^ p.α = x ^ q * x ^ d := by
    rw [← Real.rpow_add hx]
    congr 1
    dsimp [q, d]
    unfold chiPosSupercriticalD
    ring
  rw [chiPosFloorGap_supercritical_expansion p hx]
  unfold chiPosSupercriticalFloorReserve
  change 1 - p.χ * M ^ p.γ <
    1 - x ^ p.α - p.χ * M ^ p.γ * x ^ (p.m - 1) + p.χ * x ^ q
  rw [hsplit]
  have hreserveTerm :
      0 ≤ p.χ * M ^ p.γ * (1 - x ^ (p.m - 1)) := by
    exact mul_nonneg
      (mul_nonneg hχ.le (Real.rpow_nonneg hM0 p.γ))
      (sub_nonneg.mpr hxs1)
  have hpowerTerm : 0 < x ^ q * (p.χ - x ^ d) := by
    exact mul_pos hxq (sub_pos.mpr hxdχ)
  nlinarith

/-- Derivative of the supercritical floor residual at a positive point. -/
theorem chiPosFloorGap_hasDerivAt_supercritical
    (p : CMParams) (M : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (chiPosFloorGap p M)
      (-p.α * x ^ (p.α - 1) -
          p.χ * M ^ p.γ * (p.m - 1) * x ^ (p.m - 2) +
        p.χ * chiPosSupercriticalQ p *
          x ^ (chiPosSupercriticalQ p - 1)) x := by
  have hα : HasDerivAt (fun y : ℝ => y ^ p.α)
      (p.α * x ^ (p.α - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx.ne')
  have hm : HasDerivAt (fun y : ℝ => y ^ (p.m - 1))
      ((p.m - 1) * x ^ (p.m - 2)) x := by
    convert Real.hasDerivAt_rpow_const
      (x := x) (p := p.m - 1) (Or.inl hx.ne') using 1 <;> ring
  have hq : HasDerivAt (fun y : ℝ => y ^ chiPosSupercriticalQ p)
      (chiPosSupercriticalQ p *
        x ^ (chiPosSupercriticalQ p - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx.ne')
  let f : ℝ → ℝ := fun y =>
    1 - y ^ p.α - p.χ * M ^ p.γ * y ^ (p.m - 1) +
      p.χ * y ^ chiPosSupercriticalQ p
  have hf : HasDerivAt f
      (-p.α * x ^ (p.α - 1) -
          p.χ * M ^ p.γ * (p.m - 1) * x ^ (p.m - 2) +
        p.χ * chiPosSupercriticalQ p *
          x ^ (chiPosSupercriticalQ p - 1)) x := by
    dsimp [f]
    convert (((hasDerivAt_const x (1 : ℝ)).sub hα).sub
      (hm.const_mul (p.χ * M ^ p.γ))).add (hq.const_mul p.χ) using 1 <;> ring
  have heq : chiPosFloorGap p M =ᶠ[nhds x] f := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact chiPosFloorGap_supercritical_expansion p hy
  exact hf.congr_of_eventuallyEq heq

/-- Derivative of the supercritical ceiling residual at a positive point. -/
theorem chiPosCeilingGap_hasDerivAt_supercritical
    (p : CMParams) (ell : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (chiPosCeilingGap p ell)
      (p.α * x ^ (p.α - 1) -
          p.χ * chiPosSupercriticalQ p *
            x ^ (chiPosSupercriticalQ p - 1) +
        p.χ * ell ^ p.γ * (p.m - 1) * x ^ (p.m - 2)) x := by
  have hα : HasDerivAt (fun y : ℝ => y ^ p.α)
      (p.α * x ^ (p.α - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx.ne')
  have hm : HasDerivAt (fun y : ℝ => y ^ (p.m - 1))
      ((p.m - 1) * x ^ (p.m - 2)) x := by
    convert Real.hasDerivAt_rpow_const
      (x := x) (p := p.m - 1) (Or.inl hx.ne') using 1 <;> ring
  have hq : HasDerivAt (fun y : ℝ => y ^ chiPosSupercriticalQ p)
      (chiPosSupercriticalQ p *
        x ^ (chiPosSupercriticalQ p - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx.ne')
  let f : ℝ → ℝ := fun y =>
    y ^ p.α - 1 - p.χ * y ^ chiPosSupercriticalQ p +
      p.χ * ell ^ p.γ * y ^ (p.m - 1)
  have hf : HasDerivAt f
      (p.α * x ^ (p.α - 1) -
          p.χ * chiPosSupercriticalQ p *
            x ^ (chiPosSupercriticalQ p - 1) +
        p.χ * ell ^ p.γ * (p.m - 1) * x ^ (p.m - 2)) x := by
    dsimp [f]
    convert ((hα.sub_const 1).sub (hq.const_mul p.χ)).add
      (hm.const_mul (p.χ * ell ^ p.γ)) using 1 <;> ring
  have heq : chiPosCeilingGap p ell =ᶠ[nhds x] f := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact chiPosCeilingGap_supercritical_expansion p hy
  exact hf.congr_of_eventuallyEq heq

/-- Above the explicit threshold the floor residual is strictly decreasing. -/
theorem chiPosFloorGap_strictAntiOn_threshold_one
    {p : CMParams} (hχ : 0 < p.χ) (hχhalf : p.χ < 1 / 2)
    (hsuper : p.m + p.γ - 1 < p.α)
    {M : ℝ} (hM0 : 0 ≤ M) :
    StrictAntiOn (chiPosFloorGap p M)
      (Set.Icc (chiPosSupercriticalFloorThreshold p) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (chiPosFloorGap_continuous p M).continuousOn
  intro x hxint
  rw [interior_Icc] at hxint
  let q : ℝ := chiPosSupercriticalQ p
  let d : ℝ := chiPosSupercriticalD p
  let θ : ℝ := chiPosSupercriticalFloorThreshold p
  have hθ0 : 0 < θ := by
    simpa [θ] using chiPosSupercriticalFloorThreshold_pos hχ
  have hx0 : 0 < x := hθ0.trans hxint.1
  have hd : 0 < d := chiPosSupercriticalD_pos hsuper
  have hθd : θ ^ d = p.χ * q / p.α := by
    simpa [θ, d, q] using
      chiPosSupercriticalFloorThreshold_rpow_d hχ hsuper
  have hxd : θ ^ d < x ^ d :=
    Real.rpow_lt_rpow hθ0.le hxint.1 hd
  have hα : 0 < p.α := zero_lt_one.trans_le p.hα
  have hcoef : p.χ * q < p.α * x ^ d := by
    rw [hθd] at hxd
    have := mul_lt_mul_of_pos_left hxd hα
    field_simp at this
    exact this
  have hxq : 0 < x ^ (q - 1) := Real.rpow_pos_of_pos hx0 _
  have hlead :
      p.χ * q * x ^ (q - 1) < p.α * x ^ (p.α - 1) := by
    have hmul := mul_lt_mul_of_pos_right hcoef hxq
    have hsplit : x ^ (p.α - 1) = x ^ (q - 1) * x ^ d := by
      rw [← Real.rpow_add hx0]
      congr 1
      dsimp [q, d]
      unfold chiPosSupercriticalD
      ring
    rw [hsplit]
    nlinarith
  have htail :
      0 ≤ p.χ * M ^ p.γ * (p.m - 1) * x ^ (p.m - 2) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hχ.le (Real.rpow_nonneg hM0 p.γ))
        (sub_nonneg.mpr p.hm))
      (Real.rpow_nonneg hx0.le _)
  rw [(chiPosFloorGap_hasDerivAt_supercritical p M hx0).deriv]
  change -p.α * x ^ (p.α - 1) -
      p.χ * M ^ p.γ * (p.m - 1) * x ^ (p.m - 2) +
    p.χ * q * x ^ (q - 1) < 0
  linarith

/-- On and above one the supercritical ceiling residual is strictly
increasing. -/
theorem chiPosCeilingGap_strictMonoOn_Ici_one
    {p : CMParams} (hχ0 : 0 ≤ p.χ) (hχhalf : p.χ < 1 / 2)
    (hsuper : p.m + p.γ - 1 < p.α)
    {ell : ℝ} (hell0 : 0 ≤ ell) :
    StrictMonoOn (chiPosCeilingGap p ell) (Set.Ici 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 1)
    (chiPosCeilingGap_continuous p ell).continuousOn
  intro x hxint
  rw [interior_Ici] at hxint
  let q : ℝ := chiPosSupercriticalQ p
  let d : ℝ := chiPosSupercriticalD p
  have hx0 : 0 < x := zero_lt_one.trans hxint
  have hd : 0 < d := chiPosSupercriticalD_pos hsuper
  have hxd1 : 1 < x ^ d := Real.one_lt_rpow hxint hd
  have hq : 0 < q := by simpa [q] using chiPosSupercriticalQ_pos p
  have hqα : q < p.α := by simpa [q, chiPosSupercriticalQ] using hsuper
  have hχ1 : p.χ < 1 := by linarith
  have hcoef : p.χ * q < p.α * x ^ d := by
    have hχq : p.χ * q < q := by nlinarith
    have hαpos : 0 < p.α := zero_lt_one.trans_le p.hα
    nlinarith
  have hxq : 0 < x ^ (q - 1) := Real.rpow_pos_of_pos hx0 _
  have hlead :
      p.χ * q * x ^ (q - 1) < p.α * x ^ (p.α - 1) := by
    have hmul := mul_lt_mul_of_pos_right hcoef hxq
    have hsplit : x ^ (p.α - 1) = x ^ (q - 1) * x ^ d := by
      rw [← Real.rpow_add hx0]
      congr 1
      dsimp [q, d]
      unfold chiPosSupercriticalD
      ring
    rw [hsplit]
    nlinarith
  have htail :
      0 ≤ p.χ * ell ^ p.γ * (p.m - 1) * x ^ (p.m - 2) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hχ0 (Real.rpow_nonneg hell0 p.γ))
        (sub_nonneg.mpr p.hm))
      (Real.rpow_nonneg hx0.le _)
  rw [(chiPosCeilingGap_hasDerivAt_supercritical p ell hx0).deriv]
  change 0 < p.α * x ^ (p.α - 1) -
      p.χ * q * x ^ (q - 1) +
    p.χ * ell ^ p.γ * (p.m - 1) * x ^ (p.m - 2)
  linarith

/-! ## Weighted barriers from interval gap monotonicity -/

/-- A capped floor is a weighted subsolution whenever its endpoint residual
is bounded above by every residual traversed by the barrier. -/
theorem chiZeroKPPFloor_weighted_subsolution_of_gap_mono
    {p : CMParams} {M C L t : ℝ}
    (hC : 0 < C) (hCL : C < L)
    (hgap : 0 < chiPosFloorGap p M L)
    (hgapMono : ∀ B ∈ Set.Icc C L,
      chiPosFloorGap p M L ≤ chiPosFloorGap p M B)
    (ht : 0 ≤ t) :
    deriv (chiZeroKPPFloor C L (chiPosRectangleFloorRate p M C L)) t +
        p.χ * (chiZeroKPPFloor C L
          (chiPosRectangleFloorRate p M C L) t) ^ p.m *
          (M ^ p.γ - (chiZeroKPPFloor C L
            (chiPosRectangleFloorRate p M C L) t) ^ p.γ) ≤
      reactionFun p.α
        (chiZeroKPPFloor C L (chiPosRectangleFloorRate p M C L) t) := by
  let lam : ℝ := chiPosRectangleFloorRate p M C L
  let B : ℝ := chiZeroKPPFloor C L lam t
  have hlam : 0 < lam := chiPosRectangleFloorRate_pos hC hCL hgap
  have hBderiv : deriv (chiZeroKPPFloor C L lam) t = lam * (L - B) := by
    simpa [B] using (chiZeroKPPFloor_hasDerivAt C L lam t).deriv
  have hBge : C ≤ B := chiZeroKPPFloor_ge_start hCL.le hlam.le ht
  have hBle : B ≤ L := chiZeroKPPFloor_le_target hCL.le
  have hBpos : 0 < B := hC.trans_le hBge
  have hgapMonoB : chiPosFloorGap p M L ≤ chiPosFloorGap p M B :=
    hgapMono B ⟨hBge, hBle⟩
  have htime : lam * (L - B) ≤ lam * (L - C) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_left hBge L) hlam.le
  have hbudget : lam * (L - C) ≤ C * chiPosFloorGap p M L := by
    simpa [lam] using chiPosRectangleFloorRate_mul_gap_le hC hCL hgap
  have hprod : C * chiPosFloorGap p M L ≤ B * chiPosFloorGap p M B := by
    calc
      C * chiPosFloorGap p M L ≤ B * chiPosFloorGap p M L :=
        mul_le_mul_of_nonneg_right hBge hgap.le
      _ ≤ B * chiPosFloorGap p M B :=
        mul_le_mul_of_nonneg_left hgapMonoB hBpos.le
  have hweighted : B * chiPosFloorGap p M B =
      reactionFun p.α B - p.χ * B ^ p.m * (M ^ p.γ - B ^ p.γ) := by
    have hm : B * B ^ (p.m - 1) = B ^ p.m :=
      mul_rpow_sub_one p.m p.hm hBpos.le
    unfold chiPosFloorGap reactionFun
    calc
      B * (1 - B ^ p.α -
          p.χ * (B ^ (p.m - 1) * (M ^ p.γ - B ^ p.γ))) =
          B * (1 - B ^ p.α) -
            p.χ * (B * B ^ (p.m - 1)) * (M ^ p.γ - B ^ p.γ) := by ring
      _ = B * (1 - B ^ p.α) -
          p.χ * B ^ p.m * (M ^ p.γ - B ^ p.γ) := by rw [hm]
  change deriv (chiZeroKPPFloor C L lam) t +
      p.χ * B ^ p.m * (M ^ p.γ - B ^ p.γ) ≤ reactionFun p.α B
  rw [hBderiv]
  linarith [htime, hbudget, hprod, hweighted]

/-- A capped ceiling is a weighted supersolution under the analogous
interval residual monotonicity condition. -/
theorem chiPosTargetCeiling_weighted_supersolution_of_gap_mono
    {p : CMParams} {ell A D t : ℝ}
    (hA : 0 < A) (hAD : A < D)
    (hgap : 0 < chiPosCeilingGap p ell A)
    (hgapMono : ∀ B ∈ Set.Icc A D,
      chiPosCeilingGap p ell A ≤ chiPosCeilingGap p ell B)
    (ht : 0 ≤ t) :
    reactionFun p.α
        (chiPosTargetCeiling A D
          (chiPosRectangleCeilingRate p ell A D) t) +
        p.χ * (chiPosTargetCeiling A D
          (chiPosRectangleCeilingRate p ell A D) t) ^ p.m *
          ((chiPosTargetCeiling A D
            (chiPosRectangleCeilingRate p ell A D) t) ^ p.γ - ell ^ p.γ) ≤
      deriv (chiPosTargetCeiling A D
        (chiPosRectangleCeilingRate p ell A D)) t := by
  let lam : ℝ := chiPosRectangleCeilingRate p ell A D
  let B : ℝ := chiPosTargetCeiling A D lam t
  have hlam : 0 < lam := chiPosRectangleCeilingRate_pos hA hAD hgap
  have hBderiv : deriv (chiPosTargetCeiling A D lam) t = -lam * (B - A) := by
    simpa [B] using (chiPosTargetCeiling_hasDerivAt A D lam t).deriv
  have hBge : A ≤ B := chiPosTargetCeiling_ge_target hAD.le
  have hBle : B ≤ D := chiPosTargetCeiling_le_start hAD.le hlam.le ht
  have hBpos : 0 < B := hA.trans_le hBge
  have hgapMonoB : chiPosCeilingGap p ell A ≤ chiPosCeilingGap p ell B :=
    hgapMono B ⟨hBge, hBle⟩
  have htime : lam * (B - A) ≤ lam * (D - A) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_right hBle A) hlam.le
  have hbudget : lam * (D - A) ≤ A * chiPosCeilingGap p ell A := by
    simpa [lam] using chiPosRectangleCeilingRate_mul_gap_le hA hAD hgap
  have hprod : A * chiPosCeilingGap p ell A ≤ B * chiPosCeilingGap p ell B := by
    calc
      A * chiPosCeilingGap p ell A ≤ B * chiPosCeilingGap p ell A :=
        mul_le_mul_of_nonneg_right hBge hgap.le
      _ ≤ B * chiPosCeilingGap p ell B :=
        mul_le_mul_of_nonneg_left hgapMonoB hBpos.le
  have hweighted :
      reactionFun p.α B + p.χ * B ^ p.m * (B ^ p.γ - ell ^ p.γ) =
        -(B * chiPosCeilingGap p ell B) := by
    have hm : B * B ^ (p.m - 1) = B ^ p.m :=
      mul_rpow_sub_one p.m p.hm hBpos.le
    have hgapExpand : B * chiPosCeilingGap p ell B =
        B * (B ^ p.α - 1) -
          p.χ * B ^ p.m * (B ^ p.γ - ell ^ p.γ) := by
      unfold chiPosCeilingGap
      calc
        B * (B ^ p.α - 1 -
            p.χ * (B ^ (p.m - 1) * (B ^ p.γ - ell ^ p.γ))) =
            B * (B ^ p.α - 1) -
              p.χ * (B * B ^ (p.m - 1)) *
                (B ^ p.γ - ell ^ p.γ) := by ring
        _ = B * (B ^ p.α - 1) -
            p.χ * B ^ p.m * (B ^ p.γ - ell ^ p.γ) := by rw [hm]
    rw [hgapExpand]
    unfold reactionFun
    ring
  change reactionFun p.α B + p.χ * B ^ p.m * (B ^ p.γ - ell ^ p.γ) ≤
      deriv (chiPosTargetCeiling A D lam) t
  rw [hBderiv, hweighted]
  linarith [htime, hbudget, hprod]

/-! ## Supercritical round targets -/

/-- Ordinary rectangle targets supplemented by the floor-reserve information
needed on the non-monotone part below the threshold. -/
structure ChiPosSupercriticalRectangleRoundTargets
    (p : CMParams) (ell M δ : ℝ)
    extends ChiPosRectangleRoundTargets p ell M δ where
  threshold_lt_L : chiPosSupercriticalFloorThreshold p < L
  floor_raw_margin_lt_reserve :
    chiPosFloorGap p M Lraw < chiPosSupercriticalFloorReserve p M

/-- Select a full rectangle round in the supercritical regime. -/
theorem exists_chiPos_supercritical_rectangle_round_targets
    {p : CMParams} (hχ : 0 < p.χ) (hχhalf : p.χ < 1 / 2)
    (hsuper : p.m + p.γ - 1 < p.α)
    {ell M δ : ℝ}
    (hell : 0 < ell) (hell1 : ell < 1) (h1M : 1 < M)
    (hMα : M ^ p.α < 2)
    (hfloorMargin : 0 < chiPosFloorGap p M ell)
    (hceilingMargin : 0 < chiPosCeilingGap p ell M)
    (hδ : 0 < δ) :
    Nonempty (ChiPosSupercriticalRectangleRoundTargets p ell M δ) := by
  let θ : ℝ := chiPosSupercriticalFloorThreshold p
  let reserve : ℝ := chiPosSupercriticalFloorReserve p M
  let lo : ℝ := max ell θ
  let δ' : ℝ := min δ (reserve / 2)
  have hθ0 : 0 < θ := by
    simpa [θ] using chiPosSupercriticalFloorThreshold_pos hχ
  have hθ1 : θ < 1 := by
    simpa [θ] using
      chiPosSupercriticalFloorThreshold_lt_one hχ hχhalf hsuper
  have hreserve : 0 < reserve := by
    dsimp [reserve]
    exact chiPosSupercriticalFloorReserve_pos hχ.le hχhalf hsuper h1M.le hMα
  have hlo1 : lo < 1 := by
    dsimp [lo]
    exact max_lt hell1 hθ1
  have hδ' : 0 < δ' := by
    dsimp [δ']
    exact lt_min hδ (half_pos hreserve)
  have hloMargin : 0 < chiPosFloorGap p M lo := by
    rcases le_total ell θ with hellθ | hθell
    · rw [show lo = θ by simp [lo, max_eq_right hellθ]]
      exact hreserve.trans
        (chiPosSupercriticalFloorReserve_lt_gap hχ hχhalf hsuper
          (zero_le_one.trans h1M.le) hθ0 le_rfl)
    · rw [show lo = ell by simp [lo, max_eq_left hθell]]
      exact hfloorMargin
  have hfloorAtOne : chiPosFloorGap p M 1 ≤ 0 := by
    have hMγ : (1 : ℝ) ≤ M ^ p.γ :=
      Real.one_le_rpow h1M.le (zero_le_one.trans p.hγ)
    unfold chiPosFloorGap
    simp only [Real.one_rpow]
    nlinarith
  have hfloorAnti : StrictAntiOn (chiPosFloorGap p M) (Set.Icc lo 1) :=
    (chiPosFloorGap_strictAntiOn_threshold_one hχ hχhalf hsuper
      (zero_le_one.trans h1M.le)).mono (by
        intro x hx
        exact ⟨(le_max_right ell θ).trans hx.1, hx.2⟩)
  rcases exists_two_floor_targets hlo1 hδ'
      (chiPosFloorGap_continuous p M).continuousOn hfloorAnti
      hloMargin hfloorAtOne with
    ⟨L, Lraw, hloL, hLLraw, hLraw1, hfloorRaw, hfloorLδ'⟩
  have hellL : ell < L :=
    (le_max_left ell θ).trans_lt hloL
  have hθL : θ < L :=
    (le_max_right ell θ).trans_lt hloL
  have hfloorLδ : chiPosFloorGap p M L ≤ δ :=
    hfloorLδ'.trans (min_le_left δ (reserve / 2))
  have hrawL : chiPosFloorGap p M Lraw < chiPosFloorGap p M L :=
    hfloorAnti
      ⟨hloL.le, (hLLraw.trans_le hLraw1).le⟩
      ⟨(hloL.trans hLLraw).le, hLraw1⟩ hLLraw
  have hrawReserve : chiPosFloorGap p M Lraw < reserve := by
    calc
      chiPosFloorGap p M Lraw < chiPosFloorGap p M L := hrawL
      _ ≤ δ' := hfloorLδ'
      _ ≤ reserve / 2 := min_le_right δ (reserve / 2)
      _ < reserve := half_lt_self hreserve
  have hLpos : 0 < L := hell.trans hellL
  have hL1 : L < 1 := hLLraw.trans_le hLraw1
  have hceilMarginL : 0 < chiPosCeilingGap p L M :=
    hceilingMargin.trans_le
      (chiPosCeilingGap_mono_resolver_floor hχ.le hell.le hellL.le
        (zero_le_one.trans h1M.le))
  have hceilingAtOne : chiPosCeilingGap p L 1 ≤ 0 := by
    have hLγ : L ^ p.γ < 1 := by
      simpa only [Real.one_rpow] using
        Real.rpow_lt_rpow hLpos.le hL1 (zero_lt_one.trans_le p.hγ)
    rw [chiPosCeilingGap_supercritical_expansion p zero_lt_one]
    simp only [Real.one_rpow]
    nlinarith
  have hceilingMono :
      StrictMonoOn (chiPosCeilingGap p L) (Set.Icc 1 M) :=
    (chiPosCeilingGap_strictMonoOn_Ici_one hχ.le hχhalf hsuper hLpos.le).mono
      Set.Icc_subset_Ici_self
  rcases exists_two_ceiling_targets h1M hδ
      (chiPosCeilingGap_continuous p L).continuousOn hceilingMono
      hceilingAtOne hceilMarginL with
    ⟨Araw, A, h1Araw, hArawA, hAM, hceilRaw, hceilAδ⟩
  have hfloorAtL : 0 < chiPosFloorGap p M L := hfloorRaw.trans hrawL
  have hA0 : 0 ≤ A := zero_le_one.trans (h1Araw.trans hArawA.le)
  have hnextFloor : 0 < chiPosFloorGap p A L :=
    hfloorAtL.trans_le
      (chiPosFloorGap_anti_resolver_ceiling hχ.le hLpos.le hA0 hAM.le)
  have hnextCeiling : 0 < chiPosCeilingGap p L A := by
    have hArawmem : Araw ∈ Set.Icc (1 : ℝ) M :=
      ⟨h1Araw, (hArawA.trans hAM).le⟩
    have hAmem : A ∈ Set.Icc (1 : ℝ) M :=
      ⟨h1Araw.trans hArawA.le, hAM.le⟩
    exact hceilRaw.trans (hceilingMono hArawmem hAmem hArawA)
  exact ⟨
    { toChiPosRectangleRoundTargets :=
        { L := L
          Lraw := Lraw
          Araw := Araw
          A := A
          ell_lt_L := hellL
          L_lt_Lraw := hLLraw
          Lraw_le_one := hLraw1
          one_le_Araw := h1Araw
          Araw_lt_A := hArawA
          A_lt_M := hAM
          floor_raw_margin := hfloorRaw
          floor_delta :=
            chiPosFloorGap_le_iff_target_inequality.mp hfloorLδ
          ceiling_raw_margin := hceilRaw
          ceiling_delta :=
            chiPosCeilingGap_le_iff_target_inequality.mp hceilAδ
          next_floor_margin := hnextFloor
          next_ceiling_margin := hnextCeiling }
      threshold_lt_L := hθL
      floor_raw_margin_lt_reserve := hrawReserve }⟩

/-- The raw floor target is below every residual traversed from the old floor. -/
theorem ChiPosSupercriticalRectangleRoundTargets.floor_gap_le_on
    {p : CMParams} {ell M δ C : ℝ}
    (r : ChiPosSupercriticalRectangleRoundTargets p ell M δ)
    (hχ : 0 < p.χ) (hχhalf : p.χ < 1 / 2)
    (hsuper : p.m + p.γ - 1 < p.α)
    (hC : 0 < C) (hM0 : 0 ≤ M) :
    ∀ B ∈ Set.Icc C r.Lraw,
      chiPosFloorGap p M r.Lraw ≤ chiPosFloorGap p M B := by
  intro B hB
  let θ : ℝ := chiPosSupercriticalFloorThreshold p
  by_cases hBθ : B ≤ θ
  · exact (r.floor_raw_margin_lt_reserve.trans
      (chiPosSupercriticalFloorReserve_lt_gap hχ hχhalf hsuper hM0
        (hC.trans_le hB.1) hBθ)).le
  · have hθB : θ < B := lt_of_not_ge hBθ
    by_cases hEq : B = r.Lraw
    · simp [hEq]
    · have hBL : B < r.Lraw := lt_of_le_of_ne hB.2 hEq
      exact (chiPosFloorGap_strictAntiOn_threshold_one hχ hχhalf hsuper hM0
        ⟨hθB.le, hB.2.trans r.Lraw_le_one⟩
        ⟨r.threshold_lt_L.le.trans r.L_lt_Lraw.le, r.Lraw_le_one⟩
        hBL).le

/-- The raw ceiling target is below every residual traversed from it to the
old ceiling. -/
theorem ChiPosSupercriticalRectangleRoundTargets.ceiling_gap_le_on
    {p : CMParams} {ell M δ : ℝ}
    (r : ChiPosSupercriticalRectangleRoundTargets p ell M δ)
    (hχ0 : 0 ≤ p.χ) (hχhalf : p.χ < 1 / 2)
    (hsuper : p.m + p.γ - 1 < p.α) (hell : 0 < ell) :
    ∀ B ∈ Set.Icc r.Araw M,
      chiPosCeilingGap p r.L r.Araw ≤ chiPosCeilingGap p r.L B := by
  intro B hB
  exact (chiPosCeilingGap_strictMonoOn_Ici_one hχ0 hχhalf hsuper
    (hell.trans r.ell_lt_L).le).monotoneOn
      r.one_le_Araw (r.one_le_Araw.trans hB.1) hB.1

theorem ChiPosSupercriticalRectangleRoundTargets.floor_weighted_subsolution
    {p : CMParams} {ell M δ t : ℝ}
    (r : ChiPosSupercriticalRectangleRoundTargets p ell M δ)
    (hχ : 0 < p.χ) (hχhalf : p.χ < 1 / 2)
    (hsuper : p.m + p.γ - 1 < p.α)
    (hell : 0 < ell) (hM0 : 0 ≤ M) (ht : 0 ≤ t) :
    deriv (chiZeroKPPFloor ell r.Lraw
      (chiPosRectangleFloorRate p M ell r.Lraw)) t +
        p.χ * (chiZeroKPPFloor ell r.Lraw
          (chiPosRectangleFloorRate p M ell r.Lraw) t) ^ p.m *
          (M ^ p.γ - (chiZeroKPPFloor ell r.Lraw
            (chiPosRectangleFloorRate p M ell r.Lraw) t) ^ p.γ) ≤
      reactionFun p.α
        (chiZeroKPPFloor ell r.Lraw
          (chiPosRectangleFloorRate p M ell r.Lraw) t) := by
  exact chiZeroKPPFloor_weighted_subsolution_of_gap_mono hell
    (r.ell_lt_L.trans r.L_lt_Lraw) r.floor_raw_margin
    (r.floor_gap_le_on hχ hχhalf hsuper hell hM0) ht

theorem ChiPosSupercriticalRectangleRoundTargets.ceiling_weighted_supersolution
    {p : CMParams} {ell M δ t : ℝ}
    (r : ChiPosSupercriticalRectangleRoundTargets p ell M δ)
    (hχ : 0 < p.χ) (hχhalf : p.χ < 1 / 2)
    (hsuper : p.m + p.γ - 1 < p.α)
    (hell : 0 < ell) (ht : 0 ≤ t) :
    reactionFun p.α
        (chiPosTargetCeiling r.Araw M
          (chiPosRectangleCeilingRate p r.L r.Araw M) t) +
        p.χ * (chiPosTargetCeiling r.Araw M
          (chiPosRectangleCeilingRate p r.L r.Araw M) t) ^ p.m *
          ((chiPosTargetCeiling r.Araw M
            (chiPosRectangleCeilingRate p r.L r.Araw M) t) ^ p.γ -
              r.L ^ p.γ) ≤
      deriv (chiPosTargetCeiling r.Araw M
        (chiPosRectangleCeilingRate p r.L r.Araw M)) t := by
  exact chiPosTargetCeiling_weighted_supersolution_of_gap_mono
    (zero_lt_one.trans_le r.one_le_Araw)
    (r.Araw_lt_A.trans r.A_lt_M) r.ceiling_raw_margin
    (r.ceiling_gap_le_on hχ.le hχhalf hsuper hell) ht

/-! ## Seed height near the exact equilibrium -/

theorem chiPosEquilibriumCeiling_lt
    {p : CMParams} (hχ : 0 < p.χ)
    (hsuper : p.m + p.γ - 1 < p.α) :
    1 < chiPosEquilibriumCeiling p := by
  have hM1 := chiPosEquilibriumCeiling_one_le p hχ.le hsuper
  have heq := chiPosEquilibriumCeiling_eq_zero p hχ.le hsuper
  have hne : chiPosEquilibriumCeiling p ≠ 1 := by
    intro hEq
    rw [hEq, chiPosEquilibriumEq_one] at heq
    linarith
  exact lt_of_le_of_ne hM1 hne.symm

/-- A height immediately above the exact equilibrium retains both the sharp
power bound and a positive ceiling margin at the floor threshold. -/
theorem exists_chiPos_supercritical_seed_height
    (p : CMParams) (hχ : 0 < p.χ) (hχhalf : p.χ < 1 / 2)
    (hsuper : p.m + p.γ - 1 < p.α) :
    ∃ M, chiPosEquilibriumCeiling p < M ∧ M ^ p.α < 2 ∧
      0 < chiPosCeilingGap p (chiPosSupercriticalFloorThreshold p) M := by
  let Mstar : ℝ := chiPosEquilibriumCeiling p
  let θ : ℝ := chiPosSupercriticalFloorThreshold p
  have hMstar1 : 1 ≤ Mstar := by
    dsimp [Mstar]
    exact chiPosEquilibriumCeiling_one_le p hχ.le hsuper
  have hMstar0 : 0 < Mstar := zero_lt_one.trans_le hMstar1
  have hMstarEq : chiPosEquilibriumEq p Mstar = 0 := by
    dsimp [Mstar]
    exact chiPosEquilibriumCeiling_eq_zero p hχ.le hsuper
  have hMstarPow : Mstar ^ p.α < 2 :=
    chiPos_equilibrium_rpow_alpha_lt_two p hχ.le hχhalf hsuper
      hMstar1 hMstarEq
  have hθ0 : 0 < θ := by
    simpa [θ] using chiPosSupercriticalFloorThreshold_pos hχ
  have hgapStar : 0 < chiPosCeilingGap p θ Mstar :=
    chiPosCeilingGap_pos_at_equilibrium p hMstar0 hχ hθ0 hMstarEq
  have hpowEventually : ∀ᶠ M : ℝ in nhds Mstar, M ^ p.α < 2 :=
    (Real.continuous_rpow_const (zero_le_one.trans p.hα)).continuousAt.eventually
      (Iio_mem_nhds hMstarPow)
  have hgapEventually : ∀ᶠ M : ℝ in nhds Mstar,
      0 < chiPosCeilingGap p θ M :=
    (chiPosCeilingGap_continuous p θ).continuousAt.eventually
      (Ioi_mem_nhds hgapStar)
  have hboth : {M : ℝ | M ^ p.α < 2 ∧
      0 < chiPosCeilingGap p θ M} ∈ nhds Mstar := by
    filter_upwards [hpowEventually, hgapEventually] with M hpow hgap
    exact ⟨hpow, hgap⟩
  rcases mem_nhds_iff_exists_Ioo_subset.mp hboth with
    ⟨lo, hi, hMmem, hsub⟩
  let M : ℝ := (Mstar + hi) / 2
  have hMstarM : Mstar < M := by
    dsimp [M]
    linarith [hMmem.2]
  have hMhi : M < hi := by
    dsimp [M]
    linarith [hMmem.2]
  have hloM : lo < M := hMmem.1.trans hMstarM
  have hprops := hsub ⟨hloM, hMhi⟩
  exact ⟨M, hMstarM, hprops.1, hprops.2⟩

/-- A supercritical rectangle is an ordinary strict-margin rectangle together
with the invariant that keeps the floor reserve positive. -/
structure ChiPosWholeLineSupercriticalRectangle
    (p : CMParams) (u : ℝ → ℝ → ℝ)
    extends ChiPosWholeLineRectangle p u where
  M_rpow_alpha_lt_two : M ^ p.α < 2

/-! ## One supercritical rectangle round -/

theorem exists_next_chiPosWholeLineSupercriticalRectangle
    (p : CMParams) (hchi : 0 < p.χ) (hchi_half : p.χ < 1 / 2)
    (hsuper : p.m + p.γ - 1 < p.α)
    (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (hleft : StrictlyPositiveAtLeft u₀.1)
    {G δ : ℝ} (hG : 0 ≤ G)
    (hglobal : ∀ ⦃t : ℝ⦄, 0 ≤ t → ∀ x,
      wholeLineCauchyGlobalU p u₀ t x ≤ G)
    (hδ : 0 < δ)
    (old : ChiPosWholeLineSupercriticalRectangle p (wholeLineCauchyGlobalU p u₀)) :
    Nonempty {new : ChiPosWholeLineSupercriticalRectangle p
        (wholeLineCauchyGlobalU p u₀) //
      ChiPosWholeLineRectangleStep p δ
        old.toChiPosWholeLineRectangle new.toChiPosWholeLineRectangle} := by
  obtain ⟨targets⟩ := exists_chiPos_supercritical_rectangle_round_targets
    hchi hchi_half hsuper old.ell_pos old.ell_lt_one old.one_lt_M
      old.M_rpow_alpha_lt_two old.floor_margin old.ceiling_margin hδ
  let H : ℝ := max G old.M
  have hH : 0 ≤ H := hG.trans (le_max_left G old.M)
  have hMH : old.M ≤ H := le_max_right G old.M
  have hglobalH : ∀ ⦃t : ℝ⦄, 0 ≤ t → ∀ x,
      wholeLineCauchyGlobalU p u₀ t x ≤ H := by
    intro t ht x
    exact (hglobal ht x).trans (le_max_left G old.M)
  let t₀ : ℝ := max old.start 1
  have ht₀ : 0 < t₀ :=
    zero_lt_one.trans_le (le_max_right old.start 1)
  have hold_t₀ : old.start ≤ t₀ := le_max_left old.start 1
  let floorData := wholeLineCauchyGlobal_positiveRestartData
    p hregime u₀ hu₀ hleft ht₀ hglobalH
  have hfloorDataM : ∀ ⦃s : ℝ⦄, 0 ≤ s → ∀ x,
      floorData.q s x ≤ old.M := by
    intro s hs x
    rw [floorData.eq_global hs x]
    exact (old.bounds (t₀ + s) (by
      exact hold_t₀.trans (le_add_of_nonneg_right hs)) x).2
  let floorRate : ℝ :=
    chiPosRectangleFloorRate p old.M old.ell targets.Lraw
  let floorBarrier : ℝ → ℝ :=
    chiZeroKPPFloor old.ell targets.Lraw floorRate
  have hfloorRate : 0 < floorRate := by
    exact chiPosRectangleFloorRate_pos old.ell_pos
      (targets.ell_lt_L.trans targets.L_lt_Lraw)
      targets.floor_raw_margin
  have hfloorInit : ∀ x, floorBarrier 0 ≤ floorData.q 0 x := by
    intro x
    rw [show floorBarrier 0 = old.ell by simp [floorBarrier]]
    rw [floorData.eq_global (s := 0) le_rfl x]
    simpa using (old.bounds t₀ hold_t₀ x).1
  have hfloorRange : ∀ s, 0 ≤ s →
      floorBarrier s ∈ Set.Icc (0 : ℝ) H := by
    intro s hs
    have hge : old.ell ≤ floorBarrier s := by
      exact chiZeroKPPFloor_ge_start
        (targets.ell_lt_L.trans targets.L_lt_Lraw).le hfloorRate.le hs
    have hle : floorBarrier s ≤ targets.Lraw := by
      exact chiZeroKPPFloor_le_target
        (targets.ell_lt_L.trans targets.L_lt_Lraw).le
    exact ⟨old.ell_pos.le.trans hge,
      hle.trans (targets.Lraw_le_one.trans
        (old.one_lt_M.le.trans hMH))⟩
  have hfloorAll : ∀ s, 0 ≤ s → ∀ x,
      floorBarrier s ≤ floorData.q s x := by
    apply floorData.ge_of_coupled_subsolution hchi hH
    · rw [continuous_iff_continuousAt]
      intro s
      exact (chiZeroKPPFloor_hasDerivAt
        old.ell targets.Lraw floorRate s).continuousAt
    · exact hfloorRange
    · exact hfloorInit
    · intro s hs
      exact (chiZeroKPPFloor_hasDerivAt
        old.ell targets.Lraw floorRate s).differentiableAt.hasDerivAt
    · intro s x hs
      exact floorData.frozenElliptic_le_of_le
        (M := old.M) (s := s) (x := x)
        (zero_le_one.trans old.one_lt_M.le) hfloorDataM hs
    · intro s hs
      exact targets.floor_weighted_subsolution hchi hchi_half hsuper
        old.ell_pos (zero_le_one.trans old.one_lt_M.le) hs.le
  have hfloorTend : Tendsto floorBarrier atTop (nhds targets.Lraw) := by
    exact chiZeroKPPFloor_tendsto_target hfloorRate
  have hfloorNhd : Set.Ioi targets.L ∈ nhds targets.Lraw :=
    Ioi_mem_nhds targets.L_lt_Lraw
  obtain ⟨Sfloor, hSfloor⟩ := eventually_atTop.1
    (hfloorTend.eventually hfloorNhd)
  let sfloor : ℝ := max Sfloor 0
  have hsfloor : 0 ≤ sfloor := le_max_right Sfloor 0
  have hS_sfloor : Sfloor ≤ sfloor := le_max_left Sfloor 0
  let t₁ : ℝ := t₀ + sfloor
  have ht₁ : 0 < t₁ := by dsimp [t₁]; linarith
  let ceilingData := wholeLineCauchyGlobal_positiveRestartData
    p hregime u₀ hu₀ hleft ht₁ hglobalH
  have hceilingDataM : ∀ ⦃s : ℝ⦄, 0 ≤ s → ∀ x,
      ceilingData.q s x ≤ old.M := by
    intro s hs x
    rw [ceilingData.eq_global hs x]
    exact (old.bounds (t₁ + s) (by
      have : old.start ≤ t₁ := by
        dsimp [t₁]
        exact hold_t₀.trans (le_add_of_nonneg_right hsfloor)
      exact this.trans (le_add_of_nonneg_right hs)) x).2
  have hceilingDataL : ∀ ⦃s : ℝ⦄, 0 ≤ s → ∀ x,
      targets.L ≤ ceilingData.q s x := by
    intro s hs x
    have helapsed : 0 ≤ sfloor + s := add_nonneg hsfloor hs
    have hbarrier : targets.L ≤ floorBarrier (sfloor + s) := by
      exact (hSfloor (sfloor + s) (hS_sfloor.trans
        (le_add_of_nonneg_right hs))).le
    have hcomp := hfloorAll (sfloor + s) helapsed x
    calc
      targets.L ≤ floorBarrier (sfloor + s) := hbarrier
      _ ≤ floorData.q (sfloor + s) x := hcomp
      _ = ceilingData.q s x := by
        rw [floorData.eq_global helapsed x, ceilingData.eq_global hs x]
        apply congrArg (fun time : ℝ =>
          wholeLineCauchyGlobalU p u₀ time x)
        dsimp [t₁]
        ring
  let ceilingRate : ℝ :=
    chiPosRectangleCeilingRate p targets.L targets.Araw old.M
  let ceilingBarrier : ℝ → ℝ :=
    chiPosTargetCeiling targets.Araw old.M ceilingRate
  have hceilingRate : 0 < ceilingRate := by
    exact chiPosRectangleCeilingRate_pos
      (zero_lt_one.trans_le targets.one_le_Araw)
      (targets.Araw_lt_A.trans targets.A_lt_M)
      targets.ceiling_raw_margin
  have hceilingInit : ∀ x, ceilingData.q 0 x ≤ ceilingBarrier 0 := by
    intro x
    rw [show ceilingBarrier 0 = old.M by simp [ceilingBarrier]]
    exact hceilingDataM le_rfl x
  have hceilingRange : ∀ s, 0 ≤ s →
      ceilingBarrier s ∈ Set.Icc (0 : ℝ) H := by
    intro s hs
    have hge : targets.Araw ≤ ceilingBarrier s :=
      chiPosTargetCeiling_ge_target
        (targets.Araw_lt_A.trans targets.A_lt_M).le
    have hle : ceilingBarrier s ≤ old.M :=
      chiPosTargetCeiling_le_start
        (targets.Araw_lt_A.trans targets.A_lt_M).le hceilingRate.le hs
    exact ⟨(zero_le_one.trans targets.one_le_Araw).trans hge,
      hle.trans hMH⟩
  have hceilingAll : ∀ s, 0 ≤ s → ∀ x,
      ceilingData.q s x ≤ ceilingBarrier s := by
    apply ceilingData.le_of_weighted_supersolution
      (Dlo := targets.L ^ p.γ) (a := ceilingBarrier) hchi hH
    · rw [continuous_iff_continuousAt]
      intro s
      exact (chiPosTargetCeiling_hasDerivAt
        targets.Araw old.M ceilingRate s).continuousAt
    · exact hceilingRange
    · exact hceilingInit
    · intro s hs
      exact (chiPosTargetCeiling_hasDerivAt
        targets.Araw old.M ceilingRate s).differentiableAt.hasDerivAt
    · intro s x hs
      exact ceilingData.frozenElliptic_ge_of_ge
        (ell := targets.L) (s := s) (x := x) hH
        (old.ell_pos.trans targets.ell_lt_L).le hceilingDataL hs
    · intro s hs
      exact targets.ceiling_weighted_supersolution hchi hchi_half
        hsuper old.ell_pos hs.le
  have hceilingTend : Tendsto ceilingBarrier atTop (nhds targets.Araw) := by
    exact chiPosTargetCeiling_tendsto_target hceilingRate
  have hceilingNhd : Set.Iio targets.A ∈ nhds targets.Araw :=
    Iio_mem_nhds targets.Araw_lt_A
  obtain ⟨Sceiling, hSceiling⟩ := eventually_atTop.1
    (hceilingTend.eventually hceilingNhd)
  let sceiling : ℝ := max Sceiling 0
  have hsceiling : 0 ≤ sceiling := le_max_right Sceiling 0
  have hS_sceiling : Sceiling ≤ sceiling := le_max_left Sceiling 0
  have hnewMα : targets.A ^ p.α < 2 := by
    have hA0 : 0 ≤ targets.A :=
      zero_le_one.trans (targets.one_le_Araw.trans targets.Araw_lt_A.le)
    exact (Real.rpow_lt_rpow hA0 targets.A_lt_M
      (zero_lt_one.trans_le p.hα)).trans old.M_rpow_alpha_lt_two
  let new : ChiPosWholeLineSupercriticalRectangle p
      (wholeLineCauchyGlobalU p u₀) :=
    { ell := targets.L
      M := targets.A
      start := t₁ + sceiling
      ell_pos := old.ell_pos.trans targets.ell_lt_L
      ell_lt_one := targets.L_lt_Lraw.trans_le targets.Lraw_le_one
      one_lt_M := targets.one_le_Araw.trans_lt targets.Araw_lt_A
      floor_margin := targets.next_floor_margin
      ceiling_margin := targets.next_ceiling_margin
      M_rpow_alpha_lt_two := hnewMα
      bounds := by
        intro t ht x
        let s : ℝ := t - t₁
        have hs : 0 ≤ s := by
          dsimp [s]
          linarith
        have hsc : sceiling ≤ s := by
          dsimp [s]
          linarith
        have hlower := hceilingDataL hs x
        have hupperComp := hceilingAll s hs x
        have hupperBarrier : ceilingBarrier s ≤ targets.A :=
          (hSceiling s (hS_sceiling.trans hsc)).le
        have heq : t₁ + s = t := by dsimp [s]; ring
        rw [ceilingData.eq_global hs x, heq] at hlower hupperComp
        exact ⟨hlower, hupperComp.trans hupperBarrier⟩ }
  refine ⟨⟨new, ?_⟩⟩
  exact
    { ell_le := targets.ell_lt_L.le
      M_le := targets.A_lt_M.le
      floor_budget := targets.floor_delta
      ceiling_budget := targets.ceiling_delta }

/-! ## Initial supercritical rectangle -/

/-- Equilibrium descent supplies the ceiling burn-in; uniform positivity and
the threshold-aware floor barrier then produce the first rectangle. -/
theorem exists_initial_chiPosWholeLineSupercriticalRectangle
    (p : CMParams) (hchi : 0 < p.χ) (hchi_half : p.χ < 1 / 2)
    (hsuper : p.m + p.γ - 1 < p.α)
    (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (hpositive : UniformlyPositive u₀.1) :
    Nonempty (ChiPosWholeLineSupercriticalRectangle p
      (wholeLineCauchyGlobalU p u₀)) := by
  let θ : ℝ := chiPosSupercriticalFloorThreshold p
  let Mstar : ℝ := chiPosEquilibriumCeiling p
  obtain ⟨M, hMstarM, hMα, hceilingθM⟩ :=
    exists_chiPos_supercritical_seed_height p hchi hchi_half hsuper
  have hMstar1 : 1 < Mstar := by
    dsimp [Mstar]
    exact chiPosEquilibriumCeiling_lt hchi hsuper
  have hM1 : 1 < M := hMstar1.trans hMstarM
  have hθ0 : 0 < θ := by
    simpa [θ] using chiPosSupercriticalFloorThreshold_pos hchi
  have hθ1 : θ < 1 := by
    simpa [θ] using
      chiPosSupercriticalFloorThreshold_lt_one hchi hchi_half hsuper
  have hreserve : 0 < chiPosSupercriticalFloorReserve p M :=
    chiPosSupercriticalFloorReserve_pos hchi.le hchi_half hsuper hM1.le hMα
  have hfloorθM : 0 < chiPosFloorGap p M θ :=
    hreserve.trans
      (chiPosSupercriticalFloorReserve_lt_gap hchi hchi_half hsuper
        (zero_le_one.trans hM1.le) hθ0 le_rfl)
  obtain ⟨targets⟩ := exists_chiPos_supercritical_rectangle_round_targets
    hchi hchi_half hsuper hθ0 hθ1 hM1 hMα hfloorθM hceilingθM
      (by norm_num : (0 : ℝ) < 1)
  have hceilingLM : 0 < chiPosCeilingGap p targets.L M :=
    hceilingθM.trans_le
      (chiPosCeilingGap_mono_resolver_floor hchi.le hθ0.le
        targets.threshold_lt_L.le (zero_le_one.trans hM1.le))
  let G : ℝ := max Mstar ‖u₀‖
  have hG : 0 ≤ G :=
    (zero_lt_one.trans hMstar1).le.trans (le_max_left Mstar ‖u₀‖)
  have hglobal : ∀ ⦃t : ℝ⦄, 0 ≤ t → ∀ x,
      wholeLineCauchyGlobalU p u₀ t x ≤ G := by
    intro t ht x
    exact wholeLineCauchyGlobal_le_max_equilibriumCeiling_of_chi_pos_supercritical
      p hchi hsuper u₀ hu₀ ht x
  have hleft : StrictlyPositiveAtLeft u₀.1 :=
    hpositive.strictlyPositiveAtLeft
  rcases hpositive with ⟨d₀, hd₀, hd₀le⟩
  let C₀ : ℝ := d₀ / 2
  have hC₀ : 0 < C₀ := by dsimp [C₀]; linarith
  have hd₀norm : d₀ ≤ ‖u₀‖ :=
    (hd₀le 0).trans (WholeLineBUC.apply_le_norm u₀ 0)
  have hC₀G : C₀ ≤ G := by
    calc
      C₀ = d₀ / 2 := rfl
      _ ≤ d₀ := by linarith
      _ ≤ ‖u₀‖ := hd₀norm
      _ ≤ G := le_max_right Mstar ‖u₀‖
  obtain ⟨tau, htau, htrace⟩ :=
    wholeLineCauchyGlobal_hasUniformInitialTrace p u₀ C₀ hC₀
  let t₀ : ℝ := tau / 2
  have ht₀ : 0 < t₀ := by dsimp [t₀]; linarith
  have ht₀tau : t₀ < tau := by dsimp [t₀]; linarith
  have hUfloor₀ : ∀ x, C₀ ≤ wholeLineCauchyGlobalU p u₀ t₀ x := by
    intro x
    have hclose := htrace t₀ x ht₀.le ht₀tau
    have hlower := neg_lt_of_abs_lt hclose
    have hdatum := hd₀le x
    dsimp [C₀] at hlower ⊢
    linarith
  let decayData := wholeLineCauchyGlobal_positiveRestartData
    p hregime u₀ hu₀ hleft ht₀ hglobal
  let decayRate : ℝ := chiPosDecayFloorRate p G
  let decayBarrier : ℝ → ℝ := chiPosDecayFloor C₀ decayRate
  have hdecayRate : 0 < decayRate :=
    chiPosDecayFloorRate_pos hchi.le hG
  have hdecayRange : ∀ s, 0 ≤ s →
      decayBarrier s ∈ Set.Icc (0 : ℝ) G := by
    intro s hs
    exact ⟨(chiPosDecayFloor_pos hC₀).le,
      (chiPosDecayFloor_le_start hC₀.le hdecayRate.le hs).trans hC₀G⟩
  have hdecayAll : ∀ s, 0 ≤ s → ∀ x,
      decayBarrier s ≤ decayData.q s x := by
    apply decayData.ge_of_weighted_subsolution
      (Dup := G ^ p.γ) (b := decayBarrier) hchi hG
    · rw [continuous_iff_continuousAt]
      intro s
      exact (chiPosDecayFloor_hasDerivAt C₀ decayRate s).continuousAt
    · exact hdecayRange
    · intro x
      rw [show decayBarrier 0 = C₀ by simp [decayBarrier]]
      rw [decayData.eq_global (s := 0) le_rfl x]
      simpa using hUfloor₀ x
    · intro s hs
      exact (chiPosDecayFloor_hasDerivAt
        C₀ decayRate s).differentiableAt.hasDerivAt
    · intro s x hs
      exact decayData.frozenElliptic_le_of_le
        (M := G) (s := s) (x := x) hG
        (fun _r hr y => (decayData.mem_Icc hr y).2) hs
    · intro s hs
      exact chiPosDecayFloor_weighted_subsolution hchi.le hG hC₀ hC₀G hs.le
  have hlimsup :=
    wholeLineCauchyGlobal_uniformLimsupLe_equilibriumCeiling_of_chi_pos_supercritical
      p hchi hsuper u₀ hu₀
  have hMgap : 0 < M - Mstar := sub_pos.mpr hMstarM
  obtain ⟨Tupper, hTupper⟩ := eventually_atTop.1 (hlimsup _ hMgap)
  let t₁ : ℝ := max Tupper t₀
  have ht₁ : 0 < t₁ := ht₀.trans_le (le_max_right Tupper t₀)
  have hTupper_t₁ : Tupper ≤ t₁ := le_max_left Tupper t₀
  have ht₀_t₁ : t₀ ≤ t₁ := le_max_right Tupper t₀
  let s₁ : ℝ := t₁ - t₀
  have hs₁ : 0 ≤ s₁ := sub_nonneg.mpr ht₀_t₁
  have hdecayAt := hdecayAll s₁ hs₁ 0
  have hdecayAtPhysical : decayBarrier s₁ ≤
      wholeLineCauchyGlobalU p u₀ t₁ 0 := by
    rw [decayData.eq_global hs₁ 0] at hdecayAt
    have heq : t₀ + s₁ = t₁ := by dsimp [s₁]; ring
    simpa [heq] using hdecayAt
  let C₁ : ℝ := min (decayBarrier s₁ / 2) (θ / 2)
  have hdecayS₁ : 0 < decayBarrier s₁ := chiPosDecayFloor_pos hC₀
  have hC₁ : 0 < C₁ := by
    dsimp [C₁]
    exact lt_min (half_pos hdecayS₁) (half_pos hθ0)
  have hC₁_decay : C₁ ≤ decayBarrier s₁ := by
    have hhalf : C₁ ≤ decayBarrier s₁ / 2 := by
      dsimp [C₁]
      exact min_le_left _ _
    linarith
  have hC₁θ : C₁ < θ := by
    have hhalf : C₁ ≤ θ / 2 := by
      dsimp [C₁]
      exact min_le_right _ _
    linarith
  have hC₁Lraw : C₁ < targets.Lraw :=
    hC₁θ.trans (targets.threshold_lt_L.trans targets.L_lt_Lraw)
  let H : ℝ := max G M
  have hH : 0 ≤ H := hG.trans (le_max_left G M)
  have hMH : M ≤ H := le_max_right G M
  have hglobalH : ∀ ⦃t : ℝ⦄, 0 ≤ t → ∀ x,
      wholeLineCauchyGlobalU p u₀ t x ≤ H := by
    intro t ht x
    exact (hglobal ht x).trans (le_max_left G M)
  let seedData := wholeLineCauchyGlobal_positiveRestartData
    p hregime u₀ hu₀ hleft ht₁ hglobalH
  have hseedDataM : ∀ ⦃s : ℝ⦄, 0 ≤ s → ∀ x,
      seedData.q s x ≤ M := by
    intro s hs x
    rw [seedData.eq_global hs x]
    have ht : Tupper ≤ t₁ + s :=
      hTupper_t₁.trans (le_add_of_nonneg_right hs)
    have := hTupper (t₁ + s) ht x
    simpa [Mstar] using this
  let seedRate : ℝ := chiPosRectangleFloorRate p M C₁ targets.Lraw
  let seedBarrier : ℝ → ℝ := chiZeroKPPFloor C₁ targets.Lraw seedRate
  have hseedRate : 0 < seedRate :=
    chiPosRectangleFloorRate_pos hC₁ hC₁Lraw targets.floor_raw_margin
  have hseedRange : ∀ s, 0 ≤ s →
      seedBarrier s ∈ Set.Icc (0 : ℝ) H := by
    intro s hs
    have hge : C₁ ≤ seedBarrier s :=
      chiZeroKPPFloor_ge_start hC₁Lraw.le hseedRate.le hs
    have hle : seedBarrier s ≤ targets.Lraw :=
      chiZeroKPPFloor_le_target hC₁Lraw.le
    exact ⟨hC₁.le.trans hge,
      hle.trans (targets.Lraw_le_one.trans (hM1.le.trans hMH))⟩
  have hseedAll : ∀ s, 0 ≤ s → ∀ x,
      seedBarrier s ≤ seedData.q s x := by
    apply seedData.ge_of_coupled_subsolution
      (Dup := M ^ p.γ) (b := seedBarrier) hchi hH
    · rw [continuous_iff_continuousAt]
      intro s
      exact (chiZeroKPPFloor_hasDerivAt C₁ targets.Lraw seedRate s).continuousAt
    · exact hseedRange
    · intro x
      rw [show seedBarrier 0 = C₁ by simp [seedBarrier]]
      rw [seedData.eq_global (s := 0) le_rfl x]
      have hdecayAtX := hdecayAll s₁ hs₁ x
      rw [decayData.eq_global hs₁ x] at hdecayAtX
      have heq : t₀ + s₁ = t₁ := by dsimp [s₁]; ring
      rw [heq] at hdecayAtX
      simpa only [add_zero] using hC₁_decay.trans hdecayAtX
    · intro s hs
      exact (chiZeroKPPFloor_hasDerivAt
        C₁ targets.Lraw seedRate s).differentiableAt.hasDerivAt
    · intro s x hs
      exact seedData.frozenElliptic_le_of_le
        (M := M) (s := s) (x := x)
        (zero_le_one.trans hM1.le) hseedDataM hs
    · intro s hs
      exact chiZeroKPPFloor_weighted_subsolution_of_gap_mono
        hC₁ hC₁Lraw targets.floor_raw_margin
        (targets.floor_gap_le_on hchi hchi_half hsuper hC₁
          (zero_le_one.trans hM1.le)) hs.le
  have hseedTend : Tendsto seedBarrier atTop (nhds targets.Lraw) :=
    chiZeroKPPFloor_tendsto_target hseedRate
  have hseedNhd : Set.Ioi targets.L ∈ nhds targets.Lraw :=
    Ioi_mem_nhds targets.L_lt_Lraw
  obtain ⟨Sseed, hSseed⟩ := eventually_atTop.1
    (hseedTend.eventually hseedNhd)
  let sseed : ℝ := max Sseed 0
  have hsseed : 0 ≤ sseed := le_max_right Sseed 0
  have hS_sseed : Sseed ≤ sseed := le_max_left Sseed 0
  refine ⟨
    { ell := targets.L
      M := M
      start := t₁ + sseed
      ell_pos := hθ0.trans targets.threshold_lt_L
      ell_lt_one := targets.L_lt_Lraw.trans_le targets.Lraw_le_one
      one_lt_M := hM1
      floor_margin :=
        targets.floor_raw_margin.trans
          ((chiPosFloorGap_strictAntiOn_threshold_one hchi hchi_half hsuper
            (zero_le_one.trans hM1.le))
            ⟨targets.threshold_lt_L.le,
              (targets.L_lt_Lraw.trans_le targets.Lraw_le_one).le⟩
            ⟨targets.threshold_lt_L.le.trans targets.L_lt_Lraw.le,
              targets.Lraw_le_one⟩ targets.L_lt_Lraw)
      ceiling_margin := hceilingLM
      M_rpow_alpha_lt_two := hMα
      bounds := ?_ }⟩
  intro t ht x
  let s : ℝ := t - t₁
  have hs : 0 ≤ s := by dsimp [s]; linarith
  have hss : sseed ≤ s := by dsimp [s]; linarith
  have hlowerBarrier : targets.L ≤ seedBarrier s :=
    (hSseed s (hS_sseed.trans hss)).le
  have hlowerComp := hseedAll s hs x
  have heq : t₁ + s = t := by dsimp [s]; ring
  rw [seedData.eq_global hs x, heq] at hlowerComp
  have hupper : wholeLineCauchyGlobalU p u₀ t x ≤ M := by
    have htUpper : Tupper ≤ t := hTupper_t₁.trans (by linarith)
    have := hTupper t htUpper x
    simpa [Mstar] using this
  exact ⟨hlowerBarrier.trans hlowerComp, hupper⟩

/-! ## Supercritical rectangle iteration -/

/-- The ordinary numerical step estimate remains valid in the
supercritical regime after forgetting the additional ceiling invariant. -/
theorem chiPosWholeLineSupercriticalRectangleStep_gap_le
    {p : CMParams} {u : ℝ → ℝ → ℝ} {δ : ℝ}
    {old new : ChiPosWholeLineSupercriticalRectangle p u}
    (h : ChiPosWholeLineRectangleStep p δ
      old.toChiPosWholeLineRectangle new.toChiPosWholeLineRectangle)
    (hle : p.m + p.γ - 1 ≤ p.α) (hchi : 0 ≤ p.χ) :
    new.M ^ p.α - new.ell ^ p.α ≤
      2 * p.χ * (old.M ^ p.α - old.ell ^ p.α) + 2 * δ := by
  exact chiPos_squeeze_gap_step_of_le p.hm p.hγ hle hchi
    old.ell_pos h.ell_le new.ell_lt_one.le new.one_lt_M.le h.M_le
    h.floor_budget h.ceiling_budget

/-- Abstract fixed-defect iteration for supercritical rectangles.  The
extra invariant is used only to construct successors; the affine gap
recurrence is the same one as in the critical argument. -/
theorem uniformConvergesToConstant_one_of_supercritical_rectangle_successors
    (p : CMParams) {u : ℝ → ℝ → ℝ}
    (hchi : 0 ≤ p.χ) (hchi_half : p.χ < 1 / 2)
    (hle : p.m + p.γ - 1 ≤ p.α)
    (seed : ChiPosWholeLineSupercriticalRectangle p u)
    (hsuccessor : ∀ δ, 0 < δ →
      ∀ old : ChiPosWholeLineSupercriticalRectangle p u,
        Nonempty {new : ChiPosWholeLineSupercriticalRectangle p u //
          ChiPosWholeLineRectangleStep p δ
            old.toChiPosWholeLineRectangle
            new.toChiPosWholeLineRectangle}) :
    UniformConvergesToConstant u 1 := by
  intro epsilon hepsilon
  let r : ℝ := 2 * p.χ
  let δ : ℝ := epsilon * (1 - r) / 4
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r < 1 := by dsimp [r]; linarith
  have h1r : 0 < 1 - r := sub_pos.mpr hr1
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let next : ChiPosWholeLineSupercriticalRectangle p u →
      ChiPosWholeLineSupercriticalRectangle p u := fun old =>
    (Classical.choice (hsuccessor δ hδ old)).1
  have hnext : ∀ old : ChiPosWholeLineSupercriticalRectangle p u,
      ChiPosWholeLineRectangleStep p δ
        old.toChiPosWholeLineRectangle
        (next old).toChiPosWholeLineRectangle := by
    intro old
    exact (Classical.choice (hsuccessor δ hδ old)).2
  let rectangles : ℕ → ChiPosWholeLineSupercriticalRectangle p u := fun n =>
    next^[n] seed
  have hrectangleStep : ∀ n,
      ChiPosWholeLineRectangleStep p δ
        (rectangles n).toChiPosWholeLineRectangle
        (rectangles (n + 1)).toChiPosWholeLineRectangle := by
    intro n
    simpa [rectangles, Function.iterate_succ_apply'] using hnext (rectangles n)
  let gap : ℕ → ℝ := fun n =>
    (rectangles n).M ^ p.α - (rectangles n).ell ^ p.α
  have hgapStep : ∀ n, gap (n + 1) ≤ r * gap n + 2 * δ := by
    intro n
    simpa [gap, r] using
      chiPosWholeLineSupercriticalRectangleStep_gap_le
        (hrectangleStep n) hle hchi
  have hstationary : (2 * δ) / (1 - r) < epsilon := by
    have hne : 1 - r ≠ 0 := ne_of_gt h1r
    have heq : (2 * δ) / (1 - r) = epsilon / 2 := by
      dsimp [δ]
      field_simp
      ring
    rw [heq]
    linarith
  obtain ⟨n, hgap⟩ := exists_index_affine_recurrence_lt
    hr0 hr1 (mul_nonneg (by norm_num) hδ.le) hgapStep hstationary
  refine ⟨(rectangles n).start, ?_⟩
  intro t x ht
  have hrect := (rectangles n).bounds t ht x
  have habs := abs_sub_one_le_rpow_gap p.hα
    (rectangles n).ell_pos (rectangles n).ell_lt_one.le
    (rectangles n).one_lt_M.le hrect.1 hrect.2
  exact habs.trans_lt hgap

/-- In the strictly supercritical positive-sensitivity branch, every
uniformly positive datum converges uniformly to the constant equilibrium
one. -/
theorem wholeLineCauchyGlobal_uniformConvergesToConstant_one_of_chi_pos_half_supercritical
    (p : CMParams) (hchi : 0 < p.χ) (hchi_half : p.χ < 1 / 2)
    (hsuper : p.m + p.γ - 1 < p.α)
    (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (hpositive : UniformlyPositive u₀.1) :
    UniformConvergesToConstant (wholeLineCauchyGlobalU p u₀) 1 := by
  obtain ⟨seed⟩ := exists_initial_chiPosWholeLineSupercriticalRectangle
    p hchi hchi_half hsuper hregime u₀ hu₀ hpositive
  let Mstar : ℝ := chiPosEquilibriumCeiling p
  let G : ℝ := max Mstar ‖u₀‖
  have hMstar1 : 1 < Mstar := by
    dsimp [Mstar]
    exact chiPosEquilibriumCeiling_lt hchi hsuper
  have hG : 0 ≤ G :=
    (zero_lt_one.trans hMstar1).le.trans (le_max_left Mstar ‖u₀‖)
  have hglobal : ∀ t : ℝ, 0 ≤ t → ∀ x,
      wholeLineCauchyGlobalU p u₀ t x ≤ G := by
    intro t ht x
    exact wholeLineCauchyGlobal_le_max_equilibriumCeiling_of_chi_pos_supercritical
      p hchi hsuper u₀ hu₀ ht x
  apply uniformConvergesToConstant_one_of_supercritical_rectangle_successors
    p hchi.le hchi_half hsuper.le seed
  intro δ hδ old
  exact exists_next_chiPosWholeLineSupercriticalRectangle
    p hchi hchi_half hsuper hregime u₀ hu₀
      hpositive.strictlyPositiveAtLeft hG hglobal hδ old

section SupercriticalRectangleAxiomAudit

#print axioms chiPosWholeLineSupercriticalRectangleStep_gap_le
#print axioms uniformConvergesToConstant_one_of_supercritical_rectangle_successors
#print axioms wholeLineCauchyGlobal_uniformConvergesToConstant_one_of_chi_pos_half_supercritical

end SupercriticalRectangleAxiomAudit


end ShenWork.Paper1
