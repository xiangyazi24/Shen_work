import ShenWork.Paper1.WholeLineChiPosSqueezeAlgebra
import ShenWork.Paper1.WholeLineChiPosTargetCeilingNatural

open Filter Topology Real Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Scalar targets for the critical positive-sensitivity rectangle squeeze

This file isolates the one-dimensional algebra used in a rectangle round.  The
two gap functions are the residuals in the floor and ceiling target
inequalities.  At the critical exponent they are strictly monotone on the
positive half-line, which permits choosing two nested, positive-margin targets
arbitrarily close to their respective roots.  The final section supplies
positive exponential rates and the weighted scalar ODE inequalities used by
the PDE comparison arguments.
-/

/-- Residual in the floor equilibrium inequality with resolver ceiling
`M ^ p.γ`. -/
def chiPosFloorGap (p : CMParams) (M x : ℝ) : ℝ :=
  1 - x ^ p.α - p.χ * (x ^ (p.m - 1) * (M ^ p.γ - x ^ p.γ))

/-- Residual in the ceiling equilibrium inequality with resolver floor
`ell ^ p.γ`. -/
def chiPosCeilingGap (p : CMParams) (ell x : ℝ) : ℝ :=
  x ^ p.α - 1 - p.χ * (x ^ (p.m - 1) * (x ^ p.γ - ell ^ p.γ))

theorem chiPosFloorGap_critical
    {p : CMParams} {M x : ℝ} (hcritical : p.α = p.m + p.γ - 1)
    (hx : 0 < x) :
    chiPosFloorGap p M x =
      1 - (1 - p.χ) * x ^ p.α - p.χ * M ^ p.γ * x ^ (p.m - 1) := by
  have hpow : x ^ (p.m - 1) * x ^ p.γ = x ^ p.α := by
    rw [← Real.rpow_add hx]
    congr 1
    linarith
  unfold chiPosFloorGap
  rw [mul_sub]
  rw [hpow]
  ring

theorem chiPosCeilingGap_critical
    {p : CMParams} {ell x : ℝ} (hcritical : p.α = p.m + p.γ - 1)
    (hx : 0 < x) :
    chiPosCeilingGap p ell x =
      (1 - p.χ) * x ^ p.α + p.χ * ell ^ p.γ * x ^ (p.m - 1) - 1 := by
  have hpow : x ^ (p.m - 1) * x ^ p.γ = x ^ p.α := by
    rw [← Real.rpow_add hx]
    congr 1
    linarith
  unfold chiPosCeilingGap
  rw [mul_sub]
  rw [hpow]
  ring

theorem chiPosFloorGap_strictAntiOn_Ioi
    {p : CMParams} {M : ℝ} (hcritical : p.α = p.m + p.γ - 1)
    (hχ0 : 0 ≤ p.χ) (hχ1 : p.χ < 1) (hM : 0 ≤ M) :
    StrictAntiOn (chiPosFloorGap p M) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hαpos : 0 < p.α := lt_of_lt_of_le zero_lt_one p.hα
  have hm1 : 0 ≤ p.m - 1 := by linarith [p.hm]
  have hpowα : x ^ p.α < y ^ p.α :=
    Real.rpow_lt_rpow hx.le hxy hαpos
  have hpowm : x ^ (p.m - 1) ≤ y ^ (p.m - 1) :=
    Real.rpow_le_rpow hx.le hxy.le hm1
  have hlead :
      (1 - p.χ) * x ^ p.α < (1 - p.χ) * y ^ p.α :=
    mul_lt_mul_of_pos_left hpowα (sub_pos.mpr hχ1)
  have htail :
      p.χ * M ^ p.γ * x ^ (p.m - 1) ≤
        p.χ * M ^ p.γ * y ^ (p.m - 1) :=
    mul_le_mul_of_nonneg_left hpowm
      (mul_nonneg hχ0 (Real.rpow_nonneg hM _))
  rw [chiPosFloorGap_critical hcritical hx,
    chiPosFloorGap_critical hcritical hy]
  linarith

theorem chiPosCeilingGap_strictMonoOn_Ioi
    {p : CMParams} {ell : ℝ} (hcritical : p.α = p.m + p.γ - 1)
    (hχ0 : 0 ≤ p.χ) (hχ1 : p.χ < 1) (hell : 0 ≤ ell) :
    StrictMonoOn (chiPosCeilingGap p ell) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hαpos : 0 < p.α := lt_of_lt_of_le zero_lt_one p.hα
  have hm1 : 0 ≤ p.m - 1 := by linarith [p.hm]
  have hpowα : x ^ p.α < y ^ p.α :=
    Real.rpow_lt_rpow hx.le hxy hαpos
  have hpowm : x ^ (p.m - 1) ≤ y ^ (p.m - 1) :=
    Real.rpow_le_rpow hx.le hxy.le hm1
  have hlead :
      (1 - p.χ) * x ^ p.α < (1 - p.χ) * y ^ p.α :=
    mul_lt_mul_of_pos_left hpowα (sub_pos.mpr hχ1)
  have htail :
      p.χ * ell ^ p.γ * x ^ (p.m - 1) ≤
        p.χ * ell ^ p.γ * y ^ (p.m - 1) :=
    mul_le_mul_of_nonneg_left hpowm
      (mul_nonneg hχ0 (Real.rpow_nonneg hell _))
  rw [chiPosCeilingGap_critical hcritical hx,
    chiPosCeilingGap_critical hcritical hy]
  linarith

theorem chiPosFloorGap_continuous (p : CMParams) (M : ℝ) :
    Continuous (chiPosFloorGap p M) := by
  have hα : Continuous (fun x : ℝ => x ^ p.α) :=
    Real.continuous_rpow_const (zero_le_one.trans p.hα)
  have hm : Continuous (fun x : ℝ => x ^ (p.m - 1)) :=
    Real.continuous_rpow_const (sub_nonneg.mpr p.hm)
  have hγ : Continuous (fun x : ℝ => x ^ p.γ) :=
    Real.continuous_rpow_const (zero_le_one.trans p.hγ)
  unfold chiPosFloorGap
  exact (continuous_const.sub hα).sub
    (continuous_const.mul (hm.mul (continuous_const.sub hγ)))

theorem chiPosCeilingGap_continuous (p : CMParams) (ell : ℝ) :
    Continuous (chiPosCeilingGap p ell) := by
  have hα : Continuous (fun x : ℝ => x ^ p.α) :=
    Real.continuous_rpow_const (zero_le_one.trans p.hα)
  have hm : Continuous (fun x : ℝ => x ^ (p.m - 1)) :=
    Real.continuous_rpow_const (sub_nonneg.mpr p.hm)
  have hγ : Continuous (fun x : ℝ => x ^ p.γ) :=
    Real.continuous_rpow_const (zero_le_one.trans p.hγ)
  unfold chiPosCeilingGap
  exact (hα.sub continuous_const).sub
    (continuous_const.mul (hm.mul (hγ.sub continuous_const)))

/-! ## Generic two-target selection near a monotone root -/

/-- For a continuous strictly decreasing function which crosses zero on an
interval, choose two ordered points on the positive side of the root; the
first residual is at most the prescribed error. -/
theorem exists_two_floor_targets
    {f : ℝ → ℝ} {lo hi δ : ℝ}
    (hlohi : lo < hi) (hδ : 0 < δ)
    (hcont : ContinuousOn f (Set.Icc lo hi))
    (_hanti : StrictAntiOn f (Set.Icc lo hi))
    (hlo : 0 < f lo) (hhi : f hi ≤ 0) :
    ∃ L Lraw, lo < L ∧ L < Lraw ∧ Lraw ≤ hi ∧
      0 < f Lraw ∧ f L ≤ δ := by
  let eta : ℝ := min (f lo / 2) (δ / 2)
  have heta : 0 < eta := lt_min (half_pos hlo) (half_pos hδ)
  have heta_lo : eta < f lo :=
    (min_le_left (f lo / 2) (δ / 2)).trans_lt (half_lt_self hlo)
  have heta_delta : eta ≤ δ := by
    calc eta ≤ δ / 2 := min_le_right _ _
      _ ≤ δ := by linarith
  have heta_mem : eta ∈ Set.Icc (f hi) (f lo) :=
    ⟨hhi.trans heta.le, heta_lo.le⟩
  rcases (intermediate_value_Icc' hlohi.le hcont) heta_mem with
    ⟨L, hLmem, hLval⟩
  have hloL : lo < L := by
    rcases hLmem.1.eq_or_lt with hEq | hlt
    · subst L
      linarith [hLval]
    · exact hlt
  have hcontL : ContinuousOn f (Set.Icc L hi) :=
    hcont.mono (by
      intro x hx
      exact ⟨hLmem.1.trans hx.1, hx.2⟩)
  have heta2_mem : eta / 2 ∈ Set.Icc (f hi) (f L) := by
    rw [hLval]
    exact ⟨hhi.trans (half_pos heta).le, (half_le_self heta.le)⟩
  rcases (intermediate_value_Icc' hLmem.2 hcontL) heta2_mem with
    ⟨Lraw, hLrawmem, hLrawval⟩
  have hLLraw : L < Lraw := by
    rcases hLrawmem.1.eq_or_lt with hEq | hlt
    · subst Lraw
      linarith [hLrawval, hLval]
    · exact hlt
  refine ⟨L, Lraw, hloL, hLLraw, hLrawmem.2, ?_, ?_⟩
  · rw [hLrawval]
    exact half_pos heta
  · rw [hLval]
    exact heta_delta

/-- Increasing counterpart of `exists_two_floor_targets`. -/
theorem exists_two_ceiling_targets
    {f : ℝ → ℝ} {lo hi δ : ℝ}
    (hlohi : lo < hi) (hδ : 0 < δ)
    (hcont : ContinuousOn f (Set.Icc lo hi))
    (_hmono : StrictMonoOn f (Set.Icc lo hi))
    (hlo : f lo ≤ 0) (hhi : 0 < f hi) :
    ∃ Araw A, lo ≤ Araw ∧ Araw < A ∧ A < hi ∧
      0 < f Araw ∧ f A ≤ δ := by
  let eta : ℝ := min (f hi / 2) (δ / 2)
  have heta : 0 < eta := lt_min (half_pos hhi) (half_pos hδ)
  have heta_hi : eta < f hi :=
    (min_le_left (f hi / 2) (δ / 2)).trans_lt (half_lt_self hhi)
  have heta_delta : eta ≤ δ := by
    calc eta ≤ δ / 2 := min_le_right _ _
      _ ≤ δ := by linarith
  have heta_mem : eta ∈ Set.Icc (f lo) (f hi) :=
    ⟨hlo.trans heta.le, heta_hi.le⟩
  rcases (intermediate_value_Icc hlohi.le hcont) heta_mem with
    ⟨A, hAmem, hAval⟩
  have hAhi : A < hi := by
    rcases hAmem.2.eq_or_lt with hEq | hlt
    · subst A
      linarith [hAval]
    · exact hlt
  have hcontA : ContinuousOn f (Set.Icc lo A) :=
    hcont.mono (by
      intro x hx
      exact ⟨hx.1, hx.2.trans hAmem.2⟩)
  have heta2_mem : eta / 2 ∈ Set.Icc (f lo) (f A) := by
    rw [hAval]
    exact ⟨hlo.trans (half_pos heta).le, half_le_self heta.le⟩
  rcases (intermediate_value_Icc hAmem.1 hcontA) heta2_mem with
    ⟨Araw, hArawmem, hArawval⟩
  have hArawA : Araw < A := by
    rcases hArawmem.2.eq_or_lt with hEq | hlt
    · subst Araw
      linarith [hArawval, hAval]
    · exact hlt
  refine ⟨Araw, A, hArawmem.1, hArawA, hAhi, ?_, ?_⟩
  · rw [hArawval]
    exact half_pos heta
  · rw [hAval]
    exact heta_delta

/-! ## Rectangle targets -/

theorem exists_chiPos_floor_targets
    {p : CMParams} {ell M δ : ℝ}
    (hcritical : p.α = p.m + p.γ - 1)
    (hχ0 : 0 ≤ p.χ) (hχ1 : p.χ < 1)
    (hell : 0 < ell) (hell1 : ell < 1) (h1M : 1 ≤ M)
    (hmargin : 0 < chiPosFloorGap p M ell) (hδ : 0 < δ) :
    ∃ L Lraw, ell < L ∧ L < Lraw ∧ Lraw ≤ 1 ∧
      0 < chiPosFloorGap p M Lraw ∧ chiPosFloorGap p M L ≤ δ := by
  apply exists_two_floor_targets hell1 hδ
      ((chiPosFloorGap_continuous p M).continuousOn)
  · exact (chiPosFloorGap_strictAntiOn_Ioi hcritical hχ0 hχ1
      (zero_le_one.trans h1M)).mono (by
      intro x hx
      exact hell.trans_le hx.1)
  · exact hmargin
  · rw [chiPosFloorGap_critical hcritical zero_lt_one]
    have hMpow : 1 ≤ M ^ p.γ := by
      simpa only [Real.one_rpow] using
        Real.rpow_le_rpow zero_le_one h1M (zero_le_one.trans p.hγ)
    simp only [Real.one_rpow]
    nlinarith

theorem exists_chiPos_ceiling_targets
    {p : CMParams} {ell M δ : ℝ}
    (hcritical : p.α = p.m + p.γ - 1)
    (hχ0 : 0 ≤ p.χ) (hχ1 : p.χ < 1)
    (hell : 0 < ell) (hell1 : ell < 1) (h1M : 1 < M)
    (hmargin : 0 < chiPosCeilingGap p ell M) (hδ : 0 < δ) :
    ∃ Araw A, 1 ≤ Araw ∧ Araw < A ∧ A < M ∧
      0 < chiPosCeilingGap p ell Araw ∧ chiPosCeilingGap p ell A ≤ δ := by
  apply exists_two_ceiling_targets h1M hδ
      ((chiPosCeilingGap_continuous p ell).continuousOn)
  · exact (chiPosCeilingGap_strictMonoOn_Ioi hcritical hχ0 hχ1 hell.le).mono (by
      intro x hx
      exact zero_lt_one.trans_le hx.1)
  · rw [chiPosCeilingGap_critical hcritical zero_lt_one]
    have hellpow : ell ^ p.γ < 1 := by
      simpa only [Real.one_rpow] using
        Real.rpow_lt_rpow hell.le hell1 (lt_of_lt_of_le zero_lt_one p.hγ)
    simp only [Real.one_rpow]
    nlinarith
  · exact hmargin

theorem chiPosFloorGap_le_iff_target_inequality
    {p : CMParams} {M L δ : ℝ} :
    chiPosFloorGap p M L ≤ δ ↔
      1 - L ^ p.α ≤
        p.χ * (L ^ (p.m - 1) * (M ^ p.γ - L ^ p.γ)) + δ := by
  unfold chiPosFloorGap
  constructor <;> intro h <;> linarith

theorem chiPosCeilingGap_le_iff_target_inequality
    {p : CMParams} {ell A δ : ℝ} :
    chiPosCeilingGap p ell A ≤ δ ↔
      A ^ p.α - 1 ≤
        p.χ * (A ^ (p.m - 1) * (A ^ p.γ - ell ^ p.γ)) + δ := by
  unfold chiPosCeilingGap
  constructor <;> intro h <;> linarith

/-- Lowering the resolver ceiling can only increase the floor residual. -/
theorem chiPosFloorGap_anti_resolver_ceiling
    {p : CMParams} {x M' M : ℝ}
    (hχ0 : 0 ≤ p.χ) (hx : 0 ≤ x) (hM' : 0 ≤ M') (hM'M : M' ≤ M) :
    chiPosFloorGap p M x ≤ chiPosFloorGap p M' x := by
  have hm1 : 0 ≤ p.m - 1 := by linarith [p.hm]
  have hMpow : M' ^ p.γ ≤ M ^ p.γ :=
    Real.rpow_le_rpow hM' hM'M (zero_le_one.trans p.hγ)
  have hxpow : 0 ≤ x ^ (p.m - 1) := Real.rpow_nonneg hx _
  unfold chiPosFloorGap
  have hprod :
      x ^ (p.m - 1) * (M' ^ p.γ - x ^ p.γ) ≤
        x ^ (p.m - 1) * (M ^ p.γ - x ^ p.γ) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_right hMpow _) hxpow
  nlinarith [mul_le_mul_of_nonneg_left hprod hχ0]

/-- Raising the resolver floor can only increase the ceiling residual. -/
theorem chiPosCeilingGap_mono_resolver_floor
    {p : CMParams} {ell ell' x : ℝ}
    (hχ0 : 0 ≤ p.χ) (hell : 0 ≤ ell) (hellell' : ell ≤ ell')
    (hx : 0 ≤ x) :
    chiPosCeilingGap p ell x ≤ chiPosCeilingGap p ell' x := by
  have hellpow : ell ^ p.γ ≤ ell' ^ p.γ :=
    Real.rpow_le_rpow hell hellell' (zero_le_one.trans p.hγ)
  have hxpow : 0 ≤ x ^ (p.m - 1) := Real.rpow_nonneg hx _
  unfold chiPosCeilingGap
  have hprod :
      x ^ (p.m - 1) * (x ^ p.γ - ell' ^ p.γ) ≤
        x ^ (p.m - 1) * (x ^ p.γ - ell ^ p.γ) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_left hellpow _) hxpow
  nlinarith [mul_le_mul_of_nonneg_left hprod hχ0]

/-- All scalar data produced by one alternating rectangle round.  `Lraw` and
`Araw` are strict-margin asymptotic barrier targets; `L` and `A` are the
finite-time bounds passed to the contraction step. -/
structure ChiPosRectangleRoundTargets
    (p : CMParams) (ell M δ : ℝ) where
  L : ℝ
  Lraw : ℝ
  Araw : ℝ
  A : ℝ
  ell_lt_L : ell < L
  L_lt_Lraw : L < Lraw
  Lraw_le_one : Lraw ≤ 1
  one_le_Araw : 1 ≤ Araw
  Araw_lt_A : Araw < A
  A_lt_M : A < M
  floor_raw_margin : 0 < chiPosFloorGap p M Lraw
  floor_delta :
    1 - L ^ p.α ≤
      p.χ * (L ^ (p.m - 1) * (M ^ p.γ - L ^ p.γ)) + δ
  ceiling_raw_margin : 0 < chiPosCeilingGap p L Araw
  ceiling_delta :
    A ^ p.α - 1 ≤
      p.χ * (A ^ (p.m - 1) * (A ^ p.γ - L ^ p.γ)) + δ
  next_floor_margin : 0 < chiPosFloorGap p A L
  next_ceiling_margin : 0 < chiPosCeilingGap p L A

/-- Coupled target selection for a full rectangle round.  The old endpoint
strict margins propagate to strict margins for the new rectangle `[L,A]`. -/
theorem exists_chiPos_rectangle_round_targets
    {p : CMParams} {ell M δ : ℝ}
    (hcritical : p.α = p.m + p.γ - 1)
    (hχ0 : 0 ≤ p.χ) (hχ1 : p.χ < 1)
    (hell : 0 < ell) (hell1 : ell < 1) (h1M : 1 < M)
    (hfloorMargin : 0 < chiPosFloorGap p M ell)
    (hceilingMargin : 0 < chiPosCeilingGap p ell M)
    (hδ : 0 < δ) :
    Nonempty (ChiPosRectangleRoundTargets p ell M δ) := by
  rcases exists_chiPos_floor_targets hcritical hχ0 hχ1 hell hell1 h1M.le
      hfloorMargin hδ with
    ⟨L, Lraw, hellL, hLLraw, hLraw1, hfloorRaw, hfloorδgap⟩
  have hceilMarginL : 0 < chiPosCeilingGap p L M :=
    hceilingMargin.trans_le
      (chiPosCeilingGap_mono_resolver_floor hχ0 hell.le hellL.le
        (zero_le_one.trans h1M.le))
  rcases exists_chiPos_ceiling_targets hcritical hχ0 hχ1
      (hell.trans hellL) (hLLraw.trans_le hLraw1) h1M
      hceilMarginL hδ with
    ⟨Araw, A, h1Araw, hArawA, hAM, hceilRaw, hceilδgap⟩
  have hfloorAtL : 0 < chiPosFloorGap p M L := by
    have hLpos : L ∈ Set.Ioi (0 : ℝ) := hell.trans hellL
    have hLrawpos : Lraw ∈ Set.Ioi (0 : ℝ) := hLpos.trans hLLraw
    exact hfloorRaw.trans
      (chiPosFloorGap_strictAntiOn_Ioi hcritical hχ0 hχ1
        (zero_le_one.trans h1M.le)
        hLpos hLrawpos hLLraw)
  have hA0 : 0 ≤ A := zero_le_one.trans (h1Araw.trans hArawA.le)
  have hnextFloor : 0 < chiPosFloorGap p A L :=
    hfloorAtL.trans_le
      (chiPosFloorGap_anti_resolver_ceiling hχ0 (hell.trans hellL).le
        hA0 hAM.le)
  have hnextCeil : 0 < chiPosCeilingGap p L A := by
    have hArawpos : Araw ∈ Set.Ioi (0 : ℝ) := zero_lt_one.trans_le h1Araw
    have hApos : A ∈ Set.Ioi (0 : ℝ) := hArawpos.trans hArawA
    exact hceilRaw.trans
      (chiPosCeilingGap_strictMonoOn_Ioi hcritical hχ0 hχ1
        (hell.trans hellL).le
        hArawpos hApos hArawA)
  exact ⟨
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
        chiPosFloorGap_le_iff_target_inequality.mp hfloorδgap
      ceiling_raw_margin := hceilRaw
      ceiling_delta :=
        chiPosCeilingGap_le_iff_target_inequality.mp hceilδgap
      next_floor_margin := hnextFloor
      next_ceiling_margin := hnextCeil }⟩

/-! ## Weighted exponential barriers -/

/-- Positive floor relaxation rate retaining the full `b ^ m` chemotactic
weight. -/
def chiPosRectangleFloorRate (p : CMParams) (M C L : ℝ) : ℝ :=
  C * chiPosFloorGap p M L / (L - C + 1)

theorem chiPosRectangleFloorRate_pos
    {p : CMParams} {M C L : ℝ}
    (hC : 0 < C) (hCL : C < L) (hgap : 0 < chiPosFloorGap p M L) :
    0 < chiPosRectangleFloorRate p M C L := by
  unfold chiPosRectangleFloorRate
  exact div_pos (mul_pos hC hgap) (by linarith)

theorem chiPosRectangleFloorRate_mul_gap_le
    {p : CMParams} {M C L : ℝ}
    (hC : 0 < C) (hCL : C < L) (hgap : 0 < chiPosFloorGap p M L) :
    chiPosRectangleFloorRate p M C L * (L - C) ≤
      C * chiPosFloorGap p M L := by
  have hden : 0 < L - C + 1 := by linarith
  have hfrac : (L - C) / (L - C + 1) ≤ 1 :=
    (div_le_one hden).2 (by linarith)
  unfold chiPosRectangleFloorRate
  calc
    (C * chiPosFloorGap p M L / (L - C + 1)) * (L - C) =
        (C * chiPosFloorGap p M L) * ((L - C) / (L - C + 1)) := by ring
    _ ≤ (C * chiPosFloorGap p M L) * 1 :=
      mul_le_mul_of_nonneg_left hfrac (mul_pos hC hgap).le
    _ = C * chiPosFloorGap p M L := mul_one _

/-- The target-capped floor is a subsolution after retaining the weighted
resolver-ceiling defect `χ b^m (M^γ-b^γ)`. -/
theorem chiZeroKPPFloor_weighted_subsolution
    {p : CMParams} {M C L t : ℝ}
    (hcritical : p.α = p.m + p.γ - 1)
    (hχ0 : 0 ≤ p.χ) (hχ1 : p.χ < 1)
    (hC : 0 < C) (hCL : C < L) (hL1 : L ≤ 1) (h1M : 1 ≤ M)
    (hgap : 0 < chiPosFloorGap p M L) (ht : 0 ≤ t) :
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
  have hBmem : B ∈ Set.Ioi (0 : ℝ) := hBpos
  have hLmem : L ∈ Set.Ioi (0 : ℝ) := hC.trans hCL
  have hgapMono : chiPosFloorGap p M L ≤ chiPosFloorGap p M B := by
    by_cases hEq : B = L
    · simp [hEq]
    · exact (chiPosFloorGap_strictAntiOn_Ioi hcritical hχ0 hχ1
        (zero_le_one.trans h1M)
        hBmem hLmem (lt_of_le_of_ne hBle hEq)).le
  have htime : lam * (L - B) ≤ lam * (L - C) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_left hBge L) hlam.le
  have hbudget : lam * (L - C) ≤ C * chiPosFloorGap p M L := by
    simpa [lam] using chiPosRectangleFloorRate_mul_gap_le hC hCL hgap
  have hprod :
      C * chiPosFloorGap p M L ≤ B * chiPosFloorGap p M B := by
    calc
      C * chiPosFloorGap p M L ≤ B * chiPosFloorGap p M L :=
        mul_le_mul_of_nonneg_right hBge hgap.le
      _ ≤ B * chiPosFloorGap p M B :=
        mul_le_mul_of_nonneg_left hgapMono hBpos.le
  have hweighted :
      B * chiPosFloorGap p M B =
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

/-- Positive ceiling relaxation rate retaining the full `a ^ m` chemotactic
weight. -/
def chiPosRectangleCeilingRate (p : CMParams) (ell A D : ℝ) : ℝ :=
  A * chiPosCeilingGap p ell A / (D - A + 1)

theorem chiPosRectangleCeilingRate_pos
    {p : CMParams} {ell A D : ℝ}
    (hA : 0 < A) (hAD : A < D) (hgap : 0 < chiPosCeilingGap p ell A) :
    0 < chiPosRectangleCeilingRate p ell A D := by
  unfold chiPosRectangleCeilingRate
  exact div_pos (mul_pos hA hgap) (by linarith)

theorem chiPosRectangleCeilingRate_mul_gap_le
    {p : CMParams} {ell A D : ℝ}
    (hA : 0 < A) (hAD : A < D) (hgap : 0 < chiPosCeilingGap p ell A) :
    chiPosRectangleCeilingRate p ell A D * (D - A) ≤
      A * chiPosCeilingGap p ell A := by
  have hden : 0 < D - A + 1 := by linarith
  have hfrac : (D - A) / (D - A + 1) ≤ 1 :=
    (div_le_one hden).2 (by linarith)
  unfold chiPosRectangleCeilingRate
  calc
    (A * chiPosCeilingGap p ell A / (D - A + 1)) * (D - A) =
        (A * chiPosCeilingGap p ell A) * ((D - A) / (D - A + 1)) := by ring
    _ ≤ (A * chiPosCeilingGap p ell A) * 1 :=
      mul_le_mul_of_nonneg_left hfrac (mul_pos hA hgap).le
    _ = A * chiPosCeilingGap p ell A := mul_one _

/-- The target-capped ceiling is a supersolution after retaining the weighted
resolver-floor contribution `χ a^m (a^γ-ell^γ)`. -/
theorem chiPosTargetCeiling_weighted_supersolution
    {p : CMParams} {ell A D t : ℝ}
    (hcritical : p.α = p.m + p.γ - 1)
    (hχ0 : 0 ≤ p.χ) (hχ1 : p.χ < 1)
    (hell : 0 < ell) (hell1 : ell ≤ 1) (h1A : 1 ≤ A) (hAD : A < D)
    (hgap : 0 < chiPosCeilingGap p ell A) (ht : 0 ≤ t) :
    reactionFun p.α
        (chiPosTargetCeiling A D (chiPosRectangleCeilingRate p ell A D) t) +
        p.χ * (chiPosTargetCeiling A D
          (chiPosRectangleCeilingRate p ell A D) t) ^ p.m *
          ((chiPosTargetCeiling A D
            (chiPosRectangleCeilingRate p ell A D) t) ^ p.γ - ell ^ p.γ) ≤
      deriv (chiPosTargetCeiling A D
        (chiPosRectangleCeilingRate p ell A D)) t := by
  let lam : ℝ := chiPosRectangleCeilingRate p ell A D
  let B : ℝ := chiPosTargetCeiling A D lam t
  have hApos : 0 < A := zero_lt_one.trans_le h1A
  have hlam : 0 < lam := chiPosRectangleCeilingRate_pos hApos hAD hgap
  have hBderiv : deriv (chiPosTargetCeiling A D lam) t = -lam * (B - A) := by
    simpa [B] using (chiPosTargetCeiling_hasDerivAt A D lam t).deriv
  have hBge : A ≤ B := chiPosTargetCeiling_ge_target hAD.le
  have hBle : B ≤ D := chiPosTargetCeiling_le_start hAD.le hlam.le ht
  have hBpos : 0 < B := hApos.trans_le hBge
  have hAmem : A ∈ Set.Ioi (0 : ℝ) := hApos
  have hBmem : B ∈ Set.Ioi (0 : ℝ) := hBpos
  have hgapMono : chiPosCeilingGap p ell A ≤ chiPosCeilingGap p ell B := by
    by_cases hEq : A = B
    · simp [hEq]
    · exact (chiPosCeilingGap_strictMonoOn_Ioi hcritical hχ0 hχ1 hell.le
        hAmem hBmem (lt_of_le_of_ne hBge hEq)).le
  have htime : lam * (B - A) ≤ lam * (D - A) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_right hBle A) hlam.le
  have hbudget : lam * (D - A) ≤ A * chiPosCeilingGap p ell A := by
    simpa [lam] using chiPosRectangleCeilingRate_mul_gap_le hApos hAD hgap
  have hprod :
      A * chiPosCeilingGap p ell A ≤ B * chiPosCeilingGap p ell B := by
    calc
      A * chiPosCeilingGap p ell A ≤ B * chiPosCeilingGap p ell A :=
        mul_le_mul_of_nonneg_right hBge hgap.le
      _ ≤ B * chiPosCeilingGap p ell B :=
        mul_le_mul_of_nonneg_left hgapMono hBpos.le
  have hweighted :
      reactionFun p.α B + p.χ * B ^ p.m * (B ^ p.γ - ell ^ p.γ) =
        -(B * chiPosCeilingGap p ell B) := by
    have hm : B * B ^ (p.m - 1) = B ^ p.m :=
      mul_rpow_sub_one p.m p.hm hBpos.le
    have hgapExpand :
        B * chiPosCeilingGap p ell B =
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

/-! ## Round-target convenience wrappers -/

/-- The floor raw target packaged by a rectangle round carries its weighted
ODE budget, starting from the old floor `ell`. -/
theorem ChiPosRectangleRoundTargets.floor_weighted_subsolution
    {p : CMParams} {ell M δ t : ℝ}
    (r : ChiPosRectangleRoundTargets p ell M δ)
    (hcritical : p.α = p.m + p.γ - 1)
    (hχ0 : 0 ≤ p.χ) (hχ1 : p.χ < 1)
    (hell : 0 < ell) (h1M : 1 ≤ M) (ht : 0 ≤ t) :
    deriv (chiZeroKPPFloor ell r.Lraw
      (chiPosRectangleFloorRate p M ell r.Lraw)) t +
        p.χ * (chiZeroKPPFloor ell r.Lraw
          (chiPosRectangleFloorRate p M ell r.Lraw) t) ^ p.m *
          (M ^ p.γ - (chiZeroKPPFloor ell r.Lraw
            (chiPosRectangleFloorRate p M ell r.Lraw) t) ^ p.γ) ≤
      reactionFun p.α
        (chiZeroKPPFloor ell r.Lraw
          (chiPosRectangleFloorRate p M ell r.Lraw) t) := by
  exact chiZeroKPPFloor_weighted_subsolution hcritical hχ0 hχ1 hell
    (r.ell_lt_L.trans r.L_lt_Lraw) r.Lraw_le_one h1M
    r.floor_raw_margin ht

/-- The ceiling raw target packaged by a rectangle round carries its weighted
ODE budget, starting from the old ceiling `M` and using the new floor `L`. -/
theorem ChiPosRectangleRoundTargets.ceiling_weighted_supersolution
    {p : CMParams} {ell M δ t : ℝ}
    (r : ChiPosRectangleRoundTargets p ell M δ)
    (hcritical : p.α = p.m + p.γ - 1)
    (hχ0 : 0 ≤ p.χ) (hχ1 : p.χ < 1)
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
  exact chiPosTargetCeiling_weighted_supersolution hcritical hχ0 hχ1
    (hell.trans r.ell_lt_L)
    (r.L_lt_Lraw.le.trans r.Lraw_le_one) r.one_le_Araw
    (r.Araw_lt_A.trans r.A_lt_M) r.ceiling_raw_margin ht

section AxiomAudit

#print axioms chiPosFloorGap_critical
#print axioms chiPosCeilingGap_critical
#print axioms chiPosFloorGap_strictAntiOn_Ioi
#print axioms chiPosCeilingGap_strictMonoOn_Ioi
#print axioms exists_two_floor_targets
#print axioms exists_two_ceiling_targets
#print axioms exists_chiPos_floor_targets
#print axioms exists_chiPos_ceiling_targets
#print axioms chiPosFloorGap_anti_resolver_ceiling
#print axioms chiPosCeilingGap_mono_resolver_floor
#print axioms exists_chiPos_rectangle_round_targets
#print axioms chiPosRectangleFloorRate_pos
#print axioms chiZeroKPPFloor_weighted_subsolution
#print axioms chiPosRectangleCeilingRate_pos
#print axioms chiPosTargetCeiling_weighted_supersolution
#print axioms ChiPosRectangleRoundTargets.floor_weighted_subsolution
#print axioms ChiPosRectangleRoundTargets.ceiling_weighted_supersolution

end AxiomAudit

end ShenWork.Paper1
