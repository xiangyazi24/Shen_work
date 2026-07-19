import ShenWork.Paper1.WholeLineChiPosHalfLineRectangle
import ShenWork.Paper1.WholeLineChiPosRectangleTargets

open Filter Topology Real Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Scalar targets for a buffered positive-sensitivity half-line round

The finite rectangle endpoints `L` and `A` are kept separate from the
asymptotic barrier targets `Lraw` and `Araw`.  The former spend half of the
round budget, while the latter retain the strict scalar margins needed by the
exponential barriers.
-/

/-- Target data for one buffered half-line round.  Its inherited rectangle
target uses `delta / 2`; the additional fields expose the strict finite-target
bounds, the finite gap estimates, and positivity of the unbuffered barrier
rates. -/
structure ChiPosHalfLineRoundTargets
    (p : CMParams) (ell M delta : ℝ) extends
      ChiPosRectangleRoundTargets p ell M (delta / 2) where
  L_lt_one : L < 1
  one_lt_A : 1 < A
  floor_gap_pos : 0 < chiPosFloorGap p M L
  floor_gap_le_half : chiPosFloorGap p M L ≤ delta / 2
  ceiling_gap_pos : 0 < chiPosCeilingGap p L A
  ceiling_gap_le_half : chiPosCeilingGap p L A ≤ delta / 2
  Lraw_lt_one : Lraw < 1
  one_lt_Araw : 1 < Araw
  floor_rate_pos :
    0 < chiPosRectangleFloorRate p M ell Lraw
  ceiling_rate_pos :
    0 < chiPosRectangleCeilingRate p L Araw M

/-- Select the finite and raw targets for a half-line successor.  The existing
coupled rectangle selector is invoked with `delta / 2`, leaving the other half
of the successor budget for the resolver tail. -/
theorem exists_chiPos_halfLine_round_targets
    {p : CMParams} {c : ℝ} {u : ℝ → ℝ → ℝ} {delta : ℝ}
    (hcritical : p.α = p.m + p.γ - 1)
    (hchi0 : 0 ≤ p.χ) (hchi1 : p.χ < 1)
    (hdelta : 0 < delta) (old : ChiPosHalfLineRectangle p c u) :
    Nonempty (ChiPosHalfLineRoundTargets p old.ell old.M delta) := by
  obtain ⟨r⟩ := exists_chiPos_rectangle_round_targets
    hcritical hchi0 hchi1 old.ell_pos old.ell_lt_one old.one_lt_M
      old.floor_margin old.ceiling_margin (half_pos hdelta)
  have hLpos : 0 < r.L := old.ell_pos.trans r.ell_lt_L
  have hLrawpos : 0 < r.Lraw := hLpos.trans r.L_lt_Lraw
  have hL_lt_one : r.L < 1 := r.L_lt_Lraw.trans_le r.Lraw_le_one
  have hfloor_gap_pos : 0 < chiPosFloorGap p old.M r.L :=
    r.floor_raw_margin.trans
      (chiPosFloorGap_strictAntiOn_Ioi hcritical hchi0 hchi1
        (zero_le_one.trans old.one_lt_M.le)
        hLpos hLrawpos r.L_lt_Lraw)
  have hfloor_gap_le : chiPosFloorGap p old.M r.L ≤ delta / 2 :=
    chiPosFloorGap_le_iff_target_inequality.mpr r.floor_delta
  have hceiling_gap_le : chiPosCeilingGap p r.L r.A ≤ delta / 2 :=
    chiPosCeilingGap_le_iff_target_inequality.mpr r.ceiling_delta
  have hfloor_one : chiPosFloorGap p old.M 1 ≤ 0 := by
    rw [chiPosFloorGap_critical hcritical zero_lt_one]
    have hMpow : 1 ≤ old.M ^ p.γ := by
      simpa only [Real.one_rpow] using
        Real.rpow_le_rpow zero_le_one old.one_lt_M.le
          (zero_le_one.trans p.hγ)
    simp only [Real.one_rpow]
    nlinarith
  have hLraw_lt_one : r.Lraw < 1 := by
    rcases r.Lraw_le_one.eq_or_lt with hEq | hlt
    · have hraw := r.floor_raw_margin
      rw [hEq] at hraw
      linarith
    · exact hlt
  have hceiling_one : chiPosCeilingGap p r.L 1 ≤ 0 := by
    rw [chiPosCeilingGap_critical hcritical zero_lt_one]
    have hLpow : r.L ^ p.γ ≤ 1 := by
      simpa only [Real.one_rpow] using
        Real.rpow_le_rpow hLpos.le hL_lt_one.le
          (zero_le_one.trans p.hγ)
    simp only [Real.one_rpow]
    nlinarith
  have hone_lt_Araw : 1 < r.Araw := by
    rcases r.one_le_Araw.eq_or_lt with hEq | hlt
    · have hraw := r.ceiling_raw_margin
      rw [← hEq] at hraw
      linarith
    · exact hlt
  have hone_lt_A : 1 < r.A := hone_lt_Araw.trans r.Araw_lt_A
  have hfloor_rate :
      0 < chiPosRectangleFloorRate p old.M old.ell r.Lraw :=
    chiPosRectangleFloorRate_pos old.ell_pos
      (r.ell_lt_L.trans r.L_lt_Lraw) r.floor_raw_margin
  have hceiling_rate :
      0 < chiPosRectangleCeilingRate p r.L r.Araw old.M :=
    chiPosRectangleCeilingRate_pos (zero_lt_one.trans hone_lt_Araw)
      (r.Araw_lt_A.trans r.A_lt_M) r.ceiling_raw_margin
  exact ⟨
    { r with
      L_lt_one := hL_lt_one
      one_lt_A := hone_lt_A
      floor_gap_pos := hfloor_gap_pos
      floor_gap_le_half := hfloor_gap_le
      ceiling_gap_pos := r.next_ceiling_margin
      ceiling_gap_le_half := hceiling_gap_le
      Lraw_lt_one := hLraw_lt_one
      one_lt_Araw := hone_lt_Araw
      floor_rate_pos := hfloor_rate
      ceiling_rate_pos := hceiling_rate }⟩

/-! ## Tail-adjusted floor barrier -/

/-- The floor gap remaining after paying the far-field resolver tail. -/
def chiPosHalfLineFloorReserve
    (p : CMParams) (M L tau G : ℝ) : ℝ :=
  chiPosFloorGap p M L -
    p.χ * L ^ (p.m - 1) * tau * G ^ p.γ

theorem chiPosHalfLineFloorReserve_pos_of_tail_lt
    {p : CMParams} {M L tau G : ℝ}
    (htail : p.χ * L ^ (p.m - 1) * tau * G ^ p.γ <
      chiPosFloorGap p M L) :
    0 < chiPosHalfLineFloorReserve p M L tau G := by
  unfold chiPosHalfLineFloorReserve
  linarith

/-- Floor relaxation rate obtained from the tail-adjusted reserve. -/
def chiPosHalfLineFloorRate
    (p : CMParams) (M C L tau G : ℝ) : ℝ :=
  C * chiPosHalfLineFloorReserve p M L tau G / (L - C + 1)

theorem chiPosHalfLineFloorRate_pos
    {p : CMParams} {M C L tau G : ℝ}
    (hC : 0 < C) (hCL : C < L)
    (hreserve : 0 < chiPosHalfLineFloorReserve p M L tau G) :
    0 < chiPosHalfLineFloorRate p M C L tau G := by
  unfold chiPosHalfLineFloorRate
  exact div_pos (mul_pos hC hreserve) (by linarith)

theorem chiPosHalfLineFloorRate_mul_relaxation_le
    {p : CMParams} {M C L tau G : ℝ}
    (hC : 0 < C) (hCL : C < L)
    (hreserve : 0 < chiPosHalfLineFloorReserve p M L tau G) :
    chiPosHalfLineFloorRate p M C L tau G * (L - C) ≤
      C * chiPosHalfLineFloorReserve p M L tau G := by
  have hden : 0 < L - C + 1 := by linarith
  have hfrac : (L - C) / (L - C + 1) ≤ 1 :=
    (div_le_one hden).2 (by linarith)
  unfold chiPosHalfLineFloorRate
  calc
    (C * chiPosHalfLineFloorReserve p M L tau G / (L - C + 1)) *
          (L - C) =
        (C * chiPosHalfLineFloorReserve p M L tau G) *
          ((L - C) / (L - C + 1)) := by ring
    _ ≤ (C * chiPosHalfLineFloorReserve p M L tau G) * 1 :=
      mul_le_mul_of_nonneg_left hfrac (mul_pos hC hreserve).le
    _ = C * chiPosHalfLineFloorReserve p M L tau G := mul_one _

/-- The target-capped floor pays both the local resolver-ceiling defect and
the weighted far-field tail `chi * b^m * tau * G^gamma`. -/
theorem chiZeroKPPFloor_tail_weighted_subsolution
    {p : CMParams} {M C L tau G t : ℝ}
    (hcritical : p.α = p.m + p.γ - 1)
    (hchi0 : 0 ≤ p.χ) (hchi1 : p.χ < 1)
    (hC : 0 < C) (hCL : C < L) (_hL1 : L ≤ 1) (h1M : 1 ≤ M)
    (htau : 0 ≤ tau) (hG : 0 ≤ G)
    (hreserve : 0 < chiPosHalfLineFloorReserve p M L tau G)
    (ht : 0 ≤ t) :
    deriv (chiZeroKPPFloor C L
        (chiPosHalfLineFloorRate p M C L tau G)) t +
        p.χ * (chiZeroKPPFloor C L
          (chiPosHalfLineFloorRate p M C L tau G) t) ^ p.m *
          (M ^ p.γ - (chiZeroKPPFloor C L
            (chiPosHalfLineFloorRate p M C L tau G) t) ^ p.γ) +
        p.χ * (chiZeroKPPFloor C L
          (chiPosHalfLineFloorRate p M C L tau G) t) ^ p.m *
          tau * G ^ p.γ ≤
      reactionFun p.α
        (chiZeroKPPFloor C L
          (chiPosHalfLineFloorRate p M C L tau G) t) := by
  let lam : ℝ := chiPosHalfLineFloorRate p M C L tau G
  let B : ℝ := chiZeroKPPFloor C L lam t
  have hlam : 0 < lam :=
    chiPosHalfLineFloorRate_pos hC hCL hreserve
  have hBderiv : deriv (chiZeroKPPFloor C L lam) t = lam * (L - B) := by
    simpa [B] using (chiZeroKPPFloor_hasDerivAt C L lam t).deriv
  have hBge : C ≤ B := chiZeroKPPFloor_ge_start hCL.le hlam.le ht
  have hBle : B ≤ L := chiZeroKPPFloor_le_target hCL.le
  have hBpos : 0 < B := hC.trans_le hBge
  have hgapMono : chiPosFloorGap p M L ≤ chiPosFloorGap p M B := by
    by_cases hEq : B = L
    · simp [hEq]
    · exact (chiPosFloorGap_strictAntiOn_Ioi hcritical hchi0 hchi1
        (zero_le_one.trans h1M)
        hBpos (hC.trans hCL) (lt_of_le_of_ne hBle hEq)).le
  have hpowMono : B ^ (p.m - 1) ≤ L ^ (p.m - 1) :=
    Real.rpow_le_rpow hBpos.le hBle (sub_nonneg.mpr p.hm)
  have htailMono :
      p.χ * B ^ (p.m - 1) * tau * G ^ p.γ ≤
        p.χ * L ^ (p.m - 1) * tau * G ^ p.γ := by
    have hcoef : 0 ≤ p.χ * tau * G ^ p.γ :=
      mul_nonneg (mul_nonneg hchi0 htau) (Real.rpow_nonneg hG _)
    calc
      p.χ * B ^ (p.m - 1) * tau * G ^ p.γ =
          (p.χ * tau * G ^ p.γ) * B ^ (p.m - 1) := by ring
      _ ≤ (p.χ * tau * G ^ p.γ) * L ^ (p.m - 1) :=
        mul_le_mul_of_nonneg_left hpowMono hcoef
      _ = p.χ * L ^ (p.m - 1) * tau * G ^ p.γ := by ring
  have hreserveMono :
      chiPosHalfLineFloorReserve p M L tau G ≤
        chiPosHalfLineFloorReserve p M B tau G := by
    unfold chiPosHalfLineFloorReserve
    linarith
  have htime : lam * (L - B) ≤ lam * (L - C) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_left hBge L) hlam.le
  have hbudget :
      lam * (L - C) ≤
        C * chiPosHalfLineFloorReserve p M L tau G := by
    simpa [lam] using
      chiPosHalfLineFloorRate_mul_relaxation_le hC hCL hreserve
  have hprod :
      C * chiPosHalfLineFloorReserve p M L tau G ≤
        B * chiPosHalfLineFloorReserve p M B tau G := by
    calc
      C * chiPosHalfLineFloorReserve p M L tau G ≤
          B * chiPosHalfLineFloorReserve p M L tau G :=
        mul_le_mul_of_nonneg_right hBge hreserve.le
      _ ≤ B * chiPosHalfLineFloorReserve p M B tau G :=
        mul_le_mul_of_nonneg_left hreserveMono hBpos.le
  have hm : B * B ^ (p.m - 1) = B ^ p.m :=
    mul_rpow_sub_one p.m p.hm hBpos.le
  have hbase :
      B * chiPosFloorGap p M B =
        reactionFun p.α B -
          p.χ * B ^ p.m * (M ^ p.γ - B ^ p.γ) := by
    unfold chiPosFloorGap reactionFun
    calc
      B * (1 - B ^ p.α -
          p.χ * (B ^ (p.m - 1) * (M ^ p.γ - B ^ p.γ))) =
          B * (1 - B ^ p.α) -
            p.χ * (B * B ^ (p.m - 1)) *
              (M ^ p.γ - B ^ p.γ) := by ring
      _ = B * (1 - B ^ p.α) -
          p.χ * B ^ p.m * (M ^ p.γ - B ^ p.γ) := by rw [hm]
  have hweighted :
      B * chiPosHalfLineFloorReserve p M B tau G =
        reactionFun p.α B -
          p.χ * B ^ p.m * (M ^ p.γ - B ^ p.γ) -
          p.χ * B ^ p.m * tau * G ^ p.γ := by
    unfold chiPosHalfLineFloorReserve
    rw [mul_sub, hbase]
    rw [show B * (p.χ * B ^ (p.m - 1) * tau * G ^ p.γ) =
        p.χ * B ^ p.m * tau * G ^ p.γ by rw [← hm]; ring]
  change deriv (chiZeroKPPFloor C L lam) t +
      p.χ * B ^ p.m * (M ^ p.γ - B ^ p.γ) +
      p.χ * B ^ p.m * tau * G ^ p.γ ≤ reactionFun p.α B
  rw [hBderiv]
  linarith [htime, hbudget, hprod, hweighted]

/-! ## Tail-adjusted ceiling barrier -/

/-- The ceiling gap remaining after reserving the worst barrier-height tail
over the interval from `A` to `D`. -/
def chiPosHalfLineCeilingReserve
    (p : CMParams) (ell A D tau : ℝ) : ℝ :=
  chiPosCeilingGap p ell A -
    p.χ * D ^ (p.m - 1) * tau * ell ^ p.γ

theorem chiPosHalfLineCeilingReserve_pos_of_tail_lt
    {p : CMParams} {ell A D tau : ℝ}
    (htail : p.χ * D ^ (p.m - 1) * tau * ell ^ p.γ <
      chiPosCeilingGap p ell A) :
    0 < chiPosHalfLineCeilingReserve p ell A D tau := by
  unfold chiPosHalfLineCeilingReserve
  linarith

/-- Ceiling relaxation rate obtained from the tail-adjusted reserve. -/
def chiPosHalfLineCeilingRate
    (p : CMParams) (ell A D tau : ℝ) : ℝ :=
  A * chiPosHalfLineCeilingReserve p ell A D tau / (D - A + 1)

theorem chiPosHalfLineCeilingRate_pos
    {p : CMParams} {ell A D tau : ℝ}
    (hA : 0 < A) (hAD : A < D)
    (hreserve : 0 < chiPosHalfLineCeilingReserve p ell A D tau) :
    0 < chiPosHalfLineCeilingRate p ell A D tau := by
  unfold chiPosHalfLineCeilingRate
  exact div_pos (mul_pos hA hreserve) (by linarith)

theorem chiPosHalfLineCeilingRate_mul_relaxation_le
    {p : CMParams} {ell A D tau : ℝ}
    (hA : 0 < A) (hAD : A < D)
    (hreserve : 0 < chiPosHalfLineCeilingReserve p ell A D tau) :
    chiPosHalfLineCeilingRate p ell A D tau * (D - A) ≤
      A * chiPosHalfLineCeilingReserve p ell A D tau := by
  have hden : 0 < D - A + 1 := by linarith
  have hfrac : (D - A) / (D - A + 1) ≤ 1 :=
    (div_le_one hden).2 (by linarith)
  unfold chiPosHalfLineCeilingRate
  calc
    (A * chiPosHalfLineCeilingReserve p ell A D tau / (D - A + 1)) *
          (D - A) =
        (A * chiPosHalfLineCeilingReserve p ell A D tau) *
          ((D - A) / (D - A + 1)) := by ring
    _ ≤ (A * chiPosHalfLineCeilingReserve p ell A D tau) * 1 :=
      mul_le_mul_of_nonneg_left hfrac (mul_pos hA hreserve).le
    _ = A * chiPosHalfLineCeilingReserve p ell A D tau := mul_one _

/-- The target-capped ceiling pays both the local resolver-floor contribution
and the weighted tail `chi * a^m * tau * ell^gamma`.  The rate reserve uses
`D^(m-1)`, which controls every barrier value between `A` and `D`. -/
theorem chiPosTargetCeiling_tail_weighted_supersolution
    {p : CMParams} {ell A D tau t : ℝ}
    (hcritical : p.α = p.m + p.γ - 1)
    (hchi0 : 0 ≤ p.χ) (hchi1 : p.χ < 1)
    (hell : 0 < ell) (_hell1 : ell ≤ 1)
    (h1A : 1 ≤ A) (hAD : A < D) (htau : 0 ≤ tau)
    (hreserve : 0 < chiPosHalfLineCeilingReserve p ell A D tau)
    (ht : 0 ≤ t) :
    reactionFun p.α
        (chiPosTargetCeiling A D
          (chiPosHalfLineCeilingRate p ell A D tau) t) +
        p.χ * (chiPosTargetCeiling A D
          (chiPosHalfLineCeilingRate p ell A D tau) t) ^ p.m *
          ((chiPosTargetCeiling A D
            (chiPosHalfLineCeilingRate p ell A D tau) t) ^ p.γ -
              ell ^ p.γ) +
        p.χ * (chiPosTargetCeiling A D
          (chiPosHalfLineCeilingRate p ell A D tau) t) ^ p.m *
          tau * ell ^ p.γ ≤
      deriv (chiPosTargetCeiling A D
        (chiPosHalfLineCeilingRate p ell A D tau)) t := by
  let lam : ℝ := chiPosHalfLineCeilingRate p ell A D tau
  let B : ℝ := chiPosTargetCeiling A D lam t
  have hApos : 0 < A := zero_lt_one.trans_le h1A
  have hDpos : 0 < D := hApos.trans hAD
  have hlam : 0 < lam :=
    chiPosHalfLineCeilingRate_pos hApos hAD hreserve
  have hBderiv : deriv (chiPosTargetCeiling A D lam) t =
      -lam * (B - A) := by
    simpa [B] using (chiPosTargetCeiling_hasDerivAt A D lam t).deriv
  have hBge : A ≤ B := chiPosTargetCeiling_ge_target hAD.le
  have hBle : B ≤ D := chiPosTargetCeiling_le_start hAD.le hlam.le ht
  have hBpos : 0 < B := hApos.trans_le hBge
  have hgapMono :
      chiPosCeilingGap p ell A ≤ chiPosCeilingGap p ell B := by
    by_cases hEq : A = B
    · simp [hEq]
    · exact (chiPosCeilingGap_strictMonoOn_Ioi hcritical hchi0 hchi1
        hell.le hApos hBpos (lt_of_le_of_ne hBge hEq)).le
  have hpowMono : B ^ (p.m - 1) ≤ D ^ (p.m - 1) :=
    Real.rpow_le_rpow hBpos.le hBle (sub_nonneg.mpr p.hm)
  have htailMono :
      p.χ * B ^ (p.m - 1) * tau * ell ^ p.γ ≤
        p.χ * D ^ (p.m - 1) * tau * ell ^ p.γ := by
    have hcoef : 0 ≤ p.χ * tau * ell ^ p.γ :=
      mul_nonneg (mul_nonneg hchi0 htau)
        (Real.rpow_nonneg hell.le _)
    calc
      p.χ * B ^ (p.m - 1) * tau * ell ^ p.γ =
          (p.χ * tau * ell ^ p.γ) * B ^ (p.m - 1) := by ring
      _ ≤ (p.χ * tau * ell ^ p.γ) * D ^ (p.m - 1) :=
        mul_le_mul_of_nonneg_left hpowMono hcoef
      _ = p.χ * D ^ (p.m - 1) * tau * ell ^ p.γ := by ring
  have hreserveMono :
      chiPosHalfLineCeilingReserve p ell A D tau ≤
        chiPosCeilingGap p ell B -
          p.χ * B ^ (p.m - 1) * tau * ell ^ p.γ := by
    unfold chiPosHalfLineCeilingReserve
    linarith
  have htime : lam * (B - A) ≤ lam * (D - A) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_right hBle A) hlam.le
  have hbudget :
      lam * (D - A) ≤
        A * chiPosHalfLineCeilingReserve p ell A D tau := by
    simpa [lam] using
      chiPosHalfLineCeilingRate_mul_relaxation_le hApos hAD hreserve
  have hprod :
      A * chiPosHalfLineCeilingReserve p ell A D tau ≤
        B * (chiPosCeilingGap p ell B -
          p.χ * B ^ (p.m - 1) * tau * ell ^ p.γ) := by
    calc
      A * chiPosHalfLineCeilingReserve p ell A D tau ≤
          B * chiPosHalfLineCeilingReserve p ell A D tau :=
        mul_le_mul_of_nonneg_right hBge hreserve.le
      _ ≤ B * (chiPosCeilingGap p ell B -
          p.χ * B ^ (p.m - 1) * tau * ell ^ p.γ) :=
        mul_le_mul_of_nonneg_left hreserveMono hBpos.le
  have hm : B * B ^ (p.m - 1) = B ^ p.m :=
    mul_rpow_sub_one p.m p.hm hBpos.le
  have hbase :
      reactionFun p.α B +
          p.χ * B ^ p.m * (B ^ p.γ - ell ^ p.γ) =
        -(B * chiPosCeilingGap p ell B) := by
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
  have hweighted :
      reactionFun p.α B +
          p.χ * B ^ p.m * (B ^ p.γ - ell ^ p.γ) +
          p.χ * B ^ p.m * tau * ell ^ p.γ =
        -(B * (chiPosCeilingGap p ell B -
          p.χ * B ^ (p.m - 1) * tau * ell ^ p.γ)) := by
    rw [hbase]
    rw [← show B * (p.χ * B ^ (p.m - 1) * tau * ell ^ p.γ) =
        p.χ * B ^ p.m * tau * ell ^ p.γ by rw [← hm]; ring]
    ring
  change reactionFun p.α B +
      p.χ * B ^ p.m * (B ^ p.γ - ell ^ p.γ) +
      p.χ * B ^ p.m * tau * ell ^ p.γ ≤
        deriv (chiPosTargetCeiling A D lam) t
  rw [hBderiv, hweighted]
  linarith [htime, hbudget, hprod]

section AxiomAudit

#print axioms exists_chiPos_halfLine_round_targets
#print axioms chiPosHalfLineFloorReserve_pos_of_tail_lt
#print axioms chiPosHalfLineFloorRate_pos
#print axioms chiZeroKPPFloor_tail_weighted_subsolution
#print axioms chiPosHalfLineCeilingReserve_pos_of_tail_lt
#print axioms chiPosHalfLineCeilingRate_pos
#print axioms chiPosTargetCeiling_tail_weighted_supersolution

end AxiomAudit

end ShenWork.Paper1
