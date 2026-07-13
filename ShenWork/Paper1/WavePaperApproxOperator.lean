import ShenWork.Paper1.WavePaperApproxComparison

open Filter Topology Set Real

noncomputable section

namespace ShenWork.Paper1

/-- Pointwise paper operator written as diffusion, transport, the cross-frozen
gradient term, logistic reaction, favorable elliptic value term, and diagonal
absorption. -/
theorem paperWaveOperator_eq_routeA_pieces
    (p : CMParams) {c a : ℝ} {u W : ℝ → ℝ} {x : ℝ}
    (ha : a = -p.χ) (hW : 0 ≤ W x) :
    paperWaveOperator p c u W x =
      iteratedDeriv 2 W x + c * deriv W x
        + a * p.m * (W x) ^ (p.m - 1) *
            deriv (frozenElliptic p u) x * deriv W x
        + reactionFun p.α (W x)
        + a * (W x) ^ p.m * frozenElliptic p u x
        - a * (W x) ^ (p.m + p.γ) := by
  have hmγ : 1 ≤ p.m + p.γ := by linarith [p.hm, p.hγ]
  have hm_id : (W x) ^ (p.m - 1) * W x = (W x) ^ p.m := by
    rw [mul_comm]
    exact mul_rpow_sub_one p.m p.hm hW
  have hmγ_id :
      W x * (W x) ^ (p.m + p.γ - 1) =
        (W x) ^ (p.m + p.γ) :=
    mul_rpow_sub_one (p.m + p.γ) hmγ hW
  unfold paperWaveOperator reactionFun
  rw [ha, ← hm_id, ← hmγ_id]
  ring

/-- Ordered power increment on `[0,M]`, with the explicit `rpowLip` constant. -/
theorem rpow_increment_le_rpowLip
    {q M w a : ℝ} (hq : 1 ≤ q) (hM : 0 ≤ M)
    (hw : w ∈ Set.Icc (0 : ℝ) M) (ha : a ∈ Set.Icc (0 : ℝ) M)
    (hwa : w ≤ a) :
    a ^ q - w ^ q ≤ rpowLip q M * (a - w) := by
  have hLip := rpow_m_lipschitz_on_Icc hq hM
  have hd := hLip.dist_le_mul a ha w hw
  rw [Real.dist_eq, Real.dist_eq] at hd
  rw [Real.coe_toNNReal _ (rpowLip_nonneg hq hM)] at hd
  have hpow : 0 ≤ a ^ q - w ^ q := by
    exact sub_nonneg.mpr (Real.rpow_le_rpow hw.1 hwa (le_trans zero_le_one hq))
  have hgap : 0 ≤ a - w := sub_nonneg.mpr hwa
  rw [abs_of_nonneg hpow, abs_of_nonneg hgap] at hd
  exact hd

/-- Error-tolerant value-level Route-A ledger at a positive approximate
contact of `A - W`.  All zeroth-order terms are discharged here.  The caller
only supplies the cross-frozen gradient increment, where the cusp at `m < 2`
requires the weighted-slope argument. -/
theorem paperWaveOperator_diff_le_of_approx_contact
    {p : CMParams} {c a M BV Ccross Ecross eta : ℝ}
    {u A W : ℝ → ℝ} {x₀ : ℝ}
    (ha : a = -p.χ) (hχ : p.χ ≤ 0)
    (hM : 0 ≤ M)
    (hAmem : A x₀ ∈ Set.Icc (0 : ℝ) M)
    (hWmem : W x₀ ∈ Set.Icc (0 : ℝ) M)
    (hWA : W x₀ ≤ A x₀)
    (hVnonneg : 0 ≤ frozenElliptic p u x₀)
    (hVbound : frozenElliptic p u x₀ ≤ BV)
    (hsecond :
      iteratedDeriv 2 A x₀ - iteratedDeriv 2 W x₀ ≤ eta)
    (hslope : |deriv A x₀ - deriv W x₀| ≤ eta)
    (hcross :
      a * p.m * (A x₀) ^ (p.m - 1) *
            deriv (frozenElliptic p u) x₀ * deriv A x₀
        - a * p.m * (W x₀) ^ (p.m - 1) *
            deriv (frozenElliptic p u) x₀ * deriv W x₀ ≤
      Ccross * (A x₀ - W x₀) + Ecross * eta) :
    paperWaveOperator p c u A x₀ - paperWaveOperator p c u W x₀ ≤
      (reactionLip p.α M + a * BV * rpowLip p.m M + Ccross) *
          (A x₀ - W x₀)
        + (1 + |c| + Ecross) * eta := by
  have ha0 : 0 ≤ a := by
    rw [ha]
    linarith
  have hgap : 0 ≤ A x₀ - W x₀ := sub_nonneg.mpr hWA
  have hrxn :
      reactionFun p.α (A x₀) - reactionFun p.α (W x₀) ≤
        reactionLip p.α M * (A x₀ - W x₀) := by
    have habs := reaction_increment_abs_le p.hα hM hWmem hAmem
    have hle :
        reactionFun p.α (A x₀) - reactionFun p.α (W x₀) ≤
          |reactionFun p.α (A x₀) - reactionFun p.α (W x₀)| :=
      le_abs_self _
    rw [abs_of_nonneg hgap] at habs
    linarith
  have hpowm :
      (A x₀) ^ p.m - (W x₀) ^ p.m ≤
        rpowLip p.m M * (A x₀ - W x₀) :=
    rpow_increment_le_rpowLip p.hm hM hWmem hAmem hWA
  have hV0 : 0 ≤ BV := le_trans hVnonneg hVbound
  have hpowm0 : 0 ≤ (A x₀) ^ p.m - (W x₀) ^ p.m := by
    exact sub_nonneg.mpr
      (Real.rpow_le_rpow hWmem.1 hWA (le_trans zero_le_one p.hm))
  have hVterm :
      a * (A x₀) ^ p.m * frozenElliptic p u x₀ -
          a * (W x₀) ^ p.m * frozenElliptic p u x₀ ≤
        a * BV * rpowLip p.m M * (A x₀ - W x₀) := by
    have hLipgap0 : 0 ≤ rpowLip p.m M * (A x₀ - W x₀) :=
      mul_nonneg (rpowLip_nonneg p.hm hM) hgap
    have hmul := mul_le_mul hpowm hVbound hVnonneg hLipgap0
    have hmul' := mul_le_mul_of_nonneg_left hmul ha0
    nlinarith
  have hmg0 : 0 ≤ p.m + p.γ := by linarith [p.hm, p.hγ]
  have hdiagpow : (W x₀) ^ (p.m + p.γ) ≤
      (A x₀) ^ (p.m + p.γ) :=
    Real.rpow_le_rpow hWmem.1 hWA hmg0
  have hdiag :
      -a * (A x₀) ^ (p.m + p.γ) -
          (-a * (W x₀) ^ (p.m + p.γ)) ≤ 0 := by
    nlinarith
  have hcSlope :
      c * deriv A x₀ - c * deriv W x₀ ≤ |c| * eta := by
    calc
      c * deriv A x₀ - c * deriv W x₀ =
          c * (deriv A x₀ - deriv W x₀) := by ring
      _ ≤ |c * (deriv A x₀ - deriv W x₀)| := le_abs_self _
      _ = |c| * |deriv A x₀ - deriv W x₀| := abs_mul _ _
      _ ≤ |c| * eta :=
        mul_le_mul_of_nonneg_left hslope (abs_nonneg c)
  rw [paperWaveOperator_eq_routeA_pieces p ha hAmem.1,
    paperWaveOperator_eq_routeA_pieces p ha hWmem.1]
  nlinarith [hrxn, hVterm, hdiag, hcSlope, hsecond, hcross]

section AxiomAudit

#print axioms paperWaveOperator_eq_routeA_pieces
#print axioms rpow_increment_le_rpowLip
#print axioms paperWaveOperator_diff_le_of_approx_contact

end AxiomAudit

end ShenWork.Paper1
