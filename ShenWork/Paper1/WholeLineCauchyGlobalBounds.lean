import ShenWork.Paper1.WholeLineCauchyNonnegativity
import ShenWork.Paper1.WavePositiveStrictMaximum

open Real Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Stable-regime ceiling for the whole-line Cauchy problem

At a first contact with a constant upper barrier `M`, the elliptic equation
contributes the exponent `m + gamma - 1` after division by `M`. Thus the
correct scalar supersolution condition is

`1 + max chi 0 * M^(m + gamma - 1) <= M^alpha`.

The negative branch makes the chemotaxis contribution favorable. In the
positive supercritical branch `alpha > m + gamma - 1`, a sufficiently large
constant absorbs the lower chemotactic power. In the critical branch,
`alpha = m + gamma - 1` and `chi < 1`, while `MChi` is the exact positive
solution of `(1 - chi) * M^alpha = 1`.
-/

/-- The parameter regime actually needed by the Cauchy ceiling argument.
For nonpositive sensitivity there is no relation between `alpha` and
`m + gamma - 1`. For positive sensitivity either the logistic exponent is
strictly larger, or the critical equality is accompanied by the paper's
small-sensitivity condition. -/
def WholeLineCauchyCeilingRegime (p : CMParams) : Prop :=
  p.χ ≤ 0 ∨
    (0 ≤ p.χ ∧
      (p.m + p.γ - 1 < p.α ∨
        (p.χ < chiStar p ∧ p.α = p.m + p.γ - 1)))

theorem WholeLineCauchyCeilingRegime.of_nonpositive
    {p : CMParams} (hχ : p.χ ≤ 0) :
    WholeLineCauchyCeilingRegime p :=
  Or.inl hχ

theorem StableWaveParameterRegime.toWholeLineCauchyCeilingRegime
    {p : CMParams} (h : StableWaveParameterRegime p) :
    WholeLineCauchyCeilingRegime p := by
  rcases h with hneg | hpos
  · exact Or.inl hneg.1.le
  · exact Or.inr ⟨hpos.1, Or.inr hpos.2⟩

/-- Parameter-only upper threshold. In the supercritical branch it is the
explicit root which makes the higher logistic power dominate; in all other
branches it is the paper's critical ceiling `MChi`. -/
def wholeLineCauchyParameterCeiling (p : CMParams) : ℝ :=
  if p.m + p.γ - 1 < p.α then
    max 1
      ((1 + max p.χ 0) ^
        (1 / (p.α - (p.m + p.γ - 1))))
  else MChi p

/-- A canonical ceiling above both the initial BUC norm and the stable
constant-state threshold. -/
def wholeLineCauchyStableCeiling
    (p : CMParams) (u₀ : WholeLineBUC) : ℝ :=
  max (‖u₀‖ + 1) (wholeLineCauchyParameterCeiling p)

theorem wholeLineCauchyStableCeiling_gt_norm
    (p : CMParams) (u₀ : WholeLineBUC) :
    ‖u₀‖ < wholeLineCauchyStableCeiling p u₀ := by
  unfold wholeLineCauchyStableCeiling
  exact lt_of_lt_of_le (lt_add_one ‖u₀‖) (le_max_left _ _)

theorem wholeLineCauchyStableCeiling_initial_lt
    (p : CMParams) (u₀ : WholeLineBUC) (x : ℝ) :
    u₀.1 x < wholeLineCauchyStableCeiling p u₀ :=
  (WholeLineBUC.apply_le_norm u₀ x).trans_lt
    (wholeLineCauchyStableCeiling_gt_norm p u₀)

theorem wholeLineCauchyStableCeiling_one_le
    {p : CMParams} (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) :
    1 ≤ wholeLineCauchyStableCeiling p u₀ := by
  unfold wholeLineCauchyStableCeiling
  apply le_trans (b := wholeLineCauchyParameterCeiling p)
  · unfold wholeLineCauchyParameterCeiling
    split_ifs with hsuper
    · exact le_max_left _ _
    · rcases hregime with hχ | hpos
      · simpa [MChi_eq_one_of_chi_nonpos p hχ]
      · rcases hpos.2 with hsuper' | hcritical
        · exact False.elim (hsuper hsuper')
        · exact one_le_MChi_of_chi_nonneg_lt_chiStar
            p hpos.1 hcritical.1
  · exact le_max_right _ _

/-- The explicit supercritical threshold satisfies the scalar first-contact
margin. -/
theorem wholeLineCauchyParameterCeiling_margin_of_supercritical
    (p : CMParams) (hχ : 0 ≤ p.χ)
    (hsuper : p.m + p.γ - 1 < p.α)
    {M : ℝ} (hM : wholeLineCauchyParameterCeiling p ≤ M) :
    1 + max p.χ 0 * M ^ (p.m + p.γ - 1) ≤ M ^ p.α := by
  let q : ℝ := p.m + p.γ - 1
  have hq : 1 ≤ q := by
    dsimp [q]
    linarith [p.hm, p.hγ]
  have hd : 0 < p.α - q := by dsimp [q]; linarith
  have hbase : 0 ≤ 1 + max p.χ 0 := by positivity
  have hthreshold :
      max 1 ((1 + max p.χ 0) ^ (1 / (p.α - q))) ≤ M := by
    simpa [wholeLineCauchyParameterCeiling, hsuper, q] using hM
  have hM1 : 1 ≤ M := (le_max_left _ _).trans hthreshold
  have hM0 : 0 ≤ M := zero_le_one.trans hM1
  have hMpos : 0 < M := zero_lt_one.trans_le hM1
  have hroot :
      ((1 + max p.χ 0) ^ (1 / (p.α - q))) ^ (p.α - q) =
        1 + max p.χ 0 := by
    rw [one_div, Real.rpow_inv_rpow hbase hd.ne']
  have hrootM :
      (1 + max p.χ 0) ^ (1 / (p.α - q)) ≤ M :=
    (le_max_right _ _).trans hthreshold
  have hpowGap : 1 + max p.χ 0 ≤ M ^ (p.α - q) := by
    rw [← hroot]
    exact Real.rpow_le_rpow
      (Real.rpow_nonneg hbase _) hrootM hd.le
  have hpowQ : 1 ≤ M ^ q :=
    Real.one_le_rpow hM1 (zero_le_one.trans hq)
  have hfactor : M ^ p.α = M ^ q * M ^ (p.α - q) := by
    rw [← Real.rpow_add hMpos]
    congr 1
    ring
  rw [max_eq_left hχ, hfactor]
  calc
    1 + p.χ * M ^ q ≤ M ^ q + p.χ * M ^ q := by linarith
    _ = M ^ q * (1 + p.χ) := by ring
    _ ≤ M ^ q * M ^ (p.α - q) :=
      mul_le_mul_of_nonneg_left
        (by simpa [max_eq_left hχ] using hpowGap)
        (Real.rpow_nonneg hM0 _)

/-- Strict form of the supercritical scalar margin above the explicit
parameter threshold. -/
theorem wholeLineCauchyParameterCeiling_strict_margin_of_supercritical
    (p : CMParams) (hχ : 0 ≤ p.χ)
    (hsuper : p.m + p.γ - 1 < p.α)
    {M : ℝ} (hM : wholeLineCauchyParameterCeiling p < M) :
    1 + max p.χ 0 * M ^ (p.m + p.γ - 1) < M ^ p.α := by
  let q : ℝ := p.m + p.γ - 1
  have hq : 1 ≤ q := by
    dsimp [q]
    linarith [p.hm, p.hγ]
  have hd : 0 < p.α - q := by dsimp [q]; linarith
  have hbase : 0 ≤ 1 + max p.χ 0 := by positivity
  have hthreshold :
      max 1 ((1 + max p.χ 0) ^ (1 / (p.α - q))) < M := by
    simpa [wholeLineCauchyParameterCeiling, hsuper, q] using hM
  have hM1 : 1 < M := (le_max_left _ _).trans_lt hthreshold
  have hM0 : 0 ≤ M := zero_le_one.trans hM1.le
  have hMpos : 0 < M := zero_lt_one.trans hM1
  have hroot :
      ((1 + max p.χ 0) ^ (1 / (p.α - q))) ^ (p.α - q) =
        1 + max p.χ 0 := by
    rw [one_div, Real.rpow_inv_rpow hbase hd.ne']
  have hrootM :
      (1 + max p.χ 0) ^ (1 / (p.α - q)) < M :=
    (le_max_right _ _).trans_lt hthreshold
  have hpowGap : 1 + max p.χ 0 < M ^ (p.α - q) := by
    rw [← hroot]
    exact Real.rpow_lt_rpow
      (Real.rpow_nonneg hbase _) hrootM hd
  have hpowQ : 1 ≤ M ^ q :=
    Real.one_le_rpow hM1.le (zero_le_one.trans hq)
  have hpowQpos : 0 < M ^ q := Real.rpow_pos_of_pos hMpos _
  have hfactor : M ^ p.α = M ^ q * M ^ (p.α - q) := by
    rw [← Real.rpow_add hMpos]
    congr 1
    ring
  rw [max_eq_left hχ, hfactor]
  calc
    1 + p.χ * M ^ q ≤ M ^ q + p.χ * M ^ q := by linarith
    _ = M ^ q * (1 + p.χ) := by ring
    _ < M ^ q * M ^ (p.α - q) :=
      mul_lt_mul_of_pos_left
        (by simpa [max_eq_left hχ] using hpowGap) hpowQpos

/-- The exact scalar inequality required by the constant upper-barrier
first-contact argument.  In particular, the chemotaxis exponent is
`m + gamma - 1`, not `gamma`. -/
theorem wholeLineCauchyStableCeiling_margin
    {p : CMParams} (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) :
    1 + max p.χ 0 *
        (wholeLineCauchyStableCeiling p u₀) ^ (p.m + p.γ - 1) ≤
      (wholeLineCauchyStableCeiling p u₀) ^ p.α := by
  let M := wholeLineCauchyStableCeiling p u₀
  have hM1 : 1 ≤ M := wholeLineCauchyStableCeiling_one_le hregime u₀
  have hM0 : 0 ≤ M := zero_le_one.trans hM1
  rcases hregime with hχ | hpos
  · have hpow : 1 ≤ M ^ p.α :=
      Real.one_le_rpow hM1 (zero_le_one.trans p.hα)
    simpa [max_eq_right hχ, M] using hpow
  · rcases hpos.2 with hsuper | hcritical
    · exact wholeLineCauchyParameterCeiling_margin_of_supercritical
        p hpos.1 hsuper (le_max_right _ _)
    · have hχ1 : p.χ < 1 :=
        lt_of_lt_of_le hcritical.1 (chiStar_le_one p)
      have hden : 0 < 1 - p.χ := sub_pos.mpr hχ1
      have hMChi0 : 0 ≤ MChi p :=
        MChi_nonneg_of_chi_lt_one p hχ1
      have hMChiParam :
          MChi p = wholeLineCauchyParameterCeiling p := by
        simp [wholeLineCauchyParameterCeiling, hcritical.2]
      have hMChiM : MChi p ≤ M := by
        rw [hMChiParam]
        exact le_max_right _ _
      have hpow_le : (MChi p) ^ p.α ≤ M ^ p.α :=
        Real.rpow_le_rpow hMChi0 hMChiM (zero_le_one.trans p.hα)
      have hthreshold : 1 / (1 - p.χ) ≤ M ^ p.α := by
        rw [← MChi_rpow_alpha_eq_one_div_one_sub_chi p hpos.1 hχ1]
        exact hpow_le
      have hone : 1 ≤ (1 - p.χ) * (M ^ p.α) := by
        calc
          1 = (1 - p.χ) * (1 / (1 - p.χ)) := by
            field_simp
          _ ≤ (1 - p.χ) * (M ^ p.α) :=
            mul_le_mul_of_nonneg_left hthreshold hden.le
      rw [max_eq_left hpos.1, ← hcritical.2]
      nlinarith

/-- Any scalar ceiling satisfying the non-strict first-contact margin becomes
strict above the ceiling throughout the admissible regime. -/
theorem wholeLineCauchyCeiling_strict_margin_above
    {p : CMParams} (hregime : WholeLineCauchyCeilingRegime p)
    {C L : ℝ} (hC1 : 1 ≤ C)
    (hmargin :
      1 + max p.χ 0 * C ^ (p.m + p.γ - 1) ≤ C ^ p.α)
    (hCL : C < L) :
    1 + max p.χ 0 * L ^ (p.m + p.γ - 1) < L ^ p.α := by
  let q : ℝ := p.m + p.γ - 1
  have hq : 0 < q := by
    dsimp [q]
    linarith [p.hm, p.hγ]
  have hCpos : 0 < C := zero_lt_one.trans_le hC1
  have hLpos : 0 < L := hCpos.trans hCL
  rcases hregime with hχ | hpos
  · have hpow : 1 < L ^ p.α :=
      Real.one_lt_rpow (hC1.trans_lt hCL) (by linarith [p.hα])
    simpa [max_eq_right hχ] using hpow
  · rcases hpos.2 with hsuper | hcritical
    · have hd : 0 < p.α - q := by dsimp [q]; linarith
      have hCqpos : 0 < C ^ q := Real.rpow_pos_of_pos hCpos _
      have hdiv :
          (1 + p.χ * C ^ q) / C ^ q ≤ C ^ p.α / C ^ q := by
        exact (div_le_div_iff_of_pos_right hCqpos).2 (by
          simpa [q, max_eq_left hpos.1] using hmargin)
      have hCscaled : C ^ (-q) + p.χ ≤ C ^ (p.α - q) := by
        rw [Real.rpow_sub hCpos, Real.rpow_neg hCpos.le]
        calc
          (C ^ q)⁻¹ + p.χ = (1 + p.χ * C ^ q) / C ^ q := by
            field_simp [ne_of_gt hCqpos]
          _ ≤ C ^ p.α / C ^ q := hdiv
      have hdecrease : L ^ (-q) < C ^ (-q) :=
        Real.rpow_lt_rpow_of_neg hCpos hCL (neg_lt_zero.mpr hq)
      have hincrease : C ^ (p.α - q) < L ^ (p.α - q) :=
        Real.rpow_lt_rpow hCpos.le hCL hd
      have hsumDecrease : L ^ (-q) + p.χ < C ^ (-q) + p.χ := by
        linarith
      have hscaled : L ^ (-q) + p.χ < L ^ (p.α - q) :=
        (hsumDecrease.trans_le hCscaled).trans hincrease
      have hLqpos : 0 < L ^ q := Real.rpow_pos_of_pos hLpos _
      have hmul := mul_lt_mul_of_pos_right hscaled hLqpos
      rw [max_eq_left hpos.1]
      calc
        1 + p.χ * L ^ q = (L ^ (-q) + p.χ) * L ^ q := by
          rw [add_mul, ← Real.rpow_add hLpos]
          norm_num
        _ < L ^ (p.α - q) * L ^ q := hmul
        _ = L ^ p.α := by
          rw [← Real.rpow_add hLpos]
          congr 1
          ring
    · have hχ1 : p.χ < 1 :=
        lt_of_lt_of_le hcritical.1 (chiStar_le_one p)
      have hden : 0 < 1 - p.χ := sub_pos.mpr hχ1
      have hCpow_lt : C ^ p.α < L ^ p.α :=
        Real.rpow_lt_rpow hCpos.le hCL (by linarith [p.hα])
      have honeC : 1 ≤ (1 - p.χ) * C ^ p.α := by
        have hm := hmargin
        rw [max_eq_left hpos.1, ← hcritical.2] at hm
        nlinarith
      have honeL : 1 < (1 - p.χ) * L ^ p.α := by
        have hmul := mul_lt_mul_of_pos_left hCpow_lt hden
        linarith
      rw [max_eq_left hpos.1, ← hcritical.2]
      nlinarith

/-- Above the canonical ceiling the scalar first-contact inequality is
strict. This is the form consumed by the nonlocal slab maximum principle. -/
theorem wholeLineCauchyStableCeiling_strict_margin
    {p : CMParams} (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) :
    ∀ L, wholeLineCauchyStableCeiling p u₀ < L →
      1 + max p.χ 0 * L ^ (p.m + p.γ - 1) < L ^ p.α := by
  intro L hCL
  let C := wholeLineCauchyStableCeiling p u₀
  have hC1 : 1 ≤ C := wholeLineCauchyStableCeiling_one_le hregime u₀
  have hL1 : 1 < L := hC1.trans_lt (by simpa [C] using hCL)
  rcases hregime with hχ | hpos
  · have hpow : 1 < L ^ p.α :=
      Real.one_lt_rpow hL1 (by linarith [p.hα])
    simpa [max_eq_right hχ] using hpow
  · rcases hpos.2 with hsuper | hcritical
    · apply wholeLineCauchyParameterCeiling_strict_margin_of_supercritical
        p hpos.1 hsuper
      exact (le_max_right _ _).trans_lt hCL
    · have hχ1 : p.χ < 1 :=
        lt_of_lt_of_le hcritical.1 (chiStar_le_one p)
      have hden : 0 < 1 - p.χ := sub_pos.mpr hχ1
      have hMChi0 : 0 ≤ MChi p := MChi_nonneg_of_chi_lt_one p hχ1
      have hMChiParam :
          MChi p = wholeLineCauchyParameterCeiling p := by
        simp [wholeLineCauchyParameterCeiling, hcritical.2]
      have hMChiL : MChi p < L := by
        rw [hMChiParam]
        exact (le_max_right _ _).trans_lt hCL
      have hpow_lt : (MChi p) ^ p.α < L ^ p.α :=
        Real.rpow_lt_rpow hMChi0 hMChiL (by linarith [p.hα])
      have hthreshold : 1 / (1 - p.χ) < L ^ p.α := by
        rw [← MChi_rpow_alpha_eq_one_div_one_sub_chi p hpos.1 hχ1]
        exact hpow_lt
      have hone : 1 < (1 - p.χ) * L ^ p.α := by
        calc
          1 = (1 - p.χ) * (1 / (1 - p.χ)) := by field_simp
          _ < (1 - p.χ) * L ^ p.α :=
            mul_lt_mul_of_pos_left hthreshold hden
      rw [max_eq_left hpos.1, ← hcritical.2]
      nlinarith

section WholeLineCauchyGlobalBoundsAxiomAudit

#print axioms wholeLineCauchyStableCeiling_initial_lt
#print axioms wholeLineCauchyParameterCeiling_margin_of_supercritical
#print axioms wholeLineCauchyParameterCeiling_strict_margin_of_supercritical
#print axioms wholeLineCauchyStableCeiling_one_le
#print axioms wholeLineCauchyStableCeiling_margin
#print axioms wholeLineCauchyCeiling_strict_margin_above
#print axioms wholeLineCauchyStableCeiling_strict_margin

end WholeLineCauchyGlobalBoundsAxiomAudit

end ShenWork.Paper1
