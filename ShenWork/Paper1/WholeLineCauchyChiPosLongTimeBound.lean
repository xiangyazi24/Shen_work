import ShenWork.Paper1.WholeLineCauchyLongTimeBound
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

open Filter Function MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

/-!
# χ>0 eventual pointwise ceiling — relaxing barrier to MChi

For χ>0 in the critical case α = m+γ-1, the ceiling function
`MChi + (C - MChi) * exp(-α * t)` is a supersolution of the reaction
ODE at a spatial maximum. This gives `limsup sup_x u(t,x) ≤ MChi`.

The proof follows the constructive approach:
1. Define `wholeLineCauchyChiPosCeiling p C t := MChi p + (C - MChi p) * exp(-p.α * t)`
2. Show it is a supersolution via the Bernoulli inequality for rpow
3. Apply the slab maximum principle to get u ≤ ceiling on each slab
4. Chain to get the global bound
5. Take limsup to get UniformLimsupLe MChi
-/

/-- The χ>0 relaxing ceiling: decays exponentially from C to MChi at rate α. -/
def wholeLineCauchyChiPosCeiling (p : CMParams) (C t : ℝ) : ℝ :=
  MChi p + (C - MChi p) * Real.exp (-p.α * t)

theorem wholeLineCauchyChiPosCeiling_zero (p : CMParams) (C : ℝ) :
    wholeLineCauchyChiPosCeiling p C 0 = C := by
  simp [wholeLineCauchyChiPosCeiling]

theorem wholeLineCauchyChiPosCeiling_hasDerivAt (p : CMParams) (C t : ℝ) :
    HasDerivAt (wholeLineCauchyChiPosCeiling p C)
      (-p.α * (C - MChi p) * Real.exp (-p.α * t)) t := by
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-p.α * s))
      (-p.α * Real.exp (-p.α * t)) t := by
    have := (hasDerivAt_id t).const_mul (-p.α) |>.exp
    simp only [id] at this
    convert this using 1; ring
  convert (hasDerivAt_const t (MChi p)).add (hexp.const_mul (C - MChi p)) using 1 <;> ring

theorem wholeLineCauchyChiPosCeiling_deriv_eq
    (p : CMParams) (C t : ℝ) :
    deriv (wholeLineCauchyChiPosCeiling p C) t =
      -p.α * (wholeLineCauchyChiPosCeiling p C t - MChi p) := by
  rw [(wholeLineCauchyChiPosCeiling_hasDerivAt p C t).deriv]
  simp [wholeLineCauchyChiPosCeiling]
  ring

theorem wholeLineCauchyChiPosCeiling_MChi_le
    {p : CMParams} {C : ℝ} (hC : MChi p ≤ C) (t : ℝ) :
    MChi p ≤ wholeLineCauchyChiPosCeiling p C t := by
  unfold wholeLineCauchyChiPosCeiling
  have hmul : 0 ≤ (C - MChi p) * Real.exp (-p.α * t) :=
    mul_nonneg (sub_nonneg.mpr hC) (Real.exp_nonneg _)
  linarith

theorem wholeLineCauchyChiPosCeiling_le
    {p : CMParams} {C t : ℝ} (hC : MChi p ≤ C) (ht : 0 ≤ t) :
    wholeLineCauchyChiPosCeiling p C t ≤ C := by
  have hexp : Real.exp (-p.α * t) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [p.hα]
  unfold wholeLineCauchyChiPosCeiling
  nlinarith [sub_nonneg.mpr hC, Real.exp_pos (-p.α * t)]

theorem wholeLineCauchyChiPosCeiling_restart (p : CMParams) (C a s : ℝ) :
    wholeLineCauchyChiPosCeiling p (wholeLineCauchyChiPosCeiling p C a) s =
      wholeLineCauchyChiPosCeiling p C (a + s) := by
  simp only [wholeLineCauchyChiPosCeiling]
  have hexp : Real.exp (-p.α * a) * Real.exp (-p.α * s) = Real.exp (-p.α * (a + s)) := by
    rw [← Real.exp_add]; ring_nf
  have : (C - MChi p) * Real.exp (-p.α * a) * Real.exp (-p.α * s) =
         (C - MChi p) * Real.exp (-p.α * (a + s)) := by
    rw [mul_assoc, hexp]
  linarith

/-- Bernoulli inequality for rpow: for r ≥ 1 and n ≥ 2, r^n ≥ n*r - (n-1).
Proved via convexity of x^n and the tangent line bound at x = 1. -/
theorem rpow_bernoulli {r n : ℝ} (hr : 1 ≤ r) (hn : 2 ≤ n) :
    n * r - (n - 1) ≤ r ^ n := by
  by_cases hrr : r = 1
  · subst hrr; simp [Real.one_rpow]
  have hr1 : 1 < r := lt_of_le_of_ne hr (Ne.symm hrr)
  have hn1 : 1 ≤ n := le_trans (by norm_num : (1 : ℝ) ≤ 2) hn
  have hconv := convexOn_rpow hn1
  have h1mem : (1 : ℝ) ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr zero_le_one
  have hrmem : r ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (zero_le_one.trans hr)
  have hderiv : HasDerivAt (fun x : ℝ => x ^ n) (n * 1 ^ (n - 1)) 1 :=
    hasDerivAt_rpow_const (Or.inl one_ne_zero)
  rw [Real.one_rpow, mul_one] at hderiv
  have hslope := hconv.le_slope_of_hasDerivAt h1mem hrmem hr1 hderiv
  simp only [Real.one_rpow, slope_def_field] at hslope
  have hr_pos : 0 < r - 1 := sub_pos.mpr hr1
  rw [le_div_iff₀ hr_pos] at hslope
  linarith

/-- The supersolution property for the χ>0 ceiling at the ceiling value.
For B ≥ MChi (with (1-χ)MChi^α = 1):
  B(1 - (1-χ)B^α) + α(B - MChi) ≤ 0
i.e., the ceiling reaction + ceiling derivative ≤ 0. -/
theorem chiPosCeiling_supersolution
    {p : CMParams} (hχ_pos : 0 < p.χ) (hχ_lt : p.χ < 1)
    (halpha : p.α = p.m + p.γ - 1) {B : ℝ} (hB : MChi p ≤ B) :
    B * (1 - (1 - p.χ) * B ^ p.α) + p.α * (B - MChi p) ≤ 0 := by
  have hα_pos : 0 < p.α := by linarith [p.hα]
  have hMChi_pos : 0 < MChi p := MChi_pos_of_chi_lt_one p hχ_lt
  have hMChi_nonneg : 0 ≤ MChi p := hMChi_pos.le
  have hB_pos : 0 < B := lt_of_lt_of_le hMChi_pos hB
  have hone_chi : 0 < 1 - p.χ := by linarith
  have hMChi_rpow : (1 - p.χ) * (MChi p) ^ p.α = 1 := by
    rw [MChi_eq_rpow_of_chi_pos p hχ_pos]
    have hbase : 0 ≤ 1 / (1 - p.χ) := div_nonneg one_pos.le hone_chi.le
    rw [← Real.rpow_mul hbase, div_mul_cancel₀ 1 (ne_of_gt hα_pos)]
    rw [Real.rpow_one]
    field_simp
  set r := B / MChi p with hr_def
  have hr1 : 1 ≤ r := le_div_iff₀ hMChi_pos |>.mpr (by linarith)
  have hB_eq : B = MChi p * r := by rw [hr_def]; field_simp
  rw [hB_eq]
  have hα1 : 2 ≤ p.α + 1 := by linarith [p.hα]
  have hBα : (MChi p * r) ^ p.α = (MChi p) ^ p.α * r ^ p.α :=
    Real.mul_rpow hMChi_nonneg (zero_le_one.trans hr1)
  rw [hBα, ← mul_assoc (1 - p.χ), hMChi_rpow]
  -- Target: MChi*r * (1 - r^α) + α*(MChi*r - MChi) ≤ 0
  -- = MChi * [(α+1)*r - α - r^{α+1}] ≤ 0
  -- Bernoulli: (α+1)*r - α ≤ r^{α+1}
  have hkey := rpow_bernoulli hr1 hα1
  have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hrα1 : r ^ p.α * r = r ^ (p.α + 1) := by
    conv_rhs => rw [show p.α + 1 = p.α + (1 : ℝ) from rfl]
    rw [Real.rpow_add hr_pos, Real.rpow_one]
  nlinarith [hMChi_pos]

section AxiomAudit

-- #print axioms chiPosCeiling_supersolution

end AxiomAudit

end ShenWork.Paper1
