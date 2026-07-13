import ShenWork.Paper3.IntervalDomainResolverMassGap
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# Uniform mass gap for the power-law elliptic source

If `0 <= U <= M`, the unit-interval mean of `U` is `uStar`, and
`M >= uStar + d`, then the source deficit

`nu * (M^gamma - U^gamma)`

has a strictly positive integral bounded below independently of `M` and `U`.
For `gamma <= 1` this is Jensen concavity.  For `gamma >= 1` it is the
pointwise estimate `U^gamma <= M^(gamma-1) U`.  No orbit compactness,
stability, or convergence input is used.
-/

open Filter MeasureTheory Set Topology

noncomputable section

namespace ShenWork.Paper3

open ShenWork.IntervalDomain

private theorem intervalMeasure_one_isProbability :
    IsProbabilityMeasure (intervalMeasure 1) := by
  constructor
  unfold intervalMeasure intervalSet
  simp [Real.volume_Icc]

/-- A globally continuous nonnegative profile bounded by `M` is integrable
against the unit-interval measure. -/
theorem intervalMeasure_integrable_of_continuous_nonneg_le
    {U : ℝ → ℝ} {M : ℝ}
    (hU_cont : Continuous U) (hU_nonneg : ∀ y, 0 ≤ U y)
    (hU_le : ∀ y, U y ≤ M) :
    Integrable U (intervalMeasure 1) := by
  apply intervalMeasure_integrable_of_abs_bound hU_cont.aestronglyMeasurable
  intro y
  rw [abs_of_nonneg (hU_nonneg y)]
  exact hU_le y

/-- The power of a bounded nonnegative continuous profile is integrable. -/
theorem intervalMeasure_rpow_integrable_of_continuous_nonneg_le
    (gamma : ℝ) (hgamma : 0 ≤ gamma)
    {U : ℝ → ℝ} {M : ℝ}
    (hU_cont : Continuous U) (hU_nonneg : ∀ y, 0 ≤ U y)
    (hU_le : ∀ y, U y ≤ M) :
    Integrable (fun y => U y ^ gamma) (intervalMeasure 1) := by
  have hM : 0 ≤ M := le_trans (hU_nonneg 0) (hU_le 0)
  apply intervalMeasure_integrable_of_abs_bound (M := M ^ gamma)
    ((Real.continuous_rpow_const hgamma).comp hU_cont).aestronglyMeasurable
  intro y
  change |U y ^ gamma| ≤ M ^ gamma
  rw [abs_of_nonneg (Real.rpow_nonneg (hU_nonneg y) _)]
  exact Real.rpow_le_rpow (hU_nonneg y) (hU_le y) hgamma

/-- The uniform source-gap constant.  It depends only on the equilibrium mass
and the prescribed excess `d`, not on the actual profile maximum. -/
def intervalPowerSourceGapConstant
    (p : CM2Params) (uStar d : ℝ) : ℝ :=
  if p.γ ≤ 1 then
    p.ν * ((uStar + d) ^ p.γ - uStar ^ p.γ)
  else
    p.ν * ((uStar + d) ^ (p.γ - 1) * d)

theorem intervalPowerSourceGapConstant_pos
    (p : CM2Params) {uStar d : ℝ}
    (huStar : 0 < uStar) (hd : 0 < d) :
    0 < intervalPowerSourceGapConstant p uStar d := by
  unfold intervalPowerSourceGapConstant
  split_ifs with hγ1
  · have hpowStrict : uStar ^ p.γ < (uStar + d) ^ p.γ :=
      Real.rpow_lt_rpow huStar.le (by linarith) p.hγ
    exact mul_pos p.hν (sub_pos.mpr hpowStrict)
  · have hγge : 1 ≤ p.γ := le_of_not_ge hγ1
    have hbase : 0 < uStar + d := by linarith
    exact mul_pos p.hν
      (mul_pos (Real.rpow_pos_of_pos hbase (p.γ - 1)) hd)

/-- The explicit source-gap constant is a lower bound for the integrated
power deficit. -/
theorem intervalPowerSourceGapConstant_le_integral
    (p : CM2Params) {U : ℝ → ℝ} {uStar M d : ℝ}
    (huStar : 0 < uStar) (hd : 0 < d)
    (hU_cont : Continuous U) (hU_nonneg : ∀ y, 0 ≤ U y)
    (hU_le : ∀ y, U y ≤ M)
    (hmass : (∫ y, U y ∂(intervalMeasure 1)) = uStar)
    (hMgap : uStar + d ≤ M) :
    intervalPowerSourceGapConstant p uStar d ≤
      ∫ y, p.ν * (M ^ p.γ - U y ^ p.γ) ∂(intervalMeasure 1) := by
  letI : IsProbabilityMeasure (intervalMeasure 1) :=
    intervalMeasure_one_isProbability
  have hM : 0 < M := lt_of_lt_of_le (by linarith) hMgap
  have hUint : Integrable U (intervalMeasure 1) :=
    intervalMeasure_integrable_of_continuous_nonneg_le
      hU_cont hU_nonneg hU_le
  have hUpowInt : Integrable (fun y => U y ^ p.γ) (intervalMeasure 1) :=
    intervalMeasure_rpow_integrable_of_continuous_nonneg_le
      p.γ p.hγ.le hU_cont hU_nonneg hU_le
  have hsourceIntegral :
      (∫ y, p.ν * (M ^ p.γ - U y ^ p.γ) ∂(intervalMeasure 1)) =
        p.ν * (M ^ p.γ - ∫ y, U y ^ p.γ ∂(intervalMeasure 1)) := by
    rw [integral_const_mul]
    have hconst : Integrable (fun _y : ℝ => M ^ p.γ) (intervalMeasure 1) :=
      integrable_const _
    rw [integral_sub hconst hUpowInt,
      intervalMeasure_integral_const (L := (1 : ℝ)) (c := M ^ p.γ) (by norm_num)]
    ring
  by_cases hγ1 : p.γ ≤ 1
  ·
    have hbase : 0 ≤ uStar + d := by linarith
    have hpowStrict : uStar ^ p.γ < (uStar + d) ^ p.γ :=
      Real.rpow_lt_rpow huStar.le (by linarith) p.hγ
    have hJensen :
        (∫ y, U y ^ p.γ ∂(intervalMeasure 1)) ≤ uStar ^ p.γ := by
      have hj := (Real.concaveOn_rpow p.hγ.le hγ1).le_map_integral
        (Real.continuous_rpow_const p.hγ.le).continuousOn isClosed_Ici
        (Filter.Eventually.of_forall hU_nonneg) hUint
        (by simpa [Function.comp_apply] using hUpowInt)
      simpa [Function.comp_apply, hmass] using hj
    have hMpow : (uStar + d) ^ p.γ ≤ M ^ p.γ :=
      Real.rpow_le_rpow hbase hMgap p.hγ.le
    rw [hsourceIntegral]
    rw [intervalPowerSourceGapConstant, if_pos hγ1]
    exact mul_le_mul_of_nonneg_left (by linarith) p.hν.le
  · have hγge : 1 ≤ p.γ := le_of_not_ge hγ1
    have hγsub : 0 ≤ p.γ - 1 := sub_nonneg.mpr hγge
    have hbase : 0 < uStar + d := by linarith
    have hpoint : ∀ y,
        U y ^ p.γ ≤ M ^ (p.γ - 1) * U y := by
      intro y
      have hUrpow : U y ^ (p.γ - 1) ≤ M ^ (p.γ - 1) :=
        Real.rpow_le_rpow (hU_nonneg y) (hU_le y) hγsub
      calc
        U y ^ p.γ = U y ^ ((p.γ - 1) + 1) := by ring_nf
        _ = U y ^ (p.γ - 1) * U y ^ (1 : ℝ) :=
          Real.rpow_add_of_nonneg (hU_nonneg y) hγsub zero_le_one
        _ = U y ^ (p.γ - 1) * U y := by rw [Real.rpow_one]
        _ ≤ M ^ (p.γ - 1) * U y :=
          mul_le_mul_of_nonneg_right hUrpow (hU_nonneg y)
    have hlinearInt : Integrable
        (fun y => M ^ (p.γ - 1) * U y) (intervalMeasure 1) :=
      hUint.const_mul _
    have hpowIntegral :
        (∫ y, U y ^ p.γ ∂(intervalMeasure 1)) ≤
          M ^ (p.γ - 1) * uStar := by
      have hmono := integral_mono hUpowInt hlinearInt hpoint
      simpa [integral_const_mul, hmass] using hmono
    have hMsplit : M ^ p.γ = M ^ (p.γ - 1) * M := by
      calc
        M ^ p.γ = M ^ ((p.γ - 1) + 1) := by ring_nf
        _ = M ^ (p.γ - 1) * M ^ (1 : ℝ) :=
          Real.rpow_add_of_nonneg hM.le hγsub zero_le_one
        _ = M ^ (p.γ - 1) * M := by rw [Real.rpow_one]
    have hbasePow : (uStar + d) ^ (p.γ - 1) ≤ M ^ (p.γ - 1) :=
      Real.rpow_le_rpow hbase.le hMgap hγsub
    have hgapNonneg : 0 ≤ M - uStar := by linarith
    have hproduct : (uStar + d) ^ (p.γ - 1) * d ≤
        M ^ (p.γ - 1) * (M - uStar) := by
      exact mul_le_mul hbasePow (by linarith) hd.le
        (Real.rpow_nonneg hM.le _)
    rw [hsourceIntegral]
    rw [intervalPowerSourceGapConstant, if_neg hγ1]
    apply mul_le_mul_of_nonneg_left _ p.hν.le
    rw [hMsplit]
    exact le_trans hproduct (by linarith)

/-- Uniform positive integral of the power-source deficit.  The witness is
explicit in each exponent regime and is independent of the profile maximum
`M` once `M >= uStar + d`. -/
theorem intervalPowerSourceDeficit_uniform_integral_gap
    (p : CM2Params) {U : ℝ → ℝ} {uStar M d : ℝ}
    (huStar : 0 < uStar) (hd : 0 < d)
    (hU_cont : Continuous U) (hU_nonneg : ∀ y, 0 ≤ U y)
    (hU_le : ∀ y, U y ≤ M)
    (hmass : (∫ y, U y ∂(intervalMeasure 1)) = uStar)
    (hMgap : uStar + d ≤ M) :
    ∃ q > 0,
      q ≤ ∫ y, p.ν * (M ^ p.γ - U y ^ p.γ) ∂(intervalMeasure 1) := by
  exact ⟨intervalPowerSourceGapConstant p uStar d,
    intervalPowerSourceGapConstant_pos p huStar hd,
    intervalPowerSourceGapConstant_le_integral
      p huStar hd hU_cont hU_nonneg hU_le hmass hMgap⟩

#print axioms intervalMeasure_integrable_of_continuous_nonneg_le
#print axioms intervalMeasure_rpow_integrable_of_continuous_nonneg_le
#print axioms intervalPowerSourceGapConstant_pos
#print axioms intervalPowerSourceGapConstant_le_integral
#print axioms intervalPowerSourceDeficit_uniform_integral_gap

end ShenWork.Paper3
