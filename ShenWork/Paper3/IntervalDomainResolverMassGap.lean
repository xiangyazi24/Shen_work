import ShenWork.Paper3.IntervalDomainUniformHeatKernelFloor
import ShenWork.Paper2.IntervalDomainResolverStrictPos
import ShenWork.PDE.IntervalSemigroupComposition
import ShenWork.Paper2.IntervalTruncatedWeakBarrierComparison

/-!
# Quantitative mass-to-resolver positivity on the unit interval

For a nonnegative source `f`, the unit-time heat flow has the pointwise floor
`S(1)f >= kappa * integral f`.  The resolvent identity

`R_mu f = integral_0^1 exp(-mu t) S(t)f dt + exp(-mu) R_mu(S(1)f)`

then turns source mass into a uniform positive resolver gap.  The proof below
is coefficient-level and uses the already proved heat-Laplace representation;
it assumes no compactness, stability, or orbit-convergence package.
-/

open Filter MeasureTheory Set Topology

noncomputable section

namespace ShenWork.Paper3

open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalFullKernelSpectralClean
open ShenWork.IntervalResolverPositivity
open ShenWork.IntervalSemigroupComposition
open ShenWork.IntervalDomainResolverStrictPos
open ShenWork.Paper2
open ShenWork.Paper2.IntervalTruncatedWeakBarrierComparison
open ShenWork.PDE (intervalNeumannResolverWeight)

/-- The quantitative resolver coefficient multiplying the source mass. -/
def unitIntervalResolverMassGapConstant (p : CM2Params) : ℝ :=
  Real.exp (-p.μ) * unitWindowHeatKernelFloor / p.μ

theorem unitIntervalResolverMassGapConstant_pos (p : CM2Params) :
    0 < unitIntervalResolverMassGapConstant p := by
  unfold unitIntervalResolverMassGapConstant
  exact div_pos (mul_pos (Real.exp_pos _) unitWindowHeatKernelFloor_pos) p.hμ

/-- Interior quantitative mass-to-resolver bound for a globally continuous,
bounded, nonnegative representative. -/
theorem cosineResolver_ge_massGap_interior
    (p : CM2Params) {f : ℝ → ℝ} {B : ℝ}
    (hf_cont : Continuous f) (hB : 0 ≤ B)
    (hf_nonneg : ∀ y, 0 ≤ f y) (hf_bound : ∀ y, |f y| ≤ B)
    (hf_int : Integrable f (intervalMeasure 1))
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    unitIntervalResolverMassGapConstant p * (∫ y, f y ∂(intervalMeasure 1)) ≤
      ∑' k, cosineCoeffs f k * unitIntervalCosineMode k x /
        (p.μ + unitIntervalCosineEigenvalue k) := by
  let mass : ℝ := ∫ y, f y ∂(intervalMeasure 1)
  let c0 : ℝ := unitWindowHeatKernelFloor * mass
  let Sf : ℝ → ℝ := fun y => intervalFullSemigroupOperator 1 f y
  have hmass : 0 ≤ mass := by
    dsimp [mass]
    exact integral_nonneg hf_nonneg
  have hc0 : 0 ≤ c0 := mul_nonneg unitWindowHeatKernelFloor_pos.le hmass
  have hcoeff : ∀ n, |cosineCoeffs f n| ≤ 2 * B :=
    cosineCoeffs_abs_le_of_continuous_bounded hf_cont.continuousOn hB
      (fun y _ => hf_bound y)
  have hfsq : Summable (fun n : ℕ => (cosineCoeffs f n) ^ 2) :=
    cosineCoeffs_sq_summable_of_continuousOn hf_cont.continuousOn
  have hSf_cont : Continuous Sf := by
    exact (intervalFullSemigroupOperator_contDiff_two_clean
      (t := (1 : ℝ)) (by norm_num) hf_cont hcoeff).continuous
  have hSf_coeff : ∀ n,
      cosineCoeffs Sf n = Real.exp (-unitIntervalCosineEigenvalue n) *
        cosineCoeffs f n := by
    intro n
    simpa [Sf] using cosineCoeffs_semigroup
      (t := (1 : ℝ)) (by norm_num) hf_cont hcoeff n
  have hSf_ge : ∀ y, y ∈ Icc (0 : ℝ) 1 → c0 ≤ Sf y := by
    intro y hy
    simpa [Sf, c0, mass] using
      unitWindowHeatKernelFloor_mul_integral_le_semigroup
        (t := (1 : ℝ)) (x := y) (by norm_num) hy hf_int
        hf_cont.aestronglyMeasurable (fun z _ => hf_nonneg z) hf_bound
  let g : ℝ → ℝ := fun y => max c0 (Sf (clamp01 y))
  have hg_cont : Continuous g := by
    dsimp [g]
    exact continuous_const.max (hSf_cont.comp clamp01_continuous)
  have hg_ge : ∀ y, c0 ≤ g y := fun y => le_max_left _ _
  have hg_eq : ∀ y, y ∈ Icc (0 : ℝ) 1 → g y = Sf y := by
    intro y hy
    dsimp [g]
    rw [clamp01_eq_self hy, max_eq_right (hSf_ge y hy)]
  have hgsub_sq : Summable
      (fun n : ℕ => (cosineCoeffs (fun y => g y - c0) n) ^ 2) :=
    cosineCoeffs_sq_summable_of_continuousOn
      (hg_cont.sub continuous_const).continuousOn
  have hRsf_lower : c0 / p.μ ≤
      ∑' k, cosineCoeffs Sf k * unitIntervalCosineMode k x /
        (p.μ + unitIntervalCosineEigenvalue k) := by
    have h := reconstruction_ge_const p hg_cont hg_ge hgsub_sq hx
    have hcoeff_eq : ∀ k, cosineCoeffs g k = cosineCoeffs Sf k := by
      intro k
      exact cosineCoeffs_congr_on_Icc hg_eq k
    simpa only [hcoeff_eq] using h
  have hSf_sq : Summable (fun n : ℕ => (cosineCoeffs Sf n) ^ 2) :=
    cosineCoeffs_sq_summable_of_continuousOn hSf_cont.continuousOn
  let targetTerm : ℕ → ℝ := fun k =>
    cosineCoeffs f k * unitIntervalCosineMode k x /
      (p.μ + unitIntervalCosineEigenvalue k)
  let heatTailTerm : ℕ → ℝ := fun k =>
    Real.exp (-p.μ) *
      (cosineCoeffs Sf k * unitIntervalCosineMode k x /
        (p.μ + unitIntervalCosineEigenvalue k))
  let truncTerm : ℕ → ℝ := fun k =>
    cosineCoeffs f k * unitIntervalCosineMode k x *
      ((1 - Real.exp (-(p.μ + unitIntervalCosineEigenvalue k))) /
        (p.μ + unitIntervalCosineEigenvalue k))
  have htarget_sum : Summable targetTerm := by
    simpa [targetTerm] using summable_resolverTarget (p := p) hfsq x
  have hRsf_sum : Summable (fun k =>
      cosineCoeffs Sf k * unitIntervalCosineMode k x /
        (p.μ + unitIntervalCosineEigenvalue k)) :=
    summable_resolverTarget (p := p) hSf_sq x
  have htail_sum : Summable heatTailTerm := by
    simpa [heatTailTerm] using hRsf_sum.mul_left (Real.exp (-p.μ))
  have hterm : ∀ k, targetTerm k = truncTerm k + heatTailTerm k := by
    intro k
    dsimp only [targetTerm, truncTerm, heatTailTerm]
    rw [hSf_coeff k]
    have hexp : Real.exp (-p.μ) *
        Real.exp (-unitIntervalCosineEigenvalue k) =
      Real.exp (-(p.μ + unitIntervalCosineEigenvalue k)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← hexp]
    have hden : p.μ + unitIntervalCosineEigenvalue k ≠ 0 := by
      apply ne_of_gt
      have hlam : 0 ≤ unitIntervalCosineEigenvalue k := by
        unfold unitIntervalCosineEigenvalue
        positivity
      linarith [p.hμ]
    field_simp [hden]
    ring
  have htrunc_sum : Summable truncTerm := by
    have heq : truncTerm = targetTerm - heatTailTerm := by
      funext k
      have := hterm k
      dsimp only [Pi.sub_apply]
      linarith
    rw [heq]
    exact htarget_sum.sub htail_sum
  have htrunc_nonneg : 0 ≤ ∑' k, truncTerm k := by
    have htrunc := laplaceResolverTrunc_eq_tsum
      (p := p) (â := cosineCoeffs f) hfsq (x := x) (T := (1 : ℝ)) (by norm_num)
    have hnonneg := laplaceHeatTrunc_nonneg
      (p := p) hf_cont hf_nonneg hx (T := (1 : ℝ)) (by norm_num)
    rw [htrunc] at hnonneg
    simpa [truncTerm] using hnonneg
  have hdecomp : (∑' k, targetTerm k) =
      (∑' k, truncTerm k) + Real.exp (-p.μ) *
        (∑' k, cosineCoeffs Sf k * unitIntervalCosineMode k x /
          (p.μ + unitIntervalCosineEigenvalue k)) := by
    calc
      (∑' k, targetTerm k) = ∑' k, (truncTerm k + heatTailTerm k) := by
        apply tsum_congr
        intro k
        exact hterm k
      _ = (∑' k, truncTerm k) + ∑' k, heatTailTerm k :=
        htrunc_sum.tsum_add htail_sum
      _ = _ := by simp only [heatTailTerm, tsum_mul_left]
  change unitIntervalResolverMassGapConstant p * mass ≤ ∑' k, targetTerm k
  rw [hdecomp]
  have htail_lower : Real.exp (-p.μ) * (c0 / p.μ) ≤
      Real.exp (-p.μ) *
        (∑' k, cosineCoeffs Sf k * unitIntervalCosineMode k x /
          (p.μ + unitIntervalCosineEigenvalue k)) :=
    mul_le_mul_of_nonneg_left hRsf_lower (Real.exp_pos _).le
  have hmain : Real.exp (-p.μ) * (c0 / p.μ) ≤
      (∑' k, truncTerm k) + Real.exp (-p.μ) *
        (∑' k, cosineCoeffs Sf k * unitIntervalCosineMode k x /
          (p.μ + unitIntervalCosineEigenvalue k)) := by
    linarith
  simpa [unitIntervalResolverMassGapConstant, c0, div_eq_mul_inv, mul_assoc,
    mul_left_comm, mul_comm] using hmain

/-- The resolved cosine series is continuous in space.  The summable majorant
is exactly the existing `ℓ²` source / `ℓ²` resolvent-weight estimate. -/
theorem cosineResolver_continuous (p : CM2Params) {f : ℝ → ℝ}
    (hfsq : Summable (fun k : ℕ => (cosineCoeffs f k) ^ 2)) :
    Continuous (fun x => ∑' k, cosineCoeffs f k * unitIntervalCosineMode k x /
      (p.μ + unitIntervalCosineEigenvalue k)) := by
  have hmajor := summable_abs_sourceCoeff_mul_weight (p := p) hfsq
  refine continuous_tsum (fun k => ?_) hmajor (fun k x => ?_)
  · unfold unitIntervalCosineMode
    fun_prop
  · have hdpos : 0 < p.μ + unitIntervalCosineEigenvalue k := by
      have hlam : 0 ≤ unitIntervalCosineEigenvalue k := by
        unfold unitIntervalCosineEigenvalue
        positivity
      linarith [p.hμ]
    have heig : intervalNeumannResolverWeight p k =
        1 / (p.μ + unitIntervalCosineEigenvalue k) := by
      rw [intervalNeumannResolverWeight]
      congr 2
      rw [show unitIntervalNeumannSpectrum.eigenvalue k =
        (k : ℝ) ^ 2 * Real.pi ^ 2 from rfl, unitIntervalCosineEigenvalue]
      ring
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hdpos, heig,
      div_eq_mul_inv, one_div]
    refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr hdpos.le)
    calc
      |cosineCoeffs f k| * |unitIntervalCosineMode k x|
          ≤ |cosineCoeffs f k| * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            rw [unitIntervalCosineMode]
            exact Real.abs_cos_le_one _
      _ = |cosineCoeffs f k| := mul_one _

/-- Closed-interval quantitative mass-to-resolver bound.  Endpoint values are
obtained from the interior theorem by continuity; no boundary maximum
principle or compactness package is assumed. -/
theorem cosineResolver_ge_massGap_Icc
    (p : CM2Params) {f : ℝ → ℝ} {B : ℝ}
    (hf_cont : Continuous f) (hB : 0 ≤ B)
    (hf_nonneg : ∀ y, 0 ≤ f y) (hf_bound : ∀ y, |f y| ≤ B)
    (hf_int : Integrable f (intervalMeasure 1))
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    unitIntervalResolverMassGapConstant p * (∫ y, f y ∂(intervalMeasure 1)) ≤
      ∑' k, cosineCoeffs f k * unitIntervalCosineMode k x /
        (p.μ + unitIntervalCosineEigenvalue k) := by
  let Rf : ℝ → ℝ := fun z => ∑' k,
    cosineCoeffs f k * unitIntervalCosineMode k z /
      (p.μ + unitIntervalCosineEigenvalue k)
  have hfsq : Summable (fun n : ℕ => (cosineCoeffs f n) ^ 2) :=
    cosineCoeffs_sq_summable_of_continuousOn hf_cont.continuousOn
  have hRf_cont : Continuous Rf := by
    simpa [Rf] using cosineResolver_continuous p hfsq
  have hsub : Ioo (0 : ℝ) 1 ⊆
      {z : ℝ | unitIntervalResolverMassGapConstant p *
        (∫ y, f y ∂(intervalMeasure 1)) ≤ Rf z} := by
    intro z hz
    simpa [Rf] using cosineResolver_ge_massGap_interior p hf_cont hB hf_nonneg
      hf_bound hf_int hz
  have hclosed : Icc (0 : ℝ) 1 ⊆
      {z : ℝ | unitIntervalResolverMassGapConstant p *
        (∫ y, f y ∂(intervalMeasure 1)) ≤ Rf z} := by
    rw [← closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact (isClosed_le continuous_const hRf_cont).closure_subset_iff.mpr hsub
  exact hclosed hx

#print axioms cosineResolver_ge_massGap_interior
#print axioms cosineResolver_continuous
#print axioms cosineResolver_ge_massGap_Icc

end ShenWork.Paper3
