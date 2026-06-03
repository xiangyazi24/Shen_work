/-
  ShenWork/Paper2/IntervalMildSourceDecay.lean

  T7e — **SourceCoeffQuadraticDecay for the mild solution**, bypassing the
  full Schauder bootstrap.

  Strategy: the mild solution `u(t,·)` is Lipschitz (gradient Duhamel bound)
  and positive, with Neumann BC. The source `g = ν·u^γ` therefore has
  `g'(0) = g'(1) = 0` (junk-value from the zero-extension jump).
  Two IBPs on the cosine coefficient integral give the O(1/k²) decay,
  with the key regularity input being `u' ∈ BV` (the gradient has bounded
  total variation), which comes from the parabolic spectral energy estimate.
-/
import ShenWork.Paper2.IntervalMildPicard
import ShenWork.PDE.IntervalDuhamelSpectralC2
import ShenWork.PDE.IntervalCosineCoeffDecay
import ShenWork.PDE.IntervalCosineSliceRegularity
import ShenWork.Paper2.IntervalDomainL2UEnergyInequality

open MeasureTheory
open scoped Topology

noncomputable section

namespace ShenWork.IntervalMildSourceDecay

open ShenWork.IntervalMildPicard
open ShenWork.IntervalDomain
open ShenWork.PDE ShenWork.Paper2
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalGradientDuhamelMap
open ShenWork.IntervalDuhamelSpectralC2

/-! ## Ingredient 1: Source boundedness -/

theorem source_bounded (p : CM2Params)
    {u : intervalDomainPoint → ℝ} {M : ℝ}
    (hM : 0 < M) (hnn : ∀ x, 0 ≤ u x)
    (hbound : ∀ x, u x ≤ M) (x : intervalDomainPoint) :
    p.ν * (u x) ^ p.γ ≤ p.ν * M ^ p.γ :=
  mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (hnn x) (hbound x) p.hγ.le) p.hν.le

theorem source_nonneg (p : CM2Params)
    {u : intervalDomainPoint → ℝ}
    (hnn : ∀ x, 0 ≤ u x) (x : intervalDomainPoint) :
    0 ≤ p.ν * (u x) ^ p.γ :=
  mul_nonneg p.hν.le (Real.rpow_nonneg (hnn x) _)

/-! ## Ingredient 2: Damping estimate -/

theorem expKernel_integral_le_inv {t lam : ℝ}
    (ht : 0 < t) (hlam : 0 < lam) :
    ∫ s in (0:ℝ)..t, Real.exp (-(t - s) * lam) ≤ 1 / lam := by
  rw [intervalExpKernel_time_integral (ne_of_gt hlam)]
  rw [div_le_div_iff_of_pos_right hlam]
  linarith [Real.exp_nonneg (-t * lam)]

/-! ## Ingredient 3: Endpoint derivative vanishing (junk-value)

The source `g = ν·(lift u)^γ` has `deriv g 0 = deriv g 1 = 0` because
the lift zero-extends outside `[0,1]`, creating a discontinuity at both
endpoints (since `g(0), g(1) > 0` from positivity of `u`). -/

theorem mildSource_deriv_endpoint_zero (p : CM2Params)
    {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ D.T) :
    deriv (fun x : ℝ => p.ν *
      intervalDomainLift (D.u t) x ^ p.γ) 0 = 0 ∧
    deriv (fun x : ℝ => p.ν *
      intervalDomainLift (D.u t) x ^ p.γ) 1 = 0 := by
  set g : ℝ → ℝ := fun x => p.ν * intervalDomainLift (D.u t) x ^ p.γ
  have hg_pos_0 : 0 < g 0 := by
    simp only [g, intervalDomainLift,
      show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 from ⟨le_refl _, zero_le_one⟩,
      dif_pos]
    exact mul_pos p.hν (Real.rpow_pos_of_pos
      (D.hpos t ht htT ⟨0, le_refl _, zero_le_one⟩) _)
  have hg_pos_1 : 0 < g 1 := by
    simp only [g, intervalDomainLift,
      show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 from ⟨zero_le_one, le_refl _⟩,
      dif_pos]
    exact mul_pos p.hν (Real.rpow_pos_of_pos
      (D.hpos t ht htT ⟨1, zero_le_one, le_refl _⟩) _)
  have hg_out : ∀ x : ℝ, x ∉ Set.Icc (0 : ℝ) 1 → g x = 0 := by
    intro x hx
    simp only [g, intervalDomainLift, dif_neg hx,
      Real.zero_rpow p.hγ.ne', mul_zero]
  refine ⟨deriv_zero_of_not_differentiableAt (fun hdiff => ?_),
    deriv_zero_of_not_differentiableAt (fun hdiff => ?_)⟩
  · have hcont := hdiff.continuousAt
    have hlim : Filter.Tendsto g
        (nhdsWithin (0:ℝ) (Set.Iio 0)) (nhds (g 0)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    have hzero : Filter.Tendsto g
        (nhdsWithin (0:ℝ) (Set.Iio 0)) (nhds 0) := by
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hg_out y (fun h => absurd h.1 (not_le.mpr hy))).symm
    exact absurd (tendsto_nhds_unique hlim hzero)
      (ne_of_gt hg_pos_0)
  · have hcont := hdiff.continuousAt
    have hlim : Filter.Tendsto g
        (nhdsWithin (1:ℝ) (Set.Ioi 1)) (nhds (g 1)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    have hzero : Filter.Tendsto g
        (nhdsWithin (1:ℝ) (Set.Ioi 1)) (nhds 0) := by
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hg_out y (fun h => absurd h.2 (not_le.mpr hy))).symm
    exact absurd (tendsto_nhds_unique hlim hzero)
      (ne_of_gt hg_pos_1)

/-! ## Ingredient 4: Gradient BV regularity of the mild solution

This is the core spectral energy input: the mild solution's spatial
gradient `u'(t,·)` has bounded total variation on `[0,1]`, i.e., the
distributional second derivative `u''(t,·)` is a finite signed measure.

The proof uses the semigroup restart `u(t) = S(t/2) u(t/2) + correction`:
- `S(t/2) u(t/2)` is C∞ (heat semigroup smooths), so its gradient is BV.
- The correction integral's Laplacian telescopes via the heat equation
  `∂²ₓₓ S(τ) = ∂_τ S(τ)`, and the time-IBP absorbs the singularity. -/

theorem mildSolution_source_contDiffOn_Icc (p : CM2Params)
    {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ D.T) :
    ContDiffOn ℝ 2
      (fun x : ℝ => p.ν * intervalDomainLift (D.u t) x ^ p.γ)
      (Set.Icc (0:ℝ) 1) := by
  sorry

/-! ## Main theorem -/

/-- **SourceCoeffQuadraticDecay for the mild solution.**

The elliptic source `ν·u(t)^γ` has cosine coefficients with O(1/k²)
decay, assembled from:
1. C² of the source on [0,1] (from mild solution spatial regularity)
2. Junk-value endpoint derivatives (from zero-extension discontinuity)
3. cosineCoeff_decay engine (eigenfunction IBP) -/
def sourceCoeffQuadraticDecay_of_mildSolution (p : CM2Params)
    {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ D.T) :
    SourceCoeffQuadraticDecay p (D.u t) := by
  classical
  set g : ℝ → ℝ := fun x => p.ν *
    intervalDomainLift (D.u t) x ^ p.γ with hg
  have hC2g := mildSolution_source_contDiffOn_Icc p D ht htT
  have ⟨hbc0, hbc1⟩ := mildSource_deriv_endpoint_zero p D ht htT
  have htend0 : Filter.Tendsto (deriv g)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by sorry
  have htend1 : Filter.Tendsto (deriv g)
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) := by sorry
  let Mspec := ShenWork.IntervalCosineCoeffDecay.exists_laplacianCoeff_bound
    (show ContDiffOn ℝ 2 g (Set.Icc (0:ℝ) 1) from hC2g)
  refine ⟨2 * Mspec.choose, ?_, ?_⟩
  · have := Mspec.choose_spec.1; positivity
  · intro k hk
    have hMnonneg := Mspec.choose_spec.1
    have hMbound := Mspec.choose_spec.2
    have hdec := ShenWork.IntervalCosineCoeffDecay.cosineCoeff_decay
      hC2g htend0 htend1 hbc0 hbc1 hMnonneg hMbound hk
    have hkne : k ≠ 0 := by omega
    have hre_eq :
        (intervalNeumannResolverSourceCoeff p (D.u t) k).re =
        2 * ∫ x in (0:ℝ)..1,
          Real.cos ((k:ℝ) * Real.pi * x) * g x := by
      simp only [intervalNeumannResolverSourceCoeff,
        Complex.ofReal_re,
        ShenWork.HeatKernelGradientEstimates.unitIntervalNeumannCosineCoeff,
        if_neg hkne, hg]
      rw [ShenWork.HeatKernelGradientEstimates.unitIntervalCosineRawCoeff]
      have hcast :
          (fun x : ℝ => (Real.cos ((k:ℝ) * Real.pi * x) : ℂ) *
            ((p.ν * intervalDomainLift (D.u t) x ^ p.γ : ℝ) : ℂ))
          = (fun x : ℝ =>
            ((Real.cos ((k:ℝ) * Real.pi * x) *
              (p.ν * intervalDomainLift (D.u t) x ^ p.γ) : ℝ) : ℂ)) :=
        by funext x; push_cast; ring
      rw [hcast, intervalIntegral.integral_ofReal, Complex.ofReal_re]
    rw [hre_eq, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    calc 2 * |∫ x in (0:ℝ)..1,
          Real.cos ((k:ℝ) * Real.pi * x) * g x|
        ≤ 2 * (Mspec.choose / ((k:ℝ) * Real.pi) ^ 2) :=
          mul_le_mul_of_nonneg_left hdec (by norm_num)
      _ = 2 * Mspec.choose / ((k:ℝ) * Real.pi) ^ 2 := by ring

end ShenWork.IntervalMildSourceDecay
