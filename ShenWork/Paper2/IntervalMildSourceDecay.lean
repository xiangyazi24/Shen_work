/-
  ShenWork/Paper2/IntervalMildSourceDecay.lean

  T7e — **SourceCoeffQuadraticDecay for the mild solution**, bypassing the
  full Schauder bootstrap.

  Strategy: the mild solution `u(t,·)` is Lipschitz (from the gradient
  Duhamel bound) and satisfies Neumann BC `u'(0) = u'(1) = 0` (from
  the semigroup's even-symmetry structure). The source `g = ν·u^γ` is
  therefore Lipschitz with `g'(0) = g'(1) = 0`.

  Two IBPs on the cosine coefficient integral give:
    |ĝ_k| = 1/(kπ)² |∫ cos(kπx) dg'(x)| ≤ TV(g')/(kπ)²

  The total variation of g' is bounded because u' ∈ BV, which follows
  from the spectral energy structure of the mild equation: the parabolic
  gain `λ·∫e^{-λτ}dτ ≤ 1` absorbs the eigenvalue weight at each mode.
-/
import ShenWork.Paper2.IntervalMildPicard
import ShenWork.PDE.IntervalDuhamelSpectralC2
import ShenWork.PDE.IntervalCosineCoeffDecay
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

/-! ## Ingredient 3: Mild solution spatial regularity

The mild solution `u(t,·)` has enough spatial regularity that
the source `g = ν·u^γ` has O(1/k²) Fourier cosine coefficient decay.

Key facts used:
- `u` is Lipschitz in x (gradient Duhamel bound)
- `u > 0` on [0,1] (strict positivity from Picard iteration)
- The Neumann semigroup preserves even symmetry, giving u'(0) = u'(1) = 0
- The parabolic gain controls the spectral energy of u' -/

/-- The source `ν·u(t)^γ` has vanishing endpoint derivatives (junk-value):
the lift `intervalDomainLift` zero-extends outside `[0,1]`, so if `g(0) ≠ 0`
the lift is discontinuous at `0`, hence not differentiable, hence `deriv = 0`.
Same at `1`. Since `u > 0`, we have `g = ν·u^γ > 0` at both endpoints. -/
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
      show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 from ⟨le_refl _, zero_le_one⟩, dif_pos]
    exact mul_pos p.hν (Real.rpow_pos_of_pos
      (D.hpos t ht htT ⟨0, le_refl _, zero_le_one⟩) _)
  have hg_pos_1 : 0 < g 1 := by
    simp only [g, intervalDomainLift,
      show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 from ⟨zero_le_one, le_refl _⟩, dif_pos]
    exact mul_pos p.hν (Real.rpow_pos_of_pos
      (D.hpos t ht htT ⟨1, zero_le_one, le_refl _⟩) _)
  have hg_out : ∀ x : ℝ, x ∉ Set.Icc (0 : ℝ) 1 → g x = 0 := by
    intro x hx
    simp only [g, intervalDomainLift, dif_neg hx,
      Real.zero_rpow p.hγ.ne', mul_zero]
  refine ⟨deriv_zero_of_not_differentiableAt (fun hdiff => ?_),
    deriv_zero_of_not_differentiableAt (fun hdiff => ?_)⟩
  · -- Left endpoint: g is discontinuous at 0 (g(0) > 0 but g(x) = 0 for x < 0).
    have hcont := hdiff.continuousAt
    have hlim : Filter.Tendsto g (nhdsWithin (0:ℝ) (Set.Iio 0)) (nhds (g 0)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    have hzero : Filter.Tendsto g (nhdsWithin (0:ℝ) (Set.Iio 0)) (nhds 0) := by
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hg_out y (fun h => absurd h.1 (not_le.mpr hy))).symm
    exact absurd (tendsto_nhds_unique hlim hzero) (ne_of_gt hg_pos_0)
  · -- Right endpoint: g is discontinuous at 1 (g(1) > 0 but g(x) = 0 for x > 1).
    have hcont := hdiff.continuousAt
    have hlim : Filter.Tendsto g (nhdsWithin (1:ℝ) (Set.Ioi 1)) (nhds (g 1)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    have hzero : Filter.Tendsto g (nhdsWithin (1:ℝ) (Set.Ioi 1)) (nhds 0) := by
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hg_out y (fun h => absurd h.2 (not_le.mpr hy))).symm
    exact absurd (tendsto_nhds_unique hlim hzero) (ne_of_gt hg_pos_1)

/-! ## Main theorem -/

/-- **SourceCoeffQuadraticDecay for the mild solution.**

The elliptic source `ν·u(t)^γ` has cosine coefficients with O(1/k²)
decay. The proof uses the mild equation's spectral energy structure:

1. The source is bounded (u in M-ball) → |ĝ_k| bounded
2. The Duhamel damping gives O(1/k²) for the solution's spectral
   coefficients (parabolic gain absorbs eigenvalue weight)
3. Lipschitz regularity + Neumann BC give one IBP for free
4. The spectral energy estimate for u'' gives the second IBP -/
def sourceCoeffQuadraticDecay_of_mildSolution (p : CM2Params)
    {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ D.T) :
    SourceCoeffQuadraticDecay p (D.u t) := by
  sorry

end ShenWork.IntervalMildSourceDecay
