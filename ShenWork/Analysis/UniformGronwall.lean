import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals

/-!
# Uniform Gronwall Lemma (Temam)

The Uniform Gronwall lemma converts **time-integrated** bounds on a
non-negative function into **pointwise-in-time** bounds, given a
differential inequality. This is a standard tool in dissipative PDE
theory (see Temam, *Infinite-Dimensional Dynamical Systems in
Mechanics and Physics*, Lemma III.1.1).

## Main result

`uniform_gronwall_bound_const`: if `y' ≤ α·y + β` on `[0,T]` with
`y ≥ 0`, and `∫_t^{t+r} y ≤ a₃` for all valid `t`, then
`y(t) ≤ (a₃/r + β·r)·exp(α·r)` for `t ∈ [r, T]`.

The proof applies the standard Gronwall inequality (Mathlib's
`gronwallBound`) starting from each `s ∈ [t-r, t]`, then integrates
over `s`.
-/

open MeasureTheory Set

noncomputable section

namespace ShenWork.Analysis.UniformGronwall

/-- **Uniform Gronwall lemma with constant coefficients.**

Given a continuous non-negative function `y` on `[0, T]` satisfying
`y'(t) ≤ α·y(t) + β` (in the liminf-of-right-derivative sense),
if the time integral `∫_t^{t+r} y(s) ds ≤ a₃` for all `t ∈ [0, T-r]`,
then `y(t) ≤ (a₃/r + β·r) · exp(α·r)` for all `t ∈ [r, T]`.

This is the workhorse for upgrading energy/dissipation estimates
(time-integrated) to uniform-in-time bounds.
-/
theorem uniform_gronwall_bound_const
    {y : ℝ → ℝ} {T α β r a₃ : ℝ}
    (hr : 0 < r) (hrT : r ≤ T)
    (hα_nonneg : 0 ≤ α) (hβ_nonneg : 0 ≤ β) (ha₃_nonneg : 0 ≤ a₃)
    (hy_cont : ContinuousOn y (Icc 0 T))
    (hy_nonneg : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ y t)
    (hderiv :
      ∀ t ∈ Ico (0 : ℝ) T,
        ∀ r' > 0, ∃ r'' ∈ Ioo (0 : ℝ) r',
          (y (t + r'') - y t) / r'' ≤ α * y t + β + 1)
    (hint : ∀ t, 0 ≤ t → t + r ≤ T →
      ∫ s in t..t + r, y s ≤ a₃) :
    ∀ t, r ≤ t → t ≤ T →
      y t ≤ (a₃ / r + β * r) * Real.exp (α * r) := by
  sorry

/-- Variant taking `HasDerivAt` hypotheses instead of liminf slopes. -/
theorem uniform_gronwall_bound_const_of_hasDerivAt
    {y y' : ℝ → ℝ} {T α β r a₃ : ℝ}
    (hr : 0 < r) (hrT : r ≤ T)
    (hα_nonneg : 0 ≤ α) (hβ_nonneg : 0 ≤ β) (ha₃_nonneg : 0 ≤ a₃)
    (hy_cont : ContinuousOn y (Icc 0 T))
    (hy_nonneg : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ y t)
    (hderiv : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt y (y' t) t)
    (hderiv_le : ∀ t ∈ Ioo (0 : ℝ) T, y' t ≤ α * y t + β)
    (hint : ∀ t, 0 ≤ t → t + r ≤ T →
      ∫ s in t..t + r, y s ≤ a₃) :
    ∀ t, r ≤ t → t ≤ T →
      y t ≤ (a₃ / r + β * r) * Real.exp (α * r) := by
  sorry

end ShenWork.Analysis.UniformGronwall
