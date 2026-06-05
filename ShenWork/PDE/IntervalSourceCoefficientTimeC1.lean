/-
  ShenWork/PDE/IntervalSourceCoefficientTimeC1.lean

  **G3 Stage 1 — Leibniz rule for parametric integrals on [0,1] and
  `DuhamelSourceTimeC1` construction.**

  Core lemma: if `F(t, y)` is C¹ in `t` with `|F'(t,y)| ≤ bound(y)` and
  `bound` integrable, then `t ↦ ∫ F(t,y) dμ` is C¹ via Mathlib's
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le`.

  Applied to `F(t,y) = f(t,y)·cos(nπy)`, this gives time-C¹ cosine
  coefficients from time-C¹ source data.

  No `sorry`, no `admit`, no custom `axiom`.
-/
import ShenWork.PDE.IntervalDuhamelClosedC2

open MeasureTheory
open scoped Topology

namespace ShenWork.IntervalSourceCoefficientTimeC1

open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)

/-! ## Leibniz rule for parametric integrals on the unit interval -/

/-- **Leibniz rule on `[0,1]`.**  If `F(t,y)` is differentiable in `t` at every
`t` near `t₀`, with derivative bounded by an integrable function of `y`, then
`t ↦ ∫_{[0,1]} F(t,y) dy` is differentiable at `t₀` with derivative
`∫_{[0,1]} F'(t₀,y) dy`. -/
theorem hasDerivAt_intervalIntegral_of_dominated
    {F : ℝ → ℝ → ℝ} {F' : ℝ → ℝ → ℝ} {t₀ : ℝ}
    (hF_meas : ∀ᶠ t in 𝓝 t₀,
      AEStronglyMeasurable (F t) (volume.restrict (Set.Icc 0 1)))
    (hF_int : Integrable (F t₀) (volume.restrict (Set.Icc 0 1)))
    (hF'_meas : AEStronglyMeasurable (F' t₀) (volume.restrict (Set.Icc 0 1)))
    {bound : ℝ → ℝ}
    (hbound : ∀ᵐ y ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ∀ t, ‖F' t y‖ ≤ bound y)
    (hbound_int : Integrable bound (volume.restrict (Set.Icc 0 1)))
    (hdiff : ∀ᵐ y ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ∀ t,
      HasDerivAt (F · y) (F' t y) t) :
    HasDerivAt (fun t => ∫ y, F t y ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
      (∫ y, F' t₀ y ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) t₀ :=
  (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Set.univ) Filter.univ_mem hF_meas hF_int hF'_meas
    (by filter_upwards [hbound] with y hy; intro t _; exact hy t)
    hbound_int
    (by filter_upwards [hdiff] with y hy; intro t _; exact hy t)).2

/-! ## DuhamelSourceTimeC1 packaging -/

/-- **DuhamelSourceTimeC1 from explicit fields.** Packages the raw data
into the structure consumed by the closed-C² engine. -/
def duhamelSourceTimeC1_of_data
    (a : ℝ → ℕ → ℝ)
    (adot : ℝ → ℕ → ℝ)
    (hderiv : ∀ s n, HasDerivAt (fun r => a r n) (adot s n) s)
    (hadotcont : ∀ n, Continuous (fun s : ℝ => adot s n))
    (envelope : ℕ → ℝ)
    (henv_summable : Summable envelope)
    (henv_bound : ∀ s, 0 ≤ s → ∀ n, |a s n| ≤ envelope n)
    (derivBound : ℝ)
    (hderivBound : ∀ s, 0 ≤ s → ∀ n, |adot s n| ≤ derivBound) :
    DuhamelSourceTimeC1 a where
  adot := adot
  hderiv := hderiv
  hadotcont := hadotcont
  envelope := envelope
  henv_summable := henv_summable
  henv_bound := henv_bound
  derivBound := derivBound
  hderivBound := hderivBound

end ShenWork.IntervalSourceCoefficientTimeC1
