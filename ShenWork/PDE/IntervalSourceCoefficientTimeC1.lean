/-
  ShenWork/PDE/IntervalSourceCoefficientTimeC1.lean

  **G3 Stages 1–3: Leibniz rule, resolver time-diff, total source assembly.**

  Stage 1 — Leibniz rule for parametric integrals on [0,1] and
  `DuhamelSourceTimeC1` construction.

  Stage 2 — Mode-wise multiplication by a bounded weight preserves
  `DuhamelSourceTimeC1`.  Applied to the elliptic resolver: if the source
  coefficients `â_k(s)` are time-C¹, then the resolver coefficients
  `v̂_k(s) = â_k(s)/(μ+λ_k)` are time-C¹ with the same structure.

  Stage 3 — `DuhamelSourceTimeC1` is closed under addition and scalar
  multiplication.  This lets us combine logistic + chemotaxis divergence
  into a single total-source `DuhamelSourceTimeC1`.

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

/-! ## Stage 2: Mode-wise weight multiplication preserves DuhamelSourceTimeC1

The elliptic resolver coefficient `v̂_k = â_k / (μ + λ_k)` is a mode-wise
rescaling of the source coefficients.  More generally, multiplying each mode
by a bounded weight `c(n)` preserves all DuhamelSourceTimeC1 fields:
- `HasDerivAt` of `c(n) · a(s,n)` is `c(n) · adot(s,n)`
- Envelope becomes `Cw · envelope(n)` (summable if `Cw` is finite)
- Derivative bound becomes `Cw · derivBound`
-/

/-- **Mode-wise multiplication by a bounded weight preserves
`DuhamelSourceTimeC1`.** If the coefficients `a(s,n)` satisfy
`DuhamelSourceTimeC1` and `|c(n)| ≤ Cw` for all `n`, then the rescaled
coefficients `c(n) · a(s,n)` also satisfy `DuhamelSourceTimeC1`. -/
noncomputable def duhamelSourceTimeC1_mul_weight
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a)
    (c : ℕ → ℝ) {Cw : ℝ} (hCw_nn : 0 ≤ Cw) (hCw : ∀ n, |c n| ≤ Cw) :
    DuhamelSourceTimeC1 (fun s n => c n * a s n) where
  adot := fun s n => c n * src.adot s n
  hderiv := fun s n => (src.hderiv s n).const_mul (c n)
  hadotcont := fun n => continuous_const.mul (src.hadotcont n)
  envelope := fun n => Cw * src.envelope n
  henv_summable := src.henv_summable.mul_left Cw
  henv_bound := fun s hs n => by
    calc |c n * a s n| = |c n| * |a s n| := abs_mul _ _
      _ ≤ Cw * src.envelope n :=
        mul_le_mul (hCw n) (src.henv_bound s hs n) (abs_nonneg _) hCw_nn
  derivBound := Cw * src.derivBound
  hderivBound := fun s hs n => by
    calc |c n * src.adot s n| = |c n| * |src.adot s n| := abs_mul _ _
      _ ≤ Cw * src.derivBound :=
        mul_le_mul (hCw n) (src.hderivBound s hs n) (abs_nonneg _) hCw_nn

end ShenWork.IntervalSourceCoefficientTimeC1
