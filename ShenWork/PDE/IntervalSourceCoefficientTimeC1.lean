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
import Mathlib.Analysis.Real.Pi.Bounds

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

/-! ## Stage 3: Addition and scalar multiplication for DuhamelSourceTimeC1

The total PDE source is `−χ₀ · chemotaxisDiv + logisticSource`.  Once
each piece satisfies `DuhamelSourceTimeC1`, the total source inherits it
via addition and scalar multiplication.
-/

/-- **Scalar multiplication preserves `DuhamelSourceTimeC1`.**
`(fun s n => c * a s n)` inherits time-C¹ coefficient structure from `a`. -/
noncomputable def duhamelSourceTimeC1_const_mul
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a) (c : ℝ) :
    DuhamelSourceTimeC1 (fun s n => c * a s n) where
  adot := fun s n => c * src.adot s n
  hderiv := fun s n => (src.hderiv s n).const_mul c
  hadotcont := fun n => continuous_const.mul (src.hadotcont n)
  envelope := fun n => |c| * src.envelope n
  henv_summable := src.henv_summable.mul_left |c|
  henv_bound := fun s hs n => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (src.henv_bound s hs n)
      (abs_nonneg c)
  derivBound := |c| * src.derivBound
  hderivBound := fun s hs n => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (src.hderivBound s hs n)
      (abs_nonneg c)

/-- **Addition preserves `DuhamelSourceTimeC1`.**
`(fun s n => a s n + b s n)` inherits time-C¹ coefficient structure from
`a` and `b` independently. -/
noncomputable def duhamelSourceTimeC1_add
    {a b : ℝ → ℕ → ℝ}
    (ha : DuhamelSourceTimeC1 a) (hb : DuhamelSourceTimeC1 b) :
    DuhamelSourceTimeC1 (fun s n => a s n + b s n) where
  adot := fun s n => ha.adot s n + hb.adot s n
  hderiv := fun s n => (ha.hderiv s n).add (hb.hderiv s n)
  hadotcont := fun n => (ha.hadotcont n).add (hb.hadotcont n)
  envelope := fun n => ha.envelope n + hb.envelope n
  henv_summable := ha.henv_summable.add hb.henv_summable
  henv_bound := fun s hs n =>
    (abs_add_le _ _).trans
      (add_le_add (ha.henv_bound s hs n) (hb.henv_bound s hs n))
  derivBound := ha.derivBound + hb.derivBound
  hderivBound := fun s hs n =>
    (abs_add_le _ _).trans
      (add_le_add (ha.hderivBound s hs n) (hb.hderivBound s hs n))

/-- **Negation preserves `DuhamelSourceTimeC1`.**  Corollary of scalar
multiplication with `c = −1`. -/
noncomputable def duhamelSourceTimeC1_neg
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a) :
    DuhamelSourceTimeC1 (fun s n => -a s n) := by
  have : (fun s n => -a s n) = fun s n => (-1 : ℝ) * a s n := by
    ext s n; ring
  rw [this]
  exact duhamelSourceTimeC1_const_mul src (-1)

/-- **Subtraction preserves `DuhamelSourceTimeC1`.**  Combines negation
and addition. -/
noncomputable def duhamelSourceTimeC1_sub
    {a b : ℝ → ℕ → ℝ}
    (ha : DuhamelSourceTimeC1 a) (hb : DuhamelSourceTimeC1 b) :
    DuhamelSourceTimeC1 (fun s n => a s n - b s n) := by
  have : (fun s n => a s n - b s n) = fun s n => a s n + (-1 : ℝ) * b s n := by
    ext s n; ring
  rw [this]
  exact duhamelSourceTimeC1_add ha (duhamelSourceTimeC1_const_mul hb (-1))

/-! ## G4: Spectral Duhamel ODE and time differentiation of cosine series

The **spectral Duhamel ODE** says that the Duhamel spectral coefficient
`bₙ(t) = ∫₀ᵗ e^{−(t−s)λₙ} aₙ(s) ds` satisfies
`HasDerivAt bₙ (aₙ(t) − λₙ · bₙ(t)) t`.

Combined with term-by-term differentiation for the cosine series, this gives
the **PDE from the mild equation**: `∂ₜu = Δu + source`.
-/

open ShenWork.IntervalDuhamelClosedC2
  (duhamelSpectralCoeff duhamelSpectralCoeff_eigenvalue_summable)

/-- **Spectral Duhamel ODE.**  If the source coefficient `s ↦ a s n` is
continuous (implied by `DuhamelSourceTimeC1`), then the spectral Duhamel
coefficient `bₙ(t) = ∫₀ᵗ e^{−(t−s)λₙ} aₙ(s) ds` satisfies
`d/dt bₙ(t) = aₙ(t) − λₙ · bₙ(t)`.

Proof: factor `bₙ(t) = e^{−tλ} · ∫₀ᵗ e^{sλ} aₙ(s) ds`, then apply the
product rule and FTC. -/
theorem duhamelSpectralCoeff_hasDerivAt
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a)
    (t : ℝ) (n : ℕ) :
    HasDerivAt (fun r => duhamelSpectralCoeff a r n)
      (a t n - unitIntervalCosineEigenvalue n *
        duhamelSpectralCoeff a t n) t := by
  set lam := unitIntervalCosineEigenvalue n
  have hcont_an : Continuous (fun s => a s n) :=
    continuous_iff_continuousAt.2 (fun s => (src.hderiv s n).continuousAt)
  -- Factor: b(r) = e^{-rλ} · G(r) where G(r) = ∫₀ʳ e^{sλ} a(s,n) ds.
  set G : ℝ → ℝ := fun r =>
    ∫ s in (0 : ℝ)..r, Real.exp (s * lam) * a s n
  have hfactor : ∀ r, duhamelSpectralCoeff a r n =
      Real.exp (-r * lam) * G r := by
    intro r; show (∫ s in (0:ℝ)..r, _) = _
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun s _ => by
      rw [show -(r - s) * lam = -r * lam + s * lam from by ring,
        Real.exp_add, mul_assoc])
  -- HasDerivAt of e^{-rλ} at r = t.
  have hd_exp : HasDerivAt (fun r => Real.exp (-r * lam))
      (-lam * Real.exp (-t * lam)) t := by
    have h1 : HasDerivAt (fun r : ℝ => -r * lam) (-1 * lam) t := by
      exact (hasDerivAt_id t).neg.mul_const lam
    have h2 := h1.exp
    simp only [neg_mul, one_mul] at h2 ⊢
    convert h2 using 1; ring
  -- HasDerivAt of G at r = t (FTC).
  have hG_cont : Continuous (fun s => Real.exp (s * lam) * a s n) := by
    exact (Real.continuous_exp.comp (continuous_id.mul continuous_const)).mul
      hcont_an
  have hd_G : HasDerivAt G (Real.exp (t * lam) * a t n) t :=
    intervalIntegral.integral_hasDerivAt_right
      (hG_cont.intervalIntegrable 0 t)
      hG_cont.aestronglyMeasurable.stronglyMeasurableAtFilter
      hG_cont.continuousAt
  -- Product rule + simplification: e^{-tλ} * e^{tλ} = 1.
  have hexp_cancel : Real.exp (-t * lam) * Real.exp (t * lam) = 1 := by
    rw [← Real.exp_add, show -t * lam + t * lam = 0 from by ring,
      Real.exp_zero]
  have hderiv_val :
      -lam * Real.exp (-t * lam) * G t +
        Real.exp (-t * lam) * (Real.exp (t * lam) * a t n) =
      a t n - lam * (Real.exp (-t * lam) * G t) := by
    rw [← mul_assoc (Real.exp _), hexp_cancel, one_mul]; ring
  have hprod : HasDerivAt (fun r => Real.exp (-r * lam) * G r)
      (a t n - lam * (Real.exp (-t * lam) * G t)) t :=
    (hd_exp.mul hd_G).congr_deriv hderiv_val
  -- Rewrite to duhamelSpectralCoeff form.
  rw [show (fun r => duhamelSpectralCoeff a r n) =
      (fun r => Real.exp (-r * lam) * G r) from funext hfactor,
    hfactor t]
  exact hprod

/-- **Continuity of the spectral Duhamel derivative.**  The derivative
`t ↦ a(t,n) − λₙ · bₙ(t)` is continuous in `t`.  This follows from
continuity of the source coefficient (from `DuhamelSourceTimeC1`) and
continuity of `bₙ` (itself continuous as an integral of a continuous
integrand with moving upper limit). -/
theorem duhamelSpectralCoeff_deriv_continuous
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a) (n : ℕ) :
    Continuous (fun t =>
      a t n - unitIntervalCosineEigenvalue n *
        duhamelSpectralCoeff a t n) := by
  have hcont_an : Continuous (fun s => a s n) :=
    continuous_iff_continuousAt.2
      (fun s => (src.hderiv s n).continuousAt)
  have hcont_b : Continuous (fun t => duhamelSpectralCoeff a t n) :=
    continuous_iff_continuousAt.2
      (fun t => (duhamelSpectralCoeff_hasDerivAt src t n).continuousAt)
  exact hcont_an.sub (continuous_const.mul hcont_b)

/-- **Summability of spectral Duhamel derivative coefficients.**
`∑ₙ |a(t,n) − λₙ bₙ(t)| < ∞` for `t > 0`, from the ℓ¹ envelope of
`DuhamelSourceTimeC1` and the eigenvalue-weighted summability of the
Duhamel coefficients. -/
theorem duhamelSpectralCoeff_deriv_abs_summable
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a) {t : ℝ} (ht : 0 < t) :
    Summable (fun n => |a t n - unitIntervalCosineEigenvalue n *
      duhamelSpectralCoeff a t n|) := by
  have heig := duhamelSpectralCoeff_eigenvalue_summable src ht
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _)
    (fun n => ?_) (src.henv_summable.add heig)
  have henv : |a t n| ≤ src.envelope n := src.henv_bound t ht.le n
  have hlam_nn : (0 : ℝ) ≤ unitIntervalCosineEigenvalue n := by
    unfold unitIntervalCosineEigenvalue; positivity
  calc |a t n - unitIntervalCosineEigenvalue n *
        duhamelSpectralCoeff a t n|
      ≤ |a t n| + |unitIntervalCosineEigenvalue n *
          duhamelSpectralCoeff a t n| := by
        calc |a t n - _| = |a t n + (-_)| := by rw [sub_eq_add_neg]
          _ ≤ |a t n| + |-_| := abs_add_le _ _
          _ = _ := by rw [abs_neg]
    _ ≤ src.envelope n + unitIntervalCosineEigenvalue n *
          |duhamelSpectralCoeff a t n| := by
        rw [abs_mul, abs_of_nonneg hlam_nn]
        linarith

/-- **IBP simplification: the spectral derivative equals exponential + integral.**
From `duhamelCoeff_eigenvalue_mul`, the derivative `a(t,n) − λₙ bₙ(t)` equals
`e^{−tλₙ} a(0,n) + ∫₀ᵗ e^{−(t−s)λₙ} adot(s,n) ds`. -/
theorem duhamelSpectralCoeff_deriv_eq_ibp
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a)
    (t : ℝ) (n : ℕ) :
    a t n - unitIntervalCosineEigenvalue n *
      duhamelSpectralCoeff a t n =
    Real.exp (-t * unitIntervalCosineEigenvalue n) * a 0 n +
      ∫ s in (0:ℝ)..t,
        Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) *
          src.adot s n := by
  have hIBP := ShenWork.IntervalDuhamelClosedC2.duhamelCoeff_eigenvalue_mul
    (lam := unitIntervalCosineEigenvalue n)
    (fun s => src.hderiv s n) (src.hadotcont n) (t := t)
  simp only [duhamelSpectralCoeff] at hIBP ⊢
  linarith

/-- **Uniform bound on the exponential piece.**  `|e^{−tλ} a(0,n)| ≤ envelope(n)`
for `t ≥ 0`, `λ ≥ 0`, from `e^{−tλ} ≤ 1` and `|a(0,n)| ≤ envelope(n)`. -/
theorem duhamelSpectralCoeff_exp_piece_bound
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a)
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    |Real.exp (-t * unitIntervalCosineEigenvalue n) * a 0 n| ≤
      src.envelope n := by
  rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
  have hlam_nn : 0 ≤ unitIntervalCosineEigenvalue n := by
    unfold unitIntervalCosineEigenvalue; positivity
  have henv_nn : 0 ≤ src.envelope n :=
    le_trans (abs_nonneg _) (src.henv_bound 0 le_rfl n)
  calc Real.exp (-t * unitIntervalCosineEigenvalue n) * |a 0 n|
      ≤ 1 * src.envelope n := by
        apply mul_le_mul _ (src.henv_bound 0 le_rfl n)
          (abs_nonneg _) (by linarith)
        exact Real.exp_le_one_iff.2 (by nlinarith)
    _ = src.envelope n := one_mul _

/-- **Uniform bound on spectral derivative for bounded time.**
For `0 ≤ t ≤ T`, `|a(t,n) − λₙ bₙ(t)| ≤ envelope(n) + derivBound · T`.
Uses the IBP decomposition and `e^{−x} ≤ 1`. -/
theorem duhamelSpectralCoeff_deriv_bounded_time
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a)
    {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) (n : ℕ) :
    |a t n - unitIntervalCosineEigenvalue n *
      duhamelSpectralCoeff a t n| ≤
      src.envelope n + |src.derivBound| * T := by
  rw [duhamelSpectralCoeff_deriv_eq_ibp src t n]
  have hlam_nn : (0 : ℝ) ≤ unitIntervalCosineEigenvalue n := by
    unfold unitIntervalCosineEigenvalue; positivity
  have hdb_nn : 0 ≤ |src.derivBound| := abs_nonneg _
  -- Bound exponential piece.
  have h1 := duhamelSpectralCoeff_exp_piece_bound src ht n
  -- Bound integral piece: each integrand ≤ derivBound, integrate over [0,t] ⊂ [0,T].
  have h2 : |∫ s in (0:ℝ)..t,
      Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) *
        src.adot s n| ≤ |src.derivBound| * T := by
    have hii : IntervalIntegrable
        (fun s => Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) *
          src.adot s n) MeasureTheory.volume 0 t := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.mul
      · exact (Real.continuous_exp.comp (by fun_prop)).continuousOn
      · exact (src.hadotcont n).continuousOn
    have hpt : ∀ s, s ∈ Set.Icc (0 : ℝ) t →
        |Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) *
          src.adot s n| ≤ |src.derivBound| := by
      intro s hs
      rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
      calc _ ≤ 1 * |src.adot s n| := by
            apply mul_le_mul_of_nonneg_right
              (Real.exp_le_one_iff.2 (by nlinarith [hs.1, hs.2]))
              (abs_nonneg _)
        _ = |src.adot s n| := one_mul _
        _ ≤ |src.derivBound| :=
            (src.hderivBound s (by linarith [hs.1]) n).trans
              (le_abs_self _)
    calc |∫ s in (0:ℝ)..t, _|
        ≤ ∫ s in (0:ℝ)..t, |Real.exp (-(t - s) *
            unitIntervalCosineEigenvalue n) * src.adot s n| :=
          intervalIntegral.abs_integral_le_integral_abs ht
      _ ≤ ∫ _s in (0:ℝ)..t, |src.derivBound| := by
          exact intervalIntegral.integral_mono_on ht hii.abs
            (continuous_const.intervalIntegrable 0 t) hpt
      _ = |src.derivBound| * t := by
          rw [intervalIntegral.integral_const, smul_eq_mul]; ring
      _ ≤ |src.derivBound| * T :=
          mul_le_mul_of_nonneg_left htT hdb_nn
  linarith [abs_add_le
    (Real.exp (-t * unitIntervalCosineEigenvalue n) * a 0 n)
    (∫ s in (0:ℝ)..t,
      Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * src.adot s n)]

/-- **Parabolic gain bound on the integral piece.**  For `t ≥ 0`,
`|∫₀ᵗ e^{−(t−s)λ} adot(s,n) ds| ≤ |derivBound| · (1/n²)`.

Uses `|adot| ≤ derivBound` and the parabolic gain `λ ∫₀ᵗ e^{-(t-s)λ} ≤ 1`,
giving `∫₀ᵗ e^{-(t-s)λ} ≤ 1/λ_n = 1/(nπ)² ≤ 1/n²` for `n ≥ 1`.
For `n = 0` (λ₀ = 0): the integrand is `adot(s,0)`, but
`reciprocalSquareTerm 0 = 1/0 = 0`, and the integral is bounded by
`derivBound · t`, so we need a different bound. We use the fact that for
`λ = 0`, the integral `∫₀ᵗ adot = ∑ coefficient differences` is bounded
by `2 · envelope(0)` from the IBP identity (since the derivative series
telescopes). -/
theorem duhamelSpectralCoeff_integral_piece_bound
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a)
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    |∫ s in (0:ℝ)..t,
        Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) *
          src.adot s n| ≤
      src.derivBound *
        ∫ s in (0:ℝ)..t,
          Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) := by
  have hlam_nn : (0 : ℝ) ≤ unitIntervalCosineEigenvalue n := by
    unfold unitIntervalCosineEigenvalue; positivity
  have hdb_nn : 0 ≤ src.derivBound :=
    le_trans (abs_nonneg _) (src.hderivBound 0 le_rfl 0)
  calc |∫ s in (0:ℝ)..t, Real.exp (-(t - s) *
        unitIntervalCosineEigenvalue n) * src.adot s n|
      ≤ ∫ s in (0:ℝ)..t, |Real.exp (-(t - s) *
          unitIntervalCosineEigenvalue n) * src.adot s n| :=
        intervalIntegral.abs_integral_le_integral_abs ht
    _ ≤ ∫ s in (0:ℝ)..t, src.derivBound *
          Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) := by
        apply intervalIntegral.integral_mono_on ht
        · apply ContinuousOn.intervalIntegrable
          exact ((Real.continuous_exp.comp (by fun_prop :
            Continuous (fun s => -(t - s) * unitIntervalCosineEigenvalue n))).mul
            (src.hadotcont n)).continuousOn.abs
        · apply ContinuousOn.intervalIntegrable
          exact (continuous_const.mul (Real.continuous_exp.comp
            (by fun_prop : Continuous (fun s =>
              -(t - s) * unitIntervalCosineEigenvalue n)))).continuousOn
        · intro s hs
          rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _), mul_comm]
          exact mul_le_mul_of_nonneg_right
            (src.hderivBound s (by linarith [hs.1]) n) (Real.exp_nonneg _)
    _ = src.derivBound * ∫ s in (0:ℝ)..t,
          Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) := by
        rw [← intervalIntegral.integral_const_mul]

open ShenWork.IntervalDomainRegularityBootstrap
  (reciprocalSquareTerm reciprocalSquareTerm_summable) in
/-- **Summable uniform-in-time bound on the spectral derivative.**
For all `t ≥ 0` and all `n`,
`|a(t,n) − λₙ bₙ(t)| ≤ envelope(n) + derivBound · (1/n²)`.

For `n = 0` (λ₀ = 0): the derivative is just `a(t,0)` bounded by
`envelope(0)`; `reciprocalSquareTerm 0 = 0` so the bound is tight.
For `n ≥ 1`: the IBP decomposition + `parabolicGain_le_one` gives
`|integral piece| ≤ derivBound / λₙ ≤ derivBound / n²`. -/
theorem duhamelSpectralCoeff_deriv_summable_uniform_bound
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a)
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    |a t n - unitIntervalCosineEigenvalue n *
      duhamelSpectralCoeff a t n| ≤
      src.envelope n + src.derivBound * reciprocalSquareTerm n := by
  have hdb_nn : 0 ≤ src.derivBound :=
    le_trans (abs_nonneg _) (src.hderivBound 0 le_rfl 0)
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · -- n = 0: λ₀ = 0, so the derivative is just a(t,0).
    subst hn0
    have : unitIntervalCosineEigenvalue 0 = 0 := by
      simp [unitIntervalCosineEigenvalue]
    have : reciprocalSquareTerm 0 = 0 := by
      simp [reciprocalSquareTerm]
    simp only [this, mul_zero, add_zero, ‹unitIntervalCosineEigenvalue 0 = 0›,
      zero_mul, sub_zero]
    exact src.henv_bound t ht 0
  · -- n ≥ 1: use IBP decomposition + parabolic gain.
    rw [duhamelSpectralCoeff_deriv_eq_ibp src t n]
    have hlam_nn : (0 : ℝ) ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue; positivity
    have hlam_pos : 0 < unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue
      have : (0 : ℝ) < n := Nat.cast_pos.2 hn
      positivity
    have h1 := duhamelSpectralCoeff_exp_piece_bound src ht n
    have h2 := duhamelSpectralCoeff_integral_piece_bound src ht n
    have hgain := ShenWork.IntervalDuhamelRegularity.parabolicGain_le_one
      hlam_nn ht
    -- From parabolic gain: λ · ∫ ≤ 1 and λ > 0 gives ∫ ≤ 1/λ.
    have hint_le_inv : ∫ s in (0:ℝ)..t,
        Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) ≤
        1 / unitIntervalCosineEigenvalue n := by
      rw [le_div_iff₀ hlam_pos]; linarith
    -- 1/λ_n = 1/(nπ)² ≤ 1/n² since π ≥ 1.
    have hinv_le_recip :
        1 / unitIntervalCosineEigenvalue n ≤ reciprocalSquareTerm n := by
      rw [reciprocalSquareTerm, unitIntervalCosineEigenvalue]
      apply div_le_div_of_nonneg_left (by linarith) (by positivity)
      calc ((n : ℝ) * Real.pi) ^ 2
          = (n : ℝ) ^ 2 * Real.pi ^ 2 := by ring
        _ ≥ (n : ℝ) ^ 2 * 1 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            nlinarith [Real.pi_gt_three]
        _ = (n : ℝ) ^ 2 := mul_one _
    -- Combine: derivBound · ∫ ≤ derivBound · 1/n².
    have hint_bound : src.derivBound *
        ∫ s in (0:ℝ)..t,
          Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) ≤
        src.derivBound * reciprocalSquareTerm n :=
      mul_le_mul_of_nonneg_left (hint_le_inv.trans hinv_le_recip) hdb_nn
    linarith [abs_add_le
      (Real.exp (-t * unitIntervalCosineEigenvalue n) * a 0 n)
      (∫ s in (0:ℝ)..t,
        Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) *
          src.adot s n)]

open ShenWork.CosineSpectrum (cosineMode) in
open ShenWork.IntervalDuhamelClosedC2
  (cosineCoeff_summable_of_eigenvalue_summable) in
open ShenWork.IntervalDomainRegularityBootstrap
  (reciprocalSquareTerm reciprocalSquareTerm_summable) in
/-- **G4g: Term-by-term time differentiation of the Duhamel cosine series.**

For fixed `x` and any `t₀ > 0`, the cosine series
`t ↦ ∑' n, bₙ(t) · cos(nπx)` has time derivative
`∑' n, (aₙ(t₀) − λₙ bₙ(t₀)) · cos(nπx)`.

Uses `hasDerivAt_tsum_of_isPreconnected` on `(0,∞)` with the summable
uniform bound `envelope(n) + derivBound/n²` from G4f. -/
theorem duhamelSpectralCosineSeries_hasDerivAt_time
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a)
    {t₀ : ℝ} (ht₀ : 0 < t₀) (x : ℝ) :
    HasDerivAt
      (fun t => ∑' n, duhamelSpectralCoeff a t n * cosineMode n x)
      (∑' n, (a t₀ n - unitIntervalCosineEigenvalue n *
        duhamelSpectralCoeff a t₀ n) * cosineMode n x) t₀ := by
  have hcos_le : ∀ n, |cosineMode n x| ≤ 1 := fun n => by
    simp only [cosineMode]; exact Real.abs_cos_le_one _
  -- Summable uniform bound.
  set u : ℕ → ℝ := fun n =>
    src.envelope n + src.derivBound * reciprocalSquareTerm n
  have henv_nn : ∀ n, 0 ≤ src.envelope n := fun n =>
    le_trans (abs_nonneg _) (src.henv_bound 0 le_rfl n)
  have hdb_nn : 0 ≤ src.derivBound :=
    le_trans (abs_nonneg _) (src.hderivBound 0 le_rfl 0)
  have hu : Summable u := src.henv_summable.add
    (reciprocalSquareTerm_summable.mul_left src.derivBound)
  have hu_nn : ∀ n, 0 ≤ u n := fun n => add_nonneg (henv_nn n)
    (mul_nonneg hdb_nn (by unfold reciprocalSquareTerm; positivity))
  -- Per-mode HasDerivAt.
  have hg : ∀ n (t : ℝ), t ∈ Set.Ioi (0 : ℝ) → HasDerivAt
      (fun t => duhamelSpectralCoeff a t n * cosineMode n x)
      ((a t n - unitIntervalCosineEigenvalue n *
        duhamelSpectralCoeff a t n) * cosineMode n x) t :=
    fun n t _ => (duhamelSpectralCoeff_hasDerivAt src t n).mul_const _
  -- Derivative norm bound.
  have hg' : ∀ n (t : ℝ), t ∈ Set.Ioi (0 : ℝ) →
      ‖(a t n - unitIntervalCosineEigenvalue n *
        duhamelSpectralCoeff a t n) * cosineMode n x‖ ≤ u n := by
    intro n t ht
    rw [Real.norm_eq_abs, abs_mul]
    calc _ ≤ u n * 1 := mul_le_mul
          (duhamelSpectralCoeff_deriv_summable_uniform_bound src
            (le_of_lt ht) n)
          (hcos_le n) (abs_nonneg _) (hu_nn n)
      _ = u n := mul_one _
  -- Pointwise summability.
  have hg0 : Summable (fun n =>
      duhamelSpectralCoeff a t₀ n * cosineMode n x) := by
    have ⟨_, habs⟩ := cosineCoeff_summable_of_eigenvalue_summable
      (duhamelSpectralCoeff_eigenvalue_summable src ht₀)
    apply Summable.of_norm
    refine habs.of_nonneg_of_le (fun _ => abs_nonneg _) (fun n => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (hcos_le n)
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioi
    isPreconnected_Ioi hg hg' (Set.mem_Ioi.2 ht₀) hg0
    (Set.mem_Ioi.2 ht₀)

/-- `∑ₙ λₙ e^{−τλₙ} < ∞` for `τ > 0`.  Comparison with `n² e^{-cn}`. -/
private theorem eigenvalue_mul_exp_summable {τ : ℝ} (hτ : 0 < τ) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        Real.exp (-τ * unitIntervalCosineEigenvalue n)) := by
  have hc : 0 < τ * Real.pi ^ 2 := by positivity
  have hbase := (Real.summable_pow_mul_exp_neg_nat_mul 2 hc).mul_left
    (Real.pi ^ 2)
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (by unfold unitIntervalCosineEigenvalue; positivity)
      (Real.exp_nonneg _)) (fun n => ?_) hbase
  simp only [unitIntervalCosineEigenvalue]
  calc ((n : ℝ) * Real.pi) ^ 2 *
        Real.exp (-τ * ((n : ℝ) * Real.pi) ^ 2)
      = (n : ℝ) ^ 2 * Real.pi ^ 2 *
          Real.exp (-(τ * Real.pi ^ 2) * (n : ℝ) ^ 2) := by ring_nf
    _ ≤ (n : ℝ) ^ 2 * Real.pi ^ 2 *
          Real.exp (-(τ * Real.pi ^ 2) * (n : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.exp_le_exp_of_le
        have : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
          rcases Nat.eq_zero_or_pos n with h | h
          · simp [h]
          · exact le_self_pow₀ (Nat.one_le_cast.2 h) (by norm_num)
        nlinarith
    _ = Real.pi ^ 2 * ((n : ℝ) ^ 2 *
          Real.exp (-(τ * Real.pi ^ 2) * (n : ℝ))) := by ring

open ShenWork.CosineSpectrum (cosineMode) in
/-- **G4h: Time derivative of the homogeneous cosine-heat series.**
For bounded `a₀` and `t₀ > 0`, `t ↦ ∑' n, e^{−tλₙ} a₀ₙ cos(nπx)` has
time derivative `∑' n, (−λₙ e^{−t₀λₙ}) a₀ₙ cos(nπx)` at `t₀`. -/
theorem homogeneousCosineSeries_hasDerivAt_time
    {a₀ : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M) (ha₀ : ∀ n, |a₀ n| ≤ M)
    {t₀ : ℝ} (ht₀ : 0 < t₀) (x : ℝ) :
    HasDerivAt
      (fun t => ∑' n, Real.exp (-t * unitIntervalCosineEigenvalue n) *
        a₀ n * cosineMode n x)
      (∑' n, -(unitIntervalCosineEigenvalue n *
        Real.exp (-t₀ * unitIntervalCosineEigenvalue n)) *
          a₀ n * cosineMode n x) t₀ := by
  have hcos_le : ∀ n, |cosineMode n x| ≤ 1 := fun n => by
    simp only [cosineMode]; exact Real.abs_cos_le_one _
  have ht₀2 : 0 < t₀ / 2 := by linarith
  set u : ℕ → ℝ := fun n =>
    unitIntervalCosineEigenvalue n *
      Real.exp (-(t₀ / 2) * unitIntervalCosineEigenvalue n) * M
  have hu : Summable u := (eigenvalue_mul_exp_summable ht₀2).mul_right _
  have hu_nn : ∀ n, 0 ≤ u n := fun n =>
    mul_nonneg (mul_nonneg (by unfold unitIntervalCosineEigenvalue; positivity)
      (Real.exp_nonneg _)) hM
  -- Per-mode HasDerivAt.
  have hg : ∀ n (t : ℝ), t ∈ Set.Ioi (t₀ / 2) → HasDerivAt
      (fun t => Real.exp (-t * unitIntervalCosineEigenvalue n) *
        a₀ n * cosineMode n x)
      (-(unitIntervalCosineEigenvalue n *
        Real.exp (-t * unitIntervalCosineEigenvalue n)) *
          a₀ n * cosineMode n x) t := by
    intro n t _
    set lam := unitIntervalCosineEigenvalue n
    rw [show (fun t => Real.exp (-t * lam) * a₀ n * cosineMode n x) =
        (fun t => Real.exp (-t * lam) * (a₀ n * cosineMode n x))
        from funext (fun _ => by ring)]
    have harg : HasDerivAt (fun r : ℝ => -r * lam) (-lam) t := by
      simpa using (hasDerivAt_id t).neg.mul_const lam
    exact (harg.exp.mul_const _).congr_deriv (by ring)
  -- Derivative bound on (t₀/2, ∞).
  have hg' : ∀ n (t : ℝ), t ∈ Set.Ioi (t₀ / 2) →
      ‖-(unitIntervalCosineEigenvalue n *
        Real.exp (-t * unitIntervalCosineEigenvalue n)) *
          a₀ n * cosineMode n x‖ ≤ u n := by
    intro n t ht
    have ht2 : t₀ / 2 ≤ t := le_of_lt (Set.mem_Ioi.1 ht)
    have hlam_nn : (0 : ℝ) ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue; positivity
    rw [Real.norm_eq_abs]
    set lam := unitIntervalCosineEigenvalue n
    set e := Real.exp (-t * lam)
    have he_nn : 0 ≤ e := Real.exp_nonneg _
    -- Unfold: |-(lam*e) * a₀ n * cos| = lam * e * |a₀ n| * |cos|
    have habs_eq :
        |-(lam * e) * a₀ n * cosineMode n x| =
          lam * e * |a₀ n| * |cosineMode n x| := by
      rw [show -(lam * e) * a₀ n * cosineMode n x =
          -(lam * e * a₀ n * cosineMode n x) from by ring,
        abs_neg, abs_mul, abs_mul, abs_mul,
        abs_of_nonneg hlam_nn, abs_of_nonneg he_nn]
    rw [habs_eq]
    -- Step 1: lam * e * |a₀ n| * |cos| ≤ lam * e * M (using |a₀ n| ≤ M, |cos| ≤ 1)
    have hstep1 : lam * e * |a₀ n| * |cosineMode n x| ≤ lam * e * M :=
      calc lam * e * |a₀ n| * |cosineMode n x|
          ≤ lam * e * M * 1 :=
            mul_le_mul
              (mul_le_mul_of_nonneg_left (ha₀ n) (mul_nonneg hlam_nn he_nn))
              (hcos_le n) (abs_nonneg _)
              (mul_nonneg (mul_nonneg hlam_nn he_nn) hM)
        _ = lam * e * M := mul_one _
    -- Step 2: e = exp(-t*lam) ≤ exp(-(t₀/2)*lam) since t ≥ t₀/2
    calc lam * e * |a₀ n| * |cosineMode n x|
        ≤ lam * e * M := hstep1
      _ ≤ lam * Real.exp (-(t₀ / 2) * lam) * M := by
          apply mul_le_mul_of_nonneg_right _ hM
          exact mul_le_mul_of_nonneg_left
            (Real.exp_le_exp_of_le (by nlinarith)) hlam_nn
      _ = u n := rfl
  -- Pointwise summability at t₀.
  -- Majorant: exp(-t₀*lam) * M, summable by unitIntervalCosineHeatTrace_single_exp_summable.
  have hg0 : Summable (fun n =>
      Real.exp (-t₀ * unitIntervalCosineEigenvalue n) *
        a₀ n * cosineMode n x) := by
    refine Summable.of_norm_bounded
      (g := fun n => Real.exp (-t₀ * unitIntervalCosineEigenvalue n) * M)
      ((ShenWork.HeatKernelGradientEstimates.unitIntervalCosineHeatTrace_single_exp_summable
        ht₀).mul_right M)
      (fun n => ?_)
    rw [Real.norm_eq_abs,
      show Real.exp (-t₀ * unitIntervalCosineEigenvalue n) * a₀ n * cosineMode n x =
        Real.exp (-t₀ * unitIntervalCosineEigenvalue n) *
          (a₀ n * cosineMode n x) from by ring,
      abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
    exact mul_le_mul_of_nonneg_left
      (by rw [abs_mul];
          calc |a₀ n| * |cosineMode n x|
              ≤ M * 1 := mul_le_mul (ha₀ n) (hcos_le n) (abs_nonneg _) hM
            _ = M := mul_one _)
      (Real.exp_nonneg _)
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioi
    isPreconnected_Ioi hg hg' (Set.mem_Ioi.2 (by linarith : t₀ / 2 < t₀))
    hg0 (Set.mem_Ioi.2 (by linarith : t₀ / 2 < t₀))

section RestartSeries
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalDuhamelClosedC2
  (cosineCoeff_summable_of_eigenvalue_summable)
open ShenWork.IntervalDomainRegularityBootstrap
  (reciprocalSquareTerm reciprocalSquareTerm_summable)

/-- The restart coefficient: `e^{−τλₙ} a₀ₙ + bₙ(τ)`. -/
noncomputable def localRestartCoeff
    (a₀ : ℕ → ℝ) (a : ℝ → ℕ → ℝ) (τ : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n +
    duhamelSpectralCoeff a τ n

/-- **G4i: Time derivative of the full restart cosine series.**
For the restart coefficient `cₙ(τ) = e^{−τλₙ} a₀ₙ + bₙ(τ)`, the series
`τ ↦ ∑' n, cₙ(τ) cos(nπx)` has time derivative
`∑' n, (aₙ(τ₀) − λₙ cₙ(τ₀)) cos(nπx)` at every `τ₀ > 0`.

This is the **spectral PDE identity**: since `Δu = −∑ λₙ cₙ cos` and
`source = ∑ aₙ cos`, the derivative equals `source + Δu`, i.e., `∂ₜu = Δu + f`. -/
theorem restartCosineSeries_hasDerivAt_time
    {a₀ : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M) (ha₀ : ∀ n, |a₀ n| ≤ M)
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a)
    {τ₀ : ℝ} (hτ₀ : 0 < τ₀) (x : ℝ) :
    HasDerivAt
      (fun τ => ∑' n, localRestartCoeff a₀ a τ n * cosineMode n x)
      (∑' n, (a τ₀ n - unitIntervalCosineEigenvalue n *
        localRestartCoeff a₀ a τ₀ n) * cosineMode n x) τ₀ := by
  have hcos_le : ∀ n, |cosineMode n x| ≤ 1 := fun n => by
    simp only [cosineMode]; exact Real.abs_cos_le_one _
  have ht₀2 : 0 < τ₀ / 2 := by linarith
  -- Helper: summability of homogeneous term at any τ > 0
  have hsum_hom_at : ∀ τ : ℝ, 0 < τ → Summable (fun n =>
      Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n * cosineMode n x) := by
    intro τ hτ
    refine Summable.of_norm_bounded
      (g := fun n => Real.exp (-τ * unitIntervalCosineEigenvalue n) * M)
      ((ShenWork.HeatKernelGradientEstimates.unitIntervalCosineHeatTrace_single_exp_summable
        hτ).mul_right M) (fun n => ?_)
    rw [Real.norm_eq_abs,
      show Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n * cosineMode n x =
        Real.exp (-τ * unitIntervalCosineEigenvalue n) *
          (a₀ n * cosineMode n x) from by ring,
      abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
    exact mul_le_mul_of_nonneg_left
      (by rw [abs_mul];
          calc |a₀ n| * |cosineMode n x|
              ≤ M * 1 := mul_le_mul (ha₀ n) (hcos_le n) (abs_nonneg _) hM
            _ = M := mul_one _)
      (Real.exp_nonneg _)
  -- Helper: summability of Duhamel term at any τ > 0
  have hsum_duh_at : ∀ τ : ℝ, 0 < τ → Summable (fun n =>
      duhamelSpectralCoeff a τ n * cosineMode n x) := by
    intro τ hτ
    have ⟨_, habs⟩ := cosineCoeff_summable_of_eigenvalue_summable
      (duhamelSpectralCoeff_eigenvalue_summable src hτ)
    exact Summable.of_norm (habs.of_nonneg_of_le (fun _ => abs_nonneg _) (fun n => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (hcos_le n)))
  -- The localRestartCoeff series splits into homogeneous + Duhamel at every τ > 0.
  have hfun_eq : ∀ τ ∈ Set.Ioi (0 : ℝ),
      ∑' n, localRestartCoeff a₀ a τ n * cosineMode n x =
      (∑' n, Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n * cosineMode n x) +
        (∑' n, duhamelSpectralCoeff a τ n * cosineMode n x) := by
    intro τ hτ
    have hτ' : 0 < τ := Set.mem_Ioi.1 hτ
    rw [show (fun n => localRestartCoeff a₀ a τ n * cosineMode n x) =
        fun n => Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n * cosineMode n x +
          duhamelSpectralCoeff a τ n * cosineMode n x from funext (fun n => by
            simp only [localRestartCoeff]; ring)]
    exact (hsum_hom_at τ hτ').tsum_add (hsum_duh_at τ hτ')
  -- HasDerivAt of each piece.
  have hd1 := homogeneousCosineSeries_hasDerivAt_time hM ha₀ hτ₀ x
  have hd2 := duhamelSpectralCosineSeries_hasDerivAt_time src hτ₀ x
  -- Combine via HasDerivAt.add + congr_of_eventuallyEq.
  have hcombine := hd1.add hd2
  -- hcombine : HasDerivAt (fun τ => ∑' hom + ∑' duh) (d1 + d2) τ₀
  -- We need HasDerivAt (fun τ => ∑' restart) (∑' a - λ·restart) τ₀
  -- Step 1: change the function via eventuallyEq on Ioi 0.
  have hfun_ev : (fun τ => ∑' n, localRestartCoeff a₀ a τ n * cosineMode n x) =ᶠ[𝓝 τ₀]
      (fun τ => ∑' n, Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n * cosineMode n x +
        ∑' n, duhamelSpectralCoeff a τ n * cosineMode n x) := by
    apply Filter.eventuallyEq_of_mem (s := Set.Ioi 0)
    · exact Ioi_mem_nhds hτ₀
    · intro τ hτ; exact hfun_eq τ hτ
  have hstep1 : HasDerivAt
      (fun τ => ∑' n, localRestartCoeff a₀ a τ n * cosineMode n x)
      (∑' n, -(unitIntervalCosineEigenvalue n *
        Real.exp (-τ₀ * unitIntervalCosineEigenvalue n)) *
          a₀ n * cosineMode n x +
        ∑' n, (a τ₀ n - unitIntervalCosineEigenvalue n *
          duhamelSpectralCoeff a τ₀ n) * cosineMode n x) τ₀ :=
    hcombine.congr_of_eventuallyEq hfun_ev
  -- Step 2: simplify the derivative value using tsum_add + tsum_congr.
  -- Summability of hsum1 and hsum2 for tsum_add.
  have hsum1 : Summable (fun n =>
      -(unitIntervalCosineEigenvalue n *
        Real.exp (-τ₀ * unitIntervalCosineEigenvalue n)) *
          a₀ n * cosineMode n x) := by
    apply Summable.of_norm
    refine ((eigenvalue_mul_exp_summable ht₀2).mul_right M).of_nonneg_of_le
      (fun _ => norm_nonneg _) (fun n => ?_)
    have hlam_nn : (0 : ℝ) ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue; positivity
    rw [Real.norm_eq_abs, show -(unitIntervalCosineEigenvalue n *
        Real.exp (-τ₀ * unitIntervalCosineEigenvalue n)) * a₀ n * cosineMode n x =
        -(unitIntervalCosineEigenvalue n *
          Real.exp (-τ₀ * unitIntervalCosineEigenvalue n) * a₀ n * cosineMode n x) from by ring,
      abs_neg, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg hlam_nn, abs_of_nonneg (Real.exp_nonneg _)]
    have hexp_mono : Real.exp (-τ₀ * unitIntervalCosineEigenvalue n) ≤
        Real.exp (-(τ₀ / 2) * unitIntervalCosineEigenvalue n) :=
      Real.exp_le_exp_of_le (by nlinarith)
    calc unitIntervalCosineEigenvalue n *
          Real.exp (-τ₀ * unitIntervalCosineEigenvalue n) *
            |a₀ n| * |cosineMode n x|
        ≤ unitIntervalCosineEigenvalue n *
            Real.exp (-(τ₀ / 2) * unitIntervalCosineEigenvalue n) * M * 1 := by
          apply mul_le_mul (mul_le_mul ?_ (ha₀ n) (abs_nonneg _) (by positivity))
            (hcos_le n) (abs_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left hexp_mono hlam_nn
      _ = unitIntervalCosineEigenvalue n *
            Real.exp (-(τ₀ / 2) * unitIntervalCosineEigenvalue n) * M := mul_one _
  have hsum2 : Summable (fun n =>
      (a τ₀ n - unitIntervalCosineEigenvalue n *
        duhamelSpectralCoeff a τ₀ n) * cosineMode n x) := by
    apply Summable.of_norm
    exact (duhamelSpectralCoeff_deriv_abs_summable src hτ₀).of_nonneg_of_le
      (fun _ => norm_nonneg _) (fun n => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (hcos_le n))
  -- Rewrite derivative sum using tsum_add + tsum_congr (localRestartCoeff = hom + duh).
  rw [show (∑' n, (a τ₀ n - unitIntervalCosineEigenvalue n *
        localRestartCoeff a₀ a τ₀ n) * cosineMode n x) =
      ∑' n, -(unitIntervalCosineEigenvalue n *
        Real.exp (-τ₀ * unitIntervalCosineEigenvalue n)) *
          a₀ n * cosineMode n x +
      ∑' n, (a τ₀ n - unitIntervalCosineEigenvalue n *
        duhamelSpectralCoeff a τ₀ n) * cosineMode n x from by
      rw [← hsum1.tsum_add hsum2]
      congr 1; ext n; simp only [localRestartCoeff]; ring]
  exact hstep1

/-- **G4j: Time differentiability of the restart cosine series.**
Corollary of `restartCosineSeries_hasDerivAt_time`. -/
theorem restartCosineSeries_differentiableAt_time
    {a₀ : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M) (ha₀ : ∀ n, |a₀ n| ≤ M)
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a)
    {τ₀ : ℝ} (hτ₀ : 0 < τ₀) (x : ℝ) :
    DifferentiableAt ℝ
      (fun τ => ∑' n, localRestartCoeff a₀ a τ n *
        cosineMode n x) τ₀ :=
  (restartCosineSeries_hasDerivAt_time hM ha₀ src hτ₀ x).differentiableAt

/-- **G4j': Continuity of the Duhamel derivative tsum on `(0,∞)`.**
`τ ↦ ∑' n, (aₙ(τ) − λₙ bₙ(τ)) cos(nπx)` is continuous on `(0,∞)` from
the summable majorant `envelope(n) + derivBound/n²`. -/
theorem duhamelSpectralDerivSeries_continuousOn
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a) (x : ℝ) :
    ContinuousOn
      (fun τ => ∑' n, (a τ n -
        unitIntervalCosineEigenvalue n *
          duhamelSpectralCoeff a τ n) * cosineMode n x)
      (Set.Ioi (0 : ℝ)) := by
  exact continuousOn_tsum
    (fun n => ((duhamelSpectralCoeff_deriv_continuous src n).mul
      continuous_const).continuousOn)
    (src.henv_summable.add
      (reciprocalSquareTerm_summable.mul_left src.derivBound))
    (fun n τ hτ => by
      rw [Real.norm_eq_abs, abs_mul]
      have h1 := duhamelSpectralCoeff_deriv_summable_uniform_bound src
        (le_of_lt (Set.mem_Ioi.1 hτ)) n
      have h2 : |cosineMode n x| ≤ 1 := by
        unfold cosineMode; exact Real.abs_cos_le_one _
      have hnn : 0 ≤ src.envelope n + src.derivBound *
          reciprocalSquareTerm n :=
        add_nonneg (le_trans (abs_nonneg _) (src.henv_bound 0 le_rfl n))
          (mul_nonneg (le_trans (abs_nonneg _) (src.hderivBound 0 le_rfl 0))
            (by unfold reciprocalSquareTerm; positivity))
      calc _ ≤ _ * 1 := mul_le_mul h1 h2 (abs_nonneg _) hnn
        _ = _ := mul_one _)

end RestartSeries

end ShenWork.IntervalSourceCoefficientTimeC1
