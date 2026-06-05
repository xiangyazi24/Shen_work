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

end ShenWork.IntervalSourceCoefficientTimeC1
