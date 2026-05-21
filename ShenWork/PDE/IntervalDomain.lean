/-
  ShenWork/PDE/IntervalDomain.lean

  Concrete bounded-domain infrastructure: the interval [0, L].
  This is the first audit-passing bounded-domain file.

  All definitions use Mathlib primitives (volume.restrict, Set.Icc).
  No abstract structure fields. No assumed estimates.
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import ShenWork.PDE.HeatSemigroup

open MeasureTheory Set

noncomputable section

namespace ShenWork.IntervalDomain

def intervalSet (L : ℝ) : Set ℝ := Set.Icc 0 L

def intervalMeasure (L : ℝ) : Measure ℝ :=
  volume.restrict (intervalSet L)

/-- The restricted Lebesgue measure on `[0,L]` is finite. -/
theorem intervalMeasure_univ_lt_top (L : ℝ) :
    intervalMeasure L Set.univ < ⊤ := by
  unfold intervalMeasure intervalSet
  simp [Real.volume_Icc]

instance intervalMeasure_isFiniteMeasure (L : ℝ) :
    IsFiniteMeasure (intervalMeasure L) :=
  ⟨intervalMeasure_univ_lt_top L⟩

/-- A measurable function bounded on the interval is integrable against the
interval measure. -/
theorem intervalMeasure_integrable_of_abs_bound
    {L M : ℝ} {f : ℝ → ℝ}
    (hf_meas : AEStronglyMeasurable f (intervalMeasure L))
    (hf_bound : ∀ y, |f y| ≤ M) :
    Integrable f (intervalMeasure L) := by
  exact Integrable.of_bound hf_meas M
    (Filter.Eventually.of_forall fun y => by
      simpa [Real.norm_eq_abs] using hf_bound y)

def intervalVolume (L : ℝ) : ℝ :=
  (intervalMeasure L Set.univ).toReal

theorem intervalVolume_eq {L : ℝ} (hL : 0 ≤ L) :
    intervalVolume L = L := by
  unfold intervalVolume intervalMeasure intervalSet
  rw [Measure.restrict_apply_univ, Real.volume_Icc]
  simpa using ENNReal.toReal_ofReal hL

theorem intervalVolume_pos {L : ℝ} (hL : 0 < L) :
    0 < intervalVolume L := by
  rw [intervalVolume_eq hL.le]
  exact hL

/-- Constant integration against the concrete interval measure. -/
theorem intervalMeasure_integral_const {L c : ℝ} (hL : 0 ≤ L) :
    ∫ _ : ℝ, c ∂ intervalMeasure L = c * L := by
  rw [MeasureTheory.integral_const]
  have hreal : (intervalMeasure L).real Set.univ = L := by
    unfold intervalMeasure intervalSet
    rw [measureReal_restrict_apply_univ, measureReal_def, Real.volume_Icc]
    simpa using ENNReal.toReal_ofReal hL
  rw [hreal]
  simp [smul_eq_mul, mul_comm]

theorem intervalIntegral_const {L c : ℝ} :
    ∫ _ in (0 : ℝ)..L, c = c * L := by
  rw [intervalIntegral.integral_const]
  simp [smul_eq_mul]
  ring

theorem intervalIntegral_nonneg {L : ℝ} {f : ℝ → ℝ}
    (hL : 0 ≤ L) (hf : ∀ x ∈ Set.Icc 0 L, 0 ≤ f x) :
    0 ≤ ∫ x in (0 : ℝ)..L, f x :=
  intervalIntegral.integral_nonneg hL hf

theorem intervalIntegral_mono {L : ℝ} {f g : ℝ → ℝ}
    (hL : 0 ≤ L) (hfg : ∀ x ∈ Set.Icc 0 L, f x ≤ g x)
    (hf : IntervalIntegrable f volume 0 L)
    (hg : IntervalIntegrable g volume 0 L) :
    ∫ x in (0 : ℝ)..L, f x ≤ ∫ x in (0 : ℝ)..L, g x :=
  intervalIntegral.integral_mono_on hL hf hg hfg

theorem intervalIntegral_add {L : ℝ} {f g : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 L)
    (hg : IntervalIntegrable g volume 0 L) :
    ∫ x in (0 : ℝ)..L, (f x + g x) =
      (∫ x in (0 : ℝ)..L, f x) + ∫ x in (0 : ℝ)..L, g x :=
  intervalIntegral.integral_add hf hg

/-- The identity operator on interval functions preserves mass (trivially). -/
theorem identity_preserves_intervalIntegral {L : ℝ} (f : ℝ → ℝ) :
    ∫ x in (0 : ℝ)..L, (id f) x = ∫ x in (0 : ℝ)..L, f x := by
  rfl

/-- Constant functions are interval-integrable. -/
theorem const_intervalIntegrable {L c : ℝ} :
    IntervalIntegrable (fun _ => c) volume 0 L :=
  intervalIntegrable_const

/-- The average of a function on [0,L]. This is the zeroth Neumann mode. -/
def intervalAverage (L : ℝ) (f : ℝ → ℝ) : ℝ :=
  (1 / L) * ∫ x in (0 : ℝ)..L, f x

/-- The constant-mode projection: maps f to its average on [0,L]. -/
def constantModeProjection (L : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun _ => intervalAverage L f

/-- The constant-mode projection preserves mass. -/
theorem constantModeProjection_preserves_mass {L : ℝ} (hL : 0 < L) (f : ℝ → ℝ) :
    ∫ x in (0 : ℝ)..L, constantModeProjection L f x =
      ∫ x in (0 : ℝ)..L, f x := by
  unfold constantModeProjection intervalAverage
  rw [intervalIntegral_const]
  field_simp [ne_of_gt hL]

/-- The constant-mode projection maps nonneg-average functions to nonneg. -/
theorem constantModeProjection_nonneg {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hf : 0 ≤ ∫ x in (0 : ℝ)..L, f x) :
    ∀ x, 0 ≤ constantModeProjection L f x := by
  intro x
  unfold constantModeProjection intervalAverage
  exact mul_nonneg (div_nonneg one_pos.le hL.le) hf

/-- The average of a constant is itself. -/
theorem intervalAverage_const {L c : ℝ} (hL : 0 < L) :
    intervalAverage L (fun _ => c) = c := by
  unfold intervalAverage
  rw [intervalIntegral_const]
  field_simp [ne_of_gt hL]

/-- A nonnegative function on `[0,L]` has nonnegative interval average. -/
theorem intervalAverage_nonneg {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hf : ∀ x ∈ Set.Icc 0 L, 0 ≤ f x) :
    0 ≤ intervalAverage L f := by
  unfold intervalAverage
  exact mul_nonneg (div_nonneg zero_le_one hL.le)
    (intervalIntegral_nonneg hL.le hf)

/-- Monotonicity of the interval average. -/
theorem intervalAverage_mono {L : ℝ} (hL : 0 < L) {f g : ℝ → ℝ}
    (hf_int : IntervalIntegrable f volume 0 L)
    (hg_int : IntervalIntegrable g volume 0 L)
    (hfg : ∀ x ∈ Set.Icc 0 L, f x ≤ g x) :
    intervalAverage L f ≤ intervalAverage L g := by
  unfold intervalAverage
  exact mul_le_mul_of_nonneg_left
    (intervalIntegral_mono hL.le hfg hf_int hg_int)
    (div_nonneg zero_le_one hL.le)

/-- Addition commutes with the interval average for interval-integrable
inputs. -/
theorem intervalAverage_add {L : ℝ} {f g : ℝ → ℝ}
    (hf_int : IntervalIntegrable f volume 0 L)
    (hg_int : IntervalIntegrable g volume 0 L) :
    intervalAverage L (fun x => f x + g x) =
      intervalAverage L f + intervalAverage L g := by
  unfold intervalAverage
  rw [intervalIntegral.integral_add hf_int hg_int]
  ring

/-- Scalar multiplication commutes with the interval average. -/
theorem intervalAverage_const_mul (a L : ℝ) (f : ℝ → ℝ) :
    intervalAverage L (fun x => a * f x) = a * intervalAverage L f := by
  unfold intervalAverage
  rw [intervalIntegral.integral_const_mul]
  ring

/-- Negation commutes with the interval average. -/
theorem intervalAverage_neg (L : ℝ) (f : ℝ → ℝ) :
    intervalAverage L (fun x => -f x) = -intervalAverage L f := by
  unfold intervalAverage
  rw [intervalIntegral.integral_neg]
  ring

/-- Subtraction commutes with the interval average for interval-integrable
inputs. -/
theorem intervalAverage_sub {L : ℝ} {f g : ℝ → ℝ}
    (hf_int : IntervalIntegrable f volume 0 L)
    (hg_int : IntervalIntegrable g volume 0 L) :
    intervalAverage L (fun x => f x - g x) =
      intervalAverage L f - intervalAverage L g := by
  unfold intervalAverage
  rw [intervalIntegral.integral_sub hf_int hg_int]
  ring

/-- A function bounded above by `M` on `[0,L]` has interval average at most
`M`. -/
theorem intervalAverage_le_of_le {L M : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hf_int : IntervalIntegrable f volume 0 L)
    (hf_le : ∀ x ∈ Set.Icc 0 L, f x ≤ M) :
    intervalAverage L f ≤ M := by
  unfold intervalAverage
  have h_int_le :
      ∫ x in (0 : ℝ)..L, f x ≤ M * L := by
    calc
      ∫ x in (0 : ℝ)..L, f x ≤ ∫ x in (0 : ℝ)..L, M :=
        intervalIntegral_mono hL.le hf_le hf_int intervalIntegrable_const
      _ = M * L := intervalIntegral_const
  calc
    (1 / L) * ∫ x in (0 : ℝ)..L, f x
        ≤ (1 / L) * (M * L) :=
          mul_le_mul_of_nonneg_left h_int_le
            (div_nonneg zero_le_one hL.le)
    _ = M := by field_simp [ne_of_gt hL]

/-- A function bounded between `0` and `M` on `[0,L]` has interval average in
the same interval. -/
theorem intervalAverage_interval_bound {L M : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hf_int : IntervalIntegrable f volume 0 L)
    (hf_nonneg : ∀ x ∈ Set.Icc 0 L, 0 ≤ f x)
    (hf_le : ∀ x ∈ Set.Icc 0 L, f x ≤ M) :
    0 ≤ intervalAverage L f ∧ intervalAverage L f ≤ M :=
  ⟨intervalAverage_nonneg hL hf_nonneg,
    intervalAverage_le_of_le hL hf_int hf_le⟩

/-- If `|f| ≤ M` on `[0,L]`, then the interval average has absolute value at
most `M`. -/
theorem intervalAverage_abs_le {L M : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hf_int : IntervalIntegrable f volume 0 L)
    (hf_bound : ∀ x ∈ Set.Icc 0 L, |f x| ≤ M) :
    |intervalAverage L f| ≤ M := by
  have hupper : intervalAverage L f ≤ M :=
    intervalAverage_le_of_le hL hf_int fun x hx =>
      le_trans (le_abs_self (f x)) (hf_bound x hx)
  have hneg : intervalAverage L (fun x => -f x) ≤ M :=
    intervalAverage_le_of_le hL hf_int.neg fun x hx => by
      exact le_trans (neg_le_abs (f x)) (hf_bound x hx)
  rw [intervalAverage_neg] at hneg
  exact abs_le.mpr ⟨by linarith, hupper⟩

/-- The constant-mode projection fixes constants. -/
theorem constantModeProjection_const {L c : ℝ} (hL : 0 < L) :
    constantModeProjection L (fun _ => c) = fun _ => c := by
  funext x
  simp [constantModeProjection, intervalAverage_const hL]

/-- The constant-mode projection is idempotent. -/
theorem constantModeProjection_idempotent {L : ℝ} (hL : 0 < L) (f : ℝ → ℝ) :
    constantModeProjection L (constantModeProjection L f) =
      constantModeProjection L f := by
  funext x
  change intervalAverage L (fun _ => intervalAverage L f) = intervalAverage L f
  exact intervalAverage_const hL

/-- A nonnegative function on `[0,L]` is sent by the constant-mode projection
to a nonnegative constant function. -/
theorem constantModeProjection_nonneg_of_nonneg {L : ℝ} (hL : 0 < L)
    {f : ℝ → ℝ} (hf : ∀ x ∈ Set.Icc 0 L, 0 ≤ f x) :
    ∀ x, 0 ≤ constantModeProjection L f x := by
  intro x
  exact intervalAverage_nonneg hL hf

/-- Additivity of the constant-mode projection. -/
theorem constantModeProjection_add {L : ℝ} {f g : ℝ → ℝ}
    (hf_int : IntervalIntegrable f volume 0 L)
    (hg_int : IntervalIntegrable g volume 0 L) :
    constantModeProjection L (fun x => f x + g x) =
      fun x => constantModeProjection L f x + constantModeProjection L g x := by
  funext x
  simp [constantModeProjection, intervalAverage_add hf_int hg_int]

/-- Scalar multiplication for the constant-mode projection. -/
theorem constantModeProjection_const_mul (a L : ℝ) (f : ℝ → ℝ) :
    constantModeProjection L (fun x => a * f x) =
      fun x => a * constantModeProjection L f x := by
  funext x
  simp [constantModeProjection, intervalAverage_const_mul]

/-- Negation for the constant-mode projection. -/
theorem constantModeProjection_neg (L : ℝ) (f : ℝ → ℝ) :
    constantModeProjection L (fun x => -f x) =
      fun x => -constantModeProjection L f x := by
  funext x
  simp [constantModeProjection, intervalAverage_neg]

/-- Subtraction for the constant-mode projection. -/
theorem constantModeProjection_sub {L : ℝ} {f g : ℝ → ℝ}
    (hf_int : IntervalIntegrable f volume 0 L)
    (hg_int : IntervalIntegrable g volume 0 L) :
    constantModeProjection L (fun x => f x - g x) =
      fun x => constantModeProjection L f x - constantModeProjection L g x := by
  funext x
  simp [constantModeProjection, intervalAverage_sub hf_int hg_int]

/-- Monotonicity of the constant-mode projection. -/
theorem constantModeProjection_mono {L : ℝ} (hL : 0 < L) {f g : ℝ → ℝ}
    (hf_int : IntervalIntegrable f volume 0 L)
    (hg_int : IntervalIntegrable g volume 0 L)
    (hfg : ∀ x ∈ Set.Icc 0 L, f x ≤ g x) :
    ∀ x, constantModeProjection L f x ≤ constantModeProjection L g x := by
  intro x
  exact intervalAverage_mono hL hf_int hg_int hfg

/-- A function bounded between `0` and `M` on `[0,L]` is sent by the
constant-mode projection to a constant function in the same interval. -/
theorem constantModeProjection_interval_bound {L M : ℝ} (hL : 0 < L)
    {f : ℝ → ℝ}
    (hf_int : IntervalIntegrable f volume 0 L)
    (hf_nonneg : ∀ x ∈ Set.Icc 0 L, 0 ≤ f x)
    (hf_le : ∀ x ∈ Set.Icc 0 L, f x ≤ M) :
    ∀ x, 0 ≤ constantModeProjection L f x ∧
      constantModeProjection L f x ≤ M := by
  intro x
  exact intervalAverage_interval_bound hL hf_int hf_nonneg hf_le

/-- `L∞` contraction of the constant-mode projection. -/
theorem constantModeProjection_contraction {L M : ℝ} (hL : 0 < L)
    {f g : ℝ → ℝ}
    (hf_int : IntervalIntegrable f volume 0 L)
    (hg_int : IntervalIntegrable g volume 0 L)
    (hfg : ∀ x ∈ Set.Icc 0 L, |f x - g x| ≤ M) :
    ∀ x, |constantModeProjection L f x - constantModeProjection L g x| ≤ M := by
  intro x
  change |intervalAverage L f - intervalAverage L g| ≤ M
  rw [← intervalAverage_sub hf_int hg_int]
  exact intervalAverage_abs_le hL (hf_int.sub hg_int) hfg

/-- The residual after subtracting the constant-mode projection has zero
interval mass. -/
theorem constantModeProjection_residual_intervalIntegral_eq_zero
    {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hf_int : IntervalIntegrable f volume 0 L) :
    ∫ x in (0 : ℝ)..L, (f x - constantModeProjection L f x) = 0 := by
  have hproj_int :
      IntervalIntegrable (constantModeProjection L f) volume 0 L := by
    unfold constantModeProjection
    exact intervalIntegrable_const
  rw [intervalIntegral.integral_sub hf_int hproj_int]
  rw [constantModeProjection_preserves_mass hL f]
  ring

/-- The residual after subtracting the constant-mode projection has zero
interval average. -/
theorem constantModeProjection_residual_intervalAverage_eq_zero
    {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hf_int : IntervalIntegrable f volume 0 L) :
    intervalAverage L (fun x => f x - constantModeProjection L f x) = 0 := by
  unfold intervalAverage
  rw [constantModeProjection_residual_intervalIntegral_eq_zero hL hf_int]
  ring

/-- The constant-mode projection of the residual is the zero function. -/
theorem constantModeProjection_residual_eq_zero
    {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hf_int : IntervalIntegrable f volume 0 L) :
    constantModeProjection L (fun x => f x - constantModeProjection L f x) =
      fun _ => 0 := by
  funext x
  change intervalAverage L (fun x => f x - constantModeProjection L f x) = 0
  exact constantModeProjection_residual_intervalAverage_eq_zero hL hf_int

/-- Pointwise decomposition into constant mode plus zero-mean residual. -/
theorem constantModeProjection_add_residual
    (L : ℝ) (f : ℝ → ℝ) :
    (fun x => constantModeProjection L f x +
      (f x - constantModeProjection L f x)) = f := by
  funext x
  ring

/-- The Neumann heat kernel on [0,L] via method of images (reflected kernel).
For t > 0 and x, y ∈ [0,L]:
  K_N(t, x, y) = G(t, x-y) + G(t, x+y) + G(t, 2L-x-y) + ...
where G is the Gaussian. The zeroth-order approximation uses just the
first two terms (direct + one reflection), which already satisfies
Neumann BC at x=0. -/
def neumannHeatKernel_zerothReflection (_L t x y : ℝ) : ℝ :=
  heatKernel t (x - y) + heatKernel t (x + y)

/-- The zeroth-reflection Neumann kernel is nonneg. -/
theorem neumannHeatKernel_zerothReflection_nonneg
    {t : ℝ} (ht : 0 < t) (L x y : ℝ) :
    0 ≤ neumannHeatKernel_zerothReflection L t x y := by
  unfold neumannHeatKernel_zerothReflection
  exact add_nonneg (heatKernel_nonneg ht _) (heatKernel_nonneg ht _)

/-- The zeroth-reflection helper kernel is strictly positive for positive
time. -/
theorem neumannHeatKernel_zerothReflection_pos
    {t : ℝ} (ht : 0 < t) (L x y : ℝ) :
    0 < neumannHeatKernel_zerothReflection L t x y := by
  unfold neumannHeatKernel_zerothReflection
  have hleft : 0 < heatKernel t (x - y) := by
    unfold heatKernel
    have hden : 0 < Real.sqrt (4 * Real.pi * t) := by
      exact Real.sqrt_pos.2 (by positivity)
    exact mul_pos (div_pos zero_lt_one hden) (Real.exp_pos _)
  have hright : 0 < heatKernel t (x + y) := by
    unfold heatKernel
    have hden : 0 < Real.sqrt (4 * Real.pi * t) := by
      exact Real.sqrt_pos.2 (by positivity)
    exact mul_pos (div_pos zero_lt_one hden) (Real.exp_pos _)
  exact add_pos hleft hright

/-- The zeroth-reflection kernel is even in x: K(t, -x, y) = K(t, x, y).
This symmetry implies the Neumann boundary condition ∂K/∂x|_{x=0} = 0. -/
theorem neumannHeatKernel_zerothReflection_even
    (L t x y : ℝ) :
    neumannHeatKernel_zerothReflection L t (-x) y =
      neumannHeatKernel_zerothReflection L t x y := by
  unfold neumannHeatKernel_zerothReflection
  rw [show -x - y = -(x + y) from by ring,
    show -x + y = -(x - y) from by ring,
    heatKernel_neg, heatKernel_neg]
  ring

/-- The zeroth-reflection helper kernel has zero normal derivative at the
left boundary `x = 0`. -/
theorem neumannHeatKernel_zerothReflection_hasDerivAt_zero
    {t : ℝ} (ht : 0 < t) (L y : ℝ) :
    HasDerivAt (fun x : ℝ => neumannHeatKernel_zerothReflection L t x y)
      0 0 := by
  have hleft :
      HasDerivAt (fun x : ℝ => heatKernel t (x - y))
        ((y / (2 * t)) * heatKernel t y) 0 := by
    convert heatKernel_translated_hasDerivAt_left ht 0 y using 1
    rw [show 0 - y = -y by ring, heatKernel_neg]
    ring
  have hright :
      HasDerivAt (fun x : ℝ => heatKernel t (x + y))
        (-(y / (2 * t)) * heatKernel t y) 0 := by
    have hinner : HasDerivAt (fun x : ℝ => x + y) 1 0 := by
      simpa using (hasDerivAt_id 0).add_const y
    have hk :
        HasDerivAt (fun z : ℝ => heatKernel t z)
          (-(y / (2 * t)) * heatKernel t y) (0 + y) := by
      simpa using heatKernel_hasDerivAt ht y
    have h := hk.comp 0 hinner
    convert h using 1
    ring
  have hsum := hleft.add hright
  have hder :
      (y / (2 * t) * heatKernel t y + (-(y / (2 * t)) * heatKernel t y)) =
        0 := by
    ring
  rw [hder] at hsum
  simpa [neumannHeatKernel_zerothReflection] using hsum

/-- ∫ G(t, x+y) dy = 1, by substitution z = x+y. -/
theorem heatKernel_integral_add {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ∫ y, heatKernel t (x + y) = 1 := by
  have h : (fun y : ℝ => heatKernel t (x + y)) =
      (fun y => heatKernel t (y + x)) := by ext y; ring_nf
  rw [h, integral_add_right_eq_self, heatKernel_integral_eq_one ht]

/-- Translation changes the right half-line integral of `G(t,x+y)` to the
tail integral of `G(t,z)` over `(x,∞)`. -/
theorem heatKernel_setIntegral_Ioi_add {t : ℝ} (x : ℝ) :
    ∫ y in Set.Ioi (0 : ℝ), heatKernel t (x + y) =
      ∫ z in Set.Ioi x, heatKernel t z := by
  have hmp : MeasurePreserving (fun y : ℝ => y + x) volume volume :=
    measurePreserving_add_right volume x
  have hemb : MeasurableEmbedding (fun y : ℝ => y + x) :=
    (Homeomorph.addRight x).isClosedEmbedding.measurableEmbedding
  have h := hmp.setIntegral_preimage_emb hemb
    (fun z : ℝ => heatKernel t z) (Set.Ioi x)
  rw [show (fun y : ℝ => y + x) ⁻¹' Set.Ioi x = Set.Ioi (0 : ℝ) by
    ext y
    simp [Set.mem_Ioi]]
    at h
  rw [show (fun y : ℝ => heatKernel t (y + x)) =
      (fun y : ℝ => heatKernel t (x + y)) by
    ext y
    rw [add_comm]]
    at h
  exact h

/-- Reflection and translation change the right half-line integral of
`G(t,x-y)` to the left tail integral of `G(t,z)` over `(-∞,x)`. -/
theorem heatKernel_setIntegral_Ioi_sub_left {t : ℝ} (x : ℝ) :
    ∫ y in Set.Ioi (0 : ℝ), heatKernel t (x - y) =
      ∫ z in Set.Iio x, heatKernel t z := by
  have hmp : MeasurePreserving (fun y : ℝ => x - y) volume volume :=
    volume.measurePreserving_sub_left x
  have hemb : MeasurableEmbedding (fun y : ℝ => x - y) :=
    (MeasurableEquiv.subLeft x).measurableEmbedding
  have h := hmp.setIntegral_preimage_emb hemb
    (fun z : ℝ => heatKernel t z) (Set.Iio x)
  rw [show (fun y : ℝ => x - y) ⁻¹' Set.Iio x = Set.Ioi (0 : ℝ) by
    ext y
    simp]
    at h
  exact h

/-- The reflected kernel integrates to 2 over y:
∫ [G(t,x-y) + G(t,x+y)] dy = 2. -/
theorem neumannHeatKernel_zerothReflection_integral
    {t : ℝ} (ht : 0 < t) (L x : ℝ) :
    ∫ y, neumannHeatKernel_zerothReflection L t x y = 2 := by
  unfold neumannHeatKernel_zerothReflection
  rw [show (fun y => heatKernel t (x - y) + heatKernel t (x + y)) =
      (fun y => heatKernel t (x - y)) + (fun y => heatKernel t (x + y)) from by
    ext y; rfl]
  rw [Pi.add_def, MeasureTheory.integral_add
    (heatKernel_translated_integrable ht x)
    ((heatKernel_integrable ht).comp_add_left x)]
  rw [heatKernel_integral_translated ht x, heatKernel_integral_add ht x]
  norm_num

/-- The two-term reflected kernel has mass `1` on the right half-line.  This
is the exact half-line mass identity for the helper kernel. -/
theorem neumannHeatKernel_zerothReflection_setIntegral_Ioi
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ∫ y in Set.Ioi (0 : ℝ), neumannHeatKernel_zerothReflection 0 t x y = 1 := by
  unfold neumannHeatKernel_zerothReflection
  have hleft_int :
      IntegrableOn (fun y : ℝ => heatKernel t (x - y)) (Set.Ioi 0) volume :=
    (heatKernel_translated_integrable ht x).integrableOn
  have hright_int :
      IntegrableOn (fun y : ℝ => heatKernel t (x + y)) (Set.Ioi 0) volume :=
    ((heatKernel_integrable ht).comp_add_left x).integrableOn
  rw [show
      (fun y : ℝ => heatKernel t (x - y) + heatKernel t (x + y)) =
        (fun y : ℝ => heatKernel t (x - y)) +
          (fun y : ℝ => heatKernel t (x + y)) from by
      ext y
      rfl]
  rw [Pi.add_def, MeasureTheory.integral_add
    (μ := volume.restrict (Set.Ioi 0)) hleft_int hright_int]
  rw [heatKernel_setIntegral_Ioi_sub_left (t := t) x,
    heatKernel_setIntegral_Ioi_add (t := t) x]
  have hsplit :
      (∫ z in Set.Iio x, heatKernel t z) +
          ∫ z in Set.Ioi x, heatKernel t z =
        ∫ z, heatKernel t z := by
    have hcomp :=
      MeasureTheory.integral_add_compl
        (s := Set.Ioi x) measurableSet_Ioi (heatKernel_integrable ht)
    have hIic :
        (∫ z in Set.Iic x, heatKernel t z) =
          ∫ z in Set.Iio x, heatKernel t z :=
      MeasureTheory.integral_Iic_eq_integral_Iio
    rw [show (Set.Ioi x)ᶜ = Set.Iic x by ext z; simp] at hcomp
    rw [hIic] at hcomp
    rw [add_comm] at hcomp
    exact hcomp
  rw [hsplit, heatKernel_integral_eq_one ht]

/-- Candidate half-line reflected-kernel operator: integrate the two-term
reflected kernel against `f` on `(0,∞)`.  No PDE or semigroup property is
claimed here. -/
def halfLineReflectedKernelOperator (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y in Set.Ioi 0, neumannHeatKernel_zerothReflection 0 t x y * f y

/-- The half-line reflected helper operator preserves nonnegativity. -/
theorem halfLineReflectedKernelOperator_nonneg
    {f : ℝ → ℝ} (hf : ∀ y, 0 ≤ f y)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    0 ≤ halfLineReflectedKernelOperator t f x := by
  unfold halfLineReflectedKernelOperator
  exact MeasureTheory.integral_nonneg fun y =>
    mul_nonneg (neumannHeatKernel_zerothReflection_nonneg ht 0 x y) (hf y)

/-- The unnormalized two-term reflected kernel times a bounded input is
integrable on the whole line. -/
theorem neumannHeatKernel_zerothReflection_mul_bounded_integrable
    {f : ℝ → ℝ} {M t : ℝ} (hf : ∀ y, |f y| ≤ M)
    (hf_meas : AEStronglyMeasurable f volume)
    (ht : 0 < t) (x : ℝ) :
    Integrable (fun y => neumannHeatKernel_zerothReflection 0 t x y * f y) := by
  have hkernel :
      Integrable (fun y => neumannHeatKernel_zerothReflection 0 t x y) := by
    unfold neumannHeatKernel_zerothReflection
    exact (heatKernel_translated_integrable ht x).add
      ((heatKernel_integrable ht).comp_add_left x)
  exact hkernel.mul_bdd hf_meas
    (Filter.Eventually.of_forall fun y => by
      simpa [Real.norm_eq_abs] using hf y)

/-- Bounded inputs make the half-line reflected helper integrable on the
half-line. -/
theorem halfLineReflectedKernelOperator_integrableOn
    {f : ℝ → ℝ} {M t : ℝ} (hf : ∀ y, |f y| ≤ M)
    (hf_meas : AEStronglyMeasurable f volume)
    (ht : 0 < t) (x : ℝ) :
    IntegrableOn
      (fun y => neumannHeatKernel_zerothReflection 0 t x y * f y)
      (Set.Ioi 0) volume :=
  (neumannHeatKernel_zerothReflection_mul_bounded_integrable
    hf hf_meas ht x).integrableOn

/-- The half-line reflected helper operator is monotone on bounded inputs. -/
theorem halfLineReflectedKernelOperator_mono_bounded
    {f g : ℝ → ℝ} {Mf Mg t : ℝ}
    (hfg : ∀ y, f y ≤ g y)
    (hf_bound : ∀ y, |f y| ≤ Mf) (hg_bound : ∀ y, |g y| ≤ Mg)
    (hf_meas : AEStronglyMeasurable f volume)
    (hg_meas : AEStronglyMeasurable g volume)
    (ht : 0 < t) :
    ∀ x, halfLineReflectedKernelOperator t f x ≤
      halfLineReflectedKernelOperator t g x := by
  intro x
  unfold halfLineReflectedKernelOperator
  exact MeasureTheory.setIntegral_mono_on
    (halfLineReflectedKernelOperator_integrableOn hf_bound hf_meas ht x)
    (halfLineReflectedKernelOperator_integrableOn hg_bound hg_meas ht x)
    measurableSet_Ioi
    (fun y _hy =>
      mul_le_mul_of_nonneg_left (hfg y)
        (neumannHeatKernel_zerothReflection_nonneg ht 0 x y))

/-- Bounded-input additivity for the half-line reflected helper operator. -/
theorem halfLineReflectedKernelOperator_add_bounded
    {f g : ℝ → ℝ} {Mf Mg t : ℝ}
    (hf_bound : ∀ y, |f y| ≤ Mf) (hg_bound : ∀ y, |g y| ≤ Mg)
    (hf_meas : AEStronglyMeasurable f volume)
    (hg_meas : AEStronglyMeasurable g volume)
    (ht : 0 < t) :
    ∀ x,
      halfLineReflectedKernelOperator t (fun y => f y + g y) x =
        halfLineReflectedKernelOperator t f x +
          halfLineReflectedKernelOperator t g x := by
  intro x
  unfold halfLineReflectedKernelOperator
  simpa [mul_add] using
    MeasureTheory.integral_add
      (μ := volume.restrict (Set.Ioi 0))
      (halfLineReflectedKernelOperator_integrableOn hf_bound hf_meas ht x)
      (halfLineReflectedKernelOperator_integrableOn hg_bound hg_meas ht x)

/-- Additivity for the half-line reflected helper operator under explicit
integrability of the two weighted inputs. -/
theorem halfLineReflectedKernelOperator_add
    {f g : ℝ → ℝ} {t : ℝ} (x : ℝ)
    (hf : IntegrableOn
      (fun y => neumannHeatKernel_zerothReflection 0 t x y * f y)
      (Set.Ioi 0) volume)
    (hg : IntegrableOn
      (fun y => neumannHeatKernel_zerothReflection 0 t x y * g y)
      (Set.Ioi 0) volume) :
    halfLineReflectedKernelOperator t (fun y => f y + g y) x =
      halfLineReflectedKernelOperator t f x +
        halfLineReflectedKernelOperator t g x := by
  unfold halfLineReflectedKernelOperator
  simpa [mul_add] using
    MeasureTheory.integral_add (μ := volume.restrict (Set.Ioi 0)) hf hg

/-- Scalar multiplication for the half-line reflected helper operator. -/
theorem halfLineReflectedKernelOperator_const_mul
    (a : ℝ) (f : ℝ → ℝ) (t x : ℝ) :
    halfLineReflectedKernelOperator t (fun y => a * f y) x =
      a * halfLineReflectedKernelOperator t f x := by
  unfold halfLineReflectedKernelOperator
  rw [show
      (fun y : ℝ => neumannHeatKernel_zerothReflection 0 t x y * (a * f y)) =
        (fun y : ℝ => a *
          (neumannHeatKernel_zerothReflection 0 t x y * f y)) by
      ext y
      ring]
  exact MeasureTheory.integral_const_mul _ _

/-- Bounded-input subtraction for the half-line reflected helper operator. -/
theorem halfLineReflectedKernelOperator_sub_bounded
    {f g : ℝ → ℝ} {Mf Mg t : ℝ}
    (hf_bound : ∀ y, |f y| ≤ Mf) (hg_bound : ∀ y, |g y| ≤ Mg)
    (hf_meas : AEStronglyMeasurable f volume)
    (hg_meas : AEStronglyMeasurable g volume)
    (ht : 0 < t) :
    ∀ x,
      halfLineReflectedKernelOperator t (fun y => f y - g y) x =
        halfLineReflectedKernelOperator t f x -
          halfLineReflectedKernelOperator t g x := by
  intro x
  unfold halfLineReflectedKernelOperator
  simpa [mul_sub] using
    MeasureTheory.integral_sub
      (μ := volume.restrict (Set.Ioi 0))
      (halfLineReflectedKernelOperator_integrableOn hf_bound hf_meas ht x)
      (halfLineReflectedKernelOperator_integrableOn hg_bound hg_meas ht x)

/-- Subtraction for the half-line reflected helper operator under explicit
integrability of the two weighted inputs. -/
theorem halfLineReflectedKernelOperator_sub
    {f g : ℝ → ℝ} {t : ℝ} (x : ℝ)
    (hf : IntegrableOn
      (fun y => neumannHeatKernel_zerothReflection 0 t x y * f y)
      (Set.Ioi 0) volume)
    (hg : IntegrableOn
      (fun y => neumannHeatKernel_zerothReflection 0 t x y * g y)
      (Set.Ioi 0) volume) :
    halfLineReflectedKernelOperator t (fun y => f y - g y) x =
      halfLineReflectedKernelOperator t f x -
        halfLineReflectedKernelOperator t g x := by
  unfold halfLineReflectedKernelOperator
  simpa [mul_sub] using
    MeasureTheory.integral_sub (μ := volume.restrict (Set.Ioi 0)) hf hg

/-- The half-line reflected helper operator sends zero to zero. -/
theorem halfLineReflectedKernelOperator_zero_fun (t x : ℝ) :
    halfLineReflectedKernelOperator t (fun _ => 0) x = 0 := by
  simp [halfLineReflectedKernelOperator]

/-- Negation for the half-line reflected helper operator. -/
theorem halfLineReflectedKernelOperator_neg
    (f : ℝ → ℝ) (t x : ℝ) :
    halfLineReflectedKernelOperator t (fun y => -f y) x =
      -halfLineReflectedKernelOperator t f x := by
  simpa using halfLineReflectedKernelOperator_const_mul (-1) f t x

/-- The half-line reflected helper operator preserves constant inputs. -/
theorem halfLineReflectedKernelOperator_const
    {t : ℝ} (ht : 0 < t) (c x : ℝ) :
    halfLineReflectedKernelOperator t (fun _ => c) x = c := by
  unfold halfLineReflectedKernelOperator
  rw [MeasureTheory.integral_mul_const]
  rw [neumannHeatKernel_zerothReflection_setIntegral_Ioi ht x]
  ring

/-- Lower-bound preservation for the half-line reflected helper operator. -/
theorem halfLineReflectedKernelOperator_lower_bound
    {f : ℝ → ℝ} {a M t : ℝ}
    (ha : ∀ y, a ≤ f y)
    (hf_bound : ∀ y, |f y| ≤ M)
    (hf_meas : AEStronglyMeasurable f volume)
    (ht : 0 < t) (x : ℝ) :
    a ≤ halfLineReflectedKernelOperator t f x := by
  have hmono :=
    halfLineReflectedKernelOperator_mono_bounded
      (f := fun _ : ℝ => a) (g := f) (Mf := |a|) (Mg := M)
      (fun y => ha y) (fun _ => le_rfl) hf_bound
      aestronglyMeasurable_const hf_meas ht x
  simpa [halfLineReflectedKernelOperator_const ht a x] using hmono

/-- Lower-bound preservation for the half-line reflected helper operator under
explicit integrability of the weighted input. -/
theorem halfLineReflectedKernelOperator_lower_bound_of_integrableOn
    {f : ℝ → ℝ} {a t : ℝ}
    (ha : ∀ y, a ≤ f y)
    (x : ℝ)
    (hf_int : IntegrableOn
      (fun y => neumannHeatKernel_zerothReflection 0 t x y * f y)
      (Set.Ioi 0) volume)
    (ht : 0 < t) :
    a ≤ halfLineReflectedKernelOperator t f x := by
  have hconst_int :
      IntegrableOn
        (fun y => neumannHeatKernel_zerothReflection 0 t x y *
          (fun _ : ℝ => a) y)
        (Set.Ioi 0) volume :=
    halfLineReflectedKernelOperator_integrableOn
      (f := fun _ : ℝ => a) (M := |a|)
      (fun _ => le_rfl) aestronglyMeasurable_const ht x
  have hmono :
      halfLineReflectedKernelOperator t (fun _ : ℝ => a) x ≤
        halfLineReflectedKernelOperator t f x := by
    unfold halfLineReflectedKernelOperator
    exact MeasureTheory.setIntegral_mono_on hconst_int hf_int measurableSet_Ioi
      (fun y _hy =>
        mul_le_mul_of_nonneg_left (ha y)
          (neumannHeatKernel_zerothReflection_nonneg ht 0 x y))
  simpa [halfLineReflectedKernelOperator_const ht a x] using hmono

/-- Upper-bound preservation for the half-line reflected helper operator. -/
theorem halfLineReflectedKernelOperator_upper_bound
    {f : ℝ → ℝ} {b M t : ℝ}
    (hb : ∀ y, f y ≤ b)
    (hf_bound : ∀ y, |f y| ≤ M)
    (hf_meas : AEStronglyMeasurable f volume)
    (ht : 0 < t) (x : ℝ) :
    halfLineReflectedKernelOperator t f x ≤ b := by
  have hmono :=
    halfLineReflectedKernelOperator_mono_bounded
      (f := f) (g := fun _ : ℝ => b) (Mf := M) (Mg := |b|)
      (fun y => hb y) hf_bound (fun _ => le_rfl)
      hf_meas aestronglyMeasurable_const ht x
  simpa [halfLineReflectedKernelOperator_const ht b x] using hmono

/-- Upper-bound preservation for the half-line reflected helper operator under
explicit integrability of the weighted input. -/
theorem halfLineReflectedKernelOperator_upper_bound_of_integrableOn
    {f : ℝ → ℝ} {b t : ℝ}
    (hb : ∀ y, f y ≤ b)
    (x : ℝ)
    (hf_int : IntegrableOn
      (fun y => neumannHeatKernel_zerothReflection 0 t x y * f y)
      (Set.Ioi 0) volume)
    (ht : 0 < t) :
    halfLineReflectedKernelOperator t f x ≤ b := by
  have hconst_int :
      IntegrableOn
        (fun y => neumannHeatKernel_zerothReflection 0 t x y *
          (fun _ : ℝ => b) y)
        (Set.Ioi 0) volume :=
    halfLineReflectedKernelOperator_integrableOn
      (f := fun _ : ℝ => b) (M := |b|)
      (fun _ => le_rfl) aestronglyMeasurable_const ht x
  have hmono :
      halfLineReflectedKernelOperator t f x ≤
        halfLineReflectedKernelOperator t (fun _ : ℝ => b) x := by
    unfold halfLineReflectedKernelOperator
    exact MeasureTheory.setIntegral_mono_on hf_int hconst_int measurableSet_Ioi
      (fun y _hy =>
        mul_le_mul_of_nonneg_left (hb y)
          (neumannHeatKernel_zerothReflection_nonneg ht 0 x y))
  simpa [halfLineReflectedKernelOperator_const ht b x] using hmono

/-- Interval-bound preservation for the half-line reflected helper operator. -/
theorem halfLineReflectedKernelOperator_interval_bound
    {f : ℝ → ℝ} {a b M t : ℝ}
    (hlo : ∀ y, a ≤ f y) (hhi : ∀ y, f y ≤ b)
    (hf_bound : ∀ y, |f y| ≤ M)
    (hf_meas : AEStronglyMeasurable f volume)
    (ht : 0 < t) (x : ℝ) :
    a ≤ halfLineReflectedKernelOperator t f x ∧
      halfLineReflectedKernelOperator t f x ≤ b :=
  ⟨halfLineReflectedKernelOperator_lower_bound hlo hf_bound hf_meas ht x,
    halfLineReflectedKernelOperator_upper_bound hhi hf_bound hf_meas ht x⟩

/-- Interval-bound preservation for the half-line reflected helper operator
under explicit integrability of the weighted input. -/
theorem halfLineReflectedKernelOperator_interval_bound_of_integrableOn
    {f : ℝ → ℝ} {a b t : ℝ}
    (hlo : ∀ y, a ≤ f y) (hhi : ∀ y, f y ≤ b)
    (x : ℝ)
    (hf_int : IntegrableOn
      (fun y => neumannHeatKernel_zerothReflection 0 t x y * f y)
      (Set.Ioi 0) volume)
    (ht : 0 < t) :
    a ≤ halfLineReflectedKernelOperator t f x ∧
      halfLineReflectedKernelOperator t f x ≤ b :=
  ⟨halfLineReflectedKernelOperator_lower_bound_of_integrableOn
      hlo x hf_int ht,
    halfLineReflectedKernelOperator_upper_bound_of_integrableOn
      hhi x hf_int ht⟩

/-- L^∞ bound for the reflected full-line kernel integral:
if |f| ≤ M, then |∫ K_N f| ≤ 2M. -/
theorem reflectedKernelIntegral_Linfty_bound
    {f : ℝ → ℝ} {M : ℝ} (hf : ∀ y, |f y| ≤ M)
    {t : ℝ} (ht : 0 < t) (x : ℝ)
    (_hf_meas : AEStronglyMeasurable f volume) :
    |∫ y, neumannHeatKernel_zerothReflection 0 t x y * f y| ≤ 2 * M := by
  unfold neumannHeatKernel_zerothReflection
  have hplus_int : Integrable (fun y : ℝ => heatKernel t (x + y)) :=
    (heatKernel_integrable ht).comp_add_left x
  have hsum_int :
      Integrable (fun y : ℝ => heatKernel t (x - y) + heatKernel t (x + y)) :=
    (heatKernel_translated_integrable ht x).add hplus_int
  have hmajor_int :
      Integrable
        (fun y : ℝ => (heatKernel t (x - y) + heatKernel t (x + y)) * M) :=
    hsum_int.mul_const M
  have hkernel_integral :
      ∫ y, heatKernel t (x - y) + heatKernel t (x + y) = 2 := by
    have := neumannHeatKernel_zerothReflection_integral ht 0 x
    simp only [neumannHeatKernel_zerothReflection] at this
    exact this
  calc |∫ y, (heatKernel t (x - y) + heatKernel t (x + y)) * f y|
      ≤ ∫ y, ‖(heatKernel t (x - y) + heatKernel t (x + y)) * f y‖ := by
        rw [← Real.norm_eq_abs]
        exact MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ y, |(heatKernel t (x - y) + heatKernel t (x + y)) * f y| := by
        simp [Real.norm_eq_abs]
    _ = ∫ y, (heatKernel t (x - y) + heatKernel t (x + y)) * |f y| := by
        congr 1; ext y
        rw [abs_mul, abs_of_nonneg
          (add_nonneg (heatKernel_nonneg ht _) (heatKernel_nonneg ht _))]
    _ ≤ ∫ y, (heatKernel t (x - y) + heatKernel t (x + y)) * M := by
        apply MeasureTheory.integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall fun y =>
            mul_nonneg
              (add_nonneg (heatKernel_nonneg ht _) (heatKernel_nonneg ht _))
              (abs_nonneg _)
        · exact hmajor_int
        · exact Filter.Eventually.of_forall fun y =>
            mul_le_mul_of_nonneg_left (hf y)
              (add_nonneg (heatKernel_nonneg ht _) (heatKernel_nonneg ht _))
    _ = M * ∫ y, (heatKernel t (x - y) + heatKernel t (x + y)) := by
        rw [show (fun y => (heatKernel t (x - y) + heatKernel t (x + y)) * M) =
            (fun y => M * (heatKernel t (x - y) + heatKernel t (x + y))) from by
          ext y; ring]
        exact MeasureTheory.integral_const_mul _ _
    _ = M * 2 := by
        rw [hkernel_integral]
    _ = 2 * M := by ring

/-- A conservative `L∞` bound for the half-line reflected helper operator,
obtained by comparing with the whole-line two-term kernel mass.  The sharp
half-line mass is expected to be `1`; this theorem deliberately uses the
already proved whole-line mass `2`. -/
theorem halfLineReflectedKernelOperator_Linfty_bound_two
    {f : ℝ → ℝ} {M : ℝ} (hf : ∀ y, |f y| ≤ M)
    {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hf_meas : AEStronglyMeasurable f volume) :
    |halfLineReflectedKernelOperator t f x| ≤ 2 * M := by
  let fIoi : ℝ → ℝ := Set.indicator (Set.Ioi 0) f
  have hfIoi_bound : ∀ y, |fIoi y| ≤ M := by
    intro y
    by_cases hy : y ∈ Set.Ioi (0 : ℝ)
    · simp [fIoi, Set.indicator_of_mem hy, hf y]
    · have hM_nonneg : 0 ≤ M := le_trans (abs_nonneg (f y)) (hf y)
      simp [fIoi, hy, hM_nonneg]
  have hfIoi_meas : AEStronglyMeasurable fIoi volume := by
    exact hf_meas.indicator measurableSet_Ioi
  have hbound :=
    reflectedKernelIntegral_Linfty_bound
      (f := fIoi) hfIoi_bound ht x hfIoi_meas
  have hrewrite :
      (∫ y, neumannHeatKernel_zerothReflection 0 t x y * fIoi y) =
        halfLineReflectedKernelOperator t f x := by
    unfold halfLineReflectedKernelOperator fIoi
    rw [show
        (fun y : ℝ =>
          neumannHeatKernel_zerothReflection 0 t x y *
            Set.indicator (Set.Ioi 0) f y) =
          Set.indicator (Set.Ioi 0)
            (fun y : ℝ => neumannHeatKernel_zerothReflection 0 t x y * f y) by
        ext y
        by_cases hy : y ∈ Set.Ioi (0 : ℝ)
        · simp [Set.indicator, hy]
        · simp [Set.indicator, hy]]
    rw [MeasureTheory.integral_indicator measurableSet_Ioi]
  simpa [hrewrite] using hbound

/-- Sharp `L∞` bound for the half-line reflected helper operator, using the
exact half-line kernel mass `1`. -/
theorem halfLineReflectedKernelOperator_Linfty_bound
    {f : ℝ → ℝ} {M : ℝ} (hf : ∀ y, |f y| ≤ M)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    |halfLineReflectedKernelOperator t f x| ≤ M := by
  unfold halfLineReflectedKernelOperator
  have hmajor_int :
      IntegrableOn
        (fun y : ℝ => neumannHeatKernel_zerothReflection 0 t x y * M)
        (Set.Ioi 0) volume := by
    have hM_bound : ∀ y : ℝ, |(fun _ : ℝ => M) y| ≤ M := by
      intro y
      have hM_nonneg : 0 ≤ M := le_trans (abs_nonneg (f y)) (hf y)
      simp [abs_of_nonneg hM_nonneg]
    exact (neumannHeatKernel_zerothReflection_mul_bounded_integrable
      hM_bound aestronglyMeasurable_const ht x).integrableOn
  calc
    |∫ y in Set.Ioi (0 : ℝ),
        neumannHeatKernel_zerothReflection 0 t x y * f y|
        ≤ ∫ y in Set.Ioi (0 : ℝ),
            ‖neumannHeatKernel_zerothReflection 0 t x y * f y‖ := by
          rw [← Real.norm_eq_abs]
          exact MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ y in Set.Ioi (0 : ℝ),
          |neumannHeatKernel_zerothReflection 0 t x y * f y| := by
        simp [Real.norm_eq_abs]
    _ = ∫ y in Set.Ioi (0 : ℝ),
          neumannHeatKernel_zerothReflection 0 t x y * |f y| := by
        congr 1
        ext y
        rw [abs_mul, abs_of_nonneg
          (neumannHeatKernel_zerothReflection_nonneg ht 0 x y)]
    _ ≤ ∫ y in Set.Ioi (0 : ℝ),
          neumannHeatKernel_zerothReflection 0 t x y * M := by
        apply MeasureTheory.integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall fun y =>
            mul_nonneg
              (neumannHeatKernel_zerothReflection_nonneg ht 0 x y)
              (abs_nonneg _)
        · exact hmajor_int
        · exact Filter.Eventually.of_forall fun y =>
            mul_le_mul_of_nonneg_left (hf y)
              (neumannHeatKernel_zerothReflection_nonneg ht 0 x y)
    _ = M * ∫ y in Set.Ioi (0 : ℝ),
          neumannHeatKernel_zerothReflection 0 t x y := by
        rw [show
            (fun y : ℝ => neumannHeatKernel_zerothReflection 0 t x y * M) =
              (fun y : ℝ => M *
                neumannHeatKernel_zerothReflection 0 t x y) from by
            ext y
            ring]
        exact MeasureTheory.integral_const_mul _ _
    _ = M := by
        rw [neumannHeatKernel_zerothReflection_setIntegral_Ioi ht x]
        ring

/-- The half-line reflected helper operator is dominated by the same operator
applied to the pointwise absolute value. -/
theorem halfLineReflectedKernelOperator_abs_le_operator_abs
    {f : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (x : ℝ) :
    |halfLineReflectedKernelOperator t f x| ≤
      halfLineReflectedKernelOperator t (fun y => |f y|) x := by
  unfold halfLineReflectedKernelOperator
  calc
    |∫ y in Set.Ioi (0 : ℝ),
        neumannHeatKernel_zerothReflection 0 t x y * f y|
        ≤ ∫ y in Set.Ioi (0 : ℝ),
            ‖neumannHeatKernel_zerothReflection 0 t x y * f y‖ := by
          rw [← Real.norm_eq_abs]
          exact MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ y in Set.Ioi (0 : ℝ),
          |neumannHeatKernel_zerothReflection 0 t x y * f y| := by
        simp [Real.norm_eq_abs]
    _ = ∫ y in Set.Ioi (0 : ℝ),
          neumannHeatKernel_zerothReflection 0 t x y * |f y| := by
        congr 1
        ext y
        rw [abs_mul, abs_of_nonneg
          (neumannHeatKernel_zerothReflection_nonneg ht 0 x y)]

/-- Domination principle for the half-line reflected helper operator:
if `|f| ≤ g` pointwise, then `|Tf| ≤ Tg`. -/
theorem halfLineReflectedKernelOperator_abs_le_of_abs_le
    {f g : ℝ → ℝ} (hfg : ∀ y, |f y| ≤ g y)
    {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hg_int : IntegrableOn
      (fun y => neumannHeatKernel_zerothReflection 0 t x y * g y)
      (Set.Ioi 0) volume) :
    |halfLineReflectedKernelOperator t f x| ≤
      halfLineReflectedKernelOperator t g x := by
  exact le_trans
    (halfLineReflectedKernelOperator_abs_le_operator_abs ht x)
    (by
      unfold halfLineReflectedKernelOperator
      apply MeasureTheory.integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun y =>
          mul_nonneg
            (neumannHeatKernel_zerothReflection_nonneg ht 0 x y)
            (abs_nonneg (f y))
      · exact hg_int
      · exact Filter.Eventually.of_forall fun y =>
          mul_le_mul_of_nonneg_left (hfg y)
            (neumannHeatKernel_zerothReflection_nonneg ht 0 x y))

/-- Bounded-input domination for the half-line reflected helper operator. -/
theorem halfLineReflectedKernelOperator_abs_le_of_abs_le_bounded
    {f g : ℝ → ℝ} {Mg t : ℝ}
    (hfg : ∀ y, |f y| ≤ g y)
    (hg_bound : ∀ y, |g y| ≤ Mg)
    (hg_meas : AEStronglyMeasurable g volume)
    (ht : 0 < t) :
    ∀ x,
      |halfLineReflectedKernelOperator t f x| ≤
        halfLineReflectedKernelOperator t g x := by
  intro x
  exact halfLineReflectedKernelOperator_abs_le_of_abs_le hfg ht x
    (halfLineReflectedKernelOperator_integrableOn hg_bound hg_meas ht x)

/-- `L∞` contraction for the half-line reflected helper operator. -/
theorem halfLineReflectedKernelOperator_contraction
    {f g : ℝ → ℝ} {M t : ℝ}
    (hfg : ∀ y, |f y - g y| ≤ M)
    (hf_meas : AEStronglyMeasurable f volume)
    (hg_meas : AEStronglyMeasurable g volume)
    {Mf Mg : ℝ} (hf_bound : ∀ y, |f y| ≤ Mf)
    (hg_bound : ∀ y, |g y| ≤ Mg)
    (ht : 0 < t) :
    ∀ x,
      |halfLineReflectedKernelOperator t f x -
        halfLineReflectedKernelOperator t g x| ≤ M := by
  intro x
  have hsub :=
    halfLineReflectedKernelOperator_sub_bounded
      hf_bound hg_bound hf_meas hg_meas ht x
  have hbound :=
    halfLineReflectedKernelOperator_Linfty_bound
      (f := fun y : ℝ => f y - g y) hfg ht x
  simpa [hsub] using hbound

/-- Full-line mass-normalized version of the two-term reflected kernel.  This
is still only a helper kernel, not the interval Neumann heat kernel. -/
def normalizedZerothReflectionKernel (L t x y : ℝ) : ℝ :=
  (1 / 2) * neumannHeatKernel_zerothReflection L t x y

theorem normalizedZerothReflectionKernel_nonneg
    {t : ℝ} (ht : 0 < t) (L x y : ℝ) :
    0 ≤ normalizedZerothReflectionKernel L t x y := by
  unfold normalizedZerothReflectionKernel
  exact mul_nonneg (by norm_num)
    (neumannHeatKernel_zerothReflection_nonneg ht L x y)

/-- The normalized zeroth-reflection helper kernel is strictly positive for
positive time. -/
theorem normalizedZerothReflectionKernel_pos
    {t : ℝ} (ht : 0 < t) (L x y : ℝ) :
    0 < normalizedZerothReflectionKernel L t x y := by
  unfold normalizedZerothReflectionKernel
  exact mul_pos (by norm_num) (neumannHeatKernel_zerothReflection_pos ht L x y)

theorem normalizedZerothReflectionKernel_even
    (L t x y : ℝ) :
    normalizedZerothReflectionKernel L t (-x) y =
      normalizedZerothReflectionKernel L t x y := by
  unfold normalizedZerothReflectionKernel
  rw [neumannHeatKernel_zerothReflection_even]

/-- The normalized zeroth-reflection helper kernel has zero normal derivative
at the left boundary `x = 0`. -/
theorem normalizedZerothReflectionKernel_hasDerivAt_zero
    {t : ℝ} (ht : 0 < t) (L y : ℝ) :
    HasDerivAt (fun x : ℝ => normalizedZerothReflectionKernel L t x y)
      0 0 := by
  unfold normalizedZerothReflectionKernel
  convert
    (neumannHeatKernel_zerothReflection_hasDerivAt_zero ht L y).const_mul
      (1 / 2) using 1
  ring

theorem normalizedZerothReflectionKernel_integral
    {t : ℝ} (ht : 0 < t) (L x : ℝ) :
    ∫ y, normalizedZerothReflectionKernel L t x y = 1 := by
  unfold normalizedZerothReflectionKernel
  rw [MeasureTheory.integral_const_mul]
  rw [neumannHeatKernel_zerothReflection_integral ht L x]
  norm_num

/-- The normalized reflected helper kernel is integrable on the whole line. -/
theorem normalizedZerothReflectionKernel_integrable
    {t : ℝ} (ht : 0 < t) (L x : ℝ) :
    Integrable (fun y => normalizedZerothReflectionKernel L t x y) := by
  unfold normalizedZerothReflectionKernel neumannHeatKernel_zerothReflection
  exact ((heatKernel_translated_integrable ht x).add
    ((heatKernel_integrable ht).comp_add_left x)).const_mul (1 / 2)

/-- The normalized reflected helper kernel times a bounded input is
integrable. -/
theorem normalizedZerothReflectionKernel_mul_bounded_integrable
    {f : ℝ → ℝ} {M t : ℝ} (hf : ∀ y, |f y| ≤ M)
    (hf_meas : AEStronglyMeasurable f volume)
    (ht : 0 < t) (x : ℝ) :
    Integrable (fun y => normalizedZerothReflectionKernel 0 t x y * f y) :=
  (normalizedZerothReflectionKernel_integrable ht 0 x).mul_bdd hf_meas
    (Filter.Eventually.of_forall fun y => by
      simpa [Real.norm_eq_abs] using hf y)

/-- The normalized reflected helper kernel preserves constant inputs on the
whole line.  This is a mass-normalization fact for the helper kernel only, not
a full interval Neumann semigroup statement. -/
theorem normalizedZerothReflectionKernel_const_integral
    {t : ℝ} (ht : 0 < t) (L x c : ℝ) :
    ∫ y, normalizedZerothReflectionKernel L t x y * c = c := by
  rw [MeasureTheory.integral_mul_const]
  rw [normalizedZerothReflectionKernel_integral ht L x]
  ring

/-- The normalized reflected helper kernel is positivity preserving at the
level of its whole-line integral. -/
theorem normalizedReflectedKernelIntegral_nonneg
    {f : ℝ → ℝ} (hf : ∀ y, 0 ≤ f y)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    0 ≤ ∫ y, normalizedZerothReflectionKernel 0 t x y * f y := by
  exact MeasureTheory.integral_nonneg fun y =>
    mul_nonneg (normalizedZerothReflectionKernel_nonneg ht 0 x y) (hf y)

/-- The normalized reflected helper-kernel integral is monotone in its input. -/
theorem normalizedReflectedKernelIntegral_mono
    {f g : ℝ → ℝ} (hfg : ∀ y, f y ≤ g y)
    {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hf_int : Integrable
      (fun y => normalizedZerothReflectionKernel 0 t x y * f y))
    (hg_int : Integrable
      (fun y => normalizedZerothReflectionKernel 0 t x y * g y)) :
    ∫ y, normalizedZerothReflectionKernel 0 t x y * f y ≤
      ∫ y, normalizedZerothReflectionKernel 0 t x y * g y := by
  exact MeasureTheory.integral_mono hf_int hg_int fun y =>
    mul_le_mul_of_nonneg_left (hfg y)
      (normalizedZerothReflectionKernel_nonneg ht 0 x y)

/-- Bounded-input monotonicity for the normalized reflected helper-kernel
integral. -/
theorem normalizedReflectedKernelIntegral_mono_bounded
    {f g : ℝ → ℝ} {Mf Mg t : ℝ}
    (hfg : ∀ y, f y ≤ g y)
    (hf_bound : ∀ y, |f y| ≤ Mf) (hg_bound : ∀ y, |g y| ≤ Mg)
    (hf_meas : AEStronglyMeasurable f volume)
    (hg_meas : AEStronglyMeasurable g volume)
    (ht : 0 < t) :
    ∀ x,
      ∫ y, normalizedZerothReflectionKernel 0 t x y * f y ≤
        ∫ y, normalizedZerothReflectionKernel 0 t x y * g y := by
  intro x
  exact normalizedReflectedKernelIntegral_mono hfg ht x
    (normalizedZerothReflectionKernel_mul_bounded_integrable
      hf_bound hf_meas ht x)
    (normalizedZerothReflectionKernel_mul_bounded_integrable
      hg_bound hg_meas ht x)

/-- Lower-bound preservation for the normalized reflected helper-kernel
integral. -/
theorem normalizedReflectedKernelIntegral_lower_bound
    {f : ℝ → ℝ} {a M t : ℝ}
    (ha : ∀ y, a ≤ f y)
    (hf_bound : ∀ y, |f y| ≤ M)
    (hf_meas : AEStronglyMeasurable f volume)
    (ht : 0 < t) (x : ℝ) :
    a ≤ ∫ y, normalizedZerothReflectionKernel 0 t x y * f y := by
  have hmono :
      ∫ y, normalizedZerothReflectionKernel 0 t x y * (fun _ => a) y ≤
        ∫ y, normalizedZerothReflectionKernel 0 t x y * f y := by
    exact normalizedReflectedKernelIntegral_mono (fun y => ha y) ht x
      ((normalizedZerothReflectionKernel_integrable ht 0 x).mul_const a)
      (normalizedZerothReflectionKernel_mul_bounded_integrable
        hf_bound hf_meas ht x)
  simpa [normalizedZerothReflectionKernel_const_integral ht 0 x a] using hmono

/-- Upper-bound preservation for the normalized reflected helper-kernel
integral. -/
theorem normalizedReflectedKernelIntegral_upper_bound
    {f : ℝ → ℝ} {b M t : ℝ}
    (hb : ∀ y, f y ≤ b)
    (hf_bound : ∀ y, |f y| ≤ M)
    (hf_meas : AEStronglyMeasurable f volume)
    (ht : 0 < t) (x : ℝ) :
    ∫ y, normalizedZerothReflectionKernel 0 t x y * f y ≤ b := by
  have hmono :
      ∫ y, normalizedZerothReflectionKernel 0 t x y * f y ≤
        ∫ y, normalizedZerothReflectionKernel 0 t x y * (fun _ => b) y := by
    exact normalizedReflectedKernelIntegral_mono (fun y => hb y) ht x
      (normalizedZerothReflectionKernel_mul_bounded_integrable
        hf_bound hf_meas ht x)
      ((normalizedZerothReflectionKernel_integrable ht 0 x).mul_const b)
  simpa [normalizedZerothReflectionKernel_const_integral ht 0 x b] using hmono

/-- Interval-bound preservation for the normalized reflected helper-kernel
integral. -/
theorem normalizedReflectedKernelIntegral_interval_bound
    {f : ℝ → ℝ} {a b M t : ℝ}
    (hlo : ∀ y, a ≤ f y) (hhi : ∀ y, f y ≤ b)
    (hf_bound : ∀ y, |f y| ≤ M)
    (hf_meas : AEStronglyMeasurable f volume)
    (ht : 0 < t) (x : ℝ) :
    a ≤ ∫ y, normalizedZerothReflectionKernel 0 t x y * f y ∧
      ∫ y, normalizedZerothReflectionKernel 0 t x y * f y ≤ b :=
  ⟨normalizedReflectedKernelIntegral_lower_bound hlo hf_bound hf_meas ht x,
    normalizedReflectedKernelIntegral_upper_bound hhi hf_bound hf_meas ht x⟩

/-- Additivity of the normalized reflected helper-kernel integral. -/
theorem normalizedReflectedKernelIntegral_add
    {f g : ℝ → ℝ} {t : ℝ} (x : ℝ)
    (hf : Integrable
      (fun y => normalizedZerothReflectionKernel 0 t x y * f y))
    (hg : Integrable
      (fun y => normalizedZerothReflectionKernel 0 t x y * g y)) :
    ∫ y, normalizedZerothReflectionKernel 0 t x y * (f y + g y) =
      (∫ y, normalizedZerothReflectionKernel 0 t x y * f y) +
        ∫ y, normalizedZerothReflectionKernel 0 t x y * g y := by
  simpa [mul_add] using MeasureTheory.integral_add hf hg

/-- Bounded-input additivity of the normalized reflected helper-kernel
integral. -/
theorem normalizedReflectedKernelIntegral_add_bounded
    {f g : ℝ → ℝ} {Mf Mg t : ℝ}
    (hf_bound : ∀ y, |f y| ≤ Mf) (hg_bound : ∀ y, |g y| ≤ Mg)
    (hf_meas : AEStronglyMeasurable f volume)
    (hg_meas : AEStronglyMeasurable g volume)
    (ht : 0 < t) :
    ∀ x,
      ∫ y, normalizedZerothReflectionKernel 0 t x y * (f y + g y) =
        (∫ y, normalizedZerothReflectionKernel 0 t x y * f y) +
          ∫ y, normalizedZerothReflectionKernel 0 t x y * g y := by
  intro x
  exact normalizedReflectedKernelIntegral_add x
    (normalizedZerothReflectionKernel_mul_bounded_integrable
      hf_bound hf_meas ht x)
    (normalizedZerothReflectionKernel_mul_bounded_integrable
      hg_bound hg_meas ht x)

/-- Scalar multiplication for the normalized reflected helper-kernel
integral. -/
theorem normalizedReflectedKernelIntegral_const_mul
    (a : ℝ) (f : ℝ → ℝ) (t x : ℝ) :
    ∫ y, normalizedZerothReflectionKernel 0 t x y * (a * f y) =
      a * ∫ y, normalizedZerothReflectionKernel 0 t x y * f y := by
  rw [show
      (fun y : ℝ => normalizedZerothReflectionKernel 0 t x y * (a * f y)) =
        (fun y : ℝ => a *
          (normalizedZerothReflectionKernel 0 t x y * f y)) by
      ext y
      ring]
  exact MeasureTheory.integral_const_mul _ _

/-- Subtraction for the normalized reflected helper-kernel integral. -/
theorem normalizedReflectedKernelIntegral_sub
    {f g : ℝ → ℝ} {t : ℝ} (x : ℝ)
    (hf : Integrable
      (fun y => normalizedZerothReflectionKernel 0 t x y * f y))
    (hg : Integrable
      (fun y => normalizedZerothReflectionKernel 0 t x y * g y)) :
    ∫ y, normalizedZerothReflectionKernel 0 t x y * (f y - g y) =
      (∫ y, normalizedZerothReflectionKernel 0 t x y * f y) -
        ∫ y, normalizedZerothReflectionKernel 0 t x y * g y := by
  simpa [mul_sub] using MeasureTheory.integral_sub hf hg

/-- Bounded-input subtraction for the normalized reflected helper-kernel
integral. -/
theorem normalizedReflectedKernelIntegral_sub_bounded
    {f g : ℝ → ℝ} {Mf Mg t : ℝ}
    (hf_bound : ∀ y, |f y| ≤ Mf) (hg_bound : ∀ y, |g y| ≤ Mg)
    (hf_meas : AEStronglyMeasurable f volume)
    (hg_meas : AEStronglyMeasurable g volume)
    (ht : 0 < t) :
    ∀ x,
      ∫ y, normalizedZerothReflectionKernel 0 t x y * (f y - g y) =
        (∫ y, normalizedZerothReflectionKernel 0 t x y * f y) -
          ∫ y, normalizedZerothReflectionKernel 0 t x y * g y := by
  intro x
  exact normalizedReflectedKernelIntegral_sub x
    (normalizedZerothReflectionKernel_mul_bounded_integrable
      hf_bound hf_meas ht x)
    (normalizedZerothReflectionKernel_mul_bounded_integrable
      hg_bound hg_meas ht x)

theorem normalizedReflectedKernelIntegral_Linfty_bound
    {f : ℝ → ℝ} {M : ℝ} (hf : ∀ y, |f y| ≤ M)
    {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hf_meas : AEStronglyMeasurable f volume) :
    |∫ y, normalizedZerothReflectionKernel 0 t x y * f y| ≤ M := by
  have hbound :=
    reflectedKernelIntegral_Linfty_bound hf ht x hf_meas
  have hrewrite :
      (∫ y, normalizedZerothReflectionKernel 0 t x y * f y) =
        (1 / 2) *
          ∫ y, neumannHeatKernel_zerothReflection 0 t x y * f y := by
    unfold normalizedZerothReflectionKernel
    rw [show
        (fun y : ℝ =>
          ((1 / 2) * neumannHeatKernel_zerothReflection 0 t x y) * f y) =
        (fun y : ℝ =>
          (1 / 2) * (neumannHeatKernel_zerothReflection 0 t x y * f y)) by
        ext y
        ring]
    exact MeasureTheory.integral_const_mul _ _
  rw [hrewrite, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
  calc
    (1 / 2) * |∫ y, neumannHeatKernel_zerothReflection 0 t x y * f y|
        ≤ (1 / 2) * (2 * M) := by
          exact mul_le_mul_of_nonneg_left hbound (by norm_num)
    _ = M := by ring

/-- The normalized reflected helper-kernel integral is dominated by the
integral of the pointwise absolute value. -/
theorem normalizedReflectedKernelIntegral_abs_le_integral_abs
    {f : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (x : ℝ) :
    |∫ y, normalizedZerothReflectionKernel 0 t x y * f y| ≤
      ∫ y, normalizedZerothReflectionKernel 0 t x y * |f y| := by
  calc
    |∫ y, normalizedZerothReflectionKernel 0 t x y * f y|
        ≤ ∫ y, ‖normalizedZerothReflectionKernel 0 t x y * f y‖ := by
          rw [← Real.norm_eq_abs]
          exact MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ y, |normalizedZerothReflectionKernel 0 t x y * f y| := by
          simp [Real.norm_eq_abs]
    _ = ∫ y, normalizedZerothReflectionKernel 0 t x y * |f y| := by
          congr 1
          ext y
          rw [abs_mul, abs_of_nonneg
            (normalizedZerothReflectionKernel_nonneg ht 0 x y)]

/-- Domination principle for the normalized reflected helper-kernel integral:
if `|f| ≤ g` pointwise, then `|Tf| ≤ Tg`. -/
theorem normalizedReflectedKernelIntegral_abs_le_of_abs_le
    {f g : ℝ → ℝ} (hfg : ∀ y, |f y| ≤ g y)
    {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hg_int : Integrable
      (fun y => normalizedZerothReflectionKernel 0 t x y * g y)) :
    |∫ y, normalizedZerothReflectionKernel 0 t x y * f y| ≤
      ∫ y, normalizedZerothReflectionKernel 0 t x y * g y := by
  exact le_trans
    (normalizedReflectedKernelIntegral_abs_le_integral_abs ht x)
    (by
      apply MeasureTheory.integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun y =>
          mul_nonneg
            (normalizedZerothReflectionKernel_nonneg ht 0 x y)
            (abs_nonneg (f y))
      · exact hg_int
      · exact Filter.Eventually.of_forall fun y =>
          mul_le_mul_of_nonneg_left (hfg y)
            (normalizedZerothReflectionKernel_nonneg ht 0 x y))

/-- Bounded-input domination for the normalized reflected helper-kernel
integral. -/
theorem normalizedReflectedKernelIntegral_abs_le_of_abs_le_bounded
    {f g : ℝ → ℝ} {Mg t : ℝ}
    (hfg : ∀ y, |f y| ≤ g y)
    (hg_bound : ∀ y, |g y| ≤ Mg)
    (hg_meas : AEStronglyMeasurable g volume)
    (ht : 0 < t) :
    ∀ x,
      |∫ y, normalizedZerothReflectionKernel 0 t x y * f y| ≤
        ∫ y, normalizedZerothReflectionKernel 0 t x y * g y := by
  intro x
  exact normalizedReflectedKernelIntegral_abs_le_of_abs_le hfg ht x
    (normalizedZerothReflectionKernel_mul_bounded_integrable
      hg_bound hg_meas ht x)

/-- `L∞` contraction for the normalized reflected helper-kernel integral. -/
theorem normalizedReflectedKernelIntegral_contraction
    {f g : ℝ → ℝ} {M t : ℝ}
    (hfg : ∀ y, |f y - g y| ≤ M)
    (hf_meas : AEStronglyMeasurable f volume)
    (hg_meas : AEStronglyMeasurable g volume)
    {Mf Mg : ℝ} (hf_bound : ∀ y, |f y| ≤ Mf)
    (hg_bound : ∀ y, |g y| ≤ Mg)
    (ht : 0 < t) :
    ∀ x,
      |(∫ y, normalizedZerothReflectionKernel 0 t x y * f y) -
        ∫ y, normalizedZerothReflectionKernel 0 t x y * g y| ≤ M := by
  intro x
  have hf_int :
      Integrable (fun y => normalizedZerothReflectionKernel 0 t x y * f y) :=
    normalizedZerothReflectionKernel_mul_bounded_integrable
      hf_bound hf_meas ht x
  have hg_int :
      Integrable (fun y => normalizedZerothReflectionKernel 0 t x y * g y) :=
    normalizedZerothReflectionKernel_mul_bounded_integrable
      hg_bound hg_meas ht x
  have hsub_meas :
      AEStronglyMeasurable (fun y : ℝ => f y - g y) volume :=
    hf_meas.sub hg_meas
  have hbound :=
    normalizedReflectedKernelIntegral_Linfty_bound
      (f := fun y : ℝ => f y - g y) hfg ht x hsub_meas
  rwa [normalizedReflectedKernelIntegral_sub x hf_int hg_int] at hbound

/-- The heat kernel pointwise bound: G(t,x) ≤ 1/√(4πt). -/
theorem heatKernel_pointwise_bound {t : ℝ} (ht : 0 < t) (x : ℝ) :
    heatKernel t x ≤ 1 / Real.sqrt (4 * Real.pi * t) := by
  unfold heatKernel
  exact mul_le_of_le_one_right
    (div_nonneg one_pos.le (Real.sqrt_nonneg _))
    (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (sq_nonneg x)) (by linarith)))

/-- Pointwise bound for the unnormalized two-term reflected kernel. -/
theorem neumannHeatKernel_zerothReflection_pointwise_bound
    {t : ℝ} (ht : 0 < t) (L x y : ℝ) :
    neumannHeatKernel_zerothReflection L t x y ≤
      2 / Real.sqrt (4 * Real.pi * t) := by
  unfold neumannHeatKernel_zerothReflection
  calc heatKernel t (x - y) + heatKernel t (x + y)
      ≤ 1 / Real.sqrt (4 * Real.pi * t) +
          1 / Real.sqrt (4 * Real.pi * t) :=
        add_le_add (heatKernel_pointwise_bound ht _)
          (heatKernel_pointwise_bound ht _)
    _ = 2 / Real.sqrt (4 * Real.pi * t) := by ring

/-- The unnormalized two-term reflected kernel times an `L¹` half-line input
is integrable on the half-line. -/
theorem neumannHeatKernel_zerothReflection_mul_integrableOn_of_integrableOn
    {f : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hf_int : IntegrableOn f (Set.Ioi 0) volume) :
    IntegrableOn
      (fun y => neumannHeatKernel_zerothReflection 0 t x y * f y)
      (Set.Ioi 0) volume := by
  have hkernel :
      Integrable (fun y => neumannHeatKernel_zerothReflection 0 t x y) := by
    unfold neumannHeatKernel_zerothReflection
    exact (heatKernel_translated_integrable ht x).add
      ((heatKernel_integrable ht).comp_add_left x)
  have hkernel_meas :
      AEStronglyMeasurable
        (fun y : ℝ => neumannHeatKernel_zerothReflection 0 t x y)
        (volume.restrict (Set.Ioi 0)) :=
    hkernel.aestronglyMeasurable.restrict
  have hkernel_bound :
      ∀ y : ℝ, ‖neumannHeatKernel_zerothReflection 0 t x y‖ ≤
        2 / Real.sqrt (4 * Real.pi * t) := by
    intro y
    rw [Real.norm_eq_abs,
      abs_of_nonneg (neumannHeatKernel_zerothReflection_nonneg ht 0 x y)]
    exact neumannHeatKernel_zerothReflection_pointwise_bound ht 0 x y
  simpa [mul_comm] using
    hf_int.mul_bdd hkernel_meas
      (Filter.Eventually.of_forall hkernel_bound)

/-- `L¹ → L∞` smoothing for the half-line reflected helper operator. -/
theorem halfLineReflectedKernelOperator_L1_Linfty_smoothing
    {f : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hf_int : IntegrableOn f (Set.Ioi 0) volume) :
    ‖halfLineReflectedKernelOperator t f x‖ ≤
      (2 / Real.sqrt (4 * Real.pi * t)) *
        ∫ y in Set.Ioi (0 : ℝ), ‖f y‖ := by
  unfold halfLineReflectedKernelOperator
  calc ‖∫ y in Set.Ioi (0 : ℝ),
        neumannHeatKernel_zerothReflection 0 t x y * f y‖
      ≤ ∫ y in Set.Ioi (0 : ℝ),
          ‖neumannHeatKernel_zerothReflection 0 t x y * f y‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ y in Set.Ioi (0 : ℝ),
          (2 / Real.sqrt (4 * Real.pi * t)) * ‖f y‖ := by
        apply MeasureTheory.integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall fun y => norm_nonneg _
        · exact hf_int.norm.const_mul (2 / Real.sqrt (4 * Real.pi * t))
        · exact Filter.Eventually.of_forall fun y => by
            change ‖neumannHeatKernel_zerothReflection 0 t x y * f y‖ ≤
              (2 / Real.sqrt (4 * Real.pi * t)) * ‖f y‖
            rw [norm_mul, Real.norm_eq_abs,
              abs_of_nonneg
                (neumannHeatKernel_zerothReflection_nonneg ht 0 x y)]
            exact mul_le_mul_of_nonneg_right
              (neumannHeatKernel_zerothReflection_pointwise_bound ht 0 x y)
              (norm_nonneg _)
    _ = (2 / Real.sqrt (4 * Real.pi * t)) *
        ∫ y in Set.Ioi (0 : ℝ), ‖f y‖ :=
        MeasureTheory.integral_const_mul _ _

/-- Absolute-value form of the half-line reflected helper operator
`L¹ → L∞` smoothing estimate. -/
theorem halfLineReflectedKernelOperator_L1_Linfty_smoothing_abs
    {f : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hf_int : IntegrableOn f (Set.Ioi 0) volume) :
    |halfLineReflectedKernelOperator t f x| ≤
      (2 / Real.sqrt (4 * Real.pi * t)) *
        ∫ y in Set.Ioi (0 : ℝ), |f y| := by
  simpa [Real.norm_eq_abs] using
    halfLineReflectedKernelOperator_L1_Linfty_smoothing ht x hf_int

/-- `L¹ → L∞` smoothing for differences of the half-line reflected helper
operator. -/
theorem halfLineReflectedKernelOperator_diff_L1_Linfty_smoothing
    {f g : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hf_int : IntegrableOn f (Set.Ioi 0) volume)
    (hg_int : IntegrableOn g (Set.Ioi 0) volume) :
    ‖halfLineReflectedKernelOperator t f x -
        halfLineReflectedKernelOperator t g x‖ ≤
      (2 / Real.sqrt (4 * Real.pi * t)) *
        ∫ y in Set.Ioi (0 : ℝ), ‖f y - g y‖ := by
  have hf_kernel :
      IntegrableOn
        (fun y => neumannHeatKernel_zerothReflection 0 t x y * f y)
        (Set.Ioi 0) volume :=
    neumannHeatKernel_zerothReflection_mul_integrableOn_of_integrableOn
      ht x hf_int
  have hg_kernel :
      IntegrableOn
        (fun y => neumannHeatKernel_zerothReflection 0 t x y * g y)
        (Set.Ioi 0) volume :=
    neumannHeatKernel_zerothReflection_mul_integrableOn_of_integrableOn
      ht x hg_int
  have hdiff_int :
      IntegrableOn (fun y : ℝ => f y - g y) (Set.Ioi 0) volume :=
    hf_int.sub hg_int
  have h :=
    halfLineReflectedKernelOperator_L1_Linfty_smoothing
      (f := fun y : ℝ => f y - g y) ht x hdiff_int
  rwa [halfLineReflectedKernelOperator_sub x hf_kernel hg_kernel] at h

/-- Absolute-value form of `L¹ → L∞` difference smoothing for the half-line
reflected helper operator. -/
theorem halfLineReflectedKernelOperator_diff_L1_Linfty_smoothing_abs
    {f g : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hf_int : IntegrableOn f (Set.Ioi 0) volume)
    (hg_int : IntegrableOn g (Set.Ioi 0) volume) :
    |halfLineReflectedKernelOperator t f x -
        halfLineReflectedKernelOperator t g x| ≤
      (2 / Real.sqrt (4 * Real.pi * t)) *
        ∫ y in Set.Ioi (0 : ℝ), |f y - g y| := by
  simpa [Real.norm_eq_abs] using
    halfLineReflectedKernelOperator_diff_L1_Linfty_smoothing
      ht x hf_int hg_int

/-- The normalized reflected kernel pointwise bound. -/
theorem normalizedZerothReflectionKernel_pointwise_bound
    {t : ℝ} (ht : 0 < t) (L x y : ℝ) :
    normalizedZerothReflectionKernel L t x y ≤
      1 / Real.sqrt (4 * Real.pi * t) := by
  unfold normalizedZerothReflectionKernel neumannHeatKernel_zerothReflection
  calc (1 / 2) * (heatKernel t (x - y) + heatKernel t (x + y))
      ≤ (1 / 2) * (1 / Real.sqrt (4 * Real.pi * t) +
          1 / Real.sqrt (4 * Real.pi * t)) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (heatKernel_pointwise_bound ht _)
            (heatKernel_pointwise_bound ht _))
          (by norm_num)
    _ = 1 / Real.sqrt (4 * Real.pi * t) := by ring

/-- The normalized reflected helper kernel times an `L¹` input is integrable. -/
theorem normalizedZerothReflectionKernel_mul_integrable_of_integrable
    {f : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hf_int : Integrable f) :
    Integrable (fun y => normalizedZerothReflectionKernel 0 t x y * f y) := by
  have hkernel_meas :
      AEStronglyMeasurable
        (fun y : ℝ => normalizedZerothReflectionKernel 0 t x y) volume :=
    (normalizedZerothReflectionKernel_integrable ht 0 x).aestronglyMeasurable
  have hkernel_bound :
      ∀ y : ℝ, ‖normalizedZerothReflectionKernel 0 t x y‖ ≤
        1 / Real.sqrt (4 * Real.pi * t) := by
    intro y
    rw [Real.norm_eq_abs,
      abs_of_nonneg (normalizedZerothReflectionKernel_nonneg ht 0 x y)]
    exact normalizedZerothReflectionKernel_pointwise_bound ht 0 x y
  simpa [mul_comm] using
    hf_int.mul_bdd hkernel_meas
      (Filter.Eventually.of_forall hkernel_bound)

/-- L¹→L∞ smoothing for the reflected Neumann kernel:
    ‖Tf(x)‖ ≤ (1/√(4πt)) · ‖f‖₁. -/
theorem normalizedReflectedKernelIntegral_L1_Linfty_smoothing
    {f : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hf_int : Integrable f) :
    ‖∫ y, normalizedZerothReflectionKernel 0 t x y * f y‖ ≤
      (1 / Real.sqrt (4 * Real.pi * t)) * ∫ y, ‖f y‖ := by
  calc ‖∫ y, normalizedZerothReflectionKernel 0 t x y * f y‖
      ≤ ∫ y, ‖normalizedZerothReflectionKernel 0 t x y * f y‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ y, (1 / Real.sqrt (4 * Real.pi * t)) * ‖f y‖ := by
        apply MeasureTheory.integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall fun y => norm_nonneg _
        · exact (hf_int.norm).smul (1 / Real.sqrt (4 * Real.pi * t))
        · exact Filter.Eventually.of_forall fun y => by
            change ‖normalizedZerothReflectionKernel 0 t x y * f y‖ ≤
              (1 / Real.sqrt (4 * Real.pi * t)) * ‖f y‖
            rw [norm_mul, Real.norm_eq_abs,
                abs_of_nonneg
                  (normalizedZerothReflectionKernel_nonneg ht 0 x y)]
            exact mul_le_mul_of_nonneg_right
              (normalizedZerothReflectionKernel_pointwise_bound ht 0 x y)
              (norm_nonneg _)
    _ = (1 / Real.sqrt (4 * Real.pi * t)) * ∫ y, ‖f y‖ :=
        MeasureTheory.integral_const_mul _ _

/-- Absolute-value form of the normalized reflected helper-kernel
`L¹ → L∞` smoothing estimate. -/
theorem normalizedReflectedKernelIntegral_L1_Linfty_smoothing_abs
    {f : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hf_int : Integrable f) :
    |∫ y, normalizedZerothReflectionKernel 0 t x y * f y| ≤
      (1 / Real.sqrt (4 * Real.pi * t)) * ∫ y, |f y| := by
  simpa [Real.norm_eq_abs] using
    normalizedReflectedKernelIntegral_L1_Linfty_smoothing ht x hf_int

/-- `L¹ → L∞` smoothing for differences of the normalized reflected helper
kernel integral. -/
theorem normalizedReflectedKernelIntegral_diff_L1_Linfty_smoothing
    {f g : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hf_int : Integrable f) (hg_int : Integrable g) :
    ‖(∫ y, normalizedZerothReflectionKernel 0 t x y * f y) -
        ∫ y, normalizedZerothReflectionKernel 0 t x y * g y‖ ≤
      (1 / Real.sqrt (4 * Real.pi * t)) * ∫ y, ‖f y - g y‖ := by
  have hf_kernel :
      Integrable (fun y => normalizedZerothReflectionKernel 0 t x y * f y) :=
    normalizedZerothReflectionKernel_mul_integrable_of_integrable ht x hf_int
  have hg_kernel :
      Integrable (fun y => normalizedZerothReflectionKernel 0 t x y * g y) :=
    normalizedZerothReflectionKernel_mul_integrable_of_integrable ht x hg_int
  have hdiff_int : Integrable (fun y : ℝ => f y - g y) :=
    hf_int.sub hg_int
  have h :=
    normalizedReflectedKernelIntegral_L1_Linfty_smoothing
      (f := fun y : ℝ => f y - g y) ht x hdiff_int
  rwa [normalizedReflectedKernelIntegral_sub x hf_kernel hg_kernel] at h

/-- Absolute-value form of the `L¹ → L∞` difference smoothing estimate for
the normalized reflected helper kernel integral. -/
theorem normalizedReflectedKernelIntegral_diff_L1_Linfty_smoothing_abs
    {f g : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hf_int : Integrable f) (hg_int : Integrable g) :
    |(∫ y, normalizedZerothReflectionKernel 0 t x y * f y) -
        ∫ y, normalizedZerothReflectionKernel 0 t x y * g y| ≤
      (1 / Real.sqrt (4 * Real.pi * t)) * ∫ y, |f y - g y| := by
  simpa [Real.norm_eq_abs] using
    normalizedReflectedKernelIntegral_diff_L1_Linfty_smoothing
      ht x hf_int hg_int

/-- The concrete full-line operator induced by the normalized two-term
reflected helper kernel.  This is still only a helper operator, not the full
interval Neumann heat semigroup. -/
def normalizedReflectedKernelOperator
    (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, normalizedZerothReflectionKernel 0 t x y * f y

theorem normalizedReflectedKernelOperator_const
    {t : ℝ} (ht : 0 < t) (c x : ℝ) :
    normalizedReflectedKernelOperator t (fun _ => c) x = c := by
  exact normalizedZerothReflectionKernel_const_integral ht 0 x c

theorem normalizedReflectedKernelOperator_nonneg
    {f : ℝ → ℝ} (hf : ∀ y, 0 ≤ f y)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    0 ≤ normalizedReflectedKernelOperator t f x :=
  normalizedReflectedKernelIntegral_nonneg hf ht x

theorem normalizedReflectedKernelOperator_mono_bounded
    {f g : ℝ → ℝ} {Mf Mg t : ℝ}
    (hfg : ∀ y, f y ≤ g y)
    (hf_bound : ∀ y, |f y| ≤ Mf) (hg_bound : ∀ y, |g y| ≤ Mg)
    (hf_meas : AEStronglyMeasurable f volume)
    (hg_meas : AEStronglyMeasurable g volume)
    (ht : 0 < t) :
    ∀ x, normalizedReflectedKernelOperator t f x ≤
      normalizedReflectedKernelOperator t g x :=
  normalizedReflectedKernelIntegral_mono_bounded
    hfg hf_bound hg_bound hf_meas hg_meas ht

theorem normalizedReflectedKernelOperator_interval_bound
    {f : ℝ → ℝ} {a b M t : ℝ}
    (hlo : ∀ y, a ≤ f y) (hhi : ∀ y, f y ≤ b)
    (hf_bound : ∀ y, |f y| ≤ M)
    (hf_meas : AEStronglyMeasurable f volume)
    (ht : 0 < t) (x : ℝ) :
    a ≤ normalizedReflectedKernelOperator t f x ∧
      normalizedReflectedKernelOperator t f x ≤ b :=
  normalizedReflectedKernelIntegral_interval_bound
    hlo hhi hf_bound hf_meas ht x

theorem normalizedReflectedKernelOperator_add_bounded
    {f g : ℝ → ℝ} {Mf Mg t : ℝ}
    (hf_bound : ∀ y, |f y| ≤ Mf) (hg_bound : ∀ y, |g y| ≤ Mg)
    (hf_meas : AEStronglyMeasurable f volume)
    (hg_meas : AEStronglyMeasurable g volume)
    (ht : 0 < t) :
    ∀ x, normalizedReflectedKernelOperator t (fun y => f y + g y) x =
      normalizedReflectedKernelOperator t f x +
        normalizedReflectedKernelOperator t g x :=
  normalizedReflectedKernelIntegral_add_bounded
    hf_bound hg_bound hf_meas hg_meas ht

theorem normalizedReflectedKernelOperator_add
    {f g : ℝ → ℝ} {t : ℝ} (x : ℝ)
    (hf : Integrable
      (fun y => normalizedZerothReflectionKernel 0 t x y * f y))
    (hg : Integrable
      (fun y => normalizedZerothReflectionKernel 0 t x y * g y)) :
    normalizedReflectedKernelOperator t (fun y => f y + g y) x =
      normalizedReflectedKernelOperator t f x +
        normalizedReflectedKernelOperator t g x :=
  normalizedReflectedKernelIntegral_add x hf hg

theorem normalizedReflectedKernelOperator_const_mul
    (a : ℝ) (f : ℝ → ℝ) (t x : ℝ) :
    normalizedReflectedKernelOperator t (fun y => a * f y) x =
      a * normalizedReflectedKernelOperator t f x :=
  normalizedReflectedKernelIntegral_const_mul a f t x

theorem normalizedReflectedKernelOperator_zero_fun (t x : ℝ) :
    normalizedReflectedKernelOperator t (fun _ => 0) x = 0 := by
  simp [normalizedReflectedKernelOperator]

theorem normalizedReflectedKernelOperator_neg
    (f : ℝ → ℝ) (t x : ℝ) :
    normalizedReflectedKernelOperator t (fun y => -f y) x =
      -normalizedReflectedKernelOperator t f x := by
  simpa using normalizedReflectedKernelOperator_const_mul (-1) f t x

theorem normalizedReflectedKernelOperator_sub_bounded
    {f g : ℝ → ℝ} {Mf Mg t : ℝ}
    (hf_bound : ∀ y, |f y| ≤ Mf) (hg_bound : ∀ y, |g y| ≤ Mg)
    (hf_meas : AEStronglyMeasurable f volume)
    (hg_meas : AEStronglyMeasurable g volume)
    (ht : 0 < t) :
    ∀ x, normalizedReflectedKernelOperator t (fun y => f y - g y) x =
      normalizedReflectedKernelOperator t f x -
        normalizedReflectedKernelOperator t g x :=
  normalizedReflectedKernelIntegral_sub_bounded
    hf_bound hg_bound hf_meas hg_meas ht

theorem normalizedReflectedKernelOperator_sub
    {f g : ℝ → ℝ} {t : ℝ} (x : ℝ)
    (hf : Integrable
      (fun y => normalizedZerothReflectionKernel 0 t x y * f y))
    (hg : Integrable
      (fun y => normalizedZerothReflectionKernel 0 t x y * g y)) :
    normalizedReflectedKernelOperator t (fun y => f y - g y) x =
      normalizedReflectedKernelOperator t f x -
        normalizedReflectedKernelOperator t g x :=
  normalizedReflectedKernelIntegral_sub x hf hg

theorem normalizedReflectedKernelOperator_Linfty_bound
    {f : ℝ → ℝ} {M t : ℝ} (hf : ∀ y, |f y| ≤ M)
    (hf_meas : AEStronglyMeasurable f volume)
    (ht : 0 < t) :
    ∀ x, |normalizedReflectedKernelOperator t f x| ≤ M :=
  fun x => normalizedReflectedKernelIntegral_Linfty_bound hf ht x hf_meas

theorem normalizedReflectedKernelOperator_abs_le_operator_abs
    {f : ℝ → ℝ} {t : ℝ} (ht : 0 < t) :
    ∀ x, |normalizedReflectedKernelOperator t f x| ≤
      normalizedReflectedKernelOperator t (fun y => |f y|) x :=
  fun x => normalizedReflectedKernelIntegral_abs_le_integral_abs ht x

theorem normalizedReflectedKernelOperator_abs_le_of_abs_le
    {f g : ℝ → ℝ} (hfg : ∀ y, |f y| ≤ g y)
    {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hg_int : Integrable
      (fun y => normalizedZerothReflectionKernel 0 t x y * g y)) :
    |normalizedReflectedKernelOperator t f x| ≤
      normalizedReflectedKernelOperator t g x :=
  normalizedReflectedKernelIntegral_abs_le_of_abs_le hfg ht x hg_int

theorem normalizedReflectedKernelOperator_abs_le_of_abs_le_bounded
    {f g : ℝ → ℝ} {Mg t : ℝ}
    (hfg : ∀ y, |f y| ≤ g y)
    (hg_bound : ∀ y, |g y| ≤ Mg)
    (hg_meas : AEStronglyMeasurable g volume)
    (ht : 0 < t) :
    ∀ x, |normalizedReflectedKernelOperator t f x| ≤
      normalizedReflectedKernelOperator t g x :=
  normalizedReflectedKernelIntegral_abs_le_of_abs_le_bounded
    hfg hg_bound hg_meas ht

theorem normalizedReflectedKernelOperator_contraction
    {f g : ℝ → ℝ} {M t : ℝ}
    (hfg : ∀ y, |f y - g y| ≤ M)
    (hf_meas : AEStronglyMeasurable f volume)
    (hg_meas : AEStronglyMeasurable g volume)
    {Mf Mg : ℝ} (hf_bound : ∀ y, |f y| ≤ Mf)
    (hg_bound : ∀ y, |g y| ≤ Mg)
    (ht : 0 < t) :
    ∀ x, |normalizedReflectedKernelOperator t f x -
      normalizedReflectedKernelOperator t g x| ≤ M :=
  normalizedReflectedKernelIntegral_contraction
    hfg hf_meas hg_meas hf_bound hg_bound ht

theorem normalizedReflectedKernelOperator_L1_Linfty_smoothing
    {f : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hf_int : Integrable f) :
    ‖normalizedReflectedKernelOperator t f x‖ ≤
      (1 / Real.sqrt (4 * Real.pi * t)) * ∫ y, ‖f y‖ :=
  normalizedReflectedKernelIntegral_L1_Linfty_smoothing ht x hf_int

theorem normalizedReflectedKernelOperator_L1_Linfty_smoothing_abs
    {f : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hf_int : Integrable f) :
    |normalizedReflectedKernelOperator t f x| ≤
      (1 / Real.sqrt (4 * Real.pi * t)) * ∫ y, |f y| :=
  normalizedReflectedKernelIntegral_L1_Linfty_smoothing_abs ht x hf_int

theorem normalizedReflectedKernelOperator_diff_L1_Linfty_smoothing
    {f g : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hf_int : Integrable f) (hg_int : Integrable g) :
    ‖normalizedReflectedKernelOperator t f x -
        normalizedReflectedKernelOperator t g x‖ ≤
      (1 / Real.sqrt (4 * Real.pi * t)) * ∫ y, ‖f y - g y‖ :=
  normalizedReflectedKernelIntegral_diff_L1_Linfty_smoothing
    ht x hf_int hg_int

theorem normalizedReflectedKernelOperator_diff_L1_Linfty_smoothing_abs
    {f g : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hf_int : Integrable f) (hg_int : Integrable g) :
    |normalizedReflectedKernelOperator t f x -
        normalizedReflectedKernelOperator t g x| ≤
      (1 / Real.sqrt (4 * Real.pi * t)) * ∫ y, |f y - g y| :=
  normalizedReflectedKernelIntegral_diff_L1_Linfty_smoothing_abs
    ht x hf_int hg_int

/-- Interval semigroup helper operator obtained by restricting the normalized
zeroth-reflection helper kernel to `[0,L]`.  This is still a concrete helper
operator, not a packaged Neumann semigroup assumption. -/
def intervalSemigroupOperator (L t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, normalizedZerothReflectionKernel L t x y * f y ∂ intervalMeasure L

/-- The normalized helper kernel has restricted interval mass at most one. -/
theorem normalizedZerothReflectionKernel_intervalIntegral_le_one
    {t : ℝ} (ht : 0 < t) (L x : ℝ) :
    ∫ y, normalizedZerothReflectionKernel L t x y ∂ intervalMeasure L ≤ 1 := by
  unfold intervalMeasure
  change ∫ y in intervalSet L, normalizedZerothReflectionKernel L t x y ≤ 1
  rw [← normalizedZerothReflectionKernel_integral ht L x]
  exact MeasureTheory.setIntegral_le_integral
    (normalizedZerothReflectionKernel_integrable ht L x)
    (Filter.Eventually.of_forall fun y =>
      normalizedZerothReflectionKernel_nonneg ht L x y)

/-- The restricted kernel mass entering the interval helper operator is at
most one. -/
theorem intervalSemigroupOperator_intervalIntegral_le_one
    {t : ℝ} (ht : 0 < t) (L x : ℝ) :
    ∫ y, normalizedZerothReflectionKernel L t x y ∂ intervalMeasure L ≤ 1 :=
  normalizedZerothReflectionKernel_intervalIntegral_le_one ht L x

/-- The restricted interval mass of the normalized helper kernel is
nonnegative. -/
theorem normalizedZerothReflectionKernel_intervalIntegral_nonneg
    {t : ℝ} (ht : 0 < t) (L x : ℝ) :
    0 ≤ ∫ y, normalizedZerothReflectionKernel L t x y ∂ intervalMeasure L := by
  exact MeasureTheory.integral_nonneg fun y =>
    normalizedZerothReflectionKernel_nonneg ht L x y

/-- The restricted interval mass of the normalized helper kernel lies in
`[0,1]`. -/
theorem normalizedZerothReflectionKernel_intervalIntegral_mem_Icc
    {t : ℝ} (ht : 0 < t) (L x : ℝ) :
    (∫ y, normalizedZerothReflectionKernel L t x y ∂ intervalMeasure L) ∈
      Set.Icc (0 : ℝ) 1 :=
  ⟨normalizedZerothReflectionKernel_intervalIntegral_nonneg ht L x,
    normalizedZerothReflectionKernel_intervalIntegral_le_one ht L x⟩

/-- The normalized helper kernel is integrable against the interval measure. -/
theorem normalizedZerothReflectionKernel_interval_integrable
    {t : ℝ} (ht : 0 < t) (L x : ℝ) :
    Integrable (fun y => normalizedZerothReflectionKernel L t x y)
      (intervalMeasure L) := by
  unfold intervalMeasure
  exact (normalizedZerothReflectionKernel_integrable ht L x).mono_measure
    Measure.restrict_le_self

/-- Positivity preservation for the interval helper operator. -/
theorem intervalSemigroupOperator_nonneg
    {L t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf : ∀ y, 0 ≤ f y) (x : ℝ) :
    0 ≤ intervalSemigroupOperator L t f x := by
  unfold intervalSemigroupOperator
  exact MeasureTheory.integral_nonneg fun y =>
    mul_nonneg (normalizedZerothReflectionKernel_nonneg ht L x y) (hf y)

/-- `L¹ → L∞` smoothing for the interval helper operator. -/
theorem intervalSemigroupOperator_L1_Linfty
    {L t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf_int : Integrable f (intervalMeasure L)) (x : ℝ) :
    ‖intervalSemigroupOperator L t f x‖ ≤
      (1 / Real.sqrt (4 * Real.pi * t)) *
        ∫ y, ‖f y‖ ∂ intervalMeasure L := by
  unfold intervalSemigroupOperator
  calc ‖∫ y, normalizedZerothReflectionKernel L t x y * f y ∂ intervalMeasure L‖
      ≤ ∫ y, ‖normalizedZerothReflectionKernel L t x y * f y‖
          ∂ intervalMeasure L :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ y, (1 / Real.sqrt (4 * Real.pi * t)) * ‖f y‖
          ∂ intervalMeasure L := by
        apply MeasureTheory.integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall fun y => norm_nonneg _
        · exact (hf_int.norm).smul (1 / Real.sqrt (4 * Real.pi * t))
        · exact Filter.Eventually.of_forall fun y => by
            change ‖normalizedZerothReflectionKernel L t x y * f y‖ ≤
              (1 / Real.sqrt (4 * Real.pi * t)) * ‖f y‖
            rw [norm_mul, Real.norm_eq_abs,
              abs_of_nonneg (normalizedZerothReflectionKernel_nonneg ht L x y)]
            exact mul_le_mul_of_nonneg_right
              (normalizedZerothReflectionKernel_pointwise_bound ht L x y)
              (norm_nonneg _)
    _ = (1 / Real.sqrt (4 * Real.pi * t)) *
        ∫ y, ‖f y‖ ∂ intervalMeasure L :=
        MeasureTheory.integral_const_mul _ _

/-- Absolute-value form of interval helper `L¹ → L∞` smoothing. -/
theorem intervalSemigroupOperator_L1_Linfty_abs
    {L t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf_int : Integrable f (intervalMeasure L)) (x : ℝ) :
    |intervalSemigroupOperator L t f x| ≤
      (1 / Real.sqrt (4 * Real.pi * t)) *
        ∫ y, |f y| ∂ intervalMeasure L := by
  simpa [Real.norm_eq_abs] using
    intervalSemigroupOperator_L1_Linfty ht hf_int x

/-- Bounded-input `L¹ → L∞` smoothing for the interval helper operator. -/
theorem intervalSemigroupOperator_L1_Linfty_bounded
    {L t Mf : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ}
    (hf_meas : AEStronglyMeasurable f (intervalMeasure L))
    (hf_bound : ∀ y, |f y| ≤ Mf) (x : ℝ) :
    ‖intervalSemigroupOperator L t f x‖ ≤
      (1 / Real.sqrt (4 * Real.pi * t)) *
        ∫ y, ‖f y‖ ∂ intervalMeasure L :=
  intervalSemigroupOperator_L1_Linfty ht
    (intervalMeasure_integrable_of_abs_bound hf_meas hf_bound) x

/-- Absolute-value bounded-input `L¹ → L∞` smoothing for the interval helper
operator. -/
theorem intervalSemigroupOperator_L1_Linfty_abs_bounded
    {L t Mf : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ}
    (hf_meas : AEStronglyMeasurable f (intervalMeasure L))
    (hf_bound : ∀ y, |f y| ≤ Mf) (x : ℝ) :
    |intervalSemigroupOperator L t f x| ≤
      (1 / Real.sqrt (4 * Real.pi * t)) *
        ∫ y, |f y| ∂ intervalMeasure L :=
  intervalSemigroupOperator_L1_Linfty_abs ht
    (intervalMeasure_integrable_of_abs_bound hf_meas hf_bound) x

/-- Explicit interval-length `L¹ → L∞` smoothing bound for a bounded input. -/
theorem intervalSemigroupOperator_L1_Linfty_abs_le_length
    {L t M : ℝ} (hL : 0 ≤ L) (ht : 0 < t)
    {f : ℝ → ℝ}
    (hf_meas : AEStronglyMeasurable f (intervalMeasure L))
    (hf_bound : ∀ y, |f y| ≤ M) (x : ℝ) :
    |intervalSemigroupOperator L t f x| ≤
      (1 / Real.sqrt (4 * Real.pi * t)) * (M * L) := by
  have hf_int : Integrable f (intervalMeasure L) :=
    intervalMeasure_integrable_of_abs_bound hf_meas hf_bound
  have hint_abs_le :
      ∫ y, |f y| ∂ intervalMeasure L ≤
        ∫ _ : ℝ, M ∂ intervalMeasure L := by
    apply MeasureTheory.integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall fun y => abs_nonneg (f y)
    · exact integrable_const M
    · exact Filter.Eventually.of_forall hf_bound
  have hcoef_nonneg : 0 ≤ 1 / Real.sqrt (4 * Real.pi * t) :=
    div_nonneg zero_le_one (Real.sqrt_nonneg _)
  have hsmooth :=
    intervalSemigroupOperator_L1_Linfty_abs ht hf_int x
  calc
    |intervalSemigroupOperator L t f x|
        ≤ (1 / Real.sqrt (4 * Real.pi * t)) *
            ∫ y, |f y| ∂ intervalMeasure L := hsmooth
    _ ≤ (1 / Real.sqrt (4 * Real.pi * t)) *
          ∫ _ : ℝ, M ∂ intervalMeasure L :=
        mul_le_mul_of_nonneg_left hint_abs_le hcoef_nonneg
    _ = (1 / Real.sqrt (4 * Real.pi * t)) * (M * L) := by
        rw [intervalMeasure_integral_const hL]

/-- The interval helper kernel times an `L¹` interval input is integrable. -/
theorem intervalSemigroupOperator_mul_integrable_of_integrable
    {L t : ℝ} (ht : 0 < t) (x : ℝ)
    {f : ℝ → ℝ} (hf_int : Integrable f (intervalMeasure L)) :
    Integrable
      (fun y => normalizedZerothReflectionKernel L t x y * f y)
      (intervalMeasure L) := by
  have hkernel_int :
      Integrable (fun y => normalizedZerothReflectionKernel L t x y)
        (intervalMeasure L) :=
    normalizedZerothReflectionKernel_interval_integrable ht L x
  have hkernel_bound :
      ∀ y : ℝ, ‖normalizedZerothReflectionKernel L t x y‖ ≤
        1 / Real.sqrt (4 * Real.pi * t) := by
    intro y
    rw [Real.norm_eq_abs,
      abs_of_nonneg (normalizedZerothReflectionKernel_nonneg ht L x y)]
    exact normalizedZerothReflectionKernel_pointwise_bound ht L x y
  simpa [mul_comm] using
    hf_int.mul_bdd hkernel_int.aestronglyMeasurable
      (Filter.Eventually.of_forall hkernel_bound)

/-- The interval helper kernel times a bounded measurable input is integrable. -/
theorem intervalSemigroupOperator_mul_integrable_of_abs_bound
    {L t Mf : ℝ} (ht : 0 < t) (x : ℝ)
    {f : ℝ → ℝ}
    (hf_meas : AEStronglyMeasurable f (intervalMeasure L))
    (hf_bound : ∀ y, |f y| ≤ Mf) :
    Integrable
      (fun y => normalizedZerothReflectionKernel L t x y * f y)
      (intervalMeasure L) :=
  intervalSemigroupOperator_mul_integrable_of_integrable ht x
    (intervalMeasure_integrable_of_abs_bound hf_meas hf_bound)

/-- The interval helper operator sends the zero input to zero. -/
theorem intervalSemigroupOperator_zero (L t x : ℝ) :
    intervalSemigroupOperator L t (fun _ => 0) x = 0 := by
  simp [intervalSemigroupOperator]

/-- Additivity for the interval helper operator on `L¹` interval inputs. -/
theorem intervalSemigroupOperator_add
    {L t : ℝ} (ht : 0 < t)
    {f g : ℝ → ℝ}
    (hf_int : Integrable f (intervalMeasure L))
    (hg_int : Integrable g (intervalMeasure L)) (x : ℝ) :
    intervalSemigroupOperator L t (fun y => f y + g y) x =
      intervalSemigroupOperator L t f x + intervalSemigroupOperator L t g x := by
  have hf_kernel :=
    intervalSemigroupOperator_mul_integrable_of_integrable ht x hf_int
  have hg_kernel :=
    intervalSemigroupOperator_mul_integrable_of_integrable ht x hg_int
  simpa [intervalSemigroupOperator, mul_add] using
    MeasureTheory.integral_add hf_kernel hg_kernel

/-- Bounded-input additivity for the interval helper operator. -/
theorem intervalSemigroupOperator_add_bounded
    {L t Mf Mg : ℝ} (ht : 0 < t)
    {f g : ℝ → ℝ}
    (hf_meas : AEStronglyMeasurable f (intervalMeasure L))
    (hg_meas : AEStronglyMeasurable g (intervalMeasure L))
    (hf_bound : ∀ y, |f y| ≤ Mf) (hg_bound : ∀ y, |g y| ≤ Mg) (x : ℝ) :
    intervalSemigroupOperator L t (fun y => f y + g y) x =
      intervalSemigroupOperator L t f x + intervalSemigroupOperator L t g x :=
  intervalSemigroupOperator_add ht
    (intervalMeasure_integrable_of_abs_bound hf_meas hf_bound)
    (intervalMeasure_integrable_of_abs_bound hg_meas hg_bound) x

/-- Scalar multiplication for the interval helper operator. -/
theorem intervalSemigroupOperator_const_mul
    (a : ℝ) (L t : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    intervalSemigroupOperator L t (fun y => a * f y) x =
      a * intervalSemigroupOperator L t f x := by
  unfold intervalSemigroupOperator
  rw [show
      (fun y : ℝ => normalizedZerothReflectionKernel L t x y * (a * f y)) =
        (fun y : ℝ => a *
          (normalizedZerothReflectionKernel L t x y * f y)) by
      ext y
      ring]
  exact MeasureTheory.integral_const_mul _ _

/-- Constant inputs are exactly the constant times the restricted kernel
mass.  The restricted interval mass is only known to be at most one, so this
is not a constant-preservation statement. -/
theorem intervalSemigroupOperator_const_eq_kernel_mass_mul
    (L t c x : ℝ) :
    intervalSemigroupOperator L t (fun _ => c) x =
      c * ∫ y, normalizedZerothReflectionKernel L t x y ∂ intervalMeasure L := by
  unfold intervalSemigroupOperator
  rw [MeasureTheory.integral_mul_const]
  ring

/-- Absolute value of a constant input is exactly the constant absolute value
times the restricted kernel mass. -/
theorem intervalSemigroupOperator_const_abs_eq_abs_mul_kernel_mass
    {t : ℝ} (ht : 0 < t) (L c x : ℝ) :
    |intervalSemigroupOperator L t (fun _ => c) x| =
      |c| * ∫ y, normalizedZerothReflectionKernel L t x y ∂ intervalMeasure L := by
  rw [intervalSemigroupOperator_const_eq_kernel_mass_mul]
  rw [abs_mul,
    abs_of_nonneg (normalizedZerothReflectionKernel_intervalIntegral_nonneg ht L x)]

/-- Absolute difference of two constant inputs is exactly the constant
difference times the restricted kernel mass. -/
theorem intervalSemigroupOperator_const_diff_abs_eq_abs_mul_kernel_mass
    {t : ℝ} (ht : 0 < t) (L c d x : ℝ) :
    |intervalSemigroupOperator L t (fun _ => c) x -
        intervalSemigroupOperator L t (fun _ => d) x| =
      |c - d| *
        ∫ y, normalizedZerothReflectionKernel L t x y ∂ intervalMeasure L := by
  rw [intervalSemigroupOperator_const_eq_kernel_mass_mul,
    intervalSemigroupOperator_const_eq_kernel_mass_mul]
  set m : ℝ :=
    ∫ y, normalizedZerothReflectionKernel L t x y ∂ intervalMeasure L
  have hm : 0 ≤ m := by
    simpa [m] using normalizedZerothReflectionKernel_intervalIntegral_nonneg ht L x
  change |c * m - d * m| = |c - d| * m
  rw [show c * m - d * m = (c - d) * m by ring]
  rw [abs_mul, abs_of_nonneg hm]

/-- Constants are contracted by the interval helper operator. -/
theorem intervalSemigroupOperator_const_contraction
    {t : ℝ} (ht : 0 < t) (L c d x : ℝ) :
    |intervalSemigroupOperator L t (fun _ => c) x -
        intervalSemigroupOperator L t (fun _ => d) x| ≤ |c - d| := by
  rw [intervalSemigroupOperator_const_diff_abs_eq_abs_mul_kernel_mass ht L c d x]
  have hmass := normalizedZerothReflectionKernel_intervalIntegral_le_one ht L x
  calc
    |c - d| *
        ∫ y, normalizedZerothReflectionKernel L t x y ∂ intervalMeasure L
        ≤ |c - d| * 1 := mul_le_mul_of_nonneg_left hmass (abs_nonneg (c - d))
    _ = |c - d| := by ring

/-- Applying the interval helper operator to `1` returns exactly the
restricted kernel mass. -/
theorem intervalSemigroupOperator_one_eq_kernel_mass
    (L t x : ℝ) :
    intervalSemigroupOperator L t (fun _ => 1) x =
      ∫ y, normalizedZerothReflectionKernel L t x y ∂ intervalMeasure L := by
  simpa using intervalSemigroupOperator_const_eq_kernel_mass_mul L t 1 x

/-- Negation for the interval helper operator. -/
theorem intervalSemigroupOperator_neg
    (L t : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    intervalSemigroupOperator L t (fun y => -f y) x =
      -intervalSemigroupOperator L t f x := by
  simpa using intervalSemigroupOperator_const_mul (-1) L t f x

/-- Subtraction for the interval helper operator on `L¹` interval inputs. -/
theorem intervalSemigroupOperator_sub
    {L t : ℝ} (ht : 0 < t)
    {f g : ℝ → ℝ}
    (hf_int : Integrable f (intervalMeasure L))
    (hg_int : Integrable g (intervalMeasure L)) (x : ℝ) :
    intervalSemigroupOperator L t (fun y => f y - g y) x =
      intervalSemigroupOperator L t f x - intervalSemigroupOperator L t g x := by
  have hf_kernel :=
    intervalSemigroupOperator_mul_integrable_of_integrable ht x hf_int
  have hg_kernel :=
    intervalSemigroupOperator_mul_integrable_of_integrable ht x hg_int
  simpa [intervalSemigroupOperator, mul_sub] using
    MeasureTheory.integral_sub hf_kernel hg_kernel

/-- Bounded-input subtraction for the interval helper operator. -/
theorem intervalSemigroupOperator_sub_bounded
    {L t Mf Mg : ℝ} (ht : 0 < t)
    {f g : ℝ → ℝ}
    (hf_meas : AEStronglyMeasurable f (intervalMeasure L))
    (hg_meas : AEStronglyMeasurable g (intervalMeasure L))
    (hf_bound : ∀ y, |f y| ≤ Mf) (hg_bound : ∀ y, |g y| ≤ Mg) (x : ℝ) :
    intervalSemigroupOperator L t (fun y => f y - g y) x =
      intervalSemigroupOperator L t f x - intervalSemigroupOperator L t g x :=
  intervalSemigroupOperator_sub ht
    (intervalMeasure_integrable_of_abs_bound hf_meas hf_bound)
    (intervalMeasure_integrable_of_abs_bound hg_meas hg_bound) x

/-- Difference `L¹ → L∞` smoothing for the interval helper operator. -/
theorem intervalSemigroupOperator_diff_L1_Linfty
    {L t : ℝ} (ht : 0 < t)
    {f g : ℝ → ℝ}
    (hf_int : Integrable f (intervalMeasure L))
    (hg_int : Integrable g (intervalMeasure L)) (x : ℝ) :
    ‖intervalSemigroupOperator L t f x - intervalSemigroupOperator L t g x‖ ≤
      (1 / Real.sqrt (4 * Real.pi * t)) *
        ∫ y, ‖f y - g y‖ ∂ intervalMeasure L := by
  have hdiff_int : Integrable (fun y : ℝ => f y - g y) (intervalMeasure L) :=
    hf_int.sub hg_int
  have h :=
    intervalSemigroupOperator_L1_Linfty
      (L := L) (t := t) ht (f := fun y : ℝ => f y - g y) hdiff_int x
  rwa [intervalSemigroupOperator_sub ht hf_int hg_int x] at h

/-- Absolute-value form of interval helper difference smoothing. -/
theorem intervalSemigroupOperator_diff_L1_Linfty_abs
    {L t : ℝ} (ht : 0 < t)
    {f g : ℝ → ℝ}
    (hf_int : Integrable f (intervalMeasure L))
    (hg_int : Integrable g (intervalMeasure L)) (x : ℝ) :
    |intervalSemigroupOperator L t f x - intervalSemigroupOperator L t g x| ≤
      (1 / Real.sqrt (4 * Real.pi * t)) *
        ∫ y, |f y - g y| ∂ intervalMeasure L := by
  simpa [Real.norm_eq_abs] using
    intervalSemigroupOperator_diff_L1_Linfty ht hf_int hg_int x

/-- Bounded-input difference `L¹ → L∞` smoothing for the interval helper
operator. -/
theorem intervalSemigroupOperator_diff_L1_Linfty_bounded
    {L t Mf Mg : ℝ} (ht : 0 < t)
    {f g : ℝ → ℝ}
    (hf_meas : AEStronglyMeasurable f (intervalMeasure L))
    (hg_meas : AEStronglyMeasurable g (intervalMeasure L))
    (hf_bound : ∀ y, |f y| ≤ Mf) (hg_bound : ∀ y, |g y| ≤ Mg) (x : ℝ) :
    ‖intervalSemigroupOperator L t f x - intervalSemigroupOperator L t g x‖ ≤
      (1 / Real.sqrt (4 * Real.pi * t)) *
        ∫ y, ‖f y - g y‖ ∂ intervalMeasure L :=
  intervalSemigroupOperator_diff_L1_Linfty ht
    (intervalMeasure_integrable_of_abs_bound hf_meas hf_bound)
    (intervalMeasure_integrable_of_abs_bound hg_meas hg_bound) x

/-- Absolute-value bounded-input difference smoothing for the interval helper
operator. -/
theorem intervalSemigroupOperator_diff_L1_Linfty_abs_bounded
    {L t Mf Mg : ℝ} (ht : 0 < t)
    {f g : ℝ → ℝ}
    (hf_meas : AEStronglyMeasurable f (intervalMeasure L))
    (hg_meas : AEStronglyMeasurable g (intervalMeasure L))
    (hf_bound : ∀ y, |f y| ≤ Mf) (hg_bound : ∀ y, |g y| ≤ Mg) (x : ℝ) :
    |intervalSemigroupOperator L t f x - intervalSemigroupOperator L t g x| ≤
      (1 / Real.sqrt (4 * Real.pi * t)) *
        ∫ y, |f y - g y| ∂ intervalMeasure L := by
  simpa [Real.norm_eq_abs] using
    intervalSemigroupOperator_diff_L1_Linfty_bounded
      ht hf_meas hg_meas hf_bound hg_bound x

/-- Monotonicity for the interval helper operator on `L¹` interval inputs. -/
theorem intervalSemigroupOperator_mono
    {L t : ℝ} (ht : 0 < t)
    {f g : ℝ → ℝ}
    (hf_int : Integrable f (intervalMeasure L))
    (hg_int : Integrable g (intervalMeasure L))
    (hfg : ∀ y, f y ≤ g y) (x : ℝ) :
    intervalSemigroupOperator L t f x ≤ intervalSemigroupOperator L t g x := by
  have hnonneg :
      0 ≤ intervalSemigroupOperator L t (fun y => g y - f y) x :=
    intervalSemigroupOperator_nonneg ht
      (fun y => sub_nonneg.mpr (hfg y)) x
  rw [intervalSemigroupOperator_sub ht hg_int hf_int x] at hnonneg
  linarith

/-- Bounded-input monotonicity for the interval helper operator. -/
theorem intervalSemigroupOperator_mono_bounded
    {L t Mf Mg : ℝ} (ht : 0 < t)
    {f g : ℝ → ℝ}
    (hf_meas : AEStronglyMeasurable f (intervalMeasure L))
    (hg_meas : AEStronglyMeasurable g (intervalMeasure L))
    (hf_bound : ∀ y, |f y| ≤ Mf) (hg_bound : ∀ y, |g y| ≤ Mg)
    (hfg : ∀ y, f y ≤ g y) (x : ℝ) :
    intervalSemigroupOperator L t f x ≤ intervalSemigroupOperator L t g x := by
  exact intervalSemigroupOperator_mono ht
    (intervalMeasure_integrable_of_abs_bound hf_meas hf_bound)
    (intervalMeasure_integrable_of_abs_bound hg_meas hg_bound)
    hfg x

/-- Sharp sub-Markov upper bound: if `f ≤ M`, then the restricted interval
helper output is bounded by `M` times the restricted kernel mass. -/
theorem intervalSemigroupOperator_le_const_mul_kernel_mass
    {L t M : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf_int : Integrable f (intervalMeasure L))
    (hf_le : ∀ y, f y ≤ M) (x : ℝ) :
    intervalSemigroupOperator L t f x ≤
      M * ∫ y, normalizedZerothReflectionKernel L t x y ∂ intervalMeasure L := by
  have hconst_int : Integrable (fun _ : ℝ => M) (intervalMeasure L) :=
    integrable_const M
  have hmono :=
    intervalSemigroupOperator_mono
      (L := L) (t := t) ht hf_int hconst_int hf_le x
  rwa [intervalSemigroupOperator_const_eq_kernel_mass_mul] at hmono

/-- Bounded-input version of the sharp sub-Markov upper bound. -/
theorem intervalSemigroupOperator_le_const_mul_kernel_mass_bounded
    {L t Mf M : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ}
    (hf_meas : AEStronglyMeasurable f (intervalMeasure L))
    (hf_bound : ∀ y, |f y| ≤ Mf)
    (hf_le : ∀ y, f y ≤ M) (x : ℝ) :
    intervalSemigroupOperator L t f x ≤
      M * ∫ y, normalizedZerothReflectionKernel L t x y ∂ intervalMeasure L :=
  intervalSemigroupOperator_le_const_mul_kernel_mass ht
    (intervalMeasure_integrable_of_abs_bound hf_meas hf_bound) hf_le x

/-- Sharp sub-Markov lower bound: if `a ≤ f`, then the restricted interval
helper output is bounded below by `a` times the restricted kernel mass. -/
theorem intervalSemigroupOperator_const_mul_kernel_mass_le
    {L t a : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf_int : Integrable f (intervalMeasure L))
    (hf_ge : ∀ y, a ≤ f y) (x : ℝ) :
    a * ∫ y, normalizedZerothReflectionKernel L t x y ∂ intervalMeasure L ≤
      intervalSemigroupOperator L t f x := by
  have hconst_int : Integrable (fun _ : ℝ => a) (intervalMeasure L) :=
    integrable_const a
  have hmono :=
    intervalSemigroupOperator_mono
      (L := L) (t := t) ht hconst_int hf_int hf_ge x
  rwa [intervalSemigroupOperator_const_eq_kernel_mass_mul] at hmono

/-- Bounded-input version of the sharp sub-Markov lower bound. -/
theorem intervalSemigroupOperator_const_mul_kernel_mass_le_bounded
    {L t Mf a : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ}
    (hf_meas : AEStronglyMeasurable f (intervalMeasure L))
    (hf_bound : ∀ y, |f y| ≤ Mf)
    (hf_ge : ∀ y, a ≤ f y) (x : ℝ) :
    a * ∫ y, normalizedZerothReflectionKernel L t x y ∂ intervalMeasure L ≤
      intervalSemigroupOperator L t f x :=
  intervalSemigroupOperator_const_mul_kernel_mass_le ht
    (intervalMeasure_integrable_of_abs_bound hf_meas hf_bound) hf_ge x

/-- Sharp interval bound with the restricted kernel mass. -/
theorem intervalSemigroupOperator_kernel_mass_interval_bound
    {L t a b : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf_int : Integrable f (intervalMeasure L))
    (hf_ge : ∀ y, a ≤ f y) (hf_le : ∀ y, f y ≤ b) (x : ℝ) :
    a * ∫ y, normalizedZerothReflectionKernel L t x y ∂ intervalMeasure L ≤
      intervalSemigroupOperator L t f x ∧
    intervalSemigroupOperator L t f x ≤
      b * ∫ y, normalizedZerothReflectionKernel L t x y ∂ intervalMeasure L :=
  ⟨intervalSemigroupOperator_const_mul_kernel_mass_le ht hf_int hf_ge x,
    intervalSemigroupOperator_le_const_mul_kernel_mass ht hf_int hf_le x⟩

/-- Bounded-input version of the sharp interval bound with the restricted
kernel mass. -/
theorem intervalSemigroupOperator_kernel_mass_interval_bound_bounded
    {L t Mf a b : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ}
    (hf_meas : AEStronglyMeasurable f (intervalMeasure L))
    (hf_bound : ∀ y, |f y| ≤ Mf)
    (hf_ge : ∀ y, a ≤ f y) (hf_le : ∀ y, f y ≤ b) (x : ℝ) :
    a * ∫ y, normalizedZerothReflectionKernel L t x y ∂ intervalMeasure L ≤
      intervalSemigroupOperator L t f x ∧
    intervalSemigroupOperator L t f x ≤
      b * ∫ y, normalizedZerothReflectionKernel L t x y ∂ intervalMeasure L :=
  intervalSemigroupOperator_kernel_mass_interval_bound ht
    (intervalMeasure_integrable_of_abs_bound hf_meas hf_bound)
    hf_ge hf_le x

/-- Sub-Markov interval bound for inputs whose range is contained in an
interval crossing zero. -/
theorem intervalSemigroupOperator_signed_interval_bound
    {L t a b : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf_int : Integrable f (intervalMeasure L))
    (ha : a ≤ 0) (hb : 0 ≤ b)
    (hf_ge : ∀ y, a ≤ f y) (hf_le : ∀ y, f y ≤ b) (x : ℝ) :
    a ≤ intervalSemigroupOperator L t f x ∧
      intervalSemigroupOperator L t f x ≤ b := by
  have hmass_le := normalizedZerothReflectionKernel_intervalIntegral_le_one ht L x
  have hbounds :=
    intervalSemigroupOperator_kernel_mass_interval_bound
      (L := L) (t := t) (a := a) (b := b) ht hf_int hf_ge hf_le x
  constructor
  · calc
      a = a * 1 := by ring
      _ ≤ a * ∫ y, normalizedZerothReflectionKernel L t x y ∂ intervalMeasure L :=
        mul_le_mul_of_nonpos_left hmass_le ha
      _ ≤ intervalSemigroupOperator L t f x := hbounds.1
  · calc
      intervalSemigroupOperator L t f x
          ≤ b * ∫ y, normalizedZerothReflectionKernel L t x y ∂ intervalMeasure L :=
        hbounds.2
      _ ≤ b * 1 := mul_le_mul_of_nonneg_left hmass_le hb
      _ = b := by ring

/-- Bounded-input version of the signed sub-Markov interval bound. -/
theorem intervalSemigroupOperator_signed_interval_bound_bounded
    {L t Mf a b : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ}
    (hf_meas : AEStronglyMeasurable f (intervalMeasure L))
    (hf_bound : ∀ y, |f y| ≤ Mf)
    (ha : a ≤ 0) (hb : 0 ≤ b)
    (hf_ge : ∀ y, a ≤ f y) (hf_le : ∀ y, f y ≤ b) (x : ℝ) :
    a ≤ intervalSemigroupOperator L t f x ∧
      intervalSemigroupOperator L t f x ≤ b :=
  intervalSemigroupOperator_signed_interval_bound ht
    (intervalMeasure_integrable_of_abs_bound hf_meas hf_bound)
    ha hb hf_ge hf_le x

/-- Sharp sub-Markov interval bound for nonnegative inputs bounded above by
`M`. -/
theorem intervalSemigroupOperator_submarkov_interval_bound
    {L t M : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf_int : Integrable f (intervalMeasure L))
    (hf_nonneg : ∀ y, 0 ≤ f y) (hf_le : ∀ y, f y ≤ M) (x : ℝ) :
    0 ≤ intervalSemigroupOperator L t f x ∧
      intervalSemigroupOperator L t f x ≤
        M * ∫ y, normalizedZerothReflectionKernel L t x y ∂ intervalMeasure L :=
  ⟨intervalSemigroupOperator_nonneg ht hf_nonneg x,
    intervalSemigroupOperator_le_const_mul_kernel_mass ht hf_int hf_le x⟩

/-- Bounded-input version of the sharp sub-Markov interval bound for
nonnegative inputs. -/
theorem intervalSemigroupOperator_submarkov_interval_bound_bounded
    {L t Mf M : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ}
    (hf_meas : AEStronglyMeasurable f (intervalMeasure L))
    (hf_bound : ∀ y, |f y| ≤ Mf)
    (hf_nonneg : ∀ y, 0 ≤ f y) (hf_le : ∀ y, f y ≤ M) (x : ℝ) :
    0 ≤ intervalSemigroupOperator L t f x ∧
      intervalSemigroupOperator L t f x ≤
        M * ∫ y, normalizedZerothReflectionKernel L t x y ∂ intervalMeasure L :=
  intervalSemigroupOperator_submarkov_interval_bound ht
    (intervalMeasure_integrable_of_abs_bound hf_meas hf_bound)
    hf_nonneg hf_le x

/-- The interval helper operator is dominated by the integral of the pointwise
absolute value. -/
theorem intervalSemigroupOperator_abs_le_integral_abs
    {L t : ℝ} (ht : 0 < t) (f : ℝ → ℝ) (x : ℝ) :
    |intervalSemigroupOperator L t f x| ≤
      ∫ y, normalizedZerothReflectionKernel L t x y * |f y|
        ∂ intervalMeasure L := by
  unfold intervalSemigroupOperator
  calc
    |∫ y, normalizedZerothReflectionKernel L t x y * f y ∂ intervalMeasure L|
        ≤ ∫ y, ‖normalizedZerothReflectionKernel L t x y * f y‖
            ∂ intervalMeasure L := by
          rw [← Real.norm_eq_abs]
          exact MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ y, |normalizedZerothReflectionKernel L t x y * f y|
          ∂ intervalMeasure L := by
          simp [Real.norm_eq_abs]
    _ = ∫ y, normalizedZerothReflectionKernel L t x y * |f y|
          ∂ intervalMeasure L := by
          congr 1
          ext y
          rw [abs_mul, abs_of_nonneg
            (normalizedZerothReflectionKernel_nonneg ht L x y)]

/-- Domination principle for the interval helper operator. -/
theorem intervalSemigroupOperator_abs_le_of_abs_le
    {L t : ℝ} (ht : 0 < t)
    {f g : ℝ → ℝ} (hfg : ∀ y, |f y| ≤ g y)
    (hg_int : Integrable g (intervalMeasure L)) (x : ℝ) :
    |intervalSemigroupOperator L t f x| ≤
      intervalSemigroupOperator L t g x := by
  exact le_trans
    (intervalSemigroupOperator_abs_le_integral_abs ht f x)
    (by
      unfold intervalSemigroupOperator
      apply MeasureTheory.integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun y =>
          mul_nonneg
            (normalizedZerothReflectionKernel_nonneg ht L x y)
            (abs_nonneg (f y))
      · exact intervalSemigroupOperator_mul_integrable_of_integrable
          ht x hg_int
      · exact Filter.Eventually.of_forall fun y =>
          mul_le_mul_of_nonneg_left (hfg y)
            (normalizedZerothReflectionKernel_nonneg ht L x y))

/-- The interval helper operator is dominated by applying it to `|f|`. -/
theorem intervalSemigroupOperator_abs_le_operator_abs
    {L t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf_int : Integrable f (intervalMeasure L)) (x : ℝ) :
    |intervalSemigroupOperator L t f x| ≤
      intervalSemigroupOperator L t (fun y => |f y|) x :=
  intervalSemigroupOperator_abs_le_of_abs_le ht
    (fun _ => le_rfl) hf_int.norm x

/-- Bounded-input domination principle for the interval helper operator. -/
theorem intervalSemigroupOperator_abs_le_of_abs_le_bounded
    {L t Mg : ℝ} (ht : 0 < t)
    {f g : ℝ → ℝ} (hfg : ∀ y, |f y| ≤ g y)
    (hg_meas : AEStronglyMeasurable g (intervalMeasure L))
    (hg_bound : ∀ y, |g y| ≤ Mg) (x : ℝ) :
    |intervalSemigroupOperator L t f x| ≤
      intervalSemigroupOperator L t g x :=
  intervalSemigroupOperator_abs_le_of_abs_le ht hfg
    (intervalMeasure_integrable_of_abs_bound hg_meas hg_bound) x

/-- Bounded-input version of domination by applying the interval helper
operator to `|f|`. -/
theorem intervalSemigroupOperator_abs_le_operator_abs_bounded
    {L t Mf : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ}
    (hf_meas : AEStronglyMeasurable f (intervalMeasure L))
    (hf_bound : ∀ y, |f y| ≤ Mf) (x : ℝ) :
    |intervalSemigroupOperator L t f x| ≤
      intervalSemigroupOperator L t (fun y => |f y|) x :=
  intervalSemigroupOperator_abs_le_operator_abs ht
    (intervalMeasure_integrable_of_abs_bound hf_meas hf_bound) x

/-- Sharp absolute-value sub-Markov bound: if `|f| ≤ M`, then the restricted
interval helper output is bounded by `M` times the restricted kernel mass. -/
theorem intervalSemigroupOperator_abs_le_const_mul_kernel_mass
    {L t M : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf_abs : ∀ y, |f y| ≤ M) (x : ℝ) :
    |intervalSemigroupOperator L t f x| ≤
      M * ∫ y, normalizedZerothReflectionKernel L t x y ∂ intervalMeasure L := by
  have hdom :
      |intervalSemigroupOperator L t f x| ≤
        intervalSemigroupOperator L t (fun _ : ℝ => M) x :=
    intervalSemigroupOperator_abs_le_of_abs_le
      (L := L) (t := t) ht (f := f) (g := fun _ : ℝ => M)
      hf_abs (integrable_const M) x
  rwa [intervalSemigroupOperator_const_eq_kernel_mass_mul] at hdom

/-- `L∞` bound for the interval helper operator. -/
theorem intervalSemigroupOperator_Linfty_bound
    {L t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M) (hf : ∀ y, |f y| ≤ M) (x : ℝ) :
    |intervalSemigroupOperator L t f x| ≤ M := by
  unfold intervalSemigroupOperator
  have hkernel_int :
      Integrable (fun y => normalizedZerothReflectionKernel L t x y)
        (intervalMeasure L) :=
    normalizedZerothReflectionKernel_interval_integrable ht L x
  have hupper_int :
      Integrable (fun y => M * normalizedZerothReflectionKernel L t x y)
        (intervalMeasure L) :=
    hkernel_int.const_mul M
  have hmass :=
    normalizedZerothReflectionKernel_intervalIntegral_le_one ht L x
  calc |∫ y, normalizedZerothReflectionKernel L t x y * f y ∂ intervalMeasure L|
      = ‖∫ y, normalizedZerothReflectionKernel L t x y * f y
          ∂ intervalMeasure L‖ := by
        rw [Real.norm_eq_abs]
    _ ≤ ∫ y, ‖normalizedZerothReflectionKernel L t x y * f y‖
          ∂ intervalMeasure L :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ y, M * normalizedZerothReflectionKernel L t x y
          ∂ intervalMeasure L := by
        apply MeasureTheory.integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall fun y => norm_nonneg _
        · exact hupper_int
        · exact Filter.Eventually.of_forall fun y => by
            change ‖normalizedZerothReflectionKernel L t x y * f y‖ ≤
              M * normalizedZerothReflectionKernel L t x y
            rw [norm_mul, Real.norm_eq_abs,
              abs_of_nonneg (normalizedZerothReflectionKernel_nonneg ht L x y)]
            calc normalizedZerothReflectionKernel L t x y * ‖f y‖
                ≤ normalizedZerothReflectionKernel L t x y * M :=
                  mul_le_mul_of_nonneg_left
                    (by simpa [Real.norm_eq_abs] using hf y)
                    (normalizedZerothReflectionKernel_nonneg ht L x y)
              _ = M * normalizedZerothReflectionKernel L t x y := by ring
    _ = M * ∫ y, normalizedZerothReflectionKernel L t x y ∂ intervalMeasure L :=
        MeasureTheory.integral_const_mul _ _
    _ ≤ M * 1 := by
        exact mul_le_mul_of_nonneg_left hmass hM
    _ = M := by ring

/-- Short-name alias for the interval helper kernel mass bound. -/
theorem intervalIntegral_le_one
    {t : ℝ} (ht : 0 < t) (L x : ℝ) :
    ∫ y, normalizedZerothReflectionKernel L t x y ∂ intervalMeasure L ≤ 1 :=
  intervalSemigroupOperator_intervalIntegral_le_one ht L x

/-- Short-name alias for positivity preservation of the interval helper
operator. -/
theorem nonneg
    {L t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf : ∀ y, 0 ≤ f y) (x : ℝ) :
    0 ≤ intervalSemigroupOperator L t f x :=
  intervalSemigroupOperator_nonneg ht hf x

/-- Short-name alias for the interval helper `L¹ → L∞` smoothing estimate. -/
theorem L1_Linfty
    {L t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf_int : Integrable f (intervalMeasure L)) (x : ℝ) :
    ‖intervalSemigroupOperator L t f x‖ ≤
      (1 / Real.sqrt (4 * Real.pi * t)) *
        ∫ y, ‖f y‖ ∂ intervalMeasure L :=
  intervalSemigroupOperator_L1_Linfty ht hf_int x

/-- Short-name alias for the interval helper `L∞` bound. -/
theorem Linfty_bound
    {L t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M) (hf : ∀ y, |f y| ≤ M) (x : ℝ) :
    |intervalSemigroupOperator L t f x| ≤ M :=
  intervalSemigroupOperator_Linfty_bound ht hM hf x

/-- Symmetric interval bound for inputs bounded in absolute value. -/
theorem intervalSemigroupOperator_symmetric_interval_bound
    {L t M : ℝ} (ht : 0 < t) (hM : 0 ≤ M)
    {f : ℝ → ℝ} (hf_abs : ∀ y, |f y| ≤ M) (x : ℝ) :
    -M ≤ intervalSemigroupOperator L t f x ∧
      intervalSemigroupOperator L t f x ≤ M := by
  exact abs_le.mp (intervalSemigroupOperator_Linfty_bound ht hM hf_abs x)

/-- Bounded-input symmetric interval bound for inputs bounded in absolute
value. -/
theorem intervalSemigroupOperator_symmetric_interval_bound_bounded
    {L t Mf M : ℝ} (ht : 0 < t) (hM : 0 ≤ M)
    {f : ℝ → ℝ}
    (hf_meas : AEStronglyMeasurable f (intervalMeasure L))
    (hf_bound : ∀ y, |f y| ≤ Mf)
    (hf_abs : ∀ y, |f y| ≤ M) (x : ℝ) :
    -M ≤ intervalSemigroupOperator L t f x ∧
      intervalSemigroupOperator L t f x ≤ M := by
  have _ : Integrable f (intervalMeasure L) :=
    intervalMeasure_integrable_of_abs_bound hf_meas hf_bound
  exact intervalSemigroupOperator_symmetric_interval_bound ht hM hf_abs x

/-- The interval helper operator preserves pointwise bounds `0 ≤ f ≤ M`. -/
theorem intervalSemigroupOperator_interval_bound
    {L t M : ℝ} (ht : 0 < t) (hM : 0 ≤ M)
    {f : ℝ → ℝ} (hf_nonneg : ∀ y, 0 ≤ f y)
    (hf_le : ∀ y, f y ≤ M) (x : ℝ) :
    0 ≤ intervalSemigroupOperator L t f x ∧
      intervalSemigroupOperator L t f x ≤ M := by
  refine ⟨intervalSemigroupOperator_nonneg ht hf_nonneg x, ?_⟩
  have hf_abs : ∀ y, |f y| ≤ M := by
    intro y
    simpa [abs_of_nonneg (hf_nonneg y)] using hf_le y
  exact le_trans (le_abs_self _) (intervalSemigroupOperator_Linfty_bound ht hM hf_abs x)

/-- Bounded-input version of the interval helper operator preserving
pointwise bounds `0 ≤ f ≤ M`. -/
theorem intervalSemigroupOperator_interval_bound_bounded
    {L t Mf M : ℝ} (ht : 0 < t) (hM : 0 ≤ M)
    {f : ℝ → ℝ}
    (hf_meas : AEStronglyMeasurable f (intervalMeasure L))
    (hf_bound : ∀ y, |f y| ≤ Mf)
    (hf_nonneg : ∀ y, 0 ≤ f y)
    (hf_le : ∀ y, f y ≤ M) (x : ℝ) :
    0 ≤ intervalSemigroupOperator L t f x ∧
      intervalSemigroupOperator L t f x ≤ M := by
  have _ : Integrable f (intervalMeasure L) :=
    intervalMeasure_integrable_of_abs_bound hf_meas hf_bound
  exact intervalSemigroupOperator_interval_bound ht hM hf_nonneg hf_le x

/-- Constant inputs are bounded by the same nonnegative constant under the
interval helper operator. -/
theorem intervalSemigroupOperator_const_nonneg_le
    {L t c : ℝ} (ht : 0 < t) (hc : 0 ≤ c) (x : ℝ) :
    0 ≤ intervalSemigroupOperator L t (fun _ => c) x ∧
      intervalSemigroupOperator L t (fun _ => c) x ≤ c :=
  intervalSemigroupOperator_interval_bound ht hc
    (fun _ => hc) (fun _ => le_rfl) x

/-- Constant inputs satisfy the same `L∞` contraction bound under the interval
helper operator. -/
theorem intervalSemigroupOperator_const_abs_le
    {L t c : ℝ} (ht : 0 < t) (x : ℝ) :
    |intervalSemigroupOperator L t (fun _ => c) x| ≤ |c| :=
  intervalSemigroupOperator_Linfty_bound ht (abs_nonneg c)
    (fun _ => le_rfl) x

/-- The interval helper operator maps the constant one input to a value in
`[0,1]`. -/
theorem intervalSemigroupOperator_one_interval
    {L t : ℝ} (ht : 0 < t) (x : ℝ) :
    0 ≤ intervalSemigroupOperator L t (fun _ => 1) x ∧
      intervalSemigroupOperator L t (fun _ => 1) x ≤ 1 :=
  intervalSemigroupOperator_const_nonneg_le ht zero_le_one x

/-- Sharp `L∞` contraction with the restricted kernel mass. -/
theorem intervalSemigroupOperator_contraction_kernel_mass
    {L t : ℝ} (ht : 0 < t)
    {f g : ℝ → ℝ} {M : ℝ}
    (hf_int : Integrable f (intervalMeasure L))
    (hg_int : Integrable g (intervalMeasure L))
    (hfg : ∀ y, |f y - g y| ≤ M) (x : ℝ) :
    |intervalSemigroupOperator L t f x -
      intervalSemigroupOperator L t g x| ≤
      M * ∫ y, normalizedZerothReflectionKernel L t x y ∂ intervalMeasure L := by
  have hbound :=
    intervalSemigroupOperator_abs_le_const_mul_kernel_mass
      (L := L) (t := t) ht (f := fun y => f y - g y) hfg x
  rwa [intervalSemigroupOperator_sub ht hf_int hg_int x] at hbound

/-- Bounded-input version of the sharp kernel-mass contraction. -/
theorem intervalSemigroupOperator_contraction_kernel_mass_bounded
    {L t Mf Mg M : ℝ} (ht : 0 < t)
    {f g : ℝ → ℝ}
    (hf_meas : AEStronglyMeasurable f (intervalMeasure L))
    (hg_meas : AEStronglyMeasurable g (intervalMeasure L))
    (hf_bound : ∀ y, |f y| ≤ Mf) (hg_bound : ∀ y, |g y| ≤ Mg)
    (hfg : ∀ y, |f y - g y| ≤ M) (x : ℝ) :
    |intervalSemigroupOperator L t f x -
      intervalSemigroupOperator L t g x| ≤
      M * ∫ y, normalizedZerothReflectionKernel L t x y ∂ intervalMeasure L :=
  intervalSemigroupOperator_contraction_kernel_mass ht
    (intervalMeasure_integrable_of_abs_bound hf_meas hf_bound)
    (intervalMeasure_integrable_of_abs_bound hg_meas hg_bound)
    hfg x

/-- `L∞` contraction for the interval helper operator on `L¹` interval inputs. -/
theorem intervalSemigroupOperator_contraction
    {L t : ℝ} (ht : 0 < t)
    {f g : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hf_int : Integrable f (intervalMeasure L))
    (hg_int : Integrable g (intervalMeasure L))
    (hfg : ∀ y, |f y - g y| ≤ M) (x : ℝ) :
    |intervalSemigroupOperator L t f x -
      intervalSemigroupOperator L t g x| ≤ M := by
  have hbound :=
    intervalSemigroupOperator_Linfty_bound
      (L := L) (t := t) ht hM (f := fun y => f y - g y) hfg x
  rwa [intervalSemigroupOperator_sub ht hf_int hg_int x] at hbound

/-- Symmetric `L∞` contraction interval for the difference of two interval
helper outputs. -/
theorem intervalSemigroupOperator_contraction_symmetric_interval_bound
    {L t : ℝ} (ht : 0 < t)
    {f g : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hf_int : Integrable f (intervalMeasure L))
    (hg_int : Integrable g (intervalMeasure L))
    (hfg : ∀ y, |f y - g y| ≤ M) (x : ℝ) :
    -M ≤ intervalSemigroupOperator L t f x -
        intervalSemigroupOperator L t g x ∧
      intervalSemigroupOperator L t f x -
        intervalSemigroupOperator L t g x ≤ M := by
  exact abs_le.mp
    (intervalSemigroupOperator_contraction ht hM hf_int hg_int hfg x)

/-- Bounded-input `L∞` contraction for the interval helper operator. -/
theorem intervalSemigroupOperator_contraction_bounded
    {L t Mf Mg M : ℝ} (ht : 0 < t) (hM : 0 ≤ M)
    {f g : ℝ → ℝ}
    (hf_meas : AEStronglyMeasurable f (intervalMeasure L))
    (hg_meas : AEStronglyMeasurable g (intervalMeasure L))
    (hf_bound : ∀ y, |f y| ≤ Mf) (hg_bound : ∀ y, |g y| ≤ Mg)
    (hfg : ∀ y, |f y - g y| ≤ M) (x : ℝ) :
    |intervalSemigroupOperator L t f x -
      intervalSemigroupOperator L t g x| ≤ M := by
  exact intervalSemigroupOperator_contraction ht hM
    (intervalMeasure_integrable_of_abs_bound hf_meas hf_bound)
    (intervalMeasure_integrable_of_abs_bound hg_meas hg_bound)
    hfg x

/-- Bounded-input symmetric `L∞` contraction interval for the difference of
two interval helper outputs. -/
theorem intervalSemigroupOperator_contraction_symmetric_interval_bound_bounded
    {L t Mf Mg M : ℝ} (ht : 0 < t) (hM : 0 ≤ M)
    {f g : ℝ → ℝ}
    (hf_meas : AEStronglyMeasurable f (intervalMeasure L))
    (hg_meas : AEStronglyMeasurable g (intervalMeasure L))
    (hf_bound : ∀ y, |f y| ≤ Mf) (hg_bound : ∀ y, |g y| ≤ Mg)
    (hfg : ∀ y, |f y - g y| ≤ M) (x : ℝ) :
    -M ≤ intervalSemigroupOperator L t f x -
        intervalSemigroupOperator L t g x ∧
      intervalSemigroupOperator L t f x -
        intervalSemigroupOperator L t g x ≤ M :=
  abs_le.mp
    (intervalSemigroupOperator_contraction_bounded
      ht hM hf_meas hg_meas hf_bound hg_bound hfg x)

end ShenWork.IntervalDomain

end
