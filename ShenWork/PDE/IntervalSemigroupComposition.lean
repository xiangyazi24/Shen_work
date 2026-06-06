/-
  S2-atom / Q1-keystone: the Chapman–Kolmogorov composition law
  `S(s)(S(t)f) = S(s+t)f` for the full Neumann propagator, via the
  hypothesis-free spectral identity (S1).

  ## Chain

  1. `cosineCoeffs_unitIntervalCosineHeatValue` — coefficient extraction:
     the cosine coefficients of `x ↦ ∑'ₖ e^{−tλₖ} aₖ cos(kπx)` are
     `e^{−tλₙ} aₙ` (orthogonality + `∫`/`∑'` interchange, bounded `a`).
  2. `cosineCoeffs_semigroup` — `(S(t)f)^ₙ = e^{−tλₙ} f̂ₙ` for continuous
     `f` with bounded coefficients (S1 Icc identity + extraction).
  3. `intervalFullSemigroupOperator_comp` — `S(s)(S(t)f)(x) = S(s+t)f(x)`
     on `[0,1]`.

  This is the keystone for the Q1 cone-invariance positivity route
  (uniform-δ(M) hQuant for χ₀ = 0): Grönwall-type upper/lower envelopes
  `θ(t)·S(t)u₀ ≤ u(t) ≤ e^{at}·S(t)u₀` for the mild map require
  `S(t−s)S(s) = S(t)` to re-absorb the Duhamel integrand.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.PDE.IntervalFullKernelSpectralClean
import ShenWork.PDE.CosineSpectrum
import ShenWork.Paper2.IntervalMildPicardRegularity
import ShenWork.Paper2.IntervalDomainL2StaticVDifference

open MeasureTheory
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalFullKernelSpectralClean
open ShenWork.IntervalMildPicardRegularity (cosineCoeffs_eq_factor_mul_integral)
open ShenWork.Paper2 (cosineCoeffs_congr_on_Icc)

noncomputable section

namespace ShenWork.IntervalSemigroupComposition

/-! ## ℕ-summability of the heat weights -/

/-- Summability over `ℕ` of the spectral heat weights `e^{−t(nπ)²}`. -/
theorem expEigSummable {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => Real.exp (-t * unitIntervalCosineEigenvalue n)) := by
  have hr0 : (0 : ℝ) ≤ Real.exp (-(t * Real.pi ^ 2)) := (Real.exp_pos _).le
  have hr1 : Real.exp (-(t * Real.pi ^ 2)) < 1 := by
    rw [Real.exp_lt_one_iff]
    have : 0 < t * Real.pi ^ 2 := by positivity
    linarith
  refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) ?_
    (summable_geometric_of_lt_one hr0 hr1)
  intro n
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  unfold unitIntervalCosineEigenvalue
  have hn2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num
    · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith
  have hπ : (0 : ℝ) < Real.pi ^ 2 := by positivity
  calc -t * ((n : ℝ) * Real.pi) ^ 2 = -(t * Real.pi ^ 2) * (n : ℝ) ^ 2 := by ring
    _ ≤ -(t * Real.pi ^ 2) * (n : ℝ) := by
        rw [neg_mul, neg_mul, neg_le_neg_iff]
        exact mul_le_mul_of_nonneg_left hn2 (by positivity)
    _ = (n : ℝ) * -(t * Real.pi ^ 2) := by ring

/-! ## Coefficient extraction -/

set_option maxHeartbeats 800000 in
/-- **Coefficient extraction**: the cosine coefficients of the spectral
heat value `x ↦ ∑'ₖ e^{−tλₖ} aₖ cos(kπx)` are exactly `e^{−tλₙ} aₙ`,
for `t > 0` and uniformly bounded coefficients `a`. -/
theorem cosineCoeffs_unitIntervalCosineHeatValue
    {t : ℝ} (ht : 0 < t) {a : ℕ → ℝ} {M : ℝ}
    (hM : ∀ k, |a k| ≤ M) (n : ℕ) :
    cosineCoeffs (fun x => unitIntervalCosineHeatValue t a x) n
      = Real.exp (-t * unitIntervalCosineEigenvalue n) * a n := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  rw [cosineCoeffs_eq_factor_mul_integral]
  -- The summand family.
  set F : ℕ → ℝ → ℝ := fun k x =>
    Real.cos ((n : ℝ) * Real.pi * x) *
      (unitIntervalCosineHeatPointWeight t x k * a k) with hF
  -- Pointwise: cos(nπx)·heatValue(x) = ∑'ₖ F k x.
  have hpt : ∀ x : ℝ,
      Real.cos ((n : ℝ) * Real.pi * x) * unitIntervalCosineHeatValue t a x
        = ∑' k, F k x := by
    intro x
    unfold unitIntervalCosineHeatValue
    rw [← tsum_mul_left]
  -- Each summand is continuous, hence integrable on (0,1].
  have hF_cont : ∀ k, Continuous (F k) := by
    intro k
    simp only [hF]
    unfold unitIntervalCosineHeatPointWeight unitIntervalCosineMode
    fun_prop
  have hF_int : ∀ k,
      Integrable (F k) (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    intro k
    exact ((hF_cont k).integrableOn_Icc (μ := volume)).mono_set
      Set.Ioc_subset_Icc_self
  -- Uniform bounds: ‖F k x‖ ≤ e^{−tλₖ}·M.
  have hF_bound : ∀ k x, ‖F k x‖
      ≤ Real.exp (-t * unitIntervalCosineEigenvalue k) * M := by
    intro k x
    simp only [hF, Real.norm_eq_abs]
    unfold unitIntervalCosineHeatPointWeight unitIntervalCosineMode
    calc |Real.cos ((n : ℝ) * Real.pi * x) *
          (Real.exp (-t * unitIntervalCosineEigenvalue k) *
            Real.cos ((k : ℝ) * Real.pi * x) * a k)|
        = |Real.cos ((n : ℝ) * Real.pi * x)| *
          (Real.exp (-t * unitIntervalCosineEigenvalue k) *
            (|Real.cos ((k : ℝ) * Real.pi * x)| * |a k|)) := by
          rw [abs_mul, abs_mul, abs_mul,
            abs_of_pos (Real.exp_pos _)]
          ring
      _ ≤ 1 * (Real.exp (-t * unitIntervalCosineEigenvalue k) * (1 * M)) := by
          refine mul_le_mul (Real.abs_cos_le_one _) ?_ ?_ zero_le_one
          · exact mul_le_mul_of_nonneg_left
              (mul_le_mul (Real.abs_cos_le_one _) (hM k)
                (abs_nonneg _) zero_le_one)
              (Real.exp_pos _).le
          · positivity
      _ = Real.exp (-t * unitIntervalCosineEigenvalue k) * M := by ring
  -- Summability of the integral norms.
  have hF_sum : Summable (fun k =>
      ∫ x, ‖F k x‖ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
    refine Summable.of_nonneg_of_le
      (fun k => integral_nonneg fun x => norm_nonneg _) ?_
      ((expEigSummable ht).mul_right M)
    intro k
    calc (∫ x, ‖F k x‖ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)))
        ≤ ∫ _x, Real.exp (-t * unitIntervalCosineEigenvalue k) * M
            ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
          apply integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun x => norm_nonneg _)
            (integrable_const _)
          exact Filter.Eventually.of_forall fun x => hF_bound k x
      _ = (Real.exp (-t * unitIntervalCosineEigenvalue k) * M) *
            (volume.restrict (Set.Ioc (0 : ℝ) 1) Set.univ).toReal := by
          rw [integral_const, smul_eq_mul, MeasureTheory.measureReal_def]
          ring
      _ = Real.exp (-t * unitIntervalCosineEigenvalue k) * M := by
          rw [Measure.restrict_apply_univ, Real.volume_Ioc]
          norm_num
  -- The ∫/∑' interchange.
  have hswap :=
    MeasureTheory.integral_tsum_of_summable_integral_norm hF_int hF_sum
  -- Rewrite the interval integral through the interchange.
  have hIoc : (∫ x in (0 : ℝ)..1,
        Real.cos ((n : ℝ) * Real.pi * x) * unitIntervalCosineHeatValue t a x)
      = ∑' k, ∫ x, F k x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    have h1 : (∫ x in Set.Ioc (0:ℝ) 1,
          Real.cos ((n : ℝ) * Real.pi * x) *
            unitIntervalCosineHeatValue t a x ∂volume)
        = ∫ x, (∑' k, F k x) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => hpt x)
    rw [h1, ← hswap]
  rw [hIoc]
  -- Each term is a scaled orthogonality integral.
  have hterm : ∀ k, (∫ x, F k x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)))
      = (Real.exp (-t * unitIntervalCosineEigenvalue k) * a k) *
        ∫ x in (0 : ℝ)..1,
          ShenWork.CosineSpectrum.cosineMode n x *
            ShenWork.CosineSpectrum.cosineMode k x := by
    intro k
    rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _hx
    simp only [hF, ShenWork.CosineSpectrum.cosineMode]
    unfold unitIntervalCosineHeatPointWeight unitIntervalCosineMode
    ring
  -- Only the k = n term survives.
  have hsingle : (∑' k, ∫ x, F k x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)))
      = ∫ x, F n x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    apply tsum_eq_single
    intro k hk
    rw [hterm k, ShenWork.CosineSpectrum.cosineMode_orthogonal
      (Ne.symm hk), mul_zero]
  rw [hsingle, hterm n]
  -- Evaluate the self-integral and the normalisation factor.
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [ShenWork.CosineSpectrum.cosineMode_self_integral_zero]
    norm_num
  · have hne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
    rw [ShenWork.CosineSpectrum.cosineMode_self_integral_of_ne_zero hne,
      if_neg hne]
    ring

/-! ## Semigroup action on coefficients -/

/-- **Spectral action of the propagator on cosine coefficients**:
`(S(t)f)^ₙ = e^{−tλₙ}·f̂ₙ` for continuous `f` with bounded coefficients. -/
theorem cosineCoeffs_semigroup
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ}
    (hM : ∀ n, |cosineCoeffs f n| ≤ M) (n : ℕ) :
    cosineCoeffs (fun y => intervalFullSemigroupOperator t f y) n
      = Real.exp (-t * unitIntervalCosineEigenvalue n) * cosineCoeffs f n := by
  have hcongr : cosineCoeffs (fun y => intervalFullSemigroupOperator t f y) n
      = cosineCoeffs
          (fun y => unitIntervalCosineHeatValue t (cosineCoeffs f) y) n :=
    cosineCoeffs_congr_on_Icc
      (fun y hy => intervalFullSemigroupOperator_eq_cosineHeatValue_Icc
        ht hf hM hy) n
  rw [hcongr]
  exact cosineCoeffs_unitIntervalCosineHeatValue ht hM n

/-- The propagated coefficients keep the same uniform bound. -/
theorem cosineCoeffs_semigroup_abs_le
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ}
    (hM : ∀ n, |cosineCoeffs f n| ≤ M) (n : ℕ) :
    |cosineCoeffs (fun y => intervalFullSemigroupOperator t f y) n| ≤ M := by
  rw [cosineCoeffs_semigroup ht hf hM n, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  have hexp : Real.exp (-t * unitIntervalCosineEigenvalue n) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have h1 : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue; positivity
    have h2 : 0 ≤ t * unitIntervalCosineEigenvalue n := mul_nonneg ht.le h1
    linarith
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  calc Real.exp (-t * unitIntervalCosineEigenvalue n) * |cosineCoeffs f n|
      ≤ 1 * M := mul_le_mul hexp (hM n) (abs_nonneg _) zero_le_one
    _ = M := one_mul M

/-! ## The heat-value exponential reindexing -/

/-- Heat flow at time `s` applied to `e^{−tλ}`-damped coefficients is heat
flow at time `s + t`. -/
theorem unitIntervalCosineHeatValue_exp_damped (s t : ℝ) (a : ℕ → ℝ) (x : ℝ) :
    unitIntervalCosineHeatValue s
        (fun n => Real.exp (-t * unitIntervalCosineEigenvalue n) * a n) x
      = unitIntervalCosineHeatValue (s + t) a x := by
  unfold unitIntervalCosineHeatValue unitIntervalCosineHeatPointWeight
  apply tsum_congr
  intro n
  have hexp : Real.exp (-s * unitIntervalCosineEigenvalue n) *
      Real.exp (-t * unitIntervalCosineEigenvalue n)
      = Real.exp (-(s + t) * unitIntervalCosineEigenvalue n) := by
    rw [← Real.exp_add]; congr 1; ring
  calc Real.exp (-s * unitIntervalCosineEigenvalue n) *
        unitIntervalCosineMode n x *
        (Real.exp (-t * unitIntervalCosineEigenvalue n) * a n)
      = (Real.exp (-s * unitIntervalCosineEigenvalue n) *
          Real.exp (-t * unitIntervalCosineEigenvalue n)) *
        (unitIntervalCosineMode n x * a n) := by ring
    _ = Real.exp (-(s + t) * unitIntervalCosineEigenvalue n) *
        (unitIntervalCosineMode n x * a n) := by rw [hexp]
    _ = Real.exp (-(s + t) * unitIntervalCosineEigenvalue n) *
        unitIntervalCosineMode n x * a n := by ring

/-! ## The composition law -/

/-- **Chapman–Kolmogorov composition for the full Neumann propagator**:
`S(s)(S(t)f)(x) = S(s+t)f(x)` on `[0,1]`, for `s, t > 0` and continuous
`f` with bounded cosine coefficients. -/
theorem intervalFullSemigroupOperator_comp
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ}
    (hM : ∀ n, |cosineCoeffs f n| ≤ M)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    intervalFullSemigroupOperator s
        (fun y => intervalFullSemigroupOperator t f y) x
      = intervalFullSemigroupOperator (s + t) f x := by
  have hg_cont : Continuous (fun y => intervalFullSemigroupOperator t f y) :=
    (intervalFullSemigroupOperator_contDiff_two_clean ht hf hM).continuous
  have hg_bound : ∀ n,
      |cosineCoeffs (fun y => intervalFullSemigroupOperator t f y) n| ≤ M :=
    cosineCoeffs_semigroup_abs_le ht hf hM
  calc intervalFullSemigroupOperator s
        (fun y => intervalFullSemigroupOperator t f y) x
      = unitIntervalCosineHeatValue s
          (cosineCoeffs (fun y => intervalFullSemigroupOperator t f y)) x :=
        intervalFullSemigroupOperator_eq_cosineHeatValue_Icc hs hg_cont
          hg_bound hx
    _ = unitIntervalCosineHeatValue s
          (fun n => Real.exp (-t * unitIntervalCosineEigenvalue n) *
            cosineCoeffs f n) x := by
        unfold unitIntervalCosineHeatValue
        apply tsum_congr
        intro n
        rw [cosineCoeffs_semigroup ht hf hM n]
    _ = unitIntervalCosineHeatValue (s + t) (cosineCoeffs f) x :=
        unitIntervalCosineHeatValue_exp_damped s t (cosineCoeffs f) x
    _ = intervalFullSemigroupOperator (s + t) f x :=
        (intervalFullSemigroupOperator_eq_cosineHeatValue_Icc
          (by linarith) hf hM hx).symm

end ShenWork.IntervalSemigroupComposition
