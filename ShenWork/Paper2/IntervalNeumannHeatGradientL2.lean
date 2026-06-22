/-
# L²-restricted Neumann heat-gradient smoothing on the unit interval

Proves `NeumannHeatGradientTMinusHalfBound` (the `MemLp f 2`-restricted form, fixed
at `IntervalBFormCron2SemigroupWeakDuhamel`):

  `∃ C ≥ 0, ∀ τ > 0, ∀ f, MemLp f 2 μ →`
  `   √(∫ (∂ₓ S_N(τ)f)² ∂μ) ≤ C · τ^{-1/2} · √(∫ f² ∂μ)`,    `μ = intervalMeasure 1`.

The witness is `C = 1`.  Spectral chain (all landed except the sine-output Parseval,
built here as `unitInterval_sineSeries_l2_sq_of_absSummable`):

* operator → cosine model (for `Integrable` input, via the L¹-dominated interchange);
* `∂ₓ S_N(τ)f = Σ_{n} gradAmp τ (cosineCoeffs f) n · sin(nπx)`;
* sine-output Parseval: `∫₀¹ (Σ bₙ sin(nπx))² = ½ Σ bₙ²`;
* `gradAmp² = (nπ)²e^{-2τλₙ}·cₙ² = multiplierₙ·cₙ²`, and the landed scalar bound
  `Σ multiplierₙ cₙ² ≤ (1/(2τ)) Σ cₙ²`;
* cosine Bessel `Σ cₙ² ≤ 4 ∫₀¹ f²` (from `MemLp f 2`);
* assembling: `∫ (∂ₓS)² = ½ Σ gradAmp² ≤ ½·(1/(2τ))·4·∫f² = τ⁻¹ ∫f²`, then
  `√(τ⁻¹ A) = τ^{-1/2} √A`.
-/
import ShenWork.Paper2.IntervalBFormCron2SemigroupWeakDuhamel
import ShenWork.Paper2.IntervalNeumannHeatGradientL2Bricks
import ShenWork.Paper2.IntervalNeumannHeatGradientL2BrickB
import ShenWork.Paper2.IntervalNeumannHeatGradientL2BrickC

open MeasureTheory

noncomputable section

namespace ShenWork.IntervalNeumannHeatGradientL2

open scoped Real
open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator cosineCoeffs)
open ShenWork.HeatKernelGradientEstimates
open ShenWork.Paper2.BFormPositiveDatumNegPart (NeumannHeatGradientTMinusHalfBound)

/-! ## Spectral gradient amplitudes (x-free sine coefficients) -/

/-- The `x`-free amplitude multiplying `sin(nπx)` in the spectral heat gradient. -/
def gradAmp (τ : ℝ) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.exp (-τ * unitIntervalCosineEigenvalue n) *
    (-((n : ℝ) * Real.pi)) * a n

theorem gradAmp_factor (τ x : ℝ) (a : ℕ → ℝ) (n : ℕ) :
    unitIntervalCosineHeatGradientPointWeight τ x n * a n
      = gradAmp τ a n * Real.sin ((n : ℝ) * Real.pi * x) := by
  simp only [unitIntervalCosineHeatGradientPointWeight, gradAmp]; ring

theorem gradAmp_sq (τ : ℝ) (a : ℕ → ℝ) (n : ℕ) :
    (gradAmp τ a n) ^ 2
      = unitIntervalCosineHeatGradientMultiplier τ n * (a n) ^ 2 := by
  simp only [gradAmp, unitIntervalCosineHeatGradientMultiplier,
    unitIntervalCosineEigenvalue]
  rw [show (-2 * τ * ((n : ℝ) * Real.pi) ^ 2)
        = (-τ * ((n : ℝ) * Real.pi) ^ 2) + (-τ * ((n : ℝ) * Real.pi) ^ 2) by ring,
    Real.exp_add]; ring

theorem gradAmp_zero (τ : ℝ) (a : ℕ → ℝ) : gradAmp τ a 0 = 0 := by
  simp [gradAmp]

/-- The spectral gradient value is the sine series with amplitudes `gradAmp`. -/
theorem gradientValue_eq_sineSeries (τ : ℝ) (a : ℕ → ℝ) (x : ℝ) :
    unitIntervalCosineHeatGradientValue τ a x
      = ∑' n : ℕ, gradAmp τ a n * Real.sin ((n : ℝ) * Real.pi * x) := by
  simp only [unitIntervalCosineHeatGradientValue]
  exact tsum_congr (fun n => gradAmp_factor τ x a n)

/-! ## Brick C: sine-output Parseval (filled below / external) -/

/-- **Sine-output Parseval** on the unit interval.  `∫₀¹ (Σ bₙ sin(nπx))² = ½ Σ bₙ²`,
for `ℓ¹` (hence pointwise-convergent) and `ℓ²` amplitudes with `b₀ = 0`. -/
theorem unitInterval_sineSeries_l2_sq_of_absSummable
    {b : ℕ → ℝ} (hb0 : b 0 = 0)
    (hb_abs : Summable fun n => ‖b n‖) (hb_sq : Summable fun n => (b n) ^ 2) :
    (∫ x, (∑' n : ℕ, b n * Real.sin ((n : ℝ) * Real.pi * x)) ^ 2
        ∂ intervalMeasure 1)
      = (1 / 2 : ℝ) * ∑' n : ℕ, (b n) ^ 2 := by
  have hbrick := ShenWork.IntervalNHGBrickC.sineSeries_l2_sq hb0 hb_abs hb_sq
  rw [← hbrick]
  -- ∫ ... ∂(intervalMeasure 1) = ∫₀¹ (gR b x)²
  rw [intervalMeasure, intervalSet,
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    MeasureTheory.integral_Icc_eq_integral_Ioc]
  rfl

/-! ## Brick A: operator → cosine model for integrable input (filled below / external) -/

theorem operator_eq_cosineModel_of_integrable
    {τ : ℝ} (hτ : 0 < τ) {f : ℝ → ℝ}
    (hf : Integrable f (intervalMeasure 1)) {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    intervalFullSemigroupOperator τ f x
      = unitIntervalCosineHeatValue τ (cosineCoeffs f) x :=
  ShenWork.IntervalNHGBricks.operator_eq_cosineModel_of_integrable hτ hf hx

/-! ## Brick B: cosine-coefficient `ℓ²` and Bessel bound from `MemLp f 2` -/

/-- From `MemLp f 2 (intervalMeasure 1)`, the Neumann cosine coefficients are `ℓ²`
and obey the Bessel bound `√(Σ cₙ²) ≤ 2·√(∫₀¹ f²)`. -/
theorem cosineCoeffs_l2_of_memLp
    {f : ℝ → ℝ} (hf : MemLp f 2 (intervalMeasure 1)) :
    Summable (fun n => (cosineCoeffs f n) ^ 2) ∧
      Real.sqrt (∑' n, (cosineCoeffs f n) ^ 2)
        ≤ 2 * Real.sqrt (∫ x in (0 : ℝ)..1, (f x) ^ 2) :=
  ShenWork.IntervalNHGBrickB.cosineCoeffs_l2_of_memLp hf

/-! ## Spectral energy identity -/

/-- `∫₀¹ (∂ₓ S_N(τ)f)² = ½ Σ gradAmp² = ½ Σ multiplierₙ cₙ²`, for `ℓ¹`+`ℓ²` coeffs. -/
theorem gradientValue_energy_eq
    {τ : ℝ} (hτ : 0 < τ) {a : ℕ → ℝ}
    (ha_abs : Summable fun n => ‖gradAmp τ a n‖)
    (ha_sq : Summable fun n => (gradAmp τ a n) ^ 2) :
    (∫ x, (unitIntervalCosineHeatGradientValue τ a x) ^ 2 ∂ intervalMeasure 1)
      = (1 / 2 : ℝ) *
          ∑' n, unitIntervalCosineHeatGradientMultiplier τ n * (a n) ^ 2 := by
  have hser : (fun x => (unitIntervalCosineHeatGradientValue τ a x) ^ 2)
      = fun x => (∑' n : ℕ, gradAmp τ a n * Real.sin ((n : ℝ) * Real.pi * x)) ^ 2 := by
    funext x; rw [gradientValue_eq_sineSeries τ a x]
  rw [show (∫ x, (unitIntervalCosineHeatGradientValue τ a x) ^ 2 ∂ intervalMeasure 1)
        = ∫ x, (∑' n : ℕ, gradAmp τ a n * Real.sin ((n : ℝ) * Real.pi * x)) ^ 2
            ∂ intervalMeasure 1 from by rw [hser]]
  rw [unitInterval_sineSeries_l2_sq_of_absSummable (gradAmp_zero τ a) ha_abs ha_sq]
  congr 1
  exact tsum_congr (fun n => gradAmp_sq τ a n)

/-! ## ℓ¹ damping of the gradient amplitudes -/

/-- Gaussian damping makes `gradAmp` absolutely summable whenever the coefficients
are bounded (e.g. `ℓ²`-summable). -/
theorem gradAmp_absSummable
    {τ : ℝ} (hτ : 0 < τ) {a : ℕ → ℝ}
    (ha_sq : Summable fun n => (a n) ^ 2) :
    Summable fun n => ‖gradAmp τ a n‖ := by
  -- u n = exp(-τλₙ)·(nπ);  (u n)² = multiplierₙ (summable);  ‖gradAmp‖ = |u n · a n|.
  set u : ℕ → ℝ := fun n =>
    Real.exp (-τ * unitIntervalCosineEigenvalue n) * ((n : ℝ) * Real.pi) with hu
  have hu_sq : Summable fun n => (u n) ^ 2 := by
    have htrace := unitIntervalCosineHeatGradientTrace_summable hτ
      unitIntervalCosineReciprocalEigenvalueTerm_summable
    refine htrace.congr (fun n => ?_)
    simp only [hu, unitIntervalCosineHeatGradientMultiplier, unitIntervalCosineEigenvalue]
    rw [show (-2 * τ * ((n : ℝ) * Real.pi) ^ 2)
          = (-τ * ((n : ℝ) * Real.pi) ^ 2) + (-τ * ((n : ℝ) * Real.pi) ^ 2) by ring,
      Real.exp_add]
    ring
  have hcs := real_summable_abs_mul_of_summable_sq hu_sq ha_sq
  refine hcs.congr (fun n => ?_)
  simp only [hu, gradAmp, Real.norm_eq_abs]
  rw [show Real.exp (-τ * unitIntervalCosineEigenvalue n) * (-((n : ℝ) * Real.pi)) * a n
        = -(Real.exp (-τ * unitIntervalCosineEigenvalue n) * ((n : ℝ) * Real.pi) * a n) by ring,
    abs_neg]

/-! ## Main theorem -/

theorem neumannHeatGradientTMinusHalfBound_proof :
    NeumannHeatGradientTMinusHalfBound := by
  refine ⟨1, by norm_num, ?_⟩
  intro τ hτ f hf
  -- cosine coefficients are ℓ²
  obtain ⟨ha_sq, hbessel⟩ := cosineCoeffs_l2_of_memLp hf
  -- f integrable
  have hf_int : Integrable f (intervalMeasure 1) :=
    (memLp_one_iff_integrable.1 (hf.mono_exponent (by norm_num)))
  -- amplitudes ℓ¹ and ℓ²
  have hamp_abs : Summable fun n => ‖gradAmp τ (cosineCoeffs f) n‖ :=
    gradAmp_absSummable hτ ha_sq
  have hmult_nonneg : ∀ n, 0 ≤ unitIntervalCosineHeatGradientMultiplier τ n := by
    intro n
    simp only [unitIntervalCosineHeatGradientMultiplier, unitIntervalCosineEigenvalue]
    positivity
  have hamp_sq : Summable fun n => (gradAmp τ (cosineCoeffs f) n) ^ 2 := by
    refine (ha_sq.mul_left (1 / (2 * τ))).of_nonneg_of_le
      (fun n => sq_nonneg _) ?_
    intro n
    rw [gradAmp_sq]
    exact mul_le_mul_of_nonneg_right
      (unitIntervalCosineHeatGradientMultiplier_le hτ n) (sq_nonneg _)
  -- the operator derivative equals the spectral gradient a.e. on [0,1]
  have hderiv_ae :
      (fun x => deriv (fun z : ℝ => intervalFullSemigroupOperator τ f z) x)
        =ᵐ[intervalMeasure 1]
      (fun x => unitIntervalCosineHeatGradientValue τ (cosineCoeffs f) x) := by
    -- operator = cosine model on the open Ioo 0 1 (Brick A)
    have heqOn : Set.EqOn (fun z : ℝ => intervalFullSemigroupOperator τ f z)
        (fun z : ℝ => unitIntervalCosineHeatValue τ (cosineCoeffs f) z)
        (Set.Ioo (0 : ℝ) 1) := fun y hy => operator_eq_cosineModel_of_integrable hτ hf_int hy
    -- a.e. x ∈ Ioo 0 1, the two derivatives agree and equal the spectral gradient
    have hae_mem : ∀ᵐ x ∂ intervalMeasure 1, x ∈ Set.Ioo (0 : ℝ) 1 := by
      rw [intervalMeasure, intervalSet, ae_iff, Measure.restrict_apply' measurableSet_Icc]
      refine measure_mono_null (t := ({0, 1} : Set ℝ)) (fun x hx => ?_) ?_
      · simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Icc] at hx
        obtain ⟨hnot, h0, h1⟩ := hx
        rcases eq_or_lt_of_le h0 with he0 | hl0
        · left; exact he0.symm
        · rcases eq_or_lt_of_le h1 with he1 | hl1
          · right; exact he1
          · exact absurd ⟨hl0, hl1⟩ hnot
      · exact Set.Finite.measure_zero ((Set.finite_singleton (1:ℝ)).insert 0) volume
    filter_upwards [hae_mem] with x hx
    have hnhds : Set.Ioo (0 : ℝ) 1 ∈ nhds x := isOpen_Ioo.mem_nhds hx
    have hderiv_eq : deriv (fun z : ℝ => intervalFullSemigroupOperator τ f z) x
        = deriv (fun z : ℝ => unitIntervalCosineHeatValue τ (cosineCoeffs f) z) x :=
      Filter.EventuallyEq.deriv_eq (Filter.eventuallyEq_of_mem hnhds heqOn)
    rw [hderiv_eq]
    exact unitIntervalCosineHeatValue_deriv_of_l2 hτ
      unitIntervalCosineReciprocalEigenvalueTerm_summable ha_sq
  -- rewrite the gradient L² integral
  have hLHS :
      (∫ x, (deriv (fun z : ℝ => intervalFullSemigroupOperator τ f z) x) ^ 2
          ∂ intervalMeasure 1)
        = ∫ x, (unitIntervalCosineHeatGradientValue τ (cosineCoeffs f) x) ^ 2
            ∂ intervalMeasure 1 := by
    apply integral_congr_ae
    filter_upwards [hderiv_ae] with x hx; rw [hx]
  -- energy identity + scalar bound + Bessel
  rw [hLHS, gradientValue_energy_eq hτ hamp_abs hamp_sq]
  set c := cosineCoeffs f with hc
  set Ic : ℝ := ∫ x in (0 : ℝ)..1, (f x) ^ 2 with hIc
  have hIc_nonneg : 0 ≤ Ic := by
    rw [hIc]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun x _ => sq_nonneg _)
  -- interval integral equals the measure integral
  have hIc_eq : Ic = ∫ x, (f x) ^ 2 ∂ intervalMeasure 1 := by
    rw [hIc, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      intervalMeasure, intervalSet, MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hcoeff_sum_nonneg : 0 ≤ ∑' n, (c n) ^ 2 :=
    tsum_nonneg (fun n => sq_nonneg _)
  -- Bessel: Σ cₙ² ≤ 4 Ic
  have hbessel_sq : ∑' n, (c n) ^ 2 ≤ 4 * Ic := by
    have h2 := hbessel
    have hsq := mul_self_le_mul_self (Real.sqrt_nonneg _) h2
    rw [Real.mul_self_sqrt hcoeff_sum_nonneg] at hsq
    calc ∑' n, (c n) ^ 2 ≤ (2 * Real.sqrt Ic) * (2 * Real.sqrt Ic) := hsq
      _ = 4 * (Real.sqrt Ic * Real.sqrt Ic) := by ring
      _ = 4 * Ic := by rw [Real.mul_self_sqrt hIc_nonneg]
  -- scalar bound: Σ mult·cₙ² ≤ (1/(2τ)) Σ cₙ²
  have hscalar : (∑' n, unitIntervalCosineHeatGradientMultiplier τ n * (c n) ^ 2)
      ≤ (1 / (2 * τ)) * ∑' n, (c n) ^ 2 :=
    unitIntervalCosineHeatGradientTsumEnergy_le hτ ha_sq
  -- combine to bound the energy by τ⁻¹ · Ic
  have henergy_le :
      (1 / 2 : ℝ) * ∑' n, unitIntervalCosineHeatGradientMultiplier τ n * (c n) ^ 2
        ≤ τ⁻¹ * Ic := by
    have hstep : (1 / 2 : ℝ) * ∑' n, unitIntervalCosineHeatGradientMultiplier τ n * (c n) ^ 2
        ≤ (1 / 2 : ℝ) * ((1 / (2 * τ)) * (4 * Ic)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact hscalar.trans (mul_le_mul_of_nonneg_left hbessel_sq (by positivity))
    refine hstep.trans (le_of_eq ?_)
    field_simp
    ring
  -- finish: √(½ Σ …) ≤ √(τ⁻¹ Ic) = τ^{-1/2} √(Ic)
  calc Real.sqrt ((1 / 2 : ℝ) *
          ∑' n, unitIntervalCosineHeatGradientMultiplier τ n * (c n) ^ 2)
      ≤ Real.sqrt (τ⁻¹ * Ic) := Real.sqrt_le_sqrt henergy_le
    _ = Real.sqrt (τ⁻¹) * Real.sqrt Ic := Real.sqrt_mul (by positivity) _
    _ = τ ^ (-(1 / 2 : ℝ)) * Real.sqrt Ic := by
        congr 1
        rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one τ, ← Real.rpow_mul hτ.le]
        norm_num
    _ = 1 * τ ^ (-(1 / 2 : ℝ)) *
          Real.sqrt (∫ x, (f x) ^ 2 ∂ intervalMeasure 1) := by
        rw [hIc_eq, one_mul]

end ShenWork.IntervalNeumannHeatGradientL2
