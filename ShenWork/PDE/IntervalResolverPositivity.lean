/-
  ShenWork/PDE/IntervalResolverPositivity.lean

  T7 existence — **O1: resolver positivity** `R(u) ≥ 0` for `u ≥ 0`, the only
  obstruction left for the weak mild fixed point (the flux denominator
  `(1+R)^β ≥ 1` and the `hv_nonneg` conjunct both need it).  It is NOT reachable
  via the elliptic maximum principle for weak ball elements (the `R''` /
  elliptic-identity tools all need `SourceCoeffQuadraticDecay` = source `C²`,
  which an ℓ²-only weak element lacks).  Route: the positivity-preserving
  heat-Laplace representation
  `R(u) = ∫₀^∞ e^{−μt} S(t)(ν u^γ) dt` via a FINITE truncation `R_T` + a
  spectral T→∞ limit + the closed cone `Ici 0`.

  **Route correction (vs the original O1 sketch):** the sketch used the
  zeroth-reflection `intervalSemigroupOperator`, but that two-term kernel is only
  a small-`t` TRUNCATION of the Neumann kernel — it does NOT have the cosine
  spectral form `∑ e^{−tλₖ} âₖ cos` (see `IntervalSemigroupSpectralForm` header),
  so its per-mode Laplace coefficients would NOT match the resolver
  `âₖ/(μ+λₖ)`.  The correct operator is the FULL Neumann propagator
  `intervalFullSemigroupOperator`, which has BOTH: nonnegativity
  (`intervalNeumannFullKernel_nonneg`) AND the cosine spectral identity
  (`intervalFullSemigroupOperator_eq_cosineHeatValue`).

  This file starts with the full-propagator positivity (O1a).

  No `sorry`, no `admit`, no custom `axiom`.  We never assume
  `SourceCoeffQuadraticDecay` / `R''` / `chemDiv` in the weak ball.
-/
import ShenWork.PDE.IntervalFullKernelSupBound
import ShenWork.PDE.IntervalFullKernelInterchange
import ShenWork.PDE.IntervalDuhamelSpectralC2
import ShenWork.PDE.IntervalNeumannEllipticResolverR

open MeasureTheory intervalIntegral
open ShenWork.IntervalDomain (intervalMeasure)
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalFullKernelInterchange
open ShenWork.IntervalDuhamelSpectralC2 (intervalExpKernel_time_integral)

noncomputable section

namespace ShenWork.IntervalResolverPositivity

/-- **O1a — full Neumann propagator preserves positivity.**  `S(t)f ≥ 0` for
`f ≥ 0` (`t > 0`): the full Neumann kernel is nonnegative
(`intervalNeumannFullKernel_nonneg`), so the kernel integral of a nonnegative
source is nonnegative.  (Full-kernel analogue of the zeroth-reflection
`intervalSemigroupOperator_nonneg`.) -/
theorem intervalFullSemigroupOperator_nonneg {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf : ∀ y, 0 ≤ f y) (x : ℝ) :
    0 ≤ intervalFullSemigroupOperator t f x := by
  unfold intervalFullSemigroupOperator
  apply MeasureTheory.integral_nonneg
  intro y
  exact mul_nonneg (intervalNeumannFullKernel_nonneg ht x y) (hf y)

/-! ## O1b — discharging the kernel↔theta identity `hkernel` from `t > 0`

The spectral identity `intervalFullSemigroupOperator t f x =
unitIntervalCosineHeatValue t (cosineCoeffs f) x` needs the pointwise kernel
identity `hkernel : K t x y = ∑ₘ e^{−t(mπ)²}cos(mπx)cos(mπy)`, carried as a
hypothesis throughout the repo.  Here we discharge it from `t > 0`: the two
Gaussian-lattice summabilities are `latticeGaussianSummable`, and the spectral
summability `∑ₘ e^{−t(mπ)²} < ∞` is `latticeExpSummable` at `z = 0`,
`s = 1/(tπ²)` (then `exp(−(2k)²/(4s)) = exp(−t(kπ)²)`). -/

/-- The spectral exponential sum `∑_{m∈ℤ} e^{−t(mπ)²}` is summable (`t > 0`):
`latticeExpSummable` at `z = 0`, `s = 1/(tπ²)`. -/
theorem summable_spectral_exp {t : ℝ} (ht : 0 < t) :
    Summable (fun m : ℤ => Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2)) := by
  have hs : (0 : ℝ) < 1 / (t * Real.pi ^ 2) := by positivity
  refine (latticeExpSummable hs 0).congr (fun k => ?_)
  congr 1
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp
  ring

/-- The cosine-weighted spectral sum `∑_{m∈ℤ} e^{−t(mπ)²}cos(mπz)` is summable,
by comparison with `∑ e^{−t(mπ)²}` (`|cos| ≤ 1`). -/
theorem summable_spectral_exp_cos {t : ℝ} (ht : 0 < t) (z : ℝ) :
    Summable (fun m : ℤ => Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2)
      * Real.cos ((m : ℝ) * Real.pi * z)) := by
  refine (summable_spectral_exp ht).of_norm_bounded (fun m => ?_)
  rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
  calc Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) * |Real.cos ((m : ℝ) * Real.pi * z)|
      ≤ Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_nonneg _)
    _ = Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) := mul_one _

/-- **O1b gateway — the kernel↔theta identity, unconditional for `t > 0`.**
Discharges `hkernel` (`intervalNeumannFullKernel_eq_cosineKernel` with the three
summabilities supplied from `t > 0`). -/
theorem intervalNeumannFullKernel_cosineKernel_identity {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    intervalNeumannFullKernel t x y =
      ∑' m : ℤ, Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) *
        (Real.cos ((m : ℝ) * Real.pi * x) * Real.cos ((m : ℝ) * Real.pi * y)) :=
  intervalNeumannFullKernel_eq_cosineKernel t ht x y
    (latticeGaussianSummable ht (x - y)) (latticeGaussianSummable ht (x + y))
    ⟨summable_spectral_exp_cos ht (x - y), summable_spectral_exp_cos ht (x + y)⟩

/-- **O1b — the cosine spectral heat value of a nonnegative continuous source is
nonnegative** on the open interior.  Transports the kernel-side positivity (O1a)
across the now-unconditional spectral identity. -/
theorem unitIntervalCosineHeatValue_nonneg_of_continuous {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf_cont : Continuous f) (hf_nonneg : ∀ y, 0 ≤ f y)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    0 ≤ unitIntervalCosineHeatValue t (cosineCoeffs f) x := by
  rw [← intervalFullSemigroupOperator_eq_cosineHeatValue_unconditional t ht f hf_cont x hx
        (fun y => intervalNeumannFullKernel_cosineKernel_identity ht x y)]
  exact intervalFullSemigroupOperator_nonneg ht hf_nonneg x

/-! ## O1c — the heat-Laplace truncation `R_T` and its nonnegativity -/

/-- **Per-mode Laplace integral.**  `∫₀ᵀ e^{−aτ} dτ = (1−e^{−aT})/a` (`a ≠ 0`):
the `τ = T−s` reflection of the proven `intervalExpKernel_time_integral`. -/
theorem integral_exp_neg_mul {a T : ℝ} (ha : a ≠ 0) :
    (∫ τ in (0:ℝ)..T, Real.exp (-a * τ)) = (1 - Real.exp (-a * T)) / a := by
  have key : ∀ τ : ℝ,
      HasDerivAt (fun τ : ℝ => -Real.exp (-a * τ) / a) (Real.exp (-a * τ)) τ := by
    intro τ
    have hinner : HasDerivAt (fun τ : ℝ => -a * τ) (-a) τ := by
      simpa using (hasDerivAt_id τ).const_mul (-a)
    have hd := ((hinner.exp).neg).div_const a
    convert hd using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ => key τ)
      ((Real.continuous_exp.comp (by fun_prop)).intervalIntegrable 0 T)]
  simp only [mul_zero, Real.exp_zero]
  field_simp
  ring

/-- **The heat-Laplace truncation.**  `R_T(f)(x) = ∫₀ᵀ e^{−μt} S(t)f x dt`, the
finite-`T` truncation of the resolvent Laplace representation
`R(f) = ∫₀^∞ e^{−μt} S(t)f dt`.  (Defined via the FULL propagator
`intervalFullSemigroupOperator`, which carries both positivity and the cosine
spectral form.) -/
def laplaceTruncation (μ T : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..T, Real.exp (-μ * t) * intervalFullSemigroupOperator t f x

/-- **O1c (step 1) — `R_T ≥ 0`.**  For a nonnegative source `f ≥ 0` and `0 ≤ T`,
the truncation is nonnegative: the integrand `e^{−μt}·S(t)f x ≥ 0` for `t > 0`
(`Real.exp_nonneg` × O1a `intervalFullSemigroupOperator_nonneg`); the endpoint
`t = 0` is null. -/
theorem laplaceTruncation_nonneg {μ T : ℝ} (hT : 0 ≤ T) {f : ℝ → ℝ}
    (hf : ∀ y, 0 ≤ f y) (x : ℝ) : 0 ≤ laplaceTruncation μ T f x := by
  refine intervalIntegral.integral_nonneg_of_ae_restrict hT ?_
  have hne : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
  refine (ae_restrict_iff' measurableSet_Icc).mpr ?_
  filter_upwards [hne] with t ht_ne ht_mem
  have ht0 : 0 < t := lt_of_le_of_ne ht_mem.1 (Ne.symm ht_ne)
  exact mul_nonneg (Real.exp_nonneg _) (intervalFullSemigroupOperator_nonneg ht0 hf x)

/-! ## O1c step 2 / O1d — spectral limit (foundation) -/

open ShenWork.PDE in
/-- **ℓ¹ majorant.**  `∑ₙ |âₙ|/(μ+λₙ) < ∞` from `â ∈ ℓ²` and the resolvent weight
`1/(μ+λₙ) ∈ ℓ²` (`intervalNeumannResolverWeight_sq_summable`), via AM-GM
`|âₙ|·wₙ ≤ (âₙ²+wₙ²)/2`.  This is the dominating series both for the Fubini
interchange `∑ₙ ∫₀ᵀ|·|` and for the `T→∞` dominated-convergence limit. -/
theorem summable_abs_sourceCoeff_mul_weight {p : CM2Params} {â : ℕ → ℝ}
    (hâ : Summable (fun n => (â n) ^ 2)) :
    Summable (fun n => |â n| * intervalNeumannResolverWeight p n) := by
  have hw := intervalNeumannResolverWeight_sq_summable p
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    ((hâ.add hw).div_const 2)
  · refine mul_nonneg (abs_nonneg _) ?_
    rw [intervalNeumannResolverWeight]
    exact le_of_lt (one_div_pos.mpr (intervalNeumannResolver_denom_pos p n))
  · have h := two_mul_le_add_sq |â n| (intervalNeumannResolverWeight p n)
    rw [sq_abs] at h
    nlinarith [h]

end ShenWork.IntervalResolverPositivity
