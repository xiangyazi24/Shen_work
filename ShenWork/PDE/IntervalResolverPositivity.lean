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
open ShenWork.PDE (intervalNeumannResolverWeight intervalNeumannResolverWeight_sq_summable
  intervalNeumannResolver_denom_pos)
open ShenWork.Paper3 (unitIntervalNeumannSpectrum)

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

/-- The `k`-th Laplace-mode integrand `gₖ(t) = e^{−μt}·(e^{−tλₖ}cos(kπx))·âₖ
= e^{−(μ+λₖ)t}·cos(kπx)·âₖ`. -/
def laplaceMode (μ : ℝ) (â : ℕ → ℝ) (x : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  Real.exp (-μ * t) * (unitIntervalCosineHeatPointWeight t x k * â k)

/-- Each Laplace mode is continuous in `t`. -/
theorem laplaceMode_continuous (μ : ℝ) (â : ℕ → ℝ) (x : ℝ) (k : ℕ) :
    Continuous (laplaceMode μ â x k) := by
  unfold laplaceMode unitIntervalCosineHeatPointWeight
  fun_prop

/-- Closed form `gₖ(t) = (âₖ·cos(kπx))·e^{−(μ+λₖ)t}`. -/
theorem laplaceMode_eq (μ : ℝ) (â : ℕ → ℝ) (x : ℝ) (k : ℕ) (t : ℝ) :
    laplaceMode μ â x k t
      = (â k * unitIntervalCosineMode k x)
        * Real.exp (-(μ + unitIntervalCosineEigenvalue k) * t) := by
  unfold laplaceMode unitIntervalCosineHeatPointWeight unitIntervalCosineMode
  rw [show -(μ + unitIntervalCosineEigenvalue k) * t
      = (-μ * t) + (-t * unitIntervalCosineEigenvalue k) from by ring, Real.exp_add]
  ring

/-- Per-mode integral `∫₀ᵀ gₖ = âₖ·cos(kπx)·(1−e^{−(μ+λₖ)T})/(μ+λₖ)`. -/
theorem integral_laplaceMode {p : CM2Params} {â : ℕ → ℝ} {x T : ℝ} (k : ℕ) :
    (∫ t in (0:ℝ)..T, laplaceMode p.μ â x k t)
      = â k * unitIntervalCosineMode k x
          * ((1 - Real.exp (-(p.μ + unitIntervalCosineEigenvalue k) * T))
              / (p.μ + unitIntervalCosineEigenvalue k)) := by
  have hne : p.μ + unitIntervalCosineEigenvalue k ≠ 0 := by
    have : 0 < p.μ + unitIntervalCosineEigenvalue k := by
      have : 0 ≤ unitIntervalCosineEigenvalue k := by
        unfold unitIntervalCosineEigenvalue; positivity
      linarith [p.hμ]
    exact ne_of_gt this
  rw [intervalIntegral.integral_congr (fun t _ => laplaceMode_eq p.μ â x k t),
    intervalIntegral.integral_const_mul, integral_exp_neg_mul hne]

/-- **O1c step 2 — Fubini spectral form of the Laplace truncation.**  For
`â ∈ ℓ²` and `0 ≤ T`, `∫₀ᵀ e^{−μt}·(heat value t â x) dt = ∑ₖ âₖ cos(kπx)·
(1−e^{−(μ+λₖ)T})/(μ+λₖ)`.  The `∑∫=∫∑` swap is `integral_tsum_of_summable_integral_norm`,
dominated by the ℓ¹ majorant `∑ₖ|âₖ|/(μ+λₖ)`. -/
theorem laplaceResolverTrunc_eq_tsum {p : CM2Params} {â : ℕ → ℝ}
    (hâ : Summable (fun n => (â n) ^ 2)) {x T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0:ℝ)..T, Real.exp (-p.μ * t) * unitIntervalCosineHeatValue t â x)
      = ∑' k : ℕ, â k * unitIntervalCosineMode k x
          * ((1 - Real.exp (-(p.μ + unitIntervalCosineEigenvalue k) * T))
              / (p.μ + unitIntervalCosineEigenvalue k)) := by
  have hdpos : ∀ k, (0:ℝ) < p.μ + unitIntervalCosineEigenvalue k := by
    intro k
    have h0 : 0 ≤ unitIntervalCosineEigenvalue k := by
      unfold unitIntervalCosineEigenvalue; positivity
    linarith [p.hμ]
  -- per-mode integrability on `Ioc 0 T`.
  have hF_int : ∀ k, Integrable (laplaceMode p.μ â x k) (volume.restrict (Set.Ioc 0 T)) :=
    fun k => (laplaceMode_continuous p.μ â x k).integrableOn_Ioc
  -- `∫_{Ioc 0 T} ‖gₖ‖ ≤ |âₖ|·weightₖ`, summable.
  have hF_sum : Summable (fun k => ∫ t in Set.Ioc 0 T, ‖laplaceMode p.μ â x k t‖) := by
    refine Summable.of_nonneg_of_le
      (fun k => MeasureTheory.integral_nonneg (fun t => norm_nonneg _)) (fun k => ?_)
      (summable_abs_sourceCoeff_mul_weight (p := p) hâ)
    -- `∫ ‖gₖ‖ = |âₖ·cos|·(1−e^{−(μ+λₖ)T})/(μ+λₖ) ≤ |âₖ|·weightₖ`.
    have hnorm : ∀ t : ℝ, ‖laplaceMode p.μ â x k t‖
        = |â k * unitIntervalCosineMode k x|
          * Real.exp (-(p.μ + unitIntervalCosineEigenvalue k) * t) := by
      intro t
      rw [Real.norm_eq_abs, laplaceMode_eq, abs_mul, Real.abs_exp]
    rw [← intervalIntegral.integral_of_le hT]
    rw [intervalIntegral.integral_congr (fun t _ => hnorm t),
      intervalIntegral.integral_const_mul,
      integral_exp_neg_mul (ne_of_gt (hdpos k))]
    have hcos : |â k * unitIntervalCosineMode k x| ≤ |â k| := by
      rw [abs_mul]
      calc |â k| * |unitIntervalCosineMode k x|
          ≤ |â k| * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            rw [unitIntervalCosineMode]; exact Real.abs_cos_le_one _
        _ = |â k| := mul_one _
    have heig : p.μ + unitIntervalCosineEigenvalue k
        = p.μ + unitIntervalNeumannSpectrum.eigenvalue k := by
      have : unitIntervalCosineEigenvalue k = unitIntervalNeumannSpectrum.eigenvalue k := by
        rw [show unitIntervalNeumannSpectrum.eigenvalue k = (k : ℝ) ^ 2 * Real.pi ^ 2 from rfl,
          unitIntervalCosineEigenvalue]; ring
      rw [this]
    have hexp_le : Real.exp (-(p.μ + unitIntervalCosineEigenvalue k) * T) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [hdpos k, hT])
    have hfac : (1 - Real.exp (-(p.μ + unitIntervalCosineEigenvalue k) * T))
        / (p.μ + unitIntervalCosineEigenvalue k)
        ≤ intervalNeumannResolverWeight p k := by
      rw [intervalNeumannResolverWeight, ← heig, div_eq_mul_inv, one_div]
      exact mul_le_of_le_one_left (inv_nonneg.mpr (hdpos k).le)
        (by linarith [Real.exp_nonneg (-(p.μ + unitIntervalCosineEigenvalue k) * T)])
    have hfac_nn : 0 ≤ (1 - Real.exp (-(p.μ + unitIntervalCosineEigenvalue k) * T))
        / (p.μ + unitIntervalCosineEigenvalue k) :=
      div_nonneg (by linarith [hexp_le]) (hdpos k).le
    exact mul_le_mul hcos hfac hfac_nn (abs_nonneg _)
  -- Fubini.
  have hfub := integral_tsum_of_summable_integral_norm hF_int hF_sum
  have hint_eq : (fun t => Real.exp (-p.μ * t) * unitIntervalCosineHeatValue t â x)
      = (fun t => ∑' k, laplaceMode p.μ â x k t) := by
    funext t
    simp only [unitIntervalCosineHeatValue, laplaceMode]
    rw [← tsum_mul_left]
  rw [intervalIntegral.integral_of_le hT, hint_eq, ← hfub]
  refine tsum_congr (fun k => ?_)
  rw [← intervalIntegral.integral_of_le hT, integral_laplaceMode]

/-- **O1c — the heat-value Laplace truncation is nonnegative** (interior `x`).
`∫₀ᵀ e^{−μt}·(heat value t (cosineCoeffs f) x) dt ≥ 0` for `f ≥ 0` continuous,
`x ∈ (0,1)`, `0 ≤ T` — the integrand is `e^{−μt}·(≥0 by O1b)` for `t > 0`. -/
theorem laplaceHeatTrunc_nonneg {p : CM2Params} {f : ℝ → ℝ} (hf_cont : Continuous f)
    (hf_nonneg : ∀ y, 0 ≤ f y) {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ ∫ t in (0:ℝ)..T,
        Real.exp (-p.μ * t) * unitIntervalCosineHeatValue t (cosineCoeffs f) x := by
  refine intervalIntegral.integral_nonneg_of_ae_restrict hT ?_
  have hne : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by
    rw [ae_iff]; simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
  refine (ae_restrict_iff' measurableSet_Icc).mpr ?_
  filter_upwards [hne] with t ht_ne ht_mem
  have ht0 : 0 < t := lt_of_le_of_ne ht_mem.1 (Ne.symm ht_ne)
  exact mul_nonneg (Real.exp_nonneg _)
    (unitIntervalCosineHeatValue_nonneg_of_continuous ht0 hf_cont hf_nonneg hx)

/-- The `T→∞` spectral limit target `∑ₖ âₖ cos(kπx)/(μ+λₖ)` is summable
(`|·| ≤ |âₖ|·weightₖ`, the ℓ¹ majorant). -/
theorem summable_resolverTarget {p : CM2Params} {â : ℕ → ℝ}
    (hâ : Summable (fun n => (â n) ^ 2)) (x : ℝ) :
    Summable (fun k => â k * unitIntervalCosineMode k x
      / (p.μ + unitIntervalCosineEigenvalue k)) := by
  refine Summable.of_norm_bounded (summable_abs_sourceCoeff_mul_weight (p := p) hâ) (fun k => ?_)
  have hdpos : (0:ℝ) < p.μ + unitIntervalCosineEigenvalue k := by
    have h0 : 0 ≤ unitIntervalCosineEigenvalue k := by
      unfold unitIntervalCosineEigenvalue; positivity
    linarith [p.hμ]
  have heig : intervalNeumannResolverWeight p k = 1 / (p.μ + unitIntervalCosineEigenvalue k) := by
    rw [intervalNeumannResolverWeight]
    congr 2
    rw [show unitIntervalNeumannSpectrum.eigenvalue k = (k : ℝ) ^ 2 * Real.pi ^ 2 from rfl,
      unitIntervalCosineEigenvalue]; ring
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hdpos, heig]
  rw [div_eq_mul_inv, one_div]
  refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr hdpos.le)
  calc |â k| * |unitIntervalCosineMode k x| ≤ |â k| * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        rw [unitIntervalCosineMode]; exact Real.abs_cos_le_one _
    _ = |â k| := mul_one _

/-- **O1c step 3 — the spectral `T→∞` limit.**  `∫₀ᵀ e^{−μt}·(heat value t â x) dt
→ ∑ₖ âₖ cos(kπx)/(μ+λₖ)` as `T→∞`, by the uniform squeeze
`‖trunc(T) − target‖ ≤ e^{−μT}·M` (`e^{−(μ+λₖ)T} ≤ e^{−μT}`, `M = ∑|âₖ|/(μ+λₖ)`). -/
theorem laplaceHeatTrunc_tendsto {p : CM2Params} {â : ℕ → ℝ}
    (hâ : Summable (fun n => (â n) ^ 2)) (x : ℝ) :
    Filter.Tendsto
      (fun T => ∫ t in (0:ℝ)..T,
        Real.exp (-p.μ * t) * unitIntervalCosineHeatValue t â x)
      Filter.atTop
      (nhds (∑' k, â k * unitIntervalCosineMode k x
        / (p.μ + unitIntervalCosineEigenvalue k))) := by
  have hMsum := summable_abs_sourceCoeff_mul_weight (p := p) hâ
  have htargetsum := summable_resolverTarget (p := p) hâ x
  have hdpos : ∀ k, (0:ℝ) < p.μ + unitIntervalCosineEigenvalue k := by
    intro k
    have h0 : 0 ≤ unitIntervalCosineEigenvalue k := by
      unfold unitIntervalCosineEigenvalue; positivity
    linarith [p.hμ]
  have hweq : ∀ k, intervalNeumannResolverWeight p k
      = 1 / (p.μ + unitIntervalCosineEigenvalue k) := by
    intro k
    rw [intervalNeumannResolverWeight]; congr 2
    rw [show unitIntervalNeumannSpectrum.eigenvalue k = (k : ℝ) ^ 2 * Real.pi ^ 2 from rfl,
      unitIntervalCosineEigenvalue]; ring
  set M : ℝ := ∑' k, |â k| * intervalNeumannResolverWeight p k with hM
  set target : ℝ := ∑' k, â k * unitIntervalCosineMode k x
    / (p.μ + unitIntervalCosineEigenvalue k) with htarget
  -- the difference mode `cₖ(T) = âₖ cos e^{−(μ+λₖ)T}/(μ+λₖ)`, ‖cₖ‖ ≤ e^{−μT}|âₖ|weightₖ.
  set c : ℝ → ℕ → ℝ := fun T k => â k * unitIntervalCosineMode k x
    * Real.exp (-(p.μ + unitIntervalCosineEigenvalue k) * T)
    / (p.μ + unitIntervalCosineEigenvalue k) with hc
  have hnormc : ∀ T k, 0 ≤ T →
      ‖c T k‖ ≤ Real.exp (-p.μ * T) * (|â k| * intervalNeumannResolverWeight p k) := by
    intro T k hT
    have hexple : Real.exp (-(p.μ + unitIntervalCosineEigenvalue k) * T)
        ≤ Real.exp (-p.μ * T) := by
      apply Real.exp_le_exp.mpr
      have h0 : 0 ≤ unitIntervalCosineEigenvalue k := by
        unfold unitIntervalCosineEigenvalue; positivity
      nlinarith [h0, hT]
    rw [hc, Real.norm_eq_abs, abs_div, abs_mul, abs_mul, Real.abs_exp,
      abs_of_pos (hdpos k), hweq k, div_eq_mul_inv, one_div]
    have hcos : |unitIntervalCosineMode k x| ≤ 1 := by
      rw [unitIntervalCosineMode]; exact Real.abs_cos_le_one _
    have key : |â k| * |unitIntervalCosineMode k x|
        * Real.exp (-(p.μ + unitIntervalCosineEigenvalue k) * T)
        * (p.μ + unitIntervalCosineEigenvalue k)⁻¹
        ≤ |â k| * Real.exp (-p.μ * T) * (p.μ + unitIntervalCosineEigenvalue k)⁻¹ := by
      have h1 : |â k| * |unitIntervalCosineMode k x| ≤ |â k| := by
        calc |â k| * |unitIntervalCosineMode k x| ≤ |â k| * 1 :=
              mul_le_mul_of_nonneg_left hcos (abs_nonneg _)
          _ = |â k| := mul_one _
      have hinv : (0:ℝ) ≤ (p.μ + unitIntervalCosineEigenvalue k)⁻¹ := inv_nonneg.mpr (hdpos k).le
      have h2 : |â k| * |unitIntervalCosineMode k x|
          * Real.exp (-(p.μ + unitIntervalCosineEigenvalue k) * T)
          ≤ |â k| * Real.exp (-p.μ * T) :=
        mul_le_mul h1 hexple (Real.exp_nonneg _) (abs_nonneg _)
      exact mul_le_mul_of_nonneg_right h2 hinv
    calc |â k| * |unitIntervalCosineMode k x|
          * Real.exp (-(p.μ + unitIntervalCosineEigenvalue k) * T)
          * (p.μ + unitIntervalCosineEigenvalue k)⁻¹
        ≤ |â k| * Real.exp (-p.μ * T) * (p.μ + unitIntervalCosineEigenvalue k)⁻¹ := key
      _ = Real.exp (-p.μ * T) * (|â k| * (p.μ + unitIntervalCosineEigenvalue k)⁻¹) := by ring
  have hcnormsum : ∀ T, 0 ≤ T → Summable (fun k => ‖c T k‖) := by
    intro T hT
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => hnormc T k hT)
      (hMsum.mul_left (Real.exp (-p.μ * T)))
  -- the squeeze bound on the truncated-spectral series.
  have hev : ∀ᶠ T in Filter.atTop,
      (∫ t in (0:ℝ)..T, Real.exp (-p.μ * t) * unitIntervalCosineHeatValue t â x)
        = ∑' k, â k * unitIntervalCosineMode k x
            * ((1 - Real.exp (-(p.μ + unitIntervalCosineEigenvalue k) * T))
                / (p.μ + unitIntervalCosineEigenvalue k)) := by
    filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with T hT
    exact laplaceResolverTrunc_eq_tsum hâ hT
  refine Filter.Tendsto.congr' (Filter.EventuallyEq.symm hev) ?_
  rw [← tendsto_sub_nhds_zero_iff]
  apply squeeze_zero_norm' (a := fun T => Real.exp (-p.μ * T) * M)
  · filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with T hT
    -- truncSpectral T − target = − ∑' cₖ(T); its norm ≤ e^{−μT}·M.
    have hasum : Summable (fun k => â k * unitIntervalCosineMode k x
        * ((1 - Real.exp (-(p.μ + unitIntervalCosineEigenvalue k) * T))
            / (p.μ + unitIntervalCosineEigenvalue k))) := by
      refine Summable.of_norm_bounded hMsum (fun k => ?_)
      have hcos : |unitIntervalCosineMode k x| ≤ 1 := by
        rw [unitIntervalCosineMode]; exact Real.abs_cos_le_one _
      have he0 : 0 ≤ 1 - Real.exp (-(p.μ + unitIntervalCosineEigenvalue k) * T) := by
        have : Real.exp (-(p.μ + unitIntervalCosineEigenvalue k) * T) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by nlinarith [hdpos k, hT])
        linarith
      have he1 : 1 - Real.exp (-(p.μ + unitIntervalCosineEigenvalue k) * T) ≤ 1 := by
        linarith [Real.exp_nonneg (-(p.μ + unitIntervalCosineEigenvalue k) * T)]
      have hrw : â k * unitIntervalCosineMode k x
          * ((1 - Real.exp (-(p.μ + unitIntervalCosineEigenvalue k) * T))
              / (p.μ + unitIntervalCosineEigenvalue k))
          = (â k * unitIntervalCosineMode k x
              * (1 - Real.exp (-(p.μ + unitIntervalCosineEigenvalue k) * T)))
            / (p.μ + unitIntervalCosineEigenvalue k) := by ring
      rw [Real.norm_eq_abs, hrw, abs_div, abs_of_pos (hdpos k), hweq k,
        div_eq_mul_inv, one_div]
      refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr (hdpos k).le)
      rw [abs_mul, abs_mul, abs_of_nonneg he0]
      calc |â k| * |unitIntervalCosineMode k x|
            * (1 - Real.exp (-(p.μ + unitIntervalCosineEigenvalue k) * T))
          ≤ |â k| * 1 * 1 := by gcongr
        _ = |â k| := by ring
    have hdiff : (∑' k, â k * unitIntervalCosineMode k x
          * ((1 - Real.exp (-(p.μ + unitIntervalCosineEigenvalue k) * T))
              / (p.μ + unitIntervalCosineEigenvalue k))) - target
        = ∑' k, (- c T k) := by
      rw [htarget, ← Summable.tsum_sub hasum htargetsum]
      refine tsum_congr (fun k => ?_)
      rw [hc]; field_simp; ring
    rw [hdiff, tsum_neg, norm_neg]
    calc ‖∑' k, c T k‖ ≤ ∑' k, ‖c T k‖ := norm_tsum_le_tsum_norm (hcnormsum T hT)
      _ ≤ ∑' k, Real.exp (-p.μ * T) * (|â k| * intervalNeumannResolverWeight p k) :=
          (hcnormsum T hT).tsum_le_tsum (fun k => hnormc T k hT)
            (hMsum.mul_left (Real.exp (-p.μ * T)))
      _ = Real.exp (-p.μ * T) * M := by rw [hM, tsum_mul_left]
  · have hexp : Filter.Tendsto (fun T : ℝ => Real.exp (-p.μ * T)) Filter.atTop (nhds 0) := by
      have hμT : Filter.Tendsto (fun T : ℝ => p.μ * T) Filter.atTop Filter.atTop :=
        Filter.Tendsto.const_mul_atTop p.hμ Filter.tendsto_id
      have hcomp : Filter.Tendsto (fun T : ℝ => Real.exp (-(p.μ * T)))
          Filter.atTop (nhds 0) :=
        Real.tendsto_exp_neg_atTop_nhds_zero.comp hμT
      simpa only [neg_mul] using hcomp
    simpa using hexp.mul_const M

end ShenWork.IntervalResolverPositivity
