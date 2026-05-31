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

open MeasureTheory
open ShenWork.IntervalDomain (intervalMeasure)
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalFullKernelInterchange

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
  apply integral_nonneg
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

end ShenWork.IntervalResolverPositivity
