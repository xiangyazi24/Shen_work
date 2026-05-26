import ShenWork.PDE.IntervalNeumannFullKernel
import ShenWork.PDE.HeatKernelGradientEstimates
import ShenWork.PDE.CosineParsevalBridge
import Mathlib.Analysis.Fourier.AddCircle

/-!
# Pointwise cosine inversion and `ℓ¹` summability for the unit interval

This file discharges the two named analytic inputs of
`intervalFullSemigroup_tendsto_id_at_zero`
(`ShenWork/PDE/IntervalSemigroupApproxIdentity.lean`):

* `intervalCosineCoeff_summable_abs` — `Summable (fun n => |cosineCoeffs f n|)`
  (the `hl1` shape), and
* `intervalCosine_hasSum_pointwise` — `HasSum (fun n => cos(nπx) · f̂ₙ) (f x)`
  at an interior point `x ∈ (0,1)` (the `hrecon` shape).

## Route (even reflection → `AddCircle 2` Fourier inversion)

The repository already proves, in `CosineParsevalBridge.lean`, the exact bridge
relating the interval cosine coefficients to the Fourier coefficients of the even
reflection on the doubled circle of period `2`:

  `unitIntervalEvenReflection_fourierCoeffOn_eq_cosineCoeff`:
    `fourierCoeffOn (-1<1) (evenReflection f) n = ∫₀¹ cos(nπx) f(x) dx`,

together with the pointwise pairing
  `unitIntervalCosine_int_eq_fourier_pair`:
    `cos(nπx) = ½(fourier n x + fourier (-n) x)`.

We push these through Mathlib's pointwise Fourier inversion under `ℓ¹`,
`has_pointwise_sum_fourier_series_of_summable`, and the `ℤ → ℕ` regrouping
`HasSum.of_nat_of_neg_add_one`.

## The `f`-hypothesis

Both results take, beyond continuity of `f`, the single regularity input

  `hsum : Summable (fun n : ℤ => fourierCoeff (reflCircle f) n)`

i.e. `ℓ¹`-summability of the `AddCircle 2` Fourier coefficients of the even
reflection -- exactly the standard hypothesis under which the Fourier (hence
cosine) series converges absolutely and uniformly.  It holds whenever the even
`2`-periodic extension is sufficiently regular: e.g. for `f ∈ C²[0,1]` with
Neumann data `f'(0) = f'(1) = 0`, two integrations by parts give `|f̂ₙ| ≤ C/n²`,
which is summable.  (`Mathlib.Analysis.Fourier.AddCircle.fourierCoeffOn_of_hasDerivAt`
supplies the per-step integration-by-parts identity; the `C²`/Neumann derivation of
`hsum` is elementary but is not formalised here.)

### Named Mathlib blocker

The plain-function pointwise lemma `has_pointwise_sum_fourier_series_of_summable`
(Mathlib v4.29.1) does NOT elaborate here: applying it runs into a
`(deterministic) timeout at isDefEq` even at `2 000 000` heartbeats, and this
reproduces with an abstract period `T`, so it is a unification pathology in that
lemma rather than in this file.  We instead use the bundled `ContinuousMap`-valued
`hasSum_fourier_series_of_summable` (elaborates instantly) and evaluate at `x`
through `ContinuousMap.evalCLM`, reconstructing the pointwise statement by hand.

No `sorry`/`admit`/custom axiom is used (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

open MeasureTheory Filter Topology Complex
open ShenWork.CosineParsevalBridge
open ShenWork.HeatKernelGradientEstimates
open ShenWork.IntervalNeumannFullKernel

namespace ShenWork.IntervalCosineInversion

noncomputable section

open scoped Real

instance : Fact (0 < (2 : ℝ)) := ⟨by norm_num⟩
instance : Fact (0 < (1 : ℝ) - (-1)) := ⟨by norm_num⟩

/-- The even reflection of a real interval function, as a complex-valued function. -/
def reflC (f : ℝ → ℝ) : ℝ → ℂ :=
  unitIntervalEvenReflection (fun x => (f x : ℂ))

/-- The `AddCircle 2` lift of the even reflection. -/
def reflCircle (f : ℝ → ℝ) : AddCircle (2 : ℝ) → ℂ :=
  AddCircle.liftIoc (2 : ℝ) (-1) (reflC f)

/-- The even reflection on the doubled circle is continuous: `reflC f` is
continuous and agrees at the gluing endpoints `-1` and `1`. -/
theorem reflCircle_continuous (f : ℝ → ℝ) (hf : Continuous f) :
    Continuous (reflCircle f) := by
  apply AddCircle.liftIoc_continuous
  · -- `reflC f (-1) = reflC f (-1 + 2)`
    show reflC f (-1) = reflC f (-1 + 2)
    simp only [reflC, unitIntervalEvenReflection]
    norm_num
  · -- continuity on the closed fundamental domain
    apply Continuous.continuousOn
    show Continuous (unitIntervalEvenReflection (fun x => (f x : ℂ)))
    exact (Complex.continuous_ofReal.comp hf).comp continuous_abs

/-- The even reflection on the doubled circle, bundled as a continuous map.  Used
to invoke the (efficient) `ContinuousMap`-valued Fourier inversion. -/
def reflCM (f : ℝ → ℝ) (hf : Continuous f) : C(AddCircle (2 : ℝ), ℂ) :=
  ⟨reflCircle f, reflCircle_continuous f hf⟩

local notation "fco" => fourierCoeffOn (show (-1 : ℝ) < 1 by norm_num)

/-- `fourierCoeffOn (-1,1) (reflC f) n = ∫₀¹ cos(nπx) f(x) dx`, a real number. -/
theorem fco_eq_raw (f : ℝ → ℝ) (hf : Continuous f) (n : ℤ) :
    fco (reflC f) n =
      ∫ x in (0 : ℝ)..1, (Real.cos ((n : ℝ) * Real.pi * x) : ℂ) * (f x : ℂ) := by
  have hint : IntervalIntegrable (fun x => (f x : ℂ)) volume 0 1 :=
    (Complex.continuous_ofReal.comp hf).intervalIntegrable _ _
  exact unitIntervalEvenReflection_fourierCoeffOn_eq_cosineCoeff hint n

/-- The Fourier coefficient of the even reflection equals `f`'s real cosine
integral cast into `ℂ`; in particular it is real. -/
theorem fco_eq_ofReal (f : ℝ → ℝ) (hf : Continuous f) (n : ℤ) :
    fco (reflC f) n =
      ((∫ x in (0 : ℝ)..1, Real.cos ((n : ℝ) * Real.pi * x) * f x : ℝ) : ℂ) := by
  rw [fco_eq_raw f hf n]
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro x _hx
  push_cast
  ring

/-- `cosineCoeffs f n` equals the (real part of the) `AddCircle` Fourier
coefficient, scaled by `2` for positive modes. -/
theorem cosineCoeffs_eq (f : ℝ → ℝ) (hf : Continuous f) (n : ℕ) :
    cosineCoeffs f n =
      (if n = 0 then (1 : ℝ) else 2) * (fco (reflC f) (n : ℤ)).re := by
  rw [cosineCoeffs, unitIntervalNeumannCosineCoeff]
  have hre : (fco (reflC f) (n : ℤ)).re =
      (unitIntervalCosineRawCoeff (fun x => (f x : ℂ)) n).re := by
    rw [fco_eq_raw f hf, unitIntervalCosineRawCoeff]
    norm_cast
  rcases eq_or_ne n 0 with h | h
  · subst h; rw [hre]; simp
  · simp only [if_neg h]; rw [hre]

/-- The Fourier coefficients of the even reflection are even in the frequency:
`fco (reflC f) (-n) = fco (reflC f) n`, because `cos` is even in `n`. -/
theorem fco_neg (f : ℝ → ℝ) (hf : Continuous f) (n : ℤ) :
    fco (reflC f) (-n) = fco (reflC f) n := by
  rw [fco_eq_raw f hf, fco_eq_raw f hf]
  apply intervalIntegral.integral_congr
  intro x _hx
  simp only []
  have : ((-n : ℤ) : ℝ) * Real.pi * x = -((n : ℝ) * Real.pi * x) := by push_cast; ring
  rw [this, Real.cos_neg]

/-! ## The `AddCircle 2` Fourier coefficient is the interval cosine coefficient. -/

/-- The `AddCircle 2` Fourier coefficient of the lifted reflection equals the
`fourierCoeffOn` of the reflection on `[-1,1]`. -/
theorem fourierCoeff_reflCircle (f : ℝ → ℝ) (n : ℤ) :
    fourierCoeff (reflCircle f) n = fco (reflC f) n := by
  rw [reflCircle]
  rw [fourierCoeff_liftIoc_eq (reflC f) n]
  congr 1
  norm_num

/-! ## `ℓ¹` summability (the `hl1` shape) -/

/-- **`ℓ¹` summability of the cosine coefficients.**  Under summability of the
`AddCircle 2` Fourier coefficients of the even reflection (the regularity input —
guaranteed e.g. for `f ∈ C¹` with Neumann data via `|f̂ₙ| ≤ C/n²`), the
unit-interval cosine coefficients are absolutely summable. -/
theorem intervalCosineCoeff_summable_abs
    (f : ℝ → ℝ) (hf : Continuous f)
    (hsum : Summable (fun n : ℤ => fourierCoeff (reflCircle f) n)) :
    Summable (fun n => |cosineCoeffs f n|) := by
  have hnorm : Summable (fun n : ℤ => ‖fourierCoeff (reflCircle f) n‖) := hsum.norm
  have hnat : Summable (fun n : ℕ => ‖fourierCoeff (reflCircle f) (n : ℤ)‖) :=
    hnorm.comp_injective Nat.cast_injective
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) ?_
    (hnat.mul_left 2)
  intro n
  rw [cosineCoeffs_eq f hf n, abs_mul]
  have hb : |(fco (reflC f) (n : ℤ)).re| ≤ ‖fourierCoeff (reflCircle f) (n : ℤ)‖ := by
    rw [fourierCoeff_reflCircle]
    exact Complex.abs_re_le_norm _
  have hc : |(if n = 0 then (1 : ℝ) else 2)| ≤ 2 := by
    rcases eq_or_ne n 0 with h | h <;> simp [h]
  calc |if n = 0 then (1 : ℝ) else 2| * |(fco (reflC f) (n : ℤ)).re|
      ≤ 2 * ‖fourierCoeff (reflCircle f) (n : ℤ)‖ :=
        mul_le_mul hc hb (abs_nonneg _) (by norm_num)

/-! ## Pointwise cosine inversion (the `hrecon` shape) -/

/-- The lifted reflection evaluated at an interior point returns the original
value: `reflCircle f (↑x) = f x` for `x ∈ (0,1)`. -/
theorem reflCircle_coe_eq (f : ℝ → ℝ) {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    reflCircle f (x : AddCircle (2 : ℝ)) = (f x : ℂ) := by
  rw [reflCircle]
  have hmem : x ∈ Set.Ioc (-1 : ℝ) (-1 + 2) := by
    constructor <;> [linarith [hx.1]; linarith [hx.2.le]]
  rw [AddCircle.liftIoc_coe_apply hmem]
  rw [reflC, unitIntervalEvenReflection_apply_of_nonneg _ hx.1.le]

/-- The realness of the Fourier coefficient: `fourierCoeff (reflCircle f) n`
is its own real part cast back into `ℂ`. -/
theorem fourierCoeff_ofReal_re (f : ℝ → ℝ) (hf : Continuous f) (n : ℤ) :
    (((fourierCoeff (reflCircle f) n).re : ℝ) : ℂ) = fourierCoeff (reflCircle f) n := by
  rw [fourierCoeff_reflCircle, fco_eq_ofReal f hf]
  simp

set_option maxHeartbeats 1000000 in
/-- **Pointwise cosine inversion.**  Under summability of the `AddCircle 2`
Fourier coefficients of the even reflection, the unit-interval cosine series
converges pointwise to `f x` at every interior point `x ∈ (0,1)`. -/
theorem intervalCosine_hasSum_pointwise
    (f : ℝ → ℝ) (hf : Continuous f) {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : Summable (fun n : ℤ => fourierCoeff (reflCircle f) n)) :
    HasSum (fun n => unitIntervalCosineMode n x * cosineCoeffs f n) (f x) := by
  -- Abbreviate the (real-valued) Fourier coefficient and record the two facts
  -- about it that the argument needs, then make it opaque.
  obtain ⟨c, hc_def⟩ : ∃ c : ℤ → ℂ, c = fun n => fourierCoeff (reflCircle f) n :=
    ⟨_, rfl⟩
  have hc_neg : ∀ n : ℤ, c (-n) = c n := by
    intro n; rw [hc_def]; simp only []
    rw [fourierCoeff_reflCircle, fourierCoeff_reflCircle, fco_neg f hf]
  have hc_re : ∀ n : ℤ, (((c n).re : ℝ) : ℂ) = c n := by
    intro n; rw [hc_def]; simp only []; exact fourierCoeff_ofReal_re f hf n
  have hc_cos : ∀ n : ℕ,
      (cosineCoeffs f n : ℂ) = (if n = 0 then (1 : ℂ) else 2) * c (n : ℤ) := by
    intro n
    rw [hc_def]; simp only []
    rw [cosineCoeffs_eq f hf n]
    rw [← fourierCoeff_ofReal_re f hf (n : ℤ), fourierCoeff_reflCircle]
    rcases eq_or_ne n 0 with h | h <;> simp [h] <;> push_cast <;> ring
  -- uniform Fourier inversion in `C(AddCircle 2, ℂ)` for the bundled reflection
  have hsumCM : Summable (fourierCoeff ((reflCM f hf : C(AddCircle (2 : ℝ), ℂ)) :
      AddCircle (2 : ℝ) → ℂ)) := hsum
  have huniform := hasSum_fourier_series_of_summable hsumCM
  -- evaluate at `x` via the continuous-linear evaluation map
  have hpt0 := (ContinuousMap.evalCLM ℂ (x : AddCircle (2 : ℝ))).hasSum huniform
  -- rewrite into the `c`-form and the value `f x`
  have hpt : HasSum (fun n : ℤ => c n • fourier n (x : AddCircle (2 : ℝ)))
      (reflCircle f (x : AddCircle (2 : ℝ))) := by
    have hval : (ContinuousMap.evalCLM ℂ (x : AddCircle (2 : ℝ)))
        (reflCM f hf) = reflCircle f (x : AddCircle (2 : ℝ)) := rfl
    rw [hval] at hpt0
    convert hpt0 using 2 with n
    rw [hc_def]
    simp only [ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply]
    rfl
  rw [reflCircle_coe_eq f hx] at hpt
  set a : ℤ → ℂ := fun n => c n • fourier n (x : AddCircle (2 : ℝ)) with ha
  have hpair : HasSum (fun n : ℕ => a (n : ℤ) + a (-(n : ℤ))) ((f x : ℂ) + a 0) :=
    hpt.nat_add_neg
  have hsingle : HasSum (fun n : ℕ => Pi.single (M := fun _ => ℂ) (0 : ℕ) (a 0) n) (a 0) :=
    hasSum_single 0 (fun b hb => by simp [Pi.single, Function.update, hb])
  have hsub := hpair.sub hsingle
  rw [add_sub_cancel_right] at hsub
  have hterm : ∀ n : ℕ,
      (a (n : ℤ) + a (-(n : ℤ))) - Pi.single (M := fun _ => ℂ) (0 : ℕ) (a 0) n =
        ((unitIntervalCosineMode n x * cosineCoeffs f n : ℝ) : ℂ) := by
    intro n
    rcases eq_or_ne n 0 with h | h
    · subst h
      simp only [Nat.cast_zero, neg_zero, Pi.single_eq_same]
      rw [ha]
      simp only [fourier_zero, smul_eq_mul, mul_one]
      rw [unitIntervalCosineMode]
      push_cast [hc_cos 0]
      simp only [zero_mul, Complex.cos_zero]
      ring
    · rw [Pi.single_eq_of_ne h, sub_zero, ha]
      simp only [smul_eq_mul]
      rw [hc_neg (n : ℤ), ← mul_add]
      have hpair2 : fourier (n : ℤ) (x : AddCircle (2 : ℝ)) +
          fourier (-(n : ℤ)) (x : AddCircle (2 : ℝ)) =
          2 * ((Real.cos (((n : ℤ) : ℝ) * Real.pi * x) : ℂ)) := by
        rw [unitIntervalCosine_int_eq_fourier_pair (n : ℤ) x]; ring
      rw [hpair2, unitIntervalCosineMode]
      rw [show ((n : ℝ) * Real.pi * x) = (((n : ℤ) : ℝ) * Real.pi * x) by push_cast; ring]
      push_cast [hc_cos n]
      simp only [if_neg h]
      rw [← hc_re (n : ℤ)]
      push_cast; ring
  clear_value a
  rw [funext hterm] at hsub
  exact Complex.hasSum_ofReal.mp hsub

end

end ShenWork.IntervalCosineInversion
