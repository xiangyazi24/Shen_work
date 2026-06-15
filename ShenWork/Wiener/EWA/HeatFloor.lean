import ShenWork.Wiener.EWA.Decisive
import ShenWork.Wiener.EWA.HeatFlow
import ShenWork.Wiener.EWA.CoeffBridge
import ShenWork.PDE.IntervalResolverPositivity
import ShenWork.PDE.IntervalFullKernelSupBound
import ShenWork.PDE.IntervalSemigroupConeAtoms

/-!
# EWA brick (χ₀<0 Route A′) — THE HEAT-FLOOR POSITIVITY `UniformFloor (heatEWA u₀E) δ`

This file discharges the single named gap `hheat` of `picardEWA_abs_fixedPoint`
(`SourceFixedPointAbs.lean`): the **uniform spectral floor of the Neumann heat flow**
`UniformFloor (heatEWA u₀E) δ` from a positivity floor on the real-space datum
`u₀ ≥ δ > 0`.

## Setup — the realized cosine datum

The realized input is the even cosine embedding `u₀E = ⟨ofCosineCoeffs c₀, _⟩` of the
real cosine-coefficient family `c₀ = cosineCoeffs u₀` of a continuous real-space source
`u₀ : ℝ → ℝ` with floor `∀ y, δ ≤ u₀ y` (the standard `EWARealizesOn` coefficient form,
exactly as the committed resolver/gradient eval bridges take their source).

## (A) THE HEAT EVAL BRIDGE — full circle, unconditional

`heatEWA_evalST_eq_cosineHeatValue` :
`evalST τ x (incl (heatEWA u₀E)) = (unitIntervalCosineHeatValue τ.1 c₀ x : ℂ)`
for EVERY `τ` and EVERY real `x`.  The slice of `heatEWA (ofCosineCoeffs c₀)` is the
even cosine embedding of the heat-multiplied family `k ↦ exp(−τ(kπ)²)·c₀ k`
(`heatEWA_slice_eq_ofCosineCoeffs`, because `exp(−τ(nπ)²)` is even in `n`), so the
committed full-circle synthesis `evalC_ofCosineCoeffs_all` gives
`∑ₖ exp(−τ(kπ)²)·c₀ k·cosineMode k x = unitIntervalCosineHeatValue τ.1 c₀ x`
(`λ_n = (nπ)²` and `unitIntervalCosineMode = cosineMode`, both `rfl`/committed).
NO integral interchange is needed on the EWA side: the heat element is *diagonal*, so
its eval is term-by-term and the synthesis is the committed `evalC` of an
`ofCosineCoeffs`.

## (B) THE HEAT POSITIVITY → FLOOR

Through the committed *unconditional* real-space bridge
`intervalFullSemigroupOperator_eq_cosineHeatValue_unconditional`
(the `[0,1]` Neumann propagator equals the cosine spectral heat value, the kernel↔theta
identity and the integral interchange both discharged from `t>0`/continuity), with
`cosineCoeffs u₀ = c₀`:
`unitIntervalCosineHeatValue τ c₀ x = intervalFullSemigroupOperator τ u₀ x`
on `τ>0`, `x ∈ (0,1)`.  Then the floor is the heat-kernel positivity:
`∫ Kfull·u₀ ≥ ∫ Kfull·δ = δ·∫Kfull = δ` (kernel `≥0`, mass `=1`).
-/

open scoped BigOperators
open Set
open ShenWork.GWA ShenWork.Wiener
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalFullKernelInterchange
open ShenWork.IntervalResolverPositivity

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-! ### (A0) The slice of `heatEWA (ofCosineCoeffs c₀)` is an even cosine embedding. -/

/-- The heat factor `exp(−τ(nπ)²)` depends only on `|n|`: it is even in `n`. -/
theorem heatFactor_even (τ : ℝ) (n : ℤ) :
    Real.exp (-τ * ((n : ℝ) * Real.pi) ^ 2)
      = Real.exp (-τ * (((n.natAbs : ℕ) : ℝ) * Real.pi) ^ 2) := by
  congr 2
  have h : (n.natAbs : ℝ) = |(n : ℝ)| := by simp
  rw [h, show |(n : ℝ)| * Real.pi = |(n : ℝ) * Real.pi| from by
    rw [abs_mul, abs_of_nonneg Real.pi_pos.le], sq_abs]

/-- **The slice of the heat element is the cosine embedding of the heat-multiplied
family.**  `(sliceWA τ (heatEWA (ofCosineCoeffs c₀))).toFun
  = ofCosineCoeffs (fun k => exp(−τ(kπ)²)·c₀ k)`, because the per-mode heat factor is
even and folds onto the `±n` halves of `ofCosineCoeffs`. -/
theorem heatEWA_slice_eq_ofCosineCoeffs (c₀ : ℕ → ℝ) (τ : TimeDom T)
    (hmem : MemW 1 (ofCosineCoeffs c₀)) (n : ℤ) :
    ((heatEWA (T := T) (⟨ofCosineCoeffs c₀, hmem⟩ : WA 1)).toFun n) τ
      = ofCosineCoeffs (fun k => Real.exp (-(τ : ℝ) * ((k : ℝ) * Real.pi) ^ 2) * c₀ k) n := by
  rw [heatEWA_toFun]
  change heatModeFun n ((⟨ofCosineCoeffs c₀, hmem⟩ : WA 1).toFun n) (τ : ℝ)
      = ofCosineCoeffs (fun k => Real.exp (-(τ : ℝ) * ((k : ℝ) * Real.pi) ^ 2) * c₀ k) n
  change (Real.exp (-(τ : ℝ) * ((n : ℝ) * Real.pi) ^ 2) : ℂ) * (ofCosineCoeffs c₀ n)
      = ofCosineCoeffs (fun k => Real.exp (-(τ : ℝ) * ((k : ℝ) * Real.pi) ^ 2) * c₀ k) n
  unfold ofCosineCoeffs
  by_cases h : n = 0
  · subst h; simp
  · rw [if_neg h, if_neg h]
    rw [heatFactor_even (τ : ℝ) n]
    push_cast
    ring

/-! ### (A) THE HEAT EVAL BRIDGE — full circle, unconditional.

`evalST τ x (incl (heatEWA u₀E)) = (unitIntervalCosineHeatValue τ.1 c₀ x : ℂ)`. -/

/-- The `∑ₖ exp(−τ(kπ)²)·c₀ k·cosineMode k x` synthesis equals the committed
`unitIntervalCosineHeatValue τ c₀ x` (`λ_k = (kπ)²`, `cosineMode = unitIntervalCosineMode`,
both definitional). -/
theorem cosineHeatSynthesis_eq_cosineHeatValue (c₀ : ℕ → ℝ) (t x : ℝ) :
    (∑' k : ℕ, (Real.exp (-t * ((k : ℝ) * Real.pi) ^ 2) * c₀ k)
        * ShenWork.CosineSpectrum.cosineMode k x)
      = unitIntervalCosineHeatValue t c₀ x := by
  rw [unitIntervalCosineHeatValue]
  refine tsum_congr (fun k => ?_)
  rw [unitIntervalCosineHeatPointWeight,
    unitIntervalCosineEigenvalue,
    unitIntervalCosineMode_eq_cosineMode]
  ring

/-! #### Even / period-2 / reflect-about-1 symmetries of the cosine heat value. -/

/-- `cosineMode k` is even: `cos(kπ(−x)) = cos(kπx)`. -/
theorem cosineMode_neg (k : ℕ) (x : ℝ) :
    ShenWork.CosineSpectrum.cosineMode k (-x) = ShenWork.CosineSpectrum.cosineMode k x := by
  unfold ShenWork.CosineSpectrum.cosineMode
  rw [show (k : ℝ) * Real.pi * (-x) = -((k : ℝ) * Real.pi * x) from by ring, Real.cos_neg]

/-- `cosineMode k` has period `2`: `cos(kπ(x+2)) = cos(kπx)`. -/
theorem cosineMode_add_two (k : ℕ) (x : ℝ) :
    ShenWork.CosineSpectrum.cosineMode k (x + 2) = ShenWork.CosineSpectrum.cosineMode k x := by
  unfold ShenWork.CosineSpectrum.cosineMode
  rw [show (k : ℝ) * Real.pi * (x + 2)
        = (k : ℝ) * Real.pi * x + ((k : ℤ) : ℝ) * (2 * Real.pi) from by push_cast; ring,
    Real.cos_add_int_mul_two_pi _ (k : ℤ)]

/-- The cosine heat value is **even** in `x`. -/
theorem cosineHeatValue_neg (c₀ : ℕ → ℝ) (t x : ℝ) :
    unitIntervalCosineHeatValue t c₀ (-x) = unitIntervalCosineHeatValue t c₀ x := by
  rw [← cosineHeatSynthesis_eq_cosineHeatValue c₀ t (-x),
    ← cosineHeatSynthesis_eq_cosineHeatValue c₀ t x]
  exact tsum_congr (fun k => by rw [cosineMode_neg])

/-- The cosine heat value has **period `2`** in `x`. -/
theorem cosineHeatValue_add_two (c₀ : ℕ → ℝ) (t x : ℝ) :
    unitIntervalCosineHeatValue t c₀ (x + 2) = unitIntervalCosineHeatValue t c₀ x := by
  rw [← cosineHeatSynthesis_eq_cosineHeatValue c₀ t (x + 2),
    ← cosineHeatSynthesis_eq_cosineHeatValue c₀ t x]
  exact tsum_congr (fun k => by rw [cosineMode_add_two])

/-- The cosine heat value is **even about `1`**: `V(2−x) = V(x)` (period-2 ∘ evenness). -/
theorem cosineHeatValue_reflect_one (c₀ : ℕ → ℝ) (t x : ℝ) :
    unitIntervalCosineHeatValue t c₀ (2 - x) = unitIntervalCosineHeatValue t c₀ x := by
  rw [show (2 : ℝ) - x = (-x) + 2 from by ring, cosineHeatValue_add_two, cosineHeatValue_neg]

/-- **THE HEAT EVAL BRIDGE (A).**  For the realized cosine datum
`u₀E = ⟨ofCosineCoeffs c₀, _⟩` (with `c₀` absolutely summable), the EWA point evaluation
of the heat element equals the committed cosine spectral heat value at every time `τ`
and every real spatial point `x` (the full circle):
`evalST τ x (incl (heatEWA u₀E)) = (unitIntervalCosineHeatValue τ.1 c₀ x : ℂ)`. -/
theorem heatEWA_evalST_eq_cosineHeatValue (c₀ : ℕ → ℝ)
    (hsum : Summable (fun k => |c₀ k|))
    (hmem : MemW 1 (ofCosineCoeffs c₀)) (τ : TimeDom T) (x : ℝ) :
    evalST τ ((x : ℝ) : WA.Circ)
        (GWA.incl (by omega : (0:ℕ) ≤ 1) (heatEWA (T := T) (⟨ofCosineCoeffs c₀, hmem⟩ : WA 1)))
      = ((unitIntervalCosineHeatValue (τ : ℝ) c₀ x : ℝ) : ℂ) := by
  -- the heat-multiplied family and its summability
  set d : ℕ → ℝ := fun k => Real.exp (-(τ : ℝ) * ((k : ℝ) * Real.pi) ^ 2) * c₀ k with hd
  have hdsum : Summable (fun k => |d k|) := by
    refine hsum.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
    rw [hd, abs_mul, Real.abs_exp]
    have hfac : Real.exp (-(τ : ℝ) * ((k : ℝ) * Real.pi) ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have ht0 : (0 : ℝ) ≤ (τ : ℝ) := τ.2.1
      nlinarith [sq_nonneg ((k : ℝ) * Real.pi)]
    calc Real.exp (-(τ : ℝ) * ((k : ℝ) * Real.pi) ^ 2) * |c₀ k|
        ≤ 1 * |c₀ k| := mul_le_mul_of_nonneg_right hfac (abs_nonneg _)
      _ = |c₀ k| := one_mul _
  -- the heat element's `incl` and slice unfold to the cosine embedding of `d`
  have hmemd : MemW 0 (ofCosineCoeffs d) := memW_ofCosineCoeffs (r := 0) (by simpa using hdsum)
  have hslice :
      sliceWA τ (GWA.incl (by omega : (0:ℕ) ≤ 1)
          (heatEWA (T := T) (⟨ofCosineCoeffs c₀, hmem⟩ : WA 1)))
        = (⟨ofCosineCoeffs d, hmemd⟩ : WA 0) := by
    apply WA.ext
    funext n
    rw [coeff_sliceWA, GWA.incl_toFun]
    exact heatEWA_slice_eq_ofCosineCoeffs (T := T) c₀ τ hmem n
  -- evaluate the synthesis
  rw [evalST_apply, WA.evalAt_apply, ← WA.evalC_apply, hslice]
  rw [evalC_ofCosineCoeffs_all d hdsum x]
  congr 1
  rw [← cosineHeatSynthesis_eq_cosineHeatValue c₀ (τ : ℝ) x]

/-! ### (B) THE HEAT POSITIVITY → FLOOR.

`δ ≤ intervalFullSemigroupOperator t u₀ x = unitIntervalCosineHeatValue t (cosineCoeffs u₀) x`
for `t > 0`, `x ∈ (0,1)`, when `u₀ ≥ δ`. -/

/-- **Kernel floor.**  The full Neumann propagator of a source bounded below by `δ` is
itself `≥ δ`: `∫ Kfull·u₀ ≥ ∫ Kfull·δ = δ·∫Kfull = δ` (kernel `≥ 0`, mass `= 1`). -/
theorem intervalFullSemigroupOperator_ge_floor {t : ℝ} (ht : 0 < t)
    {u₀ : ℝ → ℝ} (hu₀ : Continuous u₀) {δ : ℝ} (hfloor : ∀ y, δ ≤ u₀ y) (x : ℝ) :
    δ ≤ intervalFullSemigroupOperator t u₀ x := by
  have hKint : MeasureTheory.Integrable
      (fun y => intervalNeumannFullKernel t x y)
      (ShenWork.IntervalDomain.intervalMeasure 1) :=
    intervalNeumannFullKernel_integrable ht x
  have hmass : (∫ y, intervalNeumannFullKernel t x y
      ∂(ShenWork.IntervalDomain.intervalMeasure 1)) = 1 :=
    intervalNeumannFullKernel_intervalMeasure_integral_eq_one ht x
  -- `∫ Kfull·δ = δ`
  have hconst : (∫ y, intervalNeumannFullKernel t x y * δ
      ∂(ShenWork.IntervalDomain.intervalMeasure 1)) = δ := by
    rw [MeasureTheory.integral_mul_const, hmass, one_mul]
  -- `∫ Kfull·u₀` integrable: continuous kernel × continuous source on the compact `[0,1]`
  have hKu : MeasureTheory.Integrable
      (fun y => intervalNeumannFullKernel t x y * u₀ y)
      (ShenWork.IntervalDomain.intervalMeasure 1) := by
    have hcont : ContinuousOn
        (fun y => intervalNeumannFullKernel t x y * u₀ y) (Set.Icc (0 : ℝ) 1) :=
      (continuousOn_intervalNeumannFullKernel_snd ht x).mul hu₀.continuousOn
    simp only [ShenWork.IntervalDomain.intervalMeasure,
      ShenWork.IntervalDomain.intervalSet]
    exact hcont.integrableOn_Icc
  have hmono : (∫ y, intervalNeumannFullKernel t x y * δ
        ∂(ShenWork.IntervalDomain.intervalMeasure 1))
      ≤ ∫ y, intervalNeumannFullKernel t x y * u₀ y
        ∂(ShenWork.IntervalDomain.intervalMeasure 1) := by
    refine MeasureTheory.integral_mono (hKint.mul_const δ) hKu (fun y => ?_)
    exact mul_le_mul_of_nonneg_left (hfloor y)
      (intervalNeumannFullKernel_nonneg ht x y)
  rw [intervalFullSemigroupOperator]
  calc δ = ∫ y, intervalNeumannFullKernel t x y * δ
        ∂(ShenWork.IntervalDomain.intervalMeasure 1) := hconst.symm
    _ ≤ _ := hmono

/-- **Floor on the cosine spectral heat value.**  Composing the kernel floor with the
committed unconditional eval bridge: `δ ≤ unitIntervalCosineHeatValue t (cosineCoeffs u₀) x`
for `t > 0`, `x ∈ (0,1)`, `u₀ ≥ δ` continuous. -/
theorem cosineHeatValue_ge_floor {t : ℝ} (ht : 0 < t)
    {u₀ : ℝ → ℝ} (hu₀ : Continuous u₀) {δ : ℝ} (hfloor : ∀ y, δ ≤ u₀ y)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    δ ≤ unitIntervalCosineHeatValue t (cosineCoeffs u₀) x := by
  rw [← intervalFullSemigroupOperator_eq_cosineHeatValue_unconditional t ht u₀ hu₀ x hx
        (fun y => intervalNeumannFullKernel_cosineKernel_identity ht x y)]
  exact intervalFullSemigroupOperator_ge_floor ht hu₀ hfloor x

end ShenWork.EWA
