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

/-- `cosineMode k` is invariant under integer shifts of period `2`:
`cos(kπ(x+2m)) = cos(kπx)`. -/
theorem cosineMode_add_int_two (k : ℕ) (m : ℤ) (x : ℝ) :
    ShenWork.CosineSpectrum.cosineMode k (x + 2 * m) = ShenWork.CosineSpectrum.cosineMode k x := by
  unfold ShenWork.CosineSpectrum.cosineMode
  rw [show (k : ℝ) * Real.pi * (x + 2 * m)
        = (k : ℝ) * Real.pi * x + ((k * m : ℤ) : ℝ) * (2 * Real.pi) from by push_cast; ring,
    Real.cos_add_int_mul_two_pi _ (k * m)]

/-- The cosine heat value is invariant under integer shifts of period `2`:
`V(x + 2m) = V(x)`. -/
theorem cosineHeatValue_add_int_two (c₀ : ℕ → ℝ) (t : ℝ) (m : ℤ) (x : ℝ) :
    unitIntervalCosineHeatValue t c₀ (x + 2 * m) = unitIntervalCosineHeatValue t c₀ x := by
  rw [← cosineHeatSynthesis_eq_cosineHeatValue c₀ t (x + 2 * m),
    ← cosineHeatSynthesis_eq_cosineHeatValue c₀ t x]
  exact tsum_congr (fun k => by rw [cosineMode_add_int_two])

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

/-! ### (C) CONTINUITY of the cosine heat value — uniformly summable cosine series.

Each term `exp(−t(kπ)²)·c₀ k·cosineMode k ·` is bounded in sup-norm by `|c₀ k|` for `t ≥ 0`
(`|exp(−t(kπ)²)| ≤ 1`, `|cos| ≤ 1`), so `continuous_tsum` against the summable majorant
`|c₀ k|` gives continuity of the synthesis, hence of `unitIntervalCosineHeatValue t c₀ ·`. -/

/-- Per-mode sup bound for the heat synthesis term at `t ≥ 0`:
`‖exp(−t(kπ)²)·c₀ k·cosineMode k x‖ ≤ |c₀ k|`. -/
theorem heatSynthesisTerm_norm_le (c₀ : ℕ → ℝ) {t : ℝ} (ht : 0 ≤ t) (k : ℕ) (x : ℝ) :
    ‖(Real.exp (-t * ((k : ℝ) * Real.pi) ^ 2) * c₀ k)
        * ShenWork.CosineSpectrum.cosineMode k x‖ ≤ |c₀ k| := by
  rw [Real.norm_eq_abs, abs_mul, abs_mul, Real.abs_exp]
  have hfac : Real.exp (-t * ((k : ℝ) * Real.pi) ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg ((k : ℝ) * Real.pi)]
  have hcos : |ShenWork.CosineSpectrum.cosineMode k x| ≤ 1 := by
    unfold ShenWork.CosineSpectrum.cosineMode; exact Real.abs_cos_le_one _
  calc Real.exp (-t * ((k : ℝ) * Real.pi) ^ 2) * |c₀ k|
          * |ShenWork.CosineSpectrum.cosineMode k x|
      ≤ 1 * |c₀ k| * 1 := by
        apply mul_le_mul (mul_le_mul hfac le_rfl (abs_nonneg _) (by positivity)) hcos
          (abs_nonneg _) (by positivity)
    _ = |c₀ k| := by ring

/-- **(C) Continuity in `x`.**  For `t ≥ 0` and `|c₀|` summable, the cosine heat value
`x ↦ unitIntervalCosineHeatValue t c₀ x` is continuous. -/
theorem cosineHeatValue_continuous {c₀ : ℕ → ℝ} (hsum : Summable (fun k => |c₀ k|))
    {t : ℝ} (ht : 0 ≤ t) :
    Continuous (fun x => unitIntervalCosineHeatValue t c₀ x) := by
  have heq : (fun x => unitIntervalCosineHeatValue t c₀ x)
      = fun x => ∑' k : ℕ, (Real.exp (-t * ((k : ℝ) * Real.pi) ^ 2) * c₀ k)
          * ShenWork.CosineSpectrum.cosineMode k x := by
    funext x; rw [← cosineHeatSynthesis_eq_cosineHeatValue c₀ t x]
  rw [heq]
  refine continuous_tsum (fun k => continuous_const.mul ?_) hsum
    (fun k x => heatSynthesisTerm_norm_le c₀ ht k x)
  unfold ShenWork.CosineSpectrum.cosineMode
  exact Real.continuous_cos.comp (by fun_prop)

/-- **(C) Continuity in `t` on `Ici 0`** (fixed `x`).  Same majorant `|c₀ k|`. -/
theorem cosineHeatValue_continuousOn_t {c₀ : ℕ → ℝ} (hsum : Summable (fun k => |c₀ k|))
    (x : ℝ) :
    ContinuousOn (fun t => unitIntervalCosineHeatValue t c₀ x) (Set.Ici 0) := by
  have heq : (fun t => unitIntervalCosineHeatValue t c₀ x)
      = fun t => ∑' k : ℕ, (Real.exp (-t * ((k : ℝ) * Real.pi) ^ 2) * c₀ k)
          * ShenWork.CosineSpectrum.cosineMode k x := by
    funext t; rw [← cosineHeatSynthesis_eq_cosineHeatValue c₀ t x]
  rw [heq]
  refine continuousOn_tsum
    (fun k => (Continuous.continuousOn (by fun_prop)))
    hsum (fun k t ht => ?_)
  exact heatSynthesisTerm_norm_le c₀ ht k x

/-! ### (D) FLOOR on `Icc 0 1` for `t ≥ 0` via CLOSED PREIMAGE. -/

/-- **(D1) Floor on `Icc 0 1` for `t > 0`.**  The set `{x | δ ≤ V t c₀ x}` is the closed
preimage `(V t c₀ ·)⁻¹' (Ici δ)`; it contains `Ioo 0 1` (the interior floor), so it
contains `closure (Ioo 0 1) = Icc 0 1`. -/
theorem cosineHeatValue_ge_floor_Icc_pos {t : ℝ} (ht : 0 < t)
    {u₀ : ℝ → ℝ} (hu₀ : Continuous u₀) {δ : ℝ} (hfloor : ∀ y, δ ≤ u₀ y)
    (hsum : Summable (fun k => |cosineCoeffs u₀ k|))
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    δ ≤ unitIntervalCosineHeatValue t (cosineCoeffs u₀) x := by
  have hcont : Continuous (fun x => unitIntervalCosineHeatValue t (cosineCoeffs u₀) x) :=
    cosineHeatValue_continuous hsum ht.le
  have hclosed : IsClosed
      ((fun x => unitIntervalCosineHeatValue t (cosineCoeffs u₀) x) ⁻¹' Set.Ici δ) :=
    isClosed_Ici.preimage hcont
  have hsub : Set.Ioo (0 : ℝ) 1 ⊆
      (fun x => unitIntervalCosineHeatValue t (cosineCoeffs u₀) x) ⁻¹' Set.Ici δ :=
    fun y hy => cosineHeatValue_ge_floor ht hu₀ hfloor hy
  have hIcc : Set.Icc (0 : ℝ) 1 ⊆
      (fun x => unitIntervalCosineHeatValue t (cosineCoeffs u₀) x) ⁻¹' Set.Ici δ := by
    rw [← closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact hclosed.closure_subset_iff.mpr hsub
  exact hIcc hx

/-- **(D2) Floor on `Icc 0 1` for ALL `t ≥ 0`.**  Fix `x ∈ Icc 0 1`.  The set
`{t | δ ≤ V t c₀ x}` is the closed preimage (in `t`, restricted to `Ici 0`); it contains
`Ioi 0` (D1), so it contains `closure (Ioi 0) ∩ Ici 0 ⊇ {0}`, i.e. `t = 0` too. -/
theorem cosineHeatValue_ge_floor_Icc {t : ℝ} (ht : 0 ≤ t)
    {u₀ : ℝ → ℝ} (hu₀ : Continuous u₀) {δ : ℝ} (hfloor : ∀ y, δ ≤ u₀ y)
    (hsum : Summable (fun k => |cosineCoeffs u₀ k|))
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    δ ≤ unitIntervalCosineHeatValue t (cosineCoeffs u₀) x := by
  rcases lt_or_eq_of_le ht with htpos | hteq
  · exact cosineHeatValue_ge_floor_Icc_pos htpos hu₀ hfloor hsum hx
  · -- `t = 0`: extend from `t > 0` via continuity in `t` on `Ici 0`, taking the limit
    -- along `𝓝[>] 0` where the floor holds pointwise (D1).
    subst hteq
    have hcontOn : ContinuousOn (fun s => unitIntervalCosineHeatValue s (cosineCoeffs u₀) x)
        (Set.Ici 0) := cosineHeatValue_continuousOn_t hsum x
    have hcwa : ContinuousWithinAt
        (fun s => unitIntervalCosineHeatValue s (cosineCoeffs u₀) x) (Set.Ici 0) 0 :=
      hcontOn 0 Set.self_mem_Ici
    have htend : Filter.Tendsto
        (fun s => unitIntervalCosineHeatValue s (cosineCoeffs u₀) x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (unitIntervalCosineHeatValue 0 (cosineCoeffs u₀) x)) :=
      hcwa.tendsto.mono_left (nhdsWithin_mono 0 Set.Ioi_subset_Ici_self)
    refine ge_of_tendsto htend ?_
    -- on `Ioi 0` we are at strictly positive time; D1 applies.
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact cosineHeatValue_ge_floor_Icc_pos hs hu₀ hfloor hsum hx

/-- **(E) FLOOR for ALL real `x` and ALL `t ≥ 0`.**  Reduce arbitrary `x` to a fundamental
representative in `[0,1]` by an integer period-`2` shift (`round (x/2)` lands `x` within
`[-1,1]`) followed by evenness (`|·|`), then apply (D2). -/
theorem cosineHeatValue_ge_floor_all {t : ℝ} (ht : 0 ≤ t)
    {u₀ : ℝ → ℝ} (hu₀ : Continuous u₀) {δ : ℝ} (hfloor : ∀ y, δ ≤ u₀ y)
    (hsum : Summable (fun k => |cosineCoeffs u₀ k|)) (x : ℝ) :
    δ ≤ unitIntervalCosineHeatValue t (cosineCoeffs u₀) x := by
  -- `y = x - 2*round(x/2) ∈ [-1,1]`, and `V x = V y` (period-2 integer shift).
  set m : ℤ := round (x / 2) with hm
  set y : ℝ := x - 2 * m with hy
  have hVxy : unitIntervalCosineHeatValue t (cosineCoeffs u₀) x
      = unitIntervalCosineHeatValue t (cosineCoeffs u₀) y := by
    rw [hy, ← cosineHeatValue_add_int_two (cosineCoeffs u₀) t m (x - 2 * m)]
    congr 1; ring
  have hyabs : |y| ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨abs_nonneg _, ?_⟩
    have hround : |x / 2 - (m : ℝ)| ≤ 1 / 2 := by rw [hm]; exact abs_sub_round (x / 2)
    rw [hy]
    have hb : |x - 2 * (m : ℝ)| ≤ 1 := by
      rw [show x - 2 * (m : ℝ) = 2 * (x / 2 - (m : ℝ)) from by ring, abs_mul,
        abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      nlinarith [hround]
    exact hb
  -- `V y = V |y|` (evenness), and `|y| ∈ [0,1]` → apply (D2).
  have hVy : unitIntervalCosineHeatValue t (cosineCoeffs u₀) y
      = unitIntervalCosineHeatValue t (cosineCoeffs u₀) |y| := by
    rcases abs_choice y with h | h
    · rw [h]
    · rw [h, cosineHeatValue_neg]
  rw [hVxy, hVy]
  exact cosineHeatValue_ge_floor_Icc ht hu₀ hfloor hsum hyabs

/-! ### (F) THE FINAL `UniformFloor` — assembling the eval bridge with the heat floor. -/

/-- **THE HEAT-FLOOR (F).**  For the realized cosine datum `u₀E = ⟨ofCosineCoeffs c₀, _⟩`
with `c₀ = cosineCoeffs u₀` (absolutely summable) of a continuous source `u₀ ≥ δ`, the
heat element satisfies the uniform spectral floor `UniformFloor (heatEWA u₀E) δ`.

This discharges the `hheat` gap of `picardEWA_abs_fixedPoint`: at every time `τ ∈ [0,T]`
and every circle point `x`, the included heat symbol has real part `≥ δ`.  Via the eval
bridge (A) the value is the real cast `unitIntervalCosineHeatValue τ.1 c₀ x`, whose real
part is itself; the floor (E) on all real `x` and `τ.1 ≥ 0` closes it. -/
theorem heatEWA_uniformFloor {u₀ : ℝ → ℝ} (hu₀ : Continuous u₀) {δ : ℝ}
    (hfloor : ∀ y, δ ≤ u₀ y) (hsum : Summable (fun k => |cosineCoeffs u₀ k|))
    (hmem : MemW 1 (ofCosineCoeffs (cosineCoeffs u₀))) :
    UniformFloor (heatEWA (T := T)
      (⟨ofCosineCoeffs (cosineCoeffs u₀), hmem⟩ : WA 1)) δ := by
  intro τ x
  -- lift the circle point `x : WA.Circ = AddCircle 2` to a real representative.
  induction x using QuotientAddGroup.induction_on with
  | _ x =>
    rw [heatEWA_evalST_eq_cosineHeatValue (cosineCoeffs u₀) hsum hmem τ x,
      Complex.ofReal_re]
    exact cosineHeatValue_ge_floor_all τ.2.1 hu₀ hfloor hsum x

end ShenWork.EWA
