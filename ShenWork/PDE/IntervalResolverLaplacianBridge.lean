/-
# Laplacian-mode bridge for the elliptic resolver `R u`

This file builds the second-spatial-derivative (Laplacian-mode) infrastructure
for the unit-interval elliptic Neumann resolver

  `R u = ∑' k, v̂_k · cos(k π x)`,    `v̂_k = â_k / (μ + λ_k)`,

paralleling `IntervalResolverGradientBridge` (the first-derivative bridge).

The genuine technical content here is a **strong elliptic identity at the
value-series level**: the termwise second-derivative series

  `RLap p u y := ∑' k, v̂_k · (−(k π)² · cos(k π y))`

is, for any `y` and under `SourceCoeffQuadraticDecay`, expressible purely in
terms of two already-summable cosine series, via the spectral form of the
elliptic equation `−Δ(R u) + p.μ · (R u) = source`:

  `RLap p u y  =  p.μ · R p u y  −  sourceValue p u y`,                  (★)

where `sourceValue p u y := ∑' k, â_k · cos(k π y)`.

## Why this matters for the chemotaxis flux

The chemotaxis flux Lipschitz reduces to controlling, for `v = R u`, the
difference of `∂ₓ² v` between two trajectories.  The naive route is the
"cubic-weighted" cosine sum `∑ |v̂_k| · (k π)²`, which is `ℓ¹` (proved here by
Weierstrass-M from `SourceCoeffQuadraticDecay`) but does not yield a
sup-Lipschitz bound proportional to the trajectory difference, because the
Cauchy–Schwarz `ℓ² → L^∞` route (used for the value and gradient bounds) fails
here — the weight `(k π)² / (μ + λ_k) ≤ 1` is not `ℓ²`-summable.

Strengthening the regularity bundle to *C³-Neumann* (which would give an
`O(1/k³)` source decay, hence a summable squared weight) is **false** for
classical solutions of `(CM)`: the PDE at the boundary forces
`u''(0) = ∂ₜu(0,t) − χ₀(chemotaxis flux)(0,t) + reaction`, generically nonzero.
There is no honest infrastructure addition that delivers `C³`-Neumann here.

The identity (★) bypasses the bottleneck entirely.  The difference
`RLap u₁ − RLap u₂` decomposes into

  `p.μ · (R u₁ − R u₂)  −  (sourceValue u₁ − sourceValue u₂)`,

where the first piece is already controlled by
`intervalNeumannResolverR_sup_lipschitz` (a real, proved sup-Lipschitz bound in
the trajectory difference), and the second piece reduces to the sup-Lipschitz
behaviour of the *source value series*.  The source value series is the cosine
inversion of `p.ν · u^γ` (Fourier inversion on the even reflection,
`intervalCosine_hasSum_pointwise`), so for classical solutions it equals the
pointwise function value, whose sup-Lipschitz behaviour in `u` is the standard
mean-value bound `|u₁^γ − u₂^γ| ≤ γ M^{γ−1} |u₁ − u₂|` on the trajectory ball.

## What this file proves

* `intervalNeumannResolverRLap`, `intervalNeumannResolverSourceValue` — the two
  cosine value series (Laplacian mode and source mode).
* `intervalNeumannResolverSourceValue_summable_of_sourceDecay`,
  `intervalNeumannResolverRLap_summable_of_sourceDecay`,
  `intervalNeumannResolverR_value_summable_of_sourceDecay` — pointwise `ℓ¹`
  summability of each series under `SourceCoeffQuadraticDecay`.
* `resolverCoeff_re_lap_eq` — the coefficient-form recursion
  `(v̂_k).re · (kπ)² = (â_k).re − p.μ · (v̂_k).re`.
* `intervalNeumannResolverRLap_elliptic_identity` — the strong identity (★)
  at every interval point, under `SourceCoeffQuadraticDecay`.
* `intervalNeumannResolverRLap_diff_eq` — the difference form of (★) used by
  the chemotaxis flux Lipschitz scaffold.

No `sorry`, no `admit`, no custom `axiom`.
-/
import ShenWork.PDE.IntervalNeumannEllipticResolverR
import ShenWork.PDE.IntervalCosineCoeffDecay
import ShenWork.PDE.IntervalResolverGradientBridge
import ShenWork.Paper2.IntervalDomainL2UEnergyInequality

open MeasureTheory
open ShenWork.IntervalDomain ShenWork.CosineSpectrum
open ShenWork.HeatKernelGradientEstimates
open ShenWork.Paper3 (unitIntervalNeumannSpectrum)
open scoped Topology BigOperators

namespace ShenWork.IntervalResolverLaplacianBridge

noncomputable section

open ShenWork.Paper2 ShenWork.PDE ShenWork.IntervalResolverGradientBridge

/-! ## Definitions: the two cosine value series at the Laplacian level -/

/-- **Laplacian-mode value series.**  Termwise second-derivative of the resolver
cosine series:

  `RLap p u y := ∑' k, (v̂_k).re · (−(k π)² · cos(k π y))`. -/
def intervalNeumannResolverRLap (p : CM2Params)
    (u : intervalDomainPoint → ℝ) :
    intervalDomainPoint → ℝ :=
  fun y =>
    ∑' k : ℕ,
      (intervalNeumannResolverCoeff p u k).re *
        (-(((k : ℝ) * Real.pi) ^ 2) * Real.cos ((k : ℝ) * Real.pi * y.1))

/-- **Source value series.**  Cosine series with the *source* coefficients
`â_k = intervalNeumannResolverSourceCoeff p u k`:

  `sourceValue p u y := ∑' k, (â_k).re · cos(k π y)`. -/
def intervalNeumannResolverSourceValue (p : CM2Params)
    (u : intervalDomainPoint → ℝ) :
    intervalDomainPoint → ℝ :=
  fun y =>
    ∑' k : ℕ,
      (intervalNeumannResolverSourceCoeff p u k).re *
        Real.cos ((k : ℝ) * Real.pi * y.1)

/-! ## Weierstrass-M summability from `SourceCoeffQuadraticDecay`

The source-decay input from `ShenWork.Paper2` gives `|(â_k).re| ≤ C/(kπ)²`
for `k ≥ 1`; the source-value cosine series is dominated termwise by
`|(â_k).re|`, giving a `1/k²` majorant, summable.

The Laplacian-mode series picks up the eigenvalue factor `(kπ)²` in front of
each coefficient, but the resolver multiplier `1/(μ + λ_k)` ≤ `1/(kπ)²` exactly
cancels it modulo a constant: termwise `|v̂_k|·(kπ)² ≤ |â_k|/(μ+λ_k)·(kπ)² ≤
|â_k| ≤ C/(kπ)²`, again a `1/k²` majorant. -/

/-- **Source value series ℓ¹-summable at every point**, under
`SourceCoeffQuadraticDecay`.  The decay `|(â_k).re| ≤ C/(kπ)²` gives a uniform
`(C/π²)·1/k²` majorant on each cosine term. -/
theorem intervalNeumannResolverSourceValue_summable_of_sourceDecay
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hdecay : SourceCoeffQuadraticDecay p u) (y : intervalDomainPoint) :
    Summable fun k : ℕ =>
      (intervalNeumannResolverSourceCoeff p u k).re *
        Real.cos ((k : ℝ) * Real.pi * y.1) := by
  classical
  apply Summable.of_norm
  rw [← summable_nat_add_iff 1]
  have hmaj : Summable fun k : ℕ =>
      (hdecay.C / Real.pi ^ 2) * (1 / ((k : ℝ) + 1) ^ 2) := by
    have hp2 : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2 := by
      have := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
      simpa using (summable_nat_add_iff (f := fun k : ℕ => 1 / (k : ℝ) ^ 2) 1).2 this
    exact hp2.mul_left _
  refine Summable.of_nonneg_of_le (fun k => by positivity) ?_ hmaj
  intro k
  set m : ℕ := k + 1 with hm
  have hm1 : 1 ≤ m := Nat.le_add_left 1 k
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm1
  have hmpi_pos : (0 : ℝ) < (m : ℝ) * Real.pi := mul_pos hmpos Real.pi_pos
  have hmpi_sq_pos : (0 : ℝ) < ((m : ℝ) * Real.pi) ^ 2 := by positivity
  have hsrc := hdecay.decay m hm1
  have hcos : |Real.cos ((m : ℝ) * Real.pi * y.1)| ≤ 1 := Real.abs_cos_le_one _
  have hstep1 : ‖(intervalNeumannResolverSourceCoeff p u m).re *
        Real.cos ((m : ℝ) * Real.pi * y.1)‖ ≤
      |(intervalNeumannResolverSourceCoeff p u m).re| := by
    rw [Real.norm_eq_abs, abs_mul]
    calc |(intervalNeumannResolverSourceCoeff p u m).re| *
            |Real.cos ((m : ℝ) * Real.pi * y.1)|
        ≤ |(intervalNeumannResolverSourceCoeff p u m).re| * 1 :=
          mul_le_mul_of_nonneg_left hcos (abs_nonneg _)
      _ = |(intervalNeumannResolverSourceCoeff p u m).re| := mul_one _
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hk1pos : (0 : ℝ) < ((k : ℝ) + 1) := by positivity
  have hmcast : (m : ℝ) = (k : ℝ) + 1 := by rw [hm]; push_cast; ring
  have htarget : hdecay.C / ((m : ℝ) * Real.pi) ^ 2 =
      hdecay.C / Real.pi ^ 2 * (1 / ((k : ℝ) + 1) ^ 2) := by
    rw [hmcast]
    have hne : ((k : ℝ) + 1) ≠ 0 := ne_of_gt hk1pos
    field_simp
  calc ‖(intervalNeumannResolverSourceCoeff p u m).re *
            Real.cos ((m : ℝ) * Real.pi * y.1)‖
      ≤ |(intervalNeumannResolverSourceCoeff p u m).re| := hstep1
    _ ≤ hdecay.C / ((m : ℝ) * Real.pi) ^ 2 := hsrc
    _ = hdecay.C / Real.pi ^ 2 * (1 / ((k : ℝ) + 1) ^ 2) := htarget

/-- **Laplacian-mode value series ℓ¹-summable at every point**, under
`SourceCoeffQuadraticDecay`.  Termwise: `|v̂_k|·(kπ)² ≤ |â_k|/(μ+λ_k)·(kπ)² ≤
|â_k| ≤ C/(kπ)²`, giving a `1/k²` majorant. -/
theorem intervalNeumannResolverRLap_summable_of_sourceDecay
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hdecay : SourceCoeffQuadraticDecay p u) (y : intervalDomainPoint) :
    Summable fun k : ℕ =>
      (intervalNeumannResolverCoeff p u k).re *
        (-(((k : ℝ) * Real.pi) ^ 2) * Real.cos ((k : ℝ) * Real.pi * y.1)) := by
  classical
  apply Summable.of_norm
  rw [← summable_nat_add_iff 1]
  have hmaj : Summable fun k : ℕ =>
      (hdecay.C / Real.pi ^ 2) * (1 / ((k : ℝ) + 1) ^ 2) := by
    have hp2 : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2 := by
      have := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
      simpa using (summable_nat_add_iff (f := fun k : ℕ => 1 / (k : ℝ) ^ 2) 1).2 this
    exact hp2.mul_left _
  refine Summable.of_nonneg_of_le (fun k => by positivity) ?_ hmaj
  intro k
  set m : ℕ := k + 1 with hm
  have hm1 : 1 ≤ m := Nat.le_add_left 1 k
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm1
  have hmpi_pos : (0 : ℝ) < (m : ℝ) * Real.pi := mul_pos hmpos Real.pi_pos
  have hmpi_sq_pos : (0 : ℝ) < ((m : ℝ) * Real.pi) ^ 2 := by positivity
  have hden_pos : 0 < p.μ + unitIntervalNeumannSpectrum.eigenvalue m :=
    intervalNeumannResolver_denom_pos p m
  have hlam : unitIntervalNeumannSpectrum.eigenvalue m = (m : ℝ) ^ 2 * Real.pi ^ 2 := rfl
  have hdenlow : ((m : ℝ) * Real.pi) ^ 2 ≤ p.μ + unitIntervalNeumannSpectrum.eigenvalue m := by
    rw [hlam]; nlinarith [p.hμ.le, sq_nonneg ((m:ℝ) * Real.pi)]
  have hsrc := hdecay.decay m hm1
  have hcos : |Real.cos ((m : ℝ) * Real.pi * y.1)| ≤ 1 := Real.abs_cos_le_one _
  have hnegmsq : |(-(((m : ℝ) * Real.pi) ^ 2) * Real.cos ((m : ℝ) * Real.pi * y.1))|
      ≤ ((m : ℝ) * Real.pi) ^ 2 := by
    rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ ((m:ℝ) * Real.pi) ^ 2)]
    calc ((m : ℝ) * Real.pi) ^ 2 * |Real.cos ((m : ℝ) * Real.pi * y.1)|
        ≤ ((m : ℝ) * Real.pi) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hcos (by positivity)
      _ = ((m : ℝ) * Real.pi) ^ 2 := mul_one _
  -- `|v̂_m| ≤ (C/(mπ)²)/(mπ)²`.
  have hres_abs : |(intervalNeumannResolverCoeff p u m).re| ≤
      hdecay.C / ((m : ℝ) * Real.pi) ^ 2 / ((m : ℝ) * Real.pi) ^ 2 := by
    rw [resolverCoeff_re_eq, abs_div, abs_of_pos hden_pos]
    have hden_inv : 1 / (p.μ + unitIntervalNeumannSpectrum.eigenvalue m)
        ≤ 1 / ((m : ℝ) * Real.pi) ^ 2 :=
      one_div_le_one_div_of_le hmpi_sq_pos hdenlow
    rw [div_eq_mul_one_div, div_eq_mul_one_div (hdecay.C / ((m : ℝ) * Real.pi) ^ 2)]
    apply mul_le_mul hsrc hden_inv (by positivity)
      (by have := hdecay.C_nonneg; positivity)
  have hprod : ‖(intervalNeumannResolverCoeff p u m).re *
        (-(((m : ℝ) * Real.pi) ^ 2) * Real.cos ((m : ℝ) * Real.pi * y.1))‖
      ≤ |(intervalNeumannResolverCoeff p u m).re| * ((m : ℝ) * Real.pi) ^ 2 := by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left hnegmsq (abs_nonneg _)
  have hbig : |(intervalNeumannResolverCoeff p u m).re| * ((m : ℝ) * Real.pi) ^ 2 ≤
      hdecay.C / ((m : ℝ) * Real.pi) ^ 2 := by
    have hbase := mul_le_mul_of_nonneg_right hres_abs
      (by positivity : (0:ℝ) ≤ ((m:ℝ)*Real.pi)^2)
    have hpne : ((m : ℝ) * Real.pi) ^ 2 ≠ 0 := ne_of_gt hmpi_sq_pos
    have hrw : hdecay.C / ((m : ℝ) * Real.pi) ^ 2 / ((m : ℝ) * Real.pi) ^ 2 *
          ((m : ℝ) * Real.pi) ^ 2
        = hdecay.C / ((m : ℝ) * Real.pi) ^ 2 := by
      field_simp
    rw [hrw] at hbase
    exact hbase
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hk1pos : (0 : ℝ) < ((k : ℝ) + 1) := by positivity
  have hmcast : (m : ℝ) = (k : ℝ) + 1 := by rw [hm]; push_cast; ring
  have htarget : hdecay.C / ((m : ℝ) * Real.pi) ^ 2 =
      hdecay.C / Real.pi ^ 2 * (1 / ((k : ℝ) + 1) ^ 2) := by
    rw [hmcast]
    have hne : ((k : ℝ) + 1) ≠ 0 := ne_of_gt hk1pos
    field_simp
  calc ‖(intervalNeumannResolverCoeff p u m).re *
            (-(((m : ℝ) * Real.pi) ^ 2) * Real.cos ((m : ℝ) * Real.pi * y.1))‖
      ≤ |(intervalNeumannResolverCoeff p u m).re| * ((m : ℝ) * Real.pi) ^ 2 := hprod
    _ ≤ hdecay.C / ((m : ℝ) * Real.pi) ^ 2 := hbig
    _ = hdecay.C / Real.pi ^ 2 * (1 / ((k : ℝ) + 1) ^ 2) := htarget

/-- **Resolver value series ℓ¹-summable at every point**, under
`SourceCoeffQuadraticDecay`.  Needed for `tsum`-arithmetic in the elliptic
identity below. -/
theorem intervalNeumannResolverR_value_summable_of_sourceDecay
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hdecay : SourceCoeffQuadraticDecay p u) (y : intervalDomainPoint) :
    Summable fun k : ℕ =>
      (intervalNeumannResolverCoeff p u k).re *
        unitIntervalCosineMode k y.1 := by
  classical
  apply Summable.of_norm
  rw [← summable_nat_add_iff 1]
  have hmaj : Summable fun k : ℕ =>
      (hdecay.C / Real.pi ^ 2) * (1 / ((k : ℝ) + 1) ^ 2) := by
    have hp2 : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2 := by
      have := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
      simpa using (summable_nat_add_iff (f := fun k : ℕ => 1 / (k : ℝ) ^ 2) 1).2 this
    exact hp2.mul_left _
  refine Summable.of_nonneg_of_le (fun k => by positivity) ?_ hmaj
  intro k
  set m : ℕ := k + 1 with hm
  have hm1 : 1 ≤ m := Nat.le_add_left 1 k
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm1
  have hmpi_pos : (0 : ℝ) < (m : ℝ) * Real.pi := mul_pos hmpos Real.pi_pos
  have hmpi_sq_pos : (0 : ℝ) < ((m : ℝ) * Real.pi) ^ 2 := by positivity
  have hden_pos : 0 < p.μ + unitIntervalNeumannSpectrum.eigenvalue m :=
    intervalNeumannResolver_denom_pos p m
  have hlam : unitIntervalNeumannSpectrum.eigenvalue m = (m : ℝ) ^ 2 * Real.pi ^ 2 := rfl
  have hdenlow : ((m : ℝ) * Real.pi) ^ 2 ≤ p.μ + unitIntervalNeumannSpectrum.eigenvalue m := by
    rw [hlam]; nlinarith [p.hμ.le, sq_nonneg ((m:ℝ) * Real.pi)]
  have hsrc := hdecay.decay m hm1
  have hcos : |unitIntervalCosineMode m y.1| ≤ 1 := by
    unfold unitIntervalCosineMode; exact Real.abs_cos_le_one _
  -- `|v̂_m| ≤ |â_m|/(μ+λ_m) ≤ (C/(mπ)²)/(μ+λ_m) ≤ (C/(mπ)²)/(mπ)²` for sharp form;
  -- here we use the slightly cruder bound: `1/(μ+λ_m) ≤ 1/(mπ)²` so `|v̂_m|`
  -- is dominated by `C/(mπ)² · 1/(mπ)² · (mπ)² = C/(mπ)²` after cancelling.
  -- Cleaner: directly bound `|v̂_m| ≤ |â_m| · 1/(mπ)² ≤ (C/(mπ)²) · 1/(mπ)²`, then
  -- use `(mπ)² ≥ π² > 1` for `m ≥ 1` (since `π > 1`) — but π > 1 is a Mathlib fact
  -- so this works.  We take the simpler route via `inv_le_one_of_one_le₀`.
  have hres_abs : |(intervalNeumannResolverCoeff p u m).re| ≤
      hdecay.C / ((m : ℝ) * Real.pi) ^ 2 / ((m : ℝ) * Real.pi) ^ 2 := by
    rw [resolverCoeff_re_eq, abs_div, abs_of_pos hden_pos]
    have hden_inv : 1 / (p.μ + unitIntervalNeumannSpectrum.eigenvalue m)
        ≤ 1 / ((m : ℝ) * Real.pi) ^ 2 :=
      one_div_le_one_div_of_le hmpi_sq_pos hdenlow
    rw [div_eq_mul_one_div, div_eq_mul_one_div (hdecay.C / ((m : ℝ) * Real.pi) ^ 2)]
    apply mul_le_mul hsrc hden_inv (by positivity)
      (by have := hdecay.C_nonneg; positivity)
  -- collapse `((C/(mπ)²)/(mπ)²) ≤ C/(mπ)²` via `(mπ)² ≥ 1` (since `m·π ≥ 1·π > 1`).
  have hmpi_ge_one : (1 : ℝ) ≤ ((m : ℝ) * Real.pi) ^ 2 := by
    have hpi_ge : (1 : ℝ) ≤ Real.pi := Real.pi_gt_three.le.trans' (by norm_num)
    have hmge : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have : (1 : ℝ) ≤ (m : ℝ) * Real.pi := by
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ (m : ℝ) * Real.pi :=
              mul_le_mul hmge hpi_ge (by norm_num) (by linarith)
    nlinarith [this]
  have hcollapse : hdecay.C / ((m : ℝ) * Real.pi) ^ 2 / ((m : ℝ) * Real.pi) ^ 2 ≤
      hdecay.C / ((m : ℝ) * Real.pi) ^ 2 := by
    have hC : 0 ≤ hdecay.C / ((m : ℝ) * Real.pi) ^ 2 := by
      apply div_nonneg hdecay.C_nonneg; positivity
    -- `a/b ≤ a` iff `b ≥ 1` and `a ≥ 0`.
    rw [div_le_iff₀ hmpi_sq_pos]
    calc hdecay.C / ((m : ℝ) * Real.pi) ^ 2
        = hdecay.C / ((m : ℝ) * Real.pi) ^ 2 * 1 := (mul_one _).symm
      _ ≤ hdecay.C / ((m : ℝ) * Real.pi) ^ 2 * ((m : ℝ) * Real.pi) ^ 2 :=
            mul_le_mul_of_nonneg_left hmpi_ge_one hC
  have hprod : ‖(intervalNeumannResolverCoeff p u m).re *
        unitIntervalCosineMode m y.1‖
      ≤ |(intervalNeumannResolverCoeff p u m).re| := by
    rw [Real.norm_eq_abs, abs_mul]
    calc |(intervalNeumannResolverCoeff p u m).re| * |unitIntervalCosineMode m y.1|
        ≤ |(intervalNeumannResolverCoeff p u m).re| * 1 :=
          mul_le_mul_of_nonneg_left hcos (abs_nonneg _)
      _ = |(intervalNeumannResolverCoeff p u m).re| := mul_one _
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hk1pos : (0 : ℝ) < ((k : ℝ) + 1) := by positivity
  have hmcast : (m : ℝ) = (k : ℝ) + 1 := by rw [hm]; push_cast; ring
  have htarget : hdecay.C / ((m : ℝ) * Real.pi) ^ 2 =
      hdecay.C / Real.pi ^ 2 * (1 / ((k : ℝ) + 1) ^ 2) := by
    rw [hmcast]
    have hne : ((k : ℝ) + 1) ≠ 0 := ne_of_gt hk1pos
    field_simp
  calc ‖(intervalNeumannResolverCoeff p u m).re * unitIntervalCosineMode m y.1‖
      ≤ |(intervalNeumannResolverCoeff p u m).re| := hprod
    _ ≤ hdecay.C / ((m : ℝ) * Real.pi) ^ 2 / ((m : ℝ) * Real.pi) ^ 2 := hres_abs
    _ ≤ hdecay.C / ((m : ℝ) * Real.pi) ^ 2 := hcollapse
    _ = hdecay.C / Real.pi ^ 2 * (1 / ((k : ℝ) + 1) ^ 2) := htarget

/-! ## The strong elliptic identity (★) at the value-series level

The coefficient-form identity `(p.μ + λ_k) · v̂_k = â_k` (real parts) gives
termwise `v̂_k · (kπ)² = â_k − p.μ · v̂_k`, since `λ_k = (kπ)²`.  Multiplying by
`−cos(kπy)` and summing across `k` (all three series are `ℓ¹`-summable by the
Weierstrass-M bounds above) yields

  `∑' v̂_k · (−(kπ)² · cos(kπy)) = p.μ · ∑' v̂_k · cos(kπy)  −  ∑' â_k · cos(kπy)`.

This is the spectral form of the elliptic equation `−Δ(R u) + p.μ·(R u) = source`,
rearranged as `Δ(R u) = p.μ·(R u) − source`, evaluated at `y`. -/

/-- Coefficient-form recursion: `(v̂_k).re · (kπ)² = (â_k).re − p.μ · (v̂_k).re`. -/
lemma resolverCoeff_re_lap_eq
    (p : CM2Params) (u : intervalDomainPoint → ℝ) (k : ℕ) :
    (intervalNeumannResolverCoeff p u k).re * ((k : ℝ) * Real.pi) ^ 2 =
      (intervalNeumannResolverSourceCoeff p u k).re -
        p.μ * (intervalNeumannResolverCoeff p u k).re := by
  have hellRe : (p.μ + unitIntervalNeumannSpectrum.eigenvalue k) *
        (intervalNeumannResolverCoeff p u k).re =
      (intervalNeumannResolverSourceCoeff p u k).re := by
    have hcast :
        ((p.μ : ℂ) + (unitIntervalNeumannSpectrum.eigenvalue k : ℂ)) =
          (((p.μ + unitIntervalNeumannSpectrum.eigenvalue k : ℝ)) : ℂ) := by
      push_cast; ring
    have hk := congrArg Complex.re (intervalNeumannResolverCoeff_elliptic p u k)
    rw [hcast, Complex.re_ofReal_mul] at hk
    exact hk
  have hlam : unitIntervalNeumannSpectrum.eigenvalue k = ((k : ℝ) * Real.pi) ^ 2 := by
    show ((k : ℝ) ^ 2 * Real.pi ^ 2) = _
    ring
  rw [hlam] at hellRe
  linarith

/-- **Strong elliptic identity (★).**

`RLap p u y = p.μ · R p u y  −  sourceValue p u y` at every interval point `y`,
under `SourceCoeffQuadraticDecay`.

This is the spectral form of the elliptic equation `−Δ(R u) + p.μ · (R u) = source`,
i.e., `Δ(R u) = p.μ · (R u) − source`, evaluated termwise at `y`. -/
theorem intervalNeumannResolverRLap_elliptic_identity
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hdecay : SourceCoeffQuadraticDecay p u) (y : intervalDomainPoint) :
    intervalNeumannResolverRLap p u y =
      p.μ * intervalNeumannResolverR p u y -
        intervalNeumannResolverSourceValue p u y := by
  classical
  -- summability of source value and resolver value series.
  have hSV := intervalNeumannResolverSourceValue_summable_of_sourceDecay hdecay y
  have hRV := intervalNeumannResolverR_value_summable_of_sourceDecay hdecay y
  -- termwise identity at the value level.
  have hterm : ∀ k : ℕ,
      (intervalNeumannResolverCoeff p u k).re *
          (-(((k : ℝ) * Real.pi) ^ 2) * Real.cos ((k : ℝ) * Real.pi * y.1))
        = p.μ *
            ((intervalNeumannResolverCoeff p u k).re * unitIntervalCosineMode k y.1) -
          (intervalNeumannResolverSourceCoeff p u k).re *
            Real.cos ((k : ℝ) * Real.pi * y.1) := by
    intro k
    have hcoeff := resolverCoeff_re_lap_eq p u k
    unfold unitIntervalCosineMode
    -- LHS = v̂.re · (−(kπ)²·cos) = −v̂.re·(kπ)²·cos = −(â.re − μ·v̂.re)·cos
    --     = μ·v̂.re·cos − â.re·cos.
    linear_combination -Real.cos ((k : ℝ) * Real.pi * y.1) * hcoeff
  -- assemble.
  unfold intervalNeumannResolverRLap intervalNeumannResolverR
    intervalNeumannResolverSourceValue
  -- The R sum needs `unitIntervalCosineMode k y.1` form; that's its def.
  have hRV' :
      Summable fun k : ℕ =>
        p.μ * ((intervalNeumannResolverCoeff p u k).re *
          unitIntervalCosineMode k y.1) := hRV.mul_left _
  -- compute the rearranged tsum via Summable.tsum_sub
  have hsum_split :
      (∑' k : ℕ, (p.μ *
          ((intervalNeumannResolverCoeff p u k).re * unitIntervalCosineMode k y.1) -
        (intervalNeumannResolverSourceCoeff p u k).re *
          Real.cos ((k : ℝ) * Real.pi * y.1)))
        = (∑' k : ℕ, p.μ *
              ((intervalNeumannResolverCoeff p u k).re * unitIntervalCosineMode k y.1)) -
          (∑' k : ℕ, (intervalNeumannResolverSourceCoeff p u k).re *
              Real.cos ((k : ℝ) * Real.pi * y.1)) :=
    hRV'.tsum_sub hSV
  rw [tsum_congr hterm, hsum_split, tsum_mul_left]

/-- **Difference form of (★).**

For two trajectory snapshots `u₁, u₂` each satisfying `SourceCoeffQuadraticDecay`,
the Laplacian-mode series difference at any interval point `y` equals

  `(RLap u₁ − RLap u₂)(y) = p.μ · (R u₁ − R u₂)(y) − (sourceValue u₁ − sourceValue u₂)(y)`.

This is the value-series form of `Δ(R u₁) − Δ(R u₂) = p.μ · (R u₁ − R u₂) − (g₁ − g₂)`
that the chemotaxis flux Lipschitz scaffold consumes. -/
theorem intervalNeumannResolverRLap_diff_eq
    {p : CM2Params} {u₁ u₂ : intervalDomainPoint → ℝ}
    (hdecay₁ : SourceCoeffQuadraticDecay p u₁)
    (hdecay₂ : SourceCoeffQuadraticDecay p u₂)
    (y : intervalDomainPoint) :
    intervalNeumannResolverRLap p u₁ y - intervalNeumannResolverRLap p u₂ y =
      p.μ * (intervalNeumannResolverR p u₁ y - intervalNeumannResolverR p u₂ y) -
        (intervalNeumannResolverSourceValue p u₁ y -
          intervalNeumannResolverSourceValue p u₂ y) := by
  rw [intervalNeumannResolverRLap_elliptic_identity hdecay₁ y,
      intervalNeumannResolverRLap_elliptic_identity hdecay₂ y]
  ring

/-- **Pointwise sup bound on `|RLap u₁ − RLap u₂|`** from the elliptic identity.
Once `R u_i` and `sourceValue u_i` are sup-Lipschitz in trajectory difference
(via existing infrastructure for `R`, and via Fourier inversion + closed-domain
positivity for `sourceValue = p.ν·u^γ` pointwise for solutions), this gives
the chemotaxis flux Lipschitz input by triangle inequality. -/
theorem intervalNeumannResolverRLap_diff_abs_le
    {p : CM2Params} {u₁ u₂ : intervalDomainPoint → ℝ}
    (hdecay₁ : SourceCoeffQuadraticDecay p u₁)
    (hdecay₂ : SourceCoeffQuadraticDecay p u₂)
    (y : intervalDomainPoint) :
    |intervalNeumannResolverRLap p u₁ y - intervalNeumannResolverRLap p u₂ y| ≤
      p.μ * |intervalNeumannResolverR p u₁ y - intervalNeumannResolverR p u₂ y| +
        |intervalNeumannResolverSourceValue p u₁ y -
          intervalNeumannResolverSourceValue p u₂ y| := by
  rw [intervalNeumannResolverRLap_diff_eq hdecay₁ hdecay₂]
  calc |p.μ * (intervalNeumannResolverR p u₁ y - intervalNeumannResolverR p u₂ y) -
          (intervalNeumannResolverSourceValue p u₁ y -
            intervalNeumannResolverSourceValue p u₂ y)|
      ≤ |p.μ * (intervalNeumannResolverR p u₁ y - intervalNeumannResolverR p u₂ y)| +
          |intervalNeumannResolverSourceValue p u₁ y -
            intervalNeumannResolverSourceValue p u₂ y| := abs_sub _ _
    _ = p.μ * |intervalNeumannResolverR p u₁ y - intervalNeumannResolverR p u₂ y| +
          |intervalNeumannResolverSourceValue p u₁ y -
            intervalNeumannResolverSourceValue p u₂ y| := by
          rw [abs_mul, abs_of_pos p.hμ]

end

end ShenWork.IntervalResolverLaplacianBridge
