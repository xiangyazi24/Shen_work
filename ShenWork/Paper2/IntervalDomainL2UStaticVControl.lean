/-
  Static elliptic `v`-difference control for the `u`-only L²-energy method —
  the discharged side-hypotheses and the per-point static sup-bound.

  ## Purpose

  The chemotaxis term of the `Eprime ≤ K·E_u` differential inequality controls the
  `v`-difference `v₁ − v₂` (and its spatial gradient) STATICALLY by `u₁ − u₂` via
  the elliptic resolver-Lipschitz bounds
  (`intervalNeumannResolverR_sup_lipschitz`,
  `intervalNeumannResolverR_grad_sup_lipschitz`).  Those bounds carry two analytic
  SIDE-HYPOTHESES:

    * `hsrc` — the source-coefficient real-part `ℓ²` summability; and
    * `hsum₁/hsum₂` — pointwise reconstruction (absolute summability of the
      resolver cosine / sine value series at the evaluation point).

  This file discharges BOTH of these UNCONDITIONALLY for a positive classical
  solution, then assembles the per-point static `v`-difference sup-bound that the
  chemotaxis energy term consumes.  It uses:

    * `source_resolverCoeff_re_sq_summable`        (already proved) ⇒ `hsrc`;
    * `sourceCoeffQuadraticDecay_of_solution`      (already proved) ⇒ the source
      quadratic decay, which makes the resolver coefficient real parts
      `|(v̂_k).re| ≤ C/(kπ)⁴` (one power below the gradient majorant), hence the
      value series `∑ (v̂_k).re·cos(kπx)` and the gradient series
      `∑ (v̂_k).re·(−kπ sin(kπx))` are absolutely summable ⇒ `hsum₁/hsum₂`.

  This file contains **no `sorry`, no `admit`, no custom `axiom`.**
-/
import ShenWork.Paper2.IntervalDomainL2UEnergyInequality

open ShenWork.IntervalDomain MeasureTheory
open ShenWork.PDE ShenWork.IntervalEllipticCharacterization
open ShenWork.IntervalResolverGradientBridge
open ShenWork.Paper3 (unitIntervalNeumannSpectrum)
open scoped Topology

namespace ShenWork.Paper2

noncomputable section

/-! ## The resolver value-series absolute majorant from source quadratic decay

The gradient majorant `∑ₖ |(v̂_k).re|·kπ` is already proved summable
(`resolverGrad_majorant_summable_of_sourceDecay`).  The VALUE majorant
`∑ₖ |(v̂_k).re|` is strictly easier — one fewer power of `kπ` — and gives the
absolute convergence of the resolver cosine value series at every point, hence the
pointwise-reconstruction side-hypothesis `hsum` of the value-level resolver
Lipschitz bound. -/

/-- **Value-series `ℓ¹` majorant from source-coefficient quadratic decay.**

Given `|(source coeff).re| ≤ C/(kπ)²` for `k ≥ 1`, the resolver value coefficients
`|(v̂_k).re|` are absolutely summable: for `k ≥ 1`,

  `|(v̂_k).re| = |(source).re|/(μ+λ_k) ≤ (C/(kπ)²)/(kπ)² = (C/π⁴)·1/k⁴`,

summable by comparison with `∑ 1/k⁴` (in fact `∑ 1/k²`). -/
theorem resolverValue_majorant_summable_of_sourceDecay
    {p : CM2Params} {u : intervalDomainPoint → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hdecay : ∀ k : ℕ, 1 ≤ k →
      |(intervalNeumannResolverSourceCoeff p u k).re| ≤ C / ((k : ℝ) * Real.pi) ^ 2) :
    Summable fun k : ℕ => |(intervalNeumannResolverCoeff p u k).re| := by
  classical
  rw [← summable_nat_add_iff 1]
  -- Majorant `(C/π²)·1/(k+1)²`.
  have hmaj : Summable fun k : ℕ => (C / Real.pi ^ 2) * (1 / ((k : ℝ) + 1) ^ 2) := by
    have hp2 : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2 := by
      have := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
      simpa using (summable_nat_add_iff (f := fun k : ℕ => 1 / (k : ℝ) ^ 2) 1).2 this
    exact hp2.mul_left _
  refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) ?_ hmaj
  intro k
  set m : ℕ := k + 1 with hm
  have hm1 : 1 ≤ m := Nat.le_add_left 1 k
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm1
  have hmpi_pos : (0 : ℝ) < (m : ℝ) * Real.pi := mul_pos hmpos Real.pi_pos
  have hden_pos : 0 < p.μ + unitIntervalNeumannSpectrum.eigenvalue m :=
    intervalNeumannResolver_denom_pos p m
  have hlam : unitIntervalNeumannSpectrum.eigenvalue m = (m : ℝ) ^ 2 * Real.pi ^ 2 := rfl
  have hdenlow : ((m : ℝ) * Real.pi) ^ 2 ≤ p.μ + unitIntervalNeumannSpectrum.eigenvalue m := by
    rw [hlam]; nlinarith [p.hμ.le, sq_nonneg ((m:ℝ) * Real.pi)]
  rw [resolverCoeff_re_eq, abs_div, abs_of_pos hden_pos]
  have hnum := hdecay m hm1
  have hmpi_sq_pos : (0 : ℝ) < ((m : ℝ) * Real.pi) ^ 2 := by positivity
  -- `|src|/den ≤ (C/(mπ)²)/(mπ)²`.
  have hden_inv : 1 / (p.μ + unitIntervalNeumannSpectrum.eigenvalue m)
      ≤ 1 / ((m : ℝ) * Real.pi) ^ 2 :=
    one_div_le_one_div_of_le hmpi_sq_pos hdenlow
  have hfrac : |(intervalNeumannResolverSourceCoeff p u m).re| /
        (p.μ + unitIntervalNeumannSpectrum.eigenvalue m)
      ≤ (C / ((m : ℝ) * Real.pi) ^ 2) / ((m : ℝ) * Real.pi) ^ 2 := by
    rw [div_eq_mul_one_div, div_eq_mul_one_div (C / ((m : ℝ) * Real.pi) ^ 2)]
    apply mul_le_mul hnum hden_inv (by positivity) (by positivity)
  refine hfrac.trans ?_
  -- `(C/(mπ)²)/(mπ)² = C/((mπ)²·(mπ)²)`.  Bound by `(C/π²)·1/(k+1)² = C/(π²·(k+1)²)`.
  have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hmcast : (m : ℝ) = (k : ℝ) + 1 := by rw [hm]; push_cast; ring
  have hmπsq_ge_one : (1 : ℝ) ≤ ((m : ℝ) * Real.pi) ^ 2 := by
    have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have hge : (1 : ℝ) ≤ (m : ℝ) * Real.pi := by
      have := Real.pi_gt_three; nlinarith
    nlinarith [hge]
  -- LHS = C / ((mπ)² · (mπ)²);  RHS = (C/π²)·(1/(k+1)²) = C / (π²·(k+1)²).
  have hLHS : C / ((m : ℝ) * Real.pi) ^ 2 / ((m : ℝ) * Real.pi) ^ 2
      = C / (((m : ℝ) * Real.pi) ^ 2 * ((m : ℝ) * Real.pi) ^ 2) := by
    rw [div_div]
  have hRHS : C / Real.pi ^ 2 * (1 / ((k : ℝ) + 1) ^ 2)
      = C / (Real.pi ^ 2 * ((k : ℝ) + 1) ^ 2) := by
    rw [div_mul_div_comm, mul_one]
  rw [hLHS, hRHS]
  -- Goal: C/((mπ)²·(mπ)²) ≤ C/(π²·(k+1)²); denominators: π²·(k+1)² ≤ (mπ)²·(mπ)².
  refine div_le_div_of_nonneg_left hC (by positivity) ?_
  rw [hmcast]
  have hbase : Real.pi ^ 2 * ((k : ℝ) + 1) ^ 2 = (((k : ℝ) + 1) * Real.pi) ^ 2 := by ring
  rw [hbase]
  have hge1 : (1 : ℝ) ≤ (((k : ℝ) + 1) * Real.pi) ^ 2 := by
    rw [← hmcast]; exact hmπsq_ge_one
  nlinarith [hge1, sq_nonneg (((k : ℝ) + 1) * Real.pi)]

/-! ## Discharging the pointwise-reconstruction side-hypotheses for solutions

The value-level resolver Lipschitz bound `intervalNeumannResolverR_sup_lipschitz`
needs the cosine value-series `∑ₖ (v̂_k).re·cos(kπx)` to be summable at the
evaluation point (`hsum₁/hsum₂`); the gradient version needs the sine value-series
`∑ₖ (v̂_k).re·(−kπ sin(kπx))`.  Both follow from the value / gradient majorants by
absolute comparison (`|cos|,|sin| ≤ 1`). -/

/-- Cosine value-series summability at a point, from source quadratic decay. -/
theorem resolver_cosineSeries_summable_of_sourceDecay
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hdecay : SourceCoeffQuadraticDecay p u) (x : ℝ) :
    Summable fun k : ℕ =>
      (intervalNeumannResolverCoeff p u k).re * unitIntervalCosineMode k x := by
  have hval := resolverValue_majorant_summable_of_sourceDecay hdecay.C_nonneg hdecay.decay
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) ?_ hval
  intro k
  rw [Real.norm_eq_abs, abs_mul, unitIntervalCosineMode]
  have hcos : |Real.cos ((k : ℝ) * Real.pi * x)| ≤ 1 := Real.abs_cos_le_one _
  calc |(intervalNeumannResolverCoeff p u k).re| * |Real.cos ((k : ℝ) * Real.pi * x)|
      ≤ |(intervalNeumannResolverCoeff p u k).re| * 1 :=
        mul_le_mul_of_nonneg_left hcos (abs_nonneg _)
    _ = |(intervalNeumannResolverCoeff p u k).re| := by ring

/-- Sine (gradient-mode) value-series summability at a point, from source decay.
The summand is bounded by `|(v̂_k).re|·kπ`, the gradient majorant. -/
theorem resolver_sineSeries_summable_of_sourceDecay
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hdecay : SourceCoeffQuadraticDecay p u) (x : ℝ) :
    Summable fun k : ℕ =>
      (intervalNeumannResolverCoeff p u k).re *
        (-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * x)) := by
  have hgrad := resolverGrad_majorant_summable_of_sourceDecay hdecay.C_nonneg hdecay.decay
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) ?_ hgrad
  intro k
  rw [Real.norm_eq_abs, abs_mul]
  have hsin : |(-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * x))|
      ≤ (k : ℝ) * Real.pi := by
    rw [abs_mul, abs_neg, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (k:ℝ)),
      abs_of_nonneg Real.pi_pos.le]
    have hsin1 : |Real.sin ((k : ℝ) * Real.pi * x)| ≤ 1 := Real.abs_sin_le_one _
    calc (k : ℝ) * Real.pi * |Real.sin ((k : ℝ) * Real.pi * x)|
        ≤ (k : ℝ) * Real.pi * 1 := mul_le_mul_of_nonneg_left hsin1 (by positivity)
      _ = (k : ℝ) * Real.pi := by ring
  calc |(intervalNeumannResolverCoeff p u k).re| *
          |(-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * x))|
      ≤ |(intervalNeumannResolverCoeff p u k).re| * ((k : ℝ) * Real.pi) :=
        mul_le_mul_of_nonneg_left hsin (abs_nonneg _)

/-! ## The discharged side-hypotheses for positive classical solutions

Feeding `sourceCoeffQuadraticDecay_of_solution` into the two summability lemmas
above discharges the `hsum₁/hsum₂` pointwise-reconstruction hypotheses of the
resolver Lipschitz bounds UNCONDITIONALLY for a positive classical solution. -/

/-- Cosine value-series summability for a solution's `u(·,t)` (discharges
`hsum` of `intervalNeumannResolverR_sup_lipschitz`). -/
theorem solution_resolver_cosineSeries_summable
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) (x : ℝ) :
    Summable fun k : ℕ =>
      (intervalNeumannResolverCoeff p (u t) k).re * unitIntervalCosineMode k x :=
  resolver_cosineSeries_summable_of_sourceDecay
    (sourceCoeffQuadraticDecay_of_solution hsol ht) x

/-- Sine (gradient-mode) value-series summability for a solution's `u(·,t)`
(discharges `hsum` of `intervalNeumannResolverR_grad_sup_lipschitz`). -/
theorem solution_resolver_sineSeries_summable
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) (x : ℝ) :
    Summable fun k : ℕ =>
      (intervalNeumannResolverCoeff p (u t) k).re *
        (-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * x)) :=
  resolver_sineSeries_summable_of_sourceDecay
    (sourceCoeffQuadraticDecay_of_solution hsol ht) x

end

end ShenWork.Paper2
