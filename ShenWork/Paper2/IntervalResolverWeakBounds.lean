/-
  ShenWork/Paper2/IntervalResolverWeakBounds.lean

  T7 existence — **Atom B (foundation)**: elliptic resolver `E = R` bounds that
  hold for an ARBITRARY bounded continuous ball element `u`, NOT only for a
  classical solution.

  The existing quantitative resolver bounds
  (`resolverValue_sup_le_of_ub`, `resolverGrad_sup_le_of_ub`,
   `source_resolverCoeff_re_sq_summable_single`, `source_coeffL2Norm_le`,
   `solution_resolver_cosineSeries_summable`, …) all take
  `hsol : IsPaper2ClassicalSolution …` as a hypothesis — they are *post-hoc*
  bounds and cannot feed the weak mild fixed point (where `u` is just a bounded
  trajectory ball element, not yet a classical solution).

  This file rebuilds the needed summability facts from the WEAK hypotheses
  available in the fixed-point ball — continuity and a sup bound of the lift —
  breaking the circularity:

  * **B1** `resolverSourceCoeff_re_sq_summable_of_continuousOn` — the source
    cosine coefficients are `ℓ²` from CONTINUITY of `u` alone (cosine–Bessel),
    no regularity / `hsol`.  (Mirrors `source_resolverCoeff_re_sq_summable_single`
    with `hsol` replaced by the direct continuity hypothesis.)

  * **B2** `resolver_cosineSeries_summable_of_sourceL2` /
    `resolver_sineSeries_summable_of_sourceL2` — the resolver value/gradient
    cosine series converge ABSOLUTELY from the source being `ℓ²` ALONE (NO
    `O(1/k²)` quadratic decay): `R̂ₖ = âₖ/(μ+λₖ) = âₖ·Wₖ` with both `âₖ` and
    the resolvent weight `Wₖ = 1/(μ+λₖ)` in `ℓ²`, so by AM-GM
    `|âₖ·Wₖ·cos| ≤ (âₖ² + Wₖ²)/2` is summable.  This is the genuine
    circularity-breaker: the post-hoc route needed `SourceCoeffQuadraticDecay`
    (which uses the solution's `C²` regularity); a weak ball element is only
    `ℓ²` (Bessel), and that already suffices for the resolver series.

  No `sorry`, no `admit`, no custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainResolverSupQuantitative

open MeasureTheory intervalIntegral
open ShenWork.IntervalDomain ShenWork.CosineSpectrum
open ShenWork.PDE ShenWork.IntervalEllipticCharacterization
open ShenWork.HeatKernelGradientEstimates
open ShenWork.IntervalResolverGradientBridge
open ShenWork.CosineParsevalBridge
open ShenWork.Paper2
open ShenWork.Paper3 (unitIntervalNeumannSpectrum)
open scoped Topology BigOperators

namespace ShenWork.IntervalResolverWeakBounds

/-! ## B1 — source `ℓ²` from continuity (cosine–Bessel, no `hsol`) -/

/-- **B1.**  For a lift continuous on `[0,1]`, the elliptic-source cosine
coefficients (difference against the zero source) have `ℓ²`-summable real-part
squares.  Cosine–Bessel: the source `ν·u^γ` is continuous, hence in `L²[0,1]`,
hence its Neumann cosine coefficients are `ℓ²`.  No classical-solution
regularity is used — exactly the `hsrc` side hypothesis of
`intervalNeumannResolverR_sup_lipschitz` available in the weak fixed-point ball. -/
theorem resolverSourceCoeff_re_sq_summable_of_continuousOn
    (p : CM2Params) {u : intervalDomainPoint → ℝ}
    (hUcont : ContinuousOn (intervalDomainLift u) (Set.Icc (0:ℝ) 1)) :
    Summable fun k : ℕ =>
      ((intervalNeumannResolverSourceCoeff p u k -
        intervalNeumannResolverSourceCoeff p (fun _ => 0) k).re) ^ 2 := by
  simp only [intervalNeumannResolverSourceCoeff_zero, sub_zero]
  set g : ℝ → ℝ := fun x => p.ν * intervalDomainLift u x ^ p.γ with hg
  have hgcont : ContinuousOn g (Set.Icc (0:ℝ) 1) :=
    continuousOn_const.mul (hUcont.rpow_const (fun x _ => Or.inr p.hγ.le))
  set f : ℝ → ℂ := fun x => ((g x : ℝ) : ℂ) with hf
  have hfcontOn : ContinuousOn f (Set.uIcc (0:ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact Complex.continuous_ofReal.comp_continuousOn hgcont
  have hfint : IntervalIntegrable f volume 0 1 := hfcontOn.intervalIntegrable
  have hfsq : IntervalIntegrable (fun x : ℝ => ‖f x‖ ^ 2) volume 0 1 :=
    ((hfcontOn.norm).pow 2).intervalIntegrable
  have hL2 : MemLp (unitIntervalEvenReflection f) 2
      (volume.restrict (Set.Ioc (-1:ℝ) 1)) :=
    evenReflection_memLp_two_of_continuousOn hgcont
  have hsum := (unitIntervalNeumannCosineCoeff_l2_bound hfint hL2 hfsq).1
  refine hsum.congr ?_
  intro k
  have hcoeff : (intervalNeumannResolverSourceCoeff p u k).re =
      unitIntervalNeumannCosineCoeff f k := by
    simp only [intervalNeumannResolverSourceCoeff, hf, hg, Complex.ofReal_re]
  rw [hcoeff]

/-! ## B2 — resolver series absolutely summable from source `ℓ²` (no decay) -/

/-- **B2 (value series).**  The resolver VALUE cosine series converges
absolutely from the source coefficients being `ℓ²` alone.  `R̂ₖ.re = âₖ.re·Wₖ`
with `Wₖ = 1/(μ+λₖ)` the resolvent weight (`ℓ²`), so AM-GM gives
`|R̂ₖ.re·cos(kπx)| ≤ (âₖ.re² + Wₖ²)/2`, a summable majorant. -/
theorem resolver_cosineSeries_summable_of_sourceL2
    (p : CM2Params) {u : intervalDomainPoint → ℝ}
    (hl2 : Summable fun k : ℕ => ((intervalNeumannResolverSourceCoeff p u k).re) ^ 2)
    (x : ℝ) :
    Summable fun k : ℕ =>
      (intervalNeumannResolverCoeff p u k).re * unitIntervalCosineMode k x := by
  rw [← summable_abs_iff]
  have hw := intervalNeumannResolverWeight_sq_summable p
  refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) ?_
    ((hl2.add hw).div_const 2)
  intro k
  have hd : 0 < p.μ + unitIntervalNeumannSpectrum.eigenvalue k :=
    intervalNeumannResolver_denom_pos p k
  set s := (intervalNeumannResolverSourceCoeff p u k).re with hs
  set W := intervalNeumannResolverWeight p k with hW
  have hWnn : 0 ≤ W := by rw [hW, intervalNeumannResolverWeight]; positivity
  have hcos : |unitIntervalCosineMode k x| ≤ 1 := by
    rw [unitIntervalCosineMode]; exact Real.abs_cos_le_one _
  have hWeq : W = 1 / (p.μ + unitIntervalNeumannSpectrum.eigenvalue k) := rfl
  calc |(intervalNeumannResolverCoeff p u k).re * unitIntervalCosineMode k x|
      = |s| * W * |unitIntervalCosineMode k x| := by
        rw [resolverCoeff_re_eq, abs_mul, abs_div, abs_of_pos hd, ← hs, hWeq]
        ring
    _ ≤ |s| * W * 1 :=
        mul_le_mul_of_nonneg_left hcos (mul_nonneg (abs_nonneg _) hWnn)
    _ = |s| * W := by ring
    _ ≤ (s ^ 2 + W ^ 2) / 2 := by
        have h := two_mul_le_add_sq |s| W
        rw [sq_abs] at h; nlinarith [h]

/-- **B2 (gradient series).**  The resolver GRADIENT (sine) series converges
absolutely from the source coefficients being `ℓ²` alone — same AM-GM bound with
the gradient resolvent weight `Wgₖ = kπ/(μ+λₖ)` (also `ℓ²`, since
`kπ/(μ+λₖ) ~ 1/(kπ)`). -/
theorem resolver_sineSeries_summable_of_sourceL2
    (p : CM2Params) {u : intervalDomainPoint → ℝ}
    (hl2 : Summable fun k : ℕ => ((intervalNeumannResolverSourceCoeff p u k).re) ^ 2)
    (x : ℝ) :
    Summable fun k : ℕ =>
      (intervalNeumannResolverCoeff p u k).re *
        (-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * x)) := by
  rw [← summable_abs_iff]
  have hwg := intervalNeumannResolverGradWeight_sq_summable p
  refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) ?_
    ((hl2.add hwg).div_const 2)
  intro k
  have hd : 0 < p.μ + unitIntervalNeumannSpectrum.eigenvalue k :=
    intervalNeumannResolver_denom_pos p k
  set s := (intervalNeumannResolverSourceCoeff p u k).re with hs
  set Wg := intervalNeumannResolverGradWeight p k with hWg
  have hWgnn : 0 ≤ Wg := by
    rw [hWg, intervalNeumannResolverGradWeight]; positivity
  -- `|kπ·sin(kπx)| ≤ kπ` and `R̂ₖ.re = âₖ.re/(μ+λₖ)`
  have hsin : |(-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * x))|
      ≤ (k : ℝ) * Real.pi := by
    rw [abs_mul, abs_neg, abs_mul, Nat.abs_cast, abs_of_pos Real.pi_pos]
    calc (k : ℝ) * Real.pi * |Real.sin ((k : ℝ) * Real.pi * x)|
        ≤ (k : ℝ) * Real.pi * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _)
            (by positivity)
      _ = (k : ℝ) * Real.pi := by ring
  have hWgeq : Wg = ((k : ℝ) * Real.pi) /
      (p.μ + unitIntervalNeumannSpectrum.eigenvalue k) := rfl
  have hkπnn : 0 ≤ (k : ℝ) * Real.pi := by positivity
  calc |(intervalNeumannResolverCoeff p u k).re *
          (-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * x))|
      = |s| / (p.μ + unitIntervalNeumannSpectrum.eigenvalue k)
          * |(-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * x))| := by
        rw [resolverCoeff_re_eq, abs_mul, abs_div, abs_of_pos hd, ← hs]
    _ ≤ |s| / (p.μ + unitIntervalNeumannSpectrum.eigenvalue k)
          * ((k : ℝ) * Real.pi) :=
        mul_le_mul_of_nonneg_left hsin
          (div_nonneg (abs_nonneg _) hd.le)
    _ = |s| * Wg := by rw [hWgeq]; ring
    _ ≤ (s ^ 2 + Wg ^ 2) / 2 := by
        have h := two_mul_le_add_sq |s| Wg
        rw [sq_abs] at h; nlinarith [h]

end ShenWork.IntervalResolverWeakBounds
