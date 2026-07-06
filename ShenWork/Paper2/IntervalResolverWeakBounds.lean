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
import ShenWork.Paper2.IntervalDomainL2UEnergyUniformGammaGeOne

open MeasureTheory intervalIntegral
open ShenWork.IntervalDomain ShenWork.CosineSpectrum
open ShenWork.PDE ShenWork.IntervalEllipticCharacterization
open ShenWork.HeatKernelGradientEstimates
open ShenWork.IntervalResolverGradientBridge
open ShenWork.CosineParsevalBridge
open ShenWork.PDE.ResolventEstimate
open ShenWork.Paper2
open ShenWork.Paper3 (unitIntervalNeumannSpectrum)
open scoped Topology BigOperators

namespace ShenWork.IntervalResolverWeakBounds

/-! ## Fractional sine-mode difference seed for weak gradient Holder -/

/-- Interpolation between the uniform sine bound and the Lipschitz sine bound:
`min 2 r ≤ 2^(1-θ) r^θ` for `0 ≤ θ ≤ 1` and `0 ≤ r`. -/
theorem min_two_le_two_rpow_mul_rpow {θ r : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hr : 0 ≤ r) :
    min (2 : ℝ) r ≤ (2 : ℝ) ^ (1 - θ) * r ^ θ := by
  by_cases hr2 : r ≤ 2
  · rw [min_eq_right hr2]
    by_cases hzero : r = 0
    · subst r
      positivity
    · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hzero)
      have hexp_nonneg : 0 ≤ 1 - θ := by linarith
      have hpow_le : r ^ (1 - θ) ≤ (2 : ℝ) ^ (1 - θ) :=
        Real.rpow_le_rpow hr hr2 hexp_nonneg
      have hre : r = r ^ (1 - θ) * r ^ θ := by
        rw [← Real.rpow_add hrpos, sub_add_cancel, Real.rpow_one]
      calc r
          = r ^ (1 - θ) * r ^ θ := hre
        _ ≤ (2 : ℝ) ^ (1 - θ) * r ^ θ :=
            mul_le_mul_of_nonneg_right hpow_le (Real.rpow_nonneg hr θ)
  · have h2r : (2 : ℝ) ≤ r := le_of_not_ge hr2
    rw [min_eq_left h2r]
    have hpow_le : (2 : ℝ) ^ θ ≤ r ^ θ :=
      Real.rpow_le_rpow (by norm_num) h2r hθ0
    calc (2 : ℝ)
        = (2 : ℝ) ^ (1 - θ) * (2 : ℝ) ^ θ := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
              sub_add_cancel, Real.rpow_one]
      _ ≤ (2 : ℝ) ^ (1 - θ) * r ^ θ :=
          mul_le_mul_of_nonneg_left hpow_le
            (Real.rpow_nonneg (by norm_num) (1 - θ))

/-- Fractional sine-mode difference bound for the resolver gradient modes.  This
is the single-mode seed for the weak bounded-data gradient Holder route at small
Holder exponents. -/
theorem resolverGrad_sineMode_sub_le_rpow
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (k : ℕ) (x y : ℝ) :
    |(-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * x)) -
      (-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * y))| ≤
      (2 : ℝ) ^ (1 - θ) * (((k : ℝ) * Real.pi) ^ (1 + θ)) *
        |x - y| ^ θ := by
  by_cases hk : k = 0
  · subst k
    simp only [Nat.cast_zero, zero_mul, neg_zero, zero_mul, sub_self, abs_zero]
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (1 - θ))
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 0) (1 + θ)))
      (Real.rpow_nonneg (abs_nonneg _) θ)
  · set K : ℝ := (k : ℝ) * Real.pi with hK
    have hkpos_nat : 0 < k := Nat.pos_of_ne_zero hk
    have hKpos : 0 < K := by
      rw [hK]
      positivity
    have hKnn : 0 ≤ K := hKpos.le
    have hlhs :
        |(-K * Real.sin (K * x)) - (-K * Real.sin (K * y))| =
          K * |Real.sin (K * x) - Real.sin (K * y)| := by
      have hsub : (-K * Real.sin (K * x)) - (-K * Real.sin (K * y)) =
          -K * (Real.sin (K * x) - Real.sin (K * y)) := by ring
      rw [hsub, abs_mul, abs_neg, abs_of_nonneg hKnn]
    have hsin_two : |Real.sin (K * x) - Real.sin (K * y)| ≤ 2 := by
      calc |Real.sin (K * x) - Real.sin (K * y)|
          ≤ |Real.sin (K * x)| + |Real.sin (K * y)| := by
              simpa [sub_eq_add_neg, abs_neg] using
                (abs_add_le (Real.sin (K * x)) (-(Real.sin (K * y))))
        _ ≤ 1 + 1 := add_le_add (Real.abs_sin_le_one _) (Real.abs_sin_le_one _)
        _ = 2 := by norm_num
    have hsin_lip : |Real.sin (K * x) - Real.sin (K * y)| ≤ K * |x - y| := by
      have h := Real.lipschitzWith_sin.dist_le_mul (K * x) (K * y)
      have hdist : |K * x - K * y| = K * |x - y| := by
        have hsub : K * x - K * y = K * (x - y) := by ring
        rw [hsub, abs_mul, abs_of_nonneg hKnn]
      simpa [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, one_mul, hdist] using h
    have hsin_min :
        |Real.sin (K * x) - Real.sin (K * y)| ≤ min (2 : ℝ) (K * |x - y|) :=
      le_min hsin_two hsin_lip
    have hmin_bound : min (2 : ℝ) (K * |x - y|) ≤
        (2 : ℝ) ^ (1 - θ) * (K * |x - y|) ^ θ :=
      min_two_le_two_rpow_mul_rpow hθ0.le hθ1
        (mul_nonneg hKnn (abs_nonneg _))
    calc
      |(-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * x)) -
        (-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * y))|
          = |(-K * Real.sin (K * x)) - (-K * Real.sin (K * y))| := by rw [hK]
      _ = K * |Real.sin (K * x) - Real.sin (K * y)| := hlhs
      _ ≤ K * min (2 : ℝ) (K * |x - y|) :=
          mul_le_mul_of_nonneg_left hsin_min hKnn
      _ ≤ K * ((2 : ℝ) ^ (1 - θ) * (K * |x - y|) ^ θ) :=
          mul_le_mul_of_nonneg_left hmin_bound hKnn
      _ = (2 : ℝ) ^ (1 - θ) * (((k : ℝ) * Real.pi) ^ (1 + θ)) *
            |x - y| ^ θ := by
          rw [Real.mul_rpow (x := K) (y := |x - y|) hKnn (abs_nonneg _) (z := θ)]
          have hKpow : K * K ^ θ = K ^ (1 + θ) := by
            calc K * K ^ θ
                = K ^ (1 : ℝ) * K ^ θ := by rw [Real.rpow_one]
              _ = K ^ ((1 : ℝ) + θ) := (Real.rpow_add hKpos 1 θ).symm
              _ = K ^ (1 + θ) := rfl
          calc K * ((2 : ℝ) ^ (1 - θ) * (K ^ θ * |x - y| ^ θ))
              = (2 : ℝ) ^ (1 - θ) * (K * K ^ θ) * |x - y| ^ θ := by ring
            _ = (2 : ℝ) ^ (1 - θ) * (K ^ (1 + θ)) * |x - y| ^ θ := by
                rw [hKpow]
            _ = (2 : ℝ) ^ (1 - θ) * (((k : ℝ) * Real.pi) ^ (1 + θ)) *
                  |x - y| ^ θ := by rw [hK]

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

/-! ## B3 — source `L²`-mass bound and the value/gradient sup bounds (weak) -/

/-- **Weak source `ℓ²`-mass bound `coeffL2Norm(â(u)) ≤ 2·ν·M^γ`.**  With
`0 ≤ lift u ≤ M` continuous on `[0,1]`, the source `ν·u^γ ∈ [0, ν M^γ]`, so
`∫₀¹ (ν u^γ)² ≤ (ν M^γ)²` and cosine–Bessel gives the `ℓ²`-mass bound.  Mirrors
`source_coeffL2Norm_le` with `hsol` replaced by continuity + the two-sided ball
bound `0 ≤ lift u ≤ M`. -/
theorem source_coeffL2Norm_le_of_bounded
    (p : CM2Params) {u : intervalDomainPoint → ℝ} {M : ℝ}
    (hUcont : ContinuousOn (intervalDomainLift u) (Set.Icc (0:ℝ) 1))
    (hlb : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ intervalDomainLift u x)
    (hub : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift u x ≤ M) :
    coeffL2Norm
        (fun k : ℕ => intervalNeumannResolverSourceCoeff p u k -
          intervalNeumannResolverSourceCoeff p (fun _ => 0) k)
      ≤ 2 * (p.ν * M ^ p.γ) := by
  classical
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
  obtain ⟨hsum, hnorm_le⟩ := unitIntervalNeumannCosineCoeff_l2_bound hfint hL2 hfsq
  have hre : ∀ k : ℕ,
      (intervalNeumannResolverSourceCoeff p u k).re = unitIntervalNeumannCosineCoeff f k := by
    intro k; simp only [intervalNeumannResolverSourceCoeff, hf, hg, Complex.ofReal_re]
  have hfg : ∀ x, ‖f x‖ ^ 2 = (g x) ^ 2 := by
    intro x; rw [hf, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hMnn : 0 ≤ M := by
    have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := by constructor <;> norm_num
    exact le_trans (hlb 0 h0) (hub 0 h0)
  have hgptw : ∀ x ∈ Set.Icc (0:ℝ) 1, (g x) ^ 2 ≤ (p.ν * M ^ p.γ) ^ 2 := by
    intro x hx
    have hle : intervalDomainLift u x ^ p.γ ≤ M ^ p.γ :=
      Real.rpow_le_rpow (hlb x hx) (hub x hx) p.hγ.le
    have hgnn : 0 ≤ g x := by
      rw [hg]; exact mul_nonneg p.hν.le (Real.rpow_nonneg (hlb x hx) p.γ)
    have hgub : g x ≤ p.ν * M ^ p.γ := by
      rw [hg]; exact mul_le_mul_of_nonneg_left hle p.hν.le
    nlinarith [hgnn, hgub, mul_nonneg p.hν.le (Real.rpow_nonneg hMnn p.γ)]
  have hg2cont : ContinuousOn (fun x => (g x) ^ 2) (Set.uIcc (0:ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact hgcont.pow 2
  have hIle : (∫ x in (0:ℝ)..1, (g x) ^ 2) ≤ (p.ν * M ^ p.γ) ^ 2 := by
    have hcI : IntervalIntegrable (fun _ : ℝ => (p.ν * M ^ p.γ) ^ 2) volume 0 1 :=
      (continuous_const).intervalIntegrable 0 1
    have hmono := intervalIntegral.integral_mono_on (by norm_num)
      hg2cont.intervalIntegrable hcI hgptw
    have hconst : (∫ _x in (0:ℝ)..1, (p.ν * M ^ p.γ) ^ 2 ∂volume) = (p.ν * M ^ p.γ) ^ 2 := by
      rw [intervalIntegral.integral_const, sub_zero, one_smul]
    rwa [hconst] at hmono
  have hIeq : (∫ x in (0:ℝ)..1, ‖f x‖ ^ 2) = ∫ x in (0:ℝ)..1, (g x) ^ 2 := by
    apply intervalIntegral.integral_congr; intro x _; exact hfg x
  have hnorm_eq : coeffL2Norm
      (fun k : ℕ => intervalNeumannResolverSourceCoeff p u k)
      = unitIntervalCosineL2TsumNorm (unitIntervalNeumannCosineCoeff f) := by
    rw [coeffL2Norm, coeffL2Energy, unitIntervalCosineL2TsumNorm,
      unitIntervalCosineL2TsumEnergy]
    congr 1
    refine tsum_congr (fun k => ?_)
    have him : (intervalNeumannResolverSourceCoeff p u k).im = 0 := by
      simp [intervalNeumannResolverSourceCoeff]
    rw [Complex.sq_norm, Complex.normSq_apply, him, hre k]; ring
  rw [hnorm_eq]
  refine hnorm_le.trans ?_
  rw [hIeq]
  have hsqrt : Real.sqrt (∫ x in (0:ℝ)..1, (g x) ^ 2) ≤ p.ν * M ^ p.γ := by
    have hnn : 0 ≤ p.ν * M ^ p.γ := mul_nonneg p.hν.le (Real.rpow_nonneg hMnn p.γ)
    rw [show p.ν * M ^ p.γ = Real.sqrt ((p.ν * M ^ p.γ) ^ 2) from (Real.sqrt_sq hnn).symm]
    exact Real.sqrt_le_sqrt hIle
  linarith

/-- **B3 (value sup bound `‖E u‖∞ ≤ C₀·M^γ`).**  For a bounded continuous ball
element `0 ≤ lift u ≤ M`, the resolver value is sup-bounded by
`C₀·M^γ = sqrt(∑ₖ 1/(μ+λₖ)²)·2·ν·M^γ`.  Weak analogue of
`resolverValue_sup_le_of_ub` (no `hsol`): the sup-Lipschitz against the zero
source, with the `ℓ²` side conditions discharged by B1/B2 and the mass bound by
`source_coeffL2Norm_le_of_bounded`. -/
theorem resolverValue_sup_le_of_bounded
    (p : CM2Params) {u : intervalDomainPoint → ℝ} {M : ℝ}
    (hUcont : ContinuousOn (intervalDomainLift u) (Set.Icc (0:ℝ) 1))
    (hlb : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ intervalDomainLift u x)
    (hub : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift u x ≤ M)
    (x : intervalDomainPoint) :
    |intervalNeumannResolverR p u x| ≤
      Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2) *
        (2 * (p.ν * M ^ p.γ)) := by
  have hsrc := resolverSourceCoeff_re_sq_summable_of_continuousOn p hUcont
  have hl2 : Summable fun k : ℕ => ((intervalNeumannResolverSourceCoeff p u k).re) ^ 2 := by
    simpa [intervalNeumannResolverSourceCoeff_zero, sub_zero] using hsrc
  have hsum₁ := resolver_cosineSeries_summable_of_sourceL2 p hl2 x.1
  have hsum₂ := zero_resolver_cosineSeries_summable p x.1
  have hbound := intervalNeumannResolverR_sup_lipschitz p u (fun _ => 0) hsrc x hsum₁ hsum₂
  rw [intervalNeumannResolverR_zero, sub_zero] at hbound
  refine hbound.trans ?_
  exact mul_le_mul_of_nonneg_left
    (source_coeffL2Norm_le_of_bounded p hUcont hlb hub) (Real.sqrt_nonneg _)

/-- **B3 (gradient sup bound `‖∂ₓ(E u)‖∞ ≤ C₁·M^γ`).**  Same route for the
resolver gradient `resolverGradReal` via `intervalNeumannResolverR_grad_sup_lipschitz`
and the sine-series summability B2.  `C₁·M^γ = sqrt(∑ₖ (kπ/(μ+λₖ))²)·2·ν·M^γ`. -/
theorem resolverGrad_sup_le_of_bounded
    (p : CM2Params) {u : intervalDomainPoint → ℝ} {M : ℝ}
    (hUcont : ContinuousOn (intervalDomainLift u) (Set.Icc (0:ℝ) 1))
    (hlb : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ intervalDomainLift u x)
    (hub : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift u x ≤ M)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    |resolverGradReal p u x| ≤
      Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * M ^ p.γ)) := by
  have hsrc := resolverSourceCoeff_re_sq_summable_of_continuousOn p hUcont
  have hl2 : Summable fun k : ℕ => ((intervalNeumannResolverSourceCoeff p u k).re) ^ 2 := by
    simpa [intervalNeumannResolverSourceCoeff_zero, sub_zero] using hsrc
  have hsum₁ := resolver_sineSeries_summable_of_sourceL2 p hl2 x
  have hsum₂ := zero_resolver_sineSeries_summable p x
  have hbound := intervalNeumannResolverR_grad_sup_lipschitz p u (fun _ => 0) hsrc
    ⟨x, hx⟩ hsum₁ hsum₂
  rw [intervalNeumannResolverRGrad_zero, sub_zero] at hbound
  rw [resolverGradReal_eq p u ⟨x, hx⟩]
  refine hbound.trans ?_
  exact mul_le_mul_of_nonneg_left
    (source_coeffL2Norm_le_of_bounded p hUcont hlb hub) (Real.sqrt_nonneg _)

/-- Each Neumann cosine mode is spatially Lipschitz with constant `kπ`. -/
private theorem unitIntervalCosineMode_abs_sub_le
    (k : ℕ) (x y : ℝ) :
    |unitIntervalCosineMode k x - unitIntervalCosineMode k y| ≤
      ((k : ℝ) * Real.pi) * |x - y| := by
  rw [unitIntervalCosineMode]
  calc |Real.cos ((k : ℝ) * Real.pi * x) -
        Real.cos ((k : ℝ) * Real.pi * y)|
      ≤ |((k : ℝ) * Real.pi * x) - ((k : ℝ) * Real.pi * y)| :=
        Real.abs_cos_sub_cos_le _ _
    _ = ((k : ℝ) * Real.pi) * |x - y| := by
        rw [← mul_sub, abs_mul]
        have hkp_nonneg : 0 ≤ (k : ℝ) * Real.pi :=
          mul_nonneg (Nat.cast_nonneg _) Real.pi_pos.le
        rw [abs_of_nonneg hkp_nonneg]

/-- **Weak resolver-value spatial Holder bound.**  If a bounded continuous
order-box element satisfies `0 ≤ u ≤ M`, then the elliptic resolver value is
spatially `θ`-Holder on `[0,1]` with the same gradient-weight constant that
controls `resolverGradReal`.

The proof avoids the C²/source-decay derivative bridge.  It estimates the
cosine-series difference directly by Cauchy-Schwarz, using
`|cos(kπx)-cos(kπy)| ≤ kπ|x-y|`. -/
theorem intervalNeumannResolverR_lift_holder_Icc_of_bounded
    (p : CM2Params) {u : intervalDomainPoint → ℝ} {M θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hUcont : ContinuousOn (intervalDomainLift u) (Set.Icc (0 : ℝ) 1))
    (hlb : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ intervalDomainLift u x)
    (hub : ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift u x ≤ M)
    {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |intervalDomainLift (intervalNeumannResolverR p u) x -
        intervalDomainLift (intervalNeumannResolverR p u) y| ≤
      (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * M ^ p.γ))) * |x - y| ^ θ := by
  classical
  have hMnn : 0 ≤ M := by
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
    exact le_trans (hlb 0 h0) (hub 0 h0)
  have hsrc := resolverSourceCoeff_re_sq_summable_of_continuousOn p hUcont
  have hl2 : Summable fun k : ℕ => ((intervalNeumannResolverSourceCoeff p u k).re) ^ 2 := by
    simpa [intervalNeumannResolverSourceCoeff_zero, sub_zero] using hsrc
  have hsumx := resolver_cosineSeries_summable_of_sourceL2 p hl2 x
  have hsumy := resolver_cosineSeries_summable_of_sourceL2 p hl2 y
  set A : ℕ → ℂ := fun k =>
    intervalNeumannResolverSourceCoeff p u k -
      intervalNeumannResolverSourceCoeff p (fun _ => 0) k with hA
  set e : ℕ → ℝ := fun k => (A k).re with he
  set m : ℕ → ℝ := fun k =>
    (unitIntervalCosineMode k x - unitIntervalCosineMode k y) /
      (p.μ + unitIntervalNeumannSpectrum.eigenvalue k) with hm
  have hterm : ∀ k : ℕ,
      (intervalNeumannResolverCoeff p u k).re * unitIntervalCosineMode k x -
        (intervalNeumannResolverCoeff p u k).re * unitIntervalCosineMode k y =
          e k * m k := by
    intro k
    have hden : p.μ + unitIntervalNeumannSpectrum.eigenvalue k ≠ 0 :=
      ne_of_gt (intervalNeumannResolver_denom_pos p k)
    rw [he, hA, hm, resolverCoeff_re_eq p u k]
    simp only [intervalNeumannResolverSourceCoeff_zero, sub_zero]
    field_simp [hden]
  have he_sq : Summable fun k : ℕ => (e k) ^ 2 := by
    simpa [e, A, intervalNeumannResolverSourceCoeff_zero, sub_zero] using hl2
  have hm_sq : Summable fun k : ℕ => (m k) ^ 2 := by
    refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) ?_
      ((intervalNeumannResolverGradWeight_sq_summable p).mul_left (|x - y| ^ 2))
    intro k
    have hden_pos : 0 < p.μ + unitIntervalNeumannSpectrum.eigenvalue k :=
      intervalNeumannResolver_denom_pos p k
    have hm_abs : |m k| ≤ intervalNeumannResolverGradWeight p k * |x - y| := by
      rw [hm, abs_div, abs_of_pos hden_pos, intervalNeumannResolverGradWeight]
      calc |unitIntervalCosineMode k x - unitIntervalCosineMode k y| /
            (p.μ + unitIntervalNeumannSpectrum.eigenvalue k)
          ≤ (((k : ℝ) * Real.pi) * |x - y|) /
              (p.μ + unitIntervalNeumannSpectrum.eigenvalue k) :=
            div_le_div_of_nonneg_right
              (unitIntervalCosineMode_abs_sub_le k x y) hden_pos.le
        _ = (k : ℝ) * Real.pi /
              (p.μ + unitIntervalNeumannSpectrum.eigenvalue k) * |x - y| := by
            ring
    calc (m k) ^ 2 = |m k| ^ 2 := (sq_abs (m k)).symm
      _ ≤ (intervalNeumannResolverGradWeight p k * |x - y|) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hm_abs 2
      _ = |x - y| ^ 2 * (intervalNeumannResolverGradWeight p k) ^ 2 := by ring
  have hprod_sum : Summable fun k : ℕ => e k * m k := by
    apply Summable.of_norm
    have hdom : ∀ k : ℕ,
        ‖e k * m k‖ ≤ (1/2) * (e k)^2 + (1/2) * (m k)^2 := by
      intro k
      rw [Real.norm_eq_abs, abs_mul]
      nlinarith [sq_abs (e k), sq_abs (m k), sq_nonneg (|e k| - |m k|)]
    exact Summable.of_nonneg_of_le (fun k => norm_nonneg _) hdom
      ((he_sq.mul_left (1/2)).add (hm_sq.mul_left (1/2)))
  have hsum_eq :
      intervalNeumannResolverR p u ⟨x, hx⟩ -
          intervalNeumannResolverR p u ⟨y, hy⟩ =
        ∑' k : ℕ, e k * m k := by
    simp only [intervalNeumannResolverR]
    rw [← hsumx.tsum_sub hsumy]
    refine tsum_congr ?_
    intro k
    rw [← hterm k]
  have hCS :
      |∑' k : ℕ, e k * m k| ≤
        Real.sqrt (∑' k : ℕ, (e k) ^ 2) *
          Real.sqrt (∑' k : ℕ, (m k) ^ 2) :=
    real_abs_tsum_mul_le_sqrt_tsum_sq_mul_sqrt_tsum_sq he_sq hm_sq
  have hA_l2 :
      Real.sqrt (∑' k : ℕ, (e k) ^ 2) ≤ coeffL2Norm A := by
    rw [coeffL2Norm, coeffL2Energy]
    apply Real.sqrt_le_sqrt
    refine he_sq.tsum_le_tsum ?_ (intervalNeumannResolverR_source_l2_summable p u (fun _ => 0) hsrc)
    intro k
    have : (e k) ^ 2 = (A k).re * (A k).re := by rw [he]; ring
    rw [this]
    calc (A k).re * (A k).re ≤ Complex.normSq (A k) := Complex.re_sq_le_normSq _
      _ = ‖A k‖ ^ 2 := (Complex.sq_norm _).symm
  have hmW :
      Real.sqrt (∑' k : ℕ, (m k) ^ 2) ≤
        Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
          |x - y| := by
    have hsum_le :
        (∑' k : ℕ, (m k) ^ 2) ≤
          |x - y| ^ 2 *
            (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) := by
      have hle : ∀ k : ℕ,
          (m k) ^ 2 ≤
            |x - y| ^ 2 * (intervalNeumannResolverGradWeight p k) ^ 2 := by
        intro k
        have hden_pos : 0 < p.μ + unitIntervalNeumannSpectrum.eigenvalue k :=
          intervalNeumannResolver_denom_pos p k
        have hm_abs : |m k| ≤ intervalNeumannResolverGradWeight p k * |x - y| := by
          rw [hm, abs_div, abs_of_pos hden_pos, intervalNeumannResolverGradWeight]
          calc |unitIntervalCosineMode k x - unitIntervalCosineMode k y| /
                (p.μ + unitIntervalNeumannSpectrum.eigenvalue k)
              ≤ (((k : ℝ) * Real.pi) * |x - y|) /
                  (p.μ + unitIntervalNeumannSpectrum.eigenvalue k) :=
                div_le_div_of_nonneg_right
                  (unitIntervalCosineMode_abs_sub_le k x y) hden_pos.le
            _ = (k : ℝ) * Real.pi /
                  (p.μ + unitIntervalNeumannSpectrum.eigenvalue k) * |x - y| := by
                ring
        calc (m k) ^ 2 = |m k| ^ 2 := (sq_abs (m k)).symm
          _ ≤ (intervalNeumannResolverGradWeight p k * |x - y|) ^ 2 :=
              pow_le_pow_left₀ (abs_nonneg _) hm_abs 2
          _ = |x - y| ^ 2 * (intervalNeumannResolverGradWeight p k) ^ 2 := by ring
      calc (∑' k : ℕ, (m k) ^ 2)
          ≤ ∑' k : ℕ, |x - y| ^ 2 * (intervalNeumannResolverGradWeight p k) ^ 2 :=
            hm_sq.tsum_le_tsum hle
              ((intervalNeumannResolverGradWeight_sq_summable p).mul_left (|x - y| ^ 2))
        _ = |x - y| ^ 2 *
            (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) := by
            exact Summable.tsum_mul_left (|x - y| ^ 2)
              (intervalNeumannResolverGradWeight_sq_summable p)
    calc Real.sqrt (∑' k : ℕ, (m k) ^ 2)
        ≤ Real.sqrt (|x - y| ^ 2 *
            (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2)) :=
          Real.sqrt_le_sqrt hsum_le
      _ = Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
          |x - y| := by
          rw [Real.sqrt_mul (sq_nonneg (|x - y|))
            (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2)]
          rw [Real.sqrt_sq (abs_nonneg _), mul_comm]
  have hLip :
      |intervalNeumannResolverR p u ⟨x, hx⟩ -
          intervalNeumannResolverR p u ⟨y, hy⟩| ≤
        (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
          (2 * (p.ν * M ^ p.γ))) * |x - y| := by
    rw [hsum_eq]
    have hcoeff := source_coeffL2Norm_le_of_bounded p hUcont hlb hub
    have hcoeff_nn : 0 ≤ coeffL2Norm A := Real.sqrt_nonneg _
    have hW_nn :
        0 ≤ Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) :=
      Real.sqrt_nonneg _
    have hdist_nn : 0 ≤ |x - y| := abs_nonneg _
    calc |∑' k : ℕ, e k * m k|
        ≤ Real.sqrt (∑' k : ℕ, (e k) ^ 2) *
            Real.sqrt (∑' k : ℕ, (m k) ^ 2) := hCS
      _ ≤ coeffL2Norm A *
            (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
              |x - y|) :=
          mul_le_mul hA_l2 hmW (Real.sqrt_nonneg _) hcoeff_nn
      _ ≤ (2 * (p.ν * M ^ p.γ)) *
            (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
              |x - y|) :=
          mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hW_nn hdist_nn)
      _ = (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
            (2 * (p.ν * M ^ p.γ))) * |x - y| := by ring
  have hdist_le_one : |x - y| ≤ 1 := by
    rw [abs_sub_le_iff]
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hdist_le_pow : |x - y| ≤ |x - y| ^ θ := by
    simpa [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge'
        (x := |x - y|) (y := 1) (z := θ)
        (abs_nonneg _) hdist_le_one hθ0.le hθ1)
  have hconst_nn :
      0 ≤ Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * M ^ p.γ)) := by
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (mul_nonneg p.hν.le (Real.rpow_nonneg hMnn _)))
  have hxlift :
      intervalDomainLift (intervalNeumannResolverR p u) x =
        intervalNeumannResolverR p u ⟨x, hx⟩ := by
    simp [intervalDomainLift, hx]
  have hylift :
      intervalDomainLift (intervalNeumannResolverR p u) y =
        intervalNeumannResolverR p u ⟨y, hy⟩ := by
    simp [intervalDomainLift, hy]
  rw [hxlift, hylift]
  exact hLip.trans (mul_le_mul_of_nonneg_left hdist_le_pow hconst_nn)


/-! ## B4 — resolver value/gradient DIFFERENCE Lipschitz (weak)

The Lipschitz half of Atom B.  `R` is linear in the source `ν·u^γ`, so the
value/gradient differences are controlled by the source-coefficient `ℓ²`-mass of
the difference, which cosine–Bessel bounds by the `L²` mass of `ν(u₁^γ − u₂^γ)`,
which the `γ ≥ 1` rpow-Lipschitz `rpow_lipschitz_on_Icc_zeroM_of_one_le_gamma`
bounds by `(ν γ M^{γ-1})·‖u₁ − u₂‖∞`. -/

/-- **Cosine–Bessel on the source difference (continuity-based core).**  Weak
analogue of `sourceCoeff_diff_energy_le_integral` with the two solution
hypotheses replaced by direct source continuities — the rest of the proof (the
real-coefficient linearity + Bessel) is `hsol`-free. -/
theorem sourceCoeff_diff_energy_le_integral_of_continuousOn
    (p : CM2Params) {u₁ u₂ : intervalDomainPoint → ℝ}
    (hg1 : ContinuousOn (fun x : ℝ => p.ν * intervalDomainLift u₁ x ^ p.γ)
      (Set.Icc (0:ℝ) 1))
    (hg2 : ContinuousOn (fun x : ℝ => p.ν * intervalDomainLift u₂ x ^ p.γ)
      (Set.Icc (0:ℝ) 1)) :
    coeffL2Energy
        (fun k : ℕ => intervalNeumannResolverSourceCoeff p u₁ k -
          intervalNeumannResolverSourceCoeff p u₂ k)
      ≤ 4 * ∫ x in (0:ℝ)..1,
          (p.ν * intervalDomainLift u₁ x ^ p.γ
            - p.ν * intervalDomainLift u₂ x ^ p.γ) ^ 2 := by
  classical
  set g : ℝ → ℝ := fun x =>
    p.ν * intervalDomainLift u₁ x ^ p.γ - p.ν * intervalDomainLift u₂ x ^ p.γ
    with hg
  set f : ℝ → ℂ := fun x => ((g x : ℝ) : ℂ) with hf
  have hgcont : ContinuousOn g (Set.Icc (0:ℝ) 1) := hg1.sub hg2
  have hfcontOn : ContinuousOn f (Set.uIcc (0:ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact Complex.continuous_ofReal.comp_continuousOn hgcont
  have hfint : IntervalIntegrable f volume 0 1 := hfcontOn.intervalIntegrable
  have hfsq : IntervalIntegrable (fun x : ℝ => ‖f x‖ ^ 2) volume 0 1 :=
    ((hfcontOn.norm).pow 2).intervalIntegrable
  have hL2 : MemLp (unitIntervalEvenReflection f) 2
      (volume.restrict (Set.Ioc (-1:ℝ) 1)) :=
    evenReflection_memLp_two_of_continuousOn hgcont
  -- cosine-Bessel: `∑ (cosineCoeff f)² ≤ 4·∫ ‖f‖²`.
  obtain ⟨hsum, hnorm_le⟩ := unitIntervalNeumannCosineCoeff_l2_bound hfint hL2 hfsq
  -- identify `(Δsource).re` with the cosine coefficient of `f` and `‖f‖² = g²`.
  have hre : ∀ k : ℕ,
      (intervalNeumannResolverSourceCoeff p u₁ k -
        intervalNeumannResolverSourceCoeff p u₂ k).re
        = unitIntervalNeumannCosineCoeff f k := by
    intro k
    have h1 : (intervalNeumannResolverSourceCoeff p u₁ k).re
        = unitIntervalNeumannCosineCoeff
            (fun x => ((p.ν * intervalDomainLift u₁ x ^ p.γ : ℝ) : ℂ)) k := by
      simp only [intervalNeumannResolverSourceCoeff, Complex.ofReal_re]
    have h2 : (intervalNeumannResolverSourceCoeff p u₂ k).re
        = unitIntervalNeumannCosineCoeff
            (fun x => ((p.ν * intervalDomainLift u₂ x ^ p.γ : ℝ) : ℂ)) k := by
      simp only [intervalNeumannResolverSourceCoeff, Complex.ofReal_re]
    rw [Complex.sub_re, h1, h2]
    -- linearity of the (real) Neumann cosine coefficient in the source.
    simp only [unitIntervalNeumannCosineCoeff,
      ShenWork.HeatKernelGradientEstimates.unitIntervalCosineRawCoeff, hf, hg]
    have hcos_cont : ∀ m : ℕ, ContinuousOn
        (fun x : ℝ => (Real.cos ((m:ℝ) * Real.pi * x) : ℂ)) (Set.uIcc (0:ℝ) 1) :=
      fun m => (Complex.continuous_ofReal.comp
        (Real.continuous_cos.comp (by fun_prop))).continuousOn
    have hII1 : ∀ m : ℕ, IntervalIntegrable
        (fun x : ℝ => (Real.cos ((m:ℝ) * Real.pi * x) : ℂ) *
          ((p.ν * intervalDomainLift u₁ x ^ p.γ : ℝ) : ℂ)) volume 0 1 := by
      intro m
      refine ((hcos_cont m).mul ?_).intervalIntegrable
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact Complex.continuous_ofReal.comp_continuousOn hg1
    have hII2 : ∀ m : ℕ, IntervalIntegrable
        (fun x : ℝ => (Real.cos ((m:ℝ) * Real.pi * x) : ℂ) *
          ((p.ν * intervalDomainLift u₂ x ^ p.γ : ℝ) : ℂ)) volume 0 1 := by
      intro m
      refine ((hcos_cont m).mul ?_).intervalIntegrable
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact Complex.continuous_ofReal.comp_continuousOn hg2
    have hlin : ∀ m : ℕ,
        ((∫ x in (0:ℝ)..1, (Real.cos ((m:ℝ) * Real.pi * x) : ℂ) *
            ((p.ν * intervalDomainLift u₁ x ^ p.γ : ℝ) : ℂ)).re)
          - ((∫ x in (0:ℝ)..1, (Real.cos ((m:ℝ) * Real.pi * x) : ℂ) *
            ((p.ν * intervalDomainLift u₂ x ^ p.γ : ℝ) : ℂ)).re)
          = (∫ x in (0:ℝ)..1, (Real.cos ((m:ℝ) * Real.pi * x) : ℂ) *
            ((p.ν * intervalDomainLift u₁ x ^ p.γ
              - p.ν * intervalDomainLift u₂ x ^ p.γ : ℝ) : ℂ)).re := by
      intro m
      rw [← Complex.sub_re, ← intervalIntegral.integral_sub (hII1 m) (hII2 m)]
      congr 1; apply intervalIntegral.integral_congr; intro x _; push_cast; ring
    rcases eq_or_ne k 0 with hk | hk
    · subst hk; simp only [if_pos rfl]; exact hlin 0
    · simp only [if_neg hk]; rw [← mul_sub, hlin k]
  -- now bound the energy.
  rw [coeffL2Energy]
  have hcongr : (fun k : ℕ => ‖intervalNeumannResolverSourceCoeff p u₁ k -
        intervalNeumannResolverSourceCoeff p u₂ k‖ ^ 2)
      = fun k : ℕ => (unitIntervalNeumannCosineCoeff f k) ^ 2 := by
    funext k
    have him : (intervalNeumannResolverSourceCoeff p u₁ k -
        intervalNeumannResolverSourceCoeff p u₂ k).im = 0 := by
      simp [intervalNeumannResolverSourceCoeff, Complex.sub_im]
    rw [Complex.sq_norm, Complex.normSq_apply, him, hre k]; ring
  rw [hcongr]
  -- `∑ (cosineCoeff f)² = TsumEnergy = (TsumNorm)² ≤ (2 sqrt I)² = 4 I`.
  have hI_nonneg : 0 ≤ ∫ x in (0:ℝ)..1, ‖f x‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun x _ => sq_nonneg _)
  have hEnergy_eq : (∑' k : ℕ, (unitIntervalNeumannCosineCoeff f k) ^ 2)
      = (unitIntervalCosineL2TsumNorm (unitIntervalNeumannCosineCoeff f)) ^ 2 := by
    rw [unitIntervalCosineL2TsumNorm, Real.sq_sqrt]
    · rfl
    · exact tsum_nonneg (fun k => sq_nonneg _)
  rw [hEnergy_eq]
  have hfg : (∫ x in (0:ℝ)..1, ‖f x‖ ^ 2)
      = ∫ x in (0:ℝ)..1, (p.ν * intervalDomainLift u₁ x ^ p.γ
          - p.ν * intervalDomainLift u₂ x ^ p.γ) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x _
    show ‖((g x : ℝ) : ℂ)‖ ^ 2 = (p.ν * intervalDomainLift u₁ x ^ p.γ
          - p.ν * intervalDomainLift u₂ x ^ p.γ) ^ 2
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, hg]
  rw [hfg] at hnorm_le
  -- `TsumNorm ≤ 2 sqrt I`, square both sides.
  have hnn : 0 ≤ unitIntervalCosineL2TsumNorm (unitIntervalNeumannCosineCoeff f) :=
    Real.sqrt_nonneg _
  calc (unitIntervalCosineL2TsumNorm (unitIntervalNeumannCosineCoeff f)) ^ 2
      ≤ (2 * Real.sqrt (∫ x in (0:ℝ)..1, (p.ν * intervalDomainLift u₁ x ^ p.γ
          - p.ν * intervalDomainLift u₂ x ^ p.γ) ^ 2)) ^ 2 := by
        exact pow_le_pow_left₀ hnn hnorm_le 2
    _ = 4 * ∫ x in (0:ℝ)..1, (p.ν * intervalDomainLift u₁ x ^ p.γ
          - p.ν * intervalDomainLift u₂ x ^ p.γ) ^ 2 := by
        have hInonneg : 0 ≤ ∫ x in (0:ℝ)..1, (p.ν * intervalDomainLift u₁ x ^ p.γ
            - p.ν * intervalDomainLift u₂ x ^ p.γ) ^ 2 :=
          intervalIntegral.integral_nonneg (by norm_num) (fun x _ => sq_nonneg _)
        rw [mul_pow, Real.sq_sqrt hInonneg]; ring

/-- Source-coefficient DIFFERENCE is `ℓ²`-summable from continuity of both
lifts (`(s₁−s₂)² ≤ 2s₁² + 2s₂²`, each `ℓ²` by B1). -/
theorem resolverSourceCoeff_diff_re_sq_summable_of_continuousOn
    (p : CM2Params) {u₁ u₂ : intervalDomainPoint → ℝ}
    (hUc₁ : ContinuousOn (intervalDomainLift u₁) (Set.Icc (0:ℝ) 1))
    (hUc₂ : ContinuousOn (intervalDomainLift u₂) (Set.Icc (0:ℝ) 1)) :
    Summable fun k : ℕ =>
      ((intervalNeumannResolverSourceCoeff p u₁ k -
        intervalNeumannResolverSourceCoeff p u₂ k).re) ^ 2 := by
  have h1 : Summable fun k : ℕ => ((intervalNeumannResolverSourceCoeff p u₁ k).re) ^ 2 := by
    simpa [intervalNeumannResolverSourceCoeff_zero, sub_zero] using
      resolverSourceCoeff_re_sq_summable_of_continuousOn p hUc₁
  have h2 : Summable fun k : ℕ => ((intervalNeumannResolverSourceCoeff p u₂ k).re) ^ 2 := by
    simpa [intervalNeumannResolverSourceCoeff_zero, sub_zero] using
      resolverSourceCoeff_re_sq_summable_of_continuousOn p hUc₂
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) ?_
    ((h1.mul_left 2).add (h2.mul_left 2))
  intro k
  rw [Complex.sub_re]
  nlinarith [sq_nonneg ((intervalNeumannResolverSourceCoeff p u₁ k).re
    + (intervalNeumannResolverSourceCoeff p u₂ k).re)]

/-- **B4 (mass).**  The source-coefficient difference `ℓ²`-mass is Lipschitz:
`coeffL2Norm(â(u₁) − â(u₂)) ≤ 2·ν·γ·M^{γ-1}·D` on the bounded ball
`0 ≤ lift uᵢ ≤ M` with `|lift u₁ − lift u₂| ≤ D` (uses `γ ≥ 1`). -/
theorem source_coeffL2Norm_diff_le_of_bounded
    (p : CM2Params) (hγ : 1 ≤ p.γ) {u₁ u₂ : intervalDomainPoint → ℝ} {M D : ℝ}
    (hUc₁ : ContinuousOn (intervalDomainLift u₁) (Set.Icc (0:ℝ) 1))
    (hUc₂ : ContinuousOn (intervalDomainLift u₂) (Set.Icc (0:ℝ) 1))
    (hmem₁ : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift u₁ x ∈ Set.Icc (0:ℝ) M)
    (hmem₂ : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift u₂ x ∈ Set.Icc (0:ℝ) M)
    (hD : ∀ x ∈ Set.Icc (0:ℝ) 1,
      |intervalDomainLift u₁ x - intervalDomainLift u₂ x| ≤ D) :
    coeffL2Norm (fun k : ℕ => intervalNeumannResolverSourceCoeff p u₁ k -
        intervalNeumannResolverSourceCoeff p u₂ k)
      ≤ 2 * (p.ν * (p.γ * M ^ (p.γ - 1)) * D) := by
  have h0mem : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_refl 0, zero_le_one⟩
  have hMnn : 0 ≤ M := le_trans (hmem₁ 0 h0mem).1 (hmem₁ 0 h0mem).2
  have hDnn : 0 ≤ D := le_trans (abs_nonneg _) (hD 0 h0mem)
  have hMγnn : 0 ≤ M ^ (p.γ - 1) := Real.rpow_nonneg hMnn _
  set Lc : ℝ := p.ν * (p.γ * M ^ (p.γ - 1)) * D with hLc
  have hLcnn : 0 ≤ Lc := by
    rw [hLc]
    exact mul_nonneg (mul_nonneg p.hν.le
      (mul_nonneg (by linarith) hMγnn)) hDnn
  have hg1 : ContinuousOn (fun x : ℝ => p.ν * intervalDomainLift u₁ x ^ p.γ)
      (Set.Icc (0:ℝ) 1) :=
    continuousOn_const.mul (hUc₁.rpow_const (fun x _ => Or.inr p.hγ.le))
  have hg2 : ContinuousOn (fun x : ℝ => p.ν * intervalDomainLift u₂ x ^ p.γ)
      (Set.Icc (0:ℝ) 1) :=
    continuousOn_const.mul (hUc₂.rpow_const (fun x _ => Or.inr p.hγ.le))
  have hcore := sourceCoeff_diff_energy_le_integral_of_continuousOn p hg1 hg2
  -- pointwise integrand bound `(source diff)² ≤ Lc²`.
  have hptw : ∀ x ∈ Set.Icc (0:ℝ) 1,
      (p.ν * intervalDomainLift u₁ x ^ p.γ
        - p.ν * intervalDomainLift u₂ x ^ p.γ) ^ 2 ≤ Lc ^ 2 := by
    intro x hx
    have hlip := rpow_lipschitz_on_Icc_zeroM_of_one_le_gamma hγ hMnn
      (hmem₁ x hx) (hmem₂ x hx)
    have habs : |p.ν * intervalDomainLift u₁ x ^ p.γ
        - p.ν * intervalDomainLift u₂ x ^ p.γ| ≤ Lc := by
      rw [← mul_sub, abs_mul, abs_of_nonneg p.hν.le, hLc]
      have hstep : |intervalDomainLift u₁ x ^ p.γ - intervalDomainLift u₂ x ^ p.γ|
          ≤ p.γ * M ^ (p.γ - 1) * D := by
        refine le_trans hlip ?_
        exact mul_le_mul_of_nonneg_left (hD x hx)
          (mul_nonneg (by linarith) hMγnn)
      calc p.ν * |intervalDomainLift u₁ x ^ p.γ - intervalDomainLift u₂ x ^ p.γ|
          ≤ p.ν * (p.γ * M ^ (p.γ - 1) * D) :=
            mul_le_mul_of_nonneg_left hstep p.hν.le
        _ = p.ν * (p.γ * M ^ (p.γ - 1)) * D := by ring
    nlinarith [abs_nonneg (p.ν * intervalDomainLift u₁ x ^ p.γ
      - p.ν * intervalDomainLift u₂ x ^ p.γ), sq_abs (p.ν * intervalDomainLift u₁ x ^ p.γ
      - p.ν * intervalDomainLift u₂ x ^ p.γ), habs, hLcnn]
  have hg2cont : ContinuousOn (fun x : ℝ =>
      (p.ν * intervalDomainLift u₁ x ^ p.γ
        - p.ν * intervalDomainLift u₂ x ^ p.γ) ^ 2) (Set.uIcc (0:ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact (hg1.sub hg2).pow 2
  have hInt : (∫ x in (0:ℝ)..1, (p.ν * intervalDomainLift u₁ x ^ p.γ
      - p.ν * intervalDomainLift u₂ x ^ p.γ) ^ 2) ≤ Lc ^ 2 := by
    have hcI : IntervalIntegrable (fun _ : ℝ => Lc ^ 2) volume 0 1 :=
      (continuous_const).intervalIntegrable 0 1
    have hmono := intervalIntegral.integral_mono_on (by norm_num)
      hg2cont.intervalIntegrable hcI hptw
    have hconst : (∫ _x in (0:ℝ)..1, Lc ^ 2 ∂volume) = Lc ^ 2 := by
      rw [intervalIntegral.integral_const, sub_zero, one_smul]
    rwa [hconst] at hmono
  rw [coeffL2Norm]
  have henergy : coeffL2Energy (fun k : ℕ => intervalNeumannResolverSourceCoeff p u₁ k -
      intervalNeumannResolverSourceCoeff p u₂ k) ≤ (2 * Lc) ^ 2 := by
    refine hcore.trans ?_
    nlinarith [hInt]
  calc Real.sqrt (coeffL2Energy (fun k : ℕ => intervalNeumannResolverSourceCoeff p u₁ k -
        intervalNeumannResolverSourceCoeff p u₂ k))
      ≤ Real.sqrt ((2 * Lc) ^ 2) := Real.sqrt_le_sqrt henergy
    _ = 2 * Lc := by rw [Real.sqrt_sq (by linarith [hLcnn])]
    _ = 2 * (p.ν * (p.γ * M ^ (p.γ - 1)) * D) := by rw [hLc]

/-- **B4 (value difference).**  `‖E u₁ − E u₂‖∞ ≤ sqrt(∑1/(μ+λₖ)²)·2νγM^{γ-1}·D`. -/
theorem resolverValue_diff_sup_le_of_bounded
    (p : CM2Params) (hγ : 1 ≤ p.γ) {u₁ u₂ : intervalDomainPoint → ℝ} {M D : ℝ}
    (hUc₁ : ContinuousOn (intervalDomainLift u₁) (Set.Icc (0:ℝ) 1))
    (hUc₂ : ContinuousOn (intervalDomainLift u₂) (Set.Icc (0:ℝ) 1))
    (hmem₁ : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift u₁ x ∈ Set.Icc (0:ℝ) M)
    (hmem₂ : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift u₂ x ∈ Set.Icc (0:ℝ) M)
    (hD : ∀ x ∈ Set.Icc (0:ℝ) 1,
      |intervalDomainLift u₁ x - intervalDomainLift u₂ x| ≤ D)
    (x : intervalDomainPoint) :
    |intervalNeumannResolverR p u₁ x - intervalNeumannResolverR p u₂ x| ≤
      Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2) *
        (2 * (p.ν * (p.γ * M ^ (p.γ - 1)) * D)) := by
  have hsrc := resolverSourceCoeff_diff_re_sq_summable_of_continuousOn p hUc₁ hUc₂
  have hl2₁ : Summable fun k : ℕ => ((intervalNeumannResolverSourceCoeff p u₁ k).re) ^ 2 := by
    simpa [intervalNeumannResolverSourceCoeff_zero, sub_zero] using
      resolverSourceCoeff_re_sq_summable_of_continuousOn p hUc₁
  have hl2₂ : Summable fun k : ℕ => ((intervalNeumannResolverSourceCoeff p u₂ k).re) ^ 2 := by
    simpa [intervalNeumannResolverSourceCoeff_zero, sub_zero] using
      resolverSourceCoeff_re_sq_summable_of_continuousOn p hUc₂
  have hsum₁ := resolver_cosineSeries_summable_of_sourceL2 p hl2₁ x.1
  have hsum₂ := resolver_cosineSeries_summable_of_sourceL2 p hl2₂ x.1
  have hbound := intervalNeumannResolverR_sup_lipschitz p u₁ u₂ hsrc x hsum₁ hsum₂
  refine hbound.trans ?_
  exact mul_le_mul_of_nonneg_left
    (source_coeffL2Norm_diff_le_of_bounded p hγ hUc₁ hUc₂ hmem₁ hmem₂ hD)
    (Real.sqrt_nonneg _)

/-- **B4 (gradient difference).**  `‖∂ₓ(E u₁) − ∂ₓ(E u₂)‖∞ ≤
sqrt(∑(kπ/(μ+λₖ))²)·2νγM^{γ-1}·D`. -/
theorem resolverGrad_diff_sup_le_of_bounded
    (p : CM2Params) (hγ : 1 ≤ p.γ) {u₁ u₂ : intervalDomainPoint → ℝ} {M D : ℝ}
    (hUc₁ : ContinuousOn (intervalDomainLift u₁) (Set.Icc (0:ℝ) 1))
    (hUc₂ : ContinuousOn (intervalDomainLift u₂) (Set.Icc (0:ℝ) 1))
    (hmem₁ : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift u₁ x ∈ Set.Icc (0:ℝ) M)
    (hmem₂ : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift u₂ x ∈ Set.Icc (0:ℝ) M)
    (hD : ∀ x ∈ Set.Icc (0:ℝ) 1,
      |intervalDomainLift u₁ x - intervalDomainLift u₂ x| ≤ D)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    |resolverGradReal p u₁ x - resolverGradReal p u₂ x| ≤
      Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * (p.γ * M ^ (p.γ - 1)) * D)) := by
  have hsrc := resolverSourceCoeff_diff_re_sq_summable_of_continuousOn p hUc₁ hUc₂
  have hl2₁ : Summable fun k : ℕ => ((intervalNeumannResolverSourceCoeff p u₁ k).re) ^ 2 := by
    simpa [intervalNeumannResolverSourceCoeff_zero, sub_zero] using
      resolverSourceCoeff_re_sq_summable_of_continuousOn p hUc₁
  have hl2₂ : Summable fun k : ℕ => ((intervalNeumannResolverSourceCoeff p u₂ k).re) ^ 2 := by
    simpa [intervalNeumannResolverSourceCoeff_zero, sub_zero] using
      resolverSourceCoeff_re_sq_summable_of_continuousOn p hUc₂
  have hsum₁ := resolver_sineSeries_summable_of_sourceL2 p hl2₁ x
  have hsum₂ := resolver_sineSeries_summable_of_sourceL2 p hl2₂ x
  have hbound := intervalNeumannResolverR_grad_sup_lipschitz p u₁ u₂ hsrc ⟨x, hx⟩ hsum₁ hsum₂
  rw [resolverGradReal_eq p u₁ ⟨x, hx⟩, resolverGradReal_eq p u₂ ⟨x, hx⟩]
  refine hbound.trans ?_
  exact mul_le_mul_of_nonneg_left
    (source_coeffL2Norm_diff_le_of_bounded p hγ hUc₁ hUc₂ hmem₁ hmem₂ hD)
    (Real.sqrt_nonneg _)

end ShenWork.IntervalResolverWeakBounds
