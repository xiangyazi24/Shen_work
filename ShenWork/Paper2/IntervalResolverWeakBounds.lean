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
open ShenWork.PDE.ResolventEstimate
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

end ShenWork.IntervalResolverWeakBounds
