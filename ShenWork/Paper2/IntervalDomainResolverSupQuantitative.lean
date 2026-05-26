/-
  Quantitative single-resolver value & gradient sup bounds `F(M)` (Piece 1).

  The prior agent (`IntervalDomainL2UBoundedDatumUniformOfBounded` header) flagged
  that `resolverGradReal_bounded` / `lift_v_bounded` give the resolver value/gradient
  sup bounds only via continuity on the compact `[0,1]`, with NO explicit dependence
  on a uniform sup bound `M` of the solution.  This file closes that analytic gap:
  it proves τ-independent sup bounds

    `|intervalNeumannResolverR p u x|      ≤ Fv(M)`,
    `|intervalNeumannResolverRGrad p u x|  ≤ Fg(M)`,

  whenever the lift of `u` satisfies `0 ≤ lift u y ≤ M` on `[0,1]`, with the explicit
  operator-norm constants

    `Fv(M) = sqrt(∑ₖ 1/(μ+λ_k)²)        · 2·ν·M^γ`,
    `Fg(M) = sqrt(∑ₖ (kπ/(μ+λ_k))²)     · 2·ν·M^γ`.

  These are exactly "(operator-norm constant)·S" with `S = 2·ν·M^γ` a uniform bound
  on the source `L²`-mass `coeffL2Norm(â(u))` (cosine-Bessel: the source `ν u^γ`
  satisfies `‖ν u^γ‖ ≤ ν M^γ` pointwise on `[0,1]`, so its coefficient `ℓ²` norm is
  `≤ 2·sqrt(∫ (ν u^γ)²) ≤ 2·ν·M^γ` on the unit interval).

  The route reuses the PROVEN difference sup-Lipschitz lemmas
  `intervalNeumannResolverR_sup_lipschitz` / `…_grad_sup_lipschitz` against the
  ZERO source `u₂ = (fun _ => 0)` (whose resolver value and gradient series vanish,
  `intervalNeumannResolverR_zero` / `…RGrad_zero`), so the difference becomes the
  single resolver and the coefficient `ℓ²` Lipschitz bound becomes a single source
  `ℓ²` mass.  The per-point summability side-conditions are the PROVED
  `solution_resolver_(cosine|sine)Series_summable`; the source `ℓ²` summability is
  `source_resolverCoeff_re_sq_summable`.

  No `sorry`, no `admit`, no custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainL2StaticVDifference

open MeasureTheory intervalIntegral
open ShenWork.IntervalDomain ShenWork.CosineSpectrum
open ShenWork.PDE ShenWork.IntervalEllipticCharacterization
open ShenWork.IntervalCosineCoeffDecay ShenWork.IntervalCosineInversion
open ShenWork.HeatKernelGradientEstimates ShenWork.IntervalNeumannFullKernel
open ShenWork.PDE.ResolventEstimate ShenWork.CosineParsevalBridge
open ShenWork.IntervalResolverGradientBridge
open ShenWork.Paper3 (unitIntervalNeumannSpectrum)
open scoped Topology BigOperators

namespace ShenWork.Paper2

noncomputable section

/-- The zero coefficient field: the source cosine coefficients of the zero
function vanish (the source `ν·0^γ = 0` since `γ > 0`, so every raw cosine
coefficient is the integral of `0`). -/
theorem intervalNeumannResolverSourceCoeff_zero (p : CM2Params) (k : ℕ) :
    intervalNeumannResolverSourceCoeff p (fun _ => 0) k = 0 := by
  have hγ : p.γ ≠ 0 := ne_of_gt p.hγ
  -- the source function `ν · (lift 0)^γ` is identically `0` on ℝ.
  have hzero : (fun x : ℝ =>
      ((p.ν * intervalDomainLift (fun _ => (0:ℝ)) x ^ p.γ : ℝ) : ℂ)) = fun _ => 0 := by
    funext x
    have hl : intervalDomainLift (fun _ => (0:ℝ)) x = 0 := by
      unfold intervalDomainLift; by_cases hx : x ∈ Set.Icc (0:ℝ) 1 <;> simp [hx]
    rw [hl, Real.zero_rpow hγ]
    simp
  unfold intervalNeumannResolverSourceCoeff
  rw [hzero]
  simp [unitIntervalNeumannCosineCoeff, unitIntervalCosineRawCoeff]

/-- The resolved coefficient of the zero function vanishes. -/
theorem intervalNeumannResolverCoeff_zero (p : CM2Params) (k : ℕ) :
    intervalNeumannResolverCoeff p (fun _ => 0) k = 0 := by
  unfold intervalNeumannResolverCoeff shiftedNeumannResolventCoeff
  rw [intervalNeumannResolverSourceCoeff_zero]
  ring

/-- The resolver value series of the zero function vanishes. -/
theorem intervalNeumannResolverR_zero (p : CM2Params) (x : intervalDomainPoint) :
    intervalNeumannResolverR p (fun _ => 0) x = 0 := by
  unfold intervalNeumannResolverR
  simp [intervalNeumannResolverCoeff_zero]

/-- The resolver gradient series of the zero function vanishes. -/
theorem intervalNeumannResolverRGrad_zero (p : CM2Params) (x : intervalDomainPoint) :
    intervalNeumannResolverRGrad p (fun _ => 0) x = 0 := by
  unfold intervalNeumannResolverRGrad
  simp [intervalNeumannResolverCoeff_zero]

/-- Pointwise/sine summability of the zero function's resolver series (both are the
zero series, trivially summable). -/
theorem zero_resolver_cosineSeries_summable (p : CM2Params) (x : ℝ) :
    Summable fun k : ℕ =>
      (intervalNeumannResolverCoeff p (fun _ => 0) k).re * unitIntervalCosineMode k x := by
  simp only [intervalNeumannResolverCoeff_zero, Complex.zero_re, zero_mul]
  exact summable_zero

theorem zero_resolver_sineSeries_summable (p : CM2Params) (x : ℝ) :
    Summable fun k : ℕ =>
      (intervalNeumannResolverCoeff p (fun _ => 0) k).re *
        (-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * x)) := by
  simp only [intervalNeumannResolverCoeff_zero, Complex.zero_re, zero_mul]
  exact summable_zero

/-- The source `ℓ²` summability for the single function `u` (against the zero
source), the form required by the sup-Lipschitz lemmas. -/
theorem source_resolverCoeff_re_sq_summable_single
    {p : CM2Params} {T : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T) :
    Summable fun k : ℕ =>
      ((intervalNeumannResolverSourceCoeff p (u τ) k -
        intervalNeumannResolverSourceCoeff p (fun _ => 0) k).re) ^ 2 := by
  simp only [intervalNeumannResolverSourceCoeff_zero, sub_zero]
  -- the single-function source-coefficient `re`-square is summable (cosine-Bessel).
  set g : ℝ → ℝ := fun x => p.ν * intervalDomainLift (u τ) x ^ p.γ with hg
  have hgcont : ContinuousOn g (Set.Icc (0:ℝ) 1) := source_continuousOn_Icc hsol hτ
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
  have : (intervalNeumannResolverSourceCoeff p (u τ) k).re =
      unitIntervalNeumannCosineCoeff f k := by
    simp only [intervalNeumannResolverSourceCoeff, hf, hg, Complex.ofReal_re]
  rw [this]

/-- **The uniform source `ℓ²`-mass bound `coeffL2Norm(â(u)) ≤ 2·ν·M^γ`.**
With `0 ≤ lift(u τ) y ≤ M` on `[0,1]` the source `ν·u^γ ∈ [0, ν M^γ]` pointwise,
so `∫₀¹ (ν u^γ)² ≤ (ν M^γ)²` (unit-measure interval) and cosine-Bessel gives
`coeffL2Norm(â(u)) ≤ 2·sqrt(∫ (ν u^γ)²) ≤ 2·ν·M^γ`. -/
theorem source_coeffL2Norm_le
    {p : CM2Params} {T : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {τ M : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T)
    (hub : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u τ) x ≤ M) :
    coeffL2Norm
        (fun k : ℕ => intervalNeumannResolverSourceCoeff p (u τ) k -
          intervalNeumannResolverSourceCoeff p (fun _ => 0) k)
      ≤ 2 * (p.ν * M ^ p.γ) := by
  classical
  simp only [intervalNeumannResolverSourceCoeff_zero, sub_zero]
  set g : ℝ → ℝ := fun x => p.ν * intervalDomainLift (u τ) x ^ p.γ with hg
  have hgcont : ContinuousOn g (Set.Icc (0:ℝ) 1) := source_continuousOn_Icc hsol hτ
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
  -- identify `(source coeff).re` with the cosine coefficient of `f`.
  have hre : ∀ k : ℕ,
      (intervalNeumannResolverSourceCoeff p (u τ) k).re = unitIntervalNeumannCosineCoeff f k := by
    intro k; simp only [intervalNeumannResolverSourceCoeff, hf, hg, Complex.ofReal_re]
  -- `‖f x‖² = g x ²`.
  have hfg : ∀ x, ‖f x‖ ^ 2 = (g x) ^ 2 := by
    intro x; rw [hf]; rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  -- `M ≥ 0` (from `0 ≤ lift ≤ M` and the lift is `≥ 0` on `[0,1]`).
  have hMnn : 0 ≤ M := by
    have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := by constructor <;> norm_num
    have hpos : 0 < intervalDomainLift (u τ) 0 := solution_lift_pos hsol hτ 0 h0
    exact le_trans hpos.le (hub 0 h0)
  -- `∫₀¹ g² ≤ (ν M^γ)²`.
  have hgptw : ∀ x ∈ Set.Icc (0:ℝ) 1, (g x) ^ 2 ≤ (p.ν * M ^ p.γ) ^ 2 := by
    intro x hx
    have hpos : 0 < intervalDomainLift (u τ) x := solution_lift_pos hsol hτ x hx
    have hle : intervalDomainLift (u τ) x ^ p.γ ≤ M ^ p.γ :=
      Real.rpow_le_rpow hpos.le (hub x hx) p.hγ.le
    have hgnn : 0 ≤ g x := by
      rw [hg]; exact mul_nonneg p.hν.le (Real.rpow_nonneg hpos.le p.γ)
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
  -- `coeffL2Norm = TsumNorm` of the cosine coefficients of `f`.
  have hnorm_eq : coeffL2Norm
      (fun k : ℕ => intervalNeumannResolverSourceCoeff p (u τ) k)
      = unitIntervalCosineL2TsumNorm (unitIntervalNeumannCosineCoeff f) := by
    rw [coeffL2Norm, coeffL2Energy, unitIntervalCosineL2TsumNorm,
      unitIntervalCosineL2TsumEnergy]
    congr 1
    refine tsum_congr (fun k => ?_)
    have him : (intervalNeumannResolverSourceCoeff p (u τ) k).im = 0 := by
      simp [intervalNeumannResolverSourceCoeff]
    rw [Complex.sq_norm, Complex.normSq_apply, him, hre k]; ring
  rw [hnorm_eq]
  refine hnorm_le.trans ?_
  -- `2·sqrt(∫‖f‖²) ≤ 2·ν·M^γ`.
  rw [hIeq]
  have hsqrt : Real.sqrt (∫ x in (0:ℝ)..1, (g x) ^ 2) ≤ p.ν * M ^ p.γ := by
    have hnn : 0 ≤ p.ν * M ^ p.γ := mul_nonneg p.hν.le (Real.rpow_nonneg hMnn p.γ)
    rw [show p.ν * M ^ p.γ = Real.sqrt ((p.ν * M ^ p.γ) ^ 2) from (Real.sqrt_sq hnn).symm]
    exact Real.sqrt_le_sqrt hIle
  linarith

/-- **Piece 1, value sup bound `Fv(M)`.**  Quantitative τ-independent sup bound on
the resolver VALUE (= the lifted chemical concentration `v`), explicit in a uniform
upper bound `M` on the solution:

  `|intervalNeumannResolverR p (u τ) x| ≤ Fv(M)`,  `Fv(M) = sqrt(∑ₖ 1/(μ+λ_k)²)·2·ν·M^γ`.

Proof: apply the proven difference sup-Lipschitz `intervalNeumannResolverR_sup_lipschitz`
with `u₂ = (fun _ => 0)` (whose resolver value vanishes), then bound the resulting
source `ℓ²`-mass by `source_coeffL2Norm_le`. -/
theorem resolverValue_sup_le_of_ub
    {p : CM2Params} {T : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {τ M : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T)
    (hub : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u τ) x ≤ M)
    (x : intervalDomainPoint) :
    |intervalNeumannResolverR p (u τ) x| ≤
      Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2) * (2 * (p.ν * M ^ p.γ)) := by
  have hsrc := source_resolverCoeff_re_sq_summable_single hsol hτ
  have hsum₁ := solution_resolver_cosineSeries_summable hsol hτ x.1
  have hsum₂ := zero_resolver_cosineSeries_summable p x.1
  have hbound := intervalNeumannResolverR_sup_lipschitz p (u τ) (fun _ => 0) hsrc x hsum₁ hsum₂
  rw [intervalNeumannResolverR_zero, sub_zero] at hbound
  refine hbound.trans ?_
  have hWnn : 0 ≤ Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2) :=
    Real.sqrt_nonneg _
  exact mul_le_mul_of_nonneg_left (source_coeffL2Norm_le hsol hτ hub) hWnn

/-- **Piece 1, gradient sup bound `Fg(M)`.**  Quantitative τ-independent sup bound on
the resolver GRADIENT `resolverGradReal p (u τ)` (= the spatial gradient of `v`),
explicit in a uniform upper bound `M`:

  `|resolverGradReal p (u τ) x| ≤ Fg(M)`,  `Fg(M) = sqrt(∑ₖ (kπ/(μ+λ_k))²)·2·ν·M^γ`.

Same route via `intervalNeumannResolverR_grad_sup_lipschitz` against the zero source. -/
theorem resolverGrad_sup_le_of_ub
    {p : CM2Params} {T : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {τ M : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T)
    (hub : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u τ) x ≤ M)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    |resolverGradReal p (u τ) x| ≤
      Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * M ^ p.γ)) := by
  have hsrc := source_resolverCoeff_re_sq_summable_single hsol hτ
  have hsum₁ := solution_resolver_sineSeries_summable hsol hτ x
  have hsum₂ := zero_resolver_sineSeries_summable p x
  have hbound := intervalNeumannResolverR_grad_sup_lipschitz p (u τ) (fun _ => 0) hsrc
    ⟨x, hx⟩ hsum₁ hsum₂
  rw [intervalNeumannResolverRGrad_zero, sub_zero] at hbound
  rw [resolverGradReal_eq p (u τ) ⟨x, hx⟩]
  refine hbound.trans ?_
  have hWnn : 0 ≤ Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) :=
    Real.sqrt_nonneg _
  exact mul_le_mul_of_nonneg_left (source_coeffL2Norm_le hsol hτ hub) hWnn

/-- **Uniform source-difference `L²` mass** (the `(δ,M)`-explicit analogue of
`source_integral_le_Eu`).  With `lift(uᵢ τ) ∈ [δ,M]` (δ>0) on `[0,1]`, the source
difference `L²` mass is `≤ (ν·γ(δ^{γ-1}+M^{γ-1}))²·E_u`.  Proven directly from the
uniform `rpow_lipschitz_on_pos_Icc`.  (Copy of `source_integral_le_Eu_uniform_q`, kept
here to avoid a downstream import.) -/
theorem source_integral_le_Eu_uniform_q
    {p : CM2Params} {T₁ T₂ : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂)
    {δ M τ : ℝ} (hδ : 0 < δ)
    (hmem₁ : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u₁ τ) x ∈ Set.Icc δ M)
    (hmem₂ : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u₂ τ) x ∈ Set.Icc δ M)
    (hτ₁ : τ ∈ Set.Ioo (0 : ℝ) T₁) (hτ₂ : τ ∈ Set.Ioo (0 : ℝ) T₂) :
    (∫ x in (0:ℝ)..1, (p.ν * intervalDomainLift (u₁ τ) x ^ p.γ
        - p.ν * intervalDomainLift (u₂ τ) x ^ p.γ) ^ 2)
      ≤ (p.ν * (p.γ * (δ ^ (p.γ - 1) + M ^ (p.γ - 1)))) ^ 2 *
          intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ := by
  classical
  set L : ℝ := p.γ * (δ ^ (p.γ - 1) + M ^ (p.γ - 1)) with hLdef
  have hptwise : ∀ x ∈ Set.Icc (0:ℝ) 1,
      (p.ν * intervalDomainLift (u₁ τ) x ^ p.γ
        - p.ν * intervalDomainLift (u₂ τ) x ^ p.γ) ^ 2
      ≤ (p.ν * L) ^ 2 *
        (intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x) ^ 2 := by
    intro x hxIcc
    have hlip := rpow_lipschitz_on_pos_Icc p.hγ hδ (hmem₁ x hxIcc) (hmem₂ x hxIcc)
    have habs : |intervalDomainLift (u₁ τ) x ^ p.γ - intervalDomainLift (u₂ τ) x ^ p.γ|
        ≤ L * |intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x| := hlip
    have hsq := mul_self_le_mul_self (abs_nonneg _) habs
    have hsq2 : (intervalDomainLift (u₁ τ) x ^ p.γ - intervalDomainLift (u₂ τ) x ^ p.γ) ^ 2
        ≤ L ^ 2 * (intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x) ^ 2 := by
      rw [← sq_abs (intervalDomainLift (u₁ τ) x ^ p.γ - intervalDomainLift (u₂ τ) x ^ p.γ),
          ← sq_abs (intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x)]
      calc |intervalDomainLift (u₁ τ) x ^ p.γ - intervalDomainLift (u₂ τ) x ^ p.γ| ^ 2
          = |intervalDomainLift (u₁ τ) x ^ p.γ - intervalDomainLift (u₂ τ) x ^ p.γ| *
            |intervalDomainLift (u₁ τ) x ^ p.γ - intervalDomainLift (u₂ τ) x ^ p.γ| := by ring
        _ ≤ (L * |intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x|) *
            (L * |intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x|) := hsq
        _ = L ^ 2 * |intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x| ^ 2 := by ring
    have hνsq : (0:ℝ) ≤ p.ν ^ 2 := by positivity
    calc (p.ν * intervalDomainLift (u₁ τ) x ^ p.γ
            - p.ν * intervalDomainLift (u₂ τ) x ^ p.γ) ^ 2
        = p.ν ^ 2 *
            (intervalDomainLift (u₁ τ) x ^ p.γ - intervalDomainLift (u₂ τ) x ^ p.γ) ^ 2 := by ring
      _ ≤ p.ν ^ 2 *
            (L ^ 2 * (intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq2 hνsq
      _ = (p.ν * L) ^ 2 *
            (intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x) ^ 2 := by ring
  have hEu : intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ
      = ∫ x in (0:ℝ)..1,
        (intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x) ^ 2 := by
    unfold intervalDomainClassicalL2DifferenceEnergyU
    show intervalDomainIntegral (fun x => (u₁ τ x - u₂ τ x) ^ 2)
      = ∫ x in (0:ℝ)..1, (intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x) ^ 2
    unfold intervalDomainIntegral
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
    simp only [intervalDomainLift, hx, dif_pos]
  rw [hEu, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ hptwise
  · have hc1 := source_continuousOn_Icc hsol₁ hτ₁
    have hc2 := source_continuousOn_Icc hsol₂ hτ₂
    have : ContinuousOn (fun x => (p.ν * intervalDomainLift (u₁ τ) x ^ p.γ
        - p.ν * intervalDomainLift (u₂ τ) x ^ p.γ) ^ 2) (Set.uIcc (0:ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact ((hc1.sub hc2).pow 2)
    exact this.intervalIntegrable
  · have hcu1 : ContinuousOn (intervalDomainLift (u₁ τ)) (Set.Icc (0:ℝ) 1) :=
      ((hsol₁.regularity.2.2.2.2.2.2.1 τ hτ₁).1.1).continuousOn
    have hcu2 : ContinuousOn (intervalDomainLift (u₂ τ)) (Set.Icc (0:ℝ) 1) :=
      ((hsol₂.regularity.2.2.2.2.2.2.1 τ hτ₂).1.1).continuousOn
    have : ContinuousOn (fun x => (p.ν * L) ^ 2 *
        (intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x) ^ 2)
        (Set.uIcc (0:ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact continuousOn_const.mul ((hcu1.sub hcu2).pow 2)
    exact this.intervalIntegrable

/-! ## Uniform static `v`-control constants (explicit in `(δ,M)`)

The static value/gradient `L²`-control lemmas `static_v_value_L2_le_Eu` /
`static_v_grad_L2_le_Eu` produce an EXISTENTIAL constant whose only τ-dependence is
the local `x↦x^γ` Lipschitz constant `L`.  Under a uniform two-sided lift bound
`[δ,M]` (δ>0) we replace the existential `source_integral_le_Eu` by the EXPLICIT
`source_integral_le_Eu_uniform_q`, yielding τ-independent control constants. -/

/-- **Uniform static `v`-value control.**  With `lift(uᵢ τ) ∈ [δ,M]` on `[0,1]`,
`∫₀¹(lift v₁ − lift v₂)² ≤ Cval_unif · E_u` with the EXPLICIT τ-independent
`Cval_unif = (∑ₖ weightₖ²)·4·(ν·γ(δ^{γ-1}+M^{γ-1}))²`. -/
theorem static_v_value_L2_le_Eu_uniform
    {p : CM2Params} {T₁ T₂ : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂)
    {δ M τ : ℝ} (hδ : 0 < δ)
    (hmem₁ : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u₁ τ) x ∈ Set.Icc δ M)
    (hmem₂ : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u₂ τ) x ∈ Set.Icc δ M)
    (hτ₁ : τ ∈ Set.Ioo (0 : ℝ) T₁) (hτ₂ : τ ∈ Set.Ioo (0 : ℝ) T₂) :
    (∫ x in (0:ℝ)..1,
      (intervalDomainLift (v₁ τ) x - intervalDomainLift (v₂ τ) x) ^ 2)
      ≤ ((Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2)) ^ 2 * 4 *
          (p.ν * (p.γ * (δ ^ (p.γ - 1) + M ^ (p.γ - 1)))) ^ 2) *
        intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ := by
  classical
  set Csup2 : ℝ := (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2)) ^ 2
    with hCsup2
  set A : ℕ → ℂ := fun k => intervalNeumannResolverSourceCoeff p (u₁ τ) k -
    intervalNeumannResolverSourceCoeff p (u₂ τ) k with hA
  have hCsup2_nn : 0 ≤ Csup2 := by rw [hCsup2]; positivity
  have hCe_nn : 0 ≤ coeffL2Energy A := by
    unfold coeffL2Energy; exact tsum_nonneg (fun k => by positivity)
  have hsrc := source_resolverCoeff_re_sq_summable hsol₁ hsol₂ hτ₁ hτ₂
  set B : ℝ := Csup2 * coeffL2Energy A with hB
  have hpt : ∀ x ∈ Set.Ioo (0:ℝ) 1,
      (intervalDomainLift (v₁ τ) x - intervalDomainLift (v₂ τ) x) ^ 2 ≤ B := by
    intro x hxIoo
    have h1 := solution_v_eq_resolver_pointwise_unconditional hsol₁ hτ₁ hxIoo
    have h2 := solution_v_eq_resolver_pointwise_unconditional hsol₂ hτ₂ hxIoo
    have hsum₁ := solution_resolver_cosineSeries_summable hsol₁ hτ₁ x
    have hsum₂ := solution_resolver_cosineSeries_summable hsol₂ hτ₂ x
    have hbound := intervalNeumannResolverR_sup_lipschitz p (u₁ τ) (u₂ τ) hsrc
      ⟨x, Set.Ioo_subset_Icc_self hxIoo⟩ hsum₁ hsum₂
    rw [← h1, ← h2]
    have hge : |intervalNeumannResolverR p (u₁ τ) ⟨x, Set.Ioo_subset_Icc_self hxIoo⟩ -
        intervalNeumannResolverR p (u₂ τ) ⟨x, Set.Ioo_subset_Icc_self hxIoo⟩|
        ≤ Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2) *
          coeffL2Norm A := hbound
    have hsq := mul_self_le_mul_self (abs_nonneg _) hge
    rw [← sq_abs]
    calc |intervalNeumannResolverR p (u₁ τ) ⟨x, Set.Ioo_subset_Icc_self hxIoo⟩ -
            intervalNeumannResolverR p (u₂ τ) ⟨x, Set.Ioo_subset_Icc_self hxIoo⟩| ^ 2
        = |intervalNeumannResolverR p (u₁ τ) ⟨x, Set.Ioo_subset_Icc_self hxIoo⟩ -
            intervalNeumannResolverR p (u₂ τ) ⟨x, Set.Ioo_subset_Icc_self hxIoo⟩| *
          |intervalNeumannResolverR p (u₁ τ) ⟨x, Set.Ioo_subset_Icc_self hxIoo⟩ -
            intervalNeumannResolverR p (u₂ τ) ⟨x, Set.Ioo_subset_Icc_self hxIoo⟩| := by ring
      _ ≤ (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2) * coeffL2Norm A) *
          (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2) * coeffL2Norm A) := hsq
      _ = B := by
          have hWnn : 0 ≤ ∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2 :=
            tsum_nonneg (fun k => sq_nonneg _)
          rw [hB, hCsup2]; unfold coeffL2Norm
          rw [Real.sq_sqrt hWnn,
            show (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2) *
                Real.sqrt (coeffL2Energy A)) *
              (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2) *
                Real.sqrt (coeffL2Energy A))
              = (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2) *
                  Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2)) *
                (Real.sqrt (coeffL2Energy A) * Real.sqrt (coeffL2Energy A)) by ring,
            Real.mul_self_sqrt hWnn, Real.mul_self_sqrt hCe_nn]
  have hintLHS : IntervalIntegrable
      (fun x => (intervalDomainLift (v₁ τ) x - intervalDomainLift (v₂ τ) x) ^ 2) volume 0 1 := by
    have hc1 : ContinuousOn (intervalDomainLift (v₁ τ)) (Set.Icc (0:ℝ) 1) :=
      ((hsol₁.regularity.2.2.2.2.2.2.1 τ hτ₁).2.1).continuousOn
    have hc2 : ContinuousOn (intervalDomainLift (v₂ τ)) (Set.Icc (0:ℝ) 1) :=
      ((hsol₂.regularity.2.2.2.2.2.2.1 τ hτ₂).2.1).continuousOn
    have : ContinuousOn (fun x => (intervalDomainLift (v₁ τ) x -
        intervalDomainLift (v₂ τ) x) ^ 2) (Set.uIcc (0:ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact (hc1.sub hc2).pow 2
    exact this.intervalIntegrable
  have hle_int : (∫ x in (0:ℝ)..1,
        (intervalDomainLift (v₁ τ) x - intervalDomainLift (v₂ τ) x) ^ 2) ≤ B := by
    have hBI : IntervalIntegrable (fun _ : ℝ => B) volume 0 1 :=
      (continuous_const).intervalIntegrable 0 1
    have hmono : (∫ x in (0:ℝ)..1,
        (intervalDomainLift (v₁ τ) x - intervalDomainLift (v₂ τ) x) ^ 2)
        ≤ ∫ _ in (0:ℝ)..1, B := by
      refine intervalIntegral.integral_mono_ae_restrict (by norm_num) hintLHS hBI ?_
      refine (ae_restrict_iff' (measurableSet_Icc (a := (0:ℝ)) (b := 1))).2 ?_
      have hnull : volume (insert (0:ℝ) ({(1:ℝ)} : Set ℝ)) = 0 :=
        Set.Finite.measure_zero ((Set.finite_singleton (1:ℝ)).insert (0:ℝ)) volume
      refine (MeasureTheory.ae_iff).2 (measure_mono_null ?_ hnull)
      intro x hx
      simp only [Set.mem_setOf_eq] at hx
      push_neg at hx
      obtain ⟨hxIcc, hne⟩ := hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      by_contra hcon
      push_neg at hcon
      obtain ⟨hx0, hx1⟩ := hcon
      exact absurd (hpt x ⟨lt_of_le_of_ne hxIcc.1 (Ne.symm hx0),
        lt_of_le_of_ne hxIcc.2 hx1⟩) (not_le.mpr hne)
    have hconst : (∫ _x in (0:ℝ)..1, B ∂volume) = B := by
      rw [intervalIntegral.integral_const, sub_zero, one_smul]
    rwa [hconst] at hmono
  have hEnergy_le := sourceCoeff_diff_energy_le_integral hsol₁ hsol₂ hτ₁ hτ₂
  have hsrcint := source_integral_le_Eu_uniform_q hsol₁ hsol₂ hδ hmem₁ hmem₂ hτ₁ hτ₂
  set L : ℝ := p.γ * (δ ^ (p.γ - 1) + M ^ (p.γ - 1)) with hLdef
  have hEu_nn : 0 ≤ intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ :=
    intervalDomainClassicalL2DifferenceEnergyU_nonneg u₁ u₂ τ
  refine hle_int.trans ?_
  have hstep1 : B ≤ Csup2 * (4 * ∫ x in (0:ℝ)..1,
      (p.ν * intervalDomainLift (u₁ τ) x ^ p.γ
        - p.ν * intervalDomainLift (u₂ τ) x ^ p.γ) ^ 2) := by
    rw [hB]; exact mul_le_mul_of_nonneg_left hEnergy_le hCsup2_nn
  calc B ≤ Csup2 * (4 * ∫ x in (0:ℝ)..1,
        (p.ν * intervalDomainLift (u₁ τ) x ^ p.γ
          - p.ν * intervalDomainLift (u₂ τ) x ^ p.γ) ^ 2) := hstep1
    _ ≤ Csup2 * (4 * ((p.ν * L) ^ 2 *
          intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ)) := by
        apply mul_le_mul_of_nonneg_left _ hCsup2_nn
        apply mul_le_mul_of_nonneg_left hsrcint (by norm_num)
    _ = (Csup2 * 4 * (p.ν * L) ^ 2) *
          intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ := by ring

/-- **Uniform static `v`-gradient control.**  With `lift(uᵢ τ) ∈ [δ,M]` on `[0,1]`,
`∫₀¹(resolverGrad₁ − resolverGrad₂)² ≤ Cgrad_unif · E_u` with the EXPLICIT
τ-independent `Cgrad_unif = (∑ₖ gradWeightₖ²)·4·(ν·γ(δ^{γ-1}+M^{γ-1}))²`. -/
theorem static_v_grad_L2_le_Eu_uniform
    {p : CM2Params} {T₁ T₂ : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂)
    {δ M τ : ℝ} (hδ : 0 < δ)
    (hmem₁ : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u₁ τ) x ∈ Set.Icc δ M)
    (hmem₂ : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u₂ τ) x ∈ Set.Icc δ M)
    (hτ₁ : τ ∈ Set.Ioo (0 : ℝ) T₁) (hτ₂ : τ ∈ Set.Ioo (0 : ℝ) T₂) :
    (∫ x in (0:ℝ)..1,
      (resolverGradReal p (u₁ τ) x - resolverGradReal p (u₂ τ) x) ^ 2)
      ≤ ((Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2)) ^ 2 * 4 *
          (p.ν * (p.γ * (δ ^ (p.γ - 1) + M ^ (p.γ - 1)))) ^ 2) *
        intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ := by
  classical
  set Cg2 : ℝ := (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2)) ^ 2
    with hCg2
  set A : ℕ → ℂ := fun k => intervalNeumannResolverSourceCoeff p (u₁ τ) k -
    intervalNeumannResolverSourceCoeff p (u₂ τ) k with hA
  have hCg2_nn : 0 ≤ Cg2 := by rw [hCg2]; positivity
  have hCe_nn : 0 ≤ coeffL2Energy A := by
    unfold coeffL2Energy; exact tsum_nonneg (fun k => by positivity)
  have hsrc := source_resolverCoeff_re_sq_summable hsol₁ hsol₂ hτ₁ hτ₂
  set B : ℝ := Cg2 * coeffL2Energy A with hB
  have hpt : ∀ x ∈ Set.Icc (0:ℝ) 1,
      (resolverGradReal p (u₁ τ) x - resolverGradReal p (u₂ τ) x) ^ 2 ≤ B := by
    intro x hx
    have hsum₁ := solution_resolver_sineSeries_summable hsol₁ hτ₁ x
    have hsum₂ := solution_resolver_sineSeries_summable hsol₂ hτ₂ x
    have hbound := intervalNeumannResolverR_grad_sup_lipschitz p (u₁ τ) (u₂ τ) hsrc
      ⟨x, hx⟩ hsum₁ hsum₂
    rw [resolverGradReal_eq p (u₁ τ) ⟨x, hx⟩, resolverGradReal_eq p (u₂ τ) ⟨x, hx⟩]
    have hge : |intervalNeumannResolverRGrad p (u₁ τ) ⟨x, hx⟩ -
        intervalNeumannResolverRGrad p (u₂ τ) ⟨x, hx⟩|
        ≤ Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
          coeffL2Norm A := hbound
    have hsq := mul_self_le_mul_self (abs_nonneg _) hge
    rw [← sq_abs]
    calc |intervalNeumannResolverRGrad p (u₁ τ) ⟨x, hx⟩ -
            intervalNeumannResolverRGrad p (u₂ τ) ⟨x, hx⟩| ^ 2
        = |intervalNeumannResolverRGrad p (u₁ τ) ⟨x, hx⟩ -
            intervalNeumannResolverRGrad p (u₂ τ) ⟨x, hx⟩| *
          |intervalNeumannResolverRGrad p (u₁ τ) ⟨x, hx⟩ -
            intervalNeumannResolverRGrad p (u₂ τ) ⟨x, hx⟩| := by ring
      _ ≤ (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) * coeffL2Norm A) *
          (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) * coeffL2Norm A) := hsq
      _ = B := by
          have hWnn : 0 ≤ ∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2 :=
            tsum_nonneg (fun k => sq_nonneg _)
          rw [hB, hCg2]; unfold coeffL2Norm
          rw [Real.sq_sqrt hWnn,
            show (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
                Real.sqrt (coeffL2Energy A)) *
              (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
                Real.sqrt (coeffL2Energy A))
              = (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
                  Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2)) *
                (Real.sqrt (coeffL2Energy A) * Real.sqrt (coeffL2Energy A)) by ring,
            Real.mul_self_sqrt hWnn, Real.mul_self_sqrt hCe_nn]
  -- continuity of `resolverGradReal` (same majorant argument as `static_v_grad_L2_le_Eu`).
  have hcontGrad : ∀ {Tj : ℝ} {uj vj : ℝ → intervalDomainPoint → ℝ},
      IsPaper2ClassicalSolution intervalDomain p Tj uj vj →
      τ ∈ Set.Ioo (0:ℝ) Tj →
      Continuous (fun x : ℝ => resolverGradReal p (uj τ) x) := by
    intro Tj uj vj hsolj hτj
    have hdecay := sourceCoeffQuadraticDecay_of_solution hsolj hτj
    have hmaj := resolverGrad_majorant_summable_of_sourceDecay hdecay.C_nonneg hdecay.decay
    refine continuous_tsum (fun k => ?_) hmaj (fun k x => ?_)
    · exact continuous_const.mul (continuous_const.mul
        (Real.continuous_sin.comp (by fun_prop)))
    · rw [Real.norm_eq_abs, abs_mul]
      have hsin : |(-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * x))|
          ≤ (k : ℝ) * Real.pi := by
        rw [abs_mul, abs_neg, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (k:ℝ)),
          abs_of_nonneg Real.pi_pos.le]
        have h1 : |Real.sin ((k : ℝ) * Real.pi * x)| ≤ 1 := Real.abs_sin_le_one _
        nlinarith [mul_nonneg (Nat.cast_nonneg k) Real.pi_pos.le, abs_nonneg
          (Real.sin ((k : ℝ) * Real.pi * x)), h1]
      exact mul_le_mul_of_nonneg_left hsin (abs_nonneg _)
  have hc1 := hcontGrad hsol₁ hτ₁
  have hc2 := hcontGrad hsol₂ hτ₂
  have hintLHS : IntervalIntegrable
      (fun x => (resolverGradReal p (u₁ τ) x - resolverGradReal p (u₂ τ) x) ^ 2) volume 0 1 :=
    ((hc1.sub hc2).pow 2).intervalIntegrable _ _
  have hle_int : (∫ x in (0:ℝ)..1,
        (resolverGradReal p (u₁ τ) x - resolverGradReal p (u₂ τ) x) ^ 2) ≤ B := by
    have hBI : IntervalIntegrable (fun _ : ℝ => B) volume 0 1 :=
      (continuous_const).intervalIntegrable 0 1
    have hmono : (∫ x in (0:ℝ)..1,
        (resolverGradReal p (u₁ τ) x - resolverGradReal p (u₂ τ) x) ^ 2)
        ≤ ∫ _ in (0:ℝ)..1, B :=
      intervalIntegral.integral_mono_on (by norm_num) hintLHS hBI hpt
    have hconst : (∫ _x in (0:ℝ)..1, B ∂volume) = B := by
      rw [intervalIntegral.integral_const, sub_zero, one_smul]
    rwa [hconst] at hmono
  have hEnergy_le := sourceCoeff_diff_energy_le_integral hsol₁ hsol₂ hτ₁ hτ₂
  have hsrcint := source_integral_le_Eu_uniform_q hsol₁ hsol₂ hδ hmem₁ hmem₂ hτ₁ hτ₂
  set L : ℝ := p.γ * (δ ^ (p.γ - 1) + M ^ (p.γ - 1)) with hLdef
  have hEu_nn : 0 ≤ intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ :=
    intervalDomainClassicalL2DifferenceEnergyU_nonneg u₁ u₂ τ
  refine hle_int.trans ?_
  have hstep1 : B ≤ Cg2 * (4 * ∫ x in (0:ℝ)..1,
      (p.ν * intervalDomainLift (u₁ τ) x ^ p.γ
        - p.ν * intervalDomainLift (u₂ τ) x ^ p.γ) ^ 2) := by
    rw [hB]; exact mul_le_mul_of_nonneg_left hEnergy_le hCg2_nn
  calc B ≤ Cg2 * (4 * ∫ x in (0:ℝ)..1,
        (p.ν * intervalDomainLift (u₁ τ) x ^ p.γ
          - p.ν * intervalDomainLift (u₂ τ) x ^ p.γ) ^ 2) := hstep1
    _ ≤ Cg2 * (4 * ((p.ν * L) ^ 2 *
          intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ)) := by
        apply mul_le_mul_of_nonneg_left _ hCg2_nn
        apply mul_le_mul_of_nonneg_left hsrcint (by norm_num)
    _ = (Cg2 * 4 * (p.ν * L) ^ 2) *
          intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ := by ring

end

end ShenWork.Paper2
