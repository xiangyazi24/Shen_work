/-
  Uniform (τ-independent, `(δ,M)`-explicit) energy differential inequality (Piece 2).

  Building on the quantitative single-resolver sup bounds `Fv(M)`/`Fg(M)`
  (`IntervalDomainResolverSupQuantitative`) and the uniform static `v`-control
  constants, this file produces:

  * `flux_diff_L2_le_Eu_uniform` — the chemotaxis-flux `L²`-difference bound with an
    EXPLICIT τ-independent constant `Cflux(δ,M)`, using `U ≤ M`, `G ≤ Fg(M)`, and the
    uniform static control constants `Cgrad_unif`,`Cval_unif`;
  * `intervalDomainL2U_energy_diffIneq_bound_uniform` — the per-time energy
    differential inequality `∫ Eprime ≤ K(δ,M)·E_u` with a SINGLE τ-independent
    Grönwall constant `K(δ,M) = χ₀²·Cflux(δ,M) + 2·L_react(M)`, valid whenever
    `lift(uᵢ τ) ∈ [δ,M]` on `[0,1]`;
  * `GlobalSolutionGluingFromReachability_of_uniformSupBound` — the final gluing
    theorem reduced to the CLEAN, natural "solutions uniformly bounded" hypothesis
    (a uniform two-sided lift bound `[δ,M]`) plus the genuine datum-boundedness input.

  The δ>0 lower bound is needed for the source `x↦x^γ` Lipschitz constant
  `γ(δ^{γ-1}+M^{γ-1})` when `γ<1`; for `γ≥1` the lower bound is harmless (the constant
  is finite for any `δ>0`).  We keep δ as an explicit input for both regimes.

  No `sorry`, no `admit`, no custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainResolverSupQuantitative
import ShenWork.Paper2.IntervalDomainL2UBoundedDatumUniformOfBounded
import ShenWork.Paper2.IntervalDomainGlobalWellposed

open MeasureTheory intervalIntegral
open ShenWork.IntervalDomain
open ShenWork.PDE ShenWork.IntervalEllipticCharacterization
open ShenWork.IntervalResolverGradientBridge
open scoped Topology BigOperators

namespace ShenWork.Paper2

noncomputable section

/-- Explicit τ-independent gradient sup constant `Fg(M)` (piece 1). -/
def FgQuant (p : CM2Params) (M : ℝ) : ℝ :=
  Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) * (2 * (p.ν * M ^ p.γ))

/-- Explicit τ-independent uniform static gradient-control constant `Cgrad(δ,M)`. -/
def CgradQuant (p : CM2Params) (δ M : ℝ) : ℝ :=
  (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2)) ^ 2 * 4 *
    (p.ν * (p.γ * (δ ^ (p.γ - 1) + M ^ (p.γ - 1)))) ^ 2

/-- Explicit τ-independent uniform static value-control constant `Cval(δ,M)`. -/
def CvalQuant (p : CM2Params) (δ M : ℝ) : ℝ :=
  (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2)) ^ 2 * 4 *
    (p.ν * (p.γ * (δ ^ (p.γ - 1) + M ^ (p.γ - 1)))) ^ 2

/-- Explicit τ-independent flux constant `Cflux(δ,M) = 3·(Fg² + M²·Cgrad + (M·Fg·β)²·Cval)`. -/
def CfluxQuant (p : CM2Params) (δ M : ℝ) : ℝ :=
  3 * ((FgQuant p M)^2 + M^2 * CgradQuant p δ M +
    (M * FgQuant p M * p.β)^2 * CvalQuant p δ M)

lemma FgQuant_nonneg (p : CM2Params) {M : ℝ} (hMnn : 0 ≤ M) : 0 ≤ FgQuant p M := by
  rw [FgQuant]
  exact mul_nonneg (Real.sqrt_nonneg _)
    (by have := mul_nonneg p.hν.le (Real.rpow_nonneg hMnn p.γ); linarith)

lemma CgradQuant_nonneg (p : CM2Params) (δ M : ℝ) : 0 ≤ CgradQuant p δ M := by
  rw [CgradQuant]; positivity

lemma CvalQuant_nonneg (p : CM2Params) (δ M : ℝ) : 0 ≤ CvalQuant p δ M := by
  rw [CvalQuant]; positivity

lemma CfluxQuant_nonneg (p : CM2Params) {δ M : ℝ} (hMnn : 0 ≤ M) : 0 ≤ CfluxQuant p δ M := by
  rw [CfluxQuant]
  have h1 := FgQuant_nonneg p hMnn
  have h2 := CgradQuant_nonneg p δ M
  have h3 := CvalQuant_nonneg p δ M
  positivity

/-- **Uniform chemotaxis-flux `L²`-difference bound.**  With `lift(uᵢ τ) ∈ [δ,M]`
(δ>0) on `[0,1]`,

  `∫₀¹ (flux₁ − flux₂)² ≤ Cflux(δ,M) · E_u`,

with the EXPLICIT τ-independent constant `Cflux(δ,M) = 3·(Fg² + M²·Cgrad + (M·Fg·β)²·Cval)`
where `Fg = sqrt(∑ gradWeight²)·2·ν·M^γ` (piece 1) and `Cgrad`,`Cval` are the uniform
static-control constants.  Same route as `flux_diff_L2_le_Eu` with `U ≤ M`,
`G ≤ Fg(M)`. -/
theorem flux_diff_L2_le_Eu_uniform
    {p : CM2Params} {T₁ T₂ : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂)
    {δ M τ : ℝ} (hδ : 0 < δ)
    (hmem₁ : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u₁ τ) x ∈ Set.Icc δ M)
    (hmem₂ : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u₂ τ) x ∈ Set.Icc δ M)
    (hτ₁ : τ ∈ Set.Ioo (0 : ℝ) T₁) (hτ₂ : τ ∈ Set.Ioo (0 : ℝ) T₂) :
      (∫ y in (0:ℝ)..1,
        (intervalFlux p (u₁ τ) (v₁ τ) y - intervalFlux p (u₂ τ) (v₂ τ) y) ^ 2)
        ≤ CfluxQuant p δ M * intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ := by
  classical
  set Eu : ℝ := intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ with hEu
  have hEu_nn : 0 ≤ Eu := intervalDomainClassicalL2DifferenceEnergyU_nonneg u₁ u₂ τ
  have hv₁nn : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ intervalDomainLift (v₁ τ) x :=
    solution_lift_v_nonneg_Icc hsol₁ hτ₁
  have hv₂nn : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ intervalDomainLift (v₂ τ) x :=
    solution_lift_v_nonneg_Icc hsol₂ hτ₂
  -- uniform upper bounds: `U := M` and `G := Fg(M)` (piece 1).
  -- `M ≥ 0` (from `δ ≤ lift ≤ M` and `δ>0`).
  have hMnn : 0 ≤ M := by
    have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := by constructor <;> norm_num
    exact le_trans hδ.le (le_trans (hmem₁ 0 h0).1 (hmem₁ 0 h0).2)
  have hub₁ : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u₁ τ) x ≤ M :=
    fun x hx => (hmem₁ x hx).2
  have hub₂ : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u₂ τ) x ≤ M :=
    fun x hx => (hmem₂ x hx).2
  set Fg : ℝ := Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
    (2 * (p.ν * M ^ p.γ)) with hFg
  have hMγnn : 0 ≤ M ^ p.γ := Real.rpow_nonneg hMnn p.γ
  have hFgnn : 0 ≤ Fg := by
    rw [hFg]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (by have := mul_nonneg p.hν.le hMγnn; linarith)
  have hβnn : 0 ≤ p.β := p.hβ
  -- L∞ bounds for the difference pointwise lemma.
  have hU₁ : ∀ x ∈ Set.Icc (0:ℝ) 1, |intervalDomainLift (u₁ τ) x| ≤ M := by
    intro x hx
    have hpos : 0 < intervalDomainLift (u₁ τ) x := solution_lift_pos hsol₁ hτ₁ x hx
    rw [abs_of_pos hpos]; exact hub₁ x hx
  have hU₂ : ∀ x ∈ Set.Icc (0:ℝ) 1, |intervalDomainLift (u₂ τ) x| ≤ M := by
    intro x hx
    have hpos : 0 < intervalDomainLift (u₂ τ) x := solution_lift_pos hsol₂ hτ₂ x hx
    rw [abs_of_pos hpos]; exact hub₂ x hx
  have hG₁ : ∀ x ∈ Set.Icc (0:ℝ) 1, |resolverGradReal p (u₁ τ) x| ≤ Fg := by
    intro x hx; exact resolverGrad_sup_le_of_ub hsol₁ hτ₁ hub₁ hx
  have hG₂ : ∀ x ∈ Set.Icc (0:ℝ) 1, |resolverGradReal p (u₂ τ) x| ≤ Fg := by
    intro x hx; exact resolverGrad_sup_le_of_ub hsol₂ hτ₂ hub₂ hx
  -- pointwise bound on the interior `(0,1)` of the flux representative.
  have hpt : ∀ y ∈ Set.Ioo (0:ℝ) 1,
      |intervalFluxRepr p (u₁ τ) (v₁ τ) y - intervalFluxRepr p (u₂ τ) (v₂ τ) y|
        ≤ Fg * |intervalDomainLift (u₁ τ) y - intervalDomainLift (u₂ τ) y|
          + M * |resolverGradReal p (u₁ τ) y - resolverGradReal p (u₂ τ) y|
          + M * Fg * p.β
              * |intervalDomainLift (v₁ τ) y - intervalDomainLift (v₂ τ) y| := by
    intro y hy
    have hyIcc : y ∈ Set.Icc (0:ℝ) 1 := Set.Ioo_subset_Icc_self hy
    have ha₁ := hU₁ y hyIcc
    have ha₂ := hU₂ y hyIcc
    have hg₁ := hG₁ y hyIcc
    have hg₂ := hG₂ y hyIcc
    have hq₁ := chemQuotient_mem_Ioc hβnn (hv₁nn y hyIcc)
    have hq₂ := chemQuotient_mem_Ioc hβnn (hv₂nn y hyIcc)
    have hqLip := chemQuotient_lipschitz hβnn (hv₁nn y hyIcc) (hv₂nn y hyIcc)
    have := flux_diff_pointwise_bound
      (a₁ := intervalDomainLift (u₁ τ) y) (a₂ := intervalDomainLift (u₂ τ) y)
      (g₁ := resolverGradReal p (u₁ τ) y) (g₂ := resolverGradReal p (u₂ τ) y)
      (q₁ := (1 + intervalDomainLift (v₁ τ) y) ^ (-p.β))
      (q₂ := (1 + intervalDomainLift (v₂ τ) y) ^ (-p.β))
      (v₁ := intervalDomainLift (v₁ τ) y) (v₂ := intervalDomainLift (v₂ τ) y)
      (U := M) (G := Fg) (Lq := p.β)
      ha₁ ha₂ hg₁ hg₂ hq₁.1.le hq₁.2 hq₂.1.le hq₂.2 hMnn hFgnn hqLip
    simpa only [intervalFluxRepr] using this
  -- square the pointwise bound on `(0,1)`.
  set a := fun y => (intervalDomainLift (u₁ τ) y - intervalDomainLift (u₂ τ) y) with ha
  set gg := fun y => (resolverGradReal p (u₁ τ) y - resolverGradReal p (u₂ τ) y) with hgg
  set vv := fun y => (intervalDomainLift (v₁ τ) y - intervalDomainLift (v₂ τ) y) with hvv
  have hsq : ∀ y ∈ Set.Ioo (0:ℝ) 1,
      (intervalFluxRepr p (u₁ τ) (v₁ τ) y - intervalFluxRepr p (u₂ τ) (v₂ τ) y) ^ 2
        ≤ 3 * (Fg^2 * (a y)^2 + M^2 * (gg y)^2 + (M*Fg*p.β)^2 * (vv y)^2) := by
    intro y hy
    have hb := hpt y hy
    set X := Fg * |a y| with hX
    set Y := M * |gg y| with hY
    set Z := M * Fg * p.β * |vv y| with hZ
    have hXnn : 0 ≤ X := by rw [hX]; positivity
    have hYnn : 0 ≤ Y := by rw [hY]; positivity
    have hZnn : 0 ≤ Z := by rw [hZ]; positivity
    have hb' : |intervalFluxRepr p (u₁ τ) (v₁ τ) y - intervalFluxRepr p (u₂ τ) (v₂ τ) y|
        ≤ X + Y + Z := hb
    have hsq0 : (intervalFluxRepr p (u₁ τ) (v₁ τ) y
          - intervalFluxRepr p (u₂ τ) (v₂ τ) y) ^ 2
        ≤ (X + Y + Z) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb' 2
    refine hsq0.trans ?_
    have hexp : (X + Y + Z) ^ 2 ≤ 3 * (X^2 + Y^2 + Z^2) := by
      nlinarith [sq_nonneg (X-Y), sq_nonneg (Y-Z), sq_nonneg (X-Z)]
    refine hexp.trans ?_
    have hXsq : X^2 = Fg^2 * (a y)^2 := by rw [hX]; rw [mul_pow, sq_abs]
    have hYsq : Y^2 = M^2 * (gg y)^2 := by rw [hY]; rw [mul_pow, sq_abs]
    have hZsq : Z^2 = (M*Fg*p.β)^2 * (vv y)^2 := by rw [hZ]; rw [mul_pow, sq_abs]
    rw [hXsq, hYsq, hZsq]
  -- the flux integral equals the representative integral (interior agreement).
  have hflux_eq : (∫ y in (0:ℝ)..1,
        (intervalFlux p (u₁ τ) (v₁ τ) y - intervalFlux p (u₂ τ) (v₂ τ) y) ^ 2)
      = ∫ y in (0:ℝ)..1,
        (intervalFluxRepr p (u₁ τ) (v₁ τ) y - intervalFluxRepr p (u₂ τ) (v₂ τ) y) ^ 2 := by
    refine intervalIntegral.integral_congr_ae ?_
    have hnull : volume ({(1:ℝ)} : Set ℝ) = 0 := Real.volume_singleton
    refine (MeasureTheory.ae_iff).2 (measure_mono_null ?_ hnull)
    intro y hy
    simp only [Set.mem_setOf_eq] at hy
    push_neg at hy
    obtain ⟨hyIoc0, hne⟩ := hy
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hyIoc0
    simp only [Set.mem_singleton_iff]
    by_contra hy1
    have hyIoo : y ∈ Set.Ioo (0:ℝ) 1 := ⟨hyIoc0.1, lt_of_le_of_ne hyIoc0.2 hy1⟩
    exact hne (by rw [intervalFlux_eq_repr_interior hsol₁ hτ₁ hv₁nn hyIoo,
      intervalFlux_eq_repr_interior hsol₂ hτ₂ hv₂nn hyIoo])
  have hcontR : ContinuousOn
      (fun y => (intervalFluxRepr p (u₁ τ) (v₁ τ) y
        - intervalFluxRepr p (u₂ τ) (v₂ τ) y) ^ 2) (Set.uIcc (0:ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact (((intervalFluxRepr_continuousOn hsol₁ hτ₁ hv₁nn).sub
      (intervalFluxRepr_continuousOn hsol₂ hτ₂ hv₂nn)).pow 2)
  have hintR : IntervalIntegrable
      (fun y => (intervalFluxRepr p (u₁ τ) (v₁ τ) y
        - intervalFluxRepr p (u₂ τ) (v₂ τ) y) ^ 2) volume 0 1 :=
    hcontR.intervalIntegrable
  -- the two static integrals, with the UNIFORM constants.
  have hCg := static_v_grad_L2_le_Eu_uniform hsol₁ hsol₂ hδ hmem₁ hmem₂ hτ₁ hτ₂
  have hCv := static_v_value_L2_le_Eu_uniform hsol₁ hsol₂ hδ hmem₁ hmem₂ hτ₁ hτ₂
  set Cg : ℝ := (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2)) ^ 2 * 4 *
    (p.ν * (p.γ * (δ ^ (p.γ - 1) + M ^ (p.γ - 1)))) ^ 2 with hCgdef
  set Cv : ℝ := (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2)) ^ 2 * 4 *
    (p.ν * (p.γ * (δ ^ (p.γ - 1) + M ^ (p.γ - 1)))) ^ 2 with hCvdef
  have hCgnn : 0 ≤ Cg := by rw [hCgdef]; positivity
  have hCvnn : 0 ≤ Cv := by rw [hCvdef]; positivity
  -- integrability of the three squared difference integrands.
  have hcont_u₁ : ContinuousOn (intervalDomainLift (u₁ τ)) (Set.Icc (0:ℝ) 1) :=
    ((hsol₁.regularity.2.2.2.2.2.2.1 τ hτ₁).1.1).continuousOn
  have hcont_u₂ : ContinuousOn (intervalDomainLift (u₂ τ)) (Set.Icc (0:ℝ) 1) :=
    ((hsol₂.regularity.2.2.2.2.2.2.1 τ hτ₂).1.1).continuousOn
  have hcont_v₁ : ContinuousOn (intervalDomainLift (v₁ τ)) (Set.Icc (0:ℝ) 1) :=
    ((hsol₁.regularity.2.2.2.2.2.2.1 τ hτ₁).2.1).continuousOn
  have hcont_v₂ : ContinuousOn (intervalDomainLift (v₂ τ)) (Set.Icc (0:ℝ) 1) :=
    ((hsol₂.regularity.2.2.2.2.2.2.1 τ hτ₂).2.1).continuousOn
  have hcg₁ := resolverGradReal_continuous hsol₁ hτ₁
  have hcg₂ := resolverGradReal_continuous hsol₂ hτ₂
  have hint_a : IntervalIntegrable (fun y => (a y)^2) volume 0 1 := by
    rw [ha]
    have : ContinuousOn (fun y => (intervalDomainLift (u₁ τ) y
        - intervalDomainLift (u₂ τ) y)^2) (Set.uIcc (0:ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact (hcont_u₁.sub hcont_u₂).pow 2
    exact this.intervalIntegrable
  have hint_g : IntervalIntegrable (fun y => (gg y)^2) volume 0 1 := by
    rw [hgg]; exact (((hcg₁.sub hcg₂).pow 2)).intervalIntegrable _ _
  have hint_v : IntervalIntegrable (fun y => (vv y)^2) volume 0 1 := by
    rw [hvv]
    have : ContinuousOn (fun y => (intervalDomainLift (v₁ τ) y
        - intervalDomainLift (v₂ τ) y)^2) (Set.uIcc (0:ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact (hcont_v₁.sub hcont_v₂).pow 2
    exact this.intervalIntegrable
  set RHSfun := fun y => 3 * (Fg^2 * (a y)^2 + M^2 * (gg y)^2 + (M*Fg*p.β)^2 * (vv y)^2)
    with hRHSfun
  have hint_RHS : IntervalIntegrable RHSfun volume 0 1 := by
    rw [hRHSfun]
    exact (((hint_a.const_mul (Fg^2)).add (hint_g.const_mul (M^2))).add
      (hint_v.const_mul ((M*Fg*p.β)^2))).const_mul 3
  have hmono : (∫ y in (0:ℝ)..1,
        (intervalFluxRepr p (u₁ τ) (v₁ τ) y
          - intervalFluxRepr p (u₂ τ) (v₂ τ) y) ^ 2)
      ≤ ∫ y in (0:ℝ)..1, RHSfun y := by
    have hae : (fun y => (intervalFluxRepr p (u₁ τ) (v₁ τ) y
          - intervalFluxRepr p (u₂ τ) (v₂ τ) y) ^ 2)
        ≤ᵐ[volume.restrict (Set.Icc (0:ℝ) 1)] RHSfun := by
      have hmeas : MeasurableSet (Set.Icc (0:ℝ) 1) := measurableSet_Icc
      refine (ae_restrict_iff' (μ := volume) hmeas).2 ?_
      have hnull : volume (insert (0:ℝ) ({(1:ℝ)} : Set ℝ)) = 0 :=
        Set.Finite.measure_zero
          ((Set.finite_singleton (1:ℝ)).insert (0:ℝ)) volume
      refine (MeasureTheory.ae_iff).2 (measure_mono_null ?_ hnull)
      intro y hy
      simp only [Set.mem_setOf_eq] at hy
      push_neg at hy
      obtain ⟨hyIcc, hne⟩ := hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      by_contra hcon
      push_neg at hcon
      obtain ⟨hy0, hy1⟩ := hcon
      exact absurd (hsq y ⟨lt_of_le_of_ne hyIcc.1 (Ne.symm hy0),
        lt_of_le_of_ne hyIcc.2 hy1⟩) (not_le.mpr hne)
    exact intervalIntegral.integral_mono_ae_restrict (by norm_num) hintR hint_RHS hae
  have hCflux_eq : CfluxQuant p δ M = 3 * (Fg^2 + M^2 * Cg + (M*Fg*p.β)^2 * Cv) := by
    rw [CfluxQuant, hFg, hCgdef, hCvdef, FgQuant, CgradQuant, CvalQuant]
  rw [hCflux_eq, hflux_eq]
  refine hmono.trans ?_
  have hRHSint : (∫ y in (0:ℝ)..1, RHSfun y)
      = 3 * (Fg^2 * (∫ y in (0:ℝ)..1, (a y)^2)
        + M^2 * (∫ y in (0:ℝ)..1, (gg y)^2)
        + (M*Fg*p.β)^2 * (∫ y in (0:ℝ)..1, (vv y)^2)) := by
    rw [hRHSfun]
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_add
        ((hint_a.const_mul (Fg^2)).add (hint_g.const_mul (M^2))) (hint_v.const_mul _),
      intervalIntegral.integral_add (hint_a.const_mul (Fg^2)) (hint_g.const_mul (M^2)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  rw [hRHSint]
  have hIa : (∫ y in (0:ℝ)..1, (a y)^2) = Eu := by
    rw [ha, hEu]; exact lift_u_diff_sq_integral_eq_Eu u₁ u₂ τ
  have hIg : (∫ y in (0:ℝ)..1, (gg y)^2) ≤ Cg * Eu := by rw [hgg, hEu, hCgdef]; exact hCg
  have hIv : (∫ y in (0:ℝ)..1, (vv y)^2) ≤ Cv * Eu := by rw [hvv, hEu, hCvdef]; exact hCv
  rw [hIa]
  have hMFβsq_nn : 0 ≤ (M*Fg*p.β)^2 := sq_nonneg _
  have hM2nn : 0 ≤ M^2 := sq_nonneg _
  calc 3 * (Fg^2 * Eu + M^2 * (∫ y in (0:ℝ)..1, (gg y)^2)
        + (M*Fg*p.β)^2 * (∫ y in (0:ℝ)..1, (vv y)^2))
      ≤ 3 * (Fg^2 * Eu + M^2 * (Cg * Eu) + (M*Fg*p.β)^2 * (Cv * Eu)) := by
        have h1 : M^2 * (∫ y in (0:ℝ)..1, (gg y)^2) ≤ M^2 * (Cg * Eu) :=
          mul_le_mul_of_nonneg_left hIg hM2nn
        have h2 : (M*Fg*p.β)^2 * (∫ y in (0:ℝ)..1, (vv y)^2)
            ≤ (M*Fg*p.β)^2 * (Cv * Eu) :=
          mul_le_mul_of_nonneg_left hIv hMFβsq_nn
        nlinarith [h1, h2]
    _ = 3 * (Fg^2 + M^2 * Cg + (M*Fg*p.β)^2 * Cv) * Eu := by ring

/-- **Uniform per-time energy differential inequality.**  With `lift(uᵢ τ) ∈ [δ,M]`
(δ>0) on `[0,1]`, the `u`-energy Leibniz integrand satisfies

  `∫₀¹ Eprime(τ) ≤ K · E_u(τ)`

with a Grönwall constant `K`.  The constant is `K = χ₀²·Cflux(δ,M) + 2·L_react(M+1)`,
EXPLICIT and τ-independent: the flux part `Cflux(δ,M)` from `flux_diff_L2_le_Eu_uniform`
and the reaction part `L_react` from `intervalLogisticSource_lipschitz p (M+1)` (a
τ-independent constant since the solution range is `⊆ [-(M+1),M+1]`).  Same Young /
IBP route as `intervalDomainL2U_energy_diffIneq_bound`, with the flux bound and the
reaction Lipschitz both uniformized. -/
theorem intervalDomainL2U_energy_diffIneq_bound_uniform_explicit
    {p : CM2Params} {T₁ T₂ : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂)
    {δ M τ L : ℝ} (hδ : 0 < δ)
    (hmem₁ : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u₁ τ) x ∈ Set.Icc δ M)
    (hmem₂ : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u₂ τ) x ∈ Set.Icc δ M)
    (hLip : ∀ a b : ℝ, |a| ≤ M + 1 → |b| ≤ M + 1 →
      |a * (p.a - p.b * a ^ p.α) - b * (p.a - p.b * b ^ p.α)| ≤ L * |a - b|)
    (hτ : τ ∈ Set.Ioo (0 : ℝ) (min T₁ T₂)) :
      (∫ y in (0:ℝ)..1, intervalDomainUEnergyIntegrandDeriv u₁ u₂ τ y)
        ≤ (p.χ₀ ^ 2 * CfluxQuant p δ M + 2 * L) *
          intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ := by
  classical
  have hτ₁ : τ ∈ Set.Ioo (0:ℝ) T₁ := ⟨hτ.1, lt_of_lt_of_le hτ.2 (min_le_left _ _)⟩
  have hτ₂ : τ ∈ Set.Ioo (0:ℝ) T₂ := ⟨hτ.1, lt_of_lt_of_le hτ.2 (min_le_right _ _)⟩
  set Eu : ℝ := intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ with hEu
  have hEu_nn : 0 ≤ Eu := intervalDomainClassicalL2DifferenceEnergyU_nonneg u₁ u₂ τ
  have hMnn : 0 ≤ M := by
    have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := by constructor <;> norm_num
    exact le_trans hδ.le (le_trans (hmem₁ 0 h0).1 (hmem₁ 0 h0).2)
  set wL : ℝ → ℝ := fun y => intervalDomainLift (u₁ τ) y - intervalDomainLift (u₂ τ) y with hwL
  set dwL : ℝ → ℝ := fun y => deriv (intervalDomainLift (u₁ τ)) y
      - deriv (intervalDomainLift (u₂ τ)) y with hdwL
  set Lap : ℝ → ℝ := fun y => deriv (fun z => deriv (intervalDomainLift (u₁ τ)) z) y
      - deriv (fun z => deriv (intervalDomainLift (u₂ τ)) z) y with hLap
  set Fd : ℝ → ℝ := fun y => deriv (intervalFlux p (u₁ τ) (v₁ τ)) y
      - deriv (intervalFlux p (u₂ τ) (v₂ τ)) y with hFd
  set Flx : ℝ → ℝ := fun y => intervalFlux p (u₁ τ) (v₁ τ) y - intervalFlux p (u₂ τ) (v₂ τ) y
    with hFlx
  set Rx : ℝ → ℝ := fun y => intervalDomainLift (u₁ τ) y
        * (p.a - p.b * intervalDomainLift (u₁ τ) y ^ p.α)
      - intervalDomainLift (u₂ τ) y * (p.a - p.b * intervalDomainLift (u₂ τ) y ^ p.α) with hRx
  have hintegrand : Set.EqOn (intervalDomainUEnergyIntegrandDeriv u₁ u₂ τ)
      (fun y => 2 * wL y * (Lap y - p.χ₀ * Fd y + Rx y)) (Set.Ioo (0:ℝ) 1) := by
    intro y hy
    unfold intervalDomainUEnergyIntegrandDeriv
    rw [intervalDomainLift_uDiff_eq u₁ u₂ τ y,
      intervalDomainUEnergy_timeDeriv_pde hsol₁ hsol₂ hτ hy]
  have hwLcont : ContinuousOn wL (Set.uIcc (0:ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact (((hsol₁.regularity.2.2.2.2.2.2.1 τ hτ₁).1.1).continuousOn).sub
      (((hsol₂.regularity.2.2.2.2.2.2.1 τ hτ₂).1.1).continuousOn)
  have hwLcontI : ContinuousOn wL (Set.Icc (0:ℝ) 1) := by
    rw [← Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact hwLcont
  have hdwLint : IntervalIntegrable dwL volume 0 1 := by
    have : ContinuousOn dwL (Set.uIcc (0:ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact (solution_deriv_lift_continuousOn_Icc hsol₁ hτ₁).sub
        (solution_deriv_lift_continuousOn_Icc hsol₂ hτ₂)
    exact this.intervalIntegrable
  have hLapint : IntervalIntegrable Lap volume 0 1 :=
    (solution_lap_lift_intervalIntegrable hsol₁ hτ₁).sub
      (solution_lap_lift_intervalIntegrable hsol₂ hτ₂)
  have hFdint : IntervalIntegrable Fd volume 0 1 :=
    (solution_deriv_flux_intervalIntegrable hsol₁ hτ₁).sub
      (solution_deriv_flux_intervalIntegrable hsol₂ hτ₂)
  have hRxcont : ContinuousOn Rx (Set.uIcc (0:ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    have hcu : ∀ (u : ℝ → intervalDomainPoint → ℝ) {Tj : ℝ}
        {vj : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p Tj u vj → τ ∈ Set.Ioo (0:ℝ) Tj →
        ContinuousOn (fun y => intervalDomainLift (u τ) y
          * (p.a - p.b * intervalDomainLift (u τ) y ^ p.α)) (Set.Icc (0:ℝ) 1) := by
      intro u Tj vj hsolj htj
      have hc : ContinuousOn (intervalDomainLift (u τ)) (Set.Icc (0:ℝ) 1) :=
        ((hsolj.regularity.2.2.2.2.2.2.1 τ htj).1.1).continuousOn
      have hpow : ContinuousOn (fun y => intervalDomainLift (u τ) y ^ p.α) (Set.Icc (0:ℝ) 1) :=
        hc.rpow_const (fun y hy => Or.inl (ne_of_gt (solution_lift_pos hsolj htj y hy)))
      exact hc.mul (continuousOn_const.sub (continuousOn_const.mul hpow))
    exact (hcu u₁ hsol₁ hτ₁).sub (hcu u₂ hsol₂ hτ₂)
  have hwLLap : IntervalIntegrable (fun y => wL y * Lap y) volume 0 1 :=
    hLapint.continuousOn_mul hwLcont
  have hwLFd : IntervalIntegrable (fun y => wL y * Fd y) volume 0 1 :=
    hFdint.continuousOn_mul hwLcont
  have hwLRx : IntervalIntegrable (fun y => wL y * Rx y) volume 0 1 := by
    have hRxint : IntervalIntegrable Rx volume 0 1 := hRxcont.intervalIntegrable
    exact hRxint.continuousOn_mul hwLcont
  have hIeq : (∫ y in (0:ℝ)..1, intervalDomainUEnergyIntegrandDeriv u₁ u₂ τ y)
      = ∫ y in (0:ℝ)..1, 2 * wL y * (Lap y - p.χ₀ * Fd y + Rx y) := by
    refine intervalIntegral.integral_congr_ae ?_
    have hnull : volume ({(1:ℝ)} : Set ℝ) = 0 := Real.volume_singleton
    refine (MeasureTheory.ae_iff).2 (measure_mono_null ?_ hnull)
    intro y hy
    simp only [Set.mem_setOf_eq] at hy
    push_neg at hy
    obtain ⟨hyIoc0, hne⟩ := hy
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hyIoc0
    simp only [Set.mem_singleton_iff]
    by_contra hy1
    exact hne (hintegrand ⟨hyIoc0.1, lt_of_le_of_ne hyIoc0.2 hy1⟩)
  have hsplit : (∫ y in (0:ℝ)..1, 2 * wL y * (Lap y - p.χ₀ * Fd y + Rx y))
      = 2 * (∫ y in (0:ℝ)..1, wL y * Lap y)
        - 2 * p.χ₀ * (∫ y in (0:ℝ)..1, wL y * Fd y)
        + 2 * (∫ y in (0:ℝ)..1, wL y * Rx y) := by
    have hcongr : (fun y => 2 * wL y * (Lap y - p.χ₀ * Fd y + Rx y))
        = fun y => 2 * (wL y * Lap y) + (- (2 * p.χ₀)) * (wL y * Fd y)
            + 2 * (wL y * Rx y) := by
      funext y; ring
    rw [hcongr]
    rw [intervalIntegral.integral_add
        ((hwLLap.const_mul 2).add (hwLFd.const_mul (-(2*p.χ₀)))) (hwLRx.const_mul 2),
      intervalIntegral.integral_add (hwLLap.const_mul 2) (hwLFd.const_mul (-(2*p.χ₀))),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    ring
  have hdiss := uDiff_dissipation hsol₁ hsol₂ hτ₁ hτ₂
  have hchem := uDiff_chemotaxis_ibp hsol₁ hsol₂ hτ₁ hτ₂
  set D : ℝ := ∫ y in (0:ℝ)..1, (dwL y) ^ 2 with hD
  have hD_nn : 0 ≤ D := by
    rw [hD]; refine intervalIntegral.integral_nonneg (by norm_num) (fun y _ => by positivity)
  have hwLLap_eq : (∫ y in (0:ℝ)..1, wL y * Lap y) = - D := by
    rw [hD]; exact hdiss
  have hwLFd_eq : (∫ y in (0:ℝ)..1, wL y * Fd y)
      = - ∫ y in (0:ℝ)..1, dwL y * Flx y := hchem
  -- (5) the UNIFORM flux L² bound + reaction Lipschitz bound.
  set Cflux : ℝ := CfluxQuant p δ M with hCfluxdef
  have hCflux_nn : 0 ≤ Cflux := by rw [hCfluxdef]; exact CfluxQuant_nonneg p hMnn
  have hCflux := flux_diff_L2_le_Eu_uniform hsol₁ hsol₂ hδ hmem₁ hmem₂ hτ₁ hτ₂
  set Sflx : ℝ := ∫ y in (0:ℝ)..1, (Flx y) ^ 2 with hSflx
  have hSflx_eq : Sflx ≤ Cflux * Eu := by rw [hSflx, hEu, hFlx, hCfluxdef]; exact hCflux
  have hSflx_nn : 0 ≤ Sflx := by
    rw [hSflx]; refine intervalIntegral.integral_nonneg (by norm_num) (fun y _ => by positivity)
  have hFlxcont : ContinuousOn Flx (Set.uIcc (0:ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact ((flux_contDiffOn_Icc hsol₁ hτ₁).continuousOn).sub
      ((flux_contDiffOn_Icc hsol₂ hτ₂).continuousOn)
  have hdwLcont : ContinuousOn dwL (Set.uIcc (0:ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact (solution_deriv_lift_continuousOn_Icc hsol₁ hτ₁).sub
      (solution_deriv_lift_continuousOn_Icc hsol₂ hτ₂)
  have hdwLFxint : IntervalIntegrable (fun y => dwL y * Flx y) volume 0 1 :=
    (hdwLint.mul_continuousOn hFlxcont)
  have hdwLsqint : IntervalIntegrable (fun y => (dwL y) ^ 2) volume 0 1 := by
    have : ContinuousOn (fun y => (dwL y) ^ 2) (Set.uIcc (0:ℝ) 1) := hdwLcont.pow 2
    exact this.intervalIntegrable
  have hFlxsqint : IntervalIntegrable (fun y => (Flx y) ^ 2) volume 0 1 := by
    have : ContinuousOn (fun y => (Flx y) ^ 2) (Set.uIcc (0:ℝ) 1) := hFlxcont.pow 2
    exact this.intervalIntegrable
  have hYoung : 2 * p.χ₀ * (∫ y in (0:ℝ)..1, dwL y * Flx y) ≤ D + p.χ₀ ^ 2 * Sflx := by
    have hptw : ∀ y, 2 * p.χ₀ * (dwL y * Flx y) ≤ (dwL y) ^ 2 + p.χ₀ ^ 2 * (Flx y) ^ 2 := by
      intro y; nlinarith [sq_nonneg (dwL y - p.χ₀ * Flx y)]
    have hmono : (∫ y in (0:ℝ)..1, 2 * p.χ₀ * (dwL y * Flx y))
        ≤ ∫ y in (0:ℝ)..1, ((dwL y) ^ 2 + p.χ₀ ^ 2 * (Flx y) ^ 2) := by
      refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ (fun y _ => hptw y)
      · exact hdwLFxint.const_mul _
      · exact hdwLsqint.add (hFlxsqint.const_mul _)
    rw [intervalIntegral.integral_const_mul] at hmono
    rw [intervalIntegral.integral_add hdwLsqint (hFlxsqint.const_mul _),
      intervalIntegral.integral_const_mul] at hmono
    rw [hD, hSflx]; linarith
  -- reaction Lipschitz with the UNIFORM `M+1` bound (τ-independent; supplied as `hLip`).
  have hwL2int : IntervalIntegrable (fun y => wL y ^ 2) volume 0 1 := by
    have : ContinuousOn (fun y => wL y ^ 2) (Set.uIcc (0:ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact hwLcontI.pow 2
    exact this.intervalIntegrable
  have hwL2_eq_Eu : (∫ y in (0:ℝ)..1, wL y ^ 2) = Eu := by
    rw [hEu, ← lift_u_diff_sq_integral_eq_Eu u₁ u₂ τ]
  have hRxbound : ∀ y ∈ Set.Icc (0:ℝ) 1, |Rx y| ≤ L * |wL y| := by
    intro y hy
    have ha₁ : |intervalDomainLift (u₁ τ) y| ≤ M + 1 := by
      have hpos : 0 < intervalDomainLift (u₁ τ) y := solution_lift_pos hsol₁ hτ₁ y hy
      rw [abs_of_pos hpos]; have := (hmem₁ y hy).2; linarith
    have ha₂ : |intervalDomainLift (u₂ τ) y| ≤ M + 1 := by
      have hpos : 0 < intervalDomainLift (u₂ τ) y := solution_lift_pos hsol₂ hτ₂ y hy
      rw [abs_of_pos hpos]; have := (hmem₂ y hy).2; linarith
    have := hLip (intervalDomainLift (u₁ τ) y) (intervalDomainLift (u₂ τ) y) ha₁ ha₂
    rw [hRx, hwL]; exact this
  have hptwRx : ∀ y ∈ Set.Icc (0:ℝ) 1, wL y * Rx y ≤ L * wL y ^ 2 := by
    intro y hy
    have h1 : wL y * Rx y ≤ |wL y * Rx y| := le_abs_self _
    have h2 : |wL y * Rx y| ≤ L * wL y ^ 2 := by
      rw [abs_mul]
      calc |wL y| * |Rx y| ≤ |wL y| * (L * |wL y|) :=
            mul_le_mul_of_nonneg_left (hRxbound y hy) (abs_nonneg _)
        _ = L * (|wL y| * |wL y|) := by ring
        _ = L * wL y ^ 2 := by rw [abs_mul_abs_self]; ring
    exact le_trans h1 h2
  have hLwL2int : IntervalIntegrable (fun y => L * wL y ^ 2) volume 0 1 := hwL2int.const_mul L
  have hwLRx_le : (∫ y in (0:ℝ)..1, wL y * Rx y) ≤ L * Eu := by
    have hmono := intervalIntegral.integral_mono_on (by norm_num) hwLRx hLwL2int hptwRx
    rw [intervalIntegral.integral_const_mul, hwL2_eq_Eu] at hmono
    exact hmono
  rw [show p.χ₀ ^ 2 * CfluxQuant p δ M + 2 * L = p.χ₀ ^ 2 * Cflux + 2 * L from by rw [hCfluxdef]]
  rw [hIeq, hsplit, hwLLap_eq, hwLFd_eq]
  have hkey : 2 * (-D) - 2 * p.χ₀ * (- ∫ y in (0:ℝ)..1, dwL y * Flx y)
      + 2 * (∫ y in (0:ℝ)..1, wL y * Rx y)
      ≤ (p.χ₀ ^ 2 * Cflux + 2 * L) * Eu := by
    have h1 : 2 * p.χ₀ * (∫ y in (0:ℝ)..1, dwL y * Flx y) ≤ D + p.χ₀ ^ 2 * Sflx := hYoung
    have h2 : (∫ y in (0:ℝ)..1, wL y * Rx y) ≤ L * Eu := hwLRx_le
    have h3 : p.χ₀ ^ 2 * Sflx ≤ p.χ₀ ^ 2 * (Cflux * Eu) :=
      mul_le_mul_of_nonneg_left hSflx_eq (by positivity)
    nlinarith [hD_nn, h1, h2, h3]
  exact hkey

/-! ## Clean reduction of the gluing Grönwall field to a uniform two-sided lift bound

The remaining gluing input `gronwall` of `IntervalDomainL2UBoundednessHypothesis`
requires a SINGLE τ-independent Grönwall constant.  We package the natural
"solutions uniformly bounded" datum as `IntervalDomainUniformLiftBound p`: a uniform
two-sided lift bound `[δ,M]` (δ>0) on the overlap interior, for every solution pair
sharing an initial trace.  From it the explicit τ-independent `K` is read off.

The δ>0 lower bound is genuinely needed for the source `x↦x^γ` local Lipschitz
constant when `γ<1`; for `γ≥1` any `δ>0` works (and a lower bound always exists by
strict positivity `u_pos'` of a paper solution on the compact `[0,1]`, but a UNIFORM
one across `τ` is itself the bounded-solution content — exactly what `Lemma 3.1`
supplies under the Theorem-1.1 regime). -/

/-- **The clean uniform two-sided lift-bound datum.**  For every solution pair
sharing an initial trace, the lifts stay in a fixed `[δ,M]` (δ>0) on `[0,1]` over the
whole overlap interior `(0, min T₁ T₂)`.  This is the faithful "uniformly bounded
solution" hypothesis (the upper bound is the `IsPaper2BoundedBefore`-style sup bound;
the positive lower bound encodes the away-from-zero control needed for `γ<1`). -/
structure IntervalDomainUniformLiftBound (p : CM2Params) : Prop where
  bound :
    ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
      {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
      IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
      InitialTrace intervalDomain u₀ u₁ →
      InitialTrace intervalDomain u₀ u₂ →
        ∃ δ M : ℝ, 0 < δ ∧ ∀ τ, 0 < τ → τ < min T₁ T₂ →
          (∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u₁ τ) x ∈ Set.Icc δ M) ∧
          (∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u₂ τ) x ∈ Set.Icc δ M)

/-- **The uniform Grönwall constant, derived from the uniform two-sided lift bound.**
For a solution pair with the uniform `[δ,M]` bound on `(0,min T₁ T₂)`, there is a
SINGLE τ-independent `K ≥ 0` with `∫ Eprime(τ) ≤ K·E_u(τ)` for every interior `τ`.
The `K` is the explicit closed form `χ₀²·Cflux(δ,M) + 2·L_react(M+1)`; we obtain its
two τ-independent pieces ONCE (the flux constant via `flux_diff_L2_le_Eu_uniform`
evaluated at a fixed interior time, and the reaction Lipschitz via
`intervalLogisticSource_lipschitz p (M+1)`), then verify the per-τ bound. -/
theorem gronwall_const_of_uniformLiftBound
    {p : CM2Params} {T₁ T₂ : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂)
    {δ M : ℝ} (hδ : 0 < δ)
    (hbnd : ∀ τ, 0 < τ → τ < min T₁ T₂ →
      (∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u₁ τ) x ∈ Set.Icc δ M) ∧
      (∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u₂ τ) x ∈ Set.Icc δ M)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ τ, 0 < τ → τ < min T₁ T₂ →
      (∫ y in (0:ℝ)..1, intervalDomainUEnergyIntegrandDeriv u₁ u₂ τ y)
        ≤ K * intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ := by
  classical
  -- `M ≥ 0` (the interval is nonempty: there is at least one interior τ? not needed —
  -- get `M ≥ δ > 0` if any interior time exists; otherwise the universal statement is
  -- vacuous and `K = 0` works).  We branch on whether the overlap interior is empty.
  by_cases hne : ∃ τ : ℝ, 0 < τ ∧ τ < min T₁ T₂
  · obtain ⟨τ₀, hτ₀0, hτ₀1⟩ := hne
    have hbnd₀ := hbnd τ₀ hτ₀0 hτ₀1
    have hMnn : 0 ≤ M := by
      have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := by constructor <;> norm_num
      exact le_trans hδ.le (le_trans (hbnd₀.1 0 h0).1 (hbnd₀.1 0 h0).2)
    -- reaction Lipschitz constant `L` (τ-independent, from `M+1`), obtained ONCE.
    have hMm_pos : 0 < M + 1 := by linarith
    obtain ⟨L, hLpos, hLip⟩ :=
      ShenWork.IntervalDomainExistence.intervalLogisticSource_lipschitz p hMm_pos
    -- the explicit τ-independent Grönwall constant `K = χ₀²·Cflux(δ,M) + 2·L`.
    refine ⟨p.χ₀ ^ 2 * CfluxQuant p δ M + 2 * L, by
      have := CfluxQuant_nonneg (p := p) (δ := δ) hMnn; positivity, ?_⟩
    intro τ hτ0 hτ1
    have hτmem : τ ∈ Set.Ioo (0:ℝ) (min T₁ T₂) := ⟨hτ0, hτ1⟩
    obtain ⟨hb1, hb2⟩ := hbnd τ hτ0 hτ1
    exact intervalDomainL2U_energy_diffIneq_bound_uniform_explicit
      hsol₁ hsol₂ hδ hb1 hb2 hLip hτmem
  · -- empty overlap interior: the `∀ τ` is vacuous, `K = 0`.
    refine ⟨0, le_refl _, ?_⟩
    intro τ hτ0 hτ1
    exact absurd ⟨τ, hτ0, hτ1⟩ hne

/-- **The boundedness hypothesis, from the clean uniform-sup-bound datum.**
The ad-hoc `gronwall` field of `IntervalDomainL2UBoundednessHypothesis` is DERIVED
from the natural `IntervalDomainUniformLiftBound` (uniform two-sided lift bound); the
genuinely-independent `datumBdd` (bounded shared initial datum, NOT derivable from the
trace — see `IntervalDomainL2UBoundedDatumUniformOfBounded` header) is kept as an
explicit input `hdatum`. -/
def boundednessHypothesis_of_uniformSupBound
    {p : CM2Params}
    (hbnd : IntervalDomainUniformLiftBound p)
    (hdatum :
      ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
          BddAbove (Set.range (fun x : intervalDomainPoint => |u₀ x|))) :
    IntervalDomainL2UBoundednessHypothesis p where
  datumBdd := fun hsol₁ hsol₂ htr₁ htr₂ => hdatum hsol₁ hsol₂ htr₁ htr₂
  gronwall := by
    intro u₀ T₁ T₂ u₁ v₁ u₂ v₂ hsol₁ hsol₂ htr₁ htr₂
    obtain ⟨δ, M, hδ, hb⟩ := hbnd.bound hsol₁ hsol₂ htr₁ htr₂
    exact gronwall_const_of_uniformLiftBound hsol₁ hsol₂ hδ hb

/-- **Global-solution gluing from reachability, reduced to a CLEAN uniform-sup-bound
hypothesis.**  The remaining gluing obligation is the natural "solutions uniformly
bounded" datum `IntervalDomainUniformLiftBound p` (a uniform two-sided lift bound
`[δ,M]`, δ>0, on the overlap interior) plus the genuinely-independent bounded shared
initial datum `hdatum`.  The ad-hoc uniform-Grönwall-constant field of the prior
`IntervalDomainL2UBoundednessHypothesis` is now DERIVED, not assumed: it is read off
from the uniform bound via the quantitative resolver sup bounds (`Fv,Fg` of
`IntervalDomainResolverSupQuantitative`) and the uniform flux/reaction constants.

The δ>0 lower bound is needed only for the source `x↦x^γ` Lipschitz constant when
`γ<1`; `hdatum` (datum boundedness) genuinely cannot be folded in (it is not derivable
from `InitialTrace` alone, by the junk-`0` sup convention), so it remains explicit. -/
theorem GlobalSolutionGluingFromReachability_of_uniformSupBound
    (p : CM2Params)
    (hbnd : IntervalDomainUniformLiftBound p)
    (hdatum :
      ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
          BddAbove (Set.range (fun x : intervalDomainPoint => |u₀ x|))) :
    ShenWork.IntervalDomainExistence.GlobalSolutionGluingFromReachability p :=
  GlobalSolutionGluingFromReachability_of_bounded p
    (boundednessHypothesis_of_uniformSupBound hbnd hdatum)

/-! ## Discharging the UPPER bound `M` from the proven sup-norm bound (Lemma 3.1)

`Theorem_1_1_intervalDomain_conditional` / `boundedBefore_nonminimal_of_corrected_initial_approach`
prove, under the Theorem-1.1 negative-sensitivity regime (`χ₀ ≤ 0`, `0 < a`, `0 < b`)
and for a positive bounded shared initial datum, the sup-norm bound
`supNorm (u t) ≤ M` with the EXPLICIT τ-independent
`M = max (supNorm u₀, (a/b)^{1/α})` via `Lemma_3_1_intervalDomain`
(sup-norm monotonicity above carrying capacity) + the corrected initial-approach
ε-squeeze.  Since the lift `lift (u τ)` is continuous on the compact `[0,1]`, its
range of absolute values is `BddAbove`, so `|lift (u τ) x| ≤ supNorm (u τ) ≤ M`.
With strict positivity (`solution_lift_pos`) this gives the UPPER half (and `≥0`) of
the uniform two-sided lift bound `[δ,M]`.  The δ>0 lower bound remains the only
genuine residual (needed for the source `x↦x^γ` Lipschitz constant when `γ<1`). -/

/-- **Single-slice pointwise lift bound by the sup-norm.**  For a classical solution
`u` at an interior time `τ`, `|lift (u τ) y| ≤ supNorm (u τ)` for every `y ∈ [0,1]`:
the lift is continuous on the compact `[0,1]`, so its range of absolute values is
`BddAbove` and the `sSup` defining `supNorm` is a genuine upper bound. -/
theorem abs_lift_le_supNorm
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0:ℝ) T)
    {y : ℝ} (hy : y ∈ Set.Icc (0:ℝ) 1) :
    |intervalDomainLift (u τ) y| ≤ intervalDomainSupNorm (u τ) := by
  classical
  have hcont : ContinuousOn (intervalDomainLift (u τ)) (Set.Icc (0:ℝ) 1) :=
    solution_lift_continuousOn_Icc hsol hτ
  have hbdd : BddAbove
      (Set.range (fun x : intervalDomainPoint => |u τ x|)) := by
    have hcompact : IsCompact (Set.Icc (0:ℝ) 1) := isCompact_Icc
    obtain ⟨B, hB⟩ := (hcompact.image_of_continuousOn (hcont.abs)).bddAbove
    refine ⟨B, ?_⟩
    rintro _ ⟨x, rfl⟩
    have hBx := hB ⟨x.1, x.2, rfl⟩
    have hlift : intervalDomainLift (u τ) x.1 = u τ x := by
      simp [intervalDomainLift, x.2]
    simpa only [hlift] using hBx
  have hle : |u τ ⟨y, hy⟩| ≤ intervalDomainSupNorm (u τ) :=
    le_csSup hbdd ⟨⟨y, hy⟩, rfl⟩
  have hlift : intervalDomainLift (u τ) y = u τ ⟨y, hy⟩ := by
    simp [intervalDomainLift, hy]
  rw [hlift]; exact hle

/-- **The uniform UPPER lift bound `M = max(supNorm u₀, (a/b)^{1/α})`, regime-conditional.**
Under the Theorem-1.1 negative-sensitivity regime (`χ₀ ≤ 0`, `0 < a`, `0 < b`), for a
positive bounded shared initial datum `u₀` and a classical solution `u` with initial
trace `u₀`, every interior-time lift value is sandwiched `0 < lift (u τ) x ≤ M` on
`[0,1]`, with the EXPLICIT τ-independent `M = max (supNorm u₀, (a/b)^{1/α})`.  The
upper bound is the `IsPaper2BoundedBefore` sup bound transported pointwise via
`abs_lift_le_supNorm`; the strict lower `0 <` is `solution_lift_pos`. -/
theorem uniform_lift_upper_bound_of_regime
    (p : CM2Params)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hbddu₀ : BddAbove (Set.range (fun x : intervalDomainPoint => |u₀ x|)))
    {T : ℝ} (hT : 0 < T)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (htrace : InitialTrace intervalDomain u₀ u) :
    ∀ τ, 0 < τ → τ < T →
      ∀ x ∈ Set.Icc (0:ℝ) 1,
        0 < intervalDomainLift (u τ) x ∧
        intervalDomainLift (u τ) x
          ≤ max (intervalDomainSupNorm u₀) ((p.a / p.b) ^ (1 / p.α)) := by
  classical
  -- the corrected initial sup-norm approach, proved unconditionally for the
  -- bounded shared datum `u₀` (the `BddAbove` makes the trace bound non-vacuous).
  have happroach : ∀ ε > 0, ∃ δ > 0, δ ≤ T ∧ ∀ s, 0 < s → s < δ →
      intervalDomain.supNorm (u s) ≤ intervalDomain.supNorm u₀ + ε := fun ε hε =>
    ShenWork.IntervalDomainExistence.initialSupNormApproach_intervalDomain
      p u₀ hu₀ hbddu₀ hT hsol htrace hε
  -- the proven finite-horizon sup-norm bound `supNorm (u t) ≤ max(supNorm u₀, cap)`.
  have hM :=
    ShenWork.Paper2.IntervalDomainGlobalWellposed.nonminimal_supNorm_bound_of_corrected_initial_approach
      p hχ ha hb hT hsol happroach
  intro τ hτ0 hτT x hx
  have hτmem : τ ∈ Set.Ioo (0:ℝ) T := ⟨hτ0, hτT⟩
  refine ⟨solution_lift_pos hsol hτmem x hx, ?_⟩
  have hpos : 0 < intervalDomainLift (u τ) x := solution_lift_pos hsol hτmem x hx
  have habs : |intervalDomainLift (u τ) x| ≤ intervalDomainSupNorm (u τ) :=
    abs_lift_le_supNorm hsol hτmem hx
  rw [abs_of_pos hpos] at habs
  exact le_trans habs (hM τ hτ0 hτT)

/-- **The uniform two-sided lift bound from the regime + an explicit δ>0 lower bound.**
Under the Theorem-1.1 negative-sensitivity regime (`χ₀ ≤ 0`, `0 < a`, `0 < b`), with a
positive bounded shared initial datum for each solution pair (supplied by `hpos`,
`hdatum`) and an explicit positive uniform lower bound `δ>0` (supplied by `hlower` —
genuinely needed only for the `γ<1` source Lipschitz constant), the clean datum
`IntervalDomainUniformLiftBound p` holds: the common upper bound is
`M = max (supNorm u₀, (a/b)^{1/α})`, derived from the proven sup-norm bound. -/
theorem uniformLiftBound_of_regimeAndLowerBound
    (p : CM2Params)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hpos :
      ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
          PositiveInitialDatum intervalDomain u₀)
    (hdatum :
      ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
          BddAbove (Set.range (fun x : intervalDomainPoint => |u₀ x|)))
    (hlower :
      ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
          ∃ δ : ℝ, 0 < δ ∧ ∀ τ, 0 < τ → τ < min T₁ T₂ →
            (∀ x ∈ Set.Icc (0:ℝ) 1, δ ≤ intervalDomainLift (u₁ τ) x) ∧
            (∀ x ∈ Set.Icc (0:ℝ) 1, δ ≤ intervalDomainLift (u₂ τ) x)) :
    IntervalDomainUniformLiftBound p where
  bound := by
    intro u₀ T₁ T₂ u₁ v₁ u₂ v₂ hsol₁ hsol₂ htr₁ htr₂
    obtain ⟨δ, hδ, hδlo⟩ := hlower hsol₁ hsol₂ htr₁ htr₂
    have hu₀ : PositiveInitialDatum intervalDomain u₀ := hpos hsol₁ hsol₂ htr₁ htr₂
    have hbddu₀ : BddAbove (Set.range (fun x : intervalDomainPoint => |u₀ x|)) :=
      hdatum hsol₁ hsol₂ htr₁ htr₂
    set M : ℝ := max (intervalDomainSupNorm u₀) ((p.a / p.b) ^ (1 / p.α)) with hMdef
    have hub₁ := uniform_lift_upper_bound_of_regime p hχ ha hb hu₀ hbddu₀
      hsol₁.T_pos hsol₁ htr₁
    have hub₂ := uniform_lift_upper_bound_of_regime p hχ ha hb hu₀ hbddu₀
      hsol₂.T_pos hsol₂ htr₂
    refine ⟨δ, M, hδ, ?_⟩
    intro τ hτ0 hτmin
    have hτ1 : τ < T₁ := lt_of_lt_of_le hτmin (min_le_left _ _)
    have hτ2 : τ < T₂ := lt_of_lt_of_le hτmin (min_le_right _ _)
    obtain ⟨hlo1, hlo2⟩ := hδlo τ hτ0 hτmin
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · exact ⟨hlo1 x hx, (hub₁ τ hτ0 hτ1 x hx).2⟩
    · exact ⟨hlo2 x hx, (hub₂ τ hτ0 hτ2 x hx).2⟩

/-- **Global-solution gluing from reachability, reduced to the regime + δ>0 lower bound.**
The full gluing theorem holds under the Theorem-1.1 negative-sensitivity regime
(`χ₀ ≤ 0`, `0 < a`, `0 < b`), given for each solution pair sharing an initial trace:
* `hpos` — the shared datum is a positive initial datum;
* `hdatum` — the shared datum is bounded (the genuinely-independent input);
* `hlower` — an explicit positive uniform lower bound `δ>0` on the lifts over the
  overlap interior (needed only for the `γ<1` source Lipschitz constant).

The UPPER bound `M = max (supNorm u₀, (a/b)^{1/α})` is NO LONGER an assumption: it is
DERIVED from the proven sup-norm bound (`Lemma 3.1` monotonicity + the corrected
initial approach), transported pointwise via `abs_lift_le_supNorm`.  The Grönwall
constant is read off the resulting uniform two-sided bound as in
`GlobalSolutionGluingFromReachability_of_uniformSupBound`. -/
theorem GlobalSolutionGluingFromReachability_of_regimeAndLowerBound
    (p : CM2Params)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hpos :
      ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
          PositiveInitialDatum intervalDomain u₀)
    (hdatum :
      ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
          BddAbove (Set.range (fun x : intervalDomainPoint => |u₀ x|)))
    (hlower :
      ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
          ∃ δ : ℝ, 0 < δ ∧ ∀ τ, 0 < τ → τ < min T₁ T₂ →
            (∀ x ∈ Set.Icc (0:ℝ) 1, δ ≤ intervalDomainLift (u₁ τ) x) ∧
            (∀ x ∈ Set.Icc (0:ℝ) 1, δ ≤ intervalDomainLift (u₂ τ) x)) :
    ShenWork.IntervalDomainExistence.GlobalSolutionGluingFromReachability p :=
  GlobalSolutionGluingFromReachability_of_uniformSupBound p
    (uniformLiftBound_of_regimeAndLowerBound p hχ ha hb hpos hdatum hlower)
    (fun hsol₁ hsol₂ htr₁ htr₂ => hdatum hsol₁ hsol₂ htr₁ htr₂)

end

end ShenWork.Paper2
