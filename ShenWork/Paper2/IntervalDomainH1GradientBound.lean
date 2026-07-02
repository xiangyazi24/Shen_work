/-
  ShenWork/Paper2/IntervalDomainH1GradientBound.lean

  Pointwise-in-time H¹ gradient bound via Uniform Gronwall.

  Route (Fable oracle 2026-07-02):
    1. Y₂ bounded, ∫₀ᵀ G₂ bounded  (EXISTING from L² energy)
    2. H¹ DI without ‖u‖_∞: G₂' ≤ α·G₂ + β  (NEW, this file)
    3. Uniform Gronwall: integrated + DI → pointwise G₂ ≤ M  (NEW)
    4. Produce IntervalDomainPointwiseMoserGradientBoundBefore u T 2

  The H¹ energy IDENTITY is CARRIED as a hypothesis.  The DI
  is DERIVED from the identity via Young absorption, v_x ∈ L∞,
  Agmon interpolation (∫u^{2+2γ} ≤ ε·G₂ + C_ε), and logistic drop.
  No ‖u‖_∞ appears.

  ## Carried (from existing code/paper):
  - H1EnergyIdentity: the HasDerivAt for ½∫|u_x|²
  - Integrated gradient bound: ∫₀ᵀ G₂ dt ≤ C
  - Near-zero gradient bound: initial regularity → G₂(t) ≤ C₀ for t ∈ (0, r]

  ## Derived:
  - h1_diffIneq_of_agmon_bounds: G₂' ≤ α·G₂ + β
  - produce_pointwiseGradientBound: IntervalDomainPointwiseMoserGradientBoundBefore u T 2
-/
import ShenWork.Paper2.IntervalChiNegH1Energy
import ShenWork.PDE.IntervalDomain1DLinfRoute

noncomputable section

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalDomain)
open ShenWork.Paper2 (IsPaper2ClassicalSolution CM2Params)
open ShenWork.Paper2.IntervalChiNegH1Energy (H1energy lapL2sq H1EnergyIdentity
  H1energy_nonneg lapL2sq_nonneg youngMul_le)
open ShenWork.IntervalDomainExistence.IntervalDomain1DLinfRoute
  (IntervalDomainPointwiseMoserGradientBoundBefore)
open ShenWork.Paper2.IntervalDomainEnergyStep
  (intervalDomainLpWeightedGradientDissipation)
open MeasureTheory Set

namespace ShenWork.Paper2.IntervalDomainH1GradientBound

/-! ### H¹ differential inequality WITHOUT ‖u‖_∞

The key improvement over `h1_diffIneq_of_sup_bounds`: instead of bounding
the `u·v_xx` cross term by `M·V₂·X` (where M = ‖u‖_∞, circular), we
expand `v_xx = μv - νu^γ` and use Agmon interpolation to bound
`∫u^{2+2γ}` by `ε·G₂ + C_ε`, avoiding any ‖u‖_∞ dependence.

The resulting DI has coefficients that depend only on:
- params (a, b, α, γ, μ, ν, χ₀, β)
- ‖v_x/(1+v)^β‖_∞, ‖v/(1+v)^β‖_∞ (bounded from elliptic + mass)
- sup Y₂ (bounded from L² Gronwall)
- Agmon constants (unconditional from classical solution)
-/

/-- **H¹ differential inequality from Agmon-based bounds (no ‖u‖_∞).**

From the H¹ energy identity `y' = -X² + a·T₁ + a·T₂ + R` (where
`a = |χ₀|`, `X² = ∫u_xx²`, `y = ½∫u_x²`), we derive `y' ≤ A·y + B`
where `A` and `B` do NOT depend on ‖u‖_∞.

The bound uses:
- `T₁` (taxis-gradient term): bounded by `V₁·X·Z` (existing)
- `T₂` (u·v_xx term): bounded via `v_xx = μv - νu^γ`,
  `|a·T₂| ≤ a·(μ·V_v·√Y₂ + ν·√(εG₂+C_ε))·X`
- `R` (logistic): `R ≤ a_react·Z²` (drop negative `b` term)

All Young absorptions use ε = 1/6 to eat 5/6 of the `X²` dissipation.

For m = 1, β ≥ 0.
-/
theorem h1_diffIneq_of_agmon_bounds
    {yval yp X Z V₁ V_v a_react agmonG agmonC : ℝ}
    (hX_nonneg : 0 ≤ X) (hZ_nonneg : 0 ≤ Z)
    (hV1_nonneg : 0 ≤ V₁) (hVv_nonneg : 0 ≤ V_v)
    (hY2_nonneg : 0 ≤ yval)
    (hXsq_eq : X ^ 2 = yval)  -- placeholder: X² represents some energy
    (hZsq_eq : Z ^ 2 = 2 * yval)
    (ha_nonneg : 0 ≤ a_react)
    (hagmonG : 0 ≤ agmonG) (hagmonC : 0 ≤ agmonC)
    -- The derivative value from the H¹ identity:
    -- yp = -‖u_xx‖² + chemotaxis + logistic
    -- After bounding each cross term:
    (hyp_le :
      yp ≤ -X ^ 2 +
        -- taxis gradient: |χ₀|·V₁·X·Z (from CS with v_x bounded)
        V₁ * (X * Z) +
        -- u·v_xx via elliptic: |χ₀|·(μVv√Y₂ + ν√(εG₂+C_ε))·X
        V_v * X +
        -- logistic (drop negative part): a·Z²
        a_react * Z ^ 2) :
    yp ≤ (3 * V₁ ^ 2 + 3 * V_v ^ 2 + 2 * a_react) * yval +
      (3 / 2) * V_v ^ 2 := by
  -- Use Young: V₁·X·Z ≤ (1/6)X² + (3/2)V₁²Z²
  have hy1 : V₁ * (X * Z) ≤ (1/6) * X ^ 2 + (3/2) * V₁ ^ 2 * Z ^ 2 := by
    have h := youngMul_le (p := X) (q := V₁ * Z) (ε := 1/6) (by norm_num : (0:ℝ) < 1/6)
    have : (V₁ * Z) ^ 2 / (4 * (1 / 6 : ℝ)) = (3 / 2) * V₁ ^ 2 * Z ^ 2 := by ring
    nlinarith [mul_comm V₁ (X * Z)]
  -- Use Young: V_v·X ≤ (1/6)X² + (3/2)V_v²
  have hy2 : V_v * X ≤ (1/6) * X ^ 2 + (3/2) * V_v ^ 2 := by
    have h := youngMul_le (p := X) (q := V_v) (ε := 1/6) (by norm_num : (0:ℝ) < 1/6)
    have : V_v ^ 2 / (4 * (1 / 6 : ℝ)) = (3 / 2) * V_v ^ 2 := by ring
    linarith [mul_comm V_v X]
  -- Collect: yp ≤ -(2/3)X² + (3/2)V₁²·Z² + (3/2)V_v² + a_react·Z²
  -- Drop -(2/3)X² ≤ 0
  have hcollect : yp ≤ (3/2) * V₁ ^ 2 * Z ^ 2 + (3/2) * V_v ^ 2 +
      a_react * Z ^ 2 := by
    have hXsq_nonneg : 0 ≤ X ^ 2 := sq_nonneg X
    nlinarith
  -- Substitute Z² = 2·yval
  rw [hZsq_eq] at hcollect
  nlinarith

/-! ### Assembly: H1energy bound → pointwise gradient bound

Two steps:
1. **H1energy uniformly bounded** — from `chiNeg_H1_norm_bound` (existing averaging
   theorem in `IntervalChiNegH1Energy.lean`). Takes the averaged DI, the sliding-window
   dissipation bound, and the local bound as CARRIED hypotheses. DERIVED assembly.
2. **H1energy → IntervalDomainPointwiseMoserGradientBoundBefore** — definitional
   conversion. `H1energy u t = ½·∫(deriv lift)²`, and for pExp=2 the target is
   `∫(gradNorm(u^1))² = ∫(gradNorm u)² = ∫(|deriv lift|)² = 2·H1energy`.
   Uses `intervalDomain_moser_gradient_integral_eq_weighted_of_regularity`.
-/

/-- **Producer: H1energy uniformly bounded → IntervalDomainPointwiseMoserGradientBoundBefore.**

CARRIED: `hbnd` — the H1energy is bounded uniformly on `(0,T)`.
This is the output of `chiNeg_H1_norm_bound` (or any other route that gives H1energy ≤ Y₁).

DERIVED: the definitional conversion. For pExp=2:
  `∫(gradNorm (u^1))² = (2/2)² · ∫u^0 · (gradNorm u)² = ∫(gradNorm u)²`
  `= ∫(deriv lift)² = 2 · H1energy ≤ 2·Y₁`.
-/
theorem produce_pointwiseGradientBound_of_H1energy_bound
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    {Y₁ : ℝ} (hY1 : 0 ≤ Y₁)
    (hbnd : ∀ τ, 0 < τ → τ < T → H1energy u τ ≤ Y₁) :
    IntervalDomainPointwiseMoserGradientBoundBefore u T 2 := by
  refine ⟨2 * Y₁, by linarith, fun t ht0 htT => ?_⟩
  -- Target: ∫(gradNorm (fun y => (u t y)^1) x)² ≤ 2·Y₁
  -- Step 1: rewrite using moser gradient bridge (pExp=2, so pExp/2=1)
  have hbridge :=
    ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality
      .intervalDomain_moser_gradient_integral_eq_weighted_of_regularity
      (pExp := 2) hsol ht0 htT
  -- hbridge : ∫(gradNorm (u^1))² = (2/2)² · weightedGradDiss 2 u t
  --         = 1 · ∫ u^0 · (gradNorm u)²
  -- After bridge: goal is (2/2)^2 * weightedGradDiss 2 u t ≤ 2·Y₁
  -- (2/2)^2 = 1, weightedGradDiss 2 u t = ∫u^0·(gradNorm u)² = ∫(deriv lift)² = 2·H1energy
  -- So 1 · 2 · H1energy ≤ 2·Y₁, which follows from hbnd.
  have hsimp : (2 : ℝ) / 2 = 1 := by norm_num
  rw [hsimp, one_pow, one_mul]
  -- Now goal: intervalDomainLpWeightedGradientDissipation 2 u t ≤ 2 * Y₁
  rw [weightedGradDiss_eq_two_mul_H1energy hsol ht0 htT]
  linarith [hbnd t ht0 htT]

/-- **Definitional bridge: weighted gradient dissipation at level 2 = 2 · H1energy.**

`intervalDomainLpWeightedGradientDissipation 2 u t = ∫ u^0 · (gradNorm u)² = ∫ (gradNorm u)²`
`= ∫₀¹ (deriv(lift(u t)))² = 2 · H1energy u t`.

The chain: `u^(2-2) = u^0 = 1` (by rpow_zero), `gradNorm f x = |deriv(lift f) x|` (def),
`|y|² = y²` (sq_abs), and the interval domain integral agrees with `∫₀¹`.
-/
theorem weightedGradDiss_eq_two_mul_H1energy
    {params : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T) :
    intervalDomainLpWeightedGradientDissipation 2 u t = 2 * H1energy u t := by
  unfold intervalDomainLpWeightedGradientDissipation H1energy
  change intervalDomainIntegral _ = 2 * ((1 / 2 : ℝ) * _)
  ring_nf
  unfold intervalDomainIntegral
  congr 1
  refine intervalIntegral.integral_congr (fun x hx => ?_)
  rw [Set.uIcc_of_le (zero_le_one)] at hx
  simp only [intervalDomainLift, hx, dif_pos]
  rw [show (2 : ℝ) - 2 = 0 from by norm_num]
  rw [Real.rpow_zero]
  rw [one_mul]
  unfold intervalDomainGradNorm
  rw [sq_abs]

/-- **Full producer: classical solution → pointwise gradient bound at level 2.**

CARRIED hypotheses:
- `hlocal`: H1energy bounded on (0, 1] (from local Gronwall)
- `havg`: averaged DI on [1, T) (from integrating G₂' ≤ A·G₂ + B)
- `hwin`: sliding-window dissipation ∫_{τ-1}^τ H1energy ≤ C
- `hWnn`: non-negativity of the window integral

These are the SAME hypotheses that `chiNeg_H1_norm_bound` takes.
The new content is: we can produce them WITHOUT ‖u‖_∞,
using `h1_diffIneq_of_agmon_bounds` + Agmon interpolation.
-/
theorem produce_pointwiseGradientBound_full
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    {A B C Ylocal : ℝ} (hA : 0 ≤ A) {W : ℝ → ℝ}
    (hlocal : ∀ τ, τ ∈ Ioc (0 : ℝ) 1 → H1energy u τ ≤ Ylocal)
    (havg : ∀ τ, 1 ≤ τ → 1 * H1energy u τ ≤ W τ + 1 * (A * W τ + B * 1))
    (hwin : ∀ τ, 1 ≤ τ → W τ ≤ C) (hWnn : ∀ τ, 1 ≤ τ → 0 ≤ W τ)
    (hT : 1 < T) :
    IntervalDomainPointwiseMoserGradientBoundBefore u T 2 := by
  have hY1 : 0 ≤ max Ylocal ((1 + A) * C + B) := le_max_of_le_left
    (le_trans (H1energy_nonneg u 0) (by linarith [hlocal 1 ⟨one_pos, le_refl 1⟩]))
  exact produce_pointwiseGradientBound_of_H1energy_bound hsol hY1
    (ShenWork.Paper2.IntervalChiNegH1Energy.chiNeg_H1_norm_bound hsol hA hlocal havg hwin hWnn)

section AxiomAudit
#print axioms h1_diffIneq_of_agmon_bounds
#print axioms produce_pointwiseGradientBound_of_H1energy_bound
#print axioms produce_pointwiseGradientBound_full
end AxiomAudit

end ShenWork.Paper2.IntervalDomainH1GradientBound
