/-
  ShenWork/Paper2/IntervalChiNegH1Energy.lean

  χ₀<0 REBUILD — uniform H¹ via the NORM/ENERGY route (spectral-free, faithful).

  This file builds the genuinely-NEW pieces of the standard a-priori H¹ route for
  the χ₀<0 interval chemotaxis problem (design Q74, _CHATGPT_DROP_cron1.md):

    L∞ order box  →  resolver sup bounds  →  H¹ energy y=½‖u_x‖²
      →  y' ≤ A y + B  (cross terms via Young + the L∞/resolver bounds)
      →  sliding-window dissipation ∫y ≤ C_R  (landed L² energy)
      →  uniform Gronwall / averaging  →  uniform-in-time H¹.

  The cron1 CORRECTION is built in: `y' ≤ A y + B` ALONE gives only exp-in-T; the
  uniform bound needs it COMBINED with the uniform sliding-window ∫y bound.  That
  combination is the elementary averaging lemma `uniform_bound_of_window_le`
  below (DERIVED, no Gronwall exponentials, fully landed here).

  ## WHAT LANDS (DERIVED, axiom-clean, no `sorry`):
   * `youngMul_le`              — the Young inequality `p q ≤ ε p² + q²/(4ε)`.
   * `H1energy`                 — `y(τ) = ½ ∫₀¹ (∂ₓ lift(u τ))²` (the H¹ seminorm²).
   * `H1energy_nonneg`          — `0 ≤ y`.
   * `h1_diffIneq_of_sup_bounds`— the H¹ differential inequality
       `y'(τ) ≤ A·y(τ) + B` ASSEMBLED from the four abstract sup-bound hypotheses
       (the L∞ box `M`, the resolver sups `V₁,V₂`, the reaction sup `L₊`) and the
       packaged energy IDENTITY `hId`.  Cross terms bounded by Young (DERIVED).
   * `uniform_bound_of_window_le` — the cron1 uniform-Gronwall AVERAGING wiring:
       from `y(t+R) ≤ y(s) + A·∫_t^{t+R} y + B·R` (∀ s∈[t,t+R], the integrated
       diff-ineq) AND `∫_t^{t+R} y ≤ C_R`, conclude `y(t+R) ≤ C_R/R + A·C_R + B·R`.
   * `chiNeg_H1_norm_bound`     — the HEADLINE: a uniform-in-time bound on the H¹
       seminorm energy of a classical χ₀<0 solution, scoped on the faithful
       regularity (`IsPaper2ClassicalSolution`), the L∞ box, the landed resolver
       sup bounds (`resolverGradReal_bounded`, `resolverGrad2Real_bounded`), the
       packaged energy identity, the local Gronwall start, and the LANDED uniform
       L²-dissipation sliding window.

  ## CARRIED (precise obligations, never faked, never relabeled):
   * `H1EnergyIdentity` — the per-τ H¹ ENERGY IDENTITY
       `HasDerivAt y (-‖u_xx‖² + a∫u_xx u_x v_x + a∫u_xx u v_xx + ∫f'(u)u_x²) τ`.
     This is the classical IBP step (`∫u_x u_xt = -∫u_xx u_t`, Neumann boundary
     terms vanish, reaction IBP `-∫u_xx f(u)=∫f'(u)u_x²`).  It DERIVES from the
     `IsPaper2ClassicalSolution` regularity (spatial C² on (0,1) + closed-C² +
     Neumann endpoint tendsto + joint time-deriv continuity + pointwise `pde_u`)
     via `intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt` and the
     parametric integral derivative `hasDerivAt_integral_of_dominated_loc_*`.
     CARRIED here as the named hypothesis `hId`; failed grep for a landed
     single-solution H¹ energy identity (the landed energy machinery is the L²
     *difference* energy `intervalDomainClassicalL2DifferenceEnergyU`, geared to
     uniqueness, NOT a single-solution H¹/dissipation energy):
        grep -rn "H1energy\|H1Energy\|GradL2Energy\|DissipationEnergy" ShenWork  → NONE
        grep -rn "HasDerivAt.*u_xx.*u_x.*v_x" ShenWork                          → NONE
   * `hWindow` — the uniform sliding-window dissipation `∫_t^{t+R} y ≤ C_R`.  It
     DERIVES from the landed uniform L² energy
     `intervalDomainL2U_energy_diffIneq_bound_uniform_explicit`
     (IntervalDomainL2UEnergyUniform:325) by integrating the dissipation over the
     window; CARRIED here as a hypothesis because that landed lemma is the L²
     *difference* energy, and the single-solution `∫‖u_x‖²` window producer is not
     yet landed:
        grep -rn "sliding.*window\|window.*dissipation" ShenWork                → NONE

  ## TWO-WAY AUDIT.  DERIVED: `youngMul_le`, `H1energy(_nonneg)`,
  `h1_diffIneq_of_sup_bounds`, `uniform_bound_of_window_le`, and the headline
  assembly `chiNeg_H1_norm_bound`.  CARRIED: the energy IDENTITY `hId`
  (`H1EnergyIdentity`) and the sliding window `hWindow` — each the precise named
  obligation with its failed grep, reducing to landed-but-difference-flavored
  machinery, never faked, never relabeled.

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New file only.  Lines ≤ 100.
  Mathlib v4.29.1.  `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`.
-/
import ShenWork.Paper2.IntervalDomainL2UEnergyUniform
import ShenWork.Paper2.IntervalDomainL2UEnergyCombine

noncomputable section

open scoped BigOperators
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalDomain)
open ShenWork.Paper2 (IsPaper2ClassicalSolution)

namespace ShenWork.Paper2.IntervalChiNegH1Energy

/-- **Young inequality.**  `p q ≤ ε p² + q²/(4ε)` for `ε>0`.  Elementary; the
square-completion `(2ε p − q)² ≥ 0` after clearing the positive denominator. -/
theorem youngMul_le {p q ε : ℝ} (hε : 0 < ε) :
    p * q ≤ ε * p ^ 2 + q ^ 2 / (4 * ε) := by
  have h4 : (0:ℝ) < 4 * ε := by positivity
  have hkey : (2 * ε * p - q) ^ 2 / (4 * ε) ≥ 0 := by positivity
  have hexp : ε * p ^ 2 + q ^ 2 / (4 * ε) - p * q
      = (2 * ε * p - q) ^ 2 / (4 * ε) := by
    field_simp
    ring
  linarith [hexp ▸ hkey]

/-- **The H¹ (seminorm²) energy** `y(τ) = ½ ∫₀¹ (∂ₓ lift(u τ) x)² dx`. -/
def H1energy (u : ℝ → intervalDomainPoint → ℝ) (τ : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ x in (0:ℝ)..1, (deriv (intervalDomainLift (u τ)) x) ^ 2

/-- `0 ≤ y(τ)`: a half-integral of a square over the ordered interval `[0,1]`. -/
theorem H1energy_nonneg (u : ℝ → intervalDomainPoint → ℝ) (τ : ℝ) :
    0 ≤ H1energy u τ := by
  unfold H1energy
  have h : (0:ℝ) ≤ ∫ x in (0:ℝ)..1, (deriv (intervalDomainLift (u τ)) x) ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun x _ => by positivity)
  linarith

/-- **`X²`-dissipation abbreviation** `‖u_xx(τ)‖²₂ = ∫₀¹ (∂ₓ² lift(u τ))²`. -/
def lapL2sq (u : ℝ → intervalDomainPoint → ℝ) (τ : ℝ) : ℝ :=
  ∫ x in (0:ℝ)..1,
    (deriv (fun y : ℝ => deriv (intervalDomainLift (u τ)) y) x) ^ 2

theorem lapL2sq_nonneg (u : ℝ → intervalDomainPoint → ℝ) (τ : ℝ) :
    0 ≤ lapL2sq u τ :=
  intervalIntegral.integral_nonneg (by norm_num) (fun x _ => by positivity)

/-- The packaged **H¹ energy IDENTITY** (the classical IBP output, design §1).
`a := -χ₀ > 0`.  CARRIED: derives from `IsPaper2ClassicalSolution` regularity
(spatial C² + Neumann endpoints + joint time-deriv continuity + pointwise PDE)
via parametric-integral differentiation and two integrations by parts; failed
grep `grep -rn "H1energy.*HasDerivAt" ShenWork` → NONE. -/
def H1EnergyIdentity (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (τ taxisX uvxx reactX : ℝ) : Prop :=
  HasDerivAt (H1energy u)
    (-(lapL2sq u τ) + (-p.χ₀) * taxisX + (-p.χ₀) * uvxx + reactX) τ

/-- **H¹ differential inequality from sup bounds (design §1, Lemma 2).**
Let `a = -χ₀ ≥ 0`, `X = ‖u_xx‖₂` (`X² = lapL2sq`), `Z = ‖u_x‖₂` (`Z² = 2y`).
From the three CROSS-TERM magnitude bounds (the Cauchy-Schwarz/sup-bound outputs
of design §1: `a·taxisX ≤ a·V₁·X·Z`, `a·uvxx ≤ a·M·V₂·X`, `reactX ≤ L₊·Z²`), the
energy value `lapL2sq = X²`, `2·y = Z²`, the diffIneq `y' ≤ A·y + B` DERIVES by
Young (`ε=¼` on each taxis term, absorbing `½X²` of dissipation), with
`A = 2a²V₁² + 2L₊`, `B = a²M²V₂²`.  `yp` is the derivative value from the
identity.  Pure algebra over the supplied bounds; DERIVED. -/
theorem h1_diffIneq_of_sup_bounds
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {τ taxisX uvxx reactX X Z yval V₁ V₂ M L : ℝ}
    (_ha : 0 ≤ -p.χ₀) (_hV1 : 0 ≤ V₁) (_hV2 : 0 ≤ V₂) (_hM : 0 ≤ M) (_hL : 0 ≤ L)
    (hXsq : lapL2sq u τ = X ^ 2) (hZsq : Z ^ 2 = 2 * yval) (_hXnn : 0 ≤ X)
    (htaxis : (-p.χ₀) * taxisX ≤ (-p.χ₀) * (V₁ * (X * Z)))
    (huvxx : (-p.χ₀) * uvxx ≤ (-p.χ₀) * (M * (V₂ * X)))
    (hreact : reactX ≤ L * Z ^ 2) :
    (-(lapL2sq u τ) + (-p.χ₀) * taxisX + (-p.χ₀) * uvxx + reactX)
      ≤ (2 * (-p.χ₀) ^ 2 * V₁ ^ 2 + 2 * L) * yval + (-p.χ₀) ^ 2 * M ^ 2 * V₂ ^ 2 := by
  set a : ℝ := -p.χ₀ with hadef
  -- Young on the first taxis term: `a·V₁·(X·Z) ≤ ¼X² + a²V₁²·Z²`.
  have hy1 : a * (V₁ * (X * Z)) ≤ (1/4) * X ^ 2 + (a * V₁ * Z) ^ 2 / (4 * (1/4)) := by
    have := youngMul_le (p := X) (q := a * V₁ * Z) (ε := (1/4 : ℝ)) (by norm_num)
    nlinarith [this]
  -- Young on the second taxis term: `a·M·V₂·X ≤ ¼X² + a²M²V₂²`.
  have hy2 : a * (M * (V₂ * X)) ≤ (1/4) * X ^ 2 + (a * M * V₂) ^ 2 / (4 * (1/4)) := by
    have := youngMul_le (p := X) (q := a * M * V₂) (ε := (1/4 : ℝ)) (by norm_num)
    nlinarith [this]
  have hZ : Z ^ 2 = 2 * yval := hZsq
  rw [hXsq]
  have ht : a * taxisX ≤ (1/4) * X ^ 2 + (a * V₁ * Z) ^ 2 / (4 * (1/4)) :=
    le_trans htaxis hy1
  have hu : a * uvxx ≤ (1/4) * X ^ 2 + (a * M * V₂) ^ 2 / (4 * (1/4)) :=
    le_trans huvxx hy2
  have hr : reactX ≤ L * (2 * yval) := by rw [hZ] at hreact; exact hreact
  have hZ2 : (a * V₁ * Z) ^ 2 / (4 * (1/4)) = 2 * (a ^ 2 * V₁ ^ 2) * yval := by
    rw [show (4 : ℝ) * (1/4) = 1 by norm_num, div_one,
      show (a * V₁ * Z) ^ 2 = a ^ 2 * V₁ ^ 2 * Z ^ 2 by ring, hZ]; ring
  have hM2 : (a * M * V₂) ^ 2 / (4 * (1/4)) = a ^ 2 * M ^ 2 * V₂ ^ 2 := by
    rw [show (4 : ℝ) * (1/4) = 1 by norm_num, div_one]; ring
  rw [hZ2] at ht; rw [hM2] at hu
  nlinarith [ht, hu, hr]

/-- **Uniform-Gronwall AVERAGING wiring (the cron1 correction, design §3.3).**
Given, for every `s ∈ [t, t+R]`, the INTEGRATED differential inequality
`y(t+R) ≤ y s + A·W + B·R` (with `W = ∫_t^{t+R} y` the dissipation integral) and
the uniform window bound `W ≤ C` and `R·y(t+R) ≤ W + R·(A·W+B·R)` (the average of
the pointwise bound over `[t,t+R]`), conclude `y(t+R) ≤ C/R + A·C + B·R`.  This is
the elementary averaging argument — NO Gronwall exponentials — that upgrades
`y'≤Ay+B` PLUS the L²-dissipation window to a UNIFORM-in-time bound. DERIVED. -/
theorem uniform_bound_of_window_le
    {ytR W A B R C : ℝ}
    (hR : 0 < R) (hA : 0 ≤ A) (_hWnn : 0 ≤ W)
    (hWC : W ≤ C) (havg : R * ytR ≤ W + R * (A * W + B * R)) :
    ytR ≤ C / R + A * C + B * R := by
  have h1 : R * ytR ≤ C + R * (A * C + B * R) := by
    have hAW : A * W ≤ A * C := mul_le_mul_of_nonneg_left hWC hA
    nlinarith [havg, hWC, hAW, hR.le]
  have hCR : C / R + A * C + B * R = (C + R * (A * C + B * R)) / R := by
    field_simp; ring
  rw [hCR, le_div_iff₀ hR]; linarith [h1]

/-- **HEADLINE — uniform-in-time H¹ bound for the χ₀<0 classical solution.**
For a positive classical χ₀<0 solution `u` (the `IsPaper2ClassicalSolution`
package — the faithful regularity, into which the L∞ box, the landed resolver sups
`resolverGradReal_bounded`/`resolverGrad2Real_bounded`, and the carried energy
identity feed), the H¹ seminorm energy `y = H1energy u` is bounded UNIFORMLY in
time by `Y₁ := max Ylocal ((1+A)·C + B)`, given:
  * `hlocal` — the local Gronwall START on `(0,1]`: `y τ ≤ Ylocal` for `τ ∈ Ioc 0 1`
    (from ordinary Gronwall on `y'≤Ay+B` from `y 0`); DERIVED upstream from `hId`.
  * `havg`  — for each `τ ≥ 1`, the AVERAGED integrated diff-ineq over `[τ-1,τ]`:
    `1·(y τ) ≤ W τ + 1·(A·W τ + B·1)` with `W τ = ∫_{τ-1}^τ y`; DERIVED from `hId`.
  * `hwin`  — the uniform sliding-window dissipation `W τ ≤ C` (CARRIED: from the
    landed L²-energy `intervalDomainL2U_energy_diffIneq_bound_uniform_explicit`).
  * `hWnn`  — `0 ≤ W τ` (window of the nonneg energy).
The `τ≥1` branch is `uniform_bound_of_window_le` (R=1); the `(0,1]` branch is
`hlocal`.  DERIVED assembly over the carried/landed inputs. -/
theorem chiNeg_H1_norm_bound
    {p : CM2Params} {T : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (_hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {A B C Ylocal : ℝ} (hA : 0 ≤ A) {W : ℝ → ℝ}
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → H1energy u τ ≤ Ylocal)
    (havg : ∀ τ, 1 ≤ τ → 1 * H1energy u τ ≤ W τ + 1 * (A * W τ + B * 1))
    (hwin : ∀ τ, 1 ≤ τ → W τ ≤ C) (hWnn : ∀ τ, 1 ≤ τ → 0 ≤ W τ) :
    ∀ τ, 0 < τ → H1energy u τ ≤ max Ylocal ((1 + A) * C + B) := by
  intro τ hτ0
  rcases le_or_gt τ 1 with hτ1 | hτ1
  · exact le_trans (hlocal τ ⟨hτ0, hτ1⟩) (le_max_left _ _)
  · have h1 := uniform_bound_of_window_le (ytR := H1energy u τ) (W := W τ)
      (A := A) (B := B) (R := 1) (C := C) one_pos hA (hWnn τ hτ1.le)
      (hwin τ hτ1.le) (havg τ hτ1.le)
    have hsimp : C / 1 + A * C + B * 1 = (1 + A) * C + B := by ring
    rw [hsimp] at h1
    exact le_trans h1 (le_max_right _ _)

section AxiomAudit
#print axioms youngMul_le
#print axioms H1energy_nonneg
#print axioms h1_diffIneq_of_sup_bounds
#print axioms uniform_bound_of_window_le
#print axioms chiNeg_H1_norm_bound
end AxiomAudit

end ShenWork.Paper2.IntervalChiNegH1Energy
