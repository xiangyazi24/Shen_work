/-
  WHOLE-LINE cross-frozen super-barrier, POSITIVE SENSITIVITY (`χ ≥ 0`).

  This is the `0 ≤ χ < min(½, chiStar)` analog of `whole_line_super_barrier`
  (`WaveSuperBarrier.lean`).  It establishes that for the SAME classical upper
  barrier `upperBarrier κ M = min M (e^{-κ x})` — now with `M = MChi p ≥ 1`
  instead of `M = 1` — the frozen wave operator is `≤ 0` on the WHOLE line,
  including the corner at the free interface `exp (-κ x) = M`.

  AWAY FROM THE INTERFACE everything is already committed in `Statements.lean`:
    * exponential region (`exp (-κ x) < M`):
      `frozenWaveOperator_upperBarrier_exp_region_nonpos_of_chi_nonneg`;
    * constant region (`M < exp (-κ x)`):
      `frozenWaveOperator_upperBarrier_const_region_nonpos_pos`.
  These are bundled as
  `Lemma_4_1_pos_frozen_holds_away_from_interface_at_kappa` (Statements:8038).

  THE INTERFACE KINK (this file).  At `x = x*` with `exp (-κ x*) = M`, the
  barrier and its first derivative are non-differentiable, so the classical
  `frozenWaveOperator` evaluates diffusion and convection at the Mathlib junk
  value `0`.  The residual collapses to

    `frozenWaveOperator p c u (upperBarrier κ M) x*`
      `= -χ · (deriv F x*) + M (1 - M^α)`,  `F y := (Ū y)^m · V_u'(y)`.

  Unlike the `χ ≤ 0` branch, the `χ ≥ 0` kink needs NO plateau source bound.
  We mirror the committed `χ ≥ 0` CONSTANT-region argument
  (`frozenWaveOperator_upperBarrier_const_region_nonpos_pos`):

  * differentiable subcase: `deriv F x* = M^m (V_u(x*) - u(x*)^γ)`, so
    `-χ M^m (V_u - u^γ) ≤ -χ M^m V_u + χ M^m u^γ ≤ χ M^{m+γ}` (drop `-χ M^m V_u ≤ 0`
    since `χ ≥ 0`, `V_u ≥ 0`, then `u^γ ≤ M^γ` by the trap), and with `m+γ = α+1`
    the residual is `M(1 - (1-χ) M^α) ≤ 0` by the budget `1 ≤ (1-χ) M^α`;
  * non-differentiable subcase: `deriv F x* = 0` (junk), residual `M(1-M^α) ≤ 0`.

  Main result: `whole_line_super_barrier_pos`.
-/
import ShenWork.Paper1.Statements
import ShenWork.Paper1.WaveSuperBarrier

open Filter Topology

namespace ShenWork.Paper1

variable {p : CMParams} {c κ M : ℝ} {u : ℝ → ℝ}

/-- **Chemotactic-flux interface bound, positive sensitivity.**  At the free
interface `exp (-κ x) = M`, the chemotactic term `-χ · (deriv F)` is bounded by
the constant-region budget surplus `χ · M^{m+γ}`, using only the trap bound
`u^γ ≤ M^γ` (no plateau source bound).

Two subcases:
* differentiable: `deriv F x* = M^m (V_u(x*) - u(x*)^γ)`, handled algebraically;
* not differentiable: the classical `deriv` is the junk value `0`, so the
  left-hand side is `0 ≤ χ M^{m+γ}`. -/
theorem chemFlux_deriv_neg_chi_le_at_interface_pos
    (hχ_nonneg : 0 ≤ p.χ) (hκ : 0 < κ) (hM : 1 ≤ M)
    (hu : InWaveTrapSet κ M u)
    {x : ℝ} (hx : Real.exp (-κ * x) = M) :
    -p.χ * deriv (fun y => (upperBarrier κ M y) ^ p.m *
        deriv (frozenElliptic p u) y) x ≤ p.χ * M ^ (p.m + p.γ) := by
  set F := fun y => (upperBarrier κ M y) ^ p.m * deriv (frozenElliptic p u) y
    with hF
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  have hMm_nonneg : 0 ≤ M ^ p.m := Real.rpow_nonneg hMpos.le _
  have hMmγ_nonneg : 0 ≤ M ^ (p.m + p.γ) := Real.rpow_nonneg hMpos.le _
  have hbudget_nonneg : 0 ≤ p.χ * M ^ (p.m + p.γ) := mul_nonneg hχ_nonneg hMmγ_nonneg
  by_cases hdiff : DifferentiableAt ℝ F x
  · -- differentiable: compute via the LEFT region, where F = M^m · V'
    have hMm_eq : deriv F x = M ^ p.m * (frozenElliptic p u x - (u x) ^ p.γ) := by
      have hderivWithin : derivWithin F (Set.Iio x) x = deriv F x :=
        hdiff.derivWithin (uniqueDiffWithinAt_Iio x)
      have hFx : F x = (fun y => M ^ p.m * deriv (frozenElliptic p u) y) x := by
        have hbx : upperBarrier κ M x = M := upperBarrier_eq_M_at_interface hx
        simp only [hF, hbx]
      have hEq :
          derivWithin F (Set.Iio x) x =
            derivWithin (fun y => M ^ p.m * deriv (frozenElliptic p u) y)
              (Set.Iio x) x :=
        Filter.EventuallyEq.derivWithin_eq (chemFlux_eventuallyEq_left hκ hx p u) hFx
      have hVdiff : DifferentiableAt ℝ (deriv (frozenElliptic p u)) x :=
        frozenElliptic_deriv_differentiableAt p hu.cunif_bdd hu.nonneg x
      have hMulDiff :
          DifferentiableAt ℝ
            (fun y => M ^ p.m * deriv (frozenElliptic p u) y) x :=
        hVdiff.const_mul _
      have hderivFull :
          deriv (fun y => M ^ p.m * deriv (frozenElliptic p u) y) x =
            M ^ p.m * deriv (deriv (frozenElliptic p u)) x := by
        rw [deriv_const_mul_field]
      have hderivWithinFull :
          derivWithin (fun y => M ^ p.m * deriv (frozenElliptic p u) y)
              (Set.Iio x) x =
            deriv (fun y => M ^ p.m * deriv (frozenElliptic p u) y) x :=
        hMulDiff.derivWithin (uniqueDiffWithinAt_Iio x)
      have hVV : deriv (deriv (frozenElliptic p u)) x =
          frozenElliptic p u x - (u x) ^ p.γ :=
        frozenElliptic_deriv_deriv_eq p hu.cunif_bdd hu.nonneg x
      rw [← hderivWithin, hEq, hderivWithinFull, hderivFull, hVV]
    rw [hMm_eq]
    -- now mirror the constant-region χ≥0 chemotaxis bound
    have hV_nonneg : 0 ≤ frozenElliptic p u x :=
      frozenElliptic_nonneg p hu.nonneg x
    have huγ_le_Mγ : (u x) ^ p.γ ≤ M ^ p.γ :=
      hu.rpow_le_M (by linarith [p.hγ]) x
    have hleft_nonpos :
        -p.χ * (M ^ p.m * frozenElliptic p u x) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr hχ_nonneg) (mul_nonneg hMm_nonneg hV_nonneg)
    have hsource :
        p.χ * (M ^ p.m * (u x) ^ p.γ) ≤ p.χ * (M ^ p.m * M ^ p.γ) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left huγ_le_Mγ hMm_nonneg) hχ_nonneg
    have hpow : M ^ p.m * M ^ p.γ = M ^ (p.m + p.γ) := by
      rw [← Real.rpow_add hMpos]
    nlinarith [hleft_nonpos, hsource, hpow]
  · -- not differentiable: junk value 0 ≤ χ M^{m+γ}
    rw [deriv_zero_of_not_differentiableAt hdiff]
    simpa using hbudget_nonneg

/-- **Kink super-barrier, positive sensitivity.**  At the free interface
`exp (-κ x) = M`, the classical `frozenWaveOperator` of the upper barrier is
`≤ 0` for `0 ≤ χ`, `M ≥ 1`, `α = m+γ-1`, and the budget `M ≥ (1/(1-χ))^{1/α}`
(equivalently `1 ≤ (1-χ) M^α`).  No plateau source bound is required. -/
theorem frozenWaveOperator_upperBarrier_interface_nonpos_pos
    (hχ_nonneg : 0 ≤ p.χ) (hχ_lt_one : p.χ < 1) (hκ : 0 < κ) (hM : 1 ≤ M)
    (hα : p.α = p.m + p.γ - 1)
    (hMchi : (1 / (1 - p.χ)) ^ (1 / p.α) ≤ M)
    (hu : InWaveTrapSet κ M u)
    {x : ℝ} (hx : Real.exp (-κ * x) = M) :
    frozenWaveOperator p c u (upperBarrier κ M) x ≤ 0 := by
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  have hMnonneg : (0 : ℝ) ≤ M := hMpos.le
  unfold frozenWaveOperator
  rw [upperBarrier_iteratedDeriv_two_eq_zero_at_interface hκ hMpos hx,
    upperBarrier_deriv_eq_zero_at_interface hκ hMpos hx,
    upperBarrier_eq_M_at_interface hx]
  -- residual = -χ · (deriv F x) + M (1 - M^α)
  have hchem :
      -p.χ * deriv (fun y => (upperBarrier κ M y) ^ p.m *
        deriv (frozenElliptic p u) y) x ≤ p.χ * M ^ (p.m + p.γ) :=
    chemFlux_deriv_neg_chi_le_at_interface_pos hχ_nonneg hκ hM hu hx
  -- budget: 1 ≤ (1 - χ) M^α
  have hbudget : 1 ≤ (1 - p.χ) * M ^ p.α :=
    one_le_one_sub_chi_mul_M_rpow_alpha p hχ_lt_one hMnonneg hMchi
  -- M^{m+γ} = M · M^α  (since m+γ = α+1)
  have hpow_succ : M ^ (p.m + p.γ) = M * M ^ p.α := by
    rw [hα]
    calc
      M ^ (p.m + p.γ) = M ^ (1 + (p.m + p.γ - 1)) := by
        congr 1; ring
      _ = M ^ (1 : ℝ) * M ^ (p.m + p.γ - 1) := by
        rw [Real.rpow_add hMpos]
      _ = M * M ^ (p.m + p.γ - 1) := by rw [Real.rpow_one]
  -- M(1 - M^α) + χ M^{m+γ} = M(1 - (1-χ) M^α) ≤ 0
  have hlog_chem :
      M * (1 - M ^ p.α) + p.χ * M ^ (p.m + p.γ) ≤ 0 := by
    rw [hpow_succ]; nlinarith [hbudget, hMnonneg]
  nlinarith [hchem, hlog_chem]

/-- **Whole-line cross-frozen super-barrier, positive sensitivity**
(`0 ≤ χ < min(½, chiStar)`).

For every trapped profile `u : InWaveTrapSet κ M u`, the classical
`frozenWaveOperator` of the upper barrier `upperBarrier κ M = min M (e^{-κ x})`
is `≤ 0` on the WHOLE line — including the corner at the free interface
`exp (-κ x) = M`.

The exponential and constant regions are the committed `χ ≥ 0` regional
super-barriers (`frozenWaveOperator_upperBarrier_exp_region_nonpos_of_chi_nonneg`
and `frozenWaveOperator_upperBarrier_const_region_nonpos_pos`); the interface
kink is `frozenWaveOperator_upperBarrier_interface_nonpos_pos`, where diffusion
and convection vanish at the Mathlib junk value `0` and the chemotactic flux is
absorbed by the constant-region budget `1 ≤ (1-χ) M^α`.  In contrast to the
`χ ≤ 0` branch, NO plateau source bound is needed: the trap bound `u^γ ≤ M^γ`
already closes the kink. -/
theorem whole_line_super_barrier_pos
    (hχ_nonneg : 0 ≤ p.χ) (hχ : p.χ < chiStar p)
    (hα : p.α = p.m + p.γ - 1)
    (hκ : 0 < κ) (hκ1 : κ < 1) (hmκ : p.m * κ ≤ 1)
    (hM : 1 ≤ M)
    (hMchi : (1 / (1 - p.χ)) ^ (1 / p.α) ≤ M)
    (hc : c = κ + κ⁻¹) :
    InWaveTrapSet κ M u →
    ∀ x, frozenWaveOperator p c u (upperBarrier κ M) x ≤ 0 := by
  intro hu x
  have hχ_lt_one : p.χ < 1 := lt_of_lt_of_le hχ (chiStar_le_one p)
  rcases lt_trichotomy (Real.exp (-κ * x)) M with hlt | heq | hgt
  · -- exponential region: exp (-κ x) < M
    have hx : expDecay κ x < M := by simpa [expDecay] using hlt
    have hc_two : 2 ≤ c :=
      (two_lt_of_pos_lt_one_kappa_speed hκ hκ1 hc).le
    have hκ_eq : κ = kappa c :=
      (kappa_eq_of_pos_lt_one_kappa_speed hκ hκ1 hc).symm
    exact frozenWaveOperator_upperBarrier_exp_region_nonpos_of_chi_nonneg
      p hc_two hκ_eq hχ_nonneg hχ hα hκ.le hmκ hx hu
      (frozenElliptic_deriv_differentiableAt p hu.cunif_bdd hu.nonneg x)
  · -- interface kink: exp (-κ x) = M
    exact frozenWaveOperator_upperBarrier_interface_nonpos_pos
      hχ_nonneg hχ_lt_one hκ hM hα hMchi hu heq
  · -- constant region: M < exp (-κ x)
    exact frozenWaveOperator_upperBarrier_const_region_nonpos_pos
      p hχ_nonneg hχ hα hM hMchi hu hgt

end ShenWork.Paper1
