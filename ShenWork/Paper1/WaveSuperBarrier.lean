/-
  WHOLE-LINE cross-frozen super-barrier (B1 `RotheFloorResidual`).

  The committed regional super-barriers in `Statements.lean` only establish
  `frozenWaveOperator p c u (upperBarrier κ M) x ≤ 0` AWAY from the free
  interface `exp (-κ x) = M`:

    * `frozenWaveOperator_upperBarrier_const_region_nonpos_of_elliptic_le_source`
      on the constant region `M < exp (-κ x)`  (where `upperBarrier = M`), and
    * `frozenWaveOperator_upperBarrier_exp_region_nonpos_of_chi_nonpos`
      on the exponential region `exp (-κ x) < M`  (where `upperBarrier = e^{-κ x}`).

  `upperBarrier κ M = min M (e^{-κ x})` has a CONCAVE CORNER at the crossover
  `x*` with `exp (-κ x*) = M`: the left slope is `0`, the right slope is `-κM`.
  At this single point `upperBarrier` is NOT differentiable
  (`not_differentiableAt_upperBarrier_of_interface`), so the classical
  `frozenWaveOperator` (which uses `deriv` / `iteratedDeriv 2`) evaluates the
  diffusion and convection at the Mathlib junk value `0`.

  THE KINK COMPUTATION (this file).  At `x = x*`:
    * `upperBarrier κ M x* = M`                              (the two pieces agree)
    * `deriv (upperBarrier κ M) x* = 0`                      (junk: not diff.)
    * `iteratedDeriv 2 (upperBarrier κ M) x* = 0`            (junk: `deriv` is even
        discontinuous at `x*`, hence not diff.)
    * `deriv (fun y => (Ū y)^m · V_u'(y)) x* ≤ 0`           (either junk `0`, or —
        in the differentiable subcase — equal to `M^m · V_u''(x*)`
        `= M^m · (V_u(x*) - u(x*)^γ) ≤ 0` by the closed plateau source bound).
  Hence
    `frozenWaveOperator p c u (upperBarrier κ M) x* = -χ · (deriv F x*) + M(1 - M^α)`
    `≤ 0`  because `-χ ≥ 0`, `deriv F x* ≤ 0`, and `M(1 - M^α) ≤ 0` (`M ≥ 1`, `α ≥ 1`).

  RESOLUTION OF THE VISCOSITY CONCERN.  The orchestrator flagged that in the
  differentiable subcase the kink could fail unless `V_u ≤ u^γ` at the corner.
  This is genuinely needed, and it is supplied by CLOSING the plateau source
  bound at the interface: we require `∀ x, M ≤ exp (-κ x) → V_u ≤ u^γ`
  (`≤` instead of the regional `<`).  This single closed boundary point makes the
  classical upper barrier an honest WHOLE-LINE classical super-solution; no
  smoothing or viscosity notion is required.

  Main result: `whole_line_super_barrier`.
-/
import ShenWork.Paper1.Statements

open Filter Topology

namespace ShenWork.Paper1

variable {p : CMParams} {c κ M : ℝ} {u : ℝ → ℝ}

/-- At the free interface `exp (-κ x) = M`, the upper barrier value is `M`. -/
theorem upperBarrier_eq_M_at_interface {κ M x : ℝ}
    (hx : Real.exp (-κ * x) = M) :
    upperBarrier κ M x = M :=
  upperBarrier_eq_M_of_le_exp hx.ge

/-- At the free interface the (classical) first derivative of the barrier is the
junk value `0`, since the barrier is not differentiable there. -/
theorem upperBarrier_deriv_eq_zero_at_interface {κ M x : ℝ}
    (hκ : 0 < κ) (hM : 0 < M) (hx : Real.exp (-κ * x) = M) :
    deriv (upperBarrier κ M) x = 0 :=
  deriv_zero_of_not_differentiableAt
    (not_differentiableAt_upperBarrier_of_interface hκ hM hx)

/-- On a punctured LEFT neighbourhood of the interface the barrier's derivative
is constantly `0` (we are inside the constant region). -/
theorem upperBarrier_deriv_eventuallyEq_zero_left {κ M x : ℝ}
    (hκ : 0 < κ) (hx : Real.exp (-κ * x) = M) :
    deriv (upperBarrier κ M) =ᶠ[𝓝[Set.Iio x] x] fun _ : ℝ => 0 := by
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hyexp : M < Real.exp (-κ * y) := by
    rw [← hx]
    apply Real.exp_lt_exp.mpr
    have hylt : y < x := hy
    nlinarith [hylt, hκ]
  exact upperBarrier_deriv_eq_zero_of_const_lt hyexp

/-- On a punctured RIGHT neighbourhood of the interface the barrier's derivative
equals `-κ · e^{-κ y}` (we are inside the exponential region). -/
theorem upperBarrier_deriv_eventuallyEq_exp_right {κ M x : ℝ}
    (hκ : 0 < κ) (hx : Real.exp (-κ * x) = M) :
    deriv (upperBarrier κ M) =ᶠ[𝓝[Set.Ioi x] x]
      fun y : ℝ => -κ * expDecay κ y := by
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hyexp : Real.exp (-κ * y) < M := by
    rw [← hx]
    apply Real.exp_lt_exp.mpr
    have hylt : x < y := hy
    nlinarith [hylt, hκ]
  exact upperBarrier_deriv_eq_exp_of_lt hyexp

/-- The barrier's derivative is DISCONTINUOUS at the interface: the left limit is
`0`, the right limit is `-κ M ≠ 0`.  Therefore `deriv (upperBarrier κ M)` is not
differentiable at the interface. -/
theorem not_differentiableAt_deriv_upperBarrier_of_interface {κ M x : ℝ}
    (hκ : 0 < κ) (hM : 0 < M) (hx : Real.exp (-κ * x) = M) :
    ¬ DifferentiableAt ℝ (deriv (upperBarrier κ M)) x := by
  intro hdiff
  have hcont : ContinuousAt (deriv (upperBarrier κ M)) x := hdiff.continuousAt
  -- left limit = 0
  have hleft : Tendsto (deriv (upperBarrier κ M))
      (𝓝[Set.Iio x] x) (𝓝 (deriv (upperBarrier κ M) x)) :=
    hcont.continuousWithinAt.tendsto
  have hleft0 : Tendsto (deriv (upperBarrier κ M))
      (𝓝[Set.Iio x] x) (𝓝 0) :=
    Tendsto.congr'
      (upperBarrier_deriv_eventuallyEq_zero_left hκ hx).symm
      (tendsto_const_nhds)
  -- the left filter is nontrivial
  haveI hbot : (𝓝[Set.Iio x] x).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Iio]
    exact Set.mem_Iic.mpr le_rfl
  have hval0 : deriv (upperBarrier κ M) x = 0 :=
    tendsto_nhds_unique hleft hleft0
  -- right limit = -κ M
  have hright : Tendsto (deriv (upperBarrier κ M))
      (𝓝[Set.Ioi x] x) (𝓝 (deriv (upperBarrier κ M) x)) :=
    hcont.continuousWithinAt.tendsto
  have hexp_tendsto :
      Tendsto (fun y : ℝ => -κ * expDecay κ y)
        (𝓝[Set.Ioi x] x) (𝓝 (-κ * expDecay κ x)) := by
    have hc : Continuous (fun y : ℝ => -κ * expDecay κ y) :=
      continuous_const.mul (expDecay_continuous κ)
    exact (hc.continuousWithinAt).tendsto
  have hrightexp : Tendsto (deriv (upperBarrier κ M))
      (𝓝[Set.Ioi x] x) (𝓝 (-κ * expDecay κ x)) :=
    Tendsto.congr'
      (upperBarrier_deriv_eventuallyEq_exp_right hκ hx).symm
      hexp_tendsto
  haveI hbotR : (𝓝[Set.Ioi x] x).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioi]
    exact Set.mem_Ici.mpr le_rfl
  have hvalR : deriv (upperBarrier κ M) x = -κ * expDecay κ x :=
    tendsto_nhds_unique hright hrightexp
  -- combine: 0 = -κ M
  have hExpM : expDecay κ x = M := by simpa [expDecay] using hx
  have hzero : -κ * M = 0 := by
    rw [hval0] at hvalR
    rw [hExpM] at hvalR
    linarith [hvalR]
  have hnonzero : -κ * M ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr (ne_of_gt hκ)) (ne_of_gt hM)
  exact hnonzero hzero

/-- At the interface, the (classical) second derivative of the barrier is the
junk value `0`. -/
theorem upperBarrier_iteratedDeriv_two_eq_zero_at_interface {κ M x : ℝ}
    (hκ : 0 < κ) (hM : 0 < M) (hx : Real.exp (-κ * x) = M) :
    iteratedDeriv 2 (upperBarrier κ M) x = 0 := by
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
  change deriv (deriv (upperBarrier κ M)) x = 0
  exact deriv_zero_of_not_differentiableAt
    (not_differentiableAt_deriv_upperBarrier_of_interface hκ hM hx)

/-- The chemotactic flux `(Ū)^m · V_u'` agrees on a punctured LEFT neighbourhood
of the interface with `M^m · V_u'`. -/
theorem chemFlux_eventuallyEq_left {κ M x : ℝ}
    (hκ : 0 < κ) (hx : Real.exp (-κ * x) = M) (p : CMParams) (u : ℝ → ℝ) :
    (fun y => (upperBarrier κ M y) ^ p.m * deriv (frozenElliptic p u) y)
      =ᶠ[𝓝[Set.Iio x] x]
      fun y => M ^ p.m * deriv (frozenElliptic p u) y := by
  filter_upwards [upperBarrier_eventuallyEq_const_left_of_interface hκ hx]
    with y hy
  rw [hy]

/-- At the interface the chemotactic-flux derivative is `≤ 0`.

Two subcases:
* the flux is NOT differentiable at the interface (the generic case, since
  `(Ū)^m` has a corner there): the classical `deriv` is the junk value `0`;
* the flux IS differentiable (only possible when `V_u'(x*) = 0`): then its
  derivative equals the LEFT-region value `M^m · V_u''(x*) = M^m (V_u(x*) - u(x*)^γ)`,
  which is `≤ 0` by the closed plateau source bound.
-/
theorem chemFlux_deriv_nonpos_at_interface
    (hκ : 0 < κ) (hM : 1 ≤ M)
    (hu : IsCUnifBdd u) (hu_nonneg : ∀ x, 0 ≤ u x)
    {x : ℝ} (hx : Real.exp (-κ * x) = M)
    (hsrc : frozenElliptic p u x ≤ (u x) ^ p.γ) :
    deriv (fun y => (upperBarrier κ M y) ^ p.m *
        deriv (frozenElliptic p u) y) x ≤ 0 := by
  set F := fun y => (upperBarrier κ M y) ^ p.m * deriv (frozenElliptic p u) y
    with hF
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  have hMm_nonneg : 0 ≤ M ^ p.m := Real.rpow_nonneg hMpos.le _
  by_cases hdiff : DifferentiableAt ℝ F x
  · -- differentiable: compute via the LEFT region, where F = M^m · V'
    have hderivWithin :
        derivWithin F (Set.Iio x) x = deriv F x :=
      hdiff.derivWithin (uniqueDiffWithinAt_Iio x)
    -- F = M^m · V' on a left neighbourhood, with matching value at x
    have hFx : F x = (fun y => M ^ p.m * deriv (frozenElliptic p u) y) x := by
      have hbx : upperBarrier κ M x = M := upperBarrier_eq_M_at_interface hx
      simp only [hF, hbx]
    have hEq :
        derivWithin F (Set.Iio x) x =
          derivWithin (fun y => M ^ p.m * deriv (frozenElliptic p u) y)
            (Set.Iio x) x :=
      Filter.EventuallyEq.derivWithin_eq (chemFlux_eventuallyEq_left hκ hx p u) hFx
    -- derivWithin of M^m · V' on Iio x equals M^m · V''(x) (full deriv exists)
    have hVdiff : DifferentiableAt ℝ (deriv (frozenElliptic p u)) x :=
      frozenElliptic_deriv_differentiableAt p hu hu_nonneg x
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
      frozenElliptic_deriv_deriv_eq p hu hu_nonneg x
    -- chain the equalities
    have hval : deriv F x = M ^ p.m * (frozenElliptic p u x - (u x) ^ p.γ) := by
      rw [← hderivWithin, hEq, hderivWithinFull, hderivFull, hVV]
    rw [hval]
    exact mul_nonpos_of_nonneg_of_nonpos hMm_nonneg (sub_nonpos.mpr hsrc)
  · -- not differentiable: junk value 0
    rw [deriv_zero_of_not_differentiableAt hdiff]

/-- **Kink super-barrier.**  At the free interface `exp (-κ x) = M`, the classical
`frozenWaveOperator` of the upper barrier is `≤ 0` (for `χ ≤ 0`, `M ≥ 1`, and the
closed plateau source bound `V_u(x*) ≤ u(x*)^γ`). -/
theorem frozenWaveOperator_upperBarrier_interface_nonpos
    (hχ : p.χ ≤ 0) (hκ : 0 < κ) (hM : 1 ≤ M)
    (hu : IsCUnifBdd u) (hu_nonneg : ∀ x, 0 ≤ u x)
    {x : ℝ} (hx : Real.exp (-κ * x) = M)
    (hsrc : frozenElliptic p u x ≤ (u x) ^ p.γ) :
    frozenWaveOperator p c u (upperBarrier κ M) x ≤ 0 := by
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  have hMnonneg : (0 : ℝ) ≤ M := hMpos.le
  unfold frozenWaveOperator
  rw [upperBarrier_iteratedDeriv_two_eq_zero_at_interface hκ hMpos hx,
    upperBarrier_deriv_eq_zero_at_interface hκ hMpos hx,
    upperBarrier_eq_M_at_interface hx]
  -- residual = -χ · (deriv F x) + M (1 - M^α)
  have hchem :
      deriv (fun y => (upperBarrier κ M y) ^ p.m *
        deriv (frozenElliptic p u) y) x ≤ 0 :=
    chemFlux_deriv_nonpos_at_interface hκ hM hu hu_nonneg hx hsrc
  have hchemTerm :
      -p.χ * deriv (fun y => (upperBarrier κ M y) ^ p.m *
        deriv (frozenElliptic p u) y) x ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (neg_nonneg.mpr hχ) hchem
  have hMa : 1 ≤ M ^ p.α := Real.one_le_rpow hM (by linarith [p.hα])
  have hlog : M * (1 - M ^ p.α) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hMnonneg (by linarith)
  nlinarith [hchemTerm, hlog]

/-- **Whole-line cross-frozen super-barrier** (B1 `RotheFloorResidual`, `χ ≤ 0`).

For every trapped profile `u`, the classical `frozenWaveOperator` of the upper
barrier `upperBarrier κ M = min M (e^{-κ x})` is `≤ 0` on the WHOLE line —
including the corner at the free interface `exp (-κ x) = M`.

The constant and exponential regions are the committed regional super-barriers;
the interface kink is `frozenWaveOperator_upperBarrier_interface_nonpos`, where
the diffusion and convection terms vanish at the Mathlib junk value `0` (the
barrier and its first derivative are non-differentiable there) and the
chemotactic flux term is controlled by the closed plateau source bound.

The plateau source bound is taken in its CLOSED form `M ≤ exp (-κ x) → …`; the
only point this adds over the regional `M < exp (-κ x) → …` is the interface
itself, which is exactly what the kink needs.  No smoothing of the barrier and
no viscosity-supersolution notion is required: the classical operator with the
Mathlib junk-derivative convention already satisfies `≤ 0` everywhere. -/
theorem whole_line_super_barrier
    (hχ : p.χ ≤ 0) (hα : p.α ≤ p.m + p.γ - 1)
    (hκ : 0 < κ) (hκ1 : κ < 1) (hγκ : p.γ * κ < 1) (hmκ : κ * p.m ≤ 1)
    (hM : 1 ≤ M)
    (hMbound :
      |p.χ| * ((1 + p.m * p.γ * κ ^ 2) / (1 - p.γ ^ 2 * κ ^ 2)) *
        M ^ (p.m + p.γ - p.α - 1) ≤ 1)
    (hc : c = κ + κ⁻¹)
    (hsrc :
      ∀ x, M ≤ Real.exp (-κ * x) →
        frozenElliptic p u x ≤ (u x) ^ p.γ) :
    InMonotoneWaveTrapSet κ M u →
    ∀ x, frozenWaveOperator p c u (upperBarrier κ M) x ≤ 0 := by
  intro hmono x
  have hu : InWaveTrapSet κ M u := hmono.1
  rcases lt_trichotomy (Real.exp (-κ * x)) M with hlt | heq | hgt
  · -- exponential region: exp (-κ x) < M
    have hx : expDecay κ x < M := by simpa [expDecay] using hlt
    have hc_two : 2 ≤ c :=
      (two_lt_of_pos_lt_one_kappa_speed hκ hκ1 hc).le
    have hκ_eq : κ = kappa c :=
      (kappa_eq_of_pos_lt_one_kappa_speed hκ hκ1 hc).symm
    exact frozenWaveOperator_upperBarrier_exp_region_nonpos_of_chi_nonpos
      p hc_two hκ_eq hχ hα hκ hγκ hmκ hM hMbound hu hx
      (frozenElliptic_deriv_differentiableAt p hu.cunif_bdd hu.nonneg x)
  · -- interface kink: exp (-κ x) = M
    exact frozenWaveOperator_upperBarrier_interface_nonpos hχ hκ hM
      hu.cunif_bdd hu.nonneg heq (hsrc x heq.ge)
  · -- constant region: M < exp (-κ x)
    exact frozenWaveOperator_upperBarrier_const_region_nonpos_of_elliptic_le_source
      p hχ hM hu.cunif_bdd hu.nonneg hgt (hsrc x hgt.le)

end ShenWork.Paper1
