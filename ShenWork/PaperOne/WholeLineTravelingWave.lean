import ShenWork.PaperOne.WholeLineWaveTrap
import ShenWork.PaperOne.WholeLineFrozenSignal
import Mathlib.Topology.Algebra.Order.Field

noncomputable section

open Filter
open scoped Topology

namespace ShenWork.PaperOne

/-- The whole-line traveling-wave `u(t,x) = U(x - c t)`. -/
def wholeLineTravelingWaveU (c : ℝ) (U : ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun t x => U (x - c * t)

/-- The whole-line traveling-wave `v(t,x) = V(x - c t)`. -/
def wholeLineTravelingWaveV (c : ℝ) (V : ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun t x => V (x - c * t)

/-- The PaperOne frozen signal is the whole-line resolvent `Ψ(U^γ)`. -/
theorem wholeLine_frozenSignal_eq_Psi (γ : ℝ) (U : ℝ → ℝ) (x : ℝ) :
    frozenSignal γ U x = Psi (fun y : ℝ => (U y) ^ γ) 1 1 x := by
  rw [frozenSignal, wholeLineResolvent_eq_Psi]

/--
Brick 14: a stationary traveling-wave profile gives a classical solution of
the original whole-line system after the change of variables `x - c t`.

The chain-rule calculation is the existing `IsTravelingWave` bridge from
`Defs.lean`; this theorem fixes the PaperOne names for the translated fields.
-/
theorem wholeLine_travelingWave_solves
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hU_stationary : ∀ x,
      iteratedDeriv 2 U x + c * deriv U x
        - p.χ * deriv (fun y => (U y) ^ p.m * deriv V y) x
        + U x * (1 - (U x) ^ p.α) = 0)
    (hV_stationary : ∀ x,
      iteratedDeriv 2 V x - V x + (U x) ^ p.γ = 0)
    (hU_diff : ContDiff ℝ 2 U) (hV_diff : ContDiff ℝ 2 V) :
    IsGlobalClassicalSolution p
      (wholeLineTravelingWaveU c U) (wholeLineTravelingWaveV c V) := by
  have hU_d : Differentiable ℝ U := hU_diff.differentiable two_ne_zero
  have hV_d : Differentiable ℝ V := hV_diff.differentiable two_ne_zero
  intro T hT
  exact {
    hT := hT
    u_smooth := fun t x _ _ => by
      dsimp [wholeLineTravelingWaveU]
      exact
        ⟨(hU_d _).comp _ ((differentiableAt_const x).sub
            ((differentiableAt_const c).mul differentiableAt_id)),
          (hU_d _).comp _ (differentiableAt_id.sub (differentiableAt_const _))⟩
    v_smooth := fun t x _ _ => by
      change DifferentiableAt ℝ (fun z => V (z - c * t)) x
      exact
        (hV_d _).comp _ (differentiableAt_id.sub (differentiableAt_const _))
    pde_u := fun t x _ _ => by
      change
        deriv (fun t' => U (x - c * t')) t =
          iteratedDeriv 2 (fun z => U (z - c * t)) x
            - p.χ * deriv
              (fun y => U (y - c * t) ^ p.m *
                deriv (fun z => V (z - c * t)) y) x
            + U (x - c * t) * (1 - U (x - c * t) ^ p.α)
      have hinner : HasDerivAt (fun t' => x - c * t') (-c) t := by
        have := (hasDerivAt_const t x).sub ((hasDerivAt_id t).const_mul c)
        simpa using this
      have htime :
          deriv (fun t' => U (x - c * t')) t = deriv U (x - c * t) * (-c) :=
        ((hU_d _).hasDerivAt.comp t hinner).deriv
      have hU2 := congr_fun (iteratedDeriv_comp_sub_const 2 U (c * t)) x
      have hV1 : ∀ y, deriv (fun z => V (z - c * t)) y = deriv V (y - c * t) := by
        intro y
        have := congr_fun (iteratedDeriv_comp_sub_const 1 V (c * t)) y
        simpa [iteratedDeriv_one] using this
      have hChem :
          deriv (fun y => U (y - c * t) ^ p.m *
            deriv (fun z => V (z - c * t)) y) x =
          deriv (fun ξ => U ξ ^ p.m * deriv V ξ) (x - c * t) := by
        have hfun :
            (fun y => U (y - c * t) ^ p.m *
              deriv (fun z => V (z - c * t)) y) =
            (fun y => U (y - c * t) ^ p.m * deriv V (y - c * t)) := by
          ext y
          rw [hV1 y]
        rw [hfun]
        have := congr_fun (iteratedDeriv_comp_sub_const 1
          (fun ξ => U ξ ^ p.m * deriv V ξ) (c * t)) x
        simpa [iteratedDeriv_one] using this
      rw [htime, hU2, hChem]
      linarith [hU_stationary (x - c * t)]
    pde_v := fun t x _ _ => by
      change
        iteratedDeriv 2 (fun z => V (z - c * t)) x
          - V (x - c * t) + U (x - c * t) ^ p.γ = 0
      have h := congr_fun (iteratedDeriv_comp_sub_const 2 V (c * t)) x
      rw [h]
      exact hV_stationary (x - c * t)
  }

/-- Wrapper using the existing traveling-wave structure. -/
theorem wholeLine_travelingWave_solves_of_isTravelingWave
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hU_diff : ContDiff ℝ 2 U) (hV_diff : ContDiff ℝ 2 V) :
    IsGlobalClassicalSolution p
      (wholeLineTravelingWaveU c U) (wholeLineTravelingWaveV c V) :=
  wholeLine_travelingWave_solves hTW.ode_U hTW.ode_V hU_diff hV_diff

/-- The upper exponential barrier forces the right endpoint of a trapped
whole-line profile to be zero. -/
theorem wholeLine_waveTrap_rightLimit_zero
    {κ κt D : ℝ} {U : ℝ → ℝ}
    (hκ : 0 < κ) (hU : U ∈ WaveTrap κ κt D) :
    Tendsto U atTop (𝓝 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (upperBarrier_tendsto_zero_atTop hκ)
    (fun x => waveTrap_mem_nonneg hU x)
    (fun x => (hU.1 x).2)

/-- Normalized right-tail convergence from the exponential lower/upper
barrier squeeze. -/
theorem wholeLine_waveTrap_rightTail_ratio
    {κ κt D : ℝ} {U : ℝ → ℝ}
    (hκ : 0 < κ) (hκt : κ < κt) (hU : U ∈ WaveTrap κ κt D) :
    Tendsto (fun x : ℝ => U x / Real.exp (-(κ * x))) atTop (𝓝 1) := by
  have hdelta : 0 < κt - κ := sub_pos.mpr hκt
  have hExp :
      Tendsto (fun x : ℝ => Real.exp (-(κt - κ) * x)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hdelta))
  have hLower :
      Tendsto (fun x : ℝ => 1 - D * Real.exp (-(κt - κ) * x)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.sub (hExp.const_mul D))
  have hBounds : ∀ᶠ x in atTop,
      1 - D * Real.exp (-(κt - κ) * x) ≤ U x * Real.exp (κ * x) ∧
        U x * Real.exp (κ * x) ≤ 1 := by
    refine eventually_atTop.2 ⟨0, ?_⟩
    intro x hx
    exact barrier_squeeze hκ.le hx (hU.1 x).1 (hU.1 x).2 le_rfl
  have hMul :
      Tendsto (fun x : ℝ => U x * Real.exp (κ * x)) atTop (𝓝 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hLower tendsto_const_nhds
      (hBounds.mono fun _ hx => hx.1)
      (hBounds.mono fun _ hx => hx.2)
  have hDiv :
      (fun x : ℝ => U x / Real.exp (-(κ * x))) =
        fun x : ℝ => U x * Real.exp (κ * x) := by
    funext x
    rw [div_eq_mul_inv, Real.exp_neg]
    simp
  simpa [hDiv] using hMul

/--
Brick 15: a profile in the whole-line wave trap is antitone, vanishes at the
right endpoint, and has leading right tail `exp (-κ x)`.
-/
theorem wholeLine_travelingWave_rightLimit
    {κ κt D : ℝ} {U : ℝ → ℝ}
    (hκ : 0 < κ) (hκt : κ < κt) (hU : U ∈ WaveTrap κ κt D) :
    Tendsto U atTop (𝓝 0) ∧
      Tendsto (fun x : ℝ => U x / Real.exp (-(κ * x))) atTop (𝓝 1) ∧
      Antitone U :=
  ⟨wholeLine_waveTrap_rightLimit_zero hκ hU,
    wholeLine_waveTrap_rightTail_ratio hκ hκt hU,
    hU.2⟩

#print axioms wholeLine_frozenSignal_eq_Psi
#print axioms wholeLine_travelingWave_solves
#print axioms wholeLine_travelingWave_solves_of_isTravelingWave
#print axioms wholeLine_waveTrap_rightLimit_zero
#print axioms wholeLine_waveTrap_rightTail_ratio
#print axioms wholeLine_travelingWave_rightLimit

end ShenWork.PaperOne
