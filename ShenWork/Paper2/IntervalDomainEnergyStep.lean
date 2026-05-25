/-
  ShenWork/Paper2/IntervalDomainEnergyStep.lean

  Honest bridge from the Paper 2 bootstrap energy inequality to the Moser
  single-step interface used by `IntervalDomainChain`.

  This file does not claim `Lemma_2_6 intervalDomain`.  It isolates the exact
  remaining analytic hypotheses needed to use the already-proved Moser chain:
  a nonnegative time-dissipation term and the interpolation estimate at each
  exponent.

  B3-item1 frontier note: the current interval-domain API can prove the
  endpoint Neumann boundary contribution is zero, because `intervalDomain`
  hard-codes `normalDeriv = 0` on `{0,1}`.  The actual analytic integration by
  parts identity
      `integral test * laplacian f = boundary - integral test' * f'`
  and the time chain rule
      `d/dt integral |u|^p = p * integral |u|^(p-2) u u_t`
  still require a differentiability/integrability layer for `intervalDomainLift`
  and differentiation under the parameter integral.  They are therefore kept
  below as explicitly named theorem hypotheses (`hIBP`, `hLpTime`), not as
  axioms or hidden `Prop` aliases.  The same applies to moving the pointwise
  PDE, stated on `inside`, into an interval integral: that is recorded below as
  `hPDEIntegral`.

  B3 cross-diffusion frontier note: the algebra after a
  Gagliardo-Nirenberg/Young estimate is formalized below, including absorption
  of the `eps * weighted-gradient` term into the dissipative left-hand side and
  the resulting closed derivative inequality.  What is still not proved here is
  the analytic bridge from `gagliardoNirenberg_interval` to
  `CrossDiffusionBootstrapEstimate`: it requires transporting the real
  interval `lpNorm` estimate to `intervalDomain` integrals, a spatial
  chain-rule/coercivity comparison for the weighted `u` powers, and an
  independent bound on the `v`-gradient factor in the cross-diffusion term.
  There is also a statement-level mismatch still visible in the API: the
  current `intervalDomain.chemotaxisDiv` contains the Paper 2 `u * grad v`
  structure, while the requested `∇·(u^m ∇v)` term is not yet a separate
  interval-domain operator.
-/
import ShenWork.Paper2.IntervalDomainLpMonotonicity

open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainLpMonotonicity
open ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.Paper2.IntervalDomainEnergyStep

/-- Left endpoint of the concrete unit interval domain. -/
def intervalDomainLeftEndpoint : intervalDomain.Point :=
  ⟨0, by exact ⟨le_rfl, zero_le_one⟩⟩

/-- Right endpoint of the concrete unit interval domain. -/
def intervalDomainRightEndpoint : intervalDomain.Point :=
  ⟨1, by exact ⟨zero_le_one, le_rfl⟩⟩

theorem intervalDomain_leftEndpoint_mem_boundary :
    intervalDomainLeftEndpoint ∈ intervalDomain.boundary := by
  change intervalDomainLeftEndpoint.1 = 0 ∨ intervalDomainLeftEndpoint.1 = 1
  left
  rfl

theorem intervalDomain_rightEndpoint_mem_boundary :
    intervalDomainRightEndpoint ∈ intervalDomain.boundary := by
  change intervalDomainRightEndpoint.1 = 0 ∨ intervalDomainRightEndpoint.1 = 1
  right
  rfl

/-- On the concrete interval domain, the normal derivative is definitionally
zero at boundary points.  This is the formal Neumann endpoint fact available in
the current API. -/
theorem intervalDomain_normalDeriv_zero_on_boundary
    (f : intervalDomain.Point → ℝ) {x : intervalDomain.Point}
    (hx : x ∈ intervalDomain.boundary) :
    intervalDomain.normalDeriv f x = 0 := by
  have hx' : x.1 = 0 ∨ x.1 = 1 := by
    simpa [intervalDomain] using hx
  simpa [intervalDomain] using
    (intervalDomainNormalDeriv_endpoint f (x := x) hx')

theorem intervalDomain_normalDeriv_leftEndpoint
    (f : intervalDomain.Point → ℝ) :
    intervalDomain.normalDeriv f intervalDomainLeftEndpoint = 0 := by
  exact intervalDomain_normalDeriv_zero_on_boundary f
    (x := intervalDomainLeftEndpoint) intervalDomain_leftEndpoint_mem_boundary

theorem intervalDomain_normalDeriv_rightEndpoint
    (f : intervalDomain.Point → ℝ) :
    intervalDomain.normalDeriv f intervalDomainRightEndpoint = 0 := by
  exact intervalDomain_normalDeriv_zero_on_boundary f
    (x := intervalDomainRightEndpoint) intervalDomain_rightEndpoint_mem_boundary

/-- Classical interval solutions carry the Neumann condition for `u`. -/
theorem intervalDomain_solution_neumann_u_zero
    {params : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T) {x : intervalDomain.Point}
    (hx : x ∈ intervalDomain.boundary) :
    intervalDomain.normalDeriv (u t) x = 0 :=
  (hsol.neumann ht0 htT hx).1

/-- Classical interval solutions carry the Neumann condition for `v`. -/
theorem intervalDomain_solution_neumann_v_zero
    {params : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T) {x : intervalDomain.Point}
    (hx : x ∈ intervalDomain.boundary) :
    intervalDomain.normalDeriv (v t) x = 0 :=
  (hsol.neumann ht0 htT hx).2

/-- Boundary flux term in the one-dimensional integration-by-parts formula. -/
def intervalDomainNeumannBoundaryTerm
    (test f : intervalDomain.Point → ℝ) : ℝ :=
  test intervalDomainRightEndpoint *
      intervalDomain.normalDeriv f intervalDomainRightEndpoint -
    test intervalDomainLeftEndpoint *
      intervalDomain.normalDeriv f intervalDomainLeftEndpoint

/-- The product of lifted spatial derivatives on `[0,1]`. -/
def intervalDomainDerivativePairIntegral
    (test f : intervalDomain.Point → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1,
    deriv (intervalDomainLift test) x * deriv (intervalDomainLift f) x

/-- The Neumann endpoint contribution vanishes for the concrete interval
domain. -/
theorem intervalDomain_neumannBoundaryTerm_eq_zero
    (test f : intervalDomain.Point → ℝ) :
    intervalDomainNeumannBoundaryTerm test f = 0 := by
  unfold intervalDomainNeumannBoundaryTerm
  rw [intervalDomain_normalDeriv_rightEndpoint f,
    intervalDomain_normalDeriv_leftEndpoint f]
  ring

/-- Conditional integration by parts on the interval after removing the
Neumann boundary term.

The hypothesis `hIBP` is the honest analytic frontier: it is the missing
spatial integration-by-parts theorem for the lifted interval functions.  This
theorem only discharges the boundary contribution, which is currently
formalized. -/
theorem intervalDomain_integrationByParts_neumann_of_boundary_identity
    (test f : intervalDomain.Point → ℝ)
    (hIBP :
      intervalDomain.integral
          (fun x => test x * intervalDomain.laplacian f x) =
        intervalDomainNeumannBoundaryTerm test f -
          intervalDomainDerivativePairIntegral test f) :
    intervalDomain.integral
        (fun x => test x * intervalDomain.laplacian f x) =
      -(intervalDomainDerivativePairIntegral test f) := by
  rw [hIBP, intervalDomain_neumannBoundaryTerm_eq_zero]
  ring

/-- The Lp energy functional on the concrete interval domain. -/
def intervalDomainLpEnergy
    (pExp : ℝ) (u : ℝ → intervalDomain.Point → ℝ) (t : ℝ) : ℝ :=
  intervalDomain.integral (fun x => |u t x| ^ pExp)

/-- The weighted time-derivative term appearing in the Lp chain rule. -/
def intervalDomainLpEnergyWeightedTimeTerm
    (pExp : ℝ) (u : ℝ → intervalDomain.Point → ℝ)
    (t : ℝ) (x : intervalDomain.Point) : ℝ :=
  |u t x| ^ (pExp - 2) * u t x * intervalDomain.timeDeriv u t x

/-- Conditional Lp energy identity in the form used by Paper 2 estimates.

The hypothesis `hLpTime` is the honest analytic frontier: it packages the
chain rule for `|u|^p` together with differentiation under the interval
integral. -/
theorem intervalDomain_lp_energy_identity_scaled_of_time_frontier
    {pExp T : ℝ} {u : ℝ → intervalDomain.Point → ℝ}
    (hpExp : pExp ≠ 0)
    (hLpTime : ∀ t, 0 < t → t < T →
      deriv (fun τ => intervalDomainLpEnergy pExp u τ) t =
        pExp * intervalDomain.integral
          (intervalDomainLpEnergyWeightedTimeTerm pExp u t)) :
    ∀ t, 0 < t → t < T →
      (1 / pExp) *
          deriv (fun τ => intervalDomainLpEnergy pExp u τ) t =
        intervalDomain.integral
          (intervalDomainLpEnergyWeightedTimeTerm pExp u t) := by
  intro t ht0 htT
  rw [hLpTime t ht0 htT]
  field_simp [hpExp]

/-- Multiplying the classical `u` PDE by the Lp weight is pointwise available
on the interior.  Moving this equality under the interval integral is a
separate analytic frontier because the PDE is stated on `inside`. -/
theorem intervalDomain_solution_lp_weighted_timeDeriv_eq_pde
    {params : CM2Params} {T t pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T) {x : intervalDomain.Point}
    (hx : x ∈ intervalDomain.inside) :
    intervalDomainLpEnergyWeightedTimeTerm pExp u t x =
      |u t x| ^ (pExp - 2) * u t x *
        (intervalDomain.laplacian (u t) x
          - params.χ₀ * intervalDomain.chemotaxisDiv params (u t) (v t) x
          + u t x * (params.a - params.b * (u t x) ^ params.α)) := by
  unfold intervalDomainLpEnergyWeightedTimeTerm
  rw [hsol.pde_u ht0 htT hx]

/-- Test function used after multiplying the `u` equation by
`|u|^(p-2) u`. -/
def intervalDomainLpDiffusionTest
    (pExp : ℝ) (u : ℝ → intervalDomain.Point → ℝ)
    (t : ℝ) (x : intervalDomain.Point) : ℝ :=
  |u t x| ^ (pExp - 2) * u t x

/-- The diffusion integral before integration by parts. -/
def intervalDomainLpDiffusionIntegral
    (pExp : ℝ) (u : ℝ → intervalDomain.Point → ℝ) (t : ℝ) : ℝ :=
  intervalDomain.integral
    (fun x =>
      intervalDomainLpDiffusionTest pExp u t x *
        intervalDomain.laplacian (u t) x)

/-- The derivative-pair dissipation after interval integration by parts. -/
def intervalDomainLpDiffusionDissipation
    (pExp : ℝ) (u : ℝ → intervalDomain.Point → ℝ) (t : ℝ) : ℝ :=
  intervalDomainDerivativePairIntegral
    (intervalDomainLpDiffusionTest pExp u t) (u t)

/-- The weighted gradient term controlled by the cross-diffusion bootstrap
estimate.  Turning the derivative-pair dissipation into this expression is a
separate spatial chain-rule/coercivity input. -/
def intervalDomainLpWeightedGradientDissipation
    (pExp : ℝ) (u : ℝ → intervalDomain.Point → ℝ) (t : ℝ) : ℝ :=
  intervalDomain.integral
    (fun x => (u t x) ^ (pExp - 2) * (intervalDomain.gradNorm (u t) x) ^ 2)

/-- Chemotaxis contribution in the weighted Lp energy identity. -/
def intervalDomainLpChemotaxisIntegral
    (params : CM2Params) (pExp : ℝ)
    (u v : ℝ → intervalDomain.Point → ℝ) (t : ℝ) : ℝ :=
  intervalDomain.integral
    (fun x =>
      intervalDomainLpDiffusionTest pExp u t x *
        intervalDomain.chemotaxisDiv params (u t) (v t) x)

/-- Logistic contribution in the weighted Lp energy identity. -/
def intervalDomainLpLogisticIntegral
    (params : CM2Params) (pExp : ℝ)
    (u : ℝ → intervalDomain.Point → ℝ) (t : ℝ) : ℝ :=
  intervalDomain.integral
    (fun x =>
      intervalDomainLpDiffusionTest pExp u t x *
        (u t x * (params.a - params.b * (u t x) ^ params.α)))

/-- Exact conditional Lp energy balance after the Neumann boundary term has
been removed.

The three analytic frontiers are explicit:
* `hLpTime`: time chain rule and differentiation under the interval integral;
* `hPDEIntegral`: inserting the PDE into the weighted interval integral;
* `hIBP`: spatial integration by parts for the lifted interval functions. -/
theorem intervalDomain_lp_energy_balance_of_frontiers
    {params : CM2Params} {T pExp t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hpExp : pExp ≠ 0) (ht0 : 0 < t) (htT : t < T)
    (hLpTime : ∀ s, 0 < s → s < T →
      deriv (fun τ => intervalDomainLpEnergy pExp u τ) s =
        pExp * intervalDomain.integral
          (intervalDomainLpEnergyWeightedTimeTerm pExp u s))
    (hPDEIntegral :
      intervalDomain.integral
          (intervalDomainLpEnergyWeightedTimeTerm pExp u t) =
        intervalDomainLpDiffusionIntegral pExp u t -
          params.χ₀ * intervalDomainLpChemotaxisIntegral params pExp u v t +
          intervalDomainLpLogisticIntegral params pExp u t)
    (hIBP :
      intervalDomainLpDiffusionIntegral pExp u t =
        intervalDomainNeumannBoundaryTerm
            (intervalDomainLpDiffusionTest pExp u t) (u t) -
          intervalDomainLpDiffusionDissipation pExp u t) :
    (1 / pExp) *
        deriv (fun τ => intervalDomainLpEnergy pExp u τ) t +
      intervalDomainLpDiffusionDissipation pExp u t =
        -params.χ₀ * intervalDomainLpChemotaxisIntegral params pExp u v t +
          intervalDomainLpLogisticIntegral params pExp u t := by
  have htime :=
    intervalDomain_lp_energy_identity_scaled_of_time_frontier
      (pExp := pExp) (T := T) (u := u) hpExp hLpTime t ht0 htT
  have hIBP' :
      intervalDomain.integral
          (fun x =>
            intervalDomainLpDiffusionTest pExp u t x *
              intervalDomain.laplacian (u t) x) =
        intervalDomainNeumannBoundaryTerm
            (intervalDomainLpDiffusionTest pExp u t) (u t) -
          intervalDomainDerivativePairIntegral
            (intervalDomainLpDiffusionTest pExp u t) (u t) := by
    simpa [intervalDomainLpDiffusionIntegral,
      intervalDomainLpDiffusionDissipation] using hIBP
  have hdiff :=
    intervalDomain_integrationByParts_neumann_of_boundary_identity
      (intervalDomainLpDiffusionTest pExp u t) (u t) hIBP'
  have hdiff_named :
      intervalDomainLpDiffusionIntegral pExp u t =
        -intervalDomainLpDiffusionDissipation pExp u t := by
    simpa [intervalDomainLpDiffusionIntegral,
      intervalDomainLpDiffusionDissipation] using hdiff
  calc
    (1 / pExp) *
          deriv (fun τ => intervalDomainLpEnergy pExp u τ) t +
        intervalDomainLpDiffusionDissipation pExp u t
        = intervalDomain.integral
            (intervalDomainLpEnergyWeightedTimeTerm pExp u t) +
          intervalDomainLpDiffusionDissipation pExp u t := by
            rw [htime]
    _ =
        (intervalDomainLpDiffusionIntegral pExp u t -
            params.χ₀ * intervalDomainLpChemotaxisIntegral params pExp u v t +
            intervalDomainLpLogisticIntegral params pExp u t) +
          intervalDomainLpDiffusionDissipation pExp u t := by
            rw [hPDEIntegral]
    _ =
        -params.χ₀ * intervalDomainLpChemotaxisIntegral params pExp u v t +
          intervalDomainLpLogisticIntegral params pExp u t := by
            rw [hdiff_named]
            ring

/-- Conditional Lp energy inequality with chemotaxis controlled by the
cross-diffusion energy term.  `hDiffusionCoercive` is the remaining spatial
chain-rule/coercivity bridge from the derivative-pair dissipation to the
weighted gradient dissipation. -/
theorem intervalDomain_lp_energy_gradient_inequality_of_frontiers
    {params : CM2Params} {T pExp A chiBound t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hpExp : pExp ≠ 0) (ht0 : 0 < t) (htT : t < T)
    (hLpTime : ∀ s, 0 < s → s < T →
      deriv (fun τ => intervalDomainLpEnergy pExp u τ) s =
        pExp * intervalDomain.integral
          (intervalDomainLpEnergyWeightedTimeTerm pExp u s))
    (hPDEIntegral :
      intervalDomain.integral
          (intervalDomainLpEnergyWeightedTimeTerm pExp u t) =
        intervalDomainLpDiffusionIntegral pExp u t -
          params.χ₀ * intervalDomainLpChemotaxisIntegral params pExp u v t +
          intervalDomainLpLogisticIntegral params pExp u t)
    (hIBP :
      intervalDomainLpDiffusionIntegral pExp u t =
        intervalDomainNeumannBoundaryTerm
            (intervalDomainLpDiffusionTest pExp u t) (u t) -
          intervalDomainLpDiffusionDissipation pExp u t)
    (hDiffusionCoercive :
      A * intervalDomainLpWeightedGradientDissipation pExp u t ≤
        intervalDomainLpDiffusionDissipation pExp u t)
    (hCrossControl :
      -params.χ₀ * intervalDomainLpChemotaxisIntegral params pExp u v t ≤
        chiBound *
          intervalDomain.crossDiffusionEnergyTerm params pExp (u t) (v t)) :
    (1 / pExp) *
        deriv (fun τ => intervalDomainLpEnergy pExp u τ) t +
      A * intervalDomainLpWeightedGradientDissipation pExp u t ≤
        chiBound *
          intervalDomain.crossDiffusionEnergyTerm params pExp (u t) (v t) +
          intervalDomainLpLogisticIntegral params pExp u t := by
  have hbalance :=
    intervalDomain_lp_energy_balance_of_frontiers
      (params := params) (T := T) (pExp := pExp) (t := t)
      (u := u) (v := v) hpExp ht0 htT hLpTime hPDEIntegral hIBP
  calc
    (1 / pExp) *
          deriv (fun τ => intervalDomainLpEnergy pExp u τ) t +
        A * intervalDomainLpWeightedGradientDissipation pExp u t
        ≤
          (1 / pExp) *
              deriv (fun τ => intervalDomainLpEnergy pExp u τ) t +
            intervalDomainLpDiffusionDissipation pExp u t := by
            linarith
    _ =
        -params.χ₀ * intervalDomainLpChemotaxisIntegral params pExp u v t +
          intervalDomainLpLogisticIntegral params pExp u t := hbalance
    _ ≤
        chiBound *
          intervalDomain.crossDiffusionEnergyTerm params pExp (u t) (v t) +
          intervalDomainLpLogisticIntegral params pExp u t := by
          linarith

/-- Conditional Lp energy inequality after applying the existing
`CrossDiffusionBootstrapEstimate` to the controlled chemotaxis term. -/
theorem intervalDomain_lp_energy_cross_bootstrap_inequality_of_frontiers
    {params : CM2Params} {T rho pExp eps A chiBound t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hpExp : 1 < pExp) (heps : 0 < eps) (hchiBound : 0 ≤ chiBound)
    (ht0 : 0 < t) (htT : t < T)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hLpTime : ∀ s, 0 < s → s < T →
      deriv (fun τ => intervalDomainLpEnergy pExp u τ) s =
        pExp * intervalDomain.integral
          (intervalDomainLpEnergyWeightedTimeTerm pExp u s))
    (hPDEIntegral :
      intervalDomain.integral
          (intervalDomainLpEnergyWeightedTimeTerm pExp u t) =
        intervalDomainLpDiffusionIntegral pExp u t -
          params.χ₀ * intervalDomainLpChemotaxisIntegral params pExp u v t +
          intervalDomainLpLogisticIntegral params pExp u t)
    (hIBP :
      intervalDomainLpDiffusionIntegral pExp u t =
        intervalDomainNeumannBoundaryTerm
            (intervalDomainLpDiffusionTest pExp u t) (u t) -
          intervalDomainLpDiffusionDissipation pExp u t)
    (hDiffusionCoercive :
      A * intervalDomainLpWeightedGradientDissipation pExp u t ≤
        intervalDomainLpDiffusionDissipation pExp u t)
    (hCrossControl :
      -params.χ₀ * intervalDomainLpChemotaxisIntegral params pExp u v t ≤
        chiBound *
          intervalDomain.crossDiffusionEnergyTerm params pExp (u t) (v t)) :
    ∃ Ceps,
      (1 / pExp) *
          deriv (fun τ => intervalDomainLpEnergy pExp u τ) t +
        A * intervalDomainLpWeightedGradientDissipation pExp u t ≤
          chiBound *
              (eps * intervalDomainLpWeightedGradientDissipation pExp u t +
                Ceps *
                  intervalDomain.integral
                    (fun x => (u t x) ^ (pExp + rho))) +
            intervalDomainLpLogisticIntegral params pExp u t := by
  obtain ⟨Ceps, hCeps⟩ :=
    CrossDiffusionBootstrapEstimate.bound hcross heps hpExp ht0 htT
  refine ⟨Ceps, ?_⟩
  have hpExp_ne : pExp ≠ 0 := by linarith
  have hbasic :=
    intervalDomain_lp_energy_gradient_inequality_of_frontiers
      (params := params) (T := T) (pExp := pExp) (A := A)
      (chiBound := chiBound) (t := t) (u := u) (v := v)
      hpExp_ne ht0 htT hLpTime hPDEIntegral hIBP
      hDiffusionCoercive hCrossControl
  have hCeps' :
      intervalDomain.crossDiffusionEnergyTerm params pExp (u t) (v t) ≤
        eps * intervalDomainLpWeightedGradientDissipation pExp u t +
          Ceps *
            intervalDomain.integral (fun x => (u t x) ^ (pExp + rho)) := by
    simpa [intervalDomainLpWeightedGradientDissipation] using hCeps
  have hscaled :=
    mul_le_mul_of_nonneg_left hCeps' hchiBound
  linarith

/-- A concrete Young-absorption coefficient: choosing
`eps = A / (2 * (chiBound + 1))` makes the scaled cross term at most half of
the available diffusion coefficient. -/
theorem intervalDomain_young_absorption_coefficient_half
    {A chiBound : ℝ} (hA : 0 < A) (hchiBound : 0 ≤ chiBound) :
    chiBound * (A / (2 * (chiBound + 1))) ≤ A / 2 := by
  have hchi1_pos : 0 < chiBound + 1 := by linarith
  have hden_pos : 0 < 2 * (chiBound + 1) := by positivity
  have hratio : chiBound / (chiBound + 1) ≤ 1 := by
    rw [div_le_one hchi1_pos]
    linarith
  have hA2_nonneg : 0 ≤ A / 2 := by positivity
  have heq :
      chiBound * (A / (2 * (chiBound + 1))) =
        (A / 2) * (chiBound / (chiBound + 1)) := by
    field_simp [ne_of_gt hchi1_pos, ne_of_gt hden_pos]
  calc
    chiBound * (A / (2 * (chiBound + 1)))
        = (A / 2) * (chiBound / (chiBound + 1)) := heq
    _ ≤ (A / 2) * 1 :=
        mul_le_mul_of_nonneg_left hratio hA2_nonneg
    _ = A / 2 := by ring

/-- After the GN/Young cross-diffusion estimate has supplied an `eps`-small
weighted-gradient term, it can be absorbed into the dissipative left-hand side.

The estimate `hCrossGNYoung` is intentionally a named hypothesis: deriving it
from `gagliardoNirenberg_interval` and the interval-domain chemotaxis structure
is the current B3 analytic frontier. -/
theorem intervalDomain_lp_energy_cross_bootstrap_absorbed_of_frontiers
    {params : CM2Params} {T rho pExp eps A chiBound t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hpExp : 1 < pExp) (heps : 0 < eps) (hchiBound : 0 ≤ chiBound)
    (ht0 : 0 < t) (htT : t < T)
    (hCrossGNYoung :
      CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hLpTime : ∀ s, 0 < s → s < T →
      deriv (fun τ => intervalDomainLpEnergy pExp u τ) s =
        pExp * intervalDomain.integral
          (intervalDomainLpEnergyWeightedTimeTerm pExp u s))
    (hPDEIntegral :
      intervalDomain.integral
          (intervalDomainLpEnergyWeightedTimeTerm pExp u t) =
        intervalDomainLpDiffusionIntegral pExp u t -
          params.χ₀ * intervalDomainLpChemotaxisIntegral params pExp u v t +
          intervalDomainLpLogisticIntegral params pExp u t)
    (hIBP :
      intervalDomainLpDiffusionIntegral pExp u t =
        intervalDomainNeumannBoundaryTerm
            (intervalDomainLpDiffusionTest pExp u t) (u t) -
          intervalDomainLpDiffusionDissipation pExp u t)
    (hDiffusionCoercive :
      A * intervalDomainLpWeightedGradientDissipation pExp u t ≤
        intervalDomainLpDiffusionDissipation pExp u t)
    (hCrossControl :
      -params.χ₀ * intervalDomainLpChemotaxisIntegral params pExp u v t ≤
        chiBound *
          intervalDomain.crossDiffusionEnergyTerm params pExp (u t) (v t))
    (habsorb : chiBound * eps ≤ A) :
    ∃ Ceps,
      0 ≤ A - chiBound * eps ∧
      (1 / pExp) *
          deriv (fun τ => intervalDomainLpEnergy pExp u τ) t +
        (A - chiBound * eps) *
          intervalDomainLpWeightedGradientDissipation pExp u t ≤
          chiBound * Ceps *
              intervalDomain.integral
                (fun x => (u t x) ^ (pExp + rho)) +
            intervalDomainLpLogisticIntegral params pExp u t := by
  obtain ⟨Ceps, hineq⟩ :=
    intervalDomain_lp_energy_cross_bootstrap_inequality_of_frontiers
      (params := params) (T := T) (rho := rho) (pExp := pExp)
      (eps := eps) (A := A) (chiBound := chiBound) (t := t)
      (u := u) (v := v) hpExp heps hchiBound ht0 htT
      hCrossGNYoung hLpTime hPDEIntegral hIBP
      hDiffusionCoercive hCrossControl
  refine ⟨Ceps, ?_, ?_⟩
  · linarith
  · set Y :=
      (1 / pExp) *
        deriv (fun τ => intervalDomainLpEnergy pExp u τ) t
    set G := intervalDomainLpWeightedGradientDissipation pExp u t
    set Z :=
      intervalDomain.integral (fun x => (u t x) ^ (pExp + rho))
    set R := intervalDomainLpLogisticIntegral params pExp u t
    change Y + A * G ≤ chiBound * (eps * G + Ceps * Z) + R at hineq
    calc
      Y + (A - chiBound * eps) * G
          = Y + A * G - chiBound * (eps * G) := by ring
      _ ≤ chiBound * (eps * G + Ceps * Z) + R -
            chiBound * (eps * G) := by
          linarith
      _ = chiBound * Ceps * Z + R := by ring

/-- Closed derivative bound after cross-diffusion absorption and an explicit
upper bound on the logistic contribution.

The two remaining hypotheses are semantic frontiers, not hidden axioms:
`hLogisticUpper` is the lower-order logistic estimate, and `hDissNonneg`
is the nonnegativity needed to drop the absorbed gradient term from the left. -/
theorem intervalDomain_lp_energy_closed_derivative_bound_of_frontiers
    {params : CM2Params} {T rho pExp eps A chiBound B L_const t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hpExp : 1 < pExp) (heps : 0 < eps) (hchiBound : 0 ≤ chiBound)
    (ht0 : 0 < t) (htT : t < T)
    (hCrossGNYoung :
      CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hLpTime : ∀ s, 0 < s → s < T →
      deriv (fun τ => intervalDomainLpEnergy pExp u τ) s =
        pExp * intervalDomain.integral
          (intervalDomainLpEnergyWeightedTimeTerm pExp u s))
    (hPDEIntegral :
      intervalDomain.integral
          (intervalDomainLpEnergyWeightedTimeTerm pExp u t) =
        intervalDomainLpDiffusionIntegral pExp u t -
          params.χ₀ * intervalDomainLpChemotaxisIntegral params pExp u v t +
          intervalDomainLpLogisticIntegral params pExp u t)
    (hIBP :
      intervalDomainLpDiffusionIntegral pExp u t =
        intervalDomainNeumannBoundaryTerm
            (intervalDomainLpDiffusionTest pExp u t) (u t) -
          intervalDomainLpDiffusionDissipation pExp u t)
    (hDiffusionCoercive :
      A * intervalDomainLpWeightedGradientDissipation pExp u t ≤
        intervalDomainLpDiffusionDissipation pExp u t)
    (hCrossControl :
      -params.χ₀ * intervalDomainLpChemotaxisIntegral params pExp u v t ≤
        chiBound *
          intervalDomain.crossDiffusionEnergyTerm params pExp (u t) (v t))
    (habsorb : chiBound * eps ≤ A)
    (hLogisticUpper :
      intervalDomainLpLogisticIntegral params pExp u t ≤
        B * intervalDomainLpEnergy pExp u t + L_const)
    (hDissNonneg :
      0 ≤
        (A - chiBound * eps) *
          intervalDomainLpWeightedGradientDissipation pExp u t) :
    ∃ Ceps,
      (1 / pExp) *
          deriv (fun τ => intervalDomainLpEnergy pExp u τ) t ≤
        chiBound * Ceps *
            intervalDomain.integral (fun x => (u t x) ^ (pExp + rho)) +
          B * intervalDomainLpEnergy pExp u t + L_const := by
  obtain ⟨Ceps, _hcoef_nonneg, habsorbed⟩ :=
    intervalDomain_lp_energy_cross_bootstrap_absorbed_of_frontiers
      (params := params) (T := T) (rho := rho) (pExp := pExp)
      (eps := eps) (A := A) (chiBound := chiBound) (t := t)
      (u := u) (v := v) hpExp heps hchiBound ht0 htT
      hCrossGNYoung hLpTime hPDEIntegral hIBP
      hDiffusionCoercive hCrossControl habsorb
  refine ⟨Ceps, ?_⟩
  linarith

/-- Pointwise derivative bound with all lower-order terms displayed.

Compared with `intervalDomain_lp_energy_closed_derivative_bound_of_frontiers`,
this version takes the cross-diffusion GN/Young constant for the current time
slice explicitly and returns the exact lower-order right-hand side
`p * (chi*Ccross*Z + B*Y + L)`. -/
theorem intervalDomain_lp_energy_derivative_le_explicit_lower_terms_of_frontiers
    {params : CM2Params} {T rho pExp eps A chiBound B L_const Ccross t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hpExp : 1 < pExp) (hchiBound : 0 ≤ chiBound)
    (ht0 : 0 < t) (htT : t < T)
    (hLpTime : ∀ s, 0 < s → s < T →
      deriv (fun τ => intervalDomainLpEnergy pExp u τ) s =
        pExp * intervalDomain.integral
          (intervalDomainLpEnergyWeightedTimeTerm pExp u s))
    (hPDEIntegral :
      intervalDomain.integral
          (intervalDomainLpEnergyWeightedTimeTerm pExp u t) =
        intervalDomainLpDiffusionIntegral pExp u t -
          params.χ₀ * intervalDomainLpChemotaxisIntegral params pExp u v t +
          intervalDomainLpLogisticIntegral params pExp u t)
    (hIBP :
      intervalDomainLpDiffusionIntegral pExp u t =
        intervalDomainNeumannBoundaryTerm
            (intervalDomainLpDiffusionTest pExp u t) (u t) -
          intervalDomainLpDiffusionDissipation pExp u t)
    (hDiffusionCoercive :
      A * intervalDomainLpWeightedGradientDissipation pExp u t ≤
        intervalDomainLpDiffusionDissipation pExp u t)
    (hCrossControl :
      -params.χ₀ * intervalDomainLpChemotaxisIntegral params pExp u v t ≤
        chiBound *
          intervalDomain.crossDiffusionEnergyTerm params pExp (u t) (v t))
    (hCrossGNYoungAt :
      intervalDomain.crossDiffusionEnergyTerm params pExp (u t) (v t) ≤
        eps * intervalDomainLpWeightedGradientDissipation pExp u t +
          Ccross *
            intervalDomain.integral (fun x => (u t x) ^ (pExp + rho)))
    (hLogisticUpper :
      intervalDomainLpLogisticIntegral params pExp u t ≤
        B * intervalDomainLpEnergy pExp u t + L_const)
    (hDissNonneg :
      0 ≤
        (A - chiBound * eps) *
          intervalDomainLpWeightedGradientDissipation pExp u t) :
    deriv (fun τ => intervalDomainLpEnergy pExp u τ) t ≤
      pExp *
        (chiBound * Ccross *
            intervalDomain.integral (fun x => (u t x) ^ (pExp + rho)) +
          B * intervalDomainLpEnergy pExp u t + L_const) := by
  have hpExp_ne : pExp ≠ 0 := by linarith
  have hpExp_nonneg : 0 ≤ pExp := by linarith
  have hbasic :=
    intervalDomain_lp_energy_gradient_inequality_of_frontiers
      (params := params) (T := T) (pExp := pExp) (A := A)
      (chiBound := chiBound) (t := t) (u := u) (v := v)
      hpExp_ne ht0 htT hLpTime hPDEIntegral hIBP
      hDiffusionCoercive hCrossControl
  have hscaled :=
    mul_le_mul_of_nonneg_left hCrossGNYoungAt hchiBound
  set Y :=
    (1 / pExp) *
      deriv (fun τ => intervalDomainLpEnergy pExp u τ) t
  set G := intervalDomainLpWeightedGradientDissipation pExp u t
  set Z := intervalDomain.integral (fun x => (u t x) ^ (pExp + rho))
  set E := intervalDomainLpEnergy pExp u t
  set R := intervalDomainLpLogisticIntegral params pExp u t
  have hpre :
      Y + A * G ≤ chiBound * (eps * G + Ccross * Z) + R := by
    change
      Y + A * G ≤
        chiBound *
          intervalDomain.crossDiffusionEnergyTerm params pExp (u t) (v t) +
          R at hbasic
    change
      chiBound *
          intervalDomain.crossDiffusionEnergyTerm params pExp (u t) (v t) ≤
        chiBound * (eps * G + Ccross * Z) at hscaled
    linarith
  have habsorbed :
      Y + (A - chiBound * eps) * G ≤ chiBound * Ccross * Z + R := by
    calc
      Y + (A - chiBound * eps) * G
          = Y + A * G - chiBound * (eps * G) := by ring
      _ ≤ chiBound * (eps * G + Ccross * Z) + R -
            chiBound * (eps * G) := by
          linarith
      _ = chiBound * Ccross * Z + R := by ring
  have hLogisticUpper' : R ≤ B * E + L_const := by
    simpa [E, R] using hLogisticUpper
  have hclosed :
      Y ≤ chiBound * Ccross * Z + B * E + L_const := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hclosed hpExp_nonneg
  calc
    deriv (fun τ => intervalDomainLpEnergy pExp u τ) t
        = pExp * Y := by
          dsimp [Y]
          field_simp [hpExp_ne]
    _ ≤ pExp * (chiBound * Ccross * Z + B * E + L_const) := hmul
    _ =
        pExp *
          (chiBound * Ccross *
              intervalDomain.integral (fun x => (u t x) ^ (pExp + rho)) +
            B * intervalDomainLpEnergy pExp u t + L_const) := by
          simp [Z, E]

/-- Time-family exact lower-order derivative bound for the absolute Lp energy. -/
theorem intervalDomain_lp_abs_energy_derivative_le_explicit_lower_terms_family_of_frontiers
    {params : CM2Params} {T rho pExp eps A chiBound B L_const Ccross : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hpExp : 1 < pExp) (hchiBound : 0 ≤ chiBound)
    (hLpTime : ∀ s, 0 < s → s < T →
      deriv (fun τ => intervalDomainLpEnergy pExp u τ) s =
        pExp * intervalDomain.integral
          (intervalDomainLpEnergyWeightedTimeTerm pExp u s))
    (hPDEIntegral :
      ∀ t, 0 < t → t < T →
        intervalDomain.integral
            (intervalDomainLpEnergyWeightedTimeTerm pExp u t) =
          intervalDomainLpDiffusionIntegral pExp u t -
            params.χ₀ * intervalDomainLpChemotaxisIntegral params pExp u v t +
            intervalDomainLpLogisticIntegral params pExp u t)
    (hIBP :
      ∀ t, 0 < t → t < T →
        intervalDomainLpDiffusionIntegral pExp u t =
          intervalDomainNeumannBoundaryTerm
              (intervalDomainLpDiffusionTest pExp u t) (u t) -
            intervalDomainLpDiffusionDissipation pExp u t)
    (hDiffusionCoercive :
      ∀ t, 0 < t → t < T →
        A * intervalDomainLpWeightedGradientDissipation pExp u t ≤
          intervalDomainLpDiffusionDissipation pExp u t)
    (hCrossControl :
      ∀ t, 0 < t → t < T →
        -params.χ₀ * intervalDomainLpChemotaxisIntegral params pExp u v t ≤
          chiBound *
            intervalDomain.crossDiffusionEnergyTerm params pExp (u t) (v t))
    (hCrossGNYoungAt :
      ∀ t, 0 < t → t < T →
        intervalDomain.crossDiffusionEnergyTerm params pExp (u t) (v t) ≤
          eps * intervalDomainLpWeightedGradientDissipation pExp u t +
            Ccross *
              intervalDomain.integral (fun x => (u t x) ^ (pExp + rho)))
    (hLogisticUpper :
      ∀ t, 0 < t → t < T →
        intervalDomainLpLogisticIntegral params pExp u t ≤
          B * intervalDomainLpEnergy pExp u t + L_const)
    (hDissNonneg :
      ∀ t, 0 < t → t < T →
        0 ≤
          (A - chiBound * eps) *
            intervalDomainLpWeightedGradientDissipation pExp u t) :
    ∀ t, 0 < t → t < T →
      deriv (fun τ => intervalDomainLpAbsEnergy pExp u τ) t ≤
        pExp *
          (chiBound * Ccross *
              intervalDomain.integral (fun x => (u t x) ^ (pExp + rho)) +
            B * intervalDomainLpAbsEnergy pExp u t + L_const) := by
  intro t ht0 htT
  have hpoint :=
    intervalDomain_lp_energy_derivative_le_explicit_lower_terms_of_frontiers
      (params := params) (T := T) (rho := rho) (pExp := pExp)
      (eps := eps) (A := A) (chiBound := chiBound) (B := B)
      (L_const := L_const) (Ccross := Ccross) (t := t)
      (u := u) (v := v) hpExp hchiBound ht0 htT hLpTime
      (hPDEIntegral t ht0 htT) (hIBP t ht0 htT)
      (hDiffusionCoercive t ht0 htT) (hCrossControl t ht0 htT)
      (hCrossGNYoungAt t ht0 htT) (hLogisticUpper t ht0 htT)
      (hDissNonneg t ht0 htT)
  simpa [intervalDomainLpAbsEnergy, intervalDomainLpEnergy] using hpoint

/-- Pointwise Gronwall-ready derivative bound with an explicit cross-diffusion
constant.

This is the last algebraic step after absorption: once the GN/Young estimate
has supplied the displayed `Ccross` and the remaining lower-order terms are
bounded by the constant `C`, the actual derivative of `∫ |u|^p` is bounded by
`C`.  The hypotheses named `hCrossGNYoungAt` and `hRhsConstant` are the honest
analytic frontiers for this final closure. -/
theorem intervalDomain_lp_energy_derivative_le_constant_of_explicit_cross_bound
    {params : CM2Params} {T rho pExp eps A chiBound B L_const Ccross C t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hpExp : 1 < pExp) (hchiBound : 0 ≤ chiBound)
    (ht0 : 0 < t) (htT : t < T)
    (hLpTime : ∀ s, 0 < s → s < T →
      deriv (fun τ => intervalDomainLpEnergy pExp u τ) s =
        pExp * intervalDomain.integral
          (intervalDomainLpEnergyWeightedTimeTerm pExp u s))
    (hPDEIntegral :
      intervalDomain.integral
          (intervalDomainLpEnergyWeightedTimeTerm pExp u t) =
        intervalDomainLpDiffusionIntegral pExp u t -
          params.χ₀ * intervalDomainLpChemotaxisIntegral params pExp u v t +
          intervalDomainLpLogisticIntegral params pExp u t)
    (hIBP :
      intervalDomainLpDiffusionIntegral pExp u t =
        intervalDomainNeumannBoundaryTerm
            (intervalDomainLpDiffusionTest pExp u t) (u t) -
          intervalDomainLpDiffusionDissipation pExp u t)
    (hDiffusionCoercive :
      A * intervalDomainLpWeightedGradientDissipation pExp u t ≤
        intervalDomainLpDiffusionDissipation pExp u t)
    (hCrossControl :
      -params.χ₀ * intervalDomainLpChemotaxisIntegral params pExp u v t ≤
        chiBound *
          intervalDomain.crossDiffusionEnergyTerm params pExp (u t) (v t))
    (hCrossGNYoungAt :
      intervalDomain.crossDiffusionEnergyTerm params pExp (u t) (v t) ≤
        eps * intervalDomainLpWeightedGradientDissipation pExp u t +
          Ccross *
            intervalDomain.integral (fun x => (u t x) ^ (pExp + rho)))
    (hLogisticUpper :
      intervalDomainLpLogisticIntegral params pExp u t ≤
        B * intervalDomainLpEnergy pExp u t + L_const)
    (hDissNonneg :
      0 ≤
        (A - chiBound * eps) *
          intervalDomainLpWeightedGradientDissipation pExp u t)
    (hRhsConstant :
      pExp *
          (chiBound * Ccross *
              intervalDomain.integral (fun x => (u t x) ^ (pExp + rho)) +
            B * intervalDomainLpEnergy pExp u t + L_const) ≤ C) :
    deriv (fun τ => intervalDomainLpEnergy pExp u τ) t ≤ C := by
  have hpExp_ne : pExp ≠ 0 := by linarith
  have hpExp_nonneg : 0 ≤ pExp := by linarith
  have hbasic :=
    intervalDomain_lp_energy_gradient_inequality_of_frontiers
      (params := params) (T := T) (pExp := pExp) (A := A)
      (chiBound := chiBound) (t := t) (u := u) (v := v)
      hpExp_ne ht0 htT hLpTime hPDEIntegral hIBP
      hDiffusionCoercive hCrossControl
  have hscaled :=
    mul_le_mul_of_nonneg_left hCrossGNYoungAt hchiBound
  set Y :=
    (1 / pExp) *
      deriv (fun τ => intervalDomainLpEnergy pExp u τ) t
  set G := intervalDomainLpWeightedGradientDissipation pExp u t
  set Z := intervalDomain.integral (fun x => (u t x) ^ (pExp + rho))
  set E := intervalDomainLpEnergy pExp u t
  set R := intervalDomainLpLogisticIntegral params pExp u t
  have hpre :
      Y + A * G ≤ chiBound * (eps * G + Ccross * Z) + R := by
    change
      Y + A * G ≤
        chiBound *
          intervalDomain.crossDiffusionEnergyTerm params pExp (u t) (v t) +
          R at hbasic
    change
      chiBound *
          intervalDomain.crossDiffusionEnergyTerm params pExp (u t) (v t) ≤
        chiBound * (eps * G + Ccross * Z) at hscaled
    linarith
  have habsorbed :
      Y + (A - chiBound * eps) * G ≤ chiBound * Ccross * Z + R := by
    calc
      Y + (A - chiBound * eps) * G
          = Y + A * G - chiBound * (eps * G) := by ring
      _ ≤ chiBound * (eps * G + Ccross * Z) + R -
            chiBound * (eps * G) := by
          linarith
      _ = chiBound * Ccross * Z + R := by ring
  have hLogisticUpper' : R ≤ B * E + L_const := by
    simpa [E, R] using hLogisticUpper
  have hclosed :
      Y ≤ chiBound * Ccross * Z + B * E + L_const := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hclosed hpExp_nonneg
  calc
    deriv (fun τ => intervalDomainLpEnergy pExp u τ) t
        = pExp * Y := by
          dsimp [Y]
          field_simp [hpExp_ne]
    _ ≤
        pExp * (chiBound * Ccross * Z + B * E + L_const) := hmul
    _ ≤ C := by
      simpa [Z, E] using hRhsConstant

/-- Time-family version of
`intervalDomain_lp_energy_derivative_le_constant_of_explicit_cross_bound`.

The conclusion is the exact Gronwall input for the absolute Lp energy:
`d/dt ∫ |u|^p <= C` on `(0,T)`. -/
theorem intervalDomain_lp_abs_energy_derivative_le_constant_family_of_frontiers
    {params : CM2Params} {T rho pExp eps A chiBound B L_const Ccross C : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hpExp : 1 < pExp) (hchiBound : 0 ≤ chiBound)
    (hLpTime : ∀ s, 0 < s → s < T →
      deriv (fun τ => intervalDomainLpEnergy pExp u τ) s =
        pExp * intervalDomain.integral
          (intervalDomainLpEnergyWeightedTimeTerm pExp u s))
    (hPDEIntegral :
      ∀ t, 0 < t → t < T →
        intervalDomain.integral
            (intervalDomainLpEnergyWeightedTimeTerm pExp u t) =
          intervalDomainLpDiffusionIntegral pExp u t -
            params.χ₀ * intervalDomainLpChemotaxisIntegral params pExp u v t +
            intervalDomainLpLogisticIntegral params pExp u t)
    (hIBP :
      ∀ t, 0 < t → t < T →
        intervalDomainLpDiffusionIntegral pExp u t =
          intervalDomainNeumannBoundaryTerm
              (intervalDomainLpDiffusionTest pExp u t) (u t) -
            intervalDomainLpDiffusionDissipation pExp u t)
    (hDiffusionCoercive :
      ∀ t, 0 < t → t < T →
        A * intervalDomainLpWeightedGradientDissipation pExp u t ≤
          intervalDomainLpDiffusionDissipation pExp u t)
    (hCrossControl :
      ∀ t, 0 < t → t < T →
        -params.χ₀ * intervalDomainLpChemotaxisIntegral params pExp u v t ≤
          chiBound *
            intervalDomain.crossDiffusionEnergyTerm params pExp (u t) (v t))
    (hCrossGNYoungAt :
      ∀ t, 0 < t → t < T →
        intervalDomain.crossDiffusionEnergyTerm params pExp (u t) (v t) ≤
          eps * intervalDomainLpWeightedGradientDissipation pExp u t +
            Ccross *
              intervalDomain.integral (fun x => (u t x) ^ (pExp + rho)))
    (hLogisticUpper :
      ∀ t, 0 < t → t < T →
        intervalDomainLpLogisticIntegral params pExp u t ≤
          B * intervalDomainLpEnergy pExp u t + L_const)
    (hDissNonneg :
      ∀ t, 0 < t → t < T →
        0 ≤
          (A - chiBound * eps) *
            intervalDomainLpWeightedGradientDissipation pExp u t)
    (hRhsConstant :
      ∀ t, 0 < t → t < T →
        pExp *
            (chiBound * Ccross *
                intervalDomain.integral (fun x => (u t x) ^ (pExp + rho)) +
              B * intervalDomainLpEnergy pExp u t + L_const) ≤ C) :
    ∀ t, 0 < t → t < T →
      deriv (fun τ => intervalDomainLpAbsEnergy pExp u τ) t ≤ C := by
  intro t ht0 htT
  have hpoint :=
    intervalDomain_lp_energy_derivative_le_constant_of_explicit_cross_bound
      (params := params) (T := T) (rho := rho) (pExp := pExp)
      (eps := eps) (A := A) (chiBound := chiBound) (B := B)
      (L_const := L_const) (Ccross := Ccross) (C := C) (t := t)
      (u := u) (v := v) hpExp hchiBound ht0 htT hLpTime
      (hPDEIntegral t ht0 htT) (hIBP t ht0 htT)
      (hDiffusionCoercive t ht0 htT) (hCrossControl t ht0 htT)
      (hCrossGNYoungAt t ht0 htT)
      (hLogisticUpper t ht0 htT) (hDissNonneg t ht0 htT)
      (hRhsConstant t ht0 htT)
  simpa [intervalDomainLpAbsEnergy, intervalDomainLpEnergy] using hpoint

/-- Pointwise Gronwall form with an explicit lower-order term.

This packages the already-absorbed PDE energy estimate as
`Y'(t) <= Cgr * (Y(t) + lower)`.  The hypothesis `hRhsGronwall` is exactly the
remaining analytic estimate that turns the next-power and logistic terms into
the chosen lower-order quantity. -/
theorem intervalDomain_lp_energy_derivative_le_energy_plus_lower_of_frontiers
    {params : CM2Params} {T rho pExp eps A chiBound B L_const Ccross Cgr lower t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hpExp : 1 < pExp) (hchiBound : 0 ≤ chiBound)
    (ht0 : 0 < t) (htT : t < T)
    (hLpTime : ∀ s, 0 < s → s < T →
      deriv (fun τ => intervalDomainLpEnergy pExp u τ) s =
        pExp * intervalDomain.integral
          (intervalDomainLpEnergyWeightedTimeTerm pExp u s))
    (hPDEIntegral :
      intervalDomain.integral
          (intervalDomainLpEnergyWeightedTimeTerm pExp u t) =
        intervalDomainLpDiffusionIntegral pExp u t -
          params.χ₀ * intervalDomainLpChemotaxisIntegral params pExp u v t +
          intervalDomainLpLogisticIntegral params pExp u t)
    (hIBP :
      intervalDomainLpDiffusionIntegral pExp u t =
        intervalDomainNeumannBoundaryTerm
            (intervalDomainLpDiffusionTest pExp u t) (u t) -
          intervalDomainLpDiffusionDissipation pExp u t)
    (hDiffusionCoercive :
      A * intervalDomainLpWeightedGradientDissipation pExp u t ≤
        intervalDomainLpDiffusionDissipation pExp u t)
    (hCrossControl :
      -params.χ₀ * intervalDomainLpChemotaxisIntegral params pExp u v t ≤
        chiBound *
          intervalDomain.crossDiffusionEnergyTerm params pExp (u t) (v t))
    (hCrossGNYoungAt :
      intervalDomain.crossDiffusionEnergyTerm params pExp (u t) (v t) ≤
        eps * intervalDomainLpWeightedGradientDissipation pExp u t +
          Ccross *
            intervalDomain.integral (fun x => (u t x) ^ (pExp + rho)))
    (hLogisticUpper :
      intervalDomainLpLogisticIntegral params pExp u t ≤
        B * intervalDomainLpEnergy pExp u t + L_const)
    (hDissNonneg :
      0 ≤
        (A - chiBound * eps) *
          intervalDomainLpWeightedGradientDissipation pExp u t)
    (hRhsGronwall :
      pExp *
          (chiBound * Ccross *
              intervalDomain.integral (fun x => (u t x) ^ (pExp + rho)) +
            B * intervalDomainLpEnergy pExp u t + L_const) ≤
        Cgr * (intervalDomainLpEnergy pExp u t + lower)) :
    deriv (fun τ => intervalDomainLpEnergy pExp u τ) t ≤
      Cgr * (intervalDomainLpEnergy pExp u t + lower) := by
  exact
    intervalDomain_lp_energy_derivative_le_constant_of_explicit_cross_bound
      (params := params) (T := T) (rho := rho) (pExp := pExp)
      (eps := eps) (A := A) (chiBound := chiBound) (B := B)
      (L_const := L_const) (Ccross := Ccross)
      (C := Cgr * (intervalDomainLpEnergy pExp u t + lower)) (t := t)
      (u := u) (v := v) hpExp hchiBound ht0 htT hLpTime
      hPDEIntegral hIBP hDiffusionCoercive hCrossControl
      hCrossGNYoungAt hLogisticUpper hDissNonneg hRhsGronwall

/-- Time-family Gronwall form for the absolute Lp energy:
`d/dt ∫ |u|^p <= Cgr * (∫ |u|^p + lower t)`.

This is the interface meant for downstream Gronwall arguments; all PDE-side
frontiers remain explicit and named. -/
theorem intervalDomain_lp_abs_energy_derivative_le_energy_plus_lower_family_of_frontiers
    {params : CM2Params} {T rho pExp eps A chiBound B L_const Ccross Cgr : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ} {lower : ℝ → ℝ}
    (hpExp : 1 < pExp) (hchiBound : 0 ≤ chiBound)
    (hLpTime : ∀ s, 0 < s → s < T →
      deriv (fun τ => intervalDomainLpEnergy pExp u τ) s =
        pExp * intervalDomain.integral
          (intervalDomainLpEnergyWeightedTimeTerm pExp u s))
    (hPDEIntegral :
      ∀ t, 0 < t → t < T →
        intervalDomain.integral
            (intervalDomainLpEnergyWeightedTimeTerm pExp u t) =
          intervalDomainLpDiffusionIntegral pExp u t -
            params.χ₀ * intervalDomainLpChemotaxisIntegral params pExp u v t +
            intervalDomainLpLogisticIntegral params pExp u t)
    (hIBP :
      ∀ t, 0 < t → t < T →
        intervalDomainLpDiffusionIntegral pExp u t =
          intervalDomainNeumannBoundaryTerm
              (intervalDomainLpDiffusionTest pExp u t) (u t) -
            intervalDomainLpDiffusionDissipation pExp u t)
    (hDiffusionCoercive :
      ∀ t, 0 < t → t < T →
        A * intervalDomainLpWeightedGradientDissipation pExp u t ≤
          intervalDomainLpDiffusionDissipation pExp u t)
    (hCrossControl :
      ∀ t, 0 < t → t < T →
        -params.χ₀ * intervalDomainLpChemotaxisIntegral params pExp u v t ≤
          chiBound *
            intervalDomain.crossDiffusionEnergyTerm params pExp (u t) (v t))
    (hCrossGNYoungAt :
      ∀ t, 0 < t → t < T →
        intervalDomain.crossDiffusionEnergyTerm params pExp (u t) (v t) ≤
          eps * intervalDomainLpWeightedGradientDissipation pExp u t +
            Ccross *
              intervalDomain.integral (fun x => (u t x) ^ (pExp + rho)))
    (hLogisticUpper :
      ∀ t, 0 < t → t < T →
        intervalDomainLpLogisticIntegral params pExp u t ≤
          B * intervalDomainLpEnergy pExp u t + L_const)
    (hDissNonneg :
      ∀ t, 0 < t → t < T →
        0 ≤
          (A - chiBound * eps) *
            intervalDomainLpWeightedGradientDissipation pExp u t)
    (hRhsGronwall :
      ∀ t, 0 < t → t < T →
        pExp *
            (chiBound * Ccross *
                intervalDomain.integral (fun x => (u t x) ^ (pExp + rho)) +
              B * intervalDomainLpEnergy pExp u t + L_const) ≤
          Cgr * (intervalDomainLpEnergy pExp u t + lower t)) :
    ∀ t, 0 < t → t < T →
      deriv (fun τ => intervalDomainLpAbsEnergy pExp u τ) t ≤
        Cgr * (intervalDomainLpAbsEnergy pExp u t + lower t) := by
  intro t ht0 htT
  have hpoint :=
    intervalDomain_lp_energy_derivative_le_energy_plus_lower_of_frontiers
      (params := params) (T := T) (rho := rho) (pExp := pExp)
      (eps := eps) (A := A) (chiBound := chiBound) (B := B)
      (L_const := L_const) (Ccross := Ccross) (Cgr := Cgr)
      (lower := lower t) (t := t) (u := u) (v := v)
      hpExp hchiBound ht0 htT hLpTime (hPDEIntegral t ht0 htT)
      (hIBP t ht0 htT) (hDiffusionCoercive t ht0 htT)
      (hCrossControl t ht0 htT) (hCrossGNYoungAt t ht0 htT)
      (hLogisticUpper t ht0 htT) (hDissNonneg t ht0 htT)
      (hRhsGronwall t ht0 htT)
  simpa [intervalDomainLpAbsEnergy, intervalDomainLpEnergy] using hpoint

/-- A coefficient-only version of the preceding Gronwall form with the
canonical lower-order quantity `∫ u^(p+rho) + 1`.

The nonnegativity hypotheses are exactly the positivity/integral-positivity
facts needed to compare each term with the common Gronwall coefficient. -/
theorem
intervalDomain_lp_abs_energy_derivative_le_energy_plus_next_power_family_of_frontiers
    {params : CM2Params} {T rho pExp eps A chiBound B L_const Ccross Cgr : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hpExp : 1 < pExp) (hchiBound : 0 ≤ chiBound)
    (hLpTime : ∀ s, 0 < s → s < T →
      deriv (fun τ => intervalDomainLpEnergy pExp u τ) s =
        pExp * intervalDomain.integral
          (intervalDomainLpEnergyWeightedTimeTerm pExp u s))
    (hPDEIntegral :
      ∀ t, 0 < t → t < T →
        intervalDomain.integral
            (intervalDomainLpEnergyWeightedTimeTerm pExp u t) =
          intervalDomainLpDiffusionIntegral pExp u t -
            params.χ₀ * intervalDomainLpChemotaxisIntegral params pExp u v t +
            intervalDomainLpLogisticIntegral params pExp u t)
    (hIBP :
      ∀ t, 0 < t → t < T →
        intervalDomainLpDiffusionIntegral pExp u t =
          intervalDomainNeumannBoundaryTerm
              (intervalDomainLpDiffusionTest pExp u t) (u t) -
            intervalDomainLpDiffusionDissipation pExp u t)
    (hDiffusionCoercive :
      ∀ t, 0 < t → t < T →
        A * intervalDomainLpWeightedGradientDissipation pExp u t ≤
          intervalDomainLpDiffusionDissipation pExp u t)
    (hCrossControl :
      ∀ t, 0 < t → t < T →
        -params.χ₀ * intervalDomainLpChemotaxisIntegral params pExp u v t ≤
          chiBound *
            intervalDomain.crossDiffusionEnergyTerm params pExp (u t) (v t))
    (hCrossGNYoungAt :
      ∀ t, 0 < t → t < T →
        intervalDomain.crossDiffusionEnergyTerm params pExp (u t) (v t) ≤
          eps * intervalDomainLpWeightedGradientDissipation pExp u t +
            Ccross *
              intervalDomain.integral (fun x => (u t x) ^ (pExp + rho)))
    (hLogisticUpper :
      ∀ t, 0 < t → t < T →
        intervalDomainLpLogisticIntegral params pExp u t ≤
          B * intervalDomainLpEnergy pExp u t + L_const)
    (hDissNonneg :
      ∀ t, 0 < t → t < T →
        0 ≤
          (A - chiBound * eps) *
            intervalDomainLpWeightedGradientDissipation pExp u t)
    (hEnergyNonneg :
      ∀ t, 0 < t → t < T → 0 ≤ intervalDomainLpEnergy pExp u t)
    (hNextPowerNonneg :
      ∀ t, 0 < t → t < T →
        0 ≤ intervalDomain.integral (fun x => (u t x) ^ (pExp + rho)))
    (hCrossCoeff : pExp * (chiBound * Ccross) ≤ Cgr)
    (hEnergyCoeff : pExp * B ≤ Cgr)
    (hConstCoeff : pExp * L_const ≤ Cgr) :
    ∀ t, 0 < t → t < T →
      deriv (fun τ => intervalDomainLpAbsEnergy pExp u τ) t ≤
        Cgr *
          (intervalDomainLpAbsEnergy pExp u t +
            (intervalDomain.integral (fun x => (u t x) ^ (pExp + rho)) + 1)) := by
  refine
    intervalDomain_lp_abs_energy_derivative_le_energy_plus_lower_family_of_frontiers
      (params := params) (T := T) (rho := rho) (pExp := pExp)
      (eps := eps) (A := A) (chiBound := chiBound) (B := B)
      (L_const := L_const) (Ccross := Ccross) (Cgr := Cgr)
      (lower := fun t =>
        intervalDomain.integral (fun x => (u t x) ^ (pExp + rho)) + 1)
      hpExp hchiBound hLpTime hPDEIntegral hIBP hDiffusionCoercive
      hCrossControl hCrossGNYoungAt hLogisticUpper hDissNonneg ?_
  intro t ht0 htT
  set E := intervalDomainLpEnergy pExp u t
  set Z := intervalDomain.integral (fun x => (u t x) ^ (pExp + rho))
  have hE_nonneg : 0 ≤ E := by
    simpa [E] using hEnergyNonneg t ht0 htT
  have hZ_nonneg : 0 ≤ Z := by
    simpa [Z] using hNextPowerNonneg t ht0 htT
  have hcross_term :
      pExp * (chiBound * Ccross * Z) ≤ Cgr * Z := by
    calc
      pExp * (chiBound * Ccross * Z)
          = (pExp * (chiBound * Ccross)) * Z := by ring
      _ ≤ Cgr * Z := mul_le_mul_of_nonneg_right hCrossCoeff hZ_nonneg
  have henergy_term :
      pExp * (B * E) ≤ Cgr * E := by
    calc
      pExp * (B * E) = (pExp * B) * E := by ring
      _ ≤ Cgr * E := mul_le_mul_of_nonneg_right hEnergyCoeff hE_nonneg
  have hconst_term : pExp * L_const ≤ Cgr * 1 := by
    simpa using hConstCoeff
  calc
    pExp * (chiBound * Ccross * Z + B * E + L_const)
        = pExp * (chiBound * Ccross * Z) +
          pExp * (B * E) + pExp * L_const := by ring
    _ ≤ Cgr * Z + Cgr * E + Cgr * 1 := by linarith
    _ = Cgr * (E + (Z + 1)) := by ring

/-- Half of the L2 energy.  This form avoids any convention about `0^0` in
`|u|^(p-2)` when specializing the Lp identity at `p = 2`. -/
def intervalDomainL2HalfEnergy
    (u : ℝ → intervalDomain.Point → ℝ) (t : ℝ) : ℝ :=
  (1 / 2) * intervalDomain.integral (fun x => (u t x) ^ 2)

/-- Time term for the `d/dt (1/2 ∫ u^2)` identity. -/
def intervalDomainL2TimeTerm
    (u : ℝ → intervalDomain.Point → ℝ) (t : ℝ)
    (x : intervalDomain.Point) : ℝ :=
  u t x * intervalDomain.timeDeriv u t x

def intervalDomainL2DiffusionIntegral
    (u : ℝ → intervalDomain.Point → ℝ) (t : ℝ) : ℝ :=
  intervalDomain.integral
    (fun x => u t x * intervalDomain.laplacian (u t) x)

def intervalDomainL2DiffusionDissipation
    (u : ℝ → intervalDomain.Point → ℝ) (t : ℝ) : ℝ :=
  intervalDomainDerivativePairIntegral (u t) (u t)

def intervalDomainL2ChemotaxisIntegral
    (params : CM2Params) (u v : ℝ → intervalDomain.Point → ℝ)
    (t : ℝ) : ℝ :=
  intervalDomain.integral
    (fun x => u t x * intervalDomain.chemotaxisDiv params (u t) (v t) x)

def intervalDomainL2LogisticIntegral
    (params : CM2Params) (u : ℝ → intervalDomain.Point → ℝ)
    (t : ℝ) : ℝ :=
  intervalDomain.integral
    (fun x => (u t x) ^ 2 * (params.a - params.b * (u t x) ^ params.α))

/-- Pointwise L2-weighted form of the classical `u` PDE on the interior. -/
theorem intervalDomain_solution_l2_weighted_timeDeriv_eq_pde
    {params : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T) {x : intervalDomain.Point}
    (hx : x ∈ intervalDomain.inside) :
    intervalDomainL2TimeTerm u t x =
      u t x *
        (intervalDomain.laplacian (u t) x
          - params.χ₀ * intervalDomain.chemotaxisDiv params (u t) (v t) x
          + u t x * (params.a - params.b * (u t x) ^ params.α)) := by
  unfold intervalDomainL2TimeTerm
  rw [hsol.pde_u ht0 htT hx]

/-- Exact conditional `d/dt (1/2 ∫ u^2)` balance after Neumann integration by
parts. -/
theorem intervalDomain_l2_half_energy_balance_of_frontiers
    {params : CM2Params} {t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hL2Time :
      deriv (fun τ => intervalDomainL2HalfEnergy u τ) t =
        intervalDomain.integral (intervalDomainL2TimeTerm u t))
    (hPDEIntegral :
      intervalDomain.integral (intervalDomainL2TimeTerm u t) =
        intervalDomainL2DiffusionIntegral u t -
          params.χ₀ * intervalDomainL2ChemotaxisIntegral params u v t +
          intervalDomainL2LogisticIntegral params u t)
    (hIBP :
      intervalDomainL2DiffusionIntegral u t =
        intervalDomainNeumannBoundaryTerm (u t) (u t) -
          intervalDomainL2DiffusionDissipation u t) :
    deriv (fun τ => intervalDomainL2HalfEnergy u τ) t +
      intervalDomainL2DiffusionDissipation u t =
        -params.χ₀ * intervalDomainL2ChemotaxisIntegral params u v t +
          intervalDomainL2LogisticIntegral params u t := by
  have hIBP' :
      intervalDomain.integral
          (fun x => u t x * intervalDomain.laplacian (u t) x) =
        intervalDomainNeumannBoundaryTerm (u t) (u t) -
          intervalDomainDerivativePairIntegral (u t) (u t) := by
    simpa [intervalDomainL2DiffusionIntegral,
      intervalDomainL2DiffusionDissipation] using hIBP
  have hdiff :=
    intervalDomain_integrationByParts_neumann_of_boundary_identity
      (u t) (u t) hIBP'
  have hdiff_named :
      intervalDomainL2DiffusionIntegral u t =
        -intervalDomainL2DiffusionDissipation u t := by
    simpa [intervalDomainL2DiffusionIntegral,
      intervalDomainL2DiffusionDissipation] using hdiff
  calc
    deriv (fun τ => intervalDomainL2HalfEnergy u τ) t +
        intervalDomainL2DiffusionDissipation u t
        = intervalDomain.integral (intervalDomainL2TimeTerm u t) +
          intervalDomainL2DiffusionDissipation u t := by
            rw [hL2Time]
    _ =
        (intervalDomainL2DiffusionIntegral u t -
            params.χ₀ * intervalDomainL2ChemotaxisIntegral params u v t +
            intervalDomainL2LogisticIntegral params u t) +
          intervalDomainL2DiffusionDissipation u t := by
            rw [hPDEIntegral]
    _ =
        -params.χ₀ * intervalDomainL2ChemotaxisIntegral params u v t +
          intervalDomainL2LogisticIntegral params u t := by
            rw [hdiff_named]
            ring

/-- Conditional L2 energy inequality with the chemotaxis term controlled by the
cross-diffusion energy term at exponent `2`. -/
theorem intervalDomain_l2_half_energy_inequality_of_cross_control
    {params : CM2Params} {t chiBound : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hL2Time :
      deriv (fun τ => intervalDomainL2HalfEnergy u τ) t =
        intervalDomain.integral (intervalDomainL2TimeTerm u t))
    (hPDEIntegral :
      intervalDomain.integral (intervalDomainL2TimeTerm u t) =
        intervalDomainL2DiffusionIntegral u t -
          params.χ₀ * intervalDomainL2ChemotaxisIntegral params u v t +
          intervalDomainL2LogisticIntegral params u t)
    (hIBP :
      intervalDomainL2DiffusionIntegral u t =
        intervalDomainNeumannBoundaryTerm (u t) (u t) -
          intervalDomainL2DiffusionDissipation u t)
    (hCrossControl :
      -params.χ₀ * intervalDomainL2ChemotaxisIntegral params u v t ≤
        chiBound *
          intervalDomain.crossDiffusionEnergyTerm params 2 (u t) (v t)) :
    deriv (fun τ => intervalDomainL2HalfEnergy u τ) t +
      intervalDomainL2DiffusionDissipation u t ≤
        chiBound *
          intervalDomain.crossDiffusionEnergyTerm params 2 (u t) (v t) +
          intervalDomainL2LogisticIntegral params u t := by
  have hbalance :=
    intervalDomain_l2_half_energy_balance_of_frontiers
      (params := params) (t := t) (u := u) (v := v)
      hL2Time hPDEIntegral hIBP
  rw [hbalance]
  linarith

/-- L2 energy inequality after applying the cross-diffusion bootstrap estimate
at exponent `2`. -/
theorem intervalDomain_l2_half_energy_cross_bootstrap_inequality_of_frontiers
    {params : CM2Params} {T rho eps chiBound t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (heps : 0 < eps) (hchiBound : 0 ≤ chiBound)
    (ht0 : 0 < t) (htT : t < T)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hL2Time :
      deriv (fun τ => intervalDomainL2HalfEnergy u τ) t =
        intervalDomain.integral (intervalDomainL2TimeTerm u t))
    (hPDEIntegral :
      intervalDomain.integral (intervalDomainL2TimeTerm u t) =
        intervalDomainL2DiffusionIntegral u t -
          params.χ₀ * intervalDomainL2ChemotaxisIntegral params u v t +
          intervalDomainL2LogisticIntegral params u t)
    (hIBP :
      intervalDomainL2DiffusionIntegral u t =
        intervalDomainNeumannBoundaryTerm (u t) (u t) -
          intervalDomainL2DiffusionDissipation u t)
    (hCrossControl :
      -params.χ₀ * intervalDomainL2ChemotaxisIntegral params u v t ≤
        chiBound *
          intervalDomain.crossDiffusionEnergyTerm params 2 (u t) (v t)) :
    ∃ Ceps,
      deriv (fun τ => intervalDomainL2HalfEnergy u τ) t +
        intervalDomainL2DiffusionDissipation u t ≤
          chiBound *
              (eps * intervalDomainLpWeightedGradientDissipation 2 u t +
                Ceps *
                  intervalDomain.integral (fun x => (u t x) ^ (2 + rho))) +
            intervalDomainL2LogisticIntegral params u t := by
  have htwo : (1 : ℝ) < 2 := by norm_num
  obtain ⟨Ceps, hCeps⟩ :=
    CrossDiffusionBootstrapEstimate.bound
      hcross heps htwo ht0 htT
  refine ⟨Ceps, ?_⟩
  have hbasic :=
    intervalDomain_l2_half_energy_inequality_of_cross_control
      (params := params) (t := t) (chiBound := chiBound)
      (u := u) (v := v) hL2Time hPDEIntegral hIBP hCrossControl
  have hCeps' :
      intervalDomain.crossDiffusionEnergyTerm params 2 (u t) (v t) ≤
        eps * intervalDomainLpWeightedGradientDissipation 2 u t +
          Ceps * intervalDomain.integral (fun x => (u t x) ^ (2 + rho)) := by
    simpa [intervalDomainLpWeightedGradientDissipation] using hCeps
  have hscaled :=
    mul_le_mul_of_nonneg_left hCeps' hchiBound
  linarith

/-- A full Paper 2 energy inequality gives the reduced Moser step once the
time-derivative plus lower-order contribution is nonnegative.

The extra hypothesis is not a conclusion in disguise: it is precisely the
sign/dissipation fact needed to remove
`(1 / p) Y'(t) + B Y(t)` from the left-hand side of
`(1 / p)Y' + A G + B Y <= K Z + L`. -/
theorem reduced_moser_step_of_energy_and_dissipation
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T p rho A B K L_const : ℝ}
    (hA : 0 < A) (hK : 0 < K)
    (henergy : ∀ t, 0 < t → t < T →
      (1 / p) * deriv (fun τ => D.integral (fun x => (u τ x) ^ p)) t +
        A * D.integral (fun x =>
          (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
        B * D.integral (fun x => (u t x) ^ p) ≤
      K * D.integral (fun x => (u t x) ^ (p + rho)) + L_const)
    (hdiss : ∀ t, 0 < t → t < T →
      0 ≤
        (1 / p) * deriv (fun τ => D.integral (fun x => (u τ x) ^ p)) t +
          B * D.integral (fun x => (u t x) ^ p))
    (hinterp : ∀ eps > 0, ∃ Ceps, ∀ t, 0 < t → t < T →
      D.integral (fun x => (u t x) ^ (p + rho)) ≤
        eps * D.integral (fun x =>
          (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
        Ceps) :
    LpPowerBoundedBefore D (p + rho) T u := by
  refine IntervalDomainChain.lp_bootstrap_single_step_abstract
    (L_const := L_const) hA hK ?_ hinterp
  intro t ht0 htT
  have hfull := henergy t ht0 htT
  have hdrop := hdiss t ht0 htT
  linarith

/-- Convert `LpBootstrapEnergyInequality` into the step family required by the
Moser chain, under explicit dissipation and interpolation hypotheses. -/
theorem moser_step_family_of_energy_dissipation_interpolation
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T rho p0 : ℝ}
    (henergy : LpBootstrapEnergyInequality D u T rho p0)
    (hdiss : ∀ p, p0 ≤ p → ∀ A B K L_const,
      (∀ t, 0 < t → t < T →
        (1 / p) * deriv (fun τ => D.integral (fun x => (u τ x) ^ p)) t +
          A * D.integral (fun x =>
            (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
          B * D.integral (fun x => (u t x) ^ p) ≤
        K * D.integral (fun x => (u t x) ^ (p + rho)) + L_const) →
      ∀ t, 0 < t → t < T →
        0 ≤
          (1 / p) * deriv (fun τ => D.integral (fun x => (u τ x) ^ p)) t +
            B * D.integral (fun x => (u t x) ^ p))
    (hinterp : ∀ p, p0 ≤ p → ∀ eps > 0, ∃ Ceps, ∀ t, 0 < t → t < T →
      D.integral (fun x => (u t x) ^ (p + rho)) ≤
        eps * D.integral (fun x =>
          (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
        Ceps) :
    ∀ p, p0 ≤ p →
      ∃ A > 0, ∃ K > 0, ∃ L_const,
        (∀ t, 0 < t → t < T →
          A * D.integral (fun x =>
            (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) ≤
          K * D.integral (fun x => (u t x) ^ (p + rho)) + L_const) ∧
        (∀ eps > 0, ∃ Ceps, ∀ t, 0 < t → t < T →
          D.integral (fun x => (u t x) ^ (p + rho)) ≤
            eps * D.integral (fun x =>
              (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
            Ceps) := by
  intro p hp
  rcases henergy p hp with ⟨A, hA, B, _hB, K, hK, L_const, hfull⟩
  refine ⟨A, hA, K, hK, L_const, ?_, hinterp p hp⟩
  intro t ht0 htT
  have hfull_t := hfull t ht0 htT
  have hdrop_t := hdiss p hp A B K L_const hfull t ht0 htT
  linarith

/-- Convert the Paper 2 mass-gradient interpolation estimate into the
`Z <= eps * G + Ceps` interpolation interface used by the Moser step.

The extra hypotheses are the two analytic bridges not present in
`LpMassGradientInterpolationEstimate` itself:
* the chain-rule comparison from the weighted `|∇u|²` term to
  `|∇(u^(p/2))|²`;
* a uniform bound on the lower-order mass term. -/
theorem moser_interpolation_of_mass_gradient_estimate
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T p rho cGrad : ℝ}
    (hcGrad : 0 < cGrad)
    (hMG : ∀ eta > 0, ∃ Ceta,
      LpMassGradientInterpolationEstimate D (p + rho) eta Ceta T u)
    (hgrad : ∀ t, 0 < t → t < T →
      D.integral (fun x =>
          (u t x) ^ (p + rho - 2) * (D.gradNorm (u t) x) ^ 2) ≤
        cGrad * D.integral (fun x =>
          (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2))
    (hmass : ∀ Ceta, ∃ Cmass, ∀ t, 0 < t → t < T →
      Ceta * (D.integral (u t)) ^ (p + rho) ≤ Cmass) :
    ∀ eps > 0, ∃ Ceps, ∀ t, 0 < t → t < T →
      D.integral (fun x => (u t x) ^ (p + rho)) ≤
        eps * D.integral (fun x =>
          (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
        Ceps := by
  intro eps heps
  have heta_pos : 0 < eps / cGrad := div_pos heps hcGrad
  obtain ⟨Ceta, hCeta⟩ := hMG (eps / cGrad) heta_pos
  obtain ⟨Cmass, hCmass⟩ := hmass Ceta
  refine ⟨Cmass, ?_⟩
  intro t ht0 htT
  have hbound := LpMassGradientInterpolationEstimate.bound hCeta ht0 htT
  have hgrad_t := hgrad t ht0 htT
  have hmass_t := hCmass t ht0 htT
  have hcoef_nonneg : 0 ≤ eps / cGrad := div_nonneg heps.le hcGrad.le
  have hgrad_scaled :
      (eps / cGrad) *
          D.integral (fun x =>
            (u t x) ^ (p + rho - 2) * (D.gradNorm (u t) x) ^ 2) ≤
        (eps / cGrad) *
          (cGrad * D.integral (fun x =>
            (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2)) :=
    mul_le_mul_of_nonneg_left hgrad_t hcoef_nonneg
  calc
    D.integral (fun x => (u t x) ^ (p + rho))
        ≤
          (eps / cGrad) *
              D.integral (fun x =>
                (u t x) ^ (p + rho - 2) * (D.gradNorm (u t) x) ^ 2) +
            Ceta * (D.integral (u t)) ^ (p + rho) := hbound
    _ ≤
          (eps / cGrad) *
              (cGrad * D.integral (fun x =>
                (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2)) +
            Cmass := by
          linarith
    _ =
          eps * D.integral (fun x =>
            (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
            Cmass := by
          field_simp [ne_of_gt hcGrad]

/-- Moser closure from the full bootstrap energy inequality, after supplying
the two analytic facts not present in the abstract `BoundedDomainData` API:
dissipation and interpolation.  Downward Lp monotonicity is kept abstract here. -/
theorem all_exponents_of_energy_dissipation_interpolation_lpmono
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {N T rho p0 : ℝ}
    (hboot : AbstractLpBootstrapHypothesis D u N T rho p0)
    (henergy : LpBootstrapEnergyInequality D u T rho p0)
    (hdiss : ∀ p, p0 ≤ p → ∀ A B K L_const,
      (∀ t, 0 < t → t < T →
        (1 / p) * deriv (fun τ => D.integral (fun x => (u τ x) ^ p)) t +
          A * D.integral (fun x =>
            (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
          B * D.integral (fun x => (u t x) ^ p) ≤
        K * D.integral (fun x => (u t x) ^ (p + rho)) + L_const) →
      ∀ t, 0 < t → t < T →
        0 ≤
          (1 / p) * deriv (fun τ => D.integral (fun x => (u τ x) ^ p)) t +
            B * D.integral (fun x => (u t x) ^ p))
    (hinterp : ∀ p, p0 ≤ p → ∀ eps > 0, ∃ Ceps, ∀ t, 0 < t → t < T →
      D.integral (fun x => (u t x) ^ (p + rho)) ≤
        eps * D.integral (fun x =>
          (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
        Ceps)
    (hLpMono :
      ∀ {p q : ℝ}, 1 < p → p ≤ q →
        LpPowerBoundedBefore D q T u → LpPowerBoundedBefore D p T u) :
    ∀ pExp > 1, LpPowerBoundedBefore D pExp T u := by
  exact IntervalDomainMoserClosure.all_exponents_of_moser_iteration_chain
    (AbstractLpBootstrapHypothesis.rho_pos hboot)
    (AbstractLpBootstrapHypothesis.initial_lp_bound hboot)
    (moser_step_family_of_energy_dissipation_interpolation henergy hdiss hinterp)
    hLpMono

/-- Same closure as `all_exponents_of_energy_dissipation_interpolation_lpmono`,
but with the interpolation input supplied in the Paper 2 mass-gradient form. -/
theorem all_exponents_of_energy_dissipation_mass_gradient_lpmono
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {N T rho p0 : ℝ}
    (cGrad : ℝ → ℝ)
    (hboot : AbstractLpBootstrapHypothesis D u N T rho p0)
    (henergy : LpBootstrapEnergyInequality D u T rho p0)
    (hdiss : ∀ p, p0 ≤ p → ∀ A B K L_const,
      (∀ t, 0 < t → t < T →
        (1 / p) * deriv (fun τ => D.integral (fun x => (u τ x) ^ p)) t +
          A * D.integral (fun x =>
            (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
          B * D.integral (fun x => (u t x) ^ p) ≤
        K * D.integral (fun x => (u t x) ^ (p + rho)) + L_const) →
      ∀ t, 0 < t → t < T →
        0 ≤
          (1 / p) * deriv (fun τ => D.integral (fun x => (u τ x) ^ p)) t +
            B * D.integral (fun x => (u t x) ^ p))
    (hcGrad : ∀ p, p0 ≤ p → 0 < cGrad p)
    (hMG : ∀ p, p0 ≤ p → ∀ eta > 0, ∃ Ceta,
      LpMassGradientInterpolationEstimate D (p + rho) eta Ceta T u)
    (hgrad : ∀ p, p0 ≤ p → ∀ t, 0 < t → t < T →
      D.integral (fun x =>
          (u t x) ^ (p + rho - 2) * (D.gradNorm (u t) x) ^ 2) ≤
        cGrad p * D.integral (fun x =>
          (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2))
    (hmass : ∀ p, p0 ≤ p → ∀ Ceta, ∃ Cmass, ∀ t, 0 < t → t < T →
      Ceta * (D.integral (u t)) ^ (p + rho) ≤ Cmass)
    (hLpMono :
      ∀ {p q : ℝ}, 1 < p → p ≤ q →
        LpPowerBoundedBefore D q T u → LpPowerBoundedBefore D p T u) :
    ∀ pExp > 1, LpPowerBoundedBefore D pExp T u := by
  refine all_exponents_of_energy_dissipation_interpolation_lpmono
    hboot henergy hdiss ?_ hLpMono
  intro p hp
  exact moser_interpolation_of_mass_gradient_estimate
    (hcGrad p hp) (hMG p hp) (hgrad p hp) (hmass p hp)

/-- Interval-domain version of the preceding closure, using the concrete
finite-interval Lp monotonicity proved in `IntervalDomainLpMonotonicity`. -/
theorem intervalDomain_all_exponents_of_energy_dissipation_interpolation
    {u : ℝ → intervalDomain.Point → ℝ} {N T rho p0 : ℝ}
    (hboot : AbstractLpBootstrapHypothesis intervalDomain u N T rho p0)
    (henergy : LpBootstrapEnergyInequality intervalDomain u T rho p0)
    (hdiss : ∀ p, p0 ≤ p → ∀ A B K L_const,
      (∀ t, 0 < t → t < T →
        (1 / p) * deriv
            (fun τ => intervalDomain.integral (fun x => (u τ x) ^ p)) t +
          A * intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
          B * intervalDomain.integral (fun x => (u t x) ^ p) ≤
        K * intervalDomain.integral (fun x => (u t x) ^ (p + rho)) + L_const) →
      ∀ t, 0 < t → t < T →
        0 ≤
          (1 / p) * deriv
              (fun τ => intervalDomain.integral (fun x => (u τ x) ^ p)) t +
            B * intervalDomain.integral (fun x => (u t x) ^ p))
    (hinterp : ∀ p, p0 ≤ p → ∀ eps > 0, ∃ Ceps, ∀ t, 0 < t → t < T →
      intervalDomain.integral (fun x => (u t x) ^ (p + rho)) ≤
        eps * intervalDomain.integral (fun x =>
          (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
        Ceps)
    (hu_nonneg :
      ∀ t, 0 < t → t < T → ∀ x : intervalDomain.Point, 0 ≤ u t x)
    (hpow_int :
      ∀ pExp : ℝ, 1 < pExp → ∀ t, 0 < t → t < T →
        IntervalIntegrable
          (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ pExp))
          MeasureTheory.volume 0 1) :
    ∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u := by
  exact IntervalDomainLpMonotonicity.intervalDomain_all_exponents_of_moser_iteration_chain
    (AbstractLpBootstrapHypothesis.rho_pos hboot)
    (AbstractLpBootstrapHypothesis.initial_lp_bound hboot)
    (moser_step_family_of_energy_dissipation_interpolation henergy hdiss hinterp)
    hu_nonneg hpow_int

/-- Interval-domain closure with interpolation supplied in the Paper 2
mass-gradient form.  This is the current honest H1.2 front line: the remaining
work is to prove the dissipation, chain-rule gradient comparison, and mass
control hypotheses from the actual interval PDE data. -/
theorem intervalDomain_all_exponents_of_energy_dissipation_mass_gradient
    {u : ℝ → intervalDomain.Point → ℝ} {N T rho p0 : ℝ}
    (cGrad : ℝ → ℝ)
    (hboot : AbstractLpBootstrapHypothesis intervalDomain u N T rho p0)
    (henergy : LpBootstrapEnergyInequality intervalDomain u T rho p0)
    (hdiss : ∀ p, p0 ≤ p → ∀ A B K L_const,
      (∀ t, 0 < t → t < T →
        (1 / p) * deriv
            (fun τ => intervalDomain.integral (fun x => (u τ x) ^ p)) t +
          A * intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
          B * intervalDomain.integral (fun x => (u t x) ^ p) ≤
        K * intervalDomain.integral (fun x => (u t x) ^ (p + rho)) + L_const) →
      ∀ t, 0 < t → t < T →
        0 ≤
          (1 / p) * deriv
              (fun τ => intervalDomain.integral (fun x => (u τ x) ^ p)) t +
            B * intervalDomain.integral (fun x => (u t x) ^ p))
    (hcGrad : ∀ p, p0 ≤ p → 0 < cGrad p)
    (hMG : ∀ p, p0 ≤ p → ∀ eta > 0, ∃ Ceta,
      LpMassGradientInterpolationEstimate intervalDomain (p + rho) eta Ceta T u)
    (hgrad : ∀ p, p0 ≤ p → ∀ t, 0 < t → t < T →
      intervalDomain.integral (fun x =>
          (u t x) ^ (p + rho - 2) * (intervalDomain.gradNorm (u t) x) ^ 2) ≤
        cGrad p * intervalDomain.integral (fun x =>
          (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2))
    (hmass : ∀ p, p0 ≤ p → ∀ Ceta, ∃ Cmass, ∀ t, 0 < t → t < T →
      Ceta * (intervalDomain.integral (u t)) ^ (p + rho) ≤ Cmass)
    (hu_nonneg :
      ∀ t, 0 < t → t < T → ∀ x : intervalDomain.Point, 0 ≤ u t x)
    (hpow_int :
      ∀ pExp : ℝ, 1 < pExp → ∀ t, 0 < t → t < T →
        IntervalIntegrable
          (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ pExp))
          MeasureTheory.volume 0 1) :
    ∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u := by
  refine intervalDomain_all_exponents_of_energy_dissipation_interpolation
    hboot henergy hdiss ?_ hu_nonneg hpow_int
  intro p hp
  exact moser_interpolation_of_mass_gradient_estimate
    (hcGrad p hp) (hMG p hp) (hgrad p hp) (hmass p hp)

/-- Interior-nonnegative version of
`intervalDomain_all_exponents_of_energy_dissipation_interpolation`.  This is
the form supplied directly by classical interval solutions, whose positivity is
part of `IsPaper2ClassicalSolution` on `intervalDomain.inside`. -/
theorem intervalDomain_all_exponents_of_energy_dissipation_interpolation_inside_nonneg
    {u : ℝ → intervalDomain.Point → ℝ} {N T rho p0 : ℝ}
    (hboot : AbstractLpBootstrapHypothesis intervalDomain u N T rho p0)
    (henergy : LpBootstrapEnergyInequality intervalDomain u T rho p0)
    (hdiss : ∀ p, p0 ≤ p → ∀ A B K L_const,
      (∀ t, 0 < t → t < T →
        (1 / p) * deriv
            (fun τ => intervalDomain.integral (fun x => (u τ x) ^ p)) t +
          A * intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
          B * intervalDomain.integral (fun x => (u t x) ^ p) ≤
        K * intervalDomain.integral (fun x => (u t x) ^ (p + rho)) + L_const) →
      ∀ t, 0 < t → t < T →
        0 ≤
          (1 / p) * deriv
              (fun τ => intervalDomain.integral (fun x => (u τ x) ^ p)) t +
            B * intervalDomain.integral (fun x => (u t x) ^ p))
    (hinterp : ∀ p, p0 ≤ p → ∀ eps > 0, ∃ Ceps, ∀ t, 0 < t → t < T →
      intervalDomain.integral (fun x => (u t x) ^ (p + rho)) ≤
        eps * intervalDomain.integral (fun x =>
          (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
        Ceps)
    (hu_nonneg :
      ∀ t, 0 < t → t < T →
        ∀ x : intervalDomain.Point, x ∈ intervalDomain.inside → 0 ≤ u t x)
    (hpow_int :
      ∀ pExp : ℝ, 1 < pExp → ∀ t, 0 < t → t < T →
        IntervalIntegrable
          (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ pExp))
          MeasureTheory.volume 0 1) :
    ∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u := by
  exact
    intervalDomain_all_exponents_of_moser_iteration_chain_inside_nonneg
        (AbstractLpBootstrapHypothesis.rho_pos hboot)
        (AbstractLpBootstrapHypothesis.initial_lp_bound hboot)
        (moser_step_family_of_energy_dissipation_interpolation henergy hdiss hinterp)
        hu_nonneg hpow_int

/-- Interior-nonnegative interval-domain closure with interpolation supplied in
the Paper 2 mass-gradient form. -/
theorem intervalDomain_all_exponents_of_energy_dissipation_mass_gradient_inside_nonneg
    {u : ℝ → intervalDomain.Point → ℝ} {N T rho p0 : ℝ}
    (cGrad : ℝ → ℝ)
    (hboot : AbstractLpBootstrapHypothesis intervalDomain u N T rho p0)
    (henergy : LpBootstrapEnergyInequality intervalDomain u T rho p0)
    (hdiss : ∀ p, p0 ≤ p → ∀ A B K L_const,
      (∀ t, 0 < t → t < T →
        (1 / p) * deriv
            (fun τ => intervalDomain.integral (fun x => (u τ x) ^ p)) t +
          A * intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
          B * intervalDomain.integral (fun x => (u t x) ^ p) ≤
        K * intervalDomain.integral (fun x => (u t x) ^ (p + rho)) + L_const) →
      ∀ t, 0 < t → t < T →
        0 ≤
          (1 / p) * deriv
              (fun τ => intervalDomain.integral (fun x => (u τ x) ^ p)) t +
            B * intervalDomain.integral (fun x => (u t x) ^ p))
    (hcGrad : ∀ p, p0 ≤ p → 0 < cGrad p)
    (hMG : ∀ p, p0 ≤ p → ∀ eta > 0, ∃ Ceta,
      LpMassGradientInterpolationEstimate intervalDomain (p + rho) eta Ceta T u)
    (hgrad : ∀ p, p0 ≤ p → ∀ t, 0 < t → t < T →
      intervalDomain.integral (fun x =>
          (u t x) ^ (p + rho - 2) * (intervalDomain.gradNorm (u t) x) ^ 2) ≤
        cGrad p * intervalDomain.integral (fun x =>
          (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2))
    (hmass : ∀ p, p0 ≤ p → ∀ Ceta, ∃ Cmass, ∀ t, 0 < t → t < T →
      Ceta * (intervalDomain.integral (u t)) ^ (p + rho) ≤ Cmass)
    (hu_nonneg :
      ∀ t, 0 < t → t < T →
        ∀ x : intervalDomain.Point, x ∈ intervalDomain.inside → 0 ≤ u t x)
    (hpow_int :
      ∀ pExp : ℝ, 1 < pExp → ∀ t, 0 < t → t < T →
        IntervalIntegrable
          (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ pExp))
          MeasureTheory.volume 0 1) :
    ∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u := by
  refine intervalDomain_all_exponents_of_energy_dissipation_interpolation_inside_nonneg
    hboot henergy hdiss ?_ hu_nonneg hpow_int
  intro p hp
  exact moser_interpolation_of_mass_gradient_estimate
    (hcGrad p hp) (hMG p hp) (hgrad p hp) (hmass p hp)

end ShenWork.Paper2.IntervalDomainEnergyStep

end
