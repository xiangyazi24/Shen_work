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

  B3 Moser frontier note: the abstract all-finite-Lp envelope is not a valid
  endpoint route to `L∞` on `intervalDomain`; endpoint spikes are invisible to
  the interval integral.  The usable Moser interface below therefore keeps the
  solution energy step per exponent: the relative GN/Young absorption
      `∫ u^(p+ρ) ≤ eps * ∫ |∇(u^(p/2))|^2 + Ceps * ∫ u^p`
  is combined with the already-known `p`-level bound at that induction stage,
  not with a standalone abstract Lp envelope.
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

/-- The Neumann endpoint contribution vanishes when `f` genuinely satisfies the
Neumann boundary condition (one-sided derivative `0` at both endpoints). -/
theorem intervalDomain_neumannBoundaryTerm_eq_zero
    (test f : intervalDomain.Point → ℝ)
    (hNeuR : intervalDomain.normalDeriv f intervalDomainRightEndpoint = 0)
    (hNeuL : intervalDomain.normalDeriv f intervalDomainLeftEndpoint = 0) :
    intervalDomainNeumannBoundaryTerm test f = 0 := by
  unfold intervalDomainNeumannBoundaryTerm
  rw [hNeuR, hNeuL]
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
          intervalDomainDerivativePairIntegral test f)
    (hNeuR : intervalDomain.normalDeriv f intervalDomainRightEndpoint = 0)
    (hNeuL : intervalDomain.normalDeriv f intervalDomainLeftEndpoint = 0) :
    intervalDomain.integral
        (fun x => test x * intervalDomain.laplacian f x) =
      -(intervalDomainDerivativePairIntegral test f) := by
  rw [hIBP, intervalDomain_neumannBoundaryTerm_eq_zero test f hNeuR hNeuL]
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
          intervalDomainLpDiffusionDissipation pExp u t)
    (hNeuR : intervalDomain.normalDeriv (u t) intervalDomainRightEndpoint = 0)
    (hNeuL : intervalDomain.normalDeriv (u t) intervalDomainLeftEndpoint = 0) :
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
      (intervalDomainLpDiffusionTest pExp u t) (u t) hIBP' hNeuR hNeuL
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
    (hNeuR : intervalDomain.normalDeriv (u t) intervalDomainRightEndpoint = 0)
    (hNeuL : intervalDomain.normalDeriv (u t) intervalDomainLeftEndpoint = 0)
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
      (u := u) (v := v) hpExp ht0 htT hLpTime hPDEIntegral hIBP hNeuR hNeuL
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
    (hNeuR : intervalDomain.normalDeriv (u t) intervalDomainRightEndpoint = 0)
    (hNeuL : intervalDomain.normalDeriv (u t) intervalDomainLeftEndpoint = 0)
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
      hpExp_ne ht0 htT hLpTime hPDEIntegral hIBP hNeuR hNeuL
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
    (hNeuR : intervalDomain.normalDeriv (u t) intervalDomainRightEndpoint = 0)
    (hNeuL : intervalDomain.normalDeriv (u t) intervalDomainLeftEndpoint = 0)
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
      hCrossGNYoung hLpTime hPDEIntegral hIBP hNeuR hNeuL
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
    (hNeuR : intervalDomain.normalDeriv (u t) intervalDomainRightEndpoint = 0)
    (hNeuL : intervalDomain.normalDeriv (u t) intervalDomainLeftEndpoint = 0)
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
      hCrossGNYoung hLpTime hPDEIntegral hIBP hNeuR hNeuL
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
    (hNeuR : intervalDomain.normalDeriv (u t) intervalDomainRightEndpoint = 0)
    (hNeuL : intervalDomain.normalDeriv (u t) intervalDomainLeftEndpoint = 0)
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
      hpExp_ne ht0 htT hLpTime hPDEIntegral hIBP hNeuR hNeuL
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
    (hNeuR : ∀ t, 0 < t → t < T →
      intervalDomain.normalDeriv (u t) intervalDomainRightEndpoint = 0)
    (hNeuL : ∀ t, 0 < t → t < T →
      intervalDomain.normalDeriv (u t) intervalDomainLeftEndpoint = 0)
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
      (hPDEIntegral t ht0 htT) (hIBP t ht0 htT) (hNeuR t ht0 htT) (hNeuL t ht0 htT)
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
    (hNeuR : intervalDomain.normalDeriv (u t) intervalDomainRightEndpoint = 0)
    (hNeuL : intervalDomain.normalDeriv (u t) intervalDomainLeftEndpoint = 0)
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
      hpExp_ne ht0 htT hLpTime hPDEIntegral hIBP hNeuR hNeuL
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
    (hNeuR : ∀ t, 0 < t → t < T →
      intervalDomain.normalDeriv (u t) intervalDomainRightEndpoint = 0)
    (hNeuL : ∀ t, 0 < t → t < T →
      intervalDomain.normalDeriv (u t) intervalDomainLeftEndpoint = 0)
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
      (hPDEIntegral t ht0 htT) (hIBP t ht0 htT) (hNeuR t ht0 htT) (hNeuL t ht0 htT)
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
    (hNeuR : intervalDomain.normalDeriv (u t) intervalDomainRightEndpoint = 0)
    (hNeuL : intervalDomain.normalDeriv (u t) intervalDomainLeftEndpoint = 0)
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
      hPDEIntegral hIBP hNeuR hNeuL hDiffusionCoercive hCrossControl
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
    (hNeuR : ∀ t, 0 < t → t < T →
      intervalDomain.normalDeriv (u t) intervalDomainRightEndpoint = 0)
    (hNeuL : ∀ t, 0 < t → t < T →
      intervalDomain.normalDeriv (u t) intervalDomainLeftEndpoint = 0)
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
      (hIBP t ht0 htT) (hNeuR t ht0 htT) (hNeuL t ht0 htT) (hDiffusionCoercive t ht0 htT)
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
    (hNeuR : ∀ t, 0 < t → t < T →
      intervalDomain.normalDeriv (u t) intervalDomainRightEndpoint = 0)
    (hNeuL : ∀ t, 0 < t → t < T →
      intervalDomain.normalDeriv (u t) intervalDomainLeftEndpoint = 0)
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
      hpExp hchiBound hLpTime hPDEIntegral hIBP hNeuR hNeuL hDiffusionCoercive
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

/-- Scalar Gronwall source form after a uniform bound on the next-power
lower-order term.

This is the exact open-interval inequality
`E_p'(t) <= (p*B) E_p(t) + p*(chi*Ccross*Zbound + L)`, where
`Zbound` bounds `∫ u^(p+rho)`.  The displayed source constant is the only
remaining lower-order contribution. -/
theorem intervalDomain_lp_abs_energy_derivative_le_linear_source_family_of_frontiers
    {params : CM2Params} {T rho pExp eps A chiBound B L_const Ccross Zbound : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hpExp : 1 < pExp) (hchiBound : 0 ≤ chiBound)
    (hCcross_nonneg : 0 ≤ Ccross)
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
    (hNeuR : ∀ t, 0 < t → t < T →
      intervalDomain.normalDeriv (u t) intervalDomainRightEndpoint = 0)
    (hNeuL : ∀ t, 0 < t → t < T →
      intervalDomain.normalDeriv (u t) intervalDomainLeftEndpoint = 0)
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
    (hNextPowerBound :
      ∀ t, 0 < t → t < T →
        intervalDomain.integral (fun x => (u t x) ^ (pExp + rho)) ≤ Zbound) :
    ∀ t, 0 < t → t < T →
      deriv (fun τ => intervalDomainLpAbsEnergy pExp u τ) t ≤
        (pExp * B) * intervalDomainLpAbsEnergy pExp u t +
          pExp * (chiBound * Ccross * Zbound + L_const) := by
  intro t ht0 htT
  have hpoint :=
    intervalDomain_lp_abs_energy_derivative_le_explicit_lower_terms_family_of_frontiers
      (params := params) (T := T) (rho := rho) (pExp := pExp)
      (eps := eps) (A := A) (chiBound := chiBound) (B := B)
      (L_const := L_const) (Ccross := Ccross) (u := u) (v := v)
      hpExp hchiBound hLpTime hPDEIntegral hIBP hNeuR hNeuL hDiffusionCoercive
      hCrossControl hCrossGNYoungAt hLogisticUpper hDissNonneg t ht0 htT
  set E := intervalDomainLpAbsEnergy pExp u t
  set Z := intervalDomain.integral (fun x => (u t x) ^ (pExp + rho))
  have hZ_le : Z ≤ Zbound := by
    simpa [Z] using hNextPowerBound t ht0 htT
  have hp_nonneg : 0 ≤ pExp := by linarith
  have hcoef_nonneg : 0 ≤ pExp * (chiBound * Ccross) :=
    mul_nonneg hp_nonneg (mul_nonneg hchiBound hCcross_nonneg)
  have hcross_bound :
      pExp * (chiBound * Ccross * Z) ≤
        pExp * (chiBound * Ccross * Zbound) := by
    calc
      pExp * (chiBound * Ccross * Z)
          = (pExp * (chiBound * Ccross)) * Z := by ring
      _ ≤ (pExp * (chiBound * Ccross)) * Zbound :=
          mul_le_mul_of_nonneg_left hZ_le hcoef_nonneg
      _ = pExp * (chiBound * Ccross * Zbound) := by ring
  have hsource_bound :
      pExp * (chiBound * Ccross * Z + B * E + L_const) ≤
        (pExp * B) * E +
          pExp * (chiBound * Ccross * Zbound + L_const) := by
    calc
      pExp * (chiBound * Ccross * Z + B * E + L_const)
          = pExp * (chiBound * Ccross * Z) +
              pExp * (B * E) + pExp * L_const := by ring
      _ ≤ pExp * (chiBound * Ccross * Zbound) +
              pExp * (B * E) + pExp * L_const := by
            linarith
      _ =
          (pExp * B) * E +
            pExp * (chiBound * Ccross * Zbound + L_const) := by ring
  change
    deriv (fun τ => intervalDomainLpAbsEnergy pExp u τ) t ≤
      pExp * (chiBound * Ccross * Z + B * E + L_const) at hpoint
  exact hpoint.trans hsource_bound

/-- Dominated scalar Gronwall form with user-supplied nonnegative-friendly
constants `c` and `d`.

The two coefficient hypotheses are explicit:
`p*B <= c` controls the energy term and
`p*(chi*Ccross*Zbound + L) <= d` controls all lower-order terms. -/
theorem intervalDomain_lp_abs_energy_derivative_le_gronwall_source_family_of_frontiers
    {params : CM2Params}
    {T rho pExp eps A chiBound B L_const Ccross Zbound c d : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hpExp : 1 < pExp) (hchiBound : 0 ≤ chiBound)
    (hCcross_nonneg : 0 ≤ Ccross)
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
    (hNeuR : ∀ t, 0 < t → t < T →
      intervalDomain.normalDeriv (u t) intervalDomainRightEndpoint = 0)
    (hNeuL : ∀ t, 0 < t → t < T →
      intervalDomain.normalDeriv (u t) intervalDomainLeftEndpoint = 0)
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
    (hNextPowerBound :
      ∀ t, 0 < t → t < T →
        intervalDomain.integral (fun x => (u t x) ^ (pExp + rho)) ≤ Zbound)
    (hEnergyNonneg :
      ∀ t, 0 < t → t < T → 0 ≤ intervalDomainLpAbsEnergy pExp u t)
    (hEnergyCoeff : pExp * B ≤ c)
    (hSourceCoeff : pExp * (chiBound * Ccross * Zbound + L_const) ≤ d) :
    ∀ t, 0 < t → t < T →
      deriv (fun τ => intervalDomainLpAbsEnergy pExp u τ) t ≤
        c * intervalDomainLpAbsEnergy pExp u t + d := by
  have hlinear :=
    intervalDomain_lp_abs_energy_derivative_le_linear_source_family_of_frontiers
      (params := params) (T := T) (rho := rho) (pExp := pExp)
      (eps := eps) (A := A) (chiBound := chiBound) (B := B)
      (L_const := L_const) (Ccross := Ccross) (Zbound := Zbound)
      (u := u) (v := v) hpExp hchiBound hCcross_nonneg
      hLpTime hPDEIntegral hIBP hNeuR hNeuL hDiffusionCoercive hCrossControl
      hCrossGNYoungAt hLogisticUpper hDissNonneg hNextPowerBound
  intro t ht0 htT
  set E := intervalDomainLpAbsEnergy pExp u t
  have hE_nonneg : 0 ≤ E := by
    simpa [E] using hEnergyNonneg t ht0 htT
  have henergy_term : (pExp * B) * E ≤ c * E :=
    mul_le_mul_of_nonneg_right hEnergyCoeff hE_nonneg
  have hlinear_t := hlinear t ht0 htT
  linarith

/-- `Set.Ico 0 T` version of the dominated scalar Gronwall inequality.

The open-interval PDE derivation supplies every `0 < t < T`; the single
additional hypothesis `hDerivZero` is the endpoint right-derivative frontier
needed by the repository's Gronwall wrapper. -/
theorem intervalDomain_lp_abs_energy_derivative_le_gronwall_ico_of_frontiers
    {params : CM2Params}
    {T rho pExp eps A chiBound B L_const Ccross Zbound c d : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hpExp : 1 < pExp) (hchiBound : 0 ≤ chiBound)
    (hCcross_nonneg : 0 ≤ Ccross)
    (hDerivZero :
      deriv (fun τ => intervalDomainLpAbsEnergy pExp u τ) 0 ≤
        c * intervalDomainLpAbsEnergy pExp u 0 + d)
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
    (hNeuR : ∀ t, 0 < t → t < T →
      intervalDomain.normalDeriv (u t) intervalDomainRightEndpoint = 0)
    (hNeuL : ∀ t, 0 < t → t < T →
      intervalDomain.normalDeriv (u t) intervalDomainLeftEndpoint = 0)
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
    (hNextPowerBound :
      ∀ t, 0 < t → t < T →
        intervalDomain.integral (fun x => (u t x) ^ (pExp + rho)) ≤ Zbound)
    (hEnergyNonneg :
      ∀ t, 0 < t → t < T → 0 ≤ intervalDomainLpAbsEnergy pExp u t)
    (hEnergyCoeff : pExp * B ≤ c)
    (hSourceCoeff : pExp * (chiBound * Ccross * Zbound + L_const) ≤ d) :
    ∀ t ∈ Set.Ico (0 : ℝ) T,
      deriv (fun τ => intervalDomainLpAbsEnergy pExp u τ) t ≤
        c * intervalDomainLpAbsEnergy pExp u t + d := by
  have hopen :=
    intervalDomain_lp_abs_energy_derivative_le_gronwall_source_family_of_frontiers
      (params := params) (T := T) (rho := rho) (pExp := pExp)
      (eps := eps) (A := A) (chiBound := chiBound) (B := B)
      (L_const := L_const) (Ccross := Ccross) (Zbound := Zbound)
      (c := c) (d := d) (u := u) (v := v)
      hpExp hchiBound hCcross_nonneg hLpTime hPDEIntegral hIBP hNeuR hNeuL
      hDiffusionCoercive hCrossControl hCrossGNYoungAt hLogisticUpper
      hDissNonneg hNextPowerBound hEnergyNonneg hEnergyCoeff hSourceCoeff
  intro t ht
  by_cases ht_zero : t = 0
  · subst t
    exact hDerivZero
  · have ht0 : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht_zero)
    exact hopen t ht0 ht.2

/-- Full scalar Gronwall bridge from the interval PDE frontiers plus an
explicit next-power bound.

This theorem packages the exact source constant into the repository's existing
`intervalDomain_LpPowerBoundedBefore_of_abs_energy_gronwall` interface. -/
theorem intervalDomain_LpPowerBoundedBefore_of_energy_frontiers_next_power_bound
    {params : CM2Params}
    {T rho pExp eps A chiBound B L_const Ccross Zbound c d δ : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hpExp : 1 < pExp) (hchiBound : 0 ≤ chiBound)
    (hCcross_nonneg : 0 ≤ Ccross)
    (hδ_nonneg : 0 ≤ δ) (hc_nonneg : 0 ≤ c) (hd_nonneg : 0 ≤ d)
    (hu_nonneg :
      ∀ t, 0 < t → t < T → ∀ x : intervalDomain.Point, 0 ≤ u t x)
    (hcont :
      ContinuousOn (fun t => intervalDomainLpAbsEnergy pExp u t)
        (Set.Icc (0 : ℝ) T))
    (hderiv_within :
      ∀ t ∈ Set.Ico (0 : ℝ) T,
        HasDerivWithinAt
          (fun τ => intervalDomainLpAbsEnergy pExp u τ)
          (deriv (fun τ => intervalDomainLpAbsEnergy pExp u τ) t)
          (Set.Ici t) t)
    (hinit : intervalDomainLpAbsEnergy pExp u 0 ≤ δ)
    (hDerivZero :
      deriv (fun τ => intervalDomainLpAbsEnergy pExp u τ) 0 ≤
        c * intervalDomainLpAbsEnergy pExp u 0 + d)
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
    (hNeuR : ∀ t, 0 < t → t < T →
      intervalDomain.normalDeriv (u t) intervalDomainRightEndpoint = 0)
    (hNeuL : ∀ t, 0 < t → t < T →
      intervalDomain.normalDeriv (u t) intervalDomainLeftEndpoint = 0)
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
    (hNextPowerBound :
      ∀ t, 0 < t → t < T →
        intervalDomain.integral (fun x => (u t x) ^ (pExp + rho)) ≤ Zbound)
    (hEnergyNonneg :
      ∀ t, 0 < t → t < T → 0 ≤ intervalDomainLpAbsEnergy pExp u t)
    (hEnergyCoeff : pExp * B ≤ c)
    (hSourceCoeff : pExp * (chiBound * Ccross * Zbound + L_const) ≤ d) :
    LpPowerBoundedBefore intervalDomain pExp T u := by
  have hderiv_le :=
    intervalDomain_lp_abs_energy_derivative_le_gronwall_ico_of_frontiers
      (params := params) (T := T) (rho := rho) (pExp := pExp)
      (eps := eps) (A := A) (chiBound := chiBound) (B := B)
      (L_const := L_const) (Ccross := Ccross) (Zbound := Zbound)
      (c := c) (d := d) (u := u) (v := v)
      hpExp hchiBound hCcross_nonneg hDerivZero hLpTime hPDEIntegral hIBP hNeuR hNeuL
      hDiffusionCoercive hCrossControl hCrossGNYoungAt hLogisticUpper
      hDissNonneg hNextPowerBound hEnergyNonneg hEnergyCoeff hSourceCoeff
  exact
    intervalDomain_LpPowerBoundedBefore_of_abs_energy_gronwall
      (u := u) (T := T) (p := pExp) (δ := δ) (c := c) (d := d)
      hδ_nonneg hc_nonneg hd_nonneg hu_nonneg hcont hderiv_within hinit
      hderiv_le

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
          intervalDomainL2DiffusionDissipation u t)
    (hNeuR : intervalDomain.normalDeriv (u t) intervalDomainRightEndpoint = 0)
    (hNeuL : intervalDomain.normalDeriv (u t) intervalDomainLeftEndpoint = 0) :
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
      (u t) (u t) hIBP' hNeuR hNeuL
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
    (hNeuR : intervalDomain.normalDeriv (u t) intervalDomainRightEndpoint = 0)
    (hNeuL : intervalDomain.normalDeriv (u t) intervalDomainLeftEndpoint = 0)
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
      hL2Time hPDEIntegral hIBP hNeuR hNeuL
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
    (hNeuR : intervalDomain.normalDeriv (u t) intervalDomainRightEndpoint = 0)
    (hNeuL : intervalDomain.normalDeriv (u t) intervalDomainLeftEndpoint = 0)
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
      (u := u) (v := v) hL2Time hPDEIntegral hIBP hNeuR hNeuL hCrossControl
  have hCeps' :
      intervalDomain.crossDiffusionEnergyTerm params 2 (u t) (v t) ≤
        eps * intervalDomainLpWeightedGradientDissipation 2 u t +
          Ceps * intervalDomain.integral (fun x => (u t x) ^ (2 + rho)) := by
    simpa [intervalDomainLpWeightedGradientDissipation] using hCeps
  have hscaled :=
    mul_le_mul_of_nonneg_left hCeps' hchiBound
  linarith

/-- Uniform-in-time version of
`intervalDomain_l2_half_energy_cross_bootstrap_inequality_of_frontiers`.
The cross-diffusion bootstrap predicate already supplies one constant `Ceps`
for all interior times; this theorem keeps that constant exposed instead of
rechoosing it after `t`. -/
theorem intervalDomain_l2_half_energy_cross_bootstrap_inequality_of_frontiers_uniformCeps
    {params : CM2Params} {T rho eps chiBound : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (heps : 0 < eps) (hchiBound : 0 ≤ chiBound)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hfrontiers : ∀ t, 0 < t → t < T →
      (deriv (fun τ => intervalDomainL2HalfEnergy u τ) t =
        intervalDomain.integral (intervalDomainL2TimeTerm u t)) ∧
      (intervalDomain.integral (intervalDomainL2TimeTerm u t) =
        intervalDomainL2DiffusionIntegral u t -
          params.χ₀ * intervalDomainL2ChemotaxisIntegral params u v t +
          intervalDomainL2LogisticIntegral params u t) ∧
      (intervalDomainL2DiffusionIntegral u t =
        intervalDomainNeumannBoundaryTerm (u t) (u t) -
          intervalDomainL2DiffusionDissipation u t) ∧
      (intervalDomain.normalDeriv (u t) intervalDomainRightEndpoint = 0) ∧
      (intervalDomain.normalDeriv (u t) intervalDomainLeftEndpoint = 0) ∧
      (-params.χ₀ * intervalDomainL2ChemotaxisIntegral params u v t ≤
        chiBound *
          intervalDomain.crossDiffusionEnergyTerm params 2 (u t) (v t))) :
    ∃ Ceps, ∀ t, 0 < t → t < T →
      deriv (fun τ => intervalDomainL2HalfEnergy u τ) t +
        intervalDomainL2DiffusionDissipation u t ≤
          chiBound *
              (eps * intervalDomainLpWeightedGradientDissipation 2 u t +
                Ceps *
                  intervalDomain.integral (fun x => (u t x) ^ (2 + rho))) +
            intervalDomainL2LogisticIntegral params u t := by
  have htwo : (1 : ℝ) < 2 := by norm_num
  obtain ⟨Ceps, hCeps⟩ := hcross eps heps 2 htwo
  refine ⟨Ceps, ?_⟩
  intro t ht0 htT
  rcases hfrontiers t ht0 htT with
    ⟨hL2Time, hPDEIntegral, hIBP, hNeuR, hNeuL, hCrossControl⟩
  have hbasic :=
    intervalDomain_l2_half_energy_inequality_of_cross_control
      (params := params) (t := t) (chiBound := chiBound)
      (u := u) (v := v) hL2Time hPDEIntegral hIBP hNeuR hNeuL hCrossControl
  have hCeps' :
      intervalDomain.crossDiffusionEnergyTerm params 2 (u t) (v t) ≤
        eps * intervalDomainLpWeightedGradientDissipation 2 u t +
          Ceps * intervalDomain.integral (fun x => (u t x) ^ (2 + rho)) := by
    simpa [intervalDomainLpWeightedGradientDissipation] using hCeps t ht0 htT
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

/-- Turn the relative GN/Young interpolation used in a genuine Moser
iteration into the constant interpolation expected by the existing single-step
interface, using the already-established bound at the current exponent `p`.

This is the key non-endpoint bridge: the constant depends on the current
`LpPowerBoundedBefore D p T u` datum, so it is valid inside the induction
chain but is not an abstract `Lp -> L∞` envelope principle. -/
theorem moser_interpolation_of_relative_interpolation_and_lp_bound
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T p rho : ℝ}
    (hLp : LpPowerBoundedBefore D p T u)
    (hrel : ∀ eps > 0, ∃ Ceps, 0 ≤ Ceps ∧ ∀ t, 0 < t → t < T →
      D.integral (fun x => (u t x) ^ (p + rho)) ≤
        eps * D.integral (fun x =>
          (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
        Ceps * D.integral (fun x => (u t x) ^ p)) :
    ∀ eps > 0, ∃ Cconst, ∀ t, 0 < t → t < T →
      D.integral (fun x => (u t x) ^ (p + rho)) ≤
        eps * D.integral (fun x =>
          (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
        Cconst := by
  rcases hLp with ⟨Cp, hCp⟩
  intro eps heps
  rcases hrel eps heps with ⟨Ceps, hCeps_nonneg, hCeps⟩
  refine ⟨Ceps * Cp, ?_⟩
  intro t ht0 htT
  have hmain := hCeps t ht0 htT
  have hY := hCp t ht0 htT
  have hscaled :
      Ceps * D.integral (fun x => (u t x) ^ p) ≤ Ceps * Cp :=
    mul_le_mul_of_nonneg_left hY hCeps_nonneg
  linarith

/-- Per-exponent `hstep` for `all_exponents_of_moser_iteration_chain` from
the solution energy inequality and relative GN/Young absorption.

The current `p`-level Lp bound is an explicit input because relative
absorption controls `∫u^(p+ρ)` by a gradient term plus `Ceps * ∫u^p`. -/
theorem moser_step_of_energy_dissipation_relative_interpolation
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T rho p0 p : ℝ}
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
    (hrel : ∀ p, p0 ≤ p → ∀ eps > 0, ∃ Ceps, 0 ≤ Ceps ∧
      ∀ t, 0 < t → t < T →
        D.integral (fun x => (u t x) ^ (p + rho)) ≤
          eps * D.integral (fun x =>
            (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
          Ceps * D.integral (fun x => (u t x) ^ p))
    (hp : p0 ≤ p)
    (hLp : LpPowerBoundedBefore D p T u) :
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
  rcases henergy p hp with ⟨A, hA, B, _hB, K, hK, L_const, hfull⟩
  refine ⟨A, hA, K, hK, L_const, ?_, ?_⟩
  · intro t ht0 htT
    have hfull_t := hfull t ht0 htT
    have hdrop_t := hdiss p hp A B K L_const hfull t ht0 htT
    linarith
  · exact moser_interpolation_of_relative_interpolation_and_lp_bound
      hLp (hrel p hp)

/-- Moser exponent chain driven by the per-exponent solution energy step and
relative GN/Young absorption.

Unlike the invalid abstract endpoint envelope route, this theorem consumes the
current `LpPowerBoundedBefore` bound at each induction level and then produces
the next exponent. -/
theorem moser_iteration_chain_of_energy_dissipation_relative_interpolation
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T p0 rho : ℝ}
    (hrho : 0 < rho)
    (hbase : LpPowerBoundedBefore D p0 T u)
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
    (hrel : ∀ p, p0 ≤ p → ∀ eps > 0, ∃ Ceps, 0 ≤ Ceps ∧
      ∀ t, 0 < t → t < T →
        D.integral (fun x => (u t x) ^ (p + rho)) ≤
          eps * D.integral (fun x =>
            (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
          Ceps * D.integral (fun x => (u t x) ^ p)) :
    ∀ n : ℕ, LpPowerBoundedBefore D (p0 + n * rho) T u := by
  intro n
  induction n with
  | zero =>
    simp only [CharP.cast_eq_zero, zero_mul, add_zero]
    exact hbase
  | succ n ih =>
    have hexp_eq : p0 + (↑(n + 1) : ℝ) * rho = (p0 + ↑n * rho) + rho := by
      push_cast
      ring
    rw [hexp_eq]
    have hp_ge : p0 ≤ p0 + ↑n * rho :=
      le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) hrho.le)
    obtain ⟨A, hA, K, hK, L_const, hstep_energy, hstep_interp⟩ :=
      moser_step_of_energy_dissipation_relative_interpolation
        henergy hdiss hrel hp_ge ih
    exact IntervalDomainChain.lp_bootstrap_single_step_abstract
      (L_const := L_const) hA hK hstep_energy hstep_interp

/-- All finite exponents from the solution-level relative Moser step, with
downward Lp monotonicity supplied separately. -/
theorem all_exponents_of_energy_dissipation_relative_interpolation_lpmono
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
    (hrel : ∀ p, p0 ≤ p → ∀ eps > 0, ∃ Ceps, 0 ≤ Ceps ∧
      ∀ t, 0 < t → t < T →
        D.integral (fun x => (u t x) ^ (p + rho)) ≤
          eps * D.integral (fun x =>
            (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
          Ceps * D.integral (fun x => (u t x) ^ p))
    (hLpMono :
      ∀ {p q : ℝ}, 1 < p → p ≤ q →
        LpPowerBoundedBefore D q T u → LpPowerBoundedBefore D p T u) :
    ∀ pExp > 1, LpPowerBoundedBefore D pExp T u := by
  exact IntervalDomainMoserClosure.all_exponents_of_chain_and_lp_mono
    (AbstractLpBootstrapHypothesis.rho_pos hboot)
    (moser_iteration_chain_of_energy_dissipation_relative_interpolation
      (AbstractLpBootstrapHypothesis.rho_pos hboot)
      (AbstractLpBootstrapHypothesis.initial_lp_bound hboot)
      henergy hdiss hrel)
    hLpMono

/-- Lower-order mass term conversion needed to use Lemma 4.1 inside a genuine
Moser step.

`LpMassGradientInterpolationEstimate` supplies the lower-order term
`C * (∫u)^(p+ρ)`.  The relative Moser step needs the term in the form
`Crel * ∫u^p`.  This comparison is not part of the current abstract
`BoundedDomainData` API; on the concrete interval it should come from
nonnegativity, unit volume, and mass/positive-mass information. -/
def MoserMassPowerToCurrentLpLowerOrder
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p → ∀ Cmass, ∃ Crel, 0 ≤ Crel ∧ ∀ t, 0 < t → t < T →
    Cmass * (D.integral (u t)) ^ (p + rho) ≤
      Crel * D.integral (fun x => (u t x) ^ p)

/-- Fixed-exponent eps-absorption from the mass-gradient interpolation form.

This is the algebraic handoff from the GN/Young output
`LpMassGradientInterpolationEstimate` to the relative Moser input
`∫u^(p+ρ) <= eps * ∫|∇(u^(p/2))|² + Ceps * ∫u^p`, after supplying:
* the chain-rule/coercivity comparison from the weighted `|∇u|²` term to
  `|∇(u^(p/2))|²`;
* the lower-order conversion from `(∫u)^(p+ρ)` to `∫u^p`. -/
theorem moser_relative_eps_absorption_of_mass_gradient_estimate
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T p rho cGrad : ℝ}
    (hcGrad : 0 < cGrad)
    (hMG : ∀ eta > 0, ∃ Ceta,
      LpMassGradientInterpolationEstimate D (p + rho) eta Ceta T u)
    (hgrad : ∀ t, 0 < t → t < T →
      D.integral (fun x =>
          (u t x) ^ (p + rho - 2) * (D.gradNorm (u t) x) ^ 2) ≤
        cGrad * D.integral (fun x =>
          (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2))
    (hmassToLp : ∀ Ceta, ∃ Crel, 0 ≤ Crel ∧ ∀ t, 0 < t → t < T →
      Ceta * (D.integral (u t)) ^ (p + rho) ≤
        Crel * D.integral (fun x => (u t x) ^ p)) :
    ∀ eps > 0, ∃ Ceps, 0 ≤ Ceps ∧ ∀ t, 0 < t → t < T →
      D.integral (fun x => (u t x) ^ (p + rho)) ≤
        eps * D.integral (fun x =>
          (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
        Ceps * D.integral (fun x => (u t x) ^ p) := by
  intro eps heps
  have heta_pos : 0 < eps / cGrad := div_pos heps hcGrad
  obtain ⟨Ceta, hCeta⟩ := hMG (eps / cGrad) heta_pos
  obtain ⟨Crel, hCrel_nonneg, hCrel⟩ := hmassToLp Ceta
  refine ⟨Crel, hCrel_nonneg, ?_⟩
  intro t ht0 htT
  have hbound := LpMassGradientInterpolationEstimate.bound hCeta ht0 htT
  have hgrad_t := hgrad t ht0 htT
  have hmass_t := hCrel t ht0 htT
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
            Crel * D.integral (fun x => (u t x) ^ p) := by
          linarith
    _ =
          eps * D.integral (fun x =>
            (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
            Crel * D.integral (fun x => (u t x) ^ p) := by
          field_simp [ne_of_gt hcGrad]

/-- All-exponent family form of the relative eps-absorption bridge from
mass-gradient interpolation. -/
theorem moser_relative_eps_absorption_family_of_mass_gradient_estimate
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T rho p0 : ℝ}
    (cGrad : ℝ → ℝ)
    (hcGrad : ∀ p, p0 ≤ p → 0 < cGrad p)
    (hMG : ∀ p, p0 ≤ p → ∀ eta > 0, ∃ Ceta,
      LpMassGradientInterpolationEstimate D (p + rho) eta Ceta T u)
    (hgrad : ∀ p, p0 ≤ p → ∀ t, 0 < t → t < T →
      D.integral (fun x =>
          (u t x) ^ (p + rho - 2) * (D.gradNorm (u t) x) ^ 2) ≤
        cGrad p * D.integral (fun x =>
          (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2))
    (hmassToLp : MoserMassPowerToCurrentLpLowerOrder D u T rho p0) :
    ∀ p, p0 ≤ p → ∀ eps > 0, ∃ Ceps, 0 ≤ Ceps ∧
      ∀ t, 0 < t → t < T →
        D.integral (fun x => (u t x) ^ (p + rho)) ≤
          eps * D.integral (fun x =>
            (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
          Ceps * D.integral (fun x => (u t x) ^ p) := by
  intro p hp
  exact moser_relative_eps_absorption_of_mass_gradient_estimate
    (hcGrad p hp) (hMG p hp) (hgrad p hp) (hmassToLp p hp)

/-- Moser exponent chain from the energy inequality and the GN/Young
mass-gradient eps-absorption interface. -/
theorem moser_iteration_chain_of_energy_dissipation_mass_gradient_relative
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T p0 rho : ℝ}
    (cGrad : ℝ → ℝ)
    (hrho : 0 < rho)
    (hbase : LpPowerBoundedBefore D p0 T u)
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
    (hmassToLp : MoserMassPowerToCurrentLpLowerOrder D u T rho p0) :
    ∀ n : ℕ, LpPowerBoundedBefore D (p0 + n * rho) T u := by
  exact moser_iteration_chain_of_energy_dissipation_relative_interpolation
    hrho hbase henergy hdiss
    (moser_relative_eps_absorption_family_of_mass_gradient_estimate
      cGrad hcGrad hMG hgrad hmassToLp)

/-- All finite exponents from the energy inequality and the GN/Young
mass-gradient eps-absorption interface. -/
theorem all_exponents_of_energy_dissipation_mass_gradient_relative_lpmono
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
    (hmassToLp : MoserMassPowerToCurrentLpLowerOrder D u T rho p0)
    (hLpMono :
      ∀ {p q : ℝ}, 1 < p → p ≤ q →
        LpPowerBoundedBefore D q T u → LpPowerBoundedBefore D p T u) :
    ∀ pExp > 1, LpPowerBoundedBefore D pExp T u := by
  exact all_exponents_of_energy_dissipation_relative_interpolation_lpmono
    hboot henergy hdiss
    (moser_relative_eps_absorption_family_of_mass_gradient_estimate
      cGrad hcGrad hMG hgrad hmassToLp)
    hLpMono

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

/-- Interval-domain relative eps-absorption family produced from the
mass-gradient interpolation estimate. -/
theorem intervalDomain_moser_relative_eps_absorption_family_of_mass_gradient_estimate
    {u : ℝ → intervalDomain.Point → ℝ} {T rho p0 : ℝ}
    (cGrad : ℝ → ℝ)
    (hcGrad : ∀ p, p0 ≤ p → 0 < cGrad p)
    (hMG : ∀ p, p0 ≤ p → ∀ eta > 0, ∃ Ceta,
      LpMassGradientInterpolationEstimate intervalDomain (p + rho) eta Ceta T u)
    (hgrad : ∀ p, p0 ≤ p → ∀ t, 0 < t → t < T →
      intervalDomain.integral (fun x =>
          (u t x) ^ (p + rho - 2) * (intervalDomain.gradNorm (u t) x) ^ 2) ≤
        cGrad p * intervalDomain.integral (fun x =>
          (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2))
    (hmassToLp : MoserMassPowerToCurrentLpLowerOrder intervalDomain u T rho p0) :
    ∀ p, p0 ≤ p → ∀ eps > 0, ∃ Ceps, 0 ≤ Ceps ∧
      ∀ t, 0 < t → t < T →
        intervalDomain.integral (fun x => (u t x) ^ (p + rho)) ≤
          eps * intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
          Ceps * intervalDomain.integral (fun x => (u t x) ^ p) := by
  exact moser_relative_eps_absorption_family_of_mass_gradient_estimate
    cGrad hcGrad hMG hgrad hmassToLp

/-- Interval-domain closure from the energy inequality and the relative
eps-absorption interface supplied by the mass-gradient estimate. -/
theorem intervalDomain_all_exponents_of_energy_dissipation_mass_gradient_relative
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
    (hmassToLp : MoserMassPowerToCurrentLpLowerOrder intervalDomain u T rho p0)
    (hu_nonneg :
      ∀ t, 0 < t → t < T → ∀ x : intervalDomain.Point, 0 ≤ u t x)
    (hpow_int :
      ∀ pExp : ℝ, 1 < pExp → ∀ t, 0 < t → t < T →
        IntervalIntegrable
          (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ pExp))
          MeasureTheory.volume 0 1) :
    ∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u := by
  exact IntervalDomainLpMonotonicity.intervalDomain_all_exponents_of_LpPowerBoundedBefore_chain
    (AbstractLpBootstrapHypothesis.rho_pos hboot)
    (moser_iteration_chain_of_energy_dissipation_relative_interpolation
      (AbstractLpBootstrapHypothesis.rho_pos hboot)
      (AbstractLpBootstrapHypothesis.initial_lp_bound hboot)
      henergy hdiss
      (intervalDomain_moser_relative_eps_absorption_family_of_mass_gradient_estimate
        cGrad hcGrad hMG hgrad hmassToLp))
    hu_nonneg hpow_int

/-- Interval-domain all-exponents Moser closure from the solution energy
inequality and the relative GN/Young absorption
`∫u^(p+ρ) <= eps * ∫|∇(u^(p/2))|^2 + Ceps * ∫u^p`.

This is the EnergyStep-side interface intended for the Theorem 1.1 Moser
iteration; it does not invoke the false abstract GN/Agmon endpoint envelope. -/
theorem intervalDomain_all_exponents_of_energy_dissipation_relative_interpolation
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
    (hrel : ∀ p, p0 ≤ p → ∀ eps > 0, ∃ Ceps, 0 ≤ Ceps ∧
      ∀ t, 0 < t → t < T →
        intervalDomain.integral (fun x => (u t x) ^ (p + rho)) ≤
          eps * intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
          Ceps * intervalDomain.integral (fun x => (u t x) ^ p))
    (hu_nonneg :
      ∀ t, 0 < t → t < T → ∀ x : intervalDomain.Point, 0 ≤ u t x)
    (hpow_int :
      ∀ pExp : ℝ, 1 < pExp → ∀ t, 0 < t → t < T →
        IntervalIntegrable
          (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ pExp))
          MeasureTheory.volume 0 1) :
    ∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u := by
  exact IntervalDomainLpMonotonicity.intervalDomain_all_exponents_of_LpPowerBoundedBefore_chain
    (AbstractLpBootstrapHypothesis.rho_pos hboot)
    (moser_iteration_chain_of_energy_dissipation_relative_interpolation
      (AbstractLpBootstrapHypothesis.rho_pos hboot)
      (AbstractLpBootstrapHypothesis.initial_lp_bound hboot)
      henergy hdiss hrel)
    hu_nonneg hpow_int

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

/-- Interior-nonnegative interval-domain closure from the energy inequality
and relative eps-absorption supplied by the mass-gradient estimate. -/
theorem intervalDomain_all_exponents_of_energy_dissipation_mass_gradient_relative_inside_nonneg
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
    (hmassToLp : MoserMassPowerToCurrentLpLowerOrder intervalDomain u T rho p0)
    (hu_nonneg :
      ∀ t, 0 < t → t < T →
        ∀ x : intervalDomain.Point, x ∈ intervalDomain.inside → 0 ≤ u t x)
    (hpow_int :
      ∀ pExp : ℝ, 1 < pExp → ∀ t, 0 < t → t < T →
        IntervalIntegrable
          (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ pExp))
          MeasureTheory.volume 0 1) :
    ∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u := by
  exact intervalDomain_all_exponents_of_LpPowerBoundedBefore_chain_inside_nonneg
    (AbstractLpBootstrapHypothesis.rho_pos hboot)
    (moser_iteration_chain_of_energy_dissipation_relative_interpolation
      (AbstractLpBootstrapHypothesis.rho_pos hboot)
      (AbstractLpBootstrapHypothesis.initial_lp_bound hboot)
      henergy hdiss
      (intervalDomain_moser_relative_eps_absorption_family_of_mass_gradient_estimate
        cGrad hcGrad hMG hgrad hmassToLp))
    hu_nonneg hpow_int

/-- Relative eps-absorption family using the Paper 2 Lemma 4.1 interface as
the source of mass-gradient interpolation. -/
theorem intervalDomain_moser_relative_eps_absorption_family_of_Lemma_4_1
    {params : CM2Params} {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ} {N T rho p0 : ℝ}
    (cGrad : ℝ → ℝ)
    (hboot : AbstractLpBootstrapHypothesis intervalDomain u N T rho p0)
    (hLemma41 : Lemma_4_1 intervalDomain params)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hcGrad : ∀ p, p0 ≤ p → 0 < cGrad p)
    (hgrad : ∀ p, p0 ≤ p → ∀ t, 0 < t → t < T →
      intervalDomain.integral (fun x =>
          (u t x) ^ (p + rho - 2) * (intervalDomain.gradNorm (u t) x) ^ 2) ≤
        cGrad p * intervalDomain.integral (fun x =>
          (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2))
    (hmassToLp : MoserMassPowerToCurrentLpLowerOrder intervalDomain u T rho p0) :
    ∀ p, p0 ≤ p → ∀ eps > 0, ∃ Ceps, 0 ≤ Ceps ∧
      ∀ t, 0 < t → t < T →
        intervalDomain.integral (fun x => (u t x) ^ (p + rho)) ≤
          eps * intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
          Ceps * intervalDomain.integral (fun x => (u t x) ^ p) := by
  refine intervalDomain_moser_relative_eps_absorption_family_of_mass_gradient_estimate
    cGrad hcGrad ?_ hgrad hmassToLp
  intro p hp eta heta
  have hp0_gt_one : 1 < p0 :=
    lt_of_le_of_lt (le_max_left 1 (rho * N / 2))
      (AbstractLpBootstrapHypothesis.p0_gt_threshold hboot)
  have hp_gt_one : 1 < p := lt_of_lt_of_le hp0_gt_one hp
  have hp_rho_gt_one : 1 < p + rho := by
    have hrho_pos := AbstractLpBootstrapHypothesis.rho_pos hboot
    linarith
  obtain ⟨Ceta, _hCeta_pos, hCeta⟩ :=
    hLemma41 u₀ hu₀ T (AbstractLpBootstrapHypothesis.T_pos hboot)
      u v hsol htrace eta heta (p + rho) hp_rho_gt_one
  exact ⟨Ceta, hCeta⟩

/-- Interval-domain all-exponents closure using Lemma 4.1 to supply the
relative eps-absorption interface for each Moser exponent. -/
theorem intervalDomain_all_exponents_of_energy_dissipation_Lemma_4_1_relative
    {params : CM2Params} {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ} {N T rho p0 : ℝ}
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
    (hLemma41 : Lemma_4_1 intervalDomain params)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hcGrad : ∀ p, p0 ≤ p → 0 < cGrad p)
    (hgrad : ∀ p, p0 ≤ p → ∀ t, 0 < t → t < T →
      intervalDomain.integral (fun x =>
          (u t x) ^ (p + rho - 2) * (intervalDomain.gradNorm (u t) x) ^ 2) ≤
        cGrad p * intervalDomain.integral (fun x =>
          (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2))
    (hmassToLp : MoserMassPowerToCurrentLpLowerOrder intervalDomain u T rho p0)
    (hu_nonneg :
      ∀ t, 0 < t → t < T → ∀ x : intervalDomain.Point, 0 ≤ u t x)
    (hpow_int :
      ∀ pExp : ℝ, 1 < pExp → ∀ t, 0 < t → t < T →
        IntervalIntegrable
          (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ pExp))
          MeasureTheory.volume 0 1) :
    ∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u := by
  exact intervalDomain_all_exponents_of_energy_dissipation_relative_interpolation
    hboot henergy hdiss
    (intervalDomain_moser_relative_eps_absorption_family_of_Lemma_4_1
      cGrad hboot hLemma41 hu₀ hsol htrace hcGrad hgrad hmassToLp)
    hu_nonneg hpow_int

/-- Interior-nonnegative version of
`intervalDomain_all_exponents_of_energy_dissipation_Lemma_4_1_relative`. -/
theorem intervalDomain_all_exponents_of_energy_dissipation_Lemma_4_1_relative_inside_nonneg
    {params : CM2Params} {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ} {N T rho p0 : ℝ}
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
    (hLemma41 : Lemma_4_1 intervalDomain params)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hcGrad : ∀ p, p0 ≤ p → 0 < cGrad p)
    (hgrad : ∀ p, p0 ≤ p → ∀ t, 0 < t → t < T →
      intervalDomain.integral (fun x =>
          (u t x) ^ (p + rho - 2) * (intervalDomain.gradNorm (u t) x) ^ 2) ≤
        cGrad p * intervalDomain.integral (fun x =>
          (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2))
    (hmassToLp : MoserMassPowerToCurrentLpLowerOrder intervalDomain u T rho p0)
    (hu_nonneg :
      ∀ t, 0 < t → t < T →
        ∀ x : intervalDomain.Point, x ∈ intervalDomain.inside → 0 ≤ u t x)
    (hpow_int :
      ∀ pExp : ℝ, 1 < pExp → ∀ t, 0 < t → t < T →
        IntervalIntegrable
          (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ pExp))
          MeasureTheory.volume 0 1) :
    ∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u := by
  exact intervalDomain_all_exponents_of_LpPowerBoundedBefore_chain_inside_nonneg
    (AbstractLpBootstrapHypothesis.rho_pos hboot)
    (moser_iteration_chain_of_energy_dissipation_relative_interpolation
      (AbstractLpBootstrapHypothesis.rho_pos hboot)
      (AbstractLpBootstrapHypothesis.initial_lp_bound hboot)
      henergy hdiss
      (intervalDomain_moser_relative_eps_absorption_family_of_Lemma_4_1
        cGrad hboot hLemma41 hu₀ hsol htrace hcGrad hgrad hmassToLp))
    hu_nonneg hpow_int

/-- Interior-nonnegative version of the relative-interpolation Moser closure. -/
theorem intervalDomain_all_exponents_of_energy_dissipation_relative_interpolation_inside_nonneg
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
    (hrel : ∀ p, p0 ≤ p → ∀ eps > 0, ∃ Ceps, 0 ≤ Ceps ∧
      ∀ t, 0 < t → t < T →
        intervalDomain.integral (fun x => (u t x) ^ (p + rho)) ≤
          eps * intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
          Ceps * intervalDomain.integral (fun x => (u t x) ^ p))
    (hu_nonneg :
      ∀ t, 0 < t → t < T →
        ∀ x : intervalDomain.Point, x ∈ intervalDomain.inside → 0 ≤ u t x)
    (hpow_int :
      ∀ pExp : ℝ, 1 < pExp → ∀ t, 0 < t → t < T →
        IntervalIntegrable
          (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ pExp))
          MeasureTheory.volume 0 1) :
    ∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u := by
  exact intervalDomain_all_exponents_of_LpPowerBoundedBefore_chain_inside_nonneg
    (AbstractLpBootstrapHypothesis.rho_pos hboot)
    (moser_iteration_chain_of_energy_dissipation_relative_interpolation
      (AbstractLpBootstrapHypothesis.rho_pos hboot)
      (AbstractLpBootstrapHypothesis.initial_lp_bound hboot)
      henergy hdiss hrel)
    hu_nonneg hpow_int

/-! ### Bridges to the structured relative-Moser endpoint API -/

/-- Package the raw EnergyStep dissipation/drop interface as the named
`MoserClosure` field. -/
theorem moserClosure_dissipationDropBefore_of_raw
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T rho p0 : ℝ}
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
            B * D.integral (fun x => (u t x) ^ p)) :
    IntervalDomainMoserClosure.MoserDissipationDropBefore D u T rho p0 := by
  intro p hp A B K L_const hfull t ht0 htT
  exact hdiss p hp A B K L_const hfull t ht0 htT

/-- Package the raw relative eps-absorption interface as the named
`MoserClosure` field. -/
theorem moserClosure_relativeInterpolationBefore_of_raw
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T rho p0 : ℝ}
    (hrel : ∀ p, p0 ≤ p → ∀ eps > 0, ∃ Ceps, 0 ≤ Ceps ∧
      ∀ t, 0 < t → t < T →
        D.integral (fun x => (u t x) ^ (p + rho)) ≤
          eps * D.integral (fun x =>
            (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
          Ceps * D.integral (fun x => (u t x) ^ p)) :
    IntervalDomainMoserClosure.RelativeMoserInterpolationBefore D u T rho p0 := by
  intro p hp eps heps
  exact hrel p hp eps heps

/-- The EnergyStep mass-gradient eps-absorption family supplies the named
relative-interpolation field used by the structured Moser endpoint route. -/
theorem moserClosure_relativeInterpolationBefore_of_mass_gradient_estimate
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T rho p0 : ℝ}
    (cGrad : ℝ → ℝ)
    (hcGrad : ∀ p, p0 ≤ p → 0 < cGrad p)
    (hMG : ∀ p, p0 ≤ p → ∀ eta > 0, ∃ Ceta,
      LpMassGradientInterpolationEstimate D (p + rho) eta Ceta T u)
    (hgrad : ∀ p, p0 ≤ p → ∀ t, 0 < t → t < T →
      D.integral (fun x =>
          (u t x) ^ (p + rho - 2) * (D.gradNorm (u t) x) ^ 2) ≤
        cGrad p * D.integral (fun x =>
          (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2))
    (hmassToLp : MoserMassPowerToCurrentLpLowerOrder D u T rho p0) :
    IntervalDomainMoserClosure.RelativeMoserInterpolationBefore D u T rho p0 :=
  moserClosure_relativeInterpolationBefore_of_raw
    (moser_relative_eps_absorption_family_of_mass_gradient_estimate
      cGrad hcGrad hMG hgrad hmassToLp)

/-- Interval-domain named relative-interpolation field from the mass-gradient
estimate. -/
theorem intervalDomain_moserClosure_relativeInterpolationBefore_of_mass_gradient_estimate
    {u : ℝ → intervalDomain.Point → ℝ} {T rho p0 : ℝ}
    (cGrad : ℝ → ℝ)
    (hcGrad : ∀ p, p0 ≤ p → 0 < cGrad p)
    (hMG : ∀ p, p0 ≤ p → ∀ eta > 0, ∃ Ceta,
      LpMassGradientInterpolationEstimate intervalDomain (p + rho) eta Ceta T u)
    (hgrad : ∀ p, p0 ≤ p → ∀ t, 0 < t → t < T →
      intervalDomain.integral (fun x =>
          (u t x) ^ (p + rho - 2) * (intervalDomain.gradNorm (u t) x) ^ 2) ≤
        cGrad p * intervalDomain.integral (fun x =>
          (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2))
    (hmassToLp : MoserMassPowerToCurrentLpLowerOrder intervalDomain u T rho p0) :
    IntervalDomainMoserClosure.RelativeMoserInterpolationBefore
      intervalDomain u T rho p0 :=
  moserClosure_relativeInterpolationBefore_of_mass_gradient_estimate
    cGrad hcGrad hMG hgrad hmassToLp

/-- Interval-domain named relative-interpolation field using Paper 2
Lemma 4.1 as the source of the mass-gradient interpolation estimate. -/
theorem intervalDomain_moserClosure_relativeInterpolationBefore_of_Lemma_4_1
    {params : CM2Params} {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ} {N T rho p0 : ℝ}
    (cGrad : ℝ → ℝ)
    (hboot : AbstractLpBootstrapHypothesis intervalDomain u N T rho p0)
    (hLemma41 : Lemma_4_1 intervalDomain params)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hcGrad : ∀ p, p0 ≤ p → 0 < cGrad p)
    (hgrad : ∀ p, p0 ≤ p → ∀ t, 0 < t → t < T →
      intervalDomain.integral (fun x =>
          (u t x) ^ (p + rho - 2) * (intervalDomain.gradNorm (u t) x) ^ 2) ≤
        cGrad p * intervalDomain.integral (fun x =>
          (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2))
    (hmassToLp : MoserMassPowerToCurrentLpLowerOrder intervalDomain u T rho p0) :
    IntervalDomainMoserClosure.RelativeMoserInterpolationBefore
      intervalDomain u T rho p0 :=
  moserClosure_relativeInterpolationBefore_of_raw
    (intervalDomain_moser_relative_eps_absorption_family_of_Lemma_4_1
      cGrad hboot hLemma41 hu₀ hsol htrace hcGrad hgrad hmassToLp)

/-- Build the component package expected by
`Theorem_1_1_intervalDomain_of_relative_moser_endpoint_components` from the
EnergyStep-side named fields. -/
def intervalDomain_relativeMoserEndpointComponents_of_energy_interfaces
    {u : ℝ → intervalDomain.Point → ℝ} {N T rho p0 : ℝ}
    {pSeq rootBound : ℕ → ℝ}
    (hboot : AbstractLpBootstrapHypothesis intervalDomain u N T rho p0)
    (henergy : LpBootstrapEnergyInequality intervalDomain u T rho p0)
    (hdiss : IntervalDomainMoserClosure.MoserDissipationDropBefore
      intervalDomain u T rho p0)
    (hrel : IntervalDomainMoserClosure.RelativeMoserInterpolationBefore
      intervalDomain u T rho p0)
    (hLpMono :
      ∀ {p q : ℝ}, 1 < p → p ≤ q →
        LpPowerBoundedBefore intervalDomain q T u →
        LpPowerBoundedBefore intervalDomain p T u)
    (hEndpoint :
      (∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u) →
        IntervalDomainMoserClosure.IntervalDomainMoserQuantitativeEndpoint
          u T pSeq rootBound) :
    IntervalDomainMoserClosure.IntervalDomainRelativeMoserEndpointComponents u T := by
  exact
    { N := N
      rho := rho
      p0 := p0
      pSeq := pSeq
      rootBound := rootBound
      boot := hboot
      energy := henergy
      dissipation := hdiss
      relativeInterpolation := hrel
      lpMono := hLpMono
      endpoint := hEndpoint }

/-- Same component package, starting from the raw EnergyStep dissipation and
relative-interpolation hypotheses. -/
def intervalDomain_relativeMoserEndpointComponents_of_raw_energy_relative
    {u : ℝ → intervalDomain.Point → ℝ} {N T rho p0 : ℝ}
    {pSeq rootBound : ℕ → ℝ}
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
    (hrel : ∀ p, p0 ≤ p → ∀ eps > 0, ∃ Ceps, 0 ≤ Ceps ∧
      ∀ t, 0 < t → t < T →
        intervalDomain.integral (fun x => (u t x) ^ (p + rho)) ≤
          eps * intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
          Ceps * intervalDomain.integral (fun x => (u t x) ^ p))
    (hLpMono :
      ∀ {p q : ℝ}, 1 < p → p ≤ q →
        LpPowerBoundedBefore intervalDomain q T u →
        LpPowerBoundedBefore intervalDomain p T u)
    (hEndpoint :
      (∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u) →
        IntervalDomainMoserClosure.IntervalDomainMoserQuantitativeEndpoint
          u T pSeq rootBound) :
    IntervalDomainMoserClosure.IntervalDomainRelativeMoserEndpointComponents u T :=
  intervalDomain_relativeMoserEndpointComponents_of_energy_interfaces
    hboot henergy
    (moserClosure_dissipationDropBefore_of_raw hdiss)
    (moserClosure_relativeInterpolationBefore_of_raw hrel)
    hLpMono hEndpoint

/-- Component package when the `LpBootstrapEnergyInequality` is obtained from
the cross-diffusion bootstrap estimate. -/
def intervalDomain_relativeMoserEndpointComponents_of_crossDiffusion_energy_interfaces
    {params : CM2Params}
    {u v : ℝ → intervalDomain.Point → ℝ} {T rho p0 : ℝ}
    {pSeq rootBound : ℕ → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0)
    (hEnergyFromCrossDiffusion :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain params T u v →
        CrossDiffusionBootstrapEstimate intervalDomain params T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0 →
          LpBootstrapEnergyInequality intervalDomain u T rho p0)
    (hdiss : IntervalDomainMoserClosure.MoserDissipationDropBefore
      intervalDomain u T rho p0)
    (hrel : IntervalDomainMoserClosure.RelativeMoserInterpolationBefore
      intervalDomain u T rho p0)
    (hLpMono :
      ∀ {p q : ℝ}, 1 < p → p ≤ q →
        LpPowerBoundedBefore intervalDomain q T u →
        LpPowerBoundedBefore intervalDomain p T u)
    (hEndpoint :
      (∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u) →
        IntervalDomainMoserClosure.IntervalDomainMoserQuantitativeEndpoint
          u T pSeq rootBound) :
    IntervalDomainMoserClosure.IntervalDomainRelativeMoserEndpointComponents u T :=
  intervalDomain_relativeMoserEndpointComponents_of_energy_interfaces
    hboot (hEnergyFromCrossDiffusion hsol hcross hboot)
    hdiss hrel hLpMono hEndpoint

/-- Cross-diffusion version with raw EnergyStep dissipation and
relative-interpolation inputs. -/
def intervalDomain_relativeMoserEndpointComponents_of_crossDiffusion_raw_energy_relative
    {params : CM2Params}
    {u v : ℝ → intervalDomain.Point → ℝ} {T rho p0 : ℝ}
    {pSeq rootBound : ℕ → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0)
    (hEnergyFromCrossDiffusion :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain params T u v →
        CrossDiffusionBootstrapEstimate intervalDomain params T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0 →
          LpBootstrapEnergyInequality intervalDomain u T rho p0)
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
    (hrel : ∀ p, p0 ≤ p → ∀ eps > 0, ∃ Ceps, 0 ≤ Ceps ∧
      ∀ t, 0 < t → t < T →
        intervalDomain.integral (fun x => (u t x) ^ (p + rho)) ≤
          eps * intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
          Ceps * intervalDomain.integral (fun x => (u t x) ^ p))
    (hLpMono :
      ∀ {p q : ℝ}, 1 < p → p ≤ q →
        LpPowerBoundedBefore intervalDomain q T u →
        LpPowerBoundedBefore intervalDomain p T u)
    (hEndpoint :
      (∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u) →
        IntervalDomainMoserClosure.IntervalDomainMoserQuantitativeEndpoint
          u T pSeq rootBound) :
    IntervalDomainMoserClosure.IntervalDomainRelativeMoserEndpointComponents u T :=
  intervalDomain_relativeMoserEndpointComponents_of_crossDiffusion_energy_interfaces
    hsol hcross hboot hEnergyFromCrossDiffusion
    (moserClosure_dissipationDropBefore_of_raw hdiss)
    (moserClosure_relativeInterpolationBefore_of_raw hrel)
    hLpMono hEndpoint

/-- Component package with relative interpolation supplied by Lemma 4.1. -/
def intervalDomain_relativeMoserEndpointComponents_of_Lemma_4_1_energy
    {params : CM2Params} {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ} {N T rho p0 : ℝ}
    {pSeq rootBound : ℕ → ℝ}
    (cGrad : ℝ → ℝ)
    (hboot : AbstractLpBootstrapHypothesis intervalDomain u N T rho p0)
    (henergy : LpBootstrapEnergyInequality intervalDomain u T rho p0)
    (hdiss : IntervalDomainMoserClosure.MoserDissipationDropBefore
      intervalDomain u T rho p0)
    (hLemma41 : Lemma_4_1 intervalDomain params)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hcGrad : ∀ p, p0 ≤ p → 0 < cGrad p)
    (hgrad : ∀ p, p0 ≤ p → ∀ t, 0 < t → t < T →
      intervalDomain.integral (fun x =>
          (u t x) ^ (p + rho - 2) * (intervalDomain.gradNorm (u t) x) ^ 2) ≤
        cGrad p * intervalDomain.integral (fun x =>
          (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2))
    (hmassToLp : MoserMassPowerToCurrentLpLowerOrder intervalDomain u T rho p0)
    (hLpMono :
      ∀ {p q : ℝ}, 1 < p → p ≤ q →
        LpPowerBoundedBefore intervalDomain q T u →
        LpPowerBoundedBefore intervalDomain p T u)
    (hEndpoint :
      (∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u) →
        IntervalDomainMoserClosure.IntervalDomainMoserQuantitativeEndpoint
          u T pSeq rootBound) :
    IntervalDomainMoserClosure.IntervalDomainRelativeMoserEndpointComponents u T :=
  intervalDomain_relativeMoserEndpointComponents_of_energy_interfaces
    hboot henergy hdiss
    (intervalDomain_moserClosure_relativeInterpolationBefore_of_Lemma_4_1
      cGrad hboot hLemma41 hu₀ hsol htrace hcGrad hgrad hmassToLp)
    hLpMono hEndpoint

/-- Cross-diffusion component package with relative interpolation supplied by
Lemma 4.1. -/
def intervalDomain_relativeMoserEndpointComponents_of_crossDiffusion_Lemma_4_1_energy
    {params : CM2Params} {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ} {T rho p0 : ℝ}
    {pSeq rootBound : ℕ → ℝ}
    (cGrad : ℝ → ℝ)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0)
    (hEnergyFromCrossDiffusion :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain params T u v →
        CrossDiffusionBootstrapEstimate intervalDomain params T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0 →
          LpBootstrapEnergyInequality intervalDomain u T rho p0)
    (hdiss : IntervalDomainMoserClosure.MoserDissipationDropBefore
      intervalDomain u T rho p0)
    (hLemma41 : Lemma_4_1 intervalDomain params)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hcGrad : ∀ p, p0 ≤ p → 0 < cGrad p)
    (hgrad : ∀ p, p0 ≤ p → ∀ t, 0 < t → t < T →
      intervalDomain.integral (fun x =>
          (u t x) ^ (p + rho - 2) * (intervalDomain.gradNorm (u t) x) ^ 2) ≤
        cGrad p * intervalDomain.integral (fun x =>
          (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2))
    (hmassToLp : MoserMassPowerToCurrentLpLowerOrder intervalDomain u T rho p0)
    (hLpMono :
      ∀ {p q : ℝ}, 1 < p → p ≤ q →
        LpPowerBoundedBefore intervalDomain q T u →
        LpPowerBoundedBefore intervalDomain p T u)
    (hEndpoint :
      (∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u) →
        IntervalDomainMoserClosure.IntervalDomainMoserQuantitativeEndpoint
          u T pSeq rootBound) :
    IntervalDomainMoserClosure.IntervalDomainRelativeMoserEndpointComponents u T :=
  intervalDomain_relativeMoserEndpointComponents_of_Lemma_4_1_energy
    cGrad hboot (hEnergyFromCrossDiffusion hsol hcross hboot) hdiss
    hLemma41 hu₀ hsol htrace hcGrad hgrad hmassToLp hLpMono hEndpoint

/-- Structured-data package for the `hnonminimalMoser`/`hminimalMoser` route
from the same EnergyStep-side inputs. -/
def intervalDomain_structuredMoserBootstrapData_of_energy_interfaces
    {u : ℝ → intervalDomain.Point → ℝ} {N T rho p0 : ℝ}
    {pSeq rootBound : ℕ → ℝ}
    (hboot : AbstractLpBootstrapHypothesis intervalDomain u N T rho p0)
    (henergy : LpBootstrapEnergyInequality intervalDomain u T rho p0)
    (hdiss : IntervalDomainMoserClosure.MoserDissipationDropBefore
      intervalDomain u T rho p0)
    (hrel : IntervalDomainMoserClosure.RelativeMoserInterpolationBefore
      intervalDomain u T rho p0)
    (hLpMono :
      ∀ {p q : ℝ}, 1 < p → p ≤ q →
        LpPowerBoundedBefore intervalDomain q T u →
        LpPowerBoundedBefore intervalDomain p T u)
    (hEndpoint :
      (∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u) →
        IntervalDomainMoserClosure.IntervalDomainMoserQuantitativeEndpoint
          u T pSeq rootBound) :
    IntervalDomainMoserClosure.IntervalDomainStructuredMoserBootstrapData u T :=
  (intervalDomain_relativeMoserEndpointComponents_of_energy_interfaces
    hboot henergy hdiss hrel hLpMono hEndpoint).toStructuredData

/-- Structured-data package from raw EnergyStep hypotheses. -/
def intervalDomain_structuredMoserBootstrapData_of_raw_energy_relative
    {u : ℝ → intervalDomain.Point → ℝ} {N T rho p0 : ℝ}
    {pSeq rootBound : ℕ → ℝ}
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
    (hrel : ∀ p, p0 ≤ p → ∀ eps > 0, ∃ Ceps, 0 ≤ Ceps ∧
      ∀ t, 0 < t → t < T →
        intervalDomain.integral (fun x => (u t x) ^ (p + rho)) ≤
          eps * intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
          Ceps * intervalDomain.integral (fun x => (u t x) ^ p))
    (hLpMono :
      ∀ {p q : ℝ}, 1 < p → p ≤ q →
        LpPowerBoundedBefore intervalDomain q T u →
        LpPowerBoundedBefore intervalDomain p T u)
    (hEndpoint :
      (∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u) →
        IntervalDomainMoserClosure.IntervalDomainMoserQuantitativeEndpoint
          u T pSeq rootBound) :
    IntervalDomainMoserClosure.IntervalDomainStructuredMoserBootstrapData u T :=
  (intervalDomain_relativeMoserEndpointComponents_of_raw_energy_relative
    hboot henergy hdiss hrel hLpMono hEndpoint).toStructuredData

end ShenWork.Paper2.IntervalDomainEnergyStep

end
