/-
  ShenWork/Paper2/IntervalDomainLem26PhaseA.lean

  Solution-local discharge of the routine/standard hypotheses used by the
  interval-domain Lemma 2.6 Moser closure.

  The abstract statement `Lemma_2_6 intervalDomain` quantifies over arbitrary
  bootstrap functions and therefore cannot recover classical regularity from
  its hypotheses.  This module works at the concrete solution layer, where an
  `IsPaper2ClassicalSolution` is available.  The two intentionally remaining
  inputs are the dissipation and gradient-chain frontiers.
-/
import ShenWork.Paper2.IntervalDomainTheorem11
import ShenWork.PDE.P3MoserRelativeMassGradientProducer

set_option linter.style.longLine false

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalDomainExistence.P3MoserRelativeMassGradientProducer
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality

namespace ShenWork.Paper2.IntervalDomainLem26PhaseA

noncomputable section

/-! ## A3: a guarded gradient coefficient -/

/-- Shape of the gradient coefficient in the Theorem 1.1 frontier. -/
abbrev CGradShape :=
  (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ

/-- Add a positive guard to any proposed raw gradient coefficient.

The later `hgrad` producer should target this guarded coefficient. -/
def guardedCGrad (raw : CGradShape) : CGradShape :=
  fun u T rho p0 pExp => max 0 (raw u T rho p0 pExp) + 1

theorem guardedCGrad_point_pos
    (raw : CGradShape)
    (u : ℝ → intervalDomain.Point → ℝ) (T rho p0 pExp : ℝ) :
    0 < guardedCGrad raw u T rho p0 pExp := by
  dsimp [guardedCGrad]
  have hnonneg : 0 ≤ max 0 (raw u T rho p0 pExp) := le_max_left _ _
  linarith

/-- A3 in the exact globally quantified shape used by the thin frontier. -/
theorem guardedCGrad_pos
    (raw : CGradShape) :
    ∀ {N T rho p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ},
      AbstractLpBootstrapHypothesis intervalDomain u N T rho p0 →
      LpBootstrapEnergyInequality intervalDomain u T rho p0 →
      ∀ pExp, p0 ≤ pExp →
        0 < guardedCGrad raw u T rho p0 pExp := by
  intro N T rho p0 u _hboot _henergy pExp _hpExp
  exact guardedCGrad_point_pos raw u T rho p0 pExp

/-! ## A1 and A2: positivity and power integrability -/

/-- A1: closed-domain nonnegativity of every positive-time solution slice. -/
theorem solution_u_nonneg
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    ∀ t, 0 < t → t < T → ∀ x : intervalDomain.Point, 0 ≤ u t x := by
  intro t ht0 htT x
  exact (hsol.u_pos' ht0 htT).le

/-- A2: all real powers of a positive classical slice are integrable on
the compact unit interval. -/
theorem solution_pow_intervalIntegrable
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    ∀ pExp : ℝ, 1 < pExp → ∀ t, 0 < t → t < T →
      IntervalIntegrable
        (intervalDomainLift
          (fun x : intervalDomain.Point => (u t x) ^ pExp))
        volume 0 1 := by
  intro pExp _hpExp t ht0 htT
  exact intervalDomain_u_rpow_intervalIntegrable_of_regularity
    (q := pExp) hsol ht0 htT

/-! ## A4: the existing uniform interval Agmon estimate -/

/-- A4, wired to the existing uniform positive-slice Agmon producer. -/
theorem solution_massGradientInterpolation
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0) :
    ∀ pExp, p0 ≤ pExp → ∀ eta > 0, ∃ Ceta,
      LpMassGradientInterpolationEstimate intervalDomain
        (pExp + rho) eta Ceta T u := by
  exact intervalDomain_massGradientInterpolation_of_classical hsol hcross hboot

/-! ## A5: solution-local mass control with the frontier's inner quantifier order -/

private theorem p0_gt_one_of_bootstrap
    {params : CM2Params} {T rho p0 : ℝ}
    {u : ℝ → intervalDomain.Point → ℝ}
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0) :
    1 < p0 := by
  have hthreshold := AbstractLpBootstrapHypothesis.p0_gt_threshold hboot
  have hone_le :
      (1 : ℝ) ≤ max 1 (rho * (params.N : ℝ) / 2) := le_max_left _ _
  linarith

/-- Any finite-horizon uniform mass bound supplies the inner
`forall p, forall Ceta, exists Cmass, forall t` tail required by the Lemma 2.6
mass-control frontier.  In particular, an alternate model with a linear
(`theta = 1`) reaction may supply its finite-horizon exponential bound here;
the resulting `Cmass` is allowed to depend on `T`. -/
theorem massControl_of_uniform_mass_bound
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0)
    {M : ℝ} (_hM_nonneg : 0 ≤ M)
    (hM : ∀ t, 0 < t → t < T → intervalDomain.integral (u t) ≤ M) :
    ∀ pExp, p0 ≤ pExp → ∀ Ceta, ∃ Cmass,
      ∀ t, 0 < t → t < T →
        Ceta * (intervalDomain.integral (u t)) ^ (pExp + rho) ≤ Cmass := by
  intro pExp hpExp Ceta
  let Cmass : ℝ := max Ceta 0 * M ^ (pExp + rho)
  refine ⟨Cmass, ?_⟩
  intro t ht0 htT
  have hp0_gt_one : 1 < p0 := p0_gt_one_of_bootstrap hboot
  have hpExp_gt_one : 1 < pExp := lt_of_lt_of_le hp0_gt_one hpExp
  have hrho_pos : 0 < rho := AbstractLpBootstrapHypothesis.rho_pos hboot
  have hq_nonneg : 0 ≤ pExp + rho := by linarith
  have hmass_nonneg : 0 ≤ intervalDomain.integral (u t) :=
    (intervalDomain_classicalSolution_mass_pos hsol ⟨ht0, htT⟩).le
  have hrpow_le :
      (intervalDomain.integral (u t)) ^ (pExp + rho) ≤
        M ^ (pExp + rho) :=
    Real.rpow_le_rpow hmass_nonneg (hM t ht0 htT) hq_nonneg
  have hmass_pow_nonneg :
      0 ≤ (intervalDomain.integral (u t)) ^ (pExp + rho) :=
    Real.rpow_nonneg hmass_nonneg _
  calc
    Ceta * (intervalDomain.integral (u t)) ^ (pExp + rho)
        ≤ max Ceta 0 * (intervalDomain.integral (u t)) ^ (pExp + rho) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hmass_pow_nonneg
    _ ≤ max Ceta 0 * M ^ (pExp + rho) :=
      mul_le_mul_of_nonneg_left hrpow_le (le_max_right _ _)
    _ = Cmass := rfl

/-- A5 without extra initial-trace parameters.  The bootstrap already contains
a uniform `L^p0` bound; on the unit interval it bounds the mass by `C0 + 1`.
This route covers every nonnegative choice of the logistic coefficients. -/
theorem solution_massControl_of_bootstrap
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0) :
    ∀ pExp, p0 ≤ pExp → ∀ Ceta, ∃ Cmass,
      ∀ t, 0 < t → t < T →
        Ceta * (intervalDomain.integral (u t)) ^ (pExp + rho) ≤ Cmass := by
  obtain ⟨C0, hC0⟩ := AbstractLpBootstrapHypothesis.initial_lp_bound hboot
  have hp0_one : 1 ≤ p0 := (p0_gt_one_of_bootstrap hboot).le
  let M : ℝ := max (C0 + 1) 1
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact le_trans zero_le_one (le_max_right _ _)
  have hmass :
      ∀ t, 0 < t → t < T → intervalDomain.integral (u t) ≤ M := by
    intro t ht0 htT
    have hseed := intervalDomain_mass_le_seed_plus_one_of_classical
      (params := params) (T := T) (t := t) (p0 := p0)
      (u := u) (v := v) hsol ht0 htT hp0_one
    calc
      intervalDomain.integral (u t)
          ≤ intervalDomain.integral (fun x => (u t x) ^ p0) + 1 := hseed
      _ ≤ C0 + 1 := by linarith [hC0 t ht0 htT]
      _ ≤ M := le_max_left _ _
  exact massControl_of_uniform_mass_bound hsol hboot hM_nonneg hmass

/-! ### Physical mass route through Proposition 2.4 -/

/-- The concrete reaction mass exponent is strictly above one. -/
theorem logisticMassExponent_gt_one (params : CM2Params) :
    1 < 1 + params.α := by
  linarith [params.hα]

/-- Consequently the `theta = 1` case is not inhabited by `CM2Params`.
`massControl_of_uniform_mass_bound` records the finite-horizon interface that
would consume the exponential estimate in a model permitting that case. -/
theorem logisticMassExponent_ne_one (params : CM2Params) :
    1 + params.α ≠ 1 :=
  ne_of_gt (logisticMassExponent_gt_one params)

/-- Uniform mass bound from the already-proved physical mass theorem.

`intervalDomain_Proposition_2_4` is assembled from the exact mass derivative
identity (Neumann cancellation of the Laplacian and chemotaxis flux), unit
interval Jensen, and scalar mass comparison. -/
theorem solution_uniformMassBound_of_proposition24_branches
    {params : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hbranch :
      (params.a = 0 ∧ params.b = 0) ∨ (0 < params.a ∧ 0 < params.b)) :
    ∃ M, 0 ≤ M ∧
      ∀ t, 0 < t → t < T → intervalDomain.integral (u t) ≤ M := by
  have hprop := intervalDomain_Proposition_2_4 params
    u₀ hu₀ T hsol.T_pos u v hsol htrace
  rcases hbranch with hzero | hpos
  · let M : ℝ := max (intervalDomain.integral u₀) 0
    refine ⟨M, le_max_right _ _, ?_⟩
    intro t ht0 htT
    have heq := (hprop.1 hzero.1 hzero.2) t ht0 htT
    rw [heq]
    exact le_max_left _ _
  · let K : ℝ :=
      max (intervalDomain.integral u₀)
        (((params.a / params.b) ^ (1 / params.α)) * intervalDomain.volume)
    let M : ℝ := max K 0
    refine ⟨M, le_max_right _ _, ?_⟩
    intro t ht0 htT
    have hle := (hprop.2 hpos.1 hpos.2) t ht0 htT
    exact hle.trans (le_max_left _ _)

/-- A5 through the physical Proposition 2.4 route, for the two parameter
branches used by the Paper 2 theorem assembly. -/
theorem solution_massControl_of_proposition24_branches
    {params : CM2Params} {T rho p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0)
    (hbranch :
      (params.a = 0 ∧ params.b = 0) ∨ (0 < params.a ∧ 0 < params.b)) :
    ∀ pExp, p0 ≤ pExp → ∀ Ceta, ∃ Cmass,
      ∀ t, 0 < t → t < T →
        Ceta * (intervalDomain.integral (u t)) ^ (pExp + rho) ≤ Cmass := by
  obtain ⟨M, hM_nonneg, hM⟩ :=
    solution_uniformMassBound_of_proposition24_branches
      hu₀ hsol htrace hbranch
  exact massControl_of_uniform_mass_bound hsol hboot hM_nonneg hM

/-! ## Bundled Phase A data and concrete closure -/

/-- The five solution-local hypotheses discharged in Phase A. -/
structure SolutionPhaseAData
    (raw : CGradShape)
    (u : ℝ → intervalDomain.Point → ℝ) (T rho p0 : ℝ) : Prop where
  hcGrad : ∀ pExp, p0 ≤ pExp →
    0 < guardedCGrad raw u T rho p0 pExp
  hMG : ∀ pExp, p0 ≤ pExp → ∀ eta > 0, ∃ Ceta,
    LpMassGradientInterpolationEstimate intervalDomain
      (pExp + rho) eta Ceta T u
  hmass : ∀ pExp, p0 ≤ pExp → ∀ Ceta, ∃ Cmass,
    ∀ t, 0 < t → t < T →
      Ceta * (intervalDomain.integral (u t)) ^ (pExp + rho) ≤ Cmass
  hu_nonneg : ∀ t, 0 < t → t < T →
    ∀ x : intervalDomain.Point, 0 ≤ u t x
  hpow_int : ∀ pExp : ℝ, 1 < pExp → ∀ t, 0 < t → t < T →
    IntervalIntegrable
      (intervalDomainLift
        (fun x : intervalDomain.Point => (u t x) ^ pExp))
      volume 0 1

/-- Produce all five Phase A fields for a concrete classical solution. -/
theorem solutionPhaseAData_of_classical
    (raw : CGradShape)
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0) :
    SolutionPhaseAData raw u T rho p0 where
  hcGrad := fun pExp _hpExp => guardedCGrad_point_pos raw u T rho p0 pExp
  hMG := solution_massGradientInterpolation hsol hcross hboot
  hmass := solution_massControl_of_bootstrap hsol hboot
  hu_nonneg := solution_u_nonneg hsol
  hpow_int := solution_pow_intervalIntegrable hsol

/-- Concrete Lemma 2.6 closure after Phase A: only `hdiss` and `hgrad` remain.
Neither is proved or weakened in this module. -/
theorem classicalSolution_all_exponents_of_phaseA
    (raw : CGradShape)
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0)
    (henergy : LpBootstrapEnergyInequality intervalDomain u T rho p0)
    (hdiss : ∀ pExp, p0 ≤ pExp → ∀ A B K L_const,
      (∀ t, 0 < t → t < T →
        (1 / pExp) * deriv
            (fun τ => intervalDomain.integral (fun x => (u τ x) ^ pExp)) t +
          A * intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm (fun y => (u t y) ^ (pExp / 2)) x) ^ 2) +
          B * intervalDomain.integral (fun x => (u t x) ^ pExp) ≤
        K * intervalDomain.integral (fun x => (u t x) ^ (pExp + rho)) + L_const) →
      ∀ t, 0 < t → t < T →
        0 ≤
          (1 / pExp) * deriv
              (fun τ => intervalDomain.integral (fun x => (u τ x) ^ pExp)) t +
            B * intervalDomain.integral (fun x => (u t x) ^ pExp))
    (hgrad : ∀ pExp, p0 ≤ pExp → ∀ t, 0 < t → t < T →
      intervalDomain.integral (fun x =>
          (u t x) ^ (pExp + rho - 2) * (intervalDomain.gradNorm (u t) x) ^ 2) ≤
        guardedCGrad raw u T rho p0 pExp * intervalDomain.integral (fun x =>
          (intervalDomain.gradNorm (fun y => (u t y) ^ (pExp / 2)) x) ^ 2)) :
    ∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u := by
  let H : SolutionPhaseAData raw u T rho p0 :=
    solutionPhaseAData_of_classical raw hsol hcross hboot
  exact intervalDomain_all_exponents_of_energy_dissipation_mass_gradient
    (guardedCGrad raw u T rho p0) hboot henergy hdiss
    H.hcGrad H.hMG hgrad H.hmass H.hu_nonneg H.hpow_int

/-! ### Corollary-facing solution-local wiring -/

/-- Solution-local form of the two residual analytic frontiers. -/
abbrev ClassicalSolutionDissipationGradientFrontier
    (params : CM2Params) (raw : CGradShape) : Prop :=
  ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
    IsPaper2ClassicalSolution intervalDomain params T u v →
    CrossDiffusionBootstrapEstimate intervalDomain params T rho u v →
    AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0 →
    LpBootstrapEnergyInequality intervalDomain u T rho p0 →
      (∀ pExp, p0 ≤ pExp → ∀ A B K L_const,
        (∀ t, 0 < t → t < T →
          (1 / pExp) * deriv
              (fun τ => intervalDomain.integral (fun x => (u τ x) ^ pExp)) t +
            A * intervalDomain.integral (fun x =>
              (intervalDomain.gradNorm (fun y => (u t y) ^ (pExp / 2)) x) ^ 2) +
            B * intervalDomain.integral (fun x => (u t x) ^ pExp) ≤
          K * intervalDomain.integral (fun x => (u t x) ^ (pExp + rho)) + L_const) →
        ∀ t, 0 < t → t < T →
          0 ≤
            (1 / pExp) * deriv
                (fun τ => intervalDomain.integral (fun x => (u τ x) ^ pExp)) t +
              B * intervalDomain.integral (fun x => (u t x) ^ pExp)) ∧
      (∀ pExp, p0 ≤ pExp → ∀ t, 0 < t → t < T →
        intervalDomain.integral (fun x =>
            (u t x) ^ (pExp + rho - 2) *
              (intervalDomain.gradNorm (u t) x) ^ 2) ≤
          guardedCGrad raw u T rho p0 pExp * intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm (fun y => (u t y) ^ (pExp / 2)) x) ^ 2))

/-- Corollary 2.1 with A1--A5 discharged at the concrete solution layer. -/
theorem Corollary_2_1_intervalDomain_of_phaseA
    (params : CM2Params) (raw : CGradShape)
    (hDG : ClassicalSolutionDissipationGradientFrontier params raw)
    (hEnergyFromCrossDiffusion :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain params T u v →
        CrossDiffusionBootstrapEstimate intervalDomain params T rho u v →
        AbstractLpBootstrapHypothesis
          intervalDomain u (params.N : ℝ) T rho p0 →
            LpBootstrapEnergyInequality intervalDomain u T rho p0) :
    Corollary_2_1 intervalDomain params := by
  intro T _hT u v hsol hbootstrap pExp hpExp
  rcases hbootstrap with ⟨rho, hrho, hcross, p0, hp0, hp0Bound⟩
  have hboot :
      AbstractLpBootstrapHypothesis
        intervalDomain u (params.N : ℝ) T rho p0 :=
    ⟨hrho, hsol.T_pos, hp0, hp0Bound⟩
  have henergy : LpBootstrapEnergyInequality intervalDomain u T rho p0 :=
    hEnergyFromCrossDiffusion hsol hcross hboot
  obtain ⟨hdiss, hgrad⟩ := hDG hsol hcross hboot henergy
  exact classicalSolution_all_exponents_of_phaseA
    raw hsol hcross hboot henergy hdiss hgrad pExp hpExp

#print axioms guardedCGrad_pos
#print axioms solution_u_nonneg
#print axioms solution_pow_intervalIntegrable
#print axioms solution_massGradientInterpolation
#print axioms solution_massControl_of_bootstrap
#print axioms solution_massControl_of_proposition24_branches
#print axioms solutionPhaseAData_of_classical
#print axioms classicalSolution_all_exponents_of_phaseA
#print axioms Corollary_2_1_intervalDomain_of_phaseA

end

end ShenWork.Paper2.IntervalDomainLem26PhaseA
