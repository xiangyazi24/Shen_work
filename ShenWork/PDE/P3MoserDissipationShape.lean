import ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality
import ShenWork.Paper2.IntervalDomainMCL

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality
open ShenWork.Paper2.IntervalDomainLpMonotonicity
open ShenWork.Paper2.IntervalDomainMoserClosure
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserDissipationShape

/-!
This file records the predicate-shape diagnosis for the Moser dissipation
handoff.  The old `MoserDissipationDropBefore` quantifies arbitrary `B`; the
energy interface used by the route only supplies physical coefficients
`B > 0`.  Merely adding `0 <= B`, however, is not enough to make the old
pointwise drop a valid analytic consequence: an integrated first-crossing
energy inequality is the faithful shape for the PDE estimate.
-/

/-- Physical-`B` version of the old pointwise drop predicate.

This is the smallest faithful repair of the *coefficient quantification* defect:
the route never needs negative `B`.  It is still a pointwise drop predicate, so
it should be supplied only if the PDE proof really gives such a lower bound. -/
def MoserDissipationDropBeforeNonnegB
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p → ∀ A B K L_const, 0 ≤ B →
    (∀ t, 0 < t → t < T →
      (1 / p) * deriv (fun τ => D.integral (fun x => (u τ x) ^ p)) t +
        A * D.integral (fun x =>
          (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
        B * D.integral (fun x => (u t x) ^ p) ≤
      K * D.integral (fun x => (u t x) ^ (p + rho)) + L_const) →
    ∀ t, 0 < t → t < T →
      0 ≤
        (1 / p) * deriv (fun τ => D.integral (fun x => (u τ x) ^ p)) t +
          B * D.integral (fun x => (u t x) ^ p)

/-- Raw physical drop data packages into the nonnegative-`B` predicate. -/
theorem moserDissipationDropBeforeNonnegB_of_raw_drop
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T rho p0 : ℝ}
    (hdrop :
      ∀ p, p0 ≤ p → ∀ B, 0 ≤ B → ∀ t, 0 < t → t < T →
        0 ≤
          (1 / p) * deriv (fun τ => D.integral (fun x => (u τ x) ^ p)) t +
            B * D.integral (fun x => (u t x) ^ p)) :
    MoserDissipationDropBeforeNonnegB D u T rho p0 := by
  intro p hp _A B _K _L_const hB _hfull t ht0 htT
  exact hdrop p hp B hB t ht0 htT

/-- Integrated Moser energy-drop shape after the per-step PDE calculation.

This is the formal shape produced by the `u^(p-1)` test, chemotaxis IBP,
Young absorption under `alpha > gamma`, and first-crossing integration:
`Y_p(t₂)-Y_p(t₁) + 2∫G_p <= C p ∫ max(1,Y_p)`.

The analytic PDE proof of this estimate is not present in the current abstract
`BoundedDomainData` API; this definition is the route-level replacement for the
false pointwise `Y' + B Y >= 0` drop. -/
def IntegratedMoserDissipationDropBefore
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T _rho p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p → ∃ C, 0 ≤ C ∧
    ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
      D.integral (fun x => (u t2 x) ^ p) -
          D.integral (fun x => (u t1 x) ^ p) +
        2 * ∫ s in t1..t2,
          D.integral (fun x =>
            (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2) ≤
      C * p * ∫ s in t1..t2,
        max 1 (D.integral (fun x => (u s x) ^ p))

/-- Coefficient-parameterized version of
`IntegratedMoserDissipationDropBefore`.

Scalar absorption naturally leaves whatever coefficient remains after the
higher-power term has been absorbed.  The public fixed predicate above is the
special case `theta = 2`. -/
def IntegratedMoserDissipationDropBeforeCoeff
    (theta : ℝ) (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T _rho p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p → ∃ C, 0 ≤ C ∧
    ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
      D.integral (fun x => (u t2 x) ^ p) -
          D.integral (fun x => (u t1 x) ^ p) +
        theta * ∫ s in t1..t2,
          D.integral (fun x =>
            (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2) ≤
      C * p * ∫ s in t1..t2,
        max 1 (D.integral (fun x => (u s x) ^ p))

/-- The coefficient-parameterized integrated drop specializes to the fixed
coefficient predicate at `theta = 2`. -/
theorem integratedMoserDissipationDropBefore_of_coeff_two
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T rho p0 : ℝ}
    (h : IntegratedMoserDissipationDropBeforeCoeff 2 D u T rho p0) :
    IntegratedMoserDissipationDropBefore D u T rho p0 := by
  intro p hp
  exact h p hp

/-- If the coefficient-parametric estimate has coefficient at least `2`, it
implies the fixed route predicate, provided the Moser-gradient time integral is
nonnegative.  The latter is an explicit input because `BoundedDomainData` keeps
the integral operation abstract. -/
theorem integratedMoserDissipationDropBefore_of_coeff_ge_two
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 theta : ℝ}
    (htheta : 2 ≤ theta)
    (hG_nonneg :
      ∀ p, p0 ≤ p → ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
        0 ≤ ∫ s in t1..t2,
          D.integral (fun x =>
            (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2))
    (h : IntegratedMoserDissipationDropBeforeCoeff theta D u T rho p0) :
    IntegratedMoserDissipationDropBefore D u T rho p0 := by
  intro p hp
  rcases h p hp with ⟨C, hC, hineq⟩
  refine ⟨C, hC, ?_⟩
  intro t1 ht1 t2 ht2
  have hG := hG_nonneg p hp t1 ht1 t2 ht2
  have hthetaG :
      2 * (∫ s in t1..t2,
        D.integral (fun x =>
          (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2)) ≤
      theta * (∫ s in t1..t2,
        D.integral (fun x =>
          (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2)) :=
    mul_le_mul_of_nonneg_right htheta hG
  have hmain := hineq t1 ht1 t2 ht2
  linarith

/-- Packaging theorem for the integrated first-crossing Moser drop. -/
theorem integratedMoserDissipationDropBefore_of_integrated_energy
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T rho p0 : ℝ}
    (henergy :
      ∀ p, p0 ≤ p → ∃ C, 0 ≤ C ∧
        ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
          D.integral (fun x => (u t2 x) ^ p) -
              D.integral (fun x => (u t1 x) ^ p) +
            2 * ∫ s in t1..t2,
              D.integral (fun x =>
                (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2) ≤
          C * p * ∫ s in t1..t2,
            max 1 (D.integral (fun x => (u s x) ^ p))) :
    IntegratedMoserDissipationDropBefore D u T rho p0 := by
  intro p hp
  exact henergy p hp

/-! ### A small counterexample to the pointwise drop shape with `B >= 0` -/

def unitLinearDropDomain : BoundedDomainData where
  Point := Unit
  inside := Set.univ
  boundary := ∅
  volume := 1
  supNorm := fun f => |f ()|
  infValue := fun f => f ()
  integral := fun f => f ()
  gradNorm := fun _ _ => 0
  timeDeriv := fun _ _ _ => 0
  laplacian := fun _ _ => 0
  chemotaxisDiv := fun _ _ _ _ => 0
  crossDiffusionEnergyTerm := fun _ _ _ _ => 0
  normalDeriv := fun _ _ => 0
  initialAdmissible := fun _ => True
  classicalRegularity := fun _ _ _ => True

def unitLinearDropU (t : ℝ) (_x : Unit) : ℝ := 1 - 4 * t

private theorem unitLinearDrop_deriv (t : ℝ) :
    deriv (fun τ : ℝ => 1 - 4 * τ) t = -4 := by
  rw [show (fun τ : ℝ => 1 - 4 * τ) = (fun τ : ℝ => 1 + (-4) * τ) by
    ext τ
    ring]
  rw [deriv_const_add]
  rw [deriv_const_mul_field]
  rw [show deriv (fun x : ℝ => x) t = 1 by
    exact congrFun deriv_id'' t]
  ring

theorem unitLinearDrop_not_MoserDissipationDropBeforeNonnegB :
    ¬ MoserDissipationDropBeforeNonnegB
      unitLinearDropDomain unitLinearDropU 1 1 1 := by
  intro h
  have hfull :
      ∀ t, 0 < t → t < (1 : ℝ) →
        (1 / (1 : ℝ)) *
            deriv
              (fun τ =>
                unitLinearDropDomain.integral
                  (fun x => (unitLinearDropU τ x) ^ (1 : ℝ))) t +
          0 *
            unitLinearDropDomain.integral
              (fun x =>
                (unitLinearDropDomain.gradNorm
                  (fun y => (unitLinearDropU t y) ^ ((1 : ℝ) / 2)) x) ^ 2) +
          1 *
            unitLinearDropDomain.integral
              (fun x => (unitLinearDropU t x) ^ (1 : ℝ)) ≤
        0 *
            unitLinearDropDomain.integral
              (fun x => (unitLinearDropU t x) ^ ((1 : ℝ) + 1)) +
          0 := by
    intro t ht0 _htT
    simp only [unitLinearDropDomain, unitLinearDropU]
    have hpow_one :
        (fun τ : ℝ => (1 - 4 * τ) ^ (1 : ℝ)) =
          (fun τ : ℝ => 1 - 4 * τ) := by
      ext τ
      rw [Real.rpow_one]
    rw [hpow_one]
    rw [Real.rpow_one]
    rw [unitLinearDrop_deriv]
    nlinarith
  have hbad :=
    h (1 : ℝ) (le_rfl : (1 : ℝ) ≤ 1)
      0 1 0 0 (by norm_num : (0 : ℝ) ≤ 1) hfull
      (1 / 4) (by norm_num) (by norm_num)
  simp only [unitLinearDropDomain, unitLinearDropU] at hbad
  have hpow_one :
      (fun τ : ℝ => (1 - 4 * τ) ^ (1 : ℝ)) =
        (fun τ : ℝ => 1 - 4 * τ) := by
    ext τ
    rw [Real.rpow_one]
  rw [hpow_one] at hbad
  rw [unitLinearDrop_deriv] at hbad
  norm_num at hbad

/-! ### Route wrappers that consume only the physical `B > 0` from energy -/

theorem moser_step_of_energy_nonnegB_relative_interpolation
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T rho p0 p : ℝ}
    (henergy : LpBootstrapEnergyInequality D u T rho p0)
    (hdiss : MoserDissipationDropBeforeNonnegB D u T rho p0)
    (hrel : RelativeMoserInterpolationBefore D u T rho p0)
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
  rcases henergy p hp with ⟨A, hA, B, hB, K, hK, L_const, hfull⟩
  refine ⟨A, hA, K, hK, L_const, ?_, ?_⟩
  · intro t ht0 htT
    have hfull_t := hfull t ht0 htT
    have hdrop_t := hdiss p hp A B K L_const hB.le hfull t ht0 htT
    linarith
  · exact moser_constant_interpolation_of_relative_interpolation_and_lp_bound
      hLp (hrel p hp)

theorem moser_iteration_chain_of_energy_nonnegB_relative_interpolation
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T p0 rho : ℝ}
    (hrho : 0 < rho)
    (hbase : LpPowerBoundedBefore D p0 T u)
    (henergy : LpBootstrapEnergyInequality D u T rho p0)
    (hdiss : MoserDissipationDropBeforeNonnegB D u T rho p0)
    (hrel : RelativeMoserInterpolationBefore D u T rho p0) :
    ∀ n : ℕ, LpPowerBoundedBefore D (p0 + n * rho) T u := by
  intro n
  induction n with
  | zero =>
      simp only [CharP.cast_eq_zero, zero_mul, add_zero]
      exact hbase
  | succ n ih =>
      have hexp_eq :
          p0 + (↑(n + 1) : ℝ) * rho = (p0 + ↑n * rho) + rho := by
        push_cast
        ring
      rw [hexp_eq]
      have hp_ge : p0 ≤ p0 + ↑n * rho :=
        le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) hrho.le)
      obtain ⟨A, hA, K, hK, L_const, hstep_energy, hstep_interp⟩ :=
        moser_step_of_energy_nonnegB_relative_interpolation
          henergy hdiss hrel hp_ge ih
      exact IntervalDomainChain.lp_bootstrap_single_step_abstract
        (L_const := L_const) hA hK hstep_energy hstep_interp

theorem all_exponents_of_energy_nonnegB_relative_interpolation_lpmono
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {N T rho p0 : ℝ}
    (hboot : AbstractLpBootstrapHypothesis D u N T rho p0)
    (henergy : LpBootstrapEnergyInequality D u T rho p0)
    (hdiss : MoserDissipationDropBeforeNonnegB D u T rho p0)
    (hrel : RelativeMoserInterpolationBefore D u T rho p0)
    (hLpMono :
      ∀ {p q : ℝ}, 1 < p → p ≤ q →
        LpPowerBoundedBefore D q T u → LpPowerBoundedBefore D p T u) :
    ∀ pExp > 1, LpPowerBoundedBefore D pExp T u := by
  exact all_exponents_of_chain_and_lp_mono
    (AbstractLpBootstrapHypothesis.rho_pos hboot)
    (moser_iteration_chain_of_energy_nonnegB_relative_interpolation
      (AbstractLpBootstrapHypothesis.rho_pos hboot)
      (AbstractLpBootstrapHypothesis.initial_lp_bound hboot)
      henergy hdiss hrel)
    hLpMono

theorem intervalDomain_all_exponents_of_energy_nonnegB_relative_interpolation
    {u : ℝ → intervalDomain.Point → ℝ} {N T rho p0 : ℝ}
    (hboot : AbstractLpBootstrapHypothesis intervalDomain u N T rho p0)
    (henergy : LpBootstrapEnergyInequality intervalDomain u T rho p0)
    (hdiss : MoserDissipationDropBeforeNonnegB intervalDomain u T rho p0)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0)
    (hu_nonneg :
      ∀ t, 0 < t → t < T → ∀ x : intervalDomain.Point, 0 ≤ u t x)
    (hpow_int :
      ∀ pExp : ℝ, 1 < pExp → ∀ t, 0 < t → t < T →
        IntervalIntegrable
          (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ pExp))
          MeasureTheory.volume 0 1) :
    ∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u := by
  exact intervalDomain_all_exponents_of_LpPowerBoundedBefore_chain
    (AbstractLpBootstrapHypothesis.rho_pos hboot)
    (moser_iteration_chain_of_energy_nonnegB_relative_interpolation
      (AbstractLpBootstrapHypothesis.rho_pos hboot)
      (AbstractLpBootstrapHypothesis.initial_lp_bound hboot)
      henergy hdiss hrel)
    hu_nonneg hpow_int

theorem intervalDomain_all_exponents_of_energy_nonnegB_relative_interpolation_inside
    {u : ℝ → intervalDomain.Point → ℝ} {N T rho p0 : ℝ}
    (hboot : AbstractLpBootstrapHypothesis intervalDomain u N T rho p0)
    (henergy : LpBootstrapEnergyInequality intervalDomain u T rho p0)
    (hdiss : MoserDissipationDropBeforeNonnegB intervalDomain u T rho p0)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0)
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
    (moser_iteration_chain_of_energy_nonnegB_relative_interpolation
      (AbstractLpBootstrapHypothesis.rho_pos hboot)
      (AbstractLpBootstrapHypothesis.initial_lp_bound hboot)
      henergy hdiss hrel)
    hu_nonneg hpow_int

theorem intervalDomain_boundedBefore_of_energy_nonnegB_relative_interpolation
    {u : ℝ → intervalDomain.Point → ℝ} {N T rho p0 : ℝ}
    {pSeq rootBound : ℕ → ℝ}
    (hboot : AbstractLpBootstrapHypothesis intervalDomain u N T rho p0)
    (henergy : LpBootstrapEnergyInequality intervalDomain u T rho p0)
    (hdiss : MoserDissipationDropBeforeNonnegB intervalDomain u T rho p0)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0)
    (hLpMono :
      ∀ {p q : ℝ}, 1 < p → p ≤ q →
        LpPowerBoundedBefore intervalDomain q T u →
        LpPowerBoundedBefore intervalDomain p T u)
    (hEndpoint :
      (∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u) →
        IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound) :
    IsPaper2BoundedBefore intervalDomain T u := by
  have hAll : ∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u :=
    all_exponents_of_energy_nonnegB_relative_interpolation_lpmono
      hboot henergy hdiss hrel hLpMono
  exact intervalDomain_boundedBefore_of_moser_quantitative_endpoint
    (hEndpoint hAll)

/-! ### Actual-atoms route replacements with the old dissipation shape removed -/

theorem intervalDomain_allLpBoundFromBootstrap_of_relative_moser_step_nonnegB
    {params : CM2Params}
    (hdiss :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain params T u v →
        CrossDiffusionBootstrapEstimate intervalDomain params T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (params.N : ℝ) T rho p0 →
          MoserDissipationDropBeforeNonnegB intervalDomain u T rho p0)
    (hrel :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain params T u v →
        CrossDiffusionBootstrapEstimate intervalDomain params T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (params.N : ℝ) T rho p0 →
          RelativeMoserInterpolationBefore intervalDomain u T rho p0) :
    Corollary_2_1 intervalDomain params := by
  intro T hT u v hsol hbootstrap pExp hpExp
  rcases hbootstrap with ⟨rho, hrho, hcross, p0, hp0, hp0Lp⟩
  have hboot :
      AbstractLpBootstrapHypothesis intervalDomain u
        (params.N : ℝ) T rho p0 :=
    ⟨hrho, hT, hp0, hp0Lp⟩
  exact
    intervalDomain_all_exponents_of_energy_nonnegB_relative_interpolation_inside
      hboot
      (intervalDomain_LpBootstrapEnergyInequality_of_regularity hsol hcross hboot)
      (hdiss hsol hcross hboot)
      (hrel hsol hcross hboot)
      (fun t ht0 htT x _hx =>
        (IsPaper2ClassicalSolution.u_pos' hsol ht0 htT (x := x)).le)
      (fun r _hr t ht0 htT =>
        intervalDomain_u_rpow_intervalIntegrable_of_regularity
          (q := r) hsol ht0 htT)
      pExp hpExp

theorem intervalDomain_endpointBoundFromLp_of_quantitative_root_tower_nonnegB
    {params : CM2Params}
    (hcross :
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
      ∀ {T : ℝ}, 0 < T →
      ∀ {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain params T u v →
        InitialTrace intervalDomain u₀ u →
      ∀ pExp,
        max (params.N : ℝ)
            (max (params.m * (params.N : ℝ)) (params.γ * (params.N : ℝ))) <
          pExp →
        LpPowerBoundedBefore intervalDomain pExp T u →
          CrossDiffusionBootstrapEstimate intervalDomain params T 1 u v)
    (hdiss :
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
      ∀ {T : ℝ}, 0 < T →
      ∀ {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain params T u v →
        InitialTrace intervalDomain u₀ u →
      ∀ pExp,
        max (params.N : ℝ)
            (max (params.m * (params.N : ℝ)) (params.γ * (params.N : ℝ))) <
          pExp →
        LpPowerBoundedBefore intervalDomain pExp T u →
          MoserDissipationDropBeforeNonnegB intervalDomain u T 1 pExp)
    (hrel :
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
      ∀ {T : ℝ}, 0 < T →
      ∀ {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain params T u v →
        InitialTrace intervalDomain u₀ u →
      ∀ pExp,
        max (params.N : ℝ)
            (max (params.m * (params.N : ℝ)) (params.γ * (params.N : ℝ))) <
          pExp →
        LpPowerBoundedBefore intervalDomain pExp T u →
          RelativeMoserInterpolationBefore intervalDomain u T 1 pExp)
    (hEndpoint :
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
      ∀ {T : ℝ}, 0 < T →
      ∀ {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain params T u v →
        InitialTrace intervalDomain u₀ u →
      ∀ pExp,
        max (params.N : ℝ)
            (max (params.m * (params.N : ℝ)) (params.γ * (params.N : ℝ))) <
          pExp →
        LpPowerBoundedBefore intervalDomain pExp T u →
          ∃ pSeq rootBound : ℕ → ℝ,
            (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
              IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound) :
    Proposition_2_5 intervalDomain params := by
  intro u₀ hu₀ T hT u v hsol htrace pExp hpExp hLp
  have hboot :
      AbstractLpBootstrapHypothesis intervalDomain u
        (params.N : ℝ) T 1 pExp := by
    refine ⟨one_pos, hT, ?_, hLp⟩
    have hN_lt : (params.N : ℝ) < pExp :=
      lt_of_le_of_lt (le_max_left _ _) hpExp
    have hN_ge_one_nat : 1 ≤ params.N := Nat.succ_le_of_lt params.hN
    have hN_ge_one : (1 : ℝ) ≤ (params.N : ℝ) := by
      exact_mod_cast hN_ge_one_nat
    have h1_lt : (1 : ℝ) < pExp := lt_of_le_of_lt hN_ge_one hN_lt
    have hhalf_lt : 1 * (params.N : ℝ) / 2 < pExp := by
      nlinarith
    exact max_lt h1_lt hhalf_lt
  rcases hEndpoint hu₀ hT hsol htrace pExp hpExp hLp with
    ⟨pSeq, rootBound, hQuantEndpoint⟩
  have hLpMono :
      ∀ {p q : ℝ}, 1 < p → p ≤ q →
        LpPowerBoundedBefore intervalDomain q T u →
          LpPowerBoundedBefore intervalDomain p T u := by
    intro p q hp hpq hq
    exact intervalDomain_LpPowerBoundedBefore_mono_of_integrable_nonneg
      hp hpq
      (fun t ht0 htT x =>
        (IsPaper2ClassicalSolution.u_pos' hsol ht0 htT (x := x)).le)
      (fun t ht0 htT =>
        intervalDomain_u_rpow_intervalIntegrable_of_regularity
          (q := p) hsol ht0 htT)
      (fun t ht0 htT =>
        intervalDomain_u_rpow_intervalIntegrable_of_regularity
          (q := q) hsol ht0 htT)
      hq
  exact
    intervalDomain_boundedBefore_of_energy_nonnegB_relative_interpolation
      hboot
      (intervalDomain_LpBootstrapEnergyInequality_of_regularity hsol
        (hcross hu₀ hT hsol htrace pExp hpExp hLp) hboot)
      (hdiss hu₀ hT hsol htrace pExp hpExp hLp)
      (hrel hu₀ hT hsol htrace pExp hpExp hLp)
      hLpMono
      hQuantEndpoint

#print axioms moserDissipationDropBeforeNonnegB_of_raw_drop
#print axioms integratedMoserDissipationDropBefore_of_coeff_two
#print axioms integratedMoserDissipationDropBefore_of_coeff_ge_two
#print axioms integratedMoserDissipationDropBefore_of_integrated_energy
#print axioms unitLinearDrop_not_MoserDissipationDropBeforeNonnegB
#print axioms intervalDomain_allLpBoundFromBootstrap_of_relative_moser_step_nonnegB
#print axioms intervalDomain_endpointBoundFromLp_of_quantitative_root_tower_nonnegB

end ShenWork.IntervalDomainExistence.P3MoserDissipationShape

end
