/-
  ShenWork/Paper2/IntervalDomainEnergyStep.lean

  Honest bridge from the Paper 2 bootstrap energy inequality to the Moser
  single-step interface used by `IntervalDomainChain`.

  This file does not claim `Lemma_2_6 intervalDomain`.  It isolates the exact
  remaining analytic hypotheses needed to use the already-proved Moser chain:
  a nonnegative time-dissipation term and the interpolation estimate at each
  exponent.
-/
import ShenWork.Paper2.IntervalDomainLpMonotonicity

open ShenWork.Paper2
open ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.Paper2.IntervalDomainEnergyStep

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

end ShenWork.Paper2.IntervalDomainEnergyStep

end
