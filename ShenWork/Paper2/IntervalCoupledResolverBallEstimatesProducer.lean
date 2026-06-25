/-
  ShenWork/Paper2/IntervalCoupledResolverBallEstimatesProducer.lean

  Assembles the four conjuncts of `IntervalCoupledResolverBallEstimates`
  from the proven PDE building blocks:

    (1) hmap      — self-map of the sup-ball, from
                    `intervalCoupledDuhamelOperator_bound_of_source_bound`
                    (heat semigroup L∞ contraction + Duhamel integral bound);
    (2) hchem     — chemDiv flux-divergence Lipschitz K·D, passed through;
    (3) hint      — time-integrability of the Duhamel integrand, from
                    `intervalCoupledDuhamelIntegrand_integrableOn`
                    (sup bound + a.e.-strong-measurability);
    (4) hlift_int — integrability of the lifted coupled source, from
                    `intervalCoupledSource_lift_integrable`
                    (sup bound + a.e.-strong-measurability on compact domain).

  The chemDiv Lipschitz (conjunct 2) is taken as a hypothesis — the genuine
  C¹ flux content proven by the physical bounded-weight route in
  `IntervalChemDivFluxC1PhysicalBridge`/`IntervalCoupledC1ResolverBallBridge`.
  This file does NOT re-derive it; it provides the STRUCTURAL ASSEMBLY only.

  No `sorry`, no `admit`, no custom `axiom`.
-/
import ShenWork.PDE.IntervalCoupledBallEstimates

open ShenWork.Paper2 ShenWork.IntervalDomain ShenWork.PDE MeasureTheory
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalCoupledBallEstimates

noncomputable section

namespace ShenWork.Paper2.IntervalCoupledResolverBallEstimatesProducer

/-- **Structural assembly of `IntervalCoupledResolverBallEstimates`.**

From the six concrete building-block inputs:
  * initial-data sup bound `H_init` with `hu₀ : ∀ y, |u₀ y| ≤ H_init`;
  * source L∞ bound `C` on the trajectory ball;
  * constant choice `H_init + C * T ≤ M` (self-map closure);
  * chemDiv flux Lipschitz `K · D` on the trajectory ball (`hchem_KD`);
  * individual sup bounds on chemDiv (`Kc`) and logistic (`Lc`);
  * a.e.-strong-measurability of the semigroup integrand and the lifted source;

assemble all four conjuncts of `IntervalCoupledResolverBallEstimates p R u₀ T M K`:

  (hmap)      `|Φ(u)(t,x)| ≤ M`        — from `H_init + C·T ≤ M` via the
              committed `intervalCoupledDuhamelOperator_bound_of_source_bound`;
  (hchem)     `|ΔchemDiv| ≤ K·D`        — passed through from `hchem_KD`;
  (hint)      `IntegrableOn` of the Duhamel time integrand — from
              `intervalCoupledDuhamelIntegrand_integrableOn` via sup bounds;
  (hlift_int) `Integrable` of the lifted coupled source — from
              `intervalCoupledSource_lift_integrable` via sup bounds. -/
theorem produce
    (p : CM2Params)
    (R : (intervalDomainPoint → ℝ) → intervalDomainPoint → ℝ)
    (u₀ : intervalDomainPoint → ℝ)
    {T M K : ℝ}
    {H_init C Kc Lc : ℝ}
    (hH_init : 0 ≤ H_init) (hC : 0 ≤ C) (hKc : 0 ≤ Kc) (hLc : 0 ≤ Lc)
    (hMbound : H_init + C * T ≤ M)
    (hu₀ : ∀ y : intervalDomainPoint, |u₀ y| ≤ H_init)
    -- (2) chemDiv flux Lipschitz on the trajectory ball
    (hchem_KD : ∀ (u₁ u₂ : ℝ → intervalDomainPoint → ℝ) (D : ℝ),
      0 ≤ D →
      intervalTrajectoryBoundedOn T M u₁ →
      intervalTrajectoryBoundedOn T M u₂ →
      (∀ s y, 0 ≤ s → s ≤ T → |u₁ s y - u₂ s y| ≤ D) →
        ∀ (s : ℝ) (y : intervalDomainPoint), 0 ≤ s → s ≤ T →
          |intervalDomainChemotaxisDiv p (u₁ s) (R (u₁ s)) y -
            intervalDomainChemotaxisDiv p (u₂ s) (R (u₂ s)) y| ≤ K * D)
    -- source L∞ bound on the trajectory ball
    (hsource_sup : ∀ u : ℝ → intervalDomainPoint → ℝ,
      intervalTrajectoryBoundedOn T M u →
        ∀ s, 0 ≤ s → s ≤ T → ∀ y,
          |intervalDomainLift (intervalCoupledSource p (u s) (R (u s))) y| ≤ C)
    -- individual component sup bounds
    (hchem_sup : ∀ u : ℝ → intervalDomainPoint → ℝ,
      intervalTrajectoryBoundedOn T M u →
        ∀ s y, 0 ≤ s → s ≤ T →
          |intervalDomainChemotaxisDiv p (u s) (R (u s)) y| ≤ Kc)
    (hlog_sup : ∀ u : ℝ → intervalDomainPoint → ℝ,
      intervalTrajectoryBoundedOn T M u →
        ∀ s y, 0 ≤ s → s ≤ T →
          |intervalLogisticSource p (u s) y| ≤ Lc)
    -- a.e.-strong-measurability of the semigroup integrand
    (hsemigroup_meas : ∀ u : ℝ → intervalDomainPoint → ℝ,
      intervalTrajectoryBoundedOn T M u →
        ∀ (t : ℝ) (x : intervalDomainPoint), 0 ≤ t → t ≤ T →
          AEStronglyMeasurable
            (fun s => intervalSemigroupOperator 1 (t - s)
              (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) x.1)
            (volume.restrict (Set.Icc 0 t)))
    -- a.e.-strong-measurability of the lifted coupled source
    (hlift_meas : ∀ u : ℝ → intervalDomainPoint → ℝ,
      intervalTrajectoryBoundedOn T M u →
        ∀ s, 0 ≤ s → s ≤ T →
          AEStronglyMeasurable
            (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
            (intervalMeasure 1)) :
    IntervalCoupledResolverBallEstimates p R u₀ T M K := by
  -- Assemble conjuncts (2)+(3)+(4) from the committed infrastructure.
  obtain ⟨_hchem, hint, hlift_int⟩ :=
    intervalCoupledResolver_hchem_hint_hlift p R hchem_KD hsemigroup_meas
      hlift_meas hKc hLc hchem_sup hlog_sup
  refine ⟨?_, hchem_KD, hint, hlift_int⟩
  -- (1) hmap: sup-ball self-map from the committed source-sup Duhamel bound.
  intro u hu t x ht0 htT
  exact le_trans
    (intervalCoupledDuhamelOperator_bound_of_source_bound p R u₀ u
      hH_init hC hu₀
      (fun s hs0 hsT y => hsource_sup u hu s hs0 hsT y)
      ht0 htT x
      (hint u hu t x ht0 htT)
      (fun s hs0 hsT => hlift_int u hu s hs0 hsT))
    hMbound

end ShenWork.Paper2.IntervalCoupledResolverBallEstimatesProducer
