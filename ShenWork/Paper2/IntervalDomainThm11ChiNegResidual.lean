import ShenWork.Paper2.IntervalDomainRestartLocalWiring
import ShenWork.Paper2.IntervalLemma31Closure
import ShenWork.PDE.IntervalLogisticLipschitz
import ShenWork.PDE.IntervalNeumannEllipticResolverR

/-!
  Conditional assembly for the chi0 < 0, a,b > 0 branch of Paper 2
  Theorem 1.1 on the interval domain.

  The new residual is intentionally only the coupled-flux classical local
  existence factory with a lifespan depending on an a priori sup bound for the
  datum.  The sup-norm estimate itself is not a hypothesis: it is supplied by
  the existing Lemma 3.1 bridge.
-/

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.PDE

noncomputable section

namespace ShenWork.Paper2.ChiNegResidual

/-- The precise coupled-flux classical local-existence residual needed for the
chi0 < 0, a,b > 0 Theorem 1.1 assembly.

For each datum size `M`, it gives one lifespan `delta(M) > 0` that works for
all positive admissible initial data with `|u0| <= M`.  This is the quantitative
form required by the existing restart-and-glue continuation wiring. -/
def CoupledFluxClassicalLocalExistenceResidual (p : CM2Params) : Prop :=
  ∀ M : ℝ, 0 < M → ∃ delta : ℝ, 0 < delta ∧
    ∀ {u0 : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u0 →
      (∀ x, |u0 x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p delta u v ∧
          InitialTrace intervalDomain u0 u

/-- Exact-horizon extraction from the coupled Duhamel fixed point interface.

This is the non-circular tractable part of the `χ₀ < 0` local theory: resolver
ball estimates give the contraction, while `hregularize` is the separate
parabolic/elliptic regularity bridge upgrading the fixed point to the paper's
classical solution predicate on the same horizon `T`. -/
theorem exactLocalClassicalSolution_of_coupledDuhamel_resolver_estimates
    (p : CM2Params)
    (R : (intervalDomainPoint → ℝ) → intervalDomainPoint → ℝ)
    (u0 : intervalDomainPoint → ℝ)
    (_hu0 : PositiveInitialDatum intervalDomain u0)
    {A L K T M : ℝ} (hA : 0 < A) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hT : 0 < T) (hAT : A * T < 1) (hM : 0 ≤ M)
    (hA_bound : |p.χ₀| * K + L ≤ A)
    (hL_lip : ∀ a b : ℝ, |a| ≤ M → |b| ≤ M →
      |a * (p.a - p.b * a ^ p.α) - b * (p.a - p.b * b ^ p.α)| ≤
        L * |a - b|)
    (hest : IntervalCoupledResolverBallEstimates p R u0 T M K)
    (hregularize :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        intervalTrajectoryBoundedOn T M u →
        (∀ t x, 0 ≤ t → t ≤ T →
          u t x = intervalCoupledDuhamelOperator p R u0 u t x) →
        (∀ t, v t = R (u t)) →
          RegularityBootstrap p T u0 u) :
    ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v ∧
      InitialTrace intervalDomain u0 u := by
  rcases hest with ⟨hmap, hchem, hint, hlift_int⟩
  have hcontr :
      ∀ (u1 u2 : ℝ → intervalDomainPoint → ℝ) (D : ℝ),
        0 ≤ D →
        intervalTrajectoryBoundedOn T M u1 →
        intervalTrajectoryBoundedOn T M u2 →
        (∀ s y, 0 ≤ s → s ≤ T → |u1 s y - u2 s y| ≤ D) →
        ∀ t x, 0 ≤ t → t ≤ T →
          |intervalCoupledDuhamelOperator p R u0 u1 t x -
            intervalCoupledDuhamelOperator p R u0 u2 t x| ≤ A * T * D :=
    intervalCoupledDuhamel_closedBall_contraction_of_resolver_estimates
      p R u0 hT hL hK hA_bound hL_lip ⟨hmap, hchem, hint, hlift_int⟩
  have hzero_ball :
      intervalTrajectoryBoundedOn T M
        (fun _ : ℝ => fun _ : intervalDomainPoint => 0) := by
    intro _t _x _ht0 _htT
    simpa using hM
  have hbase :
      ∀ t x, 0 ≤ t → t ≤ T →
        |intervalCoupledDuhamelOperator p R u0 (fun _ _ => 0) t x| ≤ M :=
    hmap (fun _ : ℝ => fun _ : intervalDomainPoint => 0) hzero_ball
  obtain ⟨u, vR, hu_ball, hfp, hvR⟩ :=
    intervalCoupledDuhamel_fixed_point_exists_on_closed_ball
      p R u0 hA hM hT hAT hM hmap hcontr hbase
  obtain ⟨v, hpos, hvnn, hpde_u, hpde_v, hbc, hclassreg, htrace⟩ :=
    hregularize u vR hu_ball hfp hvR
  exact ⟨u, v,
    IsPaper2ClassicalSolution.of_components
      hT hclassreg hpos hvnn hpde_u hpde_v hbc,
    htrace⟩

/-- The exact analytic frontier for closing
`CoupledFluxClassicalLocalExistenceResidual` through the concrete Neumann
resolver `intervalNeumannResolverR`.

For each datum size `M`, it asks for a larger fixed-point ball `Mball`; after
the already-proved logistic Lipschitz constant `L` is chosen on that ball, it
asks for a short horizon, resolver ball estimates, and the regularization
bridge from coupled Duhamel fixed points to `RegularityBootstrap`. -/
def CoupledFluxResolverAnalyticData (p : CM2Params) : Prop :=
  ∀ M : ℝ, 0 < M →
    ∃ Mball : ℝ, 0 < Mball ∧ M ≤ Mball ∧
      ∀ L : ℝ, 0 < L →
        ∃ T A K : ℝ, 0 < T ∧ 0 < A ∧ 0 ≤ K ∧ A * T < 1 ∧
          |p.χ₀| * K + L ≤ A ∧
            ∀ {u0 : intervalDomain.Point → ℝ},
              PositiveInitialDatum intervalDomain u0 →
              (∀ x, |u0 x| ≤ M) →
                IntervalCoupledResolverBallEstimates p
                  (intervalNeumannResolverR p) u0 T Mball K ∧
                ∀ u v : ℝ → intervalDomain.Point → ℝ,
                  intervalTrajectoryBoundedOn T Mball u →
                  (∀ t x, 0 ≤ t → t ≤ T →
                    u t x = intervalCoupledDuhamelOperator p
                      (intervalNeumannResolverR p) u0 u t x) →
                  (∀ t, v t = intervalNeumannResolverR p (u t)) →
                    RegularityBootstrap p T u0 u

/-- Resolver estimates plus the coupled fixed-point regularization bridge close
the `χ₀ < 0` local-existence residual.  The logistic Lipschitz leg is discharged
by `IntervalLogisticLipschitz.intervalLogisticReaction_lipschitz_on_bounded`;
the remaining content is exactly `CoupledFluxResolverAnalyticData`. -/
theorem coupledFluxClassicalLocalExistenceResidual_of_resolverAnalyticData
    (p : CM2Params) (hα : 1 ≤ p.α)
    (H : CoupledFluxResolverAnalyticData p) :
    CoupledFluxClassicalLocalExistenceResidual p := by
  intro M hM
  obtain ⟨Mball, hMball, _hM_le, Hlocal⟩ := H M hM
  obtain ⟨L, hLpos, hL_lip⟩ :=
    ShenWork.IntervalLogisticLipschitz.intervalLogisticReaction_lipschitz_on_bounded
      p hα hMball
  obtain ⟨T, A, K, hT, hA, hK, hAT, hA_bound, Hdatum⟩ :=
    Hlocal L hLpos
  refine ⟨T, hT, ?_⟩
  intro u0 hu0 hbound
  obtain ⟨hest, hregularize⟩ := Hdatum hu0 hbound
  exact exactLocalClassicalSolution_of_coupledDuhamel_resolver_estimates
    p (intervalNeumannResolverR p) u0 hu0 hA hLpos.le hK hT hAT
    hMball.le hA_bound hL_lip hest hregularize

/-- The quantitative residual includes ordinary per-datum short-time classical
existence because positive interval data are bounded by admissibility. -/
theorem localExistence_of_coupledFluxClassicalLocalExistenceResidual
    (p : CM2Params)
    (hExist : CoupledFluxClassicalLocalExistenceResidual p) :
    ∀ u0 : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u0 →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u0 u := by
  intro u0 hu0
  obtain ⟨B, hB⟩ := hu0.admissible.1
  set M : ℝ := max B 1 with hMdef
  have hM_pos : 0 < M := by
    rw [hMdef]
    exact lt_of_lt_of_le zero_lt_one (le_max_right B 1)
  have hbound : ∀ x : intervalDomain.Point, |u0 x| ≤ M := by
    intro x
    rw [hMdef]
    exact le_trans (hB (Set.mem_range_self x)) (le_max_left B 1)
  obtain ⟨delta, hdelta, hfactory⟩ := hExist M hM_pos
  obtain ⟨u, v, hsol, htrace⟩ := hfactory hu0 hbound
  exact ⟨delta, hdelta, u, v, hsol, htrace⟩

/-- The Lemma 3.1-derived interior bound used by the continuation wiring.

This is an explicit probe of the already-proved bound machinery: once a
coupled classical solution exists, no additional sup-norm hypothesis is needed.
-/
theorem coupledFlux_interiorSupNorm_le_regimeBound
    (p : CM2Params) (hchi_neg : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    {u0 : intervalDomain.Point → ℝ}
    (hu0 : PositiveInitialDatum intervalDomain u0)
    {M : ℝ} (hM : 0 < M)
    (hbound : ∀ x : intervalDomain.Point, |u0 x| ≤ M)
    {T : ℝ} (hT : 0 < T)
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (htrace : InitialTrace intervalDomain u0 u) :
    ∀ t, 0 < t → t < T →
      ∀ x : intervalDomain.Point,
        |u t x| ≤ SupNormBridge.regimeBound p M :=
  SupNormBridge.interiorSupNorm_le_regimeBound
    p (le_of_lt hchi_neg) ha hb hu0 hM hbound hT hsol htrace

/-- Conditional chi0 < 0 assembly for Paper 2 Theorem 1.1 on the interval.

The only open analytical input is
`CoupledFluxClassicalLocalExistenceResidual p`.  Lemma 3.1 supplies the
sup-norm bound through `SupNormBridge.interiorSupNorm_le_regimeBound`, which is
used by `RestartLocalWiring.paper2_theorem_1_1_from_quant_and_hlocal` to build
uniform continuation. -/
theorem theorem_1_1_intervalDomain_chiNeg_of_coupledFluxClassicalLocalExistenceResidual
    (p : CM2Params) (hchi_neg : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (_halpha : 1 ≤ p.α) (hgamma : 1 ≤ p.γ)
    (hExist : CoupledFluxClassicalLocalExistenceResidual p) :
    Theorem_1_1 intervalDomain p :=
  RestartLocalWiring.paper2_theorem_1_1_from_quant_and_hlocal
    p (le_of_lt hchi_neg) ha hb hgamma hExist
    (localExistence_of_coupledFluxClassicalLocalExistenceResidual p hExist)

#check Lemma31Closure.Lemma_3_1_intervalDomain
#check CoupledFluxClassicalLocalExistenceResidual
#check CoupledFluxResolverAnalyticData
#print axioms exactLocalClassicalSolution_of_coupledDuhamel_resolver_estimates
#print axioms coupledFluxClassicalLocalExistenceResidual_of_resolverAnalyticData
#print axioms coupledFlux_interiorSupNorm_le_regimeBound
#print axioms theorem_1_1_intervalDomain_chiNeg_of_coupledFluxClassicalLocalExistenceResidual

end ShenWork.Paper2.ChiNegResidual
