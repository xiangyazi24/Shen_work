import ShenWork.Paper2.IntervalDomainRestartLocalWiring
import ShenWork.Paper2.IntervalLemma31Closure

/-!
  Conditional assembly for the chi0 < 0, a,b > 0 branch of Paper 2
  Theorem 1.1 on the interval domain.

  The new residual is intentionally only the coupled-flux classical local
  existence factory with a lifespan depending on an a priori sup bound for the
  datum.  The sup-norm estimate itself is not a hypothesis: it is supplied by
  the existing Lemma 3.1 bridge.
-/

open ShenWork.IntervalDomain

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
#print axioms coupledFlux_interiorSupNorm_le_regimeBound
#print axioms theorem_1_1_intervalDomain_chiNeg_of_coupledFluxClassicalLocalExistenceResidual

end ShenWork.Paper2.ChiNegResidual

