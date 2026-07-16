/-
  Endpoint-local form of the finite-horizon continuation alternative for the
  faithful general-m interval equation.
-/
import ShenWork.Paper2.IntervalDomainMContinuationExtension
import ShenWork.Paper2.IntervalDomainMClassicalInitialOverlap

open Set Topology
open ShenWork.IntervalDomain ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.IntervalDomainMContinuation

open ShenWork.Paper2.IntervalDomainM

/-! ## Endpoint-tail predicates -/

/-- Arbitrarily large population values occur in every nonempty time tail
before the finite horizon. -/
def UpperEndpointTail
    (D : BoundedDomainData) (T : ℝ) (u : ℝ → D.Point → ℝ) : Prop :=
  ∀ M S, 0 < S → S < T →
    ∃ t x, S < t ∧ t < T ∧ x ∈ D.inside ∧ M < u t x

/-- Arbitrarily small positive-population values occur in every nonempty time
tail before the finite horizon. -/
def FloorEndpointTail
    (D : BoundedDomainData) (T : ℝ) (u : ℝ → D.Point → ℝ) : Prop :=
  ∀ δ > 0, ∀ S, 0 < S → S < T →
    ∃ t x, S < t ∧ t < T ∧ x ∈ D.inside ∧ u t x < δ

/-- Paper-faithful finite-horizon alternative: the loss of extendibility is
witnessed arbitrarily close to the endpoint, rather than merely somewhere in
the whole lifetime. -/
def EndpointFiniteHorizonAlternative
    (D : BoundedDomainData) (T : ℝ) (u : ℝ → D.Point → ℝ) : Prop :=
  UpperEndpointTail D T u ∨ FloorEndpointTail D T u

/-! ## Forgetful bridges to the whole-lifetime predicates -/

/-- Endpoint-tail upper blow-up implies the legacy whole-lifetime upper
alternative on every positive horizon. -/
theorem mgeOneFiniteHorizonAlternative_of_upperEndpointTail
    {D : BoundedDomainData} {T : ℝ} {u : ℝ → D.Point → ℝ}
    (hT : 0 < T) (h : UpperEndpointTail D T u) :
    MGeOneFiniteHorizonAlternative D T u := by
  intro M
  obtain ⟨t, x, htS, htT, hx, hM⟩ :=
    h M (T / 2) (half_pos hT) (half_lt_self hT)
  exact ⟨t, x, (half_pos hT).trans htS, htT, hx, hM⟩

/-- Endpoint-tail floor collapse implies the legacy whole-lifetime floor
alternative on every positive horizon. -/
theorem floorAlternative_of_floorEndpointTail
    {D : BoundedDomainData} {T : ℝ} {u : ℝ → D.Point → ℝ}
    (hT : 0 < T) (h : FloorEndpointTail D T u) :
    ∀ δ > 0, ∃ t x,
      0 < t ∧ t < T ∧ x ∈ D.inside ∧ u t x < δ := by
  intro δ hδ
  obtain ⟨t, x, htS, htT, hx, hsmall⟩ :=
    h δ hδ (T / 2) (half_pos hT) (half_lt_self hT)
  exact ⟨t, x, (half_pos hT).trans htS, htT, hx, hsmall⟩

/-- Forgetting endpoint localization recovers the original finite-horizon
alternative. -/
theorem finiteHorizonAlternative_of_endpointFiniteHorizonAlternative
    {D : BoundedDomainData} {T : ℝ} {u : ℝ → D.Point → ℝ}
    (hT : 0 < T) (h : EndpointFiniteHorizonAlternative D T u) :
    FiniteHorizonAlternative D T u := by
  rcases h with hupper | hfloor
  · exact Or.inl
      (mgeOneFiniteHorizonAlternative_of_upperEndpointTail hT hupper)
  · exact Or.inr (floorAlternative_of_floorEndpointTail hT hfloor)

/-! ## Uniform controls on strict subhorizons -/

/-- A paper-positive classical branch has uniform two-sided bounds on every
strict subhorizon, including the initial end.  The existing pointwise trace
estimate controls a short initial interval; the existing compact-slab theorem
controls the remainder. -/
theorem strictSubhorizon_twoSidedM
    {p : CM2Params} {T S : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hu₀ : PaperPositiveInitialDatum intervalDomainM u₀)
    (hS0 : 0 < S) (hST : S < T) :
    ∃ c M : ℝ, 0 < c ∧ c ≤ M ∧
      ∀ t, 0 < t → t ≤ S → ∀ x : intervalDomainPoint,
        c ≤ u t x ∧ |u t x| ≤ M := by
  have hu₀adm :
      BddAbove (Set.range (fun x : intervalDomainPoint => |u₀ x|)) ∧
        Continuous u₀ := by
    simpa [intervalDomainM] using hu₀.admissible
  obtain ⟨eta, heta, heta₀⟩ := hu₀.floor
  obtain ⟨B, hB⟩ := hu₀adm.1
  let c₀ : ℝ := eta / 2
  have hc₀ : 0 < c₀ := half_pos heta
  let M₀ : ℝ := B + 1
  let eps : ℝ := min c₀ 1
  have heps : 0 < eps := lt_min hc₀ one_pos
  obtain ⟨delta, hdelta, hclose⟩ :=
    intervalDomainM_initialTrace_pointwise_abs_lt_of_classical
      hsol htrace hu₀adm.1 heps
  let a : ℝ := min (delta / 2) S
  have ha : 0 < a := lt_min (half_pos hdelta) hS0
  have haS : a ≤ S := min_le_right _ _
  have haDelta : a < delta :=
    (min_le_left (delta / 2) S).trans_lt (half_lt_self hdelta)
  obtain ⟨c₁, M₁, hc₁, hc₁M₁, hslab⟩ :=
    intervalDomainM_u_two_sided_on_compact hsol ha haS hST
  let c : ℝ := min c₀ c₁
  let M : ℝ := max M₀ M₁
  have hc : 0 < c := lt_min hc₀ hc₁
  have hcM : c ≤ M :=
    (min_le_right c₀ c₁).trans
      (hc₁M₁.trans (le_max_right M₀ M₁))
  refine ⟨c, M, hc, hcM, ?_⟩
  intro t ht0 htS x
  by_cases hta : t ≤ a
  · have htDelta : t < delta := hta.trans_lt haDelta
    have hdiff := (hclose t ht0 htDelta x).le
    have hlo₀ : c₀ ≤ u t x := by
      have hneg := neg_le_of_abs_le hdiff
      have hepsc₀ : eps ≤ c₀ := min_le_left _ _
      dsimp [c₀] at *
      linarith [heta₀ x]
    have hup₀ : |u t x| ≤ M₀ := by
      calc
        |u t x| = |(u t x - u₀ x) + u₀ x| := by
          congr 1
          ring
        _ ≤ |u t x - u₀ x| + |u₀ x| := abs_add_le _ _
        _ ≤ 1 + B := add_le_add
          (hdiff.trans (min_le_right c₀ 1)) (hB ⟨x, rfl⟩)
        _ = M₀ := by dsimp [M₀]; ring
    exact ⟨(min_le_left c₀ c₁).trans hlo₀,
      hup₀.trans (le_max_left M₀ M₁)⟩
  · have hat : a ≤ t := le_of_not_ge hta
    have hb := hslab t ⟨hat, htS⟩ x
    exact ⟨(min_le_right c₀ c₁).trans hb.1,
      hb.2.trans (le_max_right M₀ M₁)⟩

/-- On every strict positive subhorizon, the solution has a finite upper
bound. -/
theorem strictSubhorizon_upper_boundM
    {p : CM2Params} {T S : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hu₀ : PaperPositiveInitialDatum intervalDomainM u₀)
    (hS0 : 0 < S) (hST : S < T) :
    ∃ B : ℝ, ∀ t, 0 < t → t ≤ S →
      ∀ x : intervalDomainPoint, u t x ≤ B := by
  obtain ⟨c, M, _hc, _hcM, hbounds⟩ :=
    strictSubhorizon_twoSidedM hsol htrace hu₀ hS0 hST
  exact ⟨M, fun t ht0 htS x =>
    (le_abs_self (u t x)).trans (hbounds t ht0 htS x).2⟩

/-- On every strict positive subhorizon, the solution retains one uniform
positive floor. -/
theorem strictSubhorizon_uniform_floorM
    {p : CM2Params} {T S : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hu₀ : PaperPositiveInitialDatum intervalDomainM u₀)
    (hS0 : 0 < S) (hST : S < T) :
    ∃ c > 0, ∀ t, 0 < t → t ≤ S →
      ∀ x : intervalDomainPoint, c ≤ u t x := by
  obtain ⟨c, _M, hc, _hcM, hbounds⟩ :=
    strictSubhorizon_twoSidedM hsol htrace hu₀ hS0 hST
  exact ⟨c, hc, fun t ht0 htS x => (hbounds t ht0 htS x).1⟩

/-! ## Bridges from the legacy whole-lifetime alternative -/

/-- Whole-lifetime upper blow-up is endpoint-local once every strict
subhorizon is known to be bounded. -/
theorem upperEndpointTail_of_mgeOneFiniteHorizonAlternativeM
    {p : CM2Params} {T : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hu₀ : PaperPositiveInitialDatum intervalDomainM u₀)
    (halt : MGeOneFiniteHorizonAlternative intervalDomainM T u) :
    UpperEndpointTail intervalDomainM T u := by
  intro M S hS0 hST
  obtain ⟨B, hB⟩ := strictSubhorizon_upper_boundM
    hsol htrace hu₀ hS0 hST
  obtain ⟨t, x, ht0, htT, hx, hlarge⟩ := halt (max M B)
  have htS : S < t := by
    by_contra hnot
    have htle : t ≤ S := le_of_not_gt hnot
    have huB := hB t ht0 htle x
    linarith [le_max_right M B]
  exact ⟨t, x, htS, htT, hx, (le_max_left M B).trans_lt hlarge⟩

/-- Whole-lifetime floor collapse is endpoint-local once every strict
subhorizon has a positive floor. -/
theorem floorEndpointTail_of_floorAlternativeM
    {p : CM2Params} {T : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hu₀ : PaperPositiveInitialDatum intervalDomainM u₀)
    (halt : ∀ δ > 0, ∃ t x,
      0 < t ∧ t < T ∧ x ∈ intervalDomainM.inside ∧ u t x < δ) :
    FloorEndpointTail intervalDomainM T u := by
  intro δ hδ S hS0 hST
  obtain ⟨c, hc, hfloor⟩ := strictSubhorizon_uniform_floorM
    hsol htrace hu₀ hS0 hST
  let d : ℝ := min δ c / 2
  have hd : 0 < d := half_pos (lt_min hδ hc)
  obtain ⟨t, x, ht0, htT, hx, hsmall⟩ := halt d hd
  have htS : S < t := by
    by_contra hnot
    have htle : t ≤ S := le_of_not_gt hnot
    have hcx := hfloor t ht0 htle x
    have hdc : d < c := by
      dsimp [d]
      exact (half_lt_self (lt_min hδ hc)).trans_le (min_le_right δ c)
    linarith
  have hdδ : d ≤ δ := by
    dsimp [d]
    exact (half_le_self (le_of_lt (lt_min hδ hc))).trans (min_le_left δ c)
  exact ⟨t, x, htS, htT, hx, hsmall.trans_le hdδ⟩

/-- The legacy finite-horizon disjunction implies the faithful endpoint-tail
disjunction for an actual solution with its paper-positive initial trace. -/
theorem endpointFiniteHorizonAlternative_of_finiteHorizonAlternativeM
    {p : CM2Params} {T : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hu₀ : PaperPositiveInitialDatum intervalDomainM u₀)
    (halt : FiniteHorizonAlternative intervalDomainM T u) :
    EndpointFiniteHorizonAlternative intervalDomainM T u := by
  rcases halt with hupper | hfloor
  · exact Or.inl
      (upperEndpointTail_of_mgeOneFiniteHorizonAlternativeM
        hsol htrace hu₀ hupper)
  · exact Or.inr
      (floorEndpointTail_of_floorAlternativeM hsol htrace hu₀ hfloor)

/-- In the `m ≥ 1` branch, the legacy upper blow-up alternative upgrades to
upper blow-up in every endpoint tail. -/
theorem endpointUpperTail_of_mgeOneFiniteHorizonAlternativeM
    {p : CM2Params} {T : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hu₀ : PaperPositiveInitialDatum intervalDomainM u₀)
    (halt : MGeOneFiniteHorizonAlternative intervalDomainM T u) :
    UpperEndpointTail intervalDomainM T u :=
  upperEndpointTail_of_mgeOneFiniteHorizonAlternativeM
    hsol htrace hu₀ halt

#print axioms strictSubhorizon_upper_boundM
#print axioms strictSubhorizon_uniform_floorM
#print axioms finiteHorizonAlternative_of_endpointFiniteHorizonAlternative
#print axioms endpointFiniteHorizonAlternative_of_finiteHorizonAlternativeM
#print axioms endpointUpperTail_of_mgeOneFiniteHorizonAlternativeM

end ShenWork.Paper2.IntervalDomainMContinuation
