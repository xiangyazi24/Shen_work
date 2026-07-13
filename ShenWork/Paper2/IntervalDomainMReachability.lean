/-
  Canonical reachable-horizon and global-gluing infrastructure for the
  paper-faithful general-m interval equation.

  The legacy continuation API in `IntervalDomainExistence` is tied to the
  linear-flux domain `intervalDomain`.  This file supplies the corresponding
  definitions and proved locality/gluing layer for `intervalDomainM`.
-/
import ShenWork.Paper2.IntervalDomainMClassicalInitialOverlap

open Filter Topology Set

noncomputable section

namespace ShenWork.Paper2.IntervalDomainMContinuation

open ShenWork.Paper2
open ShenWork.IntervalDomain
  (intervalDomainPoint intervalDomainLift intervalDomainLaplacian
    intervalDomainChemotaxisDivM intervalDomain intervalDomainM)
open ShenWork.IntervalDomainExistence

/-! ## Reachable horizons -/

/-- A horizon on which the faithful general-`m` classical Cauchy problem has
been realized with the prescribed initial trace. -/
def ReachableClassicalHorizonM
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (T : ℝ) : Prop :=
  0 < T ∧
    ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomainM p T u v ∧
      InitialTrace intervalDomainM u₀ u

/-- Set of all reachable faithful general-`m` horizons. -/
def reachableClassicalHorizonSetM
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) : Set ℝ :=
  {T | ReachableClassicalHorizonM p u₀ T}

/-- The unbounded branch of maximal continuation. -/
def ReachableArbitrarilyLongM
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) : Prop :=
  ∀ T > 0, ReachableClassicalHorizonM p u₀ T

/-- Structured finite-horizon witness. -/
structure ReachableClassicalSolutionDataM
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (T : ℝ) where
  T_pos : 0 < T
  u : ℝ → intervalDomainPoint → ℝ
  v : ℝ → intervalDomainPoint → ℝ
  sol : IsPaper2ClassicalSolution intervalDomainM p T u v
  trace : InitialTrace intervalDomainM u₀ u

/-- Repackage a reachable horizon as canonical choice data. -/
noncomputable def reachableClassicalSolutionDataMOfReach
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T : ℝ}
    (hreach : ReachableClassicalHorizonM p u₀ T) :
    ReachableClassicalSolutionDataM p u₀ T :=
  { T_pos := hreach.1
    u := Classical.choose hreach.2
    v := Classical.choose (Classical.choose_spec hreach.2)
    sol := (Classical.choose_spec (Classical.choose_spec hreach.2)).1
    trace := (Classical.choose_spec (Classical.choose_spec hreach.2)).2 }

/-- Datum-specific overlap uniqueness interface for faithful branches. -/
def IntervalMClassicalSolutionOverlapUniqueAt
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) : Prop :=
  ∀ {T₁ T₂ : ℝ}
    (d₁ : ReachableClassicalSolutionDataM p u₀ T₁)
    (d₂ : ReachableClassicalSolutionDataM p u₀ T₂),
      ∀ t, 0 < t → t < min T₁ T₂ →
        ∀ x : intervalDomainPoint,
          d₁.u t x = d₂.u t x ∧ d₁.v t x = d₂.v t x

/-- The faithful positive-strip Cauchy theory supplies exactly the overlap
interface needed by canonical continuation. -/
theorem intervalMClassicalSolutionOverlapUniqueAt_of_paperPositive
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomainM u₀) :
    IntervalMClassicalSolutionOverlapUniqueAt p u₀ := by
  intro T₁ T₂ d₁ d₂ t ht0 htT x
  exact ShenWork.Paper2.IntervalDomainM.intervalDomainM_classicalSolution_overlap_unique
    hu₀ d₁.sol d₂.sol d₁.trace d₂.trace t ht0 htT x

/-- Restrict a faithful classical solution to a shorter positive horizon. -/
theorem isPaper2ClassicalSolution_intervalDomainM_mono
    {p : CM2Params} {Tshort Tlong : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hTshort : 0 < Tshort) (hTL : Tshort ≤ Tlong)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p Tlong u v) :
    IsPaper2ClassicalSolution intervalDomainM p Tshort u v :=
  IsPaper2ClassicalSolution.of_components hTshort
    (by
      change ShenWork.IntervalDomain.intervalDomainClassicalRegularity Tshort u v
      exact intervalDomainClassicalRegularity_mono hTL hsol.regularity)
    (fun _t _x ht0 htT => hsol.u_pos' ht0 (lt_of_lt_of_le htT hTL))
    (fun _t _x ht0 htT => hsol.v_nonneg ht0 (lt_of_lt_of_le htT hTL))
    (fun _t _x ht0 htT hx => hsol.pde_u ht0 (lt_of_lt_of_le htT hTL) hx)
    (fun _t _x ht0 htT hx => hsol.pde_v ht0 (lt_of_lt_of_le htT hTL) hx)
    (fun _t _x ht0 htT hx => hsol.neumann ht0 (lt_of_lt_of_le htT hTL) hx)

/-- Reachability is downward closed. -/
theorem reachableClassicalHorizonM_mono
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {Tshort Tlong : ℝ}
    (hTshort : 0 < Tshort) (hTL : Tshort ≤ Tlong)
    (hreach : ReachableClassicalHorizonM p u₀ Tlong) :
    ReachableClassicalHorizonM p u₀ Tshort := by
  rcases hreach with ⟨_hTlong, u, v, hsol, htrace⟩
  exact ⟨hTshort, u, v,
    isPaper2ClassicalSolution_intervalDomainM_mono hTshort hTL hsol, htrace⟩

/-- An unbounded reachable set gives every positive finite horizon. -/
theorem reachableArbitrarilyLongM_of_not_bddAbove
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hnbdd : ¬ BddAbove (reachableClassicalHorizonSetM p u₀)) :
    ReachableArbitrarilyLongM p u₀ := by
  intro T hT
  obtain ⟨Tlong, hTlong, hlt⟩ := (not_bddAbove_iff.mp hnbdd) T
  exact reachableClassicalHorizonM_mono hT (le_of_lt hlt) hTlong

/-! ## Locality of the faithful classical predicate -/

/-- Extensionality of the faithful nonlinear chemotaxis divergence at an
interior point. -/
theorem intervalDomainChemotaxisDivM_eq_of_pointwise_eq
    (p : CM2Params)
    {u U v V : intervalDomainPoint → ℝ}
    (hu : ∀ x : intervalDomainPoint, u x = U x)
    (hv : ∀ x : intervalDomainPoint, v x = V x)
    {x : intervalDomainPoint} (hx : x ∈ intervalDomainM.inside) :
    intervalDomainChemotaxisDivM p u v x =
      intervalDomainChemotaxisDivM p U V x := by
  change deriv
      (fun y : ℝ =>
        (intervalDomainLift u y) ^ p.m * deriv (intervalDomainLift v) y /
          (1 + intervalDomainLift v y) ^ p.β) x.1 =
    deriv
      (fun y : ℝ =>
        (intervalDomainLift U y) ^ p.m * deriv (intervalDomainLift V) y /
          (1 + intervalDomainLift V y) ^ p.β) x.1
  have hEqOn : Set.EqOn
      (fun y : ℝ =>
        (intervalDomainLift u y) ^ p.m * deriv (intervalDomainLift v) y /
          (1 + intervalDomainLift v y) ^ p.β)
      (fun y : ℝ =>
        (intervalDomainLift U y) ^ p.m * deriv (intervalDomainLift V) y /
          (1 + intervalDomainLift V y) ^ p.β)
      (Set.Ioo (0 : ℝ) 1) := by
    intro y hy
    have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hy.1, le_of_lt hy.2⟩
    have hy_inside :
        (⟨y, hyIcc⟩ : intervalDomainPoint) ∈ intervalDomainM.inside := hy
    have hlu : intervalDomainLift u y = intervalDomainLift U y :=
      Filter.EventuallyEq.eq_of_nhds
        (intervalDomainLift_eventuallyEq_of_pointwise_eq hu hy_inside)
    have hlv : intervalDomainLift v y = intervalDomainLift V y :=
      Filter.EventuallyEq.eq_of_nhds
        (intervalDomainLift_eventuallyEq_of_pointwise_eq hv hy_inside)
    have hdv : deriv (intervalDomainLift v) y = deriv (intervalDomainLift V) y :=
      Filter.EventuallyEq.deriv_eq
        (intervalDomainLift_eventuallyEq_of_pointwise_eq hv hy_inside)
    change intervalDomainLift u y ^ p.m * deriv (intervalDomainLift v) y /
        (1 + intervalDomainLift v y) ^ p.β =
      intervalDomainLift U y ^ p.m * deriv (intervalDomainLift V) y /
        (1 + intervalDomainLift V y) ^ p.β
    rw [hlu, hlv, hdv]
  exact Filter.EventuallyEq.deriv_eq
    (Set.EqOn.eventuallyEq_of_mem hEqOn (isOpen_Ioo.mem_nhds hx))

/-- `IsPaper2ClassicalSolution intervalDomainM` is local under pointwise
agreement on its open time slab. -/
theorem classicalSolutionLocalityUnderIooAgreement_intervalDomainM
    (p : CM2Params)
    {T : ℝ} {u v U V : ℝ → intervalDomainPoint → ℝ}
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T U V)
    (hEq : ∀ t, 0 < t → t < T →
      ∀ x : intervalDomainPoint, u t x = U t x ∧ v t x = V t x) :
    IsPaper2ClassicalSolution intervalDomainM p T u v := by
  have huEq : ∀ t, 0 < t → t < T → u t = U t := by
    intro t ht0 htT
    funext x
    exact (hEq t ht0 htT x).1
  have hvEq : ∀ t, 0 < t → t < T → v t = V t := by
    intro t ht0 htT
    funext x
    exact (hEq t ht0 htT x).2
  refine IsPaper2ClassicalSolution.of_components hT ?_ ?_ ?_ ?_ ?_ ?_
  · change ShenWork.IntervalDomain.intervalDomainClassicalRegularity T u v
    exact intervalDomainClassicalRegularity_congr_Ioo
      hsol.regularity huEq hvEq
  · intro t x ht0 htT
    rw [huEq t ht0 htT]
    exact hsol.u_pos' ht0 htT
  · intro t x ht0 htT
    rw [hvEq t ht0 htT]
    exact hsol.v_nonneg ht0 htT
  · intro t x ht0 htT hx
    have htime := intervalDomainTimeDeriv_eq_of_Ioo_eq huEq ht0 htT x
    have htime' : deriv (fun s : ℝ => u s x) t =
        deriv (fun s : ℝ => U s x) t := by
      simpa [intervalDomain] using htime
    have hlap := intervalDomainLaplacian_eq_of_pointwise_eq
      (fun y => congrFun (huEq t ht0 htT) y) hx
    have hchem := intervalDomainChemotaxisDivM_eq_of_pointwise_eq p
      (fun y => congrFun (huEq t ht0 htT) y)
      (fun y => congrFun (hvEq t ht0 htT) y) hx
    have hpde := hsol.pde_u ht0 htT hx
    have huval : u t x = U t x := congrFun (huEq t ht0 htT) x
    change deriv (fun s : ℝ => u s x) t =
      intervalDomainLaplacian (u t) x -
        p.χ₀ * intervalDomainChemotaxisDivM p (u t) (v t) x +
          u t x * (p.a - p.b * (u t x) ^ p.α)
    change deriv (fun s : ℝ => U s x) t =
      intervalDomainLaplacian (U t) x -
        p.χ₀ * intervalDomainChemotaxisDivM p (U t) (V t) x +
          U t x * (p.a - p.b * (U t x) ^ p.α) at hpde
    rw [htime', hlap, hchem, huval]
    exact hpde
  · intro t x ht0 htT hx
    have hlap := intervalDomainLaplacian_eq_of_pointwise_eq
      (fun y => congrFun (hvEq t ht0 htT) y) hx
    have hpde := hsol.pde_v ht0 htT hx
    have huval : u t x = U t x := congrFun (huEq t ht0 htT) x
    have hvval : v t x = V t x := congrFun (hvEq t ht0 htT) x
    change (0 : ℝ) = intervalDomainLaplacian (v t) x -
      p.μ * v t x + p.ν * (u t x) ^ p.γ
    change (0 : ℝ) = intervalDomainLaplacian (V t) x -
      p.μ * V t x + p.ν * (U t x) ^ p.γ at hpde
    rw [hlap, hvval, huval]
    exact hpde
  · intro t x ht0 htT hx
    rw [huEq t ht0 htT, hvEq t ht0 htT]
    exact hsol.neumann ht0 htT hx

/-! ## Canonical gluing on the unbounded branch -/

/-- Canonical glued cell density, choosing the reachable horizon `t+1`. -/
noncomputable def reachableArbitrarilyLongGluedUM
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hreach : ReachableArbitrarilyLongM p u₀) :
    ℝ → intervalDomainPoint → ℝ :=
  fun t x =>
    if ht : 0 < t then
      (reachableClassicalSolutionDataMOfReach
        (hreach (t + 1) (by linarith))).u t x
    else 0

/-- Canonical glued chemical field, using the same finite witness. -/
noncomputable def reachableArbitrarilyLongGluedVM
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hreach : ReachableArbitrarilyLongM p u₀) :
    ℝ → intervalDomainPoint → ℝ :=
  fun t x =>
    if ht : 0 < t then
      (reachableClassicalSolutionDataMOfReach
        (hreach (t + 1) (by linarith))).v t x
    else 0

/-- The canonical glued branch agrees with every reachable witness on its
open lifespan. -/
theorem reachableArbitrarilyLongGluedM_eq_reachableData_of_overlapUnique
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (huniq : IntervalMClassicalSolutionOverlapUniqueAt p u₀)
    (hreach : ReachableArbitrarilyLongM p u₀)
    {T : ℝ} (d : ReachableClassicalSolutionDataM p u₀ T) :
    ∀ t, 0 < t → t < T → ∀ x : intervalDomainPoint,
      reachableArbitrarilyLongGluedUM hreach t x = d.u t x ∧
      reachableArbitrarilyLongGluedVM hreach t x = d.v t x := by
  intro t ht0 htT x
  let dshort : ReachableClassicalSolutionDataM p u₀ (t + 1) :=
    reachableClassicalSolutionDataMOfReach (hreach (t + 1) (by linarith))
  have ht_overlap : t < min (t + 1) T := lt_min (by linarith) htT
  have hsame := huniq dshort d t ht0 ht_overlap x
  constructor
  · simpa [reachableArbitrarilyLongGluedUM, ht0, dshort] using hsame.1
  · simpa [reachableArbitrarilyLongGluedVM, ht0, dshort] using hsame.2

/-- The canonical glued branch inherits the prescribed initial trace. -/
theorem reachableArbitrarilyLongGluedUM_initialTrace_of_overlapUnique
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (huniq : IntervalMClassicalSolutionOverlapUniqueAt p u₀)
    (hreach : ReachableArbitrarilyLongM p u₀) :
    InitialTrace intervalDomainM u₀ (reachableArbitrarilyLongGluedUM hreach) := by
  let d₁ : ReachableClassicalSolutionDataM p u₀ 1 :=
    reachableClassicalSolutionDataMOfReach (hreach 1 one_pos)
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := d₁.trace ε hε
  refine ⟨min δ 1, lt_min hδ_pos one_pos, ?_⟩
  intro t ht0 ht_lt
  have htδ : t < δ := lt_of_lt_of_le ht_lt (min_le_left _ _)
  have ht1 : t < (1 : ℝ) := lt_of_lt_of_le ht_lt (min_le_right _ _)
  have hsame := reachableArbitrarilyLongGluedM_eq_reachableData_of_overlapUnique
    huniq hreach d₁ t ht0 ht1
  have hfun :
      (fun x : intervalDomainPoint =>
        reachableArbitrarilyLongGluedUM hreach t x - u₀ x) =
      (fun x : intervalDomainPoint => d₁.u t x - u₀ x) := by
    funext x
    rw [(hsame x).1]
  change ShenWork.IntervalDomain.intervalDomainSupNorm
    (fun x : intervalDomainPoint =>
      reachableArbitrarilyLongGluedUM hreach t x - u₀ x) < ε
  rw [hfun]
  simpa [intervalDomainM] using hδ_bound t ht0 htδ

/-- Arbitrarily long faithful solutions glue to one genuine global classical
pair; no arbitrary post-horizon tail is reused. -/
theorem globalSolutionM_of_reachableArbitrarilyLong_of_overlapUniqueAt
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (huniq : IntervalMClassicalSolutionOverlapUniqueAt p u₀)
    (hreach : ReachableArbitrarilyLongM p u₀) :
    ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2GlobalClassicalSolution intervalDomainM p u v ∧
      InitialTrace intervalDomainM u₀ u := by
  let u := reachableArbitrarilyLongGluedUM hreach
  let v := reachableArbitrarilyLongGluedVM hreach
  refine ⟨u, v, ?_, ?_⟩
  · intro T hT
    let dT : ReachableClassicalSolutionDataM p u₀ T :=
      reachableClassicalSolutionDataMOfReach (hreach T hT)
    refine classicalSolutionLocalityUnderIooAgreement_intervalDomainM
      p hT dT.sol ?_
    intro t ht0 htT x
    exact reachableArbitrarilyLongGluedM_eq_reachableData_of_overlapUnique
      huniq hreach dT t ht0 htT x
  · exact reachableArbitrarilyLongGluedUM_initialTrace_of_overlapUnique
      huniq hreach

section AxiomAudit

#print axioms intervalMClassicalSolutionOverlapUniqueAt_of_paperPositive
#print axioms isPaper2ClassicalSolution_intervalDomainM_mono
#print axioms intervalDomainChemotaxisDivM_eq_of_pointwise_eq
#print axioms classicalSolutionLocalityUnderIooAgreement_intervalDomainM
#print axioms globalSolutionM_of_reachableArbitrarilyLong_of_overlapUniqueAt

end AxiomAudit

end ShenWork.Paper2.IntervalDomainMContinuation
