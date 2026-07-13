/- Small-data global existence near a linearly stable positive equilibrium. -/
import ShenWork.Paper2.IntervalDomainL2USubHorizonGluing
import ShenWork.PDE.P3MoserEnergyContinuity
import ShenWork.Paper3.IntervalDomainWeakSupBasinEntry

namespace ShenWork.Paper3

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.IntervalDomainExistence
open ShenWork.PDE
open ShenWork.PDE.SectorialOperator

noncomputable section

local instance : TopologicalSpace intervalDomain.Point :=
  inferInstanceAs (TopologicalSpace intervalDomainPoint)

/-- A finite classical solution with a bounded initial trace is uniformly
bounded on every closed half-horizon `(0,t]`, with `t` strictly below its
classical horizon.  The short-time leg comes from the initial trace and the
remaining compact slab from joint continuity. -/
theorem intervalDomain_solution_lift_uniform_abs_on_halfHorizon
    {p : CM2Params} {T t : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hbdd₀ : BddAbove (Set.range (fun x : intervalDomainPoint => |u₀ x|)))
    (ht0 : 0 < t) (htT : t < T) :
    ∃ M : ℝ, ∀ τ, 0 < τ → τ ≤ t →
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |intervalDomainLift (u τ) x| ≤ M := by
  obtain ⟨eta, heta, _hetaT, hnear⟩ :=
    initialSupNormApproach_intervalDomain p u₀ hu₀ hbdd₀ hsol.T_pos
      hsol htrace (by norm_num : (0 : ℝ) < 1)
  let a := min (eta / 2) (t / 2)
  have ha : 0 < a := by
    dsimp [a]
    exact lt_min (by linarith) (by linarith)
  have hat : a ≤ t := by
    have : a ≤ t / 2 := by dsimp [a]; exact min_le_right _ _
    linarith
  have haeta : a < eta := by
    have : a ≤ eta / 2 := by dsimp [a]; exact min_le_left _ _
    linarith
  let slab := Set.Icc a t ×ˢ Set.Icc (0 : ℝ) 1
  have hslabCompact : IsCompact slab := by
    dsimp [slab]
    exact isCompact_Icc.prod isCompact_Icc
  have hslabSub : slab ⊆
      Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1 := by
    dsimp [slab]
    exact Set.prod_mono (Set.Icc_subset_Ioo ha htT) Subset.rfl
  have hjoint :=
    ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity.intervalDomain_solution_jointContinuousOn
      hsol
  have habsCont : ContinuousOn
      (fun tx : ℝ × ℝ =>
        |intervalDomainLift (u tx.1) tx.2|) slab :=
    continuous_abs.comp_continuousOn (hjoint.mono hslabSub)
  have hslabNonempty : slab.Nonempty := by
    refine ⟨(a, 0), ?_⟩
    exact ⟨⟨le_rfl, hat⟩, by norm_num⟩
  obtain ⟨txmax, _htxmax, hmax⟩ :=
    hslabCompact.exists_isMaxOn hslabNonempty habsCont
  let Mcompact := |intervalDomainLift (u txmax.1) txmax.2|
  let Mnear := intervalDomain.supNorm u₀ + 1
  let M := max Mnear Mcompact
  refine ⟨M, ?_⟩
  intro τ hτ hτt x hx
  by_cases hτa : τ < a
  · have hτT : τ < T := lt_of_le_of_lt hτt htT
    have habs := abs_lift_le_supNorm hsol ⟨hτ, hτT⟩ hx
    have hsup : intervalDomain.supNorm (u τ) ≤ Mnear := by
      dsimp [Mnear]
      exact hnear τ hτ (lt_trans hτa haeta)
    exact habs.trans (hsup.trans (by dsimp [M]; exact le_max_left _ _))
  · have hτmem : (τ, x) ∈ slab := by
      dsimp [slab]
      exact ⟨⟨le_of_not_gt hτa, hτt⟩, hx⟩
    have hcompact : |intervalDomainLift (u τ) x| ≤ Mcompact := by
      simpa [Mcompact] using hmax hτmem
    exact hcompact.trans (by dsimp [M]; exact le_max_right _ _)

/-- Parameter-independent overlap uniqueness for the paper's uniformly
positive initial data.  Stability is not used: on each strict sub-horizon,
positivity and compact boundedness supply the two-sided strip needed by the
existing L2 energy argument. -/
def intervalDomainPaperPositiveOverlapUniqueAt
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀) :
    IntervalClassicalSolutionOverlapUniqueAt p u₀ := by
  intro T₁ T₂ d₁ d₂ t ht0 htmin x
  refine intervalDomain_classicalSolution_overlap_unique_of_subHorizonBound
    d₁.sol d₂.sol d₁.trace d₂.trace hu₀.admissible.1 ?_ t ht0 htmin x
  intro T' hT' hT'min
  have hT'₁ : T' < T₁ := hT'min.trans_le (min_le_left _ _)
  have hT'₂ : T' < T₂ := hT'min.trans_le (min_le_right _ _)
  obtain ⟨delta₁, hdelta₁, hlo₁⟩ := lift_u_uniformPositive_on_halfHorizon
    d₁.sol d₁.trace hu₀.floor hu₀.admissible hT' hT'₁
  obtain ⟨delta₂, hdelta₂, hlo₂⟩ := lift_u_uniformPositive_on_halfHorizon
    d₂.sol d₂.trace hu₀.floor hu₀.admissible hT' hT'₂
  obtain ⟨M₁, hM₁⟩ := intervalDomain_solution_lift_uniform_abs_on_halfHorizon
    d₁.sol d₁.trace hu₀.toPositive hu₀.admissible.1 hT' hT'₁
  obtain ⟨M₂, hM₂⟩ := intervalDomain_solution_lift_uniform_abs_on_halfHorizon
    d₂.sol d₂.trace hu₀.toPositive hu₀.admissible.1 hT' hT'₂
  refine ⟨min delta₁ delta₂, max M₁ M₂, lt_min hdelta₁ hdelta₂, ?_⟩
  intro τ hτ hτT'
  constructor
  · intro y hy
    exact ⟨(min_le_left _ _).trans (hlo₁ τ hτ hτT' y hy),
      (le_abs_self _).trans
        ((hM₁ τ hτ hτT' y hy).trans (le_max_left _ _))⟩
  · intro y hy
    exact ⟨(min_le_right _ _).trans (hlo₂ τ hτ hτT' y hy),
      (le_abs_self _).trans
        ((hM₂ τ hτ hτT' y hy).trans (le_max_right _ _))⟩

#print axioms intervalDomain_solution_lift_uniform_abs_on_halfHorizon
#print axioms intervalDomainPaperPositiveOverlapUniqueAt

end

end ShenWork.Paper3
