import ShenWork.PDE.IntervalDomainExistence
import ShenWork.PDE.GagliardoNirenberg
import ShenWork.Paper2.IntervalDomainL2CrossControl
import ShenWork.Paper2.IntervalDomainMass
import ShenWork.Paper2.IntervalDomainStructuredMoserPower

open ShenWork.Paper2 ShenWork.IntervalDomain
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainLpMonotonicity
open ShenWork.Paper2.IntervalDomainStructuredMoserData

noncomputable section

namespace ShenWork.IntervalDomainExistence

/-- The sharp one-dimensional absorption threshold for the L² bootstrap seed.
It is a genuine predicate on the carried `CM2Params`, not a theorem-field
standing for the absorption estimate. -/
def IntervalDomainSharpL2AbsorptionThreshold (p : CM2Params) : Prop :=
  p.γ < 1 ∨ 2 * p.γ < p.α

/-- Bundled parameter-side hypotheses for the interval-domain L² bootstrap.

The final conjunct is the type-level exponent requirement needed when the
L² bound is used as the bootstrap seed with the committed cross-diffusion
exponent `rho = 2γ`: it gives `2 > rho * N / 2`. -/
def IntervalDomainBoundednessHyp (p : CM2Params) : Prop :=
  IntervalDomainSharpL2AbsorptionThreshold p ∧
    0 < p.b ∧
      2 * p.γ < p.α ∧
        0 < p.γ ∧
          p.γ * (p.N : ℝ) < 2

/-- The threshold is the paper's exponent comparison
`2 + 2γ < max 4 (2 + α)`. -/
theorem intervalDomainSharpL2AbsorptionThreshold_iff_exponent
    (p : CM2Params) :
    IntervalDomainSharpL2AbsorptionThreshold p ↔
      2 + 2 * p.γ < max (4 : ℝ) (2 + p.α) := by
  unfold IntervalDomainSharpL2AbsorptionThreshold
  constructor
  · intro h
    rcases h with hγ | hαγ
    · have hleft : 2 + 2 * p.γ < (4 : ℝ) := by linarith
      exact lt_of_lt_of_le hleft (le_max_left _ _)
    · have hright : 2 + 2 * p.γ < 2 + p.α := by linarith
      exact lt_of_lt_of_le hright (le_max_right _ _)
  · intro h
    have hcases : (4 : ℝ) ≤ 2 + p.α ∨ 2 + p.α < 4 := le_or_gt _ _
    rcases hcases with hright | hleft
    · right
      have hmax : max (4 : ℝ) (2 + p.α) = 2 + p.α :=
        max_eq_right hright
      rw [hmax] at h
      linarith
    · left
      have hmax : max (4 : ℝ) (2 + p.α) = 4 :=
        max_eq_left (le_of_lt hleft)
      rw [hmax] at h
      linarith

/-- Concrete satisfiability witness for the sharp threshold:
`γ = 1/2` satisfies the first branch. -/
def intervalDomainSharpL2AbsorptionThresholdWitnessParams : CM2Params :=
  { N := 1
    hN := by norm_num
    α := 2
    γ := (1 / 2 : ℝ)
    m := 1
    μ := 1
    ν := 1
    χ₀ := 0
    a := 1
    b := 1
    β := 0
    hα := by norm_num
    hγ := by norm_num
    hm := by norm_num
    hμ := by norm_num
    hν := by norm_num
    ha := by norm_num
    hb := by norm_num
    hβ := by norm_num }

theorem intervalDomainSharpL2AbsorptionThreshold_satisfiable :
    IntervalDomainSharpL2AbsorptionThreshold
      intervalDomainSharpL2AbsorptionThresholdWitnessParams := by
  left
  norm_num [intervalDomainSharpL2AbsorptionThresholdWitnessParams]

theorem intervalDomainBoundednessHyp_satisfiable :
    IntervalDomainBoundednessHyp
      intervalDomainSharpL2AbsorptionThresholdWitnessParams := by
  refine ⟨intervalDomainSharpL2AbsorptionThreshold_satisfiable, ?_, ?_, ?_, ?_⟩
  · norm_num [intervalDomainSharpL2AbsorptionThresholdWitnessParams]
  · norm_num [intervalDomainSharpL2AbsorptionThresholdWitnessParams]
  · norm_num [intervalDomainSharpL2AbsorptionThresholdWitnessParams]
  · norm_num [intervalDomainSharpL2AbsorptionThresholdWitnessParams]

/-- Pure scalar first-crossing lemma for a continuous function satisfying an
integrated damping inequality. -/
theorem no_positive_of_integral_damping_ineq {H : ℝ → ℝ} {T lam : ℝ}
    (hlam : 0 < lam)
    (hcont : ContinuousOn H (Set.Icc 0 T)) (hH0 : H 0 ≤ 0)
    (hineq : ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
      H t2 - H t1 + lam * ∫ s in t1..t2, H s ≤ 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, H t ≤ 0 := by
  intro t ht
  by_contra hnot
  have hHt : 0 < H t := lt_of_not_ge hnot
  have ht0 : 0 ≤ t := ht.1
  have h0t : 0 ∈ Set.Icc (0 : ℝ) t := ⟨le_rfl, ht0⟩
  have htt : t ∈ Set.Icc (0 : ℝ) t := ⟨ht0, le_rfl⟩
  have hcont0t : ContinuousOn H (Set.Icc (0 : ℝ) t) :=
    hcont.mono (fun x hx => ⟨hx.1, le_trans hx.2 ht.2⟩)
  let Z : Set ℝ := {s | s ∈ Set.Icc (0 : ℝ) t ∧ H s = 0}
  have hZ_nonempty : Z.Nonempty := by
    by_cases hH0eq : H 0 = 0
    · exact ⟨0, h0t, hH0eq⟩
    · have hH0lt : H 0 < 0 := lt_of_le_of_ne hH0 hH0eq
      have hzero_mem : (0 : ℝ) ∈ Set.Icc (H 0) (H t) :=
        ⟨le_of_lt hH0lt, le_of_lt hHt⟩
      rcases isPreconnected_Icc.intermediate_value h0t htt hcont0t hzero_mem with
        ⟨z, hzI, hz⟩
      exact ⟨z, hzI, hz⟩
  have hZ_compact : IsCompact Z := by
    have hclosed : IsClosed (Set.Icc (0 : ℝ) t ∩ H ⁻¹' ({0} : Set ℝ)) :=
      hcont0t.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
    have hc : IsCompact (Set.Icc (0 : ℝ) t ∩ H ⁻¹' ({0} : Set ℝ)) :=
      IsCompact.of_isClosed_subset isCompact_Icc hclosed (fun _x hx => hx.1)
    simpa [Z, Set.setOf_and] using hc
  obtain ⟨τ, hτZ, hτmax⟩ :=
    hZ_compact.exists_isMaxOn hZ_nonempty continuousOn_id
  have hτI : τ ∈ Set.Icc (0 : ℝ) t := hτZ.1
  have hHτ : H τ = 0 := hτZ.2
  have hτt : τ < t := by
    have hτle : τ ≤ t := hτI.2
    exact lt_of_le_of_ne hτle (by
      intro hEq
      subst τ
      linarith)
  have hpos_after : ∀ s ∈ Set.Ioc τ t, 0 < H s := by
    intro s hs
    by_cases hst_eq : s = t
    · subst s
      exact hHt
    have hst : s < t := lt_of_le_of_ne hs.2 hst_eq
    by_contra hsnot
    have hHs : H s ≤ 0 := le_of_not_gt hsnot
    have hcontst : ContinuousOn H (Set.Icc s t) :=
      hcont0t.mono
        (fun x hx => ⟨le_trans hτI.1 (le_trans (le_of_lt hs.1) hx.1), hx.2⟩)
    have hs_mem : s ∈ Set.Icc s t := ⟨le_rfl, le_of_lt hst⟩
    have ht_mem : t ∈ Set.Icc s t := ⟨le_of_lt hst, le_rfl⟩
    have hzero_mem : (0 : ℝ) ∈ Set.Icc (H s) (H t) :=
      ⟨hHs, le_of_lt hHt⟩
    rcases isPreconnected_Icc.intermediate_value hs_mem ht_mem hcontst hzero_mem with
      ⟨z, hzI, hzH⟩
    have hzZ : z ∈ Z := by
      refine ⟨⟨?_, hzI.2⟩, hzH⟩
      exact le_trans hτI.1 (le_trans (le_of_lt hs.1) hzI.1)
    have hzleτ : z ≤ τ := hτmax hzZ
    have hτltz : τ < z := lt_of_lt_of_le hs.1 hzI.1
    linarith
  have hτT : τ ∈ Set.Icc (0 : ℝ) T := ⟨hτI.1, le_trans hτI.2 ht.2⟩
  have htτT : t ∈ Set.Icc τ T := ⟨le_of_lt hτt, ht.2⟩
  have hcontτt : ContinuousOn H (Set.Icc τ t) :=
    hcont.mono (fun x hx => ⟨le_trans hτI.1 hx.1, le_trans hx.2 ht.2⟩)
  have hint_pos : 0 < ∫ s in τ..t, H s :=
    intervalIntegral.integral_pos hτt hcontτt
      (fun x hx => le_of_lt (hpos_after x hx))
      ⟨t, ⟨le_of_lt hτt, le_rfl⟩, hHt⟩
  have hmain := hineq τ hτT t htτT
  nlinarith

/-- Pure scalar uniform bound derived from an integrated damping inequality. -/
theorem continuous_integral_ineq_uniform_bound {Y : ℝ → ℝ} {T lam K : ℝ}
    (hlam : 0 < lam)
    (hcont : ContinuousOn Y (Set.Icc 0 T))
    (hineq : ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
      Y t2 - Y t1 + lam * ∫ s in t1..t2, Y s ≤ K * (t2 - t1)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, Y t ≤ max (Y 0) (K / lam) := by
  let R : ℝ := max (Y 0) (K / lam)
  have hR0 : Y 0 ≤ R := le_max_left _ _
  have hRK : K / lam ≤ R := le_max_right _ _
  have hKR : K - lam * R ≤ 0 := by
    have hmul : K ≤ lam * R := by
      have := mul_le_mul_of_nonneg_left hRK hlam.le
      field_simp [ne_of_gt hlam] at this
      linarith
    linarith
  have hHcont : ContinuousOn (fun s => Y s - R) (Set.Icc (0 : ℝ) T) :=
    hcont.sub continuousOn_const
  have hH0 : (fun s => Y s - R) 0 ≤ 0 := by
    dsimp
    linarith
  have hHineq :
      ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
        (Y t2 - R) - (Y t1 - R) +
            lam * ∫ s in t1..t2, (Y s - R) ≤ 0 := by
    intro t1 ht1 t2 ht2
    have ht12 : t1 ≤ t2 := ht2.1
    have hcont12 : ContinuousOn Y (Set.Icc t1 t2) :=
      hcont.mono (fun x hx => ⟨le_trans ht1.1 hx.1, le_trans hx.2 ht2.2⟩)
    have hcont12u : ContinuousOn Y (Set.uIcc t1 t2) := by
      rwa [Set.uIcc_of_le ht12]
    have hYint : IntervalIntegrable Y MeasureTheory.volume t1 t2 :=
      hcont12u.intervalIntegrable
    have hCint : IntervalIntegrable (fun _ : ℝ => R) MeasureTheory.volume t1 t2 :=
      intervalIntegral.intervalIntegrable_const
    have hint_sub :
        (∫ s in t1..t2, (Y s - R)) =
          (∫ s in t1..t2, Y s) - (t2 - t1) * R := by
      rw [intervalIntegral.integral_sub hYint hCint]
      rw [intervalIntegral.integral_const]
      simp [smul_eq_mul]
    have hbase := hineq t1 ht1 t2 ht2
    rw [hint_sub]
    have hnonneg_len : 0 ≤ t2 - t1 := sub_nonneg.mpr ht12
    nlinarith
  have hnp := no_positive_of_integral_damping_ineq
    (H := fun s => Y s - R) (T := T) (lam := lam)
    hlam hHcont hH0 hHineq
  intro t ht
  have := hnp t ht
  dsimp [R] at this ⊢
  linarith

/-!
This file records the global-existence handoff for the a-priori route:

`mass control -> drift control -> Lp energy -> heat smoothing -> uniform L∞`.

The pure logistic maximum bound is not used here.  The final analytic output
consumed by continuation is the uniform pointwise upper bound on every finite
classical branch.
-/

/-- Standard continuation and gluing data for the corrected interval-domain
global-solution package. -/
structure IntervalDomainStandardContinuationGluingData (p : CM2Params) where
  localExistence :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u
  boundedInitial :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|))
  standardContinuation :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        1 ≤ p.m → StandardContinuationAlternative p u₀
  gluing : GlobalSolutionGluingFromReachability p

/-- The finite-supremum continuation form already used by
`IntervalDomainExistence`.  It is repackaged here so the a-priori bound can be
connected either to the standard continuation alternative or to the more
structural finite-sup skeleton. -/
structure IntervalDomainFiniteSupContinuationGluingData (p : CM2Params) where
  localExistence :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u
  boundedInitial :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|))
  realize :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ _hbdd : BddAbove (reachableClassicalHorizonSet p u₀),
      ∃ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p
          (finiteMaximalReachableHorizon p u₀) u v ∧
        InitialTrace intervalDomain u₀ u
  extendOfNotFiniteAlternative :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ (_hbdd : BddAbove (reachableClassicalHorizonSet p u₀))
      {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p
          (finiteMaximalReachableHorizon p u₀) u v →
        InitialTrace intervalDomain u₀ u →
        ¬ FiniteHorizonAlternative intervalDomain
          (finiteMaximalReachableHorizon p u₀) u →
        ReachablePast p u₀ (finiteMaximalReachableHorizon p u₀)
  extendOfNotMgeAlternative :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ (_hbdd : BddAbove (reachableClassicalHorizonSet p u₀))
      {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p
          (finiteMaximalReachableHorizon p u₀) u v →
        InitialTrace intervalDomain u₀ u →
        1 ≤ p.m →
        ¬ MGeOneFiniteHorizonAlternative intervalDomain
          (finiteMaximalReachableHorizon p u₀) u →
        ReachablePast p u₀ (finiteMaximalReachableHorizon p u₀)
  gluing : GlobalSolutionGluingFromReachability p

/-- The structural finite-sup continuation package supplies the standard
continuation alternative. -/
def IntervalDomainFiniteSupContinuationGluingData.to_standard
    {p : CM2Params}
    (h : IntervalDomainFiniteSupContinuationGluingData p) :
    IntervalDomainStandardContinuationGluingData p where
  localExistence := h.localExistence
  boundedInitial := h.boundedInitial
  standardContinuation := by
    intro u₀ hu₀ _hm
    exact standardContinuationAlternative_of_finiteSup_realization_and_extension
      p h.localExistence hu₀
      (h.realize u₀ hu₀)
      (h.extendOfNotFiniteAlternative u₀ hu₀)
      (h.extendOfNotMgeAlternative u₀ hu₀)
  gluing := h.gluing

/-- Final output of the one-dimensional mass/Lp/heat-smoothing a-priori
argument.  The parameter fields record the intended paper regime; the proof
below consumes the bound field, not the false pure-logistic maximum estimate. -/
structure IntervalDomainMassLpSmoothingAprioriBound (p : CM2Params) where
  a_pos : 0 < p.a
  b_pos : 0 < p.b
  chi_nonneg : 0 ≤ p.χ₀
  pointwiseBound :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        ∃ B, ∀ t x, 0 < t → t < T → x ∈ intervalDomain.inside →
          u t x ≤ B

/-- The drift `w = v_x / (1 + v)^β` used by the one-dimensional Lp route. -/
def intervalDomainChemotacticDrift
    (p : CM2Params) (v : intervalDomain.Point → ℝ) (y : ℝ) : ℝ :=
  deriv (intervalDomainLift v) y / (1 + intervalDomainLift v y) ^ p.β

/-- Output of the mass comparison step on a finite classical branch. -/
def IntervalDomainLogisticMassBound
    (_p : CM2Params) (T : ℝ) (u : ℝ → intervalDomain.Point → ℝ) : Prop :=
  ∃ Mmass, 0 ≤ Mmass ∧
    ∀ t, 0 < t → t < T → intervalDomain.integral (u t) ≤ Mmass

/-- Output of the elliptic resolver step: the drift is uniformly bounded. -/
def IntervalDomainChemotacticDriftBound
    (p : CM2Params) (T : ℝ) (v : ℝ → intervalDomain.Point → ℝ) : Prop :=
  ∃ W, 0 ≤ W ∧
    ∀ t y, 0 < t → t < T → y ∈ Set.Icc (0 : ℝ) 1 →
      |intervalDomainChemotacticDrift p (v t) y| ≤ W

/-- The closed absorbing half-energy differential inequality obtained after
spatially absorbing the lower-order `u²` and `u^(2+2γ)` terms.  Written with
`2 * deriv (1/2 ∫u²)` to avoid adding a separate time-regularity bridge for
`deriv (∫u²)`; this is the same differential quantity on classical branches. -/
def IntervalDomainL2AbsorbingDifferentialInequalityResult
    (p : CM2Params) (T : ℝ) (u : ℝ → intervalDomain.Point → ℝ) : Prop :=
  ∃ delta : ℝ, ∃ K : ℝ, 0 < delta ∧ 0 ≤ K ∧
    ∀ t, 0 < t → t < T →
      2 * deriv (fun τ => intervalDomainL2HalfEnergy u τ) t +
          delta * intervalDomainL2DiffusionDissipation u t +
          p.b * intervalDomain.integral
            (fun x => (u t x) ^ (2 + p.α)) ≤ K

/-- The remaining time-regularity frontiers needed to feed the scalar L² seed
interface.  The old formulation also required
`deriv (fun t => ∫ |u(t)|²) 0 ≤ 0`; that condition is false for small data
because the logistic growth can initially raise the L² energy.  The actual
seed only needs continuity and a finite initial L² size, together with the
standard interior derivative alignment used to consume the differential energy
inequality. -/
structure IntervalDomainL2SeedRegularityFrontier
    (T : ℝ) (u : ℝ → intervalDomain.Point → ℝ) where
  energyContinuous :
    ContinuousOn (fun t => intervalDomainLpAbsEnergy 2 u t)
      (Set.Icc (0 : ℝ) T)
  energyHasDerivWithin :
    ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt
        (fun τ => intervalDomainLpAbsEnergy 2 u τ)
        (deriv (fun τ => intervalDomainLpAbsEnergy 2 u τ) t)
        (Set.Ici t) t
  initialBound :
    ∃ δ0, 0 ≤ δ0 ∧ intervalDomainLpAbsEnergy 2 u 0 ≤ δ0
  derivativeAlignment :
    ∀ t ∈ Set.Ico (0 : ℝ) T,
      deriv (fun τ => intervalDomainLpAbsEnergy 2 u τ) t =
        2 * deriv (fun τ => intervalDomainL2HalfEnergy u τ) t

/-- Integrated absorbing inequality for the L² energy.  This is the exact
interface consumed by the first-crossing lemma: it bounds `Y` by
`max Y(0) (K / λ)` and does not ask for any sign of `Y'(0)`. -/
def IntervalDomainL2AbsorbingIntegratedInequalityResult
    (_p : CM2Params) (T : ℝ) (u : ℝ → intervalDomain.Point → ℝ) : Prop :=
  ∃ lam : ℝ, ∃ K : ℝ, 0 < lam ∧ 0 ≤ K ∧
    ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
      intervalDomainLpAbsEnergy 2 u t2 - intervalDomainLpAbsEnergy 2 u t1 +
          lam * ∫ s in t1..t2, intervalDomainLpAbsEnergy 2 u s ≤
        K * (t2 - t1)

/-- The exact spatial estimate needed after the half-energy inequality has
produced a fixed `Ceps`.

The consumer fixes
`eps0 = 1 / (2 * (|χ₀| + 1))`; requiring absorption for every positive `eps`
is stronger than the L² seed needs and is false for large `eps`, since the
diffusion coefficient is fixed.  This interface is deliberately pinned to the
consumer's small `eps0`. -/
def IntervalDomainL2SpatialAbsorptionEstimate
    (p : CM2Params) (T : ℝ)
    (u v : ℝ → intervalDomain.Point → ℝ)
    (_hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (_hmass : IntervalDomainLogisticMassBound p T u) : Prop :=
  ∀ Ceps : ℝ,
    ∃ delta : ℝ, ∃ K : ℝ, 0 < delta ∧ delta ≤ 2 ∧ 0 ≤ K ∧
    ∀ t, 0 < t → t < T →
      2 * (|p.χ₀| *
          ((1 / (2 * (|p.χ₀| + 1))) *
              intervalDomainLpWeightedGradientDissipation 2 u t +
            Ceps * intervalDomain.integral
              (fun x => (u t x) ^ (2 + 2 * p.γ))) +
        intervalDomainL2LogisticIntegral p u t) +
        p.b * intervalDomain.integral
          (fun x => (u t x) ^ (2 + p.α)) ≤
          (2 - delta) * intervalDomainL2DiffusionDissipation u t + K

theorem intervalDomainL2SpatialAbsorptionConsumerEps_pos (p : CM2Params) :
    0 < (1 / (2 * (|p.χ₀| + 1)) : ℝ) := by
  positivity

theorem intervalDomainL2SpatialAbsorptionConsumerEps_scaled_lt_one
    (p : CM2Params) :
    2 * |p.χ₀| * (1 / (2 * (|p.χ₀| + 1)) : ℝ) < 1 := by
  have hden : 0 < |p.χ₀| + 1 := by positivity
  have hratio : |p.χ₀| / (|p.χ₀| + 1) < 1 := by
    rw [div_lt_one hden]
    linarith
  calc
    2 * |p.χ₀| * (1 / (2 * (|p.χ₀| + 1)) : ℝ)
        = |p.χ₀| / (|p.χ₀| + 1) := by
          field_simp [ne_of_gt hden]
    _ < 1 := hratio

/-- Scalar Young absorption for real powers:
`A x^r` is controlled by an arbitrarily small multiple of `x^s`, up to a
constant, whenever `0 < r < s`. -/
theorem scalar_rpow_young_absorb
    {r s A eps x : ℝ} (hr : 0 < r) (hrs : r < s)
    (hA : 0 ≤ A) (heps : 0 < eps) (hx : 0 ≤ x) :
    A * x ^ r ≤ eps * x ^ s +
      ((A / (eps * (s / r)) ^ (r / s)) ^ (s / (s - r))) /
        (s / (s - r)) := by
  let pExp : ℝ := s / r
  let qExp : ℝ := s / (s - r)
  have hp_gt : 1 < pExp := by
    dsimp [pExp]
    rw [one_lt_div hr]
    exact hrs
  have hq_gt : 1 < qExp := by
    dsimp [qExp]
    have hsr : 0 < s - r := sub_pos.mpr hrs
    rw [one_lt_div hsr]
    linarith
  have hp_pos : 0 < pExp := lt_trans zero_lt_one hp_gt
  have hp_ne : pExp ≠ 0 := ne_of_gt hp_pos
  have hpq : pExp.HolderConjugate qExp := by
    rw [Real.holderConjugate_iff]
    refine ⟨hp_gt, ?_⟩
    dsimp [pExp, qExp]
    field_simp [ne_of_gt hr, ne_of_gt (sub_pos.mpr hrs),
      ne_of_gt (lt_trans hr hrs)]
    ring
  let B : ℝ := (eps * pExp) ^ (1 / pExp)
  have hB_pos : 0 < B := by
    dsimp [B]
    exact Real.rpow_pos_of_pos (mul_pos heps hp_pos) _
  have hleft_nonneg : 0 ≤ B * x ^ r :=
    mul_nonneg hB_pos.le (Real.rpow_nonneg hx _)
  have hright_nonneg : 0 ≤ A / B := div_nonneg hA hB_pos.le
  have hY := Real.young_inequality_of_nonneg
    (a := B * x ^ r) (b := A / B) hleft_nonneg hright_nonneg hpq
  have hab : (B * x ^ r) * (A / B) = A * x ^ r := by
    field_simp [ne_of_gt hB_pos]
  have hBp : B ^ pExp = eps * pExp := by
    dsimp [B]
    rw [← Real.rpow_mul (mul_pos heps hp_pos).le]
    have : (1 / pExp) * pExp = 1 := by field_simp [hp_ne]
    rw [this, Real.rpow_one]
  have hxrp : (x ^ r) ^ pExp = x ^ s := by
    rw [← Real.rpow_mul hx]
    dsimp [pExp]
    have : r * (s / r) = s := by field_simp [ne_of_gt hr]
    rw [this]
  have hterm1 : (B * x ^ r) ^ pExp / pExp = eps * x ^ s := by
    rw [Real.mul_rpow hB_pos.le (Real.rpow_nonneg hx _), hBp, hxrp]
    field_simp [ne_of_gt hp_pos]
  calc
    A * x ^ r = (B * x ^ r) * (A / B) := hab.symm
    _ ≤ (B * x ^ r) ^ pExp / pExp + (A / B) ^ qExp / qExp := hY
    _ = eps * x ^ s + (A / B) ^ qExp / qExp := by rw [hterm1]
    _ = eps * x ^ s +
        ((A / (eps * (s / r)) ^ (r / s)) ^ (s / (s - r))) /
          (s / (s - r)) := by
      congr 1
      dsimp [B, pExp, qExp]
      congr 2
      rw [show 1 / (s / r) = r / s by
        field_simp [ne_of_gt hr, ne_of_gt (lt_trans hr hrs)]]

/-- Integral version of the scalar power absorption on positive classical
interval-domain slices. -/
theorem intervalDomain_integral_rpow_absorb_of_classical
    {p : CM2Params} {T r s A eps : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hr : 1 < r) (hrs : r < s) (hA : 0 ≤ A) (heps : 0 < eps)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    A * intervalDomain.integral
        (fun x : intervalDomain.Point => (u t x) ^ r) ≤
      eps * intervalDomain.integral
        (fun x : intervalDomain.Point => (u t x) ^ s) +
        ((A / (eps * (s / r)) ^ (r / s)) ^ (s / (s - r))) /
          (s / (s - r)) := by
  have hs_gt_one : 1 < s := lt_trans hr hrs
  have hr_pos : 0 < r := lt_trans zero_lt_one hr
  have hpow_r :
      IntervalIntegrable
        (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ r))
        MeasureTheory.volume 0 1 :=
    intervalDomain_classical_solution_powerIntegrable hsol r hr t ht0 htT
  have hpow_s :
      IntervalIntegrable
        (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ s))
        MeasureTheory.volume 0 1 :=
    intervalDomain_classical_solution_powerIntegrable hsol s hs_gt_one t ht0 htT
  let K : ℝ :=
    ((A / (eps * (s / r)) ^ (r / s)) ^ (s / (s - r))) /
      (s / (s - r))
  have hleft_int :
      IntervalIntegrable
        (fun y : ℝ =>
          A * intervalDomainLift
            (fun x : intervalDomain.Point => (u t x) ^ r) y)
        MeasureTheory.volume 0 1 :=
    hpow_r.const_mul A
  have hright_int :
      IntervalIntegrable
        (fun y : ℝ =>
          eps * intervalDomainLift
            (fun x : intervalDomain.Point => (u t x) ^ s) y + K)
        MeasureTheory.volume 0 1 :=
    (hpow_s.const_mul eps).add intervalIntegral.intervalIntegrable_const
  have hpoint :
      ∀ y ∈ Set.Icc (0 : ℝ) 1,
        A * intervalDomainLift
            (fun x : intervalDomain.Point => (u t x) ^ r) y ≤
          eps * intervalDomainLift
            (fun x : intervalDomain.Point => (u t x) ^ s) y + K := by
    intro y hy
    let x : intervalDomain.Point := ⟨y, hy⟩
    have hux_nonneg : 0 ≤ u t x := le_of_lt (hsol.u_pos' ht0 htT)
    have hscalar := scalar_rpow_young_absorb
      (r := r) (s := s) (A := A) (eps := eps) (x := u t x)
      hr_pos hrs hA heps hux_nonneg
    simpa [K, intervalDomainLift, hy, x] using hscalar
  have hmono :
      ∫ y in (0 : ℝ)..1,
          A * intervalDomainLift
            (fun x : intervalDomain.Point => (u t x) ^ r) y ≤
        ∫ y in (0 : ℝ)..1,
          eps * intervalDomainLift
            (fun x : intervalDomain.Point => (u t x) ^ s) y + K :=
    intervalIntegral.integral_mono_on (by norm_num) hleft_int hright_int hpoint
  unfold intervalDomain intervalDomainIntegral
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hpow_s.const_mul eps)
      intervalIntegral.intervalIntegrable_const,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const] at hmono
  simpa [K, smul_eq_mul] using hmono

/-- At `p = 2`, the weighted gradient dissipation is exactly the L² diffusion
dissipation on positive classical slices. -/
theorem intervalDomainLpWeightedGradientDissipation_two_eq_l2DiffusionDissipation
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (_hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {t : ℝ} (_ht0 : 0 < t) (_htT : t < T) :
    intervalDomainLpWeightedGradientDissipation 2 u t =
      intervalDomainL2DiffusionDissipation u t := by
  unfold intervalDomainLpWeightedGradientDissipation
  unfold intervalDomainL2DiffusionDissipation
  unfold intervalDomainDerivativePairIntegral
  unfold intervalDomain intervalDomainIntegral
  apply intervalIntegral.integral_congr
  intro y hy
  have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hy
  simp [intervalDomainLift, intervalDomainGradNorm, hyIcc, Real.rpow_zero]
  ring

/-- Produce the L² spatial absorption estimate from the classical slice power
absorption, the logistic mass route's positive solution data, and the sharp
small `eps0` used by the consumer. -/
theorem intervalDomainL2SpatialAbsorptionEstimate_of_classical
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IntervalDomainBoundednessHyp p)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hmass : IntervalDomainLogisticMassBound p T u) :
    IntervalDomainL2SpatialAbsorptionEstimate p T u v hsol hmass := by
  intro Ceps
  let eps0 : ℝ := 1 / (2 * (|p.χ₀| + 1))
  let scaled : ℝ := 2 * |p.χ₀| * eps0
  let delta : ℝ := (1 - scaled) / 2
  let qExp : ℝ := 2 + 2 * p.γ
  let sExp : ℝ := 2 + p.α
  let Achem : ℝ := 2 * |p.χ₀| * |Ceps|
  let Agrow : ℝ := 2 * p.a
  let Kchem : ℝ :=
    ((Achem / ((p.b / 2) * (sExp / qExp)) ^ (qExp / sExp)) ^
        (sExp / (sExp - qExp))) /
      (sExp / (sExp - qExp))
  let Kgrow : ℝ :=
    ((Agrow / ((p.b / 2) * (sExp / (2 : ℝ))) ^ ((2 : ℝ) / sExp)) ^
        (sExp / (sExp - (2 : ℝ)))) /
      (sExp / (sExp - (2 : ℝ)))
  refine ⟨delta, max 0 (Kchem + Kgrow), ?_, ?_, ?_, ?_⟩
  · have hscaled_lt : scaled < 1 := by
      dsimp [scaled, eps0]
      exact intervalDomainL2SpatialAbsorptionConsumerEps_scaled_lt_one p
    dsimp [delta]
    linarith
  · have hscaled_nonneg : 0 ≤ scaled := by
      dsimp [scaled, eps0]
      positivity
    dsimp [delta]
    linarith
  · exact le_max_left 0 (Kchem + Kgrow)
  · intro t ht0 htT
    have hbhalf_pos : 0 < p.b / 2 := half_pos hbounded.2.1
    have hscaled_lt : scaled < 1 := by
      dsimp [scaled, eps0]
      exact intervalDomainL2SpatialAbsorptionConsumerEps_scaled_lt_one p
    have hq_gt_one : 1 < qExp := by
      dsimp [qExp]
      nlinarith [p.hγ]
    have hq_lt_s : qExp < sExp := by
      dsimp [qExp, sExp]
      nlinarith [hbounded.2.2.1]
    have htwo_lt_s : (2 : ℝ) < sExp := by
      dsimp [sExp]
      linarith [p.hα]
    have hAchem_nonneg : 0 ≤ Achem := by
      dsimp [Achem]
      positivity
    have hAgrow_nonneg : 0 ≤ Agrow := by
      dsimp [Agrow]
      exact mul_nonneg (by norm_num) p.ha
    have hchem_absorb :
        Achem * intervalDomain.integral
            (fun x : intervalDomain.Point => (u t x) ^ qExp) ≤
          (p.b / 2) * intervalDomain.integral
            (fun x : intervalDomain.Point => (u t x) ^ sExp) + Kchem := by
      simpa [Kchem] using
        intervalDomain_integral_rpow_absorb_of_classical
          (p := p) (T := T) (r := qExp) (s := sExp)
          (A := Achem) (eps := p.b / 2) (u := u) (v := v)
          hsol hq_gt_one hq_lt_s hAchem_nonneg hbhalf_pos ht0 htT
    have hgrow_absorb :
        Agrow * intervalDomain.integral
            (fun x : intervalDomain.Point => (u t x) ^ (2 : ℝ)) ≤
          (p.b / 2) * intervalDomain.integral
            (fun x : intervalDomain.Point => (u t x) ^ sExp) + Kgrow := by
      simpa [Kgrow] using
        intervalDomain_integral_rpow_absorb_of_classical
          (p := p) (T := T) (r := (2 : ℝ)) (s := sExp)
          (A := Agrow) (eps := p.b / 2) (u := u) (v := v)
          hsol (by norm_num) htwo_lt_s hAgrow_nonneg hbhalf_pos ht0 htT
    have hchem_coeff :
        2 * |p.χ₀| * Ceps *
            intervalDomain.integral
              (fun x : intervalDomain.Point => (u t x) ^ qExp) ≤
          Achem * intervalDomain.integral
              (fun x : intervalDomain.Point => (u t x) ^ qExp) := by
      have hint_nonneg :
          0 ≤ intervalDomain.integral
            (fun x : intervalDomain.Point => (u t x) ^ qExp) := by
        unfold intervalDomain intervalDomainIntegral
        refine intervalIntegral.integral_nonneg (by norm_num) ?_
        intro y hy
        have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := by
          simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hy
        let x : intervalDomain.Point := ⟨y, hyIcc⟩
        have hnonneg : 0 ≤ u t x := le_of_lt (hsol.u_pos' ht0 htT)
        simpa [intervalDomainLift, hyIcc, x] using
          Real.rpow_nonneg hnonneg qExp
      have hcoef : 2 * |p.χ₀| * Ceps ≤ Achem := by
        dsimp [Achem]
        nlinarith [le_abs_self Ceps, abs_nonneg p.χ₀]
      exact mul_le_mul_of_nonneg_right hcoef hint_nonneg
    have hW_eq :
        intervalDomainLpWeightedGradientDissipation 2 u t =
          intervalDomainL2DiffusionDissipation u t :=
      intervalDomainLpWeightedGradientDissipation_two_eq_l2DiffusionDissipation
        hsol ht0 htT
    have hD_nonneg : 0 ≤ intervalDomainL2DiffusionDissipation u t := by
      unfold intervalDomainL2DiffusionDissipation
      unfold intervalDomainDerivativePairIntegral
      refine intervalIntegral.integral_nonneg (by norm_num) (fun y _hy => ?_)
      nlinarith [sq_nonneg (deriv (intervalDomainLift (u t)) y)]
    have hD_absorb :
        scaled * intervalDomainL2DiffusionDissipation u t ≤
          (2 - delta) * intervalDomainL2DiffusionDissipation u t := by
      have hcoef : scaled ≤ 2 - delta := by
        dsimp [delta]
        linarith [hscaled_lt]
      exact mul_le_mul_of_nonneg_right hcoef hD_nonneg
    have hlog_rewrite :
        2 * intervalDomainL2LogisticIntegral p u t +
            p.b * intervalDomain.integral
              (fun x : intervalDomain.Point => (u t x) ^ sExp) =
          Agrow * intervalDomain.integral
              (fun x : intervalDomain.Point => (u t x) ^ (2 : ℝ)) -
            p.b * intervalDomain.integral
              (fun x : intervalDomain.Point => (u t x) ^ sExp) := by
      have hpow_two :
          IntervalIntegrable
            (intervalDomainLift
              (fun x : intervalDomain.Point => (u t x) ^ (2 : ℝ)))
            MeasureTheory.volume 0 1 :=
        intervalDomain_classical_solution_powerIntegrable
          hsol 2
            (by norm_num) t ht0 htT
      have hpow_s :
          IntervalIntegrable
            (intervalDomainLift
              (fun x : intervalDomain.Point => (u t x) ^ sExp))
            MeasureTheory.volume 0 1 :=
        intervalDomain_classical_solution_powerIntegrable
          hsol sExp
            (by dsimp [sExp]; linarith [p.hα]) t ht0 htT
      have hlog_int :
          IntervalIntegrable
            (intervalDomainLift
              (fun x : intervalDomain.Point =>
                (u t x) ^ 2 *
                  (p.a - p.b * (u t x) ^ p.α)))
            MeasureTheory.volume 0 1 := by
        have hlin :
            IntervalIntegrable
              (fun y : ℝ =>
                p.a *
                    intervalDomainLift
                      (fun x : intervalDomain.Point => (u t x) ^ (2 : ℝ)) y -
                  p.b *
                    intervalDomainLift
                      (fun x : intervalDomain.Point => (u t x) ^ sExp) y)
              MeasureTheory.volume 0 1 :=
          (hpow_two.const_mul p.a).sub (hpow_s.const_mul p.b)
        refine hlin.congr ?_
        intro y hy
        have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := by
          have hyIoc : y ∈ Set.Ioc (0 : ℝ) 1 := by
            simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hy
          exact ⟨le_of_lt hyIoc.1, hyIoc.2⟩
        let x : intervalDomain.Point := ⟨y, hyIcc⟩
        have hpos : 0 < u t x := hsol.u_pos' ht0 htT
        have hpow_add :
            (u t x) ^ (2 + p.α) =
              (u t x) ^ (2 : ℝ) * (u t x) ^ p.α := by
          rw [Real.rpow_add hpos]
        simp [intervalDomainLift, hyIcc, x, sExp, hpow_add]
        ring
      unfold intervalDomainL2LogisticIntegral
      have hlog_eq :
          intervalDomain.integral
                (fun x : intervalDomain.Point =>
                  (u t x) ^ 2 *
                    (p.a - p.b * (u t x) ^ p.α)) =
            p.a * intervalDomain.integral
              (fun x : intervalDomain.Point => (u t x) ^ (2 : ℝ)) -
            p.b * intervalDomain.integral
              (fun x : intervalDomain.Point => (u t x) ^ sExp) := by
        unfold intervalDomain intervalDomainIntegral
        have hcongr :
            ∫ y in (0 : ℝ)..1,
                intervalDomainLift
                  (fun x : intervalDomain.Point =>
                    (u t x) ^ 2 *
                      (p.a - p.b * (u t x) ^ p.α)) y =
              ∫ y in (0 : ℝ)..1,
                p.a *
                    intervalDomainLift
                      (fun x : intervalDomain.Point => (u t x) ^ (2 : ℝ)) y -
                  p.b *
                    intervalDomainLift
                      (fun x : intervalDomain.Point => (u t x) ^ sExp) y := by
          apply intervalIntegral.integral_congr
          intro y hy
          have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := by
            simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hy
          let x : intervalDomain.Point := ⟨y, hyIcc⟩
          have hpos : 0 < u t x := hsol.u_pos' ht0 htT
          have hpow_add :
              (u t x) ^ (2 + p.α) =
                (u t x) ^ (2 : ℝ) * (u t x) ^ p.α := by
            rw [Real.rpow_add hpos]
          simp [intervalDomainLift, hyIcc, x, sExp, hpow_add]
          ring
        change
          (∫ y in (0 : ℝ)..1,
              intervalDomainLift
                (fun x : intervalDomain.Point =>
                  (u t x) ^ 2 *
                    (p.a - p.b * (u t x) ^ p.α)) y) =
            p.a * (∫ y in (0 : ℝ)..1,
              intervalDomainLift
                (fun x : intervalDomain.Point => (u t x) ^ (2 : ℝ)) y) -
            p.b * (∫ y in (0 : ℝ)..1,
              intervalDomainLift
                (fun x : intervalDomain.Point => (u t x) ^ sExp) y)
        rw [hcongr]
        rw [intervalIntegral.integral_sub (hpow_two.const_mul p.a)
          (hpow_s.const_mul p.b)]
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
      calc
        2 * intervalDomain.integral
              (fun x : intervalDomain.Point =>
                (u t x) ^ 2 *
                  (p.a - p.b * (u t x) ^ p.α)) +
            p.b * intervalDomain.integral
              (fun x : intervalDomain.Point => (u t x) ^ sExp)
            =
          2 * (p.a * intervalDomain.integral
              (fun x : intervalDomain.Point => (u t x) ^ (2 : ℝ)) -
            p.b * intervalDomain.integral
              (fun x : intervalDomain.Point => (u t x) ^ sExp)) +
            p.b * intervalDomain.integral
              (fun x : intervalDomain.Point => (u t x) ^ sExp) := by
              rw [hlog_eq]
        _ =
          Agrow * intervalDomain.integral
              (fun x : intervalDomain.Point => (u t x) ^ (2 : ℝ)) -
            p.b * intervalDomain.integral
              (fun x : intervalDomain.Point => (u t x) ^ sExp) := by
              dsimp [Agrow]
              ring
    have hrest :
        2 * |p.χ₀| * Ceps *
            intervalDomain.integral
              (fun x : intervalDomain.Point => (u t x) ^ qExp) +
          (2 * intervalDomainL2LogisticIntegral p u t +
            p.b * intervalDomain.integral
              (fun x : intervalDomain.Point => (u t x) ^ sExp)) ≤
          Kchem + Kgrow := by
      rw [hlog_rewrite]
      nlinarith [hchem_coeff, hchem_absorb, hgrow_absorb]
    have hrest_max :
        2 * |p.χ₀| * Ceps *
            intervalDomain.integral
              (fun x : intervalDomain.Point => (u t x) ^ qExp) +
          (2 * intervalDomainL2LogisticIntegral p u t +
            p.b * intervalDomain.integral
              (fun x : intervalDomain.Point => (u t x) ^ sExp)) ≤
          max 0 (Kchem + Kgrow) :=
      le_trans hrest (le_max_right 0 (Kchem + Kgrow))
    dsimp [scaled] at hD_absorb
    dsimp [eps0, qExp] at hrest_max
    rw [hW_eq]
    nlinarith

/-- The L² diffusion term is nonnegative on the concrete interval because it is
the integral of the square of the lifted spatial derivative. -/
theorem intervalDomainL2DiffusionDissipation_nonneg
    (u : ℝ → intervalDomain.Point → ℝ) (t : ℝ) :
    0 ≤ intervalDomainL2DiffusionDissipation u t := by
  unfold intervalDomainL2DiffusionDissipation
  unfold intervalDomainDerivativePairIntegral
  refine intervalIntegral.integral_nonneg (by norm_num) (fun y _hy => ?_)
  nlinarith [sq_nonneg (deriv (intervalDomainLift (u t)) y)]

/-- The positive-power logistic sink integral in the L² absorbing estimate is
nonnegative on classical positive interval-domain solutions. -/
theorem intervalDomainL2LogisticSinkIntegral_nonneg
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    0 ≤ intervalDomain.integral
      (fun x : intervalDomain.Point => (u t x) ^ (2 + p.α)) := by
  unfold intervalDomain intervalDomainIntegral
  refine intervalIntegral.integral_nonneg (by norm_num) (fun y hy => ?_)
  have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hy
  unfold intervalDomainLift
  rw [dif_pos hyIcc]
  exact Real.rpow_nonneg (le_of_lt (hsol.u_pos' ht0 htT)) (2 + p.α)

/-- On positive classical interval slices, the logistic `u^(2+α)` sink controls
the L² energy up to the unit-volume constant. -/
theorem intervalDomainLpAbsEnergy_two_le_one_add_logisticSink
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    intervalDomainLpAbsEnergy 2 u t ≤
      1 + intervalDomain.integral
        (fun x : intervalDomain.Point => (u t x) ^ (2 + p.α)) := by
  have h2_int :
      IntervalIntegrable
        (fun y : ℝ =>
          intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ (2 : ℝ)) y)
        MeasureTheory.volume 0 1 := by
    have hcont :
        ContinuousOn
          (fun y : ℝ =>
            intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ (2 : ℝ)) y)
          (Set.Icc (0 : ℝ) 1) := by
      have hucont : ContinuousOn (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
        ((hsol.regularity.2.2.2.2.1 t ⟨ht0, htT⟩).1.1).continuousOn
      have hpos :
          ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (u t) y := by
        intro y hy
        let x : intervalDomain.Point := ⟨y, hy⟩
        unfold intervalDomainLift
        rw [dif_pos hy]
        exact (hsol.u_pos' ht0 htT : 0 < u t x)
      refine (hucont.rpow_const (p := (2 : ℝ)) ?_).congr ?_
      · intro y hy
        exact Or.inl (ne_of_gt (hpos y hy))
      · intro y hy
        simp [intervalDomainLift, hy]
    have hcontu :
        ContinuousOn
          (fun y : ℝ =>
            intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ (2 : ℝ)) y)
          (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hcont
    exact hcontu.intervalIntegrable
  have hpow_int :
      IntervalIntegrable
        (fun y : ℝ =>
          intervalDomainLift
            (fun x : intervalDomain.Point => (u t x) ^ (2 + p.α)) y)
        MeasureTheory.volume 0 1 := by
    have hcont :
        ContinuousOn
          (fun y : ℝ =>
            intervalDomainLift
              (fun x : intervalDomain.Point => (u t x) ^ (2 + p.α)) y)
          (Set.Icc (0 : ℝ) 1) := by
      have hucont : ContinuousOn (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
        ((hsol.regularity.2.2.2.2.1 t ⟨ht0, htT⟩).1.1).continuousOn
      have hpos :
          ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (u t) y := by
        intro y hy
        let x : intervalDomain.Point := ⟨y, hy⟩
        unfold intervalDomainLift
        rw [dif_pos hy]
        exact (hsol.u_pos' ht0 htT : 0 < u t x)
      refine (hucont.rpow_const (p := 2 + p.α)
        (fun y hy => Or.inl (ne_of_gt (hpos y hy)))).congr ?_
      intro y hy
      simp [intervalDomainLift, hy]
    have hcontu :
        ContinuousOn
          (fun y : ℝ =>
            intervalDomainLift
              (fun x : intervalDomain.Point => (u t x) ^ (2 + p.α)) y)
          (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hcont
    exact hcontu.intervalIntegrable
  have hright_int :
      IntervalIntegrable
        (fun y : ℝ =>
          1 +
            intervalDomainLift
              (fun x : intervalDomain.Point => (u t x) ^ (2 + p.α)) y)
        MeasureTheory.volume 0 1 := by
    exact intervalIntegral.intervalIntegrable_const.add hpow_int
  have hpoint :
      ∀ y ∈ Set.Icc (0 : ℝ) 1,
        intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ (2 : ℝ)) y ≤
          intervalDomainLift
              (fun x : intervalDomain.Point => (u t x) ^ (2 + p.α)) y + 1 := by
    intro y hy
    let x : intervalDomain.Point := ⟨y, hy⟩
    have hu_pos : 0 < u t x := (hsol.u_pos' ht0 htT : 0 < u t x)
    have hu_nonneg : 0 ≤ u t x := le_of_lt hu_pos
    have hmain :
        (u t x) ^ (2 : ℝ) ≤ (u t x) ^ (2 + p.α) + 1 :=
      ShenWork.Paper2.IntervalDomainLpMonotonicity.rpow_le_one_add_rpow_of_nonneg_of_le
        hu_nonneg (by norm_num : (0 : ℝ) ≤ 2) (by linarith [p.hα])
    unfold intervalDomainLift
    rw [dif_pos hy, dif_pos hy]
    exact hmain
  have habs_eq :
      intervalDomainLpAbsEnergy 2 u t =
        intervalDomain.integral
          (fun x : intervalDomain.Point => (u t x) ^ (2 : ℝ)) := by
    unfold intervalDomainLpAbsEnergy
    congr
    ext x
    have hxnonneg : 0 ≤ u t x := le_of_lt (hsol.u_pos' ht0 htT : 0 < u t x)
    rw [abs_of_nonneg hxnonneg]
  rw [habs_eq]
  unfold intervalDomain intervalDomainIntegral
  calc
    ∫ y in (0 : ℝ)..1,
        intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ (2 : ℝ)) y
        ≤ ∫ y in (0 : ℝ)..1,
              intervalDomainLift
                (fun x : intervalDomain.Point => (u t x) ^ (2 + p.α)) y + 1 :=
          intervalIntegral.integral_mono_on (by norm_num) h2_int
            (hpow_int.add intervalIntegral.intervalIntegrable_const) hpoint
    _ = 1 + ∫ y in (0 : ℝ)..1,
          intervalDomainLift
            (fun x : intervalDomain.Point => (u t x) ^ (2 + p.α)) y := by
          rw [intervalIntegral.integral_add hpow_int intervalIntegral.intervalIntegrable_const]
          rw [intervalIntegral.integral_const]
          simp [smul_eq_mul]
          ring

/-- Integrate the closed absorbing differential inequality and use the
logistic sink to produce the first-crossing integrated L² inequality. -/
theorem IntervalDomainL2AbsorbingIntegratedInequality
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hb : 0 < p.b)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (habsorbing : IntervalDomainL2AbsorbingDifferentialInequalityResult p T u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u) :
    IntervalDomainL2AbsorbingIntegratedInequalityResult p T u := by
  rcases habsorbing with ⟨delta, K, hdelta_pos, hK_nonneg, habs⟩
  let Y : ℝ → ℝ := fun t => intervalDomainLpAbsEnergy 2 u t
  let lam : ℝ := p.b / 2
  let Kint : ℝ := K + p.b / 2
  have hlam : 0 < lam := by
    dsimp [lam]
    exact half_pos hb
  have hKint_nonneg : 0 ≤ Kint := by
    dsimp [Kint]
    positivity
  refine ⟨lam, Kint, hlam, hKint_nonneg, ?_⟩
  intro t1 ht1 t2 ht2
  have ht12 : t1 ≤ t2 := ht2.1
  have ht2T : t2 ≤ T := ht2.2
  have hcont12 : ContinuousOn Y (Set.Icc t1 t2) :=
    hfrontier.energyContinuous.mono
      (fun r hr => ⟨le_trans ht1.1 hr.1, le_trans hr.2 ht2T⟩)
  have hY_deriv_le :
      ∀ r ∈ Set.Ioo t1 t2, deriv Y r ≤ K := by
    intro r hr
    have hr0 : 0 < r := lt_of_le_of_lt ht1.1 hr.1
    have hrT : r < T := lt_of_lt_of_le hr.2 ht2T
    have hD_nonneg :
        0 ≤ delta * intervalDomainL2DiffusionDissipation u r := by
      exact mul_nonneg hdelta_pos.le
        (intervalDomainL2DiffusionDissipation_nonneg u r)
    have hS_nonneg :
        0 ≤ p.b * intervalDomain.integral
          (fun x : intervalDomain.Point => (u r x) ^ (2 + p.α)) := by
      exact mul_nonneg p.hb
        (intervalDomainL2LogisticSinkIntegral_nonneg hsol hr0 hrT)
    have halign :
        deriv Y r = 2 * deriv (fun τ => intervalDomainL2HalfEnergy u τ) r := by
      exact hfrontier.derivativeAlignment r ⟨le_of_lt hr0, hrT⟩
    have hmain := habs r hr0 hrT
    dsimp [Y] at halign
    nlinarith
  have hY_deriv_int :
      IntervalIntegrable (fun r => deriv Y r) MeasureTheory.volume t1 t2 := by
    let F : ℝ → ℝ := fun r => K * r - Y r
    have hFcont : ContinuousOn F (Set.Icc t1 t2) := by
      exact (continuousOn_const.mul continuousOn_id).sub hcont12
    have hFderiv :
        ∀ r ∈ Set.Ioo t1 t2,
          HasDerivWithinAt F (K - deriv Y r) (Set.Ioi r) r := by
      intro r hr
      have hr0 : 0 < r := lt_of_le_of_lt ht1.1 hr.1
      have hrT : r < T := lt_of_lt_of_le hr.2 ht2T
      have hYder :=
        (hfrontier.energyHasDerivWithin r ⟨le_of_lt hr0, hrT⟩).Ioi_of_Ici
      have hKder :
          HasDerivWithinAt (fun s : ℝ => K * s) K (Set.Ioi r) r :=
        ((hasDerivAt_const r K).mul (hasDerivAt_id' r)).hasDerivWithinAt.congr_deriv
          (by ring)
      exact hKder.sub hYder
    have hFprime_nonneg :
        ∀ r ∈ Set.Ioo t1 t2, 0 ≤ K - deriv Y r := by
      intro r hr
      exact sub_nonneg.mpr (hY_deriv_le r hr)
    have hFprime_on :
        MeasureTheory.IntegrableOn (fun r => K - deriv Y r) (Set.Ioc t1 t2)
          MeasureTheory.volume :=
      intervalIntegral.integrableOn_deriv_right_of_nonneg hFcont hFderiv hFprime_nonneg
    have hFprime_interval :
        IntervalIntegrable (fun r => K - deriv Y r) MeasureTheory.volume t1 t2 := by
      constructor
      · exact hFprime_on
      · have hempty : Set.Ioc t2 t1 = ∅ := Set.Ioc_eq_empty (not_lt.mpr ht12)
        rw [hempty]
        exact MeasureTheory.integrableOn_empty
    have hconst_int : IntervalIntegrable (fun _ : ℝ => K) MeasureTheory.volume t1 t2 :=
      intervalIntegral.intervalIntegrable_const
    have hsub_int := hconst_int.sub hFprime_interval
    convert hsub_int using 1
    ext r
    ring
  have hFTC :
      ∫ r in t1..t2, deriv Y r = Y t2 - Y t1 := by
    refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht12 hcont12 ?_
      hY_deriv_int
    intro r hr
    have hr0 : 0 < r := lt_of_le_of_lt ht1.1 hr.1
    have hrT : r < T := lt_of_lt_of_le hr.2 ht2T
    exact (hfrontier.energyHasDerivWithin r ⟨le_of_lt hr0, hrT⟩).Ioi_of_Ici
  have hY_int : IntervalIntegrable Y MeasureTheory.volume t1 t2 := by
    have hcontu : ContinuousOn Y (Set.uIcc t1 t2) := by
      rwa [Set.uIcc_of_le ht12]
    exact hcontu.intervalIntegrable
  have hpoint_Ioo :
      ∀ r ∈ Set.Ioo t1 t2, deriv Y r + lam * Y r ≤ Kint := by
    intro r hrIoo
    have hr0 : 0 < r := lt_of_le_of_lt ht1.1 hrIoo.1
    have hrT : r < T := lt_of_lt_of_le hrIoo.2 ht2T
    have hlog :
        Y r ≤ 1 + intervalDomain.integral
          (fun x : intervalDomain.Point => (u r x) ^ (2 + p.α)) := by
      exact intervalDomainLpAbsEnergy_two_le_one_add_logisticSink hsol hr0 hrT
    have halign :
        deriv Y r = 2 * deriv (fun τ => intervalDomainL2HalfEnergy u τ) r := by
      exact hfrontier.derivativeAlignment r ⟨le_of_lt hr0, hrT⟩
    have hmain := habs r hr0 hrT
    have hD_nonneg :
        0 ≤ delta * intervalDomainL2DiffusionDissipation u r := by
      exact mul_nonneg hdelta_pos.le
        (intervalDomainL2DiffusionDissipation_nonneg u r)
    have hS_nonneg :
        0 ≤ intervalDomain.integral
          (fun x : intervalDomain.Point => (u r x) ^ (2 + p.α)) :=
      intervalDomainL2LogisticSinkIntegral_nonneg hsol hr0 hrT
    dsimp [Y, lam, Kint] at halign hlog ⊢
    nlinarith [halign, hmain, hD_nonneg, hlog, hS_nonneg, hb]
  have hsum_int :
      IntervalIntegrable (fun r => deriv Y r + lam * Y r) MeasureTheory.volume t1 t2 :=
    hY_deriv_int.add (hY_int.const_mul lam)
  have hKint_int : IntervalIntegrable (fun _ : ℝ => Kint) MeasureTheory.volume t1 t2 :=
    intervalIntegral.intervalIntegrable_const
  have hmono :
      ∫ r in t1..t2, (deriv Y r + lam * Y r) ≤
        ∫ _r in t1..t2, Kint := by
    exact intervalIntegral.integral_mono_on_of_le_Ioo ht12 hsum_int hKint_int hpoint_Ioo
  have hsplit :
      ∫ r in t1..t2, (deriv Y r + lam * Y r) =
        (Y t2 - Y t1) + lam * ∫ r in t1..t2, Y r := by
    rw [intervalIntegral.integral_add hY_deriv_int (hY_int.const_mul lam)]
    rw [intervalIntegral.integral_const_mul, hFTC]
  rw [hsplit] at hmono
  rw [intervalIntegral.integral_const] at hmono
  simpa [Y, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hmono

/-- The closed absorbing L² differential inequality gives the uniform `p = 2`
bootstrap seed.  The proof is only scalar after the analytic frontiers have
supplied the derivative of the L² energy. -/
theorem intervalDomainL2PowerBoundedBefore_of_absorbingDifferentialInequality
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (habsorbing : IntervalDomainL2AbsorbingDifferentialInequalityResult p T u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u) :
    LpPowerBoundedBefore intervalDomain 2 T u := by
  rcases habsorbing with ⟨delta, K, hdelta_pos, hK_nonneg, habs⟩
  rcases hfrontier.initialBound with ⟨δ0, hδ0_nonneg, hinit⟩
  let d0 : ℝ := max K (deriv (fun τ => intervalDomainLpAbsEnergy 2 u τ) 0)
  have hd0_nonneg : 0 ≤ d0 := le_trans hK_nonneg (le_max_left _ _)
  refine intervalDomain_LpPowerBoundedBefore_of_abs_energy_gronwall
    (u := u) (T := T) (p := 2) (δ := δ0) (c := 0) (d := d0)
    hδ0_nonneg (by norm_num) hd0_nonneg ?_ hfrontier.energyContinuous
    hfrontier.energyHasDerivWithin hinit ?_
  · intro t ht0 htT x
    exact le_of_lt (hsol.u_pos' ht0 htT)
  · intro t ht
    by_cases ht_zero : t = 0
    · subst t
      have hle :
          deriv (fun τ => intervalDomainLpAbsEnergy 2 u τ) 0 ≤ d0 := by
        dsimp [d0]
        exact le_max_right K
          (deriv (fun τ => intervalDomainLpAbsEnergy 2 u τ) 0)
      nlinarith
    · have ht0 : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht_zero)
      have htT : t < T := ht.2
      have hdiff_nonneg :
          0 ≤ delta * intervalDomainL2DiffusionDissipation u t := by
        exact mul_nonneg hdelta_pos.le
          (intervalDomainL2DiffusionDissipation_nonneg u t)
      have hsink_nonneg :
          0 ≤ p.b * intervalDomain.integral
            (fun x : intervalDomain.Point => (u t x) ^ (2 + p.α)) := by
        exact mul_nonneg p.hb
          (intervalDomainL2LogisticSinkIntegral_nonneg hsol ht0 htT)
      have halign := hfrontier.derivativeAlignment t ht
      have hmain := habs t ht0 htT
      have hleK :
          deriv (fun τ => intervalDomainLpAbsEnergy 2 u τ) t ≤ K := by
        nlinarith
      have hKd0 : K ≤ d0 := by
        dsimp [d0]
        exact le_max_left K
          (deriv (fun τ => intervalDomainLpAbsEnergy 2 u τ) 0)
      nlinarith

/-- The first-crossing version of the L² seed.  Unlike the older differential
Gronwall consumer above, this is the sharp interface: the bound is by
`max Y(0) (K / λ)` and remains valid when the L² energy initially increases. -/
theorem intervalDomainL2PowerBoundedBefore_of_absorbingIntegratedInequality
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (habsorbing : IntervalDomainL2AbsorbingIntegratedInequalityResult p T u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u) :
    LpPowerBoundedBefore intervalDomain 2 T u := by
  rcases habsorbing with ⟨lam, K, hlam, _hK_nonneg, hineq⟩
  let C : ℝ := max (intervalDomainLpAbsEnergy 2 u 0) (K / lam)
  have hbound :
      ∀ t ∈ Set.Icc (0 : ℝ) T, intervalDomainLpAbsEnergy 2 u t ≤ C := by
    simpa [C] using
      continuous_integral_ineq_uniform_bound
        (Y := fun t => intervalDomainLpAbsEnergy 2 u t)
        (T := T) (lam := lam) (K := K)
        hlam hfrontier.energyContinuous hineq
  exact intervalDomain_LpPowerBoundedBefore_of_abs_energy_bound
    (u := u) (T := T) (p := 2) (C := C)
    (fun t ht0 htT x => le_of_lt (hsol.u_pos' ht0 htT))
    (fun t ht0 htT => hbound t ⟨le_of_lt ht0, le_of_lt htT⟩)

/-- The elementary first step in the classical one-dimensional slice estimate:
on the unit interval, a nonnegative slice satisfies
`∫ u^p ≤ ||u||_∞^(p-1) ∫ u`.

The theorem is deliberately stated for one concrete interval-domain slice with
explicit boundedness and integrability hypotheses.  It is not the false
domain-abstract interpolation predicate from `IntervalDomainLemma41`. -/
theorem integral_pow_le_sup_pow_mul
    {pExp : ℝ} (hpExp : 1 ≤ pExp)
    {f : intervalDomain.Point → ℝ}
    (hf_nonneg : ∀ x : intervalDomain.Point, 0 ≤ f x)
    (hf_bdd : BddAbove (Set.range fun x : intervalDomain.Point => |f x|))
    (hf_int : IntervalIntegrable (intervalDomainLift f) MeasureTheory.volume 0 1)
    (hfp_int :
      IntervalIntegrable
        (fun y : ℝ => intervalDomainLift (fun x : intervalDomain.Point => (f x) ^ pExp) y)
        MeasureTheory.volume 0 1) :
    intervalDomain.integral (fun x : intervalDomain.Point => (f x) ^ pExp) ≤
      (intervalDomainSupNorm f) ^ (pExp - 1) * intervalDomain.integral f := by
  have hpow_nonneg : 0 ≤ pExp - 1 := by linarith
  have hsup_nonneg : 0 ≤ intervalDomainSupNorm f :=
    intervalDomainSupNorm_nonneg f
  have hpoint :
      ∀ y ∈ Set.Icc (0 : ℝ) 1,
        intervalDomainLift (fun x : intervalDomain.Point => (f x) ^ pExp) y ≤
          (intervalDomainSupNorm f) ^ (pExp - 1) * intervalDomainLift f y := by
    intro y hy
    let x : intervalDomain.Point := ⟨y, hy⟩
    have hf_y_nonneg : 0 ≤ f x := hf_nonneg x
    have hsup_y_abs : |f x| ≤ intervalDomainSupNorm f := by
      unfold intervalDomainSupNorm
      exact le_csSup hf_bdd (Set.mem_range_self x)
    have hsup_y : f x ≤ intervalDomainSupNorm f := by
      exact le_trans (le_abs_self (f x)) hsup_y_abs
    have hpow_le :
        (f x) ^ (pExp - 1) ≤ (intervalDomainSupNorm f) ^ (pExp - 1) :=
      Real.rpow_le_rpow hf_y_nonneg hsup_y hpow_nonneg
    have hmul_le :
        (f x) ^ (pExp - 1) * f x ≤
          (intervalDomainSupNorm f) ^ (pExp - 1) * f x :=
      mul_le_mul_of_nonneg_right hpow_le hf_y_nonneg
    have hpow_split : (f x) ^ pExp = (f x) ^ (pExp - 1) * f x := by
      rcases eq_or_lt_of_le hf_y_nonneg with hzero | hpos
      · have hp_pos : 0 < pExp := lt_of_lt_of_le zero_lt_one hpExp
        rw [← hzero]
        simp [Real.zero_rpow, hp_pos.ne']
      · have hp_split : pExp = pExp - 1 + 1 := by ring
        rw [hp_split, Real.rpow_add hpos, Real.rpow_one]
        ring_nf
    simpa [intervalDomainLift, hy, x, hpow_split] using hmul_le
  have hconst_int :
      IntervalIntegrable
        (fun y : ℝ => (intervalDomainSupNorm f) ^ (pExp - 1) *
          intervalDomainLift f y)
        MeasureTheory.volume 0 1 :=
    hf_int.const_mul ((intervalDomainSupNorm f) ^ (pExp - 1))
  unfold intervalDomain intervalDomainIntegral
  calc
    ∫ y in (0 : ℝ)..1,
        intervalDomainLift (fun x : intervalDomain.Point => (f x) ^ pExp) y
        ≤ ∫ y in (0 : ℝ)..1,
            (intervalDomainSupNorm f) ^ (pExp - 1) * intervalDomainLift f y :=
          intervalIntegral.integral_mono_on (by norm_num) hfp_int hconst_int hpoint
    _ = (intervalDomainSupNorm f) ^ (pExp - 1) *
          ∫ y in (0 : ℝ)..1, intervalDomainLift f y := by
          rw [intervalIntegral.integral_const_mul]

/-- A proved classical-slice interpolation entry point on the concrete interval.

This packages exactly the part of the `L^p` route that is currently discharged
from proved facts: the elementary `∫u^p <= ||u||∞^(p-1)∫u` estimate for a
nonnegative slice, together with the pointwise Agmon inequality for the same
slice.  The theorem is intentionally slice-level and uses
`agmon_inequality_interval`; it does not assert the false arbitrary-function
`IntervalDomainInterpolation` predicate. -/
theorem intervalDomain_Lp_interpolation_classicalSlice
    {pExp : ℝ} (hpExp : 1 ≤ pExp)
    {f : intervalDomain.Point → ℝ}
    (hf_nonneg : ∀ x : intervalDomain.Point, 0 ≤ f x)
    (hf_bdd : BddAbove (Set.range fun x : intervalDomain.Point => |f x|))
    (hf_int : IntervalIntegrable (intervalDomainLift f) MeasureTheory.volume 0 1)
    (hfp_int :
      IntervalIntegrable
        (fun y : ℝ => intervalDomainLift (fun x : intervalDomain.Point => (f x) ^ pExp) y)
        MeasureTheory.volume 0 1)
    (hf_cont : ContinuousOn (intervalDomainLift f) (Set.Icc (0 : ℝ) 1))
    {f' : ℝ → ℝ}
    (hf_deriv : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (intervalDomainLift f) (f' x) x)
    (hf'_int : IntervalIntegrable f' MeasureTheory.volume 0 1)
    (hf_sq_int : IntervalIntegrable (fun y : ℝ => (intervalDomainLift f y) ^ 2)
      MeasureTheory.volume 0 1)
    (hf'_sq_int : IntervalIntegrable (fun y : ℝ => f' y ^ 2) MeasureTheory.volume 0 1)
    (hff'_int : IntervalIntegrable (fun y : ℝ => intervalDomainLift f y * f' y)
      MeasureTheory.volume 0 1) :
    intervalDomain.integral (fun x : intervalDomain.Point => (f x) ^ pExp) ≤
        (intervalDomainSupNorm f) ^ (pExp - 1) * intervalDomain.integral f ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        (intervalDomainLift f x) ^ 2 ≤
          (2 / (1 : ℝ)) *
              (∫ y in (0 : ℝ)..1, (intervalDomainLift f y) ^ 2) +
            2 * Real.sqrt
                (∫ y in (0 : ℝ)..1, (intervalDomainLift f y) ^ 2) *
              Real.sqrt (∫ y in (0 : ℝ)..1, f' y ^ 2) := by
  constructor
  · exact integral_pow_le_sup_pow_mul hpExp hf_nonneg hf_bdd hf_int hfp_int
  · intro x hx
    exact ShenWork.GagliardoNirenberg.agmon_inequality_interval
      (L := 1) (hL := by norm_num) hf_cont hf_deriv hf'_int
      hf_sq_int hf'_sq_int hff'_int hx

/-- Uniform-in-time version of the half-energy inequality.  This is the shape
needed by a closed absorbing estimate with one constant `K`; the existing route
predicate below is weaker because its `Ceps` is chosen after `t`. -/
def IntervalDomainL2HalfEnergyDifferentialInequalityUniformCeps
    (p : CM2Params) (T : ℝ) (u _v : ℝ → intervalDomain.Point → ℝ) : Prop :=
  ∀ eps, 0 < eps →
    ∃ Ceps, ∀ t, 0 < t → t < T →
      deriv (fun τ => intervalDomainL2HalfEnergy u τ) t +
          intervalDomainL2DiffusionDissipation u t ≤
        |p.χ₀| *
            (eps * intervalDomainLpWeightedGradientDissipation 2 u t +
              Ceps *
                intervalDomain.integral (fun x => (u t x) ^ (2 + 2 * p.γ))) +
          intervalDomainL2LogisticIntegral p u t

/-- Absorbing differential inequality produced from the already proved
half-energy inequality once the purely spatial absorption estimate is supplied.

This is deliberately a theorem, not a carried field or a posited definition:
the proof term is just the algebraic absorption of the half-energy inequality. -/
theorem IntervalDomainL2AbsorbingDifferentialInequality
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (_hthreshold : IntervalDomainSharpL2AbsorptionThreshold p)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hmass : IntervalDomainLogisticMassBound p T u)
    (hspatial : IntervalDomainL2SpatialAbsorptionEstimate p T u v hsol hmass)
    (henergy : IntervalDomainL2HalfEnergyDifferentialInequalityUniformCeps p T u v) :
    IntervalDomainL2AbsorbingDifferentialInequalityResult p T u := by
  -- The spatial estimate is applied to the same constant produced by the
  -- uniform half-energy inequality.
  let eps0 : ℝ := 1 / (2 * (|p.χ₀| + 1))
  have heps0 : 0 < eps0 := by
    dsimp [eps0]
    positivity
  obtain ⟨Ceps, hhalf⟩ := henergy eps0 heps0
  obtain ⟨delta, K, hdelta_pos, hdelta_le_two, hK_nonneg, hspatialK⟩ :=
    hspatial Ceps
  refine ⟨delta, K, hdelta_pos, hK_nonneg, ?_⟩
  intro t ht0 htT
  have hhalf_t :
      deriv (fun τ => intervalDomainL2HalfEnergy u τ) t +
          intervalDomainL2DiffusionDissipation u t ≤
        |p.χ₀| *
            (eps0 * intervalDomainLpWeightedGradientDissipation 2 u t +
              Ceps *
                intervalDomain.integral (fun x => (u t x) ^ (2 + 2 * p.γ))) +
          intervalDomainL2LogisticIntegral p u t := by
    exact hhalf t ht0 htT
  have htwice :
      2 * deriv (fun τ => intervalDomainL2HalfEnergy u τ) t +
          2 * intervalDomainL2DiffusionDissipation u t ≤
        2 * (|p.χ₀| *
            (eps0 * intervalDomainLpWeightedGradientDissipation 2 u t +
              Ceps *
                intervalDomain.integral (fun x => (u t x) ^ (2 + 2 * p.γ))) +
          intervalDomainL2LogisticIntegral p u t) := by
    nlinarith
  have hsp := hspatialK t ht0 htT
  nlinarith

/-- The unconditional L² half-energy differential inequality already proved
from a classical interval-domain solution, with the cross-diffusion bootstrap
discharged by the elliptic resolver equation. -/
def IntervalDomainL2HalfEnergyDifferentialInequality
    (p : CM2Params) (T : ℝ) (u _v : ℝ → intervalDomain.Point → ℝ) : Prop :=
  ∀ eps, 0 < eps → ∀ t, 0 < t → t < T →
    ∃ Ceps,
      deriv (fun τ => intervalDomainL2HalfEnergy u τ) t +
          intervalDomainL2DiffusionDissipation u t ≤
        |p.χ₀| *
            (eps * intervalDomainLpWeightedGradientDissipation 2 u t +
              Ceps *
                intervalDomain.integral (fun x => (u t x) ^ (2 + 2 * p.γ))) +
          intervalDomainL2LogisticIntegral p u t

/-- The corrected finite-horizon route:

`mass comparison -> elliptic drift bound -> L² half-energy inequality ->
Lp bootstrap -> endpoint boundedness`.

The mass, Lp-bound, and endpoint-boundedness legs are produced below from the
repository's named Paper 2 interfaces (`Proposition_2_4`, `Corollary_2_1`,
`Proposition_2_5`).  The L² half-energy inequality is now wired below from the
proved Paper 2 theorem.  The remaining bootstrap seed is intentionally the
logistic-absorption leg: it must turn that half-energy inequality into the
starting `Lp` control under the correct `(α,γ)` threshold.
-/
structure IntervalDomainMassLpSmoothingRouteData (p : CM2Params) where
  a_pos : 0 < p.a
  b_pos : 0 < p.b
  chi_nonneg : 0 ≤ p.χ₀
  massComparison : Proposition_2_4 intervalDomain p
  driftBoundFromMass :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainLogisticMassBound p T u →
          IntervalDomainChemotacticDriftBound p T v
  l2EnergyInequality :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainLogisticMassBound p T u →
          IntervalDomainChemotacticDriftBound p T v →
            IntervalDomainL2HalfEnergyDifferentialInequality p T u v
  l2BootstrapSeed :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainL2HalfEnergyDifferentialInequality p T u v →
          ∃ rho > 0,
            CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
              ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
                LpPowerBoundedBefore intervalDomain p0 T u
  allLpBoundFromBootstrap : Corollary_2_1 intervalDomain p
  endpointBoundFromLp : Proposition_2_5 intervalDomain p

/-- The logistic mass route fact follows from the named Paper 2 mass theorem.
The witness is enlarged by `max 0` so the route predicate's nonnegative
constant requirement is automatic. -/
theorem intervalDomainLogisticMassBound_of_logisticMassUpperBoundBefore
    {p : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ} {u : ℝ → intervalDomain.Point → ℝ}
    (h : LogisticMassUpperBoundBefore intervalDomain p T u₀ u) :
    IntervalDomainLogisticMassBound p T u := by
  let M :=
    max (intervalDomain.integral u₀)
      (((p.a / p.b) ^ (1 / p.α)) * intervalDomain.volume)
  refine ⟨max 0 M, le_max_left 0 M, ?_⟩
  intro t ht0 htT
  exact le_trans (h t ht0 htT) (le_max_right 0 M)

/-- `Proposition_2_4` supplies the mass route fact in the positive-logistic
parameter regime. -/
theorem intervalDomainLogisticMassBound_of_proposition24
    {p : CM2Params}
    (h24 : Proposition_2_4 intervalDomain p)
    (ha : 0 < p.a) (hb : 0 < p.b)
    {u₀ : intervalDomain.Point → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {T : ℝ} (hT : 0 < T)
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (htrace : InitialTrace intervalDomain u₀ u) :
    IntervalDomainLogisticMassBound p T u := by
  have hlog :
      LogisticMassUpperBoundBefore intervalDomain p T u₀ u :=
    ((h24 u₀ hu₀ T hT u v hsol htrace).2) ha hb
  exact intervalDomainLogisticMassBound_of_logisticMassUpperBoundBefore hlog

/-- `Corollary_2_1` turns the bootstrap seed produced from the L² differential
inequality into the route's L² power bound. -/
theorem intervalDomainL2PowerBoundedBefore_of_corollary21
    {p : CM2Params}
    (hCor21 : Corollary_2_1 intervalDomain p)
    (hbootstrap :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
          IntervalDomainL2HalfEnergyDifferentialInequality p T u v →
            ∃ rho > 0,
              CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
                ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
                  LpPowerBoundedBefore intervalDomain p0 T u)
    {u₀ : intervalDomain.Point → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {T : ℝ} (hT : 0 < T)
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (henergy : IntervalDomainL2HalfEnergyDifferentialInequality p T u v) :
    LpPowerBoundedBefore intervalDomain 2 T u := by
  exact hCor21 T hT u v hsol
    (hbootstrap u₀ hu₀ T hT u v hsol htrace henergy)
    2 (by norm_num)

/-- Once the L² power bound itself is available, the repository's committed
cross-diffusion bootstrap estimate supplies the rest of the `l2BootstrapSeed`
payload with `rho = 2γ` and `p0 = 2`.

This isolates the remaining analytic obligation: proving
`LpPowerBoundedBefore intervalDomain 2 T u` from the absorbing L² inequality. -/
theorem intervalDomainL2BootstrapSeed_of_L2PowerBoundedBefore
    {p : CM2Params}
    (hbounded : IntervalDomainBoundednessHyp p)
    {u₀ : intervalDomain.Point → ℝ}
    (_hu₀ : PositiveInitialDatum intervalDomain u₀)
    {T : ℝ} (_hT : 0 < T)
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (_htrace : InitialTrace intervalDomain u₀ u)
    (_henergy : IntervalDomainL2HalfEnergyDifferentialInequality p T u v)
    (hL2 : LpPowerBoundedBefore intervalDomain 2 T u) :
    ∃ rho > 0,
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
        ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
          LpPowerBoundedBefore intervalDomain p0 T u := by
  refine ⟨2 * p.γ, ?_, ?_, 2, ?_, hL2⟩
  · nlinarith [hbounded.2.2.2.1]
  · exact intervalDomain_crossDiffusionBootstrapEstimate_of_classical hsol
  · have hrewrite :
        (2 * p.γ) * (p.N : ℝ) / 2 = p.γ * (p.N : ℝ) := by
      ring
    rw [hrewrite]
    exact max_lt (by norm_num) hbounded.2.2.2.2

/-- The carried route atom `l2EnergyInequality` is discharged by the already
proved unconditional interval-domain L² half-energy estimate. -/
theorem intervalDomainL2HalfEnergyDifferentialInequality_of_classicalSolution
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v) :
    IntervalDomainL2HalfEnergyDifferentialInequality p T u v := by
  intro eps heps t ht0 htT
  exact intervalDomain_l2_half_energy_inequality_unconditional_crossDiffusion
    (params := p) (T := T) (eps := eps) (t := t) (u := u) (v := v)
    heps ht0 htT hsol

/-- The same half-energy estimate with the cross-diffusion constant chosen
once for all interior times. -/
theorem intervalDomainL2HalfEnergyDifferentialInequalityUniformCeps_of_classicalSolution
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v) :
    IntervalDomainL2HalfEnergyDifferentialInequalityUniformCeps p T u v := by
  intro eps heps
  exact intervalDomain_l2_half_energy_inequality_unconditional_crossDiffusion_uniformCeps
    (params := p) (T := T) (eps := eps) (u := u) (v := v)
    heps hsol

/-- Data for the part of the mass/Lp/smoothing route that still has to be
supplied after the unconditional L² half-energy atom has been discharged. -/
structure IntervalDomainMassLpSmoothingSeedData (p : CM2Params) where
  a_pos : 0 < p.a
  b_pos : 0 < p.b
  chi_nonneg : 0 ≤ p.χ₀
  boundednessHyp : IntervalDomainBoundednessHyp p
  massComparison : Proposition_2_4 intervalDomain p
  driftBoundFromMass :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainLogisticMassBound p T u →
          IntervalDomainChemotacticDriftBound p T v
  l2SeedRegularity :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainL2SeedRegularityFrontier T u
  allLpBoundFromBootstrap : Corollary_2_1 intervalDomain p
  endpointBoundFromLp : Proposition_2_5 intervalDomain p

/-- The genuinely carried residuals for the interval-domain mass/Lp/smoothing
route.

The interval mass comparison is not a residual: it is supplied by the proved
Paper 2 interval theorem `intervalDomain_Proposition_2_4`.  Likewise `b_pos`
is already part of `IntervalDomainBoundednessHyp`. -/
structure IntervalDomainMassLpSmoothingRouteResiduals (p : CM2Params) where
  a_pos : 0 < p.a
  chi_nonneg : 0 ≤ p.χ₀
  boundednessHyp : IntervalDomainBoundednessHyp p
  driftBoundFromMass :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainLogisticMassBound p T u →
          IntervalDomainChemotacticDriftBound p T v
  l2SeedRegularity :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainL2SeedRegularityFrontier T u
  allLpBoundFromBootstrap : Corollary_2_1 intervalDomain p
  endpointBoundFromLp : Proposition_2_5 intervalDomain p

/-- Build the full seed package from the remaining route residuals.

This is the first non-orphaned construction point: the mass comparison field is
filled by the proved interval-domain Paper 2 mass theorem, and `b_pos` is
recovered from the sharp boundedness hypothesis. -/
def IntervalDomainMassLpSmoothingRouteResiduals.to_seedData
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingRouteResiduals p) :
    IntervalDomainMassLpSmoothingSeedData p where
  a_pos := h.a_pos
  b_pos := h.boundednessHyp.2.1
  chi_nonneg := h.chi_nonneg
  boundednessHyp := h.boundednessHyp
  massComparison := ShenWork.Paper2.intervalDomain_Proposition_2_4 p
  driftBoundFromMass := h.driftBoundFromMass
  l2SeedRegularity := h.l2SeedRegularity
  allLpBoundFromBootstrap := h.allLpBoundFromBootstrap
  endpointBoundFromLp := h.endpointBoundFromLp

/-- Construct the full route package after the L² half-energy atom has been
discharged.  The bootstrap seed is constructed from the L² power bound and the
committed cross-diffusion estimate; it is not a route-data field forward. -/
def IntervalDomainMassLpSmoothingSeedData.to_routeData
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingSeedData p) :
    IntervalDomainMassLpSmoothingRouteData p where
  a_pos := h.a_pos
  b_pos := h.b_pos
  chi_nonneg := h.chi_nonneg
  massComparison := h.massComparison
  driftBoundFromMass := h.driftBoundFromMass
  l2EnergyInequality := by
    intro _u₀ _hu₀ _T _hT _u _v hsol _htrace _hmass _hdrift
    exact intervalDomainL2HalfEnergyDifferentialInequality_of_classicalSolution hsol
  l2BootstrapSeed := by
    intro u₀ hu₀ T hT u v hsol htrace henergy
    have hmass :
        IntervalDomainLogisticMassBound p T u :=
      intervalDomainLogisticMassBound_of_proposition24
        h.massComparison h.a_pos h.b_pos hu₀ hT hsol htrace
    have hspatial :
        IntervalDomainL2SpatialAbsorptionEstimate p T u v hsol hmass :=
      intervalDomainL2SpatialAbsorptionEstimate_of_classical
        h.boundednessHyp hsol hmass
    have huniform :
        IntervalDomainL2HalfEnergyDifferentialInequalityUniformCeps p T u v :=
      intervalDomainL2HalfEnergyDifferentialInequalityUniformCeps_of_classicalSolution hsol
    have habsorbing :
        IntervalDomainL2AbsorbingDifferentialInequalityResult p T u :=
      IntervalDomainL2AbsorbingDifferentialInequality
        h.boundednessHyp.1 hsol hmass hspatial huniform
    have hregularity : IntervalDomainL2SeedRegularityFrontier T u :=
      h.l2SeedRegularity u₀ hu₀ T hT u v hsol htrace
    have hintegrated :
        IntervalDomainL2AbsorbingIntegratedInequalityResult p T u :=
      IntervalDomainL2AbsorbingIntegratedInequality
        h.b_pos hsol habsorbing hregularity
    have hL2 :
        LpPowerBoundedBefore intervalDomain 2 T u :=
      intervalDomainL2PowerBoundedBefore_of_absorbingIntegratedInequality
        hsol hintegrated hregularity
    exact intervalDomainL2BootstrapSeed_of_L2PowerBoundedBefore
      h.boundednessHyp hu₀ hT hsol htrace henergy
      hL2
  allLpBoundFromBootstrap := h.allLpBoundFromBootstrap
  endpointBoundFromLp := h.endpointBoundFromLp

/-- `Proposition_2_5` consumes a sufficiently high finite-Lp bound.  The high
exponent is chosen automatically as one above the proposition's threshold and
is supplied by `Corollary_2_1`. -/
theorem intervalDomainBoundedBefore_of_corollary21_and_proposition25
    {p : CM2Params}
    (hCor21 : Corollary_2_1 intervalDomain p)
    (hProp25 : Proposition_2_5 intervalDomain p)
    {u₀ : intervalDomain.Point → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {T : ℝ} (hT : 0 < T)
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hbootstrap :
      ∃ rho > 0,
        CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
          ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
            LpPowerBoundedBefore intervalDomain p0 T u) :
    IsPaper2BoundedBefore intervalDomain T u := by
  let threshold : ℝ :=
    max (p.N : ℝ) (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ)))
  let q : ℝ := threshold + 1
  have hNreal : (1 : ℝ) ≤ (p.N : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt p.hN)
  have hthreshold_ge_one : (1 : ℝ) ≤ threshold := by
    exact le_trans hNreal (le_max_left _ _)
  have hq_gt_threshold : threshold < q := by
    dsimp [q]
    linarith
  have hq_gt_one : (1 : ℝ) < q := by
    dsimp [q]
    linarith
  have hqLp : LpPowerBoundedBefore intervalDomain q T u :=
    hCor21 T hT u v hsol hbootstrap q hq_gt_one
  exact hProp25 u₀ hu₀ T hT u v hsol htrace q
    (by simpa [threshold] using hq_gt_threshold) hqLp

/-- A classical interval-domain solution has bounded spatial slices on every
interior time, from closed-interval spatial continuity. -/
theorem intervalDomain_solution_slice_abs_bddAbove
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    BddAbove (Set.range (fun x : intervalDomain.Point => |u t x|)) := by
  classical
  have hcont : ContinuousOn (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
    ((hsol.regularity.2.2.2.2.1 t ht).1.1).continuousOn
  have hcompact : IsCompact (Set.Icc (0 : ℝ) 1) := isCompact_Icc
  obtain ⟨M, hM⟩ := (hcompact.image_of_continuousOn (hcont.abs)).bddAbove
  refine ⟨M, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hMx := hM ⟨x.1, x.2, rfl⟩
  have hlift : intervalDomainLift (u t) x.1 = u t x := by
    simp [intervalDomainLift]
  simpa [hlift] using hMx

/-- For classical interval-domain solutions, the concrete `supNorm` controls
point values before the finite horizon. -/
theorem supNormControlsPointwiseBefore_of_classicalSolution
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v) :
    SupNormControlsPointwiseBefore T u :=
  supNormControlsPointwiseBefore_of_bddAbove_abs
    (fun t ht0 htT =>
      intervalDomain_solution_slice_abs_bddAbove hsol
        (show t ∈ Set.Ioo (0 : ℝ) T from ⟨ht0, htT⟩))

/-- Compose the corrected mass/Lp/heat-smoothing route into the a-priori bound
consumed by the continuation handoff. -/
theorem IntervalDomainMassLpSmoothingAprioriBound.of_l2RouteData
    {p : CM2Params}
    (hroute : IntervalDomainMassLpSmoothingRouteData p) :
    IntervalDomainMassLpSmoothingAprioriBound p := by
  refine
    { a_pos := hroute.a_pos
      b_pos := hroute.b_pos
      chi_nonneg := hroute.chi_nonneg
      pointwiseBound := ?_ }
  intro u₀ hu₀ T hT u v hsol htrace
  have hmass :
      IntervalDomainLogisticMassBound p T u :=
    intervalDomainLogisticMassBound_of_proposition24
      hroute.massComparison hroute.a_pos hroute.b_pos hu₀ hT hsol htrace
  have hdrift :
      IntervalDomainChemotacticDriftBound p T v :=
    hroute.driftBoundFromMass u₀ hu₀ T hT u v hsol htrace hmass
  have henergy :
      IntervalDomainL2HalfEnergyDifferentialInequality p T u v :=
    hroute.l2EnergyInequality u₀ hu₀ T hT u v hsol htrace hmass hdrift
  have hbootstrap :
      ∃ rho > 0,
        CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
          ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
            LpPowerBoundedBefore intervalDomain p0 T u :=
    hroute.l2BootstrapSeed u₀ hu₀ T hT u v hsol htrace henergy
  have hl2 :
      LpPowerBoundedBefore intervalDomain 2 T u :=
    hroute.allLpBoundFromBootstrap T hT u v hsol hbootstrap
      2 (by norm_num)
  have hbounded :
      IsPaper2BoundedBefore intervalDomain T u :=
    intervalDomainBoundedBefore_of_corollary21_and_proposition25
      hroute.allLpBoundFromBootstrap hroute.endpointBoundFromLp
      hu₀ hT hsol htrace hbootstrap
  exact pointwiseBoundedBefore_of_boundedBefore_and_supNormControls hbounded
    (supNormControlsPointwiseBefore_of_classicalSolution hsol)

/-- Compose residual route inputs all the way to the a-priori bound consumed by
the continuation handoff. -/
def IntervalDomainMassLpSmoothingRouteResiduals.aprioriBound
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingRouteResiduals p) :
    IntervalDomainMassLpSmoothingAprioriBound p :=
  IntervalDomainMassLpSmoothingAprioriBound.of_l2RouteData
    h.to_seedData.to_routeData

/-- The a-priori `L∞` output gives the exact pointwise boundedness predicate
needed to exclude the `m ≥ 1` blow-up alternative. -/
theorem pointwiseBoundedBefore_of_massLpSmoothingAprioriBound
    {p : CM2Params} (hbound : IntervalDomainMassLpSmoothingAprioriBound p)
    {u₀ : intervalDomain.Point → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {T : ℝ} (hT : 0 < T)
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (htrace : InitialTrace intervalDomain u₀ u) :
    PointwiseBoundedBefore T u := by
  rcases hbound.pointwiseBound u₀ hu₀ T hT u v hsol htrace with ⟨B, hB⟩
  exact ⟨B, hB⟩

/-- Uniform a-priori pointwise control rules out the finite continuation branch
in the `1 ≤ m` regime. -/
theorem not_finiteContinuationAlternativeBranch_of_massLpSmoothingAprioriBound
    {p : CM2Params} (hbound : IntervalDomainMassLpSmoothingAprioriBound p)
    {u₀ : intervalDomain.Point → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hm : 1 ≤ p.m) :
    ¬ FiniteContinuationAlternativeBranch p u₀ := by
  intro hfinite
  rcases hfinite with ⟨T, hT, u, v, hsol, htrace, _halt, hmge⟩
  exact not_mgeOneFiniteHorizonAlternative_of_pointwiseBoundedBefore
    (pointwiseBoundedBefore_of_massLpSmoothingAprioriBound
      hbound hu₀ hT hsol htrace)
    (hmge hm)

/-- Standard continuation plus the mass/Lp/smoothing a-priori bound gives the
corrected existential global-solution package. -/
theorem intervalDomainGlobalSolutionExists_of_standardContinuation_gluing_and_massLpSmoothing
    (p : CM2Params)
    (hcont : IntervalDomainStandardContinuationGluingData p)
    (hbound : IntervalDomainMassLpSmoothingAprioriBound p) :
    IntervalDomainGlobalSolutionExists p := by
  refine intervalDomainGlobalSolutionExists_of_standardContinuation_and_gluing
    p hcont.localExistence hcont.boundedInitial
    hcont.standardContinuation ?_ hcont.gluing
  intro u₀ hu₀ hm
  exact not_finiteContinuationAlternativeBranch_of_massLpSmoothingAprioriBound
    hbound hu₀ hm

/-- Finite-sup continuation plus the mass/Lp/smoothing a-priori bound gives the
corrected existential global-solution package. -/
theorem intervalDomainGlobalSolutionExists_of_finiteSupContinuation_gluing_and_massLpSmoothing
    (p : CM2Params)
    (hcont : IntervalDomainFiniteSupContinuationGluingData p)
    (hbound : IntervalDomainMassLpSmoothingAprioriBound p) :
    IntervalDomainGlobalSolutionExists p :=
  intervalDomainGlobalSolutionExists_of_standardContinuation_gluing_and_massLpSmoothing
    p hcont.to_standard hbound

end ShenWork.IntervalDomainExistence

end
