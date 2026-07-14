import ShenWork.Paper1.Theorem12Corrected

open Filter Topology MeasureTheory

noncomputable section

namespace ShenWork.Paper1

/-!
# Faithful solution-class correction for Paper 1 Theorem 1.3

The paper applies its stability theorem to the Cauchy solution whose initial
datum is the second wave.  That argument implicitly uses two facts which the
old Lean headline did not record:

* a traveling wave is a classical (in particular differentiable) profile;
* the whole-line Cauchy problem is considered in the bounded solution class.

Without the second restriction, whole-line parabolic uniqueness is not a
valid general principle.  The definitions below expose the bounded class and
state stability universally in that class.  This lets the translated second
wave be used directly, so Theorem 1.3 does not need a separate unrestricted
Cauchy-uniqueness assumption.
-/

/-- A global Cauchy solution in the bounded class used by the paper. -/
def IsBoundedGlobalCauchySolutionFrom
    (p : CMParams) (u₀ : ℝ → ℝ)
    (u v : ℝ → ℝ → ℝ) : Prop :=
  IsGlobalCauchySolutionFrom p u₀ u v ∧
    IsBoundedGlobal u ∧ IsBoundedGlobal v

/-- Differentiability is enough to turn a traveling-wave profile into the
corresponding global classical Cauchy solution.  The earlier helper asked for
`C²`, although its proof and `IsGlobalClassicalSolution` only consume the
first derivatives here. -/
theorem IsTravelingWave.to_globalCauchySolutionFrom_of_differentiable
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hU_diff : Differentiable ℝ U) (hV_diff : Differentiable ℝ V) :
    IsGlobalCauchySolutionFrom p U
      (fun t x => U (x - c * t)) (fun t x => V (x - c * t)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact
      _root_.IsTravelingWave.to_movingFrame_global_classical_solution_of_differentiable
        p hTW hU_diff hV_diff
  · intro x
    simp
  · exact HasUniformInitialTrace.movingWave
      (travelingWave_U_uniformContinuous hTW hU_diff.continuous) c
  · intro t x _ht
    exact hTW.U_pos (x - c * t)

/-- A regular traveling wave, translated at its wave speed, belongs to the
bounded global Cauchy class. -/
theorem IsTravelingWave.movingWave_isBoundedGlobalCauchySolutionFrom
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hbound : HasStrictWaveUpperTailBound p c U) :
    IsBoundedGlobalCauchySolutionFrom p U
      (fun t x => U (x - c * t)) (fun t x => V (x - c * t)) := by
  refine ⟨IsTravelingWave.to_globalCauchySolutionFrom_of_differentiable
      hTW hreg.U_diff hreg.V_diff, ?_, ?_⟩
  · refine ⟨MChi p, ?_⟩
    intro t x _ht
    rw [abs_of_pos (hTW.U_pos (x - c * t))]
    exact hbound.hasWaveUpperTailBound.le_MChi (x - c * t)
  · refine ⟨(MChi p) ^ p.γ, ?_⟩
    intro t x _ht
    exact (hreg.V_bound (x - c * t)).1

/-- Corrected stability target: existence in, and convergence of every member
of, the bounded whole-line Cauchy solution class.  The weighted norm is the
co-moving norm actually used in Section 5, and wave regularity is explicit. -/
def Theorem_1_2_amended_bounded : Prop :=
  ∀ p : CMParams, StableWaveParameterRegime p →
    ∃ cStarStar : ℝ → ℝ,
      StabilitySpeedThresholdFamilyAsymptotic p cStarStar ∧
      stabilitySpeedBaseline p ≤ cStarStar p.χ ∧
      ∀ c : ℝ, cStarStar p.χ < c →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        TravelingWaveRegularity p c U V →
        HasStrictWaveUpperTailBound p c U →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧
          HasWaveRightTailAsymptotic c κ₁ U) →
        ∀ η : ℝ, kappa c < η →
          η < 1 / (1 + |p.χ| ^ (1 / 6 : ℝ)) →
          ∀ u₀ : ℝ → ℝ,
            NonnegativeInitialDatum u₀ →
            StrictlyPositiveAtLeft u₀ →
            WeightedL2InitialCloseness η u₀ U →
            (∃ u v : ℝ → ℝ → ℝ,
              IsBoundedGlobalCauchySolutionFrom p u₀ u v) ∧
            ∀ u v : ℝ → ℝ → ℝ,
              IsBoundedGlobalCauchySolutionFrom p u₀ u v →
                CoMovingWeightedL2Convergence η c u U ∧
                UniformMovingFrameConvergence c u U

/-- Paper 1 Theorem 1.3 with the classical-wave regularity that the phrase
“traveling wave solution” carries in the paper made explicit. -/
def Theorem_1_3_amended : Prop :=
  ∀ p : CMParams, StableWaveParameterRegime p →
    ∃ cStarStar : ℝ → ℝ,
      StabilitySpeedThresholdFamilyAsymptotic p cStarStar ∧
      stabilitySpeedBaseline p ≤ cStarStar p.χ ∧
      ∀ c : ℝ, cStarStar p.χ < c →
      ∀ U₁ V₁ U₂ V₂ : ℝ → ℝ,
        IsTravelingWave p c U₁ V₁ →
        TravelingWaveRegularity p c U₁ V₁ →
        IsTravelingWave p c U₂ V₂ →
        TravelingWaveRegularity p c U₂ V₂ →
        HasStrictWaveUpperTailBound p c U₁ →
        HasStrictWaveUpperTailBound p c U₂ →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧
          HasWaveRightTailAsymptotic c κ₁ U₁ ∧
          HasWaveRightTailAsymptotic c κ₁ U₂) →
        (∀ x, U₁ x = U₂ x) ∧ (∀ x, V₁ x = V₂ x)

/-- The corrected bounded-class stability theorem implies the corrected
uniqueness theorem.  The proof applies stability directly to the translated
second wave, whose membership in the bounded Cauchy class was proved above;
there is no unrestricted whole-line uniqueness hypothesis. -/
theorem Theorem_1_3_amended.of_bounded_stability
    (h12 : Theorem_1_2_amended_bounded) :
    Theorem_1_3_amended := by
  intro p hregime
  rcases h12 p hregime with ⟨cStarStar, hasymp, hbaseline, hstability⟩
  refine ⟨cStarStar, hasymp, hbaseline, ?_⟩
  intro c hc U₁ V₁ U₂ V₂ hTW₁ hreg₁ hTW₂ hreg₂ hstrict₁ hstrict₂ htailPair
  rcases htailPair with ⟨κ₁, hκ_gt, hκ_lt_one, htail₁, htail₂⟩
  have hcap : kappa c < 1 / (1 + |p.χ| ^ (1 / 6 : ℝ)) :=
    kappa_lt_stability_weight_cap_of_stabilitySpeedBaseline_lt
      hbaseline hc
  rcases exists_between (lt_min hκ_gt hcap) with ⟨η, hκη, hηmin⟩
  have hηκ₁ : η < κ₁ := lt_of_lt_of_le hηmin (min_le_left _ _)
  have hηcap : η < 1 / (1 + |p.χ| ^ (1 / 6 : ℝ)) :=
    lt_of_lt_of_le hηmin (min_le_right _ _)
  have hηpos : 0 < η :=
    eta_pos_of_stability_weight_hypotheses hbaseline hc hκη
  have htail₁_exists :
      ∃ κ, kappa c < κ ∧ κ < 1 ∧
        HasWaveRightTailAsymptotic c κ U₁ :=
    ⟨κ₁, hκ_gt, hκ_lt_one, htail₁⟩
  have hclose : WeightedL2InitialCloseness η U₂ U₁ :=
    WeightedL2InitialCloseness.of_common_waveRightTailAsymptotic
      hηpos hηκ₁ hreg₁.U_cont hreg₂.U_cont
      hstrict₁.hasWaveUpperTailBound hstrict₂.hasWaveUpperTailBound
      htail₁ htail₂
  have hU₂bdd : IsCUnifBdd U₂ :=
    hstrict₂.isCUnifBdd_of_continuous hreg₂.U_cont
  have hU₂nn : NonnegativeInitialDatum U₂ :=
    IsTravelingWave.nonnegativeInitialDatum hTW₂ hU₂bdd
  have hU₂left : StrictlyPositiveAtLeft U₂ :=
    IsTravelingWave.strictlyPositiveAtLeft hTW₂
  rcases hstability c hc U₁ V₁ hTW₁ hreg₁ hstrict₁ htail₁_exists
      η hκη hηcap U₂ hU₂nn hU₂left hclose with
    ⟨_hexists, hall⟩
  have hmoving :
      IsBoundedGlobalCauchySolutionFrom p U₂
        (fun t x => U₂ (x - c * t))
        (fun t x => V₂ (x - c * t)) :=
    IsTravelingWave.movingWave_isBoundedGlobalCauchySolutionFrom
      hTW₂ hreg₂ hstrict₂
  have hconv :
      UniformMovingFrameConvergence c
        (fun t x => U₂ (x - c * t)) U₁ :=
    (hall _ _ hmoving).2
  exact Theorem_1_3_profile_eq_of_uniform_movingFrame_and_resolvent
    hconv
    (V_eq_frozenElliptic_of_TravelingWaveRegularity
      hTW₁ hstrict₁.hasWaveUpperTailBound hreg₁)
    (V_eq_frozenElliptic_of_TravelingWaveRegularity
      hTW₂ hstrict₂.hasWaveUpperTailBound hreg₂)

section Theorem13CorrectedAxiomAudit
#print axioms IsTravelingWave.to_globalCauchySolutionFrom_of_differentiable
#print axioms IsTravelingWave.movingWave_isBoundedGlobalCauchySolutionFrom
#print axioms Theorem_1_3_amended.of_bounded_stability
end Theorem13CorrectedAxiomAudit

end ShenWork.Paper1
