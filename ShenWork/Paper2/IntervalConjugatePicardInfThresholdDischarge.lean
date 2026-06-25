import ShenWork.Paper2.IntervalConjugatePicardInfThreshold

open MeasureTheory Set Filter Topology

open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalMildPicard
  (HasJointMeasurability)

noncomputable section

namespace ShenWork.IntervalConjugatePicard

/-- Construct the inf-threshold data from the canonical Picard data plus the
source bounds/integrability facts that are not carried by
`ConjugateMildExistenceData`.

This is not a wrapper around an existing `ConjugatePicardInfThresholdData`: the
geometric convergence fields are derived from `D` by replaying the Picard ball
and contraction argument. -/
def conjugatePicardInfThresholdData_of_picard_bounds
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀)
    (CQ CL : ℝ) (hCQ : 0 ≤ CQ) (hCL : 0 ≤ CL)
    (hQ_int : ∀ n, ∀ s, 0 < s → s ≤ D.T →
      Integrable
        (ShenWork.IntervalGradientDuhamelMap.chemFluxLifted p
          (conjugatePicardIter p u₀ n s))
        (ShenWork.IntervalDomain.intervalMeasure 1))
    (hQ_bound : ∀ n, ∀ s, 0 < s → s ≤ D.T → ∀ y,
      |ShenWork.IntervalGradientDuhamelMap.chemFluxLifted p
          (conjugatePicardIter p u₀ n s) y| ≤ CQ)
    (hB_int : ∀ n t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
      IntervalIntegrable
        (fun s : ℝ =>
          ShenWork.IntervalConjugateDuhamelMap.intervalConjugateKernelOperator
            (t - s)
            (ShenWork.IntervalGradientDuhamelMap.chemFluxLifted p
              (conjugatePicardIter p u₀ n s)) x.1)
        volume 0 t)
    (hL_bound : ∀ n, ∀ s, 0 < s → s ≤ D.T → ∀ y,
      |ShenWork.IntervalGradientDuhamelMap.logisticLifted p
          (conjugatePicardIter p u₀ n s) y| ≤ CL)
    (hL_int : ∀ n t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
      IntervalIntegrable
        (fun s : ℝ =>
          ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
            (t - s)
            (ShenWork.IntervalGradientDuhamelMap.logisticLifted p
              (conjugatePicardIter p u₀ n s)) x.1)
        volume 0 t) :
    ConjugatePicardInfThresholdData p u₀ D.T := by
  have hball_cont := fun n =>
    conjugatePicardIter_ball p u₀ D.hbase_ball D.hbase_nonneg D.hbase_cont
      D.hmapsTo D.hmapsTo_nn D.hcont_preserved D.hbase_meas D.hmeas_preserved n
  have hball := fun n => (hball_cont n).1
  have hball_nn := fun n => (hball_cont n).2.1
  have hcont_iterates := fun n => (hball_cont n).2.2
  have hmeas_iterates :
      ∀ n, HasJointMeasurability (conjugatePicardIter p u₀ n) := by
    intro n
    induction n with
    | zero => exact D.hbase_meas
    | succ n ih => exact D.hmeas_preserved _ ih
  have hgeom :=
    conjugatePicardIter_geometric p u₀ D.hK_nn hball hball_nn
      hcont_iterates hmeas_iterates D.hcontr D.hC₀ D.hbase_diff
  exact
    { K := D.K
      C₀ := D.C₀
      CQ := CQ
      CL := CL
      hT := D.hT
      hK := D.hK
      hK_nn := D.hK_nn
      hC₀ := D.hC₀
      hCQ := hCQ
      hCL := hCL
      hgeom := hgeom
      hQ_int := hQ_int
      hQ_bound := hQ_bound
      hB_int := hB_int
      hL_bound := hL_bound
      hL_int := hL_int }

/-- Strict positivity plus joint continuity gives a uniform positive lower
floor on any closed time-space strip `[s,t] × [0,1] ⊂ (0,T) × [0,1]`.

The proof consumes the two named facts directly: `hjoint` supplies continuity on
the compact slab, and `hpos` makes the attained minimum positive. -/
theorem conjugatePicardLimit_uniformPositive_on_compact
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T s t : ℝ}
    (hs : 0 < s) (hst : s ≤ t) (htT : t < T)
    (hjoint : ContinuousOn
      (Function.uncurry
        (fun (τ : ℝ) (x : ℝ) =>
          intervalDomainLift (conjugatePicardLimit p u₀ T τ) x))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1))
    (hpos : ∀ τ x, 0 < τ → τ < T →
      0 < conjugatePicardLimit p u₀ T τ x) :
    ∃ c : ℝ, 0 < c ∧
      ∀ τ ∈ Set.Icc s t, ∀ x ∈ Set.Icc (0 : ℝ) 1,
        c ≤ intervalDomainLift (conjugatePicardLimit p u₀ T τ) x := by
  have hKcompact : IsCompact (Set.Icc s t ×ˢ Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  have hKne : (Set.Icc s t ×ˢ Set.Icc (0 : ℝ) 1).Nonempty :=
    ⟨(s, 0), ⟨Set.left_mem_Icc.mpr hst,
      by constructor <;> norm_num⟩⟩
  have hsub : Set.Icc s t ×ˢ Set.Icc (0 : ℝ) 1 ⊆
      Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1 := by
    rintro ⟨τ, x⟩ ⟨hτ, hx⟩
    exact ⟨⟨lt_of_lt_of_le hs hτ.1, lt_of_le_of_lt hτ.2 htT⟩, hx⟩
  have hcontK : ContinuousOn
      (Function.uncurry
        (fun (τ : ℝ) (x : ℝ) =>
          intervalDomainLift (conjugatePicardLimit p u₀ T τ) x))
      (Set.Icc s t ×ˢ Set.Icc (0 : ℝ) 1) :=
    hjoint.mono hsub
  obtain ⟨q₀, hq₀_mem, hq₀_min⟩ :=
    hKcompact.exists_isMinOn hKne hcontK
  obtain ⟨τ₀, x₀⟩ := q₀
  obtain ⟨hτ₀_mem, hx₀_mem⟩ := hq₀_mem
  have hτ₀_open : τ₀ ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_of_lt_of_le hs hτ₀_mem.1, lt_of_le_of_lt hτ₀_mem.2 htT⟩
  have hmin_pos :
      0 < intervalDomainLift (conjugatePicardLimit p u₀ T τ₀) x₀ := by
    simpa [intervalDomainLift, hx₀_mem] using
      hpos τ₀ ⟨x₀, hx₀_mem⟩ hτ₀_open.1 hτ₀_open.2
  refine ⟨intervalDomainLift (conjugatePicardLimit p u₀ T τ₀) x₀,
    hmin_pos, ?_⟩
  intro τ hτ x hx
  exact isMinOn_iff.mp hq₀_min (τ, x) ⟨hτ, hx⟩

#print axioms conjugatePicardInfThresholdData_of_picard_bounds
#print axioms conjugatePicardLimit_uniformPositive_on_compact

end ShenWork.IntervalConjugatePicard
