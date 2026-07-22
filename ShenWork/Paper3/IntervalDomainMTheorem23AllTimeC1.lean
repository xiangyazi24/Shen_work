import ShenWork.Paper3.IntervalDomainMTheorem23RestartDuhamel

/-!
# Honest all-time general-`m` Theorem 2.3 for `C¹`-compatible orbits

The legacy global-solution API controls only strict positive times, and its
`InitialTrace` is a sup-norm trace.  Thus a spatially smooth stored zero slice
alone does not rule out re-anchoring and does not imply a uniform physical
`C¹` bound as `t ↓ 0`.

The condition below records the missing standard compatibility property of a
solution issued from smooth data: continuity, from `t = 0`, of its physical
`C¹` distance to the equilibrium.  On every compact initial time interval this
gives a finite orbit-dependent bound.  Combining that bound with the explicit-
rate eventual restart--Duhamel theorem gives an honest all-time estimate with
the same rate.  The prefactor remains orbit-dependent; no uniform bound over
an unbounded class of smooth initial data is asserted.
-/

namespace ShenWork.Paper3

open Set
open ShenWork.Paper2

noncomputable section

/-- Initial-edge compatibility for a smooth/`C¹` orbit.  This is stronger than
the repository's sup-only `InitialTrace`: it controls both components in the
actual physical stability gauge and includes the stored `t = 0` slices. -/
def C1OrbitContinuousFromZero
    (D : BoundedDomainData) (N : StabilityNorms D)
    (u v : ℝ → D.Point → ℝ) (uStar vStar : ℝ) : Prop :=
  ContinuousOn
    (fun t =>
      N.c1Distance (u t) (fun _ => uStar) +
        N.c1Distance (v t) (fun _ => vStar))
    (Set.Ici (0 : ℝ))

/-- An eventual exponential estimate extends to `t = 0` when the orbit is
`C¹`-continuous at the initial edge.  The rate is unchanged; only the
prefactor is enlarged to absorb the compact interval `[0,t₀]`. -/
theorem eventualExponentialC1_allTime_of_C1OrbitContinuousFromZero
    {D : BoundedDomainData} {N : StabilityNorms D}
    {u v : ℝ → D.Point → ℝ} {uStar vStar C rate t₀ : ℝ}
    (hC : 0 < C) (hrate : 0 < rate)
    (hevent : EventualExponentialC1ConvergenceWith
      D N u v uStar vStar C rate t₀)
    (hC1 : C1OrbitContinuousFromZero D N u v uStar vStar) :
    ∃ CAll > 0,
      ExponentialC1ConvergenceWith
        D N u v uStar vStar CAll rate := by
  let dist : ℝ → ℝ := fun t =>
    N.c1Distance (u t) (fun _ => uStar) +
      N.c1Distance (v t) (fun _ => vStar)
  have hcont : ContinuousOn dist (Set.Icc (0 : ℝ) t₀) := by
    exact hC1.mono (fun _ ht => ht.1)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  let M : ℝ := max B 1
  let early : ℝ := M * Real.exp (rate * t₀)
  let CAll : ℝ := C + early
  have hM : 0 < M := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hearly : 0 < early := mul_pos hM (Real.exp_pos _)
  have hCAll : 0 < CAll := add_pos hC hearly
  refine ⟨CAll, hCAll, ?_⟩
  intro t ht
  change dist t ≤ CAll * Real.exp (-rate * t)
  by_cases hlate : t₀ ≤ t
  · have h := hevent t hlate
    change dist t ≤ C * Real.exp (-rate * t) at h
    calc
      dist t ≤ C * Real.exp (-rate * t) := h
      _ ≤ CAll * Real.exp (-rate * t) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        dsimp [CAll, early]
        linarith [hearly]
  · have htt₀ : t ≤ t₀ := le_of_not_ge hlate
    have htmem : t ∈ Set.Icc (0 : ℝ) t₀ := ⟨ht, htt₀⟩
    have hdistB : dist t ≤ B := by
      have habs : |dist t| ≤ B := by
        simpa [Real.norm_eq_abs] using hB t htmem
      exact (le_abs_self (dist t)).trans habs
    have hBM : B ≤ M := le_max_left _ _
    have harg : 0 ≤ rate * (t₀ - t) :=
      mul_nonneg hrate.le (sub_nonneg.mpr htt₀)
    have hexpOne : 1 ≤ Real.exp (rate * (t₀ - t)) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr harg
    have hexpFactor :
        Real.exp (rate * t₀) * Real.exp (-rate * t) =
          Real.exp (rate * (t₀ - t)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hearlyBound : M ≤ early * Real.exp (-rate * t) := by
      rw [show early * Real.exp (-rate * t) =
          M * Real.exp (rate * (t₀ - t)) by
        dsimp [early]
        rw [mul_assoc, hexpFactor]]
      exact (mul_one M).symm.trans_le
        (mul_le_mul_of_nonneg_left hexpOne hM.le)
    calc
      dist t ≤ B := hdistB
      _ ≤ M := hBM
      _ ≤ early * Real.exp (-rate * t) := hearlyBound
      _ ≤ CAll * Real.exp (-rate * t) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        dsimp [CAll]
        linarith [hC]

/-- Global attraction and all-time exponential convergence on the class of
orbits that are physically `C¹`-continuous from their stored zero slice. -/
def GloballyExponentiallyStableNonminimalOnC1OrbitsWithRate
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (uStar vStar rate : ℝ) : Prop :=
  GloballyAsymptoticallyStableNonminimal D p uStar vStar ∧
    0 < rate ∧
    ∀ u v : ℝ → D.Point → ℝ,
      PositiveGlobalBoundedSolution D p u v →
      C1OrbitContinuousFromZero D N u v uStar vStar →
        ∃ C > 0,
          ExponentialC1ConvergenceWith
            D N u v uStar vStar C rate

/-- Mass-constrained all-time counterpart for `C¹`-compatible orbits. -/
def GloballyExponentiallyStableMinimalOnC1OrbitsWithRate
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (uStar vStar rate : ℝ) : Prop :=
  GloballyAsymptoticallyStableMinimalOnPhysicalMass D p uStar vStar ∧
    0 < rate ∧
    ∀ u v : ℝ → D.Point → ℝ,
      PositiveGlobalBoundedSolution D p u v →
      HasEquilibriumMassOnPositiveTimes D u uStar →
      C1OrbitContinuousFromZero D N u v uStar vStar →
        ∃ C > 0,
          ExponentialC1ConvergenceWith
            D N u v uStar vStar C rate

/-- Fixed-rate eventual global stability becomes honest all-time stability on
the `C¹`-compatible orbit class. -/
theorem
EventuallyGloballyExponentiallyStableNonminimalWithRate.allTime_on_C1Orbits
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    {uStar vStar rate : ℝ}
    (h : EventuallyGloballyExponentiallyStableNonminimalWithRate
      D p N uStar vStar rate) :
    GloballyExponentiallyStableNonminimalOnC1OrbitsWithRate
      D p N uStar vStar rate := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro u v huv hC1
  obtain ⟨C, hC, t₀, ht₀, hevent⟩ := h.2.2 u v huv
  exact eventualExponentialC1_allTime_of_C1OrbitContinuousFromZero
    hC h.2.1 hevent hC1

/-- Mass-constrained fixed-rate eventual global stability has the same
all-time upgrade. -/
theorem
EventuallyGloballyExponentiallyStableMinimalWithRate.allTime_on_C1Orbits
    {D : BoundedDomainData} {p : CM2Params} {N : StabilityNorms D}
    {uStar vStar rate : ℝ}
    (h : EventuallyGloballyExponentiallyStableMinimalWithRate
      D p N uStar vStar rate) :
    GloballyExponentiallyStableMinimalOnC1OrbitsWithRate
      D p N uStar vStar rate := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro u v huv hmass hC1
  obtain ⟨C, hC, t₀, ht₀, hevent⟩ := h.2.2 u v huv hmass
  exact eventualExponentialC1_allTime_of_C1OrbitContinuousFromZero
    hC h.2.1 hevent hC1

/-- Positive general-`m` Theorem 2.3, from `t = 0`, for `C¹`-compatible
orbits.  The rate is the explicit `(p.a * p.α) / 4`. -/
theorem intervalDomainM_Theorem_2_3_positive_allTime_of_C1Data
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) :
    ∀ (ha : 0 < p.a) (hb : 0 < p.b),
      let eq := positiveEquilibrium p ⟨ha, hb⟩
      GloballyExponentiallyStableNonminimalOnC1OrbitsWithRate
        ShenWork.IntervalDomain.intervalDomainM p
          intervalDomainMSectorialStabilityNorms
            eq.1 eq.2 ((p.a * p.α) / 4) := by
  intro ha hb
  exact
    (intervalDomainM_Theorem_2_3_positive_via_restartDuhamel
      p hχ ha hb).allTime_on_C1Orbits

/-- Minimal mass-constrained all-time branch for `C¹`-compatible orbits, at
the explicit rate `firstNonzero / 4`. -/
theorem intervalDomainM_Theorem_2_3_minimal_allTime_of_C1Data
    (p : CM2Params) (hχ : p.χ₀ ≤ 0)
    (ha0 : p.a = 0) (hb0 : p.b = 0) :
    ∀ uStar > 0,
      let eq := minimalEquilibrium p uStar
      GloballyExponentiallyStableMinimalOnC1OrbitsWithRate
        ShenWork.IntervalDomain.intervalDomainM p
          intervalDomainMSectorialStabilityNorms eq.1 eq.2
            (unitIntervalNeumannSpectrum.firstNonzero / 4) := by
  intro uStar huStar
  exact
    (intervalDomainM_Theorem_2_3_minimal_via_restartDuhamel
      p hχ ha0 hb0 uStar huStar).allTime_on_C1Orbits

/-- Full honest all-time form of faithful general-`m` Theorem 2.3 on the
`C¹`-compatible orbit class. -/
theorem intervalDomainM_Theorem_2_3_allTime_of_C1Data
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) :
    (∀ (ha : 0 < p.a) (hb : 0 < p.b),
      let eq := positiveEquilibrium p ⟨ha, hb⟩
      GloballyExponentiallyStableNonminimalOnC1OrbitsWithRate
        ShenWork.IntervalDomain.intervalDomainM p
          intervalDomainMSectorialStabilityNorms
            eq.1 eq.2 ((p.a * p.α) / 4)) ∧
    (p.a = 0 → p.b = 0 →
      ∀ uStar > 0,
        let eq := minimalEquilibrium p uStar
        GloballyExponentiallyStableMinimalOnC1OrbitsWithRate
          ShenWork.IntervalDomain.intervalDomainM p
            intervalDomainMSectorialStabilityNorms eq.1 eq.2
              (unitIntervalNeumannSpectrum.firstNonzero / 4)) := by
  exact ⟨intervalDomainM_Theorem_2_3_positive_allTime_of_C1Data p hχ,
    fun ha0 hb0 =>
      intervalDomainM_Theorem_2_3_minimal_allTime_of_C1Data
        p hχ ha0 hb0⟩

#print axioms C1OrbitContinuousFromZero
#print axioms eventualExponentialC1_allTime_of_C1OrbitContinuousFromZero
#print axioms
  EventuallyGloballyExponentiallyStableNonminimalWithRate.allTime_on_C1Orbits
#print axioms
  EventuallyGloballyExponentiallyStableMinimalWithRate.allTime_on_C1Orbits
#print axioms intervalDomainM_Theorem_2_3_positive_allTime_of_C1Data
#print axioms intervalDomainM_Theorem_2_3_minimal_allTime_of_C1Data
#print axioms intervalDomainM_Theorem_2_3_allTime_of_C1Data

end

end ShenWork.Paper3
