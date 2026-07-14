import ShenWork.Paper3.IntervalDomainSectorial
import ShenWork.Paper3.IntervalDomainStabilityChain
import ShenWork.PDE.IntervalDomainExistence
import ShenWork.PDE.P3MoserEnergyContinuity

/-!
# Zero-time obstruction for the existential-rate sectorial frontier

The rate repair removes the false `pi^2` decay demand on the mean mode, but the
current all-time API has a second independent obstruction.  `InitialTrace`
controls only the deleted-right limit as `t -> 0+`; it does not constrain the
stored slices `u 0` or `v 0`.  The interval classical-solution predicate is
likewise local on strict positive times.  Hence a global solution can be
re-anchored to an arbitrarily large spatially constant slice at `t = 0`
without changing either global classical solvability or the initial trace.

The theorem below records this obstruction for the concrete interval
sectorial norms and a linearly stable logistic equilibrium.
-/

namespace ShenWork.Paper3

open Filter Topology
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity

noncomputable section

private theorem intervalDomain_gradNorm_const (c : ℝ)
    (x : intervalDomain.Point) :
    intervalDomain.gradNorm (fun _ : intervalDomain.Point => c) x = 0 := by
  change |deriv (intervalDomainLift (fun _ : intervalDomainPoint => c)) x.1| = 0
  rcases x.property with ⟨hx0, hx1⟩
  rcases eq_or_lt_of_le hx0 with hxeq0 | hxlt
  · rw [← hxeq0, (intervalDomainLift_const_deriv_endpoint_zero c).1]
    norm_num
  · rcases eq_or_lt_of_le hx1 with hxeq1 | hxlt1
    · rw [hxeq1, (intervalDomainLift_const_deriv_endpoint_zero c).2]
      norm_num
    · rw [intervalDomainLift_const_deriv_zero c ⟨hxlt, hxlt1⟩]
      norm_num

/-- The concrete sectorial `C1` distance between two spatial constants is the
absolute difference of those constants. -/
theorem intervalDomainSectorialC1Distance_const (a b : ℝ) :
    intervalDomainSectorialC1Distance
        (fun _ : intervalDomain.Point => a)
        (fun _ : intervalDomain.Point => b) = |a - b| := by
  unfold intervalDomainSectorialC1Distance
  have hvalue :
      (fun x : intervalDomain.Point => a - b) = fun _ => a - b := by
    rfl
  have hgrad :
      (fun x : intervalDomain.Point =>
        intervalDomain.gradNorm (fun _ : intervalDomain.Point => a - b) x) =
        fun _ => 0 := by
    funext x
    exact intervalDomain_gradNorm_const (a - b) x
  rw [hvalue, hgrad]
  change intervalDomainSupNorm (fun _ : intervalDomainPoint => a - b) +
      intervalDomainSupNorm (fun _ : intervalDomainPoint => 0) = |a - b|
  rw [intervalDomainSupNorm_const, intervalDomainSupNorm_const, abs_zero, add_zero]

private theorem correctedObstruction_linearlyStable :
    LinearlyStable unitIntervalNeumannSpectrum
      nonminimalGlobalStabilityCounterParams 1 1 := by
  apply LinearlyStable_of_chi_nonpos_a_pos
  · norm_num [nonminimalGlobalStabilityCounterParams]
  · norm_num [nonminimalGlobalStabilityCounterParams]
  · norm_num
  · norm_num
  · intro n _hn
    exact unitIntervalNeumannSpectrum_hasNeumannSpectrum.eigenvalue_nonneg n

private theorem correctedObstruction_linearlyStable_wrong_vStar :
    LinearlyStable unitIntervalNeumannSpectrum
      nonminimalGlobalStabilityCounterParams 1 2 := by
  apply LinearlyStable_of_chi_nonpos_a_pos
  · norm_num [nonminimalGlobalStabilityCounterParams]
  · norm_num [nonminimalGlobalStabilityCounterParams]
  · norm_num
  · norm_num
  · intro n _hn
    exact unitIntervalNeumannSpectrum_hasNeumannSpectrum.eigenvalue_nonneg n

private theorem correctedObstruction_constant_global :
    IsPaper2GlobalClassicalSolution intervalDomain
      nonminimalGlobalStabilityCounterParams
      (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) := by
  intro T hT
  simpa [nonminimalGlobalStabilityCounterParams,
    ellipticV] using
    equilibrium_isPaper2ClassicalSolution
      nonminimalGlobalStabilityCounterParams
      (by norm_num [nonminimalGlobalStabilityCounterParams])
      (by norm_num [nonminimalGlobalStabilityCounterParams]) T hT

private theorem correctedObstruction_constant_trace :
    InitialTrace intervalDomain (fun _ : intervalDomain.Point => (1 : ℝ))
      (fun _ _ => (1 : ℝ)) := by
  simpa [constOnInterval] using
    constantSolution_initialTrace 1

private theorem initialTrace_reanchor_arbitrary
    {u0 z : intervalDomain.Point → ℝ}
    {u : ℝ → intervalDomain.Point → ℝ}
    (htrace : InitialTrace intervalDomain u0 u) :
    InitialTrace intervalDomain u0
      (intervalDomainWithInitialSlice z u) := by
  intro eps heps
  rcases htrace eps heps with ⟨eta, heta, hsmall⟩
  refine ⟨eta, heta, ?_⟩
  intro t ht0 hteta
  have htne : t ≠ 0 := ne_of_gt ht0
  simpa [intervalDomainWithInitialSlice, htne] using hsmall t ht0 hteta

/-- The requested all-time corrected frontier is still false for the concrete
interval norms.  The counterexample changes only the stored `u 0` slice of the
constant equilibrium; all strict-positive-time PDE and trace data are
unchanged. -/
theorem
not_intervalDomainSpectralSemigroupOrbitBoundAllTimeExistentialRate_sectorialNorms :
    ¬ IntervalDomainSpectralSemigroupOrbitBoundAllTimeExistentialRate
      nonminimalGlobalStabilityCounterParams
      intervalDomainSectorialStabilityNorms := by
  intro horbit
  rcases horbit (3 / 4) 2 1 1
      (by norm_num) (by norm_num) (by norm_num)
      correctedObstruction_linearlyStable with
    ⟨eps, heps, C, hC, rate, hrate, hbound⟩
  have hdatum :
      PositiveInitialDatum intervalDomain
        (fun _ : intervalDomain.Point => (1 : ℝ)) := by
    simpa [constOnInterval] using
      (constOnInterval_pos (c := (1 : ℝ)) one_pos)
  have hsmall :
      intervalDomainSectorialStabilityNorms.xpSigmaDistance (3 / 4) 2
        (fun _ : intervalDomain.Point => (1 : ℝ)) (fun _ => (1 : ℝ)) ≤ eps := by
    change intervalDomainSupNorm (fun _ : intervalDomainPoint => (1 : ℝ) - 1) ≤ eps
    simpa [intervalDomainSupNorm_const] using heps.le
  let z : intervalDomain.Point → ℝ := fun _ => C + 2
  let u : ℝ → intervalDomain.Point → ℝ :=
    intervalDomainWithInitialSlice z (fun _ _ => (1 : ℝ))
  have hglobal :
      IsPaper2GlobalClassicalSolution intervalDomain
        nonminimalGlobalStabilityCounterParams u (fun _ _ => (1 : ℝ)) := by
    exact intervalDomain_globalClassical_withInitialSlice
      (u₀ := z) correctedObstruction_constant_global
  have htrace :
      InitialTrace intervalDomain (fun _ : intervalDomain.Point => (1 : ℝ)) u := by
    exact initialTrace_reanchor_arbitrary correctedObstruction_constant_trace
  have hzero := hbound
    (fun _ : intervalDomain.Point => (1 : ℝ)) hdatum hsmall
    u (fun _ _ => (1 : ℝ)) hglobal htrace 0 (le_refl 0)
  have hu0 : u 0 = fun _ : intervalDomain.Point => C + 2 := by
    funext x
    change (if (0 : ℝ) = 0 then C + 2 else 1) = C + 2
    simp
  rw [hu0, intervalDomainSectorialStabilityNorms_c1Distance,
    intervalDomainSectorialC1Distance_const,
    intervalDomainSectorialStabilityNorms_c1Distance,
    intervalDomainSectorialC1Distance_const] at hzero
  norm_num at hzero
  have habs : |C + 2 - 1| = C + 1 := by
    rw [abs_of_pos (by linarith [hC])]
    ring
  rw [habs] at hzero
  linarith

/-- Eventual time does not repair the independent missing-equilibrium defect.
For zero sensitivity the nonzero spectrum is stable at the arbitrary target
`(uStar,vStar) = (1,2)`, while the genuine constant equilibrium is `(1,1)`.
The latter starts at zero `u`-distance but stays a fixed positive `v`-distance
from the arbitrary target for every positive time. -/
theorem
not_intervalDomainSpectralSemigroupOrbitBoundEventualWithoutEquilibrium_sectorialNorms :
    ¬ IntervalDomainSpectralSemigroupOrbitBoundEventualWithoutEquilibrium
      nonminimalGlobalStabilityCounterParams
      intervalDomainSectorialStabilityNorms := by
  intro horbit
  rcases horbit (3 / 4) 2 1 2
      (by norm_num) (by norm_num) (by norm_num)
      correctedObstruction_linearlyStable_wrong_vStar with
    ⟨eps, heps, C, hC, rate, hrate, t₀, ht₀, hbound⟩
  have hdatum :
      PositiveInitialDatum intervalDomain
        (fun _ : intervalDomain.Point => (1 : ℝ)) := by
    simpa [constOnInterval] using
      (constOnInterval_pos (c := (1 : ℝ)) one_pos)
  have hsmall :
      intervalDomainSectorialStabilityNorms.xpSigmaDistance (3 / 4) 2
        (fun _ : intervalDomain.Point => (1 : ℝ)) (fun _ => (1 : ℝ)) ≤ eps := by
    change intervalDomainSupNorm (fun _ : intervalDomainPoint => (1 : ℝ) - 1) ≤ eps
    simpa [intervalDomainSupNorm_const] using heps.le
  have hmul : Tendsto (fun t : ℝ => rate * t) atTop atTop :=
    (Filter.tendsto_id.atTop_mul_const hrate).congr
      (fun t => mul_comm t rate)
  have hneg : Tendsto (fun t : ℝ => -(rate * t)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hmul
  have hexp : Tendsto (fun t : ℝ => Real.exp (-(rate * t))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hneg
  have hlim :
      Tendsto (fun t : ℝ => C * Real.exp (-rate * t)) atTop (𝓝 0) := by
    convert tendsto_const_nhds.mul hexp using 1
    · ext t
      ring_nf
    · simp
  have hevent :
      ∀ᶠ t : ℝ in atTop, C * Real.exp (-rate * t) < (1 : ℝ) :=
    hlim.eventually (Iio_mem_nhds one_pos)
  rcases eventually_atTop.1 hevent with ⟨T, hT⟩
  let t : ℝ := max T t₀
  have ht₀le : t₀ ≤ t := le_max_right T t₀
  have hTle : T ≤ t := le_max_left T t₀
  have hsmall_rhs : C * Real.exp (-rate * t) < (1 : ℝ) := hT t hTle
  have hlarge_rhs :=
    hbound (fun _ : intervalDomain.Point => (1 : ℝ)) hdatum hsmall
      (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ))
      correctedObstruction_constant_global correctedObstruction_constant_trace
      t ht₀le
  simp only [intervalDomainSectorialStabilityNorms_c1Distance,
    intervalDomainSectorialC1Distance_const] at hlarge_rhs
  norm_num at hlarge_rhs
  have hneg_mul : -(rate * t) = -rate * t := by ring
  rw [hneg_mul] at hlarge_rhs
  exact (not_lt_of_ge hlarge_rhs) hsmall_rhs

private theorem correctedObstruction_minimal_linearlyStable :
    LinearlyStable unitIntervalNeumannSpectrum
      proposition12CounterParams 1 1 := by
  intro n hn
  have hlambda :
      0 < unitIntervalNeumannSpectrum.eigenvalue n :=
    unitIntervalNeumannSpectrum_hasNeumannSpectrum.eigenvalue_pos_of_ne_zero n hn
  simpa [sigma, proposition12CounterParams] using (neg_lt_zero.mpr hlambda)

private theorem correctedObstruction_minimal_equilibrium :
    Paper3ConstantEquilibrium proposition12CounterParams 1 1 := by
  simpa [minimalEquilibrium, proposition12CounterParams] using
    (paper3ConstantEquilibrium_minimal proposition12CounterParams
      (by rfl) (by rfl) 1 one_pos)

/-- Historical all-branch version of the mass-free eventual frontier.

This is intentionally separate from the valid positive-logistic interface
`IntervalDomainSpectralSemigroupOrbitBoundEventualEquilibriumWithoutMass`,
which assumes `0 < p.a`.  In the minimal model the zero mode is neutral, so a
mass-free attraction statement is false. -/
def IntervalDomainMinimalEventualEquilibriumWithoutMass
    (p : CM2Params) (N : StabilityNorms intervalDomain) : Prop :=
  ∀ sigma pNorm uStar vStar,
    1 / 2 < sigma → sigma < 1 → 1 < pNorm →
    Paper3ConstantEquilibrium p uStar vStar →
    LinearlyStable unitIntervalNeumannSpectrum p uStar vStar →
      ∃ eps > 0, ∃ C > 0, ∃ rate > 0, ∃ t₀ > 0,
        ∀ u₀ : intervalDomain.Point → ℝ, PositiveInitialDatum intervalDomain u₀ →
          N.xpSigmaDistance sigma pNorm u₀ (fun _ => uStar) ≤ eps →
            ∀ u v : ℝ → intervalDomain.Point → ℝ,
              IsPaper2GlobalClassicalSolution intervalDomain p u v →
              InitialTrace intervalDomain u₀ u →
                ∀ t, t₀ ≤ t →
                  N.c1Distance (u t) (fun _ => uStar) +
                    N.c1Distance (v t) (fun _ => vStar) ≤
                      C * Real.exp (-rate * t)

/-- In the zero-reaction branch, even a genuine linearly stable equilibrium
cannot attract nearby data of a different mass.  A nearby spatial constant is
itself a stationary solution and stays a fixed positive distance away. -/
theorem
not_intervalDomainMinimalEventualEquilibriumWithoutMass_sectorialNorms :
    ¬ IntervalDomainMinimalEventualEquilibriumWithoutMass
      proposition12CounterParams intervalDomainSectorialStabilityNorms := by
  intro horbit
  rcases horbit (3 / 4) 2 1 1
      (by norm_num) (by norm_num) (by norm_num)
      correctedObstruction_minimal_equilibrium
      correctedObstruction_minimal_linearlyStable with
    ⟨eps, heps, C, hC, rate, hrate, t₀, ht₀, hbound⟩
  let c : ℝ := 1 + eps / 2
  have hc : 0 < c := by dsimp [c]; linarith
  have hdatum :
      PositiveInitialDatum intervalDomain
        (fun _ : intervalDomain.Point => c) := by
    simpa [constOnInterval] using (constOnInterval_pos (c := c) hc)
  have hsmall :
      intervalDomainSectorialStabilityNorms.xpSigmaDistance (3 / 4) 2
        (fun _ : intervalDomain.Point => c) (fun _ => (1 : ℝ)) ≤ eps := by
    change intervalDomainSupNorm (fun _ : intervalDomainPoint => c - 1) ≤ eps
    rw [intervalDomainSupNorm_const, abs_of_nonneg]
    · dsimp [c]
      linarith
    · dsimp [c]
      linarith
  have hglobal :
      IsPaper2GlobalClassicalSolution intervalDomain proposition12CounterParams
        (fun _ _ => c) (fun _ _ => c) := by
    intro T hT
    simpa [ellipticV, proposition12CounterParams] using
      (zeroReaction_isPaper2ClassicalSolution proposition12CounterParams
        (by rfl) (by rfl) c hc T hT)
  have htrace :
      InitialTrace intervalDomain (fun _ : intervalDomain.Point => c)
        (fun _ _ => c) := by
    simpa [constOnInterval] using constantSolution_initialTrace c
  have hmul : Tendsto (fun t : ℝ => rate * t) atTop atTop :=
    (Filter.tendsto_id.atTop_mul_const hrate).congr
      (fun t => mul_comm t rate)
  have hneg : Tendsto (fun t : ℝ => -(rate * t)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hmul
  have hexp : Tendsto (fun t : ℝ => Real.exp (-(rate * t))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hneg
  have hlim :
      Tendsto (fun t : ℝ => C * Real.exp (-rate * t)) atTop (𝓝 0) := by
    convert tendsto_const_nhds.mul hexp using 1
    · ext t
      ring_nf
    · simp
  have hevent :
      ∀ᶠ t : ℝ in atTop, C * Real.exp (-rate * t) < eps :=
    hlim.eventually (Iio_mem_nhds heps)
  rcases eventually_atTop.1 hevent with ⟨T, hT⟩
  let t : ℝ := max T t₀
  have ht₀le : t₀ ≤ t := le_max_right T t₀
  have hTle : T ≤ t := le_max_left T t₀
  have hsmall_rhs : C * Real.exp (-rate * t) < eps := hT t hTle
  have hlarge_rhs :=
    hbound (fun _ : intervalDomain.Point => c) hdatum hsmall
      (fun _ _ => c) (fun _ _ => c) hglobal htrace t ht₀le
  simp only [intervalDomainSectorialStabilityNorms_c1Distance,
    intervalDomainSectorialC1Distance_const] at hlarge_rhs
  have hcsub : c - 1 = eps / 2 := by dsimp [c]; ring
  rw [hcsub] at hlarge_rhs
  simp only [abs_of_pos (half_pos heps)] at hlarge_rhs
  linarith

/-! ### Exact obstruction to the original Paper 3 Theorem 2.5

The preceding all-time sectorial counterexample re-anchors the stored `u 0`
slice and therefore deliberately works through `InitialTrace`.  The original
`Theorem_2_5` has an even sharper defect: its mass hypothesis constrains only
`u 0`, while its all-time `C¹` conclusion also reads `v 0`.  Re-anchoring only
`v 0` leaves the mass exactly correct and does not change the strict-positive-
time classical solution at all.
-/

/-- Whenever the paper's minimal stability condition is inhabited, the
original all-time `Theorem_2_5` target is false for the concrete interval
`C¹` distance.  The cell density is the genuine constant equilibrium and has
exact mass `uStar`; only the unused stored chemical slice `v 0` is changed
after the theorem chooses its supposedly uniform prefactor `A`. -/
theorem not_intervalDomain_Theorem_2_5_of_stabilityCondition
    (p : CM2Params) (C : Paper3Constants intervalDomain p)
    (ha : p.a = 0) (hb : p.b = 0) (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (uStar : ℝ) (huStar : 0 < uStar)
    (hcond : MinimalGlobalStabilityCondition intervalDomain p C uStar) :
    ¬ Theorem_2_5 intervalDomain p intervalDomainSectorialStabilityNorms C := by
  intro htheorem
  rcases (htheorem ha hb hm hβ uStar huStar hcond).2 with
    ⟨A, hA, rate, hrate, hbound⟩
  let vStar : ℝ := ellipticV p uStar
  let vZero : intervalDomain.Point → ℝ := fun _ => vStar + A + 2
  let u : ℝ → intervalDomain.Point → ℝ := fun _ _ => uStar
  let v : ℝ → intervalDomain.Point → ℝ :=
    intervalDomainWithInitialSlice vZero (fun _ _ => vStar)
  have hraw :
      IsPaper2GlobalClassicalSolution intervalDomain p
        (fun _ _ => uStar) (fun _ _ => vStar) := by
    simpa [vStar] using
      (zeroReaction_isPaper2ClassicalSolution p ha hb uStar huStar)
  have hglobal : IsPaper2GlobalClassicalSolution intervalDomain p u v := by
    intro T hT
    exact
      (classicalSolutionLocalityUnderIooAgreement_intervalDomain p)
        hT (hraw.classical hT) (by
          intro t ht0 _htT x
          have htne : t ≠ 0 := ne_of_gt ht0
          simp [u, v, intervalDomainWithInitialSlice, htne])
  have hbdd : IsPaper2Bounded intervalDomain u := by
    refine ⟨|uStar|, Eventually.of_forall (fun _t => ?_)⟩
    change intervalDomainSupNorm (fun _ : intervalDomainPoint => uStar) ≤ |uStar|
    rw [intervalDomainSupNorm_const]
  have hpositive : PositiveGlobalBoundedSolution intervalDomain p u v := by
    exact ⟨hglobal, hbdd, fun _t _x _ht _hx => huStar⟩
  have hmass : HasInitialMass intervalDomain u uStar := by
    change intervalDomainIntegral (fun _ : intervalDomainPoint => uStar) = 1 * uStar
    calc
      intervalDomainIntegral (fun _ : intervalDomainPoint => uStar) =
          ∫ _x in (0 : ℝ)..1, uStar := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
        rw [intervalDomainLift, dif_pos hx]
      _ = uStar := by simp
      _ = 1 * uStar := by ring
  have hzero := hbound u v hpositive hmass 0 (le_refl 0)
  have hu0 : u 0 = fun _ : intervalDomain.Point => uStar := rfl
  have hv0 : v 0 = fun _ : intervalDomain.Point => vStar + A + 2 := by
    funext x
    simp [v, vZero, intervalDomainWithInitialSlice]
  have heq1 : (minimalEquilibrium p uStar).1 = uStar := rfl
  have heq2 : (minimalEquilibrium p uStar).2 = vStar := rfl
  rw [hu0, hv0, heq1, heq2,
    intervalDomainSectorialStabilityNorms_c1Distance,
    intervalDomainSectorialC1Distance_const,
    intervalDomainSectorialStabilityNorms_c1Distance,
    intervalDomainSectorialC1Distance_const] at hzero
  norm_num at hzero
  have habs : |vStar + A + 2 - vStar| = A + 2 := by
    rw [abs_of_pos (by linarith [hA])]
    ring
  rw [habs] at hzero
  linarith

/-- A fully concrete, non-vacuous instance of the preceding obstruction.
All parameters are positive where required, the first explicit minimal
threshold branch is satisfied strictly, and the only contradiction comes from
the original theorem's all-time quantification over the unconstrained `v 0`
slice. -/
theorem not_intervalDomain_Theorem_2_5_original_allTime :
    ¬ Theorem_2_5 intervalDomain theorem21Part4CounterParams
      intervalDomainSectorialStabilityNorms
      (intervalDomainPaper3Constants theorem21Part4CounterParams 0 1 0) := by
  apply not_intervalDomain_Theorem_2_5_of_stabilityCondition
      theorem21Part4CounterParams
      (intervalDomainPaper3Constants theorem21Part4CounterParams 0 1 0)
      (by norm_num [theorem21Part4CounterParams])
      (by norm_num [theorem21Part4CounterParams])
      (by norm_num [theorem21Part4CounterParams])
      (by norm_num [theorem21Part4CounterParams])
      1 (by norm_num)
  apply MinimalGlobalStabilityCondition.of_chiMinimal1
  · norm_num [theorem21Part4CounterParams]
  · norm_num [intervalDomainPaper3Constants, chiMinimal1Formula, chiBeta,
      GammaMinimalFormula, theorem21Part4CounterParams]

#print axioms intervalDomainSectorialC1Distance_const
#print axioms
  not_intervalDomainSpectralSemigroupOrbitBoundAllTimeExistentialRate_sectorialNorms
#print axioms
  not_intervalDomainSpectralSemigroupOrbitBoundEventualWithoutEquilibrium_sectorialNorms
#print axioms
  not_intervalDomainMinimalEventualEquilibriumWithoutMass_sectorialNorms
#print axioms not_intervalDomain_Theorem_2_5_of_stabilityCondition
#print axioms not_intervalDomain_Theorem_2_5_original_allTime

end

end ShenWork.Paper3
