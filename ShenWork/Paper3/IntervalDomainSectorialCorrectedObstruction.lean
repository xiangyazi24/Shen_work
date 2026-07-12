import ShenWork.Paper3.IntervalDomainSectorial
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
not_intervalDomainSpectralSemigroupOrbitBoundCorrected_sectorialNorms :
    ¬ IntervalDomainSpectralSemigroupOrbitBoundCorrected
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

#print axioms intervalDomainSectorialC1Distance_const
#print axioms not_intervalDomainSpectralSemigroupOrbitBoundCorrected_sectorialNorms

end

end ShenWork.Paper3
