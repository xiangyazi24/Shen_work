import ShenWork.Paper3.IntervalDomainMEntropyBasinEntry
import ShenWork.Paper3.IntervalDomainStrongStageBGeneralM
import ShenWork.Paper3.IntervalDomainMWeakSupBasinEntry
import ShenWork.Paper2.IntervalDomainMContinuationExtension
import ShenWork.Paper3.EventualGlobalStability
import ShenWork.Paper3.IntervalDomainEntropyStrong1Global

/-!
# Unconditional first-branch global stability for the faithful general-`m` equation

This file consumes one general-`m` entropy-produced basin-entry slice, restarts
the proved faithful general-`m` Stage-B orbit theorem there, and derives both
eventual `C¹` exponential decay and qualitative uniform attraction, with no
`p.m = 1` hypothesis anywhere.
-/

namespace ShenWork.Paper3

open Filter Topology Set
open ShenWork.IntervalDomain ShenWork.Paper2

noncomputable section

/-- Fully closed faithful general-`m` Stage-B orbit bound, assembled from the
committed basin entry and the committed Stage-B reduction.  (Named after the
Theorem 2.4 chain to keep this file independent of the parallel
Theorem 2.2 assembly work.) -/
theorem intervalDomainM_thm24_weakSupOrbitBound
    (p : CM2Params) :
    IntervalDomainMWeakSupEventualSpectralSemigroupOrbitBound p :=
  intervalDomainM_weakSupEventualSpectralSemigroupOrbitBound_of_basinEntry
    p (intervalDomainMSupToStrongBasinEntry_proved p)

/-- A paper-positive datum is in particular a positive datum. -/
theorem positiveInitialDatum_of_paperPositiveInitialDatumM
    {u₀ : intervalDomainPoint → ℝ}
    (h : PaperPositiveInitialDatum intervalDomainM u₀) :
    PositiveInitialDatum intervalDomainM u₀ := by
  rcases h with ⟨hadm, η, hη, hfloor⟩
  exact ⟨hadm, fun x _hx => lt_of_lt_of_le hη (hfloor x)⟩

/-- Late basin entry followed by the proved faithful general-`m` weak-sup
Stage-B theorem: eventual exponential `C¹` convergence for every positive
bounded global orbit possessing arbitrarily late sup-close slices.  The
basin-entry producer is abstract, so every strong-logistic branch can consume
this theorem. -/
theorem intervalDomainM_eventualC1_of_lateSupClose
    (p : CM2Params)
    {uStar vStar : ℝ}
    (ha : 0 < p.a)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hstable : LinearlyStable unitIntervalNeumannSpectrum p uStar vStar)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v)
    (hlate : ∀ eps : ℝ, 0 < eps → ∃ t, 1 ≤ t ∧
      SupCloseToConstant intervalDomainM (u t) uStar eps) :
    ∃ C > 0, ∃ rate > 0, ∃ t₀ > 0,
      EventualExponentialC1ConvergenceWith
        intervalDomainM intervalDomainMSectorialStabilityNorms
          u v uStar vStar C rate t₀ := by
  rcases intervalDomainM_thm24_weakSupOrbitBound p uStar vStar ha heq hstable
    with ⟨delta, hdelta, C, hC, rate, hrate, delay, hdelay, hbound⟩
  obtain ⟨tau, htauLB, hclose⟩ := hlate delta hdelta
  have htau : 0 < tau := lt_of_lt_of_le one_pos htauLB
  have hsol := huv.classical (tau + 1) (by linarith)
  have hpid : PositiveInitialDatum intervalDomainM (u tau) :=
    positiveInitialDatum_of_paperPositiveInitialDatumM
      (ShenWork.Paper2.IntervalDomainMContinuation.classicalSolution_slice_paperPositiveInitialDatumM
        hsol ⟨htau, by linarith⟩)
  let us : ℝ → intervalDomainPoint → ℝ := fun t x => u (t + tau) x
  let vs : ℝ → intervalDomainPoint → ℝ := fun t x => v (t + tau) x
  have hshiftGlobal :
      IsPaper2GlobalClassicalSolution intervalDomainM p us vs := by
    intro T hT
    have hsum : 0 < T + tau := by linarith
    have hsolT := huv.classical (T + tau) hsum
    have hshift :=
      ShenWork.Paper2.IntervalDomainMContinuation.classicalSolution_timeShiftM
        hsolT htau (by linarith)
    simpa only [add_sub_cancel_right] using hshift
  have hshiftTrace : InitialTrace intervalDomainM (u tau) us := by
    simpa [us] using
      ShenWork.Paper2.IntervalDomainMContinuation.timeShiftInitialTraceM
        hsol htau (by linarith)
  have hshiftBound := hbound (u tau) hpid hclose us vs
    hshiftGlobal hshiftTrace
  let Cshift : ℝ := C * Real.exp (rate * tau)
  let t₀ : ℝ := tau + delay
  have hCshift : 0 < Cshift := mul_pos hC (Real.exp_pos _)
  have ht₀ : 0 < t₀ := by dsimp [t₀]; linarith
  refine ⟨Cshift, hCshift, rate, hrate, t₀, ht₀, ?_⟩
  intro t htt₀
  simp only [intervalDomainMSectorialStabilityNorms_c1Distance]
  let s : ℝ := t - tau
  have hdelayS : delay ≤ s := by dsimp [s, t₀] at *; linarith
  have hsEq : s + tau = t := by dsimp [s]; ring
  have hdecay := hshiftBound s hdelayS
  have hexpShift : Real.exp (-rate * s) =
      Real.exp (rate * tau) * Real.exp (-rate * t) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [s]
    ring
  calc
    intervalDomainSectorialC1Distance (u t) (fun _ => uStar) +
        intervalDomainSectorialC1Distance (v t) (fun _ => vStar) ≤
      C * Real.exp (-rate * s) := by
        simpa [us, vs, hsEq] using hdecay
    _ = Cshift * Real.exp (-rate * t) := by
      rw [hexpShift]
      dsimp [Cshift]
      ring

/-- Entropy basin entry followed by the proved faithful general-`m` weak-sup
Stage-B theorem: eventual exponential `C¹` convergence for every positive
bounded global orbit in the first strict formula branch. -/
theorem intervalDomainM_strongM_eventualC1
    (p : CM2Params) (hm : 1 ≤ p.m)
    {uStar vStar : ℝ}
    (ha : 0 < p.a) (hb : 0 < p.b)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hrel : 2 * p.γ ≤ p.α + 1)
    (hχpos : 0 < p.χ₀)
    (hχ : p.χ₀ < chiStrong1Formula p uStar vStar)
    (hstable : LinearlyStable unitIntervalNeumannSpectrum p uStar vStar)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v) :
    ∃ C > 0, ∃ rate > 0, ∃ t₀ > 0,
      EventualExponentialC1ConvergenceWith
        intervalDomainM intervalDomainMSectorialStabilityNorms
          u v uStar vStar C rate t₀ :=
  intervalDomainM_eventualC1_of_lateSupClose p ha heq hstable huv
    (fun eps heps =>
      intervalDomainM_strongM_exists_late_supClose
        p hm hb heq hrel hχpos hχ huv 1 heps)

/-- An eventual exponential bound in the faithful `C¹` gauge implies uniform
sup convergence of the `u` component, on the faithful domain. -/
theorem intervalDomainM_uniformConvergesInSup_of_eventualExponentialC1
    {u v : ℝ → intervalDomainPoint → ℝ}
    {uStar vStar C rate t₀ : ℝ}
    (hrate : 0 < rate)
    (hbound : EventualExponentialC1ConvergenceWith
      intervalDomainM intervalDomainMSectorialStabilityNorms
        u v uStar vStar C rate t₀) :
    UniformConvergesInSup intervalDomainM u uStar := by
  have hbound' : EventualExponentialC1ConvergenceWith
      intervalDomain intervalDomainSectorialStabilityNorms
        u v uStar vStar C rate t₀ := by
    intro t ht
    have hb := hbound t ht
    simpa only [intervalDomainMSectorialStabilityNorms_c1Distance,
      intervalDomainSectorialStabilityNorms_c1Distance] using hb
  have hconv :=
    intervalDomain_uniformConvergesInSup_of_eventualExponentialC1
      hrate hbound'
  exact hconv

/-- Unconditional first formula branch of faithful eventual Theorem 2.4 on
the general-`m` unit-interval equation.  No `p.m = 1` hypothesis. -/
theorem intervalDomainM_eventuallyGloballyExponentiallyStableNonminimal_strong1
    (p : CM2Params)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hmge : 1 ≤ p.m)
    (hrel : 2 * p.γ ≤ p.α + 1)
    (hχpos : 0 < p.χ₀)
    (hχ : p.χ₀ < chiStrong1Formula p
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    EventuallyGloballyExponentiallyStableNonminimal intervalDomainM p
      intervalDomainMSectorialStabilityNorms eq.1 eq.2 := by
  let eq := positiveEquilibrium p ⟨ha, hb⟩
  have heq : Paper3ConstantEquilibrium p eq.1 eq.2 := by
    simpa [eq] using paper3ConstantEquilibrium_positive p ha hb
  have hcond : NonminimalGlobalStabilityFormulaCondition p eq.1 eq.2 0 :=
    Or.inl ⟨hmge, hrel, hχpos, by simpa [eq] using hχ⟩
  have hstable : LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 := by
    simpa [eq] using hcond.linearlyStable_unitInterval p ha hb
  have hproduce : ∀ u v : ℝ → intervalDomainPoint → ℝ,
      PositiveGlobalBoundedSolution intervalDomainM p u v →
      ∃ C > 0, ∃ rate > 0, ∃ t₀ > 0,
        EventualExponentialC1ConvergenceWith intervalDomainM
          intervalDomainMSectorialStabilityNorms u v eq.1 eq.2 C rate t₀ := by
    intro u v huv
    exact intervalDomainM_strongM_eventualC1 p hmge ha hb heq hrel hχpos
      (by simpa [eq] using hχ) hstable huv
  refine ⟨?_, hproduce⟩
  intro u v huv
  obtain ⟨C, hC, rate, hrate, t₀, ht₀, hbound⟩ := hproduce u v huv
  exact intervalDomainM_uniformConvergesInSup_of_eventualExponentialC1
    hrate hbound

#print axioms intervalDomainM_thm24_weakSupOrbitBound
#print axioms intervalDomainM_eventualC1_of_lateSupClose
#print axioms intervalDomainM_strongM_eventualC1
#print axioms intervalDomainM_uniformConvergesInSup_of_eventualExponentialC1
#print axioms
  intervalDomainM_eventuallyGloballyExponentiallyStableNonminimal_strong1

end

end ShenWork.Paper3
