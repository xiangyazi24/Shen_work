/- Eventual exponential upgrade on the physical-mass minimal-model branch. -/
import ShenWork.Paper3.IntervalDomainMinimalWeakSupBasinEntry
import ShenWork.Paper3.IntervalDomainMinimalStrongBootstrap
import ShenWork.Paper3.IntervalDomainEventualConvergenceUpgrade

namespace ShenWork.Paper3

open Filter Topology Set
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.PDE
open ShenWork.PDE.SectorialOperator

noncomputable section

local instance : TopologicalSpace intervalDomain.Point :=
  inferInstanceAs (TopologicalSpace intervalDomainPoint)

/-- Positive-time physical mass is preserved when a global orbit is shifted
by a positive time. -/
theorem hasEquilibriumMassOnPositiveTimes_timeShift
    {u : ℝ → intervalDomainPoint → ℝ} {uStar tau : ℝ}
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomain u uStar)
    (htau : 0 < tau) :
    HasEquilibriumMassOnPositiveTimes intervalDomain
      (fun t x => u (t + tau) x) uStar := by
  intro t ht
  exact hmass (t + tau) (by linarith)

/-- A uniformly convergent bounded minimal-model orbit on the physical-mass
hyperplane eventually enters the strong basin and then decays exponentially
in the concrete physical `C¹` gauge.  The zero mode is removed only through
the stated physical-mass hypothesis. -/
theorem intervalDomain_minimal_eventualC1_of_uniformSup_of_massGap
    (p : CM2Params) (hm : p.m = 1) (ha0 : p.a = 0) (hb0 : p.b = 0)
    {uStar vStar gap : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearMassSpectralGap p uStar vStar gap)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomain u uStar)
    (hconv : UniformConvergesInSup intervalDomain u uStar) :
    ∃ C > 0, ∃ rate > 0, ∃ t₀ > 0,
      EventualExponentialC1ConvergenceWith
        intervalDomain intervalDomainSectorialStabilityNorms
          u v uStar vStar C rate t₀ := by
  let sigma : ℝ := 7 / 8
  have hsigmaStrong : 3 / 4 < sigma := by
    norm_num [sigma]
  have hsigma1 : sigma < 1 := by
    norm_num [sigma]
  rcases intervalDomainMassSupToStrongBasinEntry_proved
      p hsigmaStrong hsigma1 hm ha0 hb0 heq hgap with
    ⟨delta, hdelta, T, hT, henter⟩
  have hevent :
      ∀ᶠ t : ℝ in atTop,
        intervalDomain.supNorm (fun x => u t x - uStar) < delta :=
    hconv.eventually (Iio_mem_nhds hdelta)
  rcases eventually_atTop.1 hevent with ⟨threshold, hthreshold⟩
  let tau : ℝ := max threshold 1
  have htau : 0 < tau :=
    lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hthresholdTau : threshold ≤ tau := le_max_left _ _
  have hclose : SupCloseToConstant intervalDomain (u tau) uStar delta :=
    hthreshold tau hthresholdTau
  have hpid :=
    intervalDomain_globalClassicalSolution_slice_positiveInitialDatum
      huv.classical htau
  let us : ℝ → intervalDomainPoint → ℝ := fun t x => u (t + tau) x
  let vs : ℝ → intervalDomainPoint → ℝ := fun t x => v (t + tau) x
  have hshiftGlobal :
      IsPaper2GlobalClassicalSolution intervalDomain p us vs := by
    simpa [us, vs] using
      intervalDomain_globalClassicalSolution_timeShift huv.classical htau
  have hshiftTrace : InitialTrace intervalDomain (u tau) us := by
    simpa [us] using
      intervalDomain_globalClassicalSolution_timeShift_initialTrace
        huv.classical htau
  have hshiftMass :
      HasEquilibriumMassOnPositiveTimes intervalDomain us uStar := by
    simpa [us] using
      hasEquilibriumMassOnPositiveTimes_timeShift hmass htau
  have hentry := henter (u tau) hpid hclose us vs
    hshiftGlobal hshiftTrace hshiftMass
  let R : ℝ := intervalDomainStrongBootstrapRadius
    p sigma uStar vStar gap heq
  let rate : ℝ := gap / 4
  let t₀ : ℝ := T + tau
  let Cu : ℝ := intervalDomainX2SigmaValueTrace sigma +
    intervalDomainX2SigmaDerivativeTrace sigma
  let Cv : ℝ := 4 * paper3UniformSignalStrongConstant p uStar heq.u_pos *
    intervalDomainX2SigmaC1Envelope sigma
  let C : ℝ := (1 + Cu + Cv) * R * Real.exp (rate * t₀)
  have hR : 0 < R := by
    simpa [R] using intervalDomainStrongBootstrapRadius_pos
      p heq hgap.1 (by norm_num [sigma] : 0 < sigma) hsigma1
  have hrate : 0 < rate := by
    dsimp [rate]
    linarith [hgap.1]
  have ht₀ : 0 < t₀ := by dsimp [t₀]; linarith
  have hCu : 0 ≤ Cu := by
    dsimp [Cu]
    exact add_nonneg (intervalDomainX2SigmaValueTrace_nonneg sigma)
      (intervalDomainX2SigmaDerivativeTrace_nonneg sigma)
  have hCv : 0 ≤ Cv := by
    dsimp [Cv]
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (paper3UniformSignalStrongConstant_pos p uStar heq.u_pos).le)
      (intervalDomainX2SigmaC1Envelope_pos sigma).le
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (mul_pos (by linarith) hR) (Real.exp_pos _)
  have hdecay := intervalDomainMassX2SigmaDistance_restart_exponential_bound
    hshiftGlobal hm ha0 hb0 hT heq hgap hsigmaStrong hsigma1
      hshiftMass hentry.2
  refine ⟨C, hC, rate, hrate, t₀, ht₀, ?_⟩
  intro t htt₀
  let r : ℝ := t - t₀
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have htpos : 0 < t := lt_of_lt_of_le ht₀ htt₀
  have htime : T + r + tau = t := by
    dsimp [r, t₀]
    ring
  have hdist : intervalDomainX2SigmaDistance sigma uStar (u t) ≤
      R * Real.exp (-rate * r) := by
    simpa [us, R, rate, htime] using hdecay r hr
  let H : ℝ := t + 1
  have hH : 0 < H := by dsimp [H]; linarith
  have htH : t < H := by dsimp [H]; linarith
  let hsol := huv.classical H hH
  have htmem : t ∈ Set.Ioo (0 : ℝ) H := ⟨htpos, htH⟩
  have hmem : IntervalDomainX2SigmaPerturbation sigma uStar (u t) :=
    intervalDomainX2SigmaPerturbation_of_classical_positive
      hsol htmem hsigma1.le
  have hsolM := isPaper2ClassicalSolution_intervalDomainM_of_m_eq_one
    p hm hsol
  have hcont : Continuous (u t) :=
    ShenWork.Paper2.IntervalDomainM.solutionSlice_continuous hsolM htmem
  have Hreal : IntervalDomainX2SigmaRealizationBounds sigma uStar (u t) :=
    intervalDomainX2SigmaRealizationBounds_of_continuous
      hsigmaStrong hcont hmem
  have hexple : Real.exp (-rate * r) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    nlinarith [hrate.le, hr]
  have hdistR : intervalDomainX2SigmaDistance sigma uStar (u t) ≤ R := by
    calc
      intervalDomainX2SigmaDistance sigma uStar (u t) ≤
          R * Real.exp (-rate * r) := hdist
      _ ≤ R * 1 := mul_le_mul_of_nonneg_left hexple hR.le
      _ = R := mul_one R
  have hlocal : intervalDomainX2SigmaDistance sigma uStar (u t) ≤
      intervalDomainX2SigmaLocalNemytskiiRadius sigma uStar :=
    hdistR.trans (intervalDomainStrongBootstrapRadius_le_positivity
      p sigma uStar vStar gap heq)
  have huC1 := Hreal.c1Distance_le
  have hvC1 := intervalDomainSignal_c1Distance_le_X2Sigma
    hsol htmem heq Hreal hlocal
  have hsumC1 :
      intervalDomainSectorialC1Distance (u t) (fun _ => uStar) +
          intervalDomainSectorialC1Distance (v t) (fun _ => vStar) ≤
        (Cu + Cv) * intervalDomainX2SigmaDistance sigma uStar (u t) := by
    calc
      _ ≤ Cu * intervalDomainX2SigmaDistance sigma uStar (u t) +
          Cv * intervalDomainX2SigmaDistance sigma uStar (u t) := by
        exact add_le_add (by simpa [Cu] using huC1)
          (by simpa [Cv] using hvC1)
      _ = _ := by ring
  have hexpShift :
      Real.exp (-rate * r) =
        Real.exp (rate * t₀) * Real.exp (-rate * t) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [r]
    ring
  calc
    intervalDomainSectorialC1Distance (u t) (fun _ => uStar) +
        intervalDomainSectorialC1Distance (v t) (fun _ => vStar) ≤
      (Cu + Cv) * intervalDomainX2SigmaDistance sigma uStar (u t) := hsumC1
    _ ≤ (Cu + Cv) * (R * Real.exp (-rate * r)) :=
      mul_le_mul_of_nonneg_left hdist (add_nonneg hCu hCv)
    _ ≤ C * Real.exp (-rate * t) := by
      rw [hexpShift]
      dsimp [C]
      have he0 : 0 ≤ Real.exp (rate * t₀) := (Real.exp_pos _).le
      have het0 : 0 ≤ Real.exp (-rate * t) := (Real.exp_pos _).le
      nlinarith [mul_nonneg hR.le (mul_nonneg he0 het0)]

#print axioms hasEquilibriumMassOnPositiveTimes_timeShift
#print axioms intervalDomain_minimal_eventualC1_of_uniformSup_of_massGap

end

end ShenWork.Paper3
