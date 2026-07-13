/- Eventual exponential upgrade for an already existing positive global orbit. -/
import ShenWork.Paper3.IntervalDomainWeakSupStageB
import ShenWork.Paper2.IntervalDomainGlueExtension

namespace ShenWork.Paper3

open Filter Topology Set
open ShenWork.IntervalDomain
open ShenWork.Paper2

noncomputable section

/-- A positive time translate of a global interval solution is again global. -/
theorem intervalDomain_globalClassicalSolution_timeShift
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ}
    (hglobal :
      IsPaper2GlobalClassicalSolution intervalDomain p u v)
    {tau : ℝ} (htau : 0 < tau) :
    IsPaper2GlobalClassicalSolution intervalDomain p
      (fun t x => u (t + tau) x) (fun t x => v (t + tau) x) := by
  intro T hT
  have hsum : 0 < T + tau := by linarith
  have hsol := hglobal (T + tau) hsum
  have hshift := TimeShift.classicalSolution_timeShift
    TimeShift.regularityTimeShiftWorks hsol htau (by linarith)
  simpa only [add_sub_cancel_right] using hshift

/-- The translated global orbit has the original positive slice as initial
trace. -/
theorem intervalDomain_globalClassicalSolution_timeShift_initialTrace
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ}
    (hglobal :
      IsPaper2GlobalClassicalSolution intervalDomain p u v)
    {tau : ℝ} (htau : 0 < tau) :
    InitialTrace intervalDomain (u tau)
      (fun t x => u (t + tau) x) := by
  let T := tau + 1
  have hT : 0 < T := by dsimp [T]; linarith
  have htauT : tau < T := by dsimp [T]; linarith
  exact GlueExtension.timeShiftInitialTraceWorks
    (hglobal T hT) htau htauT

/-- A strictly positive classical slice is an admissible positive datum. -/
theorem intervalDomain_globalClassicalSolution_slice_positiveInitialDatum
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ}
    (hglobal :
      IsPaper2GlobalClassicalSolution intervalDomain p u v)
    {tau : ℝ} (htau : 0 < tau) :
    PositiveInitialDatum intervalDomain (u tau) := by
  let T := tau + 1
  have hT : 0 < T := by dsimp [T]; linarith
  have htauT : tau < T := by dsimp [T]; linarith
  exact UniformContinuation.classicalSolution_slice_positiveInitialDatum
    (hglobal T hT) ⟨htau, htauT⟩

/-- Stage B upgrades uniform sup convergence of any positive bounded global
orbit to eventual exponential convergence in the concrete physical `C¹`
gauge.  The orbit is restarted at a late slice already inside the weak basin;
the public orbit theorem applies to that very translated solution, so no
uniqueness substitution is needed. -/
theorem intervalDomain_eventualC1_of_uniformSup_of_linearlyStable
    (p : CM2Params) (hm : p.m = 1)
    {uStar vStar : ℝ}
    (ha : 0 < p.a)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hstable :
      LinearlyStable unitIntervalNeumannSpectrum p uStar vStar)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hconv : UniformConvergesInSup intervalDomain u uStar) :
    ∃ C > 0, ∃ rate > 0, ∃ t₀ > 0,
      EventualExponentialC1ConvergenceWith
        intervalDomain intervalDomainSectorialStabilityNorms
          u v uStar vStar C rate t₀ := by
  have horbit :=
    intervalDomain_weakSupEventualSpectralSemigroupOrbitBound p hm
  rcases horbit.2 uStar vStar ha heq hstable with
    ⟨delta, hdelta, C, hC, rate, hrate, delay, hdelay, hbound⟩
  have hevent :
      ∀ᶠ t : ℝ in atTop,
        intervalDomain.supNorm (fun x => u t x - uStar) < delta :=
    hconv.eventually (Iio_mem_nhds hdelta)
  rcases eventually_atTop.1 hevent with ⟨threshold, hthreshold⟩
  let tau : ℝ := max threshold 1
  have htau : 0 < tau := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
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
  have hshiftBound := hbound (u tau) hpid hclose us vs
    hshiftGlobal hshiftTrace
  let Cshift : ℝ := C * Real.exp (rate * tau)
  let t₀ : ℝ := tau + delay
  have hCshift : 0 < Cshift :=
    mul_pos hC (Real.exp_pos _)
  have ht₀ : 0 < t₀ := by dsimp [t₀]; linarith
  refine ⟨Cshift, hCshift, rate, hrate, t₀, ht₀, ?_⟩
  intro t htt₀
  let s : ℝ := t - tau
  have hdelayS : delay ≤ s := by dsimp [s, t₀] at *; linarith
  have hsEq : s + tau = t := by dsimp [s]; ring
  have hdecay := hshiftBound s hdelayS
  have hexpShift :
      Real.exp (-rate * s) =
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

/-- Exact critical-spectrum form of the positive global-orbit upgrade.  This
is the eventual nonlinear input used by the positive branches of Paper3
Theorems 2.3 and 2.4. -/
theorem intervalDomain_positiveEquilibrium_eventualC1_of_uniformSup
    (p : CM2Params) (hm : p.m = 1)
    (Cpaper : Paper3Constants intervalDomain p)
    (hCpaper :
      Paper3ConstantsUsesCriticalSpectrum
        unitIntervalNeumannSpectrum p Cpaper)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hchi :
      p.χ₀ < Cpaper.chiCritical
        (positiveEquilibrium p ⟨ha, hb⟩).1)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hconv : UniformConvergesInSup intervalDomain u
      (positiveEquilibrium p ⟨ha, hb⟩).1) :
    ∃ C > 0, ∃ rate > 0, ∃ t₀ > 0,
      EventualExponentialC1ConvergenceWith
        intervalDomain intervalDomainSectorialStabilityNorms u v
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2 C rate t₀ := by
  have hstable := hCpaper.positiveEquilibrium_linearlyStable
    unitIntervalNeumannSpectrum_hasNeumannSpectrum ha hb hchi
  exact intervalDomain_eventualC1_of_uniformSup_of_linearlyStable
    p hm ha (paper3ConstantEquilibrium_positive p ha hb)
      hstable huv hconv

#print axioms intervalDomain_globalClassicalSolution_timeShift
#print axioms intervalDomain_globalClassicalSolution_timeShift_initialTrace
#print axioms intervalDomain_eventualC1_of_uniformSup_of_linearlyStable
#print axioms intervalDomain_positiveEquilibrium_eventualC1_of_uniformSup

end

end ShenWork.Paper3
