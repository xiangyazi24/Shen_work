import ShenWork.Paper3.IntervalDomainEntropyStrong1BasinEntry
import ShenWork.Paper3.EventualGlobalStability

/-!
# Unconditional first-branch global stability on the unit interval

This file consumes one entropy-produced basin-entry slice, restarts the proved
weak-sup Stage B theorem there, and derives both eventual `C¹` exponential
decay and qualitative uniform attraction.  The implemented PDE scope is
explicitly `m = 1`.
-/

namespace ShenWork.Paper3

open Filter Topology Set
open ShenWork.IntervalDomain ShenWork.Paper2

noncomputable section

/-- The concrete interval supremum norm is nonnegative, without a separate
boundedness premise. -/
theorem intervalDomain_supNorm_nonneg
    (f : intervalDomainPoint → ℝ) :
    0 ≤ intervalDomain.supNorm f := by
  unfold intervalDomain intervalDomainSupNorm
  apply Real.sSup_nonneg
  intro y hy
  rcases hy with ⟨x, rfl⟩
  exact abs_nonneg _

/-- An eventual exponential bound in the concrete physical `C¹` gauge implies
uniform convergence of the `u` component in the primitive sup norm. -/
theorem intervalDomain_uniformConvergesInSup_of_eventualExponentialC1
    {u v : ℝ → intervalDomainPoint → ℝ}
    {uStar vStar C rate t₀ : ℝ}
    (hrate : 0 < rate)
    (hbound : EventualExponentialC1ConvergenceWith
      intervalDomain intervalDomainSectorialStabilityNorms
        u v uStar vStar C rate t₀) :
    UniformConvergesInSup intervalDomain u uStar := by
  have hnonneg : ∀ᶠ t : ℝ in atTop,
      0 ≤ intervalDomain.supNorm (fun x => u t x - uStar) :=
    Filter.Eventually.of_forall fun t => intervalDomain_supNorm_nonneg _
  have hupper : ∀ᶠ t : ℝ in atTop,
      intervalDomain.supNorm (fun x => u t x - uStar) ≤
        C * Real.exp (-rate * t) := by
    filter_upwards [eventually_ge_atTop t₀] with t ht
    have hb := hbound t ht
    simp only [intervalDomainSectorialStabilityNorms_c1Distance] at hb
    unfold intervalDomainSectorialC1Distance at hb
    have huGrad : 0 ≤ intervalDomain.supNorm
        (fun x => intervalDomain.gradNorm (fun y => u t y - uStar) x) :=
      intervalDomain_supNorm_nonneg _
    have hvValue : 0 ≤ intervalDomain.supNorm (fun x => v t x - vStar) :=
      intervalDomain_supNorm_nonneg _
    have hvGrad : 0 ≤ intervalDomain.supNorm
        (fun x => intervalDomain.gradNorm (fun y => v t y - vStar) x) :=
      intervalDomain_supNorm_nonneg _
    linarith
  have hmul : Tendsto (fun t : ℝ => rate * t) atTop atTop :=
    (Filter.tendsto_id.atTop_mul_const hrate).congr
      (fun t => mul_comm t rate)
  have hneg : Tendsto (fun t : ℝ => -(rate * t)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hmul
  have hexp : Tendsto (fun t : ℝ => Real.exp (-(rate * t))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hneg
  have hright : Tendsto
      (fun t : ℝ => C * Real.exp (-rate * t)) atTop (𝓝 0) := by
    convert tendsto_const_nhds.mul hexp using 1
    · ext t
      ring_nf
    · simp
  exact squeeze_zero' hnonneg hupper hright

/-- Restart Stage B from one already-close positive classical slice. -/
theorem intervalDomain_eventualC1_of_supCloseSlice_of_linearlyStable
    (p : CM2Params) (hm : p.m = 1)
    {uStar vStar : ℝ}
    (ha : 0 < p.a)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hstable : LinearlyStable unitIntervalNeumannSpectrum p uStar vStar)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    {tau : ℝ} (htau : 0 < tau)
    (hclose :
      let orbit := intervalDomain_weakSupEventualSpectralSemigroupOrbitBound p hm
      let witness := orbit.2 uStar vStar ha heq hstable
      let delta := Classical.choose witness
      SupCloseToConstant intervalDomain (u tau) uStar delta) :
    ∃ C > 0, ∃ rate > 0, ∃ t₀ > 0,
      EventualExponentialC1ConvergenceWith
        intervalDomain intervalDomainSectorialStabilityNorms
          u v uStar vStar C rate t₀ := by
  let orbit := intervalDomain_weakSupEventualSpectralSemigroupOrbitBound p hm
  let witness := orbit.2 uStar vStar ha heq hstable
  let delta : ℝ := Classical.choose witness
  have hspec := Classical.choose_spec witness
  rcases hspec with
    ⟨hdelta, C, hC, rate, hrate, delay, hdelay, hbound⟩
  change SupCloseToConstant intervalDomain (u tau) uStar delta at hclose
  have hpid := intervalDomain_globalClassicalSolution_slice_positiveInitialDatum
    huv.classical htau
  let us : ℝ → intervalDomainPoint → ℝ := fun t x => u (t + tau) x
  let vs : ℝ → intervalDomainPoint → ℝ := fun t x => v (t + tau) x
  have hshiftGlobal : IsPaper2GlobalClassicalSolution intervalDomain p us vs := by
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
  have hCshift : 0 < Cshift := mul_pos hC (Real.exp_pos _)
  have ht₀ : 0 < t₀ := by dsimp [t₀]; linarith
  refine ⟨Cshift, hCshift, rate, hrate, t₀, ht₀, ?_⟩
  intro t htt₀
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

/-- Entropy basin entry followed by the proved weak-sup Stage B theorem. -/
theorem intervalDomain_strong1_eventualC1
    (p : CM2Params) (hm : p.m = 1)
    {uStar vStar : ℝ}
    (ha : 0 < p.a) (hb : 0 < p.b)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hrel : 2 * p.γ ≤ p.α + 1)
    (hχpos : 0 < p.χ₀)
    (hχ : p.χ₀ < chiStrong1Formula p uStar vStar)
    (hstable : LinearlyStable unitIntervalNeumannSpectrum p uStar vStar)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v) :
    ∃ C > 0, ∃ rate > 0, ∃ t₀ > 0,
      EventualExponentialC1ConvergenceWith
        intervalDomain intervalDomainSectorialStabilityNorms
          u v uStar vStar C rate t₀ := by
  have horbit := intervalDomain_weakSupEventualSpectralSemigroupOrbitBound p hm
  let witness := horbit.2 uStar vStar ha heq hstable
  let delta : ℝ := Classical.choose witness
  have hdelta : 0 < delta := (Classical.choose_spec witness).1
  obtain ⟨tau, htauOne, hclose⟩ :=
    intervalDomain_strong1_exists_late_supClose
      p hm hb heq hrel hχpos hχ huv (T := (1 : ℝ)) hdelta
  have htau : 0 < tau := lt_of_lt_of_le zero_lt_one htauOne
  exact intervalDomain_eventualC1_of_supCloseSlice_of_linearlyStable
    p hm ha heq hstable huv htau (by simpa [witness, delta] using hclose)

/-- Unconditional first formula branch of faithful eventual Theorem 2.4 on
the currently implemented `m = 1` unit-interval equation. -/
theorem
    intervalDomain_eventuallyGloballyExponentiallyStableNonminimal_strong1
    (p : CM2Params) (hm : p.m = 1)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hrel : 2 * p.γ ≤ p.α + 1)
    (hχpos : 0 < p.χ₀)
    (hχ : p.χ₀ < chiStrong1Formula p
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    EventuallyGloballyExponentiallyStableNonminimal intervalDomain p
      intervalDomainSectorialStabilityNorms eq.1 eq.2 := by
  let eq := positiveEquilibrium p ⟨ha, hb⟩
  have heq : Paper3ConstantEquilibrium p eq.1 eq.2 := by
    simpa [eq] using paper3ConstantEquilibrium_positive p ha hb
  have hmge : 1 ≤ p.m := by rw [hm]
  have hcond : NonminimalGlobalStabilityFormulaCondition p eq.1 eq.2 0 :=
    Or.inl ⟨hmge, hrel, hχpos, by simpa [eq] using hχ⟩
  have hstable : LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 := by
    simpa [eq] using hcond.linearlyStable_unitInterval p ha hb
  have hproduce : ∀ u v : ℝ → intervalDomainPoint → ℝ,
      PositiveGlobalBoundedSolution intervalDomain p u v →
      ∃ C > 0, ∃ rate > 0, ∃ t₀ > 0,
        EventualExponentialC1ConvergenceWith intervalDomain
          intervalDomainSectorialStabilityNorms u v eq.1 eq.2 C rate t₀ := by
    intro u v huv
    exact intervalDomain_strong1_eventualC1 p hm ha hb heq hrel hχpos
      (by simpa [eq] using hχ) hstable huv
  refine ⟨?_, hproduce⟩
  intro u v huv
  obtain ⟨C, hC, rate, hrate, t₀, ht₀, hbound⟩ := hproduce u v huv
  exact intervalDomain_uniformConvergesInSup_of_eventualExponentialC1
    hrate hbound

#print axioms intervalDomain_supNorm_nonneg
#print axioms intervalDomain_uniformConvergesInSup_of_eventualExponentialC1
#print axioms intervalDomain_eventualC1_of_supCloseSlice_of_linearlyStable
#print axioms intervalDomain_strong1_eventualC1
#print axioms
  intervalDomain_eventuallyGloballyExponentiallyStableNonminimal_strong1

end

end ShenWork.Paper3
