/- Weak-sup basin entry followed by the closed strong-space stability theorem. -/
import ShenWork.Paper3.IntervalDomainStrongStageA

namespace ShenWork.Paper3

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.PDE
open ShenWork.PDE.SectorialOperator

noncomputable section

local instance intervalDomainStrongStageBPointTopology :
    TopologicalSpace intervalDomain.Point :=
  inferInstanceAs (TopologicalSpace intervalDomainPoint)

/-- The precise local-parabolic input for Stage B.

For weak initial data the delay is uniform over the sup-norm ball and over all
global classical realizations with that initial trace.  At that delay the
orbit has entered half of the explicit strong bootstrap radius.  Positivity of
the scalar powers is therefore inherited from the strong radius rather than
silently assumed in the subsequent Nemytskii estimate. -/
def IntervalDomainSupToStrongBasinEntry (p : CM2Params) : Prop :=
  ∀ sigma uStar vStar gap,
    3 / 4 < sigma → sigma < 1 →
    p.m = 1 →
    ∀ (heq : Paper3ConstantEquilibrium p uStar vStar),
    UnitIntervalLinearSpectralGap p uStar vStar gap →
      ∃ delta > 0, ∃ t₀ > 0,
        ∀ u₀ : intervalDomainPoint → ℝ,
          PositiveInitialDatum intervalDomain u₀ →
          SupCloseToConstant intervalDomain u₀ uStar delta →
          ∀ u v : ℝ → intervalDomainPoint → ℝ,
            IsPaper2GlobalClassicalSolution intervalDomain p u v →
            InitialTrace intervalDomain u₀ u →
              IntervalDomainX2SigmaPerturbation sigma uStar (u t₀) ∧
              intervalDomainX2SigmaDistance sigma uStar (u t₀) ≤
                intervalDomainStrongBootstrapRadius
                  p sigma uStar vStar gap heq / 2

/-- Stage B after basin entry: weak sup-small data converge exponentially in
the concrete physical `C¹` gauge after the uniform entry time.

Every Fourier mode is governed by the full linearized gap used in
`UnitIntervalLinearSpectralGap`; in particular no zero-mode projection occurs.
The time translation is absorbed into the prefactor
`exp ((gap/4) * t₀)`. -/
theorem intervalDomain_weakSupEventualSpectralSemigroupOrbitBound_of_basinEntry
    (p : CM2Params) (hm : p.m = 1)
    (hentry : IntervalDomainSupToStrongBasinEntry p) :
    IntervalDomainWeakSupEventualSpectralSemigroupOrbitBound p := by
  refine ⟨hm, ?_⟩
  intro uStar vStar ha heq hstable
  rcases unitIntervalLinearSpectralGap_of_linearlyStable_of_a_pos
      p heq hstable ha with ⟨gap, hgap0, hgap⟩
  let sigma : ℝ := 7 / 8
  have hsigmaStrong : 3 / 4 < sigma := by
    norm_num [sigma]
  have hsigma1 : sigma < 1 := by
    norm_num [sigma]
  rcases hentry sigma uStar vStar gap hsigmaStrong hsigma1 hm heq hgap with
    ⟨delta, hdelta, t₀, ht₀, henter⟩
  let R : ℝ := intervalDomainStrongBootstrapRadius
    p sigma uStar vStar gap heq
  let rate : ℝ := gap / 4
  let Cu : ℝ := intervalDomainX2SigmaValueTrace sigma +
    intervalDomainX2SigmaDerivativeTrace sigma
  let Cv : ℝ := 4 * paper3UniformSignalStrongConstant p uStar heq.u_pos *
    intervalDomainX2SigmaC1Envelope sigma
  let C : ℝ := (1 + Cu + Cv) * R * Real.exp (rate * t₀)
  have hR : 0 < R := by
    simpa [R] using intervalDomainStrongBootstrapRadius_pos
      p heq hgap0 (by norm_num [sigma] : 0 < sigma) hsigma1
  have hrate : 0 < rate := by
    dsimp [rate]
    linarith
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
  refine ⟨delta, hdelta, C, hC, rate, hrate, t₀, ht₀, ?_⟩
  intro u₀ hu₀ hclose u v hglobal htrace
  rcases henter u₀ hu₀ hclose u v hglobal htrace with
    ⟨_hmemEntry, hdistEntry⟩
  have hdecay := intervalDomainX2SigmaDistance_restart_exponential_bound
    hglobal hm ht₀ heq hgap hsigmaStrong hsigma1 hdistEntry
  intro t htt₀
  let tau : ℝ := t - t₀
  have htau : 0 ≤ tau := by
    dsimp [tau]
    linarith
  have htpos : 0 < t := lt_of_lt_of_le ht₀ htt₀
  have htEq : t₀ + tau = t := by
    dsimp [tau]
    ring
  have hdist : intervalDomainX2SigmaDistance sigma uStar (u t) ≤
      R * Real.exp (-rate * tau) := by
    simpa [R, rate, htEq] using hdecay tau htau
  let T : ℝ := t + 1
  have hT : 0 < T := by
    dsimp [T]
    linarith
  have htT : t < T := by
    dsimp [T]
    linarith
  let hsol := hglobal T hT
  have htmem : t ∈ Set.Ioo (0 : ℝ) T := ⟨htpos, htT⟩
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
  have hexple : Real.exp (-rate * tau) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    nlinarith [hrate.le, htau]
  have hdistR : intervalDomainX2SigmaDistance sigma uStar (u t) ≤ R := by
    calc
      intervalDomainX2SigmaDistance sigma uStar (u t) ≤
          R * Real.exp (-rate * tau) := hdist
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
      Real.exp (-rate * tau) =
        Real.exp (rate * t₀) * Real.exp (-rate * t) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [tau]
    ring
  calc
    intervalDomainSectorialC1Distance (u t) (fun _ => uStar) +
        intervalDomainSectorialC1Distance (v t) (fun _ => vStar) ≤
      (Cu + Cv) * intervalDomainX2SigmaDistance sigma uStar (u t) := hsumC1
    _ ≤ (Cu + Cv) * (R * Real.exp (-rate * tau)) :=
      mul_le_mul_of_nonneg_left hdist (add_nonneg hCu hCv)
    _ ≤ C * Real.exp (-rate * t) := by
      rw [hexpShift]
      dsimp [C]
      have he0 : 0 ≤ Real.exp (rate * t₀) := (Real.exp_pos _).le
      have het0 : 0 ≤ Real.exp (-rate * t) := (Real.exp_pos _).le
      nlinarith [mul_nonneg hR.le (mul_nonneg he0 het0)]

#print axioms IntervalDomainSupToStrongBasinEntry
#print axioms intervalDomain_weakSupEventualSpectralSemigroupOrbitBound_of_basinEntry

end

end ShenWork.Paper3
