/- Faithful general-`m` Stage B after weak-sup basin entry. -/
import ShenWork.Paper3.IntervalDomainStrongStageAGeneralM
import ShenWork.Paper3.IntervalDomainMSectorial

namespace ShenWork.Paper3

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.PDE
open ShenWork.PDE.SectorialOperator

noncomputable section

/-- Uniform entry from the physical sup ball into the faithful general-`m`
strong bootstrap ball. -/
def IntervalDomainMSupToStrongBasinEntry (p : CM2Params) : Prop :=
  ∀ sigma uStar vStar gap,
    3 / 4 < sigma → sigma < 1 →
    ∀ (heq : Paper3ConstantEquilibrium p uStar vStar),
    UnitIntervalLinearSpectralGap p uStar vStar gap →
      ∃ delta > 0, ∃ t₀ > 0,
        ∀ u₀ : intervalDomainPoint → ℝ,
          PositiveInitialDatum intervalDomainM u₀ →
          SupCloseToConstant intervalDomainM u₀ uStar delta →
          ∀ u v : ℝ → intervalDomainPoint → ℝ,
            IsPaper2GlobalClassicalSolution intervalDomainM p u v →
            InitialTrace intervalDomainM u₀ u →
              IntervalDomainX2SigmaPerturbation sigma uStar (u t₀) ∧
              intervalDomainX2SigmaDistance sigma uStar (u t₀) ≤
                intervalDomainStrongBootstrapRadiusGeneralM
                  p sigma uStar vStar gap heq / 2

/-- Faithful weak-data orbit interface.  The equation, datum, and trace all
use `intervalDomainM`; unlike the legacy bundle it carries no `p.m = 1`
specialization. -/
def IntervalDomainMWeakSupEventualSpectralSemigroupOrbitBound
    (p : CM2Params) : Prop :=
  ∀ uStar vStar,
    0 < p.a →
    Paper3ConstantEquilibrium p uStar vStar →
    LinearlyStable unitIntervalNeumannSpectrum p uStar vStar →
      ∃ delta > 0, ∃ C > 0, ∃ rate > 0, ∃ t₀ > 0,
        ∀ u₀ : intervalDomainPoint → ℝ,
          PositiveInitialDatum intervalDomainM u₀ →
          SupCloseToConstant intervalDomainM u₀ uStar delta →
          ∀ u v : ℝ → intervalDomainPoint → ℝ,
            IsPaper2GlobalClassicalSolution intervalDomainM p u v →
            InitialTrace intervalDomainM u₀ u →
              ∀ t, t₀ ≤ t →
                intervalDomainSectorialC1Distance
                    (u t) (fun _ => uStar) +
                  intervalDomainSectorialC1Distance
                    (v t) (fun _ => vStar) ≤
                    C * Real.exp (-rate * t)

/-- Once weak data enter the faithful strong ball, the closed general-`m`
Stage-A estimate yields eventual exponential `C¹` decay. -/
theorem
intervalDomainM_weakSupEventualSpectralSemigroupOrbitBound_of_basinEntry
    (p : CM2Params)
    (hentry : IntervalDomainMSupToStrongBasinEntry p) :
    IntervalDomainMWeakSupEventualSpectralSemigroupOrbitBound p := by
  intro uStar vStar ha heq hstable
  rcases unitIntervalLinearSpectralGap_of_linearlyStable_of_a_pos
      p heq hstable ha with ⟨gap, hgap0, hgap⟩
  let sigma : ℝ := 7 / 8
  have hsigmaStrong : 3 / 4 < sigma := by norm_num [sigma]
  have hsigma1 : sigma < 1 := by norm_num [sigma]
  rcases hentry sigma uStar vStar gap hsigmaStrong hsigma1 heq hgap with
    ⟨delta, hdelta, t₀, ht₀, henter⟩
  let R : ℝ := intervalDomainStrongBootstrapRadiusGeneralM
    p sigma uStar vStar gap heq
  let rate : ℝ := gap / 4
  let Cu : ℝ := intervalDomainX2SigmaValueTrace sigma +
    intervalDomainX2SigmaDerivativeTrace sigma
  let Cv : ℝ := 4 * paper3UniformSignalStrongConstant p uStar heq.u_pos *
    intervalDomainX2SigmaC1Envelope sigma
  let C : ℝ := (1 + Cu + Cv) * R * Real.exp (rate * t₀)
  have hR : 0 < R := by
    simpa [R] using intervalDomainStrongBootstrapRadiusGeneralM_pos
      p heq hgap0 (by norm_num [sigma] : 0 < sigma) hsigma1
  have hrate : 0 < rate := by dsimp [rate]; linarith
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
  have hdecay := intervalDomainX2SigmaDistance_restart_exponential_bound_generalM
    hglobal ht₀ heq hgap hsigmaStrong hsigma1 hdistEntry
  intro t htt₀
  let tau : ℝ := t - t₀
  have htau : 0 ≤ tau := by dsimp [tau]; linarith
  have htpos : 0 < t := lt_of_lt_of_le ht₀ htt₀
  have htEq : t₀ + tau = t := by dsimp [tau]; ring
  have hdist : intervalDomainX2SigmaDistance sigma uStar (u t) ≤
      R * Real.exp (-rate * tau) := by
    simpa [R, rate, htEq] using hdecay tau htau
  let T : ℝ := t + 1
  have hT : 0 < T := by dsimp [T]; linarith
  have htT : t < T := by dsimp [T]; linarith
  let hsol := hglobal T hT
  have htmem : t ∈ Set.Ioo (0 : ℝ) T := ⟨htpos, htT⟩
  have hmem : IntervalDomainX2SigmaPerturbation sigma uStar (u t) :=
    intervalDomainMX2SigmaPerturbation_of_classical_positive
      hsol htmem hsigma1.le
  have hcont : Continuous (u t) := solutionSlice_continuous hsol htmem
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
      intervalDomainX2SigmaLocalNemytskiiRadiusGeneralM p sigma uStar :=
    hdistR.trans (intervalDomainStrongBootstrapRadiusGeneralM_le_positivity
      p sigma uStar vStar gap heq)
  have huC1 := Hreal.c1Distance_le
  have hvC1 := intervalDomainMSignal_c1Distance_le_X2Sigma
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

#print axioms IntervalDomainMSupToStrongBasinEntry
#print axioms IntervalDomainMWeakSupEventualSpectralSemigroupOrbitBound
#print axioms
  intervalDomainM_weakSupEventualSpectralSemigroupOrbitBound_of_basinEntry

end

end ShenWork.Paper3
