import ShenWork.Paper3.IntervalDomainMNegativeSensitivity
import ShenWork.Paper3.IntervalDomainMRectangleGlobal
import ShenWork.Paper3.IntervalDomainMMinimalFaithfulTheorem22
import ShenWork.Paper3.EventualGlobalStability
import ShenWork.Paper3.IntervalDomainMMinimalChiNonposConvergence

/-!
# Faithful eventual Theorem 2.3 on the general-`m` unit interval

This file proves Theorem 2.3 of Chen–Ruau–Shen Paper 3 on the faithful
general-`m` domain `intervalDomainM`, removing the `p.m = 1` restriction
that appears in `IntervalDomainTheorem23Eventual.lean`.

**Nonminimal branch** (`a > 0, b > 0`): fully proved by wiring
`intervalDomainM_chiNonpos_globallyAsymptoticallyStableNonminimal`
through `intervalDomainM_eventualGlobal_of_globallyAsymptotic`.

**Minimal branch** (`a = 0, b = 0`): the eventual C¹ upgrade from
uniform sup convergence is fully wired through the general-`m`
mass-constrained bootstrap. The global qualitative attractor
(porous medium convergence for `χ₀ ≤ 0`) is fully proved.
-/

namespace ShenWork.Paper3

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMContinuation
open ShenWork.PDE.SectorialOperator

noncomputable section

-- ============================================================
-- Nonminimal branch: pure wiring, 0 sorry
-- ============================================================

/-- Unconditional faithful eventual-exponential positive branch of Paper 3
Theorem 2.3 for the general-`m` unit-interval equation. -/
theorem intervalDomainM_Theorem_2_3_positiveEventual
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) :
    ∀ (ha : 0 < p.a) (hb : 0 < p.b),
      let eq := positiveEquilibrium p ⟨ha, hb⟩
      EventuallyGloballyExponentiallyStableNonminimal
        intervalDomainM p intervalDomainMSectorialStabilityNorms
          eq.1 eq.2 := by
  intro ha hb
  dsimp
  exact intervalDomainM_eventualGlobal_of_globallyAsymptotic
    p ha (paper3ConstantEquilibrium_positive p ha hb)
    (unitInterval_positiveEquilibrium_linearlyStable_of_chi_nonpos p hχ ha hb)
    (intervalDomainM_chiNonpos_globallyAsymptoticallyStableNonminimal p hχ ha hb)

-- ============================================================
-- Minimal branch infrastructure
-- ============================================================

/-- Uniform sup convergence on the mass hyperplane, combined with the
general-`m` mass-constrained bootstrap, yields eventual exponential C¹
convergence.  This is the general-`m` analog of
`intervalDomain_minimal_eventualC1_of_uniformSup_of_massGap`. -/
theorem intervalDomainM_minimal_eventualC1_of_uniformSup_of_massGap
    (p : CM2Params) (ha0 : p.a = 0) (hb0 : p.b = 0)
    {uStar vStar : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    {gap : ℝ}
    (hgap : UnitIntervalLinearMassSpectralGap p uStar vStar gap)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomainM u uStar)
    (hconv : UniformConvergesInSup intervalDomainM u uStar) :
    ∃ C > 0, ∃ rate > 0, ∃ t₀ > 0,
      EventualExponentialC1ConvergenceWith
        intervalDomainM intervalDomainMSectorialStabilityNorms
          u v uStar vStar C rate t₀ := by
  let sigma : ℝ := 7 / 8
  have hsigmaStrong : 3 / 4 < sigma := by norm_num [sigma]
  have hsigma1 : sigma < 1 := by norm_num [sigma]
  obtain ⟨deltaBasin, hdeltaBasin, T, hT, henter⟩ :=
    intervalDomainMassSupToStrongBasinEntryGeneralM_proved
      p hsigmaStrong hsigma1 ha0 hb0 heq hgap
  have hevent : ∀ᶠ t : ℝ in atTop,
      intervalDomainM.supNorm (fun x => u t x - uStar) < deltaBasin :=
    hconv.eventually (Iio_mem_nhds hdeltaBasin)
  obtain ⟨threshold, hthreshold⟩ := (eventually_atTop.1 hevent)
  let tau₁ : ℝ := max threshold 1
  have htau₁ : 0 < tau₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hclose : SupCloseToConstant intervalDomainM (u tau₁) uStar deltaBasin :=
    hthreshold tau₁ (le_max_left _ _)
  have hsol := huv.classical (tau₁ + 1) (by linarith)
  have hpid : PositiveInitialDatum intervalDomainM (u tau₁) :=
    positiveInitialDatum_of_paperPositiveInitialDatumM
      (classicalSolution_slice_paperPositiveInitialDatumM
        hsol ⟨htau₁, by linarith⟩)
  let us : ℝ → intervalDomainPoint → ℝ := fun t x => u (t + tau₁) x
  let vs : ℝ → intervalDomainPoint → ℝ := fun t x => v (t + tau₁) x
  have hshiftGlobal :
      IsPaper2GlobalClassicalSolution intervalDomainM p us vs := by
    intro T₂ hT₂
    have hsum : 0 < T₂ + tau₁ := by linarith
    have hsolT := huv.classical (T₂ + tau₁) hsum
    have hshift := classicalSolution_timeShiftM hsolT htau₁ (by linarith)
    simpa only [add_sub_cancel_right] using hshift
  have hshiftTrace : InitialTrace intervalDomainM (u tau₁) us := by
    simpa [us] using timeShiftInitialTraceM hsol htau₁ (by linarith)
  have hshiftMass :
      HasEquilibriumMassOnPositiveTimes intervalDomainM us uStar := by
    intro t ht
    exact hmass (t + tau₁) (by linarith)
  have hentry := henter (u tau₁) hpid hclose us vs
    hshiftGlobal hshiftTrace hshiftMass
  let tauRestart : ℝ := T + tau₁
  have htauRestart : 0 < tauRestart := by dsimp [tauRestart]; linarith
  have hrestart :
      intervalDomainX2SigmaDistance sigma uStar (u tauRestart) ≤
        intervalDomainStrongBootstrapRadiusGeneralM
          p sigma uStar vStar gap heq / 2 := by
    change intervalDomainX2SigmaDistance sigma uStar (u (T + tau₁)) ≤ _
    simpa [us] using hentry.2
  have hresult :=
    intervalDomainM_minimal_eventualC1_of_X2Sigma_restart_of_massGap
      p ha0 hb0 heq hgap huv.1 hmass htauRestart hrestart
  let R := intervalDomainStrongBootstrapRadiusGeneralM
    p sigma uStar vStar gap heq
  let rate := gap / 4
  let Cu := intervalDomainX2SigmaValueTrace sigma +
    intervalDomainX2SigmaDerivativeTrace sigma
  let Cv := 4 * paper3UniformSignalStrongConstant p uStar heq.u_pos *
    intervalDomainX2SigmaC1Envelope sigma
  let C := (1 + Cu + Cv) * R * Real.exp (rate * tauRestart)
  have hR : 0 < R := intervalDomainStrongBootstrapRadiusGeneralM_pos
    p heq hgap.1 (by norm_num [sigma] : 0 < sigma) hsigma1
  have hrate : 0 < rate := by dsimp [rate]; linarith [hgap.1]
  have hCu : 0 ≤ Cu := add_nonneg
    (intervalDomainX2SigmaValueTrace_nonneg sigma)
    (intervalDomainX2SigmaDerivativeTrace_nonneg sigma)
  have hCv : 0 ≤ Cv := mul_nonneg
    (mul_nonneg (by norm_num)
      (paper3UniformSignalStrongConstant_pos p uStar heq.u_pos).le)
    (intervalDomainX2SigmaC1Envelope_pos sigma).le
  have hC : 0 < C := mul_pos
    (mul_pos (by linarith : (0 : ℝ) < 1 + Cu + Cv) hR)
    (Real.exp_pos _)
  exact ⟨C, hC, rate, hrate, tauRestart, htauRestart, hresult⟩

-- ============================================================
-- Minimal global attractor (proved via signal-gap + heat bridge)
-- ============================================================

/-- Qualitative global attraction for the nonpositive-sensitivity minimal
model on its physical-mass hyperplane, for the faithful general-`m` equation.

The `m = 1` version uses heat equation arguments (Fourier decay);
the general-`m` version requires porous medium convergence. -/
theorem intervalDomainM_chiNonpos_globallyAsymptoticallyStableMinimal
    (p : CM2Params)
    (ha0 : p.a = 0) (hb0 : p.b = 0) (hχ : p.χ₀ ≤ 0)
    {uStar : ℝ} (huStar : 0 < uStar) :
    let eq := minimalEquilibrium p uStar
    GloballyAsymptoticallyStableMinimalOnPhysicalMass
      intervalDomainM p eq.1 eq.2 := by
  dsimp
  intro u v huv hmass
  exact intervalDomainM_minimal_chiNonpos_uniform_u_converges
    p ha0 hb0 hχ huv huStar hmass

-- ============================================================
-- Minimal branch capstone
-- ============================================================

/-- Unconditional faithful eventual-exponential minimal branch of Paper 3
Theorem 2.3 for the general-`m` unit-interval equation. -/
theorem intervalDomainM_Theorem_2_3_minimalEventual
    (p : CM2Params) (hχ : p.χ₀ ≤ 0)
    (ha0 : p.a = 0) (hb0 : p.b = 0) :
    ∀ uStar > 0,
      let eq := minimalEquilibrium p uStar
      EventuallyGloballyExponentiallyStableMinimal
        intervalDomainM p intervalDomainMSectorialStabilityNorms
          eq.1 eq.2 := by
  intro uStar huStar
  let eq := minimalEquilibrium p uStar
  have heq : Paper3ConstantEquilibrium p eq.1 eq.2 := by
    simpa [eq] using paper3ConstantEquilibrium_minimal
      p ha0 hb0 uStar huStar
  have hgap : UnitIntervalLinearMassSpectralGap p eq.1 eq.2
      unitIntervalNeumannSpectrum.firstNonzero := by
    simpa [eq] using
      minimalEquilibrium_UnitIntervalLinearMassSpectralGap_of_chi_nonpos
        p hχ ha0 huStar
  have hglobal :
      GloballyAsymptoticallyStableMinimalOnPhysicalMass
        intervalDomainM p eq.1 eq.2 := by
    simpa [eq] using
      intervalDomainM_chiNonpos_globallyAsymptoticallyStableMinimal
        p ha0 hb0 hχ huStar
  refine ⟨hglobal, ?_⟩
  intro u v huv hmass
  exact intervalDomainM_minimal_eventualC1_of_uniformSup_of_massGap
    p ha0 hb0 heq hgap huv hmass (hglobal u v huv hmass)

-- ============================================================
-- Full Theorem 2.3 capstone
-- ============================================================

/-- Unconditional faithful eventual form of Paper 3 Theorem 2.3
for the general-`m` unit-interval equation. -/
theorem intervalDomainM_Theorem_2_3_EventualGlobalStability
    (p : CM2Params) :
    Theorem_2_3_EventualGlobalStability
      intervalDomainM p intervalDomainMSectorialStabilityNorms := by
  intro hχ _hmLower
  constructor
  · exact intervalDomainM_Theorem_2_3_positiveEventual p hχ
  · intro ha0 hb0
    exact intervalDomainM_Theorem_2_3_minimalEventual
      p hχ ha0 hb0

#print axioms intervalDomainM_Theorem_2_3_positiveEventual
#print axioms intervalDomainM_minimal_eventualC1_of_uniformSup_of_massGap
#print axioms intervalDomainM_chiNonpos_globallyAsymptoticallyStableMinimal
#print axioms intervalDomainM_Theorem_2_3_minimalEventual
#print axioms intervalDomainM_Theorem_2_3_EventualGlobalStability

end

end ShenWork.Paper3
