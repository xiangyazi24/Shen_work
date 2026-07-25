import ShenWork.Paper3.IntervalDomainMMinimalEntropy
import ShenWork.Paper3.IntervalDomainMMinimalSignalFloor
import ShenWork.Paper3.IntervalDomainMTheorem23Eventual
import ShenWork.Paper3.IntervalDomainMEntropyBasinEntry
import ShenWork.Paper3.IntervalDomainMNegativeSensitivity
import ShenWork.Paper3.IntervalDomainUniformSpectralGap

/-!
# M-native χ₀>0 minimal1 branch of faithful eventual Theorem 2.5 (`1 ≤ m < 2`)

Assembly of the general-`m` minimal1 disjunct on the faithful `u^m`-flux domain.
The entropy route produces arbitrarily late small `L²` slices; the
`θ(α) ≤ C·L²` bridge feeds the weak-supremum basin-entry consumer; the
general-`m` mass-constrained bootstrap and the general-`m` minimal linear
stability (via the `firstNonzero`-lower critical-sensitivity bound) close the
branch with no `p.m = 1` hypothesis.
-/

open Filter MeasureTheory Set Topology
open ShenWork.IntervalDomain ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMContinuation
open ShenWork.PDE.SectorialOperator

namespace ShenWork.Paper3

noncomputable section

/-- Every bounded physical-mass faithful orbit satisfying the concrete eventual
box has arbitrarily late slices with small `θ(α)`-dissipation.  The entropy
half-Young route gives late small `L²`; the bridge converts to `θ(p.α)`. -/
theorem intervalDomainM_minimal1_exists_late_thetaDissipation_lt
    (p : CM2Params) (hm : 1 ≤ p.m) (hb0 : p.b = 0)
    {uStar vStar uBar vLower : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (huBar : 0 < uBar) (hvLower : 0 ≤ vLower)
    (hχpos : 0 < p.χ₀)
    (hχ : p.χ₀ < chiMinimal1EntropyThresholdM p uStar uBar vLower)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomainM u uStar)
    (hupper : ∀ᶠ t : ℝ in atTop,
      intervalDomainM.supNorm (u t) ≤ uBar)
    (hfloor : ∀ᶠ t : ℝ in atTop,
      ∀ x : intervalDomainPoint, vLower ≤ v t x)
    {T q : ℝ} (hq : 0 < q) :
    ∃ t, T ≤ t ∧
      chemotaxisThetaDissipation intervalDomain uStar p.α (u t) < q := by
  let c := minimal1MEntropyCoefficient p uStar uBar vLower
  have hc : 0 < c := by
    simpa [c] using minimal1MEntropyCoefficient_pos_of_lt
      p hm heq.u_pos huBar hvLower hχpos hχ
  set as : ℝ := alphaSlope p uStar uBar with hasdef
  have has0 : 0 ≤ as := by
    simpa [hasdef] using alphaSlope_nonneg p heq.u_pos huBar
  have has1 : 0 < as + 1 := by linarith
  set qL2 : ℝ := q / (as + 1) with hqL2def
  have hqL2 : 0 < qL2 := div_pos hq has1
  rcases eventually_atTop.1 hupper with ⟨Tu, hTu⟩
  rcases eventually_atTop.1 hfloor with ⟨Tv, hTv⟩
  let Tbase : ℝ := max (max Tu Tv) (max T 1)
  have hTbase : 0 < Tbase :=
    lt_of_lt_of_le zero_lt_one
      ((le_max_right T 1).trans (le_max_right (max Tu Tv) (max T 1)))
  have hTle : T ≤ Tbase :=
    (le_max_left T 1).trans (le_max_right (max Tu Tv) (max T 1))
  have hTuLe : Tu ≤ Tbase :=
    (le_max_left Tu Tv).trans (le_max_left (max Tu Tv) (max T 1))
  have hTvLe : Tv ≤ Tbase :=
    (le_max_right Tu Tv).trans (le_max_left (max Tu Tv) (max T 1))
  obtain ⟨t, htbase, htSmall⟩ :=
    exists_late_dissipation_lt_of_nonnegative_energy_on_Ici
      (E := fun s => chemotaxisEntropyFunctional intervalDomain p.m uStar u s)
      (D := fun s => ∫ y in (0 : ℝ)..1,
        (intervalDomainLift (u s) y - uStar) ^ 2)
      (slope := fun s => intervalDomain.integral (fun x =>
        chemotaxisEntropyIntegrand p.m uStar (u s x) *
          intervalDomain.timeDeriv u s x))
      hc hTbase hqL2
      (fun s hs =>
        intervalDomain_chemotaxisEntropyFunctional_nonneg_of_inside_pos
          (by linarith : (1 / 2 : ℝ) ≤ p.m) heq.u_pos
          (fun x hx => huv.pos (t := s) (x := x) hs hx))
      (intervalDomainM_strongMEntropy_hasDerivAt p heq huv)
      (fun s hs => by
        have hs0 : 0 < s := lt_of_lt_of_le hTbase hs
        have hH : 0 < s + 1 := by linarith
        have hsH : s < s + 1 := by linarith
        let hsol := huv.classical (s + 1) hH
        have hsup : intervalDomainM.supNorm (u s) ≤ uBar :=
          hTu s (hTuLe.trans hs)
        have hVfloor : ∀ x : intervalDomainPoint, vLower ≤ v s x :=
          hTv s (hTvLe.trans hs)
        have hmassS : intervalDomainM.integral (u s) = uStar := by
          have h := hmass s hs0
          simpa [intervalDomainM] using h
        have huStarBar : uStar ≤ uBar := by
          have hmassSup := intervalDomainM_classicalSolution_mass_le_supNorm
            hsol (⟨hs0, hsH⟩ : s ∈ Ioo (0 : ℝ) (s + 1))
          rw [hmassS] at hmassSup
          exact hmassSup.trans hsup
        have hpointUpper : ∀ x : intervalDomainPoint, u s x ≤ uBar := by
          intro x
          have hx := intervalDomainM_lift_le_supNorm_of_classical
            hsol (⟨hs0, hsH⟩ : s ∈ Ioo (0 : ℝ) (s + 1)) x.property
          have hx' : u s x ≤ intervalDomainM.supNorm (u s) := by
            simpa [intervalDomainLift, x.property] using hx
          exact hx'.trans hsup
        exact intervalDomainM_entropySlope_le_minimal1MCoefficient
          hm hb0 hsol hs0 hsH heq huBar huStarBar hmassS
            hpointUpper hvLower hVfloor)
  -- Convert the small L² slice into a small θ(α) slice through the bridge.
  refine ⟨t, hTle.trans htbase, ?_⟩
  have hs0 : 0 < t := lt_of_lt_of_le hTbase htbase
  have hH : 0 < t + 1 := by linarith
  have hsH : t < t + 1 := by linarith
  let hsol := huv.classical (t + 1) hH
  have hsup : intervalDomainM.supNorm (u t) ≤ uBar :=
    hTu t (hTuLe.trans htbase)
  have hmassT : intervalDomainM.integral (u t) = uStar := by
    have h := hmass t hs0
    simpa [intervalDomainM] using h
  have huStarBar : uStar ≤ uBar := by
    have hmassSup := intervalDomainM_classicalSolution_mass_le_supNorm
      hsol (⟨hs0, hsH⟩ : t ∈ Ioo (0 : ℝ) (t + 1))
    rw [hmassT] at hmassSup
    exact hmassSup.trans hsup
  have hpointUpper : ∀ x : intervalDomainPoint, u t x ≤ uBar := by
    intro x
    have hx := intervalDomainM_lift_le_supNorm_of_classical
      hsol (⟨hs0, hsH⟩ : t ∈ Ioo (0 : ℝ) (t + 1)) x.property
    have hx' : u t x ≤ intervalDomainM.supNorm (u t) := by
      simpa [intervalDomainLift, x.property] using hx
    exact hx'.trans hsup
  have hbridge := intervalDomainM_minimal1_theta_le_L2
    hsol hs0 hsH heq.u_pos huStarBar hpointUpper
  set L2 : ℝ := ∫ y in (0 : ℝ)..1,
    (intervalDomainLift (u t) y - uStar) ^ 2 with hL2def
  have hL2nonneg : 0 ≤ L2 := by
    rw [hL2def]
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro y _
    exact sq_nonneg _
  have hbridge' : chemotaxisThetaDissipation intervalDomain uStar p.α (u t) ≤
      as * L2 := by
    simpa [hasdef, hL2def] using hbridge
  have hstep : as * L2 ≤ (as + 1) * L2 :=
    mul_le_mul_of_nonneg_right (by linarith) hL2nonneg
  have hlt : (as + 1) * L2 < q := by
    have hL2lt : L2 < qL2 := htSmall
    calc (as + 1) * L2 < (as + 1) * qL2 :=
          mul_lt_mul_of_pos_left hL2lt has1
      _ = q := by rw [hqL2def]; field_simp
  exact lt_of_le_of_lt (hbridge'.trans hstep) hlt

#print axioms intervalDomainM_minimal1_exists_late_thetaDissipation_lt

/-- The minimal1M entropy slices enter every weak supremum neighborhood at
arbitrarily late positive times. -/
theorem intervalDomainM_minimal1_exists_late_supClose
    (p : CM2Params) (hm : 1 ≤ p.m) (hb0 : p.b = 0)
    {uStar vStar uBar vLower : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (huBar : 0 < uBar) (hvLower : 0 ≤ vLower)
    (hχpos : 0 < p.χ₀)
    (hχ : p.χ₀ < chiMinimal1EntropyThresholdM p uStar uBar vLower)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomainM u uStar)
    (hupper : ∀ᶠ t : ℝ in atTop,
      intervalDomainM.supNorm (u t) ≤ uBar)
    (hfloor : ∀ᶠ t : ℝ in atTop,
      ∀ x : intervalDomainPoint, vLower ≤ v t x)
    {T eps : ℝ} (heps : 0 < eps) :
    ∃ t, T ≤ t ∧ SupCloseToConstant intervalDomainM (u t) uStar eps := by
  refine intervalDomainM_exists_late_supClose_of_thetaDissipation
    p heq.u_pos huv ?_ T heps
  intro T' q _hT' hq
  exact intervalDomainM_minimal1_exists_late_thetaDissipation_lt
    p hm hb0 heq huBar hvLower hχpos hχ huv hmass hupper hfloor (T := T') hq

/-- Recurrence variant of the general-`m` minimal mass-constrained bootstrap:
a single late supremum-close slice (produced recurrently, not by full uniform
convergence) plus the mass spectral gap upgrades to eventual exponential
`C¹` convergence.  Structurally identical to
`intervalDomainM_minimal_eventualC1_of_uniformSup_of_massGap`, sourcing the
basin-entry slice from a recurrence hypothesis. -/
theorem intervalDomainM_minimal_eventualC1_of_lateSupClose_of_massGap
    (p : CM2Params) (ha0 : p.a = 0) (hb0 : p.b = 0)
    {uStar vStar : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    {gap : ℝ}
    (hgap : UnitIntervalLinearMassSpectralGap p uStar vStar gap)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomainM u uStar)
    (hlate : ∀ eps : ℝ, 0 < eps → ∃ t, 1 ≤ t ∧
      SupCloseToConstant intervalDomainM (u t) uStar eps) :
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
  obtain ⟨tau₁, htau₁ge, hclose⟩ := hlate deltaBasin hdeltaBasin
  have htau₁ : 0 < tau₁ := lt_of_lt_of_le one_pos htau₁ge
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

/-- The general-`m` minimal linear-stability threshold: the `firstNonzero`-lower
bound on the minimal-equilibrium critical sensitivity.  Below it the minimal
equilibrium is discrete-linearly stable (no `p.m = 1`; the `uStar^(m+γ−1)` factor
carries the general-`m` diffusion). -/
def minimalEquilibriumLinStabThresholdM (p : CM2Params) (uStar : ℝ) : ℝ :=
  ((1 + (minimalEquilibrium p uStar).2) ^ p.β /
      (p.ν * p.γ * (minimalEquilibrium p uStar).1 ^ (p.m + p.γ - 1))) *
    (p.μ + unitIntervalNeumannSpectrum.firstNonzero)

/-- The full general-`m` minimal1 sensitivity threshold: the minimum of the
linear-stability threshold and the entropy-dissipation threshold. -/
def chiMinimal1FormulaM (p : CM2Params) (uStar uBar vLower : ℝ) : ℝ :=
  min (minimalEquilibriumLinStabThresholdM p uStar)
    (chiMinimal1EntropyThresholdM p uStar uBar vLower)

/-- **Steps 6–7 (capstone lemma).**  Unconditional first minimal-formula branch
of the faithful eventual Theorem 2.5 on the general-`m` unit-interval equation
(`1 ≤ m < 2`, `χ₀ > 0`, `a = b = 0`).  No `p.m = 1` hypothesis. -/
theorem intervalDomainM_eventuallyGloballyExponentiallyStableMinimal_minimal1M
    (p : CM2Params) (hN : p.N = 1)
    (hm : 1 ≤ p.m ∧ p.m < 2) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (hbeta : 1 ≤ p.β) {uStar : ℝ} (huStar : 0 < uStar)
    (hchi : 0 < p.χ₀)
    (hthreshold : p.χ₀ < chiMinimal1FormulaM p uStar
      (intervalDomainMMinimalEventualBoxConstants p uStar).1
      (intervalDomainMMinimalEventualBoxConstants p uStar).2) :
    EventuallyGloballyExponentiallyStableMinimal intervalDomainM p
      intervalDomainMSectorialStabilityNorms
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2 := by
  let eq := minimalEquilibrium p uStar
  let uBar := (intervalDomainMMinimalEventualBoxConstants p uStar).1
  let vLower := (intervalDomainMMinimalEventualBoxConstants p uStar).2
  have heq : Paper3ConstantEquilibrium p eq.1 eq.2 := by
    simpa [eq] using paper3ConstantEquilibrium_minimal p ha0 hb0 uStar huStar
  -- Linear stability at general `m` via the firstNonzero-lower critical bound.
  have hstable : LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 := by
    have hcrit : p.χ₀ <
        paperCriticalSensitivity unitIntervalNeumannSpectrum p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2 :=
      lt_of_lt_of_le
        (lt_of_lt_of_le hthreshold (min_le_left _ _))
        (paperCriticalSensitivity_minimalEquilibrium_ge_firstNonzero_lower
          unitIntervalNeumannSpectrum p
          unitIntervalNeumannSpectrum_hasNeumannSpectrum huStar)
    simpa [eq] using
      minimalEquilibrium_linearlyStable_of_chi_lt_paperCriticalSensitivity_neumann
        unitIntervalNeumannSpectrum p
        unitIntervalNeumannSpectrum_hasNeumannSpectrum huStar hcrit
  obtain ⟨gap, _hgapPos, hgap⟩ :=
    unitIntervalLinearMassSpectralGap_of_linearlyStable p heq hstable
  have hχent : p.χ₀ < chiMinimal1EntropyThresholdM p uStar uBar vLower :=
    lt_of_lt_of_le hthreshold (min_le_right _ _)
  have hbox := intervalDomainMMinimalEventualBoxConstants_spec
    p hm ha0 hb0 hbeta hchi huStar
  change IntervalDomainMMinimalEventualBox p uStar uBar vLower at hbox
  obtain ⟨huBar, hvLower, hboxes⟩ := hbox
  have hproduce : ∀ u v : ℝ → intervalDomainPoint → ℝ,
      PositiveGlobalBoundedSolution intervalDomainM p u v →
      HasEquilibriumMassOnPositiveTimes intervalDomainM u eq.1 →
      ∃ C > 0, ∃ rate > 0, ∃ t₀ > 0,
        EventualExponentialC1ConvergenceWith
          intervalDomainM intervalDomainMSectorialStabilityNorms
            u v eq.1 eq.2 C rate t₀ := by
    intro u v huv hmass
    obtain ⟨hupper, hfloor⟩ := hboxes u v huv hmass
    refine intervalDomainM_minimal_eventualC1_of_lateSupClose_of_massGap
      p ha0 hb0 heq hgap huv hmass ?_
    intro eps heps
    exact intervalDomainM_minimal1_exists_late_supClose
      p hm.1 hb0 heq huBar hvLower.le hchi hχent huv hmass hupper hfloor
        (T := (1 : ℝ)) heps
  refine ⟨?_, hproduce⟩
  intro u v huv hmass
  obtain ⟨C, hC, rate, hrate, t₀, ht₀, hbound⟩ := hproduce u v huv hmass
  exact intervalDomainM_uniformConvergesInSup_of_eventualExponentialC1
    hrate hbound

/-- Minimal1 disjunct of the general-`m` minimal global-stability condition. -/
def MinimalGlobalStabilityFormulaConditionM
    (p : CM2Params) (uStar uBar vLower : ℝ) : Prop :=
  0 < p.χ₀ ∧ p.χ₀ < chiMinimal1FormulaM p uStar uBar vLower

/-- **Step 7 (capstone).**  Faithful eventual Theorem 2.5, minimal1 branch, on
the general-`m` unit interval (`1 ≤ m < 2`). -/
theorem intervalDomainM_Theorem_2_5_minimal1_EventualGlobalStabilityFormula
    (p : CM2Params) (hN : p.N = 1)
    (hm : 1 ≤ p.m ∧ p.m < 2) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (hbeta : 1 ≤ p.β) {uStar : ℝ} (huStar : 0 < uStar)
    (hcond : MinimalGlobalStabilityFormulaConditionM p uStar
      (intervalDomainMMinimalEventualBoxConstants p uStar).1
      (intervalDomainMMinimalEventualBoxConstants p uStar).2) :
    EventuallyGloballyExponentiallyStableMinimal intervalDomainM p
      intervalDomainMSectorialStabilityNorms
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2 :=
  intervalDomainM_eventuallyGloballyExponentiallyStableMinimal_minimal1M
    p hN hm ha0 hb0 hbeta huStar hcond.1 hcond.2

#print axioms intervalDomainM_minimal1_exists_late_supClose
#print axioms intervalDomainM_minimal_eventualC1_of_lateSupClose_of_massGap
#print axioms intervalDomainM_eventuallyGloballyExponentiallyStableMinimal_minimal1M
#print axioms intervalDomainM_Theorem_2_5_minimal1_EventualGlobalStabilityFormula


end

end ShenWork.Paper3
