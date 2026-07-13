import ShenWork.Paper3.IntervalDomainEventualConvergenceUpgrade
import ShenWork.Paper3.ThresholdOrdering

/-!
# Faithful eventual global stability for Paper 3

The printed global `C¹` estimates in Theorems 2.3--2.5 inherit the same
zero-time defect as (2.12): a bounded positive orbit need not have a uniform
`C¹` bound at `t = 0`.  This additive layer keeps the original statements
unchanged and records the faithful conclusion obtained after an
orbit-dependent positive entrance time.

The exponential constants are deliberately quantified after the orbit.  A
qualitative global-attractor theorem only supplies an orbit-dependent basin
entry time, so moving the prefactor in front of `exp (-rate * t)` cannot in
general produce constants uniform over all bounded global orbits.
-/

namespace ShenWork.Paper3

open ShenWork.IntervalDomain
open ShenWork.Paper2

noncomputable section

/-- Global sup convergence together with orbitwise eventual exponential
convergence in the selected physical `C¹` gauge. -/
def EventuallyGloballyExponentiallyStableNonminimal
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (uStar vStar : ℝ) : Prop :=
  GloballyAsymptoticallyStableNonminimal D p uStar vStar ∧
    ∀ u v : ℝ → D.Point → ℝ,
      PositiveGlobalBoundedSolution D p u v →
        ∃ C > 0, ∃ rate > 0, ∃ t₀ > 0,
          EventualExponentialC1ConvergenceWith
            D N u v uStar vStar C rate t₀

/-- Physical mass compatibility for an already existing global orbit.

`HasInitialMass` reads the stored slice `u 0`.  The legacy classical-solution
API permits that slice to be re-anchored without changing any positive-time
PDE or initial-trace fact, so it is not by itself a faithful mass constraint
on an orbit supplied without its datum and trace. -/
def HasEquilibriumMassOnPositiveTimes
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ) (uStar : ℝ) : Prop :=
  ∀ t, 0 < t → D.integral (u t) = D.volume * uStar

/-- Faithful qualitative global attraction in the neutral-mode branch. -/
def GloballyAsymptoticallyStableMinimalOnPhysicalMass
    (D : BoundedDomainData) (p : CM2Params) (uStar _vStar : ℝ) : Prop :=
  ∀ u v : ℝ → D.Point → ℝ,
    PositiveGlobalBoundedSolution D p u v →
    HasEquilibriumMassOnPositiveTimes D u uStar →
      UniformConvergesInSup D u uStar

/-- Mass-constrained global sup convergence together with orbitwise eventual
exponential convergence.  This is the correct global target when the
constant mode is neutral. -/
def EventuallyGloballyExponentiallyStableMinimal
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (uStar vStar : ℝ) : Prop :=
  GloballyAsymptoticallyStableMinimalOnPhysicalMass D p uStar vStar ∧
    ∀ u v : ℝ → D.Point → ℝ,
      PositiveGlobalBoundedSolution D p u v →
      HasEquilibriumMassOnPositiveTimes D u uStar →
        ∃ C > 0, ∃ rate > 0, ∃ t₀ > 0,
          EventualExponentialC1ConvergenceWith
            D N u v uStar vStar C rate t₀

/-- Additive, faithful eventual version of Paper 3 Theorem 2.3.  The original
all-time statement remains untouched. -/
def Theorem_2_3_EventualGlobalStability
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D) : Prop :=
  p.χ₀ ≤ 0 → 1 ≤ p.m →
    (∀ (ha : 0 < p.a) (hb : 0 < p.b),
      let eq := positiveEquilibrium p ⟨ha, hb⟩
      EventuallyGloballyExponentiallyStableNonminimal
        D p N eq.1 eq.2) ∧
    (p.a = 0 → p.b = 0 →
      ∀ uStar > 0,
        let eq := minimalEquilibrium p uStar
        EventuallyGloballyExponentiallyStableMinimal
          D p N eq.1 eq.2)

/-- Formula-level, package-free eventual version of Paper 3 Theorem 2.4.
The four paper thresholds are exposed directly through
`NonminimalGlobalStabilityFormulaCondition`; no `Paper3Constants` field can
serve as a proof. -/
def Theorem_2_4_EventualGlobalStabilityFormula
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (M0 : ℝ) : Prop :=
  0 < p.a → 0 < p.b → 0 ≤ p.β → 0 < p.α → 0 < p.γ →
    ∀ (ha : 0 < p.a) (hb : 0 < p.b),
      let eq := positiveEquilibrium p ⟨ha, hb⟩
      NonminimalGlobalStabilityFormulaCondition p eq.1 eq.2 M0 →
        EventuallyGloballyExponentiallyStableNonminimal
          D p N eq.1 eq.2

/-- Formula-level, package-free eventual version of Paper 3 Theorem 2.5. -/
def Theorem_2_5_EventualGlobalStabilityFormula
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (uBar vLower : ℝ) : Prop :=
  p.a = 0 → p.b = 0 → p.m = 1 → 1 ≤ p.β →
    ∀ uStar > 0,
      let eq := minimalEquilibrium p uStar
      MinimalGlobalStabilityFormulaCondition p uStar uBar vLower →
        EventuallyGloballyExponentiallyStableMinimal
          D p N eq.1 eq.2

/-- Each of the four explicit strong-logistic formula branches lies below the
actual discrete critical spectrum on the unit interval.  Unlike the older
four-way-maximum wrapper, this proof case-splits on the branch and therefore
does not impose both unrelated exponent conditions at once. -/
theorem
    NonminimalGlobalStabilityFormulaCondition.linearlyStable_unitInterval
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b) {M0 : ℝ}
    (h : NonminimalGlobalStabilityFormulaCondition p
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 M0) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 := by
  have hab : 0 < p.a ∧ 0 < p.b := ⟨ha, hb⟩
  rcases h with h1 | h2 | h3 | h4
  · exact
      positiveEquilibrium_linearlyStable_of_chi_lt_paperCriticalSensitivity_neumann
        unitIntervalNeumannSpectrum p
        unitIntervalNeumannSpectrum_hasNeumannSpectrum ha hb
        (lt_of_lt_of_le h1.2.2.2
          (chiStrong1Formula_le_paperCriticalSensitivity
            unitIntervalNeumannSpectrum p
            unitIntervalNeumannSpectrum_hasNeumannSpectrum
            hab h1.1 h1.2.1))
  · exact
      positiveEquilibrium_linearlyStable_of_chi_lt_paperCriticalSensitivity_neumann
        unitIntervalNeumannSpectrum p
        unitIntervalNeumannSpectrum_hasNeumannSpectrum ha hb
        (lt_of_lt_of_le h2.2.2.2.2
          (chiStrong2Formula_le_paperCriticalSensitivity
            unitIntervalNeumannSpectrum p
            unitIntervalNeumannSpectrum_hasNeumannSpectrum
            hab h2.1 h2.2.2.1))
  · have hαmγ : p.m + p.γ ≤ p.α + 1 := by
      have hif : 0 ≤ (if p.β = 0 then 0 else p.γ) := by
        by_cases hβ : p.β = 0
        · simp [hβ]
        · simp [hβ, p.hγ.le]
      exact le_trans (le_add_of_nonneg_right hif) h3.2.2.1
    exact
      positiveEquilibrium_linearlyStable_of_chi_lt_paperCriticalSensitivity_neumann
        unitIntervalNeumannSpectrum p
        unitIntervalNeumannSpectrum_hasNeumannSpectrum ha hb
        (lt_of_lt_of_le h3.2.2.2
          (chiStrong3Formula_le_paperCriticalSensitivity
            unitIntervalNeumannSpectrum p
            unitIntervalNeumannSpectrum_hasNeumannSpectrum
            hab h3.1 M0 hαmγ))
  · have hαmγ : p.m + p.γ ≤ p.α + 1 := by
      have hγ0 : 0 ≤ p.γ := p.hγ.le
      linarith [h4.2.2.2.1]
    exact
      positiveEquilibrium_linearlyStable_of_chi_lt_paperCriticalSensitivity_neumann
        unitIntervalNeumannSpectrum p
        unitIntervalNeumannSpectrum_hasNeumannSpectrum ha hb
        (lt_of_lt_of_le h4.2.2.2.2
          (chiStrong4Formula_le_paperCriticalSensitivity
            unitIntervalNeumannSpectrum p
            unitIntervalNeumannSpectrum_hasNeumannSpectrum
            hab h4.1 M0 hαmγ))

/-- Once qualitative global attraction is known, the proved positive-logistic
Stage B supplies the honest orbitwise eventual `C¹` conclusion.  No constants,
compactness, or norm package is assumed. -/
theorem
    intervalDomain_eventuallyGloballyExponentiallyStableNonminimal_of_global
    (p : CM2Params) (hm : p.m = 1) {uStar vStar : ℝ}
    (ha : 0 < p.a)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hstable :
      LinearlyStable unitIntervalNeumannSpectrum p uStar vStar)
    (hglobal :
      GloballyAsymptoticallyStableNonminimal
        intervalDomain p uStar vStar) :
    EventuallyGloballyExponentiallyStableNonminimal
      intervalDomain p intervalDomainSectorialStabilityNorms
        uStar vStar := by
  refine ⟨hglobal, ?_⟩
  intro u v huv
  exact intervalDomain_eventualC1_of_uniformSup_of_linearlyStable
    p hm ha heq hstable huv (hglobal u v huv)

/-- Package-free Theorem 2.3 positive branch on the faithful currently
implemented `m = 1` interval equation.  Its only remaining premise is the
mathematical global-attractor statement itself. -/
theorem intervalDomain_Theorem_2_3_positiveEventual_of_global
    (p : CM2Params) (hm : p.m = 1) (hχ : p.χ₀ ≤ 0)
    (hglobal : ∀ (ha : 0 < p.a) (hb : 0 < p.b),
      let eq := positiveEquilibrium p ⟨ha, hb⟩
      GloballyAsymptoticallyStableNonminimal
        intervalDomain p eq.1 eq.2) :
    ∀ (ha : 0 < p.a) (hb : 0 < p.b),
      let eq := positiveEquilibrium p ⟨ha, hb⟩
      EventuallyGloballyExponentiallyStableNonminimal
        intervalDomain p intervalDomainSectorialStabilityNorms
          eq.1 eq.2 := by
  intro ha hb
  dsimp
  exact
    intervalDomain_eventuallyGloballyExponentiallyStableNonminimal_of_global
      p hm ha (paper3ConstantEquilibrium_positive p ha hb)
      (unitInterval_positiveEquilibrium_linearlyStable_of_chi_nonpos
        p hχ ha hb)
      (hglobal ha hb)

/-- Package-free Theorem 2.4 eventual upgrade on the currently implemented
`m = 1` interval equation.  The formula condition itself proves discrete
linear stability; the only remaining premise is qualitative global
attraction. -/
theorem intervalDomain_Theorem_2_4_positiveEventualFormula_of_global
    (p : CM2Params) (hm : p.m = 1) (M0 : ℝ)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hglobal :
      NonminimalGlobalStabilityFormulaCondition p
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2 M0 →
        GloballyAsymptoticallyStableNonminimal intervalDomain p
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2) :
    NonminimalGlobalStabilityFormulaCondition p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2 M0 →
      EventuallyGloballyExponentiallyStableNonminimal intervalDomain p
        intervalDomainSectorialStabilityNorms
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2 := by
  intro hcond
  exact
    intervalDomain_eventuallyGloballyExponentiallyStableNonminimal_of_global
      p hm ha (paper3ConstantEquilibrium_positive p ha hb)
      (hcond.linearlyStable_unitInterval p ha hb)
      (hglobal hcond)

#print axioms
  NonminimalGlobalStabilityFormulaCondition.linearlyStable_unitInterval
#print axioms
  intervalDomain_eventuallyGloballyExponentiallyStableNonminimal_of_global
#print axioms intervalDomain_Theorem_2_3_positiveEventual_of_global
#print axioms
  intervalDomain_Theorem_2_4_positiveEventualFormula_of_global

end

end ShenWork.Paper3
