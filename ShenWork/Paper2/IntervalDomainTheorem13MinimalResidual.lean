import ShenWork.Paper2.IntervalDomainTheorem12SlowBranchClosure
import ShenWork.Paper2.IntervalDomainTheorem13CorrectedHeadline
import ShenWork.Paper2.IntervalDomainInterpolationCounterexample
import ShenWork.Paper2.IntervalDomainTheorem13
import ShenWork.Paper2.IntervalDomainRestartedLpLinfProducer
import ShenWork.PDE.IntervalDomainExistence

/-!
# Paper 2, Theorem 1.3: minimal honest residual

The legacy frontier bundle in `IntervalDomainTheorem13` is not a sound final
interface.  In particular, its `globalExtension` field is false: a pair of
total functions may solve the PDE before one finite horizon and be changed
arbitrarily afterwards.  Canonical maximal continuation must be constructed
instead.

All four finite-horizon strong-logistic energy estimates, the slow/critical
finite-power seeds, the restarted `Lp`-to-`Linf` endpoint, local existence,
overlap uniqueness, continuation, and global boundedness are already proved
on the paper-faithful domain `intervalDomainM`.  What remains at statement
level is only:

* the abstract constant `C.K` must be the concrete interval value of (1.19);
* in printed alternative (iv), the missing exponent-domain guard required by
  Proposition 2.2 must hold.

The first theorem below therefore carries no energy-estimate hypothesis.
-/

open ShenWork.IntervalDomain
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.IntervalDomainTheorem13MinimalResidual

open ShenWork.Paper2.IntervalDomainTheorem12SlowBranchClosure
open ShenWork.Paper2.IntervalDomainTheorem13CorrectedBoundedness
open ShenWork.Paper2.IntervalDomainTheorem13CorrectedHeadline
open ShenWork.Paper2.IntervalDomainTheorem13CriticalConstants

/-! ## Exact obstructions in the legacy frontier -/

/-- The interpolation field in the old theorem-assembly interface is
literally false: it admits positive step functions without any Sobolev or
continuity hypothesis.  The proved solution-specific Lemma 4.1 is the sound
replacement. -/
theorem not_legacyTheorem13_interpolation_frontier :
    ¬ IntervalDomainLemma41.IntervalDomainInterpolation :=
  IntervalDomainInterpolationCounterexample.not_intervalDomainInterpolation

/-- In the real strong-logistic regime the old bundled frontier cannot be
inhabited.  Its `globalExtension` field wrongly concludes that the *same*
arbitrary total functions solve after a finite horizon; changing their tail
gives the existing clean counterexample. -/
theorem not_IntervalDomainTheorem13FrontierData_of_real_regime
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hm : 1 ≤ p.m) :
    ¬ IntervalDomainTheorem13.IntervalDomainTheorem13FrontierData p C S := by
  intro hfrontier
  exact
    _root_.ShenWork.IntervalDomainExistence.not_intervalDomainTheorem11_globalExtension_equilibrium_bad_tail
      p ha hb hm hfrontier.globalExtension

/-- The printed fourth strong-logistic alternative, before adding the missing
exponent-domain guard. -/
def PrintedStrongLogisticCaseIV
    (p : CM2Params) (C : Paper2Constants p) : Prop :=
  (1 / 2 : ℝ) ≤ p.β ∧
    p.α = 2 * p.m + p.γ - 2 ∧
    (positivePart ((p.N : ℝ) * p.α - 2) = 0 ∨
      p.χ₀ < Real.sqrt
        (8 * p.b /
          (positivePart ((p.N : ℝ) * p.α - 2) *
            Theta_beta (2 * p.β - 1) * C.K)))

/-- Minimal paper-level correction after the concrete energy estimates have
been discharged.  It identifies the arbitrary statement-layer `K` with the
actual interval constant and adds the missing exponent guard only when the
printed fourth alternative is used. -/
def IntervalDomainTheorem13MinimalHonestResidual
    (p : CM2Params) (C : Paper2Constants p) : Prop :=
  C.K = theorem13CriticalK p ∧
    (PrintedStrongLogisticCaseIV p C →
      2 - 2 * p.m < theorem13CriticalQStar p)

/-- The minimal residual upgrades the printed disjunction to the corrected
disjunction consumed by the proved interval energy estimates. -/
theorem correctedStrongLogisticCondition_of_minimalHonestResidual
    (p : CM2Params) (C : Paper2Constants p)
    (hres : IntervalDomainTheorem13MinimalHonestResidual p C)
    (hstrong : StrongLogisticCondition p C) :
    CorrectedStrongLogisticCondition p := by
  rcases hstrong with hI | hII | hIII | hIV
  · exact Or.inl hI
  · exact Or.inr (Or.inl hII)
  · refine Or.inr (Or.inr (Or.inl ⟨hIII.1, hIII.2.1, ?_⟩))
    rcases hIII.2.2 with hzero | hsmall
    · exact Or.inl hzero
    · exact Or.inr (by simpa [hres.1] using hsmall)
  · refine Or.inr (Or.inr (Or.inr ⟨hIV.1, hIV.2.1, ?_, ?_⟩))
    · exact hres.2 hIV
    · rcases hIV.2.2 with hzero | hsmall
      · exact Or.inl hzero
      · exact Or.inr (by simpa [hres.1] using hsmall)

/-- Exact repository Theorem 1.3 on the paper-faithful general-`m` interval
model.  All analytic/Cauchy fields from the old frontier bundle are gone; the
only residual is the statement correction above. -/
theorem Theorem_1_3_intervalDomainM_from_minimal_honest_residual
    (p : CM2Params) (C : Paper2Constants p)
    (hN : p.N = 1) (hχ : 0 < p.χ₀)
    (hres : IntervalDomainTheorem13MinimalHonestResidual p C) :
    Theorem_1_3 intervalDomainM p C := by
  intro ha hb _hm_pos hstrong
  have hcorrected : CorrectedStrongLogisticCondition p :=
    correctedStrongLogisticCondition_of_minimalHonestResidual p C hres hstrong
  have hheadline := correctedTheorem13_intervalDomainM p hN ha hb hχ hcorrected
  constructor
  · intro u0 hu0
    exact (hheadline.1 u0 hu0).1
  · intro hm_ge u0 hu0
    have hmax := hheadline.2 hm_ge u0 hu0
    obtain ⟨branch⟩ := hmax.1
    have hbranch := hmax.2 branch
    cases branch with
    | finite T u v hT hsol htrace halt hmge =>
        exact False.elim hbranch.1
    | global u v hglobal htrace =>
        exact ⟨u, v, hglobal, htrace, hbranch.2⟩

/-- There is no initial-layer counterexample for actual strong-logistic
solutions.  The trace-aware finite-horizon estimate controls the initial
window, while the autonomous global estimate controls the tail, yielding one
uniform supremum bound for every positive time. -/
theorem strongLogistic_global_allPositive_bound_from_minimal_honest_residual
    (p : CM2Params) (C : Paper2Constants p)
    (hN : p.N = 1) (hb : 0 < p.b) (hchi : 0 < p.χ₀)
    (hres : IntervalDomainTheorem13MinimalHonestResidual p C)
    (hstrong : StrongLogisticCondition p C)
    {u0 : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hu0 : PositiveInitialDatum intervalDomainM u0)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomainM p u v)
    (htrace : InitialTrace intervalDomainM u0 u) :
    ∃ M, ∀ t, 0 < t → intervalDomainM.supNorm (u t) ≤ M := by
  have hcorrected : CorrectedStrongLogisticCondition p :=
    correctedStrongLogisticCondition_of_minimalHonestResidual p C hres hstrong
  apply intervalDomainM_allPositive_bound_of_everyFinite_and_eventual
  · intro T hT
    exact boundedBefore_of_correctedStrongLogistic_positive_chi
      hN hb hu0 (hglobal.classical hT) htrace hchi hcorrected
  · exact boundedGlobal_of_correctedStrongLogistic_positive_chi
      hN hb hu0 hglobal htrace hchi hcorrected

/-! ## Compatibility closure for the legacy linear-flux domain -/

/-- Replace only the formal cross-diffusion exponent by one.  The faithful
`intervalDomainM` equation for this parameter record is exactly the legacy
`intervalDomain` equation for the original record. -/
def linearFluxParams (p : CM2Params) : CM2Params :=
  { p with m := 1, hm := zero_lt_one }

@[simp] theorem linearFluxParams_m (p : CM2Params) :
    (linearFluxParams p).m = 1 := rfl

@[simp] theorem linearFluxParams_N (p : CM2Params) :
    (linearFluxParams p).N = p.N := rfl

@[simp] theorem linearFluxParams_chi (p : CM2Params) :
    (linearFluxParams p).χ₀ = p.χ₀ := rfl

@[simp] theorem theorem13CriticalQStar_linearFluxParams (p : CM2Params) :
    theorem13CriticalQStar (linearFluxParams p) =
      theorem13CriticalQStar p := rfl

@[simp] theorem theorem13CriticalK_linearFluxParams (p : CM2Params) :
    theorem13CriticalK (linearFluxParams p) =
      theorem13CriticalK p := rfl

/-- On the legacy domain the solution predicate does not inspect `p.m`; its
flux is hard-coded to the linear power. -/
theorem classicalSolution_intervalDomain_linearFluxParams_iff
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ} :
    IsPaper2ClassicalSolution intervalDomain (linearFluxParams p) T u v ↔
      IsPaper2ClassicalSolution intervalDomain p T u v := by
  rfl

/-- The exact legacy `hProp25` field is unconditional for every stored `m`.
The legacy equation is linear-flux, and its exponent threshold is always at
least the threshold for the same parameter record relabelled by `m = 1`. -/
theorem Proposition_2_5_intervalDomain_legacy_unconditional
    (p : CM2Params) : Proposition_2_5 intervalDomain p := by
  intro u0 hu0 T hT u v hsol htrace P hthreshold hLp
  let q : CM2Params := linearFluxParams p
  have hN : (p.N : ℝ) < P :=
    (le_max_left (p.N : ℝ)
      (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ)))).trans_lt hthreshold
  have hgammaN : p.γ * (p.N : ℝ) < P :=
    ((le_max_right (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))).trans
      (le_max_right (p.N : ℝ)
        (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))))).trans_lt hthreshold
  have hthresholdQ :
      max (q.N : ℝ) (max (q.m * (q.N : ℝ)) (q.γ * (q.N : ℝ))) < P := by
    simpa [q, linearFluxParams] using max_lt hN (max_lt hN hgammaN)
  have hsolQ : IsPaper2ClassicalSolution intervalDomain q T u v :=
    classicalSolution_intervalDomain_linearFluxParams_iff.mpr hsol
  exact
    _root_.ShenWork.Paper2.IntervalDomainRestartedLpLinfProducer.Proposition_2_5_intervalDomain_of_restarted_affine
      (p := q) (by simp [q]) u0 hu0 T hT u v hsolQ htrace P hthresholdQ hLp

/-- In the global regime `m ≥ 1`, every printed strong-logistic alternative
for `p` implies a corrected alternative for the associated linear-flux
parameter record.  Critical constants matter only at `m = 1`; for `m > 1`
the two printed critical equalities become strict alternatives after setting
the actual flux exponent to one. -/
theorem correctedStrongLogisticCondition_linearFluxParams_of_m_ge_one
    (p : CM2Params) (C : Paper2Constants p)
    (hm_ge : 1 ≤ p.m)
    (hK : p.m = 1 → C.K = theorem13CriticalK p)
    (hstrong : StrongLogisticCondition p C) :
    CorrectedStrongLogisticCondition (linearFluxParams p) := by
  rcases hstrong with hI | hII | hIII | hIV
  · refine Or.inl ⟨hI.1, ?_⟩
    change 1 + p.γ - 1 < p.α
    linarith [hI.2]
  · refine Or.inr (Or.inl ⟨hII.1, ?_⟩)
    change 2 * 1 + p.γ - 2 < p.α
    linarith [hII.2]
  · by_cases hm_eq : p.m = 1
    · refine Or.inr (Or.inr (Or.inl ⟨hIII.1, ?_, ?_⟩))
      · simpa [linearFluxParams, hm_eq] using hIII.2.1
      · rcases hIII.2.2 with hzero | hsmall
        · exact Or.inl (by simpa [linearFluxParams] using hzero)
        · exact Or.inr (by
            simpa [linearFluxParams, hm_eq, hK hm_eq] using hsmall)
    · have hm_gt : 1 < p.m := lt_of_le_of_ne hm_ge (Ne.symm hm_eq)
      refine Or.inl ⟨hIII.1, ?_⟩
      change 1 + p.γ - 1 < p.α
      rw [hIII.2.1]
      linarith
  · by_cases hm_eq : p.m = 1
    · refine Or.inr (Or.inr (Or.inr ⟨hIV.1, ?_, ?_, ?_⟩))
      · simpa [linearFluxParams, hm_eq] using hIV.2.1
      · simpa [linearFluxParams] using
          theorem13CriticalQStar_pos (linearFluxParams p)
      · rcases hIV.2.2 with hzero | hsmall
        · exact Or.inl (by simpa [linearFluxParams] using hzero)
        · exact Or.inr (by
            simpa [linearFluxParams, hm_eq, hK hm_eq] using hsmall)
    · have hm_gt : 1 < p.m := lt_of_le_of_ne hm_ge (Ne.symm hm_eq)
      refine Or.inl ⟨(show 0 ≤ p.β by linarith [hIV.1]), ?_⟩
      change 1 + p.γ - 1 < p.α
      rw [hIV.2.1]
      linarith

/-- On the legacy linear-flux model the only remaining statement-level datum
is fidelity of the critical constant when the stored exponent is actually
`m = 1`.  If `m > 1`, the printed critical alternatives become strict for the
linear-flux equation and no critical constant is consumed. -/
def IntervalDomainTheorem13LegacyMinimalHonestResidual
    (p : CM2Params) (C : Paper2Constants p) : Prop :=
  p.m = 1 → C.K = theorem13CriticalK p

/-- Exact legacy `intervalDomain` Theorem 1.3 in the real one-dimensional,
positive-sensitivity regime.  Local bounded existence comes from the Picard
ball.  The global branch is constructed canonically on the equivalent
faithful `m = 1` equation, so the false arbitrary-tail `globalExtension`
frontier is absent. -/
theorem Theorem_1_3_intervalDomain_from_minimal_honest_residual
    (p : CM2Params) (C : Paper2Constants p)
    (hN : p.N = 1) (hχ : 0 < p.χ₀)
    (hres : IntervalDomainTheorem13LegacyMinimalHonestResidual p C) :
    Theorem_1_3 intervalDomain p C := by
  intro ha hb _hm_pos hstrong
  constructor
  · exact intervalDomain_localExistence_bounded_allExponents p
  · intro hm_ge u0 hu0
    let q : CM2Params := linearFluxParams p
    have hqN : q.N = 1 := by simpa [q] using hN
    have hqχ : 0 < q.χ₀ := by simpa [q] using hχ
    have hqb : 0 < q.b := by simpa [q] using hb
    have hqcorrected : CorrectedStrongLogisticCondition q := by
      simpa [q] using
        correctedStrongLogisticCondition_linearFluxParams_of_m_ge_one
          p C hm_ge hres hstrong
    have hu0M : PaperPositiveInitialDatum intervalDomainM u0 := by
      simpa [intervalDomainM, intervalDomain] using hu0
    have hheadline :=
      correctedTheorem13_intervalDomainM q hqN ha hqb hqχ hqcorrected
    have hmax := hheadline.2 (by simp [q]) u0 hu0M
    obtain ⟨branch⟩ := hmax.1
    have hbranch := hmax.2 branch
    cases branch with
    | finite T u v hT hsol htrace halt hmge =>
        exact False.elim hbranch.1
    | global u v hglobalM htraceM =>
        have hglobalQ :
            IsPaper2GlobalClassicalSolution intervalDomain q u v := by
          intro T hT
          exact ShenWork.Paper2.IntervalDomainM.classicalSolution_intervalDomain_of_m_eq_one
            (by simp [q]) (hglobalM.classical hT)
        have hglobalP :
            IsPaper2GlobalClassicalSolution intervalDomain p u v := by
          intro T hT
          exact classicalSolution_intervalDomain_linearFluxParams_iff.mp
            (hglobalQ.classical hT)
        have htraceP : InitialTrace intervalDomain u0 u := by
          simpa [intervalDomainM, intervalDomain] using htraceM
        have hboundedP : IsPaper2Bounded intervalDomain u := by
          simpa [intervalDomainM, intervalDomain] using hbranch.2
        exact ⟨u, v, hglobalP, htraceP, hboundedP⟩

#print axioms correctedStrongLogisticCondition_of_minimalHonestResidual
#print axioms Theorem_1_3_intervalDomainM_from_minimal_honest_residual
#print axioms strongLogistic_global_allPositive_bound_from_minimal_honest_residual
#print axioms correctedStrongLogisticCondition_linearFluxParams_of_m_ge_one
#print axioms Proposition_2_5_intervalDomain_legacy_unconditional
#print axioms Theorem_1_3_intervalDomain_from_minimal_honest_residual
#print axioms not_legacyTheorem13_interpolation_frontier
#print axioms not_IntervalDomainTheorem13FrontierData_of_real_regime

end ShenWork.Paper2.IntervalDomainTheorem13MinimalResidual

end
