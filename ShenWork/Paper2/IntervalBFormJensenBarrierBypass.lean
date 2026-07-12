import ShenWork.Paper2.IntervalBFormCron2CoefficientWeakTest
import ShenWork.Paper2.IntervalBFormCron2RegularNegativePartEnergyA3
import ShenWork.Paper2.IntervalBFormMassGronwallNonvanishing
import ShenWork.Paper2.IntervalChiNegTruncatedRestartStrictPosProducer
import ShenWork.PDE.IntervalFullKernelMass
import ShenWork.PDE.IntervalSemigroupConeAtoms
import Mathlib.Analysis.Convex.Integral

open Filter Topology Set MeasureTheory
open scoped Topology

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalNeumannFullKernel
  (intervalFullSemigroupOperator intervalNeumannFullKernel)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalBFormSpectral (bFormSourceCoeffs)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledLogisticSourceCoeffs)

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

/-!
Jensen bypass for the A4 `S_N(0)=0` stall.

The old squared-barrier comparison needs `squareHeatBarrier M f 0 = f^2`,
but the full-kernel semigroup in this repository is definitionally zero at
time `0`.  The bypass below never evaluates the semigroup at zero: it assumes a
positive restart time `s` and a positive increment `σ`, uses a discounted mild
lower bound at `s + σ`, and inserts Jensen only at `σ > 0`.
-/

/-- The positive-time Jensen inequality for the Neumann semigroup, in exactly
the shape used by the bypass.  The proof may be supplied either by the full
heat-kernel mass theorem or by the elliptic Green-kernel probability route; A4
only consumes this positive-time interface. -/
def FullKernelJensenInequality (f : ℝ → ℝ) : Prop :=
  ∀ ⦃σ x : ℝ⦄, 0 < σ →
    (intervalFullSemigroupOperator σ f x) ^ 2 ≤
      intervalFullSemigroupOperator σ (fun y => (f y) ^ 2) x

/-- Positive-time reaction-discounted mild lower bound.  This is the other
input of the bypass and is intentionally open-ended: it can be produced from
the mild formula, comparison, or the coefficient Duhamel route. -/
def ReactionDiscountedMildLower
    (D : ℝ) (u : ℝ → ℝ → ℝ) : Prop :=
  ∀ ⦃s σ x : ℝ⦄, 0 < σ →
    Real.exp (-D * σ) *
        intervalFullSemigroupOperator σ (fun y => u s y) x
      ≤ u (s + σ) x

/-- Jensen bypass for the lower barrier at positive increments:
`u(s+σ) ≥ e^{-Dσ} (Sσ f)^2`, provided `f^2 ≤ u(s)` after applying `Sσ`.
No statement here mentions or evaluates `S_N(0)`. -/
theorem jensen_discounted_square_heat_bypass
    {D s σ x : ℝ} {u : ℝ → ℝ → ℝ} {f : ℝ → ℝ}
    (hσ : 0 < σ)
    (hmild : ReactionDiscountedMildLower D u)
    (hjensen : FullKernelJensenInequality f)
    (hseed_after_heat :
      intervalFullSemigroupOperator σ (fun y => (f y) ^ 2) x ≤
        intervalFullSemigroupOperator σ (fun y => u s y) x) :
    Real.exp (-D * σ) * (intervalFullSemigroupOperator σ f x) ^ 2
      ≤ u (s + σ) x := by
  have hJ := hjensen hσ (x := x)
  have hchain :
      (intervalFullSemigroupOperator σ f x) ^ 2 ≤
        intervalFullSemigroupOperator σ (fun y => u s y) x :=
    hJ.trans hseed_after_heat
  exact (mul_le_mul_of_nonneg_left hchain (Real.exp_pos _).le).trans
    (hmild hσ)

/-- Strict positivity from the Jensen bypass.  The strict seed is positive
after `Sσ`, again only for `σ > 0`. -/
theorem strict_pos_of_jensen_discounted_bypass
    {D s σ x : ℝ} {u : ℝ → ℝ → ℝ} {f : ℝ → ℝ}
    (hσ : 0 < σ)
    (hmild : ReactionDiscountedMildLower D u)
    (hjensen : FullKernelJensenInequality f)
    (hseed_after_heat :
      intervalFullSemigroupOperator σ (fun y => (f y) ^ 2) x ≤
        intervalFullSemigroupOperator σ (fun y => u s y) x)
    (hS_pos : 0 < intervalFullSemigroupOperator σ f x) :
    0 < u (s + σ) x := by
  have hbar :
      Real.exp (-D * σ) * (intervalFullSemigroupOperator σ f x) ^ 2
        ≤ u (s + σ) x :=
    jensen_discounted_square_heat_bypass hσ hmild hjensen hseed_after_heat
  exact lt_of_lt_of_le (mul_pos (Real.exp_pos _) (sq_pos_of_pos hS_pos)) hbar

/-- The seed comparison `f^2 ≤ u(s)` passes through the positive-time Neumann
semigroup by kernel monotonicity. -/
theorem seed_after_heat_of_square_le_on_Icc
    {σ s x Mf Mu : ℝ} {u : ℝ → ℝ → ℝ} {f : ℝ → ℝ}
    (hσ : 0 < σ)
    (hf2_meas : AEStronglyMeasurable (fun y => (f y) ^ 2)
      (intervalMeasure 1))
    (hu_meas : AEStronglyMeasurable (fun y => u s y)
      (intervalMeasure 1))
    (hf2_bdd : ∀ y, |(f y) ^ 2| ≤ Mf)
    (hu_bdd : ∀ y, |u s y| ≤ Mu)
    (hseed : ∀ y ∈ Set.Icc (0 : ℝ) 1, (f y) ^ 2 ≤ u s y) :
    intervalFullSemigroupOperator σ (fun y => (f y) ^ 2) x ≤
      intervalFullSemigroupOperator σ (fun y => u s y) x :=
  ShenWork.IntervalSemigroupConeAtoms.intervalFullSemigroupOperator_mono_of_le_on_Icc
    hσ hf2_meas hu_meas hf2_bdd hu_bdd hseed x

/-- A `SquareHeatSeed` gives strict positivity of `Sσ f` for every positive
increment. -/
theorem heat_seed_strict_pos_of_squareHeatSeed
    {σ x : ℝ} {u₀ f : ℝ → ℝ}
    (hσ : 0 < σ) (hseed : SquareHeatSeed u₀ f) :
    0 < intervalFullSemigroupOperator σ f x :=
  intervalFullSemigroupOperator_pos_of_nonneg_nonzero hσ
    hseed.continuousOn hseed.nonneg hseed.pos_somewhere x

/-- The bypass comparison runs only on the open positive-increment strip
`0 < σ < T - s`. -/
theorem strict_pos_on_open_restart_strip_of_jensen_bypass
    {T D s : ℝ} {u : ℝ → ℝ → ℝ} {f : ℝ → ℝ}
    (hmild : ReactionDiscountedMildLower D u)
    (hjensen : FullKernelJensenInequality f)
    (hseed_after_heat :
      ∀ ⦃σ x : ℝ⦄, 0 < σ → σ < T - s →
        intervalFullSemigroupOperator σ (fun y => (f y) ^ 2) x ≤
          intervalFullSemigroupOperator σ (fun y => u s y) x)
    (hS_pos :
      ∀ ⦃σ x : ℝ⦄, 0 < σ → σ < T - s →
        0 < intervalFullSemigroupOperator σ f x) :
    ∀ ⦃σ x : ℝ⦄, 0 < σ → σ < T - s → 0 < u (s + σ) x := by
  intro σ x hσ hσT
  exact strict_pos_of_jensen_discounted_bypass hσ hmild hjensen
    (hseed_after_heat hσ hσT) (hS_pos hσ hσT)

/-! ### A1/A2/A3/A5 bridge fields -/

/-- A1: coefficient ODE and the tested `tsum` interchanges, specialized to the
negative-part test.  This constructor deliberately uses the spectral-series
fields already separated in `NegativePartCoefficientWeakTestData`. -/
def A1WeakTestFromSpectralSeries
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {t : ℝ}
    (H : NegativePartCoefficientWeakTestData p u t) :
    NegativePartWeakTestIdentityAt p u t :=
  negativePartWeakTestIdentityAt_of_coefficientData H

/-- A2: the scalar chain rule for `r ↦ (r_-)^2`; the derivative is
`-2 r_-`. -/
theorem A2_negativePart_sq_hasDerivAt (r : ℝ) :
    HasDerivAt (fun y : ℝ => (negativePart y)^2)
      (-2 * negativePart r) r :=
  negativePart_sq_hasDerivAt r

/-- A2: time-chain version of the same rule. -/
theorem A2_negativePart_sq_time_hasDerivAt
    {v : ℝ → ℝ} {t v' : ℝ} (hv : HasDerivAt v v' t) :
    HasDerivAt (fun s => (negativePart (v s))^2)
      ((-2 * negativePart (v t)) * v') t :=
  negativePart_sq_time_hasDerivAt hv

/-- A3: assemble Picard side fields with energy continuity and derivative
fields obtained by dominated convergence and the A2 chain rule. -/
def A3DataFromEnergyFields
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {E' : ℝ → ℝ}
    (energy_cont :
      ContinuousOn
        (negativePartEnergy
          (truncatedConjugatePicardLimit p u₀ DT.T))
        (Set.Icc (0 : ℝ) DT.T))
    (energy_has_deriv :
      ∀ t ∈ Set.Ico (0 : ℝ) DT.T,
        HasDerivWithinAt
          (negativePartEnergy
            (truncatedConjugatePicardLimit p u₀ DT.T))
          (E' t) (Set.Ici t) t) :
    TruncatedPicardNegativePartEnergyA3Data p (u₀ := u₀) DT.T E' := by
  let S := truncatedConjugateMildSolutionData_of_data DT
  refine
    { R := S.M
      hR := le_of_lt S.hM
      hcont := ?_
      hbound := ?_
      hu₀_adm := hu₀.admissible
      hu₀_nonneg := ?_
      htrace :=
        truncatedConjugatePicardLimit_initialTrace_of_truncated_data
          p hu₀.admissible.2 DT
      energy_cont := energy_cont
      energy_has_deriv := energy_has_deriv }
  · simpa [S] using S.hcont
  · intro t ht htT x
    simpa [S] using S.hbound t ht htT x
  · intro x
    have h :=
      positiveInitialDatum_intervalDomainLift_nonneg hu₀ x.1 x.2
    simpa [intervalDomainLift, x.2] using h

/-- A5: exact fields for mass equals the zeroth cosine/restart coefficient and
the logistic lower bound. -/
structure A5MassData
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (u : ℝ → intervalDomainPoint → ℝ) (aInit : ℕ → ℝ)
    (T C : ℝ) : Prop where
  hmassCoeff : ∀ t, 0 ≤ t → t ≤ T →
    intervalDomain.integral (u t) =
      localRestartCoeff aInit (bFormSourceCoeffs p u) t 0
  hAcont : ContinuousOn
    (fun t => localRestartCoeff aInit (bFormSourceCoeffs p u) t 0)
    (Icc (0 : ℝ) T)
  hsrcCont : ContinuousOn
    (fun t => bFormSourceCoeffs p u t 0) (Icc (0 : ℝ) T)
  hderiv0 : HasDerivWithinAt
    (fun t => localRestartCoeff aInit (bFormSourceCoeffs p u) t 0)
    (bFormSourceCoeffs p u 0 0) (Ici 0) 0
  hinitCoeff : aInit 0 = intervalDomain.integral u₀
  hinitMass : 0 < intervalDomain.integral u₀
  hchem0 : ∀ t ∈ Ico (0 : ℝ) T,
    coupledChemDivSourceCoeffs p u t 0 = 0
  hlogLower : ∀ t ∈ Ico (0 : ℝ) T,
    -C * localRestartCoeff aInit (bFormSourceCoeffs p u) t 0 ≤
      coupledLogisticSourceCoeffs p u t 0

/-- A5 constructor named by the intended provenance: zeroth coefficient identity
and logistic lower bound. -/
def A5MassDataFromZerothCoeffAndLogisticLower
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ} {aInit : ℕ → ℝ}
    {T C : ℝ}
    (hmassCoeff : ∀ t, 0 ≤ t → t ≤ T →
      intervalDomain.integral (u t) =
        localRestartCoeff aInit (bFormSourceCoeffs p u) t 0)
    (hAcont : ContinuousOn
      (fun t => localRestartCoeff aInit (bFormSourceCoeffs p u) t 0)
      (Icc (0 : ℝ) T))
    (hsrcCont : ContinuousOn
      (fun t => bFormSourceCoeffs p u t 0) (Icc (0 : ℝ) T))
    (hderiv0 : HasDerivWithinAt
      (fun t => localRestartCoeff aInit (bFormSourceCoeffs p u) t 0)
      (bFormSourceCoeffs p u 0 0) (Ici 0) 0)
    (hinitCoeff : aInit 0 = intervalDomain.integral u₀)
    (hinitMass : 0 < intervalDomain.integral u₀)
    (hchem0 : ∀ t ∈ Ico (0 : ℝ) T,
      coupledChemDivSourceCoeffs p u t 0 = 0)
    (hlogLower : ∀ t ∈ Ico (0 : ℝ) T,
      -C * localRestartCoeff aInit (bFormSourceCoeffs p u) t 0 ≤
        coupledLogisticSourceCoeffs p u t 0) :
    A5MassData p (u₀ := u₀) u aInit T C where
  hmassCoeff := hmassCoeff
  hAcont := hAcont
  hsrcCont := hsrcCont
  hderiv0 := hderiv0
  hinitCoeff := hinitCoeff
  hinitMass := hinitMass
  hchem0 := hchem0
  hlogLower := hlogLower

/-- A5 discharge through the scalar zeroth-mode Gronwall lemma. -/
theorem A5_mass_nonvanishing_from_fields
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ} {aInit : ℕ → ℝ}
    {T C : ℝ}
    (H : A5MassData p (u₀ := u₀) u aInit T C) :
    ∀ t, 0 < t → t ≤ T → 0 < intervalDomain.integral (u t) :=
  ShenWork.Paper2.truncatedBForm_mass_nonvanishing p H.hmassCoeff
    H.hAcont H.hsrcCont H.hderiv0 H.hinitCoeff H.hinitMass
    H.hchem0 H.hlogLower

end ShenWork.Paper2.BFormPositiveDatumNegPart
