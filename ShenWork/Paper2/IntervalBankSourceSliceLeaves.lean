/-
  Banked source-slice leaf producers for the conjugate Picard limit
  (general / negative-sensitivity case `χ₀ ≤ 0`).

  This file supplies the three remaining "leaf" producer lemmas that fill three
  fields of `BFormDirectClassical.BFormBankedInputs`:

  * field 9  `hlogCont`     — continuity of the constant-extended logistic source
                              slice of the limit;
  * field 10 `hlogFourier`  — `reflCircle` Fourier-`ℓ¹` summability of the same
                              logistic slice (via cosine-coefficient quadratic
                              decay ⟹ cosine-`ℓ¹` ⟹ Fourier-`ℓ¹`);
  * field 11 `hchemCont`    — continuity of the constant-extended chemotaxis
                              divergence slice of the limit.

  Every input is upstream of the three target fields: the existence data `DB`
  (for limit slice continuity), the PID positivity hypotheses
  (`huPaper/Hinf/hsmall`), and the per-slice restarted cosine representation of
  the limit (which the bank's `MInit/haInit/hlogSrc/hchemSrc/hB_global` produce
  through `hasRestartCosineRepresentations_of_BFormBankedInputs`).  Nothing here
  consumes the three target fields, so there is no circularity.
-/
import ShenWork.Paper2.IntervalBFormDirectClassical
import ShenWork.Paper2.IntervalDomainConstExtendAdapter
import ShenWork.Paper2.IntervalDomainLogisticWeakH2Adapter
import ShenWork.Paper2.IntervalDomainPdeUWiring
import ShenWork.Paper2.ChemMildHolderBootstrap

open Filter Topology Set

noncomputable section

namespace ShenWork.Paper2.BankSourceSliceLeaves

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint intervalDomainConstExtend
   intervalDomainChemotaxisDiv)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
open ShenWork.IntervalCosineInversion (reflCircle)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalMildPicardRegularity (logisticSourceFun)
open ShenWork.IntervalMildPicard (HasContinuousSlices HasJointMeasurability)
open ShenWork.Paper2 (PaperPositiveInitialDatum intervalLogisticSource_continuous)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceData ConjugatePicardInfThresholdData conjugatePicardLimit
   conjugatePicardLimit_pos_of_PID conjugatePicardIter conjugatePicardIter_ball
   conjugatePicardIter_geometric conjugatePicardLimit_hasContinuousSlices
   paperPositiveFloor)
open ShenWork.IntervalMildRegularityBootstrap
  (HasRestartCosineRepresentations RestartCosineRepresentation restartDuhamelCoeff
   restartDuhamelCoeff_eigenvalue_summable)
open ShenWork.HeatKernelGradientEstimates (heatGradientLinftyLinftyConstant)
open ShenWork.IntervalCoupledRegularityBootstrap (coupledChemicalConcentration)
open ShenWork.IntervalDomainLogisticWeakH2Adapter
  (logisticSource_cosineCoeff_quadratic_decay_of_representation)

/-! ## Helper: slice continuity of the limit from existence data -/

/-- The conjugate Picard limit has continuous spatial slices on `(0, DB.T]`,
extracted from the existence data `DB` exactly as in
`intervalConjugateMildSolution_of_data`. -/
theorem conjugatePicardLimit_hasContinuousSlices_of_data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀) :
    HasContinuousSlices DB.T (conjugatePicardLimit p u₀ DB.T) := by
  have hball_cont := fun n =>
    conjugatePicardIter_ball p u₀ DB.hbase_ball DB.hbase_nonneg DB.hbase_cont
      DB.hmapsTo DB.hmapsTo_nn DB.hcont_preserved DB.hbase_meas DB.hmeas_preserved n
  have hball := fun n => (hball_cont n).1
  have hball_nn := fun n => (hball_cont n).2.1
  have hcont_iterates := fun n => (hball_cont n).2.2
  have hmeas_iterates : ∀ n, HasJointMeasurability (conjugatePicardIter p u₀ n) := by
    intro n
    induction n with
    | zero => exact DB.hbase_meas
    | succ n ih => exact DB.hmeas_preserved _ ih
  have hgeom := conjugatePicardIter_geometric p u₀ DB.hK_nn hball hball_nn
    hcont_iterates hmeas_iterates DB.hcontr DB.hC₀ DB.hbase_diff
  exact conjugatePicardLimit_hasContinuousSlices p u₀ DB.hT DB.hK
    DB.hK_nn DB.hC₀ (fun n => hgeom n) hcont_iterates

/-! ## Helper: lift of the logistic source equals `logisticSourceFun` of the lift -/

/-- The zero-extension lift of the interval logistic source equals the
`logisticSourceFun` of the lift, as functions `ℝ → ℝ` (they agree on `[0,1]` by
unfolding, and both vanish off `[0,1]` since the lift vanishes there). -/
theorem lift_intervalLogisticSource_eq_logisticSourceFun
    (p : CM2Params) (w : intervalDomainPoint → ℝ) :
    intervalDomainLift (intervalLogisticSource p w)
      = logisticSourceFun p.a p.b p.α (intervalDomainLift w) := by
  funext x
  by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
  · simp only [intervalDomainLift, dif_pos hx, logisticSourceFun, intervalLogisticSource]
  · simp only [intervalDomainLift, dif_neg hx, logisticSourceFun]
    ring

/-! ## Field 9 — logistic slice continuity -/

/-- **Field 9 (`hlogCont`).**  For each interior time the constant extension of
the limit's logistic source slice is globally continuous, since the limit slice
is continuous (from `DB`) and the logistic source preserves continuity. -/
theorem coupledLogistic_constExtend_continuous_of_limit
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀) :
    ∀ t, 0 < t → t < DB.T →
      Continuous
        (intervalDomainConstExtend
          (intervalLogisticSource p ((conjugatePicardLimit p u₀ DB.T) t))) := by
  intro t ht htT
  have hcu : Continuous ((conjugatePicardLimit p u₀ DB.T) t) :=
    conjugatePicardLimit_hasContinuousSlices_of_data DB t ht htT.le
  exact ShenWork.IntervalDomain.constExtend_continuous
    (intervalLogisticSource_continuous hcu)

/-! ## Field 10 — logistic slice Fourier summability -/

/-- **Field 10 (`hlogFourier`).**  For each interior time the even-reflection
Fourier coefficients of the limit's constant-extended logistic source slice are
`ℓ¹`-summable.  The route is: the restarted cosine representation of the limit
slice gives weak-`H²`/Neumann data for the logistic source, hence quadratic
`C/(kπ)²` decay of its cosine coefficients (which equal the constant
extension's cosine coefficients), hence cosine-`ℓ¹`, hence — with field-9
continuity — `reflCircle` Fourier-`ℓ¹`. -/
theorem coupledLogistic_fourierCoeff_summable_of_limit
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀)
    (huPaper : PaperPositiveInitialDatum intervalDomain u₀)
    (Hinf : ConjugatePicardInfThresholdData p u₀ DB.T)
    (hsmall :
      |p.χ₀| * (heatGradientLinftyLinftyConstant *
          (2 * Real.sqrt DB.T) * Hinf.CQ)
        + DB.T * Hinf.CL ≤ paperPositiveFloor huPaper / 2)
    (HR : HasRestartCosineRepresentations DB.T (conjugatePicardLimit p u₀ DB.T)) :
    ∀ t, 0 < t → t < DB.T →
      Summable (fun n : ℤ =>
        fourierCoeff
          (reflCircle
            (intervalDomainConstExtend
              (intervalLogisticSource p
                ((conjugatePicardLimit p u₀ DB.T) t)))) n) := by
  intro t ht htT
  -- positivity of the limit slice on [0,1]
  have hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardLimit p u₀ DB.T t) x := by
    intro y hy
    simp only [intervalDomainLift, dif_pos hy]
    exact conjugatePicardLimit_pos_of_PID huPaper Hinf hsmall t ht htT.le ⟨y, hy⟩
  -- restarted cosine representation of the limit slice
  obtain ⟨R⟩ := HR t ht htT
  -- quadratic cosine-coefficient decay of the logistic source of the slice
  obtain ⟨C, hC, hdecay⟩ :=
    logisticSource_cosineCoeff_quadratic_decay_of_representation
      (a := p.a) (b := p.b) (α := p.α)
      (bc := restartDuhamelCoeff R.a₀ R.a R.τ)
      (restartDuhamelCoeff_eigenvalue_summable R.hτ R.ha₀ R.src)
      R.hagree hpos
  -- the constant-extension cosine coefficients equal those of the logistic source
  have hcoeff_eq : ∀ k : ℕ,
      cosineCoeffs
          (intervalDomainConstExtend
            (intervalLogisticSource p (conjugatePicardLimit p u₀ DB.T t))) k
        = cosineCoeffs
            (logisticSourceFun p.a p.b p.α
              (intervalDomainLift (conjugatePicardLimit p u₀ DB.T t))) k := by
    intro k
    rw [ShenWork.IntervalDomain.cosineCoeffs_constExtend_eq_lift,
      lift_intervalLogisticSource_eq_logisticSourceFun]
  -- cosine-ℓ¹ summability from the quadratic decay
  have hcos_sum : Summable (fun n : ℕ =>
      |cosineCoeffs
          (intervalDomainConstExtend
            (intervalLogisticSource p (conjugatePicardLimit p u₀ DB.T t))) n|) := by
    rw [← summable_nat_add_iff 1]
    -- majorant `C/((n+1)π)²`, summable, dominates the shifted decay bound
    have hmaj : Summable (fun n : ℕ => C / (((n : ℝ) + 1) * Real.pi) ^ 2) := by
      have hpi : Summable (fun n : ℕ =>
          (C / Real.pi ^ 2) * (1 / ((n : ℝ) + 1) ^ 2)) := by
        refine (Summable.mul_left _ ?_)
        have := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
        simpa using (summable_nat_add_iff (f := fun k : ℕ => 1 / (k : ℝ) ^ 2) 1).2 this
      refine hpi.congr (fun n => ?_)
      have hpi2 : Real.pi ^ 2 ≠ 0 := by positivity
      have hn1 : ((n : ℝ) + 1) ^ 2 ≠ 0 := by positivity
      rw [mul_pow]
      field_simp
    refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_) hmaj
    rw [hcoeff_eq (n + 1)]
    have hb := hdecay (n + 1) (Nat.le_add_left 1 n)
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hcast] at hb
    exact hb
  -- continuity of the constant-extended logistic slice (field 9)
  have hcont :=
    coupledLogistic_constExtend_continuous_of_limit DB t ht htT
  exact ShenWork.Paper2.PdeUWiring.fourierCoeff_reflCircle_summable_of_cosineCoeff_abs
    hcont hcos_sum

/-! ## Field 11 — chemotaxis-divergence slice continuity: STALL (false target)

The third leaf, `coupledChemDiv_constExtend_continuous_of_limit`, would assert

  `∀ t, 0 < t → t < DB.T →`
  `  Continuous (intervalDomainConstExtend`
  `    (fun x => intervalDomainChemotaxisDiv p ((conjugatePicardLimit p u₀ DB.T) t)`
  `      (coupledChemicalConcentration p (conjugatePicardLimit p u₀ DB.T) t) x))`

i.e. field 11 (`hchemCont`) of `BFormDirectClassical.BFormBankedInputs`.

This statement is FALSE at the endpoints `{0,1}` in general, so it is left as a
precise stall rather than faked.  Reason:

`intervalDomainChemotaxisDiv p u v x = deriv φ x.1` with
`φ y = intervalDomainLift u y * deriv (intervalDomainLift v) y
        / (1 + intervalDomainLift v y) ^ p.β`
(`IntervalDomain.lean:2923`).  Because `intervalDomainLift` is the
ZERO-extension, `φ` is identically `0` for `y ≤ 0`, so its left derivative at
`0` is `0`.  The right derivative is `lim_{y→0⁺} φ' y =
u(0) · v''(0) / (1+v(0)) ^ β` (using the Neumann fact `v'(0)=0` so the
`u·v'` and `v'`-quotient terms drop, leaving the `u·v''` term).  Since the
resolver `v = coupledChemicalConcentration = intervalNeumannResolverR p u`
has `v''(0) = -∑ₖ (v̂ₖ).re (kπ)² ≠ 0` generically, the one-sided derivatives
disagree, `φ` is non-differentiable at `0`, and Lean's `deriv φ 0 = 0`.

Hence the constant-extension representative `intervalDomainConstExtend
(fun x => intervalDomainChemotaxisDiv …)` takes the value `0` at `x = 0`, while
its interior limit `lim_{x→0⁺}` equals the nonzero `u(0) v''(0)/(1+v(0))^β`.
The two disagree, so the representative is discontinuous at the endpoint and
`Continuous (intervalDomainConstExtend …)` fails.

PRECISE MISSING INPUT.  To make field 11 true with THIS representative one
would need the endpoint compatibility `v''(0) = v''(1) = 0` for the resolver
slice — there is no such lemma (and it is generically false; the available
resolver facts are only `resolverR_deriv_at_zero/​one`, i.e. `v'(0)=v'(1)=0`,
in `ShenWork/PDE/IntervalResolverSpatialC2.lean:106,120`, NOT a second-derivative
endpoint vanishing).  The structurally correct fix is to change the consumer
`chemDivCosineFourierData_constExtend`
(`ShenWork/Paper2/IntervalBFormSpectralHchem.lean:55`) / the bank field
`hchemCont` so that the `ChemDivCosineFourierData.representative` is a
continuous function agreeing with `chemDivLift` only on the OPEN interval
`Ioo 0 1` (the cosine-inversion consumers
`chemDiv_cosineSeries_summable`/`chemDiv_cosineFourier_convergence`,
`IntervalBFormSpectralHchem.lean:84,105`, only ever evaluate at interior points
`hx : x.1 ∈ Ioo 0 1`), e.g. the constant extension of the GLOBALLY-smooth
interior surrogate `ψ y = U y · resolverGradReal p u y / (1 + V y)^β` whose
`deriv` agrees with `chemDivLift` on `Ioo 0 1`.  With the current
`constExtend (chemDiv)` representative the field is not provable. -/

end ShenWork.Paper2.BankSourceSliceLeaves

section Axioms

#print axioms
  ShenWork.Paper2.BankSourceSliceLeaves.coupledLogistic_constExtend_continuous_of_limit
#print axioms
  ShenWork.Paper2.BankSourceSliceLeaves.coupledLogistic_fourierCoeff_summable_of_limit

end Axioms
