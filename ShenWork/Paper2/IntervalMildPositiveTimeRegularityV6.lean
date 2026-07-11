import ShenWork.Paper2.IntervalBFormSpectralProviderDischarge
import ShenWork.Paper2.IntervalCarrySeamGradientContinuousOn
import ShenWork.PDE.IntervalCosineSliceRegularity

/-!
# Positive-time spatial regularity of a conjugate mild solution (shared `(C1)`)

This is the shared spatial-regularity crux for the χ₀<0 branch: from the
generic `ConjugateMildSolutionData` fields (`S.hcont`, `S.hbound`, `S.hpos`)
together with the two source-side leaves

* `hsrcB` — the B-form source `DuhamelSourceTimeC1` package, and
* `hB_restart` — the restart cosine representation of `S.u` near each interior
  time,

each interior slice `S.u σ` is `C²` on `[0,1]` with vanishing Neumann endpoint
derivatives, and its cosine coefficients are eigenvalue-weighted `ℓ¹`-summable.

The whole content of this file is *wiring* over the committed engines: the
eigenvalue-weighted summability of the restart coefficients comes from
`localRestartCoeff_eigenvalue_summable` (parabolic gain, no pointwise ladder),
and the `C²`+Neumann conclusion from `intervalDomainCosineSlice_conjunct7_unconditional`.
The restart base coefficient bound is discharged directly from slice continuity
(`continuousOn_intervalDomainLift_of_hasContinuousSlices`) and `S.hbound`, so no
circular appeal to the slice's own cosine series is made.

Both the HSpectral producer and the Jensen strict-positivity supersolution
import this file: it reduces their common spatial-regularity need to the single
pair of source-side leaves `{hsrcB, hB_restart}` (facet `(C2)`, the source
ladder and Duhamel representation).
-/

open Set Filter Topology
open scoped Topology

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalConjugatePicard (ConjugateMildSolutionData)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalBFormSpectral (bFormSourceCoeffs)

noncomputable section

namespace ShenWork.Paper2.IntervalMildPositiveTimeRegularityV6

/-- The restart cosine representation of `S.u` near each interior time, in the
form consumed below.  This is facet `(C2b)` — the Duhamel representation leaf. -/
def RestartRepresentation
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀) : Prop :=
  ∀ t₀, 0 < t₀ → t₀ < S.T →
    ∀ᶠ s in 𝓝 t₀, ∀ y : intervalDomainPoint,
      S.u s y =
        ∑' n,
          localRestartCoeff
            (cosineCoeffs (intervalDomainLift (S.u (t₀ / 2))))
            (fun σ n => bFormSourceCoeffs p S.u (t₀ / 2 + σ) n)
            (s - t₀ / 2) n * cosineMode n y.1

/-- The restart base coefficients `cosineCoeffs (lift (S.u τ))` are bounded by
`2 * S.M`, directly from slice continuity and boundedness — no cosine-series
circularity. -/
theorem restartBase_coeff_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀)
    {τ : ℝ} (hτ : 0 < τ) (hτT : τ < S.T) :
    ∀ k, |cosineCoeffs (intervalDomainLift (S.u τ)) k| ≤ 2 * S.M := by
  have hcontOn :
      ContinuousOn (intervalDomainLift (S.u τ)) (Set.Icc (0 : ℝ) 1) :=
    ShenWork.Paper2.IntervalCarrySeamGradientContinuousOn.continuousOn_intervalDomainLift_of_hasContinuousSlices
      S.hcont hτ hτT.le
  have hbdd : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |intervalDomainLift (S.u τ) x| ≤ S.M := by
    intro x hx
    rw [intervalDomainLift, dif_pos hx]
    exact S.hbound τ hτ hτT.le ⟨x, hx⟩
  exact ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
    hcontOn S.hM.le hbdd

/-- The interior-slice cosine realization plus eigenvalue-weighted `ℓ¹`
summability of its coefficients, wired from `{hsrcB, hB_restart}`. -/
theorem mildSlice_eigenvalueSummable_and_realization
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀)
    (hsrcB : DuhamelSourceTimeC1 (bFormSourceCoeffs p S.u))
    (hB_restart : RestartRepresentation S)
    {σ : ℝ} (hσ : 0 < σ) (hσT : σ < S.T) :
    ∃ bc : ℕ → ℝ,
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc n|) ∧
      Set.EqOn (intervalDomainLift (S.u σ))
        (fun x => ∑' n, bc n * cosineMode n x) (Set.Icc (0 : ℝ) 1) := by
  set τ : ℝ := σ / 2 with hτdef
  have hτpos : 0 < τ := by rw [hτdef]; linarith
  have hτT : τ < S.T := by rw [hτdef]; linarith
  have hσmτ : σ - τ = τ := by rw [hτdef]; ring
  set a₀ : ℕ → ℝ := cosineCoeffs (intervalDomainLift (S.u τ)) with ha₀def
  set a : ℝ → ℕ → ℝ := fun r n => bFormSourceCoeffs p S.u (τ + r) n with hadef
  have ha₀_bd : ∀ k, |a₀ k| ≤ 2 * S.M := restartBase_coeff_bound S hτpos hτT
  have srcShift : DuhamelSourceTimeC1 a := by
    simpa [a, add_comm] using
      ShenWork.IntervalDuhamelSourceShift.DuhamelSourceTimeC1.shift_nonneg
        hsrcB hτpos.le
  refine ⟨fun n => localRestartCoeff a₀ a (σ - τ) n, ?_, ?_⟩
  · rw [hσmτ]
    exact ShenWork.IntervalResolverSpectralJointC2Producer.localRestartCoeff_eigenvalue_summable
      (τ := τ) (M := 2 * S.M) (a₀ := a₀) (a := a) hτpos ha₀_bd srcShift
  · intro x hx
    have hrep := hB_restart σ hσ hσT
    have hrep_at : ∀ y : intervalDomainPoint,
        S.u σ y =
          ∑' n,
            localRestartCoeff
              (cosineCoeffs (intervalDomainLift (S.u (σ / 2))))
              (fun r n => bFormSourceCoeffs p S.u (σ / 2 + r) n)
              (σ - σ / 2) n * cosineMode n y.1 :=
      hrep.self_of_nhds
    have hval := hrep_at ⟨x, hx⟩
    rw [intervalDomainLift, dif_pos hx]
    simpa [a₀, a, τ, hτdef] using hval

/-- **Shared `(C1)` export.**  Each interior slice of a conjugate mild solution
is `C²` on `[0,1]` with vanishing Neumann endpoint derivatives, from the two
source-side leaves.  Imported by both the HSpectral producer and the Jensen
supersolution. -/
theorem mildSlice_contDiffOn_two_neumann
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀)
    (hsrcB : DuhamelSourceTimeC1 (bFormSourceCoeffs p S.u))
    (hB_restart : RestartRepresentation S)
    {σ : ℝ} (hσ : 0 < σ) (hσT : σ < S.T) :
    ContDiffOn ℝ 2 (intervalDomainLift (S.u σ)) (Set.Icc (0 : ℝ) 1)
      ∧ deriv (intervalDomainLift (S.u σ)) 0 = 0
      ∧ deriv (intervalDomainLift (S.u σ)) 1 = 0 := by
  obtain ⟨bc, hbsum, hagree⟩ :=
    mildSlice_eigenvalueSummable_and_realization S hsrcB hB_restart hσ hσT
  exact ShenWork.IntervalCosineSliceRegularity.intervalDomainCosineSlice_conjunct7_unconditional
    hbsum hagree

#print axioms mildSlice_contDiffOn_two_neumann

end ShenWork.Paper2.IntervalMildPositiveTimeRegularityV6
