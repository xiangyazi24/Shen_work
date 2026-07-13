/-
 Weak squared-heat barrier comparison for the faithful truncated Picard limit.

 The unknown trajectory is used only through its positive-time mild restart,
 bounded continuous slices, and the nonnegativity already proved by the
 energy producer. In particular this module does not reconstruct a
 pointwise time derivative or a classical second spatial derivative of the
 solution.
-/

import ShenWork.Paper2.IntervalTruncatedEnergyProducer
import ShenWork.Paper2.IntervalBFormSquareHeatT0RestartDerivativeData
import ShenWork.Paper2.IntervalMatchedDivergenceBarrierAtoms
import ShenWork.Paper2.IntervalResolverWeakODEBridge
import ShenWork.Paper2.IntervalChiNegCloseBaseSeed
import ShenWork.Paper2.IntervalTruncatedFluxC2Bounds
import ShenWork.PDE.IntervalFullKernelSecondDerivLinfty

open Filter Topology Set MeasureTheory
open scoped BigOperators Topology ENNReal

noncomputable section

namespace ShenWork.Paper2.IntervalTruncatedWeakBarrierComparison

open ShenWork.IntervalDomain
 (intervalDomain intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalNeumannFullKernel
 (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalConjugateDuhamelMap
 (intervalConjugateKernelOperator)
open ShenWork.Paper2.BFormPositiveDatumNegPart

private theorem negativePart_lipschitz_abs (r q : ℝ) :
 |negativePart r - negativePart q| ≤ |r - q| := by
 calc
 |negativePart r - negativePart q|
 = |positivePart (-r) - positivePart (-q)| := by rfl
 _ ≤ |-r - (-q)| := positivePart_lipschitz_abs (-r) (-q)
 _ = |r - q| := by
 rw [show -r - (-q) = -(r - q) by ring, abs_neg]

private theorem ae_mem_Ioo_unitInterval :
 ∀ᵐ x ∂intervalMeasure 1, x ∈ Set.Ioo (0 : ℝ) 1 := by
 rw [intervalMeasure, ShenWork.IntervalDomain.intervalSet, ae_iff,
 Measure.restrict_apply' measurableSet_Icc]
 refine measure_mono_null (t := ({0, 1} : Set ℝ)) (fun x hx => ?_) ?_
 · simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Icc] at hx
 obtain ⟨hnot, h0, h1⟩ := hx
 rcases eq_or_lt_of_le h0 with he0 | hl0
 · left
 exact he0.symm
 · rcases eq_or_lt_of_le h1 with he1 | hl1
 · right
 exact he1
 · exact absurd ⟨hl0, hl1⟩ hnot
 · exact Set.Finite.measure_zero ((Set.finite_singleton (1 : ℝ)).insert 0) volume

/-- A continuous unit-interval profile has square-summable normalized Neumann
cosine coefficients. This is the Bessel input used by the positive-time
squared-heat barrier calculus. -/
theorem cosineCoeffs_sq_summable_of_continuousOn
 {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1)) :
 Summable (fun n : ℕ => (cosineCoeffs f n) ^ 2) := by
 have h :=
 ShenWork.Paper2.ChiNegCloseBaseSeed.memHSigma_zero_of_continuousOn hf
 simpa [ShenWork.Paper2.HSigmaScale.memHSigma_zero] using h

/-- Uniform coefficient bound for a continuous bounded seed. -/
theorem cosineCoeffs_abs_le_of_continuous_bounded
 {f : ℝ → ℝ} {K : ℝ}
 (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
 (hK : 0 ≤ K) (hbound : ∀ x ∈ Set.Icc (0 : ℝ) 1, |f x| ≤ K) :
 ∀ n, |cosineCoeffs f n| ≤ 2 * K := by
 exact
 ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
 hf hK hbound

/-- Left continuity of a fixed spatial point of the faithful truncated limit.
The public time-slice theorem is restricted to the left filter used by the
backward mild energy argument. -/
theorem truncatedLimit_timeSlice_continuousWithinAt_Iio
 {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
 (DT : TruncatedConjugateMildExistenceData p u₀)
 {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T)
 (x : intervalDomainPoint) :
 ContinuousWithinAt
 (fun s => truncatedConjugatePicardLimit p u₀ DT.T s x)
 (Set.Iio t) t := by
 have hbase :=
 (ShenWork.Paper2.IntervalTruncatedEnergyProducer.truncatedLimit_timeSlice_continuousOn_Ioc
 DT x).continuousWithinAt
 (show t ∈ Set.Ioc (0 : ℝ) DT.T from ⟨ht, htT⟩)
 have hpos : Set.Ioi (t / 2) ∈ nhds t := Ioi_mem_nhds (by linarith)
 have hinter : Set.Iio t ∩ Set.Ioi (t / 2) ∈ nhdsWithin t (Set.Iio t) :=
 inter_mem_nhdsWithin _ hpos
 have hmem : Set.Ioc (0 : ℝ) DT.T ∈ nhdsWithin t (Set.Iio t) := by
 exact mem_of_superset hinter fun s hs =>
 ⟨lt_trans (by linarith : 0 < t / 2) hs.2,
 (le_of_lt hs.1).trans htT⟩
 exact hbase.mono_of_mem_nhdsWithin hmem

private def truncatedLogisticBound (p : CM2Params) (M : ℝ) : ℝ :=
 M * (p.a + p.b * M ^ p.α)

private theorem truncatedLogisticBound_nonneg
 (p : CM2Params) {M : ℝ} (hM : 0 ≤ M) :
 0 ≤ truncatedLogisticBound p M := by
 exact mul_nonneg hM
 (add_nonneg p.ha (mul_nonneg p.hb (Real.rpow_nonneg hM _)))

private theorem integrableOn_Icc_sub_rpow_neg_half_const
 (t K : ℝ) (ht : 0 ≤ t) :
 IntegrableOn (fun s : ℝ => K * (t - s) ^ (-(1 / 2) : ℝ))
 (Set.Icc (0 : ℝ) t) volume := by
 have h :=
 (ShenWork.IntervalGradDuhamelBound.intervalIntegrable_sub_rpow_neg_half t).const_mul K
 rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht] at h
 simpa [IntegrableOn, MeasureTheory.restrict_Ioc_eq_restrict_Icc] using h

private theorem truncatedLogisticLifted_abs_le
 (p : CM2Params) {M : ℝ} (hM : 0 ≤ M)
 {w : intervalDomainPoint → ℝ} (hw : ∀ x, |w x| ≤ M) :
 ∀ y, |truncatedLogisticLifted p w y| ≤ truncatedLogisticBound p M := by
 intro y
 have hlift : |intervalDomainLift w y| ≤ M := by
 by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
 · simpa [intervalDomainLift, hy] using hw ⟨y, hy⟩
 · simp [intervalDomainLift, hy, hM]
 have hpos : positivePart (intervalDomainLift w y) ≤ M := by
 have h := abs_positivePart_le_abs (intervalDomainLift w y)
 rw [abs_of_nonneg (positivePart_nonneg _)] at h
 exact h.trans hlift
 have hpow : positivePart (intervalDomainLift w y) ^ p.α ≤ M ^ p.α :=
 Real.rpow_le_rpow (positivePart_nonneg _) hpos p.hα.le
 have hinner :
 |p.a - p.b * positivePart (intervalDomainLift w y) ^ p.α| ≤
 p.a + p.b * M ^ p.α := by
 calc
 |p.a - p.b * positivePart (intervalDomainLift w y) ^ p.α|
 ≤ |p.a| + |p.b * positivePart (intervalDomainLift w y) ^ p.α| :=
 abs_sub _ _
 _ = p.a + p.b * positivePart (intervalDomainLift w y) ^ p.α := by
 rw [abs_of_nonneg p.ha, abs_mul, abs_of_nonneg p.hb,
 abs_of_nonneg (Real.rpow_nonneg (positivePart_nonneg _) _)]
 _ ≤ p.a + p.b * M ^ p.α :=
 add_le_add le_rfl (mul_le_mul_of_nonneg_left hpow p.hb)
 rw [truncatedLogisticLifted, truncatedLogisticLocal, abs_mul]
 exact mul_le_mul hlift hinner (abs_nonneg _) hM

private theorem truncatedLimit_logistic_aestronglyMeasurable
 {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
 (DT : TruncatedConjugateMildExistenceData p u₀) (s : ℝ) :
 AEStronglyMeasurable
 (truncatedLogisticLifted p
 ((truncatedConjugatePicardLimit p u₀ DT.T) s))
 (intervalMeasure 1) := by
 let U := truncatedConjugatePicardLimit p u₀ DT.T
 by_cases hs : 0 < s ∧ s ≤ DT.T
 · have hslice : Continuous (U s) := by
 simpa [U] using (truncatedConjugateMildSolutionData_of_data DT).hcont
 s hs.1 hs.2
 have hlift : ContinuousOn (intervalDomainLift (U s)) (Set.Icc (0 : ℝ) 1) := by
 rw [continuousOn_iff_continuous_restrict]
 have heq : Set.restrict (Set.Icc (0 : ℝ) 1) (intervalDomainLift (U s)) =
 U s := by
 funext ⟨x, hx⟩
 simp only [Set.restrict_apply, intervalDomainLift, dif_pos hx]
 exact congrArg _ (Subtype.ext rfl)
 rw [heq]
 exact hslice
 have hpos : ContinuousOn
 (fun y => positivePart (intervalDomainLift (U s) y))
 (Set.Icc (0 : ℝ) 1) := by
 intro y hy
 simpa [positivePart] using (hlift y hy).max continuousWithinAt_const
 have hsource : ContinuousOn (truncatedLogisticLifted p (U s))
 (Set.Icc (0 : ℝ) 1) := by
 have hpow := hpos.rpow_const (fun _ _ => Or.inr p.hα.le)
 simpa [truncatedLogisticLifted, truncatedLogisticLocal] using
 hlift.mul (continuousOn_const.sub (continuousOn_const.mul hpow))
 exact
 ShenWork.IntervalDuhamelIntegrability.continuousOn_aestronglyMeasurable_intervalMeasure
 hsource
 · have hzero : U s = fun _ => 0 := by
 funext x
 simp [U, truncatedConjugatePicardLimit, hs]
 change AEStronglyMeasurable (truncatedLogisticLifted p (U s))
 (intervalMeasure 1)
 rw [hzero]
 have hfun : truncatedLogisticLifted p (fun _ : intervalDomainPoint => 0) =
 fun _ => 0 := by
 funext y
 simp [truncatedLogisticLifted, truncatedLogisticLocal,
 intervalDomainLift, positivePart]
 rw [hfun]
 exact aestronglyMeasurable_const

private theorem truncatedLimit_flux_integrable
 {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
 (DT : TruncatedConjugateMildExistenceData p u₀) (s : ℝ) :
 Integrable
 (truncatedChemFluxLifted p
 ((truncatedConjugatePicardLimit p u₀ DT.T) s))
 (intervalMeasure 1) := by
 let U := truncatedConjugatePicardLimit p u₀ DT.T
 by_cases hs : 0 < s ∧ s ≤ DT.T
 · have hslice : Continuous (U s) := by
 simpa [U] using (truncatedConjugateMildSolutionData_of_data DT).hcont
 s hs.1 hs.2
 have hbound : ∀ x : intervalDomainPoint, |U s x| ≤ DT.M := by
 intro x
 simpa [U] using (truncatedConjugateMildSolutionData_of_data DT).hbound
 s hs.1 hs.2 x
 rw [truncatedChemFluxLifted_eq_chemFluxLifted_positivePartSlice]
 exact
 ShenWork.IntervalDuhamelIntegrability.chemFluxLifted_integrable_of_continuous
 p (fun x => (abs_positivePart_le_abs (U s x)).trans (hbound x))
 DT.hM.le (positivePartSlice_continuous hslice)
 (positivePartSlice_nonneg (U s))
 · have hzero : U s = fun _ => 0 := by
 funext x
 simp [U, truncatedConjugatePicardLimit, hs]
 change Integrable (truncatedChemFluxLifted p (U s)) (intervalMeasure 1)
 rw [hzero, truncatedChemFluxLifted_eq_chemFluxLifted_positivePartSlice]
 have hposzero : positivePartSlice (fun _ : intervalDomainPoint => 0) =
 fun _ => 0 := by
 funext x
 simp [positivePartSlice, positivePart]
 rw [hposzero]
 exact
 ShenWork.IntervalDuhamelIntegrability.chemFluxLifted_integrable_of_continuous
 p (M := 0) (by simp) le_rfl continuous_const (by simp)

private def truncatedResolverSourceDiffEnergy
 (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
 (DT : TruncatedConjugateMildExistenceData p u₀)
 (s t : ℝ) : ℝ :=
 let U := truncatedConjugatePicardLimit p u₀ DT.T
 ∫ y,
 (p.ν * positivePart (intervalDomainLift (U s) y) ^ p.γ -
 p.ν * positivePart (intervalDomainLift (U t) y) ^ p.γ) ^ 2
 ∂intervalMeasure 1

private theorem truncatedResolverSourceDiffEnergy_tendsto
 {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
 (DT : TruncatedConjugateMildExistenceData p u₀)
 {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T) :
 Tendsto (fun s => truncatedResolverSourceDiffEnergy p DT s t)
 (nhdsWithin t (Set.Iio t)) (nhds 0) := by
 let U := truncatedConjugatePicardLimit p u₀ DT.T
 let ρ : ℝ → ℝ → ℝ := fun s y =>
 p.ν * positivePart (intervalDomainLift (U s) y) ^ p.γ
 let F : ℝ → ℝ → ℝ := fun s y => (ρ s y - ρ t y) ^ 2
 let B : ℝ := (2 * (p.ν * DT.M ^ p.γ)) ^ 2
 have hsrc : 0 ≤ p.ν * DT.M ^ p.γ :=
 mul_nonneg p.hν.le (Real.rpow_nonneg DT.hM.le _)
 have hpos_event : ∀ᶠ s in nhdsWithin t (Set.Iio t), 0 < s := by
 have hnh : Set.Ioi (t / 2) ∈ nhds t := Ioi_mem_nhds (by linarith)
 filter_upwards
 [Filter.Eventually.filter_mono nhdsWithin_le_nhds hnh] with s hs
 exact lt_trans (half_pos ht) hs
 have hFmeas : ∀ᶠ s in nhdsWithin t (Set.Iio t),
 AEStronglyMeasurable (F s) (intervalMeasure 1) := by
 filter_upwards [self_mem_nhdsWithin, hpos_event] with s hst hs0
 have hsT : s ≤ DT.T := (le_of_lt hst).trans htT
 have hUs : ContinuousOn (intervalDomainLift (U s)) (Set.Icc (0 : ℝ) 1) :=
 ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity.intervalDomain_lift_continuousOn_Icc_of_continuous
 (by simpa [U] using
 (truncatedConjugateMildSolutionData_of_data DT).hcont s hs0 hsT)
 have hUt : ContinuousOn (intervalDomainLift (U t)) (Set.Icc (0 : ℝ) 1) :=
 ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity.intervalDomain_lift_continuousOn_Icc_of_continuous
 (by simpa [U] using
 (truncatedConjugateMildSolutionData_of_data DT).hcont t ht htT)
 have hp : Continuous (fun r : ℝ => positivePart r) := by
 simpa [positivePart] using continuous_id.max continuous_const
 have hρs : ContinuousOn (ρ s) (Set.Icc (0 : ℝ) 1) := by
 simpa [ρ] using continuousOn_const.mul
 ((hp.continuousOn.comp hUs (fun _ _ => Set.mem_univ _)).rpow_const
 (fun _ _ => Or.inr p.hγ.le))
 have hρt : ContinuousOn (ρ t) (Set.Icc (0 : ℝ) 1) := by
 simpa [ρ] using continuousOn_const.mul
 ((hp.continuousOn.comp hUt (fun _ _ => Set.mem_univ _)).rpow_const
 (fun _ _ => Or.inr p.hγ.le))
 exact
 ShenWork.IntervalDuhamelIntegrability.continuousOn_aestronglyMeasurable_intervalMeasure
 ((hρs.sub hρt).pow 2)
 have hFbound : ∀ᶠ s in nhdsWithin t (Set.Iio t),
 ∀ᵐ y ∂intervalMeasure 1, ‖F s y‖ ≤ B := by
 filter_upwards [self_mem_nhdsWithin, hpos_event] with s hst hs0
 have hsT : s ≤ DT.T := (le_of_lt hst).trans htT
 refine Filter.Eventually.of_forall fun y => ?_
 have hUbound : ∀ r, 0 < r → r ≤ DT.T →
 |intervalDomainLift (U r) y| ≤ DT.M := by
 intro r hr hrT
 by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
 · simpa [U, intervalDomainLift, hy] using
 (truncatedConjugateMildSolutionData_of_data DT).hbound
 r hr hrT ⟨y, hy⟩
 · simp [intervalDomainLift, hy, DT.hM.le]
 have hρbound : ∀ r, 0 < r → r ≤ DT.T →
 |ρ r y| ≤ p.ν * DT.M ^ p.γ := by
 intro r hr hrT
 have hp_le : positivePart (intervalDomainLift (U r) y) ≤ DT.M := by
 have h := abs_positivePart_le_abs (intervalDomainLift (U r) y)
 rw [abs_of_nonneg (positivePart_nonneg _)] at h
 exact h.trans (hUbound r hr hrT)
 have hpow := Real.rpow_le_rpow (positivePart_nonneg _) hp_le p.hγ.le
 change |p.ν * positivePart (intervalDomainLift (U r) y) ^ p.γ| ≤
 p.ν * DT.M ^ p.γ
 rw [abs_of_nonneg
 (mul_nonneg p.hν.le (Real.rpow_nonneg (positivePart_nonneg _) _))]
 exact mul_le_mul_of_nonneg_left hpow p.hν.le
 have hd : |ρ s y - ρ t y| ≤ 2 * (p.ν * DT.M ^ p.γ) := by
 calc
 |ρ s y - ρ t y| ≤ |ρ s y| + |ρ t y| := abs_sub _ _
 _ ≤ p.ν * DT.M ^ p.γ + p.ν * DT.M ^ p.γ :=
 add_le_add (hρbound s hs0 hsT) (hρbound t ht htT)
 _ = 2 * (p.ν * DT.M ^ p.γ) := by ring
 change ‖(ρ s y - ρ t y) ^ 2‖ ≤ B
 rw [Real.norm_eq_abs, abs_pow]
 exact pow_le_pow_left₀ (abs_nonneg _) hd 2
 have hFlim : ∀ᵐ y ∂intervalMeasure 1,
 Tendsto (fun s => F s y) (nhdsWithin t (Set.Iio t)) (nhds 0) := by
 filter_upwards [ae_mem_Ioo_unitInterval] with y hy
 have hyI : y ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hy
 let X : intervalDomainPoint := ⟨y, hyI⟩
 have hUlim : Tendsto (fun s => U s X) (nhdsWithin t (Set.Iio t))
 (nhds (U t X)) := by
 simpa [U] using
 (truncatedLimit_timeSlice_continuousWithinAt_Iio DT ht htT X)
 have hp : Continuous (fun r : ℝ => p.ν * positivePart r ^ p.γ) := by
 have hpp : Continuous (fun r : ℝ => positivePart r) := by
 simpa [positivePart] using continuous_id.max continuous_const
 exact continuous_const.mul
 (hpp.rpow_const (fun _ => Or.inr p.hγ.le))
 have hρlim : Tendsto (fun s => ρ s y) (nhdsWithin t (Set.Iio t))
 (nhds (ρ t y)) := by
 have hlift : ∀ r, intervalDomainLift (U r) y = U r X := by
 intro r
 simp [intervalDomainLift, hyI, X]
 simpa [ρ, hlift] using hp.continuousAt.tendsto.comp hUlim
 have hconst : Tendsto (fun _ : ℝ => ρ t y)
 (nhdsWithin t (Set.Iio t)) (nhds (ρ t y)) := tendsto_const_nhds
 simpa [F] using (hρlim.sub hconst).pow 2
 have hDCT := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
 (fun _ : ℝ => B) hFmeas hFbound (integrable_const _) hFlim
 simpa [truncatedResolverSourceDiffEnergy, U, ρ, F] using hDCT

private theorem intervalMeasure_integral_eq_intervalIntegral_energy
 (f : ℝ → ℝ) :
 (∫ y, f y ∂intervalMeasure 1) = ∫ y in (0 : ℝ)..1, f y := by
 simp only [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
 change (∫ y in Set.Icc (0 : ℝ) 1, f y ∂volume) =
 ∫ y in (0 : ℝ)..1, f y
 rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
 ← MeasureTheory.integral_Icc_eq_integral_Ioc]

/-! ## Weak generator identity for the concrete Neumann semigroup

The comparison must retain the heat dissipation. The next lemma differentiates
the spatial pairing only at positive heat time, integrates by parts using the
Neumann endpoint identities, and then passes to heat time zero by strong
continuity. No regularity of the nonlinear source is used here. -/

private theorem intervalFullSemigroup_time_hasDerivAt_laplacian_weak
 {q x : ℝ} (hq : 0 < q) {f : ℝ → ℝ} (hf : Continuous f)
 {K : ℝ} (hK : ∀ n, |cosineCoeffs f n| ≤ K)
 (hl2 : Summable fun n : ℕ => (cosineCoeffs f n) ^ 2)
 (hx : x ∈ Set.Icc (0 : ℝ) 1) :
 HasDerivAt (fun r : ℝ => intervalFullSemigroupOperator r f x)
 (ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianValue
 q (cosineCoeffs f) x) q := by
 have hcos :=
 ShenWork.RegularityBootstrap.unitIntervalCosineHeatValue_hasTimeDerivAt_of_l2
 (t := q) (x := x) hq hl2
 refine hcos.congr_of_eventuallyEq ?_
 filter_upwards [Ioi_mem_nhds hq] with r hr
 exact
 ShenWork.IntervalFullKernelSpectralClean.intervalFullSemigroupOperator_eq_cosineHeatValue_Icc
 (t := r) hr (f := f) hf (M := K) hK hx

private theorem intervalFullSemigroup_secondDeriv_eq_laplacian_weak
 {q x : ℝ} (hq : 0 < q) {f : ℝ → ℝ} (hf : Continuous f)
 {K : ℝ} (_hK : ∀ n, |cosineCoeffs f n| ≤ K)
 (hl2 : Summable fun n : ℕ => (cosineCoeffs f n) ^ 2)
 (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
 deriv (fun y : ℝ =>
 deriv (fun z : ℝ => intervalFullSemigroupOperator q f z) y) x =
 ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianValue
 q (cosineCoeffs f) x := by
 let H : ℝ → ℝ := fun z => intervalFullSemigroupOperator q f z
 let C : ℝ → ℝ := fun z =>
 unitIntervalCosineHeatValue q (cosineCoeffs f) z
 have hcos :
 HasDerivAt (fun y : ℝ => deriv C y)
 (ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianValue
 q (cosineCoeffs f) x) x := by
 simpa [C] using
 (ShenWork.RegularityBootstrap.unitIntervalCosineHeatValue_hasSecondSpatialDerivAt_of_l2
 (t := q) (x := x) hq (a := cosineCoeffs f) hl2)
 have hEqOn : Set.EqOn H C (Set.Ioo (0 : ℝ) 1) := by
 intro y hy
 exact
 ShenWork.IntervalFullKernelSpectralClean.intervalFullSemigroupOperator_eq_cosineHeatValue_clean
 (t := q) hq (f := f) hf hy
 have hderivEqOn : Set.EqOn (deriv H) (deriv C) (Set.Ioo (0 : ℝ) 1) := by
 intro y hy
 exact Filter.EventuallyEq.deriv_eq
 (Filter.eventuallyEq_of_mem (IsOpen.mem_nhds isOpen_Ioo hy) hEqOn)
 have hsem :
 HasDerivAt (fun y : ℝ => deriv H y)
 (ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianValue
 q (cosineCoeffs f) x) x := by
 refine hcos.congr_of_eventuallyEq ?_
 filter_upwards [IsOpen.mem_nhds isOpen_Ioo hx] with y hy
 exact hderivEqOn hy
 simpa [H] using hsem.deriv

private theorem intervalFullSemigroup_time_hasDerivAt_secondDeriv_weak
 {q x : ℝ} (hq : 0 < q) {f : ℝ → ℝ} (hf : Continuous f)
 {K : ℝ} (hK : ∀ n, |cosineCoeffs f n| ≤ K)
 (hl2 : Summable fun n : ℕ => (cosineCoeffs f n) ^ 2)
 (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
 HasDerivAt (fun r : ℝ => intervalFullSemigroupOperator r f x)
 (deriv (fun y : ℝ =>
 deriv (fun z : ℝ => intervalFullSemigroupOperator q f z) y) x) q := by
 rw [intervalFullSemigroup_secondDeriv_eq_laplacian_weak hq hf hK hl2 hx]
 exact intervalFullSemigroup_time_hasDerivAt_laplacian_weak hq hf hK hl2
 (Set.Ioo_subset_Icc_self hx)

theorem intervalFullSemigroup_pairing_hasDerivAt_dirichlet
 {f φ : ℝ → ℝ} {q Cf Cφ Gf Gφ : ℝ}
 (hq : 0 < q) (hf_cont : Continuous f)
 (hCf : 0 ≤ Cf) (hf_bound : ∀ y, |f y| ≤ Cf)
 (_hf_ac : AbsolutelyContinuousOnInterval f 0 1)
 (_hGf : 0 ≤ Gf) (_hf_deriv_bound : ∀ᵐ y ∂volume, |deriv f y| ≤ Gf)
 (hφcont : ContinuousOn φ (Set.Icc (0 : ℝ) 1))
 (hCφ : 0 ≤ Cφ) (hφbound : ∀ y, |φ y| ≤ Cφ)
 (hφ_ac : AbsolutelyContinuousOnInterval φ 0 1)
 (_hGφ : 0 ≤ Gφ) (_hφ_deriv_bound : ∀ᵐ y ∂volume, |deriv φ y| ≤ Gφ) :
 HasDerivAt
 (fun r => ∫ x, intervalFullSemigroupOperator r f x * φ x ∂intervalMeasure 1)
 (-(∫ x,
 deriv (fun z => intervalFullSemigroupOperator q f z) x * deriv φ x
 ∂intervalMeasure 1)) q := by
 let H : ℝ → ℝ := fun r =>
 ∫ x, intervalFullSemigroupOperator r f x * φ x ∂intervalMeasure 1
 let S : ℝ → ℝ := fun x => intervalFullSemigroupOperator q f x
 let Sxx : ℝ → ℝ := fun x => deriv (fun y => deriv S y) x
 have hf_meas : AEStronglyMeasurable f (intervalMeasure 1) :=
 hf_cont.aestronglyMeasurable
 have hφ_meas : AEStronglyMeasurable φ (intervalMeasure 1) :=
 ShenWork.IntervalDuhamelIntegrability.continuousOn_aestronglyMeasurable_intervalMeasure
 hφcont
 have hl2 : Summable fun n : ℕ => (cosineCoeffs f n) ^ 2 :=
 cosineCoeffs_sq_summable_of_continuousOn hf_cont.continuousOn
 have hcoeff : ∀ n, |cosineCoeffs f n| ≤ 2 * Cf :=
 cosineCoeffs_abs_le_of_continuous_bounded hf_cont.continuousOn hCf
 (fun x _hx => hf_bound x)
 haveI : IsFiniteMeasure (intervalMeasure 1) :=
 ⟨ShenWork.IntervalDomain.intervalMeasure_univ_lt_top 1⟩
 have hparam : HasDerivAt H (∫ x, Sxx x * φ x ∂intervalMeasure 1) q := by
 let C₂ : ℝ := (5 * Real.sqrt 2 / 2) * (q / 2) ^ (-(1 : ℝ)) * Cf * Cφ
 have hC₂ : 0 ≤ C₂ := by
 dsimp [C₂]
 positivity
 refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
 (F := fun r x => intervalFullSemigroupOperator r f x * φ x)
 (F' := fun r x =>
 deriv (fun y => deriv (fun z => intervalFullSemigroupOperator r f z) y) x * φ x)
 (bound := fun _ => C₂) (s := Set.Ioi (q / 2))
 (Ioi_mem_nhds (by linarith)) ?_ ?_ ?_ ?_ (integrable_const C₂) ?_).2
 · filter_upwards [Ioi_mem_nhds (half_lt_self hq)] with r hr
 exact
 (ShenWork.IntervalDuhamelIntegrability.intervalFullSemigroupOperator_continuous_of_bounded
 ((half_pos hq).trans hr) hCf hf_bound hf_meas).aestronglyMeasurable.mul
 hφ_meas
 · have hScont :=
 ShenWork.IntervalDuhamelIntegrability.intervalFullSemigroupOperator_continuous_of_bounded
 hq hCf hf_bound hf_meas
 have hSbound : ∀ x, |intervalFullSemigroupOperator q f x| ≤ Cf :=
 ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
 hq hCf hf_bound
 exact Integrable.of_bound (hScont.aestronglyMeasurable.mul hφ_meas)
 (Cf * Cφ) (Filter.Eventually.of_forall fun x => by
 rw [Real.norm_eq_abs, abs_mul]
 exact mul_le_mul (hSbound x) (hφbound x) (abs_nonneg _) hCf)
 · exact (measurable_deriv (fun x =>
 deriv (fun z => intervalFullSemigroupOperator q f z) x)).aestronglyMeasurable.mul
 hφ_meas
 · refine Filter.Eventually.of_forall fun x r hr => ?_
 have hrpos : 0 < r := (half_pos hq).trans hr
 have hinv : r ^ (-(1 : ℝ)) ≤ (q / 2) ^ (-(1 : ℝ)) := by
 rw [Real.rpow_neg_one, Real.rpow_neg_one]
 simpa [one_div] using one_div_le_one_div_of_le (half_pos hq) hr.le
 have hxx :=
 ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_secondDeriv_Linfty_pointwise_inv_t
 hrpos hf_meas hf_bound x
 rw [Real.norm_eq_abs, abs_mul]
 calc
 |deriv (fun y => deriv (fun z => intervalFullSemigroupOperator r f z) y) x| * |φ x|
 ≤ ((5 * Real.sqrt 2 / 2) * r ^ (-(1 : ℝ)) * Cf) * Cφ :=
 mul_le_mul hxx (hφbound x) (abs_nonneg _)
 (mul_nonneg (mul_nonneg (by positivity)
 (Real.rpow_nonneg hrpos.le _)) hCf)
 _ ≤ ((5 * Real.sqrt 2 / 2) * (q / 2) ^ (-(1 : ℝ)) * Cf) * Cφ := by
 gcongr
 _ = C₂ := by rfl
 · filter_upwards [ae_mem_Ioo_unitInterval] with x hx
 intro r hr
 have hrpos : 0 < r := (half_pos hq).trans hr
 exact
 (intervalFullSemigroup_time_hasDerivAt_secondDeriv_weak
 hrpos hf_cont hcoeff hl2 hx).mul_const (φ x)
 have hSderiv_ac : AbsolutelyContinuousOnInterval (deriv S) 0 1 := by
 let Cq : ℝ := (5 * Real.sqrt 2 / 2) * q ^ (-(1 : ℝ)) * Cf
 have hCq : 0 ≤ Cq := by dsimp [Cq]; positivity
 have hC2 : ContDiff ℝ 2 S := by
 simpa [S] using
 ShenWork.IntervalFullKernelSpectralClean.intervalFullSemigroupOperator_contDiff_two_clean
 hq hf_cont hcoeff
 have hhas : ∀ x ∈ Set.Icc (0 : ℝ) 1,
 HasDerivWithinAt (deriv S) (deriv (deriv S) x) (Set.Icc 0 1) x := by
 intro x _hx
 exact (((hC2.deriv' (n := 1)).differentiable
 (by norm_num : (1 : WithTop ℕ∞) ≠ 0)) x).hasDerivAt.hasDerivWithinAt
 have hbd : ∀ x ∈ Set.Icc (0 : ℝ) 1,
 ‖deriv (deriv S) x‖₊ ≤ ⟨Cq, hCq⟩ := by
 intro x _hx
 rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_mk, Real.norm_eq_abs]
 simpa [S, Cq] using
 (ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_secondDeriv_Linfty_pointwise_inv_t
 hq hf_meas hf_bound x)
 have hlip : LipschitzOnWith ⟨Cq, hCq⟩ (deriv S) (Set.Icc (0 : ℝ) 1) :=
 Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le (convex_Icc 0 1) hhas hbd
 have hlip_u : LipschitzOnWith ⟨Cq, hCq⟩ (deriv S)
 (Set.uIcc (0 : ℝ) 1) := by
 simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hlip
 exact hlip_u.absolutelyContinuousOnInterval
 have hIBP :
 (∫ x, Sxx x * φ x ∂intervalMeasure 1) =
 -(∫ x, deriv S x * deriv φ x ∂intervalMeasure 1) := by
 have hibp := hφ_ac.integral_mul_deriv_eq_deriv_mul hSderiv_ac
 have hS0 : deriv S 0 = 0 := by
 simpa [S] using
 ShenWork.IntervalSemigroupNeumann.intervalFullSemigroupOperator_neumann_at_zero
 hq hf_cont hcoeff
 have hS1 : deriv S 1 = 0 := by
 simpa [S] using
 ShenWork.IntervalSemigroupNeumann.intervalFullSemigroupOperator_neumann_at_one
 hq hf_cont hcoeff
 rw [intervalMeasure_integral_eq_intervalIntegral_energy,
 intervalMeasure_integral_eq_intervalIntegral_energy]
 calc
 (∫ x in (0 : ℝ)..1, Sxx x * φ x) =
 ∫ x in (0 : ℝ)..1, φ x * deriv (deriv S) x := by
 apply intervalIntegral.integral_congr
 intro x _hx
 simp only [Sxx]
 ring
 _ = φ 1 * deriv S 1 - φ 0 * deriv S 0 -
 ∫ x in (0 : ℝ)..1, deriv φ x * deriv S x := hibp
 _ = -(∫ x in (0 : ℝ)..1, deriv S x * deriv φ x) := by
 rw [hS0, hS1]
 simp only [mul_zero, sub_zero, zero_sub]
 apply congrArg Neg.neg
 apply intervalIntegral.integral_congr
 intro x _hx
 ring
 rw [hIBP] at hparam
 simpa [H, S] using hparam

/-- Finite-increment weak generator identity for the concrete Neumann heat
semigroup. The AC hypotheses on `f` are exactly what the positive-time
Lipschitz restart slice supplies; they make the Dirichlet tail uniformly
integrable down to heat time zero. -/
theorem intervalFullSemigroup_pairing_increment_eq_neg_dirichletTail
 {f φ : ℝ → ℝ} {h Cf Cφ Gf Gφ : ℝ}
 (hh : 0 < h) (hf_cont : Continuous f)
 (hCf : 0 ≤ Cf) (hf_bound : ∀ y, |f y| ≤ Cf)
 (hf_ac : AbsolutelyContinuousOnInterval f 0 1)
 (hGf : 0 ≤ Gf) (hf_deriv_bound : ∀ᵐ y ∂volume, |deriv f y| ≤ Gf)
 (hφcont : ContinuousOn φ (Set.Icc (0 : ℝ) 1))
 (hCφ : 0 ≤ Cφ) (hφbound : ∀ y, |φ y| ≤ Cφ)
 (hφ_ac : AbsolutelyContinuousOnInterval φ 0 1)
 (hGφ : 0 ≤ Gφ) (hφ_deriv_bound : ∀ᵐ y ∂volume, |deriv φ y| ≤ Gφ) :
 (∫ x, (intervalFullSemigroupOperator h f x - f x) * φ x
 ∂intervalMeasure 1) =
 -∫ q in (0 : ℝ)..h, (∫ x,
 deriv (fun z => intervalFullSemigroupOperator q f z) x * deriv φ x
 ∂intervalMeasure 1) := by
 let H : ℝ → ℝ := fun q =>
 ∫ x, intervalFullSemigroupOperator q f x * φ x ∂intervalMeasure 1
 let G : ℝ → ℝ := fun q => ∫ x,
 deriv (fun z => intervalFullSemigroupOperator q f z) x * deriv φ x
 ∂intervalMeasure 1
 have hf_meas : AEStronglyMeasurable f (intervalMeasure 1) :=
 hf_cont.aestronglyMeasurable
 have hφ_meas : AEStronglyMeasurable φ (intervalMeasure 1) :=
 ShenWork.IntervalDuhamelIntegrability.continuousOn_aestronglyMeasurable_intervalMeasure
 hφcont
 have hφderiv_μ : ∀ᵐ x ∂intervalMeasure 1, |deriv φ x| ≤ Gφ := by
 simp only [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
 exact hφ_deriv_bound.filter_mono ae_restrict_le
 have hHderiv : ∀ q, 0 < q → HasDerivAt H (-G q) q := by
 intro q hq
 simpa [H, G] using
 intervalFullSemigroup_pairing_hasDerivAt_dirichlet
 hq hf_cont hCf hf_bound hf_ac hGf hf_deriv_bound
 hφcont hCφ hφbound hφ_ac hGφ hφ_deriv_bound
 have hGbound : ∀ q, 0 < q → |G q| ≤ Gf * Gφ := by
 intro q hq
 have hSderiv_meas : AEStronglyMeasurable
 (fun x => deriv (fun z => intervalFullSemigroupOperator q f z) x)
 (intervalMeasure 1) :=
 (measurable_deriv (fun z => intervalFullSemigroupOperator q f z)).aestronglyMeasurable
 have hφderiv_meas : AEStronglyMeasurable (deriv φ) (intervalMeasure 1) :=
 (measurable_deriv φ).aestronglyMeasurable
 have hSbound : ∀ x,
 |deriv (fun z => intervalFullSemigroupOperator q f z) x| ≤ Gf :=
 ShenWork.Paper2.IntervalNegativePartWeakEnergy.abs_deriv_intervalFullSemigroupOperator_le_of_ac
 hq hf_meas hf_bound hf_ac hGf hf_deriv_bound
 have hprod_int : Integrable
 (fun x => deriv (fun z => intervalFullSemigroupOperator q f z) x * deriv φ x)
 (intervalMeasure 1) := by
 haveI : IsFiniteMeasure (intervalMeasure 1) :=
 ⟨ShenWork.IntervalDomain.intervalMeasure_univ_lt_top 1⟩
 exact Integrable.of_bound (hSderiv_meas.mul hφderiv_meas) (Gf * Gφ)
 (by
 filter_upwards [hφderiv_μ] with x hx
 rw [Real.norm_eq_abs, abs_mul]
 exact mul_le_mul (hSbound x) hx (abs_nonneg _) hGf)
 have hconst_int : Integrable (fun _ : ℝ => Gf * Gφ) (intervalMeasure 1) :=
 integrable_const _
 have hnorm := MeasureTheory.norm_integral_le_of_norm_le hconst_int
 (by
 filter_upwards [hφderiv_μ] with x hx
 rw [Real.norm_eq_abs, abs_mul]
 exact mul_le_mul (hSbound x) hx (abs_nonneg _) hGf)
 have hmass : (intervalMeasure 1).real Set.univ = 1 := by
 rw [intervalMeasure, ShenWork.IntervalDomain.intervalSet,
 measureReal_restrict_apply_univ, measureReal_def, Real.volume_Icc]
 simp
 rw [Real.norm_eq_abs, MeasureTheory.integral_const, hmass, one_smul] at hnorm
 simpa [G] using hnorm
 have hGii : IntervalIntegrable G volume 0 h := by
 rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hh.le]
 have hJint : IntegrableOn (deriv H) (Set.Ioc (0 : ℝ) h) volume := by
 have hJmeas : AEStronglyMeasurable (deriv H)
 (volume.restrict (Set.Ioc (0 : ℝ) h)) :=
 (measurable_deriv H).aestronglyMeasurable
 exact Integrable.of_bound hJmeas (Gf * Gφ) (by
 filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hq
 rw [(hHderiv q hq.1).deriv, Real.norm_eq_abs, abs_neg]
 exact hGbound q hq.1)
 apply hJint.neg.congr
 filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hq
 change -deriv H q = G q
 rw [(hHderiv q hq.1).deriv]
 simp
 have hprimitive : Tendsto (fun ε => ∫ q in (0 : ℝ)..ε, G q)
 (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds 0) := by
 have hcont := intervalIntegral.continuousOn_primitive_interval'
 hGii (show (0 : ℝ) ∈ Set.uIcc 0 h by simp [hh.le])
 have hmem : Set.uIcc (0 : ℝ) h ∈ nhdsWithin 0 (Set.Ioi (0 : ℝ)) := by
 rw [Set.uIcc_of_le hh.le]
 have hi : Set.Iio h ∈ nhds (0 : ℝ) := Iio_mem_nhds hh
 exact mem_of_superset (inter_mem_nhdsWithin _ hi) fun x hx =>
 ⟨hx.1.le, hx.2.le⟩
 have hc := (hcont.continuousWithinAt
 (show (0 : ℝ) ∈ Set.uIcc 0 h by simp [hh.le])).mono_of_mem_nhdsWithin hmem
 simpa using hc.tendsto
 have hHzero : Tendsto H (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
 (nhds (∫ x, f x * φ x ∂intervalMeasure 1)) := by
 let F : ℝ → ℝ → ℝ := fun q x =>
 intervalFullSemigroupOperator q f x * φ x
 have hFmeas : ∀ᶠ q in nhdsWithin 0 (Set.Ioi (0 : ℝ)),
 AEStronglyMeasurable (F q) (intervalMeasure 1) := by
 filter_upwards [self_mem_nhdsWithin] with q hq
 exact
 (ShenWork.IntervalDuhamelIntegrability.intervalFullSemigroupOperator_continuous_of_bounded
 hq hCf hf_bound hf_meas).aestronglyMeasurable.mul hφ_meas
 have hFbound : ∀ᶠ q in nhdsWithin 0 (Set.Ioi (0 : ℝ)),
 ∀ᵐ x ∂intervalMeasure 1, ‖F q x‖ ≤ Cf * Cφ := by
 filter_upwards [self_mem_nhdsWithin] with q hq
 have hSbound : ∀ x, |intervalFullSemigroupOperator q f x| ≤ Cf :=
 ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
 hq hCf hf_bound
 exact Filter.Eventually.of_forall fun x => by
 rw [Real.norm_eq_abs, abs_mul]
 exact mul_le_mul (hSbound x) (hφbound x) (abs_nonneg _) hCf
 have hFlim : ∀ᵐ x ∂intervalMeasure 1,
 Tendsto (fun q => F q x) (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
 (nhds (f x * φ x)) := by
 filter_upwards [ae_mem_Ioo_unitInterval] with x hx
 have hs :=
 (ShenWork.IntervalSemigroupUniform.intervalFullSemigroup_tendstoUniformlyOn
 f hf_cont).tendsto_at (Set.Ioo_subset_Icc_self hx)
 exact hs.mul_const (φ x)
 have hDCT := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
 (fun _ : ℝ => Cf * Cφ) hFmeas hFbound (integrable_const _) hFlim
 simpa [H, F] using hDCT
 have heq : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi (0 : ℝ)),
 H h - H ε =
 -(∫ q in (0 : ℝ)..h, G q) + ∫ q in (0 : ℝ)..ε, G q := by
 have heps : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi (0 : ℝ)), ε < h :=
 Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hh)
 filter_upwards [self_mem_nhdsWithin, heps] with ε hε hεh
 have h0ε : IntervalIntegrable G volume 0 ε :=
 hGii.mono_set (by
 rw [Set.uIcc_of_le hε.le, Set.uIcc_of_le hh.le]
 intro q hq
 exact ⟨hq.1, hq.2.trans hεh.le⟩)
 have hεhii : IntervalIntegrable G volume ε h :=
 hGii.mono_set (by
 rw [Set.uIcc_of_le hεh.le, Set.uIcc_of_le hh.le]
 intro q hq
 exact ⟨hε.le.trans hq.1, hq.2⟩)
 have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
 (f := H) (f' := fun q => -G q) (a := ε) (b := h)
 (fun q hq => by
 have hq' : q ∈ Set.Icc ε h := by
 simpa [Set.uIcc_of_le hεh.le] using hq
 exact hHderiv q (hε.trans_le hq'.1)) hεhii.neg
 rw [intervalIntegral.integral_neg] at hFTC
 have hadd := intervalIntegral.integral_add_adjacent_intervals h0ε hεhii
 linarith
 have hleft : Tendsto (fun ε => H h - H ε)
 (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
 (nhds (H h - ∫ x, f x * φ x ∂intervalMeasure 1)) :=
 tendsto_const_nhds.sub hHzero
 have hright : Tendsto
 (fun ε => -(∫ q in (0 : ℝ)..h, G q) + ∫ q in (0 : ℝ)..ε, G q)
 (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
 (nhds (-(∫ q in (0 : ℝ)..h, G q))) := by
 simpa using tendsto_const_nhds.add hprimitive
 have hright' : Tendsto (fun ε => H h - H ε)
 (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
 (nhds (-(∫ q in (0 : ℝ)..h, G q))) :=
 hright.congr' (heq.mono fun _ hε => hε.symm)
 have hlimit : H h - (∫ x, f x * φ x ∂intervalMeasure 1) =
 -(∫ q in (0 : ℝ)..h, G q) :=
 tendsto_nhds_unique hleft hright'
 have hSh_cont :=
 ShenWork.IntervalDuhamelIntegrability.intervalFullSemigroupOperator_continuous_of_bounded
 hh hCf hf_bound hf_meas
 have hSh_bound : ∀ x, |intervalFullSemigroupOperator h f x| ≤ Cf :=
 ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
 hh hCf hf_bound
 have hShφ : Integrable
 (fun x => intervalFullSemigroupOperator h f x * φ x) (intervalMeasure 1) := by
 haveI : IsFiniteMeasure (intervalMeasure 1) :=
 ⟨ShenWork.IntervalDomain.intervalMeasure_univ_lt_top 1⟩
 exact Integrable.of_bound (hSh_cont.aestronglyMeasurable.mul hφ_meas) (Cf * Cφ)
 (Filter.Eventually.of_forall fun x => by
 rw [Real.norm_eq_abs, abs_mul]
 exact mul_le_mul (hSh_bound x) (hφbound x) (abs_nonneg _) hCf)
 have hfφ : Integrable (fun x => f x * φ x) (intervalMeasure 1) := by
 haveI : IsFiniteMeasure (intervalMeasure 1) :=
 ⟨ShenWork.IntervalDomain.intervalMeasure_univ_lt_top 1⟩
 exact Integrable.of_bound (hf_meas.mul hφ_meas) (Cf * Cφ)
 (Filter.Eventually.of_forall fun x => by
 rw [Real.norm_eq_abs, abs_mul]
 exact mul_le_mul (hf_bound x) (hφbound x) (abs_nonneg _) hCf)
 rw [show (fun x => (intervalFullSemigroupOperator h f x - f x) * φ x) =
 fun x => intervalFullSemigroupOperator h f x * φ x - f x * φ x by
 funext x; ring,
 MeasureTheory.integral_sub hShφ hfφ]
 simpa [H, G] using hlimit

/-- Weak terminal residual of the positive squared-heat barrier. Its pairing
is differentiated without a pointwise Laplacian: the time increment and the
moving-source Neumann Dirichlet tail converge separately. -/
theorem squareHeatBarrier_remainder_pairing_tendsto
 {M t : ℝ} (ht : 0 < t)
 {f : ℝ → ℝ} (hf : Continuous f) {Cf K : ℝ} (hCf : 0 ≤ Cf)
 (hf_bound : ∀ y, |f y| ≤ Cf)
 (hK : ∀ n, |cosineCoeffs f n| ≤ K)
 (hl2 : Summable fun n : ℕ => (cosineCoeffs f n) ^ 2)
 {φ : ℝ → ℝ} {Cφ Gφ : ℝ}
 (hφcont : ContinuousOn φ (Set.Icc (0 : ℝ) 1))
 (hCφ : 0 ≤ Cφ) (hφbound : ∀ y, |φ y| ≤ Cφ)
 (hφac : AbsolutelyContinuousOnInterval φ 0 1)
 (hGφ : 0 ≤ Gφ)
 (hφ_deriv_bound : ∀ᵐ y ∂volume, |deriv φ y| ≤ Gφ) :
 Tendsto
 (fun q : ℝ => q⁻¹ * ∫ x,
 (squareHeatBarrier M f t x -
 intervalFullSemigroupOperator q
 (fun y => squareHeatBarrier M f (t - q) y) x) * φ x
 ∂intervalMeasure 1)
 (nhdsWithin 0 (Set.Ioi 0))
 (nhds ((∫ x,
 ShenWork.Paper2.IntervalMatchedDivergenceBarrierAtoms.barrierTimeDerivRep
 M f t x * φ x ∂intervalMeasure 1) +
 ∫ x,
 ShenWork.Paper2.IntervalMatchedDivergenceBarrierAtoms.barrierSpaceDerivRep
 M f t x * deriv φ x ∂intervalMeasure 1)) := by
 let W : ℝ → ℝ → ℝ := fun r x => squareHeatBarrier M f r x
 let TI : ℝ → ℝ := fun q => q⁻¹ * ∫ x,
 (W t x - W (t - q) x) * φ x ∂intervalMeasure 1
 let DI : ℝ → ℝ := fun q => q⁻¹ * ∫ r in (0 : ℝ)..q, ∫ x,
 deriv (fun z => intervalFullSemigroupOperator r (W (t - q)) z) x *
 deriv φ x ∂intervalMeasure 1
 let Lt : ℝ := ∫ x,
 ShenWork.Paper2.IntervalMatchedDivergenceBarrierAtoms.barrierTimeDerivRep
 M f t x * φ x ∂intervalMeasure 1
 let Lx : ℝ := ∫ x,
 ShenWork.Paper2.IntervalMatchedDivergenceBarrierAtoms.barrierSpaceDerivRep
 M f t x * deriv φ x ∂intervalMeasure 1
 have hφmeas : AEStronglyMeasurable φ (intervalMeasure 1) :=
 ShenWork.IntervalDuhamelIntegrability.continuousOn_aestronglyMeasurable_intervalMeasure
 hφcont
 have htime : Tendsto TI (nhdsWithin 0 (Set.Ioi 0)) (nhds Lt) := by
 simpa [TI, Lt, W] using
 (ShenWork.Paper2.IntervalMatchedDivergenceBarrierAtoms.squareHeatBarrier_timeIncrement_pairing_tendsto
 (M := M) ht hf hCf hf_bound hK hφmeas hCφ hφbound)
 have hspace : Tendsto DI (nhdsWithin 0 (Set.Ioi 0)) (nhds Lx) := by
 simpa [DI, Lx, W] using
 (ShenWork.Paper2.IntervalMatchedDivergenceBarrierAtoms.squareHeatBarrier_moving_dirichletAverage_tendsto
 (M := M) ht hf hCf hf_bound hK hl2 hGφ hφ_deriv_bound)
 have hsum : Tendsto (fun q => TI q + DI q)
 (nhdsWithin 0 (Set.Ioi 0)) (nhds (Lt + Lx)) := htime.add hspace
 refine hsum.congr' ?_
 have hsmall : ∀ᶠ q in nhdsWithin 0 (Set.Ioi 0), q < t :=
 Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds ht)
 filter_upwards [self_mem_nhdsWithin, hsmall] with q hq hqt
 have hqpos : 0 < q := hq
 have htq : 0 < t - q := sub_pos.mpr hqt
 let Cq : ℝ := Real.exp (-M * (t - q)) * Cf ^ 2
 let Gq : ℝ := Real.exp (-M * (t - q)) *
 (2 * Cf *
 (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
 (t - q) ^ (-(1 / 2) : ℝ) * Cf))
 have hCq : 0 ≤ Cq := mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
 have hCg : 0 ≤
 ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant :=
 ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
 have hGq : 0 ≤ Gq := by
 dsimp [Gq]
 positivity
 have hregq :=
 ShenWork.Paper2.IntervalMatchedDivergenceBarrierAtoms.squareHeatBarrierSliceRegularData_of_semigroup
 (M := M) htq hf hCf hf_bound hK hl2
 have hSq : ∀ x, |intervalFullSemigroupOperator (t - q) f x| ≤ Cf :=
 ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
 htq hCf hf_bound
 have hWqbound : ∀ x, |W (t - q) x| ≤ Cq := by
 intro x
 dsimp [W, Cq, squareHeatBarrier]
 rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_pow]
 exact mul_le_mul_of_nonneg_left
 (pow_le_pow_left₀ (abs_nonneg _) (hSq x) 2) (Real.exp_pos _).le
 have hWqderiv : ∀ᵐ x ∂volume, |deriv (W (t - q)) x| ≤ Gq := by
 filter_upwards [] with x
 simpa [W, Gq] using
 (ShenWork.Paper2.IntervalMatchedDivergenceBarrierAtoms.squareHeatBarrier_deriv_abs_le_global
 (M := M) htq hCf hf.aestronglyMeasurable hf_bound (x := x))
 have hinc := intervalFullSemigroup_pairing_increment_eq_neg_dirichletTail
 (f := W (t - q)) (φ := φ) (h := q) (Cf := Cq) (Cφ := Cφ)
 (Gf := Gq) (Gφ := Gφ) hqpos hregq.continuous hCq hWqbound
 hregq.absolutelyContinuous hGq hWqderiv hφcont hCφ hφbound hφac
 hGφ hφ_deriv_bound
 have hWtcont :=
 (ShenWork.Paper2.IntervalMatchedDivergenceBarrierAtoms.squareHeatBarrierSliceRegularData_of_semigroup
 (M := M) ht hf hCf hf_bound hK hl2).continuous
 have hSq_t : ∀ x, |intervalFullSemigroupOperator t f x| ≤ Cf :=
 ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
 ht hCf hf_bound
 let Ct : ℝ := Real.exp (-M * t) * Cf ^ 2
 have hCt : 0 ≤ Ct := mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
 have hWtbound : ∀ x, |W t x| ≤ Ct := by
 intro x
 dsimp [W, Ct, squareHeatBarrier]
 rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_pow]
 exact mul_le_mul_of_nonneg_left
 (pow_le_pow_left₀ (abs_nonneg _) (hSq_t x) 2) (Real.exp_pos _).le
 have hSWqcont :=
 ShenWork.IntervalDuhamelIntegrability.intervalFullSemigroupOperator_continuous_of_bounded
 hqpos hCq hWqbound hregq.continuous.aestronglyMeasurable
 have hSWqbound : ∀ x,
 |intervalFullSemigroupOperator q (W (t - q)) x| ≤ Cq :=
 ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
 hqpos hCq hWqbound
 have htimeint : Integrable (fun x => (W t x - W (t - q) x) * φ x)
 (intervalMeasure 1) := by
 haveI : IsFiniteMeasure (intervalMeasure 1) :=
 ⟨ShenWork.IntervalDomain.intervalMeasure_univ_lt_top 1⟩
 exact Integrable.of_bound
 ((hWtcont.aestronglyMeasurable.sub hregq.continuous.aestronglyMeasurable).mul
 hφmeas) ((Ct + Cq) * Cφ) (by
 filter_upwards [] with x
 rw [Real.norm_eq_abs, abs_mul]
 exact mul_le_mul
 ((abs_sub _ _).trans (add_le_add (hWtbound x) (hWqbound x)))
 (hφbound x) (abs_nonneg _) (add_nonneg hCt hCq))
 have hincint : Integrable
 (fun x => (intervalFullSemigroupOperator q (W (t - q)) x -
 W (t - q) x) * φ x) (intervalMeasure 1) := by
 haveI : IsFiniteMeasure (intervalMeasure 1) :=
 ⟨ShenWork.IntervalDomain.intervalMeasure_univ_lt_top 1⟩
 exact Integrable.of_bound
 ((hSWqcont.aestronglyMeasurable.sub hregq.continuous.aestronglyMeasurable).mul
 hφmeas) ((Cq + Cq) * Cφ) (by
 filter_upwards [] with x
 rw [Real.norm_eq_abs, abs_mul]
 exact mul_le_mul
 ((abs_sub _ _).trans (add_le_add (hSWqbound x) (hWqbound x)))
 (hφbound x) (abs_nonneg _) (add_nonneg hCq hCq))
 have hsplit :
 (∫ x, (W t x - intervalFullSemigroupOperator q (W (t - q)) x) * φ x
 ∂intervalMeasure 1) =
 (∫ x, (W t x - W (t - q) x) * φ x ∂intervalMeasure 1) -
 ∫ x, (intervalFullSemigroupOperator q (W (t - q)) x -
 W (t - q) x) * φ x ∂intervalMeasure 1 := by
 rw [← MeasureTheory.integral_sub htimeint hincint]
 apply integral_congr_ae
 filter_upwards [] with x
 ring
 symm
 dsimp [TI, DI]
 rw [hsplit, hinc]
 ring

private theorem truncatedResolver_diff_le_sourceEnergy
 {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
 (DT : TruncatedConjugateMildExistenceData p u₀)
 {s t y : ℝ} (hs : 0 < s) (hsT : s ≤ DT.T)
 (ht : 0 < t) (htT : t ≤ DT.T) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
 let U := truncatedConjugatePicardLimit p u₀ DT.T
 let ws := positivePartSlice (U s)
 let wt := positivePartSlice (U t)
 |resolverGradReal p ws y - resolverGradReal p wt y| ≤
 Real.sqrt (∑' k : ℕ,
 (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
 Real.sqrt (4 * truncatedResolverSourceDiffEnergy p DT s t) ∧
 |ShenWork.PDE.intervalNeumannResolverR p ws ⟨y, hy⟩ -
 ShenWork.PDE.intervalNeumannResolverR p wt ⟨y, hy⟩| ≤
 Real.sqrt (∑' k : ℕ,
 (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2) *
 Real.sqrt (4 * truncatedResolverSourceDiffEnergy p DT s t) := by
 let U := truncatedConjugatePicardLimit p u₀ DT.T
 let ws := positivePartSlice (U s)
 let wt := positivePartSlice (U t)
 have hws_cont : Continuous ws := positivePartSlice_continuous (by
 simpa [U] using
 (truncatedConjugateMildSolutionData_of_data DT).hcont s hs hsT)
 have hwt_cont : Continuous wt := positivePartSlice_continuous (by
 simpa [U] using
 (truncatedConjugateMildSolutionData_of_data DT).hcont t ht htT)
 have hws_lift : ContinuousOn (intervalDomainLift ws) (Set.Icc (0 : ℝ) 1) :=
 ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity.intervalDomain_lift_continuousOn_Icc_of_continuous
 hws_cont
 have hwt_lift : ContinuousOn (intervalDomainLift wt) (Set.Icc (0 : ℝ) 1) :=
 ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity.intervalDomain_lift_continuousOn_Icc_of_continuous
 hwt_cont
 have hsrcs : ContinuousOn
 (fun x : ℝ => p.ν * intervalDomainLift ws x ^ p.γ)
 (Set.Icc (0 : ℝ) 1) :=
 continuousOn_const.mul
 (hws_lift.rpow_const (fun _ _ => Or.inr p.hγ.le))
 have hsrct : ContinuousOn
 (fun x : ℝ => p.ν * intervalDomainLift wt x ^ p.γ)
 (Set.Icc (0 : ℝ) 1) :=
 continuousOn_const.mul
 (hwt_lift.rpow_const (fun _ _ => Or.inr p.hγ.le))
 have henergy :=
 ShenWork.IntervalResolverWeakBounds.sourceCoeff_diff_energy_le_integral_of_continuousOn
 p hsrcs hsrct
 have hInt : (∫ x in (0 : ℝ)..1,
 (p.ν * intervalDomainLift ws x ^ p.γ -
 p.ν * intervalDomainLift wt x ^ p.γ) ^ 2) =
 truncatedResolverSourceDiffEnergy p DT s t := by
 rw [← intervalMeasure_integral_eq_intervalIntegral_energy]
 unfold truncatedResolverSourceDiffEnergy
 apply integral_congr_ae
 exact Filter.Eventually.of_forall fun x => by
 simp only [ws, wt]
 rw [intervalDomainLift_positivePartSlice,
 intervalDomainLift_positivePartSlice]
 rw [hInt] at henergy
 let A : ℕ → ℂ := fun k =>
 ShenWork.PDE.intervalNeumannResolverSourceCoeff p ws k -
 ShenWork.PDE.intervalNeumannResolverSourceCoeff p wt k
 have hA : ShenWork.PDE.ResolventEstimate.coeffL2Norm A ≤
 Real.sqrt (4 * truncatedResolverSourceDiffEnergy p DT s t) := by
 rw [ShenWork.PDE.ResolventEstimate.coeffL2Norm]
 exact Real.sqrt_le_sqrt henergy
 have hdiff :=
 ShenWork.IntervalResolverWeakBounds.resolverSourceCoeff_diff_re_sq_summable_of_continuousOn
 p hws_lift hwt_lift
 have hl2s : Summable (fun k : ℕ =>
 ((ShenWork.PDE.intervalNeumannResolverSourceCoeff p ws k).re) ^ 2) := by
 simpa [ShenWork.Paper2.intervalNeumannResolverSourceCoeff_zero, sub_zero] using
 ShenWork.IntervalResolverWeakBounds.resolverSourceCoeff_re_sq_summable_of_continuousOn
 p hws_lift
 have hl2t : Summable (fun k : ℕ =>
 ((ShenWork.PDE.intervalNeumannResolverSourceCoeff p wt k).re) ^ 2) := by
 simpa [ShenWork.Paper2.intervalNeumannResolverSourceCoeff_zero, sub_zero] using
 ShenWork.IntervalResolverWeakBounds.resolverSourceCoeff_re_sq_summable_of_continuousOn
 p hwt_lift
 let Y : intervalDomainPoint := ⟨y, hy⟩
 have hgrad := ShenWork.PDE.intervalNeumannResolverR_grad_sup_lipschitz
 p ws wt hdiff Y
 (ShenWork.IntervalResolverWeakBounds.resolver_sineSeries_summable_of_sourceL2
 p hl2s y)
 (ShenWork.IntervalResolverWeakBounds.resolver_sineSeries_summable_of_sourceL2
 p hl2t y)
 have hval := ShenWork.PDE.intervalNeumannResolverR_sup_lipschitz
 p ws wt hdiff Y
 (ShenWork.IntervalResolverWeakBounds.resolver_cosineSeries_summable_of_sourceL2
 p hl2s y)
 (ShenWork.IntervalResolverWeakBounds.resolver_cosineSeries_summable_of_sourceL2
 p hl2t y)
 rw [← resolverGradReal_eq p ws Y, ← resolverGradReal_eq p wt Y] at hgrad
 constructor
 · exact hgrad.trans (mul_le_mul_of_nonneg_left hA (Real.sqrt_nonneg _))
 · exact hval.trans (mul_le_mul_of_nonneg_left hA (Real.sqrt_nonneg _))

/-- Strong left-time `L¹` continuity of the faithful truncated chemotaxis
flux. -/
theorem truncatedLimit_flux_sub_integral_tendsto_zero
 {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
 (DT : TruncatedConjugateMildExistenceData p u₀)
 {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T) :
 Tendsto
 (fun s => ∫ y,
 |truncatedChemFluxLifted p
 ((truncatedConjugatePicardLimit p u₀ DT.T) s) y -
 truncatedChemFluxLifted p
 ((truncatedConjugatePicardLimit p u₀ DT.T) t) y|
 ∂intervalMeasure 1)
 (nhdsWithin t (Set.Iio t)) (nhds 0) := by
 let U := truncatedConjugatePicardLimit p u₀ DT.T
 let Q : ℝ → ℝ → ℝ := fun s => truncatedChemFluxLifted p (U s)
 let E : ℝ → ℝ := fun s => truncatedResolverSourceDiffEnergy p DT s t
 let Cg : ℝ := Real.sqrt (∑' k : ℕ,
 (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2)
 let Cr : ℝ := Real.sqrt (∑' k : ℕ,
 (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2)
 let CQ : ℝ := DT.M * (Cg * (2 * (p.ν * DT.M ^ p.γ)))
 have hE : Tendsto E (nhdsWithin t (Set.Iio t)) (nhds 0) := by
 simpa [E] using truncatedResolverSourceDiffEnergy_tendsto DT ht htT
 have h4E : Tendsto (fun s => 4 * E s)
 (nhdsWithin t (Set.Iio t)) (nhds 0) := by
 simpa using tendsto_const_nhds.mul hE
 have hsqrt : Tendsto (fun s => Real.sqrt (4 * E s))
 (nhdsWithin t (Set.Iio t)) (nhds 0) := by
 simpa only [Function.comp_apply, Real.sqrt_zero] using
 (Real.continuous_sqrt.tendsto 0).comp h4E
 have hCgsqrt : Tendsto (fun s => Cg * Real.sqrt (4 * E s))
 (nhdsWithin t (Set.Iio t)) (nhds 0) := by
 simpa only [mul_zero] using (tendsto_const_nhds (x := Cg)).mul hsqrt
 have hCrsqrt : Tendsto (fun s => Cr * Real.sqrt (4 * E s))
 (nhdsWithin t (Set.Iio t)) (nhds 0) := by
 simpa only [mul_zero] using (tendsto_const_nhds (x := Cr)).mul hsqrt
 have hpos_event : ∀ᶠ s in nhdsWithin t (Set.Iio t), 0 < s := by
 have hnh : Set.Ioi (t / 2) ∈ nhds t := Ioi_mem_nhds (half_lt_self ht)
 filter_upwards
 [Filter.Eventually.filter_mono nhdsWithin_le_nhds hnh] with s hs
 exact (half_pos ht).trans hs
 have hQlim : ∀ᵐ y ∂intervalMeasure 1,
 Tendsto (fun s => Q s y) (nhdsWithin t (Set.Iio t))
 (nhds (Q t y)) := by
 filter_upwards [ae_mem_Ioo_unitInterval] with y hy
 have hyI : y ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hy
 let X : intervalDomainPoint := ⟨y, hyI⟩
 let w : ℝ → intervalDomainPoint → ℝ := fun s => positivePartSlice (U s)
 let A : ℝ → ℝ := fun s => positivePart (intervalDomainLift (U s) y)
 let G : ℝ → ℝ := fun s => resolverGradReal p (w s) y
 let R : ℝ → ℝ := fun s => intervalDomainLift
 (ShenWork.PDE.intervalNeumannResolverR p (w s)) y
 have hUlim : Tendsto (fun s => U s X) (nhdsWithin t (Set.Iio t))
 (nhds (U t X)) := by
 simpa [U] using
 (truncatedLimit_timeSlice_continuousWithinAt_Iio DT ht htT X)
 have hAlim : Tendsto A (nhdsWithin t (Set.Iio t)) (nhds (A t)) := by
 have hp : Continuous (fun r : ℝ => positivePart r) := by
 simpa [positivePart] using continuous_id.max continuous_const
 have hlift : ∀ s, intervalDomainLift (U s) y = U s X := by
 intro s
 simp [intervalDomainLift, hyI, X]
 simpa [A, hlift] using hp.continuousAt.tendsto.comp hUlim
 have hGdiff : ∀ᶠ s in nhdsWithin t (Set.Iio t),
 |G s - G t| ≤ Cg * Real.sqrt (4 * E s) := by
 filter_upwards [self_mem_nhdsWithin, hpos_event] with s hst hs0
 have hsT : s ≤ DT.T := (le_of_lt hst).trans htT
 simpa [G, w, Cg, E, U] using
 (truncatedResolver_diff_le_sourceEnergy DT hs0 hsT ht htT hyI).1
 have hGlim : Tendsto G (nhdsWithin t (Set.Iio t)) (nhds (G t)) := by
 rw [tendsto_iff_norm_sub_tendsto_zero]
 simpa [Real.norm_eq_abs] using squeeze_zero'
 (Filter.Eventually.of_forall fun s => abs_nonneg (G s - G t))
 hGdiff hCgsqrt
 have hRdiff : ∀ᶠ s in nhdsWithin t (Set.Iio t),
 |R s - R t| ≤ Cr * Real.sqrt (4 * E s) := by
 filter_upwards [self_mem_nhdsWithin, hpos_event] with s hst hs0
 have hsT : s ≤ DT.T := (le_of_lt hst).trans htT
 simpa [R, w, Cr, E, U, intervalDomainLift, hyI] using
 (truncatedResolver_diff_le_sourceEnergy DT hs0 hsT ht htT hyI).2
 have hRlim : Tendsto R (nhdsWithin t (Set.Iio t)) (nhds (R t)) := by
 rw [tendsto_iff_norm_sub_tendsto_zero]
 simpa [Real.norm_eq_abs] using squeeze_zero'
 (Filter.Eventually.of_forall fun s => abs_nonneg (R s - R t))
 hRdiff hCrsqrt
 have hUt_cont : Continuous (U t) := by
 simpa [U] using
 (truncatedConjugateMildSolutionData_of_data DT).hcont t ht htT
 have hRt : 0 ≤ R t := by
 simpa [R, w, U, positivePartSlice] using
 _root_.ShenWork.Paper2.TruncatedPositiveTimeBootstrap.resolverR_positivePart_lift_nonneg_of_continuous
 p hUt_cont y
 have hdenlim : Tendsto (fun s => (1 + R s) ^ p.β)
 (nhdsWithin t (Set.Iio t)) (nhds ((1 + R t) ^ p.β)) :=
 (tendsto_const_nhds.add hRlim).rpow_const
 (Or.inl (ne_of_gt (by linarith : 0 < 1 + R t)))
 have hden_ne : (1 + R t) ^ p.β ≠ 0 :=
 ne_of_gt (Real.rpow_pos_of_pos (by linarith : 0 < 1 + R t) _)
 have hfluxlim := (hAlim.mul hGlim).div hdenlim hden_ne
 simpa [Q, truncatedChemFluxLifted, A, G, R, w, U,
 positivePartSlice] using hfluxlim
 let F : ℝ → ℝ → ℝ := fun s y => |Q s y - Q t y|
 let B : ℝ := 2 * CQ
 have hCQ : 0 ≤ CQ := by
 dsimp [CQ, Cg]
 exact mul_nonneg DT.hM.le
 (mul_nonneg (Real.sqrt_nonneg _)
 (mul_nonneg (by norm_num)
 (mul_nonneg p.hν.le (Real.rpow_nonneg DT.hM.le _))))
 have hQbound : ∀ s, 0 < s → s ≤ DT.T → ∀ y, |Q s y| ≤ CQ := by
 intro s hs hsT y
 rw [show Q s y = truncatedChemFluxLifted p (U s) y by rfl,
 truncatedChemFluxLifted_eq_chemFluxLifted_positivePartSlice]
 exact
 ShenWork.IntervalConjugateChemFluxIntegrable.chemFluxLifted_sup_bound_of_ball
 p DT.hM.le
 (fun x => (abs_positivePart_le_abs (U s x)).trans (by
 simpa [U] using
 (truncatedConjugateMildSolutionData_of_data DT).hbound s hs hsT x))
 (positivePartSlice_nonneg (U s))
 (positivePartSlice_continuous (by
 simpa [U] using
 (truncatedConjugateMildSolutionData_of_data DT).hcont s hs hsT)) y
 have hFmeas : ∀ᶠ s in nhdsWithin t (Set.Iio t),
 AEStronglyMeasurable (F s) (intervalMeasure 1) := by
 filter_upwards [] with s
 exact (((truncatedLimit_flux_integrable DT s).sub
 (truncatedLimit_flux_integrable DT t)).abs.aestronglyMeasurable)
 have hFbound : ∀ᶠ s in nhdsWithin t (Set.Iio t),
 ∀ᵐ y ∂intervalMeasure 1, ‖F s y‖ ≤ B := by
 filter_upwards [self_mem_nhdsWithin, hpos_event] with s hst hs0
 have hsT : s ≤ DT.T := (le_of_lt hst).trans htT
 refine Filter.Eventually.of_forall fun y => ?_
 rw [Real.norm_eq_abs, abs_abs]
 calc
 |Q s y - Q t y| ≤ |Q s y| + |Q t y| := abs_sub _ _
 _ ≤ CQ + CQ := add_le_add (hQbound s hs0 hsT y)
 (hQbound t ht htT y)
 _ = B := by ring
 have hFlim : ∀ᵐ y ∂intervalMeasure 1,
 Tendsto (fun s => F s y) (nhdsWithin t (Set.Iio t)) (nhds 0) := by
 filter_upwards [hQlim] with y hy
 simpa [F] using (hy.sub_const (Q t y)).abs
 have hDCT := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
 (fun _ : ℝ => B) hFmeas hFbound (integrable_const _) hFlim
 simpa [F, Q, U] using hDCT

/-- Left-endpoint convergence of the chemotaxis Duhamel pairing against an
arbitrary bounded absolutely-continuous fixed test. -/
theorem truncatedLimit_chem_pairing_tendsto
 {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
 (DT : TruncatedConjugateMildExistenceData p u₀)
 {t Cφ G : ℝ} (ht : 0 < t) (htT : t ≤ DT.T)
 {φ : ℝ → ℝ}
 (hφcont : ContinuousOn φ (Set.Icc (0 : ℝ) 1))
 (hCφ : 0 ≤ Cφ) (hφbound : ∀ y, |φ y| ≤ Cφ)
 (hφac : AbsolutelyContinuousOnInterval φ 0 1)
 (hG : 0 ≤ G) (hderiv_bound_vol : ∀ᵐ y ∂volume, |deriv φ y| ≤ G) :
 Tendsto
 (fun s => ∫ x,
 truncatedChemFluxLifted p
 ((truncatedConjugatePicardLimit p u₀ DT.T) s) x *
 deriv (fun z : ℝ =>
 intervalFullSemigroupOperator (t - s) φ z) x
 ∂intervalMeasure 1)
 (nhdsWithin t (Set.Iio t))
 (nhds (∫ x,
 truncatedChemFluxLifted p
 ((truncatedConjugatePicardLimit p u₀ DT.T) t) x * deriv φ x
 ∂intervalMeasure 1)) := by
 let U := truncatedConjugatePicardLimit p u₀ DT.T
 let Q : ℝ → ℝ → ℝ := fun s => truncatedChemFluxLifted p (U s)
 let D : ℝ → (ℝ → ℝ) → ℝ → ℝ :=
 ShenWork.Paper2.IntervalNegativePartWeakEnergy.intervalConjugateApproxOperator
 let Cg : ℝ := Real.sqrt (∑' k : ℕ,
 (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2)
 let CQ : ℝ := DT.M * (Cg * (2 * (p.ν * DT.M ^ p.γ)))
 have hCQ : 0 ≤ CQ := by
 dsimp [CQ, Cg]
 exact mul_nonneg DT.hM.le
 (mul_nonneg (Real.sqrt_nonneg _)
 (mul_nonneg (by norm_num)
 (mul_nonneg p.hν.le (Real.rpow_nonneg DT.hM.le _))))
 have hQbound : ∀ s, 0 < s → s ≤ DT.T → ∀ y, |Q s y| ≤ CQ := by
 intro s hs hsT y
 rw [show Q s y = truncatedChemFluxLifted p (U s) y by rfl,
 truncatedChemFluxLifted_eq_chemFluxLifted_positivePartSlice]
 exact
 ShenWork.IntervalConjugateChemFluxIntegrable.chemFluxLifted_sup_bound_of_ball
 p DT.hM.le
 (fun x => (abs_positivePart_le_abs (U s x)).trans (by
 simpa [U] using
 (truncatedConjugateMildSolutionData_of_data DT).hbound s hs hsT x))
 (positivePartSlice_nonneg (U s))
 (positivePartSlice_continuous (by
 simpa [U] using
 (truncatedConjugateMildSolutionData_of_data DT).hcont s hs hsT)) y
 have hQt_cont : ContinuousOn (Q t) (Set.Icc (0 : ℝ) 1) := by
 simpa [Q, U] using
 _root_.ShenWork.Paper2.TruncatedPositiveTimeBootstrap.truncatedChemFlux_continuousOn_positive_time
 DT ht htT
 have hQt_meas : AEStronglyMeasurable (Q t) (intervalMeasure 1) :=
 ShenWork.IntervalDuhamelIntegrability.continuousOn_aestronglyMeasurable_intervalMeasure
 hQt_cont
 have hQt_zero : Q t 0 = 0 := by
 simpa [Q, U] using
 _root_.ShenWork.Paper2.TruncatedPositiveTimeBootstrap.truncatedChemFluxLifted_zero_left'
 p (U t)
 have hQt_one : Q t 1 = 0 := by
 simpa [Q, U] using
 _root_.ShenWork.Paper2.TruncatedPositiveTimeBootstrap.truncatedChemFluxLifted_zero_right'
 p (U t)
 have hφmeas : AEStronglyMeasurable φ (intervalMeasure 1) :=
 ShenWork.IntervalDuhamelIntegrability.continuousOn_aestronglyMeasurable_intervalMeasure
 hφcont
 let d : ℝ → ℝ := fun y => if |deriv φ y| ≤ G then deriv φ y else 0
 have hd_meas_global : Measurable d := by
 apply Measurable.ite
 · exact measurableSet_le (Measurable.abs (measurable_deriv φ)) measurable_const
 · exact measurable_deriv φ
 · exact measurable_const
 have hd_meas : AEStronglyMeasurable d (intervalMeasure 1) :=
 hd_meas_global.aestronglyMeasurable
 have hd_bound : ∀ y, |d y| ≤ G := by
 intro y
 by_cases hy : |deriv φ y| ≤ G
 · simpa [d, hy] using hy
 · simp [d, hy, hG]
 have hd_eq_vol : d =ᵐ[volume] deriv φ := by
 filter_upwards [hderiv_bound_vol] with y hy
 simp [d, hy]
 have hd_eq_μ : d =ᵐ[intervalMeasure 1] deriv φ := by
 simp only [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
 exact hd_eq_vol.filter_mono ae_restrict_le
 have hderiv_eq : ∀ {r : ℝ}, 0 < r → ∀ x,
 deriv (fun z : ℝ => intervalFullSemigroupOperator r φ z) x =
 D r d x := by
 intro r hr x
 rw [ShenWork.Paper2.IntervalNegativePartWeakEnergy.deriv_intervalFullSemigroupOperator_eq_neg_conjugateKernel_of_ac
 hr hφmeas hφbound hφac x]
 unfold D ShenWork.Paper2.IntervalNegativePartWeakEnergy.intervalConjugateApproxOperator
 congr 1
 apply intervalIntegral.integral_congr_ae
 filter_upwards [hd_eq_vol] with y hy
 intro _hy
 rw [hy]
 have hD_int : ∀ {r : ℝ}, 0 < r →
 Integrable (D r d) (intervalMeasure 1) := by
 intro r hr
 exact
 ShenWork.Paper2.IntervalNegativePartWeakEnergy.intervalConjugateApproxOperator_integrable_of_bound
 hr hd_meas hd_bound
 have hr : Tendsto (fun s : ℝ => t - s)
 (nhdsWithin t (Set.Iio t)) (nhdsWithin 0 (Set.Ioi 0)) := by
 rw [tendsto_nhdsWithin_iff]
 constructor
 · have hc : ContinuousAt (fun s : ℝ => t - s) t :=
 continuousAt_const.sub continuousAt_id
 simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
 · filter_upwards [self_mem_nhdsWithin] with s hs
 exact sub_pos.mpr (show s < t from hs)
 let V : ℝ → ℝ := fun s => ∫ x,
 (Q s x - Q t x) *
 deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) φ z) x
 ∂intervalMeasure 1
 have hVbound : ∀ᶠ s in nhdsWithin t (Set.Iio t),
 |V s| ≤ G * (∫ x, |Q s x - Q t x| ∂intervalMeasure 1) := by
 filter_upwards [self_mem_nhdsWithin] with s hst
 have hrpos : 0 < t - s := sub_pos.mpr hst
 have hQdiff_int := (truncatedLimit_flux_integrable DT s).sub
 (truncatedLimit_flux_integrable DT t)
 have hdS_int : Integrable
 (fun x => deriv
 (fun z : ℝ => intervalFullSemigroupOperator (t - s) φ z) x)
 (intervalMeasure 1) :=
 (hD_int hrpos).congr (Filter.Eventually.of_forall fun x => by
 exact (hderiv_eq hrpos x).symm)
 have hdS_bound : ∀ x,
 |deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) φ z) x| ≤ G :=
 fun x =>
 ShenWork.Paper2.IntervalNegativePartWeakEnergy.abs_deriv_intervalFullSemigroupOperator_le_of_ac
 hrpos hφmeas hφbound hφac hG hderiv_bound_vol x
 have hdom_int : Integrable (fun x => G * |Q s x - Q t x|)
 (intervalMeasure 1) := hQdiff_int.abs.const_mul G
 have hnorm := MeasureTheory.norm_integral_le_of_norm_le hdom_int
 (Filter.Eventually.of_forall fun x => by
 rw [Real.norm_eq_abs, abs_mul]
 calc
 |Q s x - Q t x| *
 |deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) φ z) x|
 ≤ |Q s x - Q t x| * G :=
 mul_le_mul_of_nonneg_left (hdS_bound x) (abs_nonneg _)
 _ = G * |Q s x - Q t x| := by ring)
 rw [Real.norm_eq_abs] at hnorm
 simpa [V, MeasureTheory.integral_const_mul] using hnorm
 have hVrhs : Tendsto
 (fun s => G * (∫ x, |Q s x - Q t x| ∂intervalMeasure 1))
 (nhdsWithin t (Set.Iio t)) (nhds 0) := by
 simpa [Q, U] using (tendsto_const_nhds (x := G)).mul
 (truncatedLimit_flux_sub_integral_tendsto_zero DT ht htT)
 have hVabs : Tendsto (fun s => |V s|)
 (nhdsWithin t (Set.Iio t)) (nhds 0) :=
 squeeze_zero'
 (Filter.Eventually.of_forall fun s => abs_nonneg (V s)) hVbound hVrhs
 have hV : Tendsto V (nhdsWithin t (Set.Iio t)) (nhds 0) := by
 rw [tendsto_iff_norm_sub_tendsto_zero]
 simpa [Real.norm_eq_abs] using hVabs
 have happrox :
 ShenWork.IntervalSemigroupC1ApproxIdentity.InitialLegConjugateDerivativeApprox
 (Q t) :=
 ShenWork.IntervalSemigroupC1ApproxIdentity.initialLegConjugateDerivativeApprox_of_continuousOn_zero
 hQt_cont hQt_zero hQt_one
 have hDQt_point : ∀ y ∈ Set.Icc (0 : ℝ) 1,
 Tendsto (fun r => D r (Q t) y) (nhdsWithin 0 (Set.Ioi 0))
 (nhds (Q t y)) := by
 intro y hy
 rw [Metric.tendsto_nhds]
 intro ε hε
 obtain ⟨δ, hδ, happ⟩ := happrox ε hε
 have hlt : ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0), r < δ :=
 Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hδ)
 filter_upwards [self_mem_nhdsWithin, hlt] with r hrpos hrδ
 simpa [D, Real.dist_eq] using happ r hrpos hrδ y hy
 let F : ℝ → ℝ → ℝ := fun s y => d y * D (t - s) (Q t) y
 let f : ℝ → ℝ := fun y => d y * Q t y
 obtain ⟨δ₁, hδ₁, happ₁⟩ := happrox 1 (by norm_num : (0 : ℝ) < 1)
 have hrlt_event : ∀ᶠ s in nhdsWithin t (Set.Iio t), t - s < δ₁ := by
 have hset : Set.Iio δ₁ ∈ nhdsWithin 0 (Set.Ioi 0) :=
 Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hδ₁)
 exact hr hset
 have hFmeas : ∀ᶠ s in nhdsWithin t (Set.Iio t),
 AEStronglyMeasurable (F s) (intervalMeasure 1) := by
 filter_upwards [self_mem_nhdsWithin] with s hst
 have hDq_int :=
 ShenWork.Paper2.IntervalNegativePartWeakEnergy.intervalConjugateApproxOperator_integrable_of_bound
 (sub_pos.mpr hst) hQt_meas (hQbound t ht htT)
 exact ((hDq_int.bdd_mul hd_meas
 (Filter.Eventually.of_forall fun y => by
 rw [Real.norm_eq_abs]
 exact hd_bound y)).congr
 (Filter.Eventually.of_forall fun _ => by ring)).aestronglyMeasurable
 have hFbound : ∀ᶠ s in nhdsWithin t (Set.Iio t),
 ∀ᵐ y ∂intervalMeasure 1, ‖F s y‖ ≤ G * (CQ + 1) := by
 filter_upwards [self_mem_nhdsWithin, hrlt_event] with s hst hrδ
 have hrpos : 0 < t - s := sub_pos.mpr hst
 filter_upwards [ae_mem_Ioo_unitInterval] with y hy
 have hyI : y ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hy
 have ha := happ₁ (t - s) hrpos hrδ y hyI
 have ha' : |D (t - s) (Q t) y - Q t y| < 1 := by
 simpa [D] using ha
 have hDq : |D (t - s) (Q t) y| ≤ CQ + 1 := by
 calc
 |D (t - s) (Q t) y| =
 |(D (t - s) (Q t) y - Q t y) + Q t y| := by
 congr 1
 ring
 _ ≤ |D (t - s) (Q t) y - Q t y| + |Q t y| := abs_add_le _ _
 _ = |Q t y| + |D (t - s) (Q t) y - Q t y| := add_comm _ _
 _ ≤ CQ + 1 := add_le_add (hQbound t ht htT y) (le_of_lt ha')
 change |d y * D (t - s) (Q t) y| ≤ G * (CQ + 1)
 rw [abs_mul]
 exact mul_le_mul (hd_bound y) hDq (abs_nonneg _)
 (hG.trans (by linarith [hCQ]))
 have hFlim : ∀ᵐ y ∂intervalMeasure 1,
 Tendsto (fun s => F s y) (nhdsWithin t (Set.Iio t)) (nhds (f y)) := by
 filter_upwards [ae_mem_Ioo_unitInterval] with y hy
 have hyI : y ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hy
 simpa [F, f] using (tendsto_const_nhds (x := d y)).mul
 ((hDQt_point y hyI).comp hr)
 have hFint : Tendsto (fun s => ∫ y, F s y ∂intervalMeasure 1)
 (nhdsWithin t (Set.Iio t)) (nhds (∫ y, f y ∂intervalMeasure 1)) :=
 MeasureTheory.tendsto_integral_filter_of_dominated_convergence
 (fun _ : ℝ => G * (CQ + 1)) hFmeas hFbound (integrable_const _) hFlim
 have htarget : (∫ y, f y ∂intervalMeasure 1) =
 ∫ y, Q t y * deriv φ y ∂intervalMeasure 1 := by
 apply integral_congr_ae
 filter_upwards [hd_eq_μ] with y hy
 simp [f, hy]
 ring
 have hfixed : Tendsto
 (fun s => ∫ x, Q t x *
 deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) φ z) x
 ∂intervalMeasure 1)
 (nhdsWithin t (Set.Iio t))
 (nhds (∫ y, Q t y * deriv φ y ∂intervalMeasure 1)) := by
 have hcongr : ∀ᶠ s in nhdsWithin t (Set.Iio t),
 (∫ x, Q t x *
 deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) φ z) x
 ∂intervalMeasure 1) =
 ∫ y, F s y ∂intervalMeasure 1 := by
 filter_upwards [self_mem_nhdsWithin] with s hst
 have hrpos : 0 < t - s := sub_pos.mpr hst
 calc
 (∫ x, Q t x *
 deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) φ z) x
 ∂intervalMeasure 1) =
 ∫ x, D (t - s) d x * Q t x ∂intervalMeasure 1 := by
 apply integral_congr_ae
 exact Filter.Eventually.of_forall fun x => by
 change Q t x *
 deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) φ z) x =
 D (t - s) d x * Q t x
 rw [hderiv_eq hrpos x]
 ring
 _ = ∫ y, d y * D (t - s) (Q t) y ∂intervalMeasure 1 :=
 ShenWork.Paper2.IntervalNegativePartWeakEnergy.intervalConjugateApproxOperator_pairing_comm
 hrpos hd_meas hQt_meas hd_bound (hQbound t ht htT)
 _ = ∫ y, F s y ∂intervalMeasure 1 := rfl
 have hcongr' : ∀ᶠ s in nhdsWithin t (Set.Iio t),
 (∫ y, F s y ∂intervalMeasure 1) =
 ∫ x, Q t x *
 deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) φ z) x
 ∂intervalMeasure 1 := hcongr.mono fun _ hs => hs.symm
 simpa [htarget] using hFint.congr' hcongr'
 have hsum : Tendsto
 (fun s => V s +
 (∫ x, Q t x *
 deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) φ z) x
 ∂intervalMeasure 1))
 (nhdsWithin t (Set.Iio t))
 (nhds (∫ y, Q t y * deriv φ y ∂intervalMeasure 1)) := by
 simpa only [zero_add] using hV.add hfixed
 refine hsum.congr' ?_
 filter_upwards [self_mem_nhdsWithin] with s hst
 have hrpos : 0 < t - s := sub_pos.mpr hst
 have hdS_int : Integrable
 (fun x => deriv
 (fun z : ℝ => intervalFullSemigroupOperator (t - s) φ z) x)
 (intervalMeasure 1) :=
 (hD_int hrpos).congr (Filter.Eventually.of_forall fun x => by
 exact (hderiv_eq hrpos x).symm)
 have hdS_bound : ∀ x,
 |deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) φ z) x| ≤ G :=
 fun x =>
 ShenWork.Paper2.IntervalNegativePartWeakEnergy.abs_deriv_intervalFullSemigroupOperator_le_of_ac
 hrpos hφmeas hφbound hφac hG hderiv_bound_vol x
 have hQs_int := truncatedLimit_flux_integrable DT s
 have hQt_int := truncatedLimit_flux_integrable DT t
 have hleft_int : Integrable (fun x =>
 (Q s x - Q t x) *
 deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) φ z) x)
 (intervalMeasure 1) :=
 ((hQs_int.sub hQt_int).bdd_mul hdS_int.aestronglyMeasurable
 (Filter.Eventually.of_forall fun x => by
 rw [Real.norm_eq_abs]
 exact hdS_bound x)).congr
 (Filter.Eventually.of_forall fun x => by
 change _ * (Q s x - Q t x) =
 (Q s x - Q t x) *
 deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) φ z) x
 ring)
 have hright_int : Integrable (fun x => Q t x *
 deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) φ z) x)
 (intervalMeasure 1) :=
 (hQt_int.bdd_mul hdS_int.aestronglyMeasurable
 (Filter.Eventually.of_forall fun x => by
 rw [Real.norm_eq_abs]
 exact hdS_bound x)).congr
 (Filter.Eventually.of_forall fun _ => by ring)
 rw [← MeasureTheory.integral_add hleft_int hright_int]
 apply integral_congr_ae
 exact Filter.Eventually.of_forall fun x => by
 change (Q s x - Q t x) *
 deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) φ z) x +
 Q t x * deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) φ z) x =
 Q s x * deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) φ z) x
 ring

/-- Left-endpoint convergence of the ordinary Duhamel pairing against an
arbitrary fixed continuous bounded test. -/
theorem truncatedLimit_logistic_pairing_tendsto
 {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
 (DT : TruncatedConjugateMildExistenceData p u₀)
 {t Cφ : ℝ} (ht : 0 < t) (htT : t ≤ DT.T)
 {φ : ℝ → ℝ}
 (hφcont : ContinuousOn φ (Set.Icc (0 : ℝ) 1))
 (hφzero : ∀ y, y ∉ Set.Icc (0 : ℝ) 1 → φ y = 0)
 (hCφ : 0 ≤ Cφ) (hφbound : ∀ y, |φ y| ≤ Cφ) :
 Tendsto
 (fun s => ∫ x,
 intervalFullSemigroupOperator (t - s)
 (truncatedLogisticLifted p
 ((truncatedConjugatePicardLimit p u₀ DT.T) s)) x * φ x
 ∂ intervalMeasure 1)
 (nhdsWithin t (Set.Iio t))
 (nhds (∫ x,
 truncatedLogisticLifted p
 ((truncatedConjugatePicardLimit p u₀ DT.T) t) x * φ x
 ∂ intervalMeasure 1)) := by
 let U := truncatedConjugatePicardLimit p u₀ DT.T
 let L : ℝ → ℝ → ℝ := fun s => truncatedLogisticLifted p (U s)
 let φD : intervalDomainPoint → ℝ := Set.restrict (Set.Icc (0 : ℝ) 1) φ
 let ψ : ℝ → ℝ := ShenWork.IntervalDomain.intervalDomainConstExtend φD
 have hφDcont : Continuous φD := by
 simpa [φD] using (continuousOn_iff_continuous_restrict.mp hφcont)
 have hψcont : Continuous ψ :=
 ShenWork.IntervalDomain.constExtend_continuous hφDcont
 have hφlift : φ = intervalDomainLift φD := by
 funext y
 by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
 · simp [φD, intervalDomainLift, hy]
 · simp [φD, intervalDomainLift, hy, hφzero y hy]
 have hψeq : ∀ y ∈ Set.Icc (0 : ℝ) 1, ψ y = φ y := by
 intro y hy
 change ShenWork.IntervalDomain.intervalDomainConstExtend φD y = φ y
 rw [ShenWork.IntervalDomain.constExtend_eq_lift_on_Icc hy, ← hφlift]
 have hψbound : ∀ y, |ψ y| ≤ Cφ := by
 intro y
 by_cases hy0 : y ≤ 0
 · simp only [ψ, ShenWork.IntervalDomain.intervalDomainConstExtend,
 dif_pos hy0]
 simpa [φD] using hφbound 0
 · by_cases hy1 : 1 ≤ y
 · simp only [ψ, ShenWork.IntervalDomain.intervalDomainConstExtend,
 dif_neg hy0, dif_pos hy1]
 simpa [φD] using hφbound 1
 · have hy : y ∈ Set.Icc (0 : ℝ) 1 :=
 ⟨(not_le.mp hy0).le, (not_le.mp hy1).le⟩
 rw [hψeq y hy]
 exact hφbound y
 have hψmeas : AEStronglyMeasurable ψ (intervalMeasure 1) :=
 hψcont.aestronglyMeasurable
 have hφmeas : AEStronglyMeasurable φ (intervalMeasure 1) :=
 ShenWork.IntervalDuhamelIntegrability.continuousOn_aestronglyMeasurable_intervalMeasure
 hφcont
 have hr : Tendsto (fun s : ℝ => t - s)
 (nhdsWithin t (Set.Iio t)) (nhdsWithin 0 (Set.Ioi 0)) := by
 rw [tendsto_nhdsWithin_iff]
 constructor
 · have hc : ContinuousAt (fun s : ℝ => t - s) t :=
 continuousAt_const.sub continuousAt_id
 simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
 · filter_upwards [self_mem_nhdsWithin] with s hs
 exact sub_pos.mpr (show s < t from hs)
 have hSpoint : ∀ y ∈ Set.Icc (0 : ℝ) 1,
 Tendsto (fun s => intervalFullSemigroupOperator (t - s) ψ y)
 (nhdsWithin t (Set.Iio t)) (nhds (ψ y)) := by
 intro y hy
 exact
 (ShenWork.IntervalSemigroupUniform.intervalFullSemigroup_tendstoUniformlyOn
 ψ hψcont).tendsto_at hy |>.comp hr
 let F : ℝ → ℝ → ℝ := fun s y =>
 L s y * intervalFullSemigroupOperator (t - s) ψ y
 let f : ℝ → ℝ := fun y => L t y * φ y
 let C : ℝ := truncatedLogisticBound p DT.M * Cφ
 have hCL : 0 ≤ truncatedLogisticBound p DT.M :=
 truncatedLogisticBound_nonneg p DT.hM.le
 have hC : 0 ≤ C := mul_nonneg hCL hCφ
 have hpos_event : ∀ᶠ s in nhdsWithin t (Set.Iio t), 0 < s := by
 have hnh : Set.Ioi (t / 2) ∈ nhds t := Ioi_mem_nhds (by linarith)
 filter_upwards
 [Filter.Eventually.filter_mono nhdsWithin_le_nhds hnh] with s hs
 exact lt_trans (by linarith : 0 < t / 2) hs
 have hFmeas : ∀ᶠ s in nhdsWithin t (Set.Iio t),
 AEStronglyMeasurable (F s) (intervalMeasure 1) := by
 filter_upwards [self_mem_nhdsWithin, hpos_event] with s hst hs0
 have hScont :=
 ShenWork.IntervalDuhamelIntegrability.intervalFullSemigroupOperator_continuous_of_bounded
 (sub_pos.mpr hst) hCφ hψbound hψmeas
 exact (truncatedLimit_logistic_aestronglyMeasurable DT s).mul
 hScont.aestronglyMeasurable
 have hFbound : ∀ᶠ s in nhdsWithin t (Set.Iio t),
 ∀ᵐ y ∂intervalMeasure 1, ‖F s y‖ ≤ C := by
 filter_upwards [self_mem_nhdsWithin, hpos_event] with s hst hs0
 have hsT : s ≤ DT.T := (le_of_lt hst).trans htT
 refine Filter.Eventually.of_forall fun y => ?_
 have hLb := truncatedLogisticLifted_abs_le p DT.hM.le
 (fun x => by simpa [U] using
 (truncatedConjugateMildSolutionData_of_data DT).hbound s hs0 hsT x) y
 have hSb :=
 ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
 (sub_pos.mpr hst) hCφ hψbound y
 change |L s y * intervalFullSemigroupOperator (t - s) ψ y| ≤ C
 rw [abs_mul]
 exact mul_le_mul hLb hSb (abs_nonneg _) hCL
 have hFlim : ∀ᵐ y ∂intervalMeasure 1,
 Tendsto (fun s => F s y) (nhdsWithin t (Set.Iio t)) (nhds (f y)) := by
 filter_upwards [ae_mem_Ioo_unitInterval] with y hy
 let X : intervalDomainPoint := ⟨y, Set.Ioo_subset_Icc_self hy⟩
 have hUlim : Tendsto (fun s => U s X) (nhdsWithin t (Set.Iio t))
 (nhds (U t X)) := by
 simpa [U] using
 (truncatedLimit_timeSlice_continuousWithinAt_Iio DT ht htT X)
 have hlocal : Continuous (truncatedLogisticLocal p) := by
 unfold truncatedLogisticLocal
 have hp : Continuous (fun r : ℝ => positivePart r) := by
 simpa [positivePart] using continuous_id.max continuous_const
 exact continuous_id.mul
 (continuous_const.sub (continuous_const.mul
 (hp.rpow_const (fun _ => Or.inr p.hα.le))))
 have hLlim : Tendsto (fun s => L s y) (nhdsWithin t (Set.Iio t))
 (nhds (L t y)) := by
 simpa [L, U, truncatedLogisticLifted, intervalDomainLift,
 Set.Ioo_subset_Icc_self hy] using hlocal.continuousAt.tendsto.comp hUlim
 have hmul := hLlim.mul (hSpoint y (Set.Ioo_subset_Icc_self hy))
 simpa [F, f, hψeq y (Set.Ioo_subset_Icc_self hy)] using hmul
 have hDCT : Tendsto (fun s => ∫ y, F s y ∂intervalMeasure 1)
 (nhdsWithin t (Set.Iio t)) (nhds (∫ y, f y ∂intervalMeasure 1)) :=
 MeasureTheory.tendsto_integral_filter_of_dominated_convergence
 (fun _ : ℝ => C) hFmeas hFbound (integrable_const _) hFlim
 refine hDCT.congr' ?_
 filter_upwards [self_mem_nhdsWithin, hpos_event] with s hst hs0
 have hsT : s ≤ DT.T := (le_of_lt hst).trans htT
 have hLbound : ∀ y, |L s y| ≤ truncatedLogisticBound p DT.M :=
 truncatedLogisticLifted_abs_le p DT.hM.le (fun x => by
 simpa [U] using
 (truncatedConjugateMildSolutionData_of_data DT).hbound s hs0 hsT x)
 have hpair :=
 ShenWork.Paper2.IntervalNegativePartWeakEnergy.intervalFullSemigroupOperator_pairing_comm
 (sub_pos.mpr hst) (truncatedLimit_logistic_aestronglyMeasurable DT s)
 hφmeas hLbound hφbound
 symm
 calc
 (∫ x, intervalFullSemigroupOperator (t - s) (L s) x * φ x
 ∂intervalMeasure 1) =
 ∫ y, L s y * intervalFullSemigroupOperator (t - s) φ y
 ∂intervalMeasure 1 := hpair
 _ = ∫ y, F s y ∂intervalMeasure 1 := by
 apply integral_congr_ae
 exact Filter.Eventually.of_forall fun y => by
 have hsem : intervalFullSemigroupOperator (t - s) φ y =
 intervalFullSemigroupOperator (t - s) ψ y := by
 rw [hφlift]
 exact ShenWork.IntervalDomain.semigroupOperator_constExtend_eq_lift.symm
 simp [F, hsem]

/-- Fubini for an ordinary-source tail against an arbitrary bounded measurable
test. -/
theorem truncatedLimit_logistic_tail_pairing
 {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
 (DT : TruncatedConjugateMildExistenceData p u₀)
 {a t Cφ : ℝ} (ha : 0 < a) (hat : a < t) (htT : t ≤ DT.T)
 {φ : ℝ → ℝ}
 (hφmeas : AEStronglyMeasurable φ (intervalMeasure 1))
 (hCφ : 0 ≤ Cφ) (hφbound : ∀ x, |φ x| ≤ Cφ) :
 let U := truncatedConjugatePicardLimit p u₀ DT.T
 Integrable (fun x =>
 (∫ s in a..t,
 intervalFullSemigroupOperator (t - s)
 (truncatedLogisticLifted p (U s)) x) * φ x)
 (intervalMeasure 1) ∧
 IntervalIntegrable (fun s => ∫ x,
 intervalFullSemigroupOperator (t - s)
 (truncatedLogisticLifted p (U s)) x * φ x
 ∂intervalMeasure 1) volume a t ∧
 (∫ x,
 (∫ s in a..t,
 intervalFullSemigroupOperator (t - s)
 (truncatedLogisticLifted p (U s)) x) * φ x
 ∂intervalMeasure 1) =
 ∫ s in a..t, ∫ x,
 intervalFullSemigroupOperator (t - s)
 (truncatedLogisticLifted p (U s)) x * φ x
 ∂intervalMeasure 1 := by
 let U := truncatedConjugatePicardLimit p u₀ DT.T
 let SD := truncatedConjugateMildSolutionData_of_data DT
 let L : ℝ → ℝ → ℝ := fun s => truncatedLogisticLifted p (U s)
 let LF : ℝ → ℝ → ℝ := fun s x =>
 intervalFullSemigroupOperator (t - s) (L s) x * φ x
 let CL : ℝ := truncatedLogisticBound p DT.M
 have hLjoint : Measurable (Function.uncurry L) := by
 simpa [L, U, SD] using
 _root_.ShenWork.Paper2.TruncatedPositiveTimeBootstrap.truncatedLogisticLifted_joint_measurable_of_lift_joint
 (p := p) (w := SD.u) SD.hmeas
 have hSjoint : Measurable (fun r : (ℝ × ℝ) × ℝ =>
 intervalFullSemigroupOperator (r.1.1 - r.2) (L r.2) r.1.2) :=
 ShenWork.IntervalMildPicardThreshold.intervalFullSemigroupOperator_s_param_joint_measurable'
 hLjoint
 have hmap : Measurable (fun z : ℝ × ℝ =>
 (((t, z.2), z.1) : (ℝ × ℝ) × ℝ)) :=
 (measurable_const.prodMk measurable_snd).prodMk measurable_fst
 have hSmeas : Measurable (fun z : ℝ × ℝ =>
 intervalFullSemigroupOperator (t - z.1) (L z.1) z.2) :=
 hSjoint.comp hmap
 have hLFmeas : AEStronglyMeasurable (Function.uncurry LF)
 ((volume.restrict (Set.Ioc a t)).prod (intervalMeasure 1)) := by
 simpa [LF] using hSmeas.aestronglyMeasurable.mul
 (hφmeas.comp_snd (μ := volume.restrict (Set.Ioc a t)))
 have hCL : 0 ≤ CL := by
 dsimp [CL]
 exact truncatedLogisticBound_nonneg p DT.hM.le
 have hprod_mem : ∀ᵐ z ∂((volume.restrict (Set.Ioc a t)).prod (intervalMeasure 1)),
 z.1 ∈ Set.Ioo a t := by
 rw [MeasureTheory.Measure.ae_prod_iff_ae_ae
 (measurableSet_Ioo.preimage measurable_fst)]
 filter_upwards [ae_restrict_mem measurableSet_Ioc,
 (Measure.ae_ne volume t).filter_mono ae_restrict_le] with s hs hsne
 exact Filter.Eventually.of_forall fun _ =>
 ⟨hs.1, lt_of_le_of_ne hs.2 hsne⟩
 have hLFbound : ∀ᵐ z ∂((volume.restrict (Set.Ioc a t)).prod (intervalMeasure 1)),
 ‖Function.uncurry LF z‖ ≤ CL * Cφ := by
 filter_upwards [hprod_mem] with z hz
 have hs0 : 0 < z.1 := ha.trans hz.1
 have hsT : z.1 ≤ DT.T := (le_of_lt hz.2).trans htT
 have hSb :=
 ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
 (sub_pos.mpr hz.2) hCL
 (truncatedLogisticLifted_abs_le p DT.hM.le
 (fun x => by simpa [U, SD] using SD.hbound z.1 hs0 hsT x)) z.2
 change |intervalFullSemigroupOperator (t - z.1) (L z.1) z.2 * φ z.2| ≤
 CL * Cφ
 rw [abs_mul]
 exact mul_le_mul hSb (hφbound z.2) (abs_nonneg _) hCL
 have hLFprod : Integrable (Function.uncurry LF)
 ((volume.restrict (Set.Ioc a t)).prod (intervalMeasure 1)) :=
 Integrable.of_bound hLFmeas (CL * Cφ) hLFbound
 have hLFprod_uIoc : Integrable (Function.uncurry LF)
 ((volume.restrict (Set.uIoc a t)).prod (intervalMeasure 1)) := by
 simpa [Set.uIoc_of_le hat.le] using hLFprod
 have hswap := MeasureTheory.intervalIntegral_integral_swap hLFprod_uIoc
 have hspatial_raw : Integrable
 (fun x => ∫ s in a..t, LF s x) (intervalMeasure 1) := by
 simpa [intervalIntegral.integral_of_le hat.le, Set.uIoc_of_le hat.le] using
 hLFprod_uIoc.integral_prod_right
 have htime_int : IntervalIntegrable
 (fun s => ∫ x, LF s x ∂intervalMeasure 1) volume a t := by
 rw [intervalIntegrable_iff]
 exact hLFprod_uIoc.integral_prod_left
 have hpoint : (fun x =>
 (∫ s in a..t, intervalFullSemigroupOperator (t - s) (L s) x) * φ x) =
 fun x => ∫ s in a..t, LF s x := by
 funext x
 rw [intervalIntegral.integral_mul_const]
 constructor
 · rw [hpoint]
 exact hspatial_raw
 constructor
 · simpa [LF] using htime_int
 · rw [hpoint]
 simpa [LF] using hswap.symm

set_option maxHeartbeats 0 in
/-- Fubini and the regular B-form adjoint identity for a chemotaxis tail
against an arbitrary bounded measurable test. -/
theorem truncatedLimit_chem_tail_pairing
 {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
 (DT : TruncatedConjugateMildExistenceData p u₀)
 {a t Cφ : ℝ} (ha : 0 < a) (hat : a < t) (htT : t ≤ DT.T)
 {φ : ℝ → ℝ}
 (hφmeas : AEStronglyMeasurable φ (intervalMeasure 1))
 (hCφ : 0 ≤ Cφ) (hφbound : ∀ x, |φ x| ≤ Cφ) :
 let U := truncatedConjugatePicardLimit p u₀ DT.T
 Integrable (fun x =>
 (∫ s in a..t,
 intervalConjugateKernelOperator (t - s)
 (truncatedChemFluxLifted p (U s)) x) * φ x)
 (intervalMeasure 1) ∧
 IntervalIntegrable (fun s => ∫ x,
 truncatedChemFluxLifted p (U s) x *
 deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) φ z) x
 ∂intervalMeasure 1) volume a t ∧
 (∫ x,
 (∫ s in a..t,
 intervalConjugateKernelOperator (t - s)
 (truncatedChemFluxLifted p (U s)) x) * φ x
 ∂intervalMeasure 1) =
 -(∫ s in a..t, ∫ x,
 truncatedChemFluxLifted p (U s) x *
 deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) φ z) x
 ∂intervalMeasure 1) := by
 let U := truncatedConjugatePicardLimit p u₀ DT.T
 let SD := truncatedConjugateMildSolutionData_of_data DT
 let Q : ℝ → ℝ → ℝ := fun s => truncatedChemFluxLifted p (U s)
 let BF : ℝ → ℝ → ℝ := fun s x =>
 intervalConjugateKernelOperator (t - s) (Q s) x * φ x
 let CP : ℝ → ℝ := fun s => ∫ x, Q s x *
 deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) φ z) x
 ∂intervalMeasure 1
 let Cg : ℝ :=
 ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
 let CQ : ℝ := DT.M *
 (Real.sqrt (∑' k : ℕ,
 (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
 (2 * (p.ν * DT.M ^ p.γ)))
 let K : ℝ := Cg * CQ * Cφ
 have hφint : Integrable φ (intervalMeasure 1) :=
 ShenWork.IntervalDomain.intervalMeasure_integrable_of_abs_bound
 hφmeas hφbound
 have hQjoint : Measurable (Function.uncurry Q) := by
 simpa [Q, U, SD] using
 _root_.ShenWork.Paper2.TruncatedPositiveTimeBootstrap.truncatedChemFluxLifted_joint_measurable_of_lift_joint
 (p := p) (w := SD.u) SD.hmeas
 have hBjoint : Measurable (fun r : (ℝ × ℝ) × ℝ =>
 intervalConjugateKernelOperator (r.1.1 - r.2) (Q r.2) r.1.2) :=
 ShenWork.IntervalConjugateKernelJointMeas.intervalConjugateKernelOperator_s_param_joint_measurable
 hQjoint
 have hmap : Measurable (fun z : ℝ × ℝ =>
 (((t, z.2), z.1) : (ℝ × ℝ) × ℝ)) :=
 (measurable_const.prodMk measurable_snd).prodMk measurable_fst
 have hBmeas : Measurable (fun z : ℝ × ℝ =>
 intervalConjugateKernelOperator (t - z.1) (Q z.1) z.2) :=
 hBjoint.comp hmap
 have hBFmeas : AEStronglyMeasurable (Function.uncurry BF)
 ((volume.restrict (Set.Ioc a t)).prod (intervalMeasure 1)) := by
 simpa [BF] using hBmeas.aestronglyMeasurable.mul
 (hφmeas.comp_snd (μ := volume.restrict (Set.Ioc a t)))
 have hCg : 0 ≤ Cg :=
 ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
 have hCQ : 0 ≤ CQ := by
 dsimp [CQ]
 exact mul_nonneg DT.hM.le
 (mul_nonneg (Real.sqrt_nonneg _)
 (mul_nonneg (by norm_num)
 (mul_nonneg p.hν.le (Real.rpow_nonneg DT.hM.le _))))
 have hK : 0 ≤ K := by
 dsimp [K]
 exact mul_nonneg (mul_nonneg hCg hCQ) hCφ
 have hprod_mem : ∀ᵐ z ∂((volume.restrict (Set.Ioc a t)).prod (intervalMeasure 1)),
 z.1 ∈ Set.Ioo a t := by
 rw [MeasureTheory.Measure.ae_prod_iff_ae_ae
 (measurableSet_Ioo.preimage measurable_fst)]
 filter_upwards [ae_restrict_mem measurableSet_Ioc,
 (Measure.ae_ne volume t).filter_mono ae_restrict_le] with s hs hsne
 exact Filter.Eventually.of_forall fun _ =>
 ⟨hs.1, lt_of_le_of_ne hs.2 hsne⟩
 have hdom_time : Integrable
 (fun s : ℝ => K * (t - s) ^ (-(1 / 2) : ℝ))
 (volume.restrict (Set.Ioc a t)) := by
 exact (integrableOn_Icc_sub_rpow_neg_half_const t K (ha.trans hat).le).mono_set
 (fun s hs => ⟨ha.le.trans hs.1.le, hs.2⟩)
 have hdom_prod : Integrable
 (fun z : ℝ × ℝ => K * (t - z.1) ^ (-(1 / 2) : ℝ))
 ((volume.restrict (Set.Ioc a t)).prod (intervalMeasure 1)) :=
 hdom_time.comp_fst (intervalMeasure 1)
 have hBFbound : ∀ᵐ z ∂((volume.restrict (Set.Ioc a t)).prod (intervalMeasure 1)),
 ‖Function.uncurry BF z‖ ≤ K * (t - z.1) ^ (-(1 / 2) : ℝ) := by
 filter_upwards [hprod_mem] with z hz
 have hs0 : 0 < z.1 := ha.trans hz.1
 have hsT : z.1 ≤ DT.T := (le_of_lt hz.2).trans htT
 have hQint : Integrable (Q z.1) (intervalMeasure 1) := by
 simpa [Q, U] using truncatedLimit_flux_integrable DT z.1
 have hQbound : ∀ y, |Q z.1 y| ≤ CQ := by
 intro y
 rw [show Q z.1 y = truncatedChemFluxLifted p (U z.1) y by rfl,
 truncatedChemFluxLifted_eq_chemFluxLifted_positivePartSlice]
 exact
 ShenWork.IntervalConjugateChemFluxIntegrable.chemFluxLifted_sup_bound_of_ball
 p DT.hM.le
 (fun X => (abs_positivePart_le_abs (U z.1 X)).trans (by
 simpa [U, SD] using SD.hbound z.1 hs0 hsT X))
 (positivePartSlice_nonneg (U z.1))
 (positivePartSlice_continuous (by
 simpa [U, SD] using SD.hcont z.1 hs0 hsT)) y
 have hBb :=
 ShenWork.IntervalConjugateDuhamelMap.intervalConjugateKernelOperator_abs_le
 (sub_pos.mpr hz.2) hQint hQbound z.2
 change |intervalConjugateKernelOperator (t - z.1) (Q z.1) z.2 * φ z.2| ≤
 K * (t - z.1) ^ (-(1 / 2) : ℝ)
 rw [abs_mul]
 calc
 |intervalConjugateKernelOperator (t - z.1) (Q z.1) z.2| * |φ z.2|
 ≤ (Cg * (t - z.1) ^ (-(1 / 2) : ℝ) * CQ) * Cφ :=
 mul_le_mul hBb (hφbound z.2) (abs_nonneg _)
 (mul_nonneg (mul_nonneg hCg
 (Real.rpow_nonneg (sub_pos.mpr hz.2).le _)) hCQ)
 _ = K * (t - z.1) ^ (-(1 / 2) : ℝ) := by
 dsimp [K]
 ring
 have hBFprod : Integrable (Function.uncurry BF)
 ((volume.restrict (Set.Ioc a t)).prod (intervalMeasure 1)) :=
 Integrable.mono' hdom_prod hBFmeas hBFbound
 have hBFprod_uIoc : Integrable (Function.uncurry BF)
 ((volume.restrict (Set.uIoc a t)).prod (intervalMeasure 1)) := by
 simpa [Set.uIoc_of_le hat.le] using hBFprod
 have hswap := MeasureTheory.intervalIntegral_integral_swap hBFprod_uIoc
 have hspatial_raw : Integrable
 (fun x => ∫ s in a..t, BF s x) (intervalMeasure 1) := by
 simpa [intervalIntegral.integral_of_le hat.le, Set.uIoc_of_le hat.le] using
 hBFprod_uIoc.integral_prod_right
 have hBtime_int : IntervalIntegrable
 (fun s => ∫ x, BF s x ∂intervalMeasure 1) volume a t := by
 rw [intervalIntegrable_iff]
 exact hBFprod_uIoc.integral_prod_left
 have hCP_int : IntervalIntegrable CP volume a t := by
 rw [intervalIntegrable_iff]
 rw [intervalIntegrable_iff] at hBtime_int
 have heq : ∀ᵐ s ∂volume.restrict (Set.uIoc a t),
 CP s = -(∫ x, BF s x ∂intervalMeasure 1) := by
 filter_upwards [ae_restrict_mem measurableSet_uIoc,
 (Measure.ae_ne volume t).filter_mono ae_restrict_le] with s hs hsne
 rw [Set.uIoc_of_le hat.le] at hs
 have hst : s < t := lt_of_le_of_ne hs.2 hsne
 have hd := bN_duality_L1 (sub_pos.mpr hst) (Q s) φ
 (by simpa [Q, U] using truncatedLimit_flux_integrable DT s) hφint
 have hd' : (∫ x, BF s x ∂intervalMeasure 1) = -CP s := by
 simpa [BF, CP] using hd
 linarith [hd']
 apply hBtime_int.neg.congr
 filter_upwards [heq] with s hs
 exact hs.symm
 have htime_eq :
 (∫ s in a..t, ∫ x, BF s x ∂intervalMeasure 1) =
 -(∫ s in a..t, CP s) := by
 rw [← intervalIntegral.integral_neg]
 apply intervalIntegral.integral_congr_ae
 filter_upwards [(Measure.ae_ne volume t)] with s hsne hsI
 rw [Set.uIoc_of_le hat.le] at hsI
 have hst : s < t := lt_of_le_of_ne hsI.2 hsne
 simpa [BF, CP] using
 (bN_duality_L1 (sub_pos.mpr hst) (Q s) φ
 (by simpa [Q, U] using truncatedLimit_flux_integrable DT s) hφint)
 have hpoint : (fun x =>
 (∫ s in a..t, intervalConjugateKernelOperator (t - s) (Q s) x) * φ x) =
 fun x => ∫ s in a..t, BF s x := by
 funext x
 rw [intervalIntegral.integral_mul_const]
 constructor
 · rw [hpoint]
 exact hspatial_raw
 constructor
 · simpa [CP, Q] using hCP_int
 · rw [hpoint]
 exact hswap.symm.trans (by simpa [BF, CP] using htime_eq)

/-- Restart the faithful truncated mild equation at a positive earlier time. -/
theorem truncatedLimit_backward_restart
 {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
 (DT : TruncatedConjugateMildExistenceData p u₀)
 {a t : ℝ} (ha : 0 < a) (hat : a < t) (htT : t ≤ DT.T)
 (x : intervalDomainPoint) :
 let U := truncatedConjugatePicardLimit p u₀ DT.T
 U t x =
 intervalFullSemigroupOperator (t - a) (intervalDomainLift (U a)) x.1 +
 (-p.χ₀) * (∫ s in a..t,
 intervalConjugateKernelOperator (t - s)
 (truncatedChemFluxLifted p (U s)) x.1) +
 ∫ s in a..t,
 intervalFullSemigroupOperator (t - s)
 (truncatedLogisticLifted p (U s)) x.1 := by
 let U := truncatedConjugatePicardLimit p u₀ DT.T
 let SD := truncatedConjugateMildSolutionData_of_data DT
 let Q : ℝ → ℝ → ℝ := fun s => truncatedChemFluxLifted p (U s)
 let L : ℝ → ℝ → ℝ := fun s => truncatedLogisticLifted p (U s)
 let CQ : ℝ := DT.M *
 (Real.sqrt (∑' k : ℕ,
 (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
 (2 * (p.ν * DT.M ^ p.γ)))
 let CL : ℝ := DT.M * (p.a + p.b * DT.M ^ p.α)
 have hCQ : 0 ≤ CQ := by
 dsimp [CQ]
 exact mul_nonneg DT.hM.le
 (mul_nonneg (Real.sqrt_nonneg _)
 (mul_nonneg (by norm_num)
 (mul_nonneg p.hν.le (Real.rpow_nonneg DT.hM.le _))))
 have hCL : 0 ≤ CL := by
 dsimp [CL]
 exact mul_nonneg DT.hM.le
 (add_nonneg p.ha
 (mul_nonneg p.hb (Real.rpow_nonneg DT.hM.le _)))
 have hcont_all : ∀ s, Continuous (U s) := by
 intro s
 by_cases hs : 0 < s ∧ s ≤ DT.T
 · simpa [U, SD] using SD.hcont s hs.1 hs.2
 · have hzero : U s = fun _ : intervalDomainPoint => 0 := by
 funext y
 simp [U, truncatedConjugatePicardLimit, hs]
 rw [hzero]
 exact continuous_const
 have hball_all : ∀ s, ∀ y : intervalDomainPoint, |U s y| ≤ DT.M := by
 intro s y
 by_cases hs : 0 < s ∧ s ≤ DT.T
 · simpa [U, SD] using SD.hbound s hs.1 hs.2 y
 · simp [U, truncatedConjugatePicardLimit, hs, DT.hM.le]
 have hQ_meas : Measurable (Function.uncurry Q) := by
 simpa [Q, U, SD] using
 _root_.ShenWork.Paper2.TruncatedPositiveTimeBootstrap.truncatedChemFluxLifted_joint_measurable_of_lift_joint
 (p := p) (w := SD.u) SD.hmeas
 have hL_meas : Measurable (Function.uncurry L) := by
 simpa [L, U, SD] using
 _root_.ShenWork.Paper2.TruncatedPositiveTimeBootstrap.truncatedLogisticLifted_joint_measurable_of_lift_joint
 (p := p) (w := SD.u) SD.hmeas
 have hQ_bound : ∀ s y, |Q s y| ≤ CQ := by
 intro s y
 simpa [Q, CQ] using
 _root_.ShenWork.Paper2.TruncatedPositiveTimeBootstrap.truncatedChemFluxLifted_abs_le_of_abs_ball
 p DT.hM (hcont_all s) (hball_all s) y
 have hL_bound : ∀ s y, |L s y| ≤ CL := by
 intro s y
 simpa [L, CL] using truncatedLogisticLifted_abs_le p DT.hM.le
 (hball_all s) y
 have hQ_int : ∀ s, Integrable (Q s) (intervalMeasure 1) := by
 intro s
 simpa [Q, U] using truncatedLimit_flux_integrable DT s
 have hL_int : ∀ s, Integrable (L s) (intervalMeasure 1) := by
 intro s
 exact Integrable.of_bound
 (hL_meas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
 CL (Filter.Eventually.of_forall (hL_bound s))
 have hu₀_int : Integrable (intervalDomainLift u₀) (intervalMeasure 1) :=
 ShenWork.IntervalDomain.intervalMeasure_integrable_of_abs_bound
 DT.hbase_lift_meas DT.hbase_lift_bound
 have hrestart := ShenWork.Paper2.IntervalFullDuhamelRestart.intervalBFormDuhamel_restart
 ha hat DT.hbase_lift_meas hu₀_int DT.hM.le DT.hbase_lift_bound
 hQ_meas hQ_int hCQ hQ_bound hL_meas hL_int hCL hL_bound
 (-p.χ₀) x.2
 have haT : a ≤ DT.T := (le_of_lt hat).trans htT
 have hinner : ∀ y ∈ Set.Icc (0 : ℝ) 1,
 (intervalFullSemigroupOperator a (intervalDomainLift u₀) y +
 (-p.χ₀) * (∫ s in (0 : ℝ)..a,
 intervalConjugateKernelOperator (a - s) (Q s) y) +
 ∫ s in (0 : ℝ)..a,
 intervalFullSemigroupOperator (a - s) (L s) y) =
 intervalDomainLift (U a) y := by
 intro y hy
 have hm := SD.hmild a ha haT ⟨y, hy⟩
 simpa [SD, U, Q, L, truncatedConjugateDuhamelMap,
 intervalDomainLift, hy] using hm.symm
 have hsem :=
 ShenWork.IntervalSemigroupC1ApproxIdentity.intervalFullSemigroupOperator_congr_on_Icc
 hinner (t - a) x.1
 have hm_t := SD.hmild t (ha.trans hat) htT x
 have hm_t' :
 truncatedConjugatePicardLimit p u₀ DT.T t x =
 truncatedConjugateDuhamelMap p u₀
 (truncatedConjugatePicardLimit p u₀ DT.T) t x := by
 simpa [SD] using hm_t
 dsimp only
 rw [hm_t']
 change
 intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1 +
 (-p.χ₀) * (∫ s in (0 : ℝ)..t,
 intervalConjugateKernelOperator (t - s) (Q s) x.1) +
 ∫ s in (0 : ℝ)..t,
 intervalFullSemigroupOperator (t - s) (L s) x.1 = _
 rw [hrestart, hsem]

private theorem intervalFullSemigroupOperator_neg
 (t : ℝ) (f : ℝ → ℝ) (x : ℝ) :
 intervalFullSemigroupOperator t (fun y => -f y) x =
 -intervalFullSemigroupOperator t f x := by
 unfold intervalFullSemigroupOperator
 rw [← MeasureTheory.integral_neg]
 apply integral_congr_ae
 filter_upwards [] with y
 ring

/-- Positive-part counterpart of the variational restart estimate used by the
negative-part energy argument. The homogeneous Neumann heat step is Markov
contractive; only the restart remainder is paired with the final positive
part. -/
theorem positivePartEnergy_sub_le_remainder_pairing
 {h : ℝ} (hh : 0 < h) {f u z : ℝ → ℝ} {M : ℝ}
 (hf_meas : AEStronglyMeasurable f (intervalMeasure 1))
 (hf_bdd : ∀ y, |f y| ≤ M)
 (hu_repr : ∀ᵐ x ∂intervalMeasure 1,
 u x = intervalFullSemigroupOperator h f x + z x)
 (huE : Integrable (fun x => (positivePart (u x)) ^ 2)
 (intervalMeasure 1))
 (hSE : Integrable
 (fun x => (positivePart (intervalFullSemigroupOperator h f x)) ^ 2)
 (intervalMeasure 1))
 (hpair : Integrable (fun x => (2 * positivePart (u x)) * z x)
 (intervalMeasure 1)) :
 (∫ x, (positivePart (u x)) ^ 2 ∂intervalMeasure 1) -
 ∫ x, (positivePart (f x)) ^ 2 ∂intervalMeasure 1 ≤
 ∫ x, (2 * positivePart (u x)) * z x ∂intervalMeasure 1 := by
 have hneg_repr : ∀ᵐ x ∂intervalMeasure 1,
 -u x = intervalFullSemigroupOperator h (fun y => -f y) x + (-z x) := by
 filter_upwards [hu_repr] with x hx
 rw [intervalFullSemigroupOperator_neg]
 linarith
 have hneg :=
 ShenWork.Paper2.IntervalNegativePartWeakEnergy.negativePartEnergy_sub_le_remainder_pairing
 hh hf_meas.neg (fun y => by simpa using hf_bdd y) hneg_repr
 (by simpa [negativePart, positivePart] using huE) (by
 have heq : (fun x =>
 negativePart (intervalFullSemigroupOperator h (-f) x) ^ 2) =
 fun x => positivePart (intervalFullSemigroupOperator h f x) ^ 2 := by
 funext x
 change negativePart
 (intervalFullSemigroupOperator h (fun y => -f y) x) ^ 2 = _
 rw [intervalFullSemigroupOperator_neg]
 simp [negativePart, positivePart]
 rw [heq]
 exact hSE) (by
 simpa [negativePart, positivePart] using hpair)
 simpa [negativePart, positivePart] using hneg

/-- Integration by parts for the already-matched divergence drift. There is
no `gₓ u z₊` term: after subtraction, the derivative of `g` multiplies only
the square of the comparison defect. -/
private theorem integral_drift_positivePart_chain
 {g φ : ℝ → ℝ}
 (hg : AbsolutelyContinuousOnInterval g 0 1)
 (hφ : AbsolutelyContinuousOnInterval φ 0 1)
 (hg0 : g 0 = 0) (hg1 : g 1 = 0) :
 (∫ x, g x * φ x * deriv φ x ∂intervalMeasure 1) =
 -(1 / 2 : ℝ) *
 (∫ x, deriv g x * φ x ^ 2 ∂intervalMeasure 1) := by
 have hsq : AbsolutelyContinuousOnInterval (φ * φ) 0 1 := hφ.mul hφ
 have hibp := hg.integral_mul_deriv_eq_deriv_mul hsq
 have hleft :
 (∫ x in (0 : ℝ)..1, g x * deriv (φ * φ) x) =
 2 * ∫ x in (0 : ℝ)..1, g x * φ x * deriv φ x := by
 rw [← intervalIntegral.integral_const_mul]
 apply intervalIntegral.integral_congr_ae
 filter_upwards [hφ.ae_differentiableAt] with x hx hxu
 have hd := (hx (Set.uIoc_subset_uIcc hxu)).hasDerivAt
 rw [(hd.mul hd).deriv]
 ring
 rw [hleft, hg0, hg1] at hibp
 simp only [Pi.mul_apply, zero_mul, zero_sub, neg_zero] at hibp
 have hright :
 (∫ x in (0 : ℝ)..1, deriv g x * (φ x * φ x)) =
 ∫ x in (0 : ℝ)..1, deriv g x * φ x ^ 2 := by
 apply intervalIntegral.integral_congr
 intro x _hx
 ring
 rw [hright] at hibp
 rw [intervalMeasure_integral_eq_intervalIntegral_energy,
 intervalMeasure_integral_eq_intervalIntegral_energy]
 nlinarith

/-! ## Resolver drift coefficient without a positivity floor -/

/-- The matched-divergence drift factor generated by a truncated slice. -/
def truncatedDriftFactor
 (p : CM2Params) (w : intervalDomainPoint → ℝ) : ℝ → ℝ :=
 fun y =>
 resolverGradReal p (positivePartSlice w) y *
 (1 + intervalDomainLift
 (ShenWork.PDE.intervalNeumannResolverR p (positivePartSlice w)) y) ^
 (-p.β)

/-- Uniform zeroth-order bound for the truncated drift factor. -/
def truncatedDriftFactorC0 (p : CM2Params) (M : ℝ) : ℝ :=
 Real.sqrt (∑' k : ℕ,
 (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
 (2 * (p.ν * M ^ p.γ))

/-- Uniform first-derivative bound for the truncated drift factor. -/
def truncatedDriftFactorC1 (p : CM2Params) (M : ℝ) : ℝ :=
 ShenWork.IntervalResolverWeakBounds.resolverWeakLapBound p M +
 p.β * truncatedDriftFactorC0 p M ^ 2

/-- The frozen logistic reaction coefficient in the matched operator. -/
def truncatedReactionCoefficient
 (p : CM2Params) (w : intervalDomainPoint → ℝ) : ℝ → ℝ :=
 fun y => p.a - p.b * positivePart (intervalDomainLift w y) ^ p.α

theorem truncatedLogisticLifted_eq_mul_reactionCoefficient
 (p : CM2Params) (w : intervalDomainPoint → ℝ) (y : ℝ) :
 truncatedLogisticLifted p w y =
 intervalDomainLift w y * truncatedReactionCoefficient p w y := by
 rfl

/-- The faithful truncated chemotaxis flux is the leading positive part times
the frozen matched-divergence drift factor. -/
theorem truncatedChemFluxLifted_eq_positivePart_mul_driftFactor
 (p : CM2Params) {w : intervalDomainPoint → ℝ}
 (hw : Continuous w) (y : ℝ) :
 truncatedChemFluxLifted p w y =
 positivePart (intervalDomainLift w y) * truncatedDriftFactor p w y := by
 let R : ℝ := intervalDomainLift
 (ShenWork.PDE.intervalNeumannResolverR p (positivePartSlice w)) y
 have hR : 0 ≤ R := by
 simpa [R, positivePartSlice] using
 (_root_.ShenWork.Paper2.TruncatedPositiveTimeBootstrap.resolverR_positivePart_lift_nonneg_of_continuous
 p hw y)
 rw [truncatedChemFluxLifted, truncatedDriftFactor,
 Real.rpow_neg (by linarith [hR])]
 have hslice : (fun x : intervalDomainPoint => positivePart (w x)) =
 positivePartSlice w := rfl
 rw [hslice, div_eq_mul_inv]
 ring

private theorem continuousOn_of_rpow_modulus
 {f : ℝ → ℝ} {s : Set ℝ} {C θ : ℝ}
 (hC : 0 ≤ C) (hθ : 0 < θ)
 (hmod : ∀ x ∈ s, ∀ y ∈ s,
 |f x - f y| ≤ C * |x - y| ^ θ) :
 ContinuousOn f s := by
 rw [Metric.continuousOn_iff]
 intro b hb ε hε
 have hcont : ContinuousAt (fun r : ℝ => C * r ^ θ) 0 :=
 continuousAt_const.mul (Real.continuous_rpow_const hθ.le).continuousAt
 rw [Metric.continuousAt_iff] at hcont
 obtain ⟨δ, hδ, hclose⟩ := hcont ε hε
 refine ⟨δ, hδ, ?_⟩
 intro a ha hab
 have hdist : dist (dist a b) 0 < δ := by
 simpa [Real.dist_eq] using hab
 have hm := hclose hdist
 have hm0 : C * (0 : ℝ) ^ θ = 0 := by
 rw [Real.zero_rpow hθ.ne']
 ring
 rw [hm0, Real.dist_eq, sub_zero,
 abs_of_nonneg (mul_nonneg hC (Real.rpow_nonneg dist_nonneg _))] at hm
 calc
 dist (f a) (f b) = |f a - f b| := Real.dist_eq _ _
 _ ≤ C * |a - b| ^ θ := hmod a ha b hb
 _ = C * dist a b ^ θ := by rw [Real.dist_eq]
 _ < ε := hm

private theorem intervalDomainLift_continuousOn_Icc
 {w : intervalDomainPoint → ℝ} (hw : Continuous w) :
 ContinuousOn (intervalDomainLift w) (Set.Icc (0 : ℝ) 1) := by
 rw [continuousOn_iff_continuous_restrict]
 have heq : Set.restrict (Set.Icc (0 : ℝ) 1) (intervalDomainLift w) = w := by
 funext ⟨x, hx⟩
 simp only [Set.restrict_apply, intervalDomainLift, dif_pos hx]
 exact congrArg w (Subtype.ext rfl)
 rw [heq]
 exact hw

private theorem truncatedDriftFactor_hasDerivAt
 (p : CM2Params) {w : intervalDomainPoint → ℝ} {M x : ℝ}
 (hw : Continuous w) (_hM : 0 ≤ M)
 (hbound : ∀ X, |w X| ≤ M) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
 HasDerivAt (truncatedDriftFactor p w)
 (deriv (truncatedDriftFactor p w) x) x := by
 let wp : intervalDomainPoint → ℝ := positivePartSlice w
 let R : ℝ → ℝ := intervalDomainLift
 (ShenWork.PDE.intervalNeumannResolverR p wp)
 let R1 : ℝ → ℝ := resolverGradReal p wp
 let R2 : ℝ → ℝ := fun y => deriv R1 y
 have hwp : Continuous wp := by
 simpa [wp, positivePartSlice, positivePart] using hw.max continuous_const
 have hwp_lift : ContinuousOn (intervalDomainLift wp) (Set.Icc (0 : ℝ) 1) :=
 intervalDomainLift_continuousOn_Icc hwp
 have hR0 : HasDerivAt R (R1 x) x := by
 simpa [R, R1] using
 ShenWork.IntervalResolverWeakBounds.intervalNeumannResolverR_lift_hasDerivAt_resolverGradReal_of_continuousOn
 p hwp_lift hx
 have hlb : ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ intervalDomainLift wp y := by
 intro y hy
 simp [wp, positivePartSlice, intervalDomainLift, hy, positivePart_nonneg]
 have hub : ∀ y ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift wp y ≤ M := by
 intro y hy
 simp only [wp, positivePartSlice, intervalDomainLift, dif_pos hy]
 exact (le_abs_self (positivePart (w ⟨y, hy⟩))).trans
 ((abs_positivePart_le_abs (w ⟨y, hy⟩)).trans (hbound ⟨y, hy⟩))
 have hR1base :=
 ShenWork.IntervalResolverWeakBounds.resolverGradReal_hasDerivAt_physicalLap_of_continuousOn
 p hwp_lift hlb hx
 have hR1 : HasDerivAt R1 (R2 x) x := by
 simpa [R1, R2, hR1base.deriv] using hR1base
 have hden : 1 ≤ 1 + R x := by
 have hnn :=
 _root_.ShenWork.Paper2.TruncatedPositiveTimeBootstrap.resolverR_positivePart_lift_nonneg_of_continuous
 p hw x
 have hnn' : 0 ≤ R x := by
 simpa [R, wp, positivePartSlice] using hnn
 linarith
 have h :=
 ShenWork.Paper2.TruncatedFluxC2Bounds.chemGrad_hasDerivAt
 (β := p.β) hR0 hR1 hden
 have heq : truncatedDriftFactor p w =
 fun y => R1 y * (1 + R y) ^ (-p.β) := by
 rfl
 rw [heq]
 simpa [h.deriv] using h

theorem truncatedDriftFactor_abs_le
 (p : CM2Params) {w : intervalDomainPoint → ℝ} {M x : ℝ}
 (hw : Continuous w) (_hM : 0 ≤ M)
 (hbound : ∀ X, |w X| ≤ M) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
 |truncatedDriftFactor p w x| ≤ truncatedDriftFactorC0 p M := by
 let wp : intervalDomainPoint → ℝ := positivePartSlice w
 let R : ℝ → ℝ := intervalDomainLift
 (ShenWork.PDE.intervalNeumannResolverR p wp)
 have hwp : Continuous wp := by
 simpa [wp, positivePartSlice, positivePart] using hw.max continuous_const
 have hwp_lift : ContinuousOn (intervalDomainLift wp) (Set.Icc (0 : ℝ) 1) :=
 intervalDomainLift_continuousOn_Icc hwp
 have hlb : ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ intervalDomainLift wp y := by
 intro y hy
 simp [wp, positivePartSlice, intervalDomainLift, hy, positivePart_nonneg]
 have hub : ∀ y ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift wp y ≤ M := by
 intro y hy
 simp only [wp, positivePartSlice, intervalDomainLift, dif_pos hy]
 exact (le_abs_self (positivePart (w ⟨y, hy⟩))).trans
 ((abs_positivePart_le_abs (w ⟨y, hy⟩)).trans (hbound ⟨y, hy⟩))
 have hR1 : |resolverGradReal p wp x| ≤ truncatedDriftFactorC0 p M := by
 simpa [truncatedDriftFactorC0] using
 ShenWork.IntervalResolverWeakBounds.resolverGrad_sup_le_of_bounded
 p hwp_lift hlb hub hx
 have hRnn : 0 ≤ R x := by
 simpa [R, wp, positivePartSlice] using
 (_root_.ShenWork.Paper2.TruncatedPositiveTimeBootstrap.resolverR_positivePart_lift_nonneg_of_continuous
 p hw x)
 have hpow :=
 ShenWork.Paper2.TruncatedFluxC2Bounds.chemGrad0_abs_le
 (A := 1 + R x) (e := -p.β)
 (by linarith) (by linarith [p.hβ]) hR1
 simpa [truncatedDriftFactor, R, wp] using hpow

private theorem truncatedDriftFactor_deriv_abs_le
 (p : CM2Params) {w : intervalDomainPoint → ℝ} {M x : ℝ}
 (hw : Continuous w) (hM : 0 ≤ M)
 (hbound : ∀ X, |w X| ≤ M) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
 |deriv (truncatedDriftFactor p w) x| ≤ truncatedDriftFactorC1 p M := by
 let wp : intervalDomainPoint → ℝ := positivePartSlice w
 let R : ℝ → ℝ := intervalDomainLift
 (ShenWork.PDE.intervalNeumannResolverR p wp)
 let R1 : ℝ → ℝ := resolverGradReal p wp
 let R2 : ℝ → ℝ := fun y => deriv R1 y
 let G0 : ℝ := truncatedDriftFactorC0 p M
 let H : ℝ := ShenWork.IntervalResolverWeakBounds.resolverWeakLapBound p M
 have hwp : Continuous wp := by
 simpa [wp, positivePartSlice, positivePart] using hw.max continuous_const
 have hwp_lift : ContinuousOn (intervalDomainLift wp) (Set.Icc (0 : ℝ) 1) :=
 intervalDomainLift_continuousOn_Icc hwp
 have hlb : ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ intervalDomainLift wp y := by
 intro y hy
 simp [wp, positivePartSlice, intervalDomainLift, hy, positivePart_nonneg]
 have hub : ∀ y ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift wp y ≤ M := by
 intro y hy
 simp only [wp, positivePartSlice, intervalDomainLift, dif_pos hy]
 exact (le_abs_self (positivePart (w ⟨y, hy⟩))).trans
 ((abs_positivePart_le_abs (w ⟨y, hy⟩)).trans (hbound ⟨y, hy⟩))
 have hG0 : 0 ≤ G0 := by
 dsimp [G0, truncatedDriftFactorC0]
 exact mul_nonneg (Real.sqrt_nonneg _)
 (mul_nonneg (by norm_num)
 (mul_nonneg p.hν.le (Real.rpow_nonneg hM _)))
 have hH : 0 ≤ H := by
 dsimp [H, ShenWork.IntervalResolverWeakBounds.resolverWeakLapBound,
 ShenWork.IntervalResolverWeakBounds.resolverWeakValueBound]
 exact add_nonneg
 (mul_nonneg p.hμ.le
 (mul_nonneg (Real.sqrt_nonneg _)
 (mul_nonneg (by norm_num)
 (mul_nonneg p.hν.le (Real.rpow_nonneg hM _)))))
 (mul_nonneg p.hν.le (Real.rpow_nonneg hM _))
 have hR1b : |R1 x| ≤ G0 := by
 simpa [R1, G0, truncatedDriftFactorC0] using
 ShenWork.IntervalResolverWeakBounds.resolverGrad_sup_le_of_bounded
 p hwp_lift hlb hub (Set.Ioo_subset_Icc_self hx)
 have hR2b : |R2 x| ≤ H := by
 simpa [R1, R2, H] using
 ShenWork.IntervalResolverWeakBounds.deriv_resolverGradReal_abs_le_of_bounded
 p hwp_lift hlb hub hx
 have hR0 : HasDerivAt R (R1 x) x := by
 simpa [R, R1] using
 ShenWork.IntervalResolverWeakBounds.intervalNeumannResolverR_lift_hasDerivAt_resolverGradReal_of_continuousOn
 p hwp_lift hx
 have hR1base :=
 ShenWork.IntervalResolverWeakBounds.resolverGradReal_hasDerivAt_physicalLap_of_continuousOn
 p hwp_lift hlb hx
 have hR1 : HasDerivAt R1 (R2 x) x := by
 simpa [R1, R2, hR1base.deriv] using hR1base
 have hRnn : 0 ≤ R x := by
 simpa [R, wp, positivePartSlice] using
 (_root_.ShenWork.Paper2.TruncatedPositiveTimeBootstrap.resolverR_positivePart_lift_nonneg_of_continuous
 p hw x)
 have hden : 1 ≤ 1 + R x := by linarith
 have hder := ShenWork.Paper2.TruncatedFluxC2Bounds.chemGrad_hasDerivAt
 (β := p.β) hR0 hR1 hden
 have hterm0 : |R2 x * (1 + R x) ^ (-p.β)| ≤ H := by
 exact ShenWork.Paper2.TruncatedFluxC2Bounds.chemGrad0_abs_le
 hden (by linarith [p.hβ]) hR2b
 have hden1 : |(-p.β) * (1 + R x) ^ (-p.β - 1) * R1 x| ≤ p.β * G0 := by
 exact ShenWork.Paper2.TruncatedFluxC2Bounds.denom1_abs_le
 p.hβ hden hR1b
 have hterm1 :
 |R1 x * (-p.β * (1 + R x) ^ (-p.β - 1) * R1 x)| ≤
 p.β * G0 ^ 2 := by
 rw [abs_mul]
 calc
 |R1 x| * |(-p.β) * (1 + R x) ^ (-p.β - 1) * R1 x|
 ≤ G0 * (p.β * G0) :=
 mul_le_mul hR1b hden1 (abs_nonneg _) hG0
 _ = p.β * G0 ^ 2 := by ring
 rw [show deriv (truncatedDriftFactor p w) x =
 R2 x * (1 + R x) ^ (-p.β) +
 R1 x * (-p.β * (1 + R x) ^ (-p.β - 1) * R1 x) by
 simpa [truncatedDriftFactor, R, R1, R2, wp] using hder.deriv]
 exact (abs_add_le _ _).trans (by
 simpa [truncatedDriftFactorC1, G0, H] using add_le_add hterm0 hterm1)

/-- Closed-interval regularity and the bounds needed by the matched barrier.
No lower floor for the solution occurs. -/
theorem truncatedDriftFactor_regular
 (p : CM2Params) {w : intervalDomainPoint → ℝ} {M : ℝ}
 (hw : Continuous w) (hM : 0 ≤ M)
 (hbound : ∀ X, |w X| ≤ M) :
 ContinuousOn (truncatedDriftFactor p w) (Set.Icc (0 : ℝ) 1) ∧
 AbsolutelyContinuousOnInterval (truncatedDriftFactor p w) 0 1 ∧
 truncatedDriftFactor p w 0 = 0 ∧ truncatedDriftFactor p w 1 = 0 ∧
 (∀ x ∈ Set.Icc (0 : ℝ) 1,
 |truncatedDriftFactor p w x| ≤ truncatedDriftFactorC0 p M) ∧
 (∀ x ∈ Set.Ioo (0 : ℝ) 1,
 |deriv (truncatedDriftFactor p w) x| ≤ truncatedDriftFactorC1 p M) := by
 let wp : intervalDomainPoint → ℝ := positivePartSlice w
 let R : ℝ → ℝ := intervalDomainLift
 (ShenWork.PDE.intervalNeumannResolverR p wp)
 let R1 : ℝ → ℝ := resolverGradReal p wp
 let C0 : ℝ := truncatedDriftFactorC0 p M
 let C1 : ℝ := truncatedDriftFactorC1 p M
 let θ : ℝ := 1 / 4
 let CH : ℝ :=
 (2 : ℝ) ^ (1 - θ) *
 Real.sqrt (∑' k : ℕ,
 (ShenWork.IntervalResolverWeakBounds.intervalNeumannResolverGradHolderWeight
 p θ k) ^ 2) *
 (2 * (p.ν * M ^ p.γ))
 have hwp : Continuous wp := by
 simpa [wp, positivePartSlice, positivePart] using hw.max continuous_const
 have hwp_lift : ContinuousOn (intervalDomainLift wp) (Set.Icc (0 : ℝ) 1) :=
 intervalDomainLift_continuousOn_Icc hwp
 have hlb : ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ intervalDomainLift wp y := by
 intro y hy
 simp [wp, positivePartSlice, intervalDomainLift, hy, positivePart_nonneg]
 have hub : ∀ y ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift wp y ≤ M := by
 intro y hy
 simp only [wp, positivePartSlice, intervalDomainLift, dif_pos hy]
 exact (le_abs_self (positivePart (w ⟨y, hy⟩))).trans
 ((abs_positivePart_le_abs (w ⟨y, hy⟩)).trans (hbound ⟨y, hy⟩))
 have hC0 : 0 ≤ C0 := by
 dsimp [C0, truncatedDriftFactorC0]
 exact mul_nonneg (Real.sqrt_nonneg _)
 (mul_nonneg (by norm_num)
 (mul_nonneg p.hν.le (Real.rpow_nonneg hM _)))
 have hC1 : 0 ≤ C1 := by
 dsimp [C1, truncatedDriftFactorC1]
 have hH : 0 ≤ ShenWork.IntervalResolverWeakBounds.resolverWeakLapBound p M := by
 dsimp [ShenWork.IntervalResolverWeakBounds.resolverWeakLapBound,
 ShenWork.IntervalResolverWeakBounds.resolverWeakValueBound]
 exact add_nonneg
 (mul_nonneg p.hμ.le
 (mul_nonneg (Real.sqrt_nonneg _)
 (mul_nonneg (by norm_num)
 (mul_nonneg p.hν.le (Real.rpow_nonneg hM _)))))
 (mul_nonneg p.hν.le (Real.rpow_nonneg hM _))
 exact add_nonneg hH (mul_nonneg p.hβ (sq_nonneg _))
 have hθ0 : 0 < θ := by norm_num [θ]
 have hθhalf : θ < (1 / 2 : ℝ) := by norm_num [θ]
 have hCH : 0 ≤ CH := by
 dsimp [CH]
 exact mul_nonneg
 (mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
 (Real.sqrt_nonneg _))
 (mul_nonneg (by norm_num)
 (mul_nonneg p.hν.le (Real.rpow_nonneg hM _)))
 have hRcont : ContinuousOn R (Set.Icc (0 : ℝ) 1) := by
 apply continuousOn_of_rpow_modulus hC0 (show (0 : ℝ) < 1 by norm_num)
 intro x hx y hy
 simpa [R, C0, truncatedDriftFactorC0, Real.rpow_one] using
 (ShenWork.IntervalResolverWeakBounds.intervalNeumannResolverR_lift_holder_Icc_of_bounded
 p (M := M) (θ := (1 : ℝ)) (by norm_num) (by norm_num)
 hwp_lift hlb hub hx hy)
 have hR1cont : ContinuousOn R1 (Set.Icc (0 : ℝ) 1) := by
 apply continuousOn_of_rpow_modulus hCH hθ0
 intro x hx y hy
 simpa [R1, CH, θ] using
 (ShenWork.IntervalResolverWeakBounds.resolverGradReal_holder_Icc_of_bounded_smallTheta
 p (M := M) (θ := θ) hθ0 hθhalf hwp_lift hlb hub hx hy)
 have hRnn : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ R x := by
 intro x hx
 simpa [R, wp, positivePartSlice] using
 (_root_.ShenWork.Paper2.TruncatedPositiveTimeBootstrap.resolverR_positivePart_lift_nonneg_of_continuous
 p hw x)
 have hpowcont : ContinuousOn (fun x => (1 + R x) ^ (-p.β))
 (Set.Icc (0 : ℝ) 1) := by
 have hbase : ContinuousOn (fun x => 1 + R x) (Set.Icc (0 : ℝ) 1) := by
 simpa using continuousOn_const.add hRcont
 exact hbase.rpow_const (fun x hx => Or.inl
 (show 0 < 1 + R x by linarith [hRnn x hx]).ne')
 have hgcont : ContinuousOn (truncatedDriftFactor p w) (Set.Icc (0 : ℝ) 1) := by
 simpa [truncatedDriftFactor, R, R1, wp] using hR1cont.mul hpowcont
 have hglip_open : LipschitzOnWith ⟨C1, hC1⟩ (truncatedDriftFactor p w)
 (Set.Ioo (0 : ℝ) 1) := by
 apply Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
 (convex_Ioo (0 : ℝ) 1)
 · intro x hx
 exact (truncatedDriftFactor_hasDerivAt p hw hM hbound hx).hasDerivWithinAt
 · intro x hx
 rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_mk, Real.norm_eq_abs]
 exact truncatedDriftFactor_deriv_abs_le p hw hM hbound hx
 have hglip : LipschitzOnWith ⟨C1, hC1⟩ (truncatedDriftFactor p w)
 (Set.Icc (0 : ℝ) 1) := by
 rw [← closure_Ioo (zero_ne_one' ℝ)]
 exact hglip_open.closure (by
 simpa [closure_Ioo (zero_ne_one' ℝ)] using hgcont)
 have hgac : AbsolutelyContinuousOnInterval (truncatedDriftFactor p w) 0 1 := by
 have hu : Set.Icc (0 : ℝ) 1 = Set.uIcc (0 : ℝ) 1 := by
 rw [Set.uIcc_of_le (by norm_num)]
 rw [hu] at hglip
 exact hglip.absolutelyContinuousOnInterval
 refine ⟨hgcont, hgac, ?_, ?_, ?_, ?_⟩
 · simp [truncatedDriftFactor, resolverGradReal_zero]
 · simp [truncatedDriftFactor, resolverGradReal_one]
 · intro x hx
 simpa [C0] using truncatedDriftFactor_abs_le p hw hM hbound hx
 · intro x hx
 simpa [C1] using truncatedDriftFactor_deriv_abs_le p hw hM hbound hx

/-! ## Matched-divergence positive-part energy closure

The analytic producer below this scalar layer must keep the chemotaxis drift
in divergence form for both trajectories. Once its Stampacchia test has
produced the half-energy inequality, the rest is the same finite-interval
Gronwall closure as in the negative-part argument. -/

/-- Lifted positive comparison defect `(w-u)₊`. -/
def comparisonPositivePartLift
 (w u : ℝ → intervalDomainPoint → ℝ) (t : ℝ) : ℝ → ℝ :=
 fun x => positivePart
 (intervalDomainLift (w t) x - intervalDomainLift (u t) x)

/-- Squared `L²` energy of the positive comparison defect. -/
def comparisonPositivePartEnergy
 (w u : ℝ → intervalDomainPoint → ℝ) (t : ℝ) : ℝ :=
 ∫ x, (comparisonPositivePartLift w u t x) ^ 2 ∂intervalMeasure 1

/-- Scalar output of a matched-divergence Stampacchia comparison.

The producer of this record is responsible for the weak PDE subtraction,
the positive-part spatial chain rule, and Young absorption of the bounded
drift. In particular its drift hypothesis is a bound on `g`, not on `gₓ`.
-/
structure PositivePartComparisonEnergyCoreData
 (s T : ℝ) (w u : ℝ → intervalDomainPoint → ℝ) where
 hsT : s ≤ T
 ell : ℝ
 hell_nonneg : 0 ≤ ell
 E' : ℝ → ℝ
 half_energy_deriv_le :
 ∀ t ∈ Set.Ico s T,
 (1 / 2 : ℝ) * E' t ≤ ell * comparisonPositivePartEnergy w u t
 energy_cont :
 ContinuousOn (comparisonPositivePartEnergy w u) (Set.Icc s T)
 energy_has_deriv :
 ∀ t ∈ Set.Ico s T,
 HasDerivWithinAt (comparisonPositivePartEnergy w u) (E' t)
 (Set.Ici t) t
 initial_zero : comparisonPositivePartEnergy w u s = 0
 zero_energy_to_pointwise_le :
 ∀ t ∈ Set.Icc s T,
 comparisonPositivePartEnergy w u t = 0 →
 ∀ x : intervalDomainPoint, w t x ≤ u t x

/-- Close a matched-divergence positive-part energy estimate by Gronwall. -/
theorem pointwise_le_of_positivePartComparisonEnergyCoreData
 {s T : ℝ} {w u : ℝ → intervalDomainPoint → ℝ}
 (H : PositivePartComparisonEnergyCoreData s T w u) :
 ∀ t ∈ Set.Icc s T, ∀ x : intervalDomainPoint, w t x ≤ u t x := by
 intro t ht x
 let E : ℝ → ℝ := comparisonPositivePartEnergy w u
 have hcont : ContinuousOn E (Set.Icc s t) := by
 exact H.energy_cont.mono (Set.Icc_subset_Icc le_rfl ht.2)
 have hderiv : ∀ r ∈ Set.Ico s t,
 HasDerivWithinAt E (H.E' r) (Set.Ici r) r := by
 intro r hr
 exact H.energy_has_deriv r ⟨hr.1, hr.2.trans_le ht.2⟩
 have hbound : ∀ r ∈ Set.Ico s t,
 H.E' r ≤ (2 * H.ell) * E r := by
 intro r hr
 have hh := H.half_energy_deriv_le r ⟨hr.1, hr.2.trans_le ht.2⟩
 dsimp [E]
 nlinarith
 have hgron : E t ≤ E s * Real.exp ((2 * H.ell) * (t - s)) :=
 ShenWork.Paper2.intervalDomainL2_gronwall_exp_of_diffIneq
 ht.1 hcont hderiv hbound
 have hEt_nonpos : E t ≤ 0 := by
 simpa [E, H.initial_zero] using hgron
 have hEt_nonneg : 0 ≤ E t := by
 exact integral_nonneg fun y => sq_nonneg (comparisonPositivePartLift w u t y)
 have hEt : comparisonPositivePartEnergy w u t = 0 := by
 exact le_antisymm hEt_nonpos hEt_nonneg
 exact H.zero_energy_to_pointwise_le t ht hEt x

end ShenWork.Paper2.IntervalTruncatedWeakBarrierComparison
