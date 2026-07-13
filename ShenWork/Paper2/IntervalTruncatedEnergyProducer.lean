/-
 Direct weak-form energy producer for the faithful truncated Picard limit.

 This file deliberately avoids the positive-time coefficient bootstrap. The
 weak PDE is obtained from the Neumann heat/Duhamel decomposition in
 `IntervalBFormCron2SemigroupWeakDuhamel`; energy regularity is then assembled
 at the variational level.
-/

import ShenWork.Paper2.IntervalChiNegUniformCoreComplete
import ShenWork.Paper2.IntervalBFormTruncatedBridgeProducerData
import ShenWork.Paper2.IntervalBFormCron2SemigroupWeakDuhamel
import ShenWork.Paper2.IntervalNeumannHeatGradientL2
import ShenWork.Paper2.IntervalBFormCron2RegularNegativePartEnergyA2
import ShenWork.Paper2.IntervalBFormCron2RegularNegativePartEnergyA3
import ShenWork.Paper2.IntervalBFormCron2EnergyRegularityConcrete
import ShenWork.Paper2.IntervalTruncatedPicardIterJointContinuity
import ShenWork.Paper2.IntervalTruncatedPicardLimitJointContinuity
import ShenWork.Paper2.IntervalConjugateChemFluxIntegrable
import ShenWork.Paper2.IntervalTruncatedPositiveTimeLipschitz
import ShenWork.Paper2.IntervalConjugateMildTimeContinuity
import ShenWork.Paper2.IntervalFullDuhamelRestart
import ShenWork.Paper2.IntervalChiNegTruncatedRestartStrictPosProducer
import ShenWork.Paper2.IntervalNegativePartWeakEnergy
import ShenWork.PDE.IntervalDomainContinuousExtension
import ShenWork.PDE.IntervalSemigroupUniform
import ShenWork.PDE.IntervalSemigroupC1ApproxIdentity

open Filter Topology Set MeasureTheory
open scoped BigOperators Topology ENNReal

noncomputable section

namespace ShenWork.Paper2.IntervalTruncatedEnergyProducer

open ShenWork.IntervalDomain
 (intervalDomain intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalConjugatePicard
 (UniformConjugateMildExistenceCore)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.IntervalConjugateDuhamelMap (intervalConjugateKernelOperator)
open ShenWork.IntervalConjugateChemFluxIntegrable
 (conjugateDuhamel_intervalIntegrable_of_measurable_bound)
open ShenWork.Paper2.BFormPositiveDatumNegPart

/-- The exact expansion of
`IntervalChiNegAssembly.UniformTruncatedEnergyData`. Keeping the producer
on this expansion avoids importing the unrelated Jensen assembly chain. -/
abbrev UniformTruncatedEnergyDataDirect (p : CM2Params) : Type :=
 ∀ {M : ℝ}, 0 < M → ∀ {u₀ : intervalDomainPoint → ℝ},
 PositiveInitialDatum intervalDomain u₀ → (∀ x, |u₀ x| ≤ M) →
 ∀ C : UniformConjugateMildExistenceCore p u₀,
 ∀ A : UniformTruncatedConjugateMapCertificate p C,
 TruncatedNegativePartEnergyCoreRegularData p
 (uniformTruncatedConjugateMildExistenceCore_of_uniformCore C A).toData

/-- The L² Neumann heat-gradient estimate used by the direct weak-Duhamel
route is already available with constant one. -/
theorem neumannHeatGradientTMinusHalfBound :
 NeumannHeatGradientTMinusHalfBound :=
 ShenWork.IntervalNeumannHeatGradientL2.neumannHeatGradientTMinusHalfBound_proof

/-! ## Algebraic adapter from the direct weak identity

The legacy energy record stores a coefficient certificate even though its
consumer uses only the resulting weak identity. A single nonzero positive
cosine test mode is enough to encode the three scalar pairings in a
finite-support coefficient certificate. -/

private def singleSeq (k : ℕ) (a : ℝ) : ℕ → ℝ :=
 Pi.single (M := fun _ => ℝ) k a

private theorem singleSeq_hasSum (k : ℕ) (a : ℝ) :
 HasSum (singleSeq k a) a := by
 change HasSum (fun n : ℕ => Pi.single (M := fun _ => ℝ) k a n) a
 convert hasSum_single
 (f := fun n : ℕ => Pi.single (M := fun _ => ℝ) k a n) k
 (fun b hb => by simp [Pi.single, Function.update, hb]) using 1 <;> simp

/-- A direct weak identity can be packaged in the coefficient-shaped legacy
interface whenever the negative-part test has a nonzero positive cosine mode.
The sequences are supported at that one mode; no coefficient regularity or
summability of the solution is used. -/
def coefficientWeakTestData_of_weakIdentity_of_nonzeroMode
 {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {t : ℝ}
 (hweak : NegativePartWeakTestIdentityAt p u t)
 {k : ℕ} (hk : k ≠ 0)
 (hmode : cosineTestCoeff (negativePartTest u t) k ≠ 0) :
 NegativePartCoefficientWeakTestData p u t := by
 classical
 let φhat : ℕ → ℝ := fun n => cosineTestCoeff (negativePartTest u t) n
 let A : ℝ :=
 ∫ x,
 intervalDomainLift
 (fun z : intervalDomainPoint => intervalDomain.timeDeriv u t z) x *
 negativePartTest u t x
 ∂ intervalMeasure 1
 let B : ℝ :=
 ∫ x,
 deriv (intervalDomainLift (u t)) x * deriv (negativePartTest u t) x
 ∂ intervalMeasure 1
 let C : ℝ :=
 p.χ₀ *
 (∫ x,
 truncatedChemFluxLifted p (u t) x *
 deriv (negativePartTest u t) x
 ∂ intervalMeasure 1) +
 ∫ x, truncatedLogisticLifted p (u t) x * negativePartTest u t x
 ∂ intervalMeasure 1
 have hABC : A + B = C := by
 simpa [A, B, C, NegativePartWeakTestIdentityAt] using hweak
 have hlam : unitIntervalCosineEigenvalue k ≠ 0 := by
 have : 0 < unitIntervalCosineEigenvalue k := by
 unfold unitIntervalCosineEigenvalue
 have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
 positivity
 exact ne_of_gt this
 have hphi : φhat k ≠ 0 := by simpa [φhat] using hmode
 let coeff : ℕ → ℝ := singleSeq k (B / (unitIntervalCosineEigenvalue k * φhat k))
 let coeffTimeDeriv : ℕ → ℝ := singleSeq k (A / φhat k)
 let sourceCoeff : ℕ → ℝ := singleSeq k (C / φhat k)
 have hlap_eq :
 (fun n : ℕ => unitIntervalCosineEigenvalue n * coeff n * φhat n) =
 singleSeq k B := by
 funext n
 by_cases hnk : n = k
 · subst n
 simp only [coeff, singleSeq, Pi.single_eq_same]
 field_simp
 · simp [coeff, singleSeq, Pi.single_eq_of_ne hnk]
 have htime_eq :
 (fun n : ℕ => coeffTimeDeriv n * φhat n) = singleSeq k A := by
 funext n
 by_cases hnk : n = k
 · subst n
 simp only [coeffTimeDeriv, singleSeq, Pi.single_eq_same]
 field_simp
 · simp [coeffTimeDeriv, singleSeq, Pi.single_eq_of_ne hnk]
 have hsource_eq :
 (fun n : ℕ => sourceCoeff n * φhat n) = singleSeq k C := by
 funext n
 by_cases hnk : n = k
 · subst n
 simp only [sourceCoeff, singleSeq, Pi.single_eq_same]
 field_simp
 · simp [sourceCoeff, singleSeq, Pi.single_eq_of_ne hnk]
 refine
 { coeff := coeff
 coeffTimeDeriv := coeffTimeDeriv
 sourceCoeff := sourceCoeff
 coeff_ode := ?_
 lap_summable := ?_
 source_summable := ?_
 time_leibniz_tsum := ?_
 gradient_ibp_tsum := ?_
 source_pairing := ?_ }
 · intro n
 by_cases hnk : n = k
 · subst n
 simp only [coeffTimeDeriv, coeff, sourceCoeff, singleSeq,
 Pi.single_eq_same]
 field_simp
 linarith
 · simp [coeffTimeDeriv, coeff, sourceCoeff, singleSeq,
 Pi.single_eq_of_ne hnk]
 · change Summable (fun n : ℕ => unitIntervalCosineEigenvalue n * coeff n * φhat n)
 rw [hlap_eq]
 exact (singleSeq_hasSum k B).summable
 · change Summable (fun n : ℕ => sourceCoeff n * φhat n)
 rw [hsource_eq]
 exact (singleSeq_hasSum k C).summable
 · change A = ∑' n : ℕ, coeffTimeDeriv n * φhat n
 rw [htime_eq, (singleSeq_hasSum k A).tsum_eq]
 · change B = ∑' n : ℕ, unitIntervalCosineEigenvalue n * coeff n * φhat n
 rw [hlap_eq, (singleSeq_hasSum k B).tsum_eq]
 · change (∑' n : ℕ, sourceCoeff n * φhat n) = C
 rw [hsource_eq, (singleSeq_hasSum k C).tsum_eq]

/-- Zero-mode version of the finite-support adapter. It applies when the
spatial-gradient pairing vanishes, since the Neumann zero mode has eigenvalue
zero. -/
def coefficientWeakTestData_of_weakIdentity_of_zeroMode
 {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {t : ℝ}
 (hweak : NegativePartWeakTestIdentityAt p u t)
 (hgrad :
 (∫ x,
 deriv (intervalDomainLift (u t)) x * deriv (negativePartTest u t) x
 ∂ intervalMeasure 1) = 0)
 (hmode : cosineTestCoeff (negativePartTest u t) 0 ≠ 0) :
 NegativePartCoefficientWeakTestData p u t := by
 classical
 let φhat : ℕ → ℝ := fun n => cosineTestCoeff (negativePartTest u t) n
 let A : ℝ :=
 ∫ x,
 intervalDomainLift
 (fun z : intervalDomainPoint => intervalDomain.timeDeriv u t z) x *
 negativePartTest u t x
 ∂ intervalMeasure 1
 let C : ℝ :=
 p.χ₀ *
 (∫ x,
 truncatedChemFluxLifted p (u t) x *
 deriv (negativePartTest u t) x
 ∂ intervalMeasure 1) +
 ∫ x, truncatedLogisticLifted p (u t) x * negativePartTest u t x
 ∂ intervalMeasure 1
 have hAC : A = C := by
 have h := hweak
 unfold NegativePartWeakTestIdentityAt at h
 simpa [A, C, hgrad] using h
 have hphi : φhat 0 ≠ 0 := by simpa [φhat] using hmode
 let coeffTimeDeriv : ℕ → ℝ := singleSeq 0 (A / φhat 0)
 let sourceCoeff : ℕ → ℝ := singleSeq 0 (C / φhat 0)
 have htime_eq :
 (fun n : ℕ => coeffTimeDeriv n * φhat n) = singleSeq 0 A := by
 funext n
 by_cases hn : n = 0
 · subst n
 simp only [coeffTimeDeriv, singleSeq, Pi.single_eq_same]
 field_simp
 · simp [coeffTimeDeriv, singleSeq, Pi.single_eq_of_ne hn]
 have hsource_eq :
 (fun n : ℕ => sourceCoeff n * φhat n) = singleSeq 0 C := by
 funext n
 by_cases hn : n = 0
 · subst n
 simp only [sourceCoeff, singleSeq, Pi.single_eq_same]
 field_simp
 · simp [sourceCoeff, singleSeq, Pi.single_eq_of_ne hn]
 refine
 { coeff := fun _ => 0
 coeffTimeDeriv := coeffTimeDeriv
 sourceCoeff := sourceCoeff
 coeff_ode := ?_
 lap_summable := ?_
 source_summable := ?_
 time_leibniz_tsum := ?_
 gradient_ibp_tsum := ?_
 source_pairing := ?_ }
 · intro n
 by_cases hn : n = 0
 · subst n
 simp only [coeffTimeDeriv, sourceCoeff, singleSeq, Pi.single_eq_same,
 mul_zero, neg_zero, zero_add]
 rw [hAC]
 · simp [coeffTimeDeriv, sourceCoeff, singleSeq, Pi.single_eq_of_ne hn]
 · simp
 · change Summable (fun n : ℕ => sourceCoeff n * φhat n)
 rw [hsource_eq]
 exact (singleSeq_hasSum 0 C).summable
 · change A = ∑' n : ℕ, coeffTimeDeriv n * φhat n
 rw [htime_eq, (singleSeq_hasSum 0 A).tsum_eq]
 · simpa [hgrad]
 · change (∑' n : ℕ, sourceCoeff n * φhat n) = C
 rw [hsource_eq, (singleSeq_hasSum 0 C).tsum_eq]

/-- Degenerate finite-support adapter when all three tested scalar pairings
vanish. -/
def coefficientWeakTestData_of_zeroPairings
 {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {t : ℝ}
 (htime :
 (∫ x,
 intervalDomainLift
 (fun z : intervalDomainPoint => intervalDomain.timeDeriv u t z) x *
 negativePartTest u t x
 ∂ intervalMeasure 1) = 0)
 (hgrad :
 (∫ x,
 deriv (intervalDomainLift (u t)) x * deriv (negativePartTest u t) x
 ∂ intervalMeasure 1) = 0)
 (hsource :
 p.χ₀ *
 (∫ x,
 truncatedChemFluxLifted p (u t) x *
 deriv (negativePartTest u t) x
 ∂ intervalMeasure 1) +
 ∫ x, truncatedLogisticLifted p (u t) x * negativePartTest u t x
 ∂ intervalMeasure 1 = 0) :
 NegativePartCoefficientWeakTestData p u t := by
 refine
 { coeff := fun _ => 0
 coeffTimeDeriv := fun _ => 0
 sourceCoeff := fun _ => 0
 coeff_ode := by simp
 lap_summable := by simp
 source_summable := by simp
 time_leibniz_tsum := by simpa [htime]
 gradient_ibp_tsum := by simpa [hgrad]
 source_pairing := by simpa [hsource] }

/-! ## Cosine totality for the adapter's remaining branch -/

private lemma memLpTwo_of_continuousOn_unitInterval
 {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1)) :
 MemLp f (2 : ℝ≥0∞) (intervalMeasure 1) := by
 obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
 have hmeas : AEStronglyMeasurable f (intervalMeasure 1) :=
 ShenWork.IntervalDuhamelIntegrability.continuousOn_aestronglyMeasurable_intervalMeasure
 hf
 refine MemLp.of_bound hmeas C ?_
 unfold intervalMeasure ShenWork.IntervalDomain.intervalSet
 filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
 simpa [Real.norm_eq_abs] using hC x hx

private lemma cosineMode_intervalIntegral (n : ℕ) :
 (∫ x in (0 : ℝ)..1, cosineMode n x) = if n = 0 then 1 else 0 := by
 by_cases hn : n = 0
 · subst n
 simp [cosineMode]
 · rw [if_neg hn]
 have horth :=
 ShenWork.CosineSpectrum.cosineMode_orthogonal
 (m := n) (n := 0) hn
 simpa [cosineMode] using horth

/-- If every positive Neumann cosine coefficient of a continuous function
vanishes, the function is constant on the closed unit interval. -/
theorem eqOn_const_of_positive_cosineTestCoeff_eq_zero
 {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
 (hcoeff : ∀ n : ℕ, n ≠ 0 → cosineTestCoeff f n = 0) :
 Set.EqOn f (fun _ => cosineTestCoeff f 0) (Set.Icc (0 : ℝ) 1) := by
 let c : ℝ := cosineTestCoeff f 0
 let g : ℝ → ℝ := fun x => f x - c
 have hgcont : ContinuousOn g (Set.Icc (0 : ℝ) 1) := by
 exact hf.sub continuousOn_const
 have hgmem : MemLp g (2 : ℝ≥0∞) (intervalMeasure 1) :=
 memLpTwo_of_continuousOn_unitInterval hgcont
 have hgreal :
 ∀ n : ℕ, (∫ x in (0 : ℝ)..1, cosineMode n x * g x) = 0 := by
 intro n
 have hcos_int : IntervalIntegrable (fun x : ℝ => cosineMode n x)
 volume 0 1 := by
 apply Continuous.intervalIntegrable
 unfold cosineMode
 fun_prop
 have hprod_int : IntervalIntegrable (fun x : ℝ => cosineMode n x * f x)
 volume 0 1 := by
 have hprod_cont : ContinuousOn (fun x : ℝ => cosineMode n x * f x)
 (Set.uIcc (0 : ℝ) 1) := by
 have hmode : Continuous (cosineMode n) := by
 unfold cosineMode
 fun_prop
 simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
 hmode.continuousOn.mul hf
 exact hprod_cont.intervalIntegrable
 calc
 (∫ x in (0 : ℝ)..1, cosineMode n x * g x)
 = (∫ x in (0 : ℝ)..1,
 cosineMode n x * f x - c * cosineMode n x) := by
 apply intervalIntegral.integral_congr
 intro x _hx
 simp [g]
 ring
 _ = (∫ x in (0 : ℝ)..1, cosineMode n x * f x) -
 ∫ x in (0 : ℝ)..1, c * cosineMode n x := by
 rw [intervalIntegral.integral_sub hprod_int
 (hcos_int.const_mul c)]
 _ = cosineTestCoeff f n -
 c * (∫ x in (0 : ℝ)..1, cosineMode n x) := by
 rw [intervalIntegral.integral_const_mul]
 rfl
 _ = 0 := by
 by_cases hn : n = 0
 · subst n
 simp [c, cosineMode_intervalIntegral, cosineTestCoeff]
 · rw [hcoeff n hn, cosineMode_intervalIntegral n, if_neg hn]
 ring
 have hgcomplex :
 (fun x : ℝ => ((g x : ℝ) : ℂ))
 =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] 0 := by
 apply ShenWork.CosineParsevalBridge.unitIntervalCosine_nat_total_ae_zero
 · exact
 ShenWork.HeatKernelGradientEstimates.unitInterval_memLp_two_intervalIntegrable
 hgmem.ofReal
 · exact
 ShenWork.HeatKernelGradientEstimates.unitIntervalEvenReflection_memLp_two
 hgmem.ofReal
 · exact
 ShenWork.HeatKernelGradientEstimates.unitInterval_memLp_two_norm_sq_intervalIntegrable
 hgmem.ofReal
 · intro n
 have hcast := congrArg (fun r : ℝ => (r : ℂ)) (hgreal n)
 calc
 (∫ x in (0 : ℝ)..1,
 (Real.cos ((n : ℝ) * Real.pi * x) : ℂ) * (g x : ℂ))
 = ∫ x in (0 : ℝ)..1,
 ((cosineMode n x * g x : ℝ) : ℂ) := by
 apply intervalIntegral.integral_congr
 intro x _hx
 simp [cosineMode]
 _ = ((∫ x in (0 : ℝ)..1,
 cosineMode n x * g x : ℝ) : ℂ) := by
 exact intervalIntegral.integral_ofReal
 _ = 0 := hcast
 have hgreal_ae :
 g =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] fun _ => 0 := by
 filter_upwards [hgcomplex] with x hx
 have hre := congrArg Complex.re hx
 simpa using hre
 rw [MeasureTheory.restrict_Ioc_eq_restrict_Icc] at hgreal_ae
 have hgeq : Set.EqOn g (fun _ : ℝ => 0) (Set.Icc (0 : ℝ) 1) := by
 refine MeasureTheory.Measure.eqOn_of_ae_eq hgreal_ae hgcont continuousOn_const ?_
 rw [interior_Icc, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
 intro x hx
 have hgzero := hgeq hx
 simpa [g, c] using sub_eq_zero.mp hgzero

private theorem ae_mem_Ioo_unitInterval :
 ∀ᵐ x ∂ intervalMeasure 1, x ∈ Set.Ioo (0 : ℝ) 1 := by
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

/-- Existence form of the complete adapter. `Nonempty` keeps the case split
inside `Prop`; the data-valued definition below then chooses the certificate. -/
theorem coefficientWeakTestData_nonempty_of_weakIdentity
 {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {t : ℝ}
 (hweak : NegativePartWeakTestIdentityAt p u t)
 (hcont : ContinuousOn (negativePartTest u t) (Set.Icc (0 : ℝ) 1)) :
 Nonempty (NegativePartCoefficientWeakTestData p u t) := by
 classical
 by_cases hpositive :
 ∃ k : ℕ, k ≠ 0 ∧ cosineTestCoeff (negativePartTest u t) k ≠ 0
 · rcases hpositive with ⟨k, hk, hmode⟩
 exact ⟨coefficientWeakTestData_of_weakIdentity_of_nonzeroMode hweak hk hmode⟩
 · have hall : ∀ k : ℕ, k ≠ 0 →
 cosineTestCoeff (negativePartTest u t) k = 0 := by
 intro k hk
 exact not_ne_iff.mp (fun hne => hpositive ⟨k, hk, hne⟩)
 have hconst : Set.EqOn (negativePartTest u t)
 (fun _ => cosineTestCoeff (negativePartTest u t) 0)
 (Set.Icc (0 : ℝ) 1) :=
 eqOn_const_of_positive_cosineTestCoeff_eq_zero hcont hall
 have hderiv :
 ∀ᵐ x ∂ intervalMeasure 1, deriv (negativePartTest u t) x = 0 := by
 filter_upwards [ae_mem_Ioo_unitInterval] with x hx
 have hevent : Filter.EventuallyEq (nhds x)
 (negativePartTest u t)
 (fun _ => cosineTestCoeff (negativePartTest u t) 0) := by
 filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
 exact hconst ⟨hy.1.le, hy.2.le⟩
 rw [hevent.deriv_eq]
 simp
 have hgrad :
 (∫ x,
 deriv (intervalDomainLift (u t)) x * deriv (negativePartTest u t) x
 ∂ intervalMeasure 1) = 0 := by
 apply integral_eq_zero_of_ae
 filter_upwards [hderiv] with x hx
 simp [hx]
 by_cases hzeroMode : cosineTestCoeff (negativePartTest u t) 0 = 0
 · have htest_zero :
 ∀ᵐ x ∂ intervalMeasure 1, negativePartTest u t x = 0 := by
 filter_upwards [ae_mem_Ioo_unitInterval] with x hx
 rw [hconst ⟨hx.1.le, hx.2.le⟩, hzeroMode]
 have htime :
 (∫ x,
 intervalDomainLift
 (fun z : intervalDomainPoint => intervalDomain.timeDeriv u t z) x *
 negativePartTest u t x
 ∂ intervalMeasure 1) = 0 := by
 apply integral_eq_zero_of_ae
 filter_upwards [htest_zero] with x hx
 simp [hx]
 have hchem :
 (∫ x,
 truncatedChemFluxLifted p (u t) x * deriv (negativePartTest u t) x
 ∂ intervalMeasure 1) = 0 := by
 apply integral_eq_zero_of_ae
 filter_upwards [hderiv] with x hx
 simp [hx]
 have hlog :
 (∫ x, truncatedLogisticLifted p (u t) x * negativePartTest u t x
 ∂ intervalMeasure 1) = 0 := by
 apply integral_eq_zero_of_ae
 filter_upwards [htest_zero] with x hx
 simp [hx]
 exact ⟨coefficientWeakTestData_of_zeroPairings
 htime hgrad (by simp [hchem, hlog])⟩
 · exact ⟨coefficientWeakTestData_of_weakIdentity_of_zeroMode
 hweak hgrad hzeroMode⟩

/-- Complete algebraic adapter from the direct weak identity to the legacy
coefficient-shaped interface. Spatial continuity is used only in the
degenerate branch where cosine totality says the test is constant. -/
def coefficientWeakTestData_of_weakIdentity
 {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {t : ℝ}
 (hweak : NegativePartWeakTestIdentityAt p u t)
 (hcont : ContinuousOn (negativePartTest u t) (Set.Icc (0 : ℝ) 1)) :
 NegativePartCoefficientWeakTestData p u t :=
 Classical.choice
 (coefficientWeakTestData_nonempty_of_weakIdentity hweak hcont)

/-! ## DT-level direct weak-form wiring -/

private theorem positivePartSlice_continuous
 {w : intervalDomainPoint → ℝ} (hw : Continuous w) :
 Continuous (positivePartSlice w) := by
 simpa [positivePartSlice, positivePart] using hw.max continuous_const

private theorem truncatedLimit_test_continuousOn
 {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
 (DT : TruncatedConjugateMildExistenceData p u₀)
 {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T) :
 ContinuousOn
 (negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t)
 (Set.Icc (0 : ℝ) 1) := by
 let SD := truncatedConjugateMildSolutionData_of_data DT
 have hslice : Continuous
 (truncatedConjugatePicardLimit p u₀ DT.T t) := by
 simpa [SD] using SD.hcont t ht htT
 have hlift : ContinuousOn
 (intervalDomainLift (truncatedConjugatePicardLimit p u₀ DT.T t))
 (Set.Icc (0 : ℝ) 1) := by
 rw [continuousOn_iff_continuous_restrict]
 have heq : Set.restrict (Set.Icc (0 : ℝ) 1)
 (intervalDomainLift (truncatedConjugatePicardLimit p u₀ DT.T t)) =
 truncatedConjugatePicardLimit p u₀ DT.T t := by
 funext ⟨x, hx⟩
 simp only [Set.restrict_apply, intervalDomainLift, dif_pos hx]
 exact congrArg _ (Subtype.ext rfl)
 rw [heq]
 exact hslice
 exact (negativePart_continuous.continuousOn.comp hlift
 (fun _ _ => Set.mem_univ _)).neg

private def truncatedLimit_fluxTestDualityData
 {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
 (DT : TruncatedConjugateMildExistenceData p u₀)
 {t s : ℝ} (ht : 0 < t) (htT : t ≤ DT.T)
 (hs : 0 < s) (hst : s < t) :
 BNDualityForFluxTestAt p
 (truncatedConjugatePicardLimit p u₀ DT.T) t s
 (negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t) := by
 let U := truncatedConjugatePicardLimit p u₀ DT.T
 let SD := truncatedConjugateMildSolutionData_of_data DT
 have hsT : s ≤ DT.T := (le_of_lt hst).trans htT
 have hs_cont : Continuous (U s) := by
 simpa [U, SD] using SD.hcont s hs hsT
 have hs_bound : ∀ x : intervalDomainPoint, |U s x| ≤ DT.M := by
 intro x
 simpa [U, SD] using SD.hbound s hs hsT x
 have hpos_bound : ∀ x : intervalDomainPoint,
 |positivePartSlice (U s) x| ≤ DT.M := by
 intro x
 exact (abs_positivePart_le_abs (U s x)).trans (hs_bound x)
 have hflux_int : Integrable (truncatedChemFluxLifted p (U s))
 (intervalMeasure 1) := by
 rw [truncatedChemFluxLifted_eq_chemFluxLifted_positivePartSlice]
 exact
 ShenWork.IntervalDuhamelIntegrability.chemFluxLifted_integrable_of_continuous
 p hpos_bound DT.hM.le (positivePartSlice_continuous hs_cont)
 (positivePartSlice_nonneg (U s))
 let CQ : ℝ := DT.M *
 (Real.sqrt (∑' k : ℕ,
 (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
 (2 * (p.ν * DT.M ^ p.γ)))
 have hflux_bound : ∀ y : ℝ, |truncatedChemFluxLifted p (U s) y| ≤ CQ := by
 intro y
 rw [truncatedChemFluxLifted_eq_chemFluxLifted_positivePartSlice]
 exact
 ShenWork.IntervalConjugateChemFluxIntegrable.chemFluxLifted_sup_bound_of_ball
 p DT.hM.le hpos_bound (positivePartSlice_nonneg (U s))
 (positivePartSlice_continuous hs_cont) y
 have htest_cont := truncatedLimit_test_continuousOn DT ht htT
 have htest_meas : AEStronglyMeasurable (negativePartTest U t)
 (intervalMeasure 1) :=
 ShenWork.IntervalDuhamelIntegrability.continuousOn_aestronglyMeasurable_intervalMeasure
 (by simpa [U] using htest_cont)
 have ht_bound : ∀ x : intervalDomainPoint, |U t x| ≤ DT.M := by
 intro x
 simpa [U, SD] using SD.hbound t ht htT x
 have htest_bound : ∀ y : ℝ, |negativePartTest U t y| ≤ DT.M := by
 intro y
 have hlift : |intervalDomainLift (U t) y| ≤ DT.M := by
 by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
 · simpa [intervalDomainLift, hy] using ht_bound ⟨y, hy⟩
 · simp [intervalDomainLift, hy, DT.hM.le]
 exact (by
 simpa [negativePartTest, negativePartLift, abs_neg] using
 (negativePart_abs_le_abs (intervalDomainLift (U t) y)).trans hlift)
 exact
 { flux_bounded :=
 { measurable := hflux_int.aestronglyMeasurable
 boundConstant := CQ
 bound := hflux_bound }
 test_bounded :=
 { measurable := htest_meas
 boundConstant := DT.M
 bound := htest_bound } }

/-- The standard heat-Duhamel bundle, the already-proved restricted B_N
duality, and the mild fixed-point equation give the negative-part weak
identity at every active time. -/
theorem truncatedLimit_weakIdentity_of_standardFacts
 {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
 (DT : TruncatedConjugateMildExistenceData p u₀)
 (H : NegativePartStandardHeatSemigroupDuhamelFacts p DT.T u₀
 (truncatedConjugatePicardLimit p u₀ DT.T))
 {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T) :
 NegativePartWeakTestIdentityAt p
 (truncatedConjugatePicardLimit p u₀ DT.T) t := by
 apply
 negativePartMildSemigroupWeakAfterFluxTestDuality_of_standardHeatSemigroupDuhamelFacts
 H (truncatedConjugateMildSolutionData_of_data DT).hmild t ht htT
 intro s hs hst
 exact (truncatedLimit_fluxTestDualityData DT ht htT hs hst).duality hst

/-- Exact DT-indexed legacy weak record obtained from the direct semigroup
weak form. Its coefficient certificates are finite-support encodings of the
weak identity and do not use the spectral bootstrap. -/
def truncatedNegativePartMildToWeakRegularData_of_standardFacts
 {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
 (DT : TruncatedConjugateMildExistenceData p u₀)
 (H : NegativePartStandardHeatSemigroupDuhamelFacts p DT.T u₀
 (truncatedConjugatePicardLimit p u₀ DT.T)) :
 TruncatedNegativePartMildToWeakRegularData p DT where
 coeff_weak := by
 intro t ht htT
 exact coefficientWeakTestData_of_weakIdentity
 (truncatedLimit_weakIdentity_of_standardFacts DT H ht htT)
 (truncatedLimit_test_continuousOn DT ht htT)

/-! ## Integrable weak-Duhamel dominators -/

private theorem semigroupGradient_pairing_abs_le
 {τ Cf Cg : ℝ} (hτ : 0 < τ) (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
 {f g : ℝ → ℝ}
 (hf_meas : AEStronglyMeasurable f (intervalMeasure 1))
 (hf_bound : ∀ y, |f y| ≤ Cf)
 (hg_bound : ∀ᵐ x ∂ intervalMeasure 1, |g x| ≤ Cg) :
 |∫ x,
 deriv (fun z : ℝ =>
 ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator τ f z) x *
 g x
 ∂ intervalMeasure 1| ≤
 (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
 Cf * Cg * (intervalMeasure 1).real Set.univ) *
 τ ^ (-(1 / 2) : ℝ) := by
 let Cgrad :=
 ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
 have hCgrad : 0 ≤ Cgrad :=
 ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
 have hpoint : ∀ᵐ x ∂ intervalMeasure 1,
 |deriv (fun z : ℝ =>
 ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator τ f z) x *
 g x| ≤ Cgrad * τ ^ (-(1 / 2) : ℝ) * Cf * Cg := by
 filter_upwards [hg_bound] with x hx
 rw [abs_mul]
 have hsem :=
 ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_deriv_Linfty_pointwise_sqrt_t
 hτ hf_meas hf_bound x
 exact mul_le_mul hsem hx (abs_nonneg _)
 (mul_nonneg
 (mul_nonneg hCgrad (Real.rpow_nonneg hτ.le _)) hCf)
 haveI : IsFiniteMeasure (intervalMeasure 1) :=
 ⟨ShenWork.IntervalDomain.intervalMeasure_univ_lt_top 1⟩
 have hpoint_norm : ∀ᵐ x ∂ intervalMeasure 1,
 ‖deriv (fun z : ℝ =>
 ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator τ f z) x *
 g x‖ ≤ Cgrad * τ ^ (-(1 / 2) : ℝ) * Cf * Cg := by
 filter_upwards [hpoint] with x hx
 simpa [Real.norm_eq_abs] using hx
 have hint := norm_integral_le_of_norm_le_const hpoint_norm
 rw [Real.norm_eq_abs] at hint
 calc
 |∫ x,
 deriv (fun z : ℝ =>
 ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator τ f z) x *
 g x
 ∂ intervalMeasure 1|
 ≤ (Cgrad * τ ^ (-(1 / 2) : ℝ) * Cf * Cg) *
 (intervalMeasure 1).real Set.univ := hint
 _ = (Cgrad * Cf * Cg * (intervalMeasure 1).real Set.univ) *
 τ ^ (-(1 / 2) : ℝ) := by ring

private theorem integrableOn_Icc_sub_rpow_neg_half_const
 (t K : ℝ) (ht : 0 ≤ t) :
 IntegrableOn (fun s : ℝ => K * (t - s) ^ (-(1 / 2) : ℝ))
 (Set.Icc (0 : ℝ) t) volume := by
 have h :=
 (ShenWork.IntervalGradDuhamelBound.intervalIntegrable_sub_rpow_neg_half t).const_mul K
 rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht] at h
 simpa [IntegrableOn, MeasureTheory.restrict_Ioc_eq_restrict_Icc] using h

/-- The ordinary-source Duhamel weak-gradient integrand has the standard
`(t-s)^(-1/2)` majorant. -/
theorem heatDuhamelDCTDominatingFunction_of_bounds
 {F : ℝ → ℝ → ℝ} {φ : ℝ → ℝ} {t CF Cφ : ℝ}
 (ht : 0 ≤ t) (hCF : 0 ≤ CF) (hCφ : 0 ≤ Cφ)
 (hF_meas : ∀ s, AEStronglyMeasurable (F s) (intervalMeasure 1))
 (hF_bound : ∀ s, 0 < s → s < t → ∀ y, |F s y| ≤ CF)
 (hφderiv : ∀ᵐ x ∂ intervalMeasure 1, |deriv φ x| ≤ Cφ) :
 HeatDuhamelDCTDominatingFunction F φ t := by
 let K : ℝ :=
 ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
 CF * Cφ * (intervalMeasure 1).real Set.univ
 refine ⟨fun s => K * (t - s) ^ (-(1 / 2) : ℝ),
 integrableOn_Icc_sub_rpow_neg_half_const t K ht, ?_⟩
 intro s hs hst
 exact semigroupGradient_pairing_abs_le (sub_pos.mpr hst) hCF hCφ
 (hF_meas s) (hF_bound s hs hst) hφderiv

/-- The divergence-source weak integrand has the same integrable majorant,
with the semigroup gradient falling on the fixed test. -/
theorem chemotaxisDuhamelDCTDominatingFunction_of_bounds
 {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
 {φ : ℝ → ℝ} {t CQ Cφ : ℝ}
 (ht : 0 ≤ t) (hCQ : 0 ≤ CQ) (hCφ : 0 ≤ Cφ)
 (hQ_meas : ∀ s, AEStronglyMeasurable
 (truncatedChemFluxLifted p (u s)) (intervalMeasure 1))
 (hQ_bound : ∀ s, 0 < s → s < t → ∀ y,
 |truncatedChemFluxLifted p (u s) y| ≤ CQ)
 (hφ_meas : AEStronglyMeasurable φ (intervalMeasure 1))
 (hφ_bound : ∀ y, |φ y| ≤ Cφ) :
 ChemotaxisDuhamelDCTDominatingFunction p u φ t := by
 let K : ℝ :=
 ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
 Cφ * CQ * (intervalMeasure 1).real Set.univ
 refine ⟨fun s => K * (t - s) ^ (-(1 / 2) : ℝ),
 integrableOn_Icc_sub_rpow_neg_half_const t K ht, ?_⟩
 intro s hs hst
 have hpair := semigroupGradient_pairing_abs_le
 (sub_pos.mpr hst) hCφ hCQ hφ_meas hφ_bound
 (Eventually.of_forall (hQ_bound s hs hst))
 have hintegral :
 (∫ y, truncatedChemFluxLifted p (u s) y *
 deriv (fun z =>
 ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
 (t - s) φ z) y ∂ intervalMeasure 1) =
 ∫ y, deriv (fun z =>
 ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
 (t - s) φ z) y *
 truncatedChemFluxLifted p (u s) y ∂ intervalMeasure 1 := by
 apply integral_congr_ae
 filter_upwards [] with y
 ring
 rw [hintegral]
 dsimp [K]
 exact hpair

private theorem negativePart_lipschitz_abs (r q : ℝ) :
 |negativePart r - negativePart q| ≤ |r - q| := by
 calc
 |negativePart r - negativePart q|
 = |positivePart (-r) - positivePart (-q)| := by
 rfl
 _ ≤ |-r - (-q)| := positivePart_lipschitz_abs (-r) (-q)
 _ = |r - q| := by
 rw [show -r - (-q) = -(r - q) by ring, abs_neg]

private theorem negativePartTest_deriv_ae_bound_of_lipschitz
 {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
 (DT : TruncatedConjugateMildExistenceData p u₀)
 {t G : ℝ} (hG : 0 ≤ G)
 (hlip : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
 |intervalDomainLift
 ((truncatedConjugatePicardLimit p u₀ DT.T) t) x -
 intervalDomainLift
 ((truncatedConjugatePicardLimit p u₀ DT.T) t) y| ≤ G * |x - y|) :
 ∀ᵐ x ∂ intervalMeasure 1,
 |deriv (negativePartTest
 (truncatedConjugatePicardLimit p u₀ DT.T) t) x| ≤ G := by
 let U := truncatedConjugatePicardLimit p u₀ DT.T
 let φ := negativePartTest U t
 have hφlip : LipschitzOnWith ⟨G, hG⟩ φ (Set.Icc (0 : ℝ) 1) := by
 apply LipschitzOnWith.of_dist_le_mul
 intro x hx y hy
 rw [Real.dist_eq, Real.dist_eq]
 change |(-negativePart (intervalDomainLift (U t) x)) -
 (-negativePart (intervalDomainLift (U t) y))| ≤ G * |x - y|
 calc
 |(-negativePart (intervalDomainLift (U t) x)) -
 (-negativePart (intervalDomainLift (U t) y))|
 = |negativePart (intervalDomainLift (U t) x) -
 negativePart (intervalDomainLift (U t) y)| := by
 rw [show
 (-negativePart (intervalDomainLift (U t) x)) -
 (-negativePart (intervalDomainLift (U t) y)) =
 -(negativePart (intervalDomainLift (U t) x) -
 negativePart (intervalDomainLift (U t) y)) by ring,
 abs_neg]
 _ ≤ |intervalDomainLift (U t) x - intervalDomainLift (U t) y| :=
 negativePart_lipschitz_abs _ _
 _ ≤ G * |x - y| := by simpa [U] using hlip x hx y hy
 filter_upwards [ae_mem_Ioo_unitInterval] with x hx
 have hnhds : Set.Icc (0 : ℝ) 1 ∈ nhds x :=
 mem_of_superset (isOpen_Ioo.mem_nhds hx) Set.Ioo_subset_Icc_self
 have hder := norm_deriv_le_of_lipschitzOn hnhds hφlip
 simpa [φ, Real.norm_eq_abs] using hder

private theorem truncatedLimit_negativePartTest_deriv_ae_bound
 {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
 (DT : TruncatedConjugateMildExistenceData p u₀)
 {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T) :
 ∃ G : ℝ, 0 ≤ G ∧
 ∀ᵐ x ∂ intervalMeasure 1,
 |deriv (negativePartTest
 (truncatedConjugatePicardLimit p u₀ DT.T) t) x| ≤ G := by
 obtain ⟨G, hG, hlip⟩ :=
 ShenWork.Paper2.TruncatedPositiveTimeBootstrap.truncatedPicardLimit_lipschitzOn_positive_time
 DT ht htT
 exact ⟨G, hG,
 negativePartTest_deriv_ae_bound_of_lipschitz DT hG hlip⟩

/-- Whole-line version of the same derivative envelope. The test is locally
zero off `[0,1]`; the two endpoints are null for Lebesgue measure. -/
private theorem truncatedLimit_negativePartTest_deriv_ae_bound_volume
 {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
 (DT : TruncatedConjugateMildExistenceData p u₀)
 {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T) :
 ∃ G : ℝ, 0 ≤ G ∧
 ∀ᵐ x ∂volume,
 |deriv (negativePartTest
 (truncatedConjugatePicardLimit p u₀ DT.T) t) x| ≤ G := by
 let U := truncatedConjugatePicardLimit p u₀ DT.T
 let φ := negativePartTest U t
 obtain ⟨G, hG, hlip⟩ :=
 ShenWork.Paper2.TruncatedPositiveTimeBootstrap.truncatedPicardLimit_lipschitzOn_positive_time
 DT ht htT
 have hφlip : LipschitzOnWith ⟨G, hG⟩ φ (Set.Icc (0 : ℝ) 1) := by
 apply LipschitzOnWith.of_dist_le_mul
 intro x hx y hy
 rw [Real.dist_eq, Real.dist_eq]
 change |(-negativePart (intervalDomainLift (U t) x)) -
 (-negativePart (intervalDomainLift (U t) y))| ≤ G * |x - y|
 calc
 |(-negativePart (intervalDomainLift (U t) x)) -
 (-negativePart (intervalDomainLift (U t) y))| =
 |negativePart (intervalDomainLift (U t) x) -
 negativePart (intervalDomainLift (U t) y)| := by
 rw [show (-negativePart (intervalDomainLift (U t) x)) -
 (-negativePart (intervalDomainLift (U t) y)) =
 -(negativePart (intervalDomainLift (U t) x) -
 negativePart (intervalDomainLift (U t) y)) by ring, abs_neg]
 _ ≤ |intervalDomainLift (U t) x - intervalDomainLift (U t) y| :=
 negativePart_lipschitz_abs _ _
 _ ≤ G * |x - y| := by simpa [U] using hlip x hx y hy
 have hne0 : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
 simp [ae_iff, measure_singleton]
 have hne1 : ∀ᵐ x : ℝ ∂volume, x ≠ 1 := by
 simp [ae_iff, measure_singleton]
 refine ⟨G, hG, ?_⟩
 filter_upwards [hne0, hne1] with x hx0 hx1
 by_cases hx : x ∈ Set.Ioo (0 : ℝ) 1
 · have hnhds : Set.Icc (0 : ℝ) 1 ∈ nhds x :=
 mem_of_superset (isOpen_Ioo.mem_nhds hx) Set.Ioo_subset_Icc_self
 have hder := norm_deriv_le_of_lipschitzOn hnhds hφlip
 simpa [φ, Real.norm_eq_abs] using hder
 · have hout : x < 0 ∨ 1 < x := by
 rw [Set.mem_Ioo, not_and_or] at hx
 rcases hx with hx | hx
 · exact Or.inl (lt_of_le_of_ne (le_of_not_gt hx) hx0)
 · exact Or.inr (lt_of_le_of_ne (le_of_not_gt hx) (Ne.symm hx1))
 have hev : φ =ᶠ[nhds x] fun _ : ℝ => 0 := by
 rcases hout with hxlt | hxgt
 · filter_upwards [Iio_mem_nhds hxlt] with y hy
 have hyI : y ∉ Set.Icc (0 : ℝ) 1 := fun h => (not_lt_of_ge h.1) hy
 simp [φ, U, negativePartTest, negativePartLift, intervalDomainLift,
 hyI, negativePart]
 · filter_upwards [Ioi_mem_nhds hxgt] with y hy
 have hyI : y ∉ Set.Icc (0 : ℝ) 1 := fun h => (not_lt_of_ge h.2) hy
 simp [φ, U, negativePartTest, negativePartLift, intervalDomainLift,
 hyI, negativePart]
 rw [hev.deriv_eq]
 simp [hG]

/-- The fixed final negative-part test is absolutely continuous on the spatial
interval. -/
private theorem truncatedLimit_negativePartTest_absolutelyContinuous
 {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
 (DT : TruncatedConjugateMildExistenceData p u₀)
 {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T) :
 AbsolutelyContinuousOnInterval
 (negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t) 0 1 := by
 let U := truncatedConjugatePicardLimit p u₀ DT.T
 let φ := negativePartTest U t
 obtain ⟨G, hG, hlip⟩ :=
 ShenWork.Paper2.TruncatedPositiveTimeBootstrap.truncatedPicardLimit_lipschitzOn_positive_time
 DT ht htT
 have hφlip : LipschitzOnWith ⟨G, hG⟩ φ (Set.Icc (0 : ℝ) 1) := by
 apply LipschitzOnWith.of_dist_le_mul
 intro x hx y hy
 rw [Real.dist_eq, Real.dist_eq]
 change |(-negativePart (intervalDomainLift (U t) x)) -
 (-negativePart (intervalDomainLift (U t) y))| ≤ G * |x - y|
 calc
 |(-negativePart (intervalDomainLift (U t) x)) -
 (-negativePart (intervalDomainLift (U t) y))| =
 |negativePart (intervalDomainLift (U t) x) -
 negativePart (intervalDomainLift (U t) y)| := by
 rw [show (-negativePart (intervalDomainLift (U t) x)) -
 (-negativePart (intervalDomainLift (U t) y)) =
 -(negativePart (intervalDomainLift (U t) x) -
 negativePart (intervalDomainLift (U t) y)) by ring, abs_neg]
 _ ≤ |intervalDomainLift (U t) x - intervalDomainLift (U t) y| :=
 negativePart_lipschitz_abs _ _
 _ ≤ G * |x - y| := by simpa [U] using hlip x hx y hy
 have hφlip_u : LipschitzOnWith ⟨G, hG⟩ φ (Set.uIcc (0 : ℝ) 1) := by
 simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hφlip
 exact hφlip_u.absolutelyContinuousOnInterval

private def truncatedLogisticBound (p : CM2Params) (M : ℝ) : ℝ :=
 M * (p.a + p.b * M ^ p.α)

private theorem truncatedLogisticBound_nonneg
 (p : CM2Params) {M : ℝ} (hM : 0 ≤ M) :
 0 ≤ truncatedLogisticBound p M := by
 exact mul_nonneg hM
 (add_nonneg p.ha (mul_nonneg p.hb (Real.rpow_nonneg hM _)))

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

/-- Concrete discharge of both DCT-majorant fields for the truncated limit. -/
theorem truncatedLimit_dctDominators
 {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
 (DT : TruncatedConjugateMildExistenceData p u₀)
 {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T) :
 HeatDuhamelDCTDominatingFunction
 (fun s => truncatedLogisticLifted p
 ((truncatedConjugatePicardLimit p u₀ DT.T) s))
 (negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t) t ∧
 ChemotaxisDuhamelDCTDominatingFunction p
 (truncatedConjugatePicardLimit p u₀ DT.T)
 (negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t) t := by
 let U := truncatedConjugatePicardLimit p u₀ DT.T
 let SD := truncatedConjugateMildSolutionData_of_data DT
 let CL := truncatedLogisticBound p DT.M
 let CQ : ℝ := DT.M *
 (Real.sqrt (∑' k : ℕ,
 (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
 (2 * (p.ν * DT.M ^ p.γ)))
 have hCL : 0 ≤ CL := truncatedLogisticBound_nonneg p DT.hM.le
 have hCQ : 0 ≤ CQ := by
 dsimp [CQ]
 exact mul_nonneg DT.hM.le
 (mul_nonneg (Real.sqrt_nonneg _)
 (mul_nonneg (by norm_num)
 (mul_nonneg p.hν.le (Real.rpow_nonneg DT.hM.le _))))
 have hbound : ∀ s, 0 < s → s < t →
 ∀ x : intervalDomainPoint, |U s x| ≤ DT.M := by
 intro s hs hst x
 simpa [U, SD] using SD.hbound s hs ((le_of_lt hst).trans htT) x
 have hlog_bound : ∀ s, 0 < s → s < t → ∀ y,
 |truncatedLogisticLifted p (U s) y| ≤ CL := by
 intro s hs hst y
 simpa [CL] using
 truncatedLogisticLifted_abs_le p DT.hM.le (hbound s hs hst) y
 have hflux_bound : ∀ s, 0 < s → s < t → ∀ y,
 |truncatedChemFluxLifted p (U s) y| ≤ CQ := by
 intro s hs hst y
 rw [truncatedChemFluxLifted_eq_chemFluxLifted_positivePartSlice]
 exact
 ShenWork.IntervalConjugateChemFluxIntegrable.chemFluxLifted_sup_bound_of_ball
 p DT.hM.le
 (fun x => (abs_positivePart_le_abs (U s x)).trans
 (hbound s hs hst x))
 (positivePartSlice_nonneg (U s))
 (positivePartSlice_continuous
 (by simpa [U, SD] using SD.hcont s hs ((le_of_lt hst).trans htT))) y
 have htest_bound : ∀ y, |negativePartTest U t y| ≤ DT.M := by
 intro y
 have hlift : |intervalDomainLift (U t) y| ≤ DT.M := by
 by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
 · simpa [intervalDomainLift, hy, U, SD] using SD.hbound t ht htT ⟨y, hy⟩
 · simp [intervalDomainLift, hy, DT.hM.le]
 simpa [negativePartTest, negativePartLift, abs_neg] using
 (negativePart_abs_le_abs (intervalDomainLift (U t) y)).trans hlift
 have htest_meas : AEStronglyMeasurable (negativePartTest U t)
 (intervalMeasure 1) :=
 ShenWork.IntervalDuhamelIntegrability.continuousOn_aestronglyMeasurable_intervalMeasure
 (by simpa [U] using truncatedLimit_test_continuousOn DT ht htT)
 obtain ⟨G, hG, htest_deriv⟩ :=
 truncatedLimit_negativePartTest_deriv_ae_bound DT ht htT
 constructor
 · exact heatDuhamelDCTDominatingFunction_of_bounds ht.le hCL hG
 (fun s => truncatedLimit_logistic_aestronglyMeasurable DT s)
 (by simpa [U] using hlog_bound) (by simpa [U] using htest_deriv)
 · exact chemotaxisDuhamelDCTDominatingFunction_of_bounds ht.le hCQ DT.hM.le
 (fun s => (truncatedLimit_flux_integrable DT s).aestronglyMeasurable)
 (by simpa [U] using hflux_bound) htest_meas htest_bound

/-- Every fixed spatial point of the faithful conjugate mild trajectory is
continuous on positive times, including one-sided continuity at the terminal
time. The only initial-datum inputs are the same boundedness and measurability
assumptions used by the faithful positive-time spatial regularity chain. -/
theorem truncatedLimit_timeSlice_continuousOn_Ioc
 {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
 (DT : TruncatedConjugateMildExistenceData p u₀)
 (x : intervalDomainPoint) :
 ContinuousOn
 (fun t : ℝ => truncatedConjugatePicardLimit p u₀ DT.T t x)
 (Set.Ioc (0 : ℝ) DT.T) := by
 let D := truncatedConjugateMildSolutionData_of_data DT
 -- Globally cut off the two source families. On every mild integration
 -- window `(0,t]`, `t ≤ D.T`, they agree with the faithful sources.
 let Q : ℝ → ℝ → ℝ := fun s y =>
 if 0 < s ∧ s ≤ D.T then truncatedChemFluxLifted p (D.u s) y else 0
 let L : ℝ → ℝ → ℝ := fun s y =>
 if 0 < s ∧ s ≤ D.T then truncatedLogisticLifted p (D.u s) y else 0
 let CQ : ℝ := D.M *
 (Real.sqrt (∑' k : ℕ,
 (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
 (2 * (p.ν * D.M ^ p.γ)))
 let CL : ℝ := D.M * (p.a + p.b * D.M ^ p.α)
 have hCQ : 0 ≤ CQ := by
 dsimp [CQ]
 exact mul_nonneg D.hM.le
 (mul_nonneg (Real.sqrt_nonneg _)
 (mul_nonneg (by norm_num)
 (mul_nonneg p.hν.le (Real.rpow_nonneg D.hM.le _))))
 have hCL : 0 ≤ CL := by
 dsimp [CL]
 exact mul_nonneg D.hM.le
 (add_nonneg p.ha (mul_nonneg p.hb (Real.rpow_nonneg D.hM.le _)))
 have hQ_meas : Measurable (Function.uncurry Q) := by
 have hbase :=
 _root_.ShenWork.Paper2.TruncatedPositiveTimeBootstrap.truncatedChemFluxLifted_joint_measurable_of_lift_joint
 (p := p) (w := D.u) D.hmeas
 simp only [Q]
 refine Measurable.ite ?_ hbase measurable_const
 exact ((isOpen_Ioi.preimage continuous_fst).measurableSet).inter
 ((isClosed_Iic.preimage continuous_fst).measurableSet)
 have hL_meas : Measurable (Function.uncurry L) := by
 have hbase :=
 _root_.ShenWork.Paper2.TruncatedPositiveTimeBootstrap.truncatedLogisticLifted_joint_measurable_of_lift_joint
 (p := p) (w := D.u) D.hmeas
 simp only [L]
 refine Measurable.ite ?_ hbase measurable_const
 exact ((isOpen_Ioi.preimage continuous_fst).measurableSet).inter
 ((isClosed_Iic.preimage continuous_fst).measurableSet)
 have hQ_bound : ∀ s y, |Q s y| ≤ CQ := by
 intro s y
 simp only [Q]
 split_ifs with hs
 · dsimp [CQ]
 exact
 _root_.ShenWork.Paper2.TruncatedPositiveTimeBootstrap.truncatedChemFluxLifted_abs_le_of_abs_ball
 p D.hM (D.hcont s hs.1 hs.2) (D.hbound s hs.1 hs.2) y
 · simpa using hCQ
 have hL_bound : ∀ s y, |L s y| ≤ CL := by
 intro s y
 simp only [L]
 split_ifs with hs
 · dsimp [CL]
 exact truncatedLogisticLifted_abs_le p D.hM.le
 (D.hbound s hs.1 hs.2) y
 · simpa using hCL
 have hQ_int : ∀ s, Integrable (Q s) (intervalMeasure 1) := by
 intro s
 simp only [Q]
 split_ifs with hs
 · simpa [D] using truncatedLimit_flux_integrable DT s
 · simp
 have hL_int : ∀ s, Integrable (L s) (intervalMeasure 1) := by
 intro s
 exact Integrable.of_bound
 (hL_meas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
 CL (Filter.Eventually.of_forall (hL_bound s))
 have hu₀_int : Integrable (intervalDomainLift u₀) (intervalMeasure 1) :=
 ShenWork.IntervalDomain.intervalMeasure_integrable_of_abs_bound
 DT.hbase_lift_meas DT.hbase_lift_bound

 intro t0 ht0
 rw [Metric.continuousWithinAt_iff]
 intro eps heps
 set Cg : ℝ :=
 ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
 let tailBound : ℝ → ℝ := fun r =>
 |p.χ₀| * (Cg * (2 * Real.sqrt r) * CQ) + r * CL
 have htail_cont : ContinuousAt tailBound 0 := by
 dsimp [tailBound]
 fun_prop
 have htail_zero : tailBound 0 = 0 := by
 simp [tailBound]
 have heps3 : 0 < eps / 3 := by positivity
 obtain ⟨dtail, hdtail, htail_close⟩ :=
 (Metric.continuousAt_iff.mp htail_cont) (eps / 3) heps3
 let rho : ℝ := min (t0 / 4) (dtail / 4)
 have hrho : 0 < rho := by
 exact lt_min (by linarith [ht0.1]) (by linarith)
 have hrho_t : rho ≤ t0 / 4 := min_le_left _ _
 have hrho_d : rho ≤ dtail / 4 := min_le_right _ _
 let c : ℝ := t0 - rho
 let lo : ℝ := t0 - rho / 2
 let hi : ℝ := t0 + rho / 2
 have hc0 : 0 ≤ c := by dsimp [c]; linarith
 have hclo : c < lo := by dsimp [c, lo]; linarith
 have hlohi : lo ≤ hi := by dsimp [lo, hi]; linarith
 have hlo0 : 0 < lo := by dsimp [lo]; linarith
 have ht0mem : t0 ∈ Set.Icc lo hi := by
 constructor <;> dsimp [lo, hi] <;> linarith
 have hbox_nhds : Set.Icc lo hi ∈ nhds t0 :=
 Icc_mem_nhds (by dsimp [lo]; linarith) (by dsimp [hi]; linarith)

 let Hom : ℝ → ℝ := fun t =>
 intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
 let BEarly : ℝ → ℝ := fun t =>
 ∫ s in (0 : ℝ)..c,
 intervalConjugateKernelOperator (t - s) (Q s) x.1
 let LEarly : ℝ → ℝ := fun t =>
 ∫ s in (0 : ℝ)..c,
 intervalFullSemigroupOperator (t - s) (L s) x.1
 let Core : ℝ → ℝ := fun t =>
 Hom t + (-p.χ₀) * BEarly t + LEarly t

 have hHom_on : ContinuousOn Hom (Set.Icc lo hi) := by
 have hjoint := fullSemigroup_fixedSource_jointContinuousOn
 hlo0 hlohi hu₀_int DT.hbase_lift_bound
 have hpair : ContinuousOn (fun t : ℝ => ((t, x.1) : ℝ × ℝ))
 (Set.Icc lo hi) := continuousOn_id.prodMk continuousOn_const
 exact hjoint.comp hpair (fun t ht => ⟨ht, x.2⟩)
 have hBEarly_on : ContinuousOn BEarly (Set.Icc lo hi) := by
 exact conjugateEarly_continuousOn hc0 hclo hlohi hCQ
 hQ_meas hQ_int hQ_bound x
 have hLEarly_on : ContinuousOn LEarly (Set.Icc lo hi) := by
 exact valueEarly_continuousOn hc0 hclo hlohi hCL
 hL_meas hL_int hL_bound x
 have hCore_on : ContinuousOn Core (Set.Icc lo hi) := by
 exact (hHom_on.add (continuousOn_const.mul hBEarly_on)).add hLEarly_on
 have hCore_at : ContinuousAt Core t0 := hCore_on.continuousAt hbox_nhds
 obtain ⟨dcore, hdcore, hcore_close⟩ :=
 (Metric.continuousAt_iff.mp hCore_at) (eps / 3) heps3
 refine ⟨min dcore (rho / 2), lt_min hdcore (by linarith), ?_⟩
 intro t ht htdist
 have htcore : dist t t0 < dcore :=
 lt_of_lt_of_le htdist (min_le_left _ _)
 have htnear : dist t t0 < rho / 2 :=
 lt_of_lt_of_le htdist (min_le_right _ _)
 have htnear_abs : |t - t0| < rho / 2 := by
 simpa [Real.dist_eq] using htnear
 have hct : c < t := by
 have hlow := (abs_lt.mp htnear_abs).1
 dsimp [c]
 linarith
 have htlocal : t ∈ Set.Icc lo hi := by
 dsimp [lo, hi]
 constructor <;> linarith [abs_lt.mp htnear_abs]
 have hgap0 : 0 ≤ t - c := sub_nonneg.mpr hct.le
 have hgap_lt : t - c < dtail := by
 dsimp [c]
 have : t - t0 < rho / 2 := (abs_lt.mp htnear_abs).2
 have h2rho : 2 * rho ≤ dtail / 2 := by linarith [hrho_d]
 linarith
 have hrho_lt : rho < dtail := by linarith [hrho_d, hdtail]
 have htail_nonneg : ∀ {r : ℝ}, 0 ≤ r → 0 ≤ tailBound r := by
 intro r hr
 dsimp [tailBound]
 have hCg0 : 0 ≤ Cg :=
 ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
 positivity
 have htail_t : tailBound (t - c) < eps / 3 := by
 have hd : dist (t - c) 0 < dtail := by
 rw [Real.dist_eq, sub_zero, abs_of_nonneg hgap0]
 exact hgap_lt
 have h := htail_close hd
 rw [htail_zero, Real.dist_eq, sub_zero,
 abs_of_nonneg (htail_nonneg hgap0)] at h
 exact h
 have htail_t0 : tailBound rho < eps / 3 := by
 have hd : dist rho 0 < dtail := by
 rw [Real.dist_eq, sub_zero, abs_of_pos hrho]
 exact hrho_lt
 have h := htail_close hd
 rw [htail_zero, Real.dist_eq, sub_zero,
 abs_of_nonneg (htail_nonneg hrho.le)] at h
 exact h

 let BTail : ℝ → ℝ := fun r =>
 ∫ s in c..r,
 intervalConjugateKernelOperator (r - s) (Q s) x.1
 let LTail : ℝ → ℝ := fun r =>
 ∫ s in c..r,
 intervalFullSemigroupOperator (r - s) (L s) x.1

 have hmild_cutoff : ∀ r, 0 < r → r ≤ D.T →
 D.u r x = Hom r + (-p.χ₀) *
 (∫ s in (0 : ℝ)..r,
 intervalConjugateKernelOperator (r - s) (Q s) x.1) +
 (∫ s in (0 : ℝ)..r,
 intervalFullSemigroupOperator (r - s) (L s) x.1) := by
 intro r hr hrT
 have hm := D.hmild r hr hrT x
 rw [hm]
 unfold truncatedConjugateDuhamelMap
 dsimp [Hom]
 have hBeq :
 (∫ s in (0 : ℝ)..r,
 intervalConjugateKernelOperator (r - s)
 (truncatedChemFluxLifted p (D.u s)) x.1) =
 (∫ s in (0 : ℝ)..r,
 intervalConjugateKernelOperator (r - s) (Q s) x.1) := by
 apply intervalIntegral.integral_congr_ae
 apply Eventually.of_forall
 intro s hs
 rw [Set.uIoc_of_le hr.le] at hs
 have hsT : s ≤ D.T := hs.2.trans hrT
 simp [Q, hs.1, hsT]
 have hLeq :
 (∫ s in (0 : ℝ)..r,
 intervalFullSemigroupOperator (r - s)
 (truncatedLogisticLifted p (D.u s)) x.1) =
 (∫ s in (0 : ℝ)..r,
 intervalFullSemigroupOperator (r - s) (L s) x.1) := by
 apply intervalIntegral.integral_congr_ae
 apply Eventually.of_forall
 intro s hs
 rw [Set.uIoc_of_le hr.le] at hs
 have hsT : s ≤ D.T := hs.2.trans hrT
 simp [L, hs.1, hsT]
 rw [hBeq, hLeq]
 have hsplit : ∀ r, 0 < r → r ≤ D.T → c < r →
 D.u r x = Core r + (-p.χ₀) * BTail r + LTail r := by
 intro r hr hrT hcr
 rw [hmild_cutoff r hr hrT]
 have hBfull :=
 conjugateDuhamel_intervalIntegrable_of_measurable_bound
 hr hCQ hQ_meas hQ_int hQ_bound (x := x.1)
 have hLfull :=
 _root_.ShenWork.IntervalDuhamelIntegrability.valueDuhamel_intervalIntegrable_of_joint_measurable
 hr hL_meas hCL hL_bound x.1
 have hc_mem : c ∈ Set.uIcc (0 : ℝ) r := by
 rw [Set.uIcc_of_le hr.le]
 exact ⟨hc0, hcr.le⟩
 have hB0c := hBfull.mono_set
 (Set.uIcc_subset_uIcc_left hc_mem)
 have hBcR := hBfull.mono_set
 (Set.uIcc_subset_uIcc_right hc_mem)
 have hL0c := hLfull.mono_set
 (Set.uIcc_subset_uIcc_left hc_mem)
 have hLcR := hLfull.mono_set
 (Set.uIcc_subset_uIcc_right hc_mem)
 have hBsplit :=
 intervalIntegral.integral_add_adjacent_intervals hB0c hBcR
 have hLsplit :=
 intervalIntegral.integral_add_adjacent_intervals hL0c hLcR
 rw [← hBsplit, ← hLsplit]
 dsimp [Core, BEarly, LEarly, BTail, LTail]
 ring
 have hsplit_t := hsplit t ht.1 ht.2 hct
 have hct0 : c < t0 := by dsimp [c]; linarith
 have hsplit_t0 := hsplit t0 ht0.1 ht0.2 hct0
 have hBtail_t : |BTail t| ≤ Cg * (2 * Real.sqrt (t - c)) * CQ := by
 simpa [BTail, Cg] using
 (conjugateTail_abs_le hct hCQ hQ_meas hQ_int hQ_bound x.1)
 have hLtail_t := valueTail_abs_le hct hCL hL_bound x.1
 have hBtail_t0 : |BTail t0| ≤ Cg * (2 * Real.sqrt (t0 - c)) * CQ := by
 simpa [BTail, Cg] using
 (conjugateTail_abs_le hct0 hCQ hQ_meas hQ_int hQ_bound x.1)
 have hLtail_t0 := valueTail_abs_le hct0 hCL hL_bound x.1
 have htail_pair_t : |(-p.χ₀) * BTail t + LTail t| < eps / 3 := by
 calc
 |(-p.χ₀) * BTail t + LTail t|
 ≤ |p.χ₀| * |BTail t| + |LTail t| := by
 calc
 |(-p.χ₀) * BTail t + LTail t|
 ≤ |(-p.χ₀) * BTail t| + |LTail t| := abs_add_le _ _
 _ = |p.χ₀| * |BTail t| + |LTail t| := by
 rw [abs_mul, abs_neg]
 _ ≤ |p.χ₀| *
 (Cg * (2 * Real.sqrt (t - c)) * CQ) + (t - c) * CL := by
 exact add_le_add
 (mul_le_mul_of_nonneg_left hBtail_t (abs_nonneg _)) hLtail_t
 _ = tailBound (t - c) := by rfl
 _ < eps / 3 := htail_t
 have htail_pair_t0 : |(-p.χ₀) * BTail t0 + LTail t0| < eps / 3 := by
 have ht0c : t0 - c = rho := by dsimp [c]; ring
 calc
 |(-p.χ₀) * BTail t0 + LTail t0|
 ≤ |p.χ₀| * |BTail t0| + |LTail t0| := by
 calc
 |(-p.χ₀) * BTail t0 + LTail t0|
 ≤ |(-p.χ₀) * BTail t0| + |LTail t0| := abs_add_le _ _
 _ = |p.χ₀| * |BTail t0| + |LTail t0| := by
 rw [abs_mul, abs_neg]
 _ ≤ |p.χ₀| *
 (Cg * (2 * Real.sqrt (t0 - c)) * CQ) + (t0 - c) * CL := by
 exact add_le_add
 (mul_le_mul_of_nonneg_left hBtail_t0 (abs_nonneg _)) hLtail_t0
 _ = tailBound rho := by rw [ht0c]
 _ < eps / 3 := htail_t0
 have hcore : dist (Core t) (Core t0) < eps / 3 := hcore_close htcore
 change dist (D.u t x) (D.u t0 x) < eps
 rw [hsplit_t, hsplit_t0, Real.dist_eq]
 have htail_sub :
 |((-p.χ₀) * BTail t + LTail t) -
 ((-p.χ₀) * BTail t0 + LTail t0)| ≤
 |(-p.χ₀) * BTail t + LTail t| +
 |(-p.χ₀) * BTail t0 + LTail t0| := by
 calc
 |((-p.χ₀) * BTail t + LTail t) -
 ((-p.χ₀) * BTail t0 + LTail t0)| =
 |((-p.χ₀) * BTail t + LTail t) +
 (-((-p.χ₀) * BTail t0 + LTail t0))| := by
 congr 1
 _ ≤ |(-p.χ₀) * BTail t + LTail t| +
 |-((-p.χ₀) * BTail t0 + LTail t0)| := abs_add_le _ _
 _ = |(-p.χ₀) * BTail t + LTail t| +
 |(-p.χ₀) * BTail t0 + LTail t0| := by rw [abs_neg]
 calc
 |(Core t + (-p.χ₀) * BTail t + LTail t) -
 (Core t0 + (-p.χ₀) * BTail t0 + LTail t0)|
 ≤ |Core t - Core t0| +
 |(-p.χ₀) * BTail t + LTail t| +
 |(-p.χ₀) * BTail t0 + LTail t0| := by
 calc
 |(Core t + (-p.χ₀) * BTail t + LTail t) -
 (Core t0 + (-p.χ₀) * BTail t0 + LTail t0)| =
 |(Core t - Core t0) +
 (((-p.χ₀) * BTail t + LTail t) -
 ((-p.χ₀) * BTail t0 + LTail t0))| := by
 congr 1
 ring
 _ ≤ |Core t - Core t0| +
 |((-p.χ₀) * BTail t + LTail t) -
 ((-p.χ₀) * BTail t0 + LTail t0)| := abs_add_le _ _
 _ ≤ |Core t - Core t0| +
 (|(-p.χ₀) * BTail t + LTail t| +
 |(-p.χ₀) * BTail t0 + LTail t0|) :=
 add_le_add (le_refl _) htail_sub
 _ = |Core t - Core t0| +
 |(-p.χ₀) * BTail t + LTail t| +
 |(-p.χ₀) * BTail t0 + LTail t0| := by ring
 _ < eps / 3 + eps / 3 + eps / 3 := by
 rw [Real.dist_eq] at hcore
 exact add_lt_add (add_lt_add hcore htail_pair_t) htail_pair_t0
 _ = eps := by ring


private theorem truncatedLimit_timeSlice_continuousWithinAt_Iio
 {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
 (DT : TruncatedConjugateMildExistenceData p u₀)
 {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T)
 (x : intervalDomainPoint) :
 ContinuousWithinAt
 (fun s => truncatedConjugatePicardLimit p u₀ DT.T s x)
 (Set.Iio t) t := by
 have hbase :=
 (truncatedLimit_timeSlice_continuousOn_Ioc DT x).continuousWithinAt
 (show t ∈ Set.Ioc (0 : ℝ) DT.T from ⟨ht, htT⟩)
 have hpos : Set.Ioi (t / 2) ∈ nhds t := Ioi_mem_nhds (by linarith)
 have hinter : Set.Iio t ∩ Set.Ioi (t / 2) ∈ nhdsWithin t (Set.Iio t) :=
 inter_mem_nhdsWithin _ hpos
 have hmem : Set.Ioc (0 : ℝ) DT.T ∈ nhdsWithin t (Set.Iio t) := by
 exact mem_of_superset hinter fun s hs =>
 ⟨lt_trans (by linarith : 0 < t / 2) hs.2, (le_of_lt hs.1).trans htT⟩
 exact hbase.mono_of_mem_nhdsWithin hmem

/-- Left-endpoint convergence of the ordinary Duhamel pairing against the
fixed final negative-part test. -/
private theorem truncatedLimit_logistic_pairing_tendsto
 {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
 (DT : TruncatedConjugateMildExistenceData p u₀)
 {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T) :
 Tendsto
 (fun s => ∫ x,
 intervalFullSemigroupOperator (t - s)
 (truncatedLogisticLifted p
 ((truncatedConjugatePicardLimit p u₀ DT.T) s)) x *
 negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t x
 ∂ intervalMeasure 1)
 (nhdsWithin t (Set.Iio t))
 (nhds (∫ x,
 truncatedLogisticLifted p
 ((truncatedConjugatePicardLimit p u₀ DT.T) t) x *
 negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t x
 ∂ intervalMeasure 1)) := by
 let U := truncatedConjugatePicardLimit p u₀ DT.T
 let L : ℝ → ℝ → ℝ := fun s => truncatedLogisticLifted p (U s)
 let φ : ℝ → ℝ := negativePartTest U t
 let φD : intervalDomainPoint → ℝ := Set.restrict (Set.Icc (0 : ℝ) 1) φ
 let ψ : ℝ → ℝ := ShenWork.IntervalDomain.intervalDomainConstExtend φD
 have hφcont : ContinuousOn φ (Set.Icc (0 : ℝ) 1) := by
 simpa [φ, U] using truncatedLimit_test_continuousOn DT ht htT
 have hφDcont : Continuous φD := by
 simpa [φD] using (continuousOn_iff_continuous_restrict.mp hφcont)
 have hψcont : Continuous ψ := by
 exact ShenWork.IntervalDomain.constExtend_continuous hφDcont
 have hφlift : φ = intervalDomainLift φD := by
 funext y
 by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
 · simp [φD, intervalDomainLift, hy]
 · simp [φ, φD, negativePartTest, negativePartLift,
 intervalDomainLift, hy, negativePart]
 have hψeq : ∀ y ∈ Set.Icc (0 : ℝ) 1, ψ y = φ y := by
 intro y hy
 change ShenWork.IntervalDomain.intervalDomainConstExtend φD y = φ y
 rw [ShenWork.IntervalDomain.constExtend_eq_lift_on_Icc hy, ← hφlift]
 have hφbound : ∀ y, |φ y| ≤ DT.M := by
 intro y
 have hlift : |intervalDomainLift (U t) y| ≤ DT.M := by
 by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
 · simpa [U, intervalDomainLift, hy] using
 (truncatedConjugateMildSolutionData_of_data DT).hbound
 t ht htT ⟨y, hy⟩
 · simp [intervalDomainLift, hy, DT.hM.le]
 simpa [φ, negativePartTest, negativePartLift, abs_neg] using
 (negativePart_abs_le_abs (intervalDomainLift (U t) y)).trans hlift
 have hψbound : ∀ y, |ψ y| ≤ DT.M := by
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
 let C : ℝ := truncatedLogisticBound p DT.M * DT.M
 have hCL : 0 ≤ truncatedLogisticBound p DT.M :=
 truncatedLogisticBound_nonneg p DT.hM.le
 have hC : 0 ≤ C := mul_nonneg hCL DT.hM.le
 have hpos_event : ∀ᶠ s in nhdsWithin t (Set.Iio t), 0 < s := by
 have hnh : Set.Ioi (t / 2) ∈ nhds t := Ioi_mem_nhds (by linarith)
 have hnh' : ∀ᶠ s in nhdsWithin t (Set.Iio t), s ∈ Set.Ioi (t / 2) :=
 Filter.Eventually.filter_mono nhdsWithin_le_nhds hnh
 filter_upwards [hnh'] with s hs
 exact lt_trans (by linarith : 0 < t / 2) hs
 have hFmeas : ∀ᶠ s in nhdsWithin t (Set.Iio t),
 AEStronglyMeasurable (F s) (intervalMeasure 1) := by
 filter_upwards [self_mem_nhdsWithin, hpos_event] with s hst hs0
 have hsT : s ≤ DT.T := (le_of_lt hst).trans htT
 have hScont :=
 ShenWork.IntervalDuhamelIntegrability.intervalFullSemigroupOperator_continuous_of_bounded
 (sub_pos.mpr hst) DT.hM.le hψbound hψmeas
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
 (sub_pos.mpr hst) DT.hM.le hψbound y
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
 have hSlim := hSpoint y (Set.Ioo_subset_Icc_self hy)
 have hmul := hLlim.mul hSlim
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
 (sub_pos.mpr hst)
 (truncatedLimit_logistic_aestronglyMeasurable DT s)
 (by simpa [φ, U] using
 (truncatedLimit_fluxTestDualityData DT ht htT
 (show 0 < t / 2 by linarith) (show t / 2 < t by linarith)).test_bounded.measurable)
 hLbound hφbound
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

private def truncatedResolverSourceDiffEnergy
 (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
 (DT : TruncatedConjugateMildExistenceData p u₀)
 (s t : ℝ) : ℝ :=
 let U := truncatedConjugatePicardLimit p u₀ DT.T
 ∫ y,
 (p.ν * positivePart (intervalDomainLift (U s) y) ^ p.γ -
 p.ν * positivePart (intervalDomainLift (U t) y) ^ p.γ) ^ 2
 ∂intervalMeasure 1

private theorem truncatedResolverSourceDiffEnergy_nonneg
 (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
 (DT : TruncatedConjugateMildExistenceData p u₀) (s t : ℝ) :
 0 ≤ truncatedResolverSourceDiffEnergy p DT s t := by
 exact integral_nonneg fun _ => sq_nonneg _

/-- The positive-part elliptic source is strongly continuous in spatial L²
along every positive-time left filter. This uses only pointwise time
continuity and the uniform truncated ball. -/
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
 have hB : 0 ≤ B := sq_nonneg _
 have hpos_event : ∀ᶠ s in nhdsWithin t (Set.Iio t), 0 < s := by
 have hnh : Set.Ioi (t / 2) ∈ nhds t := Ioi_mem_nhds (by linarith)
 have hnh' : ∀ᶠ s in nhdsWithin t (Set.Iio t), s ∈ Set.Ioi (t / 2) :=
 Filter.Eventually.filter_mono nhdsWithin_le_nhds hnh
 filter_upwards [hnh'] with s hs
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
 exact ShenWork.IntervalDuhamelIntegrability.continuousOn_aestronglyMeasurable_intervalMeasure
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
 have hρbound : ∀ r, 0 < r → r ≤ DT.T → |ρ r y| ≤
 p.ν * DT.M ^ p.γ := by
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
 have hp : Continuous (fun r : ℝ =>
 p.ν * positivePart r ^ p.γ) := by
 have hpp : Continuous (fun r : ℝ => positivePart r) := by
 simpa [positivePart] using continuous_id.max continuous_const
 exact continuous_const.mul
 (hpp.rpow_const (fun _ => Or.inr p.hγ.le))
 have hρlim : Tendsto (fun s => ρ s y) (nhdsWithin t (Set.Iio t))
 (nhds (ρ t y)) := by
 have hlift : ∀ r, intervalDomainLift (U r) y = U r X := by
 intro r
 simp [intervalDomainLift, hyI, X]
 simpa [ρ, hlift] using
 hp.continuousAt.tendsto.comp hUlim
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

/-- Static resolvent stability with the source L² distance left explicit.
Unlike the older ball-Lipschitz theorem, this works for every `γ > 0`. -/
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

/-- The faithful truncated chemotaxis flux is strongly continuous in spatial
`L¹` from the left at every active time. Resolver continuity is obtained
directly from the source `L²` energy, so no Lipschitz estimate for the power
map (and hence no assumption `1 ≤ γ`) is needed. -/
private theorem truncatedLimit_flux_sub_integral_tendsto_zero
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
 let CQ : ℝ := DT.M *
 (Cg * (2 * (p.ν * DT.M ^ p.γ)))
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
 simpa only [mul_zero] using
 (tendsto_const_nhds (x := Cg)).mul hsqrt
 have hCrsqrt : Tendsto (fun s => Cr * Real.sqrt (4 * E s))
 (nhdsWithin t (Set.Iio t)) (nhds 0) := by
 simpa only [mul_zero] using
 (tendsto_const_nhds (x := Cr)).mul hsqrt
 have hpos_event : ∀ᶠ s in nhdsWithin t (Set.Iio t), 0 < s := by
 have hnh : Set.Ioi (t / 2) ∈ nhds t := Ioi_mem_nhds (half_lt_self ht)
 have hnh' : ∀ᶠ s in nhdsWithin t (Set.Iio t), s ∈ Set.Ioi (t / 2) :=
 Filter.Eventually.filter_mono nhdsWithin_le_nhds hnh
 filter_upwards [hnh'] with s hs
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
 (nhdsWithin t (Set.Iio t)) (nhds ((1 + R t) ^ p.β)) := by
 exact (tendsto_const_nhds.add hRlim).rpow_const
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

/-- Left-endpoint convergence of the chemotaxis Duhamel pairing against the
fixed final negative-part test. The fixed-flux term is moved by
self-adjointness onto the Dirichlet heat approximation of the continuous
endpoint-zero flux; the varying-flux term is controlled by `L¹` time
continuity and the preserved derivative envelope of the test. -/
private theorem truncatedLimit_chem_pairing_tendsto_zero
 {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
 (DT : TruncatedConjugateMildExistenceData p u₀)
 {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T) :
 Tendsto
 (fun s => ∫ x,
 truncatedChemFluxLifted p
 ((truncatedConjugatePicardLimit p u₀ DT.T) s) x *
 deriv (fun z : ℝ =>
 intervalFullSemigroupOperator (t - s)
 (negativePartTest
 (truncatedConjugatePicardLimit p u₀ DT.T) t) z) x
 ∂intervalMeasure 1)
 (nhdsWithin t (Set.Iio t)) (nhds 0) := by
 let U := truncatedConjugatePicardLimit p u₀ DT.T
 let Q : ℝ → ℝ → ℝ := fun s => truncatedChemFluxLifted p (U s)
 let φ : ℝ → ℝ := negativePartTest U t
 let D : ℝ → (ℝ → ℝ) → ℝ → ℝ :=
 ShenWork.Paper2.IntervalNegativePartWeakEnergy.intervalConjugateApproxOperator
 let Cg : ℝ := Real.sqrt (∑' k : ℕ,
 (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2)
 let CQ : ℝ := DT.M *
 (Cg * (2 * (p.ν * DT.M ^ p.γ)))
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
 have hφcont : ContinuousOn φ (Set.Icc (0 : ℝ) 1) := by
 simpa [φ, U] using truncatedLimit_test_continuousOn DT ht htT
 have hφmeas : AEStronglyMeasurable φ (intervalMeasure 1) :=
 ShenWork.IntervalDuhamelIntegrability.continuousOn_aestronglyMeasurable_intervalMeasure
 hφcont
 have hφbound : ∀ y, |φ y| ≤ DT.M := by
 intro y
 have hlift : |intervalDomainLift (U t) y| ≤ DT.M := by
 by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
 · simpa [U, intervalDomainLift, hy] using
 (truncatedConjugateMildSolutionData_of_data DT).hbound
 t ht htT ⟨y, hy⟩
 · simp [U, intervalDomainLift, hy, DT.hM.le]
 simpa [φ, negativePartTest, negativePartLift, abs_neg] using
 (negativePart_abs_le_abs (intervalDomainLift (U t) y)).trans hlift
 have hφac : AbsolutelyContinuousOnInterval φ 0 1 := by
 simpa [φ, U] using
 truncatedLimit_negativePartTest_absolutelyContinuous DT ht htT
 obtain ⟨G, hG, hderiv_bound_vol⟩ :=
 truncatedLimit_negativePartTest_deriv_ae_bound_volume DT ht htT
 let d : ℝ → ℝ := fun y =>
 if |deriv φ y| ≤ G then deriv φ y else 0
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
 have hy' : |deriv φ y| ≤ G := by simpa [φ, U] using hy
 simp [d, hy']
 have hd_eq_μ : d =ᵐ[intervalMeasure 1] deriv φ := by
 simp only [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
 exact hd_eq_vol.filter_mono ae_restrict_le
 have hd_int : Integrable d (intervalMeasure 1) :=
 ShenWork.IntervalDomain.intervalMeasure_integrable_of_abs_bound
 hd_meas hd_bound
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
 have hpos_event : ∀ᶠ s in nhdsWithin t (Set.Iio t), 0 < s := by
 have hnh : Set.Ioi (t / 2) ∈ nhds t := Ioi_mem_nhds (half_lt_self ht)
 have hnh' : ∀ᶠ s in nhdsWithin t (Set.Iio t), s ∈ Set.Ioi (t / 2) :=
 Filter.Eventually.filter_mono nhdsWithin_le_nhds hnh
 filter_upwards [hnh'] with s hs
 exact (half_pos ht).trans hs
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
 _ ≤ |D (t - s) (Q t) y - Q t y| + |Q t y| :=
 abs_add_le _ _
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
 have hdu_zero : ∀ᵐ x ∂intervalMeasure 1,
 0 < intervalDomainLift (U t) x →
 deriv (negativePartLift (U t)) x = 0 := by
 filter_upwards [ae_mem_Ioo_unitInterval] with x hx hpos
 have hlift_contOn : ContinuousOn (intervalDomainLift (U t))
 (Set.Icc (0 : ℝ) 1) :=
 ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity.intervalDomain_lift_continuousOn_Icc_of_continuous
 (by simpa [U] using
 (truncatedConjugateMildSolutionData_of_data DT).hcont t ht htT)
 have hlift_cont : ContinuousAt (intervalDomainLift (U t)) x :=
 hlift_contOn.continuousAt (Icc_mem_nhds hx.1 hx.2)
 have hpos_ev : ∀ᶠ y in nhds x, 0 < intervalDomainLift (U t) y :=
 hlift_cont.tendsto.eventually (isOpen_Ioi.mem_nhds hpos)
 have hzero_ev : negativePartLift (U t) =ᶠ[nhds x] fun _ => 0 := by
 filter_upwards [hpos_ev] with y hy
 simp [negativePartLift, negativePart_eq_zero_of_nonneg hy.le]
 rw [hzero_ev.deriv_eq]
 simp
 have hchem_zero : (∫ y, f y ∂intervalMeasure 1) = 0 := by
 have hbase := negativePart_chemFlux_test_integral_eq_zero_regular p U t hdu_zero
 calc
 (∫ y, f y ∂intervalMeasure 1) =
 ∫ y, Q t y * deriv φ y ∂intervalMeasure 1 := by
 apply integral_congr_ae
 filter_upwards [hd_eq_μ] with y hy
 simp [f, hy]
 ring
 _ = 0 := by simpa [Q, φ] using hbase
 have hfixed : Tendsto
 (fun s => ∫ x, Q t x *
 deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) φ z) x
 ∂intervalMeasure 1)
 (nhdsWithin t (Set.Iio t)) (nhds 0) := by
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
 ∂intervalMeasure 1 :=
 hcongr.mono fun _ hs => hs.symm
 have := hFint.congr' hcongr'
 simpa [hchem_zero] using this
 have hsum : Tendsto
 (fun s => V s +
 (∫ x, Q t x *
 deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) φ z) x
 ∂intervalMeasure 1))
 (nhdsWithin t (Set.Iio t)) (nhds 0) := by
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
 (Filter.Eventually.of_forall fun _ => by
 simp only [Pi.sub_apply, Q, U]
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
 simp [V, Q, φ, U]
 ring

/-- Fubini for the ordinary-source tail against the fixed final negative-part
test. Besides the identity, retain integrability of the resulting spatial
pairing for the convex energy increment. -/
private theorem truncatedLimit_logistic_tail_pairing
 {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
 (DT : TruncatedConjugateMildExistenceData p u₀)
 {a t : ℝ} (ha : 0 < a) (hat : a < t) (htT : t ≤ DT.T) :
 let U := truncatedConjugatePicardLimit p u₀ DT.T
 let φ := negativePartTest U t
 Integrable (fun x =>
 (∫ s in a..t,
 intervalFullSemigroupOperator (t - s)
 (truncatedLogisticLifted p (U s)) x) * φ x)
 (intervalMeasure 1) ∧
 IntervalIntegrable (fun s => ∫ x,
 intervalFullSemigroupOperator (t - s)
 (truncatedLogisticLifted p (U s)) x * φ x
 ∂ intervalMeasure 1) volume a t ∧
 (∫ x,
 (∫ s in a..t,
 intervalFullSemigroupOperator (t - s)
 (truncatedLogisticLifted p (U s)) x) * φ x
 ∂ intervalMeasure 1) =
 ∫ s in a..t, ∫ x,
 intervalFullSemigroupOperator (t - s)
 (truncatedLogisticLifted p (U s)) x * φ x
 ∂ intervalMeasure 1 := by
 let U := truncatedConjugatePicardLimit p u₀ DT.T
 let SD := truncatedConjugateMildSolutionData_of_data DT
 let L : ℝ → ℝ → ℝ := fun s => truncatedLogisticLifted p (U s)
 let φ : ℝ → ℝ := negativePartTest U t
 let LF : ℝ → ℝ → ℝ := fun s x =>
 intervalFullSemigroupOperator (t - s) (L s) x * φ x
 let CL : ℝ := truncatedLogisticBound p DT.M
 have ht : 0 < t := ha.trans hat
 have hφmeas : AEStronglyMeasurable φ (intervalMeasure 1) :=
 ShenWork.IntervalDuhamelIntegrability.continuousOn_aestronglyMeasurable_intervalMeasure
 (by simpa [φ, U] using truncatedLimit_test_continuousOn DT ht htT)
 have hφbound : ∀ x, |φ x| ≤ DT.M := by
 intro x
 exact (truncatedLimit_fluxTestDualityData DT ht htT ha hat).test_bounded.bound x
 have hLjoint : Measurable (Function.uncurry L) := by
 simpa [L, U, SD] using
 _root_.ShenWork.Paper2.TruncatedPositiveTimeBootstrap.truncatedLogisticLifted_joint_measurable_of_lift_joint
 (p := p) (w := SD.u) SD.hmeas
 have hSjoint : Measurable (fun r : (ℝ × ℝ) × ℝ =>
 intervalFullSemigroupOperator (r.1.1 - r.2) (L r.2) r.1.2) :=
 ShenWork.IntervalMildPicardThreshold.intervalFullSemigroupOperator_s_param_joint_measurable'
 hLjoint
 have hmap : Measurable (fun z : ℝ × ℝ => (((t, z.2), z.1) : (ℝ × ℝ) × ℝ)) :=
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
 exact Filter.Eventually.of_forall fun _ => ⟨hs.1, lt_of_le_of_ne hs.2 hsne⟩
 have hLFbound : ∀ᵐ z ∂((volume.restrict (Set.Ioc a t)).prod (intervalMeasure 1)),
 ‖Function.uncurry LF z‖ ≤ CL * DT.M := by
 filter_upwards [hprod_mem] with z hz
 have hs0 : 0 < z.1 := ha.trans hz.1
 have hsT : z.1 ≤ DT.T := (le_of_lt hz.2).trans htT
 have hLb := truncatedLogisticLifted_abs_le p DT.hM.le
 (fun x => by simpa [U, SD] using SD.hbound z.1 hs0 hsT x) z.2
 have hSb :=
 ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
 (sub_pos.mpr hz.2) hCL
 (truncatedLogisticLifted_abs_le p DT.hM.le
 (fun x => by simpa [U, SD] using SD.hbound z.1 hs0 hsT x)) z.2
 change |intervalFullSemigroupOperator (t - z.1) (L z.1) z.2 * φ z.2| ≤
 CL * DT.M
 rw [abs_mul]
 exact mul_le_mul hSb (hφbound z.2) (abs_nonneg _) hCL
 have hLFprod : Integrable (Function.uncurry LF)
 ((volume.restrict (Set.Ioc a t)).prod (intervalMeasure 1)) :=
 Integrable.of_bound hLFmeas (CL * DT.M) hLFbound
 have hLFprod_uIoc : Integrable (Function.uncurry LF)
 ((volume.restrict (Set.uIoc a t)).prod (intervalMeasure 1)) := by
 simpa [Set.uIoc_of_le hat.le] using hLFprod
 have hswap := MeasureTheory.intervalIntegral_integral_swap hLFprod_uIoc
 have hspatial_raw : Integrable
 (fun x => ∫ s in a..t, LF s x) (intervalMeasure 1) := by
 simpa [intervalIntegral.integral_of_le hat.le, Set.uIoc_of_le hat.le] using
 hLFprod_uIoc.integral_prod_right
 have htime_int : IntervalIntegrable
 (fun s => ∫ x, LF s x ∂ intervalMeasure 1) volume a t := by
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

set_option maxHeartbeats 0

/-- Fubini for the B-form tail against the fixed final negative-part test.
The regular restricted duality changes the spatial B-pairing into the
negative semigroup-gradient pairing. -/
private theorem truncatedLimit_chem_tail_pairing
 {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
 (DT : TruncatedConjugateMildExistenceData p u₀)
 {a t : ℝ} (ha : 0 < a) (hat : a < t) (htT : t ≤ DT.T) :
 let U := truncatedConjugatePicardLimit p u₀ DT.T
 let φ := negativePartTest U t
 Integrable (fun x =>
 (∫ s in a..t,
 intervalConjugateKernelOperator (t - s)
 (truncatedChemFluxLifted p (U s)) x) * φ x)
 (intervalMeasure 1) ∧
 IntervalIntegrable (fun s => ∫ x,
 truncatedChemFluxLifted p (U s) x *
 deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) φ z) x
 ∂ intervalMeasure 1) volume a t ∧
 (∫ x,
 (∫ s in a..t,
 intervalConjugateKernelOperator (t - s)
 (truncatedChemFluxLifted p (U s)) x) * φ x
 ∂ intervalMeasure 1) =
 -(∫ s in a..t, ∫ x,
 truncatedChemFluxLifted p (U s) x *
 deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) φ z) x
 ∂ intervalMeasure 1) := by
 let U := truncatedConjugatePicardLimit p u₀ DT.T
 let SD := truncatedConjugateMildSolutionData_of_data DT
 let Q : ℝ → ℝ → ℝ := fun s => truncatedChemFluxLifted p (U s)
 let φ : ℝ → ℝ := negativePartTest U t
 let BF : ℝ → ℝ → ℝ := fun s x =>
 intervalConjugateKernelOperator (t - s) (Q s) x * φ x
 let CP : ℝ → ℝ := fun s => ∫ x, Q s x *
 deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) φ z) x
 ∂ intervalMeasure 1
 let Cg : ℝ :=
 ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
 let CQ : ℝ := DT.M *
 (Real.sqrt (∑' k : ℕ,
 (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
 (2 * (p.ν * DT.M ^ p.γ)))
 let K : ℝ := Cg * CQ * DT.M
 have ht : 0 < t := ha.trans hat
 have hφmeas : AEStronglyMeasurable φ (intervalMeasure 1) :=
 ShenWork.IntervalDuhamelIntegrability.continuousOn_aestronglyMeasurable_intervalMeasure
 (by simpa [φ, U] using truncatedLimit_test_continuousOn DT ht htT)
 have hφbound : ∀ x, |φ x| ≤ DT.M := by
 intro x
 exact (truncatedLimit_fluxTestDualityData DT ht htT ha hat).test_bounded.bound x
 have hQjoint : Measurable (Function.uncurry Q) := by
 simpa [Q, U, SD] using
 _root_.ShenWork.Paper2.TruncatedPositiveTimeBootstrap.truncatedChemFluxLifted_joint_measurable_of_lift_joint
 (p := p) (w := SD.u) SD.hmeas
 have hBjoint : Measurable (fun r : (ℝ × ℝ) × ℝ =>
 intervalConjugateKernelOperator (r.1.1 - r.2) (Q r.2) r.1.2) :=
 ShenWork.IntervalConjugateKernelJointMeas.intervalConjugateKernelOperator_s_param_joint_measurable
 hQjoint
 have hmap : Measurable (fun z : ℝ × ℝ => (((t, z.2), z.1) : (ℝ × ℝ) × ℝ)) :=
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
 exact mul_nonneg (mul_nonneg hCg hCQ) DT.hM.le
 have hprod_mem : ∀ᵐ z ∂((volume.restrict (Set.Ioc a t)).prod (intervalMeasure 1)),
 z.1 ∈ Set.Ioo a t := by
 rw [MeasureTheory.Measure.ae_prod_iff_ae_ae
 (measurableSet_Ioo.preimage measurable_fst)]
 filter_upwards [ae_restrict_mem measurableSet_Ioc,
 (Measure.ae_ne volume t).filter_mono ae_restrict_le] with s hs hsne
 exact Filter.Eventually.of_forall fun _ => ⟨hs.1, lt_of_le_of_ne hs.2 hsne⟩
 have hdom_time : Integrable
 (fun s : ℝ => K * (t - s) ^ (-(1 / 2) : ℝ))
 (volume.restrict (Set.Ioc a t)) := by
 exact (integrableOn_Icc_sub_rpow_neg_half_const t K ht.le).mono_set
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
 have HD := truncatedLimit_fluxTestDualityData DT ht htT hs0 hz.2
 have hQint := HD.flux_bounded.integrable
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
 ≤ (Cg * (t - z.1) ^ (-(1 / 2) : ℝ) * CQ) * DT.M :=
 mul_le_mul hBb (hφbound z.2) (abs_nonneg _)
 (mul_nonneg (mul_nonneg hCg (Real.rpow_nonneg (sub_pos.mpr hz.2).le _)) hCQ)
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
 (fun s => ∫ x, BF s x ∂ intervalMeasure 1) volume a t := by
 rw [intervalIntegrable_iff]
 exact hBFprod_uIoc.integral_prod_left
 have hCP_int : IntervalIntegrable CP volume a t := by
 rw [intervalIntegrable_iff]
 rw [intervalIntegrable_iff] at hBtime_int
 have heq : ∀ᵐ s ∂volume.restrict (Set.uIoc a t),
 CP s = -(∫ x, BF s x ∂ intervalMeasure 1) := by
 filter_upwards [ae_restrict_mem measurableSet_uIoc,
 (Measure.ae_ne volume t).filter_mono ae_restrict_le] with s hs hsne
 rw [Set.uIoc_of_le hat.le] at hs
 have hs0 : 0 < s := ha.trans hs.1
 have hst : s < t := lt_of_le_of_ne hs.2 hsne
 have hd := (truncatedLimit_fluxTestDualityData DT ht htT hs0 hst).duality hst
 have hd' : (∫ x, BF s x ∂ intervalMeasure 1) = -CP s := by
 simpa [BF, CP, Q, φ, U] using hd
 linarith [hd']
 apply hBtime_int.neg.congr
 filter_upwards [heq] with s hs
 exact hs.symm
 have htime_eq :
 (∫ s in a..t, ∫ x, BF s x ∂ intervalMeasure 1) =
 -(∫ s in a..t, CP s) := by
 rw [← intervalIntegral.integral_neg]
 apply intervalIntegral.integral_congr_ae
 filter_upwards [(Measure.ae_ne volume t)] with s hsne hsI
 rw [Set.uIoc_of_le hat.le] at hsI
 have hs0 : 0 < s := ha.trans hsI.1
 have hst : s < t := lt_of_le_of_ne hsI.2 hsne
 exact (truncatedLimit_fluxTestDualityData DT ht htT hs0 hst).duality hst
 have hpoint : (fun x =>
 (∫ s in a..t, intervalConjugateKernelOperator (t - s) (Q s) x) * φ x) =
 fun x => ∫ s in a..t, BF s x := by
 funext x
 rw [intervalIntegral.integral_mul_const]
 constructor
 · rw [hpoint]
 exact hspatial_raw
 constructor
 · simpa [CP, Q, φ] using hCP_int
 · rw [hpoint]
 exact hswap.symm.trans (by simpa [BF, CP] using htime_eq)

/-- Restart the faithful truncated mild equation at a positive earlier time.
The two nonlinear tails are left in their native B-form shapes. -/
private theorem truncatedLimit_backward_restart
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

/-- The convex negative-part energy increment is controlled by the two
time-averaged tested nonlinear tails of the positive-time restart. -/
private theorem truncatedLimit_backward_energy_increment_le
 {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
 (DT : TruncatedConjugateMildExistenceData p u₀)
 {a t : ℝ} (ha : 0 < a) (hat : a < t) (htT : t ≤ DT.T) :
 let U := truncatedConjugatePicardLimit p u₀ DT.T
 let φ := negativePartTest U t
 negativePartEnergy U t - negativePartEnergy U a ≤
 2 * (p.χ₀ * (∫ s in a..t, ∫ x,
 truncatedChemFluxLifted p (U s) x *
 deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) φ z) x
 ∂ intervalMeasure 1) +
 ∫ s in a..t, ∫ x,
 intervalFullSemigroupOperator (t - s)
 (truncatedLogisticLifted p (U s)) x * φ x
 ∂ intervalMeasure 1) := by
 let U := truncatedConjugatePicardLimit p u₀ DT.T
 let SD := truncatedConjugateMildSolutionData_of_data DT
 let f : ℝ → ℝ := intervalDomainLift (U a)
 let u : ℝ → ℝ := intervalDomainLift (U t)
 let φ : ℝ → ℝ := negativePartTest U t
 let BT : ℝ → ℝ := fun x => ∫ s in a..t,
 intervalConjugateKernelOperator (t - s)
 (truncatedChemFluxLifted p (U s)) x
 let LT : ℝ → ℝ := fun x => ∫ s in a..t,
 intervalFullSemigroupOperator (t - s)
 (truncatedLogisticLifted p (U s)) x
 let z : ℝ → ℝ := fun x => (-p.χ₀) * BT x + LT x
 let CP : ℝ → ℝ := fun s => ∫ x,
 truncatedChemFluxLifted p (U s) x *
 deriv (fun y : ℝ => intervalFullSemigroupOperator (t - s) φ y) x
 ∂ intervalMeasure 1
 let LP : ℝ → ℝ := fun s => ∫ x,
 intervalFullSemigroupOperator (t - s)
 (truncatedLogisticLifted p (U s)) x * φ x
 ∂ intervalMeasure 1
 have ht : 0 < t := ha.trans hat
 have haT : a ≤ DT.T := (le_of_lt hat).trans htT
 have hfa_cont : Continuous (U a) := by
 simpa [U, SD] using SD.hcont a ha haT
 have hft_cont : Continuous (U t) := by
 simpa [U, SD] using SD.hcont t ht htT
 have hfa_bound : ∀ X, |U a X| ≤ DT.M := by
 intro X
 simpa [U, SD] using SD.hbound a ha haT X
 have hft_bound : ∀ X, |U t X| ≤ DT.M := by
 intro X
 simpa [U, SD] using SD.hbound t ht htT X
 have hf_meas : AEStronglyMeasurable f (intervalMeasure 1) := by
 apply ShenWork.IntervalDuhamelIntegrability.continuousOn_aestronglyMeasurable_intervalMeasure
 simpa [f] using
 ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity.intervalDomain_lift_continuousOn_Icc_of_continuous
 hfa_cont
 have hf_bound : ∀ x, |f x| ≤ DT.M := by
 intro x
 by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
 · simpa [f, intervalDomainLift, hx] using hfa_bound ⟨x, hx⟩
 · simp [f, intervalDomainLift, hx, DT.hM.le]
 have huE : Integrable (fun x => (negativePart (u x)) ^ 2)
 (intervalMeasure 1) := by
 simpa [u, negativePartLift] using
 negativePart_sq_integrable_of_continuous_bound hft_cont DT.hM.le hft_bound
 have hScont : Continuous (fun x => intervalFullSemigroupOperator (t - a) f x) :=
 ShenWork.IntervalDuhamelIntegrability.intervalFullSemigroupOperator_continuous_of_bounded
 (sub_pos.mpr hat) DT.hM.le hf_bound hf_meas
 have hSbound : ∀ x, |intervalFullSemigroupOperator (t - a) f x| ≤ DT.M :=
 ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
 (sub_pos.mpr hat) DT.hM.le hf_bound
 have hSE : Integrable
 (fun x => (negativePart (intervalFullSemigroupOperator (t - a) f x)) ^ 2)
 (intervalMeasure 1) := by
 apply ShenWork.IntervalDomain.intervalMeasure_integrable_of_abs_bound
 · exact (negativePart_continuous.comp hScont).pow 2 |>.aestronglyMeasurable
 · intro x
 rw [abs_pow]
 have hn := (negativePart_abs_le_abs
 (intervalFullSemigroupOperator (t - a) f x)).trans (hSbound x)
 exact pow_le_pow_left₀ (abs_nonneg _) hn 2
 obtain ⟨hLint, _hLPint, hLpair⟩ :=
 truncatedLimit_logistic_tail_pairing DT ha hat htT
 obtain ⟨hBint, _hCPint, hBpair⟩ :=
 truncatedLimit_chem_tail_pairing DT ha hat htT
 have hcomb : Integrable (fun x =>
 (-p.χ₀) * (BT x * φ x) + LT x * φ x) (intervalMeasure 1) := by
 exact hBint.const_mul (-p.χ₀) |>.add hLint
 have hpair : Integrable (fun x => (-2 * negativePart (u x)) * z x)
 (intervalMeasure 1) := by
 have hbase := hcomb.const_mul 2
 apply hbase.congr
 filter_upwards [] with x
 simp only [u, z, BT, LT, φ, negativePartTest, negativePartLift]
 ring
 have hrepr : ∀ᵐ x ∂intervalMeasure 1,
 u x = intervalFullSemigroupOperator (t - a) f x + z x := by
 filter_upwards [ae_mem_Ioo_unitInterval] with x hx
 let X : intervalDomainPoint := ⟨x, Set.Ioo_subset_Icc_self hx⟩
 have hr := truncatedLimit_backward_restart DT ha hat htT X
 have hr' : u x = intervalFullSemigroupOperator (t - a) f x +
 (-p.χ₀) * BT x + LT x := by
 simpa [u, f, BT, LT, U, intervalDomainLift,
 Set.Ioo_subset_Icc_self hx, X] using hr
 rw [hr']
 simp only [z]
 ring
 have hinc :=
 ShenWork.Paper2.IntervalNegativePartWeakEnergy.negativePartEnergy_sub_le_remainder_pairing
 (h := t - a) (f := f) (u := u) (z := z) (M := DT.M)
 (sub_pos.mpr hat) hf_meas hf_bound hrepr huE hSE hpair
 have hpair_integral :
 (∫ x, (-2 * negativePart (u x)) * z x ∂ intervalMeasure 1) =
 2 * (p.χ₀ * (∫ s in a..t, CP s) + ∫ s in a..t, LP s) := by
 calc
 (∫ x, (-2 * negativePart (u x)) * z x ∂ intervalMeasure 1) =
 2 * (∫ x,
 ((-p.χ₀) * (BT x * φ x) + LT x * φ x)
 ∂ intervalMeasure 1) := by
 rw [← MeasureTheory.integral_const_mul]
 apply integral_congr_ae
 filter_upwards [] with x
 simp only [u, z, BT, LT, φ, negativePartTest, negativePartLift]
 ring
 _ = 2 * ((-p.χ₀) * (∫ x, BT x * φ x ∂ intervalMeasure 1) +
 ∫ x, LT x * φ x ∂ intervalMeasure 1) := by
 rw [MeasureTheory.integral_add (hBint.const_mul (-p.χ₀)) hLint,
 MeasureTheory.integral_const_mul]
 _ = 2 * (p.χ₀ * (∫ s in a..t, CP s) + ∫ s in a..t, LP s) := by
 have hb : (∫ x, BT x * φ x ∂ intervalMeasure 1) =
 -(∫ s in a..t, CP s) := by
 simpa [BT, CP, U, φ] using hBpair
 have hl : (∫ x, LT x * φ x ∂ intervalMeasure 1) =
 ∫ s in a..t, LP s := by
 simpa [LT, LP, U, φ] using hLpair
 rw [hb, hl]
 ring
 rw [hpair_integral] at hinc
 simpa [negativePartEnergy, negativePartLift, U, u, f, CP, LP, φ] using hinc

/-- At every positive active time, the backward energy quotient has a
convergent upper bound whose limit is at most `2 a E(t)`. -/
private theorem truncatedLimit_backward_energy_upper_tendsto
 {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
 (DT : TruncatedConjugateMildExistenceData p u₀)
 {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T) :
 let U := truncatedConjugatePicardLimit p u₀ DT.T
 let E := negativePartEnergy U
 ∃ d : ℝ, ∃ R : ℝ → ℝ,
 d ≤ (2 * p.a) * E t ∧
 Tendsto R (nhdsWithin 0 (Set.Ioi 0)) (nhds d) ∧
 ∀ᶠ q in nhdsWithin 0 (Set.Ioi 0),
 q⁻¹ * (E t - E (t - q)) ≤ R q := by
 let U := truncatedConjugatePicardLimit p u₀ DT.T
 let SD := truncatedConjugateMildSolutionData_of_data DT
 let E : ℝ → ℝ := negativePartEnergy U
 let φ : ℝ → ℝ := negativePartTest U t
 let CP : ℝ → ℝ := fun s => ∫ x,
 truncatedChemFluxLifted p (U s) x *
 deriv (fun y : ℝ => intervalFullSemigroupOperator (t - s) φ y) x
 ∂ intervalMeasure 1
 let LP : ℝ → ℝ := fun s => ∫ x,
 intervalFullSemigroupOperator (t - s)
 (truncatedLogisticLifted p (U s)) x * φ x
 ∂ intervalMeasure 1
 let L0 : ℝ := ∫ x,
 truncatedLogisticLifted p (U t) x * φ x ∂ intervalMeasure 1
 let c : ℝ := t / 2
 have hc : 0 < c := by dsimp [c]; linarith
 have hct : c < t := by dsimp [c]; linarith
 obtain ⟨_hLspatial, hLPint, _hLswap⟩ :=
 truncatedLimit_logistic_tail_pairing DT hc hct htT
 obtain ⟨_hBspatial, hCPint, _hBswap⟩ :=
 truncatedLimit_chem_tail_pairing DT hc hct htT
 have hLPint' : IntervalIntegrable LP volume c t := by
 simpa [LP, U, φ] using hLPint
 have hCPint' : IntervalIntegrable CP volume c t := by
 simpa [CP, U, φ] using hCPint
 have hLPmeas : AEStronglyMeasurable LP (volume.restrict (Set.uIoc c t)) := by
 rw [intervalIntegrable_iff] at hLPint'
 exact hLPint'.aestronglyMeasurable
 have hCPmeas : AEStronglyMeasurable CP (volume.restrict (Set.uIoc c t)) := by
 rw [intervalIntegrable_iff] at hCPint'
 exact hCPint'.aestronglyMeasurable
 have hLPlim : Tendsto LP (nhdsWithin t (Set.Iio t)) (nhds L0) := by
 simpa [LP, L0, U, φ] using truncatedLimit_logistic_pairing_tendsto DT ht htT
 have hCPlim : Tendsto CP (nhdsWithin t (Set.Iio t)) (nhds 0) := by
 simpa [CP, U, φ] using truncatedLimit_chem_pairing_tendsto_zero DT ht htT
 have hLPavg :=
 ShenWork.Paper2.IntervalNegativePartWeakEnergy.left_intervalAverage_tendsto
 hct hLPint' hLPmeas hLPlim
 have hCPavg :=
 ShenWork.Paper2.IntervalNegativePartWeakEnergy.left_intervalAverage_tendsto
 hct hCPint' hCPmeas hCPlim
 let d : ℝ := 2 * L0
 let R : ℝ → ℝ := fun q => 2 *
 (p.χ₀ * (q⁻¹ * ∫ s in (t - q)..t, CP s) +
 q⁻¹ * ∫ s in (t - q)..t, LP s)
 refine ⟨d, R, ?_, ?_, ?_⟩
 · have hlog_meas : AEStronglyMeasurable
 (fun x => truncatedLogisticLifted p (U t) x * φ x)
 (intervalMeasure 1) := by
 exact (truncatedLimit_logistic_aestronglyMeasurable DT t).mul
 ((truncatedLimit_fluxTestDualityData DT ht htT hc hct).test_bounded.measurable)
 have hCL : 0 ≤ truncatedLogisticBound p DT.M :=
 truncatedLogisticBound_nonneg p DT.hM.le
 have hlog_int : Integrable
 (fun x => truncatedLogisticLifted p (U t) x * φ x)
 (intervalMeasure 1) := by
 apply ShenWork.IntervalDomain.intervalMeasure_integrable_of_abs_bound hlog_meas
 intro x
 rw [abs_mul]
 exact mul_le_mul
 (truncatedLogisticLifted_abs_le p DT.hM.le (fun X => by
 simpa [U, SD] using SD.hbound t ht htT X) x)
 ((truncatedLimit_fluxTestDualityData DT ht htT hc hct).test_bounded.bound x)
 (abs_nonneg _) hCL
 have hEint : Integrable (fun x => (negativePartLift (U t) x) ^ 2)
 (intervalMeasure 1) := by
 exact negativePart_sq_integrable_of_continuous_bound
 (by simpa [U, SD] using SD.hcont t ht htT) DT.hM.le
 (fun X => by simpa [U, SD] using SD.hbound t ht htT X)
 have hL0 := truncatedLogistic_negativePartTest_integral_le
 p U t (by simpa [φ] using hlog_int) hEint
 dsimp [d, L0, E]
 nlinarith
 · have hinner := (tendsto_const_nhds (x := p.χ₀)).mul hCPavg |>.add hLPavg
 have hmul := (tendsto_const_nhds (x := (2 : ℝ))).mul hinner
 simpa [R, d] using hmul
 · have hqt : ∀ᶠ q in nhdsWithin 0 (Set.Ioi 0), q < t :=
 Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds ht)
 filter_upwards [self_mem_nhdsWithin, hqt] with q hq hqt
 have hq0 : 0 < q := hq
 have ha_q : 0 < t - q := sub_pos.mpr hqt
 have hat_q : t - q < t := sub_lt_self t hq0
 have hinc := truncatedLimit_backward_energy_increment_le
 DT ha_q hat_q htT
 have hinc' : E t - E (t - q) ≤
 2 * (p.χ₀ * (∫ s in (t - q)..t, CP s) +
 ∫ s in (t - q)..t, LP s) := by
 simpa [E, CP, LP, U, φ] using hinc
 have hm := mul_le_mul_of_nonneg_left hinc' (inv_nonneg.mpr hq0.le)
 calc
 q⁻¹ * (E t - E (t - q)) ≤
 q⁻¹ * (2 * (p.χ₀ * (∫ s in (t - q)..t, CP s) +
 ∫ s in (t - q)..t, LP s)) := hm
 _ = R q := by
 dsimp [R]
 ring


/-! ## Negative-part energy continuity from time slices

Joint time-space continuity is stronger than the scalar energy needs. The
fixed-point ball gives one integrable spatial dominator, while the preceding
theorem gives pointwise-in-space time continuity. Dominated convergence
therefore yields continuity on every compact positive-time window. -/

/-- The negative-part energy is continuous on every closed positive-time
window. No iterate-side joint-continuity bootstrap is used. -/
theorem truncatedLimit_negativePartEnergy_continuousOn_positive_window
 {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
 (DT : TruncatedConjugateMildExistenceData p u₀)
 {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbT : b ≤ DT.T) :
 ContinuousOn
 (negativePartEnergy (truncatedConjugatePicardLimit p u₀ DT.T))
 (Set.Icc a b) := by
 let U : ℝ → intervalDomainPoint → ℝ :=
 truncatedConjugatePicardLimit p u₀ DT.T
 let F : ℝ → ℝ → ℝ := fun t y =>
 (negativePart (intervalDomainLift (U t) y)) ^ 2
 have hwindow : Set.Icc a b ⊆ Set.Ioc (0 : ℝ) DT.T := by
 intro t ht
 exact ⟨ha.trans_le ht.1, ht.2.trans hbT⟩
 have hF_meas : ∀ t ∈ Set.Icc a b,
 AEStronglyMeasurable (F t) (intervalMeasure 1) := by
 intro t ht
 have ht0 : 0 < t := ha.trans_le ht.1
 have htT : t ≤ DT.T := ht.2.trans hbT
 have hint := negativePart_sq_integrable_of_continuous_bound
 ((truncatedConjugateMildSolutionData_of_data DT).hcont t ht0 htT)
 DT.hM.le
 ((truncatedConjugateMildSolutionData_of_data DT).hbound t ht0 htT)
 simpa [F, U, negativePartLift] using hint.aestronglyMeasurable
 have hF_bound : ∀ t ∈ Set.Icc a b, ∀ᵐ y ∂ intervalMeasure 1,
 ‖F t y‖ ≤ DT.M ^ 2 := by
 intro t ht
 refine Filter.Eventually.of_forall fun y => ?_
 have ht0 : 0 < t := ha.trans_le ht.1
 have htT : t ≤ DT.T := ht.2.trans hbT
 have hlift : |intervalDomainLift (U t) y| ≤ DT.M := by
 by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
 · simpa [U, intervalDomainLift, hy] using
 (truncatedConjugateMildSolutionData_of_data DT).hbound
 t ht0 htT ⟨y, hy⟩
 · simp [U, intervalDomainLift, hy, DT.hM.le]
 have hneg : |negativePart (intervalDomainLift (U t) y)| ≤ DT.M :=
 (negativePart_abs_le_abs _).trans hlift
 rw [Real.norm_eq_abs]
 simpa [F, abs_pow] using
 (pow_le_pow_left₀ (abs_nonneg _) hneg 2)
 have hdom_int : Integrable (fun _ : ℝ => DT.M ^ 2) (intervalMeasure 1) :=
 integrable_const _
 have hF_cont : ∀ᵐ y ∂ intervalMeasure 1,
 ContinuousOn (fun t => F t y) (Set.Icc a b) := by
 refine Filter.Eventually.of_forall fun y => ?_
 by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
 · let x : intervalDomainPoint := ⟨y, hy⟩
 have htime :=
 (truncatedLimit_timeSlice_continuousOn_Ioc DT x).mono hwindow
 have hcomp :=
 (negativePart_continuous.continuousOn.comp htime
 (fun _ _ => Set.mem_univ _)).pow 2
 have heq : (fun t => F t y) =
 fun t => (negativePart (U t x)) ^ 2 := by
 funext t
 simp only [F, intervalDomainLift, dif_pos hy]
 rfl
 rw [heq]
 exact hcomp
 · have hzero : (fun t => F t y) = fun _ : ℝ => 0 := by
 funext t
 simp only [F, intervalDomainLift, dif_neg hy]
 simp [negativePart]
 rw [hzero]
 exact continuousOn_const
 have hint : ContinuousOn
 (fun t => ∫ y, F t y ∂ intervalMeasure 1) (Set.Icc a b) :=
 MeasureTheory.continuousOn_of_dominated hF_meas hF_bound hdom_int hF_cont
 simpa [negativePartEnergy, negativePartLift, F, U] using hint

/-- With nonnegative initial data, the positive-window continuity extends to
the artificial zero-time endpoint of the truncated trajectory. The initial
trace makes its negative-part energy vanish there. -/
theorem truncatedLimit_negativePartEnergy_continuousOn_Icc
 {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
 (hu₀ : PositiveInitialDatum intervalDomain u₀)
 (DT : TruncatedConjugateMildExistenceData p u₀) :
 ContinuousOn
 (negativePartEnergy (truncatedConjugatePicardLimit p u₀ DT.T))
 (Set.Icc (0 : ℝ) DT.T) := by
 let U : ℝ → intervalDomainPoint → ℝ :=
 truncatedConjugatePicardLimit p u₀ DT.T
 let E : ℝ → ℝ := negativePartEnergy U
 have htrace : InitialTrace intervalDomain u₀ U := by
 simpa [U] using
 truncatedConjugatePicardLimit_initialTrace_of_truncated_data
 p hu₀.admissible.2 DT
 have hu₀_nonneg : ∀ x : intervalDomainPoint, 0 ≤ u₀ x := by
 intro x
 have h := positiveInitialDatum_intervalDomainLift_nonneg hu₀ x.1 x.2
 simpa [intervalDomainLift, x.2] using h
 have hvanish :
 ∀ eps > 0, ∃ delta > 0, ∀ s, 0 < s → s < delta → s < DT.T →
 E s < eps := by
 simpa [U, E] using
 (negativePartEnergy_initial_vanishes_of_trace_nonneg
 hu₀.admissible hu₀_nonneg htrace
 (truncatedConjugateMildSolutionData_of_data DT).hcont DT.hM.le
 (truncatedConjugateMildSolutionData_of_data DT).hbound)
 have hE_zero : E 0 = 0 := by
 have hslice : U 0 = fun _ : intervalDomainPoint => 0 := by
 funext x
 simp [U, truncatedConjugatePicardLimit]
 simp [E, negativePartEnergy, negativePartLift, hslice,
 intervalDomainLift, negativePart]
 have hzero : ContinuousWithinAt E (Set.Ici (0 : ℝ)) 0 := by
 rw [Metric.continuousWithinAt_iff]
 intro eps heps
 obtain ⟨delta, hdelta, hsmall⟩ := hvanish eps heps
 refine ⟨min delta DT.T, lt_min hdelta DT.hT, ?_⟩
 intro t ht0 hdist
 rw [hE_zero, Real.dist_eq, sub_zero]
 by_cases ht : t = 0
 · subst t
 rw [hE_zero, abs_zero]
 exact heps
 · have ht_nonneg : 0 ≤ t := ht0
 have htpos : 0 < t := lt_of_le_of_ne ht_nonneg (Ne.symm ht)
 have habs : |t| < min delta DT.T := by
 change |t - 0| < min delta DT.T at hdist
 simpa only [sub_zero] using hdist
 have htmin : t < min delta DT.T := by
 simpa only [abs_of_nonneg ht_nonneg] using habs
 have hEt : E t < eps :=
 hsmall t htpos (lt_of_lt_of_le htmin (min_le_left _ _))
 (lt_of_lt_of_le htmin (min_le_right _ _))
 have hEnonneg : 0 ≤ E t := by
 exact integral_nonneg fun y => sq_nonneg (negativePartLift (U t) y)
 rw [abs_of_nonneg hEnonneg]
 exact hEt
 intro t ht
 by_cases ht0 : t = 0
 · subst t
 exact hzero.mono fun s hs => hs.1
 · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
 let a : ℝ := t / 2
 have ha : 0 < a := by dsimp [a]; linarith
 have hat : a ≤ t := by dsimp [a]; linarith
 have htmem : t ∈ Set.Icc a DT.T := ⟨hat, ht.2⟩
 have hposwin : ContinuousOn E (Set.Icc a DT.T) := by
 simpa [E, U] using
 truncatedLimit_negativePartEnergy_continuousOn_positive_window
 DT ha (hat.trans ht.2) le_rfl
 have hnhds : Set.Icc a DT.T ∈ 𝓝[Set.Icc (0 : ℝ) DT.T] t := by
 have hopen : Set.Ioi a ∈ 𝓝 t := Ioi_mem_nhds (by dsimp [a]; linarith)
 have hinter : Set.Icc (0 : ℝ) DT.T ∩ Set.Ioi a ∈
 𝓝[Set.Icc (0 : ℝ) DT.T] t := inter_mem_nhdsWithin _ hopen
 exact mem_of_superset hinter fun s hs => ⟨hs.2.le, hs.1.2⟩
 exact (hposwin.continuousWithinAt htmem).mono_of_mem_nhdsWithin hnhds

/-! ## Open-time variational nonnegativity, then endpoint closure -/

/-- The negative-part energy vanishes at every strictly interior active time.
Only positive-time restarts are used in the fencing argument. -/
private theorem truncatedLimit_negativePartEnergy_eq_zero_open
 {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
 (hu₀ : PositiveInitialDatum intervalDomain u₀)
 (DT : TruncatedConjugateMildExistenceData p u₀)
 {t : ℝ} (ht : 0 < t) (htT : t < DT.T) :
 negativePartEnergy (truncatedConjugatePicardLimit p u₀ DT.T) t = 0 := by
 let U := truncatedConjugatePicardLimit p u₀ DT.T
 let E : ℝ → ℝ := negativePartEnergy U
 have hcont : ContinuousOn E (Set.Icc (0 : ℝ) t) := by
 exact (truncatedLimit_negativePartEnergy_continuousOn_Icc hu₀ DT).mono
 (Set.Icc_subset_Icc le_rfl htT.le)
 have hnonneg : ∀ s ∈ Set.Icc (0 : ℝ) t, 0 ≤ E s := by
 intro s _hs
 exact integral_nonneg fun x => sq_nonneg (negativePartLift (U s) x)
 have hE0 : E 0 = 0 := by
 have hU0 : U 0 = fun _ : intervalDomainPoint => 0 := by
 funext x
 simp [U, truncatedConjugatePicardLimit]
 simp [E, negativePartEnergy, negativePartLift, hU0,
 intervalDomainLift, negativePart]
 have hupper : ∀ s ∈ Set.Ioc (0 : ℝ) t, ∃ d : ℝ, ∃ R : ℝ → ℝ,
 d ≤ (2 * p.a) * E s ∧
 Tendsto R (nhdsWithin 0 (Set.Ioi 0)) (nhds d) ∧
 ∀ᶠ q in nhdsWithin 0 (Set.Ioi 0),
 q⁻¹ * (E s - E (s - q)) ≤ R q := by
 intro s hs
 simpa [E, U] using truncatedLimit_backward_energy_upper_tendsto
 DT hs.1 (hs.2.trans htT.le)
 have hzero :=
 ShenWork.Paper2.IntervalNegativePartWeakEnergy.backward_gronwall_zero_of_upper_tendsto
 ht.le hcont hnonneg hE0 hupper
 exact hzero t (Set.right_mem_Icc.mpr ht.le)

/-- Endpoint-safe second stage: continuity closes the zero-energy identity
from `[0,T)` to `[0,T]`. -/
private theorem truncatedLimit_negativePartEnergy_eq_zero_closed
 {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
 (hu₀ : PositiveInitialDatum intervalDomain u₀)
 (DT : TruncatedConjugateMildExistenceData p u₀) :
 Set.EqOn
 (negativePartEnergy (truncatedConjugatePicardLimit p u₀ DT.T))
 (fun _ : ℝ => 0) (Set.Icc (0 : ℝ) DT.T) := by
 let E : ℝ → ℝ :=
 negativePartEnergy (truncatedConjugatePicardLimit p u₀ DT.T)
 have hopen : Set.EqOn E (fun _ : ℝ => 0) (Set.Ico (0 : ℝ) DT.T) := by
 intro t ht
 by_cases ht0 : t = 0
 · subst t
 have hU0 : truncatedConjugatePicardLimit p u₀ DT.T 0 =
 fun _ : intervalDomainPoint => 0 := by
 funext x
 simp [truncatedConjugatePicardLimit]
 simp [E, negativePartEnergy, negativePartLift, hU0,
 intervalDomainLift, negativePart]
 · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
 simpa [E] using
 truncatedLimit_negativePartEnergy_eq_zero_open hu₀ DT htpos ht.2
 have hcont : ContinuousOn E (Set.Icc (0 : ℝ) DT.T) := by
 simpa [E] using truncatedLimit_negativePartEnergy_continuousOn_Icc hu₀ DT
 apply hopen.of_subset_closure hcont continuousOn_const Set.Ico_subset_Icc_self
 rw [closure_Ico (ne_of_lt DT.hT)]

/-- Pointwise nonnegativity on the whole closed active window, obtained only
after the open-time energy argument and endpoint continuity. -/
theorem truncatedConjugatePicardLimit_nonneg
 {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
 (hu₀ : PositiveInitialDatum intervalDomain u₀)
 (DT : TruncatedConjugateMildExistenceData p u₀) :
 ∀ t, 0 < t → t ≤ DT.T → ∀ x : intervalDomainPoint,
 0 ≤ truncatedConjugatePicardLimit p u₀ DT.T t x := by
 let U := truncatedConjugatePicardLimit p u₀ DT.T
 have hint : ∀ t, 0 < t → t ≤ DT.T →
 Integrable (fun x => (negativePartLift (U t) x) ^ 2) (intervalMeasure 1) := by
 intro t ht htT
 exact negativePart_sq_integrable_of_continuous_bound
 (by simpa [U] using
 (truncatedConjugateMildSolutionData_of_data DT).hcont t ht htT)
 DT.hM.le
 (fun X => by simpa [U] using
 (truncatedConjugateMildSolutionData_of_data DT).hbound t ht htT X)
 have hzero := truncatedLimit_negativePartEnergy_eq_zero_closed hu₀ DT
 intro t ht htT
 exact negativePartEnergy_zero_to_pointwise_nonneg_of_continuous
 (u := U) (truncatedConjugateMildSolutionData_of_data DT).hcont hint
 t ht htT (by exact hzero ⟨ht.le, htT⟩)


/-! ## Legacy weak-Duhamel bundle after variational nonnegativity

The old DT-indexed consumer asks for a coefficient-shaped weak certificate at
the terminal time, even though the truncated trajectory is extended by zero
to the right of its horizon. The mathematically correct order is therefore:
first prove nonnegativity by the open-time variational argument, then observe
that the negative-part test is identically zero. At that point every endpoint
and tested-differentiation field of the legacy semigroup bundle is literal
zero, including at `t = T`.
-/

private theorem negativePartTest_eq_zero_of_slice_nonneg
 {u : ℝ → intervalDomainPoint → ℝ} {t : ℝ}
 (h : ∀ x : intervalDomainPoint, 0 ≤ u t x) :
 negativePartTest u t = fun _ : ℝ => 0 := by
 funext y
 by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
 · simp [negativePartTest, negativePartLift, intervalDomainLift, hy,
 negativePart_eq_zero_of_nonneg (h ⟨y, hy⟩)]
 · simp [negativePartTest, negativePartLift, intervalDomainLift, hy,
 negativePart_eq_zero_of_nonneg (le_refl (0 : ℝ))]

/-- Once the variational argument has shown that the truncated limit is
nonnegative, the complete legacy `NegativePartStandardHeatSemigroupDuhamelFacts`
record (including its closed endpoint fields) is discharged without any
pointwise time derivative of the solution. -/
def truncatedLimit_standardHeatSemigroupDuhamelFacts_of_nonneg
 {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
 (DT : TruncatedConjugateMildExistenceData p u₀)
 (hnonneg : ∀ t, 0 < t → t ≤ DT.T → ∀ x : intervalDomainPoint,
 0 ≤ truncatedConjugatePicardLimit p u₀ DT.T t x) :
 NegativePartStandardHeatSemigroupDuhamelFacts p DT.T u₀
 (truncatedConjugatePicardLimit p u₀ DT.T) where
 gradient_tminus_half := neumannHeatGradientTMinusHalfBound
 source_endpoint_l2_lebesgue := by
 intro t ht htT
 have htest := negativePartTest_eq_zero_of_slice_nonneg
 (hnonneg t ht htT)
 simp [HeatDuhamelEndpointLebesguePointFact, htest]
 chem_endpoint_l2_lebesgue := by
 intro t ht htT
 have htest := negativePartTest_eq_zero_of_slice_nonneg
 (hnonneg t ht htT)
 simp [ChemotaxisDuhamelEndpointLebesguePointFact, htest]
 source_dct_dominator := by
 intro t ht htT
 exact (truncatedLimit_dctDominators DT ht htT).1
 chem_dct_dominator := by
 intro t ht htT
 exact (truncatedLimit_dctDominators DT ht htT).2
 semigroup_form_identity := by
 intro t ht htT
 have htest := negativePartTest_eq_zero_of_slice_nonneg
 (hnonneg t ht htT)
 simp [negativePartTestedLegWeakContribution, htest]
 source_duhamel_differentiation := by
 intro t ht htT
 have htest := negativePartTest_eq_zero_of_slice_nonneg
 (hnonneg t ht htT)
 simp [negativePartTestedLegWeakContribution,
 negativePartLogisticWeakTerm, htest]
 hminusone_duhamel_differentiation_after_restricted_duality := by
 intro t ht htT _hdual
 have htest := negativePartTest_eq_zero_of_slice_nonneg
 (hnonneg t ht htT)
 simp [negativePartTestedLegWeakContribution,
 negativePartChemWeakTerm, htest]
 tested_mild_decomposition := by
 intro _hmild t ht htT
 have htest := negativePartTest_eq_zero_of_slice_nonneg
 (hnonneg t ht htT)
 simp [negativePartTestedWeakLHS,
 negativePartTestedLegWeakContribution, htest]

private theorem truncatedLimit_negativePartLift_eq_zero_of_nonneg
 {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
 (DT : TruncatedConjugateMildExistenceData p u₀)
 (hnonneg : ∀ t, 0 < t → t ≤ DT.T → ∀ x : intervalDomainPoint,
 0 ≤ truncatedConjugatePicardLimit p u₀ DT.T t x)
 {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T) :
 negativePartLift
 (truncatedConjugatePicardLimit p u₀ DT.T t) =
 fun _ : ℝ => 0 := by
 funext y
 by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
 · simp [negativePartLift, intervalDomainLift, hy,
 negativePart_eq_zero_of_nonneg (hnonneg t ht htT ⟨y, hy⟩)]
 · simp [negativePartLift, intervalDomainLift, hy,
 negativePart_eq_zero_of_nonneg (le_refl (0 : ℝ))]

private theorem truncatedLimit_negativePartEnergy_eq_zero_of_nonneg
 {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
 (DT : TruncatedConjugateMildExistenceData p u₀)
 (hnonneg : ∀ t, 0 < t → t ≤ DT.T → ∀ x : intervalDomainPoint,
 0 ≤ truncatedConjugatePicardLimit p u₀ DT.T t x)
 {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T) :
 negativePartEnergy (truncatedConjugatePicardLimit p u₀ DT.T) t = 0 := by
 rw [negativePartEnergy,
 truncatedLimit_negativePartLift_eq_zero_of_nonneg DT hnonneg ht htT]
 simp

private theorem truncatedLimit_negativePartEnergy_eq_zero_on_Icc_of_nonneg
 {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
 (DT : TruncatedConjugateMildExistenceData p u₀)
 (hnonneg : ∀ t, 0 < t → t ≤ DT.T → ∀ x : intervalDomainPoint,
 0 ≤ truncatedConjugatePicardLimit p u₀ DT.T t x)
 {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) DT.T) :
 negativePartEnergy (truncatedConjugatePicardLimit p u₀ DT.T) t = 0 := by
 rcases lt_or_eq_of_le ht.1 with htpos | rfl
 · exact truncatedLimit_negativePartEnergy_eq_zero_of_nonneg
 DT hnonneg htpos ht.2
 · simp [negativePartEnergy, negativePartLift,
 truncatedConjugatePicardLimit, negativePart,
 intervalDomainLift]

private theorem truncatedLimit_negativePartEnergy_eq_zero_on_Ici_of_nonneg
 {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
 (DT : TruncatedConjugateMildExistenceData p u₀)
 (hnonneg : ∀ t, 0 < t → t ≤ DT.T → ∀ x : intervalDomainPoint,
 0 ≤ truncatedConjugatePicardLimit p u₀ DT.T t x)
 {t : ℝ} (ht : 0 ≤ t) :
 Set.EqOn
 (negativePartEnergy (truncatedConjugatePicardLimit p u₀ DT.T))
 (fun _ : ℝ => 0) (Set.Ici t) := by
 intro s hts
 rcases eq_or_lt_of_le (ht.trans hts) with rfl | hspos
 · simp [negativePartEnergy, negativePartLift,
 truncatedConjugatePicardLimit, negativePart,
 intervalDomainLift]
 by_cases hsT : s ≤ DT.T
 · exact truncatedLimit_negativePartEnergy_eq_zero_of_nonneg
 DT hnonneg hspos hsT
 · have hslice : truncatedConjugatePicardLimit p u₀ DT.T s =
 fun _ : intervalDomainPoint => 0 := by
 funext x
 simp [truncatedConjugatePicardLimit, not_le.mp hsT]
 simp [negativePartEnergy, negativePartLift, hslice, negativePart,
 intervalDomainLift]

/-- The exact DT-indexed legacy energy record becomes canonical once the
open-time variational argument has supplied nonnegativity. Every energy and
test field is then the zero certificate; this is the endpoint-safe second
stage of the direct weak-form route. -/
def truncatedNegativePartEnergyCoreRegularData_of_nonneg
 {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
 (DT : TruncatedConjugateMildExistenceData p u₀)
 (hnonneg : ∀ t, 0 < t → t ≤ DT.T → ∀ x : intervalDomainPoint,
 0 ≤ truncatedConjugatePicardLimit p u₀ DT.T t x) :
 TruncatedNegativePartEnergyCoreRegularData p DT where
 weak_regular :=
 truncatedNegativePartMildToWeakRegularData_of_standardFacts DT
 (truncatedLimit_standardHeatSemigroupDuhamelFacts_of_nonneg DT hnonneg)
 ell := 0
 hell_nonneg := le_rfl
 E' := fun _ => 0
 estimate := by
 refine
 { neg_deriv_zero_on_pos := ?_
 time_chain := ?_
 diffusion_chain := ?_
 diffusion_nonneg := ?_
 reaction_bound := ?_ }
 · intro t ht htT
 have hneg := truncatedLimit_negativePartLift_eq_zero_of_nonneg
 DT hnonneg ht htT
 filter_upwards [] with x
 simp [hneg]
 · intro t ht htT
 have htest := negativePartTest_eq_zero_of_slice_nonneg
 (hnonneg t ht htT)
 simp [htest]
 · intro t ht htT
 have htest := negativePartTest_eq_zero_of_slice_nonneg
 (hnonneg t ht htT)
 have hneg := truncatedLimit_negativePartLift_eq_zero_of_nonneg
 DT hnonneg ht htT
 simp [negativePartDissipation, htest, hneg]
 · intro t ht htT
 have hneg := truncatedLimit_negativePartLift_eq_zero_of_nonneg
 DT hnonneg ht htT
 simp [negativePartDissipation, hneg]
 · intro t ht htT
 have htest := negativePartTest_eq_zero_of_slice_nonneg
 (hnonneg t ht htT)
 have henergy := truncatedLimit_negativePartEnergy_eq_zero_of_nonneg
 DT hnonneg ht htT
 simp [htest, henergy]
 energy_cont := by
 have heq : Set.EqOn
 (negativePartEnergy (truncatedConjugatePicardLimit p u₀ DT.T))
 (fun _ : ℝ => 0) (Set.Icc (0 : ℝ) DT.T) := by
 intro t ht
 exact truncatedLimit_negativePartEnergy_eq_zero_on_Icc_of_nonneg
 DT hnonneg ht
 exact continuousOn_const.congr heq
 energy_has_deriv := by
 intro t ht
 have heq := truncatedLimit_negativePartEnergy_eq_zero_on_Ici_of_nonneg
 DT hnonneg ht.1
 exact (hasDerivWithinAt_const (x := t) (s := Set.Ici t) (c := (0 : ℝ))).congr
 heq (heq (Set.mem_Ici.mpr le_rfl))
 energy_integrable := by
 intro t ht htT
 have hneg := truncatedLimit_negativePartLift_eq_zero_of_nonneg
 DT hnonneg ht htT
 simp [hneg]
 initial_vanishes := by
 intro ε hε
 exact ⟨1, by norm_num, fun s hs _hs1 hsT => by
 rw [truncatedLimit_negativePartEnergy_eq_zero_of_nonneg
 DT hnonneg hs hsT.le]
 exact hε⟩
 zero_energy_to_pointwise_nonneg := by
 intro t ht htT _hzero
 exact hnonneg t ht htT

/-- Uniform energy producer. This has the exact expansion of
`IntervalChiNegAssembly.UniformTruncatedEnergyData`; the local abbreviation
keeps this file independent of the later Jensen assembly. -/
def uniformTruncatedEnergyData_producer (p : CM2Params) :
 UniformTruncatedEnergyDataDirect p := by
 intro M hM u₀ hu₀ hbound C A
 let DT : TruncatedConjugateMildExistenceData p u₀ :=
 (uniformTruncatedConjugateMildExistenceCore_of_uniformCore C A).toData
 exact truncatedNegativePartEnergyCoreRegularData_of_nonneg DT
 (truncatedConjugatePicardLimit_nonneg hu₀ DT)

end ShenWork.Paper2.IntervalTruncatedEnergyProducer
