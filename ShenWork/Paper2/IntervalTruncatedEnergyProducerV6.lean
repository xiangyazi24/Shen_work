/-
  Direct weak-form energy producer for the faithful truncated Picard limit.

  This file deliberately avoids the positive-time coefficient bootstrap.  The
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

open Filter Topology Set MeasureTheory
open scoped BigOperators Topology ENNReal

noncomputable section

namespace ShenWork.Paper2.IntervalTruncatedEnergyProducerV6

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalConjugatePicard
  (UniformConjugateMildExistenceCore)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.Paper2.BFormPositiveDatumNegPart

/-- The exact expansion of
`IntervalChiNegV6Assembly.UniformTruncatedEnergyDataV6`.  Keeping the producer
on this expansion avoids importing the unrelated Jensen assembly chain. -/
abbrev UniformTruncatedEnergyDataV6Direct (p : CM2Params) : Type :=
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
consumer uses only the resulting weak identity.  A single nonzero positive
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

/-- Zero-mode version of the finite-support adapter.  It applies when the
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

/-- Existence form of the complete adapter.  `Nonempty` keeps the case split
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
coefficient-shaped interface.  Spatial continuity is used only in the
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
weak form.  Its coefficient certificates are finite-support encodings of the
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

end ShenWork.Paper2.IntervalTruncatedEnergyProducerV6
