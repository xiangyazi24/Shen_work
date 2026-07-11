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
import ShenWork.Paper2.IntervalTruncatedPositiveTimeBootstrap

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

/-! ## Legacy weak-Duhamel bundle after variational nonnegativity

The old DT-indexed consumer asks for a coefficient-shaped weak certificate at
the terminal time, even though the truncated trajectory is extended by zero
to the right of its horizon.  The mathematically correct order is therefore:
first prove nonnegativity by the open-time variational argument, then observe
that the negative-part test is identically zero.  At that point every endpoint
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
open-time variational argument has supplied nonnegativity.  Every energy and
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

end ShenWork.Paper2.IntervalTruncatedEnergyProducerV6
