/-
  ShenWork/Paper2/IntervalDomainPPIDResolverSourceNoJointFrontier.lean

  PPID restart-core frontier from resolver-source primitive inputs with the
  joint-continuity field removed.  The already-carried u-side
  `HasTimeNeighborhoodSpectralAgreement` supplies that field.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainPPIDResolverSourceJointInputsFrontier
import ShenWork.Paper2.IntervalMildRegularityFrontierAssembly

set_option linter.style.longLine false

open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalMildPicard
open ShenWork.IntervalMildPicardRegularity
open ShenWork.IntervalPicardLimitLogisticSource
open ShenWork.IntervalMildToClassical
open ShenWork.IntervalMildTimeDerivContinuity (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.ResolverSourceWindowInput

/-- Joint-input package with `hliftCont` removed.

The PPID source surfaces already carry `HasTimeNeighborhoodSpectralAgreement`;
that u-side spectral agreement gives the lifted joint continuity, so it should
not remain an independent resolver-source input. -/
structure ResolverSourceWindowNoJointInputs
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) where
  bc : ℝ → ℕ → ℝ
  hbsum : ∀ σ, 0 < σ → σ < D.T →
    Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|)
  hagree : ∀ σ, 0 < σ → σ < D.T →
    Set.EqOn (intervalDomainLift (D.u σ))
      (fun x => ∑' n, bc σ n * cosineMode n x)
      (Set.Icc (0 : ℝ) 1)
  hG1 : ∀ a b, 0 < a → b < D.T →
    ∃ G1, ∀ σ ∈ Set.Icc a b, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (D.u σ)) x| ≤ G1
  hG2 : ∀ a b, 0 < a → b < D.T →
    ∃ G2, ∀ σ ∈ Set.Icc a b, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv (intervalDomainLift (D.u σ))) x| ≤ G2
  adotPow : ℝ → ℕ → ℝ
  hderivPow : ∀ σ, 0 < σ → σ < D.T → ∀ n,
    HasDerivAt
      (fun r => cosineCoeffs
        (fun x => p.ν * intervalDomainLift (D.u r) x ^ p.γ) n)
      (adotPow σ n) σ
  hadotPowCont : ∀ n, ContinuousOn (fun σ => adotPow σ n) (Set.Ioo 0 D.T)
  hMdotPow : ∀ a b, 0 < a → b < D.T →
    ∃ Mdot, ∀ σ ∈ Set.Icc a b, ∀ n, |adotPow σ n| ≤ Mdot

/-- Fill the removed lifted joint-continuity field from u-side spectral
agreement. -/
def resolverSourceWindowJointInputs_of_noJointInputs
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u)
    (H : ResolverSourceWindowNoJointInputs p D) :
    ResolverSourceWindowJointInputs p D where
  bc := H.bc
  hbsum := H.hbsum
  hagree := H.hagree
  hliftCont :=
    RegularityFrontierAssembly.jointSolutionClosed_u_of_spectralAgreement Hu
  hG1 := H.hG1
  hG2 := H.hG2
  adotPow := H.adotPow
  hderivPow := H.hderivPow
  hadotPowCont := H.hadotPowCont
  hMdotPow := H.hMdotPow

end ShenWork.Paper2.ResolverSourceWindowInput

namespace ShenWork.Paper2.PPIDThresholdReachability

/-- PPID source frontier where the resolver-source input package no longer
carries lifted joint continuity as a separate field. -/
def PerDatumWindowNoJointInputsSourceSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∃ _S : GradientMildHalfStepLogisticSourceData D,
  ∃ _H : ResolverSourceWindowInput.ResolverSourceWindowNoJointInputs p D,
    HasTimeNeighborhoodSpectralAgreement D.T D.u ∧
    (∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α))

/-- Iterate/source frontier with the no-joint-continuity resolver-source input
package. -/
def PerDatumIterateWindowNoJointInputsSourceSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∃ _I : PicardIterateConvergenceData D,
  ∃ _H : ResolverSourceWindowInput.ResolverSourceWindowNoJointInputs p D,
    HasTimeNeighborhoodSpectralAgreement D.T D.u ∧
    (∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α))

/-- No-joint source data fills the Task259 joint-input source frontier. -/
theorem windowJointInputsSourceSpectralFrontier_of_windowNoJointInputsSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumWindowNoJointInputsSourceSpectralFrontier p D) :
    PerDatumWindowJointInputsSourceSpectralFrontier p D := by
  obtain ⟨S, hNoJoint, hTimeNhd, hpde_u⟩ := h
  exact ⟨S,
    ResolverSourceWindowInput.resolverSourceWindowJointInputs_of_noJointInputs
      hTimeNhd hNoJoint,
    hTimeNhd, hpde_u⟩

/-- Picard-iterate convergence data supplies the logistic source-data field of
the no-joint-input source surface. -/
theorem windowNoJointInputsSourceSpectralFrontier_of_iterateWindowNoJointInputsSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumIterateWindowNoJointInputsSourceSpectralFrontier p D) :
    PerDatumWindowNoJointInputsSourceSpectralFrontier p D := by
  obtain ⟨I, hNoJoint, hTimeNhd, hpde_u⟩ := h
  exact ⟨
    gradientMildHalfStepLogisticSourceData_of_iterateConvergence D I,
    hNoJoint, hTimeNhd, hpde_u⟩

/-- Fill the Task259 joint-input surface while preserving the iterate/source
surface. -/
theorem iterateWindowJointInputsSourceSpectralFrontier_of_iterateWindowNoJointInputsSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumIterateWindowNoJointInputsSourceSpectralFrontier p D) :
    PerDatumIterateWindowJointInputsSourceSpectralFrontier p D := by
  obtain ⟨I, hNoJoint, hTimeNhd, hpde_u⟩ := h
  exact ⟨I,
    ResolverSourceWindowInput.resolverSourceWindowJointInputs_of_noJointInputs
      hTimeNhd hNoJoint,
    hTimeNhd, hpde_u⟩

/-- No-joint-input source data implies the windowed source frontier. -/
theorem windowSourceSpectralFrontier_of_windowNoJointInputsSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumWindowNoJointInputsSourceSpectralFrontier p D) :
    PerDatumWindowSourceSpectralFrontier p D :=
  windowSourceSpectralFrontier_of_windowJointInputsSourceSpectralFrontier
    (windowJointInputsSourceSpectralFrontier_of_windowNoJointInputsSourceSpectralFrontier h)

/-- Iterate/no-joint-input source data implies the windowed source frontier. -/
theorem windowSourceSpectralFrontier_of_iterateWindowNoJointInputsSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumIterateWindowNoJointInputsSourceSpectralFrontier p D) :
    PerDatumWindowSourceSpectralFrontier p D :=
  windowSourceSpectralFrontier_of_windowNoJointInputsSourceSpectralFrontier
    (windowNoJointInputsSourceSpectralFrontier_of_iterateWindowNoJointInputsSourceSpectralFrontier h)

/-- No-joint-input source version of the unified Picard-limit frontier bridge. -/
theorem picardLimitRestartFrontier_of_windowNoJointInputsSourceSpectralFrontier
    {p : CM2Params}
    (hNoJoint : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowNoJointInputsSourceSpectralFrontier p D) :
    ConeQuantBridge.PicardLimitRestartFrontier p :=
  picardLimitRestartFrontier_of_windowJointInputsSourceSpectralFrontier
    (fun u₀ hu₀ D hD =>
      windowJointInputsSourceSpectralFrontier_of_windowNoJointInputsSourceSpectralFrontier
        (hNoJoint u₀ hu₀ D hD))

/-- Iterate/no-joint-input source version of the unified Picard-limit frontier
bridge. -/
theorem picardLimitRestartFrontier_of_iterateWindowNoJointInputsSourceSpectralFrontier
    {p : CM2Params}
    (hIterNoJoint : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowNoJointInputsSourceSpectralFrontier p D) :
    ConeQuantBridge.PicardLimitRestartFrontier p :=
  picardLimitRestartFrontier_of_iterateWindowJointInputsSourceSpectralFrontier
    (fun u₀ hu₀ D hD =>
      iterateWindowJointInputsSourceSpectralFrontier_of_iterateWindowNoJointInputsSourceSpectralFrontier
        (hIterNoJoint u₀ hu₀ D hD))

/-- PPID-typed Theorem 1.1 for `χ₀ ≤ 0`, reduced to no-joint-continuity
resolver-source primitive inputs. -/
theorem theorem_1_1_intervalDomain_of_ppid_windowNoJointInputsSourceSpectralFrontier_chiNonpos
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hNoJoint : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowNoJointInputsSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_windowJointInputsSourceSpectralFrontier_chiNonpos
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      windowJointInputsSourceSpectralFrontier_of_windowNoJointInputsSourceSpectralFrontier
        (hNoJoint u₀ hu₀ D hD))

/-- Strict-negative specialization of the no-joint-input PPID source wrapper. -/
theorem theorem_1_1_intervalDomain_of_ppid_windowNoJointInputsSourceSpectralFrontier_chiNeg
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hNoJoint : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowNoJointInputsSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_windowNoJointInputsSourceSpectralFrontier_chiNonpos
    p (le_of_lt hχ) ha hb hα_ge hγ_ge_one hNoJoint

/-- PPID-typed Theorem 1.1 for `χ₀ ≤ 0`, reduced to Picard-iterate convergence
plus no-joint-continuity resolver-source primitive inputs. -/
theorem theorem_1_1_intervalDomain_of_ppid_iterateWindowNoJointInputsSourceSpectralFrontier_chiNonpos
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hIterNoJoint : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowNoJointInputsSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_iterateWindowJointInputsSourceSpectralFrontier_chiNonpos
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      iterateWindowJointInputsSourceSpectralFrontier_of_iterateWindowNoJointInputsSourceSpectralFrontier
        (hIterNoJoint u₀ hu₀ D hD))

/-- Strict-negative iterate/no-joint-input specialization. -/
theorem theorem_1_1_intervalDomain_of_ppid_iterateWindowNoJointInputsSourceSpectralFrontier_chiNeg
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hIterNoJoint : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowNoJointInputsSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_iterateWindowNoJointInputsSourceSpectralFrontier_chiNonpos
    p (le_of_lt hχ) ha hb hα_ge hγ_ge_one hIterNoJoint

#print axioms theorem_1_1_intervalDomain_of_ppid_windowNoJointInputsSourceSpectralFrontier_chiNonpos
#print axioms theorem_1_1_intervalDomain_of_ppid_windowNoJointInputsSourceSpectralFrontier_chiNeg
#print axioms theorem_1_1_intervalDomain_of_ppid_iterateWindowNoJointInputsSourceSpectralFrontier_chiNonpos
#print axioms theorem_1_1_intervalDomain_of_ppid_iterateWindowNoJointInputsSourceSpectralFrontier_chiNeg

end ShenWork.Paper2.PPIDThresholdReachability
