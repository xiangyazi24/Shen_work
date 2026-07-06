/-
  ShenWork/Paper2/IntervalDomainPPIDResolverSourceJointInputsFrontier.lean

  PPID restart-core frontier from resolver-source primitive inputs whose
  elementary positivity/upper/lower fields are discharged from
  `GradientMildSolutionData` and joint continuity.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainPPIDResolverSourceInputsFrontier
import ShenWork.Paper2.IntervalResolverSourceWindowJointInputs

set_option linter.style.longLine false

open ShenWork.IntervalDomain
open ShenWork.IntervalMildPicard
open ShenWork.IntervalMildPicardRegularity
open ShenWork.IntervalPicardLimitLogisticSource
open ShenWork.IntervalMildToClassical
open ShenWork.IntervalMildTimeDerivContinuity (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.PPIDThresholdReachability

/-- PPID source frontier where the resolver-source input package keeps only the
representation, joint continuity, spatial K2 bounds, and power-source K1 data. -/
def PerDatumWindowJointInputsSourceSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∃ _S : GradientMildHalfStepLogisticSourceData D,
  ∃ _H : ResolverSourceWindowInput.ResolverSourceWindowJointInputs p D,
    HasTimeNeighborhoodSpectralAgreement D.T D.u ∧
    (∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α))

/-- Iterate/source frontier with the joint-continuity resolver-source input
package. -/
def PerDatumIterateWindowJointInputsSourceSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∃ _I : PicardIterateConvergenceData D,
  ∃ _H : ResolverSourceWindowInput.ResolverSourceWindowJointInputs p D,
    HasTimeNeighborhoodSpectralAgreement D.T D.u ∧
    (∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α))

/-- Joint-input source data fills the Task255 primitive-input source frontier. -/
theorem windowInputsSourceSpectralFrontier_of_windowJointInputsSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumWindowJointInputsSourceSpectralFrontier p D) :
    PerDatumWindowInputsSourceSpectralFrontier p D := by
  obtain ⟨S, hJoint, hTimeNhd, hpde_u⟩ := h
  exact ⟨S,
    ResolverSourceWindowInput.resolverSourceWindowInputs_of_jointInputs hJoint,
    hTimeNhd, hpde_u⟩

/-- Picard-iterate convergence data supplies the logistic source-data field of
the joint-input source surface. -/
theorem windowJointInputsSourceSpectralFrontier_of_iterateWindowJointInputsSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumIterateWindowJointInputsSourceSpectralFrontier p D) :
    PerDatumWindowJointInputsSourceSpectralFrontier p D := by
  obtain ⟨I, hJoint, hTimeNhd, hpde_u⟩ := h
  exact ⟨
    gradientMildHalfStepLogisticSourceData_of_iterateConvergence D I,
    hJoint, hTimeNhd, hpde_u⟩

/-- Fill the Task255 primitive-input surface while preserving the iterate/source
surface. -/
theorem iterateWindowInputsSourceSpectralFrontier_of_iterateWindowJointInputsSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumIterateWindowJointInputsSourceSpectralFrontier p D) :
    PerDatumIterateWindowInputsSourceSpectralFrontier p D := by
  obtain ⟨I, hJoint, hTimeNhd, hpde_u⟩ := h
  exact ⟨I,
    ResolverSourceWindowInput.resolverSourceWindowInputs_of_jointInputs hJoint,
    hTimeNhd, hpde_u⟩

/-- Joint-input source data implies the windowed source frontier. -/
theorem windowSourceSpectralFrontier_of_windowJointInputsSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumWindowJointInputsSourceSpectralFrontier p D) :
    PerDatumWindowSourceSpectralFrontier p D :=
  windowSourceSpectralFrontier_of_windowInputsSourceSpectralFrontier
    (windowInputsSourceSpectralFrontier_of_windowJointInputsSourceSpectralFrontier h)

/-- Iterate/joint-input source data implies the windowed source frontier. -/
theorem windowSourceSpectralFrontier_of_iterateWindowJointInputsSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumIterateWindowJointInputsSourceSpectralFrontier p D) :
    PerDatumWindowSourceSpectralFrontier p D :=
  windowSourceSpectralFrontier_of_windowJointInputsSourceSpectralFrontier
    (windowJointInputsSourceSpectralFrontier_of_iterateWindowJointInputsSourceSpectralFrontier h)

/-- Joint-input source version of the unified Picard-limit frontier bridge. -/
theorem picardLimitRestartFrontier_of_windowJointInputsSourceSpectralFrontier
    {p : CM2Params}
    (hJoint : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowJointInputsSourceSpectralFrontier p D) :
    ConeQuantBridge.PicardLimitRestartFrontier p :=
  picardLimitRestartFrontier_of_windowInputsSourceSpectralFrontier
    (fun u₀ hu₀ D hD =>
      windowInputsSourceSpectralFrontier_of_windowJointInputsSourceSpectralFrontier
        (hJoint u₀ hu₀ D hD))

/-- Iterate/joint-input source version of the unified Picard-limit frontier
bridge. -/
theorem picardLimitRestartFrontier_of_iterateWindowJointInputsSourceSpectralFrontier
    {p : CM2Params}
    (hIterJoint : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowJointInputsSourceSpectralFrontier p D) :
    ConeQuantBridge.PicardLimitRestartFrontier p :=
  picardLimitRestartFrontier_of_iterateWindowInputsSourceSpectralFrontier
    (fun u₀ hu₀ D hD =>
      iterateWindowInputsSourceSpectralFrontier_of_iterateWindowJointInputsSourceSpectralFrontier
        (hIterJoint u₀ hu₀ D hD))

/-- PPID-typed Theorem 1.1 for `χ₀ ≤ 0`, reduced to joint-continuity
resolver-source primitive inputs. -/
theorem theorem_1_1_intervalDomain_of_ppid_windowJointInputsSourceSpectralFrontier_chiNonpos
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hJoint : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowJointInputsSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_windowInputsSourceSpectralFrontier_chiNonpos
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      windowInputsSourceSpectralFrontier_of_windowJointInputsSourceSpectralFrontier
        (hJoint u₀ hu₀ D hD))

/-- Strict-negative specialization of the joint-input PPID source wrapper. -/
theorem theorem_1_1_intervalDomain_of_ppid_windowJointInputsSourceSpectralFrontier_chiNeg
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hJoint : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowJointInputsSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_windowJointInputsSourceSpectralFrontier_chiNonpos
    p (le_of_lt hχ) ha hb hα_ge hγ_ge_one hJoint

/-- PPID-typed Theorem 1.1 for `χ₀ ≤ 0`, reduced to Picard-iterate convergence
plus joint-continuity resolver-source primitive inputs. -/
theorem theorem_1_1_intervalDomain_of_ppid_iterateWindowJointInputsSourceSpectralFrontier_chiNonpos
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hIterJoint : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowJointInputsSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_iterateWindowInputsSourceSpectralFrontier_chiNonpos
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      iterateWindowInputsSourceSpectralFrontier_of_iterateWindowJointInputsSourceSpectralFrontier
        (hIterJoint u₀ hu₀ D hD))

/-- Strict-negative iterate/joint-input specialization. -/
theorem theorem_1_1_intervalDomain_of_ppid_iterateWindowJointInputsSourceSpectralFrontier_chiNeg
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hIterJoint : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowJointInputsSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_iterateWindowJointInputsSourceSpectralFrontier_chiNonpos
    p (le_of_lt hχ) ha hb hα_ge hγ_ge_one hIterJoint

end ShenWork.Paper2.PPIDThresholdReachability
