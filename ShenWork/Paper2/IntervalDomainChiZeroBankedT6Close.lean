import ShenWork.PDE.IntervalCoupledResidualAfterBankedT6Discharge
import ShenWork.Paper2.IntervalDomainPdeUWiring
import ShenWork.Paper2.IntervalMildExistenceAssembly

open Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalDuhamelClosedC2
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalGradientDuhamelMap
open ShenWork.IntervalMildPicard
open ShenWork.IntervalCoupledRegularityBootstrap
open ShenWork.IntervalDomainPdeUProducer
open ShenWork.Paper2.IntervalMildExistenceAssembly

noncomputable section

namespace ShenWork.Paper2.ChiZeroBankedT6Close

/-- Localized spectral/Duhamel data sufficient to produce the χ₀=0 `pde_u`
agreement.  This is the data consumed by `PdeUWiring.hasSpectralPdeAgreement...`. -/
structure ChiZeroPdeULocalizedData
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u0) : Type where
  hα : 1 ≤ p.α
  ha : 0 ≤ p.a
  hb : 0 ≤ p.b
  hu0_cont : Continuous u0
  M0 : ℝ
  hu0_bound : ∀ k, |cosineCoeffs (intervalDomainLift u0) k| ≤ M0
  hfix : ∀ s, 0 < s → s < D.T → ∀ x : ℝ,
    (hx : x ∈ Set.Icc (0 : ℝ) 1) →
      intervalDomainLift (D.u s) x =
        intervalGradientDuhamelMap p u0 D.u s ⟨x, hx⟩
  hsrc0 : ShenWork.IntervalPicardLimitRestartBdd.DuhamelSourceBddOn
    (ShenWork.IntervalPicardLimitBddProducer.patchedSource p u0 D.u) D.T
  Msup : ℝ
  bc : ℝ → ℕ → ℝ
  hbsum : ∀ σ, 0 < σ → σ < D.T →
    Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|)
  hagree : ∀ σ, 0 < σ → σ < D.T →
    Set.EqOn (intervalDomainLift (D.u σ))
      (fun x => ∑' n, bc σ n * ShenWork.CosineSpectrum.cosineMode n x)
      (Set.Icc (0 : ℝ) 1)
  hpost : ∀ σ, 0 < σ → σ < D.T →
    ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (D.u σ) x
  hubt : ∀ σ, 0 < σ → σ < D.T →
    ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (D.u σ) x ≤ Msup
  hG1t : ∀ a' b', 0 < a' → b' < D.T → ∃ G1, ∀ σ ∈ Set.Icc a' b',
    ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (intervalDomainLift (D.u σ)) x| ≤ G1
  hG2t : ∀ a' b', 0 < a' → b' < D.T → ∃ G2, ∀ σ ∈ Set.Icc a' b',
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv (intervalDomainLift (D.u σ))) x| ≤ G2
  adott : ℝ → ℕ → ℝ
  hderivt : ∀ σ, 0 < σ → σ < D.T → ∀ k, HasDerivAt
    (fun r => cosineCoeffs
      (ShenWork.IntervalMildPicardRegularity.logisticSourceFun
        p.a p.b p.α (intervalDomainLift (D.u r))) k)
    (adott σ k) σ
  hadotcontt : ∀ k, ContinuousOn (fun σ => adott σ k) (Set.Ioo 0 D.T)
  hMdott : ∀ a' b', 0 < a' → b' < D.T → ∃ Mdot, ∀ σ ∈ Set.Icc a' b',
    ∀ k, |adott σ k| ≤ Mdot
  hLc_ce : ∀ t, 0 < t → t < D.T → ∀ s, 0 < s → s ≤ t →
    Continuous (intervalDomainConstExtend (intervalLogisticSource p (D.u s)))

theorem hasSpectralPdeAgreement_of_localizedData
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    {u0 : intervalDomainPoint → ℝ} {D : GradientMildSolutionData p u0}
    (H : ChiZeroPdeULocalizedData p D) :
    HasSpectralPdeAgreement p D.T D.u :=
  ShenWork.Paper2.PdeUWiring.hasSpectralPdeAgreement_of_localized_data
    (p := p) (u₀ := u0) (T := D.T) (M₀ := H.M0) (Msup := H.Msup)
    hχ0 D.u H.hα H.ha H.hb H.hu0_cont H.hu0_bound H.hfix H.hsrc0
    H.bc H.hbsum H.hagree H.hpost H.hubt H.hG1t H.hG2t H.adott
    H.hderivt H.hadotcontt H.hMdott H.hLc_ce

/-- The χ₀=0 pointwise parabolic identity for `D.u`, produced from the localized
spectral/Duhamel data and the banked spectral generator identity. -/
theorem pde_u_of_chiZero_localizedData
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    {u0 : intervalDomainPoint → ℝ} {D : GradientMildSolutionData p u0}
    (H : ChiZeroPdeULocalizedData p D) :
    ∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (ShenWork.IntervalMildToClassical.mildChemicalConcentration
                p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α) :=
  mildSolution_pde_u_of_spectral p hχ0 D
    (hasSpectralPdeAgreement_of_localizedData hχ0 H)

/-- The χ₀=0 banked-T6 frontier is no longer a separate `pde_u` residual once
the localized spectral/Duhamel data are available. -/
theorem coupledDuhamelBankedT6ChiZeroFrontier_of_localizedData
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    {u0 : intervalDomainPoint → ℝ} {D : GradientMildSolutionData p u0}
    (H : ChiZeroPdeULocalizedData p D)
    (R : CoupledDuhamelClassicalResidualAfterT6 p D.T D.u) :
    CoupledDuhamelBankedT6ChiZeroFrontier p D where
  hpde := hasSpectralPdeAgreement_of_localizedData hχ0 H
  classicalResidual := R

/-- Banked T6 plus localized χ₀=0 spectral data gives the full
`RegularityBootstrap`, with no `CoupledDuhamelBankedT6ChiZeroFrontier` hypothesis. -/
theorem regularityBootstrap_of_chiZero_bankedT6_localizedData
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    {u0 : intervalDomainPoint → ℝ} {D : GradientMildSolutionData p u0}
    (H : ChiZeroPdeULocalizedData p D)
    (hsrc : DuhamelSourceTimeC1 (coupledChemicalSourceCoeffs p D.u))
    (hagree : CoupledDuhamelT6SliceAgreement p D.T D.u)
    (R : CoupledDuhamelClassicalResidualAfterT6 p D.T D.u) :
    RegularityBootstrap p D.T u0 D.u :=
  regularityBootstrap_of_gradientMild_bankedT6_chiZero_spectral
    p H.hu0_cont D hχ0 hsrc hagree
    (coupledDuhamelBankedT6ChiZeroFrontier_of_localizedData hχ0 H R)

/-- Paper-2 local existence through the named `intervalDomain_localExistence...`
bridge, after the χ₀=0 banked-T6 regularity bootstrap has been discharged. -/
theorem intervalDomain_localExistence_of_chiZero_bankedT6_localizedData
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    {u0 : intervalDomainPoint → ℝ}
    (hu0 : PositiveInitialDatum intervalDomain u0)
    {D : GradientMildSolutionData p u0}
    (H : ChiZeroPdeULocalizedData p D)
    (hfp : ∀ t x, 0 ≤ t → t ≤ D.T →
      D.u t x = intervalDuhamelOperator p u0 D.u t x)
    (hsrc : DuhamelSourceTimeC1 (coupledChemicalSourceCoeffs p D.u))
    (hagree : CoupledDuhamelT6SliceAgreement p D.T D.u)
    (R : CoupledDuhamelClassicalResidualAfterT6 p D.T D.u) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u0 u :=
  intervalDomain_localExistence_of_gradientMildSolutionData p hu0 D hfp
    (regularityBootstrap_of_chiZero_bankedT6_localizedData
      hχ0 H hsrc hagree R)

#print axioms hasSpectralPdeAgreement_of_localizedData
#print axioms pde_u_of_chiZero_localizedData
#print axioms coupledDuhamelBankedT6ChiZeroFrontier_of_localizedData
#print axioms regularityBootstrap_of_chiZero_bankedT6_localizedData
#print axioms intervalDomain_localExistence_of_chiZero_bankedT6_localizedData

end ShenWork.Paper2.ChiZeroBankedT6Close
