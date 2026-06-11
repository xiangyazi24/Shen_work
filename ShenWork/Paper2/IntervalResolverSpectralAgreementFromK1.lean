import ShenWork.Paper2.IntervalPicardLimitK1Weak
import ShenWork.Paper2.IntervalPicardLimitTimeNhdSubtype
import ShenWork.Paper2.IntervalResolverTimeRegularity

/-!
# Resolver spectral agreement from the interior K1 ledger

This file packages the local restart construction in the
`ResolverHasSpectralAgreement` type.  The derivative data is not assumed
globally: it is produced from the same `(0, U)` ledger used by
`k1_quadruple_weak_of_subtypeCont`, then consumed by the localized restart
theorem.
-/

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalDomainConstExtend)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
open ShenWork.IntervalGradientDuhamelMap (intervalGradientDuhamelMap)
open ShenWork.IntervalMildTimeDerivContinuity
  (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalPicardLimitBddProducer (patchedSource)
open ShenWork.IntervalPicardLimitRestartBdd (DuhamelSourceBddOn)
open ShenWork.IntervalResolverTimeRegularity (ResolverHasSpectralAgreement)

noncomputable section

namespace ShenWork.Paper2.ResolverSpectralAgreementFromK1

/-- **Interior-ledger producer for `ResolverHasSpectralAgreement`.**

The proof first derives the interior source-coefficient K1 triple using
`k1_quadruple_weak_of_subtypeCont`; the localized restart theorem then builds,
for each interior `t₀`, the soft-clamped `DuhamelSourceTimeC1` witness and the
eventual restart representation.  The final step is just the record-type
conversion from `HasTimeNeighborhoodSpectralAgreement` to
`ResolverHasSpectralAgreement`.
-/
theorem resolverHasSpectralAgreement_of_ledger_of_subtypeCont
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    {u₀ : intervalDomainPoint → ℝ} (u : ℝ → intervalDomainPoint → ℝ)
    {U : ℝ}
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hu₀_cont : Continuous u₀)
    {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hfix : ∀ s, 0 < s → s < U → ∀ x : ℝ,
      (hx : x ∈ Set.Icc (0 : ℝ) 1) →
        intervalDomainLift (u s) x =
          intervalGradientDuhamelMap p u₀ u s ⟨x, hx⟩)
    (hsrc0 : DuhamelSourceBddOn (patchedSource p u₀ u) U)
    {Msup : ℝ}
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ, 0 < σ → σ < U →
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagree : ∀ σ, 0 < σ → σ < U →
      Set.EqOn (intervalDomainLift (u σ))
        (fun x => ∑' n, bc σ n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1))
    (hpost : ∀ σ, 0 < σ → σ < U →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (u σ) x)
    (hubt : ∀ σ, 0 < σ → σ < U →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (u σ) x ≤ Msup)
    (hG1t : ∀ a' b', 0 < a' → b' < U → ∃ G1,
      ∀ σ ∈ Set.Icc a' b', ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (intervalDomainLift (u σ)) x| ≤ G1)
    (hG2t : ∀ a' b', 0 < a' → b' < U → ∃ G2,
      ∀ σ ∈ Set.Icc a' b', ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (deriv (intervalDomainLift (u σ))) x| ≤ G2)
    (hLc_ce : ∀ t, 0 < t → t < U →
      ∀ s, 0 < s → s ≤ t →
        Continuous (intervalDomainConstExtend (intervalLogisticSource p (u s)))) :
    ResolverHasSpectralAgreement U u := by
  obtain ⟨hderiv, hadotcont, hMdot⟩ :=
    ShenWork.Paper2.PicardLimitK1Weak.k1_quadruple_weak_of_subtypeCont
      hχ0 u hα ha hb hu₀_cont hu₀_bound hfix hsrc0 bc hbsum
      hagree hpost hubt hG1t hG2t hLc_ce
  have Hu : HasTimeNeighborhoodSpectralAgreement U u :=
    ShenWork.Paper2.TimeNhdSubtype.Hu_of_restart_localized_of_subtypeCont
      hχ0 u hα ha hb hu₀_cont hu₀_bound hfix hsrc0 bc hbsum
      hagree hpost hubt hG1t hG2t
      (ShenWork.Paper2.PicardLimitK1.adottOf p u)
      hderiv hadotcont hMdot hLc_ce
  exact ⟨Hu.exists_data⟩

end ShenWork.Paper2.ResolverSpectralAgreementFromK1

