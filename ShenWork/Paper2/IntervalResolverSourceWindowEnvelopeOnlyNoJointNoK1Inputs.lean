/-
  ShenWork/Paper2/IntervalResolverSourceWindowEnvelopeOnlyNoJointNoK1Inputs.lean

  χ₀ = 0 resolver-source envelope inputs with K1 power-source fields derived
  from the bounded patched-source package.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalResolverSourceWindowEnvelopeOnlyNoJointInputs
import ShenWork.Paper2.IntervalResolverPowerK1
import ShenWork.Paper2.IntervalDomainConstExtendAdapter

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomain intervalDomainLift intervalDomainPoint
  intervalDomainConstExtend)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)
open ShenWork.IntervalPicardLimitRestartBdd (DuhamelSourceBddOn)
open ShenWork.IntervalPicardLimitBddProducer (patchedSource)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)

noncomputable section

namespace ShenWork.Paper2.ResolverSourceWindowInput

/-- Initial cosine coefficients of a positive admissible interval datum are
bounded by twice the datum sup bound. -/
theorem initial_cosineCoeffs_bound_of_positiveInitialDatum
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀) :
    ∀ k, |cosineCoeffs (intervalDomainLift u₀) k|
      ≤ 2 * sSup (Set.range fun x => |u₀ x|) := by
  have hbdd : BddAbove (Set.range fun x => |u₀ x|) := hu₀.admissible.1
  have hB0 : 0 ≤ sSup (Set.range fun x => |u₀ x|) :=
    le_trans (abs_nonneg _)
      (le_csSup hbdd ⟨⟨1 / 2, ⟨by norm_num, by norm_num⟩⟩, rfl⟩)
  have hcont : ContinuousOn (intervalDomainLift u₀) (Set.Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    have heq : (Set.Icc (0 : ℝ) 1).restrict (intervalDomainLift u₀) = u₀ := by
      funext ⟨y, hy⟩
      simp only [Set.restrict_apply, intervalDomainLift]
      split_ifs
      exact congr_arg u₀ (Subtype.ext rfl)
    rw [heq]
    exact hu₀.admissible.2
  have hfb : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |intervalDomainLift u₀ x| ≤ sSup (Set.range fun x => |u₀ x|) := by
    intro x hx
    simp only [intervalDomainLift, dif_pos hx]
    exact le_csSup hbdd ⟨⟨x, hx⟩, rfl⟩
  exact ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
    hcont hB0 hfb

/-- Envelope/no-joint primitive resolver-source inputs with the power-source K1
quadruple removed.  In the χ₀ = 0 branch, the missing K1 fields are produced
from the bounded patched-source package `hsrc0` plus the envelope-derived K2
spatial bounds. -/
structure ResolverSourceWindowEnvelopeOnlyNoJointNoK1Inputs
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) where
  bc : ℝ → ℕ → ℝ
  hagree : ∀ σ, 0 < σ → σ < D.T →
    Set.EqOn (intervalDomainLift (D.u σ))
      (fun x => ∑' n, bc σ n * cosineMode n x)
      (Set.Icc (0 : ℝ) 1)
  henv : ∀ a b, 0 < a → b < D.T → a ≤ b →
    ∃ E : ℕ → ℝ,
      Summable E ∧
      (∀ n, 0 ≤ E n) ∧
      (∀ σ ∈ Set.Icc a b, ∀ n,
        unitIntervalCosineEigenvalue n * |bc σ n| ≤ E n)
  hsrc0 : DuhamelSourceBddOn (patchedSource p u₀ D.u) D.T

/-- In the χ₀ = 0 branch, no-K1 envelope/no-joint inputs fill the previous
envelope/no-joint package by deriving the power-source K1 fields from `hsrc0`. -/
def resolverSourceWindowEnvelopeOnlyNoJointInputs_of_envelopeOnlyNoJointNoK1Inputs
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (hχ0 : p.χ₀ = 0) (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (H : ResolverSourceWindowEnvelopeOnlyNoJointNoK1Inputs p D) :
    ResolverSourceWindowEnvelopeOnlyNoJointInputs p D := by
  let hu₀_bound := initial_cosineCoeffs_bound_of_positiveInitialDatum hu₀
  let hbsum : ∀ σ, 0 < σ → σ < D.T →
      Summable (fun n => unitIntervalCosineEigenvalue n * |H.bc σ n|) :=
    hbsum_of_envelope H.bc H.henv
  let hpost : ∀ σ, 0 < σ → σ < D.T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (D.u σ) x :=
    fun σ hσ hσT x hx => by
      simp only [intervalDomainLift, dif_pos hx]
      exact D.hpos σ hσ hσT.le ⟨x, hx⟩
  let hubt : ∀ σ, 0 < σ → σ < D.T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (D.u σ) x ≤ D.M :=
    fun σ hσ hσT x hx => by
      simp only [intervalDomainLift, dif_pos hx]
      exact le_trans (le_abs_self _) (D.hbound σ hσ hσT.le ⟨x, hx⟩)
  let hG1t : ∀ a b, 0 < a → b < D.T →
      ∃ G1, ∀ σ ∈ Set.Icc a b, ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (intervalDomainLift (D.u σ)) x| ≤ G1 :=
    hG1_of_envelope H.bc hbsum H.hagree H.henv
  let hG2t : ∀ a b, 0 < a → b < D.T →
      ∃ G2, ∀ σ ∈ Set.Icc a b, ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (deriv (intervalDomainLift (D.u σ))) x| ≤ G2 :=
    hG2_of_envelope H.bc hbsum H.hagree H.henv
  let hfix : ∀ s, 0 < s → s < D.T → ∀ x : ℝ,
      (hx : x ∈ Set.Icc (0 : ℝ) 1) →
        intervalDomainLift (D.u s) x =
          ShenWork.IntervalGradientDuhamelMap.intervalGradientDuhamelMap
            p u₀ D.u s ⟨x, hx⟩ :=
    fun s hs hsT x hx => by
      simp only [intervalDomainLift, dif_pos hx]
      exact D.hmild s hs hsT.le ⟨x, hx⟩
  let hLc_ce : ∀ t, 0 < t → t < D.T →
      ∀ s, 0 < s → s ≤ t →
        Continuous (intervalDomainConstExtend (intervalLogisticSource p (D.u s))) :=
    fun _t _ht htT s hs hsT =>
      ShenWork.Paper2.ConstExtendAdapter.logisticSource_constExtend_continuous D hs
        (hsT.trans htT.le)
  obtain ⟨hderivPow, hadotPowCont, hMdotPow⟩ :=
    ShenWork.Paper2.ResolverPowerK1.powerK1_quadruple_of_subtypeCont
      (p := p) hχ0 D.u hα ha hb hu₀.admissible.2 hu₀_bound hfix H.hsrc0
      (Msup := D.M) H.bc hbsum H.hagree hpost hubt hG1t hG2t hLc_ce
  exact
    { bc := H.bc
      hagree := H.hagree
      henv := H.henv
      adotPow := ShenWork.Paper2.ResolverPowerK1.adotPowOf p D.u
      hderivPow := hderivPow
      hadotPowCont := hadotPowCont
      hMdotPow := hMdotPow }

end ShenWork.Paper2.ResolverSourceWindowInput
