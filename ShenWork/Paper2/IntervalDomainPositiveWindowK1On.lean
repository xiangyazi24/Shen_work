import ShenWork.Paper2.IntervalDomainLimitSourceRepresentationOn
import ShenWork.Paper2.IntervalPicardLimitK1Weak

/-!
# Positive-window K1 data for the `TimeC1On` source adapter

This file records the part of W9 that closes without the horizon endpoint:
on a genuine positive window `[c,d]` with `d < T`, the weak K1 producer gives
two-sided derivatives at every point of the window, and these restrict to the
one-sided closed-window derivatives consumed by the committed `On` adapter.

The remaining `d = T` endpoint is not faked here.  It requires the shifted
source package demanded by
`logisticSource_adot_hasDerivWithinAt_endpoint_window`; producing that shifted
package is the recursive endpoint gap described in the handoff.
-/

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalDomain (intervalDomainConstExtend)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
open ShenWork.IntervalGradientDuhamelMap (intervalGradientDuhamelMap logisticLifted)
open ShenWork.IntervalMildPicardRegularity (logisticSourceFun)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalPicardLimitRestartBdd (DuhamelSourceBddOn)
open ShenWork.IntervalPicardLimitBddProducer (patchedSource)
open ShenWork.IntervalDuhamelSourceTimeC1On (DuhamelSourceTimeC1On)
open ShenWork.IntervalDomainLimitSourceRepresentationOn
  (limitSource_duhamelSourceTimeC1On_of_representation)

noncomputable section

namespace ShenWork.IntervalDomainPositiveWindowK1On

abbrev sourceCoeff (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) :
    ℝ → ℕ → ℝ :=
  fun σ k => cosineCoeffs
    (logisticSourceFun p.a p.b p.α (intervalDomainLift (u σ))) k

/-- Closed-window K1 data in exactly the shape consumed by
`limitSource_duhamelSourceTimeC1On_of_representation`. -/
structure WindowK1Quadruple
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (lo hi : ℝ) where
  adot : ℝ → ℕ → ℝ
  hderiv : ∀ σ ∈ Set.Icc lo hi, ∀ k,
    HasDerivWithinAt (fun r => sourceCoeff p u r k) (adot σ k)
      (Set.Icc lo hi) σ
  hadotcont : ∀ k, ContinuousOn (fun σ => adot σ k) (Set.Icc lo hi)
  Mdot : ℝ
  hMdot : ∀ σ ∈ Set.Icc lo hi, ∀ k, |adot σ k| ≤ Mdot

/-- Strict-interior positive-window K1 producer from
`k1_quadruple_weak_of_subtypeCont`.

Every point of `[c,d]` is in `(0,T)` because `0 < c` and `d < T`, so the
two-sided weak-K1 derivative restricts to the closed-window derivative required
by `DuhamelSourceTimeC1On`. -/
noncomputable def windowK1Quadruple_interior_of_subtypeCont
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    {u₀ : intervalDomainPoint → ℝ} (u : ℝ → intervalDomainPoint → ℝ)
    {T c d : ℝ}
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hu₀_cont : Continuous u₀)
    {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hfix : ∀ s, 0 < s → s < T → ∀ x : ℝ,
      (hx : x ∈ Set.Icc (0 : ℝ) 1) →
        intervalDomainLift (u s) x =
          intervalGradientDuhamelMap p u₀ u s ⟨x, hx⟩)
    (hsrc0 : DuhamelSourceBddOn (patchedSource p u₀ u) T)
    {Msup : ℝ}
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ, 0 < σ → σ < T →
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagree : ∀ σ, 0 < σ → σ < T →
      Set.EqOn (intervalDomainLift (u σ))
        (fun x => ∑' n, bc σ n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1))
    (hpost : ∀ σ, 0 < σ → σ < T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (u σ) x)
    (hubt : ∀ σ, 0 < σ → σ < T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (u σ) x ≤ Msup)
    (hG1t : ∀ a' b', 0 < a' → b' < T → ∃ G1,
      ∀ σ ∈ Set.Icc a' b', ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (intervalDomainLift (u σ)) x| ≤ G1)
    (hG2t : ∀ a' b', 0 < a' → b' < T → ∃ G2,
      ∀ σ ∈ Set.Icc a' b', ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (deriv (intervalDomainLift (u σ))) x| ≤ G2)
    (hLc_ce : ∀ t, 0 < t → t < T →
      ∀ s, 0 < s → s ≤ t →
        Continuous (intervalDomainConstExtend (intervalLogisticSource p (u s))))
    (hc : 0 < c) (_hcd : c ≤ d) (hdT : d < T) :
    WindowK1Quadruple p u c d := by
  classical
  obtain ⟨hderiv_int, hadotcont_int, hMdot_int⟩ :=
    ShenWork.Paper2.PicardLimitK1Weak.k1_quadruple_weak_of_subtypeCont
      hχ0 u hα ha hb hu₀_cont hu₀_bound hfix hsrc0 bc hbsum hagree
      hpost hubt hG1t hG2t hLc_ce
  let hMdot_exists := hMdot_int c d hc hdT
  let Mdot := Classical.choose hMdot_exists
  have hMdot := Classical.choose_spec hMdot_exists
  refine
    { adot := ShenWork.Paper2.PicardLimitK1.adottOf p u
      hderiv := ?_
      hadotcont := ?_
      Mdot := Mdot
      hMdot := hMdot }
  · intro σ hσ k
    have hσ0 : 0 < σ := lt_of_lt_of_le hc hσ.1
    have hσT : σ < T := lt_of_le_of_lt hσ.2 hdT
    simpa [sourceCoeff] using
      (hderiv_int σ hσ0 hσT k).hasDerivWithinAt
  · intro k
    exact (hadotcont_int k).mono (fun σ hσ =>
      ⟨lt_of_lt_of_le hc hσ.1, lt_of_le_of_lt hσ.2 hdT⟩)

/-- Compose a positive-window K1 quadruple with the committed representation
adapter to obtain the closed-window source package. -/
noncomputable def limitSource_timeC1On_of_windowK1
    (p : CM2Params)
    (w : ℝ → intervalDomainPoint → ℝ)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    {lo hi M G1 G2 : ℝ}
    (hlohi : lo ≤ hi)
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ ∈ Set.Icc lo hi,
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagree : ∀ σ ∈ Set.Icc lo hi,
      Set.EqOn (intervalDomainLift (w σ))
        (fun x => ∑' n, bc σ n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1))
    (hpos : ∀ σ ∈ Set.Icc lo hi,
      ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (w σ) x)
    (hub : ∀ σ ∈ Set.Icc lo hi,
      ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (w σ) x ≤ M)
    (hG1 : ∀ σ ∈ Set.Icc lo hi,
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (intervalDomainLift (w σ)) x| ≤ G1)
    (hG2 : ∀ σ ∈ Set.Icc lo hi,
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (deriv (intervalDomainLift (w σ))) x| ≤ G2)
    (K1 : WindowK1Quadruple p w lo hi) :
    DuhamelSourceTimeC1On
      (fun s k => cosineCoeffs (logisticLifted p (w s)) k) lo hi :=
  limitSource_duhamelSourceTimeC1On_of_representation
    p w hα ha hb hlohi bc hbsum hagree hpos hub hG1 hG2
    K1.adot (by simpa [sourceCoeff] using K1.hderiv)
    K1.hadotcont K1.hMdot

/-- The strict-interior producer composed directly with the `On` adapter. -/
noncomputable def limitSource_timeC1On_interior_of_subtypeCont
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    {u₀ : intervalDomainPoint → ℝ} (u : ℝ → intervalDomainPoint → ℝ)
    {T c d M G1 G2 : ℝ}
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hu₀_cont : Continuous u₀)
    {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hfix : ∀ s, 0 < s → s < T → ∀ x : ℝ,
      (hx : x ∈ Set.Icc (0 : ℝ) 1) →
        intervalDomainLift (u s) x =
          intervalGradientDuhamelMap p u₀ u s ⟨x, hx⟩)
    (hsrc0 : DuhamelSourceBddOn (patchedSource p u₀ u) T)
    (bc : ℝ → ℕ → ℝ)
    (hbsumT : ∀ σ, 0 < σ → σ < T →
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagreeT : ∀ σ, 0 < σ → σ < T →
      Set.EqOn (intervalDomainLift (u σ))
        (fun x => ∑' n, bc σ n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1))
    (hpost : ∀ σ, 0 < σ → σ < T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (u σ) x)
    (hubt : ∀ σ, 0 < σ → σ < T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (u σ) x ≤ M)
    (hG1t : ∀ a' b', 0 < a' → b' < T → ∃ G1',
      ∀ σ ∈ Set.Icc a' b', ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (intervalDomainLift (u σ)) x| ≤ G1')
    (hG2t : ∀ a' b', 0 < a' → b' < T → ∃ G2',
      ∀ σ ∈ Set.Icc a' b', ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (deriv (intervalDomainLift (u σ))) x| ≤ G2')
    (hLc_ce : ∀ t, 0 < t → t < T →
      ∀ s, 0 < s → s ≤ t →
        Continuous (intervalDomainConstExtend (intervalLogisticSource p (u s))))
    (hc : 0 < c) (hcd : c ≤ d) (hdT : d < T)
    (hG1 : ∀ σ ∈ Set.Icc c d, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (u σ)) x| ≤ G1)
    (hG2 : ∀ σ ∈ Set.Icc c d, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv (intervalDomainLift (u σ))) x| ≤ G2) :
    DuhamelSourceTimeC1On
      (fun s k => cosineCoeffs (logisticLifted p (u s)) k) c d :=
  let K1 := windowK1Quadruple_interior_of_subtypeCont hχ0 u hα ha hb
    hu₀_cont hu₀_bound hfix hsrc0 bc hbsumT hagreeT hpost hubt
    hG1t hG2t hLc_ce hc hcd hdT
  limitSource_timeC1On_of_windowK1 p u hα ha hb hcd bc
    (fun σ hσ => hbsumT σ (lt_of_lt_of_le hc hσ.1)
      (lt_of_le_of_lt hσ.2 hdT))
    (fun σ hσ => hagreeT σ (lt_of_lt_of_le hc hσ.1)
      (lt_of_le_of_lt hσ.2 hdT))
    (fun σ hσ => hpost σ (lt_of_lt_of_le hc hσ.1)
      (lt_of_le_of_lt hσ.2 hdT))
    (fun σ hσ => hubt σ (lt_of_lt_of_le hc hσ.1)
      (lt_of_le_of_lt hσ.2 hdT))
    hG1 hG2 K1

end ShenWork.IntervalDomainPositiveWindowK1On
