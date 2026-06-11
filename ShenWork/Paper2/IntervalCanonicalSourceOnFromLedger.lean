import ShenWork.Paper2.IntervalResolverSpectralAgreementFromK1
import ShenWork.Paper2.IntervalDomainPositiveWindowK1OnEndpoint

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalDomain (intervalDomainConstExtend)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
open ShenWork.IntervalGradientDuhamelMap (intervalGradientDuhamelMap logisticLifted)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalPicardLimitRestartBdd (DuhamelSourceBddOn)
open ShenWork.IntervalPicardLimitBddProducer (patchedSource)
open ShenWork.IntervalDuhamelSourceTimeC1On (DuhamelSourceTimeC1On)
open ShenWork.IntervalResolverTimeRegularity (ResolverHasSpectralAgreement)
open ShenWork.Paper2.ResolverSpectralAgreementFromK1
  (resolverHasSpectralAgreement_of_ledger_of_subtypeCont)
open ShenWork.IntervalDomainPositiveWindowK1OnEndpoint
  (limitSource_timeC1On_endpoint_of_subtypeCont)

noncomputable section

namespace ShenWork.Paper2.CanonicalSourceOnFromLedger

/-- The non-global ledger data from which the canonical source is produced on
positive closed windows. -/
structure CanonicalSourceLedger
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) (U : ℝ) where
  hfix : ∀ s, 0 < s → s < U → ∀ x : ℝ,
    (hx : x ∈ Set.Icc (0 : ℝ) 1) →
      intervalDomainLift (u s) x =
        intervalGradientDuhamelMap p u₀ u s ⟨x, hx⟩
  hsrc0 : DuhamelSourceBddOn (patchedSource p u₀ u) U
  Msup : ℝ
  bc : ℝ → ℕ → ℝ
  hbsum : ∀ σ, 0 < σ → σ < U →
    Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|)
  hagree : ∀ σ, 0 < σ → σ < U →
    Set.EqOn (intervalDomainLift (u σ))
      (fun x => ∑' n, bc σ n * cosineMode n x)
      (Set.Icc (0 : ℝ) 1)
  hpost : ∀ σ, 0 < σ → σ < U →
    ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (u σ) x
  hubt : ∀ σ, 0 < σ → σ < U →
    ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (u σ) x ≤ Msup
  hG1t : ∀ a' b', 0 < a' → b' < U → ∃ G1,
    ∀ σ ∈ Set.Icc a' b', ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (u σ)) x| ≤ G1
  hG2t : ∀ a' b', 0 < a' → b' < U → ∃ G2,
    ∀ σ ∈ Set.Icc a' b', ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv (intervalDomainLift (u σ))) x| ≤ G2
  hLc_ce : ∀ t, 0 < t → t < U →
    ∀ s, 0 < s → s ≤ t →
      Continuous (intervalDomainConstExtend (intervalLogisticSource p (u s)))

/-- A ledger available beyond the tower horizon.  This is the tower-level form of
the strict larger-horizon endpoint fact. -/
structure CanonicalSourceLedgerBeyond
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) (T : ℝ) where
  U : ℝ
  hTU : T < U
  ledger : CanonicalSourceLedger p u₀ u U

/-- Restrict a bounded-source package from a larger horizon to a smaller one. -/
def DuhamelSourceBddOn.restrict_horizon {a : ℝ → ℕ → ℝ} {T U : ℝ}
    (src : DuhamelSourceBddOn a U) (hTU : T ≤ U) :
    DuhamelSourceBddOn a T where
  M := src.M
  hM_nonneg := src.hM_nonneg
  hM := by
    intro s hs hsT k
    exact src.hM s hs (le_trans hsT hTU) k
  hcont := by
    intro k
    exact (src.hcont k).mono (Set.Icc_subset_Icc le_rfl hTU)
  env := src.env
  henv_summable := by
    intro a' ha' ha'T
    exact src.henv_summable a' ha' (le_trans ha'T hTU)
  henv_bound := by
    intro a' ha' s has hsT k
    exact src.henv_bound a' ha' s has (le_trans hsT hTU) k

/-- Compose the `(0,U)` ledger into the canonical source `TimeC1On` package on
`[c,T]`.

The proof first produces `ResolverHasSpectralAgreement U u` from the RSA ledger,
then restricts the ledger to the endpoint theorem's `T` horizon and supplies the
closed-window facts using `c ≤ σ ≤ T < U`. -/
noncomputable def canonicalSource_duhamelSourceTimeC1On_of_ledger
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    {u₀ : intervalDomainPoint → ℝ} (u : ℝ → intervalDomainPoint → ℝ)
    {U c T : ℝ}
    (hc : 0 < c) (hcT : c < T) (hTU : T < U)
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
    DuhamelSourceTimeC1On
      (fun s k => cosineCoeffs (logisticLifted p (u s)) k) c T := by
  classical
  have H : ResolverHasSpectralAgreement U u :=
    resolverHasSpectralAgreement_of_ledger_of_subtypeCont
      hχ0 u hα ha hb hu₀_cont hu₀_bound hfix hsrc0 bc hbsum
      hagree hpost hubt hG1t hG2t hLc_ce
  let hsrc0T : DuhamelSourceBddOn (patchedSource p u₀ u) T :=
    DuhamelSourceBddOn.restrict_horizon hsrc0 hTU.le
  have hfixT : ∀ s, 0 < s → s < T → ∀ x : ℝ,
      (hx : x ∈ Set.Icc (0 : ℝ) 1) →
        intervalDomainLift (u s) x =
          intervalGradientDuhamelMap p u₀ u s ⟨x, hx⟩ :=
    fun s hs0 hsT x hx => hfix s hs0 (lt_trans hsT hTU) x hx
  have hbsumT : ∀ σ, 0 < σ → σ < T →
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|) :=
    fun σ hσ0 hσT => hbsum σ hσ0 (lt_trans hσT hTU)
  have hagreeT : ∀ σ, 0 < σ → σ < T →
      Set.EqOn (intervalDomainLift (u σ))
        (fun x => ∑' n, bc σ n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1) :=
    fun σ hσ0 hσT => hagree σ hσ0 (lt_trans hσT hTU)
  have hpostT : ∀ σ, 0 < σ → σ < T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (u σ) x :=
    fun σ hσ0 hσT => hpost σ hσ0 (lt_trans hσT hTU)
  have hubtT : ∀ σ, 0 < σ → σ < T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (u σ) x ≤ Msup :=
    fun σ hσ0 hσT => hubt σ hσ0 (lt_trans hσT hTU)
  have hG1tT : ∀ a' b', 0 < a' → b' < T → ∃ G1,
      ∀ σ ∈ Set.Icc a' b', ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (intervalDomainLift (u σ)) x| ≤ G1 :=
    fun a' b' ha' hb'T => hG1t a' b' ha' (lt_trans hb'T hTU)
  have hG2tT : ∀ a' b', 0 < a' → b' < T → ∃ G2,
      ∀ σ ∈ Set.Icc a' b', ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (deriv (intervalDomainLift (u σ))) x| ≤ G2 :=
    fun a' b' ha' hb'T => hG2t a' b' ha' (lt_trans hb'T hTU)
  have hLc_ceT : ∀ t, 0 < t → t < T →
      ∀ s, 0 < s → s ≤ t →
        Continuous (intervalDomainConstExtend (intervalLogisticSource p (u s))) :=
    fun t ht0 htT s hs0 hst => hLc_ce t ht0 (lt_trans htT hTU) s hs0 hst
  have hbsumC : ∀ σ ∈ Set.Icc c T,
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|) := by
    intro σ hσ
    exact hbsum σ (lt_of_lt_of_le hc hσ.1) (lt_of_le_of_lt hσ.2 hTU)
  have hagreeC : ∀ σ ∈ Set.Icc c T,
      Set.EqOn (intervalDomainLift (u σ))
        (fun x => ∑' n, bc σ n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1) := by
    intro σ hσ
    exact hagree σ (lt_of_lt_of_le hc hσ.1) (lt_of_le_of_lt hσ.2 hTU)
  have hposC : ∀ σ ∈ Set.Icc c T,
      ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (u σ) x := by
    intro σ hσ
    exact hpost σ (lt_of_lt_of_le hc hσ.1) (lt_of_le_of_lt hσ.2 hTU)
  have hubC : ∀ σ ∈ Set.Icc c T,
      ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (u σ) x ≤ Msup := by
    intro σ hσ
    exact hubt σ (lt_of_lt_of_le hc hσ.1) (lt_of_le_of_lt hσ.2 hTU)
  let G1C : ℝ := Classical.choose (hG1t c T hc hTU)
  have hG1C : ∀ σ ∈ Set.Icc c T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (u σ)) x| ≤ G1C :=
    Classical.choose_spec (hG1t c T hc hTU)
  let G2C : ℝ := Classical.choose (hG2t c T hc hTU)
  have hG2C : ∀ σ ∈ Set.Icc c T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv (intervalDomainLift (u σ))) x| ≤ G2C :=
    Classical.choose_spec (hG2t c T hc hTU)
  exact
    limitSource_timeC1On_endpoint_of_subtypeCont
      (p := p) (u₀ := u₀) (u := u) (U := U) (T := T) (c := c)
      (M := Msup) (G1 := G1C) (G2 := G2C)
      hχ0 H hα ha hb hu₀_cont hu₀_bound hfixT hsrc0T bc
      hbsumT hagreeT hpostT hubtT hG1tT hG2tT hLc_ceT
      hc hcT hTU hbsumC hagreeC hposC hubC hG1C hG2C

/-- Build the canonical source `TimeC1On` package on a positive subwindow from a
ledger. -/
noncomputable def CanonicalSourceLedger.timeC1On
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ} {U c T : ℝ}
    (L : CanonicalSourceLedger p u₀ u U)
    (hχ0 : p.χ₀ = 0)
    (hc : 0 < c) (hcT : c < T) (hTU : T < U)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hu₀_cont : Continuous u₀)
    {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀) :
    DuhamelSourceTimeC1On
      (fun s k => cosineCoeffs (logisticLifted p (u s)) k) c T :=
  canonicalSource_duhamelSourceTimeC1On_of_ledger
    hχ0 u hc hcT hTU hα ha hb hu₀_cont hu₀_bound
    L.hfix L.hsrc0 L.bc L.hbsum L.hagree L.hpost L.hubt
    L.hG1t L.hG2t L.hLc_ce

/-- Restrict the bounded source part of a beyond-horizon ledger to the tower
horizon. -/
def CanonicalSourceLedgerBeyond.bddOnHorizon
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (L : CanonicalSourceLedgerBeyond p u₀ u T) :
    DuhamelSourceBddOn (patchedSource p u₀ u) T :=
  DuhamelSourceBddOn.restrict_horizon L.ledger.hsrc0 L.hTU.le

/-- Build the canonical source package on a positive subwindow of the tower
horizon. -/
noncomputable def CanonicalSourceLedgerBeyond.timeC1On
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ} {Ttop c T : ℝ}
    (L : CanonicalSourceLedgerBeyond p u₀ u Ttop)
    (hχ0 : p.χ₀ = 0)
    (hc : 0 < c) (hcT : c < T) (hTT : T ≤ Ttop)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hu₀_cont : Continuous u₀)
    {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀) :
    DuhamelSourceTimeC1On
      (fun s k => cosineCoeffs (logisticLifted p (u s)) k) c T :=
  L.ledger.timeC1On hχ0 hc hcT (lt_of_le_of_lt hTT L.hTU)
    hα ha hb hu₀_cont hu₀_bound

/-- Build the shifted source package on `[0, σ/2]` from a larger-horizon ledger. -/
noncomputable def CanonicalSourceLedgerBeyond.shiftedTimeC1On
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ} {T σ : ℝ}
    (L : CanonicalSourceLedgerBeyond p u₀ u T)
    (hχ0 : p.χ₀ = 0)
    (hσ : 0 < σ) (hσT : σ ≤ T)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hu₀_cont : Continuous u₀)
    {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀) :
    DuhamelSourceTimeC1On
      (fun s k => cosineCoeffs (logisticLifted p (u (σ / 2 + s))) k)
      0 (σ / 2) := by
  have hhalf : 0 < σ / 2 := by positivity
  have hhalfσ : σ / 2 < σ := by linarith
  have hphys : DuhamelSourceTimeC1On
      (fun s k => cosineCoeffs (logisticLifted p (u s)) k) (σ / 2) σ :=
    L.timeC1On hχ0 hhalf hhalfσ hσT hα ha hb hu₀_cont hu₀_bound
  have hsum : σ / 2 + σ / 2 = σ := by ring
  have hphys' : DuhamelSourceTimeC1On
      (fun s k => cosineCoeffs (logisticLifted p (u s)) k)
      (σ / 2) (σ / 2 + σ / 2) := by
    rw [hsum]
    exact hphys
  simpa [add_comm] using
    ShenWork.IntervalDuhamelSourceTimeC1On.DuhamelSourceTimeC1On.shift_zero
      (offset := σ / 2) (W := σ / 2) hphys'

end ShenWork.Paper2.CanonicalSourceOnFromLedger
