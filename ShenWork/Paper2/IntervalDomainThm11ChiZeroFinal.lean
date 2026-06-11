/-
  Paper 2 Theorem 1.1 (χ₀ = 0): legacy ledger-level final wiring.

  This file keeps the older `paper2_theorem_1_1_chiZero_final` interface, which
  still closes Theorem 1.1 from external `Hcore` and `hPLF` hypotheses.  It is
  separate from the tower/cone path:

      IntervalPicardTowerSupply.from_cone_construction

  That path is now unconditional: the former analytic-source `hsrc0` residual has
  been eliminated, with the bounded patched source package and positive-window
  `TimeC1On` source data produced in-tower from L0 + REC.

  In this legacy interface, `LimitRegularityInputsCore.hsrc0` is just the retained
  bounded patched-source field consumed by the restart route, not a `sorry`-stubbed
  analytic-source obligation.  The `hpde_u` field is supplied by the proved
  representation producer `hpde_u_chiZero`.
-/
import ShenWork.Paper2.IntervalDomainMildLocalChi0
import ShenWork.Paper2.IntervalDomainPdeUChiZero

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.IntervalGradientDuhamelMap (intervalGradientDuhamelMap logisticLifted)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)
open ShenWork.IntervalMildToClassical (mildChemicalConcentration)
open ShenWork.IntervalMildPicardRegularity (logisticSourceFun)
open ShenWork.IntervalMildTimeDerivContinuity (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.IntervalPicardLimitRestartWeak (DuhamelSourceL1ContOn)
open ShenWork.PDE (intervalNeumannResolverSourceCoeff)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalCosineInversion (reflCircle)
open ShenWork.Paper2
open ShenWork.Paper2.ConeQuantBridge
open ShenWork.Paper2.MildLocalChi0

noncomputable section

namespace ShenWork.Paper2.Thm11ChiZeroFinal

/-! ## The legacy core ledger -/

structure LimitRegularityInputsCore
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (D : GradientMildSolutionData p u₀) where
  -- structural regime parameters
  hα : 1 ≤ p.α
  ha : 0 ≤ p.a
  hb : 0 ≤ p.b
  -- H1 datum data
  hu₀_cont : Continuous u₀
  M₀ : ℝ
  hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀
  -- mild fixed-point (= D.hmild)
  hfix : ∀ t, 0 < t → t < D.T → ∀ x : ℝ, (hx : x ∈ Set.Icc (0:ℝ) 1) →
    intervalDomainLift (D.u t) x = intervalGradientDuhamelMap p u₀ D.u t ⟨x, hx⟩
  -- bounded patched source package; on the cone path this is produced in-tower
  hsrc0 : ShenWork.IntervalPicardLimitRestartBdd.DuhamelSourceBddOn
    (ShenWork.IntervalPicardLimitBddProducer.patchedSource p u₀ D.u) D.T
  -- K2 spatial slice bounds (per time slice)
  Msup : ℝ
  -- per-slice cosine representation (replaces the unsatisfiable global-`C²` field
  -- `hC2t`; see `IntervalDomainThm11ChiZeroCoreProvider` for the vacuity, and
  -- `IntervalDomainLimitSourceRepresentation` for how it feeds every consumer)
  bc : ℝ → ℕ → ℝ
  hbsum : ∀ σ, 0 < σ → σ < D.T → Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|)
  hagree : ∀ σ, 0 < σ → σ < D.T → Set.EqOn (intervalDomainLift (D.u σ))
    (fun x => ∑' n, bc σ n * cosineMode n x) (Set.Icc (0 : ℝ) 1)
  hpost : ∀ σ, 0 < σ → σ < D.T → ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (D.u σ) x
  hubt : ∀ σ, 0 < σ → σ < D.T → ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (D.u σ) x ≤ Msup
  -- K2 gradient/Hessian bounds, PER-COMPACT (the satisfiable form)
  hG1t : ∀ a' b', 0 < a' → b' < D.T → ∃ G1, ∀ σ ∈ Set.Icc a' b',
    ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (intervalDomainLift (D.u σ)) x| ≤ G1
  hG2t : ∀ a' b', 0 < a' → b' < D.T → ∃ G2, ∀ σ ∈ Set.Icc a' b',
    ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (deriv (intervalDomainLift (D.u σ))) x| ≤ G2
  hN0t : ∀ σ, 0 < σ → σ < D.T → deriv (intervalDomainLift (D.u σ)) 0 = 0
  hN1t : ∀ σ, 0 < σ → σ < D.T → deriv (intervalDomainLift (D.u σ)) 1 = 0
  -- K1 source-coefficient time-C¹ data (UNSHIFTED, localized to (0,T))
  adott : ℝ → ℕ → ℝ
  hderivt : ∀ σ, 0 < σ → σ < D.T → ∀ k, HasDerivAt
    (fun r => cosineCoeffs
      (logisticSourceFun p.a p.b p.α (intervalDomainLift (D.u r))) k)
    (adott σ k) σ
  hadotcontt : ∀ k, ContinuousOn (fun σ => adott σ k) (Set.Ioo 0 D.T)
  hMdott : ∀ a' b', 0 < a' → b' < D.T → ∃ Mdot, ∀ σ ∈ Set.Icc a' b',
    ∀ k, |adott σ k| ≤ Mdot
  -- H3 slice continuity
  hLc : ∀ t, 0 < t → t < D.T →
    ∀ s, 0 < s → s ≤ t → Continuous (intervalLogisticSource p (D.u s))
  -- ===== frontier fields supplied to the older ledger interface =====
  Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u
  -- per-`t₀` clamped resolver-source witness (retyped from the unsatisfiable global
  -- `DuhamelSourceTimeC1`; see `IntervalDomainMildLocalChi0.Hvsrc` field doc)
  Hvsrc : ∀ t₀, 0 < t₀ → t₀ < D.T →
    ∃ (aC : ℝ → ℕ → ℝ) (_ : DuhamelSourceTimeC1 aC) (W : Set ℝ),
      W ∈ 𝓝 t₀ ∧
      (∀ s ∈ W, ∀ k, aC s k = (intervalNeumannResolverSourceCoeff p (D.u s) k).re)
  Hvpos : ∀ t, 0 < t → t < D.T → ∀ x : intervalDomainPoint,
    0 < mildChemicalConcentration p D.u t x
  -- restart-representation data feeding the proved `hpde_u` producer
  -- (`IntervalDomainPdeUChiZero.hpde_u_of_representation`): the per-time-slice
  -- cosine representation, the source-is-reaction coefficient identity, and the
  -- spectral summabilities.  Strictly weaker than the `hpde_u` PDE conclusion,
  -- which the producer derives from it.
  hpdeData : ∀ t, 0 < t → t < D.T →
    ∃ (a₀ : ℕ → ℝ) (M : ℝ) (_ : 0 ≤ M) (_ : ∀ n, |a₀ n| ≤ M) (a : ℝ → ℕ → ℝ)
      (_ : DuhamelSourceTimeC1 a) (offset : ℝ) (_ : 0 < t - offset),
      (∀ᶠ s in 𝓝 t, ∀ y : intervalDomainPoint,
        D.u s y = ∑' n, localRestartCoeff a₀ a (s - offset) n * cosineMode n y.1) ∧
      (∀ n, a (t - offset) n
        = cosineCoeffs (logisticSourceFun p.a p.b p.α (intervalDomainLift (D.u t))) n) ∧
      Continuous (logisticSourceFun p.a p.b p.α (intervalDomainLift (D.u t))) ∧
      Summable (fun n : ℤ => fourierCoeff
        (reflCircle (logisticSourceFun p.a p.b p.α (intervalDomainLift (D.u t)))) n) ∧
      Summable (fun n => unitIntervalCosineEigenvalue n
        * |localRestartCoeff a₀ a (t - offset) n|) ∧
      (∀ x : intervalDomainPoint, x.1 ∈ Set.Ioo (0:ℝ) 1 →
        Summable (fun n => a (t - offset) n * cosineMode n x.1) ∧
        Summable (fun n => unitIntervalCosineEigenvalue n
          * localRestartCoeff a₀ a (t - offset) n * cosineMode n x.1))

/-! ## The proved PDE producer used by the legacy ledger -/

/-- **Spectral→pointwise PDE identity for `u`.**
For χ₀ = 0 the chemotaxis term drops, so this is the heat/logistic
pointwise identity `u_t = Δu + u(a − b u^α)` on the interior.  It is
discharged via the proved producer
`IntervalDomainPdeUChiZero.hpde_u_of_representation` (dd1051b), fed the
restart-representation data carried by `LimitRegularityInputsCore.hpdeData`. -/
theorem hpde_u_chiZero
    {p : CM2Params} (hχ0 : p.χ₀ = 0) {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (C : LimitRegularityInputsCore p u₀ D) :
    ∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α) := by
  intro t x ht htT hx
  obtain ⟨a₀, M, hM, ha₀, a, src, offset, hoff, hrep, hsrc_coeff, hcont,
    hsum_fourier, hsum_b, hsumx⟩ := C.hpdeData t ht htT
  obtain ⟨hsum_src, hsum_lb⟩ := hsumx x hx
  exact IntervalDomainPdeUChiZero.hpde_u_of_representation p hχ0 hM ha₀ src hoff
    hrep hsrc_coeff hcont hsum_fourier hsum_b hx hsum_src hsum_lb

/-! ## Reassembling the full ledger -/

/-- **Build the full `LimitRegularityInputs` from the legacy core.**
Every field is forwarded from the core except `hpde_u`, which is produced
from the core's restart-representation data by `hpde_u_chiZero`. -/
def limitRegularityInputs_of_core
    {p : CM2Params} (hχ0 : p.χ₀ = 0) {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (C : LimitRegularityInputsCore p u₀ D) :
    MildLocalChi0.LimitRegularityInputs p u₀ D where
  hα := C.hα
  ha := C.ha
  hb := C.hb
  hu₀_cont := C.hu₀_cont
  M₀ := C.M₀
  hu₀_bound := C.hu₀_bound
  hfix := C.hfix
  hsrc0 := C.hsrc0
  Msup := C.Msup
  bc := C.bc
  hbsum := C.hbsum
  hagree := C.hagree
  hpost := C.hpost
  hubt := C.hubt
  hG1t := C.hG1t
  hG2t := C.hG2t
  hN0t := C.hN0t
  hN1t := C.hN1t
  adott := C.adott
  hderivt := C.hderivt
  hadotcontt := C.hadotcontt
  hMdott := C.hMdott
  hLc := C.hLc
  hpde_u := hpde_u_chiZero hχ0 C
  Hu := C.Hu
  Hvsrc := C.Hvsrc
  Hvpos := C.Hvpos

/-! ## The final theorem -/

/-- **Paper 2 Theorem 1.1 (χ₀ = 0), final wiring.**

This older theorem closes Theorem 1.1 (χ₀ = 0) from exactly:
  * `Hcore` — the per-datum proved-ledger remainder
    `LimitRegularityInputsCore` (the M-line images: K1/K2 bounds + the
    landed Hu/Hvsrc/Hvpos producers), and
  * `hPLF` — `PicardLimitRestartFrontier p` (the shared quantitative-side
    provider),
with `hpde_u` supplied internally through `hpde_u_chiZero`.

The unconditional χ₀ = 0 theorem is now the separate cone/tower entry point
`IntervalPicardTowerSupply.from_cone_construction`, where the old analytic-source
package is produced in-tower rather than assumed. -/
theorem paper2_theorem_1_1_chiZero_final
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p)
    (Hcore : ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
      ∀ D : GradientMildSolutionData p u₀,
        LimitRegularityInputsCore p u₀ D) :
    Theorem_1_1 intervalDomain p :=
  MildLocalChi0.paper2_theorem_1_1_chiZero_of_inputs
    p hχ0 ha hb hα_ge hγ_ge_one hPLF
    (fun u₀ hu₀ D _hDu => limitRegularityInputs_of_core hχ0 (Hcore u₀ hu₀ D))

end ShenWork.Paper2.Thm11ChiZeroFinal
