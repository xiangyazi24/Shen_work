import ShenWork.PDE.IntervalChemDivFluxTimeBridge
import ShenWork.PDE.IntervalSourceDecayQuantitative
import ShenWork.Paper2.IntervalMildPicardRegularity

open ShenWork.IntervalDomain
open ShenWork.IntervalDuhamelClosedC2
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalSourceDecayQuantitative
open ShenWork.IntervalMildPicardRegularity
  (cosineCoeffs_abs_le_of_continuous_bounded)
open ShenWork.PDE.IntervalMildSourceDecayHelper
open Set Filter Topology

noncomputable section

namespace ShenWork.IntervalCoupledRegularityBootstrap

/-- **Per-slice weak-`H²ₙ` certificate for the chem-div source.**

From the source slice being `C²` on `[0,1]` with homogeneous Neumann endpoint
data, the committed `intervalWeakH2Neumann_of_contDiffOn` packager yields the
weak `H²_N` certificate whose weak second derivative is `deriv (deriv f)`. -/
def chemDivSource_weakH2_of_spatialC2
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s : ℝ}
    (hC2 : ContDiffOn ℝ 2 (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1))
    (ht0 : Tendsto (deriv (coupledChemDivSourceLift p u s))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0))
    (ht1 : Tendsto (deriv (coupledChemDivSourceLift p u s))
      (nhdsWithin (1 : ℝ) (Iio 1)) (nhds 0))
    (hbc0 : deriv (coupledChemDivSourceLift p u s) 0 = 0)
    (hbc1 : deriv (coupledChemDivSourceLift p u s) 1 = 0) :
    IntervalWeakH2Neumann (coupledChemDivSourceLift p u s) :=
  intervalWeakH2Neumann_of_contDiffOn hC2 ht0 ht1 hbc0 hbc1

/-- **Quadratic source-decay discharge.**  Given, uniformly in `s ≥ 0`, the
per-slice weak `H²ₙ` certificate and a uniform `L¹` bound `B` on its weak second
derivative, the quadratic coefficient decay holds with `Cchem = 2 * max B Msup`
(any `Msup ≥ 0`). -/
theorem coupledChemDivSource_quadraticDecay_of_uniformH2
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (B Msup : ℝ)
    (hH2 : ∀ s, 0 ≤ s →
      IntervalWeakH2Neumann (coupledChemDivSourceLift p u s))
    (hBbound : ∀ s (hs : 0 ≤ s),
      (∫ x in (0 : ℝ)..1, |(hH2 s hs).secondDeriv x|) ≤ B) :
    ∀ s, 0 ≤ s → ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs (coupledChemDivSourceLift p u s) k|
        ≤ 2 * max B Msup / ((k : ℝ) * Real.pi) ^ 2 := by
  intro s hs k hk
  have hdec := intervalWeakH2Neumann_cosineCoeff_quadratic_decay_of_bound
    (hH2 s hs) (hBbound s hs) k hk
  have hden : 0 < ((k : ℝ) * Real.pi) ^ 2 := by
    have : (0 : ℝ) < (k : ℝ) :=
      by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hk
    positivity
  refine le_trans hdec ?_
  gcongr
  exact le_max_left _ _

/-- **Zeroth source-coefficient discharge.**  From a uniform continuity + sup
bound `Msup` on the chem-div source slice, the zeroth coefficient is bounded by
`Cchem = 2 * max B Msup` (any `B ≥ 0`). -/
theorem coupledChemDivSource_zeroCoeff_of_uniformSup
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (B Msup : ℝ) (hMsup : 0 ≤ Msup)
    (hcont : ∀ s, 0 ≤ s →
      ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1))
    (hsup : ∀ s, 0 ≤ s → ∀ x ∈ Icc (0 : ℝ) 1,
      |coupledChemDivSourceLift p u s x| ≤ Msup) :
    ∀ s, 0 ≤ s →
      |cosineCoeffs (coupledChemDivSourceLift p u s) 0| ≤ 2 * max B Msup := by
  intro s hs
  have hzero := cosineCoeffs_abs_le_of_continuous_bounded (hcont s hs) hMsup
    (hsup s hs) 0
  refine le_trans hzero ?_
  gcongr
  exact le_max_right _ _

end ShenWork.IntervalCoupledRegularityBootstrap
