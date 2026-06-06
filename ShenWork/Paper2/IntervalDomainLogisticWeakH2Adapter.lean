/-
  Additive adapter (no shared-structure edits): build the logistic-source
  weak-H²/Neumann certificate from the **cosine representation**, bypassing the
  unsatisfiable "global C² of the 0-extension lift" requirement.

  The ledger's vacuity came from asking `ContDiff ℝ 2 (intervalDomainLift (D.u σ))`
  (global) — false for the 0-extension positive at the Neumann endpoints.  But the
  restart cosine representation already gives, on `[0,1]`,
    `intervalDomainLift w =ᴵᶜᶜ (x ↦ ∑ₙ bₙ cos(nπx))`,
  and the cosine series `cs(x) = ∑ₙ bₙ cos(nπx)` IS genuinely globally `C²`
  (`cosineCoeffSeries_contDiff_two`, from `∑ₙ λₙ|bₙ| < ∞`).  So `cs` is the honest
  global-`C²` witness (the role a clamp/extension was meant to play — and unlike a
  `max/min` clamp, `cs` is genuinely `C²`, not merely `C¹`).

  We feed `cs` to the EXISTING global-`C²` constructor
  `logisticSourceFun_intervalWeakH2Neumann`, then transfer the certificate to the
  lift via `[0,1]`-agreement (`IntervalWeakH2Neumann.congr_on_Icc`): the weak
  certificate depends on its function only through `[0,1]` (its sole use of `f` is
  the `∫₀¹ cos·f` cosine-coefficient integral), so agreement on `[0,1]` suffices.

  This mirrors the already-present power-source adapter
  `intervalWeakH2Neumann_of_eigenvalue_summable` (νu^γ) for the logistic source
  `u·(a − b·u^α)`.

  No `sorry`/`admit`/custom `axiom`/`native_decide`.
-/
import ShenWork.Paper2.IntervalMildPicardRegularity
import ShenWork.PDE.IntervalMildSourceDecayHelper
import ShenWork.PDE.IntervalDuhamelClosedC2

open Set Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.PDE.IntervalMildSourceDecayHelper (IntervalWeakH2Neumann)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalMildPicardRegularity
  (logisticSourceFun logisticSourceFun_intervalWeakH2Neumann)

noncomputable section

namespace ShenWork.IntervalDomainLogisticWeakH2Adapter

/-- **Weak-H²/Neumann certificate transfers across `[0,1]`-agreement.**  The
certificate uses its function `f` only through the `∫₀¹ cos·f` integral, so two
functions equal on `[0,1]` share it (with the SAME `secondDeriv`). -/
def _root_.ShenWork.PDE.IntervalMildSourceDecayHelper.IntervalWeakH2Neumann.congr_on_Icc
    {f g : ℝ → ℝ} (hf : IntervalWeakH2Neumann f)
    (hfg : ∀ x ∈ Set.Icc (0 : ℝ) 1, f x = g x) :
    IntervalWeakH2Neumann g where
  secondDeriv := hf.secondDeriv
  second_intervalIntegrable := hf.second_intervalIntegrable
  second_abs_integral_bound := hf.second_abs_integral_bound
  weak_cosine_laplacian := fun k => by
    have hint : (∫ x in (0 : ℝ)..1, Real.cos ((k : ℝ) * Real.pi * x) * g x)
        = ∫ x in (0 : ℝ)..1, Real.cos ((k : ℝ) * Real.pi * x) * f x := by
      refine intervalIntegral.integral_congr (fun x hx => ?_)
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      rw [hfg x hx]
    rw [hint]; exact hf.weak_cosine_laplacian k

/-- **Logistic-source weak-H²/Neumann certificate from the cosine representation.**

For a positive profile `w` whose lift agrees on `[0,1]` with an eigenvalue-summable
cosine series, the logistic source `logisticSourceFun a b α (lift w)` has the
weak-H²/Neumann certificate — built from the genuinely-`C²` cosine series, with NO
global-`C²` hypothesis on the (zero-extended) lift. -/
def logisticSource_intervalWeakH2Neumann_of_eigenvalue_summable
    {a b α : ℝ} {bc : ℕ → ℝ}
    (hbsum : Summable (fun n => unitIntervalCosineEigenvalue n * |bc n|))
    {w : intervalDomainPoint → ℝ}
    (hagree : Set.EqOn (intervalDomainLift w)
        (fun x => ∑' n, bc n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift w x) :
    IntervalWeakH2Neumann (logisticSourceFun a b α (intervalDomainLift w)) := by
  have hC2 : ContDiff ℝ 2 (fun x => ∑' n, bc n * cosineMode n x) :=
    ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_contDiff_two hbsum
  have hpos_cs : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < (fun x => ∑' n, bc n * cosineMode n x) x :=
    fun x hx => (hagree hx) ▸ hpos x hx
  have hd0 : deriv (fun x => ∑' n, bc n * cosineMode n x) 0 = 0 :=
    ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_deriv_at_zero hbsum
  have hd1 : deriv (fun x => ∑' n, bc n * cosineMode n x) 1 = 0 :=
    ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_deriv_at_one hbsum
  have hwH2 : IntervalWeakH2Neumann
      (logisticSourceFun a b α (fun x => ∑' n, bc n * cosineMode n x)) :=
    logisticSourceFun_intervalWeakH2Neumann hC2 hpos_cs hd0 hd1
  refine hwH2.congr_on_Icc (fun x hx => ?_)
  simp only [logisticSourceFun]
  rw [hagree hx]

/-- **Logistic-source cosine-coefficient quadratic decay from the representation.** -/
theorem logisticSource_cosineCoeff_quadratic_decay_of_representation
    {a b α : ℝ} {bc : ℕ → ℝ}
    (hbsum : Summable (fun n => unitIntervalCosineEigenvalue n * |bc n|))
    {w : intervalDomainPoint → ℝ}
    (hagree : Set.EqOn (intervalDomainLift w)
        (fun x => ∑' n, bc n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift w x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs (logisticSourceFun a b α (intervalDomainLift w)) k|
        ≤ C / ((k : ℝ) * Real.pi) ^ 2 :=
  ShenWork.PDE.IntervalMildSourceDecayHelper.intervalWeakH2Neumann_cosineCoeff_quadratic_decay
    (logisticSource_intervalWeakH2Neumann_of_eigenvalue_summable hbsum hagree hpos)

/-- **Representation-based logistic-source `DuhamelSourceTimeC1` producer.**

The additive, representation-fed analogue of
`logisticSource_duhamelSourceTimeC1`: it replaces the global-`C²` spatial data
`(hC2, hN0, hN1)` — which on the zero-extension lift is UNSATISFIABLE — by the
cosine representation `(hbsum, hagree, hpos)` per time slice, supplying the
weak-H²/Neumann certificate through
`logisticSource_intervalWeakH2Neumann_of_eigenvalue_summable`.  The coefficient
decay/zeroth-bound and K1 time-`C¹` data are carried unchanged.

This lets a ledger build the logistic source's `DuhamelSourceTimeC1` from data the
restart cosine representation genuinely supplies, with no global-`C²` hypothesis. -/
noncomputable def logisticSource_duhamelSourceTimeC1_of_representation
    {p : CM2Params} {w : ℝ → intervalDomainPoint → ℝ}
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ, Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagree : ∀ σ, Set.EqOn (intervalDomainLift (w σ))
        (fun x => ∑' n, bc σ n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    (hpos : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (w σ) x)
    {C : ℝ} (hC : 0 ≤ C)
    (hdecay : ∀ σ, 0 ≤ σ → ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs (logisticSourceFun p.a p.b p.α (intervalDomainLift (w σ))) k|
        ≤ C / ((k : ℝ) * Real.pi) ^ 2)
    (ha0 : ∀ σ, 0 ≤ σ →
      |cosineCoeffs (logisticSourceFun p.a p.b p.α (intervalDomainLift (w σ))) 0| ≤ C)
    {adot : ℝ → ℕ → ℝ}
    (hderiv : ∀ σ n, HasDerivAt
      (fun r => cosineCoeffs
        (logisticSourceFun p.a p.b p.α (intervalDomainLift (w r))) n) (adot σ n) σ)
    (hadotcont : ∀ n, Continuous (fun σ => adot σ n))
    {Mdot : ℝ}
    (hMdot : ∀ σ, 0 ≤ σ → ∀ n, |adot σ n| ≤ Mdot) :
    DuhamelSourceTimeC1
      (fun σ n =>
        cosineCoeffs (logisticSourceFun p.a p.b p.α (intervalDomainLift (w σ))) n) :=
  ShenWork.IntervalSemigroupNeumann.duhamelSourceTimeC1_of_H2Neumann_timeC1
    (fun σ _hσ =>
      logisticSource_intervalWeakH2Neumann_of_eigenvalue_summable
        (hbsum σ) (hagree σ) (hpos σ))
    hC hdecay hderiv hadotcont hMdot ha0

end ShenWork.IntervalDomainLogisticWeakH2Adapter
