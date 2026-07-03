/-
  ShenWork/Wiener/EWA/SourceChiNegLocalExistence.lean

  **Per-datum local existence from EWA fixed point + regularity bootstrap.**

  Given a PPID datum with Wiener lifting data, produces a local-in-time
  classical solution `(u, v)` satisfying the coupled Keller-Segel system
  with initial trace `u(0) = u₀`.

  Chain:
    chiNeg_EWA_core_of_datum → CoupledDuhamelReducedClassicalCore
    → regularityBootstrap_of_coupledDuhamel_reducedClassicalCore
    → IsPaper2ClassicalSolution + InitialTrace

  This gives the `hlocal` half of `Theorem_1_1_intervalDomain_of_ppid_local_and_quant`.
  The `hQuant` half (uniform δ) additionally requires uniform Wiener norm bounds.

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.SourceChiNegPerDatumV6
import ShenWork.PDE.IntervalCoupledClassicalCoreDischarge

open Set Filter Topology
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)

noncomputable section

namespace ShenWork.EWA

theorem chiNeg_localExistence_of_wiener (p : CM2Params)
    (u₀ : ℝ → ℝ) (hu₀ : Continuous u₀)
    {δ₀ : ℝ} (hδ₀pos : 0 < δ₀) (hfloor₀ : ∀ y, δ₀ ≤ u₀ y)
    (hsumc : Summable (fun k => |cosineCoeffs u₀ k|))
    (hmem : MemW 1 (ofCosineCoeffs (cosineCoeffs u₀)))
    {Mu0 : ℝ} (hu0bd : ∀ n, |cosineCoeffs u₀ n| ≤ Mu0)
    (u₀p : intervalDomainPoint → ℝ)
    (hrecon : ∀ x : intervalDomainPoint,
      u₀p x = ∑' n, cosineCoeffs u₀ n * cosineMode n x.1)
    (hβpos : 0 < p.β) (hαnn : 0 ≤ p.α) (hμle1 : p.μ ≤ 1) :
    ∃ Tmax : ℝ, 0 < Tmax ∧ ∃ (u v : ℝ → intervalDomainPoint → ℝ),
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u₀p u := by
  obtain ⟨T, hTpos, u_star, hCore⟩ :=
    chiNeg_EWA_core_of_datum p u₀ hu₀ hδ₀pos hfloor₀ hsumc hmem hu0bd u₀p
      hrecon hβpos hαnn hμle1
  have hreg :=
    ShenWork.IntervalCoupledRegularityBootstrap.regularityBootstrap_of_coupledDuhamel_reducedClassicalCore
      p hCore
  obtain ⟨v, hpos, hvnn, hpde_u, hpde_v, hbc, hclassreg, htrace⟩ := hreg
  exact ⟨T, hTpos, realSlice u_star, v,
    IsPaper2ClassicalSolution.of_components hTpos hclassreg hpos hvnn hpde_u hpde_v hbc,
    htrace⟩

end ShenWork.EWA

#print axioms ShenWork.EWA.chiNeg_localExistence_of_wiener
