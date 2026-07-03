/-
  ShenWork/Paper2/IntervalDomainTheorem11CorePath.lean

  **EWA-free path from uniform `CoupledDuhamelReducedClassicalCore` to `Theorem_1_1`.**

  The existing chain uses `ChiNegDatumUniformConstructionStrong`, which requires
  `∃ u_star : EWA δ 1, Core p δ u₀ (realSlice u_star)` — the fixed point must
  live in the EWA type at the UNIFORM lifespan δ. This creates a type mismatch
  when the clean FP produces `u_star : EWA T 1` for a per-datum T ≠ δ.

  This file defines `ChiNegDatumUniformCore` — the same statement with
  `∃ u : ℝ → Point → ℝ, Core p δ u₀ u` (no EWA type) — and proves it implies
  Theorem_1_1 via the SAME regularity bootstrap chain. The downstream proof is
  identical because `ppid_of_strong` only uses `realSlice u_star` as a plain
  function anyway.

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainTheorem11StrongPath
import ShenWork.PDE.IntervalCoupledClassicalCoreDischarge

open ShenWork.IntervalDomain (intervalDomainPoint intervalDomain)
open ShenWork.Paper2
open ShenWork.Paper2.StrongPath (chiNeg_theorem_1_1_ppid ChiNegDatumUniformConstructionPPID)
open ShenWork.IntervalCoupledRegularityBootstrap (CoupledDuhamelReducedClassicalCore)

noncomputable section

namespace ShenWork

/-- **EWA-free uniform core construction.**

Same as `ChiNegDatumUniformConstructionStrong` but the solution `u` is a plain
function, not wrapped in `EWA δ 1`. This avoids the type mismatch when the
per-datum fixed point lives in `EWA T 1` for a different T. -/
def ChiNegDatumUniformCore (p : CM2Params) : Prop :=
  ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
    ∀ {u₀ : intervalDomainPoint → ℝ},
      PaperPositiveInitialDatum intervalDomain u₀ →
      (∀ x, |u₀ x| ≤ M) →
        ∃ u : ℝ → intervalDomainPoint → ℝ,
          CoupledDuhamelReducedClassicalCore p δ u₀ u

theorem ppid_of_uniformCore
    (hU : ChiNegDatumUniformCore p) :
    ChiNegDatumUniformConstructionPPID p := by
  intro M hM
  obtain ⟨δ, hδ, hbody⟩ := hU M hM
  refine ⟨δ, hδ, fun {u0} hu₀ hbd => ?_⟩
  obtain ⟨u, C⟩ := hbody hu₀ hbd
  have hreg :=
    ShenWork.IntervalCoupledRegularityBootstrap.regularityBootstrap_of_coupledDuhamel_reducedClassicalCore
      p C
  obtain ⟨v, hpos, hvnn, hpde_u, hpde_v, hbc, hclassreg, htrace⟩ := hreg
  exact ⟨u, v,
    IsPaper2ClassicalSolution.of_components hδ hclassreg hpos hvnn hpde_u hpde_v hbc,
    htrace⟩

theorem chiNeg_theorem_1_1_of_uniformCore (p : CM2Params) (hchi : p.χ₀ < 0)
    (ha : 0 < p.a) (hb : 0 < p.b) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hU : ChiNegDatumUniformCore p) :
    Theorem_1_1 intervalDomain p :=
  chiNeg_theorem_1_1_ppid p hchi ha hb hα hγ (ppid_of_uniformCore hU)

/-- **Strong implies UniformCore** (trivially, by forgetting the EWA type). -/
theorem uniformCore_of_strong
    (hS : ShenWork.EWA.ChiNegDatumUniformConstructionStrong p) :
    ChiNegDatumUniformCore p := by
  intro M hM
  obtain ⟨δ, hδ, hbody⟩ := hS M hM
  exact ⟨δ, hδ, fun hu₀ hbd => let ⟨u_star, C⟩ := hbody hu₀ hbd; ⟨_, C⟩⟩

end ShenWork

#print axioms ShenWork.chiNeg_theorem_1_1_of_uniformCore
