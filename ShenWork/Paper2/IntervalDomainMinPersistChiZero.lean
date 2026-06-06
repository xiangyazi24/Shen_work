/-
  Phase C (MinPersistence): **unconditional `ClassicalMinPersistence` for χ₀ = 0.**

  The χ₀ = 0 specialisation of `classicalMinPersistence_of_boundary`: the only
  remaining hypothesis there was the boundary min-point bound `hbdry`, now
  discharged for both endpoints by `hbdry_left_chi0` / `hbdry_right_chi0`.

  Rather than route through `classicalMinPersistence_of_boundary` (whose `hbdry`
  field is stated for a generic `t₁` and so cannot see `0 < t₁`), we inline the
  assembly: inside `minPersist_existsC_uniform` the time `t₁` is FIXED with
  `0 < t₁` in scope, so every `s ∈ Ico (t₁/2) T` has `0 < s` — exactly the
  interior-time hypothesis the endpoint bounds need.

  This closes general-trace MinPersistence in the flux-free regime
  unconditionally, hence the threshold-route `hQuant` for χ₀ = 0.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainMinPersistUniform
import ShenWork.Paper2.IntervalDomainHSupNorm
import ShenWork.Paper2.IntervalDomainPIDBound
import ShenWork.Paper2.IntervalDomainQuantFromThreshold
import ShenWork.Paper2.IntervalDomainBoundaryHbound
import ShenWork.Paper2.IntervalDomainBoundaryHboundRight

open ShenWork.IntervalDomain ShenWork.Paper2 Set Filter Topology

noncomputable section

namespace ShenWork.MinPersistenceAtoms

/-- **`ClassicalMinPersistence` for `χ₀ = 0`, unconditional.** -/
theorem classicalMinPersistence_chiZero
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hOverlap : GlueExtension.OverlapUniqueForPID p) :
    QuantFromThreshold.ClassicalMinPersistence p := by
  intro u₀ hu₀ δ t₁ ht₁ ht₁δ
  obtain ⟨M, hM, hbnd⟩ := pid_exists_bound hu₀
  refine minPersist_existsC_uniform (le_of_eq hχ0) hu₀ ht₁ ht₁δ
    (SupNormBridge.regimeBound_pos p hM).le hOverlap
    (fun hsol htr => hSupNorm_of_regime p (le_of_eq hχ0) ha hb hu₀ hM hbnd ht₁
      hsol.T_pos hsol htr) ?_
  -- The boundary min-point bound, both endpoints, χ₀ = 0.
  intro T u v hsol htr s hs ys _hys hys01 harg
  have hs0 : 0 < s := lt_of_lt_of_le (by linarith : (0:ℝ) < t₁ / 2) hs.1
  have hsT : s < T := hs.2
  have hMpos : (0:ℝ) ≤ SupNormBridge.regimeBound p M :=
    (SupNormBridge.regimeBound_pos p hM).le
  -- `u s x ≤ regimeBound p M` for every interior point (from the sup bound).
  have hsup := hSupNorm_of_regime p (le_of_eq hχ0) ha hb hu₀ hM hbnd ht₁
    hsol.T_pos hsol htr
  have hu_le : ∀ x : intervalDomainPoint, u s x ≤ SupNormBridge.regimeBound p M := by
    intro x
    have hb := hsup s hs x.1
    have hlift : intervalDomainLift (u s) x.1 = u s x := by
      simp only [intervalDomainLift]; exact dif_pos x.2
    rw [hlift] at hb
    exact (abs_le.mp hb).2
  rcases hys01 with h0 | h1
  · subst h0
    exact hbdry_left_chi0 hχ0 hsol hs0 hsT hMpos hu_le harg
  · subst h1
    exact hbdry_right_chi0 hχ0 hsol hs0 hsT hMpos hu_le harg

end ShenWork.MinPersistenceAtoms
