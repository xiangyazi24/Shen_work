/-
  Phase C (MinPersistence): `ClassicalMinPersistence` from the boundary bound.

  The literal `QuantFromThreshold.ClassicalMinPersistence p` predicate, reduced
  to its SINGLE remaining input — the boundary min-point bound `hbdry`
  (`ys ∈ {0,1}`).  Everything else is assembled from proved pieces:
    * `pid_exists_bound`     — the datum bound `M` (⇒ `M' := regimeBound p M`);
    * `hSupNorm_of_regime`   — the sup bound (Lemma 3.1);
    * `minPersist_existsC_uniform` — the Hamilton floor + cross-solution
                                     uniformity (overlap uniqueness);
  with `hOverlap` (`OverlapUniqueForPID`, proved in the regime) supplied.

  This isolates general-χ₀ `ClassicalMinPersistence` (hence the threshold-route
  general-χ₀ `hQuant`) to exactly the boundary chemDiv-continuity gap.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainMinPersistUniform
import ShenWork.Paper2.IntervalDomainHSupNorm
import ShenWork.Paper2.IntervalDomainPIDBound
import ShenWork.Paper2.IntervalDomainQuantFromThreshold

open ShenWork.IntervalDomain ShenWork.Paper2 Set Filter Topology

noncomputable section

namespace ShenWork.MinPersistenceAtoms

/-- **`ClassicalMinPersistence` from the boundary min-point bound.** -/
theorem classicalMinPersistence_of_boundary
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hOverlap : GlueExtension.OverlapUniqueForPID p)
    (hbdry : ∀ {u₀ : intervalDomainPoint → ℝ},
      PositiveInitialDatum intervalDomain u₀ →
      ∀ {M : ℝ}, 0 < M → (∀ x, |u₀ x| ≤ M) →
      ∀ {t₁ T : ℝ} {u v : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
        ∀ s ∈ Set.Ico (t₁/2) T, ∀ ys ∈ Set.Icc (0:ℝ) 1, ys = 0 ∨ ys = 1 →
          intervalDomainLift (u s) ys
              = sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1) →
            -(|p.χ₀| * fluxCoeffConst p.β (p.ν * (SupNormBridge.regimeBound p M) ^ p.γ)
                + p.b * (SupNormBridge.regimeBound p M) ^ p.α)
                * sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1)
              ≤ deriv (fun r => intervalDomainLift (u r) ys) s) :
    QuantFromThreshold.ClassicalMinPersistence p := by
  intro u₀ hu₀ δ t₁ ht₁ ht₁δ
  obtain ⟨M, hM, hbnd⟩ := pid_exists_bound hu₀
  exact minPersist_existsC_uniform hχ hu₀ ht₁ ht₁δ
    (SupNormBridge.regimeBound_pos p hM).le hOverlap
    (fun hsol htr => hSupNorm_of_regime p hχ ha hb hu₀ hM hbnd ht₁ hsol.T_pos hsol htr)
    (fun hsol htr => hbdry hu₀ hM hbnd hsol htr)

end ShenWork.MinPersistenceAtoms
