/-
  Phase C (MinPersistence): per-solution persistence, fully assembled.

  Combines `hbound_interior` (interior argmins, PROVED) with the boundary
  min-point bound (`hbdry`, the one remaining hard analytic input — chemDiv
  up-to-boundary continuity) and the regime sup bound (`hSupNorm`) into the
  full `hbound`, then feeds `solution_persist_exists_c` to obtain the
  per-solution persistence floor `∃ c>0, u ≥ c on [t₁,T)`.

  This isolates the project's remaining MinPersistence residual to exactly:
    * `hbdry` — the boundary (`ys ∈ {0,1}`) min-point bound, and
    * `hSupNorm` — the interior sup bound `|u| ≤ M'` (regimeBound, Lemma 3.1).
  Everything else (the Hamilton trick, interior min-point, positivity) is proved.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainHboundInterior
import ShenWork.Paper2.IntervalDomainPersistExistsC

open ShenWork.IntervalDomain ShenWork.Paper2 Set Filter Topology

noncomputable section

namespace ShenWork.MinPersistenceAtoms

/-- Full min-point bound for arbitrary sensitivity sign. -/
theorem hbound_full_allChi
    {p : CM2Params} {T t₁ M' : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht₁ : 0 < t₁) (ht₁T : t₁ < T) (hM' : 0 ≤ M')
    (hSupNorm : ∀ s ∈ Set.Ico (t₁/2) T, ∀ y,
      |intervalDomainLift (u s) y| ≤ M')
    (hbdry : ∀ s ∈ Set.Ico (t₁/2) T, ∀ ys ∈ Set.Icc (0:ℝ) 1, ys = 0 ∨ ys = 1 →
      intervalDomainLift (u s) ys
          = sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1) →
        -(|p.χ₀| * fluxCoeffConst p.β (p.ν * M' ^ p.γ) + p.b * M' ^ p.α)
            * sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1)
          ≤ deriv (fun r => intervalDomainLift (u r) ys) s) :
    ∀ s ∈ Set.Ico (t₁/2) T, ∀ ys ∈ Set.Icc (0:ℝ) 1,
      intervalDomainLift (u s) ys
          = sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1) →
        -(|p.χ₀| * fluxCoeffConst p.β (p.ν * M' ^ p.γ) + p.b * M' ^ p.α)
            * sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1)
          ≤ deriv (fun r => intervalDomainLift (u r) ys) s := by
  intro s hs ys hys_mem hargmin
  have hs0 : 0 < s := lt_of_lt_of_le (by linarith) hs.1
  have hsT : s < T := hs.2
  rcases eq_or_lt_of_le hys_mem.1 with hy0 | hy0
  · exact hbdry s hs ys hys_mem (Or.inl hy0.symm) hargmin
  · rcases eq_or_lt_of_le hys_mem.2 with hy1 | hy1
    · exact hbdry s hs ys hys_mem (Or.inr hy1) hargmin
    · exact hbound_interior_allChi hsol hs0 hsT hM' (hSupNorm s hs)
        ⟨hy0, hy1⟩ hargmin

/-- The full min-point bound `hbound` from the interior bound + the boundary
input + the sup bound, on the window `[t₁/2, T)`. -/
theorem hbound_full
    {p : CM2Params} {T t₁ M' : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hχ : p.χ₀ ≤ 0)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht₁ : 0 < t₁) (ht₁T : t₁ < T) (hM' : 0 ≤ M')
    (hSupNorm : ∀ s ∈ Set.Ico (t₁/2) T, ∀ y,
      |intervalDomainLift (u s) y| ≤ M')
    (hbdry : ∀ s ∈ Set.Ico (t₁/2) T, ∀ ys ∈ Set.Icc (0:ℝ) 1, ys = 0 ∨ ys = 1 →
      intervalDomainLift (u s) ys
          = sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1) →
        -(|p.χ₀| * fluxCoeffConst p.β (p.ν * M' ^ p.γ) + p.b * M' ^ p.α)
            * sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1)
          ≤ deriv (fun r => intervalDomainLift (u r) ys) s) :
    ∀ s ∈ Set.Ico (t₁/2) T, ∀ ys ∈ Set.Icc (0:ℝ) 1,
      intervalDomainLift (u s) ys
          = sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1) →
        -(|p.χ₀| * fluxCoeffConst p.β (p.ν * M' ^ p.γ) + p.b * M' ^ p.α)
            * sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1)
          ≤ deriv (fun r => intervalDomainLift (u r) ys) s := by
  intro s hs ys hys_mem hargmin
  have hs0 : 0 < s := lt_of_lt_of_le (by linarith) hs.1
  have hsT : s < T := hs.2
  -- Interior vs boundary.
  rcases eq_or_lt_of_le hys_mem.1 with hy0 | hy0
  · exact hbdry s hs ys hys_mem (Or.inl hy0.symm) hargmin
  · rcases eq_or_lt_of_le hys_mem.2 with hy1 | hy1
    · exact hbdry s hs ys hys_mem (Or.inr hy1) hargmin
    · exact hbound_interior hχ hsol hs0 hsT hM' (hSupNorm s hs)
        ⟨hy0, hy1⟩ hargmin

/-- **Per-solution persistence floor from the regime sup bound + boundary
input.** -/
theorem solution_persist_of_supNorm
    {p : CM2Params} {T δ t₁ M' : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hχ : p.χ₀ ≤ 0)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht₁ : 0 < t₁) (ht₁T : t₁ < T) (hTδ : T ≤ δ) (hM' : 0 ≤ M')
    (hSupNorm : ∀ s ∈ Set.Ico (t₁/2) T, ∀ y,
      |intervalDomainLift (u s) y| ≤ M')
    (hbdry : ∀ s ∈ Set.Ico (t₁/2) T, ∀ ys ∈ Set.Icc (0:ℝ) 1, ys = 0 ∨ ys = 1 →
      intervalDomainLift (u s) ys
          = sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1) →
        -(|p.χ₀| * fluxCoeffConst p.β (p.ν * M' ^ p.γ) + p.b * M' ^ p.α)
            * sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1)
          ≤ deriv (fun r => intervalDomainLift (u r) ys) s) :
    ∃ c : ℝ, 0 < c ∧
      ∀ t, t₁ ≤ t → t < T → ∀ x : intervalDomainPoint, c ≤ u t x := by
  have hKp_nonneg : 0 ≤ |p.χ₀| * fluxCoeffConst p.β (p.ν * M' ^ p.γ) + p.b * M' ^ p.α := by
    have hfc : 0 ≤ fluxCoeffConst p.β (p.ν * M' ^ p.γ) :=
      fluxCoeffConst_nonneg p.hβ (mul_nonneg p.hν.le (Real.rpow_nonneg hM' _))
    have h2 : 0 ≤ M' ^ p.α := Real.rpow_nonneg hM' _
    exact add_nonneg (mul_nonneg (abs_nonneg _) hfc) (mul_nonneg p.hb h2)
  exact solution_persist_exists_c hsol hKp_nonneg ht₁ ht₁T hTδ
    (hbound_full hχ hsol ht₁ ht₁T hM' hSupNorm hbdry)

end ShenWork.MinPersistenceAtoms
