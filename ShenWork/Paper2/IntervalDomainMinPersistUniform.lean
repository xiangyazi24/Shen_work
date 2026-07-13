/-
  Phase C (MinPersistence): the uniform-`c` capstone.

  Swaps the per-solution Hamilton floor into the `∃c`-before-`∀solution` shape
  of `ClassicalMinPersistence` (for fixed `u₀, δ, t₁`).  The cross-solution
  uniformity is supplied by overlap uniqueness (`OverlapUniqueForPID`): all
  classical solutions with trace `u₀` agree at `t₁/2`, hence share the spatial
  minimum `m(t₁/2)`, hence share the floor `c := m(t₁/2)·e^{−Kp(δ−t₁/2)}`.

  Inputs: the regime sup bound `hSupNorm` (from `hSupNorm_of_regime`), the
  boundary min-point bound `hbdry` (the one remaining hard analytic gap), and
  `hOverlap` (proved in the regime).  Everything else is the proved Hamilton
  machinery.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainPersistAssembly
import ShenWork.Paper2.IntervalDomainMinPersistSolution
import ShenWork.Paper2.IntervalDomainSliceMinPos
import ShenWork.Paper2.IntervalDomainSliceMinEq
import ShenWork.Paper2.IntervalDomainGlueExtension

open ShenWork.IntervalDomain ShenWork.Paper2 Set Filter Topology

noncomputable section

namespace ShenWork.MinPersistenceAtoms

set_option maxHeartbeats 1000000 in
/-- **Uniform-`c` persistence (the `ClassicalMinPersistence` body).** -/
theorem minPersist_existsC_uniform_allChi
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {δ t₁ M' : ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (ht₁ : 0 < t₁) (ht₁δ : t₁ < δ) (hM' : 0 ≤ M')
    (hOverlap : ShenWork.IntervalDomainExistence.IntervalClassicalSolutionOverlapUniqueAt p u₀)
    (hSupNorm : ∀ {T : ℝ} {u v : ℝ → intervalDomainPoint → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
      ∀ s ∈ Set.Ico (t₁/2) T, ∀ y, |intervalDomainLift (u s) y| ≤ M')
    (hbdry : ∀ {T : ℝ} {u v : ℝ → intervalDomainPoint → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
      ∀ s ∈ Set.Ico (t₁/2) T, ∀ ys ∈ Set.Icc (0:ℝ) 1, ys = 0 ∨ ys = 1 →
        intervalDomainLift (u s) ys
            = sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1) →
          -(|p.χ₀| * fluxCoeffConst p.β (p.ν * M' ^ p.γ) + p.b * M' ^ p.α)
              * sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1)
            ≤ deriv (fun r => intervalDomainLift (u r) ys) s) :
    ∃ c : ℝ, 0 < c ∧ ∀ T : ℝ, t₁ < T → T ≤ δ →
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
        ∀ t, t₁ ≤ t → t < T → ∀ x : intervalDomainPoint, c ≤ u t x := by
  set Kp : ℝ := |p.χ₀| * fluxCoeffConst p.β (p.ν * M' ^ p.γ) + p.b * M' ^ p.α
    with hKp_def
  have hKp_nonneg : 0 ≤ Kp := by
    rw [hKp_def]
    exact add_nonneg (mul_nonneg (abs_nonneg _)
      (fluxCoeffConst_nonneg p.hβ (mul_nonneg p.hν.le (Real.rpow_nonneg hM' _))))
      (mul_nonneg p.hb (Real.rpow_nonneg hM' _))
  by_cases hex : ∃ T : ℝ, t₁ < T ∧ T ≤ δ ∧
      ∃ u v : ℝ → intervalDomainPoint → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v ∧
        InitialTrace intervalDomain u₀ u
  · obtain ⟨T_s, hT_s_lo, _, u_s, v_s, hsol_s, htr_s⟩ := hex
    have hhalf_lt_Ts : t₁ / 2 < T_s := by linarith
    -- The reference minimum at `t₁/2`.
    set m0 : ℝ := sInf (intervalDomainLift (u_s (t₁/2)) '' Set.Icc (0:ℝ) 1)
      with hm0_def
    have hm0_pos : 0 < m0 := sliceMin_pos_of_solution hsol_s (by linarith) hhalf_lt_Ts
    refine ⟨m0 * Real.exp (-Kp * (δ - t₁/2)), by positivity, ?_⟩
    intro T hTlo hThi u v hsol htr t htlo thtT x
    -- Hamilton bound for `u` on `[t₁/2, t]`.
    have hbf := hbound_full_allChi hsol (by linarith)
      (lt_of_le_of_lt htlo thtT) hM' (hSupNorm hsol htr) (hbdry hsol htr)
    have hbnd := solution_minPersist_of_conjuncts (a := t₁/2) (b := t) (Kp := Kp)
      hsol (by linarith) thtT (by linarith)
      (fun s hs ys hys harg =>
        hbf s ⟨hs.1, lt_of_le_of_lt hs.2 thtT⟩ ys hys harg)
      t (Set.right_mem_Icc.mpr (by linarith)) x
    -- `m_u(t₁/2) = m0` by overlap uniqueness.
    have hagree : ∀ y : intervalDomainPoint, u (t₁/2) y = u_s (t₁/2) y := fun y =>
      (hOverlap
        { T_pos := hsol.T_pos, u := u, v := v, sol := hsol, trace := htr }
        { T_pos := hsol_s.T_pos, u := u_s, v := v_s, sol := hsol_s, trace := htr_s }
        (t₁/2) (by linarith)
        (lt_min (by linarith) hhalf_lt_Ts) y).1
    have hmeq : sInf (intervalDomainLift (u (t₁/2)) '' Set.Icc (0:ℝ) 1) = m0 :=
      sliceMin_eq_of_slices_eq hagree
    rw [hmeq] at hbnd
    -- `e^{−Kp(t−t₁/2)} ≥ e^{−Kp(δ−t₁/2)}`  (t ≤ δ, Kp ≥ 0).
    have hexp_le : Real.exp (-Kp * (δ - t₁/2)) ≤ Real.exp (-Kp * (t - t₁/2)) := by
      refine Real.exp_le_exp.mpr ?_
      have : t ≤ δ := le_trans thtT.le hThi
      nlinarith [hKp_nonneg]
    calc m0 * Real.exp (-Kp * (δ - t₁/2))
        ≤ m0 * Real.exp (-Kp * (t - t₁/2)) :=
          mul_le_mul_of_nonneg_left hexp_le hm0_pos.le
      _ ≤ u t x := hbnd
  · -- No solution exists: the bound is vacuous.
    refine ⟨1, one_pos, ?_⟩
    intro T hTlo hThi u v hsol htr _ _ _ _
    exact absurd ⟨T, hTlo, hThi, u, v, hsol, htr⟩ hex

/-- Compatibility wrapper for the former nonpositive-sensitivity API. -/
theorem minPersist_existsC_uniform
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {δ t₁ M' : ℝ}
    (_hχ : p.χ₀ ≤ 0)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (ht₁ : 0 < t₁) (ht₁δ : t₁ < δ) (hM' : 0 ≤ M')
    (hOverlap : GlueExtension.OverlapUniqueForPID p)
    (hSupNorm : ∀ {T : ℝ} {u v : ℝ → intervalDomainPoint → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
      ∀ s ∈ Set.Ico (t₁/2) T, ∀ y, |intervalDomainLift (u s) y| ≤ M')
    (hbdry : ∀ {T : ℝ} {u v : ℝ → intervalDomainPoint → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
      ∀ s ∈ Set.Ico (t₁/2) T, ∀ ys ∈ Set.Icc (0:ℝ) 1, ys = 0 ∨ ys = 1 →
        intervalDomainLift (u s) ys
            = sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1) →
          -(|p.χ₀| * fluxCoeffConst p.β (p.ν * M' ^ p.γ) + p.b * M' ^ p.α)
              * sInf (intervalDomainLift (u s) '' Set.Icc (0:ℝ) 1)
            ≤ deriv (fun r => intervalDomainLift (u r) ys) s) :
    ∃ c : ℝ, 0 < c ∧ ∀ T : ℝ, t₁ < T → T ≤ δ →
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
        ∀ t, t₁ ≤ t → t < T → ∀ x : intervalDomainPoint, c ≤ u t x :=
  minPersist_existsC_uniform_allChi hu₀ ht₁ ht₁δ hM'
    (by
      intro T₁ T₂ d₁ d₂ t ht0 htmin x
      exact hOverlap hu₀ d₁.sol d₂.sol d₁.trace d₂.trace t ht0 htmin x)
    hSupNorm hbdry

end ShenWork.MinPersistenceAtoms
