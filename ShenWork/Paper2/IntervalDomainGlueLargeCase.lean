/-
  RestartAndGlueWorks from PiecewiseClassicalWorks: large-T₀ case,
  complete case split, and F1 assembly.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainGlueExtension
import ShenWork.Paper2.IntervalDomainPiecewiseGlue
import ShenWork.Paper2.IntervalDomainRestartExtension

open ShenWork.IntervalDomain
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.GlueLargeCase

/-! ## Auxiliary hypotheses

These package the inputs that the restart-and-glue proof consumes beyond
the PiecewiseClassicalWorks hypothesis itself. -/

/-- Overlap uniqueness for two solutions sharing a PID initial trace. -/
def OverlapUniqueForPID (p : CM2Params) : Prop :=
  ∀ {u₀ : intervalDomainPoint → ℝ},
    PositiveInitialDatum intervalDomain u₀ →
  ∀ {T₁ T₂ : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
    IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
    IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
    InitialTrace intervalDomain u₀ u₁ →
    InitialTrace intervalDomain u₀ u₂ →
      ∀ t, 0 < t → t < min T₁ T₂ →
        ∀ x : intervalDomainPoint, u₁ t x = u₂ t x ∧ v₁ t x = v₂ t x

/-- Initial trace of a time-shifted solution: `‖u(t+τ)−u(τ)‖_∞ → 0`
as `t → 0⁺`, from joint (t,x)-continuity of u on the closed slab. -/
def TimeShiftInitialTraceWorks : Prop :=
  ∀ {p : CM2Params} {T : ℝ} {u v : ℝ → intervalDomainPoint → ℝ},
    IsPaper2ClassicalSolution intervalDomain p T u v →
    ∀ {τ : ℝ}, 0 < τ → τ < T →
      InitialTrace intervalDomain (u τ) (fun t x => u (t + τ) x)

/-! ## Large-T₀ case (T₀ > δ/2)

Given:
  - S₁ = (u,v) on [0, T₀] with InitialTrace u₀, interior sup-norm ≤ M
  - Factory giving S₂ = (w,z) on [0, δ] from any PID bounded by M
  - OverlapUniqueForPID, RegularityTimeShiftWorks, TimeShiftInitialTraceWorks
  - PiecewiseClassicalWorks

Construct a solution on [0, T₀ + δ/2] with InitialTrace u₀.

Strategy:
  1. τ = T₀ − δ/4, so τ ∈ (0, T₀) and τ + δ = T₀ + 3δ/4.
  2. u(τ) is PID bounded by M.
  3. Factory → (w,z) on [0, δ] with InitialTrace u(τ).
  4. Time-shift → (u(·+τ), v(·+τ)) on [0, δ/4].
  5. Overlap uniqueness → u(s) = w(s−τ) for s ∈ (τ, T₀).
  6. PiecewiseClassicalWorks gives:
       IsPaper2ClassicalSolution (T₀+δ/2) (splice u w) (splice v z).
  7. InitialTrace u₀ (splice u w) from splice = u for small t.
-/

theorem restartAndGlue_large_T₀_of_piecewise
    (p : CM2Params)
    (hPiecewise : PiecewiseGlue.PiecewiseClassicalWorks p)
    (hRegShift : TimeShift.RegularityTimeShiftWorks)
    (hOverlap : OverlapUniqueForPID p)
    (hTraceShift : TimeShiftInitialTraceWorks)
    {M δ : ℝ} (_hM : 0 < M) (hδ : 0 < δ)
    (hfactory : ∀ {w : intervalDomainPoint → ℝ},
      PositiveInitialDatum intervalDomain w →
      (∀ x, |w x| ≤ M) →
      ∃ uw vw, IsPaper2ClassicalSolution intervalDomain p δ uw vw ∧
        InitialTrace intervalDomain w uw)
    {u₀ : intervalDomainPoint → ℝ} (_hu₀ : PositiveInitialDatum intervalDomain u₀)
    (_hbound : ∀ x, |u₀ x| ≤ M)
    {T₀ : ℝ} (hT₀ : 0 < T₀) (hT₀_large : δ / 2 < T₀)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T₀ u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hSupBound : ∀ t, 0 < t → t < T₀ → ∀ x : intervalDomainPoint, |u t x| ≤ M) :
    ∃ u' v', IsPaper2ClassicalSolution intervalDomain p (T₀ + δ / 2) u' v' ∧
      InitialTrace intervalDomain u₀ u' := by
  -- Step 1: restart time τ = T₀ − δ/4.
  set τ : ℝ := T₀ - δ / 4 with hτ_def
  have hτ_pos : 0 < τ := by linarith
  have hτ_lt : τ < T₀ := by linarith
  have hτ_mem : τ ∈ Set.Ioo (0 : ℝ) T₀ := ⟨hτ_pos, hτ_lt⟩
  -- Step 2: u(τ) is PID bounded by M.
  have hu_τ_pid : PositiveInitialDatum intervalDomain (u τ) :=
    UniformContinuation.classicalSolution_slice_positiveInitialDatum hsol hτ_mem
  have hu_τ_bound : ∀ x : intervalDomainPoint, |u τ x| ≤ M :=
    hSupBound τ hτ_pos hτ_lt
  -- Step 3: factory → fresh solution from u(τ).
  obtain ⟨w, z, hsol_w, htrace_w⟩ := hfactory hu_τ_pid hu_τ_bound
  -- Step 4: time-shift.
  have hT₀_sub_τ : T₀ - τ = δ / 4 := by linarith
  have hsol_shift : IsPaper2ClassicalSolution intervalDomain p (T₀ - τ)
      (fun t x => u (t + τ) x) (fun t x => v (t + τ) x) :=
    TimeShift.classicalSolution_timeShift hRegShift hsol hτ_pos hτ_lt
  have htrace_shift : InitialTrace intervalDomain (u τ) (fun t x => u (t + τ) x) :=
    hTraceShift hsol hτ_pos hτ_lt
  -- Step 5: overlap uniqueness → u(s) = w(s−τ) for s ∈ (τ, T₀).
  have hmin : min (T₀ - τ) δ = T₀ - τ := by
    rw [hT₀_sub_τ]; exact min_eq_left (by linarith)
  have hoverlap_u : ∀ s, τ < s → s < T₀ → ∀ x : intervalDomainPoint,
      u s x = w (s - τ) x := by
    intro s hs_lo hs_hi x
    have hst := hOverlap hu_τ_pid hsol_shift hsol_w htrace_shift htrace_w
      (s - τ) (by linarith) (by rw [hmin]; linarith) x
    simp only [sub_add_cancel] at hst
    exact hst.1
  have hoverlap_v : ∀ s, τ < s → s < T₀ → ∀ x : intervalDomainPoint,
      v s x = z (s - τ) x := by
    intro s hs_lo hs_hi x
    have hst := hOverlap hu_τ_pid hsol_shift hsol_w htrace_shift htrace_w
      (s - τ) (by linarith) (by rw [hmin]; linarith) x
    simp only [sub_add_cancel] at hst
    exact hst.2
  -- Step 6: PiecewiseClassicalWorks gives the classical solution.
  have hT'_pos : 0 < T₀ + δ / 2 := by linarith
  have hT'_le : T₀ + δ / 2 ≤ τ + δ := by linarith
  have hsol' := hPiecewise hT₀ hδ hτ_pos hτ_lt hsol hsol_w
    hoverlap_u hoverlap_v (T₀ + δ / 2) hT'_pos hT'_le
  -- Step 7: initial trace.
  have htrace' : InitialTrace intervalDomain u₀
      (fun t x => if t ≤ T₀ then u t x else w (t - τ) x) := by
    intro ε hε
    obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := htrace ε hε
    refine ⟨min δ₁ T₀, lt_min hδ₁_pos hT₀, ?_⟩
    intro t ht0 htδ
    have htT₀ : t ≤ T₀ := le_of_lt (lt_of_lt_of_le htδ (min_le_right _ _))
    have htδ₁ : t < δ₁ := lt_of_lt_of_le htδ (min_le_left _ _)
    have hfun_eq : (fun x => (if t ≤ T₀ then u t x else w (t - τ) x) - u₀ x) =
        (fun x => u t x - u₀ x) := by
      funext x; rw [if_pos htT₀]
    simp only [intervalDomain] at hδ₁ ⊢
    rw [hfun_eq]; exact hδ₁ t ht0 htδ₁
  exact ⟨_, _, hsol', htrace'⟩

/-! ## Complete RestartAndGlueWorks: small + large case split -/

/-- **RestartAndGlueWorks from PiecewiseClassicalWorks + overlap uniqueness
+ regularity time-shift + time-shift initial trace.**

Combines the small-T₀ case (restriction, from `GlueExtension`) with the
large-T₀ case (piecewise splice, above). -/
theorem restartAndGlueWorks_of_piecewise
    (p : CM2Params)
    (hPiecewise : PiecewiseGlue.PiecewiseClassicalWorks p)
    (hRegShift : TimeShift.RegularityTimeShiftWorks)
    (hOverlap : OverlapUniqueForPID p)
    (hTraceShift : TimeShiftInitialTraceWorks) :
    RestartExtension.RestartAndGlueWorks p := by
  intro M δ hM hδ hfactory u₀ hu₀ hbound T₀ hT₀ u v hsol htrace hSupBound
  by_cases hsmall : T₀ ≤ δ / 2
  · exact GlueExtension.restartAndGlue_small_T₀ hM hδ hfactory hu₀ hbound hT₀
      hsol htrace hSupBound hsmall
  · push Not at hsmall
    exact restartAndGlue_large_T₀_of_piecewise p hPiecewise hRegShift hOverlap
      hTraceShift hM hδ hfactory hu₀ hbound hT₀ hsmall hsol htrace hSupBound

/-! ## F1 assembly: IntervalDomainUniformLocalExistence from frontier hypotheses -/

/-- **F1: IntervalDomainUniformLocalExistence from the frontier hypotheses.**

Combines:
  - `hQuant`: quantitative local existence (Picard contraction delta(M))
  - `PiecewiseClassicalWorks`: splice regularity
  - `OverlapUniqueForPID`: L2 uniqueness on overlap
  - `RegularityTimeShiftWorks`: time-shift regularity
  - `TimeShiftInitialTraceWorks`: time-shift initial trace
  - `hSupNorm`: interior sup-norm preservation (Lemma 3.1) -/
theorem uniformLocalExistence_of_frontier
    (p : CM2Params)
    (hQuant : ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v, IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u)
    (hPiecewise : PiecewiseGlue.PiecewiseClassicalWorks p)
    (hRegShift : TimeShift.RegularityTimeShiftWorks)
    (hOverlap : OverlapUniqueForPID p)
    (hTraceShift : TimeShiftInitialTraceWorks)
    (hSupNorm : ∀ {M : ℝ}, 0 < M →
      ∀ {u₀}, PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
      ∀ {T₀}, 0 < T₀ →
      ∀ {u v}, IsPaper2ClassicalSolution intervalDomain p T₀ u v →
        InitialTrace intervalDomain u₀ u →
        ∀ t, 0 < t → t < T₀ → ∀ x : intervalDomainPoint, |u t x| ≤ M) :
    IntervalDomainUniformLocalExistence p :=
  RestartExtension.uniformLocalExistence_of_quantitative_restart_supNorm
    p hQuant
    (restartAndGlueWorks_of_piecewise p hPiecewise hRegShift hOverlap hTraceShift)
    hSupNorm

end ShenWork.Paper2.GlueLargeCase
