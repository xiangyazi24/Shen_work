/-
  Glue extension: splice two classical solutions to extend the horizon.

  * `restartAndGlue_small_T₀` — trivial case T₀ ≤ δ/2
  * `restartAndGlueWorks_of_hypotheses` — general case from 3 hypotheses
-/
import ShenWork.Paper2.IntervalDomainUniformContinuation
import ShenWork.Paper2.IntervalDomainTimeShift
import ShenWork.Paper2.IntervalDomainRestartExtension

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.RestartExtension

noncomputable section

namespace ShenWork.Paper2.GlueExtension

/-- When T₀ ≤ δ/2, the fresh solution covers [0, T₀+δ/2] ⊆ [0,δ]. -/
theorem restartAndGlue_small_T₀
    {p : CM2Params} {M δ : ℝ} (_hM : 0 < M) (_hδ : 0 < δ)
    (hfactory : ∀ {w : intervalDomainPoint → ℝ},
      PositiveInitialDatum intervalDomain w →
      (∀ x, |w x| ≤ M) →
      ∃ uw vw, IsPaper2ClassicalSolution intervalDomain p δ uw vw ∧
        InitialTrace intervalDomain w uw)
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hbound : ∀ x, |u₀ x| ≤ M)
    {T₀ : ℝ} (_hT₀ : 0 < T₀)
    (hsmall : T₀ ≤ δ / 2) :
    ∃ u' v',
      IsPaper2ClassicalSolution intervalDomain p (T₀ + δ / 2) u' v' ∧
        InitialTrace intervalDomain u₀ u' := by
  obtain ⟨uf, vf, hsolf, htracef⟩ := hfactory hu₀ hbound
  exact ⟨uf, vf,
    hsolf.restrict_horizon (by linarith) (by linarith), htracef⟩

/-- Overlap uniqueness for PID-sharing solutions. -/
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
          ∀ x : intervalDomainPoint,
            u₁ t x = u₂ t x ∧ v₁ t x = v₂ t x

/-- Initial trace of a time-shifted solution. -/
def TimeShiftInitialTraceWorks : Prop :=
  ∀ {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ},
    IsPaper2ClassicalSolution intervalDomain p T u v →
    ∀ {τ : ℝ}, 0 < τ → τ < T →
      InitialTrace intervalDomain (u τ)
        (fun t x => u (t + τ) x)

/-- **RestartAndGlueWorks from three hypotheses.** -/
theorem restartAndGlueWorks_of_hypotheses
    (p : CM2Params)
    (hRegShift : TimeShift.RegularityTimeShiftWorks)
    (hOverlap : OverlapUniqueForPID p)
    (hTraceShift : TimeShiftInitialTraceWorks) :
    RestartAndGlueWorks p := by
  intro M δ hM hδ hfactory u₀ hu₀ hbound T₀ hT₀ u v hsol htrace hSupBound
  by_cases hsmall : T₀ ≤ δ / 2
  · exact restartAndGlue_small_T₀ hM hδ hfactory hu₀ hbound hT₀ hsmall
  push_neg at hsmall
  -- τ = T₀ − δ/4, so τ ∈ (0, T₀) and τ+δ = T₀ + 3δ/4 ≥ T₀ + δ/2.
  set τ : ℝ := T₀ - δ / 4
  have hτ_pos : 0 < τ := by linarith
  have hτ_lt : τ < T₀ := by linarith
  set T' : ℝ := T₀ + δ / 2
  have hT'_pos : 0 < T' := by linarith
  -- u(τ) is PID bounded by M.
  have hu_τ_pid :=
    UniformContinuation.classicalSolution_slice_positiveInitialDatum
      hsol ⟨hτ_pos, hτ_lt⟩
  have hu_τ_bnd : ∀ x : intervalDomainPoint, |u τ x| ≤ M :=
    hSupBound τ hτ_pos hτ_lt
  obtain ⟨w, z, hsol_w, htrace_w⟩ := hfactory hu_τ_pid hu_τ_bnd
  -- Time-shift + overlap.
  have hsol_sh :=
    TimeShift.classicalSolution_timeShift hRegShift hsol hτ_pos hτ_lt
  have htr_sh : InitialTrace intervalDomain (u τ)
      (fun t x => u (t + τ) x) :=
    hTraceShift hsol hτ_pos hτ_lt
  have hov : ∀ s, τ < s → s < T₀ →
      ∀ x : intervalDomainPoint,
        u s x = w (s - τ) x ∧ v s x = z (s - τ) x := by
    intro s hs1 hs2 x
    have := hOverlap hu_τ_pid hsol_sh hsol_w htr_sh htrace_w
      (s - τ) (by linarith)
      (by rw [min_eq_left (by linarith : T₀ - τ ≤ δ)]; linarith) x
    simp only [sub_add_cancel] at this; exact this
  -- Splice: u for t < T₀, w(·−τ) for t ≥ T₀.
  let u' : ℝ → intervalDomainPoint → ℝ :=
    fun t x => if t < T₀ then u t x else w (t - τ) x
  let v' : ℝ → intervalDomainPoint → ℝ :=
    fun t x => if t < T₀ then v t x else z (t - τ) x
  have hu'L : ∀ t, t < T₀ → u' t = u t :=
    fun t h => funext fun _ => if_pos h
  have hv'L : ∀ t, t < T₀ → v' t = v t :=
    fun t h => funext fun _ => if_pos h
  have hu'R : ∀ t, T₀ ≤ t → u' t = w (t - τ) :=
    fun t h => funext fun _ => if_neg (not_lt.mpr h)
  have hv'R : ∀ t, T₀ ≤ t → v' t = z (t - τ) :=
    fun t h => funext fun _ => if_neg (not_lt.mpr h)
  -- On (τ, τ+δ), splice = w(·−τ).
  have hu'F : ∀ t, τ < t → t < τ + δ → u' t = w (t - τ) := by
    intro t h1 h2
    by_cases h : t < T₀
    · rw [hu'L t h]; funext x; exact (hov t h1 h x).1
    · exact hu'R t (le_of_not_lt h)
  have hv'F : ∀ t, τ < t → t < τ + δ → v' t = z (t - τ) := by
    intro t h1 h2
    by_cases h : t < T₀
    · rw [hv'L t h]; funext x; exact (hov t h1 h x).2
    · exact hv'R t (le_of_not_lt h)
  refine ⟨u', v', ?_, ?_⟩
  · -- IsPaper2ClassicalSolution on [0, T'].
    refine IsPaper2ClassicalSolution.of_components hT'_pos
      ?_ ?_ ?_ ?_ ?_ ?_
    · -- regularity
      sorry
    · -- u > 0
      intro t x ht0 htT'
      by_cases h : t < T₀
      · exact show 0 < u t x from hsol.u_pos' ht0 h ▸
          congrFun (hu'L t h) x ▸ hsol.u_pos' ht0 h
      · have := hsol_w.u_pos' (show 0 < t - τ by linarith)
          (show t - τ < δ by linarith) (x := x)
        rw [← congrFun (hu'R t (le_of_not_lt h)) x]; exact this
    · -- v ≥ 0
      intro t x ht0 htT'
      by_cases h : t < T₀
      · rw [congrFun (hv'L t h) x]; exact hsol.v_nonneg ht0 h
      · rw [congrFun (hv'R t (le_of_not_lt h)) x]
        exact hsol_w.v_nonneg (by linarith) (by linarith)
    · -- PDE u
      intro t x ht0 htT' hx
      by_cases h : t < T₀
      · have hev : (fun s => u' s x) =ᶠ[nhds t]
            (fun s => u s x) :=
          Set.EqOn.eventuallyEq_of_mem
            (fun s (hs : s ∈ Set.Iio T₀) =>
              congrFun (hu'L s hs) x)
            (isOpen_Iio.mem_nhds h)
        have hpde := hsol.pde_u ht0 h hx
        simp only [intervalDomain] at hpde ⊢
        change deriv (fun s => u' s x) t = _
        rw [hev.deriv_eq, hu'L t h, hv'L t h]; exact hpde
      · push_neg at h
        have h1 : τ < t := by linarith
        have h2 : t < τ + δ := by linarith
        have hev : (fun s => u' s x) =ᶠ[nhds t]
            (fun s => w (s - τ) x) :=
          Set.EqOn.eventuallyEq_of_mem
            (fun s (hs : s ∈ Set.Ioo τ (τ + δ)) =>
              congrFun (hu'F s hs.1 hs.2) x)
            (isOpen_Ioo.mem_nhds ⟨h1, h2⟩)
        have hpde := hsol_w.pde_u (show 0 < t - τ by linarith)
          (show t - τ < δ by linarith) hx
        simp only [intervalDomain] at hpde ⊢
        change deriv (fun s => u' s x) t = _
        rw [hev.deriv_eq,
          show deriv (fun s => w (s - τ) x) t =
            deriv (fun s => w s x) (t - τ) from
            deriv_comp_sub_const _ t,
          hu'F t h1 h2, hv'F t h1 h2]
        exact hpde
    · -- PDE v
      intro t x ht0 htT' hx
      by_cases h : t < T₀
      · rw [hu'L t h, hv'L t h]; exact hsol.pde_v ht0 h hx
      · push_neg at h
        rw [hu'F t (by linarith) (by linarith),
          hv'F t (by linarith) (by linarith)]
        exact hsol_w.pde_v (by linarith) (by linarith) hx
    · -- Neumann
      intro t x ht0 htT' hx
      by_cases h : t < T₀
      · rw [hu'L t h, hv'L t h]; exact hsol.neumann ht0 h hx
      · push_neg at h
        rw [hu'F t (by linarith) (by linarith),
          hv'F t (by linarith) (by linarith)]
        exact hsol_w.neumann (by linarith) (by linarith) hx
  · -- InitialTrace u₀ u'.
    intro ε hε
    obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := htrace ε hε
    refine ⟨min δ₁ T₀, lt_min hδ₁_pos hT₀, ?_⟩
    intro t ht0 htδ
    have htT₀ : t < T₀ :=
      lt_of_lt_of_le htδ (min_le_right _ _)
    have hfun_eq :
        (fun x => u' t x - u₀ x) = (fun x => u t x - u₀ x) := by
      funext x; show (if t < T₀ then u t x else _) - u₀ x = _
      rw [if_pos htT₀]
    simp only [intervalDomain] at hδ₁ ⊢
    rw [hfun_eq]
    exact hδ₁ t ht0 (lt_of_lt_of_le htδ (min_le_left _ _))

end ShenWork.Paper2.GlueExtension
