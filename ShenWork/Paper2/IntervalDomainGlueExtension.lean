/-
  Glue extension: splice two classical solutions to extend the horizon.

  * `restartAndGlue_small_T₀` — trivial case T₀ ≤ δ/2
  * `restartAndGlueWorks_of_hypotheses` — general case from 3 hypotheses
-/
import ShenWork.Paper2.IntervalDomainUniformContinuation
import ShenWork.Paper2.IntervalDomainTimeShift
import ShenWork.Paper2.IntervalDomainRestartExtension
import ShenWork.Paper2.IntervalDomainPiecewiseGlue
import Mathlib.Topology.UniformSpace.HeineCantor

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
    {T₀ : ℝ} (_hT₀ : 0 < T₀) (hsmall : T₀ ≤ δ / 2) :
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
    (hTraceShift : TimeShiftInitialTraceWorks)
    (hPR : PiecewiseGlue.PiecewiseClassicalWorks p) :
    RestartAndGlueWorks p := by
  intro M δ hM hδ hfactory u₀ hu₀ hbound T₀ hT₀ u v hsol htrace hSupBound
  by_cases hsmall : T₀ ≤ δ / 2
  · exact restartAndGlue_small_T₀ hM hδ hfactory hu₀ hbound hT₀ hsmall
  push_neg at hsmall -- hsmall : δ / 2 < T₀
  -- τ = T₀ − δ/4.
  have hτ_def : T₀ - δ / 4 = T₀ - δ / 4 := rfl
  set τ : ℝ := T₀ - δ / 4 with hτ_eq
  have hτ_pos : 0 < τ := by simp [hτ_eq]; linarith
  have hτ_lt : τ < T₀ := by simp [hτ_eq]; linarith
  have hτδ : T₀ + δ / 2 ≤ τ + δ := by simp [hτ_eq]; linarith
  have hu_τ_pid :=
    UniformContinuation.classicalSolution_slice_positiveInitialDatum
      hsol ⟨hτ_pos, hτ_lt⟩
  obtain ⟨w, z, hsol_w, htrace_w⟩ :=
    hfactory hu_τ_pid (hSupBound τ hτ_pos hτ_lt)
  have hsol_sh :=
    TimeShift.classicalSolution_timeShift hRegShift hsol hτ_pos hτ_lt
  have htr_sh := hTraceShift hsol hτ_pos hτ_lt
  have hminle : T₀ - τ ≤ δ := by simp [hτ_eq]; linarith
  have hov : ∀ s, τ < s → s < T₀ →
      ∀ x : intervalDomainPoint,
        u s x = w (s - τ) x ∧ v s x = z (s - τ) x := by
    intro s hs1 hs2 x
    have h1 : 0 < s - τ := by linarith
    have h2 : s - τ < min (T₀ - τ) δ := by
      rw [min_eq_left hminle]; linarith
    have := hOverlap hu_τ_pid hsol_sh hsol_w htr_sh htrace_w
      (s - τ) h1 h2 x
    simp only [sub_add_cancel] at this; exact this
  -- Splice.
  let u' : ℝ → intervalDomainPoint → ℝ :=
    fun t x => if t < T₀ then u t x else w (t - τ) x
  let v' : ℝ → intervalDomainPoint → ℝ :=
    fun t x => if t < T₀ then v t x else z (t - τ) x
  have hu'L : ∀ t, t < T₀ → u' t = u t :=
    fun t h => funext fun _ => if_pos h
  have hv'L : ∀ t, t < T₀ → v' t = v t :=
    fun t h => funext fun _ => if_pos h
  have hu'R : ∀ t, ¬ t < T₀ → u' t = w (t - τ) :=
    fun t h => funext fun _ => if_neg h
  have hv'R : ∀ t, ¬ t < T₀ → v' t = z (t - τ) :=
    fun t h => funext fun _ => if_neg h
  have hu'F : ∀ t, τ < t → t < τ + δ → u' t = w (t - τ) := by
    intro t h1 h2
    by_cases h : t < T₀
    · rw [hu'L t h]; funext x; exact (hov t h1 h x).1
    · exact hu'R t h
  have hv'F : ∀ t, τ < t → t < τ + δ → v' t = z (t - τ) := by
    intro t h1 h2
    by_cases h : t < T₀
    · rw [hv'L t h]; funext x; exact (hov t h1 h x).2
    · exact hv'R t h
  refine ⟨u', v', ?_, ?_⟩
  · refine IsPaper2ClassicalSolution.of_components (by linarith) ?_ ?_ ?_
      ?_ ?_ ?_
    · -- regularity via PiecewiseClassicalWorks
      exact (hPR hT₀ hsol_w.T_pos hτ_pos hτ_lt hsol hsol_w
        (fun s hs hst x => (hov s hs hst x).1)
        (fun s hs hst x => (hov s hs hst x).2)
        (T₀ + δ / 2) (by linarith) (by simp only [hτ_eq]; linarith)).2.1
    · -- u > 0
      intro t x ht0 htT'
      by_cases h : t < T₀
      · have : u' t x = u t x := congrFun (hu'L t h) x
        rw [this]; exact hsol.u_pos' ht0 h
      · have hge : T₀ ≤ t := not_lt.mp h
        have : u' t x = w (t - τ) x := congrFun (hu'R t h) x
        rw [this]
        exact hsol_w.u_pos'
          (show 0 < t - τ by linarith)
          (show t - τ < δ by simp [hτ_eq] at hge ⊢; linarith)
    · -- v ≥ 0
      intro t x ht0 htT'
      by_cases h : t < T₀
      · rw [congrFun (hv'L t h) x]; exact hsol.v_nonneg ht0 h
      · have hge : T₀ ≤ t := not_lt.mp h
        rw [congrFun (hv'R t h) x]
        exact hsol_w.v_nonneg
          (show 0 < t - τ by linarith)
          (show t - τ < δ by simp [hτ_eq] at hge ⊢; linarith)
    · -- PDE u
      intro t x ht0 htT' hx
      by_cases h : t < T₀
      · have hevU : (fun s => u' s x) =ᶠ[nhds t] (fun s => u s x) :=
          Set.EqOn.eventuallyEq_of_mem
            (fun s (hs : s ∈ Set.Iio T₀) => congrFun (hu'L s hs) x)
            (isOpen_Iio.mem_nhds h)
        have hpde := hsol.pde_u ht0 h hx
        simp only [intervalDomain] at hpde ⊢
        change deriv (fun s => u' s x) t = _
        rw [hevU.deriv_eq, hu'L t h, hv'L t h]; exact hpde
      · have hge : T₀ ≤ t := not_lt.mp h
        have h1 : τ < t := by linarith
        have h2 : t < τ + δ := by simp [hτ_eq] at hge ⊢; linarith
        have hevU : (fun s => u' s x) =ᶠ[nhds t]
            (fun s => w (s - τ) x) :=
          Set.EqOn.eventuallyEq_of_mem
            (fun s (hs : s ∈ Set.Ioo τ (τ + δ)) =>
              congrFun (hu'F s hs.1 hs.2) x)
            (isOpen_Ioo.mem_nhds ⟨h1, h2⟩)
        have hpde := hsol_w.pde_u
          (show 0 < t - τ by linarith)
          (show t - τ < δ by linarith) hx
        simp only [intervalDomain] at hpde ⊢
        change deriv (fun s => u' s x) t = _
        rw [hevU.deriv_eq,
          show deriv (fun s => w (s - τ) x) t =
            deriv (fun s => w s x) (t - τ) from
            deriv_comp_sub_const
              (f := fun s => w s x) (a := τ) (x := t),
          hu'F t h1 h2, hv'F t h1 h2]
        exact hpde
    · -- PDE v
      intro t x ht0 htT' hx
      by_cases h : t < T₀
      · rw [hu'L t h, hv'L t h]; exact hsol.pde_v ht0 h hx
      · have hge : T₀ ≤ t := not_lt.mp h
        rw [hu'F t (by linarith) (by simp [hτ_eq] at hge ⊢; linarith),
          hv'F t (by linarith) (by simp [hτ_eq] at hge ⊢; linarith)]
        exact hsol_w.pde_v
          (by linarith)
          (by simp [hτ_eq] at hge ⊢; linarith) hx
    · -- Neumann
      intro t x ht0 htT' hx
      by_cases h : t < T₀
      · rw [hu'L t h, hv'L t h]; exact hsol.neumann ht0 h hx
      · have hge : T₀ ≤ t := not_lt.mp h
        rw [hu'F t (by linarith) (by simp [hτ_eq] at hge ⊢; linarith),
          hv'F t (by linarith) (by simp [hτ_eq] at hge ⊢; linarith)]
        exact hsol_w.neumann
          (by linarith)
          (by simp [hτ_eq] at hge ⊢; linarith) hx
  · -- InitialTrace u₀ u'.
    intro ε hε
    obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := htrace ε hε
    refine ⟨min δ₁ T₀, lt_min hδ₁_pos hT₀, ?_⟩
    intro t ht0 htδ
    have htT₀ : t < T₀ := lt_of_lt_of_le htδ (min_le_right _ _)
    have hfun_eq :
        (fun x => u' t x - u₀ x) =
          (fun x => u t x - u₀ x) := by
      funext x; show (if t < T₀ then u t x else _) - u₀ x = _
      rw [if_pos htT₀]
    simp only [intervalDomain] at hδ₁ ⊢
    rw [hfun_eq]
    exact hδ₁ t ht0 (lt_of_lt_of_le htδ (min_le_left _ _))

/-- **Initial trace of the time-shifted solution.**

If `(u,v)` is a classical solution on `[0,T]` and `0 < τ < T`, then the
time-shifted function `t ↦ u(t+τ)` has `u τ` as its initial trace.
This follows from joint continuity of `(t,x) ↦ u(t)(x)` (conjunct 9 of
regularity) combined with Heine-Cantor compactness on `[0,1]`. -/
theorem timeShiftInitialTraceWorks : TimeShiftInitialTraceWorks := by
  intro p T u v hsol τ hτ_pos hτ_lt
  intro ε hε
  -- Conjunct (9): joint ContinuousOn of (t,x) ↦ intervalDomainLift (u t) x on Ioo 0 T ×ˢ Icc 0 1
  have hcont9 : ContinuousOn
      (Function.uncurry (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x))
      (Set.Ioo 0 T ×ˢ Set.Icc 0 1) :=
    (hsol.regularity.2.2.2.2.2.2).1
  have hτ_in : τ ∈ Set.Ioo (0 : ℝ) T := ⟨hτ_pos, hτ_lt⟩
  -- Heine-Cantor: uniform modulus over the compact fibre Icc 0 1
  obtain ⟨nbhd, hnbhd_mem, hnbhd⟩ :=
    IsCompact.mem_uniformity_of_prod (k := Set.Icc (0 : ℝ) 1) isCompact_Icc
      hcont9 hτ_in (Metric.dist_mem_uniformity hε)
  rw [Metric.mem_nhdsWithin_iff] at hnbhd_mem
  obtain ⟨δ₀, hδ₀_pos, hδ₀_sub⟩ := hnbhd_mem
  have hTτ_pos : 0 < T - τ := by linarith
  refine ⟨min (δ₀ / 2) ((T - τ) / 2), by positivity, ?_⟩
  intro t ht_pos ht_lt
  have ht_δ₀ : t < δ₀ := by
    have := lt_of_lt_of_le ht_lt (min_le_left _ _); linarith
  have ht_Tτ : t < T - τ := by
    have := lt_of_lt_of_le ht_lt (min_le_right _ _); linarith
  have htτ_in : t + τ ∈ Set.Ioo (0 : ℝ) T := ⟨by linarith, by linarith⟩
  have hdist_tτ : dist (t + τ) τ < δ₀ := by
    rw [Real.dist_eq]; ring_nf; rw [abs_of_pos ht_pos]; exact ht_δ₀
  have htτ_in_nbhd : t + τ ∈ nbhd :=
    hδ₀_sub ⟨Metric.mem_ball.mpr hdist_tτ, htτ_in⟩
  -- Pointwise: |u(t+τ)(x) - u(τ)(x)| < ε for all x : intervalDomainPoint
  have hpt : ∀ x : intervalDomainPoint, |u (t + τ) x - u τ x| < ε := by
    intro x
    have hmem := hnbhd (t + τ) htτ_in_nbhd x.1 x.2
    -- hmem : (intervalDomainLift (u (t+τ)) x.1, intervalDomainLift (u τ) x.1) ∈
    --        {p | dist p.1 p.2 < ε}
    -- i.e., dist (intervalDomainLift (u (t+τ)) x.1) (intervalDomainLift (u τ) x.1) < ε
    have h1 : intervalDomainLift (u (t + τ)) x.1 = u (t + τ) x := by
      unfold intervalDomainLift
      exact (dif_pos x.2).trans (by exact congrArg (u (t + τ)) (Subtype.coe_eta x x.2))
    have h2 : intervalDomainLift (u τ) x.1 = u τ x := by
      unfold intervalDomainLift
      exact (dif_pos x.2).trans (by exact congrArg (u τ) (Subtype.coe_eta x x.2))
    simp only [Set.mem_setOf_eq] at hmem
    rw [h1, h2] at hmem
    rwa [Real.dist_eq] at hmem
  -- Reduce supNorm goal to the pointwise bound
  change intervalDomainSupNorm (fun x => u (t + τ) x - u τ x) < ε
  unfold intervalDomainSupNorm
  haveI : Nonempty intervalDomainPoint := ⟨⟨0, le_refl _, zero_le_one⟩⟩
  haveI : CompactSpace intervalDomainPoint :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  have hcont_tτ : Continuous (u (t + τ)) := by
    have hco := solution_lift_continuousOn_Icc hsol htτ_in
    have hcomp := hco.comp_continuous continuous_subtype_val
        (fun x : intervalDomainPoint => x.2)
    exact hcomp.congr (fun x => by
      simp only [Function.comp]
      unfold intervalDomainLift
      exact (dif_pos x.2).trans (congrArg (u (t + τ)) (Subtype.coe_eta x x.2)))
  have hcont_τ : Continuous (u τ) := by
    have hco := solution_lift_continuousOn_Icc hsol hτ_in
    have hcomp := hco.comp_continuous continuous_subtype_val
        (fun x : intervalDomainPoint => x.2)
    exact hcomp.congr (fun x => by
      simp only [Function.comp]
      unfold intervalDomainLift
      exact (dif_pos x.2).trans (congrArg (u τ) (Subtype.coe_eta x x.2)))
  have hf_cont : Continuous (fun x : intervalDomainPoint => |u (t + τ) x - u τ x|) :=
    (hcont_tτ.sub hcont_τ).abs
  -- The range is compact (hence closed), so sSup is attained
  have hrange_ne :
      (Set.range (fun x : intervalDomainPoint => |u (t + τ) x - u τ x|)).Nonempty :=
    Set.range_nonempty _
  have hrange_bdd : BddAbove
      (Set.range (fun x : intervalDomainPoint => |u (t + τ) x - u τ x|)) :=
    ⟨ε, fun _ ⟨x, hx⟩ => hx ▸ le_of_lt (hpt x)⟩
  have hrange_closed : IsClosed
      (Set.range (fun x : intervalDomainPoint => |u (t + τ) x - u τ x|)) :=
    (isCompact_range hf_cont).isClosed
  obtain ⟨x_max, hx_max⟩ :=
    Set.mem_range.mp (hrange_closed.csSup_mem hrange_ne hrange_bdd)
  rw [← hx_max]
  exact hpt x_max

/-- **OverlapUniqueForPID from the L² energy method (regime-conditional).**
Constructs `OverlapUniqueForPID p` from the L² energy chain which is
unconditional in the γ≥1 negative-sensitivity regime. -/
theorem overlapUniqueForPID_of_l2EnergyMethod
    {p : CM2Params}
    (hmethod : ShenWork.Paper2.IntervalDomainClassicalUniquenessL2EnergyMethod p) :
    OverlapUniqueForPID p := by
  intro u₀ hu₀ T₁ T₂ u₁ v₁ u₂ v₂ hsol₁ hsol₂ htrace₁ htrace₂ t ht0 ht_overlap x
  exact ShenWork.Paper2.intervalDomain_classicalSolution_overlap_unique_of_l2EnergyMethod
    hmethod hu₀ hsol₁ hsol₂ htrace₁ htrace₂ t ht0 ht_overlap x

end ShenWork.Paper2.GlueExtension
