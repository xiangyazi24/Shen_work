/-
  **Strong (PPID-typed) path to Theorem_1_1.**

  The EWA tower produces quantitative local existence for
  `PaperPositiveInitialDatum` (PPID), but the existing umbrella chain is
  typed over `PositiveInitialDatum` (PID).  Since PID ⊃ PPID (PID allows
  boundary-zero data like `x(1−x)`), we cannot fill the PID quantifier
  from the PPID factory.

  However, `Theorem_1_1` itself only quantifies over PPID, and the
  restart factory is only ever called at restart slices (which are PPID
  by compactness — `classicalSolution_slice_paperPositiveInitialDatum`).
  So the PID typing is a vestigial artifact.

  This file provides a PPID-typed parallel path, bypassing the PID umbrella
  entirely.  It is PURELY ADDITIVE — no existing definitions are modified.

  The private sup-norm helpers from `IntervalDomainMoserClosure` are
  duplicated here (they are pure real analysis, ~15 lines each, and
  inaccessible outside their defining file).

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainUniformContinuation
import ShenWork.Paper2.IntervalDomainTimeShift
import ShenWork.Paper2.IntervalDomainGlueExtension
import ShenWork.Paper2.IntervalDomainPiecewiseGlue
import ShenWork.Paper2.IntervalDomainPiecewiseClassical
import ShenWork.Paper2.IntervalDomainSupNormBridge
import ShenWork.Paper2.IntervalDomainL2UEnergyUniformGammaGeOne
import ShenWork.Paper2.IntervalDomainL2UFrontierAssembly
import ShenWork.Paper2.IntervalDomainL2UBoundedDatumUniformOfBounded
import ShenWork.Paper2.IntervalLemma31Closure
import ShenWork.PDE.IntervalDomainExistence
import ShenWork.Wiener.EWA.SourceChiNegUncondFix

open ShenWork.IntervalDomain
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.StrongPath

/-! ## §1  Sup-norm bound helpers (duplicated from MoserClosure, which marks them private)

These are pure real analysis — no PID/PPID dependence. -/

private theorem supNorm_le_initial_of_Ioc_monotone_and_approach
    {u : ℝ → intervalDomain.Point → ℝ} {u₀ : intervalDomain.Point → ℝ}
    {t : ℝ} (ht_pos : 0 < t)
    (hmono : SupNormNonincreasingOn intervalDomain u (Set.Ioc (0 : ℝ) t))
    (happroach : ∀ ε > 0, ∃ δ > 0, ∀ s, 0 < s → s < δ →
      intervalDomain.supNorm (u s) ≤ intervalDomain.supNorm u₀ + ε) :
    intervalDomain.supNorm (u t) ≤ intervalDomain.supNorm u₀ := by
  by_contra h_gt
  push_neg at h_gt
  set gap := intervalDomain.supNorm (u t) - intervalDomain.supNorm u₀ with hgap_def
  have hgap_pos : 0 < gap := by linarith
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := happroach (gap / 2) (by linarith)
  set s := min (δ / 2) (t / 2) with hs_def
  have hs_pos : 0 < s := lt_min (by linarith) (by linarith)
  have hs_lt_δ : s < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hs_le_t : s ≤ t := le_of_lt (lt_of_le_of_lt (min_le_right _ _) (by linarith))
  have hs_in_Ioc : s ∈ Set.Ioc (0 : ℝ) t := ⟨hs_pos, hs_le_t⟩
  have ht_in_Ioc : t ∈ Set.Ioc (0 : ℝ) t := ⟨ht_pos, le_rfl⟩
  have h_mono := hmono s hs_in_Ioc t ht_in_Ioc hs_le_t
  have h_approach := hδ_bound s hs_pos hs_lt_δ
  linarith

private theorem supNorm_le_initial_of_Ioo_monotone_and_approach
    {u : ℝ → intervalDomain.Point → ℝ} {u₀ : intervalDomain.Point → ℝ}
    {T : ℝ} (_hT : 0 < T)
    (hmono : SupNormNonincreasingOn intervalDomain u (Set.Ioo (0 : ℝ) T))
    (happroach : ∀ ε > 0, ∃ δ > 0, δ ≤ T ∧ ∀ s, 0 < s → s < δ →
      intervalDomain.supNorm (u s) ≤ intervalDomain.supNorm u₀ + ε)
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < T) :
    intervalDomain.supNorm (u t) ≤ intervalDomain.supNorm u₀ := by
  by_contra h_gt
  push_neg at h_gt
  set gap := intervalDomain.supNorm (u t) - intervalDomain.supNorm u₀ with hgap_def
  have hgap_pos : 0 < gap := by linarith
  obtain ⟨δ, hδ_pos, _hδ_le_T, hδ_bound⟩ :=
    happroach (gap / 2) (by linarith)
  set s := min (δ / 2) (t / 2) with hs_def
  have hs_pos : 0 < s := lt_min (by linarith) (by linarith)
  have hs_lt_δ : s < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hs_lt_t : s < t := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hs_lt_T : s < T := lt_trans hs_lt_t ht_lt
  have hs_in_Ioo : s ∈ Set.Ioo (0 : ℝ) T := ⟨hs_pos, hs_lt_T⟩
  have ht_in_Ioo : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht_pos, ht_lt⟩
  have h_mono := hmono s hs_in_Ioo t ht_in_Ioo hs_lt_t.le
  have h_approach := hδ_bound s hs_pos hs_lt_δ
  linarith

private theorem nonminimal_supNorm_bound
    (p : CM2Params)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    {u₀ : intervalDomain.Point → ℝ} {T : ℝ} (hT : 0 < T)
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (happroach : ∀ ε > 0, ∃ δ > 0, δ ≤ T ∧ ∀ s, 0 < s → s < δ →
      intervalDomain.supNorm (u s) ≤ intervalDomain.supNorm u₀ + ε) :
    ∀ t, 0 < t → t < T →
      intervalDomain.supNorm (u t) ≤
        max (intervalDomain.supNorm u₀) ((p.a / p.b) ^ (1 / p.α)) := by
  intro t ht_pos ht_lt
  by_cases h_below :
      intervalDomain.supNorm (u t) ≤ (p.a / p.b) ^ (1 / p.α)
  · exact le_trans h_below (le_max_right _ _)
  · push_neg at h_below
    have hL31 := Lemma31Closure.Lemma_3_1_intervalDomain p
    have hmono :=
      (hL31 hχ).1 ha hb T hT u v hsol t ht_pos ht_lt h_below
    have h_le_init :=
      supNorm_le_initial_of_Ioc_monotone_and_approach ht_pos hmono
        (fun ε hε => by
          obtain ⟨δ, hδ_pos, _hδ_le, hδ_bound⟩ := happroach ε hε
          exact ⟨δ, hδ_pos, hδ_bound⟩)
    exact le_trans h_le_init (le_max_left _ _)

private theorem minimal_supNorm_bound
    (p : CM2Params)
    (hχ : p.χ₀ ≤ 0) (ha : p.a = 0) (hb : p.b = 0)
    {u₀ : intervalDomain.Point → ℝ} {T : ℝ} (hT : 0 < T)
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (happroach : ∀ ε > 0, ∃ δ > 0, δ ≤ T ∧ ∀ s, 0 < s → s < δ →
      intervalDomain.supNorm (u s) ≤ intervalDomain.supNorm u₀ + ε) :
    ∀ t, 0 < t → t < T →
      intervalDomain.supNorm (u t) ≤ intervalDomain.supNorm u₀ := by
  intro t ht_pos ht_lt
  have hL31 := Lemma31Closure.Lemma_3_1_intervalDomain p
  have hmono := (hL31 hχ).2 ha hb T hT u v hsol
  exact supNorm_le_initial_of_Ioo_monotone_and_approach
    hT hmono happroach ht_pos ht_lt

private lemma exists_supBound_ppid
    {u₀ : intervalDomain.Point → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : intervalDomain.Point, |u₀ x| ≤ M := by
  obtain ⟨M₀, hM₀⟩ := hu₀.admissible.1
  refine ⟨max M₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x
  have hx_mem : |u₀ x| ∈ Set.range (fun y : intervalDomain.Point => |u₀ y|) :=
    ⟨x, rfl⟩
  exact (hM₀ hx_mem).trans (le_max_left _ _)

/-! ## §2  PPID-typed restart and glue

Close copy of `GlueExtension.restartAndGlueWorks_of_hypotheses`, but
the factory and initial datum are PPID-typed.  Two lines differ:
  * `classicalSolution_slice_positiveInitialDatum` → `…_paperPositiveInitialDatum`
  * `hOverlap` gets `.toPositive` -/

private theorem restartAndGlue_small_T₀_ppid
    {p : CM2Params} {M δ : ℝ} (_hM : 0 < M) (_hδ : 0 < δ)
    (hfactory : ∀ {w : intervalDomainPoint → ℝ},
      PaperPositiveInitialDatum intervalDomain w →
      (∀ x, |w x| ≤ M) →
      ∃ uw vw, IsPaper2ClassicalSolution intervalDomain p δ uw vw ∧
        InitialTrace intervalDomain w uw)
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hbound : ∀ x, |u₀ x| ≤ M)
    {T₀ : ℝ} (_hT₀ : 0 < T₀) (hsmall : T₀ ≤ δ / 2) :
    ∃ u' v',
      IsPaper2ClassicalSolution intervalDomain p (T₀ + δ / 2) u' v' ∧
        InitialTrace intervalDomain u₀ u' := by
  obtain ⟨uf, vf, hsolf, htracef⟩ := hfactory hu₀ hbound
  exact ⟨uf, vf,
    hsolf.restrict_horizon (by linarith) (by linarith), htracef⟩

theorem restartAndGlueWorks_ppid
    (p : CM2Params)
    (hRegShift : TimeShift.RegularityTimeShiftWorks)
    (hOverlap : GlueExtension.OverlapUniqueForPID p)
    (hTraceShift : GlueExtension.TimeShiftInitialTraceWorks)
    (hPR : PiecewiseGlue.PiecewiseClassicalWorks p)
    {M δ : ℝ} (hM : 0 < M) (hδ : 0 < δ)
    (hfactory : ∀ {w : intervalDomainPoint → ℝ},
      PaperPositiveInitialDatum intervalDomain w →
      (∀ x, |w x| ≤ M) →
      ∃ uw vw, IsPaper2ClassicalSolution intervalDomain p δ uw vw ∧
        InitialTrace intervalDomain w uw)
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hbound : ∀ x, |u₀ x| ≤ M)
    {T₀ : ℝ} (hT₀ : 0 < T₀)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T₀ u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hSupBound : ∀ t, 0 < t → t < T₀ → ∀ x : intervalDomainPoint, |u t x| ≤ M) :
    ∃ u' v',
      IsPaper2ClassicalSolution intervalDomain p (T₀ + δ / 2) u' v' ∧
        InitialTrace intervalDomain u₀ u' := by
  by_cases hsmall : T₀ ≤ δ / 2
  · exact restartAndGlue_small_T₀_ppid hM hδ hfactory hu₀ hbound hT₀ hsmall
  push_neg at hsmall
  set τ : ℝ := T₀ - δ / 4 with hτ_eq
  have hτ_pos : 0 < τ := by simp [hτ_eq]; linarith
  have hτ_lt : τ < T₀ := by simp [hτ_eq]; linarith
  have hτδ : T₀ + δ / 2 ≤ τ + δ := by simp [hτ_eq]; linarith
  -- KEY CHANGE: use PPID slice theorem instead of PID
  have hu_τ_ppid :=
    UniformContinuation.classicalSolution_slice_paperPositiveInitialDatum
      hsol ⟨hτ_pos, hτ_lt⟩
  obtain ⟨w, z, hsol_w, htrace_w⟩ :=
    hfactory hu_τ_ppid (hSupBound τ hτ_pos hτ_lt)
  have hsol_sh :=
    TimeShift.classicalSolution_timeShift hRegShift hsol hτ_pos hτ_lt
  have htr_sh := hTraceShift hsol hτ_pos hτ_lt
  have hminle : T₀ - τ ≤ δ := by simp [hτ_eq]; linarith
  -- KEY CHANGE: use .toPositive for OverlapUniqueForPID
  have hov : ∀ s, τ < s → s < T₀ →
      ∀ x : intervalDomainPoint,
        u s x = w (s - τ) x ∧ v s x = z (s - τ) x := by
    intro s hs1 hs2 x
    have h1 : 0 < s - τ := by linarith
    have h2 : s - τ < min (T₀ - τ) δ := by
      rw [min_eq_left hminle]; linarith
    have := hOverlap hu_τ_ppid.toPositive hsol_sh hsol_w htr_sh htrace_w
      (s - τ) h1 h2 x
    simp only [sub_add_cancel] at this; exact this
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
    · exact (hPR hT₀ hsol_w.T_pos hτ_pos hτ_lt hsol hsol_w
        (fun s hs hst x => (hov s hs hst x).1)
        (fun s hs hst x => (hov s hs hst x).2)
        (T₀ + δ / 2) (by linarith) (by simp only [hτ_eq]; linarith)).2.1
    · intro t x ht0 htT'
      by_cases h : t < T₀
      · have : u' t x = u t x := congrFun (hu'L t h) x
        rw [this]; exact hsol.u_pos' ht0 h
      · have hge : T₀ ≤ t := not_lt.mp h
        have : u' t x = w (t - τ) x := congrFun (hu'R t h) x
        rw [this]
        exact hsol_w.u_pos'
          (show 0 < t - τ by linarith)
          (show t - τ < δ by simp [hτ_eq] at hge ⊢; linarith)
    · intro t x ht0 htT'
      by_cases h : t < T₀
      · rw [congrFun (hv'L t h) x]; exact hsol.v_nonneg ht0 h
      · have hge : T₀ ≤ t := not_lt.mp h
        rw [congrFun (hv'R t h) x]
        exact hsol_w.v_nonneg
          (show 0 < t - τ by linarith)
          (show t - τ < δ by simp [hτ_eq] at hge ⊢; linarith)
    · intro t x ht0 htT' hx
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
    · intro t x ht0 htT' hx
      by_cases h : t < T₀
      · rw [hu'L t h, hv'L t h]; exact hsol.pde_v ht0 h hx
      · have hge : T₀ ≤ t := not_lt.mp h
        rw [hu'F t (by linarith) (by simp [hτ_eq] at hge ⊢; linarith),
          hv'F t (by linarith) (by simp [hτ_eq] at hge ⊢; linarith)]
        exact hsol_w.pde_v
          (by linarith)
          (by simp [hτ_eq] at hge ⊢; linarith) hx
    · intro t x ht0 htT' hx
      by_cases h : t < T₀
      · rw [hu'L t h, hv'L t h]; exact hsol.neumann ht0 h hx
      · have hge : T₀ ≤ t := not_lt.mp h
        rw [hu'F t (by linarith) (by simp [hτ_eq] at hge ⊢; linarith),
          hv'F t (by linarith) (by simp [hτ_eq] at hge ⊢; linarith)]
        exact hsol_w.neumann
          (by linarith)
          (by simp [hτ_eq] at hge ⊢; linarith) hx
  · intro ε hε
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

/-! ## §3  PPID-typed uniform local existence -/

theorem uniformLocalExistence_ppid
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ : 1 ≤ p.γ)
    (hQuant : ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PaperPositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v, IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u)
    {M : ℝ} (hM : 0 < M) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PaperPositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
      ∀ {T₀ : ℝ}, 0 < T₀ →
      ∀ {u v : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₀ u v →
        InitialTrace intervalDomain u₀ u →
          ∃ u' v',
            IsPaper2ClassicalSolution intervalDomain p (T₀ + δ) u' v' ∧
            InitialTrace intervalDomain u₀ u' := by
  set M' := SupNormBridge.regimeBound p M
  have hM' := SupNormBridge.regimeBound_pos p hM
  obtain ⟨δ, hδ, hex⟩ := hQuant M' hM'
  have hOverlap : GlueExtension.OverlapUniqueForPID p :=
    GlueExtension.overlapUniqueForPID_of_l2EnergyMethod
      (intervalDomainClassicalUniquenessL2EnergyMethod_of_boundedDatumUniform p
        (intervalDomainL2UBoundedDatumUniform_of_bounded
          (boundednessHypothesis_of_uniformSupBoundZeroM hγ
            (uniformLiftBoundZeroM_of_regime p hχ ha hb))))
  refine ⟨δ / 2, by linarith, ?_⟩
  intro u₀ hu₀ hbound T₀ hT₀ u v hsol htrace
  have hSupBound : ∀ t, 0 < t → t < T₀ → ∀ x : intervalDomainPoint, |u t x| ≤ M' :=
    SupNormBridge.interiorSupNorm_le_regimeBound
      p hχ ha hb hu₀.toPositive hM hbound hT₀ hsol htrace
  have hbound' : ∀ x, |u₀ x| ≤ M' := fun x =>
    le_trans (hbound x) (SupNormBridge.regimeBound_ge_M p M)
  exact restartAndGlueWorks_ppid p
    TimeShift.regularityTimeShiftWorks
    hOverlap
    GlueExtension.timeShiftInitialTraceWorks
    (PiecewiseClassical.piecewiseClassicalWorks p)
    hM' hδ (fun {w} hw hbw => hex hw hbw)
    hu₀ hbound' hT₀ hsol htrace hSupBound

/-! ## §4  PPID-typed ReachableArbitrarilyLong -/

theorem reachableArbitrarilyLong_ppid
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ : 1 ≤ p.γ)
    (hlocal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PaperPositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
    (hQuant : ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PaperPositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v, IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u)
    {u₀ : intervalDomain.Point → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀) :
    ShenWork.IntervalDomainExistence.ReachableArbitrarilyLong p u₀ := by
  intro T hT
  obtain ⟨M, hM_pos, hM_bound⟩ := exists_supBound_ppid hu₀
  obtain ⟨δ, hδ_pos, hExtend⟩ :=
    uniformLocalExistence_ppid p hχ ha hb hγ hQuant hM_pos
  obtain ⟨T₀, hT₀_pos, u₀sol, v₀sol, hsol₀, htrace₀⟩ := hlocal u₀ hu₀
  suffices h : ∀ n : ℕ, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p (T₀ + n * δ) u v ∧
      InitialTrace intervalDomain u₀ u by
    have hn : ∃ n : ℕ, T ≤ T₀ + n * δ := by
      use ⌈(T - T₀) / δ⌉₊
      have hle : (T - T₀) / δ ≤ ↑⌈(T - T₀) / δ⌉₊ := Nat.le_ceil _
      have := mul_le_mul_of_nonneg_right hle hδ_pos.le
      rw [div_mul_cancel₀ (T - T₀) (ne_of_gt hδ_pos)] at this
      linarith
    obtain ⟨n, hn⟩ := hn
    obtain ⟨un, vn, hsoln, htracen⟩ := h n
    exact ⟨hT, un, vn, hsoln.restrict_horizon hT (by linarith), htracen⟩
  intro n
  induction n with
  | zero =>
    simp only [Nat.zero_eq, Nat.cast_zero, zero_mul, add_zero]
    exact ⟨u₀sol, v₀sol, hsol₀, htrace₀⟩
  | succ n ih =>
    obtain ⟨un, vn, hsoln, htracen⟩ := ih
    have hTn_pos : 0 < T₀ + ↑n * δ := by positivity
    obtain ⟨u', v', hsol', htrace'⟩ :=
      hExtend hu₀ hM_bound hTn_pos hsoln htracen
    refine ⟨u', v', ?_, htrace'⟩
    convert hsol' using 1
    push_cast
    ring

/-! ## §5  Direct Theorem_1_1 from PPID inputs

Combines everything: PPID local + PPID quant → ReachableArbitrarilyLong →
GlobalSolutionGluingFromReachability (PID via `.toPositive`) → Theorem_1_1.
Private sup-norm helpers give the bound on the solution. -/

theorem Theorem_1_1_intervalDomain_of_ppid_local_and_quant
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ : 1 ≤ p.γ)
    (hlocal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PaperPositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
    (hQuant : ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PaperPositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v, IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u) :
    Theorem_1_1 intervalDomain p := by
  intro _hχ'
  have hReach : ∀ u₀, PaperPositiveInitialDatum intervalDomain u₀ →
      ShenWork.IntervalDomainExistence.ReachableArbitrarilyLong p u₀ :=
    fun u₀ hu₀ =>
      reachableArbitrarilyLong_ppid p hχ ha hb hγ hlocal hQuant hu₀
  have hGlue :
      ShenWork.IntervalDomainExistence.GlobalSolutionGluingFromReachability p :=
    GlobalSolutionGluingFromReachability_of_regime_gammaGeOne p hχ ha hb hγ
  constructor
  · -- Nonminimal: 0 < a, 0 < b
    intro _ha _hb u₀ hu₀paper
    by_cases hm : 1 ≤ p.m
    · have hglobal := hGlue u₀ hu₀paper.toPositive (hReach u₀ hu₀paper)
      rcases hglobal with ⟨u, v, hglob, htrace⟩
      have hT1 : (0 : ℝ) < 1 := by norm_num
      have hsol1 := hglob.classical hT1
      have happroach : ∀ ε > 0, ∃ δ > 0, δ ≤ (1 : ℝ) ∧
          ∀ s, 0 < s → s < δ →
            intervalDomain.supNorm (u s) ≤ intervalDomain.supNorm u₀ + ε :=
        fun ε hε =>
          ShenWork.IntervalDomainExistence.initialSupNormApproach_intervalDomain
            p u₀ hu₀paper.toPositive hu₀paper.toPositive.admissible.1
            hT1 hsol1 htrace hε
      refine ⟨1, hT1, u, v, hsol1, htrace, ?_, ?_⟩
      · exact nonminimal_supNorm_bound p hχ ha hb hT1 hsol1 happroach
      · intro _; exact hglob
    · obtain ⟨Tmax, hTmax, u, v, hsol, htrace⟩ := hlocal u₀ hu₀paper
      have happroach : ∀ ε > 0, ∃ δ > 0, δ ≤ Tmax ∧
          ∀ s, 0 < s → s < δ →
            intervalDomain.supNorm (u s) ≤ intervalDomain.supNorm u₀ + ε :=
        fun ε hε =>
          ShenWork.IntervalDomainExistence.initialSupNormApproach_intervalDomain
            p u₀ hu₀paper.toPositive hu₀paper.toPositive.admissible.1
            hTmax hsol htrace hε
      refine ⟨Tmax, hTmax, u, v, hsol, htrace, ?_, ?_⟩
      · exact nonminimal_supNorm_bound p hχ ha hb hTmax hsol happroach
      · intro hm'; exact False.elim (hm hm')
  · -- Minimal: a = 0, b = 0 — vacuous since 0 < a
    intro ha0 _hb0 _u₀ _hu₀paper
    exact absurd (ha0 ▸ ha) (lt_irrefl 0)

/-! ## §6  Wire to the STRONG χ₀<0 EWA construction

`ChiNegDatumUniformConstructionFaithful` is PID-typed and UNSATISFIABLE
from the EWA tower (the tower needs a uniform positive floor, which PID
data cannot supply). `ChiNegDatumUniformConstructionStrong` is PPID-typed
and IS satisfiable. We define `ChiNegDatumUniformConstructionPPID` (same
quantifier but returning solutions instead of EWA objects), bridge from
Strong via the regularity bootstrap, and prove the direct route to
`Theorem_1_1`. -/

def ChiNegDatumUniformConstructionPPID (p : CM2Params) : Prop :=
  ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
    ∀ {u0 : intervalDomain.Point → ℝ},
      PaperPositiveInitialDatum intervalDomain u0 →
      (∀ x, |u0 x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u0 u

private theorem localExistence_of_ppid_quant
    (hU : ChiNegDatumUniformConstructionPPID p)
    (u₀ : intervalDomain.Point → ℝ)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u₀ u := by
  obtain ⟨M, hM, hbnd⟩ := exists_supBound_ppid hu₀
  obtain ⟨δ, hδ, hfact⟩ := hU M hM
  obtain ⟨u, v, hsol, htrace⟩ := hfact hu₀ hbnd
  exact ⟨δ, hδ, u, v, hsol, htrace⟩

theorem chiNeg_theorem_1_1_ppid (p : CM2Params) (hchi : p.χ₀ < 0)
    (ha : 0 < p.a) (hb : 0 < p.b) (_hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hU : ChiNegDatumUniformConstructionPPID p) :
    Theorem_1_1 intervalDomain p :=
  Theorem_1_1_intervalDomain_of_ppid_local_and_quant
    p (le_of_lt hchi) ha hb hγ (localExistence_of_ppid_quant hU) hU

theorem ppid_of_strong
    (hU : ShenWork.EWA.ChiNegDatumUniformConstructionStrong p) :
    ChiNegDatumUniformConstructionPPID p := by
  intro M hM
  obtain ⟨δ, hδ, hbody⟩ := hU M hM
  refine ⟨δ, hδ, fun {u0} hu₀ hbd => ?_⟩
  obtain ⟨u_star, C⟩ := hbody hu₀ hbd
  have hreg :=
    ShenWork.IntervalCoupledRegularityBootstrap.regularityBootstrap_of_coupledDuhamel_reducedClassicalCore
      p C
  obtain ⟨v, hpos, hvnn, hpde_u, hpde_v, hbc, hclassreg, htrace⟩ := hreg
  exact ⟨ShenWork.EWA.realSlice u_star, v,
    IsPaper2ClassicalSolution.of_components hδ hclassreg hpos hvnn hpde_u hpde_v hbc,
    htrace⟩

theorem chiNeg_theorem_1_1_of_strong (p : CM2Params) (hchi : p.χ₀ < 0)
    (ha : 0 < p.a) (hb : 0 < p.b) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hU : ShenWork.EWA.ChiNegDatumUniformConstructionStrong p) :
    Theorem_1_1 intervalDomain p :=
  chiNeg_theorem_1_1_ppid p hchi ha hb hα hγ (ppid_of_strong hU)

#check @Theorem_1_1_intervalDomain_of_ppid_local_and_quant
#check @chiNeg_theorem_1_1_ppid
#check @chiNeg_theorem_1_1_of_strong

end ShenWork.Paper2.StrongPath
