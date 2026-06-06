/-
  hQuant reduction: QuantitativeLocalExistence (uniform δ(M) classical
  local existence) from

    * `ThresholdQuantitativeLocalExistence` — the Picard-contraction
      uniform existence time δ(M, c) on the threshold class
      {u₀ PID : |u₀| ≤ M, c ≤ u₀};
    * `ClassicalMinPersistence` — a quantitative strong-minimum-principle
      hypothesis: away from t = 0 the solution with initial trace u₀
      stays above a positive constant c(u₀, δ, t₁);
    * `hlocal` — per-datum classical local existence (the existing
      hMildLocal frontier output).

  ## Mathematical content

  The Picard contraction gives a uniform existence time on the threshold
  class: the contraction rate A(M)·√T + B(M)·T < 1 depends only on the
  ball radius M, and the crude mild-formulation positivity argument
  needs the Duhamel correction < inf u₀ ≥ c.  hQuant, however,
  quantifies over the larger class {u₀ PID : |u₀| ≤ M} with NO lower
  threshold (inf u₀ can be arbitrarily small, even 0 on the boundary),
  so a single Picard step cannot have a uniform duration there.

  Instead, ANY fixed horizon (δ = 1) is reached by finitely many
  restart-and-glue steps:

  1. The seed solution (hlocal) lives on [0, T₁]; restrict to
     T₀ = 3T₁/4 and set t₁ = 3T₁/8.
  2. Every restart slice u(τ) with τ ≥ t₁ satisfies
       |u(τ, ·)| ≤ regimeBound p M   (Lemma 3.1, proved), and
       c ≤ u(τ, ·)                   (ClassicalMinPersistence at (u₀,1,t₁)),
     so the threshold factory at (regimeBound p M, c) produces a fresh
     classical solution of FIXED duration δc > 0.
  3. Splicing at τ slightly below the current horizon
     (PiecewiseClassicalWorks + L² overlap uniqueness + time-shift, all
     proved) extends the horizon by δc/2 per step.
  4. Finitely many steps — the count is datum-dependent, which is fine:
     only the horizon must be uniform — reach the fixed horizon 1.

  The restart points satisfy τ ≥ Tn/2 ≥ T₀/2 ≥ t₁, so the persistence
  threshold applies at every restart.

  ## Output

  * `quantitativeLocalExistence_of_threshold_persistence_seed` — the
    hQuant statement from the three hypotheses (+ regime + hPCW).
  * `paper2_theorem_1_1_of_threshold_persistence_hlocal` — Theorem 1.1
    with hQuant replaced by Threshold + MinPersistence.

  `hPCW : PiecewiseGlue.PiecewiseClassicalWorks p` is taken as a
  hypothesis here (rather than discharged by
  `PiecewiseClassical.piecewiseClassicalWorks`) to keep this file's
  import closure green: IntervalDomainPiecewiseClassical.lean is
  committed but does not currently compile (af551f2 was committed
  unbuilt; ~25 elaboration errors).  Once it is repaired, a one-line
  wiring discharges `hPCW`.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainTheorem11Umbrella
import ShenWork.Paper2.IntervalDomainGlueExtension
import ShenWork.Paper2.IntervalDomainSupNormBridge

open ShenWork.IntervalDomain
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.QuantFromThreshold

/-! ## The frontier predicates -/

/-- **Threshold quantitative local existence** (Picard contraction
δ(M, c)): on the class of positive initial data bounded by `M` and
bounded BELOW by the threshold `c > 0`, there is a uniform classical
existence time `δ(M, c) > 0`.

This is exactly what the Picard contraction estimates deliver: the
contraction rate depends only on the ball radius `M`, and the crude
positivity argument for the mild solution requires the Duhamel
correction to stay below the initial lower bound `c`. -/
def ThresholdQuantitativeLocalExistence (p : CM2Params) : Prop :=
  ∀ M c : ℝ, 0 < M → 0 < c → ∃ δ : ℝ, 0 < δ ∧
    ∀ w : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain w →
      (∀ x, |w x| ≤ M) →
      (∀ x, c ≤ w x) →
      ∃ uw vw,
        IsPaper2ClassicalSolution intervalDomain p δ uw vw ∧
        InitialTrace intervalDomain w uw

/-- **Quantitative positivity persistence** (strong minimum principle):
for each positive initial datum `u₀` and each window `[t₁, δ]` with
`0 < t₁ < δ`, there is a constant `c = c(u₀, δ, t₁) > 0` below which no
classical solution with initial trace `u₀` can dip on `[t₁, T)` for any
horizon `T ∈ (t₁, δ]`.

Satisfiability: for the (CM) system, at an interior spatial minimum the
chemotaxis flux term is proportional to `u` and its gradient vanishes,
so `u_t ≥ Δu − K·u` with `K = K(sup-bound)`; the parabolic minimum
principle gives `min_x u(t, x) ≥ min_x u(t₁/2, x) · e^{−K(t − t₁/2)}`,
which is bounded below by a positive constant on the compact window
`[t₁, δ]`.  The constant is allowed to depend on the datum (through
`min_x u(t₁/2, x) > 0`), the window, and the parameters.  Note the
threshold `t₁ > 0` is essential: as `t → 0⁺` the spatial minimum can
tend to 0 when `inf u₀ = 0` (e.g. a datum vanishing on the boundary),
so a `t`-uniform constant on all of `(0, δ)` would be unsatisfiable. -/
def ClassicalMinPersistence (p : CM2Params) : Prop :=
  ∀ u₀ : intervalDomainPoint → ℝ,
    PositiveInitialDatum intervalDomain u₀ →
  ∀ δ t₁ : ℝ, 0 < t₁ → t₁ < δ →
  ∃ c : ℝ, 0 < c ∧
    ∀ T : ℝ, t₁ < T → T ≤ δ →
    ∀ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
      ∀ t, t₁ ≤ t → t < T → ∀ x : intervalDomainPoint, c ≤ u t x

/-! ## Restart-and-glue at an arbitrary slice

A generalization of the large-`T₀` case of
`GlueLargeCase.restartAndGlue_large_T₀_of_piecewise`: the restart point
`τ ∈ (0, T₀)` is arbitrary (subject to the overlap condition
`T₀ − τ ≤ δ`), and the fresh solution is GIVEN rather than produced by
a factory quantified over all `M`-bounded data.  This is what lets a
THRESHOLD factory drive the extension: the caller only needs to supply
the fresh solution for the one concrete slice `u(τ)`. -/
theorem restartAndGlue_at_slice
    (p : CM2Params)
    (hPiecewise : PiecewiseGlue.PiecewiseClassicalWorks p)
    (hRegShift : TimeShift.RegularityTimeShiftWorks)
    (hOverlap : GlueExtension.OverlapUniqueForPID p)
    (hTraceShift : GlueExtension.TimeShiftInitialTraceWorks)
    {u₀ : intervalDomainPoint → ℝ}
    (_hu₀ : PositiveInitialDatum intervalDomain u₀)
    {T₀ τ δ : ℝ} (hT₀ : 0 < T₀) (hδ : 0 < δ)
    (hτ_pos : 0 < τ) (hτ_lt : τ < T₀) (hτ_overlap : T₀ - τ ≤ δ)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T₀ u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    {uw vw : ℝ → intervalDomainPoint → ℝ}
    (hsol_w : IsPaper2ClassicalSolution intervalDomain p δ uw vw)
    (htrace_w : InitialTrace intervalDomain (u τ) uw)
    {T' : ℝ} (hT'_pos : 0 < T') (hT'_le : T' ≤ τ + δ) :
    ∃ u' v', IsPaper2ClassicalSolution intervalDomain p T' u' v' ∧
      InitialTrace intervalDomain u₀ u' := by
  -- The slice u(τ) is a positive initial datum.
  have hu_τ_pid : PositiveInitialDatum intervalDomain (u τ) :=
    UniformContinuation.classicalSolution_slice_positiveInitialDatum hsol
      ⟨hτ_pos, hτ_lt⟩
  -- Time-shifted solution on [0, T₀ − τ].
  have hsol_shift : IsPaper2ClassicalSolution intervalDomain p (T₀ - τ)
      (fun t x => u (t + τ) x) (fun t x => v (t + τ) x) :=
    TimeShift.classicalSolution_timeShift hRegShift hsol hτ_pos hτ_lt
  have htrace_shift : InitialTrace intervalDomain (u τ)
      (fun t x => u (t + τ) x) :=
    hTraceShift hsol hτ_pos hτ_lt
  -- Overlap uniqueness: u(s) = uw(s − τ) on (τ, T₀).
  have hmin : min (T₀ - τ) δ = T₀ - τ := min_eq_left hτ_overlap
  have hoverlap_u : ∀ s, τ < s → s < T₀ → ∀ x : intervalDomainPoint,
      u s x = uw (s - τ) x := by
    intro s hs_lo hs_hi x
    have hst := hOverlap hu_τ_pid hsol_shift hsol_w htrace_shift htrace_w
      (s - τ) (by linarith) (by rw [hmin]; linarith) x
    simp only [sub_add_cancel] at hst
    exact hst.1
  have hoverlap_v : ∀ s, τ < s → s < T₀ → ∀ x : intervalDomainPoint,
      v s x = vw (s - τ) x := by
    intro s hs_lo hs_hi x
    have hst := hOverlap hu_τ_pid hsol_shift hsol_w htrace_shift htrace_w
      (s - τ) (by linarith) (by rw [hmin]; linarith) x
    simp only [sub_add_cancel] at hst
    exact hst.2
  -- Splice is classical on [0, T'].
  have hsol' := hPiecewise hT₀ hδ hτ_pos hτ_lt hsol hsol_w
    hoverlap_u hoverlap_v T' hT'_pos hT'_le
  -- The splice keeps the initial trace u₀ (it equals u for small t).
  have htrace' : InitialTrace intervalDomain u₀
      (fun t x => if t < T₀ then u t x else uw (t - τ) x) := by
    intro ε hε
    obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := htrace ε hε
    refine ⟨min δ₁ T₀, lt_min hδ₁_pos hT₀, ?_⟩
    intro t ht0 htδ
    have htT₀ : t < T₀ := lt_of_lt_of_le htδ (min_le_right _ _)
    have htδ₁ : t < δ₁ := lt_of_lt_of_le htδ (min_le_left _ _)
    have hfun_eq : (fun x => (if t < T₀ then u t x else uw (t - τ) x) - u₀ x) =
        (fun x => u t x - u₀ x) := by
      funext x; rw [if_pos htT₀]
    simp only [intervalDomain] at hδ₁ ⊢
    rw [hfun_eq]; exact hδ₁ t ht0 htδ₁
  exact ⟨_, _, hsol', htrace'⟩

/-! ## The finite restart iteration -/

/-- **Finitely many threshold restarts reach a fixed horizon.**

For a fixed datum `u₀`, starting from a seed solution on `[0, T₀]`
(`t₁ < T₀ ≤ δ`, `t₁ ≤ T₀/2`), each step extends the horizon by `δc/2`
(capped at `δ`), where `δc` is the FIXED duration of the threshold
factory at `(M', c)`:

* the restart point is `τ = Tn − min(δc/4, Tn/2)`, so `τ ≥ Tn/2 ≥ t₁`
  and the persistence bound `c ≤ u(τ, ·)` applies;
* the slice is sup-bounded by `M'` (the per-datum interior sup bound);
* the overlap `Tn − τ ≤ δc/4 ≤ δc` makes the splice well-posed. -/
theorem reaches_fixed_horizon
    (p : CM2Params)
    (hPiecewise : PiecewiseGlue.PiecewiseClassicalWorks p)
    (hRegShift : TimeShift.RegularityTimeShiftWorks)
    (hOverlap : GlueExtension.OverlapUniqueForPID p)
    (hTraceShift : GlueExtension.TimeShiftInitialTraceWorks)
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {M' : ℝ} (_hM' : 0 < M')
    (hSupBound : ∀ T : ℝ, 0 < T →
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
        ∀ t, 0 < t → t < T → ∀ x : intervalDomainPoint, |u t x| ≤ M')
    {δ t₁ T₀ : ℝ} (hδ : 0 < δ) (ht₁ : 0 < t₁) (ht₁T₀ : t₁ < T₀)
    (hT₀δ : T₀ ≤ δ) (ht₁_half : t₁ ≤ T₀ / 2)
    {c : ℝ} (_hc : 0 < c)
    (hpersist : ∀ T : ℝ, t₁ < T → T ≤ δ →
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
        ∀ t, t₁ ≤ t → t < T → ∀ x : intervalDomainPoint, c ≤ u t x)
    {δc : ℝ} (hδc : 0 < δc)
    (hfactory : ∀ w : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain w →
      (∀ x, |w x| ≤ M') → (∀ x, c ≤ w x) →
      ∃ uw vw, IsPaper2ClassicalSolution intervalDomain p δc uw vw ∧
        InitialTrace intervalDomain w uw)
    (hseed : ∃ u v, IsPaper2ClassicalSolution intervalDomain p T₀ u v ∧
      InitialTrace intervalDomain u₀ u) :
    ∀ n : ℕ, ∃ u v,
      IsPaper2ClassicalSolution intervalDomain p
        (min δ (T₀ + n * (δc / 2))) u v ∧
      InitialTrace intervalDomain u₀ u := by
  intro n
  induction n with
  | zero =>
    obtain ⟨u, v, hsol, htrace⟩ := hseed
    have h0 : min δ (T₀ + (0 : ℕ) * (δc / 2)) = T₀ := by
      push_cast
      rw [zero_mul, add_zero]
      exact min_eq_right hT₀δ
    rw [h0]
    exact ⟨u, v, hsol, htrace⟩
  | succ n ih =>
    obtain ⟨u, v, hsol, htrace⟩ := ih
    by_cases hdone : δ ≤ T₀ + (n : ℝ) * (δc / 2)
    · -- Already capped at δ: the horizon does not change.
      have hn_eq : min δ (T₀ + (n : ℝ) * (δc / 2)) = δ := min_eq_left hdone
      have hsn_eq : min δ (T₀ + ((n : ℕ) + 1 : ℕ) * (δc / 2)) = δ := by
        apply min_eq_left
        push_cast
        nlinarith [hδc.le]
      rw [hsn_eq]
      rw [hn_eq] at hsol
      exact ⟨u, v, hsol, htrace⟩
    · push_neg at hdone
      -- Current horizon Tn = T₀ + n·(δc/2) < δ.
      set Tn : ℝ := T₀ + (n : ℝ) * (δc / 2) with hTn_def
      have hTn_eq : min δ (T₀ + (n : ℝ) * (δc / 2)) = Tn :=
        min_eq_right hdone.le
      rw [hTn_eq] at hsol
      have hn_nn : (0 : ℝ) ≤ (n : ℝ) * (δc / 2) :=
        mul_nonneg (Nat.cast_nonneg n) (by positivity)
      have hTn_ge : T₀ ≤ Tn := le_add_of_nonneg_right hn_nn
      have hTn_pos : 0 < Tn := by linarith
      have hTn_le_δ : Tn ≤ δ := hdone.le
      -- Restart point τ = Tn − min(δc/4, Tn/2).
      set m : ℝ := min (δc / 4) (Tn / 2) with hm_def
      have hm_pos : 0 < m := lt_min (by positivity) (by positivity)
      have hm_le_half : m ≤ Tn / 2 := min_le_right _ _
      have hm_le_δc4 : m ≤ δc / 4 := min_le_left _ _
      set τ : ℝ := Tn - m with hτ_def
      have hτ_pos : 0 < τ := by
        have : Tn / 2 < Tn := by linarith
        simp only [hτ_def]; linarith
      have hτ_lt : τ < Tn := by simp only [hτ_def]; linarith
      have hτ_ge_t₁ : t₁ ≤ τ := by
        have h2 : T₀ / 2 ≤ Tn / 2 := by linarith
        simp only [hτ_def]; linarith
      -- The restart slice u(τ): PID, sup-bounded, threshold-bounded.
      have hslice_pid : PositiveInitialDatum intervalDomain (u τ) :=
        UniformContinuation.classicalSolution_slice_positiveInitialDatum hsol
          ⟨hτ_pos, hτ_lt⟩
      have hslice_bound : ∀ x : intervalDomainPoint, |u τ x| ≤ M' :=
        hSupBound Tn hTn_pos u v hsol htrace τ hτ_pos hτ_lt
      have hslice_lb : ∀ x : intervalDomainPoint, c ≤ u τ x :=
        hpersist Tn (lt_of_lt_of_le ht₁T₀ hTn_ge) hTn_le_δ u v hsol htrace
          τ hτ_ge_t₁ hτ_lt
      -- Fresh solution of duration δc from the threshold factory.
      obtain ⟨uw, vw, hsol_w, htrace_w⟩ :=
        hfactory (u τ) hslice_pid hslice_bound hslice_lb
      -- Splice to the next horizon min δ (Tn + δc/2).
      have hcast : (((n : ℕ) + 1 : ℕ) : ℝ) * (δc / 2)
          = (n : ℝ) * (δc / 2) + δc / 2 := by push_cast; ring
      have hT'_pos : 0 < min δ (T₀ + ((n : ℕ) + 1 : ℕ) * (δc / 2)) := by
        apply lt_min hδ
        rw [hcast]
        linarith
      have hT'_le : min δ (T₀ + ((n : ℕ) + 1 : ℕ) * (δc / 2)) ≤ τ + δc := by
        -- Keep the `min`-term atomic (rewriting inside it would decouple it
        -- from the goal's `min`-atom for `linarith`); feed `hcast` as a
        -- linear equation instead.
        have h1 : min δ (T₀ + ((n : ℕ) + 1 : ℕ) * (δc / 2))
            ≤ T₀ + ((n : ℕ) + 1 : ℕ) * (δc / 2) := min_le_right _ _
        simp only [hτ_def]
        linarith [h1, hcast, hm_le_δc4]
      obtain ⟨u', v', hsol', htrace'⟩ :=
        restartAndGlue_at_slice p hPiecewise hRegShift hOverlap hTraceShift
          hu₀ hTn_pos hδc hτ_pos hτ_lt
          (by simp only [hτ_def]; linarith : Tn - τ ≤ δc)
          hsol htrace hsol_w htrace_w hT'_pos hT'_le
      exact ⟨u', v', hsol', htrace'⟩

/-! ## hQuant from the three hypotheses -/

/-- **Quantitative local existence from Threshold + MinPersistence +
per-datum seed (regime-conditional).**

The uniform horizon is `δ(M) = 1` — uniformity is for free once any
fixed horizon is reachable for every datum, because the restart count
may depend on the datum.  All glue ingredients (splice regularity,
L² overlap uniqueness, time-shift regularity and trace, interior
sup-norm bound) are proved in the repo from the regime hypotheses. -/
theorem quantitativeLocalExistence_of_threshold_persistence_seed
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hPCW : PiecewiseGlue.PiecewiseClassicalWorks p)
    (hThreshold : ThresholdQuantitativeLocalExistence p)
    (hPersist : ClassicalMinPersistence p)
    (hlocal : ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u) :
    ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u := by
  intro M hM
  refine ⟨1, one_pos, ?_⟩
  intro u₀ hu₀ hbound
  -- Glue ingredients (proved from the regime; hPCW is a hypothesis).
  have hOverlap : GlueExtension.OverlapUniqueForPID p :=
    GlueExtension.overlapUniqueForPID_of_l2EnergyMethod
      (intervalDomainClassicalUniquenessL2EnergyMethod_of_boundedDatumUniform p
        (intervalDomainL2UBoundedDatumUniform_of_bounded
          (boundednessHypothesis_of_uniformSupBoundZeroM hγ_ge_one
            (uniformLiftBoundZeroM_of_regime p hχ ha hb))))
  -- Seed.
  obtain ⟨T₁, hT₁, u, v, hsol, htrace⟩ := hlocal u₀ hu₀
  by_cases hbig : 1 ≤ T₁
  · exact ⟨u, v, hsol.restrict_horizon one_pos hbig, htrace⟩
  push_neg at hbig
  -- Per-datum constants.
  set M' : ℝ := SupNormBridge.regimeBound p M with hM'_def
  have hM' : 0 < M' := SupNormBridge.regimeBound_pos p hM
  have hSupBound : ∀ T : ℝ, 0 < T →
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
        ∀ t, 0 < t → t < T → ∀ x : intervalDomainPoint, |u t x| ≤ M' :=
    fun T hT u v hsol htr =>
      SupNormBridge.interiorSupNorm_le_regimeBound p hχ ha hb hu₀ hM hbound
        hT hsol htr
  -- Persistence threshold on the window [3T₁/8, 1].
  obtain ⟨c, hc, hpersist⟩ :=
    hPersist u₀ hu₀ 1 (3 * T₁ / 8) (by linarith) (by linarith)
  -- Threshold factory at (M', c).
  obtain ⟨δc, hδc, hfactory⟩ := hThreshold M' c hM' hc
  -- Seed restricted to T₀ = 3T₁/4.
  have hseed : ∃ u v,
      IsPaper2ClassicalSolution intervalDomain p (3 * T₁ / 4) u v ∧
      InitialTrace intervalDomain u₀ u :=
    ⟨u, v, hsol.restrict_horizon (by linarith) (by linarith), htrace⟩
  -- Iterate.
  have hreach := reaches_fixed_horizon p hPCW
    TimeShift.regularityTimeShiftWorks hOverlap
    GlueExtension.timeShiftInitialTraceWorks hu₀ hM' hSupBound
    (δ := 1) (t₁ := 3 * T₁ / 8) (T₀ := 3 * T₁ / 4)
    one_pos (by linarith) (by linarith) (by linarith) (by linarith)
    hc hpersist hδc (fun w hw hbw hlw => hfactory w hw hbw hlw) hseed
  -- Pick n with 1 ≤ 3T₁/4 + n·(δc/2).
  obtain ⟨n, hn⟩ := exists_nat_ge ((1 - 3 * T₁ / 4) / (δc / 2))
  have hδc2 : (0 : ℝ) < δc / 2 := by positivity
  have h1le : 1 ≤ 3 * T₁ / 4 + (n : ℝ) * (δc / 2) := by
    have := (div_le_iff₀ hδc2).mp hn
    linarith
  obtain ⟨u', v', hsol', htrace'⟩ := hreach n
  rw [min_eq_left h1le] at hsol'
  exact ⟨u', v', hsol', htrace'⟩

/-! ## End-to-end wiring -/

/-- **Paper 2 Theorem 1.1 from regime + hPCW + Threshold +
MinPersistence + `hlocal`.**

Compared to the `hQuant`-based final wirings, the uniform-δ(M)
quantitative local existence hypothesis is replaced by its two genuine
ingredients: the Picard threshold existence `δ(M, c)` and the
quantitative strong minimum principle.  The `hUniform` input of the
umbrella theorem is assembled from the derived hQuant via the proved
restart-and-glue machinery (as in
`FinalWiring.paper2_theorem_1_1_from_three`). -/
theorem paper2_theorem_1_1_of_threshold_persistence_hlocal
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hPCW : PiecewiseGlue.PiecewiseClassicalWorks p)
    (hThreshold : ThresholdQuantitativeLocalExistence p)
    (hPersist : ClassicalMinPersistence p)
    (hlocal : ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u) :
    Theorem_1_1 intervalDomain p := by
  apply Theorem_1_1_intervalDomain_via_regime_gammaGeOne_no_hextend_mge
    p hχ ha hb hγ_ge_one
  · exact hlocal
  · -- hUniform from the derived hQuant + restart-and-glue machinery.
    have hQuant := quantitativeLocalExistence_of_threshold_persistence_seed
      p hχ ha hb hγ_ge_one hPCW hThreshold hPersist hlocal
    intro M hM
    set M' := SupNormBridge.regimeBound p M
    have hM' := SupNormBridge.regimeBound_pos p hM
    obtain ⟨δ, hδ, hex⟩ := hQuant M' hM'
    have hRestart : RestartExtension.RestartAndGlueWorks p :=
      GlueExtension.restartAndGlueWorks_of_hypotheses p
        TimeShift.regularityTimeShiftWorks
        (GlueExtension.overlapUniqueForPID_of_l2EnergyMethod
          (intervalDomainClassicalUniquenessL2EnergyMethod_of_boundedDatumUniform p
            (intervalDomainL2UBoundedDatumUniform_of_bounded
              (boundednessHypothesis_of_uniformSupBoundZeroM hγ_ge_one
                (uniformLiftBoundZeroM_of_regime p hχ ha hb)))))
        GlueExtension.timeShiftInitialTraceWorks
        hPCW
    refine ⟨δ / 2, by linarith, ?_⟩
    intro u₀ hu₀ hbound T₀ hT₀ u v hsol htrace
    have hSupBound : ∀ t, 0 < t → t < T₀ →
        ∀ x : intervalDomainPoint, |u t x| ≤ M' :=
      SupNormBridge.interiorSupNorm_le_regimeBound p hχ ha hb hu₀ hM hbound
        hT₀ hsol htrace
    have hbound' : ∀ x, |u₀ x| ≤ M' := fun x =>
      le_trans (hbound x) (SupNormBridge.regimeBound_ge_M p M)
    have hfactory : ∀ {w : intervalDomainPoint → ℝ},
        PositiveInitialDatum intervalDomain w → (∀ x, |w x| ≤ M') →
        ∃ uw vw, IsPaper2ClassicalSolution intervalDomain p δ uw vw ∧
          InitialTrace intervalDomain w uw := fun hw hbw => hex hw hbw
    exact hRestart hM' hδ hfactory hu₀ hbound' hT₀ hsol htrace hSupBound

end ShenWork.Paper2.QuantFromThreshold
