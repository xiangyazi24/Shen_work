/-
  ShenWork/Paper3/IntervalDomainP31EventualSupBound.lean

  **Paper 3 Proposition 1.2 (P3.1) — the `eventualSupBound` analytic field (Gap A).**

  For the χ₀ ≤ 0 interval system, ANY global classical solution is eventually
  bounded in sup norm.  This is the genuinely-new analytic content of P3.1 that
  does NOT follow definitionally from Paper 2 Theorem 1.1's finite-`Tmax` bound
  (cf. `not_paper2_theorem_1_1_implies_paper3_proposition_1_2`).

  The key observation: for χ₀ ≤ 0 the chemotaxis term has the "good" sign, and the
  already-proved invariant region `Lemma_3_1_intervalDomain` (sup-norm
  non-increasing above the carrying capacity `(a/b)^{1/α}`) upgrades — via an
  INTERIOR reference time `t = 1` — to an eventual global bound.  Using an interior
  time means the argument needs NO initial-trace "approach" condition and is
  entirely INDEPENDENT of the χ<0 existence work: it takes the global solution as
  a hypothesis.

  This lets us discharge the `eventualSupBound` field of
  `IntervalDomainPaper3NegativeSensitivityFrontierData`, isolating the whole
  remaining P3.1 residual to the `globalSolution` (existence) field.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalLemma31Closure
import ShenWork.Paper2.IntervalDomainTheorem11ChiZeroUnconditional
import ShenWork.Paper2.IntervalChiNegHeadline
import ShenWork.Paper3.IntervalDomainStatementAssembly

open ShenWork.IntervalDomain
open ShenWork.Paper2
open Filter Topology

noncomputable section

namespace ShenWork.Paper3.P31EventualSupBound

/-- **Gap A, logistic regime `0 < a, 0 < b`.**  Any global classical solution of
the χ₀ ≤ 0 interval system is eventually bounded in sup norm.  `T₀ = 1` and
`M = max (‖u 1‖∞) ((a/b)^{1/α})`: above the carrying capacity the sup norm is
non-increasing (`Lemma_3_1_intervalDomain`), so it can never exceed its value at
the interior reference time `1`. -/
theorem eventualSupBound_of_global_posAB
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain p u v) :
    ∃ T₀ M : ℝ, ∀ t, T₀ ≤ t → intervalDomain.supNorm (u t) ≤ M := by
  refine ⟨1, max (intervalDomain.supNorm (u 1))
      ((p.a / p.b) ^ (1 / p.α)), ?_⟩
  intro t ht
  by_cases hbelow :
      intervalDomain.supNorm (u t) ≤ (p.a / p.b) ^ (1 / p.α)
  · exact le_trans hbelow (le_max_right _ _)
  · push Not at hbelow
    have hmono :
        SupNormNonincreasingOn intervalDomain u (Set.Ioc (0 : ℝ) t) :=
      (Lemma31Closure.Lemma_3_1_intervalDomain p hχ).1 ha hb (t + 1)
        (by linarith) u v (hglobal (t + 1) (by linarith)) t
        (by linarith) (by linarith) hbelow
    have h1mem : (1 : ℝ) ∈ Set.Ioc (0 : ℝ) t := ⟨by norm_num, ht⟩
    have htmem : t ∈ Set.Ioc (0 : ℝ) t := ⟨by linarith, le_rfl⟩
    exact le_trans (hmono 1 h1mem t htmem ht) (le_max_left _ _)

/-- **Gap A, degenerate regime `a = 0, b = 0`.**  With no reaction the sup norm is
non-increasing on every window, so it is eventually bounded by its value at the
interior reference time `1`. -/
theorem eventualSupBound_of_global_zeroAB
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : p.a = 0) (hb : p.b = 0)
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain p u v) :
    ∃ T₀ M : ℝ, ∀ t, T₀ ≤ t → intervalDomain.supNorm (u t) ≤ M := by
  refine ⟨1, intervalDomain.supNorm (u 1), ?_⟩
  intro t ht
  have hmono :
      SupNormNonincreasingOn intervalDomain u (Set.Ioo (0 : ℝ) (t + 1)) :=
    (Lemma31Closure.Lemma_3_1_intervalDomain p hχ).2 ha hb (t + 1)
      (by linarith) u v (hglobal (t + 1) (by linarith))
  have h1mem : (1 : ℝ) ∈ Set.Ioo (0 : ℝ) (t + 1) := ⟨by norm_num, by linarith⟩
  have htmem : t ∈ Set.Ioo (0 : ℝ) (t + 1) := ⟨by linarith, by linarith⟩
  exact hmono 1 h1mem t htmem ht

/-- **Gap A, degenerate regime `a = 0, 0 < b`.**  Pure damping (no growth): at a
spatial max the time slope is `≤ L·(0 − b·L^α) = −(L·b·L^α) ≤ 0` (with `L = max u >
0`), so the sup norm is non-increasing on every window and eventually bounded by its
value at the interior reference time `1`. -/
theorem eventualSupBound_of_global_zeroA_posB
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : p.a = 0) (hb : 0 < p.b)
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain p u v) :
    ∃ T₀ M : ℝ, ∀ t, T₀ ≤ t → intervalDomain.supNorm (u t) ≤ M := by
  refine ⟨1, intervalDomain.supNorm (u 1), ?_⟩
  intro t ht
  have hmono :
      SupNormNonincreasingOn intervalDomain u (Set.Ioo (0 : ℝ) (t + 1)) := by
    have hsol := hglobal (t + 1) (by linarith)
    refine Lemma31Closure.supNorm_nonincr_core hsol ?_
    intro s hs xs hxs hargmax
    have hmax : ∀ y, u s y ≤ u s ⟨xs, hxs⟩ := by
      intro y
      have hcontU : ContinuousOn (intervalDomainLift (u s)) (Set.Icc (0 : ℝ) 1) := by
        obtain ⟨_, _, _, _, hClosed, _, _⟩ := hsol.regularity
        exact (hClosed s hs).1.1.continuousOn
      have hbdd : BddAbove (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) :=
        (isCompact_Icc.image_of_continuousOn hcontU).bddAbove
      have huy : u s y = intervalDomainLift (u s) y.1 := by
        rw [intervalDomainLift,
          dif_pos (show (y.1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 from y.2), Subtype.coe_eta]
      have huq : u s ⟨xs, hxs⟩ = intervalDomainLift (u s) xs := by
        rw [intervalDomainLift, dif_pos hxs]
      rw [huy, huq, hargmax]
      exact le_csSup hbdd (Set.mem_image_of_mem _ y.2)
    have hsl := Lemma31Closure.max_point_slope_bound hχ hsol hs.1 hs.2 hmax
    have htd : intervalDomain.timeDeriv u s ⟨xs, hxs⟩
        = deriv (fun r => intervalDomainLift (u r) xs) s := by
      show deriv (fun r => u r ⟨xs, hxs⟩) s
        = deriv (fun r => intervalDomainLift (u r) xs) s
      congr 1; funext r; rw [intervalDomainLift, dif_pos hxs]
    rw [htd, ha] at hsl
    have hLeq : intervalDomainLift (u s) xs = u s ⟨xs, hxs⟩ := by
      rw [intervalDomainLift, dif_pos hxs]
    have hLpos : 0 < intervalDomainLift (u s) xs := by
      rw [hLeq]; exact hsol.u_pos' hs.1 hs.2
    have hLα : (0 : ℝ) < (intervalDomainLift (u s) xs) ^ p.α :=
      Real.rpow_pos_of_pos hLpos p.α
    have hrhs :
        intervalDomainLift (u s) xs
            * (0 - p.b * (intervalDomainLift (u s) xs) ^ p.α) ≤ 0 := by
      have hpos : 0 < intervalDomainLift (u s) xs
          * (p.b * (intervalDomainLift (u s) xs) ^ p.α) :=
        mul_pos hLpos (mul_pos hb hLα)
      have heq : intervalDomainLift (u s) xs
            * (0 - p.b * (intervalDomainLift (u s) xs) ^ p.α)
          = -(intervalDomainLift (u s) xs
              * (p.b * (intervalDomainLift (u s) xs) ^ p.α)) := by ring
      rw [heq]; linarith
    linarith [hsl, hrhs]
  have h1mem : (1 : ℝ) ∈ Set.Ioo (0 : ℝ) (t + 1) := ⟨by norm_num, by linarith⟩
  have htmem : t ∈ Set.Ioo (0 : ℝ) (t + 1) := ⟨by linarith, by linarith⟩
  exact hmono 1 h1mem t htmem ht

/-- **Field-by-field assembly of the P3.1 negative-sensitivity residual
(logistic regime `0 < a, 0 < b`).**  The `eventualSupBound` field (Gap A) is
DISCHARGED here from the invariant region; the `globalSolution` (existence +
initial trace) field is CARRIED as the hypothesis `hGlobal` — that is the entire
remaining P3.1 residual, supplied by Paper 2 χ≤0 existence once packaged. -/
theorem negativeSensitivityGlobalEventualBound_of_globalSolution_posAB
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b)
    (hGlobal :
      p.χ₀ ≤ 0 → 1 ≤ p.m →
        ∀ u₀ : intervalDomain.Point → ℝ,
          PositiveInitialDatum intervalDomain u₀ →
            ∃ u v : ℝ → intervalDomain.Point → ℝ,
              IsPaper2GlobalClassicalSolution intervalDomain p u v ∧
              InitialTrace intervalDomain u₀ u) :
    NegativeSensitivityGlobalEventualBound intervalDomain p := by
  intro hχ hm u₀ hu₀
  obtain ⟨u, v, hglobal, htrace⟩ := hGlobal hχ hm u₀ hu₀
  obtain ⟨T₀, M, hM⟩ := eventualSupBound_of_global_posAB p hχ ha hb hglobal
  exact ⟨u, v, hglobal, htrace, M, eventually_atTop.mpr ⟨T₀, hM⟩⟩

/-- **P3.1 (`Proposition_1_2 intervalDomain p`) in the logistic regime, reduced to
existence.**  Combines the field-by-field residual with the existing bridge
`Proposition_1_2_of_negativeSensitivityGlobalEventualBound`.  The only hypothesis
beyond `0 < a, 0 < b` is `hGlobal` (Paper 2 χ≤0 global existence + initial trace). -/
theorem proposition_1_2_of_globalSolution_posAB
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b)
    (hGlobal :
      p.χ₀ ≤ 0 → 1 ≤ p.m →
        ∀ u₀ : intervalDomain.Point → ℝ,
          PositiveInitialDatum intervalDomain u₀ →
            ∃ u v : ℝ → intervalDomain.Point → ℝ,
              IsPaper2GlobalClassicalSolution intervalDomain p u v ∧
              InitialTrace intervalDomain u₀ u) :
    Proposition_1_2 intervalDomain p :=
  Proposition_1_2_of_negativeSensitivityGlobalEventualBound intervalDomain p
    (negativeSensitivityGlobalEventualBound_of_globalSolution_posAB p ha hb hGlobal)

/-- **The key P3.1 reduction: `Proposition_1_2` from Paper 2 `Theorem_1_1`
(logistic regime `0 < a, 0 < b`).**  Paper 2's main theorem is PPID-typed and, for
`1 ≤ m`, supplies a GLOBAL classical solution + initial trace for every
`PaperPositiveInitialDatum`; Gap A upgrades its finite-window bound to the eventual
`IsPaper2Bounded`.  So P3.1 is a direct corollary of Paper 2 Theorem 1.1 — no PID
frontier/datum-class detour.  This closes P3.1 for ANY χ₀≤0 branch as soon as the
corresponding `Theorem_1_1 intervalDomain p` is available (χ₀=0 now; χ<0 when Codex
lands it). -/
theorem proposition_1_2_of_theorem_1_1_posAB
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b)
    (hT11 : Theorem_1_1 intervalDomain p) :
    Proposition_1_2 intervalDomain p := by
  intro hχ hm u₀ hu₀
  obtain ⟨hposBranch, _⟩ := hT11 hχ
  obtain ⟨_Tmax, _hTmax, u, v, _hsol, htrace, _hbound, hglobalImp⟩ :=
    hposBranch ha hb u₀ hu₀
  have hglobal := hglobalImp hm
  obtain ⟨_T₀, _M, hM⟩ := eventualSupBound_of_global_posAB p hχ ha hb hglobal
  exact ⟨u, v, hglobal, htrace, IsPaper2Bounded.of_forall_ge_supNorm_le hM⟩

/-- **P3.1 fully UNCONDITIONAL for the zero-sensitivity case `χ₀ = 0`.**  Corollary of
the Theorem 1.1 reduction applied to the axiom-clean χ₀=0 Paper 2 theorem.  A genuine
new Paper 3 headline with NO residual, independent of the χ<0 existence work. -/
theorem proposition_1_2_intervalDomain_chiZero
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ) :
    Proposition_1_2 intervalDomain p :=
  proposition_1_2_of_theorem_1_1_posAB p ha hb
    (intervalDomain_theorem_1_1_chiZero_unconditional p hχ0 ha hb hα hγ)

/-
  **χ<0 / full χ₀≤0 closure (ready one-liner, deferred to cold build).**
  The chi-nonpositive Paper 2 producers live in `IntervalDomainChiNonposHeadline`,
  whose EWA import closure is not compiled in a single-file `lake env lean` check,
  so the composition below is recorded here rather than committed unverified.  In a
  full (cold) build, add — verbatim — to close P3.1 for the whole χ₀≤0 regime,
  conditional on exactly Codex's χ<0 residual:

    theorem proposition_1_2_intervalDomain_chiNonpos_of_reducedCoreData
        (p : CM2Params) (hchi : p.χ₀ ≤ 0)
        (ha : 0 < p.a) (hb : 0 < p.b) (halpha : 1 ≤ p.α) (hgamma : 1 ≤ p.γ)
        (hnegCore : p.χ₀ < 0 → CoupledFluxResolverReducedCoreData p) :
        Proposition_1_2 intervalDomain p :=
      proposition_1_2_of_theorem_1_1_posAB p ha hb
        (paper2_theorem_1_1_intervalDomain_chiNonpos_strictLogistic_of_reducedCoreData
          p hchi ha hb halpha hgamma hnegCore)

  (import `ShenWork.Paper2.IntervalDomainChiNonposHeadline`).  Once Codex's
  `Theorem_1_1 intervalDomain p` (χ<0) is unconditional, apply
  `proposition_1_2_of_theorem_1_1_posAB` to it directly.
-/

/-- **P3.1 fully UNCONDITIONAL for the whole χ₀ ≤ 0 regime.**  Composes the Theorem 1.1
reduction with Codex's cold-verified unconditional χ≤0 Paper 2 headline
(`paper2_chiNonpos`, axiom sets exactly propext/Classical.choice/Quot.sound, uisai2
cold root build 9306 jobs OK).  This closes Paper 3 Proposition 1.2 for every χ₀ ≤ 0
(0<a, 0<b, 1≤α, 1≤γ), no residual — the full P3.1 headline. -/
theorem proposition_1_2_intervalDomain_chiNonpos
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ) :
    Proposition_1_2 intervalDomain p :=
  proposition_1_2_of_theorem_1_1_posAB p ha hb
    (ShenWork.Paper2.IntervalChiNegAssembly.paper2_chiNonpos p hχ ha hb hα hγ)

#print axioms eventualSupBound_of_global_posAB
#print axioms proposition_1_2_intervalDomain_chiNonpos

end ShenWork.Paper3.P31EventualSupBound
