import ShenWork.Paper3.IntervalDomainGlobalTailTimeEquicontinuityM
import ShenWork.Paper3.IntervalDomainPersistenceGeneralMSupport
import ShenWork.Paper3.UniformFamilyCompactness

/-!
# Compactness of faithful general-power time translates

On every fixed symmetric time window, the spatial Holder modulus and the
uniform tail time modulus give joint equicontinuity.  Arzela--Ascoli then
extracts a subsequence converging uniformly on the whole spacetime rectangle.
-/

namespace ShenWork.Paper3

open Filter Set Topology
open ShenWork.IntervalDomain ShenWork.Paper2

noncomputable section

local instance intervalDomainTranslateMetricSpace : MetricSpace intervalDomainPoint :=
  inferInstanceAs (MetricSpace (Subtype (Icc (0 : ℝ) 1)))

/-- Compact spacetime rectangle for a symmetric translated-time window. -/
abbrev IntervalDomainTranslateStrip (L : ℝ) :=
  {s : ℝ // s ∈ Icc (-L) L} × intervalDomainPoint

/-- Every sequence of late times has a subsequence whose faithful translated
orbit converges uniformly on a prescribed compact symmetric time strip. -/
theorem intervalDomainM_globalBounded_timeTranslates_subseq
    (p : CM2Params)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v)
    {L : ℝ} (hL : 0 ≤ L)
    (times : ℕ → ℝ) (htimes : Tendsto times atTop atTop) :
    ∃ U : C(IntervalDomainTranslateStrip L, ℝ),
      ∃ phi : ℕ → ℕ, StrictMono phi ∧
        TendstoUniformly
          (fun n q ↦ u (times (phi n) + q.1.1) q.2) U atTop := by
  letI : CompactSpace {s : ℝ // s ∈ Icc (-L) L} :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  letI : CompactSpace intervalDomainPoint :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  obtain ⟨Ts, M, G, hTs, hM, hG, hsup, hholder⟩ :=
    intervalDomainM_globalBounded_eventual_holder p huv
  obtain ⟨Tt, hTt, htime⟩ :=
    intervalDomainM_globalBounded_eventual_time_equi p huv
  let T : ℝ := max Ts Tt
  have hT : 0 < T := lt_of_lt_of_le hTs (le_max_left Ts Tt)
  have hevent : ∀ᶠ n : ℕ in atTop, T + L ≤ times n :=
    htimes (eventually_ge_atTop (T + L))
  rcases eventually_atTop.1 hevent with ⟨N, hN⟩
  have hbase (n : ℕ) : T + L ≤ times (N + n) :=
    hN (N + n) (by omega)
  have hwindow (n : ℕ) (s : {s : ℝ // s ∈ Icc (-L) L}) :
      T ≤ times (N + n) + s.1 := by
    have hs := s.2.1
    linarith [hbase n]
  let f : ℕ → C(IntervalDomainTranslateStrip L, ℝ) := fun n ↦
    ⟨fun q ↦ u (times (N + n) + q.1.1) q.2, by
      let H : ℝ := times (N + n) + L + 1
      have hH : 0 < H := by
        dsimp [H]
        linarith [hT, hL, hbase n]
      have hsol := huv.classical H hH
      let F : ℝ × ℝ → ℝ := fun z ↦ intervalDomainLift (u z.1) z.2
      let arg : IntervalDomainTranslateStrip L → ℝ × ℝ := fun q ↦
        (times (N + n) + q.1.1, q.2.1)
      have harg : Continuous arg := by
        dsimp [arg]
        fun_prop
      have hmaps : MapsTo arg Set.univ
          (Ioo (0 : ℝ) H ×ˢ Icc (0 : ℝ) 1) := by
        intro q _hq
        have hqlo := hwindow n q.1
        have hqhi := q.1.2.2
        refine ⟨⟨lt_of_lt_of_le hT hqlo, ?_⟩, q.2.2⟩
        dsimp [H, arg]
        linarith
      have hcomp : ContinuousOn (F ∘ arg) Set.univ :=
        hsol.regularity.2.2.2.2.2.2.1.comp harg.continuousOn hmaps
      have hcontinuous : Continuous (F ∘ arg) := continuousOn_univ.mp hcomp
      have heq : (F ∘ arg) =
          (fun q : IntervalDomainTranslateStrip L ↦
            u (times (N + n) + q.1.1) q.2) := by
        funext q
        rcases q with ⟨s, ⟨y, hy⟩⟩
        change intervalDomainLift (u (times (N + n) + s.1)) y =
          u (times (N + n) + s.1) ⟨y, hy⟩
        rw [intervalDomainLift]
        split
        · congr
        · contradiction
      rw [← heq]
      exact hcontinuous⟩
  have hf_bound : ∀ n q, |f n q| ≤ M := by
    intro n q
    let H : ℝ := times (N + n) + L + 1
    have hH : 0 < H := by
      dsimp [H]
      linarith [hT, hL, hbase n]
    have hsol := huv.classical H hH
    have habs := intervalDomainM_abs_lift_le_supNorm hsol
      (show times (N + n) + q.1.1 ∈ Ioo (0 : ℝ) H by
        constructor
        · exact lt_of_lt_of_le hT (hwindow n q.1)
        · dsimp [H]
          linarith [q.1.2.2]) q.2.2
    have htail : Ts ≤ times (N + n) + q.1.1 :=
      (le_max_left Ts Tt).trans (hwindow n q.1)
    have hpoint : |u (times (N + n) + q.1.1) q.2| ≤
        intervalDomainSupNorm (u (times (N + n) + q.1.1)) := by
      simpa [f, intervalDomainLift, q.2.2] using habs
    exact hpoint.trans (hsup _ htail)
  have hspace_equi : UniformEquicontinuous
      (fun j : ℕ × {s : ℝ // s ∈ Icc (-L) L} ↦
        fun x : intervalDomainPoint ↦
          u (times (N + j.1) + j.2.1) x) := by
    let modulus : ℝ → ℝ := fun r ↦ G * |r| ^ ((1 : ℝ) / 2)
    have hmodulus : Tendsto modulus (𝓝 0) (𝓝 0) := by
      have hcont : ContinuousAt modulus 0 := by
        exact continuousAt_const.mul
          (continuous_abs.continuousAt.rpow_const (Or.inr (by norm_num)))
      have hzero : modulus 0 = 0 := by simp [modulus]
      change Tendsto modulus (𝓝 0) (𝓝 (modulus 0)) at hcont
      simpa only [hzero] using hcont
    refine Metric.uniformEquicontinuous_of_continuity_modulus modulus hmodulus
      (fun j : ℕ × {s : ℝ // s ∈ Icc (-L) L} ↦
        fun x : intervalDomainPoint ↦
          u (times (N + j.1) + j.2.1) x) ?_
    intro x y j
    have htj : Ts ≤ times (N + j.1) + j.2.1 :=
      (le_max_left Ts Tt).trans (hwindow j.1 j.2)
    have hxy := hholder _ htj x y
    have hdist : dist x y = |x.1 - y.1| := by rfl
    simpa [modulus, hdist, Real.dist_eq] using hxy
  have hf_equi : UniformEquicontinuous (fun n q ↦ f n q) := by
    rw [Metric.uniformEquicontinuous_iff]
    intro ε hε
    obtain ⟨δt, hδt, htmod⟩ := htime (ε / 2) (by linarith)
    rw [Metric.uniformEquicontinuous_iff] at hspace_equi
    obtain ⟨δx, hδx, hxmod⟩ := hspace_equi (ε / 2) (by linarith)
    refine ⟨min δt δx, lt_min hδt hδx, ?_⟩
    intro q q' hqq n
    have hqtime : dist q.1 q'.1 < δt := by
      rw [Prod.dist_eq, max_lt_iff] at hqq
      exact hqq.1.trans_le (min_le_left _ _)
    have hqspace : dist q.2 q'.2 < δx := by
      rw [Prod.dist_eq, max_lt_iff] at hqq
      exact hqq.2.trans_le (min_le_right _ _)
    have habstime :
        |(times (N + n) + q'.1.1) - (times (N + n) + q.1.1)| < δt := by
      change |q.1.1 - q'.1.1| < δt at hqtime
      simpa [abs_sub_comm] using hqtime
    have htfirst : Tt ≤ times (N + n) + q.1.1 :=
      (le_max_right Ts Tt).trans (hwindow n q.1)
    have htsecond : Tt ≤ times (N + n) + q'.1.1 :=
      (le_max_right Ts Tt).trans (hwindow n q'.1)
    have htimepart := htmod _ _ htfirst htsecond habstime q.2
    have hspacepart := hxmod q.2 q'.2 hqspace (n, q'.1)
    have htimepart' :
        |u (times (N + n) + q.1.1) q.2 -
          u (times (N + n) + q'.1.1) q.2| < ε / 2 := by
      simpa [abs_sub_comm] using htimepart
    have hspacepart' :
        |u (times (N + n) + q'.1.1) q.2 -
          u (times (N + n) + q'.1.1) q'.2| < ε / 2 := by
      simpa [Real.dist_eq] using hspacepart
    have htri :
        |u (times (N + n) + q.1.1) q.2 -
            u (times (N + n) + q'.1.1) q'.2| ≤
          |u (times (N + n) + q.1.1) q.2 -
            u (times (N + n) + q'.1.1) q.2| +
          |u (times (N + n) + q'.1.1) q.2 -
            u (times (N + n) + q'.1.1) q'.2| := by
      rw [show
        u (times (N + n) + q.1.1) q.2 -
            u (times (N + n) + q'.1.1) q'.2 =
          (u (times (N + n) + q.1.1) q.2 -
            u (times (N + n) + q'.1.1) q.2) +
          (u (times (N + n) + q'.1.1) q.2 -
            u (times (N + n) + q'.1.1) q'.2) by ring]
      exact abs_add_le _ _
    rw [Real.dist_eq]
    change |u (times (N + n) + q.1.1) q.2 -
      u (times (N + n) + q'.1.1) q'.2| < ε
    exact htri.trans_lt (by linarith)
  obtain ⟨U, psi, hpsi, hlim⟩ :=
    exists_uniform_convergent_subseq_of_uniformEquicontinuous
      f hf_bound hf_equi
  let phi : ℕ → ℕ := fun n ↦ N + psi n
  have hphi : StrictMono phi := by
    intro i j hij
    exact Nat.add_lt_add_left (hpsi hij) N
  refine ⟨U, phi, hphi, ?_⟩
  simpa [f, phi] using hlim

end

end ShenWork.Paper3

#print axioms ShenWork.Paper3.intervalDomainM_globalBounded_timeTranslates_subseq
