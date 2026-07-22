import ShenWork.Paper1.WholeLineChiPosEntropyFarLeftCriterion
import ShenWork.Paper1.WholeLineWeightedRegularityChiNegPlateauPersistenceNatural

/-!
# Normal-family bridge for far-left entropy compactness

This file separates the genuinely parabolic input in
`ChiOneFarLeftEntropyCompactness` from its entropy/Liouville consumer.  A
space-time locally uniform normal-family limit carrying the entire weighted
entropy certificate is enough, and the persistent plateau together with the
canonical ceiling gives the uniform zeroth-order bounds on every translated
compact box.

The criterion observes its `orbit` through `coMovingPath`; consequently its
canonical argument is the laboratory-coordinate orbit
`wholeLineCauchyGlobalU p u₀`, not that orbit after a prior co-moving change
of variables.  The first lemma records the resulting double-speed identity.
-/

open Filter Real Set Topology

noncomputable section

namespace ShenWork.Paper1

/-- Applying the same co-moving observation twice observes the original orbit
at speed `2 * c`. -/
@[simp] theorem coMovingPath_coMovingPath
    (c : ℝ) (orbit : ℝ → ℝ → ℝ) (t z : ℝ) :
    coMovingPath c (coMovingPath c orbit) t z =
      coMovingPath (2 * c) orbit t z := by
  unfold coMovingPath
  apply congrArg (orbit t)
  ring

/-- A time-space translate of the orbit already observed in the frame moving
at speed `c`. -/
def chiOneFarLeftTranslate
    (c : ℝ) (orbit : ℝ → ℝ → ℝ)
    (timeShift spaceShift : ℕ → ℝ) (n : ℕ) (t x : ℝ) : ℝ :=
  coMovingPath c orbit (timeShift n + t) (spaceShift n + x)

/-- Local uniform convergence on every compact space-time box. -/
def SpaceTimeLocallyUniformConverges
    (seq : ℕ → ℝ → ℝ → ℝ) (limit : ℝ → ℝ → ℝ) : Prop :=
  ∀ R > 0, ∀ ε > 0, ∀ᶠ n in atTop,
    ∀ t ∈ Set.Icc (-R) R, ∀ x ∈ Set.Icc (-R) R,
      |seq n t x - limit t x| < ε

namespace SpaceTimeLocallyUniformConverges

theorem tendsto_at
    {seq : ℕ → ℝ → ℝ → ℝ} {limit : ℝ → ℝ → ℝ}
    (h : SpaceTimeLocallyUniformConverges seq limit) (t x : ℝ) :
    Tendsto (fun n : ℕ => seq n t x) atTop (𝓝 (limit t x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let R : ℝ := max |t| |x| + 1
  have hR : 0 < R := by
    dsimp only [R]
    have hmax : 0 ≤ max |t| |x| :=
      le_trans (abs_nonneg t) (le_max_left _ _)
    linarith
  have htR : t ∈ Set.Icc (-R) R := by
    apply abs_le.mp
    dsimp only [R]
    exact le_trans (le_max_left |t| |x|) (le_add_of_nonneg_right zero_le_one)
  have hxR : x ∈ Set.Icc (-R) R := by
    apply abs_le.mp
    dsimp only [R]
    exact le_trans (le_max_right |t| |x|) (le_add_of_nonneg_right zero_le_one)
  rcases eventually_atTop.1 (h R hR ε hε) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  simpa only [Real.dist_eq] using hN n hn t htR x hxR

/-- Closed interval bounds pass to a space-time locally uniform limit. -/
theorem bounds_of_eventually_box_bounds
    {seq : ℕ → ℝ → ℝ → ℝ} {limit : ℝ → ℝ → ℝ} {ell M : ℝ}
    (hconv : SpaceTimeLocallyUniformConverges seq limit)
    (hbound : ∀ R > 0, ∀ᶠ n in atTop,
      ∀ t ∈ Set.Icc (-R) R, ∀ x ∈ Set.Icc (-R) R,
        ell ≤ seq n t x ∧ seq n t x ≤ M) :
    ∀ t x, ell ≤ limit t x ∧ limit t x ≤ M := by
  intro t x
  let R : ℝ := max |t| |x| + 1
  have hR : 0 < R := by
    dsimp only [R]
    have hmax : 0 ≤ max |t| |x| :=
      le_trans (abs_nonneg t) (le_max_left _ _)
    linarith
  have htR : t ∈ Set.Icc (-R) R := by
    apply abs_le.mp
    dsimp only [R]
    exact le_trans (le_max_left |t| |x|) (le_add_of_nonneg_right zero_le_one)
  have hxR : x ∈ Set.Icc (-R) R := by
    apply abs_le.mp
    dsimp only [R]
    exact le_trans (le_max_right |t| |x|) (le_add_of_nonneg_right zero_le_one)
  have hev : ∀ᶠ n in atTop, ell ≤ seq n t x ∧ seq n t x ≤ M := by
    filter_upwards [hbound R hR] with n hn
    exact hn t htR x hxR
  constructor
  · exact le_of_tendsto_of_tendsto tendsto_const_nhds
      (hconv.tendsto_at t x) (hev.mono fun _ hn => hn.1)
  · exact le_of_tendsto (hconv.tendsto_at t x)
      (hev.mono fun _ hn => hn.2)

end SpaceTimeLocallyUniformConverges

/-- The exact normal-family output which is stronger than the origin-only
compactness interface consumed by the entropy Liouville argument. -/
structure ChiOneFarLeftEntropyNormalFamily
    (chi c ell k : ℝ) (orbit : ℝ → ℝ → ℝ) : Prop where
  extract :
    ∀ (timeShift spaceShift : ℕ → ℝ),
      (∀ n : ℕ, (n : ℝ) ≤ timeShift n) →
      (∀ n : ℕ, spaceShift n ≤ -(n : ℝ)) →
      ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
        ∃ (u ux uxx ut r rx rxx : ℝ → ℝ → ℝ),
          ChiOneEntireWeightedEntropyData chi c ell k 0
            u ux uxx ut r rx rxx ∧
          SpaceTimeLocallyUniformConverges
            (fun n => chiOneFarLeftTranslate c orbit timeShift spaceShift
              (subseq n)) u

/-- A genuine space-time normal-family limit supplies the origin convergence
required by `ChiOneFarLeftEntropyCompactness`. -/
theorem ChiOneFarLeftEntropyNormalFamily.to_entropyCompactness
    {chi c ell k : ℝ} {orbit : ℝ → ℝ → ℝ}
    (H : ChiOneFarLeftEntropyNormalFamily chi c ell k orbit) :
    ChiOneFarLeftEntropyCompactness chi c ell k orbit := by
  constructor
  intro timeShift spaceShift htime hspace
  obtain ⟨subseq, hsubseq, u, ux, uxx, ut, r, rx, rxx, Hentire, hconv⟩ :=
    H.extract timeShift spaceShift htime hspace
  refine ⟨subseq, hsubseq, u, ux, uxx, ut, r, rx, rxx, Hentire, ?_⟩
  simpa only [chiOneFarLeftTranslate, add_zero] using hconv.tendsto_at 0 0

/-- Eventual zeroth-order bounds in one co-moving left half-line. -/
def EventualCoMovingLeftBand
    (c ell M : ℝ) (orbit : ℝ → ℝ → ℝ) : Prop :=
  ∃ start cut : ℝ, ∀ t, start ≤ t → ∀ z, z ≤ cut →
    ell ≤ coMovingPath c orbit t z ∧ coMovingPath c orbit t z ≤ M

/-- A far-left band becomes a uniform band on each fixed compact box of any
translation sequence going to late times and to the far left. -/
theorem EventualCoMovingLeftBand.eventually_translated_box_bounds
    {c ell M : ℝ} {orbit : ℝ → ℝ → ℝ}
    (H : EventualCoMovingLeftBand c ell M orbit)
    {timeShift spaceShift : ℕ → ℝ}
    (htime : ∀ n : ℕ, (n : ℝ) ≤ timeShift n)
    (hspace : ∀ n : ℕ, spaceShift n ≤ -(n : ℝ)) :
    ∀ R > 0, ∀ᶠ n in atTop,
      ∀ t ∈ Set.Icc (-R) R, ∀ x ∈ Set.Icc (-R) R,
        ell ≤ chiOneFarLeftTranslate c orbit timeShift spaceShift n t x ∧
          chiOneFarLeftTranslate c orbit timeShift spaceShift n t x ≤ M := by
  obtain ⟨start, cut, H⟩ := H
  intro R _hR
  obtain ⟨Ntime, hNtime⟩ := exists_nat_ge (start + R)
  obtain ⟨Nspace, hNspace⟩ := exists_nat_ge (R - cut)
  filter_upwards [eventually_ge_atTop (max Ntime Nspace)] with n hn
  intro t ht x hx
  have hnTime : Ntime ≤ n := le_trans (le_max_left _ _) hn
  have hnSpace : Nspace ≤ n := le_trans (le_max_right _ _) hn
  have hnTimeReal : (Ntime : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnTime
  have hnSpaceReal : (Nspace : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnSpace
  have hlate : start ≤ timeShift n + t := by
    have hN : start + R ≤ (n : ℝ) := le_trans hNtime hnTimeReal
    have hn := htime n
    linarith [ht.1]
  have hleft : spaceShift n + x ≤ cut := by
    have hN : R - cut ≤ (n : ℝ) := le_trans hNspace hnSpaceReal
    have hn := hspace n
    linarith [hx.2]
  exact H (timeShift n + t) hlate (spaceShift n + x) hleft

/-- The already-proved persistent plateau floor and global stable ceiling give
the full zeroth-order band needed by parabolic compactness. -/
theorem exists_eventualCoMovingLeftBand_of_persistent_plateau
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    {N : ℕ} {c kappa kappaTilde D : ℝ}
    (hkappa : 0 < kappa) (hgap : kappa < kappaTilde) (hD : 1 ≤ D)
    (hpersist : ∀ n : ℕ, N ≤ n →
      ∀ r ∈ Set.Icc (0 : ℝ) (wholeLineCauchyGlobalStep p u₀), ∀ x,
        lowerBarrierPlateau kappa kappaTilde D x ≤
          wholeLineCauchyGlobalU p u₀
            (((n : ℝ) + 1) * wholeLineCauchyGlobalStep p u₀ + r)
            (x + c * (((n : ℝ) + 1) *
              wholeLineCauchyGlobalStep p u₀ + r))) :
    ∃ ell M : ℝ, 0 < ell ∧
      EventualCoMovingLeftBand c ell M (wholeLineCauchyGlobalU p u₀) := by
  obtain ⟨T, R, d, hd, hlower⟩ :=
    wholeLineCauchyGlobal_eventual_coMoving_left_floor_of_persistent_plateau
      p u₀ hkappa hgap hD hpersist
  refine ⟨d, wholeLineCauchyStableCeiling p u₀, hd, max T 0, R, ?_⟩
  intro t ht z hz
  have hT : T ≤ t := le_trans (le_max_left T 0) ht
  have ht0 : 0 ≤ t := le_trans (le_max_right T 0) ht
  constructor
  · simpa only [coMovingPath] using hlower t hT z hz
  · simpa only [coMovingPath] using
      wholeLineCauchyGlobal_le_stableCeiling p hregime u₀ hu₀ ht0 (z + c * t)

/-- The remaining analytic obligation for the canonical orbit, stated without
the origin-only weakening used by the final Liouville consumer. -/
def CanonicalChiOneFarLeftEntropyNormalFamily
    (p : CMParams) (chi c ell k : ℝ) (u₀ : WholeLineBUC) : Prop :=
  ChiOneFarLeftEntropyNormalFamily chi c ell k
    (wholeLineCauchyGlobalU p u₀)

/-- Once the canonical parabolic normal-family statement is supplied, the
sharp entropy theorem gives the real far-left convergence for `chi < 4`. -/
theorem uniformCoMovingLeftEquilibriumConvergence_chiPos_upto_four_of_normalFamily
    {p : CMParams} {chi c ell : ℝ} {u₀ : WholeLineBUC}
    (hchi : 0 ≤ chi) (hchi4 : chi < 4) (hell : 0 < ell)
    (Hnormal : ∀ k : ℝ, 0 < k → k < 1 →
      CanonicalChiOneFarLeftEntropyNormalFamily p chi c ell k u₀) :
    UniformCoMovingLeftEquilibriumConvergence c
      (wholeLineCauchyGlobalU p u₀) := by
  apply
    uniformCoMovingLeftEquilibriumConvergence_chiOne_full_sharp_range_of_entropyCompactness
      hchi hchi4 hell
  intro k hkpos hk1
  exact (Hnormal k hkpos hk1).to_entropyCompactness

section AxiomAudit

#print axioms coMovingPath_coMovingPath
#print axioms ChiOneFarLeftEntropyNormalFamily.to_entropyCompactness
#print axioms EventualCoMovingLeftBand.eventually_translated_box_bounds
#print axioms exists_eventualCoMovingLeftBand_of_persistent_plateau
#print axioms
  uniformCoMovingLeftEquilibriumConvergence_chiPos_upto_four_of_normalFamily

end AxiomAudit

end ShenWork.Paper1
