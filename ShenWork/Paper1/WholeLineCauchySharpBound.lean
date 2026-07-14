import ShenWork.Paper1.WholeLineCauchyGlobalGluing

open Filter Topology MeasureTheory Real Set Function
open scoped BoundedContinuousFunction Interval NNReal

noncomputable section

namespace ShenWork.Paper1

/-!
# Sharp maximum bound for the nonpositive-sensitivity Cauchy solution

The canonical global construction uses a deliberately larger clamp to obtain
a uniform contraction time.  This file separates that construction clamp from
the physical constant supersolution.  For `chi <= 0`, every constant `C >= 1`
which bounds the datum is preserved through all canonical restarts.  Taking
`C = max 1 M` gives Proposition 1.1, equation (1.8).
-/

/-- An arbitrary admissible constant ceiling is preserved by every recursive
datum and every canonical segment.  The larger construction clamp is supplied
independently by `wholeLineCauchyGlobalDatum_segment_bounds`. -/
theorem wholeLineCauchyGlobalDatum_segment_le_ceiling
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (C : ℝ) (hC1 : 1 ≤ C)
    (hmargin : 1 + max p.χ 0 * C ^ (p.m + p.γ - 1) ≤ C ^ p.α)
    (hinit : ∀ x, u₀.1 x ≤ C) :
    ∀ n,
      (∀ x, (wholeLineCauchyGlobalDatum p u₀ n).1 x ≤ C) ∧
      (∀ z x, (wholeLineCauchyGlobalSegment p u₀ n z).1 x ≤ C) := by
  intro n
  induction n with
  | zero =>
      have hdatum : ∀ x,
          (wholeLineCauchyGlobalDatum p u₀ 0).1 x ≤ C := by
        simpa [wholeLineCauchyGlobalDatum] using hinit
      refine ⟨hdatum, ?_⟩
      intro z x
      have hstrip :=
        (wholeLineCauchyGlobalDatum_segment_bounds
          p hregime u₀ hu₀ 0).2.1
      have hclosed := wholeLineCauchyBUCMildFixedPoint_stable_ceiling_Icc
        p hregime (wholeLineCauchyGlobalClamp_pos p u₀).le
        (wholeLineCauchyGlobalSegmentTime_pos p u₀)
        (wholeLineCauchyGlobalDatum p u₀ 0)
        (wholeLineCauchyGlobalSegmentTime_rate p u₀)
        (by simpa [wholeLineCauchyGlobalSegment] using hstrip)
        hC1 hmargin hdatum
      have hext := wholeLineBUCTrajectoryExtend_eq
        (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
        (wholeLineCauchyGlobalSegment p u₀ 0) z.2
      rw [← hext]
      simpa [wholeLineCauchyGlobalSegment] using hclosed z.1 z.2 x
  | succ n ih =>
      let δ := wholeLineCauchyGlobalStep p u₀
      let zδ : Set.Icc (0 : ℝ) (wholeLineCauchyGlobalSegmentTime p u₀) :=
        ⟨δ, (wholeLineCauchyGlobalStep_pos p u₀).le,
          by
            dsimp [δ, wholeLineCauchyGlobalStep]
            linarith [wholeLineCauchyGlobalSegmentTime_pos p u₀]⟩
      have hdatum : ∀ x,
          (wholeLineCauchyGlobalDatum p u₀ (n + 1)).1 x ≤ C := by
        intro x
        simpa [wholeLineCauchyGlobalDatum, wholeLineCauchyGlobalSegment,
          zδ, δ] using ih.2 zδ x
      refine ⟨by simpa [Nat.succ_eq_add_one] using hdatum, ?_⟩
      intro z x
      have hstrip :=
        (wholeLineCauchyGlobalDatum_segment_bounds
          p hregime u₀ hu₀ (n + 1)).2.1
      have hclosed := wholeLineCauchyBUCMildFixedPoint_stable_ceiling_Icc
        p hregime (wholeLineCauchyGlobalClamp_pos p u₀).le
        (wholeLineCauchyGlobalSegmentTime_pos p u₀)
        (wholeLineCauchyGlobalDatum p u₀ (n + 1))
        (wholeLineCauchyGlobalSegmentTime_rate p u₀)
        (by simpa [wholeLineCauchyGlobalSegment] using hstrip)
        hC1 hmargin hdatum
      have hext := wholeLineBUCTrajectoryExtend_eq
        (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
        (wholeLineCauchyGlobalSegment p u₀ (n + 1)) z.2
      rw [← hext]
      simpa [wholeLineCauchyGlobalSegment] using hclosed z.1 z.2 x

/-- The glued canonical solution inherits any admissible constant ceiling. -/
theorem wholeLineCauchyGlobal_le_ceiling
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (C : ℝ) (hC1 : 1 ≤ C)
    (hmargin : 1 + max p.χ 0 * C ^ (p.m + p.γ - 1) ≤ C ^ p.α)
    (hinit : ∀ x, u₀.1 x ≤ C)
    {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    wholeLineCauchyGlobalU p u₀ t x ≤ C := by
  let n := wholeLineCauchyGlobalIndex p u₀ t
  let q := wholeLineCauchyGlobalLocalTime p u₀ t
  let z : Set.Icc (0 : ℝ) (wholeLineCauchyGlobalSegmentTime p u₀) :=
    ⟨q, wholeLineCauchyGlobalLocalTime_nonneg p u₀ ht,
      (wholeLineCauchyGlobalLocalTime_lt_segmentTime p u₀ ht).le⟩
  have hbound :=
    (wholeLineCauchyGlobalDatum_segment_le_ceiling
      p hregime u₀ hu₀ C hC1 hmargin hinit n).2 z x
  have heq := congrArg (fun w : WholeLineBUC => w.1 x)
    (wholeLineCauchyGlobalBUC_eq_segment p u₀ ht)
  have heq' : (wholeLineCauchyGlobalBUC p u₀ t).1 x =
      (wholeLineCauchyGlobalSegment p u₀ n z).1 x := by
    simpa [n, q, z] using heq
  change (wholeLineCauchyGlobalBUC p u₀ t).1 x ≤ C
  rw [heq']
  exact hbound

/-- Proposition 1.1, equation (1.8), for the canonical solution in the
nonpositive-sensitivity branch. -/
theorem wholeLineCauchyGlobal_le_max_one_of_chi_nonpos
    (p : CMParams) (hχ : p.χ ≤ 0)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (M : ℝ) (hinit : ∀ x, u₀.1 x ≤ M)
    {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    wholeLineCauchyGlobalU p u₀ t x ≤ max 1 M := by
  let C : ℝ := max 1 M
  have hC1 : 1 ≤ C := by
    dsimp [C]
    exact le_max_left _ _
  have hmargin :
      1 + max p.χ 0 * C ^ (p.m + p.γ - 1) ≤ C ^ p.α := by
    have hpow : 1 ≤ C ^ p.α :=
      Real.one_le_rpow hC1 (zero_le_one.trans p.hα)
    simpa [max_eq_right hχ] using hpow
  apply wholeLineCauchyGlobal_le_ceiling p
    (WholeLineCauchyCeilingRegime.of_nonpositive hχ)
    u₀ hu₀ C hC1 hmargin
  · intro y
    exact (hinit y).trans (le_max_right _ _)
  · exact ht

/-- The canonical global solution simultaneously realizes the paper's
nonnegative Cauchy solution predicate and the sharp maximum bound (1.8). -/
theorem exists_wholeLineGlobalNonnegativeCauchySolution_sharpBound_of_chi_nonpos
    (p : CMParams) (hχ : p.χ ≤ 0)
    (u₀ : ℝ → ℝ) (hu₀ : PaperNonnegativeInitialDatum u₀) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalNonnegativeCauchySolutionFrom p u₀ u v ∧
      (∀ M, (∀ x, u₀ x ≤ M) →
        ∀ t x, 0 ≤ t → u t x ≤ max 1 M) := by
  let w : WholeLineBUC := wholeLineBUCOfPaperCUnifBdd u₀ hu₀.1
  have hw0 : ∀ x, 0 ≤ w.1 x := by
    intro x
    simpa [w] using hu₀.2 x
  let hregime : WholeLineCauchyCeilingRegime p :=
    WholeLineCauchyCeilingRegime.of_nonpositive hχ
  refine ⟨wholeLineCauchyGlobalU p w, wholeLineCauchyGlobalV p w,
    ?_, ?_⟩
  · simpa [w] using
      wholeLineCauchyGlobal_isGlobalNonnegativeCauchySolutionFrom
        p hregime w hw0
  · intro M hM t x ht
    exact wholeLineCauchyGlobal_le_max_one_of_chi_nonpos
      p hχ w hw0 M (by simpa [w] using hM) ht x

section WholeLineCauchySharpBoundAxiomAudit

#print axioms wholeLineCauchyGlobalDatum_segment_le_ceiling
#print axioms wholeLineCauchyGlobal_le_ceiling
#print axioms wholeLineCauchyGlobal_le_max_one_of_chi_nonpos
#print axioms exists_wholeLineGlobalNonnegativeCauchySolution_sharpBound_of_chi_nonpos

end WholeLineCauchySharpBoundAxiomAudit

end ShenWork.Paper1
