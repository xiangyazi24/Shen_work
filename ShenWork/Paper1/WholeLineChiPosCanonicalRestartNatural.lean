import ShenWork.Paper1.WholeLineWeightedRegularityChiNegLeftEquilibriumNatural

open Filter Topology Set Real

noncomputable section

namespace ShenWork.Paper1

/-!
# Positive-time whole-line restarts for the positive-sensitivity squeeze

The rectangle argument repeatedly restarts the canonical whole-line orbit at
an arbitrary positive time.  This file packages the joint continuity, range,
strict positivity, and classical parabolic regularity of that restart once,
so every squeeze round can use the finite-slab comparison directly.
-/

/-- Regularity and range data for the canonical orbit restarted at `t₀`.
The clamp by `max s 0` only supplies a globally continuous representative;
on the forward half-line it is exactly the physical restart. -/
structure WholeLineChiPosCanonicalRestartData
    (p : CMParams) (u₀ : WholeLineBUC) (t₀ G : ℝ) where
  q : ℝ → ℝ → ℝ
  eq_global : ∀ ⦃s : ℝ⦄, 0 ≤ s → ∀ x,
    q s x = wholeLineCauchyGlobalU p u₀ (t₀ + s) x
  continuous : Continuous (fun z : ℝ × ℝ => q z.1 z.2)
  mem_Icc : ∀ ⦃s : ℝ⦄, 0 ≤ s → ∀ x, q s x ∈ Set.Icc (0 : ℝ) G
  positive : ∀ ⦃s x : ℝ⦄, 0 < s → 0 < q s x
  time_operator : ∀ ⦃s x : ℝ⦄, 0 < s →
    HasDerivAt (fun r : ℝ => q r x)
      (paperWaveOperator p 0 (q s) (q s) x) s
  slice_contDiff_two : ∀ ⦃s : ℝ⦄, 0 < s → ContDiff ℝ 2 (q s)

/-- The time derivative of packaged restart data, stated using `deriv`. -/
theorem WholeLineChiPosCanonicalRestartData.time_hasDerivAt
    {p : CMParams} {u₀ : WholeLineBUC} {t₀ G : ℝ}
    (d : WholeLineChiPosCanonicalRestartData p u₀ t₀ G)
    {s x : ℝ} (hs : 0 < s) :
    HasDerivAt (fun r : ℝ => d.q r x)
      (deriv (fun r : ℝ => d.q r x) s) s :=
  (d.time_operator hs).differentiableAt.hasDerivAt

/-- First spatial differentiability of every positive restart slice. -/
theorem WholeLineChiPosCanonicalRestartData.space_hasDerivAt
    {p : CMParams} {u₀ : WholeLineBUC} {t₀ G : ℝ}
    (d : WholeLineChiPosCanonicalRestartData p u₀ t₀ G)
    {s x : ℝ} (hs : 0 < s) :
    HasDerivAt (fun y : ℝ => d.q s y)
      (deriv (fun y : ℝ => d.q s y) x) x :=
  ((d.slice_contDiff_two hs).differentiable (by norm_num)).differentiableAt.hasDerivAt

/-- Second spatial differentiability of every positive restart slice. -/
theorem WholeLineChiPosCanonicalRestartData.space_deriv_hasDerivAt
    {p : CMParams} {u₀ : WholeLineBUC} {t₀ G : ℝ}
    (d : WholeLineChiPosCanonicalRestartData p u₀ t₀ G)
    {s x : ℝ} (hs : 0 < s) :
    HasDerivAt (fun y : ℝ => deriv (fun z : ℝ => d.q s z) y)
      (deriv (fun y : ℝ => deriv (fun z : ℝ => d.q s z) y) x) x :=
  (d.slice_contDiff_two hs).differentiable_deriv_two.differentiableAt.hasDerivAt

/-- Expanded nondivergence-form PDE satisfied by packaged restart data. -/
theorem WholeLineChiPosCanonicalRestartData.expanded_pde
    {p : CMParams} {u₀ : WholeLineBUC} {t₀ G : ℝ}
    (d : WholeLineChiPosCanonicalRestartData p u₀ t₀ G)
    {s x : ℝ} (hs : 0 < s) :
    deriv (fun r : ℝ => d.q r x) s =
      deriv (fun y : ℝ => deriv (fun z : ℝ => d.q s z) y) x +
        (0 : ℝ) * deriv (fun y : ℝ => d.q s y) x -
        p.χ *
          (p.m * (d.q s x) ^ (p.m - 1) *
              deriv (fun y : ℝ => d.q s y) x *
              deriv (frozenElliptic p (d.q s)) x +
            (d.q s x) ^ p.m *
              (frozenElliptic p (d.q s) x - (d.q s x) ^ p.γ)) +
        reactionFun p.α (d.q s x) := by
  have hiter : iteratedDeriv 2 (d.q s) x =
      deriv (fun y : ℝ => deriv (fun z : ℝ => d.q s z) y) x := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
      iteratedDeriv_one]
  calc
    deriv (fun r : ℝ => d.q r x) s =
        paperWaveOperator p 0 (d.q s) (d.q s) x := (d.time_operator hs).deriv
    _ = iteratedDeriv 2 (d.q s) x +
          (0 : ℝ) * deriv (d.q s) x -
          p.χ *
            (p.m * (d.q s x) ^ (p.m - 1) * deriv (d.q s) x *
                deriv (frozenElliptic p (d.q s)) x +
              (d.q s x) ^ p.m *
                (frozenElliptic p (d.q s) x - (d.q s x) ^ p.γ)) +
          reactionFun p.α (d.q s x) :=
      paperWaveOperator_fixedPoint_eq_bufferedForm_of_pos p (d.positive hs)
    _ = _ := by rw [hiter]

/-- Construct the packaged restart from the canonical global solution. -/
def wholeLineCauchyGlobal_positiveRestartData
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (hleft : StrictlyPositiveAtLeft u₀.1)
    {t₀ G : ℝ} (ht₀ : 0 < t₀)
    (hupper : ∀ ⦃t : ℝ⦄, 0 ≤ t → ∀ x,
      wholeLineCauchyGlobalU p u₀ t x ≤ G) :
    WholeLineChiPosCanonicalRestartData p u₀ t₀ G := by
  let q : ℝ → ℝ → ℝ := fun s x =>
    wholeLineCauchyGlobalU p u₀ (t₀ + max s 0) x
  refine
    { q := q
      eq_global := ?_
      continuous := ?_
      mem_Icc := ?_
      positive := ?_
      time_operator := ?_
      slice_contDiff_two := ?_ }
  · intro s hs x
    simp [q, max_eq_left hs]
  · rw [continuous_iff_continuousAt]
    intro z
    have hphys : 0 < t₀ + max z.1 0 := by
      have : 0 ≤ max z.1 0 := le_max_right _ _
      linarith
    have hbase := wholeLineCauchyGlobalU_joint_hasFDerivAt_positive
      p hregime u₀ hu₀ hphys (x := z.2)
    have hmap : ContinuousAt
        (fun a : ℝ × ℝ => (t₀ + max a.1 0, a.2)) z := by
      fun_prop
    simpa [q, Function.comp_def] using
      hbase.continuousAt.comp
        (f := fun a : ℝ × ℝ => (t₀ + max a.1 0, a.2)) hmap
  · intro s hs x
    have hphys : 0 ≤ t₀ + s := by linarith
    constructor
    · simpa [q, max_eq_left hs] using
        wholeLineCauchyGlobal_nonnegative p hregime u₀ hu₀ hphys x
    · simpa [q, max_eq_left hs] using hupper hphys x
  · intro s x hs
    have hphys : 0 < t₀ + s := by linarith
    simpa [q, max_eq_left hs.le] using
      wholeLineCauchyGlobal_pos_of_posAtBot
        p hregime u₀ hu₀ hleft hphys x
  · intro s x hs
    have hphysical : 0 < t₀ + s := by linarith
    have hraw :=
      wholeLineCauchyGlobal_coMovingRestart_hasDerivAt_paperWaveOperator
        p hregime u₀ hu₀ 0 t₀ hphysical x
    have hraw' : HasDerivAt
        (fun r : ℝ => wholeLineCauchyGlobalU p u₀ (t₀ + r) x)
        (paperWaveOperator p 0
          (fun y => wholeLineCauchyGlobalU p u₀ (t₀ + s) y)
          (fun y => wholeLineCauchyGlobalU p u₀ (t₀ + s) y) x) s := by
      simpa using hraw
    have hev : (fun r : ℝ => q r x) =ᶠ[nhds s]
        fun r => wholeLineCauchyGlobalU p u₀ (t₀ + r) x := by
      filter_upwards [Ioi_mem_nhds hs] with r hr
      change 0 < r at hr
      simp [q, max_eq_left hr.le]
    have hcongr := hraw'.congr_of_eventuallyEq hev
    simpa [q, max_eq_left hs.le] using hcongr
  · intro s hs
    have hphysical : 0 < t₀ + s := by linarith
    simpa [q, max_eq_left hs.le] using
      wholeLineCauchyGlobal_coMovingRestart_contDiff_two
        p hregime u₀ hu₀ 0 t₀ hphysical

section AxiomAudit

#print axioms WholeLineChiPosCanonicalRestartData.time_hasDerivAt
#print axioms WholeLineChiPosCanonicalRestartData.space_hasDerivAt
#print axioms WholeLineChiPosCanonicalRestartData.space_deriv_hasDerivAt
#print axioms WholeLineChiPosCanonicalRestartData.expanded_pde
#print axioms wholeLineCauchyGlobal_positiveRestartData

end AxiomAudit

end ShenWork.Paper1
