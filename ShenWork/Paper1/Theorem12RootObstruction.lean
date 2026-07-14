import ShenWork.Paper1.Statements

open Filter Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Algebra audit of Paper 1 (5.31)--(5.35)

Equation (5.31) uses the coefficient

`η² - (c - A)η + (1 + B)`

with `A = |χ|^(1-3σ) D'` and `B = |χ|^(1-3σ) D''`.  The displayed
definitions (5.32)--(5.33) make these corrections nonnegative, and `B` is
strictly positive when `χ ≠ 0`.  Since `κ(c)` solves
`κ² - cκ + 1 = 0`, the corrected coefficient at `κ` is `Aκ + B`, not a
negative number.  The lemmas below record the resulting obstruction to the
root comparison printed in (5.35).
-/

/-- The scalar coefficient on the right-hand side of (5.31), with the two
nonnegative error budgets exposed as parameters. -/
def paper531Quadratic (c A B η : ℝ) : ℝ :=
  η ^ 2 - (c - A) * η + (1 + B)

def paper531Discriminant (c A B : ℝ) : ℝ :=
  (c - A) ^ 2 - 4 * (1 + B)

def paper531RootMinus (c A B : ℝ) : ℝ :=
  ((c - A) - Real.sqrt (paper531Discriminant c A B)) / 2

def paper531RootPlus (c A B : ℝ) : ℝ :=
  ((c - A) + Real.sqrt (paper531Discriminant c A B)) / 2

/-- The upper endpoint of the weight interval used in Paper 1, with the
paper's fixed exponent `sigma = 1 / 6`. -/
def stabilityWeightCap (p : CMParams) : ℝ :=
  1 / (1 + |p.χ| ^ (1 / 6 : ℝ))

theorem stabilityWeightCap_pos (p : CMParams) :
    0 < stabilityWeightCap p := by
  unfold stabilityWeightCap
  positivity

/-- The reciprocal of the paper's weight cap. -/
theorem stabilityWeightCap_inv (p : CMParams) :
    (stabilityWeightCap p)⁻¹ = 1 + |p.χ| ^ (1 / 6 : ℝ) := by
  have hpos : 0 < 1 + |p.χ| ^ (1 / 6 : ℝ) := by positivity
  unfold stabilityWeightCap
  field_simp

/-- Exact cancellation in the cap contribution to the corrected speed
threshold.  In particular, its first error above `2` is quadratic in
`|chi|^(1/6)`, not linear. -/
theorem stabilityWeightCap_add_inv (p : CMParams) :
    stabilityWeightCap p + (stabilityWeightCap p)⁻¹ =
      2 + (|p.χ| ^ (1 / 6 : ℝ)) ^ 2 /
        (1 + |p.χ| ^ (1 / 6 : ℝ)) := by
  let x : ℝ := |p.χ| ^ (1 / 6 : ℝ)
  have hx : 0 ≤ x := Real.rpow_nonneg (abs_nonneg _) _
  have hden : 0 < 1 + x := by linarith
  rw [stabilityWeightCap_inv]
  unfold stabilityWeightCap
  change 1 / (1 + x) + (1 + x) = 2 + x ^ 2 / (1 + x)
  field_simp
  ring

theorem stabilityWeightCap_add_inv_correction_bounds (p : CMParams) :
    0 ≤ stabilityWeightCap p + (stabilityWeightCap p)⁻¹ - 2 ∧
      stabilityWeightCap p + (stabilityWeightCap p)⁻¹ - 2 ≤
        (|p.χ| ^ (1 / 6 : ℝ)) ^ 2 := by
  let x : ℝ := |p.χ| ^ (1 / 6 : ℝ)
  have hx : 0 ≤ x := Real.rpow_nonneg (abs_nonneg _) _
  have hden : 0 < 1 + x := by linarith
  rw [stabilityWeightCap_add_inv]
  change 0 ≤ 2 + x ^ 2 / (1 + x) - 2 ∧
    2 + x ^ 2 / (1 + x) - 2 ≤ x ^ 2
  constructor
  · have hquot : 0 ≤ x ^ 2 / (1 + x) :=
      div_nonneg (sq_nonneg x) hden.le
    linarith
  · have hquot : x ^ 2 / (1 + x) ≤ x ^ 2 := by
      rw [div_le_iff₀ hden]
      nlinarith [mul_nonneg (sq_nonneg x) hx]
    linarith

/-- The full cap part of the exact threshold, split into its quadratic cap
correction and the `B` contribution. -/
theorem stabilityWeightCap_threshold_decomposition (p : CMParams) (B : ℝ) :
    stabilityWeightCap p + (1 + B) / stabilityWeightCap p =
      2 + (|p.χ| ^ (1 / 6 : ℝ)) ^ 2 /
          (1 + |p.χ| ^ (1 / 6 : ℝ)) +
        B * (1 + |p.χ| ^ (1 / 6 : ℝ)) := by
  let x : ℝ := |p.χ| ^ (1 / 6 : ℝ)
  have hx : 0 ≤ x := Real.rpow_nonneg (abs_nonneg _) _
  have hden : 0 < 1 + x := by linarith
  unfold stabilityWeightCap
  change 1 / (1 + x) + (1 + B) / (1 / (1 + x)) =
    2 + x ^ 2 / (1 + x) + B * (1 + x)
  field_simp
  ring

/-- Explicit algebraic data for the corrected (5.31) weight window.

The budgets are conclusions to be produced by the Section 5 estimates, not
assumptions built into a headline theorem.  `speed_le` makes the perturbed
quadratic have two real roots at every admitted speed, while `cap_between`
ensures that the corrected open interval is nonempty. -/
structure Paper531StabilityBudget
    (p : CMParams) (cStarStar : ℝ → ℝ) where
  A : ℝ
  B : ℝ
  A_nonneg : 0 ≤ A
  B_nonneg : 0 ≤ B
  speed_le : A + 2 * Real.sqrt (1 + B) ≤ cStarStar p.χ
  cap_between : ∀ c : ℝ, cStarStar p.χ < c →
    paper531RootMinus c A B < stabilityWeightCap p ∧
      stabilityWeightCap p < paper531RootPlus c A B

theorem paper531Quadratic_factor
    {c A B : ℝ} (hdisc : 0 ≤ paper531Discriminant c A B) (η : ℝ) :
    paper531Quadratic c A B η =
      (η - paper531RootMinus c A B) *
        (η - paper531RootPlus c A B) := by
  have hsqrt :
      Real.sqrt (paper531Discriminant c A B) ^ 2 =
        paper531Discriminant c A B :=
    Real.sq_sqrt hdisc
  unfold paper531Quadratic paper531RootMinus paper531RootPlus
    paper531Discriminant at *
  nlinarith

theorem paper531Discriminant_pos_of_speed
    {c A B : ℝ} (hB : 0 ≤ B)
    (hspeed : A + 2 * Real.sqrt (1 + B) < c) :
    0 < paper531Discriminant c A B := by
  have hbase : 0 ≤ 1 + B := by linarith
  have hsqrt_nn : 0 ≤ Real.sqrt (1 + B) := Real.sqrt_nonneg _
  have hsqrt_sq : Real.sqrt (1 + B) ^ 2 = 1 + B :=
    Real.sq_sqrt hbase
  unfold paper531Discriminant
  nlinarith [sq_nonneg (c - A - 2 * Real.sqrt (1 + B))]

theorem paper531RootMinus_lt_rootPlus
    {c A B : ℝ} (hdisc : 0 < paper531Discriminant c A B) :
    paper531RootMinus c A B < paper531RootPlus c A B := by
  have hsqrt : 0 < Real.sqrt (paper531Discriminant c A B) :=
    Real.sqrt_pos.2 hdisc
  unfold paper531RootMinus paper531RootPlus
  linarith

theorem paper531RootMinus_pos
    {c A B : ℝ} (hB : 0 ≤ B)
    (hspeed : A + 2 * Real.sqrt (1 + B) < c) :
    0 < paper531RootMinus c A B := by
  have hbase : 0 < 1 + B := by linarith
  have hsqrt_nn : 0 ≤ Real.sqrt (1 + B) := Real.sqrt_nonneg _
  have hcA : 0 < c - A := by linarith
  have hsqrt_lt :
      Real.sqrt (paper531Discriminant c A B) < c - A := by
    rw [Real.sqrt_lt' hcA]
    unfold paper531Discriminant
    nlinarith
  unfold paper531RootMinus
  linarith

theorem paper531Quadratic_neg_between_roots
    {c A B η : ℝ}
    (hdisc : 0 < paper531Discriminant c A B)
    (hminus : paper531RootMinus c A B < η)
    (hplus : η < paper531RootPlus c A B) :
    paper531Quadratic c A B η < 0 := by
  rw [paper531Quadratic_factor hdisc.le]
  exact mul_neg_of_pos_of_neg (sub_pos.mpr hminus) (sub_neg.mpr hplus)

/-- A positive cap lies strictly between the two roots once the speed exceeds
the exact value obtained by evaluating the quadratic at that cap.

This is stronger than the discriminant-only threshold
`A + 2 * sqrt (1 + B)`: the latter merely creates two real roots and does not
by itself put a prescribed weight cap between them. -/
theorem paper531_cap_between_roots_of_speed
    {c A B cap : ℝ}
    (hB : 0 ≤ B) (hcap : 0 < cap)
    (hspeed : A + cap + (1 + B) / cap < c) :
    paper531RootMinus c A B < cap ∧
      cap < paper531RootPlus c A B := by
  have hbase : 0 ≤ 1 + B := by linarith
  have hsqrt_nn : 0 ≤ Real.sqrt (1 + B) := Real.sqrt_nonneg _
  have hsqrt_sq : Real.sqrt (1 + B) ^ 2 = 1 + B :=
    Real.sq_sqrt hbase
  have hamgm :
      2 * Real.sqrt (1 + B) ≤ cap + (1 + B) / cap := by
    have htmp :
        2 * Real.sqrt (1 + B) - cap ≤ (1 + B) / cap := by
      rw [le_div_iff₀ hcap]
      nlinarith [sq_nonneg (cap - Real.sqrt (1 + B))]
    linarith

  have hdisc : 0 < paper531Discriminant c A B :=
    paper531Discriminant_pos_of_speed hB (by linarith)
  have hroots :
      paper531RootMinus c A B < paper531RootPlus c A B :=
    paper531RootMinus_lt_rootPlus hdisc
  have hq : paper531Quadratic c A B cap < 0 := by
    have hdiv : (1 + B) / cap < c - A - cap := by linarith
    have hscaled := (div_lt_iff₀ hcap).mp hdiv
    unfold paper531Quadratic
    nlinarith
  have hfactor :
      (cap - paper531RootMinus c A B) *
          (cap - paper531RootPlus c A B) < 0 := by
    rw [← paper531Quadratic_factor hdisc.le]
    exact hq
  constructor
  · by_contra hnot
    have hleft : cap - paper531RootMinus c A B ≤ 0 :=
      sub_nonpos.mpr (le_of_not_gt hnot)
    have hright : cap - paper531RootPlus c A B ≤ 0 := by
      have : cap < paper531RootPlus c A B :=
        (le_of_not_gt hnot).trans_lt hroots
      linarith
    have : 0 ≤
        (cap - paper531RootMinus c A B) *
          (cap - paper531RootPlus c A B) :=
      mul_nonneg_of_nonpos_of_nonpos hleft hright
    linarith
  · by_contra hnot
    have hright : 0 ≤ cap - paper531RootPlus c A B :=
      sub_nonneg.mpr (le_of_not_gt hnot)
    have hleft : 0 ≤ cap - paper531RootMinus c A B := by
      have : paper531RootMinus c A B < cap :=
        hroots.trans_le (le_of_not_gt hnot)
      linarith
    have : 0 ≤
        (cap - paper531RootMinus c A B) *
          (cap - paper531RootPlus c A B) :=
      mul_nonneg hleft hright
    linarith

/-- The exact cap-evaluation threshold constructs the scalar stability
budget.  Consequently, the corrected root window is not an extra analytic
assumption: after concrete nonnegative budgets `A,B` are supplied, it reduces
to this one scalar lower bound on the speed threshold. -/
def paper531StabilityBudget_of_cap_threshold
    {p : CMParams} {cStarStar : ℝ → ℝ} {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hthreshold :
      A + stabilityWeightCap p +
          (1 + B) / stabilityWeightCap p ≤ cStarStar p.χ) :
    Paper531StabilityBudget p cStarStar := by
  have hcap : 0 < stabilityWeightCap p := stabilityWeightCap_pos p
  have hbase : 0 ≤ 1 + B := by linarith
  have hsqrt_sq : Real.sqrt (1 + B) ^ 2 = 1 + B :=
    Real.sq_sqrt hbase
  have hamgm :
      2 * Real.sqrt (1 + B) ≤
        stabilityWeightCap p + (1 + B) / stabilityWeightCap p := by
    have htmp :
        2 * Real.sqrt (1 + B) - stabilityWeightCap p ≤
          (1 + B) / stabilityWeightCap p := by
      rw [le_div_iff₀ hcap]
      nlinarith [sq_nonneg (stabilityWeightCap p - Real.sqrt (1 + B))]
    linarith
  refine
    { A := A
      B := B
      A_nonneg := hA
      B_nonneg := hB
      speed_le := by linarith
      cap_between := ?_ }
  intro c hc
  exact paper531_cap_between_roots_of_speed hB hcap
    (lt_of_le_of_lt hthreshold hc)

theorem paper531Quadratic_at_unperturbed_root
    {c A B k : ℝ} (hk : k ^ 2 - c * k + 1 = 0) :
    paper531Quadratic c A B k = A * k + B := by
  unfold paper531Quadratic
  nlinarith

theorem paper531Quadratic_at_kappa
    {c A B : ℝ} (hc : 2 ≤ c) :
    paper531Quadratic c A B (kappa c) = A * kappa c + B :=
  paper531Quadratic_at_unperturbed_root (kappa_quadratic_eq_zero hc)

/-- If the correction at the unperturbed root is positive, that root cannot
lie between the two roots of the perturbed quadratic.  This directly
contradicts the comparison `κ⁻ ≤ κ < κ⁺` printed in (5.35). -/
theorem paper531_not_between_perturbed_roots
    {c A B k rootMinus rootPlus : ℝ}
    (hk : k ^ 2 - c * k + 1 = 0)
    (hcorrection : 0 < A * k + B)
    (hfactor :
      paper531Quadratic c A B k = (k - rootMinus) * (k - rootPlus)) :
    ¬(rootMinus ≤ k ∧ k ≤ rootPlus) := by
  intro hbetween
  have hleft : 0 ≤ k - rootMinus := sub_nonneg.mpr hbetween.1
  have hright : k - rootPlus ≤ 0 := sub_nonpos.mpr hbetween.2
  have hproduct : (k - rootMinus) * (k - rootPlus) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hleft hright
  rw [paper531Quadratic_at_unperturbed_root hk] at hfactor
  nlinarith

theorem paper531_kappa_not_between_perturbed_roots
    {c A B rootMinus rootPlus : ℝ}
    (hc : 2 ≤ c)
    (hcorrection : 0 < A * kappa c + B)
    (hfactor :
      paper531Quadratic c A B (kappa c) =
        (kappa c - rootMinus) * (kappa c - rootPlus)) :
    ¬(rootMinus ≤ kappa c ∧ kappa c ≤ rootPlus) :=
  paper531_not_between_perturbed_roots
    (kappa_quadratic_eq_zero hc) hcorrection hfactor

/-- Under the paper's speed threshold and nonnegative budgets, the actual
direction is `κ(c) < κ⁻`, not `κ⁻ ≤ κ`, whenever the correction at `κ` is
strictly positive. -/
theorem paper531_kappa_lt_rootMinus
    {c A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hspeed : A + 2 * Real.sqrt (1 + B) < c)
    (hcorrection : 0 < A * kappa c + B) :
    kappa c < paper531RootMinus c A B := by
  have hdisc : 0 < paper531Discriminant c A B :=
    paper531Discriminant_pos_of_speed hB hspeed
  have hbase : 1 ≤ 1 + B := by linarith
  have hsqrt_one : 1 ≤ Real.sqrt (1 + B) := by
    calc
      (1 : ℝ) = Real.sqrt 1 := by norm_num
      _ ≤ Real.sqrt (1 + B) := Real.sqrt_le_sqrt hbase
  have hcA : 2 < c - A := by linarith
  have hc : 2 < c := lt_of_lt_of_le (by linarith : 2 < c - A) (by linarith)
  have hk_one : kappa c < 1 := kappa_lt_one_of_two_lt hc
  have hrootPlus_mid : (c - A) / 2 < paper531RootPlus c A B := by
    have hsqrt_disc : 0 < Real.sqrt (paper531Discriminant c A B) :=
      Real.sqrt_pos.2 hdisc
    unfold paper531RootPlus
    linarith
  have hk_plus : kappa c < paper531RootPlus c A B := by
    have hmid : 1 < (c - A) / 2 := by linarith
    linarith
  have hfactor :
      paper531Quadratic c A B (kappa c) =
        (kappa c - paper531RootMinus c A B) *
          (kappa c - paper531RootPlus c A B) :=
    paper531Quadratic_factor hdisc.le _
  have hnot_between :
      ¬(paper531RootMinus c A B ≤ kappa c ∧
        kappa c ≤ paper531RootPlus c A B) :=
    paper531_kappa_not_between_perturbed_roots
      hc.le hcorrection hfactor
  by_contra hnot
  apply hnot_between
  exact ⟨le_of_not_gt hnot, hk_plus.le⟩

/-- The weak comparison, including the unperturbed case `A = B = 0`.
Unlike the strict comparison above, this needs no separate strict-correction
hypothesis. -/
theorem paper531_kappa_le_rootMinus
    {c A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hspeed : A + 2 * Real.sqrt (1 + B) < c) :
    kappa c ≤ paper531RootMinus c A B := by
  have hdisc : 0 < paper531Discriminant c A B :=
    paper531Discriminant_pos_of_speed hB hspeed
  have hbase : 1 ≤ 1 + B := by linarith
  have hsqrt_one : 1 ≤ Real.sqrt (1 + B) := by
    calc
      (1 : ℝ) = Real.sqrt 1 := by norm_num
      _ ≤ Real.sqrt (1 + B) := Real.sqrt_le_sqrt hbase
  have hcA : 2 < c - A := by linarith
  have hc : 2 < c := by linarith
  have hk_one : kappa c < 1 := kappa_lt_one_of_two_lt hc
  have hrootPlus_mid : (c - A) / 2 < paper531RootPlus c A B := by
    have hsqrt_disc : 0 < Real.sqrt (paper531Discriminant c A B) :=
      Real.sqrt_pos.2 hdisc
    unfold paper531RootPlus
    linarith
  have hk_plus : kappa c < paper531RootPlus c A B := by
    have hmid : 1 < (c - A) / 2 := by linarith
    linarith
  have hk_nonneg : 0 ≤ kappa c := kappa_nonneg_of_two_le hc.le
  have hq_nonneg : 0 ≤ paper531Quadratic c A B (kappa c) := by
    rw [paper531Quadratic_at_kappa hc.le]
    positivity
  by_contra hnot
  have hminus : paper531RootMinus c A B < kappa c := lt_of_not_ge hnot
  have hq_neg : paper531Quadratic c A B (kappa c) < 0 :=
    paper531Quadratic_neg_between_roots hdisc hminus hk_plus
  linarith

namespace Paper531StabilityBudget

theorem speed_at
    {p : CMParams} {cStarStar : ℝ → ℝ}
    (h : Paper531StabilityBudget p cStarStar)
    {c : ℝ} (hc : cStarStar p.χ < c) :
    h.A + 2 * Real.sqrt (1 + h.B) < c :=
  lt_of_le_of_lt h.speed_le hc

theorem discriminant_pos
    {p : CMParams} {cStarStar : ℝ → ℝ}
    (h : Paper531StabilityBudget p cStarStar)
    {c : ℝ} (hc : cStarStar p.χ < c) :
    0 < paper531Discriminant c h.A h.B :=
  paper531Discriminant_pos_of_speed h.B_nonneg (h.speed_at hc)

theorem rootMinus_pos
    {p : CMParams} {cStarStar : ℝ → ℝ}
    (h : Paper531StabilityBudget p cStarStar)
    {c : ℝ} (hc : cStarStar p.χ < c) :
    0 < paper531RootMinus c h.A h.B :=
  paper531RootMinus_pos h.B_nonneg (h.speed_at hc)

theorem kappa_le_rootMinus
    {p : CMParams} {cStarStar : ℝ → ℝ}
    (h : Paper531StabilityBudget p cStarStar)
    {c : ℝ} (hc : cStarStar p.χ < c) :
    kappa c ≤ paper531RootMinus c h.A h.B :=
  paper531_kappa_le_rootMinus h.A_nonneg h.B_nonneg (h.speed_at hc)

theorem quadratic_neg
    {p : CMParams} {cStarStar : ℝ → ℝ}
    (h : Paper531StabilityBudget p cStarStar)
    {c η : ℝ} (hc : cStarStar p.χ < c)
    (hminus : paper531RootMinus c h.A h.B < η)
    (hcap : η < stabilityWeightCap p) :
    paper531Quadratic c h.A h.B η < 0 :=
  paper531Quadratic_neg_between_roots (h.discriminant_pos hc) hminus
    (hcap.trans (h.cap_between c hc).2)

end Paper531StabilityBudget

/-- The obstruction is not confined to the excluded endpoint `η = κ`.
Continuity gives weights strictly above `κ` (and below any prescribed upper
cap) for which the coefficient in (5.31) remains positive. -/
theorem paper531_positive_inside_stated_weight_window
    {c A B cap : ℝ}
    (hc : 2 ≤ c)
    (hcorrection : 0 < A * kappa c + B)
    (hcap : kappa c < cap) :
    ∃ η : ℝ,
      kappa c < η ∧ η < cap ∧ 0 < paper531Quadratic c A B η := by
  have hqk : 0 < paper531Quadratic c A B (kappa c) := by
    rw [paper531Quadratic_at_kappa hc]
    exact hcorrection
  have hcont : Continuous (paper531Quadratic c A B) := by
    unfold paper531Quadratic
    fun_prop
  have hpreimage :
      paper531Quadratic c A B ⁻¹' Set.Ioi 0 ∈ 𝓝 (kappa c) :=
    hcont.continuousAt (Ioi_mem_nhds hqk)
  rcases Metric.mem_nhds_iff.1 hpreimage with ⟨ε, hε, hball⟩
  let d : ℝ := min (ε / 2) ((cap - kappa c) / 2)
  have hd : 0 < d := by
    dsimp [d]
    exact lt_min (by positivity) (by linarith)
  have hdε : d < ε := by
    have hdle : d ≤ ε / 2 := min_le_left _ _
    linarith
  have hdcap : d < cap - kappa c := by
    have hdle : d ≤ (cap - kappa c) / 2 := min_le_right _ _
    linarith
  refine ⟨kappa c + d, by linarith, by linarith, ?_⟩
  have hmem : kappa c + d ∈ Metric.ball (kappa c) ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    simpa [abs_of_pos hd] using hdε
  exact hball hmem

/-- The final summand displayed in (5.33).  It is enough by itself to
certify that the paper's `D''` budget is strictly positive away from
`χ = 0`. -/
def paper533VisiblePositiveTerm
    (χ sigma M m gamma : ℝ) : ℝ :=
  (1 / 2 : ℝ) * |χ| ^ (3 * sigma) * M ^ m *
    (|χ| ^ (2 * sigma) + gamma ^ 2 * (1 + |χ| ^ sigma) ^ 2)

theorem paper533VisiblePositiveTerm_pos
    {χ sigma M m gamma : ℝ}
    (hχ : χ ≠ 0) (hM : 0 < M) (hgamma : 0 < gamma) :
    0 < paper533VisiblePositiveTerm χ sigma M m gamma := by
  have habs : 0 < |χ| := abs_pos.mpr hχ
  have hχ3 : 0 < |χ| ^ (3 * sigma) := Real.rpow_pos_of_pos habs _
  have hχ2 : 0 < |χ| ^ (2 * sigma) := Real.rpow_pos_of_pos habs _
  have hχσ : 0 < |χ| ^ sigma := Real.rpow_pos_of_pos habs _
  have hMpow : 0 < M ^ m := Real.rpow_pos_of_pos hM _
  have hbracket :
      0 < |χ| ^ (2 * sigma) + gamma ^ 2 * (1 + |χ| ^ sigma) ^ 2 := by
    positivity
  unfold paper533VisiblePositiveTerm
  positivity

/-- In the actual (5.31)--(5.33) sign pattern, nonnegativity of the `D'`
budget and the visible positive last summand of `D''` make the correction at
`κ(c)` strictly positive whenever `χ ≠ 0`. -/
theorem paper531_actual_correction_pos
    {c χ sigma M m gamma DPrime DDoublePrime : ℝ}
    (hc : 2 ≤ c) (hχ : χ ≠ 0) (hM : 0 < M) (hgamma : 0 < gamma)
    (hDPrime : 0 ≤ DPrime)
    (hDDoublePrime :
      paper533VisiblePositiveTerm χ sigma M m gamma ≤ DDoublePrime) :
    0 <
      (|χ| ^ (1 - 3 * sigma) * DPrime) * kappa c +
        |χ| ^ (1 - 3 * sigma) * DDoublePrime := by
  have habs : 0 < |χ| := abs_pos.mpr hχ
  have hpref : 0 < |χ| ^ (1 - 3 * sigma) :=
    Real.rpow_pos_of_pos habs _
  have hDdouble : 0 < DDoublePrime :=
    lt_of_lt_of_le
      (paper533VisiblePositiveTerm_pos hχ hM hgamma) hDDoublePrime
  have hk : 0 ≤ kappa c := kappa_nonneg_of_two_le hc
  have hleft : 0 ≤ (|χ| ^ (1 - 3 * sigma) * DPrime) * kappa c :=
    mul_nonneg (mul_nonneg hpref.le hDPrime) hk
  have hright : 0 < |χ| ^ (1 - 3 * sigma) * DDoublePrime :=
    mul_pos hpref hDdouble
  linarith

/-- Concrete numerical sanity check: `k = 1/2` is the lower root for
`c = 5/2`.  Taking `A = B = 1/10` makes the perturbed coefficient at `k`
equal to `3/20 > 0`, so no factorization can have roots bracketing `k`. -/
theorem paper531_numeric_sanity_root_window_impossible :
    ¬∃ rootMinus rootPlus : ℝ,
      paper531Quadratic (5 / 2) (1 / 10) (1 / 10) (1 / 2) =
          ((1 / 2) - rootMinus) * ((1 / 2) - rootPlus) ∧
        rootMinus ≤ (1 / 2) ∧ (1 / 2) ≤ rootPlus := by
  rintro ⟨rootMinus, rootPlus, hfactor, hminus, hplus⟩
  exact paper531_not_between_perturbed_roots
    (c := 5 / 2) (A := 1 / 10) (B := 1 / 10) (k := 1 / 2)
    (rootMinus := rootMinus) (rootPlus := rootPlus)
    (by norm_num) (by norm_num) hfactor ⟨hminus, hplus⟩

/-! ## Sign audit of the exponential factor following (5.35) -/

/-- The factor printed after (5.35) grows, rather than decays, when the
paper's displayed definition `lam < 0` is used. -/
theorem paper531_printed_decay_factor_tendsto_atTop
    {lam : ℝ} (hlam : lam < 0) :
    Tendsto (fun t : ℝ => Real.exp (-lam * t)) atTop atTop := by
  have hcoef : 0 < -lam := neg_pos.mpr hlam
  have hlin : Tendsto (fun t : ℝ => -lam * t) atTop atTop :=
    tendsto_id.const_mul_atTop hcoef
  exact Real.tendsto_exp_atTop.comp hlin

/-- With the same negative coefficient, the decaying factor is `exp (lam t)`
(equivalently, define a positive decay rate `-lam` and write
`exp (-(-lam)t)`). -/
theorem paper531_corrected_decay_factor_tendsto_zero
    {lam : ℝ} (hlam : lam < 0) :
    Tendsto (fun t : ℝ => Real.exp (lam * t)) atTop (nhds 0) := by
  have hlin : Tendsto (fun t : ℝ => lam * t) atTop atBot :=
    tendsto_id.const_mul_atTop_of_neg hlam
  exact Real.tendsto_exp_atBot.comp hlin

section Theorem12RootObstructionAxiomAudit
#print axioms stabilityWeightCap_pos
#print axioms stabilityWeightCap_inv
#print axioms stabilityWeightCap_add_inv
#print axioms stabilityWeightCap_add_inv_correction_bounds
#print axioms stabilityWeightCap_threshold_decomposition
#print axioms paper531Quadratic_factor
#print axioms paper531Discriminant_pos_of_speed
#print axioms paper531RootMinus_pos
#print axioms paper531Quadratic_neg_between_roots
#print axioms paper531_cap_between_roots_of_speed
#print axioms paper531StabilityBudget_of_cap_threshold
#print axioms paper531_kappa_lt_rootMinus
#print axioms paper531_kappa_le_rootMinus
#print axioms Paper531StabilityBudget.quadratic_neg
#print axioms paper531Quadratic_at_kappa
#print axioms paper531_kappa_not_between_perturbed_roots
#print axioms paper531_positive_inside_stated_weight_window
#print axioms paper533VisiblePositiveTerm_pos
#print axioms paper531_actual_correction_pos
#print axioms paper531_numeric_sanity_root_window_impossible
#print axioms paper531_printed_decay_factor_tendsto_atTop
#print axioms paper531_corrected_decay_factor_tendsto_zero
end Theorem12RootObstructionAxiomAudit

end ShenWork.Paper1
