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

theorem paper531Quadratic_neg_between_roots
    {c A B η : ℝ}
    (hdisc : 0 < paper531Discriminant c A B)
    (hminus : paper531RootMinus c A B < η)
    (hplus : η < paper531RootPlus c A B) :
    paper531Quadratic c A B η < 0 := by
  rw [paper531Quadratic_factor hdisc.le]
  exact mul_neg_of_pos_of_neg (sub_pos.mpr hminus) (sub_neg.mpr hplus)

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

section Theorem12RootObstructionAxiomAudit
#print axioms paper531Quadratic_factor
#print axioms paper531Discriminant_pos_of_speed
#print axioms paper531Quadratic_neg_between_roots
#print axioms paper531_kappa_lt_rootMinus
#print axioms paper531Quadratic_at_kappa
#print axioms paper531_kappa_not_between_perturbed_roots
#print axioms paper531_positive_inside_stated_weight_window
#print axioms paper533VisiblePositiveTerm_pos
#print axioms paper531_actual_correction_pos
#print axioms paper531_numeric_sanity_root_window_impossible
end Theorem12RootObstructionAxiomAudit

end ShenWork.Paper1
