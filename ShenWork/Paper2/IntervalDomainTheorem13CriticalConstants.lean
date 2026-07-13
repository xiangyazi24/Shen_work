import ShenWork.Paper2.IntervalDomainMWeightedGradient
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# The actual constants in Paper 2, Theorem 1.3

On the one-dimensional interval the Hessian and the Laplacian are the same
scalar second derivative.  Thus the optimal constant in (1.16)--(1.17) is
`C^*_{1,q} = 1`.  We insert this value into the paper's formula (1.18), and
define (1.19) literally as a right-sided `liminf`.

The continuity lemmas below are used only in the nontrivial critical branch
`alpha > 2`, where the exponent supplied to (1.18) is strictly above one.
-/

open MeasureTheory Set Filter Topology
open scoped Topology Interval

noncomputable section

namespace ShenWork.Paper2.IntervalDomainTheorem13CriticalConstants

open ShenWork.Paper2

/-- Scalar admissibility relation obtained from (1.16) after the
one-dimensional identity `|D^2 f| = |Delta f|`. -/
def intervalHessianAdmissibleConstants : Set ℝ :=
  {C | 0 < C ∧ ∀ A B : ℝ, 0 ≤ A → 0 ≤ B → A ≤ C * (A + B)}

lemma intervalHessianAdmissibleConstants_eq_Ici :
    intervalHessianAdmissibleConstants = Set.Ici 1 := by
  ext C
  constructor
  · intro h
    exact intervalHessianOptimalConstant_minimal_aux h.2
  · intro h
    refine ⟨lt_of_lt_of_le zero_lt_one h, ?_⟩
    intro A B hA hB
    have hab : A ≤ A + B := by linarith
    have hscale : A + B ≤ C * (A + B) := by
      calc
        A + B = 1 * (A + B) := by ring
        _ ≤ C * (A + B) :=
          mul_le_mul_of_nonneg_right h (add_nonneg hA hB)
    exact hab.trans hscale
where
  intervalHessianOptimalConstant_minimal_aux
      {C : ℝ}
      (hC : ∀ A B : ℝ, 0 ≤ A → 0 ≤ B → A ≤ C * (A + B)) :
      1 ≤ C := by
    have h := hC 1 0 (by norm_num) (by norm_num)
    norm_num at h ⊢
    exact h

/-- The interval realization of the optimal elliptic constant (1.17), as
the infimum of the admissible one-dimensional constants. -/
def intervalHessianOptimalConstant (_q : ℝ) : ℝ :=
  sInf intervalHessianAdmissibleConstants

lemma intervalHessianOptimalConstant_eq_one (q : ℝ) :
    intervalHessianOptimalConstant q = 1 := by
  rw [intervalHessianOptimalConstant,
    intervalHessianAdmissibleConstants_eq_Ici, csInf_Ici]

/-- `1` is admissible in the scalar one-dimensional Hessian estimate. -/
lemma intervalHessianOptimalConstant_admissible
    {A B : ℝ} (_hA : 0 ≤ A) (hB : 0 ≤ B) :
    A ≤ intervalHessianOptimalConstant 2 * (A + B) := by
  rw [intervalHessianOptimalConstant_eq_one, one_mul]
  linarith

/-- The value one is optimal for the scalar inequality containing the
one-dimensional `D^2 = Delta` identity. -/
lemma intervalHessianOptimalConstant_minimal
    {C : ℝ} (hC : ∀ A B : ℝ, 0 ≤ A → 0 ≤ B → A ≤ C * (A + B)) :
    intervalHessianOptimalConstant 2 ≤ C := by
  have h := hC 1 0 (by norm_num) (by norm_num)
  simpa [intervalHessianOptimalConstant_eq_one] using h

/-- Formula (1.18) specialized to `N = 1`, hence `C^*_{1,q} = 1`.
The formula is only consumed under `1 < q`, exactly as in Proposition 2.2. -/
def intervalPaperMstar (p : CM2Params) (q : ℝ) : ℝ :=
  p.ν ^ q *
    (((8 : ℝ) ^ q / q) * intervalHessianOptimalConstant q *
        ((2 : ℝ) ^ q + 1 / p.μ ^ q) +
      (2 : ℝ) ^ (2 * q) / ((q - 1) * q ^ q))

lemma intervalPaperMstar_pos
    (p : CM2Params) {q : ℝ} (hq : 1 < q) :
    0 < intervalPaperMstar p q := by
  unfold intervalPaperMstar
  rw [intervalHessianOptimalConstant_eq_one, mul_one]
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hq1 : 0 < q - 1 := sub_pos.mpr hq
  have hfirst :
      0 < ((8 : ℝ) ^ q / q) * ((2 : ℝ) ^ q + 1 / p.μ ^ q) := by
    exact mul_pos
      (div_pos (Real.rpow_pos_of_pos (by norm_num) _) hq0)
      (add_pos (Real.rpow_pos_of_pos (by norm_num) _)
        (one_div_pos.mpr (Real.rpow_pos_of_pos p.hμ _)))
  have hsecond :
      0 < (2 : ℝ) ^ (2 * q) / ((q - 1) * q ^ q) := by
    exact div_pos (Real.rpow_pos_of_pos (by norm_num) _)
      (mul_pos hq1 (Real.rpow_pos_of_pos hq0 _))
  exact mul_pos (Real.rpow_pos_of_pos p.hν _) (add_pos hfirst hsecond)

lemma intervalPaperMstar_nonneg
    (p : CM2Params) {q : ℝ} (hq : 1 < q) :
    0 ≤ intervalPaperMstar p q :=
  (intervalPaperMstar_pos p hq).le

lemma intervalPaperMstar_continuousAt
    (p : CM2Params) {q : ℝ} (hq : 1 < q) :
    ContinuousAt (intervalPaperMstar p) q := by
  unfold intervalPaperMstar
  simp only [intervalHessianOptimalConstant_eq_one, mul_one]
  have hq0 : q ≠ 0 := ne_of_gt (lt_trans zero_lt_one hq)
  have hq1 : q - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hq)
  have hnu : ContinuousAt (fun r : ℝ => p.ν ^ r) q :=
    continuousAt_const.rpow continuousAt_id (Or.inl p.hν.ne')
  have h8 : ContinuousAt (fun r : ℝ => (8 : ℝ) ^ r) q :=
    continuousAt_const.rpow continuousAt_id (Or.inl (by norm_num))
  have h2 : ContinuousAt (fun r : ℝ => (2 : ℝ) ^ (2 * r)) q :=
    continuousAt_const.rpow (continuousAt_const.mul continuousAt_id)
      (Or.inl (by norm_num))
  have hqq : ContinuousAt (fun r : ℝ => r ^ r) q :=
    continuousAt_id.rpow continuousAt_id (Or.inl hq0)
  have hmuq : ContinuousAt (fun r : ℝ => p.μ ^ r) q :=
    continuousAt_const.rpow continuousAt_id (Or.inl p.hμ.ne')
  exact hnu.mul
    (((h8.div continuousAt_id hq0).mul
      ((continuousAt_const.rpow continuousAt_id (Or.inl (by norm_num))).add
        (continuousAt_const.div hmuq
          (ne_of_gt (Real.rpow_pos_of_pos p.hμ _))))).add
      (h2.div ((continuousAt_id.sub continuousAt_const).mul hqq)
        (mul_ne_zero hq1
          ((Real.rpow_ne_zero (lt_trans zero_lt_one hq).le hq0).2 hq0))))

/-- The paper's `q_* = max{1,N alpha/2}`. -/
def theorem13CriticalQStar (p : CM2Params) : ℝ :=
  max 1 (((p.N : ℝ) * p.α) / 2)

lemma one_le_theorem13CriticalQStar (p : CM2Params) :
    1 ≤ theorem13CriticalQStar p := by
  exact le_max_left _ _

lemma theorem13CriticalQStar_pos (p : CM2Params) :
    0 < theorem13CriticalQStar p :=
  zero_lt_one.trans_le (one_le_theorem13CriticalQStar p)

/-- The function whose right lower limit is the constant `K` in (1.19). -/
def theorem13CriticalProfile (p : CM2Params) (q : ℝ) : ℝ :=
  intervalPaperMstar p ((q + p.α) / p.γ) ^ (p.γ / (q + p.α))

/-- Formula (1.19), with the right-sided approach encoded by `nhdsWithin`.
-/
def theorem13CriticalK (p : CM2Params) : ℝ :=
  liminf (theorem13CriticalProfile p) (𝓝[>] theorem13CriticalQStar p)

lemma theorem13CriticalProfile_pos
    (p : CM2Params) {q : ℝ}
    (hs : 1 < (q + p.α) / p.γ) :
    0 < theorem13CriticalProfile p q := by
  unfold theorem13CriticalProfile
  exact Real.rpow_pos_of_pos (intervalPaperMstar_pos p hs) _

lemma theorem13CriticalProfile_continuousAt
    (p : CM2Params) {q : ℝ}
    (hs : 1 < (q + p.α) / p.γ) :
    ContinuousAt (theorem13CriticalProfile p) q := by
  unfold theorem13CriticalProfile
  have hsum : q + p.α ≠ 0 := by
    have hpos : 0 < q + p.α := by
      have hdiv : 0 < (q + p.α) / p.γ := zero_lt_one.trans hs
      have hprod := mul_pos hdiv p.hγ
      have heq : ((q + p.α) / p.γ) * p.γ = q + p.α := by
        field_simp [p.hγ.ne']
      rwa [heq] at hprod
    exact ne_of_gt hpos
  have hscont : ContinuousAt (fun r : ℝ => (r + p.α) / p.γ) q :=
    (continuousAt_id.add continuousAt_const).div_const p.γ
  have hbase : ContinuousAt
      (fun r : ℝ => intervalPaperMstar p ((r + p.α) / p.γ)) q :=
    ContinuousAt.comp (x := q)
      (f := fun r : ℝ => (r + p.α) / p.γ)
      (g := intervalPaperMstar p)
      (intervalPaperMstar_continuousAt p hs) hscont
  have hexp : ContinuousAt (fun r : ℝ => p.γ / (r + p.α)) q :=
    continuousAt_const.div (continuousAt_id.add continuousAt_const) hsum
  exact hbase.rpow hexp
    (Or.inl (ne_of_gt (intervalPaperMstar_pos p hs)))

lemma theorem13CriticalK_eq_profile
    (p : CM2Params)
    (hs : 1 < (theorem13CriticalQStar p + p.α) / p.γ) :
    theorem13CriticalK p =
      theorem13CriticalProfile p (theorem13CriticalQStar p) := by
  unfold theorem13CriticalK
  have ht : Tendsto (theorem13CriticalProfile p)
      (𝓝[>] theorem13CriticalQStar p)
      (𝓝 (theorem13CriticalProfile p (theorem13CriticalQStar p))) :=
    (theorem13CriticalProfile_continuousAt p hs).tendsto.mono_left inf_le_left
  exact ht.liminf_eq

lemma theorem13CriticalK_pos
    (p : CM2Params)
    (hs : 1 < (theorem13CriticalQStar p + p.α) / p.γ) :
    0 < theorem13CriticalK p := by
  rw [theorem13CriticalK_eq_profile p hs]
  exact theorem13CriticalProfile_pos p hs

/-- The literal paper constant package, now realized rather than supplied as
an arbitrary nonnegative scalar. -/
def theorem13PaperConstants (p : CM2Params)
    (hs : 1 < (theorem13CriticalQStar p + p.α) / p.γ) :
    Paper2Constants p where
  K := theorem13CriticalK p
  K_nonneg := (theorem13CriticalK_pos p hs).le

lemma theorem13PaperConstants_K
    (p : CM2Params)
    (hs : 1 < (theorem13CriticalQStar p + p.α) / p.γ) :
    (theorem13PaperConstants p hs).K = theorem13CriticalK p := rfl

/-- On the interval, binding the formal dimension field to one reduces the
paper's `q_*` to `max{1,alpha/2}`. -/
lemma theorem13CriticalQStar_eq_interval
    (p : CM2Params) (hN : p.N = 1) :
    theorem13CriticalQStar p = max 1 (p.α / 2) := by
  simp [theorem13CriticalQStar, hN]

#print axioms intervalHessianOptimalConstant_admissible
#print axioms intervalHessianOptimalConstant_minimal
#print axioms intervalPaperMstar_pos
#print axioms intervalPaperMstar_continuousAt
#print axioms theorem13CriticalProfile_continuousAt
#print axioms theorem13CriticalK_eq_profile
#print axioms theorem13CriticalK_pos
#print axioms theorem13PaperConstants
#print axioms theorem13CriticalQStar_eq_interval

end ShenWork.Paper2.IntervalDomainTheorem13CriticalConstants
