/-
  Quadratic logistic remainder near a positive Paper3 equilibrium.

  The mean mode is not discarded: after extracting its linear damping
  `-aα`, this file proves that the remaining scalar forcing is genuinely
  quadratic in the perturbation.
-/
import ShenWork.Paper3.IntervalDomainDuhamelDecomposition
import ShenWork.Paper3.EventualExponentialStability
import Mathlib.Analysis.Calculus.MeanValue

namespace ShenWork.Paper3

open Set Real

noncomputable section

/-- A locally Lipschitz derivative gives a quadratic first-order Taylor
remainder.  The proof applies the mean-value norm estimate to
`z ↦ f z - f' y z` on the segment joining `x` and `y`. -/
theorem quadratic_remainder_le_of_deriv_lipschitzOn
    {f f' : ℝ → ℝ} {s : Set ℝ} {L x y : ℝ}
    (hs : Convex ℝ s) (hL : 0 ≤ L)
    (hder : ∀ z ∈ s, HasDerivAt f (f' z) z)
    (hlip : ∀ z ∈ s, ∀ w ∈ s, |f' z - f' w| ≤ L * |z - w|)
    (hx : x ∈ s) (hy : y ∈ s) :
    |f x - f y - f' y * (x - y)| ≤ L * |x - y| ^ 2 := by
  let seg : Set ℝ := segment ℝ x y
  let g : ℝ → ℝ := fun z => f z - f' y * z
  have hseg : seg ⊆ s := hs.segment_subset hx hy
  have hxyseg : x ∈ seg := left_mem_segment ℝ x y
  have hyseg : y ∈ seg := right_mem_segment ℝ x y
  have hgder : ∀ z ∈ seg,
      HasDerivWithinAt g (f' z - f' y) seg z := by
    intro z hz
    have hf := hder z (hseg hz)
    have hlin : HasDerivAt (fun w : ℝ => f' y * w) (f' y) z := by
      simpa using (hasDerivAt_id z).const_mul (f' y)
    exact (hf.sub hlin).hasDerivWithinAt
  have hgbound : ∀ z ∈ seg, ‖f' z - f' y‖ ≤ L * |x - y| := by
    intro z hz
    have hlocal := hlip z (hseg hz) y hy
    have hzdist : |z - y| ≤ |x - y| := by
      have hzball := segment_subset_closedBall_right x y hz
      simpa [Metric.mem_closedBall, Real.dist_eq, abs_sub_comm] using hzball
    rw [Real.norm_eq_abs]
    exact hlocal.trans (mul_le_mul_of_nonneg_left hzdist hL)
  have hmv : ‖g x - g y‖ ≤ (L * |x - y|) * ‖x - y‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      hgder hgbound (convex_segment x y) hyseg hxyseg
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmv
  change |f x - f' y * x - (f y - f' y * y)| ≤
    (L * |x - y|) * |x - y| at hmv
  convert hmv using 1
  · ring
  · ring

/-- Logistic reaction and its derivative at positive arguments. -/
def paper3LogisticReaction (p : CM2Params) (z : ℝ) : ℝ :=
  z * (p.a - p.b * z ^ p.α)

def paper3LogisticReactionDeriv (p : CM2Params) (z : ℝ) : ℝ :=
  p.a - p.b * (1 + p.α) * z ^ p.α

private theorem paper3LogisticReaction_hasDerivAt
    (p : CM2Params) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (paper3LogisticReaction p)
      (paper3LogisticReactionDeriv p z) z := by
  have hpow : HasDerivAt (fun w : ℝ => w ^ p.α)
      (p.α * z ^ (p.α - 1)) z :=
    Real.hasDerivAt_rpow_const (x := z) (p := p.α) (Or.inl hz.ne')
  have hsub : HasDerivAt (fun w : ℝ => p.a - p.b * w ^ p.α)
      (0 - p.b * (p.α * z ^ (p.α - 1))) z :=
    (hasDerivAt_const z p.a).sub (hpow.const_mul p.b)
  have hprod := (hasDerivAt_id z).mul hsub
  convert hprod using 1
  have hpowadd : z * z ^ (p.α - 1) = z ^ p.α := by
    rw [mul_comm, ← Real.rpow_add_one hz.ne']
    congr 1
    ring
  simp only [paper3LogisticReactionDeriv, id_eq, one_mul, zero_sub]
  rw [show z * (-(p.b * (p.α * z ^ (p.α - 1)))) =
      -(p.b * p.α) * (z * z ^ (p.α - 1)) by ring,
    hpowadd]
  ring

/-- On the fixed positive neighborhood `[u*/2, 3u*/2]`, the derivative of
the logistic reaction is Lipschitz with some positive constant. -/
theorem paper3LogisticReactionDeriv_local_lipschitz
    (p : CM2Params) {uStar : ℝ} (huStar : 0 < uStar) :
    ∃ L > 0, ∀ x ∈ Set.Icc (uStar / 2) (3 * uStar / 2),
      ∀ y ∈ Set.Icc (uStar / 2) (3 * uStar / 2),
        |paper3LogisticReactionDeriv p x -
            paper3LogisticReactionDeriv p y| ≤ L * |x - y| := by
  let I : Set ℝ := Set.Icc (uStar / 2) (3 * uStar / 2)
  let second : ℝ → ℝ := fun z =>
    -(p.b * (1 + p.α) * p.α) * z ^ (p.α - 1)
  have hlower : 0 < uStar / 2 := by linarith
  have hpos : ∀ z ∈ I, 0 < z := by
    intro z hz
    exact lt_of_lt_of_le hlower hz.1
  have hsecond_cont : ContinuousOn second I := by
    have hpow : ContinuousOn (fun z : ℝ => z ^ (p.α - 1)) I :=
      continuousOn_id.rpow_const (fun z hz => Or.inl (hpos z hz).ne')
    exact continuousOn_const.mul hpow
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hsecond_cont
  have huI : uStar ∈ I := by
    constructor <;> dsimp [I] <;> linarith
  have hM0 : 0 ≤ M :=
    (norm_nonneg (second uStar)).trans (hM uStar huI)
  let L : ℝ := M + 1
  have hL : 0 < L := by dsimp [L]; linarith
  refine ⟨L, hL, ?_⟩
  intro x hx y hy
  have hder : ∀ z ∈ I,
      HasDerivWithinAt (paper3LogisticReactionDeriv p) (second z) I z := by
    intro z hz
    have hzpos := hpos z hz
    have hpow : HasDerivAt (fun w : ℝ => w ^ p.α)
        (p.α * z ^ (p.α - 1)) z :=
      Real.hasDerivAt_rpow_const (x := z) (p := p.α) (Or.inl hzpos.ne')
    have hmul := hpow.const_mul (p.b * (1 + p.α))
    have hsub := (hasDerivAt_const z p.a).sub hmul
    convert hsub.hasDerivWithinAt using 1
    simp only [second]
    ring
  have hbound : ∀ z ∈ I, ‖second z‖ ≤ L := by
    intro z hz
    exact (hM z hz).trans (by dsimp [L]; linarith)
  have hmv :
      ‖paper3LogisticReactionDeriv p x -
          paper3LogisticReactionDeriv p y‖ ≤ L * ‖x - y‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      hder hbound (convex_Icc _ _) hy hx
  simpa [I, Real.norm_eq_abs] using hmv

/-- The logistic forcing after its `-aα` linear part is quadratically small
near a genuine positive equilibrium. -/
theorem paper3LogisticReaction_quadratic_remainder
    (p : CM2Params) {uStar vStar : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar) :
    ∃ K > 0, ∀ x ∈ Set.Icc (uStar / 2) (3 * uStar / 2),
      |paper3LogisticReaction p x + p.a * p.α * (x - uStar)| ≤
        K * |x - uStar| ^ 2 := by
  rcases paper3LogisticReactionDeriv_local_lipschitz p heq.u_pos with
    ⟨K, hK, hLip⟩
  have huI : uStar ∈ Set.Icc (uStar / 2) (3 * uStar / 2) := by
    constructor <;> linarith [heq.u_pos]
  have hrel : p.a = p.b * uStar ^ p.α := by
    have hzero := heq.reaction_eq_zero
    rcases mul_eq_zero.mp hzero with hu0 | hrel
    · exact False.elim (heq.u_pos.ne' hu0)
    · linarith
  have hderEq : paper3LogisticReactionDeriv p uStar = -p.a * p.α := by
    simp only [paper3LogisticReactionDeriv]
    rw [hrel]
    ring
  refine ⟨K, hK, ?_⟩
  intro x hx
  have hrem := quadratic_remainder_le_of_deriv_lipschitzOn
    (f := paper3LogisticReaction p)
    (f' := paper3LogisticReactionDeriv p)
    (s := Set.Icc (uStar / 2) (3 * uStar / 2))
    (L := K) (x := x) (y := uStar)
    (convex_Icc _ _) hK.le
    (fun z hz => paper3LogisticReaction_hasDerivAt p
      (lt_of_lt_of_le (by linarith [heq.u_pos]) hz.1))
    hLip hx huI
  have hreactEq : paper3LogisticReaction p uStar = 0 := by
    simpa [paper3LogisticReaction] using heq.reaction_eq_zero
  rw [hreactEq, hderEq] at hrem
  have hremainder :
      paper3LogisticReaction p x - 0 -
          (-p.a * p.α) * (x - uStar) =
        paper3LogisticReaction p x + p.a * p.α * (x - uStar) := by
    ring
  rwa [hremainder] at hrem

#print axioms quadratic_remainder_le_of_deriv_lipschitzOn
#print axioms paper3LogisticReactionDeriv_local_lipschitz
#print axioms paper3LogisticReaction_quadratic_remainder

end

end ShenWork.Paper3
