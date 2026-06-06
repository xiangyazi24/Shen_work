/-
  ShenWork/PDE/IntervalLogisticSourceQuantBound.lean

  Phase-0 / M2-logistic: EXPLICIT (no existentials) `W^{2,1}` bound for the
  logistic source `F(x) = g(x)·(a − b·g(x)^α)` on `[0,1]`, and the resulting
  explicit cosine-coefficient quadratic decay.

  Chain rule:
    L(z)   = z·(a − b·z^α)
    L'(z)  = a − b·(1+α)·z^α
    L''(z) = −b·α·(1+α)·z^{α−1}
    (L∘g)''(x) = −b·α·(1+α)·g(x)^{α−1}·(g'(x))²
                 + (a − b·(1+α)·g(x)^α)·g''(x).

  Under `0 < g ≤ M` on `[0,1]`, `|g'| ≤ G1`, `|g''| ≤ G2`, `1 ≤ α`, `0 ≤ a`,
  `0 ≤ b`, the pointwise bound is

    |F''(x)| ≤ b·α·(1+α)·M^{α−1}·G1²  +  (a + b·(1+α)·M^α)·G2  =:  B_log,

  so `∫₀¹ |F''| ≤ B_log` (constant integrand over a unit interval) and, by
  `intervalWeakH2Neumann_cosineCoeff_quadratic_decay_of_bound`,

    |cosineCoeffs F k| ≤ 2·B_log / ((k:ℝ)·π)²   for all k ≥ 1.

  No `sorry`/`admit`/custom `axiom`/`native_decide`.
-/
import ShenWork.PDE.IntervalSourceDecayQuantitative
import ShenWork.Paper2.IntervalMildPicardRegularity

open MeasureTheory
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.PDE.IntervalMildSourceDecayHelper
open ShenWork.IntervalMildPicardRegularity
open ShenWork.IntervalEllipticCharacterization
  (intervalIntegrable_deriv_deriv_of_contDiffOn_two)

noncomputable section

namespace ShenWork.IntervalLogisticSourceQuantBound

/-- The explicit `W^{2,1}` / pointwise second-derivative bound constant for the
logistic source. -/
def B_log (a b α M G1 G2 : ℝ) : ℝ :=
  b * α * (1 + α) * M ^ (α - 1) * G1 ^ 2 + (a + b * (1 + α) * M ^ α) * G2

/-- The explicit first-derivative function of the logistic source, valid where
`g > 0`:  `F'(x) = g'(x)·(a − b·(1+α)·g(x)^α)`. -/
def F1 (a b α : ℝ) (g : ℝ → ℝ) : ℝ → ℝ :=
  fun x => deriv g x * (a - b * (1 + α) * g x ^ α)

/-- The explicit second-derivative function of the logistic source, valid where
`g > 0`:
`F''(x) = −b·α·(1+α)·g(x)^{α−1}·(g'(x))² + (a − b·(1+α)·g(x)^α)·g''(x)`. -/
def F2 (a b α : ℝ) (g : ℝ → ℝ) : ℝ → ℝ :=
  fun x =>
    (-(b * α * (1 + α)) * g x ^ (α - 1) * deriv g x) * deriv g x
      + (a - b * (1 + α) * g x ^ α) * deriv (deriv g) x

/-- First derivative of the logistic source where `g x > 0` (globally,
using `ContDiff ℝ 2 g`). -/
theorem logisticSourceFun_hasDerivAt
    {a b α : ℝ} {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) {x : ℝ} (hx : 0 < g x) :
    HasDerivAt (logisticSourceFun a b α g) (F1 a b α g x) x := by
  have hgx_ne : g x ≠ 0 := ne_of_gt hx
  have hg_diff : HasDerivAt g (deriv g x) x :=
    (hg.differentiable (by norm_num) x).hasDerivAt
  -- d/dx g^α = α·g^{α−1}·g'
  have hpow : HasDerivAt (fun y => g y ^ α)
      (deriv g x * α * g x ^ (α - 1)) x :=
    hg_diff.rpow_const (Or.inl hgx_ne)
  have hh : HasDerivAt (fun y => a - b * g y ^ α)
      (0 - b * (deriv g x * α * g x ^ (α - 1))) x :=
    (hasDerivAt_const x a).sub (hpow.const_mul b)
  have hprod := hg_diff.mul hh
  -- rewrite into F1 form
  have hrpow : g x * g x ^ (α - 1) = g x ^ α := by
    rw [mul_comm, ← Real.rpow_add_one hgx_ne]; congr 1; ring
  have heq : deriv g x * (a - b * g x ^ α)
      + g x * (0 - b * (deriv g x * α * g x ^ (α - 1)))
      = F1 a b α g x := by
    simp only [F1]
    linear_combination deriv g x * (-b * α) * hrpow
  have : logisticSourceFun a b α g = fun y => g y * (a - b * g y ^ α) := by
    funext y; simp [logisticSourceFun]
  rw [this]
  rw [← heq]; exact hprod

/-- Second derivative of `F1` (= first derivative of the source's derivative)
where `g x > 0`. -/
theorem F1_hasDerivAt
    {a b α : ℝ} {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) {x : ℝ} (hx : 0 < g x) :
    HasDerivAt (F1 a b α g) (F2 a b α g x) x := by
  have hgx_ne : g x ≠ 0 := ne_of_gt hx
  -- g' is differentiable (g is C²) with derivative deriv (deriv g)
  have hg'_has : HasDerivAt (deriv g) (deriv (deriv g) x) x := by
    have hC1 : ContDiff ℝ 1 (deriv g) := (contDiff_succ_iff_deriv.mp hg).2.2
    exact (hC1.differentiable (by norm_num) x).hasDerivAt
  have hg_has : HasDerivAt g (deriv g x) x :=
    (hg.differentiable (by norm_num) x).hasDerivAt
  -- d/dx g^α = α·g^{α−1}·g'
  have hpowα : HasDerivAt (fun y => g y ^ α)
      (deriv g x * α * g x ^ (α - 1)) x :=
    hg_has.rpow_const (Or.inl hgx_ne)
  -- second factor: a − b(1+α)g^α
  have hfac : HasDerivAt (fun y => a - b * (1 + α) * g y ^ α)
      (0 - b * (1 + α) * (deriv g x * α * g x ^ (α - 1))) x :=
    (hasDerivAt_const x a).sub ((hpowα.const_mul (b * (1 + α))).congr_deriv (by ring))
  -- product rule on F1 = g' · (a − b(1+α)g^α)
  have hprod := hg'_has.mul hfac
  refine hprod.congr_deriv ?_
  -- algebra: deriv(deriv g)·(a − b(1+α)g^α)
  --        + deriv g·(0 − b(1+α)·(deriv g · α · g^{α−1}))  =  F2
  simp only [F2]
  ring

/-- The certificate's weak second derivative equals the explicit `F2` on the
positivity neighborhood `[0,1]`. -/
theorem secondDeriv_eq_F2
    {a b α : ℝ} {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < g x)
    {x : ℝ} (hxmem : x ∈ Set.Icc (0 : ℝ) 1) :
    deriv (deriv (logisticSourceFun a b α g)) x = F2 a b α g x := by
  obtain ⟨U, hUopen, hKU, hUpos⟩ :=
    exists_pos_neighborhood_of_compact_positive hg.continuous isCompact_Icc hpos
  have hxU : x ∈ U := hKU hxmem
  -- deriv F = F1 on a neighborhood of x
  have hderivF_eq : deriv (logisticSourceFun a b α g) =ᶠ[nhds x] F1 a b α g := by
    filter_upwards [hUopen.mem_nhds hxU] with y hy
    exact (logisticSourceFun_hasDerivAt hg (hUpos y hy)).deriv
  rw [Filter.EventuallyEq.deriv_eq hderivF_eq]
  exact (F1_hasDerivAt hg (hUpos x hxU)).deriv

/-- Pointwise bound `|F2| ≤ B_log` on `[0,1]`. -/
theorem F2_abs_le_B_log
    {a b α M G1 G2 : ℝ} {g : ℝ → ℝ}
    (hα : 1 ≤ α) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hub : ∀ x ∈ Set.Icc (0 : ℝ) 1, g x ≤ M)
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < g x)
    (hG1 : ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv g x| ≤ G1)
    (hG2 : ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (deriv g) x| ≤ G2)
    {x : ℝ} (hxmem : x ∈ Set.Icc (0 : ℝ) 1) :
    |F2 a b α g x| ≤ B_log a b α M G1 G2 := by
  have hgx_pos : 0 < g x := hpos x hxmem
  have hgx_le : g x ≤ M := hub x hxmem
  have hgx_nn : 0 ≤ g x := le_of_lt hgx_pos
  have hM_pos : 0 < M := lt_of_lt_of_le hgx_pos hgx_le
  have hM_nn : 0 ≤ M := le_of_lt hM_pos
  have hG1x : |deriv g x| ≤ G1 := hG1 x hxmem
  have hG2x : |deriv (deriv g) x| ≤ G2 := hG2 x hxmem
  have hG1_nn : 0 ≤ G1 := le_trans (abs_nonneg _) hG1x
  have hG2_nn : 0 ≤ G2 := le_trans (abs_nonneg _) hG2x
  -- α - 1 ≥ 0
  have hexp_nn : (0 : ℝ) ≤ α - 1 := by linarith
  -- g^{α-1} ≤ M^{α-1}
  have hpow1 : g x ^ (α - 1) ≤ M ^ (α - 1) :=
    Real.rpow_le_rpow hgx_nn hgx_le hexp_nn
  have hpow1_nn : 0 ≤ g x ^ (α - 1) := Real.rpow_nonneg hgx_nn _
  -- g^α ≤ M^α
  have hpowα : g x ^ α ≤ M ^ α :=
    Real.rpow_le_rpow hgx_nn hgx_le (by linarith)
  have hpowα_nn : 0 ≤ g x ^ α := Real.rpow_nonneg hgx_nn _
  -- constants
  have h1α_nn : (0 : ℝ) ≤ 1 + α := by linarith
  have hbα : 0 ≤ b * α * (1 + α) := by positivity
  -- term 1 bound: |(-(bα(1+α)) g^{α-1} g') g'| = bα(1+α) g^{α-1} (g')²
  --   ≤ bα(1+α) M^{α-1} G1²
  have hterm1 :
      |(-(b * α * (1 + α)) * g x ^ (α - 1) * deriv g x) * deriv g x|
        ≤ b * α * (1 + α) * M ^ (α - 1) * G1 ^ 2 := by
    have hrw :
        |(-(b * α * (1 + α)) * g x ^ (α - 1) * deriv g x) * deriv g x|
          = b * α * (1 + α) * g x ^ (α - 1) * (deriv g x) ^ 2 := by
      rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_nonneg hbα,
          abs_of_nonneg hpow1_nn, ← sq_abs (deriv g x)]
      ring
    rw [hrw]
    have hsq : (deriv g x) ^ 2 ≤ G1 ^ 2 := by
      nlinarith [abs_nonneg (deriv g x), hG1x, sq_abs (deriv g x)]
    have hstep1 :
        b * α * (1 + α) * g x ^ (α - 1) * (deriv g x) ^ 2
          ≤ b * α * (1 + α) * M ^ (α - 1) * (deriv g x) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hpow1 hbα
    have hstep2 :
        b * α * (1 + α) * M ^ (α - 1) * (deriv g x) ^ 2
          ≤ b * α * (1 + α) * M ^ (α - 1) * G1 ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    linarith
  -- term 2 bound: |(a − b(1+α)g^α) g''| ≤ (a + b(1+α)M^α) G2
  have hterm2 :
      |(a - b * (1 + α) * g x ^ α) * deriv (deriv g) x|
        ≤ (a + b * (1 + α) * M ^ α) * G2 := by
    rw [abs_mul]
    have hfac_abs : |a - b * (1 + α) * g x ^ α| ≤ a + b * (1 + α) * M ^ α := by
      have hlow : -(a + b * (1 + α) * M ^ α) ≤ a - b * (1 + α) * g x ^ α := by
        have : b * (1 + α) * g x ^ α ≤ b * (1 + α) * M ^ α :=
          mul_le_mul_of_nonneg_left hpowα (by positivity)
        nlinarith [hpowα_nn]
      have hhigh : a - b * (1 + α) * g x ^ α ≤ a + b * (1 + α) * M ^ α := by
        nlinarith [hpowα_nn, mul_nonneg (by positivity : (0:ℝ) ≤ b * (1 + α)) hpowα_nn]
      exact abs_le.mpr ⟨hlow, hhigh⟩
    have hfac_nn : 0 ≤ a + b * (1 + α) * M ^ α := by
      have hMα_nn : 0 ≤ M ^ α := Real.rpow_nonneg hM_nn _
      positivity
    calc |a - b * (1 + α) * g x ^ α| * |deriv (deriv g) x|
        ≤ (a + b * (1 + α) * M ^ α) * |deriv (deriv g) x| :=
          mul_le_mul_of_nonneg_right hfac_abs (abs_nonneg _)
      _ ≤ (a + b * (1 + α) * M ^ α) * G2 :=
          mul_le_mul_of_nonneg_left hG2x hfac_nn
  -- combine via triangle inequality
  calc |F2 a b α g x|
      ≤ |(-(b * α * (1 + α)) * g x ^ (α - 1) * deriv g x) * deriv g x|
          + |(a - b * (1 + α) * g x ^ α) * deriv (deriv g) x| := by
        simp only [F2]; exact abs_add_le _ _
    _ ≤ b * α * (1 + α) * M ^ (α - 1) * G1 ^ 2
          + (a + b * (1 + α) * M ^ α) * G2 := add_le_add hterm1 hterm2
    _ = B_log a b α M G1 G2 := rfl

/-- `B_log` is nonnegative under the hypotheses. -/
theorem B_log_nonneg
    {a b α M G1 G2 : ℝ}
    (hα : 1 ≤ α) (ha : 0 ≤ a) (hb : 0 ≤ b) (hM : 0 ≤ M)
    (_hG1 : 0 ≤ G1) (hG2 : 0 ≤ G2) :
    0 ≤ B_log a b α M G1 G2 := by
  have hMα : 0 ≤ M ^ α := Real.rpow_nonneg hM _
  have hMα1 : 0 ≤ M ^ (α - 1) := Real.rpow_nonneg hM _
  have hαnn : 0 ≤ α := by linarith
  have h1α : 0 ≤ 1 + α := by linarith
  unfold B_log
  positivity

/-- **Explicit `W^{2,1}` bound for the logistic source.**
For `ContDiff ℝ 2 g`, `0 < g ≤ M` on `[0,1]`, `|g'| ≤ G1`, `|g''| ≤ G2` on
`[0,1]`, `1 ≤ α`, `0 ≤ a`, `0 ≤ b`:

  `∫₀¹ |deriv (deriv (logisticSourceFun a b α g)) x| dx ≤ B_log a b α M G1 G2`. -/
theorem logisticSourceFun_secondDeriv_abs_integral_le
    {a b α M G1 G2 : ℝ} {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g)
    (hα : 1 ≤ α) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < g x)
    (hub : ∀ x ∈ Set.Icc (0 : ℝ) 1, g x ≤ M)
    (hG1 : ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv g x| ≤ G1)
    (hG2 : ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (deriv g) x| ≤ G2) :
    (∫ x in (0 : ℝ)..1, |deriv (deriv (logisticSourceFun a b α g)) x|)
      ≤ B_log a b α M G1 G2 := by
  -- integrability of |second derivative|
  have hC2 : ContDiffOn ℝ 2 (logisticSourceFun a b α g) (Set.Icc (0 : ℝ) 1) :=
    logisticSourceFun_contDiffOn_Icc hg hpos
  have hint : IntervalIntegrable
      (deriv (deriv (logisticSourceFun a b α g))) volume (0 : ℝ) 1 :=
    intervalIntegrable_deriv_deriv_of_contDiffOn_two hC2
  have habs_int : IntervalIntegrable
      (fun x => |deriv (deriv (logisticSourceFun a b α g)) x|) volume (0 : ℝ) 1 := by
    simpa [Real.norm_eq_abs] using hint.norm
  calc
    (∫ x in (0 : ℝ)..1, |deriv (deriv (logisticSourceFun a b α g)) x|)
        ≤ ∫ _x in (0 : ℝ)..1, B_log a b α M G1 G2 := by
          refine intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
            habs_int intervalIntegrable_const ?_
          intro x hx
          have hxmem : x ∈ Set.Icc (0 : ℝ) 1 := by
            rcases hx with ⟨h0, h1⟩; exact ⟨h0, h1⟩
          rw [secondDeriv_eq_F2 hg hpos hxmem]
          exact F2_abs_le_B_log hα ha hb hub hpos hG1 hG2 hxmem
    _ = B_log a b α M G1 G2 := by
          rw [intervalIntegral.integral_const]; norm_num

/-- **Explicit quadratic cosine-coefficient decay for the logistic source.**
Under the same hypotheses (plus Neumann BC `deriv g 0 = deriv g 1 = 0`):

  `|cosineCoeffs (logisticSourceFun a b α g) k| ≤ 2·B_log / ((k:ℝ)·π)²`
  for every `k ≥ 1`. -/
theorem logisticSourceFun_cosineCoeff_quadratic_decay_explicit
    {a b α M G1 G2 : ℝ} {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g)
    (hα : 1 ≤ α) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < g x)
    (hub : ∀ x ∈ Set.Icc (0 : ℝ) 1, g x ≤ M)
    (hG1 : ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv g x| ≤ G1)
    (hG2 : ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (deriv g) x| ≤ G2)
    (hdg0 : deriv g 0 = 0) (hdg1 : deriv g 1 = 0) :
    ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs (logisticSourceFun a b α g) k|
        ≤ 2 * B_log a b α M G1 G2 / ((k : ℝ) * Real.pi) ^ 2 := by
  set hf := logisticSourceFun_intervalWeakH2Neumann hg hpos hdg0 hdg1 with hf_def
  -- hf.secondDeriv is definitionally deriv (deriv (logisticSourceFun a b α g))
  have hB : (∫ x in (0 : ℝ)..1, |hf.secondDeriv x|) ≤ B_log a b α M G1 G2 :=
    logisticSourceFun_secondDeriv_abs_integral_le hg hα ha hb hpos hub hG1 hG2
  exact ShenWork.IntervalSourceDecayQuantitative.intervalWeakH2Neumann_cosineCoeff_quadratic_decay_of_bound
    hf hB

end ShenWork.IntervalLogisticSourceQuantBound
