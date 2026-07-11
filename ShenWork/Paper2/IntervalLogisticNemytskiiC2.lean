import Mathlib

/-!
# Logistic Nemytskii second-derivative bound — δ-free for α ≥ 1 (Q4351)

For the logistic reaction `S(u) = a·u - b·u^{α+1}` with `u ≥ 0`, the formal second
derivative is

  S'' = a·u'' - b·( (α+1)·α·u^{α-1}·(u')² + (α+1)·u^α·u'' ).

The ChatGPT-verified audit (Q4351) confirmed: for `α ≥ 1` **no positive lower
floor `δ ≤ u` is needed** — the only exponents `α-1, α` are nonnegative, so the
powers are bounded above by `M^{α-1}, M^α` from `0 ≤ u ≤ M` alone.  (The δ-floor
is genuinely required only on the resolver source `u^γ` with `1 < γ < 2`, where
`γ-2 < 0` — a different lemma.)

This file formalizes the δ-free pointwise `C²` estimate as a standalone `0`-sorry
lemma, taking the second-derivative expression as given (the `HasDerivAt` chain
rule for `Real.rpow` on the nonnegative side is a separate calculus build).
Self-contained: Mathlib only.
-/

namespace ShenWork.Paper2.LogisticNemytskiiC2

open Real

/-- **δ-free logistic Nemytskii `C²` bound.**  Given the pointwise second-derivative
expression of `S(u) = a·u - b·u^{α+1}`, and `0 ≤ u ≤ M`, `α ≥ 1`, `|u'| ≤ B₁`,
`|u''| ≤ B₂`, the clean sup bound

  |S''| ≤ (|a| + |b|·(α+1)·M^α)·B₂ + |b|·(α+1)·α·M^{α-1}·B₁²

holds with **no lower floor on `u`**. -/
theorem logistic_secondDeriv_abs_le
    {a b α u u' u'' M B₁ B₂ : ℝ}
    (hu0 : 0 ≤ u) (huM : u ≤ M) (hα : 1 ≤ α)
    (hu' : |u'| ≤ B₁) (hu'' : |u''| ≤ B₂) :
    |a * u'' - b * ((α + 1) * α * u ^ (α - 1) * u' ^ 2 + (α + 1) * u ^ α * u'')|
      ≤ (|a| + |b| * (α + 1) * M ^ α) * B₂ + |b| * (α + 1) * α * M ^ (α - 1) * B₁ ^ 2 := by
  have hM : 0 ≤ M := le_trans hu0 huM
  have hB₁ : 0 ≤ B₁ := le_trans (abs_nonneg _) hu'
  have hB₂ : 0 ≤ B₂ := le_trans (abs_nonneg _) hu''
  have hα1 : 0 ≤ α + 1 := by linarith
  have hα0 : 0 ≤ α := by linarith
  -- power bounds (nonnegative exponents ⇒ monotone in base, no floor)
  have hP0 : 0 ≤ u ^ (α - 1) := Real.rpow_nonneg hu0 _
  have hPM : u ^ (α - 1) ≤ M ^ (α - 1) := Real.rpow_le_rpow hu0 huM (by linarith)
  have hQ0 : 0 ≤ u ^ α := Real.rpow_nonneg hu0 _
  have hQM : u ^ α ≤ M ^ α := Real.rpow_le_rpow hu0 huM hα0
  have hMP0 : 0 ≤ M ^ (α - 1) := Real.rpow_nonneg hM _
  have hMQ0 : 0 ≤ M ^ α := Real.rpow_nonneg hM _
  -- (u')² ≤ B₁²
  have hsq : u' ^ 2 ≤ B₁ ^ 2 := by
    have := abs_le.mp hu'
    nlinarith [this.1, this.2, hB₁]
  have hsq0 : 0 ≤ u' ^ 2 := sq_nonneg _
  -- |u''| ≤ B₂ already
  -- Split |a·u'' - b·(T1 + T2)| ≤ |a·u''| + |b|·(|T1| + |T2|)
  set T1 : ℝ := (α + 1) * α * u ^ (α - 1) * u' ^ 2 with hT1
  set T2 : ℝ := (α + 1) * u ^ α * u'' with hT2
  have step1 := abs_add_le (a * u'') (-(b * (T1 + T2)))
  rw [← sub_eq_add_neg, abs_neg] at step1
  -- step1 : |a·u'' - b·(T1+T2)| ≤ |a·u''| + |b·(T1+T2)|
  -- bound |a·u''|
  have ha : |a * u''| ≤ |a| * B₂ := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hu'' (abs_nonneg _)
  -- bound |b·(T1+T2)| ≤ |b|·(|T1|+|T2|)
  have hbT : |b * (T1 + T2)| ≤ |b| * (|T1| + |T2|) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)
  -- |T1| = T1 (nonneg) ≤ (α+1)·α·M^{α-1}·B₁²
  have hT1nonneg : 0 ≤ T1 := by rw [hT1]; positivity
  have hT1bd : |T1| ≤ (α + 1) * α * M ^ (α - 1) * B₁ ^ 2 := by
    rw [abs_of_nonneg hT1nonneg, hT1]
    have h1 : u ^ (α - 1) * u' ^ 2 ≤ M ^ (α - 1) * B₁ ^ 2 :=
      mul_le_mul hPM hsq hsq0 hMP0
    have hc : 0 ≤ (α + 1) * α := mul_nonneg hα1 hα0
    calc (α + 1) * α * u ^ (α - 1) * u' ^ 2
        = (α + 1) * α * (u ^ (α - 1) * u' ^ 2) := by ring
      _ ≤ (α + 1) * α * (M ^ (α - 1) * B₁ ^ 2) := mul_le_mul_of_nonneg_left h1 hc
      _ = (α + 1) * α * M ^ (α - 1) * B₁ ^ 2 := by ring
  -- |T2| = (α+1)·u^α·|u''| ≤ (α+1)·M^α·B₂
  have hT2bd : |T2| ≤ (α + 1) * M ^ α * B₂ := by
    rw [hT2, abs_mul, abs_mul, abs_of_nonneg hα1, abs_of_nonneg hQ0]
    have h2 : u ^ α * |u''| ≤ M ^ α * B₂ := mul_le_mul hQM hu'' (abs_nonneg _) hMQ0
    calc (α + 1) * u ^ α * |u''|
        = (α + 1) * (u ^ α * |u''|) := by ring
      _ ≤ (α + 1) * (M ^ α * B₂) := mul_le_mul_of_nonneg_left h2 hα1
      _ = (α + 1) * M ^ α * B₂ := by ring
  -- combine
  have hbnonneg : 0 ≤ |b| := abs_nonneg _
  calc |a * u'' - b * (T1 + T2)|
      ≤ |a * u''| + |b * (T1 + T2)| := step1
    _ ≤ |a| * B₂ + |b| * (|T1| + |T2|) := by gcongr
    _ ≤ |a| * B₂ + |b| * ((α + 1) * α * M ^ (α - 1) * B₁ ^ 2 + (α + 1) * M ^ α * B₂) := by
        gcongr
    _ = (|a| + |b| * (α + 1) * M ^ α) * B₂ + |b| * (α + 1) * α * M ^ (α - 1) * B₁ ^ 2 := by
        ring

/-! ## HasDerivAt derivative towers (Q4363) — produce the second-derivative
expression the bound above consumes, valid at `u = 0` (no strict positivity). -/

/-- **First derivative of `u^{α+1}`** via `HasDerivAt.rpow_const` with the right
disjunct `1 ≤ α+1` — fires even when `u x = 0`. -/
theorem powSucc_hasDerivAt
    {α : ℝ} {u u1 : ℝ → ℝ} {x : ℝ}
    (hu0 : HasDerivAt u (u1 x) x) (hα : 1 ≤ α) :
    HasDerivAt (fun y => u y ^ (α + 1)) (u1 x * (α + 1) * u x ^ α) x := by
  have hα1 : (1 : ℝ) ≤ α + 1 := by linarith
  have h := hu0.rpow_const (p := α + 1) (Or.inr hα1)
  rw [show (α + 1) - 1 = α from by ring] at h
  exact h

/-- **Derivative of `P₁ = u'·(α+1)·u^α`** (the second-derivative wiring for
`u^{α+1}`) — differentiates `u^α` via the right disjunct `1 ≤ α`, valid at `u=0`. -/
theorem powSucc_deriv_hasDerivAt
    {α : ℝ} {u u1 u2 : ℝ → ℝ} {x : ℝ}
    (hu0 : HasDerivAt u (u1 x) x) (hu1 : HasDerivAt u1 (u2 x) x) (hα : 1 ≤ α) :
    HasDerivAt (fun y => u1 y * (α + 1) * u y ^ α)
      (u2 x * (α + 1) * u x ^ α + u1 x * (α + 1) * (u1 x * α * u x ^ (α - 1))) x := by
  have hpowα : HasDerivAt (fun y => u y ^ α) (u1 x * α * u x ^ (α - 1)) x :=
    hu0.rpow_const (p := α) (Or.inr hα)
  have hcoef : HasDerivAt (fun y => u1 y * (α + 1)) (u2 x * (α + 1)) x :=
    hu1.mul_const (α + 1)
  have h := hcoef.mul hpowα
  exact h

/-- **Full logistic source second derivative** `S(u)=a·u−b·u^{α+1}` — `HasDerivAt`
of `S'` at value `S'' = a·u'' − b·((α+1)α·u^{α-1}(u')² + (α+1)·u^α·u'')`, valid at
`u ≥ 0` (base possibly `0`).  This is the derivative-tower residual now closed;
composing with `logistic_secondDeriv_abs_le` bounds `|S''|` with no δ-floor. -/
theorem logistic_source_secondDeriv_hasDerivAt
    {a b α : ℝ} {u u1 u2 : ℝ → ℝ} {x : ℝ}
    (hu0 : HasDerivAt u (u1 x) x) (hu1 : HasDerivAt u1 (u2 x) x) (hα : 1 ≤ α) :
    HasDerivAt (fun y => a * u1 y - b * (u1 y * (α + 1) * u y ^ α))
      (a * u2 x - b * (u2 x * (α + 1) * u x ^ α
        + u1 x * (α + 1) * (u1 x * α * u x ^ (α - 1)))) x := by
  have hP1 := powSucc_deriv_hasDerivAt hu0 hu1 hα
  exact (hu1.const_mul a).sub (hP1.const_mul b)

end ShenWork.Paper2.LogisticNemytskiiC2
