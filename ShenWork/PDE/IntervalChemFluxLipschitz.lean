/-
  ShenWork/PDE/IntervalChemFluxLipschitz.lean

  T7 existence — **glue atom 1**: the chemotaxis flux
  `Q(u)(y) = u(y)·∂ₓR(u)(y)/(1+R(u)(y))^β` is sup-Lipschitz on the trajectory
  ball, given the resolver `C⁰→C¹` bounds (Atom B) and `R ≥ 0` (O1).

  This file starts with the denominator factor `(1+r)^{−β}`: with `R ≥ 0` the
  base is `≥ 1`, so `(1+r)^{−β}` is well-defined and globally `β`-Lipschitz on
  `[0,∞)` (its derivative `−β(1+r)^{−β−1}` has modulus `≤ β`).

  No `sorry`, no `admit`, no custom `axiom`.
-/
import ShenWork.Paper2.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open Set Real

noncomputable section

namespace ShenWork.IntervalChemFluxLipschitz

/-- **`(1+r)^{−β}` is `β`-Lipschitz on `[0,∞)`** (`β ≥ 0`).  The base `1+r ≥ 1` is
nonzero, so `f(r)=(1+r)^{−β}` is differentiable with `f'(r)=−β(1+r)^{−β−1}`, and
`|f'(r)| = β(1+r)^{−β−1} ≤ β` since `(1+r)^{−β−1} ≤ 1` (base `≥ 1`, exponent
`≤ 0`).  Hence the mean-value Lipschitz bound. -/
theorem oneAddRpow_neg_lipschitz {β : ℝ} (hβ : 0 ≤ β) {r₁ r₂ : ℝ}
    (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) :
    |(1 + r₁) ^ (-β) - (1 + r₂) ^ (-β)| ≤ β * |r₁ - r₂| := by
  set f : ℝ → ℝ := fun r => (1 + r) ^ (-β) with hf
  set fp : ℝ → ℝ := fun r => -β * (1 + r) ^ (-β - 1) with hfp
  have hder : ∀ r ∈ Set.Ici (0:ℝ), HasDerivWithinAt f (fp r) (Set.Ici 0) r := by
    intro r hr
    have hbase : (0:ℝ) < 1 + r := by have := (Set.mem_Ici.mp hr); linarith
    have hpow : HasDerivAt (fun b : ℝ => b ^ (-β)) (-β * (1 + r) ^ (-β - 1)) (1 + r) :=
      Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hbase))
    have hinner : HasDerivAt (fun r : ℝ => 1 + r) 1 r := by
      simpa using (hasDerivAt_const r (1:ℝ)).add (hasDerivAt_id r)
    have hcomp : HasDerivAt f (-β * (1 + r) ^ (-β - 1) * 1) r := by
      simpa [hf] using hpow.comp r hinner
    rw [mul_one] at hcomp
    exact hcomp.hasDerivWithinAt
  have hbound : ∀ r ∈ Set.Ici (0:ℝ), ‖fp r‖ ≤ β := by
    intro r hr
    have hbase : (1:ℝ) ≤ 1 + r := by have := (Set.mem_Ici.mp hr); linarith
    have hle1 : (1 + r) ^ (-β - 1) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hbase (by linarith)
    have hpos : 0 ≤ (1 + r) ^ (-β - 1) := Real.rpow_nonneg (by linarith) _
    rw [hfp, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hβ, abs_of_nonneg hpos]
    calc β * (1 + r) ^ (-β - 1) ≤ β * 1 := by gcongr
      _ = β := mul_one β
  have hconv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbound
    (convex_Ici 0) (Set.mem_Ici.mpr hr₂) (Set.mem_Ici.mpr hr₁)
  simpa [hf, Real.norm_eq_abs] using hconv

end ShenWork.IntervalChemFluxLipschitz
