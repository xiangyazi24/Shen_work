/-
  ShenWork/Paper2/IntervalH1DIChiBetaAbsorption.lean

  **|χ₀|-form of the H¹ energy differential-inequality absorption.**

  `IntervalChiNegH1Energy.h1_diffIneq_of_sup_bounds` proves the H¹ scalar DI
  `-(lapL2sq) + (-χ₀)·taxisX + (-χ₀)·uvxx + reactX ≤ A·y + B` from the resolver
  sup-bound cross terms — but it takes the inputs in the `(-χ₀)·(…)` form, which
  is only the correct inequality direction when `χ₀ ≤ 0`.  (Note its own sign
  hypothesis `_ha : 0 ≤ -p.χ₀` is UNUSED — the Young absorption needs no sign.)

  For the Theorem 1.2 critical branch `χ₀ < chiBeta p` (where `χ₀` may be POSITIVE),
  the correct cross-term inputs are the ABSOLUTE-VALUE bounds
  `(-χ₀)·taxisX ≤ |χ₀|·(V₁·X·Z)` (from `|taxisX| ≤ V₁·X·Z`).  Since the output
  constants depend only on `χ₀²` (`|χ₀|² = (-χ₀)² = χ₀²`), the conclusion is
  IDENTICAL.  So this lemma discharges the same scalar DI for ANY `χ₀`, unblocking
  the 1D-Sobolev bypass route (which avoids the Moser γ<2 threshold) for the
  positive-sensitivity Theorem 1.2 regime.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalChiNegH1Energy
import ShenWork.Paper2.IntervalChiNegH1ScalarDIProducer

open ShenWork.IntervalDomain
open ShenWork.Paper2.IntervalChiNegH1ScalarDIProducer

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1Energy

/-- **|χ₀|-form H¹ differential-inequality absorption** — works for ANY `χ₀`
(including `0 < χ₀ < chiBeta`), from absolute-value resolver cross-term bounds.
Same `A = 2χ₀²V₁²+2L`, `B = χ₀²M²V₂²` conclusion as the `χ₀ ≤ 0` version. -/
theorem h1_diffIneq_of_sup_bounds_abs
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {τ taxisX uvxx reactX X Z yval V₁ V₂ M L : ℝ}
    (_hV1 : 0 ≤ V₁) (_hV2 : 0 ≤ V₂) (_hM : 0 ≤ M) (_hL : 0 ≤ L)
    (hXsq : lapL2sq u τ = X ^ 2) (hZsq : Z ^ 2 = 2 * yval) (_hXnn : 0 ≤ X)
    (htaxis : (-p.χ₀) * taxisX ≤ |p.χ₀| * (V₁ * (X * Z)))
    (huvxx : (-p.χ₀) * uvxx ≤ |p.χ₀| * (M * (V₂ * X)))
    (hreact : reactX ≤ L * Z ^ 2) :
    (-(lapL2sq u τ) + (-p.χ₀) * taxisX + (-p.χ₀) * uvxx + reactX)
      ≤ (2 * (-p.χ₀) ^ 2 * V₁ ^ 2 + 2 * L) * yval + (-p.χ₀) ^ 2 * M ^ 2 * V₂ ^ 2 := by
  set b : ℝ := |p.χ₀| with hbdef
  have hbsq : b ^ 2 = (-p.χ₀) ^ 2 := by rw [hbdef, sq_abs, neg_sq]
  have hy1 : b * (V₁ * (X * Z)) ≤ (1/4) * X ^ 2 + (b * V₁ * Z) ^ 2 / (4 * (1/4)) := by
    have := youngMul_le (p := X) (q := b * V₁ * Z) (ε := (1/4 : ℝ)) (by norm_num)
    nlinarith [this]
  have hy2 : b * (M * (V₂ * X)) ≤ (1/4) * X ^ 2 + (b * M * V₂) ^ 2 / (4 * (1/4)) := by
    have := youngMul_le (p := X) (q := b * M * V₂) (ε := (1/4 : ℝ)) (by norm_num)
    nlinarith [this]
  have hZ : Z ^ 2 = 2 * yval := hZsq
  rw [hXsq]
  have ht : (-p.χ₀) * taxisX ≤ (1/4) * X ^ 2 + (b * V₁ * Z) ^ 2 / (4 * (1/4)) :=
    le_trans htaxis hy1
  have hu : (-p.χ₀) * uvxx ≤ (1/4) * X ^ 2 + (b * M * V₂) ^ 2 / (4 * (1/4)) :=
    le_trans huvxx hy2
  have hr : reactX ≤ L * (2 * yval) := by rw [hZ] at hreact; exact hreact
  have hZ2 : (b * V₁ * Z) ^ 2 / (4 * (1/4)) = 2 * ((-p.χ₀) ^ 2 * V₁ ^ 2) * yval := by
    rw [show (4 : ℝ) * (1/4) = 1 by norm_num, div_one,
      show (b * V₁ * Z) ^ 2 = b ^ 2 * V₁ ^ 2 * Z ^ 2 by ring, hbsq, hZ]; ring
  have hM2 : (b * M * V₂) ^ 2 / (4 * (1/4)) = (-p.χ₀) ^ 2 * M ^ 2 * V₂ ^ 2 := by
    rw [show (4 : ℝ) * (1/4) = 1 by norm_num, div_one,
      show (b * M * V₂) ^ 2 = b ^ 2 * M ^ 2 * V₂ ^ 2 by ring, hbsq]
  rw [hZ2] at ht; rw [hM2] at hu
  nlinarith [ht, hu, hr]

/-- **|χ₀|-form sup-bound DI data** (no `hchi : 0 ≤ -χ₀` sign requirement): the
absolute-value cross-term bounds, valid for ANY `χ₀` (incl. `0 < χ₀ < chiBeta`). -/
structure H1SupBoundDIDataAbsBefore
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (T V₁ V₂ M L : ℝ) : Prop where
  hV1 : 0 ≤ V₁
  hV2 : 0 ≤ V₂
  hM : 0 ≤ M
  hL : 0 ≤ L
  point : ∀ τ, 0 < τ → τ < T →
    ∃ taxisX uvxx reactX X Z : ℝ,
      H1EnergyIdentity p u τ taxisX uvxx reactX ∧
      lapL2sq u τ = X ^ 2 ∧
      Z ^ 2 = 2 * H1energy u τ ∧
      0 ≤ X ∧
      (-p.χ₀) * taxisX ≤ |p.χ₀| * (V₁ * (X * Z)) ∧
      (-p.χ₀) * uvxx ≤ |p.χ₀| * (M * (V₂ * X)) ∧
      reactX ≤ L * Z ^ 2

/-- The |χ₀|-form DI data yields the SAME `H1IdentityRHSBoundBefore` RHS-bound
package as the `χ₀ ≤ 0` route (constants depend only on `χ₀²`), via the |χ₀|
absorption lemma.  This connects the positive-`χ₀` cross-term bounds to the
GENERIC scalar-DI reducer `H1ScalarDIOnBefore_of_identityRHSBound`. -/
theorem H1IdentityRHSBoundBefore_of_supBoundDIDataAbs
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (hdata : H1SupBoundDIDataAbsBefore p u T V₁ V₂ M L) :
    H1IdentityRHSBoundBefore p u T
      (2 * (-p.χ₀) ^ 2 * V₁ ^ 2 + 2 * L)
      ((-p.χ₀) ^ 2 * M ^ 2 * V₂ ^ 2) := by
  refine { hA := ?_, hB := ?_, bound := ?_ }
  · have h1 : 0 ≤ 2 * (-p.χ₀) ^ 2 * V₁ ^ 2 := by positivity
    have h2 : 0 ≤ 2 * L := by linarith [hdata.hL]
    linarith
  · positivity
  · intro τ hτ0 hτT
    rcases hdata.point τ hτ0 hτT with
      ⟨taxisX, uvxx, reactX, X, Z, hEnergy, hXsq, hZsq, hXnn,
        htaxis, huvxx, hreact⟩
    refine ⟨taxisX, uvxx, reactX, hEnergy, ?_⟩
    exact h1_diffIneq_of_sup_bounds_abs
      hdata.hV1 hdata.hV2 hdata.hM hdata.hL hXsq hZsq hXnn htaxis huvxx hreact

end ShenWork.Paper2.IntervalChiNegH1Energy
