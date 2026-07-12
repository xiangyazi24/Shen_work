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
import ShenWork.Paper2.IntervalChiNegH1SupBoundDIProducer
import ShenWork.Paper2.IntervalChiNegH1AverageWiring

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1ScalarDIProducer
open ShenWork.Paper2.IntervalChiNegH1SupBoundDIProducer
open ShenWork.Paper2.IntervalChiNegH1AverageWiring
open ShenWork.IntervalDomainExistence

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

/-- **Produce the |χ₀|-form DI data from χ-AGNOSTIC absolute-value resolver term
bounds.**  `|taxisX| ≤ V₁·‖Δu‖·‖∇u‖` etc. are sign-independent physical resolver
estimates (the H¹ chemotaxis/uvxx bounds), so this producer works for ANY `χ₀`
(incl. `0 < χ₀ < chiBeta`): it derives `(-χ₀)·taxisX ≤ |χ₀|·(V₁·X·Z)` from the abs
bound.  This reduces the χ₀<chiBeta Theorem 1.2 H¹-DI residual to exactly the abs
resolver term bounds (which the physical resolver machinery supplies). -/
theorem H1SupBoundDIDataAbsBefore_of_absTermBounds
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hV1 : 0 ≤ V₁) (hV2 : 0 ≤ V₂) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hId : ∀ τ, 0 < τ → τ < T →
      H1EnergyIdentity p u τ (taxisX τ) (uvxx τ) (reactX τ))
    (htaxisAbs : ∀ τ, 0 < τ → τ < T →
      |taxisX τ| ≤ V₁ * (H1lapL2Norm u τ * H1gradL2Norm u τ))
    (huvxxAbs : ∀ τ, 0 < τ → τ < T →
      |uvxx τ| ≤ M * (V₂ * H1lapL2Norm u τ))
    (hreactB : ∀ τ, 0 < τ → τ < T →
      reactX τ ≤ L * (H1gradL2Norm u τ) ^ 2) :
    H1SupBoundDIDataAbsBefore p u T V₁ V₂ M L := by
  refine { hV1 := hV1, hV2 := hV2, hM := hM, hL := hL, point := ?_ }
  intro τ hτ0 hτT
  refine ⟨taxisX τ, uvxx τ, reactX τ, H1lapL2Norm u τ, H1gradL2Norm u τ,
    hId τ hτ0 hτT, lapL2sq_eq_H1lapL2Norm_sq u τ, H1gradL2Norm_sq u τ,
    H1lapL2Norm_nonneg u τ, ?_, ?_, hreactB τ hτ0 hτT⟩
  · calc (-p.χ₀) * taxisX τ
        ≤ |(-p.χ₀) * taxisX τ| := le_abs_self _
      _ = |p.χ₀| * |taxisX τ| := by rw [abs_mul, abs_neg]
      _ ≤ |p.χ₀| * (V₁ * (H1lapL2Norm u τ * H1gradL2Norm u τ)) :=
          mul_le_mul_of_nonneg_left (htaxisAbs τ hτ0 hτT) (abs_nonneg _)
  · calc (-p.χ₀) * uvxx τ
        ≤ |(-p.χ₀) * uvxx τ| := le_abs_self _
      _ = |p.χ₀| * |uvxx τ| := by rw [abs_mul, abs_neg]
      _ ≤ |p.χ₀| * (M * (V₂ * H1lapL2Norm u τ)) :=
          mul_le_mul_of_nonneg_left (huvxxAbs τ hτ0 hτT) (abs_nonneg _)

/-- **Connector: abs resolver term bounds + H¹ scalar regularity → `H1ScalarDIOnBefore`**
(the `hDI` input of the 1D bypass entry `intervalDomain_boundedBefore_of_paperPositive_
H1scalarDI_local`).  Valid for ANY `χ₀` (incl. `0 < χ₀ < chiBeta`).  Composes the whole
|χ₀| chain, so the positive-`χ₀` Theorem 1.2 damped branch reduces to: the abs term
bounds + H¹ scalar regularity + the bypass frontiers (IntervalDomainBoundednessHyp incl.
`γ·N<2`, L² seed frontier, local H¹ start). -/
theorem H1ScalarDIOnBefore_of_absTermBounds
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hreg : H1ScalarRegularityBefore u T)
    (hV1 : 0 ≤ V₁) (hV2 : 0 ≤ V₂) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hId : ∀ τ, 0 < τ → τ < T →
      H1EnergyIdentity p u τ (taxisX τ) (uvxx τ) (reactX τ))
    (htaxisAbs : ∀ τ, 0 < τ → τ < T →
      |taxisX τ| ≤ V₁ * (H1lapL2Norm u τ * H1gradL2Norm u τ))
    (huvxxAbs : ∀ τ, 0 < τ → τ < T →
      |uvxx τ| ≤ M * (V₂ * H1lapL2Norm u τ))
    (hreactB : ∀ τ, 0 < τ → τ < T →
      reactX τ ≤ L * (H1gradL2Norm u τ) ^ 2) :
    H1ScalarDIOnBefore u T
      (2 * (-p.χ₀) ^ 2 * V₁ ^ 2 + 2 * L)
      ((-p.χ₀) ^ 2 * M ^ 2 * V₂ ^ 2) :=
  H1ScalarDIOnBefore_of_identityRHSBound hreg
    (H1IdentityRHSBoundBefore_of_supBoundDIDataAbs
      (H1SupBoundDIDataAbsBefore_of_absTermBounds
        hV1 hV2 hM hL hId htaxisAbs huvxxAbs hreactB))

/-- **Capstone: `IsPaper2BoundedBefore` for the positive-`χ₀` Theorem 1.2 damped
branch, from abs resolver term bounds + standard frontiers.**  Composes the full
|χ₀| H¹-DI chain with the 1D-Sobolev bypass.  Reduces the eventual-`L∞`-boundedness
half of Theorem 1.2 (for `0 < χ₀ < chiBeta`, under `IntervalDomainBoundednessHyp`
incl. `γ·N<2, 2γ<α, 0<b`) to EXACTLY: the sign-agnostic abs resolver term bounds +
H¹ scalar regularity (Codex's physical resolver machinery) + the standard frontiers
(L² seed regularity, local H¹ start). -/
theorem intervalDomain_boundedBefore_of_absTermBounds_and_frontiers
    {p : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    {V₁ V₂ M L Ylocal : ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hbounded : IntervalDomainBoundednessHyp p)
    (ha : 0 < p.a)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    (hreg : H1ScalarRegularityBefore u T)
    (hV1 : 0 ≤ V₁) (hV2 : 0 ≤ V₂) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hId : ∀ τ, 0 < τ → τ < T →
      H1EnergyIdentity p u τ (taxisX τ) (uvxx τ) (reactX τ))
    (htaxisAbs : ∀ τ, 0 < τ → τ < T →
      |taxisX τ| ≤ V₁ * (H1lapL2Norm u τ * H1gradL2Norm u τ))
    (huvxxAbs : ∀ τ, 0 < τ → τ < T →
      |uvxx τ| ≤ M * (V₂ * H1lapL2Norm u τ))
    (hreactB : ∀ τ, 0 < τ → τ < T →
      reactX τ ≤ L * (H1gradL2Norm u τ) ^ 2)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → H1energy u τ ≤ Ylocal) :
    IsPaper2BoundedBefore intervalDomain T u :=
  intervalDomain_boundedBefore_of_paperPositive_H1scalarDI_local
    hbounded ha hu₀ hT hsol htrace hfrontier
    (H1ScalarDIOnBefore_of_absTermBounds hreg hV1 hV2 hM hL hId
      htaxisAbs huvxxAbs hreactB)
    hlocal

end ShenWork.Paper2.IntervalChiNegH1Energy
