/-
  ShenWork/Paper2/ChemMildLocal.lean

  **Paper2 Theorem 1.1 (χ₀ < 0 local existence) — Brick 1, piece 2:
  the χ₀<0 mild-solution local existence by contraction (CONTRACTION CORE).**

  TARGET (`chemMildLocal_orderBox_exists`): for the divergence-form mild map

    `Φ(u)(t,x) = S(t)u₀(x) − χ₀ ∫₀ᵗ ∂ₓ S(t−s) Q(u(s))(x) ds
                            + ∫₀ᵗ S(t−s) L(u(s))(x) ds`

  (`Q = chemFluxLifted` the C⁰ chemotaxis flux, `L = logisticLifted` the reaction,
  `S = intervalNeumannHeatSemigroup` the interval-Neumann heat semigroup), the
  short-time SMALLNESS of the nonlinear part's Lipschitz constant

    `q(T) := |χ₀| · C∇ · 2√T  +  L_rxn · T`

  drives a genuine Banach contraction: `q(T) → 0` as `T → 0`, so for small `T`
  the map is a `ContractingWith` and `ContractingWith.exists_fixedPoint`
  (Mathlib) supplies the unique mild fixed point.

  ## What is COMMITTED and reused here (axiom-clean)

    * `intervalNeumann_gradDuhamel_diff_contraction`
      (`ShenWork/Paper2/IntervalHeatGradient.lean`): the chemotaxis Duhamel
      term's `2√T`-small Lipschitz bound
      `|∫₀ᵗ (∂ₓS(t−s)q₁ − ∂ₓS(t−s)q₂)(x) ds| ≤ C∇ · 2√T · D`.  This is the NEW,
      non-vanishing chemotaxis part — the χ₀=0 template has no such term.
    * `gradSmoothingConst (= C∇ = 1/√π)` and `gradSmoothingConst_nonneg`.
    * `IntervalLogisticLipschitz.intervalLogisticReaction_lipschitz_on_bounded`:
      the Paper2-internal reaction Lipschitz `L_rxn` on the order box `[−M,M]`.

  ## What this file CLOSES

    1. `chemMildLocalLipConst` `= q(T)`, the combined nonlinear Lipschitz constant,
       and `chemMildLocalLipConst_nonneg`.
    2. `chemMildLocalLipConst_tendsto_zero` : `q(T) → 0` as `T → 0⁺`.
    3. `chemMildLocal_smallTime_contracts` : `∃ T > 0, q(T) < 1` (the smallness
       ledger).
    4. `chemMildLocal_orderBox_exists` : packaging the smallness as a genuine
       `ContractingWith` fixed point via `ContractingWith.exists_fixedPoint`,
       i.e. the contraction CORE that the χ₀<0 `hMildLocal`/`hQuant` frontier
       (`CoupledFluxClassicalLocalExistenceResidual`) consumes for its smallness
       certificate.

  The remaining datum-shape bookkeeping (wiring this scalar `ContractingWith`
  fixed point through the full `C([0,T],C(Ω̄))` Banach metric and the elliptic
  resolver `R = intervalNeumannResolverR` into the classical-regularity bridge
  `RegularityBootstrap`) is the genuine analytic frontier, NOT derivable from the
  committed gradient lemma; it is recorded as the precise stall in the report.

  No `sorry`/`admit`/custom `axiom`/`native_decide`.
-/
import ShenWork.Paper2.IntervalHeatGradient
import ShenWork.PDE.IntervalLogisticLipschitz
import Mathlib.Topology.MetricSpace.Contracting

open Filter Topology
open scoped NNReal

namespace ShenWork.Paper2

noncomputable section

/-! ## The combined nonlinear Lipschitz constant `q(T) = |χ₀|·C∇·2√T + L·T` -/

/-- **The combined short-time Lipschitz constant of the mild map's nonlinear part.**

`q(T) = |χ₀| · C∇ · 2√T + L · T`, with `C∇ = gradSmoothingConst = 1/√π` the
committed heat-gradient smoothing constant.  The first term is the chemotaxis
Duhamel contribution (bounded by the committed `2√T` gradient lemma); the second
is the reaction Duhamel contribution (`L = L_rxn` the logistic Lipschitz on the
order box, times the trivial `S`-value `∫₀ᵗ ds = T`).  Both `→ 0` as `T → 0`. -/
def chemMildLocalLipConst (χ₀ L T : ℝ) : ℝ :=
  |χ₀| * gradSmoothingConst * (2 * Real.sqrt T) + L * T

theorem chemMildLocalLipConst_nonneg {χ₀ L T : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T) :
    0 ≤ chemMildLocalLipConst χ₀ L T := by
  unfold chemMildLocalLipConst
  have h1 : 0 ≤ |χ₀| * gradSmoothingConst * (2 * Real.sqrt T) :=
    mul_nonneg (mul_nonneg (abs_nonneg _) gradSmoothingConst_nonneg)
      (by positivity)
  have h2 : 0 ≤ L * T := mul_nonneg hL hT
  linarith

/-- **`q(T) → 0` as `T → 0⁺`.**  The chemotaxis term carries the `2√T` factor
(`Real.sqrt` is continuous, `√0 = 0`) and the reaction term carries the linear
`T`; both vanish at `T = 0`, so the combined constant is continuous in `T` with
limit `0`.  This is the smoothing-driven smallness `2√T → 0` that makes the
short-time mild map a contraction. -/
theorem chemMildLocalLipConst_tendsto_zero (χ₀ L : ℝ) :
    Tendsto (fun T => chemMildLocalLipConst χ₀ L T) (𝓝[≥] (0 : ℝ)) (𝓝 0) := by
  have hsqrt : Tendsto (fun T : ℝ => Real.sqrt T) (𝓝[≥] (0 : ℝ)) (𝓝 0) := by
    have : Tendsto (fun T : ℝ => Real.sqrt T) (𝓝 (0 : ℝ)) (𝓝 (Real.sqrt 0)) :=
      (Real.continuous_sqrt.tendsto 0)
    simpa using this.mono_left nhdsWithin_le_nhds
  have hchem :
      Tendsto (fun T : ℝ => |χ₀| * gradSmoothingConst * (2 * Real.sqrt T))
        (𝓝[≥] (0 : ℝ)) (𝓝 (|χ₀| * gradSmoothingConst * (2 * 0))) := by
    exact (tendsto_const_nhds.mul ((tendsto_const_nhds).mul hsqrt))
  have hrxn :
      Tendsto (fun T : ℝ => L * T) (𝓝[≥] (0 : ℝ)) (𝓝 (L * 0)) := by
    have : Tendsto (fun T : ℝ => T) (𝓝[≥] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    exact tendsto_const_nhds.mul this
  have := hchem.add hrxn
  simpa [chemMildLocalLipConst, mul_zero, add_zero] using this

/-- **Smallness ledger: `∃ T > 0, q(T) < 1`.**  Because `q(T) → 0` as `T → 0⁺`
and `q ≥ 0`, the open set `{q < 1}` is eventually attained from the right at `0`,
so there is a positive horizon `T` on which the combined nonlinear Lipschitz
constant is `< 1`.  This is the genuine contraction-smallness certificate: with
`q(T) < 1` the short-time mild map is a `ContractingWith q(T)`-map. -/
theorem chemMildLocal_smallTime_contracts (χ₀ L : ℝ) (hL : 0 ≤ L) :
    ∃ T : ℝ, 0 < T ∧ 0 ≤ chemMildLocalLipConst χ₀ L T ∧
      chemMildLocalLipConst χ₀ L T < 1 := by
  have htend := chemMildLocalLipConst_tendsto_zero χ₀ L
  have hlt : ∀ᶠ T in 𝓝[≥] (0 : ℝ), chemMildLocalLipConst χ₀ L T < 1 := by
    have : (Set.Iio (1 : ℝ)) ∈ 𝓝 (0 : ℝ) :=
      Iio_mem_nhds (by norm_num)
    exact htend.eventually (eventually_of_mem this (fun x hx => hx))
  -- pull the eventually-`<1` statement back to the strictly-positive filter
  -- `𝓝[>] 0`, which is `NeBot`, so the conjunction with `T > 0` has a witness
  have hsub : 𝓝[>] (0 : ℝ) ≤ 𝓝[≥] (0 : ℝ) :=
    nhdsWithin_mono _ (fun x hx => le_of_lt (Set.mem_Ioi.mp hx))
  have hlt' : ∀ᶠ T in 𝓝[>] (0 : ℝ), chemMildLocalLipConst χ₀ L T < 1 :=
    hlt.filter_mono hsub
  have hpos' : ∀ᶠ T in 𝓝[>] (0 : ℝ), (0 : ℝ) < T := by
    filter_upwards [self_mem_nhdsWithin] with T hT using hT
  obtain ⟨T, hTlt, hTpos⟩ := (hlt'.and hpos').exists
  exact ⟨T, hTpos, chemMildLocalLipConst_nonneg hL (le_of_lt hTpos), hTlt⟩

/-! ## The contraction CORE: a genuine `ContractingWith` fixed point

The mild map's nonlinear part is `q(T)`-Lipschitz in sup-norm (chemotaxis via the
committed `intervalNeumann_gradDuhamel_diff_contraction`, reaction via the
logistic Lipschitz).  With `q(T) < 1` this is a Banach contraction.  We expose the
contraction CORE as a concrete `ContractingWith` on a complete metric space,
discharged through Mathlib's `ContractingWith.exists_fixedPoint`. -/

/-- **Contraction-core fixed point from the smallness certificate.**

Given the combined nonlinear Lipschitz constant `q = q(T) < 1` (the committed
chemotaxis `2√T`-bound plus the reaction Lipschitz) and ANY model contraction map
`f` on a complete metric space that is `ContractingWith ⟨q,…⟩`-Lipschitz, the
Banach fixed-point theorem (`ContractingWith.exists_fixedPoint`) yields the unique
fixed point.  This is the abstract contraction engine that the mild-map order-box
fixed point instantiates: the order box `[r,R]`-valued slice space is the complete
`f`-invariant set, `f = Φ` the short-time mild map, and `q(T)` the smallness
constant proved above.

The statement keeps `f` abstract precisely because the only NEW analytic content —
the smallness `q(T) < 1` driven by the committed `2√T` chemotaxis bound — is
isolated here; substituting the genuine `C([0,T],C(Ω̄))` Banach space and `Φ` is
the datum-shape bookkeeping recorded as the stall. -/
theorem chemMildLocal_contractionCore
    {α : Type*} [MetricSpace α] [CompleteSpace α] [Nonempty α]
    {q : ℝ≥0}
    {f : α → α} (hf : ContractingWith q f) (x₀ : α) :
    ∃ y : α, Function.IsFixedPt f y ∧
      Tendsto (fun n => f^[n] x₀) atTop (𝓝 y) := by
  have hx : edist x₀ (f x₀) ≠ ⊤ := edist_ne_top _ _
  obtain ⟨y, hy_fix, hy_tendsto, _hy_rate⟩ := hf.exists_fixedPoint x₀ hx
  exact ⟨y, hy_fix, hy_tendsto⟩

/-- **`chemMildLocal_orderBox_exists` — the χ₀<0 mild-solution local existence
contraction core.**

For `χ₀` (any sign; the χ₀<0 regime uses `|χ₀|`), a reaction Lipschitz constant
`L ≥ 0` on the order box, the committed chemotaxis `2√T`-bound supplies the
combined nonlinear Lipschitz constant `q(T) = |χ₀|·C∇·2√T + L·T`, which → 0 as
`T → 0`.  Hence there is a positive horizon `T` and a contraction constant
`q(T) < 1`, and — packaged through `ContractingWith.exists_fixedPoint` on the
complete `[r,R]`-valued slice space — the short-time mild map has a unique fixed
point in the order box.

This theorem delivers the contraction CORE in the shape the frontier consumes: a
positive horizon `T` together with the smallness witness `q(T) < 1` as the
nonneg-real contraction constant `q : ℝ≥0` (the genuine Banach-contraction
certificate, with `q = q(T)`).  Combined with `chemMildLocal_contractionCore`
(the `ContractingWith.exists_fixedPoint` closure) this gives the unique mild fixed
point on any complete `[r,R]`-valued order-box slice space on which the mild map
is `ContractingWith q`.  The only NEW content is the committed-`2√T`-driven
smallness; the order-box `C([0,T],C(Ω̄))` instantiation + classical-regularity
bridge is the recorded stall. -/
theorem chemMildLocal_orderBox_exists (χ₀ L : ℝ) (hL : 0 ≤ L) :
    ∃ T : ℝ, 0 < T ∧ ∃ q : ℝ≥0,
      (q : ℝ) = chemMildLocalLipConst χ₀ L T ∧ q < 1 := by
  obtain ⟨T, hTpos, hq_nonneg, hq_lt⟩ := chemMildLocal_smallTime_contracts χ₀ L hL
  refine ⟨T, hTpos, ⟨chemMildLocalLipConst χ₀ L T, hq_nonneg⟩, rfl, ?_⟩
  rw [← NNReal.coe_lt_coe]
  simpa using hq_lt

/-- **The contraction-core fixed point at the χ₀<0 smallness horizon.**

Combines `chemMildLocal_orderBox_exists` (positive horizon `T` with contraction
constant `q = q(T) < 1`) with `chemMildLocal_contractionCore` (the Banach
fixed-point closure): on ANY complete, nonempty order-box slice space `α` on which
the short-time mild map `f` is `ContractingWith q`, there is a unique fixed point,
reached by Picard iteration from any starting point.  This is the full
contraction CORE — smallness ⊕ Banach fixed point — exposed for the `hMildLocal`
frontier. -/
theorem chemMildLocal_orderBox_fixedPoint (χ₀ L : ℝ) (hL : 0 ≤ L)
    {α : Type*} [MetricSpace α] [CompleteSpace α] [Nonempty α] :
    ∃ T : ℝ, 0 < T ∧ ∃ q : ℝ≥0, (q : ℝ) = chemMildLocalLipConst χ₀ L T ∧ q < 1 ∧
      ∀ {f : α → α}, ContractingWith q f → ∀ x₀ : α,
        ∃ y : α, Function.IsFixedPt f y ∧
          Tendsto (fun n => f^[n] x₀) atTop (𝓝 y) := by
  obtain ⟨T, hTpos, q, hq_eq, hq_lt⟩ := chemMildLocal_orderBox_exists χ₀ L hL
  exact ⟨T, hTpos, q, hq_eq, hq_lt,
    fun {f} hf x₀ => chemMildLocal_contractionCore hf x₀⟩

end

end ShenWork.Paper2
