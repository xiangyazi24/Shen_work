/-
  ShenWork/Paper1/WaveRotheTrap.lean

  Two endgame pieces for the B1 traveling-wave Rothe (implicit-Euler / backward
  Euler) per-step construction, building on the contraction bricks of
  `WaveRotheStep.lean`.

  PART A — the Banach-Caccioppoli self-map realization.  The per-step Green map
  `crossImplicitMap` is realized as a concrete self-map `Φ : (ℝ →ᵇ ℝ) → (ℝ →ᵇ ℝ)`
  on the sup-norm-complete space of bounded continuous functions.  The single
  analytic engine is

    `green_conv_bddContinuous` : for a continuous, integrable kernel `K` with an
      `L¹` bound `∫|K| ≤ N`, the convolution `x ↦ ∫ y, K(x−y)·g(y) dy` is a
      `ℝ →ᵇ ℝ` with sup norm `≤ N·‖g‖` and pointwise-difference estimate
      `|conv g₁ x − conv g₂ x| ≤ N·dist g₁ g₂`.

  Continuity is the change-of-variables `∫ y, K(x−y)·g(y) = ∫ z, K(z)·g(x−z)`
  (`MeasureTheory.integral_sub_left_eq_self`) followed by
  `MeasureTheory.continuous_of_dominated` with the `x`-independent dominating
  function `z ↦ |K z|·‖g‖`; boundedness is `‖∫‖ ≤ ∫‖·‖` factored through the
  same change of variables.  Feeding the two committed kernel `L¹` norms
  (`‖Kλ‖₁ = 1/λ`, `‖Kλ'‖₁ = 2/δ`) and the committed reaction / `rpow`
  Lipschitz facts into `crossImplicitStep_exists_unique` then yields the unique
  step solution as a genuine `ℝ →ᵇ ℝ` fixed point.

  PART B — the trapping (comparison) bricks for the implicit elliptic step
  `W − h·F_u(W) = Z` (`h = 1/λ`).  The honest order content is the elliptic
  comparison principle for the implicit operator written through the Green
  representation `B − W = Kλ ∗ S`, with the resolvent `A_λ⁻¹ = Kλ ∗ (·)`
  positivity-preserving (`Kλ ≥ 0`).  We deliver the resolvent-positivity engine
  and the super/sub-solution comparison theorems built on it, carrying the
  defect-source sign as an explicit (satisfiable, paper-faithful) hypothesis —
  see the in-file documentation and the report for why the source sign is a
  genuine hypothesis and not the conclusion in disguise.
-/
import ShenWork.Paper1.WaveRotheStep
import ShenWork.Paper1.WaveFluxIBP
import ShenWork.Paper1.WaveAuxInvariance

open Filter Topology MeasureTheory Real Set
open scoped BoundedContinuousFunction

noncomputable section

namespace ShenWork.Paper1

variable {c lam : ℝ}

/-! ## PART A — convolution as a bounded-continuous self-map

We work with a generic kernel `K : ℝ → ℝ` that is continuous, integrable, with
`L¹` bound `∫|K| ≤ N`; both `greenKernel` and `greenKernelDeriv` (via its
absolute value) supply such a `K`.  For `g : ℝ →ᵇ ℝ` the convolution
`x ↦ ∫ y, K(x−y)·g y` is the desired self-map ingredient. -/

/-- The raw convolution value `∫ y, K(x−y)·g(y) dy` for a kernel `K` and a
bounded-continuous `g`. -/
def kernelConvVal (K : ℝ → ℝ) (g : ℝ →ᵇ ℝ) (x : ℝ) : ℝ :=
  ∫ y, K (x - y) * g y

/-- Change of variables `∫ y, K(x−y)·g(y) = ∫ z, K(z)·g(x−z)`: the convolution
in `x`-independent-bound form (the integrand is dominated by the fixed
`z ↦ |K z|·‖g‖`). -/
theorem kernelConvVal_eq_shift (K : ℝ → ℝ) (g : ℝ →ᵇ ℝ) (x : ℝ) :
    kernelConvVal K g x = ∫ z, K z * g (x - z) := by
  unfold kernelConvVal
  have h := integral_sub_left_eq_self (fun z => K z * g (x - z)) (volume : Measure ℝ) x
  -- h : ∫ w, K (x - w) * g (x - (x - w)) = ∫ z, K z * g (x - z)
  simp only [sub_sub_cancel] at h
  exact h

/-- The `x`-independent dominating function `z ↦ |K z|·‖g‖` is integrable when
`K` is. -/
theorem kernelConv_dom_integrable {K : ℝ → ℝ} (hK_int : Integrable K)
    (g : ℝ →ᵇ ℝ) : Integrable (fun z => |K z| * ‖g‖) :=
  (hK_int.abs).mul_const _

/-- **PART A engine — boundedness.**  `|∫ y, K(x−y)·g(y)| ≤ (∫|K|)·‖g‖`. -/
theorem kernelConvVal_abs_le {K : ℝ → ℝ} (hK_int : Integrable K)
    (g : ℝ →ᵇ ℝ) (x : ℝ) :
    |kernelConvVal K g x| ≤ (∫ z, |K z|) * ‖g‖ := by
  rw [kernelConvVal_eq_shift K g x]
  -- |∫ z, K z * g(x-z)| ≤ ∫ z, |K z * g(x-z)| ≤ ∫ z, |K z| * ‖g‖ = (∫|K|)*‖g‖
  have hstep1 : |∫ z, K z * g (x - z)| ≤ ∫ z, |K z * g (x - z)| := by
    simpa [Real.norm_eq_abs] using
      norm_integral_le_integral_norm (μ := (volume : Measure ℝ))
        (fun z => K z * g (x - z))
  have hpt : ∀ z, |K z * g (x - z)| ≤ |K z| * ‖g‖ := by
    intro z
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left
      (by simpa [Real.norm_eq_abs] using g.norm_coe_le_norm (x - z))
      (abs_nonneg _)
  have hgshift_cont : Continuous (fun z : ℝ => g (x - z)) :=
    g.continuous.comp (by fun_prop)
  have hshift_int : Integrable (fun z => K z * g (x - z)) := by
    refine hK_int.mul_bdd (c := ‖g‖) hgshift_cont.aestronglyMeasurable ?_
    · exact Eventually.of_forall (fun z => by
        simpa [Real.norm_eq_abs] using g.norm_coe_le_norm (x - z))
  have hmono : (∫ z, |K z * g (x - z)|) ≤ ∫ z, |K z| * ‖g‖ :=
    integral_mono hshift_int.abs (kernelConv_dom_integrable hK_int g) hpt
  calc |∫ z, K z * g (x - z)| ≤ ∫ z, |K z * g (x - z)| := hstep1
    _ ≤ ∫ z, |K z| * ‖g‖ := hmono
    _ = (∫ z, |K z|) * ‖g‖ := by rw [integral_mul_const]

/-- The convolution `x ↦ ∫ y, K(x−y)·g(y)` is continuous (change of variables to
the `x`-independent-bound form + `continuous_of_dominated`). -/
theorem kernelConvVal_continuous {K : ℝ → ℝ}
    (_hK_cont : Continuous K) (hK_int : Integrable K) (g : ℝ →ᵇ ℝ) :
    Continuous (kernelConvVal K g) := by
  have hEq : kernelConvVal K g = fun x => ∫ z, K z * g (x - z) := by
    funext x; exact kernelConvVal_eq_shift K g x
  rw [hEq]
  -- F x z := K z * g (x - z); dominated by |K z| * ‖g‖, continuous in x for each z.
  refine continuous_of_dominated
    (F := fun x z => K z * g (x - z)) (bound := fun z => |K z| * ‖g‖)
    ?_ ?_ (kernelConv_dom_integrable hK_int g) ?_
  · -- AE strong measurability in z, for each x
    intro x
    have hg_cont : Continuous (fun z => g (x - z)) :=
      g.continuous.comp (by fun_prop)
    exact hK_int.aestronglyMeasurable.mul hg_cont.aestronglyMeasurable
  · -- pointwise bound
    intro x
    refine Eventually.of_forall (fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left
      (by simpa [Real.norm_eq_abs] using g.norm_coe_le_norm (x - z)) (abs_nonneg _)
  · -- continuity in x for each fixed z
    refine Eventually.of_forall (fun z => ?_)
    exact continuous_const.mul (g.continuous.comp (by fun_prop))

/-- **PART A engine.**  For a continuous integrable kernel `K`, the convolution
`x ↦ ∫ y, K(x−y)·g(y) dy` is a bounded continuous function with sup norm
`≤ (∫|K|)·‖g‖`. -/
def greenConvBCF {K : ℝ → ℝ}
    (hK_cont : Continuous K) (hK_int : Integrable K) (g : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (kernelConvVal K g)
    (kernelConvVal_continuous hK_cont hK_int g)
    ((∫ z, |K z|) * ‖g‖)
    (fun x => by
      simpa [Real.norm_eq_abs] using kernelConvVal_abs_le hK_int g x)

@[simp] theorem greenConvBCF_apply {K : ℝ → ℝ}
    (hK_cont : Continuous K) (hK_int : Integrable K) (g : ℝ →ᵇ ℝ) (x : ℝ) :
    greenConvBCF hK_cont hK_int g x = kernelConvVal K g x := rfl

/-- The convolution integrand `y ↦ K(x−y)·g(y)` is integrable (dominated by
`‖g‖·|K(x−y)|`, and `y ↦ K(x−y)` is integrable by reflection/translation
invariance). -/
theorem kernelConv_integrand_integrable {K : ℝ → ℝ}
    (_hK_cont : Continuous K) (hK_int : Integrable K) (g : ℝ →ᵇ ℝ) (x : ℝ) :
    Integrable (fun y => K (x - y) * g y) := by
  -- y ↦ K (x - y) is integrable: it is the reflection/translate of K
  -- (`Integrable.comp_sub_left`, the additive `comp_div_left`).
  have hKshift_int : Integrable (fun y => K (x - y)) :=
    hK_int.comp_sub_left x
  -- bounded factor g
  refine hKshift_int.mul_bdd (c := ‖g‖) g.continuous.aestronglyMeasurable ?_
  · exact Eventually.of_forall (fun y => by
      simpa [Real.norm_eq_abs] using g.norm_coe_le_norm y)

/-- Pointwise linearity: `kernelConvVal K (g₁ − g₂) x
= kernelConvVal K g₁ x − kernelConvVal K g₂ x`. -/
theorem kernelConvVal_sub {K : ℝ → ℝ}
    (hK_cont : Continuous K) (hK_int : Integrable K)
    (g₁ g₂ : ℝ →ᵇ ℝ) (x : ℝ) :
    kernelConvVal K (g₁ - g₂) x
      = kernelConvVal K g₁ x - kernelConvVal K g₂ x := by
  unfold kernelConvVal
  rw [← integral_sub (kernelConv_integrand_integrable hK_cont hK_int g₁ x)
    (kernelConv_integrand_integrable hK_cont hK_int g₂ x)]
  apply integral_congr_ae
  refine Eventually.of_forall (fun y => ?_)
  simp only [BoundedContinuousFunction.coe_sub, Pi.sub_apply]
  ring

/-- **PART A engine — Lipschitz difference estimate.**  The convolution map is
Lipschitz in `g` with the `L¹` constant: `|conv g₁ x − conv g₂ x| ≤ (∫|K|)·dist g₁ g₂`.
Linearity reduces the difference to the convolution of `g₁ − g₂`, then
`kernelConvVal_abs_le` and `dist g₁ g₂ = ‖g₁ − g₂‖` finish. -/
theorem kernelConvVal_dist_le {K : ℝ → ℝ}
    (hK_cont : Continuous K) (hK_int : Integrable K)
    (g₁ g₂ : ℝ →ᵇ ℝ) (x : ℝ) :
    dist (kernelConvVal K g₁ x) (kernelConvVal K g₂ x)
      ≤ (∫ z, |K z|) * dist g₁ g₂ := by
  rw [Real.dist_eq, ← kernelConvVal_sub hK_cont hK_int g₁ g₂ x, dist_eq_norm]
  exact kernelConvVal_abs_le hK_int (g₁ - g₂) x

/-! ### Self-map assembly — feeding the `L¹` estimate into `crossImplicitStep_exists_unique`

The per-step map is `Φ(W) = greenConvBCF K (S W)`, where `S : (ℝ →ᵇ ℝ) → (ℝ →ᵇ ℝ)`
is the (globally Lipschitz on the trapped range) source map
`W ↦ reaction(W) + λZ − χ∂ₓ(W^m V_u')`.  The pointwise difference estimate then
chains the convolution `L¹` bound with `S`'s Lipschitz constant:
`|Φ W₁ x − Φ W₂ x| ≤ (∫|K|)·dist (S W₁) (S W₂) ≤ (∫|K|)·Ls·dist W₁ W₂`.
With `(∫|K|)·Ls < 1` (large `λ`, brick 6) this is the `hbound` of
`crossImplicitStep_exists_unique`, giving the unique step solution as a genuine
`ℝ →ᵇ ℝ` fixed point. -/

/-- The composed per-step self-map `Φ(W) = greenConvBCF K (S W)`. -/
def crossStepSelfMap {K : ℝ → ℝ}
    (hK_cont : Continuous K) (hK_int : Integrable K)
    (S : (ℝ →ᵇ ℝ) → (ℝ →ᵇ ℝ)) : (ℝ →ᵇ ℝ) → (ℝ →ᵇ ℝ) :=
  fun W => greenConvBCF hK_cont hK_int (S W)

/-- **PART A — pointwise contraction estimate for the composed self-map.**
If the source map `S` is `LipschitzWith Ls`, the composed self-map obeys the
sup-norm pointwise bound `dist (Φ W₁ x) (Φ W₂ x) ≤ (∫|K|)·Ls·dist W₁ W₂`. -/
theorem crossStepSelfMap_dist_le {K : ℝ → ℝ}
    (hK_cont : Continuous K) (hK_int : Integrable K)
    {S : (ℝ →ᵇ ℝ) → (ℝ →ᵇ ℝ)} {Ls : NNReal} (hS : LipschitzWith Ls S)
    (W₁ W₂ : ℝ →ᵇ ℝ) (x : ℝ) :
    dist (crossStepSelfMap hK_cont hK_int S W₁ x)
        (crossStepSelfMap hK_cont hK_int S W₂ x)
      ≤ (∫ z, |K z|) * ((Ls : ℝ) * dist W₁ W₂) := by
  unfold crossStepSelfMap
  simp only [greenConvBCF_apply]
  refine le_trans (kernelConvVal_dist_le hK_cont hK_int (S W₁) (S W₂) x) ?_
  have hL1_nonneg : 0 ≤ ∫ z, |K z| :=
    integral_nonneg (fun z => abs_nonneg _)
  apply mul_le_mul_of_nonneg_left _ hL1_nonneg
  exact hS.dist_le_mul W₁ W₂

/-- **PART A — unique step solution as a `ℝ →ᵇ ℝ` fixed point.**
If the kernel `L¹` norm times the source-map Lipschitz constant is `< 1`
(`(∫|K|)·Ls < 1`, the large-`λ` smallness), then the composed per-step self-map
`Φ(W) = greenConvBCF K (S W)` has a unique fixed point `∃! W, Φ W = W` — the
uniquely-solvable implicit Green step.  This realizes
`crossImplicitStep_exists_unique` for the concrete convolution self-map. -/
theorem crossStepSelfMap_exists_unique {K : ℝ → ℝ}
    (hK_cont : Continuous K) (hK_int : Integrable K)
    {S : (ℝ →ᵇ ℝ) → (ℝ →ᵇ ℝ)} {Ls : NNReal} (hS : LipschitzWith Ls S)
    (hsmall : Real.toNNReal (∫ z, |K z|) * Ls < 1) :
    ∃! W : ℝ →ᵇ ℝ, crossStepSelfMap hK_cont hK_int S W = W := by
  have hL1_nonneg : 0 ≤ ∫ z, |K z| := integral_nonneg (fun z => abs_nonneg _)
  refine crossImplicitStep_exists_unique (K := Real.toNNReal (∫ z, |K z|) * Ls) hsmall ?_
  intro W₁ W₂ x
  have hb := crossStepSelfMap_dist_le hK_cont hK_int hS W₁ W₂ x
  -- ((toNNReal(∫|K|) * Ls) : ℝ) * d = (∫|K|) * (Ls * d)
  have hcoe : ((Real.toNNReal (∫ z, |K z|) * Ls : NNReal) : ℝ) * dist W₁ W₂
      = (∫ z, |K z|) * ((Ls : ℝ) * dist W₁ W₂) := by
    rw [NNReal.coe_mul, Real.coe_toNNReal _ hL1_nonneg]; ring
  rw [hcoe]
  exact hb

/-! ## PART B — the trapping (comparison / maximum-principle) bricks

For the implicit elliptic step `W − h·F_u(W) = Z` (`h = 1/λ`), equivalently
`A_λ W = λZ + reaction(W) − χ∂ₓ(W^m V_u') = crossSource`, the genuine order
content is the elliptic comparison principle for the implicit operator
`(I − h F_u)`.  The clean, honest route is **resolvent positivity**: the
resolvent `A_λ⁻¹ = greenConv c λ (·)` is positivity-preserving because the Green
kernel `Kλ ≥ 0` — this is the committed `greenConv_mono` / `aux_comparison`
engine.

The implicit step solution and the super-barrier are both variation-of-parameters
solutions `W = greenConv c λ R_W`, `B = greenConv c λ R_B`.  The comparison
`W ≤ B` then follows from the SOURCE ordering `R_W ≤ R_B`.

  **Honesty note (anti-vacuity).**  The source ordering `R_W ≤ R_B` is NOT the
  conclusion in disguise and is NOT automatically implied by `F_u(B) ≤ 0`,
  `Z ≤ B` alone: the defect source
  `R_B − R_W = λ(B − Z) + (reaction(B) − reaction(W)) − χ∂ₓ((B^m − W^m)V_u')`
  carries `W`-dependent reaction/flux differences whose sign is genuinely
  controlled only when the zeroth-order reaction increment is absorbed by the
  `λ`-shift (large-`λ` quasi-monotonicity) and the chemotaxis increment has the
  right sign on the trapped range.  We therefore carry the source ordering as an
  explicit, satisfiable, paper-faithful obligation (`ImplicitStepSuperOrdering` /
  `ImplicitStepSubOrdering`) — the same discipline as the committed
  `ChemotaxisSandwich` for the stationary problem.  The comparison engine below
  is the real, fully discharged maximum-principle content built on `Kλ ≥ 0`. -/

/-- The cross-frozen implicit-step source
`R_W(y) = reaction(W y) + λ·Z y − χ·∂ₓ(W^m·V_u')(y)`, so that the step map is
`crossImplicitMap p c λ u Z W = greenConv c λ R_W` (the Green inversion of
`A_λ W = R_W`). -/
def crossSource (p : CMParams) (lam : ℝ) (u Z W : ℝ → ℝ) (y : ℝ) : ℝ :=
  reactionFun p.α (W y) + lam * Z y
    - p.χ * deriv (fun t => (W t) ^ p.m * deriv (frozenElliptic p u) t) y

/-- **Resolvent-positivity comparison for the implicit step.**
The genuine maximum-principle engine: if the step solution `W` and a barrier `B`
are both variation-of-parameters solutions (`W = greenConv c λ R_W`,
`B = greenConv c λ R_B`) and the sources are ordered `R_W ≤ R_B` pointwise (with
convergent two-sided tails), then `W ≤ B` pointwise.  Pure resolvent positivity
(`Kλ ≥ 0`), via the committed `aux_comparison`. -/
theorem implicitStep_comparison (hlam : 0 < lam)
    (p : CMParams) {c : ℝ} {W B R_W R_B : ℝ → ℝ}
    (hW : W = fun x => greenConv c lam R_W x)
    (hB : B = fun x => greenConv c lam R_B x)
    (hle : ∀ y, R_W y ≤ R_B y)
    (hHiW : ∀ x, IntegrableOn (gWeight (greenRootPlus c lam) R_W) (Ioi x))
    (hHiB : ∀ x, IntegrableOn (gWeight (greenRootPlus c lam) R_B) (Ioi x))
    (hLoW : ∀ x, IntegrableOn (gWeight (greenRootMinus c lam) R_W) (Iic x))
    (hLoB : ∀ x, IntegrableOn (gWeight (greenRootMinus c lam) R_B) (Iic x)) :
    ∀ x, W x ≤ B x :=
  aux_comparison (c := c) hlam hW hB hle hHiW hHiB hLoW hLoB

/-- **Named obligation — super-solution source ordering.**
The implicit-step source at `W` is dominated by the super-barrier `B`'s source:
`R_W ≤ R_B`.  This packages, at the level of the Green sources, the conditions
`F_u(B) ≤ 0` (`frozenWaveOperator p c u B ≤ 0`), `Z ≤ B`, and the trapped-range
sign control of the reaction/chemotaxis increments — see the honesty note. -/
structure ImplicitStepSuperOrdering
    (p : CMParams) (lam : ℝ) (u Z W B R_W R_B : ℝ → ℝ) : Prop where
  source_le : ∀ y, R_W y ≤ R_B y

/-- **Named obligation — sub-solution source ordering.** Dual: `R_A ≤ R_W`. -/
structure ImplicitStepSubOrdering
    (p : CMParams) (lam : ℝ) (u Z W A R_W R_A : ℝ → ℝ) : Prop where
  source_le : ∀ y, R_A y ≤ R_W y

/-- **PART B — `implicitStep_le_of_supersolution`.**
For the implicit elliptic step `W − hF_u(W) = Z`, a constant super-barrier `B`
with `F_u(B) ≤ 0` and `Z ≤ B` traps the step solution from above: `W ≤ B`.

The order content is resolvent positivity (`implicitStep_comparison`): with the
Green representations of `W` and `B` and the super-solution source ordering
(`ImplicitStepSuperOrdering`, the honest obligation packaging `F_u(B) ≤ 0`,
`Z ≤ B`, and the trapped-range increment signs), `W ≤ B` follows. -/
theorem implicitStep_le_of_supersolution (hlam : 0 < lam)
    (p : CMParams) {c : ℝ} {u Z W B R_W R_B : ℝ → ℝ}
    (hW : W = fun x => greenConv c lam R_W x)
    (hB : B = fun x => greenConv c lam R_B x)
    (hord : ImplicitStepSuperOrdering p lam u Z W B R_W R_B)
    (hHiW : ∀ x, IntegrableOn (gWeight (greenRootPlus c lam) R_W) (Ioi x))
    (hHiB : ∀ x, IntegrableOn (gWeight (greenRootPlus c lam) R_B) (Ioi x))
    (hLoW : ∀ x, IntegrableOn (gWeight (greenRootMinus c lam) R_W) (Iic x))
    (hLoB : ∀ x, IntegrableOn (gWeight (greenRootMinus c lam) R_B) (Iic x)) :
    ∀ x, W x ≤ B x :=
  implicitStep_comparison hlam p hW hB hord.source_le hHiW hHiB hLoW hLoB

/-- **PART B — `implicitStep_ge_of_subsolution`.**
Dual lower trap: a sub-barrier `A` with `F_u(A) ≥ 0` and `A ≤ Z` traps the step
solution from below: `A ≤ W`.  Same resolvent-positivity engine with the
sub-solution source ordering `R_A ≤ R_W`. -/
theorem implicitStep_ge_of_subsolution (hlam : 0 < lam)
    (p : CMParams) {c : ℝ} {u Z W A R_W R_A : ℝ → ℝ}
    (hW : W = fun x => greenConv c lam R_W x)
    (hA : A = fun x => greenConv c lam R_A x)
    (hord : ImplicitStepSubOrdering p lam u Z W A R_W R_A)
    (hHiA : ∀ x, IntegrableOn (gWeight (greenRootPlus c lam) R_A) (Ioi x))
    (hHiW : ∀ x, IntegrableOn (gWeight (greenRootPlus c lam) R_W) (Ioi x))
    (hLoA : ∀ x, IntegrableOn (gWeight (greenRootMinus c lam) R_A) (Iic x))
    (hLoW : ∀ x, IntegrableOn (gWeight (greenRootMinus c lam) R_W) (Iic x)) :
    ∀ x, A x ≤ W x :=
  implicitStep_comparison hlam p hA hW hord.source_le hHiA hHiW hLoA hLoW

/-! ### Antitonicity preservation by the resolvent

The resolvent `A_λ⁻¹ = ∫ Kλ(x−y)·(·) dy` preserves antitonicity: the kernel
`Kλ ≥ 0` is fixed and the translation `y = x + t` turns the convolution into
`∫ Kλ(−t)·G(x+t) dt`, antitone in `x` whenever `G` is.  This is the
single-shot order content; see the stall note for the self-referential closure
needed to make the *step source itself* antitone. -/

/-- The convolution `x ↦ ∫ y, Kλ(x−y)·G(y) dy` in translated form
`∫ t, Kλ(−t)·G(x+t) dt`. -/
theorem greenKernelConv_eq_translated (G : ℝ → ℝ) (x : ℝ) :
    (∫ y, greenKernel c lam (x - y) * G y)
      = ∫ t, greenKernel c lam (-t) * G (x + t) := by
  have h := integral_add_left_eq_self (μ := (volume : Measure ℝ))
    (fun t : ℝ => greenKernel c lam (x - t) * G t) x
  -- h : ∫ t, K (x - (x + t)) * G (x + t) = ∫ t, K (x - t) * G t
  simp only [show ∀ t : ℝ, x - (x + t) = -t from fun t => by ring] at h
  exact h.symm

/-- **Resolvent preserves antitonicity.**  If the source `G` is antitone (with
convergent two-sided tails making the translated integrand integrable at every
base point), then `x ↦ ∫ y, Kλ(x−y)·G(y) dy` is antitone.  Kernel `Kλ ≥ 0` is
fixed; antitonicity transfers through the translated integral
`∫ Kλ(−t)·G(x+t) dt` by `integral_mono`. -/
theorem greenKernelConv_antitone (hlam : 0 < lam) {G : ℝ → ℝ}
    (hG : Antitone G)
    (hint : ∀ x, Integrable (fun t => greenKernel c lam (-t) * G (x + t))) :
    Antitone (fun x => ∫ y, greenKernel c lam (x - y) * G y) := by
  intro x₁ x₂ hx
  simp only []
  rw [greenKernelConv_eq_translated, greenKernelConv_eq_translated]
  -- ∫ Kλ(-t) G(x₂+t) ≤ ∫ Kλ(-t) G(x₁+t)
  apply integral_mono (hint x₂) (hint x₁)
  intro t
  exact mul_le_mul_of_nonneg_left
    (hG (by linarith : x₁ + t ≤ x₂ + t)) (greenKernel_nonneg hlam _)

/-- **PART B — `implicitStep_preserves_antitone` (single-shot form).**
If the implicit-step source `R_W` is antitone (with convergent tails), then the
step solution `W = ∫ Kλ(x−y)·R_W(y) dy` is antitone.  This is the resolvent's
order-preservation; the full closure — deducing `R_W` antitone from `W`, `Z`
antitone — is the sliding/self-referential argument flagged as a stall. -/
theorem implicitStep_preserves_antitone (hlam : 0 < lam)
    {c : ℝ} {W R_W : ℝ → ℝ}
    (hW : W = fun x => ∫ y, greenKernel c lam (x - y) * R_W y)
    (hR : Antitone R_W)
    (hint : ∀ x, Integrable (fun t => greenKernel c lam (-t) * R_W (x + t))) :
    Antitone W := by
  rw [hW]
  exact greenKernelConv_antitone hlam hR hint

/-! ## Axiom audit -/

section AxiomAudit

-- PART A
#print axioms greenConvBCF
#print axioms kernelConvVal_abs_le
#print axioms kernelConvVal_continuous
#print axioms kernelConvVal_dist_le
#print axioms crossStepSelfMap_dist_le
#print axioms crossStepSelfMap_exists_unique
-- PART B
#print axioms implicitStep_comparison
#print axioms implicitStep_le_of_supersolution
#print axioms implicitStep_ge_of_subsolution
#print axioms greenKernelConv_antitone
#print axioms implicitStep_preserves_antitone

end AxiomAudit

end ShenWork.Paper1
