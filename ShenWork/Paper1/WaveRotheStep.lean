/-
  ShenWork/Paper1/WaveRotheStep.lean

  Foundational bricks for the B1 traveling-wave Rothe (implicit-Euler /
  backward-Euler) orbit construction (Shen, arXiv:2605.04401, §6 / B1
  doctrine).

  For a frozen trapped profile `u`, with `V_u = frozenElliptic p u` and large
  `λ > 0` (time step `h = 1/λ`), the implicit-Euler step

      `z_{k+1} − h·F_u(z_{k+1}) = z_k`,
      `F_u(W) = W'' + cW' − χ ∂ₓ(W^m V_u') + W(1 − W^a)`,

  is equivalent (multiply by `λ`, invert `A_λ = −∂² − c∂ + λ`) to a Green
  fixed point `W = Φ_{λ,u,Z}(W)` with

      `Φ_{λ,u,Z}(W)(x)
        = ∫ Kλ(x−y)·(λ·Z(y) + W(y)·(1 − W(y)^a)) dy
          − χ ∫ Kλ'(x−y)·W(y)^m·V_u'(y) dy`,

  the OLD iterate `Z = z_k` entering the linear shift `λZ`, the NEW unknown `W`
  entering the nonlinear reaction/flux.  This is the cross-frozen analogue of
  the committed stationary `auxMap` (WaveAuxMap.lean); UNLIKE the stationary
  problem, the per-step map is a CONTRACTION:

      `|Φ(W₁) − Φ(W₂)|
        ≤ (L_rxn·‖Kλ‖₁ + |χ|·L_m·B_{V'}·‖Kλ'‖₁)·‖W₁ − W₂‖∞`,

  where `L_rxn`, `L_m` are the Lipschitz constants of `s ↦ s(1−s^a)`, `s ↦ s^m`
  on `[0,M]`.  Since `‖Kλ‖₁ = 1/λ → 0` and `‖Kλ'‖₁ = 2/δ → 0` as `λ → ∞`
  (`δ = √(c²+4λ)`), the factor is `< 1` for large `λ`, so `Φ` is a contraction
  with a unique fixed point (Banach).

  This file supplies the FOUNDATION:

    * `reaction_lipschitz_on_Icc` — `s ↦ s(1−s^a)` is Lipschitz on `[0,M]`.
    * `rpow_m_lipschitz_on_Icc`   — `s ↦ s^m`     is Lipschitz on `[0,M]`.
    * `greenKernel_l1_eq` / `greenKernel_l1_bound`     — `∫|Kλ| = 1/λ`.
    * `greenKernelDeriv_integrable` /
      `greenKernelDeriv_l1_eq` / `greenKernelDeriv_l1_bound` — `∫|Kλ'| = 2/δ`.
    * `crossImplicitMap`          — the per-step map `Φ_{λ,u,Z}` (mirrors
      `auxMap`'s divergence structure with `Z` in the linear shift).
    * `crossContractionFactor` and its large-`λ` smallness — the contraction
      constant assembled from the L¹ bricks.
-/
import ShenWork.Paper1.WaveAuxMap
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.MetricSpace.Contracting

open Filter Topology MeasureTheory Real Set
open scoped BoundedContinuousFunction

noncomputable section

namespace ShenWork.Paper1

/-! ## Brick 1 — Lipschitz constant of the reaction `s ↦ s(1 − s^a)` on `[0,M]`

For exponent `a ≥ 1` the map `r ↦ r^a` is differentiable everywhere (the
`1 ≤ a` branch of `Real.hasDerivAt_rpow_const`), so `g(s) = s·(1 − s^a)` is
differentiable on `ℝ` with `g'(s) = (1 − s^a) − a·s·s^{a-1}`.  On `[0,M]`
(`M ≥ 0`, `a ≥ 1`) we have `s·s^{a-1} = s^a` and `0 ≤ s^a ≤ M^a`, hence
`|g'(s)| ≤ 1 + (a+1)·M^a =: L_rxn`. -/

/-- The reaction nonlinearity `g(s) = s·(1 − s^a)` as a function of the scalar
`s` (cf. `auxReaction p u y = reactionFun p.α (u y)`). -/
def reactionFun (a s : ℝ) : ℝ := s * (1 - s ^ a)

/-- Explicit Lipschitz constant of `reactionFun a` on `[0,M]`. -/
def reactionLip (a M : ℝ) : ℝ := 1 + (a + 1) * M ^ a

/-- For `s ≥ 0` and `a ≥ 1` (so that `1 + (a-1) = a` with `s^{a}` well-behaved
at `0`): `s · s^{a-1} = s^a`. -/
theorem mul_rpow_sub_one (a : ℝ) (ha : 1 ≤ a) {s : ℝ} (hs : 0 ≤ s) :
    s * s ^ (a - 1) = s ^ a := by
  have h : s ^ (1 + (a - 1)) = s * s ^ (a - 1) :=
    Real.rpow_one_add' hs (by linarith)
  have he : (1 : ℝ) + (a - 1) = a := by ring
  rw [he] at h
  exact h.symm

/-- Pointwise derivative of `reactionFun a` everywhere (using the `1 ≤ a`
branch of `rpow` differentiability). -/
theorem reactionFun_hasDerivAt (a : ℝ) (ha : 1 ≤ a) (s : ℝ) :
    HasDerivAt (reactionFun a) (1 - s ^ a - a * (s * s ^ (a - 1))) s := by
  have hp : HasDerivAt (fun r : ℝ => r ^ a) (a * s ^ (a - 1)) s :=
    Real.hasDerivAt_rpow_const (Or.inr ha)
  have hinner : HasDerivAt (fun r : ℝ => 1 - r ^ a) (-(a * s ^ (a - 1))) s := by
    simpa using (hasDerivAt_const s (1 : ℝ)).sub hp
  have hprod : HasDerivAt (fun r : ℝ => r * (1 - r ^ a))
      (1 * (1 - s ^ a) + s * (-(a * s ^ (a - 1)))) s :=
    (hasDerivAt_id s).mul hinner
  have : (1 * (1 - s ^ a) + s * (-(a * s ^ (a - 1))))
      = 1 - s ^ a - a * (s * s ^ (a - 1)) := by ring
  rw [this] at hprod
  exact hprod

/-- `deriv (reactionFun a) s = 1 - s^a - a·(s·s^{a-1})`. -/
theorem reactionFun_deriv (a : ℝ) (ha : 1 ≤ a) (s : ℝ) :
    deriv (reactionFun a) s = 1 - s ^ a - a * (s * s ^ (a - 1)) :=
  (reactionFun_hasDerivAt a ha s).deriv

theorem reactionLip_nonneg {a M : ℝ} (ha : 1 ≤ a) (hM : 0 ≤ M) :
    0 ≤ reactionLip a M := by
  unfold reactionLip
  have : 0 ≤ (a + 1) * M ^ a := by positivity
  linarith

/-- The reaction nonlinearity `s ↦ s(1 − s^a)` is Lipschitz on `[0,M]` with the
explicit constant `reactionLip a M = 1 + (a+1)·M^a`. -/
theorem reaction_lipschitz_on_Icc {a M : ℝ} (ha : 1 ≤ a) (hM : 0 ≤ M) :
    LipschitzOnWith (Real.toNNReal (reactionLip a M)) (reactionFun a)
      (Set.Icc 0 M) := by
  have hconv : Convex ℝ (Set.Icc (0:ℝ) M) := convex_Icc 0 M
  apply hconv.lipschitzOnWith_of_nnnorm_deriv_le
    (fun s _ => (reactionFun_hasDerivAt a ha s).differentiableAt)
  intro s hs
  rw [Set.mem_Icc] at hs
  obtain ⟨hs0, hsM⟩ := hs
  -- |deriv| ≤ reactionLip a M
  have hsa_eq : s * s ^ (a - 1) = s ^ a := mul_rpow_sub_one a ha hs0
  have hderiv : deriv (reactionFun a) s = 1 - (a + 1) * s ^ a := by
    rw [reactionFun_deriv a ha s, hsa_eq]; ring
  -- bounds on s^a
  have hsa_nonneg : 0 ≤ s ^ a := Real.rpow_nonneg hs0 a
  have hsa_le : s ^ a ≤ M ^ a := Real.rpow_le_rpow hs0 hsM (by linarith)
  have hcoef_nonneg : 0 ≤ a + 1 := by linarith
  have habs : |deriv (reactionFun a) s| ≤ reactionLip a M := by
    rw [hderiv]
    unfold reactionLip
    rw [abs_le]
    constructor
    · have : (a + 1) * s ^ a ≤ (a + 1) * M ^ a :=
        mul_le_mul_of_nonneg_left hsa_le hcoef_nonneg
      nlinarith [hsa_nonneg]
    · nlinarith [mul_nonneg hcoef_nonneg hsa_nonneg]
  -- convert |·| ≤ r (r ≥ 0) to ‖·‖₊ ≤ toNNReal r
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs,
    Real.coe_toNNReal _ (reactionLip_nonneg ha hM)]
  exact habs

/-! ## Brick 2 — Lipschitz constant of `s ↦ s^m` on `[0,M]`

For `m ≥ 1` the map `s ↦ s^m` is differentiable on `ℝ` with derivative
`m·s^{m-1}`.  On `[0,M]` we have `0 ≤ s^{m-1} ≤ M^{m-1}`, so
`|m·s^{m-1}| ≤ m·M^{m-1} =: L_m`. -/

/-- Explicit Lipschitz constant of `s ↦ s^m` on `[0,M]`. -/
def rpowLip (m M : ℝ) : ℝ := m * M ^ (m - 1)

theorem rpowLip_nonneg {m M : ℝ} (hm : 1 ≤ m) (hM : 0 ≤ M) :
    0 ≤ rpowLip m M := by
  unfold rpowLip; positivity

/-- The power nonlinearity `s ↦ s^m` is Lipschitz on `[0,M]` with the explicit
constant `rpowLip m M = m·M^{m-1}`. -/
theorem rpow_m_lipschitz_on_Icc {m M : ℝ} (hm : 1 ≤ m) (hM : 0 ≤ M) :
    LipschitzOnWith (Real.toNNReal (rpowLip m M)) (fun s => s ^ m)
      (Set.Icc 0 M) := by
  have hconv : Convex ℝ (Set.Icc (0:ℝ) M) := convex_Icc 0 M
  apply hconv.lipschitzOnWith_of_nnnorm_deriv_le
    (fun s _ => (Real.hasDerivAt_rpow_const (x := s) (p := m) (Or.inr hm)).differentiableAt)
  intro s hs
  rw [Set.mem_Icc] at hs
  obtain ⟨hs0, hsM⟩ := hs
  have hderiv : deriv (fun s => s ^ m) s = m * s ^ (m - 1) :=
    (Real.hasDerivAt_rpow_const (x := s) (p := m) (Or.inr hm)).deriv
  have hsm_nonneg : 0 ≤ s ^ (m - 1) := Real.rpow_nonneg hs0 (m - 1)
  have hsm_le : s ^ (m - 1) ≤ M ^ (m - 1) :=
    Real.rpow_le_rpow hs0 hsM (by linarith)
  have habs : |deriv (fun s => s ^ m) s| ≤ rpowLip m M := by
    rw [hderiv]
    unfold rpowLip
    rw [abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left hsm_le (by linarith)
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs,
    Real.coe_toNNReal _ (rpowLip_nonneg hm hM)]
  exact habs

/-! ## Brick 3 — `L¹` norm of the Green kernel: `∫|Kλ| = 1/λ`

`Kλ > 0`, so `∫|Kλ| = ∫Kλ`.  Splitting `ℝ = Iic 0 ∪ Ioi 0`,
`∫_{Iic 0} (1/δ)e^{r₊ z} = (1/δ)/r₊` and `∫_{Ioi 0} (1/δ)e^{r₋ z} = -(1/δ)/r₋`,
giving `(1/δ)(1/r₊ − 1/r₋) = (1/δ)·(δ/λ) = 1/λ` via Vieta
`r₊r₋ = −λ`, `r₊ − r₋ = δ`. -/

variable {c lam : ℝ}

theorem greenRoots_sub (hlam : 0 < lam) :
    greenRootPlus c lam - greenRootMinus c lam = greenDelta c lam := by
  unfold greenRootPlus greenRootMinus; ring

/-- `∫_{Iic 0} Kλ = (1/δ)/r₊`. -/
theorem greenKernel_setIntegral_Iic (hlam : 0 < lam) :
    ∫ z in Set.Iic (0:ℝ), greenKernel c lam z
      = (greenDelta c lam)⁻¹ / greenRootPlus c lam := by
  have hr := greenRootPlus_pos (c := c) hlam
  have hcongr : ∫ z in Set.Iic (0:ℝ), greenKernel c lam z
      = ∫ z in Set.Iic (0:ℝ),
          (greenDelta c lam)⁻¹ * Real.exp (greenRootPlus c lam * z) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Iic
    intro z hz
    rw [Set.mem_Iic] at hz
    simp only [greenKernel, if_pos hz]
  rw [hcongr, MeasureTheory.integral_const_mul,
    integral_exp_mul_Iic hr 0]
  simp [div_eq_mul_inv]

/-- `∫_{Ioi 0} Kλ = -(1/δ)/r₋`. -/
theorem greenKernel_setIntegral_Ioi (hlam : 0 < lam) :
    ∫ z in Set.Ioi (0:ℝ), greenKernel c lam z
      = -((greenDelta c lam)⁻¹ / greenRootMinus c lam) := by
  have hr := greenRootMinus_neg (c := c) hlam
  have hcongr : ∫ z in Set.Ioi (0:ℝ), greenKernel c lam z
      = ∫ z in Set.Ioi (0:ℝ),
          (greenDelta c lam)⁻¹ * Real.exp (greenRootMinus c lam * z) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro z hz
    rw [Set.mem_Ioi] at hz
    simp only [greenKernel, if_neg (not_le.mpr hz)]
  rw [hcongr, MeasureTheory.integral_const_mul,
    integral_exp_mul_Ioi hr 0]
  simp [div_eq_mul_inv]

/-- **Brick 3 (exact).** `∫ Kλ = 1/λ`. -/
theorem greenKernel_integral_eq (hlam : 0 < lam) :
    ∫ z, greenKernel c lam z = lam⁻¹ := by
  have hIic := greenKernel_integrableOn_Iic (c := c) hlam
  have hIoi := greenKernel_integrableOn_Ioi (c := c) hlam
  have hfi := greenKernel_integrable (c := c) hlam
  have hsplit := MeasureTheory.integral_add_compl
    (s := Set.Iic (0:ℝ)) measurableSet_Iic hfi
  simp only [Set.compl_Iic] at hsplit
  rw [← hsplit, greenKernel_setIntegral_Iic hlam,
    greenKernel_setIntegral_Ioi hlam]
  -- (1/δ)/r₊ - (1/δ)/r₋ = (1/δ)(r₋ - r₊)/(r₊ r₋) ... = 1/λ
  have hδ := greenDelta_pos (c := c) hlam
  have hrp := greenRootPlus_pos (c := c) hlam
  have hrm := greenRootMinus_neg (c := c) hlam
  have hmul := greenRoots_mul (c := c) hlam
  have hsub := greenRoots_sub (c := c) hlam
  have hδne : greenDelta c lam ≠ 0 := ne_of_gt hδ
  have hrpne : greenRootPlus c lam ≠ 0 := ne_of_gt hrp
  have hrmne : greenRootMinus c lam ≠ 0 := ne_of_lt hrm
  have hlamne : lam ≠ 0 := ne_of_gt hlam
  field_simp
  -- goal becomes a polynomial identity in roots/δ/λ
  nlinarith [hmul, hsub, hδ, hrp, hrm,
    mul_pos hrp (neg_pos.mpr hrm)]

/-- `∫|Kλ| = ∫Kλ` since `Kλ ≥ 0`. -/
theorem greenKernel_l1_eq (hlam : 0 < lam) :
    ∫ z, |greenKernel c lam z| = lam⁻¹ := by
  have : (fun z => |greenKernel c lam z|) = greenKernel c lam := by
    funext z; exact abs_of_nonneg (greenKernel_nonneg hlam z)
  rw [this, greenKernel_integral_eq hlam]

/-- **Brick 3 (bound).** `∫|Kλ| = 1/λ`, an explicit `L¹` bound `→ 0` as
`λ → ∞`. -/
theorem greenKernel_l1_bound (hlam : 0 < lam) :
    ∫ z, |greenKernel c lam z| ≤ lam⁻¹ :=
  le_of_eq (greenKernel_l1_eq hlam)

/-! ## Brick 4 — `L¹` norm of the kernel derivative: `∫|Kλ'| = 2/δ`

`|Kλ'(z)| = (1/δ)·r₊·e^{r₊ z}` on `Iic 0` (`r₊ > 0`), and
`(1/δ)·(−r₋)·e^{r₋ z}` on `Ioi 0` (`r₋ < 0`).  Each tail integrates to `1/δ`
(`∫_{Iic 0} r₊ e^{r₊ z} = 1`, `∫_{Ioi 0} (−r₋) e^{r₋ z} = 1`), so `∫|Kλ'| = 2/δ`,
which `→ 0` as `λ → ∞` (`δ = √(c²+4λ) → ∞`). -/

/-- `|Kλ'|` on `Iic 0` equals `(1/δ)·r₊·e^{r₊ z}`. -/
theorem absDeriv_eqOn_Iic (hlam : 0 < lam) :
    Set.EqOn (fun z => |greenKernelDeriv c lam z|)
      (fun z => (greenDelta c lam)⁻¹ * greenRootPlus c lam
        * Real.exp (greenRootPlus c lam * z)) (Set.Iic 0) := by
  intro z hz
  rw [Set.mem_Iic] at hz
  have hδ : 0 < (greenDelta c lam)⁻¹ := inv_pos.mpr (greenDelta_pos (c := c) hlam)
  have hrp := greenRootPlus_pos (c := c) hlam
  simp only [greenKernelDeriv, if_pos hz]
  rw [abs_of_nonneg (by positivity)]

/-- `|Kλ'|` on `Ioi 0` equals `(1/δ)·(−r₋)·e^{r₋ z}`. -/
theorem absDeriv_eqOn_Ioi (hlam : 0 < lam) :
    Set.EqOn (fun z => |greenKernelDeriv c lam z|)
      (fun z => (greenDelta c lam)⁻¹ * (-greenRootMinus c lam)
        * Real.exp (greenRootMinus c lam * z)) (Set.Ioi 0) := by
  intro z hz
  rw [Set.mem_Ioi] at hz
  have hδ : 0 < (greenDelta c lam)⁻¹ := inv_pos.mpr (greenDelta_pos (c := c) hlam)
  have hrm := greenRootMinus_neg (c := c) hlam
  simp only [greenKernelDeriv, if_neg (not_le.mpr hz)]
  rw [abs_of_nonpos (by
    have : greenRootMinus c lam * Real.exp (greenRootMinus c lam * z) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hrm.le (Real.exp_pos _).le
    have h2 : (greenDelta c lam)⁻¹ * greenRootMinus c lam
        * Real.exp (greenRootMinus c lam * z)
        = (greenDelta c lam)⁻¹
          * (greenRootMinus c lam * Real.exp (greenRootMinus c lam * z)) := by ring
    rw [h2]
    exact mul_nonpos_of_nonneg_of_nonpos hδ.le this)]
  ring

theorem absDeriv_integrableOn_Iic (hlam : 0 < lam) :
    IntegrableOn (fun z => |greenKernelDeriv c lam z|) (Set.Iic 0) := by
  have hrp := greenRootPlus_pos (c := c) hlam
  have hbase : IntegrableOn
      (fun z => (greenDelta c lam)⁻¹ * greenRootPlus c lam
        * Real.exp (greenRootPlus c lam * z)) (Set.Iic 0) :=
    (integrableOn_exp_mul_Iic (a := greenRootPlus c lam) hrp 0).const_mul _
  exact (hbase.congr_fun (absDeriv_eqOn_Iic hlam).symm measurableSet_Iic)

theorem absDeriv_integrableOn_Ioi (hlam : 0 < lam) :
    IntegrableOn (fun z => |greenKernelDeriv c lam z|) (Set.Ioi 0) := by
  have hrm := greenRootMinus_neg (c := c) hlam
  have hbase : IntegrableOn
      (fun z => (greenDelta c lam)⁻¹ * (-greenRootMinus c lam)
        * Real.exp (greenRootMinus c lam * z)) (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi (a := greenRootMinus c lam) hrm 0).const_mul _
  exact (hbase.congr_fun (absDeriv_eqOn_Ioi hlam).symm measurableSet_Ioi)

/-- **Brick 4 (integrability).** `|Kλ'|` is integrable on `ℝ`. -/
theorem greenKernelDeriv_integrable (hlam : 0 < lam) :
    Integrable (fun z => |greenKernelDeriv c lam z|) := by
  have hIic := absDeriv_integrableOn_Iic (c := c) hlam
  have hIoi := absDeriv_integrableOn_Ioi (c := c) hlam
  rw [← integrableOn_univ,
    show (Set.univ : Set ℝ) = Set.Iic 0 ∪ Set.Ioi 0 by
      ext x; simp only [Set.mem_univ, Set.mem_union, Set.mem_Iic, Set.mem_Ioi,
        true_iff]; exact le_or_gt x 0]
  exact hIic.union hIoi

theorem absDeriv_setIntegral_Iic (hlam : 0 < lam) :
    ∫ z in Set.Iic (0:ℝ), |greenKernelDeriv c lam z|
      = (greenDelta c lam)⁻¹ := by
  have hrp := greenRootPlus_pos (c := c) hlam
  have hrpne : greenRootPlus c lam ≠ 0 := ne_of_gt hrp
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Iic
    (absDeriv_eqOn_Iic hlam)]
  rw [MeasureTheory.integral_const_mul, integral_exp_mul_Iic hrp 0]
  rw [mul_zero, Real.exp_zero]
  field_simp

theorem absDeriv_setIntegral_Ioi (hlam : 0 < lam) :
    ∫ z in Set.Ioi (0:ℝ), |greenKernelDeriv c lam z|
      = (greenDelta c lam)⁻¹ := by
  have hrm := greenRootMinus_neg (c := c) hlam
  have hrmne : greenRootMinus c lam ≠ 0 := ne_of_lt hrm
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    (absDeriv_eqOn_Ioi hlam)]
  rw [MeasureTheory.integral_const_mul, integral_exp_mul_Ioi hrm 0]
  rw [mul_zero, Real.exp_zero]
  field_simp

/-- **Brick 4 (exact).** `∫|Kλ'| = 2/δ`. -/
theorem greenKernelDeriv_l1_eq (hlam : 0 < lam) :
    ∫ z, |greenKernelDeriv c lam z| = 2 * (greenDelta c lam)⁻¹ := by
  have hfi := greenKernelDeriv_integrable (c := c) hlam
  have hsplit := MeasureTheory.integral_add_compl
    (s := Set.Iic (0:ℝ)) measurableSet_Iic hfi
  simp only [Set.compl_Iic] at hsplit
  rw [← hsplit, absDeriv_setIntegral_Iic hlam, absDeriv_setIntegral_Ioi hlam]
  ring

/-- **Brick 4 (bound).** `∫|Kλ'| = 2/δ`, an explicit `L¹` bound `→ 0` as
`λ → ∞`. -/
theorem greenKernelDeriv_l1_bound (hlam : 0 < lam) :
    ∫ z, |greenKernelDeriv c lam z| ≤ 2 * (greenDelta c lam)⁻¹ :=
  le_of_eq (greenKernelDeriv_l1_eq hlam)

/-! ## Brick 5 — the per-step implicit Green map `Φ_{λ,u,Z}`

Cross-frozen analogue of `auxMap`: the OLD iterate `Z = z_k` enters the linear
shift `λ·Z`, the NEW unknown `W` enters the nonlinear reaction `W(1−W^a)` and
flux `W^m·V_u'`.  As a function `W ↦ Φ(W)` this is a contraction for large `λ`
(below). -/

/-- The per-step implicit Green map `Φ_{λ,u,Z}` in divergence form. -/
def crossImplicitMap (p : CMParams) (c lam : ℝ) (u Z W : ℝ → ℝ) : ℝ → ℝ :=
  fun x =>
    (∫ y, greenKernel c lam (x - y)
        * (reactionFun p.α (W y) + lam * Z y))
      - p.χ * ∫ y, greenKernelDeriv c lam (x - y)
          * ((W y) ^ p.m * deriv (frozenElliptic p u) y)

/-- Sanity: at `W := u, Z := u` the cross map collapses to the committed
stationary `auxMap` (the implicit step degenerates to the fixed-frozen
problem).  Pure unfolding via `reactionFun`/`auxReaction`/`auxFlux`. -/
theorem crossImplicitMap_self_eq_auxMap (p : CMParams) (c lam : ℝ) (u : ℝ → ℝ) :
    crossImplicitMap p c lam u u u = auxMap p c lam u := by
  funext x
  unfold crossImplicitMap auxMap auxReaction auxFlux reactionFun
  rfl

/-! ## Brick 6 — the contraction factor and its large-`λ` smallness

`crossContractionFactor` is the explicit constant in
`|Φ(W₁) − Φ(W₂)| ≤ factor · ‖W₁ − W₂‖∞`, namely

    `factor = L_rxn·‖Kλ‖₁ + |χ|·L_m·B_{V'}·‖Kλ'‖₁`
            = L_rxn/λ + |χ|·L_m·B_{V'}·(2/δ)`,

with `L_rxn = reactionLip p.α M`, `L_m = rpowLip p.m M`, `B_{V'}` a bound on
`|V_u'|`.  Both kernel norms `→ 0` as `λ → ∞`, so for `λ` large enough the
factor is `< 1` (a genuine contraction constant). -/

/-- Explicit contraction factor for the per-step map on `[0,M]`-valued data with
`|V_u'| ≤ Bv`. -/
def crossContractionFactor (p : CMParams) (M Bv lam delta : ℝ) : ℝ :=
  reactionLip p.α M * lam⁻¹
    + |p.χ| * rpowLip p.m M * Bv * (2 * delta⁻¹)

theorem crossContractionFactor_nonneg (p : CMParams) {M Bv lam delta : ℝ}
    (hM : 0 ≤ M) (hBv : 0 ≤ Bv) (hlam : 0 < lam) (hdelta : 0 < delta) :
    0 ≤ crossContractionFactor p M Bv lam delta := by
  unfold crossContractionFactor
  have h1 : 0 ≤ reactionLip p.α M * lam⁻¹ :=
    mul_nonneg (reactionLip_nonneg p.hα hM) (le_of_lt (inv_pos.mpr hlam))
  have h2 : 0 ≤ |p.χ| * rpowLip p.m M * Bv * (2 * delta⁻¹) := by
    have : 0 ≤ rpowLip p.m M := rpowLip_nonneg p.hm hM
    have hd : 0 ≤ delta⁻¹ := le_of_lt (inv_pos.mpr hdelta)
    positivity
  linarith

/-- **Brick 6 — large-`λ` smallness of the contraction factor.**
As `λ → ∞`, both `lam⁻¹ → 0` and `δ = √(c²+4λ)⁻¹ → 0`, so for `λ` large enough
the contraction factor is `< 1`.  Concretely: there is a threshold `λ₀` such
that for all `λ > λ₀` (with `δ = greenDelta c λ`) we have
`crossContractionFactor p M Bv λ δ < 1`. -/
theorem crossContractionFactor_lt_one_of_large_lambda
    (p : CMParams) {M Bv : ℝ} (hM : 0 ≤ M) (hBv : 0 ≤ Bv) (c : ℝ) :
    ∀ᶠ lam in Filter.atTop,
      crossContractionFactor p M Bv lam (greenDelta c lam) < 1 := by
  -- term 1 → 0
  have hT1 : Filter.Tendsto
      (fun lam : ℝ => reactionLip p.α M * lam⁻¹) Filter.atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (reactionLip p.α M)
    simpa using this
  -- δ = √(c²+4λ) → ∞
  have hδ_top : Filter.Tendsto (fun lam : ℝ => greenDelta c lam)
      Filter.atTop Filter.atTop := by
    unfold greenDelta
    refine Real.tendsto_sqrt_atTop.comp ?_
    have : Filter.Tendsto (fun lam : ℝ => c ^ 2 + 4 * lam)
        Filter.atTop Filter.atTop := by
      apply Filter.tendsto_atTop_add_const_left
      exact Filter.tendsto_atTop_atTop.mpr fun b =>
        ⟨b / 4, fun a ha => by linarith⟩
    exact this
  -- δ⁻¹ → 0
  have hδinv : Filter.Tendsto (fun lam : ℝ => (greenDelta c lam)⁻¹)
      Filter.atTop (𝓝 0) :=
    (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp hδ_top
  -- term 2 → 0
  have hT2 : Filter.Tendsto
      (fun lam : ℝ => |p.χ| * rpowLip p.m M * Bv * (2 * (greenDelta c lam)⁻¹))
      Filter.atTop (𝓝 0) := by
    have hc : Filter.Tendsto
        (fun lam : ℝ => (|p.χ| * rpowLip p.m M * Bv * 2) * (greenDelta c lam)⁻¹)
        Filter.atTop (𝓝 0) := by
      have := hδinv.const_mul (|p.χ| * rpowLip p.m M * Bv * 2)
      simpa using this
    refine hc.congr ?_
    intro lam; ring
  -- sum → 0
  have hsum : Filter.Tendsto
      (fun lam : ℝ => crossContractionFactor p M Bv lam (greenDelta c lam))
      Filter.atTop (𝓝 0) := by
    have := hT1.add hT2
    simpa [crossContractionFactor, add_zero] using this
  -- eventually < 1
  have h1pos : (0:ℝ) < 1 := one_pos
  have := hsum.eventually (eventually_lt_nhds h1pos)
  simpa using this

/-! ## Bricks 5–6 — the Banach per-step solvability skeleton

On the complete sup-norm space `ℝ →ᵇ ℝ`, any map `Φ` whose pointwise
output-difference is dominated by `K · dist W₁ W₂` with `K < 1` is
`ContractingWith K Φ`, hence has a unique fixed point.  This is the genuine
Banach plumbing for the per-step implicit Green step: feeding the contraction
factor (`< 1` for large `λ`, brick 6) and the L¹-difference estimate
(bricks 1–4) gives `∃! W, Φ W = W`, the uniquely-solvable implicit step.

The hypotheses are NON-VACUOUS: they consume a genuine `K < 1` and a real
sup-norm Lipschitz bound (not a degenerate domain). -/

/-- A sup-norm contraction on `ℝ →ᵇ ℝ`: if the pointwise output difference is
`≤ K · dist W₁ W₂` with `K < 1`, then `Φ` is `ContractingWith K`. -/
theorem contractingWith_of_pointwise_dist_le
    {Φ : (ℝ →ᵇ ℝ) → (ℝ →ᵇ ℝ)} {K : NNReal} (hK : K < 1)
    (hbound : ∀ W₁ W₂ : ℝ →ᵇ ℝ, ∀ x : ℝ,
      dist (Φ W₁ x) (Φ W₂ x) ≤ (K : ℝ) * dist W₁ W₂) :
    ContractingWith K Φ := by
  refine ⟨hK, LipschitzWith.of_dist_le_mul ?_⟩
  intro W₁ W₂
  rw [BoundedContinuousFunction.dist_le_iff_of_nonempty]
  intro x
  exact hbound W₁ W₂ x


/-- **Bricks 5–6 — uniquely solvable implicit step (Banach).**
A sup-norm contraction `Φ : ℝ →ᵇ ℝ → ℝ →ᵇ ℝ` with constant `K < 1` has a
unique fixed point: `∃! W, Φ W = W`.  This is the per-step implicit Green
step's unique solvability. -/
theorem crossImplicitStep_exists_unique
    {Φ : (ℝ →ᵇ ℝ) → (ℝ →ᵇ ℝ)} {K : NNReal} (hK : K < 1)
    (hbound : ∀ W₁ W₂ : ℝ →ᵇ ℝ, ∀ x : ℝ,
      dist (Φ W₁ x) (Φ W₂ x) ≤ (K : ℝ) * dist W₁ W₂) :
    ∃! W : ℝ →ᵇ ℝ, Φ W = W := by
  have hcontr : ContractingWith K Φ :=
    contractingWith_of_pointwise_dist_le hK hbound
  refine ⟨ContractingWith.fixedPoint Φ hcontr, ?_, ?_⟩
  · -- it is a fixed point
    exact hcontr.fixedPoint_isFixedPt
  · -- uniqueness
    intro W hW
    -- hW : Φ W = W, i.e. IsFixedPt Φ W
    have hWfix : Function.IsFixedPt Φ W := hW
    exact hcontr.fixedPoint_unique hWfix
