import ShenWork.Wiener.EWA.RealPowLipschitz

/-!
# EWA brick 1 (χ₀<0 Route A′) — graded EWA-norm Lipschitz of the flux `Q` and source `G`

The contraction foundation for the source-form fixed point.  On a positive ball in
the bilateral Wiener envelope space we prove the EWA-norm Lipschitz estimates

* `chemFluxEWA_lipschitz` : `‖Q(u) − Q(w)‖ ≤ L_Q · ‖u − w‖`, and
* `growthEWA_lipschitz`   : `‖G(u) − G(w)‖ ≤ L_G · ‖u − w‖`,

with `Q(u) = u · v_x · (1+v)^{−β}`, `v = R_μ(ν u^γ) : EWA T 3`, `v_x = ∂_x v`, and
`G(u) = u·(a − b·u^α)`.  Everything is composed from the committed pieces — no
re-derivation:

* `realPowEWA_lipschitz` / `realPowEWA_norm_le` (the WL1 power, grade-1),
* `qFactor_lipschitz` / `qFactor_norm_le` (the WL2 factor `(1+v)^{−β}`, grade-1),
* `gResolver μ` (`+2` smoothing), `gDeriv` (`−1`), `incl` (grade-drop) — all
  *bounded-linear*, hence Lipschitz with their explicit operator-norm constants
  `resolverGainConst μ`, `Real.pi`, `1`,
* `norm_mul_le_gwa` for the Banach-algebra product/Leibniz expansion.

## Grade
The committed `chemFluxEWA u : EWA T 1` is **grade 1**: the field climbs to `EWA T 3`
via the `+2` resolver, then `gDeriv`/`incl` bring `v_x` and `v` back down to grade 1,
where the product `u · v_x · (1+v)^{−β}` and *both* committed Lipschitz lemmas
(`realPowEWA_lipschitz`, `qFactor_lipschitz`) live.  We therefore prove the Lipschitz
bound for the committed grade-1 flux; the resolver `+2` smoothing is what gives the
two spare grades the Duhamel→cosine→C² endpoint needs upstream (the field `v` is
`C²`-regular as an `EWA T 3` element), but the *flux norm* is taken in grade 1.

The constants are stated explicitly in terms of the committed constants, the ball
radius `R`, and the floors `δ_u` (for `u`) and `δ_v` (for `1+v`).
-/

open scoped BigOperators
open MeasureTheory Set Real
open ShenWork.GWA ShenWork.Wiener

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-! ### Part 0 — a CLM is Lipschitz with its operator norm. -/

/-- Any continuous linear map is Lipschitz on the difference, with its operator norm:
`‖Φ a − Φ b‖ ≤ ‖Φ‖ · ‖a − b‖`. -/
theorem clm_diff_norm_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (Φ : E →L[ℂ] F) (a b : E) :
    ‖Φ a - Φ b‖ ≤ ‖Φ‖ * ‖a - b‖ := by
  rw [← map_sub]
  exact Φ.le_opNorm _

/-- A CLM with an explicit operator-norm bound `‖Φ‖ ≤ C` is `C`-Lipschitz on the
difference: `‖Φ a − Φ b‖ ≤ C · ‖a − b‖`. -/
theorem clm_diff_norm_le_const {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (Φ : E →L[ℂ] F) {C : ℝ}
    (hΦ : ‖Φ‖ ≤ C) (a b : E) :
    ‖Φ a - Φ b‖ ≤ C * ‖a - b‖ := by
  refine le_trans (clm_diff_norm_le Φ a b) ?_
  exact mul_le_mul_of_nonneg_right hΦ (norm_nonneg _)

/-- From a pointwise apply-bound `‖Φ a‖ ≤ C·‖a‖`, the CLM is `C`-Lipschitz on the
difference via linearity `Φ a − Φ b = Φ (a−b)`. -/
theorem clm_diff_of_apply_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (Φ : E →L[ℂ] F) {C : ℝ}
    (hΦ : ∀ a, ‖Φ a‖ ≤ C * ‖a‖) (a b : E) :
    ‖Φ a - Φ b‖ ≤ C * ‖a - b‖ := by
  rw [← map_sub]; exact hΦ _

/-! ### Part 1 — explicit operator-norm bounds for the grade-flow operators.

Each is a `scalarMultiplier`/`coeffwiseCLM`, whose underlying linear-map bound
`norm_coeffwiseLM_le` is the committed `‖Φ a‖ ≤ C · ‖a‖`. -/

/-- `‖gResolver μ hμ a‖ ≤ resolverGainConst μ · ‖a‖` (the `+2` smoothing op-norm). -/
theorem norm_gResolver_apply_le {K : Type*} [NormedCommRing K] [NormedAlgebra ℂ K]
    [CompleteSpace K] {r : ℕ} {μ : ℝ} (hμ : 0 < μ) (a : GWA K r) :
    ‖GWA.gResolver μ hμ a‖ ≤ GWA.resolverGainConst μ * ‖a‖ := by
  rw [GWA.gResolver, GWA.scalarMultiplier, GWA.coeffwiseCLM,
    LinearMap.mkContinuous_apply]
  exact GWA.norm_coeffwiseLM_le _ _ (by unfold GWA.resolverGainConst; positivity) _ a

/-- `‖gDeriv a‖ ≤ Real.pi · ‖a‖` (the `−1` derivative op-norm). -/
theorem norm_gDeriv_apply_le {K : Type*} [NormedCommRing K] [NormedAlgebra ℂ K]
    [CompleteSpace K] {r : ℕ} (a : GWA K (r + 1)) :
    ‖GWA.gDeriv a‖ ≤ Real.pi * ‖a‖ := by
  rw [GWA.gDeriv, GWA.scalarMultiplier, GWA.coeffwiseCLM, LinearMap.mkContinuous_apply]
  exact GWA.norm_coeffwiseLM_le _ _ Real.pi_nonneg _ a

/-- `‖incl h a‖ ≤ ‖a‖` (grade-drop op-norm `≤ 1`). -/
theorem norm_incl_apply_le {K : Type*} [NormedCommRing K] [NormedAlgebra ℂ K]
    [CompleteSpace K] {r s : ℕ} (h : r ≤ s) (a : GWA K s) :
    ‖GWA.incl h a‖ ≤ ‖a‖ := by
  rw [GWA.incl, GWA.scalarMultiplier, GWA.coeffwiseCLM, LinearMap.mkContinuous_apply]
  refine le_trans (GWA.norm_coeffwiseLM_le _ _ zero_le_one _ a) ?_
  rw [one_mul]

/-! ### Part 2 — Banach-algebra product Lipschitz (Leibniz on a ball). -/

/-- **Bilinear / Leibniz Lipschitz.** In a normed ring, for products on a ball:
`‖a·b − c·d‖ ≤ ‖a‖·‖b − d‖ + ‖d‖·‖a − c‖`. -/
theorem mul_diff_norm_le {A : Type*} [NormedRing A] (a b c d : A) :
    ‖a * b - c * d‖ ≤ ‖a‖ * ‖b - d‖ + ‖d‖ * ‖a - c‖ := by
  have hsplit : a * b - c * d = a * (b - d) + (a - c) * d := by noncomm_ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  refine add_le_add (norm_mul_le _ _) ?_
  rw [mul_comm]
  exact norm_mul_le _ _

/-- **Triple-product Lipschitz on a ball.** If `‖aᵢ‖,‖bᵢ‖,‖cᵢ‖` are bounded by
`Ma,Mb,Mc` and each factor is Lipschitz (`‖a₁−a₂‖ ≤ La·d`, etc.) then
`‖a₁b₁c₁ − a₂b₂c₂‖ ≤ (Mb·Mc·La + Ma·Mc·Lb + Ma·Mb·Lc)·d`. -/
theorem triple_mul_diff_norm_le {A : Type*} [NormedRing A] {a₁ a₂ b₁ b₂ c₁ c₂ : A}
    {Ma Mb Mc La Lb Lc d : ℝ} (hMa : 0 ≤ Ma) (hMb : 0 ≤ Mb)
    (ha2 : ‖a₂‖ ≤ Ma) (hb2 : ‖b₂‖ ≤ Mb) (hc2 : ‖c₂‖ ≤ Mc) (hb1 : ‖b₁‖ ≤ Mb)
    (hc1 : ‖c₁‖ ≤ Mc)
    (haL : ‖a₁ - a₂‖ ≤ La * d) (hbL : ‖b₁ - b₂‖ ≤ Lb * d) (hcL : ‖c₁ - c₂‖ ≤ Lc * d) :
    ‖a₁ * b₁ * c₁ - a₂ * b₂ * c₂‖ ≤ (Mb * Mc * La + Ma * Mc * Lb + Ma * Mb * Lc) * d := by
  -- a₁b₁c₁ − a₂b₂c₂ = (a₁−a₂)(b₁c₁) + a₂(b₁−b₂)c₁ + a₂b₂(c₁−c₂).
  have hsplit : a₁ * b₁ * c₁ - a₂ * b₂ * c₂
      = (a₁ - a₂) * (b₁ * c₁) + a₂ * ((b₁ - b₂) * c₁) + a₂ * (b₂ * (c₁ - c₂)) := by
    noncomm_ring
  rw [hsplit]
  have hLa : (0 : ℝ) ≤ La * d := le_trans (norm_nonneg _) haL
  have hLb : (0 : ℝ) ≤ Lb * d := le_trans (norm_nonneg _) hbL
  have hLc : (0 : ℝ) ≤ Lc * d := le_trans (norm_nonneg _) hcL
  have hMc : (0 : ℝ) ≤ Mc := le_trans (norm_nonneg _) hc1
  -- term-by-term norm bounds.
  have hT1 : ‖(a₁ - a₂) * (b₁ * c₁)‖ ≤ Mb * Mc * (La * d) := by
    refine le_trans (norm_mul_le _ _) ?_
    refine le_trans (mul_le_mul haL (norm_mul_le _ _) (norm_nonneg _) hLa) ?_
    have hbc : ‖b₁‖ * ‖c₁‖ ≤ Mb * Mc := mul_le_mul hb1 hc1 (norm_nonneg _) hMb
    calc La * d * (‖b₁‖ * ‖c₁‖) ≤ La * d * (Mb * Mc) :=
          mul_le_mul_of_nonneg_left hbc hLa
      _ = Mb * Mc * (La * d) := by ring
  have hT2 : ‖a₂ * ((b₁ - b₂) * c₁)‖ ≤ Ma * Mc * (Lb * d) := by
    refine le_trans (norm_mul_le _ _) ?_
    have hbc : ‖(b₁ - b₂) * c₁‖ ≤ Lb * d * Mc := by
      refine le_trans (norm_mul_le _ _) ?_
      exact mul_le_mul hbL hc1 (norm_nonneg _) hLb
    calc ‖a₂‖ * ‖(b₁ - b₂) * c₁‖ ≤ Ma * (Lb * d * Mc) :=
          mul_le_mul ha2 hbc (norm_nonneg _) hMa
      _ = Ma * Mc * (Lb * d) := by ring
  have hT3 : ‖a₂ * (b₂ * (c₁ - c₂))‖ ≤ Ma * Mb * (Lc * d) := by
    refine le_trans (norm_mul_le _ _) ?_
    have hbc : ‖b₂ * (c₁ - c₂)‖ ≤ Mb * (Lc * d) := by
      refine le_trans (norm_mul_le _ _) ?_
      exact mul_le_mul hb2 hcL (norm_nonneg _) hMb
    calc ‖a₂‖ * ‖b₂ * (c₁ - c₂)‖ ≤ Ma * (Mb * (Lc * d)) :=
          mul_le_mul ha2 hbc (norm_nonneg _) hMa
      _ = Ma * Mb * (Lc * d) := by ring
  refine le_trans (norm_add_le _ _) ?_
  refine le_trans (add_le_add (le_trans (norm_add_le _ _) (add_le_add hT1 hT2)) hT3) ?_
  apply le_of_eq; ring

/-! ### Part 3 — the growth source `G(u) = u·(a − b·u^α)` Lipschitz (grade 1). -/

/-- Norm bound for the logistic factor `P(u) = a·1 − b·u^α` on the ball `‖u‖ ≤ R`. -/
theorem growthFactor_norm_le {α a b δ Md R : ℝ} {u : EWA T 1} (hα : 0 ≤ α)
    (hδpos : 0 < δ) (hMd : 0 ≤ Md) (hu_floor : UniformFloor u δ)
    (huD : ‖GWA.gDeriv u‖ ≤ Md) (huR : ‖u‖ ≤ R) (hR : 0 ≤ R) :
    ‖(a : ℂ) • (1 : EWA T 1) - (b : ℂ) • realPowEWA u α‖
      ≤ |a| * ‖(1 : EWA T 1)‖ + |b| *
        (R ^ (Nat.floor α + 1) * negNormConst ((Nat.floor α + 1 : ℝ) - α) δ Md) := by
  refine le_trans (norm_sub_le _ _) ?_
  rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs]
  have hpow := realPowEWA_norm_le (T := T) (f := u) hα hδpos hMd hu_floor huD huR hR
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hpow (abs_nonneg _))

/-- **`growthEWA_lipschitz`** (grade 1).  With `m = ⌊α⌋+1`, on the ball `‖·‖ ≤ R`
under a common floor `δ` and derivative bound `Md`:
`‖G(u) − G(w)‖ ≤ L_G · ‖u − w‖`, where
`L_G = R·|b|·L_pow + |a|·‖(1:EWA T 1)‖ + |b|·R^m·negNormConst s`,
`L_pow = m·R^{m−1}·negNormConst s + R^m·negLipConst s`, `s = m−α`. -/
theorem growthEWA_lipschitz {α a b δ Md R : ℝ} {u w : EWA T 1} (hα : 0 ≤ α)
    (hδpos : 0 < δ) (hMd : 0 ≤ Md) (hu_floor : UniformFloor u δ)
    (hw_floor : UniformFloor w δ) (huD : ‖GWA.gDeriv u‖ ≤ Md) (hwD : ‖GWA.gDeriv w‖ ≤ Md)
    (huR : ‖u‖ ≤ R) (hwR : ‖w‖ ≤ R) (hR : 0 ≤ R) :
    ‖growthEWA α a b u - growthEWA α a b w‖
      ≤ (R * (|b| * ((Nat.floor α + 1 : ℝ) * R ^ ((Nat.floor α + 1) - 1)
              * negNormConst ((Nat.floor α + 1 : ℝ) - α) δ Md
            + R ^ (Nat.floor α + 1) * negLipConst ((Nat.floor α + 1 : ℝ) - α) δ Md))
          + (|a| * ‖(1 : EWA T 1)‖ + |b| *
              (R ^ (Nat.floor α + 1) * negNormConst ((Nat.floor α + 1 : ℝ) - α) δ Md)))
        * ‖u - w‖ := by
  set Pu : EWA T 1 := (a : ℂ) • (1 : EWA T 1) - (b : ℂ) • realPowEWA u α with hPu
  set Pw : EWA T 1 := (a : ℂ) • (1 : EWA T 1) - (b : ℂ) • realPowEWA w α with hPw
  set Lp : ℝ := (Nat.floor α + 1 : ℝ) * R ^ ((Nat.floor α + 1) - 1)
            * negNormConst ((Nat.floor α + 1 : ℝ) - α) δ Md
          + R ^ (Nat.floor α + 1) * negLipConst ((Nat.floor α + 1 : ℝ) - α) δ Md with hLp
  set Np : ℝ := R ^ (Nat.floor α + 1) * negNormConst ((Nat.floor α + 1 : ℝ) - α) δ Md with hNp
  rw [growthEWA, growthEWA, ← hPu, ← hPw]
  -- Leibniz split: ‖u·Pu − w·Pw‖ ≤ ‖u‖·‖Pu − Pw‖ + ‖Pw‖·‖u − w‖.
  refine le_trans (mul_diff_norm_le u Pu w Pw) ?_
  -- ‖Pu − Pw‖ = |b|·‖u^α − w^α‖ ≤ |b|·Lp·‖u − w‖.
  have hPdiff : ‖Pu - Pw‖ ≤ |b| * (Lp * ‖u - w‖) := by
    have heq : Pu - Pw = (b : ℂ) • (realPowEWA w α - realPowEWA u α) := by
      rw [hPu, hPw]; rw [smul_sub]; abel
    rw [heq, norm_smul, Complex.norm_real, Real.norm_eq_abs, norm_sub_rev]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact realPowEWA_lipschitz hα hδpos hMd hu_floor hw_floor huD hwD huR hwR hR
  -- ‖Pw‖ ≤ |a|·‖1‖ + |b|·Np.
  have hPwn : ‖Pw‖ ≤ |a| * ‖(1 : EWA T 1)‖ + |b| * Np := by
    rw [hPw, hNp]
    exact growthFactor_norm_le hα hδpos hMd hw_floor hwD hwR hR
  -- assemble.
  have hd : (0 : ℝ) ≤ ‖u - w‖ := norm_nonneg _
  have h1 : ‖u‖ * ‖Pu - Pw‖ ≤ R * (|b| * (Lp * ‖u - w‖)) :=
    mul_le_mul huR hPdiff (norm_nonneg _) hR
  have h2 : ‖Pw‖ * ‖u - w‖ ≤ (|a| * ‖(1 : EWA T 1)‖ + |b| * Np) * ‖u - w‖ :=
    mul_le_mul_of_nonneg_right hPwn hd
  refine le_trans (add_le_add h1 h2) ?_
  rw [hLp, hNp]; apply le_of_eq; ring

/-! ### Part 4 — the resolved field `v = R_μ(ν u^γ) : EWA T 3` norm + Lipschitz. -/

/-- Norm bound for the resolved field on the ball `‖u‖ ≤ R`:
`‖v‖ ≤ C_μ·|ν|·R^m·negNormConst s` (`m = ⌊γ⌋+1`, `s = m−γ`). -/
theorem vFieldEWA_norm_le {μ ν γ δ Md R : ℝ} (hμ : 0 < μ) {u : EWA T 1} (hγ : 0 ≤ γ)
    (hδpos : 0 < δ) (hMd : 0 ≤ Md) (hu_floor : UniformFloor u δ)
    (huD : ‖GWA.gDeriv u‖ ≤ Md) (huR : ‖u‖ ≤ R) (hR : 0 ≤ R) :
    ‖vFieldEWA μ ν γ hμ u‖
      ≤ GWA.resolverGainConst μ * (|ν| *
          (R ^ (Nat.floor γ + 1) * negNormConst ((Nat.floor γ + 1 : ℝ) - γ) δ Md)) := by
  rw [vFieldEWA]
  refine le_trans (norm_gResolver_apply_le hμ _) ?_
  refine mul_le_mul_of_nonneg_left ?_ (by unfold GWA.resolverGainConst; positivity)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    (realPowEWA_norm_le hγ hδpos hMd hu_floor huD huR hR) (abs_nonneg _)

/-- Lipschitz of the resolved field on the ball:
`‖v(u) − v(w)‖ ≤ C_μ·|ν|·L_pow·‖u − w‖`. -/
theorem vFieldEWA_lipschitz {μ ν γ δ Md R : ℝ} (hμ : 0 < μ) {u w : EWA T 1} (hγ : 0 ≤ γ)
    (hδpos : 0 < δ) (hMd : 0 ≤ Md) (hu_floor : UniformFloor u δ)
    (hw_floor : UniformFloor w δ) (huD : ‖GWA.gDeriv u‖ ≤ Md) (hwD : ‖GWA.gDeriv w‖ ≤ Md)
    (huR : ‖u‖ ≤ R) (hwR : ‖w‖ ≤ R) (hR : 0 ≤ R) :
    ‖vFieldEWA μ ν γ hμ u - vFieldEWA μ ν γ hμ w‖
      ≤ GWA.resolverGainConst μ * (|ν| *
          ((Nat.floor γ + 1 : ℝ) * R ^ ((Nat.floor γ + 1) - 1)
              * negNormConst ((Nat.floor γ + 1 : ℝ) - γ) δ Md
            + R ^ (Nat.floor γ + 1) * negLipConst ((Nat.floor γ + 1 : ℝ) - γ) δ Md))
        * ‖u - w‖ := by
  have hCμ : (0 : ℝ) ≤ GWA.resolverGainConst μ := by unfold GWA.resolverGainConst; positivity
  -- the difference passes through the linear resolver (mirrors `vFieldEWA_norm_le`).
  have hsub : vFieldEWA μ ν γ hμ u - vFieldEWA μ ν γ hμ w
      = GWA.gResolver μ hμ ((ν : ℂ) • realPowEWA u γ - (ν : ℂ) • realPowEWA w γ) := by
    rw [vFieldEWA, vFieldEWA, ← map_sub]
  rw [hsub]
  refine le_trans (norm_gResolver_apply_le hμ _) ?_
  rw [mul_assoc, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hCμ
  rw [← smul_sub, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have h := realPowEWA_lipschitz hγ hδpos hMd hu_floor hw_floor huD hwD huR hwR hR
  exact h.trans_eq (by ring)

/-! ### Part 5 — the down-graded field derivative `v_x` and the field-at-grade-1. -/

/-- `v_x(u) = incl(1≤2)(gDeriv v) : EWA T 1`, the committed flux's second factor. -/
def vxEWA (μ ν γ : ℝ) (hμ : 0 < μ) (u : EWA T 1) : EWA T 1 :=
  GWA.incl (by omega : (1:ℕ) ≤ 2) (GWA.gDeriv (vFieldEWA μ ν γ hμ u))

/-- `vd(u) = incl(1≤3) v : EWA T 1`, the committed flux's resolved field at grade 1. -/
def vdEWA (μ ν γ : ℝ) (hμ : 0 < μ) (u : EWA T 1) : EWA T 1 :=
  GWA.incl (by omega : (1:ℕ) ≤ 3) (vFieldEWA μ ν γ hμ u)

/-- `v_x` norm bound on the ball: `‖v_x(u)‖ ≤ π·C_μ·|ν|·R^m·negNormConst s`. -/
theorem vxEWA_norm_le {μ ν γ δ Md R : ℝ} (hμ : 0 < μ) {u : EWA T 1} (hγ : 0 ≤ γ)
    (hδpos : 0 < δ) (hMd : 0 ≤ Md) (hu_floor : UniformFloor u δ)
    (huD : ‖GWA.gDeriv u‖ ≤ Md) (huR : ‖u‖ ≤ R) (hR : 0 ≤ R) :
    ‖vxEWA μ ν γ hμ u‖
      ≤ Real.pi * (GWA.resolverGainConst μ * (|ν| *
          (R ^ (Nat.floor γ + 1) * negNormConst ((Nat.floor γ + 1 : ℝ) - γ) δ Md))) := by
  rw [vxEWA]
  refine le_trans (norm_incl_apply_le _ _) ?_
  refine le_trans (norm_gDeriv_apply_le _) ?_
  exact mul_le_mul_of_nonneg_left
    (vFieldEWA_norm_le hμ hγ hδpos hMd hu_floor huD huR hR) Real.pi_nonneg

/-- `v_x` Lipschitz on the ball: `‖v_x(u) − v_x(w)‖ ≤ π·LipV·‖u − w‖`. -/
theorem vxEWA_lipschitz {μ ν γ δ Md R : ℝ} (hμ : 0 < μ) {u w : EWA T 1} (hγ : 0 ≤ γ)
    (hδpos : 0 < δ) (hMd : 0 ≤ Md) (hu_floor : UniformFloor u δ)
    (hw_floor : UniformFloor w δ) (huD : ‖GWA.gDeriv u‖ ≤ Md) (hwD : ‖GWA.gDeriv w‖ ≤ Md)
    (huR : ‖u‖ ≤ R) (hwR : ‖w‖ ≤ R) (hR : 0 ≤ R) :
    ‖vxEWA μ ν γ hμ u - vxEWA μ ν γ hμ w‖
      ≤ Real.pi * (GWA.resolverGainConst μ * (|ν| *
          ((Nat.floor γ + 1 : ℝ) * R ^ ((Nat.floor γ + 1) - 1)
              * negNormConst ((Nat.floor γ + 1 : ℝ) - γ) δ Md
            + R ^ (Nat.floor γ + 1) * negLipConst ((Nat.floor γ + 1 : ℝ) - γ) δ Md)))
        * ‖u - w‖ := by
  have hsub : vxEWA μ ν γ hμ u - vxEWA μ ν γ hμ w
      = GWA.incl (by omega : (1:ℕ) ≤ 2)
          (GWA.gDeriv (vFieldEWA μ ν γ hμ u - vFieldEWA μ ν γ hμ w)) := by
    rw [vxEWA, vxEWA, ← map_sub, ← map_sub]
  rw [hsub]
  refine le_trans (norm_incl_apply_le _ _) ?_
  refine le_trans (norm_gDeriv_apply_le _) ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ Real.pi_nonneg
  exact vFieldEWA_lipschitz hμ hγ hδpos hMd hu_floor hw_floor huD hwD huR hwR hR

/-- `vd` Lipschitz on the ball: `‖vd(u) − vd(w)‖ ≤ LipV·‖u − w‖`. -/
theorem vdEWA_lipschitz {μ ν γ δ Md R : ℝ} (hμ : 0 < μ) {u w : EWA T 1} (hγ : 0 ≤ γ)
    (hδpos : 0 < δ) (hMd : 0 ≤ Md) (hu_floor : UniformFloor u δ)
    (hw_floor : UniformFloor w δ) (huD : ‖GWA.gDeriv u‖ ≤ Md) (hwD : ‖GWA.gDeriv w‖ ≤ Md)
    (huR : ‖u‖ ≤ R) (hwR : ‖w‖ ≤ R) (hR : 0 ≤ R) :
    ‖vdEWA μ ν γ hμ u - vdEWA μ ν γ hμ w‖
      ≤ GWA.resolverGainConst μ * (|ν| *
          ((Nat.floor γ + 1 : ℝ) * R ^ ((Nat.floor γ + 1) - 1)
              * negNormConst ((Nat.floor γ + 1 : ℝ) - γ) δ Md
            + R ^ (Nat.floor γ + 1) * negLipConst ((Nat.floor γ + 1 : ℝ) - γ) δ Md))
        * ‖u - w‖ := by
  have hsub : vdEWA μ ν γ hμ u - vdEWA μ ν γ hμ w
      = GWA.incl (by omega : (1:ℕ) ≤ 3) (vFieldEWA μ ν γ hμ u - vFieldEWA μ ν γ hμ w) := by
    rw [vdEWA, vdEWA, ← map_sub]
  rw [hsub]
  refine le_trans (norm_incl_apply_le _ _) ?_
  exact vFieldEWA_lipschitz hμ hγ hδpos hMd hu_floor hw_floor huD hwD huR hwR hR

/-! ### Part 6 — the chemotactic flux `Q(u) = u·v_x·(1+v)^{−β}` Lipschitz (grade 1).

`Q = chemFluxEWA = u · v_x · qFactor β (vd)` is the committed triple product at grade 1
(the field climbs to `EWA T 3`, then `gDeriv`/`incl` bring `v_x`/`v` back to grade 1).
The three factor bounds:
`Mb := π·C_μ·|ν|·NormPow_γ` (v_x norm), `Mc := negNormConst β δv Mdv` (qFactor norm);
the three Lipschitz constants `La = 1`, `Lb := π·C_μ·|ν|·L_pow_γ` (v_x),
`Lc := negLipConst β δv Mdv · C_μ·|ν|·L_pow_γ` (qFactor∘vd). -/

/-- **`chemFluxEWA_lipschitz`** (grade 1).  On the positive ball `‖u‖,‖w‖ ≤ R` under
the floors `δ` (for the WL1 power on `u,w`) and `δv` (for `1+v` feeding the WL2
factor) and the derivative bounds `Md` (on `u,w`) and `Mdv` (on `vd`):
`‖Q(u) − Q(w)‖ ≤ L_Q · ‖u − w‖`,
`L_Q = Mb·Mc·1 + R·Mc·Lb + R·Mb·Lc` with `Mb,Mc,Lb,Lc` as above. -/
theorem chemFluxEWA_lipschitz {μ ν β γ δ δv Md Mdv R : ℝ} (hμ : 0 < μ) {u w : EWA T 1}
    (hγ : 0 ≤ γ) (hβ : 0 < β) (hδpos : 0 < δ) (hδvpos : 0 < δv) (hMd : 0 ≤ Md)
    (hMdv : 0 ≤ Mdv) (hu_floor : UniformFloor u δ) (hw_floor : UniformFloor w δ)
    (huD : ‖GWA.gDeriv u‖ ≤ Md) (hwD : ‖GWA.gDeriv w‖ ≤ Md) (huR : ‖u‖ ≤ R) (hwR : ‖w‖ ≤ R)
    (hR : 0 ≤ R) (hvdu_floor : UniformFloor (1 + vdEWA μ ν γ hμ u) δv)
    (hvdw_floor : UniformFloor (1 + vdEWA μ ν γ hμ w) δv)
    (hvduD : ‖GWA.gDeriv (vdEWA μ ν γ hμ u)‖ ≤ Mdv)
    (hvdwD : ‖GWA.gDeriv (vdEWA μ ν γ hμ w)‖ ≤ Mdv) :
    ‖chemFluxEWA μ ν β γ hμ u - chemFluxEWA μ ν β γ hμ w‖
      ≤ ((Real.pi * (GWA.resolverGainConst μ * (|ν| *
              (R ^ (Nat.floor γ + 1) * negNormConst ((Nat.floor γ + 1 : ℝ) - γ) δ Md))))
            * negNormConst β δv Mdv * 1
          + R * negNormConst β δv Mdv * (Real.pi * (GWA.resolverGainConst μ * (|ν| *
              ((Nat.floor γ + 1 : ℝ) * R ^ ((Nat.floor γ + 1) - 1)
                  * negNormConst ((Nat.floor γ + 1 : ℝ) - γ) δ Md
                + R ^ (Nat.floor γ + 1) * negLipConst ((Nat.floor γ + 1 : ℝ) - γ) δ Md))))
          + R * (Real.pi * (GWA.resolverGainConst μ * (|ν| *
              (R ^ (Nat.floor γ + 1) * negNormConst ((Nat.floor γ + 1 : ℝ) - γ) δ Md))))
            * (negLipConst β δv Mdv * (GWA.resolverGainConst μ * (|ν| *
                ((Nat.floor γ + 1 : ℝ) * R ^ ((Nat.floor γ + 1) - 1)
                    * negNormConst ((Nat.floor γ + 1 : ℝ) - γ) δ Md
                  + R ^ (Nat.floor γ + 1) * negLipConst ((Nat.floor γ + 1 : ℝ) - γ) δ Md)))))
        * ‖u - w‖ := by
  -- abbreviations for the factor bounds.
  set Mb : ℝ := Real.pi * (GWA.resolverGainConst μ * (|ν| *
      (R ^ (Nat.floor γ + 1) * negNormConst ((Nat.floor γ + 1 : ℝ) - γ) δ Md))) with hMb_def
  set Mc : ℝ := negNormConst β δv Mdv with hMc_def
  set Lp : ℝ := (Nat.floor γ + 1 : ℝ) * R ^ ((Nat.floor γ + 1) - 1)
          * negNormConst ((Nat.floor γ + 1 : ℝ) - γ) δ Md
        + R ^ (Nat.floor γ + 1) * negLipConst ((Nat.floor γ + 1 : ℝ) - γ) δ Md with hLp_def
  set Lb : ℝ := Real.pi * (GWA.resolverGainConst μ * (|ν| * Lp)) with hLb_def
  set Lc : ℝ := negLipConst β δv Mdv * (GWA.resolverGainConst μ * (|ν| * Lp)) with hLc_def
  -- the committed flux as a triple product `u · vx · qFactor∘vd`.
  have hfu : chemFluxEWA μ ν β γ hμ u
      = u * vxEWA μ ν γ hμ u * qFactor β (vdEWA μ ν γ hμ u) := rfl
  have hfw : chemFluxEWA μ ν β γ hμ w
      = w * vxEWA μ ν γ hμ w * qFactor β (vdEWA μ ν γ hμ w) := rfl
  rw [hfu, hfw]
  -- factor norm/Lipschitz bounds.
  have hb2 : ‖vxEWA μ ν γ hμ w‖ ≤ Mb := by
    rw [hMb_def]; exact vxEWA_norm_le hμ hγ hδpos hMd hw_floor hwD hwR hR
  have hb1 : ‖vxEWA μ ν γ hμ u‖ ≤ Mb := by
    rw [hMb_def]; exact vxEWA_norm_le hμ hγ hδpos hMd hu_floor huD huR hR
  have hMbnn : (0 : ℝ) ≤ Mb := le_trans (norm_nonneg _) hb1
  have hc2 : ‖qFactor β (vdEWA μ ν γ hμ w)‖ ≤ Mc :=
    qFactor_norm_le hβ hδvpos hMdv hvdw_floor hvdwD
  have hc1 : ‖qFactor β (vdEWA μ ν γ hμ u)‖ ≤ Mc :=
    qFactor_norm_le hβ hδvpos hMdv hvdu_floor hvduD
  have haL : ‖u - w‖ ≤ 1 * ‖u - w‖ := by rw [one_mul]
  have hbL : ‖vxEWA μ ν γ hμ u - vxEWA μ ν γ hμ w‖ ≤ Lb * ‖u - w‖ := by
    rw [hLb_def, hLp_def]
    exact vxEWA_lipschitz hμ hγ hδpos hMd hu_floor hw_floor huD hwD huR hwR hR
  -- `negLipConst β δv Mdv ≥ 0` (positive Γ-combination at `β > 0`, `δv > 0`, `Mdv ≥ 0`).
  have hnegLip_nn : (0 : ℝ) ≤ negLipConst β δv Mdv := by
    rw [negLipConst]
    have h1 : (0 : ℝ) ≤ 1 / Real.Gamma β := by positivity
    have hg1 : 0 < Real.Gamma (β + 1) := Real.Gamma_pos_of_pos (by linarith)
    have hg2 : 0 < Real.Gamma (β + 2) := Real.Gamma_pos_of_pos (by linarith)
    have hg3 : 0 < Real.Gamma (β + 3) := Real.Gamma_pos_of_pos (by linarith)
    have hδv : (0 : ℝ) < 1 / δv := by positivity
    positivity
  have hcL : ‖qFactor β (vdEWA μ ν γ hμ u) - qFactor β (vdEWA μ ν γ hμ w)‖
      ≤ Lc * ‖u - w‖ := by
    refine le_trans (qFactor_lipschitz hβ hδvpos hMdv hvdu_floor hvdw_floor hvduD hvdwD) ?_
    rw [hLc_def, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hnegLip_nn
    rw [hLp_def]
    exact vdEWA_lipschitz hμ hγ hδpos hMd hu_floor hw_floor huD hwD huR hwR hR
  -- assemble via the triple-product Lipschitz.
  have hmain := triple_mul_diff_norm_le (Ma := R) (Mb := Mb) (Mc := Mc)
    (La := 1) (Lb := Lb) (Lc := Lc) (d := ‖u - w‖) hR hMbnn hwR hb2 hc2 hb1 hc1 haL hbL hcL
  refine le_trans hmain ?_
  apply le_of_eq; ring

end ShenWork.EWA

#print axioms ShenWork.EWA.norm_gResolver_apply_le
#print axioms ShenWork.EWA.norm_gDeriv_apply_le
#print axioms ShenWork.EWA.norm_incl_apply_le
#print axioms ShenWork.EWA.growthEWA_lipschitz
#print axioms ShenWork.EWA.vFieldEWA_lipschitz
#print axioms ShenWork.EWA.vxEWA_lipschitz
#print axioms ShenWork.EWA.vdEWA_lipschitz
#print axioms ShenWork.EWA.chemFluxEWA_lipschitz
