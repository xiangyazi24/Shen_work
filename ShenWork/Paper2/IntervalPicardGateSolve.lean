/-
  ShenWork/Paper2/IntervalPicardGateSolve.lean

  **Final wiring, step 1–2 — the GATE numerics.**

  The `UniformWiring`/cone closure carries the explicit smallness hypothesis
  `GateCondition p M A₂ T` (`IntervalPicardIterateUniform`):

      ∀ t, 0 < t → t ≤ T →
        homWeightBound M t
          + duhamelGainConst·(t/2)^{1/4}·Benv p M A₂ t
        ≤ A₂ / t²

  This file proves the gate is SOLVABLE: for every regime `p` (with `1 ≤ α`) and
  every `M ≥ 0` there is a constant `A₂ ≥ 0` and a horizon `0 < Tgate ≤ 1` with
  `GateCondition p M A₂ Tgate`.  It also records the trivial horizon-monotonicity
  `GateCondition.mono` (the gate is downward-closed in `T`, since `T` appears only
  as the upper bound of the quantifier).

  ## The smallness calculus

  Multiplying through by `t² > 0`, the two LHS pieces are controlled as follows on
  `(0, 1]`:

    * **homogeneous** `homWeightBound M t = (32 M /(e π²))·(1/t²)`, so it is at most
      `(A₂/2)/t²` as soon as `A₂ ≥ 64 M /(e π²)` — NO smallness needed.

    * **Duhamel self-coupling** `Cgain·(t/2)^{1/4}·Benv`.  On `(0,1]` we bound
      `Benv p M A₂ t ≤ (Q_M + Q_A·A₂)/t²` with explicit, `t`-free constants
      `Q_M, Q_A ≥ 0` (the `G1²` piece contributes `Q_M`, the `G2 = 4A₂/(t/2)²`
      piece contributes `Q_A·A₂`).  Hence the Duhamel term is
      `≤ Cgain·(t/2)^{1/4}·(Q_M+Q_A·A₂)/t²`.  Choosing `A₂` also `≥ 4·Cgain·Q_M`
      and `Tgate` small enough that `Cgain·(Tgate/2)^{1/4}·Q_A ≤ 1/4`, the Duhamel
      term is `≤ (A₂/2)/t²` — the `A₂` in the dominant `Q_A·A₂` piece CANCELS, which
      is exactly the self-coupling closure.

  Summing, the gate holds.  The numeric constant `A₂` is an internal bootstrap
  constant chosen here (NOT threaded through any public statement).

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.  New file only.
-/
import ShenWork.Paper2.IntervalPicardIterateUniform

open MeasureTheory Filter Topology
open ShenWork.IntervalHomogeneousQuantBound (eigExpWeight)
open ShenWork.IntervalPicardIterateTimeC1 (duhamelGainConst duhamelGainConst_nonneg)
open ShenWork.IntervalPicardIterateSourceC1 (iterateSourceEnvelopeConst)
open ShenWork.IntervalLogisticSourceQuantBound (B_log)
open ShenWork.HeatKernelGradientEstimates (heatGradientLinftyLinftyConstant
  heatGradientLinftyLinftyConstant_nonneg)
open ShenWork.IntervalPicardIterateUniform
  (CL CL_nonneg G1profile G2profile Benv homWeightBound GateCondition)

noncomputable section

namespace ShenWork.IntervalPicardGateSolve

/-! ## §1 — Horizon monotonicity of the gate. -/

/-- **`GateCondition.mono`.**  The gate is downward-closed in the horizon `T`: a
gate on `T₂` restricts to any smaller `T₁ ≤ T₂`.  `T` appears only as the upper
bound `t ≤ T` of the quantifier; `homWeightBound`/`Benv` depend on `t`, not `T`. -/
theorem GateCondition.mono
    {p : CM2Params} {M A₂ T₁ T₂ : ℝ}
    (hgate : GateCondition p M A₂ T₂) (hT : T₁ ≤ T₂) :
    GateCondition p M A₂ T₁ :=
  fun t ht htT₁ => hgate t ht (le_trans htT₁ hT)

/-! ## §2 — The explicit envelope bound `Benv ≤ (Q_M + Q_A·A₂)/t²` on `(0,1]`. -/

/-- The `t`-free constant `G1c` with `G1profile p M (t/2) ≤ G1c / t` on `(0,1]`.
`G1c := √2·Cg·(M + CL p M)`. -/
def G1c (p : CM2Params) (M : ℝ) : ℝ :=
  Real.sqrt 2 * heatGradientLinftyLinftyConstant * (M + CL p M)

theorem G1c_nonneg {p : CM2Params} {M : ℝ} (hM : 0 ≤ M) : 0 ≤ G1c p M := by
  unfold G1c
  have hCg : 0 ≤ heatGradientLinftyLinftyConstant := heatGradientLinftyLinftyConstant_nonneg
  have hCL : 0 ≤ CL p M := CL_nonneg hM
  have h2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  positivity

/-- **`G1profile p M (t/2) ≤ G1c p M / t` on `(0,1]`.**  First term
`Cg·M/√(t/2) = √2·Cg·M/√t ≤ √2·Cg·M/t` (since `√t ≥ t` for `t ≤ 1`); second term
`Cg·2√(t/2)·CL = √2·Cg·√t·CL ≤ √2·Cg·CL ≤ √2·Cg·CL/t`. -/
theorem G1profile_half_le {p : CM2Params} {M t : ℝ} (hM : 0 ≤ M)
    (ht : 0 < t) (ht1 : t ≤ 1) :
    G1profile p M (t / 2) ≤ G1c p M / t := by
  have hCg : 0 ≤ heatGradientLinftyLinftyConstant := heatGradientLinftyLinftyConstant_nonneg
  have hCL : 0 ≤ CL p M := CL_nonneg hM
  have hτ : 0 < t / 2 := by positivity
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hsτ : 0 < Real.sqrt (t / 2) := Real.sqrt_pos.mpr hτ
  have hs2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  -- √(t/2) = √t / √2
  have hsplit : Real.sqrt (t / 2) = Real.sqrt t / Real.sqrt 2 := Real.sqrt_div ht.le 2
  -- key: √t ≥ t for 0 < t ≤ 1
  have hsqrt_ge : t ≤ Real.sqrt t := by
    rw [Real.le_sqrt ht.le ht.le]; nlinarith
  -- √t ≤ 1 for t ≤ 1
  have hsqrt_le1 : Real.sqrt t ≤ 1 := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt ht1
  unfold G1profile G1c
  -- First term: Cg/√(t/2)·M = √2·Cg·M/√t ≤ √2·Cg·M/t.
  have hT1 : heatGradientLinftyLinftyConstant / Real.sqrt (t / 2) * M
      ≤ Real.sqrt 2 * heatGradientLinftyLinftyConstant * M / t := by
    rw [hsplit]
    rw [div_div_eq_mul_div, div_mul_eq_mul_div]
    -- Cg·√2/√t·M ≤ √2·Cg·M/t  ⟺ Cg·√2·M/√t ≤ √2·Cg·M/t  ⟺ 1/√t ≤ 1/t (×nonneg)
    rw [div_le_div_iff₀ hst ht]
    have hbase : heatGradientLinftyLinftyConstant * Real.sqrt 2 * M * t
        ≤ Real.sqrt 2 * heatGradientLinftyLinftyConstant * M * Real.sqrt t := by
      have hcoef : 0 ≤ heatGradientLinftyLinftyConstant * Real.sqrt 2 * M := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hsqrt_ge hcoef]
    linarith [hbase]
  -- Second term: Cg·2√(t/2)·CL = √2·Cg·√t·CL ≤ √2·Cg·CL ≤ √2·Cg·CL/t.
  have hT2 : heatGradientLinftyLinftyConstant * (2 * Real.sqrt (t / 2)) * CL p M
      ≤ Real.sqrt 2 * heatGradientLinftyLinftyConstant * CL p M / t := by
    rw [hsplit]
    have h2eq : (2 : ℝ) / Real.sqrt 2 = Real.sqrt 2 := by
      rw [div_eq_iff (ne_of_gt hs2), Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    have hstep1 : heatGradientLinftyLinftyConstant * (2 * (Real.sqrt t / Real.sqrt 2)) * CL p M
        = Real.sqrt 2 * heatGradientLinftyLinftyConstant * CL p M * Real.sqrt t := by
      rw [show 2 * (Real.sqrt t / Real.sqrt 2) = (2 / Real.sqrt 2) * Real.sqrt t by ring,
        h2eq]; ring
    rw [hstep1]
    rw [le_div_iff₀ ht]
    have hcoef : 0 ≤ Real.sqrt 2 * heatGradientLinftyLinftyConstant * CL p M := by positivity
    nlinarith [mul_le_mul_of_nonneg_left (mul_le_one₀ hsqrt_le1 ht.le ht1) hcoef,
      mul_nonneg hcoef hst.le]
  have hsum : Real.sqrt 2 * heatGradientLinftyLinftyConstant * M / t
      + Real.sqrt 2 * heatGradientLinftyLinftyConstant * CL p M / t
      = Real.sqrt 2 * heatGradientLinftyLinftyConstant * (M + CL p M) / t := by
    rw [← add_div]; ring_nf
  calc heatGradientLinftyLinftyConstant / Real.sqrt (t / 2) * M
        + heatGradientLinftyLinftyConstant * (2 * Real.sqrt (t / 2)) * CL p M
      ≤ Real.sqrt 2 * heatGradientLinftyLinftyConstant * M / t
        + Real.sqrt 2 * heatGradientLinftyLinftyConstant * CL p M / t := by linarith
    _ = Real.sqrt 2 * heatGradientLinftyLinftyConstant * (M + CL p M) / t := hsum

/-- The `t`-free envelope constants `(Q_M, Q_A)` with
`Benv p M A₂ t ≤ (Q_M p M + Q_A p M · A₂)/t²` on `(0,1]`.

`Q_M` absorbs both the `G1²` part of `2·B_log` and the constant arm `M(a+bM^α)`;
`Q_A` is the `G2 = 4A₂/t²` coefficient of `2·B_log` (the self-coupling slope). -/
def Q_M (p : CM2Params) (M : ℝ) : ℝ :=
  2 * (p.b * p.α * (1 + p.α) * M ^ (p.α - 1) * G1c p M ^ 2)
    + M * (p.a + p.b * M ^ p.α)

def Q_A (p : CM2Params) (M : ℝ) : ℝ :=
  2 * ((p.a + p.b * (1 + p.α) * M ^ p.α) * 4)

theorem Q_M_nonneg {p : CM2Params} {M : ℝ} (hM : 0 ≤ M) : 0 ≤ Q_M p M := by
  unfold Q_M
  have h1 : 0 ≤ M ^ (p.α - 1) := Real.rpow_nonneg hM _
  have h2 : 0 ≤ M ^ p.α := Real.rpow_nonneg hM _
  have hG1c : 0 ≤ G1c p M := G1c_nonneg hM
  have hαnn : 0 ≤ p.α := p.hα.le
  have hpart1 : 0 ≤ 2 * (p.b * p.α * (1 + p.α) * M ^ (p.α - 1) * G1c p M ^ 2) := by
    have := p.hb; positivity
  have hpart2 : 0 ≤ M * (p.a + p.b * M ^ p.α) := by
    have := p.ha; have := p.hb; positivity
  linarith

theorem Q_A_nonneg {p : CM2Params} {M : ℝ} (hM : 0 ≤ M) : 0 ≤ Q_A p M := by
  unfold Q_A
  have h2 : 0 ≤ M ^ p.α := Real.rpow_nonneg hM _
  have hαnn : 0 ≤ p.α := p.hα.le
  have := p.ha; have := p.hb; positivity

/-- **The envelope bound.**  On `(0,1]`, with `A₂ ≥ 0` and `1 ≤ α`,
`Benv p M A₂ t ≤ (Q_M p M + Q_A p M · A₂) / t²`. -/
theorem Benv_le {p : CM2Params} {M A₂ t : ℝ} (hM : 0 ≤ M) (hA₂ : 0 ≤ A₂)
    (hα : 1 ≤ p.α) (ht : 0 < t) (ht1 : t ≤ 1) :
    Benv p M A₂ t ≤ (Q_M p M + Q_A p M * A₂) / t ^ 2 := by
  have ht2 : (0:ℝ) < t ^ 2 := by positivity
  set G1 := G1profile p M (t / 2) with hG1def
  set G2 := G2profile A₂ (t / 2) with hG2def
  have hG1nn : 0 ≤ G1 :=
    ShenWork.IntervalPicardIterateUniform.G1profile_nonneg hM (by positivity)
  have hG2nn : 0 ≤ G2 := by
    rw [hG2def]; unfold G2profile
    apply div_nonneg hA₂; positivity
  -- G1 ≤ G1c/t, hence G1² ≤ G1c²/t²
  have hG1le : G1 ≤ G1c p M / t := G1profile_half_le hM ht ht1
  have hG1c_nn : 0 ≤ G1c p M := G1c_nonneg hM
  have hG1sq : G1 ^ 2 ≤ G1c p M ^ 2 / t ^ 2 := by
    have h := mul_le_mul hG1le hG1le hG1nn (by positivity)
    calc G1 ^ 2 = G1 * G1 := by ring
      _ ≤ (G1c p M / t) * (G1c p M / t) := h
      _ = G1c p M ^ 2 / t ^ 2 := by rw [div_mul_div_comm]; ring
  -- G2 = A₂/(t/2)² = 4A₂/t²
  have hG2eq : G2 = 4 * A₂ / t ^ 2 := by
    rw [hG2def]; unfold G2profile; rw [div_pow]; ring_nf
  -- B_log bound: term-by-term
  have hMα1 : 0 ≤ M ^ (p.α - 1) := Real.rpow_nonneg hM _
  have hMα : 0 ≤ M ^ p.α := Real.rpow_nonneg hM _
  have h1α : (0:ℝ) ≤ 1 + p.α := by linarith [p.hα.le]
  have hcoef1 : 0 ≤ p.b * p.α * (1 + p.α) * M ^ (p.α - 1) :=
    mul_nonneg (mul_nonneg (mul_nonneg p.hb p.hα.le) h1α) hMα1
  have hcoef2 : 0 ≤ p.a + p.b * (1 + p.α) * M ^ p.α :=
    add_nonneg p.ha (mul_nonneg (mul_nonneg p.hb h1α) hMα)
  -- B_log = c1·G1² + c2·G2 with G1² ≤ G1c²/t², G2 = 4A₂/t².  So
  -- B_log·t² ≤ c1·G1c² + c2·4·A₂.
  have hBlog_t2 : B_log p.a p.b p.α M G1 G2 * t ^ 2
      ≤ p.b * p.α * (1 + p.α) * M ^ (p.α - 1) * G1c p M ^ 2
          + (p.a + p.b * (1 + p.α) * M ^ p.α) * 4 * A₂ := by
    unfold B_log
    have hg1sq_t2 : G1 ^ 2 * t ^ 2 ≤ G1c p M ^ 2 := (le_div_iff₀ ht2).mp hG1sq
    have hg2_t2 : G2 * t ^ 2 = 4 * A₂ := by
      rw [hG2eq]; field_simp
    have hexpand : (p.b * p.α * (1 + p.α) * M ^ (p.α - 1) * G1 ^ 2
          + (p.a + p.b * (1 + p.α) * M ^ p.α) * G2) * t ^ 2
        = p.b * p.α * (1 + p.α) * M ^ (p.α - 1) * (G1 ^ 2 * t ^ 2)
          + (p.a + p.b * (1 + p.α) * M ^ p.α) * (G2 * t ^ 2) := by ring
    rw [hexpand, hg2_t2]
    have h1 : p.b * p.α * (1 + p.α) * M ^ (p.α - 1) * (G1 ^ 2 * t ^ 2)
        ≤ p.b * p.α * (1 + p.α) * M ^ (p.α - 1) * G1c p M ^ 2 :=
      mul_le_mul_of_nonneg_left hg1sq_t2 hcoef1
    have h2 : (p.a + p.b * (1 + p.α) * M ^ p.α) * (4 * A₂)
        = (p.a + p.b * (1 + p.α) * M ^ p.α) * 4 * A₂ := by ring
    linarith [h1, h2.le, h2.ge]
  -- Assemble through the max, comparing in `t²`-cleared form.
  have hMconst_nn : 0 ≤ M * (p.a + p.b * M ^ p.α) := by
    have := p.ha; have := p.hb; positivity
  have ht2le1 : t ^ 2 ≤ 1 := by nlinarith
  unfold Benv iterateSourceEnvelopeConst
  rw [← hG1def, ← hG2def]
  refine max_le ?_ ?_
  · -- 2·B_log ≤ (Q_M + Q_A·A₂)/t²
    rw [le_div_iff₀ ht2]
    have h2blog : (2 : ℝ) * B_log p.a p.b p.α M G1 G2 * t ^ 2
        ≤ 2 * (p.b * p.α * (1 + p.α) * M ^ (p.α - 1) * G1c p M ^ 2
            + (p.a + p.b * (1 + p.α) * M ^ p.α) * 4 * A₂) := by
      have := mul_le_mul_of_nonneg_left hBlog_t2 (by norm_num : (0:ℝ) ≤ 2)
      nlinarith [this]
    unfold Q_M Q_A; nlinarith [h2blog, hMconst_nn]
  · -- M(a+bM^α) ≤ (Q_M + Q_A·A₂)/t²
    rw [le_div_iff₀ ht2]
    unfold Q_M Q_A
    have hG1csq : 0 ≤ 2 * (p.b * p.α * (1 + p.α) * M ^ (p.α - 1) * G1c p M ^ 2) := by
      have hαnn : 0 ≤ p.α := p.hα.le; have := p.hb; positivity
    have hQA : 0 ≤ 2 * ((p.a + p.b * (1 + p.α) * M ^ p.α) * 4) * A₂ :=
      mul_nonneg (by have := p.ha; have := p.hb; have hαnn : 0 ≤ p.α := p.hα.le; positivity) hA₂
    nlinarith [hG1csq, hQA, mul_le_of_le_one_right hMconst_nn ht2le1]

/-! ## §3 — The gate solver. -/

/-- **`exists_gate_solution`.**  For every regime `p` with `1 ≤ p.α` and every
`M ≥ 0`, there is an internal bootstrap constant `A₂ ≥ 0` and a horizon
`0 < Tgate ≤ 1` solving the gate `GateCondition p M A₂ Tgate`.

`A₂` is chosen `≥ 64 M/(eπ²)` (homogeneous closure), `≥ 1`, and `≥ 4·Cgain·Q_M`
(constant part of the Duhamel self-coupling); `Tgate` is shrunk so that
`Cgain·(Tgate/2)^{1/4}·Q_A ≤ 1/4` (the `A₂`-coefficient of the self-coupling). -/
theorem exists_gate_solution
    (p : CM2Params) {M : ℝ} (hM : 0 ≤ M) (hα : 1 ≤ p.α) :
    ∃ A₂ Tgate : ℝ,
      0 ≤ A₂ ∧ 0 < Tgate ∧ Tgate ≤ 1 ∧ GateCondition p M A₂ Tgate := by
  have hQMnn : 0 ≤ Q_M p M := Q_M_nonneg hM
  have hQAnn : 0 ≤ Q_A p M := Q_A_nonneg hM
  have hCg_nn : 0 ≤ duhamelGainConst := duhamelGainConst_nonneg
  -- the constant `A₂`
  set hpi : (0:ℝ) < Real.exp 1 * Real.pi ^ 2 := by positivity with hpi_def
  set A₂ : ℝ := max (64 * M / (Real.exp 1 * Real.pi ^ 2)) (max 1 (4 * duhamelGainConst * Q_M p M))
    with hA₂def
  have hA₂_hom : 64 * M / (Real.exp 1 * Real.pi ^ 2) ≤ A₂ := le_max_left _ _
  have hA₂_one : (1:ℝ) ≤ A₂ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hA₂_QM : 4 * duhamelGainConst * Q_M p M ≤ A₂ :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hA₂nn : 0 ≤ A₂ := le_trans (by norm_num) hA₂_one
  -- the shrink scale `s = 1/(4·Cgain·Q_A + 1) ∈ (0,1]`
  set den : ℝ := 4 * duhamelGainConst * Q_A p M + 1 with hden_def
  have hden_pos : 0 < den := by
    rw [hden_def]; have : 0 ≤ 4 * duhamelGainConst * Q_A p M := by positivity
    linarith
  have hden_ge1 : 1 ≤ den := by rw [hden_def]; nlinarith [hCg_nn, hQAnn]
  set s : ℝ := 1 / den with hs_def
  have hs_pos : 0 < s := by rw [hs_def]; positivity
  have hs_le1 : s ≤ 1 := by rw [hs_def, div_le_one hden_pos]; linarith
  -- the horizon
  set Tgate : ℝ := min 1 (2 * s ^ 4) with hTgate_def
  have hs4_pos : 0 < s ^ 4 := by positivity
  have hTgate_pos : 0 < Tgate := by
    rw [hTgate_def]; exact lt_min (by norm_num) (by positivity)
  have hTgate_le1 : Tgate ≤ 1 := min_le_left _ _
  have hTgate_le2 : Tgate ≤ 2 * s ^ 4 := min_le_right _ _
  refine ⟨A₂, Tgate, hA₂nn, hTgate_pos, hTgate_le1, ?_⟩
  intro t ht htT
  have ht1 : t ≤ 1 := le_trans htT hTgate_le1
  have ht2 : (0:ℝ) < t ^ 2 := by positivity
  -- term 1 (homogeneous): homWeightBound M t = (32M/(eπ²))/t² ≤ (A₂/2)/t².
  have hhom_eq : homWeightBound M t = (32 * M / (Real.exp 1 * Real.pi ^ 2)) / t ^ 2 := by
    unfold homWeightBound
    rw [div_pow]
    field_simp
    ring
  have hhom_le : homWeightBound M t ≤ (A₂ / 2) / t ^ 2 := by
    rw [hhom_eq]
    rw [div_le_div_iff_of_pos_right ht2]
    -- 32M/(eπ²) ≤ A₂/2  ⟺  64M/(eπ²) ≤ A₂
    have : 32 * M / (Real.exp 1 * Real.pi ^ 2) = (64 * M / (Real.exp 1 * Real.pi ^ 2)) / 2 := by
      rw [div_div]; ring_nf
    rw [this]; linarith [hA₂_hom]
  -- term 2 (Duhamel self-coupling): bound Benv, then the (t/2)^{1/4} factor.
  have hτ : 0 < t / 2 := by positivity
  have hτ_le1 : t / 2 ≤ 1 := by linarith
  -- (t/2)^{1/4} ≤ s
  have hrpow_le_s : (t / 2) ^ ((1 : ℝ) / 4) ≤ s := by
    have hts4 : t / 2 ≤ s ^ 4 := by linarith [hTgate_le2]
    calc (t / 2) ^ ((1 : ℝ) / 4)
        ≤ (s ^ 4) ^ ((1 : ℝ) / 4) :=
          Real.rpow_le_rpow hτ.le hts4 (by norm_num)
      _ = s := by
          rw [← Real.rpow_natCast s 4, ← Real.rpow_mul hs_pos.le]
          norm_num
  have hrpow_nn : 0 ≤ (t / 2) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hτ.le _
  have hrpow_le1 : (t / 2) ^ ((1 : ℝ) / 4) ≤ 1 := le_trans hrpow_le_s hs_le1
  -- Benv ≤ (Q_M + Q_A·A₂)/t²
  have hBenv : Benv p M A₂ t ≤ (Q_M p M + Q_A p M * A₂) / t ^ 2 :=
    Benv_le hM hA₂nn hα ht ht1
  -- the Duhamel product ≤ (A₂/2)/t²
  have hduh_le : duhamelGainConst * (t / 2) ^ ((1 : ℝ) / 4) * Benv p M A₂ t
      ≤ (A₂ / 2) / t ^ 2 := by
    -- ≤ Cgain·rpow·(Q_M + Q_A·A₂)/t²
    have hstep1 : duhamelGainConst * (t / 2) ^ ((1 : ℝ) / 4) * Benv p M A₂ t
        ≤ duhamelGainConst * (t / 2) ^ ((1 : ℝ) / 4) * ((Q_M p M + Q_A p M * A₂) / t ^ 2) := by
      apply mul_le_mul_of_nonneg_left hBenv
      exact mul_nonneg hCg_nn hrpow_nn
    refine hstep1.trans ?_
    rw [← mul_div_assoc, div_le_div_iff_of_pos_right ht2]
    -- Cgain·rpow·(Q_M + Q_A·A₂) ≤ A₂/2.  Split:
    -- (a) Cgain·rpow·Q_M ≤ Cgain·Q_M ≤ A₂/4   (rpow ≤ 1, A₂ ≥ 4 Cgain Q_M)
    -- (b) Cgain·rpow·Q_A·A₂ ≤ (Cgain·Q_A·s)·A₂ ≤ (1/4)·A₂   (rpow ≤ s)
    have hpartM : duhamelGainConst * (t / 2) ^ ((1 : ℝ) / 4) * Q_M p M ≤ A₂ / 4 := by
      have h1 : duhamelGainConst * (t / 2) ^ ((1 : ℝ) / 4) * Q_M p M
          ≤ duhamelGainConst * 1 * Q_M p M := by
        apply mul_le_mul_of_nonneg_right _ hQMnn
        exact mul_le_mul_of_nonneg_left hrpow_le1 hCg_nn
      have h2 : duhamelGainConst * 1 * Q_M p M = duhamelGainConst * Q_M p M := by ring
      rw [h2] at h1; linarith [hA₂_QM]
    have hpartA : duhamelGainConst * (t / 2) ^ ((1 : ℝ) / 4) * (Q_A p M * A₂) ≤ A₂ / 4 := by
      -- Cgain·rpow·Q_A ≤ Cgain·s·Q_A ≤ 1/4
      have hcoef : duhamelGainConst * (t / 2) ^ ((1 : ℝ) / 4) * Q_A p M ≤ 1 / 4 := by
        have h1 : duhamelGainConst * (t / 2) ^ ((1 : ℝ) / 4) * Q_A p M
            ≤ duhamelGainConst * s * Q_A p M := by
          apply mul_le_mul_of_nonneg_right _ hQAnn
          exact mul_le_mul_of_nonneg_left hrpow_le_s hCg_nn
        -- Cgain·s·Q_A = Cgain·Q_A/den ≤ 1/4  since 4·Cgain·Q_A ≤ den
        have h2 : duhamelGainConst * s * Q_A p M = (duhamelGainConst * Q_A p M) / den := by
          rw [hs_def]; ring
        rw [h2] at h1
        refine h1.trans ?_
        rw [div_le_iff₀ hden_pos]
        rw [hden_def]; nlinarith [hCg_nn, hQAnn]
      -- multiply by A₂ ≥ 0
      have hA : duhamelGainConst * (t / 2) ^ ((1 : ℝ) / 4) * (Q_A p M * A₂)
          = (duhamelGainConst * (t / 2) ^ ((1 : ℝ) / 4) * Q_A p M) * A₂ := by ring
      rw [hA]
      calc (duhamelGainConst * (t / 2) ^ ((1 : ℝ) / 4) * Q_A p M) * A₂
          ≤ (1 / 4) * A₂ := mul_le_mul_of_nonneg_right hcoef hA₂nn
        _ = A₂ / 4 := by ring
    -- combine
    have hexpand : duhamelGainConst * (t / 2) ^ ((1 : ℝ) / 4) * (Q_M p M + Q_A p M * A₂)
        = duhamelGainConst * (t / 2) ^ ((1 : ℝ) / 4) * Q_M p M
          + duhamelGainConst * (t / 2) ^ ((1 : ℝ) / 4) * (Q_A p M * A₂) := by ring
    rw [hexpand]; linarith [hpartM, hpartA]
  -- sum the two pieces.
  have hsum : (A₂ / 2) / t ^ 2 + (A₂ / 2) / t ^ 2 = A₂ / t ^ 2 := by
    rw [← add_div]; ring_nf
  calc homWeightBound M t + duhamelGainConst * (t / 2) ^ ((1 : ℝ) / 4) * Benv p M A₂ t
      ≤ (A₂ / 2) / t ^ 2 + (A₂ / 2) / t ^ 2 := by linarith [hhom_le, hduh_le]
    _ = A₂ / t ^ 2 := hsum

end ShenWork.IntervalPicardGateSolve
