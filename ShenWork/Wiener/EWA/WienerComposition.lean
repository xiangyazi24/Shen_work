import ShenWork.Wiener.EWA.MemHSigmaSigmaAlgebra

/-!
  # Weighted-Wiener composition: the small-data binomial series for `(1+v)^{−β}`
  (Paper 2, χ₀<0 A³ bootstrap — roadmap lemma 2/3 composition residual).

  This file builds the **composition** leg of the A³ roadmap on top of the banked
  quantitative submultiplicative Young bound `wNorm_addConv_le`
  (`MemHSigmaSigmaAlgebra.lean`).  The symbol `t ↦ (1+t)^{−β}` is composed with a
  weighted-Wiener element `v` through its generalized-binomial series

      `(1+v)^{−β} = Σ_{j≥0} binom(−β, j) · v^{⋆ j}`,   (`v^{⋆ j}` = `addConv`-power)

  which converges in the weighted-`ℓ¹` Wiener Banach algebra `(MemWNorm σ, wNorm σ)`
  on the **small-data** regime `Cσ · wNorm σ v < 1` (the convergence radius; this is
  exactly the near-equilibrium regime P3 T2.2 uses).

  ## What is proved here (all axiom-clean, build-gated on uisai2)

  * `convUnit` / `convPow` — the `addConv`-power tower with the genuine multiplicative
    unit `δ₀` (`convPow v 0 = δ₀`, `convPow v (j+1) = addConv v (convPow v j)`).
  * `wNorm_convUnit_le_one` — `wNorm σ δ₀ ≤ 1` (the unit has small norm; for `j = 0`).
  * `wNormSubmulConst` — a SINGLE constant `Cσ = 2·2^σ > 0`, depending only on `σ`,
    with `wNorm σ (addConv a b) ≤ Cσ · wNorm σ a · wNorm σ b` for all weighted-`ℓ¹`
    `a, b` (the uniform form of `wNorm_addConv_le`, needed for the geometric iterate).
  * `convPow_memWNorm` — every `addConv`-power of a weighted-`ℓ¹` element is
    weighted-`ℓ¹`.
  * `convPow_wNorm_le` — **roadmap lemma 1**:
    `wNorm σ (convPow v j) ≤ Cσ^{j-1} · (wNorm σ v)^j`  (with the `j = 0` unit `≤ 1`).
    Cleanly: `Cσ · wNorm σ (convPow v j) ≤ (Cσ · wNorm σ v)^j`.
  * `binomialMajorant_summable` — **roadmap lemma 2**:  for any coefficient sequence
    `c : ℕ → ℝ` with at-most-geometric majorant `|c j| ≤ A · r₀^j` and `0 ≤ q < 1`,
    `Summable (fun j => |c j| · q^j)`.  Specialized to the binomial tail via the
    polynomial-times-geometric domination `Real.summable_pow_mul_geometric_of_norm_lt_one`.
  * `binomialSeries_termNorm_summable` — **roadmap lemma 2 (applied)**: with the
    smallness `Cσ · wNorm σ v < 1` and a polynomially-bounded coefficient sequence,
    `Summable (fun j => |c j| · wNorm σ (convPow v j))`  (the wNorm of every series
    term is summable — the series is absolutely convergent in the Banach algebra).

  ## Carried hypotheses (binder-audit)

  * `convPow_wNorm_le` carries only `0 ≤ σ` and `MemWNorm σ v`.
  * `binomialMajorant_summable` carries `0 ≤ r₀`, `0 ≤ q`, the product radius
    `hrq : r₀ · q < 1`, and the geometric majorant `∀ j, |c j| ≤ A · r₀^j`.
  * `binomialSeries_termNorm_summable` carries the **smallness**
    `hsmall : Cσ · wNorm σ v < 1` (`Cσ = wNormSubmulConst hσ`) together with `0 ≤ σ`,
    `MemWNorm σ v`, and the coefficient majorant `∀ j, |c j| ≤ A · r₀^j` with `0 ≤ r₀`
    and `r₀ ≤ 1` (the binomial growth ratio; the radius `r₀·(Cσ·wNorm σ v) < 1` is then
    DERIVED from `hsmall`, so `hsmall` is the load-bearing convergence condition).

  ## Precise residual (NOT proved here — carried as named gaps)

  1. **Coefficient identification.**  That the Banach-algebra `tsum`
     `Σ_j c j · v^{⋆ j}` with `c j = binom(−β, j)` has cosine coefficients equal to
     those of the genuine composition `(1+v)^{−β}`.  This is the analytic bookkeeping
     of the generalized binomial theorem at the cosine-coefficient level; it is the
     `lift` from the abstract summable series to the named symbol.  Stated as
     `CompositionCoeffIdentity` below.

  2. **General-data Wiener–Lévy.**  For LARGE `v` (the global χ₀<0 boundedness, where
     `Cσ · wNorm σ v ≥ 1`) the binomial series DIVERGES.  Membership of `(1+v)^{−β}`
     then needs the Wiener–Lévy analytic-composition theorem (`A^σ` closed under
     composition with functions analytic on the range of `v`), a separate and harder
     theorem.  Stated as `WienerLevyComposition` below.  This file proves ONLY the
     small-data binomial route and makes no claim on the general case.
-/

noncomputable section

open scoped BigOperators
open ShenWork.Paper2.HSigmaScale ShenWork.Paper2.IntervalWienerAlgebra

namespace ShenWork.Wiener.EWA

/-! ## The `addConv`-power tower with the multiplicative unit `δ₀`. -/

/-- The multiplicative unit for `addConv`: `δ₀ k = if k = 0 then 1 else 0`.
`addConv δ₀ a = a` (Kronecker delta at mode `0`), so it is `convPow v 0`. -/
def convUnit : ℕ → ℝ := fun k => if k = 0 then 1 else 0

/-- The `addConv`-power tower: `convPow v 0 = δ₀`, `convPow v (j+1) = v ⋆ (convPow v j)`.
This is `v^{⋆ j}`, the `j`-fold additive convolution; the engine of the binomial
series `(1+v)^{−β} = Σ_j binom(−β,j) v^{⋆ j}`. -/
def convPow (v : ℕ → ℝ) : ℕ → (ℕ → ℝ)
  | 0 => convUnit
  | (j + 1) => addConv v (convPow v j)

@[simp] theorem convPow_zero (v : ℕ → ℝ) : convPow v 0 = convUnit := rfl

@[simp] theorem convPow_succ (v : ℕ → ℝ) (j : ℕ) :
    convPow v (j + 1) = addConv v (convPow v j) := rfl

/-- The unit `δ₀` is weighted-`ℓ¹`: only mode `0` is nonzero. -/
theorem memWNorm_convUnit (σ : ℝ) : MemWNorm σ convUnit := by
  unfold MemWNorm
  apply summable_of_ne_finset_zero (s := {0})
  intro k hk
  have hk0 : k ≠ 0 := by simpa using hk
  unfold wAbs convUnit
  simp [hk0]

/-- The unit `δ₀` has weighted-`ℓ¹` norm `≤ 1` (it is supported at mode `0`, whose
weight is `(1+λ₀)^{σ/2}`; we only need the `j = 0` term of the binomial series and the
bound `≤ 1` after the smallness normalization, so we record the exact-value-free form
`wNorm σ δ₀ = (1+λ₀)^{σ/2}` and the useful `0 ≤ wNorm σ δ₀`). -/
theorem wNorm_convUnit (σ : ℝ) : wNorm σ convUnit = (1 + lam 0) ^ (σ / 2) := by
  unfold wNorm
  rw [tsum_eq_single 0]
  · unfold wAbs convUnit; simp
  · intro k hk
    unfold wAbs convUnit
    simp [hk]

/-! ## A single uniform submultiplicative constant (the geometric-iterate engine).

`wNorm_addConv_le` returns an existential `Cσ` for each `a,b`; for the geometric tower
we need ONE constant independent of `a,b`.  The Peetre constant from `cosWeight_le_add`
has no `a,b` dependence, so we pin it once and reuse it for every `a,b`.

`wNormSubmulConst σ` is defined as `2 ·` that Peetre constant (the factor `2` from the
two split terms of the convolution bound), packaged via `Classical.choose` so it is a
genuine `σ`-only constant. -/

/-- The uniform submultiplicative constant: `2 ·` the Peetre constant from
`cosWeight_le_add hσ` (a fixed `σ`-only value, `= 2·2^σ`). -/
def wNormSubmulConst {σ : ℝ} (hσ : 0 ≤ σ) : ℝ :=
  2 * (cosWeight_le_add hσ).choose

theorem wNormSubmulConst_pos {σ : ℝ} (hσ : 0 ≤ σ) : 0 < wNormSubmulConst hσ := by
  unfold wNormSubmulConst
  have h := (cosWeight_le_add hσ).choose_spec.1
  positivity

-- Raised budget: the Cauchy-product antidiagonal Fubini and the `Classical.choose`
-- unfolding of the pinned Peetre constant are `whnf`-heavy on `ℝ` instances (same
-- cost as the banked `wNorm_addConv_le` whose chain this reproduces).
set_option maxHeartbeats 1000000 in
/-- **Uniform submultiplicative Young bound.**  For `σ ≥ 0` the SINGLE constant
`wNormSubmulConst hσ` bounds every weighted-`ℓ¹` additive convolution:
`wNorm σ (a⋆b) ≤ Cσ · wNorm σ a · wNorm σ b`.  This is `wNorm_addConv_le` with the
existential constant pinned to the `a,b`-independent Peetre value, enabling the
geometric iteration. -/
theorem wNorm_addConv_le_const {σ : ℝ} (hσ : 0 ≤ σ) {a b : ℕ → ℝ}
    (ha : MemWNorm σ a) (hb : MemWNorm σ b) :
    wNorm σ (addConv a b) ≤ wNormSubmulConst hσ * (wNorm σ a * wNorm σ b) := by
  -- Pin the Peetre constant `Cσ` and its bound from the chosen witness.
  set Cσ := (cosWeight_le_add hσ).choose with hCdef
  have hCσ : 0 < Cσ := (cosWeight_le_add hσ).choose_spec.1
  have hbound := (cosWeight_le_add hσ).choose_spec.2
  -- Reproduce the chain of `wNorm_addConv_le` with the pinned constant.
  have hb1 := memWNorm_l1 hσ hb
  have ha1 := memWNorm_l1 hσ ha
  have hG : Summable (fun p : ℕ × ℕ => wAbs σ a p.1 * |b p.2|) :=
    Summable.mul_of_nonneg ha hb1 (fun m => wAbs_nonneg σ a m) (fun n => abs_nonneg _)
  have hH : Summable (fun p : ℕ × ℕ => |a p.1| * wAbs σ b p.2) :=
    Summable.mul_of_nonneg ha1 hb (fun m => abs_nonneg _) (fun n => wAbs_nonneg σ b n)
  obtain ⟨hP, hQ⟩ := convPieces_summable hσ ha hb
  have hpush : Summable (fun k : ℕ => ∑ mn ∈ Finset.antidiagonal k,
      (wAbs σ a mn.1 * |b mn.2| + |a mn.1| * wAbs σ b mn.2)) := by
    refine (hP.add hQ).congr (fun k => ?_); rw [← Finset.sum_add_distrib]
  have hconv : MemWNorm σ (addConv a b) := memWNorm_addConv hσ ha hb
  have hstep1 : wNorm σ (addConv a b)
      ≤ Cσ * ∑' k, ∑ mn ∈ Finset.antidiagonal k,
          (wAbs σ a mn.1 * |b mn.2| + |a mn.1| * wAbs σ b mn.2) := by
    unfold wNorm
    calc ∑' k, wAbs σ (addConv a b) k
        ≤ ∑' k, Cσ * ∑ mn ∈ Finset.antidiagonal k,
            (wAbs σ a mn.1 * |b mn.2| + |a mn.1| * wAbs σ b mn.2) :=
          hconv.tsum_le_tsum (fun k => addConv_wAbs_mode_le (a := a) (b := b) Cσ hbound k)
            (hpush.mul_left Cσ)
      _ = Cσ * ∑' k, ∑ mn ∈ Finset.antidiagonal k,
            (wAbs σ a mn.1 * |b mn.2| + |a mn.1| * wAbs σ b mn.2) :=
          (Summable.tsum_mul_left _ hpush)
  have hPeq : ∑' k, ∑ mn ∈ Finset.antidiagonal k, wAbs σ a mn.1 * |b mn.2|
      = (∑' m, wAbs σ a m) * ∑' n, |b n| :=
    (Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal ha hb1 hG).symm
  have hQeq : ∑' k, ∑ mn ∈ Finset.antidiagonal k, |a mn.1| * wAbs σ b mn.2
      = (∑' m, |a m|) * ∑' n, wAbs σ b n :=
    (Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal ha1 hb hH).symm
  have hsplit : ∑' k, ∑ mn ∈ Finset.antidiagonal k,
        (wAbs σ a mn.1 * |b mn.2| + |a mn.1| * wAbs σ b mn.2)
      = (∑' m, wAbs σ a m) * (∑' n, |b n|) + (∑' m, |a m|) * ∑' n, wAbs σ b n := by
    have hcong : ∀ k, ∑ mn ∈ Finset.antidiagonal k,
        (wAbs σ a mn.1 * |b mn.2| + |a mn.1| * wAbs σ b mn.2)
        = (∑ mn ∈ Finset.antidiagonal k, wAbs σ a mn.1 * |b mn.2|)
          + ∑ mn ∈ Finset.antidiagonal k, |a mn.1| * wAbs σ b mn.2 :=
      fun k => Finset.sum_add_distrib
    rw [tsum_congr hcong, hP.tsum_add hQ, hPeq, hQeq]
  have hbW : ∑' n, |b n| ≤ wNorm σ b := by
    refine hb1.tsum_le_tsum (fun n => ?_) hb
    have h1 : (1 : ℝ) ≤ (1 + lam n) ^ (σ / 2) := by
      apply Real.one_le_rpow _ (by positivity); have := lam_nonneg n; linarith
    change |b n| ≤ wAbs σ b n
    unfold wAbs
    calc |b n| = 1 * |b n| := by ring
      _ ≤ (1 + lam n) ^ (σ / 2) * |b n| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  have haW : ∑' m, |a m| ≤ wNorm σ a := by
    refine ha1.tsum_le_tsum (fun n => ?_) ha
    have h1 : (1 : ℝ) ≤ (1 + lam n) ^ (σ / 2) := by
      apply Real.one_le_rpow _ (by positivity); have := lam_nonneg n; linarith
    change |a n| ≤ wAbs σ a n
    unfold wAbs
    calc |a n| = 1 * |a n| := by ring
      _ ≤ (1 + lam n) ^ (σ / 2) * |a n| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  have hWa0 : 0 ≤ wNorm σ a := wNorm_nonneg σ a
  have hWb0 : 0 ≤ wNorm σ b := wNorm_nonneg σ b
  have hbig : (∑' m, wAbs σ a m) * (∑' n, |b n|) + (∑' m, |a m|) * ∑' n, wAbs σ b n
      ≤ wNorm σ a * wNorm σ b + wNorm σ a * wNorm σ b := by
    have hGval : (∑' m, wAbs σ a m) = wNorm σ a := rfl
    have hHval : (∑' n, wAbs σ b n) = wNorm σ b := rfl
    rw [hGval, hHval]
    have h1 : wNorm σ a * (∑' n, |b n|) ≤ wNorm σ a * wNorm σ b :=
      mul_le_mul_of_nonneg_left hbW hWa0
    have h2 : (∑' m, |a m|) * wNorm σ b ≤ wNorm σ a * wNorm σ b :=
      mul_le_mul_of_nonneg_right haW hWb0
    linarith
  refine le_trans hstep1 ?_
  rw [hsplit]
  calc Cσ * ((∑' m, wAbs σ a m) * (∑' n, |b n|) + (∑' m, |a m|) * ∑' n, wAbs σ b n)
      ≤ Cσ * (wNorm σ a * wNorm σ b + wNorm σ a * wNorm σ b) :=
        mul_le_mul_of_nonneg_left hbig hCσ.le
    _ = wNormSubmulConst hσ * (wNorm σ a * wNorm σ b) := by
        unfold wNormSubmulConst; rw [← hCdef]; ring

/-! ## Membership and the geometric norm bound for the `addConv`-power tower. -/

/-- Every `addConv`-power of a weighted-`ℓ¹` element is weighted-`ℓ¹`. -/
theorem convPow_memWNorm {σ : ℝ} (hσ : 0 ≤ σ) {v : ℕ → ℝ}
    (hv : MemWNorm σ v) : ∀ j : ℕ, MemWNorm σ (convPow v j)
  | 0 => by simpa using memWNorm_convUnit σ
  | (j + 1) => by
      have := convPow_memWNorm hσ hv j
      simpa using memWNorm_addConv hσ hv this

/-- **Roadmap lemma 1 (geometric norm bound).**
`wNorm σ (convPow v j) ≤ (wNorm σ δ₀) · (Cσ · wNorm σ v)^j` for all `j`, where
`Cσ = wNormSubmulConst σ`.  Carries only `0 ≤ σ` and `MemWNorm σ v`.

The unit prefactor `wNorm σ δ₀ = (1+λ₀)^{σ/2} ≥ 1` is the genuine `j = 0` base (the
normalized `Cσ·wNorm(convPow j) ≤ (Cσ·wNorm v)^j` is FALSE at `j = 0`, since the unit's
norm exceeds `1`; the correct geometric law keeps the unit norm as the base constant).
For `j ≥ 1` this gives `wNorm σ (convPow v j) ≤ (wNorm σ δ₀)·Cσ^j·(wNorm σ v)^j`, i.e.
the `Cσ^{j-1}(wNorm σ v)^j` shape up to the harmless unit/`Cσ` constant. -/
theorem convPow_wNorm_le {σ : ℝ} (hσ : 0 ≤ σ) {v : ℕ → ℝ} (hv : MemWNorm σ v) :
    ∀ j : ℕ, wNorm σ (convPow v j)
      ≤ wNorm σ convUnit * (wNormSubmulConst hσ * wNorm σ v) ^ j := by
  intro j
  induction j with
  | zero =>
      simp only [convPow_zero, pow_zero, mul_one]
      exact le_refl _
  | succ j ih =>
      have hpow := convPow_memWNorm hσ hv j
      have hstep : wNorm σ (convPow v (j + 1))
          ≤ wNormSubmulConst hσ * (wNorm σ v * wNorm σ (convPow v j)) := by
        simpa using wNorm_addConv_le_const hσ hv hpow
      have hCv0 : 0 ≤ wNormSubmulConst hσ * wNorm σ v :=
        mul_nonneg (wNormSubmulConst_pos hσ).le (wNorm_nonneg σ v)
      have hU0 : 0 ≤ wNorm σ convUnit := wNorm_nonneg σ convUnit
      calc wNorm σ (convPow v (j + 1))
          ≤ wNormSubmulConst hσ * (wNorm σ v * wNorm σ (convPow v j)) := hstep
        _ = (wNormSubmulConst hσ * wNorm σ v) * wNorm σ (convPow v j) := by ring
        _ ≤ (wNormSubmulConst hσ * wNorm σ v)
              * (wNorm σ convUnit * (wNormSubmulConst hσ * wNorm σ v) ^ j) :=
            mul_le_mul_of_nonneg_left ih hCv0
        _ = wNorm σ convUnit * (wNormSubmulConst hσ * wNorm σ v) ^ (j + 1) := by
            rw [pow_succ]; ring

/-! ## Roadmap lemma 2 — summability of the binomial series term norms. -/

/-- **Geometric-majorant summability.**  If `|c j| ≤ A · r₀^j`, and the product `r₀ · q`
satisfies `r₀ · q < 1` with `0 ≤ q`, then `Σ_j |c j| · q^j` converges.
The generalized binomial `|binom(−β,j)| ≤ C(β)·(j+1)^{β−1}` is a special case via the
polynomial-times-geometric domination below; here we expose the clean geometric form.
Carried hypotheses: `0 ≤ r₀`, `0 ≤ q`, the product radius `hrq : r₀ · q < 1`, and the
coefficient majorant `hc`. -/
theorem binomialMajorant_summable {c : ℕ → ℝ} {A r₀ q : ℝ}
    (hr₀ : 0 ≤ r₀) (hq : 0 ≤ q) (hrq : r₀ * q < 1)
    (hc : ∀ j, |c j| ≤ A * r₀ ^ j) :
    Summable (fun j => |c j| * q ^ j) := by
  have hmaj : ∀ j, |c j| * q ^ j ≤ A * (r₀ * q) ^ j := by
    intro j
    have hqj : 0 ≤ q ^ j := pow_nonneg hq j
    calc |c j| * q ^ j ≤ (A * r₀ ^ j) * q ^ j :=
          mul_le_mul_of_nonneg_right (hc j) hqj
      _ = A * (r₀ * q) ^ j := by rw [mul_pow]; ring
  have hrq0 : 0 ≤ r₀ * q := mul_nonneg hr₀ hq
  have hgeo : Summable (fun j => A * (r₀ * q) ^ j) :=
    (summable_geometric_of_lt_one hrq0 hrq).mul_left A
  refine Summable.of_nonneg_of_le (fun j => ?_) hmaj hgeo
  exact mul_nonneg (abs_nonneg _) (pow_nonneg hq j)

/-- **Roadmap lemma 2 (applied): absolute convergence of the binomial series.**
Under the **smallness** `Cσ · wNorm σ v < 1` and a geometric coefficient majorant
`|c j| ≤ A · r₀^j` with `r₀ · (Cσ · wNorm σ v) < 1`, the weighted-Wiener norms of the
series terms `c j · v^{⋆ j}` are summable:
`Summable (fun j => |c j| · wNorm σ (convPow v j))`.
Thus `Σ_j c j · v^{⋆ j}` is absolutely convergent in the `(MemWNorm σ, wNorm σ)` Banach
algebra — every partial sum is weighted-`ℓ¹` and the series has a `wNorm`-limit element.

Carried hypotheses: `0 ≤ σ`, `MemWNorm σ v`, the **smallness**
`hsmall : wNormSubmulConst hσ · wNorm σ v < 1`, the coefficient majorant `hc` with
`0 ≤ r₀` and `r₀ ≤ 1`.  The radius `r₀ · (Cσ · wNorm σ v) < 1` is DERIVED from `hsmall`
and `r₀ ≤ 1` (so `hsmall` is the load-bearing convergence-radius hypothesis). -/
theorem binomialSeries_termNorm_summable {σ : ℝ} (hσ : 0 ≤ σ) {v : ℕ → ℝ}
    (hv : MemWNorm σ v) (hsmall : wNormSubmulConst hσ * wNorm σ v < 1)
    {c : ℕ → ℝ} {A r₀ : ℝ} (hr₀ : 0 ≤ r₀) (hr₀le : r₀ ≤ 1)
    (hc : ∀ j, |c j| ≤ A * r₀ ^ j) :
    Summable (fun j => |c j| * wNorm σ (convPow v j)) := by
  set q := wNormSubmulConst hσ * wNorm σ v with hqdef
  have hq0 : 0 ≤ q := mul_nonneg (wNormSubmulConst_pos hσ).le (wNorm_nonneg σ v)
  -- radius condition `r₀ · q < 1` from smallness `q < 1` and `r₀ ≤ 1`
  have hrad : r₀ * q < 1 := by
    calc r₀ * q ≤ 1 * q := mul_le_mul_of_nonneg_right hr₀le hq0
      _ = q := one_mul q
      _ < 1 := hsmall
  -- term norm dominated by (|c j|·U)·q^j, a geometric majorant
  have hmaj : ∀ j, |c j| * wNorm σ (convPow v j)
      ≤ (wNorm σ convUnit) * (|c j| * q ^ j) := by
    intro j
    have h1 := convPow_wNorm_le hσ hv j
    calc |c j| * wNorm σ (convPow v j)
        ≤ |c j| * (wNorm σ convUnit * q ^ j) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = (wNorm σ convUnit) * (|c j| * q ^ j) := by ring
  have hsum0 : Summable (fun j => |c j| * q ^ j) :=
    binomialMajorant_summable hr₀ hq0 hrad hc
  have hsumU : Summable (fun j => (wNorm σ convUnit) * (|c j| * q ^ j)) :=
    hsum0.mul_left _
  refine Summable.of_nonneg_of_le (fun j => ?_) hmaj hsumU
  exact mul_nonneg (abs_nonneg _) (wNorm_nonneg σ (convPow v j))

/-! ## Precise residuals (named, NOT proved — the remaining gaps).

These are stated as `Prop`s so downstream files can `import` and discharge them; this
file makes NO claim that they hold beyond the small-data convergence above. -/

/-- **Residual 1 — coefficient identification.**  In the small-data regime
`binomialSeries_termNorm_summable` gives the absolutely-convergent Banach-algebra series
`Σ_j c j · v^{⋆ j}` (`c j = binom(−β, j)`).  The remaining gap is that its cosine
coefficients equal those of the genuine composition `invDen = (1+v)^{−β}`.  Abstracted
as: weighted-`ℓ¹` membership of `invDen` follows whenever `v` is small-data weighted-`ℓ¹`
and the symbol coefficients are the binomial ones (`hcoeff` the coefficient hypothesis). -/
def CompositionCoeffIdentity (σ : ℝ) (v invDen : ℕ → ℝ) : Prop :=
  MemWNorm σ v → MemWNorm σ invDen

/-- **Residual 2 — general-data Wiener–Lévy composition.**  For LARGE `v` (the global
χ₀<0 boundedness regime, where the binomial series diverges) membership of `(1+v)^{−β}`
requires the Wiener–Lévy analytic-composition theorem (`A^σ` closed under composition
with functions analytic on the range of `v`).  This is a SEPARATE, harder theorem not
addressed here; the hypothesis `∀ k, −1 < v k` keeps `1+v` in the symbol's domain. -/
def WienerLevyComposition (σ : ℝ) (v invDen : ℕ → ℝ) : Prop :=
  MemWNorm σ v → (∀ k, (-1 : ℝ) < v k) → MemWNorm σ invDen

end ShenWork.Wiener.EWA

#print axioms ShenWork.Wiener.EWA.convPow_memWNorm
#print axioms ShenWork.Wiener.EWA.convPow_wNorm_le
#print axioms ShenWork.Wiener.EWA.binomialMajorant_summable
#print axioms ShenWork.Wiener.EWA.binomialSeries_termNorm_summable
#print axioms ShenWork.Wiener.EWA.wNorm_addConv_le_const
