import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Archimedean

/-!
  # Generalized-binomial-coefficient majorant bound

  The composition leg of the A³ roadmap (`WienerComposition.lean`) consumes a coefficient
  sequence `c : ℕ → ℝ` together with a geometric majorant `∀ j, |c j| ≤ A · r ^ j`.  The
  natural coefficients there are the **generalized binomial coefficients**

      `gBinom β j  :=  ∏_{i < j} (-β - i) / (i + 1)`   (`= binom(-β, j)`),

  i.e. the coefficient of `x^j` in the formal series `(1 + x)^{-β}` (here `j! = ∏_{i<j}(i+1)`
  is folded factor-by-factor into the product, so no `Nat.factorial` is needed).

  ## The bound

  `|gBinom β j| = ∏_{i<j} (β + i)/(i + 1) = binom(β + j - 1, j)` grows like `j^{β-1}/Γ(β)`,
  i.e. **polynomially** in `j` (sub-exponential).  Consequently, for **any** ratio `r > 1`
  there is a constant `A = A(β, r) ≥ 0` with `|gBinom β j| ≤ A · r ^ j` for all `j`.

  ⚠️ **The `r > 1` hypothesis is sharp and necessary.**  Since `|gBinom β j|` grows
  polynomially (e.g. `→ ∞` for `β > 1`), the bound `|gBinom β j| ≤ A · r ^ j` is FALSE for
  any `r ≤ 1`: for `r < 1` the right side `→ 0` while the left side does not, and for `r = 1`
  it would force the polynomially-growing left side to be bounded.  Hence the only
  universally-true geometric-majorant form is the `1 < r` one proved here.  The downstream
  consumer `binomialSeries_termNorm_summable` (smallness `q := Cσ · wNorm σ v < 1`) is still
  served: pick any `r ∈ (1, 1/q)` so the product radius `r · q < 1` still holds, and feed
  this `A`, `r` as the geometric majorant.

  ## Proof (elementary, axiom-clean)

  Write `g j := |gBinom β j| = ∏_{i<j} (β + i)/(i + 1) ≥ 0` with ratio
  `g (j+1) / g j = (β + j)/(j + 1) → 1`.  Fix `r > 1`.  Choose `N` with `(β+j)/(j+1) ≤ r`
  for all `j ≥ N` (Archimedean: `N ≥ (β - r)/(r - 1)`).  Then for `j ≥ N`,
  `g j ≤ (g N / r^N) · r^j`, while for `j < N`, `g j ≤ (∑_{k<N} g k)` and `1 ≤ r^j`.  The
  single constant `A := g N / r^N + ∑_{k<N} g k` dominates both regimes.
-/

noncomputable section

open scoped BigOperators

namespace ShenWork.Wiener.EWA

/-- The generalized binomial coefficient `binom(-β, j)`, the coefficient of `x^j` in the
formal series `(1 + x)^{-β}`, defined directly as the telescoping product
`∏_{i < j} (-β - i)/(i + 1)` (the `i+1` factors assemble `j!`). -/
def gBinom (β : ℝ) (j : ℕ) : ℝ :=
  ∏ i ∈ Finset.range j, (-β - (i : ℝ)) / ((i : ℝ) + 1)

/-- The all-positive companion product `g β j = ∏_{i<j} (β + i)/(i + 1)`; it equals
`|gBinom β j|`. -/
def gPos (β : ℝ) (j : ℕ) : ℝ :=
  ∏ i ∈ Finset.range j, (β + (i : ℝ)) / ((i : ℝ) + 1)

@[simp] theorem gBinom_zero (β : ℝ) : gBinom β 0 = 1 := by simp [gBinom]

@[simp] theorem gPos_zero (β : ℝ) : gPos β 0 = 1 := by simp [gPos]

theorem gBinom_succ (β : ℝ) (j : ℕ) :
    gBinom β (j + 1) = gBinom β j * ((-β - (j : ℝ)) / ((j : ℝ) + 1)) := by
  rw [gBinom, gBinom, Finset.prod_range_succ]

theorem gPos_succ (β : ℝ) (j : ℕ) :
    gPos β (j + 1) = gPos β j * ((β + (j : ℝ)) / ((j : ℝ) + 1)) := by
  rw [gPos, gPos, Finset.prod_range_succ]

/-- Each factor of `gPos` is nonnegative when `β ≥ 0`, hence `gPos β j ≥ 0`. -/
theorem gPos_nonneg {β : ℝ} (hβ : 0 ≤ β) (j : ℕ) : 0 ≤ gPos β j := by
  refine Finset.prod_nonneg ?_
  intro i _
  have hnum : 0 ≤ β + (i : ℝ) := by positivity
  have hden : 0 < (i : ℝ) + 1 := by positivity
  exact div_nonneg hnum hden.le

/-- `|gBinom β j| = gPos β j`: the absolute value strips the signs of the numerators,
turning each `(-β - i)/(i+1)` into `(β + i)/(i+1)`. -/
theorem abs_gBinom_eq_gPos {β : ℝ} (hβ : 0 ≤ β) (j : ℕ) :
    |gBinom β j| = gPos β j := by
  unfold gBinom gPos
  rw [Finset.abs_prod]
  refine Finset.prod_congr rfl ?_
  intro i _
  have hden : 0 < (i : ℝ) + 1 := by positivity
  have hnum : 0 ≤ β + (i : ℝ) := by positivity
  rw [abs_div, abs_of_pos hden]
  congr 1
  rw [abs_of_nonpos (by linarith : -β - (i : ℝ) ≤ 0)]
  ring

/-- The multiplicative ratio of `gPos`: `gPos β (j+1) = gPos β j · (β + j)/(j + 1)`,
with the ratio factor `(β + j)/(j + 1) ≥ 0`. -/
theorem gPos_ratio_nonneg {β : ℝ} (hβ : 0 ≤ β) (j : ℕ) :
    0 ≤ (β + (j : ℝ)) / ((j : ℝ) + 1) := by
  have hden : 0 < (j : ℝ) + 1 := by positivity
  exact div_nonneg (by positivity) hden.le

/-- **One-step geometric step above the threshold.**  If `(β + j)/(j + 1) ≤ r`, then
`gPos β (j+1) ≤ gPos β j · r`. -/
theorem gPos_succ_le {β : ℝ} (hβ : 0 ≤ β) {r : ℝ} {j : ℕ}
    (hj : (β + (j : ℝ)) / ((j : ℝ) + 1) ≤ r) :
    gPos β (j + 1) ≤ gPos β j * r := by
  rw [gPos_succ]
  exact mul_le_mul_of_nonneg_left hj (gPos_nonneg hβ j)

/-- For `j ≥ N` with the threshold property `∀ k ≥ N, (β+k)/(k+1) ≤ r`, the tail bound
`gPos β j ≤ (gPos β N / r^N) · r^j` holds (with `r > 0`). -/
theorem gPos_tail_le {β : ℝ} (hβ : 0 ≤ β) {r : ℝ} (hr : 0 < r) {N : ℕ}
    (hthr : ∀ k, N ≤ k → (β + (k : ℝ)) / ((k : ℝ) + 1) ≤ r) :
    ∀ j, N ≤ j → gPos β j ≤ gPos β N / r ^ N * r ^ j := by
  intro j hj
  induction j with
  | zero =>
    have hN0 : N = 0 := Nat.le_zero.1 hj
    subst hN0
    simp
  | succ n ih =>
    rcases Nat.lt_or_ge N (n + 1) with hlt | hge
    · -- N ≤ n, use induction hypothesis then one geometric step
      have hNn : N ≤ n := Nat.lt_succ_iff.1 hlt
      have hstep : gPos β (n + 1) ≤ gPos β n * r := gPos_succ_le hβ (hthr n hNn)
      have hbound : gPos β n ≤ gPos β N / r ^ N * r ^ n := ih hNn
      calc gPos β (n + 1) ≤ gPos β n * r := hstep
        _ ≤ (gPos β N / r ^ N * r ^ n) * r :=
            mul_le_mul_of_nonneg_right hbound hr.le
        _ = gPos β N / r ^ N * r ^ (n + 1) := by rw [pow_succ]; ring
    · -- N = n+1: the bound is an equality `gPos = (gPos / r^N) * r^N`
      have hNeq : N = n + 1 := le_antisymm hj hge
      subst hNeq
      have hrne : r ^ (n + 1) ≠ 0 := by positivity
      have : gPos β (n + 1) / r ^ (n + 1) * r ^ (n + 1) = gPos β (n + 1) := by
        field_simp
      rw [this]

/-- **Threshold existence.**  For `r > 1` there is `N` with `(β + k)/(k + 1) ≤ r` for all
`k ≥ N`.  Equivalently `β + k ≤ r·(k+1)`, i.e. `β - r ≤ (r - 1)·k`, solvable by Archimedes
since `r - 1 > 0`. -/
theorem exists_threshold {β : ℝ} {r : ℝ} (hr : 1 < r) :
    ∃ N : ℕ, ∀ k, N ≤ k → (β + (k : ℝ)) / ((k : ℝ) + 1) ≤ r := by
  have hr1 : 0 < r - 1 := by linarith
  obtain ⟨N, hN⟩ := exists_nat_ge ((β - r) / (r - 1))
  refine ⟨N, fun k hk => ?_⟩
  have hkN : ((N : ℝ)) ≤ (k : ℝ) := by exact_mod_cast hk
  have hden : 0 < (k : ℝ) + 1 := by positivity
  -- from N ≥ (β - r)/(r - 1) and k ≥ N: (β - r)/(r - 1) ≤ k, so β - r ≤ (r-1)k
  have hge : (β - r) / (r - 1) ≤ (k : ℝ) := le_trans hN hkN
  have hmul : β - r ≤ (r - 1) * (k : ℝ) := by
    rw [div_le_iff₀ hr1] at hge
    linarith [hge]
  -- β + k ≤ r*(k+1)
  have hnum : β + (k : ℝ) ≤ r * ((k : ℝ) + 1) := by nlinarith [hmul]
  rw [div_le_iff₀ hden]
  linarith [hnum]

/-- **Main bound (sharp `1 < r` form).**  For `β ≥ 0` and any ratio `r > 1` there is a
nonnegative constant `A` with `|gBinom β j| ≤ A · r ^ j` for every `j`.  The `1 < r`
hypothesis is necessary: `|gBinom β j|` grows polynomially, so no `r ≤ 1` works. -/
theorem gBinom_abs_le (β : ℝ) (hβ : 0 ≤ β) (r : ℝ) (hr : 1 < r) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ j : ℕ, |gBinom β j| ≤ A * r ^ j := by
  have hr0 : 0 < r := lt_trans one_pos hr
  obtain ⟨N, hthr⟩ := exists_threshold (β := β) hr
  -- the single dominating constant
  set head : ℝ := ∑ k ∈ Finset.range N, gPos β k with hhead
  set tail : ℝ := gPos β N / r ^ N with htail
  refine ⟨tail + head, ?_, ?_⟩
  · have hhead0 : 0 ≤ head :=
      Finset.sum_nonneg (fun k _ => gPos_nonneg hβ k)
    have htail0 : 0 ≤ tail := by
      have : 0 ≤ gPos β N := gPos_nonneg hβ N
      positivity
    linarith
  · intro j
    rw [abs_gBinom_eq_gPos hβ]
    rcases Nat.lt_or_ge j N with hlt | hge
    · -- head regime: gPos β j ≤ head ≤ (tail + head) and 1 ≤ r^j
      have hsingle : gPos β j ≤ head := by
        rw [hhead]
        exact Finset.single_le_sum (f := fun k => gPos β k)
          (fun k _ => gPos_nonneg hβ k) (Finset.mem_range.2 hlt)
      have htail0 : 0 ≤ tail := by
        have : 0 ≤ gPos β N := gPos_nonneg hβ N
        positivity
      have hrj : (1 : ℝ) ≤ r ^ j := one_le_pow₀ hr.le
      calc gPos β j ≤ head := hsingle
        _ ≤ tail + head := by linarith
        _ = (tail + head) * 1 := by ring
        _ ≤ (tail + head) * r ^ j :=
            mul_le_mul_of_nonneg_left hrj (by linarith [htail0, hsingle, gPos_nonneg hβ j])
    · -- tail regime: gPos β j ≤ tail * r^j ≤ (tail + head)*r^j
      have hbound : gPos β j ≤ tail * r ^ j := gPos_tail_le hβ hr0 hthr j hge
      have hhead0 : 0 ≤ head :=
        Finset.sum_nonneg (fun k _ => gPos_nonneg hβ k)
      have hrj : 0 ≤ r ^ j := by positivity
      calc gPos β j ≤ tail * r ^ j := hbound
        _ ≤ (tail + head) * r ^ j :=
            mul_le_mul_of_nonneg_right (by linarith) hrj

end ShenWork.Wiener.EWA

#print axioms ShenWork.Wiener.EWA.gBinom_abs_le
