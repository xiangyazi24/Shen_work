import ShenWork.Wiener.EWA.WienerComposition
import ShenWork.Wiener.EWA.BinomialCoeffBound

/-!
# Small-data composition for the genuine chemotaxis denominator `(1+v)^{-β}`

`WienerComposition.lean` proved the abstract summability
`binomialSeries_termNorm_summable`, but its carried coefficient majorant
`∀ j, |c j| ≤ A · r₀^j` together with `r₀ ≤ 1` is **UNSATISFIABLE** for the real
generalized-binomial coefficients `c j = gBinom β j`: those grow polynomially
(`|gBinom β j| ~ j^{β-1}/Γ(β)`), so the sharp majorant forces `1 < r₀`
(`BinomialCoeffBound.gBinom_abs_le`).  Hence that abstract lemma, instantiated for
the actual `(1+v)^{-β}` series, has an unsatisfiable hypothesis — a §3.3 vacuity.

This file CLOSES the gap.  It supplies the majorant INTERNALLY (via `gBinom_abs_le`
with a radius `r₀ ∈ (1, 1/q)` chosen inside the proof) and routes through the
*general* `binomialMajorant_summable` (whose radius hypothesis is the genuine
`r₀ · q < 1`, no spurious upper bound).  The result carries NO majorant hypothesis:
under only `0 ≤ σ`, `MemWNorm σ v`, `0 ≤ β`, and the smallness `Cσ · wNorm σ v < 1`,
the binomial series for `(1+v)^{-β}` is absolutely convergent in the weighted-Wiener
algebra.  The radius `r₀ ∈ (1, 1/q)` exists precisely because `q := Cσ·wNorm σ v < 1`
(near-equilibrium = the P3 T2.2 regime).
-/

namespace ShenWork.Wiener.EWA

/-- A convergence radius `1 < r₀` with `r₀ · q < 1` exists for any `0 ≤ q < 1`. -/
theorem exists_radius_of_small {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∃ r₀ : ℝ, 1 < r₀ ∧ r₀ * q < 1 := by
  rcases eq_or_lt_of_le hq0 with hqz | hqpos
  · exact ⟨2, by norm_num, by rw [← hqz]; norm_num⟩
  · have hinv : 1 < 1 / q := by rw [lt_div_iff₀ hqpos, one_mul]; exact hq1
    refine ⟨(1 + 1 / q) / 2, by linarith, ?_⟩
    have hr_lt : (1 + 1 / q) / 2 < 1 / q := by linarith
    have := mul_lt_mul_of_pos_right hr_lt hqpos
    rwa [one_div_mul_cancel (ne_of_gt hqpos)] at this

/-- **Small-data composition for `(1+v)^{-β}`, self-contained (§3.3 gap fixed).**
Under only `0 ≤ σ`, `MemWNorm σ v`, `0 ≤ β`, and the smallness
`wNormSubmulConst hσ · wNorm σ v < 1`, the binomial-series term norms
`|gBinom β j| · wNorm σ (convPow v j)` are summable — i.e. the series
`Σ_j gBinom β j · v^{⋆ j}` for `(1+v)^{-β}` is absolutely convergent in the
weighted-Wiener Banach algebra.  No majorant hypothesis is carried (it is supplied
by `gBinom_abs_le`); the only carried analytic hypothesis is the smallness. -/
theorem chemDenom_smallData_termNorm_summable {σ : ℝ} (hσ : 0 ≤ σ) {v : ℕ → ℝ}
    (hv : MemWNorm σ v) {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : wNormSubmulConst hσ * wNorm σ v < 1) :
    Summable (fun j => |gBinom β j| * wNorm σ (convPow v j)) := by
  set q := wNormSubmulConst hσ * wNorm σ v with hq_def
  have hCσ : 0 ≤ wNormSubmulConst hσ := le_of_lt (wNormSubmulConst_pos hσ)
  have hq0 : 0 ≤ q := mul_nonneg hCσ (wNorm_nonneg σ v)
  obtain ⟨r₀, hr1, hrq⟩ := exists_radius_of_small hq0 hsmall
  obtain ⟨A, _hA0, hAle⟩ := gBinom_abs_le β hβ r₀ hr1
  have hr₀0 : 0 ≤ r₀ := le_of_lt (lt_trans one_pos hr1)
  -- summable geometric majorant `Σ |gBinom β j| · q^j`
  have hbase : Summable (fun j => |gBinom β j| * q ^ j) :=
    binomialMajorant_summable hr₀0 hq0 hrq hAle
  set B := wNorm σ convUnit with hB_def
  have hB0 : 0 ≤ B := wNorm_nonneg σ convUnit
  have hsum : Summable (fun j => B * (|gBinom β j| * q ^ j)) := hbase.mul_left B
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hsum
  · exact mul_nonneg (abs_nonneg _) (wNorm_nonneg σ _)
  · have hcp : wNorm σ (convPow v j) ≤ B * q ^ j := convPow_wNorm_le hσ hv j
    calc |gBinom β j| * wNorm σ (convPow v j)
        ≤ |gBinom β j| * (B * q ^ j) :=
          mul_le_mul_of_nonneg_left hcp (abs_nonneg _)
      _ = B * (|gBinom β j| * q ^ j) := by ring

end ShenWork.Wiener.EWA
