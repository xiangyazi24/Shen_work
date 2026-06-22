import ShenWork.Paper2.IntervalWienerAlgebraConnect

/-!
  # WALL-A residual 1: the general cosine-multiplication function bridge (Paper 2).

  Discharges the load-bearing `CosineMulBridge` predicate
  (`ShenWork.Paper2.IntervalWienerAlgebraConnect`) for genuine pointwise function
  products, UNCONDITIONALLY from `ℓ¹` summability of the cosine coefficients (which
  holds for `H^σ`, `σ > 1/2`, via the landed `intervalCosineCoeff_summable_abs`).

  The analytic content is the triple-cosine integral / absolutely-convergent
  double-series interchange on `[0,1]`:

  * `mulCosInt_eq_tsum` — `∫₀¹ cos(kπx) f g = ∑'_n ĝ_n ∫₀¹ cos(kπx) cos(nπx) f`
    (`MeasureTheory.integral_tsum` interchange, dominated by `|ĝ_n|·∫₀¹|f|`).
  * `rawCos_prod_to_sum` — `cos(kπx)cos(nπx)=½(cos((k+n)πx)+cos(|k−n|πx))`.
  * `rawCosInt_eq` — `∫₀¹ cos(jπx) f = ĉ_j / w_j` (`w_0=1`, `w_{≥1}=2`).
  * `starExpr_eq_trueCosProd` — the exact `w`-bookkeeping collapse of the weighted
    double series into the landed `trueCosProd` (the `k=0` diagonal correction and the
    `Nat.dist` `n<k / n=k / n>k` casework isolated here).
  * `cosineMulBridge_of_summable` — the discharged `CosineMulBridge`.

  No `sorry`/`admit`/`native_decide`/custom axiom.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal
open ShenWork.Paper2.HSigmaScale
open ShenWork.IntervalCosineInversion
open ShenWork.IntervalNeumannFullKernel
open ShenWork.CosineParsevalBridge

namespace ShenWork.Paper2.IntervalWienerAlgebra

/-! ## 1. Neumann weight, summability helpers, and the algebraic `trueCosProd` collapse. -/

def cw (j : ℕ) : ℝ := if j = 0 then 1 else 2
theorem cw_pos (j : ℕ) : 0 < cw j := by unfold cw; split <;> norm_num
theorem cw_zero : cw 0 = 1 := rfl
theorem cw_succ {j : ℕ} (hj : j ≠ 0) : cw j = 2 := by unfold cw; simp [hj]

/-- ℓ¹ sequences are bounded. -/
theorem l1_bdd {c : ℕ → ℝ} (hc : Summable (fun n => |c n|)) :
    ∃ C, 0 ≤ C ∧ ∀ n, |c n| ≤ C := by
  obtain ⟨C, hC⟩ := hc.tendsto_cofinite_zero.bddAbove_range_of_cofinite
  exact ⟨max C 0, le_max_right _ _, fun n => le_trans (hC ⟨n, rfl⟩) (le_max_left _ _)⟩

/-- Summability of the shifted product `c(n+k)·d n` from ℓ¹. -/
theorem summable_shift_mul {c d : ℕ → ℝ} (hc : Summable (fun n => |c n|))
    (hd : Summable (fun n => |d n|)) (k : ℕ) :
    Summable (fun n => c (n + k) * d n) := by
  obtain ⟨C, hC0, hC⟩ := l1_bdd hc
  apply Summable.of_norm_bounded (g := fun n => C * |d n|) (hd.mul_left C)
  intro n; rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hC _) (le_refl _) (abs_nonneg _) hC0

/-- Summability of `d n · (c(k+n)/cw(k+n))`. -/
theorem summable_T1 {c d : ℕ → ℝ} (hc : Summable (fun n => |c n|))
    (hd : Summable (fun n => |d n|)) (k : ℕ) :
    Summable (fun n => d n * (c (k + n) / cw (k + n))) := by
  obtain ⟨C, hC0, hC⟩ := l1_bdd hc
  apply Summable.of_norm_bounded (g := fun n => C * |d n|) (hd.mul_left C)
  intro n; rw [Real.norm_eq_abs, abs_mul, abs_div]
  have h1 : |c (k + n)| / |cw (k + n)| ≤ C := by
    rw [abs_of_pos (cw_pos _)]
    calc |c (k+n)| / cw (k+n) ≤ |c (k+n)| / 1 := by
          apply div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num)
          unfold cw; split <;> norm_num
      _ = |c (k+n)| := by ring
      _ ≤ C := hC _
  calc |d n| * (|c (k + n)| / |cw (k + n)|) ≤ |d n| * C := by
        exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = C * |d n| := by ring

/-- Summability of `d n · (c(Nat.dist k n)/cw(Nat.dist k n))`. -/
theorem summable_T2 {c d : ℕ → ℝ} (hc : Summable (fun n => |c n|))
    (hd : Summable (fun n => |d n|)) (k : ℕ) :
    Summable (fun n => d n * (c (Nat.dist k n) / cw (Nat.dist k n))) := by
  obtain ⟨C, hC0, hC⟩ := l1_bdd hc
  apply Summable.of_norm_bounded (g := fun n => C * |d n|) (hd.mul_left C)
  intro n; rw [Real.norm_eq_abs, abs_mul, abs_div]
  have h1 : |c (Nat.dist k n)| / |cw (Nat.dist k n)| ≤ C := by
    rw [abs_of_pos (cw_pos _)]
    calc |c (Nat.dist k n)| / cw (Nat.dist k n) ≤ |c (Nat.dist k n)| / 1 := by
          apply div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num)
          unfold cw; split <;> norm_num
      _ = |c (Nat.dist k n)| := by ring
      _ ≤ C := hC _
  calc |d n| * (|c (Nat.dist k n)| / |cw (Nat.dist k n)|) ≤ |d n| * C :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = C * |d n| := by ring

/-- The (★) expression: `cw k · ∑'_n d n · ½(c(k+n)/cw(k+n) + c(dist k n)/cw(dist k n))`. -/
def starExpr (c d : ℕ → ℝ) (k : ℕ) : ℝ :=
  cw k * ∑' n, d n * ((1/2 : ℝ) * (c (k + n) / cw (k + n)
    + c (Nat.dist k n) / cw (Nat.dist k n)))

/-- Summability of the shifted diagonal `c(n+1)·d(n+1)`. -/
theorem summable_diag_shift {c d : ℕ → ℝ} (hc : Summable (fun n => |c n|))
    (hd : Summable (fun n => |d n|)) :
    Summable (fun n => c (n + 1) * d (n + 1)) := by
  obtain ⟨C, hC0, hC⟩ := l1_bdd hc
  apply Summable.of_norm_bounded (g := fun n => C * |d (n+1)|)
    (((summable_nat_add_iff 1).mpr hd).mul_left C)
  intro n; rw [Real.norm_eq_abs, abs_mul]
  gcongr
  exact hC _

/-- `diagCorr` split: `∑'_n c n d n = c 0 d 0 + ∑'_m c(m+1) d(m+1)`. -/
theorem diagCorr_split {c d : ℕ → ℝ} (hc : Summable (fun n => |c n|))
    (hd : Summable (fun n => |d n|)) :
    diagCorr c d = c 0 * d 0 + ∑' m, c (m + 1) * d (m + 1) := by
  unfold diagCorr
  rw [tsum_eq_zero_add' (f := fun n => c n * d n) (summable_diag_shift hc hd)]

/-- Summability of the weighted diagonal `d(n+1)·(c(n+1)/cw(n+1))`. -/
theorem summable_wdiag_shift {c d : ℕ → ℝ} (hc : Summable (fun n => |c n|))
    (hd : Summable (fun n => |d n|)) :
    Summable (fun n => d (n+1) * (c (n+1) / cw (n+1))) := by
  obtain ⟨C, hC0, hC⟩ := l1_bdd hc
  apply Summable.of_norm_bounded (g := fun n => C * |d (n+1)|)
    (((summable_nat_add_iff 1).mpr hd).mul_left C)
  intro n; rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos (cw_pos _)]
  have h1 : |c (n+1)| / cw (n+1) ≤ C := by
    calc |c (n+1)| / cw (n+1) ≤ |c (n+1)| / 1 := by
          apply div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num)
          unfold cw; split <;> norm_num
      _ = |c (n+1)| := by ring
      _ ≤ C := hC _
  calc |d (n+1)| * (|c (n+1)| / cw (n+1)) ≤ |d (n+1)| * C :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = C * |d (n+1)| := by ring

set_option maxHeartbeats 600000 in
/-- The k=0 case of (★). -/
theorem starExpr_zero {c d : ℕ → ℝ} (hc : Summable (fun n => |c n|))
    (hd : Summable (fun n => |d n|)) :
    starExpr c d 0 = trueCosProd c d 0 := by
  unfold starExpr
  rw [cw_zero, one_mul]
  have hsummand : ∀ n, d n * ((1/2:ℝ) * (c (0 + n) / cw (0 + n)
      + c (Nat.dist 0 n) / cw (Nat.dist 0 n))) = d n * (c n / cw n) := by
    intro n; rw [Nat.zero_add, Nat.dist_zero_left]; ring
  rw [tsum_congr hsummand]
  rw [tsum_eq_zero_add' (f := fun n => d n * (c n / cw n)) (summable_wdiag_shift hc hd),
    cw_zero]
  have htail : ∑' m, d (m+1) * (c (m+1) / cw (m+1))
      = (1/2:ℝ) * ∑' m, c (m+1) * d (m+1) := by
    rw [← tsum_mul_left]
    refine tsum_congr (fun m => ?_)
    rw [cw_succ (by omega : m + 1 ≠ 0)]; ring
  rw [htail]
  -- trueCosProd c d 0
  unfold trueCosProd cosProd diffConv
  rw [diagCorr_split hc hd]
  have haddc : addConv c d 0 = c 0 * d 0 := by unfold addConv; simp
  have hcorr0 : corr1 c d 0 = diagCorr c d := by
    unfold corr1 diagCorr; exact tsum_congr (fun n => by rw [add_zero])
  have hcorr0' : corr1 d c 0 = diagCorr c d := by
    unfold corr1 diagCorr; exact tsum_congr (fun n => by rw [add_zero]; ring)
  rw [haddc, hcorr0, hcorr0', diagCorr_split hc hd]
  norm_num
  ring

/-! ### The k ≥ 1 case. -/

/-- `corr1 c d k = ∑'_n d n · c(k+n)` (index/comm reshape). -/
theorem corr1_eq_d_mul {c d : ℕ → ℝ} (k : ℕ) :
    corr1 c d k = ∑' n, d n * c (k + n) := by
  unfold corr1
  exact tsum_congr (fun n => by rw [Nat.add_comm k n]; ring)

/-- T1 for k≥1: `∑'_n d n · c(k+n)/cw(k+n) = ½ corr1 c d k`. -/
theorem T1_pos {c d : ℕ → ℝ} (_hc : Summable (fun n => |c n|))
    (_hd : Summable (fun n => |d n|)) {k : ℕ} (hk : k ≠ 0) :
    (∑' n, d n * (c (k + n) / cw (k + n))) = (1/2 : ℝ) * corr1 c d k := by
  rw [corr1_eq_d_mul, ← tsum_mul_left]
  refine tsum_congr (fun n => ?_)
  rw [cw_succ (by omega : k + n ≠ 0)]; ring

/-- `addConv` as a range-sum: `addConv c d k = ∑_{j∈range(k+1)} c j · d(k-j)`. -/
theorem addConv_range (c d : ℕ → ℝ) (k : ℕ) :
    addConv c d k = ∑ j ∈ Finset.range (k+1), c j * d (k - j) := by
  unfold addConv
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk (fun ij => c ij.1 * d ij.2) k]

/-- `corr1 d c k` split off its `n=0` term: `= d k · c 0 + ∑'_m d(m+1+k)·c(m+1)`. -/
theorem corr1_swap_split {c d : ℕ → ℝ} (hc : Summable (fun n => |c n|))
    (hd : Summable (fun n => |d n|)) (k : ℕ) :
    corr1 d c k = d k * c 0 + ∑' m, d (m + 1 + k) * c (m + 1) := by
  unfold corr1
  rw [tsum_eq_zero_add' (f := fun n => d (n + k) * c n)
    (by
      obtain ⟨C, hC0, hC⟩ := l1_bdd hc
      apply Summable.of_norm_bounded (g := fun m => |d (m + 1 + k)| * C)
        ((((summable_nat_add_iff (1 + k)).mpr hd).congr (fun m => by ring_nf)).mul_right C)
      intro m; rw [Real.norm_eq_abs, abs_mul]
      gcongr; exact hC _)]
  simp only [Nat.zero_add]

/-- Summability of the full T2 summand `d n · c(dist k n)/cw(dist k n)`. -/
theorem summable_T2' {c d : ℕ → ℝ} (hc : Summable (fun n => |c n|))
    (hd : Summable (fun n => |d n|)) (k : ℕ) :
    Summable (fun n => d n * (c (Nat.dist k n) / cw (Nat.dist k n))) :=
  summable_T2 hc hd k

/-- T2 split for k≥1 via `sum_add_tsum_nat_add k`. -/
theorem T2_split {c d : ℕ → ℝ} (hc : Summable (fun n => |c n|))
    (hd : Summable (fun n => |d n|)) (k : ℕ) :
    (∑' n, d n * (c (Nat.dist k n) / cw (Nat.dist k n)))
      = (∑ n ∈ Finset.range k, d n * (c (Nat.dist k n) / cw (Nat.dist k n)))
        + ∑' m, d (m + k) * (c (Nat.dist k (m + k)) / cw (Nat.dist k (m + k))) := by
  rw [← (summable_T2' hc hd k).sum_add_tsum_nat_add k]

/-- The tail of T2 (n = m+k): at m=0 gives `d k · c 0`, at m≥1 gives `d(m+k)·c m/2`. -/
theorem T2_tail {c d : ℕ → ℝ} (hc : Summable (fun n => |c n|))
    (hd : Summable (fun n => |d n|)) (k : ℕ) :
    (∑' m, d (m + k) * (c (Nat.dist k (m + k)) / cw (Nat.dist k (m + k))))
      = d k * c 0 + (1/2 : ℝ) * ∑' m, d (m + 1 + k) * c (m + 1) := by
  have hdist : ∀ m, Nat.dist k (m + k) = m := by
    intro m; rw [Nat.dist_eq_sub_of_le (by omega : k ≤ m + k)]; omega
  have hsummand : ∀ m, d (m + k) * (c (Nat.dist k (m + k)) / cw (Nat.dist k (m + k)))
      = d (m + k) * (c m / cw m) := by
    intro m; rw [hdist]
  rw [tsum_congr hsummand]
  -- split off m=0
  rw [tsum_eq_zero_add' (f := fun m => d (m + k) * (c m / cw m))
    (by
      obtain ⟨C, hC0, hC⟩ := l1_bdd hc
      apply Summable.of_norm_bounded (g := fun m => |d (m + 1 + k)| * C)
        ((((summable_nat_add_iff (1 + k)).mpr hd).congr (fun m => by ring_nf)).mul_right C)
      intro m; rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos (cw_pos _)]
      have h1 : |c (m+1)| / cw (m+1) ≤ C := by
        calc |c (m+1)| / cw (m+1) ≤ |c (m+1)| / 1 := by
              apply div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num)
              unfold cw; split <;> norm_num
          _ = |c (m+1)| := by ring
          _ ≤ C := hC _
      calc |d (m+1+k)| * (|c (m+1)| / cw (m+1)) ≤ |d (m+1+k)| * C :=
            mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ = |d (m+1+k)| * C := rfl)]
  rw [Nat.zero_add, cw_zero]
  congr 1
  · ring
  · rw [← tsum_mul_left]
    refine tsum_congr (fun m => ?_)
    rw [cw_succ (by omega : m + 1 ≠ 0)]; ring

/-- The range-`k` part of T2 simplifies (all dist = k-n ≥ 1, so cw = 2). -/
theorem T2_range {c d : ℕ → ℝ} (k : ℕ) :
    (∑ n ∈ Finset.range k, d n * (c (Nat.dist k n) / cw (Nat.dist k n)))
      = (1/2 : ℝ) * ∑ n ∈ Finset.range k, d n * c (k - n) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  have hnk : n < k := Finset.mem_range.mp hn
  have hdist : Nat.dist k n = k - n := Nat.dist_eq_sub_of_le_right (by omega)
  rw [hdist, cw_succ (by omega : k - n ≠ 0)]; ring

/-- `addConv c d k` for k≥1 split into the `n<k` part and the `c 0 d k` boundary. -/
theorem addConv_split (c d : ℕ → ℝ) (k : ℕ) :
    addConv c d k
      = (∑ n ∈ Finset.range k, d n * c (k - n)) + c 0 * d k := by
  rw [addConv_range, Finset.sum_range_succ', Nat.sub_zero]
  -- range_succ' peels the j=0 term to the end: ∑_{i<k} c(i+1) d(k-(i+1)) + c 0 d k
  congr 1
  rw [← Finset.sum_range_reflect (fun n => d n * c (k - n)) k]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hik : i < k := Finset.mem_range.mp hi
  have e2 : k - (k - 1 - i) = i + 1 := by omega
  have e3 : k - (i + 1) = k - 1 - i := by omega
  rw [e2, e3]; ring

set_option maxHeartbeats 800000 in
/-- The k≥1 case of (★). -/
theorem starExpr_pos {c d : ℕ → ℝ} (hc : Summable (fun n => |c n|))
    (hd : Summable (fun n => |d n|)) {k : ℕ} (hk : k ≠ 0) :
    starExpr c d k = trueCosProd c d k := by
  unfold starExpr
  rw [cw_succ hk]
  -- distribute: 2 · ∑ d n · ½(A + B) = ∑ d n · (A + B) = T1 + T2
  have hsplit : (2:ℝ) * ∑' n, d n * ((1/2:ℝ) * (c (k+n)/cw (k+n)
      + c (Nat.dist k n)/cw (Nat.dist k n)))
      = (∑' n, d n * (c (k+n)/cw (k+n)))
        + ∑' n, d n * (c (Nat.dist k n)/cw (Nat.dist k n)) := by
    rw [← Summable.tsum_add (summable_T1 hc hd k) (summable_T2 hc hd k), ← tsum_mul_left]
    refine tsum_congr (fun n => ?_); ring
  rw [hsplit, T1_pos hc hd hk, T2_split hc hd k, T2_range, T2_tail hc hd k]
  -- assemble target
  unfold trueCosProd cosProd diffConv
  rw [if_neg hk, addConv_split c d k, corr1_swap_split hc hd k]
  ring


/-! ## 2. The raw cosine-integral identities (function side). -/

theorem cosineCoeffs_eq_cw (f : ℝ → ℝ) (hf : Continuous f) (j : ℕ) :
    cosineCoeffs f j = cw j * ∫ x in (0:ℝ)..1, Real.cos ((j:ℝ) * Real.pi * x) * f x := by
  rw [cosineCoeffs_eq f hf j, fco_eq_ofReal f hf]
  simp only [Complex.ofReal_re, cw]
  push_cast
  ring_nf

/-- The raw cosine integral `∫₀¹ cos(jπx) f = cosineCoeffs f j / cw j`. -/
theorem rawCosInt_eq (f : ℝ → ℝ) (hf : Continuous f) (j : ℕ) :
    (∫ x in (0:ℝ)..1, Real.cos ((j:ℝ) * Real.pi * x) * f x) = cosineCoeffs f j / cw j := by
  rw [cosineCoeffs_eq_cw f hf j]
  field_simp [(cw_pos j).ne']

/-- Product-to-sum on the raw integral:
`∫₀¹ cos(kπx) cos(nπx) f = ½(∫ cos((k+n)πx) f + ∫ cos(|k-n|πx) f)`. -/
theorem rawCos_prod_to_sum (f : ℝ → ℝ) (hf : Continuous f) (k n : ℕ) :
    (∫ x in (0:ℝ)..1, Real.cos ((k:ℝ)*Real.pi*x) * Real.cos ((n:ℝ)*Real.pi*x) * f x)
      = (1/2) * ((∫ x in (0:ℝ)..1, Real.cos (((k+n:ℕ):ℝ)*Real.pi*x) * f x)
                 + (∫ x in (0:ℝ)..1, Real.cos (((Nat.dist k n:ℕ):ℝ)*Real.pi*x) * f x)) := by
  have hpt : ∀ x : ℝ,
      Real.cos ((k:ℝ)*Real.pi*x) * Real.cos ((n:ℝ)*Real.pi*x) * f x
        = (1/2) * (Real.cos (((k+n:ℕ):ℝ)*Real.pi*x) * f x
                   + Real.cos (((Nat.dist k n:ℕ):ℝ)*Real.pi*x) * f x) := by
    intro x
    have h2 := Real.two_mul_cos_mul_cos ((k:ℝ)*Real.pi*x) ((n:ℝ)*Real.pi*x)
    have hsum : ((k:ℝ)*Real.pi*x) + ((n:ℝ)*Real.pi*x) = ((k+n:ℕ):ℝ)*Real.pi*x := by
      push_cast; ring
    have hdist : Real.cos (((k:ℝ)*Real.pi*x) - ((n:ℝ)*Real.pi*x))
        = Real.cos (((Nat.dist k n:ℕ):ℝ)*Real.pi*x) := by
      set D : ℝ := ((Nat.dist k n : ℕ) : ℝ) * Real.pi * x with hD
      rcases le_total n k with h | h
      · have he : ((k:ℝ)*Real.pi*x) - ((n:ℝ)*Real.pi*x) = D := by
          have hc : (Nat.dist k n : ℝ) = (k:ℝ) - (n:ℝ) := by
            rw [Nat.dist_eq_sub_of_le_right h]; push_cast [Nat.cast_sub h]; ring
          rw [hD, hc]; ring
        rw [he]
      · have he : ((k:ℝ)*Real.pi*x) - ((n:ℝ)*Real.pi*x) = -D := by
          have hc : (Nat.dist k n : ℝ) = (n:ℝ) - (k:ℝ) := by
            rw [Nat.dist_comm, Nat.dist_eq_sub_of_le_right h]; push_cast [Nat.cast_sub h]; ring
          rw [hD, hc]; ring
        rw [he, Real.cos_neg]
    rw [hdist, hsum] at h2
    have h3 : Real.cos ((k:ℝ)*Real.pi*x) * Real.cos ((n:ℝ)*Real.pi*x)
        = (1/2) * (Real.cos (((k+n:ℕ):ℝ)*Real.pi*x)
                   + Real.cos (((Nat.dist k n:ℕ):ℝ)*Real.pi*x)) := by
      linarith [h2]
    rw [h3]; ring
  rw [intervalIntegral.integral_congr (fun x _ => hpt x)]
  rw [intervalIntegral.integral_const_mul]
  congr 1
  rw [intervalIntegral.integral_add]
  · exact ((Real.continuous_cos.comp (by continuity)).mul hf).intervalIntegrable _ _
  · exact ((Real.continuous_cos.comp (by continuity)).mul hf).intervalIntegrable _ _

/-! ## 3. The integral interchange (insert g's cosine series). -/

def fSeq (f g : ℝ → ℝ) (k : ℕ) (n : ℕ) (x : ℝ) : ℝ :=
  cosineCoeffs g n * (Real.cos ((n:ℝ)*Real.pi*x) * Real.cos ((k:ℝ)*Real.pi*x) * f x)

theorem fSeq_continuous (f g : ℝ → ℝ) (hf : Continuous f) (k n : ℕ) :
    Continuous (fSeq f g k n) := by
  unfold fSeq
  exact continuous_const.mul
    (((Real.continuous_cos.comp (by continuity)).mul
      (Real.continuous_cos.comp (by continuity))).mul hf)

theorem hasSum_g_scaled (f g : ℝ → ℝ) (hg : Continuous g)
    (hgsum : Summable (fun n : ℤ => fourierCoeff (reflCircle g) n)) (k : ℕ)
    {x : ℝ} (hx : x ∈ Set.Ioo (0:ℝ) 1) :
    HasSum (fun n : ℕ => fSeq f g k n x)
      (Real.cos ((k:ℝ)*Real.pi*x) * (f x * g x)) := by
  have hbase := intervalCosine_hasSum_pointwise g hg hx hgsum
  have hscaled := hbase.mul_right (Real.cos ((k:ℝ)*Real.pi*x) * f x)
  have hval : g x * (Real.cos ((k:ℝ)*Real.pi*x) * f x)
      = Real.cos ((k:ℝ)*Real.pi*x) * (f x * g x) := by ring
  rw [hval] at hscaled
  refine HasSum.congr_fun hscaled ?_
  intro n; rw [unitIntervalCosineMode]; unfold fSeq; ring

theorem mulCosInt_eq_tsum (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hgsum : Summable (fun n : ℤ => fourierCoeff (reflCircle g) n)) (k : ℕ) :
    (∫ x in (0:ℝ)..1, Real.cos ((k:ℝ)*Real.pi*x) * (f x * g x))
      = ∑' n : ℕ, cosineCoeffs g n
          * (∫ x in (0:ℝ)..1,
              Real.cos ((k:ℝ)*Real.pi*x) * Real.cos ((n:ℝ)*Real.pi*x) * f x) := by
  have h01 : (0:ℝ) ≤ 1 := by norm_num
  rw [intervalIntegral.integral_of_le h01]
  have hd1 : Summable (fun n : ℕ => |cosineCoeffs g n|) :=
    intervalCosineCoeff_summable_abs g hg hgsum
  have hfabs_int : IntegrableOn (fun x => |f x|) (Set.Ioc (0:ℝ) 1) volume := by
    have : IntervalIntegrable (fun x => |f x|) volume 0 1 :=
      (hf.abs).intervalIntegrable 0 1
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le h01] at this
  set Iabs : ℝ := ∫ x in Set.Ioc (0:ℝ) 1, |f x| with hIabs
  have hIabs0 : 0 ≤ Iabs := integral_nonneg (fun x => abs_nonneg _)
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (fSeq f g k n)
      (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    fun n => (fSeq_continuous f g hf k n).aestronglyMeasurable
  have hfin : (∑' n : ℕ, ∫⁻ x in Set.Ioc (0:ℝ) 1, ‖fSeq f g k n x‖ₑ) ≠ ⊤ := by
    have hbound : ∀ n : ℕ, (∫⁻ x in Set.Ioc (0:ℝ) 1, ‖fSeq f g k n x‖ₑ)
        ≤ ENNReal.ofReal (|cosineCoeffs g n| * Iabs) := by
      intro n
      have hpt : ∀ x, ‖fSeq f g k n x‖ₑ
          ≤ ENNReal.ofReal (|cosineCoeffs g n| * |f x|) := by
        intro x
        rw [Real.enorm_eq_ofReal_abs]
        apply ENNReal.ofReal_le_ofReal
        unfold fSeq
        rw [abs_mul, abs_mul, abs_mul]
        have hc1 : |Real.cos ((n:ℝ)*Real.pi*x)| ≤ 1 := Real.abs_cos_le_one _
        have hc2 : |Real.cos ((k:ℝ)*Real.pi*x)| ≤ 1 := Real.abs_cos_le_one _
        have hnn : 0 ≤ |cosineCoeffs g n| := abs_nonneg _
        have hcc : |Real.cos ((n:ℝ)*Real.pi*x)| * |Real.cos ((k:ℝ)*Real.pi*x)| ≤ 1 :=
          mul_le_one₀ hc1 (abs_nonneg _) hc2
        have hrw : |cosineCoeffs g n| *
            (|Real.cos ((n:ℝ)*Real.pi*x)| * |Real.cos ((k:ℝ)*Real.pi*x)| * |f x|)
            = (|cosineCoeffs g n| * |f x|)
              * (|Real.cos ((n:ℝ)*Real.pi*x)| * |Real.cos ((k:ℝ)*Real.pi*x)|) := by ring
        rw [hrw]
        exact mul_le_of_le_one_right (by positivity) hcc
      calc (∫⁻ x in Set.Ioc (0:ℝ) 1, ‖fSeq f g k n x‖ₑ)
          ≤ ∫⁻ x in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (|cosineCoeffs g n| * |f x|) :=
            lintegral_mono hpt
        _ = ENNReal.ofReal (|cosineCoeffs g n| * Iabs) := by
            rw [show (fun x => ENNReal.ofReal (|cosineCoeffs g n| * |f x|))
                  = (fun x => ENNReal.ofReal (|cosineCoeffs g n|) * ENNReal.ofReal (|f x|)) from
                funext (fun x => by rw [ENNReal.ofReal_mul (abs_nonneg _)])]
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
                ← ofReal_integral_eq_lintegral_ofReal hfabs_int
                  (Filter.Eventually.of_forall (fun x => abs_nonneg _)),
                ← ENNReal.ofReal_mul (abs_nonneg _)]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) (hd1.mul_right Iabs)]
    exact ENNReal.ofReal_ne_top
  have hit := MeasureTheory.integral_tsum hmeas hfin
  have hlhs : (∫ x in Set.Ioc (0:ℝ) 1, Real.cos ((k:ℝ)*Real.pi*x) * (f x * g x))
      = ∫ x in Set.Ioc (0:ℝ) 1, ∑' n : ℕ, fSeq f g k n x := by
    refine setIntegral_congr_ae measurableSet_Ioc ?_
    filter_upwards [Ioo_ae_eq_Ioc.symm] with x hx
    intro hmem
    have hxo : x ∈ Set.Ioo (0:ℝ) 1 := hx.mp hmem
    exact ((hasSum_g_scaled f g hg hgsum k hxo).tsum_eq).symm
  rw [hlhs, hit]
  refine tsum_congr (fun n => ?_)
  unfold fSeq
  rw [MeasureTheory.integral_const_mul, intervalIntegral.integral_of_le h01]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc (fun x _ => ?_)
  ring


/-! ## 4. The full bridge: `cosineCoeffs (f·g) = trueCosProd ĉ ĝ`. -/

/-- Combiner: the (★) weighted double series equals the landed `trueCosProd`. -/
theorem starExpr_eq_trueCosProd {c d : ℕ → ℝ} (hc : Summable (fun n => |c n|))
    (hd : Summable (fun n => |d n|)) (k : ℕ) :
    starExpr c d k = trueCosProd c d k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact starExpr_zero hc hd
  · exact starExpr_pos hc hd (by omega)

set_option maxHeartbeats 1200000 in
/-- **The cosine-multiplication bridge, discharged from `ℓ¹` cosine coefficients.**
For continuous `f, g` on `[0,1]` whose even-reflection Fourier coefficients are
summable (so the cosine coefficients are `ℓ¹`; this holds for `H^σ`, `σ > 1/2`), the
cosine coefficients of the pointwise product `f·g` equal `trueCosProd` of the factor
coefficient sequences at every mode — i.e. `CosineMulBridge f g` holds. -/
theorem cosineMulBridge_of_summable {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfsum : Summable (fun n : ℤ => fourierCoeff (reflCircle f) n))
    (hgsum : Summable (fun n : ℤ => fourierCoeff (reflCircle g) n)) :
    CosineMulBridge f g := by
  intro k
  set c : ℕ → ℝ := cosineCoeffs f with hc_def
  set d : ℕ → ℝ := cosineCoeffs g with hd_def
  have hc1 : Summable (fun n => |c n|) := intervalCosineCoeff_summable_abs f hf hfsum
  have hd1 : Summable (fun n => |d n|) := intervalCosineCoeff_summable_abs g hg hgsum
  have hfg : Continuous (fun x => f x * g x) := hf.mul hg
  -- coefficient of the product = cw k * integral
  rw [cosineCoeffs_eq_cw (fun x => f x * g x) hfg k]
  -- interchange
  rw [mulCosInt_eq_tsum f g hf hg hgsum k]
  -- product-to-sum + rawCosInt inside the tsum
  have hterm : ∀ n, d n * (∫ x in (0:ℝ)..1,
        Real.cos ((k:ℝ)*Real.pi*x) * Real.cos ((n:ℝ)*Real.pi*x) * f x)
      = d n * ((1/2 : ℝ) * (c (k + n) / cw (k + n)
          + c (Nat.dist k n) / cw (Nat.dist k n))) := by
    intro n
    rw [rawCos_prod_to_sum f hf k n, rawCosInt_eq f hf, rawCosInt_eq f hf]
  rw [tsum_congr hterm]
  -- now the goal is `cw k * (∑' ...) = trueCosProd c d k`, i.e. starExpr = trueCosProd
  show starExpr c d k = trueCosProd c d k
  exact starExpr_eq_trueCosProd hc1 hd1 k

/-- **`CosineMulBridge` from `H^σ` (σ > 1/2) and continuity.**  The bridge holds for
any continuous `f, g` whose even-reflection Fourier coefficients are summable. -/
theorem cosineMulBridge_of_continuous_l1 {f g : ℝ → ℝ} (hf : Continuous f)
    (hg : Continuous g)
    (hfsum : Summable (fun n : ℤ => fourierCoeff (reflCircle f) n))
    (hgsum : Summable (fun n : ℤ => fourierCoeff (reflCircle g) n)) :
    CosineMulBridge f g :=
  cosineMulBridge_of_summable hf hg hfsum hgsum


/-- For `n ≥ 1` and `σ ≥ 0`: `(1+λn)^σ ≤ (1+π²)^σ · n^(2σ)`. -/
theorem one_add_lam_rpow_le {σ : ℝ} (hσ : 0 ≤ σ) {n : ℕ} (hn : 1 ≤ n) :
    (1 + lam n) ^ σ ≤ (1 + Real.pi ^ 2) ^ σ * ((n : ℝ) ^ (2 * σ)) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hbase : 1 + lam n ≤ (1 + Real.pi ^ 2) * (n : ℝ) ^ 2 := by
    rw [lam_eq]
    have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    have hpi : 0 ≤ Real.pi ^ 2 := by positivity
    nlinarith [hpi, hn2, sq_nonneg ((n:ℝ))]
  calc (1 + lam n) ^ σ
      ≤ ((1 + Real.pi ^ 2) * (n : ℝ) ^ 2) ^ σ :=
        Real.rpow_le_rpow (one_add_lam_pos n).le hbase hσ
    _ = (1 + Real.pi ^ 2) ^ σ * ((n : ℝ) ^ 2) ^ σ := by
        rw [Real.mul_rpow (by positivity) (by positivity)]
    _ = (1 + Real.pi ^ 2) ^ σ * ((n : ℝ) ^ (2 * σ)) := by
        rw [← Real.rpow_natCast ((n:ℝ)) 2, ← Real.rpow_mul hnpos.le]
        norm_num

/-- **Coefficient-decay ⟹ `MemHSigma`.**  If `|a n| ≤ C / n^q` for `n ≥ 1` with
`q > σ + 1/2` (`σ ≥ 0`), then `a ∈ H^σ`.  Pure comparison with the convergent
`p`-series `∑ n^{2σ−2q}` (`2q − 2σ > 1`). -/
theorem memHSigma_of_coeff_decay {σ q C : ℝ} (hσ : 0 ≤ σ) (hq : σ + 1/2 < q)
    {a : ℕ → ℝ} (hdecay : ∀ n : ℕ, 1 ≤ n → |a n| ≤ C / (n : ℝ) ^ q) :
    MemHSigma σ a := by
  unfold MemHSigma
  -- comparison series: K · n^{2σ-2q}, summable since 2q-2σ > 1
  have hC0 : 0 ≤ C := by
    have hd1 := hdecay 1 (le_refl _)
    rw [Nat.cast_one, Real.one_rpow, div_one] at hd1
    exact le_trans (abs_nonneg _) hd1
  set K : ℝ := (1 + Real.pi ^ 2) ^ σ * C ^ 2 with hK
  have hps : Summable (fun n : ℕ => ((n : ℝ) ^ (2 * q - 2 * σ))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by linarith)
  rw [← summable_nat_add_iff 1]
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    (((summable_nat_add_iff 1).mpr hps).mul_left K)
  · have := Real.rpow_nonneg (one_add_lam_pos (n+1)).le σ; positivity
  · -- (1+λ_{n+1})^σ (a_{n+1})^2 ≤ K (n+1)^{2σ-2q}
    have hn1 : 1 ≤ n + 1 := by omega
    have hnp : (0:ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
    have hlam := one_add_lam_rpow_le hσ hn1
    have hdec := hdecay (n+1) hn1
    have ha2 : (a (n+1)) ^ 2 ≤ C ^ 2 / ((n+1 : ℕ) : ℝ) ^ (2 * q) := by
      have habs : |a (n+1)| ≤ C / ((n+1:ℕ):ℝ) ^ q := hdec
      have hsq : (a (n+1))^2 = |a (n+1)|^2 := (sq_abs _).symm
      rw [hsq]
      have hpow : (C / ((n+1:ℕ):ℝ) ^ q)^2 = C^2 / ((n+1:ℕ):ℝ) ^ (2*q) := by
        rw [div_pow, ← Real.rpow_natCast (((n+1:ℕ):ℝ) ^ q) 2, ← Real.rpow_mul hnp.le]
        congr 2; push_cast; ring
      calc |a (n+1)|^2 ≤ (C / ((n+1:ℕ):ℝ) ^ q)^2 := by
            apply pow_le_pow_left₀ (abs_nonneg _) habs
        _ = C^2 / ((n+1:ℕ):ℝ) ^ (2*q) := hpow
    -- combine
    have hlamnn : 0 ≤ (1 + lam (n+1)) ^ σ := Real.rpow_nonneg (one_add_lam_pos _).le _
    have key : (1 + lam (n+1)) ^ σ * (a (n+1)) ^ 2
        ≤ ((1 + Real.pi ^ 2) ^ σ * ((n+1:ℕ):ℝ) ^ (2*σ))
            * (C^2 / ((n+1:ℕ):ℝ) ^ (2*q)) := by
      apply mul_le_mul hlam ha2 (sq_nonneg _)
      positivity
    refine le_trans key (le_of_eq ?_)
    rw [hK, Real.rpow_sub hnp]
    field_simp

/-! ## 5. Task-2 foundation: coefficient-decay ⟹ `H^σ` (classical-regularity route).

The cleanest route to `(1+v)^{−β} ∈ H^σ` and `u^m ∈ H^σ` for *real* exponents (recall
`CM2Params.m, .β : ℝ`, so the integer-power `funPow` does not cover them) is the
classical one: a `Cᵏ` interval function has cosine coefficients decaying like `n^{-k}`
(integration by parts), and `n^{-q}` decay with `q > σ + 1/2` lands in `H^σ`.  This is
the shared, exponent-agnostic foundation lemma; it is strictly lighter than the analytic
functional calculus and avoids any norm/completeness/Nemytskii machinery.

`memHSigma_of_coeff_decay` below is that foundation (pure `p`-series comparison).  The
remaining Task-2 residual is the classical-analysis input
`Cᵏ ⟹ |ĉ_n| ≤ C n^{−k}` (two integrations by parts of `∫₀¹ cos(nπx) f`) together with
the composition regularity `v ∈ Cᵏ, v ≥ 0 ⟹ (1+v)^{−β} ∈ Cᵏ` (chain rule, `Real.rpow`
smooth on `(−1,∞)`); both are standard but not formalized here. -/

#print axioms starExpr_eq_trueCosProd
#print axioms mulCosInt_eq_tsum
#print axioms cosineMulBridge_of_summable
#print axioms memHSigma_of_coeff_decay

end ShenWork.Paper2.IntervalWienerAlgebra
