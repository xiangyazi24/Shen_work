import ShenWork.Wiener.WeightedL1Deriv

/-!
# Wiener brick 4e — THE DECISIVE ESTIMATE

`‖e^{−tf}‖_{A¹} ≤ C·(1 + t‖Df‖)²·e^{−δt}`, the Wiener-Lévy core.

This file assembles the committed analytic pieces (`evalAt_exp`,
`norm_coeff_le_of_eval_bound`, `incl_exp`, `D_exp_neg_t`, the operator bound
`‖D a‖ ≤ π‖a‖`) into the decisive exponential-decay estimate.

The genuine new content is:

* **`coeff_decay`** — under the spectral floor `δ ≤ Re(evalAt x (incl10 f))`,
  every Fourier coefficient of `e^{−tf}` obeys `‖a_n‖ ≤ e^{−δt}` (the floor
  → `e^{−δt}` assembly via `evalAt_exp` + `norm_coeff_le_of_eval_bound`).
* **`tail_le_deriv`** — the `A⁰`-tail over `|n| > N` is bounded by the
  derivative norm: `∑_{|n|>N} ‖a_n‖ ≤ ‖D a‖_{A⁰} / (π(N+1))` (a subset
  `tsum` via `Summable.sum_add_tsum_compl`).
* **`wNorm1_split`** — the `‖·‖_{WA 1} = ‖incl10·‖_{A⁰} + (1/π)‖D·‖_{A⁰}`
  decomposition.
* the mode-split absorption (ChatGPT Step-4e skeleton: `exists_nat_good`,
  `absorb_le_half`, `mode_absorb`), giving the decisive bound
  **`decisive_exp_bound`**.
-/

open scoped BigOperators

noncomputable section

namespace ShenWork.Wiener

namespace WA

/-! ### Part 0 — the mode-split arithmetic (ChatGPT Step-4e skeleton). -/

/-- **`exists_nat_good`.** For `Y ≥ 0` there is `N : ℕ` with `Y/(N+1) ≤ 1/2`
and `(N+1) ≤ 2Y + 2`. -/
theorem exists_nat_good (Y : ℝ) (hY : 0 ≤ Y) :
    ∃ N : ℕ, Y / (N + 1 : ℝ) ≤ (1 / 2 : ℝ) ∧ (N + 1 : ℝ) ≤ 2 * Y + 2 := by
  classical
  set z : ℤ := ⌈(2 * Y : ℝ)⌉ with hz_def
  set N : ℕ := z.toNat with hN_def
  have hz0 : 0 ≤ z := by rw [hz_def]; exact Int.ceil_nonneg (by nlinarith)
  have hN_real : (N : ℝ) = (z : ℝ) := by
    have : ((N : ℤ) = z) := by rw [hN_def]; exact Int.toNat_of_nonneg hz0
    exact_mod_cast this
  have hz_low : 2 * Y ≤ (z : ℝ) := by rw [hz_def]; exact Int.le_ceil (2 * Y)
  refine ⟨N, ?_, ?_⟩
  · have hden : 0 < (N + 1 : ℝ) := by positivity
    have hmain : 2 * Y ≤ (N + 1 : ℝ) := by rw [hN_real]; linarith
    have hhalf : Y ≤ (1 / 2 : ℝ) * (N + 1 : ℝ) := by nlinarith
    exact (div_le_iff₀ hden).2 hhalf
  · rw [hN_real]
    have hceil : (z : ℝ) < 2 * Y + 1 := by rw [hz_def]; exact Int.ceil_lt_add_one _
    linarith

/-- **`absorb_le_half`.** If `X ≤ A + c·X` with `0 ≤ X` and `c ≤ 1/2`, then
`X ≤ 2A`. -/
theorem absorb_le_half {X A c : ℝ} (hX : 0 ≤ X) (hc : c ≤ (1 / 2 : ℝ))
    (h : X ≤ A + c * X) : X ≤ 2 * A := by
  have hcX : c * X ≤ (1 / 2 : ℝ) * X := mul_le_mul_of_nonneg_right hc hX
  nlinarith

/-! ### Part 1 — coefficient decay (the floor → `e^{−δt}` assembly). -/

/-- Point evaluation commutes with `ℂ`-scalar multiplication. -/
theorem evalAt_smul (x : Circ) (c : ℂ) (a : WA 0) :
    evalAt x (c • a) = c * evalAt x a := by
  show evalAtAlg x (c • a) = c * evalAtAlg x a
  rw [map_smul]; simp [smul_eq_mul]

/-- **`coeff_decay`.** Under the spectral floor `δ ≤ Re(evalAt x (incl10 f))`,
every coefficient of `e^{−tf}` satisfies `‖a_n‖ ≤ e^{−δt}` (for `0 ≤ t`). -/
theorem coeff_decay (f : WA 1) (t δ : ℝ) (ht : 0 ≤ t)
    (hδ : ∀ x : Circ, δ ≤ (evalAt x (incl10 f)).re) (n : ℤ) :
    ‖(incl10 (NormedSpace.exp (((-t : ℝ) : ℂ) • f))).toFun n‖
      ≤ Real.exp (-δ * t) := by
  set a : WA 0 := incl10 (NormedSpace.exp (((-t : ℝ) : ℂ) • f)) with ha_def
  have ha_exp : a = NormedSpace.exp (((-t : ℝ) : ℂ) • incl10 f) := by
    rw [ha_def, incl_exp, map_smul]
  refine norm_coeff_le_of_eval_bound a n (Real.exp (-δ * t)) (fun x => ?_)
  have hval : evalC a x = evalAt x a := by
    rw [evalAt_apply, evalC_apply, evalLin_apply]
  rw [hval, ha_exp, evalAt_exp, evalAt_smul, Complex.norm_exp]
  have hre : (((-t : ℝ) : ℂ) * evalAt x (incl10 f)).re
      = (-t) * (evalAt x (incl10 f)).re := by
    simp [Complex.ofReal_re, Complex.ofReal_im]
  rw [hre]
  exact Real.exp_le_exp.2 (by nlinarith [hδ x, ht])

/-! ### Part 2 — the norm bridges and `wNorm1_split`. -/

/-- `‖a‖_{A⁰} = ∑'_n ‖a_n‖` for `a : WA 1` (after `incl10`). -/
theorem normIncl_eq_tsum (a : WA 1) : ‖incl10 a‖ = ∑' n : ℤ, ‖a.toFun n‖ := by
  rw [norm_def, wNorm]; simp [incl10_toFun, wWeight]

/-- `‖D a‖_{A⁰} = ∑'_n ‖(D a)_n‖`. -/
theorem normD_eq_tsum (a : WA 1) : ‖D a‖ = ∑' n : ℤ, ‖(D a).toFun n‖ := by
  rw [norm_def, wNorm]; simp [wWeight]

/-- The `A⁰`-summability of the coefficients of `a : WA 1`. -/
theorem summ_a (a : WA 1) : Summable (fun n => ‖a.toFun n‖) := by
  have hm0 : MemW 0 a.toFun := memW_mono (Nat.zero_le 1) a.mem
  rw [MemW] at hm0; simpa [wWeight] using hm0

/-- The `A⁰`-summability of the derivative coefficients. -/
theorem summ_Da (a : WA 1) : Summable (fun n => ‖(D a).toFun n‖) := by
  have hm0 : MemW 0 (D a).toFun := (D a).mem
  rw [MemW] at hm0; simpa [wWeight] using hm0

/-- The summability of `|n|‖a_n‖` (the weighted half of `WA 1`). -/
theorem summ_na (a : WA 1) : Summable (fun n : ℤ => |(n : ℝ)| * ‖a.toFun n‖) := by
  have hsum1 : Summable (fun n => wWeight 1 n * ‖a.toFun n‖) := a.mem
  have hsa := summ_a a
  have : (fun n : ℤ => |(n : ℝ)| * ‖a.toFun n‖)
      = fun n : ℤ => wWeight 1 n * ‖a.toFun n‖ - ‖a.toFun n‖ := by
    funext n; simp [wWeight]; ring
  rw [this]; exact hsum1.sub hsa

/-- `‖D a‖_{A⁰} = π · ∑'_n |n|‖a_n‖`. -/
theorem normD_eq_pi (a : WA 1) :
    ‖D a‖ = Real.pi * ∑' n : ℤ, |(n : ℝ)| * ‖a.toFun n‖ := by
  rw [norm_def, wNorm]
  have hco : (fun n => wWeight 0 n * ‖(D a).toFun n‖)
      = fun n : ℤ => Real.pi * (|(n : ℝ)| * ‖a.toFun n‖) := by
    funext n
    rw [D_toFun, wDeriv]
    simp only [wWeight, pow_zero, one_mul]
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_of_nonneg Real.pi_nonneg, Complex.norm_intCast]
    ring
  rw [hco, tsum_mul_left]

/-- **`wNorm1_split`.** `‖a‖_{WA 1} = ‖incl10 a‖_{A⁰} + (1/π)‖D a‖_{A⁰}`. -/
theorem wNorm1_split (a : WA 1) :
    ‖a‖ = ‖incl10 a‖ + (1 / Real.pi) * ‖D a‖ := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  rw [normD_eq_pi, norm_def, wNorm, normIncl_eq_tsum]
  have hsa := summ_a a
  have hsna := summ_na a
  have hsplit : (fun n => wWeight 1 n * ‖a.toFun n‖)
      = fun n : ℤ => ‖a.toFun n‖ + |(n : ℝ)| * ‖a.toFun n‖ := by
    funext n; simp [wWeight]; ring
  rw [hsplit, Summable.tsum_add hsa hsna]
  field_simp

/-! ### Part 3 — the tail-via-derivative subset `tsum` (genuine new lemma). -/

/-- For `|n| ≥ N+1`, `‖a_n‖ ≤ ‖(D a)_n‖ / (π(N+1))`. -/
theorem coeff_tail_bound (a : WA 1) (N : ℕ) (n : ℤ)
    (hn : (N : ℝ) + 1 ≤ |(n : ℝ)|) :
    ‖a.toFun n‖ ≤ ‖(D a).toFun n‖ / (Real.pi * ((N : ℝ) + 1)) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hDn : ‖(D a).toFun n‖ = Real.pi * |(n : ℝ)| * ‖a.toFun n‖ := by
    rw [D_toFun, wDeriv, norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_of_nonneg Real.pi_nonneg, Complex.norm_intCast]
  rw [hDn]
  have hden : 0 < Real.pi * ((N : ℝ) + 1) := by positivity
  rw [le_div_iff₀ hden]
  have ha : 0 ≤ ‖a.toFun n‖ := norm_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hn (mul_nonneg (le_of_lt hpi) ha)]

/-- Outside `Icc (-N) N` the index satisfies `N+1 ≤ |n|`. -/
theorem mem_compl_abs (N : ℕ) (x : ℤ)
    (hx : x ∉ Finset.Icc (-(N : ℤ)) (N : ℤ)) : (N : ℝ) + 1 ≤ |(x:ℝ)| := by
  rw [Finset.mem_Icc, not_and_or] at hx
  have : (N : ℤ) + 1 ≤ |x| := by
    rcases hx with h | h
    · rw [abs_of_neg (by omega)]; omega
    · rw [abs_of_pos (by omega)]; omega
  have hcast : ((N : ℤ) + 1 : ℝ) ≤ ((|x| : ℤ) : ℝ) := by exact_mod_cast this
  push_cast [Int.cast_abs] at hcast ⊢; linarith

/-- **`tail_le_deriv`.** The `A⁰`-tail over `|n| > N` is bounded by the
derivative norm: `∑'_{n∉Icc(-N,N)} ‖a_n‖ ≤ ‖D a‖ / (π(N+1))`. -/
theorem tail_le_deriv (a : WA 1) (N : ℕ) :
    ∑' x : ↑((↑(Finset.Icc (-(N : ℤ)) (N : ℤ)) : Set ℤ))ᶜ, ‖a.toFun (x : ℤ)‖
      ≤ ‖D a‖ / (Real.pi * ((N : ℝ) + 1)) := by
  have hden : 0 < Real.pi * ((N : ℝ) + 1) := by positivity
  set s : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ) with hs_def
  have hsa := summ_a a
  have hsDa := summ_Da a
  have hsa_c : Summable (fun x : ↑((↑s : Set ℤ))ᶜ => ‖a.toFun (x : ℤ)‖) :=
    hsa.subtype _
  have hsDa_c : Summable
      (fun x : ↑((↑s : Set ℤ))ᶜ => ‖(D a).toFun (x : ℤ)‖) := hsDa.subtype _
  have hterm : ∀ x : ↑((↑s : Set ℤ))ᶜ,
      ‖a.toFun (x : ℤ)‖ ≤ ‖(D a).toFun (x : ℤ)‖ / (Real.pi * ((N : ℝ) + 1)) := by
    intro x
    have hx : (x : ℤ) ∉ s := by
      have := x.2; simpa [hs_def, Finset.coe_Icc, Set.mem_compl_iff] using this
    exact coeff_tail_bound a N _ (mem_compl_abs N _ hx)
  calc ∑' x : ↑((↑s : Set ℤ))ᶜ, ‖a.toFun (x : ℤ)‖
      ≤ ∑' x : ↑((↑s : Set ℤ))ᶜ,
          ‖(D a).toFun (x : ℤ)‖ / (Real.pi * ((N : ℝ) + 1)) :=
        Summable.tsum_le_tsum hterm hsa_c (hsDa_c.div_const _)
    _ = (∑' x : ↑((↑s : Set ℤ))ᶜ, ‖(D a).toFun (x : ℤ)‖)
          / (Real.pi * ((N : ℝ) + 1)) := by rw [tsum_div_const]
    _ ≤ ‖D a‖ / (Real.pi * ((N : ℝ) + 1)) := by
        refine div_le_div_of_nonneg_right ?_ (le_of_lt hden)
        rw [normD_eq_tsum]
        have hsplit := hsDa.sum_add_tsum_compl (s := s)
        have hnonneg : 0 ≤ ∑ n ∈ s, ‖(D a).toFun n‖ :=
          Finset.sum_nonneg (fun n _ => norm_nonneg _)
        rw [← hsplit]; linarith

/-! ### Part 4 — `‖D(e^{−tf})‖ ≤ t‖Df‖·X` and the X-split. -/

/-- `‖D(e^{−tf})‖_{A⁰} ≤ t·‖Df‖·‖e^{−tf}‖_{A⁰}` (from `D_exp_neg_t`). -/
theorem normD_exp_le (f : WA 1) (t : ℝ) (ht : 0 ≤ t) :
    ‖D (NormedSpace.exp (((-t:ℝ):ℂ) • f))‖
      ≤ t * ‖D f‖ * ‖incl10 (NormedSpace.exp (((-t:ℝ):ℂ) • f))‖ := by
  have hcast : ((-t:ℝ):ℂ) = -((t : ℝ):ℂ) := by push_cast; ring
  rw [hcast, D_exp_neg_t ((t : ℝ):ℂ) f, norm_smul]
  have hnorm : ‖-((t : ℝ):ℂ)‖ = t := by
    rw [norm_neg, Complex.norm_real, Real.norm_of_nonneg ht]
  rw [hnorm]
  have hsub : ‖D f * incl10 (NormedSpace.exp (-((t : ℝ):ℂ) • f))‖
      ≤ ‖D f‖ * ‖incl10 (NormedSpace.exp (-((t : ℝ):ℂ) • f))‖ :=
    norm_mul_le _ _
  have ht0 : (0 : ℝ) ≤ t := ht
  calc t * ‖D f * incl10 (NormedSpace.exp (-((t : ℝ):ℂ) • f))‖
      ≤ t * (‖D f‖ * ‖incl10 (NormedSpace.exp (-((t : ℝ):ℂ) • f))‖) :=
        mul_le_mul_of_nonneg_left hsub ht0
    _ = t * ‖D f‖ * ‖incl10 (NormedSpace.exp (-((t : ℝ):ℂ) • f))‖ := by ring

/-- `Icc (-N) N` has `2N+1` elements. -/
theorem card_Icc_eq (N : ℕ) :
    ((Finset.Icc (-(N : ℤ)) (N : ℤ)).card : ℝ) = 2 * (N : ℝ) + 1 := by
  rw [Int.card_Icc]
  have : ((N : ℤ) + 1 - -(N : ℤ)).toNat = 2 * N + 1 := by omega
  rw [this]; push_cast; ring

/-- **The X-split.** Writing `X = ‖e^{−tf}‖_{A⁰}`, for every `N`,
`X ≤ (2N+1)·e^{−δt} + ‖D(e^{−tf})‖/(π(N+1))`. -/
theorem X_split (f : WA 1) (t δ : ℝ) (ht : 0 ≤ t)
    (hδ : ∀ x : Circ, δ ≤ (evalAt x (incl10 f)).re) (N : ℕ) :
    ‖incl10 (NormedSpace.exp (((-t:ℝ):ℂ) • f))‖
      ≤ (2 * (N : ℝ) + 1) * Real.exp (-δ * t)
        + ‖D (NormedSpace.exp (((-t:ℝ):ℂ) • f))‖ / (Real.pi * ((N : ℝ) + 1)) := by
  set g : WA 1 := NormedSpace.exp (((-t:ℝ):ℂ) • f) with hg_def
  set s : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ) with hs_def
  rw [normIncl_eq_tsum]
  have hsg := summ_a g
  have hsplit := hsg.sum_add_tsum_compl (s := s)
  rw [← hsplit]
  -- finite part bound
  have hfin : ∑ n ∈ s, ‖g.toFun n‖ ≤ (2 * (N : ℝ) + 1) * Real.exp (-δ * t) := by
    calc ∑ n ∈ s, ‖g.toFun n‖
        ≤ ∑ _n ∈ s, Real.exp (-δ * t) := by
          refine Finset.sum_le_sum (fun n _ => ?_)
          have := coeff_decay f t δ ht hδ n
          rwa [← hg_def] at this
      _ = (s.card : ℝ) * Real.exp (-δ * t) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (2 * (N : ℝ) + 1) * Real.exp (-δ * t) := by rw [hs_def, card_Icc_eq]
  -- tail bound
  have htail : ∑' x : ↑((↑s : Set ℤ))ᶜ, ‖g.toFun (x : ℤ)‖
      ≤ ‖D g‖ / (Real.pi * ((N : ℝ) + 1)) := tail_le_deriv g N
  linarith

/-! ### Part 5 — the mode-split absorption and the decisive estimate. -/

/-- **`mode_absorb`** (ChatGPT Step-4e skeleton).  From the per-`N` split
`X ≤ (2N+1)B + (tM/(π(N+1)))·X`, pick `N` (via `exists_nat_good`) so the
coefficient absorbs (`≤ 1/2`), giving `X ≤ 2(2N+1)B` with `(N+1) ≤ 2tM/π + 2`. -/
theorem mode_absorb {X B M t : ℝ} (hX : 0 ≤ X) (ht : 0 ≤ t) (hM : 0 ≤ M)
    (hsplit : ∀ N : ℕ, X ≤ (2 * (N : ℝ) + 1) * B
        + (t * M / (Real.pi * ((N : ℝ) + 1))) * X) :
    ∃ N : ℕ, X ≤ 2 * ((2 * (N : ℝ) + 1) * B)
      ∧ (N + 1 : ℝ) ≤ 2 * (t * M / Real.pi) + 2 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  set Y : ℝ := t * M / Real.pi with hY_def
  have hY : 0 ≤ Y := by rw [hY_def]; positivity
  obtain ⟨N, hcoef, hNup⟩ := exists_nat_good Y hY
  refine ⟨N, ?_, hNup⟩
  have hsN := hsplit N
  have hden : 0 < (N + 1 : ℝ) := by positivity
  have hc : t * M / (Real.pi * ((N : ℝ) + 1)) ≤ (1 / 2 : ℝ) := by
    have heq : t * M / (Real.pi * ((N : ℝ) + 1)) = Y / ((N : ℝ) + 1) := by
      rw [hY_def]; field_simp
    rw [heq]; exact hcoef
  exact absorb_le_half hX hc hsN

/-- **`X_bound`.**  The `A⁰`-norm of `e^{−tf}` obeys
`X ≤ (8 + 8/π)·(1 + t‖Df‖)·e^{−δt}` (the absorbed mode-split). -/
theorem X_bound (f : WA 1) (t δ : ℝ) (ht : 0 ≤ t)
    (hδ : ∀ x : Circ, δ ≤ (evalAt x (incl10 f)).re) :
    ‖incl10 (NormedSpace.exp (((-t:ℝ):ℂ) • f))‖
      ≤ (8 + 8 / Real.pi) * (1 + t * ‖D f‖) * Real.exp (-δ * t) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  set g : WA 1 := NormedSpace.exp (((-t:ℝ):ℂ) • f) with hg_def
  set X : ℝ := ‖incl10 g‖ with hX_def
  set B : ℝ := Real.exp (-δ * t) with hB_def
  set M : ℝ := ‖D f‖ with hM_def
  have hX0 : 0 ≤ X := norm_nonneg _
  have hM0 : 0 ≤ M := norm_nonneg _
  have hB0 : 0 ≤ B := le_of_lt (Real.exp_pos _)
  have htm : 0 ≤ t * M := mul_nonneg ht hM0
  have hsplit : ∀ N : ℕ, X ≤ (2 * (N : ℝ) + 1) * B
      + (t * M / (Real.pi * ((N : ℝ) + 1))) * X := by
    intro N
    have h1 := X_split f t δ ht hδ N
    have h2 := normD_exp_le f t ht
    rw [← hg_def, ← hX_def, ← hB_def] at h1
    rw [← hg_def, ← hX_def, ← hM_def] at h2
    have hden : 0 < Real.pi * ((N : ℝ) + 1) := by positivity
    have h3 : ‖D g‖ / (Real.pi * ((N : ℝ) + 1))
        ≤ (t * M * X) / (Real.pi * ((N : ℝ) + 1)) :=
      div_le_div_of_nonneg_right h2 (le_of_lt hden)
    have heq : (t * M * X) / (Real.pi * ((N : ℝ) + 1))
        = (t * M / (Real.pi * ((N : ℝ) + 1))) * X := by ring
    rw [heq] at h3
    linarith
  obtain ⟨N, hXle, hNup⟩ := mode_absorb hX0 ht hM0 hsplit
  have hcoef : 2 * (2 * (N : ℝ) + 1) ≤ (8 + 8 / Real.pi) * (1 + t * M) := by
    have hstep : 2 * (2 * (N : ℝ) + 1) ≤ 8 * (t * M) / Real.pi + 8 := by
      have h : 8 * (t * M) / Real.pi = 4 * (2 * (t * M / Real.pi)) := by ring
      rw [h]; linarith [hNup]
    have hC0 : 8 * (t * M) / Real.pi + 8 ≤ (8 + 8 / Real.pi) * (1 + t * M) := by
      have h8pi : (0 : ℝ) ≤ 8 / Real.pi := by positivity
      have key : 8 * (t * M) / Real.pi = (8 / Real.pi) * (t * M) := by ring
      rw [key]
      have hexp : (8 + 8 / Real.pi) * (1 + t * M)
          = 8 + 8 * (t * M) + 8 / Real.pi + (8 / Real.pi) * (t * M) := by ring
      rw [hexp]; nlinarith [htm, h8pi]
    linarith
  calc X ≤ 2 * ((2 * (N : ℝ) + 1) * B) := hXle
    _ = (2 * (2 * (N : ℝ) + 1)) * B := by ring
    _ ≤ ((8 + 8 / Real.pi) * (1 + t * M)) * B := mul_le_mul_of_nonneg_right hcoef hB0
    _ = (8 + 8 / Real.pi) * (1 + t * M) * B := by ring

/-- **`decisive_exp_bound` — THE DECISIVE ESTIMATE.**
With the spectral floor `δ ≤ Re(evalAt x (incl10 f))` and `0 ≤ t`,
`‖e^{−tf}‖_{WA 1} ≤ C·(1 + t‖Df‖)²·e^{−δt}` with explicit
`C = 8·(1 + 1/π)²`. -/
theorem decisive_exp_bound (f : WA 1) (t δ : ℝ) (ht : 0 ≤ t)
    (hδ : ∀ x : Circ, δ ≤ (evalAt x (incl10 f)).re) :
    ‖NormedSpace.exp (((-t:ℝ):ℂ) • f)‖
      ≤ (8 * (1 + 1 / Real.pi) ^ 2) * (1 + t * ‖D f‖) ^ 2 * Real.exp (-δ * t) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  set g : WA 1 := NormedSpace.exp (((-t:ℝ):ℂ) • f) with hg_def
  set X : ℝ := ‖incl10 g‖ with hX_def
  set B : ℝ := Real.exp (-δ * t) with hB_def
  set M : ℝ := ‖D f‖ with hM_def
  have hX0 : 0 ≤ X := norm_nonneg _
  have hM0 : 0 ≤ M := norm_nonneg _
  have hB0 : 0 ≤ B := le_of_lt (Real.exp_pos _)
  have htm : 0 ≤ t * M := mul_nonneg ht hM0
  have Xbnd : X ≤ (8 + 8 / Real.pi) * (1 + t * M) * B := X_bound f t δ ht hδ
  have hsplit := wNorm1_split g
  have hDg := normD_exp_le f t ht
  rw [← hg_def, ← hX_def, ← hM_def] at hDg
  -- ‖g‖ ≤ (1 + tM/π)·X
  have hg_le : ‖g‖ ≤ (1 + t * M / Real.pi) * X := by
    rw [hsplit]
    have h1 : (1 / Real.pi) * ‖D g‖ ≤ (1 / Real.pi) * (t * M * X) :=
      mul_le_mul_of_nonneg_left hDg (by positivity)
    have heq : X + (1 / Real.pi) * (t * M * X) = (1 + t * M / Real.pi) * X := by ring
    rw [← hX_def]; linarith [h1, heq.le, heq.symm.le]
  -- (1 + tM/π) ≤ (1 + 1/π)(1 + tM)
  have hfac : (1 + t * M / Real.pi) ≤ (1 + 1 / Real.pi) * (1 + t * M) := by
    have h1pi : (0 : ℝ) ≤ 1 / Real.pi := by positivity
    have hexp : (1 + 1 / Real.pi) * (1 + t * M)
        = 1 + t * M + 1 / Real.pi + (1 / Real.pi) * (t * M) := by ring
    have hkey : t * M / Real.pi = (1 / Real.pi) * (t * M) := by ring
    rw [hexp, hkey]; nlinarith [htm, h1pi]
  have hXnn : 0 ≤ (1 + 1 / Real.pi) * (1 + t * M) := by positivity
  have step1 : ‖g‖ ≤ (1 + 1 / Real.pi) * (1 + t * M) * X := by
    calc ‖g‖ ≤ (1 + t * M / Real.pi) * X := hg_le
      _ ≤ (1 + 1 / Real.pi) * (1 + t * M) * X := mul_le_mul_of_nonneg_right hfac hX0
  have step2 : (1 + 1 / Real.pi) * (1 + t * M) * X
      ≤ (1 + 1 / Real.pi) * (1 + t * M) * ((8 + 8 / Real.pi) * (1 + t * M) * B) :=
    mul_le_mul_of_nonneg_left Xbnd hXnn
  have hC : (1 + 1 / Real.pi) * (1 + t * M) * ((8 + 8 / Real.pi) * (1 + t * M) * B)
      = (8 * (1 + 1 / Real.pi) ^ 2) * (1 + t * M) ^ 2 * B := by ring
  calc ‖g‖ ≤ (1 + 1 / Real.pi) * (1 + t * M) * X := step1
    _ ≤ (1 + 1 / Real.pi) * (1 + t * M) * ((8 + 8 / Real.pi) * (1 + t * M) * B) := step2
    _ = (8 * (1 + 1 / Real.pi) ^ 2) * (1 + t * M) ^ 2 * B := hC

end WA

end ShenWork.Wiener
