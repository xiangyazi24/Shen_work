import ShenWork.Wiener.EWA.Duhamel
import ShenWork.Wiener.WeightedL1Decisive

/-!
# EWA brick B2 — THE EWA DECISIVE ESTIMATE (cron2 Brick 5)

`‖e^{−sf}‖_{EWA 1} ≤ C·(1 + s‖gDeriv f‖)²·e^{−δs}` on the time-envelope algebra
`EWA T r := GWA (CT T) r`, the EWA analogue of the committed
`WA.decisive_exp_bound` (`ShenWork/Wiener/WeightedL1Decisive.lean`, the TEMPLATE).

The ONLY genuinely-new step is **`EWA_coeff_decay`**: the EWA coefficient norm is
the `CT` sup-norm `‖(…).toFun n‖ = sup_τ ‖((…).toFun n) τ‖`, and pointwise-in-time
`((incl(exp((-s)•f))).toFun n) τ = (incl10 (exp((-s)•(sliceWA τ f)))).toFun n`
(via `coeff_sliceWA` + `sliceWA_exp` + slice commutes with `incl`/`•`), so the
committed `WA.coeff_decay` at the slice `sliceWA τ f` gives `≤ e^{−δs}` for every
`τ`; the sup over `τ` (`ContinuousMap.norm_le`) keeps the bound.  This is cron's
"EWA decay = sup_τ static-WA decay".

The rest mirrors `WA.decisive_exp_bound` with EWA norms and `gDeriv`/`gIncl` in
place of the `WA` `D`/`incl10`, reusing the K-independent scalar mode-split lemmas
`WA.exists_nat_good` / `WA.absorb_le_half`.
-/

open scoped BigOperators
open ShenWork.GWA ShenWork.Wiener

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-! ### Part 0 — space-time evaluation and the uniform spectral floor. -/

/-- **Space-time point evaluation** `EWA T 0 →+* ℂ`: slice the time-coefficients
at time `τ` (landing in `WA 0`), then evaluate the resulting Fourier series at
the spatial point `x : WA.Circ`. -/
def evalST (τ : TimeDom T) (x : WA.Circ) : EWA T 0 →+* ℂ :=
  (WA.evalAt x).comp (sliceWA τ).toRingHom

@[simp] theorem evalST_apply (τ : TimeDom T) (x : WA.Circ) (a : EWA T 0) :
    evalST τ x a = WA.evalAt x (sliceWA τ a) := rfl

/-- **The uniform spectral floor.** `f : EWA T 1` has floor `δ` if at every time
`τ` and spatial point `x` the included symbol has real part `≥ δ`. -/
def UniformFloor (f : EWA T 1) (δ : ℝ) : Prop :=
  ∀ (τ : TimeDom T) (x : WA.Circ),
    δ ≤ (evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) f)).re

/-! ### Part 1 — slice compatibilities (slice commutes with `incl` and `•`). -/

/-- Slicing the EWA inclusion gives the committed `WA` inclusion of the slice:
`sliceWA τ (incl h f) = incl10 (sliceWA τ f)` (both have the unchanged
underlying sequence, evaluated at `τ`). -/
theorem sliceWA_incl (τ : TimeDom T) (f : EWA T 1) :
    sliceWA τ (GWA.incl (by omega : (0:ℕ) ≤ 1) f) = WA.incl10 (sliceWA τ f) := by
  apply WA.ext; funext n
  rw [coeff_sliceWA, WA.incl10_toFun, GWA.incl_toFun, coeff_sliceWA]

/-! ### Part 2 — THE ONLY GENUINELY-NEW STEP: `EWA_coeff_decay`. -/

/-- **`EWA_coeff_decay` (the sliceWA central trick).**  Under the uniform floor
`δ`, every EWA Fourier coefficient of `e^{−sf}` has `CT` sup-norm `≤ e^{−δs}`.
The EWA coefficient norm is the `CT` sup-norm; pointwise-in-time the coefficient
is the committed `WA` coefficient of `e^{−s·(sliceWA τ f)}` (via `sliceWA_exp` +
`sliceWA_incl` + `map_smul`), to which `WA.coeff_decay` applies with the floor at
`τ`.  `sup_τ` (`ContinuousMap.norm_le`) keeps the bound `e^{−δs} ≥ 0`. -/
theorem EWA_coeff_decay (f : EWA T 1) (s δ : ℝ) (hs : 0 ≤ s)
    (hf : UniformFloor f δ) (n : ℤ) :
    ‖(GWA.incl (by omega : (0:ℕ) ≤ 1)
        (NormedSpace.exp (((-s:ℝ):ℂ) • f))).toFun n‖ ≤ Real.exp (-δ * s) := by
  set g : EWA T 1 := NormedSpace.exp (((-s:ℝ):ℂ) • f) with hg_def
  have hBnn : (0 : ℝ) ≤ Real.exp (-δ * s) := le_of_lt (Real.exp_pos _)
  -- the EWA coefficient norm is the CT sup-norm; bound it via norm_le.
  rw [ContinuousMap.norm_le _ hBnn]
  intro τ
  -- pointwise-in-time: ((incl g).toFun n) τ = (incl10 (exp((-s)•(sliceWA τ f)))).toFun n.
  have hpt : ((GWA.incl (by omega : (0:ℕ) ≤ 1) g).toFun n) τ
      = (WA.incl10 (NormedSpace.exp (((-s:ℝ):ℂ) • sliceWA τ f))).toFun n := by
    have h1 : ((GWA.incl (by omega : (0:ℕ) ≤ 1) g).toFun n) τ
        = (sliceWA τ (GWA.incl (by omega : (0:ℕ) ≤ 1) g)).toFun n := by
      rw [coeff_sliceWA]
    rw [h1, sliceWA_incl, hg_def, sliceWA_exp, map_smul (sliceWA τ)]
  rw [hpt]
  -- WA.coeff_decay at the slice, with the floor at τ.
  have hδτ : ∀ x : WA.Circ, δ ≤ (WA.evalAt x (WA.incl10 (sliceWA τ f))).re := by
    intro x
    have := hf τ x
    rwa [evalST_apply, sliceWA_incl] at this
  exact WA.coeff_decay (sliceWA τ f) s δ hs hδτ n

/-! ### Part 3 — norm bridges and the `‖·‖_{EWA 1}` split (generic, EWA norms). -/

/-- `‖incl h a‖_{EWA 0} = ∑'_n ‖a.toFun n‖` (the `gWeight 0` weight is `1`). -/
theorem normIncl_eq_tsum (a : EWA T 1) :
    ‖GWA.incl (by omega : (0:ℕ) ≤ 1) a‖ = ∑' n : ℤ, ‖a.toFun n‖ := by
  rw [GWA.norm_def, GWA.gNorm]
  refine tsum_congr (fun n => ?_)
  rw [GWA.incl_toFun]; simp [GWA.gWeight]

/-- `‖gDeriv a‖_{EWA 0} = ∑'_n ‖(gDeriv a).toFun n‖`. -/
theorem normD_eq_tsum (a : EWA T 1) :
    ‖GWA.gDeriv a‖ = ∑' n : ℤ, ‖(GWA.gDeriv a).toFun n‖ := by
  rw [GWA.norm_def, GWA.gNorm]
  refine tsum_congr (fun n => ?_); simp [GWA.gWeight]

/-- The `EWA 0`-summability of the coefficients of `a : EWA T 1`. -/
theorem summ_a (a : EWA T 1) : Summable (fun n => ‖a.toFun n‖) := by
  have hm0 : GMemW 0 a.toFun := by
    have := (GWA.incl (by omega : (0:ℕ) ≤ 1) a).mem
    rwa [GWA.incl_toFun] at this
  rw [GMemW] at hm0; simpa [GWA.gWeight] using hm0

/-- The `EWA 0`-summability of the derivative coefficients. -/
theorem summ_Da (a : EWA T 1) : Summable (fun n => ‖(GWA.gDeriv a).toFun n‖) := by
  have hm0 : GMemW 0 (GWA.gDeriv a).toFun := (GWA.gDeriv a).mem
  rw [GMemW] at hm0; simpa [GWA.gWeight] using hm0

/-- The summability of `|n|‖a_n‖` (the weighted half of `EWA 1`). -/
theorem summ_na (a : EWA T 1) :
    Summable (fun n : ℤ => |(n : ℝ)| * ‖a.toFun n‖) := by
  have hsum1 : Summable (fun n => GWA.gWeight 1 n * ‖a.toFun n‖) := a.mem
  have hsa := summ_a a
  have : (fun n : ℤ => |(n : ℝ)| * ‖a.toFun n‖)
      = fun n : ℤ => GWA.gWeight 1 n * ‖a.toFun n‖ - ‖a.toFun n‖ := by
    funext n; simp [GWA.gWeight]; ring
  rw [this]; exact hsum1.sub hsa

/-- The `EWA 0` norm of a derivative coefficient: `‖(gDeriv a)_n‖ = π|n|·‖a_n‖`. -/
theorem normDcoeff (a : EWA T 1) (n : ℤ) :
    ‖(GWA.gDeriv a).toFun n‖ = Real.pi * |(n : ℝ)| * ‖a.toFun n‖ := by
  rw [GWA.gDeriv_toFun, norm_smul]
  rw [show (Complex.I * Real.pi * (n : ℂ)) = Complex.I * ((Real.pi : ℂ) * (n : ℂ)) by ring,
    norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_nonneg, Complex.norm_intCast]

/-- `‖gDeriv a‖_{EWA 0} = π · ∑'_n |n|‖a_n‖`. -/
theorem normD_eq_pi (a : EWA T 1) :
    ‖GWA.gDeriv a‖ = Real.pi * ∑' n : ℤ, |(n : ℝ)| * ‖a.toFun n‖ := by
  rw [normD_eq_tsum]
  have hco : (fun n => ‖(GWA.gDeriv a).toFun n‖)
      = fun n : ℤ => Real.pi * (|(n : ℝ)| * ‖a.toFun n‖) := by
    funext n; rw [normDcoeff]; ring
  rw [hco, tsum_mul_left]

/-- **`wNorm1_split`** (EWA). `‖a‖_{EWA 1} = ‖incl a‖_{EWA 0} + (1/π)‖gDeriv a‖_{EWA 0}`. -/
theorem wNorm1_split (a : EWA T 1) :
    ‖a‖ = ‖GWA.incl (by omega : (0:ℕ) ≤ 1) a‖ + (1 / Real.pi) * ‖GWA.gDeriv a‖ := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  rw [normD_eq_pi, GWA.norm_def, GWA.gNorm, normIncl_eq_tsum]
  have hsa := summ_a a
  have hsna := summ_na a
  have hsplit : (fun n => GWA.gWeight 1 n * ‖a.toFun n‖)
      = fun n : ℤ => ‖a.toFun n‖ + |(n : ℝ)| * ‖a.toFun n‖ := by
    funext n; simp [GWA.gWeight]; ring
  rw [hsplit, Summable.tsum_add hsa hsna]
  field_simp

/-! ### Part 4 — the tail-via-derivative subset `tsum` and the deriv-exp bound. -/

/-- For `|n| ≥ N+1`, `‖a_n‖ ≤ ‖(gDeriv a)_n‖ / (π(N+1))`. -/
theorem coeff_tail_bound (a : EWA T 1) (N : ℕ) (n : ℤ)
    (hn : (N : ℝ) + 1 ≤ |(n : ℝ)|) :
    ‖a.toFun n‖ ≤ ‖(GWA.gDeriv a).toFun n‖ / (Real.pi * ((N : ℝ) + 1)) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [normDcoeff]
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

/-- **`tail_le_deriv`** (EWA). The `EWA 0`-tail over `|n| > N` is bounded by the
derivative norm: `∑'_{n∉Icc(-N,N)} ‖a_n‖ ≤ ‖gDeriv a‖ / (π(N+1))`. -/
theorem tail_le_deriv (a : EWA T 1) (N : ℕ) :
    ∑' x : ↑((↑(Finset.Icc (-(N : ℤ)) (N : ℤ)) : Set ℤ))ᶜ, ‖a.toFun (x : ℤ)‖
      ≤ ‖GWA.gDeriv a‖ / (Real.pi * ((N : ℝ) + 1)) := by
  have hden : 0 < Real.pi * ((N : ℝ) + 1) := by positivity
  set s : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ) with hs_def
  have hsa := summ_a a
  have hsDa := summ_Da a
  have hsa_c : Summable (fun x : ↑((↑s : Set ℤ))ᶜ => ‖a.toFun (x : ℤ)‖) :=
    hsa.subtype _
  have hsDa_c : Summable
      (fun x : ↑((↑s : Set ℤ))ᶜ => ‖(GWA.gDeriv a).toFun (x : ℤ)‖) := hsDa.subtype _
  have hterm : ∀ x : ↑((↑s : Set ℤ))ᶜ,
      ‖a.toFun (x : ℤ)‖
        ≤ ‖(GWA.gDeriv a).toFun (x : ℤ)‖ / (Real.pi * ((N : ℝ) + 1)) := by
    intro x
    have hx : (x : ℤ) ∉ s := by
      have := x.2; simpa [hs_def, Finset.coe_Icc, Set.mem_compl_iff] using this
    exact coeff_tail_bound a N _ (mem_compl_abs N _ hx)
  calc ∑' x : ↑((↑s : Set ℤ))ᶜ, ‖a.toFun (x : ℤ)‖
      ≤ ∑' x : ↑((↑s : Set ℤ))ᶜ,
          ‖(GWA.gDeriv a).toFun (x : ℤ)‖ / (Real.pi * ((N : ℝ) + 1)) :=
        Summable.tsum_le_tsum hterm hsa_c (hsDa_c.div_const _)
    _ = (∑' x : ↑((↑s : Set ℤ))ᶜ, ‖(GWA.gDeriv a).toFun (x : ℤ)‖)
          / (Real.pi * ((N : ℝ) + 1)) := by rw [tsum_div_const]
    _ ≤ ‖GWA.gDeriv a‖ / (Real.pi * ((N : ℝ) + 1)) := by
        refine div_le_div_of_nonneg_right ?_ (le_of_lt hden)
        rw [normD_eq_tsum]
        have hsplit := hsDa.sum_add_tsum_compl (s := s)
        have hnonneg : 0 ≤ ∑ n ∈ s, ‖(GWA.gDeriv a).toFun n‖ :=
          Finset.sum_nonneg (fun n _ => norm_nonneg _)
        rw [← hsplit]; linarith

/-- `‖gDeriv(e^{−tf})‖_{EWA 0} ≤ t·‖gDeriv f‖·‖incl(e^{−tf})‖_{EWA 0}` (from
`gD_exp_neg_t`). -/
theorem normD_exp_le (f : EWA T 1) (t : ℝ) (ht : 0 ≤ t) :
    ‖GWA.gDeriv (NormedSpace.exp (((-t:ℝ):ℂ) • f))‖
      ≤ t * ‖GWA.gDeriv f‖
        * ‖GWA.incl (by omega : (0:ℕ) ≤ 1) (NormedSpace.exp (((-t:ℝ):ℂ) • f))‖ := by
  have hcast : ((-t:ℝ):ℂ) = -((t : ℝ):ℂ) := by push_cast; ring
  rw [hcast, GWA.gD_exp_neg_t ((t : ℝ):ℂ) f, norm_smul]
  have hnorm : ‖-((t : ℝ):ℂ)‖ = t := by
    rw [norm_neg, Complex.norm_real, Real.norm_of_nonneg ht]
  rw [hnorm]
  have hsub : ‖GWA.gDeriv f * GWA.gIncl (by omega : (0:ℕ) ≤ 1)
        (NormedSpace.exp (-((t : ℝ):ℂ) • f))‖
      ≤ ‖GWA.gDeriv f‖ * ‖GWA.gIncl (by omega : (0:ℕ) ≤ 1)
        (NormedSpace.exp (-((t : ℝ):ℂ) • f))‖ := norm_mul_le _ _
  calc t * ‖GWA.gDeriv f * GWA.gIncl (by omega : (0:ℕ) ≤ 1)
        (NormedSpace.exp (-((t : ℝ):ℂ) • f))‖
      ≤ t * (‖GWA.gDeriv f‖ * ‖GWA.gIncl (by omega : (0:ℕ) ≤ 1)
        (NormedSpace.exp (-((t : ℝ):ℂ) • f))‖) :=
        mul_le_mul_of_nonneg_left hsub ht
    _ = t * ‖GWA.gDeriv f‖ * ‖GWA.incl (by omega : (0:ℕ) ≤ 1)
        (NormedSpace.exp (-((t : ℝ):ℂ) • f))‖ := by rw [GWA.gIncl_apply]; ring

/-- `Icc (-N) N` has `2N+1` elements. -/
theorem card_Icc_eq (N : ℕ) :
    ((Finset.Icc (-(N : ℤ)) (N : ℤ)).card : ℝ) = 2 * (N : ℝ) + 1 := by
  rw [Int.card_Icc]
  have : ((N : ℤ) + 1 - -(N : ℤ)).toNat = 2 * N + 1 := by omega
  rw [this]; push_cast; ring

/-! ### Part 5 — the mode-split absorption and the EWA decisive estimate. -/

/-- **The X-split.** With `X = ‖e^{−sf}‖_{EWA 0}`, for every `N`,
`X ≤ (2N+1)·e^{−δs} + ‖gDeriv(e^{−sf})‖/(π(N+1))`. -/
theorem X_split (f : EWA T 1) (s δ : ℝ) (hs : 0 ≤ s) (hf : UniformFloor f δ) (N : ℕ) :
    ‖GWA.incl (by omega : (0:ℕ) ≤ 1) (NormedSpace.exp (((-s:ℝ):ℂ) • f))‖
      ≤ (2 * (N : ℝ) + 1) * Real.exp (-δ * s)
        + ‖GWA.gDeriv (NormedSpace.exp (((-s:ℝ):ℂ) • f))‖
            / (Real.pi * ((N : ℝ) + 1)) := by
  set g : EWA T 1 := NormedSpace.exp (((-s:ℝ):ℂ) • f) with hg_def
  set t : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ) with ht_def
  rw [normIncl_eq_tsum]
  have hsg := summ_a g
  have hsplit := hsg.sum_add_tsum_compl (s := t)
  rw [← hsplit]
  have hfin : ∑ n ∈ t, ‖g.toFun n‖ ≤ (2 * (N : ℝ) + 1) * Real.exp (-δ * s) := by
    calc ∑ n ∈ t, ‖g.toFun n‖
        ≤ ∑ _n ∈ t, Real.exp (-δ * s) := by
          refine Finset.sum_le_sum (fun n _ => ?_)
          have hc := EWA_coeff_decay f s δ hs hf n
          rw [← hg_def, GWA.incl_toFun] at hc; exact hc
      _ = (t.card : ℝ) * Real.exp (-δ * s) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (2 * (N : ℝ) + 1) * Real.exp (-δ * s) := by rw [ht_def, card_Icc_eq]
  have htail : ∑' x : ↑((↑t : Set ℤ))ᶜ, ‖g.toFun (x : ℤ)‖
      ≤ ‖GWA.gDeriv g‖ / (Real.pi * ((N : ℝ) + 1)) := tail_le_deriv g N
  linarith

/-- **`X_bound`.** The `EWA 0`-norm of `e^{−sf}` obeys
`X ≤ (8 + 8/π)·(1 + s‖gDeriv f‖)·e^{−δs}` (the absorbed mode-split, reusing the
scalar lemmas `WA.exists_nat_good`/`WA.absorb_le_half`). -/
theorem X_bound (f : EWA T 1) (s δ : ℝ) (hs : 0 ≤ s) (hf : UniformFloor f δ) :
    ‖GWA.incl (by omega : (0:ℕ) ≤ 1) (NormedSpace.exp (((-s:ℝ):ℂ) • f))‖
      ≤ (8 + 8 / Real.pi) * (1 + s * ‖GWA.gDeriv f‖) * Real.exp (-δ * s) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  set g : EWA T 1 := NormedSpace.exp (((-s:ℝ):ℂ) • f) with hg_def
  set X : ℝ := ‖GWA.incl (by omega : (0:ℕ) ≤ 1) g‖ with hX_def
  set B : ℝ := Real.exp (-δ * s) with hB_def
  set M : ℝ := ‖GWA.gDeriv f‖ with hM_def
  have hX0 : 0 ≤ X := norm_nonneg _
  have hM0 : 0 ≤ M := norm_nonneg _
  have hB0 : 0 ≤ B := le_of_lt (Real.exp_pos _)
  have hsm : 0 ≤ s * M := mul_nonneg hs hM0
  have hsplit : ∀ N : ℕ, X ≤ (2 * (N : ℝ) + 1) * B
      + (s * M / (Real.pi * ((N : ℝ) + 1))) * X := by
    intro N
    have h1 := X_split f s δ hs hf N
    have h2 := normD_exp_le f s hs
    rw [← hg_def, ← hX_def, ← hB_def] at h1
    rw [← hg_def, ← hX_def, ← hM_def] at h2
    have hden : 0 < Real.pi * ((N : ℝ) + 1) := by positivity
    have h3 : ‖GWA.gDeriv g‖ / (Real.pi * ((N : ℝ) + 1))
        ≤ (s * M * X) / (Real.pi * ((N : ℝ) + 1)) :=
      div_le_div_of_nonneg_right h2 (le_of_lt hden)
    have heq : (s * M * X) / (Real.pi * ((N : ℝ) + 1))
        = (s * M / (Real.pi * ((N : ℝ) + 1))) * X := by ring
    rw [heq] at h3
    linarith
  -- mode_absorb via the scalar lemmas WA.exists_nat_good / WA.absorb_le_half.
  obtain ⟨N, hcoef, hNup⟩ := WA.exists_nat_good (s * M / Real.pi) (by positivity)
  have hc : s * M / (Real.pi * ((N : ℝ) + 1)) ≤ (1 / 2 : ℝ) := by
    have heq : s * M / (Real.pi * ((N : ℝ) + 1))
        = (s * M / Real.pi) / ((N : ℝ) + 1) := by field_simp
    rw [heq]; exact hcoef
  have hXle : X ≤ 2 * ((2 * (N : ℝ) + 1) * B) := by
    have := WA.absorb_le_half hX0 hc (hsplit N)
    calc X ≤ 2 * ((2 * (N : ℝ) + 1) * B + 0) := by
            have h0 := WA.absorb_le_half hX0 hc (hsplit N); linarith
      _ = 2 * ((2 * (N : ℝ) + 1) * B) := by ring
  have hNup2 : (N + 1 : ℝ) ≤ 2 * (s * M / Real.pi) + 2 := hNup
  have hcoef2 : 2 * (2 * (N : ℝ) + 1) ≤ (8 + 8 / Real.pi) * (1 + s * M) := by
    have hstep : 2 * (2 * (N : ℝ) + 1) ≤ 8 * (s * M) / Real.pi + 8 := by
      have h : 8 * (s * M) / Real.pi = 4 * (2 * (s * M / Real.pi)) := by ring
      rw [h]; linarith [hNup2]
    have hC0 : 8 * (s * M) / Real.pi + 8 ≤ (8 + 8 / Real.pi) * (1 + s * M) := by
      have h8pi : (0 : ℝ) ≤ 8 / Real.pi := by positivity
      have key : 8 * (s * M) / Real.pi = (8 / Real.pi) * (s * M) := by ring
      rw [key]
      have hexp : (8 + 8 / Real.pi) * (1 + s * M)
          = 8 + 8 * (s * M) + 8 / Real.pi + (8 / Real.pi) * (s * M) := by ring
      rw [hexp]; nlinarith [hsm, h8pi]
    linarith
  calc X ≤ 2 * ((2 * (N : ℝ) + 1) * B) := hXle
    _ = (2 * (2 * (N : ℝ) + 1)) * B := by ring
    _ ≤ ((8 + 8 / Real.pi) * (1 + s * M)) * B := mul_le_mul_of_nonneg_right hcoef2 hB0
    _ = (8 + 8 / Real.pi) * (1 + s * M) * B := by ring

/-- **`EWA_decisive_exp_bound` — THE EWA DECISIVE ESTIMATE.**
Under the uniform spectral floor `δ` and `0 ≤ s`,
`‖e^{−sf}‖_{EWA 1} ≤ C·(1 + s‖gDeriv f‖)²·e^{−δs}` with explicit
`C = 8·(1 + 1/π)²`. -/
theorem EWA_decisive_exp_bound (f : EWA T 1) (s δ : ℝ) (hs : 0 ≤ s)
    (hf : UniformFloor f δ) :
    ‖NormedSpace.exp (((-s:ℝ):ℂ) • f)‖
      ≤ (8 * (1 + 1 / Real.pi) ^ 2) * (1 + s * ‖GWA.gDeriv f‖) ^ 2
          * Real.exp (-δ * s) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  set g : EWA T 1 := NormedSpace.exp (((-s:ℝ):ℂ) • f) with hg_def
  set X : ℝ := ‖GWA.incl (by omega : (0:ℕ) ≤ 1) g‖ with hX_def
  set B : ℝ := Real.exp (-δ * s) with hB_def
  set M : ℝ := ‖GWA.gDeriv f‖ with hM_def
  have hX0 : 0 ≤ X := norm_nonneg _
  have hM0 : 0 ≤ M := norm_nonneg _
  have hB0 : 0 ≤ B := le_of_lt (Real.exp_pos _)
  have hsm : 0 ≤ s * M := mul_nonneg hs hM0
  have Xbnd : X ≤ (8 + 8 / Real.pi) * (1 + s * M) * B := X_bound f s δ hs hf
  have hsplit := wNorm1_split g
  have hDg := normD_exp_le f s hs
  rw [← hg_def, ← hX_def, ← hM_def] at hDg
  have hg_le : ‖g‖ ≤ (1 + s * M / Real.pi) * X := by
    rw [hsplit]
    have h1 : (1 / Real.pi) * ‖GWA.gDeriv g‖ ≤ (1 / Real.pi) * (s * M * X) :=
      mul_le_mul_of_nonneg_left hDg (by positivity)
    have heq : X + (1 / Real.pi) * (s * M * X) = (1 + s * M / Real.pi) * X := by ring
    rw [← hX_def]; linarith [h1, heq.le, heq.symm.le]
  have hfac : (1 + s * M / Real.pi) ≤ (1 + 1 / Real.pi) * (1 + s * M) := by
    have h1pi : (0 : ℝ) ≤ 1 / Real.pi := by positivity
    have hexp : (1 + 1 / Real.pi) * (1 + s * M)
        = 1 + s * M + 1 / Real.pi + (1 / Real.pi) * (s * M) := by ring
    have hkey : s * M / Real.pi = (1 / Real.pi) * (s * M) := by ring
    rw [hexp, hkey]; nlinarith [hsm, h1pi]
  have hXnn : 0 ≤ (1 + 1 / Real.pi) * (1 + s * M) := by positivity
  have step1 : ‖g‖ ≤ (1 + 1 / Real.pi) * (1 + s * M) * X := by
    calc ‖g‖ ≤ (1 + s * M / Real.pi) * X := hg_le
      _ ≤ (1 + 1 / Real.pi) * (1 + s * M) * X := mul_le_mul_of_nonneg_right hfac hX0
  have step2 : (1 + 1 / Real.pi) * (1 + s * M) * X
      ≤ (1 + 1 / Real.pi) * (1 + s * M) * ((8 + 8 / Real.pi) * (1 + s * M) * B) :=
    mul_le_mul_of_nonneg_left Xbnd hXnn
  have hC : (1 + 1 / Real.pi) * (1 + s * M) * ((8 + 8 / Real.pi) * (1 + s * M) * B)
      = (8 * (1 + 1 / Real.pi) ^ 2) * (1 + s * M) ^ 2 * B := by ring
  calc ‖g‖ ≤ (1 + 1 / Real.pi) * (1 + s * M) * X := step1
    _ ≤ (1 + 1 / Real.pi) * (1 + s * M) * ((8 + 8 / Real.pi) * (1 + s * M) * B) := step2
    _ = (8 * (1 + 1 / Real.pi) ^ 2) * (1 + s * M) ^ 2 * B := hC

end ShenWork.EWA

#print axioms ShenWork.EWA.EWA_coeff_decay
#print axioms ShenWork.EWA.EWA_decisive_exp_bound
