import ShenWork.Wiener.EWA.WienerLevy

/-!
# EWA brick — `ExpLipschitz`: the segment mean-value exp difference bound (cron2)

The one new calculus lemma feeding the EWA flux fixed-point contraction: a
segment mean-value estimate for the difference of two Banach-algebra exponentials
`e^{−tf}` and `e^{−tg}` in the commutative Banach algebra `EWA T 1`.

The route uses the commutative one-parameter group.  With the convex segment
`seg f g θ = g + θ•(f−g)` (so `seg 0 = g`, `seg 1 = f`), set
`φ θ := exp((-t)•seg f g θ)`.  Since `EWA T 1` is a `NormedCommRing`, everything
commutes, so `φ θ = exp((-t)•g) * exp(θ•B)` with `B = (-t)•(f−g)`, and
`hasDerivAt_exp_smul_const` plus the product rule give
`φ' θ = B * φ θ`, whence `‖φ' θ‖ ≤ t‖f−g‖·‖φ θ‖`.  The committed decisive estimate
`EWA_decisive_exp_bound` (applied at `seg f g θ`, with the floor/derivative bounds
propagated convexly by `UniformFloor_seg` / `gDeriv_seg_le`) bounds `‖φ θ‖`, and
the Mathlib segment mean-value inequality
`norm_image_sub_le_of_norm_deriv_le_segment_01'` closes
`‖φ 1 − φ 0‖ ≤ sup_{[0,1]} ‖φ'‖`.
-/

open scoped BigOperators
open ShenWork.GWA ShenWork.Wiener

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-! ### Part 1 — the convex segment and its floor / derivative propagation.

The `ℝ`-normed-algebra structure on `EWA T 1` (needed by the `ℝ`-parameter exp
derivative `hasDerivAt_exp_smul_const`) is the canonical restrict-scalars one
from Mathlib's `NormedAlgebra.complexToReal` (priority-900 instance), inferred
automatically — no custom instance, hence no scalar diamond. -/

/-- The convex segment `seg f g θ = g + θ•(f − g)` (so `seg 0 = g`, `seg 1 = f`). -/
def seg (f g : EWA T 1) (θ : ℝ) : EWA T 1 := g + ((θ : ℝ) : ℂ) • (f - g)

@[simp] theorem seg_zero (f g : EWA T 1) : seg f g 0 = g := by
  simp [seg]

@[simp] theorem seg_one (f g : EWA T 1) : seg f g 1 = f := by
  simp only [seg, Complex.ofReal_one, one_smul]; abel

/-- The uniform spectral floor propagates through the convex segment: a convex
combination of the two floors stays above `δ`. -/
theorem UniformFloor_seg {f g : EWA T 1} {δ θ : ℝ}
    (hf : UniformFloor f δ) (hg : UniformFloor g δ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    UniformFloor (seg f g θ) δ := by
  intro τ x
  -- route through the ℂ-linear `evalSTCLM` so `map_add/smul/sub` are available.
  have hbridge : ∀ a : EWA T 1,
      evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) a) = evalSTCLM τ x a :=
    fun a => (evalSTCLM_apply τ x a).symm
  rw [hbridge]
  have hlin : evalSTCLM τ x (seg f g θ)
      = evalSTCLM τ x g + ((θ : ℝ) : ℂ) * (evalSTCLM τ x f - evalSTCLM τ x g) := by
    rw [seg, map_add, map_smul, map_sub, smul_eq_mul]
  set Ef := evalSTCLM τ x f with hEf
  set Eg := evalSTCLM τ x g with hEg
  have hRre : (evalSTCLM τ x (seg f g θ)).re = Eg.re + θ * (Ef.re - Eg.re) := by
    rw [hlin]
    simp only [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_im, zero_mul, sub_zero]
  have hfre : δ ≤ Ef.re := by rw [hEf, evalSTCLM_apply]; exact hf τ x
  have hgre : δ ≤ Eg.re := by rw [hEg, evalSTCLM_apply]; exact hg τ x
  rw [hRre]
  nlinarith [hfre, hgre, h0, h1]

/-- The derivative norm propagates through the convex segment (triangle + convex
combination): `gDeriv` is `ℂ`-linear so `gDeriv (seg θ) = gDeriv g + θ•(gDeriv f −
gDeriv g)`. -/
theorem gDeriv_seg_le {f g : EWA T 1} {Md θ : ℝ}
    (hf : ‖GWA.gDeriv f‖ ≤ Md) (hg : ‖GWA.gDeriv g‖ ≤ Md) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    ‖GWA.gDeriv (seg f g θ)‖ ≤ Md := by
  -- `gDeriv` is `ℂ`-linear: write the segment derivative as a convex combination.
  have hlin : GWA.gDeriv (seg f g θ)
      = (1 - ((θ : ℝ) : ℂ)) • GWA.gDeriv g + ((θ : ℝ) : ℂ) • GWA.gDeriv f := by
    have h := (GWA.gDeriv (K := CT T) (r := 0)).map_add g (((θ : ℝ) : ℂ) • (f - g))
    rw [seg, h, (GWA.gDeriv (K := CT T) (r := 0)).map_smul,
      (GWA.gDeriv (K := CT T) (r := 0)).map_sub]
    rw [smul_sub, sub_smul, one_smul]
    abel
  rw [hlin]
  have hθ : ‖((θ : ℝ) : ℂ)‖ = θ := by
    rw [Complex.norm_real, Real.norm_of_nonneg h0]
  have h1θ : ‖(1 - ((θ : ℝ) : ℂ))‖ = 1 - θ := by
    have : (1 : ℂ) - ((θ : ℝ) : ℂ) = (((1 - θ : ℝ)) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  calc ‖(1 - ((θ : ℝ) : ℂ)) • GWA.gDeriv g + ((θ : ℝ) : ℂ) • GWA.gDeriv f‖
      ≤ ‖(1 - ((θ : ℝ) : ℂ)) • GWA.gDeriv g‖ + ‖((θ : ℝ) : ℂ) • GWA.gDeriv f‖ :=
        norm_add_le _ _
    _ = (1 - θ) * ‖GWA.gDeriv g‖ + θ * ‖GWA.gDeriv f‖ := by rw [norm_smul, norm_smul, hθ, h1θ]
    _ ≤ Md := by nlinarith [hf, hg, h0, h1]

/-! ### Part 2 — the one-parameter group decomposition and its derivative. -/

/-- The segment exponential factors via the commutative one-parameter group:
`exp((-t)•seg f g θ) = exp((-t)•g) * exp(θ•B)` with `B = (-t)•(f − g)` and the
last `•` the real-scalar action. -/
theorem phi_factor (f g : EWA T 1) (t θ : ℝ) :
    NormedSpace.exp (((-t : ℝ) : ℂ) • seg f g θ)
      = NormedSpace.exp (((-t : ℝ) : ℂ) • g)
        * NormedSpace.exp (θ • (((-t : ℝ) : ℂ) • (f - g))) := by
  -- the real-scalar `θ • z` on `EWA` agrees with the complex `(θ:ℂ) • z` (`Complex.coe_smul`).
  have hreal : ∀ z : EWA T 1, θ • z = ((θ : ℝ) : ℂ) • z := fun z => (Complex.coe_smul θ z).symm
  have hdecomp : ((-t : ℝ) : ℂ) • seg f g θ
      = ((-t : ℝ) : ℂ) • g + θ • (((-t : ℝ) : ℂ) • (f - g)) := by
    rw [seg, smul_add, hreal (((-t : ℝ) : ℂ) • (f - g)), smul_smul, smul_smul]
    congr 2
    push_cast
    ring
  rw [hdecomp, NormedSpace.exp_add_of_commute (Commute.all _ _)]

/-- The `θ`-derivative of `φ θ = exp((-t)•seg f g θ)` is `B * φ θ` with
`B = (-t)•(f − g)`, via `hasDerivAt_exp_smul_const` and the product rule. -/
theorem hasDerivAt_phi (f g : EWA T 1) (t θ : ℝ) :
    HasDerivAt (fun θ : ℝ => NormedSpace.exp (((-t : ℝ) : ℂ) • seg f g θ))
      ((((-t : ℝ) : ℂ) • (f - g)) * NormedSpace.exp (((-t : ℝ) : ℂ) • seg f g θ)) θ := by
  set B : EWA T 1 := ((-t : ℝ) : ℂ) • (f - g) with hB
  set A : EWA T 1 := NormedSpace.exp (((-t : ℝ) : ℂ) • g) with hA
  have hexp : HasDerivAt (fun θ : ℝ => NormedSpace.exp (θ • B))
      (NormedSpace.exp (θ • B) * B) θ := hasDerivAt_exp_smul_const B θ
  have hprod : HasDerivAt (fun θ : ℝ => A * NormedSpace.exp (θ • B))
      (A * (NormedSpace.exp (θ • B) * B)) θ := by
    have := hexp.const_mul A
    simpa using this
  have hfun : (fun θ : ℝ => NormedSpace.exp (((-t : ℝ) : ℂ) • seg f g θ))
      = fun θ : ℝ => A * NormedSpace.exp (θ • B) := by
    funext θ'; rw [phi_factor, hA, hB]
  have hval : A * (NormedSpace.exp (θ • B) * B)
      = B * NormedSpace.exp (((-t : ℝ) : ℂ) • seg f g θ) := by
    rw [phi_factor, hA, hB]
    ring
  rw [hfun, ← hval]
  exact hprod

/-! ### Part 3 — THE MAIN LEMMA: the segment mean-value exp difference bound. -/

/-- **`expNeg_sub_expNeg_norm_le`** — the segment mean-value bound on the
difference of two Banach-algebra exponentials.  Under the uniform spectral floor
`δ` on both `f` and `g` and a common derivative bound `Md`,
`‖e^{−tf} − e^{−tg}‖ ≤ t·‖f−g‖·(8(1+1/π)²)·(1+tMd)²·e^{−δt}`. -/
theorem expNeg_sub_expNeg_norm_le {f g : EWA T 1} {t δ Md : ℝ}
    (ht : 0 ≤ t) (hMd : 0 ≤ Md) (hf_floor : UniformFloor f δ) (hg_floor : UniformFloor g δ)
    (hfD : ‖GWA.gDeriv f‖ ≤ Md) (hgD : ‖GWA.gDeriv g‖ ≤ Md) :
    ‖NormedSpace.exp (((-t : ℝ) : ℂ) • f) - NormedSpace.exp (((-t : ℝ) : ℂ) • g)‖
      ≤ t * ‖f - g‖ * (8 * (1 + 1 / Real.pi) ^ 2) * (1 + t * Md) ^ 2 * Real.exp (-δ * t) := by
  set C : ℝ :=
    t * ‖f - g‖ * (8 * (1 + 1 / Real.pi) ^ 2) * (1 + t * Md) ^ 2 * Real.exp (-δ * t) with hC
  -- the φ function and its derivative on [0,1].
  set φ : ℝ → EWA T 1 := fun θ => NormedSpace.exp (((-t : ℝ) : ℂ) • seg f g θ) with hφ
  -- endpoint identification: φ 1 − φ 0 = exp((-t)•f) − exp((-t)•g).
  have hφ1 : φ 1 = NormedSpace.exp (((-t : ℝ) : ℂ) • f) := by rw [hφ]; simp [seg_one]
  have hφ0 : φ 0 = NormedSpace.exp (((-t : ℝ) : ℂ) • g) := by rw [hφ]; simp [seg_zero]
  -- the derivative bound on [0,1].
  have hbound : ∀ θ ∈ Set.Ico (0 : ℝ) 1,
      ‖(((-t : ℝ) : ℂ) • (f - g)) * φ θ‖ ≤ C := by
    intro θ hθ
    obtain ⟨h0, h1⟩ := hθ
    have h1' : θ ≤ 1 := le_of_lt h1
    -- the decisive bound at seg f g θ.
    have hfloorθ : UniformFloor (seg f g θ) δ :=
      UniformFloor_seg hf_floor hg_floor h0 h1'
    have hdec := EWA_decisive_exp_bound (seg f g θ) t δ ht hfloorθ
    -- propagate the derivative bound through the segment.
    have hDθ : ‖GWA.gDeriv (seg f g θ)‖ ≤ Md := gDeriv_seg_le hfD hgD h0 h1'
    -- ‖φ θ‖ ≤ (8(1+1/π)²)(1+t‖gDeriv(seg)‖)² e^{-δt} ≤ (8(1+1/π)²)(1+tMd)² e^{-δt}.
    have hexp_pos : (0 : ℝ) ≤ Real.exp (-δ * t) := le_of_lt (Real.exp_pos _)
    have hCpos : (0 : ℝ) ≤ 8 * (1 + 1 / Real.pi) ^ 2 := by positivity
    have hmono : (1 + t * ‖GWA.gDeriv (seg f g θ)‖) ^ 2 ≤ (1 + t * Md) ^ 2 := by
      have hle : 1 + t * ‖GWA.gDeriv (seg f g θ)‖ ≤ 1 + t * Md := by
        nlinarith [mul_le_mul_of_nonneg_left hDθ ht]
      have hnn : (0 : ℝ) ≤ 1 + t * ‖GWA.gDeriv (seg f g θ)‖ := by positivity
      nlinarith [hle, hnn]
    have hphi_le : ‖φ θ‖
        ≤ (8 * (1 + 1 / Real.pi) ^ 2) * (1 + t * Md) ^ 2 * Real.exp (-δ * t) := by
      refine le_trans hdec ?_
      have := mul_le_mul_of_nonneg_right hmono hexp_pos
      nlinarith [this, hCpos, hmono, hexp_pos]
    -- ‖B * φ θ‖ ≤ ‖B‖·‖φ θ‖ = t‖f−g‖·‖φ θ‖.
    have hBnorm : ‖((-t : ℝ) : ℂ) • (f - g)‖ = t * ‖f - g‖ := by
      rw [norm_smul, Complex.norm_real, norm_neg, Real.norm_of_nonneg ht]
    have hmul : ‖(((-t : ℝ) : ℂ) • (f - g)) * φ θ‖
        ≤ (t * ‖f - g‖) * ‖φ θ‖ := by
      refine le_trans (norm_mul_le _ _) ?_
      rw [hBnorm]
    -- combine: t‖f−g‖·‖φ θ‖ ≤ C.
    have htfg : (0 : ℝ) ≤ t * ‖f - g‖ := mul_nonneg ht (norm_nonneg _)
    calc ‖(((-t : ℝ) : ℂ) • (f - g)) * φ θ‖
        ≤ (t * ‖f - g‖) * ‖φ θ‖ := hmul
      _ ≤ (t * ‖f - g‖)
          * ((8 * (1 + 1 / Real.pi) ^ 2) * (1 + t * Md) ^ 2 * Real.exp (-δ * t)) :=
          mul_le_mul_of_nonneg_left hphi_le htfg
      _ = C := by rw [hC]; ring
  -- the segment mean-value inequality on [0,1].
  have hderiv : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt φ ((((-t : ℝ) : ℂ) • (f - g)) * φ θ) (Set.Icc (0 : ℝ) 1) θ :=
    fun θ _ => (hasDerivAt_phi f g t θ).hasDerivWithinAt
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01' hderiv hbound
  rw [hφ1, hφ0] at hmv
  exact hmv

end ShenWork.EWA

#print axioms ShenWork.EWA.expNeg_sub_expNeg_norm_le
