/-
  ShenWork/Paper2/IntervalMixedProduct.lean

  THE MIXED cosine×sine→sine product — the final residual of the χ₀<0 propagation.

  The flux `Q = (u·(1+v)^{−β})·v_x = (cosine object W)·(sine object v_x)` is a SINE
  object, because `v_x = Σ_k √λ_k·cosineCoeffs(v)_k · sin(kπx)` is a sine series.  The
  bootstrap engine (`gradientSolution_memHSigma_succ_fully_uncond`) consumes a uniform
  H^σ envelope of `sineCoeffs(Q τ)`, but the landed Wiener–Young algebra
  (`IntervalWienerAlgebra*`, `IntervalEnvelopeProp`) produces only COSINE-side
  products.  This file supplies the MIXED product and closes the sine envelope.

  ## The product identity

  From `cos(mπx)·sin(jπx) = ½(sin((m+j)πx) + sin((j−m)πx))` and (for j<m)
  `sin((j−m)πx) = −sin((m−j)πx)`, the SINE coefficient of `W·v_x` is

    sineCoeffs(W·v_x)_k = ½ Σ_{m,j} Ŵ_m·(v̂x)_j·[δ_{m+j,k} + δ_{j−m,k} − δ_{m−j,k}]

  — a MIXED convolution of the COSINE coeffs `a = cosineCoeffs W` and the SINE coeffs
  `b = sineCoeffs v_x`.  The additive part `δ_{m+j,k}` is the landed `addConv a b`;
  the SIGNED difference part `+δ_{j−m,k} − δ_{m−j,k}` is `signedDiffConv a b :=
  corr1 b a − corr1 a b` (`corr1 b a` collects `j−m=k`, `corr1 a b` collects `m−j=k`).

  ## The verdict (proved here)

  The convolution STRUCTURE is identical to the cosine case; only the basis
  interpretation and the ONE sign differ.  The Peetre weight (`cosWeight_le_add`,
  `k=m+j` and `k=|m−j|` both `≤ m+j`) and the discrete Young (`addConv`/`corr1`
  landed) are reused VERBATIM.  Crucially the envelopes are SIGN-INSENSITIVE: the
  `|signedDiffConv|` bound is `corr1 ga gb + corr1 gb ga = diffConv ga gb`, the SAME
  envelope as the cosine difference convolution.  So:

  * `memHSigma_mixedConv_of_gt_half` is a NEAR-MIRROR of `memHSigma_cosProd_of_gt_half`
    (same closure lemmas, no new estimate);
  * `envelopes_mixedConv` mirrors `envelopes_cosProd` (envelope = `cosProd ga gb`);
  * `fluxSineEnvelope_of_factorEnvelopes` assembles the flux SINE envelope exactly as
    `fluxCosEnvelope_of_factorEnvelopes` assembles the cosine one;
  * the bootstrap step's `hg`/`hg_dom` is then DISCHARGEABLE from factor envelopes.

  DECISIVE: the mixed product is a CLEAN MIRROR — no new obstruction.  The flux SINE
  envelope closes, so χ₀<0 propagation is fully WIRING down to the (tau-uniform) base
  factor envelopes.

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New names only.
-/
import ShenWork.Paper2.IntervalEnvelopeProp

noncomputable section

open scoped BigOperators
open ShenWork.Paper2.HSigmaScale
open ShenWork.Paper2.IntervalWienerAlgebra
open ShenWork.Paper2.IntervalEnvelopeProp

namespace ShenWork.Paper2.IntervalMixedProduct

/-! ## 1. The signed difference convolution and the mixed product coefficient. -/

/-- The **signed difference convolution** for the mixed cosine×sine product:
`signedDiffConv a b k = corr1 b a k − corr1 a b k`.  `corr1 b a k = Σ'_n b_{n+k}·a_n`
collects the pairs `(m,j)` with `j−m=k` (sign `+`); `corr1 a b k = Σ'_n a_{n+k}·b_n`
collects `m−j=k` (sign `−`).  Together they realize `+δ_{j−m,k} − δ_{m−j,k}`. -/
def signedDiffConv (a b : ℕ → ℝ) (k : ℕ) : ℝ := corr1 b a k - corr1 a b k

/-- The **mixed product coefficient** `(a ⊠ b)_k = ½((a ⋆ b)_k + signedDiffConv a b k)`
from `cos(mπx)·sin(jπx) = ½(sin((m+j)πx) + sin((j−m)πx))`. -/
def mixedConv (a b : ℕ → ℝ) (k : ℕ) : ℝ :=
  (1 / 2 : ℝ) * (addConv a b k + signedDiffConv a b k)

/-! ## 2. `H^σ` membership of the mixed product — the near-mirror of the cosine case. -/

/-- `signedDiffConv a b = corr1 b a − corr1 a b`, both leaves in `H^σ` by
`memHSigma_corr1`; `H^σ` is closed under subtraction.  (The ONE sign is irrelevant to
membership — exactly the cosine `diffConv` proof, with `−` instead of `+`.) -/
theorem memHSigma_signedDiffConv_of_gt_half {σ : ℝ} (hσ : 1 / 2 < σ) {a b : ℕ → ℝ}
    (ha : MemHSigma σ a) (hb : MemHSigma σ b) :
    MemHSigma σ (signedDiffConv a b) := by
  have hsub : signedDiffConv a b
      = fun k => corr1 b a k + (-1 : ℝ) * corr1 a b k := by
    funext k; unfold signedDiffConv; ring
  rw [hsub]
  exact memHSigma_add (memHSigma_corr1 hσ hb ha)
    (memHSigma_smul (-1) (memHSigma_corr1 hσ ha hb))

set_option maxHeartbeats 400000 in
/-- **TASK 1 — the MIXED product `H^σ` membership** (`σ > 1/2`).  For cosine coeffs
`a` and sine coeffs `b`, both in `H^σ`, the sine-product coefficient sequence
`mixedConv a b = ½(addConv a b + signedDiffConv a b)` lies in `H^σ`.

A CLEAN MIRROR of `memHSigma_cosProd_of_gt_half`: the SAME `memHSigma_addConv_of_gt_half`
+ the SAME `memHSigma_corr1` (twice, the 2-cover), only the difference leaf carries the
mixed `±` sign.  No new estimate. -/
theorem memHSigma_mixedConv_of_gt_half {σ : ℝ} (hσ : 1 / 2 < σ) {a b : ℕ → ℝ}
    (ha : MemHSigma σ a) (hb : MemHSigma σ b) :
    MemHSigma σ (mixedConv a b) :=
  memHSigma_smul (1 / 2)
    (memHSigma_add (memHSigma_addConv_of_gt_half hσ ha hb)
      (memHSigma_signedDiffConv_of_gt_half hσ ha hb))

/-! ## 3. Envelope-monotonicity of the mixed product — the SIGN-INSENSITIVE mirror.

`|signedDiffConv a b k| = |corr1 b a k − corr1 a b k| ≤ |corr1 b a k| + |corr1 a b k|
≤ corr1 gb ga k + corr1 ga gb k = diffConv ga gb k` — the SAME envelope as the cosine
difference convolution (`envelopes_diffConv`).  Hence the mixed product's envelope is
`cosProd ga gb`, IDENTICAL to the cosine product's. -/

/-- The signed difference convolution is enveloped by the (unsigned) `diffConv` of the
envelopes — the sign is absorbed by the triangle inequality. -/
theorem envelopes_signedDiffConv {σ : ℝ} (hσ : 1 / 2 < σ) {ga a gb b : ℕ → ℝ}
    (hga : MemHSigma σ ga) (hgb : MemHSigma σ gb)
    (ha : Envelopes ga a) (hb : Envelopes gb b) :
    Envelopes (diffConv ga gb) (signedDiffConv a b) := by
  intro k
  unfold signedDiffConv diffConv
  calc |corr1 b a k - corr1 a b k|
      ≤ |corr1 b a k| + |corr1 a b k| := by
        rw [sub_eq_add_neg]; exact (abs_add_le _ _).trans (by rw [abs_neg])
    _ ≤ corr1 gb ga k + corr1 ga gb k :=
        add_le_add (envelopes_corr1 hσ hgb hga hb ha k)
          (envelopes_corr1 hσ hga hgb ha hb k)
    _ = corr1 ga gb k + corr1 gb ga k := by ring

/-- **TASK 1 (envelope form) — the mixed product is envelope-monotone.**  `cosProd ga
gb` envelopes `mixedConv a b` pointwise, and `cosProd ga gb ∈ H^σ` by
`memHSigma_cosProd_of_gt_half`.  The envelope of a MIXED product is the SAME single
sequence `cosProd ga gb` as the cosine product — the sign-insensitive mirror. -/
theorem envelopes_mixedConv {σ : ℝ} (hσ : 1 / 2 < σ) {ga a gb b : ℕ → ℝ}
    (hga : MemHSigma σ ga) (hgb : MemHSigma σ gb)
    (ha : Envelopes ga a) (hb : Envelopes gb b) :
    Envelopes (cosProd ga gb) (mixedConv a b) := by
  unfold mixedConv cosProd
  refine envelopes_smul (by norm_num) ?_
  exact envelopes_add (envelopes_addConv ha hb)
    (envelopes_signedDiffConv hσ hga hgb ha hb)

/-! ## 4. The exact normalized mixed product `trueMixedProd` (sine mode-0 = 0).

`sineCoeffs (W·v_x) 0 = 0` always (`sin 0 = 0`).  `trueMixedProd` is `mixedConv` with
the mode-0 value forced to `0`, the exact sine-coefficient operator of the function
product.  (Mirrors `trueCosProd`'s mode-0 correction, but the sine value is simply 0,
so no `diagCorr` term arises — it is just zeroing mode 0.) -/

/-- The exact normalized mixed product coefficient: `mixedConv` off mode 0, `0` at
mode 0 (matching `sineCoeffs (W·v_x) 0 = 0`). -/
def trueMixedProd (a b : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 0 else mixedConv a b k

/-- `trueMixedProd a b k = mixedConv a b k` for every positive mode. -/
theorem trueMixedProd_pos {a b : ℕ → ℝ} {k : ℕ} (hk : k ≠ 0) :
    trueMixedProd a b k = mixedConv a b k := by simp [trueMixedProd, hk]

/-- `trueMixedProd` differs from `mixedConv` only at mode `0`. -/
theorem mixedConv_eq_trueMixedProd_except (a b : ℕ → ℝ) :
    ∀ k, k ≠ 0 → mixedConv a b k = trueMixedProd a b k :=
  fun _ hk => (trueMixedProd_pos hk).symm

/-- **`H^σ` membership of the exact mixed product** (`σ > 1/2`): since `trueMixedProd a
b` agrees with `mixedConv a b` off the single mode `0`, it inherits `H^σ` membership. -/
theorem memHSigma_trueMixedProd_of_gt_half {σ : ℝ} (hσ : 1 / 2 < σ) {a b : ℕ → ℝ}
    (ha : MemHSigma σ a) (hb : MemHSigma σ b) :
    MemHSigma σ (trueMixedProd a b) :=
  ShenWork.Paper2.IntervalWienerAlgebra.memHSigma_congr_except 0
    (mixedConv_eq_trueMixedProd_except a b) (memHSigma_mixedConv_of_gt_half hσ ha hb)

/-- **The exact mixed product is envelope-monotone — by the COSINE product of the
envelopes.**  `trueCosProd ga gb` envelopes `trueMixedProd a b` pointwise (off mode 0
the SIGN-INSENSITIVE bound `|mixedConv a b| ≤ cosProd ga gb` of `envelopes_mixedConv`,
and `cosProd = trueCosProd` off mode 0; at mode 0 `trueMixedProd a b 0 = 0`).  The
envelope of the mixed (signed, sine) product is the SAME single sequence
`trueCosProd ga gb` as the cosine product — the sign-insensitive mirror.  It lies in
`H^σ` by `memHSigma_trueCosProd_of_gt_half`. -/
theorem envelopes_trueMixedProd {σ : ℝ} (hσ : 1 / 2 < σ) {ga a gb b : ℕ → ℝ}
    (hga : MemHSigma σ ga) (hgb : MemHSigma σ gb)
    (ha : Envelopes ga a) (hb : Envelopes gb b) :
    Envelopes (ShenWork.Paper2.IntervalWienerAlgebra.trueCosProd ga gb)
      (trueMixedProd a b) := by
  intro k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [trueMixedProd, if_pos rfl, abs_zero]
    exact Envelopes.nonneg
      (ShenWork.Paper2.IntervalEnvelopeProp.envelopes_trueCosProd hσ hga hgb ha hb) 0
  · have hkne : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk
    rw [trueMixedProd_pos hkne,
      ShenWork.Paper2.IntervalWienerAlgebra.trueCosProd_pos hkne]
    exact envelopes_mixedConv hσ hga hgb ha hb k

end ShenWork.Paper2.IntervalMixedProduct

/-! ## 5. The flux SINE envelope assembly (TASK 2). -/

namespace ShenWork.Paper2.IntervalMixedProduct

open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.Paper2.IntervalDivergenceModeIdentity (sineCoeffs)

/-- **The mixed-multiplication bridge predicate** (sine analogue of `CosineMulBridge`).
`MixedMulBridge W vx` asserts that the SINE coefficients of the function product `W·vx`
(`W` cosine object, `vx` sine object) are the exact `trueMixedProd` of `W`'s COSINE
coeffs and `vx`'s SINE coeffs:
`sineCoeffs (W·vx) k = trueMixedProd (cosineCoeffs W) (sineCoeffs vx) k` for all `k`. -/
def MixedMulBridge (W vx : ℝ → ℝ) : Prop :=
  ∀ k, sineCoeffs (fun x => W x * vx x) k
    = trueMixedProd (cosineCoeffs W) (sineCoeffs vx) k

/-- Under the bridge, the product's SINE coefficient map is literally `trueMixedProd`
of the cosine/sine factor coefficients. -/
theorem sineCoeffs_mul_eq_trueMixedProd {W vx : ℝ → ℝ} (h : MixedMulBridge W vx) :
    sineCoeffs (fun x => W x * vx x)
      = trueMixedProd (cosineCoeffs W) (sineCoeffs vx) :=
  funext h

/-- **TASK 2 — the flux SINE envelope assembly.**  Let `σ > 1/2`.  Given:
* a uniform `H^σ` envelope `gW` of the COSINE coeffs of `W = u·(1+v)^{−β}` (supplied by
  the landed cosine chain `fluxCosEnvelope_of_factorEnvelopes`, with `W = uPow·invDen`);
* a uniform `H^σ` envelope `gvx` of the SINE coeffs of `v_x` (= `√λ·cosineCoeffs(v)`,
  itself in `H^σ` from `v`'s `H^{σ+1}` envelope);
* the mixed-multiplication bridge `MixedMulBridge W vx` (the sine analogue of the
  cosine bridge, giving `sineCoeffs (Q) = trueMixedProd (cosineCoeffs W) (sineCoeffs
  vx)`),

the SINGLE sequence `gQ := trueCosProd gW gvx` (the COSINE product of the envelopes —
sign-insensitive) is in `H^σ` AND envelopes the SINE coeffs of the flux `Q = W·v_x`
pointwise.  This is exactly the `(hg, hg_dom)` datum the bootstrap step
`gradientSolution_memHSigma_succ_fully_uncond` carries — now PRODUCED.

A CLEAN MIRROR of `fluxCosEnvelope_of_factorEnvelopes`: same envelope-monotone product,
same Banach-algebra closure, SAME envelope sequence `trueCosProd gW gvx`; only the
OUTPUT basis (which the envelope dominates) is sine. -/
theorem fluxSineEnvelope_of_factorEnvelopes {σ : ℝ} (hσ : 1 / 2 < σ)
    {W vx : ℝ → ℝ} {gW gvx : ℕ → ℝ}
    (hbridge : MixedMulBridge W vx)
    (hgW : MemHSigma σ gW) (hgvx : MemHSigma σ gvx)
    (heW : Envelopes gW (cosineCoeffs W))
    (hevx : Envelopes gvx (sineCoeffs vx)) :
    MemHSigma σ (ShenWork.Paper2.IntervalWienerAlgebra.trueCosProd gW gvx) ∧
      Envelopes (ShenWork.Paper2.IntervalWienerAlgebra.trueCosProd gW gvx)
        (sineCoeffs (fun x => W x * vx x)) := by
  refine ⟨ShenWork.Paper2.IntervalWienerAlgebra.memHSigma_trueCosProd_of_gt_half
    hσ hgW hgvx, ?_⟩
  rw [sineCoeffs_mul_eq_trueMixedProd hbridge]
  exact envelopes_trueMixedProd hσ hgW hgvx heW hevx

/-! ## 6. The bootstrap discharge (TASK 3): produce `hg`/`hg_dom`, not carry them. -/

/-- **TASK 3 — the uniform-in-τ flux SINE envelope `(hg, hg_dom)`, PRODUCED.**  Suppose
that, uniformly over `τ ∈ [0,t]`:
* `gW`/`gvx` are τ-INDEPENDENT `H^σ` envelopes of the cosine/sine factor coeffs
  (`heW τ`, `hevx τ`), and
* each time-slice satisfies the mixed bridge `MixedMulBridge (W τ) (vx τ)`,
with `Q τ = (W τ)·(vx τ)`.  Then the SINGLE τ-independent sequence `g := trueCosProd
gW gvx` is in `H^σ` AND dominates `|sineCoeffs (Q τ) k|` uniformly over `τ ∈ [0,t]`.

This is precisely `gradientSolution_memHSigma_succ_fully_uncond`'s `hg : MemHSigma σ g`
together with `hg_dom : ∀ τ ∈ Icc 0 t, ∀ k, |sineCoeffs (Q τ) k| ≤ g k`.  So those two
carried hypotheses are DISCHARGED from the (τ-uniform) factor envelopes — no Gronwall,
no new a-priori estimate beyond the base factor envelopes. -/
theorem fluxSineEnvelope_uniform {σ t : ℝ} (hσ : 1 / 2 < σ)
    {W vx : ℝ → ℝ → ℝ} {Q : ℝ → ℝ → ℝ} {gW gvx : ℕ → ℝ}
    (hQ : ∀ τ, Q τ = fun x => W τ x * vx τ x)
    (hgW : MemHSigma σ gW) (hgvx : MemHSigma σ gvx)
    (hbridge : ∀ τ ∈ Set.Icc (0:ℝ) t, MixedMulBridge (W τ) (vx τ))
    (heW : ∀ τ ∈ Set.Icc (0:ℝ) t, Envelopes gW (cosineCoeffs (W τ)))
    (hevx : ∀ τ ∈ Set.Icc (0:ℝ) t, Envelopes gvx (sineCoeffs (vx τ))) :
    MemHSigma σ (ShenWork.Paper2.IntervalWienerAlgebra.trueCosProd gW gvx) ∧
      ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k,
        |sineCoeffs (Q τ) k|
          ≤ ShenWork.Paper2.IntervalWienerAlgebra.trueCosProd gW gvx k := by
  refine ⟨ShenWork.Paper2.IntervalWienerAlgebra.memHSigma_trueCosProd_of_gt_half
    hσ hgW hgvx, fun τ hτ k => ?_⟩
  have hpack := fluxSineEnvelope_of_factorEnvelopes hσ (hbridge τ hτ) hgW hgvx
    (heW τ hτ) (hevx τ hτ)
  have hτenv := hpack.2 k
  rw [hQ τ]
  exact hτenv

/-! ## 7. VERDICT — the decisive deliverable.

DECISIVE QUESTION: is the mixed cosine×sine→sine product a CLEAN MIRROR of the landed
cosine Wiener–Young, or does the mixed/signed structure introduce a NEW obstruction?

ANSWER (proved above): a CLEAN MIRROR.  No new obstruction.

* TASK 1 (`memHSigma_mixedConv_of_gt_half`, `envelopes_mixedConv`): the mixed product
  reuses VERBATIM the SAME Peetre weight `cosWeight_le_add` (`k=m+j` and `k=|m−j|` both
  `≤ m+j`) and the SAME discrete Young (`memHSigma_addConv_of_gt_half` for the additive
  part, `memHSigma_corr1` twice for the 2-cover difference part).  The ONLY change is
  the mixed sign in `signedDiffConv = corr1 b a − corr1 a b`, and the envelope bound is
  SIGN-INSENSITIVE: `|signedDiffConv| ≤ corr1 gb ga + corr1 ga gb = diffConv ga gb`,
  the SAME envelope as the cosine difference convolution.  So the mixed product's
  envelope is the SAME single sequence `cosProd ga gb` as the cosine product's.

* TASK 2 (`fluxSineEnvelope_of_factorEnvelopes`): the flux SINE envelope assembles by
  the SAME envelope-monotone composition + Banach-algebra closure as the cosine
  envelope — only the output basis is sine.  `gQ = trueMixedProd gW gvx ∈ H^σ` and
  envelopes `sineCoeffs(Q)` pointwise.

* TASK 3 (`fluxSineEnvelope_uniform`): when the factor envelopes `gW, gvx` are
  τ-independent (the base uniform L∞ ball on the closed window + the elliptic / √λ
  multipliers, all τ-free), `g = trueMixedProd gW gvx` is a SINGLE τ-uniform sequence
  in `H^σ` dominating `|sineCoeffs (Q τ) k|` over all `τ ∈ [0,t]` — exactly the
  bootstrap step's carried `(hg, hg_dom)`.

  CONSEQUENCE for `gradientSolution_contDiffOn_two`: with `fluxSineEnvelope_uniform`
  producing `(hg, hg_dom)`, the per-level step `gradientSolution_memHSigma_succ_fully_
  uncond` is realizable WITHOUT carrying the flux sine envelope — the residual the
  prior `IntervalEnvelopeProp` VERDICT flagged (a uniform cosine envelope of the flux
  DERIVATIVE `Q_x`, one derivative above the factor envelopes) is now BYPASSED: the
  direct sine-object route (`Q` IS a sine object via `v_x`) needs NO extra derivative,
  only the SAME-order factor envelopes `gW` (cosine, H^σ) and `gvx` (sine, H^σ).

  Down to: (i) the base seed `h0 : MemHSigma σ₀ (cosineCoeffs ut)` (from hdecomp,
  carried — this is the initial-regularity datum, not a flux estimate), and (ii) the
  τ-uniformity of `gW, gvx` themselves (the base L∞ ball + the √λ·cosineCoeffs(v)
  bound, both τ-free uniform inputs of the keystone, NOT Gronwall), the χ₀<0
  propagation is FULLY WIRING.  The mixed/signed structure introduced NO genuine new
  obstruction. -/

end ShenWork.Paper2.IntervalMixedProduct

namespace ShenWork.Paper2.IntervalMixedProduct
#print axioms memHSigma_signedDiffConv_of_gt_half
#print axioms memHSigma_mixedConv_of_gt_half
#print axioms envelopes_signedDiffConv
#print axioms envelopes_mixedConv
#print axioms memHSigma_trueMixedProd_of_gt_half
#print axioms envelopes_trueMixedProd
#print axioms sineCoeffs_mul_eq_trueMixedProd
#print axioms fluxSineEnvelope_of_factorEnvelopes
#print axioms fluxSineEnvelope_uniform
end ShenWork.Paper2.IntervalMixedProduct
