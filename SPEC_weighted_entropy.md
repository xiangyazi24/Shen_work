# SPEC v2 — Weighted (moving-window) sharp entropy dissipation

## What changed from v1 (READ THIS)
v1 had a FATAL design bug: hypotheses `{w ≥ 0, w a = 0, |w'| ≤ (1/ell)·w}` force
`w ≡ 0` by Grönwall, making everything vacuous (you correctly detected this).
FIX: the weight is **strictly positive everywhere** (`w_pos`), does NOT vanish at
endpoints, and the interval boundary terms are **carried explicitly** in the
identity rather than killed. The multiplicative slowly-varying bound
`|w'| ≤ (1/ell)·w` is now consistent (w > 0).

## Goal
New whole-line-localized analog of the periodic sharp entropy dissipation
(`ChiOnePeriodicEntropySlice.sharp_entropy_production_le`), with a positive
slowly-varying weight. Genuinely new; engine of far-left `χ ≤ 4−δ`.

Model (m=γ=α=1): `u_t = u_xx + c u_x − χ(u_x r_x + u r_xx) + u(1−u)`,
`−r_xx + r = u−1`. `Φ(u)=chiOneRelativeEntropy u = u−1−log u`,
`M(u)=chiOneEntropyMultiplier u = 1−1/u`. Let `A x = ux x/u x`, `W x = u x − 1`.

## Location / reuse
NEW file `ShenWork/Paper1/WholeLineChiPosWeightedEntropyDissipation.lean`.
Import and REUSE (do not re-prove): `chiOneRelativeEntropy`,
`chiOneEntropyMultiplier`, `chiOneRelativeEntropy_hasDerivAt`,
`chiOneEntropyMultiplier_comp_hasDerivAt` (from WholeLineChiPosSharpEntropyDissipation),
and mirror the real-space IBP proof of `resolver_deriv_sq_le_quarter_source_sq`
(WholeLineResolverSharpGradient.lean) for the weighted resolver below.
DO NOT edit those files. CHECK-EXISTING first:
`grep -rn "WeightedEntropy\|weightedEntropy\|ChiOneWeighted\|weighted_resolver" ShenWork/`.

## Structure
```
structure ChiOneWeightedEntropySlice
    (a b c chi ell : ℝ) (w w' : ℝ → ℝ)
    (u ux uxx r rx rxx ut : ℝ → ℝ) : Prop where
  hab   : a ≤ b
  hell  : 0 < ell
  u_pos : ∀ x, 0 < u x
  w_pos : ∀ x, 0 < w x                      -- POSITIVE (no endpoint vanishing)
  w_deriv : ∀ x, HasDerivAt w (w' x) x
  w'_cont : Continuous w'
  w_slow : ∀ x, |w' x| ≤ (1/ell) * w x       -- slowly varying (consistent: w>0)
  u_deriv : ∀ x, HasDerivAt u (ux x) x
  ux_deriv : ∀ x, HasDerivAt ux (uxx x) x
  r_deriv : ∀ x, HasDerivAt r (rx x) x
  rx_deriv : ∀ x, HasDerivAt rx (rxx x) x
  uxx_continuous : Continuous uxx
  rxx_continuous : Continuous rxx
  ut_continuous  : Continuous ut
  population_pde : ∀ x, ut x = uxx x + c*ux x − chi*(ux x*rx x + u x*rxx x) + u x*(1−u x)
  resolver_pde   : ∀ x, −rxx x + r x = u x − 1
```
(w_cont derivable from w_deriv; add if convenient.)

## STAGE 1 — weighted sharp resolver (the key new lemma; do FIRST, verify, then continue)
Mirror `resolver_deriv_sq_le_quarter_source_sq` with the weight `w` inserted.
Real-space derivation (NO Fourier). With `v=r, v₁=rx, v₂=rxx, g=W`:
- weighted IBP: `∫ w·v·v₂ = (w b·v b·v₁ b − w a·v a·v₁ a) − ∫ w'·v·v₁ − ∫ w·v₁²`
  (deriv of `w·v` is `w'·v + w·v₁`; use intervalIntegral.integral_mul_deriv_eq_deriv_mul).
- pointwise Young against `w ≥ 0`: `−2·w·v·v₂ ≤ w·v² + w·v₂²` (sq_nonneg (v+v₂), w_pos).
- decomposition (pointwise, from PDE `v₂ = v − g`): `w·g² = w·v² − 2 w·v·v₂ + w·v₂²`.
Combine (as in the unweighted proof, `4∫w v₁²`-emerges):
  `∫ w·v₁² ≤ (1/4)·∫ w·g² + (1/2)·|∫ w'·v·v₁| + (1/2)·|BT_res|`
where `BT_res = w b·v b·v₁ b − w a·v a·v₁ a`. Then bound
  `|∫ w'·v·v₁| ≤ (1/ell)·∫ w·|v·v₁| ≤ (1/(2 ell))·∫ w·(v² + v₁²)`  (w_slow + AM-GM).
STATE the lemma as (choose the cleanest equivalent):
```
weighted_resolver_le :
  ∫ w·rx² ≤ (1/4)·∫ w·W² + (1/(4·ell))·(∫ w·r² + ∫ w·rx²) + (1/2)·BT_res
```
(Coefficients need not be tight; any explicit `(C/ell)` correction + explicit
boundary `BT_res` is fine. If you also need `∫ w·r² ≤ ∫ w·W² + (C/ell)(…)+BT`,
prove it by the same IBP — but prefer to keep `∫ w·r²` on the RHS as-is and let
the caller absorb it, if that avoids extra work.)

## STAGE 2 — weighted entropy production identity (explicit boundary)
Each term via IBP on [a,b], boundary terms KEPT (factor w ≠ 0). Let
`BDRY = (w b·M(u b)·ux b − w a·M(u a)·ux a)
       + c·(w b·Φ(u b) − w a·Φ(u a))
       − chi·(w b·W b·rx b − w a·W a·rx a)`.
```
weighted_entropy_production_identity :
  ∫ w·M(u)·ut
   = (−∫ w·A² + chi·∫ w·A·rx − ∫ w·W²)          -- MAIN
   + (−∫ w'·M(u)·ux − c·∫ w'·Φ(u) + chi·∫ w'·W·rx) -- FLUX
   + BDRY                                          -- BOUNDARY
```
Derivation of each piece:
- diffusion `∫ w·M(u)·uxx = (w·M(u)·ux)|_a^b − ∫ w'·M(u)·ux − ∫ w·A²`
  (`(w·M(u))' = w'·M(u) + w·(ux/u²)`; `w·(ux/u²)·ux = w·A²`).
- drift `c·∫ w·M(u)·ux = c·(w·Φ(u))|_a^b − c·∫ w'·Φ(u)`
  (`M(u)·ux = ∂_x Φ(u)` via chiOneRelativeEntropy_hasDerivAt∘u_deriv; IBP).
- chemotaxis `−chi·∫ w·M(u)·(ux·rx+u·rxx) = −chi·(w·W·rx)|_a^b + chi·∫ w'·W·rx + chi·∫ w·A·rx`
  (`ux·rx+u·rxx=(u·rx)_x`; `(w·M(u))'·u = w'·W + w·A`; `M(u)·u = W`).
- reaction `∫ w·M(u)·u·(1−u) = −∫ w·W²` (pointwise `M(u)·u·(1−u) = −W²`).
Assemble via population_pde exactly like the periodic `entropy_production_identity`.

## STAGE 3 — weighted sharp inequality (MAIN THEOREM)
Bound MAIN + FLUX. For MAIN: pointwise Young `chi·(A·rx) ≤ A² + (chi²/4)·rx²`
(sq_nonneg (A−(chi/2)·rx)), integrate against `w≥0`; then STAGE-1
`weighted_resolver_le` folds `∫ w·rx²` into `(1/4)∫w·W²` (giving the `chi²/16`),
and split diffusion `−∫w·A² = −½∫w·A² − ½∫w·A²`, reserving `−½∫w·A²` to dominate
the FLUX `A²` mass. FLUX bounds (all via w_slow + w_pos + AM-GM):
- `|∫ w'·M(u)·ux| = |∫ w'·W·A| ≤ (1/(2ell))∫ w·(W²+A²)`  (M(u)·ux = W·A pointwise).
- `|c·∫ w'·Φ(u)| ≤ (|c|/ell)·∫ w·Φ(u)`   (need `0 ≤ Φ(u)`: prove helper
  `chiOneRelativeEntropy_nonneg : 0 < u → 0 ≤ u−1−log u` via `Real.log_le_sub_one_of_pos`).
- `|chi·∫ w'·W·rx| ≤ (chi/(2ell))∫ w·(W²+rx²)`, fold `∫w·rx²` via STAGE 1.
FINAL FORM (state with explicit `C` and the boundary/`E`/`D` terms exposed —
do NOT hide anything in a hypothesis):
```
weighted_sharp_entropy_production_le (hchi : 0 ≤ chi) :
  ∫ w·M(u)·ut
    ≤ −(1 − chi^2/16)·∫ w·W²
      + (C/ell)·((∫ w·Φ(u)) + ∫ w·(A² + W²))
      + BDRY
      + (weighted_resolver correction terms, explicit)
```
with `C = C(c,chi)` an explicit closed form (e.g. `C = |c| + chi + 2`). It is fine
if the final constant/coefficients are not tight; they must be EXPLICIT and the
`chi^2/16` margin must be exactly there (so `< 0` leading term iff chi < 4).

## Hard rules
- 0 sorry / 0 axiom / 0 admit / 0 native_decide. Clean-3 only.
- w > 0 and u > 0 ⇒ every integrand continuous on [a,b] ⇒ `intervalIntegrable`
  as in the periodic file. Mirror its `.intervalIntegrable a b` usage exactly.
- Line length ≤ 100. End with `#print axioms` for every produced theorem.
- STAGE-GATE: get STAGE 1 compiling clean-3 BEFORE STAGE 2; STAGE 2 before STAGE 3.
- If a stage genuinely stalls, deliver the compiling stages + a PRECISE stall
  report (exact goal, missing Mathlib lemma). NEVER insert sorry/axiom, NEVER
  weaken a statement to pass, NEVER make the weight degenerate.

## Acceptance
All three stages compile clean-3; file appended to `ShenWork.lean` closure in
dependency order (imports the periodic + resolver files); report `#print axioms`
verbatim. Confirm the weight is genuinely positive (no vacuity): include a one-line
sanity check that `w_pos` is used and no theorem reduces to `0 ≤ 0`.
