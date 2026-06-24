# Q113 (cron2): classical regularity frontier — EWA calculus closure vs interior smoothing

## Executive verdict

There is a unified route, but it should **not** be a full “interior `C∞` parabolic smoothing” theorem. That theorem is conceptually true, but it is far too expensive to formalize from scratch in Lean for this target. The better unified route is a **finite EWA calculus-closure theorem**:

```text
C¹_t / weighted-Wiener-in-time data for u
+ resolver smoothing for v
+ positivity of u and 1+v
+ weighted-Wiener algebra / smooth-composition lemmas
⇒ all remaining source/flux regularity packages at once.
```

This should discharge `(b)` and `(c)` mechanically and reduce `(a)` to the genuinely hard finite-time regularity statement: the nonlinear source is `C¹` in time as an EWA sequence with a locally summable majorant.

So the recommended strategy is:

```text
Do NOT prove general interior C∞ smoothing.
Do prove one finite theorem:
  EWAClassicalCore ⇒
    h_flux_diff ∧ h_src_cont ∧ DuhamelSourceTimeC1.
```

The hard part is not differentiating `u·v_x/(1+v)^β` in space. The hard part is proving the **time-`C¹` source package** with the correct weighted-Wiener bounds.

## 1. Unified route: finite EWA classical-core theorem

A useful abstraction is:

```lean
structure EWAClassicalCore
    (uCoeff uDotCoeff : ℝ → ℕ → ℝ)
    (vCoeff vDotCoeff : ℝ → ℕ → ℝ)
    (I : Set ℝ) : Prop where
  -- coefficient identities
  v_coeff : ∀ t n, vCoeff t n = uCoeff t n / (μ + lambda n)
  vdot_coeff : ∀ t n, vDotCoeff t n = uDotCoeff t n / (μ + lambda n)

  -- local uniform spatial regularity
  u_A2_loc : ∃ B, ∀ t∈I, A 2 (uCoeff t) ≤ B
  uDot_A1_loc : ∃ B, ∀ t∈I, A 1 (uDotCoeff t) ≤ B

  -- coefficient time differentiability / continuity in the EWA norm
  u_time_deriv : ∀ n t, t∈I → HasDerivAt (fun s => uCoeff s n) (uDotCoeff t n) t
  u_cont_A2 : ContinuousOn (fun t => uCoeff t) I   -- in A₂ norm, or explicit ε form
  uDot_cont_A1 : ContinuousOn (fun t => uDotCoeff t) I -- in A₁ norm

  -- positivity boxes
  u_pos : ∀ t∈I, ∀ x, 0 < u t x
  v_pos : ∀ t∈I, ∀ x, 0 ≤ v t x
```

The exact indices can be adjusted, but the important point is this:

- `u∈A₂` gives spatial `C²` for `u`.
- `u_t∈A₁` is the convenient finite assumption for time differentiability of the chem divergence source, because differentiating the flux time derivative in `x` sees `(u_t)_x`.
- `v=(μ-Δ_N)^{-1}u` gains two derivatives, so `v∈A₄` if `u∈A₂`.
- `v_t=(μ-Δ_N)^{-1}u_t` gains two derivatives, so `v_t∈A₃` if `u_t∈A₁`.

Under this core, prove one theorem:

```lean
theorem all_source_regularities_of_EWAClassicalCore
    (hcore : EWAClassicalCore uCoeff uDotCoeff vCoeff vDotCoeff I)
    (hβ : ... ) (hα : ... ) :
    DuhamelSourceTimeC1 ... ∧
    (∀ t∈I, ∀ x, DifferentiableAt ℝ (chemFluxLifted t) x) ∧
    ContinuousOn (fun p : ℝ × ℝ => wChem p.1 p.2) (I.prod Set.univ) ∧
    ContinuousOn (fun p : ℝ × ℝ => wLog p.1 p.2) (I.prod Set.univ) := by
  -- finite calculus closure, not PDE smoothing
```

This theorem is the right replacement for many small, ad hoc regularity hypotheses.

## 2. Why not formalize interior `C∞` smoothing?

The statement

```text
mild solution of a semilinear parabolic equation with smooth nonlinearity
⇒ smooth on (0,T)×(0,1)
```

is mathematically standard. But in Lean it would require a large theory:

```text
analytic semigroup smoothing in a scale of Banach spaces;
bootstrapping across time and space derivatives;
boundary compatibility or interior-only localization;
composition theorems in those spaces;
resolver regularity at each bootstrapped level;
conversion back to the exact cosine/source coefficient packages.
```

That is far more work than the finite package you actually need. Since your EWA development already has weighted-Wiener controls and coefficient time derivatives, a **finite regularity bootstrap** is much cheaper.

In short:

```text
Interior C∞ theorem: elegant on paper, expensive in Lean.
Finite EWA calculus closure: less glamorous, much cheaper and exactly targets the remaining packages.
```

## 3. Spatial flux differentiability `(b)` is mechanical

Let

```text
Φ(y) := (1+y)^(-β),
G(x) := u(x) * v_x(x) * Φ(v(x)).
```

Assume at the slice `t`:

```text
u is C¹ at x,
v is C² at x,
1+v(x)>0.
```

Then

```text
G'(x)
 = u_x v_x (1+v)^(-β)
   + u v_xx (1+v)^(-β)
   - β u v_x^2 (1+v)^(-β-1).
```

There is no hidden obstruction from non-integer `β`: the real power map

```text
y ↦ y^(-β)
```

is smooth on the open set `y>0`. Here the base is `1+v`, and since `v≥0` or `v>0`, we have `1+v>0`.

Lean-oriented chain-rule proof:

```lean
-- pointwise hypotheses at x
hu  : HasDerivAt u ux x
hv1 : HasDerivAt v vx x
hvx : HasDerivAt (deriv v) vxx x
hbase : 0 < 1 + v x

-- real-power composition
hpow : HasDerivAt (fun y => y ^ (-β)) ((-β) * (1 + v x) ^ (-β - 1)) (1 + v x)
hbase_deriv : HasDerivAt (fun x => 1 + v x) (deriv v x) x
hPhi : HasDerivAt (fun x => (1 + v x) ^ (-β))
        ((-β) * (1 + v x) ^ (-β - 1) * deriv v x) x :=
  hpow.comp x hbase_deriv

-- products
hflux : HasDerivAt
  (fun x => u x * deriv v x * (1 + v x) ^ (-β))
  (deriv u x * deriv v x * (1 + v x)^(-β)
    + u x * iteratedDeriv 2 v x * (1 + v x)^(-β)
    - β * u x * (deriv v x)^2 * (1 + v x)^(-β-1))
  x := by
  -- `hu.mul hvx` then `.mul hPhi`, ring normalize
```

If your flux is exactly

```text
chemFluxLifted = u * v_x / (1+v)^β,
```

rewrite it as

```text
u * v_x * (1+v)^(-β)
```

and use the formula above.

## 4. Source continuity `(c)` is also mechanical, but needs joint continuity

For the chem source

```text
wChem = ∂x( u v_x (1+v)^(-β) )
```

use the explicit formula:

```text
wChem
 = u_x v_x (1+v)^(-β)
   + u v_xx (1+v)^(-β)
   - β u v_x^2 (1+v)^(-β-1).
```

For the logistic source, writing the logistic constants as `r,b,α` to avoid conflict with `a=-χ₀`,

```text
wLog = u * (r - b * u^α).
```

If `u>0`, the real power `u^α` is smooth, even for non-integer `α`.

The continuity proof is just:

```text
joint continuity of u, u_x, v, v_x, v_xx
+ positivity of 1+v and u
+ continuity of real powers on positive bases
+ product/addition continuity
⇒ joint continuity of wChem and wLog.
```

Important caveat: **per-slice `C²` alone gives continuity in `x` at fixed `t`, not joint continuity in `(t,x)`**. For `h_src_cont` as a joint statement, you need local uniform coefficient convergence and time-continuity of the coefficients, for example:

```text
t ↦ uCoeff(t) is continuous into A₂,
t ↦ vCoeff(t) is continuous into A₄,
```

or explicit epsilon-majorant versions. Your coefficient time derivative / EWA data likely already gives this, but it must be stated.

Lean-shaped theorem:

```lean
theorem source_joint_cont_of_joint_C2
    (hu0  : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) domain)
    (hux  : ContinuousOn (fun p => deriv (u p.1) p.2) domain)
    (hv0  : ContinuousOn (fun p => v p.1 p.2) domain)
    (hvx  : ContinuousOn (fun p => deriv (v p.1) p.2) domain)
    (hvxx : ContinuousOn (fun p => iteratedDeriv 2 (v p.1) p.2) domain)
    (hu_pos : ∀ p∈domain, 0 < u p.1 p.2)
    (hv_base : ∀ p∈domain, 0 < 1 + v p.1 p.2) :
    ContinuousOn (fun p => wChem p.1 p.2) domain ∧
    ContinuousOn (fun p => wLog p.1 p.2) domain := by
  -- continuity algebra and `Real.continuousAt_rpow_const` on positive bases
```

## 5. The genuinely hard package `(a)`

`DuhamelSourceTimeC1` is the real analytic core.

For the logistic source:

```text
L(u) := u (r - b u^α),
L_t = u_t (r - b(1+α)u^α).
```

This is easy once `u_t` is in the right EWA space and `u>0`.

For the chem flux:

```text
G := u v_x (1+v)^(-β).
```

The time derivative is

```text
G_t
 = u_t v_x (1+v)^(-β)
   + u (v_t)_x (1+v)^(-β)
   - β u v_x v_t (1+v)^(-β-1).
```

The chem source is `∂x G`, so its time derivative is

```text
(∂xG)_t = ∂x(G_t).
```

To make this coefficientwise and summably bounded, a convenient finite assumption is:

```text
u_t ∈ A₁ locally uniformly in time,
u ∈ A₂ locally uniformly in time,
v = Rμ u,       so v ∈ A₄,
v_t = Rμ u_t,   so v_t ∈ A₃.
```

Then:

```text
v_x ∈ A₃,
(v_t)_x ∈ A₂,
(1+v)^(-β) ∈ A₂ or better,
G_t ∈ A₁,
∂xG_t ∈ A₀.
```

Since `A_s` is a Banach algebra for weighted Wiener norms and derivative maps `A_s → A_{s-1}`, this gives:

```text
t ↦ sourceCoeff(t) is differentiable into A₀,
sourceCoeffDot(t) = coeffs(∂xG_t + L_t),
sourceCoeffDot has a locally uniform ℓ¹ majorant,
sourceCoeffDot is continuous in time into A₀.
```

That is exactly the content needed by `DuhamelSourceTimeC1`.

A good theorem statement is:

```lean
theorem DuhamelSourceTimeC1_of_EWA_core
    (hcore : EWAClassicalCore uCoeff uDotCoeff vCoeff vDotCoeff I)
    (halpha : ... ) (hbeta : ... )
    (hAlg : WeightedWienerAlgebraClosure) :
    DuhamelSourceTimeC1
      (fun t => chemSourceCoeff t + logisticSourceCoeff t)
      (fun t => chemSourceCoeffDot t + logisticSourceCoeffDot t) := by
  -- logistic time derivative by smooth composition
  -- resolver time derivative v_t = Rμ u_t
  -- flux time derivative formula for G_t
  -- derivative map A₁→A₀ for ∂xG_t
  -- coefficient linearity
  -- local ℓ¹ majorant and continuity in A₀
```

This is the one to attack with full effort.

## 6. Boundary/coefficient subtlety for the divergence source

If you identify the cosine coefficients of `∂xG` by integration by parts, remember the boundary term.

For Neumann `v_x=0` at `x=0,1`,

```text
G = u v_x (1+v)^(-β)
```

vanishes at the endpoints. For `G_t`, the boundary value also vanishes if `(v_t)_x=0` at the endpoints, which follows from `v_t=Rμ u_t` with Neumann resolver data. Then

```text
⟨∂xG, cos(nπx)⟩ = -⟨G, ∂x cos(nπx)⟩,
```

and similarly for the time derivative.

If your source coefficients are defined spectrally rather than by integrals, this may already be built into the lift. But if a proof gets stuck, check that the flux boundary term is explicitly available.

## 7. Difficulty ranking

### Tier 1 — genuinely hard analytic core

```text
(a) DuhamelSourceTimeC1
```

Reasons:

```text
- requires time differentiability of nonlinear source coefficients;
- requires local ℓ¹/weighted-Wiener majorants for the source derivative;
- chem part needs v_t and (v_t)_x through the resolver;
- divergence source needs one spatial derivative of G_t;
- real-power composition must be done in a weighted-Wiener algebra, not just pointwise;
- coefficient formula may need boundary-term control.
```

This is where the proof effort should go.

### Tier 2 — moderate/mechanical but needs the right joint hypotheses

```text
(c) h_src_cont
```

The algebra is easy, but do not try to prove joint continuity from per-slice `C²` alone. Use local uniform weighted-Wiener convergence and time-continuity into `A₂/A₄`.

### Tier 3 — easiest pointwise calculus

```text
(b) h_flux_diff
```

This is immediate from `u∈C¹`, `v∈C²`, and `1+v>0`. It is a chain-rule/product-rule lemma. No serious PDE analysis remains here.

### Already essentially direct

```text
resolver C² / v positivity
```

`v∈C²` is direct from `v̂_k=û_k/(μ+λ_k)` and weighted-Wiener smoothing. Positivity of `v` is direct from the positive Neumann resolvent kernel or maximum principle, not from spectral summability.

## 8. Final recommended implementation plan

1. **Prove `h_flux_diff` now** as a local chain-rule lemma. It should be short.

2. **Prove `h_src_cont` from a reusable joint-continuity theorem** using the explicit source formula. This should be a moderate but mechanical continuity proof.

3. **Define `EWAClassicalCore`** with precisely the finite time/spatial regularity needed:

   ```text
   u∈C_t A₂,
   u_t∈C_t A₁,
   v=Rμu,
   v_t=Rμu_t,
   u>0,
   v≥0.
   ```

4. **Prove `DuhamelSourceTimeC1_of_EWA_core`**. This is the main theorem. It should consume weighted-Wiener algebra, derivative-loss, smooth-composition, and resolver-smoothing lemmas.

5. Wire `(a)+(b)+(c)` from that theorem and the two mechanical lemmas. Avoid introducing a broad interior-smoothing theorem unless you later need many more regularity levels.

## Bottom line

The remaining frontier is not “classical PDE smoothing” in full generality. It is a finite calculus problem in your EWA coefficient algebra. The only truly hard package is `DuhamelSourceTimeC1`; `h_flux_diff` and `h_src_cont` are mechanical consequences of the already-proved spatial `C²` data plus local uniform time-continuity. The best unification is a finite `EWAClassicalCore ⇒ source regularities` theorem, not an all-purpose `C∞` interior-regularity development.
