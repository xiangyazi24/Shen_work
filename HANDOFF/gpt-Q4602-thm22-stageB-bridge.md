ANSWER Q4602 0e5ad64a

# Chen–Ruau–Shen Paper 3, Theorem 2.2: the Stage B positive-time smoothing bridge

## Executive answer

The correct Stage B statement is the paper's Lemma 3.3:

> Fix `1/2 < σ < 1`, `p > 1`, and a positive constant state `u*`. For every Stage-A radius `ε > 0`, there exist `δ∞ > 0` and `T₀ > 0` such that
> `‖u₀-u*‖∞ ≤ δ∞` implies `Tmax(u₀) > T₀` and
> `‖u(T₀;u₀)-u*‖_{X_p^σ} ≤ ε`.

Here

```text
A_p := -Δ_N + μ I  on L^p,
X_p^σ := D(A_p^σ),
1/2 < σ < 1,
2σ - N/p > 1,
```

so `X_p^σ ↪ C¹`. On `[0,1]`, `N=1`, and one may take any `p>1` and `σ` satisfying `2σ-1/p>1`. If the base space is specifically `L²`, this requires `σ>3/4` for the `C¹` embedding.

The paper does **not** quantify `δ∞`. Its proof is a compactness/continuous-dependence proof:

```text
L∞-small initial data
  → existence and the invariant band u*/2 ≤ u ≤ 2u* on [0,T₀]       (3.3)
  → uniform C^{1,2} regularity on [T₀/2,T₀]                          (3.5)
  → compactness + uniqueness
  → endpoint continuity C(Ī) → X_p^σ at time T₀
  → X_p^σ entry.
```

This is Lemma 3.3 on pp. 17–18 of arXiv:2604.02599v1. Section 5.1 then restarts at `T₀` and applies Appendix Lemma A.1/Henry to obtain exponential decay for all `t≥T₀`.

A quantitative Duhamel replacement is possible, but one must state the finite-window source regularity honestly. For the actual chemotaxis equation, **an L∞ bound alone does not imply that the divergence-form nonlinear remainder is an `L²`/`L^p` function at time zero**. The safe quantitative proof either:

1. assumes an explicit `X`-valued finite-window nonlinear source bound; or
2. splits the Duhamel integral at `τ=T₀/2`, uses divergence-form smoothing on `[0,τ]`, and uses positive-time `C¹/C²` regularity on `[τ,T₀]`.

The second route mirrors the paper and is the recommended Lean target.

---

# 1. Linear fractional smoothing and the full Duhamel estimate

Write the perturbation equation as

```text
w_t = Lw + N(w),
A := -L,
S(t) := e^{-At}.
```

Assume that the Neumann cosine modes `φ_n` diagonalize `A`:

```text
A φ_n = d_n φ_n,
d_n = -σ_n,
d_n ≥ δ > 0,
d_n ≥ c_* (1+λ_n).
```

The second lower bound identifies the fractional domain with the corresponding Neumann Sobolev scale. On `L²(0,1)`,

```text
‖z‖_{X^σ} := ‖A^σ z‖₂
```

is equivalent to a weighted cosine norm and, because `A` is invertible, is equivalent to the usual graph norm.

## 1.1 A small correction to the proposed decay formula

Modewise,

```text
‖A^σ S(t)f‖_X
  ≤ (sup_n d_n^σ e^{-d_n t}) ‖f‖_X.
```

The elementary inequality

```text
x^σ e^{-xt} ≤ (σ/e)^σ t^{-σ}
```

immediately gives the analytic smoothing factor `t^{-σ}`. To retain an exponential factor uniformly for all `t>0`, use any `0<ω<δ`:

```text
d^σ e^{-dt}
 = d^σ e^{-(d-ω)t} e^{-ωt}
 ≤ (δ/(δ-ω))^σ (σ/e)^σ t^{-σ} e^{-ωt}.
```

Hence

```text
‖S(t)f‖_{X^σ}
≤ C_{σ,δ,ω} t^{-σ} e^{-ωt} ‖f‖_X,                 (1.1)

C_{σ,δ,ω}
:= (δ/(δ-ω))^σ (σ/e)^σ.
```

The frequently written bound `C t^{-σ}e^{-δt}` is not literally uniform for all large `t`: at the lowest mode `d=δ`, it would require `δ^σ≤Ct^{-σ}`. One may instead use either

```text
C (1+t^{-σ}) e^{-δt}
```

or (1.1) with an arbitrary `ω<δ`. Since Stage A also uses any rate below the spectral gap, (1.1) is the natural form.

On the unit interval, `L∞ ↪ L^p` with embedding constant one:

```text
‖f‖_p ≤ ‖f‖∞.
```

## 1.2 Exact endpoint Duhamel estimate

For a mild solution on `[0,T₀]`,

```text
w(T₀)
 = S(T₀)w₀ + ∫₀^{T₀} S(T₀-s)N(w(s)) ds.
```

Applying (1.1),

```text
‖w(T₀)‖_{X^σ}
≤ C_S T₀^{-σ}e^{-ωT₀} ‖w₀‖_X
 + C_S ∫₀^{T₀}
     (T₀-s)^{-σ}e^{-ω(T₀-s)} ‖N(w(s))‖_X ds,      (1.2)
```

where `C_S=C_{σ,δ,ω}` up to the equivalence constant between the chosen fractional norm and `‖A^σ·‖`.

Define

```text
I_{σ,ω}(T)
:= ∫₀^T r^{-σ}e^{-ωr} dr.
```

Because `σ<1`, this is finite, with the Lean-friendly estimate

```text
I_{σ,ω}(T) ≤ T^{1-σ}/(1-σ).                       (1.3)
```

For `ω>0`, its exact special-function value is

```text
I_{σ,ω}(T)
 = ω^{σ-1} γ(1-σ,ωT),
```

where `γ` is the lower incomplete gamma function; this exact expression is unnecessary for formalization.

## 1.3 Quantitative bridge under a finite-window quadratic source bound

Suppose the local theory proves that, whenever `‖w₀‖∞≤ρ≤ρ_loc(T₀)`,

```text
sup_{0≤s≤T₀} ‖N(w(s))‖_X ≤ K_{T₀} ρ².             (1.4)
```

Then (1.2)–(1.3) give

```text
‖w(T₀)‖_{X^σ}
≤ A_{T₀} ρ + B_{T₀} ρ²,                            (1.5)
```

with

```text
A_{T₀}
:= C_S C_{∞→X} T₀^{-σ}e^{-ωT₀},

B_{T₀}
:= C_S K_{T₀} I_{σ,ω}(T₀)
 ≤ C_S K_{T₀} T₀^{1-σ}/(1-σ).                     (1.6)
```

On `[0,1]`, `C_{∞→L^p}=1`.

Let `ε_A>0` be the Stage-A fractional-space radius. The exact largest positive algebraic radius solving

```text
A_{T₀}ρ+B_{T₀}ρ² ≤ ε_A
```

is

```text
ρ_quad(T₀)
:= 2ε_A /
   (A_{T₀}+sqrt(A_{T₀}²+4B_{T₀}ε_A))              (1.7)
```

when `B_{T₀}>0`; when `B_{T₀}=0`, take `ρ_quad=ε_A/A_{T₀}`. Equivalently, a simpler sufficient radius is

```text
min { ε_A/(2A_{T₀}), sqrt(ε_A/(2B_{T₀})) }.
```

Thus the quantified Stage-B threshold is

```text
ρ_∞(T₀)
:= min { ρ_loc(T₀), ρ_quad(T₀) }.                  (1.8)
```

Then

```text
‖w₀‖∞ ≤ ρ_∞(T₀)
  ⇒ ‖w(T₀)‖_{X^σ} ≤ ε_A.
```

This is the clean abstract answer to part (1).

---

# 2. The real chemotaxis subtlety: why the finite-window source bound is not automatic

For the v-eliminated chemotaxis PDE, after subtracting the full linearization, the nonlinear remainder has the schematic form

```text
N(w) = ∂ₓ Q₂(w) + R₂(w),                           (2.1)
```

where:

- `Q₂(0)=0`, `DQ₂(0)=0` is the quadratic flux remainder;
- `R₂(0)=0`, `DR₂(0)=0` is the quadratic reaction/resolvent remainder;
- the elliptic perturbation is

```text
z = v-v*
  = ν(μ-∂ₓₓ_N)^{-1}((u*+w)^γ-(u*)^γ).
```

On a fixed positive band around `u*`, the scalar maps are smooth and the elliptic resolver is bounded, so one obtains estimates such as

```text
‖Q₂(w)‖_p + ‖R₂(w)‖_p ≤ K₀ ‖w‖∞²,                 (2.2)
```

but `∂ₓQ₂(w)` need not belong to `L^p` for a merely continuous initial perturbation. Therefore, (1.4) does **not** follow from the L∞ invariant band alone.

This is why the paper does not estimate the nonlinear integral from time zero in the strong-space formulation. It waits to a positive subwindow and invokes parabolic/elliptic regularity.

## 2.1 Paper-faithful local existence and L∞ control

The paper's Lemma 3.3 first invokes the Part-I local theory to choose `T₀>0` and `0<δ₀<u*/2` such that

```text
‖w₀‖∞≤δ₀
⇒ Tmax(w₀)>T₀
   and
   u*/2 ≤ u(t,x;u₀) ≤ 2u*
   for 0≤t≤T₀.                                     (2.3)
```

This is equation (3.3) of the paper. It simultaneously provides:

- existence on the whole bridge interval;
- positivity, hence no singularity in the powers around `u*`;
- a compact range on which all scalar nonlinearities have uniform Lipschitz/Taylor constants;
- uniform elliptic estimates for `v`.

A direct short-time contraction gives the same type of statement. Write the perturbation mild equation using the Neumann heat semigroup, keeping the chemotaxis term in divergence form:

```text
w(t)
 = H(t)w₀
   + ∫₀^t ∂ₓH(t-s) Q_full(w(s)) ds
   + ∫₀^t H(t-s) R_full(w(s)) ds.                  (2.4)
```

On a fixed band `‖w‖∞≤r_band`, suppose

```text
‖Q_full(w)‖∞ ≤ L_Q ‖w‖∞,
‖R_full(w)‖∞ ≤ L_R ‖w‖∞,

‖H(t)‖_{C→C} ≤ M₀,
‖∂ₓH(t)‖_{C→C} ≤ C_G t^{-1/2}.
```

For

```text
Z(t):=sup_{0≤s≤t} ‖w(s)‖∞,
```

(2.4) yields

```text
Z(t)
≤ M₀ρ + Θ(t)Z(t),

Θ(t):=2C_G L_Q sqrt(t)+M₀L_R t.                    (2.5)
```

Choose and then freeze `T₀>0` so that `Θ(T₀)<1`, for example `Θ(T₀)≤1/2`. Then

```text
Z(T₀) ≤ C₀ρ,
C₀:=M₀/(1-Θ(T₀)) ≤ 2M₀.                           (2.6)
```

Taking

```text
ρ_loc(T₀)
≤ min { r_band/C₀, u*/(2C₀) }
```

closes the invariant band. The same `Θ(T₀)<1` estimate applied to differences gives contraction/uniqueness.

This is a quantified version of the finite-time local fact used in (3.3).

## 2.2 Positive-time regularity on `[T₀/2,T₀]`

Set

```text
τ:=T₀/2.
```

The paper uses (2.3) plus standard parabolic/elliptic regularity to obtain

```text
sup ‖u‖_{C^{1,2}([τ,T₀]×Ī)} < ∞.                  (2.7)
```

For a quantitative bridge one needs the corresponding local-Lipschitz version around the equilibrium:

```text
sup_{τ≤s≤T₀}
  (‖w(s)‖_{C¹}+‖z(s)‖_{C²})
≤ C_reg(T₀) ρ.                                     (2.8)
```

Once (2.8) is available, Taylor expansion at the equilibrium gives

```text
sup_{τ≤s≤T₀} ‖N(w(s))‖_X
≤ K_reg C_reg(T₀)² ρ².                             (2.9)
```

**This positive-time, locally Lipschitz regularization estimate is the hardest analytic component of a fully quantitative Stage B.** The paper proves only the qualitative endpoint continuity needed for Lemma 3.3, by compactness and uniqueness.

## 2.3 The safe split Duhamel estimate for the actual PDE

Assume the semigroup estimates

```text
‖A^σS(r)f‖_X
  ≤ C_σ r^{-σ}e^{-ωr} ‖f‖_X,

‖A^σS(r)∂ₓf‖_X
  ≤ C_{σ,1} r^{-(σ+1/2)}e^{-ωr} ‖f‖_X.             (2.10)
```

Split at `τ=T₀/2`:

```text
w(T₀)
= S(T₀)w₀
 + ∫₀^τ S(T₀-s)(∂ₓQ₂(w(s))+R₂(w(s))) ds
 + ∫_τ^{T₀} S(T₀-s)N(w(s)) ds.                    (2.11)
```

The early interval is safe in divergence form because `T₀-s≥T₀/2`; there is no endpoint singularity. The late interval is safe in `X` because (2.8)–(2.9) hold and `σ<1`.

Define

```text
J_{a,ω}(T,τ)
:= ∫₀^τ (T-s)^{-a}e^{-ω(T-s)} ds
 = ∫_{T-τ}^T r^{-a}e^{-ωr} dr.
```

Then (2.2), (2.6), and (2.9) imply

```text
‖w(T₀)‖_{X^σ}
≤ A_{T₀}ρ + B^{split}_{T₀}ρ²,                     (2.12)
```

where

```text
A_{T₀}
:= C_σ C_{∞→X}T₀^{-σ}e^{-ωT₀},

B^{split}_{T₀}
:= C_{σ,1} K_Q C₀² J_{σ+1/2,ω}(T₀,τ)
 + C_σ     K_R C₀² J_{σ,ω}(T₀,τ)
 + C_σ K_reg C_reg(T₀)² I_{σ,ω}(T₀-τ).             (2.13)
```

Every term is finite. Elementary Lean-friendly bounds are

```text
J_{a,ω}(T,τ)
≤ τ (T-τ)^{-a}e^{-ω(T-τ)},

I_{σ,ω}(T-τ)
≤ (T-τ)^{1-σ}/(1-σ).                              (2.14)
```

With `τ=T₀/2`, the early flux constant behaves like `T₀^{1/2-σ}` and the homogeneous smoothing constant behaves like `T₀^{-σ}` as `T₀↓0`.

Use (1.7)–(1.8) with `B^{split}_{T₀}` in place of `B_{T₀}`.

## 2.4 An alternative weighted-space formula

In a genuinely semilinear abstract problem where, for some `0≤θ<1/2`,

```text
‖w(s)‖_{X^θ} ≤ C_θ s^{-θ}ρ,
‖N(z)‖_X ≤ K_N ‖z‖_{X^θ}²,
```

one can integrate from time zero directly:

```text
∫₀^{T₀}(T₀-s)^{-σ}‖N(w(s))‖_X ds
≤ K_N C_θ² ρ²
   T₀^{1-σ-2θ} B(1-2θ,1-σ).                       (2.15)
```

The conditions `σ<1` and `2θ<1` are exactly the endpoint-integrability conditions. This elegant formula is **not automatically applicable** to the chemotactic divergence nonlinearity in the paper; the split proof above is safer.

---

# 3. Why `T₀` is fixed positive

There are two distinct singularities to track.

1. The Duhamel kernel

```text
(T₀-s)^{-σ}
```

is integrable at `s=T₀` precisely because `σ<1`.

2. The homogeneous smoothing constant

```text
T₀^{-σ}
```

blows up as `T₀↓0`.

Consequently,

```text
A_{T₀}≈C T₀^{-σ},
ρ_quad(T₀)≈ε_A T₀^σ/C
```

for small `T₀`. Thus the admissible L∞ radius collapses as `T₀→0`. In the split chemotaxis estimate, the early divergence constant also behaves like `T₀^{1/2-σ}`, which blows up because the paper takes `σ>1/2`.

There is no mysterious universal lower bound on `T₀`; one simply:

```text
(a) chooses one positive T₀ for which the local invariant-band theory closes,
(b) freezes that T₀,
(c) chooses the L∞ radius afterward.
```

This is exactly the logical order in Lemma 3.3: first `T₀,δ₀` for (3.3), then a smaller `δ` depending on the desired `X_p^σ` radius.

---

# 4. Assembly with Stage A

Assume Stage A supplies constants

```text
ε_A>0,
M_A≥1,
0<λ<δ_A,
```

such that

```text
‖z₀‖_{X^σ}≤ε_A
⇒ solution exists globally and
   ‖z(t)‖_{X^σ}
   ≤ M_A e^{-λt} ‖z₀‖_{X^σ}
   for all t≥0.                                    (4.1)
```

For the non-minimal equilibrium in the paper,

```text
δ_A = min { aα, inf_{n≥1} d_n }.
```

For the minimal mass-constrained branch, remove the constant mode and use

```text
δ_A = inf_{n≥1} d_n.
```

Fix `T₀` and let `ρ∞(T₀)` be defined by (1.8), using either `B_{T₀}` or the paper-faithful `B^{split}_{T₀}`. If

```text
‖u₀-u*‖∞≤ρ∞(T₀),
```

then Stage B gives

```text
‖u(T₀;u₀)-u*‖_{X^σ}≤ε_A.
```

Restarting at `T₀` and applying (4.1),

```text
‖u(t;u₀)-u*‖_{X^σ}
≤ M_A e^{-λ(t-T₀)}
   ‖u(T₀;u₀)-u*‖_{X^σ},
                                             t≥T₀. (4.2)
```

Using (1.5) or (2.12), this yields the Lipschitz-scaled eventual estimate

```text
‖u(t;u₀)-u*‖_{X^σ}
≤ M_A (A_{T₀}+B_{T₀}ρ∞(T₀))
   e^{-λ(t-T₀)} ‖u₀-u*‖∞,
                                             t≥T₀. (4.3)
```

The embedding `X_p^σ↪C¹` and the elliptic resolvent estimate for `v-v*` give

```text
‖u(t;u₀)-u*‖_{C¹}
 + ‖v(t;u₀)-v*‖_{C¹}
≤ C_ev e^{-λ(t-T₀)} ‖u₀-u*‖∞,
                                             t≥T₀, (4.4)
```

where one may take

```text
C_ev
:= C_out M_A (A_{T₀}+B_{T₀}ρ∞(T₀)).
```

Here `C_out` is the sum of the `X_p^σ→C¹` embedding constant and the local elliptic-resolvent/power-map constant controlling `v-v*` by `u-u*`.

Absorbing `ρ∞(T₀)` into the constant gives the weaker basin-style form

```text
‖u(t)-u*‖_{C¹}+‖v(t)-v*‖_{C¹}
≤ C e^{-λ(t-T₀)},
                                             t≥T₀. (4.5)
```

## Honest eventual Theorem 2.2 nonlinear clause

A paper-faithful corrected statement is therefore:

> Let `(u*,v*)` be the positive equilibrium and assume the exact discrete spectral-stability condition, so that `d_n=-σ_n` have a positive gap. Choose `p>1` and `1/2<σ<1` with `2σ-1/p>1`. Then for every `0<λ<δ_A`, there exist `T₀>0`, `ρ∞>0`, and `C_ev>0` such that every positive continuous initial datum satisfying
>
> ```text
> ‖u₀-u*‖∞≤ρ∞
> ```
>
> generates a global solution and
>
> ```text
> ‖u(t)-u*‖_{C¹}+‖v(t)-v*‖_{C¹}
> ≤ C_ev e^{-λ(t-T₀)} ‖u₀-u*‖∞
> ```
>
> for every `t≥T₀`.

This is what the argument in §5.1 actually proves. The paper's displayed all-time estimate is obtained after the sentence “setting `s=t+T₀` and enlarging `C`,” but that sentence does not control `[0,T₀)` in `C¹` from an L∞-only initial neighborhood.

---

# 5. Paper audit: what is literal and what is a quantitative strengthening

Source: Le Chen, Ian Ruau, Wenxian Shen, *Chemotaxis models with signal-dependent sensitivity and a logistic-type source, II: Persistence and stabilization*, arXiv:2604.02599v1.

The relevant exact dependencies are:

```text
Proposition 1.1:
  positive continuous data → unique local classical solution,
  L∞ initial trace, positivity, blow-up alternative.

Lemma 3.3, pp. 17–18:
  for every ε>0, ∃δ,T₀>0,
  L∞-small → existence to T₀ and X_p^σ-small at T₀.

Equation (3.3):
  u*/2 ≤ u ≤ 2u* on [0,T₀].

Equation (3.5):
  uniform C^{1,2} regularity on [T₀/2,T₀].

Appendix Lemma A.1:
  X_p^σ-small → all-time X_p^σ exponential stability.

Appendix Lemma A.2:
  analytic-semigroup fractional smoothing.

§5.1, equations (5.5)–(5.6):
  restart at T₀ and exponential decay thereafter.
```

The explicit formulas (1.5)–(1.8) and (2.12)–(2.14) above are a quantitative strengthening suitable for Lean, not formulas stated in the paper.

---

# 6. Lean-4-formalizable dependency order

Use `σ` for the fractional exponent so it is not confused with the logistic exponent `p.α`.

## Lemma 1 — modewise fractional smoothing

```lean
/-- Spectral gap + diagonal cosine representation imply analytic fractional
smoothing, with any exponential rate strictly below the gap. -/
theorem fullLinearizedSemigroup_fractionalSmoothing
    {σ δ ω : ℝ}
    (hσ0 : 0 ≤ σ) (hσω : σ < 1)
    (hδ : 0 < δ) (hω0 : 0 ≤ ω) (hωδ : ω < δ)
    (hgap : ∀ n, δ ≤ d n) :
    ∃ Cs > 0, ∀ t > 0, ∀ f,
      fracNorm σ (S t f) ≤
        Cs * t ^ (-σ) * Real.exp (-ω * t) * ‖f‖ := ...
```

For `L²`, prove it by Parseval and

```text
d^σ e^{-dt}
≤ (δ/(δ-ω))^σ (σ/e)^σ t^{-σ}e^{-ωt}.
```

## Lemma 2 — finite-window local existence and invariant band

```lean
/-- L∞-small perturbations exist on one common positive interval and remain
inside a fixed positive band. -/
theorem stageB_localSupControl
    (huStar : 0 < uStar) :
    ∃ T₀ > 0, ∃ ρloc > 0, ∃ C0 > 0,
      ∀ w₀, ‖w₀‖∞ ≤ ρloc →
        ExistsOn w T₀ ∧
        (∀ t ∈ Set.Icc 0 T₀, ‖w t‖∞ ≤ C0 * ‖w₀‖∞) ∧
        (∀ t ∈ Set.Icc 0 T₀, ∀ x,
          uStar / 2 ≤ uStar + w t x ∧ uStar + w t x ≤ 2 * uStar) := ...
```

A direct proof packages (2.5): choose `T₀` with

```text
2 C_G L_Q sqrt(T₀)+M₀L_R T₀ < 1.
```

## Lemma 3 — positive-time nonlinear source majorant **[HARDEST]**

```lean
/-- After waiting to τ=T₀/2, parabolic/elliptic regularity makes the full
quadratic remainder X-valued and quantitatively small. -/
theorem stageB_positiveTimeSourceMajorant
    (hlocal : StageBLocalSupControl ...)
    (τ : ℝ) (hτ : τ = T₀ / 2) :
    ∃ KQ KR KN Creg,
      (∀ s ∈ Set.Icc 0 τ,
        ‖Q₂ (w s)‖ ≤ KQ * ‖w₀‖∞ ^ 2 ∧
        ‖R₂ (w s)‖ ≤ KR * ‖w₀‖∞ ^ 2) ∧
      (∀ s ∈ Set.Icc τ T₀,
        ‖N (w s)‖ ≤ KN * ‖w₀‖∞ ^ 2) := ...
```

This should be built from:

```text
positive-time C¹ estimate for u,
elliptic C² estimate for v,
Taylor remainder bounds on the positive band,
source measurability/integrability.
```

This is the main analytic crux. It is also the honest formal counterpart of the paper's (3.5) plus endpoint compactness.

## Lemma 4 — split Duhamel endpoint bound

```lean
/-- The split Duhamel formula gives an explicit affine-quadratic endpoint
bound in the fractional norm. -/
theorem stageB_endpointXpSigma_le
    (hsm : FractionalSmoothingData ...)
    (hdiv : FractionalDivergenceSmoothingData ...)
    (hsrc : StageBPositiveTimeSourceMajorant ... ) :
    ∃ A B, 0 ≤ A ∧ 0 ≤ B ∧
      fracNorm σ (w T₀) ≤
        A * ‖w₀‖∞ + B * ‖w₀‖∞ ^ 2 := ...
```

Use the constants in (2.13), not a single unproved claim that `N(w(s))∈X` down to `s=0`.

## Lemma 5 — algebraic radius selection

```lean
/-- Explicit L∞ radius forcing entry into the Stage-A ball. -/
theorem affineQuadratic_le_of_le_entryRadius
    {A B ε ρ : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hε : 0 < ε)
    (hρ : 0 ≤ ρ)
    (hρle : ρ ≤
      2 * ε / (A + Real.sqrt (A ^ 2 + 4 * B * ε))) :
    A * ρ + B * ρ ^ 2 ≤ ε := ...
```

Handle `B=0` separately if division-side conditions make that cleaner.

## Lemma 6 — Stage B + Stage A = eventual exponential stability

```lean
/-- Sup-small data enter the genuine X_p^σ basin at T₀ and thereafter decay
exponentially. -/
theorem eventualExponential_of_supSmall_entry_and_stageA
    (hbridge : SupSmallToXpSigmaEntryAt T₀ ρ∞ εA)
    (hstageA : XpSigmaLocalExponentialStability εA M rate)
    (hemb : XpSigmaEmbedsC1 ...)
    (hres : EllipticPerturbationC1Bound ...) :
    ∃ Cev > 0, ∀ w₀,
      ‖w₀‖∞ ≤ ρ∞ →
      ∀ t, T₀ ≤ t →
        c1Distance (u t) uStar + c1Distance (v t) vStar ≤
          Cev * Real.exp (-rate * (t - T₀)) * ‖w₀‖∞ := ...
```

---

# 7. Repository-specific fidelity warning

The current files

```text
ShenWork/Paper3/IntervalDomainSectorial.lean
ShenWork/Paper3/IntervalDomainStabilityChain.lean
```

define the supposed `X_p^σ` distance to be the initial sup distance:

```lean
def intervalDomainSectorialXpSigmaDistance
    (_sigma _pNorm : ℝ) (f g : intervalDomain.Point → ℝ) : ℝ :=
  intervalDomain.supNorm (fun x => f x - g x)
```

and similarly for `intervalDomainXpSigmaDistance`.

That identification erases the actual Stage B and is not paper-faithful. The correct architecture is:

```text
initialSupDistance u₀ u*

        -- positive-time smoothing bridge, Lemma 3.3 --
                    ↓ at T₀

genuineXpSigmaDistance σ p (u T₀) u*

        -- Henry / Appendix Lemma A.1 --
                    ↓

eventual C¹ exponential decay.
```

In particular, do **not** prove or assume

```text
initial sup distance controls initial X_p^σ distance.
```

The true statement is

```text
small initial sup distance controls the X_p^σ distance at one fixed positive time.
```

That is exactly the missing Stage B frontier to add before claiming the nonlinear half of the headline theorem.
