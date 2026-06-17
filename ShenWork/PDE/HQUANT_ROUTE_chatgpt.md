═══ BRIDGE cron2 | 925efc6e | 11592 chars 1774 words 248 lines | 556s | prov=network | OK ═══
═══ BRIDGE cron2 | 925efc6e | 11592 chars 1774 words 248 lines | 556s | prov=network | OK ═══
## Verdict

For a **full classical** local solution from merely continuous positive-floor data, the irreducible analytic core is a **positive-time Hölder bootstrap plus a singular Duhamel/Schauder endpoint lemma**. A bounded chemotaxis source, or a source known only through `|cₙ| ≲ n⁻²` as an already-smoothed Duhamel output, is not enough to get `C²` by a raw heat-semigroup argument. The repo’s own audit says exactly this: bounded-source Duhamel gives only `|cₙ(t)| ≲ 1/λₙ ~ n⁻²`, hence `H^{s<3/2}`, `C⁰`, but not `C²`; forcing a bounded heat-value representation would assert false extra smoothness. fileciteturn76file0L22-L49

For Lean, I would **not** formalize abstract maximal regularity first. The lighter route is an explicit 1-D Neumann-kernel Hölder/cancellation stack: first build a uniform `C⁰` mild fixed point in an order box, then get positive-time Hölder regularity, then use the cancellation estimate for the singular `∂ₓₓS(t-s)` endpoint. This is also the route already encoded in the repo’s design/status notes. fileciteturn69file0L43-L63

---

## (1) Minimal source regularity for mild → classical

For the scalar heat equation on `[0,1]` with Neumann boundary,

```text
u_t - u_xx = f,
∂x u = 0 at 0,1,
```

the clean classical route is:

```text
f ∈ C^{θ/2, θ}_{t,x} locally away from t = 0
  ⟹ u ∈ C^{1+θ/2, 2+θ}_{t,x}
```

for any `0 < θ < 1`. For a positive-time theorem, you can weaken this in practice to: `f(t,·)` uniformly `C^θ` for `t ∈ [τ,T]`, sufficient time continuity/Duhamel interchange, and enough boundary compatibility encoded by the Neumann semigroup. You do **not** need initial datum `u₀ ∈ C²`; from continuous `u₀`, the classical statement should start at `t > 0`, with only initial trace as `t ↓ 0`.

The key estimate is the endpoint cancellation:

```text
∂xx S(σ) h(x)
  = ∫ ∂xx K_N(σ,x,y) (h(y) - h(x)) dy
```

because the Neumann heat kernel preserves constants, so

```text
∫ ∂xx K_N(σ,x,y) dy = 0.
```

If `h ∈ C^θ`, then

```text
‖∂xx S(σ) h‖∞ ≤ C σ^{-1+θ/2} [h]_{C^θ},
```

and `σ^{-1+θ/2}` is integrable at `σ = 0` for every `θ > 0`. This is the exact distinction between the false bounded-source route and the true Hölder-source route. The repo’s route notes explicitly record this: bounded source gives a non-integrable `∂xxK ~ (t-s)^{-3/2}` endpoint, while a `C^θ` source tames it to an integrable `(t-s)^{-1+θ/2}`. fileciteturn69file0L30-L40 fileciteturn69file0L43-L55

Given a cosine coefficient bound

```text
|cₙ| ≤ C / n²,
```

the represented spatial function is indeed `C^θ` for every `0 < θ < 1`, though generally not `C¹` and certainly not `C²`. In Sobolev language this is the same `H^{s<3/2}` threshold. So yes: **if those are the coefficients of the actual RHS source `f(t,·)`, then it is Hölder and Schauder is enough.** But if those are the coefficients of the **Duhamel output produced from a bounded source**, they only prove the output is Hölder-ish, not that one can differentiate it twice. That is the pitfall documented in `IntervalDuhamelRegularity`. fileciteturn76file0L31-L42

For the chemotaxis term, keep the divergence distinction explicit. The mild equation is naturally

```text
u(t) = S(t)u₀
       - χ₀ ∫₀ᵗ ∂x S(t-s) Q(s) ds
       + ∫₀ᵗ S(t-s) L(s) ds,
```

where `Q = u^m V_x` and `L = u(1-u^α)` or the corresponding logistic source. For **one spatial derivative**, the hard chemotaxis leg is

```text
∫ ∂xx S(t-s) Q(s) ds,
```

and `Q ∈ C^θ` suffices to get `u_x ∈ C^η`, `0 < η < θ`, by the same cancellation. This is exactly what `ChemMildC1eta.lean` formalizes: the file’s header states that `u ∈ C^θ` gives `Q = u·V_x ∈ C^θ`, and the divergence-form Schauder estimate gives an integrable rate `σ^{-1+(θ-η)/2}` for the chemotaxis leg of `u_x`. fileciteturn73file0L6-L20

For **full `u ∈ C²`**, you need one more level somewhere. Either prove the scalar non-divergence source

```text
F = -χ₀ ∂x Q + L
```

is `C^θ`, which requires `Q ∈ C^{1+θ}`, or prove an equivalent full divergence-form Schauder theorem. The repo notes this caveat too: the divergence leg needs `Q ∈ C^{1+θ}` for full `C²` if you rewrite `∂xS Q = S(Q_x)`, whereas the current `C^{1+η}` route is enough for the Wiener/EWA re-entry but not the standalone full-C² endpoint. fileciteturn69file0L83-L92

So the minimal regularity answer is:

```text
Full classical C²/C¹:
  f = -χ₀ ∂x Q + L must be C^θ in x, locally in positive time,
  plus enough time continuity/Duhamel interchange to identify u_t = u_xx + f.

Divergence-form chemotaxis:
  Q ∈ C^θ gives u ∈ C^{1+η};
  Q ∈ C^{1+θ}, or an equivalent divergence Schauder theorem, is needed for u ∈ C².
```

---

## Schauder vs analytic semigroup / maximal regularity

Analytic-semigroup language is conceptually fine:

```text
f ∈ C^θ_x
  ⟹ Duhamel term in D(A) with Hölder control
  ⟹ u_xx continuous.
```

But in Lean it is likely heavier than the explicit kernel route. You would have to formalize fractional domains, interpolation, sectorial estimates, Neumann realization of `A`, boundary domains, and maximal regularity. The 1-D Neumann kernel route is concrete: prove the kernel cancellation and weighted mass estimates once, then integrate the singular but integrable powers.

The repo is already following the kernel/Hölder route. `ChemMildC1eta.lean` says bricks 1–3 are the mean-zero and weighted-mass kernel estimates, and brick 4 is the `C^θ → C^η` second-derivative estimate. It even avoids a third-kernel-derivative route by a semigroup split/commutation argument. fileciteturn73file0L21-L38 fileciteturn73file0L53-L63

Recommendation: **use explicit 1-D Neumann kernel Schauder/cancellation**, not abstract maximal regularity.

---

## (2) Datum-uniform local existence

The clean mechanism is a **uniform contraction mapping in an order box**, not compactness.

Fix data class parameters:

```text
0 < r ≤ u₀(x) ≤ R₀  on [0,1],
u₀ ∈ C([0,1]).
```

Choose a working box, for example:

```text
r/2 ≤ u(t,x) ≤ R
```

with `R` depending only on `R₀`, `r`, and parameters. Then define the mild map

```text
Φ(u)(t)
  = S(t)u₀
    - χ₀ ∫₀ᵗ ∂x S(t-s) Q[u](s) ds
    + ∫₀ᵗ S(t-s) L[u](s) ds.
```

The contraction estimate should use:

```text
‖S(t)f‖∞ ≤ ‖f‖∞,
‖∂x S(t)f‖∞ ≤ C∇ t^{-1/2} ‖f‖∞,
∫₀ᵗ (t-s)^{-1/2} ds = 2√t.
```

The repo’s hQuant route says the same: local existence from `C(Ω̄)+floor` is a standard mild-solution contraction, with the chemotaxis term in divergence Duhamel form estimated by the heat-gradient bound and the short-time factor `2√t`; the contraction is in the order box `[r,R]`. fileciteturn69file0L16-L24

What must be uniform:

```text
T = T(p, r, R₀) > 0,
the order-box bounds r/2 and R,
the contraction constant < 1,
self-map estimates Φ(box) ⊆ box,
positivity/floor preservation,
resolver bounds for V[u] and V_x[u],
Lipschitz constants for u ↦ u^m, u^γ, u(1-u^α) on [r/2,R],
Lipschitz constants for Q[u] = u^m V_x[u],
positive-time Hölder/C^{1+η}/C² bounds on [τ,T], τ>0.
```

These constants must not depend on the particular modulus of continuity of `u₀`. They may depend on `‖u₀‖∞ ≤ R₀`, the floor `r`, the equation parameters, the interval, and the chosen positive-time cutoff `τ`.

A compactness/Schauder argument is worse for datum-uniformity. The set of continuous functions with only a sup bound and a positive floor is not compact in `C([0,1])`; you would still need a uniform equicontinuity mechanism, which is exactly what the semigroup estimates provide after positive time. For the actual local existence time, Banach contraction gives uniform constants directly.

---

## (3) Is the Hölder-source Schauder floor irreducible?

For a **full classical mild→classical theorem**, yes: some form of Hölder/cancellation Schauder is irreducible. A bounded-source shortcut is mathematically false, not just unavailable in Lean. The repo documents the obstruction: the `s ≈ t` part of the Duhamel integral prevents the bounded heat-value representation and only gives `1/n²` coefficients; differentiating the kernel twice gives a non-integrable `(t-s)^{-3/2}` singularity. fileciteturn76file0L36-L58

Energy/weak-solution routes do not really avoid this. They can produce weak or strong solutions, but to obtain the paper’s positive classical solution on a bounded interval with Neumann boundary, one eventually has to bootstrap to spatial Hölder or Schauder regularity and identify the PDE pointwise. That brings back the same endpoint estimate or a maximal-regularity theorem of comparable strength.

A fixed point directly in a Hölder space is possible, but for `u₀ ∈ C([0,1])` it either requires assuming Hölder initial data or building weighted positive-time Hölder norms such as

```text
sup_{0<t≤T} t^β [u(t)]_{C^θ}.
```

That is formalizable, but it is usually heavier than the two-stage route:

```text
C⁰ order-box contraction
  → positive-time C^θ smoothing
  → Hölder/cancellation Duhamel bootstrap
  → classical regularity or Wiener/EWA re-entry.
```

For this repo, I would split the final target:

1. **For hQuant/EWA re-entry:** the least-heavy route is to stop at `u(t₀) ∈ C^{1+η}` and use `C^{1+η} ⇒ Wiener ℓ¹`. The HEADLINES route says this avoids the full `C²` endpoint lemma for the headline’s hQuant chain, while keeping full `C²` as a separate Prop 1.1/local-classical goal. fileciteturn70file0L3-L10

2. **For a standalone positive classical solution:** keep `neumannDuhamel_positiveTime_C2_slice` or its divergence-form equivalent as the genuine analytic core. It should assume a `C^θ` non-divergence source, or `Q ∈ C^{1+θ}` for the flux form, and include the Duhamel derivative/time-interchange needed to prove `u_t = u_xx + f`.

The current `f89eeec` status says the Hölder bootstrap is largely built and the remaining carried hypothesis is the derivative-under-the-integral/interchange: the derivative of the mild representation exists and equals the split of initial, chemotaxis, and reaction legs. That is exactly the kind of representation lemma you should isolate as an analytic brick, not hide inside a regularity conclusion. fileciteturn70file0L59-L73

## Recommended Lean route

Use these layers:

```lean
-- Layer 1: uniform C⁰ mild existence
chemMildLocal_orderBox_exists
  (r R : ℝ) :
  ∃ T > 0, ∀ u₀, r ≤ u₀ → u₀ ≤ R →
    ∃ u, MildSolutionOn T u₀ u ∧
         (∀ t x, 0 ≤ t → t ≤ T → r/2 ≤ u t x ∧ u t x ≤ R')
```

This is the datum-uniform contraction layer.

```lean
-- Layer 2: positive-time Hölder
mild_orderBox_positiveTime_holder :
  MildSolutionOn T u₀ u →
  τ ∈ Ioo 0 T →
  UniformHolderOn θ (fun x => u t x) for t ∈ [τ,T]
```

This uses only `L∞ → C^θ` heat smoothing.

```lean
-- Layer 3a: hQuant shortcut
mild_orderBox_positiveTime_C1theta :
  ...
  → u(t₀,·) ∈ C^{1+η}

C1theta_implies_wiener_l1 :
  u(t₀,·) ∈ C^{1+η}
  → Summable |cosineCoeffs u(t₀)|
```

This is the minimal hQuant route.

```lean
-- Layer 3b: full classical
neumannDuhamel_positiveTime_C2_slice :
  source ∈ C^θ
  → Duhamel source term ∈ C²

neumannDuhamel_classical_regularize :
  mild equation + source regularity + DUI/interchange
  → u_t, u_xx continuous and PDE holds pointwise.
```

Layer 3b is the irreducible classical floor. Layer 3a is enough only if the EWA/Wiener engine then supplies the remaining classical source-regularity machinery.

Bottom line: **yes, Hölder source is the right threshold; yes, `|cₙ| ≲ n⁻²` gives enough Hölder for any exponent below one if it is the actual RHS; no, bounded-source smoothing is not enough; and for Lean the explicit Neumann-kernel Hölder/cancellation route is much lighter than abstract maximal regularity.**
