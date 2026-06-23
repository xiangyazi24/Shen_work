# Q73 (cron2): χ₀<0 chemotaxis boundedness — build vs rebuild verdict

## Executive verdict

**Rebuild the a-priori bound around the norm-based route.** Do not spend the main proof budget discharging the current coordinatewise/σ-ladder seams.

The current coordinatewise architecture is axiom-clean and useful as scaffolding, but it is proving the wrong base object for the PDE. A uniform-in-time coordinatewise `H^σ` envelope

```text
∃ g ∈ H^σ, ∀ k, sup_t |u_k(t)| ≤ g_k
```

is strictly stronger than the standard continuation quantity

```text
sup_t ||u(t)||_{H^σ} < ∞
```

and is not implied by a uniform Sobolev norm bound. That means the coordinatewise base seam is not just a missing lemma; it is a stronger invariant than the PDE needs. The over-quantified per-σ `CarrySeam` family then multiplies that extra strength across the whole ladder.

For the target **uniform `H¹` boundedness**, the least remaining Lean work should be:

```text
maximum principle L∞ bound
  → elliptic resolver L∞ bounds for v, v_x, v_xx
  → L² energy gives sliding-window integral of ||u_x||²
  → H¹ differential inequality y' ≤ A y + B
  → uniform Gronwall on sliding windows
  → optional one-shot coordinatewise envelope from Duhamel, only if an API still wants it.
```

So the recommendation is:

```text
Main theorem: rebuild as a norm-based uniform H¹ bound.
Old coordinatewise ladder: keep as optional/post-processing, not as the main route.
```

If the final formal object is currently named `TrajectoryHSigmaEnvelope 1` and literally means a coordinatewise `H¹` envelope, then that final object is stronger than “uniform `H¹` boundedness.” Either change the final statement to a norm bound, or derive the coordinatewise object after the norm/source estimates by a one-shot Duhamel lemma. Do not use it as the base of the global proof.

## Why finishing the current three seams is probably more work

The three carried seams are not comparable in difficulty:

1. **Per-mode mild decomposition** is standard and probably finite.
2. **Coordinatewise base envelope** is the real problem. It is stronger than a uniform norm bound and cannot be obtained just from `sup_t ||u(t)||_{H^σ}`. A trajectory can remain in a bounded `H^σ` ball while visiting different high modes at different times; the coordinatewise sup can fail to be in `H^σ`.
3. **Per-σ `CarrySeam` family** over-quantifies the regularity ladder. Even if each individual bridge is standard, the formal cost repeats across σ, products, resolver estimates, flux estimates, and mode summability.

By contrast, the norm route requires a small number of global estimates:

```text
L∞ comparison;
resolver max/elliptic bounds;
L² energy identity;
H¹ energy inequality;
uniform Gronwall.
```

These are analytically canonical and directly tied to the repulsive sign `χ₀<0` and logistic damping. They also prove exactly the needed continuation criterion.

## Setup and notation

Write

```text
a := -χ₀ > 0.
```

The equation becomes, in one space dimension,

```text
u_t = u_xx + a ∂x(u v_x) + f(u),
μ v - v_xx = u,
u_x = v_x = 0 at x=0,1.
```

For a logistic source, keep the hypotheses abstract but usable:

```text
f is C¹ on [0,M],
f(0) ≥ 0,
f(s) ≤ r s - b s^{1+α}     or at least gives a scalar ODE upper bound,
f'(s) ≤ L_f on [0,M].
```

The exact constants do not matter. The proof only needs an absorbing `L∞` bound `M` and a finite slope bound `L_f` on `[0,M]`.

## Step 1: maximum-principle `L∞` bound

Assume temporarily that the solution is smooth and nonnegative; for a mild solution, prove this first for Galerkin/classical approximants or for positive times and pass to the limit.

Let `m(t)=max_x u(t,x)`. At a maximum point `x_t`,

```text
u_x(t,x_t)=0,
u_xx(t,x_t)≤0.
```

The elliptic maximum principle for

```text
μ v - v_xx = u,   v_x=0 at the boundary
```

gives

```text
0 ≤ μ v ≤ ||u||∞.
```

Thus, at the maximum point where `u=m(t)`,

```text
v_xx = μv-u ≤ m(t)-m(t)=0.
```

Since

```text
∂x(u v_x)=u_x v_x + u v_xx,
```

we get at the maximum

```text
a ∂x(u v_x) = a u v_xx ≤ 0.
```

Therefore

```text
m'(t) ≤ f(m(t)).
```

For the usual logistic `f(s)=r s-b s^{1+α}`, this gives

```text
sup_{t≥0} ||u(t)||∞ ≤ M := max(||u₀||∞, (r/b)^{1/α}).
```

This is the core repulsive-sign estimate. It avoids Moser iteration entirely.

## Step 2: elliptic resolver bounds from `0≤u≤M`

From `μv-v_xx=u` and Neumann boundary conditions:

```text
0 ≤ μv ≤ M,
||v||∞ ≤ M/μ,
||v_xx||∞ = ||μv-u||∞ ≤ 2M.
```

In one dimension, the Green kernel or direct ODE representation gives a uniform bound

```text
||v_x||∞ ≤ C_μ M.
```

The precise value is unimportant. Formalize it as a resolver lemma:

```lean
resolver_Linf_bounds :
  0 ≤ u → (∀ x, u x ≤ M) →
    ||v||∞ ≤ C₀ M ∧ ||v_x||∞ ≤ C₁ M ∧ ||v_xx||∞ ≤ C₂ M.
```

For the energy proof below, `v_x` in `L∞` and `v_xx` in `L∞` or `L²` are enough.

## Step 3: L² energy gives a sliding-window bound for `||u_x||²`

Multiply the PDE by `u` and integrate over `[0,1]`. Neumann boundary terms vanish:

```text
1/2 d/dt ||u||₂²
  = -||u_x||₂² - a ∫ u u_x v_x + ∫ u f(u).
```

Integrate the chemotaxis term once:

```text
-a ∫ u u_x v_x
  = -(a/2) ∫ (u²)_x v_x
  =  (a/2) ∫ u² v_xx.
```

Using `0≤u≤M`, `||v_xx||∞≤C(M)`, and boundedness of `u f(u)` on `[0,M]`, obtain

```text
1/2 d/dt ||u||₂² + ||u_x||₂² ≤ C_L2.
```

Since `||u(t)||₂²≤M²` on the unit interval, integration over `[t,t+1]` gives

```text
∫_t^{t+1} ||u_x(s)||₂² ds ≤ C_win
```

for every `t≥0`, with `C_win` depending on `M`, `χ₀`, `μ`, and the logistic constants, but not on `t`.

This sliding-window integral is the missing ingredient that prevents the H¹ estimate from becoming an exponentially growing Gronwall bound.

## Step 4: H¹ differential inequality

Let

```text
y(t) := ||u_x(t)||₂².
```

Differentiate the equation by testing against `-u_xx`:

```text
1/2 y'(t)
  = -||u_xx||₂²
    - a ∫ u_xx ∂x(u v_x)
    - ∫ u_xx f(u).
```

Expand

```text
∂x(u v_x)=u_x v_x + u v_xx.
```

For the chemotaxis term, use Young:

```text
|a ∫ u_xx (u_x v_x + u v_xx)|
  ≤ ε ||u_xx||₂²
    + C_ε a² ( ||v_x||∞² ||u_x||₂² + ||u||∞² ||v_xx||₂² ).
```

The resolver and `L∞` bounds make

```text
||v_x||∞ ≤ C(M),
||u||∞ ≤ M,
||v_xx||₂ ≤ C(M),
```

so

```text
|a ∫ u_xx ∂x(u v_x)|
  ≤ ε ||u_xx||₂² + C₁ y(t) + C₂.
```

For the reaction term, integrate by parts:

```text
-∫ u_xx f(u) = ∫ f'(u) u_x² ≤ L_f y(t),
```

where `L_f := sup_{0≤s≤M} f'(s)`.

Taking, say, `ε=1/2`, dropping the remaining nonnegative `||u_xx||₂²` term, and doubling constants gives

```text
y'(t) ≤ A y(t) + B.        (H1-diff)
```

Here `A,B` are uniform in time.

Important: this inequality alone would only give an exponential-in-time estimate. The uniform bound comes from combining it with the sliding-window integral from the L² energy estimate.

## Step 5: uniform Gronwall on sliding windows

Use the elementary uniform Gronwall lemma:

If

```text
y' ≤ A y + B,
∫_t^{t+1} y(s) ds ≤ C_win  for all t≥0,
```

then for all `t≥0`,

```text
y(t+1) ≤ e^A C_win + e^A B.
```

Proof: for any `s∈[t,t+1]`, integrate `(H1-diff)` from `s` to `t+1`:

```text
y(t+1) ≤ e^{A(t+1-s)} y(s)
         + B ∫_s^{t+1} e^{A(t+1-r)} dr
       ≤ e^A y(s) + e^A B.
```

Average this inequality over `s∈[t,t+1]` and use the window bound.

Together with the local bound on `[0,1]`, this yields

```text
sup_{t≥0} ||u_x(t)||₂² < ∞.
```

Since `||u(t)||₂≤M` on the unit interval, we obtain

```text
sup_{t≥0} ||u(t)||_{H¹} < ∞.
```

This is the shortest rigorous arbitrary-data H¹ route I would formalize. It is not Moser iteration. It is two energy estimates plus a one-page uniform Gronwall lemma.

## Is a single H¹ energy identity enough?

Almost, but not quite by itself.

The H¹ identity gives

```text
y' ≤ A y + B.
```

That is not a uniform-in-time bound unless either:

1. `A<0`, which would require an absorption/spectral-gap condition not generally available for arbitrary coefficients; or
2. one combines it with a sliding-window integral bound for `y`.

The L² energy identity supplies exactly that window bound. So the minimal robust package is:

```text
L² energy window + H¹ differential inequality + uniform Gronwall.
```

This is still much lighter than Moser iteration and much lighter than the coordinatewise σ-ladder.

## Mild solutions and regularity justification

If the local solution is only mild in `H^σ`, prove the energy estimates by one of these standard formal routes:

1. prove them first for Galerkin/cosine truncations and pass to the limit;
2. use parabolic smoothing to show the mild solution is classical for every `t>0`, prove estimates on `[ε,T]`, then let `ε↓0` using lower semicontinuity and local boundedness;
3. define the local Picard solution in a regular enough space from the start, if the existing local theory permits it.

For Lean, Galerkin/cosine truncations may be the cleanest if the spectral infrastructure already exists. The estimates above are finite-dimensional identities before passage to the limit.

## Coordinatewise envelope: never needed for uniform H¹ boundedness

A coordinatewise envelope is not a standard continuation criterion and is not needed for the final mathematical statement

```text
sup_t ||u(t)||_{H¹} < ∞.
```

It is an artifact of the current ladder design.

Moreover, the implication

```text
sup_t ||u(t)||_{H¹} < ∞
  ⇒ ∃g∈H¹, ∀k, sup_t |u_k(t)|≤g_k
```

is false in general. A path can stay in a bounded `H¹` ball while visiting different high modes at different times. The pointwise-in-mode supremum can then fail to be square-summable with the `H¹` weights.

So do not try to prove the coordinatewise envelope from the norm bound by abstract Hilbert-space reasoning. It requires extra structure from the equation, typically the mild formula plus a uniform source estimate.

## Optional one-shot coordinatewise envelope after the H¹ proof

If some existing API still demands a `TrajectoryHSigmaEnvelope 1`, derive it after the norm/source estimates, not before.

From the PDE and the uniform `H¹` bound, in one dimension:

```text
u ∈ H¹ ⇒ u ∈ L∞,
v=(μ-Δ)^{-1}u gives v_x, v_xx controlled,
N(u):=a ∂x(u v_x)+f(u)
```

is uniformly controlled in a space strong enough to estimate Fourier coefficients. The cleanest coefficient argument is through the mild formula:

```text
u_k(t)=e^{-λ_k t}u_{0,k}
       + ∫_0^t e^{-λ_k(t-s)} N_k(s) ds,
λ_k=(kπ)².
```

If

```text
sup_s ||N(s)||_{L²} ≤ A,
```

then for `k≥1`,

```text
|N_k(s)| ≤ A,
```

and hence

```text
sup_t |∫_0^t e^{-λ_k(t-s)} N_k(s) ds|
  ≤ A ∫_0^∞ e^{-λ_k r} dr
  = A/λ_k.
```

Define

```text
g_k := |u_{0,k}| + A/λ_k,     k≥1,
```

and handle `k=0` by the mass/logistic bound. Then

```text
∑_{k≥1} (1+λ_k) g_k² < ∞
```

because `u₀∈H¹` for the heat part, and

```text
∑_{k≥1} (1+λ_k) / λ_k² < ∞
```

in one dimension.

If `u₀` is only in `H^σ` with `σ<1`, then this one-shot argument gives a coordinatewise `H^σ` envelope immediately, and an `H¹` envelope only after positive-time smoothing or with stronger source estimates / initial regularity. For the final uniform `H¹` norm theorem, none of this is necessary.

## Minimal Lean target list

To minimize remaining work, introduce or prove these lemmas instead of the σ-ladder seams:

```lean
-- 1. comparison / maximum principle
repulsive_logistic_Linf_bound :
  Nonnegative u₀ → ... → ∃ M, ∀ t x, 0 ≤ u t x ∧ u t x ≤ M

-- 2. elliptic resolver bounds
neumann_resolvent_bounds_Linf :
  0 ≤ u → (∀ x, u x ≤ M) →
    bounds_on v v_x v_xx

-- 3. L² energy window
chemotaxis_L2_energy_window :
  LinfBound M u → ResolverBounds M v →
    ∃ Cwin, ∀ t, ∫ s in t..t+1, ||u_x s||₂² ≤ Cwin

-- 4. H¹ differential inequality
chemotaxis_H1_diff_ineq :
  LinfBound M u → ResolverBounds M v →
    ∃ A B, ∀ t, deriv (fun t => ||u_x t||₂²) t ≤ A*||u_x t||₂² + B

-- 5. uniform Gronwall
uniform_gronwall_window :
  y' ≤ A*y+B → (∀t, ∫_{t}^{t+1} y≤Cwin) → ∀t≥1, y t ≤ C

-- 6. final theorem
uniform_H1_bound :
  ∃ C, ∀ t, ||u t||_{H¹} ≤ C
```

Only after this, optionally:

```lean
coordinate_envelope_from_mild_and_source_bound :
  mild_coeff_formula → sup_t ||N(t)||₂≤A → ∃g∈H¹, ∀k, sup_t |u_k(t)|≤g_k
```

This optional lemma replaces the whole finite σ-ladder if the final API still wants a coordinatewise object.

## Final build-vs-rebuild answer

**Rebuild the main a-priori proof.** The shortest rigorous path is not the coordinatewise ladder. It is:

```text
repulsive maximum principle for L∞
+ L² energy window
+ H¹ differential inequality
+ uniform Gronwall.
```

This should be less total Lean work than discharging the coordinatewise base envelope and over-quantified `CarrySeam` family. The coordinatewise envelope is not needed for uniform `H¹` boundedness; it should be removed from the main theorem path and, if still required by downstream code, recovered afterwards from the mild coefficient formula and a uniform source bound.
