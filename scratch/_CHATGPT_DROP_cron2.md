# Q69 (cron2): χ₀<0 chemotaxis boundedness strategy and coordinatewise envelopes

## Executive answer

For the repulsive sign `χ₀ < 0` on `[0,1]` with Neumann boundary conditions, the clean route is **not** to build a uniform-in-time coordinatewise Sobolev envelope as the fundamental a-priori estimate. The standard PDE route is:

1. prove nonnegativity and a **uniform `L∞` bound** by a maximum-principle/comparison argument, using the good sign of chemotaxis and the logistic damping;
2. bootstrap regularity from that boundedness by either a Sobolev energy estimate or a sliding-window Duhamel/analytic-semigroup estimate;
3. if the formalization still needs a coordinatewise envelope, derive it afterwards as a post-processing lemma from a uniform Sobolev/source norm bound.

For formalization in Lean, the most tractable hybrid is:

```text
maximum principle / scalar logistic ODE for L∞
  → elliptic resolver bounds for v=(μ-Δ)^{-1}u
  → sliding-window Duhamel or H¹ energy for Sobolev regularity
  → optional per-mode envelope lemma.
```

Trying to prove a fixed `Estar` coordinatewise box by local Duhamel margins alone is only sound if `Estar` is already backed by a genuine invariant/a-priori estimate. Otherwise the quadratic taxis term makes the box argument a disguised small-data or finite-time continuation argument, not a global arbitrary-data bound.

## References / standard techniques

The standard chemotaxis boundedness literature for attractive/logistic systems usually proceeds through `L^p` energy estimates and Moser-Alikakos iteration. Tao--Winkler's Keller--Segel boundedness paper explicitly describes the use of a modified Moser-Alikakos iteration for uniform-in-time boundedness:

- Y. Tao and M. Winkler, *Boundedness in a quasilinear parabolic-parabolic Keller-Segel system with subcritical sensitivity*, arXiv:1106.5345, https://arxiv.org/abs/1106.5345.
- N. D. Alikakos, *L^p bounds of solutions of reaction-diffusion equations*, Comm. PDE 4 (1979), 827--868.

For logistic Keller--Segel boundedness and explicit dependence on chemotaxis/logistic coefficients, see for example:

- H.-Y. Jin and T. Xiang, *Chemotaxis effect vs logistic damping on boundedness in the 2-D minimal Keller-Segel model*, arXiv:1804.02501, https://arxiv.org/abs/1804.02501.

For the formal Duhamel/semigroup side, the relevant standard reference is the variation-of-constants formula for analytic semigroups:

- A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*, Springer, 1983.
- D. Henry, *Geometric Theory of Semilinear Parabolic Equations*, Springer, 1981.

For maximum principles/comparison:

- M. Protter and H. Weinberger, *Maximum Principles in Differential Equations*, Springer, 1984.
- L. C. Evans, *Partial Differential Equations*, AMS, especially the parabolic maximum principle sections.

The point for this project is that the attractive/logistic literature often needs Moser iteration, but the **repulsive sign** on a one-dimensional bounded interval gives a simpler first bound by comparison.

## 1. Canonical a-priori technique for `χ₀ < 0`

Write `a := -χ₀ > 0`. Then

```text
u_t = u_xx + a ∂x(u v_x) + logistic(u),
μ v - v_xx = u,
∂x u = ∂x v = 0 at x=0,1.
```

Let `M(t)=max_x u(t,x)` for a smooth positive solution. The elliptic maximum principle gives

```text
0 ≤ μ v(x) ≤ M(t).
```

At a point `x_t` where `u(t,·)` attains its maximum, `u_x=0`, `u_xx≤0`, and

```text
∂x(u v_x) = u_x v_x + u v_xx = u(μv-u).
```

Since `u(x_t)=M(t)` and `μv(x_t)≤M(t)`, the repulsive chemotaxis term satisfies

```text
a u(x_t)(μv(x_t)-u(x_t)) ≤ 0.
```

Thus the taxis term does **not** increase the spatial maximum. If the logistic term is, say,

```text
f(u)=r u - b u^{1+α},   b>0, α>0,
```

then formally

```text
M'(t) ≤ r M(t) - b M(t)^{1+α}.
```

The scalar logistic ODE gives

```text
sup_{t≥0} ||u(t)||_{L∞}
  ≤ max( ||u₀||_{L∞}, (r/b)^{1/α} )
```

with the obvious modifications for the exact logistic source. This is the clean base estimate for `χ₀<0`.

After that, the standard bootstrap is either:

### Option A: energy route

Differentiate or test against `-u_xx` to estimate `||u_x||₂²`. The `L∞` bound on `u`, elliptic bounds for `v`, and Young inequalities absorb the highest derivative terms. This is PDE-standard but comparatively heavy in Lean because it requires integration by parts, Sobolev product estimates, elliptic regularity, and a Gronwall lemma.

### Option B: semigroup / Duhamel route

Use the Neumann heat semigroup and write

```text
u(t) = e^{(t-t₀)Δ}u(t₀)
       + ∫_{t₀}^{t} e^{(t-s)Δ} N(u(s)) ds,

N(u)=a ∂x(u v_x)+f(u).
```

For `t≥1`, take `t₀=t-1`. If the previous bounds give `N(u(s))` uniformly in a Sobolev space `H^r`, analytic semigroup estimates give uniform bounds for `u(t)` in higher Sobolev spaces. This is often cleaner to formalize if the project already has cosine-mode heat estimates.

My recommendation for Lean is therefore:

```text
maximum-principle L∞ bound first;
then sliding-window Duhamel estimates in Sobolev/cosine coordinates;
avoid a global coordinatewise box unless it is only a derived lemma.
```

## 2. Is the coordinatewise envelope genuinely needed?

No, not for the PDE. Standard continuation/global-existence criteria consume a **norm bound**, usually something like

```text
sup_{t<Tmax} ||u(t)||_{L∞} < ∞
```

or, for a semilinear Sobolev local theory,

```text
sup_{t<Tmax} ||u(t)||_{H^σ} < ∞.
```

A coordinatewise envelope

```text
∃ g ∈ H^σ,  ∀k, sup_{τ∈[0,T]} |u_k(τ)| ≤ g_k
```

is strictly stronger than

```text
sup_{τ∈[0,T]} ||u(τ)||_{H^σ} < ∞.
```

Indeed, a path can stay in the unit ball of `H^σ` while visiting, at different times, modes whose coefficients are comparable to `(1+λ_k)^{-σ/2}`. Then the coordinatewise supremum has weighted square sum comparable to `∑_k 1`, which diverges. Thus a uniform `H^σ` norm bound does **not** imply an `H^σ` coordinatewise envelope. At best it gives a coordinatewise envelope in lower Sobolev order, with a loss.

The standard ladder should therefore be norm-based:

```text
L∞ bound
  → elliptic resolver bounds for v
  → bound N(u) in an appropriate Sobolev space
  → Duhamel smoothing gives H^σ/H¹
  → continuation criterion closes global existence.
```

If your local theory is in `H^σ`, the continuation theorem should require only

```text
sup_{t<Tmax} ||u(t)||_{H^σ} < ∞,
```

not a per-coordinate `sup_t` majorant.

## 3. Is the box-extension continuation sound?

It is sound only under a strong invariant-box hypothesis.

A statement of the form

```text
envelope holds on [0,r]
  ⇒ envelope holds on [0,r+δ]
```

with a fixed margin can prove a finite- or infinite-time bound only if:

1. the same `δ` can be chosen uniformly while the solution remains in the box;
2. the nonlinear estimates are genuinely inward pointing at the boundary of the box;
3. the constants defining the box do not grow with the number of restarts;
4. the zero mode/mass is controlled separately.

For arbitrary large data, a purely local Duhamel margin usually does **not** supply this. The quadratic chemotaxis term produces estimates of the form

```text
||N(u)|| ≤ C(1 + ||u||^2)
```

in natural Sobolev spaces. A small time step can keep a local box invariant, but iterating such a local argument without a dissipative estimate either gives constants that depend on `T`, or requires small data, or hides the needed global a-priori estimate in the choice of `Estar`.

For `χ₀<0`, the well-known cleaner alternative is the maximum-principle/logistic `L∞` bound above. That bound is genuinely global and arbitrary-data. Once it is proved, the Duhamel bootstrap can be done on sliding windows of fixed length, with constants depending on the global `L∞` bound rather than on elapsed time.

So:

```text
box-extension alone: not the right global arbitrary-data proof;
box-extension after maximum-principle/energy bound: sound but mostly bookkeeping;
maximum-principle + Duhamel: cleaner.
```

## 4. Can one get the coordinatewise envelope directly from Duhamel?

Yes, but only as a **post-processing lemma** after obtaining a uniform source bound. Duhamel smoothing does not replace the global estimate that bounds the nonlinearity.

Let `e_k(x)=cos(kπx)` and `λ_k=(kπ)^2`, with `λ_0=0`. Suppose the mild equation is

```text
u_k(t)=e^{-λ_k t} u_{0,k}
       + ∫_0^t e^{-λ_k(t-s)} N_k(s) ds.
```

Assume, for some `A`,

```text
sup_{s∈[0,T]} ||N(s)||_{H^{σ-1}} ≤ A.
```

Then for `k≥1`,

```text
|N_k(s)| ≤ A (1+λ_k)^(-(σ-1)/2),
```

and therefore

```text
sup_{t∈[0,T]} |∫_0^t e^{-λ_k(t-s)} N_k(s) ds|
  ≤ A (1+λ_k)^(-(σ-1)/2) ∫_0^∞ e^{-λ_k r} dr
  ≤ C A (1+λ_k)^(-(σ+1)/2).
```

Hence one may define

```text
g_k = |u_{0,k}| + C A (1+λ_k)^(-(σ+1)/2),  k≥1,
```

and handle `k=0` separately by the mass/logistic estimate. In one space dimension,

```text
∑_{k≥1} (1+λ_k)^σ (1+λ_k)^(-σ-1)
  = ∑_{k≥1} (1+λ_k)^(-1) < ∞,
```

because `λ_k≈k²`. Thus `g∈H^σ`.

This is exactly the slick per-mode envelope lemma one can formalize with cosine estimates. But the key assumption is the uniform source bound

```text
sup_s ||N(s)||_{H^{σ-1}} ≤ A.
```

That assumption itself normally comes from the global `L∞`/energy bootstrap. If one tries to prove it from the same coordinatewise envelope, the argument becomes circular unless the box has already been shown invariant by a dissipative estimate.

## Recommended formalization plan

1. **Nonnegativity and mass/zero-mode control.** Prove by comparison/integration of the equation.

2. **Elliptic resolver maximum principle.** For `v=(μ-Δ)^{-1}u`, prove

   ```text
   0≤u≤M ⇒ 0≤μv≤M,
   ||v_x||∞ and ||v_xx||∞ controlled by M.
   ```

3. **Repulsive maximum-principle `L∞` bound.** At a spatial maximum of `u`, the taxis term is nonpositive; logistic damping gives a scalar ODE bound.

4. **Uniform Sobolev bootstrap.** Choose either:

   - H¹ energy estimate, if integration-by-parts/Gronwall infrastructure is acceptable; or
   - sliding-window Duhamel, if cosine semigroup estimates are already available.

5. **Optional coordinatewise envelope.** Once `sup_s ||N(s)||_{H^{σ-1}}≤A` is known, use the per-mode Duhamel estimate above to build `g∈H^σ`.

## Final verdict

The uniform coordinatewise `H^σ` envelope is a formal artifact, not a canonical PDE requirement. The canonical arbitrary-data global bound for the repulsive/logistic one-dimensional problem should start from the maximum-principle/logistic `L∞` estimate, not from a coordinatewise box. Duhamel/cosine estimates are excellent for the regularity bootstrap and for deriving a coordinatewise envelope after the fact, but they do not by themselves replace the dissipative a-priori estimate needed to control the quadratic chemotaxis nonlinearity uniformly in time.
