# ChatGPT git-drop (cron1)

## Q74 — χ₀<0 interval chemotaxis: Lean-ready H¹ energy route

### Executive verdict

The H¹ route is viable in 1D and needs no Moser/Alikakos iteration. The correct structure is:

```text
uniform L∞ order box
  → 1D elliptic resolver bounds for v, v_x, v_xx
  → H¹ energy differential inequality
  → sliding-window ∫‖u_x‖² bound from landed L² energy
  → uniform Gronwall / averaging lemma
  → uniform-in-time H¹ bound.
```

Important correction: the inequality

```text
y'(t) ≤ A y(t) + B,   y(t)=1/2 ‖u_x(t)‖²₂
```

alone gives only an exponential-in-`T` bound. A genuinely uniform-in-time H¹ bound comes from combining it with a **uniform sliding-window bound**

```text
∀ t ≥ 0,  ∫_t^{t+R} y(s) ds ≤ C_R
```

coming from the L²/dissipation energy estimate. The logistic damping is used at the L∞/L² level to produce uniform bounds and sliding-window dissipation; the H¹ differential inequality itself need not have a negative coefficient in front of `y`.

---

## 0. Sign convention

Below I write the PDE in the sign convention matching the identity you requested:

```text
u_t = u_xx - a ∂x(u v_x) + f(u),     a := -χ₀ > 0,
μ v - v_xx = u,
v_x(0)=v_x(1)=0,
u_x(0)=u_x(1)=0.
```

Then

```text
y' = -‖u_xx‖²₂ + a ∫ u_xx ∂x(u v_x) - ∫ u_xx f(u).
```

After integrating the reaction term by parts,

```text
- ∫ u_xx f(u) = ∫ f'(u) u_x².
```

If your file’s PDE uses the opposite convention

```text
u_t = u_xx + a ∂x(u v_x) + f(u),
```

then the taxis term below changes sign. All estimates are unchanged after taking absolute values.

---

## 1. H¹ energy identity

Let

```text
y(t) := 1/2 ∫_0^1 u_x(t,x)^2 dx.
```

Assume temporarily enough classical regularity to justify the calculation, e.g. `u(t,·) ∈ C²`, `u_t` continuous, and Neumann boundary condition `u_x(t,0)=u_x(t,1)=0`. Then

```text
y'(t)
  = ∫_0^1 u_x u_xt
  = [u_x u_t]_{0}^{1} - ∫_0^1 u_xx u_t
  = - ∫_0^1 u_xx u_t.
```

Using

```text
u_t = u_xx - a ∂x(u v_x) + f(u),
```

we get the exact identity

```text
y'
  = - ∫ u_xx²
    + a ∫ u_xx ∂x(u v_x)
    - ∫ u_xx f(u).
```

Since

```text
∂x(u v_x) = u_x v_x + u v_xx,
```

this is

```text
y'
  = - ‖u_xx‖²₂
    + a ∫ u_xx u_x v_x
    + a ∫ u_xx u v_xx
    - ∫ u_xx f(u).
```

For the reaction term, integration by parts gives

```text
- ∫_0^1 u_xx f(u)
  = - [u_x f(u)]_0^1 + ∫_0^1 f'(u) u_x²
  = ∫_0^1 f'(u) u_x²,
```

again because `u_x=0` at the endpoints. Thus the clean identity is

```text
y'
  = - ‖u_xx‖²₂
    + a ∫ u_xx u_x v_x
    + a ∫ u_xx u v_xx
    + ∫ f'(u) u_x².
```

This is the exact identity I would formalize.

### Bounds for the taxis terms

Assume the landed order box gives

```text
0 ≤ u(t,x) ≤ M
```

or at least `|u| ≤ M`, and resolver bounds give

```text
‖v_x‖∞ ≤ V₁,
‖v_xx‖∞ ≤ V₂.
```

Let

```text
X := ‖u_xx‖₂,
Z := ‖u_x‖₂ = sqrt(2y).
```

Then

```text
|a ∫ u_xx u_x v_x|
  ≤ a ‖v_x‖∞ ‖u_xx‖₂ ‖u_x‖₂
  ≤ a V₁ X Z,
```

and, since the interval has length `1`,

```text
|a ∫ u_xx u v_xx|
  ≤ a ‖u‖∞ ‖v_xx‖∞ ‖u_xx‖₂ ‖1‖₂
  ≤ a M V₂ X.
```

Using Young’s inequality in the form

```text
p q ≤ ε p² + q² / (4ε),      ε > 0,
```

with `ε₁ = ε₂ = 1/4`,

```text
a V₁ X Z ≤ (1/4) X² + a² V₁² Z²
         = (1/4) X² + 2 a² V₁² y,
```

and

```text
a M V₂ X ≤ (1/4) X² + a² M² V₂².
```

For the logistic/reaction term, define

```text
L₊ := max 0 (sup_{0≤z≤M} f'(z)).
```

Then

```text
∫ f'(u) u_x² ≤ L₊ ‖u_x‖²₂ = 2 L₊ y.
```

Therefore

```text
y'
  ≤ - (1/2) ‖u_xx‖²₂
     + (2 a² V₁² + 2 L₊) y
     + a² M² V₂².
```

In particular, dropping the negative term,

```text
y' ≤ A y + B,
```

with

```text
A := 2 a² V₁² + 2 L₊,
B := a² M² V₂².
```

More generally, with arbitrary `ε₁, ε₂ > 0`, `ε₁+ε₂<1`, the sharper bookkeeping is

```text
y'
  ≤ - (1 - ε₁ - ε₂) ‖u_xx‖²₂
     + (a² V₁² / (2 ε₁) + 2 L₊) y
     + a² M² V₂² / (4 ε₂).
```

This general form is better if you want to preserve a larger fraction of the `‖u_xx‖²` dissipation.

### Logistic specialization

For the usual logistic source

```text
f(u) = u (α₀ - b u^p)
```

with `b ≥ 0`, `p ≥ 0`,

```text
f'(u) = α₀ - b (p+1) u^p ≤ α₀.
```

So one may take

```text
L₊ := max 0 α₀
```

or just `L₊ := α₀` if `α₀ ≥ 0` is a parameter hypothesis.

If your paper permits a sublinear power with singular derivative at zero, e.g. `p < 1` and no positive lower bound for `u`, then the literal `f'(u)` identity is not Lean-clean without extra work. In that case use the already-landed Lipschitz-on-order-box reaction estimate when available, or assume a positive lower bound `δ ≤ u` to make `f'` bounded. For the standard `C¹` logistic regime this issue does not appear.

---

## 2. Resolver bounds needed

The H¹ estimate above needs only

```text
V₁ ≥ ‖v_x‖∞,
V₂ ≥ ‖v_xx‖∞.
```

These follow in 1D from the Neumann elliptic problem and the `L∞` order box.

Assume

```text
μ v - v_xx = u,
v_x(0)=v_x(1)=0,
0 ≤ u ≤ M,
μ > 0.
```

### Bound for `v`

By the Neumann maximum principle,

```text
0 ≤ v ≤ M / μ.
```

Indeed, at a maximum point of `v`, including endpoints via the Neumann endpoint argument, `v_xx ≤ 0`, so

```text
μ v = u + v_xx ≤ M.
```

At a minimum, `μ v = u + v_xx ≥ 0` in the corresponding maximum-principle form, giving `v ≥ 0` when `u ≥ 0`.

### Bound for `v_xx`

From the equation,

```text
v_xx = μ v - u.
```

Hence

```text
‖v_xx‖∞ ≤ μ ‖v‖∞ + ‖u‖∞ ≤ M + M = 2M.
```

So one can take

```text
V₂ := 2M.
```

If you use a sharper Green-kernel bound for `‖v‖∞`, replace `2M` by the corresponding constant.

### Bound for `v_x`

Using `v_x(0)=0`,

```text
|v_x(x)| = |∫_0^x v_xx(s) ds| ≤ ∫_0^1 |v_xx(s)| ds ≤ ‖v_xx‖∞.
```

Since the interval length is `1`,

```text
‖v_x‖∞ ≤ ‖v_xx‖∞ ≤ 2M.
```

So a simple concrete choice is

```text
V₁ := 2M,
V₂ := 2M.
```

Then

```text
A = 2 a² (2M)² + 2L₊ = 8a² M² + 2L₊,
B = a² M² (2M)² = 4a² M⁴.
```

These constants are crude but Lean-friendly.

If the repo already has quantitative resolver constants, prefer using those. The landed file `IntervalDomainL2UEnergyUniform.lean` defines explicit resolver-gradient constants such as `FgQuant`, `CgradQuant`, and `CvalQuant`, and the header records that the uniform L² machinery is built on τ-independent resolver sup bounds. In particular, it exposes `FgQuant` as a τ-independent gradient sup constant and `CfluxQuant` as a τ-independent flux constant built from resolver controls. That file’s header says the uniform inequality uses a single constant depending only on the order-box parameters, not on time.

---

## 3. Closing the uniform-in-time H¹ bound

### 3.1 What Gronwall alone gives

From

```text
y' ≤ A y + B,
```

standard Gronwall gives, on `[0,T]`,

```text
y(t) ≤ y(0) e^{At} + (B/A)(e^{At}-1)
```

if `A>0`, and

```text
y(t) ≤ y(0) + Bt
```

if `A=0`.

This is only local/exponential in final time. It is **not** a uniform-in-time estimate unless `A≤0` or another dissipative input is used.

### 3.2 Where uniformity really comes from

The uniform route needs the negative diffusion term and the landed L² energy machinery.

Keep the stronger inequality

```text
y' + c ‖u_xx‖²₂ ≤ A y + B,
```

with, for example,

```text
c = 1/2,
A = 2a²V₁² + 2L₊,
B = a²M²V₂².
```

For the final uniform H¹ bound, it is enough to know a sliding-window dissipation estimate:

```text
∀ t ≥ 0,
  ∫_t^{t+R} y(s) ds ≤ C_R.
```

Usually take `R=1`. This comes from the L² energy inequality plus the uniform `L∞` order box. A typical L² energy estimate gives

```text
E₂'(t) + c₀ ‖u_x(t)‖²₂ ≤ C₀,
```

with `E₂(t)=1/2‖u(t)‖²₂`, and `E₂(t)` uniformly bounded by the order box. Integrating over `[t,t+R]` gives

```text
∫_t^{t+R} ‖u_x(s)‖²₂ ds
  ≤ (E₂(t) - E₂(t+R) + C₀ R) / c₀
  ≤ C_R.
```

Since `y = 1/2 ‖u_x‖²₂`, this gives the needed bound on `∫ y`.

This is exactly the role of the landed L² half-energy machinery. In the repo, `IntervalDomainL2UEnergyUniform.lean` records a τ-independent energy differential inequality with a single Grönwall constant depending on the order-box parameters; the header names `intervalDomainL2U_energy_diffIneq_bound_uniform` and its explicit variant as the uniform-in-time L² energy input.

### 3.3 Uniform Gronwall / averaging lemma

A very Lean-friendly uniform lemma is the following elementary one. Suppose `y ≥ 0`, absolutely continuous, and for all `s ∈ [t,t+R]`,

```text
y'(s) ≤ A y(s) + B,
```

and

```text
∫_t^{t+R} y(s) ds ≤ C_R.
```

Then

```text
y(t+R) ≤ (1/R + A) C_R + B R.
```

Proof: for any `s ∈ [t,t+R]`, integrate the differential inequality from `s` to `t+R`:

```text
y(t+R) - y(s)
  ≤ ∫_s^{t+R} (A y(ξ) + B) dξ
  ≤ A ∫_t^{t+R} y(ξ)dξ + B R.
```

Thus

```text
y(t+R) ≤ y(s) + A C_R + B R.
```

Average this inequality in `s` over `[t,t+R]`:

```text
R y(t+R) ≤ ∫_t^{t+R} y(s) ds + R(A C_R + B R),
```

so

```text
y(t+R) ≤ C_R/R + A C_R + B R.
```

For `R=1`,

```text
y(t+1) ≤ (1+A) C_1 + B.
```

This is often easier to formalize than the textbook uniform Gronwall lemma because it avoids exponentials.

For the initial interval `[0,1]`, use ordinary Gronwall from `y(0)`:

```text
y(t) ≤ gronwallBound y(0) A B t,       0 ≤ t ≤ 1.
```

For `t ≥ 1`, apply the averaging lemma with the window `[t-1,t]`:

```text
y(t) ≤ (1+A) C_1 + B.
```

Therefore a global uniform bound is

```text
sup_{t ≥ 0} y(t)
  ≤ max (sup_{0≤s≤1} gronwallBound y(0) A B s)
        ((1+A) C_1 + B).
```

Using monotonicity of `gronwallBound` for `A,B,y(0) ≥ 0`, this can be simplified to

```text
Y_H1 := max (gronwallBound y(0) A B 1) ((1+A) C_1 + B).
```

Then

```text
‖u_x(t)‖²₂ = 2y(t) ≤ 2 Y_H1
```

uniformly in final time.

### 3.4 Does logistic damping make `A ≤ 0`?

Not in the crude H¹ inequality above. The reaction term gives

```text
∫ f'(u) u_x²,
```

and for logistic `f'(u) = α₀ - b(p+1)u^p`, the upper bound is still `≤ α₀`, which is generally positive. The taxis estimates also contribute a positive coefficient to `y`.

So do **not** claim the H¹ differential inequality is uniformly dissipative by itself. The uniformity comes from:

1. global/order-box `L∞` control,
2. L² energy producing a sliding-window `∫ y`,
3. the H¹ differential inequality and the uniform Gronwall/averaging lemma.

This is still a uniform-in-time H¹ bound, but the damping enters indirectly via the lower-level a-priori estimates.

---

## 4. Minimal Mathlib / Lean path

### 4.1 Energy time derivative

For the derivative of

```lean
fun t => (1/2 : ℝ) * ∫ x in (0:ℝ)..1, (ux t x)^2
```

there are two possible routes.

#### Route A: avoid differentiating under the spatial integral directly

This is often cleaner. Establish a lemma for smooth/classical solutions as a packaged identity:

```lean
theorem H1_energy_identity_of_classical
  (hu_reg : ...)
  (hPDE : ∀ t x, u_t t x = u_xx t x - a * deriv (fun x => u t x * v_x t x) x + f (u t x))
  (hNeu : ∀ t, deriv (u t) 0 = 0 ∧ deriv (u t) 1 = 0) :
  HasDerivAt
    (fun t => (1/2) * ∫ x in (0:ℝ)..1, (u_x t x)^2)
    (- ∫ x in (0:ℝ)..1, (u_xx t x)^2
      + a * ∫ x in (0:ℝ)..1, u_xx t x * deriv (fun x => u t x * v_x t x) x
      - ∫ x in (0:ℝ)..1, u_xx t x * f (u t x))
    t
```

Then prove it once using the parametric integral tools.

Relevant Mathlib file/lemmas:

```lean
Mathlib.Analysis.Calculus.ParametricIntervalIntegral
intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_lip
```

These are the interval-integral versions of differentiating under the integral sign.

The pointwise derivative of `(u_x)^2` is handled by:

```lean
HasDerivAt.mul
HasDerivAt.pow
```

and algebra/simp.

#### Route B: work with an already-landed weak energy identity

If the repo already has a classical/weak energy identity framework, reuse it. For formal progress, it may be better to state the H¹ identity as an intermediate theorem requiring a `ClassicalH1EnergySolution` structure with all regularity, boundary, and integration-by-parts fields, then later instantiate it from the classical bootstrap.

### 4.2 Integration by parts

Use interval integration by parts from:

```lean
Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
```

Relevant lemmas include:

```lean
intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
intervalIntegral.integral_mul_deriv_eq_deriv_mul
intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt
```

The basic identity needed repeatedly is:

```text
∫_0^1 φ * ψ' = φ(1)ψ(1) - φ(0)ψ(0) - ∫_0^1 φ' * ψ.
```

For

```text
∫ u_x u_xt = -∫ u_xx u_t,
```

use `φ = u_x`, `ψ = u_t` in the form `∫ φ * ψ'` or equivalently apply the derivative-of-product identity to `u_x * u_t`, depending on how `u_xt` is represented.

Boundary terms vanish by rewriting with:

```lean
hNeu0 : u_x t 0 = 0
hNeu1 : u_x t 1 = 0
```

For the reaction term,

```text
-∫ u_xx f(u) = ∫ f'(u) u_x²,
```

use integration by parts with

```text
φ = f(u),     ψ' = u_xx,
```

or `φ = u_x`, `ψ = f(u)` depending on the exact representation. The chain rule is:

```lean
HasDerivAt.comp
```

for

```text
deriv (fun x => f (u x)) = f'(u x) * u_x x.
```

### 4.3 Young/Cauchy estimates

For the inequalities, use elementary real arithmetic rather than searching for a named Young lemma.

Core facts:

```lean
sq_nonneg (p - q)
abs_mul
norm_mul
intervalIntegral.integral_mono_on
norm_integral_le_integral_norm
```

The algebraic Young inequality can be proved once as a local lemma:

```lean
lemma mul_le_eps_sq_add_sq_div {p q eps : ℝ} (heps : 0 < eps) :
  p * q ≤ eps * p^2 + q^2 / (4 * eps) := by
  nlinarith [sq_nonneg (2 * eps * p - q)]
```

Usually it is cleaner to state it for nonnegative `p`, `q`, but the square proof works generally after appropriate rearrangement and `eps > 0`.

For Cauchy-Schwarz on interval integrals, if not already in the repo, it may be easier to use the standard L² inequality already available in your energy files, or prove the specialized forms:

```text
|∫ f g| ≤ (∫ f²)^{1/2} (∫ g²)^{1/2}.
```

But in the estimates above we mostly use sup bounds:

```text
|∫ u_xx u_x v_x|
  ≤ ‖v_x‖∞ ∫ |u_xx| |u_x|
  ≤ ‖v_x‖∞ ‖u_xx‖₂ ‖u_x‖₂.
```

If Cauchy-Schwarz in interval form is cumbersome, a repo-local lemma for `∫ |f*g|` is worth adding once.

### 4.4 Resolver estimates

Formalize as simple interval lemmas:

```lean
theorem resolver_v_sup_le
  (hμ : 0 < μ) (hu : ∀ x ∈ Icc 0 1, 0 ≤ u x ∧ u x ≤ M)
  (hv_eq : ∀ x, μ * v x - deriv (deriv v) x = u x)
  (hNeu : deriv v 0 = 0 ∧ deriv v 1 = 0) :
  ∀ x ∈ Icc 0 1, 0 ≤ v x ∧ v x ≤ M / μ
```

This is the maximum principle already landed in spirit.

Then:

```lean
theorem resolver_vxx_sup_le_twoM
  ... : ∀ x ∈ Icc 0 1, |deriv (deriv v) x| ≤ 2*M
```

from

```lean
deriv (deriv v) x = μ * v x - u x.
```

Finally:

```lean
theorem resolver_vx_sup_le_twoM
  ... : ∀ x ∈ Icc 0 1, |deriv v x| ≤ 2*M
```

using

```text
v_x(x) = v_x(0) + ∫_0^x v_xx = ∫_0^x v_xx
```

and `v_x(0)=0`.

In Lean, this last step uses FTC / interval integral:

```lean
intervalIntegral.integral_eq_sub_of_hasDerivAt
```

or an existing derivative-integral theorem from `FundThmCalculus`.

If the repo’s spectral resolver bounds are easier to use, substitute them directly:

```lean
V₁ := FgQuant p M
V₂ := some landed C²/vxx sup constant
```

The H¹ inequality only needs the abstract assumptions `‖v_x‖∞≤V₁`, `‖v_xx‖∞≤V₂`.

### 4.5 Gronwall

Mathlib has:

```lean
Mathlib.Analysis.ODE.Gronwall
```

with:

```lean
gronwallBound
norm_le_gronwallBound_of_norm_deriv_right_le
le_gronwallBound_of_liminf_deriv_right_le
```

The theorem `norm_le_gronwallBound_of_norm_deriv_right_le` bounds `‖f x‖` when there is a right-derivative bound

```lean
‖f' x‖ ≤ K * ‖f x‖ + ε.
```

For scalar nonnegative `y`, the lemma

```lean
le_gronwallBound_of_liminf_deriv_right_le
```

is closer, but it is often simpler to prove a scalar corollary once:

```lean
theorem scalar_gronwall_of_hasDerivWithinAt
  (hy_cont : ContinuousOn y (Icc a b))
  (hy_deriv : ∀ t ∈ Ico a b, HasDerivWithinAt y (yp t) (Ici t) t)
  (hy0 : y a ≤ δ)
  (hineq : ∀ t ∈ Ico a b, yp t ≤ A * y t + B) :
  ∀ t ∈ Icc a b, y t ≤ gronwallBound δ A B (t-a)
```

by applying Mathlib’s `le_gronwallBound_of_liminf_deriv_right_le`.

For the uniform sliding-window step, Mathlib probably does not have exactly the PDE-style uniform Gronwall lemma. Add a small local theorem:

```lean
theorem uniform_bound_of_deriv_le_and_integral_window
    {y yp : ℝ → ℝ} {A B R C t : ℝ}
    (hR : 0 < R) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hy_ac : enough absolute-continuity / FTC on [t,t+R])
    (hderiv : ∀ s ∈ Icc t (t+R), HasDerivAt y (yp s) s)
    (hineq : ∀ s ∈ Icc t (t+R), yp s ≤ A * y s + B)
    (hwin : ∫ s in t..t+R, y s ≤ C) :
    y (t+R) ≤ C/R + A*C + B*R
```

The proof is just the averaging argument above. If the derivative/FTC formalization is heavy, use an integral form as input instead:

```lean
hinc : ∀ s ∈ Icc t (t+R),
  y (t+R) ≤ y s + A * (∫ ξ in t..t+R, y ξ) + B * R
```

Then the averaging lemma is elementary interval-integral algebra.

This is the most Lean-friendly route.

---

## 5. Suggested theorem factoring

I would split the formalization into four independent lemmas.

### Lemma 1: abstract H¹ identity

```lean
theorem h1_energy_identity
  (regularity_and_boundary_hypotheses)
  (pde_identity) :
  HasDerivAt y
    (- X2 t + a * taxis t + reactionH1 t)
    t
```

where

```lean
y t      = (1/2) * ∫ x in 0..1, (u_x t x)^2
X2 t     = ∫ x in 0..1, (u_xx t x)^2
taxis t  = ∫ x in 0..1, u_xx t x * deriv (fun x => u t x * v_x t x) x
reactionH1 t = ∫ x in 0..1, f' (u t x) * (u_x t x)^2
```

### Lemma 2: abstract H¹ differential inequality from sup bounds

```lean
theorem h1_diff_ineq_of_sup_bounds
  (huM : ∀ x, |u t x| ≤ M)
  (hvx : ∀ x, |v_x t x| ≤ V₁)
  (hvxx : ∀ x, |v_xx t x| ≤ V₂)
  (hf' : ∀ x, f' (u t x) ≤ L₊) :
  y' t ≤ A * y t + B
```

with

```lean
A = 2*a^2*V₁^2 + 2*L₊
B = a^2*M^2*V₂^2.
```

Or keep the stronger version with `- (1/2) ‖u_xx‖²`.

### Lemma 3: resolver bounds from `L∞`

```lean
theorem resolver_bounds_from_linf
  (hμ : 0 < μ)
  (hu : ∀ x ∈ Icc 0 1, 0 ≤ u x ∧ u x ≤ M)
  (hres : μ*v - v_xx = u)
  (hNeu : v_x 0 = 0 ∧ v_x 1 = 0) :
  (∀ x, |v_x x| ≤ 2*M) ∧ (∀ x, |v_xx x| ≤ 2*M)
```

### Lemma 4: uniform H¹ from differential inequality plus L² window

```lean
theorem uniform_H1_of_diffineq_and_window
  (hlocal : ∀ t ∈ Icc 0 1, y t ≤ gronwallBound (y 0) A B t)
  (hwin : ∀ t, 0 ≤ t → ∫ s in t..t+1, y s ≤ C₁)
  (hdiff : ∀ t, y' t ≤ A*y t + B) :
  ∀ t ≥ 0, y t ≤ max (gronwallBound (y 0) A B 1) ((1+A)*C₁ + B)
```

This last lemma is the final uniform-in-time step.

---

## Final answer

The H¹ route is clean and 1D-specific. The exact energy identity is

```text
y'
  = - ‖u_xx‖²₂
    + a ∫ u_xx u_x v_x
    + a ∫ u_xx u v_xx
    + ∫ f'(u) u_x².
```

With `0≤u≤M`, `‖v_x‖∞≤V₁`, `‖v_xx‖∞≤V₂`, and `f'(u)≤L₊`, it gives

```text
y' ≤ -1/2 ‖u_xx‖²₂ + (2a²V₁²+2L₊) y + a²M²V₂²,
```

hence in particular

```text
y' ≤ A y + B.
```

The resolver bounds can be taken crudely as

```text
‖v‖∞ ≤ M/μ,
‖v_xx‖∞ ≤ 2M,
‖v_x‖∞ ≤ 2M.
```

The final uniform-in-time H¹ bound is **not** from ordinary Gronwall alone. It is from ordinary Gronwall on the first unit interval plus a sliding-window uniform Gronwall/averaging lemma using the landed L² energy estimate

```text
∀t, ∫_t^{t+1} y(s) ds ≤ C₁.
```

Then for `t≥1`,

```text
y(t) ≤ (1+A)C₁ + B,
```

and globally

```text
y(t) ≤ max (gronwallBound (y 0) A B 1) ((1+A)C₁+B).
```

No Moser iteration is needed. The only serious formal obligations are the classical H¹ energy identity, the interval integration-by-parts bookkeeping, and the sliding-window extraction from the landed L² energy machinery.
