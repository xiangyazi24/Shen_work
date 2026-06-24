# ChatGPT git-drop (cron1)

## Q88 — χ₀<0 interval chemotaxis: constant L∞ supersolution

### Executive verdict

For the repulsive sign as stated,

```text
u_t = u_xx + a ∂x(u v_x) + u(1-u),
a := -χ₀ > 0,
μ v - v_xx = u,
```

the constant upper bound

```text
M := max(1, ‖u₀‖∞)
```

**does close uniformly in time**. No window-uniform `H^σ` flux envelope is needed.

The crucial point is to rewrite the actual equation as a local semilinear drift-reaction equation with the actual resolver `v` frozen as a coefficient:

```text
u_t = u_xx + a v_x u_x + u(1 + a μ v) - (a+1)u².
```

Then, on any strip where `0 ≤ u ≤ M`, the resolver maximum principle gives

```text
0 ≤ v ≤ M/μ,
```

hence

```text
M[(a+1)M - 1 - a μ v] ≥ M[(a+1)M - 1 - aM] = M(M-1) ≥ 0.
```

So `M` is a constant supersolution of the **rewritten local semilinear equation**. The nonlocality is closed by the same `M`-ball through `v ≤ M/μ`.

Do **not** test the constant `M` in the frozen divergence expression `a M v_xx + M(1-M)` with `v_xx = μv - u_actual`; that is the wrong comparison operator and can give a false obstruction. The comparison operator should be the local semilinear equation actually satisfied by `u`, with reaction

```text
R_v(q) := q(1 + a μ v) - (a+1)q².
```

At `q=u`, this is exactly the original equation. At `q=M`, it exposes the stabilizing `-(a+1)M²` term.

---

## 1. Expansion and exact drift-reaction form

Start from

```text
u_t = u_xx + a ∂x(u v_x) + u(1-u).
```

Expand:

```text
∂x(u v_x) = u_x v_x + u v_xx.
```

Use the elliptic equation

```text
μv - v_xx = u,
```

so

```text
v_xx = μv - u.
```

Then

```text
a ∂x(u v_x)
  = a u_x v_x + a u(μv-u)
  = a v_x u_x + a μ u v - a u².
```

Adding the logistic term gives

```text
u(1-u) = u - u².
```

Therefore

```text
u_t
  = u_xx + a v_x u_x + a μu v - a u² + u - u²
  = u_xx + a v_x u_x + u(1+a μv) - (a+1)u².
```

So the local drift and reaction are:

```text
B(t,x) := a v_x(t,x),
R_v(t,x,q) := q(1+a μ v(t,x)) - (a+1)q².
```

Equivalently,

```text
u_t = u_xx + B u_x + R_v(t,x,u).
```

The stabilizing quadratic coefficient is exactly

```text
-(a+1)u².
```

It consists of:

```text
-a u²      from a u v_xx = a u(μv-u),
-u²        from logistic u(1-u).
```

This is the sign that closes the bound.

---

## 2. Constant supersolution condition

For a constant candidate `Mbar`, the drift and diffusion terms vanish:

```text
(Mbar)_t = 0,
(Mbar)_x = 0,
(Mbar)_xx = 0.
```

For the rewritten semilinear equation, the supersolution residual is

```text
Res(Mbar)
  := (Mbar)_t - (Mbar)_xx - B(Mbar)_x - R_v(t,x,Mbar)
  = - R_v(t,x,Mbar)
  = Mbar[(a+1)Mbar - 1 - a μ v(t,x)].
```

Thus the exact condition is

```text
(a+1)Mbar ≥ 1 + a μ sup_{strip} v.
```

Equivalently,

```text
Mbar ≥ (1 + a μ sup v)/(a+1).
```

This is the inequality to use if `sup v` is known independently.

But in the bootstrap/comparison argument, `sup v` is controlled by the same `Mbar`-ball. If

```text
0 ≤ u ≤ Mbar
```

on the strip, then the Neumann resolver positivity/maximum principle gives

```text
0 ≤ v ≤ Mbar/μ.
```

Indeed, at a maximum point of `v`, the Neumann endpoint argument included,

```text
v_xx ≤ 0,
μv = u + v_xx ≤ Mbar.
```

At a minimum,

```text
v ≥ 0
```

by the already-landed resolver positivity for `u ≥ 0`.

Therefore

```text
μ v ≤ Mbar,
```

and hence

```text
Res(Mbar)
  ≥ Mbar[(a+1)Mbar - 1 - aMbar]
  = Mbar(Mbar - 1).
```

So every

```text
Mbar ≥ 1
```

is a supersolution once the same strip has `u≤Mbar`. Taking

```text
M := max(1, ‖u₀‖∞)
```

is sufficient.

### Important correction about the “raw divergence residual”

You wrote that at constant `Mbar` the residual looks like

```text
-[a Mbar v_xx + Mbar(1-Mbar)]
```

with

```text
v_xx = μv - u.
```

That expression corresponds to testing `q=Mbar` in the operator

```text
q ↦ q_xx + a ∂x(q v_x) + q(1-q)
```

while keeping `v` tied to the **actual** `u`. This is not the right local comparison operator.

For comparison, freeze the coefficient `v` and rewrite the actual PDE as

```text
q_t = q_xx + a v_x q_x + q(1+a μv) - (a+1)q².
```

The actual solution `u` satisfies this equation exactly. The constant `Mbar` is tested in this rewritten equation, not in the raw frozen-divergence expression. That is what recovers the `-(a+1)Mbar²` term.

If one insists on the raw frozen-divergence residual, one obtains a condition involving `μv-u_actual`, and it need not close. That is an artifact of choosing the wrong comparison formulation.

---

## 3. Bounded drift needed by the comparison lemma

Your comparison lemma requires bounded drift

```text
B = a v_x.
```

Under the same `M`-ball,

```text
0 ≤ u ≤ M,
0 ≤ v ≤ M/μ.
```

Then

```text
v_xx = μv - u,
```

with both `μv` and `u` in `[0,M]`, so

```text
|v_xx| ≤ M.
```

Using Neumann boundary condition `v_x(0)=0`, for `x∈[0,1]`,

```text
|v_x(x)| = |∫_0^x v_xx(y)dy|
         ≤ ∫_0^1 |v_xx(y)|dy
         ≤ M.
```

Thus

```text
‖v_x‖∞ ≤ M,
‖B‖∞ ≤ aM.
```

If you do not want to use nonnegativity, the cruder sign-free estimates are

```text
|v| ≤ M/μ,
|v_xx| ≤ 2M,
|v_x| ≤ 2M,
|B| ≤ 2aM.
```

But with `u ≥ 0`, the sharper `M` bound is available.

The reaction

```text
R_v(q) = q(1+a μv) - (a+1)q²
```

is locally Lipschitz in `q` on any bounded interval. On `q ∈ [0,M]`, one may take for example

```text
Lip_R ≤ 1 + aM + 2(a+1)M,
```

because `μv≤M`.

For the divided-difference linearization used by a linear comparison lemma, define

```text
C_M(t,x)
  := if u(t,x) = M then
       ∂_q R_v(t,x,M)
     else
       (R_v(t,x,u(t,x)) - R_v(t,x,M)) / (u(t,x)-M).
```

Algebraically, since `R_v(q)` is quadratic,

```text
R_v(u) - R_v(M)
  = [(1+a μv) - (a+1)(u+M)] (u-M).
```

So no actual `if` is needed:

```text
C_M(t,x) = (1+a μv(t,x)) - (a+1)(u(t,x)+M).
```

Then for `z := u-M`,

```text
z_t
  = z_xx + B z_x + C_M z + R_v(M).
```

Since `R_v(M) ≤ 0`, one has

```text
z_t ≤ z_xx + B z_x + C_M z.
```

With `z(0)≤0` and Neumann boundary condition for `z`, the linear comparison principle gives `z≤0`.

This is the clean bridge from a semilinear supersolution to your linear drift-reaction comparison lemma.

For nonnegativity, use `0` as a subsolution. Since

```text
R_v(0)=0,
```

and the drift/diffusion terms vanish on `0`, comparison gives

```text
u ≥ 0
```

from `u₀≥0`.

---

## 4. Uniform-in-time closure

The constant

```text
M = max(1, ‖u₀‖∞)
```

is independent of `T`. To prove the bound on any finite strip `[0,T]`, use a continuation/first-crossing argument.

### Option A: first-crossing proof

Let

```text
U(t) := sup_{x∈[0,1]} u(t,x).
```

Assume there is a first time `t*` when `U(t*) = M` and the solution attempts to cross above `M`. At a maximum point `x*`,

```text
u_x(t*,x*) = 0,
u_xx(t*,x*) ≤ 0.
```

Since before `t*` we have `u≤M`, the resolver bound gives

```text
μv(t*,x*) ≤ M.
```

Using the rewritten equation at the maximum:

```text
u_t
  = u_xx + a v_x u_x + u(1+a μv) - (a+1)u²
  ≤ M(1+aM) - (a+1)M²
  = M(1-M)
  ≤ 0.
```

So the solution cannot cross upward through `M`.

This is conceptually shortest, but in Lean it may require a fair amount of topology for the maximum point and first crossing.

### Option B: comparison + epsilon bootstrap

This is often more Lean-friendly with an existing comparison lemma.

For `ε>0`, set

```text
Mε := M + ε.
```

Then `Mε > 1` unless `M=1, ε>0`, in any case `Mε>1`.

Define

```lean
def Good (τ : ℝ) : Prop :=
  ∀ s ∈ Set.Icc (0:ℝ) τ, ∀ x ∈ Set.Icc (0:ℝ) 1,
    0 ≤ u s x ∧ u s x ≤ Mε
```

or use your interval-domain lifted formulation.

On any interval satisfying `Good τ`, the resolver bounds give

```text
0 ≤ v ≤ Mε/μ,
|v_x| ≤ Mε.
```

Then `B=a v_x` is bounded, the reaction is Lipschitz on `[0,Mε]`, and `Mε` is a **strict** supersolution:

```text
Res(Mε)
  ≥ Mε(Mε-1) > 0
```

if `Mε>1`; if `M=1`, this is positive for every `ε>0`.

Use the landed comparison lemma on the strip to prove the solution cannot exceed `Mε`. The usual open/closed continuation then yields

```text
u ≤ Mε
```

on `[0,T]`. Letting `ε ↓ 0` gives

```text
u ≤ M.
```

This version avoids relying on a strict margin at `M` when `M=1`.

In Lean, rather than literally taking a limit in `ε`, prove:

```lean
∀ ε > 0, u t x ≤ M + ε
```

then conclude `u t x ≤ M` by `le_of_forall_pos_le_add`, or the corresponding existing lemma.

---

## 5. Lean-formalizable lemma chain

Here is the clean theorem factoring.

### 5.1 Algebraic rewrite

```lean
theorem chiNeg_rewrite_drift_reaction
    (a μ : ℝ) {u v : ℝ → ℝ}
    (hres : ∀ x, μ * v x - deriv (deriv v) x = u x) :
    (fun x => deriv (deriv u) x
      + a * deriv (fun y => u y * deriv v y) x
      + u x * (1 - u x))
    =
    (fun x => deriv (deriv u) x
      + a * deriv v x * deriv u x
      + u x * (1 + a * μ * v x)
      - (a+1) * (u x)^2) := by
  -- product rule + hres + ring
```

Depending on your notation, this may be per `(t,x)` rather than a function equality.

### 5.2 Resolver order-box bounds

```lean
theorem resolver_bounds_of_orderBox
    (hμ : 0 < μ)
    (hu : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ u x ∧ u x ≤ M)
    (hres : ∀ x ∈ Set.Icc (0:ℝ) 1, μ * v x - deriv (deriv v) x = u x)
    (hNeu : deriv v 0 = 0 ∧ deriv v 1 = 0) :
    (∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ v x ∧ v x ≤ M / μ) ∧
    (∀ x ∈ Set.Icc (0:ℝ) 1, |deriv (deriv v) x| ≤ M) ∧
    (∀ x ∈ Set.Icc (0:ℝ) 1, |deriv v x| ≤ M)
```

The first part is the Neumann maximum principle / resolver positivity. The second follows from `v_xx=μv-u`. The third follows by integrating `v_xx` from the endpoint where `v_x=0`.

If the repo already has landed resolver `L∞/C²` bounds, use those and only prove the implication `u≤M ⇒ μv≤M` if not already exposed.

### 5.3 Constant supersolution residual

```lean
def Rv (a μ : ℝ) (v : ℝ) (q : ℝ) : ℝ :=
  q * (1 + a * μ * v) - (a + 1) * q^2

theorem const_super_residual_nonneg
    (ha : 0 ≤ a) (hM1 : 1 ≤ M) (hM0 : 0 ≤ M)
    (hvM : μ * v ≤ M) :
    0 ≤ M * ((a+1) * M - 1 - a * μ * v) := by
  -- nlinarith
```

This is the exact residual statement:

```text
0 ≤ M[(a+1)M - 1 - aμv].
```

### 5.4 Difference linearization for the comparison lemma

```lean
theorem reaction_diff_factor
    (a μ v u M : ℝ) :
    Rv a μ v u - Rv a μ v M
      = ((1 + a * μ * v) - (a+1) * (u + M)) * (u - M) := by
  ring
```

Then for `z = u-M`, derive:

```text
z_t ≤ z_xx + B z_x + C z
```

with

```lean
def B (t x) := a * deriv (v t) x

def C (t x) :=
  (1 + a * μ * v t x) - (a+1) * (u t x + M)
```

provided the constant residual is nonnegative.

This is the point where your `NeumannLinearDriftComparisonRegular` can be applied.

### 5.5 Uniform upper bound theorem

```lean
theorem chiNeg_uniform_Linf_upper
    (ha : 0 < a) (hμ : 0 < μ)
    (hu0_nonneg : ∀ x, 0 ≤ u0 x)
    (hu0_bound : ∀ x, u0 x ≤ M)
    (hM : M = max 1 (sSup/Norm of u0))
    (hsolution : classical/mild regular solution on [0,T]) :
    ∀ t ∈ Set.Icc (0:ℝ) T, ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 ≤ u t x ∧ u t x ≤ M
```

Prove first with `Mε = M + ε`, then send `ε→0` if the comparison continuation needs strictness.

### 5.6 Uniform in `T`

State the finite-horizon theorem with a constant that does not mention `T` except in the quantifier. Then expose a global corollary:

```lean
theorem chiNeg_uniform_Linf_upper_global
    (hsol_global : solution on all finite strips) :
    ∀ t ≥ 0, ∀ x, u t x ≤ M
```

by applying the finite-horizon theorem with `T = max 1 t` or `T=t+1`.

---

## 6. Answer to the three precise questions

### Q1

The drift is

```text
B = a v_x.
```

The reaction is

```text
R_v(u) = u(1+a μv) - (a+1)u².
```

The coefficient of `u²` is exactly

```text
-(a+1),
```

with `-a u²` from the repulsive chemotaxis term and `-u²` from logistic damping.

### Q2

The exact supersolution inequality for a constant `Mbar` is

```text
Mbar[(a+1)Mbar - 1 - a μv(t,x)] ≥ 0
```

for all `(t,x)` on the strip.

Equivalently,

```text
Mbar ≥ (1 + a μ sup v)/(a+1).
```

Under the bootstrap/order-box assumption `0≤u≤Mbar`, the resolver gives `μv≤Mbar`, hence the residual is at least

```text
Mbar(Mbar-1).
```

Thus `Mbar = max(1, ‖u₀‖∞)` closes. The nonlocality does not force dependence on anything else; it is closed by the resolver maximum principle inside the same `Mbar`-ball.

### Q3

Since the constant supersolution does close, no alternative Hσ/window-flux estimate is needed for the L∞ bound. The minimal a-priori chain is:

```text
u≤M on strip
  ⇒ resolver maximum principle: 0≤v≤M/μ
  ⇒ drift bound: |a v_x|≤aM
  ⇒ constant M supersolution residual ≥ M(M-1)
  ⇒ comparison principle preserves u≤M
  ⇒ continuation/epsilon bootstrap gives u≤M on every finite strip
  ⇒ finite-strip theorem with M independent of T gives global uniform-in-time L∞ bound.
```

This is entirely `L∞`/maximum-principle level. It avoids any window-uniform `H^σ` flux envelope.

---

## Final Lean guidance

The main formal pitfall is choosing the wrong comparison operator. Do not apply the constant supersolution test to

```text
q ↦ q_xx + a ∂x(q v_x) + q(1-q)
```

with `v` still tied to the actual `u`. Instead first rewrite the actual equation as

```text
u_t = u_xx + a v_x u_x + R_v(u),
R_v(q)=q(1+a μv)-(a+1)q².
```

Then use the constant supersolution for this local semilinear drift-reaction equation. If the landed comparison lemma is linear, feed it the difference equation for `z=u-M` with coefficient

```text
C_M = (1+a μv) - (a+1)(u+M),
```

and use the nonpositive residual `R_v(M)≤0`.

That is the clean formal path.
