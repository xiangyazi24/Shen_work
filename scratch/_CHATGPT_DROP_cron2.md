# Q78 (cron2): χ₀<0 chemotaxis uniform-H¹ proof — completeness audit

## Verdict

Modulo the three remaining carries you listed, the norm/energy route is **mathematically complete** for a uniform-in-time `H¹` bound, provided the constants in the carries are genuinely local/classical-regularity constants and not secretly using the target `H¹` bound.

The built chain

```text
L∞ order box
→ elliptic resolver C²/sup bounds
→ spectral H¹ energy identity
→ y' ≤ A y + B
→ L² dissipation window ∫_{t-1}^t y ≤ Cwin
→ uniform Gronwall / averaging
→ sup_t y(t) ≤ C
```

is the right structure. There is no missing Moser step and no hidden exponential-in-time growth once the sliding-window integral is available. The taxis term is not sign-definite in the `H¹` energy, but it does not need to be: with the `L∞` box and resolver bounds it is handled by Young and contributes only to the linear coefficient `A` and constant `B` in `y'≤Ay+B`.

The only real audit warnings are:

1. the source regularity seam must not smuggle in a uniform `H¹` bound;
2. the L² window constant must be independent of the final time `T`;
3. the uniform-Gronwall lemma needs absolute continuity/differentiability of `y` on intervals, which your spectral derivative/source seam appears designed to supply;
4. the full `H¹` norm needs the zero mode / `L²` part, not just the derivative seminorm, but the `L∞` box supplies it immediately on `[0,1]`.

## 1. Audit of the logic

Let

```text
y(t) := 1/2 ∑_k λ_k |û_k(t)|² = 1/2 ||u_x(t)||²_{L²}.
```

You have built the spectral energy derivative and the estimate

```text
y'(t) ≤ A y(t) + B                                      (1)
```

with constants `A,B` depending only on the fixed problem parameters, the `L∞` order-box bound, the resolver constants, and the logistic coefficients on that box. This is fine even if `A>0`; the point is that you also have the window estimate.

You also have

```text
∀ t ≥ 1,  ∫_{t-1}^{t} y(s) ds ≤ Cwin.                  (2)
```

Then the averaging/uniform-Gronwall step is valid. For `t≥1`, integrate (1) from any `s∈[t-1,t]` to `t`:

```text
y(t) ≤ e^{A(t-s)} y(s) + ∫_s^t e^{A(t-r)} B dr.
```

If `A≥0`, then `t-s≤1`, hence

```text
y(t) ≤ e^A y(s) + B e^A.
```

Averaging over `s∈[t-1,t]` gives

```text
y(t) ≤ e^A ∫_{t-1}^{t} y(s) ds + B e^A
     ≤ e^A Cwin + B e^A.                              (3)
```

If you want a sharper constant, replace `B e^A` with `B (e^A-1)/A` when `A>0`, and with `B` when `A=0`. The coarse bound above is enough.

For `t∈[0,1]`, use the local/classical bound or integrate (1) from `0`:

```text
y(t) ≤ e^A y(0) + B e^A.
```

Therefore

```text
sup_{t∈[0,T]} y(t)
  ≤ max(e^A y(0)+B e^A, e^A Cwin+B e^A),
```

and this bound is independent of `T`. This is a genuine uniform bound, not an exponential-in-`T` estimate.

So the uniform-Gronwall/averaging logic is sound.

## 2. Is there a hidden sign issue in the taxis term?

At the `L∞` maximum-principle level, the repulsive sign `χ₀<0` gives an inward-pointing contribution at the spatial maximum. That is the crucial sign use for the order box.

At the `H¹` level, you should **not** expect the taxis term to be dissipative pointwise. The proof only needs it to be controlled. With `a=-χ₀>0`,

```text
u_t = u_xx + a ∂x(u v_x) + f(u).
```

Testing against `-u_xx` gives schematically

```text
1/2 d/dt ||u_x||²₂
  = -||u_xx||²₂
    - a ∫ u_xx ∂x(u v_x)
    - ∫ u_xx f(u).
```

Expand

```text
∂x(u v_x) = u_x v_x + u v_xx.
```

Then Young gives, for any small `ε>0`,

```text
|a ∫ u_xx (u_x v_x + u v_xx)|
  ≤ ε ||u_xx||²₂
    + Cε a² ( ||v_x||²∞ ||u_x||²₂ + ||u||²∞ ||v_xx||²₂ ).
```

The `L∞` order box and elliptic resolver bounds give

```text
||u||∞ ≤ M,
||v_x||∞ ≤ Cv1(M),
||v_xx||₂ ≤ Cv2(M),
```

so the taxis term contributes

```text
≤ ε ||u_xx||²₂ + C1 y(t) + C2.
```

For the reaction,

```text
-∫ u_xx f(u) = ∫ f'(u) u_x² ≤ Lf y(t),
```

where

```text
Lf := sup_{0≤s≤M} f'(s) < ∞.
```

Choose `ε` small enough to leave part of the `-||u_xx||²₂` dissipation, then drop the remaining negative term. This yields exactly

```text
y' ≤ A y + B.
```

Thus there is no hidden sign issue: the repulsive sign is used to obtain the `L∞` box, not to make the `H¹` taxis contribution negative.

## 3. Audit of the L² dissipation window

The window estimate must be genuinely uniform. The standard route is to test the equation against `u`:

```text
1/2 d/dt ||u||²₂
  = -||u_x||²₂ - a ∫ u u_x v_x + ∫ u f(u).
```

Integrating the taxis term by parts,

```text
-a ∫ u u_x v_x
  = -(a/2) ∫ (u²)_x v_x
  =  (a/2) ∫ u² v_xx.
```

This term may have either sign, but the `L∞` box and resolver bound give

```text
|(a/2) ∫ u² v_xx| ≤ C(M).
```

The reaction term is also bounded on the order box:

```text
|∫ u f(u)| ≤ C_f(M).
```

Therefore

```text
1/2 d/dt ||u||²₂ + ||u_x||²₂ ≤ C0.                  (4)
```

Since `[0,1]` has finite measure and `0≤u≤M`,

```text
||u(t)||²₂ ≤ M².
```

Integrating (4) over `[t-1,t]` yields

```text
∫_{t-1}^{t} ||u_x(s)||²₂ ds
  ≤ 1/2 ||u(t-1)||²₂ - 1/2 ||u(t)||²₂ + C0
  ≤ 1/2 M² + C0.
```

Since `y=1/2||u_x||²₂`, this gives

```text
∫_{t-1}^{t} y(s) ds ≤ Cwin
```

with `Cwin` independent of `t` and independent of the final lifespan `T`.

This is the key estimate that makes the H¹ differential inequality uniform.

## 4. H¹ seminorm versus full H¹ norm

The spectral energy `y` controls only the Neumann `H¹` seminorm:

```text
y(t)=1/2 ||u_x(t)||²₂.
```

It does **not** control the zero mode by Poincaré, because Neumann boundary conditions allow constants. So, by itself, `y` is not the full `H¹` norm.

But the `L∞` order box gives the missing piece immediately:

```text
||u(t)||²₂ ≤ |[0,1]| ||u(t)||²∞ ≤ M².
```

Thus

```text
||u(t)||²_{H¹}
  = ||u(t)||²₂ + ||u_x(t)||²₂
  ≤ M² + 2 sup_t y(t).
```

So yes: the H¹ seminorm bound plus the already-built `L∞` box gives uniform full `H¹` boundedness. In the final theorem, explicitly combine the two facts rather than claiming the seminorm alone is the `H¹` norm.

## 5. Reaction/logistic subtlety

The logistic term cannot break the proof as long as the order box is truly established.

For the maximum principle, the logistic source must provide a scalar upper ODE bound, for example

```text
f(s) ≤ r s - b s^{1+α}
```

or more generally a dissipative one-sided bound producing `u≤M`.

For the H¹ energy inequality, you do **not** need the reaction to be dissipative at derivative level. You only need

```text
Lf := sup_{0≤s≤M} f'(s) < ∞,
Cf := sup_{0≤s≤M} |s f(s)| < ∞.
```

Both are automatic for the usual polynomial/logistic source once `0≤u≤M`. The contribution

```text
∫ f'(u) u_x²
```

is then bounded by `Lf ||u_x||²₂`, which is absorbed into the `A y` term. It may increase `A`; the uniform-window Gronwall handles that. Therefore the reaction term does not cause non-uniformity after the order box is known.

## 6. Remaining carries (a)--(c): are they honest?

### (a) Divergence-weighted source regularity

This is honest if it is used only to justify:

```text
termwise spectral differentiation,
time-C¹ of the coefficient source,
weighted summability needed for the derivative of the tsum,
integration-by-parts / coefficient identities.
```

It becomes suspicious only if the assumptions include something essentially equivalent to

```text
sup_t ∑ λ_k |û_k(t)|² < ∞
```

or a uniform-in-time source bound that can only be proved from the target H¹ estimate. Then the seam would be circular.

Audit it syntactically: it should talk about regularity of the classical solution/source on compact time intervals or smooth approximants, not about a global uniform `H¹` bound. If the constants in the source regularity seam are allowed to depend on `T`, that is fine for justifying identities on `[0,T]`; the **estimate constants** `A,B,Cwin` must not depend on those regularity constants.

### (b) Initial-datum coefficient bound

This is honest and necessary for the short-time part `[0,1]` and for `y(0)<∞`. It should be exactly the assumption that the initial datum belongs to `H¹` if the final statement starts at `t=0` with a finite `H¹` bound.

If the initial datum is only `L∞` or `H^σ` with `σ<1`, then a uniform `H¹` bound on `[0,∞)` including `t=0` is false as stated. You can still get

```text
sup_{t≥τ} ||u(t)||_{H¹} < ∞    for every τ>0
```

by parabolic smoothing, but not a bound including `t=0` unless `u₀∈H¹`. So make sure the theorem statement and the initial coefficient bound agree.

### (c) `IsPaper2ClassicalSolution`

This is a standard regularity wrapper. If its constructor from the chemotaxis source data is present, then it is legitimate to keep it as the remaining classicality seam. It should supply enough regularity to interpret the PDE pointwise / spectrally and to validate the energy identities.

Again, the classicality seam may depend on local existence and smoothness, but the final uniform bound constants must depend only on the order box, resolver constants, equation parameters, and initial `H¹` size, not on a hidden classical norm over `[0,T]`.

## 7. Possible hidden gaps checklist

The proof is complete if all of the following are true:

```text
[ ] The L∞ box is uniform in T and includes nonnegativity 0≤u≤M.
[ ] μ>0 for the Neumann resolver, so the zero mode of v is controlled.
[ ] Resolver bounds for v_x and v_xx are uniform from 0≤u≤M.
[ ] The spectral derivative identity is justified by source regularity without assuming the target H¹ bound.
[ ] The constants A,B in y'≤Ay+B depend only on M, χ₀, μ, f, and fixed domain constants.
[ ] The L² window ∫_{t-1}^t y≤Cwin is proved with Cwin independent of t and T.
[ ] Uniform Gronwall is applied to a nonnegative absolutely continuous y.
[ ] The interval [0,1] is handled separately by y(0) or a local bound.
[ ] The full H¹ norm combines y with the L∞→L² bound.
```

If these boxes are checked, there is no hidden analytic gap in the uniform-H¹ argument.

## Final answer to the three questions

1. **Yes**, the χ₀<0 uniform-H¹ bound is complete modulo (a)--(c), provided those carries are regularity/classicality inputs and not hidden a-priori H¹ bounds. The averaging argument is valid and gives a constant independent of `T` because it combines `y'≤Ay+B` with a uniform sliding-window integral of `y`.

2. The H¹ seminorm bound is not by itself the full H¹ bound under Neumann boundary conditions. But the already-built `L∞` box gives a uniform `L²` bound, hence full `H¹` boundedness follows immediately:

   ```text
   ||u||²_{H¹} ≤ M² + 2y.
   ```

3. There is no additional standard χ₀<0/logistic subtlety that destroys uniform boundedness in 1D. The logistic term must produce the order box and have bounded derivative on that box. Once `0≤u≤M`, its H¹ contribution is only `≤ Lf ||u_x||²`, which the uniform-window Gronwall handles. The taxis term may not have a good sign in H¹, but Young plus resolver bounds is enough.

Bottom line: the energy/norm route has now reached the right mathematical endpoint. The remaining work is regularity/classicality plumbing, not another missing a-priori estimate.
