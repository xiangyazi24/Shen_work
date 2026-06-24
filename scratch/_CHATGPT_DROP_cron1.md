# ChatGPT git-drop (cron1)

## Q120 — Positive-time `u_t ∈ A³_cos` smoothing from the linearized Duhamel equation

### Executive verdict

Yes: once `u` is already available with a positive-time window-uniform `A³_cos` envelope, the same divergence-limited `+1` weighted-Wiener smoothing ladder applies to

```text
U := u_t.
```

The linearized equation is

```text
U_t = U_xx + a ∂x( U v_x D + u V_x D - β u v_x V D₁ ) + (1-2u)U,
```

where

```text
D  := (1+v)^(-β),
D₁ := (1+v)^(-β-1),
V  := (μ-Δ_N)^(-1)U,
V_x := ∂xV.
```

At weighted-Wiener level `A^r`, if

```text
u ∈ A³_cos   and   U ∈ A^r_cos,       0 ≤ r ≤ 3,
```

then the frozen-coefficient linearized flux

```text
Qlin_r(U) := U v_x D + u V_x D - β u v_x V D₁
```

lies in `A^r_sin`. The divergence Duhamel leg then gains one derivative:

```text
Qlin_r(U) ∈ A^r_sin
  ⇒ ∫ S(t-s) ∂x Qlin_r(U(s)) ds ∈ A^{r+1}_cos.
```

The reaction derivative term

```text
(1-2u)U
```

is non-divergence and gains two derivatives through the heat Duhamel operator, so it is never the limiting term.

Thus, from a positive-time `A⁰_cos` seed for `U`, the ladder is:

```text
U ∈ A⁰ → A¹ → A² → A³.
```

This is clean and Lean-formalizable. The only important technical caveat is the usual positive-time window buffer: to prove `U ∈ A^{r+1}` on `[t₀,T]`, use a Duhamel restart at some `τ₀<t₀` and assume/prove the `A^r` seed on `[τ₀,T]`. Do not try to get a closed-window smoothing gain at the restart time itself.

---

## 1. Exact linearized equation

Let the abstract PDE be

```text
u_t = Δ_N u + F(u),
F(u) = a ∂x q(u) + u(1-u),
q(u) = u v_x (1+v)^(-β),
v = R_μ u := (μ-Δ_N)^(-1)u.
```

Set

```text
U := u_t,
V := R_μ U,
D := (1+v)^(-β),
D₁ := (1+v)^(-β-1).
```

Because the resolver is linear and time-independent,

```text
v_t = R_μ u_t = V,
(v_x)_t = (v_t)_x = V_x.
```

Differentiate the pre-divergence flux:

```text
q(u) = u v_x D.
```

Then

```text
q_t
  = U v_x D
    + u V_x D
    + u v_x D_t.
```

Since

```text
D_t = -β(1+v)^(-β-1)V = -βD₁V,
```

we get

```text
q_t
  = U v_x D
    + u V_x D
    - β u v_x V D₁.
```

Therefore the linearized operator is

```text
F'(u)U
  = a ∂x( U v_x D + u V_x D - β u v_x V D₁ )
    + (1-2u)U.
```

So `U=u_t` satisfies the linearized PDE

```text
U_t
  = U_xx
    + a ∂x( U v_x D + u V_x D - β u v_x V D₁ )
    + (1-2u)U.
```

This is the exact formula to formalize.

---

## 2. Exact linearized mild/Duhamel equation

For any positive restart time `τ₀` at which `U(τ₀)` is defined in the desired coefficient sense, the mild equation for `U` is

```text
U(t)
  = S(t-τ₀) U(τ₀)
    + a ∫_{τ₀}^t S(t-s) ∂x( U(s) v_x(s) D(s)
        + u(s) V_x(s) D(s)
        - β u(s) v_x(s) V(s) D₁(s) ) ds
    + ∫_{τ₀}^t S(t-s) ((1-2u(s))U(s)) ds.
```

Here

```text
V(s) = R_μ U(s),
V_x(s) = ∂xV(s).
```

If the initial data is smooth enough to make

```text
U(0) = Δu₀ + F(u₀)
```

meaningful in the chosen Banach space and compatible with Neumann boundary conditions, then one can write the global-from-zero form:

```text
U(t)
  = S(t)(Δu₀+F(u₀))
    + ∫_0^t S(t-s) F'(u(s))U(s) ds.
```

But for rough `u₀` / positive-time smoothing, the restart form is the correct Lean target. It avoids placing `Δu₀+F(u₀)` in a high regularity space.

### Coefficient form

Let

```text
Qlin(s) := U(s) v_x(s) D(s)
          + u(s) V_x(s) D(s)
          - β u(s) v_x(s) V(s) D₁(s),
Rlin(s) := (1-2u(s))U(s).
```

Then for each cosine mode `k`, using the sine/cosine divergence identity,

```text
Û_k(t)
  = e^{-(t-τ₀)λ_k}Û_k(τ₀)
    + a ∫_{τ₀}^t e^{-(t-s)λ_k}
        [ ± sqrt(λ_k) sineCoeff(Qlin(s))_k ] ds
    + ∫_{τ₀}^t e^{-(t-s)λ_k}
        cosineCoeff(Rlin(s))_k ds.
```

The sign convention is irrelevant for envelope estimates.

---

## 3. Weighted-Wiener budget for the linearized source

Use

```text
A^r_cos(f) := Σ_k (1+λ_k)^(r/2)|cosineCoeff(f)_k| < ∞,
A^r_sin(f) := Σ_k (1+λ_k)^(r/2)|sineCoeff(f)_k| < ∞.
```

Assume on the positive-time window:

```text
u ∈ A³_cos.
```

Then for every `0 ≤ r ≤ 3`, monotonicity gives

```text
u ∈ A^r_cos.
```

The resolver gives

```text
v ∈ A^{r+2}_cos,       v_x ∈ A^{r+1}_sin.
```

In particular, since `u∈A³`, for all `0≤r≤3`:

```text
v ∈ A^r_cos,
v_x ∈ A^r_sin.
```

The weighted Wiener composition theorem gives

```text
D=(1+v)^(-β) ∈ A^r_cos,
D₁=(1+v)^(-β-1) ∈ A^r_cos.
```

Now assume, at the current ladder level,

```text
U ∈ A^r_cos.
```

Then resolver smoothing for `U` gives

```text
V=R_μU ∈ A^{r+2}_cos,
V_x ∈ A^{r+1}_sin.
```

Thus in particular:

```text
V ∈ A^r_cos,
V_x ∈ A^r_sin.
```

Now estimate each term in `Qlin`.

### Term 1

```text
U v_x D.
```

Types:

```text
U ∈ A^r_cos,
v_x ∈ A^r_sin,
D ∈ A^r_cos.
```

Product closure gives:

```text
U*D ∈ A^r_cos,
(U*D)*v_x ∈ A^r_sin.
```

### Term 2

```text
u V_x D.
```

Types:

```text
u ∈ A^r_cos,
V_x ∈ A^r_sin,
D ∈ A^r_cos.
```

So:

```text
u*D ∈ A^r_cos,
(u*D)*V_x ∈ A^r_sin.
```

### Term 3

```text
β u v_x V D₁.
```

Types:

```text
u ∈ A^r_cos,
V ∈ A^r_cos,
D₁ ∈ A^r_cos,
v_x ∈ A^r_sin.
```

So:

```text
u*V*D₁ ∈ A^r_cos,
(u*V*D₁)*v_x ∈ A^r_sin.
```

Therefore:

```text
Qlin ∈ A^r_sin.
```

The reaction derivative term is lower order:

```text
Rlin = (1-2u)U.
```

Since

```text
1-2u ∈ A^r_cos
```

and

```text
U ∈ A^r_cos,
```

we have

```text
Rlin ∈ A^r_cos.
```

---

## 4. Duhamel gains

### Divergence term

If

```text
Qlin ∈ A^r_sin
```

uniformly in `s` on the integration window, then

```text
Dchem_U(t)
  := ∫ S(t-s) ∂x Qlin(s) ds
```

belongs to

```text
A^{r+1}_cos.
```

Modewise:

```text
cosCoeff(∂xQlin)_k = ± sqrt(λ_k) sineCoeff(Qlin)_k.
```

The heat Duhamel multiplier gives, for `k≥1`,

```text
(1+λ_k)^((r+1)/2)
  ∫_{τ₀}^t e^{-(t-s)λ_k} sqrt(λ_k)|Qlin_k(s)| ds
≤ C (1+λ_k)^(r/2) sup_s |Qlin_k(s)|.
```

This uses

```text
sqrt(1+λ_k) sqrt(λ_k) ∫_0^{t-τ₀} e^{-ρλ_k}dρ ≤ C.
```

The zero mode is harmless because the divergence coefficient vanishes at `k=0`.

Thus the divergence Duhamel leg gives exactly `+1` derivative.

### Reaction term

If

```text
Rlin ∈ A^r_cos,
```

then

```text
∫ S(t-s)Rlin(s)ds ∈ A^{r+2}_cos.
```

So it is better than needed for the `+1` ladder.

### Heat/restart term

The restart heat term is

```text
S(t-τ₀)U(τ₀).
```

For every `t>τ₀`, heat smoothing puts it in every `A^s`. Uniformly on `[t₀,T]`, choose `τ₀<t₀`; then `t-τ₀ ≥ t₀-τ₀ > 0`, so the heat term is uniformly `A^3` on `[t₀,T]` even if `U(τ₀)` is only bounded/low-regularity.

If you want the ladder theorem on a closed window `[t₀,T]`, always start the Duhamel representation from a strictly earlier time `τ₀<t₀`.

---

## 5. The `U = u_t` ladder

Given a positive-time `A⁰` seed for `U`, the steps are:

### Step 0

Assume

```text
U ∈ A⁰_cos.
```

Then:

```text
Qlin ∈ A⁰_sin,
Rlin ∈ A⁰_cos.
```

Duhamel gives:

```text
U ∈ A¹_cos.
```

### Step 1

Assume

```text
U ∈ A¹_cos.
```

Then:

```text
Qlin ∈ A¹_sin,
Rlin ∈ A¹_cos,
```

and Duhamel gives:

```text
U ∈ A²_cos.
```

### Step 2

Assume

```text
U ∈ A²_cos.
```

Then:

```text
Qlin ∈ A²_sin,
Rlin ∈ A²_cos,
```

and Duhamel gives:

```text
U ∈ A³_cos.
```

Thus:

```text
A⁰ → A¹ → A² → A³.
```

This is the exact analogue of the `u` ladder, with the same divergence-limited `+1` gain.

---

## 6. Is there an obstruction from time-dependent coefficients?

No, provided the coefficient envelopes for `u` are uniform on the integration window.

The time-dependent coefficients are:

```text
u(s), v(s), v_x(s), D(s), D₁(s).
```

If `u` has a window-uniform `A³` envelope, then all of these have window-uniform `A^r` envelopes for every `0≤r≤3`. The product estimates are pointwise in time, and the Duhamel estimates only need a time-uniform source envelope or an integrable-in-time source envelope.

So the time dependence introduces bookkeeping, not a new analytic obstruction.

The only caveat is the window buffer again: to estimate `U(t)` on `[t₀,T]`, the Duhamel integral uses source values at times before `t₀`. Work on a slightly larger window `[τ₀,T]` with `τ₀<t₀`.

---

## 7. Minimal Lean-formalizable hypotheses

Define a trajectory weighted-Wiener envelope predicate, for example:

```lean
def TrajA (r : ℝ) (J : Set ℝ) (coeff : ℝ → ℕ → ℝ) : Prop :=
  ∃ E : ℕ → ℝ,
    WeightedL1 r E ∧
    ∀ t ∈ J, ∀ k, |coeff t k| ≤ E k
```

For sine coefficients, use the same predicate with `sineCoeffs`.

Let

```lean
Jbig := Set.Icc τ₀ T
J    := Set.Icc t₀ T
```

with

```lean
0 < τ₀, τ₀ < t₀, t₀ ≤ T.
```

The minimal hypotheses for the smoothing theorem are:

```lean
-- frozen coefficient regularity
huA3 : TrajA 3 Jbig (fun t k => cosineCoeffs (u t) k)

-- seed for U = u_t
hUA0 : TrajA 0 Jbig (fun t k => cosineCoeffs (U t) k)

-- resolver identities
hv_def  : ∀ t k, cosineCoeffs (v t) k = cosineCoeffs (u t) k / (μ + lam k)
hV_def  : ∀ t k, cosineCoeffs (V t) k = cosineCoeffs (U t) k / (μ + lam k)
hvx_def : ∀ t k, sineCoeffs (vx t) k = sign k * Real.sqrt (lam k) * cosineCoeffs (v t) k
hVx_def : ∀ t k, sineCoeffs (Vx t) k = sign k * Real.sqrt (lam k) * cosineCoeffs (V t) k

-- denominator composition envelopes, or a theorem deriving them from huA3
hD_A3  : TrajA 3 Jbig (fun t k => cosineCoeffs (fun x => (1 + v t x)^(-β)) k)
hD1_A3 : TrajA 3 Jbig (fun t k => cosineCoeffs (fun x => (1 + v t x)^(-β-1)) k)

-- product/coefficient bridge hypotheses
hCosBridge : relevant CosineMulBridge facts
hMixBridge : relevant MixedMulBridge facts

-- linearized mild identity for U on [τ₀,t]
hU_mild : ∀ t ∈ J, coefficient/mild identity for U(t)
```

Conclusion:

```lean
theorem positiveTime_u_t_A3
    (hbuf : 0 < τ₀ ∧ τ₀ < t₀ ∧ t₀ ≤ T)
    (huA3 : TrajA 3 Jbig (fun t k => cosineCoeffs (u t) k))
    (hUA0 : TrajA 0 Jbig (fun t k => cosineCoeffs (U t) k))
    (linearized/resolver/product hypotheses) :
    TrajA 3 J (fun t k => cosineCoeffs (U t) k)
```

The proof is an induction over `r=0,1,2` using a step theorem:

```lean
theorem u_t_A_step
    (hr : 0 ≤ r) (hr3 : r ≤ 2)
    (huA3 : TrajA 3 Jbig uCoeff)
    (hUr : TrajA r Jbig UCoeff) :
    TrajA (r+1) J UCoeff
```

Then apply with `r=0`, `r=1`, `r=2`, shrinking/using buffered windows as needed.

---

## 8. Relation to the seed you already have

Your already-proved per-mode derivative statement

```text
deriv(s ↦ û_n(s)) = fullSourceCoeffDot_n(s)
```

is a seed for the `U` ladder **only if** it includes a window-uniform `A⁰` envelope:

```text
∃ EU0 ∈ ℓ¹, ∀ t∈Jbig, ∀ n,
  |deriv(s ↦ û_n(s)) at t| ≤ EU0_n.
```

Per-mode differentiability alone is not enough.

If the derivative theorem has an `A^r`-type summability envelope already, use that as `hUA0` or stronger.

---

## 9. Answer to the three questions

### Q1

The exact linearized Duhamel equation is, for `τ₀<t`,

```text
U(t)
  = S(t-τ₀)U(τ₀)
    + a∫_{τ₀}^t S(t-s)∂x( U v_x D + u V_x D - βu v_x V D₁ )(s) ds
    + ∫_{τ₀}^t S(t-s)((1-2u)U)(s) ds.
```

From zero, one may write

```text
U(t)=S(t)(Δu₀+F(u₀))+∫_0^t S(t-s)F'(u(s))U(s)ds
```

only if `Δu₀+F(u₀)` is meaningful in the chosen space. For positive-time smoothing, the restart form is the correct statement.

### Q2

Yes, the same `+1` weighted-Wiener ladder applies. The linearized chemotaxis term is still a divergence of a product that is linear in `U` through either `U`, `V=R_μU`, or `V_x=(R_μU)_x`. At level `A^r`, resolver smoothing and product closure give

```text
Qlin(U) ∈ A^r_sin.
```

Then heat Duhamel applied to `∂xQlin` gives

```text
A^{r+1}_cos.
```

The lower-order reaction derivative `(1-2u)U` is non-divergence and gains two derivatives, so it does not limit the ladder.

### Q3

The minimal clean hypotheses are:

```text
u has a window-uniform A³_cos envelope on a slightly larger positive-time window,
U=u_t has a window-uniform A⁰_cos envelope on that larger window,
linearized mild identity for U,
resolver identities,
denominator composition envelopes,
cosine/mixed product bridges.
```

Then a clean induction over `r=0,1,2` gives `U∈A³_cos` on the target window. There is no obstruction from time-dependent coefficients as long as their envelopes are uniform on the larger window. The only real issues are the positive-time buffer and the `A⁰` seed for `U`.

---

## Final recommendation

Formalize this as a buffered ladder theorem:

```lean
positiveTime_u_t_A3_of_u_A3_and_u_t_A0
```

rather than trying to inline it into the chem-source time-C¹ theorem. Then the chem-source theorem can simply consume:

```text
u ∈ A³_cos,
u_t ∈ A³_cos
```

and discharge `q_t ∈ A³_sin` by pure resolver/product/composition bookkeeping.
