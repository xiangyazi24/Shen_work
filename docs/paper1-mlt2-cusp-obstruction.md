The obstruction is real. For the **elliptic implicit-step comparison with `B = Z`**, the term with \(W^{m-1}\) does **not** disappear in general, and the current repo interface still exposes exactly the false-for-\(1<m<2\) Lipschitz slot.

The repo has two different things that must not be conflated:

1. **Spatial antitonicity** of one produced step, `Antitone W`. The current Route‑A file proves this by differentiating the **paper-expanded** step, setting \(q=W'\), and applying a maximum principle to \(q\). That route is structurally good: the scary \(W^{m-2}q^2V'\) term has a good sign when \(\chi\le0\) and \(V'\le0\). The file explicitly says it avoids older sliding wrappers and is driven by `q = W'` and the differentiated paper-expanded operator. fileciteturn16file0L6-L12

2. **Time descent** of the Rothe orbit, `W ≤ Z`. That is still packaged as a per-step fact/producer output in `WaveRotheConcrete.lean`, not genuinely discharged by the same Route‑A derivative argument. The file lists `W ≤ Z` as one of the produced per-step facts and says the producer carries the per-step bridge. fileciteturn24file0L47-L56 The producer requires old iterates to be supersolutions, precisely because arbitrary trapped `Z` can overshoot. fileciteturn24file0L116-L126

So for your exact question: **Shen’s actual comparison does not justify the repo’s current local elliptic `W ≤ Z` argument by a bare Lipschitz bound on \(W^{m-1}\).** The paper uses a continuous-time auxiliary parabolic map, not this exact discrete contact-max estimate; the repo’s own notes identify the paper’s §4 auxiliary equation as the paper-expanded parabolic operator and the long-time/Schauder map route. fileciteturn38file0L23-L69

# 1. Exact difference at a contact max

Let

\[
a:=-\chi\ge0,\qquad V=V_u=\mathrm{frozenElliptic}(u),
\]

and write the paper operator as

\[
P_u(W)
=
W''+cW'
+a\,mW^{m-1}V'W'
+aW^m(V-W^\gamma)
+R(W),
\]

where

\[
R(s)=s(1-s^\alpha).
\]

At a positive maximum \(x_0\) of

\[
\phi=W-Z,
\]

assume

\[
\Delta:=W(x_0)-Z(x_0)>0,
\qquad
W'(x_0)=Z'(x_0),
\qquad
W''(x_0)\le Z''(x_0).
\]

Then

\[
\begin{aligned}
P_u(W)-P_u(Z)
&=
(W''-Z'')+c(W'-Z') \\
&\quad
+a\,mV'\bigl(W^{m-1}W'-Z^{m-1}Z'\bigr) \\
&\quad
+aV(W^m-Z^m) \\
&\quad
-a(W^{m+\gamma}-Z^{m+\gamma}) \\
&\quad
+\bigl(R(W)-R(Z)\bigr),
\end{aligned}
\]

all evaluated at \(x_0\).

Using \(W'=Z'\), the transport-gradient part becomes

\[
a\,mV'(x_0)Z'(x_0)
\left(W(x_0)^{m-1}-Z(x_0)^{m-1}\right).
\]

If the profiles are antitone and the frozen elliptic signal is antitone, then

\[
Z'(x_0)\le0,\qquad V'(x_0)\le0,
\]

so

\[
V'(x_0)Z'(x_0)\ge0.
\]

Since \(W>Z\), also

\[
W^{m-1}-Z^{m-1}\ge0.
\]

Therefore this term is **nonnegative**. It is not a good-sign term. It is genuinely one of the bad terms to be absorbed.

The rest behaves as expected:

\[
W''-Z''\le0,
\qquad
c(W'-Z')=0,
\]

\[
aV(W^m-Z^m)\le a\|V\|_\infty\,L_m(M)\Delta,
\]

\[
-a(W^{m+\gamma}-Z^{m+\gamma})\le0,
\]

and

\[
R(W)-R(Z)\le L_R(M)\Delta.
\]

So the only dangerous piece is exactly

\[
a\,mV'Z'\bigl(W^{m-1}-Z^{m-1}\bigr).
\]

The current repo’s local maximum-principle infrastructure exposes the same obstruction. The `chemFlux_increment_split` lemma rewrites the flux derivative difference as

\[
mV'(W^{m-1}-B^{m-1})W'
+
(W^m-B^m)V'',
\]

after substituting \(W'=B'\). fileciteturn28file0L187-L199 Then `RotheStepChemData` requires the hypothesis

```lean
|(W x₀)^(p.m - 1) - (B x₀)^(p.m - 1)|
  ≤ L1 * (W x₀ - B x₀)
```

as an input field. fileciteturn33file0L25-L47 That field is precisely the false uniform Lipschitz bound when \(1<m<2\).

So: **the bare \(W^{m-1}\) term really appears in the local elliptic `W ≤ Z` comparison. It is not linearly absorbable from only \(0\le Z\le W\le M\) and \(|Z'|\le\Lambda\).**

# 2. Why contact positivity does not save the argument

At a positive contact maximum,

\[
W(x_0)>Z(x_0)\ge0,
\]

so \(W(x_0)>0\). This gives differentiability of \(s^m\) at \(W(x_0)\), but it does **not** give a uniform lower bound

\[
W(x_0)\ge\eta>0.
\]

The contact can occur arbitrarily far in the right tail, where both \(W\) and \(Z\) are small. For \(p=m-1\in(0,1)\),

\[
\frac{(z+\delta)^p-z^p}{\delta}
\]

can blow up as \(z,\delta\to0\). In particular, with only

\[
|Z'(x_0)|\le\Lambda,
\]

there is no uniform constant \(L\) such that

\[
|Z'(x_0)|\,
|W^{m-1}-Z^{m-1}|
\le L(W-Z).
\]

That is the cusp.

The repo comment in `WaveRotheMaxPrinciple.lean` says the chemotaxis half is derivable from the split plus a Lipschitz fact for \(s^{m-1}\) and \(s^m\), but that statement is only faithful for \(m=1\) or \(m\ge2\), or with an extra weighted derivative invariant. fileciteturn27file0L39-L48 The later `chemFlux_increment_bound` theorem is honest in the sense that it assumes the needed \(L_1\) inequality as input; it does not prove it. fileciteturn36file0L5-L23

# 3. The only ways to save this exact elliptic comparison

There are four possibilities.

## A. `m = 1`

Then \(m-1=0\), and

\[
W^{m-1}-Z^{m-1}=W^0-Z^0=0
\]

in the relevant positive region. The bad term vanishes.

## B. `m ≥ 2`

Then \(s\mapsto s^{m-1}\) is Lipschitz on `[0,M]`, with

\[
|W^{m-1}-Z^{m-1}|
\le
(m-1)M^{m-2}|W-Z|.
\]

Then the contact comparison closes using \(|Z'|\le\Lambda\), but this is an over-restriction. The paper and the repo’s `CMParams` allow real \(m,\alpha,\gamma\ge1\); restricting to natural or \(m\ge2\) is not faithful to the target. The repo’s Paper‑1 war map explicitly marks real exponents \(m,\alpha,\gamma\ge1\) as the faithful setting. fileciteturn13file0L13-L14

## C. Add a weighted derivative invariant

A possible analytic rescue is a new invariant such as

\[
|Z'(x)|\le C Z(x)
\]

or a comparable tail-weighted slope bound. Then for \(p=m-1\in(0,1)\), one can prove a weighted cusp lemma of the form

\[
z\bigl((z+\delta)^p-z^p\bigr)
\le C_{p,M}\delta
\qquad
(0\le z\le z+\delta\le M).
\]

Thus

\[
|Z'|\,|W^{m-1}-Z^{m-1}|
\le
C\,C_{p,M}(W-Z).
\]

This would make the \(1<m<2\) term absorbable.

But that is a **new invariant**, not something the current repo’s per-step facts provide. The current per-step bundle carries a uniform derivative bound \(|W'|\le\Lambda\), not a weighted logarithmic bound \(|W'|\lesssim W\). fileciteturn24file0L90-L108

## D. Avoid this local elliptic comparison

This is the faithful direction.

The paper’s actual §4 construction is a **parabolic auxiliary flow** for the paper-expanded operator, then a long-time limit/Schauder map. The repo’s OP412 note says the paper defines the auxiliary parabolic problem, proves trapping by comparison, defines the long-time map \(T_{\kappa,1}\), and applies Schauder to that map. fileciteturn38file0L23-L69

In continuous parabolic comparison, the relevant first-contact argument compares a solution with a super-solution at the first touching point, where the two values are equal. At such a first contact,

\[
W=B,
\qquad
W_x=B_x,
\]

so the coefficient difference

\[
W^{m-1}-B^{m-1}
\]

is exactly zero. No Lipschitz estimate for \(s^{m-1}\) at zero is needed. This is the structural reason the paper can allow all \(m\ge1\).

That structural cancellation is lost in the elliptic implicit-step proof with a positive maximum of \(W-Z\), because there

\[
W(x_0)>Z(x_0),
\]

not \(W(x_0)=Z(x_0)\).

# 4. Does divergence form fix it?

It depends what “use divergence form” means.

For the **Banach fixed-point solve**, yes: use divergence Green form. That is the right C⁰ route. It puts the derivative on the Green kernel and keeps the nonlinear source in terms of \(W^m\), which is Lipschitz on `[0,M]` for every \(m\ge1\). The repo’s own per-step route says the Banach part should be done in divergence Green form and that this avoids putting `W'` in the source. fileciteturn40file0L108-L118

For the **paper-expanded operator**, the repo note gives the right divergence-form Green map:

\[
\int K_\lambda
\bigl(
R(W)+\chi W^m(W^\gamma-u^\gamma)+\lambda Z
\bigr)
-
\chi\int K_\lambda'
\bigl(W^mV_u'\bigr),
\]

which avoids `deriv W` and keeps the fixed point in bounded continuous functions. fileciteturn40file0L170-L185

But for the **local differential maximum principle** proving \(W\le Z\), merely writing the operator in divergence notation does not erase the cusp. If you evaluate

\[
\partial_x\bigl((W^m-Z^m)V'\bigr)
\]

at a contact maximum, the product rule gives

\[
m(W^{m-1}-Z^{m-1})Z'V'
+
(W^m-Z^m)V'',
\]

so the same non-Lipschitz term returns.

Thus:

\[
\text{divergence form fixes the C⁰ fixed-point map, not the local elliptic } W\le Z \text{ proof by itself.}
\]

The repo’s weak/viscosity route note makes the same point: integration by parts is useful for regularity and for avoiding \(W'\) in the map, but it does not automatically create a positive-kernel comparison; \(K'\) changes sign and the chemotaxis source order does not follow from monotonicity alone. fileciteturn44file0L72-L79

# 5. What is the faithful route?

For Paper‑1 fidelity, I would not try to patch the current `W ≤ Z` proof by pretending \(s^{m-1}\) is Lipschitz.

The faithful route is one of these two.

## Route 1: Follow Shen literally — parabolic auxiliary flow

Formalize the §4 paper auxiliary parabolic problem for `paperWaveOperator`, prove comparison/trapping there, define the long-time map, and apply Schauder. This is closest to Shen.

This avoids the elliptic positive-maximum \(W>Z\) cusp because comparison is by first contact, where the compared profiles are equal.

## Route 2: Keep a discrete Rothe skeleton, but change the comparison invariant

Use the divergence-form Green map for the **solve**, and do not make the false local Lipschitz comparison a theorem. Instead, add one of:

```lean
-- weighted slope route
∀ x, |deriv Z x| ≤ C * Z x
```

plus the weighted cusp lemma; or

```lean
-- abstract faithful residual
RotheStepTimeDescentData p c lam M u Z W
```

whose contents are a real comparison argument, not the conclusion `W ≤ Z`.

But if the residual just contains

```lean
hL1 :
  |W^(m-1) - Z^(m-1)| ≤ L1 * (W - Z)
```

with \(L_1\) uniform under only \(0\le Z\le W\le M\), it is not satisfiable for \(1<m<2\).

# 6. Concrete answer to your three questions

**1. Does the \(W^{m-1}\) term cancel?**  
No, not in the elliptic contact comparison with \(B=Z\). The term is

\[
(-\chi)mV'Z'
\bigl(W^{m-1}-Z^{m-1}\bigr),
\]

and for \(\chi\le0\), \(V'\le0\), \(Z'\le0\), it is generally nonnegative and bad. The repo’s current max-principle closer exposes this exact term and requires a separate \(L_1\) Lipschitz bound for \(W^{m-1}-B^{m-1}\). fileciteturn33file0L25-L47

**2. If not absorbable, what saves it?**  
Contact positivity alone does not. It gives \(W(x_0)>0\), but not a uniform lower bound. A weighted slope invariant could save it; \(m\ge2\) saves it; \(m=1\) makes it vanish. But none of those is Shen’s general \(m\ge1\) proof as currently encoded.

**3. Is the faithful route divergence form?**  
For the fixed-point/Green solve: yes, absolutely. For the local differential `W≤Z` maximum principle: divergence notation alone is not enough, because product-rule expansion reintroduces the cusp. The most faithful route is Shen’s paper-expanded **parabolic comparison/long-time map**. If you keep Rothe, use the divergence-form paper Green map for existence and either add a genuine weighted comparison invariant or replace the time-descent step by a parabolic/first-contact comparison layer.

Bottom line: the current `hL1`/`C_chem` path is valid for \(m=1\) or \(m\ge2\), but it is not a faithful discharge for the stated \(1\le m\) real-exponent theorem.
## De-risking analysis (2026-06-19, this session) — corrects the earlier "Route 2a is cheapest" lean
Checked whether Route 2a's weighted-slope invariant `|Z'| ≤ C·Z` is already available:
- The campaign HAS log-derivative machinery: `logDerivativeBoundFormula` (Statements.lean:11310) +
  `Lemma_5_2_explicit` (`deriv U x / U x ≤ logDerivativeBoundFormula p c`). BUT it requires
  `IsTravelingWave p c U V` — it holds for the WAVE PROFILE (stationary fixed point, using the wave ODE),
  NOT for a mid-iteration trapped iterate Z. So it is LIMIT/PROFILE-level, not ITERATE-level.
- Route 2a needs the log-derivative bound as a PER-STEP INVARIANT (preserved by the implicit-step producer),
  which Lemma 5.2 does NOT provide. The uniform iterate bound is only `|W'| ≤ Λ`; on the right tail
  (x→+∞, W~e^{−κx}) that gives `|W'|/W ≤ Λ·e^{κx} → ∞`, i.e. the weighted-slope FAILS unless the iterate's
  derivative also decays exponentially (a right-tail rate the iterate does not currently carry — ExpLeftRate
  is LEFT-only).
- CONCLUSION: Route 2a is NOT a trivial reuse of Lemma 5.2; it requires a genuine new per-step
  log-derivative-preservation result (does the producer preserve `|W'| ≤ C·W` on the right tail?), whose
  truth is unverified and plausibly hard. This rebalances the routes — **Route 1 (parabolic first-contact,
  where the cusp vanishes STRUCTURALLY because W=B at the touch) deserves equal/greater weight** as the
  cleaner faithful long-term route, despite the restructure. Decision remains Xiang's; my earlier lean
  toward 2a is withdrawn pending his call.
