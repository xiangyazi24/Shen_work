ANSWER Q84 288af5da

# Adversarial audit of chiPos_squeeze_gap_step

Repository target: xiangyazi24/Shen_work

Audited theorem: ShenWork/Paper1/WholeLineChiPosSqueezeAlgebra.lean at commit b7790735.

## Executive verdict

The scalar algebra is correct, non-vacuous, and its index placement is the right one for a sequential floor-first rectangle round. I do not see a mathematical error in the proved implication.

However, the theorem is only the upper-residual half of the barrier step. It is not by itself a certificate that the PDE barriers can produce ell' and M'. The real round must also prove that the two normalized residuals are nonnegative, or equivalently that the published targets lie on the barrier-reachable sides of the two equilibrium roots. This is the main integration hazard.

Two P0 conditions must be enforced before wiring the theorem into the unattended induction:

1. Use a state-dependent b^m/a^m contact comparison, not the existing constant-defect floor wrapper. A raw constant defect of size chi*M^m*(M^gamma-ell^gamma) does not deliver the theorem's ell'^(m-1) floor inequality and is unsatisfiable from a tiny floor when m=1. The phase-2 brief correctly identifies this and asks for a weighted comparison.

1. A fixed positive delta does not prove convergence to zero. It proves entry into a radius 2*delta/(1-2*chi). For the final theorem, either choose delta=delta(epsilon) and run finitely many rounds for each requested epsilon, or use a sequence delta_n -> 0 and a variable-error recurrence.

A third bookkeeping warning is nearly P0:

delta in the algebra theorem is a normalized per-capita residual, after division by the positive contact value. It is not automatically equal to an unnormalized PDE defect or to the amplitude by which a finite-time barrier misses its asymptotic target.

That conversion needs an explicit lemma.

---

## 1. One exact PDE round and the index placement

Write the nondivergence-form equation schematically as

```plain text
q_t = q_xx + c q_x
      - chi*m*q^(m-1)*q_x*V_x
      + chi*q^m*(q^gamma - V)
      + q*(1-q^alpha),
```

where V = frozenElliptic q.

Assume that after time T_n the old rectangle is valid globally:

```plain text
0 < ell <= q(t,x) <= M,
ell <= 1 <= M.
```

Because the whole-line resolvent kernel is positive and has mass one,

```plain text
ell^gamma <= V(t,x) <= M^gamma.
```

The correct full round is sequential.

### Step A: improve the floor first, using the OLD ceiling M

Let b(t) be a spatially constant increasing lower barrier. At a lower contact, q=b; the first-order chemotaxis term is handled as a drift coefficient in the maximum principle, while the zeroth-order term satisfies

```plain text
chi*b^m*(b^gamma - V)
  >= -chi*b^m*(M^gamma - b^gamma).
```

Thus the scalar sufficient inequality is

```plain text
b' <= b*(1-b^alpha)
      - chi*b^m*(M^gamma-b^gamma)
```

or, after dividing by b>0,

```plain text
b'/b <= F_M(b),

F_M(x) := 1-x^alpha
          - chi*x^(m-1)*(M^gamma-x^gamma).
```

The old floor ell is only the starting value of the barrier. The adverse resolver bound comes from the old ceiling M, and the contact value tends to the new floor. Therefore the endpoint residual is exactly

```plain text
F_M(ell')
 = 1-ell'^alpha
   - chi*ell'^(m-1)*(M^gamma-ell'^gamma).
```

So the theorem's floor placement is correct:

```plain text
1-ell'^alpha
  <= chi*ell'^(m-1)*(M^gamma-ell'^gamma) + delta.
```

It would be wrong to use the old prefactor ell^(m-1) at the endpoint, and it would be premature to use the new ceiling M', which has not yet been proved.

### Step B: publish the finite-time floor ell'

The floor barrier approaches a raw equilibrium target asymptotically. At finite time one publishes a slightly weaker lower bound ell'. Only this published value is known uniformly for all later times.

The round must now restart at a later time T_floor with

```plain text
ell' <= q(t,x) <= M,
qquad t >= T_floor.
```

This restart is not cosmetic. Without it, the ceiling comparison cannot use ell'^gamma as a lower resolver bound.

### Step C: improve the ceiling, using the NEW published floor ell'

Now positivity and mass one give

```plain text
V(t,x) >= ell'^gamma.
```

Let a(t) be a decreasing upper barrier. At an upper contact q=a,

```plain text
chi*a^m*(a^gamma-V)
  <= chi*a^m*(a^gamma-ell'^gamma).
```

A sufficient supersolution inequality is

```plain text
a' >= a*(1-a^alpha)
      + chi*a^m*(a^gamma-ell'^gamma).
```

Define

```plain text
C_ell'(x) := x^alpha-1
             - chi*x^(m-1)*(x^gamma-ell'^gamma).
```

Then the right-hand side is -a*C_ell'(a). The endpoint residual is therefore

```plain text
C_ell'(M')
 = M'^alpha-1
   - chi*M'^(m-1)*(M'^gamma-ell'^gamma).
```

Hence the theorem's ceiling placement is also correct:

```plain text
M'^alpha-1
  <= chi*M'^(m-1)*(M'^gamma-ell'^gamma) + delta.
```

The prefactor and the first power in the difference are both M' because the upper contact value tends to the new ceiling. The resolver lower endpoint is ell' because the floor step has already been completed and restarted.

### Conclusion on index placement

The exact dependency graph is

```plain text
old [ell,M]
  -- floor barrier using V <= M^gamma --> published ell'
  -- restart: [ell',M]
  -- ceiling barrier using V >= ell'^gamma --> published M'
  --> new [ell',M'].
```

This is precisely the theorem's indexing.

The theorem is not compatible with a simultaneous floor/ceiling barrier round. If the ceiling barrier is launched before the floor is published, it can use only the old floor ell, not ell'. The Lean round theorem should expose an intermediate time and visibly sequence the two comparisons.

---

## 2. What the algebra hypotheses omit: the side-of-root conditions

The displayed hypotheses are not, by themselves, sufficient to run either barrier. They say only that the endpoint residuals are at most delta:

```plain text
F_M(ell') <= delta,
C_ell'(M') <= delta.
```

A reachable increasing floor and decreasing ceiling also need the opposite inequalities:

```plain text
0 <= F_M(ell'),
0 <= C_ell'(M').
```

The honest target package is therefore

```plain text
0 <= F_M(ell') <= delta_floor,
0 <= C_ell'(M') <= delta_ceil.
```

Why these signs?

- For the floor, b' <= b*F_M(b) must allow b to increase on [ell,ell'); hence F_M must be nonnegative there.

- For the ceiling, a' >= -a*C_ell'(a) must allow a to decrease on (M',M]; hence C_ell' must be nonnegative there.

At the critical exponent the residuals simplify dramatically. For positive x, using

```plain text
alpha = m+gamma-1,
x^(m-1)*x^gamma = x^alpha,
```

we get

```plain text
F_M(x)
 = 1-(1-chi)*x^alpha-chi*M^gamma*x^(m-1),

C_l(x)
 = (1-chi)*x^alpha+chi*l^gamma*x^(m-1)-1.
```

Under the intended regime 0 <= chi < 1/2, F_M is strictly decreasing and C_l is strictly increasing on positive values. This can be proved in Lean mostly by Real.rpow monotonicity; a derivative theorem is not necessary.

Consequently:

```plain text
F_M(ell)>0 and F_M(1)<=0
  => a unique floor root Lstar in (ell,1],

C_ell'(1)<=0 and C_ell'(M)>0
  => a unique ceiling root Astar in [1,M).
```

The finite-time published targets should lie on the reachable sides:

```plain text
ell < ell' < Lstar,
Astar < M' < M.
```

Then

```plain text
0 < F_M(ell') <= delta_floor,
0 < C_ell'(M') <= delta_ceil
```

can be made arbitrarily small by choosing the published targets sufficiently close to the roots.

### Required state invariants

The scalar theorem does not need these facts, but the PDE round producer does. It should maintain or derive:

```plain text
F_M(ell) > 0,       -- floor can start improving
C_ell'(M) > 0,      -- ceiling root lies below the old ceiling
```

plus the two-sided target residual bounds.

The root-existence conditions are not automatic for an arbitrary enormous initial rectangle. In particular, when m=1,

```plain text
F_M(0+) = 1-chi*M^gamma,
```

so a ceiling burn-in satisfying roughly chi*M^gamma<1 is genuinely needed. This is exactly the special m=1 issue identified in the phase-2 implementation brief. For m>1, the adverse factor vanishes as the floor tends to zero, but the induction should still carry the sign invariant explicitly.

### Current implementation hazard

The existing phase-1 buffered floor comparison uses a constant raw defect of the form

```plain text
H = chi*M^m*(M^gamma-ell^gamma + tail)
```

and asks for

```plain text
H < ell*(1-L^alpha).
```

That is much stronger than the contact-sharp condition and does not imply the theorem's endpoint formula. It loses the crucial b^m factor. From a tiny floor with m=1, it can be unsatisfiable even when the genuine weighted contact inequality is favorable.

Therefore the scalar engine must be wired only to the planned weighted comparison that preserves

```plain text
chi*b^m*(M^gamma-b^gamma)
```

throughout the floor barrier. The phase-2 brief already says this; it is not an optional optimization.

---

## 3. Vacuity check: explicit nontrivial data

The theorem is decisively non-vacuous. Take

```plain text
m      = 1
gamma  = 1
alpha  = 1
chi    = 1/4
ell    = 1/4
ell'   = 33/50
M      = 2
M'     = 28/25
delta  = 1/200.
```

All structural hypotheses hold:

```plain text
1 <= m,
1 <= gamma,
alpha = m+gamma-1,
0 <= chi,
0 < ell <= ell' <= 1 <= M' <= M.
```

The old rectangle has width

```plain text
M-ell = 2-1/4 = 7/4,
```

so it is genuinely order one.

Because m-1=0, all prefactors are one.

### Floor inequality

```plain text
1-ell'
 = 1-33/50
 = 17/50
 = 68/200.
```

The right side is

```plain text
chi*(M-ell') + delta
 = (1/4)*(2-33/50) + 1/200
 = (1/4)*(67/50) + 1/200
 = 67/200 + 1/200
 = 68/200.
```

Thus hfloor holds with equality.

### Ceiling inequality

```plain text
M'-1
 = 28/25-1
 = 3/25
 = 24/200.
```

The right side is

```plain text
chi*(M'-ell') + delta
 = (1/4)*(28/25-33/50) + 1/200
 = (1/4)*(23/50) + 1/200
 = 23/200 + 1/200
 = 24/200.
```

Thus hceil also holds with equality.

This example is not an artificial incompatible choice. The exact floor root for the old ceiling M=2 is

```plain text
F_M(x) = 1-x-(1/4)*(2-x)
       = 1/2-(3/4)x,

Lstar = 2/3.
```

The published floor 33/50=0.66 lies just below 2/3, and its residual is exactly 1/200.

Using the published floor ell'=33/50, the ceiling residual is

```plain text
C_ell'(x) = x-1-(1/4)*(x-ell')
          = (3/4)x + (1/4)ell' - 1.
```

Its exact root is

```plain text
Astar = 167/150 = 1.11333...,
```

and the published ceiling 28/25=1.12 lies just above it, again with residual 1/200.

So the tuple models precisely what a finite-time round should do: publish endpoints slightly inside the exact asymptotic roots.

For an even simpler exact-root witness, take

```plain text
ell' = 2/3,
M'   = 10/9,
delta = 0
```

with all other parameters unchanged. Both target inequalities then hold with equality. This proves non-vacuity even at zero defect, although exact roots are normally reached only asymptotically rather than at finite time.

---

## 4. Finite-time asymptotic targets and delta bookkeeping

The theorem is compatible with barriers that reach their raw targets only asymptotically, but the bookkeeping must be done in the residual variables, not by informal amplitude language.

### Correct finite-time construction

Let Lstar be the exact floor root:

```plain text
F_M(Lstar)=0.
```

The increasing barrier tends to Lstar from below. Choose the finite-time published floor ell'<Lstar first, with

```plain text
0 < F_M(ell') <= delta_floor.
```

Then choose a finite time at which the barrier exceeds ell'.

After restarting with the published floor, let Astar be the exact ceiling root for ell':

```plain text
C_ell'(Astar)=0.
```

Choose M'>Astar with

```plain text
0 < C_ell'(M') <= delta_ceil,
```

then choose a finite time at which the decreasing barrier is below M'.

This ordering avoids trying to convert an arbitrary time error after the fact.

### Amplitude slack is not automatically residual slack

If one instead knows only

```plain text
Lstar-ell' <= eta_floor,
M'-Astar <= eta_ceil,
```

one still needs continuity or Lipschitz bounds such as

```plain text
F_M(ell') <= K_floor*eta_floor,
C_ell'(M') <= K_ceil*eta_ceil.
```

Setting delta=eta without proving this conversion is dimensionally and mathematically unjustified. A named residual-modulus lemma would prevent this error in Lean.

### Raw PDE defects must be normalized

Suppose a floor barrier theorem produces a raw additive defect H_floor in

```plain text
ell'*(1-ell'^alpha)
  <= chi*ell'^m*(M^gamma-ell'^gamma) + H_floor.
```

After division, the theorem needs

```plain text
1-ell'^alpha
  <= chi*ell'^(m-1)*(M^gamma-ell'^gamma)
     + H_floor/ell'.
```

Thus the algebraic delta must dominate H_floor/ell', not merely H_floor. This distinction is dangerous when the floor is small.

For the ceiling, a raw defect H_ceil becomes H_ceil/M' after division. Since M'>=1, this side is benign, but the two normalizations are different.

For a buffered half-line rather than the exact whole-line rectangle, resolver tail errors can still be absorbed in delta, provided the normalization is explicit. Schematically:

```plain text
floor tail contribution
  <= chi*b^(m-1)*tail_upper
  <= chi*tail_upper              because b<=1 and m>=1,

ceiling tail contribution
  <= chi*a^(m-1)*tail_lower
  <= chi*M^(m-1)*tail_lower.
```

Take delta_floor and delta_ceil large enough to include these normalized tail terms plus the finite-publication residuals.

### Across rounds

Let

```plain text
g_n = M_n^alpha-ell_n^alpha,
r   = 2*chi.
```

With a uniform per-side bound delta, the current theorem gives

```plain text
g_(n+1) <= r*g_n + 2*delta.
```

The committed recurrence lemma correctly yields

```plain text
g_n <= r^n*g_0 + 2*delta/(1-r).
```

This is consistent, but it does not tend to zero for fixed delta>0.

There are two honest closure patterns.

Recommended: choose delta after epsilon

For a requested final tolerance epsilon, choose for example

```plain text
2*delta/(1-r) < epsilon/4,
```

then choose N with

```plain text
r^N*g_0 < epsilon/4.
```

After N finite rounds,

```plain text
g_N < epsilon/2,
```

leaving room for strict inequalities and the endgame. This is likely the simplest Lean proof because UniformConvergesToConstant already quantifies over epsilon; the construction may depend on epsilon.

Alternative: variable defects

If one wants a single infinite squeeze sequence, prove the variable-error recurrence

```plain text
g_n <= r^n*g_0
       + 2*sum_{j<n} r^(n-1-j)*delta_j.
```

Then delta_j -> 0 implies the convolution tends to zero. A geometric choice is particularly easy. This requires a new recurrence lemma; the current constant-error theorem is insufficient for that route.

### Separate the two defects

The floor and ceiling errors naturally differ. A cleaner base theorem would take delta_floor and delta_ceil separately and conclude

```plain text
M'^alpha-ell'^alpha
  <= 2*chi*(M^alpha-ell^alpha)
     + delta_floor + delta_ceil.
```

The current theorem is then the corollary with both errors bounded by delta. This avoids repeatedly replacing two different normalized budgets by their maximum and then paying an opaque factor two.

---

## 5. A sharper power-gap form

There is a strictly sharper contraction coefficient available without changing the gap variable.

Let

```plain text
g  = M^alpha-ell^alpha,
g' = M'^alpha-ell'^alpha.
```

After adding the target inequalities, write the two chemotaxis products as A and B.

The floor product satisfies

```plain text
A <= M^alpha-ell'^alpha <= g.
```

For the ceiling product, do not immediately enlarge to the old gap. The same critical-exponent absorption gives

```plain text
B <= M'^alpha-ell'^alpha = g'.
```

Therefore, with separate errors,

```plain text
g' <= chi*g + chi*g' + delta_floor + delta_ceil,
```

hence the division-free sharper inequality

```plain text
(1-chi)*g'
  <= chi*g + delta_floor + delta_ceil.
```

If chi<1, this becomes

```plain text
g'
  <= (chi/(1-chi))*g
     + (delta_floor+delta_ceil)/(1-chi).
```

For chi<1/2,

```plain text
chi/(1-chi) < 1
```

and it is smaller than 2*chi. Thus it reduces the number of rounds.

There is no improvement in the eventual fixed-error radius:

```plain text
[(delta_floor+delta_ceil)/(1-chi)]
  / [1-chi/(1-chi)]
 = (delta_floor+delta_ceil)/(1-2*chi),
```

which is the same radius obtained from the current recurrence. The sharper version trades a better geometric factor for a larger per-step normalized additive term.

### Lean recommendation

Add, but do not necessarily replace the existing theorem with, a lemma of the form

```javascript
theorem chiPos_squeeze_gap_step_self_absorb ... :
  (1-chi)*(M'^alpha-ell'^alpha) <=
    chi*(M^alpha-ell^alpha) + deltaFloor + deltaCeil
```

The division-free statement is robust and useful. The current 2*chi theorem remains simpler to feed into affine_recurrence_iterate_le and makes the paper's chi<1/2 condition immediate.

---

## 6. Should the induction use M-ell instead?

No. The alpha-power gap is the right global Lean variable.

The critical identity

```plain text
alpha = m+gamma-1
```

absorbs each nonlinear product directly into a power gap. This is why the contraction constant is parameter-clean.

It is true that

```plain text
M-ell <= M^alpha-ell^alpha
```

for 0<ell<=1<=M and alpha>=1, so the power gap already controls the desired physical width and |u-1|.

The reverse comparison

```plain text
M^alpha-ell^alpha <= C*(M-ell)
```

requires an upper bound on M and a mean-value/real-power derivative constant. The resulting linear-width recurrence has coefficient roughly 2*chi*C, which need not be below one globally. Near equilibrium one can obtain sharper local constants related to 2*chi*gamma/alpha, but that requires a local-entry radius and additional Real.rpow calculus. It is not simpler than the existing exact absorption.

Likewise, a log-ratio gap is natural for the continuous rectangle ODE, but introduces positivity, logarithm, and conversion lemmas with no clear benefit for this discrete target map.

Recommended induction state:

```plain text
g_n := M_n^alpha-ell_n^alpha.
```

Use the committed endgame theorem directly.

---

## 7. Concrete Lean architecture recommended by this audit

### Residual definitions

```javascript
def chiPosFloorResidual
    (m gamma alpha chi M x : R) : R :=
  1 - x^alpha - chi*x^(m-1)*(M^gamma-x^gamma)

def chiPosCeilResidual
    (m gamma alpha chi ell x : R) : R :=
  x^alpha - 1 - chi*x^(m-1)*(x^gamma-ell^gamma)
```

### Critical rewrites and monotonicity

Prove named lemmas:

```plain text
floorResidual = 1-(1-chi)x^alpha-chi*M^gamma*x^(m-1),
ceilResidual  = (1-chi)x^alpha+chi*ell^gamma*x^(m-1)-1,
```

then strict antitonicity/monotonicity for positive x under chi<1.

### Target package

```javascript
structure ChiPosSqueezeTargets (...) : Prop where
  ell_le_ell' : ell <= ell'
  ell'_le_one : ell' <= 1
  one_le_M'   : 1 <= M'
  M'_le_M     : M' <= M
  floor_nonneg : 0 <= chiPosFloorResidual ... M ell'
  floor_small  : chiPosFloorResidual ... M ell' <= deltaFloor
  ceil_nonneg  : 0 <= chiPosCeilResidual ... ell' M'
  ceil_small   : chiPosCeilResidual ... ell' M' <= deltaCeil
```

The PDE barrier constructors should consume the nonnegative fields; the scalar contraction theorem should consume the small fields.

### Sequential round theorem

The round theorem should visibly have two times:

```plain text
T_n
  -> T_floor, where q >= ell' and q <= M
  -> T_(n+1), where ell' <= q <= M'.
```

Do not hide the floor-first ordering in a symmetric record.

### Recurrence

Prefer the two-error scalar theorem. For the final convergence proof, either:

```plain text
fix epsilon -> choose one delta -> finite Nat iteration,
```

or add the variable-error convolution lemma before attempting an infinite sequence.

---

## Final audit judgment

### What passes

- The theorem's algebraic implication is sound.

- The old/new index placement is exactly right for a floor-first sequential round.

- The critical exponent is used in the correct place.

- The assumptions are satisfiable with an order-one old rectangle and even with delta=0.

- The endgame through the alpha-power gap is the right global choice.

### What would cost a week if missed

1. Treating hfloor/hceil as sufficient barrier hypotheses rather than only the small-residual halves.

1. Wiring the constant-defect floor comparison into this engine; it does not produce the required normalized target relation and fails at small m=1 floors.

1. Running floor and ceiling simultaneously while still using ell' in the ceiling resolver bound.

1. Calling raw PDE defect or amplitude slack delta without dividing by the contact value and proving a residual-modulus conversion.

1. Iterating with a fixed positive delta and claiming convergence to zero.

Bottom line: keep the scalar engine. Add the two-sided residual target package and a weighted, sequential PDE round producer before proceeding to the Nat induction.