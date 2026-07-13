ANSWER Q4597 36411cf2

# Negative-branch upper barrier: the relaxed `1 + |χ|` budget is correct, but for the paper-expanded operator

## Verdict

The proposed correction is mathematically correct:

```text
|χ| (1 + mγκ²) / (1 - γ²κ²) ≤ 1 + |χ|
```

is exactly the scalar condition needed for the exponential part of the negative-branch upper barrier with `M = 1`. It covers every `χ ≤ 0`, provided the speed satisfies the paper's `c > cStarLower p`; there is no hidden upper bound on `|χ|`.

There is, however, an important operator-level qualification.

* The current repo theorem `whole_line_super_barrier` concludes a supersolution inequality for the off-diagonal divergence-form operator `frozenWaveOperator`.
* The favorable term `-|χ| W^(m+γ)` is present in the paper's modified cross-frozen operator `paperWaveOperator`, not in `frozenWaveOperator` with an arbitrary frozen profile in the elliptic source slot.
* Therefore, one must **not** simply replace the hypothesis `… ≤ 1` by `… ≤ 1 + |χ|` inside the existing `whole_line_super_barrier`. That edit would make its proof claim false in general.
* The paper-faithful fix is to prove a new whole-line supersolution theorem for `paperWaveOperator` and feed that into the already existing paper-Rothe route. At the eventual diagonal fixed point, the repo already proves that `paperWaveOperator = frozenWaveOperator`.

This distinction also removes the current extra constant-region hypothesis

```lean
hsrc : frozenElliptic p q x ≤ (q x) ^ p.γ
```

from the upper-barrier construction. The paper-expanded constant branch closes from the ordinary trap bound `frozenElliptic p q ≤ 1`.

---

# 1. Exact residual calculation

Write

```text
h := |χ| = -χ ≥ 0,
V := V_q = frozenElliptic p q,
E(x) := exp(-κ x).
```

A translated barrier `min(1, exp(-κ(x-x₀)))` gives the same calculation after translating `q`; the repo's canonical `upperBarrier κ 1` corresponds to `x₀ = 0`, so I use that normalization.

The repo definitions are:

```lean
def frozenWaveOperator (p : CMParams) (c : ℝ) (q W : ℝ → ℝ) : ℝ → ℝ :=
  fun x =>
    iteratedDeriv 2 W x + c * deriv W x
      - p.χ * deriv
          (fun y => (W y) ^ p.m * deriv (frozenElliptic p q) y) x
      + W x * (1 - (W x) ^ p.α)
```

and

```lean
def paperWaveOperator (p : CMParams) (c : ℝ) (q W : ℝ → ℝ) : ℝ → ℝ :=
  fun x =>
    let V := frozenElliptic p q
    iteratedDeriv 2 W x + c * deriv W x
      - p.χ * p.m * (W x) ^ (p.m - 1) * deriv V x * deriv W x
      + W x *
          (1 - p.χ * (W x) ^ (p.m - 1) * V x
            - ((W x) ^ p.α - p.χ * (W x) ^ (p.m + p.γ - 1)))
```

For `χ ≤ 0`, the latter expands to

```text
A_q(W)
 = W'' + cW'
   + h m W^(m-1) V' W'
   + W + h W^m V
   - W^(1+α)
   - h W^(m+γ).                         (1)
```

The last term is the favorable term in the question.

By contrast, expansion of the actual divergence-form operator gives

```text
F_q(W)
 = W'' + cW'
   + h m W^(m-1) V' W'
   + W + h W^m V
   - h W^m q^γ
   - W^(1+α).                           (2)
```

The two agree only on the diagonal `q = W`. The repo records their exact difference as

```lean
paperWaveOperator p c q W x =
  frozenWaveOperator p c q W x
    + p.χ * (W x) ^ p.m * ((W x) ^ p.γ - (q x) ^ p.γ)
```

in `paperWaveOperator_eq_frozenWaveOperator_add_offdiag`, and records diagonal equality in

```lean
paperWaveOperator_eq_frozenWaveOperator_at_fixed_point
```

This is why the relaxed proof must live on the paper-expanded route.

## 1.1 The elliptic drift estimate

Assume the frozen profile is trapped:

```text
0 ≤ q(y) ≤ min(1, exp(-κy)).
```

In particular `q(y) ≤ exp(-κy)` for every `y`, including negative `y`, because there `exp(-κy) ≥ 1`. Hence

```text
q(y)^γ ≤ exp(-γκy).
```

For the normalized resolvent

```text
V(x) = (1/2) ∫_ℝ exp(-|x-y|) q(y)^γ dy,
```

split at `y=x`:

```text
V(x)
 = (1/2) e^{-x} ∫_{-∞}^x e^y q(y)^γ dy
   + (1/2) e^x ∫_x^∞ e^{-y} q(y)^γ dy,

V'(x)
 = -(1/2) e^{-x} ∫_{-∞}^x e^y q(y)^γ dy
   + (1/2) e^x ∫_x^∞ e^{-y} q(y)^γ dy.
```

Therefore

```text
V(x) - mκ V'(x)
 = (1/2)(1+mκ)e^{-x} ∫_{-∞}^x e^y q(y)^γ dy
   + (1/2)(1-mκ)e^x ∫_x^∞ e^{-y} q(y)^γ dy.       (3)
```

The condition `mκ ≤ 1` makes both coefficients nonnegative. If also `γκ < 1`, then

```text
∫_{-∞}^x e^y q(y)^γ dy
  ≤ ∫_{-∞}^x e^{(1-γκ)y} dy
  = e^{(1-γκ)x}/(1-γκ),

∫_x^∞ e^{-y} q(y)^γ dy
  ≤ ∫_x^∞ e^{-(1+γκ)y} dy
  = e^{-(1+γκ)x}/(1+γκ).
```

Substitution into (3) gives

```text
V - mκV'
 ≤ (1/2) [ (1+mκ)/(1-γκ) + (1-mκ)/(1+γκ) ] e^{-γκx}
 = (1 + mγκ²)/(1 - γ²κ²) e^{-γκx}.                (4)
```

This is the only genuinely analytic estimate required by the relaxed upper-barrier lemma. Everything after (4) is scalar algebra and case splitting.

## 1.2 Exponential branch

On the strict exponential branch of `upperBarrier κ 1`, set

```text
W = E = e^{-κx},   0 < E < 1.
```

Choose `κ` to solve

```text
κ² - cκ + 1 = 0,
```

or equivalently

```text
c = κ + κ⁻¹.
```

Then

```text
E'' + cE' + E = 0.
```

Plugging `W=E` into (1) gives the exact residual

```text
A_q(E)
 = h E^m (V - mκV')
   - E^(1+α)
   - h E^(m+γ).                                    (5)
```

Using (4), with

```text
Cκ := (1 + mγκ²)/(1 - γ²κ²),
```

we obtain

```text
A_q(E)
 ≤ h Cκ E^(m+γ) - E^(1+α) - h E^(m+γ).             (6)
```

The negative-branch exponent assumption is

```text
α ≤ m + γ - 1,
```

so

```text
1 + α ≤ m + γ.
```

Because `0 < E ≤ 1`, larger exponents give smaller powers, hence

```text
E^(m+γ) ≤ E^(1+α).
```

Consequently

```text
A_q(E)
 ≤ [h Cκ - (1+h)] E^(m+γ).                         (7)
```

Thus the exponential branch is a supersolution under exactly

```text
h Cκ ≤ 1+h,
```

that is,

```text
|χ| (1 + mγκ²)/(1 - γ²κ²) ≤ 1 + |χ|.              (8)
```

This is where the current stronger budget loses one full `|χ|`: dropping the favorable `-hE^(m+γ)` from (5) changes (7) to

```text
[h Cκ - 1] E^(m+γ),
```

which requires `h Cκ ≤ 1`.

## 1.3 Constant branch

On the strict constant branch, `W=1`, `W'=W''=0`. The paper-expanded residual is

```text
A_q(1)
 = h(V-1).                                         (9)
```

The trap gives `0 ≤ q ≤ 1`; positivity and unit mass of the elliptic kernel give

```text
0 ≤ V_q ≤ 1.
```

Hence (9) is nonpositive. This is already covered by the repo theorem

```lean
paperWaveOperator_upperBarrier_const_region_nonpos_neg
```

specialized to `M = 1`.

Notice that this uses only `V_q ≤ 1`. It does **not** require the much stronger pointwise comparison `V_q ≤ q^γ` carried by the current divergence-form `whole_line_super_barrier`.

## 1.4 Interface

At the interface `e^{-κx}=1` (for the unshifted barrier, `x=0`), the repo treats the nonsmooth minimum using Mathlib's total `deriv`: the first and second derivatives of the barrier evaluate to zero at the kink. For `paperWaveOperator`, the drift term also vanishes because it contains `W'`. Thus the residual is again exactly

```text
A_q(1) = h(V_q-1) ≤ 0.                              (10)
```

This interface lemma is substantially simpler than the current

```lean
frozenWaveOperator_upperBarrier_interface_nonpos
```

because the paper-expanded operator does not differentiate the kinked product `W^m V'` at the interface.

Combining the exponential, interface, and constant cases proves the whole-line paper supersolution.

---

# 2. Where `c > cStarLower p` enters

Define

```text
Θ := mγ|χ| + γ²|χ| + γ²
   = |χ|mγ + (1+|χ|)γ².                            (11)
```

The repo definitions are

```lean
def cStarLower (p : CMParams) : ℝ :=
  max (1 / p.m + p.m)
    (1 / Real.sqrt
        (p.m * p.γ * |p.χ| + p.γ ^ 2 * |p.χ| + p.γ ^ 2)
      + Real.sqrt
        (p.m * p.γ * |p.χ| + p.γ ^ 2 * |p.χ| + p.γ ^ 2))

def kappa (c : ℝ) : ℝ :=
  (c - Real.sqrt (c ^ 2 - 4)) / 2
```

For `c>2`, `κ(c)` is the smaller positive root of

```text
r² - cr + 1 = 0.
```

The other positive root is `κ(c)⁻¹`; equivalently the spatial characteristic roots for `U''+cU'+U=0` are

```text
-κ(c),  -κ(c)⁻¹.
```

The repo already has:

```lean
cStarLower_ge_two

two_lt_of_cStarLower_lt

kappa_pos_of_cStarLower_lt

kappa_lt_one_of_cStarLower_lt

kappa_add_inv_eq_of_cStarLower_lt

kappa_strictAntiOn
```

The two entries in `cStarLower` perform two distinct jobs.

## 2.1 The `m + 1/m` entry

Since `m ≥ 1`, the speed corresponding to the trial root `1/m` is

```text
1/m + m.
```

Because `r ↦ r+r⁻¹` is strictly decreasing on `(0,1)`,

```text
c > m + 1/m
```

implies

```text
κ(c) < 1/m,
```

hence

```text
mκ(c) < 1.                                         (12)
```

This makes the coefficient `1-mκ` in the second half of (3) nonnegative.

## 2.2 The `sqrt Θ + 1/sqrt Θ` entry

The second speed entry is the speed corresponding to the trial root `1/sqrt Θ`. Since `m,γ ≥ 1`, we have `Θ ≥ γ² ≥ 1`. Therefore

```text
c > sqrt Θ + 1/sqrt Θ
```

implies

```text
κ(c) < 1/sqrt Θ,
```

and hence

```text
Θ κ(c)² < 1.                                       (13)
```

Because `Θ ≥ γ²`, (13) gives

```text
γκ(c) < 1,
```

so

```text
1 - γ²κ(c)² > 0.                                   (14)
```

This is the exact denominator-positivity point.

Moreover, after multiplying (8) by the positive denominator, (8) is algebraically equivalent to

```text
|χ|(1+mγκ²) ≤ (1+|χ|)(1-γ²κ²)
```

and then to

```text
[|χ|mγ + (1+|χ|)γ²] κ² ≤ 1,
```

namely

```text
Θκ² ≤ 1.                                           (15)
```

Thus (13) proves the relaxed scalar condition, in fact strictly.

## 2.3 Admissible root range

For `c > cStarLower p`, the useful consolidated range is

```text
0 < κ(c) < min(1/m, 1/sqrt Θ) ≤ 1,
```

and therefore

```text
mκ(c) < 1,
γκ(c) < 1,
1 - γ²κ(c)² > 0,
c = κ(c) + κ(c)⁻¹.
```

For a lower-barrier correction exponent `κtilde` in the paper's interval

```text
κ < κtilde ≤ min((1+α)κ, mκ+1/2, 1),
```

one also has the root ordering

```text
κ < κtilde ≤ 1 < κ⁻¹,
```

and hence

```text
c κtilde - κtilde² - 1
 = (κtilde-κ)(κ⁻¹-κtilde) > 0.
```

That is the denominator used by the lower-subsolution calculation; it is separate from, but compatible with, the upper-barrier denominator `1-γ²κ²`.

---

# 3. Does this cover every `χ ≤ 0`?

Yes, with the paper's speed condition. There is no amplitude restriction such as `|χ| < C`.

Let `h=|χ|`. Then

```text
Θ = hγ(m+γ) + γ².
```

As `h → ∞`,

```text
sqrt Θ ~ sqrt(h γ(m+γ)),

cStarLower p ~ sqrt(h γ(m+γ)),

κ(c) < 1/sqrt Θ = O(h^{-1/2})
```

for admissible speeds. Therefore

```text
Θκ² < 1
```

continues to hold, and this is exactly the relaxed barrier condition.

The honest nuance is that the favorable term does **not** make a fixed speed work uniformly for arbitrarily large `|χ|`. For fixed `κ>0`,

```text
Cκ = (1+mγκ²)/(1-γ²κ²) > 1,
```

so

```text
h Cκ ≤ 1+h
```

fails when `h` is sufficiently large. The theorem avoids this because the allowed speed grows with `|χ|`, forcing `κ` down like `|χ|^{-1/2}`.

So the correct statement is:

```text
for every χ ≤ 0 and every c > cStarLower(χ,m,γ),
the M=1 paper upper barrier is valid.
```

It is not:

```text
for one fixed c>2, the same barrier works for all χ≤0.
```

This matches the headline negative branch and the asymptotic scale of `cStarLower`.

---

# 4. Minimal Lean-4 implementation route

## 4.1 Do not mutate the current frozen theorem

The following direct edit is wrong:

```diff
 theorem whole_line_super_barrier
-  (hMbound : coeff ≤ 1)
+  (hMbound : coeff ≤ 1 + |p.χ|)
   ... : ∀ x, frozenWaveOperator ... ≤ 0
```

The conclusion is still about `frozenWaveOperator`, which has `-|χ|W^m q^γ`, not `-|χ|W^(m+γ)`. The favorable term needed by the relaxed budget is absent off diagonal.

Keep `whole_line_super_barrier` for any route that genuinely needs the divergence-form frozen operator. Add a paper-side theorem instead.

## 4.2 Existing lemmas to reuse

The following are already present and directly wireable:

```lean
-- Definitions / characteristic root
cStarLower
kappa
cStarLower_ge_two
two_lt_of_cStarLower_lt
kappa_pos_of_cStarLower_lt
kappa_lt_one_of_cStarLower_lt
kappa_add_inv_eq_of_cStarLower_lt
kappa_strictAntiOn

-- Trap and resolver bounds
InWaveTrapSet.le_exp
InWaveTrapSet.rpow_le_exp
InWaveTrapSet.rpow_le_exp_mul
frozenElliptic_le_M_of_inWaveTrapSet
frozenElliptic_le_rpow_of_inWaveTrapSet

-- Exact paper-operator exponential identity
paperWaveOperator_upperBarrier_exp_region_eq_of_kappa_speed
paperWaveOperator_upperBarrier_exp_region_nonpos_of_dominance

-- Constant branch
paperWaveOperator_upperBarrier_const_region_nonpos_neg

-- Kink arithmetic already proved for upperBarrier
upperBarrier_eq_M_at_interface
upperBarrier_deriv_eq_zero_at_interface
upperBarrier_iteratedDeriv_two_eq_zero_at_interface

-- Final diagonal conversion
paperWaveOperator_eq_frozenWaveOperator_add_offdiag
paperWaveOperator_eq_frozenWaveOperator_at_fixed_point
FrozenStationaryWaveProfile.mk_from_paper_stationarity

-- Existing paper-Rothe consumer
PerStepBoxParams.basePaperSuper
```

`PerStepBoxParams.basePaperSuper` already consumes the paper-side hook

```lean
paperUpperBarrier_super_of_scalar
```

through its `hbarrierScalar : PaperUpperBarrierSuperScalarConditions ...` field. The least invasive integration is therefore either:

1. add a negative-`M=1` constructor for `PaperUpperBarrierSuperScalarConditions` using the relaxed theorem below; or
2. add a specialized theorem `PerStepBoxParams.basePaperSuper_neg_one_of_cStarLower_lt` and leave the existing generic scalar package untouched.

## 4.3 New lemma DAG

### Lemma A — the resolver drift combination

This is the **single hardest analytic leaf**.

```lean
/-- Paper equations (4.3)--(4.4), normalized and specialized to M=1. -/
theorem frozenElliptic_sub_mkappa_deriv_le
    (p : CMParams) {κ : ℝ} {q : ℝ → ℝ}
    (hκ : 0 < κ)
    (hγκ : p.γ * κ < 1)
    (hmκ : p.m * κ ≤ 1)
    (hq : InWaveTrapSet κ 1 q) (x : ℝ) :
    frozenElliptic p q x - p.m * κ * deriv (frozenElliptic p q) x ≤
      ((1 + p.m * p.γ * κ ^ 2) /
        (1 - p.γ ^ 2 * κ ^ 2)) *
        (expDecay κ x) ^ p.γ := by
  -- unfold frozenElliptic/Psi;
  -- split the kernel integral at x;
  -- use q^γ ≤ exp(-γκ·);
  -- integrate the two exponentials;
  -- combine the fractions.
```

A useful proof decomposition is:

```lean
lemma frozenElliptic_sub_mkappa_deriv_eq_split_integrals ...
lemma left_kernel_source_integral_le_exp ...
lemma right_kernel_source_integral_le_exp ...
lemma resolver_drift_coefficient_identity ...
```

The coefficient identity is purely `field_simp`/`ring` once `1-γκ>0` and `1+γκ>0` are available.

### Lemma B — exact negative-χ residual on the exponential branch

```lean
theorem paperWaveOperator_upperBarrier_exp_region_eq_neg
    (p : CMParams) {c κ : ℝ} {q : ℝ → ℝ}
    (hχ : p.χ ≤ 0) (hκ : κ ≠ 0)
    (hc : c = κ + κ⁻¹)
    {x : ℝ} (hx : Real.exp (-κ * x) < 1) :
    paperWaveOperator p c q (upperBarrier κ 1) x =
      |p.χ| * (expDecay κ x) ^ p.m *
          (frozenElliptic p q x -
            p.m * κ * deriv (frozenElliptic p q) x)
        - (expDecay κ x) ^ (1 + p.α)
        - |p.χ| * (expDecay κ x) ^ (p.m + p.γ) := by
  -- rewrite with
  -- paperWaveOperator_upperBarrier_exp_region_eq_of_kappa_speed;
  -- use abs_of_nonpos hχ and rpow_add for the positive exponential;
  -- ring.
```

This is mechanical and isolates the favorable term in exactly the shape needed downstream.

### Lemma C — relaxed exponential supersolution

```lean
theorem paperWaveOperator_upperBarrier_exp_region_nonpos_neg_relaxed
    (p : CMParams) {c κ : ℝ} {q : ℝ → ℝ}
    (hχ : p.χ ≤ 0)
    (hα : p.α ≤ p.m + p.γ - 1)
    (hκ : 0 < κ)
    (hγκ : p.γ * κ < 1)
    (hmκ : p.m * κ ≤ 1)
    (hc : c = κ + κ⁻¹)
    (hq : InWaveTrapSet κ 1 q)
    (hcoef :
      |p.χ| *
          ((1 + p.m * p.γ * κ ^ 2) /
            (1 - p.γ ^ 2 * κ ^ 2)) ≤
        1 + |p.χ|)
    {x : ℝ} (hx : Real.exp (-κ * x) < 1) :
    paperWaveOperator p c q (upperBarrier κ 1) x ≤ 0 := by
  -- use Lemma B;
  -- multiply Lemma A by |χ| * E^m;
  -- prove E^(m+γ) ≤ E^(1+α) from E≤1 and 1+α≤m+γ;
  -- finish by nlinarith/ring normalization.
```

### Lemma D — interface

```lean
theorem paperWaveOperator_upperBarrier_interface_nonpos_neg_one
    (p : CMParams) {c κ : ℝ} {q : ℝ → ℝ}
    (hχ : p.χ ≤ 0) (hκ : 0 < κ)
    (hq : InWaveTrapSet κ 1 q)
    {x : ℝ} (hx : Real.exp (-κ * x) = 1) :
    paperWaveOperator p c q (upperBarrier κ 1) x ≤ 0 := by
  have hV : frozenElliptic p q x ≤ 1 := by
    simpa using
      frozenElliptic_le_M_of_inWaveTrapSet p
        (M := (1 : ℝ)) one_pos le_rfl hq x
  -- rewrite the kink value/derivatives using the existing WaveSuperBarrier lemmas;
  -- the residual becomes |χ| * (V-1).
```

### Lemma E — whole-line paper barrier

```lean
theorem whole_line_paper_super_barrier_neg_one
    (p : CMParams) {c κ : ℝ} {q : ℝ → ℝ}
    (hχ : p.χ ≤ 0)
    (hα : p.α ≤ p.m + p.γ - 1)
    (hκ : 0 < κ) (hκ1 : κ < 1)
    (hγκ : p.γ * κ < 1)
    (hmκ : p.m * κ ≤ 1)
    (hc : c = κ + κ⁻¹)
    (hcoef :
      |p.χ| *
          ((1 + p.m * p.γ * κ ^ 2) /
            (1 - p.γ ^ 2 * κ ^ 2)) ≤
        1 + |p.χ|)
    (hq : InWaveTrapSet κ 1 q) :
    ∀ x, paperWaveOperator p c q (upperBarrier κ 1) x ≤ 0 := by
  intro x
  rcases lt_trichotomy (Real.exp (-κ * x)) 1 with hExp | hEq | hConst
  · exact paperWaveOperator_upperBarrier_exp_region_nonpos_neg_relaxed
      p hχ hα hκ hγκ hmκ hc hq hcoef hExp
  · exact paperWaveOperator_upperBarrier_interface_nonpos_neg_one
      p hχ hκ hq hEq
  · exact paperWaveOperator_upperBarrier_const_region_nonpos_neg
      p hχ hα hκ (by norm_num) hq hConst
```

No `hsrc` is present.

### Lemma F — scalar condition from the speed threshold

Introduce the exact radicand already used in `cStarLower`:

```lean
def negBarrierTheta (p : CMParams) : ℝ :=
  p.m * p.γ * |p.χ| + p.γ ^ 2 * |p.χ| + p.γ ^ 2
```

Then prove one arithmetic/root package:

```lean
theorem negBarrierData_of_cStarLower_lt
    (p : CMParams) {c : ℝ} (hc : cStarLower p < c) :
    let κ := kappa c
    0 < κ ∧
    κ < 1 ∧
    p.m * κ < 1 ∧
    p.γ * κ < 1 ∧
    0 < 1 - p.γ ^ 2 * κ ^ 2 ∧
    c = κ + κ⁻¹ ∧
    |p.χ| *
        ((1 + p.m * p.γ * κ ^ 2) /
          (1 - p.γ ^ 2 * κ ^ 2)) ≤
      1 + |p.χ| := by
  -- κ positivity / κ<1 / c=κ+κ⁻¹: existing lemmas.
  -- c > m+1/m      -> κ<1/m.
  -- c > sqrt Θ+1/sqrt Θ -> κ<1/sqrt Θ.
  -- derive Θκ²<1 and rewrite it into the final fraction inequality.
```

The `m=1` and `Θ=1` boundary cases can be handled separately; otherwise use `kappa_strictAntiOn` together with `kappa_eq_of_pos_lt_one_kappa_speed` at the comparison roots `1/m` and `1/sqrt Θ`. This lemma is arithmetic engineering, not new PDE analysis.

### Lemma G — direct headline-ready wrapper

```lean
theorem whole_line_paper_super_barrier_neg_one_of_cStarLower_lt
    (p : CMParams) {c : ℝ} {q : ℝ → ℝ}
    (hα : p.α ≤ p.m + p.γ - 1)
    (hχ : p.χ ≤ 0)
    (hc : cStarLower p < c)
    (hq : InWaveTrapSet (kappa c) 1 q) :
    ∀ x,
      paperWaveOperator p c q (upperBarrier (kappa c) 1) x ≤ 0 := by
  obtain ⟨hκ, hκ1, hmκ, hγκ, _hden, hspeed, hcoef⟩ :=
    negBarrierData_of_cStarLower_lt p hc
  exact whole_line_paper_super_barrier_neg_one
    p hχ hα hκ hκ1 hγκ hmκ.le hspeed.symm hcoef hq
```

Adjust the orientation of `hspeed` to match the chosen statement (`c = κ+κ⁻¹` versus its symmetric equality).

## 4.4 Downstream wiring

The dependency order is:

```text
A  resolver drift estimate                         [hard analytic leaf]
   ↓
B  exact paper residual with -|χ|E^(m+γ)          [mechanical]
   ↓
C  relaxed exponential branch                      [mechanical]

D  paper interface branch                          [short]
existing paper constant branch                     [already proved]
   \        |        /
    E  whole-line paper upper barrier               [case split]

F  cStarLower -> κ/root/scalar package              [arithmetic]
   ↓
G  whole-line barrier from c > cStarLower           [wrapper]
   ↓
PaperUpperBarrierSuperScalarConditions constructor
or specialized PerStepBoxParams.basePaperSuper
   ↓
paper Rothe step / lower-pinned Schauder construction
   ↓
outer fixed point q = W
   ↓
paperWaveOperator_eq_frozenWaveOperator_at_fixed_point
   ↓
FrozenStationaryWaveProfile.mk_from_paper_stationarity
```

The repo already has the final diagonal bridge, so using `paperWaveOperator` during the frozen iteration does not weaken the traveling-wave conclusion.

## Hardest step

The genuine mathematical leaf is Lemma A, the split-kernel estimate (4). It is bounded and self-contained: two explicit exponential integrals plus fraction algebra. It does not require new compactness, Schauder, or maximum-principle theory.

Everything else in this barrier correction is a small Lean layer:

* one operator normalization lemma;
* one power comparison on `0<E≤1`;
* one kink evaluation;
* one three-way case split;
* one characteristic-root arithmetic wrapper.

So this correction is a **bounded one-leaf build**, not a new multi-week formalization. It fixes the scalar obstruction only on the correct paper-expanded construction route; the remaining Rothe/Schauder residuals elsewhere in the repo are independent of this barrier calculation.
