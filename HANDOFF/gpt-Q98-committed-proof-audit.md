ANSWER Q98 aeefa925

# Executive verdict

PASS for the theorem actually stated at commit 338b8f866e4b9edd18832547becd809e03a01a69. I found no vacuity in the seed, no direction reversal or formal stalling in the successor, no missing finiteness premise in the affine endgame, no eventual/all-time mix-up, and no co-moving/laboratory-frame confusion.

There is, however, one statement-scope caveat: Proposition12PositiveBranchCritical carries WholeLineCauchyCeilingRegime p explicitly. In the positive critical branch that predicate includes p.χ < chiStar p. The paper-facing Proposition12PositiveBranch only records 0 < χ < 1/2 and m+γ-1 ≤ α. Thus the committed theorem is a correct, non-vacuous restricted critical theorem, but it does not by itself close every parameter point in the paper's raw critical χ < 1/2 range.

Audit target: 338b8f86.

# PASS/FAIL summary

# 1. Seed rectangle: no vacuity

The rectangle stores both strict margins:

```javascript
structure ChiPosWholeLineRectangle
    (p : CMParams) (u : ℝ → ℝ → ℝ) where
  ell : ℝ
  M : ℝ
  start : ℝ
  ell_pos : 0 < ell
  ell_lt_one : ell < 1
  one_lt_M : 1 < M
  floor_margin : 0 < chiPosFloorGap p M ell
  ceiling_margin : 0 < chiPosCeilingGap p ell M
  bounds : ∀ t, start ≤ t → ∀ x, ell ≤ u t x ∧ u t x ≤ M
```

See WholeLineChiPosRectangleSqueeze.lean:29-39.

The gaps are exactly

```javascript
chiPosFloorGap p M ell =
  1 - ell^α - χ * ell^(m-1) * (M^γ - ell^γ)

chiPosCeilingGap p ell M =
  M^α - 1 - χ * M^(m-1) * (M^γ - ell^γ)
```

from WholeLineChiPosRectangleTargets.lean:24-32.

## General satisfiability argument

At the critical exponent α=m+γ-1:

```plain text
floorGap(M,x)
  = 1 - (1-χ)x^α - χ M^γ x^(m-1),

ceilingGap(ell,M)
  = (1-χ)M^α + χ ell^γ M^(m-1) - 1.
```

For the ceiling margin, M>MChi gives

```plain text
(1-χ) M^α > (1-χ) MChi^α = 1,
```

so ceilingGap(ell,M)>0 for every ell≥0.

For the floor margin:

- If m>1, then x^(m-1)→0 and x^α→0 as x↓0, so floorGap(M,x)→1. A small positive x works for any fixed finite M.

- If m=1, the zero-floor limit is 1-χM^γ. The seed first chooses M>MChi sufficiently close to MChi so that χM^γ<1. At criticality, α=γ, and

This is implemented, without assuming the margins, in:

- chi_mul_MChi_rpow_gamma_lt_one_of_m_eq_one,

- exists_M_gt_MChi_with_m_one_margin,

- exists_ell_with_positive_rectangle_floor_margin, and

- exists_chiPos_rectangle_seed

at WholeLineChiPosRectangleSeed.lean:21-195.

## Concrete requested example

Take

```plain text
m = γ = α = 1,
χ = 1/4,
‖u₀‖ = 2,
inf u₀ = 1/10.
```

Then

```plain text
MChi = 1/(1-χ) = 4/3.
```

Choose the perfectly explicit algebraic seed values

```plain text
M = 3/2,
ellRaw = 1/2,
ell = ellRaw/2 = 1/4.
```

The exceptional m=1 condition is satisfied:

```plain text
χ M^γ = (1/4)(3/2) = 3/8 < 1.
```

The raw floor margin is

```plain text
floorGap(3/2,1/2)
 = 1 - 1/2 - (1/4)(3/2-1/2)
 = 1/4 > 0.
```

The final seed rectangle has both margins:

```plain text
floorGap(3/2,1/4)
 = 1 - 1/4 - (1/4)(3/2-1/4)
 = 7/16 > 0,

ceilingGap(1/4,3/2)
 = 3/2 - 1 - (1/4)(3/2-1/4)
 = 3/16 > 0.
```

So the two strict fields are not merely abstractly compatible; this concrete parameter/data profile admits a simple explicit pair.

## The initial datum being above M is handled correctly

Here ‖u₀‖=2>M=3/2. The proof does not assume the seed ceiling from time zero.

It sets

```plain text
G = max(MChi,‖u₀‖) = 2,
C₀ = (inf u₀)/2 = 1/20,
```

and preserves a positive floor through the finite burn-in using

```plain text
chiPosDecayFloorRate
 = χ G^(m-1) G^γ + G^α + 1
 = (1/4)*1*2 + 2 + 1
 = 7/2.
```

Thus the crude floor remains

```plain text
C₀ exp(-(7/2)s) > 0
```

at every finite time. Only after the already-proved eventual ceiling has entered u≤M does the proof restart the increasing seed floor. This division is explicit in WholeLineChiPosRectangleSqueeze.lean:508-724:

1. preserve C₀ exp(-rate s) under the global bound G;

1. use UniformLimsupLe MChi to obtain Tupper with u≤M after Tupper;

1. set t₁=max Tupper t₀;

1. take a still-positive C₁ from the decayed floor;

1. grow from C₁ toward ellRaw under the sharper ceiling M;

1. begin the rectangle when the barrier has crossed ellRaw/2.

The burn-in may be quantitatively long when C₁ is tiny, but it is finite. Proposition 1.2 only needs an existential entry time.

# 2. Successor construction: strict improvement and exact budgets

The successor theorem is exists_next_chiPosWholeLineRectangle.

Its scalar producer exists_chiPos_rectangle_round_targets returns

```javascript
ell < L < Lraw ≤ 1,
1 ≤ Araw < A < M,
0 < floorGap M Lraw,
floorGap M L ≤ δ,
0 < ceilingGap L Araw,
ceilingGap L A ≤ δ,
0 < floorGap A L,
0 < ceilingGap L A.
```

See WholeLineChiPosRectangleTargets.lean:320-402.

The direction is correct:

- The floor barrier starts at old.ell and increases toward Lraw; the proof waits until it is above the finite-time bound L.

- Only then is the ceiling comparison restarted.

- The ceiling barrier starts at old.M and decreases toward Araw; the proof waits until it is below the finite-time bound A.

- The new rectangle is exactly [L,A].

The final subtype is constructed with

```javascript
ell_le := targets.ell_lt_L.le
M_le := targets.A_lt_M.le
floor_budget := targets.floor_delta
ceiling_budget := targets.ceiling_delta
```

at the end of WholeLineChiPosRectangleSqueeze.lean:468-496.

Therefore the concrete constructor is stronger than the ChiPosWholeLineRectangleStep interface: it gives strict endpoint improvement even though the step structure stores only ≤.

## Concrete successor witness

Continue the example from the seed rectangle

```plain text
old.ell = 1/4,
old.M = 3/2,
δ = 1/100.
```

For m=γ=α=1, χ=1/4, the floor residual under the old ceiling is

```plain text
f(x) = 1 - x - (1/4)(3/2-x)
     = 5/8 - 3x/4.
```

Choose

```plain text
L = 33/40 = 0.825,
Lraw = 83/100 = 0.83.
```

Then

```plain text
f(L)    = 1/160 = 0.00625 ≤ δ,
f(Lraw) = 1/400 = 0.0025 > 0.
```

With the new floor L, the ceiling residual is

```plain text
g(A) = A - 1 - (1/4)(A-L)
     = 3A/4 + L/4 - 1.
```

Choose

```plain text
Araw = 53/50 = 1.06,
A    = 213/200 = 1.065.
```

Then

```plain text
g(Araw) = 1/800 > 0,
g(A)    = 1/200 = 0.005 ≤ δ,
```

and

```plain text
1/4 < 33/40,
213/200 < 3/2.
```

The next floor margin is also strict:

```plain text
floorGap(A,L)
 = 1 - 33/40 - (1/4)(213/200-33/40)
 = 23/200 > 0.
```

Thus this step genuinely changes both endpoints from [0.25,1.5] to [0.825,1.065].

## Why arbitrarily small endpoint changes cannot make the formal iteration stall

The proof does not infer contraction from the endpoint changes alone. It feeds the two budget inequalities into chiPos_squeeze_gap_step:

```plain text
newGap ≤ 2χ * oldGap + 2δ.
```

See WholeLineChiPosSqueezeAlgebra.lean:52-87.

In the numerical step,

```plain text
oldGap = 3/2 - 1/4 = 5/4,
newGap = 213/200 - 33/40 = 6/25,
2χ oldGap + 2δ = (1/2)(5/4) + 1/50 = 129/200.
```

Indeed 6/25 < 129/200.

If a chosen successor moved only slightly, it would still have to satisfy the two near-root budgets. Those budgets, not a hidden monotonicity assumption, force the affine gap estimate. Consequently there is no formal path that repeatedly chooses a non-improving rectangle while evading contraction.

# 3. Endgame recurrence and epsilon quantifiers

The endgame is uniformConvergesToConstant_one_of_rectangle_successors.

It sets

```javascript
r := 2 * p.χ
δ := epsilon * (1-r) / 4
```

so the recurrence defect is c=2δ, and

```plain text
c/(1-r) = 2δ/(1-r) = epsilon/2 < epsilon.
```

It then obtains an index from

```javascript
exists_index_affine_recurrence_lt
```

whose exact statement is:

```javascript
theorem exists_index_affine_recurrence_lt
    {g : ℕ → ℝ} {r c epsilon : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hc : 0 ≤ c)
    (hstep : ∀ k, g (k + 1) ≤ r * g k + c)
    (hepsilon : c / (1 - r) < epsilon) :
    ∃ n, g n < epsilon
```

at WholeLineChiPosAffineIteration.lean:17-32.

## No extra gap₀ finiteness hypothesis is needed

g : ℕ → ℝ, not ℝ≥0∞. Therefore g 0 is an ordinary finite real by type. The proof uses

```plain text
r^n * g(0) → 0,
```

which holds for every real constant g(0) when 0≤r<1.

Moreover, the rectangle fields imply actual nonnegativity:

```plain text
0 < ell < 1 < M,
α ≥ 1,
```

so ell^α ≤ 1 ≤ M^α and hence

```plain text
gap n = M_n^α - ell_n^α ≥ 0.
```

This nonnegativity is mathematically available even though exists_index_affine_recurrence_lt does not require it.

## Quantifier order is exactly right

The definition is

```javascript
def UniformConvergesToConstant (u : ℝ → ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ T, ∀ t x, T ≤ t → |u t x - a| < ε
```

at Statements.lean:188-189.

The proof performs:

```javascript
intro epsilon hepsilon
-- choose δ, the successor function, and n depending on epsilon
refine ⟨(rectangles n).start, ?_⟩
intro t x ht
...
```

Thus the result is precisely

```plain text
∀ ε>0, ∃ T(ε), ∀ t≥T(ε), ∀ x, |u(t,x)-1|<ε.
```

There is no swapped x/T quantifier and no merely subsequential convergence.

# 4. Eventual versus all-time bounds, and frame audit

## Successor timeline

The old rectangle only guarantees bounds for t≥old.start. The successor immediately chooses

```javascript
t₀ := max old.start 1,
```

so every use of the old upper bound occurs inside its valid tail.

The floor barrier is valid for all restart times s≥0. After it eventually exceeds L, the proof chooses sfloor≥0 and restarts the ceiling at

```plain text
t₁ = t₀ + sfloor.
```

The crucial lower bound for the ceiling restart is proved for every future s≥0 by evaluating the old floor barrier at sfloor+s:

```plain text
L ≤ floorBarrier(sfloor+s)
  ≤ floorData.q(sfloor+s,x)
  = ceilingData.q(s,x).
```

This is the key block in WholeLineChiPosRectangleSqueeze.lean:398-416. It is exactly the ordering needed for the resolver lower bound during the entire ceiling comparison.

After the ceiling barrier eventually drops below A, the new rectangle starts at t₁+sceiling. No estimate is back-propagated to earlier times.

## Seed timeline

The seed similarly separates:

- the all-time static bound G=max(MChi,‖u₀‖);

- a crude decaying floor valid during burn-in;

- the eventual sharper ceiling M>MChi;

- a new restart after both are available.

The proof never applies the eventual u≤M statement before Tupper.

## Laboratory frame, not co-moving frame

WholeLineChiPosCanonicalRestartData states

```javascript
eq_global : q s x = wholeLineCauchyGlobalU p u₀ (t₀+s) x
```

for s≥0, and its time operator is

```javascript
paperWaveOperator p 0 (q s) (q s) x.
```

See WholeLineChiPosCanonicalRestartNatural.lean:23-34 and :97-163.

There is no x+c t or x-c t translation anywhere in the rectangle. This is correct: Proposition 1.2 concerns uniform stabilization of the Cauchy solution to the spatial constant 1 in the laboratory frame.

# 5. Weighted resolver comparison audit

The requested file WholeLineChiPosWeightedResolverComparisonNatural.lean proves a half-line comparison. Its critical source estimate is mathematically sound:

1. q,b ∈ [0,M] gives the Lipschitz estimate

1. V-q^γ ≤ Dup and Dup≥0 give

1. The barrier hypothesis

1. The remaining reaction and power differences are absorbed into a linear |b-q| coefficient, while the chemotactic gradient term is absorbed into K|∂x(b-q)|.

The decisive lines are the power comparison and zeroth-order estimate around WholeLineChiPosWeightedResolverComparisonNatural.lean:76-140, and the final parabolic inequality around :181-370.

### Important live-path distinction

The rectangle proof does not directly call the half-line theorem leftHalfLine_ge_of_weighted_resolver_reaction_subsolution. The live rectangle calls the whole-line comparators in WholeLineChiPosWholeLineComparisonNatural.lean through the wrappers:

```javascript
WholeLineChiPosCanonicalRestartData.ge_of_coupled_subsolution
WholeLineChiPosCanonicalRestartData.ge_of_weighted_subsolution
WholeLineChiPosCanonicalRestartData.le_of_weighted_supersolution
```

The live lower theorem retains the complete barrier gap

```plain text
χ b^m (Dup-b^γ),
```

and controls the difference

```plain text
χ[q^m(Dup-q^γ)-b^m(Dup-b^γ)]
```

with Lipschitz bounds for both s^m and s^(m+γ). See WholeLineChiPosWholeLineComparisonNatural.lean:155-461.

I found no sign reversal in either version. In particular, the proof does not use the false global implication q^m≤b^m; it pays the exact Lipschitz error away from contact.

# 6. Final proposition and target predicate

The capstone theorem is a direct concrete construction:

```javascript
theorem Proposition_1_2_positive_branch_critical :
    Proposition12PositiveBranchCritical
```

in Proposition12PositiveBranchCritical.lean:24-53.

It converts the paper BUC datum to WholeLineBUC, invokes the rectangle theorem, and packages the already-constructed canonical global Cauchy solution. There is no assumed rectangle, convergence package, or theorem projection hidden in the capstone.

UniformConvergesToConstant u 1 is the right formal target for paper equation (1.12):

```plain text
∀ε>0, eventually uniformly in x, |u(t,x)-1|<ε,
```

which is equivalent to

```plain text
‖u(t,·)-1‖∞ → 0.
```

## Statement-scope caveat

The committed critical definition is

```javascript
0 < p.χ → p.χ < 1/2 →
p.α = p.m+p.γ-1 →
WholeLineCauchyCeilingRegime p → ...
```

The regime predicate is defined in the positive critical case using

```javascript
p.χ < chiStar p ∧ p.α = p.m+p.γ-1.
```

See WholeLineCauchyGlobalBounds.lean:33-37.

This extra premise is harmless in the requested numerical example: when m=γ=1,

```plain text
chiStar = min(1,(2m+2γ)/(m²+m+2γ)) = 1.
```

But it is not automatic for arbitrary critical exponents. For example,

```plain text
m=5, γ=1, α=5, χ=2/5.
```

Then

```plain text
χ=0.4<1/2,
chiStar=min(1,12/32)=3/8=0.375,
```

so WholeLineCauchyCeilingRegime p fails. This parameter point lies in the raw χ<1/2, critical equality surface but is not covered by the committed theorem.

Therefore:

- Internal theorem correctness: PASS.

- Non-vacuity: PASS.

- Exact paper-critical coverage without an extra guard: not yet established by this theorem.

# Two most fragile points

1. The exceptional m=1 seed margin. The open room above MChi is exactly the inequality χ/(1-χ)<1, hence exactly χ<1/2. At the endpoint χ=1/2, the zero-floor margin closes and the continuity seed fails. This is correctly guarded, but it is the most parameter-sensitive algebraic point.

1. The delayed ceiling restart. The resolver lower bound for the ceiling step is valid only because the proof first waits until the floor barrier exceeds L and then proves L≤q(t,x) for all future times. The identity between floorData.q(sfloor+s) and ceilingData.q(s) is load-bearing. The current direction and timing are correct.

A close third is the weighted b^m comparison: replacing its Lipschitz four-point estimate by the unjustified global inequality q^m≤b^m would break the proof, but the committed implementation does not make that mistake.

# Final conclusion

I found no defect in the committed rectangle proof at its stated hypotheses. The seed is concretely satisfiable, the successor strictly improves both endpoints and carries the exact two defect inequalities, the affine endgame has the correct hypotheses and quantifier order, and all PDE comparisons are applied only on time intervals where their rectangle bounds are available.

The only substantive adverse finding is at the interface level: calling this the complete paper critical positive branch should be qualified until the extra WholeLineCauchyCeilingRegime premise is either derived from the paper hypotheses or removed from the canonical Cauchy construction route.