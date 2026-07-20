ANSWER Q132 83d0e733

# Adversarial audit of the χ-positive closure at 503e0855

## Verdict

One concrete statement-level defect found, in claim D only.

- A — Proposition 1.2: I found no break in the requested scalar, critical/supercritical split, or exact-equilibrium-ceiling paths.

- B — χ-positive Step 4: I found no break in the requested half-line rectangle iteration or its δ/cut quantifiers.

- C — amended Theorems 1.2 and 1.3: the displayed capstones are wired to B with the correct positive-weight window; I found no break in the requested attack lines.

- D — chiPos_stability_nonvacuous: defective as advertised. Its documentation says that it exhibits every hypothesis of the Step-4 capstone, but its theorem statement omits the two essential weight-window hypotheses

This defect does not propagate into A–C: D is an auxiliary witness theorem importing the capstones, not an input to them. It should nevertheless be fixed because its stated purpose and docstring are false.

I audited source at full commit

503e085561e3bf1d0cfd513eb2da2404974e93c8.

I did not independently rerun the 9947-job build; this is a source-level mathematical and dependency audit.

---

## 1. Scalar engine

Files:

- ShenWork/Paper1/WholeLineChiPosSqueezeAlgebra.lean:52-87

- ShenWork/Paper1/WholeLineChiPosSqueezeAlgebra.lean:127-176

- callers in WholeLineChiPosHalfLineRectangle.lean:65-74 and WholeLineChiPosSupercriticalRectangle.lean near chiPosWholeLineSupercriticalRectangleStep_gap_le

### Critical equality

Put

```plain text
β = m + γ - 1 = α,
g  = M^α - ell^α,
g' = M'^α - ell'^α.
```

The two target inequalities sum to

```plain text
g'
≤ χ ell'^(m-1)(M^γ-ell'^γ)
  + χ M'^(m-1)(M'^γ-ell'^γ)
  + 2δ.
```

For 0 < ell' ≤ 1 ≤ U, m-1 ≥ 0, γ ≥ 0,

```plain text
ell'^(m-1)(U^γ-ell'^γ)
≤ U^(m-1)(U^γ-ell'^γ)
≤ U^(m+γ-1)-ell'^(m+γ-1).
```

The second inequality is exactly the straddling-gap product lemma. Therefore

```plain text
ell'^(m-1)(M^γ-ell'^γ) ≤ M^α-ell'^α ≤ M^α-ell^α,
```

because ell ≤ ell' and α ≥ 0.

Likewise,

```plain text
M'^(m-1)(M'^γ-ell'^γ)
≤ M'^α-ell'^α
≤ M^α-ell'^α
≤ M^α-ell^α.
```

Hence

```plain text
g' ≤ 2χ g + 2δ.
```

That is independent of the Lean proof and matches chiPos_squeeze_gap_step.

### Exponent widening

For 0 < ell ≤ 1 ≤ M and β ≤ α,

```plain text
M^β ≤ M^α,
ell^α ≤ ell^β,
```

so

```plain text
M^β-ell^β ≤ M^α-ell^α.
```

This is precisely rpow_gap_mono_exponent.

The important adversarial question is whether it is called at a pair whose lower endpoint might exceed 1. It is not:

- floor side: the call is on (ell', M) and the theorem has the explicit hypothesis ell' ≤ 1;

- ceiling side: the call is on (ell', M') and the theorem has ell' ≤ 1 ≤ M';

- the half-line caller supplies new.ell_lt_one.le and new.one_lt_M.le;

- the supercritical rectangle caller supplies the same fields from the new rectangle.

So the widening is not being applied to the old floor without checking its side of 1, nor to an intermediate barrier value that could cross 1.

Verdict on attack line 1: sound. I found no hidden use of ell ≤ 1 where it can fail. The unused local fact hα1 in chiPos_squeeze_gap_step_of_le is harmless.

---

## 2. Exact equilibrium ceiling

File: ShenWork/Paper1/WholeLineChiPosEquilibriumCeiling.lean:32-121.

Let

```plain text
q = m + γ - 1,
M^α = 1 + χ M^q.
```

### Exact ceiling margin

By definition,

```plain text
chiPosCeilingGap p ell M
= M^α - 1
  - χ M^(m-1)(M^γ-ell^γ).
```

At the equilibrium,

```plain text
M^α - 1 = χ M^q = χ M^(m-1)M^γ,
```

hence

```plain text
chiPosCeilingGap p ell M
= χ M^(m-1) ell^γ.
```

This is exact; no inequality, no dropped term, and no use of q < α is needed for this identity. The Lean theorem chiPosCeilingGap_at_equilibrium is correct.

### Why M^α < 2

Assume M ≥ 1, χ < 1/2, and q < α.

If M=1, the conclusion is immediate. If M>1, then M^q < M^α, and the root equation gives

```plain text
M^α = 1 + χ M^q < 1 + χ M^α.
```

Thus

```plain text
(1-χ)M^α < 1,
M^α < 1/(1-χ) < 2.
```

The committed proof obtains the same result by contradiction.

### Critical case

The numerical conclusion also survives at q=α. Then

```plain text
(1-χ)M^α = 1,
M^α = 1/(1-χ) < 2
```

for χ<1/2.

But the committed theorem is deliberately supercritical because the selected object chiPosEquilibriumCeiling is constructed only from the supercritical intermediate-value argument. The critical branch uses the separate exact normalization MChi, with

```plain text
(MChi p)^α = 1/(1-χ).
```

I found no downstream call of chiPos_equilibrium_rpow_alpha_lt_two at q=α. Its load-bearing use is in the supercritical seed-height construction, under the strict hypothesis q<α.

Verdict on attack line 2: sound. The bound could be generalized as a scalar lemma to the critical root equation, but the current theorem and all observed callers are honestly supercritical.

---

## 3. General trap height Q

Files:

- WavePositivePlateauTrapHeight.lean:37-80

- old specialized proof in WavePositivePlateauComparison.lean:68-140

- downstream cap in WholeLineChiPosPlateauPersistence.lean:25-55

For a constant plateau d, the expanded constant operator at the critical exponent reduces to

```plain text
paperWaveOperator(..., d)
= d * [1
       - χ d^(m-1) V
       - (1-χ)d^α].
```

The general trap assumptions give

```plain text
0 < d ≤ 1,
0 ≤ V ≤ Q^γ,
χ Q^γ < 1,
(1-χ)d ≤ (1-χ Q^γ)/2.
```

Since m≥1,

```plain text
d^(m-1) ≤ 1,
χ d^(m-1)V ≤ χ Q^γ.
```

Since α≥1 and d≤1,

```plain text
d^α ≤ d,
(1-χ)d^α ≤ (1-χ)d ≤ (1-χ Q^γ)/2.
```

Therefore

```plain text
χ d^(m-1)V + (1-χ)d^α
≤ χ Q^γ + (1-χ Q^γ)/2
< 1.
```

The bracket is positive, so the constant plateau is a subsolution.

The old MChi proof used

```plain text
(MChi)^γ ≤ 1/(1-χ)
```

to manufacture the special case χ(MChi)^γ<1; it did not need the identity

```plain text
(1-χ)(MChi)^α = 1
```

inside the plateau budget. The generalized theorem replaces the special bound by the exact hypothesis it actually needs.

The critical equality α=m+γ-1 is still used: it identifies the positive diagonal power appearing in the expanded paper operator with d^α. It was not silently discarded.

Verdict on attack line 3: sound. No term was lost in passing from MChi to general Q.

---

## 4. δ, moving cuts, and quantifier order

Files:

- WholeLineChiPosHalfLineRectangle.lean:79-130

- WholeLineChiPosHalfLineSuccessor.lean:650-748

- buffer-width theorem near WholeLineChiPosHalfLineSuccessor.lean:250-311

### Per-ε choice

The endgame has the correct order:

```plain text
∀ ε>0,
  let r = 2χ,
  let δ = ε(1-r)/4,
  choose one successor function nextδ,
  iterate it finitely,
  select n with gap_n<ε.
```

For this fixed δ,

```plain text
g_{k+1} ≤ r g_k + 2δ,
2δ/(1-r) = ε/2 < ε.
```

The successor hypothesis is

```javascript
∀ δ, 0 < δ → ∀ old, Nonempty {new // Step δ old new},
```

so using one fixed δ through the entire finite iteration is legitimate.

### The cut remains finite

Each successor produces a real-valued cut satisfying

```plain text
new.cut ≤ old.cut.
```

The recurrence theorem chooses a finite natural number n. The conclusion uses only (rectangles n).cut, obtained after finitely many applications of the successor. No limit of cuts is taken and no lower bound on the infinite sequence of cuts is required. A finite composition of real-valued min, subtraction, and choice outputs remains a real number.

Thus the fact that the cuts may drift to -∞ over an infinite hypothetical iteration is irrelevant to the existential statement for each fixed ε.

### Targets before buffer width

The actual successor order is:

```plain text
old, δ
→ choose L, Lraw, Araw, A
→ choose global bound G
→ choose R from the two target-dependent tail budgets
→ choose a far-left cut supporting that R-buffer
→ run floor
→ restart
→ run ceiling.
```

This is visible in exists_next_chiPosHalfLineRectangle: targets are selected first, then R, then cut.

The order matters mathematically, not merely cosmetically. The required inequalities are

```plain text
χ Lraw^(m-1) (e^{-R}/2) G^γ
  < chiPosFloorGap p M Lraw,

χ M^(m-1) (e^{-R}/2) L^γ
  < chiPosCeilingGap p L Araw.
```

Both the coefficients and the positive margins depend on the chosen targets. Choosing R before the targets would require a uniform positive lower bound over all later target choices, which the interface does not provide. The committed order is the safe one.

After R is fixed, the far-left-buffer theorem takes

```plain text
cut = min (oldCut-(R+1)) (B-R),
```

so both cut≤oldCut and cut+R≤oldCut hold.

Verdict on attack line 4: sound. The δ quantifiers, finite stopping index, and target→R→cut order are correct.

---

## 5. Non-vacuity defect

Files:

- claimed witness: WholeLineChiPosNonvacuity.lean:45-105

- real capstone: WholeLineChiPosStabilityNatural.lean:23-46

- positive-weight construction already used correctly in Theorem13ChiPosNatural.lean:63-75

### What the witness actually states

chiPos_stability_nonvacuous existentially supplies:

```plain text
parameters, speed, eta, kappaOne, wave, datum,
regime and χ inequalities,
wave regularity/tails,
datum nonnegativity and left positivity,
WeightedL2InitialCloseness eta datum U.
```

It does not supply

```plain text
paper531RootMinus c budget.A budget.B < eta,
eta < stabilityWeightCap p.
```

Those are explicit mandatory hypotheses of

wholeLineCauchyGlobal_solution_weighted_and_uniformConvergence_chi_pos_natural.

The witness then sets

```javascript
eta := 0
```

and proves closeness by reflexivity because the datum is the wave itself.

### Why eta=0 cannot instantiate B

At a speed above the corrected threshold, the concrete budget proves

```plain text
0 < paper531RootMinus c budget.A budget.B.
```

The capstone assumption

```plain text
rootMinus < eta
```

therefore implies eta>0. With eta=0, it is impossible.

Indeed the half-line successor explicitly derives

```javascript
have heta : 0 < eta :=
  (budget.rootMinus_pos hc).trans hroot
```

before using weighted convergence to construct the far-left buffer.

So eta=0 does not merely make a norm degenerate; it is outside the admissible stability window. The zero difference makes WeightedL2InitialCloseness.refl 0 U true, but that is irrelevant because the missing root inequality cannot hold.

### Concrete repair

The repository already contains the correct construction in the uniqueness proof. Let

```javascript
let budget := paper531ConcreteStabilityBudget p hregime
```

and use

```javascript
have hroot_cap :
    paper531RootMinus c budget.A budget.B < stabilityWeightCap p :=
  (budget.cap_between c hcStar).1

obtain ⟨eta, hroot_eta, heta_cap⟩ := exists_between hroot_cap

have heta_pos : 0 < eta :=
  (budget.rootMinus_pos hcStar).trans hroot_eta
```

Then the wave-as-datum witness still has

```javascript
WeightedL2InitialCloseness.refl eta U
```

for this genuinely positive eta, because its integrand is identically zero.

The theorem statement should be strengthened to include hroot_eta and heta_cap, preferably with the concrete budget exposed, or should directly existentially instantiate the full Step-4 capstone and return its conclusion.

Verdict on attack line 5: real defect in D. A genuinely positive admissible eta is readily exhibitable; the current theorem simply failed to state and construct it.

---

## Effect on A, B, and C

### A. Proposition_1_2.unconditional

Proposition12PositiveBranchSupercritical.lean:55-67 splits

```plain text
m+γ-1 ≤ α
```

into strict supercritical and equality critical cases. The strict branch constructs the explicit supercritical ceiling regime; the equality branch constructs the critical MChi regime. The scalar widening lemma is called only with straddling rectangles.

I found no defect in this assembly under the requested attacks.

### B. χ-positive Step 4

WholeLineChiPosStabilityNatural.lean requires the full weight window, passes it to the left-equilibrium theorem, and then to the weighted/uniform assembly. The half-line seed and successor consume a positive eta; they do not exploit a degenerate zero-weight case.

I found no defect in B under the requested attacks.

### C. paper-datum Theorem 1.2 and amended Theorem 1.3

The paper-datum theorem explicitly restricts the positive branch to χ<1/2, and its quantifiers include both

```plain text
rootMinus < eta,
eta < stabilityWeightCap.
```

The uniqueness theorem constructs a positive eta between rootMinus and min(kappaOne,cap) before applying B to each wave. It does not depend on D.

I found no defect in C under the requested attacks.

---

## Most fragile surviving hypotheses

After the concrete D defect, the three parts I would keep under the highest review pressure are:

1. Weighted-L² plus spatial modulus ⇒ uniform compact-buffer closeness in exists_eventual_chiPos_farLeft_buffer. This is the analytic bridge that makes a moving finite buffer simultaneously strict for all later times.

1. Persistent positive plateau / initial half-line seed, especially the scaled positive Lemma-4.2 ledger and its translation into a floor valid on a co-moving left half-line.

1. Supercritical floor-residual threshold split and invariant M^α<2. The floor residual is not globally monotone, so the threshold/reserve decomposition and preservation of the sharp ceiling-height invariant are load-bearing.

## Final assessment

A–C survive the five requested attacks. D does not.

The appropriate status is not “everything passed.” It is:

```plain text
Main mathematical closure A–C: no defect found in audited lines.
Auxiliary non-vacuity certification D: statement-level failure;
repair is small and uses an already-proved positive-weight-window lemma.
```