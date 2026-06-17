## Executive answer

The per-step solve is **closable**, but not with the current “prove `R_anti` from the trap” obligation. Pointwise antitonicity of the Green source `R` is a **sufficient** way to prove `W` antitone, but it is not the minimal property and is generally too strong. The clean route is:

```text
Banach fixed point for W in a bounded continuous ball
+ max-principle comparisons for 0 ≤ W ≤ Ubar and U⁻ ≤ W
+ a separate sliding/shift comparison lemma for W antitone
```

Do not try to derive `R_anti` from `Z,u,W` being trapped. The reaction part alone prevents that in general.

The repo already reflects this: `RotheStepFloor` and `PaperGreenStepInput` explicitly carry the per-step Green/trap package as the remaining floor, including `R_cont`, `R_bound`, `R_anti`, tails, comparison data, and flux/IBP data. fileciteturn153file0L8-L32 fileciteturn155file0L23-L82

---

## (1) Source antitone: probably false as stated

The source antitonicity obligation is currently:

```lean
R_anti : Antitone R
```

inside both the frozen and paper step analytic bundles. fileciteturn156file0L91-L116 fileciteturn164file0L3-L16

This is used only to prove:

```lean
Antitone W
```

via the already-proved resolvent lemma:

```lean
implicitStep_preserves_antitone :
  W = ∫ Kλ(x-y) R(y) dy →
  Antitone R →
  Antitone W
```

The lemma itself is clean: after translating the convolution to `∫ Kλ(-t) R(x+t) dt`, kernel nonnegativity transfers antitonicity by `integral_mono`. fileciteturn162file0L14-L44

But `R_anti` is not a natural consequence of the trap.

For the frozen divergence step, the Green map is

```lean
crossImplicitMap p c lam u Z W x =
  ∫ Kλ(x-y) * (reactionFun p.α (W y) + lam * Z y)
  - χ * ∫ Kλ'(x-y) * (W y)^m * V_u'(y)
```

so the nonlinear source depends on `W`, not only on `Z`. fileciteturn125file0L16-L30

Even ignoring chemotaxis, the reaction function

```text
g(s) = s(1 - s^α)
```

is not monotone on `[0,1]`. For `α = 1`, `g(1)=0` and `g(1/2)=1/4`; if `W` decreases from `1` to `1/2`, then `g(W)` increases. Thus

```text
W antitone  ⟹  reaction(W) antitone
```

is false. Adding `λZ` does not fix this uniformly: if `Z` is locally flat, `λZ` gives no strict monotone margin to dominate the reaction bump. The chemotaxis derivative term is also not pointwise sign-controlled enough to repair this.

So the minimal property is not `R_anti`; it is:

```lean
Antitone W
```

The current proof obtains `Antitone W` through the sufficient condition `R_anti`, but for the actual theorem this should be replaced by a direct **step monotonicity** theorem.

Recommended shape:

```lean
structure StepAntitoneComparisonData
    (p : CMParams) (c lam M κ : ℝ)
    (u Z W : ℝ → ℝ) : Prop where
  shift_compare :
    ∀ s, 0 ≤ s →
      -- the shifted profile W_s(x)=W(x+s) is a sub/sup comparison
      -- against W for the same implicit step, using Z(x+s) ≤ Z(x)
      ShiftedStepComparison p c lam u Z W s
```

Then prove:

```lean
theorem implicitStep_preserves_antitone_by_sliding
    (hstep : ∀ x, implicitStepOp p c (1/lam) u W x = Z x)
    (hdata : StepAntitoneComparisonData p c lam M κ u Z W)
    (hZanti : Antitone Z)
    :
    Antitone W
```

For the paper-step layer, use the analogous `paperImplicitStepOp`. The repo already has a paper-step producer and paper upper/lower comparison layer; the remaining input is explicitly named as `PaperGreenStepInput` / `PaperGreenStepInputCore`. fileciteturn163file0L8-L29 fileciteturn166file0L126-L156

---

## (2) Banach fixed point: yes, this part is standard and closable

The Banach part should be done in **divergence Green form**, not as a pointwise derivative source.

For the frozen divergence operator, the fixed-point map is already the right one:

```lean
W ↦ crossImplicitMap p c lam u Z W
```

It avoids putting `W'` in the source by integrating the chemotaxis divergence term against `Kλ'`. The repo’s `crossImplicitMap` has exactly this form. fileciteturn125file0L16-L30

The contraction estimate is also already conceptually built:

```text
factor =
  reactionLip / λ
  + |χ| * rpowLip * Bv * (2 / δ)
```

where `δ = sqrt(c² + 4λ)`, and this tends to `0` as `λ → ∞`. The repo defines this as `crossContractionFactor` and proves eventual smallness for large `λ`. fileciteturn125file0L40-L78

Mathlib’s Banach fixed point is usable. The repo already wraps it in:

```lean
crossImplicitStep_exists_unique
```

using `ContractingWith.fixedPoint`. fileciteturn125file0L147-L163

The convolution-as-bounded-continuous self-map is also already in place: `WaveRotheTrap.lean` builds `greenConvBCF`, proves the `L¹` convolution bound, and feeds it into a contraction theorem for a composed self-map. fileciteturn159file0L10-L27 fileciteturn160file0L12-L56

So the Banach floor is closable by:

```lean
def StepSourceMap
    (u Z : ℝ →ᵇ ℝ) : (ℝ →ᵇ ℝ) → (ℝ →ᵇ ℝ) :=
  fun W => -- reaction(W)+λZ and flux W^m V'

theorem stepSource_lipschitz :
  LipschitzWith Ls (StepSourceMap u Z)

theorem stepMap_contraction :
  ContractingWith K (crossStepSelfMap ... (StepSourceMap u Z))
```

The obstacle is not source dependence on `W`; Banach is designed for exactly that. The obstacle is proving the source map is a bounded-continuous map with the right Lipschitz constant and then proving the **trap fields**, especially monotonicity.

### Important paper-operator warning

If you use the expanded `paperWaveOperator`, the current `paperStepSource` includes `deriv W`:

```lean
paperStepNonlinearity p u W x :=
  -χ*m*W^(m-1)*V'*(deriv W) + ...
paperStepSource := paperStepNonlinearity + lam * Z
```

fileciteturn163file0L43-L56

That is harder for a `C⁰` Banach fixed point, because the source map depends on `W'`.

For least pain, define the **divergence-form paper step** instead:

```text
paperWaveOperator(W;u)
= frozenWaveOperator(W;u)
  + χ W^m (W^γ - u^γ)
```

so the Green map is

```text
∫ Kλ * (reaction(W) + χ W^m(W^γ-u^γ) + λZ)
  - χ ∫ Kλ' * (W^m V_u')
```

This avoids `deriv W` in the fixed-point source and keeps the Banach space as bounded continuous functions. The extra zeroth-order term is Lipschitz on `[0,M]`, so it just adds another `1/λ`-scaled Lipschitz constant.

---

## (3) What is irreducible, and what is closable?

### Closable

These are standard Green/resolvent facts and should close from the explicit kernel:

```text
bounded continuous source → bounded continuous convolution,
Green convolution is C¹/C² under the stated tail hypotheses,
variation-of-parameters identity,
Banach contraction for large λ,
positivity/comparison from Kλ ≥ 0 or max principle.
```

The repo already closes a substantial part of this: it proves per-step `C²` from Green convolution once `R_cont` and weighted tail integrability are supplied. fileciteturn154file0L17-L30 It also provides bounded-source tail lemmas on the paper side: bounded continuous `H` gives the weighted `gWeight` tail integrability and raw kernel-integrability facts. fileciteturn164file0L103-L167

### Still genuinely hard

The hard part is the **trap self-map package**, not Banach existence.

In particular:

```text
R_anti / W antitone,
whole-line barrier comparison tails,
flux IBP / divergence-form identity,
paper lower barrier comparison,
upper-barrier kink handling,
chemotaxis increment estimates at maxima.
```

The repo’s own floor file says exactly this: it has no committed whole-line `greenConv` tendsto lemma, the whole-line super-barrier is regionwise and the upper barrier is not everywhere `C²`, and `R_anti` for the chemotaxis flux is not committed. fileciteturn153file0L25-L32

So the floor is not impossible; it is **irreducible analytic work**. The bad subgoal to avoid is:

```lean
∀ trapped u Z W, Antitone (stepSource u Z W)
```

because that is stronger than needed and likely false.

---

## Concrete path to close it

### Step 1: Use a divergence-form Green map for the fixed point

For the frozen step, keep:

```lean
crossImplicitMap p c lam u Z W
```

For the paper step, add:

```lean
def paperCrossImplicitMapDiv
    (p : CMParams) (c lam : ℝ)
    (u Z W : ℝ → ℝ) : ℝ → ℝ :=
  fun x =>
    ∫ y, greenKernel c lam (x-y) *
      (reactionFun p.α (W y)
       + p.χ * (W y)^p.m * ((W y)^p.γ - (u y)^p.γ)
       + lam * Z y)
    - p.χ * ∫ y, greenKernelDeriv c lam (x-y) *
      ((W y)^p.m * deriv (frozenElliptic p u) y)
```

This keeps the contraction in `ℝ →ᵇ ℝ`.

### Step 2: Prove Banach contraction on the bounded ball

Use a truncated source if needed:

```lean
clip : ℝ → ℝ := min M (max 0 s)
```

so the source map is globally Lipschitz. Then prove the fixed point lies in `[0,M]` by comparison, so the truncation is inactive.

Expected smallness:

```text
(1/λ) * L_reaction
+ (1/λ) * |χ| * L_extra
+ (2/δ) * |χ| * L_m * Bv
< 1.
```

This is the same structure as the existing `crossContractionFactor`; add the paper zeroth-order extra term if using the paper operator.

### Step 3: Prove source regularity and Green regularity after the fixed point

Once `W` is a bounded continuous fixed point:

```lean
W = paperCrossImplicitMapDiv ...
```

derive:

```lean
Continuous W
R_bound
R_hi
R_lo
C¹/C²
step_op
```

Use the existing Green lemmas, especially the bounded-source tail lemmas on the paper side. fileciteturn166file0L40-L67

### Step 4: Trap by comparison, not by source signs

For lower/upper bounds:

```lean
0 ≤ W
Uminus ≤ W
W ≤ Ubar
W ≤ Z
```

use the clean max-principle/comparison data. The paper file already has upper and lower comparison structures:

```lean
PaperStepUpperData
PaperStepLowerData
```

with fields exactly for `paperSuper`, `paperSub`, tails, and one-sided operator-difference estimates. fileciteturn164file0L18-L55

This is the right pattern.

### Step 5: Replace `R_anti` by direct antitone comparison

Do not prove `R_anti`. Instead add:

```lean
structure PaperStepAntitoneData
    (p : CMParams) (c lam M κ : ℝ)
    (u Z W : ℝ → ℝ) : Prop where
  shift :
    ∀ s, 0 ≤ s →
      -- comparison data proving W(·+s) ≤ W
```

Then:

```lean
theorem paperStep_antitone_of_shiftComparison
    (hstep : ∀ x, paperImplicitStepOp p c (1/lam) u W x = Z x)
    (hshift : PaperStepAntitoneData p c lam M κ u Z W) :
    Antitone W
```

This is the replacement for:

```lean
paperStep_anti ... ha.R_anti
```

currently used in the paper producer. fileciteturn164file0L88-L94

If the shift comparison is too much to close immediately, carry **that** as the named residual instead of `R_anti`. It is closer to the true PDE monotonicity statement and avoids a false source-level claim.

---

## Minimal corrected floor shape

I would change the analytic core from:

```lean
R_cont
R_bound
R_anti
...
```

to:

```lean
R_cont
R_bound
...
step_antitone : Antitone W
```

or, better:

```lean
antitoneData : PaperStepAntitoneData p c lam M κ u Z W
```

and then prove `Antitone W` from that.

For example:

```lean
structure PaperStepAnalyticCore'
    (p : CMParams) (c lam M κ Λ : ℝ) (u Z W : ℝ → ℝ) where
  R : ℝ → ℝ
  source_eq : R = paperStepSourceDiv p c lam u Z W
  green_repr : W = fun x => greenConv c lam R x
  R_cont : Continuous R
  R_bound_const : ℝ
  R_bound : ∀ y, |R y| ≤ R_bound_const
  R_bound_eq : Λ = 2 * (greenDelta c lam)⁻¹ * R_bound_const
  antitoneW : Antitone W
```

Then the producer does not need `implicitStep_preserves_antitone`.

---

## Direct answers

**(1) Is `R` antitone?**  
Not in general. The reaction term alone makes this false on `[0,1]`; the chemotaxis derivative term is also not pointwise ordered. The construction needs `W` antitone, not `R` antitone. `R_anti` is a sufficient but overstrong current proof device.

**(2) Is the Green Banach fixed point closable?**  
Yes. Use the divergence-form Green map so the source depends on `W` but not `W'`. The repo already has the convolution BCF self-map and `ContractingWith` infrastructure. The contraction is the standard large-`λ` estimate. The trap bounds should come from max principles, not from source monotonicity.

**(3) Is the floor irreducible?**  
The full per-step floor is real analytic work, but not a fundamental obstruction. The linear resolvent and nonlinear Banach solve are standard and closable from the explicit Green kernel. The genuinely irreducible parts are the whole-line comparison/tail/flux-IBP/monotonicity preservation lemmas. The most important refactor is to stop trying to prove `R_anti`; prove or carry a direct `W`-antitone comparison instead.
