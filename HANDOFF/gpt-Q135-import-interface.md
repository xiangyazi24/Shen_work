ANSWER Q135 ff566d3a

# Executive recommendation

Use one explicit higher-order hypothesis hmax, exactly in the style of the Henry-semigroup input hcore in Theorem12Corrected.lean. Do not create a typeclass, do not hide the citation inside a record of unrelated estimates, and do not put the local-moment or Stage 3 bounds into the imported input.

The imported proposition should expose one maximal BUC-valued orbit, its finite-subhorizon classical and mild identities, nonnegativity and initial trace, and only the following projection of the Salako–Shen blow-up alternative:

```plain text
uniformly bounded in BUC before Tmax  ⟹  Tmax = ⊤.
```

That is strictly weaker than the cited statement Tmax<∞ ⟹ limsup ‖u(t)‖∞=∞, but it is exactly the part consumed by the continuation proof. A future formalization of the cited theorem proves the stronger result and then instantiates this interface.

The downstream capstone should conclude

```plain text
∃ u v,
  IsGlobalNonnegativeCauchySolutionFrom p u₀ u v ∧
  UniformEventuallyBounded u
```

under the faithful critical threshold, 1 ≤ χ, and this single hmax hypothesis.

There is one genuine analytic gap after the imported local theory: Stage 3, the weighted heat-semigroup bootstrap. The committed local-moment theorem gives a translation-uniform weighted L^P bound; the committed resolver theorem gives ‖vₓ‖∞; neither currently gives ‖u‖∞. The missing load-bearing estimate is the one-dimensional gradient semigroup bound

```plain text
‖∂x e^{(Δ-I)τ} f‖∞
  ≤ Cq e^{-τ} τ^{-(1/2+1/(2q))} ‖f‖q,
```

used at q=P/m>1 for the weighted chemotaxis source u^m vₓ ψ.

# Repository vocabulary that fixes the design

The historical predicate IsCUnifBdd is only continuity plus boundedness:

```javascript
def IsBddFun (f : ℝ → ℝ) : Prop := ∃ M : ℝ, ∀ x, |f x| ≤ M

def IsCUnifBdd (f : ℝ → ℝ) : Prop :=
  Continuous f ∧ IsBddFun f
```

See Defs.lean:44-49. It is therefore not the correct carrier for the cited BUC(ℝ) evolution.

The actual complete BUC phase space is

```javascript
def wholeLineBUCSubmodule :
    Submodule ℝ (BoundedContinuousFunction ℝ ℝ) where
  carrier := {f | UniformContinuous (f : ℝ → ℝ)}
  ...

abbrev WholeLineBUC := wholeLineBUCSubmodule
```

from WholeLineCauchyBUC.lean:25-39. Every such slice has the compatibility theorem

```javascript
theorem WholeLineBUC.isCUnifBdd (u : WholeLineBUC) :
    IsCUnifBdd (u.1 : ℝ → ℝ)
```

at WholeLineCauchyBUC.lean:84-89.

The paper-level datum predicate is already exactly the correct input:

```javascript
def PaperCUnifBdd (f : ℝ → ℝ) : Prop :=
  UniformContinuous f ∧ IsBddFun f

def PaperNonnegativeInitialDatum (u₀ : ℝ → ℝ) : Prop :=
  PaperCUnifBdd u₀ ∧ ∀ x, 0 ≤ u₀ x
```

See Statements.lean:28-35. The final global interface is

```javascript
def IsGlobalNonnegativeCauchySolutionFrom
    (p : CMParams) (u₀ : ℝ → ℝ)
    (u v : ℝ → ℝ → ℝ) : Prop :=
  IsGlobalClassicalSolution p u v ∧
    HasInitialDatum u u₀ ∧
    HasUniformInitialTrace u u₀ ∧
    ∀ t x, 0 ≤ t → 0 ≤ u t x
```

and eventual boundedness is

```javascript
def UniformEventuallyBounded (u : ℝ → ℝ → ℝ) : Prop :=
  ∃ M, ∀ᶠ t in atTop, ∀ x, |u t x| ≤ M
```

at Statements.lean:173-181.

Finally, the repository’s IsClassicalSolution is intentionally lean: it records positive-time differentiability and the two PDEs, but it does not encode BUC time continuity or a variation-of-constants identity; see Defs.lean:52-67. Stage 3 actually consumes a Duhamel representation, so the imported operational interface should expose the repo’s existing mild map rather than silently assume that the weak structure already contains it.

The mild map to use is

```javascript
def wholeLineCauchyMildMap
    (p : CMParams) (u₀ : ℝ → ℝ) (U : ℝ → ℝ → ℝ)
    (t x : ℝ) : ℝ :=
  if t = 0 then u₀ x
  else
    wholeLineCauchyHeatOp t u₀ x +
      wholeLineCauchyChemDuhamel p U t x +
      wholeLineCauchyReactionDuhamel p U t x
```

from WholeLineCauchyDuhamel.lean:252-274.

# (a) Recommended exact imported interface

Place this in a small file such as

```plain text
ShenWork/Paper1/WholeLineMaximalBUCInput.lean
```

with the ordinary Paper 1 namespace open.

```javascript
namespace ShenWork.Paper1

/--
Minimal operational projection of the Salako–Shen whole-line maximal BUC
Cauchy theory.  The cited theorem is stronger: it also gives uniqueness and
the finite-time limsup blow-up statement.  This predicate retains exactly the
orbit data and continuation implication consumed by Proposition 1.1(2).
-/
def WholeLineMaximalBUCSolution
    (p : CMParams) (u₀ : ℝ → ℝ) : Prop :=
  ∃ Tmax : WithTop ℝ, ∃ U : ℝ → WholeLineBUC,
    let u : ℝ → ℝ → ℝ := fun t x => (U t).1 x
    let v : ℝ → ℝ → ℝ := fun t => frozenElliptic p (u t)
    0 < Tmax ∧
      HasInitialDatum u u₀ ∧
      HasUniformInitialTrace u u₀ ∧
      (∀ T : ℝ, 0 ≤ T → (T : WithTop ℝ) < Tmax →
        ContinuousOn U (Set.Icc (0 : ℝ) T)) ∧
      (∀ T : ℝ, 0 < T → (T : WithTop ℝ) < Tmax →
        IsClassicalSolution p T u v) ∧
      (∀ T : ℝ, 0 < T → (T : WithTop ℝ) < Tmax →
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : ℝ,
          u t x = wholeLineCauchyMildMap p u₀ u t x) ∧
      (∀ t x, 0 ≤ t → (t : WithTop ℝ) < Tmax → 0 ≤ u t x) ∧
      ((∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
          (t : WithTop ℝ) < Tmax → ‖U t‖ ≤ C) →
        Tmax = ⊤)

end ShenWork.Paper1
```

## Why each field is present

## What is intentionally omitted

Uniqueness is omitted. The source theorem proves it, but the Proposition 1.1 continuation chain never compares two maximal solutions. Adding uniqueness would enlarge the imported axiom surface without serving this capstone. If a later theorem needs identification with the canonical segment construction, add a separate proved or imported uniqueness interface rather than burdening this one.

No local-moment, resolver-gradient, or L∞ estimate appears here. Those are the paper’s downstream argument and must remain proved in Lean.

No ceiling regime appears. In particular, there is no WholeLineCauchyCeilingRegime p, no MChi, and no fixed clamp ceiling.

## What a future proof of this predicate must produce

Given p, u₀, and hu₀ : PaperNonnegativeInitialDatum u₀, a future formalization of Salako–Shen must:

1. convert u₀ to the complete phase space using wholeLineBUCOfPaperCUnifBdd u₀ hu₀.1;

1. construct Tmax : WithTop ℝ and a BUC-valued orbit U on every compact subinterval below it;

1. prove the original classical PDE with v(t)=frozenElliptic p (u t);

1. prove the repo’s Duhamel identity wholeLineCauchyMildMap for that same orbit;

1. prove initial datum, uniform trace, and nonnegativity;

1. derive the final implication from the cited blow-up alternative: if ‖U t‖ had one finite bound for every t<Tmax, then a finite Tmax would contradict limsup_{t↑Tmax} ‖U t‖=∞, hence Tmax=⊤.

The arbitrary values of U t outside [0,Tmax) are irrelevant; all fields are guarded by (t : WithTop ℝ) < Tmax.

## Why this matches the Theorem 1.2 precedent

The Theorem 1.2 wrapper takes one explicit hcore hypothesis whose conclusion is the cited Henry-semigroup block, while every later estimate is proved in the repository; see the docstring and signature of paper1_Theorem_1_2_amended_of_wholeLineCauchyEnergyStep4, Theorem12Corrected.lean:197-259. The proposed hmax below is the direct analogue: one explicit hypothesis, no typeclass and no omnibus structure of downstream estimates.

# (b) Exact capstone statement

```javascript
namespace ShenWork.Paper1

/--
The residual positive-critical window of Paper 1 Proposition 1.1(2), conditional
only on the imported Salako–Shen maximal BUC theory.  Every a-priori estimate
used to force `Tmax = ⊤` is proved downstream of `hmax`.
-/
theorem Proposition_1_1_positive_critical_large_of_maximalBUC
    (hmax : ∀ (p : CMParams) (u₀ : ℝ → ℝ),
      PaperNonnegativeInitialDatum u₀ →
        WholeLineMaximalBUCSolution p u₀)
    (p : CMParams)
    (hχ : 1 ≤ p.χ)
    (hcritical : p.α = p.m + p.γ - 1)
    (hthreshold : paper1PositiveCriticalThreshold p)
    (u₀ : ℝ → ℝ)
    (hu₀ : PaperNonnegativeInitialDatum u₀) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalNonnegativeCauchySolutionFrom p u₀ u v ∧
      UniformEventuallyBounded u := by
  -- proof described below
  sorry

end ShenWork.Paper1
```

The faithful threshold is already defined as

```javascript
def paper1PositiveCriticalThreshold (p : CMParams) : Prop :=
  p.χ * (p.m - 1) < 2 * p.m - 1 ∧
    p.χ * (p.γ - 1) < p.m + p.γ - 1
```

at Proposition11PositiveErrata.lean:38-43.

The output intentionally matches the existing small-critical branch except that there is no MChi range or limsup conclusion. The existing branch has the shape

```javascript
theorem Proposition_1_1_positive_critical_branch
    ... :
    ∃ u v,
      IsGlobalNonnegativeCauchySolutionFrom p u₀ u v ∧
      ... ∧ UniformEventuallyBounded u ∧ UniformLimsupLe u (MChi p)
```

at Proposition11PositiveCritical.lean:30-41. For 1≤χ, only global existence and eventual boundedness are justified by the cited local theory plus the §3.1 bootstrap.

# (c) Exact proof chain

## Step 0 — unpack the one imported input

The beginning should look like this:

```javascript
rcases hmax p u₀ hu₀ with ⟨Tmax, U, hmaxData⟩
dsimp only at hmaxData
rcases hmaxData with
  ⟨hTmax, hinit, htrace, hcont, hclass, hmild,
    hnonneg, hcontinue⟩
let u : ℝ → ℝ → ℝ := fun t x => (U t).1 x
let v : ℝ → ℝ → ℝ := fun t => frozenElliptic p (u t)
have hχ0 : 0 ≤ p.χ := zero_le_one.trans hχ
```

No global orbit has yet been asserted. Every estimate below is proved on an arbitrary finite T satisfying (T : WithTop ℝ) < Tmax, with constants independent of T.

## Step 1 — choose the paper’s single admissible exponent

Use the committed theorem

```javascript
theorem exists_paper1PositiveCritical_admissibleExponent
    (p : CMParams) (hχ : 0 ≤ p.χ)
    (hthreshold : paper1PositiveCriticalThreshold p) :
    ∃ P : ℝ,
      max 1 (max p.m p.γ) < P ∧
      P < p.m + p.γ ∧
      p.χ * (P - 1) < P + p.m - 1
```

from WholeLineLocalMomentEnergy.lean:32-40:

```javascript
obtain ⟨P, hP, hPupper, hadm⟩ :=
  exists_paper1PositiveCritical_admissibleExponent
    p hχ0 hthreshold
```

The two later inequalities are already encoded in hP:

```plain text
p.γ < P   -- Stage 2
p.m < P   -- Stage 3
```

## Step 2 — choose the translated-weight decay rate

The committed absorption selector is

```javascript
theorem exists_small_localMomentWeight
    (p : CMParams) {P : ℝ} (hP : 1 < P)
    (hχ : 0 ≤ p.χ)
    (hadm : p.χ * (P - 1) < P + p.m - 1)
    (hcritical : p.α = p.m + p.γ - 1) :
    ∃ κ : ℝ, 0 < κ ∧ κ < 1 / 2 ∧
      0 < wholeLineLocalMomentAbsorption p P κ
```

at WholeLineLocalMomentBound.lean:438-463.

```javascript
have hPone : 1 < P :=
  (le_max_left 1 (max p.m p.γ)).trans_lt hP
obtain ⟨κ, hκ, hκhalf, habsorb⟩ :=
  exists_small_localMomentWeight
    p hPone hχ0 hadm hcritical
```

## Step 3 — build the finite-horizon local-moment package

The abstract closure is already generic. Its input structure is

```javascript
structure WholeLineLocalMomentBoundData
    (p : CMParams) (P κ T U₀ : ℝ)
    (u v : ℝ → ℝ → ℝ) where
  hT : 0 ≤ T
  hP : max 1 (max p.m p.γ) < P
  hκ : 0 < κ
  hκhalf : κ < 1 / 2
  hχ : 0 ≤ p.χ
  hcritical : p.α = p.m + p.γ - 1
  admissible : p.χ * (P - 1) < P + p.m - 1
  absorption_pos : 0 < wholeLineLocalMomentAbsorption p P κ
  energyData : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x₀,
    WholeLineLocalMomentEnergyData p P κ T t x₀ u v
  u_nonnegative : ...
  u_slice_isCUnifBdd : ...
  resolver : ...
  energy_continuous : ...
  hU₀ : 0 ≤ U₀
  initial_isCUnifBdd : IsCUnifBdd (u 0)
  initial_upper : ∀ x, u 0 x ≤ U₀
```

and it yields

```javascript
theorem WholeLineLocalMomentBoundData.uniformlyLocalLpBounded :
  UniformlyLocalLpBounded P κ u T
    (wholeLineLocalMomentUniformBound p P κ U₀)
```

at WholeLineLocalMomentBound.lean:744-779.

The moment predicate itself is

```javascript
def UniformlyLocalLpBounded
    (P κ : ℝ) (u : ℝ → ℝ → ℝ) (T K : ℝ) : Prop :=
  ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x₀,
    wholeLineLocalLpMoment P κ u t x₀ ≤ K
```

at WholeLineLocalMoment.lean:23-34.

### What can be reused

The fixed-time generic assembler

```javascript
wholeLineLocalMomentEnergyData_of_bounded_contDiff_two
```

already turns a positive bounded C² slice, bounded first and second derivatives, time-differentiation data, and IsClassicalSolution into WholeLineLocalMomentEnergyData; see WholeLineLocalMomentEnergyProducer.lean:276-290.

The energy algebra, resolver-gradient absorption, damping, and Grönwall closure then reuse verbatim.

### What cannot be reused directly

The currently exported global producer is tied to the ceiling-gated canonical orbit:

```javascript
noncomputable def wholeLineCauchyGlobal_localMomentBoundData
    (p : CMParams)
    (hregime : WholeLineCauchyCeilingRegime p)
    ...
    (hleft : StrictlyPositiveAtLeft u₀.1)
    ... :
    WholeLineLocalMomentBoundData ...
      (wholeLineCauchyGlobalU p u₀)
      (wholeLineCauchyGlobalV p u₀)
```

and its final theorem wholeLineCauchyGlobal_uniformlyLocalLpBounded retains the same regime and left-floor hypotheses; see WholeLineLocalMomentGlobalProducer.lean:441-480. It must not be called in the 1≤χ proof.

Add a parallel, regime-free adapter for the imported orbit, for example:

```javascript
noncomputable def wholeLineMaximalBUC_localMomentBoundData
    ...
    {T : ℝ} (hT : 0 ≤ T)
    (hTTmax : (T : WithTop ℝ) < Tmax) :
    WholeLineLocalMomentBoundData p P κ T U₀ u v
```

where one may take

```javascript
U₀ := ‖wholeLineBUCOfPaperCUnifBdd u₀ hu₀.1‖.
```

Compact-subhorizon BUC continuity gives a temporary finite strip bound on [0,T]; the mild identity supplies the positive-time smoothing data; all constants in the final moment bound depend on p,P,κ,U₀, not on T.

### Separate positivity adapter that must not be hidden

The generic energy assembler currently assumes

```javascript
hu_pos : ∀ x, 0 < u t x
```

because the test derivative contains powers such as u^(P-2); see WholeLineLocalMomentEnergyProducer.lean:276-290. The current concrete producer obtains this only for the canonical orbit and explicitly takes a positive-slice hypothesis; see WholeLineLocalMomentEnergyProducer.lean:717-732.

For arbitrary PaperNonnegativeInitialDatum, use an explicit split:

```plain text
u₀ ≡ 0       → the zero global solution is immediate;
u₀ not ≡ 0   → prove u(t,x)>0 for every t>0 from the positive heat kernel /
                strong maximum principle for the imported mild orbit.
```

This is not a reason to enlarge hmax: strict positivity is a standard consequence of the same nonnegative mild equation and should be proved downstream. It also cannot always be avoided by selecting P≥2, since in the case m=γ=1 the admissible interval requires P<m+γ=2.

## Step 4 — Stage 2 is already committed

Once the finite-horizon WholeLineLocalMomentBoundData exists, the repository already proves

```javascript
theorem WholeLineLocalMomentBoundData
    .uniformPositiveTimeSignalGradientBounded :
  UniformPositiveTimeSignalGradientBounded v T
    (wholeLineChiLargeGradientConstant κ
      (wholeLineLocalMomentUniformBound p P κ U₀))
```

at WholeLineChiLargeGradientBound.lean:156-173.

The key point is that the constant is independent of the finite horizon T. The theorem uses p.γ<P, which follows from the chosen exponent.

## Step 5 — the local L^P bound is not an L∞ bound

This is the genuine remaining analytic stage. A bounded uniformly-local weighted moment does not imply sup_x u(t,x)<∞ uniformly in time without an additional parabolic smoothing argument. The committed Stage 2 estimate bounds vₓ, not u.

The source proof fixes a translated weight

```plain text
ψx₀(x) = localizingWeightAt κ x₀ x
```

and sets

```plain text
w(t,x) = u(t,x) ψx₀(x).
```

The weighted PDE has a divergence source containing

```plain text
2 u ψx₀' + χ u^m vₓ ψx₀.
```

Let

```plain text
q = P / m.
```

Since P>m, one has q>1. The chemotaxis source satisfies, uniformly in t<Tmax and x₀,

```plain text
∫ |u^m vₓ ψx₀|^q
  ≤ ‖vₓ‖∞^q ∫ u^(m q) ψx₀^q
  = ‖vₓ‖∞^q ∫ u^P ψx₀^q
  ≤ ‖vₓ‖∞^q ∫ u^P ψx₀,
```

because m q=P, q>1, and 0<ψx₀≤1.

### Exact missing gradient-side estimate

Add a theorem of the following shape for the modified heat operator:

```javascript
theorem wholeLineCauchyHeatGradOp_Lp_to_Linf
    {q τ : ℝ} (hq : 1 < q) (hτ : 0 < τ)
    {f : ℝ → ℝ}
    (hf : Integrable (fun y : ℝ => |f y| ^ q)) :
    ∀ x : ℝ,
      |wholeLineCauchyHeatGradOp τ f x| ≤
        wholeLineHeatGradLpLinfConstant q * Real.exp (-τ) *
          τ ^ (-(1 / 2 + 1 / (2 * q))) *
            (∫ y : ℝ, |f y| ^ q) ^ (1 / q)
```

The exponent is forced by Young’s convolution inequality in one dimension:

```plain text
‖∂x Gτ‖_{q'} ∼ τ^{-1/2-1/(2q)},
1/q + 1/q' = 1.
```

At q=P/m, the time singularity is

```plain text
1/2 + 1/(2q) = 1/2 + m/(2P) < 1
```

exactly because P>m. Thus its Duhamel time integral is finite. The e^{-τ} factor from the generator Δ-I also makes the large-τ tail integrable uniformly in the final time.

The repository currently has only the bounded-input estimate

```javascript
theorem wholeLineCauchyHeatGradOp_norm_le_rpow
    ... (hf : ∀ y, |f y| ≤ M) ... :
    ‖wholeLineCauchyHeatGradOp τ f x‖ ≤
      C * M * τ^(-1/2)
```

at WholeLineCauchyDuhamel.lean:52-98. That theorem is circular here because f=u^m vₓ ψ is not known to be bounded before Stage 3.

HeatKernelLpEstimates.lean currently supplies heat-kernel L^p norms and smoothing constants, for example

```javascript
def heatSemigroupYoungExponent ...
def heatSemigroupLpLqSmoothingConstant ...
```

at HeatKernelLpEstimates.lean:154-168, but it does not yet supply the derivative-kernel L^q→L∞ convolution theorem above.

### Companion value-side estimate

The same Stage 3 file should also provide

```plain text
‖e^{(Δ-I)τ} f‖∞
  ≤ Cq e^{-τ} τ^{-1/(2q)} ‖f‖q,
```

for the non-divergence source in the weighted equation. Its singularity is easier. The threshold-producing term is the gradient estimate, because it needs

```plain text
1/2 + m/(2P) < 1.
```

After estimating all weighted Duhamel terms, obtain

```plain text
u(t,x) ψx₀(x) ≤ C
```

uniformly for 0≤t<Tmax, all x, and all centers x₀. Choosing x₀=x gives

```plain text
u(t,x) ≤ C / localizingWeightAt κ x x = C / localizingWeight κ 0,
```

and localizingWeight κ 0>0. Since u≥0, this is a uniform BUC norm bound before Tmax.

Package Stage 3 as a theorem such as

```javascript
theorem wholeLineMaximalBUC_uniformBound_before
    ...
    (hlocal : ∀ T, (T : WithTop ℝ) < Tmax →
      UniformlyLocalLpBounded P κ u T K)
    (hgrad : ∀ T, (T : WithTop ℝ) < Tmax →
      UniformPositiveTimeSignalGradientBounded v T Cv)
    (hmild : ...)
    ... :
    ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
      (t : WithTop ℝ) < Tmax → ‖U t‖ ≤ C
```

No blow-up alternative belongs in this theorem.

## Step 6 — invoke the blow-up alternative exactly once

After Stage 3:

```javascript
obtain ⟨C, hC⟩ := wholeLineMaximalBUC_uniformBound_before ...
have hTmaxTop : Tmax = ⊤ := hcontinue ⟨C, hC⟩
```

This is the sole use of the imported continuation field. Nothing before this line assumes global existence.

This ordering is the formal counterpart of the paper:

```plain text
maximal local solution
  → finite-horizon local L^P estimate, constant independent of T
  → finite-horizon ‖vₓ‖∞ estimate, constant independent of T
  → finite-horizon ‖u‖∞ estimate, constant independent of T
  → blow-up alternative
  → Tmax = ∞.
```

## Step 7 — package the global solution and eventual bound

After rewriting with hTmaxTop, every finite real T>0 lies below Tmax, so:

```javascript
have hglobalClassical : IsGlobalClassicalSolution p u v := by
  intro T hT
  exact hclass T hT (by simp [hTmaxTop])

have hglobalNonnegative : ∀ t x, 0 ≤ t → 0 ≤ u t x := by
  intro t x ht
  exact hnonneg t x ht (by simp [hTmaxTop])

have hsolution :
    IsGlobalNonnegativeCauchySolutionFrom p u₀ u v :=
  ⟨hglobalClassical, hinit, htrace, hglobalNonnegative⟩
```

The Stage 3 bound is stronger than UniformEventuallyBounded. Use pointwise evaluation in the BUC norm:

```javascript
have hbounded : UniformEventuallyBounded u := by
  refine ⟨max C 0, ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht x
  exact (WholeLineBUC.abs_apply_le_norm (U t) x).trans
    ((hC t ht (by simp [hTmaxTop])).trans (le_max_left _ _))

exact ⟨u, v, hsolution, hbounded⟩
```

# Recommended implementation order

1. WholeLineMaximalBUCInput.lean

1. WholeLineMaximalBUCMildRegularity.lean

1. WholeLineMaximalBUCLocalMoment.lean

1. Reuse WholeLineChiLargeGradientBound.lean verbatim for Stage 2.

1. WholeLineWeightedHeatLpLinf.lean

1. WholeLinePositiveCriticalStage3.lean

1. Proposition11PositiveCriticalLarge.lean

# Reuse / new-work matrix

# Final verdict

The right imported surface is not “there exists a global solution,” and it is not a ceiling-free version of the current canonical gluing. It is one maximal BUC orbit on (0,Tmax), together with the repo-compatible classical/mild interfaces and the minimal continuation projection

```plain text
bounded before Tmax  ⟹  Tmax=⊤.
```

The local-moment and resolver-gradient layers then run on arbitrary T<Tmax. They do not yet close the theorem because a uniformly-local weighted L^P bound is not a pointwise bound. The exact remaining bridge is the weighted Stage 3 semigroup estimate, especially

```plain text
∂x e^{(Δ-I)t} : L^{P/m}(ℝ) → L∞(ℝ),
```

whose singularity is integrable precisely because the faithful threshold supplies an exponent P>m. Only after that uniform L∞ bound is proved should the final conjunct of WholeLineMaximalBUCSolution be invoked to force Tmax=⊤.