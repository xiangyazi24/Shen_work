# DESIGN_CODEX.md — route to unconditional Paper2 Theorem 1.1

Scope: formal interval-domain Paper2 Theorem 1.1, i.e.
`Theorem_1_1 intervalDomain p`, in the current γ ≥ 1 route.  Here
"unconditional" means removing the remaining textbook/PDE input hypotheses from
the current wrappers.  It does not mean removing the paper regime assumptions
such as `p.χ₀ ≤ 0`, `0 < p.a`, `0 < p.b`, or `1 ≤ p.γ`.

This document is intentionally pessimistic.  Several gaps below are not Lean
plumbing; some are possible statement-level blockers.

## 0. Immediate Formal Warning

The current formal target is probably stronger than the Picard/local-existence
machinery can prove as stated.

Current statement:

```lean
def Theorem_1_1 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  p.χ₀ ≤ 0 →
    (0 < p.a → 0 < p.b →
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
          IsPaper2ClassicalSolution D p Tmax u v ∧
          InitialTrace D u₀ u ∧
          ... ∧
          (1 ≤ p.m → IsPaper2GlobalClassicalSolution D p u v)) ∧
    ...
```

For `intervalDomain`,

```lean
initialAdmissible := fun u₀ => BddAbove (Set.range fun x => |u₀ x|)

def PositiveInitialDatum (D : BoundedDomainData) (u₀ : D.Point → ℝ) : Prop :=
  D.initialAdmissible u₀ ∧ ∀ x, x ∈ D.inside → 0 < u₀ x
```

So the theorem currently asks for sup-norm initial trace for every bounded
interior-positive datum, with no continuity and no boundary positivity.  But
every positive-time classical slice has closed spatial regularity, and
`InitialTrace` is a sup-norm trace.  A discontinuous bounded positive initial
datum should not be reachable by uniform trace from continuous positive-time
slices.  Unless this statement is intentionally this strong, the first real
task is to strengthen `intervalDomain.initialAdmissible` or add a separate
continuous-positive initial-data layer.  Without that, a fully unconditional
formal proof is likely impossible.

## 1. Current Proven Interfaces

### 1.1 Weak divergence-form mild map

File: `ShenWork/Paper2/IntervalGradientDuhamelMap.lean`.

```lean
def chemFluxLifted (p : CM2Params) (w : intervalDomainPoint → ℝ) : ℝ → ℝ

def logisticLifted (p : CM2Params) (w : intervalDomainPoint → ℝ) : ℝ → ℝ

def intervalGradientDuhamelMap
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ)
    (x : intervalDomainPoint) : ℝ

def IntervalMildSolution
    (p : CM2Params) (T : ℝ) (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) : Prop :=
  ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
    u t x = intervalGradientDuhamelMap p u₀ u t x
```

This is the right weak map: chemotaxis is in divergence form with `∂ₓ` on the
semigroup, so the fixed point needs only C0 flux `Q`, not `chemDiv`.

### 1.2 Picard fixed point exists, but only as weak mild solution

File: `ShenWork/Paper2/IntervalMildPicard.lean`.

Auxiliary predicates:

```lean
def HasContinuousSlices (T : ℝ) (u : ℝ → intervalDomainPoint → ℝ) : Prop :=
  ∀ t, 0 < t → t ≤ T → Continuous (u t)

def HasJointMeasurability (u : ℝ → intervalDomainPoint → ℝ) : Prop :=
  Measurable (fun p : ℝ × ℝ => intervalDomainLift (u p.1) p.2)
```

Packaged input:

```lean
structure MildExistenceData (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) where
  T M K C₀ : ℝ
  hT : 0 < T
  hM : 0 < M
  hK : K < 1
  hK_nn : 0 ≤ K
  hC₀ : 0 ≤ C₀
  hbase_ball : ...
  hbase_nonneg : ...
  hbase_cont : HasContinuousSlices T (picardIter p u₀ 0)
  hmapsTo : ...
  hmapsTo_nn : ...
  hmapsTo_pos : ...
  hcont_preserved : ...
  hcontr : ...
  hbase_diff : ...
  hbase_meas : HasJointMeasurability (picardIter p u₀ 0)
  hmeas_preserved : ...
```

Output theorem from that data:

```lean
theorem intervalMildSolution_of_data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : MildExistenceData p u₀) :
    ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ → intervalDomainPoint → ℝ,
      IntervalMildSolution p T u₀ u
```

Stronger record exists:

```lean
structure GradientMildSolutionData
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) where
  T : ℝ
  hT : 0 < T
  M : ℝ
  hM : 0 < M
  u : ℝ → intervalDomainPoint → ℝ
  hmild : IntervalMildSolution p T u₀ u
  hbound : ∀ t, 0 < t → t ≤ T → ∀ x, |u t x| ≤ M
  hnonneg : ∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ u t x
  hpos : ∀ t, 0 < t → t ≤ T → ∀ x, 0 < u t x
  hcont : HasContinuousSlices T u
  hmeas : HasJointMeasurability u

def gradientMildSolutionData_of_data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : MildExistenceData p u₀) : GradientMildSolutionData p u₀
```

Concrete Picard theorem:

```lean
theorem intervalMildSolution_exists_picard
    (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ)
    (_hu₀_bounded : ∃ B : ℝ, ∀ x, |u₀ x| ≤ B)
    (_hu₀_cont : Continuous u₀)
    (hα_ge : 1 ≤ p.α)
    (hγ_ge : 1 ≤ p.γ)
    (_hu₀_nonneg : ∀ x, 0 ≤ u₀ x)
    (_hu₀_pos : ∀ x, 0 < u₀ x) :
    ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ → intervalDomainPoint → ℝ,
      IntervalMildSolution p T u₀ u
```

Important: this theorem does not expose the `GradientMildSolutionData` record,
even though its proof internally constructs `MildExistenceData`.  The downstream
local-existence bridge needs `GradientMildSolutionData`.

Also important: the theorem assumes `Continuous u₀`, `∀ x, 0 ≤ u₀ x`,
`∀ x, 0 < u₀ x`, `1 ≤ p.α`, and `1 ≤ p.γ`.  Current `PositiveInitialDatum
intervalDomain u₀` gives only boundedness plus positivity on the open interior.

### 1.3 Analytic atoms for the Picard contraction

These are already proved and used by `intervalMildSolution_exists_picard`.

Resolver weak bounds, file `ShenWork/Paper2/IntervalResolverWeakBounds.lean`:

```lean
theorem resolverValue_sup_le_of_bounded
    (p : CM2Params) {u : intervalDomainPoint → ℝ} {M : ℝ}
    (hUcont : ContinuousOn (intervalDomainLift u) (Set.Icc (0:ℝ) 1))
    (hlb : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ intervalDomainLift u x)
    (hub : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift u x ≤ M)
    (x : intervalDomainPoint) :
    |intervalNeumannResolverR p u x| ≤
      Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2) *
        (2 * (p.ν * M ^ p.γ))

theorem resolverGrad_sup_le_of_bounded
    (p : CM2Params) {u : intervalDomainPoint → ℝ} {M : ℝ}
    (hUcont : ContinuousOn (intervalDomainLift u) (Set.Icc (0:ℝ) 1))
    (hlb : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ intervalDomainLift u x)
    (hub : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift u x ≤ M)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    |resolverGradReal p u x| ≤
      Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * M ^ p.γ))

theorem resolverValue_diff_sup_le_of_bounded
    (p : CM2Params) (hγ : 1 ≤ p.γ) ... :
    |intervalNeumannResolverR p u₁ x - intervalNeumannResolverR p u₂ x| ≤
      Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2) *
        (2 * (p.ν * (p.γ * M ^ (p.γ - 1)) * D))

theorem resolverGrad_diff_sup_le_of_bounded
    (p : CM2Params) (hγ : 1 ≤ p.γ) ... :
    |resolverGradReal p u₁ x - resolverGradReal p u₂ x| ≤
      Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * (p.γ * M ^ (p.γ - 1)) * D))
```

Resolver positivity, file `ShenWork/PDE/IntervalResolverPositivity.lean`:

```lean
theorem intervalNeumannResolverR_nonneg_of_nonneg_source
    {p : CM2Params} {u : intervalDomainPoint → ℝ} {f : ℝ → ℝ}
    (hf_cont : Continuous f) (hf_nonneg : ∀ y, 0 ≤ f y)
    (hf_coeff : ∀ k, cosineCoeffs f k =
      (intervalNeumannResolverSourceCoeff p u k).re)
    (hâ : Summable (fun k => (cosineCoeffs f k) ^ 2))
    (xp : intervalDomainPoint) :
    0 ≤ intervalNeumannResolverR p u xp
```

Logistic Lipschitz, file `ShenWork/PDE/IntervalLogisticLipschitz.lean`:

```lean
theorem intervalLogisticReaction_lipschitz_on_bounded
    (p : CM2Params) (hα : 1 ≤ p.α) {M : ℝ} (hM : 0 < M) :
    ∃ L > 0, ∀ u₁ u₂ : ℝ, |u₁| ≤ M → |u₂| ≤ M →
      |u₁ * (p.a - p.b * u₁ ^ p.α) -
        u₂ * (p.a - p.b * u₂ ^ p.α)| ≤ L * |u₁ - u₂|
```

Gradient/value Duhamel bounds, file `ShenWork/PDE/IntervalGradDuhamelBound.lean`:

```lean
theorem valueDuhamel_diff_sup_bound ... :
  |∫ s in (0:ℝ)..t, (S(t-s) r₁ - S(t-s) r₂)| ≤ T * D

theorem gradDuhamel_diff_sup_bound ... :
  |∫ s in (0:ℝ)..t, (∂ₓS(t-s) q₁ - ∂ₓS(t-s) q₂)| ≤
    Cgrad * (2 * Real.sqrt T) * D
```

Flux algebra and small-time contraction, file `ShenWork/PDE/IntervalChemFluxLipschitz.lean`:

```lean
theorem chemFlux_div_lipschitz {β M B_G d L_G L_R : ℝ}
    (hβ : 0 ≤ β) ... :
    |a₁ * g₁ / (1 + v₁) ^ β -
      a₂ * g₂ / (1 + v₂) ^ β| ≤
      (B_G + M * L_G + M * B_G * β * L_R) * d

theorem exists_small_contraction_time {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ T : ℝ, 0 < T ∧ A * Real.sqrt T + B * T < 1

theorem gradientDuhamel_contraction_pointwise
    {χ₀ Cgrad C_Q C_L T d G V : ℝ}
    (hG : |G| ≤ Cgrad * (2 * Real.sqrt T) * (C_Q * d))
    (hV : |V| ≤ T * (C_L * d)) :
    |(-χ₀) * G + V| ≤
      (2 * |χ₀| * Cgrad * C_Q * Real.sqrt T + C_L * T) * d
```

### 1.4 Restart/regularity bootstrap for a `GradientMildSolutionData`

File: `ShenWork/Paper2/IntervalMildRegularityBootstrap.lean`.

```lean
def HasRestartCosineRepresentations
    (T : ℝ) (u : ℝ → intervalDomainPoint → ℝ) : Prop :=
  ∀ t, 0 < t → t < T → Nonempty (RestartCosineRepresentation (u t))

structure GradientMildHalfStepRestartData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) where
  a : ℝ → ℝ → ℕ → ℝ
  src : ∀ t, 0 < t → t < D.T → DuhamelSourceTimeC1 (a t)
  hagree : ∀ t, 0 < t → t < D.T →
    Set.EqOn (intervalDomainLift (D.u t))
      (fun x : ℝ =>
        ∑' n : ℕ,
          restartDuhamelCoeff (gradientMildHalfStepInitialCoeff D t)
            (a t) (t / 2) n * cosineMode n x)
      (Set.Icc (0 : ℝ) 1)

structure GradientMildHalfStepH2SourceData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) where
  source : ℝ → ℝ → ℝ → ℝ
  ...
  hH2 : ∀ t, 0 < t → t < D.T →
    ∀ s, 0 ≤ s → IntervalWeakH2Neumann (source t s)
  ...
  hagree : ...
```

Key outputs:

```lean
theorem hasRestartCosineRepresentations_of_gradientMildHalfStepRestartData
    (D : GradientMildSolutionData p u₀)
    (R : GradientMildHalfStepRestartData D) :
    HasRestartCosineRepresentations D.T D.u

theorem gradientMild_closedC2_endpointDerivs_of_halfStepRestartData
    (D : GradientMildSolutionData p u₀)
    (R : GradientMildHalfStepRestartData D) :
    ∀ t, 0 < t → t < D.T →
      ContDiffOn ℝ 2 (intervalDomainLift (D.u t)) (Set.Icc 0 1)
        ∧ deriv (intervalDomainLift (D.u t)) 0 = 0
        ∧ deriv (intervalDomainLift (D.u t)) 1 = 0
```

### 1.5 Picard-iterate regularity, not Picard-limit regularity

File: `ShenWork/Paper2/IntervalMildPicardRegularity.lean`.

Logistic source package:

```lean
structure GradientMildHalfStepLogisticSourceData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) where
  profile : ℝ → ℝ → ℝ → ℝ
  C : ℝ → ℝ
  hC : ...
  hC2 : ...
  hpos : ...
  hN0 : ...
  hN1 : ...
  hdecay : ...
  ha0_bound : ...
  adot : ℝ → ℝ → ℕ → ℝ
  hderiv : ...
  hadotcont : ...
  Mdot : ℝ → ℝ
  hMdot : ...
  hagree : ...

theorem hasRestartCosineRepresentations_of_gradientMildHalfStepLogisticSourceData
    (D : GradientMildSolutionData p u₀)
    (S : GradientMildHalfStepLogisticSourceData D) :
    HasRestartCosineRepresentations D.T D.u

theorem gradientMild_closedC2_endpointDerivs_of_halfStepLogisticSourceData
    (D : GradientMildSolutionData p u₀)
    (S : GradientMildHalfStepLogisticSourceData D) :
    ∀ t, 0 < t → t < D.T →
      ContDiffOn ℝ 2 (intervalDomainLift (D.u t)) (Set.Icc 0 1)
        ∧ deriv (intervalDomainLift (D.u t)) 0 = 0
        ∧ deriv (intervalDomainLift (D.u t)) 1 = 0
```

Picard iterate predicate and induction:

```lean
def PicardIterateHasC2Slices
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (T : ℝ) (n : ℕ) : Prop :=
  ∀ t, 0 < t → t ≤ T →
    ContDiffOn ℝ 2 (intervalDomainLift (picardIter p u₀ n t)) (Set.Icc 0 1)
    ∧ deriv (intervalDomainLift (picardIter p u₀ n t)) 0 = 0
    ∧ deriv (intervalDomainLift (picardIter p u₀ n t)) 1 = 0

structure PicardRegularityStepData
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (T : ℝ) (n : ℕ) where
  M_restart : ℝ
  ha₀_bound : ...
  source : ℝ → ℝ → ℕ → ℝ
  src : ∀ t, 0 < t → t ≤ T → DuhamelSourceTimeC1 (source t)
  hagree : ...
  hne0 : ...
  hne1 : ...

theorem picardIterateHasC2Slices_zero ...
theorem picardIterateHasC2Slices_succ
    (S : PicardRegularityStepData p u₀ T n) :
    PicardIterateHasC2Slices p u₀ T (n + 1)

theorem picardIterateHasC2Slices_all ... :
    ∀ n, PicardIterateHasC2Slices p u₀ T n
```

This proves regularity of iterates under step data.  It does not prove the
limit has `DuhamelSourceTimeC1`, `HasRestartCosineRepresentations`, or classical
regularity.

### 1.6 Mild-to-local-existence bridge

File: `ShenWork/Paper2/IntervalMildToLocalExistence.lean`.

Residual classical core:

```lean
structure GradientMildClassicalCoreData
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u0) : Prop where
  hpde_u : ∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
    intervalDomain.timeDeriv D.u t x =
      intervalDomain.laplacian (D.u t) x
        - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
            (mildChemicalConcentration p D.u t) x
        + D.u t x * (p.a - p.b * (D.u t x) ^ p.α)
  hclassicalRegularity :
    intervalDomainClassicalRegularity D.T D.u
      (mildChemicalConcentration p D.u)

structure GradientMildClassicalFrontierCoreData
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u0) : Prop where
  hpde_u : same as above
  hregularityFrontier :
    GradientMildClassicalRegularityFrontierData p D

def GradientMildInitialApproach
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u0) : Prop :=
  ∀ ε, 0 < ε →
    ∃ δ > 0, ∀ t, 0 < t → t < δ →
      ∀ x : intervalDomainPoint,
        |intervalGradientDuhamelMap p u0 D.u t x - u0 x| < ε
```

Local-existence bridge:

```lean
theorem localExistence_of_gradientMildSolutionData_of_halfStepLogisticSourceData_and_frontierCore
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (hu0 : PositiveInitialDatum intervalDomain u0)
    (D : GradientMildSolutionData p u0)
    (S : GradientMildHalfStepLogisticSourceData D)
    (hInitialApproach : ∀ ε, 0 < ε →
      ∃ δ > 0, ∀ t, 0 < t → t < δ →
        ∀ x : intervalDomainPoint,
          |intervalGradientDuhamelMap p u0 D.u t x - u0 x| < ε)
    (C : GradientMildClassicalFrontierCoreData p D) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u0 u
```

This theorem is useful only after producing all of:
`GradientMildSolutionData`, `GradientMildHalfStepLogisticSourceData`,
`GradientMildInitialApproach`, and `GradientMildClassicalFrontierCoreData`.

### 1.7 Remaining regularity frontier shape

File: `ShenWork/Paper2/IntervalMildToClassical.lean`.

```lean
structure GradientMildClassicalRegularityFrontierData
    (p : CM2Params) {u₀ : intervalDomainPoint -> ℝ}
    (D : GradientMildSolutionData p u₀) : Prop where
  supnormLogistic : ...
  supnormZero : ...
  vSpatialInterior : ...
  timeSlices : ...
  jointTimeDerivInterior : ...
  vNeumannLimits : ...
  vClosedSpatial : ...
  jointTimeDerivClosed : ...
  jointSolutionClosed : ...

theorem mildSolution_classicalRegularity_of_restartCosineRepresentations_and_frontier
    (p : CM2Params) {u₀ : intervalDomainPoint -> ℝ}
    (D : GradientMildSolutionData p u₀)
    (H : HasRestartCosineRepresentations D.T D.u)
    (F : GradientMildClassicalRegularityFrontierData p D) :
    intervalDomainClassicalRegularity D.T D.u
      (mildChemicalConcentration p D.u)
```

Crucial negative fact: `mildSolution_parabolicPDE` has signature

```lean
theorem mildSolution_parabolicPDE
    (p : CM2Params) (D : GradientMildSolutionData p u₀)
    (hclassical : IsPaper2ClassicalSolution intervalDomain p D.T D.u
      (mildChemicalConcentration p D.u)) :
    ...
```

So it does not derive the parabolic PDE from the mild equation; it extracts it
from an already-classical solution.  The post-hoc proof of `hpde_u` remains open.

### 1.8 Older coupled Duhamel local-existence scaffold

File: `ShenWork/PDE/IntervalDomainExistence.lean`.

Old source/operator:

```lean
def intervalCoupledSource (p : CM2Params)
    (u v : intervalDomainPoint → ℝ) (x : intervalDomainPoint) : ℝ :=
  -p.χ₀ * intervalDomainChemotaxisDiv p u v x + intervalLogisticSource p u x

def intervalCoupledDuhamelOperator
    (p : CM2Params)
    (R : (intervalDomainPoint → ℝ) → intervalDomainPoint → ℝ)
    (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ)
    (t : ℝ) (x : intervalDomainPoint) : ℝ
```

Resolver-estimate interface for the old divergence-form source:

```lean
def IntervalCoupledResolverBallEstimates
    (p : CM2Params)
    (R : (intervalDomainPoint → ℝ) → intervalDomainPoint → ℝ)
    (u₀ : intervalDomainPoint → ℝ)
    (T M K : ℝ) : Prop := ...

theorem localExistence_of_coupledDuhamel_resolver_estimates_and_regularization
    (p : CM2Params)
    (R : (intervalDomainPoint → ℝ) → intervalDomainPoint → ℝ)
    (u₀ : intervalDomainPoint → ℝ)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {A L K T M : ℝ} (hA : 0 < A) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hT : 0 < T) (hAT : A * T < 1) (hM : 0 ≤ M)
    (hA_bound : |p.χ₀| * K + L ≤ A)
    (hL_lip : ...)
    (hest : IntervalCoupledResolverBallEstimates p R u₀ T M K)
    (hregularize : ...) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u₀ u
```

This scaffold is mostly superseded for the weak route because it uses
`intervalDomainChemotaxisDiv` in the source.  It is still useful as a reference
for Banach/regularization packaging, but not the right operator for avoiding
the over-strong `chemDiv` Lipschitz assumption.

### 1.9 Paper-level γ ≥ 1 wrapper

File: `ShenWork/Paper2/IntervalDomainTheorem11Umbrella.lean`.

Uniform continuation input:

```lean
def IntervalDomainUniformLocalExistence (p : CM2Params) : Prop :=
  ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
    ∀ {u₀ : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u₀ →
      (∀ x : intervalDomain.Point, |u₀ x| ≤ M) →
      ∀ {T₀ : ℝ}, 0 < T₀ →
      ∀ {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₀ u v →
        InitialTrace intervalDomain u₀ u →
        ∃ u' v' : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p (T₀ + δ) u' v' ∧
          InitialTrace intervalDomain u₀ u'
```

Leanest current wrapper:

```lean
theorem Theorem_1_1_intervalDomain_via_regime_gammaGeOne_no_hextend_mge
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hlocal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
    (hUniform : IntervalDomainUniformLocalExistence p)
    (hposWit :
      ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
          PositiveInitialDatum intervalDomain u₀) :
    Theorem_1_1 intervalDomain p
```

Gradient-mild local-data wrapper:

```lean
theorem Theorem_1_1_intervalDomain_via_regime_gammaGeOne_gradientMildHalfStepLogisticSourceFrontierCoreLocalData
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hMildLocal :
      IntervalDomainGradientMildHalfStepLogisticSourceFrontierCoreLocalData p)
    (hUniform : IntervalDomainUniformLocalExistence p)
    (hposWit : ...) :
    Theorem_1_1 intervalDomain p
```

The data consumed by this wrapper is:

```lean
def IntervalDomainGradientMildHalfStepLogisticSourceFrontierCoreLocalData
    (p : CM2Params) : Prop :=
  ∀ u₀ : intervalDomain.Point → ℝ,
    PositiveInitialDatum intervalDomain u₀ →
      ∃ D : GradientMildSolutionData p u₀,
      ∃ _S : GradientMildHalfStepLogisticSourceData D,
        GradientMildInitialApproach p D ∧
        GradientMildClassicalFrontierCoreData p D
```

## 2. Missing Pieces

### Gap A: formal initial datum surface is too weak

Needed for current theorem:

```lean
∀ u₀, PositiveInitialDatum intervalDomain u₀ → local existence with sup InitialTrace
```

Available Picard theorem requires:

```lean
∃ B, ∀ x, |u₀ x| ≤ B
Continuous u₀
1 ≤ p.α
1 ≤ p.γ
∀ x, 0 ≤ u₀ x
∀ x, 0 < u₀ x
```

Current `PositiveInitialDatum intervalDomain u₀` gives only:

```lean
BddAbove (Set.range fun x => |u₀ x|)
∀ x, x ∈ intervalDomain.inside → 0 < u₀ x
```

Exact missing mathematical content:

1. continuity of `u₀`;
2. boundary nonnegativity or positivity;
3. `1 ≤ p.α` if the current Banach-in-sup ball proof is kept;
4. a way to obtain sup-norm `InitialTrace` from discontinuous bounded data,
   which is mathematically false for a heat-type classical solution.

This is not wiring.

### Gap B: Picard theorem should export `GradientMildSolutionData`

Needed by the bridge:

```lean
∃ D : GradientMildSolutionData p u₀, ...
```

Current theorem exports only:

```lean
∃ T > 0, ∃ u, IntervalMildSolution p T u₀ u
```

Exact missing content:

```lean
theorem gradientMildSolutionData_exists_picard
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    ...same assumptions as intervalMildSolution_exists_picard... :
    ∃ D : GradientMildSolutionData p u₀, True
```

This is wiring: factor the internal `MildExistenceData` construction and apply
`gradientMildSolutionData_of_data`.

### Gap C: initial approach of the gradient mild map

Needed:

```lean
GradientMildInitialApproach p D
```

For a fixed point `D.hmild`, this is equivalent to uniform initial trace:

```lean
∀ ε > 0, ∃ δ > 0, ∀ 0 < t < δ, ∀ x,
  |D.u t x - u₀ x| < ε
```

Exact missing mathematical content:

1. uniform convergence of the full Neumann semigroup:
   `sup_x |S(t)(lift u₀)(x) - u₀(x)| → 0` as `t → 0+`;
2. uniform smallness of the gradient Duhamel chemotaxis term:
   `O(sqrt t)`;
3. uniform smallness of the logistic Duhamel term:
   `O(t)`;
4. endpoint handling for the lift/subtype equality.

Existing `intervalFullSemigroup_tendsto_id_at_zero` is pointwise on the
interior and requires ℓ1 coefficient/reconstruction hypotheses:

```lean
theorem intervalFullSemigroup_tendsto_id_at_zero
    (f : ℝ → ℝ) (hf : Continuous f) (x : ℝ) (hx : x ∈ Set.Ioo 0 1)
    (hl1 : Summable (fun n => |cosineCoeffs f n|))
    (hrecon : HasSum ...)
    (hkernel : ...) :
    Tendsto (fun t => intervalFullSemigroupOperator t f x)
      (𝓝[>] 0) (𝓝 (f x))
```

This is not enough for sup-norm `InitialTrace`.

### Gap D: restart/source regularity for the Picard limit

Needed by the current best bridge:

```lean
GradientMildHalfStepLogisticSourceData D
```

or at least:

```lean
HasRestartCosineRepresentations D.T D.u
```

plus sufficient closed C2/Neumann data.

What is proved now:

* Picard iterates have C2 slices under `PicardRegularityStepData`.
* A `GradientMildHalfStepLogisticSourceData D` would imply restart
  representations and closed C2 for the limit.

What is missing:

1. passage from iterate regularity to limit regularity with weighted coefficient
   control;
2. `DuhamelSourceTimeC1` for the limit source;
3. exact half-step spectral agreement `hagree` for the limit;
4. for `χ₀ ≠ 0`, a representation of the chemotaxis gradient-Duhamel term.

The last point is serious: `GradientMildHalfStepLogisticSourceData` only feeds
the logistic source into the restart Duhamel series.  For the full chemotaxis
equation, the half-step representation must account for

```lean
(-p.χ₀) * ∫ ∂ₓS(t-s) Q(u(s)) ds
```

either by a new gradient-Duhamel restart representation, or by proving after
regularization that `∂ₓQ = chemDiv` and converting to a value-Duhamel source.
That conversion is circular unless enough regularity of `Q` is already known.

### Gap E: parabolic PDE and full frontier regularity

Needed:

```lean
GradientMildClassicalFrontierCoreData p D
```

This contains:

* `hpde_u`, the actual PDE for `u`;
* `GradientMildClassicalRegularityFrontierData p D`, including time-slice
  differentiability, joint time-derivative continuity, joint solution
  continuity on closed slabs, `v` spatial C2, and `v` Neumann limits.

Current `mildSolution_parabolicPDE` is not a proof from the mild equation; it
requires an existing `IsPaper2ClassicalSolution`.  So `hpde_u` is open.

Exact missing mathematical content:

1. differentiate the weak gradient-Duhamel fixed point in time;
2. identify the time derivative with `Δu - χ chemDiv + logistic`;
3. prove `Q = u ∂ₓR/(1+R)^β` has enough spatial regularity to define
   `chemDiv = ∂ₓQ`;
4. prove joint continuity of all derivative fields on the required slabs;
5. prove `v = R(u)` has the stated elliptic C2/Neumann package from the
   post-hoc `u` regularity.

This is a real parabolic-regularity theorem.  It is not discharged by the
existing bridge layer.

### Gap F: local existence for all formal `PositiveInitialDatum`

Even after Gaps B-E, the resulting theorem will likely have assumptions close
to:

```lean
Continuous u₀
∀ x, 0 ≤ u₀ x
maybe ∀ x, 0 < u₀ x
1 ≤ p.α
1 ≤ p.γ
```

But paper-level `hlocal` asks:

```lean
∀ u₀, PositiveInitialDatum intervalDomain u₀ → ...
```

So one of the following must happen:

1. strengthen `intervalDomain.initialAdmissible`;
2. introduce a new theorem statement with a stronger initial-datum predicate;
3. develop a genuinely L∞-initial-data theory with sup-norm trace, which is
   not plausible for discontinuous data;
4. prove a contradiction/counterexample and revise the formal target.

### Gap G: uniform local continuation

Needed by current γ ≥ 1 wrapper:

```lean
IntervalDomainUniformLocalExistence p
```

This is not merely "local existence with a small T".  Its output is a solution
on `T₀ + δ` with the same initial trace as `u₀`, for every existing solution on
`T₀`.  Proving it requires a continuation/restart theorem:

1. obtain an a priori bound for the current branch up to `T₀`;
2. obtain a restart datum at/near `T₀`;
3. run local existence with lifespan depending only on that bound;
4. glue the old branch and restarted branch;
5. preserve the original initial trace.

The current definition does not require the output branch to agree with the
input branch on `(0,T₀)`, but a proof will still need such agreement internally
unless one already has arbitrary-long existence.  This is a major PDE
continuation theorem.

### Gap H: `hposWit` pass-through

Current wrapper still consumes:

```lean
hposWit :
  ∀ {u₀ T₁ T₂ u₁ v₁ u₂ v₂},
    IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
    IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
    InitialTrace intervalDomain u₀ u₁ →
    InitialTrace intervalDomain u₀ u₂ →
      PositiveInitialDatum intervalDomain u₀
```

As a standalone theorem this is too strong: strict positivity of the initial
datum is not a formal consequence of uniform trace from positive-time positive
solutions without more structure.  The right route is probably to remove this
argument from the gluing wrapper by threading the original `hu₀ :
PositiveInitialDatum intervalDomain u₀` through the reachable/gluing chain.

This is mostly wiring, but the existing `hposWit` statement itself should not be
treated as a harmless theorem to prove.

## 3. Attack Routes

### Route A: fix or explicitly narrow the initial-data surface

Preferred if the target is allowed to match the actual PDE theorem:

* Strengthen `intervalDomain.initialAdmissible` from boundedness only to at
  least boundedness plus continuity and nonnegativity.
* If closed-domain strict positivity is required by the current Picard proof,
  either include it or redesign the positivity proof to allow boundary zeros.

Likely Lean work:

* update constructors using `PositiveInitialDatum.admissible`;
* replace direct use of `hu₀.admissible : BddAbove ...` by projections;
* repair theorem wrappers that build bounded-initial data.

Useful Mathlib/Lean tools:

* `Continuous.comp`, `ContinuousOn.comp_continuousOn`;
* `isCompact_Icc`, `IsCompact.exists_forall_le`;
* `continuousOn_iff_continuous_restrict`;
* `Set.restrict`, `Subtype.ext`, `simp [intervalDomainLift]`.

If the formal target cannot be narrowed, prove first that the current statement
forces initial continuity from `InitialTrace` and positive-time closed
regularity, then exhibit a bounded positive discontinuous datum.  This would
show the current statement is not the right unconditional target.

### Route B: expose `GradientMildSolutionData`

Create an exported theorem whose proof is the existing
`intervalMildSolution_exists_picard` proof, but ending with:

```lean
exact ⟨gradientMildSolutionData_of_data Ddata⟩
```

No new math.  Do not duplicate the 1000-line proof if avoidable; factor the
record construction into a private or public def:

```lean
def mildExistenceData_picard ... : MildExistenceData p u₀
```

Then:

```lean
theorem gradientMildSolutionData_exists_picard ... :
  ∃ D : GradientMildSolutionData p u₀, True :=
⟨gradientMildSolutionData_of_data (mildExistenceData_picard ...), trivial⟩
```

Tactics: `refine`, `exact`, `simpa`, `rcases`, `obtain`.  This is wiring.

### Route C: prove `GradientMildInitialApproach`

For the fixed point, use:

```lean
D.hmild t ht htT x
```

and expand `intervalGradientDuhamelMap`.

Duhamel terms:

* use `valueDuhamel_sup_bound_universal` for `O(t)`;
* use `gradDuhamel_sup_bound_universal` for `O(sqrt t)`;
* reuse the same source bounds already built inside `intervalMildSolution_exists_picard`.

Semigroup term:

Needed theorem:

```lean
theorem intervalFullSemigroupOperator_uniform_tendsto_id_at_zero
    {f : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Set.Icc 0 1))
    (hf_zero_outside_or_lift : ... ) :
    ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
      ∀ x ∈ Set.Icc 0 1,
        |intervalFullSemigroupOperator t f x - f x| < ε
```

Attack options:

1. Kernel approximate identity route:
   * use full kernel positivity and mass `intervalNeumannFullKernel_integral_eq_one`;
   * use uniform continuity of `f` on `[0,1]`;
   * split integral into near/far parts;
   * use Gaussian tail estimates for the full reflected kernel.
2. Spectral route:
   * approximate `f` uniformly by finite cosine polynomials;
   * use exact semigroup action on finite modes;
   * use contraction in sup norm.

The kernel route matches existing heat-kernel infrastructure better.  Useful
Mathlib:

* `Metric.uniformContinuousOn_iff`;
* `IsCompact.uniformContinuousOn_of_continuousOn`;
* `MeasureTheory.norm_setIntegral_le_of_norm_le_const_ae'`;
* `intervalIntegral.integral_mono_on`;
* `Filter.Tendsto`, `Metric.tendsto_nhds`;
* existing `intervalFullSemigroupOperator_Linfty_bound`;
* existing kernel mass/positivity lemmas.

This is real analysis in Lean, but standard.

### Route D: replace logistic-only restart data by full gradient-form regularity

Do not assume `GradientMildHalfStepLogisticSourceData` is enough for `χ₀ ≠ 0`
unless its `hagree` can actually include the chemotaxis term.  The honest
route is one of:

1. New gradient-Duhamel restart representation:
   ```lean
   GradientMildHalfStepFluxRestartData D
   ```
   with coefficients for both
   `∫ ∂ₓS Q` and `∫ S L`.
2. Prove after a positive half-step that `Q` is C1 and time-C1, so that
   `∫ ∂ₓS Q` can be integrated by parts or rewritten as a value-Duhamel term
   with source `-χ ∂ₓQ`.

Needed estimates:

* weighted coefficient summability for the chemotaxis contribution;
* time derivative of flux coefficients;
* uniform envelopes sufficient for `DuhamelSourceTimeC1` or a new analogue;
* exact series agreement with `D.u t`.

Useful existing lemmas:

* `duhamelSpectralCoeff_eigenvalue_summable`;
* `restartDuhamelCoeffSeries_contDiff_two`;
* `hasDerivAt_tsum_of_isPreconnected`;
* `intervalFullSemigroupOperator_deriv_sub`;
* `ContDiffOn.div`;
* `Real.contDiffAt_rpow_const_of_ne`;
* `chemFlux_div_lipschitz` for pointwise algebra only.

This is a real math gap.

### Route E: prove `GradientMildClassicalFrontierCoreData`

Break it into explicit theorem targets:

1. `gradientMild_hpde_u_of_regularized_fixedPoint`
   * differentiate the mild equation in time;
   * identify `∂t S(t)u₀ = ΔS(t)u₀`;
   * handle Duhamel endpoint terms;
   * convert divergence-form chemotaxis into `chemDiv`.
2. `gradientMild_timeSlices_of_regularized_fixedPoint`
3. `gradientMild_jointTimeDerivInterior_of_regularized_fixedPoint`
4. `gradientMild_jointTimeDerivClosed_of_regularized_fixedPoint`
5. `mildChemical_vClosedSpatial_from_uClosedSpatial`
6. `mildChemical_vNeumannLimits_from_uClosedSpatial`
7. `gradientMild_supnormLogistic/supnormZero`

Useful existing files:

* `IntervalDuhamelClosedC2.lean` for time-IBP removing singular second
  derivatives;
* `IntervalUnderIntegralLeibniz.lean` for parameter differentiation;
* `IntervalMildSourceDecayHelper.lean` for weak H2/Neumann;
* `IntervalResolverPositivity.lean` and `IntervalResolverWeakBounds.lean`;
* `IntervalDomainL2CrossControl.lean` and energy files for supnorm/monotonicity
  only if the needed theorem is already there.

Useful tactics/lemmas:

* `rw [D.hmild ...]`, then `unfold intervalGradientDuhamelMap`;
* `intervalIntegral.integral_congr_ae`;
* `MeasureTheory.integral_sub`, `integral_add`, `integral_const_mul`;
* `HasDerivAt.integral` or local project-specific Leibniz lemmas;
* `ContDiffOn.congr`, `ContinuousOn.congr`;
* `Filter.Tendsto.congr'`, `EventuallyEq.deriv_eq`;
* `nlinarith`, `ring_nf`, `field_simp` for algebra.

This is the central hard PDE/Lean task.

### Route F: remove or thread `hposWit`

Do not try to prove the current standalone `hposWit` unless a new lemma shows
it follows from the specific reachable construction.

Better route:

* create a fixed-initial-datum gluing theorem:
  ```lean
  GlobalSolutionGluingFromReachability_of_regime_gammaGeOne_fixedDatum
      ... (u₀) (hu₀ : PositiveInitialDatum intervalDomain u₀) ...
  ```
* propagate `hu₀` through overlap uniqueness and locality instead of recovering
  it from two traces;
* wrap back into the `∀ u₀, PositiveInitialDatum ... → ...` theorem.

This is mostly wiring through existing gluing proofs.

### Route G: prove uniform local continuation

A plausible non-circular route:

1. Prove a local-existence theorem with lifespan depending only on a closed
   set of quantitative bounds:
   * `‖u_restart‖∞ ≤ M`;
   * continuity/C2 bounds as needed;
   * nonnegativity/positivity assumptions actually used;
   * parameter constants.
2. Use already proved a priori bounds in the regime `χ₀ ≤ 0`, `a,b>0`,
   `1 ≤ γ` to bound any classical branch before `T₀`.
3. Extract a restart datum near the finite horizon from closed-time
   compactness/regularity.
4. Solve locally from restart datum.
5. Glue with old branch and keep original initial trace.

Potential existing inputs:

* `GlobalSolutionGluingFromReachability_of_regime_gammaGeOne` is already proved
  modulo `hposWit`;
* T8 notes say the `Kunif` chain is discharged:
  `uniformLiftBoundZeroM_of_regime`,
  `gronwall_const_of_uniformLiftBoundZeroM`,
  `boundednessHypothesis_of_uniformSupBoundZeroM`;
* `classicalSolutionLocalityUnderIooAgreement_intervalDomain`;
* overlap uniqueness from energy method.

Likely missing theorem shape:

```lean
theorem intervalDomainUniformLocalExistence_of_regime
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hlocal_quantitative : ...)
    (hcontinuation_regularize : ...) :
    IntervalDomainUniformLocalExistence p
```

This is a true continuation theorem, not just wrapper code.

## 4. Wiring vs Real Mathematics

Wiring / packaging:

* export `GradientMildSolutionData` from the Picard construction;
* add theorem wrappers from exported local data to the existing umbrella;
* remove/thread `hposWit` through gluing;
* avoid the old `intervalCoupledDuhamelOperator` route when using the gradient
  mild map;
* import organization and `Fact` wrappers.

Real mathematics:

* current initial-datum predicate mismatch;
* α < 1 if the final theorem really allows it;
* non-strict boundary initial data if the final theorem really allows it;
* uniform semigroup approximate identity in sup norm;
* chemotaxis gradient-Duhamel post-hoc C2 regularity;
* `hpde_u` from differentiating the weak mild equation;
* full time/joint regularity frontier;
* uniform local continuation at finite horizons.

## 5. Dependency DAG

```text
A. Fix/narrow initial-data surface
   ├─> B. Export GradientMildSolutionData from Picard
   │   ├─> C. InitialApproach
   │   ├─> D. Restart/source or direct gradient-Duhamel regularity
   │   │   └─> E. GradientMildClassicalFrontierCoreData
   │   │       └─> Hlocal. localExistence for all admissible initial data
   │   └─> Hlocal
   ├─> α/boundary positivity redesign if theorem keeps current assumptions
   │   └─> B/C/D/E
   └─> statement-level theorem correctness

Hlocal
   ├─> G. IntervalDomainUniformLocalExistence
   └─> final γ≥1 wrapper

F. Remove/thread hposWit
   └─> final γ≥1 wrapper

G. IntervalDomainUniformLocalExistence
   └─> final γ≥1 wrapper

Final:
  Theorem_1_1_intervalDomain_via_regime_gammaGeOne_no_hextend_mge
  or a new no-hposWit variant
```

If the target theorem is restated as a direct implication:

```lean
theorem Theorem_1_1_intervalDomain_unconditional_gammaGeOne
    (p : CM2Params) (hγ_ge_one : 1 ≤ p.γ) :
    Theorem_1_1 intervalDomain p
```

then the proof will still internally introduce `hχ`, `ha`, `hb` from
`Theorem_1_1` and route through the γ ≥ 1 wrapper.

## 6. Risk Assessment

Highest risk: current initial datum formalization.

The combination of `PositiveInitialDatum = bounded + interior positivity` and
sup-norm `InitialTrace` is probably too broad.  A discontinuous bounded positive
datum should not be the uniform trace of positive-time C2 slices.  If this is
not fixed, the target may be unprovable because it is false.

High risk: α regime.

Current local Picard proof uses `1 ≤ p.α`.  The formal `CM2Params` only has
`0 < p.α`, and `Theorem_1_1` does not assume `1 ≤ p.α`.  For `0 < α < 1`, the
reaction is not Lipschitz on a nonnegative ball touching zero.  A different
path space with a positive lower bound, or a different fixed-point theorem, is
needed.  This is not a tactic issue.

High risk: `GradientMildHalfStepLogisticSourceData` for the full chemotaxis
equation.

The logistic-source half-step package cannot by itself represent the
chemotaxis gradient-Duhamel contribution when `χ₀ ≠ 0`.  If no separate
gradient-Duhamel regularity package is added, the `hagree` field is likely
false for the full equation.

High risk: `GradientMildClassicalFrontierCoreData`.

This is the real parabolic regularity theorem: deriving the PDE, time
derivatives, and joint continuity from a weak gradient-form mild fixed point.
Mathlib will not have this as a black box.  Existing files provide atoms, not
the assembled theorem.

Medium/high risk: uniform local continuation.

`IntervalDomainUniformLocalExistence` is a strong finite-horizon continuation
input.  It can probably be proved only after a quantitative local theorem,
a priori bounds, endpoint/restart compactness, and gluing are all in place.

Medium risk: uniform semigroup initial trace.

This is standard but not currently available in the needed sup-norm form.
Pointwise spectral approximate identity is already present but too weak.

Low risk: exporting `GradientMildSolutionData`.

This is straightforward refactoring/wiring if the current Picard theorem
continues to compile.

Low/medium risk: eliminating `hposWit`.

The standalone statement is suspect, but threading the original `hu₀` through
the gluing chain should be mostly proof engineering.

## 7. Short Honest Path

The shortest honest path is not "two lemmas".  It is:

1. Decide/fix the initial-data predicate and α regime.
2. Export `GradientMildSolutionData` from Picard.
3. Prove sup-norm initial approach.
4. Add a chemotaxis-aware post-hoc regularity package for the gradient mild
   fixed point.
5. Prove `GradientMildClassicalFrontierCoreData`.
6. Obtain `hlocal`.
7. Prove or replace `IntervalDomainUniformLocalExistence`.
8. Thread away `hposWit`.
9. Call the γ ≥ 1 Paper2 umbrella.

Items 1, 4, 5, and 7 are the likely hard blockers.
