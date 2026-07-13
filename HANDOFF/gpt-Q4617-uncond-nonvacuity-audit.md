ANSWER Q4617 5fd615a0

# Second vacuity audit: the unconditional positive-critical theorem is genuinely inhabited

## Executive verdict

**PASS, with one important scope qualification.** The newly committed theorems do not inherit the fatal vacuity of the former `hglobalExtension` wrapper. The local solution is constructed by an actual closed-ball B-form Picard iteration, the continuation argument produces arbitrarily long certified classical branches, and the global pair is obtained by an overlap-compatible gluing theorem which re-proves `IsPaper2ClassicalSolution` on every finite horizon.

The exact results of the four requested checks are:

| Audit item | Verdict |
|---|---|
| (1) Local existence | **CONFIRM non-vacuous for every `PaperPositiveInitialDatum`.** There is an actual positive-time Picard fixed point and a proved regularity bootstrap to `IsPaper2ClassicalSolution`. There is no assumed mild-solution object. **Scope correction:** this is not a theorem for the weaker `PositiveInitialDatum`; it is PPID-typed, exactly as the committed headline states. |
| (2) Global construction | **CONFIRM genuine.** `positiveCritical_reachableArbitrarilyLong_geOne` constructs certified branches past every positive horizon, and `GlobalSolutionGluingFromReachability_of_overlapUnique` builds one pair which is classical on every `T > 0`. It does not assert that an arbitrary finite-horizon tail is global. |
| (3) Finite branch | **CONFIRM genuine contradiction.** `Paper2MaximalContinuation` is a real two-constructor inductive type and its `.global` constructor is explicitly inhabited. A `.finite` branch is eliminated by a produced finite-horizon bound plus its own `mge` blow-up field. `not_mgeOneFiniteHorizonAlternative_of_pointwiseBoundedBefore` is an elementary, non-vacuous contradiction. |
| (4) Parameter class | **CONFIRM nonempty.** Take `N=1`, `α=γ=m=μ=ν=a=b=β=1`, `χ₀=1/2`. Then `chiBeta=1`, so `0<χ₀<chiBeta`; all remaining hypotheses hold. The datum `u₀≡1` is PPID and the constant pair `u≡1`, `v≡1` is an explicit global bounded classical solution. |

Thus I find **no remaining empty-hypothesis or degenerate-witness defect** in the current theorem. The old impossible arbitrary-extension premise has genuinely disappeared.

Two limitations should not be blurred into the word “unconditional”:

1. the theorem is unconditional only **inside the stated `α≥1`, `γ≥1`, positive-critical parameter regime**;
2. its datum quantifier is `PaperPositiveInitialDatum`, meaning a continuous bounded datum with a uniform positive floor on the closed interval, not the weaker interior-only `PositiveInitialDatum`.

Neither limitation is vacuity; both classes are explicitly nonempty.

---

# 0. Audited source snapshot

The main fetched file on `chatgpt-scratch` was:

```text
ShenWork/Paper2/IntervalDomainTheorem12PositiveCriticalUnconditional.lean
blob SHA d1fea2a1d405df16464950029b88fe8b33de13fb
```

The load-bearing dependencies inspected include:

```text
ShenWork/Paper2/IntervalChiNegV6Headline.lean
blob SHA abe3d65bb7ae32ddf7ce9c2dca4299e63af42a34

ShenWork/Paper2/IntervalChiNegV6DirectClassical.lean
blob SHA 4923bc869303c462a51a41f52891205119942a24

ShenWork/Paper2/IntervalUniformConjugateCore.lean
blob SHA 1998365b9c718f64dc30b0080d080cad71a6e001

ShenWork/Paper2/IntervalConjugatePicard.lean
blob SHA 578c0709b706fe3d080e2ebf5485eed9bdac7a1a

ShenWork/Paper2/IntervalUniformTruncatedMapCertificateDatum.lean
blob SHA eab10160dc1ad478495d38b2a09893af74871936

ShenWork/Paper2/IntervalDomainTheorem11CorePath.lean
blob SHA bb95775a2a5ba5fe5ddb16bfb2e003a6d3d9d1e5

ShenWork/Paper2/IntervalDomainTheorem11StrongPath.lean
blob SHA aafee98b89c16412ef85154dcd1c552aff78b65b

ShenWork/Paper2/IntervalDomainRestartedLpLinfProducer.lean
blob SHA 79a8a9619930c6c2b2df15a3a9e1a060cac02fe2

ShenWork/PDE/IntervalDomainExistence.lean
blob SHA dd22a347f7e983f8995882306563ab04d60eb322

ShenWork/Paper2/Statements.lean
blob SHA 8fc1d58d4121dac343f92b4261cf565a16b016ac
```

This was a source-level audit of the connector-visible current branch. The question already reports the clean `#print axioms` result; the issue audited here is whether the types used by that proof are inhabited.

---

# 1. Local existence is actually constructed

## 1.1 Exact scope: arbitrary PPID, not arbitrary weak PID

The committed local producer is, in `IntervalDomainTheorem12PositiveCriticalUnconditional.lean` lines 45–63:

```lean
theorem positiveCriticalLocalExistence_geOne
    (p : CM2Params) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ) :
    ∀ u₀ : intervalDomainPoint → ℝ,
      PaperPositiveInitialDatum intervalDomain u₀ →
        ∃ T > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
          IsPaper2ClassicalSolution intervalDomain p T u v ∧
          InitialTrace intervalDomain u₀ u
```

This quantifies over every `PaperPositiveInitialDatum`. In `Statements.lean`, that predicate is the genuinely nonempty condition

```lean
def PaperPositiveInitialDatum (D : BoundedDomainData)
    (u₀ : D.Point → ℝ) : Prop :=
  D.initialAdmissible u₀ ∧
    ∃ η : ℝ, 0 < η ∧ ∀ x : D.Point, η ≤ u₀ x
```

On the interval, the admissibility component supplies boundedness and continuity; the second component supplies a uniform positive floor on the closed domain.

This is broader than constant data. For example,

```text
u₀(x) = 1 + x(1-x)/4,     0 ≤ x ≤ 1,
```

is continuous, bounded, nonconstant, and satisfies `u₀(x) ≥ 1`. It therefore lies in the quantified class.

However, PPID is strictly stronger than the repository’s weak

```lean
PositiveInitialDatum intervalDomain u₀
```

which asks only for positivity on the open interior and permits a zero boundary floor. Therefore:

> **The actual theorem covers arbitrary paper-positive data, not every weak PID.**

That is a scope restriction, not an empty class. The committed theorem itself is correctly PPID-typed.

## 1.2 The local producer DAG

The construction in the target file is:

```text
uniformTruncatedV6AssemblyInputs_producer
  + uniformConjugateMildExistenceCore_exists
  + uniformTruncatedConjugateMapCertificateData_producer
  + uniformTruncatedEnergyDataV6_producer
  + uniformTruncatedJensenStrictPosDataV6_producer
        ↓
chiNegDatumUniformCore_v6
        ↓
ppid_of_uniformCore
        ↓
positiveCriticalQuantitativeLocalPPID_geOne
        ↓
positiveCriticalLocalExistence_geOne
```

The historical `chiNeg` names do not impose `χ₀<0` here. The relevant declarations have no sign hypothesis, and their estimates use `|p.χ₀|`. This makes the local construction genuinely usable at positive sensitivity.

### Target wrapper

At lines 35–42 of the new file:

```lean
def positiveCriticalQuantitativeLocalPPID_geOne
    (p : CM2Params) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ) :
    ChiNegDatumUniformConstructionPPID p :=
  ShenWork.ppid_of_uniformCore
    (chiNegDatumUniformCore_v6 p hα hγ
      (uniformTruncatedV6AssemblyInputs_producer p hα hγ))
```

The type `ChiNegDatumUniformConstructionPPID p` is the quantitative statement

```lean
∀ M > 0, ∃ δ > 0,
  ∀ {u₀}, PaperPositiveInitialDatum intervalDomain u₀ →
    (∀ x, |u₀ x| ≤ M) →
      ∃ u v,
        IsPaper2ClassicalSolution intervalDomain p δ u v ∧
        InitialTrace intervalDomain u₀ u
```

The time `δ` is chosen before the datum under a fixed outer bound `M`, and is explicitly positive.

## 1.3 The Banach object is real, not an assumed mild-solution package

The successful construction does **not** use the old logistic-only

```lean
intervalDuhamelOperator
```

as its main map. It uses the full conjugate B-form map

```lean
intervalConjugateDuhamelMap
```

and its faithful truncated-positive-part variant. This distinction matters: the chemotaxis divergence is represented through the conjugate derivative-kernel operator, not omitted.

In `IntervalConjugatePicard.lean`, the iterates are actual definitions:

```lean
def conjugatePicardIter ...
  | 0 => fun t x =>
      intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
  | n + 1 => fun t x =>
      intervalConjugateDuhamelMap p u₀
        (conjugatePicardIter p u₀ n) t x
```

and the limit is

```lean
def conjugatePicardLimit ... :=
  if 0 < t ∧ t ≤ T then
    atTop.limUnder (fun n => conjugatePicardIter p u₀ n t x)
  else 0
```

The file proves:

```text
conjugatePicardIter_pointwise_convergent
conjugatePicardIter_pointwise_tail_bound
conjugatePicardIter_uniform_convergence
conjugatePicardLimit_bounded
conjugatePicardLimit_nonneg
conjugatePicardLimit_hasContinuousSlices
conjugatePicardLimit_is_mildSolution
```

In particular, `conjugatePicardLimit_is_mildSolution` proves the fixed-point identity by combining the geometric tail bound with the contraction estimate and sending the tail to zero. The fixed-point equation is not a field assumed from the caller.

## 1.4 The small-time conditions are jointly satisfiable

`IntervalUniformConjugateCore.lean` defines the explicit core record

```lean
structure UniformConjugateMildExistenceCore ... where
  T M0 R K ... : ℝ
  hT   : 0 < T
  hM0  : 0 < M0
  hR   : 0 < R
  hK   : K < 1
  hK_nn : 0 ≤ K
  ...
  hmapsTo_budget :
    M0 + (|χ₀| * Cgrad * 2√T * CQsup + T * CLsup) ≤ R
  hcontr :
    |χ₀| * Cgrad * 2√T * CQ + T * CL < 1
```

The producer `uniformConjugateMildExistenceCore_exists`, lines 114–273, sets

```text
R = 2M,
```

constructs finite nonnegative constants `CQ`, `CQsup`, `CL`, and `CLsup`, and chooses `T>0` through

```lean
exists_small_contraction_time_target
```

so that the expression of the form

```text
A √T + B T
```

is simultaneously below the contraction threshold and below the spare ball budget. It then constructs every field of `UniformConjugateMildExistenceCore` explicitly. In particular,

```lean
K = |p.χ₀| * (Cgrad * 2√T * CQ) + T * CL
```

is proved nonnegative and strictly below one.

This avoids the classic closed-ball vacuity bug `Mρ + nonlinear ≤ ρ` with the same radius on both sides: the datum radius is `M` while the trajectory radius is `R=2M`, leaving a real half-ball budget.

## 1.5 The truncated map certificate is also produced

`uniformTruncatedConjugateMapCertificateData_producer` is not a carried frontier. In `IntervalUniformTruncatedMapCertificateDatum.lean` it is assembled from:

```text
uniformTruncatedSourceSupBudgetRealization_of_uniformCore
uniformTruncatedDuhamelDifferenceCertificate_of_uniformCore
uniformTruncatedConjugateMapCertificateData_of_realizations
```

The chemotaxis and logistic Duhamel difference estimates are proved from the uniform core’s concrete constants. There is no externally supplied proposition asserting that the map is contractive.

Likewise `uniformTruncatedV6AssemblyInputs_producer` packages three proved producers:

```lean
mapCertificate := uniformTruncatedConjugateMapCertificateData_producer hα hγ
energy         := uniformTruncatedEnergyDataV6_producer p
jensenStrictPos := uniformTruncatedJensenStrictPosDataV6_producer p Hmap
```

## 1.6 Mild-to-classical closure is not assumed

`chiNegDatumUniformCore_v6`, in `IntervalChiNegV6DirectClassical.lean` lines 76–118, performs the actual closure:

1. obtains a positive common lifespan `T` and concrete uniform core `C`;
2. constructs the faithful map certificate, negative-part energy package, and strict-positivity/Jensen package;
3. builds
   ```lean
   S : ConjugateMildSolutionData p u₀
   ```
   with `conjugateMildSolutionData_of_truncatedEnergyJensen_v6`;
4. proves `InitialTrace intervalDomain u₀ S.u`;
5. proves the direct joint time derivative and reduced classical core with
   ```lean
   conjugateMild_reducedClassicalCore_direct
   ```;
6. returns a genuine
   ```lean
   CoupledDuhamelReducedClassicalCore p T u₀ S.u.
   ```

Then `ppid_of_uniformCore`, in `IntervalDomainTheorem11CorePath.lean` lines 46–59, invokes

```lean
regularityBootstrap_of_coupledDuhamel_reducedClassicalCore
```

and constructs

```lean
IsPaper2ClassicalSolution.of_components hδ
  hclassreg hpos hvnn hpde_u hpde_v hbc
```

with the actual PDE, elliptic equation, positivity, nonnegative signal, Neumann boundary conditions, full classical regularity, and initial trace.

There is therefore no hypothesis of the form

```text
“assume a mild solution satisfying all desired properties exists.”
```

The mild object and its regularity are outputs of prior theorems.

## 1.7 Why the output cannot be a constant witness for arbitrary data

For nonconstant `u₀`, a constant-in-space trajectory cannot satisfy the repository’s `InitialTrace` in sup norm. The factory’s output explicitly carries

```lean
InitialTrace intervalDomain u₀ u.
```

Moreover, the zeroth Picard iterate contains

```lean
intervalFullSemigroupOperator t (intervalDomainLift u₀),
```

so the construction genuinely depends on the input datum.

### Verdict on (1)

**CONFIRM non-vacuous**, with the precise wording:

> `positiveCriticalLocalExistence_geOne` produces a genuine positive-horizon classical solution for every **paper-positive** datum. It does not merely cover equilibrium data, does not assume a mild-solution-data predicate, and has no always-false premise.

**Refute only the broader paraphrase** “for every weak `PositiveInitialDatum`”: that is not the theorem’s type.

---

# 2. The global solution is genuinely glued on every finite horizon

## 2.1 Overlap uniqueness is internally produced

The global gluing needs compatibility of finite-horizon witnesses. The new file does not assume uniqueness. It defines

```lean
def positiveCriticalOverlapUnique_geOne ... :
    IntervalClassicalSolutionOverlapUnique p :=
  IntervalClassicalSolutionOverlapUnique_of_l2EnergyMethod
    (intervalDomainClassicalUniquenessL2EnergyMethod_of_boundedDatumUniform p
      (intervalDomainL2UBoundedDatumUniform_of_bounded
        (boundednessHypothesis_of_uniformSupBoundZeroM hγ
          (positiveCriticalUniformLiftBoundZeroM_geOne ...))))
```

The input `positiveCriticalUniformLiftBoundZeroM_geOne` is itself produced by applying

```lean
critical_bounded_before_positive_restarted_affine_intervalDomain
```

to both finite classical solutions with the same initial trace. It does not rely on the later global theorem. Thus the use of uniqueness is not circular.

## 2.2 The one-step continuation is a real restart-and-glue construction

`positiveCritical_reachablePast_of_bounded_geOne` starts with:

```lean
hsol   : IsPaper2ClassicalSolution intervalDomain p T u v
htrace : InitialTrace intervalDomain u₀ u
hbdd   : IsPaper2BoundedBefore intervalDomain T u
```

It then:

1. extracts a uniform finite pointwise bound from `hbdd` and spatial boundedness of each classical slice;
2. obtains a quantitative local lifespan `δ>0` from the same local PPID factory;
3. if `T ≤ δ/2`, starts a fresh solution from `u₀` whose lifespan already exceeds `T`;
4. otherwise sets
   ```text
   τ = T - δ/4;
   ```
5. proves the restart slice is paper-positive via
   ```lean
   UniformContinuation.classicalSolution_slice_paperPositiveInitialDatum;
   ```
   this uses closed-domain positivity and compactness to obtain a uniform positive minimum;
6. launches a new classical solution `(w,z)` from `u(τ)` on `(0,δ)`;
7. time-shifts the old branch and proves equality with `(w,z)` on their overlap using `positiveCriticalOverlapUnique_geOne`;
8. invokes
   ```lean
   PiecewiseClassical.piecewiseClassicalWorks
   ```
   to certify the piecewise pair on
   ```text
   T' = T + δ/2 > T;
   ```
9. proves the piecewise pair retains the original initial trace.

This produces `ReachablePast p u₀ T` by constructing an actual larger reachable horizon. It is not a proposition saying merely that extension “ought to exist.”

## 2.3 Arbitrarily long reachability is proved by a genuine bounded/unbounded split

`positiveCritical_reachableArbitrarilyLong_geOne`, lines 233–272 of the target file, proves

```lean
ReachableArbitrarilyLong p u₀
```

where

```lean
def ReachableArbitrarilyLong ... : Prop :=
  ∀ T > 0, ReachableClassicalHorizon p u₀ T
```

and a reachable horizon explicitly contains a classical pair and initial trace.

The proof splits on

```lean
BddAbove (reachableClassicalHorizonSet p u₀).
```

### Unbounded case

If the set is not bounded above, `reachableArbitrarilyLong_of_not_bddAbove` chooses a reachable horizon above any prescribed `T` and restricts that genuine solution down to `T`.

### Bounded case

If it is bounded above, the proof:

1. obtains one local reachable horizon, so the set is nonempty;
2. lets `T*` be `finiteMaximalReachableHorizon`, the supremum of reachable horizons;
3. constructs
   ```lean
   boundedReachableGluedU hbdd hne
   boundedReachableGluedV hbdd hne;
   ```
4. proves they form an actual classical solution at horizon `T*` via
   ```lean
   boundedReachableGlued_isPaper2ClassicalSolution_of_overlapUnique;
   ```
5. proves the original initial trace;
6. applies the positive-critical finite-horizon a priori bound;
7. applies `positiveCritical_reachablePast_of_bounded_geOne` to extend past `T*`;
8. contradicts
   ```lean
   not_reachablePast_finiteMaximalReachableHorizon hbdd.
   ```

The “solution at the supremum” is not an endpoint compactness fiction. The formal classical predicate only asks for properties on the open time interval `(0,T*)`. At each interior time the glued pair agrees with a genuine reachable witness on a larger horizon, and overlap uniqueness makes the choices compatible.

## 2.4 The final global gluing theorem checks every `T>0`

The decisive theorem in `PDE/IntervalDomainExistence.lean` is:

```lean
theorem GlobalSolutionGluingFromReachability_of_overlapUnique
    (huniq : IntervalClassicalSolutionOverlapUnique p) :
    GlobalSolutionGluingFromReachability p
```

Its underlying theorem `..._of_overlapUnique_and_locality` defines

```lean
u := reachableArbitrarilyLongGluedU hreach
v := reachableArbitrarilyLongGluedV hreach
```

and proves global classicality by:

```lean
intro T hT
let dT : ReachableClassicalSolutionData p u₀ T :=
  reachableClassicalSolutionDataOfReach (hreach T hT)
refine hlocality hT dT.sol ?_
intro t ht0 htT x
exact reachableArbitrarilyLongGlued_eq_reachableData_of_overlapUnique
  huniq hu₀ hreach dT t ht0 htT x
```

Thus, for **each** `T>0`, the glued pair agrees throughout `(0,T)` with an actual certified finite-horizon solution, and the locality theorem transfers every field of `IsPaper2ClassicalSolution`.

This is exactly the definition

```lean
def IsPaper2GlobalClassicalSolution ... : Prop :=
  ∀ T > 0, IsPaper2ClassicalSolution D p T u v.
```

It is not the old invalid rule “the same arbitrary total functions supplied on `(0,Tmax)` are automatically global.”

Values outside positive time may be arbitrary implementation values, as usual for a total-function encoding, but every positive time lies in some certified finite horizon. Consequently the PDE, elliptic equation, positivity, regularity, and Neumann conditions hold wherever the global predicate asks for them.

## 2.5 `positiveCriticalGlobalSolution_geOne`

The target theorem, lines 274–299, is now a short honest assembly:

```lean
have huniq := positiveCriticalOverlapUnique_geOne ...
have hreach := positiveCritical_reachableArbitrarilyLong_geOne ...
obtain ⟨u,v,hglobal,htrace⟩ :=
  (GlobalSolutionGluingFromReachability_of_overlapUnique huniq)
    u₀ hu₀.toPositive hreach
have hbounded :=
  critical_bounded_global_positive_restarted_affine_intervalDomain ...
exact ⟨u,v,hglobal,htrace,hbounded⟩
```

The global bound is also produced rather than assumed: its finite `L^P` input comes from the critical seed/bootstrap chain audited in Q4614.

### Verdict on (2)

**CONFIRM genuinely non-vacuous.** The construction supplies one pair satisfying the full `∀T>0` global classical predicate. It is neither an arbitrary extension nor a constant placeholder. For nonconstant `u₀`, the retained initial trace alone rules out the equilibrium-placeholder interpretation.

---

# 3. The finite maximal-continuation branch is eliminated analytically

## 3.1 `Paper2MaximalContinuation` is a genuine sum type

In `Statements.lean`, the exact declaration is:

```lean
inductive Paper2MaximalContinuation
    (D : BoundedDomainData) (p : CM2Params) (u₀ : D.Point → ℝ) : Type
  | finite
      (Tmax : ℝ) (u v : ℝ → D.Point → ℝ)
      (Tmax_pos : 0 < Tmax)
      (solution : IsPaper2ClassicalSolution D p Tmax u v)
      (initialTrace : InitialTrace D u₀ u)
      (alternative : FiniteHorizonAlternative D Tmax u)
      (mge : 1 ≤ p.m → MGeOneFiniteHorizonAlternative D Tmax u)
  | global
      (u v : ℝ → D.Point → ℝ)
      (solution : IsPaper2GlobalClassicalSolution D p u v)
      (initialTrace : InitialTrace D u₀ u)
```

The finite constructor is not defined using `False`, an empty subtype, or a contradictory equality. It asks for the standard finite maximal-time data. Whether such data exist is an analytic question.

The global constructor is explicitly inhabited in the new theorem:

```lean
⟨Paper2MaximalContinuation.global u v hglobal htrace⟩
```

Therefore both

```lean
Nonempty (Paper2MaximalContinuation intervalDomain p u₀)
```

and the subsequent universal quantification over `branch` have a genuinely inhabited domain.

The branch predicates are also substantive:

```lean
IsGlobal (.finite ..) = False
IsGlobal (.global ..) = True

IsBounded (.finite Tmax u ..) = IsPaper2BoundedBefore D Tmax u
IsBounded (.global u ..) = IsPaper2Bounded D u
```

So proving `branch.IsGlobal` for all branches really proves that no finite branch exists in the target regime.

## 3.2 Exact finite-branch contradiction in the target

For a hypothetical constructor

```lean
.finite T U V hT hsol htr halt hmge
```

`correctedTheorem12_positiveCriticalBranch_unconditional_geOne` performs:

```lean
have hbdd : IsPaper2BoundedBefore intervalDomain T U :=
  critical_bounded_before_positive_restarted_affine_intervalDomain ...

have hcontrols : SupNormControlsPointwiseBefore T U :=
  supNormControlsPointwiseBefore_of_bddAbove_abs
    (fun t ht0 htT =>
      classicalSolution_u_range_bddAbove hsol ⟨ht0,htT⟩)

have hpw : PointwiseBoundedBefore T U :=
  pointwiseBoundedBefore_of_boundedBefore_and_supNormControls
    hbdd hcontrols

have hfalse : False :=
  (not_mgeOneFiniteHorizonAlternative_of_pointwiseBoundedBefore hpw)
    (hmge (by rw [hm]))
```

Each step is inhabited:

* `hbdd` is the produced positive-critical finite-horizon bound;
* `classicalSolution_u_range_bddAbove` follows from the spatial regularity of the genuine classical slice;
* the concrete supremum therefore controls each point;
* `hmge (by rw [hm])` is the finite branch’s own upper-blow-up alternative, specialized using `p.m=1`.

The ordinary `alternative : FiniteHorizonAlternative ...` field is not needed; the sharper `mge` field is enough.

## 3.3 The contradiction lemma has no hidden premise

In `PDE/IntervalDomainExistence.lean`, the definitions are:

```lean
def PointwiseBoundedBefore (T : ℝ)
    (u : ℝ → intervalDomain.Point → ℝ) : Prop :=
  ∃ M, ∀ t x, 0 < t → t < T →
    x ∈ intervalDomain.inside → u t x ≤ M


def MGeOneFiniteHorizonAlternative ... : Prop :=
  ∀ M, ∃ t x, 0 < t ∧ t < Tmax ∧
    x ∈ D.inside ∧ M < u t x
```

and the proof of the negation is literally:

```lean
theorem not_mgeOneFiniteHorizonAlternative_of_pointwiseBoundedBefore
    (hbounded : PointwiseBoundedBefore T u) :
    ¬ MGeOneFiniteHorizonAlternative intervalDomain T u := by
  intro hblow
  rcases hbounded with ⟨M, hM⟩
  rcases hblow M with ⟨t,x,ht0,htT,hx,hlt⟩
  exact not_lt_of_ge (hM t x ht0 htT hx) hlt
```

There is no integrability, differentiability, sign, or nonemptiness premise hiding here. The same number `M` is simultaneously the upper bound and the level the blow-up alternative must exceed.

### Verdict on (3)

**CONFIRM genuine.** The carrier type is inhabited by the constructed global branch; the finite constructor is not definitionally empty; and any finite inhabitant under the theorem’s hypotheses is ruled out by a concrete a priori-bound contradiction.

---

# 4. The parameter and datum classes are explicitly nonempty

## 4.1 Concrete parameter witness

Take the following `CM2Params` values:

```text
N   = 1
α   = 1
γ   = 1
m   = 1
μ   = 1
ν   = 1
χ₀  = 1/2
a   = 1
b   = 1
β   = 1
```

All structure-side positivity/nonnegativity fields are immediate. The theorem-side hypotheses are:

```text
1 ≤ α              true
1 ≤ γ              true
a = 0 ∨ 0 < b      true by the right disjunct
0 < χ₀             0 < 1/2
1 ≤ β              true
m = 1              true
```

The threshold is

```text
chiBeta
 = 2(2β-1) / max(2, γN)
 = 2(2·1-1) / max(2,1·1)
 = 2/2
 = 1.
```

Hence

```text
0 < χ₀ = 1/2 < 1 = chiBeta.
```

A Lean-shaped witness is:

```lean
def q4617Params : CM2Params where
  N := 1
  hN := by norm_num
  α := 1
  hα := by norm_num
  γ := 1
  hγ := by norm_num
  m := 1
  hm := by norm_num
  μ := 1
  hμ := by norm_num
  ν := 1
  hν := by norm_num
  χ₀ := (1 / 2 : ℝ)
  a := 1
  ha := by norm_num
  b := 1
  hb := by norm_num
  β := 1
  hβ := by norm_num
```

For this record, the external inequalities reduce by `norm_num [q4617Params, chiBeta]`.

## 4.2 Concrete datum witness

Take

```text
u₀(x) = 1.
```

It is continuous and bounded, and the floor witness `η=1` proves

```lean
PaperPositiveInitialDatum intervalDomain u₀.
```

A nonconstant witness is also available:

```text
u₀(x) = 1 + x(1-x)/4,
```

with the same floor `η=1`.

Thus the datum quantifier is far from empty.

## 4.3 Concrete global bounded solution witness

For the constant datum and the concrete parameters above, the positive logistic equilibrium is

```text
u* = (a/b)^(1/α) = 1,
v* = (ν/μ)(u*)^γ = 1.
```

Therefore

```text
u(t,x) = 1,
v(t,x) = 1
```

satisfies:

* all time and spatial derivatives vanish;
* the chemotaxis divergence vanishes;
* `u(a-bu^α)=1·(1-1)=0`;
* `-μv+νu^γ=-1+1=0`;
* both Neumann conditions hold;
* `u>0` and `v≥0`;
* the initial trace is exact;
* the sup norm is constantly one.

The repository already exposes the corresponding constructors:

```text
equilibrium_isPaper2ClassicalSolution
constantSolution_initialTrace
constantSolution_globalExistence
```

This independently demonstrates that the conclusion type is inhabited for a concrete parameter/data instance, even before invoking the new general Picard-and-continuation theorem.

### Verdict on (4)

**CONFIRM nonempty.** The theorem is not proving an implication over an empty parameter set, and its conclusion has an explicit classical model.

---

# 5. Consolidated dependency and vacuity ledger

| Potential vacuity point | Producer actually used | Audit result |
|---|---|---|
| Positive local lifespan | `uniformConjugateMildExistenceCore_exists` | Produces `T>0` from explicit `A√T+BT` small-time inequalities. |
| Closed Picard ball | Same theorem, with `R=2M` | Initial and trajectory radii are separated; maps-to and contraction budgets are jointly satisfiable. |
| Mild fixed point | `conjugatePicardIter`, `conjugatePicardLimit`, `conjugatePicardLimit_is_mildSolution` | Limit and fixed-point equation are proved, not assumed. |
| Chemotaxis included | `intervalConjugateDuhamelMap` and truncated B-form certificates | Full conjugate chemotaxis Duhamel leg is present; this is not the logistic-only toy map. |
| Sign of `χ₀` | Uniform core uses `|p.χ₀|`; local producer has no sign premise | Historical `chiNeg` naming does not make the positive branch impossible. |
| Positivity/untruncation | V6 energy + Jensen strict-positivity producers | Produced for PPID; no positivity field assumed from caller. |
| Mild-to-classical upgrade | `conjugateMild_reducedClassicalCore_direct` then `ppid_of_uniformCore` | Produces actual PDE, elliptic equation, boundary conditions, regularity, and trace. |
| Finite `L^P` bound | `exists_critical_lp_above_gamma` / global version | Internally produced; not a top-level assumption. |
| Overlap uniqueness | `positiveCriticalOverlapUnique_geOne` | Internally produced from the branch’s own finite bound and L² uniqueness machinery. |
| Extension past bounded horizon | `positiveCritical_reachablePast_of_bounded_geOne` | Constructs a restarted piecewise classical pair on a strictly longer horizon. |
| Arbitrarily long reachability | `positiveCritical_reachableArbitrarilyLong_geOne` | Proved by unbounded-set downward closure or contradiction at the finite supremum. |
| One global pair | `GlobalSolutionGluingFromReachability_of_overlapUnique` | For every `T>0`, transfers a real reachable solution through overlap equality and locality. |
| Finite maximal branch | A priori bound + `not_mgeOneFiniteHorizonAlternative_of_pointwiseBoundedBefore` | Direct contradiction at the same bound `M`; no impossible side premise. |
| Carrier nonemptiness | `.global u v hglobal htrace` | Explicitly inhabited. |
| Parameter class | Concrete `q4617Params` above | Explicitly inhabited, with `chiBeta=1` and `χ₀=1/2`. |
| Datum class | `u₀≡1`, or a nonconstant positive polynomial | Explicitly inhabited. |

---

# Final verdict

The second audit does **not** reproduce the defect found in Q4614.

The old theorem was vacuous because it assumed an impossible statement about every arbitrary total-function extension of a finite branch. The new theorem instead performs the mathematically appropriate operations:

```text
actual B-form local Picard solution
  → finite-horizon a priori bound
  → overlap uniqueness
  → restart and piecewise extension
  → arbitrarily long reachable horizons
  → canonical compatible gluing
  → one global classical solution
  → global restarted-Duhamel bound.
```

The maximal-continuation wrapper is also meaningful:

```text
one explicit global carrier exists,
and every hypothetical finite carrier contradicts its own m≥1 blow-up field.
```

Accordingly:

> **`Theorem_1_2_intervalDomain_positive_critical_branch_unconditional_geOne` and `correctedTheorem12_positiveCriticalBranch_unconditional_geOne` pass the vacuity/non-vacuity audit under their exact committed signatures.**

The honest residual qualifications are about **generality**, not vacuity: `α≥1`, `γ≥1`, and PPID data remain part of the theorem. Within that nonempty regime, the hypotheses and conclusions are genuinely inhabited.