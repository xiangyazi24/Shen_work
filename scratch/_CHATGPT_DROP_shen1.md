# CANONICAL-K-AUDIT-REQUEST

Audited current `main` around `e3aa461e`, focusing on `ShenWork/Paper3/IntervalDomainStatementAssembly.lean`, `CompactnessData`, `intervalDomainStabilityNorms`, `IntervalDomainPaper3ConcreteCompactnessRegularizationData`, and `intervalDomain_Lemma_3_4_of_upperEnvelope_eq_supNorm`.

## 1. Existing canonical `K` / stability-norm object

There is an existing canonical stability-norm object:

`intervalDomainStabilityNorms : StabilityNorms intervalDomain`

Its `xpSigmaDistance` is definitionally the concrete interval sup-distance, with the simp theorem:

`intervalDomainStabilityNorms_xpSigmaDistance`

and the control bridge:

`intervalDomainStabilityNorms_supControlsXpSigmaDistance`.

But this is not a `CompactnessData intervalDomain`. `CompactnessData` is a separate structure:

```lean
structure CompactnessData (D : BoundedDomainData) where
  locallyConverges :
    (ℕ → ℝ → D.Point → ℝ) → (ℝ → D.Point → ℝ) → Prop
  upperEnvelope : (D.Point → ℝ) → ℝ
  neumannResolventGradientBound :
    (mu nu : ℝ) → (D.Point → ℝ) → ℝ → Prop
```

I found no existing canonical `K : CompactnessData intervalDomain` whose `upperEnvelope` is definitionally or theorem-wise equal to `intervalDomain.supNorm`. The current concrete compactness data still quantifies over arbitrary `K` and therefore carries:

```lean
upperEq : ∀ f : intervalDomain.Point → ℝ,
  K.upperEnvelope f = intervalDomain.supNorm f
```

So the answer to “is there an existing canonical `K`?” is **no**. The answer to “can one be introduced as pure wiring?” is **yes**.

## 2. Can pure wiring eliminate only `upperEq`?

Yes, if the repo is willing to add a new wrapper route that fixes `K.upperEnvelope := intervalDomain.supNorm` by construction. This does not discharge any analytic residual. The following fields remain explicit:

- `compact : TimeTranslateCompactnessRaw intervalDomain p K.locallyConverges`
- `initialContinuity : IntervalDomainInitialContinuityRaw p`
- `minimalUpper : ... EventuallyUpperBoundMinimalConclusion ...`
- `resolvent : NeumannResolventGradientBoundExistsRaw intervalDomain K.neumannResolventGradientBound`

For arbitrary existing `K`, no pure theorem can remove `upperEq`: `intervalDomain_Lemma_3_4_of_upperEnvelope_eq_supNorm` needs exactly that equality to route Lemma 3.4 through the interval sup-norm max principle.

## 3. Minimal Lean code and placement

Placement: add this in `ShenWork/Paper3/IntervalDomainStatementAssembly.lean`, immediately after `IntervalDomainPaper3ConcreteCompactnessRegularizationData` and its current wrapper `intervalDomain_paper3_concreteCompactnessRegularizationTargets_of_frontiers`, or immediately after the data structure if you want the new factory before both wrappers.

If added in the same file, no new import is needed because the file already imports the required Paper3 and interval-domain infrastructure. As a standalone snippet, the required import is:

```lean
import ShenWork.Paper3.IntervalDomainStatementAssembly
```

In-place code:

```lean
/-- Compactness data on the interval with the upper envelope fixed to the
concrete interval sup norm.  The convergence relation and Neumann-resolvent
bound predicate remain parameters, so their analytic frontiers are not hidden. -/
def intervalDomainSupNormCompactnessData
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop) :
    CompactnessData intervalDomain where
  locallyConverges := locallyConverges
  upperEnvelope := intervalDomain.supNorm
  neumannResolventGradientBound := neumannResolventGradientBound

@[simp] theorem intervalDomainSupNormCompactnessData_upperEnvelope
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop)
    (f : intervalDomain.Point → ℝ) :
    (intervalDomainSupNormCompactnessData
      locallyConverges neumannResolventGradientBound).upperEnvelope f =
      intervalDomain.supNorm f :=
  rfl

/-- Concrete-constants compactness/regularization data for the canonical
sup-envelope compactness package.  This removes only the structural `upperEq`
field; the analytic compactness, initial-continuity, minimal-upper, and
resolvent frontiers remain explicit. -/
structure IntervalDomainPaper3SupNormCompactnessRegularizationData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop) : Prop where
  compact :
    TimeTranslateCompactnessRaw intervalDomain p locallyConverges
  initialContinuity : IntervalDomainInitialContinuityRaw p
  minimalUpper :
    p.a = 0 → p.b = 0 → p.m = 1 → 1 ≤ p.β →
      0 < p.χ₀ → p.χ₀ < min (chiBeta p / 2) (Real.sqrt (chiBeta p)) →
        ∀ u v : ℝ → intervalDomain.Point → ℝ,
          PositiveGlobalBoundedSolution intervalDomain p u v →
            EventuallyUpperBoundMinimalConclusion intervalDomain p
              (intervalDomainPaper3Constants p M0 uBar vLower) u
  resolvent :
    NeumannResolventGradientBoundExistsRaw intervalDomain
      neumannResolventGradientBound

/-- Convert the sup-envelope compactness data to the existing concrete data
record by filling `upperEq` definitionally. -/
def IntervalDomainPaper3SupNormCompactnessRegularizationData.toConcrete
    {p : CM2Params} {M0 uBar vLower : ℝ}
    {locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop}
    {neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop}
    (h : IntervalDomainPaper3SupNormCompactnessRegularizationData
      p M0 uBar vLower locallyConverges neumannResolventGradientBound) :
    IntervalDomainPaper3ConcreteCompactnessRegularizationData
      p M0 uBar vLower
      (intervalDomainSupNormCompactnessData
        locallyConverges neumannResolventGradientBound) where
  upperEq := by
    intro f
    rfl
  compact := h.compact
  initialContinuity := h.initialContinuity
  minimalUpper := h.minimalUpper
  resolvent := h.resolvent

/-- Compactness/regularization targets for the canonical sup-envelope
compactness package.  This is only a wrapper; it does not discharge the analytic
compactness, initial-continuity, minimal-upper, or resolvent residuals. -/
theorem
    intervalDomain_paper3_concreteCompactnessRegularizationTargets_of_supNormData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop)
    (hData : IntervalDomainPaper3SupNormCompactnessRegularizationData
      p M0 uBar vLower locallyConverges neumannResolventGradientBound) :
    IntervalDomainPaper3CompactnessRegularizationTargets p
      (intervalDomainSupNormCompactnessData
        locallyConverges neumannResolventGradientBound)
      intervalDomainStabilityNorms
      (intervalDomainPaper3Constants p M0 uBar vLower) :=
  intervalDomain_paper3_concreteCompactnessRegularizationTargets_of_frontiers
    p M0 uBar vLower
    (intervalDomainSupNormCompactnessData
      locallyConverges neumannResolventGradientBound)
    hData.toConcrete
```

This code eliminates only the structural equality field on the new route. It does not alter the existing arbitrary-`K` theorem and does not claim compactness, continuity, minimal upper bounds, or Neumann resolvent estimates.

## 4. Risk classification

As an additive wrapper, this is **local and low risk**. It adds a canonical sup-envelope route and leaves the current arbitrary-`K` API untouched.

As a refactor that replaces `K : CompactnessData intervalDomain` throughout existing Paper3 mainline/frontier records, it becomes **invasive**. It would change theorem signatures, reduce generality, and force downstream code to use the chosen sup-envelope compactness package.

Recommended action: add the optional local wrapper above if the repo wants a clearer route with `upperEq` discharged by construction. Otherwise, use only a doc/comment cleanup saying that `upperEq` is structural and can be removed only on a route that fixes `K.upperEnvelope := intervalDomain.supNorm`; do not hide the four analytic residuals.
