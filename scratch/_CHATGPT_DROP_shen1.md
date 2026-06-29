# Q2241 canonical-`K` compactness wrapper feasibility audit

Audited current `main` around `e3aa461e`, focusing on `ShenWork/Paper3/IntervalDomainStatementAssembly.lean`, `CompactnessData`, `intervalDomainStabilityNorms`, `IntervalDomainPaper3ConcreteCompactnessRegularizationData`, and `intervalDomain_Lemma_3_4_of_upperEnvelope_eq_supNorm`.

## 1. Existing canonical `K` / stability-norm object

There is an existing canonical stability-norm object:

`intervalDomainStabilityNorms : StabilityNorms intervalDomain`

Its `xpSigmaDistance` is definitionally the concrete interval sup-distance, and the file has simp lemmas such as `intervalDomainStabilityNorms_xpSigmaDistance` and the bridge `intervalDomainStabilityNorms_supControlsXpSigmaDistance`.

But this is not a `CompactnessData intervalDomain` object. `CompactnessData` is a separate structure with exactly these fields:

```lean
structure CompactnessData (D : BoundedDomainData) where
  locallyConverges :
    (ℕ → ℝ → D.Point → ℝ) → (ℝ → D.Point → ℝ) → Prop
  upperEnvelope : (D.Point → ℝ) → ℝ
  neumannResolventGradientBound :
    (mu nu : ℝ) → (D.Point → ℝ) → ℝ → Prop
```

I did not find an existing canonical `CompactnessData intervalDomain` value whose `upperEnvelope` is definitionally or theorem-wise equal to `intervalDomain.supNorm`. The current interval-domain concrete compactness route remains parameterized by an arbitrary `K : CompactnessData intervalDomain` and therefore carries

```lean
upperEq : ∀ f : intervalDomain.Point → ℝ,
  K.upperEnvelope f = intervalDomain.supNorm f
```

inside `IntervalDomainPaper3ConcreteCompactnessRegularizationData`.

## 2. Can pure wiring eliminate only `upperEq`?

Yes, but only by introducing a new local compactness-data factory that chooses `upperEnvelope := intervalDomain.supNorm` by construction. This is pure wiring: it does not prove compactness, initial continuity, minimal upper bounds, resolvent estimates, or stability. Those remain explicit fields.

Without such a new `K` factory, no: for an arbitrary `K`, Lemma 3.4 still needs either `upperEq` or an equivalent hypothesis. The existing theorem

`intervalDomain_Lemma_3_4_of_upperEnvelope_eq_supNorm`

is already the exact bridge: it proves `Lemma_3_4 intervalDomain p K` from `∀ f, K.upperEnvelope f = intervalDomain.supNorm f`. So `upperEq` cannot simply disappear from the arbitrary-`K` API.

## 3. Minimal Lean code if the wrapper is desired

Placement: `ShenWork/Paper3/IntervalDomainStatementAssembly.lean`, after `IntervalDomainPaper3ConcreteCompactnessRegularizationData` and the existing theorem `intervalDomain_paper3_concreteCompactnessRegularizationTargets_of_frontiers`, or just after the data structure if you prefer the new factory to appear before the target wrapper.

This code adds a canonical sup-envelope compactness-data factory and a parallel data record that omits only `upperEq`.

```lean
import ShenWork.Paper3.IntervalDomainStatementAssembly

open ShenWork.IntervalDomain
open ShenWork.Paper2

namespace ShenWork.Paper3

noncomputable section

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
record by filling `upperEq` with `rfl`. -/
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
  compact := by
    simpa [intervalDomainSupNormCompactnessData] using h.compact
  initialContinuity := h.initialContinuity
  minimalUpper := h.minimalUpper
  resolvent := by
    simpa [intervalDomainSupNormCompactnessData] using h.resolvent

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

end

end ShenWork.Paper3
```

If the goal is to eliminate `upperEq` all the way from a full Paper3 mainline route such as `IntervalDomainPaper3MainlineMoserActualLinearSmallCETerminalFrontierData`, a parallel mainline/frontier record would also be needed so that the route uses `intervalDomainSupNormCompactnessData locallyConverges neumannResolventGradientBound` instead of an arbitrary `K`. That is more code, but it is still a wrapper-layer change, not a new PDE theorem.

## 4. Risk classification

As an optional compactness-target wrapper, this is a local wrapper. It is low-risk because it adds a new route and reuses the existing theorem `intervalDomain_paper3_concreteCompactnessRegularizationTargets_of_frontiers`.

As a refactor of existing APIs to replace the arbitrary `K : CompactnessData intervalDomain` everywhere, it becomes invasive. It would touch the Paper3 mainline/frontier records and theorem signatures, and it would reduce generality. I would not do that unless the repository wants to standardize on the interval sup-envelope compactness package.

Recommended next edit: add the optional local wrapper above, or, if you want zero API expansion, just add a doc comment saying that `upperEq` is structural and can be eliminated only on a route that fixes `K.upperEnvelope := intervalDomain.supNorm` by construction. Do not remove `compact`, `initialContinuity`, `minimalUpper`, or `resolvent` from the exposed residual surface.
