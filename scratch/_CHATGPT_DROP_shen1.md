# Q2906 (shen1) — next frontier after anchoring: raw Moser-gradient time integrability

Repo: `xiangyazi24/Shen_work`  
Delivery branch: `chatgpt-scratch`  
Target files: `ShenWork/PDE/P3MoserEnergyContinuity.lean`, `ShenWork/PDE/P3MoserRegularityProducer.lean`, nearby Paper2/PDE Moser files  
Source edit requested: none; answer file only.

## Verdict

The remaining raw gradient time-integrability input for

```lean
intervalDomain_integratedMoserFirstCrossingRegularity_of_globalClassicalTraceAnchored
```

is still a **genuine analytic frontier**. It is not currently derivable from the visible proved classical/global/Picard/energy facts.

What anchoring solved:

```lean
u 0 = u₀      -- for the anchored representative
InitialTrace  -- preserved
Classical/global positive-time facts -- preserved
raw gradient time-integrability -> anchored gradient time-integrability -- by a.e. equality
```

What it did **not** solve:

```lean
∀ p, p0 ≤ p →
  IntegrableOn
    (fun t => intervalDomain.integral (fun x =>
      (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2))
    (Set.uIcc (0 : ℝ) T) volume
```

for the raw positive-time representative `u`.

The repo currently has wiring lemmas that consume either raw gradient time-integrability or the stronger closed-time gradient-energy continuity package, but I do not see a theorem producing these all-exponent Moser-gradient integrability facts from `IsPaper2GlobalClassicalSolution`, `InitialTrace`, `conjugatePicardLimit`, or the existing p=2 energy seed facts.

## Existing wiring already present

### `P3MoserIntegratedClosure.lean`

The main regularity structure explicitly requires gradient time-integrability:

```lean
structure IntegratedMoserFirstCrossingRegularity
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T p0 : ℝ) : Prop where
  ...
  gradientTimeIntegrable :
    ∀ p, p0 ≤ p →
      IntegrableOn
        (fun t =>
          D.integral (fun x =>
            (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2))
        (Set.uIcc (0 : ℝ) T) volume
```

So this is not cosmetic: the first-crossing Moser step consumes it as part of its regularity package.

### `P3MoserRegularityProducer.lean`

This file already has the only cheap conversion available:

```lean
theorem intervalDomain_gradientTimeIntegrable_of_gradientEnergyContinuous
    {T p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ}
    (hT : 0 ≤ T)
    (hgrad :
      ∀ p, p0 ≤ p →
        ContinuousOn
          (fun t =>
            intervalDomain.integral (fun x =>
              (intervalDomain.gradNorm
                (fun y => (u t y) ^ (p / 2)) x) ^ 2))
          (Set.Icc (0 : ℝ) T)) :
    ∀ p, p0 ≤ p →
      IntegrableOn
        (fun t =>
          intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm
              (fun y => (u t y) ^ (p / 2)) x) ^ 2))
        (Set.uIcc (0 : ℝ) T) volume
```

and the data-wrapper version:

```lean
theorem intervalDomain_gradientTimeIntegrable_of_gradientEnergyContinuityData
    {T p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ}
    (hT : 0 ≤ T)
    (hdata : IntervalDomainIntegratedMoserGradientEnergyContinuityData u T p0) :
    ∀ p, p0 ≤ p → ...
```

But `IntervalDomainIntegratedMoserGradientEnergyContinuityData` itself is not produced from current classical/Picard data; it is a stronger analytic input.

### `P3MoserLemmas.lean`

This file has useful p=2 seed regularity plumbing:

```lean
structure ClosedEnergyIdentityTraceData
...
theorem closedEnergyTrace_to_l2SeedRegularityFrontier
```

and `IntervalDomainClosedL2SeedBridge.to_frontier` in `IntervalDomainMoserActualAtoms.lean` packages p=2 closed energy data. This is not enough for the integrated first-crossing Moser regularity, which is indexed over **every** `p ≥ p0` and asks for the Moser-gradient energy of `u^(p/2)`, not just the L2 seed energy.

### `P3MoserDissipationShape.lean`

`IntegratedMoserDissipationDropBefore` contains an integral of the Moser gradient:

```lean
D.integral (fun x => (u t2 x) ^ p) -
    D.integral (fun x => (u t1 x) ^ p) +
  2 * ∫ s in t1..t2,
    D.integral (fun x =>
      (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2) ≤
  C * p * ∫ s in t1..t2,
    max 1 (D.integral (fun x => (u s x) ^ p))
```

But this is **not** a proof of `IntegrableOn` for the gradient integrand. In Lean, interval integrals are total; an inequality mentioning `∫` does not automatically give Bochner integrability of the integrand. The Moser first-crossing step separately asks for `hreg.gradientTimeIntegrable` exactly to avoid relying on an undefined/nonintegrable interval integral.

So do not try to derive raw gradient integrability merely by pointing at the integrated drop inequality.

## Why classical/global/Picard facts are insufficient as currently stated

`IsPaper2ClassicalSolution` gives positive-time regularity on every strict interior window. This should be enough, with some work, to prove local-in-time integrability on `[a,b] ⊆ (0,T)`. It is not enough for integrability all the way down to `0`.

The global solution interface gives classical solutions on every finite positive horizon, but still only at positive times. It does not include a near-zero estimate of the form

```lean
∫ t in 0..T, ∫ x, |∇(u(t)^(p/2))|^2 < ∞
```

nor a dominating bound such as `G_p(t) ≤ C t^{-α}` with `α < 1`.

The Picard/conjugate route proves deleted-right initial trace and positive-time mild/classical facts, but the visible B-form initial-trace files only prove sup-norm approach to `u₀`. They do not prove an H1/gradient-energy estimate near `t = 0` for all Moser exponents.

Thus the raw gradient time-integrability input is not just an artifact of anchoring; it is the next real analytic producer frontier.

## Search terms/files to inspect

Use these exact grep/search terms.

### Regularity consumer and cheap conversions

```text
ShenWork/PDE/P3MoserRegularityProducer.lean
```

Search:

```text
IntervalDomainIntegratedMoserGlobalClassicalRegularityData
IntervalDomainIntegratedMoserGradientEnergyContinuityData
intervalDomain_gradientTimeIntegrable_of_gradientEnergyContinuous
intervalDomain_gradientTimeIntegrable_of_gradientEnergyContinuityData
gradientTimeIntegrable
```

### First-crossing regularity requirement

```text
ShenWork/PDE/P3MoserIntegratedClosure.lean
```

Search:

```text
IntegratedMoserFirstCrossingRegularity
gradientTimeIntegrable
integratedMoser_gradientIntegral_le_of_endpoint_and_timeIntegral_bounds
```

### Integrated dissipation shape

```text
ShenWork/PDE/P3MoserDissipationShape.lean
```

Search:

```text
IntegratedMoserDissipationDropBefore
IntegratedMoserDissipationDropBeforeCoeff
integratedMoserDissipationDropBefore_of_integrated_energy
```

### p=2 seed only; not full Moser-gradient ladder

```text
ShenWork/PDE/P3MoserLemmas.lean
ShenWork/PDE/IntervalDomainMoserActualAtoms.lean
ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean
```

Search:

```text
ClosedEnergyIdentityTraceData
closedEnergyTrace_to_l2SeedRegularityFrontier
IntervalDomainClosedL2SeedBridge
IntervalDomainL2SeedRegularityFrontier
l2SeedRegularity
```

### Picard/conjugate source

```text
ShenWork/Paper2/IntervalConjugatePicard.lean
ShenWork/Paper2/IntervalBFormInitialTrace.lean
ShenWork/Paper2/IntervalBFormEndToEnd.lean
```

Search:

```text
conjugatePicardLimit
conjugatePicardLimit_initialTrace_of_conjugate_data
BFormSpectralFrontier
BFormBankedInputs
gradientInitialApproach_of_BForm
```

These files currently support positive-time/classical/trace construction, not the all-exponent gradient time-integrability needed here.

## Smallest useful wiring theorem if a stronger input is supplied

If you can supply closed-time gradient-energy continuity, the existing wiring already proves integrability. The smallest producer theorem should just expose this route for the anchored global-classical trace package:

```lean
import ShenWork.PDE.P3MoserRegularityProducer
import ShenWork.PDE.P3MoserEnergyContinuity

open MeasureTheory Set
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
open ShenWork.IntervalDomainExistence.P3MoserRegularityProducer
open scoped Interval

namespace ShenWork.IntervalDomainExistence.P3MoserRegularityProducer

/-- If the raw representative has closed-time Moser-gradient energy continuity,
then the anchored representative has the regularity package needed for
integrated first crossing.  This is only wiring; the gradient continuity input is
still analytic. -/
theorem intervalDomain_integratedMoserFirstCrossingRegularity_of_globalClassicalTraceAnchored_gradientContinuous
    {params : CM2Params} {T p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hT : 0 < T)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hdatum : PaperPositiveInitialDatum intervalDomain u₀)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hgradRaw :
      ∀ p, p0 ≤ p →
        ContinuousOn
          (fun t =>
            intervalDomain.integral (fun x =>
              (intervalDomain.gradNorm
                (fun y => (u t y) ^ (p / 2)) x) ^ 2))
          (Set.Icc (0 : ℝ) T)) :
    IntegratedMoserFirstCrossingRegularity intervalDomain
      (intervalDomainWithInitialSlice u₀ u) T p0 := by
  have hgradRawInt :
      ∀ p, p0 ≤ p →
        IntegrableOn
          (fun t =>
            intervalDomain.integral (fun x =>
              (intervalDomain.gradNorm
                (fun y => (u t y) ^ (p / 2)) x) ^ 2))
          (Set.uIcc (0 : ℝ) T) volume :=
    intervalDomain_gradientTimeIntegrable_of_gradientEnergyContinuous hT.le hgradRaw
  have hgradAnchored :
      ∀ p, p0 ≤ p →
        IntegrableOn
          (fun t =>
            intervalDomain.integral (fun x =>
              (intervalDomain.gradNorm
                (fun y => ((intervalDomainWithInitialSlice u₀ u) t y) ^ (p / 2)) x) ^ 2))
          (Set.uIcc (0 : ℝ) T) volume :=
    intervalDomain_gradientTimeIntegrable_withInitialSlice_of_raw hgradRawInt
  exact intervalDomain_integratedMoserFirstCrossingRegularity_of_globalClassicalTraceAnchored
    hT htrace hdatum hglobal hgradAnchored

end ShenWork.IntervalDomainExistence.P3MoserRegularityProducer
```

Caveat: for the **raw** representative, closed-time continuity at `0` is often false or irrelevant because raw Picard stores zero at `t = 0`. So this theorem is only useful if the raw `u 0` has already been made compatible or if the continuity statement is actually for the anchored representative.

The safer wiring theorem is the one you effectively already have: assume raw `IntegrableOn`, transfer to anchored by a.e. equality, then produce regularity.

## Missing analytic statement to add

The smallest honest missing producer is a near-zero/all-window Moser-gradient time-integrability theorem. A direct statement is:

```lean
/-- Analytic near-zero Moser-gradient time-integrability for the raw positive-time
solution representative.  This is the missing producer, not mere wiring. -/
theorem intervalDomain_rawMoserGradientTimeIntegrable_of_globalPicard
    {params : CM2Params} {T p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hT : 0 < T)
    (hdatum : PaperPositiveInitialDatum intervalDomain u₀)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    -- likely additional source-specific Picard/spectral smoothing data here
    :
    ∀ p, p0 ≤ p →
      IntegrableOn
        (fun t =>
          intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm
              (fun y => (u t y) ^ (p / 2)) x) ^ 2))
        (Set.uIcc (0 : ℝ) T) volume
```

But as written this is too strong for the currently visible hypotheses: `hglobal` and `htrace` alone do not contain a quantitative near-zero gradient estimate. The theorem should be proved from one of the following honest stronger packages.

### Option A: direct near-zero estimate package

```lean
structure IntervalDomainMoserGradientNearZeroIntegrability
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop where
  gradientTimeIntegrable :
    ∀ p, p0 ≤ p →
      IntegrableOn
        (fun t =>
          intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm
              (fun y => (u t y) ^ (p / 2)) x) ^ 2))
        (Set.uIcc (0 : ℝ) T) volume
```

This is essentially the current raw input, but named as the genuine analytic frontier.

### Option B: quantitative smoothing estimate

This is more informative and probably closer to a Picard/spectral proof:

```lean
structure IntervalDomainMoserGradientNearZeroSmoothingBound
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop where
  bound :
    ∀ p, p0 ≤ p →
      ∃ C σ, 0 ≤ C ∧ σ < 1 ∧
        ∀ t ∈ Set.Ioc (0 : ℝ) T,
          intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm
              (fun y => (u t y) ^ (p / 2)) x) ^ 2) ≤ C * t ^ (-σ)
```

Then add a pure real-analysis theorem turning this bound into `IntegrableOn` on `Set.uIcc 0 T`. This is honest because it states the actual near-zero smoothing/integrability information needed.

### Option C: spectral/Picard producer

If the B-form/cosine machinery has enough coefficient decay, add a source-facing theorem such as:

```lean
theorem intervalDomain_rawMoserGradientTimeIntegrable_of_BFormSpectralFrontier
    {params : CM2Params} {p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {DB : ShenWork.IntervalConjugatePicard.ConjugateMildExistenceData params u₀}
    (F : ShenWork.Paper2.BFormEndToEnd.BFormSpectralFrontier params DB)
    -- plus any exponent/lower-bound hypotheses actually needed for rpow chain rule
    :
    ∀ p, p0 ≤ p →
      IntegrableOn
        (fun t =>
          intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm
              (fun y => (conjugatePicardLimit params u₀ DB.T t y) ^ (p / 2)) x) ^ 2))
        (Set.uIcc (0 : ℝ) DB.T) volume
```

This is likely the right long-term producer if the Picard construction can provide enough heat-smoothing / coefficient summability. But I do not see this theorem currently in the repo.

## Why not derive it from integrated drop?

A tempting theorem would be:

```lean
IntegratedMoserDissipationDropBefore intervalDomain u T rho p0 →
(power energy bounded/integrable) →
gradientTimeIntegrable
```

This is not currently a safe Lean route. The integrated drop predicate is stated using total interval integrals and does not include `IntervalIntegrable`/`IntegrableOn` of the gradient integrand as a field. A Bochner interval integral inequality alone is not a reliable integrability proof in this setup.

If you want this route, the missing statement would need to be strengthened to include integrability, e.g.

```lean
structure IntegratedMoserDissipationDropBeforeWithGradientIntegrability
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) : Prop where
  drop : IntegratedMoserDissipationDropBefore D u T rho p0
  gradientTimeIntegrable :
    ∀ p, p0 ≤ p →
      IntegrableOn
        (fun t =>
          D.integral (fun x =>
            (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2))
        (Set.uIcc (0 : ℝ) T) volume
```

But that just moves the frontier into the dissipation producer. It is honest, though.

## Recommended next Lean step

Do not spend time trying to prove raw all-exponent gradient time-integrability from `IsPaper2GlobalClassicalSolution` plus `InitialTrace`; the current interfaces do not contain the needed near-zero gradient estimate.

The highest-signal next step is to name the frontier explicitly and wire it cleanly:

```lean
def IntervalDomainRawMoserGradientTimeIntegrability
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p →
    IntegrableOn
      (fun t =>
        intervalDomain.integral (fun x =>
          (intervalDomain.gradNorm
            (fun y => (u t y) ^ (p / 2)) x) ^ 2))
      (Set.uIcc (0 : ℝ) T) volume
```

Then make the anchored producer consume this raw frontier:

```lean
theorem intervalDomain_integratedMoserFirstCrossingRegularity_of_globalClassicalTraceAnchored_rawGradient
    {params : CM2Params} {T p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hT : 0 < T)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hdatum : PaperPositiveInitialDatum intervalDomain u₀)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hgradRaw : IntervalDomainRawMoserGradientTimeIntegrability u T p0) :
    IntegratedMoserFirstCrossingRegularity intervalDomain
      (intervalDomainWithInitialSlice u₀ u) T p0 := by
  exact intervalDomain_integratedMoserFirstCrossingRegularity_of_globalClassicalTraceAnchored
    hT htrace hdatum hglobal
    (intervalDomain_gradientTimeIntegrable_withInitialSlice_of_raw hgradRaw)
```

This theorem is pure wiring and should be provable now, assuming the names from your local anchored work. The **unconditional** headline still waits for a real producer of `IntervalDomainRawMoserGradientTimeIntegrability`, most likely from B-form/spectral heat-smoothing estimates or an explicitly strengthened integrated-energy producer.
