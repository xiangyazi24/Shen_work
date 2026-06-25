# Q451 (cron2): B-form Picard iterate logistic-source `TimeC1On` tower

## Executive verdict

I read the exact signatures of the seven named pieces. The proposed file is feasible as a **tower skeleton**, but it is not closed from only

```lean
DB : ConjugateMildExistenceData p u₀
Hinf : ConjugatePicardInfThresholdData p u₀ DB.T
huPaper : PaperPositiveInitialDatum intervalDomain u₀
```

The precise gap is not the induction combinator. The generic successor theorem

```lean
sourceTimeC1On_succ_of_sourceTimeC1On
```

is strong enough to produce the successor **logistic** source package once the successor slice already has a restart representation, strict positivity, bounds, spatial `G1/G2`, endpoint/closed-slice continuity, and joint continuity. The problem is supplying those inputs for

```lean
w = conjugatePicardIter p u₀ (n + 1)
```

in the B-form chain.

The key missing inputs are:

1. **B-form total source `TimeC1On` for the predecessor.**  The successor iterate is represented using
   ```lean
   bFormSourceCoeffs p (conjugatePicardIter p u₀ n)
   = logisticSourceCoeffs - χ₀ * chemDivSourceCoeffs
   ```
   so the induction needs **both** the predecessor logistic source `TimeC1On` and the predecessor chem-div source `TimeC1On`. The logistic tower alone is insufficient.

2. **Chem-div source `TimeC1On` for the finite B-form iterates.**  I did not find a landed producer of
   ```lean
   DuhamelSourceTimeC1On
     (coupledChemDivSourceCoeffs p (conjugatePicardIter p u₀ n)) c T
   ```
   from `DB/Hinf`. The analogous `IntervalChemDivWinDischarge.lean` route for a gradient solution explicitly bottoms out in a heavy `ChemDivSolutionRegularityResidual`, including time-`C²`, space-`C²`, FAC/chain-rule, weak-H², decay, and `adot` bounds. So this is a real residual unless a finite-iterate chem-div chain is built separately.

3. **A restart representation for finite B-form iterates.**  `intervalConjugateDuhamelMap_cosineSeries` gives a **from-zero** B-form cosine formula for one map application. `sourceTimeC1On_succ_of_sourceTimeC1On` wants a **positive-offset restart representation** on `[c,T]` with `offset = c/2`. There is a landed `bForm_restart_of_global_cosine` and a `conjugatePicardLimit_B_restart_of_global_cosine`, but I did not find the corresponding finite-iterate wrapper for `conjugatePicardIter (n+1)`. It should be buildable from the same generic `bForm_restart_of_global_cosine`, but it is a required new lemma.

4. **Spatial derivative bounds `G1/G2` and joint continuity for B-form iterates.**  `DB/Hinf` provide value bounds, nonnegativity, continuity slices, integrability, and geometric convergence, but not spatial first/second derivative bounds for `conjugatePicardIter`. The existing `IntervalPicardSourceTower.lean` for the non-conjugate tower carries `hG1all`, endpoint `hG2end`, a gate, and source-window data in `TowerInputs`; this is not cosmetic — those are exactly the derivative regularity walls needed by the successor. A B-form analogue needs comparable inputs or new heat-kernel/spectral proofs.

5. **Source bridge slice data.**  `source_bridge_slice_of_sliceC1` is the right bridge, but it requires per-slice chem-flux continuity, logistic continuity, coefficient bounds, a derivative identity for the flux, and divergence continuity. These are not supplied by `DB/Hinf`; they follow from stronger slice regularity of the iterates/resolver.

For the limit passage, the gap is different:

* coefficient value convergence of logistic sources should follow from geometric convergence plus a Lipschitz bound for `u ↦ logisticLifted p u` on the ball, but I did not see that exact coefficient-convergence lemma;
* the serious missing hypothesis is **uniform convergence of the derivative coefficient functions** (`adotSeq → adot`) on the closed window, plus a common derivative bound. Geometric convergence of iterates as functions does not imply convergence of time derivatives/source `adot`s.

There is no unavoidable circularity if the finite-iterate tower is built from predecessor source packages and independent B-form derivative/regularity inputs, then the limit is taken last. But there **would** be a circularity if the chem-div source `TimeC1On` is obtained from the final classical solution/regularity theorem whose inputs already include the desired limit source packages.

## Exact existing pieces read

### 1. Generic successor step

`IntervalPicardSourceTimeC1OnRecursion.lean` has:

```lean
noncomputable def sourceTimeC1On_succ_of_sourceTimeC1On
    {p : CM2Params}
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    {w : ℝ → intervalDomainPoint → ℝ}
    {a₀ : ℕ → ℝ} {M₀ : ℝ} (hM₀ : 0 ≤ M₀)
    (ha₀ : ∀ n, |a₀ n| ≤ M₀)
    {a : ℝ → ℕ → ℝ} {offset W lo hi aτ M G1 G2 : ℝ}
    (src : DuhamelSourceTimeC1On a 0 W)
    (hlohi : lo ≤ hi)
    (haτpos : 0 < aτ)
    (hshift : Set.MapsTo (fun s : ℝ => s - offset)
      (Set.Icc lo hi) (Set.Icc aτ W))
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ ∈ Set.Icc lo hi,
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagree : ∀ σ ∈ Set.Icc lo hi,
      Set.EqOn (intervalDomainLift (w σ))
        (fun x => ∑' n, bc σ n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1))
    (hpos : ∀ σ ∈ Set.Icc lo hi, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (w σ) x)
    (hub : ∀ σ ∈ Set.Icc lo hi, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (w σ) x ≤ M)
    (hG1 : ∀ σ ∈ Set.Icc lo hi, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (w σ)) x| ≤ G1)
    (hG2 : ∀ σ ∈ Set.Icc lo hi, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv (intervalDomainLift (w σ))) x| ≤ G2)
    (hrestart : ∀ s ∈ Set.Icc lo hi, ∀ x : intervalDomainPoint,
      intervalDomainLift (w s) x.1 =
        ∑' n, localRestartCoeff a₀ a (s - offset) n * cosineMode n x.1)
    (hC2cont : ∀ s ∈ Set.Icc lo hi,
      ContinuousOn (intervalDomainLift (w s)) (Set.Icc (0 : ℝ) 1))
    (hprofile_joint : ContinuousOn
      (Function.uncurry (fun s x => intervalDomainLift (w s) x))
      (Set.Icc lo hi ×ˢ Set.Icc (0 : ℝ) 1)) :
    DuhamelSourceTimeC1On
      (fun s k => cosineCoeffs (logisticLifted p (w s)) k) lo hi
```

This is generic and usable for `w = conjugatePicardIter p u₀ (n+1)`, but only after the B-form-specific restart/spectral/regularity facts have been produced.

### 2. B-form cosine series from zero

`IntervalConjugateCosineSeries.lean` has:

```lean
theorem intervalConjugateDuhamelMap_cosineSeries
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ} {t x M₀ : ℝ}
    (ht : 0 < t) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hu₀_cont : Continuous (intervalDomainLift u₀))
    (hu₀_bound : ∀ n, |cosineCoeffs (intervalDomainLift u₀) n| ≤ M₀)
    (hsrcB : DuhamelSourceTimeC1 (bFormSourceCoeffs p u))
    (hB_int : IntervalIntegrable
      (fun s : ℝ => intervalConjugateKernelOperator (t - s)
        (chemFluxLifted p (u s)) x) volume 0 t)
    (hlog_int : IntervalIntegrable
      (fun s : ℝ => intervalFullSemigroupOperator (t - s)
        (logisticLifted p (u s)) x) volume 0 t)
    (hsource_bridge : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      (-p.χ₀) * intervalConjugateKernelOperator (t - s)
          (chemFluxLifted p (u s)) x
        + intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x
        = unitIntervalCosineHeatValue (t - s) (bFormSourceCoeffs p u s) x) :
    intervalConjugateDuhamelMap p u₀ u t ⟨x, hx⟩ =
      ∑' n : ℕ,
        localRestartCoeff (cosineCoeffs (intervalDomainLift u₀))
          (bFormSourceCoeffs p u) t n * cosineMode n x
```

For `conjugatePicardIter (n+1)`, instantiate `u := conjugatePicardIter p u₀ n`. But this gives a from-zero representation; the source successor wants a positive-offset restart representation.

### 3. Source bridge

`IntervalChiNegFinalClose.lean` has:

```lean
theorem source_bridge_slice_of_sliceC1
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    {s : ℝ}
    (hchem_cont : Continuous (chemFluxLifted p (u s)))
    (hlog_cont : Continuous (logisticLifted p (u s)))
    {Mlog : ℝ}
    (hlog_bound : ∀ n, |cosineCoeffs (logisticLifted p (u s)) n| ≤ Mlog)
    {Mchem : ℝ}
    (hchem_bound : ∀ n, |coupledChemDivSourceCoeffs p u s n| ≤ Mchem)
    (hderiv : ∀ y ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (chemFluxLifted p (u s)) (coupledChemDivSourceLift p u s y) y)
    (hdivcont : Continuous (coupledChemDivSourceLift p u s)) :
    (-p.χ₀) * intervalConjugateKernelOperator r (chemFluxLifted p (u s)) x
        + intervalFullSemigroupOperator r (logisticLifted p (u s)) x
      = unitIntervalCosineHeatValue r (bFormSourceCoeffs p u s) x
```

This is the right bridge, but it exposes another residual: finite-iterate flux/divergence slice `C¹` and continuity.

### 4. Base case

`IntervalPicardLevel0SourceTimeC1On.lean` has:

```lean
noncomputable def level0Source_timeC1On
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {c T M G1 G2 Udot M₀ : ℝ}
    (hc : 0 < c) (hcT : c < T)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀)
    (hpos : ∀ σ ∈ Set.Icc c T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (picardIter p u₀ 0 σ) x)
    (hub : ∀ σ ∈ Set.Icc c T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (picardIter p u₀ 0 σ) x ≤ M)
    (hG1 : ∀ σ ∈ Set.Icc c T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (picardIter p u₀ 0 σ)) x| ≤ G1)
    (hG2 : ∀ σ ∈ Set.Icc c T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv (intervalDomainLift (picardIter p u₀ 0 σ))) x| ≤ G2)
    (hUdot : ∀ σ ∈ Set.Icc c T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |unitIntervalCosineHeatSecondValue σ (heatCoeff u₀) x| ≤ Udot) :
    DuhamelSourceTimeC1On
      (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ 0 s)) k)
      c T
```

`conjugatePicardIter p u₀ 0` is definitionally the same heat-semigroup slice as `picardIter p u₀ 0`, so a base wrapper should be a `simpa [conjugatePicardIter, picardIter]` around this theorem.

### 5. Limit passage

`IntervalMildPicardLimitRegularityOn.lean` has:

```lean
def duhamelSourceTimeC1On_of_uniform_limit
    {a : ℝ → ℕ → ℝ} {aSeq : ℕ → ℝ → ℕ → ℝ}
    {lo hi : ℝ}
    (hconv : ∀ s ∈ Icc lo hi, ∀ k, Tendsto (fun n => aSeq n s k) atTop (nhds (a s k)))
    {adotSeq : ℕ → ℝ → ℕ → ℝ}
    (hderiv_each : ∀ n, ∀ s ∈ Icc lo hi, ∀ k,
      HasDerivWithinAt (fun r => aSeq n r k) (adotSeq n s k) (Icc lo hi) s)
    {adot : ℝ → ℕ → ℝ}
    (hadot_unif : ∀ k, TendstoUniformlyOn (fun n s => adotSeq n s k)
      (fun s => adot s k) atTop (Icc lo hi))
    (hadot_cont : ∀ k, ContinuousOn (fun s => adot s k) (Icc lo hi))
    {envelope : ℕ → ℝ}
    (henv_summable : Summable envelope)
    (henv_bound : ∀ n, ∀ s ∈ Icc lo hi, ∀ k, |aSeq n s k| ≤ envelope k)
    {D : ℝ}
    (hderiv_bound : ∀ n, ∀ s ∈ Icc lo hi, ∀ k, |adotSeq n s k| ≤ D) :
    DuhamelSourceTimeC1On a lo hi
```

This tells us exactly what the limit gap is: uniform derivative-coefficient convergence and common bounds, not just pointwise convergence of iterates.

## Proposed Lean file structure

Suggested file name:

```lean
ShenWork/Paper2/IntervalConjugatePicardIterateLogSourceTimeC1On.lean
```

### Imports / namespace

```lean
import ShenWork.Paper2.IntervalPicardSourceTimeC1OnRecursion
import ShenWork.Paper2.IntervalConjugateCosineSeries
import ShenWork.Paper2.IntervalChiNegFinalClose
import ShenWork.Paper2.IntervalPicardLevel0SourceTimeC1On
import ShenWork.Paper2.IntervalMildPicardLimitRegularityOn
import ShenWork.Paper2.IntervalBankInfAndLogSrcWiring
import ShenWork.Paper2.IntervalBFormSpectralHtime
import ShenWork.Paper2.IntervalBFormRestart
import ShenWork.Paper2.IntervalConjugatePicardInfThreshold

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceData ConjugatePicardInfThresholdData
   conjugatePicardIter conjugatePicardLimit paperPositiveFloor)
open ShenWork.IntervalDuhamelSourceTimeC1On (DuhamelSourceTimeC1On)
open ShenWork.IntervalBFormSpectral
  (bFormSourceCoeffs bFormSource_duhamelSourceTimeC1On)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledLogisticSourceCoeffs)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.Paper2 (PaperPositiveInitialDatum)

noncomputable section

namespace ShenWork.IntervalConjugatePicardIterateLogSourceTimeC1On
```

### Basic abbreviations

```lean
abbrev ConjIterLogSourceCoeffs
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ) : ℝ → ℕ → ℝ :=
  fun s k => cosineCoeffs (logisticLifted p (conjugatePicardIter p u₀ n s)) k

abbrev ConjIterLogSourceTimeC1On
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (n : ℕ) (lo hi : ℝ) : Prop :=
  DuhamelSourceTimeC1On (ConjIterLogSourceCoeffs p u₀ n) lo hi

abbrev ConjIterLogSourceTimeC1OnUpTo
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (n : ℕ) (T : ℝ) : Prop :=
  ∀ c, 0 < c → c < T → ConjIterLogSourceTimeC1On p u₀ n c T

abbrev ConjIterChemSourceTimeC1On
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (n : ℕ) (lo hi : ℝ) : Prop :=
  DuhamelSourceTimeC1On
    (coupledChemDivSourceCoeffs p (conjugatePicardIter p u₀ n)) lo hi

abbrev ConjIterBFormSourceTimeC1On
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (n : ℕ) (lo hi : ℝ) : Prop :=
  DuhamelSourceTimeC1On
    (bFormSourceCoeffs p (conjugatePicardIter p u₀ n)) lo hi
```

### Combine predecessor log + chem into B-form source

This one should be straightforward:

```lean
noncomputable def conjIter_bFormSourceTimeC1On_of_log_chem
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {n : ℕ} {lo hi : ℝ}
    (hlog : ConjIterLogSourceTimeC1On p u₀ n lo hi)
    (hchem : ConjIterChemSourceTimeC1On p u₀ n lo hi) :
    ConjIterBFormSourceTimeC1On p u₀ n lo hi := by
  simpa [ConjIterLogSourceTimeC1On, ConjIterLogSourceCoeffs,
    ConjIterChemSourceTimeC1On, ConjIterBFormSourceTimeC1On,
    coupledLogisticSourceCoeffs] using
    bFormSource_duhamelSourceTimeC1On (p := p)
      (u := conjugatePicardIter p u₀ n) hlog hchem
```

The exact `simpa` may need tuning around `coupledLogisticSourceCoeffs`, but this is the intended wrapper.

### Base wrapper

```lean
noncomputable def conjugateLevel0_logSourceTimeC1On
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {c T M G1 G2 Udot M₀ : ℝ}
    (hc : 0 < c) (hcT : c < T)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |ShenWork.IntervalPicardLevel0SourceTimeC1On.heatCoeff u₀ k| ≤ M₀)
    (hpos : ∀ σ ∈ Set.Icc c T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x)
    (hub : ∀ σ ∈ Set.Icc c T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x ≤ M)
    (hG1 : ∀ σ ∈ Set.Icc c T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (conjugatePicardIter p u₀ 0 σ)) x| ≤ G1)
    (hG2 : ∀ σ ∈ Set.Icc c T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv (intervalDomainLift (conjugatePicardIter p u₀ 0 σ))) x| ≤ G2)
    (hUdot : ∀ σ ∈ Set.Icc c T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |ShenWork.IntervalDomainRegularityBootstrap.unitIntervalCosineHeatSecondValue σ
        (ShenWork.IntervalPicardLevel0SourceTimeC1On.heatCoeff u₀) x| ≤ Udot) :
    ConjIterLogSourceTimeC1On p u₀ 0 c T := by
  -- Should close by definitional equality of the zero iterate.
  simpa [ConjIterLogSourceTimeC1On, ConjIterLogSourceCoeffs,
    conjugatePicardIter, ShenWork.IntervalMildPicard.picardIter] using
    ShenWork.IntervalPicardLevel0SourceTimeC1On.level0Source_timeC1On
      p hc hcT hα ha hb hu₀_cont hu₀_bound
      (by simpa [conjugatePicardIter, ShenWork.IntervalMildPicard.picardIter] using hpos)
      (by simpa [conjugatePicardIter, ShenWork.IntervalMildPicard.picardIter] using hub)
      (by simpa [conjugatePicardIter, ShenWork.IntervalMildPicard.picardIter] using hG1)
      (by simpa [conjugatePicardIter, ShenWork.IntervalMildPicard.picardIter] using hG2)
      hUdot
```

### Successor data package

This is the key practical structure. It records exactly what the generic successor step needs for the B-form successor iterate.

```lean
structure ConjSuccLogSourceWindowData
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (n : ℕ) (lo hi : ℝ) where
  offset : ℝ
  W : ℝ
  aτ : ℝ
  M : ℝ
  G1 : ℝ
  G2 : ℝ
  M₀ : ℝ
  hM₀ : 0 ≤ M₀
  h_lo_hi : lo ≤ hi
  h_aτ_pos : 0 < aτ
  hshift : Set.MapsTo (fun s : ℝ => s - offset)
    (Set.Icc lo hi) (Set.Icc aτ W)

  /-- Shifted B-form source for predecessor level `n`. -/
  srcB_shift : DuhamelSourceTimeC1On
    (fun s k => bFormSourceCoeffs p (conjugatePicardIter p u₀ n) (offset + s) k)
    0 W

  a₀ : ℕ → ℝ
  ha₀ : ∀ k, |a₀ k| ≤ M₀

  bc : ℝ → ℕ → ℝ
  hbsum : ∀ σ ∈ Set.Icc lo hi,
    Summable (fun k => unitIntervalCosineEigenvalue k * |bc σ k|)
  hagree : ∀ σ ∈ Set.Icc lo hi,
    Set.EqOn (intervalDomainLift (conjugatePicardIter p u₀ (n + 1) σ))
      (fun x => ∑' k, bc σ k * cosineMode k x)
      (Set.Icc (0 : ℝ) 1)
  hpos : ∀ σ ∈ Set.Icc lo hi, ∀ x ∈ Set.Icc (0 : ℝ) 1,
    0 < intervalDomainLift (conjugatePicardIter p u₀ (n + 1) σ) x
  hub : ∀ σ ∈ Set.Icc lo hi, ∀ x ∈ Set.Icc (0 : ℝ) 1,
    intervalDomainLift (conjugatePicardIter p u₀ (n + 1) σ) x ≤ M
  hG1 : ∀ σ ∈ Set.Icc lo hi, ∀ x ∈ Set.Icc (0 : ℝ) 1,
    |deriv (intervalDomainLift (conjugatePicardIter p u₀ (n + 1) σ)) x| ≤ G1
  hG2 : ∀ σ ∈ Set.Icc lo hi, ∀ x ∈ Set.Icc (0 : ℝ) 1,
    |deriv (deriv (intervalDomainLift (conjugatePicardIter p u₀ (n + 1) σ))) x| ≤ G2
  hrestart : ∀ s ∈ Set.Icc lo hi, ∀ x : intervalDomainPoint,
    intervalDomainLift (conjugatePicardIter p u₀ (n + 1) s) x.1 =
      ∑' k, localRestartCoeff a₀
        (fun σ k => bFormSourceCoeffs p (conjugatePicardIter p u₀ n) (offset + σ) k)
        (s - offset) k * cosineMode k x.1
  hC2cont : ∀ s ∈ Set.Icc lo hi,
    ContinuousOn (intervalDomainLift (conjugatePicardIter p u₀ (n + 1) s))
      (Set.Icc (0 : ℝ) 1)
  hprofile_joint : ContinuousOn
    (Function.uncurry
      (fun s x => intervalDomainLift (conjugatePicardIter p u₀ (n + 1) s) x))
    (Set.Icc lo hi ×ˢ Set.Icc (0 : ℝ) 1)
```

### Successor wrapper

```lean
noncomputable def conjugateLogSourceTimeC1On_succ_of_windowData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {n : ℕ} {lo hi : ℝ}
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (Dwin : ConjSuccLogSourceWindowData p u₀ n lo hi) :
    ConjIterLogSourceTimeC1On p u₀ (n + 1) lo hi := by
  simpa [ConjIterLogSourceTimeC1On, ConjIterLogSourceCoeffs] using
    ShenWork.IntervalPicardSourceTimeC1OnRecursion.sourceTimeC1On_succ_of_sourceTimeC1On
      (p := p)
      (w := conjugatePicardIter p u₀ (n + 1))
      (a₀ := Dwin.a₀)
      (M₀ := Dwin.M₀)
      (a := fun σ k => bFormSourceCoeffs p (conjugatePicardIter p u₀ n) (Dwin.offset + σ) k)
      (offset := Dwin.offset)
      (W := Dwin.W)
      (lo := lo)
      (hi := hi)
      (aτ := Dwin.aτ)
      (M := Dwin.M)
      (G1 := Dwin.G1)
      (G2 := Dwin.G2)
      hα ha hb
      Dwin.hM₀ Dwin.ha₀ Dwin.srcB_shift Dwin.h_lo_hi Dwin.h_aτ_pos
      Dwin.hshift Dwin.bc Dwin.hbsum Dwin.hagree Dwin.hpos Dwin.hub
      Dwin.hG1 Dwin.hG2 Dwin.hrestart Dwin.hC2cont Dwin.hprofile_joint
```

### Building `srcB_shift` from predecessor log+chem source packages

A helper theorem for the actual induction step:

```lean
noncomputable def shiftedBFormSource_of_prev_log_chem
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {n : ℕ}
    {offset W T : ℝ}
    (hsumTW : offset + W = T)
    (hlog_prev : ConjIterLogSourceTimeC1On p u₀ n offset T)
    (hchem_prev : ConjIterChemSourceTimeC1On p u₀ n offset T) :
    DuhamelSourceTimeC1On
      (fun s k => bFormSourceCoeffs p (conjugatePicardIter p u₀ n) (offset + s) k)
      0 W := by
  have hsrcB : ConjIterBFormSourceTimeC1On p u₀ n offset T :=
    conjIter_bFormSourceTimeC1On_of_log_chem hlog_prev hchem_prev
  have hsrcB' : DuhamelSourceTimeC1On
      (bFormSourceCoeffs p (conjugatePicardIter p u₀ n)) offset (offset + W) := by
    simpa [ConjIterBFormSourceTimeC1On, hsumTW] using hsrcB
  simpa [add_comm] using
    ShenWork.IntervalDuhamelSourceTimeC1On.DuhamelSourceTimeC1On.shift_zero
      (offset := offset) (W := W) hsrcB'
```

This displays the chem-div dependency cleanly.

### Induction theorem skeleton

The induction theorem should not pretend `DB/Hinf` supplies all analytic regularity. Use a data provider for successor windows.

```lean
structure ConjIterLogSourceTowerInputs
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (DB : ConjugateMildExistenceData p u₀) where
  hα : 1 ≤ p.α
  ha : 0 ≤ p.a
  hb : 0 ≤ p.b

  /-- Base-case data for `n = 0`, on every positive window. -/
  base : ConjIterLogSourceTimeC1OnUpTo p u₀ 0 DB.T

  /-- Chem-div source package for each finite iterate, on positive windows.  This is
  the major missing analytic input unless a finite-iterate chem-div tower is built. -/
  chem : ∀ n c, 0 < c → c < DB.T →
    ConjIterChemSourceTimeC1On p u₀ n c DB.T

  /-- The B-form successor-window facts needed by the generic successor.  In a
  fully built file this should be derived from B-form restart, source bridge,
  G1/G2 estimates, positivity/bounds, and joint continuity. -/
  succData : ∀ n,
    ConjIterLogSourceTimeC1OnUpTo p u₀ n DB.T →
      ∀ c, 0 < c → c < DB.T →
        ConjSuccLogSourceWindowData p u₀ n c DB.T

noncomputable def conjugateIter_logSourceTimeC1On_all
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (H : ConjIterLogSourceTowerInputs p u₀ DB) :
    ∀ n, ConjIterLogSourceTimeC1OnUpTo p u₀ n DB.T
  | 0 => H.base
  | n + 1 => by
      intro c hc hcT
      exact conjugateLogSourceTimeC1On_succ_of_windowData
        H.hα H.ha H.hb (H.succData n (conjugateIter_logSourceTimeC1On_all H n) c hc hcT)
```

This is the right theorem shape if you want the induction to compile before closing all analytic producers.

## How to actually fill `succData`

A later file should derive `ConjSuccLogSourceWindowData` using these sublemmas.

### Needed finite-iterate B-form from-zero representation

```lean
theorem conjugatePicardIter_succ_global_cosine
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {n : ℕ} {T M₀ : ℝ}
    (hu₀_cont : Continuous (intervalDomainLift u₀))
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hsrcB : DuhamelSourceTimeC1On
      (bFormSourceCoeffs p (conjugatePicardIter p u₀ n)) 0 T)
    (hB_int : ∀ t, 0 < t → t ≤ T → ∀ x : ℝ,
      IntervalIntegrable
        (fun s : ℝ => intervalConjugateKernelOperator (t - s)
          (chemFluxLifted p ((conjugatePicardIter p u₀ n) s)) x)
        volume 0 t)
    (hlog_int : ∀ t, 0 < t → t ≤ T → ∀ x : ℝ,
      IntervalIntegrable
        (fun s : ℝ => intervalFullSemigroupOperator (t - s)
          (logisticLifted p ((conjugatePicardIter p u₀ n) s)) x)
        volume 0 t)
    (hsource_bridge : ∀ t, 0 < t → t ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ∀ s ∈ Set.Ioo (0 : ℝ) t,
        (-p.χ₀) * intervalConjugateKernelOperator (t - s)
            (chemFluxLifted p ((conjugatePicardIter p u₀ n) s)) x
          + intervalFullSemigroupOperator (t - s)
              (logisticLifted p ((conjugatePicardIter p u₀ n) s)) x
          = unitIntervalCosineHeatValue (t - s)
              (bFormSourceCoeffs p (conjugatePicardIter p u₀ n) s) x) :
    ∀ t, 0 < t → t ≤ T →
      Set.EqOn
        (intervalDomainLift (conjugatePicardIter p u₀ (n + 1) t))
        (fun x => ∑' k,
          localRestartCoeff (cosineCoeffs (intervalDomainLift u₀))
            (bFormSourceCoeffs p (conjugatePicardIter p u₀ n)) t k * cosineMode k x)
        (Set.Icc (0 : ℝ) 1) := by
  -- use `intervalConjugateDuhamelMap_cosineSeries`; `conjugatePicardIter.succ`
  -- unfolds to `intervalConjugateDuhamelMap`.
  sorry
```

This is buildable from the named theorem, but the source bridge and integrability inputs are nontrivial.

### Needed finite-iterate B-form restart representation

The generic `bForm_restart_of_global_cosine` already exists. Add a finite-iterate wrapper:

```lean
theorem conjugatePicardIter_succ_B_restart_of_global_cosine
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {n : ℕ} {T : ℝ}
    {a₀ : ℕ → ℝ} {aB : ℝ → ℕ → ℝ}
    (ha_cont : ∀ k, ContinuousOn (fun s => aB s k) (Set.Icc 0 T))
    (hrep : ∀ t, 0 < t → t ≤ T →
      Set.EqOn (intervalDomainLift (conjugatePicardIter p u₀ (n + 1) t))
        (fun x => ∑' k, localRestartCoeff a₀ aB t k * cosineMode k x)
        (Set.Icc (0 : ℝ) 1))
    (hsum : ∀ t, 0 < t → t ≤ T →
      Summable (fun k => |localRestartCoeff a₀ aB t k|)) :
    ∀ t₀, 0 < t₀ → t₀ < T →
      ∀ᶠ s in 𝓝 t₀, ∀ y : intervalDomainPoint,
        conjugatePicardIter p u₀ (n + 1) s y =
          ∑' k,
            localRestartCoeff
              (cosineCoeffs
                (intervalDomainLift (conjugatePicardIter p u₀ (n + 1) (t₀ / 2))))
              (fun σ k => aB (t₀ / 2 + σ) k)
              (s - t₀ / 2) k * cosineMode k y.1 := by
  exact ShenWork.IntervalConjugatePicard.bForm_restart_of_global_cosine
    (u := conjugatePicardIter p u₀ (n + 1)) ha_cont hrep hsum
```

This is probably the easiest missing finite-iterate restart lemma.

### Needed source bridge from slice C1

The source bridge theorem has a good final form. What is missing is a per-iterate provider:

```lean
structure ConjIterSourceBridgeSliceData
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ) (T : ℝ) where
  hchem_cont : ∀ s, 0 < s → s ≤ T,
    Continuous (chemFluxLifted p (conjugatePicardIter p u₀ n s))
  hlog_cont : ∀ s, 0 < s → s ≤ T,
    Continuous (logisticLifted p (conjugatePicardIter p u₀ n s))
  Mlog : ℝ
  hlog_bound : ∀ s, 0 < s → s ≤ T → ∀ k,
    |cosineCoeffs (logisticLifted p (conjugatePicardIter p u₀ n s)) k| ≤ Mlog
  Mchem : ℝ
  hchem_bound : ∀ s, 0 < s → s ≤ T → ∀ k,
    |coupledChemDivSourceCoeffs p (conjugatePicardIter p u₀ n) s k| ≤ Mchem
  hderiv : ∀ s, 0 < s → s ≤ T → ∀ y ∈ Set.uIcc (0 : ℝ) 1,
    HasDerivAt
      (chemFluxLifted p (conjugatePicardIter p u₀ n s))
      (coupledChemDivSourceLift p (conjugatePicardIter p u₀ n) s y) y
  hdivcont : ∀ s, 0 < s → s ≤ T,
    Continuous (coupledChemDivSourceLift p (conjugatePicardIter p u₀ n) s)

theorem source_bridge_of_conjIter_sliceData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {n : ℕ} {T : ℝ}
    (S : ConjIterSourceBridgeSliceData p u₀ n T) :
    ∀ t, 0 < t → t ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ∀ s ∈ Set.Ioo (0 : ℝ) t,
        (-p.χ₀) * intervalConjugateKernelOperator (t - s)
            (chemFluxLifted p (conjugatePicardIter p u₀ n s)) x
          + intervalFullSemigroupOperator (t - s)
              (logisticLifted p (conjugatePicardIter p u₀ n s)) x
          = unitIntervalCosineHeatValue (t - s)
              (bFormSourceCoeffs p (conjugatePicardIter p u₀ n) s) x := by
  intro t ht htT x hx s hs
  exact ShenWork.Paper2.IntervalChiNegFinalClose.source_bridge_slice_of_sliceC1
    (p := p) (u := conjugatePicardIter p u₀ n)
    (r := t - s) (x := x) (by linarith [hs.2]) hx
    (S.hchem_cont s hs.1 (le_trans hs.2 htT))
    (S.hlog_cont s hs.1 (le_trans hs.2 htT))
    (S.hlog_bound s hs.1 (le_trans hs.2 htT))
    (S.hchem_bound s hs.1 (le_trans hs.2 htT))
    (S.hderiv s hs.1 (le_trans hs.2 htT))
    (S.hdivcont s hs.1 (le_trans hs.2 htT))
```

This makes the bridge gap explicit.

## Limit passage file structure

The clean limit theorem should be stated first on arbitrary `[lo,hi]`, then specialized to `[0,DB.T]` if the endpoint data is available.

### Abbreviations for the limit

```lean
abbrev ConjLimitLogSourceCoeffs
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (T : ℝ) : ℝ → ℕ → ℝ :=
  coupledLogisticSourceCoeffs p (conjugatePicardLimit p u₀ T)
```

### Limit data package

```lean
structure ConjLogSourceLimitPassageData
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (T lo hi : ℝ) where
  aSeq : ℕ → ℝ → ℕ → ℝ :=
    fun n s k => cosineCoeffs (logisticLifted p (conjugatePicardIter p u₀ n s)) k
  aLim : ℝ → ℕ → ℝ :=
    coupledLogisticSourceCoeffs p (conjugatePicardLimit p u₀ T)
  srcSeq : ∀ n, DuhamelSourceTimeC1On (aSeq n) lo hi
  adotSeq : ℕ → ℝ → ℕ → ℝ
  hderiv_each : ∀ n, ∀ s ∈ Set.Icc lo hi, ∀ k,
    HasDerivWithinAt (fun r => aSeq n r k) (adotSeq n s k) (Set.Icc lo hi) s
  adot : ℝ → ℕ → ℝ
  hadot_unif : ∀ k, TendstoUniformlyOn (fun n s => adotSeq n s k)
    (fun s => adot s k) atTop (Set.Icc lo hi)
  hadot_cont : ∀ k, ContinuousOn (fun s => adot s k) (Set.Icc lo hi)
  envelope : ℕ → ℝ
  henv_summable : Summable envelope
  henv_bound : ∀ n, ∀ s ∈ Set.Icc lo hi, ∀ k, |aSeq n s k| ≤ envelope k
  derivBound : ℝ
  hderiv_bound : ∀ n, ∀ s ∈ Set.Icc lo hi, ∀ k,
    |adotSeq n s k| ≤ derivBound
  hconv : ∀ s ∈ Set.Icc lo hi, ∀ k,
    Tendsto (fun n => aSeq n s k) atTop (nhds (aLim s k))
```

### Limit theorem signature

```lean
noncomputable def conjugateLimit_logSourceTimeC1On_of_limitData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T lo hi : ℝ}
    (L : ConjLogSourceLimitPassageData p u₀ T lo hi) :
    DuhamelSourceTimeC1On
      (coupledLogisticSourceCoeffs p (conjugatePicardLimit p u₀ T)) lo hi :=
  ShenWork.IntervalMildPicardLimitRegularityOn.duhamelSourceTimeC1On_of_uniform_limit
    (a := L.aLim) (aSeq := L.aSeq) (lo := lo) (hi := hi)
    L.hconv L.hderiv_each L.hadot_unif L.hadot_cont
    L.henv_summable L.henv_bound L.hderiv_bound
```

### Desired final limit wrapper

```lean
noncomputable def conjugateLimit_logSourceTimeC1On_zero_T
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀)
    (L : ConjLogSourceLimitPassageData p u₀ DB.T 0 DB.T) :
    DuhamelSourceTimeC1On
      (coupledLogisticSourceCoeffs p (conjugatePicardLimit p u₀ DB.T)) 0 DB.T :=
  conjugateLimit_logSourceTimeC1On_of_limitData L
```

This is the exact shape of part (B). It honestly names the uniform-derivative convergence and common-bound gap instead of hiding it.

## Do the needed limit hypotheses follow from geometric convergence?

Only partly.

### Coefficient value convergence

Geometric convergence of `conjugatePicardIter` gives uniform convergence of `u_n → u` on positive-time windows. With a boundedness/positivity ball and a local Lipschitz lemma for

```lean
u ↦ logisticLifted p u
```

one should be able to prove:

```lean
theorem logisticCoeff_tendsto_of_conjugatePicardIter
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (Hinf : ConjugatePicardInfThresholdData p u₀ T)
    (hball : ∀ n t, 0 < t → t ≤ T → ∀ x,
      |conjugatePicardIter p u₀ n t x| ≤ M) :
    ∀ s, 0 < s → s ≤ T → ∀ k,
      Tendsto
        (fun n => cosineCoeffs (logisticLifted p (conjugatePicardIter p u₀ n s)) k)
        atTop
        (nhds (coupledLogisticSourceCoeffs p (conjugatePicardLimit p u₀ T) s k)) := by
  -- needs Lipschitz / dominated coefficient lemma for logisticLifted.
  sorry
```

This is plausible, but I did not see it landed in the files read.

### Uniform derivative convergence

Geometric convergence of values does **not** give:

```lean
∀ k, TendstoUniformlyOn (fun n s => adotSeq n s k) (fun s => adot s k) atTop (Icc lo hi)
```

The `adotSeq` for the logistic source depends on the time derivative of the iterate slice (through `logisticSourceDot` / restart field derivative). To prove uniform convergence, you need convergence of those time-derivative fields, not just convergence of `u_n`. This is the main limit gap.

### Common envelopes and derivative bounds

`duhamelSourceTimeC1On_of_uniform_limit` also requires a single summable envelope and a single derivative bound for all iterates on the window. Per-level `DuhamelSourceTimeC1On` packages are not enough unless the induction is designed to produce uniform envelopes/bounds. Existing `sourceTimeC1On_succ_of_sourceTimeC1On` chooses a compact-window bound by `Classical.choose`; without an external uniform estimate, those constants may depend on `n`.

So part (B) needs a stronger tower than just:

```lean
∀ n, DuhamelSourceTimeC1On (... iterate n ...) lo hi
```

It needs a **uniform** tower carrying:

```lean
henv_bound_uniform : ∀ n s∈Icc lo hi k, |aSeq n s k| ≤ envelope k
hderiv_bound_uniform : ∀ n s∈Icc lo hi k, |adotSeq n s k| ≤ D
hadot_unif : ∀ k, TendstoUniformlyOn ...
```

## What `DB/Hinf/huPaper` already give

Available from the named inputs:

* `iter_ball_package DB n` gives value bound, nonnegativity, continuous slices, and joint measurability for `conjugatePicardIter n` on `(0,DB.T]`.
* `Hinf + huPaper + hsmall` gives strict positivity for iterates/limit via the inf-threshold lemmas.
* `Hinf.hgeom` gives geometric convergence of the iterates in value.
* `Hinf.hQ_int`, `Hinf.hQ_bound`, `Hinf.hB_int`, `Hinf.hL_bound`, `Hinf.hL_int` provide source bounds/integrability for positivity and Duhamel estimates.

Not available from those inputs:

* finite-iterate chem-div source `TimeC1On`;
* finite-iterate chem-flux slice derivative identity / div continuity for the source bridge;
* finite-iterate spatial `G1/G2` derivative bounds;
* positive-offset B-form restart for finite iterates (should be easy wrapper, but not found landed);
* uniform derivative-coefficient convergence for the limit passage.

## Circularity check

No circularity if the construction is layered as:

```text
finite iterate ball/positivity/bounds
  + finite iterate source bridge + B-form source TimeC1On
  + finite iterate G1/G2/restart/joint continuity
    ⇒ finite iterate logistic source TimeC1On tower
    ⇒ uniform limit data
    ⇒ limit logistic source TimeC1On
```

But there is circularity if one tries to obtain chem-div source `TimeC1On` from the final classical-solution theorem: the final B-form classical chain wants `hlogSrc`/`hchemSrc` in the bank, and those are exactly the source packages being built.

## Recommended implementation plan

### File 1: finite B-form restart wrappers

Land easy wrappers around existing generic B-form restart:

```lean
conjugatePicardIter_succ_global_cosine
conjugatePicardIter_succ_B_restart_of_global_cosine
```

### File 2: finite B-form source-bridge data package

Define `ConjIterSourceBridgeSliceData` and `source_bridge_of_conjIter_sliceData`. This isolates the chem-flux/divergence regularity gap.

### File 3: finite logistic source tower skeleton

Define:

```lean
ConjIterLogSourceCoeffs
ConjIterLogSourceTimeC1On
ConjIterLogSourceTimeC1OnUpTo
ConjSuccLogSourceWindowData
conjugateLevel0_logSourceTimeC1On
conjugateLogSourceTimeC1On_succ_of_windowData
conjugateIter_logSourceTimeC1On_all
```

This file can compile with `ConjSuccLogSourceWindowData` as an input record.

### File 4: analytic producers for `ConjSuccLogSourceWindowData`

This is the real work. It must provide:

* predecessor B-form source `TimeC1On` (`log + chem`);
* restart representation;
* `hbsum/hagree`;
* strict positivity/sup;
* `G1/G2`;
* `hC2cont`;
* `hprofile_joint`.

### File 5: limit passage

Define `ConjLogSourceLimitPassageData` and the theorem:

```lean
conjugateLimit_logSourceTimeC1On_of_limitData
```

Then separately prove the fields of `ConjLogSourceLimitPassageData`. The key missing field is `hadot_unif`.

## Final answer

For part (A), the Lean wrapper should be built around `sourceTimeC1On_succ_of_sourceTimeC1On`, but the induction must carry more than the previous logistic source package. The B-form successor uses the predecessor **B-form total source**, so each induction step needs predecessor chem-div `TimeC1On` plus source bridge/restart/G1/G2/joint-continuity data.

For part (B), `duhamelSourceTimeC1On_of_uniform_limit` is the right limit theorem, but geometric convergence alone is insufficient. You need coefficient convergence, uniform convergence of derivative coefficients, a common summable envelope, and a common derivative bound. The coefficient convergence is probably derivable from geometric convergence plus a logistic Lipschitz/coefficient lemma; the derivative convergence is the genuine gap.

The construction is not inherently circular unless the chem-div source package is imported from the final classical regularity theorem. It should be built at the finite-iterate/source-tower level instead.
