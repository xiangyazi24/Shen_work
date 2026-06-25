# Q452 / cron1: spatial `C²` of `coupledChemDivSourceLift` for B-form iterates

## Executive verdict

I do **not** find a theorem in the repo that proves

```lean
ContDiffOn ℝ 2
  (coupledChemDivSourceLift p (conjugatePicardIter p u₀ n) s)
  (Set.Icc (0 : ℝ) 1)
```

for `s > 0`, nor a theorem that proves the corresponding homogeneous Neumann endpoint data

```lean
Tendsto (deriv (coupledChemDivSourceLift p (conjugatePicardIter p u₀ n) s))
  (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)

Tendsto (deriv (coupledChemDivSourceLift p (conjugatePicardIter p u₀ n) s))
  (nhdsWithin 1 (Set.Iio 1)) (nhds 0)

deriv (coupledChemDivSourceLift p (conjugatePicardIter p u₀ n) s) 0 = 0

deriv (coupledChemDivSourceLift p (conjugatePicardIter p u₀ n) s) 1 = 0
```

The repo contains several **conditional consumers** of exactly this kind of `C²`/Neumann regularity, and several **higher-level residual bundles** that carry it as an input, but no unconditional producer for `conjugatePicardIter` or `conjugatePicardLimit`.

The strongest current conclusion is:

```text
Spatial C²-Neumann regularity of the chem-div source is still a genuine residual.
For the B-form iterates, the current existence data only gives boundedness,
nonnegativity, continuous spatial slices, and joint measurability — not enough.
```

This matches the repo's own comments in `SourceSliceC2Neumann.lean`: logistic source C²-Neumann is discharged from banked `u`-regularity, but the **chem source** is explicitly marked as a residual because `intervalDomainChemotaxisDiv` differentiates a flux already containing `∂ₓv`; `ContDiffOn ℝ 2` of the source requires more than the banked `C²` u/v data.

---

## 1. Definitions: what the target is

`coupledChemDivSourceLift` is defined in `ShenWork/PDE/IntervalCoupledSourceTimeC1.lean:18-28`:

```lean
/-- Lifted chemotaxis-divergence source with the elliptic resolver substituted. -/
def coupledChemDivSourceLift (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (s : ℝ) : ℝ → ℝ :=
  intervalDomainLift
    (fun x => intervalDomainChemotaxisDiv p (u s)
      (coupledChemicalConcentration p u s) x)

/-- Cosine coefficients of the chemotaxis-divergence source. -/
def coupledChemDivSourceCoeffs (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) : ℝ → ℕ → ℝ :=
  fun s n => cosineCoeffs (coupledChemDivSourceLift p u s) n
```

`intervalDomainChemotaxisDiv` is defined in `ShenWork/PDE/IntervalDomain.lean:2922-2932`:

```lean
def intervalDomainLaplacian (f : intervalDomainPoint → ℝ)
    (x : intervalDomainPoint) : ℝ :=
  deriv (fun y : ℝ => deriv (intervalDomainLift f) y) x.1

def intervalDomainChemotaxisDiv (p : CM2Params)
    (u v : intervalDomainPoint → ℝ) (x : intervalDomainPoint) : ℝ :=
  deriv
    (fun y : ℝ =>
      intervalDomainLift u y * deriv (intervalDomainLift v) y /
        (1 + intervalDomainLift v y) ^ p.β)
    x.1
```

So your target is the `C²` regularity of the **spatial derivative of a flux**:

```lean
Q(y) = lift u(y) * deriv(lift v)(y) / (1 + lift v(y))^β
chemDiv = deriv Q
```

For `chemDiv` to be `C²`, the flux `Q` must effectively have three spatial derivatives on the interval; since `Q` already contains `deriv v`, this pushes the resolver side to higher regularity.

---

## 2. No direct `ContDiffOn` producer for the requested iterate target

Searches performed:

```text
coupledChemDivSourceLift ContDiffOn
coupledChemDivSourceLift
intervalDomainChemotaxisDiv ContDiffOn
coupledChemDivSourceLift neumann
coupledChemDivSourceLift deriv
```

The hits are not unconditional producers for

```lean
u = conjugatePicardIter p u₀ n
```

Instead they fall into these buckets:

1. **conditional consumers of `ContDiffOn` + Neumann data**, e.g. Fourier/H² packaging;
2. **residual bundles** that carry the missing regularity as fields;
3. **flux-level joint C² packages**, which prove joint regularity of the chem-div flux, not closed-interval `ContDiffOn` of the chem-div source slice;
4. **EWA/realSlice route diagnostics**, explicitly saying chem source C²-Neumann is not discharged from banked `C²` data.

I did not find a theorem with a conclusion shaped like:

```lean
theorem ...
  (D : ConjugateMildExistenceData p u₀) ... :
  ContDiffOn ℝ 2
    (coupledChemDivSourceLift p (conjugatePicardIter p u₀ n) s)
    (Set.Icc (0 : ℝ) 1)
```

nor one for the limit:

```lean
ContDiffOn ℝ 2
  (coupledChemDivSourceLift p (conjugatePicardLimit p u₀ DB.T) s)
  (Set.Icc (0 : ℝ) 1)
```

---

## 3. Conditional C²/Neumann consumers that require your target

### 3.1 `chemDivSource_weakH2_of_spatialC2`

`ShenWork/PDE/IntervalChemDivFluxFACSourceDecay.lean:20-35` has a clean packager:

```lean
/-- **Per-slice weak-`H²ₙ` certificate for the chem-div source.**

From the source slice being `C²` on `[0,1]` with homogeneous Neumann endpoint
data, the committed `intervalWeakH2Neumann_of_contDiffOn` packager yields the
weak `H²_N` certificate whose weak second derivative is `deriv (deriv f)`. -/
def chemDivSource_weakH2_of_spatialC2
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s : ℝ}
    (hC2 : ContDiffOn ℝ 2 (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1))
    (ht0 : Tendsto (deriv (coupledChemDivSourceLift p u s))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0))
    (ht1 : Tendsto (deriv (coupledChemDivSourceLift p u s))
      (nhdsWithin (1 : ℝ) (Iio 1)) (nhds 0))
    (hbc0 : deriv (coupledChemDivSourceLift p u s) 0 = 0)
    (hbc1 : deriv (coupledChemDivSourceLift p u s) 1 = 0) :
    IntervalWeakH2Neumann (coupledChemDivSourceLift p u s) :=
  intervalWeakH2Neumann_of_contDiffOn hC2 ht0 ht1 hbc0 hbc1
```

This is exactly the shape you need — but as **hypotheses**, not as a producer.

### 3.2 `hchemFourier_of_chemDiv_C2Neumann`

`ShenWork/Paper2/IntervalBankChemDivFourier.lean:45-91` gives Fourier summability from `C²`/Neumann data:

```lean
/-- **Conditional `ℓ¹` Fourier summability of a chemotaxis-divergence slice.**

Given the chemotaxis-divergence slice `s x = intervalDomainChemotaxisDiv p u v x`
(a function `intervalDomainPoint → ℝ`), assume:

* `hcont` — `s` is continuous on the subtype (so its constant extension to `ℝ` is
  globally continuous);
* `hC2` — the lift of `s` to `ℝ` is `C²` on `[0,1]`;
* `htend0`/`htend1` — the one-sided derivative limits of the lift vanish at the
  endpoints `0` and `1`;
* `hbc0`/`hbc1` — the lift satisfies homogeneous Neumann boundary data
  (`deriv = 0` at the endpoints).

Then the `ℤ`-indexed even-reflection Fourier coefficients of the constant extension
of `s` are absolutely summable. -/
theorem hchemFourier_of_chemDiv_C2Neumann
    (p : CM2Params) (u v : intervalDomainPoint → ℝ)
    (hcont : Continuous (fun x : intervalDomainPoint =>
      intervalDomainChemotaxisDiv p u v x))
    (hC2 : ContDiffOn ℝ 2
      (intervalDomainLift (fun x => intervalDomainChemotaxisDiv p u v x))
      (Set.Icc (0 : ℝ) 1))
    (htend0 : Filter.Tendsto
      (deriv (intervalDomainLift (fun x => intervalDomainChemotaxisDiv p u v x)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (htend1 : Filter.Tendsto
      (deriv (intervalDomainLift (fun x => intervalDomainChemotaxisDiv p u v x)))
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0))
    (hbc0 : deriv
      (intervalDomainLift (fun x => intervalDomainChemotaxisDiv p u v x)) 0 = 0)
    (hbc1 : deriv
      (intervalDomainLift (fun x => intervalDomainChemotaxisDiv p u v x)) 1 = 0) :
    Summable (fun n : ℤ =>
      fourierCoeff
        (reflCircle
          (intervalDomainConstExtend
            (fun x : intervalDomainPoint =>
              intervalDomainChemotaxisDiv p u v x))) n)
```

Again, this is a **consumer** of the requested regularity.

### 3.3 `hchemFourier_slice_of_limit_C2Neumann`

`ShenWork/Paper2/IntervalBankChemDivFourier.lean:93-136` specializes the same conditional result to a limit trajectory:

```lean
theorem hchemFourier_slice_of_limit_C2Neumann
    (p : CM2Params) (limit : ℝ → intervalDomainPoint → ℝ) (t : ℝ)
    (hcont : Continuous (fun x : intervalDomainPoint =>
      intervalDomainChemotaxisDiv p (limit t)
        (coupledChemicalConcentration p limit t) x))
    (hC2 : ContDiffOn ℝ 2
      (intervalDomainLift (fun x => intervalDomainChemotaxisDiv p (limit t)
        (coupledChemicalConcentration p limit t) x))
      (Set.Icc (0 : ℝ) 1))
    ... Neumann endpoint data ... :
    Summable (fun n : ℤ => fourierCoeff ... n)
```

It still takes `hC2` and Neumann as hypotheses.

---

## 4. Interior continuity exists only as a consequence of assumed C²

`ShenWork/Paper2/IntervalBankChemSliceFix.lean:84-99` proves only interior continuity from assumed `ContDiffOn`:

```lean
/-- **The chemotaxis-divergence lift is continuous on the open interior.**
`ContDiffOn ℝ 2` on the closed `Icc 0 1` restricts to `ContinuousOn` on the open
`Ioo 0 1` (interior continuity); the endpoint discontinuity is excluded. -/
theorem chemDivLift_continuousOn_Ioo
    {p : CM2Params} {u v : intervalDomainPoint → ℝ}
    (hC2 : ContDiffOn ℝ 2 (chemDivLift p u v) (Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (chemDivLift p u v) (Set.Ioo (0 : ℝ) 1) :=
  (hC2.continuousOn).mono Set.Ioo_subset_Icc_self
```

This file is important because its module comment explains an endpoint issue: the hard-coded constant-extension representative is false/discontinuous at endpoints, and the repair is an `Ioo`-agreement package.  Lines `24-31` explicitly state the discontinuity diagnosis; lines `44-59` summarize what the file actually lands.

This is relevant to your Neumann question: endpoint behavior is delicate.  The repo does not treat closed-endpoint chem-div regularity as automatic.

---

## 5. Flux-level joint C² exists conditionally, but it is not source-slice C²

`ShenWork/PDE/IntervalChemDivFluxJointC2Producer.lean` has product/quotient/rpow calculus for the **flux**:

```lean
/-- Product/quotient/rpow calculus for the lifted chem-div flux. -/
theorem coupledChemDivFlux_contDiffAt_of_factorJointC2
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s x : ℝ}
    (hu : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (s, x))
    (hv : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        intervalDomainLift (coupledChemicalConcentration p u q.1) q.2)
      (s, x))
    (hgradv : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        deriv (intervalDomainLift (coupledChemicalConcentration p u q.1))
          q.2)
      (s, x))
    (hbase : 0 <
      1 + intervalDomainLift (coupledChemicalConcentration p u s) x) :
    ContDiffAt ℝ 2
      (Function.uncurry (coupledChemDivFluxLift p u)) (s, x)
```

This proves joint `C²` of

```lean
coupledChemDivFluxLift p u s x
```

not `ContDiffOn ℝ 2` of

```lean
coupledChemDivSourceLift p u s = ∂ₓ(coupledChemDivFluxLift p u s)
```

The same file defines `CoupledChemDivFluxFactorJointC2Inputs`; its local slab asks for continuity of `coupledChemDivSourceLift`, factor joint C², positivity, and time derivative data, then produces outer-commute/source-time-C¹ wiring.  It does not provide the closed-slice `C²`/Neumann theorem you ask for.

Important fields from `ShenWork/PDE/IntervalChemDivFluxJointC2Producer.lean:81-110`:

```lean
structure CoupledChemDivFluxFactorJointC2Inputs
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  exists_local_slab : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
    (∀ᶠ s in 𝓝 τ,
      ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1)) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      ContDiffAt ℝ 2
        (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (s, x)) ∧
    ... resolver factor C² fields ...
```

So even the advanced flux machinery only carries **source continuity** on `Icc`, not source `ContDiffOn ℝ 2`.

---

## 6. Explicit residual bundle: chem-div source regularity is carried, not produced

`ShenWork/Paper2/IntervalChemDivWinDischarge.lean` is the clearest audit/producer file for the chem-div source window.  The module comment says the gradient mild solution data is insufficient and names the real residual.

Key comments from `IntervalChemDivWinDischarge.lean:34-46`:

```text
GradientMildSolutionData carries only HasContinuousSlices (per-slice spatial continuity)
and HasJointMeasurability of D.u, plus pointwise bound/nonneg/positivity facts.  It does
not carry the time-C²/space-C² parabolic regularity that IterateSourceTimeData demands
(time1/time2: the solution is twice differentiable in time with explicit derivative fields;
sliceC2/sliceNeumann: each slice is space-C² with Neumann endpoint data).  The positivity
floor IterateSourceTimeData.floor IS available (from D.hpos), but the time/space C² legs
are the genuine solution-regularity residual.
```

The residual structure is in `IntervalChemDivWinDischarge.lean:75-120`:

```lean
/-- **The genuine residual bundle.**  Everything `CoupledChemDivTimeC1Fields p u`
needs that is NOT carried by a bare `GradientMildSolutionData`: the iterate
time-`C²`/space-`C²` source datum `IterateSourceTimeData`, the bounded-weight
`ℓ¹` source summability (value + gradient), the FAC slab `other`, the chem-div
source weak-`H²ₙ`/decay/zeroth-coefficient envelopes, and the time-derivative
coefficient continuity/uniform-bound. -/
structure ChemDivSolutionRegularityResidual
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) where
  du : ℝ → ℝ → ℝ
  d2u : ℝ → ℝ → ℝ
  hiter : ShenWork.IntervalFlooredSourceTimeDataIterate.IterateSourceTimeData p u du d2u
  ...
  hH2 : ∀ s, 0 ≤ s → IntervalWeakH2Neumann (coupledChemDivSourceLift p u s)
  hdecay : ∀ s, 0 ≤ s → ∀ k : ℕ, 1 ≤ k →
    |cosineCoeffs (coupledChemDivSourceLift p u s) k| ≤ Cchem / ((k : ℝ) * Real.pi) ^ 2
  hzero : ∀ s, 0 ≤ s →
    |cosineCoeffs (coupledChemDivSourceLift p u s) 0| ≤ Cchem
  ...
```

Then the actual producer is conditional on that residual:

```lean
noncomputable def coupledChemDivSource_timeC1On_of_gradientSolution
    (D : GradientMildSolutionData p u₀)
    (R : ChemDivSolutionRegularityResidual p D.u) :
    DuhamelSourceTimeC1On (coupledChemDivSourceCoeffs p D.u) 0 D.T
```

This is for `GradientMildSolutionData`, not `conjugatePicardIter`; and even there it requires the residual.

---

## 7. `IterateSourceTimeData` contains C²/Neumann data, but for the resolver source, not directly for chem-div source

`ShenWork/PDE/IntervalFlooredSourceTimeDataIterate.lean` defines the honest iterate time/space regularity package for the concrete source slice

```lean
srcSlice p u t x = p.ν * (intervalDomainLift (u t) x)^p.γ
```

Its comments and fields are strong evidence that the needed regularity is not derivable from mere ball data.  The structure appears at `IntervalFlooredSourceTimeDataIterate.lean:95-147` and includes:

```lean
structure IterateSourceTimeData
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (du d2u : ℝ → ℝ → ℝ)
    : Prop where
  floor : ∀ t : ℝ, ∀ x ∈ Ioo (0:ℝ) 1, 0 < intervalDomainLift (u t) x
  time1 : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧ ...
  time2 : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧ ...
  sliceC2 : ∀ i : ℕ, i ≤ 2 → ∀ t : ℝ,
    ContDiffOn ℝ 2
      ((sliceFam (srcSlice p u) (srcSlice1 p u du) (srcSlice2 p u du d2u) i) t)
      (Icc (0:ℝ) 1)
  sliceNeumann : ∀ i : ℕ, i ≤ 2 → ∀ t : ℝ,
    Tendsto (deriv ((sliceFam ...) i t)) (𝓝[Ioi 0] 0) (𝓝 0) ∧
    Tendsto (deriv ((sliceFam ...) i t)) (𝓝[Iio 1] 1) (𝓝 0) ∧
    deriv ((sliceFam ...) i t) 0 = 0 ∧
    deriv ((sliceFam ...) i t) 1 = 0
  zerothBound : ...
  laplBound : ...
```

This is not a direct theorem about `coupledChemDivSourceLift`; rather, it feeds the resolver/FAC machinery needed to eventually produce chem-div source time-regularity.

---

## 8. EWA route explicitly says chem source C²-Neumann is not discharged from banked C² data

`ShenWork/Wiener/EWA/SourceSliceC2Neumann.lean:42-56` is directly on point.  It states that the logistic source C²-Neumann data is discharged, but the chem source is not:

```text
CHEM source — precise regularity-budget residual (NOT discharged).
`intervalDomainChemotaxisDiv p u v x = ∂ₓ( lift u · ∂ₓ(lift v) / (1 + lift v)^β )`
is ONE spatial derivative of an expression already containing `∂ₓ(lift v)`.  For
this slice to be `ContDiffOn ℝ 2` on `[0,1]` the bracketed inner expression must be
`ContDiffOn ℝ 3`, which forces `lift u ∈ C³` AND `∂ₓ(lift v) ∈ C³`, i.e.
`lift v ∈ C⁴`.  The banked u/v regularity is only `C²` on both sides ...
So the chem source genuinely needs `lift (realSlice u_star t) ∈ C³` and
`lift (coupledChemicalConcentration p (realSlice u_star) t) ∈ C⁴`; neither is among
the banked atoms.
```

This is not about `conjugatePicardIter` specifically, but it confirms the regularity budget: `C²` of the chem-div source is stronger than the usual `C²` of the solution/resolver slices.

---

## 9. Neumann boundary data status

I did not find a direct producer of the Neumann endpoint data for

```lean
coupledChemDivSourceLift p (conjugatePicardIter p u₀ n) s
```

The endpoint data appear as hypotheses in the packagers:

* `chemDivSource_weakH2_of_spatialC2` requires `ht0`, `ht1`, `hbc0`, `hbc1` for `coupledChemDivSourceLift`.
* `hchemFourier_of_chemDiv_C2Neumann` requires the same one-sided limits and point derivatives for the lifted `intervalDomainChemotaxisDiv` slice.
* `IterateSourceTimeData.sliceNeumann` carries Neumann data for `srcSlice`, `srcSlice1`, `srcSlice2`, not directly for `coupledChemDivSourceLift`.
* `ChemDivSolutionRegularityResidual.hH2` carries the resulting `IntervalWeakH2Neumann (coupledChemDivSourceLift p u s)`, which already packages the consequence, but it is not produced from `conjugatePicardIter`.

Also, the repo contains explicit warnings that endpoint behavior of chem-div lift/const-extension is subtle and in some hard-coded forms false.  `IntervalBankChemSliceFix.lean:24-31` says the constant-extension representative is discontinuous at endpoints because `intervalDomainChemotaxisDiv = deriv φ` with `φ` built from zero-extension, forcing endpoint derivative behavior that differs from the generic interior limit.

So: no, the Neumann BC of the chem-div source does not appear to be landed for conjugate iterates.

---

## 10. What exists for `conjugatePicardIter` itself

The B-form Picard machinery gives only low-regularity iterate facts.  In `IntervalConjugatePicard.lean`, `ConjugateMildExistenceData` carries:

```lean
hbase_ball : ∀ t, 0 < t → t ≤ T → ∀ x, |conjugatePicardIter p u₀ 0 t x| ≤ M
hbase_nonneg : ∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ conjugatePicardIter p u₀ 0 t x
hbase_cont : HasContinuousSlices T (conjugatePicardIter p u₀ 0)
hmapsTo : ... preserves ball bound
hmapsTo_nn : ... preserves nonnegativity
hmapsTo_pos : ... preserves strict positivity
hcont_preserved : ... preserves HasContinuousSlices
hbase_meas : HasJointMeasurability (conjugatePicardIter p u₀ 0)
hmeas_preserved : ... preserves HasJointMeasurability
```

The derived `iter_ball_package` in `IntervalBankInfAndLogSrcWiring.lean` similarly gives:

```lean
(∀ t, 0 < t → t ≤ D.T → ∀ x, |conjugatePicardIter p u₀ n t x| ≤ D.M) ∧
(∀ t, 0 < t → t ≤ D.T → ∀ x, 0 ≤ conjugatePicardIter p u₀ n t x) ∧
HasContinuousSlices D.T (conjugatePicardIter p u₀ n) ∧
HasJointMeasurability (conjugatePicardIter p u₀ n)
```

There is no `ContDiffOn`/`C²` iterate package analogous to what your target needs.

---

## Final answer

* `ContDiffOn ℝ 2 (coupledChemDivSourceLift p (conjugatePicardIter p u₀ n) s) (Icc 0 1)` is **not already proved** in the repo.
* The corresponding Neumann endpoint data are **not already proved** for `conjugatePicardIter` either.
* The repo has several **conditional** tools that consume exactly this C²/Neumann data (`chemDivSource_weakH2_of_spatialC2`, `hchemFourier_of_chemDiv_C2Neumann`, `hchemFourier_slice_of_limit_C2Neumann`), but they do not produce it.
* The strongest productive chain for chem-div source time regularity goes through a residual bundle (`ChemDivSolutionRegularityResidual`) containing `IterateSourceTimeData`, FAC/resolver summability, `hH2`, coefficient decay, and derivative-coefficient bounds.
* For B-form/conjugate Picard iterates, the existing `ConjugateMildExistenceData` / `iter_ball_package` only yields ball, nonnegativity, continuous slices, and joint measurability — insufficient for source C².
* Endpoint regularity is especially nontrivial: the repo explicitly records false/discontinuous closed-endpoint const-extension behavior for chem-div and replaces it with an `Ioo`-agreement route.

Recommended next target: prove or package a B-form iterate regularity residual analogous to `ChemDivSolutionRegularityResidual`, specialized to `u = conjugatePicardIter p u₀ n`, rather than trying to derive source `C²` directly from the existing ball package.
