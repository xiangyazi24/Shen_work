# Q1334 / cron1 — `DuhamelSourceTimeC2Coeff` search report

Repo: `xiangyazi24/Shen_work`

Branch written: `chatgpt-scratch`

Target file updated by this drop:

```text
scratch/_CHATGPT_DROP_cron1.md
```

## Executive answer

`DuhamelSourceTimeC2Coeff` is **not** just a C²-in-time regularity package.  It is a strong spectral-restart source package requiring:

1. a `DuhamelSourceTimeC1 a` package;
2. λ-weighted and λ²-weighted summable envelopes for the source coefficients `a s n`;
3. λ-weighted and λ²-weighted summable envelopes for the time derivative `adot s n`.

So the line-158 `srcC2 : DuhamelSourceTimeC2Coeff a` obligation in

```text
ShenWork/Paper2/IntervalResolverLevel0SpectralC2Coeff.lean
```

is genuinely the deepest one.  For the level-0 resolver restart source

```lean
level0ResolverRestartSource p u₀ t₀ ρ k =
  deriv (resolverTimeCoeff p (heatLevel0 p u₀) k) (halfOffset t₀ + ρ)
    + unitIntervalCosineEigenvalue k *
      resolverTimeCoeff p (heatLevel0 p u₀) k (halfOffset t₀ + ρ)
```

building `DuhamelSourceTimeC2Coeff` means proving C¹ in `ρ` for this family plus those λ/λ² envelopes for both it and its derivative.  I did **not** find an existing producer for this exact heat-level-0 restart source.

There **is** a simpler path if the end goal is joint `C²` of the resolver value/gradient: avoid `ResolverHasSpectralAgreementC2Coeff` and use the committed physical/bounded-weight route:

```text
PhysicalSourceTimeC2
  → physicalResolverJointC2Data_of_floor
  → coupledChemical_jointContDiffAt_two / coupledChemical_grad_jointContDiffAt_two
```

This route is explicitly documented as avoiding `DuhamelSourceTimeC2Coeff` and the λ²/λ³ spectral restart ladder.

## 1. Exact structure fields

Definition location:

```text
ShenWork/PDE/IntervalResolverSpectralTimeC2.lean
```

Exact structure:

```lean
import ShenWork.PDE.IntervalResolverSpectralTimeC2

open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)

namespace ShenWork.IntervalResolverSpectralTimeC2

/-- Concrete source regularity strong enough to differentiate the restart
coefficients with one eigenvalue weight.  This strengthens
`DuhamelSourceTimeC1` by adding summable λ-weighted envelopes for the source
coefficients and their time derivatives. -/
structure DuhamelSourceTimeC2Coeff (a : ℝ → ℕ → ℝ) where
  toTimeC1 : DuhamelSourceTimeC1 a
  sourceEigenEnvelope : ℕ → ℝ
  sourceEigen_nonneg : ∀ n, 0 ≤ sourceEigenEnvelope n
  sourceEigen_summable : Summable sourceEigenEnvelope
  sourceEigen_bound : ∀ s, 0 ≤ s → ∀ n,
    unitIntervalCosineEigenvalue n * |a s n| ≤ sourceEigenEnvelope n
  sourceEigenSqEnvelope : ℕ → ℝ
  sourceEigenSq_nonneg : ∀ n, 0 ≤ sourceEigenSqEnvelope n
  sourceEigenSq_summable : Summable sourceEigenSqEnvelope
  sourceEigenSq_bound : ∀ s, 0 ≤ s → ∀ n,
    unitIntervalCosineEigenvalue n *
      (unitIntervalCosineEigenvalue n * |a s n|) ≤
        sourceEigenSqEnvelope n
  adotEigenEnvelope : ℕ → ℝ
  adotEigen_nonneg : ∀ n, 0 ≤ adotEigenEnvelope n
  adotEigen_summable : Summable adotEigenEnvelope
  adotEigen_bound : ∀ s, 0 ≤ s → ∀ n,
    unitIntervalCosineEigenvalue n * |toTimeC1.adot s n| ≤
      adotEigenEnvelope n
  adotEigenSqEnvelope : ℕ → ℝ
  adotEigenSq_nonneg : ∀ n, 0 ≤ adotEigenSqEnvelope n
  adotEigenSq_summable : Summable adotEigenSqEnvelope
  adotEigenSq_bound : ∀ s, 0 ≤ s → ∀ n,
    unitIntervalCosineEigenvalue n *
      (unitIntervalCosineEigenvalue n * |toTimeC1.adot s n|) ≤
        adotEigenSqEnvelope n

end ShenWork.IntervalResolverSpectralTimeC2
```

Important downstream facts in the same file:

```lean
localRestartCoeff_hasDerivAt
localRestartCoeffAdot_hasDerivAt
localRestartCoeffAdot_hasDerivAt_addot
localRestartCoeffAdot_continuous
localRestartCoeffAdot_contDiff_one
localRestartCoeff_contDiff_two
localRestartCoeffAdot_eigenvalue_summable
```

These explain why the package is so strong: it is designed to make the local restart coefficients themselves C² and to control their λ-weighted derivatives.

## 2. Existing producers / constructors found

### A. Weight transporters

File:

```text
ShenWork/PDE/IntervalDuhamelSourceTimeC2Coeff.lean
```

Producers:

```lean
import ShenWork.PDE.IntervalDuhamelSourceTimeC2Coeff

namespace ShenWork.IntervalDuhamelSourceTimeC2Coeff

/-- Mode-wise multiplication by a bounded weight preserves the strengthened
`DuhamelSourceTimeC2Coeff` package. -/
def duhamelSourceTimeC2Coeff_mul_weight
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC2Coeff a)
    (c : ℕ → ℝ) {Cw : ℝ} (hCw_nn : 0 ≤ Cw)
    (hCw : ∀ n, |c n| ≤ Cw) :
    DuhamelSourceTimeC2Coeff (fun s n => c n * a s n)

/-- The concrete elliptic resolver multiplier preserves
`DuhamelSourceTimeC2Coeff`. -/
def duhamelSourceTimeC2Coeff_resolver_weight
    (p : CM2Params) {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a) :
    DuhamelSourceTimeC2Coeff
      (fun s n => intervalNeumannResolverWeight p n * a s n)

end ShenWork.IntervalDuhamelSourceTimeC2Coeff
```

These are **transporters**, not base producers.  They assume a `DuhamelSourceTimeC2Coeff a` already exists.

### B. Source-field packer and local-restart wrapper

File:

```text
ShenWork/Paper2/IntervalPicardLimitK1C2Coeff.lean
```

This file introduces a field-level wrapper mirroring the fields of `DuhamelSourceTimeC2Coeff` except that it starts from an existing `DuhamelSourceTimeC1`:

```lean
import ShenWork.Paper2.IntervalPicardLimitK1C2Coeff

open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalResolverSpectralTimeC2 (DuhamelSourceTimeC2Coeff)

namespace ShenWork.Paper2.PicardLimitK1C2Coeff

/-- The raw source-side fields needed to upgrade a K1 C1 source package to the
coefficient-level C2 package.  These are source fields, not restart transport
facts. -/
structure SourceC2CoeffFields {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC1 a) where
  sourceEigenEnvelope : ℕ → ℝ
  sourceEigen_nonneg : ∀ n, 0 ≤ sourceEigenEnvelope n
  sourceEigen_summable : Summable sourceEigenEnvelope
  sourceEigen_bound : ∀ s, 0 ≤ s → ∀ n,
    unitIntervalCosineEigenvalue n * |a s n| ≤ sourceEigenEnvelope n
  sourceEigenSqEnvelope : ℕ → ℝ
  sourceEigenSq_nonneg : ∀ n, 0 ≤ sourceEigenSqEnvelope n
  sourceEigenSq_summable : Summable sourceEigenSqEnvelope
  sourceEigenSq_bound : ∀ s, 0 ≤ s → ∀ n,
    unitIntervalCosineEigenvalue n *
      (unitIntervalCosineEigenvalue n * |a s n|) ≤ sourceEigenSqEnvelope n
  adotEigenEnvelope : ℕ → ℝ
  adotEigen_nonneg : ∀ n, 0 ≤ adotEigenEnvelope n
  adotEigen_summable : Summable adotEigenEnvelope
  adotEigen_bound : ∀ s, 0 ≤ s → ∀ n,
    unitIntervalCosineEigenvalue n * |src.adot s n| ≤ adotEigenEnvelope n
  adotEigenSqEnvelope : ℕ → ℝ
  adotEigenSq_nonneg : ∀ n, 0 ≤ adotEigenSqEnvelope n
  adotEigenSq_summable : Summable adotEigenSqEnvelope
  adotEigenSq_bound : ∀ s, 0 ≤ s → ∀ n,
    unitIntervalCosineEigenvalue n *
      (unitIntervalCosineEigenvalue n * |src.adot s n|) ≤ adotEigenSqEnvelope n

/-- Assemble the existing `DuhamelSourceTimeC2Coeff` API from source-side fields. -/
def SourceC2CoeffFields.toC2Coeff {a : ℝ → ℕ → ℝ}
    {src : DuhamelSourceTimeC1 a} (F : SourceC2CoeffFields src) :
    DuhamelSourceTimeC2Coeff a

/-- Local restart data at K1, strengthened with the base C2 coefficient package for
the same clamped source family. -/
structure LocalRestartC2
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (T σ : ℝ) where
  base : ShenWork.Paper2.PicardLimitK1.LocalRestart p u T σ
  srcC2 : DuhamelSourceTimeC2Coeff base.aC

/-- Upgrade an existing K1 local restart once the source-side C2 coefficient fields
have been proved from the heat-kernel smoothing construction. -/
def LocalRestartC2.ofSourceFields
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {T σ : ℝ}
    (L : ShenWork.Paper2.PicardLimitK1.LocalRestart p u T σ)
    (F : SourceC2CoeffFields L.srcC) :
    LocalRestartC2 p u T σ

end ShenWork.Paper2.PicardLimitK1C2Coeff
```

Again, this is mostly a **packer**: it does not prove the source-side envelopes by itself.

### C. Shifted homogeneous heat-factor producer

File:

```text
ShenWork/Paper2/IntervalPicardLimitK1C2Heat.lean
```

This is the strongest actual base producer I found.  It handles coefficient families that already have a positive heat factor:

```lean
import ShenWork.Paper2.IntervalPicardLimitK1C2Heat

namespace ShenWork.Paper2.PicardLimitK1C2Heat

/-- Homogeneous heat-smoothed coefficients with a positive time shift. -/
def shiftedHeatCoeff (ε : ℝ) (a₀ : ℕ → ℝ) (s : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-(ε + s) * unitIntervalCosineEigenvalue n) * a₀ n

/-- The time derivative of `shiftedHeatCoeff`. -/
def shiftedHeatCoeffAdot (ε : ℝ) (a₀ : ℕ → ℝ) (s : ℝ) (n : ℕ) : ℝ :=
  -(unitIntervalCosineEigenvalue n *
      Real.exp (-(ε + s) * unitIntervalCosineEigenvalue n)) * a₀ n

/-- The shifted homogeneous heat coefficients form a `DuhamelSourceTimeC1`
package. -/
def shiftedHeatCoeff_timeC1
    {ε M : ℝ} {a₀ : ℕ → ℝ} (hε : 0 < ε) (_hM : 0 ≤ M)
    (ha₀ : ∀ n, |a₀ n| ≤ M) :
    DuhamelSourceTimeC1 (shiftedHeatCoeff ε a₀)

/-- Positive-time homogeneous heat smoothing gives all source-side C2
coefficient envelopes. -/
def shiftedHeatCoeff_sourceC2CoeffFields
    {ε M : ℝ} {a₀ : ℕ → ℝ} (hε : 0 < ε) (hM : 0 ≤ M)
    (ha₀ : ∀ n, |a₀ n| ≤ M) :
    SourceC2CoeffFields (shiftedHeatCoeff_timeC1 hε hM ha₀)

/-- The base `DuhamelSourceTimeC2Coeff` package obtained from the source fields. -/
def shiftedHeatCoeff_c2Coeff
    {ε M : ℝ} {a₀ : ℕ → ℝ} (hε : 0 < ε) (hM : 0 ≤ M)
    (ha₀ : ∀ n, |a₀ n| ≤ M) :
    DuhamelSourceTimeC2Coeff (shiftedHeatCoeff ε a₀)

end ShenWork.Paper2.PicardLimitK1C2Heat
```

This does **not** directly apply to `level0ResolverRestartSource`, because that source is defined as `c' + λc` for resolver coefficients `c`, not merely a shifted homogeneous heat coefficient family.

### D. Heat-factor bound bridge for raw clamped sources

File:

```text
ShenWork/Paper2/IntervalBC2H3EResolverAudit.lean
```

This file gives a useful generic producer from explicit heat-factor bounds:

```lean
import ShenWork.Paper2.IntervalBC2H3EResolverAudit

open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.Paper2.PicardLimitK1C2Coeff (SourceC2CoeffFields)

namespace ShenWork.Paper2.BC2H3EResolverAudit

/-- Raw-source heat-factor bridge.  This is the exact non-circular missing
shape for `LocalRestart.aC`: source coefficients carry `exp (-eps * lambda_n)`,
and source time derivatives carry one extra `lambda_n` times the same heat
factor. -/
def source_fields_of_heat_factor_bounds
    {a : ℝ → ℕ → ℝ} {src : DuhamelSourceTimeC1 a}
    {eps M Mdot : ℝ} (heps : 0 < eps) (hM : 0 ≤ M)
    (hMdot : 0 ≤ Mdot)
    (hsrc : ∀ s, 0 ≤ s → ∀ n,
      |a s n| ≤ Real.exp (-eps * unitIntervalCosineEigenvalue n) * M)
    (hadot : ∀ s, 0 ≤ s → ∀ n,
      |src.adot s n| ≤
        unitIntervalCosineEigenvalue n *
          Real.exp (-eps * unitIntervalCosineEigenvalue n) * Mdot) :
    SourceC2CoeffFields src

/-- Instantiation of the heat-factor bridge at the actual K1 local-restart
source family. -/
def local_restart_source_fields_of_heat_factor_bounds
    {p : CM2Params}
    {u : ℝ → ShenWork.IntervalDomain.intervalDomainPoint → ℝ}
    {T sigma : ℝ}
    (L : ShenWork.Paper2.PicardLimitK1.LocalRestart p u T sigma)
    {eps M Mdot : ℝ} (heps : 0 < eps) (hM : 0 ≤ M)
    (hMdot : 0 ≤ Mdot)
    (hsrc : ∀ s, 0 ≤ s → ∀ n,
      |L.aC s n| ≤ Real.exp (-eps * unitIntervalCosineEigenvalue n) * M)
    (hadot : ∀ s, 0 ≤ s → ∀ n,
      |L.srcC.adot s n| ≤
        unitIntervalCosineEigenvalue n *
          Real.exp (-eps * unitIntervalCosineEigenvalue n) * Mdot) :
    SourceC2CoeffFields L.srcC

/-- The K1 C2 closure point remains exactly `SourceC2CoeffFields` for the raw
clamped source package. -/
def source_fields_to_c2Coeff
    {a : ℝ → ℕ → ℝ}
    {src : DuhamelSourceTimeC1 a}
    (fields : SourceC2CoeffFields src) :
    DuhamelSourceTimeC2Coeff a

end ShenWork.Paper2.BC2H3EResolverAudit
```

This is useful if you can prove explicit heat-factor bounds for the source and its derivative.  It still does not provide a direct producer for the level-0 resolver restart source.

### E. Direct Duhamel bounds consume the structure; they do not produce it

File:

```text
ShenWork/PDE/IntervalDuhamelDirectC2Coeff.lean
```

This file proves direct bounds such as:

```lean
duhamelSpectralCoeff_eigenvalue_sq_bound_direct
duhamelSpectralCoeff_eigenvalue_sq_summable_direct
duhamelSpectralCoeff_eigenvalue_cube_bound_direct
```

but all of these already assume:

```lean
src : DuhamelSourceTimeC2Coeff a
```

So they are consumers, not producers.

## 3. Is there a simpler path avoiding `DuhamelSourceTimeC2Coeff` for heat level 0?

Yes — if the target is joint `C²` of the resolver/coupled chemical concentration, use the physical/bounded-weight lane.  The repo already has the architecture.

### Physical resolver data

File:

```text
ShenWork/PDE/IntervalResolverJointC2PhysicalConcrete.lean
```

Key structure:

```lean
structure PhysicalResolverJointC2Data
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (Bt : ℕ → ℕ → ℝ) : Prop where
  coeff_contDiff : ∀ k, ContDiff ℝ (2 : ℕ∞) (resolverTimeCoeff p u k)
  coeff_bound : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 →
    ‖iteratedFDeriv ℝ i (resolverTimeCoeff p u k) t‖ ≤ Bt i k
  value_summable : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (boundedWeightJointMajorant Bt m)
  grad_summable : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (boundedWeightJointGradMajorant Bt m)
```

And the two concrete producers:

```lean
theorem coupledChemical_jointContDiffAt_two
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Bt : ℕ → ℕ → ℝ}
    (H : PhysicalResolverJointC2Data p u Bt) {s x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        intervalDomainLift (coupledChemicalConcentration p u q.1) q.2) (s, x)

theorem coupledChemical_grad_jointContDiffAt_two
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Bt : ℕ → ℕ → ℝ}
    (H : PhysicalResolverJointC2Data p u Bt) {s x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        deriv (intervalDomainLift (coupledChemicalConcentration p u q.1)) q.2)
      (s, x)
```

### Source-side physical data → resolver physical data

File:

```text
ShenWork/PDE/IntervalPhysicalResolverDataConcrete.lean
```

The source-side package is:

```lean
structure PhysicalSourceTimeC2
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (Es : ℕ → ℕ → ℝ) : Prop where
  src_contDiff : ∀ k, ContDiff ℝ (2 : ℕ∞) (srcTimeCoeff p u k)
  src_bound : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 →
    ‖iteratedFDeriv ℝ i (srcTimeCoeff p u k) t‖ ≤ Es i k
  value_summable : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (boundedWeightJointMajorant
      (fun i k => intervalNeumannResolverWeight p k * Es i k) m)
  grad_summable : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (boundedWeightJointGradMajorant
      (fun i k => intervalNeumannResolverWeight p k * Es i k) m)
```

Then:

```lean
theorem physicalResolverJointC2Data_of_floor
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Es : ℕ → ℕ → ℝ}
    (H : PhysicalSourceTimeC2 p u Es) :
    PhysicalResolverJointC2Data p u
      (fun i k => intervalNeumannResolverWeight p k * Es i k)
```

This is exactly the lane that bypasses `DuhamelSourceTimeC2Coeff`.

### Practical skeleton for the bypass

For a theorem whose goal is the actual joint C² statement, use this shape instead of going through `resolverHasSpectralAgreementC2Coeff_heatLevel0`:

```lean
import ShenWork.PDE.IntervalPhysicalSourceTimeC2Concrete
import ShenWork.PDE.IntervalPhysicalResolverDataConcrete
import ShenWork.PDE.IntervalResolverJointC2PhysicalConcrete
import ShenWork.Paper2.IntervalConjugatePicard

open Set
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalPhysicalResolverDataConcrete
open ShenWork.IntervalResolverJointC2PhysicalConcrete
open ShenWork.IntervalCoupledRegularityBootstrap (coupledChemicalConcentration)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)

noncomputable section

namespace ShenWork.Paper2.ResolverLevel0SpectralC2Coeff

/-- Schematic: use physical source data to prove resolver value/gradient joint C²,
without constructing `DuhamelSourceTimeC2Coeff`. -/
theorem heatLevel0_resolver_jointC2_from_physical_source
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {Es : ℕ → ℕ → ℝ}
    (Hsrc : PhysicalSourceTimeC2 p (conjugatePicardIter p u₀ 0) Es)
    {s x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2
        (fun q : ℝ × ℝ =>
          intervalDomainLift
            (coupledChemicalConcentration p (conjugatePicardIter p u₀ 0) q.1) q.2)
        (s, x) ∧
      ContDiffAt ℝ 2
        (fun q : ℝ × ℝ =>
          deriv (intervalDomainLift
            (coupledChemicalConcentration p (conjugatePicardIter p u₀ 0) q.1)) q.2)
        (s, x) := by
  have Hres := physicalResolverJointC2Data_of_floor (p := p) Hsrc
  exact ⟨coupledChemical_jointContDiffAt_two Hres hx,
    coupledChemical_grad_jointContDiffAt_two Hres hx⟩

end ShenWork.Paper2.ResolverLevel0SpectralC2Coeff
```

If a downstream API explicitly demands

```lean
ResolverHasSpectralAgreementC2Coeff T v
```

then you cannot avoid the `DuhamelSourceTimeC2Coeff` field, because it is literally part of `exists_c2_data`.  But if the goal is only the actual analytic conclusion (`ContDiffAt ℝ 2` of resolver value/gradient), the physical route is strictly simpler and already designed to avoid the spectral restart ladder.

## Diagnosis for the four `sorry` in `resolverHasSpectralAgreementC2Coeff_heatLevel0`

Current theorem file:

```text
ShenWork/Paper2/IntervalResolverLevel0SpectralC2Coeff.lean
```

Remaining obligations:

1. **line 143 coefficient bound**:
   `∃ M ≥ 0, ∀ n, |level0ResolverRestartA0 p u₀ t₀ n| ≤ M`.
   This is comparatively easy: positive-time heat/resolver smoothing or a crude boundedness lemma at fixed `offset = t₀/2` should suffice.

2. **line 158 `srcC2 : DuhamelSourceTimeC2Coeff a`**:
   deepest.  It requires a full C1 source package plus λ/λ² envelopes for
   `a ρ k = c'_k(offset+ρ)+λ_k c_k(offset+ρ)` and the derivative `a'`.
   I found no existing producer for this exact `a`.

3. **line 168 global `HasDerivAt`**:
   required only because `localRestartCoeff_variation_of_constants` is global in time.
   For heat level 0, the natural coefficient regularity is positive-time/local.  A local/windowed VOC lemma would remove this global burden.

4. **line 177 continuous derivative**:
   same issue: should follow from local positive-time C² coefficient regularity, but the current VOC interface asks for global continuity of `deriv c_k`.

## Recommended action

For `resolverHasSpectralAgreementC2Coeff_heatLevel0` specifically, either:

1. keep it as a spectral-restart theorem and expect a substantial proof of `DuhamelSourceTimeC2Coeff` for `level0ResolverRestartSource`; or
2. replace the consumer so that it uses `PhysicalResolverJointC2Data`/`PhysicalSourceTimeC2` instead of `ResolverHasSpectralAgreementC2Coeff`.

I recommend option 2 for heat level 0.  The repo comments already say the physical resolver lane bypasses `DuhamelSourceTimeC2Coeff`; the level-0 theorem’s own comment says the existing physical resolver route bypasses this structure.  So line 158 is not the right closure point unless you specifically need the spectral restart certificate as a data artifact.

No local `lake build` was run; this drop was produced through the GitHub connector only.
