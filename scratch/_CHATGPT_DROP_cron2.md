# Q1018 (cron2) — `ResolverHasSpectralAgreementC2Coeff` for heat Level0 resolver

Static repo inspection only; I did **not** run Lean.

## Executive verdict

There is **no existing completed constructor** in the repo that directly produces

```lean
ResolverHasSpectralAgreementC2Coeff U
  (coupledChemicalConcentration p (conjugatePicardIter p u₀ 0))
```

for the heat semigroup Level0 resolver.

The closest existing infrastructure is:

1. `ResolverHasSpectralAgreementC2Coeff` itself, in
   `ShenWork/PDE/IntervalResolverJointC2C2Coeff.lean`.
2. A K1 packaging constructor:
   `resolverHasSpectralAgreementC2Coeff_of_localRestartC2` and
   `resolverHasSpectralAgreementC2Coeff_of_sourceFields`, in
   `ShenWork/Paper2/IntervalResolverSpectralAgreementC2CoeffFromK1.lean`.
3. A K1 constructor for **parabolic solution trajectories**:
   `resolverHasSpectralAgreement_of_ledger_of_subtypeCont`, in
   `ShenWork/Paper2/IntervalResolverSpectralAgreementFromK1.lean`.
4. A completed C2Coeff package for **shifted linear heat coefficients**:
   `shiftedHeatCoeff_c2Coeff`, in
   `ShenWork/Paper2/IntervalPicardLimitK1C2Heat.lean`.

But none of these directly handles the nonlinear elliptic resolver trajectory

```lean
v t = coupledChemicalConcentration p (conjugatePicardIter p u₀ 0) t
```

whose elliptic source coefficients are

```lean
cosineCoeffs (fun x => p.ν * (S(t)u₀ x)^p.γ) k
```

The existing K1 route is also not a clean fit for the χ₀<0 Level0 resolver target: `resolverHasSpectralAgreement_of_ledger_of_subtypeCont` assumes `hχ0 : p.χ₀ = 0` and constructs spectral restart data for a Picard/parabolic trajectory satisfying the gradient Duhamel equation, not for the static elliptic resolver of `ν u^γ`.

## What `ResolverHasSpectralAgreementC2Coeff` really asks for

From `IntervalResolverJointC2C2Coeff.lean`:

```lean
structure ResolverHasSpectralAgreementC2Coeff
    (T : ℝ) (v : ℝ → intervalDomainPoint → ℝ) : Prop where
  toSpectralAgreement :
    ShenWork.IntervalResolverTimeRegularity.ResolverHasSpectralAgreement T v
  exists_c2_data : ∀ t₀, 0 < t₀ → t₀ < T →
    ∃ (a₀ : ℕ → ℝ) (M : ℝ) (_ : 0 ≤ M) (_ : ∀ n, |a₀ n| ≤ M)
      (a : ℝ → ℕ → ℝ) (_ : DuhamelSourceTimeC2Coeff a) (offset : ℝ),
      (0 < t₀ - offset) ∧
      (∀ᶠ s in 𝓝 t₀, ∀ x : intervalDomainPoint,
        v s x = ∑' n, localRestartCoeff a₀ a (s - offset) n *
          cosineMode n x.1)
```

So the strengthened record is not just “`v` has cosine coefficients”.  It wants a **local parabolic restart representation** of `v`, plus a `DuhamelSourceTimeC2Coeff` package for the restart forcing `a`.

For an arbitrary smooth coefficient family

```lean
c n t := cosine coefficient of v(t)
```

one can mathematically manufacture a restart representation by setting, at a local offset `η < t₀`,

```lean
a₀ n := c n η
a ρ n := deriv (fun t => c n t) (η + ρ)
         + unitIntervalCosineEigenvalue n * c n (η + ρ)
```

Then `localRestartCoeff a₀ a (t - η) n` solves the scalar ODE

```text
C' = a - λ C,    C(0) = a₀,
```

and therefore should equal `c n t`.  But I did **not** find a generic committed constructor that packages this “arbitrary C¹ coefficient family → local restart representation” into `ResolverHasSpectralAgreement` / `ResolverHasSpectralAgreementC2Coeff`.

That generic constructor would be a useful shortcut target.

## Q1. Simplest way to construct `ResolverHasSpectralAgreement` for heat Level0 resolver

### For the heat semigroup **u itself**

If the target were simply

```lean
v := conjugatePicardIter p u₀ 0   -- i.e. S(t)u₀
```

then the simplest construction is direct: the heat coefficient

```lean
c n t = Real.exp (-t * λ n) * heatCoeff u₀ n
```

has a restart representation with source `a = 0` from any positive offset, or equivalently as a shifted homogeneous heat coefficient.  The file

```text
ShenWork/Paper2/IntervalPicardLimitK1C2Heat.lean
```

already has the relevant linear heat coefficient C2Coeff package:

```lean
shiftedHeatCoeff_timeC1
shiftedHeatCoeff_sourceC2CoeffFields
shiftedHeatCoeff_c2Coeff
```

This is for **linear shifted heat coefficients**.

### For the elliptic resolver **v = resolver(ν·u^γ)**

For the actual Level0 target,

```lean
v := coupledChemicalConcentration p (conjugatePicardIter p u₀ 0)
```

the repo does **not** contain a direct constructor.

The K1 constructor

```lean
resolverHasSpectralAgreement_of_ledger_of_subtypeCont
```

is not the right direct tool: it assumes `hχ0 : p.χ₀ = 0` and builds local restart data for a parabolic/Picard trajectory satisfying a Duhamel equation.  The elliptic resolver is instead a static-in-space operator at each time:

```lean
v̂_k(t) = sourcê_k(t) / (p.μ + λ_k)
```

where

```lean
sourcê_k(t) = cosineCoeffs (fun x => p.ν * (S(t)u₀ x)^p.γ) k.
```

So the simplest honest route is a **new direct coefficient-family constructor** for the resolver coefficients:

```lean
import ShenWork.PDE.IntervalResolverJointC2C2Coeff
import ShenWork.PDE.IntervalPhysicalResolverDataConcrete
import ShenWork.Paper2.IntervalConjugatePicard
import ShenWork.Paper2.IntervalPicardLevel0SourceTimeC1On

open Filter Topology Set
open ShenWork.IntervalDomain
open ShenWork.IntervalResolverJointC2
open ShenWork.IntervalResolverSpectralTimeC2
open ShenWork.IntervalSourceCoefficientTimeC1
open ShenWork.IntervalResolverJointC2PhysicalConcrete (resolverTimeCoeff)
open ShenWork.IntervalPhysicalResolverDataConcrete

noncomputable section

namespace ShenWork.Paper2.Level0ResolverSpectralAgreement

/-- Coefficients of the Level0 elliptic resolver. -/
def level0ResolverCoeff
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) : ℕ → ℝ → ℝ :=
  resolverTimeCoeff p (ShenWork.IntervalConjugatePicard.conjugatePicardIter p u₀ 0)

/-- Artificial parabolic restart source for the resolver coefficient family. -/
def level0ResolverRestartSource
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (offset : ℝ) :
    ℝ → ℕ → ℝ :=
  fun ρ k =>
    deriv (level0ResolverCoeff p u₀ k) (offset + ρ) +
      unitIntervalCosineEigenvalue k * level0ResolverCoeff p u₀ k (offset + ρ)

/-- Direct positive-time local restart C2 package for the Level0 elliptic resolver.
This is the missing constructor. -/
theorem level0_resolverHasSpectralAgreementC2Coeff_direct
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {U : ℝ}
    -- positive horizon and heat-level hypotheses go here
    :
    ResolverHasSpectralAgreementC2Coeff U
      (ShenWork.IntervalCoupledRegularityBootstrap.coupledChemicalConcentration
        p (ShenWork.IntervalConjugatePicard.conjugatePicardIter p u₀ 0)) := by
  -- For each t₀ ∈ (0,U), choose offset = t₀ / 2.
  -- a₀ := level0ResolverCoeff p u₀ · offset
  -- a  := level0ResolverRestartSource p u₀ offset
  -- prove DuhamelSourceTimeC2Coeff a from positive-time heat smoothing
  -- prove variation-of-constants identity for each coefficient
  -- prove cosine-series agreement for v on a neighborhood of t₀
  sorry

end ShenWork.Paper2.Level0ResolverSpectralAgreement
```

This avoids the K1 tower, but it requires proving the missing coefficient C2/bounds for the nonlinear source.

## Q2. What is `DuhamelSourceTimeC2Coeff` for the heat semigroup source? Existing theorem?

For Level0 resolver, the natural elliptic source coefficients are

```lean
a_src t k := cosineCoeffs
  (fun x => p.ν * (intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)^p.γ) k
```

For `t > 0`, these are mathematically smooth in time because `S(t)u₀` is heat-smoothed.  But I found **no completed theorem** in the repo giving

```lean
DuhamelSourceTimeC2Coeff a_src
```

or the equivalent `SourceC2CoeffFields` for this nonlinear source.

What exists:

### Existing `DuhamelSourceTimeC2Coeff` API

`IntervalResolverSpectralTimeC2.lean` defines:

```lean
structure DuhamelSourceTimeC2Coeff (a : ℝ → ℕ → ℝ) where
  toTimeC1 : DuhamelSourceTimeC1 a
  sourceEigenEnvelope : ℕ → ℝ
  sourceEigen_summable : Summable sourceEigenEnvelope
  sourceEigen_bound : ∀ s, 0 ≤ s → ∀ n,
    λ n * |a s n| ≤ sourceEigenEnvelope n
  sourceEigenSqEnvelope : ℕ → ℝ
  sourceEigenSq_summable : Summable sourceEigenSqEnvelope
  sourceEigenSq_bound : ∀ s, 0 ≤ s → ∀ n,
    λ n * (λ n * |a s n|) ≤ sourceEigenSqEnvelope n
  adotEigenEnvelope : ℕ → ℝ
  adotEigen_summable : Summable adotEigenEnvelope
  adotEigen_bound : ∀ s, 0 ≤ s → ∀ n,
    λ n * |toTimeC1.adot s n| ≤ adotEigenEnvelope n
  adotEigenSqEnvelope : ℕ → ℝ
  adotEigenSq_summable : Summable adotEigenSqEnvelope
  adotEigenSq_bound : ∀ s, 0 ≤ s → ∀ n,
    λ n * (λ n * |toTimeC1.adot s n|) ≤ adotEigenSqEnvelope n
```

So the source must carry λ and λ² summable envelopes for both the coefficient and its time derivative.

### Existing completed heat C2Coeff theorem is only linear

`IntervalPicardLimitK1C2Heat.lean` proves:

```lean
shiftedHeatCoeff_c2Coeff
```

for

```lean
shiftedHeatCoeff ε a₀ s n = exp (-(ε+s) * λ n) * a₀ n.
```

This is excellent for homogeneous heat coefficients, but it is not the nonlinear chemotaxis source `ν·(S(t)u₀)^γ`.

### Existing Level0 source theorem is C1On and logistic, not chem C2Coeff

`IntervalPicardLevel0SourceTimeC1On.lean` provides:

```lean
level0Source_timeC1On
level0Source_shiftedTimeC1On
```

These are for the logistic source family

```lean
cosineCoeffs (logisticLifted p (picardIter p u₀ 0 s)) k
```

and provide `DuhamelSourceTimeC1On`, not `DuhamelSourceTimeC2Coeff`.  They are not the elliptic chem source `ν·u^γ`.

### Existing physical source route is blocked globally

`IntervalPhysicalSourceTimeC2Concrete.lean` has a route from `FlooredSourceTimeData` to physical source C2 data, and `IntervalHeatSemigroupFlooredSourceTimeData.lean` tries to build that for Level0.  But that is the global/all-time route with the known `S(0)`/floor obstruction and sorry'd obligations.  It is not a completed positive-time `DuhamelSourceTimeC2Coeff` theorem.

Conclusion: the desired heat semigroup nonlinear source C2Coeff theorem is **not currently committed**.

## Q3. Is there a shortcut avoiding the full K1 tower?

Mathematically, yes.  In the repo, not yet as a completed theorem.

The shortcut is to avoid K1/local-Picard restart and construct `ResolverHasSpectralAgreementC2Coeff` directly from the explicit positive-time coefficient family of the elliptic resolver.

For a target time `t₀ > 0`, choose:

```lean
offset := t₀ / 2
a₀ n := resolverTimeCoeff p u n offset
a ρ n := deriv (resolverTimeCoeff p u n) (offset + ρ)
       + unitIntervalCosineEigenvalue n * resolverTimeCoeff p u n (offset + ρ)
```

Then prove:

```lean
resolverTimeCoeff p u n s = localRestartCoeff a₀ a (s - offset) n
```

near `t₀` by variation of constants.

This is much more direct than the K1 tower.  It needs four local ingredients:

1. `∀ n`, `resolverTimeCoeff p u n` is C² on a positive neighborhood.
2. The artificial restart source `a` has `DuhamelSourceTimeC2Coeff`.
3. The resolver cosine series agrees with `coupledChemicalConcentration` on the closed interval / interior neighborhood.
4. The resolver coefficient series has enough summability for the representation and eventual equality.

For heat Level0, all four are mathematically true from heat smoothing and elliptic weights.  But the nonlinear source estimates are not currently packaged.  In particular, proving `DuhamelSourceTimeC2Coeff a` still requires λ² envelopes for the nonlinear source and its time derivative.

The audit file

```text
ShenWork/Paper2/IntervalChiNegResolverC2SourceAudit.lean
```

matches this conclusion: the heat-factor route closes coefficient families already carrying an `exp(-ε λ)` factor, but not the actual clamped/nonlinear source family; closing resolver-C2 requires either a new direct positive-Duhamel/heat-factor producer or a higher-regularity bootstrap producing `sourceEigenEnvelope`, `sourceEigenSqEnvelope`, and the matching `adot` envelopes.

So the shortcut is the right design target, but it is a new proof, not just an application of an existing theorem.

## Q4. Minimal K1 inputs for `resolverHasSpectralAgreementC2Coeff_of_localRestartC2`

Strictly, the theorem in `IntervalResolverSpectralAgreementC2CoeffFromK1.lean` needs only:

```lean
theorem resolverHasSpectralAgreementC2Coeff_of_localRestartC2
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (H : ResolverHasSpectralAgreement T u)
    (mkL : ∀ σ, 0 < σ → σ < T → LocalRestartC2 p u T σ) :
    ResolverHasSpectralAgreementC2Coeff T u
```

Equivalently, using the source-fields wrapper:

```lean
theorem resolverHasSpectralAgreementC2Coeff_of_sourceFields
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (H : ResolverHasSpectralAgreement T u)
    (mkL : ∀ σ, 0 < σ → σ < T → LocalRestart p u T σ)
    (fields : ∀ σ (hσ0 : 0 < σ) (hσT : σ < T),
      SourceC2CoeffFields (mkL σ hσ0 hσT).srcC) :
    ResolverHasSpectralAgreementC2Coeff T u
```

So the minimal abstract inputs are:

```lean
H      : ResolverHasSpectralAgreement T u
mkL    : ∀ σ, 0 < σ → σ < T → LocalRestart p u T σ
fields : ∀ σ hσ0 hσT, SourceC2CoeffFields (mkL σ hσ0 hσT).srcC
```

If you build `mkL` using the existing K1 ledger constructor `localRestart_of_ledger`, the concrete input list expands to:

```lean
hχ0       : p.χ₀ = 0
hα        : 1 ≤ p.α
ha        : 0 ≤ p.a
hb        : 0 ≤ p.b
hu₀_cont  : Continuous (intervalDomainLift u₀)
hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀
hfix      : ∀ s, 0 < s → s < T → ∀ x, (hx : x ∈ Icc 0 1) →
              intervalDomainLift (u s) x = intervalGradientDuhamelMap p u₀ u s ⟨x,hx⟩
hsrc0     : DuhamelSourceL1ContOn
              (fun s k => cosineCoeffs (logisticLifted p (u s)) k) T
bc        : ℝ → ℕ → ℝ
hbsum     : ∀ σ, 0 < σ → σ < T →
              Summable (fun n => λ n * |bc σ n|)
hagree    : ∀ σ, 0 < σ → σ < T →
              EqOn (intervalDomainLift (u σ))
                (fun x => ∑' n, bc σ n * cosineMode n x) (Icc 0 1)
hpost     : ∀ σ, 0 < σ → σ < T → ∀ x ∈ Icc 0 1,
              0 < intervalDomainLift (u σ) x
hubt      : ∀ σ, 0 < σ → σ < T → ∀ x ∈ Icc 0 1,
              intervalDomainLift (u σ) x ≤ Msup
hG1t      : ∀ a' b', 0 < a' → b' < T → ∃ G1,
              ∀ σ ∈ Icc a' b', ∀ x ∈ Icc 0 1,
                |deriv (intervalDomainLift (u σ)) x| ≤ G1
hG2t      : ∀ a' b', 0 < a' → b' < T → ∃ G2,
              ∀ σ ∈ Icc a' b', ∀ x ∈ Icc 0 1,
                |deriv (deriv (intervalDomainLift (u σ))) x| ≤ G2
adott     : ℝ → ℕ → ℝ
hderivt   : ∀ σ, 0 < σ → σ < T → ∀ k,
              HasDerivAt
                (fun r => cosineCoeffs
                  (logisticSourceFun p.a p.b p.α (intervalDomainLift (u r))) k)
                (adott σ k) σ
hadotcontt : ∀ k, ContinuousOn (fun σ => adott σ k) (Ioo 0 T)
hMdott    : ∀ a' b', 0 < a' → b' < T → ∃ Mdot,
              ∀ σ ∈ Icc a' b', ∀ k, |adott σ k| ≤ Mdot
hLc       : ∀ t, 0 < t → t < T →
              ∀ s, 0 < s → s ≤ t → Continuous (logisticLifted p (u s))
```

and then, for C2:

```lean
fields : ∀ σ hσ0 hσT,
  SourceC2CoeffFields (localRestart_of_ledger ... hσ0 hσT).srcC
```

But this is the K1 parabolic/logistic tower, not the shortest route for the Level0 elliptic resolver.

## Recommended route for Level0 3C/3D

For the Level0 resolver, I would not try to force the existing K1 constructor.

The shortest sound target is a new positive-time, resolver-specific constructor:

```lean
import ShenWork.PDE.IntervalResolverJointC2C2Coeff
import ShenWork.PDE.IntervalPhysicalResolverDataConcrete
import ShenWork.PDE.IntervalResolverSpectralTimeC2
import ShenWork.Paper2.IntervalConjugatePicard
import ShenWork.Paper2.IntervalHeatSemigroupHighRegularity

open Filter Topology Set
open ShenWork.IntervalDomain
open ShenWork.IntervalResolverJointC2
open ShenWork.IntervalResolverSpectralTimeC2
open ShenWork.IntervalCoupledRegularityBootstrap
open ShenWork.IntervalResolverJointC2PhysicalConcrete (resolverTimeCoeff)

noncomputable section

namespace ShenWork.Paper2.Level0ResolverC2Coeff

/-- Missing local positive-time source-C2 package for the nonlinear heat-smoothed
chemotaxis source.  This is the real analytic core. -/
theorem level0_chemSource_DuhamelSourceTimeC2Coeff_local
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {offset : ℝ}
    (hoff : 0 < offset)
    -- plus heat coefficient bound, positivity/floor on the local window, etc.
    :
    DuhamelSourceTimeC2Coeff
      (fun ρ k => cosineCoeffs
        (fun x => p.ν *
          (intervalDomainLift
            (ShenWork.IntervalConjugatePicard.conjugatePicardIter p u₀ 0 (offset + ρ)) x) ^ p.γ)
        k) := by
  -- Prove from positive-time heat smoothing:
  -- source λ and λ² coefficient envelopes,
  -- adot λ and λ² envelopes.
  sorry

/-- Direct local restart C2 data for the Level0 elliptic resolver. -/
theorem level0_resolver_localRestartC2
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {U σ : ℝ}
    (hσ0 : 0 < σ) (hσU : σ < U)
    -- plus heat bounds/floor/summability data
    :
    -- either produce `LocalRestartC2` if you choose to reuse the K1 type,
    -- or directly produce the `exists_c2_data` witness required by
    -- `ResolverHasSpectralAgreementC2Coeff`.
    True := by
  -- offset := σ / 2
  -- a₀ := resolver coefficients at offset
  -- a := resolverCoeff' + λ * resolverCoeff
  -- srcC2 := DuhamelSourceTimeC2Coeff for a
  -- prove local restart representation by variation-of-constants
  trivial

end ShenWork.Paper2.Level0ResolverC2Coeff
```

This is smaller and more semantically correct than the full K1 tower.  The genuinely missing theorem is the local positive-time C2 coefficient/envelope package for the nonlinear heat-smoothed source (or equivalently for the artificial parabolic source of the resolver coefficient family).

## Bottom line

* Existing K1 C2 constructors package already-existing local restarts; they do **not** directly construct the heat Level0 elliptic resolver package.
* `IntervalPicardLevel0SourceTimeC1On.lean` gives a positive-window C1 package for the logistic Level0 source, not a `DuhamelSourceTimeC2Coeff` for `ν·(S(t)u₀)^γ`.
* `IntervalPicardLimitK1C2Heat.lean` gives C2Coeff for shifted **linear heat coefficients**, not the nonlinear chemotaxis source.
* The mathematically shortest route is a new direct positive-time constructor for the resolver coefficient family; the hard part is proving λ/λ² source and `adot` envelopes for `ν·(S(t)u₀)^γ` on a positive window.
