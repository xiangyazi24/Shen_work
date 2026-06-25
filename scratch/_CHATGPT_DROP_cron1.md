# Q374 / cron1: What is `CoupledDuhamelT6SliceAgreement p D.T D.u`, and does it depend on `χ₀`?

## Executive verdict

`CoupledDuhamelT6SliceAgreement p T u` is **not** merely the ordinary statement that each slice `u t` agrees with its own cosine series, as one would get from a generic Picard-limit/cosine convergence argument.

It is a much more specific T6 handoff predicate:

```text
for every interior time t, the lifted slice intervalDomainLift (u t)
agrees on [0,1] with the inhomogeneous Neumann-heat Duhamel profile
built from the full coupled source coefficients coupledChemicalSourceCoeffs p u s.
```

That full source is chemotaxis-specific.  It is the coupled source

```lean
(-p.χ₀ * chemotaxisDiv) + logistic
```

with the elliptic resolver substituted into the chemical concentration.  Therefore the predicate **does depend on `χ₀` through `p`**, although it is not restricted to the negative-`χ₀` regime and does not use the sign of `χ₀`.  When `p.χ₀ = 0`, the chemotaxis part of the source split vanishes, so the same definition specializes to the logistic-only source.  For general nonzero `χ₀`, it is genuinely coupled/chemotaxis-specific.

Short answer to the user’s fork:

```text
It is about agreement with a T6 Duhamel source profile, not plain slice Fourier inversion.
The profile uses the full coupled source coefficients, hence it is χ₀-dependent via p.χ₀.
```

---

## Exact definition

The definition is in:

```text
ShenWork/PDE/IntervalCoupledRegularityBanked.lean
```

Lean context:

```lean
import ShenWork.PDE.IntervalCoupledRegularityBanked

open MeasureTheory
open scoped Topology

namespace ShenWork.IntervalCoupledRegularityBootstrap

open ShenWork.IntervalDomain
open ShenWork.IntervalDuhamelClosedC2
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalNeumannFullKernel
open ShenWork.Paper2
```

Definition:

```lean
/-- The exact slice agreement needed to apply the T6 Duhamel closed-`C²` atom to
the coupled fixed point slice.  This is the missing bridge between the fixed
point equation and the spectral Duhamel profile. -/
def CoupledDuhamelT6SliceAgreement
    (p : CM2Params) (T : ℝ) (u : ℝ → intervalDomainPoint → ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → t < T →
    Set.EqOn (intervalDomainLift (u t))
      (fun x => ∫ s in (0 : ℝ)..t,
        unitIntervalCosineHeatValue (t - s)
          (coupledChemicalSourceCoeffs p u s) x)
      (Set.Icc (0 : ℝ) 1)
```

Key observations:

1. The right side is **not**

```lean
fun x => ∑' n, b t n * cosineMode n x
```

for an arbitrary slice coefficient family `b t n`.

2. The right side is an **integral in time** of the Neumann heat evolution of a coefficient sequence:

```lean
unitIntervalCosineHeatValue (t - s)
  (coupledChemicalSourceCoeffs p u s) x
```

3. There is no `u₀` argument in the predicate.  It is not the usual full mild formula

```text
S(t) u₀ + ∫₀ᵗ S(t-s) F(u(s)) ds.
```

It is specifically the source-Duhamel profile consumed by the T6 closed-`C²` atom.

---

## What source coefficients are used?

The coefficients are defined in:

```text
ShenWork/PDE/IntervalCoupledSourceTimeC1.lean
```

Relevant context:

```lean
import ShenWork.PDE.IntervalCoupledRegularityBootstrap
import ShenWork.PDE.IntervalSourceCoefficientTimeC1
import ShenWork.PDE.IntervalSemigroupNeumann

open ShenWork.IntervalDomain
open ShenWork.IntervalDuhamelClosedC2
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalSemigroupNeumann
open ShenWork.IntervalSourceCoefficientTimeC1
open ShenWork.PDE.IntervalMildSourceDecayHelper

namespace ShenWork.IntervalCoupledRegularityBootstrap
```

Definitions:

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

/-- Lifted logistic source. -/
def coupledLogisticSourceLift (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (s : ℝ) : ℝ → ℝ :=
  intervalDomainLift
    (ShenWork.IntervalDomainExistence.intervalLogisticSource p (u s))

/-- Cosine coefficients of the logistic source. -/
def coupledLogisticSourceCoeffs (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) : ℝ → ℕ → ℝ :=
  fun s n => cosineCoeffs (coupledLogisticSourceLift p u s) n

/-- Lifted full chemotaxis-logistic source with the elliptic resolver substituted. -/
def coupledChemicalSourceLift (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (s : ℝ) : ℝ → ℝ :=
  intervalDomainLift
    (ShenWork.IntervalDomainExistence.intervalCoupledSource p (u s)
      (coupledChemicalConcentration p u s))

/-- Cosine coefficients of the coupled chemotaxis-logistic source. -/
def coupledChemicalSourceCoeffs (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) : ℝ → ℕ → ℝ :=
  fun s n => cosineCoeffs (coupledChemicalSourceLift p u s) n
```

So `CoupledDuhamelT6SliceAgreement` uses coefficients of the **full coupled source**, not merely coefficients of `u t`.

---

## Where `χ₀` enters

The full coupled source is split in `IntervalCoupledSourceTimeC1.lean` as:

```lean
/-- Coupled source `DuhamelSourceTimeC1` by scaling chem-div and adding logistic. -/
noncomputable def coupledChemicalSource_duhamelSourceTimeC1
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (hlog : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p u))
    (hchem : DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p u))
    (hsplit : coupledChemicalSourceCoeffs p u =
      fun s n => -(p.χ₀ * coupledChemDivSourceCoeffs p u s n)
        + coupledLogisticSourceCoeffs p u s n) :
    DuhamelSourceTimeC1 (coupledChemicalSourceCoeffs p u) := by
  have hchemScaled :
      DuhamelSourceTimeC1
        (fun s n => (-p.χ₀) * coupledChemDivSourceCoeffs p u s n) :=
    duhamelSourceTimeC1_const_mul hchem (-p.χ₀)
  have hsum :
      DuhamelSourceTimeC1
        (fun s n => -(p.χ₀ * coupledChemDivSourceCoeffs p u s n)
          + coupledLogisticSourceCoeffs p u s n) := by
    simpa using
      duhamelSourceTimeC1_add hchemScaled hlog
  rw [hsplit]
  exact hsum
```

And `intervalCoupledSource` unfolds in `IntervalCoupledBallEstimates.lean` as:

```lean
unfold intervalCoupledSource
calc
  |(-p.χ₀ * intervalDomainChemotaxisDiv p u v y) +
      intervalLogisticSource p u y|
      ≤ |(-p.χ₀ * intervalDomainChemotaxisDiv p u v y)| +
          |intervalLogisticSource p u y| := abs_add_le _ _
```

That is the smoking gun: the source used by `CoupledDuhamelT6SliceAgreement` is not χ-independent.  It contains the chemotaxis-divergence term scaled by `-p.χ₀`.

---

## What T6 does with this predicate

The immediate consumer is:

```lean
/-- The full closed-slice package supplied by T6 once the source is time-`C¹`
and the fixed point slice agrees with the corresponding Duhamel profile. -/
theorem coupledDuhamel_T6_closedSlicePack
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (hsrc : DuhamelSourceTimeC1 (coupledChemicalSourceCoeffs p u))
    (hagree : CoupledDuhamelT6SliceAgreement p T u) :
    ∀ t : ℝ, 0 < t → t < T →
      ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) ∧
      Filter.Tendsto (deriv (intervalDomainLift (u t)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (deriv (intervalDomainLift (u t)))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) ∧
      deriv (intervalDomainLift (u t)) 0 = 0 ∧
      deriv (intervalDomainLift (u t)) 1 = 0 := by
  intro t ht htT
  exact duhamelProfile_closedC2_neumann_of_timeC1_source
    hsrc ht (hagree t ht htT)
```

So the predicate is exactly the handoff that lets T6 transfer regularity from the Duhamel heat profile to the actual slice `u t`.

It is then used by:

```lean
theorem intervalDomainClassicalRegularity_of_T6_source_and_residual
    (hsrc : DuhamelSourceTimeC1 (coupledChemicalSourceCoeffs p u))
    (hagree : CoupledDuhamelT6SliceAgreement p T u)
    (R : CoupledDuhamelClassicalResidualAfterT6 p T u) :
    intervalDomainClassicalRegularity T u (coupledChemicalConcentration p u)
```

and finally by:

```lean
theorem regularityBootstrap_of_coupledDuhamel_bankedT6_source_and_residual
    (hsrc : DuhamelSourceTimeC1 (coupledChemicalSourceCoeffs p u))
    (hagree : CoupledDuhamelT6SliceAgreement p T u)
    (R : CoupledDuhamelResidualAfterBankedT6 p T u₀ u) :
    RegularityBootstrap p T u₀ u
```

So `CoupledDuhamelT6SliceAgreement` is a **regularity-transfer assumption** for the T6 atom, not just a passive Fourier inversion lemma.

---

## Is it “cosine series agreeing with the function on each slice”?

Only in a very indirect sense.

The predicate says `intervalDomainLift (u t)` agrees with a Duhamel profile built from `unitIntervalCosineHeatValue`.  Since `unitIntervalCosineHeatValue` is a cosine-heat series evaluator, the right side is spectral.  But the statement is not the generic slice inversion shape:

```lean
Set.EqOn (intervalDomainLift (u t))
  (fun x => ∑' n, b t n * cosineMode n x)
  (Set.Icc (0 : ℝ) 1)
```

Instead, it is:

```lean
Set.EqOn (intervalDomainLift (u t))
  (fun x => ∫ s in (0 : ℝ)..t,
    unitIntervalCosineHeatValue (t - s)
      (coupledChemicalSourceCoeffs p u s) x)
  (Set.Icc (0 : ℝ) 1)
```

So the agreement is with a **Duhamel reconstruction from the full source coefficients**, not with a standalone per-slice coefficient expansion of `u t`.

This matters because a Picard convergence argument that gives a per-slice cosine expansion of the limit would normally produce a statement involving coefficients of the slice, restart coefficients, or initial-data coefficients.  This definition instead requires exact equality with a source-only Duhamel profile involving `coupledChemicalSourceCoeffs p u s`.

---

## Does it depend on `χ₀`?

Yes, syntactically and semantically, through `p`.

The predicate itself has no separate `hχ` or sign assumption:

```lean
CoupledDuhamelT6SliceAgreement (p : CM2Params) (T : ℝ) (u : ...)
```

So it is not **regime-specific**.  It works uniformly for any parameter record `p`.

But the RHS uses:

```lean
coupledChemicalSourceCoeffs p u s
```

and those coefficients are coefficients of the full coupled source.  The code explicitly uses the split:

```lean
coupledChemicalSourceCoeffs p u
  = fun s n => -(p.χ₀ * coupledChemDivSourceCoeffs p u s n)
      + coupledLogisticSourceCoeffs p u s n
```

Therefore, changing only `p.χ₀` changes the coefficient family unless the chem-div coefficients vanish.  At `p.χ₀ = 0`, the source becomes logistic-only.  At `p.χ₀ ≠ 0`, it includes chemotaxis.

---

## Answer to the intended design question

`CoupledDuhamelT6SliceAgreement p D.T D.u` is **not** the χ-independent “cosine series agrees with the function on each slice” fact that should follow just from Picard convergence.

It is chemotaxis-aware because it asks for equality with the T6 Duhamel profile using `coupledChemicalSourceCoeffs`, and those coefficients encode

```lean
-logistic? no:
-(p.χ₀ * chemDivCoeffs) + logisticCoeffs
```

more explicitly:

```lean
fun s n => -(p.χ₀ * coupledChemDivSourceCoeffs p u s n)
  + coupledLogisticSourceCoeffs p u s n
```

So if the plan was to discharge `CoupledDuhamelT6SliceAgreement p D.T D.u` by “Picard convergence gives slice cosine agreement,” that is not enough as stated.  One would need to prove the stronger identity that the actual slice equals the **full coupled Duhamel heat profile** formed from the coupled source coefficients.  In particular, one must account for the chemotaxis source term and its `χ₀` scaling.

---

## Practical implication

The name `SliceAgreement` is slightly misleading if read too broadly.  It is not a generic inversion lemma.  It is the missing bridge between:

```text
fixed point equation / mild formula
```

and

```text
T6 source-coefficient Duhamel profile with coupledChemicalSourceCoeffs
```

For general `χ₀`, proving it is tied to the same chemotaxis source-identification problem as the rest of the general-χ banked-T6 path.  For `χ₀ = 0`, the chemotaxis part drops out and it reduces to the logistic-source Duhamel profile, but the definition itself is still parameterized by the full coupled source machinery.
