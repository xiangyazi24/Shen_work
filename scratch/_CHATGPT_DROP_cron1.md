# Q1082 / cron1 — revised route assessment after Q1076 setback

Repo inspected: `xiangyazi24/Shen_work`

Commit inspected: `4000f01e726fd00b7eb365893810377bb4ac245c`

Branch written: `chatgpt-scratch`

Target drop file:

```text
scratch/_CHATGPT_DROP_cron1.md
```

## Executive answer

**Shortest implementable route: Option B.**

The main reason is that the current physical-data route is still global in time. After `4000f01`, `FlooredSourceTimeData` became positive-time local for the derivative/slab fields, but the consumer chain still wants global coefficient regularity and global time-uniform envelopes. That leaves the old `t ↓ 0` blow-up problem in a new place.

The best route is therefore to bypass the global `PhysicalSourceTimeC2` / `PhysicalResolverJointC2Data` structures for Level0 and prove the exact positive-time local resolver facts directly:

```text
at target (s₀,x₀), s₀ > 0, x₀ ∈ (0,1):
  ContDiffAt ℝ 2 (resolver value series) (s₀,x₀)
  ContDiffAt ℝ 2 (resolver spatial-gradient series) (s₀,x₀)
```

using a smooth time cutoff and `contDiff_tsum`, exactly like `heatSemigroup_jointContDiffAt_two` does for the heat series. This avoids all global `∀ t > 0` uniform bounds and avoids proving actual global `ContDiff ℝ 2` across `t = 0`.

Very compact ranking:

```text
B   shortest / most local / fewest structure changes
A′  medium-large; becomes B plus rewiring of all physical-data consumers
C   not viable literally under current definitions; global PhysicalResolverJointC2Data has the same t=0/global-bound problem
```

## What I found in the requested files

### 1. `IntervalPhysicalSourceTimeC2Concrete.lean`: `physicalSourceTimeC2_of_floored`

The post-`4000f01` file has more than just the six `FlooredSourceTimeData` holes upstream. The consumer itself still has sorries.

Relevant skeleton:

```lean
import ShenWork.PDE.IntervalPhysicalSourceTimeC2Concrete

open Filter Topology Set
open ShenWork.PDE (intervalNeumannResolverWeight intervalNeumannResolverSourceCoeff)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)

noncomputable section

namespace ShenWork.IntervalPhysicalSourceTimeC2Concrete

/-- Positive-time coefficient C²-at theorem. -/
theorem srcTimeCoeff_contDiffAt
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s₁ s₂ : ℝ → ℝ → ℝ}
    (H : FlooredSourceTimeData p u s₁ s₂) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    ContDiffAt ℝ (2 : ℕ∞) (srcTimeCoeff p u k) t := by
  sorry

/-- Identification of second iterated derivative at positive time. -/
private theorem srcTimeCoeff_iteratedDeriv2
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s₁ s₂ : ℝ → ℝ → ℝ}
    (H : FlooredSourceTimeData p u s₁ s₂) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv 2 (srcTimeCoeff p u k) t = cosineCoeffs (s₂ t) k := by
  sorry

/-- The physical producer still wants global PhysicalSourceTimeC2. -/
theorem physicalSourceTimeC2_of_floored
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s₁ s₂ : ℝ → ℝ → ℝ}
    (H : FlooredSourceTimeData p u s₁ s₂)
    (hval : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointMajorant
        (fun i k => intervalNeumannResolverWeight p k * builtEs H i k) m))
    (hgrad : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointGradMajorant
        (fun i k => intervalNeumannResolverWeight p k * builtEs H i k) m)) :
    PhysicalSourceTimeC2 p u (builtEs H) where
  src_contDiff k := by
    -- positive-time data → global ContDiff on ℝ
    sorry
  src_bound i k t hi := by
    -- t > 0 from FlooredSourceTimeData; t ≤ 0 needs separate envelope
    sorry
  value_summable := hval
  grad_summable := hgrad

end ShenWork.IntervalPhysicalSourceTimeC2Concrete
```

Important interpretation:

* The two internal sorries `srcTimeCoeff_contDiffAt` and `srcTimeCoeff_iteratedDeriv2` are local positive-time proof assembly. They are finite work.
* The two sorries inside `physicalSourceTimeC2_of_floored` are the serious structural issue: the target `PhysicalSourceTimeC2` is still global. It asks for `ContDiff ℝ 2` and global coefficient bounds for all `t : ℝ`, not merely `t > 0` or `t ∈ [c,T]`.
* Even if A′ changes `zerothBound`/`laplBound` to window-local, this producer can no longer return the existing `PhysicalSourceTimeC2` without changing its type or adding an extension argument.

Also, in `IntervalHeatSemigroupHighRegularity.lean`, the call to `physicalSourceTimeC2_of_floored` still supplies two additional sorries for the value and gradient summability hypotheses:

```lean
import ShenWork.Paper2.IntervalHeatSemigroupHighRegularity

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)

noncomputable section

namespace ShenWork.Paper2.HeatResolverJointRegularity

-- Inside heatSemigroup_level0_resolverJointC2Data:
--
-- have hSTC2 : PhysicalSourceTimeC2 p u Es :=
--   physicalSourceTimeC2_of_floored hFSTD
--     (by intro m hm; sorry)  -- value_summable
--     (by intro m hm; sorry)  -- grad_summable

end ShenWork.Paper2.HeatResolverJointRegularity
```

So the current FSTD route has, after the six heat-file sorries, at least these further proof obligations:

```text
srcTimeCoeff_contDiffAt       local positive-time assembly
srcTimeCoeff_iteratedDeriv2   local positive-time derivative identification
physicalSourceTimeC2.src_contDiff   global ContDiff extension over ℝ
physicalSourceTimeC2.src_bound      global bound over all t
hval / hgrad summability in heatSemigroup_level0_resolverJointC2Data
```

### 2. `IntervalResolverJointC2PhysicalConcrete.lean`: what `PhysicalResolverJointC2Data` needs

The structure itself is simple and strong:

```lean
import ShenWork.PDE.IntervalResolverJointC2PhysicalConcrete

open Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)

noncomputable section

namespace ShenWork.IntervalResolverJointC2PhysicalConcrete

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

end ShenWork.IntervalResolverJointC2PhysicalConcrete
```

Beyond `PhysicalSourceTimeC2`, the conversion is complete. In `IntervalPhysicalResolverDataConcrete.lean`, `physicalResolverJointC2Data_of_floor` just transfers source coefficient regularity and bounds through the constant elliptic weight:

```lean
import ShenWork.PDE.IntervalPhysicalResolverDataConcrete

open Filter Topology Set
open ShenWork.PDE (intervalNeumannResolverWeight)
open ShenWork.IntervalResolverJointC2PhysicalConcrete (PhysicalResolverJointC2Data)
open ShenWork.IntervalDomain (intervalDomainPoint)

noncomputable section

namespace ShenWork.IntervalPhysicalResolverDataConcrete

theorem physicalResolverJointC2Data_of_floor
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Es : ℕ → ℕ → ℝ}
    (H : PhysicalSourceTimeC2 p u Es) :
    PhysicalResolverJointC2Data p u
      (fun i k => intervalNeumannResolverWeight p k * Es i k) where
  coeff_contDiff k := by
    have : resolverTimeCoeff p u k =
        fun t => intervalNeumannResolverWeight p k * srcTimeCoeff p u k t := by
      funext t; exact resolverTimeCoeff_eq_weight_smul p u k t
    rw [this]
    exact contDiff_const.mul (H.src_contDiff k)
  coeff_bound i k t hi :=
    resolverTimeCoeff_bound p u H.src_contDiff H.src_bound i k t hi
  value_summable := H.value_summable
  grad_summable := H.grad_summable

end ShenWork.IntervalPhysicalResolverDataConcrete
```

Conclusion: **there is no hidden work after `PhysicalSourceTimeC2`.** The bottleneck is that `PhysicalSourceTimeC2` and `PhysicalResolverJointC2Data` are global structures.

### 3. `IntervalHeatSemigroupHighRegularity.lean`: `heatResolverJointContDiffAt_two`

This theorem is **not independent**. It goes through the FlooredSourceTimeData route:

```lean
import ShenWork.Paper2.IntervalHeatSemigroupHighRegularity

open Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalCoupledRegularityBootstrap (coupledChemicalConcentration)
open ShenWork.IntervalResolverJointC2PhysicalConcrete
  (PhysicalResolverJointC2Data coupledChemical_jointContDiffAt_two resolverTimeCoeff)

noncomputable section

namespace ShenWork.Paper2.HeatResolverJointRegularity

theorem heatSemigroup_level0_resolverJointC2Data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀) :
    ∃ Bt : ℕ → ℕ → ℝ,
      PhysicalResolverJointC2Data p (conjugatePicardIter p u₀ 0) Bt := by
  set u := conjugatePicardIter p u₀ 0
  have hFSTD := ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatSemigroup_flooredSourceTimeData
    hu₀_bound hu₀_cont (p := p)
  set Es := ShenWork.IntervalPhysicalSourceTimeC2Concrete.builtEs hFSTD
  have hSTC2 : ShenWork.IntervalPhysicalResolverDataConcrete.PhysicalSourceTimeC2 p u Es :=
    ShenWork.IntervalPhysicalSourceTimeC2Concrete.physicalSourceTimeC2_of_floored hFSTD
      (by intro m hm; sorry)
      (by intro m hm; sorry)
  exact ⟨_, ShenWork.IntervalPhysicalResolverDataConcrete.physicalResolverJointC2Data_of_floor hSTC2⟩

theorem heatResolverJointContDiffAt_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    {c : ℝ} (_hc : 0 < c) {s₀ x₀ : ℝ} (_hs₀ : c < s₀)
    (hx₀ : x₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2 (fun q : ℝ × ℝ =>
      intervalDomainLift (coupledChemicalConcentration p
        (conjugatePicardIter p u₀ 0) q.1) q.2) (s₀, x₀) := by
  obtain ⟨Bt, hBt⟩ := heatSemigroup_level0_resolverJointC2Data
    (p := p) hu₀_bound hu₀_cont
  exact coupledChemical_jointContDiffAt_two hBt hx₀

end ShenWork.Paper2.HeatResolverJointRegularity
```

So it is only a wrapper over the current global physical-data route. It does **not** solve the Q1076 issue independently.

## Option A′ — weaken `zerothBound`/`laplBound` to `[c,T]`

### Verdict

**Not the shortest. Medium-large structural refactor.**

A′ fixes the two Q1076 blockers in the heat FSTD file, but it breaks the current consumer shape. The current `builtEs H` is global:

```lean
builtEs H i k : ℝ
```

It is chosen from global fields:

```lean
H.zerothBound i hi : ∃ D, 0 ≤ D ∧ ∀ t, 0 < t → ... ≤ D
H.laplBound i hi   : ∃ M, 0 ≤ M ∧ ∀ t, 0 < t → ... ≤ M/(kπ)^2
```

If these become window-local, `builtEs` must become window-local too:

```lean
builtEsOn H c T i k : ℝ
```

Then `srcTimeCoeff_bound`, `PhysicalSourceTimeC2`, and `PhysicalResolverJointC2Data` can no longer remain the existing global structures.

### Files likely touched

```text
ShenWork/PDE/IntervalPhysicalSourceTimeC2Concrete.lean
  - change FlooredSourceTimeData bound fields or add FlooredSourceTimeDataOn
  - replace builtEs with builtEsOn
  - replace physicalSourceTimeC2_of_floored or add physicalSourceTimeC2On_of_flooredOn

ShenWork/PDE/IntervalPhysicalResolverDataConcrete.lean
  - add PhysicalSourceTimeC2On → resolver data on a window, or abandon global conversion

ShenWork/PDE/IntervalResolverJointC2Physical.lean
  - add local/window version of boundedWeightJointSeries_contDiff_two, or use cutoff

ShenWork/PDE/IntervalResolverJointC2PhysicalConcrete.lean
  - add coupledChemical_jointContDiffAt_two_of_window/local data
  - same for gradient

ShenWork/Paper2/IntervalHeatSemigroupFlooredSourceTimeData.lean
  - fill positive-window source data

ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean
  - rewrite heatSemigroup_level0_resolverJointC2Data / heatResolverJointContDiffAt_two

ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean
  - import/use new local resolver theorem
```

### New lemmas needed

```text
1. Window-local zeroth and laplacian bounds for slice_i, i=0,1,2.
2. Window-local source coefficient derivative bound:
   ∀ t ∈ Icc c T, ‖∂ₜ^i srcTimeCoeff k t‖ ≤ builtEsOn c T i k.
3. Window-local summability of bounded-weight majorants.
4. A local `contDiffAt` resolver-series assembler, since current generic assembler wants global coefficient ContDiff and global Bt.
5. Local value and gradient resolver producers.
```

### Effort estimate

```text
Files:        6-7 existing files, possibly 1-2 new files
New lemmas:   ~12-18, including local variants of existing global structures
Risk:         high structural churn; easy to chase definitions across consumers
```

A′ is mathematically coherent, but once the data is window-local, the proof wants a local cutoff/tendsto series assembler anyway. That is essentially Option B with extra structure rewiring.

## Option B — bypass FSTD and prove direct resolver joint C² by cutoff + `contDiff_tsum`

### Verdict

**Shortest route.**

Do not build `PhysicalSourceTimeC2`. Do not build `PhysicalResolverJointC2Data`. Do not prove global bounds. Prove the local theorem Level0 actually needs:

```lean
import ShenWork.PDE.IntervalResolverJointC2Physical
import ShenWork.PDE.IntervalResolverJointC2PhysicalConcrete
import ShenWork.PDE.IntervalResolverSpectralJointC2Concrete
import ShenWork.PDE.IntervalResolverSpectralJointC2Cutoff
import ShenWork.PDE.IntervalResolverSpectralJointC2CutoffBounds
import ShenWork.Paper2.IntervalConjugatePicard
import ShenWork.Paper2.IntervalHeatSemigroupHighRegularity

open Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalCoupledRegularityBootstrap (coupledChemicalConcentration)
open ShenWork.IntervalResolverJointC2Physical
  (boundedWeightJointTerm boundedWeightJointGradTerm boundedWeightJointMajorant
   boundedWeightJointGradMajorant)
open ShenWork.IntervalResolverJointC2PhysicalConcrete
  (resolverTimeCoeff)
open ShenWork.IntervalResolverSpectralJointC2Cutoff
  (smoothRightCutoff)

noncomputable section

namespace ShenWork.Paper2.Level0DirectResolverJointC2

-- Target theorem 1: resolver value joint C², local in positive time.
theorem level0_resolver_value_jointContDiffAt_two_direct
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ c s₀ x₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hc : 0 < c) (hs₀ : c < s₀)
    (hx₀ : x₀ ∈ Ioo (0 : ℝ) 1)
    -- plus whatever floor/positive datum hypothesis is required
    :
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        intervalDomainLift (coupledChemicalConcentration p
          (conjugatePicardIter p u₀ 0) q.1) q.2)
      (s₀, x₀) := by
  sorry

-- Target theorem 2: resolver gradient joint C², local in positive time.
theorem level0_resolver_grad_jointContDiffAt_two_direct
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ c s₀ x₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hc : 0 < c) (hs₀ : c < s₀)
    (hx₀ : x₀ ∈ Ioo (0 : ℝ) 1)
    -- plus floor/positive datum
    :
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        deriv (intervalDomainLift (coupledChemicalConcentration p
          (conjugatePicardIter p u₀ 0) q.1)) q.2)
      (s₀, x₀) := by
  sorry

end ShenWork.Paper2.Level0DirectResolverJointC2
```

### Why this is shorter

The direct proof is exactly the local shape of the current heat proof:

```text
1. choose a positive time window around s₀;
2. multiply the resolver coefficient family by a smooth cutoff φ(t) that is 1 near s₀;
3. prove the cutoff resolver series is globally ContDiff ℝ 2 by contDiff_tsum;
4. transfer back to the real resolver near (s₀,x₀) by eventuallyEq;
5. transfer from the cosine series to intervalDomainLift(coupledChemicalConcentration ...) on x ∈ (0,1).
```

This avoids every global `t ↓ 0` problem because all estimates are made on the cutoff support, a compact positive-time interval.

### New lemmas needed

The core local lemmas are finite and do not require changing global structures:

```text
B1. Local positive-window heat floor / positivity input.
    If the existing Level0 caller has PositiveInitialDatum, thread it. Otherwise add an explicit floor hypothesis.

B2. Local source coefficient time derivatives for
      a_k(t) = cosineCoeffs (fun x => p.ν * (S(t)u₀ x)^p.γ) k
    on the cutoff support, orders 0,1,2.
    This can be done by differentiating the smooth heat representative under the integral.

B3. Local coefficient decay / majorants for a_k, a'_k, a''_k.
    This is where the now-available arbitrary-depth NeumannTower / depth-3 IBP is useful.
    The gradient resolver joint C² needs stronger decay than the value-only theorem.

B4. Cutoff coefficient family:
      c_k(t) = φ(t) * intervalNeumannResolverWeight p k * a_k(t)
    has global ContDiff ℝ 2 and global summable majorants because φ has compact support
    inside positive time.

B5. `contDiff_tsum` for the value series:
      ∑ c_k(t) cos(kπx)

B6. `contDiff_tsum` for the gradient series:
      ∑ c_k(t) deriv(cos(kπx))

B7. Eventual equality near s₀ because φ = 1.

B8. Series agreement with the actual resolver on `[0,1]` / interior.
```

The generic infrastructure already exists for most of the series assembly:

```text
IntervalResolverJointC2Physical.lean
  - boundedWeightJointTerm
  - boundedWeightJointMajorant
  - boundedWeightJointSeries_contDiff_two
  - boundedWeightJointGradTerm / grad majorant / grad assembler

IntervalResolverSpectralJointC2Cutoff.lean
  - smooth cutoff/restart cutoff machinery

IntervalHeatSemigroupHighRegularity.lean
  - heatSemigroup_jointContDiffAt_two pattern
```

The direct proof can either reuse the existing generic bounded-weight assembler with cutoff-patched coefficient families, or make a small local copy specialized to the Level0 resolver coefficients. Reuse is preferable.

### Files likely touched

```text
New file (preferred):
  ShenWork/Paper2/IntervalLevel0DirectResolverJointC2.lean

Possibly new helper file:
  ShenWork/Paper2/IntervalLevel0HeatSourceCoeffLocalBounds.lean

Small consumer change:
  ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean
    - import direct resolver theorem
    - use direct value/grad C² theorem in the 3C/3D proof body
    - use direct Clairaut inner commute or a direct analogue of coupledChemical_innerCommute_of_physicalJointC2
```

### Effort estimate

```text
Files:        1-2 new files + 1 consumer import/use
New lemmas:   ~8-12, mostly local/cutoff coefficient bounds and transfer lemmas
Risk:         medium; analytic proof work, but little structure churn
```

### Important small addition for 3F

If we bypass `PhysicalResolverJointC2Data`, then `coupledChemical_innerCommute_of_physicalJointC2` is not directly available. But its proof pattern is reusable. Add a direct local lemma:

```lean
import ShenWork.PDE.IntervalChemDivFACCommuteDischarge
import ShenWork.Paper2.IntervalLevel0DirectResolverJointC2

open Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemicalConcentration coupledChemicalTimeDerivativeLift)

noncomputable section

namespace ShenWork.Paper2.Level0DirectResolverJointC2

-- Direct analogue of coupledChemical_innerCommute_of_physicalJointC2.
theorem level0_coupledChemical_innerCommute_direct
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ c s y : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hc : 0 < c) (hs : c < s) (hy : y ∈ Ioo (0 : ℝ) 1)
    -- plus floor/positive datum
    :
    HasDerivAt
      (fun r => deriv (intervalDomainLift
        (coupledChemicalConcentration p (conjugatePicardIter p u₀ 0) r)) y)
      (deriv (coupledChemicalTimeDerivativeLift p
        (conjugatePicardIter p u₀ 0) s) y) s := by
  -- Same proof skeleton as coupledChemical_innerCommute_of_physicalJointC2,
  -- replacing `coupledChemical_jointContDiffAt_two H hy` with
  -- `level0_resolver_value_jointContDiffAt_two_direct ... hy`.
  sorry

end ShenWork.Paper2.Level0DirectResolverJointC2
```

That closes the 3F ingredient without ever manufacturing global `PhysicalResolverJointC2Data`.

## Option C — build `PhysicalResolverJointC2Data` directly for heat Level0

### Verdict

**Not viable literally under the current structure; not shortest even if localized.**

The literal structure is global:

```lean
coeff_contDiff : ∀ k, ContDiff ℝ (2 : ℕ∞) (resolverTimeCoeff p u k)
coeff_bound : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 → ... ≤ Bt i k
```

For `u = conjugatePicardIter p u₀ 0` with only `_hu₀_cont` and `_hu₀_bound`, positive-time heat smoothing does not imply global `ContDiff ℝ 2` through `t = 0`, and it does not imply global time-uniform derivative bounds. The same `t ↓ 0` issue that killed Q1076’s global `zerothBound/laplBound` reappears here.

If C is interpreted as “construct a local/positive-window variant of `PhysicalResolverJointC2Data` directly,” then it collapses into Option B plus extra structure definitions. If C is interpreted literally as the existing `PhysicalResolverJointC2Data`, it is blocked unless the initial data assumptions are strengthened significantly or the actual resolver coefficient functions are globally regularized, which would no longer be data about the real `resolverTimeCoeff`.

### Files likely touched if literal C is attempted

```text
ShenWork/PDE/IntervalResolverJointC2PhysicalConcrete.lean
  - impossible/global data target remains unchanged

ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean
  - replace heatSemigroup_level0_resolverJointC2Data body

Possibly many heat-source files
  - prove global C² source coefficient regularity through t=0
  - prove global Bt bounds all t
```

### Effort estimate

```text
Files:        unclear; at least 3, likely more
New lemmas:   would require global regularity/bounds that are false under current assumptions
Risk:         very high / blocked
```

### If C is localized

A localized C would define something like:

```lean
structure PhysicalResolverJointC2DataOn
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (c T : ℝ) (Bt : ℕ → ℕ → ℝ) : Prop where
  coeff_contDiffOn : ∀ k, ContDiffOn ℝ (2 : ℕ∞) (resolverTimeCoeff p u k) (Icc c T)
  coeff_boundOn : ∀ i k t, i ≤ 2 → t ∈ Icc c T →
    ‖iteratedFDeriv ℝ i (resolverTimeCoeff p u k) t‖ ≤ Bt i k
  value_summable : ∀ m, (m : ℕ∞) ≤ 2 → Summable (boundedWeightJointMajorant Bt m)
  grad_summable : ∀ m, (m : ℕ∞) ≤ 2 → Summable (boundedWeightJointGradMajorant Bt m)
```

But then the consumer still needs a local `contDiffAt` assembler with cutoff or local-to-global transfer. That is Option B with more wrapping.

## Side-by-side option table

| Option | Short verdict | Files to change | New lemmas | Main blocker / risk |
|---|---:|---:|---:|---|
| **A′** window-local `zerothBound/laplBound` | Coherent but not shortest | 6-7 files | ~12-18 | Existing `PhysicalSourceTimeC2` and `PhysicalResolverJointC2Data` are global; must introduce local versions or a cutoff assembler anyway. |
| **B** direct resolver `ContDiffAt` by cutoff + `contDiff_tsum` | **Shortest** | 1-2 new files + 1 consumer | ~8-12 | Need local source coefficient derivative/decay bounds and floor; no global structure churn. |
| **C** direct global `PhysicalResolverJointC2Data` | Not viable literally | 3+ files | false/global facts | Existing structure requires global `ContDiff ℝ 2` and global bounds through `t = 0`; same blow-up problem. |

## Recommended implementation plan

Do **Option B** in a new file and keep it laser-focused on the Level0 consumer.

Suggested file:

```text
ShenWork/Paper2/IntervalLevel0DirectResolverJointC2.lean
```

Suggested theorem list:

```lean
import ShenWork.PDE.IntervalResolverJointC2Physical
import ShenWork.PDE.IntervalResolverJointC2PhysicalConcrete
import ShenWork.PDE.IntervalResolverSpectralJointC2Concrete
import ShenWork.PDE.IntervalResolverSpectralJointC2Cutoff
import ShenWork.PDE.IntervalResolverSpectralJointC2CutoffBounds
import ShenWork.PDE.IntervalChemDivFACCommuteDischarge
import ShenWork.Paper2.IntervalConjugatePicard
import ShenWork.Paper2.IntervalHeatSemigroupHighRegularity

open Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemicalConcentration coupledChemicalTimeDerivativeLift)
open ShenWork.IntervalResolverJointC2Physical
  (boundedWeightJointTerm boundedWeightJointGradTerm boundedWeightJointMajorant
   boundedWeightJointGradMajorant)
open ShenWork.IntervalResolverJointC2PhysicalConcrete
  (resolverTimeCoeff)

noncomputable section

namespace ShenWork.Paper2.Level0DirectResolverJointC2

-- 1. Local cutoff source coefficient family for heat Level0.
def level0ResolverCoeffCutoff
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (s₀ : ℝ) : ℕ → ℝ → ℝ :=
  fun k t =>
    -- φ(t) * resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k t
    sorry

-- 2. Global C² of cutoff coefficient family.
theorem level0ResolverCoeffCutoff_contDiff_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ c s₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hc : 0 < c) (hs₀ : c < s₀) :
    ∀ k, ContDiff ℝ (2 : ℕ∞) (level0ResolverCoeffCutoff p u₀ s₀ k) := by
  sorry

-- 3. Summable value and gradient majorants for the cutoff coefficient family.
theorem level0ResolverCoeffCutoff_value_summable
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ c s₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hc : 0 < c) (hs₀ : c < s₀) :
    ∃ Bt : ℕ → ℕ → ℝ,
      (∀ i k t, i ≤ 2 →
        ‖iteratedFDeriv ℝ i (level0ResolverCoeffCutoff p u₀ s₀ k) t‖ ≤ Bt i k) ∧
      (∀ m, (m : ℕ∞) ≤ 2 → Summable (boundedWeightJointMajorant Bt m)) ∧
      (∀ m, (m : ℕ∞) ≤ 2 → Summable (boundedWeightJointGradMajorant Bt m)) := by
  sorry

-- 4. Value resolver joint C² by contDiff_tsum + eventual equality.
theorem level0_resolver_value_jointContDiffAt_two_direct
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ c s₀ x₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hc : 0 < c) (hs₀ : c < s₀) (hx₀ : x₀ ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        intervalDomainLift (coupledChemicalConcentration p
          (conjugatePicardIter p u₀ 0) q.1) q.2)
      (s₀, x₀) := by
  sorry

-- 5. Gradient resolver joint C² by the gradient bounded-weight assembler.
theorem level0_resolver_grad_jointContDiffAt_two_direct
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ c s₀ x₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hc : 0 < c) (hs₀ : c < s₀) (hx₀ : x₀ ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        deriv (intervalDomainLift (coupledChemicalConcentration p
          (conjugatePicardIter p u₀ 0) q.1)) q.2)
      (s₀, x₀) := by
  sorry

-- 6. Direct inner commute for 3F, copied from the physical proof pattern.
theorem level0_coupledChemical_innerCommute_direct
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ c s y : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hc : 0 < c) (hs : c < s) (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun r => deriv (intervalDomainLift
        (coupledChemicalConcentration p (conjugatePicardIter p u₀ 0) r)) y)
      (deriv (coupledChemicalTimeDerivativeLift p
        (conjugatePicardIter p u₀ 0) s) y) s := by
  sorry

end ShenWork.Paper2.Level0DirectResolverJointC2
```

This gives Level0 the local resolver facts it needs for 3C/3D/3F, without pretending that global positive-time coefficient bounds are available.

## Bottom line

A′ is a valid redesign if the goal is to preserve a structured physical-source data pipeline, but it is not the shortest. It requires localizing multiple global structures and consumers.

C is blocked if interpreted literally because `PhysicalResolverJointC2Data` is global in time and therefore inherits the same near-zero problem.

B is the shortest practical implementation: prove the resolver value/gradient `ContDiffAt` directly at positive target times using the already-existing cutoff/`contDiff_tsum` pattern, and add a direct local inner-commute lemma for 3F.
