# Q1037 / cron2 — concrete route for 1A uniform `secondDeriv` bound

Repo inspected: `xiangyazi24/Shen_work`

Branch written: `chatgpt-scratch`

Target drop file:

```text
scratch/_CHATGPT_DROP_cron1.md
```

## Answer

Use route **(a)**, with one important refinement:

> Build a canonical closed-slab cosine representative for the chemDiv expression, prove joint continuity of its classical second spatial derivative on `[c,T] × [0,1]`, and tie the `hH2_per_slice.secondDeriv` field definitionally or by a small equality lemma to that canonical derivative.

Do **not** try route (b) as the primary path. `ContDiffAt` on the open interior is not enough for the compact bound on `[c,T] × [0,1]`, and it does not control the endpoint behavior of the `IntervalWeakH2Neumann.secondDeriv`. The existing code already warns that boundary behavior of `coupledChemDivSourceLift` is delicate because of `intervalDomainLift`; the safe object is the smooth cosine representative, not the raw lifted interval source.

## What the current code does

In `IntervalChemDivSpatialC2.lean`, the key constructor is:

```lean
ShenWork.Paper2.ChemDivSpatialC2.chemDivSource_weakH2_of_cosineRep
```

It takes global cosine representatives `U_cos` and `V_cos`, proves C2 for

```lean
F := deriv (chemFluxFun p.β U_cos V_cos)
```

then builds:

```lean
hF_H2 : IntervalWeakH2Neumann F :=
  ShenWork.PDE.IntervalMildSourceDecayHelper.intervalWeakH2Neumann_of_contDiffOn
    hF_C2on htend0 htend1 hbc0 hbc1
```

The structure `IntervalWeakH2Neumann` stores:

```lean
secondDeriv : ℝ → ℝ
second_intervalIntegrable : IntervalIntegrable secondDeriv volume 0 1
second_abs_integral_bound : ∃ B ≥ 0, ∫₀¹ |secondDeriv| ≤ B
weak_cosine_laplacian : ...
```

and `intervalWeakH2Neumann_of_contDiffOn` sets:

```lean
secondDeriv := deriv (deriv g)
```

Thus, for the H2 object produced from the cosine representative, the stored second derivative is the classical `deriv (deriv F)`, i.e. the second derivative of chemDiv / the third derivative of the flux representative.

In `IntervalConjugateLevel0BFormSourceOn.lean`, the current `hH2_per_slice` block already calls `chemDivSource_weakH2_of_cosineRep`, then 1A is exactly:

```lean
have hunif_ptwise : ∃ C, 0 ≤ C ∧ ∀ s (hs : s ∈ Icc c T),
    ∀ x ∈ Icc (0 : ℝ) 1, |(hH2_per_slice s hs).secondDeriv x| ≤ C := by
  sorry -- [SUB-SORRY 1A: joint continuity + compactness → ptwise bound]
```

So the missing thing is not another per-slice H2 proof. It is the closed-slab joint continuity and the equality between the H2 field and the canonical representative derivative.

## Concrete route

### Step 1: Stop hiding the representatives behind per-slice `choose`

Define canonical representatives for Level0:

```lean
import ShenWork.Paper2.IntervalChemDivSpatialC2
import ShenWork.Paper2.IntervalConjugateLevel0BFormSourceOn
import ShenWork.Paper2.IntervalHeatSemigroupHighRegularity
import ShenWork.Paper2.IntervalResolverHighRegularity

open Set Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalCoupledRegularityBootstrap (coupledChemicalConcentration)
open ShenWork.Paper2.ChemDivSpatialC2
  (chemFluxFun chemDivSource_weakH2_of_cosineRep)
open ShenWork.Paper2.IntervalResolverHighRegularity
  (intervalResolverLiftR intervalResolverLiftR_contDiff_four
   intervalResolverLiftR_even intervalResolverLiftR_reflect_one)
open ShenWork.PDE.IntervalMildSourceDecayHelper (IntervalWeakH2Neumann)
open ShenWork.CosineSpectrum (cosineMode)

noncomputable section

namespace ShenWork.Paper2.Level0ChemDivSecondDerivRoute

/-- Canonical heat cosine representative for `conjugatePicardIter p u₀ 0`. -/
def level0Ucos (u₀ : intervalDomainPoint → ℝ) (s x : ℝ) : ℝ :=
  ∑' k : ℕ,
    (Real.exp (-s * unitIntervalCosineEigenvalue k) *
      cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k x

/-- Canonical resolver cosine representative for the Level0 heat iterate. -/
def level0Vcos (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (s x : ℝ) : ℝ :=
  intervalResolverLiftR p (conjugatePicardIter p u₀ 0 s) x

/-- Canonical chemDiv representative on the slab. -/
def level0ChemDivRep (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (s x : ℝ) : ℝ :=
  deriv (chemFluxFun p.β (level0Ucos u₀ s) (level0Vcos p u₀ s)) x

/-- Canonical second derivative stored in the H2 certificate. -/
def level0ChemDivSecondRep (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (s x : ℝ) : ℝ :=
  deriv (deriv (level0ChemDivRep p u₀ s)) x

end ShenWork.Paper2.Level0ChemDivSecondDerivRoute
```

This avoids proof-dependent `Classical.choose` representatives when proving the uniform bound. You can still use the same per-slice data to build `IntervalWeakH2Neumann`; just make the reps explicit.

### Step 2: Prove closed-slab joint continuity of `level0ChemDivSecondRep`

This is the actual 1A theorem:

```lean
namespace ShenWork.Paper2.Level0ChemDivSecondDerivRoute

/-- Main analytic input for 1A: the classical second derivative of the smooth
cosine representative is jointly continuous on the closed positive-time slab. -/
theorem level0ChemDivSecondRep_continuousOn_Icc
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ c T : ℝ}
    (hc : 0 < c) (hcT : c ≤ T)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hVpos : ∀ s ∈ Icc c T, ∀ x : ℝ,
      0 < 1 + level0Vcos p u₀ s x) :
    ContinuousOn
      (fun q : ℝ × ℝ => level0ChemDivSecondRep p u₀ q.1 q.2)
      (Icc c T ×ˢ Icc (0 : ℝ) 1) := by
  -- Route:
  -- 1. U side: generalize/use the cutoff cosine-series theorem.
  --    Existing nearby theorem:
  --      HeatSemigroupJointRegularity.heatSemigroup_jointContDiffAt_two
  --    For this 1A target, use the same cutoff-tsum proof at order 4, not order 2:
  --      desired: level0Ucos_contDiffOn_four_Icc.
  --
  -- 2. V side: use the resolver cosine representative, not intervalDomainLift.
  --    Per-slice C4 theorem already exists:
  --      IntervalResolverHighRegularity.intervalResolverLiftR_contDiff_four
  --    The closed-slab joint version should be proved by the same spectral/cutoff
  --    route as the heat theorem, using the positive-time heat source tails.
  --      desired: level0Vcos_contDiffOn_four_Icc.
  --
  -- 3. Mixed algebra:
  --    From joint C4 of U and V and hVpos, prove the flux
  --      (s,x) ↦ U(s,x) * ∂x V(s,x) / (1+V(s,x))^β
  --    is joint C3, hence its x-derivative is joint C2 and its x-second derivative
  --    is continuous. This is the joint analogue of existing one-slice theorems:
  --      ChemDivSpatialC2.chemFlux_contDiff_three
  --      ChemDivSpatialC2.chemFluxDeriv_contDiff_two
  --
  -- Suggested new theorem name:
  --      chemDivSecondRep_continuousOn_of_jointC4
  --
  -- The proof should use ContDiffOn.mul, ContDiffOn.div, rpow_const_of_ne,
  -- and continuity of spatial derivatives obtained from ContDiffOn of the
  -- uncurried representative.
  sorry

end ShenWork.Paper2.Level0ChemDivSecondDerivRoute
```

The existing theorem `HeatSemigroupJointRegularity.heatSemigroup_jointContDiffAt_two` is only order 2, so it is not the final tool for 1A. It is the template: copy its cutoff-tsum route and raise the order to 4. Per-slice `heatSemigroup_contDiff_four` and `intervalResolverLiftR_contDiff_four` confirm the required spatial order is mathematically available.

### Step 3: Tie `hH2_per_slice.secondDeriv` to the canonical representative

Do not attempt to prove continuity of

```lean
fun q => (hH2_per_slice q.1 ?).secondDeriv q.2
```

directly. It is proof dependent because `hs : s ∈ Icc c T` is an argument and the current construction locally builds representatives.

Instead prove a bridge lemma for the explicit H2 constructor:

```lean
namespace ShenWork.Paper2.Level0ChemDivSecondDerivRoute

/-- If the Level0 H2 certificate is built from the canonical cosine reps, its
stored `secondDeriv` is the canonical classical second derivative. -/
theorem level0_hH2_secondDeriv_eq
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {s : ℝ}
    (H : IntervalWeakH2Neumann
      (ShenWork.IntervalBFormSpectral.chemDivLift p
        (conjugatePicardIter p u₀ 0 s)
        (coupledChemicalConcentration p (conjugatePicardIter p u₀ 0) s)))
    -- In the real patch, replace this abstract `H` by the actual expression
    -- returned by `chemDivSource_weakH2_of_cosineRep` with
    -- `U_cos = level0Ucos u₀ s` and `V_cos = level0Vcos p u₀ s`.
    : H.secondDeriv = H.secondDeriv := by
  -- With the real H2 expression, this is essentially:
  --   unfold chemDivSource_weakH2_of_cosineRep
  --   unfold IntervalMildSourceDecayHelper.intervalWeakH2Neumann_of_contDiffOn
  --   rfl
  -- because `intervalWeakH2Neumann_of_contDiffOn` sets
  --   secondDeriv := deriv (deriv g)
  -- and `chemDivSource_weakH2_of_cosineRep` uses `g = F = deriv flux`.
  rfl

end ShenWork.Paper2.Level0ChemDivSecondDerivRoute
```

In the actual patch, make the theorem state the concrete expression, not the trivial abstract form above. The important point is that the equality should be by unfolding the two constructors, not by analysis.

### Step 4: Compactness gives the 1A bound

Once you have `ContinuousOn` for the canonical `level0ChemDivSecondRep`, the bound is a standard compactness lemma already used elsewhere in the repo:

```lean
(isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hcont
```

Concrete target:

```lean
namespace ShenWork.Paper2.Level0ChemDivSecondDerivRoute

/-- 1A target: uniform pointwise bound for the second derivative stored in the
per-slice H2 data. -/
theorem level0_hH2_secondDeriv_uniform_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ c T : ℝ}
    (hc : 0 < c) (hcT : c ≤ T)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hVpos : ∀ s ∈ Icc c T, ∀ x : ℝ,
      0 < 1 + level0Vcos p u₀ s x)
    (hH2_per_slice : ∀ s, s ∈ Icc c T →
      IntervalWeakH2Neumann
        (ShenWork.IntervalBFormSpectral.chemDivLift p
          (conjugatePicardIter p u₀ 0 s)
          (coupledChemicalConcentration p (conjugatePicardIter p u₀ 0) s)))
    (hH2_second_eq : ∀ s (hs : s ∈ Icc c T),
      (hH2_per_slice s hs).secondDeriv = level0ChemDivSecondRep p u₀ s) :
    ∃ C, 0 ≤ C ∧ ∀ s (hs : s ∈ Icc c T),
      ∀ x ∈ Icc (0 : ℝ) 1, |(hH2_per_slice s hs).secondDeriv x| ≤ C := by
  have hcont := level0ChemDivSecondRep_continuousOn_Icc
    (p := p) (u₀ := u₀) (M₀ := M₀) hc hcT hu₀_bound hu₀_cont hVpos
  have hcont_abs : ContinuousOn
      (fun q : ℝ × ℝ => |level0ChemDivSecondRep p u₀ q.1 q.2|)
      (Icc c T ×ˢ Icc (0 : ℝ) 1) := hcont.abs
  obtain ⟨C, hCbound⟩ :=
    (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hcont_abs
  refine ⟨max C 0, le_max_right C 0, ?_⟩
  intro s hs x hx
  have hb := hCbound (s, x) ⟨hs, hx⟩
  rw [hH2_second_eq s hs]
  -- `hb` is a norm bound on the abs-valued function; simplify to a scalar abs bound.
  have : |level0ChemDivSecondRep p u₀ s x| ≤ C := by
    simpa [Real.norm_eq_abs, abs_abs] using hb
  exact this.trans (le_max_left C 0)

end ShenWork.Paper2.Level0ChemDivSecondDerivRoute
```

After this theorem, the existing 1B block in `IntervalConjugateLevel0BFormSourceOn.lean` already converts the pointwise bound to the uniform L1 bound:

```lean
∫ x in (0 : ℝ)..1, |(hH2_per_slice s hs).secondDeriv x| ≤ C
```

using `intervalIntegral.integral_mono_on` and `(hH2_per_slice s hs).second_intervalIntegrable.norm`.

## Why not route (b)?

Route (b) would try to use interior `ContDiffAt` for the raw flux or raw chemDiv source. That is the wrong object for 1A because:

1. the desired compact set is closed, `[c,T] × [0,1]`;
2. `coupledChemDivSourceLift` can have boundary artifacts from `intervalDomainLift`;
3. `IntervalWeakH2Neumann.secondDeriv` is attached to the smooth representative used in the weak-H2 proof, not automatically to the raw interior `ContDiffAt` object;
4. compactness on `Ioo 0 1` is unavailable.

So the closed-slab representative route is the robust path.

## Minimal theorem-name checklist

Use existing:

```text
ChemDivSpatialC2.chemDivSource_weakH2_of_cosineRep
ChemDivSpatialC2.chemFlux_contDiff_three
ChemDivSpatialC2.chemFluxDeriv_contDiff_two
PDE.IntervalMildSourceDecayHelper.intervalWeakH2Neumann_of_contDiffOn
HeatSemigroupHighRegularity.heatSemigroup_contDiff_four
HeatSemigroupJointRegularity.heatSemigroup_jointContDiffAt_two   -- template, order 2 only
IntervalResolverHighRegularity.intervalResolverLiftR_contDiff_four
IntervalResolverHighRegularity.intervalResolverLiftR_even
IntervalResolverHighRegularity.intervalResolverLiftR_reflect_one
(isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
```

Add or generalize:

```text
level0Ucos_contDiffOn_four_Icc
level0Vcos_contDiffOn_four_Icc
chemDivSecondRep_continuousOn_of_jointC4
level0_hH2_secondDeriv_eq
level0_hH2_secondDeriv_uniform_bound
```

## Bottom line

The simplest route is **(a)**: prove joint continuity of the classical second derivative of the smooth cosine-series chemDiv representative on the closed slab, then use compactness. The only extra engineering is to make the per-slice H2 construction use explicit canonical reps, or prove a small unfolding lemma showing its `secondDeriv` field is the canonical `deriv (deriv (deriv flux))`. Route (b) is not recommended because it loses endpoint control and does not naturally identify the `IntervalWeakH2Neumann.secondDeriv` field.
