# Q1046 + Q1042 (cron2) — resolver-C² shortcut and uniform `secondDeriv` bound bridge

Static repo inspection only; I did **not** run Lean.

I treated the pasted message as two tasks and answered both here:

1. **Q1046** — whether `srcC2 : DuhamelSourceTimeC2Coeff a` can be bypassed in `IntervalResolverLevel0SpectralC2Coeff.lean`.
2. **Q1042** — how to prove the uniform bound on the H² `secondDeriv` once a joint-in-time continuous closed representative exists.

Files read / searched:

- `ShenWork/PDE/IntervalResolverSpectralJointC2Concrete.lean`, around `resolverSpectralJointC2At_of_restartSmoothCutoff`.
- `ShenWork/PDE/IntervalResolverSpectralJointC2Cutoff.lean`, especially `resolverSpectralJointC2At_of_smooth_cutoff_contDiff_tsum`.
- `ShenWork/Paper2/IntervalResolverLevel0SpectralC2Coeff.lean`.
- `ShenWork/PDE/IntervalPhysicalResolverDataConcrete.lean` and `IntervalPhysicalSourceTimeC2Concrete.lean`.
- `ShenWork/Paper2/IntervalChemDivSpatialC2.lean`.
- Searches for `tsum_cos_jointContinuousOn`, `cosineCoeffSeries_continuousOn`, `continuousOn_tsum`, `duhamelSeries_jointContinuousOn`.
- `ShenWork/PDE/IntervalSourceCoefficientTimeC1.lean`.
- `ShenWork/Wiener/EWA/SourceJointRegularity.lean`.
- `ShenWork/Paper2/IntervalParabolicDuhamelGainNonCircular.lean`.

---

# Q1046 — Is there a shortcut avoiding `DuhamelSourceTimeC2Coeff`?

## Executive verdict

Yes, but with an important qualification.

There is a genuine shortcut **if you are willing to bypass the current `ResolverHasSpectralAgreementC2Coeff` path**.  The current theorem

```lean
resolverHasSpectralAgreementC2Coeff_heatLevel0
```

has, by definition, a field requiring:

```lean
srcC2 : DuhamelSourceTimeC2Coeff a
```

So if the goal is literally to fill the existing `srcC2` hole inside that theorem, then no: the structure demands the full package.

But if the real goal is the consumer output — resolver joint `C²` of the concrete heat-Level0 resolver — then yes: one can bypass `DuhamelSourceTimeC2Coeff` entirely and prove the two `ContDiffAt` conclusions directly by a cutoff + `contDiff_tsum` argument for the concrete resolver coefficient series.

This is not just a speculative idea.  The repo already has the generic theorem that shows exactly what data is needed:

```lean
ShenWork.IntervalResolverSpectralJointC2Cutoff
  .resolverSpectralJointC2At_of_smooth_cutoff_contDiff_tsum
```

and the concrete restart theorem simply feeds it with data derived from `DuhamelSourceTimeC2Coeff`:

```lean
ShenWork.IntervalResolverSpectralJointC2Concrete
  .resolverSpectralJointC2At_of_restartSmoothCutoff
```

So the shortcut is: **feed the generic cutoff/tsum theorem directly with heat-Level0 resolver terms and heat-specific majorants**, rather than first forcing the data through the restart-source `DuhamelSourceTimeC2Coeff` interface.

## What the consumer actually uses

The concrete restart theorem is:

```lean
theorem resolverSpectralJointC2At_of_restartSmoothCutoff
    {a₀ : ℕ → ℝ} {M : ℝ} {a : ℝ → ℕ → ℝ} {offset s x : ℝ}
    (hτ : 0 < s - offset) (ha₀ : ∀ n, |a₀ n| ≤ M)
    (src : DuhamelSourceTimeC2Coeff a) :
    ResolverSpectralJointC2At a₀ a offset s x :=
  resolverSpectralJointC2At_of_smooth_cutoff_contDiff_tsum
    (φ := restartSmoothCutoff offset s)
    (gradTerm := resolverSpectralConcreteGradTerm a₀ a offset)
    (vValue := concreteRestartValueMajorant a₀ src offset s hτ)
    (vGrad := concreteRestartGradMajorant a₀ src offset s hτ)
    (restartSmoothCutoff_eventually_eq_one hτ)
    (cutoffValueTerm_restartSmoothCutoff_contDiff src)
    (concreteRestartValueMajorant_summable hτ ha₀ src)
    (cutoffValueTerm_restartSmoothCutoff_iteratedFDeriv_bound hτ src)
    (cutoffGradTerm_restartSmoothCutoff_contDiff src)
    (concreteRestartGradMajorant_summable hτ ha₀ src)
    (cutoffGradTerm_restartSmoothCutoff_iteratedFDeriv_bound hτ src)
    (resolverSpectralGradSeries_eventuallyEq_concreteGradTerm hτ ha₀ src)
```

The underlying generic theorem is:

```lean
theorem resolverSpectralJointC2At_of_smooth_cutoff_contDiff_tsum
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ} {offset s x : ℝ}
    (φ : ℝ → ℝ) (gradTerm : ℕ → ℝ × ℝ → ℝ)
    (vValue vGrad : ℕ → ℕ → ℝ)
    (hφ_one : φ =ᶠ[𝓝 s] fun _ : ℝ => 1)
    (hValueTerm : ∀ n : ℕ,
      ContDiff ℝ (2 : ℕ∞) (cutoffValueTerm φ a₀ a offset n))
    (hValueSumm : ∀ k : ℕ, (k : ℕ∞) ≤ (2 : ℕ∞) → Summable (vValue k))
    (hValueBound : ∀ (k n : ℕ) (q : ℝ × ℝ), (k : ℕ∞) ≤ (2 : ℕ∞) →
      ‖iteratedFDeriv ℝ k (cutoffValueTerm φ a₀ a offset n) q‖ ≤ vValue k n)
    (hGradTerm : ∀ n : ℕ, ContDiff ℝ (2 : ℕ∞) (cutoffGradTerm φ gradTerm n))
    (hGradSumm : ∀ k : ℕ, (k : ℕ∞) ≤ (2 : ℕ∞) → Summable (vGrad k))
    (hGradBound : ∀ (k n : ℕ) (q : ℝ × ℝ), (k : ℕ∞) ≤ (2 : ℕ∞) →
      ‖iteratedFDeriv ℝ k (cutoffGradTerm φ gradTerm n) q‖ ≤ vGrad k n)
    (hGradEq :
      resolverSpectralGradSeries a₀ a offset =ᶠ[𝓝 (s, x)]
        fun q : ℝ × ℝ => ∑' n : ℕ, gradTerm n q) :
    ResolverSpectralJointC2At a₀ a offset s x
```

So the real consumer data are exactly the seven items in the prompt:

1. value term `ContDiff ℝ 2`,
2. value majorant summability,
3. value derivative bounds,
4. gradient term `ContDiff ℝ 2`,
5. gradient majorant summability,
6. gradient derivative bounds,
7. eventual equality of the gradient series.

`DuhamelSourceTimeC2Coeff` is one **sufficient package** for producing those seven items, not logically the only possible route.

## Why the current generic theorem cannot be reused literally for direct heat coefficients

One subtlety: `resolverSpectralJointC2At_of_smooth_cutoff_contDiff_tsum` is still expressed in the restart coefficient language:

```lean
cutoffValueTerm φ a₀ a offset n
```

where the coefficient is:

```lean
localRestartCoeff a₀ a (q.1 - offset) n
```

If we use the direct heat-Level0 elliptic coefficient

```lean
ck t := intervalNeumannResolverWeight p k *
  srcTimeCoeff p (conjugatePicardIter p u₀ 0) k t
```

then this is not definitionally a `localRestartCoeff`.  We have two options:

1. **VOC route:** still prove a local variation-of-constants identity identifying `localRestartCoeff a₀ a` with `ck`; this is exactly the current `IntervalResolverLevel0SpectralC2Coeff.lean` design and leads back to needing a strong package for `a`.
2. **Direct-series route:** clone the generic cutoff theorem with an arbitrary coefficient family `ck : ℕ → ℝ → ℝ`, and conclude the actual `ContDiffAt` statements for the direct resolver series rather than `ResolverSpectralJointC2At a₀ a offset s x`.

The true shortcut is option 2.

## Suggested direct theorem shape

The direct target should bypass `ResolverHasSpectralAgreementC2Coeff` and produce the final local regularity directly:

```lean
import ShenWork.PDE.IntervalResolverSpectralJointC2Cutoff
import ShenWork.PDE.IntervalPhysicalResolverDataConcrete
import ShenWork.Paper2.IntervalConjugatePicard

open Set Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalPhysicalResolverDataConcrete (srcTimeCoeff)

noncomputable section

namespace ShenWork.Paper2.Level0ResolverDirectC2

abbrev heatLevel0 (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) :
    ℝ → intervalDomainPoint → ℝ :=
  ShenWork.IntervalConjugatePicard.conjugatePicardIter p u₀ 0

/-- Direct elliptic resolver coefficient for heat Level0. -/
def level0ResolverCoeff (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (k : ℕ) (t : ℝ) : ℝ :=
  ShenWork.PDE.intervalNeumannResolverWeight p k *
    srcTimeCoeff p (heatLevel0 p u₀) k t

/-- Direct value summand with a time cutoff. -/
def cutoffLevel0ResolverValueTerm
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (φ : ℝ → ℝ) (k : ℕ) : ℝ × ℝ → ℝ :=
  fun q => φ q.1 * level0ResolverCoeff p u₀ k q.1 * cosineMode k q.2

/-- Direct gradient summand with a time cutoff. -/
def cutoffLevel0ResolverGradTerm
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (φ : ℝ → ℝ) (k : ℕ) : ℝ × ℝ → ℝ :=
  fun q => φ q.1 * level0ResolverCoeff p u₀ k q.1 *
    (-(k : ℝ) * Real.pi * Real.sin ((k : ℝ) * Real.pi * q.2))

/-- A direct majorant package for the heat-Level0 resolver series.

This is the exact data consumed by `contDiff_tsum`; it replaces the large
`DuhamelSourceTimeC2Coeff` restart package. -/
structure Level0ResolverDirectC2Majorants
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (s : ℝ) : Prop where
  φ : ℝ → ℝ
  hφ_one : φ =ᶠ[𝓝 s] fun _ : ℝ => 1
  vValue : ℕ → ℕ → ℝ
  vGrad : ℕ → ℕ → ℝ
  valueTerm_c2 : ∀ k,
    ContDiff ℝ (2 : ℕ∞) (cutoffLevel0ResolverValueTerm p u₀ φ k)
  valueSumm : ∀ j : ℕ, (j : ℕ∞) ≤ (2 : ℕ∞) → Summable (vValue j)
  valueBound : ∀ (j k : ℕ) (q : ℝ × ℝ), (j : ℕ∞) ≤ (2 : ℕ∞) →
    ‖iteratedFDeriv ℝ j (cutoffLevel0ResolverValueTerm p u₀ φ k) q‖ ≤ vValue j k
  gradTerm_c2 : ∀ k,
    ContDiff ℝ (2 : ℕ∞) (cutoffLevel0ResolverGradTerm p u₀ φ k)
  gradSumm : ∀ j : ℕ, (j : ℕ∞) ≤ (2 : ℕ∞) → Summable (vGrad j)
  gradBound : ∀ (j k : ℕ) (q : ℝ × ℝ), (j : ℕ∞) ≤ (2 : ℕ∞) →
    ‖iteratedFDeriv ℝ j (cutoffLevel0ResolverGradTerm p u₀ φ k) q‖ ≤ vGrad j k

/-- Direct heat-Level0 resolver joint `C²` from direct coefficient majorants.
This is the shortcut theorem: no `DuhamelSourceTimeC2Coeff`. -/
theorem level0Resolver_direct_jointC2At_of_majorants
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {s x : ℝ}
    (H : Level0ResolverDirectC2Majorants p u₀ s)
    (hValueAgree :
      (fun q : ℝ × ℝ =>
        intervalDomainLift
          (ShenWork.IntervalCoupledRegularityBootstrap.coupledChemicalConcentration
            p (heatLevel0 p u₀) q.1) q.2)
        =ᶠ[𝓝 (s, x)]
        fun q => ∑' k, level0ResolverCoeff p u₀ k q.1 * cosineMode k q.2)
    (hGradAgree :
      (fun q : ℝ × ℝ =>
        deriv (intervalDomainLift
          (ShenWork.IntervalCoupledRegularityBootstrap.coupledChemicalConcentration
            p (heatLevel0 p u₀) q.1)) q.2)
        =ᶠ[𝓝 (s, x)]
        fun q => ∑' k, level0ResolverCoeff p u₀ k q.1 *
          (-(k : ℝ) * Real.pi * Real.sin ((k : ℝ) * Real.pi * q.2))) :
    ContDiffAt ℝ 2
        (fun q : ℝ × ℝ =>
          intervalDomainLift
            (ShenWork.IntervalCoupledRegularityBootstrap.coupledChemicalConcentration
              p (heatLevel0 p u₀) q.1) q.2) (s, x) ∧
      ContDiffAt ℝ 2
        (fun q : ℝ × ℝ =>
          deriv (intervalDomainLift
            (ShenWork.IntervalCoupledRegularityBootstrap.coupledChemicalConcentration
              p (heatLevel0 p u₀) q.1)) q.2) (s, x) := by
  -- Same proof as `resolverSpectralJointC2At_of_smooth_cutoff_contDiff_tsum`,
  -- but with direct coefficients instead of `localRestartCoeff`.
  have hφ_prod : (fun q : ℝ × ℝ => H.φ q.1) =ᶠ[𝓝 (s, x)] fun _ => 1 :=
    H.hφ_one.comp_tendsto continuous_fst.continuousAt
  have hValue : ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ => ∑' k, cutoffLevel0ResolverValueTerm p u₀ H.φ k q) :=
    contDiff_tsum
      (𝕜 := ℝ)
      (f := fun k : ℕ => cutoffLevel0ResolverValueTerm p u₀ H.φ k)
      (v := H.vValue) H.valueTerm_c2 H.valueSumm H.valueBound
  have hGrad : ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ => ∑' k, cutoffLevel0ResolverGradTerm p u₀ H.φ k q) :=
    contDiff_tsum
      (𝕜 := ℝ)
      (f := fun k : ℕ => cutoffLevel0ResolverGradTerm p u₀ H.φ k)
      (v := H.vGrad) H.gradTerm_c2 H.gradSumm H.gradBound
  have hValueCutEq :
      (fun q : ℝ × ℝ =>
        ∑' k, level0ResolverCoeff p u₀ k q.1 * cosineMode k q.2)
        =ᶠ[𝓝 (s, x)]
        fun q => ∑' k, cutoffLevel0ResolverValueTerm p u₀ H.φ k q := by
    filter_upwards [hφ_prod] with q hq
    simp [cutoffLevel0ResolverValueTerm, hq]
  have hGradCutEq :
      (fun q : ℝ × ℝ =>
        ∑' k, level0ResolverCoeff p u₀ k q.1 *
          (-(k : ℝ) * Real.pi * Real.sin ((k : ℝ) * Real.pi * q.2)))
        =ᶠ[𝓝 (s, x)]
        fun q => ∑' k, cutoffLevel0ResolverGradTerm p u₀ H.φ k q := by
    filter_upwards [hφ_prod] with q hq
    simp [cutoffLevel0ResolverGradTerm, hq]
  exact
    ⟨hValue.contDiffAt.congr_of_eventuallyEq (hValueAgree.trans hValueCutEq),
     hGrad.contDiffAt.congr_of_eventuallyEq (hGradAgree.trans hGradCutEq)⟩

end ShenWork.Paper2.Level0ResolverDirectC2
```

This is the clean direct shortcut pattern.  It is not meant as a drop-in replacement for the current `srcC2` line; it is a replacement for the surrounding consumer path.

## Does the shortcut still need the same λ²-summable data?

Not literally the same package.

The full `DuhamelSourceTimeC2Coeff` structure is strong because the restart coefficient

```lean
c_k(τ) = localRestartCoeff a₀ a τ k
```

satisfies the scalar ODE:

```text
c'_k = a_k - λ_k c_k,
c''_k = adot_k - λ_k a_k + λ_k² c_k.
```

So the generic restart proof asks for λ- and λ²-weighted envelopes for `a` and `adot` to control the value and gradient series after differentiating in time and space.

For the **direct elliptic resolver coefficient**

```lean
v_k(t) = (1 / (μ + λ_k)) * srcTimeCoeff p u k t,
```

the elliptic weight is built in from the start.  Direct `contDiff_tsum` asks for summability of the actual derivatives of `v_k(t)` times the spatial frequency factors.  Schematically, for the gradient field, the worst spatial part is closer to

```text
λ_k^(3/2) * |v_k(t)| ≈ λ_k^(1/2) * |srcCoeff_k(t)|,
```

not `λ_k² * |srcCoeff_k(t)|`.

This is exactly why the repo has the physical lane:

```lean
PhysicalSourceTimeC2
physicalSourceTimeC2_of_floored
physicalResolverJointC2Data_of_floor
```

in `IntervalPhysicalResolverDataConcrete.lean` and `IntervalPhysicalSourceTimeC2Concrete.lean`.  That route folds the resolver weight

```lean
intervalNeumannResolverWeight p k = 1 / (p.μ + λ_k)
```

into the majorants and explicitly says it bypasses the `DuhamelSourceTimeC2Coeff` / eigen-cube ladder.

So:

- If you use **direct elliptic coefficients** or the **physical resolver lane**, you do not need the exact `DuhamelSourceTimeC2Coeff` fields.
- You still need the analytic content of term `C²` and summable majorants for the concrete resolver series.
- If you prove exponential decay of the nonlinear source coefficients on a positive time slab, these majorants are easy.
- If you use only polynomial IBP, the needed depth is lower than the full restart `DuhamelSourceTimeC2Coeff` lane, because the elliptic weight cancels spatial growth.

## Practical recommendation for Q1046

For filling `IntervalResolverLevel0SpectralC2Coeff.lean` specifically, there are two choices:

### Choice A: keep the current theorem shape

Then you must fill:

```lean
srcC2 : DuhamelSourceTimeC2Coeff a
```

No shortcut inside that structure.

### Choice B: replace the theorem path

Add a new direct theorem, e.g.

```lean
level0Resolver_direct_jointC2At_of_majorants
```

or use the already-existing physical resolver lane:

```lean
physicalSourceTimeC2_of_floored
physicalResolverJointC2Data_of_floor
```

Then wire the Level0 FAC/inner-commute proof from this direct local `ContDiffAt` data instead of from `ResolverHasSpectralAgreementC2Coeff`.

This is the real shortcut.  It avoids the full `DuhamelSourceTimeC2Coeff`, but it requires a local rewrite of the consumer path.

---

# Q1042 — uniform bound of `secondDeriv` from joint continuity

## Executive verdict

The compactness bridge is straightforward and should be added as a small generic lemma.

But the hard part is still producing the closed-slab jointly continuous representative `G2` and proving it agrees with the specific `secondDeriv` selected by:

```lean
chemDivSource_weakH2_of_cosineRep
```

The repo has many examples of `continuousOn_tsum`, but I did not find a generic theorem named like:

```lean
tsum_cos_jointContinuousOn
cosine_series_continuousOn_compact
```

Instead, existing files use `continuousOn_tsum` directly:

- `SourceJointRegularity.lean` has private heat-leg joint continuity theorems:
  - `heatValueSeries_jointContinuousOn`
  - `heatDerivSeries_jointContinuousOn`
- `IntervalSourceCoefficientTimeC1.lean` has public restart/Duhamel joint-continuity theorems:
  - `duhamelSeries_jointContinuousOn`
  - `duhamelDerivSeries_jointContinuousOn`
  - `homogeneousSeries_jointContinuousOn`
  - `restartSeries_jointContinuousOn`
- `IntervalResolverSpectralJointC2Cutoff.lean` uses `contDiff_tsum` in the generic resolver C² cutoff theorem.

So for Q1042, the compactness part can be closed now by a generic lemma.  The missing analytic lemma is a `G2` producer.

## Important correction: which representative is relevant for 1A?

For the Level0 1A sorry, the per-slice H² datum comes from:

```lean
chemDivSource_weakH2_of_cosineRep
```

in `IntervalChemDivSpatialC2.lean`.  Inside that theorem, the representative is:

```lean
set F := deriv (chemFluxFun p.β U_cos V_cos)
```

and the H² second derivative is:

```lean
secondDeriv := hF_H2.secondDeriv
```

where `hF_H2` was built by:

```lean
intervalWeakH2Neumann_of_contDiffOn
```

Thus, concretely:

```text
secondDeriv(s,x) = deriv (deriv F_s) x
                 = ∂ₓ² [∂ₓ flux_s](x)
                 = ∂ₓ³ flux_s(x),
```

with

```lean
flux_s(y) = chemFluxFun p.β U_cos_s V_cos_s y.
```

This is **not** merely the second derivative of the resolver source `ν·u^γ`.  The resolver source coefficients are relevant for `v`, but the chemDiv H² source is the spatial derivative of the chemotaxis flux.

So the needed `G2` is something like:

```lean
def chemDivH2SecondRepr
    (p : CM2Params) (U V : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun q =>
    deriv (deriv (deriv (chemFluxFun p.β (U q.1) (V q.1)))) q.2
```

The proof of `ContinuousOn G2 ([c,T]×[0,1])` needs joint continuity of enough spatial derivatives of `U` and `V` up to the order used by this expression.  Fixed-time `ContDiff ℝ 4` is not enough by itself; it must be made uniform/joint in `s` on the positive slab.

## Compactness bridge: concrete Lean code

This is the lemma I would add near `IntervalConjugateLevel0BFormSourceOn.lean`, or in a small helper file imported by it.

```lean
import ShenWork.PDE.IntervalMildSourceDecayHelper

open Set Topology MeasureTheory
open ShenWork.PDE.IntervalMildSourceDecayHelper (IntervalWeakH2Neumann)

noncomputable section

namespace ShenWork.Paper2.Level0SecondDerivCompactBridge

/-- Uniform bound for the selected weak-H² `secondDeriv` once it has a closed-slab
jointly continuous representative.

This is exactly the compactness step needed by Level0 sub-sorry 1A.  The analytic
work is isolated in `G2`, `hG2_cont`, and `hagree`. -/
theorem uniform_secondDeriv_bound_of_closed_repr
    {F : ℝ → ℝ → ℝ} {c T : ℝ}
    (hcT : c ≤ T)
    (H2 : ∀ s, s ∈ Icc c T → IntervalWeakH2Neumann (F s))
    {G2 : ℝ × ℝ → ℝ}
    (hG2_cont : ContinuousOn G2 (Icc c T ×ˢ Icc (0 : ℝ) 1))
    (hagree : ∀ s (hs : s ∈ Icc c T), ∀ x ∈ Icc (0 : ℝ) 1,
      (H2 s hs).secondDeriv x = G2 (s, x)) :
    ∃ C, 0 ≤ C ∧ ∀ s (hs : s ∈ Icc c T),
      ∀ x ∈ Icc (0 : ℝ) 1,
        |(H2 s hs).secondDeriv x| ≤ C := by
  classical
  set K : Set (ℝ × ℝ) := Icc c T ×ˢ Icc (0 : ℝ) 1 with hKdef
  have hKcompact : IsCompact K := by
    rw [hKdef]
    exact isCompact_Icc.prod isCompact_Icc
  have hKnonempty : K.Nonempty := by
    refine ⟨(c, (0 : ℝ)), ?_⟩
    rw [hKdef]
    exact mem_prod.mpr
      ⟨left_mem_Icc.mpr hcT,
       left_mem_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1)⟩
  have hAbsCont : ContinuousOn (fun q : ℝ × ℝ => |G2 q|) K := by
    rw [hKdef]
    exact hG2_cont.abs
  obtain ⟨q0, hq0K, hmax⟩ := hKcompact.exists_isMaxOn hKnonempty hAbsCont
  refine ⟨|G2 q0|, abs_nonneg _, ?_⟩
  intro s hs x hx
  rw [hagree s hs x hx]
  have hqx : (s, x) ∈ K := by
    rw [hKdef]
    exact mem_prod.mpr ⟨hs, hx⟩
  exact hmax hqx

end ShenWork.Paper2.Level0SecondDerivCompactBridge
```

Then the 1A block becomes:

```lean
have hunif_ptwise : ∃ C, 0 ≤ C ∧ ∀ s (hs : s ∈ Icc c T),
    ∀ x ∈ Icc (0 : ℝ) 1, |(hH2_per_slice s hs).secondDeriv x| ≤ C := by
  exact ShenWork.Paper2.Level0SecondDerivCompactBridge
    .uniform_secondDeriv_bound_of_closed_repr
      (F := fun s => coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) s)
      (c := c) (T := T) hcT hH2_per_slice
      hG2_cont hG2_agree
```

where the remaining analytic obligations are:

```lean
hG2_cont : ContinuousOn G2 (Icc c T ×ˢ Icc (0 : ℝ) 1)

hG2_agree : ∀ s (hs : s ∈ Icc c T), ∀ x ∈ Icc (0 : ℝ) 1,
  (hH2_per_slice s hs).secondDeriv x = G2 (s, x)
```

This is exactly the right decomposition: compactness is solved separately from the source/flux calculus.

## Generic cosine-series joint-continuity skeleton

Although no named `tsum_cos_jointContinuousOn` theorem was found, the repo repeatedly uses `continuousOn_tsum`.  A reusable helper can be added if desired:

```lean
import Mathlib.Analysis.Calculus.SmoothSeries
import ShenWork.Paper2.IntervalConjugatePicard

open Set Topology
open ShenWork.CosineSpectrum (cosineMode)

noncomputable section

namespace ShenWork.Paper2.CosineSeriesJointContinuity

/-- Generic joint continuity of a cosine synthesis from a summable uniform majorant. -/
theorem cosineSeries_jointContinuousOn_of_summable_bound
    {K : Set (ℝ × ℝ)} {b : ℝ → ℕ → ℝ} {E : ℕ → ℝ}
    (hterm : ∀ n, ContinuousOn
      (fun q : ℝ × ℝ => b q.1 n * cosineMode n q.2) K)
    (hE : Summable E)
    (hbound : ∀ n, ∀ q ∈ K,
      ‖b q.1 n * cosineMode n q.2‖ ≤ E n) :
    ContinuousOn
      (fun q : ℝ × ℝ => ∑' n, b q.1 n * cosineMode n q.2) K := by
  exact continuousOn_tsum hterm hE hbound

/-- Joint continuity of a second-spatial-derivative cosine synthesis.
If `F(s,x) = ∑ b(s,n) cos(nπx)`, then formally
`∂ₓ²F(s,x) = ∑ -λₙ b(s,n) cos(nπx)`. -/
theorem cosineSeries_secondDeriv_jointContinuousOn_of_summable_bound
    {K : Set (ℝ × ℝ)} {b : ℝ → ℕ → ℝ} {E : ℕ → ℝ}
    (hterm : ∀ n, ContinuousOn
      (fun q : ℝ × ℝ =>
        (-(unitIntervalCosineEigenvalue n) * b q.1 n) * cosineMode n q.2) K)
    (hE : Summable E)
    (hbound : ∀ n, ∀ q ∈ K,
      ‖(-(unitIntervalCosineEigenvalue n) * b q.1 n) * cosineMode n q.2‖ ≤ E n) :
    ContinuousOn
      (fun q : ℝ × ℝ => ∑' n,
        (-(unitIntervalCosineEigenvalue n) * b q.1 n) * cosineMode n q.2) K := by
  exact continuousOn_tsum hterm hE hbound

end ShenWork.Paper2.CosineSeriesJointContinuity
```

For the actual 1A `secondDeriv`, the coefficient-series route may not be the shortest route, because `secondDeriv` is tied to the `F := deriv (chemFluxFun ...)` representative chosen in `chemDivSource_weakH2_of_cosineRep`.  It may be cleaner to define `G2` by the chain-rule expression and prove `hG2_cont` from joint regularity of `U_cos`/`V_cos` and their spatial derivatives, instead of re-identifying it as a cosine series.

## What repo theorem is closest?

The closest public reusable tools are:

```lean
continuousOn_tsum
contDiff_tsum
```

plus examples:

```lean
ShenWork.IntervalSourceCoefficientTimeC1.duhamelSeries_jointContinuousOn
ShenWork.IntervalSourceCoefficientTimeC1.duhamelDerivSeries_jointContinuousOn
ShenWork.IntervalSourceCoefficientTimeC1.homogeneousSeries_jointContinuousOn
ShenWork.IntervalSourceCoefficientTimeC1.restartSeries_jointContinuousOn
```

and the private examples in:

```lean
ShenWork.EWA.SourceJointRegularity.heatValueSeries_jointContinuousOn
ShenWork.EWA.SourceJointRegularity.heatDerivSeries_jointContinuousOn
```

The theorem

```lean
ShenWork.IntervalDomainPositiveWindowK1OnEndpoint
  .cosineCoeffs_continuousOn_of_jointContinuousOn_Icc
```

is useful in the reverse direction: joint continuity of a spatial field gives continuity of each cosine coefficient in time.  It does not synthesize joint continuity of a cosine series.

## Bottom line for Q1042

The compactness bridge is available with a small lemma, shown above.  The repo does not appear to have a single generic `tsum_cos_jointContinuousOn` theorem, but it has the Mathlib `continuousOn_tsum` pattern repeatedly instantiated.

The remaining analytic task is to build the closed-slab representative:

```lean
G2(s,x) = ∂ₓ² [∂ₓ chemFluxFun p.β U_s V_s](x)
```

or an equivalent cosine-series representative, prove:

```lean
ContinuousOn G2 (Icc c T ×ˢ Icc 0 1)
```

and prove that this is exactly the `secondDeriv` field selected by `chemDivSource_weakH2_of_cosineRep`.

That is the real 1A closure point; after that, the uniform bound is just compactness.
