# Q343 (cron2): heat smoothing, EWA start data, and the χ₀<0 unconditional route

## Executive verdict

The obstruction is **real for the current EWA framework**, but it is **not a mathematical requirement of Paper 2 local existence**.

A merely positive continuous datum on `[0,1]` need not have absolutely summable cosine coefficients, so it need not produce a `WA 1` datum. The EWA fixed-point tower still requires exactly that `WA 1` datum:

```lean
hsumc : Summable (fun k => |cosineCoeffs u₀ k|)
hmem  : MemW 1 (ofCosineCoeffs (cosineCoeffs u₀))
```

This is visible in the current χ₀<0 source-form fixed-point engine and in the strong-datum wrapper.

There is **partial heat-smoothing infrastructure** in the repo:

```lean
ShenWork.Wiener.EWA.HeatSmoothing.heat_L2_to_memHSob
ShenWork.Wiener.EWA.HeatSmoothing.heat_L2_to_memWNorm
```

but it is not yet the exact bridge needed for the EWA tower, namely:

```lean
0 < t₀ → Continuous u₀ → bounded cosine coefficients of u₀
→ MemW 1 (ofCosineCoeffs (fun k => exp (-t₀ * λ_k) * cosineCoeffs u₀ k))
```

The closest landed ingredients are `HeatSmoothing.lean` and the level-0 heat-slice coefficient identity:

```lean
heatSliceCoeff_eq_damped :
  cosineCoeffs (intervalDomainLift (picardIter p u₀ 0 σ)) k
    = Real.exp (-σ * λ_k) * heatCoeff u₀ k
```

So the positive-time smoothing fix is analytically right, but the exact `S(t₀)u₀ ∈ WA 1` bridge is not obviously already packaged as a theorem.

The clean strategic fix is **not** “EWA from the raw datum.” It is:

```text
canonical/local PDE chain for arbitrary positive C⁰ datum u₀
  → get a classical/mild solution on [0,t₀]
  → use u(t₀) as a smooth/Wiener datum for the EWA/source-regularity chain
  → glue/identify by uniqueness on the overlap, or use the EWA chain only as a positive-time regularity supplier.
```

The repo already has forward restart/glue infrastructure, but it does **not** take a solution constructed only after `t₀` and extend it backward to the original datum. To connect back to `t=0`, you still need the canonical local solution from `u₀` on `[0,t₀]`, then restart from an interior slice.

## 1. Heat smoothing → cosine summability: what is actually in the repo?

### 1.1 `HeatFloorIcc.lean` is not the smoothing bridge

`HeatFloorIcc.lean` is about the **positivity floor**, not about manufacturing Wiener summability. Its docstring explicitly says the remaining datum-level gap is:

```text
obstruction (a) — the Wiener-ℓ¹ / absolute cosine summability `Summable |c₀ k|`
and the corresponding `MemW` membership — which the C(Ω̄)+floor class does NOT supply.
```

The theorem it ultimately provides still takes both summability and `MemW` as inputs:

```lean
import ShenWork.Wiener.EWA.HeatFloorIcc

open ShenWork.GWA ShenWork.Wiener ShenWork.EWA
open ShenWork.IntervalNeumannFullKernel

#check ShenWork.EWA.heatEWA_uniformFloor_Icc
-- theorem heatEWA_uniformFloor_Icc
--   {u₀ : ℝ → ℝ} (hu₀ : Continuous u₀) {δ : ℝ}
--   (hfloor : ∀ y ∈ Set.Icc (0 : ℝ) 1, δ ≤ u₀ y)
--   (hsum : Summable (fun k => |cosineCoeffs u₀ k|))
--   (hmem : MemW 1 (ofCosineCoeffs (cosineCoeffs u₀))) :
--   UniformFloor (heatEWA (T := T)
--     (⟨ofCosineCoeffs (cosineCoeffs u₀), hmem⟩ : WA 1)) δ

#check ShenWork.EWA.paperFloorDatum_heatEWA_uniformFloor
-- theorem paperFloorDatum_heatEWA_uniformFloor
--   ...
--   (hsum : Summable (fun k => |cosineCoeffs u₀ k|))
--   (hmem : MemW 1 (ofCosineCoeffs (cosineCoeffs u₀))) :
--   UniformFloor (heatEWA ... ) η
```

So `HeatFloorIcc` discharges the **floor** from closed-domain positivity; it deliberately does **not** discharge the raw datum `MemW 1` obstruction.

### 1.2 `HeatFlow.lean` constructs heat flow only from an existing `WA r` input

`HeatFlow.lean` has:

```lean
import ShenWork.Wiener.EWA.HeatFlow

open ShenWork.GWA ShenWork.Wiener ShenWork.EWA

#check ShenWork.EWA.heatEWA
-- noncomputable def heatEWA (u₀E : WA r) : EWA T r

#check ShenWork.EWA.heatEWA_mem
-- theorem heatEWA_mem (u₀E : WA r) :
--   GMemW (K := CT T) r (fun n => heatModeCT n (u₀E.toFun n))
```

This proves the heat evolution preserves a Wiener datum already in `WA r`. It does not turn arbitrary continuous data into `WA r`.

### 1.3 `HeatSmoothing.lean` is close, but not the exact `WA 1` bridge

There is a useful heat-smoothing file:

```lean
import ShenWork.Wiener.EWA.HeatSmoothing

open ShenWork.Wiener.EWA

#check ShenWork.Wiener.EWA.heat_L2_to_memHSob
-- theorem heat_L2_to_memHSob {θ t : ℝ}
--   (hθ : 0 ≤ θ) (ht : 0 < t) {f : ℕ → ℝ}
--   (hf : MemL2 f) : MemHSob θ (heatCoeff t f)

#check ShenWork.Wiener.EWA.heat_L2_to_memWNorm
-- theorem heat_L2_to_memWNorm {θ t : ℝ}
--   (hθ : (1 / 2 : ℝ) < θ) (ht : 0 < t) {f : ℕ → ℝ}
--   (hf : MemL2 f) : MemWNorm 0 (heatCoeff t f)
```

This proves positive-time smoothing into `A⁰ = MemWNorm 0`. Since `heat_L2_to_memHSob` is for arbitrary `θ ≥ 0`, one should be able to get an `A¹` version by composing with:

```lean
#check ShenWork.Wiener.EWA.memWNorm_of_memHSob
-- theorem memWNorm_of_memHSob {σ s : ℝ}
--   (hs : σ + 1 / 2 < s) {a : ℕ → ℝ}
--   (ha : MemHSob s a) : MemWNorm σ a
```

with `σ := 1` and any `s > 3/2`.

But I did not find an already-packaged theorem of the exact form:

```lean
heat_C0_to_MemW1_or_WA1_at_positive_time
```

nor a theorem that directly produces:

```lean
MemW 1 (ofCosineCoeffs (fun k => Real.exp (-t₀ * λ_k) * cosineCoeffs u₀ k))
```

from `Continuous u₀` or `PositiveInitialDatum`.

### 1.4 The closest concrete coefficient identity is already present

For the level-0 heat slice, the repo has:

```lean
import ShenWork.Paper2.IntervalPicardLevel0SourceTimeC1On

open ShenWork.IntervalPicardLevel0SourceTimeC1On

#check heatSliceCoeff_eq_damped
-- theorem heatSliceCoeff_eq_damped
--   (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
--   {σ M₀ : ℝ} (hσ : 0 < σ) (hu₀_cont : Continuous u₀)
--   (hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀) (k : ℕ) :
--   cosineCoeffs (intervalDomainLift (picardIter p u₀ 0 σ)) k =
--     Real.exp (-σ * λ_k) * heatCoeff u₀ k
```

This is nearly the bridge you want. Given a crude uniform coefficient bound on the raw cosine coefficients, the exponential damping gives weighted ℓ¹ summability for positive `σ`. What still seems missing is the final packaging into `MemW 1` / `WA 1` for the smoothed datum.

A plausible missing theorem shape is:

```lean
import ShenWork.Paper2.IntervalPicardLevel0SourceTimeC1On
import ShenWork.Wiener.EWA.HeatFlow

open ShenWork.GWA ShenWork.Wiener ShenWork.EWA
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalPicardLevel0SourceTimeC1On

-- Suggested missing bridge.
theorem heatSlice_MemW1_of_coeff_bound
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {σ M₀ : ℝ} (hσ : 0 < σ)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀) :
    MemW 1 (ofCosineCoeffs
      (fun k => cosineCoeffs (intervalDomainLift (picardIter p u₀ 0 σ)) k)) := by
  -- Use `heatSliceCoeff_eq_damped` to rewrite coefficients as
  --   exp(-σ λ_k) * heatCoeff u₀ k.
  -- Bound by `M₀ * exp(-σ λ_k)`.
  -- Prove `∑ (1+k) * M₀ * exp(-σ λ_k)` summable from the existing heat-trace
  -- exponential summability lemmas.
  -- Then fold through `ofCosineCoeffs`/`MemW 1`.
  sorry
```

That bridge is finite and much smaller than the original global EWA obstruction.

## 2. Restart / continuation: what exists and what it does

The repo has a forward restart-and-glue interface:

```lean
import ShenWork.Paper2.IntervalDomainRestartExtension

open ShenWork.Paper2.RestartExtension

#check RestartAndGlueWorks
-- def RestartAndGlueWorks (p : CM2Params) : Prop :=
--   ∀ {M δ : ℝ}, 0 < M → 0 < δ →
--     (∀ {w : intervalDomain.Point → ℝ},
--       PositiveInitialDatum intervalDomain w →
--       (∀ x, |w x| ≤ M) →
--       ∃ uw vw, IsPaper2ClassicalSolution intervalDomain p δ uw vw ∧
--         InitialTrace intervalDomain w uw) →
--     ∀ {u₀}, PositiveInitialDatum intervalDomain u₀ →
--       (∀ x, |u₀ x| ≤ M) →
--     ∀ {T₀}, 0 < T₀ →
--     ∀ {u v}, IsPaper2ClassicalSolution intervalDomain p T₀ u v →
--       InitialTrace intervalDomain u₀ u →
--       (∀ t, 0 < t → t < T₀ → ∀ x, |u t x| ≤ M) →
--       ∃ u' v', IsPaper2ClassicalSolution intervalDomain p (T₀ + δ / 2) u' v' ∧
--         InitialTrace intervalDomain u₀ u'
```

And a concrete glue theorem from explicit hypotheses:

```lean
import ShenWork.Paper2.IntervalDomainGlueExtension

open ShenWork.Paper2.GlueExtension

#check restartAndGlueWorks_of_hypotheses
-- theorem restartAndGlueWorks_of_hypotheses
--   (p : CM2Params)
--   (hRegShift : TimeShift.RegularityTimeShiftWorks)
--   (hOverlap : OverlapUniqueForPID p)
--   (hTraceShift : TimeShiftInitialTraceWorks)
--   (hPR : PiecewiseGlue.PiecewiseClassicalWorks p) :
--   RestartAndGlueWorks p
```

This is a **forward extension** mechanism. It assumes an existing solution on `[0,T₀]`, restarts from an interior slice near `T₀`, and glues forward. It does not say:

```text
given a solution on (t₀,t₀+T), extend backward to initial datum u₀ at t=0.
```

So the proposed “start EWA at `S(t₀)u₀`, then extend back to `t=0`” is not directly supported as a backward theorem. The Lean-faithful way is:

```text
1. Use canonical/local existence from u₀ to build a solution on [0,t₀].
2. Use an interior slice u(t₀) or u(t₀/2) as the restart datum.
3. Run the EWA or source-regularity chain from that positive-time datum.
4. Glue forward using overlap uniqueness / time-shift / piecewise-classical infrastructure.
```

This matches how `RestartAndGlueWorks` is typed.

## 3. Does the canonical Picard chain require cosine summability?

The core canonical gradient-mild Picard chain does **not** expose a `MemW 1` or absolute cosine summability assumption in its primary data structure.

`MildExistenceData` is function-space / kernel-based:

```lean
import ShenWork.Paper2.IntervalMildPicard

open ShenWork.IntervalMildPicard

#check MildExistenceData
-- structure MildExistenceData (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) where
--   T M K C₀ : ℝ
--   hbase_ball : ... |picardIter p u₀ 0 t x| ≤ M
--   hbase_nonneg : ... 0 ≤ picardIter p u₀ 0 t x
--   hbase_cont : HasContinuousSlices T (picardIter p u₀ 0)
--   hmapsTo / hmapsTo_nn / hmapsTo_pos
--   hcont_preserved
--   hcontr
--   hbase_diff
--   hbase_meas
--   hmeas_preserved
```

The output is:

```lean
#check intervalMildSolution_of_data
-- theorem intervalMildSolution_of_data
--   (D : MildExistenceData p u₀) :
--   ∃ T > 0, ∃ u, IntervalMildSolution p T u₀ u

#check GradientMildSolutionData
#check gradientMildSolutionData_of_data
```

This layer is not the EWA layer. It defines Picard iterates as plain functions and uses the Neumann heat kernel / Duhamel map machinery. The module docstring even says it avoids the bounded-continuous-function topology and proceeds by pointwise Cauchy convergence.

At the theorem-assembly level, the repo has a local-existence input stated for every positive admissible datum:

```lean
import ShenWork.Paper2.IntervalDomainTheorem11Umbrella

open ShenWork.Paper2

#check IntervalDomainGradientMildLocalData
-- def IntervalDomainGradientMildLocalData (p : CM2Params) : Prop :=
--   ∀ u₀, PositiveInitialDatum intervalDomain u₀ →
--     ∃ D : GradientMildSolutionData p u₀,
--       initial-approach ∧
--       IsPaper2ClassicalSolution intervalDomain p D.T D.u ...

#check localExistence_of_gradientMildLocalData
-- theorem localExistence_of_gradientMildLocalData
--   (p : CM2Params)
--   (hMildLocal : IntervalDomainGradientMildLocalData p) :
--   ∀ u₀, PositiveInitialDatum intervalDomain u₀ →
--     ∃ Tmax > 0, ∃ u v,
--       IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
--       InitialTrace intervalDomain u₀ u
```

There is also a B-form positive-datum route:

```lean
import ShenWork.Paper2.IntervalBFormPositiveDatumLocalExistence

open ShenWork.Paper2.BFormPositiveDatumLocal

#check PositiveDatumBFormLocalHyp
-- def PositiveDatumBFormLocalHyp (p : CM2Params) : Prop :=
--   ∀ u₀, PositiveInitialDatum intervalDomain u₀ →
--     Nonempty (PositiveDatumBFormLocalComponents p u₀)

#check positiveDatum_localExistence_of_BForm
-- theorem positiveDatum_localExistence_of_BForm
--   (hBForm : PositiveDatumBFormLocalHyp p) :
--   ∀ u₀, PositiveInitialDatum intervalDomain u₀ →
--     ∃ Tmax > 0, ∃ u v,
--       IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
--       InitialTrace intervalDomain u₀ u
```

So yes: the canonical chain can be routed over arbitrary positive continuous data, modulo its own Picard/local-classical side conditions. It does not require the raw datum to be a `WA 1` datum.

## 4. Is the cosine-summability obstruction an EWA artifact?

Yes. It is an artifact of the **EWA source-form fixed-point framework**, not a genuine mathematical requirement for Keller–Segel local existence from positive continuous data.

The evidence is visible in the EWA fixed-point theorem:

```lean
import ShenWork.Wiener.EWA.SourceUncondFixedPoint

open ShenWork.EWA

#check picardEWA_uncond_fixedPoint
-- theorem picardEWA_uncond_fixedPoint ...
--   (hsumc : Summable (fun k => |cosineCoeffs u₀ k|))
--   (hmem : MemW 1 (ofCosineCoeffs (cosineCoeffs u₀)))
--   ...
--   ∃ u_star ∈ closedBall (heatEWA ... ) ρ,
--     u_star = picardEWA ... u_star
```

And in the strong-datum wrapper:

```lean
#check chiNegStrong_heatFloor_of_paperDatum
-- theorem chiNegStrong_heatFloor_of_paperDatum
--   ...
--   (hsum : Summable (fun k => |cosineCoeffs u₀ k|))
--   (hmem : MemW 1 (ofCosineCoeffs (cosineCoeffs u₀))) :
--   ∃ η > 0, UniformFloor (heatEWA ... ) η
```

The comments in `SourceChiNegUncondFix.lean` identify the same issue: the strong datum supplies the floor, but not the cosine-summability/Wiener membership. It says the remaining residual includes the per-slice realization frontier and notes that the EWA fixed-point engine still needs standard `hsumc`/`hmem` inputs.

Mathematically, positive-time heat smoothing eliminates the rough datum issue. Lean-wise, the correct hybrid plan is:

```text
A. Use the canonical local-existence chain from raw positive C⁰ datum u₀.
B. Pick t₀ > 0 inside that local solution.
C. Prove the slice u(t₀) has the coefficient envelope needed by EWA:
     MemW 1 (ofCosineCoeffs (cosineCoeffs (intervalDomainLift (u t₀))))
   or a direct `Bv` envelope for `embedEWA`.
D. Run the EWA/source-regularity chain on the restarted interval with datum u(t₀).
E. Glue/identify with the canonical solution using overlap uniqueness, or only use EWA to supply positive-time regularity fields.
```

## Recommended next theorem targets

### Target 1: exact positive-time heat-to-`WA 1` bridge

This is the missing small bridge if the restart datum is literally a heat slice:

```lean
import ShenWork.Paper2.IntervalPicardLevel0SourceTimeC1On
import ShenWork.Wiener.EWA.HeatFlow

open ShenWork.IntervalPicardLevel0SourceTimeC1On
open ShenWork.GWA ShenWork.Wiener ShenWork.EWA
open ShenWork.IntervalNeumannFullKernel

-- Suggested target.
theorem heatSlice_MemW1_of_coeff_bound
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {σ M₀ : ℝ} (hσ : 0 < σ)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀) :
    MemW 1 (ofCosineCoeffs
      (fun k => cosineCoeffs (intervalDomainLift (picardIter p u₀ 0 σ)) k)) := by
  -- Rewrite by `heatSliceCoeff_eq_damped`.
  -- Bound by `M₀ * exp(-σ λ_k)`.
  -- Use exponential summability with polynomial weight `(1+k)`.
  -- Fold through `ofCosineCoeffs`.
  sorry
```

### Target 2: general positive-time solution-slice Wiener bridge

For the actual nonlinear solution, this is the stronger target:

```lean
import ShenWork.Wiener.EWA.EmbedEWA

open ShenWork.EWA

-- Suggested target.
theorem classical_positive_time_slice_has_A1_envelope
    {p : CM2Params} {T t₀ : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht₀ : 0 < t₀) (ht₀T : t₀ < T) :
    ∃ Bv : ℕ → ℝ,
      (∀ k, 0 ≤ Bv k) ∧
      Summable (fun k => (1 + (k : ℝ)) * Bv k) ∧
      (∀ k, |cosineCoeffs (intervalDomainLift (u t₀)) k| ≤ Bv k) := by
  -- Use positive-time classical/smoothing regularity or C² coefficient decay.
  -- A `C²` Neumann slice gives O(k^{-2}); weighted by (1+k) this is summable.
  sorry
```

If `intervalDomainClassicalRegularity` already gives closed spatial `C²` with Neumann data at positive times, this theorem should be much more direct than proving EWA existence from the raw datum.

### Target 3: restart/EWA splice theorem

This is the correct glue shape:

```lean
-- Pseudocode shape, not an existing theorem name.
theorem canonical_then_EWA_positive_time_splice
    (hlocal : local solution from u₀ on [0,t₀])
    (hA1 : A¹/Wiener data for u(t₀))
    (hEWA : EWA source-regularity/classical core from u(t₀) on [0,T])
    (huniq : overlap uniqueness) :
    solution / regularity on [0,t₀+T]
```

Do not try to construct a solution on `(0,t₀+T)` by running EWA from `S(t₀)u₀` alone unless you also identify `S(t₀)u₀` with the actual nonlinear solution slice. In the nonlinear problem, `u(t₀)` is not merely `S(t₀)u₀`; it includes Duhamel source contributions. `S(t₀)u₀` is useful for a smoothing seed, but it is not the exact state of the nonlinear solution at time `t₀`.

## Final answers to the four questions

1. **Heat smoothing bridge:** partially yes, but not the exact EWA-start bridge. `HeatSmoothing.lean` gives `L² → H^θ` and `L² → A⁰`. `HeatFloorIcc.lean` is not the smoothing bridge; it still requires `Summable |cosineCoeffs u₀|` and `MemW 1`. A direct positive-time `C⁰ → WA 1` theorem for the damped heat coefficients appears not to be packaged, though the needed ingredients exist.

2. **Restart / continuation:** yes, forward restart-and-glue exists (`RestartAndGlueWorks`, `restartAndGlueWorks_of_hypotheses`). It extends an existing solution forward by restarting from an interior slice. It does not extend a later EWA solution backward to the original datum.

3. **Canonical Picard:** the function-space Picard chain (`MildExistenceData`, `GradientMildSolutionData`) does not require raw `MemW 1`. It is formulated over positive continuous interval data and the kernel/Duhamel map, modulo its own maps-to/contraction/classicality side conditions. The B-form and gradient-mild local-data routes expose local existence for arbitrary positive data through component/frontier packages, not through EWA raw-datum membership.

4. **Strategic classification:** the cosine-summability obstruction is an EWA artifact. The mathematically faithful route is hybrid: canonical local existence for arbitrary positive `C⁰` data, then positive-time smoothing/regularity to get EWA-compatible data, then EWA only as a positive-time source-regularity/spectral-realization engine. This avoids demanding `MemW 1` at `t=0`, where it is false for general continuous data.
