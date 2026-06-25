# Q363 (cron2): `LimitRegularityInputs` and the χ₀<0 resolver-data route

## Executive verdict

I read the current definitions.

`MildLocalChi0.LimitRegularityInputs` is **not** a mild-fixed-point package. It contains exactly one field that is the mild equation (`hfix`) plus a large amount of independent datum/coefficient/spectral/spatial/classical/frontier data. The current definition does **not** ask for datum absolute cosine summability as a field; it asks for a bounded datum-coefficient witness (`M₀`, `hu₀_bound`) and for per-slice summability/series representation (`bc`, `hbsum`, `hagree`).

From the mild contraction fixed point **alone**, the only `LimitRegularityInputs` field I would count as directly produced is `hfix`. If one also carries the ordinary external hypotheses used to launch the fixed point, then `hα`, `ha`, `hb`, `hu₀_cont`, and possibly elementary bounded-coefficient/ball facts can be supplied from those external assumptions/packages. But that is not “from the fixed-point equality alone,” and it does not produce the spectral K1/K2 ledger, `hpde_u`, `Hvsrc`, or `Hvpos`.

`Hu` is the one subtle exception: `IntervalDomainLedgerSweep.lean` now deletes `Hu` from a reduced ledger and reconstructs it. But that reconstruction still uses the heavy reduced ledger fields (`hsrc0`, `bc/hbsum/hagree`, `hG1t/hG2t`, K1 coefficient time-C¹ data, etc.). So `Hu` is derivable from the **reduced regularity ledger**, not from the mild fixed point alone.

The repo **does** contain

```lean
coupledFluxClassicalLocalExistenceResidual_of_resolverAnalyticData
```

in `ShenWork/Paper2/IntervalDomainThm11ChiNegResidual.lean`. It takes `CoupledFluxResolverAnalyticData`. That object is a nested `Prop`, not a structure with projections. Its final datum-level payload is:

1. `IntervalCoupledResolverBallEstimates p (intervalNeumannResolverR p) u0 T Mball K`, and
2. a regularization bridge from any bounded coupled-Duhamel fixed point with `v = intervalNeumannResolverR p (u t)` to `RegularityBootstrap p T u0 u`.

So `CoupledFluxResolverAnalyticData` is **not easier than `hregularize` in the absolute sense**: it includes an `hregularize`-shaped obligation plus resolver ball estimates and uniform parameter choices. It is cleaner than the χ₀=0 spectral ledger only in the sense that it avoids the `LimitRegularityInputs` K1/K2 cosine-restart machinery. The hard PDE/classical-bootstrap content remains.

## Lean probes used

```lean
import ShenWork.Paper2.IntervalDomainMildLocalChi0
import ShenWork.Paper2.IntervalDomainLedgerSweep

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalGradientDuhamelMap (intervalGradientDuhamelMap)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)
open ShenWork.IntervalMildToClassical (mildChemicalConcentration)
open ShenWork.IntervalMildPicardRegularity (logisticSourceFun)
open ShenWork.IntervalMildTimeDerivContinuity
  (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.PDE (intervalNeumannResolverSourceCoeff)

#check ShenWork.Paper2.MildLocalChi0.LimitRegularityInputs
#check ShenWork.Paper2.MildLocalChi0.LimitRegularityInputs.hfix
#check ShenWork.Paper2.MildLocalChi0.LimitRegularityInputs.Hu
#check ShenWork.Paper2.MildLocalChi0.LimitRegularityInputs.Hvsrc
#check ShenWork.Paper2.LedgerSweep.ReducedLimitRegularityInputs
#check ShenWork.Paper2.LedgerSweep.Hu_of_reduced
#check ShenWork.Paper2.LedgerSweep.limitRegularityInputs_of_reduced
```

```lean
import ShenWork.Paper2.IntervalDomainThm11ChiNegResidual

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.PDE
open ShenWork.Paper2.ChiNegResidual

#check CoupledFluxClassicalLocalExistenceResidual
#check CoupledFluxResolverAnalyticData
#check exactLocalClassicalSolution_of_coupledDuhamel_resolver_estimates
#check coupledFluxClassicalLocalExistenceResidual_of_resolverAnalyticData
#check IntervalCoupledResolverBallEstimates
#check RegularityBootstrap
```

## 1. Exact contents of `LimitRegularityInputs`

Definition read from `ShenWork/Paper2/IntervalDomainMildLocalChi0.lean`:

```lean
import ShenWork.Paper2.IntervalDomainMildLocalChi0

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalGradientDuhamelMap (intervalGradientDuhamelMap)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)
open ShenWork.IntervalMildToClassical (mildChemicalConcentration)
open ShenWork.IntervalMildPicardRegularity (logisticSourceFun)
open ShenWork.IntervalMildTimeDerivContinuity
  (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.PDE (intervalNeumannResolverSourceCoeff)

-- Current object:
#check ShenWork.Paper2.MildLocalChi0.LimitRegularityInputs

-- The full structure, as read, has these fields:
--
-- structure LimitRegularityInputs
--     (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
--     (D : GradientMildSolutionData p u₀) where
--   hα : 1 ≤ p.α
--   ha : 0 ≤ p.a
--   hb : 0 ≤ p.b
--   hu₀_cont : Continuous u₀
--   M₀ : ℝ
--   hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀
--   hfix : ∀ t, 0 < t → t < D.T → ∀ x : ℝ,
--     (hx : x ∈ Set.Icc (0:ℝ) 1) →
--       intervalDomainLift (D.u t) x =
--         intervalGradientDuhamelMap p u₀ D.u t ⟨x, hx⟩
--   hsrc0 : ShenWork.IntervalPicardLimitRestartBdd.DuhamelSourceBddOn
--     (ShenWork.IntervalPicardLimitBddProducer.patchedSource p u₀ D.u) D.T
--   Msup : ℝ
--   bc : ℝ → ℕ → ℝ
--   hbsum : ∀ σ, 0 < σ → σ < D.T →
--     Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|)
--   hagree : ∀ σ, 0 < σ → σ < D.T →
--     Set.EqOn (intervalDomainLift (D.u σ))
--       (fun x => ∑' n, bc σ n * cosineMode n x)
--       (Set.Icc (0 : ℝ) 1)
--   hpost : ∀ σ, 0 < σ → σ < D.T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
--     0 < intervalDomainLift (D.u σ) x
--   hubt : ∀ σ, 0 < σ → σ < D.T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
--     intervalDomainLift (D.u σ) x ≤ Msup
--   hG1t : ∀ a' b', 0 < a' → b' < D.T → ∃ G1,
--     ∀ σ ∈ Set.Icc a' b', ∀ x ∈ Set.Icc (0 : ℝ) 1,
--       |deriv (intervalDomainLift (D.u σ)) x| ≤ G1
--   hG2t : ∀ a' b', 0 < a' → b' < D.T → ∃ G2,
--     ∀ σ ∈ Set.Icc a' b', ∀ x ∈ Set.Icc (0 : ℝ) 1,
--       |deriv (deriv (intervalDomainLift (D.u σ))) x| ≤ G2
--   hN0t : ∀ σ, 0 < σ → σ < D.T →
--     deriv (intervalDomainLift (D.u σ)) 0 = 0
--   hN1t : ∀ σ, 0 < σ → σ < D.T →
--     deriv (intervalDomainLift (D.u σ)) 1 = 0
--   adott : ℝ → ℕ → ℝ
--   hderivt : ∀ σ, 0 < σ → σ < D.T → ∀ k,
--     HasDerivAt
--       (fun r => cosineCoeffs
--         (logisticSourceFun p.a p.b p.α (intervalDomainLift (D.u r))) k)
--       (adott σ k) σ
--   hadotcontt : ∀ k, ContinuousOn (fun σ => adott σ k) (Set.Ioo 0 D.T)
--   hMdott : ∀ a' b', 0 < a' → b' < D.T → ∃ Mdot,
--     ∀ σ ∈ Set.Icc a' b', ∀ k, |adott σ k| ≤ Mdot
--   hLc : ∀ t, 0 < t → t < D.T →
--     ∀ s, 0 < s → s ≤ t → Continuous (intervalLogisticSource p (D.u s))
--   hpde_u :
--     ∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
--       intervalDomain.timeDeriv D.u t x =
--         intervalDomain.laplacian (D.u t) x
--           - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
--               (mildChemicalConcentration p D.u t) x
--           + D.u t x * (p.a - p.b * (D.u t x) ^ p.α)
--   Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u
--   Hvsrc : ∀ t₀, 0 < t₀ → t₀ < D.T →
--     ∃ (aC : ℝ → ℕ → ℝ) (_ : DuhamelSourceTimeC1 aC) (W : Set ℝ),
--       W ∈ 𝓝 t₀ ∧
--       (∀ s ∈ W, ∀ k,
--         aC s k = (intervalNeumannResolverSourceCoeff p (D.u s) k).re)
--   Hvpos : ∀ t, 0 < t → t < D.T → ∀ x : intervalDomainPoint,
--     0 < mildChemicalConcentration p D.u t x
```

Grouped semantically, that is:

* Regime fields: `hα`, `ha`, `hb`.
* Datum fields: `hu₀_cont`, `M₀`, `hu₀_bound`.
* Fixed-point field: `hfix`.
* Weak source package: `hsrc0` for the patched logistic-source coefficients.
* K2/slice representation and spatial bounds: `Msup`, `bc`, `hbsum`, `hagree`, `hpost`, `hubt`, `hG1t`, `hG2t`, `hN0t`, `hN1t`.
* K1/time-coefficient data: `adott`, `hderivt`, `hadotcontt`, `hMdott`.
* H3 slice continuity: `hLc`.
* Frontier/classical residuals: `hpde_u`, `Hu`, `Hvsrc`, `Hvpos`.

Important correction to older mental models: there is no current `HsupNorm` field in this structure, and there is no datum field literally saying `Summable (fun k => |cosineCoeffs (intervalDomainLift u₀) k|)`. The datum field is the uniform bound `hu₀_bound`; the summability field in this structure is the per-positive-slice representation field `hbsum`.

## 2. What can be produced from the mild fixed point alone?

By “mild fixed point alone,” I mean just the equality `u = Φ(u)` produced by the contraction/Picard step, not the whole surrounding cone package, not the PID hypotheses, and not extra spectral regularity inputs.

Under that interpretation:

* Directly produced: `hfix`.
* Not produced by the fixed-point equality itself: essentially everything else.

More nuanced split:

* `hα`, `ha`, `hb` are regime assumptions on `p`, not consequences of a fixed point.
* `hu₀_cont` is from the initial datum/PID assumption, not from the fixed point.
* `M₀`/`hu₀_bound` are not datum absolute summability. They are plausibly routine from bounded/continuous datum plus coefficient estimates, but still not from the fixed-point equality alone.
* `hpost`/`hubt` may be available from the stronger cone/closed-ball construction package, depending on which `D` is in hand, but not from the equality `u = Φ(u)` alone.
* `hsrc0`, `bc`, `hbsum`, `hagree`, `hG1t`, `hG2t`, `hN0t`, `hN1t`, `adott`, `hderivt`, `hadotcontt`, `hMdott`, and `hLc` are the real K1/K2/continuity regularity ledger. They require spectral/coefficient/spatial bootstrap inputs. They are not consequences of a bare contraction fixed point.
* `hpde_u` is the pointwise parabolic PDE. The file comments explicitly treat it as a residual because the available mild-to-PDE producer is circular at this layer.
* `Hvsrc` is a per-`t₀` clamped resolver-source `DuhamelSourceTimeC1` witness. It is not generated by the u-fixed-point equation alone.
* `Hvpos` is strict positivity of the elliptic chemical concentration. The ledger comments treat this as a strong-maximum-principle type residual.

The special case is `Hu`. `IntervalDomainLedgerSweep.lean` defines `ReducedLimitRegularityInputs` by deleting `Hu`, and proves:

```lean
import ShenWork.Paper2.IntervalDomainLedgerSweep

open ShenWork.Paper2.LedgerSweep

#check ReducedLimitRegularityInputs
#check Hu_of_reduced
#check limitRegularityInputs_of_reduced
```

That gives the theorem-level fact:

```lean
-- Conceptually:
-- ReducedLimitRegularityInputs p u₀ D  +  hχ0 : p.χ₀ = 0
--   ⟹ HasTimeNeighborhoodSpectralAgreement D.T D.u
--   ⟹ LimitRegularityInputs p u₀ D
```

But `Hu_of_reduced` consumes the reduced ledger fields (`hsrc0`, `bc/hbsum/hagree`, positivity/sup bounds, K2 compact gradient/Hessian bounds, K1 time-C¹ data, and `hLc`). It is **not** a theorem saying that the contraction fixed point alone implies `Hu`.

So the answer to the practical question is: without the spectral/coefficient datum/ledger, the mild contraction fixed point only gives the fixed-point equation. It does not fill `hregularize`/`LimitRegularityInputs`.

## 3. The χ₀<0 resolver-data theorem exists

Yes, the repo has the theorem in `ShenWork/Paper2/IntervalDomainThm11ChiNegResidual.lean`:

```lean
import ShenWork.Paper2.IntervalDomainThm11ChiNegResidual

open ShenWork.Paper2.ChiNegResidual

#check coupledFluxClassicalLocalExistenceResidual_of_resolverAnalyticData
```

Its statement is:

```lean
import ShenWork.Paper2.IntervalDomainThm11ChiNegResidual

open ShenWork.Paper2.ChiNegResidual

-- theorem coupledFluxClassicalLocalExistenceResidual_of_resolverAnalyticData
--     (p : CM2Params) (hα : 1 ≤ p.α)
--     (H : CoupledFluxResolverAnalyticData p) :
--     CoupledFluxClassicalLocalExistenceResidual p
#check coupledFluxClassicalLocalExistenceResidual_of_resolverAnalyticData
```

The target residual is:

```lean
import ShenWork.Paper2.IntervalDomainThm11ChiNegResidual

open ShenWork.IntervalDomain
open ShenWork.Paper2.ChiNegResidual

-- def CoupledFluxClassicalLocalExistenceResidual (p : CM2Params) : Prop :=
--   ∀ M : ℝ, 0 < M → ∃ delta : ℝ, 0 < delta ∧
--     ∀ {u0 : intervalDomain.Point → ℝ},
--       PositiveInitialDatum intervalDomain u0 →
--       (∀ x, |u0 x| ≤ M) →
--         ∃ u v,
--           IsPaper2ClassicalSolution intervalDomain p delta u v ∧
--           InitialTrace intervalDomain u0 u
#check CoupledFluxClassicalLocalExistenceResidual
```

## 4. Exact contents of `CoupledFluxResolverAnalyticData`

`CoupledFluxResolverAnalyticData` is not a structure. It is a nested `Prop` with quantifiers and conjunctions. Definition read from `IntervalDomainThm11ChiNegResidual.lean`:

```lean
import ShenWork.Paper2.IntervalDomainThm11ChiNegResidual

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.PDE
open ShenWork.Paper2.ChiNegResidual

-- Current object:
#check CoupledFluxResolverAnalyticData

-- Full definition, as read:
-- def CoupledFluxResolverAnalyticData (p : CM2Params) : Prop :=
--   ∀ M : ℝ, 0 < M →
--     ∃ Mball : ℝ, 0 < Mball ∧ M ≤ Mball ∧
--       ∀ L : ℝ, 0 < L →
--         ∃ T A K : ℝ, 0 < T ∧ 0 < A ∧ 0 ≤ K ∧ A * T < 1 ∧
--           |p.χ₀| * K + L ≤ A ∧
--             ∀ {u0 : intervalDomain.Point → ℝ},
--               PositiveInitialDatum intervalDomain u0 →
--               (∀ x, |u0 x| ≤ M) →
--                 IntervalCoupledResolverBallEstimates p
--                   (intervalNeumannResolverR p) u0 T Mball K ∧
--                 ∀ u v : ℝ → intervalDomain.Point → ℝ,
--                   intervalTrajectoryBoundedOn T Mball u →
--                   (∀ t x, 0 ≤ t → t ≤ T →
--                     u t x = intervalCoupledDuhamelOperator p
--                       (intervalNeumannResolverR p) u0 u t x) →
--                   (∀ t, v t = intervalNeumannResolverR p (u t)) →
--                     RegularityBootstrap p T u0 u
```

Spelled out as “fields”:

* For every datum size `M > 0`, choose a fixed-point ball radius `Mball`.
* Prove `0 < Mball` and `M ≤ Mball`.
* For every positive logistic Lipschitz constant `L`, choose `T`, `A`, and `K`.
* Prove numeric constraints:
  * `0 < T`,
  * `0 < A`,
  * `0 ≤ K`,
  * `A * T < 1`,
  * `|p.χ₀| * K + L ≤ A`.
* For every positive initial datum `u0` with `|u0| ≤ M`, provide:
  * `IntervalCoupledResolverBallEstimates p (intervalNeumannResolverR p) u0 T Mball K`, and
  * for every `u v`, a regularization bridge:

```lean
import ShenWork.Paper2.IntervalDomainThm11ChiNegResidual

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.PDE
open ShenWork.Paper2.ChiNegResidual

-- This is the second datum-level conjunct inside CoupledFluxResolverAnalyticData:
--
-- ∀ u v : ℝ → intervalDomain.Point → ℝ,
--   intervalTrajectoryBoundedOn T Mball u →
--   (∀ t x, 0 ≤ t → t ≤ T →
--     u t x = intervalCoupledDuhamelOperator p
--       (intervalNeumannResolverR p) u0 u t x) →
--   (∀ t, v t = intervalNeumannResolverR p (u t)) →
--     RegularityBootstrap p T u0 u
#check RegularityBootstrap
```

The `IntervalCoupledResolverBallEstimates` conjunct itself is also a nested `Prop`, with four pieces:

```lean
import ShenWork.Paper2.IntervalDomainThm11ChiNegResidual

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.PDE

#check IntervalCoupledResolverBallEstimates

-- Conceptually, for IntervalCoupledResolverBallEstimates p R u₀ T M K:
--
-- (1) self-map bound:
--     any trajectory bounded by M on [0,T] is sent by the coupled Duhamel map
--     back into the M-ball.
--
-- (2) chemotaxis-divergence Lipschitz bound:
--     if u₁,u₂ are in the M-ball and differ by at most D, then
--     |chemDiv(u₁,Ru₁) - chemDiv(u₂,Ru₂)| ≤ K * D.
--
-- (3) time-integrability of the Duhamel integrand:
--     IntegrableOn in s over Set.Icc 0 t.
--
-- (4) lifted-source integrability:
--     Integrable (intervalDomainLift (intervalCoupledSource ...))
--     against intervalMeasure 1.
```

There is also a structural producer `IntervalCoupledResolverBallEstimatesProducer.produce` that assembles these four pieces from more primitive estimates: initial-data bound, source sup bound, chemDiv `K·D` Lipschitz, component sup bounds, and measurability of the semigroup integrand and lifted source. That producer **does not** prove the regularization bridge; it just packages the ball estimates.

## 5. Is `CoupledFluxResolverAnalyticData` easier to produce than `hregularize`?

No, not as a whole.

The key reason is that `CoupledFluxResolverAnalyticData` literally contains a regularization bridge of this shape:

```lean
import ShenWork.Paper2.IntervalDomainThm11ChiNegResidual

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.PDE
open ShenWork.Paper2.ChiNegResidual

-- The hregularize argument in exactLocalClassicalSolution_of_coupledDuhamel_resolver_estimates
-- has the same essential shape:
--
-- hregularize :
--   ∀ u v : ℝ → intervalDomainPoint → ℝ,
--     intervalTrajectoryBoundedOn T M u →
--     (∀ t x, 0 ≤ t → t ≤ T →
--       u t x = intervalCoupledDuhamelOperator p R u0 u t x) →
--     (∀ t, v t = R (u t)) →
--       RegularityBootstrap p T u0 u
#check exactLocalClassicalSolution_of_coupledDuhamel_resolver_estimates
```

And `RegularityBootstrap` itself is the classical/PDE payload:

```lean
import ShenWork.Paper2.IntervalDomainThm11ChiNegResidual

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.PDE

-- def RegularityBootstrap (p : CM2Params) (T : ℝ)
--     (u₀ : intervalDomainPoint → ℝ)
--     (u : ℝ → intervalDomainPoint → ℝ) : Prop :=
--   ∃ v : ℝ → intervalDomainPoint → ℝ,
--     (∀ t x, 0 < t → t < T → 0 < u t x) ∧
--     (∀ t x, 0 < t → t < T → 0 ≤ v t x) ∧
--     (∀ t x, 0 < t → t < T → x ∈ intervalDomain.inside →
--       intervalDomain.timeDeriv u t x =
--         intervalDomain.laplacian (u t) x
--           - p.χ₀ * intervalDomain.chemotaxisDiv p (u t) (v t) x
--           + u t x * (p.a - p.b * (u t x) ^ p.α)) ∧
--     (∀ t x, 0 < t → t < T → x ∈ intervalDomain.inside →
--       0 = intervalDomain.laplacian (v t) x
--         - p.μ * v t x + p.ν * (u t x) ^ p.γ) ∧
--     (∀ t x, 0 < t → t < T → x ∈ intervalDomain.boundary →
--       intervalDomain.normalDeriv (u t) x = 0 ∧
--       intervalDomain.normalDeriv (v t) x = 0) ∧
--     intervalDomainClassicalRegularity T u v ∧
--     InitialTrace intervalDomain u₀ u
#check RegularityBootstrap
```

Thus, `CoupledFluxResolverAnalyticData` is better understood as:

```text
uniform parameter choices
+ resolver self-map / chemDiv-Lipschitz / integrability estimates
+ hregularize-like RegularityBootstrap bridge
```

The first two parts are more modular than the χ₀=0 `LimitRegularityInputs` spectral restart ledger. But the last part is exactly the hard classical bootstrap/comparison/regularity content. Producing `CoupledFluxResolverAnalyticData` is therefore **not** a shortcut around `hregularize`; it is a wrapper that still asks for it, in a resolver-specialized form.

## Bottom line for the route decision

* χ₀=0 `LimitRegularityInputs`: enormous spectral/restart/classical ledger. Fixed point alone gives only `hfix`. `Hu` can be removed only after keeping the other heavy reduced-ledger fields.
* χ₀<0 `CoupledFluxResolverAnalyticData`: avoids the χ₀=0 cosine-restart ledger, but it still contains the core regularization bridge to `RegularityBootstrap`, plus resolver ball estimates and uniform constants.
* Therefore, if the target is “derive local classical existence from contraction alone,” neither route closes it. The χ₀<0 resolver-data route is cleaner as an interface, but it is not easier than `hregularize`; it includes `hregularize` as one of its required payloads.
