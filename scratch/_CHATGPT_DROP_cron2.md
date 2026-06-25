# Q328 (cron2): logistic source `DuhamelSourceTimeC1On` for `realSlice u_star`

## Executive answer

Yes: the repo has the **right general coefficient-Leibniz lemmas** to produce the logistic `hderiv`/`hadotcont` on a closed time window without first producing a global `DuhamelSourceTimeC1`.

The most relevant theorem is the windowed one:

```lean
ShenWork.IntervalMildPicardRegularityEndpoint2.cosineCoeffs_hasDerivWithinAt_of_smooth_param
```

It gives exactly the shape needed for a `DuhamelSourceTimeC1On` constructor:

```lean
HasDerivWithinAt
  (fun s => cosineCoeffs (f s) n)
  (cosineCoeffs (f' σ) n)
  (Set.Icc a' W) σ
```

from:

```lean
hf_cont      : ∀ s ∈ Set.Icc a' W, ContinuousOn (f s) (Set.Icc 0 1)
h_diff       : ∀ x ∈ Set.Ioo 0 1, ∀ s ∈ Set.Icc a' W,
                 HasDerivAt / HasDerivWithinAt of s ↦ f s x
h_cont_deriv : ContinuousOn (Function.uncurry f')
                 (Set.Icc a' W ×ˢ Set.Icc 0 1)
```

There is also an older/global local-neighborhood version:

```lean
ShenWork.IntervalMildPicardRegularity.cosineCoeffs_hasDerivAt_of_smooth_param
```

which gives global `HasDerivAt` at a point from a local slab, but for your new target the `Endpoint2` closed-window theorem is the better match.

So the answer to the core question is:

```text
The logistic hderiv/hadotcont can be produced without global DuhamelSourceTimeC1.
Use the windowed coefficient-Leibniz theorem plus pointwise logistic chain rule and joint continuity of the derivative field.
```

The remaining burden is not global source `TimeC1`; it is the usual local/window data for `realSlice u_star`: positivity, profile joint continuity, a time-derivative field for `realSlice`, and a uniform derivative-coefficient bound `Mdot`.

## Exact target family

Your target is:

```lean
DuhamelSourceTimeC1On
  (coupledLogisticSourceCoeffs p (realSlice u_star)) 0 T
```

The relevant definitions identify this family with the `logisticLifted` family used by the windowed constructors.

```lean
-- from ShenWork/PDE/IntervalCoupledSourceTimeC1.lean
/-- Lifted logistic source. -/
def coupledLogisticSourceLift (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (s : ℝ) : ℝ → ℝ :=
  intervalDomainLift
    (ShenWork.IntervalDomainExistence.intervalLogisticSource p (u s))

/-- Cosine coefficients of the logistic source. -/
def coupledLogisticSourceCoeffs (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) : ℝ → ℕ → ℝ :=
  fun s n => cosineCoeffs (coupledLogisticSourceLift p u s) n

-- from ShenWork/Paper2/IntervalGradientDuhamelMap.lean
/-- The lifted logistic source `L(w) = lift(w·(a − b·w^α))`. -/
def logisticLifted (p : CM2Params) (w : intervalDomainPoint → ℝ) : ℝ → ℝ :=
  intervalDomainLift (intervalLogisticSource p w)
```

Thus this rewrite should be a `simpa`/`rfl`-level bridge:

```lean
coupledLogisticSourceCoeffs p u
  = fun s k => cosineCoeffs (logisticLifted p (u s)) k
```

up to namespace unfolding.

## Windowed constructor already in the repo

The theorem you named is exactly the windowed logistic constructor:

```lean
noncomputable def limitSource_duhamelSourceTimeC1On_of_representation
    (p : CM2Params)
    (w : ℝ → intervalDomainPoint → ℝ)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    {lo hi M G1 G2 : ℝ}
    (hlohi : lo ≤ hi)
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ ∈ Set.Icc lo hi,
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagree : ∀ σ ∈ Set.Icc lo hi, Set.EqOn (intervalDomainLift (w σ))
        (fun x => ∑' n, bc σ n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    (hpos : ∀ σ ∈ Set.Icc lo hi,
      ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (w σ) x)
    (hub : ∀ σ ∈ Set.Icc lo hi,
      ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (w σ) x ≤ M)
    (hG1 : ∀ σ ∈ Set.Icc lo hi,
      ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (intervalDomainLift (w σ)) x| ≤ G1)
    (hG2 : ∀ σ ∈ Set.Icc lo hi,
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (deriv (intervalDomainLift (w σ))) x| ≤ G2)
    (adot : ℝ → ℕ → ℝ)
    (hderiv : ∀ σ ∈ Set.Icc lo hi, ∀ k, HasDerivWithinAt
      (fun r => cosineCoeffs
        (logisticSourceFun p.a p.b p.α (intervalDomainLift (w r))) k)
      (adot σ k) (Set.Icc lo hi) σ)
    (hadotcont : ∀ k, ContinuousOn (fun σ => adot σ k) (Set.Icc lo hi))
    {Mdot : ℝ}
    (hMdot : ∀ σ ∈ Set.Icc lo hi, ∀ k, |adot σ k| ≤ Mdot) :
    DuhamelSourceTimeC1On
      (fun s k => cosineCoeffs (logisticLifted p (w s)) k) lo hi
```

It builds the value envelope from the representation data and forwards the time-derivative fields:

```lean
{ adot := adot
  hderiv := hderiv
  hadotcont := hadotcont
  envelope := fun n => if n = 0 then C else C / ((n : ℝ) * Real.pi) ^ 2
  henv_summable := ...
  henv_bound := ...
  derivBound := Mdot
  hderivBound := hMdot }
```

So if you instantiate:

```lean
w  := realSlice u_star
lo := 0
hi := T
```

and provide the representation/bounds and derivative fields on `[0,T]`, its output should reduce to your desired target by unfolding `coupledLogisticSourceCoeffs`/`coupledLogisticSourceLift`/`logisticLifted`.

## General coefficient-Leibniz theorem: global/local version

The repo has this general local-neighborhood theorem:

```lean
-- ShenWork/Paper2/IntervalMildPicardRegularity.lean
namespace ShenWork.IntervalMildPicardRegularity

theorem cosineCoeffs_hasDerivAt_of_smooth_param
    {f f' : ℝ → ℝ → ℝ} {τ δ : ℝ} {n : ℕ} (hδ : 0 < δ)
    (hf_cont : ∀ᶠ s in 𝓝 τ, ContinuousOn (f s) (Set.Icc (0 : ℝ) 1))
    (h_diff : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      ∀ s ∈ Metric.ball τ δ,
        HasDerivAt (fun r => f r x) (f' s x) s)
    (h_cont_deriv : ContinuousOn (Function.uncurry f')
      (Set.Icc (τ - δ) (τ + δ) ×ˢ Set.Icc (0 : ℝ) 1)) :
    HasDerivAt (fun s => cosineCoeffs (f s) n)
      (cosineCoeffs (f' τ) n) τ
```

This is useful if you already have a local open slab around a point and want a full `HasDerivAt`.

## General coefficient-Leibniz theorem: closed-window version

For `DuhamelSourceTimeC1On`, use this theorem instead:

```lean
-- ShenWork/Paper2/IntervalMildPicardRegularityEndpoint2.lean
namespace ShenWork.IntervalMildPicardRegularityEndpoint2

/-- One-sided closed-window time-Leibniz rule for cosine coefficients. -/
theorem cosineCoeffs_hasDerivWithinAt_of_smooth_param
    {f f' : ℝ → ℝ → ℝ} {a' W : ℝ} {n : ℕ} (ha'W : a' ≤ W)
    {σ : ℝ} (hσ : σ ∈ Set.Icc a' W)
    (hf_cont : ∀ s ∈ Set.Icc a' W,
      ContinuousOn (f s) (Set.Icc (0 : ℝ) 1))
    (h_diff : ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ s ∈ Set.Icc a' W,
      HasDerivWithinAt (fun r => f r x) (f' s x) (Set.Icc a' W) s)
    (h_cont_deriv : ContinuousOn (Function.uncurry f')
      (Set.Icc a' W ×ˢ Set.Icc (0 : ℝ) 1)) :
    HasDerivWithinAt (fun s => cosineCoeffs (f s) n)
      (cosineCoeffs (f' σ) n) (Set.Icc a' W) σ
```

There is also a sibling with `{lo hi τ}` in `IntervalMildPicardRegularityEndpoint.lean`:

```lean
theorem cosineCoeffs_hasDerivWithinAt_of_smooth_param
    {f f' : ℝ → ℝ → ℝ} {lo hi τ : ℝ} {n : ℕ} (_hlohi : lo ≤ hi)
    (hτ : τ ∈ Set.Icc lo hi)
    (hf_cont : ∀ s ∈ Set.Icc lo hi,
      ContinuousOn (f s) (Set.Icc (0 : ℝ) 1))
    (h_diff : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ∀ s ∈ Set.Icc lo hi,
        HasDerivWithinAt (fun r => f r x) (f' s x) (Set.Icc lo hi) s)
    (h_cont_deriv : ContinuousOn (Function.uncurry f')
      (Set.Icc lo hi ×ˢ Set.Icc (0 : ℝ) 1)) :
    HasDerivWithinAt (fun s => cosineCoeffs (f s) n)
      (cosineCoeffs (f' τ) n) (Set.Icc lo hi) τ
```

Either form is suitable; `Endpoint2` is the one used by the restart-window logistic theorem.

## Logistic pointwise chain rule

The scalar/global lemma is:

```lean
-- ShenWork/Paper2/IntervalMildPicardRegularity.lean
namespace ShenWork.IntervalMildPicardRegularity

theorem logisticSourceFun_hasDerivAt_time
    {a b α : ℝ} (_hα : 0 < α)
    {f : ℝ → ℝ} {f' σ : ℝ}
    (hf_pos : 0 < f σ)
    (hf_deriv : HasDerivAt f f' σ) :
    HasDerivAt (fun r => f r * (a - b * (f r) ^ α))
      (f' * (a - b * (1 + α) * (f σ) ^ α)) σ
```

For the closed-window route, the repo uses the windowed/within version inside:

```lean
-- ShenWork/Paper2/IntervalPicardIterateTimeC1EndpointAdot.lean
theorem logisticSource_adot_hasDerivWithinAt_endpoint_window
    {p : CM2Params} (hα : 0 < p.α)
    {w : ℝ → intervalDomainPoint → ℝ}
    {a₀ : ℕ → ℝ} {M₀ : ℝ} (hM₀ : 0 ≤ M₀) (ha₀ : ∀ n, |a₀ n| ≤ M₀)
    {a : ℝ → ℕ → ℝ} {offset W lo hi aτ σ : ℝ}
    (src : DuhamelSourceTimeC1On a 0 W)
    (haτpos : 0 < aτ) (hσ : σ ∈ Set.Icc lo hi)
    (hshift : Set.MapsTo (fun s : ℝ => s - offset)
      (Set.Icc lo hi) (Set.Icc aτ W))
    (hagree : ∀ s ∈ Set.Icc lo hi, ∀ x : intervalDomainPoint,
      intervalDomainLift (w s) x.1 =
        ∑' n, localRestartCoeff a₀ a (s - offset) n * cosineMode n x.1)
    (hpos : ∀ s ∈ Set.Icc lo hi, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (w s) x)
    (hC2cont : ∀ s ∈ Set.Icc lo hi,
      ContinuousOn (intervalDomainLift (w s)) (Set.Icc (0 : ℝ) 1))
    (hprofile_joint : ContinuousOn
      (Function.uncurry (fun s x => intervalDomainLift (w s) x))
      (Set.Icc lo hi ×ˢ Set.Icc (0 : ℝ) 1))
    (k : ℕ) :
    HasDerivWithinAt
      (fun r => cosineCoeffs
        (logisticSourceFun p.a p.b p.α (intervalDomainLift (w r))) k)
      (cosineCoeffs (fun x => logisticSourceDot a₀ a p w offset σ x) k)
      (Set.Icc lo hi) σ
```

This theorem is already a specialized production of `hderiv` for logistic coefficients. It does **not** assume global `DuhamelSourceTimeC1`; it assumes a predecessor window source package and a restart representation.

## Existing packaged recursion theorem

The repo has a higher-level packaged theorem that already combines the hderiv/hadotcont/Mdot pieces for a successor logistic source:

```lean
-- ShenWork/Paper2/IntervalPicardSourceTimeC1OnRecursion.lean
namespace ShenWork.IntervalPicardSourceTimeC1OnRecursion

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

Inside, it defines:

```lean
let adot : ℝ → ℕ → ℝ :=
  fun σ k => cosineCoeffs (fun x => logisticSourceDot a₀ a p w offset σ x) k
```

then obtains `Mdot` from:

```lean
exists_logisticSource_adot_bound_On_shift
```

and supplies `hderiv` via:

```lean
logisticSource_adot_hasDerivWithinAt_endpoint_window
```

and supplies `hadotcont` via:

```lean
cosineCoeffs_continuousOn_of_jointContinuousOn_Icc
```

applied to the joint-continuity theorem for `logisticSourceDot`.

So this theorem is a ready-made route if your `realSlice u_star` is represented in the same restart form on `[0,T]`.

## Mdot producer

The Mdot producer is:

```lean
theorem exists_logisticSource_adot_bound_On_shift
    {p : CM2Params}
    {w : ℝ → intervalDomainPoint → ℝ}
    {a₀ : ℕ → ℝ} {M₀ : ℝ} (hM₀ : 0 ≤ M₀)
    (ha₀ : ∀ n, |a₀ n| ≤ M₀)
    {a : ℝ → ℕ → ℝ} {offset W lo hi aτ : ℝ}
    (src : DuhamelSourceTimeC1On a 0 W)
    (haτpos : 0 < aτ)
    (hshift : Set.MapsTo (fun s : ℝ => s - offset)
      (Set.Icc lo hi) (Set.Icc aτ W))
    (hpos : ∀ s ∈ Set.Icc lo hi, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (w s) x)
    (hprofile_joint : ContinuousOn
      (Function.uncurry (fun s x => intervalDomainLift (w s) x))
      (Set.Icc lo hi ×ˢ Set.Icc (0 : ℝ) 1)) :
    ∃ Mdot : ℝ, ∀ σ ∈ Set.Icc lo hi, ∀ k,
      |cosineCoeffs (fun x => logisticSourceDot a₀ a p w offset σ x) k|
        ≤ Mdot
```

It works by proving joint continuity of the derivative field on the compact window and then applying the general bound for cosine coefficients of a continuous bounded function.

## Minimal direct route for `realSlice u_star`

If you do **not** want to use the restart recursion theorem, the direct proof should look like this:

```lean
import ShenWork.Paper2.IntervalDomainLimitSourceRepresentationOn
import ShenWork.Paper2.IntervalMildPicardRegularityEndpoint2
import ShenWork.PDE.IntervalDuhamelSourceTimeC1On
import ShenWork.Wiener.EWA.SourceClassicalExistence

open Set
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalMildPicardRegularity (logisticSourceFun)
open ShenWork.IntervalMildPicardRegularityEndpoint2
open ShenWork.IntervalDomainLimitSourceRepresentationOn
open ShenWork.IntervalDuhamelSourceTimeC1On

noncomputable section

namespace ShenWork.EWA

-- Suggested shape only; names of `uDot`/`adot` can be adjusted.
theorem logistic_timeC1On_realSlice_of_window_data
    {T : ℝ} (p : CM2Params) (u_star : EWA T 1)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    {M G1 G2 : ℝ}
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ ∈ Set.Icc (0 : ℝ) T,
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagree : ∀ σ ∈ Set.Icc (0 : ℝ) T,
      Set.EqOn (intervalDomainLift (realSlice u_star σ))
        (fun x => ∑' n, bc σ n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1))
    (hpos : ∀ σ ∈ Set.Icc (0 : ℝ) T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (realSlice u_star σ) x)
    (hub : ∀ σ ∈ Set.Icc (0 : ℝ) T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (realSlice u_star σ) x ≤ M)
    (hG1 : ∀ σ ∈ Set.Icc (0 : ℝ) T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (realSlice u_star σ)) x| ≤ G1)
    (hG2 : ∀ σ ∈ Set.Icc (0 : ℝ) T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv (intervalDomainLift (realSlice u_star σ))) x| ≤ G2)
    (adot : ℝ → ℕ → ℝ)
    (hderiv : ∀ σ ∈ Set.Icc (0 : ℝ) T, ∀ k,
      HasDerivWithinAt
        (fun r => cosineCoeffs
          (logisticSourceFun p.a p.b p.α
            (intervalDomainLift (realSlice u_star r))) k)
        (adot σ k) (Set.Icc (0 : ℝ) T) σ)
    (hadotcont : ∀ k, ContinuousOn (fun σ => adot σ k) (Set.Icc (0 : ℝ) T))
    {Mdot : ℝ}
    (hMdot : ∀ σ ∈ Set.Icc (0 : ℝ) T, ∀ k, |adot σ k| ≤ Mdot) :
    DuhamelSourceTimeC1On
      (coupledLogisticSourceCoeffs p (realSlice u_star)) 0 T := by
  have H : DuhamelSourceTimeC1On
      (fun s k => cosineCoeffs (logisticLifted p (realSlice u_star s)) k) 0 T :=
    limitSource_duhamelSourceTimeC1On_of_representation
      p (realSlice u_star) hα ha hb (show (0 : ℝ) ≤ T from by
        -- supply/derive this from the window assumptions in the real theorem
        sorry)
      bc hbsum hagree hpos hub hG1 hG2 adot hderiv hadotcont hMdot
  -- The family is definitionally the same after unfolding the two lifted-source definitions.
  simpa [coupledLogisticSourceCoeffs, coupledLogisticSourceLift, logisticLifted] using H

end ShenWork.EWA
```

This direct wrapper shows the key point: `limitSource_duhamelSourceTimeC1On_of_representation` does not need global `DuhamelSourceTimeC1`; it needs the local `hderiv`, `hadotcont`, and `hMdot` on `[0,T]`.

## How to produce `hderiv` directly

Use the closed-window coefficient-Leibniz theorem with:

```lean
f  := fun s x => logisticSourceFun p.a p.b p.α
        (intervalDomainLift (realSlice u_star s)) x

f' := fun s x =>
        u_t(s,x) * (p.a - p.b * (1 + p.α) *
          (intervalDomainLift (realSlice u_star s) x) ^ p.α)
```

Then prove:

```lean
hf_cont : ∀ s ∈ Set.Icc 0 T, ContinuousOn (f s) (Set.Icc 0 1)
h_diff  : ∀ x ∈ Set.Ioo 0 1, ∀ s ∈ Set.Icc 0 T,
  HasDerivWithinAt (fun r => f r x) (f' s x) (Set.Icc 0 T) s
h_cont_deriv : ContinuousOn (Function.uncurry f')
  (Set.Icc 0 T ×ˢ Set.Icc 0 1)
```

The pointwise `h_diff` is just the logistic chain rule plus the time derivative of `realSlice`. The continuity `h_cont_deriv` is product/rpow continuity using positivity of `realSlice`.

## How to produce `hadotcont`

After defining:

```lean
adot σ k := cosineCoeffs (f' σ) k
```

use the existing compact dominated-continuity lemma:

```lean
cosineCoeffs_continuousOn_of_jointContinuousOn_Icc
```

This is exactly what `sourceTimeC1On_succ_of_sourceTimeC1On` does after proving joint continuity of `logisticSourceDot`.

## Bottom line

The repo already has the correct general machinery. For the logistic source, you do **not** need to manufacture a global `DuhamelSourceTimeC1` first.

Use one of two routes:

1. **Direct route:** instantiate `IntervalMildPicardRegularityEndpoint2.cosineCoeffs_hasDerivWithinAt_of_smooth_param` with the pointwise logistic derivative field of `realSlice`, then feed `limitSource_duhamelSourceTimeC1On_of_representation`.

2. **Existing restart route:** use `sourceTimeC1On_succ_of_sourceTimeC1On`, which already packages `hderiv`, `hadotcont`, and `Mdot` via `logisticSource_adot_hasDerivWithinAt_endpoint_window`, `cosineCoeffs_continuousOn_of_jointContinuousOn_Icc`, and `exists_logisticSource_adot_bound_On_shift`.

For `realSlice u_star`, the missing theorem is not a coefficient-Leibniz theorem. It is the window data that lets you instantiate that theorem: a `[0,T]` representation/bounds for `realSlice`, positivity, joint continuity of the field and its time derivative, and a uniform `Mdot` bound. The source time-C¹ part itself is window-local and does not require a global source package.
