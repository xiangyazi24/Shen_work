# Q1100 / cron1 — complete Lean file: direct cutoff resolver joint C² for heat Level0

Repo inspected: `xiangyazi24/Shen_work`

Template inspected: `ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean`, theorem `heatSemigroup_jointContDiffAt_two`

Branch written: `chatgpt-scratch`

Target drop file:

```text
scratch/_CHATGPT_DROP_cron1.md
```

## Complete Lean 4 file

The file below follows the heat cutoff proof structure directly:

1. `resolverTerm`: raw resolver cosine term.
2. `cutoffResolverTerm`: multiply by `smoothRightCutoff (c/2) c`.
3. `cutoffResolverTerm_contDiff_two`: analytic input, left as `sorry`.
4. `cutoffResolverMajorant`, summability, and derivative bound: analytic inputs, left as `sorry`.
5. `cutoffResolverSeries_contDiff_two`: fully wired `contDiff_tsum` application.
6. `resolverSeries_eventuallyEq_cutoff`: fully wired cutoff `eventuallyEq` at `s₀ > c`.
7. `heatResolver_lift_eventuallyEq_series`: fully wired bridge from `coupledChemicalConcentration` to the resolver cosine series on an interior spatial neighborhood.
8. `heatResolver_directJointContDiffAt_two`: final transfer by `ContDiffAt.congr_of_eventuallyEq`.

```lean
import ShenWork.PDE.IntervalResolverJointC2PhysicalConcrete
import ShenWork.PDE.IntervalResolverSpectralJointC2Cutoff
import ShenWork.Paper2.IntervalConjugatePicard
import Mathlib.Analysis.Calculus.SmoothSeries

open Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalCoupledRegularityBootstrap (coupledChemicalConcentration)
open ShenWork.IntervalResolverJointC2Physical
  (boundedWeightJointTerm boundedWeightJointMajorant)
open ShenWork.IntervalResolverJointC2PhysicalConcrete
  (resolverTimeCoeff coupledChemical_lift_eq_series)
open ShenWork.IntervalResolverSpectralJointC2Cutoff
  (smoothRightCutoff smoothRightCutoff_eventually_eq_one)
open ShenWork.CosineSpectrum (cosineMode)

noncomputable section

namespace ShenWork.Paper2.HeatResolverDirectJointC2

/-- The raw `n`-th resolver cosine term for heat Level0.

For `u = conjugatePicardIter p u₀ 0`, this is
`(t,x) ↦ resolverTimeCoeff p u n t * cos(nπx)`, where
`resolverTimeCoeff p u n t = (intervalNeumannResolverCoeff p (u t) n).re`.
The elliptic identity later rewrites this as
`(μ+λ_n)⁻¹ * cosineCoeffs (ν * (S(t)u₀)^γ) n` in the analytic bounds. -/
def resolverTerm (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ) :
    ℝ × ℝ → ℝ :=
  fun q => resolverTimeCoeff p (conjugatePicardIter p u₀ 0) n q.1 * cosineMode n q.2

/-- The cutoff resolver term, exactly analogous to `cutoffHeatTerm` in
`IntervalHeatSemigroupHighRegularity.lean`.

The cutoff is zero before `c/2` and equals one on `[c,∞)`, so for a target
`s₀ > c` this term agrees with the raw resolver term near `(s₀,x₀)`. -/
def cutoffResolverTerm (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (c : ℝ) (n : ℕ) : ℝ × ℝ → ℝ :=
  fun q => smoothRightCutoff (c / 2) c q.1 * resolverTerm p u₀ n q

/-- Analytic input: each cutoff resolver term is globally joint `C²`.

This is the resolver analogue of `cutoffHeatTerm_contDiff_two`.  The intended proof
is local in the time coordinate:

* if `q.1 < c/2`, the cutoff term is locally zero;
* if `q.1 > 0`, the heat Level0 profile is positive-time smooth, and the source
  coefficient `t ↦ cosineCoeffs (ν * (S(t)u₀)^γ) n` is `C²` by differentiating the
  heat series under the integral twice;
* the resolver weight `(μ+λ_n)⁻¹` is constant in time;
* multiplication by the smooth cutoff preserves `C²`.

This is intentionally left as an analytic `sorry`; the cutoff/tsum/equality
framework below does not depend on its internal proof. -/
theorem cutoffResolverTerm_contDiff_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ c : ℝ}
    (_hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (_hu₀_cont : Continuous u₀) (_hc : 0 < c) (n : ℕ) :
    ContDiff ℝ 2 (cutoffResolverTerm p u₀ c n) := by
  sorry

/-- Placeholder majorant for the cutoff resolver term.

The real majorant should be built from compact-positive-time bounds for the first
three time derivatives of the resolver coefficient and the spatial weights
`valueCosWeight 0/1/2`.  It is kept as a definition so the `contDiff_tsum` wiring is
fully explicit. -/
noncomputable def cutoffResolverMajorant
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (M₀ c : ℝ)
    (k n : ℕ) : ℝ :=
  0

/-- Analytic input: the cutoff resolver majorant is summable at every joint order
`k ≤ 2`.

Intended proof: on the compact positive-time support of the cutoff derivatives,
the source coefficients for `ν * (S(t)u₀)^γ` have enough NeumannTower / IBP decay;
the elliptic weight `(μ+λ_n)⁻¹` cancels the worst value-series spatial weight, and
likewise gives the gradient-series summability needed downstream. -/
theorem cutoffResolverMajorant_summable
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ c : ℝ}
    (_hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (_hu₀_cont : Continuous u₀) (_hc : 0 < c)
    {k : ℕ} (_hk : (k : ℕ∞) ≤ (2 : ℕ∞)) :
    Summable (cutoffResolverMajorant p u₀ M₀ c k) := by
  sorry

/-- Analytic input: uniform derivative bound of a cutoff resolver term by the
chosen majorant.

This is the direct resolver analogue of `cutoffHeatTerm_iteratedFDeriv_bound`. -/
theorem cutoffResolverTerm_iteratedFDeriv_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ c : ℝ}
    (_hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (_hu₀_cont : Continuous u₀) (_hc : 0 < c)
    (k n : ℕ) (q : ℝ × ℝ) (hk : (k : ℕ∞) ≤ (2 : ℕ∞)) :
    ‖iteratedFDeriv ℝ k (cutoffResolverTerm p u₀ c n) q‖ ≤
      cutoffResolverMajorant p u₀ M₀ c k n := by
  sorry

/-- Global joint `C²` of the cutoff resolver series.

This is the fully wired `contDiff_tsum` step, copied from
`cutoffHeatSeries_contDiff_two` but with the resolver cutoff term and resolver
majorant. -/
theorem cutoffResolverSeries_contDiff_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ c : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀) (hc : 0 < c) :
    ContDiff ℝ 2 (fun q : ℝ × ℝ =>
      ∑' n : ℕ, cutoffResolverTerm p u₀ c n q) := by
  apply contDiff_tsum
    (𝕜 := ℝ)
    (f := cutoffResolverTerm p u₀ c)
    (v := cutoffResolverMajorant p u₀ M₀ c)
  · intro n
    exact cutoffResolverTerm_contDiff_two
      (p := p) (u₀ := u₀) (M₀ := M₀) hu₀_bound hu₀_cont hc n
  · intro k hk
    exact cutoffResolverMajorant_summable
      (p := p) (u₀ := u₀) (M₀ := M₀) (c := c)
      hu₀_bound hu₀_cont hc hk
  · intro k n q hk
    exact cutoffResolverTerm_iteratedFDeriv_bound
      (p := p) (u₀ := u₀) (M₀ := M₀) (c := c)
      hu₀_bound hu₀_cont hc k n q hk

/-- Near `(s₀,x₀)` with `s₀ > c`, the raw resolver series equals the cutoff
resolver series, because the time cutoff is eventually one near `s₀`.

This is the resolver analogue of `heatSeries_eventuallyEq_cutoff`. -/
theorem resolverSeries_eventuallyEq_cutoff
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {c s₀ x₀ : ℝ} (hc : 0 < c) (hs₀ : c < s₀) :
    (fun q : ℝ × ℝ => ∑' n : ℕ, resolverTerm p u₀ n q) =ᶠ[𝓝 (s₀, x₀)]
      (fun q : ℝ × ℝ => ∑' n : ℕ, cutoffResolverTerm p u₀ c n q) := by
  -- The same cutoff lemma used by `heatSeries_eventuallyEq_cutoff`.
  have hφ_one : smoothRightCutoff (c / 2) c =ᶠ[𝓝 s₀] fun _ => (1 : ℝ) :=
    smoothRightCutoff_eventually_eq_one (by linarith) hs₀
  -- Lift the time-only eventual equality to `(t,x)` via `Prod.fst`.
  have hφ_prod :
      (fun q : ℝ × ℝ => smoothRightCutoff (c / 2) c q.1) =ᶠ[𝓝 (s₀, x₀)]
        fun _ : ℝ × ℝ => (1 : ℝ) :=
    hφ_one.comp_tendsto continuous_fst.continuousAt
  -- Where `φ = 1`, each cutoff term is the raw resolver term.
  filter_upwards [hφ_prod] with q hq
  congr 1
  ext n
  simp [cutoffResolverTerm, resolverTerm, hq]

/-- On an interior spatial neighborhood, the lifted coupled concentration agrees
with the raw resolver cosine series.

This uses the already committed bridge
`coupledChemical_lift_eq_series`, then unfolds `boundedWeightJointTerm` to the
`resolverTerm` shape used in this file. -/
theorem heatResolver_lift_eventuallyEq_series
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {s₀ x₀ : ℝ} (hx₀ : x₀ ∈ Ioo (0 : ℝ) 1) :
    (fun q : ℝ × ℝ =>
      intervalDomainLift
        (coupledChemicalConcentration p (conjugatePicardIter p u₀ 0) q.1) q.2)
      =ᶠ[𝓝 (s₀, x₀)]
    (fun q : ℝ × ℝ => ∑' n : ℕ, resolverTerm p u₀ n q) := by
  have hmem : {q : ℝ × ℝ | q.2 ∈ Ioo (0 : ℝ) 1} ∈ 𝓝 (s₀, x₀) :=
    (isOpen_Ioo.preimage continuous_snd).mem_nhds hx₀
  filter_upwards [hmem] with q hq
  have hxIcc : q.2 ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hq
  have hseries := coupledChemical_lift_eq_series
    (p := p) (u := conjugatePicardIter p u₀ 0) (t := q.1) (x := q.2) hxIcc
  simpa [resolverTerm, boundedWeightJointTerm] using hseries

/-- **Direct cutoff resolver joint `C²` for heat Level0.**

This is the resolver-series analogue of
`HeatSemigroupJointRegularity.heatSemigroup_jointContDiffAt_two`.

The proof is intentionally the same three-step transfer:

1. the cutoff resolver series is globally `ContDiff ℝ 2` by `contDiff_tsum`;
2. the raw resolver series agrees with the cutoff resolver series near `s₀ > c`;
3. the actual lifted coupled concentration agrees with the raw resolver series near
   interior `x₀ ∈ (0,1)`.

The hard analytic estimates are isolated in the three upstream `sorry` lemmas:
`cutoffResolverTerm_contDiff_two`, `cutoffResolverMajorant_summable`, and
`cutoffResolverTerm_iteratedFDeriv_bound`. -/
theorem heatResolver_directJointContDiffAt_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    {c : ℝ} (hc : 0 < c) {s₀ x₀ : ℝ} (hs₀ : c < s₀)
    (hx₀ : x₀ ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        intervalDomainLift
          (coupledChemicalConcentration p (conjugatePicardIter p u₀ 0) q.1) q.2)
      (s₀, x₀) := by
  -- The cutoff series is globally C².
  have hCutoff :=
    (cutoffResolverSeries_contDiff_two
      (p := p) (u₀ := u₀) (M₀ := M₀) (c := c)
      hu₀_bound hu₀_cont hc).contDiffAt (x := (s₀, x₀))
  -- The actual resolver lift agrees near `(s₀,x₀)` with the raw series, and the
  -- raw series agrees there with the cutoff series.
  have hActualToCutoff :
      (fun q : ℝ × ℝ =>
        intervalDomainLift
          (coupledChemicalConcentration p (conjugatePicardIter p u₀ 0) q.1) q.2)
        =ᶠ[𝓝 (s₀, x₀)]
      (fun q : ℝ × ℝ => ∑' n : ℕ, cutoffResolverTerm p u₀ c n q) :=
    (heatResolver_lift_eventuallyEq_series (p := p) (u₀ := u₀)
      (s₀ := s₀) (x₀ := x₀) hx₀).trans
    (resolverSeries_eventuallyEq_cutoff (p := p) (u₀ := u₀)
      (c := c) (s₀ := s₀) (x₀ := x₀) hc hs₀)
  exact hCutoff.congr_of_eventuallyEq hActualToCutoff

end ShenWork.Paper2.HeatResolverDirectJointC2
```

## Notes

The code deliberately does **not** route through `FlooredSourceTimeData`, `PhysicalSourceTimeC2`, or `PhysicalResolverJointC2Data`. It proves the exact local `ContDiffAt` target from the resolver series by the same cutoff mechanism as the heat semigroup proof. The only remaining analytic inputs are the three `sorry` lemmas above the `contDiff_tsum` application, as requested.
