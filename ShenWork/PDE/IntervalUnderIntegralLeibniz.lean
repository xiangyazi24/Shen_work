/-
  ShenWork/PDE/IntervalUnderIntegralLeibniz.lean

  A *localized* under-integral time-Leibniz lemma for the unit interval `[0,1]`.

  Both remaining spatial-integral-in-time obligations of the Paper2 interval
  uniqueness/coefficient machinery have the same shape

      d/dτ ∫₀¹ g τ x dx  =  ∫₀¹ (∂_τ g) τ x dx,

  namely

  * **E (energy):**      `g τ x = (u₁ τ x − u₂ τ x)²`, so
                         `d/dτ ∫₀¹ w² = ∫₀¹ 2 w ∂_τ w`  (`w = u₁ − u₂`);
  * **B (coeff ODE):**   `g τ x = cos(nπx) · u(τ,x)`, so
                         `d/ds ⟨u s, eₙ⟩ = ⟨∂_s u s, eₙ⟩`.

  Both previously stalled because the *global* application of Mathlib's
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le` was set up on the FIXED
  ball `Metric.ball τ 1`
  (see `IntervalDomainLpMonotonicity.intervalDomain_intervalIntegral_hasDerivAt_of_dominated_deriv_le`),
  which extends *outside* `(0,T)` where the classical solution is no longer
  known to be regular (the artificial "D1-ball" obstruction).

  The fix implemented here is the LOCALIZATION suggested by the energy method:
  run the same Mathlib lemma on a *small* ball `Metric.ball τ δ` chosen so that
  the closed interval `[τ−δ, τ+δ] ⊆ (0,T)`.  On such a ball **every** time
  `s ∈ Metric.ball τ δ` is an interior time, so the per-`x`/per-`t`
  differentiability conjunct of `intervalDomainClassicalRegularity` (conjunct
  `.2.2.2.1`, the *interior time-differentiability* conjunct) supplies the
  Leibniz hypothesis (D1) at every point of the ball — not merely at `τ`.

  This file states the reusable lemma `intervalIntegral_hasDerivAt_time_of_local`,
  whose hypotheses are exactly what one can genuinely produce:

  * (D1) per-`x` time-`HasDerivAt` for *all* `s ∈ Metric.ball τ δ`
         — from conjunct `.2.2.2.1` of `intervalDomainClassicalRegularity`,
           valid because `Metric.ball τ δ ⊆ Ioo 0 T`;
  * (D2) a τ-uniform integrable dominating envelope `bound` on `∂_τ g` over the
         same ball — see the §"Honest gap" note below for what supplies this and
         what does NOT.

  This file contains **no `sorry`, no `admit`, no custom `axiom`.**
-/
import ShenWork.Paper2.IntervalDomainLpMonotonicity

open MeasureTheory Filter Topology Set
open scoped Topology

noncomputable section

namespace ShenWork.IntervalUnderIntegralLeibniz

open ShenWork.Paper2.IntervalDomainLpMonotonicity

/-- **Localized under-integral time-Leibniz on `[0,1]`.**

For a family `g : ℝ → ℝ → ℝ` (time `τ`, space `x`) with

* (D1) per-`x` time differentiability on the whole ball `Metric.ball τ δ`
       (`h_diff`), with derivative `g'`;
* (D2) a single integrable envelope `bound` dominating `‖g' s y‖` for *all*
       `s ∈ Metric.ball τ δ` (`h_bound`, `hbound_int`);
* the usual measurability/integrability side conditions at the base point,

we get the genuine derivative of the spatial integral

    `d/dτ ∫₀¹ g τ x dx = ∫₀¹ g' τ x dx`.

The radius `δ` is *arbitrary positive*; the caller will pick `δ` small enough
that `Metric.ball τ δ ⊆ Ioo 0 T`, so that (D1) follows pointwise from the
interior-time-differentiability conjunct of `intervalDomainClassicalRegularity`.

This is just a thin renaming of
`intervalDomain_intervalIntegral_hasDerivAt_of_dominated_deriv_le` with the
ball radius made an explicit positive parameter `δ` (the original hard-codes
`δ = 1`).  The localization is what lets the caller stay inside `(0,T)`. -/
theorem intervalIntegral_hasDerivAt_time_of_local
    {g g' : ℝ → ℝ → ℝ} {bound : ℝ → ℝ} {τ δ : ℝ} (hδ : 0 < δ)
    (hF_meas :
      ∀ᶠ s in 𝓝 τ,
        AEStronglyMeasurable (g s) intervalDomainInteriorMeasure)
    (hF_int : IntervalIntegrable (g τ) volume 0 1)
    (hF'_meas :
      AEStronglyMeasurable (g' τ) intervalDomainInteriorMeasure)
    (h_bound :
      ∀ᵐ y ∂intervalDomainInteriorMeasure,
        ∀ s ∈ Metric.ball τ δ, ‖g' s y‖ ≤ bound y)
    (hbound_int : Integrable bound intervalDomainInteriorMeasure)
    (h_diff :
      ∀ᵐ y ∂intervalDomainInteriorMeasure,
        ∀ s ∈ Metric.ball τ δ, HasDerivAt (fun r => g r y) (g' s y) s) :
    HasDerivAt
      (fun s => ∫ y in (0 : ℝ)..1, g s y)
      (∫ y in (0 : ℝ)..1, g' τ y) τ := by
  -- Reduce to the finite-measure parametric-integral theorem on the interior
  -- measure (volume restricted to `Ioo 0 1`), exactly as in the `δ = 1`
  -- helper, but with `δ` an explicit positive radius.
  have hF_int_restrict :
      Integrable (g τ) intervalDomainInteriorMeasure := by
    have hIoc : Integrable
        (g τ) (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le
      (show (0 : ℝ) ≤ 1 by norm_num)).mp hF_int).integrable
    simpa [intervalDomainInteriorMeasure,
      MeasureTheory.restrict_Ioo_eq_restrict_Ioc] using hIoc
  have hmain :
      HasDerivAt
        (fun s => ∫ y, g s y ∂intervalDomainInteriorMeasure)
        (∫ y, g' τ y ∂intervalDomainInteriorMeasure) τ :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := intervalDomainInteriorMeasure)
      (bound := bound)
      (F := g)
      (F' := g')
      (x₀ := τ)
      (s := Metric.ball τ δ)
      (Metric.ball_mem_nhds τ hδ)
      hF_meas hF_int_restrict hF'_meas h_bound hbound_int h_diff).2
  simpa [intervalDomainInteriorMeasure,
    intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    MeasureTheory.restrict_Ioo_eq_restrict_Ioc] using hmain

/-- **Choosing a ball inside `(0,T)`.**  If `τ ∈ Ioo 0 T` then there is a
positive radius `δ` with `Metric.ball τ δ ⊆ Ioo 0 T`.  This is the geometric
fact that makes the localization work: on this ball, every time is an interior
time, so the `.2.2.2.1` differentiability conjunct of
`intervalDomainClassicalRegularity` applies at *every* `s` in the ball, giving
the (D1) hypothesis of `intervalIntegral_hasDerivAt_time_of_local`. -/
theorem exists_ball_subset_Ioo
    {τ T : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T) :
    ∃ δ : ℝ, 0 < δ ∧ Metric.ball τ δ ⊆ Set.Ioo (0 : ℝ) T := by
  have hopen : IsOpen (Set.Ioo (0 : ℝ) T) := isOpen_Ioo
  obtain ⟨δ, hδpos, hsub⟩ := Metric.isOpen_iff.mp hopen τ hτ
  exact ⟨δ, hδpos, hsub⟩

/-- **The (D2) envelope, from joint continuity of `∂ₜg` on a compact slab.**

Given the time-derivative field `g'` *jointly continuous* on the compact slab
`Set.Icc (τ−δ) (τ+δ) ×ˢ Set.Icc 0 1`, there is a single **constant** integrable
envelope `bound ≡ M` with `‖g' s y‖ ≤ bound y` for every `s ∈ Metric.ball τ δ`
and almost every `y` (the interior measure is supported in `Ioo 0 1 ⊆ Icc 0 1`).
A constant is `intervalDomainInteriorMeasure`-integrable because that measure is
finite (`volume.restrict (Ioo 0 1)`, total mass `1`).

This is the reusable lemma that supplies the `h_bound`/`hbound_int` hypotheses of
`intervalIntegral_hasDerivAt_time_of_local`: joint continuity on the compact
slab is exactly the genuine `C¹`-in-time (continuous `∂ₜu`) regularity that the
strengthened time conjunct of `intervalDomainClassicalRegularity` records. -/
theorem exists_bound_of_continuousOn_slab
    {g' : ℝ → ℝ → ℝ} {τ δ : ℝ} (hδ : 0 < δ)
    (hcont : ContinuousOn (Function.uncurry g')
      (Set.Icc (τ - δ) (τ + δ) ×ˢ Set.Icc (0 : ℝ) 1)) :
    ∃ bound : ℝ → ℝ,
      Integrable bound intervalDomainInteriorMeasure ∧
      (∀ᵐ y ∂intervalDomainInteriorMeasure,
        ∀ s ∈ Metric.ball τ δ, ‖g' s y‖ ≤ bound y) := by
  classical
  -- The slab is compact, so the continuous `‖∂ₜg‖` attains a finite bound `M`.
  have hcompact : IsCompact
      (Set.Icc (τ - δ) (τ + δ) ×ˢ Set.Icc (0 : ℝ) 1) :=
    (isCompact_Icc).prod isCompact_Icc
  obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuousOn hcont
  refine ⟨fun _ => M, ?_, ?_⟩
  · -- A constant is integrable for the finite interior measure.
    have : IsFiniteMeasure intervalDomainInteriorMeasure := by
      refine ⟨?_⟩
      simp [intervalDomainInteriorMeasure, MeasureTheory.Measure.restrict_apply,
        Real.volume_Ioo]
    exact integrable_const M
  · -- Almost every `y` lies in `Ioo 0 1 ⊆ Icc 0 1`; for `s ∈ ball τ δ ⊆
    -- Icc (τ−δ) (τ+δ)` the slab bound `M` applies.
    refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
    refine Filter.Eventually.of_forall (fun y hy s hs => ?_)
    have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hy
    have hsIcc : s ∈ Set.Icc (τ - δ) (τ + δ) := by
      rw [Metric.mem_ball, Real.dist_eq] at hs
      rw [Set.mem_Icc]
      constructor <;> [linarith [abs_lt.mp hs |>.1]; linarith [abs_lt.mp hs |>.2]]
    exact hM (s, y) (Set.mk_mem_prod hsIcc hyIcc)

/-!
## Honest gap report — what (D1) and (D2) require, and what supplies them

Let `g τ x` be the integrand (E: `(u₁ τ x − u₂ τ x)²`; B: `cos(nπx)·u(τ,x)`),
and write `g' s x = ∂_τ g s x` for its time-slice derivative.

### (D1) — time-slice differentiability on the whole ball — **SUPPLIED.**

For `τ ∈ Ioo 0 T`, pick `δ` from `exists_ball_subset_Ioo`, so
`Metric.ball τ δ ⊆ Ioo 0 T`.  For each interior spatial `x ∈ (0,1)` and each
`s ∈ Metric.ball τ δ ⊆ (0,T)`, conjunct `.2.2.2.1` of
`intervalDomainClassicalRegularity` (the *interior time-differentiability*
conjunct, `∀ x ∈ Ioo 0 1, ∀ t ∈ Ioo 0 T, DifferentiableAt ℝ (fun s => u s x) t`)
upgrades to `HasDerivAt (fun r => u r x) (timeDeriv u s x) s`
(this is `intervalDomain_timeDeriv_isGenuine` in
`IntervalDomainL2EnergyInequality.lean`).  For E, compose with the square chain
rule (`intervalDomain_difference_sq_hasDerivAt_time`); for B, multiply by the
`s`-constant weight `cos(nπx)`.  Endpoints `x ∈ {0,1}` form a `volume`-null set,
so the `∀ᵐ y ∂intervalDomainInteriorMeasure` quantifier ignores them.  This is
the localization payoff: the old global `Metric.ball τ 1` leaked outside `(0,T)`
where conjunct `.2.2.2.1` is silent, whereas `Metric.ball τ δ` does not.

### (D2) — τ-uniform integrable dominating envelope — **NOT supplied by the 5
conjuncts; needs joint continuity (genuine parabolic regularity).**

`intervalIntegral_hasDerivAt_time_of_local` requires a single integrable
`bound : ℝ → ℝ` with `‖g' s y‖ ≤ bound y` for *all* `s ∈ Metric.ball τ δ`.
The natural envelope is `bound y = sup_{s ∈ [τ−δ, τ+δ]} ‖g' s y‖`, which is
integrable on `[0,1]` provided `g'` is **bounded** on the compact slab
`[τ−δ, τ+δ] × [0,1]` (e.g. `g'` jointly continuous there ⇒ bounded ⇒ the
constant envelope `bound ≡ M` is `volume`-integrable on the finite interval).

The 5 conjuncts of `intervalDomainClassicalRegularity` give:
  * `.2.2.1`   — per-`t` *spatial* `C²` on `(0,1)` (no `t`-uniformity);
  * `.2.2.2.1` — per-`(x,t)` *pointwise* time `DifferentiableAt`
                 (no continuity/boundedness of `s ↦ g' s x`, no joint bound).

Neither yields boundedness of the *time-derivative field* `g'` over the slab.
The precise missing input is therefore a **joint space-time regularity /
boundedness** fact, NOT a missing Mathlib lemma:

> `∃ M, ∀ s ∈ [τ−δ, τ+δ], ∀ x ∈ [0,1], ‖∂_τ g s x‖ ≤ M`
>   (e.g. from `ContinuousOn (uncurry (∂_τ g)) ([τ−δ,τ+δ] ×ˢ [0,1])`).

This is exactly the obligation already isolated as
`IntervalDomainL2JointTimeRegularity p`
(see `ShenWork.Paper2.IntervalDomainL2FrontierBuilder`).  Once it is supplied,
`exists_ball_subset_Ioo` + `intervalIntegral_hasDerivAt_time_of_local` close
both E and B with no further Mathlib gap.

### Verdict

* The localization eliminates the **(D1)-ball** obstruction completely: the new
  lemma takes an arbitrary `δ > 0`, and `exists_ball_subset_Ioo` keeps the ball
  inside `(0,T)`, so the `.2.2.2.1` conjunct discharges (D1) on the whole ball.
* The **(D2)-envelope** obstruction is *not* a missing Mathlib lemma; Mathlib's
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le` is exactly the right tool
  and is used here.  What remains is a genuine *boundedness of `∂_τ g` on a
  compact time-slab*, i.e. joint parabolic regularity
  (`IntervalDomainL2JointTimeRegularity`), which the 5 regularity conjuncts do
  not contain.
-/

end ShenWork.IntervalUnderIntegralLeibniz

end
