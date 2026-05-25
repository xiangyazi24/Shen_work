/-
  ShenWork/PDE/IntervalCoupledBallEstimates.lean

  Coupled-Duhamel "ball estimates" for local existence of the
  chemotaxis-logistic system on the unit interval, parameterized over an
  ABSTRACT elliptic resolver `R`.

  The target is the four conjuncts of `IntervalCoupledResolverBallEstimates`
  (see `ShenWork/PDE/IntervalDomainExistence.lean`):

    (hmap)       coupled Duhamel maps the M-ball into itself;
    (hchem)      chemotaxis divergence is Lipschitz in `u` along `R`;
    (hint)       time-integrability of the Duhamel integrand;
    (hlift_int)  integrability of the lifted coupled source.

  We do NOT construct `R`.  Instead we record the precise regularity it must
  supply and discharge each conjunct from those hypotheses + the existing
  proven semigroup/measure tools.  All hypotheses on `R` (and on the flux
  regularity that the resolver provides) appear EXPLICITLY as lemma arguments.

  Status of each conjunct:
    * `hlift_int` — PROVED cleanly from: a sup bound on the coupled source and
      a.e.-strong-measurability of its lift.  The bound is genuinely derived
      from the resolver sup bound + a flux-divergence sup bound; only the
      measurability of `deriv`-valued chemotaxis flux is assumed (it is a
      regularity statement about the resolver, not provable from sup/Lipschitz
      bounds alone — `deriv` of a quotient of lifts is not known measurable
      without smoothness).
    * `hint` — PROVED cleanly from `hlift_int` + a.e.-strong-measurability of
      the time integrand `s ↦ S(t-s)(…)(x)` (the trajectory's time regularity,
      which abstractly cannot follow from spatial bounds alone) + the L∞
      semigroup contraction (proven `intervalSemigroupOperator_Linfty_bound`).
    * `hchem` — reduced to an explicit flux-divergence Lipschitz hypothesis the
      resolver supplies.  A pointwise bound on a *difference of derivatives*
      cannot be produced from sup/Lipschitz bounds on `R`; it is a genuine
      `C¹` flux estimate of the elliptic problem.  We package it into the
      `K · D` form required by `IntervalCoupledResolverBallEstimates`.

  REMAINING GAP (documented, not faked): the abstract regularity inputs
  `hchem_meas`, `hsemigroup_meas`, and the flux-divergence Lipschitz/sup bounds
  are the precise analytic facts the concrete interval Neumann resolver must
  establish.  They are not derivable from sup/Lipschitz control of `R` alone.
-/
import ShenWork.PDE.IntervalDomainExistence

open ShenWork.Paper2 ShenWork.IntervalDomain MeasureTheory

noncomputable section

namespace ShenWork.IntervalCoupledBallEstimates

open ShenWork.IntervalDomainExistence

/-! ## Pointwise bound for the lifted coupled source

The coupled source is `-χ₀ · chemotaxisDiv p u v + logisticSource p u`.
On the M-ball with a flux-divergence sup bound `Kc` and a logistic-source sup
bound `Lc`, the lift is bounded by `|χ₀| · Kc + Lc`. -/

/-- A pointwise sup bound on the lifted coupled source from a chemotaxis-flux
divergence sup bound and a logistic-source sup bound.  These two scalar bounds
are what the resolver/ball control provides. -/
theorem intervalCoupledSource_lift_abs_le
    (p : CM2Params) (u v : intervalDomainPoint → ℝ)
    {Kc Lc : ℝ}
    (hchem_sup : ∀ y : intervalDomainPoint,
      |intervalDomainChemotaxisDiv p u v y| ≤ Kc)
    (hlog_sup : ∀ y : intervalDomainPoint,
      |intervalLogisticSource p u y| ≤ Lc) :
    ∀ x : ℝ,
      |intervalDomainLift (intervalCoupledSource p u v) x| ≤ |p.χ₀| * Kc + Lc := by
  -- Reduce the lift bound to a pointwise bound on `intervalDomainPoint`.
  have hpt : ∀ y : intervalDomainPoint,
      |intervalCoupledSource p u v y| ≤ |p.χ₀| * Kc + Lc := by
    intro y
    unfold intervalCoupledSource
    calc
      |(-p.χ₀ * intervalDomainChemotaxisDiv p u v y) +
          intervalLogisticSource p u y|
          ≤ |(-p.χ₀ * intervalDomainChemotaxisDiv p u v y)| +
              |intervalLogisticSource p u y| := abs_add_le _ _
      _ = |p.χ₀| * |intervalDomainChemotaxisDiv p u v y| +
              |intervalLogisticSource p u y| := by
            rw [abs_mul, abs_neg]
      _ ≤ |p.χ₀| * Kc + Lc :=
            add_le_add
              (mul_le_mul_of_nonneg_left (hchem_sup y) (abs_nonneg _))
              (hlog_sup y)
  -- The lift only ever returns either a value `f ⟨x,_⟩` or `0`.
  intro x
  unfold intervalDomainLift
  by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
  · simp only [hx, dif_pos]
    exact hpt ⟨x, hx⟩
  · simp only [hx, dif_neg, not_false_iff]
    have hnn : 0 ≤ |p.χ₀| * Kc + Lc :=
      le_trans (abs_nonneg _) (hpt ⟨0, by constructor <;> norm_num⟩)
    simpa using hnn

/-! ## (hlift_int) Integrability of the lifted coupled source

A bounded, a.e.-strongly-measurable function is integrable against the finite
interval measure (`intervalMeasure_integrable_of_abs_bound`).  The bound is
provided by `intervalCoupledSource_lift_abs_le`; the measurability of the lift
(whose chemotaxis part is a `deriv`) is supplied as a resolver-regularity
hypothesis. -/

/-- **(hlift_int).**  Integrability of the lifted coupled source against the
interval measure, from a sup bound on the chemotaxis flux divergence, a sup
bound on the logistic source, and a.e.-strong-measurability of the lift. -/
theorem intervalCoupledSource_lift_integrable
    (p : CM2Params) (u v : intervalDomainPoint → ℝ)
    {Kc Lc : ℝ}
    (hmeas : AEStronglyMeasurable
      (intervalDomainLift (intervalCoupledSource p u v)) (intervalMeasure 1))
    (hchem_sup : ∀ y : intervalDomainPoint,
      |intervalDomainChemotaxisDiv p u v y| ≤ Kc)
    (hlog_sup : ∀ y : intervalDomainPoint,
      |intervalLogisticSource p u y| ≤ Lc) :
    Integrable (intervalDomainLift (intervalCoupledSource p u v))
      (intervalMeasure 1) :=
  intervalMeasure_integrable_of_abs_bound hmeas
    (intervalCoupledSource_lift_abs_le p u v hchem_sup hlog_sup)

/-! ## (hint) Time-integrability of the Duhamel integrand

The integrand `s ↦ S(t-s)(lift(coupledSource(u s, R(u s))))(x)` is bounded by a
constant via the proven `intervalSemigroupOperator_Linfty_bound` (for positive
heat time `t - s`).  Combined with a.e.-strong-measurability of the integrand
in `s` (the trajectory time regularity supplied by the resolver setup) and
finiteness of `volume` on the bounded set `Icc 0 t`, integrability follows. -/

/-- **(hint).**  Integrability on `Icc 0 t` of the coupled Duhamel time
integrand.  The pointwise sup bounds (chemotaxis flux + logistic) give a uniform
L∞ bound on the semigroup output; together with measurability in `s` and the
finite measure on the bounded time interval this yields integrability. -/
theorem intervalCoupledDuhamelIntegrand_integrableOn
    (p : CM2Params)
    (R : (intervalDomainPoint → ℝ) → intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ)
    {t Kc Lc : ℝ} (ht0 : 0 ≤ t) (hKc : 0 ≤ Kc) (hLc : 0 ≤ Lc)
    (x : intervalDomainPoint)
    (hmeas : AEStronglyMeasurable
      (fun s => intervalSemigroupOperator 1 (t - s)
        (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) x.1)
      (volume.restrict (Set.Icc 0 t)))
    (hchem_sup : ∀ s y, 0 ≤ s → s ≤ t →
      |intervalDomainChemotaxisDiv p (u s) (R (u s)) y| ≤ Kc)
    (hlog_sup : ∀ s y, 0 ≤ s → s ≤ t →
      |intervalLogisticSource p (u s) y| ≤ Lc) :
    IntegrableOn
      (fun s => intervalSemigroupOperator 1 (t - s)
        (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) x.1)
      (Set.Icc 0 t) volume := by
  -- Uniform L∞ bound on the integrand for `s < t` via the proven semigroup
  -- contraction.  The single point `s = t` (zero heat time) is `volume`-null,
  -- so an a.e. bound on the finite measure `volume.restrict (Icc 0 t)` is all we
  -- need for the dominated-integrability criterion.
  set B : ℝ := |p.χ₀| * Kc + Lc with hB
  have hBnn : 0 ≤ B := add_nonneg (mul_nonneg (abs_nonneg _) hKc) hLc
  rw [IntegrableOn]
  -- a.e.-strong-measurability + a.e. bound `≤ B` on a finite measure ⟹ Integrable.
  refine Integrable.of_bound hmeas B ?_
  -- The bound `‖…‖ ≤ B` holds whenever `0 ≤ s < t` (positive heat time); the only
  -- exceptional point in `Icc 0 t` is `s = t`, which is `volume`-null.
  have hpt : ∀ s : ℝ, 0 ≤ s → s < t →
      ‖intervalSemigroupOperator 1 (t - s)
        (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) x.1‖ ≤ B := by
    intro s hs0 hs
    have htpos : 0 < t - s := by linarith
    have :=
      intervalSemigroupOperator_Linfty_bound (L := 1) (t := t - s) htpos
        (M := B) hBnn
        (intervalCoupledSource_lift_abs_le p (u s) (R (u s))
          (fun y => hchem_sup s y hs0 hs.le) (fun y => hlog_sup s y hs0 hs.le)) x.1
    rwa [Real.norm_eq_abs]
  -- Express the a.e. bound on the restricted measure: with `s ∈ Icc 0 t` in
  -- context, the only exceptional point is `s = t`, a null set.
  refine (MeasureTheory.ae_restrict_iff' (by measurability)).2 ?_
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null (t := ({t} : Set ℝ)) ?_ ?_
  · intro s hs
    -- `hs : ¬ (s ∈ Icc 0 t → ‖…‖ ≤ B)`.  Hence `s ∈ Icc 0 t` and the bound fails.
    simp only [Set.mem_setOf_eq, Classical.not_imp] at hs
    obtain ⟨hmem, hfail⟩ := hs
    -- If `s ≠ t`, then `s < t` (since `s ≤ t`), giving the bound — contradiction.
    by_contra hst
    have hslt : s < t := lt_of_le_of_ne hmem.2 (by simpa using hst)
    exact hfail (hpt s hmem.1 hslt)
  · -- `{t}` is null for the (restricted) measure in play.
    simp

/-! ## (hchem) Chemotaxis-divergence Lipschitz bound in `u` along `R`

The chemotaxis divergence `intervalDomainChemotaxisDiv p u v y` is the spatial
derivative of the flux `u · ∂v / (1+v)^β`.  Bounding the *difference* of two
such divergences pointwise is a genuine `C¹` estimate of the elliptic flux:
it cannot be produced from sup/Lipschitz control of `R` alone, because it is a
bound on a difference of `deriv`s, not of the underlying functions.

We therefore record the flux-divergence Lipschitz estimate as an explicit
hypothesis the resolver supplies (its constant `Kr` absorbs `|χ₀|`, the
`β`-power factors, the resolver Lipschitz constant `Lr`, and the gradient
smoothing of `R`), and package it into the `K · D` form demanded by
`IntervalCoupledResolverBallEstimates`. -/

/-- **(hchem).**  The chemotaxis divergence is `K`-Lipschitz in `u` along the
resolver `R`, on the trajectory ball.  This is a direct repackaging of the
resolver-supplied flux-divergence Lipschitz estimate `hflux_lip` into the
constant `K = Kr` against the trajectory difference bound `D`. -/
theorem intervalDomainChemotaxisDiv_resolver_lipschitz
    (p : CM2Params)
    (R : (intervalDomainPoint → ℝ) → intervalDomainPoint → ℝ)
    {u₁ u₂ : intervalDomainPoint → ℝ} (y : intervalDomainPoint) {D Kr : ℝ}
    (hflux_lip :
      |intervalDomainChemotaxisDiv p u₁ (R u₁) y -
        intervalDomainChemotaxisDiv p u₂ (R u₂) y| ≤ Kr * D) :
    |intervalDomainChemotaxisDiv p u₁ (R u₁) y -
      intervalDomainChemotaxisDiv p u₂ (R u₂) y| ≤ Kr * D :=
  hflux_lip

/-- The four resolver-supplied regularity inputs assembled into the
`IntervalCoupledResolverBallEstimates` shape (for the `hchem`, `hint`,
`hlift_int` conjuncts).  `hmap` is left to the existing
`intervalCoupledDuhamel_zero_trajectory_bound_of_initial_bound` /
`intervalCoupledDuhamelOperator_bound_of_source_bound` infrastructure in
`IntervalDomainExistence.lean`, which requires the same sup bounds plus the
map-time integrability already covered by `hint`. -/
theorem intervalCoupledResolver_hchem_hint_hlift
    (p : CM2Params)
    (R : (intervalDomainPoint → ℝ) → intervalDomainPoint → ℝ)
    {T M K : ℝ}
    -- (hchem) resolver flux-divergence Lipschitz estimate on the ball
    (hflux_lip : ∀ (u₁ u₂ : ℝ → intervalDomainPoint → ℝ) (D : ℝ),
      0 ≤ D →
      intervalTrajectoryBoundedOn T M u₁ →
      intervalTrajectoryBoundedOn T M u₂ →
      (∀ s y, 0 ≤ s → s ≤ T → |u₁ s y - u₂ s y| ≤ D) →
        ∀ (s : ℝ) (y : intervalDomainPoint), 0 ≤ s → s ≤ T →
          |intervalDomainChemotaxisDiv p (u₁ s) (R (u₁ s)) y -
            intervalDomainChemotaxisDiv p (u₂ s) (R (u₂ s)) y| ≤ K * D)
    -- (hint) measurability in time of the Duhamel integrand on the ball
    (hsemigroup_meas : ∀ u : ℝ → intervalDomainPoint → ℝ,
      intervalTrajectoryBoundedOn T M u →
        ∀ (t : ℝ) (x : intervalDomainPoint), 0 ≤ t → t ≤ T →
          AEStronglyMeasurable
            (fun s => intervalSemigroupOperator 1 (t - s)
              (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) x.1)
            (volume.restrict (Set.Icc 0 t)))
    -- (hlift_int) measurability of the lifted coupled source on the ball
    (hlift_meas : ∀ u : ℝ → intervalDomainPoint → ℝ,
      intervalTrajectoryBoundedOn T M u →
        ∀ s, 0 ≤ s → s ≤ T →
          AEStronglyMeasurable
            (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
            (intervalMeasure 1))
    -- flux-divergence sup bound on the ball (gives the L∞ source/integrand bound)
    {Kc Lc : ℝ} (hKc : 0 ≤ Kc) (hLc : 0 ≤ Lc)
    (hchem_sup : ∀ u : ℝ → intervalDomainPoint → ℝ,
      intervalTrajectoryBoundedOn T M u →
        ∀ s y, 0 ≤ s → s ≤ T →
          |intervalDomainChemotaxisDiv p (u s) (R (u s)) y| ≤ Kc)
    (hlog_sup : ∀ u : ℝ → intervalDomainPoint → ℝ,
      intervalTrajectoryBoundedOn T M u →
        ∀ s y, 0 ≤ s → s ≤ T →
          |intervalLogisticSource p (u s) y| ≤ Lc) :
    -- (hchem)
    (∀ (u₁ u₂ : ℝ → intervalDomainPoint → ℝ) (D : ℝ),
        0 ≤ D →
        intervalTrajectoryBoundedOn T M u₁ →
        intervalTrajectoryBoundedOn T M u₂ →
        (∀ s y, 0 ≤ s → s ≤ T → |u₁ s y - u₂ s y| ≤ D) →
          ∀ (s : ℝ) (y : intervalDomainPoint), 0 ≤ s → s ≤ T →
            |intervalDomainChemotaxisDiv p (u₁ s) (R (u₁ s)) y -
              intervalDomainChemotaxisDiv p (u₂ s) (R (u₂ s)) y| ≤ K * D) ∧
    -- (hint)
    (∀ u : ℝ → intervalDomainPoint → ℝ,
        intervalTrajectoryBoundedOn T M u →
          ∀ (t : ℝ) (x : intervalDomainPoint), 0 ≤ t → t ≤ T →
            MeasureTheory.IntegrableOn
              (fun s => intervalSemigroupOperator 1 (t - s)
                (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) x.1)
              (Set.Icc 0 t) MeasureTheory.volume) ∧
    -- (hlift_int)
    (∀ u : ℝ → intervalDomainPoint → ℝ,
        intervalTrajectoryBoundedOn T M u →
          ∀ s, 0 ≤ s → s ≤ T →
            MeasureTheory.Integrable
              (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
              (intervalMeasure 1)) := by
  refine ⟨hflux_lip, ?_, ?_⟩
  · -- (hint): integrability of the Duhamel time integrand.  The integrand's
    -- support is `Icc 0 t ⊆ Icc 0 T`, so the ball sup bounds (valid on `[0,T]`)
    -- apply on the relevant range `[0,t]`.
    intro u hu t x ht0 htT
    exact intervalCoupledDuhamelIntegrand_integrableOn p R u (Kc := Kc) (Lc := Lc)
      ht0 hKc hLc x
      (hsemigroup_meas u hu t x ht0 htT)
      (fun s y hs0 hst => hchem_sup u hu s y hs0 (le_trans hst htT))
      (fun s y hs0 hst => hlog_sup u hu s y hs0 (le_trans hst htT))
  · -- (hlift_int): integrability of the lifted coupled source.
    intro u hu s hs0 hsT
    exact intervalCoupledSource_lift_integrable p (u s) (R (u s))
      (hlift_meas u hu s hs0 hsT)
      (fun y => hchem_sup u hu s y hs0 hsT)
      (fun y => hlog_sup u hu s y hs0 hsT)

end ShenWork.IntervalCoupledBallEstimates
