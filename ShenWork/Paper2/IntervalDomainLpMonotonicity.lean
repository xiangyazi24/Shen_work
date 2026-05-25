/-
  ShenWork/Paper2/IntervalDomainLpMonotonicity.lean

  Finite-interval Lp monotonicity used by the Moser closure.

  On a finite-measure domain, L^q control implies L^p control for 1 < p ≤ q
  once the solution is nonnegative and the relevant powers are integrable.
  This file proves the concrete `[0,1]` intervalDomain version needed to turn
  the arithmetic Moser exponent chain into all exponents p > 1.
-/
import ShenWork.Paper2.IntervalDomainMoserClosure
import ShenWork.PDE.LeibnizRule
import Mathlib.Analysis.ODE.Gronwall

open ShenWork.Paper2
open ShenWork.IntervalDomain
open Filter
open Topology

noncomputable section

namespace ShenWork.Paper2.IntervalDomainLpMonotonicity

/-- Lebesgue measure restricted to the open interval that carries the
`intervalDomain` interval integral. -/
abbrev intervalDomainInteriorMeasure : MeasureTheory.Measure ℝ :=
  MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)

lemma hasDerivAt_abs_rpow_of_hasDerivAt_pos
    {f : ℝ → ℝ} {f' t p : ℝ}
    (hf : HasDerivAt f f' t) (hpos : 0 < f t) :
    HasDerivAt (fun s => |f s| ^ p) (f' * p * (f t) ^ (p - 1)) t := by
  have hpos_eventually : ∀ᶠ s in 𝓝 t, 0 < f s :=
    continuousAt_const.eventually_lt hf.continuousAt hpos
  have habs :
      (fun s => |f s| ^ p) =ᶠ[𝓝 t] fun s => (f s) ^ p := by
    filter_upwards [hpos_eventually] with s hs
    rw [abs_of_pos hs]
  exact habs.hasDerivAt_iff.mpr
    (hf.rpow_const (Or.inl (ne_of_gt hpos)))

/-- Dominated differentiation under the `[0,1]` interval integral.

This is the finite-interval form of the parametric-integral theorem used in
the `Psi_deriv` Leibniz-rule family: local pointwise derivatives, dominated
uniformly on a time neighborhood, pass through the interval integral. -/
theorem intervalDomain_intervalIntegral_hasDerivAt_of_dominated_deriv_le
    {F F' : ℝ → ℝ → ℝ} {bound : ℝ → ℝ} {t : ℝ}
    (hF_meas :
      ∀ᶠ s in 𝓝 t,
        MeasureTheory.AEStronglyMeasurable (F s)
          intervalDomainInteriorMeasure)
    (hF_int : IntervalIntegrable (F t) MeasureTheory.volume 0 1)
    (hF'_meas :
      MeasureTheory.AEStronglyMeasurable (F' t)
        intervalDomainInteriorMeasure)
    (h_bound :
      ∀ᵐ y ∂intervalDomainInteriorMeasure,
        ∀ s ∈ Metric.ball t 1, ‖F' s y‖ ≤ bound y)
    (hbound_int : MeasureTheory.Integrable bound intervalDomainInteriorMeasure)
    (h_diff :
      ∀ᵐ y ∂intervalDomainInteriorMeasure,
        ∀ s ∈ Metric.ball t 1, HasDerivAt (fun τ => F τ y) (F' s y) s) :
    HasDerivAt
      (fun s => ∫ y in (0 : ℝ)..1, F s y)
      (∫ y in (0 : ℝ)..1, F' t y) t := by
  have hF_int_restrict :
      MeasureTheory.Integrable (F t) intervalDomainInteriorMeasure := by
    have hIoc : MeasureTheory.Integrable
        (F t) (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le
      (show (0 : ℝ) ≤ 1 by norm_num)).mp hF_int).integrable
    simpa [intervalDomainInteriorMeasure,
      MeasureTheory.restrict_Ioo_eq_restrict_Ioc] using hIoc
  have hmain :
      HasDerivAt
        (fun s => ∫ y, F s y ∂intervalDomainInteriorMeasure)
        (∫ y, F' t y ∂intervalDomainInteriorMeasure) t :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := intervalDomainInteriorMeasure)
      (bound := bound)
      (F := F)
      (F' := F')
      (x₀ := t)
      (s := Metric.ball t 1)
      (Metric.ball_mem_nhds t zero_lt_one)
      hF_meas hF_int_restrict hF'_meas h_bound hbound_int h_diff).2
  simpa [intervalDomainInteriorMeasure,
    intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    MeasureTheory.restrict_Ioo_eq_restrict_Ioc] using hmain

/-- The concrete interval-domain power-energy derivative:
`d/dt ∫ |u|^p = ∫ u_t * p * u^(p-1)`, conditional on the standard
dominated-convergence hypotheses for the time derivative.

The positivity hypothesis is only needed on `intervalDomain.inside`; endpoints
do not affect the interval integral. -/
theorem intervalDomain_integral_abs_rpow_hasDerivAt_of_dominated_deriv_le
    {u ut : ℝ → intervalDomain.Point → ℝ} {p t : ℝ} {bound : ℝ → ℝ}
    (hpow_meas :
      ∀ᶠ s in 𝓝 t,
        MeasureTheory.AEStronglyMeasurable
          (intervalDomainLift (fun x : intervalDomain.Point => |u s x| ^ p))
          intervalDomainInteriorMeasure)
    (hpow_int :
      IntervalIntegrable
        (intervalDomainLift (fun x : intervalDomain.Point => |u t x| ^ p))
        MeasureTheory.volume 0 1)
    (hderiv_meas :
      MeasureTheory.AEStronglyMeasurable
        (intervalDomainLift
          (fun x : intervalDomain.Point => ut t x * p * (u t x) ^ (p - 1)))
        intervalDomainInteriorMeasure)
    (hderiv_bound :
      ∀ᵐ y ∂intervalDomainInteriorMeasure,
        ∀ s ∈ Metric.ball t 1,
          ‖intervalDomainLift
            (fun x : intervalDomain.Point => ut s x * p * (u s x) ^ (p - 1)) y‖ ≤
            bound y)
    (hbound_int : MeasureTheory.Integrable bound intervalDomainInteriorMeasure)
    (hu_hasDeriv :
      ∀ s ∈ Metric.ball t 1,
        ∀ x : intervalDomain.Point, x ∈ intervalDomain.inside →
          HasDerivAt (fun τ => u τ x) (ut s x) s)
    (hu_pos :
      ∀ s ∈ Metric.ball t 1,
        ∀ x : intervalDomain.Point, x ∈ intervalDomain.inside → 0 < u s x) :
    HasDerivAt
      (fun s => intervalDomain.integral
        (fun x : intervalDomain.Point => |u s x| ^ p))
      (intervalDomain.integral
        (fun x : intervalDomain.Point => ut t x * p * (u t x) ^ (p - 1))) t := by
  let F : ℝ → ℝ → ℝ :=
    fun s y => intervalDomainLift
      (fun x : intervalDomain.Point => |u s x| ^ p) y
  let F' : ℝ → ℝ → ℝ :=
    fun s y => intervalDomainLift
      (fun x : intervalDomain.Point => ut s x * p * (u s x) ^ (p - 1)) y
  have hmem :
      ∀ᵐ y ∂intervalDomainInteriorMeasure, y ∈ Set.Ioo (0 : ℝ) 1 :=
    MeasureTheory.ae_restrict_mem measurableSet_Ioo
  have hdiff :
      ∀ᵐ y ∂intervalDomainInteriorMeasure,
        ∀ s ∈ Metric.ball t 1, HasDerivAt (fun τ => F τ y) (F' s y) s := by
    filter_upwards [hmem] with y hy s hs
    have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hy.1, le_of_lt hy.2⟩
    let x : intervalDomain.Point := ⟨y, hyIcc⟩
    have hx_inside : x ∈ intervalDomain.inside := by
      simpa [intervalDomain, x] using hy
    have hbase : HasDerivAt (fun τ => u τ x) (ut s x) s :=
      hu_hasDeriv s hs x hx_inside
    have hpos : 0 < u s x := hu_pos s hs x hx_inside
    have hpow :=
      hasDerivAt_abs_rpow_of_hasDerivAt_pos
        (p := p) hbase hpos
    have hF_eq :
        (fun τ => F τ y) = fun τ => |u τ x| ^ p := by
      funext τ
      by_cases h : y ∈ Set.Icc (0 : ℝ) 1
      · have hx_eq : (⟨y, h⟩ : intervalDomain.Point) = x := Subtype.ext rfl
        dsimp [F, intervalDomainLift]
        rw [dif_pos h, hx_eq]
      · exact False.elim (h hyIcc)
    have hF'_eq :
        F' s y = ut s x * p * (u s x) ^ (p - 1) := by
      by_cases h : y ∈ Set.Icc (0 : ℝ) 1
      · have hx_eq : (⟨y, h⟩ : intervalDomain.Point) = x := Subtype.ext rfl
        dsimp [F', intervalDomainLift]
        rw [dif_pos h, hx_eq]
      · exact False.elim (h hyIcc)
    rwa [hF_eq, hF'_eq]
  have hmain :=
    intervalDomain_intervalIntegral_hasDerivAt_of_dominated_deriv_le
      (F := F) (F' := F') (bound := bound) (t := t)
      (by simpa [F] using hpow_meas)
      (by simpa [F] using hpow_int)
      (by simpa [F'] using hderiv_meas)
      (by simpa [F'] using hderiv_bound)
      hbound_int
      hdiff
  simpa [intervalDomain, intervalDomainIntegral, F, F'] using hmain

/-- Absolute Lp energy on the concrete interval domain. -/
def intervalDomainLpAbsEnergy
    (pExp : ℝ) (u : ℝ → intervalDomain.Point → ℝ) (t : ℝ) : ℝ :=
  intervalDomain.integral (fun x : intervalDomain.Point => |u t x| ^ pExp)

/-- The weighted time derivative delivered by differentiating
`intervalDomainLpAbsEnergy` under the interval integral on positive interior
traces. -/
def intervalDomainLpWeightedTimeDerivative
    (pExp : ℝ) (u ut : ℝ → intervalDomain.Point → ℝ)
    (t : ℝ) (x : intervalDomain.Point) : ℝ :=
  ut t x * pExp * (u t x) ^ (pExp - 1)

/-- The Moser-gradient term paired with the Lp energy. -/
def intervalDomainLpGradientEnergy
    (pExp : ℝ) (u : ℝ → intervalDomain.Point → ℝ) (t : ℝ) : ℝ :=
  intervalDomain.integral (fun x : intervalDomain.Point =>
    (intervalDomain.gradNorm
      (fun y : intervalDomain.Point => (u t y) ^ (pExp / 2)) x) ^ 2)

/-- Derivative equality form of
`intervalDomain_integral_abs_rpow_hasDerivAt_of_dominated_deriv_le`. -/
theorem intervalDomain_Lp_abs_energy_deriv_eq_weighted_time
    {u ut : ℝ → intervalDomain.Point → ℝ} {p t : ℝ} {bound : ℝ → ℝ}
    (hpow_meas :
      ∀ᶠ s in 𝓝 t,
        MeasureTheory.AEStronglyMeasurable
          (intervalDomainLift (fun x : intervalDomain.Point => |u s x| ^ p))
          intervalDomainInteriorMeasure)
    (hpow_int :
      IntervalIntegrable
        (intervalDomainLift (fun x : intervalDomain.Point => |u t x| ^ p))
        MeasureTheory.volume 0 1)
    (hderiv_meas :
      MeasureTheory.AEStronglyMeasurable
        (intervalDomainLift
          (fun x : intervalDomain.Point => ut t x * p * (u t x) ^ (p - 1)))
        intervalDomainInteriorMeasure)
    (hderiv_bound :
      ∀ᵐ y ∂intervalDomainInteriorMeasure,
        ∀ s ∈ Metric.ball t 1,
          ‖intervalDomainLift
            (fun x : intervalDomain.Point => ut s x * p * (u s x) ^ (p - 1)) y‖ ≤
            bound y)
    (hbound_int : MeasureTheory.Integrable bound intervalDomainInteriorMeasure)
    (hu_hasDeriv :
      ∀ s ∈ Metric.ball t 1,
        ∀ x : intervalDomain.Point, x ∈ intervalDomain.inside →
          HasDerivAt (fun τ => u τ x) (ut s x) s)
    (hu_pos :
      ∀ s ∈ Metric.ball t 1,
        ∀ x : intervalDomain.Point, x ∈ intervalDomain.inside → 0 < u s x) :
    deriv (fun s => intervalDomainLpAbsEnergy p u s) t =
      intervalDomain.integral
        (intervalDomainLpWeightedTimeDerivative p u ut t) := by
  have hderiv :=
    intervalDomain_integral_abs_rpow_hasDerivAt_of_dominated_deriv_le
      (u := u) (ut := ut) (p := p) (t := t) (bound := bound)
      hpow_meas hpow_int hderiv_meas hderiv_bound hbound_int
      hu_hasDeriv hu_pos
  simpa [intervalDomainLpAbsEnergy, intervalDomainLpWeightedTimeDerivative]
    using hderiv.deriv

/-- Replace the weighted time-derivative frontier by the actual time derivative
of the Lp energy.

The hypothesis `hweighted_frontier` is exactly the estimate obtained after the
PDE has been tested against the Lp weight and the Neumann integration-by-parts
boundary term has been discharged.  This theorem only supplies the
differentiation-under-the-integral part. -/
theorem intervalDomain_Lp_abs_energy_gronwall_of_weighted_time_frontier
    {u ut : ℝ → intervalDomain.Point → ℝ}
    {p rho t A B K L_const : ℝ} {bound : ℝ → ℝ}
    (hpow_meas :
      ∀ᶠ s in 𝓝 t,
        MeasureTheory.AEStronglyMeasurable
          (intervalDomainLift (fun x : intervalDomain.Point => |u s x| ^ p))
          intervalDomainInteriorMeasure)
    (hpow_int :
      IntervalIntegrable
        (intervalDomainLift (fun x : intervalDomain.Point => |u t x| ^ p))
        MeasureTheory.volume 0 1)
    (hderiv_meas :
      MeasureTheory.AEStronglyMeasurable
        (intervalDomainLift
          (fun x : intervalDomain.Point => ut t x * p * (u t x) ^ (p - 1)))
        intervalDomainInteriorMeasure)
    (hderiv_bound :
      ∀ᵐ y ∂intervalDomainInteriorMeasure,
        ∀ s ∈ Metric.ball t 1,
          ‖intervalDomainLift
            (fun x : intervalDomain.Point => ut s x * p * (u s x) ^ (p - 1)) y‖ ≤
            bound y)
    (hbound_int : MeasureTheory.Integrable bound intervalDomainInteriorMeasure)
    (hu_hasDeriv :
      ∀ s ∈ Metric.ball t 1,
        ∀ x : intervalDomain.Point, x ∈ intervalDomain.inside →
          HasDerivAt (fun τ => u τ x) (ut s x) s)
    (hu_pos :
      ∀ s ∈ Metric.ball t 1,
        ∀ x : intervalDomain.Point, x ∈ intervalDomain.inside → 0 < u s x)
    (hweighted_frontier :
      (1 / p) *
          intervalDomain.integral
            (intervalDomainLpWeightedTimeDerivative p u ut t) +
        A * intervalDomainLpGradientEnergy p u t +
        B * intervalDomainLpAbsEnergy p u t ≤
      K * intervalDomainLpAbsEnergy (p + rho) u t + L_const) :
    (1 / p) * deriv (fun τ => intervalDomainLpAbsEnergy p u τ) t +
        A * intervalDomainLpGradientEnergy p u t +
        B * intervalDomainLpAbsEnergy p u t ≤
      K * intervalDomainLpAbsEnergy (p + rho) u t + L_const := by
  have hderiv :=
    intervalDomain_Lp_abs_energy_deriv_eq_weighted_time
      (u := u) (ut := ut) (p := p) (t := t) (bound := bound)
      hpow_meas hpow_int hderiv_meas hderiv_bound hbound_int
      hu_hasDeriv hu_pos
  rwa [hderiv]

/-- Gronwall-form Lp differential inequality from the dissipative estimate
left by Neumann integration by parts.

Here `hneumann_by_parts_bound` is the honest spatial frontier: after testing
the PDE by the Lp weight, the Neumann boundary contribution has vanished and
the diffusion/source terms have been bounded by the displayed right-hand side. -/
theorem intervalDomain_Lp_abs_energy_gronwall_of_neumann_by_parts_bound
    {u ut : ℝ → intervalDomain.Point → ℝ}
    {p rho t A B K L_const : ℝ} {bound : ℝ → ℝ}
    (hpow_meas :
      ∀ᶠ s in 𝓝 t,
        MeasureTheory.AEStronglyMeasurable
          (intervalDomainLift (fun x : intervalDomain.Point => |u s x| ^ p))
          intervalDomainInteriorMeasure)
    (hpow_int :
      IntervalIntegrable
        (intervalDomainLift (fun x : intervalDomain.Point => |u t x| ^ p))
        MeasureTheory.volume 0 1)
    (hderiv_meas :
      MeasureTheory.AEStronglyMeasurable
        (intervalDomainLift
          (fun x : intervalDomain.Point => ut t x * p * (u t x) ^ (p - 1)))
        intervalDomainInteriorMeasure)
    (hderiv_bound :
      ∀ᵐ y ∂intervalDomainInteriorMeasure,
        ∀ s ∈ Metric.ball t 1,
          ‖intervalDomainLift
            (fun x : intervalDomain.Point => ut s x * p * (u s x) ^ (p - 1)) y‖ ≤
            bound y)
    (hbound_int : MeasureTheory.Integrable bound intervalDomainInteriorMeasure)
    (hu_hasDeriv :
      ∀ s ∈ Metric.ball t 1,
        ∀ x : intervalDomain.Point, x ∈ intervalDomain.inside →
          HasDerivAt (fun τ => u τ x) (ut s x) s)
    (hu_pos :
      ∀ s ∈ Metric.ball t 1,
        ∀ x : intervalDomain.Point, x ∈ intervalDomain.inside → 0 < u s x)
    (hneumann_by_parts_bound :
      (1 / p) *
          intervalDomain.integral
            (intervalDomainLpWeightedTimeDerivative p u ut t) ≤
        -A * intervalDomainLpGradientEnergy p u t -
          B * intervalDomainLpAbsEnergy p u t +
          K * intervalDomainLpAbsEnergy (p + rho) u t + L_const) :
    (1 / p) * deriv (fun τ => intervalDomainLpAbsEnergy p u τ) t +
        A * intervalDomainLpGradientEnergy p u t +
        B * intervalDomainLpAbsEnergy p u t ≤
      K * intervalDomainLpAbsEnergy (p + rho) u t + L_const := by
  have hderiv :=
    intervalDomain_Lp_abs_energy_deriv_eq_weighted_time
      (u := u) (ut := ut) (p := p) (t := t) (bound := bound)
      hpow_meas hpow_int hderiv_meas hderiv_bound hbound_int
      hu_hasDeriv hu_pos
  rw [hderiv]
  linarith

/-- Time-interval version of
`intervalDomain_Lp_abs_energy_gronwall_of_neumann_by_parts_bound`.

This is the Lp-norm Gronwall differential inequality over `(0,T)`.  The only
remaining frontiers are exactly the analytic hypotheses listed here: dominated
differentiation under the integral and the Neumann-by-parts dissipative bound
for the weighted time term. -/
theorem intervalDomain_Lp_abs_energy_gronwall_family_of_neumann_by_parts_bound
    {u ut : ℝ → intervalDomain.Point → ℝ}
    {T p rho A B K L_const : ℝ} {bound : ℝ → ℝ → ℝ}
    (hpow_meas :
      ∀ t, 0 < t → t < T →
        ∀ᶠ s in 𝓝 t,
          MeasureTheory.AEStronglyMeasurable
            (intervalDomainLift (fun x : intervalDomain.Point => |u s x| ^ p))
            intervalDomainInteriorMeasure)
    (hpow_int :
      ∀ t, 0 < t → t < T →
        IntervalIntegrable
          (intervalDomainLift (fun x : intervalDomain.Point => |u t x| ^ p))
          MeasureTheory.volume 0 1)
    (hderiv_meas :
      ∀ t, 0 < t → t < T →
        MeasureTheory.AEStronglyMeasurable
          (intervalDomainLift
            (fun x : intervalDomain.Point => ut t x * p * (u t x) ^ (p - 1)))
          intervalDomainInteriorMeasure)
    (hderiv_bound :
      ∀ t, 0 < t → t < T →
        ∀ᵐ y ∂intervalDomainInteriorMeasure,
          ∀ s ∈ Metric.ball t 1,
            ‖intervalDomainLift
              (fun x : intervalDomain.Point => ut s x * p * (u s x) ^ (p - 1)) y‖ ≤
              bound t y)
    (hbound_int :
      ∀ t, 0 < t → t < T →
        MeasureTheory.Integrable (bound t) intervalDomainInteriorMeasure)
    (hu_hasDeriv :
      ∀ t, 0 < t → t < T →
        ∀ s ∈ Metric.ball t 1,
          ∀ x : intervalDomain.Point, x ∈ intervalDomain.inside →
            HasDerivAt (fun τ => u τ x) (ut s x) s)
    (hu_pos :
      ∀ t, 0 < t → t < T →
        ∀ s ∈ Metric.ball t 1,
          ∀ x : intervalDomain.Point, x ∈ intervalDomain.inside → 0 < u s x)
    (hneumann_by_parts_bound :
      ∀ t, 0 < t → t < T →
        (1 / p) *
            intervalDomain.integral
              (intervalDomainLpWeightedTimeDerivative p u ut t) ≤
          -A * intervalDomainLpGradientEnergy p u t -
            B * intervalDomainLpAbsEnergy p u t +
            K * intervalDomainLpAbsEnergy (p + rho) u t + L_const) :
    ∀ t, 0 < t → t < T →
      (1 / p) * deriv (fun τ => intervalDomainLpAbsEnergy p u τ) t +
          A * intervalDomainLpGradientEnergy p u t +
          B * intervalDomainLpAbsEnergy p u t ≤
        K * intervalDomainLpAbsEnergy (p + rho) u t + L_const := by
  intro t ht0 htT
  exact intervalDomain_Lp_abs_energy_gronwall_of_neumann_by_parts_bound
    (u := u) (ut := ut) (p := p) (rho := rho) (t := t)
    (A := A) (B := B) (K := K) (L_const := L_const)
    (bound := bound t)
    (hpow_meas t ht0 htT)
    (hpow_int t ht0 htT)
    (hderiv_meas t ht0 htT)
    (hderiv_bound t ht0 htT)
    (hbound_int t ht0 htT)
    (hu_hasDeriv t ht0 htT)
    (hu_pos t ht0 htT)
    (hneumann_by_parts_bound t ht0 htT)

/-- Scalar Gronwall bound for the absolute Lp energy on `[0,T]`.

The right-derivative hypothesis is the analytic frontier needed by Mathlib's
Gronwall theorem. -/
theorem intervalDomain_Lp_abs_energy_le_gronwallBound
    {u : ℝ → intervalDomain.Point → ℝ} {T p δ c d : ℝ}
    (hcont :
      ContinuousOn (fun t => intervalDomainLpAbsEnergy p u t)
        (Set.Icc (0 : ℝ) T))
    (hderiv_within :
      ∀ t ∈ Set.Ico (0 : ℝ) T,
        HasDerivWithinAt
          (fun τ => intervalDomainLpAbsEnergy p u τ)
          (deriv (fun τ => intervalDomainLpAbsEnergy p u τ) t)
          (Set.Ici t) t)
    (hinit : intervalDomainLpAbsEnergy p u 0 ≤ δ)
    (hderiv_le :
      ∀ t ∈ Set.Ico (0 : ℝ) T,
        deriv (fun τ => intervalDomainLpAbsEnergy p u τ) t ≤
          c * intervalDomainLpAbsEnergy p u t + d) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      intervalDomainLpAbsEnergy p u t ≤ gronwallBound δ c d (t - 0) := by
  exact le_gronwallBound_of_liminf_deriv_right_le
    (f := fun t => intervalDomainLpAbsEnergy p u t)
    (f' := fun t => deriv (fun τ => intervalDomainLpAbsEnergy p u τ) t)
    (δ := δ) (K := c) (ε := d) (a := 0) (b := T)
    hcont
    (fun t ht r hr => (hderiv_within t ht).liminf_right_slope_le hr)
    hinit
    hderiv_le

/-- A Gronwall estimate on `[0,T]` gives a uniform absolute Lp bound on
`(0,T)`. -/
theorem intervalDomain_Lp_abs_energy_bounded_before_of_gronwall
    {u : ℝ → intervalDomain.Point → ℝ} {T p δ c d : ℝ}
    (hδ_nonneg : 0 ≤ δ) (hc_nonneg : 0 ≤ c) (hd_nonneg : 0 ≤ d)
    (hcont :
      ContinuousOn (fun t => intervalDomainLpAbsEnergy p u t)
        (Set.Icc (0 : ℝ) T))
    (hderiv_within :
      ∀ t ∈ Set.Ico (0 : ℝ) T,
        HasDerivWithinAt
          (fun τ => intervalDomainLpAbsEnergy p u τ)
          (deriv (fun τ => intervalDomainLpAbsEnergy p u τ) t)
          (Set.Ici t) t)
    (hinit : intervalDomainLpAbsEnergy p u 0 ≤ δ)
    (hderiv_le :
      ∀ t ∈ Set.Ico (0 : ℝ) T,
        deriv (fun τ => intervalDomainLpAbsEnergy p u τ) t ≤
          c * intervalDomainLpAbsEnergy p u t + d) :
    ∃ C, ∀ t, 0 < t → t < T →
      intervalDomainLpAbsEnergy p u t ≤ C := by
  refine ⟨gronwallBound δ c d T, ?_⟩
  intro t ht0 htT
  have htIcc : t ∈ Set.Icc (0 : ℝ) T := ⟨le_of_lt ht0, le_of_lt htT⟩
  have hpoint :=
    intervalDomain_Lp_abs_energy_le_gronwallBound
      (u := u) (T := T) (p := p) (δ := δ) (c := c) (d := d)
      hcont hderiv_within hinit hderiv_le t htIcc
  have hmono := gronwallBound_mono hδ_nonneg hd_nonneg hc_nonneg
  have hleT : t - 0 ≤ T := by linarith
  exact hpoint.trans (hmono hleT)

/-- Convert a uniform absolute Lp-energy bound into the repository's
`LpPowerBoundedBefore` statement, under nonnegativity of the solution. -/
theorem intervalDomain_LpPowerBoundedBefore_of_abs_energy_bound
    {u : ℝ → intervalDomain.Point → ℝ} {T p C : ℝ}
    (hu_nonneg :
      ∀ t, 0 < t → t < T → ∀ x : intervalDomain.Point, 0 ≤ u t x)
    (habs_bound :
      ∀ t, 0 < t → t < T → intervalDomainLpAbsEnergy p u t ≤ C) :
    LpPowerBoundedBefore intervalDomain p T u := by
  refine ⟨C, ?_⟩
  intro t ht0 htT
  have hfun :
      (fun x : intervalDomain.Point => (u t x) ^ p) =
        fun x : intervalDomain.Point => |u t x| ^ p := by
    funext x
    rw [abs_of_nonneg (hu_nonneg t ht0 htT x)]
  have henergy_eq :
      intervalDomain.integral (fun x : intervalDomain.Point => (u t x) ^ p) =
        intervalDomainLpAbsEnergy p u t := by
    simp [intervalDomainLpAbsEnergy, hfun]
  rw [henergy_eq]
  exact habs_bound t ht0 htT

/-- Gronwall plus nonnegativity gives the standard uniform Lp bound
`LpPowerBoundedBefore`. -/
theorem intervalDomain_LpPowerBoundedBefore_of_abs_energy_gronwall
    {u : ℝ → intervalDomain.Point → ℝ} {T p δ c d : ℝ}
    (hδ_nonneg : 0 ≤ δ) (hc_nonneg : 0 ≤ c) (hd_nonneg : 0 ≤ d)
    (hu_nonneg :
      ∀ t, 0 < t → t < T → ∀ x : intervalDomain.Point, 0 ≤ u t x)
    (hcont :
      ContinuousOn (fun t => intervalDomainLpAbsEnergy p u t)
        (Set.Icc (0 : ℝ) T))
    (hderiv_within :
      ∀ t ∈ Set.Ico (0 : ℝ) T,
        HasDerivWithinAt
          (fun τ => intervalDomainLpAbsEnergy p u τ)
          (deriv (fun τ => intervalDomainLpAbsEnergy p u τ) t)
          (Set.Ici t) t)
    (hinit : intervalDomainLpAbsEnergy p u 0 ≤ δ)
    (hderiv_le :
      ∀ t ∈ Set.Ico (0 : ℝ) T,
        deriv (fun τ => intervalDomainLpAbsEnergy p u τ) t ≤
          c * intervalDomainLpAbsEnergy p u t + d) :
    LpPowerBoundedBefore intervalDomain p T u := by
  rcases intervalDomain_Lp_abs_energy_bounded_before_of_gronwall
      (u := u) (T := T) (p := p) (δ := δ) (c := c) (d := d)
      hδ_nonneg hc_nonneg hd_nonneg hcont hderiv_within hinit hderiv_le with
    ⟨C, hC⟩
  exact intervalDomain_LpPowerBoundedBefore_of_abs_energy_bound
    (u := u) (T := T) (p := p) (C := C) hu_nonneg hC

/-- Drop nonnegative terms and a uniformly bounded right-hand side from the
assembled Lp Gronwall differential inequality, yielding the scalar derivative
bound used by `intervalDomain_LpPowerBoundedBefore_of_abs_energy_gronwall`. -/
theorem intervalDomain_Lp_abs_energy_deriv_le_of_energy_source_bound
    {u : ℝ → intervalDomain.Point → ℝ}
    {T p rho A B K L_const R : ℝ}
    (hp : 0 < p)
    (henergy :
      ∀ t ∈ Set.Ico (0 : ℝ) T,
        (1 / p) * deriv (fun τ => intervalDomainLpAbsEnergy p u τ) t +
            A * intervalDomainLpGradientEnergy p u t +
            B * intervalDomainLpAbsEnergy p u t ≤
          K * intervalDomainLpAbsEnergy (p + rho) u t + L_const)
    (hdrop :
      ∀ t ∈ Set.Ico (0 : ℝ) T,
        0 ≤ A * intervalDomainLpGradientEnergy p u t +
          B * intervalDomainLpAbsEnergy p u t)
    (hsource :
      ∀ t ∈ Set.Ico (0 : ℝ) T,
        K * intervalDomainLpAbsEnergy (p + rho) u t + L_const ≤ R) :
    ∀ t ∈ Set.Ico (0 : ℝ) T,
      deriv (fun τ => intervalDomainLpAbsEnergy p u τ) t ≤
        0 * intervalDomainLpAbsEnergy p u t + p * R := by
  intro t ht
  have hscaled :
      (1 / p) * deriv (fun τ => intervalDomainLpAbsEnergy p u τ) t ≤ R := by
    have hfull := henergy t ht
    have hdrop_t := hdrop t ht
    have hsource_t := hsource t ht
    linarith
  have hmul := mul_le_mul_of_nonneg_left hscaled hp.le
  have hident :
      p * ((1 / p) * deriv (fun τ => intervalDomainLpAbsEnergy p u τ) t) =
        deriv (fun τ => intervalDomainLpAbsEnergy p u τ) t := by
    field_simp [ne_of_gt hp]
  calc
    deriv (fun τ => intervalDomainLpAbsEnergy p u τ) t =
        p * ((1 / p) * deriv (fun τ => intervalDomainLpAbsEnergy p u τ) t) :=
          hident.symm
    _ ≤ p * R := hmul
    _ = 0 * intervalDomainLpAbsEnergy p u t + p * R := by ring

/-- From the assembled Lp Gronwall inequality plus a uniform source bound,
derive `LpPowerBoundedBefore` for the current exponent.

The hypotheses at `t = 0` are kept explicit: they are the initial trace and
right-derivative regularity needed by Mathlib's Gronwall theorem. -/
theorem intervalDomain_LpPowerBoundedBefore_of_energy_gronwall_source_bound
    {u : ℝ → intervalDomain.Point → ℝ}
    {T p rho A B K L_const R δ : ℝ}
    (hp : 0 < p) (hδ_nonneg : 0 ≤ δ) (hR_nonneg : 0 ≤ R)
    (hu_nonneg :
      ∀ t, 0 < t → t < T → ∀ x : intervalDomain.Point, 0 ≤ u t x)
    (hcont :
      ContinuousOn (fun t => intervalDomainLpAbsEnergy p u t)
        (Set.Icc (0 : ℝ) T))
    (hderiv_within :
      ∀ t ∈ Set.Ico (0 : ℝ) T,
        HasDerivWithinAt
          (fun τ => intervalDomainLpAbsEnergy p u τ)
          (deriv (fun τ => intervalDomainLpAbsEnergy p u τ) t)
          (Set.Ici t) t)
    (hinit : intervalDomainLpAbsEnergy p u 0 ≤ δ)
    (henergy :
      ∀ t ∈ Set.Ico (0 : ℝ) T,
        (1 / p) * deriv (fun τ => intervalDomainLpAbsEnergy p u τ) t +
            A * intervalDomainLpGradientEnergy p u t +
            B * intervalDomainLpAbsEnergy p u t ≤
          K * intervalDomainLpAbsEnergy (p + rho) u t + L_const)
    (hdrop :
      ∀ t ∈ Set.Ico (0 : ℝ) T,
        0 ≤ A * intervalDomainLpGradientEnergy p u t +
          B * intervalDomainLpAbsEnergy p u t)
    (hsource :
      ∀ t ∈ Set.Ico (0 : ℝ) T,
        K * intervalDomainLpAbsEnergy (p + rho) u t + L_const ≤ R) :
    LpPowerBoundedBefore intervalDomain p T u := by
  have hderiv_le :
      ∀ t ∈ Set.Ico (0 : ℝ) T,
        deriv (fun τ => intervalDomainLpAbsEnergy p u τ) t ≤
          0 * intervalDomainLpAbsEnergy p u t + p * R :=
    intervalDomain_Lp_abs_energy_deriv_le_of_energy_source_bound
      (u := u) (T := T) (p := p) (rho := rho)
      (A := A) (B := B) (K := K) (L_const := L_const) (R := R)
      hp henergy hdrop hsource
  exact intervalDomain_LpPowerBoundedBefore_of_abs_energy_gronwall
    (u := u) (T := T) (p := p) (δ := δ) (c := 0) (d := p * R)
    hδ_nonneg (by norm_num) (mul_nonneg hp.le hR_nonneg)
    hu_nonneg hcont hderiv_within hinit hderiv_le

lemma rpow_le_one_add_rpow_of_nonneg_of_le
    {a p q : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpq : p ≤ q) :
    a ^ p ≤ a ^ q + 1 := by
  by_cases ha_le_one : a ≤ 1
  · have hle_one : a ^ p ≤ 1 := Real.rpow_le_one ha ha_le_one hp
    have hq_nonneg : 0 ≤ a ^ q := Real.rpow_nonneg ha q
    linarith
  · have hone_le : 1 ≤ a := le_of_not_ge ha_le_one
    have hpq_pow : a ^ p ≤ a ^ q :=
      Real.rpow_le_rpow_of_exponent_le hone_le hpq
    linarith

/-- On `intervalDomain = [0,1]`, an L^q power bound gives an L^p power bound
for `1 < p ≤ q`, provided the solution is nonnegative and the two power traces
are interval-integrable on each time slice. -/
theorem intervalDomain_LpPowerBoundedBefore_mono_of_integrable_nonneg
    {u : ℝ → intervalDomain.Point → ℝ} {T p q : ℝ}
    (hp : 1 < p) (hpq : p ≤ q)
    (hu_nonneg :
      ∀ t, 0 < t → t < T → ∀ x : intervalDomain.Point, 0 ≤ u t x)
    (hp_int :
      ∀ t, 0 < t → t < T →
        IntervalIntegrable
          (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ p))
          MeasureTheory.volume 0 1)
    (hq_int :
      ∀ t, 0 < t → t < T →
        IntervalIntegrable
          (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ q))
          MeasureTheory.volume 0 1)
    (hq_bound : LpPowerBoundedBefore intervalDomain q T u) :
    LpPowerBoundedBefore intervalDomain p T u := by
  rcases hq_bound with ⟨Cq, hCq⟩
  refine ⟨Cq + 1, ?_⟩
  intro t ht0 htT
  have hp_nonneg : 0 ≤ p := le_trans zero_le_one hp.le
  have hpoint :
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        intervalDomainLift (fun y : intervalDomain.Point => (u t y) ^ p) x ≤
          intervalDomainLift (fun y : intervalDomain.Point => (u t y) ^ q) x + 1 := by
    intro x hx
    simp only [intervalDomainLift, dif_pos hx]
    exact rpow_le_one_add_rpow_of_nonneg_of_le
      (hu_nonneg t ht0 htT ⟨x, hx⟩) hp_nonneg hpq
  have hmono :
      (∫ x in (0 : ℝ)..1,
          intervalDomainLift (fun y : intervalDomain.Point => (u t y) ^ p) x) ≤
        (∫ x in (0 : ℝ)..1,
          intervalDomainLift (fun y : intervalDomain.Point => (u t y) ^ q) x) + 1 := by
    have hle :=
      intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
        (hp_int t ht0 htT)
        ((hq_int t ht0 htT).add intervalIntegrable_const)
        hpoint
    have hadd :
        ∫ x in (0 : ℝ)..1,
            (intervalDomainLift (fun y : intervalDomain.Point => (u t y) ^ q) x + 1) =
          (∫ x in (0 : ℝ)..1,
            intervalDomainLift (fun y : intervalDomain.Point => (u t y) ^ q) x) + 1 := by
      rw [intervalIntegral.integral_add (hq_int t ht0 htT) intervalIntegrable_const,
        intervalIntegral.integral_const]
      norm_num [smul_eq_mul]
    simpa [hadd] using hle
  have hq_t : intervalDomain.integral (fun x => (u t x) ^ q) ≤ Cq :=
    hCq t ht0 htT
  have hq_t_int :
      (∫ x in (0 : ℝ)..1,
          intervalDomainLift (fun y : intervalDomain.Point => (u t y) ^ q) x) ≤ Cq := by
    simpa [intervalDomain, intervalDomainIntegral] using hq_t
  have htarget :
      (∫ x in (0 : ℝ)..1,
          intervalDomainLift (fun y : intervalDomain.Point => (u t y) ^ q) x) + 1 ≤
        Cq + 1 := by
    linarith
  change
    (∫ x in (0 : ℝ)..1,
        intervalDomainLift (fun y : intervalDomain.Point => (u t y) ^ p) x) ≤ Cq + 1
  exact le_trans hmono htarget

/-- Interior-nonnegative version of
`intervalDomain_LpPowerBoundedBefore_mono_of_integrable_nonneg`.

The interval integral is over `(0,1)` up to endpoints of measure zero, so the
pointwise comparison only needs nonnegativity on `intervalDomain.inside`. -/
theorem intervalDomain_LpPowerBoundedBefore_mono_of_integrable_inside_nonneg
    {u : ℝ → intervalDomain.Point → ℝ} {T p q : ℝ}
    (hp : 1 < p) (hpq : p ≤ q)
    (hu_nonneg :
      ∀ t, 0 < t → t < T →
        ∀ x : intervalDomain.Point, x ∈ intervalDomain.inside → 0 ≤ u t x)
    (hp_int :
      ∀ t, 0 < t → t < T →
        IntervalIntegrable
          (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ p))
          MeasureTheory.volume 0 1)
    (hq_int :
      ∀ t, 0 < t → t < T →
        IntervalIntegrable
          (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ q))
          MeasureTheory.volume 0 1)
    (hq_bound : LpPowerBoundedBefore intervalDomain q T u) :
    LpPowerBoundedBefore intervalDomain p T u := by
  rcases hq_bound with ⟨Cq, hCq⟩
  refine ⟨Cq + 1, ?_⟩
  intro t ht0 htT
  have hp_nonneg : 0 ≤ p := le_trans zero_le_one hp.le
  have hpoint :
      ∀ x ∈ Set.Ioo (0 : ℝ) 1,
        intervalDomainLift (fun y : intervalDomain.Point => (u t y) ^ p) x ≤
          intervalDomainLift (fun y : intervalDomain.Point => (u t y) ^ q) x + 1 := by
    intro x hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    have hx_inside : (⟨x, hxIcc⟩ : intervalDomain.Point) ∈ intervalDomain.inside := by
      simpa [intervalDomain] using hx
    simp only [intervalDomainLift, dif_pos hxIcc]
    exact rpow_le_one_add_rpow_of_nonneg_of_le
      (hu_nonneg t ht0 htT ⟨x, hxIcc⟩ hx_inside) hp_nonneg hpq
  have hmono :
      (∫ x in (0 : ℝ)..1,
          intervalDomainLift (fun y : intervalDomain.Point => (u t y) ^ p) x) ≤
        (∫ x in (0 : ℝ)..1,
          intervalDomainLift (fun y : intervalDomain.Point => (u t y) ^ q) x) + 1 := by
    have hle :=
      intervalIntegral.integral_mono_on_of_le_Ioo
        (by norm_num : (0 : ℝ) ≤ 1)
        (hp_int t ht0 htT)
        ((hq_int t ht0 htT).add intervalIntegrable_const)
        hpoint
    have hadd :
        ∫ x in (0 : ℝ)..1,
            (intervalDomainLift (fun y : intervalDomain.Point => (u t y) ^ q) x + 1) =
          (∫ x in (0 : ℝ)..1,
            intervalDomainLift (fun y : intervalDomain.Point => (u t y) ^ q) x) + 1 := by
      rw [intervalIntegral.integral_add (hq_int t ht0 htT) intervalIntegrable_const,
        intervalIntegral.integral_const]
      norm_num [smul_eq_mul]
    simpa [hadd] using hle
  have hq_t : intervalDomain.integral (fun x => (u t x) ^ q) ≤ Cq :=
    hCq t ht0 htT
  have hq_t_int :
      (∫ x in (0 : ℝ)..1,
          intervalDomainLift (fun y : intervalDomain.Point => (u t y) ^ q) x) ≤ Cq := by
    simpa [intervalDomain, intervalDomainIntegral] using hq_t
  have htarget :
      (∫ x in (0 : ℝ)..1,
          intervalDomainLift (fun y : intervalDomain.Point => (u t y) ^ q) x) + 1 ≤
        Cq + 1 := by
    linarith
  change
    (∫ x in (0 : ℝ)..1,
        intervalDomainLift (fun y : intervalDomain.Point => (u t y) ^ p) x) ≤ Cq + 1
  exact le_trans hmono htarget

/-- Feed an arithmetic chain of Gronwall-produced Lp bounds into the concrete
finite-interval Moser closure. -/
theorem intervalDomain_all_exponents_of_LpPowerBoundedBefore_chain
    {u : ℝ → intervalDomain.Point → ℝ} {T p0 rho : ℝ}
    (hrho : 0 < rho)
    (hchain : ∀ n : ℕ, LpPowerBoundedBefore intervalDomain (p0 + n * rho) T u)
    (hu_nonneg :
      ∀ t, 0 < t → t < T → ∀ x : intervalDomain.Point, 0 ≤ u t x)
    (hpow_int :
      ∀ pExp : ℝ, 1 < pExp → ∀ t, 0 < t → t < T →
        IntervalIntegrable
          (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ pExp))
          MeasureTheory.volume 0 1) :
    ∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u := by
  exact IntervalDomainMoserClosure.all_exponents_of_chain_and_lp_mono
    hrho hchain (fun {p q} hp hpq hq_bound =>
      intervalDomain_LpPowerBoundedBefore_mono_of_integrable_nonneg
        (p := p) (q := q) hp hpq hu_nonneg
        (hpow_int p hp)
        (hpow_int q (lt_of_lt_of_le hp hpq))
        hq_bound)

/-- Same Moser closure from a Gronwall-produced exponent chain, with
nonnegativity required only on the open interval carrying the integral. -/
theorem intervalDomain_all_exponents_of_LpPowerBoundedBefore_chain_inside_nonneg
    {u : ℝ → intervalDomain.Point → ℝ} {T p0 rho : ℝ}
    (hrho : 0 < rho)
    (hchain : ∀ n : ℕ, LpPowerBoundedBefore intervalDomain (p0 + n * rho) T u)
    (hu_nonneg :
      ∀ t, 0 < t → t < T →
        ∀ x : intervalDomain.Point, x ∈ intervalDomain.inside → 0 ≤ u t x)
    (hpow_int :
      ∀ pExp : ℝ, 1 < pExp → ∀ t, 0 < t → t < T →
        IntervalIntegrable
          (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ pExp))
          MeasureTheory.volume 0 1) :
    ∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u := by
  exact IntervalDomainMoserClosure.all_exponents_of_chain_and_lp_mono
    hrho hchain (fun {p q} hp hpq hq_bound =>
      intervalDomain_LpPowerBoundedBefore_mono_of_integrable_inside_nonneg
        (p := p) (q := q) hp hpq hu_nonneg
        (hpow_int p hp)
        (hpow_int q (lt_of_lt_of_le hp hpq))
        hq_bound)

/-- Interval-domain Moser chain closure with the concrete finite-interval Lp
monotonicity lemma above.  The remaining hypotheses are the standard PDE
regularity facts: nonnegativity and integrability of all time-slice powers. -/
theorem intervalDomain_all_exponents_of_moser_iteration_chain
    {u : ℝ → intervalDomain.Point → ℝ} {T p0 rho : ℝ}
    (hrho : 0 < rho)
    (hbase : LpPowerBoundedBefore intervalDomain p0 T u)
    (hstep : ∀ p, p0 ≤ p →
      ∃ A > 0, ∃ K > 0, ∃ L_const,
        (∀ t, 0 < t → t < T →
          A * intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) ≤
          K * intervalDomain.integral (fun x => (u t x) ^ (p + rho)) + L_const) ∧
        (∀ eps > 0, ∃ Ceps, ∀ t, 0 < t → t < T →
          intervalDomain.integral (fun x => (u t x) ^ (p + rho)) ≤
            eps * intervalDomain.integral (fun x =>
              (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
            Ceps))
    (hu_nonneg :
      ∀ t, 0 < t → t < T → ∀ x : intervalDomain.Point, 0 ≤ u t x)
    (hpow_int :
      ∀ pExp : ℝ, 1 < pExp → ∀ t, 0 < t → t < T →
        IntervalIntegrable
          (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ pExp))
          MeasureTheory.volume 0 1) :
    ∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u := by
  exact IntervalDomainMoserClosure.all_exponents_of_moser_iteration_chain
    hrho hbase hstep (fun {p q} hp hpq hq_bound =>
      intervalDomain_LpPowerBoundedBefore_mono_of_integrable_nonneg
        (p := p) (q := q) hp hpq hu_nonneg
        (hpow_int p hp)
        (hpow_int q (lt_of_lt_of_le hp hpq))
        hq_bound)

/-- Same Moser closure, with nonnegativity only required on the open interval
where the interval integral lives. -/
theorem intervalDomain_all_exponents_of_moser_iteration_chain_inside_nonneg
    {u : ℝ → intervalDomain.Point → ℝ} {T p0 rho : ℝ}
    (hrho : 0 < rho)
    (hbase : LpPowerBoundedBefore intervalDomain p0 T u)
    (hstep : ∀ p, p0 ≤ p →
      ∃ A > 0, ∃ K > 0, ∃ L_const,
        (∀ t, 0 < t → t < T →
          A * intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) ≤
          K * intervalDomain.integral (fun x => (u t x) ^ (p + rho)) + L_const) ∧
        (∀ eps > 0, ∃ Ceps, ∀ t, 0 < t → t < T →
          intervalDomain.integral (fun x => (u t x) ^ (p + rho)) ≤
            eps * intervalDomain.integral (fun x =>
              (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
            Ceps))
    (hu_nonneg :
      ∀ t, 0 < t → t < T →
        ∀ x : intervalDomain.Point, x ∈ intervalDomain.inside → 0 ≤ u t x)
    (hpow_int :
      ∀ pExp : ℝ, 1 < pExp → ∀ t, 0 < t → t < T →
        IntervalIntegrable
          (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ pExp))
          MeasureTheory.volume 0 1) :
    ∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u := by
  exact IntervalDomainMoserClosure.all_exponents_of_moser_iteration_chain
    hrho hbase hstep (fun {p q} hp hpq hq_bound =>
      intervalDomain_LpPowerBoundedBefore_mono_of_integrable_inside_nonneg
        (p := p) (q := q) hp hpq hu_nonneg
        (hpow_int p hp)
        (hpow_int q (lt_of_lt_of_le hp hpq))
        hq_bound)

end ShenWork.Paper2.IntervalDomainLpMonotonicity

end
