/-
  ShenWork/Paper2/IntervalDomainL2HalfEnergyTimeLeibniz.lean

  **T5 tail R1 — the single-solution time-Leibniz chain rule `hL2Time`.**

  The L² half-energy `½∫₀¹ u² ` differentiates in time to the weighted-time term
  `∫₀¹ u·∂ₜu`:

    `d/dt (½ ∫₀¹ (u t)²) = ∫₀¹ (u t)·(∂ₜ u t)`,

  which is exactly the `hL2Time` frontier consumed by the L²-energy inequality
  (`intervalDomain_l2_half_energy_inequality_of_cosineProfile{,_interior}`).  This
  is the single-solution mirror of the difference-energy reduction
  `intervalDomainClassicalL2DifferenceEnergy_hasDerivAt_of_slabContinuous`.

  The key simplification over the *spatial* IBP: here the derivative is in TIME,
  so the spatial jump of `intervalDomainLift` at the endpoints is irrelevant.  For
  every fixed `y ∈ [0,1]` (endpoints included), `intervalDomainLift (u r) y = u r
  ⟨y⟩` for ALL `r`, so the time-derivative field
  `(lift (u s) y)·∂ₜ(lift (u·) y)` agrees with `lift (u·∂ₜu)` on the *whole*
  `[0,1]` — no almost-everywhere argument needed.

  Reduction chain (mirrors `IntervalDomainL2EnergyInequality`):
  * `intervalDomainHalfEnergyIntegrand_hasDerivAt_interior` — (D1): the integrand
    time-slice has the expected derivative on a localization ball `⊆ (0,T)` and at
    a.e. interior `y`, from the 4th regularity conjunct + the square chain rule.
  * `intervalDomainL2HalfEnergy_hasDerivAt_of_envelope` — localized Leibniz from an
    integrable (D2) envelope.
  * `intervalDomainL2HalfEnergy_hasDerivAt_of_slabContinuous` — (D2) from closed-
    slab joint continuity of the integrand-derivative field, via
    `exists_bound_of_continuousOn_slab`.
  * `intervalDomain_l2_half_energy_hL2Time_of_slabContinuous` — assembles the exact
    `hL2Time` equation `deriv (½∫u²) = ∫ u·∂ₜu`.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainNeumannIBP
import ShenWork.Paper2.IntervalDomainL2EnergyInequality
import ShenWork.PDE.IntervalUnderIntegralLeibniz

open ShenWork.IntervalDomain MeasureTheory
open ShenWork.IntervalUnderIntegralLeibniz
open ShenWork.Paper2.IntervalDomainLpMonotonicity
open scoped Topology

namespace ShenWork.Paper2

noncomputable section

open ShenWork.Paper2.IntervalDomainEnergyStep

/-- The lift of a pointwise square is the square of the lift (everywhere on `ℝ`:
both sides vanish off `[0,1]`). -/
theorem intervalDomainLift_sq (f : intervalDomain.Point → ℝ) (y : ℝ) :
    intervalDomainLift (fun x => (f x) ^ 2) y = (intervalDomainLift f y) ^ 2 := by
  unfold intervalDomainLift
  by_cases hy : y ∈ Set.Icc (0 : ℝ) 1 <;> simp [hy]

/-- The per-`x` integrand `½ (lift (u s) y)²` of the L² half-energy, as a family in
`(s, y)`. -/
def intervalDomainHalfEnergyIntegrand
    (u : ℝ → intervalDomain.Point → ℝ) (s y : ℝ) : ℝ :=
  (1 / 2) * (intervalDomainLift (u s) y) ^ 2

/-- The time-derivative field `(lift (u s) y)·∂ₜ(lift (u·) y)` of the half-energy
integrand. -/
def intervalDomainHalfEnergyIntegrandDeriv
    (u : ℝ → intervalDomain.Point → ℝ) (s y : ℝ) : ℝ :=
  intervalDomainLift (u s) y *
    deriv (fun r => intervalDomainLift (u r) y) s

/-- The L² half-energy as a plain interval integral of the lifted squared slice. -/
theorem intervalDomainL2HalfEnergy_eq_integral
    (u : ℝ → intervalDomain.Point → ℝ) (t : ℝ) :
    intervalDomainL2HalfEnergy u t
      = ∫ y in (0 : ℝ)..1, intervalDomainHalfEnergyIntegrand u t y := by
  unfold intervalDomainL2HalfEnergy intervalDomain
  change (1 / 2 : ℝ) * intervalDomainIntegral (fun x => (u t x) ^ 2) = _
  unfold intervalDomainIntegral intervalDomainHalfEnergyIntegrand
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun y _ => ?_)
  rw [intervalDomainLift_sq]

/-- **(D1), discharged on the localization ball.**  For an interior spatial point
`y ∈ (0,1)` and every interior time `s ∈ (0,T)`, the half-energy integrand
`r ↦ intervalDomainHalfEnergyIntegrand u r y` has the stated time derivative.
Uses the interior-time-differentiability conjunct (`intervalDomain_timeDeriv_isGenuine`)
at the interior time `s` together with the square chain rule, lifted through
`intervalDomainLift` on the interior branch. -/
theorem intervalDomainHalfEnergyIntegrand_hasDerivAt_interior
    {p : CM2Params} {T : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1)
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt
      (fun r => intervalDomainHalfEnergyIntegrand u r y)
      (intervalDomainHalfEnergyIntegrandDeriv u s y) s := by
  classical
  have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hy
  set x : intervalDomain.Point := ⟨y, hyIcc⟩ with hx
  have hxIoo : (x.1 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := hy
  have hlift : ∀ r : ℝ, intervalDomainLift (u r) y = u r x := by
    intro r; simp [intervalDomainLift, hyIcc, hx]
  -- Genuine pointwise time derivative of the slice at the interior time `s`.
  have hw : HasDerivAt (fun r : ℝ => u r x) (intervalDomain.timeDeriv u s x) s :=
    intervalDomain_timeDeriv_isGenuine hsol hxIoo hs
  -- Square chain rule, then the `½` constant factor.
  have hsq : HasDerivAt (fun r : ℝ => (1 / 2 : ℝ) * (u r x) ^ 2)
      (u s x * intervalDomain.timeDeriv u s x) s := by
    have hp := (hw.pow 2).const_mul (1 / 2 : ℝ)
    convert hp using 1
    rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    push_cast
    ring
  -- Rewrite the integrand to the slice form.
  have hfun : (fun r => intervalDomainHalfEnergyIntegrand u r y)
      = fun r => (1 / 2 : ℝ) * (u r x) ^ 2 := by
    funext r; simp [intervalDomainHalfEnergyIntegrand, hlift r]
  rw [hfun]
  -- Rewrite the derivative value to the slice form.
  have hval : intervalDomainHalfEnergyIntegrandDeriv u s y
      = u s x * intervalDomain.timeDeriv u s x := by
    unfold intervalDomainHalfEnergyIntegrandDeriv
    rw [hlift s]
    have hfun2 : (fun r => intervalDomainLift (u r) y) = fun r => u r x := funext hlift
    rw [hfun2]
    rfl
  rw [hval]
  exact hsq

/-- **The half-energy time derivative from an integrable (D2) envelope.**  Given an
integrable dominating envelope `bound` for the integrand's time-derivative field,
uniform over a localization ball `Metric.ball τ δ ⊆ (0,T)`, the L² half-energy has
a genuine time derivative `∫₀¹ ∂τ[½ (lift (u τ))²]` at `τ`.  (D1) is supplied by
`intervalDomainHalfEnergyIntegrand_hasDerivAt_interior`. -/
theorem intervalDomainL2HalfEnergy_hasDerivAt_of_envelope
    {p : CM2Params} {T : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {τ δ : ℝ} (hδ : 0 < δ)
    (hball : Metric.ball τ δ ⊆ Set.Ioo (0 : ℝ) T)
    {bound : ℝ → ℝ}
    (hF_meas : ∀ᶠ s in 𝓝 τ,
        AEStronglyMeasurable
          (intervalDomainHalfEnergyIntegrand u s)
          intervalDomainInteriorMeasure)
    (hF_int : IntervalIntegrable
        (intervalDomainHalfEnergyIntegrand u τ) volume 0 1)
    (hF'_meas : AEStronglyMeasurable
        (intervalDomainHalfEnergyIntegrandDeriv u τ)
        intervalDomainInteriorMeasure)
    (h_bound : ∀ᵐ y ∂intervalDomainInteriorMeasure,
        ∀ s ∈ Metric.ball τ δ,
          ‖intervalDomainHalfEnergyIntegrandDeriv u s y‖ ≤ bound y)
    (hbound_int : Integrable bound intervalDomainInteriorMeasure) :
    HasDerivAt
      (fun s => intervalDomainL2HalfEnergy u s)
      (∫ y in (0 : ℝ)..1,
        intervalDomainHalfEnergyIntegrandDeriv u τ y) τ := by
  have h_diff : ∀ᵐ y ∂intervalDomainInteriorMeasure,
      ∀ s ∈ Metric.ball τ δ,
        HasDerivAt (fun r => intervalDomainHalfEnergyIntegrand u r y)
          (intervalDomainHalfEnergyIntegrandDeriv u s y) s := by
    refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
    refine Filter.Eventually.of_forall (fun y hy s hs => ?_)
    exact intervalDomainHalfEnergyIntegrand_hasDerivAt_interior hsol hy (hball hs)
  have hderiv :
      HasDerivAt
        (fun s => ∫ y in (0 : ℝ)..1, intervalDomainHalfEnergyIntegrand u s y)
        (∫ y in (0 : ℝ)..1, intervalDomainHalfEnergyIntegrandDeriv u τ y) τ :=
    intervalIntegral_hasDerivAt_time_of_local hδ hF_meas hF_int hF'_meas
      h_bound hbound_int h_diff
  have hEeq : (fun s => intervalDomainL2HalfEnergy u s)
      = fun s => ∫ y in (0 : ℝ)..1, intervalDomainHalfEnergyIntegrand u s y := by
    funext s; rw [intervalDomainL2HalfEnergy_eq_integral]
  rw [hEeq]
  exact hderiv

/-- **The half-energy time derivative from closed-slab joint continuity.**  If the
integrand's time-derivative field is jointly continuous on the closed slab
`Icc(τ−δ,τ+δ) ×ˢ Icc 0 1`, then `exists_bound_of_continuousOn_slab` supplies the
(D2) envelope and the L² half-energy has a genuine time derivative at `τ`.  This is
the single-solution mirror of
`intervalDomainClassicalL2DifferenceEnergy_hasDerivAt_of_slabContinuous`. -/
theorem intervalDomainL2HalfEnergy_hasDerivAt_of_slabContinuous
    {p : CM2Params} {T : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {τ δ : ℝ} (hδ : 0 < δ)
    (hball : Metric.ball τ δ ⊆ Set.Ioo (0 : ℝ) T)
    (hF_meas : ∀ᶠ s in 𝓝 τ,
        AEStronglyMeasurable
          (intervalDomainHalfEnergyIntegrand u s)
          intervalDomainInteriorMeasure)
    (hF_int : IntervalIntegrable
        (intervalDomainHalfEnergyIntegrand u τ) volume 0 1)
    (hF'_meas : AEStronglyMeasurable
        (intervalDomainHalfEnergyIntegrandDeriv u τ)
        intervalDomainInteriorMeasure)
    (hslab : ContinuousOn
        (Function.uncurry (intervalDomainHalfEnergyIntegrandDeriv u))
        (Set.Icc (τ - δ) (τ + δ) ×ˢ Set.Icc (0 : ℝ) 1)) :
    HasDerivAt
      (fun s => intervalDomainL2HalfEnergy u s)
      (∫ y in (0 : ℝ)..1,
        intervalDomainHalfEnergyIntegrandDeriv u τ y) τ := by
  obtain ⟨bound, hbound_int, h_bound⟩ :=
    exists_bound_of_continuousOn_slab hδ hslab
  exact intervalDomainL2HalfEnergy_hasDerivAt_of_envelope hsol hδ hball
    hF_meas hF_int hF'_meas h_bound hbound_int

/-- **The integral of the time-derivative field equals the weighted-time term.**
On all of `[0,1]` (endpoints included, since the derivative is in TIME and the
lift's branch value at any `y ∈ [0,1]` is the genuine slice value for every time),
`(lift (u t) y)·∂ₜ(lift (u·) y) = lift (u·∂ₜu)`, so the two interval integrals
coincide — no almost-everywhere argument is needed. -/
theorem intervalDomainHalfEnergyIntegrandDeriv_integral_eq_timeTerm
    (u : ℝ → intervalDomain.Point → ℝ) (t : ℝ) :
    (∫ y in (0 : ℝ)..1, intervalDomainHalfEnergyIntegrandDeriv u t y)
      = intervalDomain.integral (intervalDomainL2TimeTerm u t) := by
  classical
  change _ = intervalDomainIntegral (intervalDomainL2TimeTerm u t)
  unfold intervalDomainIntegral
  refine intervalIntegral.integral_congr (fun y hy => ?_)
  rw [Set.uIcc_of_le (zero_le_one)] at hy
  have hlift : ∀ r : ℝ, intervalDomainLift (u r) y = u r ⟨y, hy⟩ := by
    intro r; simp [intervalDomainLift, hy]
  have hfun : (fun r => intervalDomainLift (u r) y) = fun r => u r ⟨y, hy⟩ :=
    funext hlift
  -- RHS: the lift of `intervalDomainL2TimeTerm u t` at `y ∈ [0,1]`.
  have hRHS : intervalDomainLift (intervalDomainL2TimeTerm u t) y
      = intervalDomainL2TimeTerm u t ⟨y, hy⟩ := by
    simp [intervalDomainLift, hy]
  -- LHS: the integrand-derivative field at `y ∈ [0,1]`.
  unfold intervalDomainHalfEnergyIntegrandDeriv
  rw [hRHS, hlift t, hfun]
  rfl

/-- **The exact `hL2Time` equation, from closed-slab joint continuity.**  Assembles
the time-Leibniz chain rule

  `deriv (fun τ => ½∫₀¹ (u τ)²) t = ∫₀¹ (u t)·(∂ₜ u t) = intervalDomain.integral
   (intervalDomainL2TimeTerm u t)`,

the precise `hL2Time` frontier of the L²-energy inequality.  All inputs except the
closed-slab joint continuity of the integrand-derivative field (conjuncts (8)/(9))
and the measurability/integrability side conditions are discharged. -/
theorem intervalDomain_l2_half_energy_hL2Time_of_slabContinuous
    {p : CM2Params} {T : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {t δ : ℝ} (hδ : 0 < δ)
    (hball : Metric.ball t δ ⊆ Set.Ioo (0 : ℝ) T)
    (hF_meas : ∀ᶠ s in 𝓝 t,
        AEStronglyMeasurable
          (intervalDomainHalfEnergyIntegrand u s)
          intervalDomainInteriorMeasure)
    (hF_int : IntervalIntegrable
        (intervalDomainHalfEnergyIntegrand u t) volume 0 1)
    (hF'_meas : AEStronglyMeasurable
        (intervalDomainHalfEnergyIntegrandDeriv u t)
        intervalDomainInteriorMeasure)
    (hslab : ContinuousOn
        (Function.uncurry (intervalDomainHalfEnergyIntegrandDeriv u))
        (Set.Icc (t - δ) (t + δ) ×ˢ Set.Icc (0 : ℝ) 1)) :
    deriv (fun τ => intervalDomainL2HalfEnergy u τ) t =
      intervalDomain.integral (intervalDomainL2TimeTerm u t) := by
  have hHD := intervalDomainL2HalfEnergy_hasDerivAt_of_slabContinuous hsol hδ hball
    hF_meas hF_int hF'_meas hslab
  rw [hHD.deriv]
  exact intervalDomainHalfEnergyIntegrandDeriv_integral_eq_timeTerm u t

/-! ## Discharging the side conditions: `hL2Time` UNCONDITIONALLY from the
regularity conjuncts -/

/-- A jointly-continuous space-time field on the open-time/closed-space slab,
restricted to a fixed interior time, is continuous in space on `[0,1]`. -/
theorem intervalDomain_continuousOn_timeSlice
    {g : ℝ → ℝ → ℝ} {T t : ℝ}
    (hg : ContinuousOn (Function.uncurry g)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1))
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    ContinuousOn (fun x => g t x) (Set.Icc (0 : ℝ) 1) := by
  have hmap : ContinuousOn (fun x : ℝ => (t, x)) (Set.Icc (0 : ℝ) 1) :=
    (continuous_const.prodMk continuous_id).continuousOn
  have hsub : Set.MapsTo (fun x : ℝ => (t, x)) (Set.Icc (0 : ℝ) 1)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
    fun x hx => Set.mk_mem_prod ht hx
  exact hg.comp hmap hsub

/-- **Joint continuity of the half-energy integrand-derivative field, from the
regularity conjuncts.**  The field is the product of the solution field (conjunct
(9)) and its time-derivative field (conjunct (8)), both jointly continuous on
`Ioo 0 T ×ˢ Icc 0 1`. -/
theorem intervalDomainHalfEnergyIntegrandDeriv_continuousOn_of_regularity
    {p : CM2Params} {T : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v) :
    ContinuousOn (Function.uncurry (intervalDomainHalfEnergyIntegrandDeriv u))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
  have hreg := hsol.regularity
  have hc9 : ContinuousOn
      (Function.uncurry (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
    hreg.2.2.2.2.2.2.2.2.1
  have hc8 : ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) => deriv (fun s : ℝ => intervalDomainLift (u s) x) t))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
    hreg.2.2.2.2.2.2.2.1.1
  exact hc9.mul hc8

/-- **Continuity of the half-energy integrand at a fixed interior time.**  From
conjunct (9) (continuity of the solution field). -/
theorem intervalDomainHalfEnergyIntegrand_continuousOn_timeSlice
    {p : CM2Params} {T : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    ContinuousOn (intervalDomainHalfEnergyIntegrand u t) (Set.Icc (0 : ℝ) 1) := by
  have hc9 : ContinuousOn
      (Function.uncurry (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
    hsol.regularity.2.2.2.2.2.2.2.2.1
  have hlift : ContinuousOn (fun x => intervalDomainLift (u t) x) (Set.Icc (0 : ℝ) 1) :=
    intervalDomain_continuousOn_timeSlice hc9 ht
  have : ContinuousOn (fun y => (intervalDomainLift (u t) y) ^ 2) (Set.Icc (0 : ℝ) 1) :=
    hlift.pow 2
  exact this.const_mul (1 / 2)

/-- A closed time-slab `[t−δ,t+δ] ⊆ (0,T)` together with the open ball, for a
positive radius `δ`. -/
theorem exists_closedSlab_subset
    {t T : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    ∃ δ : ℝ, 0 < δ ∧ Metric.ball t δ ⊆ Set.Ioo (0 : ℝ) T ∧
      Set.Icc (t - δ) (t + δ) ⊆ Set.Ioo (0 : ℝ) T := by
  obtain ⟨δ', hδ'pos, hsub'⟩ := exists_ball_subset_Ioo ht
  refine ⟨δ' / 2, by positivity, ?_, ?_⟩
  · exact subset_trans (Metric.ball_subset_ball (by linarith)) hsub'
  · intro x hx
    apply hsub'
    rw [Metric.mem_ball, Real.dist_eq]
    rw [Set.mem_Icc] at hx
    rw [abs_lt]
    constructor <;> linarith [hx.1, hx.2]

/-- **`hL2Time`, UNCONDITIONALLY for any classical solution at an interior time.**
The single-solution time-Leibniz chain rule

  `deriv (fun τ => ½∫₀¹ (u τ)²) t = intervalDomain.integral (u·∂ₜu)`

holds for every `IsPaper2ClassicalSolution` and every interior time `t ∈ (0,T)`,
with NO extra hypotheses: the closed-slab joint continuity is the product of
conjuncts (8) and (9), and the measurability/integrability side conditions follow
from the same joint continuity by restriction to a fixed time.  This fully
discharges the `hL2Time` frontier of the L²-energy inequality from the regularity
conjuncts every classical solution carries. -/
theorem intervalDomain_l2_half_energy_hL2Time
    {p : CM2Params} {T : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    deriv (fun τ => intervalDomainL2HalfEnergy u τ) t =
      intervalDomain.integral (intervalDomainL2TimeTerm u t) := by
  obtain ⟨δ, hδ, hball, hIcc⟩ := exists_closedSlab_subset ht
  -- Joint continuity of the integrand-derivative field on the open-T slab.
  have hjoint := intervalDomainHalfEnergyIntegrandDeriv_continuousOn_of_regularity hsol
  -- (D2) input: continuity on the compact slab `[t−δ,t+δ] ×ˢ [0,1]`.
  have hslab : ContinuousOn
      (Function.uncurry (intervalDomainHalfEnergyIntegrandDeriv u))
      (Set.Icc (t - δ) (t + δ) ×ˢ Set.Icc (0 : ℝ) 1) :=
    hjoint.mono (Set.prod_mono hIcc (le_refl _))
  -- `hF'_meas`: the deriv field at `t` is continuous on `[0,1]`, hence a.e.-measurable.
  have hderiv_slice : ContinuousOn (intervalDomainHalfEnergyIntegrandDeriv u t)
      (Set.Icc (0 : ℝ) 1) :=
    intervalDomain_continuousOn_timeSlice hjoint ht
  have hF'_meas : AEStronglyMeasurable
      (intervalDomainHalfEnergyIntegrandDeriv u t) intervalDomainInteriorMeasure :=
    (hderiv_slice.mono Set.Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  -- `hF_int`: the integrand at `t` is continuous on `[0,1]`, hence interval-integrable.
  have hint_slice : ContinuousOn (intervalDomainHalfEnergyIntegrand u t)
      (Set.Icc (0 : ℝ) 1) :=
    intervalDomainHalfEnergyIntegrand_continuousOn_timeSlice hsol ht
  have hF_int : IntervalIntegrable
      (intervalDomainHalfEnergyIntegrand u t) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le (zero_le_one)]
  -- `hF_meas`: for `s` near `t` (hence in `(0,T)`) the integrand is a.e.-measurable.
  have hF_meas : ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable (intervalDomainHalfEnergyIntegrand u s)
        intervalDomainInteriorMeasure := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact ((intervalDomainHalfEnergyIntegrand_continuousOn_timeSlice hsol hs).mono
      Set.Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  exact intervalDomain_l2_half_energy_hL2Time_of_slabContinuous hsol hδ hball
    hF_meas hF_int hF'_meas hslab

end

end ShenWork.Paper2
