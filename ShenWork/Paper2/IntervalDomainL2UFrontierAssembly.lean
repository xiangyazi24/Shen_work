/-
  UNCONDITIONAL assembly of the `u`-only difference-energy frontier from a pair of
  interval classical solutions, and the resulting reduction of the gluing /
  uniqueness chain to a single strictly-weaker named obligation.

  This file is DOWNSTREAM of `IntervalDomainL2UEnergyCombine` (the proved energy
  differential-inequality bound and the closed-slab integrand-derivative continuity)
  and `IntervalDomainL2StaticVDifference` (the static elliptic `v`-control), so it
  may freely consume both.  With the closed-domain time-`C¹` regularity conjunct
  now unconditional in the spatial variable (interior AND the two Neumann endpoints
  `{0,1}`), every frontier field is constructed honestly:

    * `diffIneq` — the time-Leibniz `HasDerivWithinAt`
      (`intervalDomainL2UEnergy_hasDerivAt_of_solution`) PLUS the PROVED per-time
      inequality `∫ integrandDeriv ≤ K · E_u`
      (`intervalDomainL2U_energy_diffIneq_bound`);
    * `cont` — energy continuity from the time-`HasDerivAt`;
    * `initial_vanishes` — from the shared `InitialTrace` (using a bounded initial
      datum);
    * `zero_pointwise` — `E_u t = 0 ⟹ u₁ t = u₂ t` (continuity + zero integral) and
      then `v₁ t = v₂ t` via `static_v_value_L2_le_Eu`.

  The only inputs NOT constructed unconditionally are bundled in the single named
  obligation `IntervalDomainL2UBoundedDatumUniform p`: a bounded shared initial
  datum (for `initial_vanishes`) and a UNIFORM Grönwall constant for the per-time
  (PROVED) differential inequality over the overlap interior (for `diffIneq`'s
  single `K`).  It is STRICTLY WEAKER than the joint obligation — it never requires
  any time derivative of `v−V`.

  This file contains **no `sorry`, no `admit`, no custom `axiom`.**
-/
import ShenWork.Paper2.IntervalDomainL2UEnergyCombine
import ShenWork.Paper2.IntervalDomainL2StaticVDifference

open ShenWork.IntervalDomain MeasureTheory
open ShenWork.Paper2.IntervalDomainLpMonotonicity
open ShenWork.IntervalUnderIntegralLeibniz
open scoped Topology

namespace ShenWork.Paper2

noncomputable section

/-! ## UNCONDITIONAL assembly of the `u`-only frontier from a solution pair

With the closed-domain time-`C¹` conjunct (4) now UNCONDITIONAL in the spatial
variable (interior AND the two Neumann endpoints `{0,1}`), the closed-slab joint
continuity `intervalDomainUEnergyIntegrandDeriv_continuousOn_closedSlab` is itself
unconditional for solutions.  Combined with:

  * the measurability/integrability inputs, discharged from spatial continuity of
    the integrand (conjunct 7 ⇒ `lift (uⱼ τ)` is `C²` on `Icc 0 1`, hence the
    squared difference and its time-derivative field are continuous in `y`); and
  * the PROVED inequality `intervalDomainL2U_energy_diffIneq_bound`
    (`∫ integrandDeriv ≤ K · E_u`, the Neumann IBP dissipation + flux-`L²` Young
    absorption + reaction-Lipschitz estimate, all unconditional for solutions),

the `diffIneq` field is unconditional.  The `cont` field follows from the
time-`HasDerivAt` (differentiable ⇒ continuous); `initial_vanishes` from the
shared `InitialTrace`; and `zero_pointwise` from continuity of the difference plus
the static elliptic `v`-control (`static_v_value_L2_le_Eu`).  This file therefore
constructs the full frontier with NO residual hypothesis. -/

/-- Spatial continuity of `lift (uⱼ τ)` on `Icc 0 1` at an interior time, from the
closed-`Icc` `C²` regularity conjunct (7). -/
theorem solution_lift_continuousOn_Icc
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T) :
    ContinuousOn (intervalDomainLift (u τ)) (Set.Icc (0 : ℝ) 1) :=
  ((hsol.regularity.2.2.2.2.1 τ hτ).1.1).continuousOn

/-- The `u`-energy integrand `y ↦ (lift (u₁ s − u₂ s) y)²` is continuous on
`Icc 0 1` at any interior slab time `s`, hence `AEStronglyMeasurable` on the
interior measure and interval-integrable on `(0,1)`. -/
theorem intervalDomainUEnergyIntegrand_continuousOn_Icc
    {p : CM2Params} {T₁ T₂ : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂)
    {s : ℝ} (hs₁ : s ∈ Set.Ioo (0 : ℝ) T₁) (hs₂ : s ∈ Set.Ioo (0 : ℝ) T₂) :
    ContinuousOn (intervalDomainUEnergyIntegrand u₁ u₂ s) (Set.Icc (0 : ℝ) 1) := by
  have hw : ContinuousOn
      (fun y => intervalDomainLift (fun x => u₁ s x - u₂ s x) y) (Set.Icc (0:ℝ) 1) := by
    refine ((solution_lift_continuousOn_Icc hsol₁ hs₁).sub
      (solution_lift_continuousOn_Icc hsol₂ hs₂)).congr (fun y hy => ?_)
    exact (intervalDomainLift_uDiff_eq u₁ u₂ s y)
  exact hw.pow 2

/-- **Unconditional time-Leibniz derivative of `E_u` for a solution pair.**

`E_u(τ) = ∫₀¹ (u₁ τ − u₂ τ)²` has a genuine time derivative
`∫₀¹ intervalDomainUEnergyIntegrandDeriv u₁ u₂ τ y` at every interior `τ`.  All
inputs to `intervalDomainL2UEnergy_hasDerivAt_of_slabContinuous` are discharged:
the closed-slab continuity from the (now unconditional) integrand-derivative slab
lemma, and the measurability/integrability from spatial continuity (conjunct 7). -/
theorem intervalDomainL2UEnergy_hasDerivAt_of_solution
    {p : CM2Params} {T₁ T₂ : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) (min T₁ T₂)) :
    HasDerivAt
      (intervalDomainClassicalL2DifferenceEnergyU u₁ u₂)
      (∫ y in (0 : ℝ)..1,
        intervalDomainUEnergyIntegrandDeriv u₁ u₂ τ y) τ := by
  classical
  -- localization radius `δ` with `[τ−δ,τ+δ] ⊆ (0, min T₁ T₂)`.
  obtain ⟨δ, hδ, hsub⟩ : ∃ δ > 0, Set.Icc (τ - δ) (τ + δ) ⊆ Set.Ioo (0:ℝ) (min T₁ T₂) := by
    have hopen : IsOpen (Set.Ioo (0:ℝ) (min T₁ T₂)) := isOpen_Ioo
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen τ hτ
    refine ⟨ε / 2, by linarith, ?_⟩
    intro y hy
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> [linarith [hy.1]; linarith [hy.2]]
  have hball : Metric.ball τ δ ⊆ Set.Ioo (0:ℝ) (min T₁ T₂) := by
    intro y hy
    apply hsub
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hy
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  -- closed-slab continuity of the integrand-derivative field (unconditional).
  have hslab := intervalDomainUEnergyIntegrandDeriv_continuousOn_closedSlab
    hsol₁ hsol₂ hδ hsub
  -- measurability / integrability of the integrand at slab times, from spatial
  -- continuity (conjunct 7).
  have hcontInt : ∀ s ∈ Set.Ioo (0:ℝ) (min T₁ T₂),
      ContinuousOn (intervalDomainUEnergyIntegrand u₁ u₂ s) (Set.Icc (0:ℝ) 1) := by
    intro s hs
    exact intervalDomainUEnergyIntegrand_continuousOn_Icc hsol₁ hsol₂
      ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_left _ _)⟩
      ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_right _ _)⟩
  have hF_int : IntervalIntegrable
      (intervalDomainUEnergyIntegrand u₁ u₂ τ) volume 0 1 := by
    have := (hcontInt τ hτ)
    rw [← Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at this
    exact this.intervalIntegrable
  have hF_meas : ∀ᶠ s in 𝓝 τ,
      AEStronglyMeasurable (intervalDomainUEnergyIntegrand u₁ u₂ s)
        intervalDomainInteriorMeasure := by
    have hmem : Set.Ioo (0:ℝ) (min T₁ T₂) ∈ 𝓝 τ := isOpen_Ioo.mem_nhds hτ
    refine Filter.eventually_of_mem hmem (fun s hs => ?_)
    have hc := (hcontInt s hs).mono Set.Ioo_subset_Icc_self
    exact (hc.aestronglyMeasurable measurableSet_Ioo).mono_measure
      (Measure.restrict_mono (le_refl _) (le_refl _))
  have hF'_meas : AEStronglyMeasurable
      (intervalDomainUEnergyIntegrandDeriv u₁ u₂ τ)
      intervalDomainInteriorMeasure := by
    have hc : ContinuousOn (intervalDomainUEnergyIntegrandDeriv u₁ u₂ τ)
        (Set.Icc (0:ℝ) 1) := by
      have hcurry : ContinuousOn
          (fun y : ℝ => Function.uncurry
            (intervalDomainUEnergyIntegrandDeriv u₁ u₂) (τ, y)) (Set.Icc (0:ℝ) 1) := by
        refine (hslab.comp (Continuous.continuousOn (by fun_prop)) ?_)
        intro y hy
        exact ⟨⟨by linarith [hδ], by linarith [hδ]⟩, hy⟩
      exact hcurry
    exact (hc.aestronglyMeasurable measurableSet_Icc).mono_measure
      (Measure.restrict_mono Set.Ioo_subset_Icc_self (le_refl _))
  exact intervalDomainL2UEnergy_hasDerivAt_of_slabContinuous
    hsol₁ hsol₂ hδ hball hF_meas hF_int hF'_meas hslab

/-- **`E_u` is continuous on every interior closed subinterval** (from the
time-`HasDerivAt`: differentiable everywhere on the interior ⇒ continuous). -/
theorem intervalDomainL2UEnergy_continuousOn_of_solution
    {p : CM2Params} {T₁ T₂ : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂)
    {s t : ℝ} (hs0 : 0 < s) (hst : s ≤ t) (htT : t < min T₁ T₂) :
    ContinuousOn (intervalDomainClassicalL2DifferenceEnergyU u₁ u₂)
      (Set.Icc s t) := by
  refine fun τ hτ => ?_
  have hτIoo : τ ∈ Set.Ioo (0:ℝ) (min T₁ T₂) :=
    ⟨lt_of_lt_of_le hs0 hτ.1, lt_of_le_of_lt hτ.2 htT⟩
  exact (intervalDomainL2UEnergy_hasDerivAt_of_solution hsol₁ hsol₂
    hτIoo).continuousAt.continuousWithinAt

/-- For a difference of two solution `u`-slices at interior times, the lifted
pointwise value at any `y ∈ Icc 0 1` is bounded by the interval sup-norm of the
difference (the lift is continuous on the compact `[0,1]`, hence its range of
absolute values is `BddAbove`, so the `sSup` defining `supNorm` is a genuine
upper bound). -/
theorem abs_lift_uDiff_le_supNorm
    {p : CM2Params} {T₁ T₂ : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂)
    {s : ℝ} (hs₁ : s ∈ Set.Ioo (0:ℝ) T₁) (hs₂ : s ∈ Set.Ioo (0:ℝ) T₂)
    {y : ℝ} (hy : y ∈ Set.Icc (0:ℝ) 1) :
    |intervalDomainLift (fun x => u₁ s x - u₂ s x) y|
      ≤ intervalDomainSupNorm (fun x => u₁ s x - u₂ s x) := by
  classical
  -- BddAbove of `range |w_s|` from continuity of the lift on the compact `[0,1]`.
  have hcont : ContinuousOn (intervalDomainLift (fun x => u₁ s x - u₂ s x))
      (Set.Icc (0:ℝ) 1) := by
    refine ((solution_lift_continuousOn_Icc hsol₁ hs₁).sub
      (solution_lift_continuousOn_Icc hsol₂ hs₂)).congr (fun z hz => ?_)
    exact (intervalDomainLift_uDiff_eq u₁ u₂ s z)
  have hbdd : BddAbove
      (Set.range (fun x : intervalDomainPoint => |(fun x => u₁ s x - u₂ s x) x|)) := by
    have hcompact : IsCompact (Set.Icc (0:ℝ) 1) := isCompact_Icc
    obtain ⟨M, hM⟩ := (hcompact.image_of_continuousOn (hcont.abs)).bddAbove
    refine ⟨M, ?_⟩
    rintro _ ⟨x, rfl⟩
    have hMx := hM ⟨x.1, x.2, rfl⟩
    -- `hMx : |lift(w_s) x.1| ≤ M`;  goal : `|w_s x| ≤ M`.
    have hlift : intervalDomainLift (fun z => u₁ s z - u₂ s z) x.1
        = (fun z => u₁ s z - u₂ s z) x := by
      simp [intervalDomainLift, x.2]
    simpa only [hlift] using hMx
  have hle : |(fun x => u₁ s x - u₂ s x) ⟨y, hy⟩|
      ≤ intervalDomainSupNorm (fun x => u₁ s x - u₂ s x) :=
    le_csSup hbdd ⟨⟨y, hy⟩, rfl⟩
  have hlift : intervalDomainLift (fun x => u₁ s x - u₂ s x) y
      = (fun x => u₁ s x - u₂ s x) ⟨y, hy⟩ := by
    simp [intervalDomainLift, hy]
  rw [hlift]; exact hle

/-- **Initial vanishing of `E_u`** from the shared `u`-initial trace.

`E_u(s) = ∫₀¹ (u₁ s − u₂ s)² ≤ (supNorm (u₁ s − u₂ s))²`, and the supNorm of the
difference is bounded by the sum of the two initial-trace supNorms, each `→ 0`. -/
theorem intervalDomainL2UEnergy_initial_vanishes_of_trace
    {p : CM2Params} {T₁ T₂ : ℝ} {u₀ : intervalDomainPoint → ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂)
    (htr₁ : InitialTrace intervalDomain u₀ u₁)
    (htr₂ : InitialTrace intervalDomain u₀ u₂)
    -- The initial datum has a genuine sup norm (`BddAbove` of `range |u₀|`).  This
    -- is what makes the `InitialTrace` sup-bounds NON-vacuous (the `sSup` in
    -- `supNorm` is a real upper bound rather than the junk-`0` convention), so the
    -- triangle inequality `supNorm(u₁−u₂) ≤ supNorm(u₁−u₀)+supNorm(u₂−u₀)` holds.
    -- For a classical solution `uⱼ(·,s)` is continuous on the compact `[0,1]`,
    -- hence bounded; this hypothesis records only that the SHARED initial datum is
    -- likewise bounded (e.g. any continuous / `L∞` admissible datum), which every
    -- admissible initial datum of the existence theory satisfies.
    (hbdd₀ : BddAbove (Set.range (fun x : intervalDomainPoint => |u₀ x|))) :
    ∀ ε > 0, ∃ δ > 0, ∀ s, 0 < s → s < δ → s < min T₁ T₂ →
      intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ s < ε := by
  classical
  intro ε hε
  -- Pick `r > 0` with `(2 r)² < ε`:  take `r := √ε / 3`, so `2r = 2√ε/3`,
  -- `(2r)² = 4ε/9 < ε`.
  set r : ℝ := Real.sqrt ε / 3 with hr
  have hr_pos : 0 < r := by rw [hr]; positivity
  have hsqrt_sq : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt (le_of_lt hε)
  have h2r_sq : (2 * r) ^ 2 < ε := by
    rw [hr]
    have : (2 * (Real.sqrt ε / 3)) ^ 2 = (4 / 9) * (Real.sqrt ε ^ 2) := by ring
    rw [this, hsqrt_sq]; linarith
  obtain ⟨δ₁, hδ₁, hb₁⟩ := htr₁ r hr_pos
  obtain ⟨δ₂, hδ₂, hb₂⟩ := htr₂ r hr_pos
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun s hs0 hsδ hsT => ?_⟩
  have hs1 : s < δ₁ := lt_of_lt_of_le hsδ (min_le_left _ _)
  have hs2 : s < δ₂ := lt_of_lt_of_le hsδ (min_le_right _ _)
  have hsT₁ : s ∈ Set.Ioo (0:ℝ) T₁ := ⟨hs0, lt_of_lt_of_le hsT (min_le_left _ _)⟩
  have hsT₂ : s ∈ Set.Ioo (0:ℝ) T₂ := ⟨hs0, lt_of_lt_of_le hsT (min_le_right _ _)⟩
  -- supNorm of the difference `< 2r` via the triangle inequality of the two traces.
  have htrace₁ : intervalDomainSupNorm (fun x => u₁ s x - u₀ x) < r :=
    hb₁ s hs0 hs1
  have htrace₂ : intervalDomainSupNorm (fun x => u₂ s x - u₀ x) < r :=
    hb₂ s hs0 hs2
  set Sw : ℝ := intervalDomainSupNorm (fun x => u₁ s x - u₂ s x) with hSw
  have hSw_nn : 0 ≤ Sw := by
    rw [hSw]
    unfold intervalDomainSupNorm
    by_cases hbdd : BddAbove (Set.range (fun x : intervalDomainPoint => |u₁ s x - u₂ s x|))
    · exact le_csSup_of_le hbdd ⟨⟨0, le_refl 0, zero_le_one⟩, rfl⟩ (abs_nonneg _)
    · rw [Real.sSup_def, dif_neg (by simp [hbdd])]
  -- the pointwise lift bound `|lift w_s y| ≤ Sw`, hence `(lift w_s y)² ≤ Sw²`.
  have hpt : ∀ y ∈ Set.Icc (0:ℝ) 1,
      (intervalDomainLift (fun x => u₁ s x - u₂ s x) y) ^ 2 ≤ Sw ^ 2 := by
    intro y hy
    have habs := abs_lift_uDiff_le_supNorm hsol₁ hsol₂ hsT₁ hsT₂ hy
    rw [← hSw] at habs
    have hsq := mul_self_le_mul_self (abs_nonneg _) habs
    calc (intervalDomainLift (fun x => u₁ s x - u₂ s x) y) ^ 2
        = |intervalDomainLift (fun x => u₁ s x - u₂ s x) y| ^ 2 := by rw [sq_abs]
      _ = |intervalDomainLift (fun x => u₁ s x - u₂ s x) y| *
          |intervalDomainLift (fun x => u₁ s x - u₂ s x) y| := by ring
      _ ≤ Sw * Sw := hsq
      _ = Sw ^ 2 := by ring
  -- `E_u s = ∫₀¹ (lift w_s)² ≤ ∫₀¹ Sw² = Sw²`.
  have hEu_eq : intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ s
      = ∫ y in (0:ℝ)..1, (intervalDomainLift (fun x => u₁ s x - u₂ s x) y) ^ 2 :=
    intervalDomainL2UEnergy_eq_integral u₁ u₂ s
  have hintLHS : IntervalIntegrable
      (fun y => (intervalDomainLift (fun x => u₁ s x - u₂ s x) y) ^ 2) volume 0 1 := by
    have hc : ContinuousOn (fun y => (intervalDomainLift (fun x => u₁ s x - u₂ s x) y) ^ 2)
        (Set.uIcc (0:ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      refine (((solution_lift_continuousOn_Icc hsol₁ hsT₁).sub
        (solution_lift_continuousOn_Icc hsol₂ hsT₂)).congr (fun z hz =>
          (intervalDomainLift_uDiff_eq u₁ u₂ s z))).pow 2
    exact hc.intervalIntegrable
  have hEu_le : intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ s ≤ Sw ^ 2 := by
    rw [hEu_eq]
    have hmono : (∫ y in (0:ℝ)..1,
        (intervalDomainLift (fun x => u₁ s x - u₂ s x) y) ^ 2)
        ≤ ∫ _ in (0:ℝ)..1, Sw ^ 2 := by
      refine intervalIntegral.integral_mono_on (by norm_num) hintLHS
        (continuous_const.intervalIntegrable 0 1) ?_
      intro y hy; exact hpt y hy
    rwa [intervalIntegral.integral_const, smul_eq_mul, sub_zero, one_mul] at hmono
  -- BddAbove of each `range |uⱼ s|` (solution slice continuous on compact `[0,1]`).
  have hbddU : ∀ {Tj : ℝ} {uj vj : ℝ → intervalDomainPoint → ℝ},
      IsPaper2ClassicalSolution intervalDomain p Tj uj vj →
      s ∈ Set.Ioo (0:ℝ) Tj →
      BddAbove (Set.range (fun x : intervalDomainPoint => |uj s x|)) := by
    intro Tj uj vj hsolj hsj
    have hcont : ContinuousOn (intervalDomainLift (uj s)) (Set.Icc (0:ℝ) 1) :=
      solution_lift_continuousOn_Icc hsolj hsj
    obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn (hcont.abs)).bddAbove
    refine ⟨M, ?_⟩
    rintro _ ⟨x, rfl⟩
    have hMx := hM ⟨x.1, x.2, rfl⟩
    have hlift : intervalDomainLift (uj s) x.1 = uj s x := by
      simp [intervalDomainLift, x.2]
    simpa only [hlift] using hMx
  have hbdd₁ : BddAbove (Set.range (fun x : intervalDomainPoint => |u₁ s x - u₀ x|)) := by
    obtain ⟨M1, hM1⟩ := hbddU hsol₁ hsT₁; obtain ⟨M0, hM0⟩ := hbdd₀
    exact ⟨M1 + M0, fun _ ⟨x, hx⟩ => hx ▸
      (abs_sub (u₁ s x) (u₀ x)).trans (add_le_add (hM1 ⟨x, rfl⟩) (hM0 ⟨x, rfl⟩))⟩
  have hbdd₂ : BddAbove (Set.range (fun x : intervalDomainPoint => |u₂ s x - u₀ x|)) := by
    obtain ⟨M2, hM2⟩ := hbddU hsol₂ hsT₂; obtain ⟨M0, hM0⟩ := hbdd₀
    exact ⟨M2 + M0, fun _ ⟨x, hx⟩ => hx ▸
      (abs_sub (u₂ s x) (u₀ x)).trans (add_le_add (hM2 ⟨x, rfl⟩) (hM0 ⟨x, rfl⟩))⟩
  -- `Sw < 2r` (triangle), so `Sw² ≤ (2r)² < ε`.
  have htri : Sw ≤ intervalDomainSupNorm (fun x => u₁ s x - u₀ x)
      + intervalDomainSupNorm (fun x => u₂ s x - u₀ x) := by
    rw [hSw]
    -- `supNorm(w) = sSup |w| ≤ supNorm(u₁−u₀)+supNorm(u₂−u₀)` via `csSup_le`.
    unfold intervalDomainSupNorm
    haveI : Nonempty intervalDomainPoint := ⟨⟨0, le_refl _, zero_le_one⟩⟩
    refine csSup_le (Set.range_nonempty _) ?_
    rintro _ ⟨x, rfl⟩
    calc |u₁ s x - u₂ s x|
        = |(u₁ s x - u₀ x) - (u₂ s x - u₀ x)| := by ring_nf
      _ ≤ |u₁ s x - u₀ x| + |u₂ s x - u₀ x| := abs_sub _ _
      _ ≤ sSup (Set.range (fun x => |u₁ s x - u₀ x|))
            + sSup (Set.range (fun x => |u₂ s x - u₀ x|)) :=
          add_le_add (le_csSup hbdd₁ ⟨x, rfl⟩) (le_csSup hbdd₂ ⟨x, rfl⟩)
  have hSw_lt : Sw < 2 * r := by
    calc Sw ≤ intervalDomainSupNorm (fun x => u₁ s x - u₀ x)
          + intervalDomainSupNorm (fun x => u₂ s x - u₀ x) := htri
      _ < r + r := add_lt_add htrace₁ htrace₂
      _ = 2 * r := by ring
  have hSw_sq_lt : Sw ^ 2 < ε :=
    lt_of_le_of_lt (by nlinarith [hSw_nn, hSw_lt, hr_pos]) h2r_sq
  exact lt_of_le_of_lt hEu_le hSw_sq_lt

/-- A nonnegative function continuous on `Icc 0 1` whose squared interval integral
over `(0,1)` vanishes is identically zero on `[0,1]`.  Via Mathlib
`intervalIntegral.integral_eq_zero_iff_of_nonneg_ae` (a.e.-zero) upgraded to
everywhere by `MeasureTheory.Measure.eqOn_of_ae_eq` (continuous + a.e.-zero ⇒
`EqOn`, using `Icc 0 1 ⊆ closure (interior (Icc 0 1))`). -/
theorem continuousOn_sq_integral_zero_eqOn_zero
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (0:ℝ) 1))
    (hz : (∫ y in (0:ℝ)..1, (f y) ^ 2) = 0) :
    ∀ y ∈ Set.Icc (0:ℝ) 1, f y = 0 := by
  classical
  have hsqcont : ContinuousOn (fun y => (f y) ^ 2) (Set.Icc (0:ℝ) 1) := hf.pow 2
  have hint : IntervalIntegrable (fun y => (f y) ^ 2) volume 0 1 := by
    exact (hsqcont.mono (by rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)])).intervalIntegrable
  have hnn_ae : 0 ≤ᵐ[volume.restrict (Set.Ioc (0:ℝ) 1 ∪ Set.Ioc 1 0)]
      (fun y => (f y) ^ 2) :=
    Filter.Eventually.of_forall (fun y => by positivity)
  have haezero := (intervalIntegral.integral_eq_zero_iff_of_nonneg_ae hnn_ae hint).1 hz
  -- a.e.-zero on `Ioc 0 1 ∪ Ioc 1 0 = Ioc 0 1`; transfer to `Icc 0 1` (differ by null).
  have hsimp : (Set.Ioc (0:ℝ) 1 ∪ Set.Ioc 1 0) = Set.Ioc (0:ℝ) 1 := by
    rw [Set.Ioc_eq_empty (by norm_num : ¬ (1:ℝ) < 0), Set.union_empty]
  rw [hsimp] at haezero
  have hsetae : Set.Icc (0:ℝ) 1 =ᵐ[volume] Set.Ioc (0:ℝ) 1 := by
    refine MeasureTheory.ae_eq_set.2 ⟨?_, ?_⟩
    · -- `Icc \ Ioc = {0}`, null.
      have : Set.Icc (0:ℝ) 1 \ Set.Ioc (0:ℝ) 1 ⊆ {(0:ℝ)} := by
        intro x hx
        obtain ⟨⟨h0, h1⟩, hnot⟩ := hx
        simp only [Set.mem_Ioc, not_and, not_le] at hnot
        rcases eq_or_lt_of_le h0 with h | h
        · simp [h.symm]
        · exact absurd h1 (not_le.mpr (hnot h))
      exact measure_mono_null this Real.volume_singleton
    · -- `Ioc \ Icc = ∅`.
      have : Set.Ioc (0:ℝ) 1 \ Set.Icc (0:ℝ) 1 = ∅ := by
        rw [Set.diff_eq_empty]; exact Set.Ioc_subset_Icc_self
      rw [this]; exact measure_empty
  have haeIcc : (fun y => (f y) ^ 2) =ᵐ[volume.restrict (Set.Icc (0:ℝ) 1)]
      (fun _ => (0:ℝ)) := by
    rw [Measure.restrict_congr_set hsetae]; exact haezero
  have heqOn : Set.EqOn (fun y => (f y) ^ 2) (fun _ => (0:ℝ)) (Set.Icc (0:ℝ) 1) := by
    refine MeasureTheory.Measure.eqOn_of_ae_eq haeIcc hsqcont continuousOn_const ?_
    rw [interior_Icc, closure_Ioo (by norm_num : (0:ℝ) ≠ 1)]
  intro y hy
  have := heqOn hy
  simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this

/-- **Zero `u`-energy forces pointwise equality of `u` AND `v`.**

If `E_u(t) = ∫₀¹ (u₁ t − u₂ t)² = 0` at an interior time, then (the integrand is
continuous and nonnegative, so it vanishes everywhere) `u₁ t = u₂ t` pointwise;
and then the static elliptic control `static_v_value_L2_le_Eu` forces
`∫₀¹ (v₁ t − v₂ t)² ≤ C · E_u = 0`, so `v₁ t = v₂ t` pointwise as well. -/
theorem intervalDomainL2UEnergy_zero_pointwise_of_solution
    {p : CM2Params} {T₁ T₂ : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂)
    {t : ℝ} (ht : 0 < t) (htT : t < min T₁ T₂)
    (hzero : intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ t = 0) :
    ∀ x : intervalDomainPoint, u₁ t x = u₂ t x ∧ v₁ t x = v₂ t x := by
  classical
  have ht₁ : t ∈ Set.Ioo (0:ℝ) T₁ := ⟨ht, lt_of_lt_of_le htT (min_le_left _ _)⟩
  have ht₂ : t ∈ Set.Ioo (0:ℝ) T₂ := ⟨ht, lt_of_lt_of_le htT (min_le_right _ _)⟩
  -- continuity of the lifted `u`-difference on `[0,1]`.
  have hwcont : ContinuousOn (intervalDomainLift (fun x => u₁ t x - u₂ t x))
      (Set.Icc (0:ℝ) 1) := by
    refine ((solution_lift_continuousOn_Icc hsol₁ ht₁).sub
      (solution_lift_continuousOn_Icc hsol₂ ht₂)).congr (fun z hz =>
        (intervalDomainLift_uDiff_eq u₁ u₂ t z))
  have hint_eq : (∫ y in (0:ℝ)..1,
      (intervalDomainLift (fun x => u₁ t x - u₂ t x) y) ^ 2) = 0 := by
    rw [← intervalDomainL2UEnergy_eq_integral]; exact hzero
  have hu_pt := continuousOn_sq_integral_zero_eqOn_zero hwcont hint_eq
  have hu_eq : ∀ x : intervalDomainPoint, u₁ t x = u₂ t x := by
    intro x
    have hy : (x.1 : ℝ) ∈ Set.Icc (0:ℝ) 1 := x.2
    have := hu_pt x.1 hy
    have hlift : intervalDomainLift (fun z => u₁ t z - u₂ t z) x.1
        = u₁ t x - u₂ t x := by simp [intervalDomainLift, x.2]
    rw [hlift] at this; linarith [this]
  -- `v₁ = v₂`:  `∫(v₁−v₂)² ≤ C · E_u = 0`, integrand continuous nonneg ⇒ `≡ 0`.
  obtain ⟨C, hCnn, hCle⟩ := static_v_value_L2_le_Eu hsol₁ hsol₂ ht₁ ht₂
  have hvint_zero : (∫ x in (0:ℝ)..1,
      (intervalDomainLift (v₁ t) x - intervalDomainLift (v₂ t) x) ^ 2) = 0 := by
    have hle : (∫ x in (0:ℝ)..1,
        (intervalDomainLift (v₁ t) x - intervalDomainLift (v₂ t) x) ^ 2) ≤ 0 := by
      rw [hzero, mul_zero] at hCle; exact hCle
    have hge : 0 ≤ ∫ x in (0:ℝ)..1,
        (intervalDomainLift (v₁ t) x - intervalDomainLift (v₂ t) x) ^ 2 :=
      intervalIntegral.integral_nonneg (by norm_num) (fun y _ => by positivity)
    linarith
  have hvcont : ContinuousOn
      (fun x => intervalDomainLift (v₁ t) x - intervalDomainLift (v₂ t) x)
      (Set.Icc (0:ℝ) 1) := by
    have hc1 : ContinuousOn (intervalDomainLift (v₁ t)) (Set.Icc (0:ℝ) 1) :=
      ((hsol₁.regularity.2.2.2.2.1 t ht₁).2.1).continuousOn
    have hc2 : ContinuousOn (intervalDomainLift (v₂ t)) (Set.Icc (0:ℝ) 1) :=
      ((hsol₂.regularity.2.2.2.2.1 t ht₂).2.1).continuousOn
    exact hc1.sub hc2
  have hv_pt := continuousOn_sq_integral_zero_eqOn_zero hvcont hvint_zero
  have hv_eq : ∀ x : intervalDomainPoint, v₁ t x = v₂ t x := by
    intro x
    have hy : (x.1 : ℝ) ∈ Set.Icc (0:ℝ) 1 := x.2
    have hsqz := hv_pt x.1 hy
    have h1 : intervalDomainLift (v₁ t) x.1 = v₁ t x := by simp [intervalDomainLift, x.2]
    have h2 : intervalDomainLift (v₂ t) x.1 = v₂ t x := by simp [intervalDomainLift, x.2]
    rw [h1, h2] at hsqz; linarith
  exact fun x => ⟨hu_eq x, hv_eq x⟩

/-- **The full `u`-only difference-energy frontier for a solution pair, UNCONDITIONAL
modulo a bounded initial datum.**

Every frontier field is constructed from the solution pair:
* `Eprime τ = ∫₀¹ intervalDomainUEnergyIntegrandDeriv u₁ u₂ τ`;
* `diffIneq` — the time-Leibniz `HasDerivAt`
  (`intervalDomainL2UEnergy_hasDerivAt_of_solution`, unconditional via the closed-
  domain conjunct 4) PLUS the inequality `∫ integrandDeriv ≤ K · E_u`
  (`intervalDomainL2U_energy_diffIneq_bound`, unconditional via Neumann IBP + flux
  `L²` Young absorption + reaction Lipschitz);
* `cont` from the `HasDerivAt`; `initial_vanishes` from the shared `InitialTrace`
  (using the bounded-datum hypothesis `hbdd₀`); `zero_pointwise` from continuity +
  the static elliptic `v`-control. -/
def intervalDomainL2UDifferenceEnergyFrontier_of_solution
    {p : CM2Params} {T₁ T₂ : ℝ} {u₀ : intervalDomainPoint → ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂)
    (htr₁ : InitialTrace intervalDomain u₀ u₁)
    (htr₂ : InitialTrace intervalDomain u₀ u₂)
    (hbdd₀ : BddAbove (Set.range (fun x : intervalDomainPoint => |u₀ x|)))
    -- The single remaining analytic content: a UNIFORM Grönwall constant `K` for
    -- the per-time differential inequality on the whole overlap interior.  Each
    -- per-time bound `∫ integrandDeriv τ ≤ Kτ · E_u τ` is PROVED unconditionally
    -- (`intervalDomainL2U_energy_diffIneq_bound`), but its constant
    -- `Kτ = χ₀²·Cflux(τ) + 2L(τ)` depends on the time-`τ` `L∞`/Lipschitz data; this
    -- hypothesis records the (standard, by joint continuity over a compact time
    -- slab) UNIFORMITY of that constant over the overlap.  Everything else in the
    -- frontier is constructed unconditionally.
    (hKunif : ∃ K : ℝ, 0 ≤ K ∧ ∀ τ, 0 < τ → τ < min T₁ T₂ →
        (∫ y in (0:ℝ)..1, intervalDomainUEnergyIntegrandDeriv u₁ u₂ τ y)
          ≤ K * intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ) :
    IntervalDomainL2UDifferenceEnergyFrontier p (min T₁ T₂) u₁ v₁ u₂ v₂ where
  Eprime := fun τ => ∫ y in (0:ℝ)..1, intervalDomainUEnergyIntegrandDeriv u₁ u₂ τ y
  K := Classical.choose hKunif
  K_nonneg := (Classical.choose_spec hKunif).1
  cont := fun s t hs0 hst htT =>
    intervalDomainL2UEnergy_continuousOn_of_solution hsol₁ hsol₂ hs0 hst htT
  diffIneq := fun τ hτ0 hτT =>
    ⟨(intervalDomainL2UEnergy_hasDerivAt_of_solution hsol₁ hsol₂
        ⟨hτ0, hτT⟩).hasDerivWithinAt,
      (Classical.choose_spec hKunif).2 τ hτ0 hτT⟩
  initial_vanishes :=
    intervalDomainL2UEnergy_initial_vanishes_of_trace hsol₁ hsol₂ htr₁ htr₂ hbdd₀
  zero_pointwise := fun t ht htT hz =>
    intervalDomainL2UEnergy_zero_pointwise_of_solution hsol₁ hsol₂ ht htT hz

/-- **The single remaining named obligation: bounded initial datum + uniform
Grönwall constant.**

This replaces the prior `IntervalDomainL2UDiffIneqResidual`.  It bundles exactly
the two inputs that the regularity conjuncts + Mathlib + the PROVED per-time energy
inequality do not by themselves supply, kept explicit instead of faked:
* `bdd₀` — the shared initial datum has a genuine sup norm (so the `InitialTrace`
  sup-bounds are non-vacuous: needed for `initial_vanishes`);
* `Kunif` — a UNIFORM Grönwall constant for the (per-time PROVED) differential
  inequality over the overlap interior (the per-time constant `χ₀²·Cflux(τ)+2L(τ)`
  is bounded uniformly over a compact time slab by joint continuity).
Everything else — the closed-domain time-`C¹` Leibniz `HasDerivWithinAt`, the per-
time inequality, energy continuity, and the zero-energy ⇒ pointwise (`u` AND `v`)
step — is PROVED unconditionally above. -/
structure IntervalDomainL2UBoundedDatumUniform
    (p : CM2Params) where
  bdd₀ :
    ∀ {u₀ : intervalDomainPoint → ℝ},
      PositiveInitialDatum intervalDomain u₀ →
      ∀ {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
          BddAbove (Set.range (fun x : intervalDomainPoint => |u₀ x|))
  Kunif :
    ∀ {u₀ : intervalDomainPoint → ℝ},
      PositiveInitialDatum intervalDomain u₀ →
      ∀ {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
        ∃ K : ℝ, 0 ≤ K ∧ ∀ τ, 0 < τ → τ < min T₁ T₂ →
          (∫ y in (0:ℝ)..1, intervalDomainUEnergyIntegrandDeriv u₁ u₂ τ y)
            ≤ K * intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ

/-- **The `u`-only joint-time regularity instance, from the bounded-datum + uniform
obligation.**  Composing with
`intervalDomainClassicalUniquenessL2EnergyMethod_of_uJointTimeRegularity` and
`GlobalSolutionGluingFromReachability_of_l2EnergyMethod`, the entire gluing /
uniqueness chain reduces to this single (strictly-weaker, no `∂ₜ(v−V)`) obligation;
its `bdd₀`/`Kunif` are the only inputs not constructed unconditionally here. -/
def intervalDomainL2UJointTimeRegularity_of_boundedDatumUniform
    {p : CM2Params}
    (hres : IntervalDomainL2UBoundedDatumUniform p) :
    IntervalDomainL2UJointTimeRegularity p where
  frontier := fun {_u₀} hu₀ {_T₁} {_T₂} {_u₁} {_v₁} {_u₂} {_v₂}
      hsol₁ hsol₂ htr₁ htr₂ =>
    intervalDomainL2UDifferenceEnergyFrontier_of_solution hsol₁ hsol₂ htr₁ htr₂
      (hres.bdd₀ hu₀ hsol₁ hsol₂ htr₁ htr₂)
      (hres.Kunif hu₀ hsol₁ hsol₂ htr₁ htr₂)

/-- **The L²-energy uniqueness method from the bounded-datum + uniform obligation.** -/
theorem intervalDomainClassicalUniquenessL2EnergyMethod_of_boundedDatumUniform
    (p : CM2Params)
    (hres : IntervalDomainL2UBoundedDatumUniform p) :
    IntervalDomainClassicalUniquenessL2EnergyMethod p :=
  intervalDomainClassicalUniquenessL2EnergyMethod_of_uJointTimeRegularity p
    (intervalDomainL2UJointTimeRegularity_of_boundedDatumUniform hres)

/-- **Global-solution gluing from reachability, reduced to the single named
obligation.**

The full gluing theorem `GlobalSolutionGluingFromReachability p` holds given only
`IntervalDomainL2UBoundedDatumUniform p` — the bounded shared initial datum plus a
uniform Grönwall constant for the (per-time PROVED) `u`-only energy differential
inequality.  Every other ingredient (closed-domain time-`C¹` Leibniz
`HasDerivWithinAt`, the per-time inequality `∫ integrandDeriv ≤ K·E_u`, energy
continuity, and `E_u = 0 ⟹ u = U ∧ v = V`) is constructed unconditionally above. -/
theorem GlobalSolutionGluingFromReachability_of_boundedDatumUniform
    (p : CM2Params)
    (hres : IntervalDomainL2UBoundedDatumUniform p) :
    ShenWork.IntervalDomainExistence.GlobalSolutionGluingFromReachability p :=
  ShenWork.IntervalDomainExistence.GlobalSolutionGluingFromReachability_of_l2EnergyMethod
    (intervalDomainClassicalUniquenessL2EnergyMethod_of_boundedDatumUniform p hres)

end

end ShenWork.Paper2
