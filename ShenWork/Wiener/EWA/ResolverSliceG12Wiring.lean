/-
  ShenWork/Wiener/EWA/ResolverSliceG12Wiring.lean

  **χ₀<0 — window-uniform G1/G2 (first/second spatial-derivative
  sup bounds) for `realSlice u_star`, DISCHARGED from the
  just-committed joint (t,x)-continuity of ∂ₓ/∂ₓₓ of the
  value field.**

  Pattern: identical to how `realSlice_window_uniform_C0`
  (`ResolverSliceWindowBounds.lean`) produces m/M from
  `fullSourceCoeff_jointSolutionClosed`:

  * joint continuity on the closed slab
    `Ioo 0 T ×ˢ Icc 0 1` → restrict to the compact
    window-by-`[0,1]` box;
  * `IsCompact.exists_isMaxOn` extracts a finite per-t₀
    constant;
  * bridge: on `Ioo 0 1` the lift derivative equals the
    cosine-series derivative (by `EventuallyEq.deriv_eq`
    + `hrealizes`); at the endpoints `{0,1}` the lift
    derivative is 0 (junk-value non-differentiability,
    since the lift is positive there but zero-extends
    outside `[0,1]`).

  Then `realSlice_Hv_full` wires the produced G1/G2 into
  `realSlice_Hv`, discharging ALL of
  `C/hC/hdecay/ha0/G1/G2/hG1/hG2`.

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.ResolverSliceHvWiring
import ShenWork.Wiener.EWA.SourceSpatialJointRegularity

noncomputable section

namespace ShenWork.EWA

open Set Topology Filter
open ShenWork.GWA ShenWork.Wiener
open ShenWork.IntervalDomain
  (intervalDomainPoint intervalDomainLift)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalMildToClassical
  (mildChemicalConcentration)
open ShenWork.IntervalResolverDirectTimeRegularity
  (HasResolverDirectSpectralData)
open ShenWork.IntervalDuhamelClosedC2
  (DuhamelSourceTimeC1
   cosineCoeffSeries_grad_hasDerivAt
   cosineCoeffSeries_grad2_hasDerivAt)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs
   coupledLogisticSourceCoeffs)
open ShenWork.IntervalCosineSliceRegularity
  (intervalDomainLift_deriv_left_endpoint_zero_of_ne
   intervalDomainLift_deriv_right_endpoint_zero_of_ne)

variable {T : ℝ}

/-! ### Helpers -/

private theorem clampWindow_subset_Ioo
    {t₀ : ℝ} (ht₀ : 0 < t₀) (ht₀T : t₀ < T) :
    Icc (t₀ / 4) ((t₀ + 3 * T) / 4) ⊆ Ioo (0 : ℝ) T :=
  fun _ hy =>
    ⟨lt_of_lt_of_le (by linarith) hy.1,
     lt_of_le_of_lt hy.2 (by linarith)⟩

/-- Derivative of `deriv (intervalDomainLift g)` is 0
at `x = 0`: the function `deriv (intervalDomainLift g)`
is 0 on `(-∞, 0]` (zero-extension + endpoint), so the
one-sided argument forces the second derivative to 0. -/
private theorem lift_deriv2_zero_at_zero
    {g : intervalDomainPoint → ℝ}
    (hne : intervalDomainLift g 0 ≠ 0) :
    deriv (deriv (intervalDomainLift g)) 0 = 0 := by
  set f := intervalDomainLift g with hfdef
  set h := deriv f with hhdef
  -- h(y) = 0 for y < 0 (f is constant 0 on Iio 0)
  have hzero : ∀ y ∈ Iio (0 : ℝ), h y = 0 := by
    intro y hy
    rw [hhdef]
    have hee : f =ᶠ[𝓝 y] fun _ => (0 : ℝ) :=
      eventually_of_mem (isOpen_Iio.mem_nhds hy)
        (fun z hz => by
          simp [hfdef, intervalDomainLift, show
            z ∉ Icc (0 : ℝ) 1 from
              fun hm => absurd hm.1 (not_le.mpr hz)])
    rw [hee.deriv_eq, deriv_const]
  -- h(0) = 0 (endpoint lemma)
  have h0 : h 0 = 0 := by
    rw [hhdef]
    exact intervalDomainLift_deriv_left_endpoint_zero_of_ne
      hne
  -- deriv h 0 = 0 by one-sided argument
  by_cases hd : DifferentiableAt ℝ h 0
  · have hcw : HasDerivWithinAt h 0 (Iio 0) 0 :=
      (hasDerivWithinAt_const 0 (Iio 0) (0 : ℝ)).congr
        hzero h0
    have hw := hd.hasDerivAt.hasDerivWithinAt.derivWithin
      (uniqueDiffWithinAt_Iio 0)
    rw [← hw]
    exact hcw.derivWithin (uniqueDiffWithinAt_Iio 0)
  · exact deriv_zero_of_not_differentiableAt hd

/-- Mirror at `x = 1`. -/
private theorem lift_deriv2_zero_at_one
    {g : intervalDomainPoint → ℝ}
    (hne : intervalDomainLift g 1 ≠ 0) :
    deriv (deriv (intervalDomainLift g)) 1 = 0 := by
  set f := intervalDomainLift g with hfdef
  set h := deriv f with hhdef
  have hzero : ∀ y ∈ Ioi (1 : ℝ), h y = 0 := by
    intro y hy
    rw [hhdef]
    have hee : f =ᶠ[𝓝 y] fun _ => (0 : ℝ) :=
      eventually_of_mem (isOpen_Ioi.mem_nhds hy)
        (fun z hz => by
          simp [hfdef, intervalDomainLift, show
            z ∉ Icc (0 : ℝ) 1 from
              fun hm => absurd hm.2 (not_le.mpr hz)])
    rw [hee.deriv_eq, deriv_const]
  have h1 : h 1 = 0 := by
    rw [hhdef]
    exact intervalDomainLift_deriv_right_endpoint_zero_of_ne
      hne
  by_cases hd : DifferentiableAt ℝ h 1
  · have hcw : HasDerivWithinAt h 0 (Ioi 1) 1 :=
      (hasDerivWithinAt_const 1 (Ioi 1) (0 : ℝ)).congr
        hzero h1
    have hw := hd.hasDerivAt.hasDerivWithinAt.derivWithin
      (uniqueDiffWithinAt_Ioi 1)
    rw [← hw]
    exact hcw.derivWithin (uniqueDiffWithinAt_Ioi 1)
  · exact deriv_zero_of_not_differentiableAt hd

/-- Lift positivity at the endpoint 0: the lift there
is `realSlice u_star σ ⟨0, …⟩ > 0`, hence ≠ 0. -/
private theorem lift_ne_zero_at_zero
    {u₀E : WA 1} {δ₀ ρ : ℝ} (hδρ : 0 < δ₀ - ρ)
    (hheat : UniformFloor (heatEWA (T := T) u₀E) δ₀)
    {u_star : EWA T 1}
    (hu_ball : u_star ∈
      Metric.closedBall (heatEWA (T := T) u₀E) ρ)
    {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) T) :
    intervalDomainLift (realSlice u_star σ) 0 ≠ 0 := by
  have hmem : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  simp [intervalDomainLift, hmem]
  exact ne_of_gt
    (realSlice_pos hδρ hheat hu_ball hσ ⟨0, hmem⟩)

/-- Lift positivity at the endpoint 1. -/
private theorem lift_ne_zero_at_one
    {u₀E : WA 1} {δ₀ ρ : ℝ} (hδρ : 0 < δ₀ - ρ)
    (hheat : UniformFloor (heatEWA (T := T) u₀E) δ₀)
    {u_star : EWA T 1}
    (hu_ball : u_star ∈
      Metric.closedBall (heatEWA (T := T) u₀E) ρ)
    {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) T) :
    intervalDomainLift (realSlice u_star σ) 1 ≠ 0 := by
  have hmem : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  simp [intervalDomainLift, hmem]
  exact ne_of_gt
    (realSlice_pos hδρ hheat hu_ball hσ ⟨1, hmem⟩)

/-! ### G1/G2 producer -/

/-- **Window-uniform G1/G2 bounds for `realSlice u_star`
— DISCHARGED.**

For each interior `t₀ ∈ (0,T)`, the spatial-derivative
joint continuity theorems
`fullSourceCoeff_jointGradClosed`/`…Grad2Closed`
(on the closed slab `Ioo 0 T ×ˢ Icc 0 1`), combined
with the slice representation `hrealizes` and the
heat-floor positivity `realSlice_pos`, give — over the
COMPACT window box `Icc(t₀/4,(t₀+3T)/4) ×ˢ Icc 0 1` —
finite per-t₀ bounds `G1 t₀`/`G2 t₀` on
`|deriv (intervalDomainLift (realSlice u_star σ)) x|`
and
`|deriv (deriv (intervalDomainLift …)) x|`,
uniformly in `(σ,x)` over the window.

Bridge:
* `Ioo 0 1`: `EventuallyEq.deriv_eq` + `hrealizes`
  matches lift-deriv to series-deriv.
* `{0,1}`: junk-value non-differentiability (lift is
  positive but zero-extends outside `[0,1]`) forces
  `deriv = 0 ≤ G`. -/
theorem realSlice_window_uniform_G12
    (p : CM2Params) (u_star : EWA T 1)
    (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceTimeC1
      (coupledChemDivSourceCoeffs p (realSlice u_star)))
    (hlog : DuhamelSourceTimeC1
      (coupledLogisticSourceCoeffs p (realSlice u_star)))
    {u₀E : WA 1} {δ₀ ρ : ℝ} (hδρ : 0 < δ₀ - ρ)
    (hheat : UniformFloor (heatEWA (T := T) u₀E) δ₀)
    (hu_ball : u_star ∈
      Metric.closedBall (heatEWA (T := T) u₀E) ρ)
    (hsumE : ∀ t ∈ Ioo (0 : ℝ) T,
      Summable (fun n =>
        unitIntervalCosineEigenvalue n *
          |fullSourceCoeff p (realSlice u_star)
            u₀cos t n|))
    (hrealizes : ∀ t ∈ Ioo (0 : ℝ) T,
      ∀ x ∈ Icc (0 : ℝ) 1,
        intervalDomainLift (realSlice u_star t) x =
          ∑' n, fullSourceCoeff p (realSlice u_star)
            u₀cos t n * cosineMode n x) :
    ∃ G1 G2 : ℝ → ℝ,
      (∀ t₀, 0 < t₀ → t₀ < T →
        ∀ σ ∈ Icc (t₀ / 4) ((t₀ + 3 * T) / 4),
        ∀ x ∈ Icc (0 : ℝ) 1,
          |deriv
            (intervalDomainLift (realSlice u_star σ))
            x| ≤ G1 t₀) ∧
      (∀ t₀, 0 < t₀ → t₀ < T →
        ∀ σ ∈ Icc (t₀ / 4) ((t₀ + 3 * T) / 4),
        ∀ x ∈ Icc (0 : ℝ) 1,
          |deriv (deriv
            (intervalDomainLift (realSlice u_star σ)))
            x| ≤ G2 t₀) := by
  classical
  -- Abbreviations for the two jointly-continuous
  -- derivative fields.
  set Fg : ℝ × ℝ → ℝ := Function.uncurry
    (fun t x => deriv (fun y => ∑' n,
      fullSourceCoeff p (realSlice u_star) u₀cos t n *
        cosineMode n y) x) with hFg
  set Fg2 : ℝ × ℝ → ℝ := Function.uncurry
    (fun t x => deriv (fun y => deriv (fun z => ∑' n,
      fullSourceCoeff p (realSlice u_star) u₀cos t n *
        cosineMode n z) y) x) with hFg2
  -- Joint continuity on the slab.
  have hjcG : ContinuousOn Fg
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) :=
    fullSourceCoeff_jointGradClosed p (realSlice u_star)
      u₀cos hu0bd hchem hlog hsumE
  have hjcG2 : ContinuousOn Fg2
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) :=
    fullSourceCoeff_jointGrad2Closed p
      (realSlice u_star) u₀cos hu0bd hchem hlog hsumE
  -- Per-t₀ window extraction.
  have hwin : ∀ t₀, 0 < t₀ → t₀ < T →
      ∃ A1 A2 : ℝ, 0 ≤ A1 ∧ 0 ≤ A2 ∧
        (∀ σ ∈ Icc (t₀ / 4) ((t₀ + 3 * T) / 4),
          ∀ x ∈ Icc (0 : ℝ) 1,
            |deriv (intervalDomainLift
              (realSlice u_star σ)) x| ≤ A1) ∧
        (∀ σ ∈ Icc (t₀ / 4) ((t₀ + 3 * T) / 4),
          ∀ x ∈ Icc (0 : ℝ) 1,
            |deriv (deriv (intervalDomainLift
              (realSlice u_star σ))) x| ≤ A2) := by
    intro t₀ ht₀ ht₀T
    set W := Icc (t₀ / 4) ((t₀ + 3 * T) / 4) with hWdef
    have hsub : W ⊆ Ioo (0 : ℝ) T :=
      clampWindow_subset_Ioo ht₀ ht₀T
    have hcd : t₀ / 4 ≤ (t₀ + 3 * T) / 4 := by linarith
    have hbox_sub :
        W ×ˢ Icc (0 : ℝ) 1 ⊆
          Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1 :=
      prod_mono hsub (Subset.refl _)
    have hKc : IsCompact (W ×ˢ Icc (0 : ℝ) 1) :=
      isCompact_Icc.prod isCompact_Icc
    have hKne : (W ×ˢ Icc (0 : ℝ) 1).Nonempty :=
      ⟨(t₀ / 4, 0), mem_prod.mpr
        ⟨left_mem_Icc.mpr hcd, by norm_num⟩⟩
    -- |Fg| and |Fg2| are continuous on the box.
    have hcFg := (hjcG.mono hbox_sub).norm
    have hcFg2 := (hjcG2.mono hbox_sub).norm
    -- max of |Fg| on the compact box.
    obtain ⟨q₁, hq₁mem, hq₁max⟩ :=
      hKc.exists_isMaxOn hKne hcFg
    obtain ⟨q₂, hq₂mem, hq₂max⟩ :=
      hKc.exists_isMaxOn hKne hcFg2
    -- The max values (as absolute values) are ≥ 0.
    have hA1nn : 0 ≤ ‖Fg q₁‖ := norm_nonneg _
    have hA2nn : 0 ≤ ‖Fg2 q₂‖ := norm_nonneg _
    refine ⟨‖Fg q₁‖, ‖Fg2 q₂‖, hA1nn, hA2nn,
      ?_, ?_⟩
    -- G1 bound
    · intro σ hσ x hx
      -- Case split: interior vs boundary of [0,1].
      by_cases hxint : x ∈ Ioo (0 : ℝ) 1
      · -- Interior: deriv (lift) = deriv (series).
        have hσIoo : σ ∈ Ioo (0 : ℝ) T := hsub hσ
        have hIcc_nhds : Icc (0 : ℝ) 1 ∈ 𝓝 x :=
          Icc_mem_nhds hxint.1 hxint.2
        have hee : intervalDomainLift
              (realSlice u_star σ) =ᶠ[𝓝 x]
            (fun y => ∑' n,
              fullSourceCoeff p (realSlice u_star)
                u₀cos σ n * cosineMode n y) :=
          eventually_of_mem hIcc_nhds
            (fun y hy => hrealizes σ hσIoo y hy)
        rw [EventuallyEq.deriv_eq hee]
        have hmem : (σ, x) ∈ W ×ˢ Icc (0 : ℝ) 1 :=
          mem_prod.mpr ⟨hσ, hx⟩
        calc |Fg (σ, x)|
            = ‖Fg (σ, x)‖ :=
              (Real.norm_eq_abs _).symm
          _ ≤ ‖Fg q₁‖ :=
              isMaxOn_iff.mp hq₁max (σ, x) hmem
          _ = _ := rfl
      · -- Boundary: x = 0 or x = 1.
        have hσIcc : σ ∈ Icc (0 : ℝ) T :=
          ⟨(hsub hσ).1.le, (hsub hσ).2.le⟩
        have hx01 : x = 0 ∨ x = 1 := by
          rcases hx with ⟨h0, h1⟩
          rcases lt_or_eq_of_le h0 with h0' | h0'
          · rcases lt_or_eq_of_le h1 with h1' | h1'
            · exact absurd ⟨h0', h1'⟩ hxint
            · exact Or.inr h1'
          · exact Or.inl h0'.symm
        rcases hx01 with rfl | rfl
        · rw [intervalDomainLift_deriv_left_endpoint_zero_of_ne
            (lift_ne_zero_at_zero hδρ hheat
              hu_ball hσIcc), abs_zero]
          exact hA1nn
        · rw [intervalDomainLift_deriv_right_endpoint_zero_of_ne
            (lift_ne_zero_at_one hδρ hheat
              hu_ball hσIcc), abs_zero]
          exact hA1nn
    -- G2 bound
    · intro σ hσ x hx
      by_cases hxint : x ∈ Ioo (0 : ℝ) 1
      · have hσIoo : σ ∈ Ioo (0 : ℝ) T := hsub hσ
        have hIoo_nhds : Ioo (0 : ℝ) 1 ∈ 𝓝 x :=
          isOpen_Ioo.mem_nhds hxint
        -- First-derivative agreement on Ioo 0 1.
        have hee1 : ∀ y ∈ Ioo (0 : ℝ) 1,
            deriv (intervalDomainLift
              (realSlice u_star σ)) y =
            deriv (fun z => ∑' n,
              fullSourceCoeff p (realSlice u_star)
                u₀cos σ n * cosineMode n z) y := by
          intro y hy
          exact EventuallyEq.deriv_eq
            (eventually_of_mem
              (Icc_mem_nhds hy.1 hy.2)
              (fun z hz =>
                hrealizes σ hσIoo z hz))
        -- Second-derivative agreement via EE.
        have hee2 :
            deriv (intervalDomainLift
              (realSlice u_star σ))
            =ᶠ[𝓝 x]
            deriv (fun z => ∑' n,
              fullSourceCoeff p (realSlice u_star)
                u₀cos σ n * cosineMode n z) :=
          eventually_of_mem hIoo_nhds
            (fun y hy => hee1 y hy)
        rw [EventuallyEq.deriv_eq hee2]
        have hmem : (σ, x) ∈ W ×ˢ Icc (0 : ℝ) 1 :=
          mem_prod.mpr ⟨hσ, hx⟩
        calc |Fg2 (σ, x)|
            = ‖Fg2 (σ, x)‖ :=
              (Real.norm_eq_abs _).symm
          _ ≤ ‖Fg2 q₂‖ :=
              isMaxOn_iff.mp hq₂max (σ, x) hmem
          _ = _ := rfl
      · have hσIcc : σ ∈ Icc (0 : ℝ) T :=
          ⟨(hsub hσ).1.le, (hsub hσ).2.le⟩
        have hx01 : x = 0 ∨ x = 1 := by
          rcases hx with ⟨h0, h1⟩
          rcases lt_or_eq_of_le h0 with h0' | h0'
          · rcases lt_or_eq_of_le h1 with h1' | h1'
            · exact absurd ⟨h0', h1'⟩ hxint
            · exact Or.inr h1'
          · exact Or.inl h0'.symm
        rcases hx01 with rfl | rfl
        · rw [lift_deriv2_zero_at_zero
            (lift_ne_zero_at_zero hδρ hheat
              hu_ball hσIcc), abs_zero]
          exact hA2nn
        · rw [lift_deriv2_zero_at_one
            (lift_ne_zero_at_one hδρ hheat
              hu_ball hσIcc), abs_zero]
          exact hA2nn
  -- Assemble per-window constants into G1/G2 : ℝ → ℝ.
  refine ⟨fun t₀ => if h : 0 < t₀ ∧ t₀ < T then
      (hwin t₀ h.1 h.2).choose else 0,
    fun t₀ => if h : 0 < t₀ ∧ t₀ < T then
      (hwin t₀ h.1 h.2).choose_spec.choose else 0,
    ?_, ?_⟩
  · intro t₀ ht₀ ht₀T σ hσ x hx
    have h : 0 < t₀ ∧ t₀ < T := ⟨ht₀, ht₀T⟩
    simp only [dif_pos h]
    exact (hwin t₀ ht₀ ht₀T).choose_spec.choose_spec
      |>.2.2.1 σ hσ x hx
  · intro t₀ ht₀ ht₀T σ hσ x hx
    have h : 0 < t₀ ∧ t₀ < T := ⟨ht₀, ht₀T⟩
    simp only [dif_pos h]
    exact (hwin t₀ ht₀ ht₀T).choose_spec.choose_spec
      |>.2.2.2 σ hσ x hx

/-! ### Capstone: full Hv with G1/G2 discharged -/

/-- **`Hv` for the EWA slice with ALL of
`C/hC/hdecay/ha0/G1/G2/hG1/hG2` DISCHARGED.**

Consumes `realSlice_Hv` (which already discharges
`C/hC/hdecay/ha0` from `m/M/G1/G2`) and
`realSlice_window_uniform_G12` (which produces
`G1/G2` from the spatial-derivative joint
continuity), leaving only:

* the value-side standing atoms
  (`hu0bd`/`hchem`/`hlog`/`hδρ`/`hheat`/`hu_ball`/
   `hsumE`/`hrealizes`),
* the window cosine representation
  (`bc`/`hbsum`/`hagree`). -/
theorem realSlice_Hv_full
    (p : CM2Params) (u_star : EWA T 1)
    (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceTimeC1
      (coupledChemDivSourceCoeffs p (realSlice u_star)))
    (hlog : DuhamelSourceTimeC1
      (coupledLogisticSourceCoeffs p (realSlice u_star)))
    {u₀E : WA 1} {δ₀ ρ : ℝ} (hδρ : 0 < δ₀ - ρ)
    (hheat : UniformFloor (heatEWA (T := T) u₀E) δ₀)
    (hu_ball : u_star ∈
      Metric.closedBall (heatEWA (T := T) u₀E) ρ)
    (hsumE : ∀ t ∈ Ioo (0 : ℝ) T,
      Summable (fun n =>
        unitIntervalCosineEigenvalue n *
          |fullSourceCoeff p (realSlice u_star)
            u₀cos t n|))
    (hrealizes : ∀ t ∈ Ioo (0 : ℝ) T,
      ∀ x ∈ Icc (0 : ℝ) 1,
        intervalDomainLift (realSlice u_star t) x =
          ∑' n, fullSourceCoeff p (realSlice u_star)
            u₀cos t n * cosineMode n x)
    -- window cosine representation:
    (bc : ℝ → ℝ → ℕ → ℝ)
    (hbsum : ∀ t₀, 0 < t₀ → t₀ < T →
      ∀ σ ∈ Icc (t₀ / 4) ((t₀ + 3 * T) / 4),
        Summable (fun n =>
          unitIntervalCosineEigenvalue n *
            |bc t₀ σ n|))
    (hagree : ∀ t₀, 0 < t₀ → t₀ < T →
      ∀ σ ∈ Icc (t₀ / 4) ((t₀ + 3 * T) / 4),
        EqOn (intervalDomainLift (realSlice u_star σ))
          (fun x => ∑' n, bc t₀ σ n * cosineMode n x)
          (Icc (0 : ℝ) 1)) :
    HasResolverDirectSpectralData T
      (mildChemicalConcentration p (realSlice u_star))
      p := by
  obtain ⟨G1, G2, hG1, hG2⟩ :=
    realSlice_window_uniform_G12 p u_star u₀cos
      hu0bd hchem hlog hδρ hheat hu_ball hsumE hrealizes
  exact realSlice_Hv p u_star u₀cos hu0bd hchem hlog
    hδρ hheat hu_ball hsumE hrealizes bc hbsum hagree
    G1 G2 hG1 hG2

end ShenWork.EWA

#print axioms ShenWork.EWA.realSlice_window_uniform_G12
#print axioms ShenWork.EWA.realSlice_Hv_full
