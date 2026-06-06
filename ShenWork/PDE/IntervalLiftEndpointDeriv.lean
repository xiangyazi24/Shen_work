/-
  ShenWork/PDE/IntervalLiftEndpointDeriv.lean

  Phase-0 / endpoint:  the SECOND derivative of the zero-extension lift
  `intervalDomainLift f` VANISHES at the two interval endpoints `x = 0` and
  `x = 1`, for ANY `f : intervalDomainPoint → ℝ`.

  ## Why this is true (junk-value + slope-uniqueness argument)

  Write `g := deriv (intervalDomainLift f)`.  The lift is `≡ 0` on `Iio 0`
  (and on `Ioi 1`), because outside `Icc 0 1` the `dite` in `intervalDomainLift`
  takes its `else`-branch `0`.  Consequently:

    * `g = 0` on `Iio 0`:  for `x < 0` the lift is `≡ 0` on the open nbhd
      `Iio 0` of `x`, so `HasDerivAt (lift) 0 x` (congr of `hasDerivAt_const`),
      whence `deriv (lift) x = 0`.

    * `deriv g 0 = 0`:  by cases on `DifferentiableAt ℝ g 0`.
        - not differentiable: `deriv_zero_of_not_differentiableAt`.
        - differentiable, `D := deriv g 0`, `hD : HasDerivAt g D 0`:
            (a) `g 0 = 0`:  `hD.continuousAt` restricted to the (`NeBot`)
                left filter `𝓝[<] 0` tends to `g 0`, but `g =ᶠ[𝓝[<] 0] 0`
                (since `Iio 0 ∈ 𝓝[<] 0`), so the limit is also `0`;
                `tendsto_nhds_unique`.
            (b) `D = 0`:  `hD` gives `Tendsto (slope g 0) (𝓝[<] 0) (𝓝 D)`
                (`hasDerivAt_iff_tendsto_slope_left_right`), and using `g = 0`
                on `Iio 0` together with `g 0 = 0` one gets
                `slope g 0 =ᶠ[𝓝[<] 0] 0`, hence `Tendsto … (𝓝 0)`;
                `tendsto_nhds_unique` ⟹ `D = 0`.
          Then `deriv g 0 = D = 0`.

  The endpoint `x = 1` is the exact mirror with `Iio`/`𝓝[<]` replaced by
  `Ioi`/`𝓝[>]`.

  The two exported lemmas are produced in the residual shapes consumed by
  `ShenWork/Paper2/IntervalPicardUniformWiring.lean` (`hEnd0`/`hEnd1`):

    * the `= 0` core (`lift_deriv2_eq_zero_at_zero`, `lift_deriv2_eq_zero_at_one`);
    * a `≤ B` corollary for any `0 ≤ B` (`lift_deriv2_abs_le_at_zero`,
      `lift_deriv2_abs_le_at_one`), matching `|deriv²| ≤ G2profile …` and the
      `∃ M₁' ≤ 2M ∧ |deriv²| ≤ M₁'·… + …` budget shapes.

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.  New file only.
-/
import Mathlib.Analysis.Calculus.Deriv.Slope
import ShenWork.PDE.IntervalDomain

open Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)

noncomputable section

namespace ShenWork.IntervalLiftEndpointDeriv

/-! ## §0 — The lift and its first derivative vanish off `Icc 0 1`. -/

/-- For `x ∉ Icc 0 1` the `dite` in `intervalDomainLift` takes the `else`-branch. -/
theorem lift_eq_zero_of_not_mem
    (f : intervalDomainPoint → ℝ) {x : ℝ} (hx : x ∉ Set.Icc (0 : ℝ) 1) :
    intervalDomainLift f x = 0 := by
  simp [intervalDomainLift, hx]

/-- The lift is `EventuallyEq 0` near any point of the open set `Iio 0`. -/
theorem lift_eventuallyEq_zero_Iio
    (f : intervalDomainPoint → ℝ) {x : ℝ} (hx : x < 0) :
    intervalDomainLift f =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
  have hmem : Set.Iio (0 : ℝ) ∈ nhds x := isOpen_Iio.mem_nhds hx
  filter_upwards [hmem] with z hz
  have hzn : z ∉ Set.Icc (0 : ℝ) 1 := by
    intro hcon; exact absurd hcon.1 (not_le.2 hz)
  exact lift_eq_zero_of_not_mem f hzn

/-- The lift is `EventuallyEq 0` near any point of the open set `Ioi 1`. -/
theorem lift_eventuallyEq_zero_Ioi
    (f : intervalDomainPoint → ℝ) {x : ℝ} (hx : 1 < x) :
    intervalDomainLift f =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
  have hmem : Set.Ioi (1 : ℝ) ∈ nhds x := isOpen_Ioi.mem_nhds hx
  filter_upwards [hmem] with z hz
  have hzn : z ∉ Set.Icc (0 : ℝ) 1 := by
    intro hcon; exact absurd hcon.2 (not_le.2 hz)
  exact lift_eq_zero_of_not_mem f hzn

/-- The first derivative of the lift vanishes for `x < 0`. -/
theorem lift_deriv_eq_zero_of_neg
    (f : intervalDomainPoint → ℝ) {x : ℝ} (hx : x < 0) :
    deriv (intervalDomainLift f) x = 0 := by
  have hEq := lift_eventuallyEq_zero_Iio f hx
  have hD : HasDerivAt (intervalDomainLift f) 0 x := by
    have : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 x := hasDerivAt_const x (0 : ℝ)
    exact this.congr_of_eventuallyEq hEq
  exact hD.deriv

/-- The first derivative of the lift vanishes for `1 < x`. -/
theorem lift_deriv_eq_zero_of_gt_one
    (f : intervalDomainPoint → ℝ) {x : ℝ} (hx : 1 < x) :
    deriv (intervalDomainLift f) x = 0 := by
  have hEq := lift_eventuallyEq_zero_Ioi f hx
  have hD : HasDerivAt (intervalDomainLift f) 0 x := by
    have : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 x := hasDerivAt_const x (0 : ℝ)
    exact this.congr_of_eventuallyEq hEq
  exact hD.deriv

/-! ## §1 — Endpoint `x = 0`: `deriv g 0 = 0` for `g = deriv lift`. -/

/-- `deriv (deriv (intervalDomainLift f)) 0 = 0`. -/
theorem lift_deriv2_eq_zero_at_zero (f : intervalDomainPoint → ℝ) :
    deriv (deriv (intervalDomainLift f)) 0 = 0 := by
  set g : ℝ → ℝ := deriv (intervalDomainLift f) with hg_def
  -- `g = 0` on `Iio 0`.
  have hg_Iio : ∀ y : ℝ, y < 0 → g y = 0 := fun y hy => lift_deriv_eq_zero_of_neg f hy
  -- `g =ᶠ[𝓝[<] 0] 0`.
  have hgEv : g =ᶠ[𝓝[<] (0 : ℝ)] (fun _ => (0 : ℝ)) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact hg_Iio y hy
  by_cases hdiff : DifferentiableAt ℝ g 0
  · -- differentiable case: identify `D := deriv g 0`.
    set D : ℝ := deriv g 0 with hD_def
    have hD : HasDerivAt g D 0 := hdiff.hasDerivAt
    -- (a) `g 0 = 0`.
    have hg0 : g 0 = 0 := by
      have hcont : Tendsto g (𝓝[<] (0 : ℝ)) (𝓝 (g 0)) :=
        hD.continuousAt.continuousWithinAt.tendsto
      have hcont0 : Tendsto g (𝓝[<] (0 : ℝ)) (𝓝 0) := by
        refine (tendsto_const_nhds (x := (0 : ℝ)) (f := 𝓝[<] (0 : ℝ))).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with y hy
        exact (hg_Iio y hy).symm
      exact tendsto_nhds_unique hcont hcont0
    -- (b) `D = 0`, via slope uniqueness on the (NeBot) left filter.
    have hslopeD : Tendsto (slope g 0) (𝓝[<] (0 : ℝ)) (𝓝 D) :=
      (hasDerivAt_iff_tendsto_slope_left_right.mp hD).1
    have hslope0 : Tendsto (slope g 0) (𝓝[<] (0 : ℝ)) (𝓝 0) := by
      refine (tendsto_const_nhds (x := (0 : ℝ)) (f := 𝓝[<] (0 : ℝ))).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hsl : slope g 0 y = (g y - g 0) / (y - 0) := slope_def_field g 0 y
      rw [hsl, hg_Iio y hy, hg0]; simp
    have hDz : D = 0 := tendsto_nhds_unique hslopeD hslope0
    -- conclude `deriv g 0 = D = 0`.
    rw [← hg_def] at *
    simpa [hg_def, hD_def] using hDz
  · -- non-differentiable case.
    simpa [hg_def] using deriv_zero_of_not_differentiableAt hdiff

/-! ## §2 — Endpoint `x = 1`: mirror of §1 (`Iio`→`Ioi`, `𝓝[<]`→`𝓝[>]`). -/

/-- `deriv (deriv (intervalDomainLift f)) 1 = 0`. -/
theorem lift_deriv2_eq_zero_at_one (f : intervalDomainPoint → ℝ) :
    deriv (deriv (intervalDomainLift f)) 1 = 0 := by
  set g : ℝ → ℝ := deriv (intervalDomainLift f) with hg_def
  -- `g = 0` on `Ioi 1`.
  have hg_Ioi : ∀ y : ℝ, 1 < y → g y = 0 := fun y hy => lift_deriv_eq_zero_of_gt_one f hy
  by_cases hdiff : DifferentiableAt ℝ g 1
  · set D : ℝ := deriv g 1 with hD_def
    have hD : HasDerivAt g D 1 := hdiff.hasDerivAt
    -- (a) `g 1 = 0` via the (NeBot) right filter.
    have hg1 : g 1 = 0 := by
      have hcont : Tendsto g (𝓝[>] (1 : ℝ)) (𝓝 (g 1)) :=
        hD.continuousAt.continuousWithinAt.tendsto
      have hcont0 : Tendsto g (𝓝[>] (1 : ℝ)) (𝓝 0) := by
        refine (tendsto_const_nhds (x := (0 : ℝ)) (f := 𝓝[>] (1 : ℝ))).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with y hy
        exact (hg_Ioi y hy).symm
      exact tendsto_nhds_unique hcont hcont0
    -- (b) `D = 0` via slope uniqueness on the right filter.
    have hslopeD : Tendsto (slope g 1) (𝓝[>] (1 : ℝ)) (𝓝 D) :=
      (hasDerivAt_iff_tendsto_slope_left_right.mp hD).2
    have hslope0 : Tendsto (slope g 1) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
      refine (tendsto_const_nhds (x := (0 : ℝ)) (f := 𝓝[>] (1 : ℝ))).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hsl : slope g 1 y = (g y - g 1) / (y - 1) := slope_def_field g 1 y
      rw [hsl, hg_Ioi y hy, hg1]; simp
    have hDz : D = 0 := tendsto_nhds_unique hslopeD hslope0
    rw [← hg_def] at *
    simpa [hg_def, hD_def] using hDz
  · simpa [hg_def] using deriv_zero_of_not_differentiableAt hdiff

/-! ## §3 — Residual shapes consumed by `IntervalPicardUniformWiring`.

The wiring file's `hEnd0`/`hEnd1` residuals are absolute-value bounds
(`|deriv²| ≤ bound`).  Since the second derivative is exactly `0` at the
endpoints, any `0 ≤ bound` discharges them. -/

/-- `|deriv² (lift f) 0| ≤ B` for any nonneg bound `B`. -/
theorem lift_deriv2_abs_le_at_zero
    (f : intervalDomainPoint → ℝ) {B : ℝ} (hB : 0 ≤ B) :
    |deriv (deriv (intervalDomainLift f)) 0| ≤ B := by
  rw [lift_deriv2_eq_zero_at_zero f, abs_zero]; exact hB

/-- `|deriv² (lift f) 1| ≤ B` for any nonneg bound `B`. -/
theorem lift_deriv2_abs_le_at_one
    (f : intervalDomainPoint → ℝ) {B : ℝ} (hB : 0 ≤ B) :
    |deriv (deriv (intervalDomainLift f)) 1| ≤ B := by
  rw [lift_deriv2_eq_zero_at_one f, abs_zero]; exact hB

end ShenWork.IntervalLiftEndpointDeriv
