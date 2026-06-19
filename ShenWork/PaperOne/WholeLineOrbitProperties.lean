import ShenWork.PaperOne.WholeLineBarrierInequalities
import ShenWork.PaperOne.WholeLineTravelingWaveExistence
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

open Filter Set Topology MeasureTheory
open scoped Topology

noncomputable section

namespace ShenWork.PaperOne

/-!
Orbit trapping and spatial antitonicity for the whole-line auxiliary flow.

The trapping layer consumes the exponential barrier comparison brick together
with the discharged barrier inequalities in `WholeLineBarrierInequalities`.
The spatial monotonicity layer consumes the weak parabolic comparison brick
for the differentiated field `q = w_x`.  The analytic construction of that
differentiated comparison datum is kept explicit as named auxiliary-flow data.
-/

/-- The comparison packages needed on a single spatial-derivative horizon. -/
structure WholeLineSpatialAntitoneHorizonData
    (q qt qx qxx a b : ℝ → ℝ → ℝ) (T : ℝ) where
  A : ℝ
  Bb : ℝ
  comparison : WholeLineWeakParabolicComparisonData q qt qx qxx a b T A Bb

/--
Named data saying that the spatial derivative `q = w_x` is eligible for Brick 7.

The fields `q_eq_deriv`, `slice_differentiable`, and
`initial_deriv_eq_upper` are the carried auxiliary-flow regularity and trace
identifications.  The `comparison` field is the differentiated weak parabolic
comparison datum on every finite positive horizon.
-/
structure WholeLineSpatialAntitoneData
    (κ : ℝ) (w q qt qx qxx a b : ℝ → ℝ → ℝ) where
  q_eq_deriv : ∀ t x, q t x = deriv (w t) x
  slice_differentiable : ∀ t, Differentiable ℝ (w t)
  initial_deriv_eq_upper :
    ∀ x, q 0 x = deriv (upperBarrier κ) x
  comparison : ∀ T, 0 < T →
    WholeLineSpatialAntitoneHorizonData q qt qx qxx a b T

/-- A packaged differentiated comparison witness for one frozen orbit. -/
structure WholeLineSpatialAntitoneWitness
    (κ : ℝ) (w : ℝ → ℝ → ℝ) where
  q : ℝ → ℝ → ℝ
  qt : ℝ → ℝ → ℝ
  qx : ℝ → ℝ → ℝ
  qxx : ℝ → ℝ → ℝ
  a : ℝ → ℝ → ℝ
  b : ℝ → ℝ → ℝ
  data : WholeLineSpatialAntitoneData κ w q qt qx qxx a b

/-- The initial derivative trace is nonpositive because the upper barrier is
antitone. -/
theorem WholeLineSpatialAntitoneData.initial_nonpos
    {κ : ℝ} {w q qt qx qxx a b : ℝ → ℝ → ℝ}
    (H : WholeLineSpatialAntitoneData κ w q qt qx qxx a b)
    (hκ : 0 < κ) :
    ∀ x, q 0 x ≤ 0 := by
  intro x
  rw [H.initial_deriv_eq_upper x]
  exact (upperBarrier_antitone hκ).deriv_nonpos

/-- Brick 7 applied to `q = w_x` on a finite closed horizon. -/
theorem wholeLine_spatial_derivative_nonpos_on
    {κ T : ℝ} {w q qt qx qxx a b : ℝ → ℝ → ℝ}
    (H : WholeLineSpatialAntitoneData κ w q qt qx qxx a b)
    (hκ : 0 < κ) (hT : 0 < T) :
    ∀ t, 0 ≤ t → t ≤ T → ∀ x, q t x ≤ 0 := by
  intro t ht0 htT x
  let HT := H.comparison T hT
  exact
    wholeLine_weak_parabolic_comparison
      (q := q) (qt := qt) (qx := qx) (qxx := qxx)
      (a := a) (b := b) (T := T) (A := HT.A) (Bb := HT.Bb)
      (hinitial := H.initial_nonpos hκ)
      (H := HT.comparison) t ht0 htT x

/-- Global forward-time derivative sign from finite-horizon comparison. -/
theorem wholeLine_spatial_derivative_nonpos
    {κ : ℝ} {w q qt qx qxx a b : ℝ → ℝ → ℝ}
    (H : WholeLineSpatialAntitoneData κ w q qt qx qxx a b)
    (hκ : 0 < κ) :
    ∀ t, 0 ≤ t → ∀ x, q t x ≤ 0 := by
  intro t ht0 x
  have hT : 0 < t + 1 := by linarith
  have htT : t ≤ t + 1 := by linarith
  exact wholeLine_spatial_derivative_nonpos_on H hκ hT t ht0 htT x

/-- Spatial antitonicity of the auxiliary orbit on forward time. -/
theorem orbit_spatial_antitone_forward
    {κ : ℝ} {w q qt qx qxx a b : ℝ → ℝ → ℝ}
    (H : WholeLineSpatialAntitoneData κ w q qt qx qxx a b)
    (hκ : 0 < κ) :
    ∀ t, 0 ≤ t → Antitone (w t) := by
  intro t ht0
  refine antitone_of_deriv_nonpos (H.slice_differentiable t) ?_
  intro x
  have hq := wholeLine_spatial_derivative_nonpos H hκ t ht0 x
  simpa [H.q_eq_deriv t x] using hq

/--
Named data for trapping one frozen auxiliary orbit.

The barrier-inequality fields are exactly the hypotheses consumed by
`wholeLineExponentialBarrierInequalities_of_waveExponent`; the comparison
fields are the upper/lower Brick 6 packages on every positive horizon.
-/
structure WholeLineOrbitTrappingData
    (p : CMParams) (c κt D : ℝ)
    (w : ℝ → ℝ → ℝ) (V Vx : ℝ → ℝ) where
  speed_ge : 2 ≤ c
  kappa_lt_kappat : waveExponent c < κt
  D_ge_one : 1 ≤ D
  kappat_le_alpha : κt ≤ (1 + p.α) * waveExponent c
  kappat_le_m : κt ≤ p.m * waveExponent c + 1 / 2
  kappat_le_one : κt ≤ 1
  upper_constant_branch :
    ∀ x, x ≤ 0 → 0 ≤ p.χ * (1 - V x)
  upper_domination :
    UpperExponentialBranchDomination p (waveExponent c) V Vx
  lower_domination :
    LowerPositiveBranchDomination p c (waveExponent c) κt D V Vx
  initial_eq_upper :
    ∀ x, w 0 x = upperBarrier (waveExponent c) x
  upper_comparison : ∀ T, 0 < T →
    WholeLineExponentialUpperComparisonData (waveExponent c) T w
  lower_comparison : ∀ T, 0 < T →
    WholeLineExponentialLowerComparisonData (waveExponent c) κt D T w

/-- Assemble the discharged branch inequalities for the frozen orbit. -/
def WholeLineOrbitTrappingData.barrierInequalities
    {p : CMParams} {c κt D : ℝ}
    {w : ℝ → ℝ → ℝ} {V Vx : ℝ → ℝ}
    (H : WholeLineOrbitTrappingData p c κt D w V Vx) :
    WholeLineExponentialBarrierInequalities
      p c (waveExponent c) κt D V Vx :=
  wholeLineExponentialBarrierInequalities_of_waveExponent
    (p := p) (c := c) (κt := κt) (D := D)
    (V := V) (Vx := Vx)
    H.speed_ge H.kappa_lt_kappat H.D_ge_one
    H.kappat_le_alpha H.kappat_le_m H.kappat_le_one
    H.upper_constant_branch H.upper_domination H.lower_domination

/-- Assemble the finite-horizon Brick 6 trapping datum. -/
def WholeLineOrbitTrappingData.toBarrierTrappingData
    {p : CMParams} {c κt D T : ℝ}
    {w : ℝ → ℝ → ℝ} {V Vx : ℝ → ℝ}
    (H : WholeLineOrbitTrappingData p c κt D w V Vx) (hT : 0 < T) :
    WholeLineExponentialBarrierTrappingData
      p c (waveExponent c) κt D T w V Vx where
  barrier_ineq := H.barrierInequalities
  upper := H.upper_comparison T hT
  lower := H.lower_comparison T hT

/-- Forward-time orbit trapping from Brick 6 and the barrier inequalities. -/
theorem orbit_trapping_forward
    {p : CMParams} {c κt D : ℝ}
    {w : ℝ → ℝ → ℝ} {V Vx : ℝ → ℝ}
    (H : WholeLineOrbitTrappingData p c κt D w V Vx) :
    ∀ t, 0 ≤ t → ∀ x,
      lowerBarrier (waveExponent c) κt D x ≤ w t x ∧
        w t x ≤ upperBarrier (waveExponent c) x := by
  exact
    wholeLine_exponential_barrier_trapping
      (p := p) (c := c) (κ := waveExponent c) (κt := κt) (D := D)
      (w := w) (V := V) (Vx := Vx)
      H.initial_eq_upper
      (fun T hT => H.toBarrierTrappingData (T := T) hT)

/-- Forward-time lower barrier field. -/
theorem orbit_lower_bound_forward
    {p : CMParams} {c κt D : ℝ}
    {w : ℝ → ℝ → ℝ} {V Vx : ℝ → ℝ}
    (H : WholeLineOrbitTrappingData p c κt D w V Vx) :
    ∀ t, 0 ≤ t → ∀ x,
      lowerBarrier (waveExponent c) κt D x ≤ w t x := by
  intro t ht x
  exact (orbit_trapping_forward H t ht x).1

/-- Forward-time upper barrier field. -/
theorem orbit_upper_bound_forward
    {p : CMParams} {c κt D : ℝ}
    {w : ℝ → ℝ → ℝ} {V Vx : ℝ → ℝ}
    (H : WholeLineOrbitTrappingData p c κt D w V Vx) :
    ∀ t, 0 ≤ t → ∀ x,
      w t x ≤ upperBarrier (waveExponent c) x := by
  intro t ht x
  exact (orbit_trapping_forward H t ht x).2

/--
Forward-orbit extension to all real times.  For negative time the profile is
the upper barrier, so the all-time fields required by the long-time map do not
add extra parabolic content.
-/
def wholeLineForwardOrbitExtension
    (κ : ℝ) (w : (ℝ → ℝ) → ℝ → ℝ → ℝ) :
    (ℝ → ℝ) → ℝ → ℝ → ℝ :=
  fun U t x => if 0 ≤ t then w U t x else upperBarrier κ x

/-- All orbit-property data for the frozen auxiliary flow family. -/
structure WholeLineOrbitPropertiesData
    (p : CMParams) (c κt D : ℝ)
    (w : (ℝ → ℝ) → ℝ → ℝ → ℝ) where
  trapping : ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
    WholeLineOrbitTrappingData p c κt D (w U)
      (frozenSignal p.γ U)
      (fun x => deriv (frozenSignal p.γ U) x)
  spatial : ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
    WholeLineSpatialAntitoneWitness (waveExponent c) (w U)

/-- The lower-bound field for the all-time forward extension. -/
theorem wholeLine_orbit_lower_bound
    {p : CMParams} {c κt D : ℝ}
    {w : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    (H : WholeLineOrbitPropertiesData p c κt D w) :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      ∀ t x,
        lowerBarrier (waveExponent c) κt D x ≤
          wholeLineForwardOrbitExtension (waveExponent c) w U t x := by
  intro U hU t x
  by_cases ht : 0 ≤ t
  · simpa [wholeLineForwardOrbitExtension, ht] using
      orbit_lower_bound_forward (H.trapping U hU) t ht x
  · have Htrap := H.trapping U hU
    have hκ : 0 ≤ waveExponent c := (waveExponent_pos Htrap.speed_ge).le
    simpa [wholeLineForwardOrbitExtension, ht] using
      lowerBarrier_le_upper
        (κ := waveExponent c) (κt := κt) (D := D) (x := x)
        hκ Htrap.kappa_lt_kappat Htrap.D_ge_one

/-- The upper-bound field for the all-time forward extension. -/
theorem wholeLine_orbit_upper_bound
    {p : CMParams} {c κt D : ℝ}
    {w : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    (H : WholeLineOrbitPropertiesData p c κt D w) :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      ∀ t x,
        wholeLineForwardOrbitExtension (waveExponent c) w U t x ≤
          upperBarrier (waveExponent c) x := by
  intro U hU t x
  by_cases ht : 0 ≤ t
  · simpa [wholeLineForwardOrbitExtension, ht] using
      orbit_upper_bound_forward (H.trapping U hU) t ht x
  · simp [wholeLineForwardOrbitExtension, ht]

/-- The spatial-antitonicity field for the all-time forward extension. -/
theorem wholeLine_orbit_spatial_antitone
    {p : CMParams} {c κt D : ℝ}
    {w : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    (H : WholeLineOrbitPropertiesData p c κt D w) :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      ∀ t, Antitone
        (wholeLineForwardOrbitExtension (waveExponent c) w U t) := by
  intro U hU t
  have Htrap := H.trapping U hU
  have hκ : 0 < waveExponent c := waveExponent_pos Htrap.speed_ge
  by_cases ht : 0 ≤ t
  · rcases H.spatial U hU with ⟨q, qt, qx, qxx, a, b, Hspace⟩
    intro x y hxy
    have hanti := orbit_spatial_antitone_forward Hspace hκ t ht hxy
    simpa [wholeLineForwardOrbitExtension, ht] using hanti
  · intro x y hxy
    have hanti := upperBarrier_antitone hκ hxy
    simpa [wholeLineForwardOrbitExtension, ht] using hanti

/--
The three orbit fields in exactly the shape expected by
`WholeLineTravelingWaveData`, for the all-time forward extension of the raw
auxiliary flow.
-/
theorem wholeLine_orbit_fields
    {p : CMParams} {c κt D : ℝ}
    {w : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    (H : WholeLineOrbitPropertiesData p c κt D w) :
    (∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      ∀ t x,
        lowerBarrier (waveExponent c) κt D x ≤
          wholeLineForwardOrbitExtension (waveExponent c) w U t x) ∧
    (∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      ∀ t x,
        wholeLineForwardOrbitExtension (waveExponent c) w U t x ≤
          upperBarrier (waveExponent c) x) ∧
    (∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      ∀ t,
        Antitone (wholeLineForwardOrbitExtension (waveExponent c) w U t)) := by
  exact
    ⟨wholeLine_orbit_lower_bound H,
      wholeLine_orbit_upper_bound H,
      wholeLine_orbit_spatial_antitone H⟩

#print axioms WholeLineSpatialAntitoneData.initial_nonpos
#print axioms wholeLine_spatial_derivative_nonpos_on
#print axioms wholeLine_spatial_derivative_nonpos
#print axioms orbit_spatial_antitone_forward
#print axioms WholeLineOrbitTrappingData.barrierInequalities
#print axioms WholeLineOrbitTrappingData.toBarrierTrappingData
#print axioms orbit_trapping_forward
#print axioms orbit_lower_bound_forward
#print axioms orbit_upper_bound_forward
#print axioms wholeLine_orbit_lower_bound
#print axioms wholeLine_orbit_upper_bound
#print axioms wholeLine_orbit_spatial_antitone
#print axioms wholeLine_orbit_fields

end ShenWork.PaperOne
