import ShenWork.Paper2.IntervalBFormDirectClassical
import ShenWork.Paper2.IntervalBFormPositiveDatumLocalExistenceSq
import ShenWork.Paper2.IntervalChiNegH1ZeroStartPrimitiveTraceReducer
import ShenWork.Paper2.IntervalPicardLimitSliceTimeContinuity
import ShenWork.PDE.P3MoserEnergyContinuity

/-!
# B-form zero-start trace consumer for the H¹ source route

The raw B-form Picard representative stores zero at `t = 0`, so it cannot be
used directly as initialized zero-start data.  This file reanchors the stored
zero slices of both `u` and `v`, then composes the direct B-form classical
solution with the explicit zero-face trace frontier from
`IntervalChiNegH1ZeroStartPrimitiveTraceReducer`.

It does not prove the zero-face C¹ traces.  Those remain the analytic frontier.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
  (classicalSolutionLocalityUnderIooAgreement_intervalDomain)
open ShenWork.IntervalMildPicard
  (GradientMildSolutionData)
open ShenWork.IntervalPicardLimitBddHcontP
  (patchedSlice patchedSlice_of_nonpos)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceData conjugatePicardLimit)
open ShenWork.IntervalMildToClassical
  (mildChemicalConcentration)
open ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
open ShenWork.Paper2
open ShenWork.Paper2.BFormDirectClassical
open ShenWork.Paper2.BFormPositiveDatumLocalSq

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1ZeroStartComponents

/-- Value/sign zero-face data, separated from the derivative trace frontier. -/
structure H1ZeroStartPrimitiveValueZeroFaceTrace
    (u v : ℝ → intervalDomainPoint → ℝ) (T : ℝ) : Prop where
  u_zeroFace : ∀ {b : ℝ}, 0 ≤ b → b < T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
    ContinuousWithinAt
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1) (0, x)
  v_zeroFace : ∀ {b : ℝ}, 0 ≤ b → b < T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
    ContinuousWithinAt
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1) (0, x)
  u_zero_pos : ∀ x : intervalDomainPoint, 0 < u (0 : ℝ) x
  v_zero_nonneg : ∀ x : intervalDomainPoint, 0 ≤ v (0 : ℝ) x

/-- Derivative zero-face data, isolated as the analytic C¹ frontier. -/
structure H1ZeroStartPrimitiveDerivativeZeroFaceTrace
    (u v : ℝ → intervalDomainPoint → ℝ) (T : ℝ) : Prop where
  ux_zeroFace : ∀ {b : ℝ}, 0 ≤ b → b < T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
    ContinuousWithinAt
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) => deriv (intervalDomainLift (u t)) x))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1) (0, x)
  vx_zeroFace : ∀ {b : ℝ}, 0 ≤ b → b < T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
    ContinuousWithinAt
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) => deriv (intervalDomainLift (v t)) x))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1) (0, x)

/-- Combine the value/sign zero-face package with the derivative zero-face
frontier into the full C¹ zero-face trace record. -/
theorem H1ZeroStartPrimitiveC1ZeroFaceTrace_of_value_derivative
    {u v : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (hv : H1ZeroStartPrimitiveValueZeroFaceTrace u v T)
    (hd : H1ZeroStartPrimitiveDerivativeZeroFaceTrace u v T) :
    H1ZeroStartPrimitiveC1ZeroFaceTrace u v T where
  u_zeroFace := hv.u_zeroFace
  v_zeroFace := hv.v_zeroFace
  ux_zeroFace := hd.ux_zeroFace
  vx_zeroFace := hd.vx_zeroFace
  u_zero_pos := hv.u_zero_pos
  v_zero_nonneg := hv.v_zero_nonneg

/-- The patched Picard u-slice has the required value zero-face continuity.
This uses the existing uniform-in-space time continuity at zero and the spatial
continuity of the initial datum. -/
theorem patchedSlice_lift_zeroFace_of_timeContinuousAt_zero
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hu₀cont : Continuous u₀)
    (D : GradientMildSolutionData p u₀) :
    ∀ {b : ℝ}, 0 ≤ b → b ≤ D.T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ContinuousWithinAt
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) =>
            intervalDomainLift (patchedSlice u₀ D.u t) x))
        (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1) (0, x) := by
  intro b _hb0 hbT x hx
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨δt, hδt_pos, hδt⟩ :=
    ShenWork.IntervalPicardLimitSliceTimeContinuity.patchedSlice_timeContinuousAt_zero
      hu₀cont D (ε / 2) hε2
  have hu₀_lift_cont : ContinuousOn (intervalDomainLift u₀) (Set.Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    have hrestrict :
        Set.restrict (Set.Icc (0 : ℝ) 1) (intervalDomainLift u₀) = u₀ := by
      ext z
      simp [Set.restrict, intervalDomainLift]
    rw [hrestrict]
    exact hu₀cont
  have hspatial_cont :
      ContinuousWithinAt (intervalDomainLift u₀) (Set.Icc (0 : ℝ) 1) x :=
    hu₀_lift_cont x hx
  rw [Metric.continuousWithinAt_iff] at hspatial_cont
  obtain ⟨δx, hδx_pos, hδx⟩ := hspatial_cont (ε / 2) hε2
  refine ⟨min δt δx, lt_min hδt_pos hδx_pos, ?_⟩
  rintro ⟨t, y⟩ ⟨htb, hy⟩ hdist
  have hdist_t : dist t (0 : ℝ) < δt := by
    have hprod : dist (t, y) (0, x) < δt :=
      lt_of_lt_of_le hdist (min_le_left _ _)
    have hle : dist t (0 : ℝ) ≤ dist (t, y) (0, x) := by
      rw [Prod.dist_eq]
      exact le_max_left _ _
    exact lt_of_le_of_lt hle hprod
  have hdist_x : dist y x < δx := by
    have hprod : dist (t, y) (0, x) < δx :=
      lt_of_lt_of_le hdist (min_le_right _ _)
    have hle : dist y x ≤ dist (t, y) (0, x) := by
      rw [Prod.dist_eq]
      exact le_max_right _ _
    exact lt_of_le_of_lt hle hprod
  have htD : t ∈ Set.Icc (0 : ℝ) D.T := ⟨htb.1, le_trans htb.2 hbT⟩
  let Y : intervalDomainPoint := ⟨y, hy⟩
  let X : intervalDomainPoint := ⟨x, hx⟩
  have htime :
      |patchedSlice u₀ D.u t Y - u₀ Y| < ε / 2 := by
    have h :=
      hδt t htD (by simpa [Real.dist_eq] using hdist_t) Y
    simpa [Y, patchedSlice_of_nonpos u₀ D.u (le_refl (0 : ℝ))] using h
  have hspace :
      |u₀ Y - u₀ X| < ε / 2 := by
    have h := hδx hy (by simpa [Real.dist_eq] using hdist_x)
    simpa [Real.dist_eq, intervalDomainLift, Y, X, hy, hx] using h
  have hval_ty :
      Function.uncurry
          (fun (t : ℝ) (x : ℝ) =>
            intervalDomainLift (patchedSlice u₀ D.u t) x) (t, y) =
        patchedSlice u₀ D.u t Y := by
    simp [Function.uncurry, intervalDomainLift, Y, hy]
  have hval_0x :
      Function.uncurry
          (fun (t : ℝ) (x : ℝ) =>
            intervalDomainLift (patchedSlice u₀ D.u t) x) (0, x) =
        u₀ X := by
    simp [Function.uncurry, intervalDomainLift, X, hx,
      patchedSlice_of_nonpos u₀ D.u (le_refl (0 : ℝ))]
  rw [hval_ty, hval_0x, Real.dist_eq]
  calc
    |patchedSlice u₀ D.u t Y - u₀ X|
        = |(patchedSlice u₀ D.u t Y - u₀ Y) + (u₀ Y - u₀ X)| := by
          ring_nf
    _ ≤ |patchedSlice u₀ D.u t Y - u₀ Y| + |u₀ Y - u₀ X| :=
          abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add htime hspace
    _ = ε := by ring

/-- Direct B-form classical data plus explicit zero-face primitive C¹ traces
for the reanchored Picard pair supplies the initialized source package.

The theorem is intentionally a consumer of `H1ZeroStartPrimitiveC1ZeroFaceTrace`:
the B-form frontier proves strict positive-time classical regularity, while the
closed zero-time face remains separate. -/
theorem H1ZeroStartInitializedPrimitiveC1SignSource_of_BFormDirect_zeroFace
    {p : CM2Params} {u₀ v₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (F : BFormDirectFrontier p DB)
    (hface : H1ZeroStartPrimitiveC1ZeroFaceTrace
      (intervalDomainWithInitialSlice u₀
        (conjugatePicardLimit p u₀ DB.T))
      (intervalDomainWithInitialSlice v₀
        (mildChemicalConcentration p
          (conjugatePicardLimit p u₀ DB.T)))
      DB.T) :
    H1ZeroStartInitializedPrimitiveC1SignSource u₀ v₀
      (intervalDomainWithInitialSlice u₀
        (conjugatePicardLimit p u₀ DB.T))
      (intervalDomainWithInitialSlice v₀
        (mildChemicalConcentration p
          (conjugatePicardLimit p u₀ DB.T)))
      DB.T := by
  let uZ : ℝ → intervalDomainPoint → ℝ :=
    intervalDomainWithInitialSlice u₀
      (conjugatePicardLimit p u₀ DB.T)
  let vZ : ℝ → intervalDomainPoint → ℝ :=
    intervalDomainWithInitialSlice v₀
      (mildChemicalConcentration p
        (conjugatePicardLimit p u₀ DB.T))
  have hraw :
      IsPaper2ClassicalSolution intervalDomain p DB.T
        (conjugatePicardLimit p u₀ DB.T)
        (mildChemicalConcentration p
          (conjugatePicardLimit p u₀ DB.T)) :=
    intervalConjugatePicardLimit_isClassicalSolution_direct F
  have hsolZ :
      IsPaper2ClassicalSolution intervalDomain p DB.T uZ vZ := by
    exact
      (classicalSolutionLocalityUnderIooAgreement_intervalDomain p)
      DB.hT hraw (by
        intro t ht0 _htT x
        have ht_ne : t ≠ 0 := ne_of_gt ht0
        constructor <;> simp [uZ, vZ, intervalDomainWithInitialSlice, ht_ne])
  have hu0 : uZ (0 : ℝ) = u₀ := by
    funext x
    simp [uZ, intervalDomainWithInitialSlice]
  have hv0 : vZ (0 : ℝ) = v₀ := by
    funext x
    simp [vZ, intervalDomainWithInitialSlice]
  exact
    H1ZeroStartInitializedPrimitiveC1SignSource_of_classical_zeroFace
      (p := p) hu0 hv0 hsolZ hface

/-- Squared-barrier B-form components consume the same explicit zero-face trace
frontier after reanchoring the raw Picard pair at `t = 0`. -/
theorem H1ZeroStartInitializedPrimitiveC1SignSource_of_BFormSq_zeroFace
    {p : CM2Params} {u₀ v₀ : intervalDomainPoint → ℝ}
    (K : PositiveDatumBFormLocalComponentsSq p u₀)
    (hface : H1ZeroStartPrimitiveC1ZeroFaceTrace
      (intervalDomainWithInitialSlice u₀
        (conjugatePicardLimit p u₀ K.DB.T))
      (intervalDomainWithInitialSlice v₀
        (mildChemicalConcentration p
          (conjugatePicardLimit p u₀ K.DB.T)))
      K.DB.T) :
    H1ZeroStartInitializedPrimitiveC1SignSource u₀ v₀
      (intervalDomainWithInitialSlice u₀
        (conjugatePicardLimit p u₀ K.DB.T))
      (intervalDomainWithInitialSlice v₀
        (mildChemicalConcentration p
          (conjugatePicardLimit p u₀ K.DB.T)))
      K.DB.T := by
  let uZ : ℝ → intervalDomainPoint → ℝ :=
    intervalDomainWithInitialSlice u₀
      (conjugatePicardLimit p u₀ K.DB.T)
  let vZ : ℝ → intervalDomainPoint → ℝ :=
    intervalDomainWithInitialSlice v₀
      (mildChemicalConcentration p
        (conjugatePicardLimit p u₀ K.DB.T))
  have hraw :
      IsPaper2ClassicalSolution intervalDomain p K.DB.T
        (conjugatePicardLimit p u₀ K.DB.T)
        (mildChemicalConcentration p
          (conjugatePicardLimit p u₀ K.DB.T)) :=
    K.isClassicalSolution
  have hsolZ :
      IsPaper2ClassicalSolution intervalDomain p K.DB.T uZ vZ := by
    exact
      (classicalSolutionLocalityUnderIooAgreement_intervalDomain p)
      K.DB.hT hraw (by
        intro t ht0 _htT x
        have ht_ne : t ≠ 0 := ne_of_gt ht0
        constructor <;> simp [uZ, vZ, intervalDomainWithInitialSlice, ht_ne])
  have hu0 : uZ (0 : ℝ) = u₀ := by
    funext x
    simp [uZ, intervalDomainWithInitialSlice]
  have hv0 : vZ (0 : ℝ) = v₀ := by
    funext x
    simp [vZ, intervalDomainWithInitialSlice]
  exact
    H1ZeroStartInitializedPrimitiveC1SignSource_of_classical_zeroFace
      (p := p) hu0 hv0 hsolZ hface

section AxiomAudit

#print axioms H1ZeroStartInitializedPrimitiveC1SignSource_of_BFormDirect_zeroFace
#print axioms H1ZeroStartInitializedPrimitiveC1SignSource_of_BFormSq_zeroFace
#print axioms H1ZeroStartPrimitiveC1ZeroFaceTrace_of_value_derivative
#print axioms patchedSlice_lift_zeroFace_of_timeContinuousAt_zero

end AxiomAudit

end ShenWork.Paper2.IntervalChiNegH1ZeroStartComponents
