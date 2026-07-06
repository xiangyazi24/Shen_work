import ShenWork.Paper2.IntervalBFormDirectClassical
import ShenWork.Paper2.IntervalBFormPositiveDatumLocalExistenceSq
import ShenWork.Paper2.IntervalChiNegH1ZeroStartPrimitiveTraceReducer
import ShenWork.Paper2.IntervalDuhamelIntegrability
import ShenWork.Paper2.IntervalPicardLimitSliceTimeContinuity
import ShenWork.Paper2.IntervalResolverWeakBounds
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
  (patchedSlice patchedSlice_of_nonpos patchedSlice_of_pos)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceData conjugatePicardLimit)
open ShenWork.IntervalMildToClassical
  (mildChemicalConcentration mildChemical_nonneg)
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

/-- Static resolver nonnegativity for a continuous nonnegative interval profile.
This is the time-free form of `mildChemical_nonneg`. -/
theorem intervalNeumannResolverR_nonneg_of_continuous_nonneg
    (p : CM2Params) {w : intervalDomainPoint → ℝ}
    (hw_cont : Continuous w)
    (hw_nonneg : ∀ y : intervalDomainPoint, 0 ≤ w y) :
    ∀ x : intervalDomainPoint, 0 ≤ ShenWork.PDE.intervalNeumannResolverR p w x := by
  intro x
  have hcont_on : ContinuousOn (intervalDomainLift w) (Set.Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    have : Set.restrict (Set.Icc (0 : ℝ) 1) (intervalDomainLift w) = w := by
      ext ⟨y, hy⟩
      simp [Set.restrict, intervalDomainLift, hy]
      rfl
    rw [this]
    exact hw_cont
  have hcont_src : Continuous
      (fun y : intervalDomainPoint => p.ν * (w y) ^ p.γ) :=
    continuous_const.mul (hw_cont.rpow_const (fun _ => Or.inr p.hγ.le))
  set clip : ℝ → intervalDomainPoint := fun y =>
    ⟨max 0 (min y 1), le_max_left 0 _,
      max_le (by norm_num) (min_le_right y 1)⟩
  have hclip_cont : Continuous clip :=
    Continuous.subtype_mk
      (continuous_const.max (continuous_id.min continuous_const)) _
  set f : ℝ → ℝ :=
    (fun y : intervalDomainPoint => p.ν * (w y) ^ p.γ) ∘ clip
  have hf_cont : Continuous f := hcont_src.comp hclip_cont
  have hf_nonneg : ∀ z, 0 ≤ f z := fun _ =>
    mul_nonneg p.hν.le (Real.rpow_nonneg (hw_nonneg _) _)
  have hf_coeff : ∀ k, ShenWork.IntervalNeumannFullKernel.cosineCoeffs f k =
      (ShenWork.PDE.intervalNeumannResolverSourceCoeff p w k).re := by
    intro k
    have hsrc_eq :
        (ShenWork.PDE.intervalNeumannResolverSourceCoeff p w k).re =
        ShenWork.IntervalNeumannFullKernel.cosineCoeffs
          (fun y => p.ν * intervalDomainLift w y ^ p.γ) k := by
      simp [ShenWork.IntervalNeumannFullKernel.cosineCoeffs,
        ShenWork.PDE.intervalNeumannResolverSourceCoeff, Complex.ofReal_re]
    rw [hsrc_eq]
    exact cosineCoeffs_congr_on_Icc (fun y hy => by
      simp only [f, Function.comp, clip]
      have hclip_eq : max 0 (min y 1) = y := by
        rw [min_eq_left hy.2, max_eq_right hy.1]
      simp only [hclip_eq, intervalDomainLift,
        dif_pos (Set.mem_Icc.mpr hy)]) k
  have ha_sq :
      Summable
        (fun k => (ShenWork.IntervalNeumannFullKernel.cosineCoeffs f k) ^ 2) := by
    have h :=
      ShenWork.IntervalResolverWeakBounds.resolverSourceCoeff_re_sq_summable_of_continuousOn
        p hcont_on
    simp only [ShenWork.Paper2.intervalNeumannResolverSourceCoeff_zero, sub_zero] at h
    exact h.congr (fun k => by rw [hf_coeff])
  exact
    ShenWork.IntervalResolverPositivity.intervalNeumannResolverR_nonneg_of_nonneg_source
      hf_cont hf_nonneg hf_coeff ha_sq x

/-- Paper-positive data give a nonnegative initial elliptic resolver. -/
theorem intervalNeumannResolverR_nonneg_of_paperPositiveInitialDatum
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀) :
    ∀ x : intervalDomainPoint, 0 ≤ ShenWork.PDE.intervalNeumannResolverR p u₀ x := by
  have hu₀_cont : Continuous u₀ := (PaperPositiveInitialDatum.admissible hu₀).2
  obtain ⟨η, hη, hfloor⟩ := PaperPositiveInitialDatum.floor hu₀
  exact intervalNeumannResolverR_nonneg_of_continuous_nonneg p hu₀_cont
    (fun y => le_trans (le_of_lt hη) (hfloor y))

/-- Initialised chemical concentration: the resolver of the initial datum at
`t ≤ 0`, and the usual mild chemical concentration at positive time. -/
noncomputable def patchedChemical (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ)
    (t : ℝ) : intervalDomainPoint → ℝ :=
  if t ≤ 0 then ShenWork.PDE.intervalNeumannResolverR p u₀
  else mildChemicalConcentration p u t

theorem patchedChemical_of_nonpos (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    {t : ℝ} (ht : t ≤ 0) :
    patchedChemical p u₀ u t = ShenWork.PDE.intervalNeumannResolverR p u₀ := by
  simp [patchedChemical, ht]

theorem patchedChemical_of_pos (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    {t : ℝ} (ht : 0 < t) :
    patchedChemical p u₀ u t = mildChemicalConcentration p u t := by
  simp [patchedChemical, not_le.mpr ht]

theorem patchedChemical_zero (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ) (u : ℝ → intervalDomainPoint → ℝ) :
    patchedChemical p u₀ u 0 = ShenWork.PDE.intervalNeumannResolverR p u₀ :=
  patchedChemical_of_nonpos p u₀ u le_rfl

/-- The zero-time patched chemical concentration is nonnegative for
paper-positive data. -/
theorem patchedChemical_zero_nonneg_of_paperPositiveInitialDatum
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (u : ℝ → intervalDomainPoint → ℝ)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀) :
    ∀ x : intervalDomainPoint, 0 ≤ patchedChemical p u₀ u 0 x := by
  intro x
  rw [patchedChemical_zero]
  exact intervalNeumannResolverR_nonneg_of_paperPositiveInitialDatum p hu₀ x

/-- Positive-time patched chemical nonnegativity from the existing mild resolver
theorem. -/
theorem patchedChemical_pos_time_nonneg
    (p : CM2Params) {T : ℝ} {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (hu_nonneg : ∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ u t x)
    (hu_cont : ShenWork.IntervalMildPicard.HasContinuousSlices T u)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    ∀ x : intervalDomainPoint, 0 ≤ patchedChemical p u₀ u t x := by
  intro x
  rw [patchedChemical_of_pos p u₀ u ht]
  exact mildChemical_nonneg p hu_nonneg hu_cont ht htT x

/-- The lifted static resolver profile is spatially continuous on the closed
interval whenever the source profile is continuous on the subtype. -/
theorem intervalNeumannResolverR_lift_continuousOn
    (p : CM2Params) {w : intervalDomainPoint → ℝ} (hw_cont : Continuous w) :
    ContinuousOn
      (intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w))
      (Set.Icc (0 : ℝ) 1) := by
  have hcont_on :
      ContinuousOn (intervalDomainLift w) (Set.Icc (0 : ℝ) 1) :=
    ShenWork.IntervalPicardLimitBddHcontP.lift_continuousOn_Icc hw_cont
  have hseries_cont : Continuous (fun y : ℝ =>
      ∑' k : ℕ, (ShenWork.PDE.intervalNeumannResolverCoeff p w k).re *
        unitIntervalCosineMode k y) :=
    ShenWork.IntervalDuhamelIntegrability.resolverValueReal_continuous_of_continuousOn
      p hcont_on
  refine hseries_cont.continuousOn.congr ?_
  intro y hy
  simp [intervalDomainLift, hy, ShenWork.PDE.intervalNeumannResolverR]

/-- The patched chemical concentration is uniformly time-continuous at zero in
the resolver value, provided the patched u-slices stay in a common nonnegative
`M`-ball. -/
theorem patchedChemical_timeContinuousAt_zero_of_patchedSlice_ball
    {p : CM2Params} (hγ : 1 ≤ p.γ) {u₀ : intervalDomainPoint → ℝ}
    (hu₀cont : Continuous u₀) (D : GradientMildSolutionData p u₀)
    {M : ℝ} (hM : 0 < M)
    (hu₀_mem : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift u₀ x ∈ Set.Icc (0 : ℝ) M)
    (hpatch_mem : ∀ t ∈ Set.Icc (0 : ℝ) D.T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (patchedSlice u₀ D.u t) x ∈ Set.Icc (0 : ℝ) M) :
    ∀ ε > 0, ∃ δ > 0,
      ∀ t ∈ Set.Icc (0 : ℝ) D.T, |t - 0| < δ →
        ∀ x : intervalDomainPoint,
          |patchedChemical p u₀ D.u t x - patchedChemical p u₀ D.u 0 x| < ε := by
  intro ε hε
  let C : ℝ :=
    Real.sqrt (∑' k : ℕ, (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2) *
      (2 * (p.ν * (p.γ * M ^ (p.γ - 1))))
  have hγ_nonneg : 0 ≤ p.γ := le_trans (by norm_num : (0 : ℝ) ≤ 1) hγ
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num)
        (mul_nonneg p.hν.le
          (mul_nonneg hγ_nonneg (Real.rpow_nonneg hM.le _))))
  have hCden_pos : 0 < C + 1 := by linarith
  have hεC : 0 < ε / (C + 1) := div_pos hε hCden_pos
  obtain ⟨δ, hδpos, hδ⟩ :=
    ShenWork.IntervalPicardLimitSliceTimeContinuity.patchedSlice_timeContinuousAt_zero
      hu₀cont D (ε / (C + 1)) hεC
  refine ⟨δ, hδpos, ?_⟩
  intro t htD htdist x
  by_cases htzero : t = 0
  · subst t
    rw [sub_self, abs_zero]
    exact hε
  have htpos : 0 < t := lt_of_le_of_ne htD.1 (Ne.symm htzero)
  have hUc₁ :
      ContinuousOn (intervalDomainLift (D.u t)) (Set.Icc (0 : ℝ) 1) :=
    ShenWork.IntervalPicardLimitBddHcontP.lift_continuousOn_Icc
      (D.hcont t htpos htD.2)
  have hUc₂ :
      ContinuousOn (intervalDomainLift u₀) (Set.Icc (0 : ℝ) 1) :=
    ShenWork.IntervalPicardLimitBddHcontP.lift_continuousOn_Icc hu₀cont
  have hmem₁ : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (D.u t) y ∈ Set.Icc (0 : ℝ) M := by
    intro y hy
    simpa [patchedSlice_of_pos u₀ D.u htpos] using hpatch_mem t htD y hy
  have hD : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |intervalDomainLift (D.u t) y - intervalDomainLift u₀ y| ≤ ε / (C + 1) := by
    intro y hy
    let Y : intervalDomainPoint := ⟨y, hy⟩
    have htime :=
      hδ t htD (by simpa [sub_zero] using htdist) Y
    have htime' :
        |D.u t Y - u₀ Y| < ε / (C + 1) := by
      simpa [patchedSlice_of_pos u₀ D.u htpos,
        patchedSlice_of_nonpos u₀ D.u (le_refl (0 : ℝ))] using htime
    exact le_of_lt (by simpa [intervalDomainLift, Y, hy] using htime')
  have hbound :=
    ShenWork.IntervalResolverWeakBounds.resolverValue_diff_sup_le_of_bounded
      p hγ hUc₁ hUc₂ hmem₁ hu₀_mem hD x
  have hrewrite :
      Real.sqrt (∑' k : ℕ, (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2) *
          (2 * (p.ν * (p.γ * M ^ (p.γ - 1)) * (ε / (C + 1)))) =
        C * (ε / (C + 1)) := by
    dsimp [C]
    ring
  rw [patchedChemical_of_pos p u₀ D.u htpos, patchedChemical_zero,
    mildChemicalConcentration]
  refine lt_of_le_of_lt (by simpa [hrewrite] using hbound) ?_
  have hlt : C * (ε / (C + 1)) < ε := by
    field_simp [hCden_pos.ne']
    nlinarith [hε, hC_nonneg]
  exact hlt

/-- Under a common nonnegative `M`-ball for the patched u-slices, the patched
chemical concentration has the value zero-face continuity required by the split
zero-start trace record. -/
theorem patchedChemical_lift_zeroFace_of_timeContinuousAt_zero
    {p : CM2Params} (hγ : 1 ≤ p.γ) {u₀ : intervalDomainPoint → ℝ}
    (hu₀cont : Continuous u₀) (D : GradientMildSolutionData p u₀)
    {M : ℝ} (hM : 0 < M)
    (hu₀_mem : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift u₀ x ∈ Set.Icc (0 : ℝ) M)
    (hpatch_mem : ∀ t ∈ Set.Icc (0 : ℝ) D.T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (patchedSlice u₀ D.u t) x ∈ Set.Icc (0 : ℝ) M) :
    ∀ {b : ℝ}, 0 ≤ b → b ≤ D.T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ContinuousWithinAt
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) =>
            intervalDomainLift (patchedChemical p u₀ D.u t) x))
        (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1) (0, x) := by
  intro b _hb0 hbT x hx
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨δt, hδt_pos, hδt⟩ :=
    patchedChemical_timeContinuousAt_zero_of_patchedSlice_ball
      hγ hu₀cont D hM hu₀_mem hpatch_mem (ε / 2) hε2
  have hspatial_on :
      ContinuousOn
        (intervalDomainLift (patchedChemical p u₀ D.u 0))
        (Set.Icc (0 : ℝ) 1) := by
    rw [patchedChemical_zero]
    exact intervalNeumannResolverR_lift_continuousOn p hu₀cont
  have hspatial_cont :
      ContinuousWithinAt
        (intervalDomainLift (patchedChemical p u₀ D.u 0))
        (Set.Icc (0 : ℝ) 1) x :=
    hspatial_on x hx
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
      |patchedChemical p u₀ D.u t Y - patchedChemical p u₀ D.u 0 Y| < ε / 2 := by
    have h :=
      hδt t htD (by simpa [Real.dist_eq] using hdist_t) Y
    simpa using h
  have hspace :
      |patchedChemical p u₀ D.u 0 Y - patchedChemical p u₀ D.u 0 X| < ε / 2 := by
    have h := hδx hy (by simpa [Real.dist_eq] using hdist_x)
    simpa [Real.dist_eq, intervalDomainLift, Y, X, hy, hx] using h
  have hval_ty :
      Function.uncurry
          (fun (t : ℝ) (x : ℝ) =>
            intervalDomainLift (patchedChemical p u₀ D.u t) x) (t, y) =
        patchedChemical p u₀ D.u t Y := by
    simp [Function.uncurry, intervalDomainLift, Y, hy]
  have hval_0x :
      Function.uncurry
          (fun (t : ℝ) (x : ℝ) =>
            intervalDomainLift (patchedChemical p u₀ D.u t) x) (0, x) =
        patchedChemical p u₀ D.u 0 X := by
    simp [Function.uncurry, intervalDomainLift, X, hx]
  rw [hval_ty, hval_0x, Real.dist_eq]
  calc
    |patchedChemical p u₀ D.u t Y - patchedChemical p u₀ D.u 0 X|
        = |(patchedChemical p u₀ D.u t Y - patchedChemical p u₀ D.u 0 Y) +
            (patchedChemical p u₀ D.u 0 Y - patchedChemical p u₀ D.u 0 X)| := by
          ring_nf
    _ ≤ |patchedChemical p u₀ D.u t Y - patchedChemical p u₀ D.u 0 Y| +
          |patchedChemical p u₀ D.u 0 Y - patchedChemical p u₀ D.u 0 X| :=
          abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add htime hspace
    _ = ε := by ring

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

/-- Uniform-in-space initial approach of the spatial derivative of the patched
Picard slice. This is the explicit analytic derivative input, not a disguised
zero-face trace field. -/
def PatchedSliceDerivUniformApproachAtZero
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∀ ε > 0, ∃ δ > 0,
    ∀ t ∈ Set.Icc (0 : ℝ) D.T, |t| < δ →
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (intervalDomainLift (patchedSlice u₀ D.u t)) x -
          deriv (intervalDomainLift u₀) x| < ε

/-- The u-derivative zero face follows from uniform derivative approach at zero
and spatial continuity of the initial derivative. This is the derivative
analogue of `patchedSlice_lift_zeroFace_of_timeContinuousAt_zero`.

The theorem is non-circular: it does not assume
`H1ZeroStartPrimitiveDerivativeZeroFaceTrace`; it only consumes the explicit
uniform derivative approach that remains an analytic frontier for the
construction. -/
theorem patchedSlice_ux_zeroFace_of_derivUniformApproachAt_zero
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (hu₀x_cont :
      ContinuousOn (fun x : ℝ => deriv (intervalDomainLift u₀) x)
        (Set.Icc (0 : ℝ) 1))
    (hdux : PatchedSliceDerivUniformApproachAtZero (p := p) (u₀ := u₀) D) :
    ∀ {b : ℝ}, 0 ≤ b → b ≤ D.T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ContinuousWithinAt
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) =>
            deriv (intervalDomainLift (patchedSlice u₀ D.u t)) x))
        (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1) (0, x) := by
  intro b _hb0 hbT x hx
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨δt, hδt_pos, hδt⟩ := hdux (ε / 2) hε2
  have hx_cont :
      ContinuousWithinAt
        (fun x : ℝ => deriv (intervalDomainLift u₀) x)
        (Set.Icc (0 : ℝ) 1) x :=
    hu₀x_cont x hx
  rw [Metric.continuousWithinAt_iff] at hx_cont
  obtain ⟨δx, hδx_pos, hδx⟩ := hx_cont (ε / 2) hε2
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
  have htime :
      |deriv (intervalDomainLift (patchedSlice u₀ D.u t)) y -
        deriv (intervalDomainLift u₀) y| < ε / 2 := by
    exact hδt t htD (by simpa [Real.dist_eq] using hdist_t) y hy
  have hspace :
      |deriv (intervalDomainLift u₀) y -
        deriv (intervalDomainLift u₀) x| < ε / 2 := by
    have h := hδx hy (by simpa [Real.dist_eq] using hdist_x)
    simpa [Real.dist_eq] using h
  have hval_ty :
      Function.uncurry
          (fun (t : ℝ) (x : ℝ) =>
            deriv (intervalDomainLift (patchedSlice u₀ D.u t)) x) (t, y) =
        deriv (intervalDomainLift (patchedSlice u₀ D.u t)) y := by
    simp [Function.uncurry]
  have hval_0x :
      Function.uncurry
          (fun (t : ℝ) (x : ℝ) =>
            deriv (intervalDomainLift (patchedSlice u₀ D.u t)) x) (0, x) =
        deriv (intervalDomainLift u₀) x := by
    simp [Function.uncurry, patchedSlice_of_nonpos u₀ D.u (le_refl (0 : ℝ))]
  rw [hval_ty, hval_0x, Real.dist_eq]
  calc
    |deriv (intervalDomainLift (patchedSlice u₀ D.u t)) y -
        deriv (intervalDomainLift u₀) x|
        = |(deriv (intervalDomainLift (patchedSlice u₀ D.u t)) y -
              deriv (intervalDomainLift u₀) y) +
            (deriv (intervalDomainLift u₀) y -
              deriv (intervalDomainLift u₀) x)| := by
          ring_nf
    _ ≤ |deriv (intervalDomainLift (patchedSlice u₀ D.u t)) y -
          deriv (intervalDomainLift u₀) y| +
        |deriv (intervalDomainLift u₀) y -
          deriv (intervalDomainLift u₀) x| :=
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
#print axioms intervalNeumannResolverR_nonneg_of_continuous_nonneg
#print axioms intervalNeumannResolverR_nonneg_of_paperPositiveInitialDatum
#print axioms patchedChemical_zero_nonneg_of_paperPositiveInitialDatum
#print axioms patchedChemical_pos_time_nonneg
#print axioms intervalNeumannResolverR_lift_continuousOn
#print axioms patchedChemical_timeContinuousAt_zero_of_patchedSlice_ball
#print axioms patchedChemical_lift_zeroFace_of_timeContinuousAt_zero
#print axioms patchedSlice_ux_zeroFace_of_derivUniformApproachAt_zero

end AxiomAudit

end ShenWork.Paper2.IntervalChiNegH1ZeroStartComponents
