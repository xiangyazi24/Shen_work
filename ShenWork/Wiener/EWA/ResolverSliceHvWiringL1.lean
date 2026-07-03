/-
  ShenWork/Wiener/EWA/ResolverSliceHvWiringL1.lean

  L1ContOn retype of `ResolverSliceHvWiring.lean` + `ResolverSliceG12Wiring.lean`.

  Produces `HasResolverDirectSpectralData` from `DuhamelSourceL1ContOn`
  (not `DuhamelSourceTimeC1`), with `bc/hbsum/hagree` and `G1/G2` fully
  discharged.

  Chain:
  * `realSlice_window_uniform_C0_of_L1ContOn`
    — C⁰ window bounds from L1ContOn joint continuity
  * `realSlice_window_uniform_G12_of_L1ContOn`
    — G1/G2 window bounds from L1ContOn spatial derivative joint continuity
  * `realSlice_Hv_of_L1ContOn`
    — Hv from L1ContOn with `C/hC/hdecay/ha0` discharged (G1/G2 carried)
  * `realSlice_Hv_full_of_L1ContOn`
    — Hv with ALL residuals discharged, `bc/hbsum/hagree` trivially set
      to `fullSourceCoeff/hsumE/hrealizes`

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.ResolverSliceWindowBounds
import ShenWork.Wiener.EWA.ResolverSourceWindowUniformDecay
import ShenWork.Wiener.EWA.SourcePerSliceCloseL1
import ShenWork.Wiener.EWA.SourceSpatialJointRegularityL1

noncomputable section

namespace ShenWork.EWA

open Set Topology Filter
open ShenWork.GWA ShenWork.Wiener
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalMildToClassical (mildChemicalConcentration)
open ShenWork.IntervalResolverDirectTimeRegularity (HasResolverDirectSpectralData)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledLogisticSourceCoeffs)
open ShenWork.IntervalPicardLimitRestartWeak (DuhamelSourceL1ContOn)

variable {T : ℝ}

private theorem clampWindow_subset_Ioo {t₀ : ℝ} (ht₀ : 0 < t₀) (ht₀T : t₀ < T) :
    Icc (t₀ / 4) ((t₀ + 3 * T) / 4) ⊆ Ioo (0 : ℝ) T := by
  intro y hy
  exact ⟨lt_of_lt_of_le (by linarith) hy.1, lt_of_le_of_lt hy.2 (by linarith)⟩

open ShenWork.IntervalCosineSliceRegularity
  (intervalDomainLift_deriv_left_endpoint_zero_of_ne
   intervalDomainLift_deriv_right_endpoint_zero_of_ne)

private theorem lift_ne_zero_at_zero
    {u₀E : WA 1} {δ₀ ρ : ℝ} (hδρ : 0 < δ₀ - ρ)
    (hheat : UniformFloor (heatEWA (T := T) u₀E) δ₀)
    {u_star : EWA T 1}
    (hu_ball : u_star ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ)
    {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) T) :
    intervalDomainLift (realSlice u_star σ) 0 ≠ 0 := by
  have hmem : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  simp [intervalDomainLift, hmem]
  exact ne_of_gt (realSlice_pos hδρ hheat hu_ball hσ ⟨0, hmem⟩)

private theorem lift_ne_zero_at_one
    {u₀E : WA 1} {δ₀ ρ : ℝ} (hδρ : 0 < δ₀ - ρ)
    (hheat : UniformFloor (heatEWA (T := T) u₀E) δ₀)
    {u_star : EWA T 1}
    (hu_ball : u_star ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ)
    {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) T) :
    intervalDomainLift (realSlice u_star σ) 1 ≠ 0 := by
  have hmem : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  simp [intervalDomainLift, hmem]
  exact ne_of_gt (realSlice_pos hδρ hheat hu_ball hσ ⟨1, hmem⟩)

private theorem lift_deriv2_zero_at_zero
    {g : intervalDomainPoint → ℝ}
    (hne : intervalDomainLift g 0 ≠ 0) :
    deriv (deriv (intervalDomainLift g)) 0 = 0 := by
  set f := intervalDomainLift g with hfdef
  set h := deriv f with hhdef
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
  have h0 : h 0 = 0 := by
    rw [hhdef]
    exact intervalDomainLift_deriv_left_endpoint_zero_of_ne hne
  by_cases hd : DifferentiableAt ℝ h 0
  · have hcw : HasDerivWithinAt h 0 (Iio 0) 0 :=
      (hasDerivWithinAt_const 0 (Iio 0) (0 : ℝ)).congr hzero h0
    have hw := hd.hasDerivAt.hasDerivWithinAt.derivWithin
      (uniqueDiffWithinAt_Iio 0)
    rw [← hw]
    exact hcw.derivWithin (uniqueDiffWithinAt_Iio 0)
  · exact deriv_zero_of_not_differentiableAt hd

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
    exact intervalDomainLift_deriv_right_endpoint_zero_of_ne hne
  by_cases hd : DifferentiableAt ℝ h 1
  · have hcw : HasDerivWithinAt h 0 (Ioi 1) 1 :=
      (hasDerivWithinAt_const 1 (Ioi 1) (0 : ℝ)).congr hzero h1
    have hw := hd.hasDerivAt.hasDerivWithinAt.derivWithin
      (uniqueDiffWithinAt_Ioi 1)
    rw [← hw]
    exact hcw.derivWithin (uniqueDiffWithinAt_Ioi 1)
  · exact deriv_zero_of_not_differentiableAt hd

/-! ### C⁰ window bounds (L1ContOn retype of ResolverSliceWindowBounds) -/

theorem realSlice_window_uniform_C0_of_L1ContOn
    (p : CM2Params) (u_star : EWA T 1) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceL1ContOn
      (coupledChemDivSourceCoeffs p (realSlice u_star)) T)
    (hlog : DuhamelSourceL1ContOn
      (coupledLogisticSourceCoeffs p (realSlice u_star)) T)
    {u₀E : WA 1} {δ ρ : ℝ} (hδρ : 0 < δ - ρ)
    (hheat : UniformFloor (heatEWA (T := T) u₀E) δ)
    (hu_ball : u_star ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ)
    (hrealizes : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (realSlice u_star t) x
        = ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x) :
    ∃ m M : ℝ → ℝ, (∀ t₀, 0 < m t₀) ∧
      (∀ t₀, 0 < t₀ → t₀ < T → ∀ σ ∈ Icc (t₀ / 4) ((t₀ + 3 * T) / 4),
        ∀ x ∈ Icc (0 : ℝ) 1, m t₀ ≤ intervalDomainLift (realSlice u_star σ) x) ∧
      (∀ t₀, 0 < t₀ → t₀ < T → ∀ σ ∈ Icc (t₀ / 4) ((t₀ + 3 * T) / 4),
        ∀ x ∈ Icc (0 : ℝ) 1, intervalDomainLift (realSlice u_star σ) x ≤ M t₀) := by
  classical
  have hjc : ContinuousOn
      (Function.uncurry (fun (t : ℝ) (x : ℝ) =>
        ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x))
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) :=
    fullSourceCoeff_jointSolutionClosed_of_L1ContOn p (realSlice u_star) u₀cos hu0bd hchem hlog
  have hwin : ∀ t₀, 0 < t₀ → t₀ < T →
      ∃ mt Mt : ℝ, 0 < mt ∧
        (∀ σ ∈ Icc (t₀ / 4) ((t₀ + 3 * T) / 4),
          ∀ x ∈ Icc (0 : ℝ) 1,
            mt ≤ intervalDomainLift (realSlice u_star σ) x) ∧
        (∀ σ ∈ Icc (t₀ / 4) ((t₀ + 3 * T) / 4),
          ∀ x ∈ Icc (0 : ℝ) 1,
            intervalDomainLift (realSlice u_star σ) x ≤ Mt) := by
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
    set F : ℝ × ℝ → ℝ := Function.uncurry
      (fun t x => ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x)
    have hcF := hjc.mono hbox_sub
    obtain ⟨q_min, hq_min_mem, hq_min_min⟩ :=
      hKc.exists_isMinOn hKne hcF
    obtain ⟨q_max, hq_max_mem, hq_max_max⟩ :=
      hKc.exists_isMaxOn hKne hcF
    have hq_min_Ioo : q_min.1 ∈ Ioo (0 : ℝ) T :=
      hsub (mem_prod.1 hq_min_mem).1
    have hq_min_Icc : q_min.2 ∈ Icc (0 : ℝ) 1 :=
      (mem_prod.1 hq_min_mem).2
    have hF_min_pos : 0 < F q_min := by
      show 0 < ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos q_min.1 n *
        cosineMode n q_min.2
      rw [← hrealizes q_min.1 hq_min_Ioo q_min.2 hq_min_Icc]
      rw [intervalDomainLift, dif_pos hq_min_Icc]
      exact realSlice_pos hδρ hheat hu_ball
        ⟨hq_min_Ioo.1.le, hq_min_Ioo.2.le⟩ ⟨q_min.2, hq_min_Icc⟩
    refine ⟨F q_min, F q_max, hF_min_pos, ?_, ?_⟩
    · intro σ hσ x hx
      have hmem : (σ, x) ∈ W ×ˢ Icc (0 : ℝ) 1 :=
        mem_prod.mpr ⟨hσ, hx⟩
      have hσIoo : σ ∈ Ioo (0 : ℝ) T := hsub hσ
      rw [hrealizes σ hσIoo x hx]
      exact hq_min_min hmem
    · intro σ hσ x hx
      have hmem : (σ, x) ∈ W ×ˢ Icc (0 : ℝ) 1 :=
        mem_prod.mpr ⟨hσ, hx⟩
      have hσIoo : σ ∈ Ioo (0 : ℝ) T := hsub hσ
      rw [hrealizes σ hσIoo x hx]
      exact hq_max_max hmem
  refine ⟨fun t₀ => if h : 0 < t₀ ∧ t₀ < T then
    (hwin t₀ h.1 h.2).choose else 1,
    fun t₀ => if h : 0 < t₀ ∧ t₀ < T then
    (hwin t₀ h.1 h.2).choose_spec.choose else 1,
    ?_, ?_, ?_⟩
  · intro t₀
    dsimp only
    split_ifs with h
    · exact (hwin t₀ h.1 h.2).choose_spec.choose_spec.1
    · exact one_pos
  · intro t₀ ht₀ ht₀T σ hσ x hx
    have h : 0 < t₀ ∧ t₀ < T := ⟨ht₀, ht₀T⟩
    simp only [dif_pos h]
    exact (hwin t₀ ht₀ ht₀T).choose_spec.choose_spec.2.1 σ hσ x hx
  · intro t₀ ht₀ ht₀T σ hσ x hx
    have h : 0 < t₀ ∧ t₀ < T := ⟨ht₀, ht₀T⟩
    simp only [dif_pos h]
    exact (hwin t₀ ht₀ ht₀T).choose_spec.choose_spec.2.2 σ hσ x hx

/-! ### G1/G2 window bounds (L1ContOn retype of ResolverSliceG12Wiring) -/

theorem realSlice_window_uniform_G12_of_L1ContOn
    (p : CM2Params) (u_star : EWA T 1)
    (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceL1ContOn
      (coupledChemDivSourceCoeffs p (realSlice u_star)) T)
    (hlog : DuhamelSourceL1ContOn
      (coupledLogisticSourceCoeffs p (realSlice u_star)) T)
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
  set Fg : ℝ × ℝ → ℝ := Function.uncurry
    (fun t x => deriv (fun y => ∑' n,
      fullSourceCoeff p (realSlice u_star) u₀cos t n *
        cosineMode n y) x) with hFg
  set Fg2 : ℝ × ℝ → ℝ := Function.uncurry
    (fun t x => deriv (fun y => deriv (fun z => ∑' n,
      fullSourceCoeff p (realSlice u_star) u₀cos t n *
        cosineMode n z) y) x) with hFg2
  have hjcG : ContinuousOn Fg
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) :=
    fullSourceCoeff_jointGradClosed_of_L1ContOn p (realSlice u_star)
      u₀cos hu0bd hchem hlog hsumE
  have hjcG2 : ContinuousOn Fg2
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) :=
    fullSourceCoeff_jointGrad2Closed_of_L1ContOn p
      (realSlice u_star) u₀cos hu0bd hchem hlog hsumE
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
    have hcFg := (hjcG.mono hbox_sub).norm
    have hcFg2 := (hjcG2.mono hbox_sub).norm
    obtain ⟨q₁, hq₁mem, hq₁max⟩ :=
      hKc.exists_isMaxOn hKne hcFg
    obtain ⟨q₂, hq₂mem, hq₂max⟩ :=
      hKc.exists_isMaxOn hKne hcFg2
    have hA1nn : 0 ≤ ‖Fg q₁‖ := norm_nonneg _
    have hA2nn : 0 ≤ ‖Fg2 q₂‖ := norm_nonneg _
    refine ⟨‖Fg q₁‖, ‖Fg2 q₂‖, hA1nn, hA2nn, ?_, ?_⟩
    · intro σ hσ x hx
      by_cases hxint : x ∈ Ioo (0 : ℝ) 1
      · have hσIoo : σ ∈ Ioo (0 : ℝ) T := hsub hσ
        have hIcc_nhds : Icc (0 : ℝ) 1 ∈ 𝓝 x :=
          Icc_mem_nhds hxint.1 hxint.2
        have hee : intervalDomainLift (realSlice u_star σ) =ᶠ[𝓝 x]
            (fun y => ∑' n, fullSourceCoeff p (realSlice u_star)
              u₀cos σ n * cosineMode n y) :=
          eventually_of_mem hIcc_nhds (fun y hy => hrealizes σ hσIoo y hy)
        rw [EventuallyEq.deriv_eq hee]
        have hmem : (σ, x) ∈ W ×ˢ Icc (0 : ℝ) 1 :=
          mem_prod.mpr ⟨hσ, hx⟩
        calc |Fg (σ, x)|
            = ‖Fg (σ, x)‖ := (Real.norm_eq_abs _).symm
          _ ≤ ‖Fg q₁‖ := isMaxOn_iff.mp hq₁max (σ, x) hmem
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
        · rw [intervalDomainLift_deriv_left_endpoint_zero_of_ne
            (lift_ne_zero_at_zero hδρ hheat hu_ball hσIcc), abs_zero]
          exact hA1nn
        · rw [intervalDomainLift_deriv_right_endpoint_zero_of_ne
            (lift_ne_zero_at_one hδρ hheat hu_ball hσIcc), abs_zero]
          exact hA1nn
    · intro σ hσ x hx
      by_cases hxint : x ∈ Ioo (0 : ℝ) 1
      · have hσIoo : σ ∈ Ioo (0 : ℝ) T := hsub hσ
        have hIoo_nhds : Ioo (0 : ℝ) 1 ∈ 𝓝 x :=
          isOpen_Ioo.mem_nhds hxint
        have hee1 : ∀ y ∈ Ioo (0 : ℝ) 1,
            deriv (intervalDomainLift (realSlice u_star σ)) y =
            deriv (fun z => ∑' n, fullSourceCoeff p (realSlice u_star)
              u₀cos σ n * cosineMode n z) y := by
          intro y hy
          exact EventuallyEq.deriv_eq
            (eventually_of_mem (Icc_mem_nhds hy.1 hy.2)
              (fun z hz => hrealizes σ hσIoo z hz))
        have hee2 :
            deriv (intervalDomainLift (realSlice u_star σ)) =ᶠ[𝓝 x]
            deriv (fun z => ∑' n, fullSourceCoeff p (realSlice u_star)
              u₀cos σ n * cosineMode n z) :=
          eventually_of_mem hIoo_nhds (fun y hy => hee1 y hy)
        rw [EventuallyEq.deriv_eq hee2]
        have hmem : (σ, x) ∈ W ×ˢ Icc (0 : ℝ) 1 :=
          mem_prod.mpr ⟨hσ, hx⟩
        calc |Fg2 (σ, x)|
            = ‖Fg2 (σ, x)‖ := (Real.norm_eq_abs _).symm
          _ ≤ ‖Fg2 q₂‖ := isMaxOn_iff.mp hq₂max (σ, x) hmem
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
            (lift_ne_zero_at_zero hδρ hheat hu_ball hσIcc), abs_zero]
          exact hA2nn
        · rw [lift_deriv2_zero_at_one
            (lift_ne_zero_at_one hδρ hheat hu_ball hσIcc), abs_zero]
          exact hA2nn
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

/-! ### Full Hv from L1ContOn (G1/G2 + bc/hbsum/hagree all discharged) -/

theorem realSlice_Hv_full_of_L1ContOn
    (p : CM2Params) (u_star : EWA T 1)
    (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceL1ContOn
      (coupledChemDivSourceCoeffs p (realSlice u_star)) T)
    (hlog : DuhamelSourceL1ContOn
      (coupledLogisticSourceCoeffs p (realSlice u_star)) T)
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
    HasResolverDirectSpectralData T
      (mildChemicalConcentration p (realSlice u_star)) p := by
  -- Window cosine representation — trivially set to fullSourceCoeff.
  set bc : ℝ → ℝ → ℕ → ℝ := fun _t₀ σ n =>
    fullSourceCoeff p (realSlice u_star) u₀cos σ n
  have hbsum : ∀ t₀, 0 < t₀ → t₀ < T →
      ∀ σ ∈ Icc (t₀ / 4) ((t₀ + 3 * T) / 4),
        Summable (fun n => unitIntervalCosineEigenvalue n * |bc t₀ σ n|) := by
    intro t₀ ht₀ ht₀T σ hσ
    exact hsumE σ (clampWindow_subset_Ioo ht₀ ht₀T hσ)
  have hagree : ∀ t₀, 0 < t₀ → t₀ < T →
      ∀ σ ∈ Icc (t₀ / 4) ((t₀ + 3 * T) / 4),
        EqOn (intervalDomainLift (realSlice u_star σ))
          (fun x => ∑' n, bc t₀ σ n * cosineMode n x) (Icc (0 : ℝ) 1) := by
    intro t₀ ht₀ ht₀T σ hσ x hx
    exact hrealizes σ (clampWindow_subset_Ioo ht₀ ht₀T hσ) x hx
  -- C⁰ window bounds.
  obtain ⟨m, M, hm, hlb, hub⟩ :=
    realSlice_window_uniform_C0_of_L1ContOn p u_star u₀cos hu0bd
      hchem hlog hδρ hheat hu_ball hrealizes
  -- G1/G2 window bounds.
  obtain ⟨G1, G2, hG1, hG2⟩ :=
    realSlice_window_uniform_G12_of_L1ContOn p u_star u₀cos
      hu0bd hchem hlog hδρ hheat hu_ball hsumE hrealizes
  -- Quadratic decay from C⁰ + G1/G2.
  obtain ⟨C, hC, hdecay, ha0⟩ :=
    realSlice_powerSource_window_uniform_decay p u_star bc hbsum hagree m M hm hlb hub
      G1 G2 hG1 hG2
  -- Feed into the L1ContOn Hv producer.
  exact realSlice_Hv_closed_of_L1ContOn p u_star u₀cos hu0bd hchem hlog hδρ hheat hu_ball
    hsumE hrealizes C hC hdecay ha0

end ShenWork.EWA

#print axioms ShenWork.EWA.realSlice_window_uniform_C0_of_L1ContOn
#print axioms ShenWork.EWA.realSlice_window_uniform_G12_of_L1ContOn
#print axioms ShenWork.EWA.realSlice_Hv_full_of_L1ContOn
