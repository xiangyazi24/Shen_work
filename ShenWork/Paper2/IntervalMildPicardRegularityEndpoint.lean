import ShenWork.Paper2.IntervalMildPicardRegularity
import ShenWork.PDE.HasDerivWithinAtIntegral

open MeasureTheory Filter Topology Set
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)

noncomputable section

namespace ShenWork.IntervalMildPicardRegularityEndpoint

private lemma integrable_of_mem_var
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set ℝ}
    (hs : Convex ℝ s) {F F' : α → ℝ → ℝ} {a₀ a : ℝ}
    (ha₀ : a₀ ∈ s) (ha : a ∈ s) {bound : α → ℝ}
    (hF_meas : ∀ a ∈ s, AEStronglyMeasurable (fun x => F x a) μ)
    (hF_int : Integrable (fun x => F x a₀) μ)
    (h_bound : ∀ᵐ x ∂μ, ∀ a ∈ s, |F' x a| ≤ bound x)
    (bound_int : Integrable bound μ)
    (h_diff : ∀ᵐ x ∂μ, ∀ a ∈ s,
      HasDerivWithinAt (fun a => F x a) (F' x a) s a) :
    Integrable (fun x => F x a) μ := by
  have hdiff_bound :
      ∀ᵐ x ∂μ, ‖F x a₀ - F x a‖ ≤ ‖a - a₀‖ * |bound x| := by
    filter_upwards [h_diff, h_bound] with x hx_diff hx_bound
    have hmvt : ‖F x a - F x a₀‖ ≤ |bound x| * ‖a - a₀‖ := by
      refine hs.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := fun b => F x b) (f' := fun b => F' x b) (C := |bound x|)
        hx_diff (fun b hb => ?_) ha₀ ha
      have hle : |F' x b| ≤ |bound x| := (hx_bound b hb).trans (le_abs_self _)
      simpa [Real.norm_eq_abs] using hle
    simpa [norm_sub_rev, mul_comm] using hmvt
  exact integrable_of_norm_sub_le (hF_meas a ha) hF_int
    (bound_int.norm.const_mul ‖a - a₀‖) hdiff_bound

/-- Variant of W7b with a parameter-dependent derivative field. -/
theorem hasDerivWithinAt_integral_of_dominated_loc_var
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set ℝ}
    (hs : Convex ℝ s) {F F' : α → ℝ → ℝ} {a₀ : ℝ} (ha₀ : a₀ ∈ s)
    {bound : α → ℝ}
    (hF_meas : ∀ a ∈ s, AEStronglyMeasurable (fun x => F x a) μ)
    (hF_int : Integrable (fun x => F x a₀) μ)
    (hF'_meas : AEStronglyMeasurable (fun x => F' x a₀) μ)
    (h_bound : ∀ᵐ x ∂μ, ∀ a ∈ s, |F' x a| ≤ bound x)
    (bound_int : Integrable bound μ)
    (h_diff : ∀ᵐ x ∂μ, ∀ a ∈ s,
      HasDerivWithinAt (fun a => F x a) (F' x a) s a) :
    HasDerivWithinAt (fun a => ∫ x, F x a ∂μ)
      (∫ x, F' x a₀ ∂μ) s a₀ := by
  have hF'_int : Integrable (fun x => F' x a₀) μ := by
    refine bound_int.mono' hF'_meas ?_
    exact h_bound.mono fun x hx => by
      simpa [Real.norm_eq_abs] using hx a₀ ha₀
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have h_integral_slope :
      (fun a => slope (fun b => ∫ x, F x b ∂μ) a₀ a)
        =ᶠ[𝓝[s \ {a₀}] a₀]
      fun a => ∫ x, slope (fun b => F x b) a₀ a ∂μ := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    have ha_s : a ∈ s := ha.1
    have hFa : Integrable (fun x => F x a) μ :=
      integrable_of_mem_var hs ha₀ ha_s hF_meas hF_int h_bound bound_int h_diff
    rw [slope_def_module]
    calc
      (a - a₀)⁻¹ • (∫ x, F x a ∂μ - ∫ x, F x a₀ ∂μ)
          = (a - a₀)⁻¹ • ∫ x, F x a - F x a₀ ∂μ := by
            rw [integral_sub hFa hF_int]
      _ = ∫ x, (a - a₀)⁻¹ • (F x a - F x a₀) ∂μ := by
            rw [integral_smul]
      _ = ∫ x, slope (fun b => F x b) a₀ a ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards with x
            rw [slope_def_module]
  refine Tendsto.congr' h_integral_slope.symm ?_
  apply tendsto_integral_filter_of_dominated_convergence (bound := fun x => |bound x|)
  · filter_upwards [self_mem_nhdsWithin] with a ha
    simpa [slope_def_module] using
      (((hF_meas a ha.1).sub (hF_meas a₀ ha₀)).const_smul ((a - a₀)⁻¹ : ℝ))
  · filter_upwards [self_mem_nhdsWithin] with a ha
    have ha_s : a ∈ s := ha.1
    have ha_ne : a ≠ a₀ := by simpa using ha.2
    filter_upwards [h_diff, h_bound] with x hx_diff hx_bound
    have hmvt : ‖F x a - F x a₀‖ ≤ |bound x| * ‖a - a₀‖ := by
      refine hs.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := fun b => F x b) (f' := fun b => F' x b) (C := |bound x|)
        hx_diff (fun b hb => ?_) ha₀ ha_s
      have hle : |F' x b| ≤ |bound x| := (hx_bound b hb).trans (le_abs_self _)
      simpa [Real.norm_eq_abs] using hle
    have hapos : 0 < |a - a₀| := abs_pos.mpr (sub_ne_zero.mpr ha_ne)
    rw [slope_def_module, norm_smul, Real.norm_eq_abs, abs_inv,
      inv_mul_le_iff₀ hapos]
    simpa [Real.norm_eq_abs, mul_comm] using hmvt
  · exact bound_int.norm
  · exact h_diff.mono fun x hx => hasDerivWithinAt_iff_tendsto_slope.mp
      (hx a₀ ha₀)

/-- One-sided closed-window time-Leibniz rule for cosine coefficients.

This is the endpoint analogue of
`IntervalMildPicardRegularity.cosineCoeffs_hasDerivAt_of_smooth_param`.
The parameter derivative is taken within the closed time window `Icc lo hi`. -/
theorem cosineCoeffs_hasDerivWithinAt_of_smooth_param
    {f f' : ℝ → ℝ → ℝ} {lo hi τ : ℝ} {n : ℕ} (_hlohi : lo ≤ hi)
    (hτ : τ ∈ Set.Icc lo hi)
    (hf_cont : ∀ s ∈ Set.Icc lo hi,
      ContinuousOn (f s) (Set.Icc (0 : ℝ) 1))
    (h_diff : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ∀ s ∈ Set.Icc lo hi,
        HasDerivWithinAt (fun r => f r x) (f' s x) (Set.Icc lo hi) s)
    (h_cont_deriv : ContinuousOn (Function.uncurry f')
      (Set.Icc lo hi ×ˢ Set.Icc (0 : ℝ) 1)) :
    HasDerivWithinAt (fun s => cosineCoeffs (f s) n)
      (cosineCoeffs (f' τ) n) (Set.Icc lo hi) τ := by
  classical
  set S : Set ℝ := Set.Icc lo hi with hS
  set μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1) with hμ
  set g : ℝ → ℝ → ℝ := fun s x =>
    Real.cos ((n : ℝ) * Real.pi * x) * f s x with hg
  set g' : ℝ → ℝ → ℝ := fun s x =>
    Real.cos ((n : ℝ) * Real.pi * x) * f' s x with hg'
  have hSconv : Convex ℝ S := by
    rw [hS]
    exact convex_Icc lo hi
  have hcos_cont : Continuous (fun x : ℝ => Real.cos ((n : ℝ) * Real.pi * x)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id')
  have hg'_cont : ContinuousOn (Function.uncurry g') (S ×ˢ Set.Icc (0 : ℝ) 1) := by
    rw [hS]
    change ContinuousOn
      (fun p : ℝ × ℝ => Real.cos ((n : ℝ) * Real.pi * p.2) * f' p.1 p.2) _
    exact ContinuousOn.mul (hcos_cont.comp continuous_snd).continuousOn h_cont_deriv
  have hcompact : IsCompact (S ×ˢ Set.Icc (0 : ℝ) 1) := by
    rw [hS]
    exact isCompact_Icc.prod isCompact_Icc
  obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuousOn hg'_cont
  set bound : ℝ → ℝ := fun _ => M with hbound_def
  have hF_meas : ∀ a ∈ S, AEStronglyMeasurable (fun x => g a x) μ := by
    intro a ha
    rw [hμ]
    have hcont : ContinuousOn (g a) (Set.Icc (0 : ℝ) 1) := by
      rw [hg]
      exact hcos_cont.continuousOn.mul (hf_cont a (by simpa [hS] using ha))
    exact (hcont.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hF_int : Integrable (fun x => g τ x) μ := by
    rw [hμ]
    have hcont : ContinuousOn (g τ) (Set.Icc (0 : ℝ) 1) := by
      rw [hg]
      exact hcos_cont.continuousOn.mul (hf_cont τ (by simpa [hS] using hτ))
    have hcont' : ContinuousOn (g τ) (Set.uIcc (0 : ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact hcont
    have hi : IntervalIntegrable (g τ) volume (0 : ℝ) 1 :=
      hcont'.intervalIntegrable
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le
      (show (0 : ℝ) ≤ 1 by norm_num)).mp hi).integrable
  have hF'_meas : AEStronglyMeasurable (fun x => g' τ x) μ := by
    rw [hμ]
    have hf'τ_cont : ContinuousOn (f' τ) (Set.Icc (0 : ℝ) 1) :=
      h_cont_deriv.comp (continuousOn_const.prodMk continuousOn_id)
        (fun x hx => Set.mk_mem_prod hτ hx)
    have hcont : ContinuousOn (g' τ) (Set.Icc (0 : ℝ) 1) := by
      rw [hg']
      exact hcos_cont.continuousOn.mul hf'τ_cont
    exact (hcont.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have h_bound : ∀ᵐ x ∂μ, ∀ a ∈ S, |g' a x| ≤ bound x := by
    rw [hμ]
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    refine Filter.Eventually.of_forall (fun x hx a ha => ?_)
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ioc_subset_Icc_self hx
    have hle : ‖Function.uncurry g' (a, x)‖ ≤ M :=
      hM (a, x) (Set.mk_mem_prod ha hxIcc)
    simpa [Real.norm_eq_abs, bound, hbound_def, Function.uncurry] using hle
  have hbound_int : Integrable bound μ := by
    rw [hμ, hbound_def]
    exact integrable_const M
  have h_diff_g : ∀ᵐ x ∂μ, ∀ a ∈ S,
      HasDerivWithinAt (fun a => g a x) (g' a x) S a := by
    rw [hμ]
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    refine Filter.Eventually.of_forall (fun x hx a ha => ?_)
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ioc_subset_Icc_self hx
    have hconst : HasDerivWithinAt
        (fun _ : ℝ => Real.cos ((n : ℝ) * Real.pi * x)) 0 S a :=
      (hasDerivAt_const a _).hasDerivWithinAt
    have hf := h_diff x hxIcc a (by simpa [hS] using ha)
    rw [hg, hg']
    convert hconst.mul hf using 1
    ring
  have hraw : HasDerivWithinAt
      (fun a => ∫ x, g a x ∂μ) (∫ x, g' τ x ∂μ) S τ :=
    hasDerivWithinAt_integral_of_dominated_loc_var hSconv (by simpa [hS] using hτ)
      hF_meas hF_int hF'_meas h_bound hbound_int h_diff_g
  have hinterval : HasDerivWithinAt
      (fun a => ∫ x in (0 : ℝ)..1, g a x)
      (∫ x in (0 : ℝ)..1, g' τ x) S τ := by
    simpa [hμ, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      using hraw
  have hfactor : ∀ s, cosineCoeffs (f s) n =
      (if n = 0 then 1 else 2) *
        ∫ x in (0 : ℝ)..1, g s x := by
    intro s
    rw [ShenWork.IntervalMildPicardRegularity.cosineCoeffs_eq_factor_mul_integral]
  have hfactor' : cosineCoeffs (f' τ) n =
      (if n = 0 then 1 else 2) *
        ∫ x in (0 : ℝ)..1, g' τ x := by
    rw [ShenWork.IntervalMildPicardRegularity.cosineCoeffs_eq_factor_mul_integral]
  have hmul := hinterval.const_mul (if n = 0 then 1 else 2)
  rw [← hfactor'] at hmul
  exact hmul.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun s => hfactor s)) (hfactor τ)

end ShenWork.IntervalMildPicardRegularityEndpoint
