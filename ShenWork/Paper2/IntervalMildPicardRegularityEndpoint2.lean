import ShenWork.Paper2.IntervalMildPicardRegularityEndpoint

open MeasureTheory Filter Topology Set
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalMildPicardRegularityEndpoint

noncomputable section

namespace ShenWork.IntervalMildPicardRegularityEndpoint2

/-- One-sided closed-window time-Leibniz rule for cosine coefficients.

This is the endpoint analogue of
`IntervalMildPicardRegularity.cosineCoeffs_hasDerivAt_of_smooth_param`, with
the parameter derivative taken within the closed time window `Icc a' W`. -/
theorem cosineCoeffs_hasDerivWithinAt_of_smooth_param
    {f f' : ℝ → ℝ → ℝ} {a' W : ℝ} {n : ℕ} (ha'W : a' ≤ W)
    {σ : ℝ} (hσ : σ ∈ Set.Icc a' W)
    (hf_cont : ∀ s ∈ Set.Icc a' W,
      ContinuousOn (f s) (Set.Icc (0 : ℝ) 1))
    (h_diff : ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ s ∈ Set.Icc a' W,
      HasDerivWithinAt (fun r => f r x) (f' s x) (Set.Icc a' W) s)
    (h_cont_deriv : ContinuousOn (Function.uncurry f')
      (Set.Icc a' W ×ˢ Set.Icc (0 : ℝ) 1)) :
    HasDerivWithinAt (fun s => cosineCoeffs (f s) n)
      (cosineCoeffs (f' σ) n) (Set.Icc a' W) σ := by
  classical
  set S : Set ℝ := Set.Icc a' W with hS
  set μ : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) 1) with hμ
  have hS_nonempty : S.Nonempty := by
    rw [hS]
    exact ⟨a', le_rfl, ha'W⟩
  set g : ℝ → ℝ → ℝ := fun s x =>
    Real.cos ((n : ℝ) * Real.pi * x) * f s x with hg
  set g' : ℝ → ℝ → ℝ := fun s x =>
    Real.cos ((n : ℝ) * Real.pi * x) * f' s x with hg'
  have hSconv : Convex ℝ S := by
    rw [hS]
    exact convex_Icc a' W
  have hcos_cont : Continuous (fun x : ℝ =>
      Real.cos ((n : ℝ) * Real.pi * x)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id')
  have hg'_cont : ContinuousOn (Function.uncurry g')
      (S ×ˢ Set.Icc (0 : ℝ) 1) := by
    rw [hS]
    change ContinuousOn
      (fun p : ℝ × ℝ =>
        Real.cos ((n : ℝ) * Real.pi * p.2) * f' p.1 p.2) _
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
    exact (hcont.mono Set.Ioo_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioo
  have hF_int : Integrable (fun x => g σ x) μ := by
    rw [hμ]
    have hcont : ContinuousOn (g σ) (Set.Icc (0 : ℝ) 1) := by
      rw [hg]
      exact hcos_cont.continuousOn.mul (hf_cont σ (by simpa [hS] using hσ))
    have hcont' : ContinuousOn (g σ) (Set.uIcc (0 : ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact hcont
    have hi : IntervalIntegrable (g σ) volume (0 : ℝ) 1 :=
      hcont'.intervalIntegrable
    have hIoc : Integrable (fun x => g σ x)
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le
        (show (0 : ℝ) ≤ 1 by norm_num)).mp hi).integrable
    exact hIoc.mono_measure
      (Measure.restrict_mono Set.Ioo_subset_Ioc_self le_rfl)
  have hF'_meas : AEStronglyMeasurable (fun x => g' σ x) μ := by
    rw [hμ]
    have hf'σ_cont : ContinuousOn (f' σ) (Set.Icc (0 : ℝ) 1) :=
      h_cont_deriv.comp (continuousOn_const.prodMk continuousOn_id)
        (fun x hx => Set.mk_mem_prod hσ hx)
    have hcont : ContinuousOn (g' σ) (Set.Icc (0 : ℝ) 1) := by
      rw [hg']
      exact hcos_cont.continuousOn.mul hf'σ_cont
    exact (hcont.mono Set.Ioo_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioo
  have h_bound : ∀ᵐ x ∂μ, ∀ a ∈ S, |g' a x| ≤ bound x := by
    rw [hμ]
    refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
    refine Filter.Eventually.of_forall (fun x hx a ha => ?_)
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hx
    have hle : ‖Function.uncurry g' (a, x)‖ ≤ M :=
      hM (a, x) (Set.mk_mem_prod ha hxIcc)
    simpa [Real.norm_eq_abs, bound, hbound_def, Function.uncurry] using hle
  have hbound_int : Integrable bound μ := by
    rw [hμ, hbound_def]
    exact integrable_const M
  have h_diff_g : ∀ᵐ x ∂μ, ∀ a ∈ S,
      HasDerivWithinAt (fun a => g a x) (g' a x) S a := by
    rw [hμ]
    refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
    refine Filter.Eventually.of_forall (fun x hx a ha => ?_)
    have hconst : HasDerivWithinAt
        (fun _ : ℝ => Real.cos ((n : ℝ) * Real.pi * x)) 0 S a :=
      (hasDerivAt_const a _).hasDerivWithinAt
    have hf := h_diff x hx a (by simpa [hS] using ha)
    rw [hg, hg']
    convert hconst.mul hf using 1
    ring
  have hraw : HasDerivWithinAt
      (fun a => ∫ x, g a x ∂μ) (∫ x, g' σ x ∂μ) S σ :=
    hasDerivWithinAt_integral_of_dominated_loc_var hSconv
      (by simpa [hS] using hσ) hF_meas hF_int hF'_meas h_bound
      hbound_int h_diff_g
  have hinterval : HasDerivWithinAt
      (fun a => ∫ x in (0 : ℝ)..1, g a x)
      (∫ x in (0 : ℝ)..1, g' σ x) S σ := by
    have hsrc : (fun a => ∫ x in (0 : ℝ)..1, g a x) =
        fun a => ∫ x, g a x ∂μ := by
      funext a
      rw [hμ, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        integral_Ioc_eq_integral_Ioo]
    have htgt : (∫ x in (0 : ℝ)..1, g' σ x) =
        ∫ x, g' σ x ∂μ := by
      rw [hμ, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        integral_Ioc_eq_integral_Ioo]
    simpa [hsrc, htgt] using hraw
  have hfactor : ∀ s, cosineCoeffs (f s) n =
      (if n = 0 then 1 else 2) *
        ∫ x in (0 : ℝ)..1, g s x := by
    intro s
    rw [ShenWork.IntervalMildPicardRegularity.cosineCoeffs_eq_factor_mul_integral]
  have hfactor' : cosineCoeffs (f' σ) n =
      (if n = 0 then 1 else 2) *
        ∫ x in (0 : ℝ)..1, g' σ x := by
    rw [ShenWork.IntervalMildPicardRegularity.cosineCoeffs_eq_factor_mul_integral]
  have hmul := hinterval.const_mul (if n = 0 then 1 else 2)
  rw [← hfactor'] at hmul
  exact hmul.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun s => hfactor s)) (hfactor σ)

#print axioms cosineCoeffs_hasDerivWithinAt_of_smooth_param

end ShenWork.IntervalMildPicardRegularityEndpoint2
