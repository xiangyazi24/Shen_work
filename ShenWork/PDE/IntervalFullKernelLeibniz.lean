/-
  ShenWork/PDE/IntervalFullKernelLeibniz.lean

  **T2 — full-kernel source-integral differentiation (Leibniz machinery).**

  Full-Neumann-kernel mirrors of `intervalCoupledDuhamel_grad_integral_hasDerivAt`
  and `intervalCoupledDuhamel_grad_leibniz`: differentiation under the time-integral
  sign for the source term, built on the per-slice spatial `HasDerivAt`
  `intervalFullSemigroupOperator_hasDerivAt_fst` (6.6), the per-slice gradient bound
  `intervalFullCoupledDuhamel_grad_integrand_pointwise_bound` (T2-a), and the
  `L∞` contraction `intervalFullSemigroupOperator_Linfty_bound` (T2-h).  Joint
  measurability in `s` of the integrand and its parameter-derivative are taken as
  hypotheses (as in the zeroth-reflection version).

  These discharge `hSplit`/`hLeibniz`/`hGrad_int` for `_cleaner_full`.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.PDE.IntervalFullKernelGradEstimate
import ShenWork.PDE.IntervalFullKernelSupBound

open MeasureTheory
open scoped Topology

namespace ShenWork.IntervalNeumannFullKernel

open ShenWork.IntervalDomain

/-- **Full-kernel source-integral `HasDerivAt`.**  Mirror of
`intervalCoupledDuhamel_grad_integral_hasDerivAt`. -/
theorem intervalFullCoupledDuhamel_grad_integral_hasDerivAt
    {t : ℝ} (ht : 0 < t)
    {F : ℝ → ℝ → ℝ}
    (hF_int : ∀ s, MeasureTheory.Integrable (F s) (intervalMeasure 1))
    {C_source : ℝ} (hC_source_nn : 0 ≤ C_source)
    (hF_sup : ∀ s, ∀ y : ℝ, |F s y| ≤ C_source)
    (x₀ : ℝ)
    (hF_meas :
      ∀ x : ℝ,
        MeasureTheory.AEStronglyMeasurable
          (fun s : ℝ => intervalFullSemigroupOperator (t - s) (F s) x)
          (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)))
    (hF'_meas :
      MeasureTheory.AEStronglyMeasurable
        (fun s : ℝ =>
          deriv (fun z : ℝ =>
            intervalFullSemigroupOperator (t - s) (F s) z) x₀)
        (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)))
    (hDom_int :
      IntervalIntegrable
        (fun s : ℝ =>
          ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
            * C_source * (t - s) ^ (-(1/2 : ℝ)))
        MeasureTheory.volume (0 : ℝ) t) :
    HasDerivAt
      (fun x : ℝ =>
        ∫ s in (0 : ℝ)..t,
          intervalFullSemigroupOperator (t - s) (F s) x)
      (∫ s in (0 : ℝ)..t,
        deriv (fun z : ℝ =>
          intervalFullSemigroupOperator (t - s) (F s) z) x₀)
      x₀ := by
  set Cgrad :=
    ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant with hCgrad_def
  set F_p : ℝ → ℝ → ℝ :=
    fun x s => intervalFullSemigroupOperator (t - s) (F s) x with hF_p_def
  set F'_p : ℝ → ℝ → ℝ :=
    fun x s => deriv (fun z : ℝ =>
      intervalFullSemigroupOperator (t - s) (F s) z) x with hF'_p_def
  set bound : ℝ → ℝ :=
    fun s => Cgrad * C_source * (t - s) ^ (-(1/2 : ℝ)) with hbound_def
  have huIoc_eq : Set.uIoc (0 : ℝ) t = Set.Ioc (0 : ℝ) t := Set.uIoc_of_le ht.le
  have hae_ne_t : ∀ᵐ s ∂MeasureTheory.volume, s ≠ t := by
    have heq : {s : ℝ | ¬ s ≠ t} = {t} := by ext s; simp [eq_comm]
    rw [MeasureTheory.ae_iff, heq]; exact Real.volume_singleton
  have hDiff_pt : ∀ᵐ s ∂MeasureTheory.volume, s ∈ Set.uIoc (0 : ℝ) t →
      ∀ x ∈ (Set.univ : Set ℝ), HasDerivAt (fun x => F_p x s) (F'_p x s) x := by
    filter_upwards [hae_ne_t] with s hsne hs x _
    rw [huIoc_eq] at hs
    have htms_pos : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hsne)
    have h := intervalFullSemigroupOperator_hasDerivAt_fst (t := t - s) htms_pos
      (f := F s) (hF_int s).aestronglyMeasurable (Cf := C_source) (hF_sup s) x
    simp only [F_p, F'_p]
    rw [h.deriv]
    exact h
  have hBound_pt : ∀ᵐ s ∂MeasureTheory.volume, s ∈ Set.uIoc (0 : ℝ) t →
      ∀ x ∈ (Set.univ : Set ℝ), ‖F'_p x s‖ ≤ bound s := by
    filter_upwards [hae_ne_t] with s hsne hs x _
    rw [huIoc_eq] at hs
    have h := intervalFullCoupledDuhamel_grad_integrand_pointwise_bound
      (t := t) (s := s) hs.1.le (lt_of_le_of_ne hs.2 hsne) (F := F s) (hF_int s)
      (C_source := C_source) hC_source_nn (hF_sup s) x
    simp only [F'_p, bound, Real.norm_eq_abs]
    calc |deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) (F s) z) x|
        ≤ Cgrad * (t - s) ^ (-(1/2 : ℝ)) * C_source := h
      _ = Cgrad * C_source * (t - s) ^ (-(1/2 : ℝ)) := by ring
  have hF_p_sup_ae :
      (fun s => ‖F_p x₀ s‖) ≤ᵐ[MeasureTheory.volume.restrict (Set.uIoc 0 t)]
        (fun _ => C_source) := by
    refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr ?_
    filter_upwards [hae_ne_t] with s hsne hs
    rw [huIoc_eq] at hs
    have htms_pos : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hsne)
    have h := intervalFullSemigroupOperator_Linfty_bound (t := t - s) htms_pos
      (M := C_source) hC_source_nn (hF_sup s) x₀
    simpa [F_p, Real.norm_eq_abs] using h
  have hconst_int : IntervalIntegrable (fun _ : ℝ => C_source)
      MeasureTheory.volume (0 : ℝ) t := intervalIntegrable_const
  have hF_p_int : IntervalIntegrable (F_p x₀) MeasureTheory.volume (0 : ℝ) t :=
    IntervalIntegrable.mono_fun' (f := F_p x₀) (g := fun _ => C_source)
      hconst_int (hF_meas x₀) hF_p_sup_ae
  have hF_meas_evt :
      ∀ᶠ x in 𝓝 x₀,
        MeasureTheory.AEStronglyMeasurable (F_p x)
          (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)) :=
    Filter.Eventually.of_forall (fun x => hF_meas x)
  have hresult :=
    intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := t)
      (F := F_p) (F' := F'_p) (x₀ := x₀)
      (s := (Set.univ : Set ℝ))
      (bound := bound)
      (hs := Filter.univ_mem)
      (hF_meas := hF_meas_evt)
      (hF_int := hF_p_int)
      (hF'_meas := hF'_meas)
      (h_bound := hBound_pt)
      (bound_integrable := hDom_int)
      (h_diff := hDiff_pt)
  exact hresult.2

/-- **Full-kernel Leibniz interchange** (`deriv` form of the previous). -/
theorem intervalFullCoupledDuhamel_grad_leibniz
    {t : ℝ} (ht : 0 < t)
    {F : ℝ → ℝ → ℝ}
    (hF_int : ∀ s, MeasureTheory.Integrable (F s) (intervalMeasure 1))
    {C_source : ℝ} (hC_source_nn : 0 ≤ C_source)
    (hF_sup : ∀ s, ∀ y : ℝ, |F s y| ≤ C_source)
    (x₀ : ℝ)
    (hF_meas :
      ∀ x : ℝ,
        MeasureTheory.AEStronglyMeasurable
          (fun s : ℝ => intervalFullSemigroupOperator (t - s) (F s) x)
          (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)))
    (hF'_meas :
      MeasureTheory.AEStronglyMeasurable
        (fun s : ℝ =>
          deriv (fun z : ℝ =>
            intervalFullSemigroupOperator (t - s) (F s) z) x₀)
        (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)))
    (hDom_int :
      IntervalIntegrable
        (fun s : ℝ =>
          ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
            * C_source * (t - s) ^ (-(1/2 : ℝ)))
        MeasureTheory.volume (0 : ℝ) t) :
    deriv (fun x : ℝ =>
        ∫ s in (0 : ℝ)..t,
          intervalFullSemigroupOperator (t - s) (F s) x) x₀ =
      ∫ s in (0 : ℝ)..t,
        deriv (fun z : ℝ =>
          intervalFullSemigroupOperator (t - s) (F s) z) x₀ :=
  (intervalFullCoupledDuhamel_grad_integral_hasDerivAt ht hF_int hC_source_nn hF_sup
    x₀ hF_meas hF'_meas hDom_int).deriv

/-- **Full-kernel gradient integrand is interval-integrable in `s`** (the
`hGrad_int` ingredient): the deriv integrand is dominated by the envelope
`Cgrad·C·(t−s)^(−1/2)` (T2-a) and so interval-integrable. -/
theorem intervalFullCoupledDuhamel_grad_integrand_intervalIntegrable
    {t : ℝ} (ht : 0 < t)
    {F : ℝ → ℝ → ℝ}
    (hF_int : ∀ s, MeasureTheory.Integrable (F s) (intervalMeasure 1))
    {C_source : ℝ} (hC_source_nn : 0 ≤ C_source)
    (hF_sup : ∀ s, ∀ y : ℝ, |F s y| ≤ C_source)
    (x₀ : ℝ)
    (hF'_meas :
      MeasureTheory.AEStronglyMeasurable
        (fun s : ℝ =>
          deriv (fun z : ℝ =>
            intervalFullSemigroupOperator (t - s) (F s) z) x₀)
        (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)))
    (hDom_int :
      IntervalIntegrable
        (fun s : ℝ =>
          ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
            * C_source * (t - s) ^ (-(1/2 : ℝ)))
        MeasureTheory.volume (0 : ℝ) t) :
    IntervalIntegrable
      (fun s : ℝ =>
        deriv (fun z : ℝ =>
          intervalFullSemigroupOperator (t - s) (F s) z) x₀)
      MeasureTheory.volume (0 : ℝ) t := by
  have huIoc_eq : Set.uIoc (0 : ℝ) t = Set.Ioc (0 : ℝ) t := Set.uIoc_of_le ht.le
  have hae_ne_t : ∀ᵐ s ∂MeasureTheory.volume, s ≠ t := by
    have heq : {s : ℝ | ¬ s ≠ t} = {t} := by ext s; simp [eq_comm]
    rw [MeasureTheory.ae_iff, heq]; exact Real.volume_singleton
  refine IntervalIntegrable.mono_fun'
    (g := fun s : ℝ => ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
      * C_source * (t - s) ^ (-(1/2 : ℝ)))
    hDom_int hF'_meas ?_
  refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr ?_
  filter_upwards [hae_ne_t] with s hsne hs
  rw [huIoc_eq] at hs
  have h := intervalFullCoupledDuhamel_grad_integrand_pointwise_bound
    (t := t) (s := s) hs.1.le (lt_of_le_of_ne hs.2 hsne) (F := F s) (hF_int s)
    (C_source := C_source) hC_source_nn (hF_sup s) x₀
  rw [Real.norm_eq_abs]
  calc |deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) (F s) z) x₀|
      ≤ ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
          * (t - s) ^ (-(1/2 : ℝ)) * C_source := h
    _ = ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
          * C_source * (t - s) ^ (-(1/2 : ℝ)) := by ring

end ShenWork.IntervalNeumannFullKernel
