/-
  One-sided time differentiability of the negative-part energy.

  This file provides the previously missing API named in
  `IntervalChiNegV5SelfContained`: differentiating
  `t ↦ ∫ (u_-(t))² d(intervalMeasure 1)` under the integral.

  The inputs are deliberately window-local.  The truncated Picard limit is cut
  off to `0` outside `(0, T]`, so no dominated data can exist on the unbounded
  set `Ici t`; instead everything is assumed on the compact window `[t, T]`,
  the dominated one-sided Leibniz rule
  `hasDerivWithinAt_integral_of_dominated_loc_var` is applied there, and the
  result is upgraded to `Ici t` (legitimate because `HasDerivWithinAt` only
  sees a neighbourhood of the base point within the set).

  The pointwise derivative of the integrand is the scalar chain rule
  `negativePart_sq_hasDerivAt` (derivative `-2 · negativePart r`) composed
  with the pointwise time derivative of the trajectory; the measurability of
  the differentiated integrand is recovered from difference quotients, so no
  separate measurability input is needed for the time derivative.
-/
import ShenWork.Paper2.IntervalBFormCron2RegularNegativePartEnergyA2
import ShenWork.Paper2.IntervalMildPicardRegularityEndpoint
import ShenWork.PDE.P3MoserEnergyContinuity
import ShenWork.Paper2.IntervalDuhamelIntegrability

open Filter Topology Set MeasureTheory
open scoped Topology

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint intervalMeasure
   intervalMeasure_integrable_of_abs_bound)
open ShenWork.IntervalMildPicard (HasContinuousSlices)
open ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
  (intervalDomain_lift_continuousOn_Icc_of_continuous)
open ShenWork.IntervalDuhamelIntegrability
  (continuousOn_aestronglyMeasurable_intervalMeasure)
open ShenWork.IntervalMildPicardRegularityEndpoint
  (hasDerivWithinAt_integral_of_dominated_loc_var)

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

/-- Absolute bound transfer through the interval-domain lift. -/
lemma abs_intervalDomainLift_le_of_forall_abs_le
    {w : intervalDomainPoint → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hw : ∀ z : intervalDomainPoint, |w z| ≤ R) (x : ℝ) :
    |intervalDomainLift w x| ≤ R := by
  by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
  · simpa [intervalDomainLift, hx] using hw ⟨x, hx⟩
  · simp [intervalDomainLift, hx, hR]

/-- A.e. strong measurability of the squared negative part of a continuous
slice. -/
lemma negativePart_sq_aestronglyMeasurable_of_continuous
    {w : intervalDomainPoint → ℝ} (hw : Continuous w) :
    AEStronglyMeasurable
      (fun x => (negativePartLift w x) ^ 2) (intervalMeasure 1) := by
  have hlift :
      ContinuousOn (intervalDomainLift w) (Set.Icc (0 : ℝ) 1) :=
    intervalDomain_lift_continuousOn_Icc_of_continuous
      hw
  have hneg :
      ContinuousOn (fun x => (negativePartLift w x) ^ 2)
        (Set.Icc (0 : ℝ) 1) := by
    have h :=
      (negativePart_continuous.continuousOn.comp hlift
        (fun _ _ => Set.mem_univ _)).pow 2
    simpa [negativePartLift, Function.comp] using h
  exact
    continuousOn_aestronglyMeasurable_intervalMeasure
      hneg

/-- **One-sided time Leibniz rule for the negative-part energy.**

If the trajectory `u` has continuous, uniformly bounded slices on `(0, T]`,
and on the compact window `[t, T] ⊆ (0, T]` it is a.e.-in-space pointwise
differentiable in time with a uniformly bounded lifted time derivative, then
the negative-part energy has the tested one-sided derivative
`2 ∫ u_t · (-u_-)` at `t` within `Ici t`. -/
theorem negativePartEnergy_hasDerivWithinAt_Ici_of_window_data
    {T t R B : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (ht : 0 < t) (htT : t < T) (hR : 0 ≤ R)
    (hcont : HasContinuousSlices T u)
    (hbound : ∀ r, 0 < r → r ≤ T → ∀ x : intervalDomainPoint, |u r x| ≤ R)
    (hwindow : ∀ᵐ x ∂ intervalMeasure 1, ∀ r ∈ Set.Icc t T,
      HasDerivWithinAt (fun s => intervalDomainLift (u s) x)
        (intervalDomainLift
          (fun z : intervalDomainPoint =>
            intervalDomain.timeDeriv u r z) x)
        (Set.Icc t T) r ∧
      |intervalDomainLift
          (fun z : intervalDomainPoint =>
            intervalDomain.timeDeriv u r z) x| ≤ B) :
    HasDerivWithinAt (negativePartEnergy u)
      (2 * ∫ x,
        intervalDomainLift
            (fun z : intervalDomainPoint =>
              intervalDomain.timeDeriv u t z) x *
          negativePartTest u t x
        ∂ intervalMeasure 1)
      (Set.Ici t) t := by
  have htmem : t ∈ Set.Icc t T := ⟨le_rfl, htT.le⟩
  set F : ℝ → ℝ → ℝ := fun x r => (negativePartLift (u r) x) ^ 2 with hF_def
  set F' : ℝ → ℝ → ℝ := fun x r =>
    -2 * negativePartLift (u r) x *
      intervalDomainLift
        (fun z : intervalDomainPoint => intervalDomain.timeDeriv u r z) x
    with hF'_def
  -- (1) Measurability of the integrand along the window.
  have hF_meas : ∀ r ∈ Set.Icc t T,
      AEStronglyMeasurable (fun x => F x r) (intervalMeasure 1) := by
    intro r hr
    exact negativePart_sq_aestronglyMeasurable_of_continuous
      (hcont r (lt_of_lt_of_le ht hr.1) hr.2)
  -- (2) Integrability at the base time.
  have hF_int : Integrable (fun x => F x t) (intervalMeasure 1) := by
    refine intervalMeasure_integrable_of_abs_bound (M := R ^ 2)
      (hF_meas t htmem) ?_
    intro y
    have hlift_le : |intervalDomainLift (u t) y| ≤ R :=
      abs_intervalDomainLift_le_of_forall_abs_le hR (hbound t ht htT.le) y
    have hneg_le : |negativePartLift (u t) y| ≤ R := by
      have habs := negativePart_abs_le_abs (intervalDomainLift (u t) y)
      simpa [negativePartLift] using habs.trans hlift_le
    calc |F y t| = |negativePartLift (u t) y| ^ 2 := by
          simp [hF_def, abs_pow]
      _ ≤ R ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hneg_le 2
  -- (3) Uniform dominated bound for the differentiated integrand.
  have hbound_ae : ∀ᵐ x ∂ intervalMeasure 1, ∀ r ∈ Set.Icc t T,
      |F' x r| ≤ 2 * R * B := by
    filter_upwards [hwindow] with x hx r hr
    have hr0 : 0 < r := lt_of_lt_of_le ht hr.1
    have hlift_le : |intervalDomainLift (u r) x| ≤ R :=
      abs_intervalDomainLift_le_of_forall_abs_le hR (hbound r hr0 hr.2) x
    have hneg_le : |negativePartLift (u r) x| ≤ R := by
      have habs := negativePart_abs_le_abs (intervalDomainLift (u r) x)
      simpa [negativePartLift] using habs.trans hlift_le
    have htd_le :
        |intervalDomainLift
            (fun z : intervalDomainPoint =>
              intervalDomain.timeDeriv u r z) x| ≤ B :=
      (hx r hr).2
    have habs_eq : |F' x r| =
        2 * |negativePartLift (u r) x| *
          |intervalDomainLift
            (fun z : intervalDomainPoint =>
              intervalDomain.timeDeriv u r z) x| := by
      simp only [hF'_def]
      rw [abs_mul, abs_mul]
      norm_num
    rw [habs_eq]
    calc 2 * |negativePartLift (u r) x| *
          |intervalDomainLift
            (fun z : intervalDomainPoint =>
              intervalDomain.timeDeriv u r z) x|
        ≤ 2 * R *
          |intervalDomainLift
            (fun z : intervalDomainPoint =>
              intervalDomain.timeDeriv u r z) x| :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hneg_le (by norm_num)) (abs_nonneg _)
      _ ≤ 2 * R * B :=
          mul_le_mul_of_nonneg_left htd_le
            (mul_nonneg (by norm_num) hR)
  have hbound_int :
      Integrable (fun _ : ℝ => 2 * R * B) (intervalMeasure 1) :=
    intervalMeasure_integrable_of_abs_bound (M := |2 * R * B|)
      aestronglyMeasurable_const (fun _ => le_rfl)
  -- (4) Chain rule: pointwise one-sided derivative of the integrand.
  have hdiff : ∀ᵐ x ∂ intervalMeasure 1, ∀ r ∈ Set.Icc t T,
      HasDerivWithinAt (fun a => F x a) (F' x r) (Set.Icc t T) r := by
    filter_upwards [hwindow] with x hx r hr
    have hsq := negativePart_sq_hasDerivAt (intervalDomainLift (u r) x)
    have hcomp := hsq.comp_hasDerivWithinAt r (hx r hr).1
    simpa [hF_def, hF'_def, negativePartLift, Function.comp, mul_assoc]
      using hcomp
  -- (5) Measurability of the differentiated integrand at the base time,
  -- from difference quotients along a sequence inside the window.
  have hslice_meas : ∀ r ∈ Set.Icc t T,
      AEStronglyMeasurable (fun x => intervalDomainLift (u r) x)
        (intervalMeasure 1) := by
    intro r hr
    exact
      continuousOn_aestronglyMeasurable_intervalMeasure
        (intervalDomain_lift_continuousOn_Icc_of_continuous
          (hcont r (lt_of_lt_of_le ht hr.1) hr.2))
  have htd_meas :
      AEStronglyMeasurable
        (fun x =>
          intervalDomainLift
            (fun z : intervalDomainPoint =>
              intervalDomain.timeDeriv u t z) x)
        (intervalMeasure 1) := by
    set δ : ℕ → ℝ := fun n => (T - t) / ((n : ℝ) + 2) with hδ_def
    have hδpos : ∀ n, 0 < δ n := fun n =>
      div_pos (sub_pos.mpr htT) (by positivity)
    have hδle : ∀ n, t + δ n ≤ T := by
      intro n
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have h1 : (1 : ℝ) ≤ (n : ℝ) + 2 := by linarith
      have hd := div_le_self (sub_pos.mpr htT).le h1
      have : δ n ≤ T - t := by simpa [hδ_def] using hd
      linarith
    have hmem_seq : ∀ n, t + δ n ∈ Set.Icc t T \ {t} := by
      intro n
      refine ⟨⟨le_add_of_nonneg_right (hδpos n).le, hδle n⟩, ?_⟩
      have hne : t + δ n ≠ t := by
        have h := (hδpos n).ne'
        intro hcontra
        exact h (by linarith)
      simpa using hne
    have hδlim : Tendsto (fun n => t + δ n) atTop (𝓝 t) := by
      have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
        tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
      have hδ0 : Tendsto δ atTop (𝓝 (0 : ℝ)) := by
        simpa [hδ_def] using
          (tendsto_const_nhds (X := ℝ) (x := T - t)).div_atTop hden
      simpa using (tendsto_const_nhds (X := ℝ) (x := t)).add hδ0
    have htends :
        Tendsto (fun n => t + δ n) atTop (𝓝[Set.Icc t T \ {t}] t) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hδlim
        (Filter.Eventually.of_forall hmem_seq)
    have hslope_meas : ∀ n,
        AEStronglyMeasurable
          (fun x =>
            slope (fun s => intervalDomainLift (u s) x) t (t + δ n))
          (intervalMeasure 1) := by
      intro n
      have h1 := hslice_meas (t + δ n)
        ⟨le_add_of_nonneg_right (hδpos n).le, hδle n⟩
      have h0 := hslice_meas t htmem
      have heq :
          (fun x =>
              slope (fun s => intervalDomainLift (u s) x) t (t + δ n))
            = (t + δ n - t)⁻¹ •
                ((fun x => intervalDomainLift (u (t + δ n)) x) -
                  fun x => intervalDomainLift (u t) x) := by
        funext x
        rw [slope_def_module]
        simp [Pi.smul_apply, Pi.sub_apply]
      rw [heq]
      exact (h1.sub h0).const_smul _
    have htendsto_ae :
        ∀ᵐ x ∂ intervalMeasure 1,
          Tendsto
            (fun n =>
              slope (fun s => intervalDomainLift (u s) x) t (t + δ n))
            atTop
            (𝓝 (intervalDomainLift
              (fun z : intervalDomainPoint =>
                intervalDomain.timeDeriv u t z) x)) := by
      filter_upwards [hwindow] with x hx
      have hder := (hx t htmem).1
      have hslope := hasDerivWithinAt_iff_tendsto_slope.mp hder
      exact hslope.comp htends
    exact aestronglyMeasurable_of_tendsto_ae atTop hslope_meas htendsto_ae
  have hF'_meas :
      AEStronglyMeasurable (fun x => F' x t) (intervalMeasure 1) := by
    have hneg_meas :
        AEStronglyMeasurable
          (fun x => -2 * negativePartLift (u t) x) (intervalMeasure 1) := by
      have hlift :
          ContinuousOn (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
        intervalDomain_lift_continuousOn_Icc_of_continuous
          (hcont t ht htT.le)
      have hcontOn :
          ContinuousOn (fun x => -2 * negativePartLift (u t) x)
            (Set.Icc (0 : ℝ) 1) := by
        have h :=
          (negativePart_continuous.continuousOn.comp hlift
            (fun _ _ => Set.mem_univ _)).const_smul (-2 : ℝ)
        simpa [negativePartLift, Function.comp, smul_eq_mul] using h
      exact
        continuousOn_aestronglyMeasurable_intervalMeasure
          hcontOn
    have h := hneg_meas.mul htd_meas
    have heq :
        (fun x => F' x t)
          = (fun x => -2 * negativePartLift (u t) x) *
            fun x =>
              intervalDomainLift
                (fun z : intervalDomainPoint =>
                  intervalDomain.timeDeriv u t z) x := by
      funext x
      simp [hF'_def]
    rw [heq]
    exact h
  -- (6) Dominated one-sided differentiation under the integral.
  have hraw :
      HasDerivWithinAt (fun r => ∫ x, F x r ∂ intervalMeasure 1)
        (∫ x, F' x t ∂ intervalMeasure 1) (Set.Icc t T) t :=
    hasDerivWithinAt_integral_of_dominated_loc_var
      (convex_Icc t T) htmem hF_meas hF_int hF'_meas hbound_ae
      hbound_int hdiff
  -- (7) Identify the function and the derivative value.
  have henergy :
      (fun r => ∫ x, F x r ∂ intervalMeasure 1) = negativePartEnergy u := by
    funext r
    simp [hF_def, negativePartEnergy]
  have hE' :
      (∫ x, F' x t ∂ intervalMeasure 1) =
        2 * ∫ x,
          intervalDomainLift
              (fun z : intervalDomainPoint =>
                intervalDomain.timeDeriv u t z) x *
            negativePartTest u t x
          ∂ intervalMeasure 1 := by
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hF'_def, negativePartTest]
    ring
  rw [← henergy, ← hE']
  have hwin : Set.Icc t T ∈ 𝓝[Set.Ici t] t := by
    rw [← Set.Ici_inter_Iic]
    exact inter_mem_nhdsWithin _ (Iic_mem_nhds htT)
  exact hraw.mono_of_mem_nhdsWithin hwin

end ShenWork.Paper2.BFormPositiveDatumNegPart
