/-
  ShenWork/PDE/IntervalFullKernelCleanFull.lean

  **T2 — `_clean_full`: the snapshot-preservation hmap on the FULL Neumann kernel.**

  Full-Neumann-kernel mirror of
  `intervalCoupledClassicalC1BallEstimates_hmap_dirichlet_initial_clean`, on the
  full Duhamel operator `intervalFullKernelCoupledDuhamelOperator`.  The decisive
  difference: the boundary-derivative bridge `hGradEq` — carried as a HYPOTHESIS in
  the zeroth-reflection `_clean` (it is FALSE at the right endpoint for that kernel)
  — is here DISCHARGED via the proved `intervalFullKernel_hGradEq` (true at every
  `x ∈ [0,1]`, including `x = 1`).  The gradient conjunct then uses the complete
  full-kernel gradient estimate `intervalFullCoupledDuhamel_grad_estimate_full`
  (T2-g), and the sup conjunct uses `intervalFullKernelDuhamel_lift_abs_le` (T2-i).

  The Leibniz/integrability bridges (`hSplit`, `hLeibniz`, `hGrad_int`) are carried
  as hypotheses, exactly as `_clean` carries `hSplit` — textbook differentiation-
  under-the-integral, dischargeable by a full-kernel Leibniz lemma.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.PDE.IntervalFullKernelGradEstimateFull
import ShenWork.PDE.IntervalFullKernelDuhamelSup
import ShenWork.PDE.IntervalFullKernelDuhamelGradEq
import ShenWork.PDE.IntervalCoupledClassicalBallEstimates

open MeasureTheory
open scoped Topology

namespace ShenWork.IntervalNeumannFullKernel

open ShenWork.IntervalDomain ShenWork.IntervalDomainExistence
open ShenWork.IntervalCoupledClassicalBallEstimates ShenWork.Paper2

/-- **`_clean_full`.**  Snapshot preservation by the full-kernel coupled Duhamel
operator, with `hGradEq` discharged on the full Neumann kernel. -/
theorem intervalFullKernelClassicalC1BallEstimates_hmap_dirichlet_initial_clean
    {p : CM2Params}
    {R : (intervalDomainPoint → ℝ) → intervalDomainPoint → ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u₀_ext u₀'_ext : ℝ → ℝ}
    {T M G_u G_u_init C_source H Cu₀ : ℝ}
    (hT : 0 < T) (hH_nn : 0 ≤ H) (hC_nn : 0 ≤ C_source)
    (hG_init_nn : 0 ≤ G_u_init)
    (hM_eq : M = H + C_source * T)
    (hG_u_eq : G_u = G_u_init +
      ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
        (2 * Real.sqrt T) * C_source)
    (hu₀_sup : ∀ y : intervalDomainPoint, |u₀ y| ≤ H)
    (hext_eq : ∀ y ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift u₀ y = u₀_ext y)
    (hu₀_ext_int : MeasureTheory.Integrable u₀_ext (intervalMeasure 1))
    (hu₀_ext_bound : ∀ y, |u₀_ext y| ≤ Cu₀)
    (hu₀_ext_C1 : ∀ y ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt u₀_ext (u₀'_ext y) y)
    (hu₀_ext'_int : IntervalIntegrable u₀'_ext MeasureTheory.volume 0 1)
    (hu₀_ext_one : u₀_ext 1 = 0)
    (hu₀_ext'_sup : ∀ y : ℝ, |u₀'_ext y| ≤ G_u_init)
    (hSol : ∀ u v : ℝ → intervalDomainPoint → ℝ,
      IntervalDomainClassicalC1Snapshot p T M G_u u v →
        IsPaper2ClassicalSolution intervalDomain p T
          (fun τ : ℝ => fun y : intervalDomainPoint =>
            intervalFullKernelCoupledDuhamelOperator p R u₀ u τ y) v)
    (hSource_sup_local :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ s, 0 ≤ s → s ≤ T → ∀ y : ℝ,
            |intervalDomainLift
              (intervalCoupledSource p (u s) (R (u s))) y| ≤ C_source)
    (hSource_sup_global :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ s : ℝ, ∀ y : ℝ,
            |intervalDomainLift
              (intervalCoupledSource p (u s) (R (u s))) y| ≤ C_source)
    (hint :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ (t : ℝ) (x : intervalDomainPoint), 0 < t → t ≤ T →
            MeasureTheory.IntegrableOn
              (fun s => intervalFullSemigroupOperator (t - s)
                (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) x.1)
              (Set.Icc 0 t) MeasureTheory.volume)
    (hSource_int_global :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ s : ℝ,
            MeasureTheory.Integrable
              (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
              (intervalMeasure 1))
    (hSplit :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ (τ : ℝ) (x : ℝ), τ ∈ Set.Ioo (0 : ℝ) T → x ∈ Set.Icc (0 : ℝ) 1 →
            deriv (fun z : ℝ =>
              intervalFullSemigroupOperator τ u₀_ext z +
              ∫ s in (0 : ℝ)..τ,
                intervalFullSemigroupOperator (τ - s)
                  (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) z) x =
            deriv (fun z : ℝ => intervalFullSemigroupOperator τ u₀_ext z) x +
            deriv (fun z : ℝ =>
              ∫ s in (0 : ℝ)..τ,
                intervalFullSemigroupOperator (τ - s)
                  (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) z) x)
    (hLeibniz :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ (τ : ℝ) (x : ℝ), τ ∈ Set.Ioo (0 : ℝ) T → x ∈ Set.Icc (0 : ℝ) 1 →
            deriv (fun z : ℝ =>
              ∫ s in (0 : ℝ)..τ,
                intervalFullSemigroupOperator (τ - s)
                  (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) z) x =
            ∫ s in (0 : ℝ)..τ,
              deriv (fun z : ℝ =>
                intervalFullSemigroupOperator (τ - s)
                  (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) z) x)
    (hGrad_int :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ (τ : ℝ) (x : ℝ), τ ∈ Set.Ioo (0 : ℝ) T → x ∈ Set.Icc (0 : ℝ) 1 →
            IntervalIntegrable
              (fun s : ℝ =>
                deriv (fun z : ℝ =>
                  intervalFullSemigroupOperator (τ - s)
                    (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) z) x)
              MeasureTheory.volume (0 : ℝ) τ) :
    ∀ u v : ℝ → intervalDomainPoint → ℝ,
      IntervalDomainClassicalC1Snapshot p T M G_u u v →
        IntervalDomainClassicalC1Snapshot p T M G_u
          (fun t : ℝ => fun x : intervalDomainPoint =>
            intervalFullKernelCoupledDuhamelOperator p R u₀ u t x) v := by
  intro u v hsnap
  -- `hLiftSemigroupEq` from `hext_eq`, for the full kernel.
  have hLiftSemigroupEq :
      ∀ (τ : ℝ) (x : ℝ),
        intervalFullSemigroupOperator τ (intervalDomainLift u₀) x =
        intervalFullSemigroupOperator τ u₀_ext x := by
    intro τ x
    unfold intervalFullSemigroupOperator
    refine MeasureTheory.integral_congr_ae ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro y hy
    show intervalNeumannFullKernel τ x y * intervalDomainLift u₀ y =
      intervalNeumannFullKernel τ x y * u₀_ext y
    rw [hext_eq y hy]
  -- envelope integrability (kernel-agnostic).
  have hDom_int_local :
      ∀ (τ : ℝ), τ ∈ Set.Ioo (0 : ℝ) T →
        IntervalIntegrable
          (fun s : ℝ =>
            ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
              * C_source * (τ - s) ^ (-(1/2 : ℝ)))
          MeasureTheory.volume (0 : ℝ) τ :=
    fun τ hτ => intervalCoupledDuhamel_grad_envelope_intervalIntegrable hτ.1 C_source
  refine ⟨hSol u v hsnap, ?_, ?_⟩
  · -- Sup-bound conjunct (via the full-kernel Duhamel sup bound, T2-i).
    intro τ hτ x hxIcc
    have hτ_le : τ ≤ T := le_of_lt hτ.2
    have hsource' :
        ∀ s, 0 ≤ s → s ≤ T → ∀ y : ℝ,
          |intervalDomainLift (intervalCoupledSource p (u s) (R (u s))) y| ≤ C_source :=
      fun s hs0 hsT y => hSource_sup_local u v hsnap s hs0 hsT y
    have hint_pt :
        ∀ x' : intervalDomainPoint,
          MeasureTheory.IntegrableOn
            (fun s => intervalFullSemigroupOperator (τ - s)
              (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) x'.1)
            (Set.Icc 0 τ) MeasureTheory.volume :=
      fun x' => hint u v hsnap τ x' hτ.1 hτ_le
    have hsup_le :=
      intervalFullKernelDuhamel_lift_abs_le
        (p := p) (R := R) (u₀ := u₀) (u := u) (H := H) (C := C_source) (T := T)
        hH_nn hC_nn hu₀_sup hsource' (t := τ) hτ.1 hτ_le hint_pt x hxIcc
    rw [hM_eq.symm] at hsup_le
    exact hsup_le
  · -- Gradient-bound conjunct: discharge `hGradEq` via `intervalFullKernel_hGradEq`.
    intro τ hτ x hxIcc
    have hτ_le : τ ≤ T := le_of_lt hτ.2
    have hτ_pos : 0 < τ := hτ.1
    rw [intervalFullKernel_hGradEq (T := T) τ x hτ hxIcc]
    have hreplace_fun :
        (fun z : ℝ =>
          intervalFullSemigroupOperator τ (intervalDomainLift u₀) z +
          ∫ s in (0 : ℝ)..τ,
            intervalFullSemigroupOperator (τ - s)
              (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) z) =
        (fun z : ℝ =>
          intervalFullSemigroupOperator τ u₀_ext z +
          ∫ s in (0 : ℝ)..τ,
            intervalFullSemigroupOperator (τ - s)
              (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) z) := by
      funext z
      rw [hLiftSemigroupEq τ z]
    rw [hreplace_fun]
    have hF_int_τ :
        ∀ s, MeasureTheory.Integrable
          (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
          (intervalMeasure 1) :=
      fun s => hSource_int_global u v hsnap s
    have hF_sup_τ :
        ∀ s : ℝ, ∀ y : ℝ,
          |intervalDomainLift (intervalCoupledSource p (u s) (R (u s))) y| ≤ C_source :=
      fun s y => hSource_sup_global u v hsnap s y
    have hbound :=
      intervalFullCoupledDuhamel_grad_estimate_full
        (t := τ) (T := T) hτ_pos hτ_le
        (u₀ := u₀_ext) (u₀' := u₀'_ext)
        hu₀_ext_int.aestronglyMeasurable (Cu₀ := Cu₀) hu₀_ext_bound
        hu₀_ext_C1 hu₀_ext'_int hu₀_ext_one
        (G_init := G_u_init) hG_init_nn hu₀_ext'_sup
        (F := fun s : ℝ => intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
        hF_int_τ (C_source := C_source) hC_nn hF_sup_τ x
        (hSplit u v hsnap τ x hτ hxIcc)
        (hLeibniz u v hsnap τ x hτ hxIcc)
        (hGrad_int u v hsnap τ x hτ hxIcc)
        (hDom_int_local τ hτ)
    rw [hG_u_eq]
    exact hbound

end ShenWork.IntervalNeumannFullKernel
