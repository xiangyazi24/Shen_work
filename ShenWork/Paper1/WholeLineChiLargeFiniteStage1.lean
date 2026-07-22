import ShenWork.Paper1.WholeLineChiLargeNonnegativeEnergyProducer

/-!
# Uniform local moments on one physical BUC fixed-point segment

The nonnegative energy package gives the same scalar damping estimate as the
strictly-positive package.  Continuity of a BUC trajectory supplies continuity
of the translated local energy at time zero, so the damping estimate closes
uniformly in the terminal time and in the translated centre.
-/

open Filter MeasureTheory Real Set Topology

noncomputable section

namespace ShenWork.Paper1

/-- A bounded physical BUC trajectory has continuous translated local energy.
The extension is projected to the compact construction interval, hence the
same spatial majorant works at every ambient time. -/
theorem wholeLineBUCTrajectory_localLpEnergy_continuous
    {M T P κ : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hP : 0 ≤ P) (hκ : 0 < κ)
    (U : WholeLineBUCTrajectory T)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (U z).1 x ∈ Set.Icc (0 : ℝ) M)
    (x₀ : ℝ) :
    let u : ℝ → ℝ → ℝ := fun t x =>
      (wholeLineBUCTrajectoryExtend hT U t).1 x
    Continuous (fun t : ℝ => wholeLineLocalLpEnergy P κ u t x₀) := by
  dsimp only
  let Ext : ℝ → WholeLineBUC := wholeLineBUCTrajectoryExtend hT U
  let u : ℝ → ℝ → ℝ := fun t x => (Ext t).1 x
  have hExt : Continuous Ext :=
    wholeLineBUCTrajectoryExtend_continuous hT U
  have hstripExt : ∀ s x, u s x ∈ Set.Icc (0 : ℝ) M := by
    intro s x
    dsimp [u, Ext, wholeLineBUCTrajectoryExtend]
    exact hstrip (Set.projIcc 0 T hT s) x
  rw [continuous_iff_continuousAt]
  intro t
  let F : ℝ → ℝ → ℝ := fun s x =>
    (u s x) ^ P * localizingWeightAt κ x₀ x
  let bound : ℝ → ℝ := fun x =>
    M ^ P * localizingWeightAt κ x₀ x
  have hmeas : ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable (F s) volume := by
    filter_upwards [] with s
    exact (((Real.continuous_rpow_const hP).comp
      (WholeLineBUC.isCUnifBdd (Ext s)).1).mul
        continuous_localizingWeightAt).aestronglyMeasurable
  have hbound : ∀ᶠ s in 𝓝 t,
      ∀ᵐ x ∂volume, ‖F s x‖ ≤ bound x := by
    filter_upwards [] with s
    filter_upwards [] with x
    have hu0 := (hstripExt s x).1
    have huM := (hstripExt s x).2
    have hpow := Real.rpow_le_rpow hu0 huM hP
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg hu0 P),
      abs_of_pos (localizingWeightAt_pos κ x₀ x)]
    exact mul_le_mul_of_nonneg_right hpow
      (localizingWeightAt_pos κ x₀ x).le
  have hboundInt : Integrable bound volume :=
    (localizingWeightAt_integrable hκ x₀).const_mul (M ^ P)
  have hlim : ∀ᵐ x ∂volume,
      Tendsto (fun s => F s x) (𝓝 t) (𝓝 (F t x)) := by
    filter_upwards [] with x
    have heval : Continuous (fun w : WholeLineBUC => w.1 x) := by
      fun_prop
    have hu : Tendsto (fun s => u s x) (𝓝 t) (𝓝 (u t x)) := by
      change Tendsto (fun s => (Ext s).1 x) (𝓝 t) (𝓝 ((Ext t).1 x))
      exact heval.continuousAt.tendsto.comp
        (show ContinuousAt Ext t from hExt.continuousAt)
    exact (((Real.continuous_rpow_const hP).tendsto (u t x)).comp hu).mul_const _
  have hint := tendsto_integral_filter_of_dominated_convergence
    bound hmeas hbound hboundInt hlim
  change Tendsto
    (fun s => (1 / P) * ∫ x, F s x) (𝓝 t)
      (𝓝 ((1 / P) * ∫ x, F t x))
  exact hint.const_mul (1 / P)

/-- The complete Stage-1 estimate on one physical canonical segment.  Its
constant is independent of the segment horizon and of its clamp ceiling. -/
theorem wholeLineCauchyBUCMildFixedPoint_uniformlyLocalLpBounded_nonnegative
    (p : CMParams) {M T P κ : ℝ}
    (hM : 0 ≤ M) (hT : 0 < T)
    (hP : 1 < P) (hPtwo : 2 ≤ P)
    (hκ : 0 < κ) (hκhalf : κ < 1 / 2)
    (hχ : 0 ≤ p.χ)
    (hcritical : p.α = p.m + p.γ - 1)
    (habsorption : 0 < wholeLineLocalMomentAbsorption p P κ)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT.le
        u₀ hsmall z).1 x ∈ Set.Icc (0 : ℝ) M) :
    let Traj :=
      wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall
    let u : ℝ → ℝ → ℝ := fun t x =>
      (wholeLineBUCTrajectoryExtend hT.le Traj t).1 x
    UniformlyLocalLpBounded P κ u T
      (P * max ((‖u₀‖ ^ P * (2 / κ)) / P)
        (wholeLineLocalMomentDampingRhs p P κ)) := by
  dsimp only
  let Traj : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall
  let u : ℝ → ℝ → ℝ := fun t x =>
    (wholeLineBUCTrajectoryExtend hT.le Traj t).1 x
  let v : ℝ → ℝ → ℝ := fun t => frozenElliptic p (u t)
  let E : ℝ → ℝ → ℝ := fun x₀ t =>
    wholeLineLocalLpEnergy P κ u t x₀
  have hP0 : 0 < P := zero_lt_one.trans hP
  have hcont : ∀ x₀, ContinuousOn (E x₀) (Set.Icc (0 : ℝ) T) := by
    intro x₀
    exact (wholeLineBUCTrajectory_localLpEnergy_continuous
      hM hT.le hP0.le hκ Traj (by simpa [Traj] using hstrip) x₀).continuousOn
  have hdamping : ∀ x₀, ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt (E x₀) (deriv (E x₀) s) s ∧
        deriv (E x₀) s + E x₀ s ≤
          wholeLineLocalMomentDampingRhs p P κ := by
    intro x₀ s hs
    let H :=
      wholeLineCauchyBUCMildFixedPoint_localMomentNonnegativeEnergyData
        p (x₀ := x₀) hM hT.le hP hPtwo hκ hs.1 hs.2
          u₀ hsmall hstrip
    have hderiv := H.energy_hasDerivAt
    have huC : IsCUnifBdd (u s) :=
      WholeLineBUC.isCUnifBdd
        (wholeLineBUCTrajectoryExtend hT.le Traj s)
    have hu0 : ∀ x, 0 ≤ u s x := by
      intro x
      dsimp [u, wholeLineBUCTrajectoryExtend]
      exact (hstrip (Set.projIcc 0 T hT.le s) x).1
    have hdamp := H.critical_energy_damping hχ hκhalf hcritical
      habsorption huC hu0 rfl
    exact ⟨hderiv.congr_deriv hderiv.deriv.symm, by
      simpa [E, u, v, Traj] using hdamp⟩
  intro t ht x₀
  have hscalar : E x₀ t ≤
      max (E x₀ 0) (wholeLineLocalMomentDampingRhs p P κ) := by
    have hraw := scalarEnergy_uniform_bound_of_positive_time_damping
      (E := E x₀) (T := T) (lam := 1)
      (K := wholeLineLocalMomentDampingRhs p P κ)
      hT.le one_pos (hcont x₀)
      (fun s hs => (hdamping x₀ s hs).1)
      (fun s hs => by simpa only [one_mul] using (hdamping x₀ s hs).2)
      t ⟨ht.1, ht.2.le⟩
    simpa only [div_one] using hraw
  have hzero : wholeLineBUCTrajectoryExtend hT.le Traj 0 = u₀ := by
    rw [wholeLineBUCTrajectoryExtend_eq hT.le Traj ⟨le_rfl, hT.le⟩]
    simpa [Traj] using wholeLineCauchyBUCMildFixedPoint_initial
      p hM hT.le u₀ hsmall ⟨le_rfl, hT.le⟩
  have hu0_nonneg : ∀ x, 0 ≤ u 0 x := by
    intro x
    let z0 : Set.Icc (0 : ℝ) T := ⟨0, le_rfl, hT.le⟩
    have hs := (hstrip z0 x).1
    have hinit :
        wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall z0 = u₀ := by
      simpa [z0] using wholeLineCauchyBUCMildFixedPoint_initial
        p hM hT.le u₀ hsmall ⟨le_rfl, hT.le⟩
    rw [hinit] at hs
    simpa [u, hzero] using hs
  have hmoment0 :
      wholeLineLocalLpMoment P κ u 0 x₀ ≤
        ‖u₀‖ ^ P * (2 / κ) := by
    apply wholeLineLocalLpMoment_le_two_mul_div
      hP0.le hκ (norm_nonneg u₀)
    · simpa [u, hzero] using WholeLineBUC.isCUnifBdd u₀ |>.1
    · exact hu0_nonneg
    · intro x
      simpa [u, hzero] using WholeLineBUC.apply_le_norm u₀ x
  have hEzero : E x₀ 0 ≤ (‖u₀‖ ^ P * (2 / κ)) / P := by
    change (1 / P) * wholeLineLocalLpMoment P κ u 0 x₀ ≤
      (‖u₀‖ ^ P * (2 / κ)) / P
    have hscaled := mul_le_mul_of_nonneg_left hmoment0
      (one_div_nonneg.mpr hP0.le)
    convert hscaled using 1 <;> field_simp [hP0.ne']
  have hEt : E x₀ t ≤
      max ((‖u₀‖ ^ P * (2 / κ)) / P)
        (wholeLineLocalMomentDampingRhs p P κ) :=
    hscalar.trans (max_le_max hEzero le_rfl)
  have hscaled := mul_le_mul_of_nonneg_left hEt hP0.le
  have hmomentEq :
      wholeLineLocalLpMoment P κ u t x₀ = P * E x₀ t := by
    dsimp [E, wholeLineLocalLpEnergy]
    field_simp [hP0.ne']
  rw [hmomentEq]
  exact hscaled

section AxiomAudit

#print axioms wholeLineBUCTrajectory_localLpEnergy_continuous
#print axioms wholeLineCauchyBUCMildFixedPoint_uniformlyLocalLpBounded_nonnegative

end AxiomAudit

end ShenWork.Paper1
