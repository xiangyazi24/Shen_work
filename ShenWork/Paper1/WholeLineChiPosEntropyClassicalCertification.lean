import ShenWork.Paper1.WholeLineChiPosEntropyLiouville
import ShenWork.Paper1.WholeLineLocalMomentBound
import ShenWork.Paper1.WholeLineLocalMomentEnergyProducer

/-!
# Entropy certification of a bounded entire classical limit

The compactness argument should only have to produce a bounded entire
classical solution.  This file proves that such a solution automatically
carries every weighted integrability, whole-line integration-by-parts, and
time-Leibniz field in `ChiOneEntireWeightedEntropyData`.
-/

open Filter MeasureTheory Real Set Topology

noncomputable section

namespace ShenWork.Paper1

/-- Natural classical payload for an entire normalized co-moving solution.
All seven fields have one uniform bound.  The four displayed spatial
derivative identities are exactly what is preserved by local `C²` convergence;
the time identity is preserved by local convergence of `u` and `uₜ`. -/
structure ChiOneEntireBoundedClassicalData
    (chi c ell k x₀ : ℝ)
    (u ux uxx ut r rx rxx : ℝ → ℝ → ℝ) : Prop where
  hkpos : 0 < k
  hk1 : k < 1
  hchi : 0 ≤ chi
  hell : 0 < ell
  u_floor : ∀ t x, ell ≤ u t x
  u_space_deriv : ∀ t x, HasDerivAt (u t) (ux t x) x
  ux_space_deriv : ∀ t x, HasDerivAt (ux t) (uxx t x) x
  r_space_deriv : ∀ t x, HasDerivAt (r t) (rx t x) x
  rx_space_deriv : ∀ t x, HasDerivAt (rx t) (rxx t x) x
  u_time_deriv : ∀ t x, HasDerivAt (fun s => u s x) (ut t x) t
  uxx_continuous : ∀ t, Continuous (uxx t)
  ut_continuous : ∀ t, Continuous (ut t)
  rxx_continuous : ∀ t, Continuous (rxx t)
  population_pde : ∀ t x,
    ut t x = uxx t x + c * ux t x -
      chi * (ux t x * rx t x + u t x * rxx t x) +
        u t x * (1 - u t x)
  resolver : ∀ t x, -rxx t x + r t x = u t x - 1
  uniform_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ t x,
    |u t x| ≤ C ∧ |ux t x| ≤ C ∧ |uxx t x| ≤ C ∧
    |ut t x| ≤ C ∧ |r t x| ≤ C ∧ |rx t x| ≤ C ∧
    |rxx t x| ≤ C

private theorem cub_add {f g : ℝ → ℝ}
    (hf : IsCUnifBdd f) (hg : IsCUnifBdd g) :
    IsCUnifBdd (fun x => f x + g x) := by
  obtain ⟨Cf, hfC⟩ := hf.2
  obtain ⟨Cg, hgC⟩ := hg.2
  refine ⟨hf.1.add hg.1, ⟨Cf + Cg, fun x => ?_⟩⟩
  exact (abs_add_le (f x) (g x)).trans (add_le_add (hfC x) (hgC x))

private theorem cub_neg {f : ℝ → ℝ} (hf : IsCUnifBdd f) :
    IsCUnifBdd (fun x => -f x) := by
  obtain ⟨C, hC⟩ := hf.2
  exact ⟨hf.1.neg, ⟨C, fun x => by simpa using hC x⟩⟩

private theorem cub_sub {f g : ℝ → ℝ}
    (hf : IsCUnifBdd f) (hg : IsCUnifBdd g) :
    IsCUnifBdd (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using cub_add hf (cub_neg hg)

private theorem cub_mul {f g : ℝ → ℝ}
    (hf : IsCUnifBdd f) (hg : IsCUnifBdd g) :
    IsCUnifBdd (fun x => f x * g x) := by
  obtain ⟨Cf, hfC⟩ := hf.2
  obtain ⟨Cg, hgC⟩ := hg.2
  have hCf0 : 0 ≤ Cf := (abs_nonneg (f 0)).trans (hfC 0)
  have hCg0 : 0 ≤ Cg := (abs_nonneg (g 0)).trans (hgC 0)
  refine ⟨hf.1.mul hg.1, ⟨Cf * Cg, fun x => ?_⟩⟩
  rw [abs_mul]
  exact mul_le_mul (hfC x) (hgC x) (abs_nonneg _) hCf0

private theorem cub_const_mul (a : ℝ) {f : ℝ → ℝ}
    (hf : IsCUnifBdd f) : IsCUnifBdd (fun x => a * f x) :=
  cub_mul (isCUnifBdd_const a) hf

private theorem cub_pow_two {f : ℝ → ℝ} (hf : IsCUnifBdd f) :
    IsCUnifBdd (fun x => (f x) ^ 2) := by
  simpa only [pow_two] using cub_mul hf hf

private theorem cub_inv_of_floor
    {ell : ℝ} {f : ℝ → ℝ} (hell : 0 < ell)
    (hfloor : ∀ x, ell ≤ f x) (hf : IsCUnifBdd f) :
    IsCUnifBdd (fun x => (f x)⁻¹) := by
  have hfpos : ∀ x, 0 < f x := fun x => hell.trans_le (hfloor x)
  refine ⟨hf.1.inv₀ (fun x => (hfpos x).ne'), ⟨ell⁻¹, fun x => ?_⟩⟩
  rw [abs_of_pos (inv_pos.mpr (hfpos x))]
  exact (inv_le_inv₀ (hfpos x) hell).2 (hfloor x)

private theorem cub_entropyMultiplier_of_floor
    {ell : ℝ} {f : ℝ → ℝ} (hell : 0 < ell)
    (hfloor : ∀ x, ell ≤ f x) (hf : IsCUnifBdd f) :
    IsCUnifBdd (fun x => chiOneEntropyMultiplier (f x)) := by
  simpa only [chiOneEntropyMultiplier] using
    cub_sub (isCUnifBdd_const 1) (cub_inv_of_floor hell hfloor hf)

private theorem cub_relativeEntropy_of_floor
    {ell : ℝ} {f : ℝ → ℝ} (hell : 0 < ell)
    (hfloor : ∀ x, ell ≤ f x) (hf : IsCUnifBdd f) :
    IsCUnifBdd (fun x => chiOneRelativeEntropy (f x)) := by
  obtain ⟨C, hC⟩ := hf.2
  have hC0 : 0 ≤ C := (abs_nonneg (f 0)).trans (hC 0)
  have hfpos : ∀ x, 0 < f x := fun x => hell.trans_le (hfloor x)
  refine ⟨?_, ⟨(C + 1) ^ 2 / ell, fun x => ?_⟩⟩
  · unfold chiOneRelativeEntropy
    exact (hf.1.sub continuous_const).sub (hf.1.log fun x => (hfpos x).ne')
  · rw [abs_of_nonneg (chiOneRelativeEntropy_nonneg (hfpos x))]
    have hent := chiOneRelativeEntropy_le_sq_div hell (hfloor x)
    have habs : |f x - 1| ≤ C + 1 := by
      exact (abs_sub (f x) 1).trans <| by
        simpa only [abs_one] using add_le_add (hC x) (le_refl 1)
    have hsquare : (f x - 1) ^ 2 ≤ (C + 1) ^ 2 := by
      nlinarith [sq_abs (f x - 1), abs_nonneg (f x - 1)]
    exact hent.trans (div_le_div_of_nonneg_right hsquare hell.le)

private theorem integrable_mul_weight
    {k x₀ : ℝ} (hk : 0 < k) {f : ℝ → ℝ} (hf : IsCUnifBdd f) :
    Integrable (fun x => f x * localizingWeightAt k x₀ x) := by
  obtain ⟨C, hC⟩ := hf.2
  have hC0 : 0 ≤ C := (abs_nonneg (f 0)).trans (hC 0)
  have hmajor : Integrable (fun x => C * localizingWeightAt k x₀ x) :=
    (localizingWeightAt_integrable hk x₀).const_mul C
  refine Integrable.mono' hmajor
    (hf.1.mul continuous_localizingWeightAt).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_pos (localizingWeightAt_pos k x₀ x)]
  exact mul_le_mul_of_nonneg_right (hC x)
    (localizingWeightAt_pos k x₀ x).le

private theorem integrable_mul_weightDeriv
    {k x₀ : ℝ} (hk : 0 < k) {f : ℝ → ℝ} (hf : IsCUnifBdd f) :
    Integrable (fun x => f x * deriv (localizingWeightAt k x₀) x) := by
  obtain ⟨C, hC⟩ := hf.2
  have hC0 : 0 ≤ C := (abs_nonneg (f 0)).trans (hC 0)
  have hmajor : Integrable
      (fun x => (C * k) * localizingWeightAt k x₀ x) :=
    (localizingWeightAt_integrable hk x₀).const_mul (C * k)
  have hwcont : Continuous (deriv (localizingWeightAt k x₀)) := by
    simpa only [iteratedDeriv_one] using
      (contDiff_two_localizingWeightAt k x₀).continuous_iteratedDeriv 1 (by norm_num)
  refine Integrable.mono' hmajor (hf.1.mul hwcont).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have hmul := mul_le_mul (hC x)
    (abs_deriv_localizingWeightAt_le hk.le x₀ x)
    (abs_nonneg _) hC0
  simpa only [mul_assoc] using hmul

private theorem tendsto_bounded_mul_zero
    {l : Filter ℝ} {f g : ℝ → ℝ} (hf : IsBddFun f)
    (hg : Tendsto g l (𝓝 0)) :
    Tendsto (fun x => f x * g x) l (𝓝 0) := by
  obtain ⟨C, hC⟩ := hf
  have hC0 : 0 ≤ C := (abs_nonneg (f 0)).trans (hC 0)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (g := fun x => C * ‖g x‖)
    (Eventually.of_forall fun x => norm_nonneg _)
    (Eventually.of_forall fun x => ?_) ?_
  · rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg (g x))
  · simpa using tendsto_const_nhds.mul hg.norm

namespace ChiOneEntireBoundedClassicalData

variable {chi c ell k x₀ : ℝ}
    {u ux uxx ut r rx rxx : ℝ → ℝ → ℝ}
    (H : ChiOneEntireBoundedClassicalData chi c ell k x₀
      u ux uxx ut r rx rxx)

include H

theorem u_continuous (t : ℝ) : Continuous (u t) :=
  continuous_iff_continuousAt.2 fun x => (H.u_space_deriv t x).continuousAt

theorem ux_continuous (t : ℝ) : Continuous (ux t) :=
  continuous_iff_continuousAt.2 fun x => (H.ux_space_deriv t x).continuousAt

theorem r_continuous (t : ℝ) : Continuous (r t) :=
  continuous_iff_continuousAt.2 fun x => (H.r_space_deriv t x).continuousAt

theorem rx_continuous (t : ℝ) : Continuous (rx t) :=
  continuous_iff_continuousAt.2 fun x => (H.rx_space_deriv t x).continuousAt

private theorem slice_cub (t : ℝ) :
    IsCUnifBdd (u t) ∧ IsCUnifBdd (ux t) ∧ IsCUnifBdd (uxx t) ∧
    IsCUnifBdd (ut t) ∧ IsCUnifBdd (r t) ∧ IsCUnifBdd (rx t) ∧
    IsCUnifBdd (rxx t) := by
  obtain ⟨C, _hC, hbound⟩ := H.uniform_bound
  exact ⟨
    ⟨H.u_continuous t, ⟨C, fun x => (hbound t x).1⟩⟩,
    ⟨H.ux_continuous t, ⟨C, fun x => (hbound t x).2.1⟩⟩,
    ⟨H.uxx_continuous t, ⟨C, fun x => (hbound t x).2.2.1⟩⟩,
    ⟨H.ut_continuous t, ⟨C, fun x => (hbound t x).2.2.2.1⟩⟩,
    ⟨H.r_continuous t, ⟨C, fun x => (hbound t x).2.2.2.2.1⟩⟩,
    ⟨H.rx_continuous t, ⟨C, fun x => (hbound t x).2.2.2.2.2.1⟩⟩,
    ⟨H.rxx_continuous t, ⟨C, fun x => (hbound t x).2.2.2.2.2.2⟩⟩⟩

/-- Every bounded classical time slice has all weighted resolver and entropy
IBP/integrability data. -/
theorem weightedEntropyData (t : ℝ) :
    ChiOneWeightedEntropyData chi c ell k x₀
      (u t) (ux t) (uxx t) (ut t) (r t) (rx t) (rxx t) := by
  obtain ⟨hu, hux, huxx, hut, hr, hrx, hrxx⟩ := H.slice_cub t
  have hfloor : ∀ x, ell ≤ u t x := H.u_floor t
  have hupos : ∀ x, 0 < u t x := fun x => H.hell.trans_le (hfloor x)
  have hinv : IsCUnifBdd (fun x => (u t x)⁻¹) :=
    cub_inv_of_floor H.hell hfloor hu
  have hinvSq : IsCUnifBdd (fun x => ((u t x)⁻¹) ^ 2) :=
    cub_pow_two hinv
  have hmult : IsCUnifBdd (fun x => chiOneEntropyMultiplier (u t x)) :=
    cub_entropyMultiplier_of_floor H.hell hfloor hu
  have hent : IsCUnifBdd (fun x => chiOneRelativeEntropy (u t x)) :=
    cub_relativeEntropy_of_floor H.hell hfloor hu
  have hsource : IsCUnifBdd (fun x => u t x - 1) :=
    cub_sub hu (isCUnifBdd_const 1)
  have huxOverU : IsCUnifBdd (fun x => ux t x / u t x) := by
    simpa only [div_eq_mul_inv] using cub_mul hux hinv
  have huxOverUSq : IsCUnifBdd (fun x => ux t x / (u t x) ^ 2) := by
    have hraw := cub_mul hux hinvSq
    convert hraw using 1
    funext x
    field_simp [(hupos x).ne']
  have hresolverIBP : WholeLineIBPData
      (fun x => localizingWeightAt k x₀ x * r t x)
      (fun x => deriv (localizingWeightAt k x₀) x * r t x +
        localizingWeightAt k x₀ x * rx t x)
      (rx t) (rxx t) := by
    refine
      { hasDerivAt_left := fun x _ => by
          simpa only [deriv_localizingWeightAt] using
            (hasDerivAt_localizingWeightAt k x₀ x).mul (H.r_space_deriv t x)
        hasDerivAt_right := fun x _ => H.rx_space_deriv t x
        left_integrable := ?_
        right_integrable := ?_
        decay_atBot := ?_
        decay_atTop := ?_ }
    · simpa only [mul_assoc, mul_comm, mul_left_comm] using
        integrable_mul_weight H.hkpos (cub_mul hr hrxx)
    · rw [show (fun x : ℝ =>
          (deriv (localizingWeightAt k x₀) x * r t x +
            localizingWeightAt k x₀ x * rx t x) * rx t x) =
          fun x => (r t x * rx t x) * deriv (localizingWeightAt k x₀) x +
            (rx t x * rx t x) * localizingWeightAt k x₀ x by
          funext x; ring]
      exact (integrable_mul_weightDeriv H.hkpos (cub_mul hr hrx)).add
        (integrable_mul_weight H.hkpos (cub_mul hrx hrx))
    · have hraw := tendsto_bounded_mul_zero (cub_mul hr hrx).2
          (localizingWeightAt_tendsto_atBot_zero H.hkpos x₀)
      convert hraw using 1
      funext x
      ring
    · have hraw := tendsto_bounded_mul_zero (cub_mul hr hrx).2
          (localizingWeightAt_tendsto_atTop_zero H.hkpos x₀)
      convert hraw using 1
      funext x
      ring
  have hresolverData : ChiOneWeightedResolverData k x₀
      (fun x => u t x - 1) (r t) (rx t) (rxx t) := by
    refine
      { hk0 := H.hkpos.le
        resolver := H.resolver t
        ibp := hresolverIBP
        sourceSquare_integrable := ?_
        signalSquare_integrable := ?_
        gradientSquare_integrable := ?_
        secondSquare_integrable := ?_
        weightCross_integrable := ?_
        sourceSignal_integrable := ?_ }
    · simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using
        integrable_mul_weight H.hkpos (cub_mul hsource hsource)
    · simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using
        integrable_mul_weight H.hkpos (cub_mul hr hr)
    · simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using
        integrable_mul_weight H.hkpos (cub_mul hrx hrx)
    · simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using
        integrable_mul_weight H.hkpos (cub_mul hrxx hrxx)
    · simpa only [mul_assoc, mul_comm, mul_left_comm] using
        integrable_mul_weightDeriv H.hkpos (cub_mul hr hrx)
    · simpa only [mul_assoc, mul_comm, mul_left_comm] using
        integrable_mul_weight H.hkpos (cub_mul hsource hr)
  have hdiffusionIBP : WholeLineIBPData
      (fun x => localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u t x))
      (fun x => deriv (localizingWeightAt k x₀) x *
          chiOneEntropyMultiplier (u t x) +
        localizingWeightAt k x₀ x * (ux t x / (u t x) ^ 2))
      (ux t) (uxx t) := by
    refine
      { hasDerivAt_left := fun x _ => by
          have hraw := (hasDerivAt_localizingWeightAt k x₀ x).mul
            (chiOneEntropyMultiplier_comp_hasDerivAt
              (H.u_space_deriv t x) (hupos x).ne')
          simpa only [deriv_localizingWeightAt, div_eq_mul_inv] using hraw
        hasDerivAt_right := fun x _ => H.ux_space_deriv t x
        left_integrable := ?_
        right_integrable := ?_
        decay_atBot := ?_
        decay_atTop := ?_ }
    · simpa only [mul_assoc, mul_comm, mul_left_comm] using
        integrable_mul_weight H.hkpos (cub_mul hmult huxx)
    · rw [show (fun x : ℝ =>
          (deriv (localizingWeightAt k x₀) x *
              chiOneEntropyMultiplier (u t x) +
            localizingWeightAt k x₀ x * (ux t x / (u t x) ^ 2)) * ux t x) =
          fun x => (chiOneEntropyMultiplier (u t x) * ux t x) *
              deriv (localizingWeightAt k x₀) x +
            ((ux t x / (u t x) ^ 2) * ux t x) *
              localizingWeightAt k x₀ x by
          funext x; ring]
      exact (integrable_mul_weightDeriv H.hkpos (cub_mul hmult hux)).add
        (integrable_mul_weight H.hkpos (cub_mul huxOverUSq hux))
    · have hraw := tendsto_bounded_mul_zero (cub_mul hmult hux).2
          (localizingWeightAt_tendsto_atBot_zero H.hkpos x₀)
      convert hraw using 1
      funext x
      ring
    · have hraw := tendsto_bounded_mul_zero (cub_mul hmult hux).2
          (localizingWeightAt_tendsto_atTop_zero H.hkpos x₀)
      convert hraw using 1
      funext x
      ring
  have hdriftIBP : WholeLineIBPData
      (localizingWeightAt k x₀)
      (fun x => deriv (localizingWeightAt k x₀) x)
      (fun x => chiOneRelativeEntropy (u t x))
      (fun x => chiOneEntropyMultiplier (u t x) * ux t x) := by
    refine
      { hasDerivAt_left := fun x _ => by
          simpa only [deriv_localizingWeightAt] using
            hasDerivAt_localizingWeightAt k x₀ x
        hasDerivAt_right := fun x _ =>
          (chiOneRelativeEntropy_hasDerivAt (hupos x).ne').comp x
            (H.u_space_deriv t x)
        left_integrable := ?_
        right_integrable := ?_
        decay_atBot := ?_
        decay_atTop := ?_ }
    · simpa only [mul_assoc, mul_comm, mul_left_comm] using
        integrable_mul_weight H.hkpos (cub_mul hmult hux)
    · simpa only [mul_assoc, mul_comm, mul_left_comm] using
        integrable_mul_weightDeriv H.hkpos hent
    · have hraw := tendsto_bounded_mul_zero hent.2
          (localizingWeightAt_tendsto_atBot_zero H.hkpos x₀)
      simpa only [mul_comm] using hraw
    · have hraw := tendsto_bounded_mul_zero hent.2
          (localizingWeightAt_tendsto_atTop_zero H.hkpos x₀)
      simpa only [mul_comm] using hraw
  have huRx : IsCUnifBdd (fun x => u t x * rx t x) := cub_mul hu hrx
  have hchemDeriv : IsCUnifBdd
      (fun x => ux t x * rx t x + u t x * rxx t x) :=
    cub_add (cub_mul hux hrx) (cub_mul hu hrxx)
  have hchemotaxisIBP : WholeLineIBPData
      (fun x => localizingWeightAt k x₀ x * chiOneEntropyMultiplier (u t x))
      (fun x => deriv (localizingWeightAt k x₀) x *
          chiOneEntropyMultiplier (u t x) +
        localizingWeightAt k x₀ x * (ux t x / (u t x) ^ 2))
      (fun x => u t x * rx t x)
      (fun x => ux t x * rx t x + u t x * rxx t x) := by
    refine
      { hasDerivAt_left := fun x _ => by
          have hraw := (hasDerivAt_localizingWeightAt k x₀ x).mul
            (chiOneEntropyMultiplier_comp_hasDerivAt
              (H.u_space_deriv t x) (hupos x).ne')
          simpa only [deriv_localizingWeightAt, div_eq_mul_inv] using hraw
        hasDerivAt_right := fun x _ =>
          (H.u_space_deriv t x).mul (H.rx_space_deriv t x)
        left_integrable := ?_
        right_integrable := ?_
        decay_atBot := ?_
        decay_atTop := ?_ }
    · simpa only [mul_assoc, mul_comm, mul_left_comm] using
        integrable_mul_weight H.hkpos (cub_mul hmult hchemDeriv)
    · rw [show (fun x : ℝ =>
          (deriv (localizingWeightAt k x₀) x *
              chiOneEntropyMultiplier (u t x) +
            localizingWeightAt k x₀ x * (ux t x / (u t x) ^ 2)) *
              (u t x * rx t x)) =
          fun x => (chiOneEntropyMultiplier (u t x) * (u t x * rx t x)) *
              deriv (localizingWeightAt k x₀) x +
            ((ux t x / (u t x) ^ 2) * (u t x * rx t x)) *
              localizingWeightAt k x₀ x by
          funext x; ring]
      exact (integrable_mul_weightDeriv H.hkpos (cub_mul hmult huRx)).add
        (integrable_mul_weight H.hkpos (cub_mul huxOverUSq huRx))
    · have hraw := tendsto_bounded_mul_zero (cub_mul hmult huRx).2
          (localizingWeightAt_tendsto_atBot_zero H.hkpos x₀)
      convert hraw using 1
      funext x
      ring
    · have hraw := tendsto_bounded_mul_zero (cub_mul hmult huRx).2
          (localizingWeightAt_tendsto_atTop_zero H.hkpos x₀)
      convert hraw using 1
      funext x
      ring
  refine
    { toChiOneWeightedResolverData := hresolverData
      hchi := H.hchi
      hk1 := H.hk1
      hell := H.hell
      u_floor := hfloor
      population_pde := H.population_pde t
      diffusion_ibp := hdiffusionIBP
      drift_ibp := hdriftIBP
      chemotaxis_ibp := hchemotaxisIBP
      production_integrable := ?_
      logGradient_integrable := ?_
      mainCross_integrable := ?_
      diffusionFlux_integrable := ?_
      driftFlux_integrable := ?_
      chemotaxisFlux_integrable := ?_
      reaction_integrable := ?_ }
  · simpa only [mul_assoc, mul_comm, mul_left_comm] using
      integrable_mul_weight H.hkpos (cub_mul hmult hut)
  · simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using
      integrable_mul_weight H.hkpos (cub_mul huxOverU huxOverU)
  · simpa only [mul_assoc, mul_comm, mul_left_comm] using
      integrable_mul_weight H.hkpos (cub_mul huxOverU hrx)
  · simpa only [mul_assoc, mul_comm, mul_left_comm] using
      integrable_mul_weightDeriv H.hkpos (cub_mul hmult hux)
  · simpa only [mul_assoc, mul_comm, mul_left_comm] using
      integrable_mul_weightDeriv H.hkpos hent
  · simpa only [mul_assoc, mul_comm, mul_left_comm] using
      integrable_mul_weightDeriv H.hkpos (cub_mul hsource hrx)
  · have hreaction : IsCUnifBdd
        (fun x => chiOneEntropyMultiplier (u t x) *
          (u t x * (1 - u t x))) := by
      exact cub_mul hmult (cub_mul hu (cub_sub (isCUnifBdd_const 1) hu))
    simpa only [mul_assoc, mul_comm, mul_left_comm] using
      integrable_mul_weight H.hkpos hreaction

theorem entropy_integrable (t : ℝ) : Integrable
    (fun x => localizingWeightAt k x₀ x * chiOneRelativeEntropy (u t x)) := by
  obtain ⟨hu, _hux, _huxx, _hut, _hr, _hrx, _hrxx⟩ := H.slice_cub t
  have hent := cub_relativeEntropy_of_floor H.hell (H.u_floor t) hu
  simpa only [mul_comm] using integrable_mul_weight H.hkpos hent

/-- Uniform boundedness and the positive floor justify differentiation of the
weighted entropy integral on the entire time axis. -/
theorem entropy_hasDerivAt (t : ℝ) :
    HasDerivAt (chiOneWeightedEntropyEnergy k x₀ u)
      (chiOneWeightedEntropyProduction k x₀ (u t) (ut t)) t := by
  obtain ⟨C, hC0, hbound⟩ := H.uniform_bound
  let F : ℝ → ℝ → ℝ := fun s x =>
    localizingWeightAt k x₀ x * chiOneRelativeEntropy (u s x)
  let F' : ℝ → ℝ → ℝ := fun s x =>
    localizingWeightAt k x₀ x *
      chiOneEntropyMultiplier (u s x) * ut s x
  let D : ℝ := (1 + ell⁻¹) * C
  let major : ℝ → ℝ := fun x => D * localizingWeightAt k x₀ x
  have hD0 : 0 ≤ D := by
    dsimp only [D]
    exact mul_nonneg (add_nonneg zero_le_one (inv_nonneg.mpr H.hell.le)) hC0
  have hmajor : Integrable major := by
    dsimp only [major]
    exact (localizingWeightAt_integrable H.hkpos x₀).const_mul D
  have hFmeas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (F s) volume := by
    filter_upwards with s
    obtain ⟨hu, _hux, _huxx, _hut, _hr, _hrx, _hrxx⟩ := H.slice_cub s
    have hent := cub_relativeEntropy_of_floor H.hell (H.u_floor s) hu
    exact (continuous_localizingWeightAt.mul hent.1).aestronglyMeasurable
  have hF'meas : AEStronglyMeasurable (F' t) volume := by
    obtain ⟨hu, _hux, _huxx, hut, _hr, _hrx, _hrxx⟩ := H.slice_cub t
    have hmult := cub_entropyMultiplier_of_floor H.hell (H.u_floor t) hu
    exact ((continuous_localizingWeightAt.mul hmult.1).mul hut.1).aestronglyMeasurable
  have hderivBound : ∀ᵐ x ∂volume, ∀ s ∈ (Set.univ : Set ℝ),
      ‖F' s x‖ ≤ major x := by
    filter_upwards with x
    intro s _hs
    have huspos : 0 < u s x := H.hell.trans_le (H.u_floor s x)
    have hinv : |(u s x)⁻¹| ≤ ell⁻¹ := by
      rw [abs_of_pos (inv_pos.mpr huspos)]
      exact (inv_le_inv₀ huspos H.hell).2 (H.u_floor s x)
    have hmult : |chiOneEntropyMultiplier (u s x)| ≤ 1 + ell⁻¹ := by
      unfold chiOneEntropyMultiplier
      exact (abs_sub 1 (u s x)⁻¹).trans <| by
        simpa only [abs_one] using add_le_add (le_refl 1) hinv
    have hut := (hbound s x).2.2.2.1
    have hproduct :
        |chiOneEntropyMultiplier (u s x)| * |ut s x| ≤ D := by
      dsimp only [D]
      exact mul_le_mul hmult hut (abs_nonneg _) (by
        exact add_nonneg zero_le_one (inv_nonneg.mpr H.hell.le))
    dsimp only [F', major]
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_pos (localizingWeightAt_pos k x₀ x)]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_of_nonneg_left hproduct (localizingWeightAt_pos k x₀ x).le
  have hdiff : ∀ᵐ x ∂volume, ∀ s ∈ (Set.univ : Set ℝ),
      HasDerivAt (fun q => F q x) (F' s x) s := by
    filter_upwards with x
    intro s _hs
    have hchain :=
      (chiOneRelativeEntropy_hasDerivAt
        (H.hell.trans_le (H.u_floor s x)).ne').comp s (H.u_time_deriv s x)
    have hconst : HasDerivAt
        (fun _q : ℝ => localizingWeightAt k x₀ x) 0 s :=
      hasDerivAt_const s _
    simpa only [F, F', zero_mul, zero_add, mul_assoc] using hconst.mul hchain
  have hraw :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (bound := major) (F := F) (F' := F')
      (x₀ := t) (s := (Set.univ : Set ℝ)) Filter.univ_mem
      hFmeas (H.entropy_integrable t) hF'meas hderivBound hmajor hdiff).2
  simpa only [F, F', chiOneWeightedEntropyEnergy,
    chiOneWeightedEntropyProduction] using hraw

/-- A bounded entire classical solution automatically carries the full
entropy certificate consumed by the sharp Liouville theorem. -/
theorem to_entireWeightedEntropyData :
    ChiOneEntireWeightedEntropyData chi c ell k x₀
      u ux uxx ut r rx rxx := by
  refine
    { hkpos := H.hkpos
      slice := H.weightedEntropyData
      entropy_integrable := H.entropy_integrable
      entropy_deriv := H.entropy_hasDerivAt
      u_continuous := H.u_continuous
      band := ?_ }
  obtain ⟨C, hC0, hbound⟩ := H.uniform_bound
  refine ⟨C + 1, by linarith, ?_⟩
  intro t x
  exact (abs_sub (u t x) 1).trans <| by
    simpa only [abs_one] using add_le_add (hbound t x).1 (le_refl 1)

section AxiomAudit

#print axioms ChiOneEntireBoundedClassicalData.weightedEntropyData
#print axioms ChiOneEntireBoundedClassicalData.entropy_hasDerivAt
#print axioms ChiOneEntireBoundedClassicalData.to_entireWeightedEntropyData

end AxiomAudit

end ChiOneEntireBoundedClassicalData

end ShenWork.Paper1
