/-
  ShenWork/Paper2/IntervalSingleSolutionL2Window.lean

  Single-solution L² half-energy and the H¹ sliding-window frontier.

  The time-Leibniz identity is derived from the landed localized
  under-integral theorem, through `IntervalDomainL2HalfEnergyTimeLeibniz`.

  The final window theorem integrates the carried absorbing L² differential
  inequality over `[τ-1, τ]`, uses the seed frontier for FTC, and converts the
  diffusion dissipation into `H1energy`.
-/
import ShenWork.Paper2.IntervalChiNegH1Energy
import ShenWork.PDE.IntervalDomain
import ShenWork.PDE.IntervalDomainAPrioriGlobal
import ShenWork.PDE.IntervalUnderIntegralLeibniz
import ShenWork.Paper2.Statements
import ShenWork.Paper2.IntervalDomainL2HalfEnergyTimeLeibniz

noncomputable section

open scoped BigOperators Topology
open MeasureTheory
open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalDomain)
open ShenWork.Paper2 (IsPaper2ClassicalSolution)
open ShenWork.Paper2.IntervalChiNegH1Energy (H1energy)
open ShenWork.Paper2.IntervalDomainEnergyStep
  (intervalDomainDerivativePairIntegral intervalDomainL2DiffusionDissipation
    intervalDomainL2HalfEnergy)
open ShenWork.Paper2.IntervalDomainLpMonotonicity
  (intervalDomainLpAbsEnergy)
open ShenWork.IntervalDomainExistence
  (IntervalDomainL2AbsorbingDifferentialInequalityResult
    IntervalDomainL2SeedRegularityFrontier
    intervalDomainL2DiffusionDissipation_nonneg
    intervalDomainL2LogisticSinkIntegral_nonneg)

namespace ShenWork.Paper2.IntervalSingleSolutionL2Window

/-- The single-solution L² half-energy on the interval. -/
def L2energy (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ x in (0 : ℝ)..1, (intervalDomainLift (u t) x) ^ 2

/-- The local definition agrees with the repository's existing half-energy. -/
theorem L2energy_eq_intervalDomainL2HalfEnergy
    (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ) :
    L2energy u t = intervalDomainL2HalfEnergy u t := by
  unfold L2energy intervalDomainL2HalfEnergy intervalDomain
  change (1 / 2 : ℝ) *
      (∫ x in (0 : ℝ)..1, (intervalDomainLift (u t) x) ^ 2)
    = (1 / 2 : ℝ) * ShenWork.IntervalDomain.intervalDomainIntegral
        (fun x : intervalDomainPoint => (u t x) ^ 2)
  unfold ShenWork.IntervalDomain.intervalDomainIntegral
  congr 1
  exact intervalIntegral.integral_congr (fun x _ => by
    rw [ShenWork.Paper2.intervalDomainLift_sq])

/-- The absolute `p = 2` energy is twice the local half-energy on nonnegative
classical slices. -/
theorem intervalDomainLpAbsEnergy_two_eq_two_mul_L2energy_of_nonneg
    (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ)
    (hu_nonneg : ∀ x : intervalDomainPoint, 0 ≤ u t x) :
    intervalDomainLpAbsEnergy 2 u t = 2 * L2energy u t := by
  unfold intervalDomainLpAbsEnergy L2energy intervalDomain
  change ShenWork.IntervalDomain.intervalDomainIntegral
        (fun x : intervalDomainPoint => |u t x| ^ (2 : ℝ)) =
      2 * ((1 / 2 : ℝ) *
        ∫ x in (0 : ℝ)..1, (intervalDomainLift (u t) x) ^ 2)
  unfold ShenWork.IntervalDomain.intervalDomainIntegral
  have hcongr :
      (∫ x in (0 : ℝ)..1,
          intervalDomainLift
            (fun y : intervalDomainPoint => |u t y| ^ (2 : ℝ)) x) =
        ∫ x in (0 : ℝ)..1, (intervalDomainLift (u t) x) ^ 2 := by
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    unfold intervalDomainLift
    rw [dif_pos hx, dif_pos hx]
    simp [abs_of_nonneg (hu_nonneg ⟨x, hx⟩)]
  rw [hcongr]
  ring

/-- The L² diffusion dissipation is exactly twice the `H1energy`. -/
theorem intervalDomainL2DiffusionDissipation_eq_two_mul_H1energy
    (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ) :
    intervalDomainL2DiffusionDissipation u t = 2 * H1energy u t := by
  unfold intervalDomainL2DiffusionDissipation intervalDomainDerivativePairIntegral
    H1energy
  have hcongr :
      (∫ x in (0 : ℝ)..1,
          deriv (intervalDomainLift (u t)) x *
            deriv (intervalDomainLift (u t)) x) =
        ∫ x in (0 : ℝ)..1, (deriv (intervalDomainLift (u t)) x) ^ 2 := by
    exact intervalIntegral.integral_congr (fun _ _ => by ring)
  rw [hcongr]
  ring

/-- Absolute `p = 2` interval-domain energy is nonnegative. -/
theorem intervalDomainLpAbsEnergy_two_nonneg
    (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ) :
    0 ≤ intervalDomainLpAbsEnergy 2 u t := by
  unfold intervalDomainLpAbsEnergy intervalDomain ShenWork.IntervalDomain.intervalDomainIntegral
  refine intervalIntegral.integral_nonneg (by norm_num) (fun x hx => ?_)
  unfold intervalDomainLift
  rw [dif_pos hx]
  exact Real.rpow_nonneg (abs_nonneg (u t ⟨x, hx⟩)) 2

/-- The integrand derivative field is the requested pointwise product. -/
theorem intervalDomainHalfEnergyIntegrandDeriv_eq
    (u : ℝ → intervalDomainPoint → ℝ) (t x : ℝ) :
    ShenWork.Paper2.intervalDomainHalfEnergyIntegrandDeriv u t x
      = intervalDomainLift (u t) x *
          deriv (fun s => intervalDomainLift (u s) x) t := by
  rfl

/--
Leibniz differentiation under the integral for the single-solution L²
half-energy:

`d/dt (1/2 ∫ u(t,x)^2 dx) = ∫ u(t,x) u_t(t,x) dx`.
-/
theorem singleSolution_L2energy_hasDerivAt
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {τ : ℝ} (hτ0 : 0 < τ) (hτT : τ < T) :
    HasDerivAt (L2energy u)
      (∫ x in (0 : ℝ)..1,
        intervalDomainLift (u τ) x *
          deriv (fun s => intervalDomainLift (u s) x) τ) τ := by
  have hτ : τ ∈ Set.Ioo (0 : ℝ) T := ⟨hτ0, hτT⟩
  obtain ⟨δ, hδ, hball, hIcc⟩ :=
    ShenWork.Paper2.exists_closedSlab_subset hτ
  have hjoint :=
    ShenWork.Paper2.intervalDomainHalfEnergyIntegrandDeriv_continuousOn_of_regularity
      hsol
  have hslab : ContinuousOn
      (Function.uncurry
        (ShenWork.Paper2.intervalDomainHalfEnergyIntegrandDeriv u))
      (Set.Icc (τ - δ) (τ + δ) ×ˢ Set.Icc (0 : ℝ) 1) :=
    hjoint.mono (Set.prod_mono hIcc (le_refl _))
  have hderiv_slice : ContinuousOn
      (ShenWork.Paper2.intervalDomainHalfEnergyIntegrandDeriv u τ)
      (Set.Icc (0 : ℝ) 1) :=
    ShenWork.Paper2.intervalDomain_continuousOn_timeSlice hjoint hτ
  have hF'_meas : AEStronglyMeasurable
      (ShenWork.Paper2.intervalDomainHalfEnergyIntegrandDeriv u τ)
      ShenWork.Paper2.IntervalDomainLpMonotonicity.intervalDomainInteriorMeasure :=
    (hderiv_slice.mono Set.Ioo_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioo
  have hint_slice : ContinuousOn
      (ShenWork.Paper2.intervalDomainHalfEnergyIntegrand u τ)
      (Set.Icc (0 : ℝ) 1) :=
    ShenWork.Paper2.intervalDomainHalfEnergyIntegrand_continuousOn_timeSlice
      hsol hτ
  have hF_int : IntervalIntegrable
      (ShenWork.Paper2.intervalDomainHalfEnergyIntegrand u τ)
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le (zero_le_one)]
  have hF_meas : ∀ᶠ s in 𝓝 τ,
      AEStronglyMeasurable
        (ShenWork.Paper2.intervalDomainHalfEnergyIntegrand u s)
        ShenWork.Paper2.IntervalDomainLpMonotonicity.intervalDomainInteriorMeasure := by
    filter_upwards [isOpen_Ioo.mem_nhds hτ] with s hs
    exact
      ((ShenWork.Paper2.intervalDomainHalfEnergyIntegrand_continuousOn_timeSlice
        hsol hs).mono Set.Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  have hHD :=
    ShenWork.Paper2.intervalDomainL2HalfEnergy_hasDerivAt_of_slabContinuous
      hsol hδ hball hF_meas hF_int hF'_meas hslab
  have hfun : L2energy u = fun s => intervalDomainL2HalfEnergy u s := by
    funext s
    exact L2energy_eq_intervalDomainL2HalfEnergy u s
  have hval :
      (∫ x in (0 : ℝ)..1,
        ShenWork.Paper2.intervalDomainHalfEnergyIntegrandDeriv u τ x)
        =
      ∫ x in (0 : ℝ)..1,
        intervalDomainLift (u τ) x *
          deriv (fun s => intervalDomainLift (u s) x) τ := by
    exact intervalIntegral.integral_congr (fun x _ => by
      rw [intervalDomainHalfEnergyIntegrandDeriv_eq])
  rw [hval] at hHD
  rw [hfun]
  exact hHD

/--
Sliding-window H¹ dissipation bound from a carried uniform L² bound.

This is the intended paper-level consumer: once the single-solution integrated
L² absorbing differential inequality and the seed regularity frontier are
available, it gives the uniform one-unit H¹ window estimate.
-/
theorem singleSolution_H1_window_bound
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (habsorbing : IntervalDomainL2AbsorbingDifferentialInequalityResult p T u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    {Y_L2 : ℝ} (hL2 : ∀ τ, 0 < τ → τ < T → L2energy u τ ≤ Y_L2) :
    ∃ C, 0 ≤ C ∧ ∀ τ, 1 ≤ τ → τ < T →
      ∫ s in (τ - 1)..τ, H1energy u s ≤ C := by
  rcases habsorbing with ⟨delta, K, hdelta_pos, hK_nonneg, habs⟩
  rcases hfrontier.initialBound with ⟨δ0, hδ0_nonneg, hinit⟩
  let Y : ℝ → ℝ := fun t => intervalDomainLpAbsEnergy 2 u t
  let B : ℝ := max (2 * Y_L2) δ0
  let C : ℝ := (K + B) / (2 * delta)
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact le_trans hδ0_nonneg (le_max_right (2 * Y_L2) δ0)
  have hcoef_pos : 0 < 2 * delta := by positivity
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact div_nonneg (add_nonneg hK_nonneg hB_nonneg) hcoef_pos.le
  refine ⟨C, hC_nonneg, ?_⟩
  intro τ hτ1 hτT
  let a : ℝ := τ - 1
  let b : ℝ := τ
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have ha0 : 0 ≤ a := by dsimp [a]; linarith
  have hbT : b ≤ T := by dsimp [b]; exact le_of_lt hτT
  have hcont_ab : ContinuousOn Y (Set.Icc a b) :=
    hfrontier.energyContinuous.mono
      (fun r hr => ⟨le_trans ha0 hr.1, le_trans hr.2 hbT⟩)
  have hY_deriv_le :
      ∀ r ∈ Set.Ioo a b, deriv Y r ≤ K := by
    intro r hr
    have hr0 : 0 < r := lt_of_le_of_lt ha0 hr.1
    have hrT : r < T := lt_of_lt_of_le hr.2 hbT
    have hD_nonneg :
        0 ≤ delta * intervalDomainL2DiffusionDissipation u r := by
      exact mul_nonneg hdelta_pos.le
        (intervalDomainL2DiffusionDissipation_nonneg u r)
    have hS_nonneg :
        0 ≤ p.b * intervalDomain.integral
          (fun x : intervalDomain.Point => (u r x) ^ (2 + p.α)) := by
      exact mul_nonneg p.hb
        (intervalDomainL2LogisticSinkIntegral_nonneg hsol hr0 hrT)
    have halign :
        deriv Y r = 2 * deriv (fun τ => intervalDomainL2HalfEnergy u τ) r := by
      exact hfrontier.derivativeAlignment r ⟨le_of_lt hr0, hrT⟩
    have hmain := habs r hr0 hrT
    dsimp [Y] at halign
    nlinarith
  have hY_deriv_int :
      IntervalIntegrable (fun r => deriv Y r) MeasureTheory.volume a b := by
    let F : ℝ → ℝ := fun r => K * r - Y r
    have hFcont : ContinuousOn F (Set.Icc a b) := by
      exact (continuousOn_const.mul continuousOn_id).sub hcont_ab
    have hFderiv :
        ∀ r ∈ Set.Ioo a b,
          HasDerivWithinAt F (K - deriv Y r) (Set.Ioi r) r := by
      intro r hr
      have hr0 : 0 < r := lt_of_le_of_lt ha0 hr.1
      have hrT : r < T := lt_of_lt_of_le hr.2 hbT
      have hYder :=
        (hfrontier.energyHasDerivWithin r ⟨le_of_lt hr0, hrT⟩).Ioi_of_Ici
      have hKder :
          HasDerivWithinAt (fun s : ℝ => K * s) K (Set.Ioi r) r :=
        ((hasDerivAt_const r K).mul (hasDerivAt_id' r)).hasDerivWithinAt.congr_deriv
          (by ring)
      exact hKder.sub hYder
    have hFprime_nonneg :
        ∀ r ∈ Set.Ioo a b, 0 ≤ K - deriv Y r := by
      intro r hr
      exact sub_nonneg.mpr (hY_deriv_le r hr)
    have hFprime_on :
        MeasureTheory.IntegrableOn (fun r => K - deriv Y r) (Set.Ioc a b)
          MeasureTheory.volume :=
      intervalIntegral.integrableOn_deriv_right_of_nonneg hFcont hFderiv hFprime_nonneg
    have hFprime_interval :
        IntervalIntegrable (fun r => K - deriv Y r) MeasureTheory.volume a b := by
      constructor
      · exact hFprime_on
      · have hempty : Set.Ioc b a = ∅ := Set.Ioc_eq_empty (not_lt.mpr hab)
        rw [hempty]
        exact MeasureTheory.integrableOn_empty
    have hconst_int : IntervalIntegrable (fun _ : ℝ => K) MeasureTheory.volume a b :=
      intervalIntegral.intervalIntegrable_const
    have hsub_int := hconst_int.sub hFprime_interval
    convert hsub_int using 1
    ext r
    ring
  have hFTC :
      ∫ r in a..b, deriv Y r = Y b - Y a := by
    refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hcont_ab ?_
      hY_deriv_int
    intro r hr
    have hr0 : 0 < r := lt_of_le_of_lt ha0 hr.1
    have hrT : r < T := lt_of_lt_of_le hr.2 hbT
    exact (hfrontier.energyHasDerivWithin r ⟨le_of_lt hr0, hrT⟩).Ioi_of_Ici
  have hright_int :
      IntervalIntegrable (fun r => K - deriv Y r) MeasureTheory.volume a b := by
    exact intervalIntegral.intervalIntegrable_const.sub hY_deriv_int
  have hright_eval :
      ∫ r in a..b, K - deriv Y r = K - (Y b - Y a) := by
    rw [intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_const hY_deriv_int,
      intervalIntegral.integral_const, hFTC]
    dsimp [a, b]
    ring
  have hYa_bound : Y a ≤ B := by
    rcases lt_or_eq_of_le hτ1 with hτ_gt | hτ_eq
    · have ha_pos : 0 < a := by dsimp [a]; linarith
      have haT : a < T := by dsimp [a]; linarith
      have hY_eq : Y a = 2 * L2energy u a := by
        dsimp [Y]
        exact intervalDomainLpAbsEnergy_two_eq_two_mul_L2energy_of_nonneg u a
          (fun x => le_of_lt (hsol.u_pos' ha_pos haT : 0 < u a x))
      have hL2a := hL2 a ha_pos haT
      dsimp [B]
      rw [hY_eq]
      exact le_trans (mul_le_mul_of_nonneg_left hL2a (by norm_num : (0 : ℝ) ≤ 2))
        (le_max_left (2 * Y_L2) δ0)
    · have ha_eq_zero : a = 0 := by dsimp [a]; linarith
      dsimp [B]
      rw [ha_eq_zero]
      exact le_trans hinit (le_max_right (2 * Y_L2) δ0)
  have hYb_nonneg : 0 ≤ Y b := by
    dsimp [Y]
    exact intervalDomainLpAbsEnergy_two_nonneg u b
  by_cases hH1_int :
      IntervalIntegrable (fun s => H1energy u s) MeasureTheory.volume a b
  · have hleft_int :
        IntervalIntegrable (fun r => (2 * delta) * H1energy u r)
          MeasureTheory.volume a b :=
      hH1_int.const_mul (2 * delta)
    have hpoint :
        ∀ r ∈ Set.Ioo a b,
          (2 * delta) * H1energy u r ≤ K - deriv Y r := by
      intro r hr
      have hr0 : 0 < r := lt_of_le_of_lt ha0 hr.1
      have hrT : r < T := lt_of_lt_of_le hr.2 hbT
      have hS_nonneg :
          0 ≤ p.b * intervalDomain.integral
            (fun x : intervalDomain.Point => (u r x) ^ (2 + p.α)) := by
        exact mul_nonneg p.hb
          (intervalDomainL2LogisticSinkIntegral_nonneg hsol hr0 hrT)
      have halign :
          deriv Y r = 2 * deriv (fun τ => intervalDomainL2HalfEnergy u τ) r := by
        exact hfrontier.derivativeAlignment r ⟨le_of_lt hr0, hrT⟩
      have hD_eq :=
        intervalDomainL2DiffusionDissipation_eq_two_mul_H1energy u r
      have hmain := habs r hr0 hrT
      dsimp [Y] at halign
      nlinarith
    have hmono :
        ∫ r in a..b, (2 * delta) * H1energy u r ≤
          ∫ r in a..b, K - deriv Y r :=
      intervalIntegral.integral_mono_on_of_le_Ioo hab hleft_int hright_int hpoint
    rw [hright_eval] at hmono
    rw [intervalIntegral.integral_const_mul] at hmono
    have hscaled :
        (2 * delta) * ∫ s in a..b, H1energy u s ≤ K + B := by
      nlinarith
    have hbound :
        ∫ s in a..b, H1energy u s ≤ C := by
      dsimp [C]
      have hscaled' :
          (∫ s in a..b, H1energy u s) * (2 * delta) ≤ K + B := by
        nlinarith [hscaled]
      exact (le_div_iff₀ hcoef_pos).2 hscaled'
    simpa [a, b] using hbound
  · have hzero :
        ∫ s in a..b, H1energy u s = 0 :=
      intervalIntegral.integral_undef hH1_int
    rw [hzero]
    simpa [a, b, C] using hC_nonneg

end ShenWork.Paper2.IntervalSingleSolutionL2Window

end
