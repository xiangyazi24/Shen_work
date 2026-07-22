import ShenWork.Paper1.WholeLineChiLargeNonnegativeEnergy
import ShenWork.Paper1.WholeLineLocalMomentEnergyProducer

/-!
# Concrete nonnegative local-moment energy producer
-/

open Filter MeasureTheory Real Set Topology
open scoped Topology

noncomputable section

namespace ShenWork.Paper1

private theorem largeChi_localMoment_isCUnifBdd_mul
    {f g : ℝ → ℝ} (hf : IsCUnifBdd f) (hg : IsCUnifBdd g) :
    IsCUnifBdd (fun x => f x * g x) := by
  rcases hf.2 with ⟨A, hA⟩
  rcases hg.2 with ⟨B, hB⟩
  have hA0 : 0 ≤ A := (abs_nonneg (f 0)).trans (hA 0)
  have hB0 : 0 ≤ B := (abs_nonneg (g 0)).trans (hB 0)
  refine ⟨hf.1.mul hg.1, ⟨A * B, fun x => ?_⟩⟩
  rw [abs_mul]
  exact mul_le_mul (hA x) (hB x) (abs_nonneg _) hA0

private theorem largeChi_localMoment_isCUnifBdd_add
    {f g : ℝ → ℝ} (hf : IsCUnifBdd f) (hg : IsCUnifBdd g) :
    IsCUnifBdd (fun x => f x + g x) := by
  rcases hf.2 with ⟨A, hA⟩
  rcases hg.2 with ⟨B, hB⟩
  refine ⟨hf.1.add hg.1, ⟨A + B, fun x => ?_⟩⟩
  exact (abs_add_le (f x) (g x)).trans (add_le_add (hA x) (hB x))

private theorem largeChi_localMoment_isCUnifBdd_const_mul
    (c : ℝ) {f : ℝ → ℝ} (hf : IsCUnifBdd f) :
    IsCUnifBdd (fun x => c * f x) := by
  rcases hf.2 with ⟨A, hA⟩
  refine ⟨continuous_const.mul hf.1, ⟨|c| * A, fun x => ?_⟩⟩
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hA x) (abs_nonneg c)

private theorem largeChi_localMoment_isCUnifBdd_rpow
    {f : ℝ → ℝ} (hf : IsCUnifBdd f) (hf0 : ∀ x, 0 ≤ f x)
    {q : ℝ} (hq : 0 ≤ q) :
    IsCUnifBdd (fun x => (f x) ^ q) := by
  rcases hf.2 with ⟨A, hA⟩
  have hA0 : 0 ≤ A := (abs_nonneg (f 0)).trans (hA 0)
  refine ⟨(Real.continuous_rpow_const hq).comp hf.1,
    ⟨A ^ q, fun x => ?_⟩⟩
  rw [abs_of_nonneg (Real.rpow_nonneg (hf0 x) q)]
  exact Real.rpow_le_rpow (hf0 x)
    ((le_abs_self (f x)).trans (hA x)) hq

private theorem largeChi_localMoment_integrable_mul_weight
    {κ x₀ : ℝ} (hκ : 0 < κ) {f : ℝ → ℝ}
    (hf : IsCUnifBdd f) :
    Integrable (fun x => f x * localizingWeightAt κ x₀ x) := by
  rcases hf.2 with ⟨C, hC⟩
  have hC0 : 0 ≤ C := (abs_nonneg (f 0)).trans (hC 0)
  have hmajor : Integrable (fun x => C * localizingWeightAt κ x₀ x) :=
    (localizingWeightAt_integrable hκ x₀).const_mul C
  refine Integrable.mono' hmajor
    (hf.1.mul continuous_localizingWeightAt).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_pos (localizingWeightAt_pos κ x₀ x)]
  have hmajor_nonneg : 0 ≤ C * localizingWeightAt κ x₀ x :=
    mul_nonneg hC0 (localizingWeightAt_pos κ x₀ x).le
  exact mul_le_mul_of_nonneg_right (hC x)
    (localizingWeightAt_pos κ x₀ x).le

private theorem largeChi_largeChi_localMoment_integrable_mul_weightDeriv
    {κ x₀ : ℝ} (hκ : 0 < κ) {f : ℝ → ℝ}
    (hf : IsCUnifBdd f) :
    Integrable (fun x => f x * deriv (localizingWeightAt κ x₀) x) := by
  rcases hf.2 with ⟨C, hC⟩
  have hC0 : 0 ≤ C := (abs_nonneg (f 0)).trans (hC 0)
  have hmajor : Integrable
      (fun x => (C * κ) * localizingWeightAt κ x₀ x) :=
    (localizingWeightAt_integrable hκ x₀).const_mul (C * κ)
  have hwcont : Continuous (deriv (localizingWeightAt κ x₀)) := by
    simpa [iteratedDeriv_one] using
      (contDiff_two_localizingWeightAt κ x₀).continuous_iteratedDeriv 1 (by norm_num)
  refine Integrable.mono' hmajor (hf.1.mul hwcont).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have hleft := mul_le_mul (hC x)
    (abs_deriv_localizingWeightAt_le hκ.le x₀ x)
    (abs_nonneg _) hC0
  have hmajor_nonneg : 0 ≤ (C * κ) * localizingWeightAt κ x₀ x := by
    exact mul_nonneg (mul_nonneg hC0 hκ.le)
      (localizingWeightAt_pos κ x₀ x).le
  simpa [mul_assoc] using hleft

private theorem largeChi_largeChi_localMoment_integrable_mul_weightSecond
    {κ x₀ : ℝ} (hκ : 0 < κ) {f : ℝ → ℝ}
    (hf : IsCUnifBdd f) :
    Integrable
      (fun x => f x * iteratedDeriv 2 (localizingWeightAt κ x₀) x) := by
  rcases hf.2 with ⟨C, hC⟩
  have hC0 : 0 ≤ C := (abs_nonneg (f 0)).trans (hC 0)
  have hmajor : Integrable
      (fun x => (C * (κ + κ ^ 2)) * localizingWeightAt κ x₀ x) :=
    (localizingWeightAt_integrable hκ x₀).const_mul (C * (κ + κ ^ 2))
  have hwcont : Continuous (iteratedDeriv 2 (localizingWeightAt κ x₀)) :=
    (contDiff_two_localizingWeightAt κ x₀).continuous_iteratedDeriv 2 (by norm_num)
  refine Integrable.mono' hmajor (hf.1.mul hwcont).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have hleft := mul_le_mul (hC x)
    (abs_iteratedDeriv_two_localizingWeightAt_le hκ.le x₀ x)
    (abs_nonneg _) hC0
  have hmajor_nonneg :
      0 ≤ (C * (κ + κ ^ 2)) * localizingWeightAt κ x₀ x := by
    exact mul_nonneg
      (mul_nonneg hC0 (add_nonneg hκ.le (sq_nonneg κ)))
      (localizingWeightAt_pos κ x₀ x).le
  simpa [mul_assoc] using hleft

private theorem largeChi_localMoment_tendsto_mul_zero_of_bounded
    {l : Filter ℝ} {f g : ℝ → ℝ} (hf : IsBddFun f)
    (hg : Tendsto g l (nhds 0)) :
    Tendsto (fun x => f x * g x) l (nhds 0) := by
  rcases hf with ⟨C, hC⟩
  have hC0 : 0 ≤ C := (abs_nonneg (f 0)).trans (hC 0)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (g := fun x => C * ‖g x‖)
    (Eventually.of_forall fun x => norm_nonneg _)
    (Eventually.of_forall fun x => ?_) ?_
  · rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg (g x))
  · simpa using tendsto_const_nhds.mul hg.norm

private theorem largeChi_deriv_localizingWeightAt_tendsto_atTop_zero
    {κ : ℝ} (hκ : 0 < κ) (x₀ : ℝ) :
    Tendsto (deriv (localizingWeightAt κ x₀)) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero'
    (g := fun x => κ * localizingWeightAt κ x₀ x)
    (Eventually.of_forall fun x => norm_nonneg _)
    (Eventually.of_forall fun x => ?_) ?_
  · simpa [Real.norm_eq_abs] using
      abs_deriv_localizingWeightAt_le hκ.le x₀ x
  · simpa using tendsto_const_nhds.mul
      (localizingWeightAt_tendsto_atTop_zero hκ x₀)

private theorem largeChi_deriv_localizingWeightAt_tendsto_atBot_zero
    {κ : ℝ} (hκ : 0 < κ) (x₀ : ℝ) :
    Tendsto (deriv (localizingWeightAt κ x₀)) atBot (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero'
    (g := fun x => κ * localizingWeightAt κ x₀ x)
    (Eventually.of_forall fun x => norm_nonneg _)
    (Eventually.of_forall fun x => ?_) ?_
  · simpa [Real.norm_eq_abs] using
      abs_deriv_localizingWeightAt_le hκ.le x₀ x
  · simpa using tendsto_const_nhds.mul
      (localizingWeightAt_tendsto_atBot_zero hκ x₀)

/-! ## Generic fixed-time assembler -/

/-- Assemble all four whole-line IBP packages and all weighted integrability
fields from positive `C²` slices with bounded values and first two
derivatives. -/

noncomputable def wholeLineLocalMomentNonnegativeEnergyData_of_bounded_contDiff_two
    {p : CMParams} {P κ T t x₀ : ℝ} {u v : ℝ → ℝ → ℝ}
    {Cu Cux Cuxx Cv Cvx Cvxx : ℝ}
    (hP : 1 < P) (hPtwo : 2 ≤ P) (hκ : 0 < κ)
    (ht0 : 0 < t) (htT : t < T)
    (hsol : IsClassicalSolution p T u v)
    (hu_nonneg : ∀ x, 0 ≤ u t x)
    (htime : WholeLineLocalMomentTimeData P κ t x₀ u
      (fun s x => deriv (fun r => u r x) s))
    (hu2 : ContDiff ℝ 2 (u t)) (hv2 : ContDiff ℝ 2 (v t))
    (hu_bdd : ∀ x, |u t x| ≤ Cu)
    (hux_bdd : ∀ x, |deriv (u t) x| ≤ Cux)
    (huxx_bdd : ∀ x, |iteratedDeriv 2 (u t) x| ≤ Cuxx)
    (hv_bdd : ∀ x, |v t x| ≤ Cv)
    (hvx_bdd : ∀ x, |deriv (v t) x| ≤ Cvx)
    (hvxx_bdd : ∀ x, |iteratedDeriv 2 (v t) x| ≤ Cvxx) :
    WholeLineLocalMomentNonnegativeEnergyData p P κ T t x₀ u v := by
  let U : ℝ → ℝ := u t
  let V : ℝ → ℝ := v t
  have hU0 : ∀ x, 0 ≤ U x := by simpa [U] using hu_nonneg
  have hU : IsCUnifBdd U :=
    ⟨by simpa [U] using hu2.continuous, ⟨Cu, by simpa [U] using hu_bdd⟩⟩
  have hUxcont : Continuous (deriv U) := by
    simpa [U, iteratedDeriv_one] using
      hu2.continuous_iteratedDeriv 1 (by norm_num)
  have hUxxcont : Continuous (iteratedDeriv 2 U) := by
    simpa [U] using hu2.continuous_iteratedDeriv 2 (by norm_num)
  have hUx : IsCUnifBdd (deriv U) :=
    ⟨hUxcont, ⟨Cux, by simpa [U] using hux_bdd⟩⟩
  have hUxx : IsCUnifBdd (iteratedDeriv 2 U) :=
    ⟨hUxxcont, ⟨Cuxx, by simpa [U] using huxx_bdd⟩⟩
  have hV : IsCUnifBdd V :=
    ⟨by simpa [V] using hv2.continuous, ⟨Cv, by simpa [V] using hv_bdd⟩⟩
  have hVxcont : Continuous (deriv V) := by
    simpa [V, iteratedDeriv_one] using
      hv2.continuous_iteratedDeriv 1 (by norm_num)
  have hVxxcont : Continuous (iteratedDeriv 2 V) := by
    simpa [V] using hv2.continuous_iteratedDeriv 2 (by norm_num)
  have hVx : IsCUnifBdd (deriv V) :=
    ⟨hVxcont, ⟨Cvx, by simpa [V] using hvx_bdd⟩⟩
  have hVxx : IsCUnifBdd (iteratedDeriv 2 V) :=
    ⟨hVxxcont, ⟨Cvxx, by simpa [V] using hvxx_bdd⟩⟩
  have hPm1 : 0 ≤ P - 1 := by linarith
  have hPm2m : 0 ≤ P + p.m - 2 := by linarith [p.hm]
  have hPmp1 : 0 ≤ P + p.m - 1 := by linarith [p.hm]
  have hPalpha : 0 ≤ P + p.α := by linarith [p.hα]
  have hPmGamma : 0 ≤ P + p.m + p.γ - 1 := by
    linarith [p.hm, p.hγ]
  have hUPm1 : IsCUnifBdd (fun x => (U x) ^ (P - 1)) :=
    largeChi_localMoment_isCUnifBdd_rpow hU hU0 hPm1
  have hUP : IsCUnifBdd (fun x => (U x) ^ P) :=
    largeChi_localMoment_isCUnifBdd_rpow hU hU0 (by linarith)
  have hUPm2m : IsCUnifBdd (fun x => (U x) ^ (P + p.m - 2)) :=
    largeChi_localMoment_isCUnifBdd_rpow hU hU0 hPm2m
  have hUPmp1 : IsCUnifBdd (fun x => (U x) ^ (P + p.m - 1)) :=
    largeChi_localMoment_isCUnifBdd_rpow hU hU0 hPmp1
  have hUPalpha : IsCUnifBdd (fun x => (U x) ^ (P + p.α)) :=
    largeChi_localMoment_isCUnifBdd_rpow hU hU0 hPalpha
  have hUPmGamma :
      IsCUnifBdd (fun x => (U x) ^ (P + p.m + p.γ - 1)) :=
    largeChi_localMoment_isCUnifBdd_rpow hU hU0 hPmGamma
  have hUm : IsCUnifBdd (fun x => (U x) ^ p.m) :=
    largeChi_localMoment_isCUnifBdd_rpow hU hU0 (by linarith [p.hm])
  have hUm1 : IsCUnifBdd (fun x => (U x) ^ (p.m - 1)) :=
    largeChi_localMoment_isCUnifBdd_rpow hU hU0 (by linarith [p.hm])
  let flux : ℝ → ℝ := wholeLineLocalChemotaxisFlux p u v t
  have hflux : IsCUnifBdd flux := by
    simpa [flux, wholeLineLocalChemotaxisFlux, U, V] using
      largeChi_localMoment_isCUnifBdd_mul hUm hVx
  let fluxDerivValue : ℝ → ℝ := fun x =>
    p.m * (U x) ^ (p.m - 1) * deriv U x * deriv V x +
      (U x) ^ p.m * iteratedDeriv 2 V x
  have hfluxDerivValue : IsCUnifBdd fluxDerivValue := by
    dsimp only [fluxDerivValue]
    exact largeChi_localMoment_isCUnifBdd_add
      (largeChi_localMoment_isCUnifBdd_mul
        (largeChi_localMoment_isCUnifBdd_mul
          (largeChi_localMoment_isCUnifBdd_const_mul p.m hUm1) hUx) hVx)
      (largeChi_localMoment_isCUnifBdd_mul hUm hVxx)
  have hU_has : ∀ x, HasDerivAt U (deriv U x) x := by
    intro x
    exact (hu2.differentiable (by norm_num) x).hasDerivAt
  have hVx_has : ∀ x,
      HasDerivAt (deriv V) (iteratedDeriv 2 V x) x := by
    intro x
    have hraw :=
      (hv2.differentiable_iteratedDeriv 1 (by norm_num)).differentiableAt.hasDerivAt
        (x := x)
    simpa [V, iteratedDeriv_one, iteratedDeriv_succ,
      iteratedDeriv_zero] using hraw
  have hflux_has : ∀ x, HasDerivAt flux (fluxDerivValue x) x := by
    intro x
    have hpow := (hU_has x).rpow_const (p := p.m) (Or.inr p.hm)
    have hprod := hpow.mul (hVx_has x)
    have hbase : HasDerivAt flux
        (deriv U x * p.m * (U x) ^ (p.m - 1) * deriv V x +
          (U x) ^ p.m * iteratedDeriv 2 V x) x := by
      simpa only [flux, wholeLineLocalChemotaxisFlux, U, V, Pi.mul_apply]
        using hprod
    convert hbase using 1
    dsimp only [fluxDerivValue]
    ring
  have hfluxDerivEq : deriv flux = fluxDerivValue := by
    funext x
    exact (hflux_has x).deriv
  have hfluxDeriv : IsCUnifBdd (deriv flux) := by
    rw [hfluxDerivEq]
    exact hfluxDerivValue
  let B₀ : ℝ := Cuxx
  have hB₀ : ∀ x, |iteratedDeriv 2 U x| ≤ B₀ := by
    intro x
    simpa [B₀, U] using huxx_bdd x
  have hB₀0 : 0 ≤ B₀ := (abs_nonneg (iteratedDeriv 2 U 0)).trans (hB₀ 0)
  let B : ℝ := B₀ + 1
  have hB : 0 < B := by dsimp [B]; linarith
  have hsecond : ∀ x, |iteratedDeriv 2 U x| ≤ B := fun x => by
    dsimp [B]
    linarith [hB₀ x]
  have hDiss : Integrable (fun x : ℝ =>
      (U x) ^ (P - 2) * (deriv U x) ^ 2 *
        localizingWeightAt κ x₀ x) := by
    have hmajor :=
      (largeChi_localMoment_integrable_mul_weight (x₀ := x₀) hκ hUPm1).const_mul (4 * B)
    have htargetCont : Continuous (fun x : ℝ =>
        (U x) ^ (P - 2) * (deriv U x) ^ 2 *
          localizingWeightAt κ x₀ x) := by
      exact ((hu2.continuous.rpow_const
        (fun _ => Or.inr (sub_nonneg.mpr hPtwo))).mul
          (hUxcont.pow 2)).mul continuous_localizingWeightAt
    refine Integrable.mono' hmajor htargetCont.aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    have hgl := localMoment_deriv_sq_le hu2 hU0 hB hsecond x
    have hpow_nonneg : 0 ≤ (U x) ^ (P - 2) :=
      Real.rpow_nonneg (hU0 x) _
    have hcombine : (U x) ^ (P - 2) * U x = (U x) ^ (P - 1) := by
      calc
        (U x) ^ (P - 2) * U x =
            (U x) ^ (P - 2) * (U x) ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = (U x) ^ ((P - 2) + 1) := by
          rw [← Real.rpow_add_of_nonneg (hU0 x)
            (sub_nonneg.mpr hPtwo) (by norm_num)]
        _ = (U x) ^ (P - 1) := by ring_nf
    have hcore : (U x) ^ (P - 2) * (deriv U x) ^ 2 ≤
        4 * B * (U x) ^ (P - 1) := by
      calc
        (U x) ^ (P - 2) * (deriv U x) ^ 2 ≤
            (U x) ^ (P - 2) * (4 * B * U x) :=
          mul_le_mul_of_nonneg_left hgl hpow_nonneg
        _ = 4 * B * (U x) ^ (P - 1) := by rw [← hcombine]; ring
    have hw0 := (localizingWeightAt_pos κ x₀ x).le
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (mul_nonneg (Real.rpow_nonneg (hU0 x) _) (sq_nonneg _)) hw0)]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcore hw0

  have hDiffWeight : Integrable (fun x : ℝ =>
      (U x) ^ (P - 1) * deriv U x *
        deriv (localizingWeightAt κ x₀) x) := by
    simpa [mul_assoc] using largeChi_largeChi_localMoment_integrable_mul_weightDeriv hκ
      (largeChi_localMoment_isCUnifBdd_mul hUPm1 hUx)
  have hWeightSecond : Integrable (fun x : ℝ =>
      (U x) ^ P * iteratedDeriv 2 (localizingWeightAt κ x₀) x) :=
    largeChi_largeChi_localMoment_integrable_mul_weightSecond hκ hUP
  have hFirstCross : Integrable (fun x : ℝ =>
      (U x) ^ (P + p.m - 2) * deriv U x * deriv V x *
        localizingWeightAt κ x₀ x) := by
    simpa [mul_assoc] using largeChi_localMoment_integrable_mul_weight hκ
      (largeChi_localMoment_isCUnifBdd_mul
        (largeChi_localMoment_isCUnifBdd_mul hUPm2m hUx) hVx)
  have hMoment : Integrable (fun x : ℝ =>
      (U x) ^ P * localizingWeightAt κ x₀ x) :=
    largeChi_localMoment_integrable_mul_weight hκ hUP
  have hLogistic : Integrable (fun x : ℝ =>
      (U x) ^ (P + p.α) * localizingWeightAt κ x₀ x) :=
    largeChi_localMoment_integrable_mul_weight hκ hUPalpha
  have hHigh : Integrable (fun x : ℝ =>
      (U x) ^ (P + p.m + p.γ - 1) *
        localizingWeightAt κ x₀ x) :=
    largeChi_localMoment_integrable_mul_weight hκ hUPmGamma
  have hSignal : Integrable (fun x : ℝ =>
      (U x) ^ (P + p.m - 1) * V x *
        localizingWeightAt κ x₀ x) := by
    simpa [mul_assoc] using largeChi_localMoment_integrable_mul_weight hκ
      (largeChi_localMoment_isCUnifBdd_mul hUPmp1 hV)
  have hSignalSecond : Integrable (fun x : ℝ =>
      (U x) ^ (P + p.m - 1) * iteratedDeriv 2 V x *
        localizingWeightAt κ x₀ x) := by
    simpa [mul_assoc] using largeChi_localMoment_integrable_mul_weight hκ
      (largeChi_localMoment_isCUnifBdd_mul hUPmp1 hVxx)
  have hSignalWeight : Integrable (fun x : ℝ =>
      (U x) ^ (P + p.m - 1) * deriv V x *
        deriv (localizingWeightAt κ x₀) x) := by
    simpa [mul_assoc] using largeChi_largeChi_localMoment_integrable_mul_weightDeriv hκ
      (largeChi_localMoment_isCUnifBdd_mul hUPmp1 hVx)
  have hAbsVx : IsCUnifBdd (fun x => |deriv V x|) := by
    refine ⟨hVxcont.abs, ?_⟩
    rcases hVx.2 with ⟨C, hC⟩
    exact ⟨C, fun x => by simpa only [abs_abs] using hC x⟩
  have hSignalAbs : Integrable (fun x : ℝ =>
      (U x) ^ (P + p.m - 1) * |deriv V x| *
        localizingWeightAt κ x₀ x) := by
    simpa [mul_assoc] using largeChi_localMoment_integrable_mul_weight hκ
      (largeChi_localMoment_isCUnifBdd_mul hUPmp1 hAbsVx)

  have hUderiv_has : ∀ x,
      HasDerivAt (deriv U) (iteratedDeriv 2 U x) x := by
    intro x
    have hraw :=
      (hu2.differentiable_iteratedDeriv 1 (by norm_num)).differentiableAt.hasDerivAt
        (x := x)
    simpa [U, iteratedDeriv_one, iteratedDeriv_succ,
      iteratedDeriv_zero] using hraw
  have htest_has : ∀ x,
      HasDerivAt (wholeLineLocalLpTest P κ u t x₀)
        (wholeLineLocalLpTestDeriv P κ u t x₀ x) x := by
    intro x
    exact hasDerivAt_wholeLineLocalLpTest_of_nonneg hPtwo
      (by simpa [U] using hU_has x)
  have hnormalizedPower_has : ∀ x,
      HasDerivAt (fun y : ℝ => (1 / P) * (U y) ^ P)
        ((U x) ^ (P - 1) * deriv U x) x := by
    intro x
    have hraw := ((hU_has x).rpow_const (p := P)
      (Or.inr hP.le)).const_mul (1 / P)
    convert hraw using 1
    field_simp [ne_of_gt (lt_trans zero_lt_one hP)] <;> ring
  have hweightDeriv_has : ∀ x,
      HasDerivAt (deriv (localizingWeightAt κ x₀))
        (iteratedDeriv 2 (localizingWeightAt κ x₀) x) x := by
    intro x
    have hraw := hasDerivAt_deriv_localizingWeightAt_actual κ x₀ x
    convert hraw using 1
    rw [iteratedDeriv_two_localizingWeightAt]
  have hchemPower_has : ∀ x,
      HasDerivAt (fun y : ℝ => (U y) ^ (P + p.m - 1))
        ((P + p.m - 1) * (U x) ^ (P + p.m - 2) * deriv U x) x := by
    intro x
    simpa [U] using
      hasDerivAt_wholeLineLocalChemotaxisPower_of_nonneg
        (p := p) (P := P) (t := t) (u := u) hPtwo
          (by simpa [U] using hU_has x)
  have hsignalWeight_has : ∀ x,
      HasDerivAt
        (fun y : ℝ => deriv V y * localizingWeightAt κ x₀ y)
        (iteratedDeriv 2 V x * localizingWeightAt κ x₀ x +
          deriv V x * deriv (localizingWeightAt κ x₀) x) x := by
    intro x
    simpa [V] using
      hasDerivAt_signalGradient_mul_localizingWeightAt
        (κ := κ) (t := t) (x₀ := x₀) (v := v)
          (by simpa [V] using hVx_has x)

  have hDiffusion : WholeLineIBPData
      (wholeLineLocalLpTest P κ u t x₀)
      (wholeLineLocalLpTestDeriv P κ u t x₀)
      (deriv (u t)) (iteratedDeriv 2 (u t)) := by
    refine
      { hasDerivAt_left := fun x _ => htest_has x
        hasDerivAt_right := fun x _ => by simpa [U] using hUderiv_has x
        left_integrable := ?_
        right_integrable := ?_
        decay_atBot := ?_
        decay_atTop := ?_ }
    · have hraw := largeChi_localMoment_integrable_mul_weight (x₀ := x₀) hκ
        (largeChi_localMoment_isCUnifBdd_mul hUPm1 hUxx)
      simpa [wholeLineLocalLpTest, U, mul_assoc, mul_comm, mul_left_comm] using hraw
    · rw [show (fun x : ℝ =>
          wholeLineLocalLpTestDeriv P κ u t x₀ x * deriv (u t) x) =
          fun x => (P - 1) *
              ((U x) ^ (P - 2) * (deriv U x) ^ 2 *
                localizingWeightAt κ x₀ x) +
            (U x) ^ (P - 1) * deriv U x *
              deriv (localizingWeightAt κ x₀) x by
        funext x
        simp only [wholeLineLocalLpTestDeriv, U]
        ring]
      exact (hDiss.const_mul (P - 1)).add hDiffWeight
    · have hraw := largeChi_localMoment_tendsto_mul_zero_of_bounded
        (largeChi_localMoment_isCUnifBdd_mul hUPm1 hUx).2
        (localizingWeightAt_tendsto_atBot_zero hκ x₀)
      convert hraw using 1
      funext x
      simp only [wholeLineLocalLpTest, U]
      ring
    · have hraw := largeChi_localMoment_tendsto_mul_zero_of_bounded
        (largeChi_localMoment_isCUnifBdd_mul hUPm1 hUx).2
        (localizingWeightAt_tendsto_atTop_zero hκ x₀)
      convert hraw using 1
      funext x
      simp only [wholeLineLocalLpTest, U]
      ring

  have hDiffusionWeight : WholeLineIBPData
      (fun x : ℝ => (1 / P) * (u t x) ^ P)
      (fun x : ℝ => (u t x) ^ (P - 1) * deriv (u t) x)
      (deriv (localizingWeightAt κ x₀))
      (iteratedDeriv 2 (localizingWeightAt κ x₀)) := by
    let F : ℝ → ℝ := fun x => (1 / P) * (U x) ^ P
    have hF : IsCUnifBdd F := by
      simpa [F] using largeChi_localMoment_isCUnifBdd_const_mul (1 / P) hUP
    refine
      { hasDerivAt_left := fun x _ => by simpa [F, U] using hnormalizedPower_has x
        hasDerivAt_right := fun x _ => hweightDeriv_has x
        left_integrable := ?_
        right_integrable := ?_
        decay_atBot := ?_
        decay_atTop := ?_ }
    · simpa [F, U, mul_assoc] using
        largeChi_largeChi_localMoment_integrable_mul_weightSecond hκ hF
    · simpa [U] using hDiffWeight
    · have hraw := largeChi_localMoment_tendsto_mul_zero_of_bounded hF.2
        (largeChi_deriv_localizingWeightAt_tendsto_atBot_zero hκ x₀)
      simpa [F, U] using hraw
    · have hraw := largeChi_localMoment_tendsto_mul_zero_of_bounded hF.2
        (largeChi_deriv_localizingWeightAt_tendsto_atTop_zero hκ x₀)
      simpa [F, U] using hraw

  have hChemotaxisFirst : WholeLineIBPData
      (wholeLineLocalLpTest P κ u t x₀)
      (wholeLineLocalLpTestDeriv P κ u t x₀)
      (wholeLineLocalChemotaxisFlux p u v t)
      (deriv (wholeLineLocalChemotaxisFlux p u v t)) := by
    refine
      { hasDerivAt_left := fun x _ => htest_has x
        hasDerivAt_right := fun x _ => by
          simpa [flux] using
            (hflux_has x).congr_deriv (hflux_has x).deriv.symm
        left_integrable := ?_
        right_integrable := ?_
        decay_atBot := ?_
        decay_atTop := ?_ }
    · have hraw := largeChi_localMoment_integrable_mul_weight (x₀ := x₀) hκ
        (largeChi_localMoment_isCUnifBdd_mul hUPm1 hfluxDeriv)
      simpa [wholeLineLocalLpTest, flux, U, mul_assoc, mul_comm, mul_left_comm] using hraw
    · rw [show (fun x : ℝ =>
          wholeLineLocalLpTestDeriv P κ u t x₀ x *
            wholeLineLocalChemotaxisFlux p u v t x) =
          fun x => (P - 1) *
              ((U x) ^ (P + p.m - 2) * deriv U x * deriv V x *
                localizingWeightAt κ x₀ x) +
            (U x) ^ (P + p.m - 1) * deriv V x *
              deriv (localizingWeightAt κ x₀) x by
        funext x
        simpa [U, V] using
          wholeLineLocalLpTestDeriv_mul_flux_of_nonneg
            (p := p) (P := P) (κ := κ) (t := t) (x₀ := x₀)
              (u := u) (v := v) hPtwo (hu_nonneg x)]
      exact (hFirstCross.const_mul (P - 1)).add hSignalWeight
    · have hraw := largeChi_localMoment_tendsto_mul_zero_of_bounded
        (largeChi_localMoment_isCUnifBdd_mul hUPm1 hflux).2
        (localizingWeightAt_tendsto_atBot_zero hκ x₀)
      convert hraw using 1
      funext x
      simp only [wholeLineLocalLpTest, flux, U]
      ring
    · have hraw := largeChi_localMoment_tendsto_mul_zero_of_bounded
        (largeChi_localMoment_isCUnifBdd_mul hUPm1 hflux).2
        (localizingWeightAt_tendsto_atTop_zero hκ x₀)
      convert hraw using 1
      funext x
      simp only [wholeLineLocalLpTest, flux, U]
      ring

  have hChemotaxisSecond : WholeLineIBPData
      (fun x : ℝ => (u t x) ^ (P + p.m - 1))
      (fun x : ℝ => (P + p.m - 1) *
        (u t x) ^ (P + p.m - 2) * deriv (u t) x)
      (fun x : ℝ => deriv (v t) x * localizingWeightAt κ x₀ x)
      (fun x : ℝ => iteratedDeriv 2 (v t) x *
          localizingWeightAt κ x₀ x +
        deriv (v t) x * deriv (localizingWeightAt κ x₀) x) := by
    refine
      { hasDerivAt_left := fun x _ => by simpa [U] using hchemPower_has x
        hasDerivAt_right := fun x _ => by simpa [V] using hsignalWeight_has x
        left_integrable := ?_
        right_integrable := ?_
        decay_atBot := ?_
        decay_atTop := ?_ }
    · rw [show (fun x : ℝ =>
          (u t x) ^ (P + p.m - 1) *
            (iteratedDeriv 2 (v t) x * localizingWeightAt κ x₀ x +
              deriv (v t) x * deriv (localizingWeightAt κ x₀) x)) =
          fun x =>
            (U x) ^ (P + p.m - 1) * iteratedDeriv 2 V x *
              localizingWeightAt κ x₀ x +
            (U x) ^ (P + p.m - 1) * deriv V x *
              deriv (localizingWeightAt κ x₀) x by
        funext x
        simp only [U, V]
        ring]
      exact hSignalSecond.add hSignalWeight
    · rw [show (fun x : ℝ =>
          ((P + p.m - 1) * (u t x) ^ (P + p.m - 2) *
            deriv (u t) x) *
            (deriv (v t) x * localizingWeightAt κ x₀ x)) =
          fun x => (P + p.m - 1) *
            ((U x) ^ (P + p.m - 2) * deriv U x * deriv V x *
              localizingWeightAt κ x₀ x) by
        funext x
        simp only [U, V]
        ring]
      exact hFirstCross.const_mul (P + p.m - 1)
    · have hraw := largeChi_localMoment_tendsto_mul_zero_of_bounded
        (largeChi_localMoment_isCUnifBdd_mul hUPmp1 hVx).2
        (localizingWeightAt_tendsto_atBot_zero hκ x₀)
      convert hraw using 1
      funext x
      simp only [U, V]
      ring
    · have hraw := largeChi_localMoment_tendsto_mul_zero_of_bounded
        (largeChi_localMoment_isCUnifBdd_mul hUPmp1 hVx).2
        (localizingWeightAt_tendsto_atTop_zero hκ x₀)
      convert hraw using 1
      funext x
      simp only [U, V]
      ring

  exact
    { hP := hP
      hPtwo := hPtwo
      hκ := hκ
      ht0 := ht0
      htT := htT
      solution := hsol
      u_nonnegative := hu_nonneg
      time := htime
      diffusion := hDiffusion
      diffusionWeight := hDiffusionWeight
      chemotaxisFirst := hChemotaxisFirst
      chemotaxisSecond := hChemotaxisSecond
      diffusion_dissipation_integrable := by simpa [U] using hDiss
      diffusion_weightCross_integrable := by simpa [U] using hDiffWeight
      weightSecond_integrable := by simpa [U] using hWeightSecond
      chemotaxis_firstCross_integrable := by simpa [U, V] using hFirstCross
      moment_integrable := by simpa [U] using hMoment
      logistic_integrable := by simpa [U] using hLogistic
      chemotaxis_high_integrable := by simpa [U] using hHigh
      signal_integrable := by simpa [U, V] using hSignal
      signal_secondDerivative_integrable := by simpa [U, V] using hSignalSecond
      signal_weightCross_integrable := by simpa [U, V] using hSignalWeight
      signal_gradient_abs_integrable := by simpa [U, V] using hSignalAbs }

/-! ## Canonical mild-solution producer -/

/-- A strictly positive interior slice of the canonical mild solution supplies
the complete local-moment energy package. -/

noncomputable def wholeLineCauchyBUCMildFixedPoint_localMomentNonnegativeEnergyData
    (p : CMParams) {M T P κ t x₀ : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (hP : 1 < P) (hPtwo : 2 ≤ P)
    (hκ : 0 < κ)
    (ht0 : 0 < t) (htT : t < T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M) :
    let Traj := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    let u : ℝ → ℝ → ℝ := fun s x ↦
      (wholeLineBUCTrajectoryExtend hT Traj s).1 x
    let v : ℝ → ℝ → ℝ := fun s ↦ frozenElliptic p (u s)
    WholeLineLocalMomentNonnegativeEnergyData p P κ T t x₀ u v := by
  dsimp only
  let Traj : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let u : ℝ → ℝ → ℝ := fun s x ↦
    (wholeLineBUCTrajectoryExtend hT Traj s).1 x
  let v : ℝ → ℝ → ℝ := fun s ↦ frozenElliptic p (u s)
  have hTpos : 0 < T := ht0.trans htT
  let zt : Set.Icc (0 : ℝ) T := ⟨t, ht0.le, htT.le⟩
  have hext : wholeLineBUCTrajectoryExtend hT Traj t = Traj zt :=
    wholeLineBUCTrajectoryExtend_eq hT Traj zt.2
  have hstripExt : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineBUCTrajectoryExtend hT Traj s).1 x ∈ Set.Icc (0 : ℝ) M := by
    intro s hs x
    rw [wholeLineBUCTrajectoryExtend_eq hT Traj hs]
    exact hstrip ⟨s, hs⟩ x
  have hwindow : ∀ s ∈ Set.Icc (t / 2) t, ∀ x,
      (wholeLineBUCTrajectoryExtend hT Traj s).1 x ∈ Set.Icc (0 : ℝ) M := by
    intro s hs x
    exact hstripExt s
      ⟨(half_pos ht0).le.trans hs.1, hs.2.trans htT.le⟩ x
  let htime := wholeLineCauchyBUCMildFixedPoint_localMomentTimeData
    p (x₀ := x₀) hM hT hP hκ ht0 htT u₀ hsmall hstrip
  have hsol : IsClassicalSolution p T u v := by
    simpa only [u, v, Traj] using
      (wholeLineCauchyBUCMildFixedPoint_isClassicalSolution
        p (theta := (1 / 2 : ℝ)) (eta := (1 / 4 : ℝ))
          hM hTpos u₀ hsmall
          (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) hstrip)
  have hu_nonneg : ∀ x, 0 ≤ u t x := by
    intro x
    simpa only [u, hext] using (hstrip zt x).1
  have hu2slice : ContDiff ℝ 2 (fun x ↦ (Traj zt).1 x) := by
    simpa only [Traj] using
      (wholeLineCauchyBUCMildFixedPoint_slice_contDiff_two_positive
        (theta := (1 / 2 : ℝ)) (eta := (1 / 4 : ℝ))
        p hM hT u₀ hsmall zt ht0
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by simpa only [Traj] using hwindow))
  have hu2 : ContDiff ℝ 2 (u t) := by
    simpa only [u, hext] using hu2slice
  have huC : IsCUnifBdd (u t) := by
    simpa only [u, hext] using WholeLineBUC.isCUnifBdd (Traj zt)
  have huM : ∀ x, u t x ∈ Set.Icc (0 : ℝ) M := by
    intro x
    simpa only [u, hext] using hstrip zt x
  have hu0 : ∀ x, 0 ≤ u t x := fun x ↦ (huM x).1
  have hv2 : ContDiff ℝ 2 (v t) := by
    simpa only [v] using
      frozenElliptic_contDiff_two_of_cunifBdd_nonneg p huC hu0
  have hu_bdd : ∀ x, |u t x| ≤ M := by
    intro x
    rw [abs_of_nonneg (huM x).1]
    exact (huM x).2
  have hstripPoint : ∀ s ∈ Set.Icc t t, ∀ x,
      (wholeLineBUCTrajectoryExtend hT Traj s).1 x ∈ Set.Icc (0 : ℝ) M := by
    intro s hs x
    exact hstripExt s ⟨ht0.le.trans hs.1, hs.2.trans htT.le⟩ x
  have hBxExists :=
    wholeLineCauchyBUCMildFixedPoint_spatial_deriv_bounded_positive_window
      p hM hT ht0 le_rfl htT.le u₀ hsmall
        (theta := (1 / 2 : ℝ)) (eta := (1 / 4 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by simpa only [Traj] using hstripPoint)
  let Bx : ℝ := Classical.choose hBxExists
  have huxBound := (Classical.choose_spec hBxExists).2
  have hux_bdd : ∀ x, |deriv (u t) x| ≤ Bx := by
    intro x
    simpa only [u, Traj] using huxBound t ⟨le_rfl, le_rfl⟩ x
  have hBxxExists :=
    wholeLineCauchyBUCMildFixedPoint_spatial_second_bounded_positive_window
      p hM hT ht0 le_rfl htT.le u₀ hsmall
        (theta := (1 / 2 : ℝ)) (eta := (1 / 4 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by simpa only [Traj] using hwindow)
  let Bxx : ℝ := Classical.choose hBxxExists
  have huxxBound := (Classical.choose_spec hBxxExists).2
  have huxx_bdd : ∀ x, |iteratedDeriv 2 (u t) x| ≤ Bxx := by
    intro x
    simpa only [u, Traj, iteratedDeriv_succ, iteratedDeriv_zero] using
      huxxBound t ⟨le_rfl, le_rfl⟩ x
  have hsource : ∀ x, (u t x) ^ p.γ ≤ M ^ p.γ := by
    intro x
    exact Real.rpow_le_rpow (huM x).1 (huM x).2
      (by linarith [p.hγ])
  have hv_bdd : ∀ x, |v t x| ≤ M ^ p.γ := by
    intro x
    rw [abs_of_nonneg (by simpa only [v] using frozenElliptic_nonneg p hu0 x)]
    simpa only [v] using frozenElliptic_le_of_rpow_le p
      (Real.rpow_nonneg hM p.γ) huC.1 hu0 hsource x
  have hvx_bdd : ∀ x, |deriv (v t) x| ≤ M ^ p.γ := by
    intro x
    simpa only [v] using
      frozenElliptic_deriv_abs_le_rpow_of_Icc p hM huC huM x
  have hvxx_bdd : ∀ x, |iteratedDeriv 2 (v t) x| ≤ 2 * M ^ p.γ := by
    intro x
    change |iteratedDeriv 2 (frozenElliptic p (u t)) x| ≤ 2 * M ^ p.γ
    rw [frozenElliptic_iteratedDeriv_two_eq p huC hu0 x]
    calc
      |frozenElliptic p (u t) x - (u t x) ^ p.γ| ≤
          |frozenElliptic p (u t) x| + |(u t x) ^ p.γ| := abs_sub _ _
      _ ≤ M ^ p.γ + M ^ p.γ := by
        exact add_le_add (by simpa only [v] using hv_bdd x)
          (by rw [abs_of_nonneg (Real.rpow_nonneg (huM x).1 p.γ)]; exact hsource x)
      _ = 2 * M ^ p.γ := by ring
  let H := wholeLineLocalMomentNonnegativeEnergyData_of_bounded_contDiff_two
    (p := p) (P := P) (κ := κ) (T := T) (t := t) (x₀ := x₀)
    (u := u) (v := v) (Cu := M) (Cux := Bx) (Cuxx := Bxx)
    (Cv := M ^ p.γ) (Cvx := M ^ p.γ) (Cvxx := 2 * M ^ p.γ)
    hP hPtwo hκ ht0 htT hsol hu_nonneg htime hu2 hv2
      hu_bdd hux_bdd huxx_bdd hv_bdd hvx_bdd hvxx_bdd
  exact H

section AxiomAudit

#print axioms wholeLineLocalMomentNonnegativeEnergyData_of_bounded_contDiff_two
#print axioms wholeLineCauchyBUCMildFixedPoint_localMomentNonnegativeEnergyData

end AxiomAudit

end ShenWork.Paper1
