import ShenWork.Paper1.WholeLineWeightedRegularityDuhamel
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

open Filter MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace ShenWork.Paper1

/-!
# Canonical weighted `L²` history sections

Pointwise existence of an `L²` representative does not provide a measurable
time history.  This file starts the history bridge with the canonical
square-integrable representative, leaving the genuinely separate measurable
section and Bochner/Fubini lemmas explicit.
-/

def wholeLineRealL2Section
    {ι : Type*}
    (g : ι → ℝ → ℝ)
    (hg_meas : ∀ s, AEStronglyMeasurable (g s) volume)
    (hg2 : ∀ s, Integrable (fun x : ℝ => g s x ^ 2) volume) :
    ι → WholeLineRealL2 :=
  fun s => wholeLineRealL2OfSqIntegrable
    (g s) (hg_meas s) (hg2 s)

theorem wholeLineRealL2Section_coe_ae
    {ι : Type*} (g : ι → ℝ → ℝ)
    (hg_meas : ∀ s, AEStronglyMeasurable (g s) volume)
    (hg2 : ∀ s, Integrable (fun x : ℝ => g s x ^ 2) volume)
    (s : ι) :
    (((wholeLineRealL2Section g hg_meas hg2 s : WholeLineRealL2) : ℝ → ℝ)
      =ᵐ[volume] g s) := by
  exact wholeLineRealL2OfSqIntegrable_coe_ae
    (g s) (hg_meas s) (hg2 s)

theorem wholeLineRealL2Section_norm_sq
    {ι : Type*} (g : ι → ℝ → ℝ)
    (hg_meas : ∀ s, AEStronglyMeasurable (g s) volume)
    (hg2 : ∀ s, Integrable (fun x : ℝ => g s x ^ 2) volume)
    (s : ι) :
    ‖wholeLineRealL2Section g hg_meas hg2 s‖ ^ 2 = ∫ x : ℝ, g s x ^ 2 := by
  exact wholeLineRealL2OfSqIntegrable_norm_sq
    (g s) (hg_meas s) (hg2 s)

/-- The squared distance between two canonical `L²` sections is the concrete
square integral of the difference of their representatives. -/
theorem wholeLineRealL2Section_norm_sub_sq
    {ι : Type*} (g : ι → ℝ → ℝ)
    (hg_meas : ∀ s, AEStronglyMeasurable (g s) volume)
    (hg2 : ∀ s, Integrable (fun x : ℝ => g s x ^ 2) volume)
    (s t : ι) :
    ‖wholeLineRealL2Section g hg_meas hg2 s -
        wholeLineRealL2Section g hg_meas hg2 t‖ ^ 2 =
      ∫ x : ℝ, (g s x - g t x) ^ 2 := by
  let Zs := wholeLineRealL2Section g hg_meas hg2 s
  let Zt := wholeLineRealL2Section g hg_meas hg2 t
  have hrep :
      (((Zs - Zt : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        fun x => g s x - g t x) := by
    filter_upwards [
      Lp.coeFn_sub Zs Zt,
      wholeLineRealL2Section_coe_ae g hg_meas hg2 s,
      wholeLineRealL2Section_coe_ae g hg_meas hg2 t]
      with x hsub hs ht
    rw [hsub]
    simp only [Pi.sub_apply]
    rw [hs, ht]
  have hinner := wholeLineIntegral_mul_eq_inner_of_aeEq
    (Zs - Zt) (Zs - Zt) hrep hrep
  rw [real_inner_self_eq_norm_sq] at hinner
  simpa only [Zs, Zt, pow_two] using hinner.symm

/-- Scalar `L²` convergence of the representatives gives continuity of the
canonical `L²` section.  This is the deterministic replacement for choosing
an unrelated `L²` witness at each time. -/
theorem wholeLineRealL2Section_continuous_of_integral_sub_sq_tendsto_zero
    {g : ℝ → ℝ → ℝ}
    (hg_meas : ∀ s, AEStronglyMeasurable (g s) volume)
    (hg2 : ∀ s, Integrable (fun x : ℝ => g s x ^ 2) volume)
    (hlim : ∀ t, Tendsto
      (fun s => ∫ x : ℝ, (g s x - g t x) ^ 2)
      (nhds t) (nhds 0)) :
    Continuous (wholeLineRealL2Section g hg_meas hg2) := by
  rw [continuous_iff_continuousAt]
  intro t
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp (hlim t)
  have hsqrt0 : Tendsto
      (fun s => Real.sqrt (∫ x : ℝ, (g s x - g t x) ^ 2))
      (nhds t) (nhds 0) := by
    simpa only [Function.comp_apply, Real.sqrt_zero] using hsqrt
  refine hsqrt0.congr' (Eventually.of_forall fun s => ?_)
  rw [← wholeLineRealL2Section_norm_sub_sq g hg_meas hg2]
  exact Real.sqrt_sq (norm_nonneg _)

/-- In particular, scalar `L²` convergence supplies the strong measurability
needed for Bochner integration of the canonical history. -/
theorem wholeLineRealL2Section_aestronglyMeasurable_of_integral_sub_sq_tendsto_zero
    {g : ℝ → ℝ → ℝ}
    (hg_meas : ∀ s, AEStronglyMeasurable (g s) volume)
    (hg2 : ∀ s, Integrable (fun x : ℝ => g s x ^ 2) volume)
    (hlim : ∀ t, Tendsto
      (fun s => ∫ x : ℝ, (g s x - g t x) ^ 2)
      (nhds t) (nhds 0)) :
    AEStronglyMeasurable (wholeLineRealL2Section g hg_meas hg2) volume :=
  (wholeLineRealL2Section_continuous_of_integral_sub_sq_tendsto_zero
    hg_meas hg2 hlim).aestronglyMeasurable

/-- A Bochner integral in the whole-line `L²` space agrees almost everywhere
with the pointwise scalar integral of any representative, provided only local
product integrability on finite-measure spatial windows.  No global spatial
`L¹` hypothesis is imposed. -/
theorem wholeLineRealL2_integral_coe_ae_of_local_prod_integrable
    {ι : Type*} [MeasurableSpace ι]
    {μ : Measure ι} [SigmaFinite μ]
    {Z : ι → WholeLineRealL2} {g : ι → ℝ → ℝ}
    (hZint : Integrable Z μ)
    (hrep : ∀ᵐ s ∂μ,
      (((Z s : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] g s))
    (hlocal : ∀ A : Set ℝ, MeasurableSet A →
      (volume : Measure ℝ) A < ⊤ →
      Integrable
        (fun z : ι × ℝ => A.indicator (g z.1) z.2)
        (μ.prod volume)) :
    ((((∫ s, Z s ∂μ) : WholeLineRealL2) : ℝ → ℝ)
      =ᵐ[volume] fun x => ∫ s, g s x ∂μ) := by
  let H : WholeLineRealL2 := ∫ s, Z s ∂μ
  let h : ℝ → ℝ := fun x => ∫ s, g s x ∂μ
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
  · intro A hA hAfin
    exact integrableOn_Lp_of_measure_ne_top H
      fact_one_le_two_ennreal.elim hAfin.ne
  · intro A hA hAfin
    have hprod := hlocal A hA hAfin
    have hxint : Integrable
        (fun x => ∫ s, A.indicator (g s) x ∂μ) volume :=
      hprod.integral_prod_right
    apply (integrable_indicator_iff hA).mp
    refine hxint.congr ?_
    filter_upwards with x
    by_cases hx : x ∈ A
    · simp only [Set.indicator_of_mem hx]
    · simp only [Set.indicator_of_notMem hx, integral_zero]
  · intro A hA hAfin
    let I : WholeLineRealL2 :=
      indicatorConstLp 2 hA hAfin.ne (1 : ℝ)
    have hinner_integral :
        (⟪I, H⟫ : ℝ) = ∫ s, (⟪I, Z s⟫ : ℝ) ∂μ := by
      dsimp only [H]
      exact ((innerSL ℝ I).integral_comp_comm hZint).symm
    have hinner_rep : ∀ᵐ s ∂μ,
        (⟪I, Z s⟫ : ℝ) = ∫ x in A, g s x := by
      filter_upwards [hrep] with s hs
      have hI := L2.inner_indicatorConstLp_one hA hAfin.ne (Z s)
      rw [show I = indicatorConstLp 2 hA hAfin.ne (1 : ℝ) by rfl]
      refine hI.trans (setIntegral_congr_ae hA ?_)
      filter_upwards [hs] with x hx
      exact fun _ => hx
    have hswap := integral_integral_swap
      (μ := μ) (ν := volume)
      (f := fun s x => A.indicator (g s) x)
      (hlocal A hA hAfin)
    have hswap' :
        (∫ s, ∫ x in A, g s x ∂volume ∂μ) =
          ∫ x in A, ∫ s, g s x ∂μ ∂volume := by
      calc
        (∫ s, ∫ x in A, g s x ∂volume ∂μ) =
            ∫ s, ∫ x, A.indicator (g s) x ∂volume ∂μ := by
          simp only [integral_indicator hA]
        _ = ∫ x, ∫ s, A.indicator (g s) x ∂μ ∂volume := hswap
        _ = ∫ x, A.indicator (fun x => ∫ s, g s x ∂μ) x ∂volume := by
          apply integral_congr_ae
          filter_upwards with x
          by_cases hx : x ∈ A
          · simp only [Set.indicator_of_mem hx]
          · simp only [Set.indicator_of_notMem hx, integral_zero]
        _ = ∫ x in A, ∫ s, g s x ∂μ ∂volume := by
          rw [integral_indicator hA]
    calc
      (∫ x in A, (H : ℝ → ℝ) x) = (⟪I, H⟫ : ℝ) :=
        (L2.inner_indicatorConstLp_one hA hAfin.ne H).symm
      _ = ∫ s, (⟪I, Z s⟫ : ℝ) ∂μ := hinner_integral
      _ = ∫ s, ∫ x in A, g s x ∂volume ∂μ :=
        integral_congr_ae hinner_rep
      _ = ∫ x in A, ∫ s, g s x ∂μ ∂volume := hswap'
      _ = ∫ x in A, h x ∂volume := by rfl

/-- Interval-integral specialization of the local Bochner/Fubini bridge. -/
theorem wholeLineRealL2_intervalIntegral_coe_ae_of_local_prod_integrable
    {a b : ℝ} (hab : a ≤ b)
    {Z : ℝ → WholeLineRealL2} {g : ℝ → ℝ → ℝ}
    (hZint : IntervalIntegrable Z volume a b)
    (hrep : ∀ᵐ s ∂(volume.restrict (Set.Ioc a b)),
      (((Z s : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] g s))
    (hlocal : ∀ A : Set ℝ, MeasurableSet A →
      (volume : Measure ℝ) A < ⊤ →
      Integrable
        (fun z : ℝ × ℝ => A.indicator (g z.1) z.2)
        ((volume.restrict (Set.Ioc a b)).prod volume)) :
    ((((∫ s in a..b, Z s) : WholeLineRealL2) : ℝ → ℝ)
      =ᵐ[volume] fun x => ∫ s in a..b, g s x) := by
  simp_rw [intervalIntegral.integral_of_le hab]
  change
    ((((∫ s, Z s ∂(volume.restrict (Set.Ioc a b))) : WholeLineRealL2) :
        ℝ → ℝ) =ᵐ[volume]
      fun x => ∫ s, g s x ∂(volume.restrict (Set.Ioc a b)))
  exact wholeLineRealL2_integral_coe_ae_of_local_prod_integrable
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hZint)
    hrep hlocal

end ShenWork.Paper1

#print axioms ShenWork.Paper1.wholeLineRealL2Section_coe_ae
#print axioms ShenWork.Paper1.wholeLineRealL2Section_norm_sq
#print axioms ShenWork.Paper1.wholeLineRealL2Section_norm_sub_sq
#print axioms
  ShenWork.Paper1.wholeLineRealL2Section_continuous_of_integral_sub_sq_tendsto_zero
#print axioms
  ShenWork.Paper1.wholeLineRealL2Section_aestronglyMeasurable_of_integral_sub_sq_tendsto_zero
#print axioms
  ShenWork.Paper1.wholeLineRealL2_integral_coe_ae_of_local_prod_integrable
#print axioms
  ShenWork.Paper1.wholeLineRealL2_intervalIntegral_coe_ae_of_local_prod_integrable
