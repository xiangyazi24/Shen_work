/-
  ShenWork/Paper2/IntervalChemFluxHolderFrontier.lean

  Source-side frontier for the chemotaxis differentiated leg.

  The full-kernel second-derivative Duhamel zero-time API consumes a uniform
  spatial `C^θ` modulus for the source family

    `Q(s) = chemFluxLifted p (u s)`.

  This file deliberately packages that source regularity as a frontier assumption.
  It does not prove the nonlinear flux is Hölder and does not mention the downstream
  patched zero-face/headline targets.

-/
import ShenWork.Paper2.IntervalGradientDuhamelMap
import ShenWork.PDE.IntervalFullKernelSecondDerivCtheta

open MeasureTheory
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted)

namespace ShenWork.Paper2

noncomputable section

/-- Source-side frontier: uniform small-time `C^θ` data for the chemotaxis flux
`Q(s) = chemFluxLifted p (u s)`.  This is only a source-regularity package; it does
not assert any downstream zero-face trace or patched derivative convergence. -/
structure ChemFluxCthetaSourceOn
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (T θ CQ HQ : ℝ) : Prop where
  theta_pos : 0 < θ
  theta_lt_one : θ < 1
  CQ_nonneg : 0 ≤ CQ
  HQ_nonneg : 0 ≤ HQ
  flux_meas : Measurable (Function.uncurry (fun s => chemFluxLifted p (u s)))
  flux_int : ∀ s : ℝ, Integrable (chemFluxLifted p (u s)) (intervalMeasure 1)
  flux_bound : ∀ s : ℝ, 0 < s → s ≤ T → ∀ y : ℝ,
    |chemFluxLifted p (u s) y| ≤ CQ
  flux_cont : ∀ s : ℝ, 0 < s → s ≤ T → Continuous (chemFluxLifted p (u s))
  flux_holder : ∀ s : ℝ, 0 < s → s ≤ T →
    ∀ a b : ℝ, a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
      |chemFluxLifted p (u s) a - chemFluxLifted p (u s) b| ≤
        HQ * |a - b| ^ θ

/-- A `ChemFluxCthetaSourceOn` package supplies exactly the per-slice hypotheses
needed by the full-kernel cancellative Hessian estimate. -/
theorem chemFlux_secondDeriv_slice_bound_of_CthetaSourceOn
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {T θ CQ HQ : ℝ}
    (H : ChemFluxCthetaSourceOn p u T θ CQ HQ)
    {s σ x : ℝ} (hs0 : 0 < s) (hsT : s ≤ T)
    (hσ : 0 < σ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |deriv (fun z : ℝ => deriv
        (fun w : ℝ =>
          ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator σ
            (chemFluxLifted p (u s)) w) z) x| ≤
      ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst θ *
        σ ^ (-1 + θ / 2 : ℝ) * HQ :=
  ShenWork.IntervalNeumannFullKernel.neumannHeatSecondDeriv_Ctheta_to_Linfty
    hσ H.theta_pos H.theta_lt_one
    (H.flux_int s).aestronglyMeasurable
    (H.flux_bound s hs0 hsT)
    H.HQ_nonneg
    (H.flux_holder s hs0 hsT)
    hx

/-- Helper for bounding a triple product from absolute-value bounds. -/
private theorem abs_mul_three_le {a b c A B C : ℝ}
    (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    |a * b * c| ≤ A * B * C := by
  rw [abs_mul, abs_mul]
  have hab : |a| * |b| ≤ A * B :=
    mul_le_mul ha hb (abs_nonneg _) hA
  exact mul_le_mul hab hc (abs_nonneg _) (mul_nonneg hA hB)

/-- Pure source algebra: if the three component factors
`u`, `resolverGradReal p u`, and `intervalNeumannResolverR p u` have pointwise
`θ`-Hölder bounds on `[0,1]`, and the resolver value is nonnegative there, then
the nonlinear flux `chemFluxLifted p u` is also `θ`-Hölder.

This is only the algebraic reduction.  It does not produce the component Hölder
data for the resolver. -/
theorem chemFluxLifted_holder_of_component_holder
    {p : CM2Params} {w : intervalDomainPoint → ℝ}
    {θ U G Hu Hg Hv : ℝ}
    (hU_nonneg : 0 ≤ U) (hG_nonneg : 0 ≤ G)
    (hHu_nonneg : 0 ≤ Hu) (hHg_nonneg : 0 ≤ Hg)
    (hu_bound : ∀ x ∈ Set.Icc (0 : ℝ) 1, |intervalDomainLift w x| ≤ U)
    (hg_bound : ∀ x ∈ Set.Icc (0 : ℝ) 1, |resolverGradReal p w x| ≤ G)
    (hR_nonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) x)
    (hu_holder : ∀ a b, a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
      |intervalDomainLift w a - intervalDomainLift w b| ≤ Hu * |a - b| ^ θ)
    (hg_holder : ∀ a b, a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
      |resolverGradReal p w a - resolverGradReal p w b| ≤ Hg * |a - b| ^ θ)
    (hR_holder : ∀ a b, a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
      |intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) a -
          intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) b| ≤
        Hv * |a - b| ^ θ)
    (a b : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    |chemFluxLifted p w a - chemFluxLifted p w b| ≤
      (Hu * G + U * Hg + U * G * p.β * Hv) * |a - b| ^ θ := by
  set ua : ℝ := intervalDomainLift w a with hua
  set ub : ℝ := intervalDomainLift w b with hub
  set ga : ℝ := resolverGradReal p w a with hga
  set gb : ℝ := resolverGradReal p w b with hgb
  set Ra : ℝ := intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) a with hRa
  set Rb : ℝ := intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) b with hRb
  set wa : ℝ := (1 + Ra) ^ (-p.β) with hwa
  set wb : ℝ := (1 + Rb) ^ (-p.β) with hwb
  set r : ℝ := |a - b| ^ θ with hr
  have hr_nonneg : 0 ≤ r := by rw [hr]; exact Real.rpow_nonneg (abs_nonneg _) _
  have hRa_nonneg : 0 ≤ Ra := by rw [hRa]; exact hR_nonneg a ha
  have hRb_nonneg : 0 ≤ Rb := by rw [hRb]; exact hR_nonneg b hb
  have hwa_nonneg : 0 ≤ wa := by rw [hwa]; exact Real.rpow_nonneg (by linarith) _
  have hwa_abs : |wa| ≤ 1 := by
    rw [abs_of_nonneg hwa_nonneg, hwa]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith [p.hβ])
  have hwd : |wa - wb| ≤ p.β * (Hv * r) := by
    have hbase := ShenWork.IntervalChemFluxLipschitz.oneAddRpow_neg_lipschitz
      p.hβ hRa_nonneg hRb_nonneg
    have hR := hR_holder a b ha hb
    rw [← hRa, ← hRb, ← hr] at hR
    rw [hwa, hwb]
    exact hbase.trans (mul_le_mul_of_nonneg_left hR p.hβ)
  have hflux : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      chemFluxLifted p w y =
        intervalDomainLift w y * resolverGradReal p w y *
          (1 + intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) y) ^ (-p.β) := by
    intro y hy
    unfold chemFluxLifted
    rw [Real.rpow_neg (by linarith [hR_nonneg y hy]), div_eq_mul_inv]
  have htel : ua * ga * wa - ub * gb * wb =
      (ua - ub) * ga * wa + ub * (ga - gb) * wa + ub * gb * (wa - wb) := by ring
  have hb1 : |(ua - ub) * ga * wa| ≤ (Hu * r) * G * 1 := by
    refine abs_mul_three_le ?_ ?_ hwa_abs (mul_nonneg hHu_nonneg hr_nonneg) hG_nonneg
    · rw [hua, hub, hr]; exact hu_holder a b ha hb
    · rw [hga]; exact hg_bound a ha
  have hb2 : |ub * (ga - gb) * wa| ≤ U * (Hg * r) * 1 := by
    refine abs_mul_three_le ?_ ?_ hwa_abs hU_nonneg (mul_nonneg hHg_nonneg hr_nonneg)
    · rw [hub]; exact hu_bound b hb
    · rw [hga, hgb, hr]; exact hg_holder a b ha hb
  have hb3 : |ub * gb * (wa - wb)| ≤ U * G * (p.β * (Hv * r)) := by
    refine abs_mul_three_le ?_ ?_ hwd hU_nonneg hG_nonneg
    · rw [hub]; exact hu_bound b hb
    · rw [hgb]; exact hg_bound b hb
  calc |chemFluxLifted p w a - chemFluxLifted p w b|
      = |ua * ga * wa - ub * gb * wb| := by
        rw [hflux a ha, hflux b hb, ← hua, ← hub, ← hga, ← hgb,
          ← hRa, ← hRb, ← hwa, ← hwb]
    _ = |(ua - ub) * ga * wa + ub * (ga - gb) * wa + ub * gb * (wa - wb)| := by
        rw [htel]
    _ ≤ |(ua - ub) * ga * wa + ub * (ga - gb) * wa| + |ub * gb * (wa - wb)| :=
        abs_add_le _ _
    _ ≤ (|(ua - ub) * ga * wa| + |ub * (ga - gb) * wa|) + |ub * gb * (wa - wb)| := by
        gcongr
        exact abs_add_le _ _
    _ ≤ ((Hu * r) * G * 1 + U * (Hg * r) * 1) + U * G * (p.β * (Hv * r)) := by
        gcongr
    _ = (Hu * G + U * Hg + U * G * p.β * Hv) * |a - b| ^ θ := by
        rw [hr]
        ring

end

end ShenWork.Paper2
