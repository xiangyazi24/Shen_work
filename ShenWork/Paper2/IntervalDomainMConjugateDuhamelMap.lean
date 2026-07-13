import ShenWork.Paper2.IntervalPositiveFloorNonlinearLipschitz
import ShenWork.Paper2.IntervalDuhamelIntegrability
import ShenWork.Paper2.ChemMildHolderBootstrap

/-!
# General-power conjugate mild map on the interval

The published equation uses the divergence flux
`u^m * v_x / (1+v)^beta`.  This file defines its B-form mild map and proves
the positive-strip value estimates needed by the local fixed-point argument.
-/

open MeasureTheory Set
open scoped Topology Interval

noncomputable section

namespace ShenWork.Paper2.IntervalDomainMConjugateDuhamelMap

open ShenWork.IntervalDomain
open ShenWork.PDE
open ShenWork.Paper2
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalConjugateDuhamelMap
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalMildPicard (HasContinuousSlices HasJointMeasurability)
open ShenWork.IntervalPositiveFloorNonlinearLipschitz
open ShenWork.IntervalResolverWeakBounds

/-- Lifted general-`m` chemotaxis flux from the published equation. -/
def chemFluxMLifted (p : CM2Params)
    (w : intervalDomainPoint → ℝ) (y : ℝ) : ℝ :=
  intervalDomainLift w y ^ p.m * resolverGradReal p w y /
    (1 + intervalDomainLift (intervalNeumannResolverR p w) y) ^ p.β

/-- The B-form Picard map for the faithful general-`m` equation. -/
def intervalConjugateDuhamelMapM (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ)
    (t : ℝ) (x : intervalDomainPoint) : ℝ :=
  intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
    + (-p.χ₀) * (∫ s in (0 : ℝ)..t,
        intervalConjugateKernelOperator (t - s) (chemFluxMLifted p (u s)) x.1)
    + ∫ s in (0 : ℝ)..t,
        intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x.1

/-- Fixed-point predicate for the faithful general-`m` B-form map. -/
def IntervalConjugateMildSolutionM (p : CM2Params) (T : ℝ)
    (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) : Prop :=
  ∀ t, 0 < t → t ≤ T → ∀ x,
    u t x = intervalConjugateDuhamelMapM p u₀ u t x

/-- Telescoping estimate when the mass factor has its own Lipschitz
constant.  This is the scalar algebra behind the general-`m` flux bound. -/
theorem chemFlux_div_lipschitz_with_massLip
    {β A B d LA LG LR : ℝ} (hβ : 0 ≤ β)
    {a₁ a₂ g₁ g₂ v₁ v₂ : ℝ}
    (ha₂ : |a₂| ≤ A) (hg₁ : |g₁| ≤ B) (hg₂ : |g₂| ≤ B)
    (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂)
    (had : |a₁ - a₂| ≤ LA * d)
    (hgd : |g₁ - g₂| ≤ LG * d)
    (hvd : |v₁ - v₂| ≤ LR * d)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hLA : 0 ≤ LA)
    (hLG : 0 ≤ LG) (_hLR : 0 ≤ LR) (hd : 0 ≤ d) :
    |a₁ * g₁ / (1 + v₁) ^ β - a₂ * g₂ / (1 + v₂) ^ β| ≤
      (LA * B + A * LG + A * B * β * LR) * d := by
  have hcv : ∀ {v : ℝ}, 0 ≤ v →
      (1 + v) ^ (-β) = ((1 + v) ^ β)⁻¹ := by
    intro v hv
    rw [Real.rpow_neg (by linarith)]
  have heq : ∀ {a g v : ℝ}, 0 ≤ v →
      a * g / (1 + v) ^ β = a * g * (1 + v) ^ (-β) := by
    intro a g v hv
    rw [hcv hv, div_eq_mul_inv]
  rw [heq hv₁, heq hv₂]
  let w₁ := (1 + v₁) ^ (-β)
  let w₂ := (1 + v₂) ^ (-β)
  have hw₁nn : 0 ≤ w₁ := Real.rpow_nonneg (by linarith) _
  have hw₁le : w₁ ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hw₁abs : |w₁| ≤ 1 := by simpa [abs_of_nonneg hw₁nn]
  have hwd : |w₁ - w₂| ≤ β * (LR * d) := by
    calc
      |w₁ - w₂| ≤ β * |v₁ - v₂| :=
        ShenWork.IntervalChemFluxLipschitz.oneAddRpow_neg_lipschitz hβ hv₁ hv₂
      _ ≤ β * (LR * d) := mul_le_mul_of_nonneg_left hvd hβ
  have htel :
      a₁ * g₁ * w₁ - a₂ * g₂ * w₂ =
        (a₁ - a₂) * g₁ * w₁ + a₂ * (g₁ - g₂) * w₁ +
          a₂ * g₂ * (w₁ - w₂) := by ring
  rw [htel]
  calc
    |(a₁ - a₂) * g₁ * w₁ + a₂ * (g₁ - g₂) * w₁ +
        a₂ * g₂ * (w₁ - w₂)|
        ≤ |(a₁ - a₂) * g₁ * w₁| +
            |a₂ * (g₁ - g₂) * w₁| + |a₂ * g₂ * (w₁ - w₂)| := by
          linarith [abs_add_le ((a₁ - a₂) * g₁ * w₁)
            (a₂ * (g₁ - g₂) * w₁),
            abs_add_le ((a₁ - a₂) * g₁ * w₁ + a₂ * (g₁ - g₂) * w₁)
              (a₂ * g₂ * (w₁ - w₂))]
    _ ≤ (LA * d) * B * 1 + A * (LG * d) * 1 +
          A * B * (β * (LR * d)) := by
        gcongr
        · simpa [abs_mul] using
            mul_le_mul (mul_le_mul had hg₁ (abs_nonneg _) (by positivity))
              hw₁abs (abs_nonneg _) (by positivity)
        · simpa [abs_mul] using
            mul_le_mul (mul_le_mul ha₂ hgd (abs_nonneg _) (by positivity))
              hw₁abs (abs_nonneg _) (by positivity)
        · simpa [abs_mul] using
            mul_le_mul (mul_le_mul ha₂ hg₂ (abs_nonneg _) (by positivity))
              hwd (abs_nonneg _) (by positivity)
    _ = (LA * B + A * LG + A * B * β * LR) * d := by ring

/-- General-`m` chemotaxis flux is Lipschitz on a positive strip. -/
theorem chemFluxMLifted_diff_bound_of_pos_slice
    (p : CM2Params) {c M d : ℝ}
    (hc : 0 < c) (hcM : c ≤ M) (hd_nn : 0 ≤ d)
    {u w : intervalDomainPoint → ℝ}
    (hu_bound : ∀ x, |u x| ≤ M) (hu_floor : ∀ x, c ≤ u x)
    (hu_cont : Continuous u)
    (hw_bound : ∀ x, |w x| ≤ M) (hw_floor : ∀ x, c ≤ w x)
    (hw_cont : Continuous w)
    (hd : ∀ x, |u x - w x| ≤ d) (y : ℝ) :
    |chemFluxMLifted p u y - chemFluxMLifted p w y| ≤
      (powerLip p.m c M *
          (Real.sqrt (∑' k : ℕ,
            (intervalNeumannResolverGradWeight p k) ^ 2) *
              (2 * (p.ν * M ^ p.γ))) +
        M ^ p.m *
          (Real.sqrt (∑' k : ℕ,
            (intervalNeumannResolverGradWeight p k) ^ 2) *
              (2 * (p.ν * powerLip p.γ c M))) +
        M ^ p.m *
          (Real.sqrt (∑' k : ℕ,
            (intervalNeumannResolverGradWeight p k) ^ 2) *
              (2 * (p.ν * M ^ p.γ))) * p.β *
          (Real.sqrt (∑' k : ℕ,
            (intervalNeumannResolverWeight p k) ^ 2) *
              (2 * (p.ν * powerLip p.γ c M)))) * d := by
  let BG := Real.sqrt (∑' k : ℕ,
      (intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * M ^ p.γ))
  let LG := Real.sqrt (∑' k : ℕ,
      (intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * powerLip p.γ c M))
  let LR := Real.sqrt (∑' k : ℕ,
      (intervalNeumannResolverWeight p k) ^ 2) *
        (2 * (p.ν * powerLip p.γ c M))
  let LA := powerLip p.m c M
  have hM : 0 < M := hc.trans_le hcM
  have hLA : 0 ≤ LA := powerLip_nonneg p.hm hc hcM
  have hLγ : 0 ≤ powerLip p.γ c M := powerLip_nonneg p.hγ hc hcM
  have hBG : 0 ≤ BG := by
    dsimp [BG]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num)
        (mul_nonneg p.hν.le (Real.rpow_nonneg hM.le _)))
  have hLG : 0 ≤ LG := by
    dsimp [LG]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num) (mul_nonneg p.hν.le hLγ))
  have hLR : 0 ≤ LR := by
    dsimp [LR]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num) (mul_nonneg p.hν.le hLγ))
  unfold chemFluxMLifted
  by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
  · have hcont_u : ContinuousOn (intervalDomainLift u) (Set.Icc (0 : ℝ) 1) := by
      rw [continuousOn_iff_continuous_restrict]
      have heq : Set.restrict (Set.Icc (0 : ℝ) 1) (intervalDomainLift u) = u := by
        ext ⟨x, hx⟩
        simp [Set.restrict, intervalDomainLift, hx]
        rfl
      rw [heq]
      exact hu_cont
    have hcont_w : ContinuousOn (intervalDomainLift w) (Set.Icc (0 : ℝ) 1) := by
      rw [continuousOn_iff_continuous_restrict]
      have heq : Set.restrict (Set.Icc (0 : ℝ) 1) (intervalDomainLift w) = w := by
        ext ⟨x, hx⟩
        simp [Set.restrict, intervalDomainLift, hx]
        rfl
      rw [heq]
      exact hw_cont
    have hmem_u : ∀ x ∈ Set.Icc (0 : ℝ) 1,
        intervalDomainLift u x ∈ Set.Icc c M := by
      intro x hx
      exact ⟨by simpa [intervalDomainLift, hx] using hu_floor ⟨x, hx⟩,
        by simpa [intervalDomainLift, hx] using (abs_le.mp (hu_bound ⟨x, hx⟩)).2⟩
    have hmem_w : ∀ x ∈ Set.Icc (0 : ℝ) 1,
        intervalDomainLift w x ∈ Set.Icc c M := by
      intro x hx
      exact ⟨by simpa [intervalDomainLift, hx] using hw_floor ⟨x, hx⟩,
        by simpa [intervalDomainLift, hx] using (abs_le.mp (hw_bound ⟨x, hx⟩)).2⟩
    have hlift : ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |intervalDomainLift u x - intervalDomainLift w x| ≤ d := by
      intro x hx
      simpa [intervalDomainLift, hx] using hd ⟨x, hx⟩
    have hpow := rpow_lipschitz_on_pos_Icc p.hm hc (hmem_u y hy) (hmem_w y hy)
    have had : |intervalDomainLift u y ^ p.m - intervalDomainLift w y ^ p.m| ≤
        LA * d := hpow.trans (mul_le_mul_of_nonneg_left (hlift y hy) hLA)
    have hgradU : |resolverGradReal p u y| ≤ BG := by
      exact resolverGrad_sup_le_of_bounded p hcont_u
        (fun x hx => hc.le.trans (hmem_u x hx).1)
        (fun x hx => (hmem_u x hx).2) hy
    have hgradW : |resolverGradReal p w y| ≤ BG := by
      exact resolverGrad_sup_le_of_bounded p hcont_w
        (fun x hx => hc.le.trans (hmem_w x hx).1)
        (fun x hx => (hmem_w x hx).2) hy
    have hgradDiff : |resolverGradReal p u y - resolverGradReal p w y| ≤ LG * d := by
      simpa [LG, mul_assoc] using
        (resolverGrad_diff_sup_le_of_pos_bounded
          p hc hcont_u hcont_w hmem_u hmem_w hlift hy)
    have hRu : 0 ≤ intervalDomainLift (intervalNeumannResolverR p u) y := by
      simp [intervalDomainLift, hy]
      exact resolverR_nonneg_of_continuous_nonneg p hu_cont
        (fun x => hc.le.trans (hu_floor x)) ⟨y, hy⟩
    have hRw : 0 ≤ intervalDomainLift (intervalNeumannResolverR p w) y := by
      simp [intervalDomainLift, hy]
      exact resolverR_nonneg_of_continuous_nonneg p hw_cont
        (fun x => hc.le.trans (hw_floor x)) ⟨y, hy⟩
    have hRdiff :
        |intervalDomainLift (intervalNeumannResolverR p u) y -
          intervalDomainLift (intervalNeumannResolverR p w) y| ≤ LR * d := by
      simpa [LR, intervalDomainLift, hy, mul_assoc] using
        (resolverValue_diff_sup_le_of_pos_bounded
          p hc hcont_u hcont_w hmem_u hmem_w hlift ⟨y, hy⟩)
    have hmass : |intervalDomainLift w y ^ p.m| ≤ M ^ p.m := by
      rw [abs_of_nonneg (Real.rpow_nonneg (hc.le.trans (hmem_w y hy).1) _)]
      exact Real.rpow_le_rpow (hc.le.trans (hmem_w y hy).1)
        (hmem_w y hy).2 p.hm.le
    simpa [LA, BG, LG, LR] using
      (chemFlux_div_lipschitz_with_massLip p.hβ hmass hgradU hgradW
        hRu hRw had hgradDiff hRdiff (Real.rpow_nonneg hM.le _)
        hBG hLA hLG hLR hd_nn)
  · have hcoef : 0 ≤ LA * BG + M ^ p.m * LG +
        M ^ p.m * BG * p.β * LR := by
      exact add_nonneg
        (add_nonneg (mul_nonneg hLA hBG)
          (mul_nonneg (Real.rpow_nonneg hM.le _) hLG))
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (Real.rpow_nonneg hM.le _) hBG) p.hβ)
          hLR)
    simp [intervalDomainLift, hy, Real.zero_rpow p.hm.ne']
    simpa [LA, BG, LG, LR] using mul_nonneg hcoef hd_nn

/-- A positive bounded slice has an explicit general-`m` flux bound. -/
theorem chemFluxMLifted_abs_le_of_pos_slice
    (p : CM2Params) {c M : ℝ} (hc : 0 < c) (hcM : c ≤ M)
    {u : intervalDomainPoint → ℝ}
    (hu_bound : ∀ x, |u x| ≤ M) (hu_floor : ∀ x, c ≤ u x)
    (hu_cont : Continuous u) (y : ℝ) :
    |chemFluxMLifted p u y| ≤
      M ^ p.m *
        (Real.sqrt (∑' k : ℕ,
          (intervalNeumannResolverGradWeight p k) ^ 2) *
            (2 * (p.ν * M ^ p.γ))) := by
  unfold chemFluxMLifted
  by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
  · have hM : 0 < M := hc.trans_le hcM
    have hcont_u : ContinuousOn (intervalDomainLift u) (Set.Icc (0 : ℝ) 1) := by
      rw [continuousOn_iff_continuous_restrict]
      have heq : Set.restrict (Set.Icc (0 : ℝ) 1) (intervalDomainLift u) = u := by
        ext ⟨x, hx⟩
        simp [Set.restrict, intervalDomainLift, hx]
        rfl
      rw [heq]
      exact hu_cont
    have hU0 : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ intervalDomainLift u x := by
      intro x hx
      simpa [intervalDomainLift, hx] using hc.le.trans (hu_floor ⟨x, hx⟩)
    have hUM : ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift u x ≤ M := by
      intro x hx
      simpa [intervalDomainLift, hx] using (abs_le.mp (hu_bound ⟨x, hx⟩)).2
    have hgrad := resolverGrad_sup_le_of_bounded p hcont_u hU0 hUM hy
    have hR : 0 ≤ intervalDomainLift (intervalNeumannResolverR p u) y := by
      simp [intervalDomainLift, hy]
      exact resolverR_nonneg_of_continuous_nonneg p hu_cont
        (fun x => hc.le.trans (hu_floor x)) ⟨y, hy⟩
    have hden : 1 ≤ (1 + intervalDomainLift (intervalNeumannResolverR p u) y) ^ p.β :=
      Real.one_le_rpow (by linarith) p.hβ
    have hBG : 0 ≤ Real.sqrt (∑' k : ℕ,
        (intervalNeumannResolverGradWeight p k) ^ 2) *
          (2 * (p.ν * M ^ p.γ)) := by
      exact mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (by norm_num)
          (mul_nonneg p.hν.le (Real.rpow_nonneg hM.le _)))
    rw [abs_div, abs_mul, abs_of_nonneg (Real.rpow_nonneg (hU0 y hy) _),
      abs_of_nonneg (Real.rpow_nonneg (by linarith [hR]) _)]
    exact (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hden)).2 <| by
      calc
        intervalDomainLift u y ^ p.m * |resolverGradReal p u y| ≤
            M ^ p.m *
              (Real.sqrt (∑' k : ℕ,
                (intervalNeumannResolverGradWeight p k) ^ 2) *
                  (2 * (p.ν * M ^ p.γ))) :=
          mul_le_mul
            (Real.rpow_le_rpow (hU0 y hy) (hUM y hy) p.hm.le)
            hgrad (abs_nonneg _)
            (Real.rpow_nonneg hM.le _)
        _ ≤ _ * (1 + intervalDomainLift
            (intervalNeumannResolverR p u) y) ^ p.β :=
          le_mul_of_one_le_right
            (mul_nonneg (Real.rpow_nonneg hM.le _) hBG) hden
  · simp [intervalDomainLift, hy, Real.zero_rpow p.hm.ne']
    exact mul_nonneg (Real.rpow_nonneg (hc.le.trans hcM) _) (by
      exact mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (by norm_num)
          (mul_nonneg p.hν.le
            (Real.rpow_nonneg (hc.le.trans hcM) _))))

/-- Joint measurability of the faithful general-`m` flux family. -/
theorem chemFluxMLifted_uncurry_measurable
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (hmeas : HasJointMeasurability u) :
    Measurable (Function.uncurry (fun s => chemFluxMLifted p (u s))) := by
  have hR := ShenWork.Paper2.resolverR_lift_uncurry_measurable
    (p := p) (w := u) hmeas
  have hG := ShenWork.Paper2.resolverGradReal_uncurry_measurable
    (p := p) (w := u) hmeas
  have hpow : Measurable (fun q : ℝ × ℝ =>
      intervalDomainLift (u q.1) q.2 ^ p.m) := by
    exact (by fun_prop : Measurable (fun z : ℝ => z ^ p.m)).comp hmeas
  have hden : Measurable (fun q : ℝ × ℝ =>
      (1 + intervalDomainLift (intervalNeumannResolverR p (u q.1)) q.2) ^ p.β) := by
    exact (by fun_prop : Measurable (fun z : ℝ => z ^ p.β)).comp
      (measurable_const.add hR)
  simpa [Function.uncurry, chemFluxMLifted] using (hpow.mul hG).div hden

/-- A positive continuous slice has a continuous faithful flux on the closed
physical interval. -/
theorem chemFluxMLifted_continuousOn_Icc_of_pos_slice
    (p : CM2Params) {c M : ℝ} (hc : 0 < c) (hcM : c ≤ M)
    {u : intervalDomainPoint → ℝ}
    (hu_bound : ∀ x, |u x| ≤ M) (hu_floor : ∀ x, c ≤ u x)
    (hu_cont : Continuous u) :
    ContinuousOn (chemFluxMLifted p u) (Set.Icc (0 : ℝ) 1) := by
  have hcont_u : ContinuousOn (intervalDomainLift u) (Set.Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    have heq : Set.restrict (Set.Icc (0 : ℝ) 1) (intervalDomainLift u) = u := by
      ext ⟨x, hx⟩
      simp [Set.restrict, intervalDomainLift, hx]
      rfl
    rw [heq]
    exact hu_cont
  have hgrad : Continuous (resolverGradReal p u) :=
    ShenWork.IntervalDuhamelIntegrability.resolverGradReal_continuous_of_continuousOn
      p hcont_u
  have hval : Continuous (fun x : ℝ => ∑' k : ℕ,
      (intervalNeumannResolverCoeff p u k).re * unitIntervalCosineMode k x) :=
    ShenWork.IntervalDuhamelIntegrability.resolverValueReal_continuous_of_continuousOn
      p hcont_u
  have hR : ∀ x, 0 ≤ intervalNeumannResolverR p u x :=
    resolverR_nonneg_of_continuous_nonneg p hu_cont
      (fun x => hc.le.trans (hu_floor x))
  rw [continuousOn_iff_continuous_restrict]
  have heq : Set.restrict (Set.Icc (0 : ℝ) 1) (chemFluxMLifted p u) =
      fun x : ↑(Set.Icc (0 : ℝ) 1) =>
        u x ^ p.m * resolverGradReal p u x.1 /
          (1 + intervalNeumannResolverR p u x) ^ p.β := by
    ext ⟨x, hx⟩
    simp [Set.restrict, chemFluxMLifted, intervalDomainLift, hx]
    rfl
  rw [heq]
  refine Continuous.div
    (((hu_cont.comp (continuous_subtype_val.subtype_mk _)).rpow_const
        (fun _ => Or.inr p.hm.le)).mul
      (hgrad.comp continuous_subtype_val))
    ((continuous_const.add (hval.comp continuous_subtype_val)).rpow_const
      (fun _ => Or.inr p.hβ)) ?_
  intro x
  exact ne_of_gt (Real.rpow_pos_of_pos (by linarith [hR x]) _)

/-- The general-`m` B-form flux vanishes at the Neumann endpoints. -/
theorem chemFluxMLifted_endpoint_zero (p : CM2Params)
    (u : intervalDomainPoint → ℝ) : chemFluxMLifted p u 0 = 0 := by
  simp [chemFluxMLifted, intervalDomainLift, resolverGradReal_zero]

theorem chemFluxMLifted_endpoint_one (p : CM2Params)
    (u : intervalDomainPoint → ℝ) : chemFluxMLifted p u 1 = 0 := by
  simp [chemFluxMLifted, intervalDomainLift, resolverGradReal_one]

/-- A continuous slice in a positive strip has integrable faithful flux. -/
theorem chemFluxMLifted_integrable_of_pos_slice
    (p : CM2Params) {c M : ℝ} (hc : 0 < c) (hcM : c ≤ M)
    {u : intervalDomainPoint → ℝ}
    (hu_bound : ∀ x, |u x| ≤ M) (hu_floor : ∀ x, c ≤ u x)
    (hu_cont : Continuous u) :
    Integrable (chemFluxMLifted p u) (intervalMeasure 1) := by
  have hcont_u : ContinuousOn (intervalDomainLift u) (Set.Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    have heq : Set.restrict (Set.Icc (0 : ℝ) 1) (intervalDomainLift u) = u := by
      ext ⟨x, hx⟩
      simp [Set.restrict, intervalDomainLift, hx]
      rfl
    rw [heq]
    exact hu_cont
  have hgrad : Continuous (resolverGradReal p u) :=
    ShenWork.IntervalDuhamelIntegrability.resolverGradReal_continuous_of_continuousOn
      p hcont_u
  have hval : Continuous (fun x : ℝ => ∑' k : ℕ,
      (intervalNeumannResolverCoeff p u k).re * unitIntervalCosineMode k x) :=
    ShenWork.IntervalDuhamelIntegrability.resolverValueReal_continuous_of_continuousOn
      p hcont_u
  have hR : ∀ x, 0 ≤ intervalNeumannResolverR p u x :=
    resolverR_nonneg_of_continuous_nonneg p hu_cont
      (fun x => hc.le.trans (hu_floor x))
  have hflux_cont : ContinuousOn (chemFluxMLifted p u) (Set.Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    have heq : Set.restrict (Set.Icc (0 : ℝ) 1) (chemFluxMLifted p u) =
        fun x : ↑(Set.Icc (0 : ℝ) 1) =>
          u x ^ p.m * resolverGradReal p u x.1 /
            (1 + intervalNeumannResolverR p u x) ^ p.β := by
      ext ⟨x, hx⟩
      simp [Set.restrict, chemFluxMLifted, intervalDomainLift, hx]
      rfl
    rw [heq]
    refine Continuous.div
      (((hu_cont.comp (continuous_subtype_val.subtype_mk _)).rpow_const
          (fun _ => Or.inr p.hm.le)).mul
        (hgrad.comp continuous_subtype_val))
      ((continuous_const.add (hval.comp continuous_subtype_val)).rpow_const
        (fun _ => Or.inr p.hβ)) ?_
    intro x
    exact ne_of_gt (Real.rpow_pos_of_pos (by linarith [hR x]) _)
  have hmeas : AEStronglyMeasurable (chemFluxMLifted p u) (intervalMeasure 1) :=
    hflux_cont.aestronglyMeasurable measurableSet_Icc
  let CQ := M ^ p.m *
    (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
      (2 * (p.ν * M ^ p.γ)))
  exact ShenWork.IntervalDomain.intervalMeasure_integrable_of_abs_bound hmeas
    (fun y => by
      simpa [CQ] using chemFluxMLifted_abs_le_of_pos_slice
        p hc hcM hu_bound hu_floor hu_cont y)

#print axioms chemFlux_div_lipschitz_with_massLip
#print axioms chemFluxMLifted_diff_bound_of_pos_slice
#print axioms chemFluxMLifted_abs_le_of_pos_slice
#print axioms chemFluxMLifted_uncurry_measurable
#print axioms chemFluxMLifted_continuousOn_Icc_of_pos_slice
#print axioms chemFluxMLifted_endpoint_zero
#print axioms chemFluxMLifted_endpoint_one
#print axioms chemFluxMLifted_integrable_of_pos_slice

end ShenWork.Paper2.IntervalDomainMConjugateDuhamelMap
