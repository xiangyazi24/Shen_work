/-
# χ₀<0 CarrySeam with the SATISFIABLE `ContinuousOn [0,1]` slice hypothesis

FAITHFULNESS FIX (§3.3 vacuity).  `carrySeam_of_mild_gradient`
(`IntervalCarrySeamGradient.lean`) carries `hu_cont : Continuous (intervalDomainLift
(u τ))` on ALL of ℝ.  `intervalDomainLift` is the ZERO-extension; for a
strictly-positive conj-mild slice it is DISCONTINUOUS at the boundary
(`IntervalDomainConstantEquilibriumWitness` proves `¬ ContinuousAt`).  So `hu_cont`
is UNSATISFIABLE for the actual solution ⟹ the headline is vacuously conditional.

This file removes that hypothesis.  Every continuity-consumer in the CarrySeam reads
the lift ONLY on `[0,1]` (cosine/sine coefficients are `∫₀¹`; `reflCircle` folds via
`|·|`).  So each is re-discharged from `ContinuousOn (intervalDomainLift (u τ))
(Set.Icc 0 1)` by swapping in the continuous CLAMP representative `u τ ∘ clamp`,
which agrees with the lift on `[0,1]` (`reflCircle_eq_of_eqOn_Icc`,
`cosineCoeffs_eqOn_Icc`, `sineCoeffs_eqOn_Icc`).  The new hypothesis is GENUINELY
satisfied by `conjugatePicardLimit` via `HasContinuousSlices`
(`continuousOn_intervalDomainLift_of_hasContinuousSlices`).

No `sorry`/`admit`/`native_decide`/custom axiom.  New file only.  Lines ≤ 100.
-/
import ShenWork.Paper2.IntervalCarrySeamGradient
import ShenWork.Paper2.IntervalReflCircleContinuousOn
import ShenWork.Paper2.IntervalMildPicard

noncomputable section

namespace ShenWork.Paper2.IntervalCarrySeamGradientContinuousOn

open scoped Real
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalMildPicard (HasContinuousSlices)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.HeatKernelGradientEstimates
  (unitIntervalNeumannCosineCoeff unitIntervalCosineRawCoeff)
open ShenWork.IntervalCosineInversion (reflCircle)
open ShenWork.Paper2.IntervalDivergenceModeIdentity (sineCoeffs)
open ShenWork.Paper2.IntervalReflCircleContinuousOn (reflCircle_eq_of_eqOn_Icc)
open ShenWork.Paper2.IntervalWienerAlgebra
  (CosineMulBridge trueCosProd cosineMulBridge_of_summable)
open ShenWork.Paper2.IntervalMixedProduct (MixedMulBridge trueMixedProd)
open ShenWork.Paper2.IntervalMixedMulBridge (mixedMulBridge_of_summable)
open ShenWork.Paper2.IntervalDenomEnvelopeResolver (resolverValue)
open ShenWork.Paper2.HSigmaScale (MemHSigma resolverCoeff)
open ShenWork.Paper2.IntervalTrajectoryEnvelope (TrajectoryHSigmaEnvelope)
open ShenWork.Paper2.IntervalChiNegSeamFixedReach (CarrySeam)
open ShenWork.Paper2.IntervalCarrySeamGradient
  (v_contDiff_two_of_envelope mixedMulBridge_of_Wsum)
open ShenWork.Paper2.IntervalReflCircleWiener (reflCircle_mul_fourier_summable)
open ShenWork.Paper2.IntervalCkComposition (contDiff_two_one_add_rpow_neg)
open ShenWork.Paper2.IntervalCarrySeamDischarge
  (hvrel_of_mild abs_sineCoeffs_deriv_eq_sqrtLambda_abs_cosineCoeff)
open ShenWork.Paper2.IntervalCarrySeamFrontier
  (memHSigma_lift_of_envelope resolverCoeff_summable_of_envelope)
open ShenWork.Paper2.IntervalReflCircleContinuousOn
  (fourierCoeff_reflCircle_summable_of_cosineCoeff_abs_continuousOn)
open ShenWork.Paper2.IntervalWienerAlgebra (hSigma_subset_l1_of_gt_half)
open ShenWork.Paper2.IntervalDenomEnvelopeResolver (denom_envelope_memHSigma)

/-! ## 0. Continuous clamp representative agreeing on `[0,1]`. -/

/-- The clamp `x ↦ max 0 (min 1 x)` lands in `[0,1]` and is the identity there. -/
private def clamp01 (x : ℝ) : ℝ := max 0 (min 1 x)

private theorem clamp01_mem (x : ℝ) : clamp01 x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

private theorem clamp01_continuous : Continuous clamp01 := by unfold clamp01; fun_prop

private theorem clamp01_eq_self {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : clamp01 x = x := by
  unfold clamp01; rw [min_eq_right hx.2, max_eq_right hx.1]

/-- The continuous CLAMP extension of a `ContinuousOn [0,1]` function, agreeing on `[0,1]`. -/
def clampExt (f : ℝ → ℝ) : ℝ → ℝ := fun x => f (clamp01 x)

theorem clampExt_continuous {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1)) :
    Continuous (clampExt f) := by
  rw [← continuousOn_univ]
  exact hf.comp clamp01_continuous.continuousOn (fun x _ => clamp01_mem x)

theorem clampExt_eqOn (f : ℝ → ℝ) : Set.EqOn f (clampExt f) (Set.Icc 0 1) :=
  fun x hx => by simp only [clampExt, clamp01_eq_self hx]

/-! ## 1. Coefficient transfer under agreement on `[0,1]`. -/

theorem cosineCoeffs_eqOn_Icc {f g : ℝ → ℝ} (h : Set.EqOn f g (Set.Icc 0 1)) :
    cosineCoeffs f = cosineCoeffs g := by
  have hraw : (fun n => unitIntervalCosineRawCoeff (fun x => (f x : ℂ)) n)
      = (fun n => unitIntervalCosineRawCoeff (fun x => (g x : ℂ)) n) := by
    funext n
    simp only [unitIntervalCosineRawCoeff]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    simp only []; rw [h hx]
  funext n
  simp only [cosineCoeffs, unitIntervalNeumannCosineCoeff]
  rw [show unitIntervalCosineRawCoeff (fun x => (f x : ℂ))
      = unitIntervalCosineRawCoeff (fun x => (g x : ℂ)) from hraw]

theorem sineCoeffs_eqOn_Icc {f g : ℝ → ℝ} (h : Set.EqOn f g (Set.Icc 0 1)) :
    sineCoeffs f = sineCoeffs g := by
  funext n
  simp only [sineCoeffs]
  split_ifs with hn
  · rfl
  · congr 1
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    simp only []; rw [h hx]

/-! ## 2. `reflCircle` summability under `[0,1]`-agreement. -/

/-- `reflCircle` Fourier summability transfers across `[0,1]`-agreement. -/
theorem reflCircle_summable_eqOn_Icc {f g : ℝ → ℝ}
    (h : Set.EqOn f g (Set.Icc 0 1))
    (hf : Summable (fun n : ℤ => fourierCoeff (reflCircle f) n)) :
    Summable (fun n : ℤ => fourierCoeff (reflCircle g) n) := by
  rwa [reflCircle_eq_of_eqOn_Icc h] at hf

/-! ## 3. The new hypothesis is SATISFIABLE: `HasContinuousSlices` supplies it. -/

/-- **Satisfiability witness.**  `HasContinuousSlices` (e.g. for
`conjugatePicardLimit`) gives, for each interior time, `ContinuousOn
(intervalDomainLift (u t)) [0,1]` — exactly the new hypothesis.  No vanishing at
the boundary is required (contrast the UNSATISFIABLE `Continuous` on ℝ). -/
theorem continuousOn_intervalDomainLift_of_hasContinuousSlices
    {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ} (hcs : HasContinuousSlices T u)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    ContinuousOn (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) := by
  have hf : Continuous (u t) := hcs t ht htT
  rw [continuousOn_iff_continuous_restrict]
  have heq : (Set.Icc (0 : ℝ) 1).restrict (intervalDomainLift (u t)) = u t := by
    funext y
    simp only [Set.restrict_apply, intervalDomainLift]
    rw [dif_pos y.2]
    exact congr_arg (u t) (Subtype.ext rfl)
  rw [heq]; exact hf

/-! ## 4. Multiplication-bridge transfer under `[0,1]`-agreement. -/

private theorem eqOn_mul {f₁ f₂ g₁ g₂ : ℝ → ℝ}
    (hf : Set.EqOn f₁ f₂ (Set.Icc 0 1)) (hg : Set.EqOn g₁ g₂ (Set.Icc 0 1)) :
    Set.EqOn (fun x => f₁ x * g₁ x) (fun x => f₂ x * g₂ x) (Set.Icc 0 1) :=
  fun x hx => by simp only []; rw [hf hx, hg hx]

/-- `CosineMulBridge` transfers across `[0,1]`-agreement of both factors. -/
theorem cosineMulBridge_eqOn_Icc {f₁ f₂ g₁ g₂ : ℝ → ℝ}
    (hf : Set.EqOn f₁ f₂ (Set.Icc 0 1)) (hg : Set.EqOn g₁ g₂ (Set.Icc 0 1))
    (h : CosineMulBridge f₁ g₁) : CosineMulBridge f₂ g₂ := by
  intro k
  rw [← cosineCoeffs_eqOn_Icc (eqOn_mul hf hg), ← cosineCoeffs_eqOn_Icc hf,
    ← cosineCoeffs_eqOn_Icc hg]
  exact h k

/-- `MixedMulBridge` transfers across `[0,1]`-agreement of both factors. -/
theorem mixedMulBridge_eqOn_Icc {W₁ W₂ vx₁ vx₂ : ℝ → ℝ}
    (hW : Set.EqOn W₁ W₂ (Set.Icc 0 1)) (hvx : Set.EqOn vx₁ vx₂ (Set.Icc 0 1))
    (h : MixedMulBridge W₁ vx₁) : MixedMulBridge W₂ vx₂ := by
  intro k
  rw [← sineCoeffs_eqOn_Icc (eqOn_mul hW hvx), ← cosineCoeffs_eqOn_Icc hW,
    ← sineCoeffs_eqOn_Icc hvx]
  exact h k

/-! ## 5. ℓ¹ producers from `ContinuousOn [0,1]`. -/

variable {p : CM2Params} {μ β t σ : ℝ}
variable {u : ℝ → intervalDomainPoint → ℝ} {v vx W : ℝ → ℝ → ℝ}

/-- `hu_sum` from the envelope + the SATISFIABLE `ContinuousOn` slice hypothesis. -/
theorem reflCircle_lift_summable_of_envelope_cont (hσ0 : 1 / 2 < σ)
    (E : TrajectoryHSigmaEnvelope σ t (fun τ => cosineCoeffs (intervalDomainLift (u τ))))
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) t)
    (hu_on : ContinuousOn (intervalDomainLift (u τ)) (Set.Icc 0 1)) :
    Summable (fun n : ℤ => fourierCoeff (reflCircle (intervalDomainLift (u τ))) n) :=
  fourierCoeff_reflCircle_summable_of_cosineCoeff_abs_continuousOn hu_on
    (hSigma_subset_l1_of_gt_half hσ0 (memHSigma_lift_of_envelope E hτ))

/-- `hwfac_sum` from the envelope + denom positivity + denom `ContinuousOn` (genuine). -/
theorem reflCircle_denom_summable_of_envelope_cont (hμ : 0 < μ)
    (hσ0 : 1 / 2 < σ) (hσ1 : σ < 3 / 2)
    (E : TrajectoryHSigmaEnvelope σ t (fun τ => cosineCoeffs (intervalDomainLift (u τ))))
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) t)
    (hvnn : ∀ x, 0 ≤ resolverValue μ (cosineCoeffs (intervalDomainLift (u τ))) x)
    (hwfac_on : ContinuousOn (fun x => (1 + resolverValue μ
      (cosineCoeffs (intervalDomainLift (u τ))) x) ^ (-β)) (Set.Icc 0 1)) :
    Summable (fun n : ℤ => fourierCoeff (reflCircle (fun x => (1 + resolverValue μ
      (cosineCoeffs (intervalDomainLift (u τ))) x) ^ (-β))) n) :=
  fourierCoeff_reflCircle_summable_of_cosineCoeff_abs_continuousOn hwfac_on
    (hSigma_subset_l1_of_gt_half hσ0
      (denom_envelope_memHSigma hμ hσ0 hσ1 (memHSigma_lift_of_envelope E hτ) hvnn))

/-! ## 6. The χ₀<0 CarrySeam with the SATISFIABLE slice hypothesis. -/

/-- **`carrySeam_of_mild_gradient_cont` — `carrySeam_of_mild_gradient` with the
UNSATISFIABLE `hu_cont : Continuous (intervalDomainLift (u τ))` REPLACED by the
SATISFIABLE `hu_cont_on : ContinuousOn (intervalDomainLift (u τ)) [0,1]`.**

Every continuity-consumer reads the lift only on `[0,1]`.  The continuous CLAMP
representative `W̃ τ = clampExt (lift (u τ)) · denom`, which agrees with `W τ` on
`[0,1]`, discharges `hbr`/`hbridge` through the existing `Continuous`-based bridges,
then `cosineMulBridge_eqOn_Icc`/`mixedMulBridge_eqOn_Icc` transfer back.  The new
hypothesis is GENUINELY satisfied by `conjugatePicardLimit`
(`continuousOn_intervalDomainLift_of_hasContinuousSlices`). -/
def carrySeam_of_mild_gradient_cont
    (E : TrajectoryHSigmaEnvelope σ t (fun τ => cosineCoeffs (intervalDomainLift (u τ))))
    (hμ : 0 < μ) (hμ1 : 1 ≤ μ) (hσ0 : 1 / 2 < σ) (hσ1 : σ < 3 / 2)
    (hβ : 0 ≤ β) (ht : 0 < t) (ht1 : t ≤ 1)
    (hû₀ : MemHSigma (σ + 1 / 4) (cosineCoeffs (intervalDomainLift (u 0))))
    (hvnn : ∀ τ ∈ Set.Icc (0 : ℝ) t, ∀ x,
      0 ≤ resolverValue μ (cosineCoeffs (intervalDomainLift (u τ))) x)
    (hQ : ∀ τ, ShenWork.Paper2.IntervalDecompTauLift.conjQ p u τ = fun x => W τ x * vx τ x)
    (hWdef : ∀ τ, W τ = fun x => intervalDomainLift (u τ) x
      * (1 + resolverValue μ (cosineCoeffs (intervalDomainLift (u τ))) x) ^ (-β))
    (hu_cont_on : ∀ τ ∈ Set.Icc (0 : ℝ) t,
      ContinuousOn (intervalDomainLift (u τ)) (Set.Icc 0 1))
    (hvdef : ∀ τ, v τ = resolverValue μ (cosineCoeffs (intervalDomainLift (u τ))))
    (hvxdef : ∀ τ, vx τ = deriv (v τ))
    (hQ_cont : ∀ k, Continuous (fun τ => sineCoeffs
      (ShenWork.Paper2.IntervalDecompTauLift.conjQ p u τ) k))
    (L : TrajectoryHSigmaEnvelope σ t
      (fun τ k => ShenWork.Paper2.IntervalDecompTauLift.conjFl p u k τ))
    (hFl_cont : ∀ k, Continuous (ShenWork.Paper2.IntervalDecompTauLift.conjFl p u k)) :
    CarrySeam p μ β t u v vx W σ E := by
  have hv2 : ∀ τ ∈ Set.Icc (0 : ℝ) t, ContDiff ℝ 2 (v τ) :=
    fun τ hτ => v_contDiff_two_of_envelope hμ hσ0 E hτ (hvdef τ)
  have hvxcont : ∀ τ ∈ Set.Icc (0 : ℝ) t, Continuous (vx τ) := fun τ hτ => by
    rw [hvxdef τ]; exact (hv2 τ hτ).continuous_deriv (by norm_num)
  have hvderiv : ∀ τ ∈ Set.Icc (0 : ℝ) t, ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (v τ) (vx τ x) x := fun τ hτ x _ => by
    rw [hvxdef τ]; exact ((hv2 τ hτ).differentiable (by norm_num) x).hasDerivAt
  -- denom factor is GENUINELY continuous on ℝ (resolver-gain `ContDiff 2`).
  have hwfac_cont : ∀ τ ∈ Set.Icc (0 : ℝ) t, Continuous (fun x => (1 + resolverValue μ
      (cosineCoeffs (intervalDomainLift (u τ))) x) ^ (-β)) := fun τ hτ => by
    have h := contDiff_two_one_add_rpow_neg (v := v τ) (hv2 τ hτ) (fun x => by
      rw [hvdef τ]; exact hvnn τ hτ x) β
    rw [hvdef τ] at h; exact h.continuous
  have hwfac_on : ∀ τ ∈ Set.Icc (0 : ℝ) t, ContinuousOn (fun x => (1 + resolverValue μ
      (cosineCoeffs (intervalDomainLift (u τ))) x) ^ (-β)) (Set.Icc 0 1) :=
    fun τ hτ => (hwfac_cont τ hτ).continuousOn
  -- ℓ¹ producers from the SATISFIABLE ContinuousOn data.
  have hu_sum : ∀ τ ∈ Set.Icc (0 : ℝ) t,
      Summable (fun n : ℤ => fourierCoeff (reflCircle (intervalDomainLift (u τ))) n) :=
    fun τ hτ => reflCircle_lift_summable_of_envelope_cont hσ0 E hτ (hu_cont_on τ hτ)
  have hwfac_sum : ∀ τ ∈ Set.Icc (0 : ℝ) t,
      Summable (fun n : ℤ => fourierCoeff (reflCircle (fun x => (1 + resolverValue μ
        (cosineCoeffs (intervalDomainLift (u τ))) x) ^ (-β))) n) :=
    fun τ hτ => reflCircle_denom_summable_of_envelope_cont hμ hσ0 hσ1 E hτ
      (fun x => hvnn τ hτ x) (hwfac_on τ hτ)
  refine
    { hμ := hμ, hσ0 := hσ0, hσ1 := hσ1, hβ := hβ, ht := ht, ht1 := ht1
      hû₀ := hû₀, hvnn := hvnn, hQ := hQ, hWdef := hWdef
      hQ_cont := hQ_cont, L := L, hFl_cont := hFl_cont
      hvrel := fun τ hτ => hvrel_of_mild hμ hμ1 (fun k => E.hdom τ hτ k)
        (resolverCoeff_summable_of_envelope hμ hσ0 E) (hvdef τ)
      hdiv := fun τ hτ k =>
        abs_sineCoeffs_deriv_eq_sqrtLambda_abs_cosineCoeff k (hvderiv τ hτ) (hvxcont τ hτ)
      hbr := ?_, hbridge := ?_ }
  · -- `hbr` : CosineMulBridge (lift u) denom, via the continuous CLAMP representative.
    intro τ hτ
    set denom : ℝ → ℝ := fun x => (1 + resolverValue μ
      (cosineCoeffs (intervalDomainLift (u τ))) x) ^ (-β) with hdenom
    set ue : ℝ → ℝ := clampExt (intervalDomainLift (u τ)) with hue
    have huec : Continuous ue := clampExt_continuous (hu_cont_on τ hτ)
    have hueeq : Set.EqOn (intervalDomainLift (u τ)) ue (Set.Icc 0 1) := clampExt_eqOn _
    have huesum : Summable (fun n : ℤ => fourierCoeff (reflCircle ue) n) :=
      reflCircle_summable_eqOn_Icc hueeq (hu_sum τ hτ)
    have hbase : CosineMulBridge ue denom :=
      cosineMulBridge_of_summable huec (hwfac_cont τ hτ) huesum (hwfac_sum τ hτ)
    exact cosineMulBridge_eqOn_Icc hueeq.symm (fun _ _ => rfl) hbase
  · -- `hbridge` : MixedMulBridge (W τ) (vx τ), via the continuous CLAMP representative.
    intro τ hτ
    set denom : ℝ → ℝ := fun x => (1 + resolverValue μ
      (cosineCoeffs (intervalDomainLift (u τ))) x) ^ (-β) with hdenom
    set ue : ℝ → ℝ := clampExt (intervalDomainLift (u τ)) with hue
    have huec : Continuous ue := clampExt_continuous (hu_cont_on τ hτ)
    have hueeq : Set.EqOn (intervalDomainLift (u τ)) ue (Set.Icc 0 1) := clampExt_eqOn _
    set We : ℝ → ℝ := fun x => ue x * denom x with hWe
    have hWec : Continuous We := huec.mul (hwfac_cont τ hτ)
    have hWeq : Set.EqOn (W τ) We (Set.Icc 0 1) := by
      intro x hx; rw [hWdef τ]; simp only [hWe, hue]; rw [hueeq hx]
    have huesum : Summable (fun n : ℤ => fourierCoeff (reflCircle ue) n) :=
      reflCircle_summable_eqOn_Icc hueeq (hu_sum τ hτ)
    have hWesum : Summable (fun n : ℤ => fourierCoeff (reflCircle We) n) :=
      reflCircle_mul_fourier_summable huesum (hwfac_sum τ hτ) huec (hwfac_cont τ hτ)
    have hbase : MixedMulBridge We (vx τ) :=
      mixedMulBridge_of_Wsum hWec (hvxcont τ hτ) hWesum
    exact mixedMulBridge_eqOn_Icc hWeq.symm (fun _ _ => rfl) hbase

end ShenWork.Paper2.IntervalCarrySeamGradientContinuousOn

namespace ShenWork.Paper2.IntervalCarrySeamGradientContinuousOn
section AxiomAudit
#print axioms clampExt_continuous
#print axioms continuousOn_intervalDomainLift_of_hasContinuousSlices
#print axioms cosineMulBridge_eqOn_Icc
#print axioms mixedMulBridge_eqOn_Icc
#print axioms carrySeam_of_mild_gradient_cont
end AxiomAudit
end ShenWork.Paper2.IntervalCarrySeamGradientContinuousOn
