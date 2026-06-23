/-
  ShenWork/Paper2/IntervalChiNegTrajBanachClose.lean

  χ₀<0 — the G1 singular-Duhamel joint-continuity ENGINE + its conjugate-leg
  instantiation for the trajectory-BCF Banach machine
  (`trajBanach_envelope_of_invariance`, IntervalChiNegTrajBanach).

  ## What this file BUILDS (axiom-clean, the genuinely-new analysis lemma)

  `continuous_singular_duhamel` — the dominated-convergence continuity of a
  VARIABLE-UPPER-LIMIT, DIAGONAL-SINGULAR interval integral
      `z ↦ ∫ s in 0..(τ z), F z s`.
  Mathlib's `continuous_parametric_intervalIntegral_of_continuous` needs a
  `Continuous f.uncurry` integrand and so does NOT apply to the gradient-Duhamel
  kernel `∂ₓS(τ z − s)Q(z)`, which has an integrable `(τ z − s)^{−1/2}`
  singularity on the diagonal `s = τ z`.  We BUILD the continuity from
  `intervalIntegral.continuous_of_dominated_interval`: the substitution
  `s = τ z · r` (Mathlib `smul_integral_comp_mul_left`) turns the variable upper
  limit into the FIXED window `0..1`, after which the rescaled integrand
  `(z,r) ↦ τ z · F z (τ z · r)` is dominated by the FIXED integrable majorant
  `bound r` (the rescaled `(τ z(1−r))^{−1/2}·τ z = √(τ z)·(1−r)^{−1/2}`, with
  `∫₀¹ (1−r)^{−1/2} dr = 2 < ∞`) and is continuous in `z` for a.e. fixed `r`.

  `conjugateLeg_continuous` — the ENGINE instantiated on the χ₀<0 conjugate
  gradient-Duhamel leg `z ↦ ∫ s in 0..(z.1.1), B_N(z.1.1−s)(Q s)(z.2)` over the
  compact box `[0,t] × Ω̄`.  Its measurability (`hG_meas`) and its FIXED
  `Cg·CQ·√t·(1−r)^{−1/2}` majorant (`hG_bound`) are DISCHARGED here from the
  LANDED `intervalConjugateKernelOperator_s_param_joint_measurable` and
  `intervalConjugateKernelOperator_abs_le`.

  ## HONEST ACCOUNTING — what this CLOSES and what remains (DERIVED vs CARRIED)

  CLOSED-NEW here (axiom-clean, ⊆ {propext, Classical.choice, Quot.sound}):
  the singular-Duhamel continuity ENGINE `continuous_singular_duhamel`, and — in
  `conjugateLeg_continuous` — the measurability and the fixed integrable majorant
  of the conjugate leg (the diagonal `(z.1.1−s)^{−1/2}` blow-up absorbed).

  CARRIED (the precise remaining input, NOT faked): the a.e.-fibre continuity
  `hG_cont` — for a.e. fixed `r`, `z ↦ z.1.1·B_N(z.1.1(1−r))(Q(z.1.1 r))(z.2)` is
  continuous.  This needs the JOINT `(τ,x)`-continuity of
  `intervalConjugateKernelOperator` (the repo has only the in-`x`
  `intervalConjugateKernelOperator_continuous_of_bounded`; the joint-in-`(τ,x)`
  deriv-series continuity is unbuilt) AND the time-continuity of the candidate's
  flux slices.  It is the explicit hypothesis `hG_cont`, never a disguised
  conclusion.  No `sorry`/`admit`/`native_decide`/custom `axiom`.  Lines ≤ 100.
-/
import ShenWork.Paper2.IntervalConjugateDuhamelMap
import ShenWork.Paper2.IntervalConjugateKernelJointMeas
import ShenWork.PDE.IntervalGradDuhamelBound
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Set intervalIntegral
open scoped Topology Interval
open ShenWork.IntervalDomain (intervalMeasure intervalDomainPoint)
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateKernelOperator intervalConjugateKernelOperator_abs_le)
open ShenWork.IntervalConjugateKernelJointMeas
  (intervalConjugateKernelOperator_s_param_joint_measurable)
open ShenWork.HeatKernelGradientEstimates
  (heatGradientLinftyLinftyConstant heatGradientLinftyLinftyConstant_nonneg)

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegTrajBanachClose

/-! ## G1 — the singular-Duhamel joint-continuity ENGINE (the new analysis lemma). -/

/-- **G1 ENGINE — dominated-convergence continuity of a variable-upper-limit,
diagonal-singular interval integral.**

For a parameter `z : X` over a first-countable space, the map
`z ↦ ∫ s in 0..(τ z), F z s` is continuous, PROVIDED the rescaled integrand
`(z,r) ↦ τ z · F z (τ z · r)` on the FIXED window `0..1`
  * is a.e.-strongly-measurable in `r` for each `z`            (`hG_meas`);
  * is dominated by a FIXED interval-integrable majorant `bound` (`hG_bound`);
  * is continuous in `z` for a.e. fixed `r`                     (`hG_cont`).

The substitution `s = τ z · r` (`smul_integral_comp_mul_left`) reduces the
variable upper limit `τ z` to the constant `1`, and the diagonal singularity is
absorbed into the fixed majorant `bound` (the rescaled `(τ z(1−r))^{−1/2}·τ z`).
This is the singular analogue of `continuous_parametric_primitive_of_continuous`,
which is unavailable here because the integrand is NOT `Continuous`-uncurried. -/
theorem continuous_singular_duhamel
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {F : X → ℝ → ℝ} {τ : X → ℝ} {bound : ℝ → ℝ}
    (hG_meas : ∀ z, AEStronglyMeasurable (fun r => τ z * F z (τ z * r))
      (volume.restrict (Ι (0 : ℝ) 1)))
    (hbound_int : IntervalIntegrable bound volume 0 1)
    (hG_bound : ∀ z, ∀ᵐ r ∂volume, r ∈ Ι (0 : ℝ) 1 →
      ‖τ z * F z (τ z * r)‖ ≤ bound r)
    (hG_cont : ∀ᵐ r ∂volume, r ∈ Ι (0 : ℝ) 1 →
      Continuous (fun z => τ z * F z (τ z * r))) :
    Continuous (fun z => ∫ s in (0 : ℝ)..(τ z), F z s) := by
  have hrescale : (fun z => ∫ s in (0 : ℝ)..(τ z), F z s)
      = fun z => ∫ r in (0 : ℝ)..1, τ z * F z (τ z * r) := by
    funext z
    have h := smul_integral_comp_mul_left (a := (0 : ℝ)) (b := 1) (f := F z) (τ z)
    simp only [mul_zero, mul_one, smul_eq_mul] at h
    rw [← h, intervalIntegral.integral_const_mul]
  rw [hrescale]
  exact continuous_of_dominated_interval hG_meas hG_bound hbound_int hG_cont

/-! ## G1 — the conjugate gradient-Duhamel leg over the compact box. -/

/-- The FIXED `(1−r)^{−1/2}` interval majorant is interval-integrable on `0..1`. -/
theorem boundOneSubRpow_intervalIntegrable (C : ℝ) :
    IntervalIntegrable (fun r : ℝ => C * (1 - r) ^ (-(1/2) : ℝ)) volume 0 1 :=
  (ShenWork.IntervalGradDuhamelBound.intervalIntegrable_sub_rpow_neg_half 1).const_mul C

set_option maxHeartbeats 1000000 in
-- raised: the landed joint-measurability term elaborates a heavy spectral-series `whnf`.
/-- **Measurability of the rescaled conjugate-leg integrand** for a jointly
measurable source `Q`. -/
theorem conjugateLeg_rescaled_aemeasurable {t : ℝ} {Q : ℝ → ℝ → ℝ}
    (hQ_meas : Measurable (Function.uncurry Q))
    (z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint) :
    AEStronglyMeasurable
      (fun r => z.1.1 *
        intervalConjugateKernelOperator (z.1.1 - z.1.1 * r) (Q (z.1.1 * r)) z.2.1)
      (volume.restrict (Ι (0 : ℝ) 1)) := by
  have hmap : Measurable (fun r : ℝ => (((z.1.1, z.2.1), z.1.1 * r) : (ℝ × ℝ) × ℝ)) :=
    measurable_const.prodMk (measurable_const.mul measurable_id)
  have hc := (intervalConjugateKernelOperator_s_param_joint_measurable hQ_meas).comp hmap
  exact (measurable_const.mul hc).aestronglyMeasurable

/-- **The FIXED majorant bound of the rescaled conjugate-leg integrand**:
`z.1.1·|B_N(z.1.1(1−r))(Q(z.1.1 r))(z.2)| ≤ Cg·CQ·√t·(1−r)^{−1/2}`, absorbing the
diagonal `(z.1.1−s)^{−1/2}` blow-up into the fixed `(1−r)^{−1/2}` majorant. -/
theorem conjugateLeg_rescaled_bound {t : ℝ} {Q : ℝ → ℝ → ℝ} {CQ : ℝ} (hCQ : 0 ≤ CQ)
    (hQ_int : ∀ s, Integrable (Q s) (intervalMeasure 1)) (hQ_bound : ∀ s y, |Q s y| ≤ CQ)
    (z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint) :
    ∀ᵐ r ∂volume, r ∈ Ι (0 : ℝ) 1 →
      ‖z.1.1 *
        intervalConjugateKernelOperator (z.1.1 - z.1.1 * r) (Q (z.1.1 * r)) z.2.1‖
        ≤ heatGradientLinftyLinftyConstant * CQ * Real.sqrt t * (1 - r) ^ (-(1/2) : ℝ) := by
  set Cg := heatGradientLinftyLinftyConstant with hCg
  have hCgnn : 0 ≤ Cg := heatGradientLinftyLinftyConstant_nonneg
  have ht1 : z.1.1 ≤ t := z.1.2.2
  have ht0 : 0 ≤ z.1.1 := z.1.2.1
  have hne1 : ∀ᵐ r : ℝ ∂volume, r ≠ 1 := by
    rw [ae_iff]; simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
  filter_upwards [hne1] with r hr1 hrI
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hrI
  have hr_lt1 : r < 1 := lt_of_le_of_ne hrI.2 hr1
  have hfac0 : z.1.1 - z.1.1 * r = z.1.1 * (1 - r) := by ring
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ht0, hfac0]
  by_cases hz0 : z.1.1 = 0
  · rw [hz0]; simp only [zero_mul]
    have hrp : 0 ≤ (1 - r) ^ (-(1/2):ℝ) := Real.rpow_nonneg (by linarith) _
    have : 0 ≤ Cg * CQ * Real.sqrt t * (1 - r) ^ (-(1/2):ℝ) :=
      mul_nonneg (mul_nonneg (mul_nonneg hCgnn hCQ) (Real.sqrt_nonneg t)) hrp
    linarith
  · have hzpos : 0 < z.1.1 := lt_of_le_of_ne ht0 (Ne.symm hz0)
    have hlag : 0 < z.1.1 * (1 - r) := mul_pos hzpos (by linarith)
    have hb := intervalConjugateKernelOperator_abs_le (hfac0 ▸ hlag) (hQ_int (z.1.1 * r))
      (hQ_bound (z.1.1 * r)) z.2.1
    rw [hfac0,
      Real.mul_rpow ht0 (by linarith : (0 : ℝ) ≤ 1 - r)] at hb
    calc z.1.1 * |intervalConjugateKernelOperator (z.1.1 * (1 - r)) (Q (z.1.1 * r)) z.2.1|
        ≤ z.1.1 * (Cg * (z.1.1 ^ (-(1/2):ℝ) * (1 - r) ^ (-(1/2):ℝ)) * CQ) :=
          mul_le_mul_of_nonneg_left hb ht0
      _ = Cg * CQ * (z.1.1 * z.1.1 ^ (-(1/2):ℝ)) * (1 - r) ^ (-(1/2):ℝ) := by ring
      _ = Cg * CQ * z.1.1 ^ (1/2:ℝ) * (1 - r) ^ (-(1/2):ℝ) := by
          have hhalf : z.1.1 * z.1.1 ^ (-(1/2):ℝ) = z.1.1 ^ (1/2:ℝ) := by
            nth_rewrite 1 [← Real.rpow_one (z.1.1)]
            rw [← Real.rpow_add hzpos]; norm_num
          rw [hhalf]
      _ ≤ Cg * CQ * Real.sqrt t * (1 - r) ^ (-(1/2):ℝ) := by
          have hle : z.1.1 ^ (1/2:ℝ) ≤ Real.sqrt t := by
            rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow ht0 ht1 (by norm_num)
          have hrp : 0 ≤ (1 - r) ^ (-(1/2):ℝ) := Real.rpow_nonneg (by linarith) _
          have hcc : 0 ≤ Cg * CQ := mul_nonneg hCgnn hCQ
          nlinarith [Real.rpow_nonneg ht0 (1/2:ℝ), mul_nonneg hcc hrp]

set_option maxHeartbeats 1000000 in
-- raised: re-elaborates the heavy joint-measurability spectral-series `whnf`.
/-- **G1 — joint continuity of the conjugate gradient-Duhamel leg over the box.**
The ENGINE instantiated on `z ↦ ∫ s in 0..(z.1.1), B_N(z.1.1−s)(Q s)(z.2)`:
measurability and the fixed `(1−r)^{−1/2}` majorant are DISCHARGED from the
landed lemmas; only the a.e.-fibre continuity `hG_cont` is carried. -/
theorem conjugateLeg_continuous {t : ℝ} {Q : ℝ → ℝ → ℝ} {CQ : ℝ} (hCQ : 0 ≤ CQ)
    (hQ_meas : Measurable (Function.uncurry Q))
    (hQ_int : ∀ s, Integrable (Q s) (intervalMeasure 1)) (hQ_bound : ∀ s y, |Q s y| ≤ CQ)
    (hG_cont : ∀ᵐ r ∂volume, r ∈ Ι (0 : ℝ) 1 →
      Continuous (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
        z.1.1 * intervalConjugateKernelOperator (z.1.1 - z.1.1 * r) (Q (z.1.1 * r)) z.2.1)) :
    Continuous (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
      ∫ s in (0 : ℝ)..(z.1.1),
        intervalConjugateKernelOperator (z.1.1 - s) (Q s) z.2.1) :=
  continuous_singular_duhamel
    (F := fun z s => intervalConjugateKernelOperator (z.1.1 - s) (Q s) z.2.1)
    (τ := fun z => z.1.1)
    (bound := fun r => heatGradientLinftyLinftyConstant * CQ * Real.sqrt t * (1 - r) ^ (-(1/2):ℝ))
    (fun z => conjugateLeg_rescaled_aemeasurable hQ_meas z)
    (boundOneSubRpow_intervalIntegrable _)
    (fun z => conjugateLeg_rescaled_bound hCQ hQ_int hQ_bound z)
    hG_cont

/-! ## AxiomAudit -/

section AxiomAudit
#print axioms continuous_singular_duhamel
#print axioms boundOneSubRpow_intervalIntegrable
#print axioms conjugateLeg_rescaled_aemeasurable
#print axioms conjugateLeg_rescaled_bound
#print axioms conjugateLeg_continuous
end AxiomAudit

end ShenWork.Paper2.IntervalChiNegTrajBanachClose
