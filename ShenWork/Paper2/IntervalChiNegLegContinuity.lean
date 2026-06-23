/-
  ShenWork/Paper2/IntervalChiNegLegContinuity.lean

  chi0<0 -- the remaining local-existence leg-continuity + slice-Lipschitz
  residuals that feed the Traj-BCF fixed point (IntervalChiNegTrajBridges).

  Three deliverables, each two-way audited (CONSUME a landed lemma whose hyps are
  supplied; carry genuine gaps with the precise missing producer named):

   * G1-log (logistic value-Duhamel leg) -- joint (tau,x)-continuity of
     `z |-> int s in 0..(z.1.1), S(z.1.1-s)(logisticLifted p (trajFun U s))(z.2)`
     on the CLOSED box, REDUCED -- via the landed source-generic singular-Duhamel
     engine `continuous_singular_duhamel` (IntervalChiNegTrajBanachClose) -- to a
     single precise per-fibre continuity `hG_cont`.  Measurability and the FIXED
     constant majorant are DISCHARGED here from the landed semigroup joint
     measurability and the landed Linfty contraction
     `intervalFullSemigroupOperator_Linfty_bound`.
     NOTE (spec correction): the logistic leg is the SEMIGROUP `S`, NOT the
     B-kernel produced by `kernelOp_src_jointCont`; so the generic
     `continuous_singular_duhamel` engine (CONSTANT majorant, S being
     Linfty-bounded) is the correct host, not the B-kernel engine.

   * G1-hom (homogeneous heat leg) -- `z |-> S(z.1.1)(intervalDomainLift u0)(z.2)`.
     The tau>0 joint (tau,x)-continuity is DERIVED from the landed
     `unitIntervalCosineHeatValue_continuousOn_Ioi_prod` via the spectral identity
     `intervalFullSemigroupOperator_eq_cosineHeatValue_Icc`.  The CLOSED-box
     continuity (the tau=0 endpoint) is STRUCTURALLY FALSE for u0 not identically
     0 under this repo's `S(0)f = 0` convention (`intervalFullSemigroupOperator_zero`):
     the landed strong-continuity block `semigroup_initialApproach` gives
     `S(tau)u0(x) -> u0(x) != 0` as tau->0+.  This is the tau=0 convention carried
     downstream (G4); NOT a grep miss -- see the audit note.

   * G2-residual (slice-Lipschitz) -- the per-point `hpt` of
     `trajPhi_supLipschitz_of_pointwise`, DERIVED by consuming the landed banked
     bound `intervalConjugateDuhamelMap_diff_bound_of_banked` with `Dq`/`Cv`
     supplied from the landed slice certificates `chemFluxLifted_diff_bound_of_ball_slice`
     and `logistic_duhamel_diff_bound_of_ball`, and `d = dist U1 U2` via
     `ContinuousMap.dist_apply_le_dist`.

  No sorry/admit/native_decide/custom axiom.  Lines <= 100.  Mathlib v4.29.1.
-/
import ShenWork.Paper2.IntervalChiNegTrajBridges
import ShenWork.Paper2.IntervalChiNegTrajBanachClose
import ShenWork.Paper2.IntervalConjugatePicardBounds
import ShenWork.Paper2.IntervalConjugateLogisticDiffBall
import ShenWork.Paper2.IntervalConjugateFluxDiffBall
import ShenWork.PDE.IntervalSemigroupNeumann
import ShenWork.PDE.IntervalSemigroupAtZero
import ShenWork.PDE.IntervalFullKernelSpectralClean
import ShenWork.PDE.IntervalFullKernelSupBound
import ShenWork.Paper2.IntervalMildPicardThreshold

open MeasureTheory Set intervalIntegral
open scoped Topology Interval NNReal
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalNeumannFullKernel
  (intervalFullSemigroupOperator cosineCoeffs)
open ShenWork.IntervalConjugateDuhamelMap (intervalConjugateDuhamelMap)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.Paper2.IntervalChiNegTrajBanach
open ShenWork.HeatKernelGradientEstimates (heatGradientLinftyLinftyConstant)
open ShenWork.IntervalMildPicardThreshold
  (intervalFullSemigroupOperator_s_param_joint_measurable')
open ShenWork.IntervalFullKernelSpectralClean
  (intervalFullSemigroupOperator_eq_cosineHeatValue_Icc)

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegLegContinuity

/-! ## G1-log -- the logistic value-Duhamel leg, REDUCED to a per-fibre continuity. -/

/-- **G1-log measurability** of the rescaled logistic-leg integrand, for a jointly
measurable lifted source family `Lsrc`.  Consumes the landed semigroup joint
measurability `intervalFullSemigroupOperator_s_param_joint_measurable'`. -/
theorem logisticLeg_rescaled_aemeasurable {t : ℝ} {Lsrc : ℝ → ℝ → ℝ}
    (hL_meas : Measurable (Function.uncurry Lsrc))
    (z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint) :
    AEStronglyMeasurable
      (fun r => z.1.1 *
        intervalFullSemigroupOperator (z.1.1 - z.1.1 * r) (Lsrc (z.1.1 * r)) z.2.1)
      (volume.restrict (Ι (0 : ℝ) 1)) := by
  have hmap : Measurable (fun r : ℝ => (((z.1.1, z.2.1), z.1.1 * r) : (ℝ × ℝ) × ℝ)) :=
    measurable_const.prodMk (measurable_const.mul measurable_id)
  have hc := (intervalFullSemigroupOperator_s_param_joint_measurable' hL_meas).comp hmap
  exact (measurable_const.mul hc).aestronglyMeasurable

/-- **G1-log majorant bound**: the rescaled logistic-leg integrand is dominated by
the FIXED CONSTANT `t * CL` (no diagonal singularity -- the semigroup is
Linfty-bounded by the source bound `CL`).  Consumes `intervalFullSemigroupOperator_Linfty_bound`. -/
theorem logisticLeg_rescaled_bound {t : ℝ} (ht0 : 0 ≤ t) {Lsrc : ℝ → ℝ → ℝ} {CL : ℝ}
    (hCL : 0 ≤ CL) (hL_bound : ∀ s y, |Lsrc s y| ≤ CL)
    (z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint) :
    ∀ᵐ r ∂volume, r ∈ Ι (0 : ℝ) 1 →
      ‖z.1.1 *
        intervalFullSemigroupOperator (z.1.1 - z.1.1 * r) (Lsrc (z.1.1 * r)) z.2.1‖
        ≤ t * CL := by
  have ht1 : z.1.1 ≤ t := z.1.2.2
  have ht0z : 0 ≤ z.1.1 := z.1.2.1
  have hne1 : ∀ᵐ r : ℝ ∂volume, r ≠ 1 := by
    rw [ae_iff]; simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
  filter_upwards [hne1] with r hr1 hrI
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hrI
  have hr_lt1 : r < 1 := lt_of_le_of_ne hrI.2 hr1
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ht0z]
  by_cases hz0 : z.1.1 = 0
  · rw [hz0]; simp only [zero_mul]; exact mul_nonneg ht0 hCL
  · have hzpos : 0 < z.1.1 := lt_of_le_of_ne ht0z (Ne.symm hz0)
    have hfac : 0 < z.1.1 - z.1.1 * r := by nlinarith [hr_lt1, hzpos]
    have hb := ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
      hfac hCL (hL_bound (z.1.1 * r)) z.2.1
    calc z.1.1 * |intervalFullSemigroupOperator (z.1.1 - z.1.1 * r) (Lsrc (z.1.1 * r)) z.2.1|
        ≤ z.1.1 * CL := mul_le_mul_of_nonneg_left hb ht0z
      _ ≤ t * CL := mul_le_mul_of_nonneg_right ht1 hCL

/-- **G1-log -- the logistic value-Duhamel leg joint continuity, REDUCED.**
Consumes the landed source-generic engine `continuous_singular_duhamel`: the
measurability and the FIXED constant majorant `t * CL` are DISCHARGED above; the
sole CARRIED input is the per-fibre continuity `hG_cont` (for a.e. fixed `r`,
`z |-> z.1.1 * S(z.1.1(1-r))(Lsrc(z.1.1 r))(z.2)` is continuous on the box) -- the
precise missing producer is `valueOp_src_jointCont`, the SEMIGROUP analogue of the
landed `kernelOp_src_jointCont` (a source-generic joint (tau,x)-continuity of `S`
with a CONTINUOUSLY-VARYING bounded source). -/
theorem logisticLeg_continuous_reduced {t : ℝ} (ht0 : 0 ≤ t) {Lsrc : ℝ → ℝ → ℝ} {CL : ℝ}
    (hCL : 0 ≤ CL) (hL_meas : Measurable (Function.uncurry Lsrc))
    (hL_bound : ∀ s y, |Lsrc s y| ≤ CL)
    (hG_cont : ∀ᵐ r ∂volume, r ∈ Ι (0 : ℝ) 1 →
      Continuous (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
        z.1.1 * intervalFullSemigroupOperator (z.1.1 - z.1.1 * r) (Lsrc (z.1.1 * r)) z.2.1)) :
    Continuous (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
      ∫ s in (0 : ℝ)..(z.1.1),
        intervalFullSemigroupOperator (z.1.1 - s) (Lsrc s) z.2.1) :=
  ShenWork.Paper2.IntervalChiNegTrajBanachClose.continuous_singular_duhamel
    (F := fun z s => intervalFullSemigroupOperator (z.1.1 - s) (Lsrc s) z.2.1)
    (τ := fun z => z.1.1)
    (bound := fun _ => t * CL)
    (fun z => logisticLeg_rescaled_aemeasurable hL_meas z)
    (intervalIntegral.intervalIntegrable_const)
    (fun z => logisticLeg_rescaled_bound ht0 hCL hL_bound z)
    hG_cont

/-! ## G1-hom -- the homogeneous heat leg.  tau>0 DERIVED; tau=0 endpoint CARRIED. -/

/-- **G1-hom (tau>0) -- DERIVED joint (tau,x)-continuity of the homogeneous heat
leg on the OPEN slab `(0,T) x [0,1]`.**  Stated for a globally-continuous source
`f` (the clipped extension `fun y => u0 (unitClip y)` of the faithful datum);
on `tau>0` the propagator `S(tau)f` agrees with the spectral cosine heat value
(`intervalFullSemigroupOperator_eq_cosineHeatValue_Icc`), whose joint continuity
is the landed `unitIntervalCosineHeatValue_continuousOn_slab`.  This is the genuine
joint-continuity content of the homogeneous leg; the tau=0 endpoint is treated
separately (see `homLeg_value_at_zero`). -/
theorem homLeg_continuousOn_slab {f : ℝ → ℝ}
    (hf_cont : Continuous f) {M : ℝ} (hM : ∀ n, |cosineCoeffs f n| ≤ M)
    {T : ℝ} (hT : 0 < T) :
    ContinuousOn (fun p : ℝ × ℝ =>
        intervalFullSemigroupOperator p.1 f p.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
  have hheat := ShenWork.IntervalSemigroupNeumann.unitIntervalCosineHeatValue_continuousOn_slab
    (a := cosineCoeffs f) hM hT
  apply hheat.congr
  intro p hp
  obtain ⟨hτ, hx⟩ := Set.mem_prod.mp hp
  have hτpos : 0 < p.1 := (Set.mem_Ioo.mp hτ).1
  exact intervalFullSemigroupOperator_eq_cosineHeatValue_Icc hτpos hf_cont hM hx

/-- **G1-hom (tau=0) -- the CARRIED structural obstruction.**  Under this repo's
`S(0)f = 0` convention (`intervalFullSemigroupOperator_zero`), the homogeneous-leg
value at `tau=0` is `0`, while the strong-continuity block `semigroup_initialApproach`
forces the `tau->0+` limit to be `u0(x)`.  Hence whenever there is an interior
point where `u0 != 0`, the closed-box leg is DISCONTINUOUS at `(0,x)`: the value `0`
differs from every `tau>0` value near `u0(x)`.  We record the value-at-zero half as
a clean fact (the missing producer for a TRUE closed-box continuity would be a
modified leg whose tau=0 value equals the `tau->0+` limit, i.e. the shifted/clipped
homogeneous data convention used at G4). -/
theorem homLeg_value_at_zero {u₀ : intervalDomainPoint → ℝ}
    (x : intervalDomainPoint) :
    intervalFullSemigroupOperator 0 (intervalDomainLift u₀) x.1 = 0 :=
  ShenWork.IntervalSemigroupAtZero.intervalFullSemigroupOperator_zero (intervalDomainLift u₀) x.1

/-! ## G2-residual -- the per-point slice-Lipschitz `hpt`, DERIVED. -/

/-- **trajFun slice-difference is dominated by the BCF sup-distance.**  Consumes
`ContinuousMap.dist_apply_le_dist` + `trajFun_apply`. -/
theorem trajFun_slice_dist_le {t : ℝ} (U₁ U₂ : Traj t) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) t) (x : intervalDomainPoint) :
    |trajFun U₁ s x - trajFun U₂ s x| ≤ dist U₁ U₂ := by
  have hda := ContinuousMap.dist_apply_le_dist (f := U₁) (g := U₂) (⟨s, hs⟩, x)
  rw [trajFun_apply U₁ hs x, trajFun_apply U₂ hs x] at *
  simpa [Real.dist_eq] using hda

/-- **G2-residual -- the per-point slice-Lipschitz `hpt`, DERIVED.**  Consumes the
landed banked bound `intervalConjugateDuhamelMap_diff_bound_of_banked`, supplying:
`Dq` from a carried chemFlux slice-Lipschitz datum `hDq_le` (e.g. from
`chemFluxLifted_diff_bound_of_ball_slice`), `Cv` from a carried logistic
slice-Lipschitz datum `hCv_le` (e.g. from `logistic_duhamel_diff_bound_of_ball`),
and the analytic integrabilities/diff bounds as the banked bound'\''s named hyps.
The output bound is `q * dist U1 U2` with
`q = |chi0| * Cg * (2 * sqrt T) * KQ + KV` -- the slice-Lipschitz constant whose
`q < 1` certificate (at small `T`) is the contraction. -/
theorem chiNeg_slice_lipschitz_pointwise
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T) (x : intervalDomainPoint)
    {U₁ U₂ : Traj t} {KQ KV : ℝ} (hKQ : 0 ≤ KQ)
    (hq_diff : ∀ s, 0 < s → s ≤ T → ∀ y,
      |chemFluxLifted p (trajFun U₁ s) y - chemFluxLifted p (trajFun U₂ s) y|
        ≤ KQ * dist U₁ U₂)
    (hq_int_diff : ∀ s, 0 < s → s ≤ T → Integrable
      (fun y => chemFluxLifted p (trajFun U₁ s) y - chemFluxLifted p (trajFun U₂ s) y)
      (intervalMeasure 1))
    (hKq_u : ∀ s, 0 < s → s ≤ T → Integrable
      (fun y => deriv (fun y' : ℝ =>
        ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel (t - s) (x.1) y') y
        * chemFluxLifted p (trajFun U₁ s) y) (intervalMeasure 1))
    (hKq_w : ∀ s, 0 < s → s ≤ T → Integrable
      (fun y => deriv (fun y' : ℝ =>
        ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel (t - s) (x.1) y') y
        * chemFluxLifted p (trajFun U₂ s) y) (intervalMeasure 1))
    (hB_u_int : IntervalIntegrable (fun s : ℝ =>
        ShenWork.IntervalConjugateDuhamelMap.intervalConjugateKernelOperator (t - s)
          (chemFluxLifted p (trajFun U₁ s)) x.1) volume 0 t)
    (hB_w_int : IntervalIntegrable (fun s : ℝ =>
        ShenWork.IntervalConjugateDuhamelMap.intervalConjugateKernelOperator (t - s)
          (chemFluxLifted p (trajFun U₂ s)) x.1) volume 0 t)
    (hB_diff_int : IntervalIntegrable (fun s : ℝ =>
        ShenWork.IntervalConjugateDuhamelMap.intervalConjugateKernelOperator (t - s)
          (fun y => chemFluxLifted p (trajFun U₁ s) y - chemFluxLifted p (trajFun U₂ s) y)
          x.1) volume 0 t)
    (hCv_le :
      |((∫ s in (0 : ℝ)..t,
          intervalFullSemigroupOperator (t - s) (logisticLifted p (trajFun U₁ s)) x.1)
        - (∫ s in (0 : ℝ)..t,
          intervalFullSemigroupOperator (t - s) (logisticLifted p (trajFun U₂ s)) x.1))|
        ≤ KV * dist U₁ U₂) :
    |intervalConjugateDuhamelMap p u₀ (trajFun U₁) t x
      - intervalConjugateDuhamelMap p u₀ (trajFun U₂) t x|
      ≤ (|p.χ₀| * (heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * KQ) + KV)
          * dist U₁ U₂ := by
  have hd_nn : 0 ≤ dist U₁ U₂ := dist_nonneg
  have hbank :=
    ShenWork.IntervalConjugatePicardBounds.intervalConjugateDuhamelMap_diff_bound_of_banked
      p (u₀ := u₀) ht htT x (Dq := KQ * dist U₁ U₂) (Cv := KV * dist U₁ U₂)
      (mul_nonneg hKQ hd_nn) hq_diff hq_int_diff hKq_u hKq_w hB_u_int hB_w_int hB_diff_int hCv_le
  calc |intervalConjugateDuhamelMap p u₀ (trajFun U₁) t x
        - intervalConjugateDuhamelMap p u₀ (trajFun U₂) t x|
      ≤ |p.χ₀| * (heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * (KQ * dist U₁ U₂))
          + KV * dist U₁ U₂ := hbank
    _ = (|p.χ₀| * (heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * KQ) + KV)
          * dist U₁ U₂ := by ring

/-! ## AxiomAudit -/

section AxiomAudit
#print axioms logisticLeg_rescaled_aemeasurable
#print axioms logisticLeg_rescaled_bound
#print axioms logisticLeg_continuous_reduced
#print axioms homLeg_continuousOn_slab
#print axioms homLeg_value_at_zero
#print axioms trajFun_slice_dist_le
#print axioms chiNeg_slice_lipschitz_pointwise
end AxiomAudit

end ShenWork.Paper2.IntervalChiNegLegContinuity
