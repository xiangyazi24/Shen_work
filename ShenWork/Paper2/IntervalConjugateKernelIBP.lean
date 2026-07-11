/-
  Operator-level integration by parts for the Neumann conjugate kernel.

  B_N(t)Q(x) = -∫₀¹ ∂_y K_N(t,x,y) Q(y) dy
             = ∫₀¹ K_N(t,x,y) Q'(y) dy      when Q(0)=Q(1)=0 and Q∈W^{1,1}
             = S_N(t)(Q')(x)

  This eliminates the 1/(t-s) singularity in the gradient estimate of the
  chemotaxis Duhamel leg, reducing it to the integrable √(t-s) singularity.
-/

import ShenWork.Paper2.IntervalConjugateDuhamelMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

open MeasureTheory intervalIntegral Set
open scoped NNReal Topology

noncomputable section

namespace ShenWork.Paper2.IntervalConjugateKernelIBP

open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift intervalMeasure intervalSet)
open ShenWork.IntervalNeumannFullKernel
  (intervalNeumannFullKernel intervalFullSemigroupOperator
   continuousOn_intervalNeumannFullKernel_snd
   hasDerivAt_intervalNeumannFullKernel_snd
   intervalIntegrable_deriv_intervalNeumannFullKernel_snd)
open ShenWork.IntervalConjugateDuhamelMap (intervalConjugateKernelOperator)

/-- Regularity predicate for one-dimensional integration by parts with a
countable exceptional set.  Positive-part fluxes naturally satisfy this shape:
their only possible corners are transversal zeros. -/
def IntervalIBPRegularity (Q : ℝ → ℝ) : Prop :=
  ∃ exceptional : Set ℝ,
    exceptional.Countable ∧
    ContinuousOn Q (Icc (0 : ℝ) 1) ∧
    (∀ y ∈ Ioo (0 : ℝ) 1 \ exceptional,
      HasDerivAt Q (deriv Q y) y) ∧
    IntervalIntegrable (deriv Q) volume 0 1

lemma intervalMeasure_one_integral_eq_intervalIntegral (f : ℝ → ℝ) :
    (∫ y, f y ∂ intervalMeasure 1) = ∫ y in (0 : ℝ)..1, f y := by
  unfold intervalMeasure intervalSet
  change (∫ y in Icc (0 : ℝ) 1, f y ∂ volume) = ∫ y in (0 : ℝ)..1, f y
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]

theorem intervalConjugateKernelOperator_eq_semigroup_deriv
    {t x : ℝ} (ht : 0 < t) {Q : ℝ → ℝ}
    (hQ_cont : ContinuousOn Q (uIcc (0 : ℝ) 1))
    (hQ_deriv : ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivAt Q (deriv Q y) y)
    (hQ_deriv_int :
      IntervalIntegrable (fun y : ℝ => deriv Q y) volume 0 1)
    (hQ0 : Q 0 = 0) (hQ1 : Q 1 = 0) :
    intervalConjugateKernelOperator t Q x =
      intervalFullSemigroupOperator t (deriv Q) x := by
  classical
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  set K : ℝ → ℝ := fun y : ℝ => intervalNeumannFullKernel t x y with hK
  set K' : ℝ → ℝ :=
    fun y : ℝ => deriv (fun y' : ℝ => intervalNeumannFullKernel t x y') y with hK'
  have hK_cont : ContinuousOn K (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le h01]
    simpa [K] using continuousOn_intervalNeumannFullKernel_snd ht x
  have hK_deriv :
      ∀ y ∈ Ioo (min (0 : ℝ) 1) (max 0 1), HasDerivAt K (K' y) y := by
    intro y _hy
    have h := hasDerivAt_intervalNeumannFullKernel_snd ht x y
    simpa [K, K', h.deriv] using h
  have hQ_deriv_minmax :
      ∀ y ∈ Ioo (min (0 : ℝ) 1) (max 0 1), HasDerivAt Q (deriv Q y) y := by
    intro y hy
    have hy' : y ∈ Ioo (0 : ℝ) 1 := by
      simpa [min_eq_left h01, max_eq_right h01] using hy
    exact hQ_deriv y hy'
  have hK'_int : IntervalIntegrable K' volume 0 1 := by
    simpa [K'] using intervalIntegrable_deriv_intervalNeumannFullKernel_snd ht x
  have hIBP :
      (∫ y in (0 : ℝ)..1, K y * deriv Q y) =
        K 1 * Q 1 - K 0 * Q 0 - ∫ y in (0 : ℝ)..1, K' y * Q y :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      hK_cont hQ_cont hK_deriv hQ_deriv_minmax hK'_int hQ_deriv_int
  have hIBP_zero :
      (∫ y in (0 : ℝ)..1, K y * deriv Q y) =
        - ∫ y in (0 : ℝ)..1, K' y * Q y := by
    simpa [hQ0, hQ1] using hIBP
  unfold intervalConjugateKernelOperator intervalFullSemigroupOperator
  rw [intervalMeasure_one_integral_eq_intervalIntegral
    (f := fun y : ℝ =>
      deriv (fun y' : ℝ => intervalNeumannFullKernel t x y') y * Q y)]
  rw [intervalMeasure_one_integral_eq_intervalIntegral
    (f := fun y : ℝ => intervalNeumannFullKernel t x y * deriv Q y)]
  simpa [K, K'] using hIBP_zero.symm

/-- Operator-level integration by parts for an absolutely continuous flux.

Unlike `intervalConjugateKernelOperator_eq_semigroup_deriv`, this version does
not require pointwise differentiability on the whole open interval.  In
particular it applies to Lipschitz fluxes with corners: their classical
derivative agrees almost everywhere with the weak derivative, which is the
quantity appearing in the absolutely-continuous integration-by-parts theorem. -/
theorem intervalConjugateKernelOperator_eq_semigroup_deriv_of_ac
    {t x : ℝ} (ht : 0 < t) {Q : ℝ → ℝ}
    (hQ_ac : AbsolutelyContinuousOnInterval Q 0 1)
    (hQ0 : Q 0 = 0) (hQ1 : Q 1 = 0) :
    intervalConjugateKernelOperator t Q x =
      intervalFullSemigroupOperator t (deriv Q) x := by
  classical
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  set K : ℝ → ℝ := fun y : ℝ => intervalNeumannFullKernel t x y with hK
  set K' : ℝ → ℝ :=
    fun y : ℝ => deriv (fun y' : ℝ => intervalNeumannFullKernel t x y') y with hK'
  have hK_deriv : ∀ y : ℝ, HasDerivAt K (K' y) y := by
    intro y
    simpa [K, K', (hasDerivAt_intervalNeumannFullKernel_snd ht x y).deriv] using
      hasDerivAt_intervalNeumannFullKernel_snd ht x y
  have hK'_cont : ContinuousOn K' (Icc (0 : ℝ) 1) := by
    simpa [K'] using
      ShenWork.IntervalNeumannFullKernel.continuousOn_deriv_intervalNeumannFullKernel_snd
        ht x
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hK'_cont
  have hB_nonneg : 0 ≤ B := by
    exact le_trans (norm_nonneg (K' 0)) (hB 0 (by norm_num))
  let C : ℝ≥0 := ⟨B, hB_nonneg⟩
  have hK_lip : LipschitzOnWith C K (Icc (0 : ℝ) 1) := by
    apply (convex_Icc (0 : ℝ) 1).lipschitzOnWith_of_nnnorm_deriv_le
    · intro y _hy
      exact (hK_deriv y).differentiableAt
    · intro y hy
      have hnorm : ‖deriv K y‖ ≤ B := by
        rw [(hK_deriv y).deriv]
        exact hB y hy
      exact_mod_cast hnorm
  have hK_ac : AbsolutelyContinuousOnInterval K 0 1 := by
    have hK_lip' : LipschitzOnWith C K (uIcc (0 : ℝ) 1) := by
      simpa [uIcc_of_le h01] using hK_lip
    exact hK_lip'.absolutelyContinuousOnInterval
  have hIBP :
      (∫ y in (0 : ℝ)..1, K y * deriv Q y) =
        K 1 * Q 1 - K 0 * Q 0 - ∫ y in (0 : ℝ)..1, deriv K y * Q y :=
    hK_ac.integral_mul_deriv_eq_deriv_mul hQ_ac
  have hIBP_zero :
      (∫ y in (0 : ℝ)..1, K y * deriv Q y) =
        -∫ y in (0 : ℝ)..1, K' y * Q y := by
    simpa [hQ0, hQ1, (hK_deriv _).deriv] using hIBP
  unfold intervalConjugateKernelOperator intervalFullSemigroupOperator
  rw [intervalMeasure_one_integral_eq_intervalIntegral
    (f := fun y : ℝ =>
      deriv (fun y' : ℝ => intervalNeumannFullKernel t x y') y * Q y)]
  rw [intervalMeasure_one_integral_eq_intervalIntegral
    (f := fun y : ℝ => intervalNeumannFullKernel t x y * deriv Q y)]
  simpa [K, K'] using hIBP_zero.symm

/-- Operator-level integration by parts when the flux is differentiable away
from a countable exceptional set.  This is the form needed for a positive-part
flux: transversal zeros may create corners, but they form a countable set. -/
theorem intervalConjugateKernelOperator_eq_semigroup_deriv_off_countable
    {t x : ℝ} (ht : 0 < t) {Q : ℝ → ℝ} {s : Set ℝ}
    (hs : s.Countable)
    (hQ_cont : ContinuousOn Q (Icc (0 : ℝ) 1))
    (hQ_deriv : ∀ y ∈ Ioo (0 : ℝ) 1 \ s,
      HasDerivAt Q (deriv Q y) y)
    (hQ_deriv_int : IntervalIntegrable (deriv Q) volume 0 1)
    (hQ0 : Q 0 = 0) (hQ1 : Q 1 = 0) :
    intervalConjugateKernelOperator t Q x =
      intervalFullSemigroupOperator t (deriv Q) x := by
  classical
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  set K : ℝ → ℝ := fun y : ℝ => intervalNeumannFullKernel t x y with hK
  set K' : ℝ → ℝ :=
    fun y : ℝ => deriv (fun y' : ℝ => intervalNeumannFullKernel t x y') y with hK'
  have hK_cont : ContinuousOn K (Icc (0 : ℝ) 1) := by
    simpa [K] using continuousOn_intervalNeumannFullKernel_snd ht x
  have hK_deriv : ∀ y : ℝ, HasDerivAt K (K' y) y := by
    intro y
    simpa [K, K', (hasDerivAt_intervalNeumannFullKernel_snd ht x y).deriv] using
      hasDerivAt_intervalNeumannFullKernel_snd ht x y
  have hK'_int : IntervalIntegrable K' volume 0 1 := by
    simpa [K'] using intervalIntegrable_deriv_intervalNeumannFullKernel_snd ht x
  have hprod_cont : ContinuousOn (fun y => K y * Q y) (Icc (0 : ℝ) 1) :=
    hK_cont.mul hQ_cont
  have hprod_deriv : ∀ y ∈ Ioo (0 : ℝ) 1 \ s,
      HasDerivAt (fun z => K z * Q z) (K' y * Q y + K y * deriv Q y) y := by
    intro y hy
    exact (hK_deriv y).mul (hQ_deriv y hy)
  have hQ_cont_u : ContinuousOn Q (uIcc (0 : ℝ) 1) := by
    simpa [uIcc_of_le h01] using hQ_cont
  have hK_cont_u : ContinuousOn K (uIcc (0 : ℝ) 1) := by
    simpa [uIcc_of_le h01] using hK_cont
  have hleft_int : IntervalIntegrable (fun y => K' y * Q y) volume 0 1 :=
    hK'_int.mul_continuousOn hQ_cont_u
  have hright_int : IntervalIntegrable (fun y => K y * deriv Q y) volume 0 1 :=
    hQ_deriv_int.continuousOn_mul hK_cont_u
  have hFTC :
      (∫ y in (0 : ℝ)..1, K' y * Q y + K y * deriv Q y) =
        K 1 * Q 1 - K 0 * Q 0 :=
    MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
      (fun y => K y * Q y)
      (fun y => K' y * Q y + K y * deriv Q y)
      h01 hs hprod_cont hprod_deriv (hleft_int.add hright_int)
  have hsum_zero :
      (∫ y in (0 : ℝ)..1, K' y * Q y) +
          (∫ y in (0 : ℝ)..1, K y * deriv Q y) = 0 := by
    rw [← intervalIntegral.integral_add hleft_int hright_int]
    simpa [hQ0, hQ1] using hFTC
  have hIBP_zero :
      (∫ y in (0 : ℝ)..1, K y * deriv Q y) =
        -∫ y in (0 : ℝ)..1, K' y * Q y := by
    linarith
  unfold intervalConjugateKernelOperator intervalFullSemigroupOperator
  rw [intervalMeasure_one_integral_eq_intervalIntegral
    (f := fun y : ℝ =>
      deriv (fun y' : ℝ => intervalNeumannFullKernel t x y') y * Q y)]
  rw [intervalMeasure_one_integral_eq_intervalIntegral
    (f := fun y : ℝ => intervalNeumannFullKernel t x y * deriv Q y)]
  simpa [K, K'] using hIBP_zero.symm

theorem intervalConjugateKernelOperator_eq_semigroup_deriv_of_regularity
    {t x : ℝ} (ht : 0 < t) {Q : ℝ → ℝ}
    (H : IntervalIBPRegularity Q)
    (hQ0 : Q 0 = 0) (hQ1 : Q 1 = 0) :
    intervalConjugateKernelOperator t Q x =
      intervalFullSemigroupOperator t (deriv Q) x :=
  by
    rcases H with ⟨exceptional, hexceptional, hcont, hderiv, hint⟩
    exact intervalConjugateKernelOperator_eq_semigroup_deriv_off_countable
      ht hexceptional hcont hderiv hint hQ0 hQ1

end ShenWork.Paper2.IntervalConjugateKernelIBP
