import ShenWork.Paper2.IntervalDomainProposition21
import ShenWork.PDE.IntervalAgmonInterpolation
import ShenWork.PDE.IntervalFullKernelBoundaryRegularity

/-!
# Paper 2, Proposition 2.3 on the unit interval

The key variable is

`z = v / (1 + v)^(β/(P+1))`.

The already-proved uniform positive one-dimensional Agmon inequality applied
to `z` has exactly the left-hand moment and mass remainder in Proposition 2.3.
The remaining derivative term is controlled by one weighted elliptic
multiplier.
-/

open MeasureTheory Set
open scoped Topology Interval
open ShenWork.IntervalDomain
open ShenWork.IntervalEllipticCharacterization
open ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation

noncomputable section

namespace ShenWork.Paper2

/-- The signal transform whose `(P+1)` moment is the weighted signal moment. -/
def intervalWeightedSignalTransform
    (P beta : ℝ) (f : intervalDomain.Point → ℝ) :
    intervalDomain.Point → ℝ :=
  fun X => f X * (1 + f X) ^ (-(beta / (P + 1)))

lemma intervalWeightedSignalTransform_lift_eq
    {P beta : ℝ} {f : intervalDomain.Point → ℝ}
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    intervalDomainLift (intervalWeightedSignalTransform P beta f) x =
      intervalDomainLift f x *
        (1 + intervalDomainLift f x) ^ (-(beta / (P + 1))) := by
  simp [intervalWeightedSignalTransform, intervalDomainLift, hx]

/-- The signal transform stays strictly positive on a positive signal. -/
lemma intervalWeightedSignalTransform_pos
    {P beta : ℝ} {f : intervalDomain.Point → ℝ}
    (hf : ∀ X, 0 < f X) :
    ∀ X, 0 < intervalWeightedSignalTransform P beta f X := by
  intro X
  exact mul_pos (hf X) (Real.rpow_pos_of_pos (by linarith [hf X]) _)

/-- Closed `C²` regularity of the transformed chemical slice. -/
lemma intervalWeightedSignalTransform_contDiffOn_two
    {p : CM2Params} {T t P beta : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    ContDiffOn ℝ 2
      (intervalDomainLift (intervalWeightedSignalTransform P beta (v t)))
      (Set.Icc (0 : ℝ) 1) := by
  let V : ℝ → ℝ := intervalDomainLift (v t)
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hV2 : ContDiffOn ℝ 2 V (Set.Icc (0 : ℝ) 1) := by
    simpa [V] using (hsol.regularity.2.2.2.2.1 t ht).2.1
  have hbase : ContDiffOn ℝ 2 (fun x => 1 + V x) (Set.Icc (0 : ℝ) 1) :=
    contDiffOn_const.add hV2
  have hbase_ne : ∀ x ∈ Set.Icc (0 : ℝ) 1, 1 + V x ≠ 0 := by
    intro x hx
    exact ne_of_gt (by
      linarith [intervalDomain_solution_lift_v_pos_Icc hsol ht0 htT x hx])
  have hcalc : ContDiffOn ℝ 2
      (fun x => V x * (1 + V x) ^ (-(beta / (P + 1))))
      (Set.Icc (0 : ℝ) 1) :=
    hV2.mul (hbase.rpow_const_of_ne hbase_ne)
  exact hcalc.congr fun x hx => by
    simpa [V] using
      intervalWeightedSignalTransform_lift_eq (P := P) (beta := beta)
        (f := v t) hx

/-- Scalar factor in the derivative of the weighted signal transform. -/
lemma weightedSignalTransform_deriv_factor_mem_unit
    {P beta V : ℝ} (hbeta : 0 ≤ beta) (hbetaP : beta < P)
    (hV : 0 ≤ V) :
    0 ≤ 1 - (beta / (P + 1)) * (V / (1 + V)) ∧
      1 - (beta / (P + 1)) * (V / (1 + V)) ≤ 1 := by
  have hP1 : 0 < P + 1 := by linarith
  have hc0 : 0 ≤ beta / (P + 1) := div_nonneg hbeta hP1.le
  have hc1 : beta / (P + 1) < 1 := by
    rw [div_lt_one hP1]
    linarith
  have hbase : 0 < 1 + V := by linarith
  have hratio0 : 0 ≤ V / (1 + V) := div_nonneg hV hbase.le
  have hratio1 : V / (1 + V) ≤ 1 := by
    rw [div_le_one hbase]
    linarith
  constructor
  · have : (beta / (P + 1)) * (V / (1 + V)) ≤ 1 := by
      simpa using mul_le_mul hc1.le hratio1 hratio0 (by norm_num : (0 : ℝ) ≤ 1)
    linarith
  · exact sub_le_self _ (mul_nonneg hc0 hratio0)

/-- Pointwise derivative contraction of the weighted signal transform. -/
lemma intervalWeightedSignalTransform_deriv_abs_le
    {p : CM2Params} {T t P beta x : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hbeta : 0 ≤ beta) (hbetaP : beta < P)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    |deriv
        (intervalDomainLift (intervalWeightedSignalTransform P beta (v t))) x| ≤
      (1 + intervalDomainLift (v t) x) ^ (-(beta / (P + 1))) *
        |deriv (intervalDomainLift (v t)) x| := by
  let V : ℝ → ℝ := intervalDomainLift (v t)
  let c : ℝ := beta / (P + 1)
  let Z : ℝ → ℝ :=
    intervalDomainLift (intervalWeightedSignalTransform P beta (v t))
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hV2 : ContDiffOn ℝ 2 V (Set.Icc (0 : ℝ) 1) := by
    simpa [V] using (hsol.regularity.2.2.2.2.1 t ht).2.1
  have hVpos : 0 < V x := by
    exact intervalDomain_solution_lift_v_pos_Icc hsol ht0 htT x
      (Set.Ioo_subset_Icc_self hx)
  have hbase : 0 < 1 + V x := by linarith
  have hVderiv : HasDerivAt V (deriv V x) x :=
    (ShenWork.MinPersistenceAtoms.contDiffOn_two_hasDerivAt_pair
      isOpen_Ioo (hV2.mono Set.Ioo_subset_Icc_self) hx).1
  have hbaseDeriv : HasDerivAt (fun y => 1 + V y) (deriv V x) x := by
    exact hVderiv.const_add 1
  have hpowDeriv := hbaseDeriv.rpow_const (p := -c) (Or.inl (ne_of_gt hbase))
  have hcalc : HasDerivAt
      (fun y => V y * (1 + V y) ^ (-c))
      (deriv V x * (1 + V x) ^ (-c) +
        V x * ((-c) * (1 + V x) ^ (-c - 1) * deriv V x)) x := by
    convert hVderiv.mul hpowDeriv using 1
    ring
  have heq : Z =ᶠ[𝓝 x] (fun y => V y * (1 + V y) ^ (-c)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    simpa [Z, V, c] using
      intervalWeightedSignalTransform_lift_eq (P := P) (beta := beta)
        (f := v t) (Set.Ioo_subset_Icc_self hy)
  have hderiv : deriv Z x =
      deriv V x * (1 + V x) ^ (-c) +
        V x * ((-c) * (1 + V x) ^ (-c - 1) * deriv V x) :=
    (hcalc.congr_of_eventuallyEq heq).deriv
  have hpow_sub : (1 + V x) ^ (-c - 1) =
      (1 + V x) ^ (-c) / (1 + V x) := by
    simpa using Real.rpow_sub hbase (-c) 1
  have hfactor : deriv Z x =
      (1 + V x) ^ (-c) * (1 - c * (V x / (1 + V x))) * deriv V x := by
    rw [hderiv, hpow_sub]
    field_simp [ne_of_gt hbase]
    ring
  have hfac := weightedSignalTransform_deriv_factor_mem_unit
    hbeta hbetaP hVpos.le
  have hpow_nonneg : 0 ≤ (1 + V x) ^ (-c) := Real.rpow_nonneg hbase.le _
  rw [hfactor, abs_mul, abs_mul,
    abs_of_nonneg hpow_nonneg, abs_of_nonneg hfac.1]
  simpa [V, c, mul_assoc] using
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hfac.2 (abs_nonneg (deriv V x))) hpow_nonneg

/-- The transformed `(P+1)` power is exactly the paper's weighted signal. -/
lemma weightedSignalTransform_rpow_add_one
    {P beta V : ℝ} (hP1 : P + 1 ≠ 0) (hV : 0 ≤ V) :
    (V * (1 + V) ^ (-(beta / (P + 1)))) ^ (P + 1) =
      V ^ (P + 1) / (1 + V) ^ beta := by
  have hbase : 0 ≤ 1 + V := by linarith
  rw [Real.mul_rpow hV (Real.rpow_nonneg hbase _),
    ← Real.rpow_mul hbase]
  have hexp : -(beta / (P + 1)) * (P + 1) = -beta := by
    field_simp [hP1]
  rw [hexp, Real.rpow_neg hbase]
  simp only [div_eq_mul_inv]

/-- Algebra matching the transformed derivative weight with the elliptic
weighted-gradient integrand. -/
lemma weightedSignalTransform_gradient_weight_eq
    {P beta V D : ℝ} (hP1 : P + 1 ≠ 0) (hV : 0 ≤ V) :
    (V * (1 + V) ^ (-(beta / (P + 1)))) ^ (P - 1) *
        ((1 + V) ^ (-(beta / (P + 1))) * D) ^ 2 =
      V ^ (P - 1) / (1 + V) ^ beta * D ^ 2 := by
  have hbase : 0 ≤ 1 + V := by linarith
  have hbasepos : 0 < 1 + V := by linarith
  have hsq : ((1 + V) ^ (-(beta / (P + 1)))) ^ (2 : ℕ) =
      (1 + V) ^ (-(beta / (P + 1)) * 2) := by
    rw [← Real.rpow_mul_natCast hbase]
    norm_num
  have hexp : -(beta / (P + 1)) * (P - 1) +
      -(beta / (P + 1)) * 2 = -beta := by
    field_simp [hP1]
    ring
  have hpow :
      (1 + V) ^ (-(beta / (P + 1)) * (P - 1)) *
          (1 + V) ^ (-(beta / (P + 1)) * 2) =
        ((1 + V) ^ beta)⁻¹ := by
    rw [← Real.rpow_add hbasepos, hexp, Real.rpow_neg hbase]
  rw [Real.mul_rpow hV (Real.rpow_nonneg hbase _),
    ← Real.rpow_mul hbase, mul_pow, hsq]
  calc
    V ^ (P - 1) * (1 + V) ^ (-(beta / (P + 1)) * (P - 1)) *
          ((1 + V) ^ (-(beta / (P + 1)) * 2) * D ^ 2) =
        V ^ (P - 1) *
          ((1 + V) ^ (-(beta / (P + 1)) * (P - 1)) *
            (1 + V) ^ (-(beta / (P + 1)) * 2)) * D ^ 2 := by ring
    _ = V ^ (P - 1) / (1 + V) ^ beta * D ^ 2 := by
      rw [hpow]
      simp only [div_eq_mul_inv]

/-- The Agmon gradient integrand of the transformed signal is bounded by the
weighted elliptic-gradient integrand. -/
lemma intervalWeightedSignalTransform_gradient_pointwise_le
    {p : CM2Params} {T t P beta : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hP : 1 < P) (hbeta : 0 ≤ beta) (hbetaP : beta < P) :
    ∀ X : intervalDomain.Point,
      (intervalWeightedSignalTransform P beta (v t) X) ^ (P - 1) *
          (intervalDomain.gradNorm
            (intervalWeightedSignalTransform P beta (v t)) X) ^ 2 ≤
        (v t X) ^ (P - 1) / (1 + v t X) ^ beta *
          (intervalDomain.gradNorm (v t) X) ^ 2 := by
  intro X
  let y : ℝ := X.1
  have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := X.2
  by_cases hy0 : y = 0
  · have hX0 : (X.1 : ℝ) = 0 := by simpa [y] using hy0
    have hz0 :=
      ShenWork.IntervalFullKernelRegularity.deriv_intervalDomainLift_eq_zero_at_zero
        (intervalWeightedSignalTransform P beta (v t))
    have hv0 :=
      ShenWork.IntervalFullKernelRegularity.deriv_intervalDomainLift_eq_zero_at_zero
        (v t)
    simp [intervalDomain, intervalDomainGradNorm, hX0, hz0, hv0]
  by_cases hy1 : y = 1
  · have hX1 : (X.1 : ℝ) = 1 := by simpa [y] using hy1
    have hz1 :=
      ShenWork.IntervalFullKernelRegularity.deriv_intervalDomainLift_eq_zero_at_one
        (intervalWeightedSignalTransform P beta (v t))
    have hv1 :=
      ShenWork.IntervalFullKernelRegularity.deriv_intervalDomainLift_eq_zero_at_one
        (v t)
    simp [intervalDomain, intervalDomainGradNorm, hX1, hz1, hv1]
  have hyIoo : y ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hyIcc.1 (Ne.symm hy0), lt_of_le_of_ne hyIcc.2 hy1⟩
  have hder := intervalWeightedSignalTransform_deriv_abs_le
    hsol ht0 htT hbeta hbetaP hyIoo
  have hsq :
      |deriv
        (intervalDomainLift (intervalWeightedSignalTransform P beta (v t))) y| ^ 2 ≤
      ((1 + intervalDomainLift (v t) y) ^ (-(beta / (P + 1))) *
        |deriv (intervalDomainLift (v t)) y|) ^ 2 := by
    exact (sq_le_sq₀ (abs_nonneg _)
      (mul_nonneg (Real.rpow_nonneg (by
        linarith [intervalDomain_solution_lift_v_pos_Icc hsol ht0 htT y hyIcc]) _)
        (abs_nonneg _))).2 hder
  have hz_nonneg : 0 ≤
      (intervalDomainLift (v t) y *
        (1 + intervalDomainLift (v t) y) ^ (-(beta / (P + 1)))) ^ (P - 1) :=
    Real.rpow_nonneg
      (mul_nonneg
        (intervalDomain_solution_lift_v_pos_Icc hsol ht0 htT y hyIcc).le
        (Real.rpow_nonneg (by
          linarith [intervalDomain_solution_lift_v_pos_Icc hsol ht0 htT y hyIcc]) _)) _
  have hmul := mul_le_mul_of_nonneg_left hsq hz_nonneg
  have halg := weightedSignalTransform_gradient_weight_eq
    (P := P) (beta := beta)
    (V := intervalDomainLift (v t) y)
    (D := |deriv (intervalDomainLift (v t)) y|)
    (by linarith : P + 1 ≠ 0)
    (intervalDomain_solution_lift_v_pos_Icc hsol ht0 htT y hyIcc).le
  simpa [intervalDomain, intervalDomainGradNorm,
    intervalWeightedSignalTransform, intervalDomainLift, hyIcc,
    sq_abs] using (hmul.trans_eq halg)

/-- Positivity of the derivative of the elliptic multiplier
`V^P (1+V)^(-β)`, with the sharp factor `P-β`. -/
lemma weightedSignalMultiplier_deriv_lower
    {P beta V D : ℝ} (hbeta : 0 ≤ beta)
    (hV : 0 ≤ V) :
    (P - beta) * (V ^ (P - 1) * (1 + V) ^ (-beta) * D ^ 2) ≤
      V ^ (P - 1) * (1 + V) ^ (-beta - 1) *
        (P + (P - beta) * V) * D ^ 2 := by
  have hbase : 0 < 1 + V := by linarith
  have hpowV : 0 ≤ V ^ (P - 1) := Real.rpow_nonneg hV _
  have hpowBase : 0 ≤ (1 + V) ^ (-beta - 1) :=
    Real.rpow_nonneg hbase.le _
  have hD : 0 ≤ D ^ 2 := sq_nonneg D
  have hrel : (1 + V) ^ (-beta) =
      (1 + V) ^ (-beta - 1) * (1 + V) := by
    calc
      (1 + V) ^ (-beta) = (1 + V) ^ ((-beta - 1) + 1) := by ring_nf
      _ = (1 + V) ^ (-beta - 1) * (1 + V) ^ (1 : ℝ) :=
        Real.rpow_add hbase _ _
      _ = (1 + V) ^ (-beta - 1) * (1 + V) := by rw [Real.rpow_one]
  rw [hrel]
  let H := V ^ (P - 1) * (1 + V) ^ (-beta - 1) * D ^ 2
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hcoef : (P - beta) * (1 + V) ≤ P + (P - beta) * V := by
    nlinarith
  calc
    (P - beta) *
        (V ^ (P - 1) * ((1 + V) ^ (-beta - 1) * (1 + V)) * D ^ 2) =
      ((P - beta) * (1 + V)) * H := by ring
    _ ≤ (P + (P - beta) * V) * H :=
      mul_le_mul_of_nonneg_right hcoef hH
    _ = V ^ (P - 1) * (1 + V) ^ (-beta - 1) *
        (P + (P - beta) * V) * D ^ 2 := by ring

/-- Weighted elliptic multiplier identity underlying Proposition 2.3. -/
lemma intervalDomain_weightedSignal_gradient_preestimate
    {p : CM2Params} {T t P : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    (P - p.β) *
        (∫ x in (0 : ℝ)..1,
          intervalDomainLift (v t) x ^ (P - 1) *
            (1 + intervalDomainLift (v t) x) ^ (-p.β) *
              deriv (intervalDomainLift (v t)) x ^ 2) +
      p.μ * (∫ x in (0 : ℝ)..1,
        intervalDomainLift (v t) x ^ (P + 1) *
          (1 + intervalDomainLift (v t) x) ^ (-p.β)) ≤
    p.ν * (∫ x in (0 : ℝ)..1,
      intervalDomainLift (u t) x ^ p.γ *
        intervalDomainLift (v t) x ^ P *
          (1 + intervalDomainLift (v t) x) ^ (-p.β)) := by
  let V : ℝ → ℝ := intervalDomainLift (v t)
  let U : ℝ → ℝ := intervalDomainLift (u t)
  let W : ℝ → ℝ := fun x => V x ^ P * (1 + V x) ^ (-p.β)
  let W' : ℝ → ℝ := fun x =>
    V x ^ (P - 1) * (1 + V x) ^ (-p.β - 1) *
      (P + (P - p.β) * V x) * deriv V x
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hV2 : ContDiffOn ℝ 2 V (Set.Icc (0 : ℝ) 1) := by
    simpa [V] using (hsol.regularity.2.2.2.2.1 t ht).2.1
  have hVpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < V x := by
    simpa [V] using intervalDomain_solution_lift_v_pos_Icc hsol ht0 htT
  have hUpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < U x := by
    intro x hx
    simpa [U] using solution_lift_pos hsol ht x hx
  have hdVcont : ContinuousOn (deriv V) (Set.Icc (0 : ℝ) 1) := by
    simpa [V] using
      (resolverGradReal_contDiffOn_Icc hsol ht).continuousOn.congr
        (fun x hx => solution_lift_v_deriv_eq_resolverGrad_Icc hsol ht hx)
  have hbase_ne : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ((fun _ : ℝ => (1 : ℝ)) + V) x ≠ 0 := by
    intro x hx
    simpa only [Pi.add_apply] using
      ne_of_gt (show 0 < 1 + V x by linarith [hVpos x hx])
  have hWcont : ContinuousOn W (Set.Icc (0 : ℝ) 1) := by
    exact (hV2.continuousOn.rpow_const
      (fun x hx => Or.inl (ne_of_gt (hVpos x hx)))).mul
        ((continuousOn_const.add hV2.continuousOn).rpow_const
          (fun x hx => Or.inl (hbase_ne x hx)))
  have hW'cont : ContinuousOn W' (Set.Icc (0 : ℝ) 1) := by
    exact ((((hV2.continuousOn.rpow_const
      (fun x hx => Or.inl (ne_of_gt (hVpos x hx)))).mul
        ((continuousOn_const.add hV2.continuousOn).rpow_const
          (fun x hx => Or.inl (hbase_ne x hx)))).mul
            (continuousOn_const.add
              (continuousOn_const.mul hV2.continuousOn))).mul hdVcont)
  have hWderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt W (W' x) x := by
    intro x hx
    have hxIcc := Set.Ioo_subset_Icc_self hx
    have hVderiv :=
      (ShenWork.MinPersistenceAtoms.contDiffOn_two_hasDerivAt_pair
        isOpen_Ioo (hV2.mono Set.Ioo_subset_Icc_self) hx).1
    have hbaseDeriv : HasDerivAt (fun y => 1 + V y) (deriv V x) x :=
      hVderiv.const_add 1
    have hraw := (hVderiv.rpow_const (p := P)
      (Or.inl (ne_of_gt (hVpos x hxIcc)))).mul
        (hbaseDeriv.rpow_const (p := -p.β)
          (Or.inl (ne_of_gt (by linarith [hVpos x hxIcc]))))
    have hVpow : V x ^ P = V x ^ (P - 1) * V x := by
      calc
        V x ^ P = V x ^ ((P - 1) + 1) := by ring_nf
        _ = V x ^ (P - 1) * V x ^ (1 : ℝ) :=
          Real.rpow_add (hVpos x hxIcc) _ _
        _ = V x ^ (P - 1) * V x := by rw [Real.rpow_one]
    have hBpow : (1 + V x) ^ (-p.β) =
        (1 + V x) ^ (-p.β - 1) * (1 + V x) := by
      calc
        (1 + V x) ^ (-p.β) = (1 + V x) ^ ((-p.β - 1) + 1) := by ring_nf
        _ = (1 + V x) ^ (-p.β - 1) * (1 + V x) ^ (1 : ℝ) :=
          Real.rpow_add (by linarith [hVpos x hxIcc]) _ _
        _ = (1 + V x) ^ (-p.β - 1) * (1 + V x) := by rw [Real.rpow_one]
    have hrawW : HasDerivAt W
        (deriv V x * P * V x ^ (P - 1) * (1 + V x) ^ (-p.β) +
          V x ^ P * (deriv V x * -p.β *
            (1 + V x) ^ (-p.β - 1))) x := by
      simpa [W] using hraw
    exact hrawW.congr_deriv (by
      dsimp [W']
      rw [hVpow, hBpow]
      ring)
  have hV2deriv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (deriv V) (deriv (deriv V) x) x := by
    intro x hx
    exact (ShenWork.MinPersistenceAtoms.contDiffOn_two_hasDerivAt_pair
      isOpen_Ioo (hV2.mono Set.Ioo_subset_Icc_self) hx).2
  have hW'int : IntervalIntegrable W' volume 0 1 := by
    have hc : ContinuousOn W' (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hW'cont
    exact hc.intervalIntegrable
  have hV2int : IntervalIntegrable (deriv (deriv V)) volume 0 1 :=
    intervalIntegrable_deriv_deriv_of_contDiffOn_two hV2
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (u := W) (v := deriv V)
    (u' := W') (v' := deriv (deriv V))
    (by simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hWcont)
    (by simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hdVcont)
    (by simpa using hWderiv) (by simpa using hV2deriv) hW'int hV2int
  have hNeu0 : deriv V 0 = 0 := by
    simpa [V] using (hsol.regularity.2.2.2.2.1 t ht).2.2.1
  have hNeu1 : deriv V 1 = 0 := by
    simpa [V] using (hsol.regularity.2.2.2.2.1 t ht).2.2.2
  have hgradlower :
      (P - p.β) * (∫ x in (0 : ℝ)..1,
        V x ^ (P - 1) * (1 + V x) ^ (-p.β) * deriv V x ^ 2) ≤
        ∫ x in (0 : ℝ)..1, W' x * deriv V x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (by norm_num)
    · have hc : ContinuousOn
          (fun x => (P - p.β) *
            (V x ^ (P - 1) * (1 + V x) ^ (-p.β) * deriv V x ^ 2))
          (Set.uIcc (0 : ℝ) 1) := by
        rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        exact ((((hV2.continuousOn.rpow_const
            (fun x hx => Or.inl (ne_of_gt (hVpos x hx)))).mul
          ((continuousOn_const.add hV2.continuousOn).rpow_const
            (fun x hx => Or.inl (hbase_ne x hx)))).mul
              (hdVcont.pow 2)).const_mul (P - p.β))
      exact hc.intervalIntegrable
    · have hc : ContinuousOn (fun x => W' x * deriv V x)
          (Set.uIcc (0 : ℝ) 1) := by
        rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        exact hW'cont.mul hdVcont
      exact hc.intervalIntegrable
    · intro x hx
      dsimp [W']
      simpa [mul_assoc, pow_two] using weightedSignalMultiplier_deriv_lower
        (P := P) (beta := p.β) (V := V x) (D := deriv V x)
        p.hβ (hVpos x hx).le
  have hlap_upper :
      (∫ x in (0 : ℝ)..1, W x * deriv (deriv V) x) ≤
        -(P - p.β) * (∫ x in (0 : ℝ)..1,
          V x ^ (P - 1) * (1 + V x) ^ (-p.β) * deriv V x ^ 2) := by
    rw [hIBP, hNeu0, hNeu1]
    linarith
  have hPDE :
      (∫ x in (0 : ℝ)..1, W x * deriv (deriv V) x) =
        ∫ x in (0 : ℝ)..1,
          p.μ * (V x ^ (P + 1) * (1 + V x) ^ (-p.β)) -
            p.ν * (U x ^ p.γ * V x ^ P * (1 + V x) ^ (-p.β)) := by
    apply intervalIntegral.integral_congr_ae
    rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    have hnull : volume ({(1 : ℝ)} : Set ℝ) = 0 := by simp
    refine (MeasureTheory.ae_iff).2 (measure_mono_null ?_ hnull)
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    push Not at hx
    obtain ⟨hxIoc, hne⟩ := hx
    simp only [Set.mem_singleton_iff]
    by_contra hx1
    have hxoo : x ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨hxIoc.1, lt_of_le_of_ne hxIoc.2 hx1⟩
    apply hne
    have hpde : deriv (deriv V) x = p.μ * V x - p.ν * U x ^ p.γ := by
      simpa [V, U] using
        intervalDomain_v_xx_eq_reaction_lift hsol ht0 htT hxoo.1 hxoo.2
    have hVpow : V x ^ P * V x = V x ^ (P + 1) := by
      calc
        V x ^ P * V x = V x ^ P * V x ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = V x ^ (P + 1) :=
          (Real.rpow_add (hVpos x (Set.Ioo_subset_Icc_self hxoo)) _ _).symm
    dsimp [W]
    rw [hpde]
    rw [← hVpow]
    ring
  rw [hPDE] at hlap_upper
  have hVtermInt : IntervalIntegrable
      (fun x => V x ^ (P + 1) * (1 + V x) ^ (-p.β)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact (hV2.continuousOn.rpow_const
      (fun x hx => Or.inl (ne_of_gt (hVpos x hx)))).mul
        ((continuousOn_const.add hV2.continuousOn).rpow_const
          (fun x hx => Or.inl (hbase_ne x hx)))
  have hUcont : ContinuousOn U (Set.Icc (0 : ℝ) 1) := by
    simpa [U] using (hsol.regularity.2.2.2.2.1 t ht).1.1.continuousOn
  have hCrossInt : IntervalIntegrable
      (fun x => U x ^ p.γ * V x ^ P * (1 + V x) ^ (-p.β)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ((hUcont.rpow_const
      (fun x hx => Or.inl (ne_of_gt (hUpos x hx)))).mul
        (hV2.continuousOn.rpow_const
          (fun x hx => Or.inl (ne_of_gt (hVpos x hx))))).mul
            ((continuousOn_const.add hV2.continuousOn).rpow_const
              (fun x hx => Or.inl (hbase_ne x hx)))
  rw [intervalIntegral.integral_sub (hVtermInt.const_mul p.μ)
      (hCrossInt.const_mul p.ν),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hlap_upper
  dsimp [V, U] at hlap_upper ⊢
  linarith

/-- Pointwise Young absorption preserving the exact signal weight. -/
lemma weightedSignal_source_young
    {mu nu P beta gamma U V C : ℝ}
    (hP : 1 < P) (hU : 0 < U) (hV : 0 < V)
    (hY : ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      nu * A * B ^ P ≤ mu / 2 * B ^ (P + 1) + C * A ^ (P + 1)) :
    nu * (U ^ gamma * V ^ P * (1 + V) ^ (-beta)) ≤
      mu / 2 * (V ^ (P + 1) * (1 + V) ^ (-beta)) +
        C * (U ^ (gamma * (P + 1)) * (1 + V) ^ (-beta)) := by
  let c : ℝ := beta / (P + 1)
  let A : ℝ := U ^ gamma * (1 + V) ^ (-c)
  let B : ℝ := V * (1 + V) ^ (-c)
  have hP1 : P + 1 ≠ 0 := by linarith
  have hbase : 0 < 1 + V := by linarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hy := hY A B hA hB
  have hBpowP : B ^ P = V ^ P * (1 + V) ^ (-c * P) := by
    dsimp [B]
    rw [Real.mul_rpow hV.le (Real.rpow_nonneg hbase.le _),
      ← Real.rpow_mul hbase.le]
  have hweight : (1 + V) ^ (-c) * (1 + V) ^ (-c * P) =
      (1 + V) ^ (-beta) := by
    rw [← Real.rpow_add hbase]
    congr 1
    dsimp [c]
    field_simp [hP1]
    ring
  have hleft : nu * A * B ^ P =
      nu * (U ^ gamma * V ^ P * (1 + V) ^ (-beta)) := by
    rw [hBpowP]
    dsimp [A]
    calc
      nu * (U ^ gamma * (1 + V) ^ (-c)) *
          (V ^ P * (1 + V) ^ (-c * P)) =
        nu * (U ^ gamma * V ^ P *
          ((1 + V) ^ (-c) * (1 + V) ^ (-c * P))) := by ring
      _ = nu * (U ^ gamma * V ^ P * (1 + V) ^ (-beta)) := by rw [hweight]
  have hBpow : B ^ (P + 1) =
      V ^ (P + 1) * (1 + V) ^ (-beta) := by
    calc
      B ^ (P + 1) = V ^ (P + 1) / (1 + V) ^ beta := by
        simpa [B, c] using
          weightedSignalTransform_rpow_add_one
            (P := P) (beta := beta) (V := V) hP1 hV.le
      _ = V ^ (P + 1) * (1 + V) ^ (-beta) := by
        rw [Real.rpow_neg hbase.le]
        simp only [div_eq_mul_inv]
  have hApow : A ^ (P + 1) =
      U ^ (gamma * (P + 1)) * (1 + V) ^ (-beta) := by
    dsimp [A]
    rw [Real.mul_rpow (Real.rpow_nonneg hU.le _)
        (Real.rpow_nonneg hbase.le _),
      ← Real.rpow_mul hU.le, ← Real.rpow_mul hbase.le]
    congr 1
    dsimp [c]
    field_simp [hP1]
  rw [hleft, hBpow, hApow] at hy
  exact hy

/-- The weighted signal-gradient term is controlled by the weighted source
moment, uniformly in time. -/
lemma intervalDomain_weightedSignal_gradient_bound
    {p : CM2Params} {T P : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hP : 1 < P) (hbetaP : p.β < P) :
    ∃ Cgrad > 0, ∀ t, 0 < t → t < T →
      (∫ x in (0 : ℝ)..1,
        intervalDomainLift (v t) x ^ (P - 1) *
          (1 + intervalDomainLift (v t) x) ^ (-p.β) *
            deriv (intervalDomainLift (v t)) x ^ 2) ≤
        Cgrad * (∫ x in (0 : ℝ)..1,
          intervalDomainLift (u t) x ^ (p.γ * (P + 1)) *
            (1 + intervalDomainLift (v t) x) ^ (-p.β)) := by
  obtain ⟨C0, hC0, hY⟩ :=
    elliptic_source_young_exists p.hμ p.hν (by linarith : 1 < P + 1)
  let Cgrad : ℝ := C0 / (P - p.β)
  have hden : 0 < P - p.β := sub_pos.mpr hbetaP
  have hCgrad : 0 < Cgrad := div_pos hC0 hden
  refine ⟨Cgrad, hCgrad, ?_⟩
  intro t ht0 htT
  let V : ℝ → ℝ := intervalDomainLift (v t)
  let U : ℝ → ℝ := intervalDomainLift (u t)
  let G : ℝ := ∫ x in (0 : ℝ)..1,
    V x ^ (P - 1) * (1 + V x) ^ (-p.β) * deriv V x ^ 2
  let A : ℝ := ∫ x in (0 : ℝ)..1,
    V x ^ (P + 1) * (1 + V x) ^ (-p.β)
  let B : ℝ := ∫ x in (0 : ℝ)..1,
    U x ^ (p.γ * (P + 1)) * (1 + V x) ^ (-p.β)
  let Cross : ℝ := ∫ x in (0 : ℝ)..1,
    U x ^ p.γ * V x ^ P * (1 + V x) ^ (-p.β)
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hV2 : ContDiffOn ℝ 2 V (Set.Icc (0 : ℝ) 1) := by
    simpa [V] using (hsol.regularity.2.2.2.2.1 t ht).2.1
  have hUcont : ContinuousOn U (Set.Icc (0 : ℝ) 1) := by
    simpa [U] using (hsol.regularity.2.2.2.2.1 t ht).1.1.continuousOn
  have hVpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < V x := by
    simpa [V] using intervalDomain_solution_lift_v_pos_Icc hsol ht0 htT
  have hUpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < U x := by
    intro x hx
    simpa [U] using solution_lift_pos hsol ht x hx
  have hbase_ne : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ((fun _ : ℝ => (1 : ℝ)) + V) x ≠ 0 := by
    intro x hx
    simpa only [Pi.add_apply] using
      ne_of_gt (show 0 < 1 + V x by linarith [hVpos x hx])
  have hbasecont : ContinuousOn (fun x => (1 + V x) ^ (-p.β))
      (Set.Icc (0 : ℝ) 1) :=
    (continuousOn_const.add hV2.continuousOn).rpow_const
      (fun x hx => Or.inl (hbase_ne x hx))
  have hAint : IntervalIntegrable
      (fun x => V x ^ (P + 1) * (1 + V x) ^ (-p.β)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact (hV2.continuousOn.rpow_const
      (fun x hx => Or.inl (ne_of_gt (hVpos x hx)))).mul hbasecont
  have hBint : IntervalIntegrable
      (fun x => U x ^ (p.γ * (P + 1)) *
        (1 + V x) ^ (-p.β)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact (hUcont.rpow_const
      (fun x hx => Or.inl (ne_of_gt (hUpos x hx)))).mul hbasecont
  have hCrossInt : IntervalIntegrable
      (fun x => U x ^ p.γ * V x ^ P *
        (1 + V x) ^ (-p.β)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ((hUcont.rpow_const
      (fun x hx => Or.inl (ne_of_gt (hUpos x hx)))).mul
        (hV2.continuousOn.rpow_const
          (fun x hx => Or.inl (ne_of_gt (hVpos x hx))))).mul hbasecont
  have hYoungInt : p.ν * Cross ≤ p.μ / 2 * A + C0 * B := by
    have hY' : ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
        p.ν * A * B ^ P ≤
          p.μ / 2 * B ^ (P + 1) + C0 * A ^ (P + 1) := by
      intro X Y hX hY0
      simpa using hY X Y hX hY0
    dsimp [Cross, A, B]
    calc
      p.ν * (∫ x in (0 : ℝ)..1,
          U x ^ p.γ * V x ^ P * (1 + V x) ^ (-p.β)) =
        ∫ x in (0 : ℝ)..1,
          p.ν * (U x ^ p.γ * V x ^ P * (1 + V x) ^ (-p.β)) :=
            by rw [intervalIntegral.integral_const_mul]
      _ ≤ ∫ x in (0 : ℝ)..1,
          p.μ / 2 * (V x ^ (P + 1) * (1 + V x) ^ (-p.β)) +
            C0 * (U x ^ (p.γ * (P + 1)) *
              (1 + V x) ^ (-p.β)) :=
        intervalIntegral.integral_mono_on (by norm_num)
          (hCrossInt.const_mul p.ν)
          ((hAint.const_mul (p.μ / 2)).add (hBint.const_mul C0))
          (fun x hx => weightedSignal_source_young hP
            (hUpos x hx) (hVpos x hx) hY')
      _ = p.μ / 2 * (∫ x in (0 : ℝ)..1,
          V x ^ (P + 1) * (1 + V x) ^ (-p.β)) +
            C0 * (∫ x in (0 : ℝ)..1,
              U x ^ (p.γ * (P + 1)) * (1 + V x) ^ (-p.β)) := by
        rw [intervalIntegral.integral_add
            (hAint.const_mul (p.μ / 2)) (hBint.const_mul C0),
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
  have hpre := intervalDomain_weightedSignal_gradient_preestimate
    (P := P) hsol ht0 htT
  have hpre' : (P - p.β) * G + p.μ * A ≤ p.ν * Cross := by
    simpa [G, A, Cross, V, U] using hpre
  have hAnonneg : 0 ≤ A := by
    dsimp [A]
    exact intervalIntegral.integral_nonneg (by norm_num) fun x hx =>
      mul_nonneg (Real.rpow_nonneg (hVpos x hx).le _)
        (Real.rpow_nonneg (by linarith [hVpos x hx]) _)
  have hGB : (P - p.β) * G ≤ C0 * B := by
    nlinarith [mul_nonneg p.hμ.le hAnonneg]
  dsimp [Cgrad]
  change G ≤ C0 / (P - p.β) * B
  rw [show C0 / (P - p.β) * B = (C0 * B) / (P - p.β) by ring]
  exact (le_div_iff₀ hden).2 (by simpa [mul_comm] using hGB)

/-- Endpoint-safe integrability of the ordinary weighted gradient integrand
for a positive closed-`C²` interval function. -/
lemma intervalDomainLift_rpow_grad_sq_intervalIntegrable
    {q : ℝ} (hq : q ≠ 0) {f : intervalDomain.Point → ℝ}
    (hfpos : ∀ X, 0 < f X)
    (hfC2 : ContDiffOn ℝ 2 (intervalDomainLift f) (Set.Icc (0 : ℝ) 1)) :
    IntervalIntegrable
      (fun x => intervalDomainLift f x ^ (q - 2) *
        deriv (intervalDomainLift f) x ^ 2) volume 0 1 := by
  have hchain := intervalDomainLift_rpow_deriv_sq_intervalIntegrable
    (q := q) hfpos hfC2
  have hq2 : q ^ 2 ≠ 0 := pow_ne_zero 2 hq
  have hscaled := hchain.const_mul (4 / q ^ 2)
  refine hscaled.congr ?_
  intro x hx
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := by
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    exact ⟨le_of_lt hx.1, hx.2⟩
  have hfactor := rpow_half_deriv_sq_factor
    (a := intervalDomainLift f x) (b := deriv (intervalDomainLift f) x) (q := q)
    (intervalDomainLift_pos_on_Icc hfpos x hxIcc).le
  dsimp
  rw [hfactor]
  field_simp [hq2]

/-- Integral version of the transformed-gradient contraction. -/
lemma intervalDomain_weightedSignalTransform_gradient_integral_le
    {p : CM2Params} {T t P : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hP : 1 < P) (hbetaP : p.β < P) :
    intervalDomain.integral (fun X =>
      (intervalWeightedSignalTransform P p.β (v t) X) ^ (P - 1) *
        (intervalDomain.gradNorm
          (intervalWeightedSignalTransform P p.β (v t)) X) ^ 2) ≤
      ∫ x in (0 : ℝ)..1,
        intervalDomainLift (v t) x ^ (P - 1) *
          (1 + intervalDomainLift (v t) x) ^ (-p.β) *
            deriv (intervalDomainLift (v t)) x ^ 2 := by
  let z : intervalDomain.Point → ℝ :=
    intervalWeightedSignalTransform P p.β (v t)
  let Z : ℝ → ℝ := intervalDomainLift z
  let V : ℝ → ℝ := intervalDomainLift (v t)
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hzpos : ∀ X, 0 < z X := by
    exact intervalWeightedSignalTransform_pos
      (fun X => by
        have hv := intervalDomain_solution_lift_v_pos_Icc hsol ht0 htT X.1 X.2
        simpa [intervalDomainLift, X.2] using hv)
  have hzC2 : ContDiffOn ℝ 2 Z (Set.Icc (0 : ℝ) 1) := by
    simpa [z, Z] using
      intervalWeightedSignalTransform_contDiffOn_two
        (P := P) (beta := p.β) hsol ht0 htT
  have hleftActual : IntervalIntegrable
      (fun x => Z x ^ (P - 1) * deriv Z x ^ 2) volume 0 1 := by
    simpa [show P + 1 - 2 = P - 1 by ring] using
      intervalDomainLift_rpow_grad_sq_intervalIntegrable
        (q := P + 1) (by linarith) hzpos hzC2
  have hleftInt : IntervalIntegrable
      (intervalDomainLift (fun X => z X ^ (P - 1) *
        (intervalDomain.gradNorm z X) ^ 2)) volume 0 1 := by
    refine hleftActual.congr ?_
    intro x hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := by
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      exact ⟨le_of_lt hx.1, hx.2⟩
    simp [z, Z, intervalDomainLift, intervalDomain,
      intervalDomainGradNorm, hxIcc, sq_abs]
  have hV2 : ContDiffOn ℝ 2 V (Set.Icc (0 : ℝ) 1) := by
    simpa [V] using (hsol.regularity.2.2.2.2.1 t ht).2.1
  have hVpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < V x := by
    simpa [V] using intervalDomain_solution_lift_v_pos_Icc hsol ht0 htT
  have hdVcont : ContinuousOn (deriv V) (Set.Icc (0 : ℝ) 1) := by
    simpa [V] using
      (resolverGradReal_contDiffOn_Icc hsol ht).continuousOn.congr
        (fun x hx => solution_lift_v_deriv_eq_resolverGrad_Icc hsol ht hx)
  have hrightInt : IntervalIntegrable
      (fun x => V x ^ (P - 1) * (1 + V x) ^ (-p.β) *
        deriv V x ^ 2) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ((hV2.continuousOn.rpow_const
      (fun x hx => Or.inl (ne_of_gt (hVpos x hx)))).mul
        ((continuousOn_const.add hV2.continuousOn).rpow_const
          (fun x hx => Or.inl (ne_of_gt (by
            have : 0 < 1 + V x := by linarith [hVpos x hx]
            simpa only [Pi.add_apply] using this))))).mul (hdVcont.pow 2)
  change (∫ x in (0 : ℝ)..1,
      intervalDomainLift (fun X => z X ^ (P - 1) *
        (intervalDomain.gradNorm z X) ^ 2) x) ≤
    ∫ x in (0 : ℝ)..1,
      V x ^ (P - 1) * (1 + V x) ^ (-p.β) * deriv V x ^ 2
  exact intervalIntegral.integral_mono_on (by norm_num) hleftInt hrightInt
    (fun x hx => by
      let X : intervalDomain.Point := ⟨x, hx⟩
      have hpoint := intervalWeightedSignalTransform_gradient_pointwise_le
        hsol ht0 htT hP p.hβ hbetaP X
      have hvX : 0 < v t X := by
        have hv := intervalDomain_solution_lift_v_pos_Icc hsol ht0 htT x hx
        simpa [X, intervalDomainLift, hx] using hv
      simp only [div_eq_mul_inv] at hpoint
      rw [← Real.rpow_neg (by linarith [hvX] : 0 ≤ 1 + v t X)] at hpoint
      simpa [X, z, Z, V, intervalDomainLift, intervalDomain,
        intervalDomainGradNorm, hx, sq_abs] using hpoint)

/-- Rewrite an abstract weighted interval power integral as its concrete lift
integral with a negative real-power weight. -/
lemma intervalDomain_weightedPower_integral_eq_lift
    {p : CM2Params} {T t a : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (f : intervalDomain.Point → ℝ) :
    intervalDomain.integral
        (fun X => f X ^ a / (1 + v t X) ^ p.β) =
      ∫ x in (0 : ℝ)..1,
        intervalDomainLift f x ^ a *
          (1 + intervalDomainLift (v t) x) ^ (-p.β) := by
  change (∫ x in (0 : ℝ)..1,
      intervalDomainLift (fun X => f X ^ a / (1 + v t X) ^ p.β) x) = _
  apply intervalIntegral.integral_congr
  intro x hx
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
  let X : intervalDomain.Point := ⟨x, hxIcc⟩
  have hvX : 0 < v t X := by
    have hv := intervalDomain_solution_lift_v_pos_Icc hsol ht0 htT x hxIcc
    simpa [X, intervalDomainLift, hxIcc] using hv
  simp only [intervalDomainLift, hxIcc, dif_pos]
  change f X ^ a / (1 + v t X) ^ p.β =
    f X ^ a * (1 + v t X) ^ (-p.β)
  rw [Real.rpow_neg (by linarith [hvX] : 0 ≤ 1 + v t X)]
  simp only [div_eq_mul_inv]

/-- The transformed signal moment is exactly the weighted signal moment. -/
lemma intervalDomain_weightedSignalTransform_power_integral_eq
    {p : CM2Params} {T t P : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht0 : 0 < t) (htT : t < T) (hP : 1 < P) :
    intervalDomain.integral (fun X =>
      (intervalWeightedSignalTransform P p.β (v t) X) ^ (P + 1)) =
    intervalDomain.integral (fun X =>
      (v t X) ^ (P + 1) / (1 + v t X) ^ p.β) := by
  change (∫ x in (0 : ℝ)..1,
      intervalDomainLift (fun X =>
        intervalWeightedSignalTransform P p.β (v t) X ^ (P + 1)) x) =
    ∫ x in (0 : ℝ)..1,
      intervalDomainLift (fun X =>
        v t X ^ (P + 1) / (1 + v t X) ^ p.β) x
  apply intervalIntegral.integral_congr
  intro x hx
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
  let X : intervalDomain.Point := ⟨x, hxIcc⟩
  have hvX : 0 ≤ v t X := by
    have hv := intervalDomain_solution_lift_v_pos_Icc hsol ht0 htT x hxIcc
    simpa [X, intervalDomainLift, hxIcc] using hv.le
  simpa [X, intervalWeightedSignalTransform, intervalDomainLift, hxIcc] using
    weightedSignalTransform_rpow_add_one
      (P := P) (beta := p.β) (V := v t X) (by linarith) hvX

/-- The transformed mass is the last integral in Proposition 2.3. -/
lemma intervalDomain_weightedSignalTransform_mass_integral_eq
    {p : CM2Params} {T t P : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    intervalDomain.integral (intervalWeightedSignalTransform P p.β (v t)) =
      intervalDomain.integral
        (fun X => v t X / (1 + v t X) ^ (p.β / (P + 1))) := by
  change (∫ x in (0 : ℝ)..1,
      intervalDomainLift (intervalWeightedSignalTransform P p.β (v t)) x) =
    ∫ x in (0 : ℝ)..1,
      intervalDomainLift
        (fun X => v t X / (1 + v t X) ^ (p.β / (P + 1))) x
  apply intervalIntegral.integral_congr
  intro x hx
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
  let X : intervalDomain.Point := ⟨x, hxIcc⟩
  have hvX : 0 < v t X := by
    have hv := intervalDomain_solution_lift_v_pos_Icc hsol ht0 htT x hxIcc
    simpa [X, intervalDomainLift, hxIcc] using hv
  simp only [intervalDomainLift, hxIcc, dif_pos]
  change v t X * (1 + v t X) ^ (-(p.β / (P + 1))) =
    v t X / (1 + v t X) ^ (p.β / (P + 1))
  rw [Real.rpow_neg (by linarith [hvX] : 0 ≤ 1 + v t X)]
  simp only [div_eq_mul_inv]

/-- Genuine interval-domain realization of Paper 2, Proposition 2.3. -/
theorem intervalDomain_Proposition_2_3 (p : CM2Params) :
    Proposition_2_3 intervalDomain p := by
  intro T _hT u v hsol P hPmax eps heps
  have hP : 1 < P := lt_of_le_of_lt (le_max_left _ _) hPmax
  have hbetaP : p.β < P := lt_of_le_of_lt (le_max_right _ _) hPmax
  obtain ⟨Cgrad, hCgrad, hgrad⟩ :=
    intervalDomain_weightedSignal_gradient_bound hsol hP hbetaP
  let delta : ℝ := eps / Cgrad
  have hdelta : 0 < delta := div_pos heps hCgrad
  obtain ⟨Ceps, hCeps, hagmon⟩ :=
    unitIntervalPositiveAgmonInterpolation (P + 1) (by linarith) delta hdelta
  refine ⟨Ceps, hCeps, ?_⟩
  intro t ht0 htT
  let z : intervalDomain.Point → ℝ :=
    intervalWeightedSignalTransform P p.β (v t)
  have hzpos : ∀ X, 0 < z X := by
    exact intervalWeightedSignalTransform_pos
      (fun X => by
        have hv := intervalDomain_solution_lift_v_pos_Icc hsol ht0 htT X.1 X.2
        simpa [intervalDomainLift, X.2] using hv)
  have hzC2 : ContDiffOn ℝ 2 (intervalDomainLift z)
      (Set.Icc (0 : ℝ) 1) := by
    simpa [z] using
      intervalWeightedSignalTransform_contDiffOn_two
        (P := P) (beta := p.β) hsol ht0 htT
  have hag := hagmon z hzpos hzC2
  have htrans := intervalDomain_weightedSignalTransform_gradient_integral_le
    hsol ht0 htT hP hbetaP
  have hG := hgrad t ht0 htT
  have hsourceEq := intervalDomain_weightedPower_integral_eq_lift
    (p := p) (a := p.γ * (P + 1)) hsol ht0 htT (u t)
  have hdeltaC : delta * Cgrad = eps := by
    dsimp [delta]
    field_simp [ne_of_gt hCgrad]
  have hgradSource :
      delta * intervalDomain.integral (fun X =>
        z X ^ (P - 1) * (intervalDomain.gradNorm z X) ^ 2) ≤
      eps * intervalDomain.integral (fun X =>
        (u t X) ^ (p.γ * (P + 1)) / (1 + v t X) ^ p.β) := by
    calc
      delta * intervalDomain.integral (fun X =>
          z X ^ (P - 1) * (intervalDomain.gradNorm z X) ^ 2) ≤
        delta * (∫ x in (0 : ℝ)..1,
          intervalDomainLift (v t) x ^ (P - 1) *
            (1 + intervalDomainLift (v t) x) ^ (-p.β) *
              deriv (intervalDomainLift (v t)) x ^ 2) :=
        mul_le_mul_of_nonneg_left (by simpa [z] using htrans) hdelta.le
      _ ≤ delta * (Cgrad * (∫ x in (0 : ℝ)..1,
          intervalDomainLift (u t) x ^ (p.γ * (P + 1)) *
            (1 + intervalDomainLift (v t) x) ^ (-p.β))) :=
        mul_le_mul_of_nonneg_left hG hdelta.le
      _ = eps * intervalDomain.integral (fun X =>
          (u t X) ^ (p.γ * (P + 1)) / (1 + v t X) ^ p.β) := by
        calc
          delta * (Cgrad * (∫ x in (0 : ℝ)..1,
              intervalDomainLift (u t) x ^ (p.γ * (P + 1)) *
                (1 + intervalDomainLift (v t) x) ^ (-p.β))) =
            (delta * Cgrad) * (∫ x in (0 : ℝ)..1,
              intervalDomainLift (u t) x ^ (p.γ * (P + 1)) *
                (1 + intervalDomainLift (v t) x) ^ (-p.β)) := by ring
          _ = eps * (∫ x in (0 : ℝ)..1,
              intervalDomainLift (u t) x ^ (p.γ * (P + 1)) *
                (1 + intervalDomainLift (v t) x) ^ (-p.β)) := by rw [hdeltaC]
          _ = eps * intervalDomain.integral (fun X =>
              (u t X) ^ (p.γ * (P + 1)) /
                (1 + v t X) ^ p.β) := by rw [hsourceEq]
  have hfinal :
      intervalDomain.integral (fun X => z X ^ (P + 1)) ≤
        eps * intervalDomain.integral (fun X =>
          (u t X) ^ (p.γ * (P + 1)) / (1 + v t X) ^ p.β) +
        Ceps * (intervalDomain.integral z) ^ (P + 1) := by
    calc
      intervalDomain.integral (fun X => z X ^ (P + 1)) ≤
          delta * intervalDomain.integral (fun X =>
            z X ^ (P + 1 - 2) * (intervalDomain.gradNorm z X) ^ 2) +
            Ceps * (intervalDomain.integral z) ^ (P + 1) := hag
      _ = delta * intervalDomain.integral (fun X =>
            z X ^ (P - 1) * (intervalDomain.gradNorm z X) ^ 2) +
            Ceps * (intervalDomain.integral z) ^ (P + 1) := by ring_nf
      _ ≤ eps * intervalDomain.integral (fun X =>
            (u t X) ^ (p.γ * (P + 1)) / (1 + v t X) ^ p.β) +
            Ceps * (intervalDomain.integral z) ^ (P + 1) :=
        add_le_add hgradSource (le_refl _)
  rw [intervalDomain_weightedSignalTransform_power_integral_eq
      hsol ht0 htT hP,
    intervalDomain_weightedSignalTransform_mass_integral_eq
      hsol ht0 htT] at hfinal
  simpa [z] using hfinal

#print axioms intervalDomain_weightedSignal_gradient_preestimate
#print axioms intervalDomain_weightedSignal_gradient_bound
#print axioms intervalDomain_Proposition_2_3

end ShenWork.Paper2
