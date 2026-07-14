/-
  ShenWork/Paper2/IntervalDomainMConjugateMildHolderBootstrap.lean

  Positive-time spatial Holder regularity for the faithful conjugate-kernel
  mild fixed point.  The chemotaxis leg uses the mixed-kernel estimate from
  `IntervalConjugateKernelHolder`; the initial and reaction legs reuse the
  heat-semigroup estimates from `ChemMildHolderBootstrap`.
-/
import ShenWork.Paper2.IntervalConjugateKernelHolder
import ShenWork.Paper2.IntervalDomainMConjugateMapBounds
import ShenWork.Paper2.IntervalDomainMConjugatePicardFloorInhabit

open MeasureTheory Filter
open ShenWork.IntervalDomain
  (intervalMeasure intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalConjugateDuhamelMap (intervalConjugateKernelOperator)
open ShenWork.IntervalMildPicard (HasContinuousSlices HasJointMeasurability)
open ShenWork.Paper2.IntervalDomainMConjugateDuhamelMap
  (chemFluxMLifted intervalConjugateDuhamelMapM
    chemFluxMLifted_abs_le_of_pos_slice
    chemFluxMLifted_integrable_of_pos_slice)
open ShenWork.Paper2.IntervalDomainMConjugateMapBounds
  (chemFluxMLifted_duhamel_intervalIntegrable_of_positive_cone)
open ShenWork.Paper2.IntervalDomainMConjugatePicardFloorInhabit
  (ConjugateMildSolutionDataM)
open ShenWork.HeatKernelGradientEstimates
  (heatGradientLinftyLinftyConstant heatGradientLinftyLinftyConstant_nonneg)

namespace ShenWork.Paper2

noncomputable section

/-! ## The conjugate chemotaxis leg -/

/-- The faithful conjugate-kernel chemotaxis Duhamel leg is spatially Holder.
The per-slice singularity is `t^{-(1+theta)/2}`, hence is time-integrable for
`theta < 1`. -/
theorem holderLeg_conjugateChemotaxisM
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {T M c : ℝ} (hM : 0 < M) (hc : 0 < c) (hcM : c ≤ M)
    (hbound : ∀ t, 0 < t → t ≤ T → ∀ x, |u t x| ≤ M)
    (hfloor : ∀ t, 0 < t → t ≤ T → ∀ x, c ≤ u t x)
    (hcont : HasContinuousSlices T u) (hmeas : HasJointMeasurability u)
    {t θ : ℝ} (ht : 0 < t) (htT : t ≤ T)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (x y : intervalDomainPoint) :
    |(∫ s in (0 : ℝ)..t,
        intervalConjugateKernelOperator (t - s) (chemFluxMLifted p (u s)) x.1)
      - (∫ s in (0 : ℝ)..t,
        intervalConjugateKernelOperator (t - s) (chemFluxMLifted p (u s)) y.1)|
      ≤ (∫ s in (0 : ℝ)..t,
          (2 : ℝ) ^ (1 - θ)
            * ((5 * Real.sqrt 2 / 2) ^ θ
              * heatGradientLinftyLinftyConstant ^ (1 - θ))
            * (t - s) ^ (-((1 + θ) / 2) : ℝ)
            * (M ^ p.m * (Real.sqrt (∑' k : ℕ,
                (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2)
                * (2 * (p.ν * M ^ p.γ)))))
        * |x.1 - y.1| ^ θ := by
  set CQ : ℝ := M ^ p.m * (Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2)
      * (2 * (p.ν * M ^ p.γ))) with hCQ
  have hCQ_nn : 0 ≤ CQ := by
    rw [hCQ]
    exact mul_nonneg (Real.rpow_nonneg hM.le _) (mul_nonneg (Real.sqrt_nonneg _)
      (by have := p.hν; positivity))
  have hQbound : ∀ s, 0 < s → s ≤ T → ∀ yy,
      |chemFluxMLifted p (u s) yy| ≤ CQ := by
    intro s hs hsT yy
    simpa [CQ] using
      chemFluxMLifted_abs_le_of_pos_slice p hc hcM
        (hbound s hs hsT) (hfloor s hs hsT) (hcont s hs hsT) yy
  have hφ_int : IntervalIntegrable
      (fun s : ℝ => (2 : ℝ) ^ (1 - θ)
        * ((5 * Real.sqrt 2 / 2) ^ θ
          * heatGradientLinftyLinftyConstant ^ (1 - θ))
        * (t - s) ^ (-((1 + θ) / 2) : ℝ) * CQ) volume 0 t := by
    have h0 := duhamel_holder_gradTime_integrand_integrable ht hθ0 hθ1
    have h1 := h0.const_mul ((2 : ℝ) ^ (1 - θ)
      * ((5 * Real.sqrt 2 / 2) ^ θ
        * heatGradientLinftyLinftyConstant ^ (1 - θ)))
    have h2 := h1.mul_const CQ
    exact h2.congr (fun s _ => by ring)
  refine holder_of_duhamel_integral ht.le
    (chemFluxMLifted_duhamel_intervalIntegrable_of_positive_cone
      p hc hcM hCQ_nn hbound hfloor hcont hmeas hQbound ht htT x)
    (chemFluxMLifted_duhamel_intervalIntegrable_of_positive_cone
      p hc hcM hCQ_nn hbound hfloor hcont hmeas hQbound ht htT y)
    hφ_int ?_
  have hne_t : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton]
    exact Real.volume_singleton
  have hne_0 : ∀ᵐ s : ℝ ∂volume, s ≠ 0 := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton]
    exact Real.volume_singleton
  refine (ae_restrict_iff' measurableSet_Icc).mpr ?_
  filter_upwards [hne_t, hne_0] with s hs_ne_t hs_ne_0 hs_mem
  have hs0 : 0 < s := lt_of_le_of_ne hs_mem.1 (Ne.symm hs_ne_0)
  have hsT : s ≤ T := hs_mem.2.trans htT
  have hts : 0 < t - s :=
    sub_pos.mpr (lt_of_le_of_ne hs_mem.2 hs_ne_t)
  have hQ_int : Integrable (chemFluxMLifted p (u s)) (intervalMeasure 1) :=
    chemFluxMLifted_integrable_of_pos_slice p hc hcM
      (hbound s hs0 hsT) (hfloor s hs0 hsT) (hcont s hs0 hsT)
  exact ShenWork.IntervalConjugateDuhamelMap.intervalConjugateKernelOperator_Linf_to_Ctheta
    hts hθ0 hθ1 hQ_int (hQbound s hs0 hsT) x.1 y.1

/-! ## Positive-time capstone -/

/-- An explicit spatial Holder constant for the faithful conjugate mild
solution.  In particular, it depends on the ceiling `M` but not on the
positive floor used to construct a local mild solution. -/
def conjugateMildMHolderConstant
    (p : CM2Params) (M T θ τ : ℝ) : ℝ :=
  let base : ℝ := (2 : ℝ) ^ (1 - θ) * gradSmoothingConst ^ θ
  let CL : ℝ := M * (p.a + p.b * M ^ p.α)
  let CQ : ℝ := M ^ p.m * (Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2)
      * (2 * (p.ν * M ^ p.γ)))
  let gbase : ℝ := (2 : ℝ) ^ (1 - θ)
    * ((5 * Real.sqrt 2 / 2) ^ θ
      * heatGradientLinftyLinftyConstant ^ (1 - θ))
  let UB_L : ℝ := T ^ (-(θ / 2) + 1) / (-(θ / 2) + 1)
  let UB_Q : ℝ := T ^ (-((1 + θ) / 2) + 1)
    / (-((1 + θ) / 2) + 1)
  base * M * τ ^ (-(θ / 2) : ℝ)
    + |p.χ₀| * (gbase * CQ * UB_Q) + base * CL * UB_L

set_option maxHeartbeats 400000 in
-- The explicit witness adds one normalization step to the original estimate;
-- the analytic proof itself is unchanged.
/-- Positive-time spatial Holder regularity of the faithful conjugate-kernel
mild fixed point, with its explicit floor-independent constant. -/
theorem conjugateMildM_positiveTime_holder_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {θ τ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hτ : 0 < τ) :
    0 ≤ conjugateMildMHolderConstant p D.M D.T θ τ ∧
      ∀ t ∈ Set.Icc τ D.T,
      ∀ x y : intervalDomainPoint,
        |D.u t x - D.u t y|
          ≤ conjugateMildMHolderConstant p D.M D.T θ τ
            * |x.1 - y.1| ^ θ := by
  classical
  set M := D.M with hMdef
  have hMpos : 0 < M := D.hM
  set base : ℝ := (2 : ℝ) ^ (1 - θ) * gradSmoothingConst ^ θ with hbase
  have hbase_nn : 0 ≤ base := by
    rw [hbase]
    have := gradSmoothingConst_nonneg
    positivity
  set CL : ℝ := M * (p.a + p.b * M ^ p.α) with hCL
  have hCL_nn : 0 ≤ CL := by
    rw [hCL]
    exact mul_nonneg hMpos.le (by have := p.ha; have := p.hb; positivity)
  set CQ : ℝ := M ^ p.m * (Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2)
      * (2 * (p.ν * M ^ p.γ))) with hCQ
  have hCQ_nn : 0 ≤ CQ := by
    rw [hCQ]
    exact mul_nonneg (Real.rpow_nonneg hMpos.le _) (mul_nonneg (Real.sqrt_nonneg _)
      (by have := p.hν; positivity))
  set gbase : ℝ := (2 : ℝ) ^ (1 - θ)
    * ((5 * Real.sqrt 2 / 2) ^ θ
      * heatGradientLinftyLinftyConstant ^ (1 - θ)) with hgbase
  have hgbase_nn : 0 ≤ gbase := by
    rw [hgbase]
    have := heatGradientLinftyLinftyConstant_nonneg
    positivity
  set UB_L : ℝ := D.T ^ (-(θ / 2) + 1) / (-(θ / 2) + 1) with hUBL
  set UB_Q : ℝ := D.T ^ (-((1 + θ) / 2) + 1)
    / (-((1 + θ) / 2) + 1) with hUBQ
  have hexpL : 0 < -(θ / 2) + 1 := by linarith
  have hexpQ : 0 < -((1 + θ) / 2) + 1 := by linarith
  have hTnn : 0 ≤ D.T := D.hT.le
  have hUBL_nn : 0 ≤ UB_L := by
    rw [hUBL]
    exact div_nonneg (Real.rpow_nonneg hTnn _) hexpL.le
  have hUBQ_nn : 0 ≤ UB_Q := by
    rw [hUBQ]
    exact div_nonneg (Real.rpow_nonneg hTnn _) hexpQ.le
  set K : ℝ := base * M * τ ^ (-(θ / 2) : ℝ)
      + |p.χ₀| * (gbase * CQ * UB_Q) + base * CL * UB_L with hK
  have hτrpow_nn : 0 ≤ τ ^ (-(θ / 2) : ℝ) :=
    (Real.rpow_pos_of_pos hτ _).le
  have hK_nn : 0 ≤ K := by
    rw [hK]
    have h1 : 0 ≤ base * M * τ ^ (-(θ / 2) : ℝ) :=
      mul_nonneg (mul_nonneg hbase_nn hMpos.le) hτrpow_nn
    have h2 : 0 ≤ |p.χ₀| * (gbase * CQ * UB_Q) :=
      mul_nonneg (abs_nonneg _)
        (mul_nonneg (mul_nonneg hgbase_nn hCQ_nn) hUBQ_nn)
    have h3 : 0 ≤ base * CL * UB_L :=
      mul_nonneg (mul_nonneg hbase_nn hCL_nn) hUBL_nn
    linarith
  have hK_eq : K = conjugateMildMHolderConstant p D.M D.T θ τ := by
    simp only [conjugateMildMHolderConstant, hK, hbase, hCL, hCQ,
      hgbase, hUBL, hUBQ, hMdef]
  rw [← hK_eq]
  refine ⟨hK_nn, fun t ht x y => ?_⟩
  obtain ⟨hτt, htT⟩ := ht
  have htpos : 0 < t := lt_of_lt_of_le hτ hτt
  have hdxy_nn : 0 ≤ |x.1 - y.1| ^ θ :=
    Real.rpow_nonneg (abs_nonneg _) _
  set I1 : ℝ := intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
      - intervalFullSemigroupOperator t (intervalDomainLift u₀) y.1 with hI1
  set I2 : ℝ := (∫ s in (0 : ℝ)..t,
      intervalConjugateKernelOperator (t - s) (chemFluxMLifted p (D.u s)) x.1)
      - (∫ s in (0 : ℝ)..t,
      intervalConjugateKernelOperator (t - s) (chemFluxMLifted p (D.u s)) y.1)
    with hI2
  set I3 : ℝ := (∫ s in (0 : ℝ)..t,
      intervalFullSemigroupOperator (t - s) (logisticLifted p (D.u s)) x.1)
      - (∫ s in (0 : ℝ)..t,
      intervalFullSemigroupOperator (t - s) (logisticLifted p (D.u s)) y.1)
    with hI3
  have hmildx := D.hmild t htpos htT x
  have hmildy := D.hmild t htpos htT y
  have hdiff : D.u t x - D.u t y = I1 + (-p.χ₀) * I2 + I3 := by
    rw [hmildx, hmildy, hI1, hI2, hI3]
    unfold intervalConjugateDuhamelMapM
    ring
  have hleg1 := holderLeg_initial (p := p) (u₀ := u₀) (M := M)
    hMpos.le hu₀ hu₀_meas htpos hθ0 hθ1 x y
  have hcM : D.c ≤ M := by
    let x0 : intervalDomainPoint := ⟨0, ⟨le_rfl, zero_le_one⟩⟩
    have hf := D.hfloor D.T D.hT le_rfl x0
    have hb := D.hbound D.T D.hT le_rfl x0
    exact hf.trans ((le_abs_self _).trans (by simpa [M] using hb))
  have hleg2 := holderLeg_conjugateChemotaxisM
    (p := p) (u := D.u) (M := M) (c := D.c) hMpos D.hc
    hcM
    D.hbound D.hfloor D.hcont D.hmeas htpos htT hθ0 hθ1 x y
  have hleg3 := holderLeg_reaction (p := p) (u := D.u) (M := M) hMpos
    D.hbound D.hcont D.hmeas htpos htT hθ0 hθ1 x y
  have htmono : t ^ (-(θ / 2) : ℝ) ≤ τ ^ (-(θ / 2) : ℝ) := by
    rw [Real.rpow_neg hτ.le, Real.rpow_neg (lt_of_lt_of_le hτ hτt).le]
    have hτpow : 0 < τ ^ (θ / 2 : ℝ) := Real.rpow_pos_of_pos hτ _
    gcongr
  have hL1 : |I1| ≤
      (base * M * τ ^ (-(θ / 2) : ℝ)) * |x.1 - y.1| ^ θ := by
    rw [hI1]
    refine hleg1.trans ?_
    have hcoef : base * t ^ (-(θ / 2) : ℝ) * M
        ≤ base * M * τ ^ (-(θ / 2) : ℝ) := by
      have hbm : 0 ≤ base * M := mul_nonneg hbase_nn hMpos.le
      nlinarith [mul_le_mul_of_nonneg_left htmono hbm]
    exact mul_le_mul_of_nonneg_right hcoef hdxy_nn
  have hintL :
      (∫ s in (0 : ℝ)..t, base * (t - s) ^ (-(θ / 2) : ℝ) * CL)
        ≤ base * CL * UB_L := by
    have hfun_eq :
        (fun s : ℝ => base * (t - s) ^ (-(θ / 2) : ℝ) * CL)
          = fun s : ℝ => (base * CL) * (t - s) ^ (-(θ / 2) : ℝ) := by
      funext s
      ring
    have heq :
        (∫ s in (0 : ℝ)..t, base * (t - s) ^ (-(θ / 2) : ℝ) * CL)
          = base * CL * (∫ s in (0 : ℝ)..t,
              (t - s) ^ (-(θ / 2) : ℝ)) := by
      rw [hfun_eq, intervalIntegral.integral_const_mul]
    rw [heq]
    exact mul_le_mul_of_nonneg_left
      (duhamel_time_integral_le htpos.le htT (by linarith))
      (mul_nonneg hbase_nn hCL_nn)
  have hL3 : |I3| ≤ (base * CL * UB_L) * |x.1 - y.1| ^ θ := by
    rw [hI3]
    exact hleg3.trans (mul_le_mul_of_nonneg_right hintL hdxy_nn)
  have hintQ :
      (∫ s in (0 : ℝ)..t,
        gbase * (t - s) ^ (-((1 + θ) / 2) : ℝ) * CQ)
        ≤ gbase * CQ * UB_Q := by
    have hfun_eq :
        (fun s : ℝ =>
          gbase * (t - s) ^ (-((1 + θ) / 2) : ℝ) * CQ)
          = fun s : ℝ =>
            (gbase * CQ) * (t - s) ^ (-((1 + θ) / 2) : ℝ) := by
      funext s
      ring
    have heq :
        (∫ s in (0 : ℝ)..t,
          gbase * (t - s) ^ (-((1 + θ) / 2) : ℝ) * CQ)
          = gbase * CQ * (∫ s in (0 : ℝ)..t,
              (t - s) ^ (-((1 + θ) / 2) : ℝ)) := by
      rw [hfun_eq, intervalIntegral.integral_const_mul]
    rw [heq]
    exact mul_le_mul_of_nonneg_left
      (duhamel_gradTime_integral_le htpos.le htT hθ1)
      (mul_nonneg hgbase_nn hCQ_nn)
  have hL2 : |I2| ≤ (gbase * CQ * UB_Q) * |x.1 - y.1| ^ θ := by
    rw [hI2]
    exact hleg2.trans (mul_le_mul_of_nonneg_right hintQ hdxy_nn)
  rw [hdiff]
  have hχL2 : |(-p.χ₀) * I2|
      ≤ |p.χ₀| * ((gbase * CQ * UB_Q) * |x.1 - y.1| ^ θ) := by
    rw [abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left hL2 (abs_nonneg _)
  have htri : |I1 + (-p.χ₀) * I2 + I3|
      ≤ |I1| + |(-p.χ₀) * I2| + |I3| := by
    refine (abs_add_le (I1 + (-p.χ₀) * I2) I3).trans ?_
    gcongr
    exact abs_add_le I1 ((-p.χ₀) * I2)
  refine htri.trans ?_
  rw [hK, add_mul, add_mul]
  have hsum := add_le_add (add_le_add hL1 hχL2) hL3
  have hassoc :
      (base * M * τ ^ (-(θ / 2) : ℝ)) * |x.1 - y.1| ^ θ
        + |p.χ₀| * ((gbase * CQ * UB_Q) * |x.1 - y.1| ^ θ)
        + (base * CL * UB_L) * |x.1 - y.1| ^ θ
      = base * M * τ ^ (-(θ / 2) : ℝ) * |x.1 - y.1| ^ θ
        + |p.χ₀| * (gbase * CQ * UB_Q) * |x.1 - y.1| ^ θ
        + base * CL * UB_L * |x.1 - y.1| ^ θ := by
    ring
  rw [hassoc] at hsum
  exact hsum

/-- Positive-time spatial Holder regularity of the faithful conjugate-kernel
mild fixed point. -/
theorem conjugateMildM_positiveTime_holder
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {θ τ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hτ : 0 < τ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Set.Icc τ D.T,
      ∀ x y : intervalDomainPoint,
        |D.u t x - D.u t y| ≤ K * |x.1 - y.1| ^ θ := by
  exact ⟨conjugateMildMHolderConstant p D.M D.T θ τ,
    conjugateMildM_positiveTime_holder_bound D hu₀ hu₀_meas hθ0 hθ1 hτ⟩

end

end ShenWork.Paper2

#print axioms ShenWork.Paper2.holderLeg_conjugateChemotaxisM
#print axioms ShenWork.Paper2.conjugateMildM_positiveTime_holder_bound
#print axioms ShenWork.Paper2.conjugateMildM_positiveTime_holder
