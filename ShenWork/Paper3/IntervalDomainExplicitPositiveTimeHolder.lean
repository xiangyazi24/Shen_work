/- Explicit, trajectory-independent positive-time Holder constants. -/
import ShenWork.Paper2.IntervalConjugateMildPositiveTimeC1

namespace ShenWork.Paper3

open MeasureTheory Filter Set
open ShenWork.IntervalDomain
  (intervalMeasure intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel
  (intervalFullSemigroupOperator)
open ShenWork.IntervalGradientDuhamelMap
  (chemFluxLifted logisticLifted)
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateKernelOperator)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildSolutionData)
open ShenWork.HeatKernelGradientEstimates
  (heatGradientLinftyLinftyConstant heatGradientLinftyLinftyConstant_nonneg)
open ShenWork.Paper2

noncomputable section

/-- The explicit positive-time Holder constant obtained from the three mild
legs.  It depends only on the equation, the fixed cone ceiling, the horizon,
and the positive delay. -/
def paper3MildPositiveTimeHolderConstant
    (p : CM2Params) (M T theta tau : ℝ) : ℝ :=
  let base := (2 : ℝ) ^ (1 - theta) * gradSmoothingConst ^ theta
  let CL := M * (p.a + p.b * M ^ p.α)
  let CQ := M * (Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * M ^ p.γ)))
  let gbase := (2 : ℝ) ^ (1 - theta) *
    ((5 * Real.sqrt 2 / 2) ^ theta *
      heatGradientLinftyLinftyConstant ^ (1 - theta))
  let UB_L := T ^ (-(theta / 2) + 1) / (-(theta / 2) + 1)
  let UB_Q := T ^ (-((1 + theta) / 2) + 1) /
    (-((1 + theta) / 2) + 1)
  base * M * tau ^ (-(theta / 2) : ℝ) +
    |p.χ₀| * (gbase * CQ * UB_Q) + base * CL * UB_L

theorem paper3MildPositiveTimeHolderConstant_nonneg
    (p : CM2Params) {M T theta tau : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (htheta0 : 0 < theta) (htheta1 : theta < 1) (htau : 0 < tau) :
    0 ≤ paper3MildPositiveTimeHolderConstant p M T theta tau := by
  let base := (2 : ℝ) ^ (1 - theta) * gradSmoothingConst ^ theta
  let CL := M * (p.a + p.b * M ^ p.α)
  let CQ := M * (Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * M ^ p.γ)))
  let gbase := (2 : ℝ) ^ (1 - theta) *
    ((5 * Real.sqrt 2 / 2) ^ theta *
      heatGradientLinftyLinftyConstant ^ (1 - theta))
  let UB_L := T ^ (-(theta / 2) + 1) / (-(theta / 2) + 1)
  let UB_Q := T ^ (-((1 + theta) / 2) + 1) /
    (-((1 + theta) / 2) + 1)
  have hbase : 0 ≤ base := by
    dsimp [base]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg gradSmoothingConst_nonneg _)
  have hCL : 0 ≤ CL := by
    dsimp [CL]
    exact mul_nonneg hM
      (add_nonneg p.ha (mul_nonneg p.hb (Real.rpow_nonneg hM _)))
  have hCQ : 0 ≤ CQ := by
    dsimp [CQ]
    exact mul_nonneg hM (mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num)
        (mul_nonneg p.hν.le (Real.rpow_nonneg hM _))))
  have hgbase : 0 ≤ gbase := by
    dsimp [gbase]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (Real.rpow_nonneg heatGradientLinftyLinftyConstant_nonneg _))
  have hUBL : 0 ≤ UB_L := by
    dsimp [UB_L]
    exact div_nonneg (Real.rpow_nonneg hT _) (by linarith)
  have hUBQ : 0 ≤ UB_Q := by
    dsimp [UB_Q]
    exact div_nonneg (Real.rpow_nonneg hT _) (by linarith)
  unfold paper3MildPositiveTimeHolderConstant
  dsimp only
  exact add_nonneg
    (add_nonneg
      (mul_nonneg (mul_nonneg hbase hM)
        (Real.rpow_nonneg htau.le _))
      (mul_nonneg (abs_nonneg _)
        (mul_nonneg (mul_nonneg hgbase hCQ) hUBQ)))
    (mul_nonneg (mul_nonneg hbase hCL) hUBL)

/-- Explicit version of the positive-time Holder estimate. -/
theorem conjugateMild_positiveTime_holder_explicit
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionData p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {theta tau : ℝ} (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (htau : 0 < tau) :
    ∀ t ∈ Set.Icc tau D.T, ∀ x y : intervalDomainPoint,
      |D.u t x - D.u t y| ≤
        paper3MildPositiveTimeHolderConstant
          p D.M D.T theta tau * |x.1 - y.1| ^ theta := by
  let base : ℝ := (2 : ℝ) ^ (1 - theta) * gradSmoothingConst ^ theta
  let CL : ℝ := D.M * (p.a + p.b * D.M ^ p.α)
  let CQ : ℝ := D.M * (Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * D.M ^ p.γ)))
  let gbase : ℝ := (2 : ℝ) ^ (1 - theta) *
    ((5 * Real.sqrt 2 / 2) ^ theta *
      heatGradientLinftyLinftyConstant ^ (1 - theta))
  let UB_L : ℝ := D.T ^ (-(theta / 2) + 1) / (-(theta / 2) + 1)
  let UB_Q : ℝ := D.T ^ (-((1 + theta) / 2) + 1) /
    (-((1 + theta) / 2) + 1)
  have hbase : 0 ≤ base := by
    dsimp [base]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg gradSmoothingConst_nonneg _)
  have hCL : 0 ≤ CL := by
    dsimp [CL]
    exact mul_nonneg D.hM.le
      (add_nonneg p.ha (mul_nonneg p.hb
        (Real.rpow_nonneg D.hM.le _)))
  have hCQ : 0 ≤ CQ := by
    dsimp [CQ]
    exact mul_nonneg D.hM.le (mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num)
        (mul_nonneg p.hν.le (Real.rpow_nonneg D.hM.le _))))
  have hgbase : 0 ≤ gbase := by
    dsimp [gbase]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (Real.rpow_nonneg heatGradientLinftyLinftyConstant_nonneg _))
  have hUBL : 0 ≤ UB_L := by
    dsimp [UB_L]
    exact div_nonneg (Real.rpow_nonneg D.hT.le _) (by linarith)
  have hUBQ : 0 ≤ UB_Q := by
    dsimp [UB_Q]
    exact div_nonneg (Real.rpow_nonneg D.hT.le _) (by linarith)
  intro t ht x y
  have htpos : 0 < t := lt_of_lt_of_le htau ht.1
  have hdxy : 0 ≤ |x.1 - y.1| ^ theta :=
    Real.rpow_nonneg (abs_nonneg _) _
  let I1 : ℝ := intervalFullSemigroupOperator t
      (intervalDomainLift u₀) x.1 -
    intervalFullSemigroupOperator t (intervalDomainLift u₀) y.1
  let I2 : ℝ := (∫ s in (0 : ℝ)..t,
      intervalConjugateKernelOperator (t - s)
        (chemFluxLifted p (D.u s)) x.1) -
    (∫ s in (0 : ℝ)..t,
      intervalConjugateKernelOperator (t - s)
        (chemFluxLifted p (D.u s)) y.1)
  let I3 : ℝ := (∫ s in (0 : ℝ)..t,
      intervalFullSemigroupOperator (t - s)
        (logisticLifted p (D.u s)) x.1) -
    (∫ s in (0 : ℝ)..t,
      intervalFullSemigroupOperator (t - s)
        (logisticLifted p (D.u s)) y.1)
  have hmildx := D.hmild t htpos ht.2 x
  have hmildy := D.hmild t htpos ht.2 y
  have hdiff : D.u t x - D.u t y = I1 + (-p.χ₀) * I2 + I3 := by
    rw [hmildx, hmildy]
    dsimp [I1, I2, I3]
    unfold ShenWork.IntervalConjugateDuhamelMap.intervalConjugateDuhamelMap
    ring
  have hleg1 := holderLeg_initial (p := p) (u₀ := u₀) (M := D.M)
    D.hM.le hu₀ hu₀_meas htpos htheta0 htheta1 x y
  have hleg2 := holderLeg_conjugateChemotaxis
    (p := p) (u := D.u) (M := D.M) D.hM
    D.hbound D.hnonneg D.hcont D.hmeas htpos ht.2
      htheta0 htheta1 x y
  have hleg3 := holderLeg_reaction
    (p := p) (u := D.u) (M := D.M) D.hM
    D.hbound D.hcont D.hmeas htpos ht.2 htheta0 htheta1 x y
  have htmono : t ^ (-(theta / 2) : ℝ) ≤
      tau ^ (-(theta / 2) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos htau ht.1 (by linarith)
  have hI1 : |I1| ≤
      (base * D.M * tau ^ (-(theta / 2) : ℝ)) *
        |x.1 - y.1| ^ theta := by
    dsimp [I1]
    refine hleg1.trans ?_
    exact mul_le_mul_of_nonneg_right
      (by
        have hbM : 0 ≤ base * D.M := mul_nonneg hbase D.hM.le
        nlinarith [mul_le_mul_of_nonneg_left htmono hbM]) hdxy
  have hintL :
      (∫ s in (0 : ℝ)..t,
        base * (t - s) ^ (-(theta / 2) : ℝ) * CL) ≤
        base * CL * UB_L := by
    have heq :
        (∫ s in (0 : ℝ)..t,
          base * (t - s) ^ (-(theta / 2) : ℝ) * CL) =
          base * CL * (∫ s in (0 : ℝ)..t,
            (t - s) ^ (-(theta / 2) : ℝ)) := by
      rw [show (fun s : ℝ => base * (t - s) ^ (-(theta / 2) : ℝ) * CL) =
          fun s => (base * CL) * (t - s) ^ (-(theta / 2) : ℝ) by
        funext s; ring,
        intervalIntegral.integral_const_mul]
    rw [heq]
    exact mul_le_mul_of_nonneg_left
      (duhamel_time_integral_le htpos.le ht.2 (by linarith))
      (mul_nonneg hbase hCL)
  have hI3 : |I3| ≤
      (base * CL * UB_L) * |x.1 - y.1| ^ theta := by
    dsimp [I3]
    exact hleg3.trans (mul_le_mul_of_nonneg_right hintL hdxy)
  have hintQ :
      (∫ s in (0 : ℝ)..t,
        gbase * (t - s) ^ (-((1 + theta) / 2) : ℝ) * CQ) ≤
        gbase * CQ * UB_Q := by
    have heq :
        (∫ s in (0 : ℝ)..t,
          gbase * (t - s) ^ (-((1 + theta) / 2) : ℝ) * CQ) =
          gbase * CQ * (∫ s in (0 : ℝ)..t,
            (t - s) ^ (-((1 + theta) / 2) : ℝ)) := by
      rw [show (fun s : ℝ =>
          gbase * (t - s) ^ (-((1 + theta) / 2) : ℝ) * CQ) =
          fun s => (gbase * CQ) *
            (t - s) ^ (-((1 + theta) / 2) : ℝ) by
        funext s; ring,
        intervalIntegral.integral_const_mul]
    rw [heq]
    exact mul_le_mul_of_nonneg_left
      (duhamel_gradTime_integral_le htpos.le ht.2 htheta1)
      (mul_nonneg hgbase hCQ)
  have hI2 : |I2| ≤
      (gbase * CQ * UB_Q) * |x.1 - y.1| ^ theta := by
    dsimp [I2]
    exact hleg2.trans (mul_le_mul_of_nonneg_right hintQ hdxy)
  rw [hdiff]
  have htri : |I1 + (-p.χ₀) * I2 + I3| ≤
      |I1| + |(-p.χ₀) * I2| + |I3| := by
    refine (abs_add_le (I1 + (-p.χ₀) * I2) I3).trans ?_
    gcongr
    exact abs_add_le I1 ((-p.χ₀) * I2)
  refine htri.trans ?_
  have hchi : |(-p.χ₀) * I2| ≤
      |p.χ₀| * ((gbase * CQ * UB_Q) * |x.1 - y.1| ^ theta) := by
    rw [abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left hI2 (abs_nonneg _)
  calc
    |I1| + |(-p.χ₀) * I2| + |I3| ≤
        (base * D.M * tau ^ (-(theta / 2) : ℝ)) * |x.1 - y.1| ^ theta +
          |p.χ₀| * ((gbase * CQ * UB_Q) * |x.1 - y.1| ^ theta) +
          (base * CL * UB_L) * |x.1 - y.1| ^ theta :=
      add_le_add (add_le_add hI1 hchi) hI3
    _ = paper3MildPositiveTimeHolderConstant
          p D.M D.T theta tau * |x.1 - y.1| ^ theta := by
      unfold paper3MildPositiveTimeHolderConstant
      dsimp only
      ring

/-- Explicit Holder constant for the eliminated chemotaxis flux. -/
def paper3ChemFluxPositiveTimeHolderConstant
    (p : CM2Params) (M T theta tau : ℝ) : ℝ :=
  let Hu := paper3MildPositiveTimeHolderConstant p M T theta tau
  let G := Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * M ^ p.γ))
  let Hg := (2 : ℝ) ^ (1 - theta) *
      Real.sqrt (∑' k : ℕ,
        (ShenWork.IntervalResolverWeakBounds.intervalNeumannResolverGradHolderWeight
          p theta k) ^ 2) * (2 * (p.ν * M ^ p.γ))
  Hu * G + M * Hg + M * G * p.β * G

theorem paper3ChemFluxPositiveTimeHolderConstant_nonneg
    (p : CM2Params) {M T theta tau : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (htheta0 : 0 < theta) (hthetaHalf : theta < 1 / 2)
    (htau : 0 < tau) :
    0 ≤ paper3ChemFluxPositiveTimeHolderConstant p M T theta tau := by
  have htheta1 : theta < 1 := by linarith
  let Hu := paper3MildPositiveTimeHolderConstant p M T theta tau
  let G := Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * M ^ p.γ))
  let Hg := (2 : ℝ) ^ (1 - theta) *
      Real.sqrt (∑' k : ℕ,
        (ShenWork.IntervalResolverWeakBounds.intervalNeumannResolverGradHolderWeight
          p theta k) ^ 2) * (2 * (p.ν * M ^ p.γ))
  have hHu : 0 ≤ Hu := by
    simpa [Hu] using paper3MildPositiveTimeHolderConstant_nonneg
      p hM hT htheta0 htheta1 htau
  have hG : 0 ≤ G := by
    dsimp [G]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num)
        (mul_nonneg p.hν.le (Real.rpow_nonneg hM _)))
  have hHg : 0 ≤ Hg := by
    dsimp [Hg]
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (Real.sqrt_nonneg _))
      (mul_nonneg (by norm_num)
        (mul_nonneg p.hν.le (Real.rpow_nonneg hM _)))
  unfold paper3ChemFluxPositiveTimeHolderConstant
  dsimp only
  exact add_nonneg (add_nonneg (mul_nonneg hHu hG) (mul_nonneg hM hHg))
    (mul_nonneg (mul_nonneg (mul_nonneg hM hG) p.hβ) hG)

/-- Explicit, trajectory-independent Holder estimate for the flux. -/
theorem conjugateMild_chemFlux_positiveTime_holder_explicit
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionData p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {theta tau : ℝ} (htheta0 : 0 < theta)
    (hthetaHalf : theta < 1 / 2) (htau : 0 < tau) :
    ∀ s ∈ Set.Icc tau D.T, ∀ a b : ℝ,
      a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
      |chemFluxLifted p (D.u s) a - chemFluxLifted p (D.u s) b| ≤
        paper3ChemFluxPositiveTimeHolderConstant
          p D.M D.T theta tau * |a - b| ^ theta := by
  have htheta1 : theta < 1 := by linarith
  let Hu := paper3MildPositiveTimeHolderConstant p D.M D.T theta tau
  let G := Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * D.M ^ p.γ))
  let Hg := (2 : ℝ) ^ (1 - theta) *
      Real.sqrt (∑' k : ℕ,
        (ShenWork.IntervalResolverWeakBounds.intervalNeumannResolverGradHolderWeight
          p theta k) ^ 2) * (2 * (p.ν * D.M ^ p.γ))
  have hHu : 0 ≤ Hu := by
    simpa [Hu] using paper3MildPositiveTimeHolderConstant_nonneg
      p D.hM.le D.hT.le htheta0 htheta1 htau
  have hG : 0 ≤ G := by
    dsimp [G]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num)
        (mul_nonneg p.hν.le (Real.rpow_nonneg D.hM.le _)))
  have hHg : 0 ≤ Hg := by
    dsimp [Hg]
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (Real.sqrt_nonneg _))
      (mul_nonneg (by norm_num)
        (mul_nonneg p.hν.le (Real.rpow_nonneg D.hM.le _)))
  intro s hs a b ha hb
  have hs0 : 0 < s := lt_of_lt_of_le htau hs.1
  have hUcont : ContinuousOn (intervalDomainLift (D.u s))
      (Set.Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    have heq : Set.restrict (Set.Icc (0 : ℝ) 1)
        (intervalDomainLift (D.u s)) = D.u s := by
      ext ⟨y, hy⟩
      simp [Set.restrict, intervalDomainLift, hy]
      rfl
    rw [heq]
    exact D.hcont s hs0 hs.2
  have hlb : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ intervalDomainLift (D.u s) y := by
    intro y hy
    simpa [intervalDomainLift, hy] using D.hnonneg s hs0 hs.2 ⟨y, hy⟩
  have hub : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (D.u s) y ≤ D.M := by
    intro y hy
    have h := D.hbound s hs0 hs.2 ⟨y, hy⟩
    simpa [intervalDomainLift, hy] using (abs_le.mp h).2
  have huBound : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |intervalDomainLift (D.u s) y| ≤ D.M := by
    intro y hy
    simpa [intervalDomainLift, hy] using D.hbound s hs0 hs.2 ⟨y, hy⟩
  have hgBound : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |resolverGradReal p (D.u s) y| ≤ G := by
    intro y hy
    dsimp [G]
    exact ShenWork.IntervalResolverWeakBounds.resolverGrad_sup_le_of_bounded
      p hUcont hlb hub hy
  have hRnonneg : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ intervalDomainLift
        (ShenWork.PDE.intervalNeumannResolverR p (D.u s)) y := by
    intro y hy
    have h := ShenWork.IntervalMildToClassical.mildChemical_nonneg
      (T := D.T) p (u := D.u) D.hnonneg D.hcont hs0 hs.2 ⟨y, hy⟩
    simpa [ShenWork.IntervalMildToClassical.mildChemicalConcentration,
      intervalDomainLift, hy] using h
  have huHolder : ∀ x y : ℝ,
      x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 →
      |intervalDomainLift (D.u s) x - intervalDomainLift (D.u s) y| ≤
        Hu * |x - y| ^ theta := by
    intro x y hx hy
    simpa [Hu, intervalDomainLift, hx, hy] using
      conjugateMild_positiveTime_holder_explicit
        D hu₀ hu₀_meas htheta0 htheta1 htau s hs
          ⟨x, hx⟩ ⟨y, hy⟩
  have hgHolder : ∀ x y : ℝ,
      x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 →
      |resolverGradReal p (D.u s) x - resolverGradReal p (D.u s) y| ≤
        Hg * |x - y| ^ theta := by
    intro x y hx hy
    dsimp [Hg]
    exact ShenWork.IntervalResolverWeakBounds.resolverGradReal_holder_Icc_of_bounded_smallTheta
      p htheta0 hthetaHalf hUcont hlb hub hx hy
  have hRHolder : ∀ x y : ℝ,
      x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 →
      |intervalDomainLift
          (ShenWork.PDE.intervalNeumannResolverR p (D.u s)) x -
        intervalDomainLift
          (ShenWork.PDE.intervalNeumannResolverR p (D.u s)) y| ≤
        G * |x - y| ^ theta := by
    intro x y hx hy
    dsimp [G]
    exact ShenWork.IntervalResolverWeakBounds.intervalNeumannResolverR_lift_holder_Icc_of_bounded
      p htheta0 htheta1.le hUcont hlb hub hx hy
  unfold paper3ChemFluxPositiveTimeHolderConstant
  dsimp only
  exact chemFluxLifted_holder_of_component_holder
    (p := p) (w := D.u s) (θ := theta) (U := D.M) (G := G)
    (Hu := Hu) (Hg := Hg) (Hv := G)
    D.hM.le hG hHu hHg huBound hgBound hRnonneg
    huHolder hgHolder hRHolder a b ha hb

#print axioms paper3MildPositiveTimeHolderConstant_nonneg
#print axioms conjugateMild_positiveTime_holder_explicit
#print axioms paper3ChemFluxPositiveTimeHolderConstant_nonneg
#print axioms conjugateMild_chemFlux_positiveTime_holder_explicit

end

end ShenWork.Paper3
