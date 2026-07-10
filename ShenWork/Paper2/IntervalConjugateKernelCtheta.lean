/-
  C^theta cancellation for the faithful interval conjugate-kernel operator.

  The mixed Hessian has a nonintegrable t^{-1} L1 bound on bounded data.  If
  Q is Holder and Q(0)=Q(1)=0, its direct image is tested against Q(y)-Q(x),
  while its reflected image is tested against Q(y)+Q(x).  The latter is small
  at the nearest endpoint.  Both image families are then controlled by the
  same whole-line |w|^theta-weighted heat-Hessian mass, giving the integrable
  t^{-1+theta/2} bound.
-/
import ShenWork.PDE.IntervalFullKernelSecondDerivCtheta
import ShenWork.Paper2.IntervalConjugateKernelHolder

open MeasureTheory
open scoped Topology

noncomputable section

namespace ShenWork.IntervalNeumannFullKernel

open ShenWork.IntervalDomain

/-! ## Direct/reflected Hessian components -/

/-- The direct-image heat-Hessian lattice component. -/
def intervalDirectHeatHessComponent (t x y : ℝ) : ℝ :=
  ∑' k : ℤ,
    deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
      (x - y + 2 * (k : ℝ))

/-- The reflected-image heat-Hessian lattice component. -/
def intervalReflectedHeatHessComponent (t x y : ℝ) : ℝ :=
  ∑' k : ℤ,
    deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
      (x + y + 2 * (k : ℝ))

/-- The pure Neumann Hessian is the sum of its direct and reflected components. -/
theorem secondDeriv_intervalNeumannFullKernel_eq_components
    {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    deriv (fun z : ℝ => deriv
      (fun w : ℝ => intervalNeumannFullKernel t w y) z) x =
      intervalDirectHeatHessComponent t x y +
        intervalReflectedHeatHessComponent t x y := by
  rw [(hasDerivAt_deriv_intervalNeumannFullKernel_fst ht x y).deriv]
  rfl

/-- The mixed Hessian is minus the direct component plus the reflected one. -/
theorem mixedDeriv_intervalNeumannFullKernel_eq_components
    {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    deriv (fun z : ℝ => deriv
      (fun y' : ℝ => intervalNeumannFullKernel t z y') y) x =
      -intervalDirectHeatHessComponent t x y +
        intervalReflectedHeatHessComponent t x y := by
  rw [(hasDerivAt_deriv_intervalNeumannFullKernel_snd_fst ht x y).deriv]
  rfl

/-- Continuity of the direct Hessian component on the integration interval. -/
theorem continuousOn_intervalDirectHeatHessComponent
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ContinuousOn (intervalDirectHeatHessComponent t x) (Set.Icc 0 1) := by
  have hp := continuousOn_secondDeriv_intervalNeumannFullKernel_fst ht x
  have hm := continuousOn_mixedDeriv_intervalNeumannFullKernel ht x
  have heq : intervalDirectHeatHessComponent t x = fun y =>
      (deriv (fun z : ℝ => deriv
          (fun w : ℝ => intervalNeumannFullKernel t w y) z) x -
        deriv (fun z : ℝ => deriv
          (fun y' : ℝ => intervalNeumannFullKernel t z y') y) x) / 2 := by
    funext y
    rw [secondDeriv_intervalNeumannFullKernel_eq_components ht,
      mixedDeriv_intervalNeumannFullKernel_eq_components ht]
    ring
  rw [heq]
  exact (hp.sub hm).div_const 2

/-- Continuity of the reflected Hessian component on the integration interval. -/
theorem continuousOn_intervalReflectedHeatHessComponent
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ContinuousOn (intervalReflectedHeatHessComponent t x) (Set.Icc 0 1) := by
  have hp := continuousOn_secondDeriv_intervalNeumannFullKernel_fst ht x
  have hm := continuousOn_mixedDeriv_intervalNeumannFullKernel ht x
  have heq : intervalReflectedHeatHessComponent t x = fun y =>
      (deriv (fun z : ℝ => deriv
          (fun w : ℝ => intervalNeumannFullKernel t w y) z) x +
        deriv (fun z : ℝ => deriv
          (fun y' : ℝ => intervalNeumannFullKernel t z y') y) x) / 2 := by
    funext y
    rw [secondDeriv_intervalNeumannFullKernel_eq_components ht,
      mixedDeriv_intervalNeumannFullKernel_eq_components ht]
    ring
  rw [heq]
  exact (hp.add hm).div_const 2

/-! ## Period-cell weighted mass -/

/-- Local public copy of the weighted whole-line heat-Hessian integrand. -/
noncomputable def weightedHeatHess (t θ : ℝ) : ℝ → ℝ :=
  fun w => |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) w| *
    |w| ^ θ

/-- The weighted Hessian mass carried by the two image cells indexed by `k`. -/
def weightedHeatHessCellMass (t θ x : ℝ) (k : ℤ) : ℝ :=
  (∫ y in (0 : ℝ)..1,
      weightedHeatHess t θ (x - y + 2 * (k : ℝ))) +
    ∫ y in (0 : ℝ)..1,
      weightedHeatHess t θ (x + y + 2 * (k : ℝ))

/-- The weighted two-image cell masses are summable. -/
theorem summable_weightedHeatHessCellMass
    {t θ : ℝ} (ht : 0 < t) (hθ0 : 0 < θ) (hθ1 : θ < 1) (x : ℝ) :
    Summable (weightedHeatHessCellMass t θ x) := by
  have hg_int : Integrable (weightedHeatHess t θ) :=
    heatKernel_secondDeriv_weighted_abs_integrable ht hθ0 hθ1
  have hint : IntegrableOn (weightedHeatHess t θ)
      (⋃ k : ℤ, Set.Ioc ((x - 1) + 2 * (k : ℝ))
        ((x - 1) + 2 * (k : ℝ) + 2)) := by
    rw [ShenWork.iUnion_Ioc_offset_eq_univ]
    exact hg_int.integrableOn
  have hsum := (hasSum_integral_iUnion (fun k : ℤ => measurableSet_Ioc)
    (ShenWork.pairwise_disjoint_Ioc_offset (x - 1)) hint).summable
  refine hsum.congr (fun k => ?_)
  have hset : Set.Ioc ((x - 1) + 2 * (k : ℝ))
      ((x - 1) + 2 * (k : ℝ) + 2) =
      Set.Ioc (x + 2 * (k : ℝ) - 1) (x + 2 * (k : ℝ) + 1) := by
    congr 1 <;> ring
  rw [hset]
  exact (ShenWork.cell_integral_eq hg_int x k).symm

/-- The weighted two-image cell masses tile the whole-line weighted mass. -/
theorem tsum_weightedHeatHessCellMass_eq_integral
    {t θ : ℝ} (ht : 0 < t) (hθ0 : 0 < θ) (hθ1 : θ < 1) (x : ℝ) :
    (∑' k : ℤ, weightedHeatHessCellMass t θ x k) =
      ∫ w : ℝ, weightedHeatHess t θ w := by
  exact ShenWork.tsum_cell_integral_eq_integral
    (heatKernel_secondDeriv_weighted_abs_integrable ht hθ0 hθ1) x

/-! ## Endpoint geometry -/

/-- Distance of the reflected pair `(x,y)` to its nearest endpoint image. -/
def reflectedPairDistance (x y : ℝ) : ℝ :=
  min (x + y) (2 - x - y)

theorem reflectedPairDistance_nonneg
    {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ reflectedPairDistance x y := by
  unfold reflectedPairDistance
  exact le_min (by linarith [hx.1, hy.1]) (by linarith [hx.2, hy.2])

/-- Every reflected lattice image dominates the distance to the nearer endpoint. -/
theorem reflectedPairDistance_le_image
    {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) (k : ℤ) :
    reflectedPairDistance x y ≤ |x + y + 2 * (k : ℝ)| := by
  have hdL : reflectedPairDistance x y ≤ x + y := min_le_left _ _
  have hdR : reflectedPairDistance x y ≤ 2 - x - y := min_le_right _ _
  rcases le_or_gt 0 k with hk | hk
  · have hkR : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have harg : 0 ≤ x + y + 2 * (k : ℝ) := by linarith [hx.1, hy.1]
    rw [abs_of_nonneg harg]
    linarith
  · have hkZ : k ≤ -1 := by omega
    have hkR : (k : ℝ) ≤ -1 := by exact_mod_cast hkZ
    have harg : x + y + 2 * (k : ℝ) ≤ 0 := by linarith [hx.2, hy.2]
    rw [abs_of_nonpos harg]
    linarith

/-- Endpoint-zero Holder data controls the reflected source sum. -/
theorem abs_add_le_reflectedPairDistance_rpow
    {θ HQ : ℝ} (hθ0 : 0 < θ) (hHQ : 0 ≤ HQ)
    {Q : ℝ → ℝ} (hQ0 : Q 0 = 0) (hQ1 : Q 1 = 0)
    (hholder : ∀ a b : ℝ,
      a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
        |Q a - Q b| ≤ HQ * |a - b| ^ θ)
    {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |Q y + Q x| ≤
      2 * HQ * (reflectedPairDistance x y) ^ θ := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have hQy0 : |Q y| ≤ HQ * y ^ θ := by
    have h := hholder y 0 hy h0
    simpa [hQ0, abs_of_nonneg hy.1] using h
  have hQx0 : |Q x| ≤ HQ * x ^ θ := by
    have h := hholder x 0 hx h0
    simpa [hQ0, abs_of_nonneg hx.1] using h
  have hQy1 : |Q y| ≤ HQ * (1 - y) ^ θ := by
    have h := hholder y 1 hy h1
    have habs : |y - 1| = 1 - y := by
      rw [abs_of_nonpos (sub_nonpos.mpr hy.2)]
      ring
    simpa [hQ1, habs] using h
  have hQx1 : |Q x| ≤ HQ * (1 - x) ^ θ := by
    have h := hholder x 1 hx h1
    have habs : |x - 1| = 1 - x := by
      rw [abs_of_nonpos (sub_nonpos.mpr hx.2)]
      ring
    simpa [hQ1, habs] using h
  have hleft : |Q y + Q x| ≤ 2 * HQ * (x + y) ^ θ := by
    have hy_pow : y ^ θ ≤ (x + y) ^ θ :=
      Real.rpow_le_rpow hy.1 (by linarith [hx.1]) hθ0.le
    have hx_pow : x ^ θ ≤ (x + y) ^ θ :=
      Real.rpow_le_rpow hx.1 (by linarith [hy.1]) hθ0.le
    calc
      |Q y + Q x| ≤ |Q y| + |Q x| := abs_add_le _ _
      _ ≤ HQ * y ^ θ + HQ * x ^ θ := add_le_add hQy0 hQx0
      _ ≤ HQ * (x + y) ^ θ + HQ * (x + y) ^ θ := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hy_pow hHQ)
          (mul_le_mul_of_nonneg_left hx_pow hHQ)
      _ = 2 * HQ * (x + y) ^ θ := by ring
  have hright : |Q y + Q x| ≤ 2 * HQ * (2 - x - y) ^ θ := by
    have hy_pow : (1 - y) ^ θ ≤ (2 - x - y) ^ θ :=
      Real.rpow_le_rpow (by linarith [hy.2]) (by linarith [hx.2]) hθ0.le
    have hx_pow : (1 - x) ^ θ ≤ (2 - x - y) ^ θ :=
      Real.rpow_le_rpow (by linarith [hx.2]) (by linarith [hy.2]) hθ0.le
    calc
      |Q y + Q x| ≤ |Q y| + |Q x| := abs_add_le _ _
      _ ≤ HQ * (1 - y) ^ θ + HQ * (1 - x) ^ θ := add_le_add hQy1 hQx1
      _ ≤ HQ * (2 - x - y) ^ θ + HQ * (2 - x - y) ^ θ := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hy_pow hHQ)
          (mul_le_mul_of_nonneg_left hx_pow hHQ)
      _ = 2 * HQ * (2 - x - y) ^ θ := by ring
  rcases le_total (x + y) (2 - x - y) with hxy | hxy
  · simpa [reflectedPairDistance, min_eq_left hxy] using hleft
  · simpa [reflectedPairDistance, min_eq_right hxy] using hright

/-! ## C^theta to L-infinity derivative estimate -/

private lemma intervalMeasure_one_integral_eq_intervalIntegral (f : ℝ → ℝ) :
    (∫ y, f y ∂(intervalMeasure 1)) = ∫ y in (0 : ℝ)..1, f y := by
  unfold intervalMeasure intervalSet
  change (∫ y in Set.Icc (0 : ℝ) 1, f y ∂volume) =
    ∫ y in (0 : ℝ)..1, f y
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]

/-- The faithful conjugate-kernel operator gains one spatial derivative from
endpoint-zero Holder data with the integrable rate `t^{-1+theta/2}`. -/
theorem intervalConjugateKernelOperator_deriv_Ctheta_to_Linfty
    {t θ : ℝ} (ht : 0 < t) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {Q : ℝ → ℝ} (hQ_int : Integrable Q (intervalMeasure 1))
    {CQ : ℝ} (hQ_bound : ∀ y, |Q y| ≤ CQ)
    (hQ_cont : ContinuousOn Q (Set.Icc (0 : ℝ) 1))
    {HQ : ℝ} (hHQ : 0 ≤ HQ)
    (hQ_holder : ∀ a b : ℝ,
      a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
        |Q a - Q b| ≤ HQ * |a - b| ^ θ)
    (hQ0 : Q 0 = 0) (hQ1 : Q 1 = 0)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |deriv (fun z : ℝ =>
        ShenWork.IntervalConjugateDuhamelMap.intervalConjugateKernelOperator t Q z) x|
      ≤ 2 * HQ *
        (weightedHeatHessConst θ * t ^ (-1 + θ / 2 : ℝ)) := by
  let A : ℝ → ℝ := intervalDirectHeatHessComponent t x
  let B : ℝ → ℝ := intervalReflectedHeatHessComponent t x
  let P : ℝ → ℝ := fun y => deriv (fun z : ℝ => deriv
    (fun w : ℝ => intervalNeumannFullKernel t w y) z) x
  let M : ℝ → ℝ := fun y => deriv (fun z : ℝ => deriv
    (fun y' : ℝ => intervalNeumannFullKernel t z y') y) x
  let R : ℝ → ℝ := fun y =>
    -A y * (Q y - Q x) + B y * (Q y + Q x)
  let F : ℤ → ℝ → ℝ := fun k y =>
    -(deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
        (x - y + 2 * (k : ℝ))) * (Q y - Q x) +
      deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
        (x + y + 2 * (k : ℝ)) * (Q y + Q x)
  have hPA : ∀ y, P y = A y + B y := by
    intro y
    exact secondDeriv_intervalNeumannFullKernel_eq_components ht x y
  have hMA : ∀ y, M y = -A y + B y := by
    intro y
    exact mixedDeriv_intervalNeumannFullKernel_eq_components ht x y
  have hRseries : ∀ y, R y = ∑' k : ℤ, F k y := by
    intro y
    have hAs : Summable (fun k : ℤ =>
        deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
          (x - y + 2 * (k : ℝ))) :=
      latticeGaussianHessSummable ht (x - y)
    have hBs : Summable (fun k : ℤ =>
        deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
          (x + y + 2 * (k : ℝ))) :=
      latticeGaussianHessSummable ht (x + y)
    let da : ℤ → ℝ := fun k => deriv (fun u : ℝ => deriv
      (fun z : ℝ => heatKernel t z) u) (x - y + 2 * (k : ℝ))
    let rb : ℤ → ℝ := fun k => deriv (fun u : ℝ => deriv
      (fun z : ℝ => heatKernel t z) u) (x + y + 2 * (k : ℝ))
    have hda : Summable da := hAs
    have hrb : Summable rb := hBs
    have hAd : (∑' k : ℤ, (-da k) * (Q y - Q x)) =
        -(∑' k : ℤ, da k) * (Q y - Q x) := by
      calc
        (∑' k : ℤ, (-da k) * (Q y - Q x)) =
            (∑' k : ℤ, -da k) * (Q y - Q x) :=
          (hda.neg).tsum_mul_right (Q y - Q x)
        _ = -(∑' k : ℤ, da k) * (Q y - Q x) := by rw [tsum_neg]
    have hBd : (∑' k : ℤ, rb k * (Q y + Q x)) =
        (∑' k : ℤ, rb k) * (Q y + Q x) := by
      exact hrb.tsum_mul_right (Q y + Q x)
    change -(∑' k : ℤ, da k) * (Q y - Q x) +
      (∑' k : ℤ, rb k) * (Q y + Q x) = ∑' k : ℤ, F k y
    calc
      -(∑' k : ℤ, da k) * (Q y - Q x) +
          (∑' k : ℤ, rb k) * (Q y + Q x) =
          (∑' k : ℤ, (-da k) * (Q y - Q x)) +
            ∑' k : ℤ, rb k * (Q y + Q x) := by rw [hAd, hBd]
      _ = ∑' k : ℤ,
          ((-da k) * (Q y - Q x) + rb k * (Q y + Q x)) := by
        rw [Summable.tsum_add ((hda.neg).mul_right (Q y - Q x))
          (hrb.mul_right (Q y + Q x))]
      _ = ∑' k : ℤ, F k y := by
        refine tsum_congr (fun k => ?_)
        dsimp [F, da, rb]
  have hP_int : Integrable P (intervalMeasure 1) := by
    simp only [intervalMeasure, intervalSet]
    exact (continuousOn_secondDeriv_intervalNeumannFullKernel_fst ht x).integrableOn_Icc
  have hM_int : Integrable M (intervalMeasure 1) := by
    simp only [intervalMeasure, intervalSet]
    exact (continuousOn_mixedDeriv_intervalNeumannFullKernel ht x).integrableOn_Icc
  have hAQ_cont : ContinuousOn
      (fun y => A y * (Q y - Q x)) (Set.Icc (0 : ℝ) 1) :=
    (continuousOn_intervalDirectHeatHessComponent ht x).mul
      (hQ_cont.sub continuousOn_const)
  have hBQ_cont : ContinuousOn
      (fun y => B y * (Q y + Q x)) (Set.Icc (0 : ℝ) 1) :=
    (continuousOn_intervalReflectedHeatHessComponent ht x).mul
      (hQ_cont.add continuousOn_const)
  have hR_int : Integrable R (intervalMeasure 1) := by
    simp only [intervalMeasure, intervalSet]
    simpa [R] using (hAQ_cont.neg.add hBQ_cont).integrableOn_Icc
  have hMQ_int : Integrable (fun y => M y * Q y) (intervalMeasure 1) := by
    have hbdd : ∀ᵐ y ∂(intervalMeasure 1), ‖Q y‖ ≤ CQ :=
      Filter.Eventually.of_forall fun y => by
        simpa [Real.norm_eq_abs] using hQ_bound y
    exact hM_int.mul_bdd hQ_int.aestronglyMeasurable hbdd
  have hPx_int : Integrable (fun y => Q x * P y) (intervalMeasure 1) :=
    hP_int.const_mul (Q x)
  have hpoint : ∀ y, M y * Q y = R y - Q x * P y := by
    intro y
    rw [hPA y, hMA y]
    dsimp [R]
    ring
  have hcancel : (∫ y, P y ∂(intervalMeasure 1)) = 0 := by
    exact intervalNeumannFullKernel_secondDeriv_integral_zero ht x
  have hMR : (∫ y, M y * Q y ∂(intervalMeasure 1)) =
      ∫ y, R y ∂(intervalMeasure 1) := by
    calc
      (∫ y, M y * Q y ∂(intervalMeasure 1)) =
          ∫ y, (R y - Q x * P y) ∂(intervalMeasure 1) :=
        MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall fun y => hpoint y)
      _ = (∫ y, R y ∂(intervalMeasure 1)) -
          ∫ y, Q x * P y ∂(intervalMeasure 1) :=
        MeasureTheory.integral_sub hR_int hPx_int
      _ = (∫ y, R y ∂(intervalMeasure 1)) -
          Q x * (∫ y, P y ∂(intervalMeasure 1)) := by
        rw [MeasureTheory.integral_const_mul]
      _ = ∫ y, R y ∂(intervalMeasure 1) := by rw [hcancel]; ring
  have hF_int : ∀ k : ℤ, Integrable (F k) (intervalMeasure 1) := by
    intro k
    simp only [intervalMeasure, intervalSet]
    apply ContinuousOn.integrableOn_Icc
    change ContinuousOn
      (fun y =>
        -(deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
            (x - y + 2 * (k : ℝ))) * (Q y - Q x) +
          deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
            (x + y + 2 * (k : ℝ)) * (Q y + Q x))
      (Set.Icc (0 : ℝ) 1)
    exact ((((continuous_secondDeriv_heatKernel ht).comp (by fun_prop)).neg.continuousOn).mul
      (hQ_cont.sub continuousOn_const)).add
      ((((continuous_secondDeriv_heatKernel ht).comp (by fun_prop)).continuousOn).mul
        (hQ_cont.add continuousOn_const))
  have hF_norm_bound : ∀ k : ℤ,
      (∫ y, ‖F k y‖ ∂(intervalMeasure 1)) ≤
        2 * HQ * weightedHeatHessCellMass t θ x k := by
    intro k
    let G : ℝ → ℝ := fun y => 2 * HQ *
      (weightedHeatHess t θ (x - y + 2 * (k : ℝ)) +
        weightedHeatHess t θ (x + y + 2 * (k : ℝ)))
    have hG_cont : ContinuousOn G (Set.Icc (0 : ℝ) 1) := by
      have hgcont : Continuous (weightedHeatHess t θ) := by
        unfold weightedHeatHess
        exact (continuous_secondDeriv_heatKernel ht).abs.mul
          (continuous_abs.rpow_const (fun _ => Or.inr hθ0.le))
      exact (continuous_const.mul
        ((hgcont.comp (by fun_prop)).add (hgcont.comp (by fun_prop)))).continuousOn
    have hG_int : Integrable G (intervalMeasure 1) := by
      simp only [intervalMeasure, intervalSet]
      exact hG_cont.integrableOn_Icc
    have hae : (fun y => ‖F k y‖) ≤ᵐ[intervalMeasure 1] G := by
      simp only [intervalMeasure, intervalSet]
      refine (MeasureTheory.ae_restrict_iff' measurableSet_Icc).2 ?_
      refine Filter.Eventually.of_forall fun y hy => ?_
      have hdiff : |Q y - Q x| ≤ HQ * |x - y| ^ θ := by
        simpa [abs_sub_comm] using hQ_holder y x hy hx
      have hsum := abs_add_le_reflectedPairDistance_rpow
        hθ0 hHQ hQ0 hQ1 hQ_holder hx hy
      have hdarg := (abs_sub_le_image_args hx hy k).1
      have hrarg := reflectedPairDistance_le_image hx hy k
      have hdweight : |x - y| ^ θ ≤
          |x - y + 2 * (k : ℝ)| ^ θ :=
        Real.rpow_le_rpow (abs_nonneg _) hdarg hθ0.le
      have hrweight : (reflectedPairDistance x y) ^ θ ≤
          |x + y + 2 * (k : ℝ)| ^ θ :=
        Real.rpow_le_rpow (reflectedPairDistance_nonneg hx hy) hrarg hθ0.le
      let da := deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
        (x - y + 2 * (k : ℝ))
      let rb := deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
        (x + y + 2 * (k : ℝ))
      have hdirect : |da * (Q y - Q x)| ≤
          HQ * weightedHeatHess t θ (x - y + 2 * (k : ℝ)) := by
        rw [abs_mul]
        calc
          |da| * |Q y - Q x| ≤ |da| * (HQ * |x - y| ^ θ) :=
            mul_le_mul_of_nonneg_left hdiff (abs_nonneg _)
          _ ≤ |da| * (HQ * |x - y + 2 * (k : ℝ)| ^ θ) := by
            gcongr
          _ = HQ * weightedHeatHess t θ (x - y + 2 * (k : ℝ)) := by
            unfold weightedHeatHess da
            ring
      have hreflected : |rb * (Q y + Q x)| ≤
          2 * HQ * weightedHeatHess t θ (x + y + 2 * (k : ℝ)) := by
        rw [abs_mul]
        calc
          |rb| * |Q y + Q x| ≤
              |rb| * (2 * HQ * (reflectedPairDistance x y) ^ θ) :=
            mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
          _ ≤ |rb| * (2 * HQ * |x + y + 2 * (k : ℝ)| ^ θ) := by
            gcongr
          _ = 2 * HQ * weightedHeatHess t θ (x + y + 2 * (k : ℝ)) := by
            unfold weightedHeatHess rb
            ring
      change |F k y| ≤ G y
      calc
        |F k y| ≤ |da * (Q y - Q x)| + |rb * (Q y + Q x)| := by
          simpa only [F, da, rb, abs_mul, abs_neg] using
            abs_add_le ((-da) * (Q y - Q x)) (rb * (Q y + Q x))
        _ ≤ HQ * weightedHeatHess t θ (x - y + 2 * (k : ℝ)) +
            2 * HQ * weightedHeatHess t θ (x + y + 2 * (k : ℝ)) :=
          add_le_add hdirect hreflected
        _ ≤ G y := by
          dsimp [G]
          have hga : 0 ≤ weightedHeatHess t θ
              (x - y + 2 * (k : ℝ)) := by unfold weightedHeatHess; positivity
          have hgb : 0 ≤ weightedHeatHess t θ
              (x + y + 2 * (k : ℝ)) := by unfold weightedHeatHess; positivity
          nlinarith
    have hmono := MeasureTheory.integral_mono_ae (hF_int k).norm hG_int hae
    calc
      (∫ y, ‖F k y‖ ∂(intervalMeasure 1)) ≤
          ∫ y, G y ∂(intervalMeasure 1) := hmono
      _ = 2 * HQ * weightedHeatHessCellMass t θ x k := by
        rw [MeasureTheory.integral_const_mul]
        have hAii : IntervalIntegrable
            (fun y : ℝ => weightedHeatHess t θ
              (x - y + 2 * (k : ℝ))) volume 0 1 := by
          exact (((continuous_secondDeriv_heatKernel ht).abs.mul
            (continuous_abs.rpow_const (fun _ => Or.inr hθ0.le))).comp
              (by fun_prop)).intervalIntegrable 0 1
        have hBii : IntervalIntegrable
            (fun y : ℝ => weightedHeatHess t θ
              (x + y + 2 * (k : ℝ))) volume 0 1 := by
          exact (((continuous_secondDeriv_heatKernel ht).abs.mul
            (continuous_abs.rpow_const (fun _ => Or.inr hθ0.le))).comp
              (by fun_prop)).intervalIntegrable 0 1
        rw [MeasureTheory.integral_add]
        · rw [intervalMeasure_one_integral_eq_intervalIntegral,
            intervalMeasure_one_integral_eq_intervalIntegral]
          rfl
        · simpa only [intervalMeasure, intervalSet] using
            ((((continuous_secondDeriv_heatKernel ht).abs.mul
              (continuous_abs.rpow_const (fun _ => Or.inr hθ0.le))).comp
                (by fun_prop)).continuousOn.integrableOn_Icc)
        · simpa only [intervalMeasure, intervalSet] using
            ((((continuous_secondDeriv_heatKernel ht).abs.mul
              (continuous_abs.rpow_const (fun _ => Or.inr hθ0.le))).comp
                (by fun_prop)).continuousOn.integrableOn_Icc)
  have hF_norm_summable : Summable
      (fun k : ℤ => ∫ y, ‖F k y‖ ∂(intervalMeasure 1)) := by
    refine Summable.of_nonneg_of_le
      (fun k => MeasureTheory.integral_nonneg fun _ => norm_nonneg _)
      hF_norm_bound
      ((summable_weightedHeatHessCellMass ht hθ0 hθ1 x).mul_left (2 * HQ))
  have hInt := MeasureTheory.integral_tsum_of_summable_integral_norm
    (μ := intervalMeasure 1) (F := F) hF_int hF_norm_summable
  have hIntNormSummable : Summable
      (fun k : ℤ => ‖∫ y, F k y ∂(intervalMeasure 1)‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun k => norm_integral_le_integral_norm (F k)) hF_norm_summable
  have hIntSummable : Summable
      (fun k : ℤ => ∫ y, F k y ∂(intervalMeasure 1)) :=
    summable_norm_iff.mp hIntNormSummable
  have hRint_series : (∫ y, R y ∂(intervalMeasure 1)) =
      ∑' k : ℤ, ∫ y, F k y ∂(intervalMeasure 1) := by
    rw [show R = fun y => ∑' k : ℤ, F k y from funext hRseries]
    exact hInt.symm
  have hRbound : |∫ y, R y ∂(intervalMeasure 1)| ≤
      2 * HQ * (weightedHeatHessConst θ * t ^ (-1 + θ / 2 : ℝ)) := by
    rw [hRint_series, ← Real.norm_eq_abs]
    calc
      ‖∑' k : ℤ, ∫ y, F k y ∂(intervalMeasure 1)‖ ≤
          ∑' k : ℤ, ‖∫ y, F k y ∂(intervalMeasure 1)‖ :=
        norm_tsum_le_tsum_norm hIntNormSummable
      _ ≤ ∑' k : ℤ, 2 * HQ * weightedHeatHessCellMass t θ x k := by
        refine Summable.tsum_le_tsum (fun k => ?_) hIntNormSummable
          ((summable_weightedHeatHessCellMass ht hθ0 hθ1 x).mul_left (2 * HQ))
        exact (norm_integral_le_integral_norm (F k)).trans (hF_norm_bound k)
      _ = 2 * HQ * (∫ w : ℝ, weightedHeatHess t θ w) := by
        rw [tsum_mul_left, tsum_weightedHeatHessCellMass_eq_integral ht hθ0 hθ1]
      _ ≤ 2 * HQ *
          (weightedHeatHessConst θ * t ^ (-1 + θ / 2 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left
          (heatKernel_secondDeriv_weighted_abs_integral_le ht hθ0 hθ1)
          (mul_nonneg (by norm_num) hHQ)
  rw [(ShenWork.IntervalConjugateDuhamelMap.intervalConjugateKernelOperator_hasDerivAt
    ht hQ_int hQ_bound x).deriv, abs_neg, hMR]
  exact hRbound

end ShenWork.IntervalNeumannFullKernel
