import ShenWork.Paper1.Theorem12EnergyProducer
import ShenWork.Paper1.WholeLineCauchyGlobalGluing
import ShenWork.Paper1.WavePositiveLeftEndpoint

open Filter MeasureTheory Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Available global-Cauchy inputs for the corrected Step 4 energy argument

This file records exactly the fields that the canonical global BUC solution
already supplies to the corrected Section 5 energy producer.  It deliberately
does not package the still-missing weighted Sobolev propagation, dominated
time differentiation, or Step 4 compactness statements as assumptions.
-/

theorem wholeLineCauchyGlobal_coMoving_slice_isCUnifBdd
    (p : CMParams) (u₀ : WholeLineBUC) (c t : ℝ) :
    IsCUnifBdd (coMovingPath c (wholeLineCauchyGlobalU p u₀) t) := by
  apply isCUnifBdd_comp_add_const
  exact WholeLineBUC.isCUnifBdd (wholeLineCauchyGlobalBUC p u₀ t)

theorem wholeLineCauchyGlobal_coMoving_mem_Icc_stableCeiling
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    coMovingPath c (wholeLineCauchyGlobalU p u₀) t x ∈
      Set.Icc (0 : ℝ) (wholeLineCauchyStableCeiling p u₀) := by
  constructor
  · exact wholeLineCauchyGlobal_nonnegative p hregime u₀ hu₀ ht (x + c * t)
  · exact wholeLineCauchyGlobal_le_stableCeiling
      p hregime u₀ hu₀ ht (x + c * t)

theorem wholeLineCauchyGlobal_coMovingV_eq_frozenElliptic
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (c : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    coMovingPath c (wholeLineCauchyGlobalV p u₀) t =
      frozenElliptic p
        (coMovingPath c (wholeLineCauchyGlobalU p u₀) t) := by
  have huC : IsCUnifBdd (wholeLineCauchyGlobalU p u₀ t) :=
    WholeLineBUC.isCUnifBdd (wholeLineCauchyGlobalBUC p u₀ t)
  have hu0 : ∀ x, 0 ≤ wholeLineCauchyGlobalU p u₀ t x :=
    fun x => wholeLineCauchyGlobal_nonnegative p hregime u₀ hu₀ ht x
  change
    (fun x => frozenElliptic p (wholeLineCauchyGlobalU p u₀ t)
        (x + c * t)) =
      frozenElliptic p
        (fun x => wholeLineCauchyGlobalU p u₀ t (x + c * t))
  exact (frozenElliptic_comp_add_const_fun p huC hu0 (c * t)).symm

theorem wholeLineCauchyGlobal_weightedEnergy_control
    (p : CMParams) (u₀ : WholeLineBUC) (η c : ℝ) (U : ℝ → ℝ) :
    ∀ᶠ t in atTop,
      coMovingWeightedL2Energy η c (wholeLineCauchyGlobalU p u₀) U t ≤
        paper5WeightedEnergy η c (wholeLineCauchyGlobalU p u₀) U t := by
  filter_upwards [] with t
  exact (paper5WeightedEnergy_eq_coMovingWeightedL2Energy
    η c (wholeLineCauchyGlobalU p u₀) U t).symm.le

/-! ## The weighted initial seed -/

/-- The canonical global solution realizes the supplied weighted initial
closeness at time zero in the co-moving coordinates used by Section 5. -/
theorem wholeLineCauchyGlobal_weightedInitialCloseness
    (p : CMParams) (u₀ : WholeLineBUC) (η c : ℝ) (U : ℝ → ℝ)
    (hclose : WeightedL2InitialCloseness η u₀.1 U) :
    Integrable (fun x =>
      Real.exp (2 * η * x) *
        |coMovingPath c (wholeLineCauchyGlobalU p u₀) 0 x - U x| ^ 2) := by
  have hinit : wholeLineCauchyGlobalU p u₀ 0 = u₀.1 := by
    funext x
    exact wholeLineCauchyGlobal_hasInitialDatum p u₀ x
  simpa [WeightedL2InitialCloseness, coMovingPath, hinit] using hclose

/-- At time zero the canonical full energy is exactly the weighted norm of
the prescribed perturbation. -/
theorem wholeLineCauchyGlobal_weightedEnergy_zero_eq_initial
    (p : CMParams) (u₀ : WholeLineBUC) (η c : ℝ) (U : ℝ → ℝ) :
    paper5WeightedEnergy η c (wholeLineCauchyGlobalU p u₀) U 0 =
      ∫ x, Real.exp (2 * η * x) * |u₀.1 x - U x| ^ 2 := by
  rw [paper5WeightedEnergy_eq_coMovingWeightedL2Energy]
  unfold coMovingWeightedL2Energy
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [mul_zero, add_zero]
  rw [wholeLineCauchyGlobal_hasInitialDatum p u₀ x]

/-- The initial weighted population belongs to `L²`; this is the exact
zero-time endpoint of the `hclose` producer requested by the energy identity. -/
theorem wholeLineCauchyGlobal_weightedPopulation_sq_integrable_zero
    (p : CMParams) (u₀ : WholeLineBUC) (η c : ℝ) (U : ℝ → ℝ)
    (hclose : WeightedL2InitialCloseness η u₀.1 U) :
    Integrable (fun x =>
      (paper5WeightedPopulation η
        (coMovingPath c (wholeLineCauchyGlobalU p u₀)) U 0 x) ^ 2) := by
  have hseed := wholeLineCauchyGlobal_weightedInitialCloseness
    p u₀ η c U hclose
  refine hseed.congr (Filter.Eventually.of_forall fun x => ?_)
  change Real.exp (2 * η * x) *
      |coMovingPath c (wholeLineCauchyGlobalU p u₀) 0 x - U x| ^ 2 =
    (Real.exp (η * x) *
      (coMovingPath c (wholeLineCauchyGlobalU p u₀) 0 x - U x)) ^ 2
  rw [mul_pow, sq_abs]
  congr 1
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

/-! ## Positive-time chart localization for Step 4 -/

/-- After the first restart step, the preferred canonical segment is always
evaluated at least one full step away from its initial face. -/
theorem wholeLineCauchyGlobalStep_le_localTime
    (p : CMParams) (u₀ : WholeLineBUC) {t : ℝ}
    (ht : wholeLineCauchyGlobalStep p u₀ ≤ t) :
    wholeLineCauchyGlobalStep p u₀ ≤
      wholeLineCauchyGlobalLocalTime p u₀ t := by
  let δ := wholeLineCauchyGlobalStep p u₀
  have hδ : 0 < δ := wholeLineCauchyGlobalStep_pos p u₀
  have ht0 : 0 ≤ t := hδ.le.trans ht
  have hratio1 : 1 ≤ t / δ := by
    exact (le_div_iff₀ hδ).2 (by simpa [δ] using ht)
  have hratio0 : 0 ≤ t / δ := zero_le_one.trans hratio1
  generalize hk : Nat.floor (t / δ) = k
  cases k with
  | zero =>
      have hlt : t / δ < 1 := by
        simpa [hk] using Nat.lt_floor_add_one (t / δ)
      exact (not_lt_of_ge hratio1 hlt).elim
  | succ n =>
      have hklo : (((n + 1 : ℕ) : ℝ)) ≤ t / δ := by
        have := Nat.floor_le hratio0
        rw [hk] at this
        simpa [Nat.succ_eq_add_one] using this
      have hklo' : (((n + 1 : ℕ) : ℝ)) * δ ≤ t :=
        (le_div_iff₀ hδ).mp hklo
      have hk' :
          Nat.floor (t / wholeLineCauchyGlobalStep p u₀) = n + 1 := by
        simpa [δ] using hk
      unfold wholeLineCauchyGlobalLocalTime wholeLineCauchyGlobalIndex
      rw [if_pos ht0, hk']
      simp only [Nat.pred_succ]
      dsimp [δ] at hklo'
      push_cast at hklo'
      linarith

/-- A datum-uniform version of the explicit positive-time slice Holder
coefficient.  It is used with a common norm ceiling for every restart datum. -/
def wholeLineCauchySliceHolderWindowConst
    (p : CMParams) (M C a b theta : ℝ) : ℝ :=
  let MF : ℝ := M ^ p.m * M ^ p.γ
  let MR : ℝ := M + M * (1 + M ^ p.α)
  let Hheat : ℝ := max
    ((2 / Real.sqrt (4 * Real.pi)) * C * a ^ (-(1 / 2 : ℝ)))
    (2 * C)
  let Hgrad : ℝ :=
    (2 : ℝ) ^ (1 - theta) *
      ((5 * Real.sqrt 2 / 2) ^ theta *
        (2 / Real.sqrt (4 * Real.pi)) ^ (1 - theta)) *
      MF * (b ^ ((1 - theta) / 2 : ℝ) / ((1 - theta) / 2))
  let Hvalue : ℝ := max
    ((2 / Real.sqrt (4 * Real.pi)) * MR * (2 * Real.sqrt b))
    (2 * (MR * b))
  Hheat + |p.χ| * Hgrad + Hvalue

theorem wholeLineCauchySliceHolderWindowConst_nonneg
    (p : CMParams) {M C a b theta : ℝ}
    (hM : 0 ≤ M) (hC : 0 ≤ C) (ha : 0 < a) (hb : 0 ≤ b)
    (htheta1 : theta < 1) :
    0 ≤ wholeLineCauchySliceHolderWindowConst p M C a b theta := by
  unfold wholeLineCauchySliceHolderWindowConst
  dsimp only
  have hden : 0 < (1 - theta) / 2 := by linarith
  positivity

/-- The explicit slice coefficient is bounded uniformly when the datum norm
and the positive time window have common bounds. -/
theorem wholeLineCauchySliceHolderConst_le_window
    (p : CMParams) {M C a b t theta : ℝ} {u₀ : WholeLineBUC}
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hnorm : ‖u₀‖ ≤ C)
    (ha : 0 < a) (ht : t ∈ Set.Icc a b)
    (htheta1 : theta < 1) :
    wholeLineCauchySliceHolderConst p M u₀ t theta ≤
      wholeLineCauchySliceHolderWindowConst p M C a b theta := by
  have ht0 : 0 ≤ t := ha.le.trans ht.1
  have hb0 : 0 ≤ b := ht0.trans ht.2
  have hneg : (-(1 / 2 : ℝ)) ≤ 0 := by norm_num
  have hpowNeg : t ^ (-(1 / 2 : ℝ)) ≤ a ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos ha ht.1 hneg
  have hexp : 0 < (1 - theta) / 2 := by linarith
  have hpowPos : t ^ ((1 - theta) / 2 : ℝ) ≤
      b ^ ((1 - theta) / 2 : ℝ) :=
    Real.rpow_le_rpow ht0 ht.2 hexp.le
  have hsqrt : Real.sqrt t ≤ Real.sqrt b := Real.sqrt_le_sqrt ht.2
  let A : ℝ := 2 / Real.sqrt (4 * Real.pi)
  let MF : ℝ := M ^ p.m * M ^ p.γ
  let MR : ℝ := M + M * (1 + M ^ p.α)
  let G : ℝ :=
    (2 : ℝ) ^ (1 - theta) *
      ((5 * Real.sqrt 2 / 2) ^ theta *
        (2 / Real.sqrt (4 * Real.pi)) ^ (1 - theta)) * MF
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hMF : 0 ≤ MF := by dsimp [MF]; positivity
  have hMR : 0 ≤ MR := by dsimp [MR]; positivity
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hheat1 : A * ‖u₀‖ * t ^ (-(1 / 2 : ℝ)) ≤
      A * C * a ^ (-(1 / 2 : ℝ)) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left hnorm hA) hpowNeg
      (Real.rpow_nonneg ht0 _) (mul_nonneg hA hC)
  have hheat2 : 2 * ‖u₀‖ ≤ 2 * C := by nlinarith
  have hgrad : G * (t ^ ((1 - theta) / 2 : ℝ) /
        ((1 - theta) / 2)) ≤
      G * (b ^ ((1 - theta) / 2 : ℝ) / ((1 - theta) / 2)) := by
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hpowPos hexp.le) hG
  have hvalue1 : A * MR * (2 * Real.sqrt t) ≤
      A * MR * (2 * Real.sqrt b) := by
    exact mul_le_mul_of_nonneg_left (by nlinarith)
      (mul_nonneg hA hMR)
  have hvalue2 : 2 * (MR * t) ≤ 2 * (MR * b) := by
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left ht.2 hMR) (by norm_num)
  unfold wholeLineCauchySliceHolderConst
    wholeLineCauchySliceHolderWindowConst
  dsimp only
  exact add_le_add
    (add_le_add (max_le_max hheat1 hheat2)
      (mul_le_mul_of_nonneg_left
        (by simpa [G, MF, mul_assoc] using hgrad) (abs_nonneg p.χ)))
    (max_le_max hvalue1 hvalue2)

/-- Every global canonical slice after the first restart step has one common
spatial `C^(1/2)` coefficient. -/
theorem wholeLineCauchyGlobal_slice_holder_eventual
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ t x y : ℝ,
      wholeLineCauchyGlobalStep p u₀ ≤ t →
      |wholeLineCauchyGlobalU p u₀ t x -
          wholeLineCauchyGlobalU p u₀ t y| ≤
        H * |x - y| ^ (1 / 2 : ℝ) := by
  let M := wholeLineCauchyGlobalClamp p u₀
  let C := wholeLineCauchyStableCeiling p u₀
  let a := wholeLineCauchyGlobalStep p u₀
  let b := wholeLineCauchyGlobalSegmentTime p u₀
  let theta : ℝ := 1 / 2
  let H := wholeLineCauchySliceHolderWindowConst p M C a b theta
  have hM : 0 ≤ M := (wholeLineCauchyGlobalClamp_pos p u₀).le
  have hC : 0 ≤ C :=
    zero_le_one.trans (wholeLineCauchyStableCeiling_one_le hregime u₀)
  have ha : 0 < a := wholeLineCauchyGlobalStep_pos p u₀
  have hb : 0 ≤ b := (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
  have htheta0 : 0 < theta := by norm_num [theta]
  have htheta1 : theta < 1 := by norm_num [theta]
  have hH : 0 ≤ H :=
    wholeLineCauchySliceHolderWindowConst_nonneg p hM hC ha hb htheta1
  refine ⟨H, hH, ?_⟩
  intro t x y ht
  have ht0 : 0 ≤ t := ha.le.trans ht
  let n := wholeLineCauchyGlobalIndex p u₀ t
  let q := wholeLineCauchyGlobalLocalTime p u₀ t
  have hqa : a ≤ q := by
    simpa [a, q] using wholeLineCauchyGlobalStep_le_localTime p u₀ ht
  have hqb : q ≤ b := by
    exact (wholeLineCauchyGlobalLocalTime_lt_segmentTime p u₀ ht0).le
  have hq0 : 0 < q := ha.trans_le hqa
  let z : Set.Icc (0 : ℝ) b := ⟨q, hq0.le, hqb⟩
  let w : WholeLineBUC := wholeLineCauchyGlobalDatum p u₀ n
  have hw := (wholeLineCauchyGlobalDatum_segment_bounds
    p hregime u₀ hu₀ n).1
  have hnorm : ‖w‖ ≤ C := by
    change ‖w.1‖ ≤ C
    apply (BoundedContinuousFunction.norm_le hC).2
    intro r
    rw [Real.norm_eq_abs, abs_of_nonneg (hw.1 r)]
    exact hw.2 r
  have hraw := wholeLineCauchyBUCMildFixedPoint_slice_Ctheta_explicit
    p hM hb w (wholeLineCauchyGlobalSegmentTime_rate p u₀) z hq0
      htheta0 htheta1
  have hcoeff :
      wholeLineCauchySliceHolderConst p M w q theta ≤ H := by
    exact wholeLineCauchySliceHolderConst_le_window p hM hC hnorm ha
      ⟨hqa, hqb⟩ htheta1
  have hsegment :
      |(wholeLineCauchyGlobalSegment p u₀ n z).1 x -
          (wholeLineCauchyGlobalSegment p u₀ n z).1 y| ≤
        H * |x - y| ^ theta := by
    calc
      |(wholeLineCauchyGlobalSegment p u₀ n z).1 x -
          (wholeLineCauchyGlobalSegment p u₀ n z).1 y| ≤
          wholeLineCauchySliceHolderConst p M w q theta *
            |x - y| ^ theta := by
              simpa [wholeLineCauchyGlobalSegment, M, b, w, n, q, z]
                using hraw.2 x y
      _ ≤ H * |x - y| ^ theta :=
        mul_le_mul_of_nonneg_right hcoeff
          (Real.rpow_nonneg (abs_nonneg _) _)
  have heq := wholeLineCauchyGlobalBUC_eq_segment p u₀ ht0
  have heq' : wholeLineCauchyGlobalBUC p u₀ t =
      wholeLineCauchyGlobalSegment p u₀ n z := by
    simpa [n, q, z, b] using heq
  change |(wholeLineCauchyGlobalBUC p u₀ t).1 x -
      (wholeLineCauchyGlobalBUC p u₀ t).1 y| ≤ _
  rw [heq']
  simpa [theta] using hsegment

/-- The canonical global solution supplies the spatial equicontinuity half of
Step 4.  Translation to the wave frame does not change spatial distances. -/
theorem wholeLineCauchyGlobal_eventuallyUniformMovingFrameSpatialModulus
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (c : ℝ) {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V) :
    EventuallyUniformMovingFrameSpatialModulus 0
      (coMovingPath c (wholeLineCauchyGlobalU p u₀)) U := by
  rcases wholeLineCauchyGlobal_slice_holder_eventual p hregime u₀ hu₀ with
    ⟨H, hH, hholder⟩
  have hU := travelingWave_U_uniformContinuous hTW hreg.U_cont
  rw [Metric.uniformContinuous_iff] at hU
  intro ε hε
  obtain ⟨δU, hδU, hUmod⟩ := hU (ε / 2) (by positivity)
  let ρ : ℝ := ε / (2 * (H + 1))
  let δH : ℝ := ρ ^ 2
  have hρ : 0 < ρ := by
    dsimp [ρ]
    positivity
  have hδH : 0 < δH := sq_pos_of_pos hρ
  have hHρ : H * ρ < ε / 2 := by
    have hfrac : H / (H + 1) < 1 := by
      rw [div_lt_one (by linarith)]
      linarith
    calc
      H * ρ = (ε / 2) * (H / (H + 1)) := by
        dsimp [ρ]
        field_simp [show H + 1 ≠ 0 by linarith]
      _ < (ε / 2) * 1 :=
        mul_lt_mul_of_pos_left hfrac (by positivity)
      _ = ε / 2 := by ring
  refine ⟨min δU δH, lt_min hδU hδH,
    wholeLineCauchyGlobalStep p u₀, ?_⟩
  intro t x y ht hxy
  have hxyU : dist x y < δU := by
    rw [Real.dist_eq]
    exact hxy.trans_le (min_le_left _ _)
  have hUxy : |U x - U y| < ε / 2 := by
    simpa [Real.dist_eq] using hUmod hxyU
  have hxyH : |x - y| < δH :=
    hxy.trans_le (min_le_right _ _)
  have hsqrt : Real.sqrt |x - y| < ρ := by
    have hsqrt' := Real.sqrt_lt_sqrt (abs_nonneg (x - y)) hxyH
    simpa [δH, Real.sqrt_sq hρ.le] using hsqrt'
  have hpow : H * |x - y| ^ (1 / 2 : ℝ) < ε / 2 := by
    rw [← Real.sqrt_eq_rpow]
    exact (mul_le_mul_of_nonneg_left hsqrt.le hH).trans_lt hHρ
  have huxy := hholder t (x + c * t) (y + c * t) ht
  have hshift : |(x + c * t) - (y + c * t)| = |x - y| := by
    congr 1
    ring
  rw [hshift] at huxy
  have huxy' :
      |wholeLineCauchyGlobalU p u₀ t (x + c * t) -
          wholeLineCauchyGlobalU p u₀ t (y + c * t)| < ε / 2 :=
    huxy.trans_lt hpow
  simp only [movingFrameError, coMovingPath, zero_mul, sub_zero]
  calc
    |(wholeLineCauchyGlobalU p u₀ t (x + c * t) - U x) -
        (wholeLineCauchyGlobalU p u₀ t (y + c * t) - U y)| ≤
        |wholeLineCauchyGlobalU p u₀ t (x + c * t) -
          wholeLineCauchyGlobalU p u₀ t (y + c * t)| +
          |U x - U y| := by
            calc
              _ = |(wholeLineCauchyGlobalU p u₀ t (x + c * t) -
                    wholeLineCauchyGlobalU p u₀ t (y + c * t)) -
                  (U x - U y)| := by ring_nf
              _ ≤ _ := abs_sub _ _
    _ < ε / 2 + ε / 2 := add_lt_add huxy' hUxy
    _ = ε := by ring

/-- The complete nonnegative-global/frame-control fragment currently
available for the canonical BUC solution.  The omitted fields are precisely
the analytic producers that cannot be obtained from the present classical
solution interface alone. -/
theorem wholeLineCauchyGlobal_step4Energy_available_data
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (η c : ℝ) (U : ℝ → ℝ) :
    let u := wholeLineCauchyGlobalU p u₀
    let v := wholeLineCauchyGlobalV p u₀
    let E := paper5WeightedEnergy η c u U
    IsGlobalNonnegativeCauchySolutionFrom p u₀.1 u v ∧
      (∀ᶠ t in atTop, coMovingWeightedL2Energy η c u U t ≤ E t) ∧
      (∀ t, IsCUnifBdd (coMovingPath c u t)) ∧
      (∀ t, 0 ≤ t → ∀ x,
        coMovingPath c u t x ∈
          Set.Icc (0 : ℝ) (wholeLineCauchyStableCeiling p u₀)) ∧
      (∀ t, 0 ≤ t →
        coMovingPath c v t = frozenElliptic p (coMovingPath c u t)) := by
  dsimp only
  refine ⟨wholeLineCauchyGlobal_isGlobalNonnegativeCauchySolutionFrom
      p hregime u₀ hu₀, wholeLineCauchyGlobal_weightedEnergy_control
      p u₀ η c U, ?_, ?_, ?_⟩
  · exact fun t => wholeLineCauchyGlobal_coMoving_slice_isCUnifBdd p u₀ c t
  · exact fun t ht x =>
      wholeLineCauchyGlobal_coMoving_mem_Icc_stableCeiling
        p hregime u₀ hu₀ c ht x
  · exact fun t ht => wholeLineCauchyGlobal_coMovingV_eq_frozenElliptic
      p hregime u₀ hu₀ c ht

/-- Function-level specialization for the paper's actual BUC datum class.
This is the strongest direct bridge from the global construction toward the
`hcore` surface: it gives a nonnegative global solution and a (possibly large)
uniform ceiling, but makes no claim that the ceiling is close enough to
`MChi p` for the corrected quadratic to remain negative. -/
theorem paperNonnegativeInitialDatum_step4Energy_available_data
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : ℝ → ℝ) (hu₀ : PaperNonnegativeInitialDatum u₀)
    (η c : ℝ) (U : ℝ → ℝ) :
    ∃ u v : ℝ → ℝ → ℝ, ∃ E : ℝ → ℝ, ∃ M : ℝ,
      IsGlobalNonnegativeCauchySolutionFrom p u₀ u v ∧
      (∀ᶠ t in atTop, coMovingWeightedL2Energy η c u U t ≤ E t) ∧
      (∀ t, IsCUnifBdd (coMovingPath c u t)) ∧
      (∀ t, 0 ≤ t → ∀ x, coMovingPath c u t x ∈ Set.Icc (0 : ℝ) M) ∧
      (∀ t, 0 ≤ t →
        coMovingPath c v t = frozenElliptic p (coMovingPath c u t)) := by
  let w : WholeLineBUC := wholeLineBUCOfPaperCUnifBdd u₀ hu₀.1
  have hw0 : ∀ x, 0 ≤ w.1 x := by
    intro x
    simpa [w] using hu₀.2 x
  have hdata := wholeLineCauchyGlobal_step4Energy_available_data
    p hregime w hw0 η c U
  refine ⟨wholeLineCauchyGlobalU p w, wholeLineCauchyGlobalV p w,
    paper5WeightedEnergy η c (wholeLineCauchyGlobalU p w) U,
    wholeLineCauchyStableCeiling p w, ?_⟩
  simpa [w] using hdata

section Theorem12Step4EnergyProducerAxiomAudit

#print axioms wholeLineCauchyGlobal_coMoving_slice_isCUnifBdd
#print axioms wholeLineCauchyGlobal_coMoving_mem_Icc_stableCeiling
#print axioms wholeLineCauchyGlobal_coMovingV_eq_frozenElliptic
#print axioms wholeLineCauchyGlobal_weightedEnergy_control
#print axioms wholeLineCauchyGlobal_weightedInitialCloseness
#print axioms wholeLineCauchyGlobal_weightedEnergy_zero_eq_initial
#print axioms wholeLineCauchyGlobal_weightedPopulation_sq_integrable_zero
#print axioms wholeLineCauchyGlobalStep_le_localTime
#print axioms wholeLineCauchySliceHolderWindowConst_nonneg
#print axioms wholeLineCauchySliceHolderConst_le_window
#print axioms wholeLineCauchyGlobal_slice_holder_eventual
#print axioms
  wholeLineCauchyGlobal_eventuallyUniformMovingFrameSpatialModulus
#print axioms wholeLineCauchyGlobal_step4Energy_available_data
#print axioms paperNonnegativeInitialDatum_step4Energy_available_data

end Theorem12Step4EnergyProducerAxiomAudit

end ShenWork.Paper1
