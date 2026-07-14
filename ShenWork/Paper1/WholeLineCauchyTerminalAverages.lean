import ShenWork.Paper1.WholeLineCauchySemigroupRestart

open Filter Topology MeasureTheory Real Set
open scoped Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# Terminal averages for the whole-line Cauchy Duhamel formula

The short terminal reaction window converges to the reaction source in BUC.
For the divergence window, Gaussian integration by parts moves the spatial
derivative onto the physical flux.  The endpoint where the heat lag is zero
is discarded only as a measure-zero point; no false value is assigned to the
totalized gradient operator there.
-/

/-- A continuous BUC source is recovered from its short terminal heat
average. -/
theorem wholeLineCauchyRecentHeatAverage_tendsto
    (F : ℝ → WholeLineBUC) {t : ℝ}
    (hF : ContinuousAt F t)
    (hInt : ∀ h : ℝ, 0 < h →
      IntervalIntegrable
        (fun s => wholeLineCauchyHeatBUCTotal (t + h - s) (F s))
        volume t (t + h)) :
    Tendsto
      (fun h : ℝ => h⁻¹ • ∫ s in t..(t + h),
        wholeLineCauchyHeatBUCTotal (t + h - s) (F s))
      (𝓝[>] (0 : ℝ)) (𝓝 (F t)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hε4 : 0 < ε / 4 := by linarith
  rw [Metric.continuousAt_iff] at hF
  obtain ⟨δF, hδF, hFdist⟩ := hF (ε / 4) hε4
  have hHeat := wholeLineCauchyHeatBUCTotal_continuousAt_zero (F t)
  rw [Metric.continuousAt_iff] at hHeat
  obtain ⟨δH, hδH, hHdist⟩ := hHeat (ε / 4) hε4
  refine ⟨min δF δH, lt_min hδF hδH, ?_⟩
  intro h hh hhdist
  have hhpos : 0 < h := hh
  rw [Real.dist_eq, sub_zero, abs_of_pos hhpos] at hhdist
  let G : ℝ → WholeLineBUC := fun s =>
    wholeLineCauchyHeatBUCTotal (t + h - s) (F s)
  have hG : IntervalIntegrable G volume t (t + h) := hInt h hhpos
  have hconst : IntervalIntegrable (fun _ : ℝ => F t) volume t (t + h) :=
    _root_.intervalIntegrable_const (μ := volume) (c := F t)
  have hpoint : ∀ s ∈ Ι t (t + h), ‖G s - F t‖ < ε / 2 := by
    intro s hs
    rw [Set.uIoc_of_le (le_add_of_nonneg_right hhpos.le)] at hs
    have hst : t ≤ s := hs.1.le
    have hsth : s ≤ t + h := hs.2
    have hsDist : dist s t < δF := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hst)]
      have : s - t ≤ h := by linarith
      exact lt_of_le_of_lt this (lt_of_lt_of_le hhdist (min_le_left _ _))
    have hlag0 : 0 ≤ t + h - s := by linarith
    have hlagDist : dist (t + h - s) 0 < δH := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hlag0]
      have : t + h - s ≤ h := by linarith
      exact lt_of_le_of_lt this (lt_of_lt_of_le hhdist (min_le_right _ _))
    have hsource : dist (F s) (F t) < ε / 4 := hFdist hsDist
    have hheat0 :
        dist (wholeLineCauchyHeatBUCTotal (t + h - s) (F t)) (F t) < ε / 4 := by
      simpa using hHdist hlagDist
    rw [← WholeLineBUC.dist_eq_norm_sub]
    calc
      dist (G s) (F t) ≤
          dist (G s) (wholeLineCauchyHeatBUCTotal (t + h - s) (F t)) +
            dist (wholeLineCauchyHeatBUCTotal (t + h - s) (F t)) (F t) :=
        dist_triangle _ _ _
      _ ≤ dist (F s) (F t) +
            dist (wholeLineCauchyHeatBUCTotal (t + h - s) (F t)) (F t) := by
        exact add_le_add
          (wholeLineCauchyHeatBUCTotal_dist_le_of_nonneg hlag0 (F s) (F t)) le_rfl
      _ < ε / 4 + ε / 4 := add_lt_add hsource hheat0
      _ = ε / 2 := by ring
  have hdistEq : dist
      (h⁻¹ • ∫ s in t..t + h,
        wholeLineCauchyHeatBUCTotal (t + h - s) (F s))
      (F t) =
      ‖h⁻¹ • ∫ s in t..t + h, (G s - F t)‖ := by
    rw [WholeLineBUC.dist_eq_norm_sub,
      intervalIntegral.integral_sub hG hconst,
      @intervalIntegral.integral_const WholeLineBUC
        WholeLineBUC.normedAddCommGroup inferInstance t (t + h)
        wholeLineBUCMetricCompleteSpace (F t)]
    dsimp [G]
    rw [smul_sub]
    simp [hhpos.ne']
  rw [hdistEq]
  calc
    ‖h⁻¹ • ∫ s in t..t + h, (G s - F t)‖ =
        |h⁻¹| * ‖∫ s in t..t + h, (G s - F t)‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ |h⁻¹| * ((ε / 2) * |t + h - t|) := by
      gcongr
      exact intervalIntegral.norm_integral_le_of_norm_le_const
        (fun s hs => (hpoint s hs).le)
    _ = ε / 2 := by
      have hinvabs : |h⁻¹| = h⁻¹ := abs_of_pos (inv_pos.mpr hhpos)
      have habsh : |t + h - t| = h := by
        rw [show t + h - t = h by ring, abs_of_pos hhpos]
      rw [hinvabs, habsh]
      field_simp
    _ < ε := by linarith

/-- The terminal reaction Duhamel average converges in BUC to the current
reaction source. -/
theorem wholeLineCauchyValueRecentAverage_tendsto
    (p : CMParams) {M T t : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) (ht : 0 < t) :
    Tendsto
      (fun h : ℝ => h⁻¹ • ∫ s in t..(t + h),
        wholeLineCauchyValueBUCIntegrand p hM hT U (t + h) s)
      (𝓝[>] (0 : ℝ))
      (𝓝 (wholeLineCauchyReactionSourceTrajectory p hM hT U t)) := by
  apply wholeLineCauchyRecentHeatAverage_tendsto
  · exact (wholeLineCauchyReactionSourceTrajectory_continuous
      p hM hT U).continuousAt
  · intro h hh
    have hth : 0 ≤ t + h := (add_pos ht hh).le
    have hfull := wholeLineCauchyValueBUCIntegrand_intervalIntegrable
      p hM hT U hth
    have hrecent : IntervalIntegrable
        (wholeLineCauchyValueBUCIntegrand p hM hT U (t + h))
        volume t (t + h) := by
      apply hfull.mono_set
      rw [Set.uIcc_of_le (le_add_of_nonneg_right hh.le),
        Set.uIcc_of_le hth]
      exact Set.Icc_subset_Icc_left ht.le
    simpa [wholeLineCauchyValueBUCIntegrand] using hrecent

/-- A global positive Holder modulus is a uniform continuity modulus. -/
theorem wholeLineUniformContinuous_of_holder
    {g : ℝ → ℝ} {rho H : ℝ} (hrho : 0 < rho) (hH : 0 ≤ H)
    (hholder : ∀ x y, |g x - g y| ≤ H * |x - y| ^ rho) :
    UniformContinuous g := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  let δ : ℝ := min 1 ((ε / (H + 1)) ^ (1 / rho))
  have hδ : 0 < δ := by
    dsimp [δ]
    apply lt_min one_pos
    apply Real.rpow_pos_of_pos
    positivity
  refine ⟨δ, hδ, ?_⟩
  intro x y hxy
  rw [Real.dist_eq] at hxy ⊢
  have hxy0 : 0 ≤ |x - y| := abs_nonneg _
  have hpow : |x - y| ^ rho ≤ δ ^ rho :=
    Real.rpow_le_rpow hxy0 hxy.le hrho.le
  have hδpow : δ ^ rho ≤ ε / (H + 1) := by
    have hle : δ ≤ (ε / (H + 1)) ^ (1 / rho) := by
      dsimp [δ]
      exact min_le_right _ _
    calc
      δ ^ rho ≤ ((ε / (H + 1)) ^ (1 / rho)) ^ rho :=
        Real.rpow_le_rpow hδ.le hle hrho.le
      _ = ε / (H + 1) := by
        rw [← Real.rpow_mul (by positivity), one_div,
          inv_mul_cancel₀ (ne_of_gt hrho), Real.rpow_one]
  calc
    |g x - g y| ≤ H * |x - y| ^ rho := hholder x y
    _ ≤ H * (ε / (H + 1)) :=
      mul_le_mul_of_nonneg_left (hpow.trans hδpow) hH
    _ < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [mul_nonneg hH hε.le]

/-- At every positive physical time, the differentiated chemotaxis flux is a
genuine bounded uniformly continuous function. -/
theorem wholeLineCauchyFluxDerivative_paperCUnifBdd_positive
    (p : CMParams) {M T theta eta : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (z : Set.Icc (0 : ℝ) T) (hz : 0 < z.1)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hrel : eta * (1 + theta) < theta)
    (hstrip : ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M) :
    let U := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    PaperCUnifBdd
      (deriv (wholeLineCauchyFluxSourceTrajectory p hM hT U z.1).1) := by
  dsimp only
  let U := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let F := (wholeLineCauchyFluxSourceTrajectory p hM hT U z.1).1
  rcases wholeLineCauchyFluxSourceTrajectory_slice_deriv_holder_positive
      p hM hT u₀ hsmall z hz htheta0 htheta1 heta0 heta1 hrel hstrip with
    ⟨rho, H, hrho, _hrho1, hH, hholder⟩
  rcases wholeLineCauchyFluxSourceTrajectory_restartC1Data_positive
      p hM hT u₀ hsmall z hz htheta0 htheta1 heta0 heta1 hrel hstrip with
    ⟨_hhas, _hcont, D, hD⟩
  refine ⟨?_, D, ?_⟩
  · apply wholeLineUniformContinuous_of_holder hrho hH
    simpa [U, F] using hholder
  · simpa [U, F] using hD

/-- The differentiated positive-time physical flux as an element of
`BUC(ℝ)`. -/
noncomputable def wholeLineCauchyFluxDerivativeBUCPositive
    (p : CMParams) {M T theta eta : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (z : Set.Icc (0 : ℝ) T) (hz : 0 < z.1)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hrel : eta * (1 + theta) < theta)
    (hstrip : ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M) : WholeLineBUC :=
  let U := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  wholeLineBUCOfPaperCUnifBdd
    (deriv (wholeLineCauchyFluxSourceTrajectory p hM hT U z.1).1)
    (wholeLineCauchyFluxDerivative_paperCUnifBdd_positive p hM hT u₀ hsmall z hz
      htheta0 htheta1 heta0 heta1 hrel hstrip)

@[simp] theorem wholeLineCauchyFluxDerivativeBUCPositive_apply
    (p : CMParams) {M T theta eta : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (z : Set.Icc (0 : ℝ) T) (hz : 0 < z.1)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hrel : eta * (1 + theta) < theta)
    (hstrip : ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M) (x : ℝ) :
    (wholeLineCauchyFluxDerivativeBUCPositive p hM hT u₀ hsmall z hz
      htheta0 htheta1 heta0 heta1 hrel hstrip).1 x =
      deriv
        (wholeLineCauchyFluxSourceTrajectory p hM hT
          (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) z.1).1 x := by
  rfl

/-- For a bounded `C1` source, positive-time gradient heat flow is ordinary
heat flow applied to its BUC derivative. -/
theorem wholeLineCauchyHeatGradientBUCTotal_eq_heatDerivativeBUC
    {q D : ℝ} (hq : 0 < q) (f df : WholeLineBUC)
    (hdf : ∀ x, df.1 x = deriv f.1 x)
    (hfd : ∀ x, |deriv f.1 x| ≤ D)
    (hfderiv : ∀ x, HasDerivAt f.1 (deriv f.1 x) x)
    (hfdcont : Continuous (deriv f.1)) :
    wholeLineCauchyHeatGradientBUCTotal q f =
      wholeLineCauchyHeatBUCTotal q df := by
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro x
  simp only [wholeLineCauchyHeatGradientBUCTotal,
    wholeLineCauchyHeatBUCTotal, dif_pos hq,
    wholeLineCauchyHeatGradientBUC_apply,
    wholeLineCauchyHeatBUC_apply]
  rw [wholeLineCauchyHeatGradOp_eq_heatOp_deriv hq
    (fun y => by simpa [Real.norm_eq_abs] using f.1.norm_coe_le_norm y)
    hfd hfderiv hfdcont]
  congr 1
  funext y
  exact (hdf y).symm

/-- The short terminal divergence Duhamel average converges in BUC to the
spatial derivative of the current physical flux. -/
theorem wholeLineCauchyGradientRecentAverage_tendsto_fixedPoint
    (p : CMParams) {M T t theta eta : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (ht : 0 < t) (htT : t < T)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hrel : eta * (1 + theta) < theta)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M) :
    let U := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    let zt : Set.Icc (0 : ℝ) T := ⟨t, ht.le, htT.le⟩
    let Dt := wholeLineCauchyFluxDerivativeBUCPositive p hM hT u₀ hsmall zt ht
      htheta0 htheta1 heta0 heta1 hrel (hstrip zt)
    Tendsto
      (fun h : ℝ => h⁻¹ • ∫ s in t..(t + h),
        wholeLineCauchyGradientBUCIntegrand p hM hT U (t + h) s)
      (𝓝[>] (0 : ℝ)) (𝓝 Dt) := by
  dsimp only
  let U := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let zt : Set.Icc (0 : ℝ) T := ⟨t, ht.le, htT.le⟩
  let Dt := wholeLineCauchyFluxDerivativeBUCPositive p hM hT u₀ hsmall zt ht
    htheta0 htheta1 heta0 heta1 hrel (hstrip zt)
  have hDeriv :=
    wholeLineCauchyFluxSourceTrajectory_deriv_uniformContinuousAt_positive
      p hM hT u₀ hsmall zt ht htT htheta0 htheta1
        heta0 heta1 hrel hstrip
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hε8 : 0 < ε / 8 := by linarith
  obtain ⟨δD, hδD, hDclose⟩ := hDeriv (ε / 8) hε8
  have hHeat := wholeLineCauchyHeatBUCTotal_continuousAt_zero Dt
  rw [Metric.continuousAt_iff] at hHeat
  obtain ⟨δH, hδH, hHclose⟩ := hHeat (ε / 8) hε8
  have hTt : 0 < T - t := sub_pos.mpr htT
  refine ⟨min δD (min δH (T - t)),
    lt_min hδD (lt_min hδH hTt), ?_⟩
  intro h hh hhdist
  have hhpos : 0 < h := hh
  rw [Real.dist_eq, sub_zero, abs_of_pos hhpos] at hhdist
  have hhD : h < δD :=
    hhdist.trans_le (min_le_left _ _)
  have hhH : h < δH :=
    hhdist.trans_le ((min_le_right δD _).trans (min_le_left _ _))
  have hhT : h < T - t :=
    hhdist.trans_le ((min_le_right δD _).trans (min_le_right _ _))
  have hthT : t + h < T := by linarith
  let G : ℝ → WholeLineBUC := fun s =>
    wholeLineCauchyGradientBUCIntegrand p hM hT U (t + h) s
  have hGfull := wholeLineCauchyGradientBUCIntegrand_intervalIntegrable
    p hM hT U (add_pos ht hhpos).le
  have hG : IntervalIntegrable G volume t (t + h) := by
    apply hGfull.mono_set
    rw [Set.uIcc_of_le (le_add_of_nonneg_right hhpos.le),
      Set.uIcc_of_le (add_pos ht hhpos).le]
    exact Set.Icc_subset_Icc_left ht.le
  have hconst : IntervalIntegrable (fun _ : ℝ => Dt) volume t (t + h) :=
    _root_.intervalIntegrable_const (μ := volume) (c := Dt)
  have hpoint : ∀ᵐ s,
      s ∈ Ι t (t + h) → ‖G s - Dt‖ ≤ ε / 2 := by
    filter_upwards [Measure.ae_ne volume (t + h)] with s hsend hs
    rw [Set.uIoc_of_le (le_add_of_nonneg_right hhpos.le)] at hs
    have hst : t < s := hs.1
    have hsth : s < t + h := lt_of_le_of_ne hs.2 hsend
    have hspos : 0 < s := ht.trans hst
    have hsT : s ≤ T := (hsth.trans hthT).le
    let zs : Set.Icc (0 : ℝ) T := ⟨s, hspos.le, hsT⟩
    let Ds := wholeLineCauchyFluxDerivativeBUCPositive p hM hT u₀ hsmall zs hspos
      htheta0 htheta1 heta0 heta1 hrel (hstrip zs)
    have hsclose : |s - t| < δD := by
      rw [abs_of_nonneg (sub_nonneg.mpr hst.le)]
      have : s - t < h := by linarith
      exact this.trans hhD
    have hDsDt : dist Ds Dt ≤ ε / 8 := by
      rw [WholeLineBUC.dist_eq_norm_sub]
      change ‖Ds.1 - Dt.1‖ ≤ ε / 8
      refine (BoundedContinuousFunction.norm_le hε8.le).2 ?_
      intro x
      rw [Real.norm_eq_abs]
      simpa [Ds, Dt, zs, zt, U] using (hDclose s hsclose x).le
    have hlag : 0 < t + h - s := sub_pos.mpr hsth
    have hlag0 : 0 ≤ t + h - s := hlag.le
    have hlagH : dist (t + h - s) 0 < δH := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hlag]
      have : t + h - s < h := by linarith
      exact this.trans hhH
    have hheat0 :
        dist (wholeLineCauchyHeatBUCTotal (t + h - s) Dt) Dt < ε / 8 := by
      simpa using hHclose hlagH
    rcases wholeLineCauchyFluxSourceTrajectory_restartC1Data_positive
        p hM hT u₀ hsmall zs hspos htheta0 htheta1
          heta0 heta1 hrel (hstrip zs) with
      ⟨hhas, hcont, D, hDbound⟩
    have hGeq : G s = wholeLineCauchyHeatBUCTotal (t + h - s) Ds := by
      dsimp [G, wholeLineCauchyGradientBUCIntegrand]
      apply wholeLineCauchyHeatGradientBUCTotal_eq_heatDerivativeBUC
        hlag _ _ (fun x => by simp [Ds, zs]) hDbound hhas hcont
    rw [← WholeLineBUC.dist_eq_norm_sub, hGeq]
    calc
      dist (wholeLineCauchyHeatBUCTotal (t + h - s) Ds) Dt ≤
          dist (wholeLineCauchyHeatBUCTotal (t + h - s) Ds)
              (wholeLineCauchyHeatBUCTotal (t + h - s) Dt) +
            dist (wholeLineCauchyHeatBUCTotal (t + h - s) Dt) Dt :=
        dist_triangle _ _ _
      _ ≤ dist Ds Dt +
            dist (wholeLineCauchyHeatBUCTotal (t + h - s) Dt) Dt := by
        exact add_le_add
          (wholeLineCauchyHeatBUCTotal_dist_le_of_nonneg hlag0 Ds Dt) le_rfl
      _ ≤ ε / 8 + ε / 8 := add_le_add hDsDt hheat0.le
      _ ≤ ε / 2 := by linarith
  have hdistEq : dist
      (h⁻¹ • ∫ s in t..t + h,
        wholeLineCauchyGradientBUCIntegrand p hM hT U (t + h) s)
      Dt = ‖h⁻¹ • ∫ s in t..t + h, (G s - Dt)‖ := by
    rw [WholeLineBUC.dist_eq_norm_sub,
      intervalIntegral.integral_sub hG hconst,
      @intervalIntegral.integral_const WholeLineBUC
        WholeLineBUC.normedAddCommGroup inferInstance t (t + h)
        wholeLineBUCMetricCompleteSpace Dt]
    dsimp [G]
    rw [smul_sub]
    simp [hhpos.ne']
  rw [hdistEq]
  calc
    ‖h⁻¹ • ∫ s in t..t + h, (G s - Dt)‖ =
        |h⁻¹| * ‖∫ s in t..t + h, (G s - Dt)‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ |h⁻¹| * ((ε / 2) * |t + h - t|) := by
      gcongr
      exact intervalIntegral.norm_integral_le_of_norm_le_const_ae hpoint
    _ = ε / 2 := by
      have hinvabs : |h⁻¹| = h⁻¹ := abs_of_pos (inv_pos.mpr hhpos)
      have habsh : |t + h - t| = h := by
        rw [show t + h - t = h by ring, abs_of_pos hhpos]
      rw [hinvabs, habsh]
      field_simp
    _ < ε := by linarith

section WholeLineCauchyTerminalAveragesAxiomAudit

#print axioms wholeLineCauchyRecentHeatAverage_tendsto
#print axioms wholeLineCauchyValueRecentAverage_tendsto
#print axioms wholeLineUniformContinuous_of_holder
#print axioms wholeLineCauchyFluxDerivative_paperCUnifBdd_positive
#print axioms wholeLineCauchyFluxDerivativeBUCPositive
#print axioms wholeLineCauchyHeatGradientBUCTotal_eq_heatDerivativeBUC
#print axioms wholeLineCauchyGradientRecentAverage_tendsto_fixedPoint

end WholeLineCauchyTerminalAveragesAxiomAudit

end ShenWork.Paper1
