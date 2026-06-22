import Mathlib

open MeasureTheory Filter Topology Set

open scoped Real ENNReal

noncomputable section

namespace ShenWork.IntervalNHGBrickC

/-- Real sine series. -/
def gR (b : ℕ → ℝ) : ℝ → ℝ :=
  fun x => ∑' n : ℕ, b n * Real.sin ((n : ℝ) * Real.pi * x)

/-- Odd reflection of the complexified sine series to `[-1,1]`. -/
def oddC (b : ℕ → ℝ) : ℝ → ℂ :=
  fun x => if 0 ≤ x then (gR b x : ℂ) else -(gR b (-x) : ℂ)

lemma norm_sin_le (t : ℝ) : ‖Real.sin t‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_le]; exact ⟨Real.neg_one_le_sin t, Real.sin_le_one t⟩

lemma term_norm_le (b : ℕ → ℝ) (x : ℝ) (n : ℕ) :
    ‖b n * Real.sin ((n : ℝ) * Real.pi * x)‖ ≤ ‖b n‖ := by
  rw [norm_mul]
  calc ‖b n‖ * ‖Real.sin ((n : ℝ) * Real.pi * x)‖
      ≤ ‖b n‖ * 1 := by gcongr; exact norm_sin_le _
    _ = ‖b n‖ := by ring

lemma sineSeries_summable
    {b : ℕ → ℝ} (hb_abs : Summable fun n => ‖b n‖) (x : ℝ) :
    Summable fun n : ℕ => b n * Real.sin ((n : ℝ) * Real.pi * x) :=
  Summable.of_norm_bounded hb_abs (fun n => term_norm_le b x n)

/-- `gR` is odd: `gR b (-x) = - gR b x`. -/
lemma gR_neg (b : ℕ → ℝ) (x : ℝ) : gR b (-x) = - gR b x := by
  rw [gR, gR, ← tsum_neg]
  refine tsum_congr (fun n => ?_)
  rw [show ((n : ℝ) * Real.pi * (-x)) = -((n : ℝ) * Real.pi * x) by ring, Real.sin_neg]
  ring

/-- The odd reflection is exactly the complexified (already odd) series. -/
lemma oddC_eq (b : ℕ → ℝ) : oddC b = fun x => (gR b x : ℂ) := by
  funext x
  by_cases hx : 0 ≤ x
  · simp [oddC, hx]
  · simp only [oddC, hx, if_false]
    rw [gR_neg]; push_cast; ring

/-- The real sine series is continuous (ℓ¹ uniform convergence). -/
lemma continuous_gR {b : ℕ → ℝ} (hb_abs : Summable fun n => ‖b n‖) :
    Continuous (gR b) :=
  continuous_tsum (fun n => by fun_prop) hb_abs (fun n x => term_norm_le b x n)

lemma norm_gR_le {b : ℕ → ℝ} (hb_abs : Summable fun n => ‖b n‖) (x : ℝ) :
    ‖(gR b x : ℂ)‖ ≤ ∑' n : ℕ, ‖b n‖ := by
  rw [Complex.norm_real]
  have hsn : Summable fun n : ℕ => ‖b n * Real.sin ((n : ℝ) * Real.pi * x)‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => term_norm_le b x n) hb_abs
  calc ‖gR b x‖ = ‖∑' n : ℕ, b n * Real.sin ((n : ℝ) * Real.pi * x)‖ := by rw [gR]
    _ ≤ ∑' n : ℕ, ‖b n * Real.sin ((n : ℝ) * Real.pi * x)‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' n : ℕ, ‖b n‖ := hsn.tsum_le_tsum (fun n => term_norm_le b x n) hb_abs

lemma continuous_oddC {b : ℕ → ℝ} (hb_abs : Summable fun n => ‖b n‖) :
    Continuous (oddC b) := by
  have hg : Continuous (gR b) := continuous_gR hb_abs
  have hg0 : gR b 0 = 0 := by simp [gR]
  have hgneg : Continuous (fun x : ℝ => -(gR b (-x) : ℂ)) := by
    exact ((Complex.continuous_ofReal.comp (hg.comp continuous_neg)).neg)
  have hgpos : Continuous (fun x : ℝ => (gR b x : ℂ)) :=
    Complex.continuous_ofReal.comp hg
  exact Continuous.if_le hgpos hgneg continuous_const continuous_id
    (fun x hx => by rw [← hx]; simp [hg0])

lemma oddC_memLp {b : ℕ → ℝ} (hb_abs : Summable fun n => ‖b n‖) :
    MemLp (oddC b) 2 (volume.restrict (Set.Ioc (-1 : ℝ) 1)) := by
  have hcont : Continuous (oddC b) := continuous_oddC hb_abs
  refine MemLp.of_bound hcont.aestronglyMeasurable (∑' n : ℕ, ‖b n‖) ?_
  filter_upwards with x
  by_cases hx : 0 ≤ x
  · simpa [oddC, hx] using norm_gR_le hb_abs x
  · simp only [oddC, hx, if_false, norm_neg]
    exact norm_gR_le hb_abs (-x)

/-! ### Coefficient identity -/

open AddCircle

/-- `fourierCoeffOn` of a single Fourier monomial on `[-1,1]` is `Pi.single`. -/
lemma fourierCoeffOn_fourier_unit (m k : ℤ) :
    fourierCoeffOn (show (-1 : ℝ) < 1 by norm_num)
        (fun x : ℝ => fourier (T := (2 : ℝ)) m (x : AddCircle (2 : ℝ))) k
      = (Pi.single m (1 : ℂ) : ℤ → ℂ) k := by
  letI : Fact (0 < (2 : ℝ)) := ⟨by norm_num⟩
  have hff : fourierCoeff (T := (2 : ℝ)) (fourier (T := (2:ℝ)) m)
      = (Pi.single m 1 : ℤ → ℂ) := fourierCoeff_fourier (T := (2 : ℝ)) (n := m)
  have h := congr_fun hff k
  rw [fourierCoeff_eq_intervalIntegral
        (f := fun z : AddCircle (2 : ℝ) => fourier (T := (2 : ℝ)) m z) (n := k)
        (a := (-1 : ℝ))] at h
  rw [fourierCoeffOn_eq_integral
        (f := fun x : ℝ => fourier (T := (2 : ℝ)) m (x : AddCircle (2 : ℝ))) (n := k)
        (hab := (show (-1 : ℝ) < 1 by norm_num))]
  rw [show ((1 : ℝ) - (-1)) = 2 by norm_num]
  rw [show ((-1 : ℝ) + 2 = 1) by norm_num] at h
  rw [h]

/-- Sine as a difference of two Fourier modes on `AddCircle 2`. -/
lemma sine_as_fourier (n : ℕ) (x : ℝ) :
    ((Real.sin ((n : ℝ) * Real.pi * x) : ℝ) : ℂ)
      = (fourier (T := (2 : ℝ)) (n : ℤ) (x : AddCircle (2 : ℝ))
          - fourier (T := (2 : ℝ)) (-(n : ℤ)) (x : AddCircle (2 : ℝ))) / (2 * Complex.I) := by
  rw [fourier_coe_apply, fourier_coe_apply]
  rw [Complex.ofReal_sin, Complex.sin]
  push_cast
  rw [div_eq_div_iff (by simp [Complex.I_ne_zero]) (by norm_num)]
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  ring_nf
  rw [hI2]
  ring

/-- `fourierCoeffOn` is additive (proved via the integral form). -/
lemma fourierCoeffOn_sub {a b : ℝ} (hab : a < b) (f g : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g) (k : ℤ) :
    fourierCoeffOn hab (fun x => f x - g x) k
      = fourierCoeffOn hab f k - fourierCoeffOn hab g k := by
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  have hfi : IntervalIntegrable
      (fun x => fourier (-k) ((x : AddCircle (b - a))) • f x) volume a b := by
    apply Continuous.intervalIntegrable; fun_prop
  have hgi : IntervalIntegrable
      (fun x => fourier (-k) ((x : AddCircle (b - a))) • g x) volume a b := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [← smul_sub, ← intervalIntegral.integral_sub hfi hgi]
  congr 1
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_sub]

/-- Per-mode coefficient: `fourierCoeffOn (sin(nπ·)) k = (single n − single (-n))/(2I)`. -/
lemma fourierCoeffOn_sin (n : ℕ) (k : ℤ) :
    fourierCoeffOn (show (-1 : ℝ) < 1 by norm_num)
        (fun x : ℝ => ((Real.sin ((n : ℝ) * Real.pi * x) : ℝ) : ℂ)) k
      = ((Pi.single (n : ℤ) (1:ℂ) : ℤ → ℂ) k
          - (Pi.single (-(n : ℤ)) (1:ℂ) : ℤ → ℂ) k) / (2 * Complex.I) := by
  have hfun : (fun x : ℝ => ((Real.sin ((n : ℝ) * Real.pi * x) : ℝ) : ℂ))
      = fun x : ℝ => (fourier (T := (2 : ℝ)) (n : ℤ) (x : AddCircle (2 : ℝ))
          - fourier (T := (2 : ℝ)) (-(n : ℤ)) (x : AddCircle (2 : ℝ))) / (2 * Complex.I) :=
    funext (fun x => sine_as_fourier n x)
  rw [hfun]
  have hII1 : Continuous
      (fun x : ℝ => fourier (T := (2:ℝ)) (n:ℤ) (x : AddCircle (2:ℝ))) :=
    (map_continuous _).comp (AddCircle.continuous_mk' _)
  have hII2 : Continuous
      (fun x : ℝ => fourier (T := (2:ℝ)) (-(n:ℤ)) (x : AddCircle (2:ℝ))) :=
    (map_continuous _).comp (AddCircle.continuous_mk' _)
  rw [show (fun x : ℝ => (fourier (T := (2 : ℝ)) (n : ℤ) (x : AddCircle (2 : ℝ))
        - fourier (T := (2 : ℝ)) (-(n : ℤ)) (x : AddCircle (2 : ℝ))) / (2 * Complex.I))
      = (fun x : ℝ => (2 * Complex.I)⁻¹ *
          (fourier (T := (2 : ℝ)) (n : ℤ) (x : AddCircle (2 : ℝ))
            - fourier (T := (2 : ℝ)) (-(n : ℤ)) (x : AddCircle (2 : ℝ)))) from by
    funext x; rw [div_eq_inv_mul]]
  rw [fourierCoeffOn.const_mul, fourierCoeffOn_sub _ _ _ hII1 hII2,
    fourierCoeffOn_fourier_unit, fourierCoeffOn_fourier_unit]
  rw [div_eq_inv_mul]

/-- Bundled continuous integrand term for the interchange. -/
def fcTerm (b : ℕ → ℝ) (k : ℤ) (n : ℕ) : C(ℝ, ℂ) where
  toFun := fun x => fourier (T := (2:ℝ)) (-k) (x : AddCircle (2:ℝ)) •
    ((b n * Real.sin ((n : ℝ) * Real.pi * x) : ℝ) : ℂ)
  continuous_toFun := by
    refine Continuous.mul ((map_continuous _).comp (AddCircle.continuous_mk' _)) ?_
    fun_prop

lemma fcTerm_norm_le (b : ℕ → ℝ) (k : ℤ) (n : ℕ) :
    ‖(fcTerm b k n).restrict (⟨Set.uIcc (-1:ℝ) 1, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖
      ≤ ‖b n‖ := by
  rw [ContinuousMap.norm_le _ (norm_nonneg _)]
  rintro ⟨x, hx⟩
  simp only [ContinuousMap.restrict_apply, fcTerm, ContinuousMap.coe_mk]
  rw [norm_smul]
  have hfourier : ‖fourier (T := (2:ℝ)) (-k) (x : AddCircle (2:ℝ))‖ = 1 := by
    rw [fourier_coe_apply]; rw [Complex.norm_exp]; simp
  rw [hfourier, one_mul, Complex.norm_real]
  exact term_norm_le b x n

lemma fcTerm_summable {b : ℕ → ℝ} (hb_abs : Summable fun n => ‖b n‖) (k : ℤ) :
    Summable fun n : ℕ =>
      ‖(fcTerm b k n).restrict (⟨Set.uIcc (-1:ℝ) 1, isCompact_uIcc⟩ :
        TopologicalSpace.Compacts ℝ)‖ :=
  Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => fcTerm_norm_le b k n) hb_abs

/-- Coefficient of the full sine series equals the sum of per-mode coefficients. -/
lemma fourierCoeffOn_gC (b : ℕ → ℝ) (hb_abs : Summable fun n => ‖b n‖) (k : ℤ) :
    fourierCoeffOn (show (-1:ℝ) < 1 by norm_num) (fun x => (gR b x : ℂ)) k
      = ∑' n : ℕ, b n * (((Pi.single (n : ℤ) (1:ℂ) : ℤ → ℂ) k
          - (Pi.single (-(n : ℤ)) (1:ℂ) : ℤ → ℂ) k) / (2 * Complex.I)) := by
  rw [fourierCoeffOn_eq_integral]
  -- pull the series out of the integrand and interchange
  have hgRcast : ∀ x : ℝ, ((gR b x : ℝ) : ℂ)
      = ∑' n : ℕ, ((b n * Real.sin ((n : ℝ) * Real.pi * x) : ℝ) : ℂ) := by
    intro x
    rw [gR, Complex.ofReal_tsum]
  have hintegrand : (fun x : ℝ => fourier (-k) ((x : AddCircle ((1:ℝ) - (-1)))) • (gR b x : ℂ))
      = fun x : ℝ => ∑' n : ℕ, fcTerm b k n x := by
    funext x
    rw [smul_eq_mul, hgRcast x, ← tsum_mul_left]
    refine tsum_congr (fun n => ?_)
    simp only [fcTerm, ContinuousMap.coe_mk, smul_eq_mul]
    rw [show ((1:ℝ) - (-1)) = 2 by norm_num]
  rw [hintegrand,
    ← intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm (fcTerm_summable hb_abs k)]
  rw [show ((1:ℝ) - (-1)) = 2 by norm_num, ← tsum_const_smul'' ((1:ℝ)/2)]
  refine tsum_congr (fun n => ?_)
  -- per term: (1/2) • ∫ fcTerm n = b n · coeff
  have hcoeff := fourierCoeffOn_sin n k
  rw [fourierCoeffOn_eq_integral, show ((1:ℝ) - (-1)) = 2 by norm_num] at hcoeff
  -- ∫ fcTerm n = b n • ∫ (fourier • sin)
  have hfac : (∫ x in (-1:ℝ)..1, (fcTerm b k n) x)
      = (b n : ℂ) • ∫ x in (-1:ℝ)..1,
          fourier (T := (2:ℝ)) (-k) (x : AddCircle (2:ℝ)) •
            ((Real.sin ((n : ℝ) * Real.pi * x) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_smul]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    simp only [fcTerm, ContinuousMap.coe_mk, smul_eq_mul]
    push_cast; ring
  rw [hfac, smul_comm, hcoeff, smul_eq_mul]

/-- The coefficient at `k` of the sine series, evaluated. -/
lemma fourierCoeff_value (b : ℕ → ℝ) (hb0 : b 0 = 0)
    (hb_abs : Summable fun n => ‖b n‖) (k : ℤ) :
    ‖fourierCoeffOn (show (-1:ℝ) < 1 by norm_num) (fun x => (gR b x : ℂ)) k‖ ^ 2
      = (b k.natAbs) ^ 2 / 4 := by
  rw [fourierCoeffOn_gC b hb_abs k]
  rcases eq_or_ne k 0 with hk0 | hk0
  · -- k = 0: coefficient is 0, and b 0 = 0
    subst hk0
    have hterm0 : ∀ n : ℕ, (b n : ℂ) * (((Pi.single (n : ℤ) (1:ℂ) : ℤ → ℂ) 0
          - (Pi.single (-(n : ℤ)) (1:ℂ) : ℤ → ℂ) 0) / (2 * Complex.I)) = 0 := by
      intro n
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; simp [hb0]
      · rw [Pi.single_eq_of_ne (by omega : (0:ℤ) ≠ (n:ℤ)),
          Pi.single_eq_of_ne (by omega : (0:ℤ) ≠ -(n:ℤ))]; simp
    rw [tsum_congr hterm0, tsum_zero]; simp [hb0]
  -- k ≠ 0: the tsum collapses to the n = |k| term
  have hterm : ∀ n : ℕ, (b n : ℂ) * (((Pi.single (n : ℤ) (1:ℂ) : ℤ → ℂ) k
        - (Pi.single (-(n : ℤ)) (1:ℂ) : ℤ → ℂ) k) / (2 * Complex.I))
      = if n = k.natAbs then
          (b k.natAbs : ℂ) * ((if 0 ≤ k then (1:ℂ) else -1) / (2 * Complex.I)) else 0 := by
    intro n
    by_cases hn : n = k.natAbs
    · subst hn
      rw [if_pos rfl]
      congr 2
      rcases le_or_gt 0 k with hk | hk
      · rw [show ((k.natAbs : ℤ)) = k by omega]
        rw [Pi.single_eq_same, Pi.single_eq_of_ne (by omega : k ≠ -k), sub_zero, if_pos hk]
      · rw [show ((k.natAbs : ℤ)) = -k by omega]
        rw [Pi.single_eq_of_ne (by omega : k ≠ -k), neg_neg, Pi.single_eq_same, zero_sub,
          if_neg (not_le.2 hk)]
    · rw [if_neg hn]
      have h1 : (Pi.single (n : ℤ) (1:ℂ) : ℤ → ℂ) k = 0 := by
        rw [Pi.single_eq_of_ne]; omega
      have h2 : (Pi.single (-(n : ℤ)) (1:ℂ) : ℤ → ℂ) k = 0 := by
        rw [Pi.single_eq_of_ne]; omega
      rw [h1, h2]; simp
  rw [tsum_congr hterm, tsum_ite_eq]
  rw [norm_mul, norm_div, mul_pow, div_pow]
  have hI : ‖(2 * Complex.I)‖ = 2 := by
    rw [norm_mul, Complex.norm_I, mul_one]; norm_num
  rw [hI, Complex.norm_real]
  rcases le_or_gt 0 k with hk | hk
  · rw [if_pos hk]; simp [sq_abs]; ring
  · rw [if_neg (not_le.2 hk)]; simp [sq_abs]; ring

/-- The squared mass of the odd reflection over `[-1,1]` is twice that of `gR` over `[0,1]`. -/
lemma oddC_norm_sq_integral {b : ℕ → ℝ} (hb_abs : Summable fun n => ‖b n‖) :
    (∫ x in (-1:ℝ)..1, ‖oddC b x‖ ^ 2)
      = 2 * ∫ x in (0:ℝ)..1, (gR b x) ^ 2 := by
  have hcont : Continuous (oddC b) := continuous_oddC hb_abs
  have hcontR : Continuous (gR b) := continuous_gR hb_abs
  have hII : IntervalIntegrable (fun x => ‖oddC b x‖ ^ 2) volume (-1) 1 :=
    ((hcont.norm).pow 2).intervalIntegrable _ _
  have hII0 : IntervalIntegrable (fun x => ‖oddC b x‖ ^ 2) volume 0 1 :=
    ((hcont.norm).pow 2).intervalIntegrable _ _
  have hIIneg : IntervalIntegrable (fun x => ‖oddC b x‖ ^ 2) volume (-1) 0 :=
    ((hcont.norm).pow 2).intervalIntegrable _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals hIIneg hII0]
  have hpos : (∫ x in (0:ℝ)..1, ‖oddC b x‖ ^ 2) = ∫ x in (0:ℝ)..1, (gR b x) ^ 2 := by
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    have hx0 : 0 ≤ x := by
      have : x ∈ Set.Icc (0:ℝ) 1 := by
        simpa [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hx
      exact this.1
    simp [oddC, hx0, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hneg : (∫ x in (-1:ℝ)..0, ‖oddC b x‖ ^ 2) = ∫ x in (0:ℝ)..1, (gR b x) ^ 2 := by
    have hcomp : (∫ x in (0:ℝ)..1, ‖oddC b (-x)‖ ^ 2)
        = ∫ x in (-1:ℝ)..0, ‖oddC b x‖ ^ 2 := by
      have := intervalIntegral.integral_comp_neg
        (f := fun x => ‖oddC b x‖ ^ 2) (a := (0:ℝ)) (b := 1)
      simpa using this
    rw [← hcomp]
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    have hx0 : 0 ≤ x := by
      have : x ∈ Set.Icc (0:ℝ) 1 := by
        simpa [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hx
      exact this.1
    by_cases hxz : x = 0
    · subst hxz; simp [oddC, gR]
    · have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hxz)
      have : oddC b (-x) = -(gR b x : ℂ) := by
        simp only [oddC]; rw [if_neg (by linarith : ¬ (0:ℝ) ≤ -x), neg_neg]
      rw [this]
      simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hneg, hpos]; ring

/-- **Sine-output Parseval.** `∫₀¹ (Σ bₙ sin(nπx))² = ½ Σ bₙ²`. -/
theorem sineSeries_l2_sq
    {b : ℕ → ℝ} (hb0 : b 0 = 0)
    (hb_abs : Summable fun n => ‖b n‖) (hb_sq : Summable fun n => (b n) ^ 2) :
    (∫ x in (0:ℝ)..1, (gR b x) ^ 2) = (1 / 2 : ℝ) * ∑' n : ℕ, (b n) ^ 2 := by
  -- Parseval on the doubled circle
  have hParseval := tsum_sq_fourierCoeffOn (show (-1:ℝ) < 1 by norm_num)
    (f := oddC b) (oddC_memLp hb_abs)
  rw [oddC_eq b] at hParseval
  -- LHS of Parseval = Σ_k (b_{|k|})²/4
  have hcoeffsum : (∑' k : ℤ, ‖fourierCoeffOn (show (-1:ℝ) < 1 by norm_num)
      (fun x => (gR b x : ℂ)) k‖ ^ 2) = ∑' k : ℤ, (b k.natAbs) ^ 2 / 4 :=
    tsum_congr (fun k => fourierCoeff_value b hb0 hb_abs k)
  -- fold ℤ → ℕ⁺
  have hfeven : Function.Even (fun k : ℤ => (b k.natAbs) ^ 2 / 4) := by
    intro k; simp [Int.natAbs_neg]
  have hfsumm : Summable (fun k : ℤ => (b k.natAbs) ^ 2 / 4) := by
    have h1 : Summable (fun n : ℕ => (b n) ^ 2 / 4) := hb_sq.div_const 4
    refine summable_int_iff_summable_nat_and_neg.mpr ⟨?_, ?_⟩
    · exact (h1.congr (fun n => by simp))
    · exact (h1.congr (fun n => by simp [Int.natAbs_neg]))
  have hfold := tsum_int_eq_zero_add_two_mul_tsum_pnat hfeven hfsumm
  -- Σ_{n:ℕ⁺} = Σ_{n:ℕ} (b n)²/4 since the b 0 term is 0
  have hpnat : (∑' n : ℕ+, (b (n:ℤ).natAbs) ^ 2 / 4)
      = (1/2 : ℝ) * (1/2 * ∑' n : ℕ, (b n) ^ 2) := by
    rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => (b (n:ℤ).natAbs) ^ 2 / 4)]
    have hreindex : (∑' n : ℕ, (b ((n + 1 : ℕ) : ℤ).natAbs) ^ 2 / 4)
        = ∑' n : ℕ, (b (n+1)) ^ 2 / 4 := by
      refine tsum_congr (fun n => ?_)
      have : ((n + 1 : ℕ) : ℤ).natAbs = n + 1 := by omega
      rw [this]
    rw [hreindex]
    have hsucc : (∑' n : ℕ, (b (n+1)) ^ 2 / 4) = (1/4) * ∑' n : ℕ, (b (n+1)) ^ 2 := by
      rw [← tsum_mul_left]; refine tsum_congr (fun n => by ring)
    rw [hsucc]
    have htail : (∑' n : ℕ, (b (n+1)) ^ 2) = ∑' n : ℕ, (b n) ^ 2 := by
      rw [hb_sq.tsum_eq_zero_add]; simp [hb0]
    rw [htail]; ring
  -- assemble: Parseval LHS = coeff-sum = fold; RHS = (1/2)•(2∫₀¹gR²) = ∫₀¹gR²
  rw [hcoeffsum, hfold] at hParseval
  simp only [Int.natAbs_zero, hb0] at hParseval
  rw [zero_pow (by norm_num), zero_div, zero_add] at hParseval
  -- convert ‖↑(gR)‖² → (gR)² and apply the doubled-mass lemma
  have hnormint : (∫ x in (-1:ℝ)..1, ‖(gR b x : ℂ)‖ ^ 2)
      = 2 * ∫ x in (0:ℝ)..1, (gR b x) ^ 2 := by
    rw [← oddC_norm_sq_integral hb_abs]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    rw [oddC_eq]
  rw [hnormint] at hParseval
  -- hParseval : 2 * Σ_{ℕ⁺} (b_{|·|})²/4 = (1/2) • (2 * ∫₀¹ gR²)
  rw [hpnat] at hParseval
  rw [nsmul_eq_mul, show ((1:ℝ) - (-1))⁻¹ = 1/2 by norm_num, smul_eq_mul] at hParseval
  push_cast at hParseval
  linarith [hParseval]

end ShenWork.IntervalNHGBrickC
