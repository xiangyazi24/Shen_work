import ShenWork.Paper2.IntervalWienerAlgebraResidual
import ShenWork.Paper2.IntervalMixedProduct

/-!
  # χ₀<0 last bridge: the mixed cosine×sine multiplication function bridge (Paper 2).

  Discharges `MixedMulBridge W vx` (`ShenWork.Paper2.IntervalMixedProduct`) for genuine
  pointwise products `W·vx` UNCONDITIONALLY from continuity + `ℓ¹` summability of the
  even-reflection Fourier coefficients of `W` and `vx`.

  The chain MIRRORS `cosineMulBridge_of_summable`, only the OUTPUT basis is sine and the
  inserted series is `W`'s COSINE series (so the landed pointwise cosine inversion
  `intervalCosine_hasSum_pointwise` and `intervalCosineCoeff_summable_abs` are REUSED for
  `W` — no new sine inversion is built):

  * `mulSinInt_eq_tsum` — `∫₀¹ sin(kπx) W vx = ∑'_m Ŵ_m ∫₀¹ cos(mπx) sin(kπx) vx`
    (`MeasureTheory.integral_tsum`, dominated by `|Ŵ_m|·∫₀¹|vx|`).
  * `rawSinCos_prod_to_sum` — `cos(mπx)sin(kπx)=½(sin((k+m)πx)+sgn·sin(|k−m|πx))`.
  * `rawSinInt_eq` — `∫₀¹ sin(jπx) vx = sineCoeffs vx j / 2`.
  * `sineStarExpr_eq_trueMixedProd` — the `Nat.dist` sign bookkeeping collapse into the
    landed `trueMixedProd` (mode 0 = 0, no diagonal correction since `sin 0 = 0`).
  * `mixedMulBridge_of_summable` — the discharged `MixedMulBridge`.

  No `sorry`/`admit`/`native_decide`/custom axiom.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal
open ShenWork.IntervalCosineInversion
open ShenWork.IntervalNeumannFullKernel
open ShenWork.Paper2.IntervalWienerAlgebra
open ShenWork.Paper2.IntervalMixedProduct
open ShenWork.Paper2.IntervalDivergenceModeIdentity (sineCoeffs sineCoeffs_zero
  sineCoeffs_pos)

namespace ShenWork.Paper2.IntervalMixedMulBridge

/-! ## 1. The raw sine-integral identity (function side). -/

/-- `∫₀¹ sin(jπx)·g = sineCoeffs g j / 2` (for `j = 0` both sides are `0`). -/
theorem rawSinInt_eq (g : ℝ → ℝ) (j : ℕ) :
    (∫ x in (0:ℝ)..1, Real.sin ((j:ℝ) * Real.pi * x) * g x) = sineCoeffs g j / 2 := by
  rcases eq_or_ne j 0 with rfl | hj
  · simp [sineCoeffs_zero]
  · rw [sineCoeffs_pos hj]; ring

/-- Product-to-sum on the raw integral, with the ODD-sine sign on the difference mode:
`∫₀¹ sin(kπx) cos(mπx) g = ½(∫ sin((k+m)πx) g + sgn(k−m)·∫ sin(|k−m|πx) g)`. -/
theorem rawSinCos_prod_to_sum (g : ℝ → ℝ) (hg : Continuous g) (k m : ℕ) :
    (∫ x in (0:ℝ)..1, Real.sin ((k:ℝ)*Real.pi*x) * Real.cos ((m:ℝ)*Real.pi*x) * g x)
      = (1/2) * ((∫ x in (0:ℝ)..1, Real.sin (((k+m:ℕ):ℝ)*Real.pi*x) * g x)
                 + (if m ≤ k then (1:ℝ) else -1)
                    * (∫ x in (0:ℝ)..1, Real.sin (((Nat.dist k m:ℕ):ℝ)*Real.pi*x) * g x)) := by
  set s : ℝ := if m ≤ k then (1:ℝ) else -1 with hs
  have hpt : ∀ x : ℝ,
      Real.sin ((k:ℝ)*Real.pi*x) * Real.cos ((m:ℝ)*Real.pi*x) * g x
        = (1/2) * (Real.sin (((k+m:ℕ):ℝ)*Real.pi*x) * g x
                   + s * (Real.sin (((Nat.dist k m:ℕ):ℝ)*Real.pi*x) * g x)) := by
    intro x
    have hadd := Real.sin_add ((k:ℝ)*Real.pi*x) ((m:ℝ)*Real.pi*x)
    have hsub := Real.sin_sub ((k:ℝ)*Real.pi*x) ((m:ℝ)*Real.pi*x)
    have hsum : ((k:ℝ)*Real.pi*x) + ((m:ℝ)*Real.pi*x) = ((k+m:ℕ):ℝ)*Real.pi*x := by
      push_cast; ring
    have hdist : Real.sin (((k:ℝ)*Real.pi*x) - ((m:ℝ)*Real.pi*x))
        = s * Real.sin (((Nat.dist k m:ℕ):ℝ)*Real.pi*x) := by
      set D : ℝ := ((Nat.dist k m : ℕ) : ℝ) * Real.pi * x with hD
      rcases le_total m k with h | h
      · have he : ((k:ℝ)*Real.pi*x) - ((m:ℝ)*Real.pi*x) = D := by
          have hc : (Nat.dist k m : ℝ) = (k:ℝ) - (m:ℝ) := by
            rw [Nat.dist_eq_sub_of_le_right h]; push_cast [Nat.cast_sub h]; ring
          rw [hD, hc]; ring
        rw [he, hs, if_pos h]; ring
      · have he : ((k:ℝ)*Real.pi*x) - ((m:ℝ)*Real.pi*x) = -D := by
          have hc : (Nat.dist k m : ℝ) = (m:ℝ) - (k:ℝ) := by
            rw [Nat.dist_comm, Nat.dist_eq_sub_of_le_right h]; push_cast [Nat.cast_sub h]; ring
          rw [hD, hc]; ring
        rcases eq_or_ne m k with rfl | hne
        · simp only [Nat.dist_self, Nat.cast_zero, zero_mul] at hD ⊢
          rw [he, hD]; simp
        · rw [he, Real.sin_neg, hs, if_neg (by omega)]; ring
    have hkey : Real.sin ((k:ℝ)*Real.pi*x) * Real.cos ((m:ℝ)*Real.pi*x)
        = (1/2) * (Real.sin (((k+m:ℕ):ℝ)*Real.pi*x)
                   + s * Real.sin (((Nat.dist k m:ℕ):ℝ)*Real.pi*x)) := by
      have h2 : 2 * (Real.sin ((k:ℝ)*Real.pi*x) * Real.cos ((m:ℝ)*Real.pi*x))
          = Real.sin (((k+m:ℕ):ℝ)*Real.pi*x)
            + s * Real.sin (((Nat.dist k m:ℕ):ℝ)*Real.pi*x) := by
        rw [← hsum, ← hdist, hadd, hsub]; ring
      linarith [h2]
    rw [hkey]; ring
  rw [intervalIntegral.integral_congr (fun x _ => hpt x),
    intervalIntegral.integral_const_mul]
  congr 1
  rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul]
  · exact ((Real.continuous_sin.comp (by continuity)).mul hg).intervalIntegrable _ _
  · exact (((Real.continuous_sin.comp (by continuity)).mul hg).const_mul s).intervalIntegrable _ _

/-! ## 2. The integral interchange (insert `W`'s COSINE series). -/

def sSeq (W vx : ℝ → ℝ) (k : ℕ) (m : ℕ) (x : ℝ) : ℝ :=
  cosineCoeffs W m * (Real.cos ((m:ℝ)*Real.pi*x) * Real.sin ((k:ℝ)*Real.pi*x) * vx x)

theorem sSeq_continuous (W vx : ℝ → ℝ) (hvx : Continuous vx) (k m : ℕ) :
    Continuous (sSeq W vx k m) := by
  unfold sSeq
  exact continuous_const.mul
    (((Real.continuous_cos.comp (by continuity)).mul
      (Real.continuous_sin.comp (by continuity))).mul hvx)

theorem hasSum_W_scaled (W vx : ℝ → ℝ) (hW : Continuous W)
    (hWsum : Summable (fun n : ℤ => fourierCoeff (reflCircle W) n)) (k : ℕ)
    {x : ℝ} (hx : x ∈ Set.Ioo (0:ℝ) 1) :
    HasSum (fun m : ℕ => sSeq W vx k m x)
      (Real.sin ((k:ℝ)*Real.pi*x) * (vx x * W x)) := by
  have hbase := intervalCosine_hasSum_pointwise W hW hx hWsum
  have hscaled := hbase.mul_right (Real.sin ((k:ℝ)*Real.pi*x) * vx x)
  have hval : W x * (Real.sin ((k:ℝ)*Real.pi*x) * vx x)
      = Real.sin ((k:ℝ)*Real.pi*x) * (vx x * W x) := by ring
  rw [hval] at hscaled
  refine HasSum.congr_fun hscaled ?_
  intro m; rw [unitIntervalCosineMode]; unfold sSeq; ring

set_option maxHeartbeats 1200000 in
theorem mulSinInt_eq_tsum (W vx : ℝ → ℝ) (hW : Continuous W) (hvx : Continuous vx)
    (hWsum : Summable (fun n : ℤ => fourierCoeff (reflCircle W) n)) (k : ℕ) :
    (∫ x in (0:ℝ)..1, Real.sin ((k:ℝ)*Real.pi*x) * (vx x * W x))
      = ∑' m : ℕ, cosineCoeffs W m
          * (∫ x in (0:ℝ)..1,
              Real.sin ((k:ℝ)*Real.pi*x) * Real.cos ((m:ℝ)*Real.pi*x) * vx x) := by
  have h01 : (0:ℝ) ≤ 1 := by norm_num
  rw [intervalIntegral.integral_of_le h01]
  have hd1 : Summable (fun m : ℕ => |cosineCoeffs W m|) :=
    intervalCosineCoeff_summable_abs W hW hWsum
  have hvxabs_int : IntegrableOn (fun x => |vx x|) (Set.Ioc (0:ℝ) 1) volume := by
    have : IntervalIntegrable (fun x => |vx x|) volume 0 1 :=
      (hvx.abs).intervalIntegrable 0 1
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le h01] at this
  set Iabs : ℝ := ∫ x in Set.Ioc (0:ℝ) 1, |vx x| with hIabs
  have hmeas : ∀ m : ℕ, AEStronglyMeasurable (sSeq W vx k m)
      (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    fun m => (sSeq_continuous W vx hvx k m).aestronglyMeasurable
  have hfin : (∑' m : ℕ, ∫⁻ x in Set.Ioc (0:ℝ) 1, ‖sSeq W vx k m x‖ₑ) ≠ ⊤ := by
    have hbound : ∀ m : ℕ, (∫⁻ x in Set.Ioc (0:ℝ) 1, ‖sSeq W vx k m x‖ₑ)
        ≤ ENNReal.ofReal (|cosineCoeffs W m| * Iabs) := by
      intro m
      have hpt : ∀ x, ‖sSeq W vx k m x‖ₑ
          ≤ ENNReal.ofReal (|cosineCoeffs W m| * |vx x|) := by
        intro x
        rw [Real.enorm_eq_ofReal_abs]
        apply ENNReal.ofReal_le_ofReal
        unfold sSeq
        rw [abs_mul, abs_mul, abs_mul]
        have hc1 : |Real.cos ((m:ℝ)*Real.pi*x)| ≤ 1 := Real.abs_cos_le_one _
        have hc2 : |Real.sin ((k:ℝ)*Real.pi*x)| ≤ 1 := Real.abs_sin_le_one _
        have hcc : |Real.cos ((m:ℝ)*Real.pi*x)| * |Real.sin ((k:ℝ)*Real.pi*x)| ≤ 1 :=
          mul_le_one₀ hc1 (abs_nonneg _) hc2
        have hrw : |cosineCoeffs W m| *
            (|Real.cos ((m:ℝ)*Real.pi*x)| * |Real.sin ((k:ℝ)*Real.pi*x)| * |vx x|)
            = (|cosineCoeffs W m| * |vx x|)
              * (|Real.cos ((m:ℝ)*Real.pi*x)| * |Real.sin ((k:ℝ)*Real.pi*x)|) := by ring
        rw [hrw]
        exact mul_le_of_le_one_right (by positivity) hcc
      calc (∫⁻ x in Set.Ioc (0:ℝ) 1, ‖sSeq W vx k m x‖ₑ)
          ≤ ∫⁻ x in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (|cosineCoeffs W m| * |vx x|) :=
            lintegral_mono hpt
        _ = ENNReal.ofReal (|cosineCoeffs W m| * Iabs) := by
            rw [show (fun x => ENNReal.ofReal (|cosineCoeffs W m| * |vx x|))
                  = (fun x => ENNReal.ofReal (|cosineCoeffs W m|) * ENNReal.ofReal (|vx x|)) from
                funext (fun x => by rw [ENNReal.ofReal_mul (abs_nonneg _)])]
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
                ← ofReal_integral_eq_lintegral_ofReal hvxabs_int
                  (Filter.Eventually.of_forall (fun x => abs_nonneg _)),
                ← ENNReal.ofReal_mul (abs_nonneg _)]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) (hd1.mul_right Iabs)]
    exact ENNReal.ofReal_ne_top
  have hit := MeasureTheory.integral_tsum hmeas hfin
  have hlhs : (∫ x in Set.Ioc (0:ℝ) 1, Real.sin ((k:ℝ)*Real.pi*x) * (vx x * W x))
      = ∫ x in Set.Ioc (0:ℝ) 1, ∑' m : ℕ, sSeq W vx k m x := by
    refine setIntegral_congr_ae measurableSet_Ioc ?_
    filter_upwards [Ioo_ae_eq_Ioc.symm] with x hx
    intro hmem
    have hxo : x ∈ Set.Ioo (0:ℝ) 1 := hx.mp hmem
    exact ((hasSum_W_scaled W vx hW hWsum k hxo).tsum_eq).symm
  rw [hlhs, hit]
  refine tsum_congr (fun m => ?_)
  unfold sSeq
  rw [MeasureTheory.integral_const_mul, intervalIntegral.integral_of_le h01]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc (fun x _ => ?_)
  ring

/-! ## 3. Boundedness of the sine coefficients (continuity only). -/

/-- `|sineCoeffs vx n| ≤ 2·∫₀¹|vx|` — a uniform bound from continuity alone. -/
theorem sineCoeffs_abs_le (vx : ℝ → ℝ) (hvx : Continuous vx) (n : ℕ) :
    |sineCoeffs vx n| ≤ 2 * ∫ x in (0:ℝ)..1, |vx x| := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [sineCoeffs_zero, abs_zero]
    have : (0:ℝ) ≤ ∫ x in (0:ℝ)..1, |vx x| :=
      intervalIntegral.integral_nonneg (by norm_num) (fun x _ => abs_nonneg _)
    linarith
  · rw [sineCoeffs_pos hn, abs_mul, abs_two]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    have h01 : (0:ℝ) ≤ 1 := by norm_num
    calc |∫ x in (0:ℝ)..1, Real.sin ((n:ℝ)*Real.pi*x) * vx x|
        ≤ ∫ x in (0:ℝ)..1, |Real.sin ((n:ℝ)*Real.pi*x) * vx x| :=
          intervalIntegral.abs_integral_le_integral_abs h01
      _ ≤ ∫ x in (0:ℝ)..1, |vx x| := by
          refine intervalIntegral.integral_mono_on h01 ?_ ?_ (fun x _ => ?_)
          · exact ((Real.continuous_sin.comp (by continuity)).mul hvx).abs.intervalIntegrable _ _
          · exact hvx.abs.intervalIntegrable _ _
          · rw [abs_mul]
            exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_sin_le_one _)

/-! ## 4. The collapse to `trueMixedProd`. -/

set_option maxHeartbeats 1600000 in
/-- **The mixed bridge collapse.** After interchange + product-to-sum + `rawSinInt`, the
weighted double series over `W`'s cosine modes equals the landed `trueMixedProd`. -/
theorem mixedConvSum_eq_trueMixedProd {W vx : ℝ → ℝ} (hvx : Continuous vx)
    (hWl1 : Summable (fun m => |cosineCoeffs W m|)) (k : ℕ) (hk : k ≠ 0) :
    2 * ∑' m : ℕ, cosineCoeffs W m * ((1/2 : ℝ) *
        (sineCoeffs vx (k + m) / 2
          + (if m ≤ k then (1:ℝ) else -1) * (sineCoeffs vx (Nat.dist k m) / 2)))
      = trueMixedProd (cosineCoeffs W) (sineCoeffs vx) k := by
  set a : ℕ → ℝ := cosineCoeffs W with ha_def
  set b : ℕ → ℝ := sineCoeffs vx with hb_def
  obtain ⟨B, hB0, hB⟩ : ∃ B, 0 ≤ B ∧ ∀ n, |b n| ≤ B :=
    ⟨2 * ∫ x in (0:ℝ)..1, |vx x|,
      by have : (0:ℝ) ≤ ∫ x in (0:ℝ)..1, |vx x| :=
          intervalIntegral.integral_nonneg (by norm_num) (fun x _ => abs_nonneg _)
         linarith,
      fun n => by rw [hb_def]; exact sineCoeffs_abs_le vx hvx n⟩
  -- summability of the add-term `a m · b(k+m)`
  have hsum_add : Summable (fun m => a m * b (k + m)) := by
    apply Summable.of_norm_bounded (g := fun m => |a m| * B) (hWl1.mul_right B)
    intro m; rw [Real.norm_eq_abs, abs_mul]; gcongr; exact hB _
  -- summability of the signed-diff term
  have hsum_diff : Summable
      (fun m => a m * ((if m ≤ k then (1:ℝ) else -1) * b (Nat.dist k m))) := by
    apply Summable.of_norm_bounded (g := fun m => |a m| * B) (hWl1.mul_right B)
    intro m; rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have hs : |(if m ≤ k then (1:ℝ) else -1)| = 1 := by split <;> norm_num
    rw [hs, one_mul]; gcongr; exact hB _
  -- distribute the ½ and split the tsum
  have hcongr : (fun m : ℕ => a m * ((1/2 : ℝ) *
        (b (k + m) / 2 + (if m ≤ k then (1:ℝ) else -1) * (b (Nat.dist k m) / 2))))
      = (fun m => (1/4 : ℝ) * (a m * b (k + m))
          + (1/4 : ℝ) * (a m * ((if m ≤ k then (1:ℝ) else -1) * b (Nat.dist k m)))) := by
    funext m; ring
  have hsplit : 2 * ∑' m : ℕ, a m * ((1/2 : ℝ) *
        (b (k + m) / 2 + (if m ≤ k then (1:ℝ) else -1) * (b (Nat.dist k m) / 2)))
      = (1/2) * (∑' m, a m * b (k + m))
        + (1/2) * (∑' m, a m * ((if m ≤ k then (1:ℝ) else -1) * b (Nat.dist k m))) := by
    rw [hcongr, Summable.tsum_add (hsum_add.mul_left (1/4)) (hsum_diff.mul_left (1/4)),
      tsum_mul_left, tsum_mul_left]
    ring
  rw [hsplit]
  -- corr1 b a k = ∑' m, b(m+k)·a m = ∑' m, a m·b(k+m)
  have hcorr_ba : (∑' m, a m * b (k + m)) = corr1 b a k := by
    unfold corr1; exact tsum_congr (fun m => by rw [Nat.add_comm k m]; ring)
  -- the signed-diff tsum = addConv a b k − corr1 a b k
  have hdiff : (∑' m, a m * ((if m ≤ k then (1:ℝ) else -1) * b (Nat.dist k m)))
      = addConv a b k - corr1 a b k := by
    have hsplitk := (hsum_diff.sum_add_tsum_nat_add k).symm
    rw [hsplitk]
    -- range k part: m < k, sgn = +1, dist = k−m  ⟹  addConv a b k
    have hrange : (∑ m ∈ Finset.range k,
          a m * ((if m ≤ k then (1:ℝ) else -1) * b (Nat.dist k m)))
        = addConv a b k := by
      rw [addConv_range, Finset.sum_range_succ, Nat.sub_self,
        show b 0 = (0:ℝ) from by rw [hb_def, sineCoeffs_zero], mul_zero, add_zero]
      refine Finset.sum_congr rfl (fun m hm => ?_)
      have hmk : m < k := Finset.mem_range.mp hm
      rw [if_pos (by omega), one_mul, Nat.dist_eq_sub_of_le_right (by omega)]
    -- tail m = j+k: sgn = −1 (for j≥1), dist = j; j=0 gives b 0 = 0
    have htail : (∑' j, a (j + k) * ((if j + k ≤ k then (1:ℝ) else -1) * b (Nat.dist k (j+k))))
        = - corr1 a b k := by
      unfold corr1
      rw [← tsum_neg]
      refine tsum_congr (fun j => ?_)
      have hdist : Nat.dist k (j + k) = j := by
        rw [Nat.dist_eq_sub_of_le (by omega)]; omega
      rw [hdist]
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp [hb_def, sineCoeffs_zero]
      · rw [if_neg (by omega)]; ring
    rw [hrange, htail]; ring
  rw [hcorr_ba, hdiff, trueMixedProd_pos hk]
  unfold mixedConv signedDiffConv
  ring

/-! ## 5. The discharged mixed-multiplication bridge. -/

set_option maxHeartbeats 1600000 in
/-- **The mixed cosine×sine multiplication bridge, discharged from `ℓ¹` cosine/sine
coefficients.**  For continuous `W, vx` on `[0,1]` whose even-reflection Fourier
coefficients are summable, the SINE coefficients of the product `W·vx` equal the exact
`trueMixedProd` of `W`'s COSINE coeffs and `vx`'s SINE coeffs at every mode — i.e.
`MixedMulBridge W vx` holds. -/
theorem mixedMulBridge_of_summable {W vx : ℝ → ℝ} (hW : Continuous W) (hvx : Continuous vx)
    (hWsum : Summable (fun n : ℤ => fourierCoeff (reflCircle W) n))
    (_hvxsum : Summable (fun n : ℤ => fourierCoeff (reflCircle vx) n)) :
    MixedMulBridge W vx := by
  intro k
  have hWl1 : Summable (fun m => |cosineCoeffs W m|) :=
    intervalCosineCoeff_summable_abs W hW hWsum
  rcases eq_or_ne k 0 with rfl | hk
  · rw [sineCoeffs_zero, trueMixedProd]; simp
  · -- sineCoeffs (W·vx) k = 2 · ∫ sin(kπx)·(W·vx)
    rw [sineCoeffs_pos hk]
    rw [show (∫ x in (0:ℝ)..1, Real.sin ((k:ℝ)*Real.pi*x) * (W x * vx x))
        = ∫ x in (0:ℝ)..1, Real.sin ((k:ℝ)*Real.pi*x) * (vx x * W x) from by
      refine intervalIntegral.integral_congr (fun x _ => ?_); ring]
    rw [mulSinInt_eq_tsum W vx hW hvx hWsum k]
    -- product-to-sum + rawSinInt inside the tsum, then collapse
    have hterm : ∀ m, cosineCoeffs W m * (∫ x in (0:ℝ)..1,
          Real.sin ((k:ℝ)*Real.pi*x) * Real.cos ((m:ℝ)*Real.pi*x) * vx x)
        = cosineCoeffs W m * ((1/2 : ℝ) *
            (sineCoeffs vx (k + m) / 2
              + (if m ≤ k then (1:ℝ) else -1) * (sineCoeffs vx (Nat.dist k m) / 2))) := by
      intro m
      rw [rawSinCos_prod_to_sum vx hvx k m, rawSinInt_eq vx (k+m), rawSinInt_eq vx (Nat.dist k m)]
    rw [tsum_congr hterm]
    exact mixedConvSum_eq_trueMixedProd hvx hWl1 k hk

end ShenWork.Paper2.IntervalMixedMulBridge

section AxiomAudit
open ShenWork.Paper2.IntervalMixedMulBridge
#print axioms mixedMulBridge_of_summable
end AxiomAudit
