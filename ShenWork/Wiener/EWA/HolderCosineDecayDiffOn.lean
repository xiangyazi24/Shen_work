/-
  # `ShenWork.Wiener.EWA.HolderCosineDecayDiffOn`

  A **`DifferentiableOn (Set.Icc 0 1)`** variant of `HolderCosineDecay`.

  The committed `holderCosineCoeff_summable` (`HolderCosineDecay.lean:409`) assumes
  `Differentiable ℝ f` (global).  But its only use of the derivative is through the
  integration-by-parts identity `cos_integral_eq_neg_sine_integral`, whose Mathlib IBP
  (`intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt`) integrates over
  `[0,1]` and needs only a one-sided `HasDerivWithinAt` on the **closed** interval `[0,1]`.

  Here we re-prove the chain assuming only

    * `Continuous g`                                   (so `cosineCoeffs` are well-defined),
    * `DifferentiableOn ℝ g (Set.Icc 0 1)`             (the `[0,1]` differentiability),
    * `derivWithin g (Icc 0 1) 0 = 0 ∧ … 1 = 0`        (Neumann, on `[0,1]`),
    * `∀ x y ∈ [0,1], |g'⁻ x − g'⁻ y| ≤ K |x−y|^η`     (`η`-Hölder of `derivWithin` on `[0,1]`),

  where `g'⁻ = derivWithin g (Icc 0 1)`.  The conclusion is `Summable |cosineCoeffs g n|`.

  The Hölder modulus of `derivWithin g (Icc 0 1)` only constrains `[0,1]`, while the committed
  `sine_integral_holder_decay` needs a global `η`-Hölder modulus (it probes a half-period strip
  `[0,1+1/n]`).  We bridge by the clamp extension `Dᶜ x := derivWithin g (Icc 0 1) (clamp01 x)`,
  which is globally `η`-Hölder (clamp is `1`-Lipschitz) and agrees with `derivWithin` on `[0,1]`,
  so the boundary `∫₀¹` integral is unchanged.

  No `sorry`/`admit`/custom `axiom`/`native_decide`.
-/
import ShenWork.Wiener.EWA.HolderCosineDecay
import ShenWork.Paper2.IntervalDomainL2StaticVDifference

open MeasureTheory Set
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalCosineInversion
open ShenWork.Paper2 (clamp01 clamp01_mem clamp01_eq_self clamp01_continuous)

namespace ShenWork.Wiener.EWA

/-- IBP over `[0,1]` using only a closed-interval `HasDerivWithinAt`.  With
`v x = sin(nπx)/(nπ)` (so `v' = cos(nπx)`) and the boundary term killed by
`sin 0 = sin(nπ) = 0`,
`∫₀¹ cos(nπx) g = −(1/(nπ)) ∫₀¹ (derivWithin g [0,1])(x) sin(nπx) dx`. -/
theorem cos_integral_eq_neg_sine_integral_diffOn (g : ℝ → ℝ)
    (_hg : Continuous g) (hg' : DifferentiableOn ℝ g (Set.Icc (0:ℝ) 1))
    (hD_cont : Continuous (fun x => derivWithin g (Set.Icc (0:ℝ) 1) (clamp01 x)))
    {n : ℕ} (hn : 1 ≤ n) :
    (∫ x in (0 : ℝ)..1, Real.cos ((n : ℝ) * Real.pi * x) * g x) =
      -(1 / ((n : ℝ) * Real.pi)) *
        ∫ x in (0 : ℝ)..1,
          derivWithin g (Set.Icc (0:ℝ) 1) x * Real.sin ((n : ℝ) * Real.pi * x) := by
  have hnπ_pos : 0 < (n : ℝ) * Real.pi :=
    mul_pos (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn) Real.pi_pos
  have hnπ_ne : ((n : ℝ) * Real.pi) ≠ 0 := ne_of_gt hnπ_pos
  set v : ℝ → ℝ := fun x => Real.sin ((n : ℝ) * Real.pi * x) / ((n : ℝ) * Real.pi) with hv
  -- `v` has derivative `cos(nπx)` everywhere; here as a closed-interval one-sided deriv.
  have hv_deriv : ∀ x : ℝ, HasDerivAt v (Real.cos ((n : ℝ) * Real.pi * x)) x := by
    intro x
    have hinner : HasDerivAt (fun x : ℝ => (n : ℝ) * Real.pi * x) ((n : ℝ) * Real.pi) x := by
      simpa using (hasDerivAt_id x).const_mul ((n : ℝ) * Real.pi)
    have hs : HasDerivAt (fun x : ℝ => Real.sin ((n : ℝ) * Real.pi * x))
        (Real.cos ((n : ℝ) * Real.pi * x) * ((n : ℝ) * Real.pi)) x :=
      (Real.hasDerivAt_sin ((n : ℝ) * Real.pi * x)).comp x hinner
    have := hs.div_const ((n : ℝ) * Real.pi)
    simpa [hv, mul_div_assoc, mul_div_cancel_right₀ _ hnπ_ne] using this
  -- closed-interval data for `g` (one-sided `HasDerivWithinAt` from `DifferentiableOn`).
  have huIcc : Set.uIcc (0:ℝ) 1 = Set.Icc (0:ℝ) 1 := Set.uIcc_of_le (by norm_num)
  have hu_data : ∀ x ∈ Set.uIcc (0:ℝ) 1,
      HasDerivWithinAt g (derivWithin g (Set.Icc (0:ℝ) 1) x) (Set.uIcc (0:ℝ) 1) x := by
    intro x hx
    rw [huIcc] at hx ⊢
    exact (hg' x hx).hasDerivWithinAt
  have hv_data : ∀ x ∈ Set.uIcc (0:ℝ) 1,
      HasDerivWithinAt v (Real.cos ((n : ℝ) * Real.pi * x)) (Set.uIcc (0:ℝ) 1) x :=
    fun x _ => (hv_deriv x).hasDerivWithinAt
  -- integrability of `u' = derivWithin g [0,1]` over `[0,1]`: it equals the continuous
  -- clamp extension `Dᶜ` on `[0,1]`, which is interval-integrable.
  have hu'_int : IntervalIntegrable (derivWithin g (Set.Icc (0:ℝ) 1)) volume 0 1 := by
    have hDc_int : IntervalIntegrable
        (fun x => derivWithin g (Set.Icc (0:ℝ) 1) (clamp01 x)) volume 0 1 :=
      hD_cont.intervalIntegrable _ _
    refine hDc_int.congr ?_
    have : Set.uIoc (0:ℝ) 1 ⊆ Set.Icc (0:ℝ) 1 := by
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact Set.Ioc_subset_Icc_self
    intro x hx
    change derivWithin g (Set.Icc (0:ℝ) 1) (clamp01 x) =
      derivWithin g (Set.Icc (0:ℝ) 1) x
    rw [clamp01_eq_self (this hx)]
  have hcos_int : IntervalIntegrable
      (fun x => Real.cos ((n : ℝ) * Real.pi * x)) volume 0 1 :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hIBP :
      (∫ x in (0 : ℝ)..1, g x * Real.cos ((n : ℝ) * Real.pi * x)) =
        g 1 * v 1 - g 0 * v 0
          - ∫ x in (0 : ℝ)..1, derivWithin g (Set.Icc (0:ℝ) 1) x * v x :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
      hu_data hv_data hu'_int hcos_int
  -- boundary term vanishes.
  have hv0 : v 0 = 0 := by simp [hv]
  have hv1 : v 1 = 0 := by
    have hsin1 : Real.sin ((n : ℝ) * Real.pi * 1) = 0 := by
      rw [mul_one]; exact_mod_cast Real.sin_nat_mul_pi n
    show Real.sin ((n : ℝ) * Real.pi * 1) / ((n : ℝ) * Real.pi) = 0
    rw [hsin1, zero_div]
  rw [hv0, hv1] at hIBP
  have hcomm : (∫ x in (0 : ℝ)..1, Real.cos ((n : ℝ) * Real.pi * x) * g x) =
      ∫ x in (0 : ℝ)..1, g x * Real.cos ((n : ℝ) * Real.pi * x) := by
    apply intervalIntegral.integral_congr; intro x _; ring
  have hpull : (∫ x in (0 : ℝ)..1, derivWithin g (Set.Icc (0:ℝ) 1) x * v x) =
      (1 / ((n : ℝ) * Real.pi)) *
        ∫ x in (0 : ℝ)..1,
          derivWithin g (Set.Icc (0:ℝ) 1) x * Real.sin ((n : ℝ) * Real.pi * x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr; intro x _
    show derivWithin g (Set.Icc (0:ℝ) 1) x
        * (Real.sin ((n : ℝ) * Real.pi * x) / ((n : ℝ) * Real.pi)) =
      1 / ((n : ℝ) * Real.pi) *
        (derivWithin g (Set.Icc (0:ℝ) 1) x * Real.sin ((n : ℝ) * Real.pi * x))
    ring
  rw [hcomm, hIBP, hpull]; ring

/-- **Main closed-interval decay bound.**  A function that is differentiable on
`[0,1]`, with `η`-Hölder closed-interval derivative, has cosine coefficients decaying
like `n^{-(1+η)}`.

The derivative used in the sine-decay lemma is the clamped representative
`x ↦ derivWithin g (Icc 0 1) (clamp01 x)`, so no global differentiability of `g` is
required. -/
theorem holderCosineCoeff_decay_diffOn (g : ℝ → ℝ)
    (hg : Continuous g) (hg' : DifferentiableOn ℝ g (Set.Icc (0:ℝ) 1))
    (hD_cont : Continuous (fun x => derivWithin g (Set.Icc (0:ℝ) 1) (clamp01 x)))
    (_hNeumann : derivWithin g (Set.Icc (0:ℝ) 1) 0 = 0 ∧
      derivWithin g (Set.Icc (0:ℝ) 1) 1 = 0)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) {K : ℝ} (hK : 0 ≤ K)
    (hHolder : ∀ x y, x ∈ Set.Icc (0:ℝ) 1 → y ∈ Set.Icc (0:ℝ) 1 →
      |derivWithin g (Set.Icc (0:ℝ) 1) x -
        derivWithin g (Set.Icc (0:ℝ) 1) y| ≤ K * |x - y| ^ η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      |cosineCoeffs g n| ≤ C * (n : ℝ) ^ (-(1 + η)) := by
  classical
  let D : ℝ → ℝ := fun x => derivWithin g (Set.Icc (0:ℝ) 1) (clamp01 x)
  have hD_holder : ∀ x y : ℝ, |D x - D y| ≤ K * |x - y| ^ η := by
    intro x y
    have hxy := hHolder (clamp01 x) (clamp01 y) (clamp01_mem x) (clamp01_mem y)
    have hclamp : |clamp01 x - clamp01 y| ≤ |x - y| := by
      have hlip : LipschitzWith 1 clamp01 :=
        ((LipschitzWith.id.const_min (1 : ℝ)).const_max (0 : ℝ))
      have := hlip.dist_le_mul x y
      simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using this
    have hp : |clamp01 x - clamp01 y| ^ η ≤ |x - y| ^ η :=
      Real.rpow_le_rpow (abs_nonneg _) hclamp (le_of_lt hη0)
    exact (hxy.trans (mul_le_mul_of_nonneg_left hp hK))
  set Cη : ℝ := (1 / 2) * (K + 2 * (|D 0| + K * 2 ^ η)) with hCη
  have hCη_nonneg : 0 ≤ Cη := by
    rw [hCη]
    have : (0:ℝ) ≤ K * 2 ^ η := mul_nonneg hK (by positivity)
    positivity
  refine ⟨2 * Cη / Real.pi, by positivity, fun n hn => ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hπpos : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [cosineCoeffs_eq_two_mul_integral g hg hn,
    cos_integral_eq_neg_sine_integral_diffOn g hg hg' hD_cont hn]
  set S := ∫ x in (0 : ℝ)..1,
    derivWithin g (Set.Icc (0:ℝ) 1) x * Real.sin ((n : ℝ) * Real.pi * x) with hSdef
  set Sc := ∫ x in (0 : ℝ)..1, D x * Real.sin ((n : ℝ) * Real.pi * x) with hScdef
  have hS_eq : S = Sc := by
    rw [hSdef, hScdef]
    apply intervalIntegral.integral_congr
    intro x hx
    have hxIcc : x ∈ Set.Icc (0:ℝ) 1 := by
      rwa [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
    change derivWithin g (Set.Icc (0:ℝ) 1) x * Real.sin ((n : ℝ) * Real.pi * x) =
      derivWithin g (Set.Icc (0:ℝ) 1) (clamp01 x) * Real.sin ((n : ℝ) * Real.pi * x)
    rw [clamp01_eq_self hxIcc]
  have hSbd : |Sc| ≤ Cη * (n : ℝ) ^ (-η) := by
    rw [hCη]
    exact sine_integral_holder_decay D hD_cont hη0 hη1 hK hD_holder hn
  have habs :
      |2 * (-(1 / ((n : ℝ) * Real.pi)) * S)| =
        (2 / ((n : ℝ) * Real.pi)) * |S| := by
    rw [abs_mul, abs_mul, abs_neg]
    rw [abs_of_pos (show (0:ℝ) < 1 / ((n:ℝ) * Real.pi) by positivity)]
    rw [show |(2:ℝ)| = 2 by norm_num]
    ring
  rw [habs, hS_eq]
  have hrpow : (n : ℝ) ^ (-η) = (n : ℝ) ^ (-(1 + η)) * (n : ℝ) := by
    rw [show (-η : ℝ) = (-(1 + η)) + 1 by ring, Real.rpow_add hnpos, Real.rpow_one]
  calc (2 / ((n : ℝ) * Real.pi)) * |Sc|
      ≤ (2 / ((n : ℝ) * Real.pi)) * (Cη * (n : ℝ) ^ (-η)) := by
        apply mul_le_mul_of_nonneg_left hSbd
        positivity
    _ = 2 * Cη / Real.pi * (n : ℝ) ^ (-(1 + η)) := by
        rw [hrpow]
        have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
        have hπne : Real.pi ≠ 0 := ne_of_gt hπpos
        field_simp

/-- **Closed-interval summability of cosine coefficients.**  This is the
`DifferentiableOn (Icc 0 1)` replacement for `holderCosineCoeff_summable`. -/
theorem holderCosineCoeff_summable_diffOn (g : ℝ → ℝ)
    (hg : Continuous g) (hg' : DifferentiableOn ℝ g (Set.Icc (0:ℝ) 1))
    (hD_cont : Continuous (fun x => derivWithin g (Set.Icc (0:ℝ) 1) (clamp01 x)))
    (hNeumann : derivWithin g (Set.Icc (0:ℝ) 1) 0 = 0 ∧
      derivWithin g (Set.Icc (0:ℝ) 1) 1 = 0)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) {K : ℝ} (hK : 0 ≤ K)
    (hHolder : ∀ x y, x ∈ Set.Icc (0:ℝ) 1 → y ∈ Set.Icc (0:ℝ) 1 →
      |derivWithin g (Set.Icc (0:ℝ) 1) x -
        derivWithin g (Set.Icc (0:ℝ) 1) y| ≤ K * |x - y| ^ η) :
    Summable (fun n : ℕ => |cosineCoeffs g n|) := by
  obtain ⟨C, _hC0, hCbd⟩ :=
    holderCosineCoeff_decay_diffOn g hg hg' hD_cont hNeumann hη0 hη1 hK hHolder
  have hsummable_tail : Summable (fun n : ℕ => C * (n : ℝ) ^ (-(1 + η))) := by
    apply Summable.mul_left
    rw [Real.summable_nat_rpow]
    linarith
  apply Summable.of_norm_bounded_eventually_nat hsummable_tail
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  rw [Real.norm_eq_abs, abs_abs]
  exact hCbd n hn

end ShenWork.Wiener.EWA
