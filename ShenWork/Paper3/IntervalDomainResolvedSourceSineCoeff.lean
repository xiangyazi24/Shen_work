/- Normalized sine coefficient of a differentiated resolved cosine series. -/
import ShenWork.Paper3.IntervalDomainSolutionSignalDecomposition

namespace ShenWork.Paper3

open MeasureTheory Set Real
open ShenWork.PDE
open ShenWork.IntervalConjugateCosineSeries

noncomputable section

private lemma hasDerivAt_const_mul_id_p3 (a x : ℝ) :
    HasDerivAt (fun y : ℝ => a * y) a x := by
  simpa using (hasDerivAt_id x).const_mul a

lemma intervalIntegral_cos_int_mul_pi_eq_zero_p3
    {k : ℤ} (hk : k ≠ 0) :
    ∫ x in (0 : ℝ)..1, Real.cos ((k : ℝ) * Real.pi * x) = 0 := by
  have hk_real : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hfreq : (k : ℝ) * Real.pi ≠ 0 :=
    mul_ne_zero hk_real Real.pi_ne_zero
  let F : ℝ → ℝ := fun x =>
    Real.sin (((k : ℝ) * Real.pi) * x) / ((k : ℝ) * Real.pi)
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt F (Real.cos (((k : ℝ) * Real.pi) * x)) x := by
    intro x _hx
    have hsin :
        HasDerivAt
          (fun y : ℝ => Real.sin (((k : ℝ) * Real.pi) * y))
          (Real.cos (((k : ℝ) * Real.pi) * x) *
            ((k : ℝ) * Real.pi)) x :=
      (Real.hasDerivAt_sin (((k : ℝ) * Real.pi) * x)).comp x
        (hasDerivAt_const_mul_id_p3 ((k : ℝ) * Real.pi) x)
    convert hsin.div_const ((k : ℝ) * Real.pi) using 1
    field_simp [hfreq]
  have hint : IntervalIntegrable
      (fun x : ℝ => Real.cos (((k : ℝ) * Real.pi) * x))
      volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) hderiv hint
  have hsin : Real.sin ((k : ℝ) * Real.pi) = 0 := by simp
  simpa [F, hsin, mul_assoc] using hftc

/-- Positive-frequency normalized sine orthogonality. -/
lemma two_mul_intervalIntegral_sin_mul_sin_p3
    (n : ℕ) (hn : n ≠ 0) (k : ℕ) :
    2 * (∫ x in (0 : ℝ)..1,
      Real.sin ((n : ℝ) * Real.pi * x) *
        Real.sin ((k : ℝ) * Real.pi * x)) =
      if k = n then 1 else 0 := by
  have htrig : ∀ x : ℝ,
      2 * (Real.sin ((n : ℝ) * Real.pi * x) *
          Real.sin ((k : ℝ) * Real.pi * x)) =
        Real.cos ((((n : ℤ) - (k : ℤ) : ℤ) : ℝ) * Real.pi * x) -
          Real.cos ((((n : ℤ) + (k : ℤ) : ℤ) : ℝ) * Real.pi * x) := by
    intro x
    rw [show ((((n : ℤ) - (k : ℤ) : ℤ) : ℝ) * Real.pi * x) =
        (n : ℝ) * Real.pi * x - (k : ℝ) * Real.pi * x by
          push_cast; ring]
    rw [show ((((n : ℤ) + (k : ℤ) : ℤ) : ℝ) * Real.pi * x) =
        (n : ℝ) * Real.pi * x + (k : ℝ) * Real.pi * x by
          push_cast; ring]
    simpa [mul_assoc] using
      Real.two_mul_sin_mul_sin
        ((n : ℝ) * Real.pi * x) ((k : ℝ) * Real.pi * x)
  have hint1 : IntervalIntegrable
      (fun x : ℝ => Real.cos
        ((((n : ℤ) - (k : ℤ) : ℤ) : ℝ) * Real.pi * x)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hint2 : IntervalIntegrable
      (fun x : ℝ => Real.cos
        ((((n : ℤ) + (k : ℤ) : ℤ) : ℝ) * Real.pi * x)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hrewrite :
      2 * (∫ x in (0 : ℝ)..1,
        Real.sin ((n : ℝ) * Real.pi * x) *
          Real.sin ((k : ℝ) * Real.pi * x)) =
        (∫ x in (0 : ℝ)..1,
          Real.cos ((((n : ℤ) - (k : ℤ) : ℤ) : ℝ) * Real.pi * x)) -
        (∫ x in (0 : ℝ)..1,
          Real.cos ((((n : ℤ) + (k : ℤ) : ℤ) : ℝ) * Real.pi * x)) := by
    rw [← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_sub hint1 hint2]
    exact intervalIntegral.integral_congr (fun x _ => htrig x)
  rw [hrewrite]
  by_cases hkn : k = n
  · subst k
    simp only [sub_self, Int.cast_zero, zero_mul, Real.cos_zero]
    rw [intervalIntegral.integral_const]
    have hsum : (n : ℤ) + (n : ℤ) ≠ 0 := by
      have hnpos : (0 : ℤ) < (n : ℤ) := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      omega
    rw [intervalIntegral_cos_int_mul_pi_eq_zero_p3 hsum]
    norm_num
  · rw [if_neg hkn]
    have hdiff : (n : ℤ) - (k : ℤ) ≠ 0 := by
      exact sub_ne_zero.mpr (by exact_mod_cast Ne.symm hkn)
    have hsum : (n : ℤ) + (k : ℤ) ≠ 0 := by
      have hnpos : (0 : ℤ) < (n : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      omega
    rw [intervalIntegral_cos_int_mul_pi_eq_zero_p3 hdiff,
      intervalIntegral_cos_int_mul_pi_eq_zero_p3 hsum]
    ring

private def paper3ResolvedSinePairingTerm
    (p : CM2Params) (a : ℕ → ℝ) (n k : ℕ) : C(ℝ, ℝ) where
  toFun := fun x =>
    Real.sin ((n : ℝ) * Real.pi * x) *
      (a k * intervalNeumannResolverGradWeight p k *
        (-Real.sin ((k : ℝ) * Real.pi * x)))
  continuous_toFun := by fun_prop

private lemma paper3ResolvedSinePairingTerm_norm_le
    (p : CM2Params) (a : ℕ → ℝ) (n k : ℕ) :
    ‖(paper3ResolvedSinePairingTerm p a n k).restrict
      (⟨Set.uIcc (0 : ℝ) 1, isCompact_uIcc⟩ :
        TopologicalSpace.Compacts ℝ)‖ ≤
      |a k| * intervalNeumannResolverGradWeight p k := by
  have hB : 0 ≤ |a k| * intervalNeumannResolverGradWeight p k :=
    mul_nonneg (abs_nonneg _) (intervalNeumannResolverGradWeight_nonneg p k)
  rw [ContinuousMap.norm_le _ hB]
  rintro ⟨x, hx⟩
  simp only [ContinuousMap.restrict_apply,
    paper3ResolvedSinePairingTerm, ContinuousMap.coe_mk, Real.norm_eq_abs]
  rw [abs_mul, abs_mul, abs_mul, abs_neg]
  have hn := Real.abs_sin_le_one ((n : ℝ) * Real.pi * x)
  have hk := Real.abs_sin_le_one ((k : ℝ) * Real.pi * x)
  have hw := intervalNeumannResolverGradWeight_nonneg p k
  calc
    |Real.sin ((n : ℝ) * Real.pi * x)| *
          (|a k| * |intervalNeumannResolverGradWeight p k| *
            |Real.sin ((k : ℝ) * Real.pi * x)|) ≤
        1 * (|a k| * intervalNeumannResolverGradWeight p k * 1) := by
          rw [abs_of_nonneg hw]
          gcongr
    _ = |a k| * intervalNeumannResolverGradWeight p k := by ring

/-- The normalized sine coefficient of the resolved gradient selects exactly
the corresponding diagonal derivative multiplier. -/
theorem intervalSineInner_paper3ResolvedSourceGradient
    (p : CM2Params) {a : ℕ → ℝ}
    (ha : Summable fun k => (a k) ^ 2)
    (n : ℕ) :
    intervalSineInner (paper3ResolvedSourceGradient p a) n =
      -a n * intervalNeumannResolverGradWeight p n := by
  by_cases hn : n = 0
  · subst n
    simp [intervalSineInner, intervalNeumannResolverGradWeight]
  · have hprod : Summable fun k : ℕ =>
        |a k| * intervalNeumannResolverGradWeight p k := by
      have hw := intervalNeumannResolverGradWeight_sq_summable p
      refine Summable.of_nonneg_of_le
        (fun k => mul_nonneg (abs_nonneg _)
          (intervalNeumannResolverGradWeight_nonneg p k)) ?_
        ((ha.add hw).mul_left (1 / 2 : ℝ))
      intro k
      nlinarith [sq_abs (a k),
        sq_nonneg (|a k| - intervalNeumannResolverGradWeight p k)]
    have hterms : Summable fun k : ℕ =>
        ‖(paper3ResolvedSinePairingTerm p a n k).restrict
          (⟨Set.uIcc (0 : ℝ) 1, isCompact_uIcc⟩ :
            TopologicalSpace.Compacts ℝ)‖ :=
      Summable.of_nonneg_of_le (fun k => norm_nonneg _)
        (fun k => paper3ResolvedSinePairingTerm_norm_le p a n k) hprod
    unfold intervalSineInner
    rw [if_neg hn]
    unfold paper3ResolvedSourceGradient
    have hswap := intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hterms
    have hpoint : (fun y : ℝ =>
        Real.sin ((n : ℝ) * Real.pi * y) *
          (∑' k : ℕ, a k * intervalNeumannResolverGradWeight p k *
            (-Real.sin ((k : ℝ) * Real.pi * y)))) =
        fun y : ℝ => ∑' k : ℕ,
          paper3ResolvedSinePairingTerm p a n k y := by
      funext y
      rw [← tsum_mul_left]
      refine tsum_congr (fun k => ?_)
      rfl
    rw [hpoint]
    rw [← hswap]
    rw [← tsum_mul_left]
    rw [tsum_eq_single n]
    · simp only [paper3ResolvedSinePairingTerm, ContinuousMap.coe_mk]
      rw [show (∫ x in (0 : ℝ)..1,
          Real.sin ((n : ℝ) * Real.pi * x) *
            (a n * intervalNeumannResolverGradWeight p n *
              -Real.sin ((n : ℝ) * Real.pi * x))) =
          -(a n * intervalNeumannResolverGradWeight p n) *
            (∫ x in (0 : ℝ)..1,
              Real.sin ((n : ℝ) * Real.pi * x) *
                Real.sin ((n : ℝ) * Real.pi * x)) by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro x _
        ring]
      have hself := two_mul_intervalIntegral_sin_mul_sin_p3 n hn n
      rw [if_pos rfl] at hself
      calc
        2 * (-(a n * intervalNeumannResolverGradWeight p n) *
            (∫ x in (0 : ℝ)..1,
              Real.sin ((n : ℝ) * Real.pi * x) *
                Real.sin ((n : ℝ) * Real.pi * x))) =
            -(a n * intervalNeumannResolverGradWeight p n) *
              (2 * (∫ x in (0 : ℝ)..1,
                Real.sin ((n : ℝ) * Real.pi * x) *
                  Real.sin ((n : ℝ) * Real.pi * x))) := by ring
        _ = -a n * intervalNeumannResolverGradWeight p n := by
          rw [hself]
          ring
    · intro k hkn
      simp only [paper3ResolvedSinePairingTerm, ContinuousMap.coe_mk]
      rw [show (∫ x in (0 : ℝ)..1,
          Real.sin ((n : ℝ) * Real.pi * x) *
            (a k * intervalNeumannResolverGradWeight p k *
              -Real.sin ((k : ℝ) * Real.pi * x))) =
          -(a k * intervalNeumannResolverGradWeight p k) *
            (∫ x in (0 : ℝ)..1,
              Real.sin ((n : ℝ) * Real.pi * x) *
                Real.sin ((k : ℝ) * Real.pi * x)) by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro x _
        ring]
      have hortho := two_mul_intervalIntegral_sin_mul_sin_p3 n hn k
      rw [if_neg hkn] at hortho
      have hzero : (∫ x in (0 : ℝ)..1,
          Real.sin ((n : ℝ) * Real.pi * x) *
            Real.sin ((k : ℝ) * Real.pi * x)) = 0 := by
        linarith
      rw [hzero]
      ring

#print axioms two_mul_intervalIntegral_sin_mul_sin_p3
#print axioms intervalSineInner_paper3ResolvedSourceGradient

end

end ShenWork.Paper3
