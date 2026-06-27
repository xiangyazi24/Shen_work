# Q1143 cron2 — resolver nonnegativity helper

Static GitHub connector inspection only. I did not run Lean locally.

Add this helper inside `namespace ShenWork.Paper2.ConjugateLevel0BFormSourceOn`.

```lean
theorem intervalNeumannResolverR_nonneg_of_continuous_nonneg
    (p : CM2Params) {w : intervalDomainPoint → ℝ}
    (hw_cont : Continuous w)
    (hw_nonneg : ∀ x : intervalDomainPoint, 0 ≤ w x) :
    ∀ y : intervalDomainPoint, 0 ≤ intervalNeumannResolverR p w y := by
  intro yp
  have hcont_on : ContinuousOn (intervalDomainLift w) (Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    have heq : (Icc (0 : ℝ) 1).restrict (intervalDomainLift w) = w := by
      funext ⟨z, hz⟩
      simp only [Set.restrict_apply, intervalDomainLift]
      split_ifs
      exact congr_arg w (Subtype.ext rfl)
    rw [heq]
    exact hw_cont

  set clip : ℝ → intervalDomainPoint := fun z =>
    ⟨max 0 (min z 1), le_max_left 0 _,
      max_le (by norm_num) (min_le_right z 1)⟩

  have hclip_cont : Continuous clip :=
    Continuous.subtype_mk
      (continuous_const.max (continuous_id.min continuous_const)) _

  have hcont_src : Continuous
      (fun z : intervalDomainPoint => p.ν * (w z) ^ p.γ) :=
    continuous_const.mul (hw_cont.rpow_const (fun _ => Or.inr p.hγ.le))

  set f : ℝ → ℝ :=
    (fun z : intervalDomainPoint => p.ν * (w z) ^ p.γ) ∘ clip

  have hf_cont : Continuous f := hcont_src.comp hclip_cont

  have hf_nonneg : ∀ z : ℝ, 0 ≤ f z := fun z =>
    mul_nonneg p.hν.le (Real.rpow_nonneg (hw_nonneg (clip z)) _)

  have hf_coeff : ∀ k : ℕ, cosineCoeffs f k =
      (ShenWork.PDE.intervalNeumannResolverSourceCoeff p w k).re := by
    intro k
    have hsrc_eq :
        (ShenWork.PDE.intervalNeumannResolverSourceCoeff p w k).re =
          cosineCoeffs (fun z : ℝ => p.ν * intervalDomainLift w z ^ p.γ) k := by
      simp [cosineCoeffs, ShenWork.PDE.intervalNeumannResolverSourceCoeff,
        Complex.ofReal_re]
    rw [hsrc_eq]
    exact ShenWork.Paper2.cosineCoeffs_congr_on_Icc (fun z hz => by
      simp only [f, Function.comp, clip]
      have hclip_eq : max 0 (min z 1) = z := by
        rw [min_eq_left hz.2, max_eq_right hz.1]
      simp only [hclip_eq, intervalDomainLift,
        dif_pos (Set.mem_Icc.mpr hz)]) k

  have hsrc_l2 : Summable (fun k : ℕ => (cosineCoeffs f k) ^ 2) := by
    open ShenWork.IntervalResolverWeakBounds ShenWork.Paper2
      ShenWork.IntervalResolverPositivity in
    have h := resolverSourceCoeff_re_sq_summable_of_continuousOn p hcont_on
    simp only [intervalNeumannResolverSourceCoeff_zero, sub_zero] at h
    exact h.congr (fun k => by rw [hf_coeff])

  open ShenWork.IntervalResolverPositivity in
  exact intervalNeumannResolverR_nonneg_of_nonneg_source
    hf_cont hf_nonneg hf_coeff hsrc_l2 yp
```

Wrappers:

```lean
theorem intervalNeumannResolverR_nonneg_on_Icc_of_continuous_nonneg
    (p : CM2Params) {w : intervalDomainPoint → ℝ}
    (hw_cont : Continuous w)
    (hw_nonneg : ∀ x : intervalDomainPoint, 0 ≤ w x) :
    ∀ x : ℝ, ∀ hx : x ∈ Icc (0 : ℝ) 1,
      0 ≤ intervalNeumannResolverR p w ⟨x, hx⟩ := by
  intro x hx
  exact intervalNeumannResolverR_nonneg_of_continuous_nonneg
    p hw_cont hw_nonneg ⟨x, hx⟩

theorem intervalResolverLiftR_eq_intervalNeumannResolverR_on_Icc
    (p : CM2Params) (w : intervalDomainPoint → ℝ)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    intervalResolverLiftR p w x = intervalNeumannResolverR p w ⟨x, hx⟩ := by
  unfold intervalResolverLiftR intervalNeumannResolverR
  exact tsum_congr (fun k => by
    rw [unitIntervalCosineMode_eq_cosineMode])

theorem intervalResolverLiftR_nonneg_on_Icc_of_continuous_nonneg
    (p : CM2Params) {w : intervalDomainPoint → ℝ}
    (hw_cont : Continuous w)
    (hw_nonneg : ∀ x : intervalDomainPoint, 0 ≤ w x) :
    ∀ x : ℝ, ∀ hx : x ∈ Icc (0 : ℝ) 1,
      0 ≤ intervalResolverLiftR p w x := by
  intro x hx
  rw [intervalResolverLiftR_eq_intervalNeumannResolverR_on_Icc p w hx]
  exact intervalNeumannResolverR_nonneg_on_Icc_of_continuous_nonneg
    p hw_cont hw_nonneg x hx
```

At the old duplicate site, replace the long local `hR_nonneg` proof with:

```lean
have hR_nonneg : ∀ yp : intervalDomainPoint,
    0 ≤ intervalNeumannResolverR p w yp :=
  intervalNeumannResolverR_nonneg_of_continuous_nonneg p hw_cont hw_nonneg
```

At line about 1103, after `intro x hx`, use:

```lean
set w := conjugatePicardIter p u₀ 0 r with hw_def

have hcont_on : ContinuousOn (intervalDomainLift w) (Icc (0 : ℝ) 1) :=
  hU_C4.continuous.continuousOn.congr (fun y hy => by
    simpa [w, hw_def] using hU_agree y hy)

have hw_cont : Continuous w := by
  have hrestr : Set.restrict (Icc (0 : ℝ) 1) (intervalDomainLift w) = w := by
    funext ⟨z, hz⟩
    show intervalDomainLift w z = w ⟨z, hz⟩
    rw [intervalDomainLift, dif_pos hz]
  rw [← hrestr]
  exact continuousOn_iff_continuous_restrict.mp hcont_on

have hw_nonneg : ∀ z : intervalDomainPoint, 0 ≤ w z := by
  intro z
  simp only [w, hw_def, conjugatePicardIter]
  apply ShenWork.IntervalResolverPositivity.intervalFullSemigroupOperator_nonneg hr_pos'
  intro y
  unfold intervalDomainLift
  split_ifs with hy
  · exact _hu₀_nonneg ⟨y, hy⟩
  · norm_num

exact intervalResolverLiftR_nonneg_on_Icc_of_continuous_nonneg
  p hw_cont hw_nonneg x hx
```
