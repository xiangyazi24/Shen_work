import ShenWork.Paper2.IntervalBFormSquareHeatSubsolutionRegular
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open Set Filter Topology
open scoped Topology

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceData conjugatePicardLimit)
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

namespace NeumannLinearDriftComparisonRegularDischarge

open ShenWork.PDE.ParabolicMaxPrinciple

def intervalBump (x : ℝ) : ℝ := x * (1 - x)

def driftExpDiff (lam : ℝ) (w u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun t x => Real.exp (-(lam * t)) * (w t x - u t x)

def driftComparisonPerturb
    (lam ε : ℝ) (w u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun t x => driftExpDiff lam w u t x + ε * intervalBump x - 2 * ε

lemma intervalBump_nonneg {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ intervalBump x := by
  unfold intervalBump
  nlinarith [hx.1, hx.2]

lemma intervalBump_le_one {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    intervalBump x ≤ 1 := by
  unfold intervalBump
  nlinarith [hx.1, hx.2]

lemma intervalBump_hasDerivAt (x : ℝ) :
    HasDerivAt intervalBump (1 - 2 * x) x := by
  unfold intervalBump
  have h1 : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have h2 : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    simpa using (hasDerivAt_const (x := x) (c := (1 : ℝ))).sub (hasDerivAt_id x)
  convert h1.mul h2 using 1 <;> ring

lemma intervalBump_deriv (x : ℝ) :
    deriv intervalBump x = 1 - 2 * x :=
  (intervalBump_hasDerivAt x).deriv

lemma intervalBump_second_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => deriv intervalBump y) (-2) x := by
  have hfun : (fun y : ℝ => deriv intervalBump y) = fun y : ℝ => 1 - 2 * y := by
    funext y
    exact intervalBump_deriv y
  rw [hfun]
  have h : HasDerivAt (fun y : ℝ => 1 - 2 * y) (0 - 2 * 1) x := by
    exact (hasDerivAt_const (x := x) (c := (1 : ℝ))).sub
      ((hasDerivAt_id x).const_mul (2 : ℝ))
  convert h using 1 <;> ring

lemma intervalBump_second_deriv (x : ℝ) :
    deriv (fun y : ℝ => deriv intervalBump y) x = -2 :=
  (intervalBump_second_hasDerivAt x).deriv

private lemma exists_max_on_unit_strip
    {T : ℝ} (hT : 0 ≤ T)
    {F : ℝ × ℝ → ℝ}
    (hF :
      ContinuousOn F
        (Set.Icc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)) :
    ∃ p : ℝ × ℝ,
      p ∈ Set.Icc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1 ∧
      ∀ q ∈ Set.Icc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1,
        F q ≤ F p := by
  have hK : IsCompact (Set.Icc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  have hne : (Set.Icc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1).Nonempty := by
    refine ⟨(0, 0), ?_⟩
    exact ⟨⟨le_rfl, hT⟩, ⟨le_rfl, zero_le_one⟩⟩
  obtain ⟨p, hp, hmax⟩ := hK.exists_isMaxOn hne hF
  exact ⟨p, hp, fun q hq => hmax hq⟩

private lemma time_deriv_nonneg_at_Icc_max
    {ψ : ℝ → ℝ → ℝ} {T t₀ x₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Icc (0 : ℝ) T)
    (htpos : 0 < t₀)
    (hdt : HasDerivAt (fun τ : ℝ => ψ τ x₀) (dt ψ t₀ x₀) t₀)
    (hmax : ∀ t ∈ Set.Icc (0 : ℝ) T, ψ t x₀ ≤ ψ t₀ x₀) :
    0 ≤ dt ψ t₀ x₀ := by
  let f : ℝ → ℝ := fun τ => ψ τ x₀
  have hmaxOn : IsMaxOn f (Set.Icc (0 : ℝ) T) t₀ := by
    intro y hy
    exact hmax y hy
  have hT : 0 ≤ T := le_trans htpos.le ht₀.2
  have hseg : segment ℝ t₀ 0 ⊆ Set.Icc (0 : ℝ) T := by
    exact (convex_Icc (0 : ℝ) T).segment_subset ht₀ (left_mem_Icc.mpr hT)
  have htan : (0 : ℝ) - t₀ ∈ posTangentConeAt (Set.Icc (0 : ℝ) T) t₀ :=
    sub_mem_posTangentConeAt_of_segment_subset hseg
  have hfderiv :
      HasFDerivWithinAt f (ContinuousLinearMap.toSpanSingleton ℝ (dt ψ t₀ x₀))
        (Set.Icc (0 : ℝ) T) t₀ := by
    exact hdt.hasFDerivAt.hasFDerivWithinAt
  have hle :
      (ContinuousLinearMap.toSpanSingleton ℝ (dt ψ t₀ x₀)) ((0 : ℝ) - t₀) ≤ 0 :=
    hmaxOn.localize.hasFDerivWithinAt_nonpos hfderiv htan
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at hle
  nlinarith

private lemma space_deriv_eq_zero_at_Icc_interior_max
    {ψ : ℝ → ℝ → ℝ} {t₀ x₀ : ℝ}
    (hx₀ : x₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hdx : HasDerivAt (fun y : ℝ => ψ t₀ y) (dx ψ t₀ x₀) x₀)
    (hmax : ∀ x ∈ Set.Icc (0 : ℝ) 1, ψ t₀ x ≤ ψ t₀ x₀) :
    dx ψ t₀ x₀ = 0 := by
  let f : ℝ → ℝ := fun y => ψ t₀ y
  have hmaxOn : IsMaxOn f (Set.Icc (0 : ℝ) 1) x₀ := by
    intro y hy
    exact hmax y hy
  have hnhds : Set.Icc (0 : ℝ) 1 ∈ 𝓝 x₀ := by
    rw [← mem_interior_iff_mem_nhds, interior_Icc]
    exact hx₀
  exact (hmaxOn.isLocalMax hnhds).hasDerivAt_eq_zero hdx

private lemma second_space_deriv_nonpos_at_Icc_interior_max
    {ψ : ℝ → ℝ → ℝ} {t₀ x₀ : ℝ}
    (hx₀ : x₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hdx : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun r : ℝ => ψ t₀ r) (dx ψ t₀ y) y)
    (hdxx : HasDerivAt (fun y : ℝ => dx ψ t₀ y) (dxx ψ t₀ x₀) x₀)
    (hmax : ∀ x ∈ Set.Icc (0 : ℝ) 1, ψ t₀ x ≤ ψ t₀ x₀) :
    dxx ψ t₀ x₀ ≤ 0 := by
  by_contra hnot
  push_neg at hnot
  let f : ℝ → ℝ := fun y => ψ t₀ y
  let g : ℝ → ℝ := fun y => dx ψ t₀ y
  have hgx₀ : g x₀ = 0 := by
    exact space_deriv_eq_zero_at_Icc_interior_max hx₀
      (hdx x₀ (Set.Ioo_subset_Icc_self hx₀)) hmax
  have hhalf_pos : 0 < dxx ψ t₀ x₀ / 2 := by linarith
  have hslope_tendsto :
      Filter.Tendsto (slope g x₀) (𝓝[>] x₀) (𝓝 (dxx ψ t₀ x₀)) := by
    simpa [g] using hdxx.tendsto_slope.mono_left (nhdsGT_le_nhdsNE x₀)
  have hpos_near : {y : ℝ | 0 < g y} ∈ 𝓝[>] x₀ := by
    have hhalf_lt : dxx ψ t₀ x₀ / 2 < dxx ψ t₀ x₀ := by
      nlinarith
    have hslope_event :
        {y : ℝ | dxx ψ t₀ x₀ / 2 < slope g x₀ y} ∈ 𝓝[>] x₀ :=
      hslope_tendsto (isOpen_Ioi.mem_nhds hhalf_lt)
    filter_upwards [hslope_event, self_mem_nhdsWithin] with y hslope hygt
    have hden : 0 < y - x₀ := sub_pos.mpr hygt
    have hslope_pos : 0 < slope g x₀ y := lt_trans hhalf_pos hslope
    rw [slope_def_field] at hslope_pos
    have hnum : 0 < g y - g x₀ := by
      rcases (div_pos_iff.mp hslope_pos) with h | h
      · exact h.1
      · linarith
    linarith
  obtain ⟨b₁, hx₀b₁, hb₁_sub⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.mp hpos_near
  let b₀ : ℝ := (x₀ + 1) / 2
  have hx₀b₀ : x₀ < b₀ := by
    dsimp [b₀]
    linarith [hx₀.2]
  have hb₀1 : b₀ < 1 := by
    dsimp [b₀]
    linarith [hx₀.2]
  let b : ℝ := min b₁ b₀
  have hx₀b : x₀ < b := lt_min hx₀b₁ hx₀b₀
  have hb1 : b < 1 := lt_of_le_of_lt (min_le_right b₁ b₀) hb₀1
  have hb_le_b₁ : b ≤ b₁ := min_le_left b₁ b₀
  have hf_cont : ContinuousOn f (Set.Icc x₀ b) := by
    intro y hy
    have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨le_trans (le_of_lt hx₀.1) hy.1, le_trans hy.2 (le_of_lt hb1)⟩
    exact (hdx y hyIcc).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn f (Set.Icc x₀ b) := by
    refine strictMonoOn_of_hasDerivWithinAt_pos (f' := g)
      (convex_Icc x₀ b) hf_cont ?_ ?_
    · intro y hy
      have hyIoo : y ∈ Set.Ioo x₀ b := by
        simpa [interior_Icc, hx₀b] using hy
      have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := by
        exact ⟨le_trans (le_of_lt hx₀.1) (le_of_lt hyIoo.1),
          le_trans (le_of_lt hyIoo.2) (le_of_lt hb1)⟩
      exact (hdx y hyIcc).hasDerivWithinAt
    · intro y hy
      have hyIoo : y ∈ Set.Ioo x₀ b := by
        simpa [interior_Icc, hx₀b] using hy
      exact hb₁_sub ⟨hyIoo.1, lt_of_lt_of_le hyIoo.2 hb_le_b₁⟩
  have hb_full : b ∈ Set.Icc (0 : ℝ) 1 := by
    exact ⟨le_trans (le_of_lt hx₀.1) (le_of_lt hx₀b), le_of_lt hb1⟩
  have hlt : f x₀ < f b :=
    hmono (left_mem_Icc.mpr hx₀b.le) (right_mem_Icc.mpr hx₀b.le) hx₀b
  have hle : f b ≤ f x₀ := hmax b hb_full
  linarith

private lemma left_endpoint_not_max_of_pos_deriv
    {f : ℝ → ℝ} {d : ℝ}
    (hder : HasDerivAt f d 0)
    (hdpos : 0 < d)
    (hmax : ∀ x ∈ Set.Icc (0 : ℝ) 1, f x ≤ f 0) :
    False := by
  have hmaxOn : IsMaxOn f (Set.Icc (0 : ℝ) 1) 0 := by
    intro y hy
    exact hmax y hy
  have htan : (1 : ℝ) - 0 ∈ posTangentConeAt (Set.Icc (0 : ℝ) 1) (0 : ℝ) := by
    have hseg : segment ℝ (0 : ℝ) 1 ⊆ Set.Icc (0 : ℝ) 1 := by
      exact (convex_Icc (0 : ℝ) 1).segment_subset
        (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one)
    exact sub_mem_posTangentConeAt_of_segment_subset hseg
  have hfderiv :
      HasFDerivWithinAt f (ContinuousLinearMap.toSpanSingleton ℝ d)
        (Set.Icc (0 : ℝ) 1) 0 :=
    hder.hasFDerivAt.hasFDerivWithinAt
  have hle :
      (ContinuousLinearMap.toSpanSingleton ℝ d) ((1 : ℝ) - 0) ≤ 0 :=
    hmaxOn.localize.hasFDerivWithinAt_nonpos hfderiv htan
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, sub_zero,
    mul_one] at hle
  linarith

private lemma right_endpoint_not_max_of_neg_deriv
    {f : ℝ → ℝ} {d : ℝ}
    (hder : HasDerivAt f d 1)
    (hdneg : d < 0)
    (hmax : ∀ x ∈ Set.Icc (0 : ℝ) 1, f x ≤ f 1) :
    False := by
  have hmaxOn : IsMaxOn f (Set.Icc (0 : ℝ) 1) 1 := by
    intro y hy
    exact hmax y hy
  have htan : (0 : ℝ) - 1 ∈ posTangentConeAt (Set.Icc (0 : ℝ) 1) (1 : ℝ) := by
    have hseg : segment ℝ (1 : ℝ) 0 ⊆ Set.Icc (0 : ℝ) 1 := by
      exact (convex_Icc (0 : ℝ) 1).segment_subset
        (right_mem_Icc.mpr zero_le_one) (left_mem_Icc.mpr zero_le_one)
    exact sub_mem_posTangentConeAt_of_segment_subset hseg
  have hfderiv :
      HasFDerivWithinAt f (ContinuousLinearMap.toSpanSingleton ℝ d)
        (Set.Icc (0 : ℝ) 1) 1 :=
    hder.hasFDerivAt.hasFDerivWithinAt
  have hle :
      (ContinuousLinearMap.toSpanSingleton ℝ d) ((0 : ℝ) - 1) ≤ 0 :=
    hmaxOn.localize.hasFDerivWithinAt_nonpos hfderiv htan
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at hle
  norm_num at hle
  linarith

private lemma Icc_mem_nhds_of_Ioo01 {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    Set.Icc (0 : ℝ) 1 ∈ 𝓝 x := by
  rw [← mem_interior_iff_mem_nhds, interior_Icc]
  exact hx

private lemma residual_eq_dt_dx_dxx
    (B C v : ℝ → ℝ → ℝ) (t x : ℝ) :
    neumannLinearDriftResidual B C v t x =
      dt v t x - dxx v t x - B t x * dx v t x - C t x * v t x := by
  rfl

private lemma dt_sub_eq
    {w u : ℝ → ℝ → ℝ} {t x : ℝ}
    (hw : HasDerivAt (fun τ : ℝ => w τ x) (dt w t x) t)
    (hu : HasDerivAt (fun τ : ℝ => u τ x) (dt u t x) t) :
    dt (fun τ y => w τ y - u τ y) t x = dt w t x - dt u t x := by
  unfold dt
  exact (hw.sub hu).deriv

private lemma dx_sub_eq
    {w u : ℝ → ℝ → ℝ} {t x : ℝ}
    (hw : HasDerivAt (fun y : ℝ => w t y) (dx w t x) x)
    (hu : HasDerivAt (fun y : ℝ => u t y) (dx u t x) x) :
    dx (fun τ y => w τ y - u τ y) t x = dx w t x - dx u t x := by
  unfold dx
  exact (hw.sub hu).deriv

private lemma dxx_sub_eq_of_interior
    {T : ℝ} {B C w u : ℝ → ℝ → ℝ} {t x : ℝ}
    (ht0 : 0 < t) (htT : t < T) (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hw :
      IsClassicalNeumannLinearDriftSubSolution T B C w)
    (hu :
      IsClassicalNeumannLinearDriftSuperSolution T B C u) :
    dxx (fun τ y => w τ y - u τ y) t x = dxx w t x - dxx u t x := by
  have hder :
      HasDerivAt (fun y : ℝ => dx w t y - dx u t y)
        (dxx w t x - dxx u t x) x :=
    (hw.space_second_hasDerivAt ht0 htT hx).sub
      (hu.space_second_hasDerivAt ht0 htT hx)
  have hEq :
      (fun y : ℝ => dx (fun τ z => w τ z - u τ z) t y)
        =ᶠ[𝓝 x]
      (fun y : ℝ => dx w t y - dx u t y) := by
    refine Filter.eventuallyEq_of_mem (Icc_mem_nhds_of_Ioo01 hx) ?_
    intro y hy
    exact dx_sub_eq
      (hw.space_hasDerivAt ht0 htT hy)
      (hu.space_hasDerivAt ht0 htT hy)
  exact (hder.congr_of_eventuallyEq hEq).deriv

private lemma residual_sub_eq_of_interior
    {T : ℝ} {B C w u : ℝ → ℝ → ℝ} {t x : ℝ}
    (ht0 : 0 < t) (htT : t < T) (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hw :
      IsClassicalNeumannLinearDriftSubSolution T B C w)
    (hu :
      IsClassicalNeumannLinearDriftSuperSolution T B C u) :
    neumannLinearDriftResidual B C (fun τ y => w τ y - u τ y) t x =
      neumannLinearDriftResidual B C w t x -
        neumannLinearDriftResidual B C u t x := by
  have hdt := dt_sub_eq
    (hw.time_hasDerivAt ht0 htT (Set.Ioo_subset_Icc_self hx))
    (hu.time_hasDerivAt ht0 htT (Set.Ioo_subset_Icc_self hx))
  have hdx := dx_sub_eq
    (hw.space_hasDerivAt ht0 htT (Set.Ioo_subset_Icc_self hx))
    (hu.space_hasDerivAt ht0 htT (Set.Ioo_subset_Icc_self hx))
  have hdxx := dxx_sub_eq_of_interior
    (T := T) (B := B) (C := C) (w := w) (u := u)
    ht0 htT hx hw hu
  simp [residual_eq_dt_dx_dxx, hdt, hdx, hdxx]
  ring

private lemma residual_sub_nonpos_of_interior
    {T : ℝ} {B C w u : ℝ → ℝ → ℝ} {t x : ℝ}
    (ht0 : 0 < t) (htT : t < T) (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hw :
      IsClassicalNeumannLinearDriftSubSolution T B C w)
    (hu :
      IsClassicalNeumannLinearDriftSuperSolution T B C u) :
    neumannLinearDriftResidual B C (fun τ y => w τ y - u τ y) t x ≤ 0 := by
  rw [residual_sub_eq_of_interior ht0 htT hx hw hu]
  linarith [hw.pde_le ht0 htT hx, hu.pde_ge ht0 htT hx]

private lemma dt_driftExpDiff_eq
    {lam : ℝ} {w u : ℝ → ℝ → ℝ} {t x : ℝ}
    (hw : HasDerivAt (fun τ : ℝ => w τ x) (dt w t x) t)
    (hu : HasDerivAt (fun τ : ℝ => u τ x) (dt u t x) t) :
    dt (driftExpDiff lam w u) t x =
      Real.exp (-(lam * t)) *
        (dt w t x - dt u t x - lam * (w t x - u t x)) := by
  have hExp :
      HasDerivAt (fun τ : ℝ => Real.exp (-(lam * τ)))
        (Real.exp (-(lam * t)) * (-lam)) t := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id t).const_mul lam).neg.exp)
  have hdiff : HasDerivAt (fun τ : ℝ => w τ x - u τ x)
      (dt w t x - dt u t x) t := hw.sub hu
  have h := (hExp.mul hdiff).deriv
  unfold dt driftExpDiff
  convert h using 1 <;> simp [dt] <;> ring

private lemma dx_driftExpDiff_eq
    {lam : ℝ} {w u : ℝ → ℝ → ℝ} {t x : ℝ}
    (hw : HasDerivAt (fun y : ℝ => w t y) (dx w t x) x)
    (hu : HasDerivAt (fun y : ℝ => u t y) (dx u t x) x) :
    dx (driftExpDiff lam w u) t x =
      Real.exp (-(lam * t)) * (dx w t x - dx u t x) := by
  have hdiff : HasDerivAt (fun y : ℝ => w t y - u t y)
      (dx w t x - dx u t x) x := hw.sub hu
  have hder :
      HasDerivAt (fun y : ℝ => Real.exp (-(lam * t)) * (w t y - u t y))
        (Real.exp (-(lam * t)) * (dx w t x - dx u t x)) x := by
    simpa [Pi.mul_apply, mul_comm, mul_left_comm, mul_assoc] using
      (hasDerivAt_const x (Real.exp (-(lam * t)))).mul hdiff
  unfold dx driftExpDiff
  exact hder.deriv

private lemma dxx_driftExpDiff_eq_of_interior
    {T lam : ℝ} {B C w u : ℝ → ℝ → ℝ} {t x : ℝ}
    (ht0 : 0 < t) (htT : t < T) (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hw :
      IsClassicalNeumannLinearDriftSubSolution T B C w)
    (hu :
      IsClassicalNeumannLinearDriftSuperSolution T B C u) :
    dxx (driftExpDiff lam w u) t x =
      Real.exp (-(lam * t)) * (dxx w t x - dxx u t x) := by
  have hder :
      HasDerivAt
        (fun y : ℝ => Real.exp (-(lam * t)) * (dx w t y - dx u t y))
        (Real.exp (-(lam * t)) * (dxx w t x - dxx u t x)) x := by
    simpa [Pi.mul_apply, mul_comm, mul_left_comm, mul_assoc] using
      (hasDerivAt_const x (Real.exp (-(lam * t)))).mul
        ((hw.space_second_hasDerivAt ht0 htT hx).sub
          (hu.space_second_hasDerivAt ht0 htT hx))
  have hEq :
      (fun y : ℝ => dx (driftExpDiff lam w u) t y)
        =ᶠ[𝓝 x]
      (fun y : ℝ => Real.exp (-(lam * t)) * (dx w t y - dx u t y)) := by
    refine Filter.eventuallyEq_of_mem (Icc_mem_nhds_of_Ioo01 hx) ?_
    intro y hy
    exact dx_driftExpDiff_eq
      (hw.space_hasDerivAt ht0 htT hy)
      (hu.space_hasDerivAt ht0 htT hy)
  exact (hder.congr_of_eventuallyEq hEq).deriv

private lemma residual_driftExpDiff_shift_nonpos_of_interior
    {T lam : ℝ} {B C w u : ℝ → ℝ → ℝ} {t x : ℝ}
    (ht0 : 0 < t) (htT : t < T) (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hw :
      IsClassicalNeumannLinearDriftSubSolution T B C w)
    (hu :
      IsClassicalNeumannLinearDriftSuperSolution T B C u) :
    neumannLinearDriftResidual B (fun τ y => C τ y - lam)
        (driftExpDiff lam w u) t x ≤ 0 := by
  have hdt := dt_driftExpDiff_eq (lam := lam)
    (hw.time_hasDerivAt ht0 htT (Set.Ioo_subset_Icc_self hx))
    (hu.time_hasDerivAt ht0 htT (Set.Ioo_subset_Icc_self hx))
  have hdx := dx_driftExpDiff_eq (lam := lam)
    (hw.space_hasDerivAt ht0 htT (Set.Ioo_subset_Icc_self hx))
    (hu.space_hasDerivAt ht0 htT (Set.Ioo_subset_Icc_self hx))
  have hdxx := dxx_driftExpDiff_eq_of_interior
    (T := T) (lam := lam) (B := B) (C := C) (w := w) (u := u)
    ht0 htT hx hw hu
  have hres_sub :=
    residual_sub_nonpos_of_interior
      (T := T) (B := B) (C := C) (w := w) (u := u)
      ht0 htT hx hw hu
  have hEpos : 0 < Real.exp (-(lam * t)) := Real.exp_pos _
  have hres_eq :
      neumannLinearDriftResidual B (fun τ y => C τ y - lam)
          (driftExpDiff lam w u) t x =
        Real.exp (-(lam * t)) *
          neumannLinearDriftResidual B C (fun τ y => w τ y - u τ y) t x := by
    have hdt_sub := dt_sub_eq
      (hw.time_hasDerivAt ht0 htT (Set.Ioo_subset_Icc_self hx))
      (hu.time_hasDerivAt ht0 htT (Set.Ioo_subset_Icc_self hx))
    have hdx_sub := dx_sub_eq
      (hw.space_hasDerivAt ht0 htT (Set.Ioo_subset_Icc_self hx))
      (hu.space_hasDerivAt ht0 htT (Set.Ioo_subset_Icc_self hx))
    have hdxx_sub := dxx_sub_eq_of_interior
      (T := T) (B := B) (C := C) (w := w) (u := u)
      ht0 htT hx hw hu
    simp [residual_eq_dt_dx_dxx, hdt, hdx, hdxx, hdt_sub, hdx_sub, hdxx_sub,
      driftExpDiff]
    ring
  rw [hres_eq]
  exact mul_nonpos_of_nonneg_of_nonpos hEpos.le hres_sub

private lemma dt_perturb_eq
    {lam ε : ℝ} {w u : ℝ → ℝ → ℝ} {t x : ℝ}
    (hw : HasDerivAt (fun τ : ℝ => w τ x) (dt w t x) t)
    (hu : HasDerivAt (fun τ : ℝ => u τ x) (dt u t x) t) :
    dt (driftComparisonPerturb lam ε w u) t x =
      dt (driftExpDiff lam w u) t x := by
  have hz :
      HasDerivAt (fun τ : ℝ => driftExpDiff lam w u τ x)
        (dt (driftExpDiff lam w u) t x) t := by
    have hExp :
        HasDerivAt (fun τ : ℝ => Real.exp (-(lam * τ)))
          (Real.exp (-(lam * t)) * (-lam)) t := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (((hasDerivAt_id t).const_mul lam).neg.exp)
    have hdiff : HasDerivAt (fun τ : ℝ => w τ x - u τ x)
        (dt w t x - dt u t x) t := hw.sub hu
    have hprod :
        HasDerivAt (fun τ : ℝ => driftExpDiff lam w u τ x)
          (Real.exp (-(lam * t)) *
            (dt w t x - dt u t x - lam * (w t x - u t x))) t := by
      convert hExp.mul hdiff using 1 <;> ring
    have hdt := dt_driftExpDiff_eq (lam := lam) hw hu
    rwa [hdt]
  have hψ :
      HasDerivAt
        (fun τ : ℝ => driftExpDiff lam w u τ x + ε * intervalBump x - 2 * ε)
        (dt (driftExpDiff lam w u) t x) t := by
    simpa using (hz.add_const (ε * intervalBump x - 2 * ε))
  unfold dt driftComparisonPerturb
  exact hψ.deriv

private lemma dx_perturb_eq
    {lam ε : ℝ} {w u : ℝ → ℝ → ℝ} {t x : ℝ}
    (hw : HasDerivAt (fun y : ℝ => w t y) (dx w t x) x)
    (hu : HasDerivAt (fun y : ℝ => u t y) (dx u t x) x) :
    dx (driftComparisonPerturb lam ε w u) t x =
      dx (driftExpDiff lam w u) t x + ε * (1 - 2 * x) := by
  have hz :
      HasDerivAt (fun y : ℝ => driftExpDiff lam w u t y)
        (dx (driftExpDiff lam w u) t x) x := by
    have hdiff : HasDerivAt (fun y : ℝ => w t y - u t y)
        (dx w t x - dx u t x) x := hw.sub hu
    have hprod :
        HasDerivAt (fun y : ℝ => driftExpDiff lam w u t y)
          (Real.exp (-(lam * t)) * (dx w t x - dx u t x)) x := by
      simpa [driftExpDiff, Pi.mul_apply, mul_comm, mul_left_comm, mul_assoc] using
        (hasDerivAt_const x (Real.exp (-(lam * t)))).mul hdiff
    have hdx := dx_driftExpDiff_eq (lam := lam) hw hu
    rwa [hdx]
  have hb :
      HasDerivAt (fun y : ℝ => ε * intervalBump y) (ε * (1 - 2 * x)) x :=
    (intervalBump_hasDerivAt x).const_mul ε
  have hsum := (hz.add hb).sub_const (2 * ε)
  have hψ :
      HasDerivAt
        (fun y : ℝ => driftExpDiff lam w u t y + ε * intervalBump y - 2 * ε)
        (dx (driftExpDiff lam w u) t x + ε * (1 - 2 * x)) x := by
    convert hsum using 1
  unfold dx driftComparisonPerturb
  exact hψ.deriv

private lemma dxx_perturb_eq_of_interior
    {T lam ε : ℝ} {B C w u : ℝ → ℝ → ℝ} {t x : ℝ}
    (ht0 : 0 < t) (htT : t < T) (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hw :
      IsClassicalNeumannLinearDriftSubSolution T B C w)
    (hu :
      IsClassicalNeumannLinearDriftSuperSolution T B C u) :
    dxx (driftComparisonPerturb lam ε w u) t x =
      dxx (driftExpDiff lam w u) t x - 2 * ε := by
  have hz :
      HasDerivAt
        (fun y : ℝ => dx (driftExpDiff lam w u) t y)
        (dxx (driftExpDiff lam w u) t x) x := by
    have hder :
        HasDerivAt
          (fun y : ℝ => Real.exp (-(lam * t)) * (dx w t y - dx u t y))
          (Real.exp (-(lam * t)) * (dxx w t x - dxx u t x)) x := by
      simpa [Pi.mul_apply, mul_comm, mul_left_comm, mul_assoc] using
        (hasDerivAt_const x (Real.exp (-(lam * t)))).mul
          ((hw.space_second_hasDerivAt ht0 htT hx).sub
            (hu.space_second_hasDerivAt ht0 htT hx))
    have hEq :
        (fun y : ℝ => dx (driftExpDiff lam w u) t y)
          =ᶠ[𝓝 x]
        (fun y : ℝ => Real.exp (-(lam * t)) * (dx w t y - dx u t y)) := by
      refine Filter.eventuallyEq_of_mem (Icc_mem_nhds_of_Ioo01 hx) ?_
      intro y hy
      exact dx_driftExpDiff_eq
        (hw.space_hasDerivAt ht0 htT hy)
        (hu.space_hasDerivAt ht0 htT hy)
    have hdxx := dxx_driftExpDiff_eq_of_interior
      (T := T) (lam := lam) (B := B) (C := C) (w := w) (u := u)
      ht0 htT hx hw hu
    convert (hder.congr_of_eventuallyEq hEq) using 1
  have hder :
      HasDerivAt
        (fun y : ℝ => dx (driftExpDiff lam w u) t y + ε * (1 - 2 * y))
        (dxx (driftExpDiff lam w u) t x - 2 * ε) x := by
    have hlin : HasDerivAt (fun y : ℝ => ε * (1 - 2 * y)) (ε * (-2)) x := by
      convert ((hasDerivAt_const (x := x) (c := (1 : ℝ))).sub
        ((hasDerivAt_id x).const_mul (2 : ℝ))).const_mul ε using 1 <;> ring
    convert hz.add hlin using 1 <;> ring
  have hEq :
      (fun y : ℝ => dx (driftComparisonPerturb lam ε w u) t y)
        =ᶠ[𝓝 x]
      (fun y : ℝ => dx (driftExpDiff lam w u) t y + ε * (1 - 2 * y)) := by
    refine Filter.eventuallyEq_of_mem (Icc_mem_nhds_of_Ioo01 hx) ?_
    intro y hy
    exact dx_perturb_eq
      (hw.space_hasDerivAt ht0 htT hy)
      (hu.space_hasDerivAt ht0 htT hy)
  exact (hder.congr_of_eventuallyEq hEq).deriv

private lemma residual_perturb_shift_upper_bound_of_interior
    {T lam ε K : ℝ} {B C w u : ℝ → ℝ → ℝ} {t x : ℝ}
    (ht0 : 0 < t) (htT : t < T) (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hε_nonneg : 0 ≤ ε)
    (hlam_nonneg : 0 ≤ lam)
    (hB : |B t x| ≤ K)
    (hCabs : |C t x| ≤ K)
    (hK : 0 ≤ K)
    (hw :
      IsClassicalNeumannLinearDriftSubSolution T B C w)
    (hu :
      IsClassicalNeumannLinearDriftSuperSolution T B C u) :
    neumannLinearDriftResidual B (fun τ y => C τ y - lam)
        (driftComparisonPerturb lam ε w u) t x ≤
      ε * (2 + K + (lam + K) * 1 + 2 * K) := by
  have hz_nonpos :=
    residual_driftExpDiff_shift_nonpos_of_interior
      (T := T) (lam := lam) (B := B) (C := C) (w := w) (u := u)
      ht0 htT hx hw hu
  have hdt := dt_perturb_eq (lam := lam) (ε := ε)
    (hw.time_hasDerivAt ht0 htT (Set.Ioo_subset_Icc_self hx))
    (hu.time_hasDerivAt ht0 htT (Set.Ioo_subset_Icc_self hx))
  have hdx := dx_perturb_eq (lam := lam) (ε := ε)
    (hw.space_hasDerivAt ht0 htT (Set.Ioo_subset_Icc_self hx))
    (hu.space_hasDerivAt ht0 htT (Set.Ioo_subset_Icc_self hx))
  have hdxx := dxx_perturb_eq_of_interior
    (T := T) (lam := lam) (ε := ε) (B := B) (C := C) (w := w) (u := u)
    ht0 htT hx hw hu
  have hz_res_eq :
      neumannLinearDriftResidual B (fun τ y => C τ y - lam)
          (driftComparisonPerturb lam ε w u) t x =
        neumannLinearDriftResidual B (fun τ y => C τ y - lam)
          (driftExpDiff lam w u) t x
        + ε * (2 - B t x * (1 - 2 * x)
            - (C t x - lam) * intervalBump x
            + (C t x - lam) * 2) := by
    simp [residual_eq_dt_dx_dxx, hdt, hdx, hdxx, driftComparisonPerturb]
    ring
  rw [hz_res_eq]
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hx
  have hbump_nonneg : 0 ≤ intervalBump x := intervalBump_nonneg hxIcc
  have hbump_le : intervalBump x ≤ 1 := intervalBump_le_one hxIcc
  have hphi' : |1 - 2 * x| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith [hxIcc.1, hxIcc.2]
  have hBterm : -(B t x * (1 - 2 * x)) ≤ K := by
    calc
      -(B t x * (1 - 2 * x)) ≤ |-(B t x * (1 - 2 * x))| := le_abs_self _
      _ = |B t x * (1 - 2 * x)| := by rw [abs_neg]
      _ = |B t x| * |1 - 2 * x| := by rw [abs_mul]
      _ ≤ K * 1 := by
        exact mul_le_mul hB hphi' (abs_nonneg _) hK
      _ = K := by ring
  have hCneg : C t x - lam ≤ K := by
    have hC_le : C t x ≤ K := (le_abs_self _).trans hCabs
    linarith
  have hreact_bump :
      - (C t x - lam) * intervalBump x ≤ (lam + K) * 1 := by
    have hminus : -(C t x - lam) ≤ lam + K := by
      have hC_ge : -K ≤ C t x := by
        exact (neg_le_neg hCabs).trans (neg_abs_le (C t x))
      linarith
    have hlamK_nonneg : 0 ≤ lam + K := by
      linarith
    calc
      - (C t x - lam) * intervalBump x ≤ (lam + K) * intervalBump x := by
        exact mul_le_mul_of_nonneg_right hminus hbump_nonneg
      _ ≤ (lam + K) * 1 := by
        exact mul_le_mul_of_nonneg_left hbump_le hlamK_nonneg
  have hconst :
      (C t x - lam) * 2 ≤ 2 * K := by
    nlinarith [hCneg]
  have hraw :
      2 - B t x * (1 - 2 * x)
            - (C t x - lam) * intervalBump x
            + (C t x - lam) * 2
        ≤ 2 + K + (lam + K) * 1 + 2 * K := by
    nlinarith [hBterm, hreact_bump, hconst]
  have hraw_simple :
      2 - B t x * (1 - 2 * x)
            - (C t x - lam) * intervalBump x
            + (C t x - lam) * 2
        ≤ 2 + K + (lam + K) * 1 + 2 * K := hraw
  nlinarith [hz_nonpos, mul_le_mul_of_nonneg_left hraw_simple hε_nonneg]

private lemma perturb_time_hasDerivAt
    {lam ε : ℝ} {w u : ℝ → ℝ → ℝ} {t x : ℝ}
    (hw : HasDerivAt (fun τ : ℝ => w τ x) (dt w t x) t)
    (hu : HasDerivAt (fun τ : ℝ => u τ x) (dt u t x) t) :
    HasDerivAt (fun τ : ℝ => driftComparisonPerturb lam ε w u τ x)
      (dt (driftComparisonPerturb lam ε w u) t x) t := by
  have hExp :
      HasDerivAt (fun τ : ℝ => Real.exp (-(lam * τ)))
        (Real.exp (-(lam * t)) * (-lam)) t := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id t).const_mul lam).neg.exp)
  have hdiff : HasDerivAt (fun τ : ℝ => w τ x - u τ x)
      (dt w t x - dt u t x) t := hw.sub hu
  have hz :
      HasDerivAt (fun τ : ℝ => driftExpDiff lam w u τ x)
        (Real.exp (-(lam * t)) *
          (dt w t x - dt u t x - lam * (w t x - u t x))) t := by
    convert hExp.mul hdiff using 1 <;> ring
  have hψ :=
    (hz.add_const (ε * intervalBump x - 2 * ε))
  have hdt := dt_perturb_eq (lam := lam) (ε := ε) hw hu
  have hzdt := dt_driftExpDiff_eq (lam := lam) hw hu
  convert hψ using 1
  · funext τ
    unfold driftComparisonPerturb
    ring
  · rw [hdt, hzdt]

private lemma perturb_space_hasDerivAt
    {lam ε : ℝ} {w u : ℝ → ℝ → ℝ} {t x : ℝ}
    (hw : HasDerivAt (fun y : ℝ => w t y) (dx w t x) x)
    (hu : HasDerivAt (fun y : ℝ => u t y) (dx u t x) x) :
    HasDerivAt (fun y : ℝ => driftComparisonPerturb lam ε w u t y)
      (dx (driftComparisonPerturb lam ε w u) t x) x := by
  have hdiff : HasDerivAt (fun y : ℝ => w t y - u t y)
      (dx w t x - dx u t x) x := hw.sub hu
  have hz :
      HasDerivAt (fun y : ℝ => driftExpDiff lam w u t y)
        (Real.exp (-(lam * t)) * (dx w t x - dx u t x)) x := by
    simpa [driftExpDiff, Pi.mul_apply, mul_comm, mul_left_comm, mul_assoc] using
      (hasDerivAt_const x (Real.exp (-(lam * t)))).mul hdiff
  have hb :
      HasDerivAt (fun y : ℝ => ε * intervalBump y) (ε * (1 - 2 * x)) x :=
    (intervalBump_hasDerivAt x).const_mul ε
  have hψ := (hz.add hb).sub_const (2 * ε)
  have hdx := dx_perturb_eq (lam := lam) (ε := ε) hw hu
  have hzx := dx_driftExpDiff_eq (lam := lam) hw hu
  convert hψ using 1
  rw [hdx, hzx]

private lemma perturb_space_second_hasDerivAt_of_interior
    {T lam ε : ℝ} {B C w u : ℝ → ℝ → ℝ} {t x : ℝ}
    (ht0 : 0 < t) (htT : t < T) (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hw :
      IsClassicalNeumannLinearDriftSubSolution T B C w)
    (hu :
      IsClassicalNeumannLinearDriftSuperSolution T B C u) :
    HasDerivAt
      (fun y : ℝ => dx (driftComparisonPerturb lam ε w u) t y)
      (dxx (driftComparisonPerturb lam ε w u) t x) x := by
  have hder :
      HasDerivAt
        (fun y : ℝ => dx (driftExpDiff lam w u) t y + ε * (1 - 2 * y))
        (dxx (driftExpDiff lam w u) t x - 2 * ε) x := by
    have hz :
        HasDerivAt
          (fun y : ℝ => dx (driftExpDiff lam w u) t y)
          (dxx (driftExpDiff lam w u) t x) x := by
      have hbase :
          HasDerivAt
            (fun y : ℝ => Real.exp (-(lam * t)) * (dx w t y - dx u t y))
            (Real.exp (-(lam * t)) * (dxx w t x - dxx u t x)) x := by
        simpa [Pi.mul_apply, mul_comm, mul_left_comm, mul_assoc] using
          (hasDerivAt_const x (Real.exp (-(lam * t)))).mul
            ((hw.space_second_hasDerivAt ht0 htT hx).sub
              (hu.space_second_hasDerivAt ht0 htT hx))
      have hEq :
          (fun y : ℝ => dx (driftExpDiff lam w u) t y)
            =ᶠ[𝓝 x]
          (fun y : ℝ => Real.exp (-(lam * t)) * (dx w t y - dx u t y)) := by
        refine Filter.eventuallyEq_of_mem (Icc_mem_nhds_of_Ioo01 hx) ?_
        intro y hy
        exact dx_driftExpDiff_eq
          (hw.space_hasDerivAt ht0 htT hy)
          (hu.space_hasDerivAt ht0 htT hy)
      have hdxx_z := dxx_driftExpDiff_eq_of_interior
        (T := T) (lam := lam) (B := B) (C := C) (w := w) (u := u)
        ht0 htT hx hw hu
      rw [hdxx_z]
      exact hbase.congr_of_eventuallyEq hEq
    have hlin : HasDerivAt (fun y : ℝ => ε * (1 - 2 * y)) (ε * (-2)) x := by
      convert ((hasDerivAt_const (x := x) (c := (1 : ℝ))).sub
        ((hasDerivAt_id x).const_mul (2 : ℝ))).const_mul ε using 1 <;> ring
    convert hz.add hlin using 1 <;> ring
  have hEq :
      (fun y : ℝ => dx (driftComparisonPerturb lam ε w u) t y)
        =ᶠ[𝓝 x]
      (fun y : ℝ => dx (driftExpDiff lam w u) t y + ε * (1 - 2 * y)) := by
    refine Filter.eventuallyEq_of_mem (Icc_mem_nhds_of_Ioo01 hx) ?_
    intro y hy
    exact dx_perturb_eq
      (hw.space_hasDerivAt ht0 htT hy)
      (hu.space_hasDerivAt ht0 htT hy)
  have hdxx := dxx_perturb_eq_of_interior
    (T := T) (lam := lam) (ε := ε) (B := B) (C := C) (w := w) (u := u)
    ht0 htT hx hw hu
  convert (hder.congr_of_eventuallyEq hEq) using 1

private lemma perturb_residual_ge_at_interior_max
    {lam : ℝ} {B C ψ : ℝ → ℝ → ℝ} {t x : ℝ}
    (hdt : 0 ≤ dt ψ t x)
    (hdx : dx ψ t x = 0)
    (hdxx : dxx ψ t x ≤ 0)
    (ha : 1 ≤ lam - C t x)
    (hpos : 0 < ψ t x) :
    ψ t x ≤
      neumannLinearDriftResidual B (fun τ y => C τ y - lam) ψ t x := by
  rw [residual_eq_dt_dx_dxx, hdx]
  nlinarith

theorem neumann_interval_comparison_with_drift
    {T : ℝ} {B C : ℝ → ℝ → ℝ} {u₀ : ℝ → ℝ}
    {u : ℝ → ℝ → ℝ} :
    NeumannLinearDriftComparisonRegular T B C u₀ u := by
  intro w hT hcoeff hsuper hinit_u hsub hinit_w t x ht0 htT hx
  by_contra hnot
  have hpos_r : 0 < w t x - u t x := by linarith

  rcases hcoeff.drift_bounded with ⟨MB, hMB_nn, hMB⟩
  rcases hcoeff.reaction_bounded with ⟨MC, hMC_nn, hMC⟩
  let K : ℝ := MB + MC
  have hK_nn : 0 ≤ K := by dsimp [K]; nlinarith
  let lam : ℝ := K + 1
  have hlam_nn : 0 ≤ lam := by dsimp [lam]; nlinarith
  have hlam_gap :
      ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        1 ≤ lam - C s y := by
    intro s hs y hy
    have hC_le : C s y ≤ MC := (le_abs_self _).trans (hMC s hs y hy)
    dsimp [lam, K]
    nlinarith [hC_le, hMB_nn]
  have hB_K :
      ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        |B s y| ≤ K := by
    intro s hs y hy
    have h := hMB s hs y hy
    dsimp [K]
    nlinarith [h, hMC_nn]
  have hC_K :
      ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        |C s y| ≤ K := by
    intro s hs y hy
    have h := hMC s hs y hy
    dsimp [K]
    nlinarith [h, hMB_nn]

  let z0 : ℝ := driftExpDiff lam w u t x
  have hz0_pos : 0 < z0 := by
    dsimp [z0, driftExpDiff]
    exact mul_pos (Real.exp_pos _) hpos_r
  let U : ℝ := 2 + K + (lam + K) * 1 + 2 * K
  have hU_nn : 0 ≤ U := by
    dsimp [U, lam]
    nlinarith [hK_nn]
  let ε : ℝ := z0 / (4 * (U + 1))
  have hden_pos : 0 < 4 * (U + 1) := by
    nlinarith [hU_nn]
  have hε_pos : 0 < ε := by
    dsimp [ε]
    exact div_pos hz0_pos hden_pos
  have hε_nonneg : 0 ≤ ε := le_of_lt hε_pos
  have htwoε_lt_z0 : 2 * ε < z0 := by
    have hfactor_lt : (2 : ℝ) / (4 * (U + 1)) < 1 := by
      rw [div_lt_one hden_pos]
      nlinarith [hU_nn]
    have hfactor_nonneg : 0 ≤ (2 : ℝ) / (4 * (U + 1)) := by positivity
    have hprod := mul_lt_mul_of_pos_left hfactor_lt hz0_pos
    have hrewrite : 2 * ε = z0 * ((2 : ℝ) / (4 * (U + 1))) := by
      dsimp [ε]
      ring
    rw [hrewrite]
    simpa using hprod
  have hεU_lt_z0 : ε * (U + 2) < z0 := by
    have hfactor_lt : (U + 2) / (4 * (U + 1)) < 1 := by
      rw [div_lt_one hden_pos]
      nlinarith [hU_nn]
    have hprod := mul_lt_mul_of_pos_left hfactor_lt hz0_pos
    have hrewrite : ε * (U + 2) =
        z0 * ((U + 2) / (4 * (U + 1))) := by
      dsimp [ε]
      ring
    rw [hrewrite]
    simpa using hprod

  let ψ : ℝ → ℝ → ℝ := driftComparisonPerturb lam ε w u

  have hψ_cont :
      ContinuousOn (fun p : ℝ × ℝ => ψ p.1 p.2)
        (Set.Icc (0 : ℝ) t ×ˢ Set.Icc (0 : ℝ) 1) := by
    have hwu_T :
        ContinuousOn (fun p : ℝ × ℝ => w p.1 p.2 - u p.1 p.2)
          (Set.Icc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
      hsub.continuousOn_rect.sub hsuper.continuousOn_rect
    have hwu :
        ContinuousOn (fun p : ℝ × ℝ => w p.1 p.2 - u p.1 p.2)
          (Set.Icc (0 : ℝ) t ×ˢ Set.Icc (0 : ℝ) 1) :=
      hwu_T.mono (by
        intro p hp
        exact ⟨⟨hp.1.1, le_trans hp.1.2 (le_of_lt htT)⟩, hp.2⟩)
    have hlin_cont : Continuous (fun p : ℝ × ℝ => -(lam * p.1)) :=
      (continuous_const.mul continuous_fst).neg
    have hexp_cont :
        ContinuousOn (fun p : ℝ × ℝ => Real.exp (-(lam * p.1)))
          (Set.Icc (0 : ℝ) t ×ˢ Set.Icc (0 : ℝ) 1) :=
      (Real.continuous_exp.comp hlin_cont).continuousOn
    have hz_cont :
        ContinuousOn (fun p : ℝ × ℝ => driftExpDiff lam w u p.1 p.2)
          (Set.Icc (0 : ℝ) t ×ˢ Set.Icc (0 : ℝ) 1) := by
      change ContinuousOn
        (fun p : ℝ × ℝ => Real.exp (-(lam * p.1)) *
          (w p.1 p.2 - u p.1 p.2))
        (Set.Icc (0 : ℝ) t ×ˢ Set.Icc (0 : ℝ) 1)
      exact hexp_cont.mul hwu
    have hbump_cont :
        Continuous (fun p : ℝ × ℝ => ε * intervalBump p.2 - 2 * ε) := by
      unfold intervalBump
      exact (continuous_const.mul
        (continuous_snd.mul (continuous_const.sub continuous_snd))).sub
          continuous_const
    change ContinuousOn
      (fun p : ℝ × ℝ =>
        driftExpDiff lam w u p.1 p.2 + ε * intervalBump p.2 - 2 * ε)
      (Set.Icc (0 : ℝ) t ×ˢ Set.Icc (0 : ℝ) 1)
    convert hz_cont.add hbump_cont.continuousOn using 1
    funext p
    simp [Pi.add_apply]
    ring

  have hψ_point_pos : 0 < ψ t x := by
    have hphi_nonneg : 0 ≤ intervalBump x := intervalBump_nonneg hx
    dsimp [ψ, driftComparisonPerturb, z0] at *
    nlinarith

  obtain ⟨p, hp, hmax⟩ :=
    exists_max_on_unit_strip (T := t) (F := fun p : ℝ × ℝ => ψ p.1 p.2)
      (le_of_lt ht0) hψ_cont
  rcases p with ⟨tp, xp⟩
  have hp_pos : 0 < ψ tp xp := by
    exact lt_of_lt_of_le hψ_point_pos
      (hmax (t, x) ⟨⟨le_of_lt ht0, le_rfl⟩, hx⟩)
  have htp_ne_zero : tp ≠ 0 := by
    intro htp0
    have hinit_le : driftExpDiff lam w u 0 xp ≤ 0 := by
      dsimp [driftExpDiff]
      simp only [mul_zero, neg_zero, Real.exp_zero, one_mul]
      have hwu0 : w 0 xp ≤ u 0 xp := by
        have hw0 := hinit_w xp hp.2
        have hu0 := hinit_u xp hp.2
        linarith
      linarith
    have hneg : ψ 0 xp < 0 := by
      have hphi_le : intervalBump xp ≤ 1 := intervalBump_le_one hp.2
      dsimp [ψ, driftComparisonPerturb]
      nlinarith [hinit_le, hphi_le, hε_pos]
    have : ψ tp xp < 0 := by simpa [htp0] using hneg
    linarith
  have htp_pos : 0 < tp := lt_of_le_of_ne hp.1.1 (Ne.symm htp_ne_zero)
  have htp_lt_T : tp < T := lt_of_le_of_lt hp.1.2 htT
  have htp_Icc_T : tp ∈ Set.Icc (0 : ℝ) T :=
    ⟨le_of_lt htp_pos, le_of_lt htp_lt_T⟩

  have hxp_ne_zero : xp ≠ 0 := by
    intro hxp0
    have hmax_x : ∀ y ∈ Set.Icc (0 : ℝ) 1, ψ tp y ≤ ψ tp 0 := by
      intro y hy
      simpa [hxp0] using hmax (tp, y) ⟨hp.1, hy⟩
    have hder0_base :
        HasDerivAt (fun y : ℝ => ψ tp y)
          (dx (driftComparisonPerturb lam ε w u) tp 0) 0 := by
      dsimp [ψ]
      exact perturb_space_hasDerivAt (lam := lam) (ε := ε)
        (hsub.space_hasDerivAt htp_pos htp_lt_T
          (left_mem_Icc.mpr zero_le_one))
        (hsuper.space_hasDerivAt htp_pos htp_lt_T
          (left_mem_Icc.mpr zero_le_one))
    have hdx0 : dx (driftComparisonPerturb lam ε w u) tp 0 = ε := by
      have hdxp := dx_perturb_eq (lam := lam) (ε := ε)
        (hsub.space_hasDerivAt htp_pos htp_lt_T
          (left_mem_Icc.mpr zero_le_one))
        (hsuper.space_hasDerivAt htp_pos htp_lt_T
          (left_mem_Icc.mpr zero_le_one))
      have hdxz := dx_driftExpDiff_eq (lam := lam)
        (hsub.space_hasDerivAt htp_pos htp_lt_T
          (left_mem_Icc.mpr zero_le_one))
        (hsuper.space_hasDerivAt htp_pos htp_lt_T
          (left_mem_Icc.mpr zero_le_one))
      have hnw := (hsub.neumann tp htp_pos htp_lt_T).1
      have hnu := (hsuper.neumann tp htp_pos htp_lt_T).1
      rw [hdxp, hdxz, hnw, hnu]
      ring
    have hder0 : HasDerivAt (fun y : ℝ => ψ tp y) ε 0 := by
      simpa [hdx0] using hder0_base
    exact left_endpoint_not_max_of_pos_deriv hder0 hε_pos hmax_x

  have hxp_ne_one : xp ≠ 1 := by
    intro hxp1
    have hmax_x : ∀ y ∈ Set.Icc (0 : ℝ) 1, ψ tp y ≤ ψ tp 1 := by
      intro y hy
      simpa [hxp1] using hmax (tp, y) ⟨hp.1, hy⟩
    have hder1_base :
        HasDerivAt (fun y : ℝ => ψ tp y)
          (dx (driftComparisonPerturb lam ε w u) tp 1) 1 := by
      dsimp [ψ]
      exact perturb_space_hasDerivAt (lam := lam) (ε := ε)
        (hsub.space_hasDerivAt htp_pos htp_lt_T
          (right_mem_Icc.mpr zero_le_one))
        (hsuper.space_hasDerivAt htp_pos htp_lt_T
          (right_mem_Icc.mpr zero_le_one))
    have hdx1 : dx (driftComparisonPerturb lam ε w u) tp 1 = -ε := by
      have hdxp := dx_perturb_eq (lam := lam) (ε := ε)
        (hsub.space_hasDerivAt htp_pos htp_lt_T
          (right_mem_Icc.mpr zero_le_one))
        (hsuper.space_hasDerivAt htp_pos htp_lt_T
          (right_mem_Icc.mpr zero_le_one))
      have hdxz := dx_driftExpDiff_eq (lam := lam)
        (hsub.space_hasDerivAt htp_pos htp_lt_T
          (right_mem_Icc.mpr zero_le_one))
        (hsuper.space_hasDerivAt htp_pos htp_lt_T
          (right_mem_Icc.mpr zero_le_one))
      have hnw := (hsub.neumann tp htp_pos htp_lt_T).2
      have hnu := (hsuper.neumann tp htp_pos htp_lt_T).2
      rw [hdxp, hdxz, hnw, hnu]
      ring
    have hder1 : HasDerivAt (fun y : ℝ => ψ tp y) (-ε) 1 := by
      simpa [hdx1] using hder1_base
    exact right_endpoint_not_max_of_neg_deriv hder1 (by linarith) hmax_x

  have hxp_int : xp ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hp.2.1 (Ne.symm hxp_ne_zero),
      lt_of_le_of_ne hp.2.2 hxp_ne_one⟩
  have hxp_Icc : xp ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hxp_int

  have hdt_der :
      HasDerivAt (fun τ : ℝ => ψ τ xp) (dt ψ tp xp) tp := by
    dsimp [ψ]
    exact perturb_time_hasDerivAt (lam := lam) (ε := ε)
      (hsub.time_hasDerivAt htp_pos htp_lt_T hxp_Icc)
      (hsuper.time_hasDerivAt htp_pos htp_lt_T hxp_Icc)
  have hdt_nonneg : 0 ≤ dt ψ tp xp :=
    time_deriv_nonneg_at_Icc_max
      (ψ := ψ) (T := t) hp.1 htp_pos hdt_der
      (fun s hs => hmax (s, xp) ⟨hs, hp.2⟩)
  have hdx_der :
      HasDerivAt (fun y : ℝ => ψ tp y) (dx ψ tp xp) xp := by
    dsimp [ψ]
    exact perturb_space_hasDerivAt (lam := lam) (ε := ε)
      (hsub.space_hasDerivAt htp_pos htp_lt_T hxp_Icc)
      (hsuper.space_hasDerivAt htp_pos htp_lt_T hxp_Icc)
  have hdx_zero : dx ψ tp xp = 0 :=
    space_deriv_eq_zero_at_Icc_interior_max hxp_int hdx_der
      (fun y hy => hmax (tp, y) ⟨hp.1, hy⟩)
  have hdx_all :
      ∀ y ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (fun r : ℝ => ψ tp r) (dx ψ tp y) y := by
    intro y hy
    dsimp [ψ]
    exact perturb_space_hasDerivAt (lam := lam) (ε := ε)
      (hsub.space_hasDerivAt htp_pos htp_lt_T hy)
      (hsuper.space_hasDerivAt htp_pos htp_lt_T hy)
  have hdxx_der :
      HasDerivAt (fun y : ℝ => dx ψ tp y) (dxx ψ tp xp) xp := by
    dsimp [ψ]
    exact perturb_space_second_hasDerivAt_of_interior
      (T := T) (lam := lam) (ε := ε) (B := B) (C := C) (w := w) (u := u)
      htp_pos htp_lt_T hxp_int hsub hsuper
  have hdxx_nonpos : dxx ψ tp xp ≤ 0 :=
    second_space_deriv_nonpos_at_Icc_interior_max hxp_int hdx_all hdxx_der
      (fun y hy => hmax (tp, y) ⟨hp.1, hy⟩)

  have hres_lower :
      ψ tp xp ≤
        neumannLinearDriftResidual B (fun τ y => C τ y - lam) ψ tp xp :=
    perturb_residual_ge_at_interior_max
      (lam := lam) (B := B) (C := C) (ψ := ψ)
      hdt_nonneg hdx_zero hdxx_nonpos
      (hlam_gap tp htp_Icc_T xp hxp_Icc) hp_pos
  have hres_upper :
      neumannLinearDriftResidual B (fun τ y => C τ y - lam) ψ tp xp
        ≤ ε * U := by
    dsimp [ψ, U]
    exact residual_perturb_shift_upper_bound_of_interior
      (T := T) (lam := lam) (ε := ε) (K := K)
      (B := B) (C := C) (w := w) (u := u)
      htp_pos htp_lt_T hxp_int hε_nonneg hlam_nn
      (hB_K tp htp_Icc_T xp hxp_Icc)
      (hC_K tp htp_Icc_T xp hxp_Icc)
      hK_nn hsub hsuper
  have hψ_le : ψ tp xp ≤ ε * U := le_trans hres_lower hres_upper
  have hpoint_le_max :
      z0 - 2 * ε ≤ ψ tp xp := by
    have hphi_nonneg : 0 ≤ intervalBump x := intervalBump_nonneg hx
    have hle := hmax (t, x) ⟨⟨le_of_lt ht0, le_rfl⟩, hx⟩
    dsimp [ψ, driftComparisonPerturb, z0] at hle ⊢
    nlinarith
  have hz0_le : z0 ≤ ε * (U + 2) := by
    nlinarith [hpoint_le_max, hψ_le]
  exact not_lt_of_ge hz0_le hεU_lt_z0

end NeumannLinearDriftComparisonRegularDischarge

/-- Public discharge of the regular Neumann interval comparison principle with
first-order drift. -/
theorem neumann_interval_comparison_with_drift
    {T : ℝ} {B C : ℝ → ℝ → ℝ} {u₀ : ℝ → ℝ}
    {u : ℝ → ℝ → ℝ} :
    NeumannLinearDriftComparisonRegular T B C u₀ u :=
  NeumannLinearDriftComparisonRegularDischarge.neumann_interval_comparison_with_drift

theorem NeumannLinearDriftComparisonRegular.unconditional
    {T : ℝ} {B C : ℝ → ℝ → ℝ} {u₀ : ℝ → ℝ}
    {u : ℝ → ℝ → ℝ} :
    NeumannLinearDriftComparisonRegular T B C u₀ u :=
  neumann_interval_comparison_with_drift

/-- Strict positivity through the regular comparison route, with the comparison
principle discharged in this file. -/
theorem strict_pos_of_neumann_linear_drift_square_heat_subsolution_regular_unconditional
    {T A D M : ℝ} {u₀ f : ℝ → ℝ} {B C u : ℝ → ℝ → ℝ}
    (hT : 0 < T)
    (hcoeff : NeumannLinearDriftCoefficientsRegular T B C)
    (hsuper : IsClassicalNeumannLinearDriftSuperSolution T B C u)
    (hu_initial : ∀ x ∈ Set.Icc (0 : ℝ) 1, u 0 x = u₀ x)
    (hbarrier_reg :
      NeumannLinearDriftSubSolutionRegularity T B C (squareHeatBarrier M f))
    (hcalc : SquareHeatSubsolutionCalculus T M f B C)
    (hM : A ^ 2 / 2 + D ≤ M)
    (hB_bound :
      ∀ t x, 0 < t → t < T → x ∈ Set.Ioo (0 : ℝ) 1 → |B t x| ≤ A)
    (hC_neg_bound :
      ∀ t x, 0 < t → t < T → x ∈ Set.Ioo (0 : ℝ) 1 → -C t x ≤ D)
    (hseed : SquareHeatSeed u₀ f) :
    ∀ t x, 0 < t → t < T → x ∈ Set.Icc (0 : ℝ) 1 →
      0 < u t x :=
  strict_pos_of_neumann_linear_drift_square_heat_subsolution_regular
    hT hcoeff hsuper hu_initial neumann_interval_comparison_with_drift
    hbarrier_reg hcalc hM hB_bound hC_neg_bound hseed

/-- B-form strict positivity with the regular comparison principle discharged. -/
theorem bform_strictPos_of_square_heat_subsolution_regular_unconditional
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    {A D M : ℝ} {f : ℝ → ℝ} {drift react : ℝ → ℝ → ℝ}
    (hcoeff : NeumannLinearDriftCoefficientsRegular DB.T drift react)
    (hsuper :
      IsClassicalNeumannLinearDriftSuperSolution DB.T drift react
        (bformConjugatePicardLift p DB))
    (hu_initial :
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        bformConjugatePicardLift p DB 0 x = intervalDomainLift u₀ x)
    (hbarrier_reg :
      NeumannLinearDriftSubSolutionRegularity DB.T drift react
        (squareHeatBarrier M f))
    (hcalc : SquareHeatSubsolutionCalculus DB.T M f drift react)
    (hM : A ^ 2 / 2 + D ≤ M)
    (hB_bound :
      ∀ t x, 0 < t → t < DB.T → x ∈ Set.Ioo (0 : ℝ) 1 →
        |drift t x| ≤ A)
    (hC_neg_bound :
      ∀ t x, 0 < t → t < DB.T → x ∈ Set.Ioo (0 : ℝ) 1 →
        -react t x ≤ D)
    (hseed : SquareHeatSeed (intervalDomainLift u₀) f) :
    ∀ t x, 0 < t → t < DB.T →
      0 < conjugatePicardLimit p u₀ DB.T t x :=
  bform_strictPos_of_square_heat_subsolution_regular
    hcoeff hsuper hu_initial neumann_interval_comparison_with_drift
    hbarrier_reg hcalc hM hB_bound hC_neg_bound hseed

/-- Route constructor with the regular comparison principle discharged. -/
def bform_negpart_route_of_square_heat_subsolution_regular_unconditional
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    {A D M : ℝ} {f : ℝ → ℝ} {drift react : ℝ → ℝ → ℝ}
    (datum : PositiveInitialDatum intervalDomain u₀)
    (Bbank : ShenWork.Paper2.BFormDirectClassical.BFormBankedInputs p DB)
    (hnegativePart_zero :
      ∀ t, 0 < t → t ≤ DB.T → ∀ x : intervalDomainPoint,
        negativePart (conjugatePicardLimit p u₀ DB.T t x) = 0)
    (hcoeff : NeumannLinearDriftCoefficientsRegular DB.T drift react)
    (hsuper :
      IsClassicalNeumannLinearDriftSuperSolution DB.T drift react
        (bformConjugatePicardLift p DB))
    (hu_initial :
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        bformConjugatePicardLift p DB 0 x = intervalDomainLift u₀ x)
    (hbarrier_reg :
      NeumannLinearDriftSubSolutionRegularity DB.T drift react
        (squareHeatBarrier M f))
    (hcalc : SquareHeatSubsolutionCalculus DB.T M f drift react)
    (hM : A ^ 2 / 2 + D ≤ M)
    (hB_bound :
      ∀ t x, 0 < t → t < DB.T → x ∈ Set.Ioo (0 : ℝ) 1 →
        |drift t x| ≤ A)
    (hC_neg_bound :
      ∀ t x, 0 < t → t < DB.T → x ∈ Set.Ioo (0 : ℝ) 1 →
        -react t x ≤ D)
    (hseed : SquareHeatSeed (intervalDomainLift u₀) f) :
    BFormNegativePartPositivityRoute p DB :=
  bform_negpart_route_of_square_heat_subsolution_regular datum Bbank
    hnegativePart_zero hcoeff hsuper hu_initial
    neumann_interval_comparison_with_drift hbarrier_reg hcalc hM
    hB_bound hC_neg_bound hseed

end ShenWork.Paper2.BFormPositiveDatumNegPart
