/-
  MinPersistence atoms, Phase A(i): one-dimensional second-derivative
  tests at interior local extrema.

  These are the pointwise calculus facts behind the parabolic minimum
  principle (Hamilton's trick) for `ClassicalMinPersistence`:
  at an interior spatial argmin `x*` of a `C²` slice,
  `deriv f x* = 0` and `deriv (deriv f) x* ≥ 0`, so the diffusion term
  in the PDE pushes the minimum UP, leaving only the zeroth-order
  (logistic + chemotaxis-coefficient) terms — which are `≥ −K·f(x*)`.

  No `sorry`/`admit`/custom `axiom`.
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section

namespace ShenWork.MinPersistenceAtoms

/-- **Second-derivative test at a local minimum.**  If `f` is
differentiable near `x`, its derivative has derivative `D` at `x`, and
`x` is a local minimum of `f`, then `0 ≤ D`. -/
theorem deriv2_nonneg_of_isLocalMin {f : ℝ → ℝ} {x D : ℝ}
    (hmin : IsLocalMin f x)
    (hdiff : ∀ᶠ y in nhds x, DifferentiableAt ℝ f y)
    (hf'' : HasDerivAt (deriv f) D x) :
    0 ≤ D := by
  by_contra hD
  push_neg at hD
  -- The derivative vanishes at the local minimum.
  have hf'0 : deriv f x = 0 := hmin.deriv_eq_zero
  -- The slope of `deriv f` at `x` tends to `D < 0`; to the right of `x`
  -- this forces `deriv f y < 0`.
  have hslope : Filter.Tendsto (slope (deriv f) x)
      (nhdsWithin x {x}ᶜ) (nhds D) :=
    hasDerivAt_iff_tendsto_slope.mp hf''
  have hev : ∀ᶠ y in nhdsWithin x {x}ᶜ,
      slope (deriv f) x y < D / 2 :=
    hslope.eventually_lt_const (by linarith)
  have hIoi_sub : Set.Ioi x ⊆ ({x}ᶜ : Set ℝ) := fun y hy =>
    Set.mem_compl_singleton_iff.mpr (ne_of_gt hy)
  have hev' : ∀ᶠ y in nhdsWithin x (Set.Ioi x),
      slope (deriv f) x y < D / 2 :=
    hev.filter_mono (nhdsWithin_mono x hIoi_sub)
  have hneg : ∀ᶠ y in nhdsWithin x (Set.Ioi x), deriv f y < 0 := by
    filter_upwards [hev', self_mem_nhdsWithin] with y hy hyI
    have hyx : 0 < y - x := sub_pos.mpr hyI
    have hslope_eq : slope (deriv f) x y = deriv f y / (y - x) := by
      rw [slope_def_field, hf'0]
      ring
    rw [hslope_eq] at hy
    have hD2 : D / 2 < 0 := by linarith
    have := (div_lt_iff₀ hyx).mp (lt_trans hy hD2)
    linarith [this]
  -- Extract concrete radii from the three eventual facts.
  obtain ⟨u, hu_mem, hu_sub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hneg
  have hboth : ∀ᶠ y in nhds x, DifferentiableAt ℝ f y ∧ f x ≤ f y :=
    hdiff.and hmin
  rw [Metric.eventually_nhds_iff] at hboth
  obtain ⟨ε, hε, hball⟩ := hboth
  set η : ℝ := min ((u - x) / 2) (ε / 2) with hη_def
  have hux : 0 < u - x := sub_pos.mpr hu_mem
  have hη : 0 < η := lt_min (by linarith) (by linarith)
  -- All points of `[x, x+η]` are differentiable and ≥ f x.
  have hIcc_props : ∀ y ∈ Set.Icc x (x + η),
      DifferentiableAt ℝ f y ∧ f x ≤ f y := by
    intro y hy
    apply hball
    rw [Real.dist_eq, abs_sub_lt_iff]
    constructor
    · have : η ≤ ε / 2 := min_le_right _ _
      linarith [hy.1, hy.2]
    · linarith [hy.1, hy.2, hε]
  -- `deriv f < 0` on the open part.
  have hderiv_neg : ∀ y ∈ Set.Ioo x (x + η), deriv f y < 0 := by
    intro y hy
    apply hu_sub
    have : η ≤ (u - x) / 2 := min_le_left _ _
    exact ⟨hy.1, by linarith [hy.2]⟩
  -- Strict decrease on `[x, x+η]` contradicts the local minimum.
  have hcont : ContinuousOn f (Set.Icc x (x + η)) := fun y hy =>
    ((hIcc_props y hy).1.continuousAt).continuousWithinAt
  have hanti : StrictAntiOn f (Set.Icc x (x + η)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hcont
    intro y hy
    rw [interior_Icc] at hy
    exact hderiv_neg y hy
  have hlt : f (x + η) < f x :=
    hanti (Set.left_mem_Icc.mpr (by linarith))
      (Set.right_mem_Icc.mpr (by linarith)) (by linarith)
  have hge : f x ≤ f (x + η) :=
    (hIcc_props (x + η) (Set.right_mem_Icc.mpr (by linarith))).2
  linarith

/-- **Second-derivative test at a local maximum** (negation of the
minimum version). -/
theorem deriv2_nonpos_of_isLocalMax {f : ℝ → ℝ} {x D : ℝ}
    (hmax : IsLocalMax f x)
    (hdiff : ∀ᶠ y in nhds x, DifferentiableAt ℝ f y)
    (hf'' : HasDerivAt (deriv f) D x) :
    D ≤ 0 := by
  have hminneg : IsLocalMin (fun y => -f y) x := hmax.neg
  have hdiffneg : ∀ᶠ y in nhds x, DifferentiableAt ℝ (fun z => -f z) y :=
    hdiff.mono (fun y hy => hy.neg)
  have hf''neg : HasDerivAt (deriv (fun z => -f z)) (-D) x := by
    have heq : deriv (fun z => -f z) = fun y => -deriv f y :=
      funext (fun y => deriv.neg)
    rw [heq]
    exact hf''.neg
  linarith [deriv2_nonneg_of_isLocalMin hminneg hdiffneg hf''neg]

/-! ## Phase A(iii): the one-dimensional elliptic sup bound

`w'' = μ·w − Src` on `(0,1)` with `|Src| ≤ B`, Neumann limits at the
endpoints, and `w` continuous on `[0,1]` force `w ≤ B/μ`.

The proof avoids one-sided second-derivative tests entirely: if
`w(x*) > B/μ` at an argmax `x*`, the PDE forces `w'' > 0` on a
neighbourhood, so `w'` is strictly increasing there; the pivot
(`w'(x*) = 0` at an interior argmax, `w' → 0` at a Neumann endpoint)
then makes `w'` one-signed adjacent to `x*`, so `w` strictly
increases/decreases away from the maximum — a contradiction. -/

/-- `w'` is strictly positive just RIGHT of `a` when `w'' > 0` on
`(a, a+η)` and `w' → 0` along `a⁺`. -/
private theorem deriv_pos_right_of_deriv2_pos_of_pivot
    {w : ℝ → ℝ} {a η : ℝ} (_hη : 0 < η)
    (hd1 : ∀ y ∈ Set.Ioo a (a + η), DifferentiableAt ℝ (deriv w) y)
    (hd2pos : ∀ y ∈ Set.Ioo a (a + η), 0 < deriv (deriv w) y)
    (hpivot : Filter.Tendsto (deriv w) (nhdsWithin a (Set.Ioi a)) (nhds 0)) :
    ∀ y ∈ Set.Ioo a (a + η), 0 < deriv w y := by
  have hmono : ∀ z y, a < z → z < y → y < a + η → deriv w z < deriv w y := by
    intro z y hz hzy hy
    have hstrict : StrictMonoOn (deriv w) (Set.Icc z y) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      · intro r hr
        exact ((hd1 r ⟨lt_of_lt_of_le hz hr.1,
          lt_of_le_of_lt hr.2 hy⟩).continuousAt).continuousWithinAt
      · intro r hr
        rw [interior_Icc] at hr
        exact hd2pos r ⟨lt_trans hz hr.1, lt_trans hr.2 hy⟩
    exact hstrict (Set.left_mem_Icc.mpr hzy.le)
      (Set.right_mem_Icc.mpr hzy.le) hzy
  intro y hy
  set y' : ℝ := a + (y - a) / 2 with hy'_def
  have hay' : a < y' := by
    have := hy.1
    simp only [hy'_def]; linarith
  have hy'y : y' < y := by
    have := hy.1
    simp only [hy'_def]; linarith
  have hy'_nonneg : 0 ≤ deriv w y' := by
    apply le_of_tendsto hpivot
    filter_upwards [Ioo_mem_nhdsGT hay'] with z hz
    exact (hmono z y' hz.1 hz.2 (lt_trans hy'y hy.2)).le
  exact lt_of_le_of_lt hy'_nonneg (hmono y' y hay' hy'y hy.2)

/-- `w'` is strictly negative just LEFT of `b` when `w'' > 0` on
`(b−η, b)` and `w' → 0` along `b⁻`. -/
private theorem deriv_neg_left_of_deriv2_pos_of_pivot
    {w : ℝ → ℝ} {b η : ℝ} (_hη : 0 < η)
    (hd1 : ∀ y ∈ Set.Ioo (b - η) b, DifferentiableAt ℝ (deriv w) y)
    (hd2pos : ∀ y ∈ Set.Ioo (b - η) b, 0 < deriv (deriv w) y)
    (hpivot : Filter.Tendsto (deriv w) (nhdsWithin b (Set.Iio b)) (nhds 0)) :
    ∀ y ∈ Set.Ioo (b - η) b, deriv w y < 0 := by
  have hmono : ∀ z y, b - η < z → z < y → y < b → deriv w z < deriv w y := by
    intro z y hz hzy hy
    have hstrict : StrictMonoOn (deriv w) (Set.Icc z y) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      · intro r hr
        exact ((hd1 r ⟨lt_of_lt_of_le hz hr.1,
          lt_of_le_of_lt hr.2 hy⟩).continuousAt).continuousWithinAt
      · intro r hr
        rw [interior_Icc] at hr
        exact hd2pos r ⟨lt_trans hz hr.1, lt_trans hr.2 hy⟩
    exact hstrict (Set.left_mem_Icc.mpr hzy.le)
      (Set.right_mem_Icc.mpr hzy.le) hzy
  intro y hy
  set y' : ℝ := b - (b - y) / 2 with hy'_def
  have hyy' : y < y' := by
    have := hy.2
    simp only [hy'_def]; linarith
  have hy'b : y' < b := by
    have := hy.2
    simp only [hy'_def]; linarith
  have hy'_nonpos : deriv w y' ≤ 0 := by
    apply ge_of_tendsto hpivot
    filter_upwards [Ioo_mem_nhdsLT hy'b] with z hz
    exact (hmono y' z (lt_trans hy.1 hyy') hz.1 hz.2).le
  exact lt_of_lt_of_le (hmono y y' hy.1 hyy' hy'b) hy'_nonpos

set_option maxHeartbeats 800000 in
/-- **One-dimensional elliptic sup bound.**  If `w` is continuous on
`[0,1]`, `C²` on `(0,1)` with `w'' = μ·w − Src` there, `|Src| ≤ B` on
the interior, and `w'` has Neumann limits `0` at both endpoints, then
`w ≤ B/μ` on `[0,1]`. -/
theorem elliptic_sup_bound
    {w Src : ℝ → ℝ} {μ B : ℝ} (hμ : 0 < μ)
    (hcont : ContinuousOn w (Set.Icc (0:ℝ) 1))
    (hd1 : ∀ y ∈ Set.Ioo (0:ℝ) 1, DifferentiableAt ℝ w y)
    (hd2 : ∀ y ∈ Set.Ioo (0:ℝ) 1, DifferentiableAt ℝ (deriv w) y)
    (hPDE : ∀ y ∈ Set.Ioo (0:ℝ) 1, deriv (deriv w) y = μ * w y - Src y)
    (hSrc : ∀ y ∈ Set.Ioo (0:ℝ) 1, |Src y| ≤ B)
    (hNeu0 : Filter.Tendsto (deriv w) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hNeu1 : Filter.Tendsto (deriv w) (nhdsWithin 1 (Set.Iio 1)) (nhds 0)) :
    ∀ x ∈ Set.Icc (0:ℝ) 1, w x ≤ B / μ := by
  obtain ⟨x₀, hx₀_mem, hx₀_max⟩ :=
    isCompact_Icc.exists_isMaxOn ⟨0, Set.left_mem_Icc.mpr zero_le_one⟩ hcont
  suffices hmax : w x₀ ≤ B / μ by
    intro x hx
    exact le_trans (hx₀_max hx) hmax
  by_contra hgt
  push_neg at hgt
  -- The PDE forces `w'' > 0` wherever `w > B/μ`.
  have hpos_at : ∀ y ∈ Set.Ioo (0:ℝ) 1, B / μ < w y →
      0 < deriv (deriv w) y := by
    intro y hy hwy
    rw [hPDE y hy]
    have h1 : B < μ * w y := by
      have := (div_lt_iff₀ hμ).mp hwy
      linarith
    have h2 := (abs_le.mp (hSrc y hy)).2
    linarith
  -- A one-sided neighbourhood of the argmax where `w > B/μ`.
  have hev : ∀ᶠ y in nhdsWithin x₀ (Set.Icc (0:ℝ) 1), B / μ < w y :=
    (hcont x₀ hx₀_mem).eventually_const_lt hgt
  rw [Filter.eventually_iff, mem_nhdsWithin] at hev
  obtain ⟨U, hU_open, hx₀U, hUsub⟩ := hev
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU_open x₀ hx₀U
  have hgt_near : ∀ y, |y - x₀| < ε → y ∈ Set.Icc (0:ℝ) 1 → B / μ < w y := by
    intro y hyε hy01
    apply hUsub
    refine ⟨hball ?_, hy01⟩
    rw [Metric.mem_ball, Real.dist_eq]
    exact hyε
  rcases lt_or_eq_of_le hx₀_mem.1 with h0x | h0x
  · rcases lt_or_eq_of_le hx₀_mem.2 with hx1 | hx1
    · -- Interior argmax.
      have hx₀_in : x₀ ∈ Set.Ioo (0:ℝ) 1 := ⟨h0x, hx1⟩
      set η : ℝ := min (ε / 2) ((1 - x₀) / 2) with hη_def
      have hη : 0 < η := lt_min (by linarith) (by linarith)
      have hsub : Set.Ioo x₀ (x₀ + η) ⊆ Set.Ioo (0:ℝ) 1 := by
        intro y hy
        have h1 : η ≤ (1 - x₀) / 2 := min_le_right _ _
        exact ⟨lt_trans h0x hy.1, by linarith [hy.2]⟩
      have hd2pos : ∀ y ∈ Set.Ioo x₀ (x₀ + η), 0 < deriv (deriv w) y := by
        intro y hy
        apply hpos_at y (hsub hy)
        apply hgt_near
        · rw [abs_sub_lt_iff]
          have h1 : η ≤ ε / 2 := min_le_left _ _
          constructor <;> linarith [hy.1, hy.2, hε]
        · exact Set.Ioo_subset_Icc_self (hsub hy)
      -- Pivot: `deriv w x₀ = 0` and `deriv w` continuous at `x₀`.
      have hmax_loc : IsLocalMax w x₀ := by
        have hnhds : Set.Icc (0:ℝ) 1 ∈ nhds x₀ := Icc_mem_nhds h0x hx1
        exact Filter.eventually_of_mem hnhds (fun y hy => hx₀_max hy)
      have hderiv0 : deriv w x₀ = 0 := hmax_loc.deriv_eq_zero
      have hpivot : Filter.Tendsto (deriv w) (nhdsWithin x₀ (Set.Ioi x₀))
          (nhds 0) := by
        rw [← hderiv0]
        exact ((hd2 x₀ hx₀_in).continuousAt.tendsto).mono_left
          nhdsWithin_le_nhds
      have hdpos := deriv_pos_right_of_deriv2_pos_of_pivot hη
        (fun y hy => hd2 y (hsub hy)) hd2pos hpivot
      -- `w` strictly increases on `[x₀, x₀ + η/2]` — contradiction.
      have hicc_sub : Set.Icc x₀ (x₀ + η / 2) ⊆ Set.Icc (0:ℝ) 1 := by
        intro y hy
        have h1 : η ≤ (1 - x₀) / 2 := min_le_right _ _
        exact ⟨le_trans hx₀_mem.1 hy.1, by linarith [hy.2]⟩
      have hmono_w : StrictMonoOn w (Set.Icc x₀ (x₀ + η / 2)) := by
        apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
          (hcont.mono hicc_sub)
        intro y hy
        rw [interior_Icc] at hy
        exact hdpos y ⟨hy.1, by linarith [hy.2]⟩
      have hlt : w x₀ < w (x₀ + η / 2) :=
        hmono_w (Set.left_mem_Icc.mpr (by linarith))
          (Set.right_mem_Icc.mpr (by linarith)) (by linarith)
      have hge : w (x₀ + η / 2) ≤ w x₀ :=
        hx₀_max (hicc_sub (Set.right_mem_Icc.mpr (by linarith)))
      linarith
    · -- Argmax at the RIGHT endpoint `x₀ = 1`.
      subst hx1
      set η : ℝ := min (ε / 2) ((1:ℝ) / 2) with hη_def
      have hη : 0 < η := lt_min (by linarith) (by norm_num)
      have hsub : Set.Ioo (1 - η) 1 ⊆ Set.Ioo (0:ℝ) 1 := by
        intro y hy
        have h1 : η ≤ (1:ℝ) / 2 := min_le_right _ _
        exact ⟨by linarith [hy.1], hy.2⟩
      have hd2pos : ∀ y ∈ Set.Ioo (1 - η) 1, 0 < deriv (deriv w) y := by
        intro y hy
        apply hpos_at y (hsub hy)
        apply hgt_near
        · rw [abs_sub_lt_iff]
          have h1 : η ≤ ε / 2 := min_le_left _ _
          constructor <;> linarith [hy.1, hy.2, hε]
        · exact Set.Ioo_subset_Icc_self (hsub hy)
      have hdneg := deriv_neg_left_of_deriv2_pos_of_pivot hη
        (fun y hy => hd2 y (hsub hy)) hd2pos hNeu1
      -- `w` strictly decreases on `[1 − η/2, 1]` — contradiction.
      have hicc_sub : Set.Icc (1 - η / 2) 1 ⊆ Set.Icc (0:ℝ) 1 := by
        intro y hy
        have h1 : η ≤ (1:ℝ) / 2 := min_le_right _ _
        exact ⟨by linarith [hy.1], hy.2⟩
      have hanti_w : StrictAntiOn w (Set.Icc (1 - η / 2) 1) := by
        apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
          (hcont.mono hicc_sub)
        intro y hy
        rw [interior_Icc] at hy
        exact hdneg y ⟨by linarith [hy.1], hy.2⟩
      have hlt : w 1 < w (1 - η / 2) :=
        hanti_w (Set.left_mem_Icc.mpr (by linarith))
          (Set.right_mem_Icc.mpr (by linarith)) (by linarith)
      have hge : w (1 - η / 2) ≤ w 1 :=
        hx₀_max (hicc_sub (Set.left_mem_Icc.mpr (by linarith)))
      linarith
  · -- Argmax at the LEFT endpoint `x₀ = 0`.
    have h0x' : x₀ = 0 := h0x.symm
    subst h0x'
    set η : ℝ := min (ε / 2) ((1:ℝ) / 2) with hη_def
    have hη : 0 < η := lt_min (by linarith) (by norm_num)
    have hsub : Set.Ioo (0:ℝ) (0 + η) ⊆ Set.Ioo (0:ℝ) 1 := by
      intro y hy
      have h1 : η ≤ (1:ℝ) / 2 := min_le_right _ _
      exact ⟨hy.1, by linarith [hy.2]⟩
    have hd2pos : ∀ y ∈ Set.Ioo (0:ℝ) (0 + η), 0 < deriv (deriv w) y := by
      intro y hy
      apply hpos_at y (hsub hy)
      apply hgt_near
      · rw [abs_sub_lt_iff]
        have h1 : η ≤ ε / 2 := min_le_left _ _
        constructor <;> linarith [hy.1, hy.2, hε]
      · exact Set.Ioo_subset_Icc_self (hsub hy)
    have hdpos := deriv_pos_right_of_deriv2_pos_of_pivot hη
      (fun y hy => hd2 y (hsub hy)) hd2pos hNeu0
    have hicc_sub : Set.Icc (0:ℝ) (0 + η / 2) ⊆ Set.Icc (0:ℝ) 1 := by
      intro y hy
      have h1 : η ≤ (1:ℝ) / 2 := min_le_right _ _
      exact ⟨hy.1, by linarith [hy.2]⟩
    have hmono_w : StrictMonoOn w (Set.Icc (0:ℝ) (0 + η / 2)) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
        (hcont.mono hicc_sub)
      intro y hy
      rw [interior_Icc] at hy
      exact hdpos y ⟨hy.1, by linarith [hy.2]⟩
    have hlt : w 0 < w (0 + η / 2) :=
      hmono_w (Set.left_mem_Icc.mpr (by linarith))
        (Set.right_mem_Icc.mpr (by linarith)) (by linarith)
    have hge : w (0 + η / 2) ≤ w 0 :=
      hx₀_max (hicc_sub (Set.right_mem_Icc.mpr (by linarith)))
    linarith

/-! ## Phase A(iv): the gradient bound from the Neumann endpoint

`w'(y) = lim_{z→0⁺} (w'(y) − w'(z)) = lim ∫_z^y w''`, and the integrand
is bounded by `μ·Mw + B`, so `|w'| ≤ μ·Mw + B` on the interior. -/

theorem elliptic_deriv_bound
    {w Src : ℝ → ℝ} {μ B Mw : ℝ} (hμ : 0 ≤ μ) (hB : 0 ≤ B) (hMw : 0 ≤ Mw)
    (hd2 : ∀ y ∈ Set.Ioo (0:ℝ) 1, DifferentiableAt ℝ (deriv w) y)
    (hd2c : ContinuousOn (deriv (deriv w)) (Set.Ioo (0:ℝ) 1))
    (hPDE : ∀ y ∈ Set.Ioo (0:ℝ) 1, deriv (deriv w) y = μ * w y - Src y)
    (hSrc : ∀ y ∈ Set.Ioo (0:ℝ) 1, |Src y| ≤ B)
    (hw_bd : ∀ y ∈ Set.Ioo (0:ℝ) 1, |w y| ≤ Mw)
    (hNeu0 : Filter.Tendsto (deriv w) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    ∀ y ∈ Set.Ioo (0:ℝ) 1, |deriv w y| ≤ μ * Mw + B := by
  intro y hy
  -- The second derivative is bounded on the interior.
  have hbd2 : ∀ r ∈ Set.Ioo (0:ℝ) 1, |deriv (deriv w) r| ≤ μ * Mw + B := by
    intro r hr
    rw [hPDE r hr]
    calc |μ * w r - Src r| = |μ * w r + -(Src r)| := by ring_nf
      _ ≤ |μ * w r| + |-(Src r)| := abs_add_le _ _
      _ = |μ * w r| + |Src r| := by rw [abs_neg]
      _ ≤ μ * Mw + B := by
          rw [abs_mul, abs_of_nonneg hμ]
          exact add_le_add
            (mul_le_mul_of_nonneg_left (hw_bd r hr) hμ) (hSrc r hr)
  -- FTC on `[z, y] ⊂ (0,1)`: `w'(y) − w'(z) = ∫_z^y w''`.
  have hFTC : ∀ z ∈ Set.Ioo (0:ℝ) y,
      |deriv w y - deriv w z| ≤ μ * Mw + B := by
    intro z hz
    have hzy : z < y := hz.2
    have hsub : Set.uIcc z y ⊆ Set.Ioo (0:ℝ) 1 := by
      rw [Set.uIcc_of_le hzy.le]
      intro r hr
      exact ⟨lt_of_lt_of_le hz.1 hr.1, lt_of_le_of_lt hr.2 hy.2⟩
    have hderiv : ∀ r ∈ Set.uIcc z y,
        HasDerivAt (deriv w) (deriv (deriv w) r) r := fun r hr =>
      (hd2 r (hsub hr)).hasDerivAt
    have hint : IntervalIntegrable (deriv (deriv w)) MeasureTheory.volume z y := by
      apply ContinuousOn.intervalIntegrable
      exact hd2c.mono hsub
    have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    rw [← heq]
    calc |∫ r in z..y, deriv (deriv w) r|
        ≤ (μ * Mw + B) * |y - z| := by
          rw [← Real.norm_eq_abs]
          apply intervalIntegral.norm_integral_le_of_norm_le_const
          intro r hr
          rw [Set.uIoc_of_le hzy.le] at hr
          rw [Real.norm_eq_abs]
          exact hbd2 r ⟨lt_trans hz.1 hr.1, lt_of_le_of_lt hr.2 hy.2⟩
      _ ≤ (μ * Mw + B) * 1 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [abs_of_pos (sub_pos.mpr hzy)]
          linarith [hz.1, hy.2]
      _ = μ * Mw + B := mul_one _
  -- Send `z → 0⁺` along the Neumann pivot.
  have hclose : ∀ z ∈ Set.Ioo (0:ℝ) y,
      |deriv w y| ≤ μ * Mw + B + |deriv w z| := by
    intro z hz
    calc |deriv w y| = |(deriv w y - deriv w z) + deriv w z| := by ring_nf
      _ ≤ |deriv w y - deriv w z| + |deriv w z| := abs_add_le _ _
      _ ≤ μ * Mw + B + |deriv w z| := by linarith [hFTC z hz]
  have htends : Filter.Tendsto (fun z => μ * Mw + B + |deriv w z|)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (μ * Mw + B + |(0:ℝ)|)) :=
    (tendsto_const_nhds.add (hNeu0.abs))
  have hlim : |deriv w y| ≤ μ * Mw + B + |(0:ℝ)| := by
    apply ge_of_tendsto htends
    filter_upwards [Ioo_mem_nhdsGT hy.1] with z hz
    exact hclose z hz
  simpa using hlim

/-! ## Phase B1: continuity of the spatial-minimum trajectory

`m(t) := sInf (F t '' [0,1])` is continuous in `t` whenever `F` is
jointly continuous on a compact slab — by Heine–Cantor uniform
continuity, `|m(t) − m(s)| ≤ sup_x |F(t,x) − F(s,x)|`. -/

/-- The spatial minimum is attained and bounds slices from below. -/
theorem sliceMin_isMinOn {F : ℝ → ℝ → ℝ} {a b t : ℝ}
    (ht : t ∈ Set.Icc a b)
    (hF : ContinuousOn (Function.uncurry F)
      (Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1)) :
    ∃ x ∈ Set.Icc (0:ℝ) 1,
      F t x = sInf (F t '' Set.Icc (0:ℝ) 1) := by
  have hslice : ContinuousOn (F t) (Set.Icc (0:ℝ) 1) := by
    intro x hx
    have := hF (t, x) ⟨ht, hx⟩
    exact (this.comp (Continuous.continuousWithinAt (by fun_prop))
      (fun y hy => ⟨ht, hy⟩) : ContinuousWithinAt (fun y => F t y) _ x)
  have himg : IsCompact (F t '' Set.Icc (0:ℝ) 1) :=
    isCompact_Icc.image_of_continuousOn hslice
  have hne : (F t '' Set.Icc (0:ℝ) 1).Nonempty :=
    ⟨F t 0, Set.mem_image_of_mem _ (Set.left_mem_Icc.mpr zero_le_one)⟩
  obtain ⟨x, hx, hxeq⟩ := himg.sInf_mem hne
  exact ⟨x, hx, hxeq⟩

set_option maxHeartbeats 800000 in
/-- **Continuity of the minimum trajectory** on a compact slab. -/
theorem sliceMin_continuousOn {F : ℝ → ℝ → ℝ} {a b : ℝ}
    (hF : ContinuousOn (Function.uncurry F)
      (Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1)) :
    ContinuousOn (fun t => sInf (F t '' Set.Icc (0:ℝ) 1))
      (Set.Icc a b) := by
  -- Uniform continuity on the compact slab.
  have hcpt : IsCompact (Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  have huc := hcpt.uniformContinuousOn_of_continuous hF
  rw [Metric.uniformContinuousOn_iff] at huc
  rw [Metric.continuousOn_iff]
  intro t ht ε hε
  obtain ⟨δ, hδ, hmod⟩ := huc (ε / 2) (by linarith)
  refine ⟨δ, hδ, ?_⟩
  intro s hs hst
  -- One-sided estimate `m s ≤ m t + ε/2` (and symmetrically).
  have hkey : ∀ r r' : ℝ, r ∈ Set.Icc a b → r' ∈ Set.Icc a b →
      dist r r' < δ →
      sInf (F r '' Set.Icc (0:ℝ) 1)
        ≤ sInf (F r' '' Set.Icc (0:ℝ) 1) + ε / 2 := by
    intro r r' hr hr' hrr'
    obtain ⟨x', hx', hx'eq⟩ := sliceMin_isMinOn hr' hF
    have hbdd : BddBelow (F r '' Set.Icc (0:ℝ) 1) := by
      have hslice : ContinuousOn (F r) (Set.Icc (0:ℝ) 1) := by
        intro x hx
        exact ((hF (r, x) ⟨hr, hx⟩).comp
          (Continuous.continuousWithinAt (by fun_prop))
          (fun y hy => ⟨hr, hy⟩) :
            ContinuousWithinAt (fun y => F r y) _ x)
      exact (isCompact_Icc.image_of_continuousOn hslice).bddBelow
    have hmem : F r x' ∈ F r '' Set.Icc (0:ℝ) 1 :=
      Set.mem_image_of_mem _ hx'
    have h1 : sInf (F r '' Set.Icc (0:ℝ) 1) ≤ F r x' := csInf_le hbdd hmem
    have h2 : dist (F r x') (F r' x') < ε / 2 := by
      have := hmod (r, x') ⟨hr, hx'⟩ (r', x') ⟨hr', hx'⟩ ?_
      · simpa [Function.uncurry] using this
      · rw [Prod.dist_eq]
        simp only [dist_self]
        rw [max_eq_left dist_nonneg]
        exact hrr'
    rw [Real.dist_eq] at h2
    have h3 : F r x' ≤ F r' x' + ε / 2 := by
      have := (abs_lt.mp h2).2
      linarith
    rw [← hx'eq]
    linarith
  have hfwd := hkey s t hs ht hst
  have hbwd := hkey t s ht hs (by rwa [dist_comm])
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor <;> linarith

end ShenWork.MinPersistenceAtoms
