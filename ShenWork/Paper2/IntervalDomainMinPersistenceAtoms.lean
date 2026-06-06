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

end ShenWork.MinPersistenceAtoms
