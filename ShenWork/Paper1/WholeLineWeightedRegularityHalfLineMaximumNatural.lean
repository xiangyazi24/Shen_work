import ShenWork.Paper1.WholeLineCauchySpaceTimeMaximum

open Filter Topology MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

/-!
# A scalar parabolic maximum principle on a left half-line

The whole-line approximate-maximum argument does not see a lateral boundary.
For the zero-sensitivity left-tail problem we need the corresponding result
on `(-∞, z₀]`: both the initial slice and the fixed right boundary are below
the comparison level.  A quadratic penalty forces a maximum away from
`-∞`; the strict slab gap forces it away from the right boundary.
-/

/-- Values assumed on the closed left-half-line slab `[0,T] × (-∞,z₀]`. -/
def leftHalfLineSlabValues
    (T z₀ : ℝ) (u : ℝ → ℝ → ℝ) : Set ℝ :=
  {a | ∃ t ∈ Set.Icc (0 : ℝ) T, ∃ x ∈ Set.Iic z₀, u t x = a}

/-- Supremum of the values on a closed left-half-line slab. -/
def leftHalfLineSlabSup
    (T z₀ : ℝ) (u : ℝ → ℝ → ℝ) : ℝ :=
  sSup (leftHalfLineSlabValues T z₀ u)

theorem leftHalfLineSlabValues_nonempty
    {T z₀ : ℝ} (hT : 0 ≤ T) (u : ℝ → ℝ → ℝ) :
    (leftHalfLineSlabValues T z₀ u).Nonempty := by
  exact ⟨u 0 z₀, 0, ⟨le_rfl, hT⟩, z₀,
    Set.mem_Iic.mpr le_rfl, rfl⟩

theorem leftHalfLineSlabValues_bddAbove
    {T z₀ A : ℝ} {u : ℝ → ℝ → ℝ}
    (hupper : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x ∈ Set.Iic z₀,
      u t x ≤ A) :
    BddAbove (leftHalfLineSlabValues T z₀ u) := by
  refine ⟨A, ?_⟩
  rintro a ⟨t, ht, x, hx, rfl⟩
  exact hupper t ht x hx

theorem le_leftHalfLineSlabSup
    {T z₀ A : ℝ} {u : ℝ → ℝ → ℝ}
    (_hT : 0 ≤ T)
    (hupper : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x ∈ Set.Iic z₀,
      u t x ≤ A)
    {t x : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (hx : x ∈ Set.Iic z₀) :
    u t x ≤ leftHalfLineSlabSup T z₀ u := by
  exact le_csSup (leftHalfLineSlabValues_bddAbove hupper)
    ⟨t, ht, x, hx, rfl⟩

theorem leftHalfLineSlabSup_le
    {T z₀ A : ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0 ≤ T)
    (hupper : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x ∈ Set.Iic z₀,
      u t x ≤ A) :
    leftHalfLineSlabSup T z₀ u ≤ A := by
  exact csSup_le (leftHalfLineSlabValues_nonempty hT u) (by
    rintro a ⟨t, ht, x, hx, rfl⟩
    exact hupper t ht x hx)

private lemma time_deriv_nonneg_at_Icc_max_leftHalfLine
    {f : ℝ → ℝ} {S t f' : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) S) (htpos : 0 < t)
    (hder : HasDerivAt f f' t)
    (hmax : IsMaxOn f (Set.Icc (0 : ℝ) S) t) :
    0 ≤ f' := by
  have hS : 0 ≤ S := le_trans htpos.le ht.2
  have hseg : segment ℝ t 0 ⊆ Set.Icc (0 : ℝ) S :=
    (convex_Icc (0 : ℝ) S).segment_subset ht (left_mem_Icc.mpr hS)
  have htan : (0 : ℝ) - t ∈ posTangentConeAt (Set.Icc (0 : ℝ) S) t :=
    sub_mem_posTangentConeAt_of_segment_subset hseg
  have hle :
      (ContinuousLinearMap.toSpanSingleton ℝ f') ((0 : ℝ) - t) ≤ 0 :=
    hmax.localize.hasFDerivWithinAt_nonpos
      hder.hasFDerivAt.hasFDerivWithinAt htan
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at hle
  nlinarith

private lemma second_deriv_nonpos_of_localMax_leftHalfLine
    {f : ℝ → ℝ} {x : ℝ}
    (hmax : IsLocalMax f x) (hcont : ContinuousAt f x) :
    deriv (deriv f) x ≤ 0 := by
  by_contra hpos
  push Not at hpos
  have hd0 : deriv f x = 0 := hmax.deriv_eq_zero
  have hmin : IsLocalMin f x :=
    isLocalMin_of_deriv_deriv_pos hpos hd0 hcont
  have hconst : f =ᶠ[nhds x] (fun _ => f x) :=
    eventuallyEq_of_isMinFilter_of_isMaxFilter hmin hmax
  have hderiv_const : deriv f =ᶠ[nhds x] deriv (fun _ : ℝ => f x) :=
    hconst.deriv
  have hderiv_zero : deriv f =ᶠ[nhds x] (fun _ : ℝ => 0) := by
    refine hderiv_const.trans ?_
    filter_upwards with y using deriv_const y (f x)
  have heq : deriv (deriv f) x = deriv (fun _ : ℝ => 0) x :=
    hderiv_zero.deriv_eq
  rw [heq, deriv_const] at hpos
  exact lt_irrefl 0 hpos

set_option maxHeartbeats 800000 in
-- The coercive compact-rectangle construction has one large dependent term.
/-- If the left-half-line slab supremum lies strictly above both its initial
and lateral-boundary ceiling, there is an interior positive-time
almost-maximizer with controlled spatial derivative errors. -/
theorem exists_leftHalfLineSlab_approx_max_deriv_data
    {T z₀ C A delta rho : ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0 < T) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hcont : Continuous (fun q : ℝ × ℝ => u q.1 q.2))
    (hupper : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x ∈ Set.Iic z₀,
      u t x ≤ A)
    (hinit : ∀ x ∈ Set.Iic z₀, u 0 x ≤ C)
    (hboundary : ∀ t ∈ Set.Icc (0 : ℝ) T, u t z₀ ≤ C)
    (hgap : C + 2 * delta < leftHalfLineSlabSup T z₀ u)
    (htime : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun s : ℝ => u s x)
        (deriv (fun s : ℝ => u s x) t) t)
    (hspace1 : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => u t y)
        (deriv (fun y : ℝ => u t y) x) x)
    (hspace2 : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => deriv (fun z : ℝ => u t z) y)
        (deriv (fun y : ℝ => deriv (fun z : ℝ => u t z) y) x) x) :
    ∃ t ∈ Set.Ioc (0 : ℝ) T, ∃ x ∈ Set.Iio z₀,
      leftHalfLineSlabSup T z₀ u - 2 * delta < u t x ∧
        0 ≤ deriv (fun s : ℝ => u s x) t ∧
        |deriv (fun y : ℝ => u t y) x| < rho ∧
        deriv (fun y : ℝ => deriv (fun z : ℝ => u t z) y) x < rho := by
  let L : ℝ := leftHalfLineSlabSup T z₀ u
  have hne : (leftHalfLineSlabValues T z₀ u).Nonempty :=
    leftHalfLineSlabValues_nonempty hT.le u
  have hbdd : BddAbove (leftHalfLineSlabValues T z₀ u) :=
    leftHalfLineSlabValues_bddAbove hupper
  have hLA : L ≤ A := leftHalfLineSlabSup_le hT.le hupper
  have hnear : L - delta < L := by linarith
  obtain ⟨a, ⟨s, hs, y, hy, hay⟩, ha⟩ :=
    exists_lt_of_lt_csSup hne (show L - delta < sSup
      (leftHalfLineSlabValues T z₀ u) by
        change L - delta < L
        exact hnear)
  have husy : L - delta < u s y := by simpa [← hay] using ha
  let D : ℝ := A - C + 2 * delta + (y - z₀) ^ 2 + 1
  have hD : 0 < D := by
    dsimp [D]
    nlinarith [hgap, hLA, sq_nonneg (y - z₀)]
  let eps : ℝ :=
    min (delta / ((y - z₀) ^ 2 + 1))
      (min (rho / 2) (rho ^ 2 / (4 * D))) / 2
  have hyden : 0 < (y - z₀) ^ 2 + 1 := by positivity
  have hrhosq : 0 < rho ^ 2 := sq_pos_of_pos hrho
  have heps : 0 < eps := by
    dsimp [eps]
    positivity
  have hepsDelta : eps * ((y - z₀) ^ 2 + 1) < delta := by
    have hlt : eps < delta / ((y - z₀) ^ 2 + 1) := by
      dsimp [eps]
      have hle : min (delta / ((y - z₀) ^ 2 + 1))
          (min (rho / 2) (rho ^ 2 / (4 * D))) ≤
            delta / ((y - z₀) ^ 2 + 1) := min_le_left _ _
      nlinarith [div_pos hdelta hyden]
    exact (lt_div_iff₀ hyden).mp hlt
  have htwoEps : 2 * eps < rho := by
    have hle : min (delta / ((y - z₀) ^ 2 + 1))
        (min (rho / 2) (rho ^ 2 / (4 * D))) ≤ rho / 2 :=
      (min_le_right _ _).trans (min_le_left _ _)
    dsimp [eps]
    nlinarith
  have hfourEpsD : 4 * eps * D < rho ^ 2 := by
    have hlt : eps < rho ^ 2 / (4 * D) := by
      dsimp [eps]
      have hle : min (delta / ((y - z₀) ^ 2 + 1))
          (min (rho / 2) (rho ^ 2 / (4 * D))) ≤ rho ^ 2 / (4 * D) :=
        (min_le_right _ _).trans (min_le_right _ _)
      nlinarith [div_pos hrhosq (by positivity : 0 < 4 * D)]
    nlinarith [(lt_div_iff₀ (by positivity : 0 < 4 * D)).mp hlt]
  have href : L - 2 * delta < u s y - eps * (y - z₀) ^ 2 := by
    have hepsy : eps * (y - z₀) ^ 2 < delta := by
      have hyle : (y - z₀) ^ 2 ≤ (y - z₀) ^ 2 + 1 := by linarith
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hyle heps.le) hepsDelta
    linarith
  let R : ℝ :=
    max (|y - z₀| + 1)
      (Real.sqrt ((A - (L - 2 * delta)) / eps + 1) + 1)
  have hAL : 0 < A - (L - 2 * delta) := by
    nlinarith [hLA, hdelta]
  have hrootArg : 0 ≤ (A - (L - 2 * delta)) / eps + 1 := by positivity
  have hR : 0 < R :=
    lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hyR : |y - z₀| < R := by
    linarith [le_max_left (|y - z₀| + 1)
      (Real.sqrt ((A - (L - 2 * delta)) / eps + 1) + 1)]
  have hRlarge : A - eps * R ^ 2 < L - 2 * delta := by
    have hsqrtR : Real.sqrt ((A - (L - 2 * delta)) / eps + 1) < R := by
      linarith [le_max_right (|y - z₀| + 1)
        (Real.sqrt ((A - (L - 2 * delta)) / eps + 1) + 1)]
    have hargRsq : (A - (L - 2 * delta)) / eps + 1 < R ^ 2 := by
      nlinarith [Real.sq_sqrt hrootArg,
        Real.sqrt_nonneg ((A - (L - 2 * delta)) / eps + 1), hsqrtR, hR]
    have hmul := mul_lt_mul_of_pos_left hargRsq heps
    have hcancel : eps * ((A - (L - 2 * delta)) / eps) =
        A - (L - 2 * delta) := by field_simp [ne_of_gt heps]
    rw [mul_add, hcancel] at hmul
    nlinarith
  let K : Set (ℝ × ℝ) :=
    Set.Icc (0 : ℝ) T ×ˢ Set.Icc (z₀ - R) z₀
  have hKcompact : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKne : K.Nonempty := by
    refine ⟨(0, z₀), ⟨⟨le_rfl, hT.le⟩, ?_⟩⟩
    exact ⟨by linarith [hR], le_rfl⟩
  have hgcont : ContinuousOn
      (fun q : ℝ × ℝ => u q.1 q.2 - eps * (q.2 - z₀) ^ 2) K :=
    hcont.sub (by fun_prop) |>.continuousOn
  obtain ⟨q, hqK, hqmax⟩ := hKcompact.exists_isMaxOn hKne hgcont
  have hsyK : (s, y) ∈ K := by
    have hyleft : z₀ - R ≤ y := by
      rw [sub_le_iff_le_add]
      have habs : z₀ - y ≤ |y - z₀| := by
        rw [abs_sub_comm]
        exact le_abs_self _
      linarith
    exact ⟨hs, ⟨hyleft, hy⟩⟩
  have hqref : L - 2 * delta <
      u q.1 q.2 - eps * (q.2 - z₀) ^ 2 :=
    href.trans_le (hqmax hsyK)
  rcases q with ⟨t₀, x₀⟩
  have ht₀pos : 0 < t₀ := by
    by_contra hnot
    have ht₀zero : t₀ = 0 := le_antisymm (le_of_not_gt hnot) hqK.1.1
    have hbarInit : u t₀ x₀ - eps * (x₀ - z₀) ^ 2 ≤ C := by
      rw [ht₀zero]
      nlinarith [hinit x₀ hqK.2.2,
        mul_nonneg heps.le (sq_nonneg (x₀ - z₀))]
    have hCL : C < L - 2 * delta := by linarith [hgap]
    linarith
  have ht₀ : t₀ ∈ Set.Ioc (0 : ℝ) T := ⟨ht₀pos, hqK.1.2⟩
  have hx₀neRight : x₀ ≠ z₀ := by
    intro hx
    have hside := hboundary t₀ hqK.1
    rw [hx, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      mul_zero, sub_zero] at hqref
    linarith [hgap]
  have hx₀neLeft : x₀ ≠ z₀ - R := by
    intro hx
    have hside := hupper t₀ hqK.1 (z₀ - R)
      (Set.mem_Iic.mpr (sub_le_self z₀ hR.le))
    rw [hx] at hqref
    have hsquare : (z₀ - R - z₀) ^ 2 = R ^ 2 := by ring
    rw [hsquare] at hqref
    linarith [hRlarge]
  have hx₀int : x₀ ∈ Set.Ioo (z₀ - R) z₀ :=
    ⟨lt_of_le_of_ne hqK.2.1 (Ne.symm hx₀neLeft),
      lt_of_le_of_ne hqK.2.2 hx₀neRight⟩
  have huclose : L - 2 * delta < u t₀ x₀ := by
    nlinarith [mul_nonneg heps.le (sq_nonneg (x₀ - z₀))]
  have htimeMax : IsMaxOn
      (fun t : ℝ => u t x₀ - eps * (x₀ - z₀) ^ 2)
      (Set.Icc (0 : ℝ) T) t₀ := by
    intro t ht
    exact @hqmax (t, x₀) ⟨ht, hqK.2⟩
  have hut := htime (t := t₀) (x := x₀) ht₀
  have hutNonneg : 0 ≤ deriv (fun t : ℝ => u t x₀) t₀ := by
    have hder : HasDerivAt
        (fun t : ℝ => u t x₀ - eps * (x₀ - z₀) ^ 2)
        (deriv (fun t : ℝ => u t x₀) t₀) t₀ := by
      simpa using hut.sub_const (eps * (x₀ - z₀) ^ 2)
    exact time_deriv_nonneg_at_Icc_max_leftHalfLine
      hqK.1 ht₀pos hder htimeMax
  have hspaceMaxOn : IsMaxOn
      (fun x : ℝ => u t₀ x - eps * (x - z₀) ^ 2)
      (Set.Icc (z₀ - R) z₀) x₀ := by
    intro x hx
    exact @hqmax (t₀, x) ⟨hqK.1, hx⟩
  have hspaceNhds : Set.Icc (z₀ - R) z₀ ∈ nhds x₀ := by
    rw [← mem_interior_iff_mem_nhds, interior_Icc]
    exact hx₀int
  have hspaceLocal : IsLocalMax
      (fun x : ℝ => u t₀ x - eps * (x - z₀) ^ 2) x₀ :=
    hspaceMaxOn.isLocalMax hspaceNhds
  have hux := hspace1 (t := t₀) (x := x₀) ht₀
  have hquad : HasDerivAt
      (fun x : ℝ => eps * (x - z₀) ^ 2)
      (2 * eps * (x₀ - z₀)) x₀ := by
    convert (((hasDerivAt_id x₀).sub_const z₀).pow 2).const_mul eps using 1
    all_goals simp only [id_eq]
    all_goals ring
  have huxEq : deriv (fun x : ℝ => u t₀ x) x₀ =
      2 * eps * (x₀ - z₀) := by
    have hzero : deriv
        (fun x : ℝ => u t₀ x - eps * (x - z₀) ^ 2) x₀ = 0 :=
      hspaceLocal.deriv_eq_zero
    have hderivEq : deriv
        (fun x : ℝ => u t₀ x - eps * (x - z₀) ^ 2) x₀ =
          deriv (fun x : ℝ => u t₀ x) x₀ -
            2 * eps * (x₀ - z₀) := by
      simpa only [Pi.sub_apply] using (hux.sub hquad).deriv
    rw [hderivEq] at hzero
    linarith
  have hepsx : eps * (x₀ - z₀) ^ 2 < D := by
    have huA := hupper t₀ hqK.1 x₀ hqK.2.2
    dsimp [D]
    nlinarith [hqref, hgap]
  have huxSq : (2 * eps * (x₀ - z₀)) ^ 2 < rho ^ 2 := by
    have hmul : 4 * eps * (eps * (x₀ - z₀) ^ 2) < 4 * eps * D :=
      mul_lt_mul_of_pos_left hepsx (by positivity)
    calc
      (2 * eps * (x₀ - z₀)) ^ 2 =
          4 * eps * (eps * (x₀ - z₀) ^ 2) := by ring
      _ < 4 * eps * D := hmul
      _ < rho ^ 2 := hfourEpsD
  have huxAbs : |deriv (fun x : ℝ => u t₀ x) x₀| < rho := by
    rw [huxEq]
    exact abs_lt_of_sq_lt_sq huxSq hrho.le
  let f : ℝ → ℝ := fun x => u t₀ x - eps * (x - z₀) ^ 2
  have hfcont : ContinuousAt f x₀ := by
    have hslice : Continuous (fun x : ℝ => u t₀ x) :=
      hcont.comp (continuous_const.prodMk continuous_id)
    exact hslice.continuousAt.sub (by fun_prop)
  have hfsecond : deriv (deriv f) x₀ ≤ 0 :=
    second_deriv_nonpos_of_localMax_leftHalfLine hspaceLocal hfcont
  have hderivEvent : deriv f =ᶠ[nhds x₀]
      (fun x => deriv (fun y : ℝ => u t₀ y) x -
        2 * eps * (x - z₀)) := by
    filter_upwards with x
    have hxder := hspace1 (t := t₀) (x := x) ht₀
    have hxquad : HasDerivAt
        (fun y : ℝ => eps * (y - z₀) ^ 2)
        (2 * eps * (x - z₀)) x := by
      convert (((hasDerivAt_id x).sub_const z₀).pow 2).const_mul eps using 1
      all_goals simp only [id_eq]
      all_goals ring
    exact (hxder.sub hxquad).deriv
  have hlin : HasDerivAt (fun x : ℝ => 2 * eps * (x - z₀))
      (2 * eps) x₀ := by
    convert ((hasDerivAt_id x₀).sub_const z₀).const_mul (2 * eps) using 1
    ring
  have hright := (hspace2 (t := t₀) (x := x₀) ht₀).sub hlin
  have hsecondEq : deriv (deriv f) x₀ =
      deriv (fun x : ℝ => deriv (fun y : ℝ => u t₀ y) x) x₀ -
        2 * eps := by
    rw [hderivEvent.deriv_eq]
    exact hright.deriv
  have huxx : deriv
      (fun x : ℝ => deriv (fun y : ℝ => u t₀ y) x) x₀ < rho := by
    rw [hsecondEq] at hfsecond
    linarith [htwoEps]
  exact ⟨t₀, ht₀, x₀, hx₀int.2, huclose, hutNonneg, huxAbs, huxx⟩

/-- Scalar parabolic closure on a left half-line.  The initial and right
boundary ceilings are both `C`; a strict negative reaction at any larger
slab supremum prevents crossing. -/
theorem leftHalfLineSlabSup_le_of_scalar_pde
    {T z₀ C A K : ℝ} {u : ℝ → ℝ → ℝ} {G : ℝ → ℝ}
    (hT : 0 < T) (hK : 0 ≤ K)
    (hcont : Continuous (fun q : ℝ × ℝ => u q.1 q.2))
    (hupper : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x ∈ Set.Iic z₀,
      u t x ≤ A)
    (hinit : ∀ x ∈ Set.Iic z₀, u 0 x ≤ C)
    (hboundary : ∀ t ∈ Set.Icc (0 : ℝ) T, u t z₀ ≤ C)
    (hGcont : Continuous G)
    (hGstrict : C < leftHalfLineSlabSup T z₀ u →
      G (leftHalfLineSlabSup T z₀ u) < 0)
    (htime : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun s : ℝ => u s x)
        (deriv (fun s : ℝ => u s x) t) t)
    (hspace1 : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => u t y)
        (deriv (fun y : ℝ => u t y) x) x)
    (hspace2 : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => deriv (fun z : ℝ => u t z) y)
        (deriv (fun y : ℝ => deriv (fun z : ℝ => u t z) y) x) x)
    (hpde : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T → x < z₀ →
      deriv (fun s : ℝ => u s x) t ≤
        deriv (fun y : ℝ => deriv (fun z : ℝ => u t z) y) x +
          K * |deriv (fun y : ℝ => u t y) x| + G (u t x)) :
    leftHalfLineSlabSup T z₀ u ≤ C := by
  let L : ℝ := leftHalfLineSlabSup T z₀ u
  have hLA : L ≤ A := leftHalfLineSlabSup_le hT.le hupper
  by_contra hnot
  have hCL : C < L := lt_of_not_ge hnot
  have hGL : G L < 0 := by
    simpa [L] using hGstrict (by simpa [L] using hCL)
  have hGat : ContinuousAt G L := hGcont.continuousAt
  rw [Metric.continuousAt_iff] at hGat
  obtain ⟨d, hd, hGclose⟩ := hGat (-G L / 2) (by linarith)
  let delta : ℝ := min ((L - C) / 4) (d / 4)
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min (div_pos (sub_pos.mpr hCL) (by norm_num))
      (div_pos hd (by norm_num))
  have hgap : C + 2 * delta < L := by
    have hle : delta ≤ (L - C) / 4 := by
      dsimp [delta]
      exact min_le_left _ _
    linarith
  let rho : ℝ := (-G L) / (4 * (K + 1))
  have hKone : 0 < K + 1 := by linarith
  have hrho : 0 < rho := by
    dsimp [rho]
    exact div_pos (neg_pos.mpr hGL) (mul_pos (by norm_num) hKone)
  obtain ⟨t, ht, x, hx, huclose, hut, hux, huxx⟩ :=
    exists_leftHalfLineSlab_approx_max_deriv_data hT hdelta hrho
      hcont hupper hinit hboundary hgap htime hspace1 hspace2
  have huL : u t x ≤ L :=
    le_leftHalfLineSlabSup hT.le hupper ⟨ht.1.le, ht.2⟩
      (Set.mem_Iic.mpr hx.le)
  have hudist : dist (u t x) L < d := by
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr huL)]
    have hdeltaD : 2 * delta < d := by
      have hle : delta ≤ d / 4 := by
        dsimp [delta]
        exact min_le_right _ _
      linarith
    linarith
  have hGnear := hGclose hudist
  rw [Real.dist_eq] at hGnear
  have hGu : G (u t x) < G L / 2 := by
    have h := lt_of_le_of_lt (le_abs_self (G (u t x) - G L)) hGnear
    linarith
  have hpdeAt := hpde (t := t) (x := x) ht hx
  have hrhoId : (K + 1) * rho = -G L / 4 := by
    dsimp [rho]
    field_simp [ne_of_gt hKone]
  have hRhsNeg :
      deriv (fun y : ℝ => deriv (fun z : ℝ => u t z) y) x +
          K * |deriv (fun y : ℝ => u t y) x| + G (u t x) < 0 := by
    have hKux : K * |deriv (fun y : ℝ => u t y) x| ≤ K * rho :=
      mul_le_mul_of_nonneg_left hux.le hK
    calc
      deriv (fun y : ℝ => deriv (fun z : ℝ => u t z) y) x +
            K * |deriv (fun y : ℝ => u t y) x| + G (u t x)
          < rho + K * rho + G L / 2 := by linarith
      _ = (K + 1) * rho + G L / 2 := by ring
      _ = G L / 4 := by rw [hrhoId]; ring
      _ < 0 := by linarith
  linarith

section AxiomAudit

#print axioms leftHalfLineSlabValues_nonempty
#print axioms le_leftHalfLineSlabSup
#print axioms exists_leftHalfLineSlab_approx_max_deriv_data
#print axioms leftHalfLineSlabSup_le_of_scalar_pde

end AxiomAudit

end ShenWork.Paper1
