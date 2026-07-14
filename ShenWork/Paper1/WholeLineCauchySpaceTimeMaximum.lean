import ShenWork.Paper1.WholeLineCauchyUniformRestart

open Filter Topology MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Space-time approximate maxima on a whole-line slab

The nonlocal Cauchy ceiling is tested at points approaching the supremum of a
bounded space-time slab.  A quadratic spatial penalty forces attainment on a
finite rectangle, while compactness in time gives the correct one-sided sign
of the time derivative.  The output retains explicit small first- and second-
spatial derivative errors.
-/

/-- Values assumed by a trajectory on the closed whole-line slab `[0,T]`. -/
def wholeLineSlabValues (T : ℝ) (u : ℝ → ℝ → ℝ) : Set ℝ :=
  {a | ∃ t ∈ Set.Icc (0 : ℝ) T, ∃ x : ℝ, u t x = a}

/-- Supremum of all values on a closed whole-line slab. -/
def wholeLineSlabSup (T : ℝ) (u : ℝ → ℝ → ℝ) : ℝ :=
  sSup (wholeLineSlabValues T u)

theorem wholeLineSlabValues_nonempty
    {T : ℝ} (hT : 0 ≤ T) (u : ℝ → ℝ → ℝ) :
    (wholeLineSlabValues T u).Nonempty := by
  exact ⟨u 0 0, 0, ⟨le_rfl, hT⟩, 0, rfl⟩

theorem wholeLineSlabValues_bddAbove
    {T A : ℝ} {u : ℝ → ℝ → ℝ}
    (hupper : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, u t x ≤ A) :
    BddAbove (wholeLineSlabValues T u) := by
  refine ⟨A, ?_⟩
  rintro a ⟨t, ht, x, rfl⟩
  exact hupper t ht x

theorem le_wholeLineSlabSup
    {T A : ℝ} {u : ℝ → ℝ → ℝ}
    (_hT : 0 ≤ T)
    (hupper : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, u t x ≤ A)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (x : ℝ) :
    u t x ≤ wholeLineSlabSup T u := by
  exact le_csSup (wholeLineSlabValues_bddAbove hupper) ⟨t, ht, x, rfl⟩

theorem wholeLineSlabSup_le
    {T A : ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0 ≤ T)
    (hupper : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, u t x ≤ A) :
    wholeLineSlabSup T u ≤ A := by
  exact csSup_le (wholeLineSlabValues_nonempty hT u) (by
    rintro a ⟨t, ht, x, rfl⟩
    exact hupper t ht x)

private lemma time_deriv_nonneg_at_Icc_max
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

private lemma second_deriv_nonpos_of_localMax
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
-- The coercive maximum construction and its derivative bookkeeping elaborate
-- one large dependent expression; the proof itself has no unbounded search.
/-- A slab supremum separated from the initial ceiling produces an interior
positive-time almost-maximizer with controlled spatial derivative errors.
The terminal time is allowed; callers apply the lemma on a shorter slab lying
strictly inside their classical-solution horizon. -/
theorem exists_wholeLineSlab_approx_max_deriv_data
    {T C A delta rho : ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0 < T) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hcont : Continuous (fun q : ℝ × ℝ => u q.1 q.2))
    (hupper : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, u t x ≤ A)
    (hinit : ∀ x, u 0 x ≤ C)
    (hgap : C + 2 * delta < wholeLineSlabSup T u)
    (htime : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun s : ℝ => u s x)
        (deriv (fun s : ℝ => u s x) t) t)
    (hspace1 : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => u t y)
        (deriv (fun y : ℝ => u t y) x) x)
    (hspace2 : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => deriv (fun z : ℝ => u t z) y)
        (deriv (fun y : ℝ => deriv (fun z : ℝ => u t z) y) x) x) :
    ∃ t ∈ Set.Ioc (0 : ℝ) T, ∃ x : ℝ,
      wholeLineSlabSup T u - 2 * delta < u t x ∧
        0 ≤ deriv (fun s : ℝ => u s x) t ∧
        |deriv (fun y : ℝ => u t y) x| < rho ∧
        deriv (fun y : ℝ => deriv (fun z : ℝ => u t z) y) x < rho := by
  let L : ℝ := wholeLineSlabSup T u
  have hne : (wholeLineSlabValues T u).Nonempty :=
    wholeLineSlabValues_nonempty hT.le u
  have hbdd : BddAbove (wholeLineSlabValues T u) :=
    wholeLineSlabValues_bddAbove hupper
  have hLA : L ≤ A := wholeLineSlabSup_le hT.le hupper
  have hnear : L - delta < L := by linarith
  obtain ⟨a, ⟨s, hs, y, hay⟩, ha⟩ :=
    exists_lt_of_lt_csSup hne (show L - delta < sSup
      (wholeLineSlabValues T u) by
        change L - delta < L
        exact hnear)
  have husy : L - delta < u s y := by simpa [← hay] using ha
  let D : ℝ := A - C + 2 * delta + y ^ 2 + 1
  have hD : 0 < D := by
    dsimp [D]
    nlinarith [hgap, hLA, sq_nonneg y]
  let eps : ℝ :=
    min (delta / (y ^ 2 + 1))
      (min (rho / 2) (rho ^ 2 / (4 * D))) / 2
  have hyden : 0 < y ^ 2 + 1 := by positivity
  have hrhosq : 0 < rho ^ 2 := sq_pos_of_pos hrho
  have heps : 0 < eps := by
    dsimp [eps]
    positivity
  have hepsDelta : eps * (y ^ 2 + 1) < delta := by
    have hle : min (delta / (y ^ 2 + 1))
        (min (rho / 2) (rho ^ 2 / (4 * D))) ≤
          delta / (y ^ 2 + 1) := min_le_left _ _
    have hlt : eps < delta / (y ^ 2 + 1) := by
      dsimp [eps]
      nlinarith [div_pos hdelta hyden]
    exact (lt_div_iff₀ hyden).mp hlt
  have htwoEps : 2 * eps < rho := by
    have hle : min (delta / (y ^ 2 + 1))
        (min (rho / 2) (rho ^ 2 / (4 * D))) ≤ rho / 2 :=
      (min_le_right _ _).trans (min_le_left _ _)
    dsimp [eps]
    nlinarith
  have hfourEpsD : 4 * eps * D < rho ^ 2 := by
    have hle : min (delta / (y ^ 2 + 1))
        (min (rho / 2) (rho ^ 2 / (4 * D))) ≤ rho ^ 2 / (4 * D) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hlt : eps < rho ^ 2 / (4 * D) := by
      dsimp [eps]
      nlinarith [div_pos hrhosq (by positivity : 0 < 4 * D)]
    nlinarith [(lt_div_iff₀ (by positivity : 0 < 4 * D)).mp hlt]
  have href : L - 2 * delta < u s y - eps * y ^ 2 := by
    have hepsy : eps * y ^ 2 < delta := by
      have hyle : y ^ 2 ≤ y ^ 2 + 1 := by linarith
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hyle heps.le) hepsDelta
    linarith
  let R : ℝ :=
    max (|y| + 1) (Real.sqrt ((A - (L - 2 * delta)) / eps + 1) + 1)
  have hAL : 0 < A - (L - 2 * delta) := by
    nlinarith [hLA, hdelta]
  have hrootArg : 0 ≤ (A - (L - 2 * delta)) / eps + 1 := by positivity
  have hR : 0 < R :=
    lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hyR : |y| < R := by
    linarith [le_max_left (|y| + 1)
      (Real.sqrt ((A - (L - 2 * delta)) / eps + 1) + 1)]
  have hRlarge : A - eps * R ^ 2 < L - 2 * delta := by
    have hsqrtR : Real.sqrt ((A - (L - 2 * delta)) / eps + 1) < R := by
      linarith [le_max_right (|y| + 1)
        (Real.sqrt ((A - (L - 2 * delta)) / eps + 1) + 1)]
    have hargRsq : (A - (L - 2 * delta)) / eps + 1 < R ^ 2 := by
      nlinarith [Real.sq_sqrt hrootArg,
        Real.sqrt_nonneg ((A - (L - 2 * delta)) / eps + 1), hsqrtR, hR]
    have hmul := mul_lt_mul_of_pos_left hargRsq heps
    have hcancel : eps * ((A - (L - 2 * delta)) / eps) =
        A - (L - 2 * delta) := by field_simp [ne_of_gt heps]
    rw [mul_add, hcancel] at hmul
    nlinarith
  let K : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) T ×ˢ Set.Icc (-R) R
  have hKcompact : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKne : K.Nonempty := by
    refine ⟨(0, 0), ⟨⟨le_rfl, hT.le⟩, ?_⟩⟩
    exact ⟨by linarith [hR], hR.le⟩
  have hgcont : ContinuousOn
      (fun q : ℝ × ℝ => u q.1 q.2 - eps * q.2 ^ 2) K :=
    hcont.sub (by fun_prop) |>.continuousOn
  obtain ⟨q, hqK, hqmax⟩ := hKcompact.exists_isMaxOn hKne hgcont
  have hsyK : (s, y) ∈ K := by
    exact ⟨hs, ⟨le_of_lt (abs_lt.mp hyR).1, le_of_lt (abs_lt.mp hyR).2⟩⟩
  have hqref : L - 2 * delta < u q.1 q.2 - eps * q.2 ^ 2 :=
    href.trans_le (hqmax hsyK)
  rcases q with ⟨t₀, x₀⟩
  have ht₀pos : 0 < t₀ := by
    by_contra hnot
    have ht₀zero : t₀ = 0 := le_antisymm (le_of_not_gt hnot) hqK.1.1
    have hbarInit : u t₀ x₀ - eps * x₀ ^ 2 ≤ C := by
      rw [ht₀zero]
      nlinarith [hinit x₀, mul_nonneg heps.le (sq_nonneg x₀)]
    have hCL : C < L - 2 * delta := by linarith [hgap]
    linarith
  have ht₀ : t₀ ∈ Set.Ioc (0 : ℝ) T := ⟨ht₀pos, hqK.1.2⟩
  have hx₀neR : x₀ ≠ R := by
    intro hx
    have hside := hupper t₀ hqK.1 R
    rw [hx] at hqref
    linarith [hRlarge]
  have hx₀neNegR : x₀ ≠ -R := by
    intro hx
    have hside := hupper t₀ hqK.1 (-R)
    rw [hx, neg_sq] at hqref
    linarith [hRlarge]
  have hx₀ : x₀ ∈ Set.Ioo (-R) R :=
    ⟨lt_of_le_of_ne hqK.2.1 (Ne.symm hx₀neNegR),
      lt_of_le_of_ne hqK.2.2 hx₀neR⟩
  have huclose : L - 2 * delta < u t₀ x₀ := by
    nlinarith [mul_nonneg heps.le (sq_nonneg x₀)]
  have htimeMax : IsMaxOn (fun t : ℝ => u t x₀ - eps * x₀ ^ 2)
      (Set.Icc (0 : ℝ) T) t₀ := by
    intro t ht
    exact @hqmax (t, x₀) ⟨ht, hqK.2⟩
  have hut := htime (t := t₀) (x := x₀) ht₀
  have hutNonneg : 0 ≤ deriv (fun t : ℝ => u t x₀) t₀ := by
    have hder : HasDerivAt (fun t : ℝ => u t x₀ - eps * x₀ ^ 2)
        (deriv (fun t : ℝ => u t x₀) t₀) t₀ := by
      simpa using hut.sub_const (eps * x₀ ^ 2)
    exact time_deriv_nonneg_at_Icc_max hqK.1 ht₀pos hder htimeMax
  have hspaceMaxOn : IsMaxOn (fun x : ℝ => u t₀ x - eps * x ^ 2)
      (Set.Icc (-R) R) x₀ := by
    intro x hx
    exact @hqmax (t₀, x) ⟨hqK.1, hx⟩
  have hspaceNhds : Set.Icc (-R) R ∈ nhds x₀ := by
    rw [← mem_interior_iff_mem_nhds, interior_Icc]
    exact hx₀
  have hspaceLocal : IsLocalMax (fun x : ℝ => u t₀ x - eps * x ^ 2) x₀ :=
    hspaceMaxOn.isLocalMax hspaceNhds
  have hux := hspace1 (t := t₀) (x := x₀) ht₀
  have hquad : HasDerivAt (fun x : ℝ => eps * x ^ 2) (2 * eps * x₀) x₀ := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      ((hasDerivAt_id x₀).pow 2).const_mul eps
  have huxEq : deriv (fun x : ℝ => u t₀ x) x₀ = 2 * eps * x₀ := by
    have hzero : deriv (fun x : ℝ => u t₀ x - eps * x ^ 2) x₀ = 0 :=
      hspaceLocal.deriv_eq_zero
    have hderivEq : deriv (fun x : ℝ => u t₀ x - eps * x ^ 2) x₀ =
        deriv (fun x : ℝ => u t₀ x) x₀ - 2 * eps * x₀ := by
      simpa only [Pi.sub_apply] using (hux.sub hquad).deriv
    rw [hderivEq] at hzero
    linarith
  have hepsx : eps * x₀ ^ 2 < D := by
    have huA := hupper t₀ hqK.1 x₀
    dsimp [D]
    nlinarith [hqref, hgap]
  have huxSq : (2 * eps * x₀) ^ 2 < rho ^ 2 := by
    have hmul : 4 * eps * (eps * x₀ ^ 2) < 4 * eps * D :=
      mul_lt_mul_of_pos_left hepsx (by positivity)
    calc
      (2 * eps * x₀) ^ 2 = 4 * eps * (eps * x₀ ^ 2) := by ring
      _ < 4 * eps * D := hmul
      _ < rho ^ 2 := hfourEpsD
  have huxAbs : |deriv (fun x : ℝ => u t₀ x) x₀| < rho := by
    rw [huxEq]
    exact abs_lt_of_sq_lt_sq huxSq hrho.le
  let f : ℝ → ℝ := fun x => u t₀ x - eps * x ^ 2
  have hfcont : ContinuousAt f x₀ := by
    have hslice : Continuous (fun x : ℝ => u t₀ x) :=
      hcont.comp (continuous_const.prodMk continuous_id)
    exact hslice.continuousAt.sub (by fun_prop)
  have hfsecond : deriv (deriv f) x₀ ≤ 0 :=
    second_deriv_nonpos_of_localMax hspaceLocal hfcont
  have hderivEvent : deriv f =ᶠ[nhds x₀]
      (fun x => deriv (fun y : ℝ => u t₀ y) x - 2 * eps * x) := by
    filter_upwards with x
    have hxder := hspace1 (t := t₀) (x := x) ht₀
    have hxquad : HasDerivAt (fun y : ℝ => eps * y ^ 2) (2 * eps * x) x := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        ((hasDerivAt_id x).pow 2).const_mul eps
    exact (hxder.sub hxquad).deriv
  have hlin : HasDerivAt (fun x : ℝ => 2 * eps * x) (2 * eps) x₀ := by
    simpa [mul_assoc] using (hasDerivAt_id x₀).const_mul (2 * eps)
  have hright := (hspace2 (t := t₀) (x := x₀) ht₀).sub hlin
  have hsecondEq : deriv (deriv f) x₀ =
      deriv (fun x : ℝ => deriv (fun y : ℝ => u t₀ y) x) x₀ - 2 * eps := by
    rw [hderivEvent.deriv_eq]
    exact hright.deriv
  have huxx : deriv (fun x : ℝ => deriv (fun y : ℝ => u t₀ y) x) x₀ < rho := by
    rw [hsecondEq] at hfsecond
    linarith [htwoEps]
  exact ⟨t₀, ht₀, x₀, huclose, hutNonneg, huxAbs, huxx⟩

/-- Abstract scalar closure of the approximate-maximum argument.  If the PDE
is bounded above by `u_xx + K |u_x| + G(u)` and `G` is strictly negative at
every slab supremum above the initial ceiling, then the slab never crosses
that ceiling. -/
theorem wholeLineSlabSup_le_of_scalar_pde
    {T C A K : ℝ} {u : ℝ → ℝ → ℝ} {G : ℝ → ℝ}
    (hT : 0 < T) (hK : 0 ≤ K)
    (hcont : Continuous (fun q : ℝ × ℝ => u q.1 q.2))
    (hupper : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, u t x ≤ A)
    (hinit : ∀ x, u 0 x ≤ C)
    (hGcont : Continuous G)
    (hGstrict : ∀ L, C < L → L ≤ A → G L < 0)
    (htime : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun s : ℝ => u s x)
        (deriv (fun s : ℝ => u s x) t) t)
    (hspace1 : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => u t y)
        (deriv (fun y : ℝ => u t y) x) x)
    (hspace2 : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => deriv (fun z : ℝ => u t z) y)
        (deriv (fun y : ℝ => deriv (fun z : ℝ => u t z) y) x) x)
    (hpde : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      deriv (fun s : ℝ => u s x) t ≤
        deriv (fun y : ℝ => deriv (fun z : ℝ => u t z) y) x +
          K * |deriv (fun y : ℝ => u t y) x| + G (u t x)) :
    wholeLineSlabSup T u ≤ C := by
  let L : ℝ := wholeLineSlabSup T u
  have hLA : L ≤ A := wholeLineSlabSup_le hT.le hupper
  by_contra hnot
  have hCL : C < L := lt_of_not_ge hnot
  have hGL : G L < 0 := hGstrict L hCL hLA
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
  obtain ⟨t, ht, x, huclose, hut, hux, huxx⟩ :=
    exists_wholeLineSlab_approx_max_deriv_data
      hT hdelta hrho hcont hupper hinit hgap htime hspace1 hspace2
  have huL : u t x ≤ L :=
    le_wholeLineSlabSup hT.le hupper ⟨ht.1.le, ht.2⟩ x
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
    have h := (lt_of_le_of_lt (le_abs_self (G (u t x) - G L)) hGnear)
    linarith
  have hpdeAt := hpde (t := t) (x := x) ht
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

section WholeLineCauchySpaceTimeMaximumAxiomAudit

#print axioms wholeLineSlabValues_nonempty
#print axioms wholeLineSlabValues_bddAbove
#print axioms le_wholeLineSlabSup
#print axioms wholeLineSlabSup_le
#print axioms exists_wholeLineSlab_approx_max_deriv_data
#print axioms wholeLineSlabSup_le_of_scalar_pde

end WholeLineCauchySpaceTimeMaximumAxiomAudit

end ShenWork.Paper1
