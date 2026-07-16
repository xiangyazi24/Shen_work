import ShenWork.Paper1.WavePositivePlateauComparison
import ShenWork.Paper1.WholeLineCauchySpaceTimeMaximum

open Filter Topology Set

noncomputable section

namespace ShenWork.Paper1

/-!
# One-sided second derivative at a plateau splice

At a contact with the constant side of a `C¹` plateau, the smooth evolving
profile has only a one-sided spatial minimum available.  Vanishing first
derivative nevertheless forces its second derivative to be nonnegative.  This
is the splice atom used by the continuous-time plateau comparison.
-/

/-- A `C²` function with a one-sided local minimum on the left and zero first
derivative has nonnegative second derivative at the endpoint. -/
theorem second_deriv_nonneg_of_localMinOn_Iic_of_deriv_eq_zero
    {g : ℝ → ℝ} {X : ℝ}
    (hg : ContDiff ℝ 2 g)
    (hmin : IsLocalMinOn g (Set.Iic X) X)
    (hzero : deriv g X = 0) :
    0 ≤ deriv (deriv g) X := by
  by_contra hnot
  have hsecond : deriv (deriv g) X < 0 := lt_of_not_ge hnot
  have hsign_nhds :=
    eventually_nhdsWithin_sign_eq_of_deriv_neg hsecond hzero
  have hsign_ne : ∀ᶠ y in nhdsWithin X {X}ᶜ,
      SignType.sign (deriv g y) = SignType.sign (X - y) :=
    (nhdsWithin_le_nhds (s := {X}ᶜ)) hsign_nhds
  have hderiv_pos : ∀ᶠ y in nhdsWithin X (Set.Iio X),
      0 < deriv g y := deriv_pos_left_of_sign_deriv hsign_ne
  have hmin_left : ∀ᶠ y in nhdsWithin X (Set.Iio X), g X ≤ g y :=
    (nhdsWithin_mono X Set.Iio_subset_Iic_self) hmin
  have hboth : {y : ℝ | g X ≤ g y ∧ 0 < deriv g y} ∈
      nhdsWithin X (Set.Iio X) := by
    filter_upwards [hmin_left, hderiv_pos] with y hymin hyderiv
    exact ⟨hymin, hyderiv⟩
  obtain ⟨a, haX, ha⟩ :=
    (mem_nhdsLT_iff_exists_Ioo_subset.mp hboth)
  have haX' : a < X := haX
  let b : ℝ := (a + X) / 2
  have hab : a < b := by
    dsimp [b]
    linarith [haX']
  have hbX : b < X := by
    dsimp [b]
    linarith [haX']
  have hbmem : b ∈ Set.Ioo a X := ⟨hab, hbX⟩
  have hbmin : g X ≤ g b := (ha hbmem).1
  have hmono : StrictMonoOn g (Set.Icc b X) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc b X)
    · exact hg.continuous.continuousOn
    · intro y hy
      rw [interior_Icc] at hy
      exact (ha ⟨hab.trans hy.1, hy.2⟩).2
  have hb_lt : g b < g X :=
    hmono (Set.left_mem_Icc.mpr hbX.le) (Set.right_mem_Icc.mpr hbX.le) hbX
  exact (not_lt_of_ge hbmin) hb_lt

private theorem time_deriv_nonneg_at_Icc_max_c1splice
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

private theorem second_deriv_nonpos_of_localMax_c1splice
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

private theorem iteratedDeriv_two_mul_sq_sub
    (eps X x : ℝ) :
    iteratedDeriv 2 (fun y : ℝ => eps * (y - X) ^ 2) x = 2 * eps := by
  rw [iteratedDeriv_const_mul_field eps (fun y : ℝ => (y - X) ^ 2)]
  simp only [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
    iteratedDeriv_zero]
  have hfirst :
      (fun z : ℝ => deriv (fun y : ℝ => (y - X) ^ 2) z) =
        fun z => 2 * (z - X) := by
    funext z
    have hder := (((hasDerivAt_id z).sub_const X).pow 2).deriv
    convert hder using 1 <;> simp [id] <;> ring
  have hsecond : deriv (deriv (fun y : ℝ => (y - X) ^ 2)) x = 2 := by
    have hout := congrArg (fun f : ℝ → ℝ => deriv f x) hfirst
    have hrhs : deriv (fun z : ℝ => 2 * (z - X)) x = 2 := by
      convert (((hasDerivAt_id x).sub_const X).const_mul 2).deriv using 1 <;>
        simp <;> ring
    exact hout.trans hrhs
  rw [hsecond]
  ring

/-- At a penalized contact with the splice, the evolving smooth profile has
zero first derivative and its second derivative is bounded below by the
quadratic penalty.  Only the constant branch of the stationary profile is
used on the left of the splice. -/
theorem smooth_profile_deriv_data_at_C1splice_contact
    {A u : ℝ → ℝ} {X eps : ℝ}
    (hAleft : ∀ x, x ≤ X → A x = A X)
    (hAX : HasDerivAt A 0 X)
    (hu : ContDiff ℝ 2 u)
    (hmax : IsLocalMax (fun x => A x - u x - eps * (x - X) ^ 2) X) :
    deriv u X = 0 ∧ -2 * eps ≤ deriv (deriv u) X := by
  have hu1 : HasDerivAt u (deriv u X) X :=
    (hu.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hpen : HasDerivAt (fun x : ℝ => eps * (x - X) ^ 2) 0 X := by
    convert
      (((hasDerivAt_id X).sub_const X).pow 2).const_mul eps using 1 <;>
      simp [id] <;> ring
  have hcontact_deriv :
      deriv (fun x => A x - u x - eps * (x - X) ^ 2) X =
        -(deriv u X) := by
    have hder := ((hAX.sub hu1).sub hpen).deriv
    simpa only [Pi.sub_apply, zero_sub, sub_zero] using hder
  have huX : deriv u X = 0 := by
    have hzero := hmax.deriv_eq_zero
    rw [hcontact_deriv] at hzero
    linarith
  let g : ℝ → ℝ := fun x => u x + eps * (x - X) ^ 2
  have hg : ContDiff ℝ 2 g := by
    dsimp [g]
    fun_prop
  have hgzero : deriv g X = 0 := by
    have hgder : HasDerivAt g (deriv u X) X := by
      dsimp [g]
      simpa using hu1.add hpen
    rw [hgder.deriv, huX]
  have hmin : IsLocalMinOn g (Set.Iic X) X := by
    filter_upwards [
      (nhdsWithin_le_nhds (s := Set.Iic X)) hmax,
      self_mem_nhdsWithin] with x hxmax hxle
    dsimp [g] at hxmax ⊢
    rw [hAleft x hxle, hAleft X le_rfl] at hxmax
    linarith
  have hgsecond :=
    second_deriv_nonneg_of_localMinOn_Iic_of_deriv_eq_zero hg hmin hgzero
  have hgsecond_eq :
      deriv (deriv g) X = deriv (deriv u) X + 2 * eps := by
    have hiter : iteratedDeriv 2 g X = iteratedDeriv 2 u X + 2 * eps := by
      dsimp [g]
      rw [iteratedDeriv_fun_add (hu.contDiffAt) (by fun_prop)]
      rw [iteratedDeriv_two_mul_sq_sub]
    simpa [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ] using hiter
  rw [hgsecond_eq] at hgsecond
  exact ⟨huX, by linarith⟩

/-- Positive spatial rescaling of the splice-contact estimate.  This is the
form used after the exponential-in-time transform in the comparison proof. -/
theorem smooth_profile_scaled_deriv_data_at_C1splice_contact
    {A u : ℝ → ℝ} {X eps scale : ℝ}
    (hscale : 0 < scale)
    (hAleft : ∀ x, x ≤ X → A x = A X)
    (hAX : HasDerivAt A 0 X)
    (hu : ContDiff ℝ 2 u)
    (hmax : IsLocalMax
      (fun x => scale * (A x - u x) - eps * (x - X) ^ 2) X) :
    deriv u X = 0 ∧ -scale * deriv (deriv u) X ≤ 2 * eps := by
  have hmax' : IsLocalMax
      (fun x => A x - u x - (eps / scale) * (x - X) ^ 2) X := by
    filter_upwards [hmax] with x hx
    have hcancel : (eps / scale) * scale = eps := by
      field_simp [ne_of_gt hscale]
    nlinarith [sq_nonneg (x - X)]
  have hcontact := smooth_profile_deriv_data_at_C1splice_contact
    hAleft hAX hu hmax'
  refine ⟨hcontact.1, ?_⟩
  have hcancel : (eps / scale) * scale = eps := by
    field_simp [ne_of_gt hscale]
  nlinarith [hcontact.2]

set_option maxHeartbeats 800000 in
/-- Space-time almost-maximizer for the difference between a stationary
`C¹` profile with a constant left branch and a spatially `C²` evolution.
Away from the splice it gives the usual two spatial derivative estimates; at
the splice it gives the one-sided replacement needed by the PDE comparison. -/
theorem exists_wholeLineSlab_approx_max_deriv_data_C1splice
    {T C B delta rho X : ℝ} {A : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    {scale : ℝ → ℝ}
    (hT : 0 < T) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hscale : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 < scale t)
    (hcont : Continuous
      (fun q : ℝ × ℝ => scale q.1 * (A q.2 - u q.1 q.2)))
    (hupper : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
      scale t * (A x - u t x) ≤ B)
    (hinit : ∀ x, scale 0 * (A x - u 0 x) ≤ C)
    (hgap : C + 2 * delta <
      wholeLineSlabSup T (fun t x => scale t * (A x - u t x)))
    (hAleft : ∀ x, x ≤ X → A x = A X)
    (hAX : HasDerivAt A 0 X)
    (hAaway : ∀ x, x ≠ X → ContDiffAt ℝ 2 A x)
    (huspace : ∀ ⦃t⦄, t ∈ Set.Ioc (0 : ℝ) T → ContDiff ℝ 2 (u t))
    (htime : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun s : ℝ => scale s * (A x - u s x))
        (deriv (fun s : ℝ => scale s * (A x - u s x)) t) t) :
    ∃ t ∈ Set.Ioc (0 : ℝ) T, ∃ x : ℝ,
      wholeLineSlabSup T (fun s y => scale s * (A y - u s y)) - 2 * delta <
        scale t * (A x - u t x) ∧
      0 ≤ deriv (fun s : ℝ => scale s * (A x - u s x)) t ∧
      ((x ≠ X ∧
          |deriv (fun y : ℝ => scale t * (A y - u t y)) x| < rho ∧
          deriv (deriv (fun y : ℝ => scale t * (A y - u t y))) x < rho) ∨
        (x = X ∧ deriv (u t) X = 0 ∧
          -scale t * deriv (deriv (u t)) X < rho)) := by
  let e : ℝ → ℝ → ℝ := fun t x => scale t * (A x - u t x)
  let L : ℝ := wholeLineSlabSup T e
  have hne : (wholeLineSlabValues T e).Nonempty :=
    wholeLineSlabValues_nonempty hT.le e
  have hbdd : BddAbove (wholeLineSlabValues T e) :=
    wholeLineSlabValues_bddAbove hupper
  have hLB : L ≤ B := wholeLineSlabSup_le hT.le hupper
  obtain ⟨a, ⟨s, hs, y, hay⟩, ha⟩ :=
    exists_lt_of_lt_csSup hne
      (show L - delta < sSup (wholeLineSlabValues T e) by
        change L - delta < L
        linarith)
  have hesy : L - delta < e s y := by simpa [← hay] using ha
  let D : ℝ := B - C + 2 * delta + (y - X) ^ 2 + 1
  have hD : 0 < D := by
    dsimp [D]
    nlinarith [hgap, hLB, sq_nonneg (y - X)]
  let eps : ℝ :=
    min (delta / ((y - X) ^ 2 + 1))
      (min (rho / 2) (rho ^ 2 / (4 * D))) / 2
  have hyden : 0 < (y - X) ^ 2 + 1 := by positivity
  have heps : 0 < eps := by
    dsimp [eps]
    positivity
  have hepsDelta : eps * ((y - X) ^ 2 + 1) < delta := by
    have hle : min (delta / ((y - X) ^ 2 + 1))
        (min (rho / 2) (rho ^ 2 / (4 * D))) ≤
          delta / ((y - X) ^ 2 + 1) := min_le_left _ _
    have hlt : eps < delta / ((y - X) ^ 2 + 1) := by
      dsimp [eps]
      nlinarith [div_pos hdelta hyden]
    exact (lt_div_iff₀ hyden).mp hlt
  have htwoEps : 2 * eps < rho := by
    have hle : min (delta / ((y - X) ^ 2 + 1))
        (min (rho / 2) (rho ^ 2 / (4 * D))) ≤ rho / 2 :=
      (min_le_right _ _).trans (min_le_left _ _)
    dsimp [eps]
    nlinarith
  have hfourEpsD : 4 * eps * D < rho ^ 2 := by
    have hle : min (delta / ((y - X) ^ 2 + 1))
        (min (rho / 2) (rho ^ 2 / (4 * D))) ≤ rho ^ 2 / (4 * D) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hlt : eps < rho ^ 2 / (4 * D) := by
      dsimp [eps]
      nlinarith [div_pos (sq_pos_of_pos hrho) (by positivity : 0 < 4 * D)]
    nlinarith [(lt_div_iff₀ (by positivity : 0 < 4 * D)).mp hlt]
  have href : L - 2 * delta < e s y - eps * (y - X) ^ 2 := by
    have hepsy : eps * (y - X) ^ 2 < delta := by
      have hyle : (y - X) ^ 2 ≤ (y - X) ^ 2 + 1 := by linarith
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hyle heps.le) hepsDelta
    linarith
  let R : ℝ :=
    max (|y - X| + 1)
      (Real.sqrt ((B - (L - 2 * delta)) / eps + 1) + 1)
  have hBL : 0 < B - (L - 2 * delta) := by
    nlinarith [hLB, hdelta]
  have hrootArg : 0 ≤ (B - (L - 2 * delta)) / eps + 1 := by positivity
  have hR : 0 < R :=
    lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hyR : |y - X| < R := by
    linarith [le_max_left (|y - X| + 1)
      (Real.sqrt ((B - (L - 2 * delta)) / eps + 1) + 1)]
  have hRlarge : B - eps * R ^ 2 < L - 2 * delta := by
    have hsqrtR : Real.sqrt ((B - (L - 2 * delta)) / eps + 1) < R := by
      linarith [le_max_right (|y - X| + 1)
        (Real.sqrt ((B - (L - 2 * delta)) / eps + 1) + 1)]
    have hargRsq : (B - (L - 2 * delta)) / eps + 1 < R ^ 2 := by
      nlinarith [Real.sq_sqrt hrootArg,
        Real.sqrt_nonneg ((B - (L - 2 * delta)) / eps + 1), hsqrtR, hR]
    have hmul := mul_lt_mul_of_pos_left hargRsq heps
    have hcancel : eps * ((B - (L - 2 * delta)) / eps) =
        B - (L - 2 * delta) := by field_simp [ne_of_gt heps]
    rw [mul_add, hcancel] at hmul
    nlinarith
  let K : Set (ℝ × ℝ) :=
    Set.Icc (0 : ℝ) T ×ˢ Set.Icc (X - R) (X + R)
  have hKcompact : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKne : K.Nonempty := by
    refine ⟨(0, X), ⟨⟨le_rfl, hT.le⟩, ?_⟩⟩
    exact ⟨by linarith [hR], by linarith [hR]⟩
  have hgcont : ContinuousOn
      (fun q : ℝ × ℝ => e q.1 q.2 - eps * (q.2 - X) ^ 2) K :=
    hcont.sub (by fun_prop) |>.continuousOn
  obtain ⟨q, hqK, hqmax⟩ := hKcompact.exists_isMaxOn hKne hgcont
  have hsyK : (s, y) ∈ K := by
    have hy : y ∈ Set.Icc (X - R) (X + R) := by
      have hybounds := abs_lt.mp hyR
      constructor <;> linarith [hybounds.1, hybounds.2]
    exact ⟨hs, hy⟩
  have hqref : L - 2 * delta < e q.1 q.2 - eps * (q.2 - X) ^ 2 :=
    href.trans_le (hqmax hsyK)
  rcases q with ⟨t₀, x₀⟩
  have ht₀pos : 0 < t₀ := by
    by_contra hnot
    have ht₀zero : t₀ = 0 := le_antisymm (le_of_not_gt hnot) hqK.1.1
    have hbarInit : e t₀ x₀ - eps * (x₀ - X) ^ 2 ≤ C := by
      rw [ht₀zero]
      nlinarith [hinit x₀, mul_nonneg heps.le (sq_nonneg (x₀ - X))]
    have hCL : C < L - 2 * delta := by linarith [hgap]
    linarith
  have ht₀ : t₀ ∈ Set.Ioc (0 : ℝ) T := ⟨ht₀pos, hqK.1.2⟩
  have hx₀neRight : x₀ ≠ X + R := by
    intro hx
    have hside := hupper t₀ hqK.1 (X + R)
    rw [hx] at hqref
    have hsquare : (X + R - X) ^ 2 = R ^ 2 := by ring
    rw [hsquare] at hqref
    linarith [hRlarge]
  have hx₀neLeft : x₀ ≠ X - R := by
    intro hx
    have hside := hupper t₀ hqK.1 (X - R)
    rw [hx] at hqref
    have hsquare : (X - R - X) ^ 2 = R ^ 2 := by ring
    rw [hsquare] at hqref
    linarith [hRlarge]
  have hx₀ : x₀ ∈ Set.Ioo (X - R) (X + R) :=
    ⟨lt_of_le_of_ne hqK.2.1 (Ne.symm hx₀neLeft),
      lt_of_le_of_ne hqK.2.2 hx₀neRight⟩
  have heclose : L - 2 * delta < e t₀ x₀ := by
    nlinarith [mul_nonneg heps.le (sq_nonneg (x₀ - X))]
  have htimeMax : IsMaxOn
      (fun t : ℝ => e t x₀ - eps * (x₀ - X) ^ 2)
      (Set.Icc (0 : ℝ) T) t₀ := by
    intro t ht
    exact @hqmax (t, x₀) ⟨ht, hqK.2⟩
  have hetNonneg : 0 ≤ deriv (fun t : ℝ => e t x₀) t₀ := by
    have hder : HasDerivAt
        (fun t : ℝ => e t x₀ - eps * (x₀ - X) ^ 2)
        (deriv (fun t : ℝ => e t x₀) t₀) t₀ := by
      simpa only [e] using
        (htime (t := t₀) (x := x₀) ht₀).sub_const
          (eps * (x₀ - X) ^ 2)
    exact time_deriv_nonneg_at_Icc_max_c1splice hqK.1 ht₀pos hder htimeMax
  have hspaceMaxOn : IsMaxOn
      (fun x : ℝ => e t₀ x - eps * (x - X) ^ 2)
      (Set.Icc (X - R) (X + R)) x₀ := by
    intro x hx
    exact @hqmax (t₀, x) ⟨hqK.1, hx⟩
  have hspaceNhds : Set.Icc (X - R) (X + R) ∈ nhds x₀ := by
    rw [← mem_interior_iff_mem_nhds, interior_Icc]
    exact hx₀
  have hspaceLocal : IsLocalMax
      (fun x : ℝ => scale t₀ * (A x - u t₀ x) - eps * (x - X) ^ 2) x₀ := by
    simpa [e] using hspaceMaxOn.isLocalMax hspaceNhds
  refine ⟨t₀, ht₀, x₀, ?_, ?_, ?_⟩
  · simpa [e, L] using heclose
  · simpa [e] using hetNonneg
  · by_cases hxX : x₀ = X
    · right
      subst x₀
      have hcontact := smooth_profile_scaled_deriv_data_at_C1splice_contact
        (hscale t₀ hqK.1) hAleft hAX (huspace ht₀) hspaceLocal
      exact ⟨rfl, hcontact.1, lt_of_le_of_lt hcontact.2 htwoEps⟩
    · left
      have hebase : ContDiffAt ℝ 2 (fun x => A x - u t₀ x) x₀ :=
        (hAaway x₀ hxX).sub (huspace ht₀).contDiffAt
      have he2 : ContDiffAt ℝ 2
          (fun x => scale t₀ * (A x - u t₀ x)) x₀ :=
        contDiffAt_const.mul hebase
      have he1 : HasDerivAt (fun x => scale t₀ * (A x - u t₀ x))
          (deriv (fun x => scale t₀ * (A x - u t₀ x)) x₀) x₀ :=
        (he2.differentiableAt (by norm_num)).hasDerivAt
      have hquad : HasDerivAt (fun x : ℝ => eps * (x - X) ^ 2)
          (2 * eps * (x₀ - X)) x₀ := by
        convert ((((hasDerivAt_id x₀).sub_const X).pow 2).const_mul eps) using 1 <;>
          simp [id] <;> ring
      have hexEq : deriv (fun x : ℝ => scale t₀ * (A x - u t₀ x)) x₀ =
          2 * eps * (x₀ - X) := by
        have hzero := hspaceLocal.deriv_eq_zero
        have hderivEq := (he1.sub hquad).deriv
        have hderivEq' :
            deriv (fun x : ℝ =>
              scale t₀ * (A x - u t₀ x) - eps * (x - X) ^ 2) x₀ =
              deriv (fun x : ℝ => scale t₀ * (A x - u t₀ x)) x₀ -
                2 * eps * (x₀ - X) := by
          simpa only [Pi.sub_apply] using hderivEq
        rw [hderivEq'] at hzero
        linarith
      have hepsx : eps * (x₀ - X) ^ 2 < D := by
        have heB := hupper t₀ hqK.1 x₀
        dsimp [D]
        nlinarith [hqref, hgap]
      have hexSq : (2 * eps * (x₀ - X)) ^ 2 < rho ^ 2 := by
        have hmul : 4 * eps * (eps * (x₀ - X) ^ 2) < 4 * eps * D :=
          mul_lt_mul_of_pos_left hepsx (by positivity)
        calc
          (2 * eps * (x₀ - X)) ^ 2 =
              4 * eps * (eps * (x₀ - X) ^ 2) := by ring
          _ < 4 * eps * D := hmul
          _ < rho ^ 2 := hfourEpsD
      have hexAbs :
          |deriv (fun x : ℝ => scale t₀ * (A x - u t₀ x)) x₀| < rho := by
        rw [hexEq]
        exact abs_lt_of_sq_lt_sq hexSq hrho.le
      let f : ℝ → ℝ := fun x =>
        scale t₀ * (A x - u t₀ x) - eps * (x - X) ^ 2
      have hfcont : ContinuousAt f x₀ := by
        exact he2.continuousAt.sub (by fun_prop)
      have hfsecond : deriv (deriv f) x₀ ≤ 0 :=
        second_deriv_nonpos_of_localMax_c1splice hspaceLocal hfcont
      have hsecondEq : deriv (deriv f) x₀ =
          deriv (deriv (fun x => scale t₀ * (A x - u t₀ x))) x₀ -
            2 * eps := by
        have hiter := iteratedDeriv_fun_sub he2 (by fun_prop :
          ContDiffAt ℝ 2 (fun x : ℝ => eps * (x - X) ^ 2) x₀)
        have hquad2 : iteratedDeriv 2 (fun x : ℝ => eps * (x - X) ^ 2) x₀ =
            2 * eps := by
          exact iteratedDeriv_two_mul_sq_sub eps X x₀
        rw [hquad2] at hiter
        simpa [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ] using hiter
      have hexx : deriv
          (deriv (fun x : ℝ => scale t₀ * (A x - u t₀ x))) x₀ < rho := by
        rw [hsecondEq] at hfsecond
        linarith [htwoEps]
      exact ⟨hxX, hexAbs, hexx⟩

set_option maxHeartbeats 800000 in
/-- Continuous-time comparison with a stationary `C¹` barrier having one
constant-to-smooth splice.  The two PDE hypotheses are the ordinary scalar
operator-difference estimate away from the splice and its honest one-sided
form at the splice.  The exponential time weight is internal, so a
nonnegative zeroth-order Lipschitz constant is allowed. -/
theorem stationary_C1splice_le_of_scalar_parabolic_comparison
    {T B K C X : ℝ} {A : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0 < T) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hAleft : ∀ x, x ≤ X → A x = A X)
    (hAX : HasDerivAt A 0 X)
    (hAaway : ∀ x, x ≠ X → ContDiffAt ℝ 2 A x)
    (hcont : Continuous (fun q : ℝ × ℝ => A q.2 - u q.1 q.2))
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, |A x - u t x| ≤ B)
    (hinit : ∀ x, A x ≤ u 0 x)
    (huspace : ∀ ⦃t⦄, t ∈ Set.Ioc (0 : ℝ) T → ContDiff ℝ 2 (u t))
    (htime : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun s : ℝ => A x - u s x)
        (deriv (fun s : ℝ => A x - u s x) t) t)
    (hpdeAway : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T → x ≠ X →
      deriv (fun s : ℝ => A x - u s x) t ≤
        deriv (deriv (fun y : ℝ => A y - u t y)) x +
          K * |deriv (fun y : ℝ => A y - u t y) x| +
          C * (A x - u t x))
    (hpdeSplice : ∀ ⦃t : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      deriv (fun s : ℝ => A X - u s X) t ≤
        -deriv (deriv (u t)) X + K * |deriv (u t) X| +
          C * (A X - u t X)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, A x ≤ u t x := by
  let lam : ℝ := C + 1
  let scale : ℝ → ℝ := fun t => Real.exp (-(lam * t))
  let w : ℝ → ℝ → ℝ := fun t x => scale t * (A x - u t x)
  have hlam : 0 < lam := by dsimp [lam]; linarith
  have hscale_pos : ∀ t, 0 < scale t := by
    intro t
    exact Real.exp_pos _
  have hscale_le_one : ∀ t, 0 ≤ t → scale t ≤ 1 := by
    intro t ht
    dsimp [scale]
    rw [Real.exp_le_one_iff]
    nlinarith
  have hB : 0 ≤ B := by
    have h := hbound 0 ⟨le_rfl, hT.le⟩ 0
    exact (abs_nonneg (A 0 - u 0 0)).trans h
  have hwcont : Continuous (fun q : ℝ × ℝ => w q.1 q.2) := by
    dsimp [w, scale, lam]
    have hscont : Continuous (fun q : ℝ × ℝ =>
        Real.exp (-((C + 1) * q.1))) := by
      fun_prop
    exact hscont.mul hcont
  have hwupper : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, w t x ≤ B := by
    intro t ht x
    have heB : A x - u t x ≤ B :=
      (le_abs_self (A x - u t x)).trans (hbound t ht x)
    have hmul : scale t * (A x - u t x) ≤ scale t * B :=
      mul_le_mul_of_nonneg_left heB (hscale_pos t).le
    have hmulB : scale t * B ≤ 1 * B :=
      mul_le_mul_of_nonneg_right (hscale_le_one t ht.1) hB
    exact hmul.trans (by simpa using hmulB)
  have hwinit : ∀ x, w 0 x ≤ 0 := by
    intro x
    dsimp [w, scale]
    simpa using sub_nonpos.mpr (hinit x)
  have htimeW : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun s : ℝ => w s x)
        (deriv (fun s : ℝ => w s x) t) t := by
    intro t x ht
    have hlin : HasDerivAt (fun s : ℝ => -(lam * s)) (-lam) t := by
      convert ((hasDerivAt_id t).const_mul lam).neg using 1 <;> ring
    have hexp : HasDerivAt scale (-lam * scale t) t := by
      simpa [scale, mul_comm] using hlin.exp
    have hprod := hexp.mul (htime (t := t) (x := x) ht)
    exact hprod.differentiableAt.hasDerivAt
  have hpdeWAway : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T → x ≠ X →
      deriv (fun s : ℝ => w s x) t ≤
        deriv (deriv (fun y : ℝ => w t y)) x +
          K * |deriv (fun y : ℝ => w t y) x| - w t x := by
    intro t x ht hx
    let e : ℝ → ℝ := fun y => A y - u t y
    have hlin : HasDerivAt (fun s : ℝ => -(lam * s)) (-lam) t := by
      convert ((hasDerivAt_id t).const_mul lam).neg using 1 <;> ring
    have hexp : HasDerivAt scale (-lam * scale t) t := by
      simpa [scale, mul_comm] using hlin.exp
    have hprod := hexp.mul (htime (t := t) (x := x) ht)
    have hwt : deriv (fun s : ℝ => w s x) t =
        (-lam * scale t) * (A x - u t x) +
          scale t * deriv (fun s : ℝ => A x - u s x) t := by
      simpa [w] using hprod.deriv
    have hwx : deriv (fun y : ℝ => w t y) x =
        scale t * deriv e x := by
      simpa [w, e] using
        (deriv_const_mul_field (x := x) (scale t) (v := e))
    have hwxx : deriv (deriv (fun y : ℝ => w t y)) x =
        scale t * deriv (deriv e) x := by
      have hiter := iteratedDeriv_const_mul_field
        (x := x) (n := 2) (scale t) e
      simpa [w, e, show (2 : ℕ) = 1 + 1 by norm_num,
        iteratedDeriv_succ] using hiter
    have habs : |scale t * deriv e x| = scale t * |deriv e x| := by
      rw [abs_mul, abs_of_pos (hscale_pos t)]
    have hmul := mul_le_mul_of_nonneg_left (hpdeAway ht hx) (hscale_pos t).le
    rw [mul_add, mul_add] at hmul
    rw [hwt, hwx, hwxx, habs]
    dsimp [w, e, lam]
    nlinarith
  have hpdeWSplice : ∀ ⦃t : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      deriv (fun s : ℝ => w s X) t ≤
        -scale t * deriv (deriv (u t)) X +
          K * (scale t * |deriv (u t) X|) - w t X := by
    intro t ht
    have hlin : HasDerivAt (fun s : ℝ => -(lam * s)) (-lam) t := by
      convert ((hasDerivAt_id t).const_mul lam).neg using 1 <;> ring
    have hexp : HasDerivAt scale (-lam * scale t) t := by
      simpa [scale, mul_comm] using hlin.exp
    have hprod := hexp.mul (htime (t := t) (x := X) ht)
    have hwt : deriv (fun s : ℝ => w s X) t =
        (-lam * scale t) * (A X - u t X) +
          scale t * deriv (fun s : ℝ => A X - u s X) t := by
      simpa [w] using hprod.deriv
    have hmul := mul_le_mul_of_nonneg_left (hpdeSplice ht) (hscale_pos t).le
    rw [mul_add, mul_add] at hmul
    rw [hwt]
    dsimp [w, lam]
    nlinarith
  intro t ht x
  by_contra hnot
  have hlt : u t x < A x := lt_of_not_ge hnot
  have hepos : 0 < A x - u t x := by linarith
  have hwpos : 0 < w t x := mul_pos (hscale_pos t) hepos
  let L : ℝ := wholeLineSlabSup T w
  have hwL : w t x ≤ L :=
    le_wholeLineSlabSup hT.le hwupper ht x
  have hL : 0 < L := lt_of_lt_of_le hwpos hwL
  let delta : ℝ := L / 8
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hgap : 0 + 2 * delta < L := by dsimp [delta]; linarith
  let rho : ℝ := L / (8 * (K + 1))
  have hKone : 0 < K + 1 := by linarith
  have hrho : 0 < rho := by
    dsimp [rho]
    positivity
  obtain ⟨t₀, ht₀, x₀, hwclose, hwtNonneg, hbranch⟩ :=
    exists_wholeLineSlab_approx_max_deriv_data_C1splice
      (A := A) (u := u) (scale := scale) hT hdelta hrho
      (fun s _ => hscale_pos s) hwcont hwupper hwinit hgap
      hAleft hAX hAaway huspace htimeW
  have hLrho : (K + 1) * rho = L / 8 := by
    dsimp [rho]
    field_simp [ne_of_gt hKone]
  rcases hbranch with haway | hsplice
  · have hpdeAt := hpdeWAway ht₀ haway.1
    have hKderiv :
        K * |deriv (fun y : ℝ => w t₀ y) x₀| ≤ K * rho :=
      mul_le_mul_of_nonneg_left haway.2.1.le hK
    have hneg : deriv (deriv (fun y : ℝ => w t₀ y)) x₀ +
          K * |deriv (fun y : ℝ => w t₀ y) x₀| - w t₀ x₀ < 0 := by
      have hclose : L - 2 * delta < w t₀ x₀ := by
        simpa [w, L] using hwclose
      have hsecond := haway.2.2
      calc
        deriv (deriv (fun y : ℝ => w t₀ y)) x₀ +
              K * |deriv (fun y : ℝ => w t₀ y) x₀| - w t₀ x₀
            < rho + K * rho - (L - 2 * delta) := by linarith
        _ = (K + 1) * rho - (L - 2 * delta) := by ring
        _ < 0 := by rw [hLrho]; dsimp [delta]; linarith
    linarith
  · have hpdeAt := hpdeWSplice ht₀
    have hclose : L - 2 * delta < w t₀ x₀ := by
      simpa [w, L] using hwclose
    rw [hsplice.1] at hwtNonneg hclose
    simp only [hsplice.2.1, abs_zero, mul_zero, add_zero] at hpdeAt
    have hneg : -scale t₀ * deriv (deriv (u t₀)) X - w t₀ X < 0 := by
      calc
        -scale t₀ * deriv (deriv (u t₀)) X - w t₀ X
            < rho - (L - 2 * delta) := by
              linarith [hsplice.2.2]
        _ < 0 := by
          have hrhoL : rho ≤ L / 8 := by
            dsimp [rho]
            have hden : 8 ≤ 8 * (K + 1) := by nlinarith
            exact div_le_div_of_nonneg_left hL.le (by norm_num) hden
          dsimp [delta]
          linarith
    linarith

section AxiomAudit

#print axioms second_deriv_nonneg_of_localMinOn_Iic_of_deriv_eq_zero
#print axioms smooth_profile_deriv_data_at_C1splice_contact
#print axioms smooth_profile_scaled_deriv_data_at_C1splice_contact
#print axioms exists_wholeLineSlab_approx_max_deriv_data_C1splice
#print axioms stationary_C1splice_le_of_scalar_parabolic_comparison

end AxiomAudit

end ShenWork.Paper1
