/-
  Joint continuity of a parametrized spatial derivative from joint continuity
  of the values and a spatial Holder modulus uniform in the parameter.

  The key point is that, at a fixed interior spatial point, the derivative is
  uniformly approximated by one fixed secant slope.  The mean value theorem
  controls the error by the common Holder modulus, while joint continuity of
  the values makes that secant slope continuous in the parameter.
-/
import ShenWork.Paper2.IntervalJointContinuityFromHolder

open Set Topology
open scoped Topology

noncomputable section

namespace ShenWork.Paper2

/-- At a fixed interior spatial point, a common spatial Holder modulus for the
derivatives upgrades joint continuity of the values to parameter continuity of
the derivative, using a fixed secant slope and the mean value theorem. -/
private theorem parametricSpatialDeriv_timeSlice_continuousOn_interior
    {f : ℝ → ℝ → ℝ} {I : Set ℝ} {K theta x : ℝ}
    (hK : 0 ≤ K) (htheta : 0 < theta)
    (hjoint : ContinuousOn (Function.uncurry f)
      (I ×ˢ Set.Icc (0 : ℝ) 1))
    (hslice_diff : ∀ t ∈ I,
      DifferentiableOn ℝ (f t) (Set.Ioo (0 : ℝ) 1))
    (hholder : ∀ t ∈ I, ∀ z ∈ Set.Ioo (0 : ℝ) 1,
      ∀ w ∈ Set.Ioo (0 : ℝ) 1,
        |deriv (f t) z - deriv (f t) w| ≤ K * |z - w| ^ theta)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    ContinuousOn (fun t ↦ deriv (f t) x) I := by
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hx
  have hvalue_cont : ∀ z ∈ Set.Icc (0 : ℝ) 1,
      ContinuousOn (fun t ↦ f t z) I := by
    intro z hz
    have hpair : ContinuousOn (fun t : ℝ ↦ ((t, z) : ℝ × ℝ)) I :=
      continuousOn_id.prodMk continuousOn_const
    have hmaps : MapsTo (fun t : ℝ ↦ ((t, z) : ℝ × ℝ)) I
        (I ×ˢ Set.Icc (0 : ℝ) 1) := by
      intro t ht
      exact Set.mem_prod.mpr ⟨ht, hz⟩
    have hcomp := hjoint.comp hpair hmaps
    simpa [Function.comp_def, Function.uncurry] using hcomp
  have hslice_cont : ∀ t ∈ I,
      ContinuousOn (f t) (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    have hpair : ContinuousOn (fun z : ℝ ↦ ((t, z) : ℝ × ℝ))
        (Set.Icc (0 : ℝ) 1) :=
      continuousOn_const.prodMk continuousOn_id
    have hmaps : MapsTo (fun z : ℝ ↦ ((t, z) : ℝ × ℝ))
        (Set.Icc (0 : ℝ) 1) (I ×ˢ Set.Icc (0 : ℝ) 1) := by
      intro z hz
      exact Set.mem_prod.mpr ⟨ht, hz⟩
    have hcomp := hjoint.comp hpair hmaps
    simpa [Function.comp_def, Function.uncurry] using hcomp
  rw [Metric.continuousOn_iff]
  intro q hq eps heps
  have heps3 : 0 < eps / 3 := by linarith
  let modulus : ℝ → ℝ := fun s ↦ K * |s| ^ theta
  have hmodulus_cont : Continuous modulus := by
    dsimp [modulus]
    have habs_cont : Continuous (fun s : ℝ ↦ |s|) := continuous_abs
    exact continuous_const.mul
      (habs_cont.rpow_const (fun _ ↦ Or.inr htheta.le))
  have hmodulus_zero : modulus 0 = 0 := by
    simp [modulus, htheta.ne']
  have hmodulus_at : ContinuousAt modulus 0 := hmodulus_cont.continuousAt
  rw [Metric.continuousAt_iff] at hmodulus_at
  obtain ⟨delta_x, hdelta_x, hmodulus_delta⟩ :=
    hmodulus_at (eps / 3) heps3
  let step : ℝ := min (delta_x / 2) ((1 - x) / 2)
  have hstep_pos : 0 < step := by
    dsimp [step]
    exact lt_min (half_pos hdelta_x) (half_pos (sub_pos.mpr hx.2))
  have hstep_lt_delta : step < delta_x := by
    calc
      step ≤ delta_x / 2 := min_le_left _ _
      _ < delta_x := half_lt_self hdelta_x
  have hstep_lt_boundary : x + step < 1 := by
    have hs : step ≤ (1 - x) / 2 := min_le_right _ _
    linarith [sub_pos.mpr hx.2]
  have hstep_dist : dist step 0 < delta_x := by
    simpa [Real.dist_eq, abs_of_pos hstep_pos] using hstep_lt_delta
  have hmodulus_step_dist := hmodulus_delta hstep_dist
  have hmodulus_step_nonneg : 0 ≤ modulus step := by
    exact mul_nonneg hK (Real.rpow_nonneg (abs_nonneg _) _)
  have hmodulus_step : modulus step < eps / 3 := by
    rw [hmodulus_zero, Real.dist_eq, sub_zero,
      abs_of_nonneg hmodulus_step_nonneg] at hmodulus_step_dist
    exact hmodulus_step_dist
  let y : ℝ := x + step
  have hxy : x < y := by
    dsimp [y]
    linarith
  have hy1 : y < 1 := by
    simpa [y] using hstep_lt_boundary
  have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨le_trans hx.1.le hxy.le, hy1.le⟩
  let secant : ℝ → ℝ := fun t ↦ (f t y - f t x) / (y - x)
  have hsecant_cont : ContinuousOn secant I := by
    dsimp [secant]
    exact ((hvalue_cont y hyIcc).sub (hvalue_cont x hxIcc)).div_const (y - x)
  have happrox : ∀ t ∈ I,
      |deriv (f t) x - secant t| < eps / 3 := by
    intro t ht
    have hIcc_sub : Set.Icc x y ⊆ Set.Icc (0 : ℝ) 1 := by
      intro z hz
      exact ⟨le_trans hx.1.le hz.1, le_trans hz.2 hyIcc.2⟩
    have hIoo_sub : Set.Ioo x y ⊆ Set.Ioo (0 : ℝ) 1 := by
      intro z hz
      exact ⟨hx.1.trans hz.1, lt_of_lt_of_le hz.2 hyIcc.2⟩
    obtain ⟨c, hc, hc_eq⟩ := exists_deriv_eq_slope (f t) hxy
      ((hslice_cont t ht).mono hIcc_sub)
      ((hslice_diff t ht).mono hIoo_sub)
    have hcIoo : c ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨hx.1.trans hc.1, hc.2.trans hy1⟩
    have hxc : |x - c| ≤ step := by
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hc.1.le)]
      exact (sub_le_iff_le_add).2 (by simpa [y, add_comm] using hc.2.le)
    have hrpow : |x - c| ^ theta ≤ step ^ theta := by
      exact Real.rpow_le_rpow (abs_nonneg _) hxc htheta.le
    have hholder_xc := hholder t ht x hx c hcIoo
    have hbound : K * |x - c| ^ theta < eps / 3 := by
      calc
        K * |x - c| ^ theta ≤ K * step ^ theta :=
          mul_le_mul_of_nonneg_left hrpow hK
        _ = modulus step := by simp [modulus, abs_of_pos hstep_pos]
        _ < eps / 3 := hmodulus_step
    have hc_secant : deriv (f t) c = secant t := by
      simpa [secant] using hc_eq
    rw [← hc_secant]
    exact lt_of_le_of_lt hholder_xc hbound
  rw [Metric.continuousOn_iff] at hsecant_cont
  obtain ⟨delta_t, hdelta_t, hsecant_delta⟩ :=
    hsecant_cont q hq (eps / 3) heps3
  refine ⟨delta_t, hdelta_t, ?_⟩
  intro t ht hdist
  have hsecant_close : |secant t - secant q| < eps / 3 := by
    simpa [Real.dist_eq] using hsecant_delta t ht hdist
  have happrox_t := happrox t ht
  have happrox_q : |secant q - deriv (f q) x| < eps / 3 := by
    simpa [abs_sub_comm] using happrox q hq
  rw [Real.dist_eq]
  calc
    |deriv (f t) x - deriv (f q) x|
        = |(deriv (f t) x - secant t) +
            (secant t - secant q) +
            (secant q - deriv (f q) x)| := by ring_nf
    _ ≤ |deriv (f t) x - secant t| +
          |secant t - secant q| +
          |secant q - deriv (f q) x| := by
        exact (abs_add_le _ _).trans
          (add_le_add (abs_add_le _ _) le_rfl)
    _ < eps / 3 + eps / 3 + eps / 3 := by
        exact add_lt_add (add_lt_add happrox_t hsecant_close) happrox_q
    _ = eps := by ring

/-- Closed-space wrapper for the fixed-point result.  The endpoint time slices
are constant zero; interior points use the secant-slope theorem above. -/
private theorem parametricSpatialDeriv_timeSlice_continuousOn
    {f : ℝ → ℝ → ℝ} {I : Set ℝ} {K theta x : ℝ}
    (hK : 0 ≤ K) (htheta : 0 < theta)
    (hjoint : ContinuousOn (Function.uncurry f)
      (I ×ˢ Set.Icc (0 : ℝ) 1))
    (hslice_diff : ∀ t ∈ I,
      DifferentiableOn ℝ (f t) (Set.Ioo (0 : ℝ) 1))
    (hholder : ∀ t ∈ I, ∀ z ∈ Set.Icc (0 : ℝ) 1,
      ∀ w ∈ Set.Icc (0 : ℝ) 1,
        |deriv (f t) z - deriv (f t) w| ≤ K * |z - w| ^ theta)
    (hleft : ∀ t ∈ I, deriv (f t) 0 = 0)
    (hright : ∀ t ∈ I, deriv (f t) 1 = 0)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ContinuousOn (fun t ↦ deriv (f t) x) I := by
  rcases eq_or_lt_of_le hx.1 with hx0 | hxpos
  · subst x
    exact continuousOn_const.congr (fun t ht ↦ hleft t ht)
  rcases eq_or_lt_of_le hx.2 with hx1 | hxlt
  · subst x
    exact continuousOn_const.congr (fun t ht ↦ hright t ht)
  exact parametricSpatialDeriv_timeSlice_continuousOn_interior
    hK htheta hjoint hslice_diff
      (fun t ht z hz w hw ↦ hholder t ht z
        (Set.Ioo_subset_Icc_self hz) w (Set.Ioo_subset_Icc_self hw))
      ⟨hxpos, hxlt⟩

/-- Joint continuity of a parametrized ordinary spatial derivative on the
closed unit interval.  No derivative continuity in the parameter is assumed:
it is produced from joint continuity of the values and the common spatial
Holder modulus. -/
theorem parametricSpatialDeriv_jointContinuousOn_of_uniformHolder
    {f : ℝ → ℝ → ℝ} {I : Set ℝ} {K theta : ℝ}
    (hK : 0 ≤ K) (htheta : 0 < theta)
    (hjoint : ContinuousOn (Function.uncurry f)
      (I ×ˢ Set.Icc (0 : ℝ) 1))
    (hslice_diff : ∀ t ∈ I,
      DifferentiableOn ℝ (f t) (Set.Ioo (0 : ℝ) 1))
    (hholder : ∀ t ∈ I, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ∀ y ∈ Set.Icc (0 : ℝ) 1,
        |deriv (f t) x - deriv (f t) y| ≤ K * |x - y| ^ theta)
    (hleft : ∀ t ∈ I, deriv (f t) 0 = 0)
    (hright : ∀ t ∈ I, deriv (f t) 1 = 0) :
    ContinuousOn
      (Function.uncurry (fun t x ↦ deriv (f t) x))
      (I ×ˢ Set.Icc (0 : ℝ) 1) := by
  apply jointContinuousOn_of_timeSlices_and_uniformHolder hK htheta
  · intro x hx
    exact parametricSpatialDeriv_timeSlice_continuousOn hK htheta hjoint
      hslice_diff hholder hleft hright hx
  · exact hholder

/-- Positive-time local form.  The spatial Holder constant may deteriorate as
the lower time cutoff tends to zero. -/
theorem parametricSpatialDeriv_jointContinuousOn_Ioo_of_positiveStripHolder
    {f : ℝ → ℝ → ℝ} {T theta : ℝ}
    (htheta : 0 < theta)
    (hjoint : ContinuousOn (Function.uncurry f)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1))
    (hslice_diff : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      DifferentiableOn ℝ (f t) (Set.Ioo (0 : ℝ) 1))
    (hholder : ∀ tau : ℝ, 0 < tau →
      ∃ K : ℝ, 0 ≤ K ∧
        ∀ t ∈ Set.Icc tau T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
          ∀ y ∈ Set.Icc (0 : ℝ) 1,
            |deriv (f t) x - deriv (f t) y| ≤ K * |x - y| ^ theta)
    (hleft : ∀ t ∈ Set.Ioo (0 : ℝ) T, deriv (f t) 0 = 0)
    (hright : ∀ t ∈ Set.Ioo (0 : ℝ) T, deriv (f t) 1 = 0) :
    ContinuousOn
      (Function.uncurry (fun t x ↦ deriv (f t) x))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
  have htime : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ContinuousOn (fun t ↦ deriv (f t) x) (Set.Ioo (0 : ℝ) T) := by
    intro x hx q hq
    let tau : ℝ := q / 2
    have htau_pos : 0 < tau := by
      dsimp [tau]
      linarith [hq.1]
    have htau_q : tau < q := by
      dsimp [tau]
      linarith [hq.1]
    obtain ⟨K, hK, hKholder⟩ := hholder tau htau_pos
    have htime_sub : Set.Ioo tau T ⊆ Set.Ioo (0 : ℝ) T := by
      intro t ht
      exact ⟨htau_pos.trans ht.1, ht.2⟩
    have hjoint_local : ContinuousOn (Function.uncurry f)
        (Set.Ioo tau T ×ˢ Set.Icc (0 : ℝ) 1) :=
      hjoint.mono (Set.prod_mono htime_sub Subset.rfl)
    have hdiff_local : ∀ t ∈ Set.Ioo tau T,
        DifferentiableOn ℝ (f t) (Set.Ioo (0 : ℝ) 1) := by
      intro t ht
      exact hslice_diff t (htime_sub ht)
    have hholder_local : ∀ t ∈ Set.Ioo tau T,
        ∀ z ∈ Set.Icc (0 : ℝ) 1, ∀ w ∈ Set.Icc (0 : ℝ) 1,
          |deriv (f t) z - deriv (f t) w| ≤ K * |z - w| ^ theta := by
      intro t ht z hz w hw
      exact hKholder t ⟨ht.1.le, ht.2.le⟩ z hz w hw
    have hleft_local : ∀ t ∈ Set.Ioo tau T, deriv (f t) 0 = 0 := by
      intro t ht
      exact hleft t (htime_sub ht)
    have hright_local : ∀ t ∈ Set.Ioo tau T, deriv (f t) 1 = 0 := by
      intro t ht
      exact hright t (htime_sub ht)
    have hcont_local : ContinuousOn (fun t ↦ deriv (f t) x)
        (Set.Ioo tau T) :=
      parametricSpatialDeriv_timeSlice_continuousOn hK htheta
        hjoint_local hdiff_local hholder_local hleft_local hright_local hx
    have hq_local : q ∈ Set.Ioo tau T := ⟨htau_q, hq.2⟩
    apply (hcont_local q hq_local).mono_of_mem_nhdsWithin
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨Set.Ioi tau, Ioi_mem_nhds htau_q, ?_⟩
    intro t ht
    exact ⟨ht.1, ht.2.2⟩
  exact jointContinuousOn_Ioo_of_timeSlices_and_positiveStripHolder
    htheta htime hholder

/-- Direct positive-time/interior-space form.  This version needs no endpoint
derivative hypotheses and assumes the uniform Holder estimate only for
interior spatial points, exactly as supplied by the faithful conjugate-mild
positive-time estimate. -/
theorem parametricSpatialDeriv_jointContinuousOn_Ioo_space_of_positiveStripHolder
    {f : ℝ → ℝ → ℝ} {T theta : ℝ}
    (htheta : 0 < theta)
    (hjoint : ContinuousOn (Function.uncurry f)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1))
    (hslice_diff : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      DifferentiableOn ℝ (f t) (Set.Ioo (0 : ℝ) 1))
    (hholder : ∀ tau : ℝ, 0 < tau →
      ∃ K : ℝ, 0 ≤ K ∧
        ∀ t ∈ Set.Icc tau T, ∀ x ∈ Set.Ioo (0 : ℝ) 1,
          ∀ y ∈ Set.Ioo (0 : ℝ) 1,
            |deriv (f t) x - deriv (f t) y| ≤ K * |x - y| ^ theta) :
    ContinuousOn
      (Function.uncurry (fun t x ↦ deriv (f t) x))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Ioo (0 : ℝ) 1) := by
  have htime : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      ContinuousOn (fun t ↦ deriv (f t) x) (Set.Ioo (0 : ℝ) T) := by
    intro x hx q hq
    let tau : ℝ := q / 2
    have htau_pos : 0 < tau := by
      dsimp [tau]
      linarith [hq.1]
    have htau_q : tau < q := by
      dsimp [tau]
      linarith [hq.1]
    obtain ⟨K, hK, hKholder⟩ := hholder tau htau_pos
    have htime_sub : Set.Ioo tau T ⊆ Set.Ioo (0 : ℝ) T := by
      intro t ht
      exact ⟨htau_pos.trans ht.1, ht.2⟩
    have hjoint_local : ContinuousOn (Function.uncurry f)
        (Set.Ioo tau T ×ˢ Set.Icc (0 : ℝ) 1) :=
      hjoint.mono (Set.prod_mono htime_sub Subset.rfl)
    have hdiff_local : ∀ t ∈ Set.Ioo tau T,
        DifferentiableOn ℝ (f t) (Set.Ioo (0 : ℝ) 1) := by
      intro t ht
      exact hslice_diff t (htime_sub ht)
    have hholder_local : ∀ t ∈ Set.Ioo tau T,
        ∀ z ∈ Set.Ioo (0 : ℝ) 1, ∀ w ∈ Set.Ioo (0 : ℝ) 1,
          |deriv (f t) z - deriv (f t) w| ≤ K * |z - w| ^ theta := by
      intro t ht z hz w hw
      exact hKholder t ⟨ht.1.le, ht.2.le⟩ z hz w hw
    have hcont_local : ContinuousOn (fun t ↦ deriv (f t) x)
        (Set.Ioo tau T) :=
      parametricSpatialDeriv_timeSlice_continuousOn_interior hK htheta
        hjoint_local hdiff_local hholder_local hx
    have hq_local : q ∈ Set.Ioo tau T := ⟨htau_q, hq.2⟩
    apply (hcont_local q hq_local).mono_of_mem_nhdsWithin
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨Set.Ioi tau, Ioi_mem_nhds htau_q, ?_⟩
    intro t ht
    exact ⟨ht.1, ht.2.2⟩
  exact jointContinuousOn_Ioo_of_timeSlices_and_positiveStripHolder
    htheta htime hholder

end ShenWork.Paper2

#print axioms ShenWork.Paper2.parametricSpatialDeriv_jointContinuousOn_of_uniformHolder
#print axioms ShenWork.Paper2.parametricSpatialDeriv_jointContinuousOn_Ioo_of_positiveStripHolder
#print axioms ShenWork.Paper2.parametricSpatialDeriv_jointContinuousOn_Ioo_space_of_positiveStripHolder
