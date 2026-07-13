/-
  Lower-barrier comparison data for the positive-attraction construction.

  The paper's positive trap is not spatially monotone.  Its lower barrier is
  the positive plateau followed by the two-exponential tail.  The smallness
  `chi < 1/2` supplies the constant-plateau subsolution even though the frozen
  elliptic field is only bounded by `MChi^gamma`.
-/
import ShenWork.Paper1.WavePositiveLocalStep
import ShenWork.Paper1.WaveLowerRawTailfree
import ShenWork.Paper1.StatementAssembly

open Filter Topology Set Real

noncomputable section

namespace ShenWork.Paper1

/-- A conservative positive height for the constant part of the positive
lower barrier. -/
def paper1PositivePlateauFloor (p : CMParams) : ℝ :=
  min 1 ((1 - 2 * p.χ) / (2 * (1 - p.χ) ^ 2))

theorem paper1PositivePlateauFloor_pos
    (p : CMParams) (hχ : p.χ < (1 / 2 : ℝ)) :
    0 < paper1PositivePlateauFloor p := by
  unfold paper1PositivePlateauFloor
  have hden : 0 < 1 - p.χ := by linarith
  apply lt_min one_pos
  exact div_pos (by linarith) (by positivity)

/-- In the positive headline regime the normalized elliptic source-box bound
obeys `MChi^gamma <= 1/(1-chi)`.  The exponent inequality is exactly
`gamma <= alpha = m+gamma-1`. -/
theorem MChi_rpow_gamma_le_one_div_one_sub_chi
    (p : CMParams)
    (hχ0 : 0 ≤ p.χ) (hχ1 : p.χ < 1)
    (hα : p.α = p.m + p.γ - 1) :
    (MChi p) ^ p.γ ≤ 1 / (1 - p.χ) := by
  let b : ℝ := 1 / (1 - p.χ)
  have hden : 0 < 1 - p.χ := by linarith
  have hbpos : 0 < b := by
    dsimp [b]
    positivity
  have hb1 : 1 ≤ b := by
    dsimp [b]
    rw [le_div_iff₀ hden]
    linarith
  have hαpos : 0 < p.α := lt_of_lt_of_le one_pos p.hα
  have hγleα : p.γ ≤ p.α := by
    rw [hα]
    linarith [p.hm]
  have hexp : (1 / p.α) * p.γ ≤ 1 := by
    rw [one_div_mul_eq_div]
    exact (div_le_one hαpos).2 hγleα
  rw [MChi_eq_rpow_of_chi_nonneg_lt_one p hχ0 hχ1]
  change (b ^ (1 / p.α)) ^ p.γ ≤ b
  rw [← Real.rpow_mul hbpos.le (1 / p.α) p.γ]
  calc
    b ^ ((1 / p.α) * p.γ) ≤ b ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hb1 hexp
    _ = b := Real.rpow_one b

/-- The small positive plateau is a genuine paper-expanded frozen
subsolution for every frozen profile in the nonmonotone positive trap. -/
theorem paperWaveOperator_const_subsolution_nonneg_pos_MChi
    (p : CMParams) {c κ d : ℝ} {u : ℝ → ℝ}
    (hχ0 : 0 ≤ p.χ) (hχhalf : p.χ < (1 / 2 : ℝ))
    (hα : p.α = p.m + p.γ - 1)
    (hd0 : 0 < d) (hd : d ≤ paper1PositivePlateauFloor p)
    (hu : InWaveTrapSet κ (MChi p) u) :
    ∀ x, 0 ≤ paperWaveOperator p c u (fun _ => d) x := by
  intro x
  rw [paperWaveOperator_const_eq p hu.cunif_bdd hu.nonneg x]
  apply mul_nonneg hd0.le
  have hχ1 : p.χ < 1 := by linarith
  have hden : 0 < 1 - p.χ := by linarith
  have hMpos : 0 < MChi p := MChi_pos_of_chi_lt_one p hχ1
  have hV0 : 0 ≤ frozenElliptic p u x :=
    frozenElliptic_nonneg_of_inWaveTrapSet p hu x
  have hVle : frozenElliptic p u x ≤ (MChi p) ^ p.γ :=
    frozenElliptic_le_rpow_of_inWaveTrapSet p hMpos hu x
  have hMγ : (MChi p) ^ p.γ ≤ 1 / (1 - p.χ) :=
    MChi_rpow_gamma_le_one_div_one_sub_chi p hχ0 hχ1 hα
  have hd1 : d ≤ 1 :=
    hd.trans (min_le_left _ _)
  have hdm1 : d ^ (p.m - 1) ≤ 1 :=
    Real.rpow_le_one hd0.le hd1 (sub_nonneg.mpr p.hm)
  have hdm10 : 0 ≤ d ^ (p.m - 1) :=
    Real.rpow_nonneg hd0.le _
  have hchem :
      p.χ * d ^ (p.m - 1) * frozenElliptic p u x ≤
        p.χ / (1 - p.χ) := by
    calc
      p.χ * d ^ (p.m - 1) * frozenElliptic p u x ≤
          p.χ * 1 * (1 / (1 - p.χ)) := by
        gcongr
        exact hVle.trans hMγ
      _ = p.χ / (1 - p.χ) := by ring
  have hdα : d ^ p.α ≤ d := by
    calc
      d ^ p.α ≤ d ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hd0 hd1 p.hα
      _ = d := Real.rpow_one d
  have hdfloor :
      d ≤ (1 - 2 * p.χ) / (2 * (1 - p.χ) ^ 2) :=
    hd.trans (min_le_right _ _)
  have hlogistic :
      (1 - p.χ) * d ^ p.α ≤
        (1 - 2 * p.χ) / (2 * (1 - p.χ)) := by
    have h1 := mul_le_mul_of_nonneg_left hdα hden.le
    have h2 := mul_le_mul_of_nonneg_left hdfloor hden.le
    have hdenne : 1 - p.χ ≠ 0 := ne_of_gt hden
    calc
      (1 - p.χ) * d ^ p.α ≤ (1 - p.χ) * d := h1
      _ ≤ (1 - p.χ) *
          ((1 - 2 * p.χ) / (2 * (1 - p.χ) ^ 2)) := h2
      _ = (1 - 2 * p.χ) / (2 * (1 - p.χ)) := by
        field_simp [hdenne]
  have hmargin :
      0 < (1 - 2 * p.χ) / (2 * (1 - p.χ)) := by
    exact div_pos (by linarith) (by positivity)
  have hbudget :
      p.χ / (1 - p.χ) +
          (1 - 2 * p.χ) / (2 * (1 - p.χ)) < 1 := by
    have hdenne : 1 - p.χ ≠ 0 := ne_of_gt hden
    have heq :
        p.χ / (1 - p.χ) +
            (1 - 2 * p.χ) / (2 * (1 - p.χ)) =
          1 - (1 - 2 * p.χ) / (2 * (1 - p.χ)) := by
      field_simp [hdenne]
      ring
    rw [heq]
    linarith
  have hpow : d ^ (p.m + p.γ - 1) = d ^ p.α := by
    rw [hα]
  rw [hpow]
  nlinarith [hchem, hlogistic, hbudget]

/-- Choose the lower-barrier coefficient far enough past the Lemma 4.2
threshold that its entire plateau lies below the positive constant-floor
budget. -/
theorem exists_positivePlateau_D
    (p : CMParams) {c κ κtilde : ℝ}
    (hχhalf : p.χ < (1 / 2 : ℝ))
    (hκ : 0 < κ) (hgap : 0 < κtilde - κ) :
    ∃ D : ℝ,
      1 ≤ D ∧
      paperDMin p.χ (MChi p) κ κtilde p.m p.γ c < D ∧
      ∀ x, lowerBarrierPlateau κ κtilde D x ≤
        paper1PositivePlateauFloor p := by
  let B : ℝ := max 1 (paperDMin p.χ (MChi p) κ κtilde p.m p.γ c)
  obtain ⟨D, hDB, htail⟩ :=
    exists_D_gt_with_exp_xplus_le
      (B := B) hκ hgap (paper1PositivePlateauFloor_pos p hχhalf)
  have hD1 : 1 ≤ D :=
    (le_max_left 1 _).trans hDB.le
  have hDmin :
      paperDMin p.χ (MChi p) κ κtilde p.m p.γ c < D :=
    lt_of_le_of_lt (le_max_right 1 _) hDB
  refine ⟨D, hD1, hDmin, ?_⟩
  intro x
  exact (lowerBarrierPlateau_le_exp_xplus hκ.le
    (lt_of_lt_of_le zero_lt_one hD1).le x).trans htail

/-! ## A piecewise-smooth tail-free maximum principle -/

/-- Centered version of the coercive quadratic-penalty maximum theorem. -/
theorem exists_isMaxOn_sub_mul_sq_center_of_bounded
    {f : ℝ → ℝ} {A eps a x₁ : ℝ}
    (hf : Continuous f) (hA : ∀ x, |f x| ≤ A) (heps : 0 < eps) :
    ∃ x₀,
      IsMaxOn (fun x => f x - eps * (x - a) ^ 2) Set.univ x₀ ∧
      f x₁ - eps * (x₁ - a) ^ 2 ≤
        f x₀ - eps * (x₀ - a) ^ 2 := by
  let F : ℝ → ℝ := fun y => f (y + a)
  have hF : Continuous F := by
    dsimp [F]
    fun_prop
  have hFA : ∀ y, |F y| ≤ A := fun y => hA (y + a)
  obtain ⟨y₀, hmax, hvalue⟩ :=
    exists_isMaxOn_sub_mul_sq_of_bounded
      (f := F) (A := A) (eps := eps) (x₁ := x₁ - a) hF hFA heps
  refine ⟨y₀ + a, ?_, ?_⟩
  · rw [isMaxOn_univ_iff] at hmax ⊢
    intro x
    have hx := hmax (x - a)
    dsimp [F] at hx
    convert hx using 1 <;> ring
  · dsimp [F] at hvalue
    convert hvalue using 1 <;> ring

/-- Omori-type data for a bounded function which is `C²` away from one
interface and differentiable at the interface.  If the first penalized maximum
lands on the interface, shifting the quadratic center by one makes a second
landing there impossible. -/
theorem exists_approx_positive_max_deriv_data_away_C1splice
    {f : ℝ → ℝ} {A eta x₁ X : ℝ}
    (hf : Continuous f) (hA : ∀ x, |f x| ≤ A)
    (hpos : 0 < f x₁) (heta : 0 < eta)
    (hXdiff : DifferentiableAt ℝ f X)
    (hf2 : ∀ x, x ≠ X → ContDiffAt ℝ 2 f x) :
    ∃ x₀, x₀ ≠ X ∧
      f x₁ / 2 < f x₀ ∧
      |deriv f x₀| < eta ∧
      deriv (deriv f) x₀ < eta := by
  have hApos : 0 < A :=
    lt_of_lt_of_le hpos (le_trans (le_abs_self (f x₁)) (hA x₁))
  let D : ℝ := 2 * A + x₁ ^ 2 + (x₁ - 1) ^ 2 + 2
  have hD : 0 < D := by
    dsimp [D]
    nlinarith [sq_nonneg x₁, sq_nonneg (x₁ - 1)]
  let eps : ℝ :=
    min 1
      (min (f x₁ / (2 * (x₁ ^ 2 + (x₁ - 1) ^ 2 + 1)))
        (min (eta / 2) (eta ^ 2 / (8 * D)))) / 2
  have hrefden : 0 < 2 * (x₁ ^ 2 + (x₁ - 1) ^ 2 + 1) := by
    positivity
  have heps : 0 < eps := by
    dsimp [eps]
    positivity
  have heps_one : eps < 1 := by
    dsimp [eps]
    have hmin : min 1
        (min (f x₁ / (2 * (x₁ ^ 2 + (x₁ - 1) ^ 2 + 1)))
          (min (eta / 2) (eta ^ 2 / (8 * D)))) ≤ 1 := min_le_left _ _
    nlinarith
  have heps_value :
      eps < f x₁ / (2 * (x₁ ^ 2 + (x₁ - 1) ^ 2 + 1)) := by
    dsimp [eps]
    have hmin : min 1
        (min (f x₁ / (2 * (x₁ ^ 2 + (x₁ - 1) ^ 2 + 1)))
          (min (eta / 2) (eta ^ 2 / (8 * D)))) ≤
        f x₁ / (2 * (x₁ ^ 2 + (x₁ - 1) ^ 2 + 1)) :=
      (min_le_right _ _).trans (min_le_left _ _)
    nlinarith [div_pos hpos hrefden]
  have heps_eta : 2 * eps < eta := by
    dsimp [eps]
    have hmin : min 1
        (min (f x₁ / (2 * (x₁ ^ 2 + (x₁ - 1) ^ 2 + 1)))
          (min (eta / 2) (eta ^ 2 / (8 * D)))) ≤ eta / 2 :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    nlinarith
  have heps_sq : 4 * eps * D < eta ^ 2 := by
    dsimp [eps]
    have hmin : min 1
        (min (f x₁ / (2 * (x₁ ^ 2 + (x₁ - 1) ^ 2 + 1)))
          (min (eta / 2) (eta ^ 2 / (8 * D)))) ≤ eta ^ 2 / (8 * D) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have hmul := mul_le_mul_of_nonneg_right hmin
      (show 0 ≤ 4 * D by positivity)
    field_simp [ne_of_gt hD] at hmul
    nlinarith [sq_pos_of_pos heta]
  have finish : ∀ a x₀,
      (a = 0 ∨ a = 1) → x₀ ≠ X →
      IsMaxOn (fun x => f x - eps * (x - a) ^ 2) Set.univ x₀ →
      f x₁ - eps * (x₁ - a) ^ 2 ≤
        f x₀ - eps * (x₀ - a) ^ 2 →
      f x₁ / 2 < f x₀ ∧
        |deriv f x₀| < eta ∧ deriv (deriv f) x₀ < eta := by
    intro a x₀ ha hx₀ hmax hvalue
    have ha0 : 0 ≤ a := by rcases ha with rfl | rfl <;> norm_num
    have ha1 : a ≤ 1 := by rcases ha with rfl | rfl <;> norm_num
    have hrefsq : (x₁ - a) ^ 2 ≤ x₁ ^ 2 + (x₁ - 1) ^ 2 := by
      rcases ha with rfl | rfl
      · nlinarith [sq_nonneg (x₁ - 1)]
      · nlinarith [sq_nonneg x₁]
    have hvalue_pos : f x₁ / 2 < f x₀ := by
      have hmul := mul_le_mul_of_nonneg_left hrefsq heps.le
      have hfrac :
          eps * (x₁ ^ 2 + (x₁ - 1) ^ 2) < f x₁ / 2 := by
        have hmul' := mul_le_mul_of_nonneg_right heps_value.le
          (show 0 ≤ x₁ ^ 2 + (x₁ - 1) ^ 2 by positivity)
        have hstrict :
            f x₁ /
                (2 * (x₁ ^ 2 + (x₁ - 1) ^ 2 + 1)) *
                (x₁ ^ 2 + (x₁ - 1) ^ 2) < f x₁ / 2 := by
          rw [div_mul_eq_mul_div]
          apply (div_lt_iff₀ hrefden).2
          nlinarith [sq_nonneg x₁, sq_nonneg (x₁ - 1)]
        exact lt_of_le_of_lt hmul' hstrict
      nlinarith [mul_nonneg heps.le (sq_nonneg (x₀ - a))]
    have hxbound : eps * (x₀ - a) ^ 2 < D := by
      have hfx₀ : f x₀ ≤ A := (le_abs_self (f x₀)).trans (hA x₀)
      have hfx₁ : -A ≤ f x₁ := neg_le_of_abs_le (hA x₁)
      have hepsref : eps * (x₁ - a) ^ 2 ≤
          x₁ ^ 2 + (x₁ - 1) ^ 2 := by
        calc
          eps * (x₁ - a) ^ 2 ≤ 1 * (x₁ - a) ^ 2 :=
            mul_le_mul_of_nonneg_right heps_one.le (sq_nonneg _)
          _ ≤ x₁ ^ 2 + (x₁ - 1) ^ 2 := by simpa using hrefsq
      dsimp [D]
      nlinarith
    have hlocal : IsLocalMax (fun x => f x - eps * (x - a) ^ 2) x₀ :=
      hmax.isLocalMax Filter.univ_mem
    have hf₀ := hf2 x₀ hx₀
    have hpen : HasDerivAt (fun x : ℝ => eps * (x - a) ^ 2)
        (2 * eps * (x₀ - a)) x₀ := by
      convert (((hasDerivAt_id x₀).sub_const a).pow 2).const_mul eps using 1
      simp only [id_eq]
      ring
    have hfirst : deriv f x₀ = 2 * eps * (x₀ - a) := by
      have hzero : deriv (fun x => f x - eps * (x - a) ^ 2) x₀ = 0 :=
        hlocal.deriv_eq_zero
      have heq : deriv (fun x => f x - eps * (x - a) ^ 2) x₀ =
          deriv f x₀ - 2 * eps * (x₀ - a) :=
        ((hf₀.differentiableAt (by norm_num)).hasDerivAt.sub hpen).deriv
      rw [heq] at hzero
      linarith
    have hpen2 : ContDiffAt ℝ 2 (fun x : ℝ => eps * (x - a) ^ 2) x₀ := by
      fun_prop
    have hsecond0 :
        iteratedDeriv 2 (fun x => f x - eps * (x - a) ^ 2) x₀ ≤ 0 :=
      iteratedDeriv2_nonpos_of_isLocalMax hlocal
        (hf₀.continuousAt.sub hpen2.continuousAt)
    have hlin :
        iteratedDeriv 2 (fun x => f x - eps * (x - a) ^ 2) x₀ =
          iteratedDeriv 2 f x₀ -
            iteratedDeriv 2 (fun x : ℝ => eps * (x - a) ^ 2) x₀ :=
      iteratedDeriv_fun_sub hf₀ hpen2
    have hpen2eq :
        iteratedDeriv 2 (fun x : ℝ => eps * (x - a) ^ 2) x₀ =
          2 * eps := by
      have hpen_all : ∀ y, HasDerivAt (fun x : ℝ => eps * (x - a) ^ 2)
          (2 * eps * (y - a)) y := by
        intro y
        convert (((hasDerivAt_id y).sub_const a).pow 2).const_mul eps using 1
        · simp only [id_eq]
          ring
      have hderiv_eq : deriv (fun x : ℝ => eps * (x - a) ^ 2) =
          fun y => 2 * eps * (y - a) := by
        funext y
        exact (hpen_all y).deriv
      rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero,
        hderiv_eq]
      convert (((hasDerivAt_id x₀).sub_const a).const_mul (2 * eps)).deriv using 1
      ring
    have hf2eq : iteratedDeriv 2 f x₀ = deriv (deriv f) x₀ := by
      simp [iteratedDeriv_succ, iteratedDeriv_zero]
    rw [hlin, hpen2eq, hf2eq] at hsecond0
    have hderiv_sq : (deriv f x₀) ^ 2 < eta ^ 2 := by
      rw [hfirst]
      calc
        (2 * eps * (x₀ - a)) ^ 2 =
            4 * eps * (eps * (x₀ - a) ^ 2) := by ring
        _ < 4 * eps * D :=
          mul_lt_mul_of_pos_left hxbound (by positivity)
        _ < eta ^ 2 := heps_sq
    have hderiv : |deriv f x₀| < eta := by
      rw [← sq_lt_sq₀ (abs_nonneg (deriv f x₀)) heta.le, sq_abs]
      exact hderiv_sq
    have hsecond : deriv (deriv f) x₀ ≤ 2 * eps := by linarith
    exact ⟨hvalue_pos, hderiv, lt_of_le_of_lt hsecond heps_eta⟩
  obtain ⟨x₀, hmax₀, hvalue₀⟩ :=
    exists_isMaxOn_sub_mul_sq_center_of_bounded
      (f := f) (A := A) (eps := eps) (a := 0) (x₁ := x₁) hf hA heps
  by_cases hx₀ : x₀ = X
  · have hlocal₀ : IsLocalMax (fun x => f x - eps * (x - 0) ^ 2) X := by
      rw [← hx₀]
      exact hmax₀.isLocalMax Filter.univ_mem
    have hpen₀ : HasDerivAt (fun x : ℝ => eps * (x - 0) ^ 2)
        (2 * eps * X) X := by
      convert (((hasDerivAt_id X).sub_const 0).pow 2).const_mul eps using 1
      simp only [id_eq]
      ring
    have hzero₀ : deriv (fun x => f x - eps * (x - 0) ^ 2) X = 0 :=
      hlocal₀.deriv_eq_zero
    have heq₀ : deriv (fun x => f x - eps * (x - 0) ^ 2) X =
        deriv f X - 2 * eps * X :=
      (hXdiff.hasDerivAt.sub hpen₀).deriv
    have hfX : deriv f X = 2 * eps * X := by
      rw [heq₀] at hzero₀
      linarith
    obtain ⟨x₂, hmax₂, hvalue₂⟩ :=
      exists_isMaxOn_sub_mul_sq_center_of_bounded
        (f := f) (A := A) (eps := eps) (a := 1) (x₁ := x₁) hf hA heps
    have hx₂ : x₂ ≠ X := by
      intro hx₂
      have hlocal₂ : IsLocalMax (fun x => f x - eps * (x - 1) ^ 2) X := by
        rw [← hx₂]
        exact hmax₂.isLocalMax Filter.univ_mem
      have hpen₂ : HasDerivAt (fun x : ℝ => eps * (x - 1) ^ 2)
          (2 * eps * (X - 1)) X := by
        convert (((hasDerivAt_id X).sub_const 1).pow 2).const_mul eps using 1
        simp only [id_eq]
        ring
      have hzero₂ : deriv (fun x => f x - eps * (x - 1) ^ 2) X = 0 :=
        hlocal₂.deriv_eq_zero
      have heq₂ : deriv (fun x => f x - eps * (x - 1) ^ 2) X =
          deriv f X - 2 * eps * (X - 1) :=
        (hXdiff.hasDerivAt.sub hpen₂).deriv
      rw [heq₂, hfX] at hzero₂
      nlinarith
    exact ⟨x₂, hx₂, finish 1 x₂ (Or.inr rfl) hx₂ hmax₂ hvalue₂⟩
  · exact ⟨x₀, hx₀, finish 0 x₀ (Or.inl rfl) hx₀ hmax₀ hvalue₀⟩

/-! ## Smoothness and the subsolution inequality away from the splice -/

theorem lowerBarrierPlateau_eventuallyEq_const_of_lt
    {κ κtilde D x : ℝ}
    (hx : x < lowerBarrierXPlus κ κtilde D) :
    Filter.EventuallyEq (nhds x) (lowerBarrierPlateau κ κtilde D)
      (fun _ => lowerBarrierRaw κ κtilde D
        (lowerBarrierXPlus κ κtilde D)) := by
  filter_upwards [eventually_lt_nhds hx] with y hy
  exact lowerBarrierPlateau_eq_const_of_le hy.le

theorem lowerBarrierPlateau_eventuallyEq_raw_of_gt
    {κ κtilde D x : ℝ}
    (hx : lowerBarrierXPlus κ κtilde D < x) :
    Filter.EventuallyEq (nhds x) (lowerBarrierPlateau κ κtilde D)
      (lowerBarrierRaw κ κtilde D) := by
  filter_upwards [eventually_gt_nhds hx] with y hy
  exact lowerBarrierPlateau_eq_raw_of_xplus_lt hy

/-- The plateau and raw tail have matching first derivative at the splice. -/
theorem lowerBarrierPlateau_hasDerivAt_xplus
    {κ κtilde D : ℝ}
    (hκ : 0 < κ) (hgap : 0 < κtilde - κ) (hD : 0 < D) :
    HasDerivAt (lowerBarrierPlateau κ κtilde D) 0
      (lowerBarrierXPlus κ κtilde D) := by
  let X := lowerBarrierXPlus κ κtilde D
  let P := lowerBarrierRaw κ κtilde D X
  apply (hasDerivAt_iff_tendsto_slope_left_right).2
  constructor
  · have heq :
        Filter.EventuallyEq (nhdsWithin X (Set.Iio X))
          (fun y => slope (lowerBarrierPlateau κ κtilde D) X y)
          (fun y => slope (fun _ : ℝ => P) X y) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      unfold slope
      rw [lowerBarrierPlateau_eq_const_of_le hy.le,
        lowerBarrierPlateau_eq_const_of_le (le_refl X)]
    have hconst : HasDerivAt (fun _ : ℝ => P) 0 X := hasDerivAt_const X P
    exact ((hasDerivAt_iff_tendsto_slope_left_right.mp hconst).1).congr' heq.symm
  · have heq :
        Filter.EventuallyEq (nhdsWithin X (Set.Ioi X))
          (fun y => slope (lowerBarrierPlateau κ κtilde D) X y)
          (fun y => slope (lowerBarrierRaw κ κtilde D) X y) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      unfold slope
      rw [lowerBarrierPlateau_eq_raw_of_xplus_lt hy,
        lowerBarrierPlateau_eq_const_of_le (le_refl X)]
    have hraw : HasDerivAt (lowerBarrierRaw κ κtilde D) 0 X := by
      convert lowerBarrierRaw_hasDerivAt κ κtilde D X using 1
      rw [← lowerBarrierRaw_deriv]
      simpa [X] using
        (lowerBarrierRaw_deriv_eq_zero_at_xplus hκ hgap hD).symm
    exact ((hasDerivAt_iff_tendsto_slope_left_right.mp hraw).2).congr' heq.symm

theorem lowerBarrierPlateau_differentiableAt_xplus
    {κ κtilde D : ℝ}
    (hκ : 0 < κ) (hgap : 0 < κtilde - κ) (hD : 0 < D) :
    DifferentiableAt ℝ (lowerBarrierPlateau κ κtilde D)
      (lowerBarrierXPlus κ κtilde D) :=
  (lowerBarrierPlateau_hasDerivAt_xplus hκ hgap hD).differentiableAt

theorem lowerBarrierPlateau_contDiffAt_two_of_ne_xplus
    {κ κtilde D x : ℝ}
    (hx : x ≠ lowerBarrierXPlus κ κtilde D) :
    ContDiffAt ℝ 2 (lowerBarrierPlateau κ κtilde D) x := by
  rcases lt_or_gt_of_ne hx with hxlt | hxgt
  · exact (contDiff_const : ContDiff ℝ 2
      (fun _ : ℝ => lowerBarrierRaw κ κtilde D
        (lowerBarrierXPlus κ κtilde D))).contDiffAt.congr_of_eventuallyEq
        (lowerBarrierPlateau_eventuallyEq_const_of_lt hxlt)
  · have hraw : ContDiff ℝ 2 (lowerBarrierRaw κ κtilde D) := by
      unfold lowerBarrierRaw
      fun_prop
    exact hraw.contDiffAt.congr_of_eventuallyEq
      (lowerBarrierPlateau_eventuallyEq_raw_of_gt hxgt)

/-- The patched positive lower barrier is a paper subsolution at every point
away from its `C¹` splice.  The left branch uses the new `MChi` constant
budget; the right branch is the already proved positive Lemma 4.2 estimate. -/
theorem paperWaveOperator_lowerBarrierPlateau_nonneg_pos_away
    (p : CMParams) {c κ κtilde D : ℝ} {u : ℝ → ℝ}
    (hcond : PositivePaperLemma42ExactConditions
      p c κ κtilde (MChi p))
    (hD : paperDMin p.χ (MChi p) κ κtilde p.m p.γ c < D)
    (hD1 : 1 ≤ D)
    (hχhalf : p.χ < (1 / 2 : ℝ))
    (hplateau : ∀ x, lowerBarrierPlateau κ κtilde D x ≤
      paper1PositivePlateauFloor p)
    (hu : InWaveTrapSet κ (MChi p) u)
    {x : ℝ} (hx : x ≠ lowerBarrierXPlus κ κtilde D) :
    0 ≤ paperWaveOperator p c u (lowerBarrierPlateau κ κtilde D) x := by
  rcases lt_or_gt_of_ne hx with hxlt | hxgt
  · let d := lowerBarrierRaw κ κtilde D
        (lowerBarrierXPlus κ κtilde D)
    have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD1
    have hd0 : 0 < d := by
      dsimp [d]
      exact lowerBarrierRaw_pos_at_xplus hcond.hκ0
        (sub_pos.mpr hcond.hgap) hDpos
    have hd : d ≤ paper1PositivePlateauFloor p := by
      simpa [d, lowerBarrierPlateau_eq_const_of_le (le_refl
        (lowerBarrierXPlus κ κtilde D))] using
          hplateau (lowerBarrierXPlus κ κtilde D)
    have hconst := paperWaveOperator_const_subsolution_nonneg_pos_MChi
      p (c := c) (κ := κ) hcond.hχ_nonneg hχhalf hcond.hα_eq hd0 hd hu x
    have heq := lowerBarrierPlateau_eventuallyEq_const_of_lt hxlt
    have hval : lowerBarrierPlateau κ κtilde D x = d := by
      rw [lowerBarrierPlateau_eq_const_of_le hxlt.le]
    have hderiv : deriv (lowerBarrierPlateau κ κtilde D) x = 0 := by
      rw [heq.deriv_eq]
      simp
    have hderiv2 : iteratedDeriv 2 (lowerBarrierPlateau κ κtilde D) x = 0 := by
      rw [heq.iteratedDeriv_eq 2]
      simp only [iteratedDeriv_const, show (2 : ℕ) ≠ 0 from by norm_num,
        ite_false]
    have hconst2 : iteratedDeriv 2 (fun _ : ℝ => d) x = 0 := by
      simp only [iteratedDeriv_const, show (2 : ℕ) ≠ 0 from by norm_num,
        ite_false]
    have hopEq :
        paperWaveOperator p c u (lowerBarrierPlateau κ κtilde D) x =
          paperWaveOperator p c u (fun _ => d) x := by
      unfold paperWaveOperator
      dsimp only
      rw [hval, hderiv, hderiv2, hconst2]
      simp
    rw [hopEq]
    exact hconst
  · have hregion : x ∈ Set.Ioi (lowerBarrierXMinus κ κtilde D) := by
      exact lt_trans
        (lowerBarrierXMinus_lt_xplus hcond.hκ0
          (sub_pos.mpr hcond.hgap) (lt_of_lt_of_le zero_lt_one hD1)) hxgt
    have hraw := PaperLemma_4_2_positive_paperWaveOperator_of_conditions
      hcond hD hD1 u hu x hregion
    have heq := lowerBarrierPlateau_eventuallyEq_raw_of_gt hxgt
    have hval : lowerBarrierPlateau κ κtilde D x =
        lowerBarrierRaw κ κtilde D x :=
      lowerBarrierPlateau_eq_raw_of_xplus_lt hxgt
    have hderiv : deriv (lowerBarrierPlateau κ κtilde D) x =
        deriv (lowerBarrierRaw κ κtilde D) x := heq.deriv_eq
    have hderiv2 : iteratedDeriv 2 (lowerBarrierPlateau κ κtilde D) x =
        iteratedDeriv 2 (lowerBarrierRaw κ κtilde D) x :=
      heq.iteratedDeriv_eq 2
    unfold paperWaveOperator at hraw ⊢
    dsimp only
    rw [hval, hderiv, hderiv2]
    exact hraw

section AxiomAudit

#print axioms MChi_rpow_gamma_le_one_div_one_sub_chi
#print axioms paperWaveOperator_const_subsolution_nonneg_pos_MChi
#print axioms exists_positivePlateau_D
#print axioms exists_approx_positive_max_deriv_data_away_C1splice
#print axioms lowerBarrierPlateau_hasDerivAt_xplus
#print axioms paperWaveOperator_lowerBarrierPlateau_nonneg_pos_away

end AxiomAudit

end ShenWork.Paper1
