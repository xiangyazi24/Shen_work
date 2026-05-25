/-
  ShenWork/PDE/TravelingWaveConstruction.lean
  Explicit front profiles used as barriers in the traveling-wave construction.
-/
import ShenWork.Defs
import ShenWork.Paper1.Statements
import Mathlib.Analysis.SpecialFunctions.Sigmoid

open Filter Topology Real

noncomputable section

/-- Capped exponential: min(1, exp(-κx)). Decreasing, 0 < U ≤ 1. -/
def cappedExp (κ : ℝ) : ℝ → ℝ := fun x => min 1 (Real.exp (-(κ * x)))

lemma cappedExp_pos (κ x : ℝ) : 0 < cappedExp κ x :=
  lt_min one_pos (Real.exp_pos _)

lemma cappedExp_le_one (κ x : ℝ) : cappedExp κ x ≤ 1 := by
  exact min_le_left _ _

lemma cappedExp_le_exp (κ x : ℝ) :
    cappedExp κ x ≤ Real.exp (-(κ * x)) := by
  exact min_le_right _ _

lemma cappedExp_continuous (κ : ℝ) : Continuous (cappedExp κ) := by
  have hlin : Continuous fun x : ℝ => -(κ * x) := by
    fun_prop
  simpa [cappedExp] using continuous_const.min (Real.continuous_exp.comp hlin)

lemma cappedExp_isBddFun (κ : ℝ) : IsBddFun (cappedExp κ) := by
  refine ⟨1, fun x => ?_⟩
  have hnonneg : 0 ≤ cappedExp κ x := (cappedExp_pos κ x).le
  have hle : cappedExp κ x ≤ 1 := cappedExp_le_one κ x
  simpa [abs_of_nonneg hnonneg] using hle

lemma cappedExp_isCUnifBdd (κ : ℝ) : IsCUnifBdd (cappedExp κ) :=
  ⟨cappedExp_continuous κ, cappedExp_isBddFun κ⟩

lemma cappedExp_tendsto_atTop {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (cappedExp κ) atTop (𝓝 0) := by
  have hmul : Tendsto (fun x : ℝ => κ * x) atTop atTop :=
    (Filter.tendsto_id.atTop_mul_const hκ).congr (fun x => mul_comm x κ)
  have hexp : Tendsto (fun x => Real.exp (-(κ * x))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (Filter.tendsto_neg_atTop_atBot.comp hmul)
  exact squeeze_zero (fun x => le_of_lt (cappedExp_pos κ x))
    (fun x => min_le_right _ _) hexp

lemma cappedExp_tendsto_atBot {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (cappedExp κ) atBot (𝓝 1) := by
  suffices h : ∀ᶠ x in atBot, cappedExp κ x = 1 from
    tendsto_const_nhds.congr' (h.mono fun x hx => hx.symm)
  exact Filter.eventually_atBot.mpr ⟨0, fun x hx => by
    show cappedExp κ x = 1; unfold cappedExp
    have h1 : 0 ≤ -(κ * x) := by nlinarith [mul_nonpos_of_nonneg_of_nonpos (le_of_lt hκ) hx]
    exact min_eq_left (by linarith [Real.add_one_le_exp (-(κ * x))])⟩

lemma cappedExp_deriv_nonpos {κ : ℝ} (hκ : 0 < κ) (x : ℝ) :
    deriv (cappedExp κ) x ≤ 0 := by
  have hEqOn_nonpos : Set.EqOn (cappedExp κ) (fun _ => (1 : ℝ)) (Set.Iic 0) := by
    intro y hy; unfold cappedExp
    exact min_eq_left (Real.one_le_exp (neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hκ.le hy)))
  have hEqOn_nonneg : Set.EqOn (cappedExp κ) (fun y => Real.exp (-(κ * y))) (Set.Ici 0) := by
    intro y hy; unfold cappedExp
    have : Real.exp (-(κ * y)) ≤ 1 := by
      simpa [Real.exp_zero] using Real.exp_le_exp.mpr (neg_nonpos.mpr (mul_nonneg hκ.le hy))
    exact min_eq_right this
  have hExpDeriv : ∀ z, HasDerivAt (fun y => Real.exp (-(κ * y))) (Real.exp (-(κ * z)) * (-κ)) z :=
    fun z => by simpa using ((hasDerivAt_id z).const_mul κ).neg.exp
  by_cases hx0 : x = 0
  · subst hx0
    have hnot : ¬DifferentiableAt ℝ (cappedExp κ) 0 := by
      intro hdiff
      have hdl := hdiff.derivWithin (uniqueDiffWithinAt_Iic (0 : ℝ))
      have hdr := hdiff.derivWithin (uniqueDiffWithinAt_Ici (0 : ℝ))
      rw [derivWithin_congr hEqOn_nonpos (by simp [cappedExp])] at hdl
      rw [derivWithin_congr hEqOn_nonneg (by simp [cappedExp])] at hdr
      simp at hdl
      have := (hExpDeriv 0).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici (0 : ℝ))
      simp at this; rw [this] at hdr; linarith
    rw [deriv_zero_of_not_differentiableAt hnot]
  · by_cases hxpos : 0 < x
    · have hder : deriv (cappedExp κ) x = deriv (fun y => Real.exp (-(κ * y))) x :=
        ((hEqOn_nonneg.mono Set.Ioi_subset_Ici_self).deriv isOpen_Ioi) hxpos
      rw [hder, (hExpDeriv x).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (neg_nonpos.mpr hκ.le)
    · have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hxpos) hx0
      have hder : deriv (cappedExp κ) x = deriv (fun _ => (1 : ℝ)) x :=
        ((hEqOn_nonpos.mono Set.Iio_subset_Iic_self).deriv isOpen_Iio) hxneg
      simp [hder]

theorem cappedExp_facts_with_isCUnifBdd {κ : ℝ} (hκ : 0 < κ) :
    ∃ U : ℝ → ℝ,
      U = cappedExp κ ∧
      IsCUnifBdd U ∧
      (∀ x, 0 < U x) ∧
      (∀ x, U x ≤ 1) ∧
      Tendsto U atBot (𝓝 1) ∧
      Tendsto U atTop (𝓝 0) ∧
      (∀ x, deriv U x ≤ 0) := by
  exact ⟨cappedExp κ, rfl, cappedExp_isCUnifBdd κ,
    fun x => cappedExp_pos κ x,
    fun x => cappedExp_le_one κ x,
    cappedExp_tendsto_atBot hκ,
    cappedExp_tendsto_atTop hκ,
    fun x => cappedExp_deriv_nonpos hκ x⟩

/-- Smooth logistic profile connecting 1 at -∞ to 0 at +∞. -/
def logisticProfile (κ : ℝ) : ℝ → ℝ := fun x => Real.sigmoid (-(κ * x))

lemma logisticProfile_pos (κ x : ℝ) : 0 < logisticProfile κ x := by
  simpa [logisticProfile] using Real.sigmoid_pos (-(κ * x))

lemma logisticProfile_lt_one (κ x : ℝ) : logisticProfile κ x < 1 := by
  simpa [logisticProfile] using Real.sigmoid_lt_one (-(κ * x))

lemma logisticProfile_le_exp (κ x : ℝ) :
    logisticProfile κ x ≤ Real.exp (-(κ * x)) := by
  have hmul :
      Real.sigmoid (-(κ * x)) * Real.exp (κ * x) =
        Real.sigmoid (κ * x) := by
    simpa using Real.sigmoid_mul_rexp_neg (-(κ * x))
  have hcancel : Real.exp (κ * x) * Real.exp (-(κ * x)) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  calc
    logisticProfile κ x =
        (Real.sigmoid (-(κ * x)) * Real.exp (κ * x)) *
          Real.exp (-(κ * x)) := by
          simp [logisticProfile, mul_assoc, hcancel]
    _ = Real.sigmoid (κ * x) * Real.exp (-(κ * x)) := by
      rw [hmul]
    _ ≤ 1 * Real.exp (-(κ * x)) := by
      exact mul_le_mul_of_nonneg_right (Real.sigmoid_le_one (κ * x))
        (Real.exp_nonneg _)
    _ = Real.exp (-(κ * x)) := by simp

lemma logisticProfile_lt_exp (κ x : ℝ) :
    logisticProfile κ x < Real.exp (-(κ * x)) := by
  have hpos : 0 < Real.exp (κ * x) := Real.exp_pos _
  have hlt : Real.exp (κ * x) < 1 + Real.exp (κ * x) := by linarith
  have hsum : 0 < 1 + Real.exp (κ * x) := by positivity
  have hinv : (1 + Real.exp (κ * x))⁻¹ < (Real.exp (κ * x))⁻¹ :=
    (inv_lt_inv₀ hsum hpos).2 hlt
  have hexp_inv : (Real.exp (κ * x))⁻¹ = Real.exp (-(κ * x)) := by
    simpa using (Real.exp_neg (κ * x)).symm
  simpa [logisticProfile, Real.sigmoid_def, hexp_inv] using hinv

lemma logisticProfile_le_cappedExp {κ : ℝ} (hκ : 0 < κ) (x : ℝ) :
    logisticProfile κ x ≤ cappedExp κ x := by
  by_cases hx : 0 ≤ x
  · have hexp_le_one : Real.exp (-(κ * x)) ≤ 1 := by
      simpa [Real.exp_zero] using
        Real.exp_le_exp.mpr (neg_nonpos.mpr (mul_nonneg hκ.le hx))
    rw [cappedExp, min_eq_right hexp_le_one]
    exact logisticProfile_le_exp κ x
  · have hxle : x ≤ 0 := le_of_lt (lt_of_not_ge hx)
    have hone_le_exp : 1 ≤ Real.exp (-(κ * x)) := by
      exact Real.one_le_exp (neg_nonneg.mpr
        (mul_nonpos_of_nonneg_of_nonpos hκ.le hxle))
    rw [cappedExp, min_eq_left hone_le_exp]
    exact (logisticProfile_lt_one κ x).le

lemma logisticProfile_lt_cappedExp {κ : ℝ} (hκ : 0 < κ) (x : ℝ) :
    logisticProfile κ x < cappedExp κ x := by
  by_cases hx : 0 ≤ x
  · have hexp_le_one : Real.exp (-(κ * x)) ≤ 1 := by
      simpa [Real.exp_zero] using
        Real.exp_le_exp.mpr (neg_nonpos.mpr (mul_nonneg hκ.le hx))
    rw [cappedExp, min_eq_right hexp_le_one]
    exact logisticProfile_lt_exp κ x
  · have hxle : x ≤ 0 := le_of_lt (lt_of_not_ge hx)
    have hone_le_exp : 1 ≤ Real.exp (-(κ * x)) := by
      exact Real.one_le_exp (neg_nonneg.mpr
        (mul_nonpos_of_nonneg_of_nonpos hκ.le hxle))
    rw [cappedExp, min_eq_left hone_le_exp]
    exact logisticProfile_lt_one κ x

lemma logisticProfile_tendsto_atTop {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (logisticProfile κ) atTop (𝓝 0) := by
  have hmul : Tendsto (fun x : ℝ => κ * x) atTop atTop :=
    (Filter.tendsto_id.atTop_mul_const hκ).congr (fun x => mul_comm x κ)
  have hneg : Tendsto (fun x : ℝ => -(κ * x)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hmul
  exact Real.tendsto_sigmoid_atBot.comp hneg

lemma logisticProfile_tendsto_atBot {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (logisticProfile κ) atBot (𝓝 1) := by
  have hmul : Tendsto (fun x : ℝ => κ * x) atBot atBot :=
    (Filter.tendsto_id.atBot_mul_const hκ).congr (fun x => mul_comm x κ)
  have hneg : Tendsto (fun x : ℝ => -(κ * x)) atBot atTop :=
    tendsto_neg_atBot_atTop.comp hmul
  exact Real.tendsto_sigmoid_atTop.comp hneg

lemma logisticProfile_antitone {κ : ℝ} (hκ : 0 < κ) :
    Antitone (logisticProfile κ) := by
  intro a b hab
  simp only [logisticProfile]
  exact Real.sigmoid_le (neg_le_neg (mul_le_mul_of_nonneg_left hab hκ.le))

lemma logisticProfile_deriv_nonpos {κ : ℝ} (hκ : 0 < κ) (x : ℝ) :
    deriv (logisticProfile κ) x ≤ 0 :=
  (logisticProfile_antitone hκ).deriv_nonpos

lemma logisticProfile_hasDerivAt (κ x : ℝ) :
    HasDerivAt (logisticProfile κ)
      (-κ * logisticProfile κ x * (1 - logisticProfile κ x)) x := by
  have hinner : HasDerivAt (fun y : ℝ => -(κ * y)) (-κ) x := by
    simpa using ((hasDerivAt_id x).const_mul κ).neg
  simpa [logisticProfile, Function.comp_def, mul_assoc, mul_left_comm, mul_comm] using
    (Real.hasDerivAt_sigmoid (-(κ * x))).comp x hinner

lemma logisticProfile_deriv (κ x : ℝ) :
    deriv (logisticProfile κ) x =
      -κ * logisticProfile κ x * (1 - logisticProfile κ x) :=
  (logisticProfile_hasDerivAt κ x).deriv

lemma logisticProfile_deriv_neg {κ : ℝ} (hκ : 0 < κ) (x : ℝ) :
    deriv (logisticProfile κ) x < 0 := by
  rw [logisticProfile_deriv]
  have hpos : 0 < logisticProfile κ x := logisticProfile_pos κ x
  have hone : 0 < 1 - logisticProfile κ x :=
    sub_pos.mpr (logisticProfile_lt_one κ x)
  have hleft : -κ * logisticProfile κ x < 0 :=
    mul_neg_of_neg_of_pos (neg_lt_zero.mpr hκ) hpos
  exact mul_neg_of_neg_of_pos hleft hone

lemma logisticProfile_contDiff (κ : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (logisticProfile κ) := by
  have hlin : ContDiff ℝ n (fun x : ℝ => -(κ * x)) := by
    fun_prop
  simpa [logisticProfile, Function.comp_def] using (contDiff_sigmoid.of_le le_top).comp hlin

lemma logisticProfile_contDiff_two (κ : ℝ) :
    ContDiff ℝ 2 (logisticProfile κ) :=
  logisticProfile_contDiff κ

lemma logisticProfile_isBddFun (κ : ℝ) :
    IsBddFun (logisticProfile κ) := by
  refine ⟨1, fun x => ?_⟩
  have hnonneg : 0 ≤ logisticProfile κ x := (logisticProfile_pos κ x).le
  have hle : logisticProfile κ x ≤ 1 := (logisticProfile_lt_one κ x).le
  simpa [abs_of_nonneg hnonneg] using hle

lemma logisticProfile_isCUnifBdd (κ : ℝ) :
    IsCUnifBdd (logisticProfile κ) :=
  ⟨(logisticProfile_contDiff_two κ).continuous, logisticProfile_isBddFun κ⟩

structure LogisticProfileFacts (κ : ℝ) where
  U : ℝ → ℝ
  U_def : U = logisticProfile κ
  U_pos : ∀ x, 0 < U x
  U_lt_one : ∀ x, U x < 1
  U_lim_neg_inf : Tendsto U atBot (𝓝 1)
  U_lim_pos_inf : Tendsto U atTop (𝓝 0)
  U_deriv_nonpos : ∀ x, deriv U x ≤ 0

def logisticProfile_facts {κ : ℝ} (hκ : 0 < κ) :
    LogisticProfileFacts κ := by
  exact {
    U := logisticProfile κ
    U_def := rfl
    U_pos := fun x => logisticProfile_pos κ x
    U_lt_one := fun x => logisticProfile_lt_one κ x
    U_lim_neg_inf := logisticProfile_tendsto_atBot hκ
    U_lim_pos_inf := logisticProfile_tendsto_atTop hκ
    U_deriv_nonpos := fun x => logisticProfile_deriv_nonpos hκ x
  }

lemma LogisticProfileFacts.U_contDiff_two {κ : ℝ} (F : LogisticProfileFacts κ) :
    ContDiff ℝ 2 F.U := by
  simpa [F.U_def] using logisticProfile_contDiff_two κ

lemma LogisticProfileFacts.U_isCUnifBdd {κ : ℝ} (F : LogisticProfileFacts κ) :
    IsCUnifBdd F.U := by
  simpa [F.U_def] using logisticProfile_isCUnifBdd κ

lemma logisticProfile_strict_exp_bound (κ x : ℝ) :
    logisticProfile κ x < max 1 (Real.exp (-κ * x)) := by
  exact (logisticProfile_lt_one κ x).trans_le (le_max_left _ _)

theorem logisticProfile_facts_with_exp_bound {κ : ℝ} (hκ : 0 < κ) :
    ∃ F : LogisticProfileFacts κ,
      F.U = logisticProfile κ ∧
      (∀ x, 0 < F.U x) ∧
      (∀ x, F.U x < max 1 (Real.exp (-κ * x))) := by
  refine ⟨logisticProfile_facts hκ, rfl, ?_, ?_⟩
  · exact fun x => logisticProfile_pos κ x
  · exact fun x => logisticProfile_strict_exp_bound κ x

theorem logisticProfile_facts_with_contDiff {κ : ℝ} (hκ : 0 < κ) :
    ∃ F : LogisticProfileFacts κ,
      F.U = logisticProfile κ ∧
      ContDiff ℝ 2 F.U ∧
      (∀ x, 0 < F.U x) ∧
      (∀ x, F.U x < 1) ∧
      (∀ x, deriv F.U x ≤ 0) := by
  refine ⟨logisticProfile_facts hκ, rfl, ?_, ?_, ?_, ?_⟩
  · exact LogisticProfileFacts.U_contDiff_two (logisticProfile_facts hκ)
  · exact fun x => logisticProfile_pos κ x
  · exact fun x => logisticProfile_lt_one κ x
  · exact fun x => logisticProfile_deriv_nonpos hκ x

theorem logisticProfile_facts_with_isCUnifBdd {κ : ℝ} (hκ : 0 < κ) :
    ∃ F : LogisticProfileFacts κ,
      F.U = logisticProfile κ ∧
      IsCUnifBdd F.U ∧
      (∀ x, 0 < F.U x) ∧
      (∀ x, F.U x < 1) ∧
      (∀ x, deriv F.U x ≤ 0) := by
  refine ⟨logisticProfile_facts hκ, rfl, ?_, ?_, ?_, ?_⟩
  · exact LogisticProfileFacts.U_isCUnifBdd (logisticProfile_facts hκ)
  · exact fun x => logisticProfile_pos κ x
  · exact fun x => logisticProfile_lt_one κ x
  · exact fun x => logisticProfile_deriv_nonpos hκ x

theorem logisticProfile_facts_with_contDiff_exp_bound_and_strict_deriv
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ F : LogisticProfileFacts κ,
      F.U = logisticProfile κ ∧
      ContDiff ℝ 2 F.U ∧
      (∀ x, 0 < F.U x) ∧
      (∀ x, F.U x < max 1 (Real.exp (-κ * x))) ∧
      (∀ x, deriv F.U x < 0) := by
  refine ⟨logisticProfile_facts hκ, rfl, ?_, ?_, ?_, ?_⟩
  · exact LogisticProfileFacts.U_contDiff_two (logisticProfile_facts hκ)
  · exact fun x => logisticProfile_pos κ x
  · exact fun x => logisticProfile_strict_exp_bound κ x
  · exact fun x => logisticProfile_deriv_neg hκ x

theorem logisticProfile_facts_with_cappedExp_bound {κ : ℝ} (hκ : 0 < κ) :
    ∃ F : LogisticProfileFacts κ,
      F.U = logisticProfile κ ∧
      IsCUnifBdd F.U ∧
      (∀ x, 0 < F.U x) ∧
      (∀ x, F.U x ≤ cappedExp κ x) ∧
      (∀ x, deriv F.U x < 0) := by
  refine ⟨logisticProfile_facts hκ, rfl, ?_, ?_, ?_, ?_⟩
  · exact LogisticProfileFacts.U_isCUnifBdd (logisticProfile_facts hκ)
  · exact fun x => logisticProfile_pos κ x
  · exact fun x => logisticProfile_le_cappedExp hκ x
  · exact fun x => logisticProfile_deriv_neg hκ x

theorem logisticProfile_shenUpperBoundPositive
    {p : CMParams} {c : ℝ}
    (hχ_nonneg : 0 ≤ p.χ) (hχ_lt : p.χ < 1) :
    ShenWork.Paper1.ShenUpperBoundPositive p c
      (logisticProfile (kappa c)) := by
  intro x
  have hone_le :
      1 ≤ (1 / (1 - p.χ)) ^ (1 / p.α) := by
    have hM := ShenWork.Paper1.one_le_MChi_of_chi_nonneg_lt_one
      p hχ_nonneg hχ_lt
    rwa [ShenWork.Paper1.MChi_eq_rpow_of_chi_nonneg_lt_one
      p hχ_nonneg hχ_lt] at hM
  refine ⟨logisticProfile_pos (kappa c) x, ?_⟩
  apply lt_min
  · exact (logisticProfile_lt_one (kappa c) x).trans_le hone_le
  · simpa [neg_mul] using logisticProfile_lt_exp (kappa c) x

theorem logisticProfile_hasStrictWaveUpperTailBound
    {p : CMParams} {c : ℝ}
    (hχ_nonneg : 0 ≤ p.χ) (hχ_lt : p.χ < 1) :
    ShenWork.Paper1.HasStrictWaveUpperTailBound p c
      (logisticProfile (kappa c)) :=
  ShenWork.Paper1.ShenUpperBoundPositive.hasStrictWaveUpperTailBound
    (logisticProfile_shenUpperBoundPositive hχ_nonneg hχ_lt)
    hχ_nonneg hχ_lt

theorem logisticProfile_tail_bounds
    {p : CMParams} {c : ℝ}
    (hχ_nonneg : 0 ≤ p.χ) (hχ_lt : p.χ < 1) :
    ShenWork.Paper1.ShenUpperBoundPositive p c
        (logisticProfile (kappa c)) ∧
      ShenWork.Paper1.HasStrictWaveUpperTailBound p c
        (logisticProfile (kappa c)) ∧
      ShenWork.Paper1.HasWaveUpperTailBound p c
        (logisticProfile (kappa c)) := by
  let hupper := logisticProfile_shenUpperBoundPositive
    (p := p) (c := c) hχ_nonneg hχ_lt
  let hstrict :=
    ShenWork.Paper1.ShenUpperBoundPositive.hasStrictWaveUpperTailBound
      hupper hχ_nonneg hχ_lt
  exact ⟨hupper, hstrict, hstrict.hasWaveUpperTailBound⟩

end
