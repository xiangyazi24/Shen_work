/-
  ShenWork/PDE/TravelingWaveConstruction.lean
  Explicit front profiles used as barriers in the traveling-wave construction.
-/
import ShenWork.Defs
import Mathlib.Analysis.SpecialFunctions.Sigmoid

open Filter Topology Real

noncomputable section

/-- Capped exponential: min(1, exp(-κx)). Decreasing, 0 < U ≤ 1. -/
def cappedExp (κ : ℝ) : ℝ → ℝ := fun x => min 1 (Real.exp (-(κ * x)))

lemma cappedExp_pos (κ x : ℝ) : 0 < cappedExp κ x :=
  lt_min one_pos (Real.exp_pos _)

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

/-- Smooth logistic profile connecting 1 at -∞ to 0 at +∞. -/
def logisticProfile (κ : ℝ) : ℝ → ℝ := fun x => Real.sigmoid (-(κ * x))

lemma logisticProfile_pos (κ x : ℝ) : 0 < logisticProfile κ x := by
  simpa [logisticProfile] using Real.sigmoid_pos (-(κ * x))

lemma logisticProfile_lt_one (κ x : ℝ) : logisticProfile κ x < 1 := by
  simpa [logisticProfile] using Real.sigmoid_lt_one (-(κ * x))

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

end
