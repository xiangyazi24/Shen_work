import ShenWork.Paper1.Theorem12WeightedResolverEta

open Filter MeasureTheory Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Elementary logistic exhaustion for the weighted core

For fixed `R`, `capWeight eta R` agrees asymptotically with the exponential
weight on the left and is bounded by its plateau `exp (2 * eta * R)` on the
right.  Increasing `R` exhausts the full exponential weight monotonically.
-/

/-- The elementary logistic exhaustion of `exp (2 * eta * z)`. -/
def capWeight (eta R z : ℝ) : ℝ :=
  Real.exp (2 * eta * z) / (1 + Real.exp (2 * eta * (z - R)))

theorem capWeight_pos (eta R z : ℝ) :
    0 < capWeight eta R z := by
  unfold capWeight
  positivity

theorem capWeight_continuous (eta R : ℝ) :
    Continuous (capWeight eta R) := by
  unfold capWeight
  apply Continuous.div₀
  · fun_prop
  · fun_prop
  · intro z
    positivity

theorem capWeight_le_full (eta R z : ℝ) :
    capWeight eta R z ≤ Real.exp (2 * eta * z) := by
  unfold capWeight
  apply div_le_self (Real.exp_pos _).le
  nlinarith [Real.exp_pos (2 * eta * (z - R))]

theorem capWeight_le_plateau (eta R z : ℝ) :
    capWeight eta R z ≤ Real.exp (2 * eta * R) := by
  unfold capWeight
  rw [div_le_iff₀ (by positivity : 0 < 1 + Real.exp (2 * eta * (z - R)))]
  rw [show Real.exp (2 * eta * z) =
      Real.exp (2 * eta * R) * Real.exp (2 * eta * (z - R)) by
    rw [← Real.exp_add]
    congr 1
    ring]
  nlinarith [Real.exp_pos (2 * eta * R),
    Real.exp_pos (2 * eta * (z - R))]

theorem capWeight_mono_R {eta : ℝ} (heta : 0 ≤ eta) (z : ℝ) :
    Monotone (fun R => capWeight eta R z) := by
  intro R₁ R₂ hR
  unfold capWeight
  have hexp : Real.exp (2 * eta * (z - R₂)) ≤
      Real.exp (2 * eta * (z - R₁)) := by
    exact Real.exp_le_exp.mpr (by nlinarith)
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity) (by linarith)

theorem capWeight_tendsto_full {eta : ℝ} (heta : 0 < eta) (z : ℝ) :
    Tendsto (fun R => capWeight eta R z) atTop
      (nhds (Real.exp (2 * eta * z))) := by
  have hlinear : Tendsto (fun R : ℝ => 2 * eta * (z - R)) atTop atBot := by
    have hneg : -2 * eta < 0 := by linarith
    have hbase : Tendsto (fun R : ℝ => (-2 * eta) * R + 2 * eta * z)
        atTop atBot :=
      tendsto_atBot_add_const_right _ (2 * eta * z)
        (tendsto_id.const_mul_atTop_of_neg hneg)
    convert hbase using 1
    funext R
    ring
  have hexp : Tendsto (fun R : ℝ => Real.exp (2 * eta * (z - R)))
      atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp hlinear
  have hden : Tendsto
      (fun R : ℝ => 1 + Real.exp (2 * eta * (z - R)))
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hexp
  have hnum : Tendsto (fun _ : ℝ => Real.exp (2 * eta * z)) atTop
      (nhds (Real.exp (2 * eta * z))) := tendsto_const_nhds
  unfold capWeight
  simpa using hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)

theorem capWeight_hasDerivAt (eta R z : ℝ) :
    HasDerivAt (capWeight eta R)
      (2 * eta * capWeight eta R z /
        (1 + Real.exp (2 * eta * (z - R)))) z := by
  have hnum : HasDerivAt (fun y : ℝ => Real.exp (2 * eta * y))
      (2 * eta * Real.exp (2 * eta * z)) z := by
    simpa [mul_comm] using ((hasDerivAt_id z).const_mul (2 * eta)).exp
  have hinner : HasDerivAt (fun y : ℝ => 2 * eta * (y - R))
      (2 * eta) z := by
    convert ((hasDerivAt_id z).sub_const R).const_mul (2 * eta) using 1
    all_goals ring
  have hden : HasDerivAt
      (fun y : ℝ => 1 + Real.exp (2 * eta * (y - R)))
      (2 * eta * Real.exp (2 * eta * (z - R))) z := by
    convert hinner.exp.const_add 1 using 1
    all_goals ring
  have hquot := hnum.div hden (by positivity :
    1 + Real.exp (2 * eta * (z - R)) ≠ 0)
  convert hquot using 1
  · unfold capWeight
    field_simp
    ring

theorem capWeight_deriv_eq (eta R z : ℝ) :
    deriv (capWeight eta R) z =
      2 * eta * capWeight eta R z /
        (1 + Real.exp (2 * eta * (z - R))) :=
  (capWeight_hasDerivAt eta R z).deriv

theorem capWeight_abs_deriv_le
    {eta : ℝ} (heta : 0 ≤ eta) (R z : ℝ) :
    |deriv (capWeight eta R) z| ≤ 2 * eta * capWeight eta R z := by
  rw [capWeight_deriv_eq, abs_of_nonneg (div_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) heta) (capWeight_pos eta R z).le)
    (by positivity))]
  have hden : 1 ≤ 1 + Real.exp (2 * eta * (z - R)) :=
    le_add_of_nonneg_right (Real.exp_pos _).le
  exact div_le_self (mul_nonneg (mul_nonneg (by norm_num) heta)
    (capWeight_pos eta R z).le) hden

/-- Exact second derivative formula for the logistic exhaustion. -/
theorem capWeight_hasSecondDerivAt (eta R z : ℝ) :
    HasDerivAt (fun y => deriv (capWeight eta R) y)
      (4 * eta ^ 2 * capWeight eta R z *
        (1 - Real.exp (2 * eta * (z - R))) /
          (1 + Real.exp (2 * eta * (z - R))) ^ 2) z := by
  have hfun : (fun y => deriv (capWeight eta R) y) =
      fun y => 2 * eta * capWeight eta R y /
        (1 + Real.exp (2 * eta * (y - R))) := by
    funext y
    exact capWeight_deriv_eq eta R y
  rw [hfun]
  have hnum := (capWeight_hasDerivAt eta R z).const_mul (2 * eta)
  have hinner : HasDerivAt (fun y : ℝ => 2 * eta * (y - R))
      (2 * eta) z := by
    convert ((hasDerivAt_id z).sub_const R).const_mul (2 * eta) using 1
    all_goals ring
  have hden : HasDerivAt
      (fun y : ℝ => 1 + Real.exp (2 * eta * (y - R)))
      (2 * eta * Real.exp (2 * eta * (z - R))) z := by
    convert hinner.exp.const_add 1 using 1
    all_goals ring
  convert hnum.div hden (by positivity :
      1 + Real.exp (2 * eta * (z - R)) ≠ 0) using 1
  field_simp
  ring

theorem capWeight_abs_secondDeriv_le
    {eta : ℝ} (_heta : 0 ≤ eta) (R z : ℝ) :
    |deriv (fun y => deriv (capWeight eta R) y) z| ≤
      6 * eta ^ 2 * capWeight eta R z := by
  rw [(capWeight_hasSecondDerivAt eta R z).deriv]
  have he : 0 < Real.exp (2 * eta * (z - R)) := Real.exp_pos _
  have habs : |1 - Real.exp (2 * eta * (z - R))| ≤
      1 + Real.exp (2 * eta * (z - R)) := by
    rw [abs_sub_le_iff]
    constructor <;> linarith
  have hden : 0 < 1 + Real.exp (2 * eta * (z - R)) := by positivity
  rw [abs_div, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 4 * eta ^ 2),
    abs_of_pos (capWeight_pos eta R z), abs_of_pos (sq_pos_of_pos hden)]
  have hfour :
      4 * eta ^ 2 * capWeight eta R z *
          |1 - Real.exp (2 * eta * (z - R))| /
            (1 + Real.exp (2 * eta * (z - R))) ^ 2 ≤
        4 * eta ^ 2 * capWeight eta R z := by
    rw [div_le_iff₀ (sq_pos_of_pos hden)]
    have hnonneg : 0 ≤ 4 * eta ^ 2 * capWeight eta R z :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg eta))
        (capWeight_pos eta R z).le
    calc
      4 * eta ^ 2 * capWeight eta R z *
          |1 - Real.exp (2 * eta * (z - R))| ≤
          4 * eta ^ 2 * capWeight eta R z *
            (1 + Real.exp (2 * eta * (z - R))) :=
        mul_le_mul_of_nonneg_left habs hnonneg
      _ ≤ 4 * eta ^ 2 * capWeight eta R z *
            (1 + Real.exp (2 * eta * (z - R))) ^ 2 := by
        gcongr
        nlinarith
  calc
    4 * eta ^ 2 * capWeight eta R z *
          |1 - Real.exp (2 * eta * (z - R))| /
            (1 + Real.exp (2 * eta * (z - R))) ^ 2 ≤
        4 * eta ^ 2 * capWeight eta R z := hfour
    _ ≤ 6 * eta ^ 2 * capWeight eta R z := by
      have hnonneg : 0 ≤ eta ^ 2 * capWeight eta R z :=
        mul_nonneg (sq_nonneg eta) (capWeight_pos eta R z).le
      nlinarith

/-! ## Pointwise difference equation -/

/-- The population flux difference in co-moving coordinates. -/
def coMovingFluxDifference
    (p : CMParams) (c : ℝ) (u v : ℝ → ℝ → ℝ) (U V : ℝ → ℝ)
    (t z : ℝ) : ℝ :=
  (coMovingPath c u t z) ^ p.m * deriv (coMovingPath c v t) z -
    (U z) ^ p.m * deriv V z

/-- The logistic reaction difference in co-moving coordinates. -/
def coMovingReactionDifference
    (p : CMParams) (c : ℝ) (u : ℝ → ℝ → ℝ) (U : ℝ → ℝ)
    (t z : ℝ) : ℝ :=
  coMovingPath c u t z * (1 - (coMovingPath c u t z) ^ p.α) -
    U z * (1 - (U z) ^ p.α)

/-- The classical population equation minus the traveling-wave equation,
kept in divergence form. -/
theorem differencePDE_divergence
    (p : CMParams) {T c t z : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hsol : IsClassicalSolution p T u v) (ht0 : 0 < t) (htT : t < T)
    (hTW : IsTravelingWave p c U V)
    (hu2 : ContDiff ℝ 2 (coMovingPath c u t))
    (hv2 : ContDiff ℝ 2 (coMovingPath c v t))
    (hU2 : ContDiff ℝ 2 U) (hV2 : ContDiff ℝ 2 V) :
    paper5CoMovingMaterialTime c u t z =
      iteratedDeriv 2 (fun y => coMovingPath c u t y - U y) z +
        c * deriv (fun y => coMovingPath c u t y - U y) z -
        p.χ * deriv (coMovingFluxDifference p c u v U V t) z +
        coMovingReactionDifference p c u U t z := by
  have hpde := paper5CoMovingMaterialPDE_of_classical p hsol ht0 htT
    (c := c) (x := z)
  have hsecond :
      iteratedDeriv 2 (fun y => coMovingPath c u t y - U y) z =
        iteratedDeriv 2 (coMovingPath c u t) z - iteratedDeriv 2 U z :=
    iteratedDeriv_fun_sub hu2.contDiffAt hU2.contDiffAt
  have hfirst :
      deriv (fun y => coMovingPath c u t y - U y) z =
        deriv (coMovingPath c u t) z - deriv U z :=
    deriv_sub (hu2.differentiable (by norm_num) z)
      (hU2.differentiable (by norm_num) z)
  have hv2' : ContDiff ℝ ((1 : WithTop ℕ∞) + 1) (coMovingPath c v t) := by
    simpa using hv2
  have hV2' : ContDiff ℝ ((1 : WithTop ℕ∞) + 1) V := by
    simpa using hV2
  have hdv : Differentiable ℝ (deriv (coMovingPath c v t)) :=
    ((contDiff_succ_iff_deriv.mp hv2').2.2).differentiable (by norm_num)
  have hdV : Differentiable ℝ (deriv V) :=
    ((contDiff_succ_iff_deriv.mp hV2').2.2).differentiable (by norm_num)
  have hflux_u : DifferentiableAt ℝ
      (fun y => (coMovingPath c u t y) ^ p.m *
        deriv (coMovingPath c v t) y) z :=
    ((hu2.differentiable (by norm_num) z).rpow_const (Or.inr p.hm)).mul
      (hdv z)
  have hflux_U : DifferentiableAt ℝ
      (fun y => (U y) ^ p.m * deriv V y) z :=
    ((hU2.differentiable (by norm_num) z).rpow_const (Or.inr p.hm)).mul
      (hdV z)
  have hflux :
      deriv (coMovingFluxDifference p c u v U V t) z =
        deriv (fun y => (coMovingPath c u t y) ^ p.m *
          deriv (coMovingPath c v t) y) z -
        deriv (fun y => (U y) ^ p.m * deriv V y) z := by
    unfold coMovingFluxDifference
    exact deriv_sub hflux_u hflux_U
  rw [hsecond, hfirst, hflux]
  unfold coMovingReactionDifference
  linarith [hTW.ode_U z]

/-! ## Fixed-cap integrability -/

/-- Full exponential integrability dominates every fixed logistic cap. -/
theorem capWeight_mul_sq_integrable_of_full
    {eta R : ℝ} {w : ℝ → ℝ} (hw : Continuous w)
    (hfull : Integrable (fun z => Real.exp (2 * eta * z) * |w z| ^ 2)) :
    Integrable (fun z => capWeight eta R z * |w z| ^ 2) := by
  refine hfull.mono'
    ((capWeight_continuous eta R).mul (hw.abs.pow 2)).aestronglyMeasurable ?_
  filter_upwards with z
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (capWeight_pos eta R z).le (sq_nonneg _))]
  exact mul_le_mul_of_nonneg_right (capWeight_le_full eta R z) (sq_nonneg _)

/-- The exact split needed for fixed-cap finiteness: exponential `L²` on the
left and ordinary `L²` on the right. -/
theorem capWeight_mul_sq_integrable_of_split
    {eta R a : ℝ} {w : ℝ → ℝ} (hw : Continuous w)
    (hleft : IntegrableOn
      (fun z => Real.exp (2 * eta * z) * |w z| ^ 2) (Iic a))
    (hright : IntegrableOn (fun z => |w z| ^ 2) (Ioi a)) :
    Integrable (fun z => capWeight eta R z * |w z| ^ 2) := by
  let f : ℝ → ℝ := fun z => capWeight eta R z * |w z| ^ 2
  have hf : Continuous f :=
    (capWeight_continuous eta R).mul (hw.abs.pow 2)
  have hfleft : IntegrableOn f (Iic a) := by
    refine hleft.mono'
      (hf.aestronglyMeasurable.mono_measure Measure.restrict_le_self) ?_
    filter_upwards with z
    rw [show f z = capWeight eta R z * |w z| ^ 2 by rfl,
      Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (capWeight_pos eta R z).le (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right (capWeight_le_full eta R z) (sq_nonneg _)
  have hfright : IntegrableOn f (Ioi a) := by
    have hdom : IntegrableOn
        (fun z => Real.exp (2 * eta * R) * |w z| ^ 2) (Ioi a) :=
      hright.const_mul _
    refine hdom.mono'
      (hf.aestronglyMeasurable.mono_measure Measure.restrict_le_self) ?_
    filter_upwards with z
    rw [show f z = capWeight eta R z * |w z| ^ 2 by rfl,
      Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (capWeight_pos eta R z).le (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right (capWeight_le_plateau eta R z) (sq_nonneg _)
  have hunion : IntegrableOn f (Iic a ∪ Ioi a) := hfleft.union hfright
  rw [Iic_union_Ioi, IntegrableOn, Measure.restrict_univ] at hunion
  exact hunion

/-! ## Monotone exhaustion -/

/-- A uniform bound for the elementary cap energies implies integrability of
the full exponential energy. -/
theorem fullWeightedL2_integrable_of_uniform_cap
    {eta C : ℝ} (heta : 0 < eta) {w : ℝ → ℝ} (hw : Continuous w)
    (hcap : ∀ n : ℕ,
      Integrable (fun z => capWeight eta (n : ℝ) z * |w z| ^ 2))
    (hbound : ∀ n : ℕ,
      (∫ z : ℝ, capWeight eta (n : ℝ) z * |w z| ^ 2) ≤ C) :
    Integrable (fun z => Real.exp (2 * eta * z) * |w z| ^ 2) := by
  let G : ℕ → ℝ → ℝ :=
    fun n z => capWeight eta (n : ℝ) z * |w z| ^ 2
  let F : ℝ → ℝ := fun z => Real.exp (2 * eta * z) * |w z| ^ 2
  have hGF : ∀ᵐ z : ℝ ∂volume,
      Tendsto (fun n => G n z) atTop (nhds (F z)) := by
    filter_upwards with z
    have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have hweight := (capWeight_tendsto_full heta z).comp hnat
    simpa only [G, F, Function.comp_apply, sq_abs] using
      hweight.mul_const (w z ^ 2)
  have hGmeas : ∀ n : ℕ, AEStronglyMeasurable (G n) volume := by
    intro n
    exact ((capWeight_continuous eta (n : ℝ)).mul
      (hw.abs.pow 2)).aestronglyMeasurable
  have hlintegral_le : ∀ n : ℕ,
      (∫⁻ z : ℝ, ‖G n z‖ₑ ∂volume) ≤ ENNReal.ofReal C := by
    intro n
    have hnonneg : ∀ z : ℝ, 0 ≤ G n z := fun z =>
      mul_nonneg (capWeight_pos eta (n : ℝ) z).le (sq_nonneg _)
    calc
      (∫⁻ z : ℝ, ‖G n z‖ₑ ∂volume) =
          ∫⁻ z : ℝ, ENNReal.ofReal (G n z) ∂volume := by
        apply lintegral_congr
        intro z
        exact Real.enorm_of_nonneg (hnonneg z)
      _ = ENNReal.ofReal (∫ z : ℝ, G n z) :=
        (ofReal_integral_eq_lintegral_ofReal (hcap n)
          (Eventually.of_forall hnonneg)).symm
      _ ≤ ENNReal.ofReal C := by
        apply ENNReal.ofReal_le_ofReal
        simpa [G] using hbound n
  have hliminf_le :
      liminf (fun n => ∫⁻ z : ℝ, ‖G n z‖ₑ ∂volume) atTop ≤
        ENNReal.ofReal C :=
    liminf_le_of_frequently_le' (Frequently.of_forall hlintegral_le)
  have hliminf_ne :
      liminf (fun n => ∫⁻ z : ℝ, ‖G n z‖ₑ ∂volume) atTop ≠ ⊤ :=
    (lt_of_le_of_lt hliminf_le ENNReal.ofReal_lt_top).ne
  exact MeasureTheory.integrable_of_tendsto hGF hGmeas hliminf_ne

/-- The cap energies converge to the full exponential energy once the latter
is known finite. -/
theorem tentEnergy_mono_limit
    {eta : ℝ} (heta : 0 < eta) {w : ℝ → ℝ} (hw : Continuous w)
    (hfull : Integrable (fun z => Real.exp (2 * eta * z) * |w z| ^ 2)) :
    Tendsto
      (fun n : ℕ => ∫ z : ℝ, capWeight eta (n : ℝ) z * |w z| ^ 2)
      atTop
      (nhds (∫ z : ℝ, Real.exp (2 * eta * z) * |w z| ^ 2)) := by
  apply integral_tendsto_of_tendsto_of_monotone
  · intro n
    exact capWeight_mul_sq_integrable_of_full hw hfull
  · exact hfull
  · filter_upwards with z
    intro n m hnm
    exact mul_le_mul_of_nonneg_right
      (capWeight_mono_R heta.le z (Nat.cast_le.mpr hnm)) (sq_nonneg _)
  · filter_upwards with z
    have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    simpa only [Function.comp_apply, sq_abs] using
      ((capWeight_tendsto_full heta z).comp hnat).mul_const
      (w z ^ 2)

#print axioms capWeight_pos
#print axioms capWeight_le_full
#print axioms capWeight_le_plateau
#print axioms capWeight_mono_R
#print axioms capWeight_tendsto_full
#print axioms capWeight_hasDerivAt
#print axioms capWeight_abs_deriv_le
#print axioms capWeight_abs_secondDeriv_le
#print axioms differencePDE_divergence
#print axioms capWeight_mul_sq_integrable_of_full
#print axioms capWeight_mul_sq_integrable_of_split
#print axioms fullWeightedL2_integrable_of_uniform_cap
#print axioms tentEnergy_mono_limit

end ShenWork.Paper1
