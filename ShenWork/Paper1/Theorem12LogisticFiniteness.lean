import ShenWork.Paper1.Theorem12WeightedResolverEta

open Filter MeasureTheory Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Logistic exhaustion weight for the route-B weighted finiteness

`capWeight η R z = e^{2ηz} / (1 + e^{2η(z-R)})` is a smooth, elementary exhaustion of the
exponential weight `e^{2ηz}`: it equals `e^{2ηz}` for `z ≪ R`, levels off to the plateau
`e^{2ηR}` for `z ≫ R`, is bounded, and is *moderate* — `|∂_z capWeight| ≤ 2η · capWeight`
on the whole line.  This moderateness (the derivative of the cap only *decreases* the log
derivative, never blows it up as a compact cutoff would) is what makes the truncated weighted
energy estimate close with an `R`-independent constant.
-/

/-- The (strictly positive) denominator of the logistic weight. -/
theorem capWeight_denom_pos (η R z : ℝ) : 0 < 1 + Real.exp (2 * η * (z - R)) := by
  have := Real.exp_pos (2 * η * (z - R)); linarith

/-- Logistic exhaustion weight `e^{2ηz}/(1+e^{2η(z-R)})`. -/
def capWeight (η R z : ℝ) : ℝ :=
  Real.exp (2 * η * z) / (1 + Real.exp (2 * η * (z - R)))

theorem capWeight_pos (η R z : ℝ) : 0 < capWeight η R z :=
  div_pos (Real.exp_pos _) (capWeight_denom_pos η R z)

theorem capWeight_nonneg (η R z : ℝ) : 0 ≤ capWeight η R z := (capWeight_pos η R z).le

/-- `capWeight ≤ e^{2ηz}` since the denominator is `≥ 1`. -/
theorem capWeight_le_full (η R z : ℝ) : capWeight η R z ≤ Real.exp (2 * η * z) := by
  refine div_le_self (Real.exp_nonneg _) ?_
  have := Real.exp_pos (2 * η * (z - R)); linarith

/-- `capWeight ≤ e^{2ηR}` (the plateau bound). -/
theorem capWeight_le_plateau (η R z : ℝ) : capWeight η R z ≤ Real.exp (2 * η * R) := by
  rw [capWeight, div_le_iff₀ (capWeight_denom_pos η R z)]
  have hmul : Real.exp (2 * η * R) * Real.exp (2 * η * (z - R)) = Real.exp (2 * η * z) := by
    rw [← Real.exp_add]; ring_nf
  nlinarith [Real.exp_pos (2 * η * R), Real.exp_pos (2 * η * (z - R)), hmul]

/-- Chain-rule derivative of `z ↦ e^{2ηz}`. -/
theorem hasDerivAt_exp_lin (a z : ℝ) :
    HasDerivAt (fun z => Real.exp (a * z)) (a * Real.exp (a * z)) z := by
  have h : HasDerivAt (fun z => a * z) a z := by
    simpa using (hasDerivAt_id z).const_mul a
  simpa [mul_comm] using (Real.hasDerivAt_exp (a * z)).comp z h

/-- The exact derivative of the logistic weight:
`∂_z capWeight = 2η · capWeight / (1 + e^{2η(z-R)})`. -/
theorem capWeight_hasDerivAt (η R z : ℝ) :
    HasDerivAt (capWeight η R)
      (2 * η * capWeight η R z / (1 + Real.exp (2 * η * (z - R)))) z := by
  have hf : HasDerivAt (fun z => Real.exp (2 * η * z)) (2 * η * Real.exp (2 * η * z)) z :=
    hasDerivAt_exp_lin (2 * η) z
  have hg' : HasDerivAt (fun z => Real.exp (2 * η * (z - R)))
      (2 * η * Real.exp (2 * η * (z - R))) z := by
    have h : HasDerivAt (fun z => 2 * η * (z - R)) (2 * η) z := by
      simpa using ((hasDerivAt_id z).sub_const R).const_mul (2 * η)
    simpa [mul_comm] using (Real.hasDerivAt_exp (2 * η * (z - R))).comp z h
  have hg : HasDerivAt (fun z => 1 + Real.exp (2 * η * (z - R)))
      (2 * η * Real.exp (2 * η * (z - R))) z := by
    simpa using hg'.const_add (1 : ℝ)
  have hd := hf.div hg (ne_of_gt (capWeight_denom_pos η R z))
  convert hd using 1
  set E := Real.exp (2 * η * z) with hE
  set F := Real.exp (2 * η * (z - R)) with hF
  have hden : (0 : ℝ) < 1 + F := by rw [hF]; exact capWeight_denom_pos η R z
  rw [capWeight]
  field_simp
  ring

theorem capWeight_deriv_eq (η R z : ℝ) :
    deriv (capWeight η R) z
      = 2 * η * capWeight η R z / (1 + Real.exp (2 * η * (z - R))) :=
  (capWeight_hasDerivAt η R z).deriv

/-- The MODERATE bound: `|∂_z capWeight| ≤ 2η · capWeight` on the whole line. -/
theorem capWeight_abs_deriv_le {η : ℝ} (hη : 0 ≤ η) (R z : ℝ) :
    |deriv (capWeight η R) z| ≤ 2 * η * capWeight η R z := by
  rw [capWeight_deriv_eq]
  have hden : (0 : ℝ) < 1 + Real.exp (2 * η * (z - R)) := capWeight_denom_pos η R z
  have hnum : 0 ≤ 2 * η * capWeight η R z :=
    mul_nonneg (by positivity) (capWeight_nonneg η R z)
  rw [abs_of_nonneg (div_nonneg hnum hden.le)]
  refine div_le_self hnum ?_
  have := Real.exp_pos (2 * η * (z - R)); linarith

/-- `capWeight` is monotone increasing in the truncation radius `R` (for `η ≥ 0`). -/
theorem capWeight_mono_R {η : ℝ} (hη : 0 ≤ η) (z : ℝ) :
    Monotone (fun R => capWeight η R z) := by
  intro R₁ R₂ hR
  simp only [capWeight]
  apply div_le_div_of_nonneg_left (Real.exp_nonneg _) (capWeight_denom_pos η R₂ z)
  have h : Real.exp (2 * η * (z - R₂)) ≤ Real.exp (2 * η * (z - R₁)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  linarith

/-- `capWeight η R z → e^{2ηz}` as `R → ∞` (for `η > 0`). -/
theorem capWeight_tendsto_full {η : ℝ} (hη : 0 < η) (z : ℝ) :
    Filter.Tendsto (fun R => capWeight η R z) Filter.atTop
      (nhds (Real.exp (2 * η * z))) := by
  have hRz : Filter.Tendsto (fun R : ℝ => 2 * η * (R - z)) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity)
      (Filter.tendsto_atTop_add_const_right _ (-z) Filter.tendsto_id)
  have hinner : Filter.Tendsto (fun R : ℝ => 2 * η * (z - R)) Filter.atTop Filter.atBot := by
    have : (fun R : ℝ => 2 * η * (z - R)) = fun R => -(2 * η * (R - z)) := by
      funext R; ring
    rw [this]; exact tendsto_neg_atTop_atBot.comp hRz
  have hexp : Filter.Tendsto (fun R => Real.exp (2 * η * (z - R))) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_comp_nhds_zero.mpr hinner
  have hden : Filter.Tendsto (fun R => 1 + Real.exp (2 * η * (z - R))) Filter.atTop (nhds 1) := by
    simpa using hexp.const_add (1 : ℝ)
  have hquot := (tendsto_const_nhds (x := Real.exp (2 * η * z))
    (f := Filter.atTop)).div hden (by norm_num)
  simpa [capWeight, div_one] using hquot

/-- The logistic weight is continuous in the space variable. -/
theorem capWeight_continuous (η R : ℝ) : Continuous (capWeight η R) := by
  unfold capWeight
  refine Continuous.div ?_ ?_ (fun z => (capWeight_denom_pos η R z).ne')
  · exact Real.continuous_exp.comp (continuous_const.mul continuous_id)
  · exact continuous_const.add
      (Real.continuous_exp.comp (continuous_const.mul (continuous_id.sub continuous_const)))

/-- **Monotone-convergence bridge (route-B E-step).**  A uniform bound `K` on the
`capWeight η n`-truncated integral of a nonnegative measurable `f` yields integrability of `f`
against the full exponential weight `e^{2ηz}`, with the same bound `K`.  This is the reusable
machinery that converts the `R`-independent truncated weighted-energy bound into the
`coreIntegrability` inputs (`hclose`, `hWx2`, `hrem_int`). -/
theorem weighted_integrable_of_uniform_capWeight_bound
    {η : ℝ} (hη : 0 < η) {f : ℝ → ℝ} (hf0 : ∀ z, 0 ≤ f z) (hfm : Measurable f) {K : ℝ}
    (hint : ∀ n : ℕ, Integrable (fun z => capWeight η (n : ℝ) z * f z))
    (hbd : ∀ n : ℕ, ∫ z, capWeight η (n : ℝ) z * f z ≤ K) :
    Integrable (fun z => Real.exp (2 * η * z) * f z) ∧
      ∫ z, Real.exp (2 * η * z) * f z ≤ K := by
  set g : ℕ → ℝ → ℝ := fun n z => capWeight η (n : ℝ) z * f z with hgdef
  set G : ℝ → ℝ := fun z => Real.exp (2 * η * z) * f z with hGdef
  have hg0 : ∀ n z, 0 ≤ g n z := fun n z => mul_nonneg (capWeight_nonneg η _ z) (hf0 z)
  have hG0 : ∀ z, 0 ≤ G z := fun z => mul_nonneg (Real.exp_pos _).le (hf0 z)
  have hgm : ∀ n, Measurable (g n) := fun n => ((capWeight_continuous η _).measurable).mul hfm
  have hGm : Measurable G :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable).mul hfm
  have hmono : Monotone (fun n z => ENNReal.ofReal (g n z)) := by
    intro n m hnm z
    exact ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (capWeight_mono_R hη.le z (by exact_mod_cast hnm)) (hf0 z))
  have hsup : (fun z => ⨆ n, ENNReal.ofReal (g n z)) = fun z => ENNReal.ofReal (G z) := by
    funext z
    have htend : Tendsto (fun n : ℕ => g n z) atTop (nhds (G z)) :=
      ((capWeight_tendsto_full hη z).comp tendsto_natCast_atTop_atTop).mul_const (f z)
    have htende : Tendsto (fun n : ℕ => ENNReal.ofReal (g n z)) atTop
        (nhds (ENNReal.ofReal (G z))) := (ENNReal.continuous_ofReal.tendsto _).comp htend
    have hmonoe : Monotone (fun n : ℕ => ENNReal.ofReal (g n z)) := fun n m hnm =>
      ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (capWeight_mono_R hη.le z (by exact_mod_cast hnm)) (hf0 z))
    exact tendsto_nhds_unique (tendsto_atTop_iSup hmonoe) htende
  have hK0 : 0 ≤ K := le_trans (integral_nonneg (fun z => hg0 0 z)) (hbd 0)
  have hli : ∫⁻ z, ENNReal.ofReal (G z) ≤ ENNReal.ofReal K := by
    rw [← hsup, lintegral_iSup (fun n => (hgm n).ennreal_ofReal) hmono]
    refine iSup_le (fun n => ?_)
    rw [← ofReal_integral_eq_lintegral_ofReal (hint n) (Filter.Eventually.of_forall (hg0 n))]
    exact ENNReal.ofReal_le_ofReal (hbd n)
  have hfin : HasFiniteIntegral G := by
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hG0)]
    exact lt_of_le_of_lt hli ENNReal.ofReal_lt_top
  have hInt : Integrable G := ⟨hGm.aestronglyMeasurable, hfin⟩
  refine ⟨hInt, ?_⟩
  have hle : ENNReal.ofReal (∫ z, G z) ≤ ENNReal.ofReal K := by
    rw [ofReal_integral_eq_lintegral_ofReal hInt (Filter.Eventually.of_forall hG0)]; exact hli
  exact (ENNReal.ofReal_le_ofReal_iff hK0).mp hle

/-- `capWeight`-truncated integral of a nonnegative field is bounded by its full
exponential-weighted integral, uniformly in `R` (`capWeight ≤ e^{2ηz}`).  This bounds
`E_n(0)` by the initial closeness `E0`, the `R`-independent Grönwall input for step D. -/
theorem capWeight_integral_le_full {η R : ℝ} {f : ℝ → ℝ}
    (hf : ∀ z, 0 ≤ f z) (hfmeas : AEStronglyMeasurable f volume)
    (hfull : Integrable (fun z => Real.exp (2 * η * z) * f z)) :
    ∫ z, capWeight η R z * f z ≤ ∫ z, Real.exp (2 * η * z) * f z := by
  have hcapint : Integrable (fun z => capWeight η R z * f z) := by
    refine hfull.mono' ((capWeight_continuous η R).aestronglyMeasurable.mul hfmeas) ?_
    filter_upwards with z
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (capWeight_nonneg η R z) (hf z))]
    exact mul_le_mul_of_nonneg_right (capWeight_le_full η R z) (hf z)
  exact integral_mono hcapint hfull
    (fun z => mul_le_mul_of_nonneg_right (capWeight_le_full η R z) (hf z))

/-- Reduction bridge: pointwise exponential right-tail decay of a continuous function gives
`L²` integrability of its square on a right half-line.  This isolates the finiteness crux
(`IntegrableOn |w(t,·)|² (Ioi a)` for the moving-frame error `w = u(t,·) - U`) to the SOLUTION's
own tail decay `|u(t,·) - U| ≤ C e^{-κ·}` — the §5 content the paper obtains from Henry's
semigroup regularity (Thm 7.1.3), which is unavailable via the glued whole-line mild solution and
so must be supplied by a solution-tail supersolution comparison. -/
theorem rightTailL2_of_exp_decay {w : ℝ → ℝ} {a C κ : ℝ} (hκ : 0 < κ)
    (hwc : Continuous w)
    (hdecay : ∀ z, a ≤ z → |w z| ≤ C * Real.exp (-κ * z)) :
    IntegrableOn (fun z => |w z| ^ 2) (Set.Ioi a) := by
  have hb : (0 : ℝ) < 2 * κ := by linarith
  have hdom : IntegrableOn (fun z => C ^ 2 * Real.exp (-(2 * κ) * z)) (Set.Ioi a) :=
    (exp_neg_integrableOn_Ioi a hb).const_mul (C ^ 2)
  refine hdom.mono' ((hwc.abs.pow 2).aestronglyMeasurable) ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
  have hz' : a ≤ z := le_of_lt hz
  have hnn : (0 : ℝ) ≤ |w z| := abs_nonneg _
  have hbound : |w z| ≤ C * Real.exp (-κ * z) := hdecay z hz'
  have hexp : Real.exp (-κ * z) ^ 2 = Real.exp (-(2 * κ) * z) := by
    rw [pow_two, ← Real.exp_add]; ring_nf
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ |w z| ^ 2)]
  calc |w z| ^ 2 ≤ (C * Real.exp (-κ * z)) ^ 2 := pow_le_pow_left₀ hnn hbound 2
    _ = C ^ 2 * Real.exp (-(2 * κ) * z) := by rw [mul_pow, hexp]

section Theorem12LogisticFinitenessAxiomAudit

#print axioms capWeight_pos
#print axioms capWeight_le_full
#print axioms capWeight_le_plateau
#print axioms capWeight_hasDerivAt
#print axioms capWeight_abs_deriv_le
#print axioms capWeight_mono_R
#print axioms capWeight_tendsto_full
#print axioms capWeight_continuous
#print axioms weighted_integrable_of_uniform_capWeight_bound
#print axioms capWeight_integral_le_full
#print axioms rightTailL2_of_exp_decay

end Theorem12LogisticFinitenessAxiomAudit

end ShenWork.Paper1
