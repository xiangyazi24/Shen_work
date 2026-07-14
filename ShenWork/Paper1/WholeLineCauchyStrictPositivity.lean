import ShenWork.Paper1.WholeLineCauchyDuhamel
import ShenWork.Paper1.WholeLineCauchyBUCHeatContinuity
import ShenWork.Paper1.WholeLineCauchySpaceTimeMaximum
import ShenWork.Paper1.Statements

open MeasureTheory Set Filter Topology

noncomputable section

namespace ShenWork.Paper1

/-- **STEP 1 (homogeneous strict positivity).**  The modified heat semigroup of a
nonnegative, bounded, measurable datum that is bounded below by `δ > 0` on a
left half-line `Iic A` is strictly positive everywhere at every positive time.
The strictly-positive heat kernel integrated against a datum that is `≥ δ` on a
set of positive measure is strictly positive; the reaction damping `e^{-t}` only
rescales. Reusable base for the whole-line Cauchy strict-positivity conjunct. -/
theorem wholeLineCauchyHeatOp_pos_of_nonneg_of_pos_atBot
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} {M : ℝ}
    (hf_bd : ∀ y, |f y| ≤ M)
    (hf_meas : AEStronglyMeasurable f volume)
    (hf_nonneg : ∀ y, 0 ≤ f y)
    {δ A : ℝ} (hδ : 0 < δ) (hA : ∀ y ≤ A, δ ≤ f y) (x : ℝ) :
    0 < wholeLineCauchyHeatOp t f x := by
  have hg_nonneg : 0 ≤ fun y => heatKernel t (x - y) * f y := by
    intro y; exact mul_nonneg (heatKernel_nonneg ht _) (hf_nonneg y)
  have hg_int : Integrable (fun y => heatKernel t (x - y) * f y) volume :=
    heatKernel_mul_bounded_integrable ht x hf_bd hf_meas
  -- The integrand is strictly positive on `Icc (A-1) A`, a set of measure `1`.
  have hsub : Set.Icc (A - 1) A ⊆ Function.support (fun y => heatKernel t (x - y) * f y) := by
    intro y hy
    have hpos : 0 < heatKernel t (x - y) * f y :=
      mul_pos (heatKernel_pos ht _) (lt_of_lt_of_le hδ (hA y hy.2))
    exact ne_of_gt hpos
  have hmeas_pos : 0 < volume (Function.support (fun y => heatKernel t (x - y) * f y)) := by
    have hIcc : (0 : ENNReal) < volume (Set.Icc (A - 1) A) := by
      rw [Real.volume_Icc]
      simp only [sub_sub_cancel]
      exact ENNReal.ofReal_pos.mpr one_pos
    exact lt_of_lt_of_le hIcc (measure_mono hsub)
  have hint_pos : 0 < ∫ y, heatKernel t (x - y) * f y :=
    (integral_pos_iff_support_of_nonneg hg_nonneg hg_int).mpr hmeas_pos
  -- Unfold `wholeLineCauchyHeatOp = modifiedSemigroup = e^{-t} · heatSemigroup`.
  show 0 < modifiedSemigroup t f x
  rw [modifiedSemigroup, heatSemigroup]
  exact mul_pos (Real.exp_pos _) hint_pos

/-- The homogeneous heat part of the whole-line Cauchy construction is strictly
positive at every positive time, for a nonnegative BUC datum that is `≥ δ > 0`
on a left half-line.  This is the strict-positivity base (`S(t)u₀ > 0`) any
lower-barrier propagation argument builds on. -/
theorem wholeLineCauchyHeatBUCTotal_pos_of_nonneg_of_pos_atBot
    {t : ℝ} (ht : 0 < t) (u₀ : WholeLineBUC)
    (hnn : ∀ y, 0 ≤ u₀.1 y)
    {δ A : ℝ} (hδ : 0 < δ) (hA : ∀ y ≤ A, δ ≤ u₀.1 y) (x : ℝ) :
    0 < (wholeLineCauchyHeatBUCTotal t u₀).1 x := by
  rw [wholeLineCauchyHeatBUCTotal, dif_pos ht, wholeLineCauchyHeatBUC_apply]
  exact wholeLineCauchyHeatOp_pos_of_nonneg_of_pos_atBot ht
    (fun y => WholeLineBUC.abs_apply_le_norm u₀ y)
    u₀.1.continuous.aestronglyMeasurable hnn hδ hA x

/-- **Pure-drift weak maximum principle (no zeroth-order term).**  A bounded
space-time-regular trajectory whose PDE is bounded above by `u_xx + K|u_x|`
(a drift subsolution, *no* reaction term) never exceeds its initial ceiling on
the slab.  Proved from the strict-`G` slab driver by the standard `-η t`
perturbation, which supplies the strict negativity the driver needs and is then
removed in the limit `η → 0`.  This is the reusable min/max-side tool the strict
positivity comparison runs on: applying it to `δ - e^{K t} u` turns the linear
drift supersolution into a lower barrier. -/
theorem wholeLineSlabSup_le_of_drift_subsolution
    {T A C K : ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0 < T) (hK : 0 ≤ K)
    (hcont : Continuous (fun q : ℝ × ℝ => u q.1 q.2))
    (hupper : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, u t x ≤ A)
    (hinit : ∀ x, u 0 x ≤ C)
    (htime : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun s : ℝ => u s x) (deriv (fun s : ℝ => u s x) t) t)
    (hspace1 : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => u t y) (deriv (fun y : ℝ => u t y) x) x)
    (hspace2 : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => deriv (fun z : ℝ => u t z) y)
        (deriv (fun y : ℝ => deriv (fun z : ℝ => u t z) y) x) x)
    (hpde : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      deriv (fun s : ℝ => u s x) t ≤
        deriv (fun y : ℝ => deriv (fun z : ℝ => u t z) y) x +
          K * |deriv (fun y : ℝ => u t y) x|) :
    wholeLineSlabSup T u ≤ C := by
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  set η : ℝ := ε / T with hηdef
  have hη : 0 < η := div_pos hε hT
  have hηT : η * T = ε := by rw [hηdef]; field_simp
  set uη : ℝ → ℝ → ℝ := fun t x => u t x - η * t with huηdef
  have hcontη : Continuous (fun q : ℝ × ℝ => uη q.1 q.2) := by
    simp only [huηdef]
    exact hcont.sub ((continuous_const.mul continuous_fst))
  have hupperη : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, uη t x ≤ A := by
    intro t ht x
    have : 0 ≤ η * t := mul_nonneg hη.le ht.1
    simp only [huηdef]
    linarith [hupper t ht x]
  have hinitη : ∀ x, uη 0 x ≤ C := by
    intro x; simp only [huηdef, mul_zero, sub_zero]; exact hinit x
  have hdtη : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun s : ℝ => uη s x) (deriv (fun s : ℝ => u s x) t - η) t := by
    intro t x ht
    simp only [huηdef]
    exact (htime ht).sub (((hasDerivAt_id t).const_mul η).congr_deriv (by ring))
  have htimeη : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun s : ℝ => uη s x) (deriv (fun s : ℝ => uη s x) t) t := by
    intro t x ht
    exact (hdtη ht).differentiableAt.hasDerivAt
  have hslice : ∀ t : ℝ, (fun y : ℝ => uη t y) = fun y : ℝ => u t y - η * t := by
    intro t; rfl
  have hspace1η : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => uη t y) (deriv (fun y : ℝ => uη t y) x) x := by
    intro t x ht
    have : DifferentiableAt ℝ (fun y : ℝ => uη t y) x := by
      rw [hslice]; exact (hspace1 ht).differentiableAt.sub_const _
    exact this.hasDerivAt
  have hderiv_slice : ∀ t : ℝ,
      (fun y : ℝ => deriv (fun z : ℝ => uη t z) y) =
        fun y : ℝ => deriv (fun z : ℝ => u t z) y := by
    intro t; funext y
    simp only [huηdef]
    exact deriv_sub_const _
  have hspace2η : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => deriv (fun z : ℝ => uη t z) y)
        (deriv (fun y : ℝ => deriv (fun z : ℝ => uη t z) y) x) x := by
    intro t x ht
    have : DifferentiableAt ℝ (fun y : ℝ => deriv (fun z : ℝ => uη t z) y) x := by
      rw [hderiv_slice]; exact (hspace2 ht).differentiableAt
    exact this.hasDerivAt
  have hpdeη : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      deriv (fun s : ℝ => uη s x) t ≤
        deriv (fun y : ℝ => deriv (fun z : ℝ => uη t z) y) x +
          K * |deriv (fun y : ℝ => uη t y) x| + (fun _ : ℝ => -η) (uη t x) := by
    intro t x ht
    have hdt : deriv (fun s : ℝ => uη s x) t = deriv (fun s : ℝ => u s x) t - η :=
      (hdtη ht).deriv
    have hd2 : deriv (fun y : ℝ => deriv (fun z : ℝ => uη t z) y) x =
        deriv (fun y : ℝ => deriv (fun z : ℝ => u t z) y) x := by
      rw [hderiv_slice]
    have hd1 : deriv (fun y : ℝ => uη t y) x = deriv (fun y : ℝ => u t y) x := by
      rw [hslice]; exact deriv_sub_const _
    simp only [hdt, hd2, hd1]
    have := hpde (x := x) ht
    linarith
  have hdriver : wholeLineSlabSup T uη ≤ C :=
    wholeLineSlabSup_le_of_scalar_pde hT hK hcontη hupperη hinitη
      continuous_const (fun _ => by simpa using neg_neg_iff_pos.mpr hη)
      htimeη hspace1η hspace2η hpdeη
  have hkey : ∀ a ∈ wholeLineSlabValues T u, a ≤ C + ε := by
    rintro a ⟨t, ht, x, rfl⟩
    have hle : uη t x ≤ wholeLineSlabSup T uη :=
      le_wholeLineSlabSup hT.le hupperη ht x
    have hηt : η * t ≤ η * T := mul_le_mul_of_nonneg_left ht.2 hη.le
    have hueq : u t x = uη t x + η * t := by simp only [huηdef]; ring
    calc u t x = uη t x + η * t := hueq
      _ ≤ wholeLineSlabSup T uη + η * T := add_le_add hle hηt
      _ ≤ C + η * T := by linarith
      _ = C + ε := by rw [hηT]
  exact csSup_le (wholeLineSlabValues_nonempty hT.le u) hkey

section WholeLineCauchyStrictPositivityAxiomAudit

#print axioms wholeLineCauchyHeatOp_pos_of_nonneg_of_pos_atBot
#print axioms wholeLineCauchyHeatBUCTotal_pos_of_nonneg_of_pos_atBot
#print axioms wholeLineSlabSup_le_of_drift_subsolution

end WholeLineCauchyStrictPositivityAxiomAudit

end ShenWork.Paper1
