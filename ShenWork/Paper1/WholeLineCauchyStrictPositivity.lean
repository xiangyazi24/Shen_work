import ShenWork.Paper1.WholeLineCauchyDuhamel
import ShenWork.Paper1.WholeLineCauchyBUCHeatContinuity
import ShenWork.Paper1.WholeLineCauchySpaceTimeMaximum
import ShenWork.Paper1.WholeLineCauchyC2Bootstrap
import ShenWork.Paper1.WholeLineCauchyTimeRegularity
import ShenWork.Paper1.WholeLineCauchyNonnegativity
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

/-- On a nonnegative interval, a power with exponent at least one is bounded
by its endpoint slope times the base.  This is the factorization used to turn
the zeroth-order chemotaxis term into a linear-in-`u` bound. -/
theorem rpow_le_endpoint_rpow_sub_one_mul
    {u M a : ℝ} (ha : 1 ≤ a) (hu0 : 0 ≤ u) (huM : u ≤ M) :
    u ^ a ≤ M ^ (a - 1) * u := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  by_cases hu : u = 0
  · subst u
    have hane : a ≠ 0 := ne_of_gt ha0
    simp [Real.zero_rpow hane]
  · have hupos : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu)
    have hpow : u ^ a = u ^ (a - 1) * u := by
      calc
        u ^ a = u ^ ((a - 1) + 1) := by ring_nf
        _ = u ^ (a - 1) * u ^ (1 : ℝ) := by
          rw [Real.rpow_add hupos]
        _ = u ^ (a - 1) * u := by rw [Real.rpow_one]
    have hm1 : 0 ≤ a - 1 := sub_nonneg.mpr ha
    have hle : u ^ (a - 1) ≤ M ^ (a - 1) :=
      Real.rpow_le_rpow hupos.le huM hm1
    rw [hpow]
    exact mul_le_mul_of_nonneg_right hle hupos.le

/-- Product/elliptic expansion of the physical chemotaxis flux at a
nonnegative differentiable profile. -/
theorem wholeLineChemotaxisFlux_deriv_eq_of_nonneg
    (p : CMParams) {u : ℝ → ℝ} {x : ℝ}
    (hu : IsCUnifBdd u) (hu0 : ∀ y, 0 ≤ u y)
    (hux : HasDerivAt u (deriv u x) x) :
    deriv (wholeLineChemotaxisFlux p u) x =
      p.m * (u x) ^ (p.m - 1) * deriv u x *
          deriv (frozenElliptic p u) x +
        (u x) ^ p.m * (frozenElliptic p u x - (u x) ^ p.γ) := by
  exact (wholeLineChemotaxisFlux_hasDerivAt p hu hu0 hux).deriv

/-- Uniform coefficient of the first-order drift on the strip `[0,M]`. -/
def wholeLineCauchyStrictPositivityDriftRate (p : CMParams) (M : ℝ) : ℝ :=
  |p.χ| * p.m * M ^ (p.m - 1) * M ^ p.γ

/-- Uniform zeroth-order loss rate on the strip `[0,M]`. -/
def wholeLineCauchyStrictPositivityZeroRate (p : CMParams) (M : ℝ) : ℝ :=
  |p.χ| * M ^ (p.m - 1) * (2 * M ^ p.γ) + (1 + M ^ p.α)

/-- The expanded physical equation has a linear drift/zeroth-order lower
bound on every nonnegative bounded strip. -/
theorem wholeLineCauchy_physical_pde_drift_lower_bound
    (p : CMParams) {M u ux vx v ut uxx : ℝ}
    (hM : 0 ≤ M) (hu0 : 0 ≤ u) (huM : u ≤ M)
    (hv0 : 0 ≤ v) (hvM : v ≤ M ^ p.γ)
    (hvx : |vx| ≤ M ^ p.γ)
    (hpde : ut = uxx - p.χ *
        (p.m * u ^ (p.m - 1) * ux * vx +
          u ^ p.m * (v - u ^ p.γ)) + u * (1 - u ^ p.α)) :
    uxx - wholeLineCauchyStrictPositivityZeroRate p M * u -
          wholeLineCauchyStrictPositivityDriftRate p M * |ux| ≤ ut := by
  have hMpow_m1 : 0 ≤ M ^ (p.m - 1) := Real.rpow_nonneg hM _
  have hMpow_g : 0 ≤ M ^ p.γ := Real.rpow_nonneg hM _
  have hMpow_a : 0 ≤ M ^ p.α := Real.rpow_nonneg hM _
  have hum1 : u ^ (p.m - 1) ≤ M ^ (p.m - 1) :=
    Real.rpow_le_rpow hu0 huM (sub_nonneg.mpr p.hm)
  have hum : u ^ p.m ≤ M ^ (p.m - 1) * u :=
    rpow_le_endpoint_rpow_sub_one_mul p.hm hu0 huM
  have hug : u ^ p.γ ≤ M ^ p.γ :=
    Real.rpow_le_rpow hu0 huM (zero_le_one.trans p.hγ)
  have hua : u ^ p.α ≤ M ^ p.α :=
    Real.rpow_le_rpow hu0 huM (zero_le_one.trans p.hα)
  have hvabs : |v| ≤ M ^ p.γ := by
    rw [abs_of_nonneg hv0]
    exact hvM
  have hugabs : |u ^ p.γ| ≤ M ^ p.γ := by
    rw [abs_of_nonneg (Real.rpow_nonneg hu0 _)]
    exact hug
  have hvsub : |v - u ^ p.γ| ≤ 2 * M ^ p.γ := by
    calc
      |v - u ^ p.γ| ≤ |v| + |u ^ p.γ| := abs_sub _ _
      _ ≤ M ^ p.γ + M ^ p.γ := add_le_add hvabs hugabs
      _ = 2 * M ^ p.γ := by ring
  have hdrift_abs :
      |-p.χ * (p.m * u ^ (p.m - 1) * ux * vx)| ≤
        wholeLineCauchyStrictPositivityDriftRate p M * |ux| := by
    calc
      |-p.χ * (p.m * u ^ (p.m - 1) * ux * vx)| =
          |p.χ| * p.m * u ^ (p.m - 1) * |ux| * |vx| := by
            rw [abs_mul, abs_neg, abs_mul, abs_mul, abs_mul,
              abs_of_nonneg (zero_le_one.trans p.hm),
              abs_of_nonneg (Real.rpow_nonneg hu0 _)]
            ring
      _ ≤ wholeLineCauchyStrictPositivityDriftRate p M * |ux| := by
        have hcoef0 : 0 ≤ |p.χ| * p.m :=
          mul_nonneg (abs_nonneg _) (zero_le_one.trans p.hm)
        have hux0 : 0 ≤ |ux| := abs_nonneg _
        have huv : u ^ (p.m - 1) * |vx| ≤
            M ^ (p.m - 1) * M ^ p.γ :=
          mul_le_mul hum1 hvx (abs_nonneg _) hMpow_m1
        dsimp [wholeLineCauchyStrictPositivityDriftRate]
        calc
          |p.χ| * p.m * u ^ (p.m - 1) * |ux| * |vx| =
              (|p.χ| * p.m) * |ux| * (u ^ (p.m - 1) * |vx|) := by ring
          _ ≤ (|p.χ| * p.m) * |ux| *
                (M ^ (p.m - 1) * M ^ p.γ) :=
            mul_le_mul_of_nonneg_left huv (mul_nonneg hcoef0 hux0)
          _ = |p.χ| * p.m * M ^ (p.m - 1) * M ^ p.γ * |ux| := by ring
  have hdrift :
      -(wholeLineCauchyStrictPositivityDriftRate p M * |ux|) ≤
        -p.χ * (p.m * u ^ (p.m - 1) * ux * vx) :=
    neg_le_of_abs_le hdrift_abs
  have hchem_abs :
      |-p.χ * (u ^ p.m * (v - u ^ p.γ))| ≤
        (|p.χ| * M ^ (p.m - 1) * (2 * M ^ p.γ)) * u := by
    calc
      |-p.χ * (u ^ p.m * (v - u ^ p.γ))| =
          |p.χ| * u ^ p.m * |v - u ^ p.γ| := by
            rw [abs_mul, abs_neg, abs_mul,
              abs_of_nonneg (Real.rpow_nonneg hu0 _)]
            ring
      _ ≤ |p.χ| * (M ^ (p.m - 1) * u) * (2 * M ^ p.γ) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hum (abs_nonneg _)) hvsub
          (abs_nonneg _) (mul_nonneg (abs_nonneg _)
            (mul_nonneg hMpow_m1 hu0))
      _ = (|p.χ| * M ^ (p.m - 1) * (2 * M ^ p.γ)) * u := by ring
  have hchem :
      -((|p.χ| * M ^ (p.m - 1) * (2 * M ^ p.γ)) * u) ≤
        -p.χ * (u ^ p.m * (v - u ^ p.γ)) :=
    neg_le_of_abs_le hchem_abs
  have hreaction_inner : -(1 + M ^ p.α) ≤ 1 - u ^ p.α := by
    linarith
  have hreaction : -(1 + M ^ p.α) * u ≤ u * (1 - u ^ p.α) := by
    have := mul_le_mul_of_nonneg_right hreaction_inner hu0
    nlinarith
  rw [hpde]
  dsimp [wholeLineCauchyStrictPositivityZeroRate]
  linarith

/-- A nonnegative classical strip supersolution with uniformly positive
initial data stays strictly positive.  The exponential change of variables
removes the zeroth-order loss, and the pure-drift slab maximum principle is
applied on horizons strictly below `T`; continuity supplies the terminal
slice. -/
theorem wholeLine_pos_of_uniform_initial_of_drift_supersolution
    {T δ Kzero Kdrift : ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0 < T) (hδ : 0 < δ) (hKzero : 0 ≤ Kzero)
    (hKdrift : 0 ≤ Kdrift)
    (hcont : Continuous (fun q : ℝ × ℝ => u q.1 q.2))
    (hnonneg : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, 0 ≤ u t x)
    (hinit : ∀ x, δ ≤ u 0 x)
    (htime : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T →
      HasDerivAt (fun s : ℝ => u s x)
        (deriv (fun s : ℝ => u s x) t) t)
    (hspace1 : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => u t y)
        (deriv (fun y : ℝ => u t y) x) x)
    (hspace2 : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => deriv (fun z : ℝ => u t z) y)
        (deriv (fun y : ℝ => deriv (fun z : ℝ => u t z) y) x) x)
    (hpde : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T →
      deriv (fun s : ℝ => u s x) t ≥
        deriv (fun y : ℝ => deriv (fun z : ℝ => u t z) y) x -
          Kzero * u t x - Kdrift * |deriv (fun y : ℝ => u t y) x|) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, 0 < u t x := by
  let q : ℝ → ℝ → ℝ := fun t x => δ - Real.exp (Kzero * t) * u t x
  have hcontq : Continuous (fun r : ℝ × ℝ => q r.1 r.2) := by
    dsimp [q]
    fun_prop
  have hupperq : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, q t x ≤ δ := by
    intro t ht x
    have hexp0 : 0 ≤ Real.exp (Kzero * t) :=
      zero_le_one.trans (Real.one_le_exp (mul_nonneg hKzero ht.1))
    have hprod : 0 ≤ Real.exp (Kzero * t) * u t x :=
      mul_nonneg hexp0 (hnonneg t ht x)
    dsimp [q]
    linarith
  have hinitq : ∀ x, q 0 x ≤ 0 := by
    intro x
    simpa [q] using sub_nonpos.mpr (hinit x)
  have htimeq : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T →
      HasDerivAt (fun s : ℝ => q s x)
        (deriv (fun s : ℝ => q s x) t) t := by
    intro t x ht
    have hexp : HasDerivAt (fun s : ℝ => Real.exp (Kzero * s))
        (Kzero * Real.exp (Kzero * t)) t := by
      convert (Real.hasDerivAt_exp (Kzero * t)).comp t
        ((hasDerivAt_id t).const_mul Kzero) using 1
      all_goals ring
    have hraw := (hexp.mul (htime (t := t) (x := x) ht)).const_sub δ
    simpa [q] using hraw.differentiableAt.hasDerivAt
  have hspace1q : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => q t y)
        (deriv (fun y : ℝ => q t y) x) x := by
    intro t x ht
    have hraw :=
      ((hspace1 (t := t) (x := x) ht).const_mul
        (Real.exp (Kzero * t))).const_sub δ
    simpa [q] using hraw.differentiableAt.hasDerivAt
  have hderivq : ∀ ⦃t : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T → ∀ y,
      deriv (fun z : ℝ => q t z) y =
        -(Real.exp (Kzero * t) * deriv (fun z : ℝ => u t z) y) := by
    intro t ht y
    have hraw :=
      ((hspace1 (t := t) (x := y) ht).const_mul
        (Real.exp (Kzero * t))).const_sub δ
    simpa [q] using hraw.deriv
  have hspace2q : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => deriv (fun z : ℝ => q t z) y)
        (deriv (fun y : ℝ => deriv (fun z : ℝ => q t z) y) x) x := by
    intro t x ht
    have hfun : (fun y : ℝ => deriv (fun z : ℝ => q t z) y) =
        fun y : ℝ => -(Real.exp (Kzero * t) *
          deriv (fun z : ℝ => u t z) y) := by
      funext y
      exact hderivq ht y
    have hraw :=
      ((hspace2 (t := t) (x := x) ht).const_mul
        (Real.exp (Kzero * t))).neg
    rw [hfun]
    exact hraw.differentiableAt.hasDerivAt
  have hpdeq : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T →
      deriv (fun s : ℝ => q s x) t ≤
        deriv (fun y : ℝ => deriv (fun z : ℝ => q t z) y) x +
          Kdrift * |deriv (fun y : ℝ => q t y) x| := by
    intro t x ht
    have hexp : HasDerivAt (fun s : ℝ => Real.exp (Kzero * s))
        (Kzero * Real.exp (Kzero * t)) t := by
      convert (Real.hasDerivAt_exp (Kzero * t)).comp t
        ((hasDerivAt_id t).const_mul Kzero) using 1
      all_goals ring
    have hqt : deriv (fun s : ℝ => q s x) t =
        -((Kzero * Real.exp (Kzero * t)) * u t x +
          Real.exp (Kzero * t) * deriv (fun s : ℝ => u s x) t) := by
      have hraw :=
        (hexp.mul (htime (t := t) (x := x) ht)).const_sub δ
      simpa [q] using hraw.deriv
    have hqx : deriv (fun y : ℝ => q t y) x =
        -(Real.exp (Kzero * t) * deriv (fun y : ℝ => u t y) x) :=
      hderivq ht x
    have hfun : (fun y : ℝ => deriv (fun z : ℝ => q t z) y) =
        fun y : ℝ => -(Real.exp (Kzero * t) *
          deriv (fun z : ℝ => u t z) y) := by
      funext y
      exact hderivq ht y
    have hqxx : deriv (fun y : ℝ => deriv (fun z : ℝ => q t z) y) x =
        -(Real.exp (Kzero * t) *
          deriv (fun y : ℝ => deriv (fun z : ℝ => u t z) y) x) := by
      rw [hfun]
      exact ((hspace2 (t := t) (x := x) ht).const_mul
        (Real.exp (Kzero * t))).neg.deriv
    have hqabs : |deriv (fun y : ℝ => q t y) x| =
        Real.exp (Kzero * t) * |deriv (fun y : ℝ => u t y) x| := by
      rw [hqx, abs_neg, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hbase : 0 ≤ deriv (fun s : ℝ => u s x) t -
        (deriv (fun y : ℝ => deriv (fun z : ℝ => u t z) y) x -
          Kzero * u t x - Kdrift * |deriv (fun y : ℝ => u t y) x|) :=
      sub_nonneg.mpr (hpde (t := t) (x := x) ht)
    have hscaled := mul_nonneg (Real.exp_pos (Kzero * t)).le hbase
    rw [hqt, hqxx, hqabs]
    nlinarith
  have hq_nonpos_Ico : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x, q t x ≤ 0 := by
    intro t ht x
    let S : ℝ := (t + T) / 2
    have hS0 : 0 < S := by dsimp [S]; linarith [ht.1, hT]
    have htS : t ≤ S := by dsimp [S]; linarith [ht.2]
    have hST : S < T := by dsimp [S]; linarith [ht.2]
    have hupperS : ∀ s ∈ Set.Icc (0 : ℝ) S, ∀ y, q s y ≤ δ := by
      intro s hs y
      exact hupperq s ⟨hs.1, hs.2.trans hST.le⟩ y
    have hsup : wholeLineSlabSup S q ≤ 0 :=
      wholeLineSlabSup_le_of_drift_subsolution hS0 hKdrift hcontq
        hupperS hinitq
        (fun _ _ hs => htimeq ⟨hs.1, hs.2.trans_lt hST⟩)
        (fun _ _ hs => hspace1q ⟨hs.1, hs.2.trans_lt hST⟩)
        (fun _ _ hs => hspace2q ⟨hs.1, hs.2.trans_lt hST⟩)
        (fun _ _ hs => hpdeq ⟨hs.1, hs.2.trans_lt hST⟩)
    have hle : q t x ≤ wholeLineSlabSup S q :=
      le_wholeLineSlabSup hS0.le hupperS ⟨ht.1, htS⟩ x
    exact hle.trans hsup
  intro t ht x
  have hqle : q t x ≤ 0 := by
    by_cases hlt : t < T
    · exact hq_nonpos_Ico t ⟨ht.1, hlt⟩ x
    · have htT : t = T := le_antisymm ht.2 (le_of_not_gt hlt)
      subst t
      have htimeCont : Continuous (fun s : ℝ => q s x) :=
        hcontq.comp (continuous_id.prodMk continuous_const)
      have htend : Tendsto (fun s : ℝ => q s x) (𝓝[<] T) (𝓝 (q T x)) :=
        htimeCont.continuousAt.mono_left inf_le_left
      have hevent : ∀ᶠ s in 𝓝[<] T, q s x ≤ 0 := by
        filter_upwards [self_mem_nhdsWithin,
          (eventually_gt_nhds hT).filter_mono inf_le_left] with s hsT hs0
        exact hq_nonpos_Ico s ⟨hs0.le, hsT⟩ x
      exact le_of_tendsto htend hevent
  have hprod : δ ≤ Real.exp (Kzero * t) * u t x := by
    dsimp [q] at hqle
    linarith
  have hprod_pos : 0 < Real.exp (Kzero * t) * u t x := hδ.trans_le hprod
  nlinarith [Real.exp_pos (Kzero * t)]

/-- A uniformly positive BUC datum produces a canonical whole-line Cauchy
fixed point that is strictly positive at every positive physical time. -/
theorem wholeLineCauchyBUCMildFixedPoint_pos_of_uniformlyPositive
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 < T)
    (u₀ : WholeLineBUC) (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    {δ : ℝ} (hδ : 0 < δ) (hu₀ : ∀ x, δ ≤ u₀.1 x)
    (hstrip : ∀ (z : Set.Icc (0 : ℝ) T), ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M) :
    ∀ (z : Set.Icc (0 : ℝ) T), 0 < z.1 → ∀ x,
      0 < (wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall z).1 x := by
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall
  let ue : ℝ → ℝ → ℝ :=
    fun t x => (wholeLineBUCTrajectoryExtend hT.le U t).1 x
  let Kzero : ℝ := wholeLineCauchyStrictPositivityZeroRate p M
  let Kdrift : ℝ := wholeLineCauchyStrictPositivityDriftRate p M
  have hu₀nonneg : ∀ x, 0 ≤ u₀.1 x := fun x => hδ.le.trans (hu₀ x)
  have hUnonneg : ∀ z : Set.Icc (0 : ℝ) T, ∀ x, 0 ≤ (U z).1 x := by
    simpa [U] using wholeLineCauchyBUCMildFixedPoint_nonnegative
      p hM hT u₀ hu₀nonneg hsmall
  have hcont : Continuous (fun q : ℝ × ℝ => ue q.1 q.2) := by
    have hmap : Continuous
        (fun q : ℝ × ℝ => (Set.projIcc 0 T hT.le q.1, q.2)) :=
      (continuous_projIcc.comp continuous_fst).prodMk continuous_snd
    simpa [ue, wholeLineBUCTrajectoryExtend] using
      (wholeLineBUCTrajectory_jointContinuous U).comp hmap
  have hnonneg : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, 0 ≤ ue t x := by
    intro t ht x
    let z : Set.Icc (0 : ℝ) T := ⟨t, ht⟩
    have hext : wholeLineBUCTrajectoryExtend hT.le U t = U z :=
      wholeLineBUCTrajectoryExtend_eq hT.le U ht
    simpa [ue, hext] using hUnonneg z x
  have hinit : ∀ x, δ ≤ ue 0 x := by
    intro x
    have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
    have hext : wholeLineBUCTrajectoryExtend hT.le U 0 = U ⟨0, hzero⟩ :=
      wholeLineBUCTrajectoryExtend_eq hT.le U hzero
    have hUzero : U ⟨0, hzero⟩ = u₀ := by
      simpa [U] using wholeLineCauchyBUCMildFixedPoint_initial
        p hM hT.le u₀ hsmall hzero
    simpa [ue, hext, hUzero] using hu₀ x
  have htime : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T →
      HasDerivAt (fun s : ℝ => ue s x)
        (deriv (fun s : ℝ => ue s x) t) t := by
    intro t x ht
    have hphysical := wholeLineCauchyBUCMildFixedPoint_physical_pde_hasDerivAt
      p hM hT.le u₀ hsmall ht.1 ht.2
        (theta := (1 / 2 : ℝ)) (eta := (1 / 4 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        hstrip x
    simpa [ue, U] using hphysical.differentiableAt.hasDerivAt
  have hspace1 : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => ue t y)
        (deriv (fun y : ℝ => ue t y) x) x := by
    intro t x ht
    let z : Set.Icc (0 : ℝ) T := ⟨t, ht.1.le, ht.2.le⟩
    have hext : wholeLineBUCTrajectoryExtend hT.le U t = U z :=
      wholeLineBUCTrajectoryExtend_eq hT.le U z.2
    have hspatial := wholeLineCauchyBUCMildFixedPoint_spatial_hasDerivAt_positive
      p hM hT.le u₀ hsmall z ht.1 x
    have hdiff : DifferentiableAt ℝ (fun y : ℝ => ue t y) x := by
      simpa [ue, U, hext] using hspatial.differentiableAt
    exact hdiff.hasDerivAt
  have hspace2 : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T →
      HasDerivAt (fun y : ℝ => deriv (fun z : ℝ => ue t z) y)
        (deriv (fun y : ℝ => deriv (fun z : ℝ => ue t z) y) x) x := by
    intro t x ht
    let z : Set.Icc (0 : ℝ) T := ⟨t, ht.1.le, ht.2.le⟩
    have hext : wholeLineBUCTrajectoryExtend hT.le U t = U z :=
      wholeLineBUCTrajectoryExtend_eq hT.le U z.2
    have hwindow : ∀ s ∈ Set.Icc (t / 2) t, ∀ y,
        (wholeLineBUCTrajectoryExtend hT.le U s).1 y ∈ Set.Icc (0 : ℝ) M := by
      intro s hs y
      have hs0 : 0 ≤ s := le_trans (by linarith [ht.1] : 0 ≤ t / 2) hs.1
      have hsT : s ≤ T := hs.2.trans ht.2.le
      let zs : Set.Icc (0 : ℝ) T := ⟨s, hs0, hsT⟩
      have hsext : wholeLineBUCTrajectoryExtend hT.le U s = U zs :=
        wholeLineBUCTrajectoryExtend_eq hT.le U zs.2
      simpa [hsext, U] using hstrip zs y
    have hsecond :=
      wholeLineCauchyBUCMildFixedPoint_spatial_second_hasDerivAt_positive
        p hM hT.le u₀ hsmall z ht.1
          (theta := (1 / 2 : ℝ)) (eta := (1 / 4 : ℝ))
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by simpa [U] using hwindow) x
    have hslice : (fun y : ℝ => ue t y) = fun y : ℝ => (U z).1 y := by
      funext y
      simp [ue, hext]
    rw [hslice]
    exact hsecond.differentiableAt.hasDerivAt
  have hpde : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T →
      deriv (fun s : ℝ => ue s x) t ≥
        deriv (fun y : ℝ => deriv (fun z : ℝ => ue t z) y) x -
          Kzero * ue t x - Kdrift * |deriv (fun y : ℝ => ue t y) x| := by
    intro t x ht
    let z : Set.Icc (0 : ℝ) T := ⟨t, ht.1.le, ht.2.le⟩
    have hext : wholeLineBUCTrajectoryExtend hT.le U t = U z :=
      wholeLineBUCTrajectoryExtend_eq hT.le U z.2
    have hslice : (fun y : ℝ => ue t y) = fun y : ℝ => (U z).1 y := by
      funext y
      simp [ue, hext]
    have hux : HasDerivAt (U z).1 (deriv (U z).1 x) x :=
      (wholeLineCauchyBUCMildFixedPoint_spatial_hasDerivAt_positive
        p hM hT.le u₀ hsmall z ht.1 x).differentiableAt.hasDerivAt
    have hflux : deriv (wholeLineChemotaxisFlux p (U z).1) x =
        p.m * ((U z).1 x) ^ (p.m - 1) * deriv (U z).1 x *
            deriv (frozenElliptic p (U z).1) x +
          ((U z).1 x) ^ p.m *
            (frozenElliptic p (U z).1 x - ((U z).1 x) ^ p.γ) :=
      wholeLineChemotaxisFlux_deriv_eq_of_nonneg p
        (WholeLineBUC.isCUnifBdd (U z)) (hUnonneg z) hux
    have hphysical := wholeLineCauchyBUCMildFixedPoint_physical_pde_hasDerivAt
      p hM hT.le u₀ hsmall ht.1 ht.2
        (theta := (1 / 2 : ℝ)) (eta := (1 / 4 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        hstrip x
    have hpdeEq : deriv (fun s : ℝ => ue s x) t =
        deriv (fun y : ℝ => deriv (fun w : ℝ => (U z).1 w) y) x -
          p.χ * deriv (wholeLineChemotaxisFlux p (U z).1) x +
            wholeLineLogisticSource p (U z).1 x := by
      simpa [ue, U] using hphysical.deriv
    rw [hflux] at hpdeEq
    have huM := hstrip z x
    have hv0 : 0 ≤ frozenElliptic p (U z).1 x :=
      frozenElliptic_nonneg p (hUnonneg z) x
    have hvM : frozenElliptic p (U z).1 x ≤ M ^ p.γ := by
      apply frozenElliptic_le_of_rpow_le p (Real.rpow_nonneg hM _)
        (U z).1.continuous (hUnonneg z)
      intro y
      exact Real.rpow_le_rpow (hstrip z y).1 (hstrip z y).2
        (zero_le_one.trans p.hγ)
    have hvx : |deriv (frozenElliptic p (U z).1) x| ≤ M ^ p.γ :=
      frozenElliptic_deriv_abs_le_rpow_of_Icc p hM
        (WholeLineBUC.isCUnifBdd (U z)) (hstrip z) x
    have hlower := wholeLineCauchy_physical_pde_drift_lower_bound p hM
      huM.1 huM.2 hv0 hvM hvx
      (ut := deriv (fun s : ℝ => ue s x) t)
      (uxx := deriv (fun y : ℝ => deriv (fun w : ℝ => (U z).1 w) y) x)
      (ux := deriv (U z).1 x)
      (vx := deriv (frozenElliptic p (U z).1) x)
      (v := frozenElliptic p (U z).1 x)
      (by simpa [wholeLineLogisticSource, reactionFun] using hpdeEq)
    have hueq : ue t x = (U z).1 x := congrFun hslice x
    have huxeq : deriv (fun y : ℝ => ue t y) x = deriv (U z).1 x := by
      rw [hslice]
    have huxxeq : deriv (fun y : ℝ => deriv (fun w : ℝ => ue t w) y) x =
        deriv (fun y : ℝ => deriv (fun w : ℝ => (U z).1 w) y) x := by
      rw [hslice]
    dsimp [Kzero, Kdrift]
    rw [hueq, huxeq, huxxeq]
    exact hlower
  have hKzero : 0 ≤ Kzero := by
    dsimp [Kzero, wholeLineCauchyStrictPositivityZeroRate]
    positivity
  have hKdrift : 0 ≤ Kdrift := by
    dsimp [Kdrift, wholeLineCauchyStrictPositivityDriftRate]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (abs_nonneg _) (zero_le_one.trans p.hm))
        (Real.rpow_nonneg hM _))
      (Real.rpow_nonneg hM _)
  have hpos := wholeLine_pos_of_uniform_initial_of_drift_supersolution
    hT hδ hKzero hKdrift hcont hnonneg hinit htime hspace1 hspace2 hpde
  intro z _hz x
  have hext : wholeLineBUCTrajectoryExtend hT.le U z.1 = U z :=
    wholeLineBUCTrajectoryExtend_eq hT.le U z.2
  simpa [ue, U, hext] using hpos z.1 z.2 x

section WholeLineCauchyStrictPositivityAxiomAudit

#print axioms wholeLineCauchyHeatOp_pos_of_nonneg_of_pos_atBot
#print axioms wholeLineCauchyHeatBUCTotal_pos_of_nonneg_of_pos_atBot
#print axioms wholeLineSlabSup_le_of_drift_subsolution
#print axioms rpow_le_endpoint_rpow_sub_one_mul
#print axioms wholeLineChemotaxisFlux_deriv_eq_of_nonneg
#print axioms wholeLineCauchy_physical_pde_drift_lower_bound
#print axioms wholeLine_pos_of_uniform_initial_of_drift_supersolution
#print axioms wholeLineCauchyBUCMildFixedPoint_pos_of_uniformlyPositive

end WholeLineCauchyStrictPositivityAxiomAudit

end ShenWork.Paper1
