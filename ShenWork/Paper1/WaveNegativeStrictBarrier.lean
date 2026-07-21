/-
  Paper 1, negative sensitivity (χ<0): strict min-form upper barrier.

  The negative Schauder construction only exposes `ShenUpperBoundNegative`
  (the max-form `U x < max 1 (exp(-κx))`).  The stability datum
  `paper1_Theorem_1_2_chi_nonpos_paperDatum` needs the strict min-form barrier
  `HasStrictWaveUpperTailBound p c U` (`∀ x, 0 < U x ∧ U x < min (MChi p) exp(-κx)`,
  with `MChi p = 1` for `χ ≤ 0`).

  This file builds the three no-contact fields of
  `PositiveUpperBarrierContactContradictions` for the negative wave:
  * interface (`x = 0`): differentiability kink-avoidance (already available);
  * exp branch (`x > 0`): a STRICT `χ ≤ 0` exp-region operator sign, coming from
    the strict speed slack `A·κ² < 1` (`A = mγ|χ| + γ²|χ| + γ²`);
  * const branch (`x < 0`): a strong-maximum-principle argument ruling out a left
    plateau `U ≡ 1`.  A plateau forces `V'' = 0` hence `V = frozenElliptic p U = 1`
    on the plateau, contradicting the strict Green bound `frozenElliptic p U < 1`.
-/
import ShenWork.Paper1.UpperBarrierContact
import ShenWork.Paper1.WaveNegativeSuperBarrier

open Filter Topology MeasureTheory

namespace ShenWork.Paper1

noncomputable section

/-! ## Strict exp-region operator sign for χ ≤ 0

The strictness comes from the speed slack `A·κ² < 1`, re-derived here with an
explicit (non-private) coefficient so the `|χ|·(C-1) < 1` gap is strict. -/

/-- Explicit form of the negative-branch speed coefficient bound
`(mγ|χ| + γ²|χ| + γ²)·κ² < 1`, re-derived from `cStarLower p < c` without the
private `negativeBarrierSpeedCoefficient` alias. -/
theorem negStrict_speedCoeff_mul_kappa_sq_lt_one
    (p : CMParams) {c : ℝ} (hc : cStarLower p < c) :
    (p.m * p.γ * |p.χ| + p.γ ^ 2 * |p.χ| + p.γ ^ 2) * (kappa c) ^ 2 < 1 := by
  set A : ℝ := p.m * p.γ * |p.χ| + p.γ ^ 2 * |p.χ| + p.γ ^ 2 with hA_def
  have hm0 : 0 ≤ p.m := le_trans zero_le_one p.hm
  have hγ0 : 0 ≤ p.γ := le_trans zero_le_one p.hγ
  have hχ0 : 0 ≤ |p.χ| := abs_nonneg p.χ
  have hterm1 : 0 ≤ p.m * p.γ * |p.χ| :=
    mul_nonneg (mul_nonneg hm0 hγ0) hχ0
  have hterm2 : 0 ≤ p.γ ^ 2 * |p.χ| :=
    mul_nonneg (sq_nonneg p.γ) hχ0
  have hγsq_one : 1 ≤ p.γ ^ 2 := by nlinarith [p.hγ]
  have hA1 : 1 ≤ A := by
    rw [hA_def]; nlinarith
  have hA0 : 0 ≤ A := le_trans zero_le_one hA1
  have hsqrt_sq : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt hA0
  have hsqrt1 : 1 ≤ Real.sqrt A := by
    nlinarith [Real.sqrt_nonneg A]
  have hc2 : 2 < c := two_lt_of_cStarLower_lt hc
  have hsqrt_speed : Real.sqrt A + (Real.sqrt A)⁻¹ < c := by
    have hbranch : 1 / Real.sqrt A + Real.sqrt A < c :=
      lt_of_le_of_lt
        (le_max_right (1 / p.m + p.m) (1 / Real.sqrt A + Real.sqrt A))
        (by simpa [cStarLower, hA_def] using hc)
    simpa [one_div, add_comm] using hbranch
  have hsqrtκ : Real.sqrt A * kappa c < 1 :=
    gamma_mul_kappa_lt_one_of_gamma_add_inv_lt_speed hc2 hsqrt1 hsqrt_speed
  have hsqrtκ0 : 0 < Real.sqrt A * kappa c :=
    mul_pos (lt_of_lt_of_le zero_lt_one hsqrt1)
      (kappa_pos_of_cStarLower_lt hc)
  have hsquare : (Real.sqrt A * kappa c) ^ 2 < 1 := by nlinarith
  calc
    A * (kappa c) ^ 2 = (Real.sqrt A) ^ 2 * (kappa c) ^ 2 := by rw [hsqrt_sq]
    _ = (Real.sqrt A * kappa c) ^ 2 := by ring
    _ < 1 := hsquare

/-- Strict exponential-region paper-operator sign at `M = 1` for `χ ≤ 0`.
The favorable cross-frozen reaction term lets the strict speed slack
`A·κ² < 1` push the operator strictly below zero. -/
theorem paperWaveOperator_upperBarrier_exp_region_neg_of_chi_nonpos
    (p : CMParams) {c : ℝ} {u : ℝ → ℝ}
    (hχ : p.χ ≤ 0) (hα : p.α ≤ p.m + p.γ - 1)
    (hc : cStarLower p < c)
    (hu : InWaveTrapSet (kappa c) 1 u)
    {x : ℝ} (hx : Real.exp (-(kappa c) * x) < 1) :
    paperWaveOperator p c u (upperBarrier (kappa c) 1) x < 0 := by
  set κ : ℝ := kappa c with hκ_def
  have hκ : 0 < κ := kappa_pos_of_cStarLower_lt hc
  have hκ1 : κ < 1 := kappa_lt_one_of_cStarLower_lt hc
  have hc2 : 2 < c := two_lt_of_cStarLower_lt hc
  have hc_eq : c = κ + κ⁻¹ := (kappa_add_inv_eq_of_cStarLower_lt hc).symm
  have hscalar := paperUpperBarrierSuperScalarConditions_one_of_cStarLower_lt p hχ hα hc
  have hγκ : p.γ * κ < 1 := hscalar.hγκ
  have hmκ : κ * p.m ≤ 1 := hscalar.hmκ
  have hγ_pos : 0 < p.γ := lt_of_lt_of_le zero_lt_one p.hγ
  have hγκ_pos : 0 < p.γ * κ := mul_pos hγ_pos hκ
  have hden : 0 < 1 - p.γ ^ 2 * κ ^ 2 := by
    have hsq : (p.γ * κ) ^ 2 < 1 := by
      rw [sq_lt_one_iff_abs_lt_one, abs_of_pos hγκ_pos]; exact hγκ
    nlinarith
  -- strict speed slack
  have hAκ : (p.m * p.γ * |p.χ| + p.γ ^ 2 * |p.χ| + p.γ ^ 2) * κ ^ 2 < 1 :=
    negStrict_speedCoeff_mul_kappa_sq_lt_one p hc
  set C : ℝ := (1 + p.m * p.γ * κ ^ 2) / (1 - p.γ ^ 2 * κ ^ 2) with hC_def
  -- the strict resolvent gap: |χ|·(C-1) < 1
  have hCden : C * (1 - p.γ ^ 2 * κ ^ 2) = 1 + p.m * p.γ * κ ^ 2 := by
    rw [hC_def]; field_simp
  have hCgap : |p.χ| * (C - 1) < 1 := by
    have hrewrite : |p.χ| * (C - 1) * (1 - p.γ ^ 2 * κ ^ 2)
        = |p.χ| * (p.m * p.γ * κ ^ 2 + p.γ ^ 2 * κ ^ 2) := by
      have hcm1 : (C - 1) * (1 - p.γ ^ 2 * κ ^ 2)
          = p.m * p.γ * κ ^ 2 + p.γ ^ 2 * κ ^ 2 := by
        rw [sub_mul, hCden]; ring
      rw [mul_assoc, hcm1]
    have hkey : |p.χ| * (C - 1) * (1 - p.γ ^ 2 * κ ^ 2) < 1 * (1 - p.γ ^ 2 * κ ^ 2) := by
      rw [hrewrite, one_mul]
      nlinarith [hAκ, abs_nonneg p.χ]
    exact lt_of_mul_lt_mul_right hkey hden.le
  -- explicit exp-region form
  rw [paperWaveOperator_upperBarrier_exp_region_eq_of_kappa_speed p
    (ne_of_gt hκ) hc_eq (by simpa [hκ_def] using hx)]
  set E : ℝ := expDecay κ x with hE_def
  set V : ℝ := frozenElliptic p u x with hV_def
  set Vx : ℝ := deriv (frozenElliptic p u) x with hVx_def
  have hE_pos : 0 < E := by rw [hE_def]; exact expDecay_pos κ x
  have hE_lt1 : E < 1 := by
    rw [hE_def]; simpa [expDecay, hκ_def] using hx
  -- resolvent bound: -(κm)·Vx + V ≤ C·E^γ
  have hEγ : Real.exp (-(p.γ * κ) * x) = E ^ p.γ := by
    rw [hE_def, expDecay_rpow_eq κ p.γ x]; unfold expDecay; congr 1; ring
  have hres : -(p.m * κ) * Vx + V ≤ C * E ^ p.γ := by
    rw [hVx_def, hV_def, hC_def]
    have h := chemotaxis_resolvent_bound p hκ hγκ hmκ le_rfl hu x
    rw [hEγ] at h
    convert h using 1 <;> ring
  -- crossvalue term identity
  have hpow_m : E ^ (p.m - 1) * E = E ^ p.m := by
    calc E ^ (p.m - 1) * E = E ^ (p.m - 1) * E ^ (1 : ℝ) := by rw [Real.rpow_one E]
      _ = E ^ ((p.m - 1) + 1) := by rw [Real.rpow_add hE_pos]
      _ = E ^ p.m := by congr 1; ring
  have hpow_mγ : E * E ^ (p.m + p.γ - 1) = E ^ p.m * E ^ p.γ := by
    calc E * E ^ (p.m + p.γ - 1) = E ^ (1 : ℝ) * E ^ (p.m + p.γ - 1) := by rw [Real.rpow_one E]
      _ = E ^ (1 + (p.m + p.γ - 1)) := by rw [Real.rpow_add hE_pos]
      _ = E ^ (p.m + p.γ) := by congr 1; ring
      _ = E ^ p.m * E ^ p.γ := by rw [← Real.rpow_add hE_pos]
  have hcross_eq :
      -p.χ * p.m * E ^ (p.m - 1) * Vx * (-κ * E)
        + E * (-p.χ * E ^ (p.m - 1) * V + p.χ * E ^ (p.m + p.γ - 1)) =
      -p.χ * E ^ p.m * (-(p.m * κ) * Vx + V - E ^ p.γ) := by
    calc
      -p.χ * p.m * E ^ (p.m - 1) * Vx * (-κ * E)
          + E * (-p.χ * E ^ (p.m - 1) * V + p.χ * E ^ (p.m + p.γ - 1))
          =
        -p.χ * p.m * (E ^ (p.m - 1) * E) * Vx * (-κ)
          + (-p.χ * (E ^ (p.m - 1) * E) * V
            + p.χ * (E * E ^ (p.m + p.γ - 1))) := by ring
      _ = -p.χ * p.m * E ^ p.m * Vx * (-κ)
          + (-p.χ * E ^ p.m * V + p.χ * (E ^ p.m * E ^ p.γ)) := by
            rw [hpow_m, hpow_mγ]
      _ = -p.χ * E ^ p.m * (-(p.m * κ) * Vx + V - E ^ p.γ) := by ring
  -- bound crossvalue ≤ |χ|(C-1)·E^(m+γ)
  have hcoef_nonneg : 0 ≤ -p.χ * E ^ p.m :=
    mul_nonneg (neg_nonneg.mpr hχ) (Real.rpow_nonneg hE_pos.le p.m)
  have hbracket : -(p.m * κ) * Vx + V - E ^ p.γ ≤ (C - 1) * E ^ p.γ := by
    have : -(p.m * κ) * Vx + V - E ^ p.γ ≤ C * E ^ p.γ - E ^ p.γ := by linarith
    linarith [this]
  have hcross_le : -p.χ * E ^ p.m * (-(p.m * κ) * Vx + V - E ^ p.γ)
      ≤ -p.χ * E ^ p.m * ((C - 1) * E ^ p.γ) :=
    mul_le_mul_of_nonneg_left hbracket hcoef_nonneg
  -- |χ|(C-1)·E^(m+γ) ≤ |χ|(C-1)·E·E^α  and strict < E·E^α
  have hminus_chi : -p.χ = |p.χ| := by rw [abs_of_nonpos hχ]
  have hCgap_nonneg : 0 ≤ |p.χ| * (C - 1) := by
    have hC1 : 1 ≤ C := by
      rw [hC_def, le_div_iff₀ hden]
      have : 0 ≤ p.m * p.γ * κ ^ 2 :=
        mul_nonneg (mul_nonneg (le_trans zero_le_one p.hm) hγ_pos.le) (sq_nonneg κ)
      nlinarith [sq_nonneg κ, sq_nonneg p.γ]
    exact mul_nonneg (abs_nonneg _) (by linarith)
  have hEmγ_eq : -p.χ * E ^ p.m * ((C - 1) * E ^ p.γ)
      = (|p.χ| * (C - 1)) * (E ^ p.m * E ^ p.γ) := by
    rw [hminus_chi]; ring
  have hδ_nonneg : 0 ≤ p.m + p.γ - (p.α + 1) := by linarith
  have hEmγ_le : E ^ p.m * E ^ p.γ ≤ E * E ^ p.α := by
    have hsplit : E ^ p.m * E ^ p.γ = E ^ (p.α + 1) * E ^ (p.m + p.γ - (p.α + 1)) := by
      rw [← Real.rpow_add hE_pos, ← Real.rpow_add hE_pos]; congr 1; ring
    have hEα1 : E ^ (p.α + 1) = E * E ^ p.α := by
      rw [show E * E ^ p.α = E ^ (1 : ℝ) * E ^ p.α by rw [Real.rpow_one],
        ← Real.rpow_add hE_pos]; congr 1; ring
    rw [hsplit, hEα1]
    have hEδ_le1 : E ^ (p.m + p.γ - (p.α + 1)) ≤ 1 := by
      calc E ^ (p.m + p.γ - (p.α + 1)) ≤ (1 : ℝ) ^ (p.m + p.γ - (p.α + 1)) :=
            Real.rpow_le_rpow hE_pos.le hE_lt1.le hδ_nonneg
        _ = 1 := Real.one_rpow _
    have hEα1_nonneg : 0 ≤ E * E ^ p.α := mul_nonneg hE_pos.le (Real.rpow_nonneg hE_pos.le _)
    nlinarith [hEδ_le1, hEα1_nonneg]
  have hEEα_pos : 0 < E * E ^ p.α := mul_pos hE_pos (Real.rpow_pos_of_pos hE_pos _)
  have hcross_final : -p.χ * E ^ p.m * (-(p.m * κ) * Vx + V - E ^ p.γ) < E * E ^ p.α := by
    calc -p.χ * E ^ p.m * (-(p.m * κ) * Vx + V - E ^ p.γ)
          ≤ -p.χ * E ^ p.m * ((C - 1) * E ^ p.γ) := hcross_le
      _ = (|p.χ| * (C - 1)) * (E ^ p.m * E ^ p.γ) := hEmγ_eq
      _ ≤ (|p.χ| * (C - 1)) * (E * E ^ p.α) :=
            mul_le_mul_of_nonneg_left hEmγ_le hCgap_nonneg
      _ < 1 * (E * E ^ p.α) := by
            exact mul_lt_mul_of_pos_right hCgap hEEα_pos
      _ = E * E ^ p.α := by ring
  have hEq : -E * E ^ p.α - p.χ * p.m * E ^ (p.m - 1) * Vx * (-κ * E)
      + E * (-p.χ * E ^ (p.m - 1) * V + p.χ * E ^ (p.m + p.γ - 1))
      = -E * E ^ p.α + -p.χ * E ^ p.m * (-(p.m * κ) * Vx + V - E ^ p.γ) := by
    rw [← hcross_eq]; ring
  rw [hEq]; linarith [hcross_final]

/-- Strict exponential-contact residual for the negative branch (`χ ≤ 0`,
`M = 1`).  At an exponential-region contact `U x = exp(-κx)`, the frozen wave
operator applied to the upper barrier is strictly negative, because at contact
the paper/frozen off-diagonal correction vanishes and the paper operator is
strictly signed by the speed slack. -/
theorem negativeUpperBarrier_expStrictSuperAtContact
    (p : CMParams) {c : ℝ} {U : ℝ → ℝ}
    (hχ : p.χ ≤ 0) (hα : p.α ≤ p.m + p.γ - 1)
    (hc : cStarLower p < c)
    (htrap : InMonotoneWaveTrapSet (kappa c) 1 U) :
    ∀ x, Real.exp (-(kappa c) * x) < 1 →
      U x = Real.exp (-(kappa c) * x) →
        frozenWaveOperator p c U (upperBarrier (kappa c) 1) x < 0 := by
  intro x hx hUx
  set κ : ℝ := kappa c with hκ_def
  have hκ : 0 < κ := kappa_pos_of_cStarLower_lt hc
  have hpaper : paperWaveOperator p c U (upperBarrier κ 1) x < 0 :=
    paperWaveOperator_upperBarrier_exp_region_neg_of_chi_nonpos p hχ hα hc
      htrap.trap (by simpa [hκ_def] using hx)
  have hE : Real.exp (-κ * x) < 1 := by simpa [hκ_def] using hx
  have hWdiff : DifferentiableAt ℝ (upperBarrier κ 1) x := by
    have heq : Filter.EventuallyEq (nhds x) (upperBarrier κ 1) (expDecay κ) :=
      upperBarrier_eventuallyEq_exp_of_lt (by simpa [expDecay] using hE)
    exact (expDecay_hasDerivAt κ x).differentiableAt.congr_of_eventuallyEq heq
  have hoff := paperWaveOperator_eq_frozenWaveOperator_add_offdiag
    p (c := c) (u := U) (W := upperBarrier κ 1) x
    htrap.trap.cunif_bdd htrap.nonneg
    (fun y => upperBarrier_nonneg (by norm_num) y)
    hWdiff
    (frozenElliptic_deriv_differentiableAt p htrap.trap.cunif_bdd htrap.nonneg x)
    (hWdiff.rpow_const (Or.inr p.hm))
  have hbarx : upperBarrier κ 1 x = Real.exp (-κ * x) := by
    rw [upperBarrier_eq_exp_of_exp_le hE.le]
  have heqOp :
      paperWaveOperator p c U (upperBarrier κ 1) x =
        frozenWaveOperator p c U (upperBarrier κ 1) x := by
    have hUxE : U x = Real.exp (-κ * x) := by simpa [hκ_def] using hUx
    simp only [hbarx, hUxE, sub_self, mul_zero, add_zero] at hoff
    exact hoff
  rw [← heqOp]; exact hpaper

/-! ## Const-branch: strong maximum principle (no left plateau)

A left plateau `U ≡ 1` on `(-∞, x]` forces `V'' = 0` on the plateau interior
(the stationary equation collapses to `-χ·V'' = 0`), hence
`V = frozenElliptic p U = 1` there.  But the Green representation makes
`frozenElliptic p U < 1` strictly whenever `U ≤ 1` and `U → 0` at `+∞`.  -/

/-- Strict Green (elliptic) bound: a nonnegative profile with `U ≤ 1`
everywhere and `U → 0` at `+∞` has `frozenElliptic p U x < 1` at every point.
The strictness comes from the Green kernel integrating the strictly-positive
deficit `1 - U^γ` over the right tail. -/
theorem frozenElliptic_lt_one_of_le_one_tendsto
    (p : CMParams) {U : ℝ → ℝ}
    (hUcont : Continuous U) (hnonneg : ∀ z, 0 ≤ U z) (hle : ∀ z, U z ≤ 1)
    (hlim : Tendsto U atTop (𝓝 0)) (x : ℝ) :
    frozenElliptic p U x < 1 := by
  have hγ0 : 0 ≤ p.γ := le_trans zero_le_one p.hγ
  have hγpos : 0 < p.γ := lt_of_lt_of_le zero_lt_one p.hγ
  have hUγ_cont : Continuous (fun z => (U z) ^ p.γ) :=
    hUcont.rpow_const (fun z => Or.inr hγ0)
  set g : ℝ → ℝ := fun z => 1 - (U z) ^ p.γ with hg_def
  have hg_cont : Continuous g :=
    continuous_const.sub hUγ_cont
  have hg_nonneg : ∀ z, 0 ≤ g z := by
    intro z
    have : (U z) ^ p.γ ≤ 1 := Real.rpow_le_one (hnonneg z) (hle z) hγ0
    simp only [hg_def]; linarith
  have hg_le1 : ∀ z, g z ≤ 1 := by
    intro z
    have : 0 ≤ (U z) ^ p.γ := Real.rpow_nonneg (hnonneg z) _
    simp only [hg_def]; linarith
  -- integrability of the kernel products
  have hint_one : Integrable
      (fun y => Real.exp (-Real.sqrt 1 * |x - y|) * (fun _ : ℝ => (1 : ℝ)) y) :=
    psi_kernel_mul_bounded_integrable (M := 1) one_pos (by norm_num)
      (fun _ => by norm_num) x aestronglyMeasurable_const
  have hint_Uγ : Integrable
      (fun y => Real.exp (-Real.sqrt 1 * |x - y|) * (U y) ^ p.γ) :=
    psi_kernel_mul_bounded_integrable (M := 1) one_pos (by norm_num)
      (fun z => by
        rw [abs_of_nonneg (Real.rpow_nonneg (hnonneg z) _)]
        exact Real.rpow_le_one (hnonneg z) (hle z) hγ0)
      x hUγ_cont.aestronglyMeasurable
  -- Psi g = 1 - frozenElliptic
  have hPsi_g_eq : Psi g 1 1 x = 1 - frozenElliptic p U x := by
    have hsub : Psi g 1 1 x
        = Psi (fun _ : ℝ => (1 : ℝ)) 1 1 x - Psi (fun z => (U z) ^ p.γ) 1 1 x := by
      simp only [hg_def]
      exact Psi_sub x hint_one hint_Uγ
    rw [hsub, Psi_const (by norm_num) x]
    rfl
  -- 0 < Psi g via the Green positivity template
  have hker_nonneg : 0 ≤ fun y => Real.exp (-Real.sqrt 1 * |x - y|) * g y :=
    fun y => mul_nonneg (Real.exp_nonneg _) (hg_nonneg y)
  have hker_int : Integrable (fun y => Real.exp (-Real.sqrt 1 * |x - y|) * g y) :=
    psi_kernel_mul_bounded_integrable (M := 1) one_pos (by norm_num)
      (fun z => by rw [abs_of_nonneg (hg_nonneg z)]; exact hg_le1 z)
      x hg_cont.aestronglyMeasurable
  obtain ⟨N, hN⟩ : ∃ N, ∀ z ≥ N, U z < 1 := by
    have hev : ∀ᶠ z in atTop, U z < 1 :=
      hlim (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
    exact eventually_atTop.mp hev
  have hsub : Set.Icc N (N + 1) ⊆
      Function.support (fun y => Real.exp (-Real.sqrt 1 * |x - y|) * g y) := by
    intro y hy
    have hUy1 : U y < 1 := hN y hy.1
    have hgy : 0 < g y := by
      have : (U y) ^ p.γ < 1 := Real.rpow_lt_one (hnonneg y) hUy1 hγpos
      simp only [hg_def]; linarith
    exact ne_of_gt (mul_pos (Real.exp_pos _) hgy)
  have hmeas_pos : 0 < volume
      (Function.support (fun y => Real.exp (-Real.sqrt 1 * |x - y|) * g y)) := by
    have hIcc : (0 : ENNReal) < volume (Set.Icc N (N + 1)) := by
      rw [Real.volume_Icc]
      simp only [add_sub_cancel_left]
      exact ENNReal.ofReal_pos.mpr one_pos
    exact lt_of_lt_of_le hIcc (measure_mono hsub)
  have hint_pos : 0 < ∫ y, Real.exp (-Real.sqrt 1 * |x - y|) * g y :=
    (integral_pos_iff_support_of_nonneg hker_nonneg hker_int).mpr hmeas_pos
  have hPsi_pos : 0 < Psi g 1 1 x := by
    have hval : Psi g 1 1 x
        = 1 / (2 * Real.sqrt 1) * ∫ y, Real.exp (-Real.sqrt 1 * |x - y|) * g y := rfl
    rw [hval]
    apply mul_pos _ hint_pos
    positivity
  linarith [hPsi_pos, hPsi_g_eq]

/-- No left plateau at level `1` for the negative wave.  A plateau `U ≡ 1` on
`(-∞, x]` collapses the stationary equation to `-χ·V'' = 0`, forcing `V = 1` on
the plateau, contradicting the strict Green bound `frozenElliptic p U < 1`. -/
theorem negativeUpperBarrier_noConstLeftPlateau
    (p : CMParams) {c : ℝ} {U : ℝ → ℝ}
    (hχ : p.χ < 0)
    (htrap : InMonotoneWaveTrapSet (kappa c) 1 U)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0)
    (hUdiff : Differentiable ℝ U)
    (_hUd_diff : Differentiable ℝ (deriv U))
    (hlim : Tendsto U atTop (𝓝 0)) :
    ∀ x, (1 : ℝ) < Real.exp (-(kappa c) * x) →
      (∀ y, y ≤ x → U y = 1) → False := by
  intro x _hx hplateau
  set x₀ : ℝ := x - 1 with hx0_def
  have hx0_lt : x₀ < x := by rw [hx0_def]; linarith
  set V : ℝ → ℝ := frozenElliptic p U with hV_def
  -- derivatives of U vanish on the open plateau interior
  have hderivU_zero_on : ∀ y ∈ Set.Iio x, deriv U y = 0 := by
    intro y hy
    have hUconst : U =ᶠ[𝓝 y] (fun _ => (1 : ℝ)) := by
      filter_upwards [Iio_mem_nhds hy] with z hz
      exact hplateau z hz.le
    rw [hUconst.deriv_eq]; simp
  have hderivU_eq : deriv U =ᶠ[𝓝 x₀] (fun _ => (0 : ℝ)) := by
    filter_upwards [Iio_mem_nhds hx0_lt] with y hy
    exact hderivU_zero_on y hy
  have hdU_x0 : deriv U x₀ = 0 := hderivU_zero_on x₀ hx0_lt
  have hddU_x0 : deriv (deriv U) x₀ = 0 := by
    rw [hderivU_eq.deriv_eq]; simp
  have hiter2_x0 : iteratedDeriv 2 U x₀ = 0 := by
    simp only [iteratedDeriv_succ, iteratedDeriv_zero]; exact hddU_x0
  -- chemotaxis derivative collapses to V'' on the plateau
  have hchemeq : (fun y => (U y) ^ p.m * deriv V y) =ᶠ[𝓝 x₀] deriv V := by
    filter_upwards [Iio_mem_nhds hx0_lt] with y hy
    rw [hplateau y hy.le, Real.one_rpow, one_mul]
  have hchem_deriv :
      deriv (fun y => (U y) ^ p.m * deriv V y) x₀ = deriv (deriv V) x₀ :=
    hchemeq.deriv_eq
  have hUx0 : U x₀ = 1 := hplateau x₀ hx0_lt.le
  -- stationary equation at x₀
  have hstat0 := hstat x₀
  unfold frozenWaveOperator at hstat0
  rw [← hV_def] at hstat0
  rw [hiter2_x0, hdU_x0, hchem_deriv, hUx0] at hstat0
  simp only [Real.one_rpow, mul_zero, sub_self, mul_zero, add_zero] at hstat0
  -- hstat0 : -(p.χ * deriv (deriv V) x₀) = 0
  have hV2_zero : deriv (deriv V) x₀ = 0 := by
    have hχne : p.χ ≠ 0 := ne_of_lt hχ
    have : p.χ * deriv (deriv V) x₀ = 0 := by linarith [hstat0]
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hχne
    · exact h
  -- V''(x₀) = V(x₀) - 1, so V(x₀) = 1
  have hV2_eq : deriv (deriv V) x₀ = V x₀ - (U x₀) ^ p.γ := by
    rw [hV_def]
    exact frozenElliptic_deriv_deriv_eq p htrap.trap.cunif_bdd htrap.nonneg x₀
  rw [hUx0, Real.one_rpow] at hV2_eq
  have hVx0_one : V x₀ = 1 := by
    rw [hV2_zero] at hV2_eq; linarith
  -- strict Green bound contradicts V(x₀) = 1
  have hVlt : V x₀ < 1 :=
    frozenElliptic_lt_one_of_le_one_tendsto p hUdiff.continuous htrap.nonneg
      (fun z => htrap.le_M z) hlim x₀
  rw [hVx0_one] at hVlt
  exact lt_irrefl 1 hVlt

/-- The negative-branch strict exponential-contact residual packaged in the
`PositiveUpperBarrierExpStrictContactResidual` interface (`MChi p = 1`). -/
theorem negativeUpperBarrier_expStrictContactResidual
    (p : CMParams) {c : ℝ} {U : ℝ → ℝ}
    (hχ : p.χ < 0) (hα : p.α ≤ p.m + p.γ - 1)
    (hc : cStarLower p < c)
    (htrap : InMonotoneWaveTrapSet (kappa c) 1 U) :
    PositiveUpperBarrierExpStrictContactResidual p c U := by
  have hM1 : MChi p = 1 := MChi_eq_one_of_chi_nonpos p hχ.le
  refine ⟨?_⟩
  intro x hx hUx
  rw [hM1] at hx ⊢
  exact negativeUpperBarrier_expStrictSuperAtContact p hχ.le hα hc htrap x hx hUx

/-! ## Assembly: the full negative-branch no-contact package and the strict
min-form upper tail bound. -/

/-- All three no-contact fields for the negative wave (`χ < 0`, `M = 1`). -/
theorem negativeWave_contactContradictions
    (p : CMParams) {c : ℝ} {U : ℝ → ℝ}
    (hχ : p.χ < 0) (hα : p.α ≤ p.m + p.γ - 1)
    (hc : cStarLower p < c)
    (htrap : InMonotoneWaveTrapSet (kappa c) 1 U)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0)
    (hUdiff : Differentiable ℝ U) (hUd_diff : Differentiable ℝ (deriv U))
    (hlim : Tendsto U atTop (𝓝 0)) :
    PositiveUpperBarrierContactContradictions p c U := by
  have hM1 : MChi p = 1 := MChi_eq_one_of_chi_nonpos p hχ.le
  have hκ : 0 < kappa c := kappa_pos_of_cStarLower_lt hc
  have htrapM : InMonotoneWaveTrapSet (kappa c) (MChi p) U := by rw [hM1]; exact htrap
  have hres : PositiveUpperBarrierRemainingContactResidual p c U :=
    { no_const_left_plateau := by
        rw [hM1]
        exact negativeUpperBarrier_noConstLeftPlateau p hχ htrap hstat
          hUdiff hUd_diff hlim
      exp_strict_super_at_contact :=
        (negativeUpperBarrier_expStrictContactResidual p hχ hα hc htrap).exp_strict_super_at_contact }
  have hsmooth : PositiveUpperBarrierSmoothBranchNoContact p c U :=
    positiveUpperBarrierSmoothBranchNoContact_of_remainingResidual_profile
      (by rw [hM1]; norm_num) htrapM hstat hUdiff hUd_diff hres
  exact PositiveUpperBarrierContactContradictions.of_smoothBranchNoContact_profile
    hsmooth hκ (by rw [hM1]; norm_num) htrapM hUdiff

/-- **Strict min-form upper tail bound for the negative wave.**
`∀ x, 0 < U x ∧ U x < min (MChi p) (exp(-κx))`, exactly the input the stability
datum `paper1_Theorem_1_2_chi_nonpos_paperDatum` requires. -/
theorem negativeWave_hasStrictWaveUpperTailBound
    (p : CMParams) {c : ℝ} {U : ℝ → ℝ}
    (hχ : p.χ < 0) (hα : p.α ≤ p.m + p.γ - 1)
    (hc : cStarLower p < c)
    (htrap : InMonotoneWaveTrapSet (kappa c) 1 U)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0)
    (hpos : ∀ x, 0 < U x)
    (hUdiff : Differentiable ℝ U) (hUd_diff : Differentiable ℝ (deriv U))
    (hlim : Tendsto U atTop (𝓝 0)) :
    HasStrictWaveUpperTailBound p c U := by
  have hM1 : MChi p = 1 := MChi_eq_one_of_chi_nonpos p hχ.le
  have htrapM : InMonotoneWaveTrapSet (kappa c) (MChi p) U := by rw [hM1]; exact htrap
  have hcontra : PositiveUpperBarrierContactContradictions p c U :=
    negativeWave_contactContradictions p hχ hα hc htrap hstat hUdiff hUd_diff hlim
  have hstrict : ∀ x, U x < upperBarrier (kappa c) (MChi p) x :=
    strict_upperBarrier_MChi_of_contactContradictions htrapM hcontra
  intro x
  exact ⟨hpos x, by simpa [upperBarrier] using hstrict x⟩

section AxiomAudit
#print axioms negStrict_speedCoeff_mul_kappa_sq_lt_one
#print axioms paperWaveOperator_upperBarrier_exp_region_neg_of_chi_nonpos
#print axioms negativeUpperBarrier_expStrictSuperAtContact
#print axioms frozenElliptic_lt_one_of_le_one_tendsto
#print axioms negativeUpperBarrier_noConstLeftPlateau
#print axioms negativeWave_hasStrictWaveUpperTailBound
end AxiomAudit

end

end ShenWork.Paper1
