/-
  Static elliptic `v = R(u)` characterization and L²-difference control, both
  UNCONDITIONAL for positive classical solutions.

  ## Step (1): pointwise elliptic representative (unconditional for solutions)

  `solution_v_eq_resolver_pointwise_unconditional`: for a classical solution
  `(u,v)` and `t ∈ (0,T)`, at every interior point `x ∈ (0,1)`,

    `intervalNeumannResolverR p (u t) ⟨x,…⟩ = intervalDomainLift (v t) x`.

  This DISCHARGES all five carried hypotheses of the conditional
  `ShenWork.IntervalEllipticCharacterization.solution_v_eq_resolver_pointwise`:
  the resolver-side summability `hRsum` from
  `solution_resolver_cosineSeries_summable`, and the `v`-side data
  `F`/`hFcont`/`hFcoeff`/`hFsum`/`hFeq` by constructing the explicit globally
  continuous even-reflection representative `F` of `lift (v t)` (the lift composed
  with a clamp into `[0,1]`) and feeding the C²-Neumann regularity (conjuncts 6,7)
  into `ShenWork.IntervalCosineCoeffDecay.fourierCoeff_reflCircle_summable`.

  ## Step (2): static L² control of the `v`-difference by `E_u`

  For two positive classical solutions `(u₁,v₁),(u₂,v₂)` and `τ ∈ (0,T)`:

    `∫₀¹ (lift(v₁ τ) − lift(v₂ τ))² ≤ C · E_u(τ)`     (value), and
    `∫₀¹ (∂ₓlift(v₁ τ) − ∂ₓlift(v₂ τ))² ≤ C · E_u(τ)`  (gradient),

  where `E_u(τ) = ∫₀¹ (lift(u₁−u₂) τ)²`.  Route: step (1) ⇒ `v_i = R(u_i)`;
  the SUP resolver-Lipschitz bounds (`intervalNeumannResolverR_sup_lipschitz` /
  `…_grad_sup_lipschitz`) give `|v₁−v₂|, |∂ₓ(v₁−v₂)| ≤ C·coeffL2Norm(â₁−â₂)`;
  the cosine-Parseval/Bessel bound `unitIntervalNeumannCosineCoeff_l2_bound`
  gives `coeffL2Norm(â₁−â₂)² ≤ 4·∫₀¹(ν u₁^γ − ν u₂^γ)²`; the local Lipschitz of
  `x ↦ x^γ` on the bounded positive range of the two solutions
  (`rpow_lipschitz_on_solution_range`) gives
  `∫₀¹(ν u₁^γ − ν u₂^γ)² ≤ (ν L)²·E_u`; and `∫₀¹ g² ≤ (sup g)²·1` passes sup→L²
  on the unit interval.

  This file contains **no `sorry`, no `admit`, no custom `axiom`.**
-/
import ShenWork.Paper2.IntervalDomainL2UStaticVControl
import ShenWork.PDE.IntervalCosineCoeffDecay

open MeasureTheory intervalIntegral
open ShenWork.IntervalDomain ShenWork.CosineSpectrum
open ShenWork.PDE ShenWork.IntervalEllipticCharacterization
open ShenWork.IntervalCosineCoeffDecay ShenWork.IntervalCosineInversion
open ShenWork.HeatKernelGradientEstimates ShenWork.IntervalNeumannFullKernel
open ShenWork.PDE.ResolventEstimate ShenWork.CosineParsevalBridge
open ShenWork.IntervalResolverGradientBridge
open ShenWork.Paper3 (unitIntervalNeumannSpectrum)
open scoped Topology

namespace ShenWork.Paper2

noncomputable section

open ShenWork.Paper2 (IsPaper2ClassicalSolution)

/-! ## Step (1): the explicit continuous even-reflection representative of `lift (v t)`

The lift `intervalDomainLift (v t)` is `0` outside `[0,1]` (definitional), so it is
NOT globally continuous in general.  We build a genuinely continuous global
representative by composing the lift with the continuous clamp
`clamp x = max 0 (min 1 x)` into `[0,1]`; it equals the lift on `[0,1]` and is
continuous everywhere because the lift is continuous on the compact `[0,1]`
(conjunct 7). -/

/-- The clamp `ℝ → [0,1]`, `clamp x = max 0 (min 1 x)`. -/
def clamp01 (x : ℝ) : ℝ := max 0 (min 1 x)

lemma clamp01_continuous : Continuous clamp01 := by
  unfold clamp01; fun_prop

lemma clamp01_mem (x : ℝ) : clamp01 x ∈ Set.Icc (0 : ℝ) 1 := by
  unfold clamp01
  constructor
  · exact le_max_left _ _
  · rw [max_le_iff]; exact ⟨by norm_num, min_le_left _ _⟩

lemma clamp01_eq_self {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : clamp01 x = x := by
  unfold clamp01
  rw [min_eq_right hx.2, max_eq_right hx.1]

/-- The continuous global representative of `lift (v t)`: the lift clamped to
`[0,1]`. -/
def liftRepr (w : intervalDomainPoint → ℝ) : ℝ → ℝ :=
  fun x => intervalDomainLift w (clamp01 x)

/-- `liftRepr w` agrees with `lift w` on `[0,1]`. -/
lemma liftRepr_eq_on_Icc {w : intervalDomainPoint → ℝ} {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : liftRepr w x = intervalDomainLift w x := by
  rw [liftRepr, clamp01_eq_self hx]

/-- `liftRepr w` is globally continuous when `lift w` is continuous on the
compact `[0,1]` (e.g. for `C²` data). -/
lemma liftRepr_continuous {w : intervalDomainPoint → ℝ}
    (hcont : ContinuousOn (intervalDomainLift w) (Set.Icc (0 : ℝ) 1)) :
    Continuous (liftRepr w) := by
  have hmaps : Set.MapsTo clamp01 Set.univ (Set.Icc (0 : ℝ) 1) :=
    fun x _ => clamp01_mem x
  have hcomp : ContinuousOn (liftRepr w) Set.univ :=
    (hcont.comp clamp01_continuous.continuousOn hmaps)
  exact continuousOn_univ.mp hcomp

/-- Cosine coefficients depend only on values on `[0,1]`: if `f = g` there, the
coefficients agree (the raw coefficient integrates over `[0,1]`). -/
lemma cosineCoeffs_congr_on_Icc {f g : ℝ → ℝ}
    (hfg : ∀ x ∈ Set.Icc (0:ℝ) 1, f x = g x) (k : ℕ) :
    cosineCoeffs f k = cosineCoeffs g k := by
  simp only [cosineCoeffs,
    ShenWork.HeatKernelGradientEstimates.unitIntervalNeumannCosineCoeff,
    ShenWork.HeatKernelGradientEstimates.unitIntervalCosineRawCoeff]
  have hint : ∀ m : ℕ,
      (∫ x in (0:ℝ)..1, (Real.cos ((m:ℝ) * Real.pi * x) : ℂ) * ((f x : ℝ) : ℂ))
      = ∫ x in (0:ℝ)..1, (Real.cos ((m:ℝ) * Real.pi * x) : ℂ) * ((g x : ℝ) : ℂ) := by
    intro m
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
    simp only []
    rw [hfg x hx]
  rcases eq_or_ne k 0 with hk | hk
  · subst hk; rw [if_pos rfl, if_pos rfl, hint 0]
  · rw [if_neg hk, if_neg hk, hint k]

/-- Cosine coefficients of `liftRepr w` equal those of `lift w` (they agree on
`[0,1]`). -/
lemma cosineCoeffs_liftRepr {w : intervalDomainPoint → ℝ} (k : ℕ) :
    cosineCoeffs (liftRepr w) k = cosineCoeffs (intervalDomainLift w) k :=
  cosineCoeffs_congr_on_Icc (fun x hx => liftRepr_eq_on_Icc hx) k

/- **`ℓ¹` summability of the even-reflection Fourier coefficients for a continuous
representative `F` of a C²-Neumann interval datum `g`.**  We only need the
C²/Neumann data of `g` (the genuine lift, whose endpoint derivative values and
one-sided limits are recorded by the solution regularity); `F` only needs to be
continuous and to agree with `g` on `[0,1]`.  Because the Fourier coefficients of
the even reflection depend on `F` only through its `[0,1]` cosine integral
(= `g`'s), and the decay bound `cosineCoeff_decay` needs only
`ContDiffOn ℝ 2 g (Icc 0 1)` plus the Neumann data, we re-run the comparison
directly. -/
set_option maxHeartbeats 1200000 in
-- the ℤ→ℕ regrouping (`Summable.of_nat_of_neg_add_one`) plus two `field_simp`
-- comparisons against `∑ 1/n²` push the default heartbeat budget.
theorem fourierCoeff_reflCircle_summable_of_repr
    {F g : ℝ → ℝ} (hFcont : Continuous F)
    (hgC2 : ContDiffOn ℝ 2 g (Set.Icc (0 : ℝ) 1))
    (hagree : ∀ x ∈ Set.Icc (0:ℝ) 1, F x = g x)
    (htend0 : Filter.Tendsto (deriv g) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (htend1 : Filter.Tendsto (deriv g) (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0))
    (hbc0 : deriv g 0 = 0) (hbc1 : deriv g 1 = 0) :
    Summable (fun n : ℤ => fourierCoeff (reflCircle F) n) := by
  classical
  obtain ⟨M, hMnonneg, hMbound⟩ := exists_laplacianCoeff_bound hgC2
  -- the per-coefficient value equals `g`'s `[0,1]` cosine integral.
  have hcoeff : ∀ n : ℤ, fourierCoeff (reflCircle F) n
      = ((∫ x in (0:ℝ)..1, Real.cos ((n:ℝ) * Real.pi * x) * g x : ℝ) : ℂ) := by
    intro n
    rw [fourierCoeff_reflCircle, fco_eq_ofReal F hFcont]
    congr 1
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
    simp only []
    rw [hagree x hx]
  -- evenness of the Fourier coefficient in `n` (reuse the proved `fco_neg`).
  have hfcoeff_even : ∀ n : ℤ,
      fourierCoeff (reflCircle F) (-n) = fourierCoeff (reflCircle F) n := by
    intro n
    rw [fourierCoeff_reflCircle, fourierCoeff_reflCircle, fco_neg F hFcont]
  rw [← summable_norm_iff]
  apply Summable.of_nat_of_neg_add_one
  · rw [← summable_nat_add_iff 1]
    have hmaj : Summable fun n : ℕ =>
        (M / Real.pi ^ 2) * (1 / ((n : ℝ) + 1) ^ 2) := by
      have hp2 : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by
        have := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
        simpa using (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).2 this
      exact hp2.mul_left _
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ hmaj
    intro n
    rw [hcoeff, Complex.norm_real, Real.norm_eq_abs]
    have hdecay := cosineCoeff_decay hgC2 htend0 htend1 hbc0 hbc1 hMnonneg hMbound
      (n := n + 1) (Nat.le_add_left 1 n)
    have hcast : ((↑(n + 1) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
    rw [hcast] at hdecay
    have hsplit : M / (((n:ℝ) + 1) * Real.pi) ^ 2
        = (M / Real.pi ^ 2) * (1 / ((n:ℝ) + 1) ^ 2) := by
      have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
      have hn1 : ((n:ℝ) + 1) ≠ 0 := by positivity
      rw [mul_pow]; field_simp
    rw [hsplit] at hdecay
    -- align the cast `↑↑(n+1)` in the goal with `↑n + 1` in `hdecay`.
    rw [show ((((n : ℕ) + 1 : ℕ) : ℤ) : ℝ) = (n : ℝ) + 1 by push_cast; ring]
    exact hdecay
  · -- negative part via evenness.
    have heven : ∀ n : ℕ,
        ‖fourierCoeff (reflCircle F) (-((n : ℤ) + 1))‖
          = ‖fourierCoeff (reflCircle F) ((n : ℤ) + 1)‖ := by
      intro n
      rw [hfcoeff_even ((n : ℤ) + 1)]
    have hpos1 : Summable fun n : ℕ => ‖fourierCoeff (reflCircle F) ((n : ℤ) + 1)‖ := by
      have hmaj : Summable fun n : ℕ =>
          (M / Real.pi ^ 2) * (1 / ((n : ℝ) + 1) ^ 2) := by
        have hp2 : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by
          have := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
          simpa using (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).2 this
        exact hp2.mul_left _
      refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ hmaj
      intro n
      rw [hcoeff, Complex.norm_real, Real.norm_eq_abs]
      have hdecay := cosineCoeff_decay hgC2 htend0 htend1 hbc0 hbc1 hMnonneg hMbound
        (n := n + 1) (Nat.le_add_left 1 n)
      have hcast : ((↑(n + 1) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
      rw [hcast] at hdecay
      have hsplit : M / (((n:ℝ) + 1) * Real.pi) ^ 2
          = (M / Real.pi ^ 2) * (1 / ((n:ℝ) + 1) ^ 2) := by
        have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
        have hn1 : ((n:ℝ) + 1) ≠ 0 := by positivity
        rw [mul_pow]; field_simp
      rw [hsplit] at hdecay
      rw [show ((((n : ℤ) + 1 : ℤ)) : ℝ) = (n : ℝ) + 1 by push_cast; ring]
      exact hdecay
    exact hpos1.congr (fun n => (heven n).symm)

/-- **Pointwise elliptic characterization, UNCONDITIONAL for solutions.**

For a positive classical solution `(u,v)` and an interior time `t ∈ (0,T)`, at
every interior point `x ∈ (0,1)`,

  `intervalNeumannResolverR p (u t) ⟨x,…⟩ = intervalDomainLift (v t) x`. -/
theorem solution_v_eq_resolver_pointwise_unconditional
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    intervalNeumannResolverR p (u t) ⟨x, Set.Ioo_subset_Icc_self hx⟩ =
      intervalDomainLift (v t) x := by
  classical
  -- regularity conjuncts for `v(·,t)`.
  have hreg : intervalDomainClassicalRegularity T u v := hsol.regularity
  have h7 := (hreg.2.2.2.2.1 t ht).2
  obtain ⟨hC2v, hbc0, hbc1⟩ := h7
  have h6 := (hreg.2.2.2.1 t ht).2
  obtain ⟨htend0, htend1⟩ := h6
  -- the continuous global representative `F` of `lift (v t)`.
  set F : ℝ → ℝ := liftRepr (v t) with hFdef
  have hVcontOn : ContinuousOn (intervalDomainLift (v t)) (Set.Icc (0:ℝ) 1) :=
    hC2v.continuousOn
  have hFcont : Continuous F := liftRepr_continuous hVcontOn
  -- `F` agrees with `lift (v t)` on `[0,1]`.
  have hFeqOn : ∀ y ∈ Set.Icc (0:ℝ) 1, F y = intervalDomainLift (v t) y :=
    fun y hy => liftRepr_eq_on_Icc hy
  -- (hFcoeff) cosine coefficients of `F` equal those of `lift (v t)`.
  have hFcoeff : ∀ k, cosineCoeffs F k = cosineCoeffs (intervalDomainLift (v t)) k :=
    fun k => cosineCoeffs_liftRepr k
  -- (hFsum) `ℓ¹` summability of the even-reflection Fourier coefficients of `F`,
  -- via the C²-Neumann data of the genuine lift `g := lift (v t)`.
  have hFsum : Summable (fun n : ℤ => fourierCoeff (reflCircle F) n) :=
    fourierCoeff_reflCircle_summable_of_repr hFcont hC2v hFeqOn htend0 htend1 hbc0 hbc1
  -- (hRsum) resolver-side summability, unconditional for solutions.
  have hRsum : Summable fun k : ℕ =>
      (intervalNeumannResolverCoeff p (u t) k).re * unitIntervalCosineMode k x :=
    solution_resolver_cosineSeries_summable hsol ht x
  -- (hFeq) `F` equals the lift at the interior point `x`.
  have hFeq : F x = intervalDomainLift (v t) x :=
    hFeqOn x (Set.Ioo_subset_Icc_self hx)
  -- feed the conditional pointwise characterization.
  exact ShenWork.IntervalEllipticCharacterization.solution_v_eq_resolver_pointwise
    hsol ht F hFcont hFcoeff hFsum hx hFeq hRsum

/-! ## Step (2): static L² control of the `v`-difference by `E_u`

We combine step (1) (`v_i = R(u_i)` pointwise on the interior) with the SUP
resolver-Lipschitz bounds and the cosine-Parseval/Bessel bound, then pass sup→L²
on the unit interval; the source nonlinearity `u ↦ ν u^γ` is handled by the local
Lipschitz of `x ↦ x^γ` on the common bounded positive range of the two solutions. -/

/-- **Local Lipschitz of `x ↦ x^γ` on a bounded positive interval `[δ,M]`
(`δ > 0`).**  For `a, b ∈ [δ,M]`, `|a^γ − b^γ| ≤ L·|a−b|` with
`L = γ·(δ^(γ−1) + M^(γ−1))`.  Proof: MVT on the convex `Icc δ M`, where
`(·)^γ` has derivative `γ·x^(γ−1)` (well-defined since `x ≥ δ > 0`), bounded by
`L` (the derivative is monotone in the sign of `γ−1`; both endpoint values are
nonnegative, so their sum dominates). -/
theorem rpow_lipschitz_on_pos_Icc
    {γ δ M : ℝ} (hγ : 0 < γ) (hδ : 0 < δ) {a b : ℝ}
    (ha : a ∈ Set.Icc δ M) (hb : b ∈ Set.Icc δ M) :
    |a ^ γ - b ^ γ| ≤ γ * (δ ^ (γ - 1) + M ^ (γ - 1)) * |a - b| := by
  set L : ℝ := γ * (δ ^ (γ - 1) + M ^ (γ - 1)) with hL
  -- the derivative bound on `Icc δ M`.
  have hbound : ∀ x ∈ Set.Icc δ M, ‖γ * x ^ (γ - 1)‖ ≤ L := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hδ hx.1
    have hxle : x ≤ M := hx.2
    have hδle : δ ≤ x := hx.1
    have hMpos : 0 < M := lt_of_lt_of_le hxpos hxle
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    -- `x^(γ-1) ≤ δ^(γ-1) + M^(γ-1)` for `x ∈ [δ,M]`, both cases of the sign of `γ-1`.
    have hxbound : x ^ (γ - 1) ≤ δ ^ (γ - 1) + M ^ (γ - 1) := by
      rcases le_or_gt 1 γ with hγ1 | hγ1
      · -- `γ-1 ≥ 0`: `x^(γ-1)` increasing, `≤ M^(γ-1)`.
        have hmono : x ^ (γ - 1) ≤ M ^ (γ - 1) :=
          Real.rpow_le_rpow hxpos.le hxle (by linarith)
        have hδnn : 0 ≤ δ ^ (γ - 1) := by positivity
        linarith
      · -- `γ-1 < 0`: `x^(γ-1)` decreasing, `≤ δ^(γ-1)`.
        have hmono : x ^ (γ - 1) ≤ δ ^ (γ - 1) :=
          Real.rpow_le_rpow_of_nonpos hδ hδle (by linarith)
        have hMnn : 0 ≤ M ^ (γ - 1) := by positivity
        linarith
    have : γ * x ^ (γ - 1) ≤ γ * (δ ^ (γ - 1) + M ^ (γ - 1)) :=
      mul_le_mul_of_nonneg_left hxbound hγ.le
    rwa [hL]
  -- MVT on the convex set `Icc δ M`.
  have hconv : Convex ℝ (Set.Icc δ M) := convex_Icc δ M
  have hderiv : ∀ x ∈ Set.Icc δ M,
      HasDerivWithinAt (fun y : ℝ => y ^ γ) (γ * x ^ (γ - 1)) (Set.Icc δ M) x := by
    intro x hx
    have hxne : x ≠ 0 := ne_of_gt (lt_of_lt_of_le hδ hx.1)
    exact (Real.hasDerivAt_rpow_const (Or.inl hxne)).hasDerivWithinAt
  have hmvt := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound hb ha
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  exact hmvt

/-- A uniform positive lower bound and upper bound on `lift (u t)` over `[0,1]`,
for a positive classical solution at an interior time (continuity on the compact
`[0,1]` + closed-domain positivity `u_pos'`). -/
theorem lift_u_bounded_pos
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    ∃ δ M : ℝ, 0 < δ ∧
      ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u t) x ∈ Set.Icc δ M := by
  classical
  have hreg : intervalDomainClassicalRegularity T u v := hsol.regularity
  have hC2u := (hreg.2.2.2.2.1 t ht).1.1
  have hcont : ContinuousOn (intervalDomainLift (u t)) (Set.Icc (0:ℝ) 1) :=
    hC2u.continuousOn
  have hne : (Set.Icc (0:ℝ) 1).Nonempty := ⟨0, by constructor <;> norm_num⟩
  -- positivity of `lift (u t)` on `[0,1]`.
  have hpos : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 < intervalDomainLift (u t) x := by
    intro x hx
    have : intervalDomainLift (u t) x = u t ⟨x, hx⟩ := by
      simp only [intervalDomainLift, hx, dif_pos]
    rw [this]; exact hsol.u_pos' ht.1 ht.2
  -- min and max on the compact `[0,1]`.
  obtain ⟨xmin, hxmin_mem, hxmin⟩ :=
    isCompact_Icc.exists_isMinOn hne hcont
  obtain ⟨xmax, hxmax_mem, hxmax⟩ :=
    isCompact_Icc.exists_isMaxOn hne hcont
  refine ⟨intervalDomainLift (u t) xmin, intervalDomainLift (u t) xmax,
    hpos xmin hxmin_mem, ?_⟩
  intro x hx
  exact ⟨isMinOn_iff.mp hxmin x hx, isMaxOn_iff.mp hxmax x hx⟩

/-! ### The source-difference coefficient energy bounded by `E_u`

The diagonal source-coefficient energy `coeffL2Energy(â(u₁) − â(u₂))` is bounded
by `4·∫₀¹ (ν u₁^γ − ν u₂^γ)²` (cosine-Bessel), which the local Lipschitz of
`x ↦ x^γ` bounds by `4·(ν L)²·∫₀¹(u₁−u₂)² = 4·(ν L)²·E_u`. -/

/-- The source-difference coefficient `ℓ²` energy is `≤ 4·∫₀¹ (ν u₁^γ − ν u₂^γ)²`.
The two source coefficient sequences are real (`ofReal`), so their difference's
norm-square is `(re of the difference)²`, which is the squared Neumann cosine
coefficient of the (real) source difference `g := ν·(lift u₁^γ − lift u₂^γ)`;
cosine-Bessel (`unitIntervalNeumannCosineCoeff_l2_bound`) bounds the sum by
`4·∫₀¹ g²`. -/
theorem sourceCoeff_diff_energy_le_integral
    {p : CM2Params} {T₁ T₂ : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂)
    {t : ℝ} (ht₁ : t ∈ Set.Ioo (0 : ℝ) T₁) (ht₂ : t ∈ Set.Ioo (0 : ℝ) T₂) :
    coeffL2Energy
        (fun k : ℕ => intervalNeumannResolverSourceCoeff p (u₁ t) k -
          intervalNeumannResolverSourceCoeff p (u₂ t) k)
      ≤ 4 * ∫ x in (0:ℝ)..1,
          (p.ν * intervalDomainLift (u₁ t) x ^ p.γ
            - p.ν * intervalDomainLift (u₂ t) x ^ p.γ) ^ 2 := by
  classical
  set g : ℝ → ℝ := fun x =>
    p.ν * intervalDomainLift (u₁ t) x ^ p.γ - p.ν * intervalDomainLift (u₂ t) x ^ p.γ
    with hg
  set f : ℝ → ℂ := fun x => ((g x : ℝ) : ℂ) with hf
  -- `g` is continuous on `[0,1]` (difference of continuous sources).
  have hg1 : ContinuousOn (fun x : ℝ => p.ν * intervalDomainLift (u₁ t) x ^ p.γ)
      (Set.Icc (0:ℝ) 1) := by
    have := source_continuousOn_Icc hsol₁ ht₁; exact this
  have hg2 : ContinuousOn (fun x : ℝ => p.ν * intervalDomainLift (u₂ t) x ^ p.γ)
      (Set.Icc (0:ℝ) 1) := by
    have := source_continuousOn_Icc hsol₂ ht₂; exact this
  have hgcont : ContinuousOn g (Set.Icc (0:ℝ) 1) := hg1.sub hg2
  have hfcontOn : ContinuousOn f (Set.uIcc (0:ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact Complex.continuous_ofReal.comp_continuousOn hgcont
  have hfint : IntervalIntegrable f volume 0 1 := hfcontOn.intervalIntegrable
  have hfsq : IntervalIntegrable (fun x : ℝ => ‖f x‖ ^ 2) volume 0 1 :=
    ((hfcontOn.norm).pow 2).intervalIntegrable
  have hL2 : MemLp (unitIntervalEvenReflection f) 2
      (volume.restrict (Set.Ioc (-1:ℝ) 1)) :=
    evenReflection_memLp_two_of_continuousOn hgcont
  -- cosine-Bessel: `∑ (cosineCoeff f)² ≤ 4·∫ ‖f‖²`.
  obtain ⟨hsum, hnorm_le⟩ := unitIntervalNeumannCosineCoeff_l2_bound hfint hL2 hfsq
  -- identify `(Δsource).re` with the cosine coefficient of `f` and `‖f‖² = g²`.
  have hre : ∀ k : ℕ,
      (intervalNeumannResolverSourceCoeff p (u₁ t) k -
        intervalNeumannResolverSourceCoeff p (u₂ t) k).re
        = unitIntervalNeumannCosineCoeff f k := by
    intro k
    have h1 : (intervalNeumannResolverSourceCoeff p (u₁ t) k).re
        = unitIntervalNeumannCosineCoeff
            (fun x => ((p.ν * intervalDomainLift (u₁ t) x ^ p.γ : ℝ) : ℂ)) k := by
      simp only [intervalNeumannResolverSourceCoeff, Complex.ofReal_re]
    have h2 : (intervalNeumannResolverSourceCoeff p (u₂ t) k).re
        = unitIntervalNeumannCosineCoeff
            (fun x => ((p.ν * intervalDomainLift (u₂ t) x ^ p.γ : ℝ) : ℂ)) k := by
      simp only [intervalNeumannResolverSourceCoeff, Complex.ofReal_re]
    rw [Complex.sub_re, h1, h2]
    -- linearity of the (real) Neumann cosine coefficient in the source.
    simp only [unitIntervalNeumannCosineCoeff,
      ShenWork.HeatKernelGradientEstimates.unitIntervalCosineRawCoeff, hf, hg]
    have hcos_cont : ∀ m : ℕ, ContinuousOn
        (fun x : ℝ => (Real.cos ((m:ℝ) * Real.pi * x) : ℂ)) (Set.uIcc (0:ℝ) 1) :=
      fun m => (Complex.continuous_ofReal.comp
        (Real.continuous_cos.comp (by fun_prop))).continuousOn
    have hII1 : ∀ m : ℕ, IntervalIntegrable
        (fun x : ℝ => (Real.cos ((m:ℝ) * Real.pi * x) : ℂ) *
          ((p.ν * intervalDomainLift (u₁ t) x ^ p.γ : ℝ) : ℂ)) volume 0 1 := by
      intro m
      refine ((hcos_cont m).mul ?_).intervalIntegrable
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact Complex.continuous_ofReal.comp_continuousOn hg1
    have hII2 : ∀ m : ℕ, IntervalIntegrable
        (fun x : ℝ => (Real.cos ((m:ℝ) * Real.pi * x) : ℂ) *
          ((p.ν * intervalDomainLift (u₂ t) x ^ p.γ : ℝ) : ℂ)) volume 0 1 := by
      intro m
      refine ((hcos_cont m).mul ?_).intervalIntegrable
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact Complex.continuous_ofReal.comp_continuousOn hg2
    have hlin : ∀ m : ℕ,
        ((∫ x in (0:ℝ)..1, (Real.cos ((m:ℝ) * Real.pi * x) : ℂ) *
            ((p.ν * intervalDomainLift (u₁ t) x ^ p.γ : ℝ) : ℂ)).re)
          - ((∫ x in (0:ℝ)..1, (Real.cos ((m:ℝ) * Real.pi * x) : ℂ) *
            ((p.ν * intervalDomainLift (u₂ t) x ^ p.γ : ℝ) : ℂ)).re)
          = (∫ x in (0:ℝ)..1, (Real.cos ((m:ℝ) * Real.pi * x) : ℂ) *
            ((p.ν * intervalDomainLift (u₁ t) x ^ p.γ
              - p.ν * intervalDomainLift (u₂ t) x ^ p.γ : ℝ) : ℂ)).re := by
      intro m
      rw [← Complex.sub_re, ← intervalIntegral.integral_sub (hII1 m) (hII2 m)]
      congr 1; apply intervalIntegral.integral_congr; intro x _; push_cast; ring
    rcases eq_or_ne k 0 with hk | hk
    · subst hk; simp only [if_pos rfl]; exact hlin 0
    · simp only [if_neg hk]; rw [← mul_sub, hlin k]
  -- now bound the energy.
  rw [coeffL2Energy]
  have hcongr : (fun k : ℕ => ‖intervalNeumannResolverSourceCoeff p (u₁ t) k -
        intervalNeumannResolverSourceCoeff p (u₂ t) k‖ ^ 2)
      = fun k : ℕ => (unitIntervalNeumannCosineCoeff f k) ^ 2 := by
    funext k
    have him : (intervalNeumannResolverSourceCoeff p (u₁ t) k -
        intervalNeumannResolverSourceCoeff p (u₂ t) k).im = 0 := by
      simp [intervalNeumannResolverSourceCoeff, Complex.sub_im]
    rw [Complex.sq_norm, Complex.normSq_apply, him, hre k]; ring
  rw [hcongr]
  -- `∑ (cosineCoeff f)² = TsumEnergy = (TsumNorm)² ≤ (2 sqrt I)² = 4 I`.
  have hI_nonneg : 0 ≤ ∫ x in (0:ℝ)..1, ‖f x‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun x _ => sq_nonneg _)
  have hEnergy_eq : (∑' k : ℕ, (unitIntervalNeumannCosineCoeff f k) ^ 2)
      = (unitIntervalCosineL2TsumNorm (unitIntervalNeumannCosineCoeff f)) ^ 2 := by
    rw [unitIntervalCosineL2TsumNorm, Real.sq_sqrt]
    · rfl
    · exact tsum_nonneg (fun k => sq_nonneg _)
  rw [hEnergy_eq]
  have hfg : (∫ x in (0:ℝ)..1, ‖f x‖ ^ 2)
      = ∫ x in (0:ℝ)..1, (p.ν * intervalDomainLift (u₁ t) x ^ p.γ
          - p.ν * intervalDomainLift (u₂ t) x ^ p.γ) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x _
    show ‖((g x : ℝ) : ℂ)‖ ^ 2 = (p.ν * intervalDomainLift (u₁ t) x ^ p.γ
          - p.ν * intervalDomainLift (u₂ t) x ^ p.γ) ^ 2
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, hg]
  rw [hfg] at hnorm_le
  -- `TsumNorm ≤ 2 sqrt I`, square both sides.
  have hnn : 0 ≤ unitIntervalCosineL2TsumNorm (unitIntervalNeumannCosineCoeff f) :=
    Real.sqrt_nonneg _
  calc (unitIntervalCosineL2TsumNorm (unitIntervalNeumannCosineCoeff f)) ^ 2
      ≤ (2 * Real.sqrt (∫ x in (0:ℝ)..1, (p.ν * intervalDomainLift (u₁ t) x ^ p.γ
          - p.ν * intervalDomainLift (u₂ t) x ^ p.γ) ^ 2)) ^ 2 := by
        exact pow_le_pow_left₀ hnn hnorm_le 2
    _ = 4 * ∫ x in (0:ℝ)..1, (p.ν * intervalDomainLift (u₁ t) x ^ p.γ
          - p.ν * intervalDomainLift (u₂ t) x ^ p.γ) ^ 2 := by
        have hInonneg : 0 ≤ ∫ x in (0:ℝ)..1, (p.ν * intervalDomainLift (u₁ t) x ^ p.γ
            - p.ν * intervalDomainLift (u₂ t) x ^ p.γ) ^ 2 :=
          intervalIntegral.integral_nonneg (by norm_num) (fun x _ => sq_nonneg _)
        rw [mul_pow, Real.sq_sqrt hInonneg]; ring

/-- The source-difference `L²` mass is bounded by `(ν L)²·E_u`, where `L` is the
local Lipschitz constant of `x ↦ x^γ` on the common bounded positive range of the
two solutions and `E_u = ∫₀¹ (u₁ − u₂)²`. -/
theorem source_integral_le_Eu
    {p : CM2Params} {T₁ T₂ : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂)
    {t : ℝ} (ht₁ : t ∈ Set.Ioo (0 : ℝ) T₁) (ht₂ : t ∈ Set.Ioo (0 : ℝ) T₂) :
    ∃ L : ℝ, 0 ≤ L ∧
      (∫ x in (0:ℝ)..1, (p.ν * intervalDomainLift (u₁ t) x ^ p.γ
        - p.ν * intervalDomainLift (u₂ t) x ^ p.γ) ^ 2)
        ≤ (p.ν * L) ^ 2 *
          intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ t := by
  classical
  -- common bounded positive range `[δ, M]`.
  obtain ⟨δ₁, M₁, hδ₁, hb₁⟩ := lift_u_bounded_pos hsol₁ ht₁
  obtain ⟨δ₂, M₂, hδ₂, hb₂⟩ := lift_u_bounded_pos hsol₂ ht₂
  set δ : ℝ := min δ₁ δ₂ with hδdef
  set M : ℝ := max M₁ M₂ with hMdef
  have hδpos : 0 < δ := lt_min hδ₁ hδ₂
  have hmem₁ : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u₁ t) x ∈ Set.Icc δ M := by
    intro x hx
    obtain ⟨hl, hr⟩ := hb₁ x hx
    exact ⟨le_trans (min_le_left _ _) hl, le_trans hr (le_max_left _ _)⟩
  have hmem₂ : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (u₂ t) x ∈ Set.Icc δ M := by
    intro x hx
    obtain ⟨hl, hr⟩ := hb₂ x hx
    exact ⟨le_trans (min_le_right _ _) hl, le_trans hr (le_max_right _ _)⟩
  have hMpos : 0 < M := by
    have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := by constructor <;> norm_num
    have hmem := hmem₁ 0 h0
    have hδM : δ ≤ M := le_trans hmem.1 hmem.2
    linarith
  set L : ℝ := p.γ * (δ ^ (p.γ - 1) + M ^ (p.γ - 1)) with hLdef
  have hLnonneg : 0 ≤ L := by
    rw [hLdef]
    have h1 : 0 ≤ δ ^ (p.γ - 1) := Real.rpow_nonneg hδpos.le _
    have h2 : 0 ≤ M ^ (p.γ - 1) := Real.rpow_nonneg hMpos.le _
    have := p.hγ.le
    positivity
  refine ⟨L, hLnonneg, ?_⟩
  -- pointwise bound on `[0,1]`: `(νu₁^γ − νu₂^γ)² ≤ (νL)²·(u₁−u₂)²`.
  have hptwise : ∀ x ∈ Set.Icc (0:ℝ) 1,
      (p.ν * intervalDomainLift (u₁ t) x ^ p.γ
        - p.ν * intervalDomainLift (u₂ t) x ^ p.γ) ^ 2
      ≤ (p.ν * L) ^ 2 *
        (intervalDomainLift (u₁ t) x - intervalDomainLift (u₂ t) x) ^ 2 := by
    intro x hxIcc
    have hlip := rpow_lipschitz_on_pos_Icc p.hγ hδpos (hmem₁ x hxIcc) (hmem₂ x hxIcc)
    -- `|u₁^γ − u₂^γ| ≤ L |u₁ − u₂|`; multiply by `ν ≥ 0`, square.
    -- `(u₁^γ − u₂^γ)² ≤ L²·(u₁−u₂)²` from `|·| ≤ L|·|`.
    have habs : |intervalDomainLift (u₁ t) x ^ p.γ - intervalDomainLift (u₂ t) x ^ p.γ|
        ≤ L * |intervalDomainLift (u₁ t) x - intervalDomainLift (u₂ t) x| := hlip
    have hsq := mul_self_le_mul_self (abs_nonneg _) habs
    have hsq2 : (intervalDomainLift (u₁ t) x ^ p.γ - intervalDomainLift (u₂ t) x ^ p.γ) ^ 2
        ≤ L ^ 2 * (intervalDomainLift (u₁ t) x - intervalDomainLift (u₂ t) x) ^ 2 := by
      rw [← sq_abs (intervalDomainLift (u₁ t) x ^ p.γ - intervalDomainLift (u₂ t) x ^ p.γ),
          ← sq_abs (intervalDomainLift (u₁ t) x - intervalDomainLift (u₂ t) x)]
      calc |intervalDomainLift (u₁ t) x ^ p.γ - intervalDomainLift (u₂ t) x ^ p.γ| ^ 2
          = |intervalDomainLift (u₁ t) x ^ p.γ - intervalDomainLift (u₂ t) x ^ p.γ| *
            |intervalDomainLift (u₁ t) x ^ p.γ - intervalDomainLift (u₂ t) x ^ p.γ| := by ring
        _ ≤ (L * |intervalDomainLift (u₁ t) x - intervalDomainLift (u₂ t) x|) *
            (L * |intervalDomainLift (u₁ t) x - intervalDomainLift (u₂ t) x|) := hsq
        _ = L ^ 2 * |intervalDomainLift (u₁ t) x - intervalDomainLift (u₂ t) x| ^ 2 := by ring
    -- combine with the `ν` factor.
    have hνsq : (0:ℝ) ≤ p.ν ^ 2 := by positivity
    calc (p.ν * intervalDomainLift (u₁ t) x ^ p.γ
            - p.ν * intervalDomainLift (u₂ t) x ^ p.γ) ^ 2
        = p.ν ^ 2 *
            (intervalDomainLift (u₁ t) x ^ p.γ - intervalDomainLift (u₂ t) x ^ p.γ) ^ 2 := by
          ring
      _ ≤ p.ν ^ 2 *
            (L ^ 2 * (intervalDomainLift (u₁ t) x - intervalDomainLift (u₂ t) x) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq2 hνsq
      _ = (p.ν * L) ^ 2 *
            (intervalDomainLift (u₁ t) x - intervalDomainLift (u₂ t) x) ^ 2 := by ring
  -- integrate the pointwise bound; `E_u = ∫₀¹ lift((u₁−u₂)²) = ∫₀¹ (lift u₁ − lift u₂)²`.
  have hEu : intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ t
      = ∫ x in (0:ℝ)..1,
        (intervalDomainLift (u₁ t) x - intervalDomainLift (u₂ t) x) ^ 2 := by
    unfold intervalDomainClassicalL2DifferenceEnergyU
    show intervalDomainIntegral (fun x => (u₁ t x - u₂ t x) ^ 2)
      = ∫ x in (0:ℝ)..1, (intervalDomainLift (u₁ t) x - intervalDomainLift (u₂ t) x) ^ 2
    unfold intervalDomainIntegral
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
    simp only [intervalDomainLift, hx, dif_pos]
  rw [hEu, ← intervalIntegral.integral_const_mul]
  -- monotonicity of the integral under the a.e. pointwise bound.
  refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ ?_
  · -- integrability of LHS (continuous on uIcc).
    have hc1 := source_continuousOn_Icc hsol₁ ht₁
    have hc2 := source_continuousOn_Icc hsol₂ ht₂
    have : ContinuousOn (fun x => (p.ν * intervalDomainLift (u₁ t) x ^ p.γ
        - p.ν * intervalDomainLift (u₂ t) x ^ p.γ) ^ 2) (Set.uIcc (0:ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact ((hc1.sub hc2).pow 2)
    exact this.intervalIntegrable
  · -- integrability of RHS.
    have hreg1 := hsol₁.regularity
    have hreg2 := hsol₂.regularity
    have hcu1 : ContinuousOn (intervalDomainLift (u₁ t)) (Set.Icc (0:ℝ) 1) :=
      ((hreg1.2.2.2.2.2.2.1 t ht₁).1.1).continuousOn
    have hcu2 : ContinuousOn (intervalDomainLift (u₂ t)) (Set.Icc (0:ℝ) 1) :=
      ((hreg2.2.2.2.2.2.2.1 t ht₂).1.1).continuousOn
    have : ContinuousOn (fun x => (p.ν * L) ^ 2 *
        (intervalDomainLift (u₁ t) x - intervalDomainLift (u₂ t) x) ^ 2)
        (Set.uIcc (0:ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact continuousOn_const.mul ((hcu1.sub hcu2).pow 2)
    exact this.intervalIntegrable
  · exact hptwise

/-! ### The static L² control theorems (value and gradient) -/

/-- **Static L² control of the `v`-difference value by `E_u`.**

For two positive classical solutions sharing parameters and an interior time
`τ ∈ (0,T₁) ∩ (0,T₂)`,

  `∫₀¹ (lift(v₁ τ) − lift(v₂ τ))² dx
     ≤ C · intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ`,

with `C = (∑ₖ weightₖ²) · 4 · (ν L)²` (the resolver value-weight ℓ²-mass, the
cosine-Bessel factor `4`, and the `x↦x^γ` Lipschitz constant `L`).  Route: step (1)
`v_i = R(u_i)` pointwise on `(0,1)`; the sup resolver-Lipschitz bound
`intervalNeumannResolverR_sup_lipschitz`; sup→L² on the unit interval; and
`sourceCoeff_diff_energy_le_integral` + `source_integral_le_Eu`. -/
theorem static_v_value_L2_le_Eu
    {p : CM2Params} {T₁ T₂ : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂)
    {τ : ℝ} (hτ₁ : τ ∈ Set.Ioo (0 : ℝ) T₁) (hτ₂ : τ ∈ Set.Ioo (0 : ℝ) T₂) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∫ x in (0:ℝ)..1,
        (intervalDomainLift (v₁ τ) x - intervalDomainLift (v₂ τ) x) ^ 2)
        ≤ C * intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ := by
  classical
  set Csup2 : ℝ := (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2)) ^ 2
    with hCsup2
  set A : ℕ → ℂ := fun k => intervalNeumannResolverSourceCoeff p (u₁ τ) k -
    intervalNeumannResolverSourceCoeff p (u₂ τ) k with hA
  have hCsup2_nn : 0 ≤ Csup2 := by rw [hCsup2]; positivity
  have hCe_nn : 0 ≤ coeffL2Energy A := by
    unfold coeffL2Energy; exact tsum_nonneg (fun k => by positivity)
  have hsrc := source_resolverCoeff_re_sq_summable hsol₁ hsol₂ hτ₁ hτ₂
  -- const bound `B := Csup² · coeffL2Energy A`.
  set B : ℝ := Csup2 * coeffL2Energy A with hB
  -- interior pointwise: `(lift v₁ − lift v₂)² ≤ B` for `x ∈ (0,1)`.
  have hpt : ∀ x ∈ Set.Ioo (0:ℝ) 1,
      (intervalDomainLift (v₁ τ) x - intervalDomainLift (v₂ τ) x) ^ 2 ≤ B := by
    intro x hxIoo
    have h1 := solution_v_eq_resolver_pointwise_unconditional hsol₁ hτ₁ hxIoo
    have h2 := solution_v_eq_resolver_pointwise_unconditional hsol₂ hτ₂ hxIoo
    have hsum₁ := solution_resolver_cosineSeries_summable hsol₁ hτ₁ x
    have hsum₂ := solution_resolver_cosineSeries_summable hsol₂ hτ₂ x
    have hbound := intervalNeumannResolverR_sup_lipschitz p (u₁ τ) (u₂ τ) hsrc
      ⟨x, Set.Ioo_subset_Icc_self hxIoo⟩ hsum₁ hsum₂
    rw [← h1, ← h2]
    have hge : |intervalNeumannResolverR p (u₁ τ) ⟨x, Set.Ioo_subset_Icc_self hxIoo⟩ -
        intervalNeumannResolverR p (u₂ τ) ⟨x, Set.Ioo_subset_Icc_self hxIoo⟩|
        ≤ Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2) *
          coeffL2Norm A := hbound
    have hsq := mul_self_le_mul_self (abs_nonneg _) hge
    rw [← sq_abs]
    calc |intervalNeumannResolverR p (u₁ τ) ⟨x, Set.Ioo_subset_Icc_self hxIoo⟩ -
            intervalNeumannResolverR p (u₂ τ) ⟨x, Set.Ioo_subset_Icc_self hxIoo⟩| ^ 2
        = |intervalNeumannResolverR p (u₁ τ) ⟨x, Set.Ioo_subset_Icc_self hxIoo⟩ -
            intervalNeumannResolverR p (u₂ τ) ⟨x, Set.Ioo_subset_Icc_self hxIoo⟩| *
          |intervalNeumannResolverR p (u₁ τ) ⟨x, Set.Ioo_subset_Icc_self hxIoo⟩ -
            intervalNeumannResolverR p (u₂ τ) ⟨x, Set.Ioo_subset_Icc_self hxIoo⟩| := by ring
      _ ≤ (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2) * coeffL2Norm A) *
          (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2) * coeffL2Norm A) := hsq
      _ = B := by
          have hWnn : 0 ≤ ∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2 :=
            tsum_nonneg (fun k => sq_nonneg _)
          rw [hB, hCsup2]
          unfold coeffL2Norm
          rw [Real.sq_sqrt hWnn,
            show (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2) *
                Real.sqrt (coeffL2Energy A)) *
              (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2) *
                Real.sqrt (coeffL2Energy A))
              = (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2) *
                  Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2)) *
                (Real.sqrt (coeffL2Energy A) * Real.sqrt (coeffL2Energy A)) by ring,
            Real.mul_self_sqrt hWnn, Real.mul_self_sqrt hCe_nn]
  -- pass to the integral: integrand `≤ B` a.e. on `[0,1]` (interior is co-null).
  have hintLHS : IntervalIntegrable
      (fun x => (intervalDomainLift (v₁ τ) x - intervalDomainLift (v₂ τ) x) ^ 2) volume 0 1 := by
    have hc1 : ContinuousOn (intervalDomainLift (v₁ τ)) (Set.Icc (0:ℝ) 1) :=
      ((hsol₁.regularity.2.2.2.2.1 τ hτ₁).2.1).continuousOn
    have hc2 : ContinuousOn (intervalDomainLift (v₂ τ)) (Set.Icc (0:ℝ) 1) :=
      ((hsol₂.regularity.2.2.2.2.1 τ hτ₂).2.1).continuousOn
    have : ContinuousOn (fun x => (intervalDomainLift (v₁ τ) x -
        intervalDomainLift (v₂ τ) x) ^ 2) (Set.uIcc (0:ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact (hc1.sub hc2).pow 2
    exact this.intervalIntegrable
  have hle_int : (∫ x in (0:ℝ)..1,
        (intervalDomainLift (v₁ τ) x - intervalDomainLift (v₂ τ) x) ^ 2) ≤ B := by
    have hmono : (∫ x in (0:ℝ)..1,
        (intervalDomainLift (v₁ τ) x - intervalDomainLift (v₂ τ) x) ^ 2)
        ≤ ∫ _ in (0:ℝ)..1, B := by
      refine intervalIntegral.integral_mono_ae_restrict (by norm_num) hintLHS
        (continuous_const.intervalIntegrable 0 1) ?_
      -- the bound holds on `Ioo 0 1`, which is `Icc 0 1` minus the null endpoints.
      refine (ae_restrict_iff' (measurableSet_Icc (a := (0:ℝ)) (b := 1))).2 ?_
      have hnull : volume (insert (0:ℝ) ({(1:ℝ)} : Set ℝ)) = 0 :=
        Set.Finite.measure_zero
          ((Set.finite_singleton (1:ℝ)).insert (0:ℝ)) volume
      refine (MeasureTheory.ae_iff).2 (measure_mono_null ?_ hnull)
      intro x hx
      simp only [Set.mem_setOf_eq] at hx
      push_neg at hx
      obtain ⟨hxIcc, hne⟩ := hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      by_contra hcon
      push_neg at hcon
      obtain ⟨hx0, hx1⟩ := hcon
      exact absurd (hpt x ⟨lt_of_le_of_ne hxIcc.1 (Ne.symm hx0),
        lt_of_le_of_ne hxIcc.2 hx1⟩) (not_le.mpr hne)
    rwa [intervalIntegral.integral_const, smul_eq_mul, sub_zero, one_mul] at hmono
  -- chain: `B ≤ Csup²·4·∫source² ≤ Csup²·4·(νL)²·E_u`.
  have hEnergy_le := sourceCoeff_diff_energy_le_integral hsol₁ hsol₂ hτ₁ hτ₂
  obtain ⟨L, hLnn, hsrcint⟩ := source_integral_le_Eu hsol₁ hsol₂ hτ₁ hτ₂
  refine ⟨Csup2 * 4 * (p.ν * L) ^ 2, by positivity, ?_⟩
  refine hle_int.trans ?_
  -- `B = Csup²·coeffL2Energy A ≤ Csup²·(4·∫src²) ≤ Csup²·4·(νL)²·E_u`.
  have hstep1 : B ≤ Csup2 * (4 * ∫ x in (0:ℝ)..1,
      (p.ν * intervalDomainLift (u₁ τ) x ^ p.γ
        - p.ν * intervalDomainLift (u₂ τ) x ^ p.γ) ^ 2) := by
    rw [hB]; exact mul_le_mul_of_nonneg_left hEnergy_le hCsup2_nn
  have hEu_nn : 0 ≤ intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ :=
    intervalDomainClassicalL2DifferenceEnergyU_nonneg u₁ u₂ τ
  calc B ≤ Csup2 * (4 * ∫ x in (0:ℝ)..1,
        (p.ν * intervalDomainLift (u₁ τ) x ^ p.γ
          - p.ν * intervalDomainLift (u₂ τ) x ^ p.γ) ^ 2) := hstep1
    _ ≤ Csup2 * (4 * ((p.ν * L) ^ 2 *
          intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ)) := by
        apply mul_le_mul_of_nonneg_left _ hCsup2_nn
        apply mul_le_mul_of_nonneg_left hsrcint (by norm_num)
    _ = Csup2 * 4 * (p.ν * L) ^ 2 *
          intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ := by ring

/-- The resolver spatial-gradient series as a plain real function of `x : ℝ`
(`intervalNeumannResolverRGrad` only reads `x.1`, so this is the same value at
interval points). -/
def resolverGradReal (p : CM2Params) (u : intervalDomainPoint → ℝ) (x : ℝ) : ℝ :=
  ∑' k : ℕ,
    (intervalNeumannResolverCoeff p u k).re *
      (-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * x))

lemma resolverGradReal_eq (p : CM2Params) (u : intervalDomainPoint → ℝ)
    (x : intervalDomainPoint) :
    resolverGradReal p u x.1 = intervalNeumannResolverRGrad p u x := rfl

/-- **Static L² control of the `v`-gradient difference by `E_u`.**

The repo models the spatial gradient of the elliptic resolver as the termwise
differentiated cosine series (`intervalNeumannResolverRGrad`, here written as the
plain real function `resolverGradReal`); by step (1) this is the gradient of
`v_i(·,τ)`.  For two positive classical solutions and `τ ∈ (0,T₁) ∩ (0,T₂)`,

  `∫₀¹ (resolverGradReal p (u₁ τ) x − resolverGradReal p (u₂ τ) x)² dx
     ≤ C · intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ`,

with `C = (∑ₖ gradWeightₖ²) · 4 · (ν L)²`.  Same route as the value bound, using
the gradient sup-Lipschitz `intervalNeumannResolverR_grad_sup_lipschitz` and
`solution_resolver_sineSeries_summable`. -/
theorem static_v_grad_L2_le_Eu
    {p : CM2Params} {T₁ T₂ : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂)
    {τ : ℝ} (hτ₁ : τ ∈ Set.Ioo (0 : ℝ) T₁) (hτ₂ : τ ∈ Set.Ioo (0 : ℝ) T₂) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∫ x in (0:ℝ)..1,
        (resolverGradReal p (u₁ τ) x - resolverGradReal p (u₂ τ) x) ^ 2)
        ≤ C * intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ := by
  classical
  set Cg2 : ℝ := (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2)) ^ 2
    with hCg2
  set A : ℕ → ℂ := fun k => intervalNeumannResolverSourceCoeff p (u₁ τ) k -
    intervalNeumannResolverSourceCoeff p (u₂ τ) k with hA
  have hCg2_nn : 0 ≤ Cg2 := by rw [hCg2]; positivity
  have hCe_nn : 0 ≤ coeffL2Energy A := by
    unfold coeffL2Energy; exact tsum_nonneg (fun k => by positivity)
  have hsrc := source_resolverCoeff_re_sq_summable hsol₁ hsol₂ hτ₁ hτ₂
  set B : ℝ := Cg2 * coeffL2Energy A with hB
  -- pointwise bound on `[0,1]` (`resolverGradReal x = RGrad ⟨x,hx⟩` there).
  have hpt : ∀ x ∈ Set.Icc (0:ℝ) 1,
      (resolverGradReal p (u₁ τ) x - resolverGradReal p (u₂ τ) x) ^ 2 ≤ B := by
    intro x hx
    have hsum₁ := solution_resolver_sineSeries_summable hsol₁ hτ₁ x
    have hsum₂ := solution_resolver_sineSeries_summable hsol₂ hτ₂ x
    have hbound := intervalNeumannResolverR_grad_sup_lipschitz p (u₁ τ) (u₂ τ) hsrc
      ⟨x, hx⟩ hsum₁ hsum₂
    rw [resolverGradReal_eq p (u₁ τ) ⟨x, hx⟩, resolverGradReal_eq p (u₂ τ) ⟨x, hx⟩]
    have hge : |intervalNeumannResolverRGrad p (u₁ τ) ⟨x, hx⟩ -
        intervalNeumannResolverRGrad p (u₂ τ) ⟨x, hx⟩|
        ≤ Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
          coeffL2Norm A := hbound
    have hsq := mul_self_le_mul_self (abs_nonneg _) hge
    rw [← sq_abs]
    calc |intervalNeumannResolverRGrad p (u₁ τ) ⟨x, hx⟩ -
            intervalNeumannResolverRGrad p (u₂ τ) ⟨x, hx⟩| ^ 2
        = |intervalNeumannResolverRGrad p (u₁ τ) ⟨x, hx⟩ -
            intervalNeumannResolverRGrad p (u₂ τ) ⟨x, hx⟩| *
          |intervalNeumannResolverRGrad p (u₁ τ) ⟨x, hx⟩ -
            intervalNeumannResolverRGrad p (u₂ τ) ⟨x, hx⟩| := by ring
      _ ≤ (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) * coeffL2Norm A) *
          (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) * coeffL2Norm A) := hsq
      _ = B := by
          have hWnn : 0 ≤ ∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2 :=
            tsum_nonneg (fun k => sq_nonneg _)
          rw [hB, hCg2]
          unfold coeffL2Norm
          rw [Real.sq_sqrt hWnn,
            show (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
                Real.sqrt (coeffL2Energy A)) *
              (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
                Real.sqrt (coeffL2Energy A))
              = (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
                  Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2)) *
                (Real.sqrt (coeffL2Energy A) * Real.sqrt (coeffL2Energy A)) by ring,
            Real.mul_self_sqrt hWnn, Real.mul_self_sqrt hCe_nn]
  -- `resolverGradReal p u` is continuous (uniform limit of continuous terms under
  -- the summable gradient majorant `∑ |coeff_k.re|·kπ`, from the source decay).
  have hcontGrad : ∀ {Tj : ℝ} {uj vj : ℝ → intervalDomainPoint → ℝ},
      IsPaper2ClassicalSolution intervalDomain p Tj uj vj →
      τ ∈ Set.Ioo (0:ℝ) Tj →
      Continuous (fun x : ℝ => resolverGradReal p (uj τ) x) := by
    intro Tj uj vj hsolj hτj
    have hdecay := sourceCoeffQuadraticDecay_of_solution hsolj hτj
    have hmaj := resolverGrad_majorant_summable_of_sourceDecay hdecay.C_nonneg hdecay.decay
    refine continuous_tsum (fun k => ?_) hmaj (fun k x => ?_)
    · exact continuous_const.mul (continuous_const.mul
        (Real.continuous_sin.comp (by fun_prop)))
    · rw [Real.norm_eq_abs, abs_mul]
      have hsin : |(-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * x))|
          ≤ (k : ℝ) * Real.pi := by
        rw [abs_mul, abs_neg, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (k:ℝ)),
          abs_of_nonneg Real.pi_pos.le]
        have h1 : |Real.sin ((k : ℝ) * Real.pi * x)| ≤ 1 := Real.abs_sin_le_one _
        nlinarith [mul_nonneg (Nat.cast_nonneg k) Real.pi_pos.le, abs_nonneg
          (Real.sin ((k : ℝ) * Real.pi * x)), h1]
      have hfin : |(intervalNeumannResolverCoeff p (uj τ) k).re| *
            |(-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * x))|
          ≤ |(intervalNeumannResolverCoeff p (uj τ) k).re| * ((k : ℝ) * Real.pi) :=
        mul_le_mul_of_nonneg_left hsin (abs_nonneg _)
      exact hfin
  have hc1 := hcontGrad hsol₁ hτ₁
  have hc2 := hcontGrad hsol₂ hτ₂
  have hintLHS : IntervalIntegrable
      (fun x => (resolverGradReal p (u₁ τ) x - resolverGradReal p (u₂ τ) x) ^ 2) volume 0 1 :=
    ((hc1.sub hc2).pow 2).intervalIntegrable _ _
  have hle_int : (∫ x in (0:ℝ)..1,
        (resolverGradReal p (u₁ τ) x - resolverGradReal p (u₂ τ) x) ^ 2) ≤ B := by
    have hmono : (∫ x in (0:ℝ)..1,
        (resolverGradReal p (u₁ τ) x - resolverGradReal p (u₂ τ) x) ^ 2)
        ≤ ∫ _ in (0:ℝ)..1, B :=
      intervalIntegral.integral_mono_on (by norm_num) hintLHS
        (continuous_const.intervalIntegrable 0 1) hpt
    rwa [intervalIntegral.integral_const, smul_eq_mul, sub_zero, one_mul] at hmono
  -- chain to `E_u`.
  have hEnergy_le := sourceCoeff_diff_energy_le_integral hsol₁ hsol₂ hτ₁ hτ₂
  obtain ⟨L, hLnn, hsrcint⟩ := source_integral_le_Eu hsol₁ hsol₂ hτ₁ hτ₂
  refine ⟨Cg2 * 4 * (p.ν * L) ^ 2, (by positivity), ?_⟩
  refine hle_int.trans ?_
  have hstep1 : B ≤ Cg2 * (4 * ∫ x in (0:ℝ)..1,
      (p.ν * intervalDomainLift (u₁ τ) x ^ p.γ
        - p.ν * intervalDomainLift (u₂ τ) x ^ p.γ) ^ 2) := by
    rw [hB]; exact mul_le_mul_of_nonneg_left hEnergy_le hCg2_nn
  calc B ≤ Cg2 * (4 * ∫ x in (0:ℝ)..1,
        (p.ν * intervalDomainLift (u₁ τ) x ^ p.γ
          - p.ν * intervalDomainLift (u₂ τ) x ^ p.γ) ^ 2) := hstep1
    _ ≤ Cg2 * (4 * ((p.ν * L) ^ 2 *
          intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ)) := by
        apply mul_le_mul_of_nonneg_left _ hCg2_nn
        apply mul_le_mul_of_nonneg_left hsrcint (by norm_num)
    _ = Cg2 * 4 * (p.ν * L) ^ 2 *
          intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ := by ring

/-- **Uniform positive lower bound for `lift (u τ)` on a closed time sub-interval
`[s,t] ⊂ (0,T)` jointly in time and space.**

For a positive classical solution and any `0 < s ≤ t < T`, there exists `δ > 0`
such that `δ ≤ intervalDomainLift (u τ) x` simultaneously for every `τ ∈ [s,t]`
and every `x ∈ [0,1]`.

Proof: conjunct (9) of the classical regularity bundle gives joint continuity of
`(τ,x) ↦ intervalDomainLift (u τ) x` on `Ioo 0 T ×ˢ Icc 0 1`; the compact closed
slab `Icc s t ×ˢ Icc 0 1` sits inside that open-by-closed slab, so the function
attains its minimum on the compact at some `(τ₀,x₀)`; closed-domain positivity
`u_pos'` (via `solution_lift_pos`) makes that minimum strictly positive. -/
theorem lift_u_uniformPositive_on_compact
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (htT : t < T) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ τ ∈ Set.Icc s t, ∀ x ∈ Set.Icc (0 : ℝ) 1,
        δ ≤ intervalDomainLift (u τ) x := by
  classical
  -- (9) joint continuity of `(τ,x) ↦ lift (u τ) x` on `Ioo 0 T ×ˢ Icc 0 1`.
  have hfield : ContinuousOn
      (Function.uncurry (fun (τ : ℝ) (x : ℝ) => intervalDomainLift (u τ) x))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.2.2).1
  -- compact slab `Icc s t ×ˢ Icc 0 1`.
  have hKcompact : IsCompact (Set.Icc s t ×ˢ Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  have hKne : (Set.Icc s t ×ˢ Set.Icc (0 : ℝ) 1).Nonempty :=
    ⟨(s, 0), ⟨Set.left_mem_Icc.mpr hst, by constructor <;> norm_num⟩⟩
  -- inclusion `Icc s t ×ˢ Icc 0 1 ⊆ Ioo 0 T ×ˢ Icc 0 1`.
  have hsub : Set.Icc s t ×ˢ Set.Icc (0 : ℝ) 1 ⊆
      Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1 := by
    rintro ⟨τ, x⟩ ⟨hτ, hx⟩
    refine ⟨⟨lt_of_lt_of_le hs hτ.1, lt_of_le_of_lt hτ.2 htT⟩, hx⟩
  -- restrict continuity to the compact slab.
  have hcontK : ContinuousOn
      (Function.uncurry (fun (τ : ℝ) (x : ℝ) => intervalDomainLift (u τ) x))
      (Set.Icc s t ×ˢ Set.Icc (0 : ℝ) 1) := hfield.mono hsub
  -- minimum of the (uncurried) continuous function on the nonempty compact.
  obtain ⟨q₀, hq₀_mem, hq₀_min⟩ :=
    hKcompact.exists_isMinOn hKne hcontK
  -- the minimum value is positive: `q₀ = (τ₀, x₀)` with `τ₀ ∈ Ioo 0 T`,
  -- `x₀ ∈ Icc 0 1`, so `solution_lift_pos` applies.
  obtain ⟨τ₀, x₀⟩ := q₀
  obtain ⟨hτ₀_mem, hx₀_mem⟩ := hq₀_mem
  have hτ₀_open : τ₀ ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_of_lt_of_le hs hτ₀_mem.1, lt_of_le_of_lt hτ₀_mem.2 htT⟩
  have hmin_pos : 0 < intervalDomainLift (u τ₀) x₀ :=
    solution_lift_pos hsol hτ₀_open x₀ hx₀_mem
  refine ⟨intervalDomainLift (u τ₀) x₀, hmin_pos, ?_⟩
  intro τ hτ x hx
  have hmem : (τ, x) ∈ Set.Icc s t ×ˢ Set.Icc (0 : ℝ) 1 := ⟨hτ, hx⟩
  exact isMinOn_iff.mp hq₀_min (τ, x) hmem

/-- **Uniform upper bound for `|lift (v τ)|` on a closed time sub-interval
`[s,t] ⊂ (0,T)` jointly in time and space.**

For a classical solution and any `0 < s ≤ t < T`, there exists `M ≥ 0` such
that `|intervalDomainLift (v τ) x| ≤ M` simultaneously for every `τ ∈ [s,t]`
and every `x ∈ [0,1]`.

Proof: conjunct (9) of the classical regularity bundle provides joint continuity
of `(τ,x) ↦ intervalDomainLift (v τ) x` on `Ioo 0 T ×ˢ Icc 0 1`.  Compose with
`|·|` (continuous) and restrict to the compact slab `Icc s t ×ˢ Icc 0 1`; a
continuous function on a nonempty compact attains its maximum, and that maximum
is `≥ 0` since it bounds an absolute value at one of the slab's points. -/
theorem lift_v_bounded_on_compact
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (htT : t < T) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ τ ∈ Set.Icc s t, ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |intervalDomainLift (v τ) x| ≤ M := by
  classical
  -- (9) joint continuity of `(τ,x) ↦ lift (v τ) x` on `Ioo 0 T ×ˢ Icc 0 1`
  -- (the v-side conjunct of (9), paired alongside the u-side conjunct).
  have hfield : ContinuousOn
      (Function.uncurry (fun (τ : ℝ) (x : ℝ) => intervalDomainLift (v τ) x))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.2.2).2
  -- compact slab `Icc s t ×ˢ Icc 0 1`.
  have hKcompact : IsCompact (Set.Icc s t ×ˢ Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  have hKne : (Set.Icc s t ×ˢ Set.Icc (0 : ℝ) 1).Nonempty :=
    ⟨(s, 0), ⟨Set.left_mem_Icc.mpr hst, by constructor <;> norm_num⟩⟩
  -- inclusion `Icc s t ×ˢ Icc 0 1 ⊆ Ioo 0 T ×ˢ Icc 0 1`.
  have hsub : Set.Icc s t ×ˢ Set.Icc (0 : ℝ) 1 ⊆
      Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1 := by
    rintro ⟨τ, x⟩ ⟨hτ, hx⟩
    refine ⟨⟨lt_of_lt_of_le hs hτ.1, lt_of_le_of_lt hτ.2 htT⟩, hx⟩
  -- restrict joint continuity to the compact slab.
  have hcontK : ContinuousOn
      (Function.uncurry (fun (τ : ℝ) (x : ℝ) => intervalDomainLift (v τ) x))
      (Set.Icc s t ×ˢ Set.Icc (0 : ℝ) 1) := hfield.mono hsub
  -- compose with `|·|`: still continuous on the compact slab.
  have hcontAbs : ContinuousOn
      (fun q : ℝ × ℝ => |intervalDomainLift (v q.1) q.2|)
      (Set.Icc s t ×ˢ Set.Icc (0 : ℝ) 1) := hcontK.abs
  -- maximum of the (uncurried) continuous function on the nonempty compact.
  obtain ⟨q₀, hq₀_mem, hq₀_max⟩ :=
    hKcompact.exists_isMaxOn hKne hcontAbs
  obtain ⟨τ₀, x₀⟩ := q₀
  refine ⟨|intervalDomainLift (v τ₀) x₀|, abs_nonneg _, ?_⟩
  intro τ hτ x hx
  have hmem : (τ, x) ∈ Set.Icc s t ×ˢ Set.Icc (0 : ℝ) 1 := ⟨hτ, hx⟩
  exact isMaxOn_iff.mp hq₀_max (τ, x) hmem

/-- **Strengthened positive initial datum predicate: uniform positive lower bound.**

A faithful PDE-textbook strengthening of `PositiveInitialDatum`: the datum `u₀`
admits a *uniform* positive lower bound `δ₀ > 0` that is independent of the
spatial point.  Stated as a standalone predicate (not folded into
`PositiveInitialDatum` / `initialAdmissible`) so that downstream gluing
theorems that need a *uniform* short-time positivity gap can opt in
selectively without blast-radius to the rest of the existence theory. -/
def IntervalDomainPosDatumLowerBound (u₀ : intervalDomainPoint → ℝ) : Prop :=
  ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ x : intervalDomainPoint, δ₀ ≤ u₀ x

/-- **Uniform positive lower bound for `lift (u τ)` on the half-horizon `(0,t]`
jointly in time and space**, from a bounded-below initial datum + initial trace.

Given a classical solution `(u,v)` sharing its initial trace with an initial
datum `u₀` that admits a uniform positive lower bound `δ₀ > 0` (and is
admissible, i.e. `BddAbove (range |u₀|)` — needed to make the trace sup-norm
bound pointwise via `le_csSup`), for every `t ∈ (0,T)` there is `δ > 0` such
that `δ ≤ intervalDomainLift (u τ) x` for every `τ ∈ (0,t]` and every
`x ∈ [0,1]`.

Proof: split `(0,t]` at a short-time cut `τ_a ∈ (0,t]`.  On `(0, τ_a]` the
initial trace gives `supNorm(u τ - u₀) < δ₀/2`, hence pointwise on `Icc 0 1`
`lift(u τ) y ≥ u₀ ⟨y,hy⟩ - δ₀/2 ≥ δ₀/2`.  On `[τ_a, t]` the existing compact-
slab uniform lower bound `lift_u_uniformPositive_on_compact` gives a uniform
`δ_a > 0`.  Take `δ := min (δ₀/2) δ_a`. -/
theorem lift_u_uniformPositive_on_halfHorizon
    {p : CM2Params} {T : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hTrace : InitialTrace intervalDomain u₀ u)
    (hPos : IntervalDomainPosDatumLowerBound u₀)
    (hAdm : intervalDomain.initialAdmissible u₀)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ t →
        ∀ x ∈ Set.Icc (0 : ℝ) 1, δ ≤ intervalDomainLift (u τ) x := by
  classical
  -- 1. extract the datum lower bound.
  obtain ⟨δ₀, hδ₀_pos, hδ₀_le⟩ := hPos
  have hδ₀_half_pos : 0 < δ₀ / 2 := by linarith
  -- 2. trace: pick `τ_raw > 0` such that for `τ ∈ (0, τ_raw)`,
  --    `supNorm(u τ - u₀) < δ₀/2`.  Then trim to land inside `(0, t]`.
  obtain ⟨τ_raw, hτ_raw_pos, hτ_raw_bound⟩ :=
    hTrace.eventually_small (ε := δ₀ / 2) hδ₀_half_pos
  -- pick `τ_a := min (τ_raw / 2) t`, a positive point with `τ_a < τ_raw` and `τ_a ≤ t`.
  set τ_a : ℝ := min (τ_raw / 2) t with hτ_a_def
  have hτ_raw_half_pos : 0 < τ_raw / 2 := by linarith
  have hτ_a_pos : 0 < τ_a := lt_min hτ_raw_half_pos ht0
  have hτ_a_le_t : τ_a ≤ t := min_le_right _ _
  have hτ_a_lt_raw : τ_a < τ_raw := by
    have h1 : τ_a ≤ τ_raw / 2 := min_le_left _ _
    linarith
  -- 3. compact-slab uniform bound on `[τ_a, t]`.
  obtain ⟨δ_a, hδ_a_pos, hδ_a_bound⟩ :=
    lift_u_uniformPositive_on_compact hsol (s := τ_a) (t := t) hτ_a_pos hτ_a_le_t htT
  -- 4. set `δ := min (δ₀/2) δ_a`.
  set δ : ℝ := min (δ₀ / 2) δ_a with hδ_def
  have hδ_pos : 0 < δ := lt_min hδ₀_half_pos hδ_a_pos
  refine ⟨δ, hδ_pos, ?_⟩
  intro τ hτ_pos hτ_le_t x hx
  -- case split: `τ ≤ τ_a` (short-time, use trace) vs `τ_a ≤ τ` (slab, use compact lemma).
  by_cases hcase : τ ≤ τ_a
  · -- short-time leg `(0, τ_a]`: use the trace bound.
    have hτ_lt_raw : τ < τ_raw := lt_of_le_of_lt hcase hτ_a_lt_raw
    have hsup_lt : intervalDomainSupNorm (fun y => u τ y - u₀ y) < δ₀ / 2 :=
      hτ_raw_bound τ hτ_pos hτ_lt_raw
    -- pointwise: `|u τ ⟨y,hy⟩ - u₀ ⟨y,hy⟩| ≤ supNorm`, via BddAbove of the range.
    -- BddAbove comes from continuity of `lift (u τ)` on `[0,1]` and admissibility of `u₀`.
    have hτ_open : τ ∈ Set.Ioo (0 : ℝ) T :=
      ⟨hτ_pos, lt_of_le_of_lt (le_trans hcase hτ_a_le_t) htT⟩
    have hu_cont : ContinuousOn (intervalDomainLift (u τ)) (Set.Icc (0 : ℝ) 1) :=
      ((hsol.regularity.2.2.2.2.1 τ hτ_open).1.1).continuousOn
    have hu_bddR : BddAbove (Set.range (fun z : intervalDomainPoint => |u τ z|)) := by
      have hcompact : IsCompact (Set.Icc (0:ℝ) 1) := isCompact_Icc
      obtain ⟨M, hM⟩ := (hcompact.image_of_continuousOn (hu_cont.abs)).bddAbove
      refine ⟨M, ?_⟩
      rintro _ ⟨z, rfl⟩
      have hMz := hM ⟨z.1, z.2, rfl⟩
      have hlift : intervalDomainLift (u τ) z.1 = u τ z := by
        simp [intervalDomainLift, z.2]
      simpa only [hlift] using hMz
    -- `u₀` admissibility = BddAbove of `range |u₀|`.
    have hu₀_bddR : BddAbove (Set.range (fun z : intervalDomainPoint => |u₀ z|)) := hAdm.1
    -- BddAbove of `range |u τ - u₀|` via triangle inequality.
    have hdiff_bddR :
        BddAbove (Set.range (fun z : intervalDomainPoint => |u τ z - u₀ z|)) := by
      obtain ⟨M₁, hM₁⟩ := hu_bddR
      obtain ⟨M₂, hM₂⟩ := hu₀_bddR
      refine ⟨M₁ + M₂, ?_⟩
      rintro _ ⟨z, rfl⟩
      have h1 : |u τ z| ≤ M₁ := hM₁ ⟨z, rfl⟩
      have h2 : |u₀ z| ≤ M₂ := hM₂ ⟨z, rfl⟩
      calc |u τ z - u₀ z|
          ≤ |u τ z| + |u₀ z| := abs_sub _ _
        _ ≤ M₁ + M₂ := add_le_add h1 h2
    -- pointwise extraction at `⟨x, hx⟩ : intervalDomainPoint`.
    have hpt : |u τ ⟨x, hx⟩ - u₀ ⟨x, hx⟩|
        ≤ intervalDomainSupNorm (fun z => u τ z - u₀ z) := by
      have hmem : |u τ ⟨x, hx⟩ - u₀ ⟨x, hx⟩|
          ∈ Set.range (fun z : intervalDomainPoint => |u τ z - u₀ z|) :=
        ⟨⟨x, hx⟩, rfl⟩
      exact le_csSup hdiff_bddR hmem
    have hpt_lt : |u τ ⟨x, hx⟩ - u₀ ⟨x, hx⟩| < δ₀ / 2 :=
      lt_of_le_of_lt hpt hsup_lt
    -- translate to lift: at `x ∈ Icc 0 1`, `lift (u τ) x = u τ ⟨x, hx⟩` and
    -- `lift u₀ x = u₀ ⟨x, hx⟩`.
    have hlift_u : intervalDomainLift (u τ) x = u τ ⟨x, hx⟩ := by
      simp [intervalDomainLift, hx]
    have hlift_u₀ : intervalDomainLift u₀ x = u₀ ⟨x, hx⟩ := by
      simp [intervalDomainLift, hx]
    -- so `lift (u τ) x ≥ u₀ ⟨x,hx⟩ - δ₀/2 ≥ δ₀ - δ₀/2 = δ₀/2 ≥ δ`.
    have habs_lt : |intervalDomainLift (u τ) x - u₀ ⟨x, hx⟩| < δ₀ / 2 := by
      rw [hlift_u]; exact hpt_lt
    have hge : u₀ ⟨x, hx⟩ - δ₀ / 2 < intervalDomainLift (u τ) x := by
      have := abs_lt.mp habs_lt
      linarith [this.1]
    have hu₀_ge : δ₀ ≤ u₀ ⟨x, hx⟩ := hδ₀_le ⟨x, hx⟩
    have hhalf_le : δ₀ / 2 ≤ intervalDomainLift (u τ) x := by linarith
    exact le_trans (min_le_left _ _) hhalf_le
  · -- slab leg `[τ_a, t]`: use `lift_u_uniformPositive_on_compact`.
    have hcase' : τ_a < τ := lt_of_not_ge hcase
    have hτ_in : τ ∈ Set.Icc τ_a t := ⟨le_of_lt hcase', hτ_le_t⟩
    have hδa_le : δ_a ≤ intervalDomainLift (u τ) x := hδ_a_bound τ hτ_in x hx
    exact le_trans (min_le_right _ _) hδa_le

/-- **Range boundedness of `|u t ·|` for a classical solution at an interior time.**

For an `IsPaper2ClassicalSolution` and every interior time `t ∈ (0,T)`, the
absolute-value range `{|u t x| : x : intervalDomainPoint}` is bounded above.

Proof: conjunct (7) of `intervalDomainClassicalRegularity` provides
`ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Icc 0 1)`, hence
`ContinuousOn (intervalDomainLift (u t)) (Icc 0 1)`; composing with `|·|`
gives a continuous function on the compact `Icc 0 1`, whose image is bounded
above.  For every `x : intervalDomainPoint`, `intervalDomainLift (u t) x.1 =
u t x` (since `x.1 ∈ Icc 0 1`), so the absolute-value range over the subtype
embeds into the absolute-value image over `Icc 0 1`, which is bounded.

This is the internal discharge for the `hrangeBounded` data hypothesis of the
`no_hreach` umbrella in `IntervalDomainTheorem11Umbrella.lean`. -/
theorem classicalSolution_u_range_bddAbove
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    BddAbove (Set.range (fun x : intervalDomainPoint => |u t x|)) := by
  classical
  -- conjunct (7): closed-domain `C²` regularity of the lift on `Icc 0 1`.
  have hcont : ContinuousOn (intervalDomainLift (u t)) (Set.Icc (0:ℝ) 1) :=
    ((hsol.regularity.2.2.2.2.1 t ht).1.1).continuousOn
  -- image of `|lift (u t)|` over the compact `Icc 0 1` is bounded above.
  obtain ⟨B, hB⟩ :=
    (isCompact_Icc.image_of_continuousOn hcont.abs).bddAbove
  refine ⟨B, ?_⟩
  rintro _ ⟨x, rfl⟩
  -- bound at `x.1 ∈ Icc 0 1`.
  have hBx : |intervalDomainLift (u t) x.1| ≤ B := hB ⟨x.1, x.2, rfl⟩
  -- `intervalDomainLift (u t) x.1 = u t x`.
  have hlift : intervalDomainLift (u t) x.1 = u t x := by
    simp [intervalDomainLift, x.2]
  simpa only [hlift] using hBx

end

end ShenWork.Paper2
