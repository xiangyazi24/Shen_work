/-
  ShenWork/PDE/PoincareInequality.lean

  One-dimensional Poincaré inequality on a finite interval [0, L]:

    ∫₀ᴸ (f(x) - f̄)² dx ≤ L² · ∫₀ᴸ f'(x)² dx

  where f̄ = (1/L) ∫₀ᴸ f(x) dx is the mean value.

  The constant L² is not optimal (the optimal constant is (L/π)²),
  but suffices for downstream PDE estimates.

  Proof sketch:
  1. Let g = f - f̄. Then ∫₀ᴸ g = 0 and g' = f'.
  2. By the mean value theorem for integrals (or IVT + integral constraint),
     there exists x₀ ∈ [0,L] with g(x₀) = 0.
  3. By FTC: g(x) = ∫_{x₀}^x f'(s) ds.
  4. |g(x)| ≤ ∫₀ᴸ |f'(s)| ds.
  5. By Cauchy–Schwarz: (∫₀ᴸ |f'|)² ≤ L · ∫₀ᴸ f'².
  6. So g(x)² ≤ L · ∫₀ᴸ f'².
  7. Integrating: ∫₀ᴸ g² ≤ L² · ∫₀ᴸ f'².
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.IntermediateValue

open MeasureTheory Set intervalIntegral
open scoped ENNReal Interval

noncomputable section

namespace ShenWork.Poincare

/-! ### Helper: a continuous function with zero integral has a root -/

/-- If `g` is continuous on `[0, L]` and `∫₀ᴸ g = 0`, then `g` has a root in `[0, L]`.
This follows from the intermediate value theorem: if `g` were always positive (or always
negative), the integral would be strictly positive (resp. negative). -/
theorem continuous_zero_integral_has_root
    {L : ℝ} (hL : 0 < L)
    {g : ℝ → ℝ}
    (hg_cont : ContinuousOn g (Icc 0 L))
    (hg_int : ∫ x in (0 : ℝ)..L, g x = 0) :
    ∃ x₀ ∈ Icc (0 : ℝ) L, g x₀ = 0 := by
  -- g attains its min and max on [0, L]
  have hne : (Icc (0 : ℝ) L).Nonempty := ⟨0, left_mem_Icc.mpr hL.le⟩
  obtain ⟨xmin, hxmin, hmin⟩ := IsCompact.exists_isMinOn isCompact_Icc hne hg_cont
  obtain ⟨xmax, hxmax, hmax⟩ := IsCompact.exists_isMaxOn isCompact_Icc hne hg_cont
  -- The min value is ≤ 0 and max value is ≥ 0 (from ∫g = 0)
  have hmin_le : g xmin ≤ 0 := by
    by_contra hc
    push Not at hc
    have hpos : ∀ x ∈ Ioc (0 : ℝ) L, 0 ≤ g x := by
      intro x hx
      exact le_of_lt (lt_of_lt_of_le hc (hmin (Ioc_subset_Icc_self hx)))
    have : 0 < ∫ x in (0 : ℝ)..L, g x :=
      integral_pos hL hg_cont hpos ⟨xmin, hxmin, hc⟩
    linarith
  have hmax_ge : 0 ≤ g xmax := by
    by_contra hc
    push Not at hc
    -- g xmax < 0, and g x ≤ g xmax for all x ∈ [0,L], so g x < 0 everywhere
    have hneg : ∀ x ∈ Ioc (0 : ℝ) L, 0 ≤ -g x := by
      intro x hx
      have h1 : g x ≤ g xmax := hmax (Ioc_subset_Icc_self hx)
      linarith
    have hng : 0 < ∫ x in (0 : ℝ)..L, -g x :=
      integral_pos hL hg_cont.neg hneg ⟨xmax, hxmax, neg_pos.mpr hc⟩
    have heq : ∫ x in (0 : ℝ)..L, -g x = -(∫ x in (0 : ℝ)..L, g x) :=
      intervalIntegral.integral_neg
    linarith
  -- By IVT, g has a root between xmin and xmax (or at one of them)
  rcases eq_or_lt_of_le hmin_le with heq | hlt
  · exact ⟨xmin, hxmin, heq⟩
  -- g xmin < 0
  rcases eq_or_lt_of_le hmax_ge with heq | hlt2
  · exact ⟨xmax, hxmax, heq.symm⟩
  -- g xmin < 0 < g xmax, use IVT
  rcases le_or_gt xmin xmax with hle | hgt
  · have hIcc_sub : Icc xmin xmax ⊆ Icc 0 L :=
      Icc_subset_Icc hxmin.1 hxmax.2
    have hcont_sub : ContinuousOn g (Icc xmin xmax) :=
      hg_cont.mono hIcc_sub
    have := intermediate_value_Icc hle hcont_sub
    have hmem : (0 : ℝ) ∈ Icc (g xmin) (g xmax) :=
      ⟨hlt.le, hlt2.le⟩
    obtain ⟨x₀, hx₀_mem, hx₀_eq⟩ := this hmem
    exact ⟨x₀, hIcc_sub hx₀_mem, hx₀_eq⟩
  · have hIcc_sub : Icc xmax xmin ⊆ Icc 0 L :=
      Icc_subset_Icc hxmax.1 hxmin.2
    have hcont_sub : ContinuousOn g (Icc xmax xmin) :=
      hg_cont.mono hIcc_sub
    have := intermediate_value_Icc' hgt.le hcont_sub
    have hmem : (0 : ℝ) ∈ Icc (g xmin) (g xmax) :=
      ⟨hlt.le, hlt2.le⟩
    obtain ⟨x₀, hx₀_mem, hx₀_eq⟩ := this hmem
    exact ⟨x₀, hIcc_sub hx₀_mem, hx₀_eq⟩

/-! ### Helper: integral Cauchy–Schwarz on an interval

  `(∫₀ᴸ |h(x)| dx)² ≤ L · ∫₀ᴸ h(x)² dx`

  Proof: for any `t`, `0 ≤ ∫₀ᴸ (t - |h(x)|)² dx`.
  Expanding and choosing `t = (∫|h|)/L` gives the result.
-/

/-- Cauchy–Schwarz for interval integrals:
  `(∫₀ᴸ |h|)² ≤ L · ∫₀ᴸ h²` -/
theorem integral_abs_sq_le_length_mul_integral_sq
    {L : ℝ} (hL : 0 < L)
    {h : ℝ → ℝ}
    (hh_int : IntervalIntegrable h volume 0 L)
    (hh_sq_int : IntervalIntegrable (fun x => h x ^ 2) volume 0 L) :
    (∫ x in (0 : ℝ)..L, |h x|) ^ 2 ≤ L * ∫ x in (0 : ℝ)..L, h x ^ 2 := by
  set A := ∫ x in (0 : ℝ)..L, |h x|
  set B := ∫ x in (0 : ℝ)..L, h x ^ 2
  -- Key identity: |h x|² = h x²
  have habs_sq : ∀ x, |h x| ^ 2 = h x ^ 2 := fun x => sq_abs (h x)
  -- The integrand |h|² is integrable
  have habs_sq_int : IntervalIntegrable (fun x => |h x| ^ 2) volume 0 L :=
    hh_sq_int.congr_ae ((ae_restrict_mem measurableSet_uIoc).mono
      fun x _ => (habs_sq x).symm)
  -- For any t, ∫(t - |h|)² ≥ 0
  have hkey : ∀ t : ℝ, 0 ≤ t ^ 2 * L - 2 * t * A + B := by
    intro t
    -- The quadratic integrand (t - |h x|)² is nonneg
    have hnn : 0 ≤ ∫ x in (0 : ℝ)..L, (t - |h x|) ^ 2 := by
      apply integral_nonneg_of_forall hL.le
      intro x; exact sq_nonneg _
    -- Expand the integral
    have h_eq : ∫ x in (0 : ℝ)..L, (t - |h x|) ^ 2 =
        t ^ 2 * L - 2 * t * A + B := by
      -- Rewrite integrand as sum
      have h_rw : (fun x => (t - |h x|) ^ 2) = (fun x => t ^ 2 - 2 * t * |h x| + |h x| ^ 2) :=
        funext fun x => by ring
      rw [h_rw]
      -- Split the integral
      have h_int1 : IntervalIntegrable (fun _ => t ^ 2) volume 0 L :=
        intervalIntegrable_const
      have h_int2 : IntervalIntegrable (fun x => 2 * t * |h x|) volume 0 L :=
        (hh_int.norm).const_mul (2 * t)
      rw [show (fun x => t ^ 2 - 2 * t * |h x| + |h x| ^ 2) =
        (fun x => (t ^ 2 - 2 * t * |h x|) + |h x| ^ 2) from funext fun x => by ring]
      rw [integral_add (h_int1.sub h_int2) habs_sq_int]
      rw [integral_sub h_int1 h_int2]
      rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
      simp only [sub_zero, smul_eq_mul]
      -- Now we have: t² * L - 2t * ∫|h| + ∫|h|²
      -- and ∫|h|² = ∫h² = B
      have : ∫ x in (0 : ℝ)..L, |h x| ^ 2 = B := by
        congr 1; ext x; exact habs_sq x
      rw [this]
      ring
    linarith
  -- Substitute t = A / L
  have hspec := hkey (A / L)
  have hsimp : (A / L) ^ 2 * L - 2 * (A / L) * A + B = B - A ^ 2 / L := by
    field_simp
    ring
  rw [hsimp] at hspec
  -- hspec : 0 ≤ B - A² / L, so A² / L ≤ B, so A² ≤ L * B
  rw [sub_nonneg, div_le_iff₀ hL] at hspec
  linarith

/-! ### The Poincaré inequality -/

/-- **Poincaré inequality on [0, L]**.  For `f` continuously differentiable on `[0, L]`,
  with mean `f̄ = (1/L) ∫₀ᴸ f`, we have
  `∫₀ᴸ (f - f̄)² ≤ L² · ∫₀ᴸ (f')²`. -/
theorem poincare_interval
    {L : ℝ} (hL : 0 < L)
    {f f' : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Icc 0 L))
    (hf_deriv : ∀ x ∈ Icc 0 L, HasDerivAt f (f' x) x)
    (hf'_int : IntervalIntegrable f' volume 0 L)
    (hf'_sq_int : IntervalIntegrable (fun x => f' x ^ 2) volume 0 L) :
    let fbar := (1 / L) * ∫ x in (0 : ℝ)..L, f x
    ∫ x in (0 : ℝ)..L, (f x - fbar) ^ 2 ≤
      L ^ 2 * ∫ x in (0 : ℝ)..L, f' x ^ 2 := by
  intro fbar
  -- Step 1: let g x = f x - fbar; then g' = f' and ∫g = 0
  set g : ℝ → ℝ := fun x => f x - fbar with hg_def
  have hg_cont : ContinuousOn g (Icc 0 L) :=
    hf_cont.sub continuousOn_const
  have hg_deriv : ∀ x ∈ Icc 0 L, HasDerivAt g (f' x) x := by
    intro x hx
    have h := (hf_deriv x hx).sub (hasDerivAt_const x fbar)
    simp only [sub_zero] at h
    exact h
  have hg_int_zero : ∫ x in (0 : ℝ)..L, g x = 0 := by
    simp only [g]
    rw [integral_sub (hf_cont.intervalIntegrable_of_Icc hL.le) intervalIntegrable_const]
    rw [intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul, fbar]
    field_simp
    ring
  -- Step 2: find x₀ with g(x₀) = 0
  obtain ⟨x₀, hx₀, hgx₀⟩ := continuous_zero_integral_has_root hL hg_cont hg_int_zero
  -- Step 3: pointwise bound |g(x)| ≤ ∫₀ᴸ |f'|
  have hpointwise : ∀ x ∈ Icc (0 : ℝ) L, g x ^ 2 ≤ L * ∫ s in (0 : ℝ)..L, f' s ^ 2 := by
    intro x hx
    -- FTC: g(x) = g(x₀) + ∫_{x₀}^x f'(s) ds = ∫_{x₀}^x f'(s) ds
    have huIcc_sub : uIcc x₀ x ⊆ Icc 0 L := uIcc_subset_Icc hx₀ hx
    have hftc : g x = ∫ s in x₀..x, f' s := by
      have := integral_eq_sub_of_hasDerivAt
        (fun s hs => hg_deriv s (huIcc_sub hs))
        (hf'_int.mono (uIcc_subset_uIcc
          (Icc_subset_uIcc hx₀) (Icc_subset_uIcc hx)) le_rfl)
      rw [this, hgx₀, sub_zero]
    -- |g(x)| = |∫_{x₀}^x f'| ≤ ∫₀ᴸ |f'|
    have habs_bound : |g x| ≤ ∫ s in (0 : ℝ)..L, |f' s| := by
      rw [hftc]
      rcases le_or_gt x₀ x with hle | hgt
      · calc |∫ s in x₀..x, f' s|
            ≤ ∫ s in x₀..x, |f' s| := abs_integral_le_integral_abs hle
          _ ≤ ∫ s in (0 : ℝ)..L, |f' s| :=
              integral_mono_interval hx₀.1 hle hx.2
                (Filter.Eventually.of_forall fun _ => abs_nonneg _)
                hf'_int.norm
      · rw [integral_symm, abs_neg]
        calc |∫ s in x..x₀, f' s|
            ≤ ∫ s in x..x₀, |f' s| := abs_integral_le_integral_abs hgt.le
          _ ≤ ∫ s in (0 : ℝ)..L, |f' s| :=
              integral_mono_interval hx.1 hgt.le hx₀.2
                (Filter.Eventually.of_forall fun _ => abs_nonneg _)
                hf'_int.norm
    -- g(x)² = |g(x)|² ≤ (∫|f'|)² ≤ L · ∫f'² (by Cauchy-Schwarz)
    have hCS := integral_abs_sq_le_length_mul_integral_sq hL hf'_int hf'_sq_int
    calc g x ^ 2 = |g x| ^ 2 := (sq_abs _).symm
      _ ≤ (∫ s in (0 : ℝ)..L, |f' s|) ^ 2 := by
          apply sq_le_sq'
          · linarith [abs_nonneg (g x)]
          · exact habs_bound
      _ ≤ L * ∫ s in (0 : ℝ)..L, f' s ^ 2 := hCS
  -- Step 4: integrate the pointwise bound
  -- ∫g² ≤ ∫(L · ∫f'²) = L · ∫f'² · L = L² · ∫f'²
  have hg_sq_int : IntervalIntegrable (fun x => g x ^ 2) volume 0 L :=
    (hg_cont.pow 2).intervalIntegrable_of_Icc hL.le
  calc ∫ x in (0 : ℝ)..L, g x ^ 2
      ≤ ∫ _x in (0 : ℝ)..L, L * ∫ s in (0 : ℝ)..L, f' s ^ 2 := by
        apply integral_mono_on hL.le hg_sq_int intervalIntegrable_const
        exact hpointwise
    _ = L * (∫ s in (0 : ℝ)..L, f' s ^ 2) * L := by
        rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
        ring
    _ = L ^ 2 * ∫ s in (0 : ℝ)..L, f' s ^ 2 := by ring

/-- Coarse Neumann-Poincaré inequality on the unit interval.

The sharp constant is `1 / π²`; this theorem keeps the already proved
constant `1`, which is enough for the downstream absorbing estimate because it
is still a positive Poincaré constant. -/
theorem poincare_unit_interval_coarse
    {f f' : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf_deriv : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivAt f (f' x) x)
    (hf'_int : IntervalIntegrable f' volume 0 1)
    (hf'_sq_int : IntervalIntegrable (fun x => f' x ^ 2) volume 0 1) :
    let fbar := ∫ x in (0 : ℝ)..1, f x
    ∫ x in (0 : ℝ)..1, (f x - fbar) ^ 2 ≤
      ∫ x in (0 : ℝ)..1, f' x ^ 2 := by
  intro fbar
  have h := poincare_interval (L := 1) (f := f) (f' := f')
    (by norm_num) hf_cont hf_deriv hf'_int hf'_sq_int
  change ∫ x in (0 : ℝ)..1,
      (f x - ((1 / 1) * ∫ x in (0 : ℝ)..1, f x)) ^ 2 ≤
        1 ^ 2 * ∫ x in (0 : ℝ)..1, f' x ^ 2 at h
  simpa using h

end ShenWork.Poincare

end