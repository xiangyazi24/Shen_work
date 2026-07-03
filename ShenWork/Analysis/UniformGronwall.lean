import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Uniform Gronwall Lemma (Temam)

The Uniform Gronwall lemma converts **time-integrated** bounds on a
non-negative function into **pointwise-in-time** bounds, given a
differential inequality. This is a standard tool in dissipative PDE
theory (see Temam, *Infinite-Dimensional Dynamical Systems in
Mechanics and Physics*, Lemma III.1.1).

## Main result

`uniform_gronwall_bound_const`: if `y' ≤ α·y + β` on `[0,T]` with
`y ≥ 0`, and `∫_t^{t+r} y ≤ a₃` for all valid `t`, then
`y(t) ≤ (a₃/r + β·r)·exp(α·r)` for `t ∈ [r, T]`.

The proof applies the standard Gronwall inequality (Mathlib's
`gronwallBound`) starting from each `s ∈ [t-r, t]`, then integrates
over `s`.
-/

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

namespace ShenWork.Analysis.UniformGronwall

private lemma exp_sub_one_le_mul_exp_of_nonneg {x : ℝ} (_hx : 0 ≤ x) :
    Real.exp x - 1 ≤ x * Real.exp x := by
  have h := Real.one_sub_le_exp_neg x
  have hmul := mul_le_mul_of_nonneg_right h (Real.exp_nonneg x)
  have hle : (1 - x) * Real.exp x ≤ 1 := by
    calc
      (1 - x) * Real.exp x ≤ Real.exp (-x) * Real.exp x := hmul
      _ = Real.exp 0 := by
        rw [← Real.exp_add]
        ring_nf
      _ = 1 := Real.exp_zero
  nlinarith

private lemma gronwallBound_le_mul_exp
    {δ K ε R : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε) (hR : 0 ≤ R) :
    gronwallBound δ K ε R ≤ (δ + ε * R) * Real.exp (K * R) := by
  by_cases hK0 : K = 0
  · subst K
    simp [gronwallBound_K0]
  · have hKpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hK0)
    have hKR : 0 ≤ K * R := mul_nonneg hK hR
    have hterm := exp_sub_one_le_mul_exp_of_nonneg hKR
    have hcoef : 0 ≤ ε / K := div_nonneg hε hKpos.le
    have hterm' :
        ε / K * (Real.exp (K * R) - 1) ≤
          ε / K * ((K * R) * Real.exp (K * R)) :=
      mul_le_mul_of_nonneg_left hterm hcoef
    calc
      gronwallBound δ K ε R
          = δ * Real.exp (K * R) + ε / K * (Real.exp (K * R) - 1) := by
              rw [gronwallBound_of_K_ne_0 hK0]
      _ ≤ δ * Real.exp (K * R) + ε / K * ((K * R) * Real.exp (K * R)) := by
              exact add_le_add_right hterm' _
      _ = (δ + ε * R) * Real.exp (K * R) := by
              field_simp [hK0]

private lemma gronwallBound_le_window
    {δ K ε r x : ℝ}
    (hδ : 0 ≤ δ) (hK : 0 ≤ K) (hε : 0 ≤ ε) (hr : 0 ≤ r) (hx : x ≤ r) :
    gronwallBound δ K ε x ≤ (δ + ε * r) * Real.exp (K * r) :=
  ((gronwallBound_mono hδ hε hK) hx).trans (gronwallBound_le_mul_exp hK hε hr)

private theorem uniform_gronwall_bound_const_core
    {y dy : ℝ → ℝ} {T α β r a₃ : ℝ}
    (hr : 0 < r) (_hrT : r ≤ T)
    (hα_nonneg : 0 ≤ α) (hβ_nonneg : 0 ≤ β) (_ha₃_nonneg : 0 ≤ a₃)
    (hy_cont : ContinuousOn y (Icc 0 T))
    (hy_nonneg : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ y t)
    (hderiv :
      ∀ t ∈ Ioo (0 : ℝ) T,
        ∀ R, dy t < R →
          ∃ᶠ z in 𝓝[>] t, (z - t)⁻¹ * (y z - y t) < R)
    (hderiv_le : ∀ t ∈ Ioo (0 : ℝ) T, dy t ≤ α * y t + β)
    (hint : ∀ t, 0 ≤ t → t + r ≤ T →
      ∫ s in t..t + r, y s ≤ a₃) :
    ∀ t, r ≤ t → t ≤ T →
      y t ≤ (a₃ / r + β * r) * Real.exp (α * r) := by
  intro t ht_ge ht_le
  set E : ℝ := Real.exp (α * r) with hE
  have hE_nonneg : 0 ≤ E := by
    rw [hE]
    exact (Real.exp_pos _).le
  have hleft_le : t - r ≤ t := by linarith
  have hstart_nonneg : 0 ≤ t - r := by linarith
  have hwindow :
      ∫ s in t - r..t, y s ≤ a₃ := by
    simpa [sub_add_cancel] using hint (t - r) hstart_nonneg (by simpa [sub_add_cancel] using ht_le)
  have hy_int : IntervalIntegrable y volume (t - r) t := by
    have hcont : ContinuousOn y (Icc (t - r) t) :=
      hy_cont.mono (fun x hx => by
        constructor
        · exact le_trans hstart_nonneg hx.1
        · exact le_trans hx.2 ht_le)
    exact hcont.intervalIntegrable_of_Icc hleft_le
  have hpoint :
      ∀ s ∈ Ioo (t - r) t, y t ≤ E * (y s + β * r) := by
    intro s hs
    have hs_pos : 0 < s := lt_of_le_of_lt hstart_nonneg hs.1
    have hs_le_T : s ≤ T := le_trans (le_of_lt hs.2) ht_le
    have hys_nonneg : 0 ≤ y s := hy_nonneg s ⟨le_of_lt hs_pos, hs_le_T⟩
    have hcont_st : ContinuousOn y (Icc s t) :=
      hy_cont.mono (fun x hx => by
        constructor
        · exact le_trans (le_of_lt hs_pos) hx.1
        · exact le_trans hx.2 ht_le)
    have hlim_st :
        ∀ x ∈ Ico s t, ∀ R, dy x < R →
          ∃ᶠ z in 𝓝[>] x, (z - x)⁻¹ * (y z - y x) < R := by
      intro x hx R hR
      have hx_pos : 0 < x := lt_of_lt_of_le hs_pos hx.1
      have hx_lt_T : x < T := lt_of_lt_of_le hx.2 ht_le
      exact hderiv x ⟨hx_pos, hx_lt_T⟩ R hR
    have hbound_st : ∀ x ∈ Ico s t, dy x ≤ α * y x + β := by
      intro x hx
      have hx_pos : 0 < x := lt_of_lt_of_le hs_pos hx.1
      have hx_lt_T : x < T := lt_of_lt_of_le hx.2 ht_le
      exact hderiv_le x ⟨hx_pos, hx_lt_T⟩
    have hG :=
      le_gronwallBound_of_liminf_deriv_right_le
        (f := y) (f' := dy) (δ := y s) (K := α) (ε := β)
        (a := s) (b := t) hcont_st hlim_st le_rfl hbound_st
    have ht_mem : t ∈ Icc s t := ⟨le_of_lt hs.2, le_rfl⟩
    have hgr : y t ≤ gronwallBound (y s) α β (t - s) := hG t ht_mem
    have hdt_le : t - s ≤ r := by
      linarith [hs.1]
    have hgb :
        gronwallBound (y s) α β (t - s) ≤ (y s + β * r) * E := by
      simpa [hE] using
        gronwallBound_le_window (δ := y s) (K := α) (ε := β) (r := r) (x := t - s)
          hys_nonneg hα_nonneg hβ_nonneg hr.le hdt_le
    exact hgr.trans (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hgb)
  have hright_int :
      IntervalIntegrable (fun s => E * (y s + β * r)) volume (t - r) t :=
    (hy_int.add intervalIntegrable_const).const_mul E
  have hmono :
      (∫ s in t - r..t, y t) ≤
        ∫ s in t - r..t, E * (y s + β * r) :=
    intervalIntegral.integral_mono_on_of_le_Ioo hleft_le intervalIntegrable_const hright_int hpoint
  have hleft_eq : (∫ s in t - r..t, y t) = r * y t := by
    rw [intervalIntegral.integral_const]
    simp [smul_eq_mul]
  have hright_eq :
      (∫ s in t - r..t, E * (y s + β * r)) =
        E * ((∫ s in t - r..t, y s) + β * r ^ 2) := by
    have hsum_int :
        IntervalIntegrable (fun s => y s + β * r) volume (t - r) t :=
      hy_int.add intervalIntegrable_const
    have hinner :
        (∫ s in t - r..t, y s + β * r) =
          (∫ s in t - r..t, y s) + β * r ^ 2 := by
      rw [intervalIntegral.integral_add hy_int intervalIntegrable_const]
      rw [intervalIntegral.integral_const]
      simp [smul_eq_mul]
      ring_nf
    calc
      (∫ s in t - r..t, E * (y s + β * r))
          = ∫ s in t - r..t, E • (y s + β * r) := by simp
      _ = E • (∫ s in t - r..t, y s + β * r) :=
          IntervalIntegrable.integral_smul E hsum_int
      _ = E * ((∫ s in t - r..t, y s) + β * r ^ 2) := by
          rw [hinner]
          simp [smul_eq_mul]
  have hmain : r * y t ≤ E * (a₃ + β * r ^ 2) := by
    calc
      r * y t = ∫ s in t - r..t, y t := hleft_eq.symm
      _ ≤ ∫ s in t - r..t, E * (y s + β * r) := hmono
      _ = E * ((∫ s in t - r..t, y s) + β * r ^ 2) := hright_eq
      _ ≤ E * (a₃ + β * r ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add_left hwindow _) hE_nonneg
  have hdiv : y t ≤ E * (a₃ + β * r ^ 2) / r := by
    calc
      y t = (r * y t) / r := by
        field_simp [hr.ne']
      _ ≤ E * (a₃ + β * r ^ 2) / r := div_le_div_of_nonneg_right hmain hr.le
  calc
    y t ≤ E * (a₃ + β * r ^ 2) / r := hdiv
    _ = (a₃ / r + β * r) * Real.exp (α * r) := by
      rw [hE]
      field_simp [hr.ne']

/-- **Uniform Gronwall lemma with constant coefficients.**

Given a continuous non-negative function `y` on `[0, T]` satisfying
`y'(t) ≤ α·y(t) + β` (in the liminf-of-right-derivative sense),
if the time integral `∫_t^{t+r} y(s) ds ≤ a₃` for all `t ∈ [0, T-r]`,
then `y(t) ≤ (a₃/r + β·r) · exp(α·r)` for all `t ∈ [r, T]`.

This is the workhorse for upgrading energy/dissipation estimates
(time-integrated) to uniform-in-time bounds.
-/
theorem uniform_gronwall_bound_const
    {y : ℝ → ℝ} {T α β r a₃ : ℝ}
    (hr : 0 < r) (hrT : r ≤ T)
    (hα_nonneg : 0 ≤ α) (hβ_nonneg : 0 ≤ β) (ha₃_nonneg : 0 ≤ a₃)
    (hy_cont : ContinuousOn y (Icc 0 T))
    (hy_nonneg : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ y t)
    (hderiv :
      ∀ t ∈ Ioo (0 : ℝ) T,
        ∀ R, α * y t + β < R →
          ∃ᶠ z in 𝓝[>] t, (z - t)⁻¹ * (y z - y t) < R)
    (hint : ∀ t, 0 ≤ t → t + r ≤ T →
      ∫ s in t..t + r, y s ≤ a₃) :
    ∀ t, r ≤ t → t ≤ T →
      y t ≤ (a₃ / r + β * r) * Real.exp (α * r) := by
  exact uniform_gronwall_bound_const_core hr hrT hα_nonneg hβ_nonneg ha₃_nonneg
    hy_cont hy_nonneg hderiv (fun t ht => le_rfl) hint

/-- Variant taking `HasDerivAt` hypotheses instead of liminf slopes. -/
theorem uniform_gronwall_bound_const_of_hasDerivAt
    {y y' : ℝ → ℝ} {T α β r a₃ : ℝ}
    (hr : 0 < r) (hrT : r ≤ T)
    (hα_nonneg : 0 ≤ α) (hβ_nonneg : 0 ≤ β) (ha₃_nonneg : 0 ≤ a₃)
    (hy_cont : ContinuousOn y (Icc 0 T))
    (hy_nonneg : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ y t)
    (hderiv : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt y (y' t) t)
    (hderiv_le : ∀ t ∈ Ioo (0 : ℝ) T, y' t ≤ α * y t + β)
    (hint : ∀ t, 0 ≤ t → t + r ≤ T →
      ∫ s in t..t + r, y s ≤ a₃) :
    ∀ t, r ≤ t → t ≤ T →
      y t ≤ (a₃ / r + β * r) * Real.exp (α * r) := by
  refine uniform_gronwall_bound_const_core hr hrT hα_nonneg hβ_nonneg ha₃_nonneg
    hy_cont hy_nonneg ?_ hderiv_le hint
  intro t ht R hR
  exact ((hderiv t ht).hasDerivWithinAt).liminf_right_slope_le hR

end ShenWork.Analysis.UniformGronwall
