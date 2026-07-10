import ShenWork.Paper2.IntervalCoeffLadderPassBasic

/-!
# Full coefficient ladder envelope interface

This file packages the coefficient-side ladder used on positive restart
windows.  The analytic product/resolver work is represented by a uniform source
envelope for the divergence term; the heat/Duhamel gain is proved here.
-/

open scoped Real

noncomputable section

namespace ShenWork.Paper2.IntervalCoeffLadderFull

open ShenWork.IntervalDuhamelClosedC2 (duhamelSpectralCoeff)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.Paper2.IntervalCoeffLadderPassBasic

/-- A uniform coefficient envelope on a positive time window.  The zero mode is
carried by `env`; polynomial decay is required only for nonzero modes. -/
structure WindowCoefficientEnvelope (m : ℕ) (c T' : ℝ) (û : ℝ → ℕ → ℝ) where
  env : ℕ → ℝ
  C : ℝ
  hC : 0 < C
  henv : ∀ s ∈ Set.Icc c T', ∀ k, |û s k| ≤ env k
  hdecay : ∀ k, k ≠ 0 → env k ≤ C / (k : ℝ) ^ m

/-- A source envelope with decay exponent `r`, uniform on a restart window. -/
structure WindowSourceEnvelope (r : ℕ) (c T' : ℝ) (a : ℝ → ℕ → ℝ) where
  C : ℝ
  hC : 0 ≤ C
  hbound :
    ∀ τ ∈ Set.Icc c T', ∀ s, 0 ≤ s → s ≤ τ → ∀ k, k ≠ 0 →
      |a s k| ≤ C / (k : ℝ) ^ r

lemma one_div_unitIntervalCosineEigenvalue_le_one_div_nat_sq {k : ℕ} (hk : k ≠ 0) :
    1 / unitIntervalCosineEigenvalue k ≤ 1 / (k : ℝ) ^ 2 := by
  have hkpos : 0 < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
  have hk2pos : 0 < (k : ℝ) ^ 2 := sq_pos_of_ne_zero (ne_of_gt hkpos)
  have hpi2 : (1 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hle : (k : ℝ) ^ 2 ≤ unitIntervalCosineEigenvalue k := by
    calc (k : ℝ) ^ 2
        = (k : ℝ) ^ 2 * 1 := by ring
      _ ≤ (k : ℝ) ^ 2 * Real.pi ^ 2 :=
          mul_le_mul_of_nonneg_left hpi2 (sq_nonneg _)
      _ = unitIntervalCosineEigenvalue k := by
          unfold unitIntervalCosineEigenvalue
          ring
  exact one_div_le_one_div_of_le hk2pos hle

lemma one_div_unitIntervalCosineEigenvalue_le_one_div_nat {k : ℕ} (hk : k ≠ 0) :
    1 / unitIntervalCosineEigenvalue k ≤ 1 / (k : ℝ) := by
  have hkpos : 0 < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
  have hkone : (1 : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hk)
  have hsq_le : 1 / (k : ℝ) ^ 2 ≤ 1 / (k : ℝ) := by
    have hle : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
    exact one_div_le_one_div_of_le hkpos hle
  exact (one_div_unitIntervalCosineEigenvalue_le_one_div_nat_sq hk).trans hsq_le

lemma div_unitIntervalCosineEigenvalue_le_div_nat {A : ℝ} (hA : 0 ≤ A)
    {k : ℕ} (hk : k ≠ 0) :
    A / unitIntervalCosineEigenvalue k ≤ A / (k : ℝ) := by
  calc A / unitIntervalCosineEigenvalue k
      = A * (1 / unitIntervalCosineEigenvalue k) := by ring
    _ ≤ A * (1 / (k : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (one_div_unitIntervalCosineEigenvalue_le_one_div_nat hk) hA
    _ = A / (k : ℝ) := by ring

lemma div_unitIntervalCosineEigenvalue_power_le {A : ℝ} (hA : 0 ≤ A)
    {r k : ℕ} (hk : k ≠ 0) :
    (A / (k : ℝ) ^ r) / unitIntervalCosineEigenvalue k
      ≤ A / (k : ℝ) ^ (r + 2) := by
  have hkpos : 0 < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
  have hfactor : 0 ≤ A / (k : ℝ) ^ r := by positivity
  calc (A / (k : ℝ) ^ r) / unitIntervalCosineEigenvalue k
      = (A / (k : ℝ) ^ r) * (1 / unitIntervalCosineEigenvalue k) := by ring
    _ ≤ (A / (k : ℝ) ^ r) * (1 / (k : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left
          (one_div_unitIntervalCosineEigenvalue_le_one_div_nat_sq hk) hfactor
    _ = A / (k : ℝ) ^ (r + 2) := by
        field_simp [ne_of_gt hkpos]
        rw [pow_add]
        ring

/-- Pass 1: on a positive restart window, a bounded source plus a homogeneous
`k⁻¹` tail gives a `k⁻¹` restart-coefficient envelope. -/
def restartCoeff_pass1_window_envelope
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ} {c T' H S Z : ℝ}
    (hc : 0 < c) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (hhom :
      ∀ τ ∈ Set.Icc c T', ∀ k, k ≠ 0 →
        |Real.exp (-τ * unitIntervalCosineEigenvalue k) * a₀ k| ≤ H / (k : ℝ))
    (hsrc :
      ∀ τ ∈ Set.Icc c T', ∀ s, 0 ≤ s → s ≤ τ → ∀ k, |a s k| ≤ S)
    (hzero :
      ∀ τ ∈ Set.Icc c T', |localRestartCoeff a₀ a τ 0| ≤ max Z 0) :
    WindowCoefficientEnvelope 1 c T' (fun τ k => localRestartCoeff a₀ a τ k) := by
  refine
    { env := fun k => if k = 0 then max Z 0 else (H + S + 1) / (k : ℝ)
      C := H + S + 1
      hC := by linarith
      henv := ?_
      hdecay := ?_ }
  · intro τ hτ k
    by_cases hk : k = 0
    · subst k
      simp [hzero τ hτ]
    · have hτpos : 0 < τ := lt_of_lt_of_le hc hτ.1
      have hduh := duhamelSpectralCoeff_abs_le_div_eigenvalue
        (a := a) hτpos hk (E := S)
        (fun s hs0 hsτ => hsrc τ hτ s hs0 hsτ k)
      have hduh_k : |duhamelSpectralCoeff a τ k| ≤ S / (k : ℝ) :=
        hduh.trans (div_unitIntervalCosineEigenvalue_le_div_nat hS hk)
      unfold localRestartCoeff
      have hsum :
          |Real.exp (-τ * unitIntervalCosineEigenvalue k) * a₀ k
              + duhamelSpectralCoeff a τ k|
            ≤ H / (k : ℝ) + S / (k : ℝ) :=
        (abs_add_le _ _).trans (add_le_add (hhom τ hτ k hk) hduh_k)
      have hkpos : 0 < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
      have htail : H / (k : ℝ) + S / (k : ℝ)
          ≤ (H + S + 1) / (k : ℝ) := by
        field_simp [ne_of_gt hkpos]
        linarith
      simpa [hk] using hsum.trans htail
  · intro k hk
    simp [hk]

/-- Duhamel gives two powers of mode decay: a source in `A_r` yields restart
coefficients in `A_{r+2}`, once the homogeneous part has the same tail. -/
def duhamel_power_gain_window
    {r : ℕ} {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ} {c T' H Z : ℝ}
    (hc : 0 < c) (hH : 0 ≤ H) (src : WindowSourceEnvelope r c T' a)
    (hhom :
      ∀ τ ∈ Set.Icc c T', ∀ k, k ≠ 0 →
        |Real.exp (-τ * unitIntervalCosineEigenvalue k) * a₀ k|
          ≤ H / (k : ℝ) ^ (r + 2))
    (hzero :
      ∀ τ ∈ Set.Icc c T', |localRestartCoeff a₀ a τ 0| ≤ max Z 0) :
    WindowCoefficientEnvelope (r + 2) c T'
      (fun τ k => localRestartCoeff a₀ a τ k) := by
  refine
    { env := fun k =>
        if k = 0 then max Z 0 else (H + src.C + 1) / (k : ℝ) ^ (r + 2)
      C := H + src.C + 1
      hC := by linarith [src.hC]
      henv := ?_
      hdecay := ?_ }
  · intro τ hτ k
    by_cases hk : k = 0
    · subst k
      simp [hzero τ hτ]
    · have hτpos : 0 < τ := lt_of_lt_of_le hc hτ.1
      have hduh := duhamelSpectralCoeff_abs_le_div_eigenvalue
        (a := a) hτpos hk (E := src.C / (k : ℝ) ^ r)
        (src.hbound τ hτ · · · k hk)
      have hduh_k :
          |duhamelSpectralCoeff a τ k|
            ≤ src.C / (k : ℝ) ^ (r + 2) :=
        hduh.trans (div_unitIntervalCosineEigenvalue_power_le src.hC hk)
      unfold localRestartCoeff
      have hsum :
          |Real.exp (-τ * unitIntervalCosineEigenvalue k) * a₀ k
              + duhamelSpectralCoeff a τ k|
            ≤ H / (k : ℝ) ^ (r + 2) + src.C / (k : ℝ) ^ (r + 2) :=
        (abs_add_le _ _).trans (add_le_add (hhom τ hτ k hk) hduh_k)
      have hkpos : 0 < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
      have htail :
          H / (k : ℝ) ^ (r + 2) + src.C / (k : ℝ) ^ (r + 2)
            ≤ (H + src.C + 1) / (k : ℝ) ^ (r + 2) := by
        have hpowpos : 0 < (k : ℝ) ^ (r + 2) := by positivity
        field_simp [ne_of_gt hpowpos]
        linarith
      simpa [hk] using hsum.trans htail
  · intro k hk
    simp [hk]

/-- Generic ladder gain.  The product/resolver/divergence chain supplies
`chemDiv` with an `A_r` envelope; the heat equation turns it into `A_{r+2}`.
For the chemotaxis branch one applies this with `r = m - 1`, i.e. net
`A_m → A_{m+1}`. -/
def ladder_pass_gain_envelope
    {r : ℕ} {a₀ : ℕ → ℝ} {chemDiv : ℝ → ℕ → ℝ} {c T' H Z : ℝ}
    (hc : 0 < c) (hH : 0 ≤ H)
    (hdiv : WindowSourceEnvelope r c T' chemDiv)
    (hhom :
      ∀ τ ∈ Set.Icc c T', ∀ k, k ≠ 0 →
        |Real.exp (-τ * unitIntervalCosineEigenvalue k) * a₀ k|
          ≤ H / (k : ℝ) ^ (r + 2))
    (hzero :
      ∀ τ ∈ Set.Icc c T', |localRestartCoeff a₀ chemDiv τ 0| ≤ max Z 0) :
    WindowCoefficientEnvelope (r + 2) c T'
      (fun τ k => localRestartCoeff a₀ chemDiv τ k) :=
  duhamel_power_gain_window hc hH hdiv hhom hzero

/-- Existence form of the generic gain, with the same constructive witness as
`ladder_pass_gain_envelope`. -/
theorem ladder_pass_gain
    {r : ℕ} {a₀ : ℕ → ℝ} {chemDiv : ℝ → ℕ → ℝ} {c T' H Z : ℝ}
    (hc : 0 < c) (hH : 0 ≤ H)
    (hdiv : WindowSourceEnvelope r c T' chemDiv)
    (hhom :
      ∀ τ ∈ Set.Icc c T', ∀ k, k ≠ 0 →
        |Real.exp (-τ * unitIntervalCosineEigenvalue k) * a₀ k|
          ≤ H / (k : ℝ) ^ (r + 2))
    (hzero :
      ∀ τ ∈ Set.Icc c T', |localRestartCoeff a₀ chemDiv τ 0| ≤ max Z 0) :
    ∃ E : WindowCoefficientEnvelope (r + 2) c T'
      (fun τ k => localRestartCoeff a₀ chemDiv τ k), 0 < E.C := by
  exact ⟨ladder_pass_gain_envelope hc hH hdiv hhom hzero,
    (ladder_pass_gain_envelope hc hH hdiv hhom hzero).hC⟩

def ladder_pass2_from_divergence_A0
    {a₀ : ℕ → ℝ} {chemDiv : ℝ → ℕ → ℝ} {c T' H Z : ℝ}
    (hc : 0 < c) (hH : 0 ≤ H)
    (hdiv : WindowSourceEnvelope 0 c T' chemDiv)
    (hhom :
      ∀ τ ∈ Set.Icc c T', ∀ k, k ≠ 0 →
        |Real.exp (-τ * unitIntervalCosineEigenvalue k) * a₀ k|
          ≤ H / (k : ℝ) ^ 2)
    (hzero :
      ∀ τ ∈ Set.Icc c T', |localRestartCoeff a₀ chemDiv τ 0| ≤ max Z 0) :
    WindowCoefficientEnvelope 2 c T'
      (fun τ k => localRestartCoeff a₀ chemDiv τ k) :=
  ladder_pass_gain_envelope hc hH hdiv hhom hzero

/-- After pass 4, `λ_k |û_k|` is summable on every time slice in the window. -/
theorem eigenvalue_weighted_summable_of_pass4
    {c T' : ℝ} {û : ℝ → ℕ → ℝ}
    (env4 : WindowCoefficientEnvelope 4 c T' û)
    {s : ℝ} (hs : s ∈ Set.Icc c T') :
    Summable (fun k : ℕ => unitIntervalCosineEigenvalue k * |û s k|) := by
  have hmajor : Summable (fun k : ℕ => env4.C * Real.pi ^ 2 / (k : ℝ) ^ 2) := by
    have hbase : Summable (fun k : ℕ => 1 / (k : ℝ) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
    refine (hbase.mul_left (env4.C * Real.pi ^ 2)).congr ?_
    intro k
    ring
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hmajor
  · exact mul_nonneg (by unfold unitIntervalCosineEigenvalue; positivity) (abs_nonneg _)
  · by_cases hk : k = 0
    · subst k
      simp [unitIntervalCosineEigenvalue]
    · have hcoeff : |û s k| ≤ env4.C / (k : ℝ) ^ 4 :=
        (env4.henv s hs k).trans (env4.hdecay k hk)
      have hlam_nn : 0 ≤ unitIntervalCosineEigenvalue k := by
        unfold unitIntervalCosineEigenvalue
        positivity
      calc unitIntervalCosineEigenvalue k * |û s k|
          ≤ unitIntervalCosineEigenvalue k * (env4.C / (k : ℝ) ^ 4) :=
            mul_le_mul_of_nonneg_left hcoeff hlam_nn
        _ = env4.C * Real.pi ^ 2 / (k : ℝ) ^ 2 := by
            have hkpos : 0 < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
            unfold unitIntervalCosineEigenvalue
            field_simp [ne_of_gt hkpos]

end ShenWork.Paper2.IntervalCoeffLadderFull
