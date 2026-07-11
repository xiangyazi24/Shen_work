/-
  Finite chaining for truncated positive-time gradient windows.

  The output on window k supplies the left input for window k+1 whenever the
  windows abut and overlap.  All windows use one common gradient envelope G;
  concrete callers may obtain it from a finite maximum or, for equal-width
  windows, from their common affine fixed point.
-/

import ShenWork.Paper2.IntervalTruncatedGradientWindow

open Set

noncomputable section

namespace ShenWork.Paper2.TruncatedGradientWindow

open ShenWork.IntervalDomain (intervalDomainPoint)
open ShenWork.HeatKernelGradientEstimates
  (heatGradientLinftyLinftyConstant heatGradientLinftyLinftyConstant_nonneg)

/-- An equal-step chain whose windows are
`[(k+1)h, (k+2)h, (k+4)h]`.  All windows therefore have the same restart gap
and the same affine gradient map. -/
structure EqualStepGradientWindowChain (t B_F χ : ℝ) where
  N : ℕ
  h : ℝ
  h_pos : 0 < h
  target : ((N : ℝ) + 4) * h = t
  contract :
    heatGradientLinftyLinftyConstant * (2 * (|χ| * B_F)) *
      Real.sqrt (3 * h) < 1

namespace EqualStepGradientWindowChain

def a {t B_F χ : ℝ} (C : EqualStepGradientWindowChain t B_F χ)
    (k : ℕ) : ℝ :=
  ((k : ℝ) + 1) * C.h

def lo {t B_F χ : ℝ} (C : EqualStepGradientWindowChain t B_F χ)
    (k : ℕ) : ℝ :=
  ((k : ℝ) + 2) * C.h

def hi {t B_F χ : ℝ} (C : EqualStepGradientWindowChain t B_F χ)
    (k : ℕ) : ℝ :=
  ((k : ℝ) + 4) * C.h

@[simp] theorem a_zero {t B_F χ : ℝ}
    (C : EqualStepGradientWindowChain t B_F χ) : C.a 0 = C.h := by
  simp [a]

@[simp] theorem lo_zero {t B_F χ : ℝ}
    (C : EqualStepGradientWindowChain t B_F χ) : C.lo 0 = 2 * C.h := by
  simp [lo]

@[simp] theorem hi_zero {t B_F χ : ℝ}
    (C : EqualStepGradientWindowChain t B_F χ) : C.hi 0 = 4 * C.h := by
  simp [hi]

theorem a_lt_lo {t B_F χ : ℝ}
    (C : EqualStepGradientWindowChain t B_F χ) (k : ℕ) :
    C.a k < C.lo k := by
  unfold a lo
  nlinarith [C.h_pos]

theorem lo_le_hi {t B_F χ : ℝ}
    (C : EqualStepGradientWindowChain t B_F χ) (k : ℕ) :
    C.lo k ≤ C.hi k := by
  unfold lo hi
  nlinarith [C.h_pos]

theorem next_a {t B_F χ : ℝ}
    (C : EqualStepGradientWindowChain t B_F χ) (k : ℕ) :
    C.a (k + 1) = C.lo k := by
  simp only [a, lo, Nat.cast_add, Nat.cast_one]
  ring

theorem overlap {t B_F χ : ℝ}
    (C : EqualStepGradientWindowChain t B_F χ) (k : ℕ) :
    C.lo (k + 1) ≤ C.hi k := by
  simp only [lo, hi, Nat.cast_add, Nat.cast_one]
  nlinarith [C.h_pos]

theorem hi_le_target {t B_F χ : ℝ}
    (C : EqualStepGradientWindowChain t B_F χ) {k : ℕ} (hk : k ≤ C.N) :
    C.hi k ≤ t := by
  have hkR : (k : ℝ) ≤ C.N := by exact_mod_cast hk
  calc
    C.hi k = ((k : ℝ) + 4) * C.h := rfl
    _ ≤ ((C.N : ℝ) + 4) * C.h :=
      mul_le_mul_of_nonneg_right (by linarith) C.h_pos.le
    _ = t := C.target

theorem hi_last {t B_F χ : ℝ}
    (C : EqualStepGradientWindowChain t B_F χ) : C.hi C.N = t := by
  simpa [hi] using C.target

@[simp] theorem lo_sub_a {t B_F χ : ℝ}
    (C : EqualStepGradientWindowChain t B_F χ) (k : ℕ) :
    C.lo k - C.a k = C.h := by
  unfold lo a
  ring

@[simp] theorem hi_sub_a {t B_F χ : ℝ}
    (C : EqualStepGradientWindowChain t B_F χ) (k : ℕ) :
    C.hi k - C.a k = 3 * C.h := by
  unfold hi a
  ring

theorem window_contraction {t B_F χ : ℝ}
    (C : EqualStepGradientWindowChain t B_F χ) (k : ℕ) :
    truncWindowB B_F χ (C.a k) (C.hi k) < 1 := by
  apply truncWindowB_lt_one_of_sqrt_prod
  simpa [C.hi_sub_a k] using C.contract

theorem fixedG_eq_zero {t B_F χ M A_L A_F : ℝ}
    (C : EqualStepGradientWindowChain t B_F χ) (k : ℕ) :
    truncWindowFixedG M A_L A_F B_F χ (C.a k) (C.lo k) (C.hi k) =
      truncWindowFixedG M A_L A_F B_F χ (C.a 0) (C.lo 0) (C.hi 0) := by
  unfold truncWindowFixedG truncWindowA truncWindowB
  rw [C.lo_sub_a k, C.hi_sub_a k, C.lo_sub_a 0, C.hi_sub_a 0]

theorem affine_eq_zero {t B_F χ M A_L A_F G : ℝ}
    (C : EqualStepGradientWindowChain t B_F χ) (k : ℕ) :
    truncWindowAffine M A_L A_F B_F χ (C.a k) (C.lo k) (C.hi k) G =
      truncWindowAffine M A_L A_F B_F χ (C.a 0) (C.lo 0) (C.hi 0) G := by
  unfold truncWindowAffine truncWindowA truncWindowB
  rw [C.lo_sub_a k, C.hi_sub_a k, C.lo_sub_a 0, C.hi_sub_a 0]

end EqualStepGradientWindowChain

/-- Every positive target time admits an equal-step finite chain on which the
gradient affine coefficient contracts. -/
theorem exists_equalStepGradientWindowChain
    {t B_F χ : ℝ} (ht : 0 < t) (hBF : 0 ≤ B_F) :
    Nonempty (EqualStepGradientWindowChain t B_F χ) := by
  let q : ℝ :=
    heatGradientLinftyLinftyConstant * (2 * (|χ| * B_F))
  have hq : 0 ≤ q := by
    dsimp only [q]
    exact mul_nonneg heatGradientLinftyLinftyConstant_nonneg
      (mul_nonneg (by norm_num) (mul_nonneg (abs_nonneg χ) hBF))
  obtain ⟨N, hN⟩ := exists_nat_gt (3 * t * q ^ 2)
  let h : ℝ := t / ((N : ℝ) + 4)
  have hden_pos : 0 < (N : ℝ) + 4 := by positivity
  have hh : 0 < h := div_pos ht hden_pos
  have htarget : ((N : ℝ) + 4) * h = t := by
    dsimp only [h]
    field_simp
  have hsmall_sq : q ^ 2 * (3 * h) < 1 := by
    have hnum : 3 * t * q ^ 2 < (N : ℝ) + 4 := by
      exact hN.trans_le (by norm_num)
    rw [show q ^ 2 * (3 * h) = (3 * t * q ^ 2) / ((N : ℝ) + 4) by
      dsimp only [h]
      ring]
    exact (div_lt_one hden_pos).2 hnum
  have hcontract : q * Real.sqrt (3 * h) < 1 := by
    have hrad : 0 ≤ 3 * h := mul_nonneg (by norm_num) hh.le
    have hsquare : (q * Real.sqrt (3 * h)) ^ 2 < 1 := by
      rw [mul_pow, Real.sq_sqrt hrad]
      exact hsmall_sq
    have hnonneg : 0 ≤ q * Real.sqrt (3 * h) :=
      mul_nonneg hq (Real.sqrt_nonneg _)
    nlinarith
  exact ⟨⟨N, h, hh, htarget, by simpa [q] using hcontract⟩⟩

/-- Chain finitely many gradient-window bootstraps.  The window builder is
given the left control propagated from the preceding window. -/
theorem truncatedGradientWindow_chain_all
    {p : CM2Params}
    {U : ℕ → ℝ → intervalDomainPoint → ℝ}
    {Src : ℕ → ℝ → ℝ → ℝ}
    {M A_L A_F B_F G : ℝ}
    {N : ℕ} {a lo hi : ℕ → ℝ}
    (hnext_a : ∀ k, k < N → a (k + 1) = lo k)
    (hoverlap : ∀ k, k < N → lo (k + 1) ≤ hi k)
    (hleft_zero : ∀ n : ℕ, IterGradOnWindow U (a 0) (lo 0) n G)
    (hbuild : ∀ k, k ≤ N →
      (∀ n : ℕ, IterGradOnWindow U (a k) (lo k) n G) →
        TruncatedGradientWindowWiring
          p U Src M A_L A_F B_F (a k) (lo k) (hi k) G) :
    ∀ k, k ≤ N → ∀ n : ℕ, IterGradOnWindow U (lo k) (hi k) n G := by
  intro k hk
  induction k with
  | zero =>
      exact truncatedGradientWindow_all
        (hbuild 0 (Nat.zero_le N) hleft_zero)
  | succ k ih =>
      have hk_lt_N : k < N := Nat.lt_of_succ_le hk
      have hk_le_N : k ≤ N := Nat.le_of_lt hk_lt_N
      have hprevious : ∀ n : ℕ,
          IterGradOnWindow U (lo k) (hi k) n G :=
        ih hk_le_N
      have hleft_next : ∀ n : ℕ,
          IterGradOnWindow U (a (k + 1)) (lo (k + 1)) n G := by
        intro n t hta htlo
        have hlot : lo k ≤ t := by
          rw [← hnext_a k hk_lt_N]
          exact hta
        have hthi : t ≤ hi k := htlo.trans (hoverlap k hk_lt_N)
        exact hprevious n t hlot hthi
      exact truncatedGradientWindow_all
        (hbuild (k + 1) hk hleft_next)

end ShenWork.Paper2.TruncatedGradientWindow
