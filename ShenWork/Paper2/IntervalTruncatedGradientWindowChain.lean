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
