import ShenWork.Paper1.WholeLineWeightedRegularityGlobalScaledTrapFamilyNatural
import ShenWork.Paper1.WholeLineWeightedRegularityChiNegPlateauWindowComparisonNatural

open Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Propagation of a lower plateau across all late canonical windows

The one-window comparison includes both endpoints.  Consequently its right
endpoint is exactly the initial seam of the successor window, so the same
stationary plateau propagates by ordinary induction over the canonical
restart index.
-/

/-- If a stationary lower plateau is seeded at the first late canonical
seam, and every subsequent closed global window has the same scaled trap,
then the plateau remains below the canonical global co-moving orbit on every
one of those windows. -/
theorem
    wholeLineCauchyGlobal_ge_lowerBarrierPlateau_on_all_late_windows_chiNonpos
    (p : CMParams) (hchi : p.χ ≤ 0)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    {N : ℕ} {c kappa kappaTilde D Q : ℝ}
    (hcond : PaperLemma42ExactConditions
      p c kappa kappaTilde 1)
    (hQ : 1 ≤ Q)
    (hD : paperScaledDMin p Q kappa kappaTilde c < D)
    (hD1 : 1 ≤ D)
    (hplateau : ∀ x, lowerBarrierPlateau kappa kappaTilde D x ≤
      constantSubsolutionThreshold p.χ kappa kappaTilde D)
    (htrap : ∀ n : ℕ, N ≤ n →
      InTimeWaveTrapSet kappa Q
        (wholeLineCauchyGlobalStep p u₀)
        (fun r x => wholeLineCauchyGlobalU p u₀
          (((n : ℝ) + 1) * wholeLineCauchyGlobalStep p u₀ + r)
          (x + c * (((n : ℝ) + 1) *
            wholeLineCauchyGlobalStep p u₀ + r))))
    (hseed : ∀ x, lowerBarrierPlateau kappa kappaTilde D x ≤
      wholeLineCauchyGlobalU p u₀
        (((N : ℝ) + 1) * wholeLineCauchyGlobalStep p u₀)
        (x + c * (((N : ℝ) + 1) *
          wholeLineCauchyGlobalStep p u₀))) :
    ∀ n : ℕ, N ≤ n →
      ∀ r ∈ Set.Icc (0 : ℝ) (wholeLineCauchyGlobalStep p u₀), ∀ x,
        lowerBarrierPlateau kappa kappaTilde D x ≤
          wholeLineCauchyGlobalU p u₀
            (((n : ℝ) + 1) * wholeLineCauchyGlobalStep p u₀ + r)
            (x + c * (((n : ℝ) + 1) *
              wholeLineCauchyGlobalStep p u₀ + r)) := by
  let step := wholeLineCauchyGlobalStep p u₀
  have hstep : 0 < step := by
    simpa only [step] using wholeLineCauchyGlobalStep_pos p u₀
  have hind : ∀ k : ℕ,
      ∀ r ∈ Set.Icc (0 : ℝ) step, ∀ x,
        lowerBarrierPlateau kappa kappaTilde D x ≤
          wholeLineCauchyGlobalU p u₀
            ((((N + k : ℕ) : ℝ) + 1) * step + r)
            (x + c * ((((N + k : ℕ) : ℝ) + 1) * step + r)) := by
    intro k
    induction k with
    | zero =>
        have ht₀ : 0 < ((N : ℝ) + 1) * step := by
          have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
          positivity
        have hwindow :=
          wholeLineCauchyGlobal_coMovingRestart_ge_lowerBarrierPlateau_chiNonpos_scaled
            p hchi u₀ hu₀ ht₀ hstep hcond hQ hD hD1 hplateau
              (by simpa only [step] using htrap N le_rfl)
              (by simpa only [step] using hseed)
        simpa only [Nat.add_zero, step] using hwindow
    | succ k ih =>
        have hNkSucc : N ≤ N + k.succ := Nat.le_add_right N k.succ
        have hseam : ∀ x, lowerBarrierPlateau kappa kappaTilde D x ≤
            wholeLineCauchyGlobalU p u₀
              ((((N + k.succ : ℕ) : ℝ) + 1) * step)
              (x + c * ((((N + k.succ : ℕ) : ℝ) + 1) * step)) := by
          intro x
          have hend := ih step ⟨hstep.le, le_rfl⟩ x
          have htime :
              ((((N + k : ℕ) : ℝ) + 1) * step + step) =
                (((((N + k.succ : ℕ) : ℝ) + 1) * step)) := by
            push_cast
            ring
          simpa only [htime] using hend
        have ht₀ : 0 < (((N + k.succ : ℕ) : ℝ) + 1) * step := by
          have hNk0 : 0 ≤ ((N + k.succ : ℕ) : ℝ) := Nat.cast_nonneg _
          positivity
        have hwindow :=
          wholeLineCauchyGlobal_coMovingRestart_ge_lowerBarrierPlateau_chiNonpos_scaled
            p hchi u₀ hu₀ ht₀ hstep hcond hQ hD hD1 hplateau
              (by simpa only [step] using htrap (N + k.succ) hNkSucc)
              hseam
        simpa only [step] using hwindow
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa only [step] using hind k

#print axioms
  wholeLineCauchyGlobal_ge_lowerBarrierPlateau_on_all_late_windows_chiNonpos

end ShenWork.Paper1
