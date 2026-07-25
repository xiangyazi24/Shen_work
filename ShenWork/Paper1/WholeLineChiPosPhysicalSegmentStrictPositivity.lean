import ShenWork.Paper1.WholeLineWeightedRegularityGlobalStrictPositivityNatural
import ShenWork.Paper1.WholeLinePhysicalMildUniqueness

/-!
# Strict positivity on arbitrary physical BUC segments

The maximal-orbit construction is assembled from physical mild segments, not
from the historical fixed-ceiling global glue.  The local comparison theorem
already propagates a positive left-hand floor on one canonical contraction
window.  Here it is iterated over an arbitrary physical fixed point.  The
result is independent of `WholeLineCauchyCeilingRegime`.
-/

open Filter Real Set Topology Function

noncomputable section

namespace ShenWork.Paper1

/-- A nonnegative physical BUC fixed point whose datum has a positive
left-hand floor is strictly positive at every positive time and retains a
positive left-hand floor on every closed time slice. -/
theorem wholeLinePhysicalFixedPoint_pos_and_left_of_posAtBot
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 < T)
    (u₀ : WholeLineBUC)
    (hleft : StrictlyPositiveAtLeft u₀.1)
    (U : WholeLineBUCTrajectory T)
    (hfixed : IsFixedPt (wholeLineCauchyBUCMildMap p hM hT.le u₀) U)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (U z).1 x ∈ Set.Icc (0 : ℝ) M) :
    (∀ z : Set.Icc (0 : ℝ) T, 0 < z.1 → ∀ x, 0 < (U z).1 x) ∧
      (∀ z : Set.Icc (0 : ℝ) T, StrictlyPositiveAtLeft (U z).1) := by
  obtain ⟨δ, hδ, hsmall⟩ :=
    exists_pos_time_wholeLineCauchyBUCMildRate_lt_one p hM
  have hflux := wholeLinePhysicalFixedPoint_fluxSource_spatialC1_positive
    p hM hT u₀ U hfixed hstrip
  let zzero : Set.Icc (0 : ℝ) T := ⟨0, le_rfl, hT.le⟩
  have hUzero : U zzero = u₀ := by
    have hf := congrArg (fun Q : WholeLineBUCTrajectory T => Q zzero) hfixed
    simpa [zzero, wholeLineCauchyBUCMildMap,
      wholeLineCauchyGradientDuhamelBUC,
      wholeLineCauchyValueDuhamelBUC,
      wholeLineCauchyHeatBUCTotal] using hf.symm
  have hstage : ∀ n : ℕ, ∀ (s : ℝ),
      ∀ hs : s ∈ Set.Icc (0 : ℝ) (min T ((n : ℝ) * δ)),
      (0 < s → ∀ x, 0 < (U ⟨s, hs.1,
        hs.2.trans (min_le_left T ((n : ℝ) * δ))⟩).1 x) ∧
      StrictlyPositiveAtLeft
        (U ⟨s, hs.1,
          hs.2.trans (min_le_left T ((n : ℝ) * δ))⟩).1 := by
    intro n
    induction n with
    | zero =>
        intro s hs
        have hs0 : s = 0 := by
          norm_num [min_eq_right hT.le] at hs
          exact hs
        subst s
        constructor
        · intro hbad
          exact (lt_irrefl 0 hbad).elim
        · have hz :
              (⟨0, hs.1,
                hs.2.trans (min_le_left T ((0 : ℕ) * δ))⟩ :
                  Set.Icc (0 : ℝ) T) = zzero := by
              apply Subtype.ext
              rfl
          rw [hz, hUzero]
          exact hleft
    | succ n ih =>
        let a : ℝ := min T ((n : ℝ) * δ)
        let b : ℝ := min T (((n + 1 : ℕ) : ℝ) * δ)
        let h : ℝ := b - a
        have ha0 : 0 ≤ a := by
          dsimp [a]
          exact le_min hT.le (mul_nonneg (Nat.cast_nonneg n) hδ.le)
        have hab : a ≤ b := by
          dsimp [a, b]
          apply min_le_min le_rfl
          push_cast
          nlinarith
        have hbT : b ≤ T := min_le_left _ _
        have hh0 : 0 ≤ h := sub_nonneg.mpr hab
        have hah : a + h ≤ T := by dsimp [h]; linarith
        have hhδ : h ≤ δ := by
          dsimp [h, a, b]
          by_cases hnT : (n : ℝ) * δ ≤ T
          · rw [min_eq_right hnT]
            have hb : min T (((n + 1 : ℕ) : ℝ) * δ) ≤
                ((n : ℝ) * δ) + δ := by
              apply le_trans (min_le_right _ _)
              push_cast
              ring_nf
              exact le_rfl
            linarith
          · have hTn : T ≤ (n : ℝ) * δ := le_of_not_ge hnT
            rw [min_eq_left hTn]
            have hTb : min T (((n + 1 : ℕ) : ℝ) * δ) = T := by
              apply min_eq_left
              exact hTn.trans (by push_cast; nlinarith)
            rw [hTb]
            linarith [hδ]
        have hsmallh : wholeLineCauchyBUCMildRate p M h < 1 :=
          lt_of_le_of_lt
            (wholeLineCauchyBUCMildRate_mono p hM hh0 hhδ) hsmall
        intro s hs
        have hsb : s ≤ b := by simpa [b] using hs.2
        by_cases hsa : s ≤ a
        · have hsOld : s ∈ Set.Icc (0 : ℝ) a := ⟨hs.1, hsa⟩
          have hold := ih s (by simpa [a] using hsOld)
          simpa [a, b] using hold
        · have has : a < s := lt_of_not_ge hsa
          have hhpos : 0 < h := by
            dsimp [h]
            linarith
          let za : Set.Icc (0 : ℝ) T :=
            ⟨a, ha0, (le_add_of_nonneg_right hh0).trans hah⟩
          have hchart :
              wholeLineBUCTrajectoryShift ha0 hh0 hah U =
                wholeLineCauchyBUCMildFixedPoint p hM hh0 (U za) hsmallh := by
            by_cases haZero : a = 0
            · have hza : za = zzero := by
                apply Subtype.ext
                exact haZero
              have hrestrict := wholeLineFixedPoint_restrict_eq_canonical
                p hM hT.le u₀ U hfixed hh0 (by linarith) hsmallh
              rw [hza, hUzero]
              convert hrestrict using 1; simp only [haZero]
            · have hapos : 0 < a := lt_of_le_of_ne ha0 (Ne.symm haZero)
              apply wholeLinePhysicalFixedPoint_shift_eq_of_fluxC1
                p hM hT.le u₀ U hfixed hapos hhpos hah hsmallh
              · intro q hq y
                exact (hflux q ⟨hq.1, hq.2.trans
                  ((le_add_of_nonneg_right hh0).trans hah)⟩).1 y
              · intro q hq
                exact (hflux q ⟨hq.1, hq.2.trans
                  ((le_add_of_nonneg_right hh0).trans hah)⟩).2.1
              · intro q hq
                exact (hflux q ⟨hq.1, hq.2.trans
                  ((le_add_of_nonneg_right hh0).trans hah)⟩).2.2
          let Canon : WholeLineBUCTrajectory h :=
            wholeLineCauchyBUCMildFixedPoint p hM hh0 (U za) hsmallh
          have hstripCanon : ∀ z : Set.Icc (0 : ℝ) h, ∀ x,
              (Canon z).1 x ∈ Set.Icc (0 : ℝ) M := by
            intro z x
            have happ := congrArg
              (fun Q : WholeLineBUCTrajectory h => Q z) hchart
            have hzT : a + z.1 ∈ Set.Icc (0 : ℝ) T :=
              ⟨add_nonneg ha0 z.2.1, by linarith [z.2.2, hah]⟩
            have heq : Canon z = U ⟨a + z.1, hzT⟩ := by
              simpa [Canon, za, wholeLineBUCTrajectoryShift] using happ.symm
            rw [heq]
            exact hstrip ⟨a + z.1, hzT⟩ x
          have hdatum0 : ∀ x, 0 ≤ (U za).1 x := fun x => (hstrip za x).1
          have hdatumLeft : StrictlyPositiveAtLeft (U za).1 := by
            by_cases haZero : a = 0
            · have hza : za = zzero := by
                apply Subtype.ext
                exact haZero
              rw [hza, hUzero]
              exact hleft
            · have hapos : 0 < a := lt_of_le_of_ne ha0 (Ne.symm haZero)
              have haOld : a ∈ Set.Icc (0 : ℝ) (min T ((n : ℝ) * δ)) := by
                simpa [a] using And.intro ha0 (le_refl a)
              exact (ih a haOld).2
          have hlocal := wholeLineCauchyBUCMildFixedPoint_pos_and_left_of_posAtBot
            p hM hhpos (U za) hdatum0 hdatumLeft hsmallh
              (by simpa [Canon] using hstripCanon)
          let r : ℝ := s - a
          have hr0 : 0 < r := sub_pos.mpr has
          have hrh : r ≤ h := by dsimp [r, h]; linarith
          let zr : Set.Icc (0 : ℝ) h := ⟨r, hr0.le, hrh⟩
          have heqSlice : Canon zr =
              U ⟨s, hs.1, hsb.trans hbT⟩ := by
            have happ := congrArg
              (fun Q : WholeLineBUCTrajectory h => Q zr) hchart
            simpa [Canon, za, zr, r, wholeLineBUCTrajectoryShift] using happ.symm
          constructor
          · intro _hspos x
            rw [← heqSlice]
            exact hlocal.1 zr hr0 x
          · rw [← heqSlice]
            exact hlocal.2 zr
  obtain ⟨n, hn⟩ := exists_nat_gt (T / δ)
  have hTn : T ≤ (n : ℝ) * δ := ((div_lt_iff₀ hδ).mp hn).le
  have hmin : min T ((n : ℝ) * δ) = T := min_eq_left hTn
  constructor
  · intro z hz x
    have hz' : z.1 ∈ Set.Icc (0 : ℝ) (min T ((n : ℝ) * δ)) := by
      rw [hmin]
      exact z.2
    exact (hstage n z.1 hz').1 hz x
  · intro z
    have hz' : z.1 ∈ Set.Icc (0 : ℝ) (min T ((n : ℝ) * δ)) := by
      rw [hmin]
      exact z.2
    exact (hstage n z.1 hz').2

section AxiomAudit

#print axioms wholeLinePhysicalFixedPoint_pos_and_left_of_posAtBot

end AxiomAudit

end ShenWork.Paper1
