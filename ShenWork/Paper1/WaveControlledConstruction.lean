import ShenWork.Paper1.WaveControlledRouteA
import ShenWork.Paper1.WaveControlledSchauder

open Set

noncomputable section

namespace ShenWork.Paper1

/-- Schauder fixed point of the corrected controlled Rothe map.  Source-box
existence, compactness, invariance, and the finite-dimensional
Schauder--Tychonoff construction are internal; the only map-level analytic
input is the explicitly named L10 continuous-dependence statement. -/
theorem paperControlledLowerRaw_exists_fixed
    {p : CMParams} {c lam M κ κtilde D Λ sigma aL C : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M}
    (floor : PaperControlledLowerRawFloor
      p c lam M κ κtilde D Λ sigma aL C hκ hM)
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hbarLip : ∀ x y,
      |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (hsigma : 0 < sigma)
    (hne : ∃ u, InControlledLowerPinnedMonotoneTrap κ M M sigma aL C
      (lowerBarrierRaw κ κtilde D) u)
    (hdep : PaperControlledLowerRawContinuousDependence floor) :
    ∃ U, InControlledLowerPinnedMonotoneTrap κ M M sigma aL C
        (lowerBarrierRaw κ κtilde D) U ∧
      rotheLimit (paperControlledLowerRawRotheSeq floor U) = U := by
  let Tmap : (ℝ → ℝ) → ℝ → ℝ := fun u =>
    rotheLimit (paperControlledLowerRawRotheSeq floor u)
  have hmap : ∀ u,
      InControlledLowerPinnedMonotoneTrap κ M M sigma aL C
        (lowerBarrierRaw κ κtilde D) u →
      InControlledLowerPinnedMonotoneTrap κ M M sigma aL C
        (lowerBarrierRaw κ κtilde D) (Tmap u) :=
    paperControlledLowerRaw_mapsTo floor hcond hD hD_ge_one
      hΛ0 hΛM hbarLip hsigma
  have hcompact : LocalUniformSequentiallyCompactRange
      (InControlledLowerPinnedMonotoneTrap κ M M sigma aL C
        (lowerBarrierRaw κ κtilde D)) Tmap :=
    paperControlledLowerRaw_compactRange floor hmap
  have hfix :=
    (InControlledLowerPinnedMonotoneTrap.boundedConvexProfileTrapData hne).exists_fixed
      hmap hdep hcompact
  simpa [Tmap] using hfix

section AxiomAudit

#print axioms paperControlledLowerRaw_exists_fixed

end AxiomAudit

end ShenWork.Paper1
