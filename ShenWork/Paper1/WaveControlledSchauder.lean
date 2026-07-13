import ShenWork.Paper1.WaveControlledModulusTrap
import ShenWork.Paper1.CompactConvexProfileSchauder

namespace ShenWork.Paper1

noncomputable section

namespace InControlledLowerPinnedMonotoneTrap

variable {κ M L sigma aL C : ℝ} {φ : ℝ → ℝ}

/-- The controlled parameter trap satisfies the exact hypotheses of the
compact-open Schauder--Tychonoff construction. -/
theorem boundedConvexProfileTrapData
    (hne : ∃ u,
      InControlledLowerPinnedMonotoneTrap κ M L sigma aL C φ u) :
    BoundedConvexProfileTrapData
      (InControlledLowerPinnedMonotoneTrap κ M L sigma aL C φ) M := by
  refine
    { nonempty := hne
      convex := set_convex κ M L sigma aL C φ
      continuous := ?_
      abs_le := ?_ }
  · intro u hu
    exact hu.bare.trap.cunif_bdd.1
  · intro u hu x
    rw [abs_of_nonneg (hu.bare.nonneg x)]
    exact hu.bare.le_M x

/-- Schauder--Tychonoff on the corrected compact convex parameter trap, with
no finite-cube approximation package left as a hypothesis. -/
theorem schauderPrinciple
    (hne : ∃ u,
      InControlledLowerPinnedMonotoneTrap κ M L sigma aL C φ u) :
    LocalUniformSchauderFixedPointPrinciple
      (InControlledLowerPinnedMonotoneTrap κ M L sigma aL C φ) :=
  (boundedConvexProfileTrapData hne).schauderPrinciple

end InControlledLowerPinnedMonotoneTrap

namespace InLowerPinnedUniformModulusMonotoneTrap

variable {κ M L : ℝ} {φ : ℝ → ℝ}

/-- The no-tail, uniform-modulus parameter trap is a bounded convex subset of
the compact-open profile space. -/
theorem boundedConvexProfileTrapData
    (hne : ∃ u,
      InLowerPinnedUniformModulusMonotoneTrap κ M L φ u) :
    BoundedConvexProfileTrapData
      (InLowerPinnedUniformModulusMonotoneTrap κ M L φ) M := by
  refine
    { nonempty := hne
      convex := set_convex κ M L φ
      continuous := ?_
      abs_le := ?_ }
  · intro u hu
    exact hu.uniformTrap.bare.trap.cunif_bdd.1
  · intro u hu x
    rw [abs_of_nonneg (hu.uniformTrap.bare.nonneg x)]
    exact hu.uniformTrap.bare.le_M x

/-- A self-map of the uniform-modulus trap automatically has compact-open
sequentially compact range. -/
theorem compactRange_of_mapsTo
    (hM : 0 ≤ M) (hL : 0 ≤ L)
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (hmap : ∀ u,
      InLowerPinnedUniformModulusMonotoneTrap κ M L φ u →
      InLowerPinnedUniformModulusMonotoneTrap κ M L φ (Tmap u)) :
    LocalUniformSequentiallyCompactRange
      (InLowerPinnedUniformModulusMonotoneTrap κ M L φ) Tmap := by
  intro seq hseq
  obtain ⟨sub, hsub, g, hg, hconv⟩ :=
    locallyUniform_sequentiallyCompact
      (κ := κ) (M := M) (L := L) (φ := φ) hM hL
      (fun n => Tmap (seq n)) (fun n => hmap (seq n) (hseq n))
  exact ⟨sub, hsub, g, hg, hconv⟩

/-- Schauder--Tychonoff directly on the compact-convex modulus trap.  The
finite-cube approximate-fixed-point package is no longer a hypothesis. -/
theorem exists_fixed
    (hne : ∃ u,
      InLowerPinnedUniformModulusMonotoneTrap κ M L φ u)
    (hM : 0 ≤ M) (hL : 0 ≤ L)
    (Tmap : (ℝ → ℝ) → ℝ → ℝ)
    (hmap : ∀ u,
      InLowerPinnedUniformModulusMonotoneTrap κ M L φ u →
      InLowerPinnedUniformModulusMonotoneTrap κ M L φ (Tmap u))
    (hcont : LocalUniformContinuousOn
      (InLowerPinnedUniformModulusMonotoneTrap κ M L φ) Tmap) :
    ∃ U,
      InLowerPinnedUniformModulusMonotoneTrap κ M L φ U ∧ Tmap U = U :=
  (boundedConvexProfileTrapData hne).exists_fixed hmap hcont
    (compactRange_of_mapsTo hM hL hmap)

/-- A continuous auxiliary limit self-map on the uniform-modulus trap gives a
full `FrozenWaveMapConstruction`; compactness and the fixed point are both
derived internally. -/
theorem frozenWaveMapConstruction
    {p : CMParams} {c : ℝ}
    (hne : ∃ u,
      InLowerPinnedUniformModulusMonotoneTrap κ M L φ u)
    (hM : 0 ≤ M) (hL : 0 ≤ L)
    (Tmap : (ℝ → ℝ) → ℝ → ℝ)
    (hmap : ∀ u,
      InLowerPinnedUniformModulusMonotoneTrap κ M L φ u →
      InLowerPinnedUniformModulusMonotoneTrap κ M L φ (Tmap u))
    (hlimit : ∀ u,
      InLowerPinnedUniformModulusMonotoneTrap κ M L φ u →
      FrozenAuxiliaryLimitOutput p c κ M
        (InLowerPinnedUniformModulusMonotoneTrap κ M L φ) u (Tmap u))
    (hcont : LocalUniformContinuousOn
      (InLowerPinnedUniformModulusMonotoneTrap κ M L φ) Tmap) :
    FrozenWaveMapConstruction p c κ M
      (InLowerPinnedUniformModulusMonotoneTrap κ M L φ) := by
  have hcompact := compactRange_of_mapsTo hM hL hmap
  exact ⟨Tmap, hmap, hlimit, hcont, hcompact,
    exists_fixed hne hM hL Tmap hmap hcont⟩

end InLowerPinnedUniformModulusMonotoneTrap

section AxiomAudit

#print axioms InControlledLowerPinnedMonotoneTrap.boundedConvexProfileTrapData
#print axioms InControlledLowerPinnedMonotoneTrap.schauderPrinciple
#print axioms InLowerPinnedUniformModulusMonotoneTrap.boundedConvexProfileTrapData
#print axioms InLowerPinnedUniformModulusMonotoneTrap.compactRange_of_mapsTo
#print axioms InLowerPinnedUniformModulusMonotoneTrap.exists_fixed
#print axioms InLowerPinnedUniformModulusMonotoneTrap.frozenWaveMapConstruction

end AxiomAudit

end

end ShenWork.Paper1
