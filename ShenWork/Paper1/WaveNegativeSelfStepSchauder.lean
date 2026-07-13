import ShenWork.Paper1.WavePinnedStepUniqueness
import ShenWork.Paper1.WaveNegativePinnedSchauder
import ShenWork.Paper1.WaveControlledSchauder

open Filter Set Topology Real

noncomputable section

namespace ShenWork.Paper1

/-! ## A compact-convex regular trap for the negative branch

The long-time Rothe map is not needed to obtain the stationary profile.  On
the regular lower-pinned trap below, solve one genuine whole-line Green step
with both frozen and old profile equal to the parameter profile.  A fixed
point of that one-step map is already a stationary wave.
-/

/-- Lower-pinned profiles with the common spatial modulus needed by the
fixed-source construction and enough regularity for the Route-A derivative
maximum principle. -/
structure InLowerPinnedC1UniformModulusMonotoneTrap
    (κ M L : ℝ) (φ u : ℝ → ℝ) : Prop where
  pinned : InLowerPinnedUniformModulusMonotoneTrap κ M L φ u
  contDiff_one : ContDiff ℝ 1 u

namespace InLowerPinnedC1UniformModulusMonotoneTrap

variable {κ M L : ℝ} {φ u : ℝ → ℝ}

theorem bare
    (h : InLowerPinnedC1UniformModulusMonotoneTrap κ M L φ u) :
    InMonotoneWaveTrapSet κ M u :=
  h.pinned.uniformTrap.bare

theorem lower
    (h : InLowerPinnedC1UniformModulusMonotoneTrap κ M L φ u) :
    ∀ x, φ x ≤ u x :=
  h.pinned.lower

theorem modulus
    (h : InLowerPinnedC1UniformModulusMonotoneTrap κ M L φ u) :
    ∀ x y, |u x - u y| ≤ L * |x - y| :=
  h.pinned.uniformTrap.modulus

theorem toLowerPinned
    (h : InLowerPinnedC1UniformModulusMonotoneTrap κ M L φ u) :
    InLowerPinnedMonotoneTrap κ M φ u :=
  ⟨h.bare, h.lower⟩

/-- The regular trap remains convex.  The extra `C¹` field is stable under
the same convex combinations as the order and modulus fields. -/
theorem set_convex (κ M L : ℝ) (φ : ℝ → ℝ) :
    Convex ℝ
      {u : ℝ → ℝ |
        InLowerPinnedC1UniformModulusMonotoneTrap κ M L φ u} := by
  rw [convex_iff_add_mem]
  intro u hu v hv a b ha hb hab
  refine
    { pinned :=
        InLowerPinnedUniformModulusMonotoneTrap.set_convex κ M L φ
          hu.pinned hv.pinned ha hb hab
      contDiff_one := ?_ }
  exact (hu.contDiff_one.const_smul a).add (hv.contDiff_one.const_smul b)

/-- The regular lower-pinned trap has the bounded-convex data consumed by the
compact-open Schauder construction. -/
theorem boundedConvexProfileTrapData
    (hne : ∃ u,
      InLowerPinnedC1UniformModulusMonotoneTrap κ M L φ u) :
    BoundedConvexProfileTrapData
      (InLowerPinnedC1UniformModulusMonotoneTrap κ M L φ) M := by
  refine
    { nonempty := hne
      convex := set_convex κ M L φ
      continuous := ?_
      abs_le := ?_ }
  · intro u hu
    exact hu.contDiff_one.continuous
  · intro u hu x
    rw [abs_of_nonneg (hu.bare.nonneg x)]
    exact hu.bare.le_M x

end InLowerPinnedC1UniformModulusMonotoneTrap

/-! ## The selected genuine self step -/

/-- The old-profile data used by the fixed-source Green construction follows
directly from the regular trap. -/
def paperFixedSourceOldData_of_C1UniformTrap
    {κ M L : ℝ} {φ u : ℝ → ℝ}
    (hL : 0 ≤ L)
    (hu : InLowerPinnedC1UniformModulusMonotoneTrap κ M L φ u) :
    PaperFixedSourceOldData κ M u :=
  { cont := hu.bare.trap.cunif_bdd.1
    nonneg := hu.bare.nonneg
    le_barrier := hu.bare.le_upperBarrier
    L := L
    L_nonneg := hL
    local_lip := fun x y _ => hu.modulus x y }

/-- Select the exact whole-line Green solution of the cross-frozen implicit
step with frozen profile and old profile both equal to `u`. -/
noncomputable def paperNegativePinnedSelfStepData
    {p : CMParams} {c D : ℝ}
    (s : Paper1NegativeLocalStepScalarData p c D)
    {u : ℝ → ℝ}
    (hu : InLowerPinnedC1UniformModulusMonotoneTrap (kappa c) 1
      (paperNegativePinnedOrbitModulus s)
      (lowerBarrierRaw (kappa c) (negativeBranchTailCap p c) D) u) :
    PaperLocalFixedStepData
      p c s.lam 1 (kappa c) s.Λ s.B u u := by
  let oldData : PaperFixedSourceOldData (kappa c) 1 u :=
    paperFixedSourceOldData_of_C1UniformTrap
      (paperNegativePinnedOrbitModulus_nonneg s) hu
  let holderKernel :=
    paperFixedSourceMap_holder_kernel_of_oldData
      (p := p) (c := c) (lam := s.lam) (M := 1) (κ := kappa c)
      (B := s.B) (u := u) (Z := u)
      s.hlam s.hrpκ s.hrmκ s.hκ.le one_pos s.hB hu.bare.trap oldData
  let H : ℝ := Classical.choose holderKernel
  exact Classical.choose
    (paperLocalFixedStepData_exists_of_oldData
      p (c := c) (lam := s.lam) (M := 1) (κ := kappa c) (Λ := s.Λ)
      (B := s.B) (H := H) (u := u) (Z := u)
      s.hlam s.hrpκ s.hrmκ s.hκ one_pos s.hB hu.bare oldData
      s.sourceScalar le_rfl s.barrier s.hΛ)

/-- Totalized selected self-step map.  Schauder only uses the branch where the
parameter belongs to the regular trap. -/
noncomputable def paperNegativePinnedSelfStepMap
    {p : CMParams} {c D : ℝ}
    (s : Paper1NegativeLocalStepScalarData p c D) :
    (ℝ → ℝ) → ℝ → ℝ :=
  fun u => by
    classical
    exact if hu : InLowerPinnedC1UniformModulusMonotoneTrap (kappa c) 1
        (paperNegativePinnedOrbitModulus s)
        (lowerBarrierRaw (kappa c) (negativeBranchTailCap p c) D) u then
      (paperNegativePinnedSelfStepData s hu).fixed.W
    else upperBarrier (kappa c) 1

@[simp] theorem paperNegativePinnedSelfStepMap_eq
    {p : CMParams} {c D : ℝ}
    (s : Paper1NegativeLocalStepScalarData p c D)
    {u : ℝ → ℝ}
    (hu : InLowerPinnedC1UniformModulusMonotoneTrap (kappa c) 1
      (paperNegativePinnedOrbitModulus s)
      (lowerBarrierRaw (kappa c) (negativeBranchTailCap p c) D) u) :
    paperNegativePinnedSelfStepMap s u =
      (paperNegativePinnedSelfStepData s hu).fixed.W := by
  simp [paperNegativePinnedSelfStepMap, hu]

/-- The selected self step stays in the regular lower-pinned trap. -/
theorem paperNegativePinnedSelfStepMap_mapsTo
    {p : CMParams} {c D : ℝ}
    (hcond : PaperLemma42ExactConditions
      p c (kappa c) (negativeBranchTailCap p c) 1)
    (hD : paperDMin p.χ 1 (kappa c) (negativeBranchTailCap p c)
      p.m p.γ c < D)
    (hD1 : 1 ≤ D)
    (s : Paper1NegativeLocalStepScalarData p c D)
    {u : ℝ → ℝ}
    (hu : InLowerPinnedC1UniformModulusMonotoneTrap (kappa c) 1
      (paperNegativePinnedOrbitModulus s)
      (lowerBarrierRaw (kappa c) (negativeBranchTailCap p c) D) u) :
    InLowerPinnedC1UniformModulusMonotoneTrap (kappa c) 1
      (paperNegativePinnedOrbitModulus s)
      (lowerBarrierRaw (kappa c) (negativeBranchTailCap p c) D)
      (paperNegativePinnedSelfStepMap s u) := by
  let d := paperNegativePinnedSelfStepData s hu
  have hDpos : 0 < D := D_pos_of_paperDMin_lt hcond hD
  have hlower : ∀ x,
      lowerBarrierRaw (kappa c) (negativeBranchTailCap p c) D x ≤
        d.fixed.W x :=
    d.lowerRaw_of_old_lowerRaw hcond hD hD1 hu.toLowerPinned hu.lower
      s.hlam s.lowerRaw_small
  have hpinned : InLowerPinnedMonotoneTrap (kappa c) 1
      (lowerBarrierRaw (kappa c) (negativeBranchTailCap p c) D)
      d.fixed.W := by
    have hrouteCmono :
        paperCmono p (-p.χ) 1 (1 ^ p.γ) (2 * 1 ^ p.γ) ≤ s.Cmono := by
      rw [s.Cmono_eq]
      simp only [Real.one_rpow, mul_one]
      exact le_rfl
    have hOldPos : ∀ x, 0 < u x := by
      intro x
      exact lt_of_lt_of_le
        (lowerBarrierPlateau_pos s.hκ (sub_pos.mpr hcond.hgap) hDpos x)
        (plateau_le_of_lowerPinnedRaw hu.toLowerPinned x)
    have hanti : Antitone d.fixed.W :=
      d.antitone_of_old_pos_contDiff_one
        s.hlam hu.bare (paperFrozenEllipticSourceBox_of_conditions hcond)
        s.barrier.hχ s.Cmono_small hrouteCmono hu.contDiff_one hOldPos
        hu.bare.antitone
    have hbare : InMonotoneWaveTrapSet (kappa c) 1 d.fixed.W := by
      refine ⟨⟨⟨(d.contDiff_two s.hlam).continuous, ⟨1, ?_⟩⟩, ?_⟩, hanti⟩
      · intro x
        rw [abs_of_nonneg (d.range x).1]
        exact (d.range x).2.trans (upperBarrier_le_M (kappa c) 1 x)
      · intro x
        exact d.range x
    exact ⟨hbare, hlower⟩
  rw [paperNegativePinnedSelfStepMap_eq s hu]
  refine
    { pinned :=
        { uniformTrap :=
            { bare := hpinned.bare
              modulus := ?_ }
          lower := hpinned.lower }
      contDiff_one := (d.contDiff_two s.hlam).of_le (by norm_num) }
  intro x y
  have hraw := abs_sub_le_of_deriv_abs_le_core
    ((d.contDiff_two s.hlam).differentiable (by norm_num))
    (d.deriv_le s.hlam) x y
  exact hraw.trans (mul_le_mul_of_nonneg_right
    (lambda_le_paperNegativePinnedOrbitModulus s) (abs_nonneg _))

section AxiomAudit

#print axioms InLowerPinnedC1UniformModulusMonotoneTrap.set_convex
#print axioms paperNegativePinnedSelfStepData
#print axioms paperNegativePinnedSelfStepMap_mapsTo

end AxiomAudit

end ShenWork.Paper1
