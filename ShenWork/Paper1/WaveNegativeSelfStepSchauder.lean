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

/-! ## Compactness of the regular image -/

/-- A locally-uniform limit of genuine Green steps with the common first- and
second-derivative bounds is `C¹`.  Only a derivative subsequence is extracted;
the profile limit remains the originally supplied locally-uniform limit. -/
theorem contDiff_one_of_locallyUniform_paperStepAnalytic
    (p : CMParams) (c lam M κ Λ : ℝ)
    (hM : 0 < M) (hΛ : 0 ≤ Λ) (hlam : 0 < lam)
    {us Zs Ws : ℕ → ℝ → ℝ}
    (A : ∀ n, PaperStepAnalytic p c lam M κ Λ (us n) (Zs n) (Ws n))
    (hWs0 : ∀ n x, 0 ≤ Ws n x)
    (hWsM : ∀ n x, Ws n x ≤ M)
    {W : ℝ → ℝ}
    (hW : LocallyUniformConverges Ws W) :
    ContDiff ℝ 1 W ∧
      (∀ x, |deriv W x| ≤ Λ) ∧
      ∃ sub : ℕ → ℕ, StrictMono sub ∧
        LocallyUniformConverges
          (fun n x => deriv (Ws (sub n)) x) (fun x => deriv W x) := by
  let C2 : ℝ := paperStepC2Bound c lam M Λ
  let Q : ℝ := max Λ C2
  have hC2 : 0 ≤ C2 := paperStepC2Bound_nonneg hlam hM.le hΛ
  have hQ : 0 ≤ Q := by
    rcases le_total Λ C2 with h | h
    · simpa [Q, max_eq_right h] using hC2
    · simpa [Q, max_eq_left h] using hΛ
  have hderivLip : ∀ n x y,
      |deriv (Ws n) x - deriv (Ws n) y| ≤ Q * |x - y| := by
    intro n x y
    have hdiff : Differentiable ℝ (fun t => deriv (Ws n) t) :=
      fun t => (paperStep_hasDerivAt_deriv (A n) t).differentiableAt
    have hbound : ∀ t, |deriv (fun z => deriv (Ws n) z) t| ≤ C2 := by
      intro t
      rw [(paperStep_hasDerivAt_deriv (A n) t).deriv]
      exact paperStep_second_deriv_le hlam hM.le hΛ
        (fun z => by
          rw [abs_of_nonneg (hWs0 n z)]
          exact hWsM n z)
        (A n) t
    exact le_trans (abs_sub_le_of_deriv_abs_le_core hdiff hbound x y)
      (mul_le_mul_of_nonneg_right (le_max_right Λ C2) (abs_nonneg _))
  have hderivBdd : ∀ n x, |deriv (Ws n) x| ≤ Q := by
    intro n x
    exact le_trans (paperStep_deriv_le hlam (A n) x) (le_max_left Λ C2)
  obtain ⟨sub, hsub, Dfun, hDpt, hDLip⟩ :=
    helly_pointwise_selection Q (fun n x => deriv (Ws n) x)
      hderivLip hderivBdd
  have hDLU : LocallyUniformConverges
      (fun n x => deriv (Ws (sub n)) x) Dfun :=
    locallyUniform_of_helly_pointwise hQ hDpt hderivLip hDLip
  have hWsub : LocallyUniformConverges (fun n => Ws (sub n)) W :=
    hW.comp_strictMono hsub
  have hWhas : ∀ x, HasDerivAt W (Dfun x) x := by
    intro x
    exact hasDerivAt_of_tendstoLocallyUniformlyOn
      (𝕜 := ℝ) (l := atTop) (s := (Set.univ : Set ℝ))
      (f := fun n => Ws (sub n)) (g := W)
      (f' := fun n x => deriv (Ws (sub n)) x) (g' := Dfun)
      isOpen_univ hDLU.tendstoLocallyUniformlyOn_univ
      (Eventually.of_forall fun n y _hy =>
        paperStep_hasDerivAt_value (A (sub n)) y)
      (fun y _hy => hWsub.tendsto_at y) (Set.mem_univ x)
  have hD_eq : Dfun = fun x => deriv W x := by
    funext x
    exact (hWhas x).deriv.symm
  have hWd : LocallyUniformConverges
      (fun n x => deriv (Ws (sub n)) x) (fun x => deriv W x) := by
    simpa [hD_eq] using hDLU
  have hderivW : ∀ x, |deriv W x| ≤ Λ := by
    intro x
    rw [← congrFun hD_eq x]
    refine le_of_tendsto (hDpt x).abs ?_
    exact Eventually.of_forall fun n => paperStep_deriv_le hlam (A (sub n)) x
  have hDcont : Continuous Dfun :=
    continuous_of_locallyUniform
      (fun n => continuous_iff_continuousAt.mpr fun x =>
        (paperStep_hasDerivAt_deriv (A (sub n)) x).continuousAt)
      hDLU
  have hWdiff : Differentiable ℝ W :=
    fun x => (hWhas x).differentiableAt
  have hWderivCont : Continuous (fun x => deriv W x) := by
    rw [← hD_eq]
    exact hDcont
  exact ⟨contDiff_one_iff_deriv.mpr ⟨hWdiff, hWderivCont⟩,
    hderivW, sub, hsub, hWd⟩

/-- The regular trap is inhabited by the first smooth Green successor of the
kinked upper barrier. -/
theorem paperNegativePinnedC1UniformTrap_nonempty
    {p : CMParams} {c D : ℝ}
    (hcond : PaperLemma42ExactConditions
      p c (kappa c) (negativeBranchTailCap p c) 1)
    (hD : paperDMin p.χ 1 (kappa c) (negativeBranchTailCap p c)
      p.m p.γ c < D)
    (hD1 : 1 ≤ D)
    (s : Paper1NegativeLocalStepScalarData p c D) :
    ∃ u, InLowerPinnedC1UniformModulusMonotoneTrap (kappa c) 1
      (paperNegativePinnedOrbitModulus s)
      (lowerBarrierRaw (kappa c) (negativeBranchTailCap p c) D) u := by
  obtain ⟨u, hu⟩ :=
    paperNegativePinnedUniformModulusTrap_nonempty hcond hD hD1 s
  let st := paperNegativePinnedStepState hcond hD hD1 s u hu.toLowerPinned 0
  refine ⟨st.data.fixed.W, ?_⟩
  refine
    { pinned :=
        { uniformTrap :=
            { bare := st.pinned.bare
              modulus := ?_ }
          lower := st.pinned.lower }
      contDiff_one := (st.data.contDiff_two s.hlam).of_le (by norm_num) }
  intro x y
  have hraw := abs_sub_le_of_deriv_abs_le_core
    ((st.data.contDiff_two s.hlam).differentiable (by norm_num))
    (st.data.deriv_le s.hlam) x y
  exact hraw.trans (mul_le_mul_of_nonneg_right
    (lambda_le_paperNegativePinnedOrbitModulus s) (abs_nonneg _))

/-- The selected self-step map has compact range in the regular trap.  The
base profiles are compact by the uniform modulus; the common Green `C²` bound
restores the `C¹` field in every locally-uniform cluster. -/
theorem paperNegativePinnedSelfStepMap_compactRange
    {p : CMParams} {c D : ℝ}
    (hcond : PaperLemma42ExactConditions
      p c (kappa c) (negativeBranchTailCap p c) 1)
    (hD : paperDMin p.χ 1 (kappa c) (negativeBranchTailCap p c)
      p.m p.γ c < D)
    (hD1 : 1 ≤ D)
    (s : Paper1NegativeLocalStepScalarData p c D) :
    LocalUniformSequentiallyCompactRange
      (InLowerPinnedC1UniformModulusMonotoneTrap (kappa c) 1
        (paperNegativePinnedOrbitModulus s)
        (lowerBarrierRaw (kappa c) (negativeBranchTailCap p c) D))
      (paperNegativePinnedSelfStepMap s) := by
  intro seq hseq
  let Ws : ℕ → ℝ → ℝ := fun n => paperNegativePinnedSelfStepMap s (seq n)
  have hmaps : ∀ n,
      InLowerPinnedC1UniformModulusMonotoneTrap (kappa c) 1
        (paperNegativePinnedOrbitModulus s)
        (lowerBarrierRaw (kappa c) (negativeBranchTailCap p c) D) (Ws n) :=
    fun n => paperNegativePinnedSelfStepMap_mapsTo
      hcond hD hD1 s (hseq n)
  obtain ⟨sub, hsub, W, hWpinned, hconv⟩ :=
    InLowerPinnedUniformModulusMonotoneTrap.locallyUniform_sequentiallyCompact
      (κ := kappa c) zero_le_one
      (paperNegativePinnedOrbitModulus_nonneg s) Ws
      (fun n => (hmaps n).pinned)
  let us : ℕ → ℝ → ℝ := fun n => seq (sub n)
  let As : ∀ n, PaperStepAnalytic p c s.lam 1 (kappa c) s.Λ
      (us n) (us n) (Ws (sub n)) := fun n => by
    rw [show Ws (sub n) =
        (paperNegativePinnedSelfStepData s (hseq (sub n))).fixed.W by
      exact paperNegativePinnedSelfStepMap_eq s (hseq (sub n))]
    exact paperStepAnalytic_of_core s.hlam
      (paperNegativePinnedSelfStepData s (hseq (sub n))).fixed.analyticCore
  have hconv' : LocallyUniformConverges (fun n => Ws (sub n)) W := hconv
  have hW1 : ContDiff ℝ 1 W :=
    (contDiff_one_of_locallyUniform_paperStepAnalytic
      p c s.lam 1 (kappa c) s.Λ one_pos s.hΛ0 s.hlam As
      (fun n x => (hmaps (sub n)).bare.nonneg x)
      (fun n x => (hmaps (sub n)).bare.le_M x) hconv').1
  exact ⟨sub, hsub, W, ⟨hWpinned, hW1⟩, by simpa [Ws] using hconv⟩

section AxiomAudit

#print axioms InLowerPinnedC1UniformModulusMonotoneTrap.set_convex
#print axioms paperNegativePinnedSelfStepData
#print axioms paperNegativePinnedSelfStepMap_mapsTo
#print axioms contDiff_one_of_locallyUniform_paperStepAnalytic
#print axioms paperNegativePinnedC1UniformTrap_nonempty
#print axioms paperNegativePinnedSelfStepMap_compactRange

end AxiomAudit

end ShenWork.Paper1
