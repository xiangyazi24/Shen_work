/- Direct compact-convex Schauder map for the positive-attraction branch. -/
import ShenWork.Paper1.WavePositiveParameters
import ShenWork.Paper1.WaveNegativeSelfStepSchauder

open Filter Set Topology Real

noncomputable section

namespace ShenWork.Paper1

structure InLowerPinnedC1UniformModulusWaveTrap
    (κ M L : ℝ) (φ u : ℝ → ℝ) : Prop where
  bare : InWaveTrapSet κ M u
  modulus : ∀ x y, |u x - u y| ≤ L * |x - y|
  lower : ∀ x, φ x ≤ u x
  contDiff_one : ContDiff ℝ 1 u

namespace InLowerPinnedC1UniformModulusWaveTrap

variable {κ M L : ℝ} {φ u : ℝ → ℝ}

theorem set_convex (κ M L : ℝ) (φ : ℝ → ℝ) :
    Convex ℝ {u : ℝ → ℝ |
      InLowerPinnedC1UniformModulusWaveTrap κ M L φ u} := by
  rw [convex_iff_add_mem]
  intro u hu v hv a b ha hb hab
  refine
    { bare := (InWaveTrapSet.set_convex κ M) hu.bare hv.bare ha hb hab
      modulus := ?_
      lower := ?_
      contDiff_one :=
        (hu.contDiff_one.const_smul a).add (hv.contDiff_one.const_smul b) }
  · intro x y
    change |(a * u x + b * v x) - (a * u y + b * v y)| ≤ L * |x - y|
    calc
      |(a * u x + b * v x) - (a * u y + b * v y)| =
          |a * (u x - u y) + b * (v x - v y)| := by ring_nf
      _ ≤ |a * (u x - u y)| + |b * (v x - v y)| := abs_add_le _ _
      _ = a * |u x - u y| + b * |v x - v y| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * (L * |x - y|) + b * (L * |x - y|) :=
        add_le_add (mul_le_mul_of_nonneg_left (hu.modulus x y) ha)
          (mul_le_mul_of_nonneg_left (hv.modulus x y) hb)
      _ = L * |x - y| := by rw [← add_mul, hab, one_mul]
  · intro x
    calc
      φ x = (a + b) * φ x := by rw [hab, one_mul]
      _ = a * φ x + b * φ x := by ring
      _ ≤ a * u x + b * v x :=
        add_le_add
          (mul_le_mul_of_nonneg_left
            (InLowerPinnedC1UniformModulusWaveTrap.lower hu x) ha)
          (mul_le_mul_of_nonneg_left
            (InLowerPinnedC1UniformModulusWaveTrap.lower hv x) hb)

theorem boundedConvexProfileTrapData
    (hne : ∃ u, InLowerPinnedC1UniformModulusWaveTrap κ M L φ u) :
    BoundedConvexProfileTrapData
      (InLowerPinnedC1UniformModulusWaveTrap κ M L φ) M := by
  refine
    { nonempty := hne
      convex := set_convex κ M L φ
      continuous := fun _ hu => hu.contDiff_one.continuous
      abs_le := ?_ }
  intro u hu x
  rw [abs_of_nonneg (hu.bare.nonneg x)]
  exact hu.bare.le_M x

/-- Uniform modulus, pointwise trap bounds, and the closed lower pin are
compact in the compact-open topology. -/
theorem locallyUniform_sequentiallyCompact
    (hM : 0 ≤ M) (hL : 0 ≤ L)
    {seq : ℕ → ℝ → ℝ}
    (hseq : ∀ n, InLowerPinnedC1UniformModulusWaveTrap κ M L φ (seq n)) :
    ∃ sub : ℕ → ℕ, StrictMono sub ∧ ∃ g,
      InWaveTrapSet κ M g ∧
      (∀ x y, |g x - g y| ≤ L * |x - y|) ∧
      (∀ x, φ x ≤ g x) ∧
      LocallyUniformConverges (fun n => seq (sub n)) g := by
  let Q : ℝ := max M L
  have hQ : 0 ≤ Q := le_trans hM (le_max_left M L)
  have hLipQ : ∀ n x y, |seq n x - seq n y| ≤ Q * |x - y| := by
    intro n x y
    exact (hseq n).modulus x y |>.trans
      (mul_le_mul_of_nonneg_right (le_max_right M L) (abs_nonneg _))
  have hBddQ : ∀ n x, |seq n x| ≤ Q := by
    intro n x
    rw [abs_of_nonneg ((hseq n).bare.nonneg x)]
    exact (hseq n).bare.le_M x |>.trans (le_max_left M L)
  obtain ⟨sub, hsub, g, hpt, hgQ⟩ :=
    helly_pointwise_selection Q seq hLipQ hBddQ
  have hLU : LocallyUniformConverges (fun n => seq (sub n)) g :=
    locallyUniform_of_helly_pointwise hQ hpt hLipQ hgQ
  have hnn : ∀ x, 0 ≤ g x := fun x =>
    hLU.nonneg_of_forall_nonneg (fun n => (hseq (sub n)).bare.nonneg x)
  have hbar : ∀ x, g x ≤ upperBarrier κ M x := fun x =>
    hLU.le_of_forall_le (fun n => (hseq (sub n)).bare.le_upperBarrier x)
  have hgcont : Continuous g := continuous_of_locallyUniform
    (fun n => (hseq (sub n)).bare.cunif_bdd.1) hLU
  have hgbdd : IsBddFun g := by
    refine ⟨M, fun x => ?_⟩
    rw [abs_of_nonneg (hnn x)]
    exact (hbar x).trans (upperBarrier_le_M κ M x)
  have hmod : ∀ x y, |g x - g y| ≤ L * |x - y| := by
    intro x y
    exact le_of_tendsto ((hpt x).sub (hpt y) |>.abs)
      (Eventually.of_forall fun n => (hseq (sub n)).modulus x y)
  have hlower : ∀ x, φ x ≤ g x := by
    intro x
    exact le_of_tendsto_of_tendsto tendsto_const_nhds (hLU.tendsto_at x)
      (Eventually.of_forall fun n => (hseq (sub n)).lower x)
  exact ⟨sub, hsub, g, ⟨⟨hgcont, hgbdd⟩, fun x => ⟨hnn x, hbar x⟩⟩,
    hmod, hlower, hLU⟩

end InLowerPinnedC1UniformModulusWaveTrap

def paperPositiveSelfStepModulus
    {p : CMParams} {c D : ℝ} (s : Paper1PositiveLocalStepScalarData p c D) : ℝ :=
  max 1 s.Λ

theorem paperPositiveSelfStepModulus_nonneg
    {p : CMParams} {c D : ℝ} (s : Paper1PositiveLocalStepScalarData p c D) :
    0 ≤ paperPositiveSelfStepModulus s :=
  le_trans zero_le_one (le_max_left 1 s.Λ)

theorem paperPositiveSelfStepModulus_ge_lambda
    {p : CMParams} {c D : ℝ} (s : Paper1PositiveLocalStepScalarData p c D) :
    s.Λ ≤ paperPositiveSelfStepModulus s := le_max_right 1 s.Λ

def paperFixedSourceOldData_of_positiveC1Trap
    {κ M L : ℝ} {φ u : ℝ → ℝ} (hL : 0 ≤ L)
    (hu : InLowerPinnedC1UniformModulusWaveTrap κ M L φ u) :
    PaperFixedSourceOldData κ M u :=
  { cont := hu.bare.cunif_bdd.1
    nonneg := hu.bare.nonneg
    le_barrier := hu.bare.le_upperBarrier
    L := L
    L_nonneg := hL
    local_lip := fun x y _ => hu.modulus x y }

/-- Select a genuine positive Green step for arbitrary admissible frozen and
old profiles. -/
noncomputable def paperPositiveSelectedStepData
    {p : CMParams} {c D : ℝ}
    (hcond : PositivePaperLemma42ExactConditions p c (kappa c)
      (positiveBranchTailCap p c) (MChi p))
    (s : Paper1PositiveLocalStepScalarData p c D)
    {u Z : ℝ → ℝ} (hu : InWaveTrapSet (kappa c) (MChi p) u)
    (hZ : PaperFixedSourceOldData (kappa c) (MChi p) Z) :
    PaperLocalFixedStepData p c s.lam (MChi p) (kappa c) s.Λ s.B u Z := by
  let holderKernel := paperFixedSourceMap_holder_kernel_of_oldData
    (p := p) (c := c) (lam := s.lam) (M := MChi p) (κ := kappa c)
    (B := s.B) (u := u) (Z := Z) s.hlam s.hrpκ s.hrmκ hcond.hκ0.le
    (lt_of_lt_of_le zero_lt_one hcond.hM) s.hB hu hZ
  let H : ℝ := Classical.choose holderKernel
  exact Classical.choose (paperPositiveLocalFixedStepData_exists
    p hcond.hχ_nonneg
    (lt_of_lt_of_le hcond.hχ_small (min_le_right _ _)) hcond.hα_eq
    hcond.hκ0 hcond.hκ1 hcond.hM
    (le_of_eq (MChi_eq_rpow_of_chi_nonneg_lt_one p hcond.hχ_nonneg
      (lt_of_lt_of_le hcond.hχ_small
        (le_trans (min_le_left _ _) (by norm_num)))).symm)
    hcond.hc s.hlam s.hrpκ s.hrmκ s.hB hu hZ s.sourceScalar le_rfl s.hΛ)

noncomputable def paperPositiveSelfStepData
    {p : CMParams} {c D : ℝ}
    (hcond : PositivePaperLemma42ExactConditions p c (kappa c)
      (positiveBranchTailCap p c) (MChi p))
    (s : Paper1PositiveLocalStepScalarData p c D)
    {u : ℝ → ℝ}
    (hu : InLowerPinnedC1UniformModulusWaveTrap (kappa c) (MChi p)
      (paperPositiveSelfStepModulus s)
      (lowerBarrierPlateau (kappa c) (positiveBranchTailCap p c) D) u) :
    PaperLocalFixedStepData p c s.lam (MChi p) (kappa c) s.Λ s.B u u :=
  paperPositiveSelectedStepData hcond s hu.bare
    (paperFixedSourceOldData_of_positiveC1Trap
      (paperPositiveSelfStepModulus_nonneg s) hu)

noncomputable def paperPositiveSelfStepMap
    {p : CMParams} {c D : ℝ}
    (hcond : PositivePaperLemma42ExactConditions p c (kappa c)
      (positiveBranchTailCap p c) (MChi p))
    (s : Paper1PositiveLocalStepScalarData p c D) :
    (ℝ → ℝ) → ℝ → ℝ := fun u => by
  classical
  exact if hu : InLowerPinnedC1UniformModulusWaveTrap (kappa c) (MChi p)
      (paperPositiveSelfStepModulus s)
      (lowerBarrierPlateau (kappa c) (positiveBranchTailCap p c) D) u then
    (paperPositiveSelfStepData hcond s hu).fixed.W
  else upperBarrier (kappa c) (MChi p)

@[simp] theorem paperPositiveSelfStepMap_eq
    {p : CMParams} {c D : ℝ}
    (hcond : PositivePaperLemma42ExactConditions p c (kappa c)
      (positiveBranchTailCap p c) (MChi p))
    (s : Paper1PositiveLocalStepScalarData p c D) {u : ℝ → ℝ}
    (hu : InLowerPinnedC1UniformModulusWaveTrap (kappa c) (MChi p)
      (paperPositiveSelfStepModulus s)
      (lowerBarrierPlateau (kappa c) (positiveBranchTailCap p c) D) u) :
    paperPositiveSelfStepMap hcond s u =
      (paperPositiveSelfStepData hcond s hu).fixed.W := by
  simp [paperPositiveSelfStepMap, hu]

/-- The chosen positive plateau belongs to the nonmonotone pointwise trap. -/
theorem positivePlateau_mem_InWaveTrapSet
    {p : CMParams} {c D : ℝ}
    (hcond : PositivePaperLemma42ExactConditions p c (kappa c)
      (positiveBranchTailCap p c) (MChi p))
    (hD1 : 1 ≤ D)
    (hplateau : ∀ x, lowerBarrierPlateau (kappa c)
      (positiveBranchTailCap p c) D x ≤ paper1PositivePlateauFloor p) :
    InWaveTrapSet (kappa c) (MChi p)
      (lowerBarrierPlateau (kappa c) (positiveBranchTailCap p c) D) := by
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD1
  have hgap : 0 < positiveBranchTailCap p c - kappa c :=
    sub_pos.mpr hcond.hgap
  refine ⟨lowerBarrierPlateau_cunif_bdd hcond.hκ0 hgap hDpos, ?_⟩
  intro x
  refine ⟨(lowerBarrierPlateau_pos hcond.hκ0 hgap hDpos x).le, ?_⟩
  unfold upperBarrier
  apply le_min
  · exact (hplateau x).trans ((min_le_left _ _).trans hcond.hM)
  · exact lowerBarrierPlateau_le_exp hcond.hκ0.le hDpos.le x

/-- A selected positive Green step is above the plateau.  Its Green derivative
bound is first compared with the upper barrier and then with the plateau, so
the proof does not assume the conclusion. -/
theorem PaperLocalFixedStepData.ge_positivePlateau
    {p : CMParams} {c D : ℝ}
    (hcond : PositivePaperLemma42ExactConditions p c (kappa c)
      (positiveBranchTailCap p c) (MChi p))
    (hD : paperDMin p.χ (MChi p) (kappa c)
      (positiveBranchTailCap p c) p.m p.γ c < D)
    (hD1 : 1 ≤ D)
    (hplateau : ∀ x, lowerBarrierPlateau (kappa c)
      (positiveBranchTailCap p c) D x ≤ paper1PositivePlateauFloor p)
    (s : Paper1PositiveLocalStepScalarData p c D)
    {u Z : ℝ → ℝ}
    (hu : InWaveTrapSet (kappa c) (MChi p) u)
    (hprev : ∀ x, lowerBarrierPlateau (kappa c)
      (positiveBranchTailCap p c) D x ≤ Z x)
    (d : PaperLocalFixedStepData p c s.lam (MChi p) (kappa c)
      s.Λ s.B u Z) :
    ∀ x, lowerBarrierPlateau (kappa c)
      (positiveBranchTailCap p c) D x ≤ d.fixed.W x := by
  let K : ℝ := paperLowerPinnedStepLogSlopeCoeff c s.lam (kappa c)
    (positiveBranchTailCap p c) D (MChi p) s.B
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD1
  have hMpos : 0 < MChi p := lt_of_lt_of_le zero_lt_one hcond.hM
  have hK : 0 ≤ K := paperLowerPinnedStepLogSlopeCoeff_nonneg
    s.hlam s.hrpκ s.hrmκ hcond.hκ0 (sub_pos.mpr hcond.hgap)
    hDpos hMpos.le s.hB
  have hWupper : ∀ x, |deriv d.fixed.W x| ≤
      K * lowerBarrierPlateau (kappa c) (positiveBranchTailCap p c) D x := by
    intro x
    have hd := d.deriv_abs_le_weighted_barrier s.hlam s.hrpκ s.hrmκ
      hcond.hκ0.le hMpos.le s.hB x
    have hratio := upperBarrier_le_lowerPinnedBarrierRatio_mul_plateau
      hcond.hκ0 (sub_pos.mpr hcond.hgap) hDpos hMpos.le x
    have hcoeff0 := d.weightedDerivCoeff_nonneg
      s.hlam s.hrpκ s.hrmκ s.hB
    calc
      |deriv d.fixed.W x| ≤
          d.weightedDerivCoeff c s.lam (kappa c) *
            upperBarrier (kappa c) (MChi p) x := hd
      _ ≤ d.weightedDerivCoeff c s.lam (kappa c) *
          (lowerPinnedBarrierRatio (kappa c) (positiveBranchTailCap p c) D
            (MChi p) * lowerBarrierPlateau (kappa c)
              (positiveBranchTailCap p c) D x) :=
        mul_le_mul_of_nonneg_left hratio hcoeff0
      _ = K * lowerBarrierPlateau (kappa c)
          (positiveBranchTailCap p c) D x := by
        unfold K paperLowerPinnedStepLogSlopeCoeff
          PaperLocalFixedStepData.weightedDerivCoeff
        ring
  exact paperImplicitStep_ge_lowerBarrierPlateau_positive_tailfree
    p hcond hD hD1
    (lt_of_lt_of_le hcond.hχ_small (min_le_left _ _)) hplateau
    s.hlam hu hprev (d.step_op s.hlam) (d.contDiff_two s.hlam)
    (fun x => ⟨(d.range x).1,
      (d.range x).2.trans (upperBarrier_le_M _ _ _)⟩)
    hK hWupper (by simpa [K] using s.plateauStep_small)

/-- The selected self step maps the compact-convex positive trap into itself. -/
theorem paperPositiveSelfStepMap_mapsTo
    {p : CMParams} {c D : ℝ}
    (hcond : PositivePaperLemma42ExactConditions p c (kappa c)
      (positiveBranchTailCap p c) (MChi p))
    (hD : paperDMin p.χ (MChi p) (kappa c)
      (positiveBranchTailCap p c) p.m p.γ c < D)
    (hD1 : 1 ≤ D)
    (hplateau : ∀ x, lowerBarrierPlateau (kappa c)
      (positiveBranchTailCap p c) D x ≤ paper1PositivePlateauFloor p)
    (s : Paper1PositiveLocalStepScalarData p c D) {u : ℝ → ℝ}
    (hu : InLowerPinnedC1UniformModulusWaveTrap (kappa c) (MChi p)
      (paperPositiveSelfStepModulus s)
      (lowerBarrierPlateau (kappa c) (positiveBranchTailCap p c) D) u) :
    InLowerPinnedC1UniformModulusWaveTrap (kappa c) (MChi p)
      (paperPositiveSelfStepModulus s)
      (lowerBarrierPlateau (kappa c) (positiveBranchTailCap p c) D)
      (paperPositiveSelfStepMap hcond s u) := by
  let d := paperPositiveSelfStepData hcond s hu
  have hlower := d.ge_positivePlateau hcond hD hD1 hplateau s hu.bare hu.lower
  rw [paperPositiveSelfStepMap_eq hcond s hu]
  refine
    { bare := ?_
      modulus := ?_
      lower := hlower
      contDiff_one := (d.contDiff_two s.hlam).of_le (by norm_num) }
  · refine ⟨⟨(d.contDiff_two s.hlam).continuous, ⟨MChi p, ?_⟩⟩, d.range⟩
    intro x
    rw [abs_of_nonneg (d.range x).1]
    exact (d.range x).2.trans (upperBarrier_le_M _ _ _)
  · intro x y
    have hraw := abs_sub_le_of_deriv_abs_le_core
      ((d.contDiff_two s.hlam).differentiable (by norm_num))
      (d.deriv_le s.hlam) x y
    exact hraw.trans (mul_le_mul_of_nonneg_right
      (paperPositiveSelfStepModulus_ge_lambda s) (abs_nonneg _))

/-- The positive regular trap is inhabited by the first genuine Green step
from the canonical upper barrier. -/
theorem paperPositiveC1UniformTrap_nonempty
    {p : CMParams} {c D : ℝ}
    (hcond : PositivePaperLemma42ExactConditions p c (kappa c)
      (positiveBranchTailCap p c) (MChi p))
    (hD : paperDMin p.χ (MChi p) (kappa c)
      (positiveBranchTailCap p c) p.m p.γ c < D)
    (hD1 : 1 ≤ D)
    (hplateau : ∀ x, lowerBarrierPlateau (kappa c)
      (positiveBranchTailCap p c) D x ≤ paper1PositivePlateauFloor p)
    (s : Paper1PositiveLocalStepScalarData p c D) :
    ∃ u, InLowerPinnedC1UniformModulusWaveTrap (kappa c) (MChi p)
      (paperPositiveSelfStepModulus s)
      (lowerBarrierPlateau (kappa c) (positiveBranchTailCap p c) D) u := by
  let Ubar := upperBarrier (kappa c) (MChi p)
  have hUbar : InWaveTrapSet (kappa c) (MChi p) Ubar :=
    upperBarrier_mem_InWaveTrapSet (le_trans zero_le_one hcond.hM)
  have hsuper : ∀ x, paperWaveOperator p c Ubar Ubar x ≤ 0 :=
    paperWaveOperator_super_barrier_pos p hcond.hχ_nonneg
      (lt_of_lt_of_le hcond.hχ_small (min_le_right _ _)) hcond.hα_eq
      hcond.hκ0 hcond.hκ1 hcond.hM
      (le_of_eq (MChi_eq_rpow_of_chi_nonneg_lt_one p hcond.hχ_nonneg
        (lt_of_lt_of_le hcond.hχ_small
          (le_trans (min_le_left _ _) (by norm_num)))).symm)
      hcond.hc hUbar
  let base : PaperIterateBase p c (kappa c) (MChi p) Ubar Ubar :=
    upperBarrier_paperIterateBase hcond.hκ0.le
      (le_trans zero_le_one hcond.hM) hsuper
  let oldData := base.toFixedSourceOldData hcond.hκ0.le
    (le_trans zero_le_one hcond.hM)
  let d := paperPositiveSelectedStepData hcond s hUbar oldData
  have hplatTrap := positivePlateau_mem_InWaveTrapSet hcond hD1 hplateau
  have hlower := d.ge_positivePlateau hcond hD hD1 hplateau s hUbar
    hplatTrap.le_upperBarrier
  refine ⟨d.fixed.W, ?_⟩
  refine
    { bare := ?_
      modulus := ?_
      lower := hlower
      contDiff_one := (d.contDiff_two s.hlam).of_le (by norm_num) }
  · refine ⟨⟨(d.contDiff_two s.hlam).continuous, ⟨MChi p, ?_⟩⟩, d.range⟩
    intro x
    rw [abs_of_nonneg (d.range x).1]
    exact (d.range x).2.trans (upperBarrier_le_M _ _ _)
  · intro x y
    exact (abs_sub_le_of_deriv_abs_le_core
      ((d.contDiff_two s.hlam).differentiable (by norm_num))
      (d.deriv_le s.hlam) x y).trans
        (mul_le_mul_of_nonneg_right
          (paperPositiveSelfStepModulus_ge_lambda s) (abs_nonneg _))

/-- The selected positive self-step map has compact range in the compact-open
topology; the common Green second-derivative estimate restores the `C¹` field
of every cluster. -/
theorem paperPositiveSelfStepMap_compactRange
    {p : CMParams} {c D : ℝ}
    (hcond : PositivePaperLemma42ExactConditions p c (kappa c)
      (positiveBranchTailCap p c) (MChi p))
    (hD : paperDMin p.χ (MChi p) (kappa c)
      (positiveBranchTailCap p c) p.m p.γ c < D)
    (hD1 : 1 ≤ D)
    (hplateau : ∀ x, lowerBarrierPlateau (kappa c)
      (positiveBranchTailCap p c) D x ≤ paper1PositivePlateauFloor p)
    (s : Paper1PositiveLocalStepScalarData p c D) :
    LocalUniformSequentiallyCompactRange
      (InLowerPinnedC1UniformModulusWaveTrap (kappa c) (MChi p)
        (paperPositiveSelfStepModulus s)
        (lowerBarrierPlateau (kappa c) (positiveBranchTailCap p c) D))
      (paperPositiveSelfStepMap hcond s) := by
  intro seq hseq
  let Ws : ℕ → ℝ → ℝ := fun n => paperPositiveSelfStepMap hcond s (seq n)
  have hmaps : ∀ n,
      InLowerPinnedC1UniformModulusWaveTrap (kappa c) (MChi p)
        (paperPositiveSelfStepModulus s)
        (lowerBarrierPlateau (kappa c) (positiveBranchTailCap p c) D) (Ws n) :=
    fun n => paperPositiveSelfStepMap_mapsTo hcond hD hD1 hplateau s (hseq n)
  obtain ⟨sub, hsub, W, hWbare, hWmod, hWlower, hconv⟩ :=
    InLowerPinnedC1UniformModulusWaveTrap.locallyUniform_sequentiallyCompact
      (le_trans zero_le_one hcond.hM) (paperPositiveSelfStepModulus_nonneg s)
      hmaps
  let us : ℕ → ℝ → ℝ := fun n => seq (sub n)
  let As : ∀ n, PaperStepAnalytic p c s.lam (MChi p) (kappa c) s.Λ
      (us n) (us n) (Ws (sub n)) := fun n => by
    rw [show Ws (sub n) =
        (paperPositiveSelfStepData hcond s (hseq (sub n))).fixed.W by
      exact paperPositiveSelfStepMap_eq hcond s (hseq (sub n))]
    exact paperStepAnalytic_of_core s.hlam
      (paperPositiveSelfStepData hcond s (hseq (sub n))).fixed.analyticCore
  have hW1 : ContDiff ℝ 1 W :=
    (contDiff_one_of_locallyUniform_paperStepAnalytic
      p c s.lam (MChi p) (kappa c) s.Λ
      (lt_of_lt_of_le zero_lt_one hcond.hM) s.hΛ0 s.hlam As
      (fun n x => (hmaps (sub n)).bare.nonneg x)
      (fun n x => (hmaps (sub n)).bare.le_M x) hconv).1
  exact ⟨sub, hsub, W, ⟨hWbare, hWmod, hWlower, hW1⟩,
    by simpa [Ws] using hconv⟩

section AxiomAudit

#print axioms InLowerPinnedC1UniformModulusWaveTrap.set_convex
#print axioms paperPositiveSelectedStepData
#print axioms PaperLocalFixedStepData.ge_positivePlateau
#print axioms paperPositiveSelfStepMap_mapsTo
#print axioms paperPositiveC1UniformTrap_nonempty
#print axioms paperPositiveSelfStepMap_compactRange

end AxiomAudit

end ShenWork.Paper1
