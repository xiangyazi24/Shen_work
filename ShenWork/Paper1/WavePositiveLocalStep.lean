/-
  The genuine whole-line paper Green step on the positive-attraction trap.

  The positive trap is not monotone.  The source Schauder argument and the
  tail-free clamp maximum principles only use the pointwise wave trap, so this
  file records their nonmonotone form and feeds the paper-expanded positive
  super-barrier into the exact implicit step.
-/
import ShenWork.Paper1.WavePaperSuperBarrierPos

open Filter Topology MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

/-- The compact-open source Schauder construction needs only the pointwise
wave trap; spatial monotonicity of the frozen profile is irrelevant. -/
theorem paperFixedSourceMap_exists_fixed_local_of_inWaveTrap_oldData
    (p : CMParams)
    {c lam M κ B H : ℝ} {u Z : ℝ → ℝ}
    (hlam : 0 < lam)
    (hrpκ : κ < greenRootPlus c lam)
    (hrmκ : κ < -greenRootMinus c lam)
    (hκ : 0 ≤ κ) (hM : 0 < M) (hB : 0 ≤ B)
    (hu : InWaveTrapSet κ M u)
    (hZ : PaperFixedSourceOldData κ M Z)
    (hscalar :
      |(-p.χ * p.m)| * M ^ (p.m - 1) * M ^ p.γ *
            greenWeightedMass1 c lam κ * B
        + (1 + |p.χ| * M ^ (p.m - 1) * M ^ p.γ
            + M ^ p.α + |p.χ| * M ^ (p.m + p.γ - 1))
        + lam ≤ B)
    (hHolder :
      Classical.choose
        (paperFixedSourceMap_holder_kernel_of_oldData
          (p := p) (c := c) (lam := lam) (M := M) (κ := κ) (B := B)
          (u := u) (Z := Z)
          hlam hrpκ hrmκ hκ hM hB hu hZ) ≤ H) :
    ∃ R,
      PaperLocalHolderSourceBox κ M (paperWeightedHolderExponent p) B H R ∧
      paperFixedSourceMap p c lam M κ u Z R = R := by
  let holderKernel :=
    paperFixedSourceMap_holder_kernel_of_oldData
      (p := p) (c := c) (lam := lam) (M := M) (κ := κ) (B := B)
      (u := u) (Z := Z)
      hlam hrpκ hrmκ hκ hM hB hu hZ
  let H0 : ℝ := Classical.choose holderKernel
  have hH0 : 0 ≤ H0 := (Classical.choose_spec holderKernel).1
  have hH : 0 ≤ H := hH0.trans hHolder
  let hmap_cont :
      ∀ R,
        PaperLocalHolderSourceBox κ M (paperWeightedHolderExponent p) B H R →
        Continuous (paperFixedSourceMap p c lam M κ u Z R) := by
    intro R hR
    exact paperFixedSourceMap_continuous_of_localSourceBox
      (p := p) (c := c) (lam := lam) (M := M) (κ := κ)
      (β := paperWeightedHolderExponent p) (B := B) (H := H)
      (u := u) (Z := Z) (R := R)
      hlam hB hZ.cont
      (frozenElliptic_continuous p hu.cunif_bdd hu.nonneg)
      (frozenElliptic_deriv_continuous p hu.cunif_bdd hu.nonneg) hR
  let hmap_bound :
      ∀ R,
        PaperLocalHolderSourceBox κ M (paperWeightedHolderExponent p) B H R →
        ∀ x, |paperFixedSourceMap p c lam M κ u Z R x| ≤
          B * upperBarrier κ M x := by
    intro R hR
    have hVbound : ∀ x, |frozenElliptic p u x| ≤ M ^ p.γ := by
      intro x
      rw [abs_of_nonneg (frozenElliptic_nonneg_of_inWaveTrapSet p hu x)]
      exact frozenElliptic_le_rpow_of_inWaveTrapSet p hM hu x
    have hVderiv : ∀ x, |deriv (frozenElliptic p u) x| ≤ M ^ p.γ := by
      intro x
      exact (frozenElliptic_deriv_abs_le p hu.cunif_bdd hu.nonneg x).trans
        (frozenElliptic_le_rpow_of_inWaveTrapSet p hM hu x)
    exact paperFixedSourceMap_bound_of_localSourceBox
      (p := p) (c := c) (lam := lam) (M := M) (κ := κ)
      (β := paperWeightedHolderExponent p) (B := B) (H := H)
      (BV := M ^ p.γ) (BVd := M ^ p.γ)
      (u := u) (Z := Z) (R := R)
      hlam hrpκ hrmκ hκ hM.le hB
      (Real.rpow_nonneg hM.le p.γ) (Real.rpow_nonneg hM.le p.γ)
      hZ.nonneg hZ.le_barrier hVbound hVderiv hscalar hR
  let hmap_holder :
      ∀ R,
        PaperLocalHolderSourceBox κ M (paperWeightedHolderExponent p) B H R →
        ∀ x y,
          |paperFixedSourceMap p c lam M κ u Z R x -
              paperFixedSourceMap p c lam M κ u Z R y| ≤
            H * |x - y| ^ paperWeightedHolderExponent p := by
    intro R hR x y
    have h0 :=
      (Classical.choose_spec holderKernel).2 H (fun _ => 0) R hR x y
    exact h0.trans (mul_le_mul_of_nonneg_right hHolder
      (Real.rpow_nonneg (abs_nonneg _) (paperWeightedHolderExponent p)))
  let hmap :
      ∀ R,
        PaperLocalHolderSourceBox κ M (paperWeightedHolderExponent p) B H R →
        PaperLocalHolderSourceBox κ M (paperWeightedHolderExponent p) B H
          (paperFixedSourceMap p c lam M κ u Z R) := by
    intro R hR
    exact
      { cont := hmap_cont R hR
        bound := hmap_bound R hR
        holder := hmap_holder R hR }
  exact paperLocalHolderSourceBox_exists_fixed
    hM.le hB hH (paperWeightedHolderExponent_pos p)
    (paperFixedSourceMap p c lam M κ u Z) hmap
    (paperFixedSourceMap_continuousOn_of_localBox
      p hlam hB hH (paperWeightedHolderExponent_pos p) hmap_holder)

/-- Nonnegativity of the exact Green profile on the nonmonotone wave trap. -/
theorem paperFixedSource_truncated_ge_zero_local_of_inWaveTrap
    {p : CMParams} {c lam M κ β B H : ℝ} {u Z R : ℝ → ℝ}
    (hlam : 0 < lam) (hM : 0 < M) (hB : 0 ≤ B)
    (hu : InWaveTrapSet κ M u)
    (hR : PaperLocalHolderSourceBox κ M β B H R)
    (hRfix : paperFixedSourceMap p c lam M κ u Z R = R)
    (hZnonneg : ∀ x, 0 ≤ Z x) :
    ∀ x, 0 ≤ greenConv c lam R x := by
  have hR_const : ∀ y, |R y| ≤ B * M := by
    intro y
    calc
      |R y| ≤ B * upperBarrier κ M y := hR.bound y
      _ ≤ B * M :=
        mul_le_mul_of_nonneg_left (upperBarrier_le_M κ M y) hB
  have hHi : ∀ t,
      IntegrableOn (gWeight (greenRootPlus c lam) R) (Ioi t) :=
    fun t => gWeight_integrableOn_Ioi_of_bounded
      (greenRootPlus_pos (c := c) hlam) hR.cont hR_const t
  have hLo : ∀ t,
      IntegrableOn (gWeight (greenRootMinus c lam) R) (Iic t) :=
    fun t => gWeight_integrableOn_Iic_of_bounded
      (greenRootMinus_neg (c := c) hlam) hR.cont hR_const t
  have hstep : ∀ x,
      paperImplicitStepOp_truncated p c (1 / lam) M κ u
          (greenConv c lam R) x = Z x :=
    paperImplicitStepOp_truncated_of_green_fixed_source
      (c := c) (lam := lam) (p := p) (M := M) (κ := κ)
      (u := u) (Z := Z) (R := R) hlam hRfix.symm hR.cont hHi hLo
  have hW2 : ContDiff ℝ 2 (greenConv c lam R) :=
    greenConv_contDiff_two hR.cont hHi hLo
  have hWbound : ∀ x, |greenConv c lam R x| ≤ lam⁻¹ * (B * M) :=
    greenConv_abs_le_of_bound (c := c) (lam := lam)
      hlam hR.cont hR_const
  let C : ℝ := |(-p.χ * p.m)| * M ^ (p.m - 1) * M ^ p.γ
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hcoeff : ∀ x,
      |(-p.χ * p.m) *
          (paperWeightedClamp κ M (greenConv c lam R) x) ^ (p.m - 1) *
            deriv (frozenElliptic p u) x| ≤ C := by
    intro x
    have hpow :
        |(paperWeightedClamp κ M (greenConv c lam R) x) ^ (p.m - 1)| ≤
          M ^ (p.m - 1) :=
      paperWeightedClamp_rpow_abs_le_M hM.le (sub_nonneg.mpr p.hm) x
    have hVd : |deriv (frozenElliptic p u) x| ≤ M ^ p.γ :=
      (frozenElliptic_deriv_abs_le p hu.cunif_bdd hu.nonneg x).trans
        (frozenElliptic_le_rpow_of_inWaveTrapSet p hM hu x)
    dsimp [C]
    rw [abs_mul, abs_mul]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hpow (abs_nonneg (-p.χ * p.m)))
      hVd (abs_nonneg _) (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hM.le _))
  exact paperImplicitStep_truncated_ge_zero_tailfree
    (p := p) (c := c) (lam := lam) (M := M) (κ := κ)
    (A := lam⁻¹ * (B * M)) (C := C) (u := u) (Z := Z)
    (W := greenConv c lam R)
    hlam hM.le hC hstep hW2 hWbound hZnonneg hcoeff

/-- Upper comparison of the exact Green profile on the nonmonotone wave
trap, assuming the actual paper-expanded super-barrier inequality. -/
theorem paperFixedSource_truncated_le_upperBarrier_local_of_inWaveTrap
    {p : CMParams} {c lam M κ β B H : ℝ} {u Z R : ℝ → ℝ}
    (hlam : 0 < lam) (hκ : 0 < κ) (hM : 0 < M) (hB : 0 ≤ B)
    (hu : InWaveTrapSet κ M u)
    (hR : PaperLocalHolderSourceBox κ M β B H R)
    (hRfix : paperFixedSourceMap p c lam M κ u Z R = R)
    (hZupper : ∀ x, Z x ≤ upperBarrier κ M x)
    (hsuper : ∀ x,
      paperWaveOperator p c u (upperBarrier κ M) x ≤ 0) :
    ∀ x, greenConv c lam R x ≤ upperBarrier κ M x := by
  have hR_const : ∀ y, |R y| ≤ B * M := by
    intro y
    calc
      |R y| ≤ B * upperBarrier κ M y := hR.bound y
      _ ≤ B * M :=
        mul_le_mul_of_nonneg_left (upperBarrier_le_M κ M y) hB
  have hHi : ∀ t,
      IntegrableOn (gWeight (greenRootPlus c lam) R) (Ioi t) :=
    fun t => gWeight_integrableOn_Ioi_of_bounded
      (greenRootPlus_pos (c := c) hlam) hR.cont hR_const t
  have hLo : ∀ t,
      IntegrableOn (gWeight (greenRootMinus c lam) R) (Iic t) :=
    fun t => gWeight_integrableOn_Iic_of_bounded
      (greenRootMinus_neg (c := c) hlam) hR.cont hR_const t
  have hstep : ∀ x,
      paperImplicitStepOp_truncated p c (1 / lam) M κ u
          (greenConv c lam R) x = Z x :=
    paperImplicitStepOp_truncated_of_green_fixed_source
      (c := c) (lam := lam) (p := p) (M := M) (κ := κ)
      (u := u) (Z := Z) (R := R) hlam hRfix.symm hR.cont hHi hLo
  have hW2 : ContDiff ℝ 2 (greenConv c lam R) :=
    greenConv_contDiff_two hR.cont hHi hLo
  have hWbound : ∀ x, |greenConv c lam R x| ≤ lam⁻¹ * (B * M) :=
    greenConv_abs_le_of_bound (c := c) (lam := lam)
      hlam hR.cont hR_const
  let C : ℝ := |(-p.χ * p.m)| * M ^ (p.m - 1) * M ^ p.γ
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hcoeff : ∀ x,
      |(-p.χ * p.m) * (upperBarrier κ M x) ^ (p.m - 1) *
          deriv (frozenElliptic p u) x| ≤ C := by
    intro x
    have hbar0 : 0 ≤ upperBarrier κ M x := upperBarrier_nonneg hM.le x
    have hbarM : upperBarrier κ M x ≤ M := upperBarrier_le_M κ M x
    have hpownn : 0 ≤ (upperBarrier κ M x) ^ (p.m - 1) :=
      Real.rpow_nonneg hbar0 _
    have hpow : |(upperBarrier κ M x) ^ (p.m - 1)| ≤ M ^ (p.m - 1) := by
      rw [abs_of_nonneg hpownn]
      exact Real.rpow_le_rpow hbar0 hbarM (sub_nonneg.mpr p.hm)
    have hVd : |deriv (frozenElliptic p u) x| ≤ M ^ p.γ :=
      (frozenElliptic_deriv_abs_le p hu.cunif_bdd hu.nonneg x).trans
        (frozenElliptic_le_rpow_of_inWaveTrapSet p hM hu x)
    dsimp [C]
    rw [abs_mul, abs_mul]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hpow (abs_nonneg (-p.χ * p.m)))
      hVd (abs_nonneg _) (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hM.le _))
  exact paperImplicitStep_truncated_le_upperBarrier_tailfree
    (p := p) (c := c) (lam := lam) (M := M) (κ := κ)
    (A := lam⁻¹ * (B * M)) (C := C) (u := u) (Z := Z)
    (W := greenConv c lam R)
    hlam hκ hM hC hstep hW2 hWbound hZupper hsuper hcoeff

/-- Both spatial clamps are inactive on a nonmonotone positive trap when the
paper-expanded upper barrier has been proved directly. -/
theorem paperFixedSource_truncation_inactive_local_of_inWaveTrap_super
    {p : CMParams} {c lam M κ β B H : ℝ} {u Z R : ℝ → ℝ}
    (hlam : 0 < lam) (hκ : 0 < κ) (hM : 0 < M) (hB : 0 ≤ B)
    (hu : InWaveTrapSet κ M u)
    (hZ : PaperFixedSourceOldData κ M Z)
    (hsuper : ∀ x,
      paperWaveOperator p c u (upperBarrier κ M) x ≤ 0)
    (hR : PaperLocalHolderSourceBox κ M β B H R)
    (hRfix : paperFixedSourceMap p c lam M κ u Z R = R) :
    ∀ x, greenConv c lam R x ∈
      Set.Icc (0 : ℝ) (upperBarrier κ M x) := by
  have hnonneg := paperFixedSource_truncated_ge_zero_local_of_inWaveTrap
    (p := p) (c := c) (lam := lam) (M := M) (κ := κ)
    (u := u) (Z := Z) (R := R)
    hlam hM hB hu hR hRfix hZ.nonneg
  have hupper :=
    paperFixedSource_truncated_le_upperBarrier_local_of_inWaveTrap
      (p := p) (c := c) (lam := lam) (M := M) (κ := κ)
      (u := u) (Z := Z) (R := R)
      hlam hκ hM hB hu hR hRfix hZ.le_barrier hsuper
  exact fun x => ⟨hnonneg x, hupper x⟩

/-- Exact genuine paper step on the nonmonotone positive trap. -/
theorem paperLocalFixedStepData_exists_of_inWaveTrap_oldData_super
    (p : CMParams)
    {c lam M κ Λ B H : ℝ} {u Z : ℝ → ℝ}
    (hlam : 0 < lam)
    (hrpκ : κ < greenRootPlus c lam)
    (hrmκ : κ < -greenRootMinus c lam)
    (hκ : 0 < κ) (hM : 0 < M) (hB : 0 ≤ B)
    (hu : InWaveTrapSet κ M u)
    (hZ : PaperFixedSourceOldData κ M Z)
    (hsourceScalar :
      |(-p.χ * p.m)| * M ^ (p.m - 1) * M ^ p.γ *
            greenWeightedMass1 c lam κ * B
        + (1 + |p.χ| * M ^ (p.m - 1) * M ^ p.γ
            + M ^ p.α + |p.χ| * M ^ (p.m + p.γ - 1))
        + lam ≤ B)
    (hHolder :
      Classical.choose
        (paperFixedSourceMap_holder_kernel_of_oldData
          (p := p) (c := c) (lam := lam) (M := M) (κ := κ) (B := B)
          (u := u) (Z := Z)
          hlam hrpκ hrmκ hκ.le hM hB hu hZ) ≤ H)
    (hsuper : ∀ x,
      paperWaveOperator p c u (upperBarrier κ M) x ≤ 0)
    (hΛ : Λ = 2 * (greenDelta c lam)⁻¹ * (B * M)) :
    ∃ d : PaperLocalFixedStepData p c lam M κ Λ B u Z,
      PaperLocalHolderSourceBox κ M (paperWeightedHolderExponent p) B H
        d.fixed.R := by
  obtain ⟨R, hR, hRfix⟩ :=
    paperFixedSourceMap_exists_fixed_local_of_inWaveTrap_oldData
      p (c := c) (lam := lam) (M := M) (κ := κ) (B := B) (H := H)
      (u := u) (Z := Z)
      hlam hrpκ hrmκ hκ.le hM hB hu hZ hsourceScalar hHolder
  have hIcc : ∀ x, greenConv c lam R x ∈
      Set.Icc (0 : ℝ) (upperBarrier κ M x) :=
    paperFixedSource_truncation_inactive_local_of_inWaveTrap_super
      (p := p) (c := c) (lam := lam) (M := M) (κ := κ)
      (u := u) (Z := Z) (R := R)
      hlam hκ hM hB hu hZ hsuper hR hRfix
  have htrunc :
      paperFixedSourceMap p c lam M κ u Z R =
        paperStepSource p c lam u Z (fun x => greenConv c lam R x) :=
    paperStepSource_truncated_eq_paperStepSource_of_Icc
      (p := p) (c := c) (lam := lam) (M := M) (κ := κ)
      (u := u) (Z := Z) (R := R) hM.le hIcc
  have hsource :
      R = paperStepSource p c lam u Z (fun x => greenConv c lam R x) := by
    calc
      R = paperFixedSourceMap p c lam M κ u Z R := hRfix.symm
      _ = paperStepSource p c lam u Z (fun x => greenConv c lam R x) := htrunc
  have hRbound : ∀ y, |R y| ≤ B * M := by
    intro y
    calc
      |R y| ≤ B * upperBarrier κ M y := hR.bound y
      _ ≤ B * M :=
        mul_le_mul_of_nonneg_left (upperBarrier_le_M κ M y) hB
  let fixed : PaperStepFixedSourceCore p c lam M κ Λ u Z :=
    { R := R
      source_eq := hsource
      R_cont := hR.cont
      R_bound_const := B * M
      R_bound := hRbound
      R_bound_eq := hΛ }
  let d : PaperLocalFixedStepData p c lam M κ Λ B u Z :=
    { fixed := fixed
      range := by
        intro x
        simpa [fixed, PaperStepFixedSourceCore.W] using hIcc x
      sourceWeightedBound := by
        intro x
        simpa [fixed] using hR.bound x }
  exact ⟨d, by simpa [d, fixed] using hR⟩

/-- Positive headline specialization of the nonmonotone exact paper step. -/
theorem paperPositiveLocalFixedStepData_exists
    (p : CMParams)
    {c lam M κ Λ B H : ℝ} {u Z : ℝ → ℝ}
    (hχ0 : 0 ≤ p.χ) (hχ : p.χ < chiStar p)
    (hα : p.α = p.m + p.γ - 1)
    (hκ : 0 < κ) (hκ1 : κ < 1) (hM : 1 ≤ M)
    (hMχ : (1 / (1 - p.χ)) ^ (1 / p.α) ≤ M)
    (hc : c = κ + κ⁻¹)
    (hlam : 0 < lam)
    (hrpκ : κ < greenRootPlus c lam)
    (hrmκ : κ < -greenRootMinus c lam)
    (hB : 0 ≤ B)
    (hu : InWaveTrapSet κ M u)
    (hZ : PaperFixedSourceOldData κ M Z)
    (hsourceScalar :
      |(-p.χ * p.m)| * M ^ (p.m - 1) * M ^ p.γ *
            greenWeightedMass1 c lam κ * B
        + (1 + |p.χ| * M ^ (p.m - 1) * M ^ p.γ
            + M ^ p.α + |p.χ| * M ^ (p.m + p.γ - 1))
        + lam ≤ B)
    (hHolder :
      Classical.choose
        (paperFixedSourceMap_holder_kernel_of_oldData
          (p := p) (c := c) (lam := lam) (M := M) (κ := κ) (B := B)
          (u := u) (Z := Z)
          hlam hrpκ hrmκ hκ.le (lt_of_lt_of_le zero_lt_one hM)
            hB hu hZ) ≤ H)
    (hΛ : Λ = 2 * (greenDelta c lam)⁻¹ * (B * M)) :
    ∃ d : PaperLocalFixedStepData p c lam M κ Λ B u Z,
      PaperLocalHolderSourceBox κ M (paperWeightedHolderExponent p) B H
        d.fixed.R := by
  apply paperLocalFixedStepData_exists_of_inWaveTrap_oldData_super
    p hlam hrpκ hrmκ hκ (lt_of_lt_of_le zero_lt_one hM) hB hu hZ
      hsourceScalar hHolder
  · exact paperWaveOperator_super_barrier_pos
      p hχ0 hχ hα hκ hκ1 hM hMχ hc hu
  · exact hΛ

section AxiomAudit

#print axioms paperFixedSourceMap_exists_fixed_local_of_inWaveTrap_oldData
#print axioms paperFixedSource_truncation_inactive_local_of_inWaveTrap_super
#print axioms paperLocalFixedStepData_exists_of_inWaveTrap_oldData_super
#print axioms paperPositiveLocalFixedStepData_exists

end AxiomAudit

end ShenWork.Paper1
