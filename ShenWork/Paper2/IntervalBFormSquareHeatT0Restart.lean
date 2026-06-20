import ShenWork.Paper2.IntervalBFormLinearDriftComparisonRegularDischarge

open Filter Topology Set

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceData conjugatePicardLimit)
open ShenWork.IntervalMildPicardThreshold
  (unitClip_of_mem)

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

/-- Shift a two-variable field from the original time `τ` to restart time `s`. -/
def restartTimeShift (τ : ℝ) (F : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun s x => F (τ + s) x

/-- The squared heat barrier viewed on the restarted strip. -/
def restartedSquareHeatBarrier (τ M : ℝ) (f : ℝ → ℝ) : ℝ → ℝ → ℝ :=
  restartTimeShift τ (squareHeatBarrier M f)

/-- The t>0 residual identity for the squared heat barrier on a restarted
strip.  This deliberately has no `s = 0` trace field: the comparison initial
condition is supplied separately at the positive original time `τ`. -/
structure SquareHeatRestartCalculus
    (L τ M : ℝ) (f : ℝ → ℝ) (B C : ℝ → ℝ → ℝ) : Prop where
  residual_eq :
    ∀ s x, 0 < s → s < L → x ∈ Set.Ioo (0 : ℝ) 1 →
      neumannLinearDriftResidual
          (restartTimeShift τ B) (restartTimeShift τ C)
          (restartedSquareHeatBarrier τ M f) s x =
        Real.exp (-M * (τ + s)) *
          squareHeatResidualCore M (B (τ + s) x) (C (τ + s) x)
            (ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
              (τ + s) f x)
            (deriv (fun z : ℝ =>
              ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
                (τ + s) f z) x)

/-- The complete regular comparison package needed on one restarted strip. -/
structure SquareHeatRestartStripData
    (L τ A D M : ℝ) (f : ℝ → ℝ) (B C u : ℝ → ℝ → ℝ) : Prop where
  length_pos : 0 < L
  coeff :
    NeumannLinearDriftCoefficientsRegular L
      (restartTimeShift τ B) (restartTimeShift τ C)
  super :
    IsClassicalNeumannLinearDriftSuperSolution L
      (restartTimeShift τ B) (restartTimeShift τ C)
      (restartTimeShift τ u)
  barrier_reg :
    NeumannLinearDriftSubSolutionRegularity L
      (restartTimeShift τ B) (restartTimeShift τ C)
      (restartedSquareHeatBarrier τ M f)
  calculus : SquareHeatRestartCalculus L τ M f B C
  M_bound : A ^ 2 / 2 + D ≤ M
  drift_bound :
    ∀ s x, 0 < s → s < L → x ∈ Set.Ioo (0 : ℝ) 1 →
      |B (τ + s) x| ≤ A
  reaction_neg_bound :
    ∀ s x, 0 < s → s < L → x ∈ Set.Ioo (0 : ℝ) 1 →
      -C (τ + s) x ≤ D
  initial :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      squareHeatBarrier M f τ x ≤ u τ x

/-- Local positive-time semigroup facts sufficient to assemble the restarted
squared barrier.  The time trace is the shifted map `s ↦ S(τ+s)f`; no field
mentions the degenerate value of `S(0)`. -/
structure SquareHeatRestartDerivativeData
    (L τ M : ℝ) (f : ℝ → ℝ) : Prop where
  continuousOn_rect :
    ContinuousOn (fun p : ℝ × ℝ => restartedSquareHeatBarrier τ M f p.1 p.2)
      (Set.Icc (0 : ℝ) L ×ˢ Set.Icc (0 : ℝ) 1)
  time_hasDerivAt :
    ∀ ⦃s x : ℝ⦄,
      0 < s → s < L → x ∈ Set.Icc (0 : ℝ) 1 →
        HasDerivAt
          (fun r : ℝ =>
            ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
              (τ + r) f x)
          (deriv (fun r : ℝ =>
            ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
              (τ + r) f x) s) s
  space_hasDerivAt :
    ∀ ⦃s x : ℝ⦄,
      0 < s → s < L → x ∈ Set.Icc (0 : ℝ) 1 →
        HasDerivAt
          (fun y : ℝ =>
            ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
              (τ + s) f y)
          (deriv (fun y : ℝ =>
            ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
              (τ + s) f y) x) x
  space_second_hasDerivAt :
    ∀ ⦃s x : ℝ⦄,
      0 < s → s < L → x ∈ Set.Ioo (0 : ℝ) 1 →
        HasDerivAt
          (fun y : ℝ =>
            deriv (fun z : ℝ =>
              ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
                (τ + s) f z) y)
          (deriv (fun y : ℝ =>
            deriv (fun z : ℝ =>
              ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
                (τ + s) f z) y) x) x
  heat_eq :
    ∀ ⦃s x : ℝ⦄,
      0 < s → s < L → x ∈ Set.Ioo (0 : ℝ) 1 →
        deriv (fun r : ℝ =>
          ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
            (τ + r) f x) s =
          deriv (fun y : ℝ =>
            deriv (fun z : ℝ =>
              ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
                (τ + s) f z) y) x
  neumann :
    ∀ s, 0 < s → s < L →
      deriv (fun x : ℝ =>
        ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
          (τ + s) f x) 0 = 0 ∧
      deriv (fun x : ℝ =>
        ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
          (τ + s) f x) 1 = 0
  bounded : BoundedOnIntervalStrip L (restartedSquareHeatBarrier τ M f)

private theorem restartedSquareHeatBarrier_time_hasDerivAt
    {τ M : ℝ} {f : ℝ → ℝ} {s x : ℝ}
    (hS :
      HasDerivAt
        (fun r : ℝ =>
          ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
            (τ + r) f x)
        (deriv (fun r : ℝ =>
          ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
            (τ + r) f x) s) s) :
    HasDerivAt (fun r : ℝ => restartedSquareHeatBarrier τ M f r x)
      (Real.exp (-M * (τ + s)) *
        (-M *
          (ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
            (τ + s) f x) ^ 2 +
          2 *
            ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
              (τ + s) f x *
            deriv (fun r : ℝ =>
              ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
                (τ + r) f x) s)) s := by
  have hinner :
      HasDerivAt (fun r : ℝ => -M * (τ + r)) (-M) s := by
    convert (((hasDerivAt_const (x := s) (c := τ)).add
      (hasDerivAt_id s)).const_mul (-M)) using 1
    ring
  have hE :
      HasDerivAt (fun r : ℝ => Real.exp (-M * (τ + r)))
        (Real.exp (-M * (τ + s)) * (-M)) s := by
    simpa using (Real.hasDerivAt_exp (-M * (τ + s))).comp s hinner
  have hSq := hS.mul hS
  have h := hE.mul hSq
  convert h using 1
  · ext r
    simp [restartedSquareHeatBarrier, restartTimeShift, squareHeatBarrier,
      Pi.mul_apply, pow_two]
  · simp [Pi.mul_apply]
    ring_nf

private theorem restartedSquareHeatBarrier_space_hasDerivAt
    {τ M : ℝ} {f : ℝ → ℝ} {s x : ℝ}
    (hS :
      HasDerivAt
        (fun y : ℝ =>
          ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
            (τ + s) f y)
        (deriv (fun y : ℝ =>
          ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
            (τ + s) f y) x) x) :
    HasDerivAt (fun y : ℝ => restartedSquareHeatBarrier τ M f s y)
      (Real.exp (-M * (τ + s)) *
        (2 *
          ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
            (τ + s) f x *
          deriv (fun y : ℝ =>
            ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
              (τ + s) f y) x)) x := by
  have hE :
      HasDerivAt (fun _y : ℝ => Real.exp (-M * (τ + s))) 0 x :=
    hasDerivAt_const x _
  have hSq := hS.mul hS
  have h := hE.mul hSq
  convert h using 1
  · ext y
    simp [restartedSquareHeatBarrier, restartTimeShift, squareHeatBarrier,
      Pi.mul_apply, pow_two]
  · simp [Pi.mul_apply]
    ring_nf

private theorem restartedSquareHeatBarrier_space_deriv_eq
    {L τ M : ℝ} {f : ℝ → ℝ}
    (H : SquareHeatRestartDerivativeData L τ M f)
    {s y : ℝ} (hs0 : 0 < s) (hsL : s < L)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    deriv (fun z : ℝ => restartedSquareHeatBarrier τ M f s z) y =
      Real.exp (-M * (τ + s)) *
        (2 *
          ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
            (τ + s) f y *
          deriv (fun z : ℝ =>
            ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
              (τ + s) f z) y) := by
  exact (restartedSquareHeatBarrier_space_hasDerivAt
    (H.space_hasDerivAt hs0 hsL hy)).deriv

private theorem restartedSquareHeatBarrier_space_second_hasDerivAt
    {L τ M : ℝ} {f : ℝ → ℝ}
    (H : SquareHeatRestartDerivativeData L τ M f)
    {s x : ℝ} (hs0 : 0 < s) (hsL : s < L)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun y : ℝ =>
        ShenWork.PDE.ParabolicMaxPrinciple.dx
          (restartedSquareHeatBarrier τ M f) s y)
      (Real.exp (-M * (τ + s)) *
        (2 *
          (deriv (fun z : ℝ =>
            ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
              (τ + s) f z) x) ^ 2 +
          2 *
            ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
              (τ + s) f x *
            deriv (fun y : ℝ =>
              deriv (fun z : ℝ =>
                ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
                  (τ + s) f z) y) x)) x := by
  let q : ℝ → ℝ :=
    fun y =>
      ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
        (τ + s) f y
  let qx : ℝ → ℝ := fun y => deriv q y
  have hq : HasDerivAt q (qx x) x := by
    simpa [q, qx] using
      (H.space_hasDerivAt hs0 hsL (Set.Ioo_subset_Icc_self hx))
  have hqx : HasDerivAt qx (deriv qx x) x := by
    simpa [q, qx] using H.space_second_hasDerivAt hs0 hsL hx
  have hmodel :
      HasDerivAt
        (fun y : ℝ =>
          Real.exp (-M * (τ + s)) * (2 * q y * qx y))
        (Real.exp (-M * (τ + s)) *
          (2 * (qx x) ^ 2 + 2 * q x * deriv qx x)) x := by
    have hconst :
        HasDerivAt (fun _y : ℝ => Real.exp (-M * (τ + s))) 0 x :=
      hasDerivAt_const x _
    have hprod : HasDerivAt (fun y : ℝ => 2 * q y * qx y)
        (2 * (qx x) ^ 2 + 2 * q x * deriv qx x) x := by
      convert (((hq.const_mul 2).mul hqx)) using 1
      ring
    convert hconst.mul hprod using 1
    ring
  refine hmodel.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hy
  simp [ShenWork.PDE.ParabolicMaxPrinciple.dx,
    restartedSquareHeatBarrier_space_deriv_eq H hs0 hsL hyIcc, q, qx]

private theorem restartedSquareHeatBarrier_neumann
    {L τ M : ℝ} {f : ℝ → ℝ}
    (H : SquareHeatRestartDerivativeData L τ M f) :
    ∀ s, 0 < s → s < L →
      ShenWork.PDE.ParabolicMaxPrinciple.dx
          (restartedSquareHeatBarrier τ M f) s 0 = 0 ∧
        ShenWork.PDE.ParabolicMaxPrinciple.dx
          (restartedSquareHeatBarrier τ M f) s 1 = 0 := by
  intro s hs0 hsL
  constructor
  · rw [ShenWork.PDE.ParabolicMaxPrinciple.dx,
      restartedSquareHeatBarrier_space_deriv_eq H hs0 hsL
        (left_mem_Icc.mpr zero_le_one)]
    rw [(H.neumann s hs0 hsL).1]
    ring
  · rw [ShenWork.PDE.ParabolicMaxPrinciple.dx,
      restartedSquareHeatBarrier_space_deriv_eq H hs0 hsL
        (right_mem_Icc.mpr zero_le_one)]
    rw [(H.neumann s hs0 hsL).2]
    ring

/-- Assemble the regularity part of the restarted squared barrier from
positive-time semigroup derivative witnesses. -/
theorem restartedSquareHeatBarrier_regularity
    {L τ M : ℝ} {f : ℝ → ℝ} {B C : ℝ → ℝ → ℝ}
    (H : SquareHeatRestartDerivativeData L τ M f) :
    NeumannLinearDriftSubSolutionRegularity L
      (restartTimeShift τ B) (restartTimeShift τ C)
      (restartedSquareHeatBarrier τ M f) where
  continuousOn_rect := H.continuousOn_rect
  time_hasDerivAt := by
    intro s x hs0 hsL hx
    have h := restartedSquareHeatBarrier_time_hasDerivAt (M := M)
      (H.time_hasDerivAt hs0 hsL hx)
    simpa [ShenWork.PDE.ParabolicMaxPrinciple.dt, h.deriv] using h
  space_hasDerivAt := by
    intro s x hs0 hsL hx
    have h := restartedSquareHeatBarrier_space_hasDerivAt (M := M)
      (H.space_hasDerivAt hs0 hsL hx)
    simpa [ShenWork.PDE.ParabolicMaxPrinciple.dx, h.deriv] using h
  space_second_hasDerivAt := by
    intro s x hs0 hsL hx
    have h := restartedSquareHeatBarrier_space_second_hasDerivAt H hs0 hsL hx
    simpa [ShenWork.PDE.ParabolicMaxPrinciple.dxx, h.deriv] using h
  neumann := restartedSquareHeatBarrier_neumann H
  bounded := H.bounded

/-- Assemble the residual calculus identity on the restarted strip. -/
theorem restartedSquareHeatBarrier_calculus
    {L τ M : ℝ} {f : ℝ → ℝ} {B C : ℝ → ℝ → ℝ}
    (H : SquareHeatRestartDerivativeData L τ M f) :
    SquareHeatRestartCalculus L τ M f B C where
  residual_eq := by
    intro s x hs0 hsL hx
    let q : ℝ :=
      ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
        (τ + s) f x
    let qx : ℝ :=
      deriv (fun z : ℝ =>
        ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
          (τ + s) f z) x
    let qxx : ℝ :=
      deriv (fun y : ℝ =>
        deriv (fun z : ℝ =>
          ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
            (τ + s) f z) y) x
    have htime :=
      restartedSquareHeatBarrier_time_hasDerivAt (M := M)
        (H.time_hasDerivAt hs0 hsL (Set.Ioo_subset_Icc_self hx))
    have hspace :=
      restartedSquareHeatBarrier_space_hasDerivAt (M := M)
        (H.space_hasDerivAt hs0 hsL (Set.Ioo_subset_Icc_self hx))
    have hsecond :=
      restartedSquareHeatBarrier_space_second_hasDerivAt H hs0 hsL hx
    have hheat :
        deriv (fun r : ℝ =>
          ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
            (τ + r) f x) s = qxx := by
      simpa [qxx] using H.heat_eq hs0 hsL hx
    have hsecond_deriv :
        deriv (fun z : ℝ =>
          deriv (fun y : ℝ => restartedSquareHeatBarrier τ M f s y) z) x =
          Real.exp (-M * (τ + s)) *
            (2 *
              (deriv (fun z : ℝ =>
                ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
                  (τ + s) f z) x) ^ 2 +
              2 *
                ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
                  (τ + s) f x *
                deriv (fun y : ℝ =>
                  deriv (fun z : ℝ =>
                    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
                      (τ + s) f z) y) x) := by
      simpa [ShenWork.PDE.ParabolicMaxPrinciple.dx] using hsecond.deriv
    rw [neumannLinearDriftResidual]
    rw [htime.deriv, hspace.deriv, hsecond_deriv, hheat]
    simp [restartedSquareHeatBarrier, restartTimeShift, squareHeatBarrier,
      squareHeatResidualCore, qxx]
    ring

/-- Build the full restarted strip data after the positive-time semigroup
derivative package and the comparison-side hypotheses have been supplied. -/
def squareHeatRestartStripData_of_derivativeData
    {L τ A D M : ℝ} {f : ℝ → ℝ} {B C u : ℝ → ℝ → ℝ}
    (hderiv : SquareHeatRestartDerivativeData L τ M f)
    (hL : 0 < L)
    (hcoeff :
      NeumannLinearDriftCoefficientsRegular L
        (restartTimeShift τ B) (restartTimeShift τ C))
    (hsuper :
      IsClassicalNeumannLinearDriftSuperSolution L
        (restartTimeShift τ B) (restartTimeShift τ C)
        (restartTimeShift τ u))
    (hM : A ^ 2 / 2 + D ≤ M)
    (hB_bound :
      ∀ s x, 0 < s → s < L → x ∈ Set.Ioo (0 : ℝ) 1 →
        |B (τ + s) x| ≤ A)
    (hC_neg_bound :
      ∀ s x, 0 < s → s < L → x ∈ Set.Ioo (0 : ℝ) 1 →
        -C (τ + s) x ≤ D)
    (hinitial :
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        squareHeatBarrier M f τ x ≤ u τ x) :
    SquareHeatRestartStripData L τ A D M f B C u where
  length_pos := hL
  coeff := hcoeff
  super := hsuper
  barrier_reg := restartedSquareHeatBarrier_regularity (B := B) (C := C) hderiv
  calculus := restartedSquareHeatBarrier_calculus (B := B) (C := C) hderiv
  M_bound := hM
  drift_bound := hB_bound
  reaction_neg_bound := hC_neg_bound
  initial := hinitial

theorem restarted_squareHeatBarrier_subsolution_residual_nonpos
    {L τ A D M : ℝ} {f : ℝ → ℝ} {B C : ℝ → ℝ → ℝ}
    (hcalc : SquareHeatRestartCalculus L τ M f B C)
    (hM : A ^ 2 / 2 + D ≤ M)
    (hB_bound :
      ∀ s x, 0 < s → s < L → x ∈ Set.Ioo (0 : ℝ) 1 →
        |B (τ + s) x| ≤ A)
    (hC_neg_bound :
      ∀ s x, 0 < s → s < L → x ∈ Set.Ioo (0 : ℝ) 1 →
        -C (τ + s) x ≤ D) :
    ∀ s x, 0 < s → s < L → x ∈ Set.Ioo (0 : ℝ) 1 →
      neumannLinearDriftResidual
          (restartTimeShift τ B) (restartTimeShift τ C)
          (restartedSquareHeatBarrier τ M f) s x ≤ 0 := by
  intro s x hs0 hsL hx
  rw [hcalc.residual_eq s x hs0 hsL hx]
  exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
    (squareHeatResidualCore_nonpos_of_bounds
      (hB_bound s x hs0 hsL hx) (hC_neg_bound s x hs0 hsL hx) hM)

/-- Lower barrier on a single restarted strip, obtained by applying the proved
regular drift comparison to the shifted fields on `[0,L]`. -/
theorem square_heat_hbarrier_via_t0_restart
    {L τ A D M : ℝ} {f : ℝ → ℝ} {B C u : ℝ → ℝ → ℝ}
    (H : SquareHeatRestartStripData L τ A D M f B C u) :
    ∀ s x, 0 < s → s < L → x ∈ Set.Icc (0 : ℝ) 1 →
      squareHeatBarrier M f (τ + s) x ≤ u (τ + s) x := by
  have hpde :
      ∀ ⦃s x : ℝ⦄,
        0 < s → s < L → x ∈ Set.Ioo (0 : ℝ) 1 →
          neumannLinearDriftResidual
              (restartTimeShift τ B) (restartTimeShift τ C)
              (restartedSquareHeatBarrier τ M f) s x ≤ 0 := by
    intro s x hs0 hsL hx
    exact restarted_squareHeatBarrier_subsolution_residual_nonpos
      H.calculus H.M_bound H.drift_bound H.reaction_neg_bound s x hs0 hsL hx
  have hsub :
      IsClassicalNeumannLinearDriftSubSolution L
        (restartTimeShift τ B) (restartTimeShift τ C)
        (restartedSquareHeatBarrier τ M f) :=
    NeumannLinearDriftSubSolutionRegularity.toSubSolution H.barrier_reg hpde
  have hu_initial :
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        restartTimeShift τ u 0 x = u τ x := by
    intro x hx
    simp [restartTimeShift]
  have hw_initial :
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        restartedSquareHeatBarrier τ M f 0 x ≤ u τ x := by
    intro x hx
    simpa [restartedSquareHeatBarrier, restartTimeShift] using H.initial x hx
  intro s x hs0 hsL hx
  have hle :=
    neumann_interval_comparison_with_drift
      (T := L)
      (B := restartTimeShift τ B)
      (C := restartTimeShift τ C)
      (u₀ := fun x : ℝ => u τ x)
      (u := restartTimeShift τ u)
      (w := restartedSquareHeatBarrier τ M f)
      H.length_pos H.coeff H.super hu_initial hsub hw_initial
      s x hs0 hsL hx
  simpa [restartedSquareHeatBarrier, restartTimeShift] using hle

/-- Strict positivity from restarted squared-heat barriers.  For each target
time `t`, the hypothesis supplies a positive restart time `τ < t` and the
regular comparison package on the shifted strip of length `DB.T - τ`. -/
theorem bform_strictPos_via_t0_restart
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    {A D M : ℝ} {f : ℝ → ℝ} {drift react : ℝ → ℝ → ℝ}
    (hseed : SquareHeatSeed (intervalDomainLift u₀) f)
    (hrestart :
      ∀ t, 0 < t → t < DB.T →
        ∃ τ, 0 < τ ∧ τ < t ∧
          SquareHeatRestartStripData (DB.T - τ) τ A D M f drift react
            (bformConjugatePicardLift p DB)) :
    ∀ t x, 0 < t → t < DB.T →
      0 < conjugatePicardLimit p u₀ DB.T t x := by
  intro t x ht0 htT
  rcases hrestart t ht0 htT with ⟨τ, hτ0, hτt, H⟩
  have hs0 : 0 < t - τ := by linarith
  have hsL : t - τ < DB.T - τ := by linarith
  have hx : x.1 ∈ Set.Icc (0 : ℝ) 1 := x.2
  have hbarrier_pos :
      0 < squareHeatBarrier M f t x.1 :=
    squareHeatBarrier_pos (M := M) ht0
      hseed.continuousOn hseed.nonneg hseed.pos_somewhere x.1
  have hle_shift :=
    square_heat_hbarrier_via_t0_restart (H := H)
      (t - τ) x.1 hs0 hsL hx
  have htime : τ + (t - τ) = t := by ring
  have hle :
      squareHeatBarrier M f t x.1 ≤
        conjugatePicardLimit p u₀ DB.T t x := by
    simpa [htime, bformConjugatePicardLift, unitClip_of_mem hx] using hle_shift
  exact lt_of_lt_of_le hbarrier_pos hle

end ShenWork.Paper2.BFormPositiveDatumNegPart
