/-
  ShenWork/PDE/IntervalFullKernelDuhamelGradEq.lean

  **The `hGradEq` boundary-derivative bridge is TRUE on the full Neumann kernel.**

  ROUND-15 found that `hGradEq` is FALSE at `x = 1` when the Duhamel operator is
  built on the zeroth-reflection semigroup `intervalSemigroupOperator` (Neumann
  at `0` only).  Resolution (b): rebuild on the full Neumann kernel.

  This file defines the full-kernel coupled Duhamel operator
  `intervalFullKernelCoupledDuhamelOperator` (identical to
  `intervalCoupledDuhamelOperator` but with `intervalFullSemigroupOperator` in
  place of `intervalSemigroupOperator 1`) and proves the `hGradEq` identity for
  it holds at EVERY `x ∈ Icc 0 1`:

  * interior `x ∈ Ioo 0 1`: the lift coincides with the explicit field on the
    open interior, so the derivatives agree;
  * endpoints `x ∈ {0,1}`: BOTH sides are `0` — the LHS by the zero-extension
    (`intervalDomainLift_deriv_at_{zero,one}_eq_zero`), the RHS by the genuine
    two-endpoint Neumann property of the full semigroup
    (`intervalFullDuhamelExplicit_deriv_at_{zero,one}_eq_zero`).

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.PDE.IntervalChemDivAEMeasurable
import ShenWork.PDE.IntervalFullSemigroupNeumann

open MeasureTheory
open scoped Topology

namespace ShenWork

open ShenWork.IntervalDomain ShenWork.IntervalDomainExistence
open ShenWork.IntervalNeumannFullKernel

/-- **Full-kernel coupled Duhamel operator.**  The paper-2 Duhamel map with the
genuine two-endpoint-Neumann full kernel `intervalFullSemigroupOperator` in
place of the zeroth-reflection `intervalSemigroupOperator 1`. -/
noncomputable def intervalFullKernelCoupledDuhamelOperator (p : CM2Params)
    (R : (intervalDomainPoint → ℝ) → intervalDomainPoint → ℝ)
    (u₀ : intervalDomainPoint → ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    (t : ℝ) (x : intervalDomainPoint) : ℝ :=
  intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
    + ∫ s in Set.Icc 0 t, intervalFullSemigroupOperator (t - s)
        (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) x.1

/-- **`hGradEq` holds on the full Neumann kernel, at every `x ∈ Icc 0 1`.**

The spatial derivative of the lifted full-kernel Duhamel image equals the
derivative of the explicit semigroup+integral field — including at the right
endpoint `x = 1`, where it FAILED for the zeroth-reflection kernel. -/
theorem intervalFullKernel_hGradEq
    {p : CM2Params} {R : (intervalDomainPoint → ℝ) → intervalDomainPoint → ℝ}
    {u₀ : intervalDomainPoint → ℝ} {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (τ x : ℝ) (hτ : τ ∈ Set.Ioo (0 : ℝ) T) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    deriv
      (intervalDomainLift
        (fun y : intervalDomainPoint =>
          intervalFullKernelCoupledDuhamelOperator p R u₀ u τ y)) x =
    deriv (fun z : ℝ =>
      intervalFullSemigroupOperator τ (intervalDomainLift u₀) z +
      ∫ s in (0 : ℝ)..τ,
        intervalFullSemigroupOperator (τ - s)
          (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) z) x := by
  have hτ0 : (0 : ℝ) ≤ τ := le_of_lt hτ.1
  -- The set-integral over `Icc 0 τ` equals the interval integral over `0..τ`.
  have hIntEq : ∀ z : ℝ,
      (∫ s in Set.Icc 0 τ, intervalFullSemigroupOperator (τ - s)
        (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) z)
        = ∫ s in (0 : ℝ)..τ, intervalFullSemigroupOperator (τ - s)
          (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) z := by
    intro z
    rw [intervalIntegral.integral_of_le hτ0,
      MeasureTheory.integral_Icc_eq_integral_Ioc]
  -- The lifted Duhamel image agrees with the explicit field on the open interior.
  have hlift_eq : ∀ z ∈ Set.Ioo (0 : ℝ) 1,
      intervalDomainLift
        (fun y : intervalDomainPoint =>
          intervalFullKernelCoupledDuhamelOperator p R u₀ u τ y) z =
      (intervalFullSemigroupOperator τ (intervalDomainLift u₀) z +
        ∫ s in (0 : ℝ)..τ,
          intervalFullSemigroupOperator (τ - s)
            (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) z) := by
    intro z hz
    have hzIcc : z ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hz
    have hval : intervalDomainLift
        (fun y : intervalDomainPoint =>
          intervalFullKernelCoupledDuhamelOperator p R u₀ u τ y) z
        = intervalFullKernelCoupledDuhamelOperator p R u₀ u τ ⟨z, hzIcc⟩ := by
      simp only [intervalDomainLift, dif_pos hzIcc]
    rw [hval]
    show intervalFullSemigroupOperator τ (intervalDomainLift u₀) z +
        (∫ s in Set.Icc 0 τ, intervalFullSemigroupOperator (τ - s)
          (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) z)
      = intervalFullSemigroupOperator τ (intervalDomainLift u₀) z +
        ∫ s in (0 : ℝ)..τ, intervalFullSemigroupOperator (τ - s)
          (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) z
    rw [hIntEq z]
  -- Split into the interior and the two endpoints.
  rcases eq_or_lt_of_le hx.1 with hx0 | hx0
  · -- x = 0
    have hx0' : x = 0 := hx0.symm
    subst hx0'
    rw [intervalDomainLift_deriv_at_zero_eq_zero]
    exact (intervalFullDuhamelExplicit_deriv_at_zero_eq_zero τ (intervalDomainLift u₀)
      (fun s => intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))).symm
  rcases eq_or_lt_of_le hx.2 with hx1 | hx1
  · -- x = 1
    subst hx1
    rw [intervalDomainLift_deriv_at_one_eq_zero]
    exact (intervalFullDuhamelExplicit_deriv_at_one_eq_zero τ (intervalDomainLift u₀)
      (fun s => intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))).symm
  · -- x ∈ Ioo 0 1 : derivatives agree by `EventuallyEq` on the open interior
    have hxIoo : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨hx0, hx1⟩
    exact Filter.EventuallyEq.deriv_eq
      (Filter.eventuallyEq_of_mem (IsOpen.mem_nhds isOpen_Ioo hxIoo) hlift_eq)

end ShenWork
