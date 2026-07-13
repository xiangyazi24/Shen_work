/- Coefficient `L2` estimate for the full physical nonlinear remainder. -/
import ShenWork.Paper3.IntervalDomainFluxRemainderDerivative
import ShenWork.Paper3.IntervalDomainLogisticRemainderCoeffs

namespace ShenWork.Paper3

open MeasureTheory Set Real
open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel
open ShenWork.PDE.SectorialOperator

noncomputable section

/-- Bessel estimate specialized to a uniform pointwise bound on the unit
interval. -/
theorem cosineCoeffs_l2_norm_le_of_pointwise_abs_bound
    {f : ℝ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hf_meas : AEStronglyMeasurable f (intervalMeasure 1))
    (hf : ∀ x ∈ Set.Icc (0 : ℝ) 1, |f x| ≤ B) :
    Summable (fun n => (cosineCoeffs f n) ^ 2) ∧
      Real.sqrt (∑' n, (cosineCoeffs f n) ^ 2) ≤ 2 * B := by
  have hone : MemLp (fun _x : ℝ => (1 : ℝ)) 2 (intervalMeasure 1) :=
    memLp_const 1
  have h := cosineCoeffs_l2_norm_le_of_pointwise_mul
    (f := f) (g := fun _x : ℝ => (1 : ℝ)) (B := B)
    hB hone hf_meas (by simpa using hf)
  rcases h with ⟨hsum, hbound⟩
  refine ⟨hsum, hbound.trans_eq ?_⟩
  have hint : (∫ x in (0 : ℝ)..1, ((1 : ℝ)) ^ 2) = 1 := by norm_num
  rw [hint, Real.sqrt_one]
  ring

/-- Physical realization of the two pieces of the full modal nonlinear
remainder.  `chemProfile` already includes the factor `-chi0` and the outer
spatial derivative. -/
structure FullNonlinearRemainderPhysicalData
    (rem : ℕ → ℝ) where
  M : ℝ
  L : ℝ
  Kchem : ℝ
  Klog : ℝ
  chemProfile : ℝ → ℝ
  logProfile : ℝ → ℝ
  M_nonneg : 0 ≤ M
  L_nonneg : 0 ≤ L
  Kchem_nonneg : 0 ≤ Kchem
  Klog_nonneg : 0 ≤ Klog
  chem_measurable : AEStronglyMeasurable chemProfile (intervalMeasure 1)
  log_measurable : AEStronglyMeasurable logProfile (intervalMeasure 1)
  chem_bound : ∀ x ∈ Set.Icc (0 : ℝ) 1,
    |chemProfile x| ≤ Kchem * M * L
  log_bound : ∀ x ∈ Set.Icc (0 : ℝ) 1,
    |logProfile x| ≤ Klog * M * L
  coeff_eq : ∀ n,
    rem n = cosineCoeffs chemProfile n + cosineCoeffs logProfile n

namespace FullNonlinearRemainderPhysicalData

/-- Explicit quadratic coefficient constant furnished by the physical
Bessel estimate. -/
def quadraticConstant {rem : ℕ → ℝ}
    (H : FullNonlinearRemainderPhysicalData rem) : ℝ :=
  2 * Real.sqrt 2 * (H.Kchem + H.Klog)

theorem quadraticConstant_pos_of_one_pos {rem : ℕ → ℝ}
    (H : FullNonlinearRemainderPhysicalData rem)
    (hK : 0 < H.Kchem + H.Klog) : 0 < H.quadraticConstant := by
  unfold quadraticConstant
  exact mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.2 (by norm_num))) hK

/-- L12 in coefficient form: the full modal nonlinear remainder has base
`ell2` norm bounded by one strong factor times one weak factor. -/
theorem coeffL2Norm_le {rem : ℕ → ℝ}
    (H : FullNonlinearRemainderPhysicalData rem) :
    Summable (fun n : ℕ => ‖(rem n : ℂ)‖ ^ 2) ∧
      coeffL2Norm (fun n => (rem n : ℂ)) ≤
        H.quadraticConstant * H.M * H.L := by
  let Bc : ℝ := H.Kchem * H.M * H.L
  let Bl : ℝ := H.Klog * H.M * H.L
  have hBc : 0 ≤ Bc := by
    dsimp [Bc]
    exact mul_nonneg (mul_nonneg H.Kchem_nonneg H.M_nonneg) H.L_nonneg
  have hBl : 0 ≤ Bl := by
    dsimp [Bl]
    exact mul_nonneg (mul_nonneg H.Klog_nonneg H.M_nonneg) H.L_nonneg
  rcases cosineCoeffs_l2_norm_le_of_pointwise_abs_bound hBc
      H.chem_measurable (by simpa [Bc] using H.chem_bound) with
    ⟨hcsum, hcroot⟩
  rcases cosineCoeffs_l2_norm_le_of_pointwise_abs_bound hBl
      H.log_measurable (by simpa [Bl] using H.log_bound) with
    ⟨hlsum, hlroot⟩
  let c : ℕ → ℝ := fun n => cosineCoeffs H.chemProfile n
  let l : ℕ → ℝ := fun n => cosineCoeffs H.logProfile n
  have hcsum' : Summable fun n => (c n) ^ 2 := by simpa [c] using hcsum
  have hlsum' : Summable fun n => (l n) ^ 2 := by simpa [l] using hlsum
  have hmajor : Summable fun n => 2 * (c n) ^ 2 + 2 * (l n) ^ 2 :=
    (hcsum'.mul_left 2).add (hlsum'.mul_left 2)
  have hpoint : ∀ n, ‖(rem n : ℂ)‖ ^ 2 ≤
      2 * (c n) ^ 2 + 2 * (l n) ^ 2 := by
    intro n
    rw [H.coeff_eq]
    dsimp [c, l]
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    nlinarith [sq_nonneg
      (cosineCoeffs H.chemProfile n - cosineCoeffs H.logProfile n)]
  have hsum : Summable fun n => ‖(rem n : ℂ)‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun n => sq_nonneg _) hpoint hmajor
  refine ⟨hsum, ?_⟩
  have henergy : coeffL2Energy (fun n => (rem n : ℂ)) ≤
      2 * (∑' n, (c n) ^ 2) + 2 * (∑' n, (l n) ^ 2) := by
    unfold coeffL2Energy
    calc
      (∑' n, ‖(rem n : ℂ)‖ ^ 2) ≤
          ∑' n, (2 * (c n) ^ 2 + 2 * (l n) ^ 2) :=
        hsum.tsum_le_tsum hpoint hmajor
      _ = (∑' n, 2 * (c n) ^ 2) + ∑' n, 2 * (l n) ^ 2 :=
        (hcsum'.mul_left 2).tsum_add (hlsum'.mul_left 2)
      _ = 2 * (∑' n, (c n) ^ 2) + 2 * (∑' n, (l n) ^ 2) := by
        rw [tsum_mul_left, tsum_mul_left]
  have hcEnergy0 : 0 ≤ ∑' n, (c n) ^ 2 := tsum_nonneg fun n => sq_nonneg _
  have hlEnergy0 : 0 ≤ ∑' n, (l n) ^ 2 := tsum_nonneg fun n => sq_nonneg _
  have hcEnergy : (∑' n, (c n) ^ 2) ≤ (2 * Bc) ^ 2 := by
    have hs := Real.sq_sqrt hcEnergy0
    have hsq := mul_self_le_mul_self (Real.sqrt_nonneg _) hcroot
    nlinarith
  have hlEnergy : (∑' n, (l n) ^ 2) ≤ (2 * Bl) ^ 2 := by
    have hs := Real.sq_sqrt hlEnergy0
    have hsq := mul_self_le_mul_self (Real.sqrt_nonneg _) hlroot
    nlinarith
  have htotal : coeffL2Energy (fun n => (rem n : ℂ)) ≤
      2 * ((2 * Bc) + (2 * Bl)) ^ 2 := by
    calc
      coeffL2Energy (fun n => (rem n : ℂ)) ≤
          2 * (∑' n, (c n) ^ 2) + 2 * (∑' n, (l n) ^ 2) := henergy
      _ ≤ 2 * (2 * Bc) ^ 2 + 2 * (2 * Bl) ^ 2 := by nlinarith
      _ ≤ 2 * ((2 * Bc) + (2 * Bl)) ^ 2 := by
        nlinarith [mul_nonneg hBc hBl]
  unfold coeffL2Norm
  have hsqrt := Real.sqrt_le_sqrt htotal
  have hsumB : 0 ≤ 2 * Bc + 2 * Bl := by positivity
  calc
    Real.sqrt (coeffL2Energy (fun n => (rem n : ℂ))) ≤
        Real.sqrt (2 * ((2 * Bc) + (2 * Bl)) ^ 2) := hsqrt
    _ = Real.sqrt 2 * (2 * Bc + 2 * Bl) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
        Real.sqrt_sq hsumB]
    _ = H.quadraticConstant * H.M * H.L := by
      unfold quadraticConstant
      dsimp [Bc, Bl]
      ring

end FullNonlinearRemainderPhysicalData

/-- The strong-space nonlinear estimate only needs the differentiated physical
profiles in `L²`; asking for pointwise bounds on their derivatives would
silently strengthen `X^sigma`, `sigma > 3/4`, to a classical `C²` space. -/
structure FullNonlinearRemainderL2Data
    (rem : ℕ → ℝ) where
  M : ℝ
  L : ℝ
  Kchem : ℝ
  Klog : ℝ
  chemProfile : ℝ → ℝ
  logProfile : ℝ → ℝ
  M_nonneg : 0 ≤ M
  L_nonneg : 0 ≤ L
  Kchem_nonneg : 0 ≤ Kchem
  Klog_nonneg : 0 ≤ Klog
  chem_memLp : MemLp chemProfile 2 (intervalMeasure 1)
  log_memLp : MemLp logProfile 2 (intervalMeasure 1)
  chem_l2 : Real.sqrt (∫ x in (0 : ℝ)..1, (chemProfile x) ^ 2) ≤
    Kchem * M * L
  log_l2 : Real.sqrt (∫ x in (0 : ℝ)..1, (logProfile x) ^ 2) ≤
    Klog * M * L
  coeff_eq : ∀ n,
    rem n = cosineCoeffs chemProfile n + cosineCoeffs logProfile n

namespace FullNonlinearRemainderL2Data

def quadraticConstant {rem : ℕ → ℝ}
    (H : FullNonlinearRemainderL2Data rem) : ℝ :=
  2 * Real.sqrt 2 * (H.Kchem + H.Klog)

theorem quadraticConstant_nonneg {rem : ℕ → ℝ}
    (H : FullNonlinearRemainderL2Data rem) :
    0 ≤ H.quadraticConstant := by
  unfold quadraticConstant
  exact mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
    (add_nonneg H.Kchem_nonneg H.Klog_nonneg)

/-- L12 at its natural regularity: a Bessel estimate applied to the two `L²`
physical remainder profiles. -/
theorem coeffL2Norm_le {rem : ℕ → ℝ}
    (H : FullNonlinearRemainderL2Data rem) :
    Summable (fun n : ℕ => ‖(rem n : ℂ)‖ ^ 2) ∧
      coeffL2Norm (fun n => (rem n : ℂ)) ≤
        H.quadraticConstant * H.M * H.L := by
  rcases ShenWork.IntervalNHGBrickB.cosineCoeffs_l2_of_memLp H.chem_memLp with
    ⟨hcsum, hcroot⟩
  rcases ShenWork.IntervalNHGBrickB.cosineCoeffs_l2_of_memLp H.log_memLp with
    ⟨hlsum, hlroot⟩
  let c : ℕ → ℝ := fun n => cosineCoeffs H.chemProfile n
  let l : ℕ → ℝ := fun n => cosineCoeffs H.logProfile n
  have hcsum' : Summable fun n => (c n) ^ 2 := by simpa [c] using hcsum
  have hlsum' : Summable fun n => (l n) ^ 2 := by simpa [l] using hlsum
  have hcroot' : Real.sqrt (∑' n, (c n) ^ 2) ≤
      2 * H.Kchem * H.M * H.L := by
    calc
      _ ≤ 2 * Real.sqrt (∫ x in (0 : ℝ)..1, (H.chemProfile x) ^ 2) := hcroot
      _ ≤ 2 * (H.Kchem * H.M * H.L) :=
        mul_le_mul_of_nonneg_left H.chem_l2 (by norm_num)
      _ = _ := by ring
  have hlroot' : Real.sqrt (∑' n, (l n) ^ 2) ≤
      2 * H.Klog * H.M * H.L := by
    calc
      _ ≤ 2 * Real.sqrt (∫ x in (0 : ℝ)..1, (H.logProfile x) ^ 2) := hlroot
      _ ≤ 2 * (H.Klog * H.M * H.L) :=
        mul_le_mul_of_nonneg_left H.log_l2 (by norm_num)
      _ = _ := by ring
  have hmajor : Summable fun n => 2 * (c n) ^ 2 + 2 * (l n) ^ 2 :=
    (hcsum'.mul_left 2).add (hlsum'.mul_left 2)
  have hpoint : ∀ n, ‖(rem n : ℂ)‖ ^ 2 ≤
      2 * (c n) ^ 2 + 2 * (l n) ^ 2 := by
    intro n
    rw [H.coeff_eq]
    dsimp [c, l]
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    nlinarith [sq_nonneg
      (cosineCoeffs H.chemProfile n - cosineCoeffs H.logProfile n)]
  have hsum : Summable fun n => ‖(rem n : ℂ)‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun n => sq_nonneg _) hpoint hmajor
  refine ⟨hsum, ?_⟩
  have hc0 : 0 ≤ ∑' n, (c n) ^ 2 := tsum_nonneg fun n => sq_nonneg _
  have hl0 : 0 ≤ ∑' n, (l n) ^ 2 := tsum_nonneg fun n => sq_nonneg _
  have hcEnergy : (∑' n, (c n) ^ 2) ≤
      (2 * H.Kchem * H.M * H.L) ^ 2 := by
    nlinarith [Real.sq_sqrt hc0,
      mul_self_le_mul_self (Real.sqrt_nonneg _) hcroot']
  have hlEnergy : (∑' n, (l n) ^ 2) ≤
      (2 * H.Klog * H.M * H.L) ^ 2 := by
    nlinarith [Real.sq_sqrt hl0,
      mul_self_le_mul_self (Real.sqrt_nonneg _) hlroot']
  have henergy : coeffL2Energy (fun n => (rem n : ℂ)) ≤
      2 * (∑' n, (c n) ^ 2) + 2 * (∑' n, (l n) ^ 2) := by
    unfold coeffL2Energy
    calc
      _ ≤ ∑' n, (2 * (c n) ^ 2 + 2 * (l n) ^ 2) :=
        hsum.tsum_le_tsum hpoint hmajor
      _ = (∑' n, 2 * (c n) ^ 2) + ∑' n, 2 * (l n) ^ 2 :=
        (hcsum'.mul_left 2).tsum_add (hlsum'.mul_left 2)
      _ = _ := by rw [tsum_mul_left, tsum_mul_left]
  have htotal : coeffL2Energy (fun n => (rem n : ℂ)) ≤
      2 * ((2 * H.Kchem * H.M * H.L) +
        (2 * H.Klog * H.M * H.L)) ^ 2 := by
    calc
      _ ≤ 2 * (∑' n, (c n) ^ 2) + 2 * (∑' n, (l n) ^ 2) := henergy
      _ ≤ 2 * (2 * H.Kchem * H.M * H.L) ^ 2 +
          2 * (2 * H.Klog * H.M * H.L) ^ 2 := by nlinarith
      _ ≤ _ := by
        nlinarith [mul_nonneg
          (mul_nonneg (mul_nonneg H.Kchem_nonneg H.M_nonneg) H.L_nonneg)
          (mul_nonneg (mul_nonneg H.Klog_nonneg H.M_nonneg) H.L_nonneg)]
  unfold coeffL2Norm
  have hsqrt := Real.sqrt_le_sqrt htotal
  have hsumK : 0 ≤
      2 * H.Kchem * H.M * H.L + 2 * H.Klog * H.M * H.L :=
    add_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) H.Kchem_nonneg)
        H.M_nonneg) H.L_nonneg)
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) H.Klog_nonneg)
        H.M_nonneg) H.L_nonneg)
  calc
    Real.sqrt (coeffL2Energy (fun n => (rem n : ℂ))) ≤
        Real.sqrt (2 * ((2 * H.Kchem * H.M * H.L) +
          (2 * H.Klog * H.M * H.L)) ^ 2) := hsqrt
    _ = Real.sqrt 2 *
        (2 * H.Kchem * H.M * H.L + 2 * H.Klog * H.M * H.L) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq hsumK]
    _ = H.quadraticConstant * H.M * H.L := by
      unfold quadraticConstant
      ring

end FullNonlinearRemainderL2Data

/-- Polarized local Nemytskii estimate used by the Banach contraction.  The
profiles realize `N(w1)-N(w2)` and carry the sharp local factor
`(‖w1‖+‖w2‖)‖w1-w2‖`. -/
structure FullNonlinearRemainderDifferenceL2Data
    (remDiff : ℕ → ℝ) where
  M1 : ℝ
  M2 : ℝ
  D : ℝ
  Kchem : ℝ
  Klog : ℝ
  chemProfile : ℝ → ℝ
  logProfile : ℝ → ℝ
  M1_nonneg : 0 ≤ M1
  M2_nonneg : 0 ≤ M2
  D_nonneg : 0 ≤ D
  Kchem_nonneg : 0 ≤ Kchem
  Klog_nonneg : 0 ≤ Klog
  chem_memLp : MemLp chemProfile 2 (intervalMeasure 1)
  log_memLp : MemLp logProfile 2 (intervalMeasure 1)
  chem_l2 : Real.sqrt (∫ x in (0 : ℝ)..1, (chemProfile x) ^ 2) ≤
    Kchem * (M1 + M2) * D
  log_l2 : Real.sqrt (∫ x in (0 : ℝ)..1, (logProfile x) ^ 2) ≤
    Klog * (M1 + M2) * D
  coeff_eq : ∀ n,
    remDiff n = cosineCoeffs chemProfile n + cosineCoeffs logProfile n

namespace FullNonlinearRemainderDifferenceL2Data

def toL2Data {remDiff : ℕ → ℝ}
    (H : FullNonlinearRemainderDifferenceL2Data remDiff) :
    FullNonlinearRemainderL2Data remDiff where
  M := H.M1 + H.M2
  L := H.D
  Kchem := H.Kchem
  Klog := H.Klog
  chemProfile := H.chemProfile
  logProfile := H.logProfile
  M_nonneg := add_nonneg H.M1_nonneg H.M2_nonneg
  L_nonneg := H.D_nonneg
  Kchem_nonneg := H.Kchem_nonneg
  Klog_nonneg := H.Klog_nonneg
  chem_memLp := H.chem_memLp
  log_memLp := H.log_memLp
  chem_l2 := H.chem_l2
  log_l2 := H.log_l2
  coeff_eq := H.coeff_eq

def lipschitzConstant {remDiff : ℕ → ℝ}
    (H : FullNonlinearRemainderDifferenceL2Data remDiff) : ℝ :=
  2 * Real.sqrt 2 * (H.Kchem + H.Klog)

/-- Polarized L12: the actual contraction estimate, separate from the
one-trajectory quadratic self-map estimate. -/
theorem coeffL2Norm_le {remDiff : ℕ → ℝ}
    (H : FullNonlinearRemainderDifferenceL2Data remDiff) :
    Summable (fun n : ℕ => ‖(remDiff n : ℂ)‖ ^ 2) ∧
      coeffL2Norm (fun n => (remDiff n : ℂ)) ≤
        H.lipschitzConstant * (H.M1 + H.M2) * H.D := by
  simpa [toL2Data, lipschitzConstant,
    FullNonlinearRemainderL2Data.quadraticConstant] using
      H.toL2Data.coeffL2Norm_le

end FullNonlinearRemainderDifferenceL2Data

#print axioms cosineCoeffs_l2_norm_le_of_pointwise_abs_bound
#print axioms FullNonlinearRemainderPhysicalData.coeffL2Norm_le
#print axioms FullNonlinearRemainderL2Data.coeffL2Norm_le
#print axioms FullNonlinearRemainderDifferenceL2Data.coeffL2Norm_le

end

end ShenWork.Paper3
