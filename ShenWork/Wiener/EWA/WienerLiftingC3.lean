import ShenWork.Wiener.EWA.CosineDecayC3
import ShenWork.Wiener.WeightedL1CosineAdapter
import ShenWork.PDE.IntervalDomain
import ShenWork.PDE.CosineSpectrum
import ShenWork.Paper2.Statements

/-!
# Certified C³ Neumann datum to Wiener lifting

This file defines the single-datum Wiener lifting record and packages a C³
Neumann interval datum into it once the needed cosine-side analytic certificates
are supplied explicitly.
-/

open Set Filter Topology
open ShenWork.IntervalDomain (intervalDomain intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.Paper2 (PaperPositiveInitialDatum)
open ShenWork.Wiener (MemW ofCosineCoeffs memW_ofCosineCoeffs)

noncomputable section

namespace ShenWork.EWA

/-- Single-datum Wiener lifting record used by the uniform EWA bridge. -/
structure DatumWienerLifting (u₀p : intervalDomainPoint → ℝ) where
  u₀ : ℝ → ℝ
  hu₀ : Continuous u₀
  floor : ℝ
  hfloor_pos : 0 < floor
  hfloor : ∀ y, floor ≤ u₀ y
  hsumc : Summable (fun k => |cosineCoeffs u₀ k|)
  hmem : MemW 1 (ofCosineCoeffs (cosineCoeffs u₀))
  coeff_bound : ℝ
  hcoeff_bound : ∀ n, |cosineCoeffs u₀ n| ≤ coeff_bound
  hrecon : ∀ x : intervalDomainPoint,
    u₀p x = ∑' n, cosineCoeffs u₀ n * cosineMode n x.1

/-- A C³ Neumann representative of a paper initial datum, in the form consumed by
the Wiener/EWA fixed-point layer.

The weighted summability and closed-interval reconstruction fields are explicit
certificates; they are not consequences of `hfC3` in this file. -/
structure C3NeumannDatum (u₀p : intervalDomainPoint → ℝ) where
  u₀ : ℝ → ℝ
  hu₀ : Continuous u₀
  hagree : ∀ x : intervalDomainPoint, u₀ x.1 = u₀p x
  hfC3 : ContDiffOn ℝ 3 u₀ (Set.Icc (0 : ℝ) 1)
  hN0 : deriv u₀ 0 = 0
  hN1 : deriv u₀ 1 = 0
  floor : ℝ
  hfloor_pos : 0 < floor
  hfloor : ∀ y : ℝ, floor ≤ u₀ y
  coeff_bound : ℝ
  coeff_bound_nonneg : 0 ≤ coeff_bound
  hcoeff_bound : ∀ n : ℕ, |cosineCoeffs u₀ n| ≤ coeff_bound
  hweighted :
    Summable (fun k : ℕ => (1 + (k : ℝ)) ^ (1 : ℕ) * |cosineCoeffs u₀ k|)
  hrecon : ∀ x : intervalDomainPoint,
    u₀p x = ∑' n, cosineCoeffs u₀ n * cosineMode n x.1

private theorem summable_abs_of_weighted_one {c : ℕ → ℝ}
    (hc : Summable (fun k : ℕ => (1 + (k : ℝ)) ^ (1 : ℕ) * |c k|)) :
    Summable (fun k : ℕ => |c k|) := by
  refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) ?_ hc
  intro k
  have hw : 1 ≤ (1 + (k : ℝ)) ^ (1 : ℕ) := by
    simp
  calc
    |c k| = 1 * |c k| := by ring
    _ ≤ (1 + (k : ℝ)) ^ (1 : ℕ) * |c k| :=
      mul_le_mul_of_nonneg_right hw (abs_nonneg _)

/-- Package a certified C³ Neumann datum into the single-datum Wiener lifting record. -/
def datumWienerLifting_of_C3_neumann
    {u₀p : intervalDomainPoint → ℝ}
    (_hppid : PaperPositiveInitialDatum intervalDomain u₀p)
    (hC3 : C3NeumannDatum u₀p) :
    DatumWienerLifting u₀p := by
  classical
  have hweighted :
      Summable
        (fun k : ℕ => (1 + (k : ℝ)) ^ (1 : ℕ) * |cosineCoeffs hC3.u₀ k|) :=
    hC3.hweighted
  have hsumc : Summable (fun k : ℕ => |cosineCoeffs hC3.u₀ k|) :=
    summable_abs_of_weighted_one (c := cosineCoeffs hC3.u₀) hweighted
  have hmem : MemW 1 (ofCosineCoeffs (cosineCoeffs hC3.u₀)) :=
    memW_ofCosineCoeffs (r := 1) (c := cosineCoeffs hC3.u₀) hweighted
  refine
    { u₀ := hC3.u₀
      hu₀ := hC3.hu₀
      floor := hC3.floor
      hfloor_pos := hC3.hfloor_pos
      hfloor := hC3.hfloor
      hsumc := hsumc
      hmem := hmem
      coeff_bound := hC3.coeff_bound
      hcoeff_bound := hC3.hcoeff_bound
      hrecon := hC3.hrecon }

end ShenWork.EWA
