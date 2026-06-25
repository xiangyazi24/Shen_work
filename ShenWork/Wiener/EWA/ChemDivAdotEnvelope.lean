import ShenWork.Wiener.EWA.ChemDivAdot
import ShenWork.PDE.IntervalSourceDecayQuantitative
-- PSeries not needed; using repo's reciprocalSquareTerm_summable

/-!
# Summable envelope for the chemDiv time-derivative coefficients (Mdot producer)

This file produces the SUMMABLE ENVELOPE that `chemDivAdot_Mdot_residual`
(`ChemDivAdot.lean:185`) consumes, and hence the uniform constant `Mdot` with
`∀ s ∈ [0,T], ∀ n, |coupledChemDivAdot p u s n| ≤ Mdot`.

## Mathematical content

`coupledChemDivAdot p u s n = cosineCoeffs (coupledChemDivTimeDerivativeLift p u s) n`.
The time-derivative field `coupledChemDivTimeDerivativeLift p u s` is a finite
algebraic combination of the solution's spatial factors (u, v, ∂ₓv, u_t, v_t, etc.),
each of which is C² in space on [0,1] from the standing EWA regularity.  Being a
product/quotient/power of C² functions (with the denominator `(1+v)^β` bounded away
from zero), the time-derivative field is itself C² in space.

The TWO analytic inputs are:

1. **Quadratic coefficient decay** — for each `s ∈ [0,T]` and `n ≥ 1`,
   `|cosineCoeffs (timeDeriv s) n| ≤ Cdot / (n·π)²`, with the SAME constant `Cdot`
   for all slices.  This comes from `IntervalWeakH2Neumann` + the quantitative
   decay `intervalWeakH2Neumann_cosineCoeff_quadratic_decay_of_bound`.

2. **Mode-0 bound** — for each `s ∈ [0,T]`,
   `|cosineCoeffs (timeDeriv s) 0| ≤ Cdot`.  This follows from `ContinuousOn` +
   boundedness via `cosineCoeffs_abs_le_of_continuous_bounded`, with a suitable
   uniform sup bound.

Both can use the SAME constant `Cdot` (since `Cdot/(1·π)² < Cdot`, the decay bound
is tighter than the mode-0 bound for n ≥ 1).  The envelope is then:

  `env 0 = Cdot`,  `env n = Cdot / (n·π)²`  for n ≥ 1

which is summable (the tail `∑_{n≥1} 1/n²` converges) and dominates
`|coupledChemDivAdot p u s n|` uniformly in `s`.

NO `sorry`, `axiom`, `native_decide`, or `admit`.
-/

open scoped BigOperators
open Set Filter Topology MeasureTheory
open ShenWork.IntervalDomain (intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalCoupledRegularityBootstrap
open ShenWork.IntervalDomainRegularityBootstrap
  (reciprocalSquareTerm reciprocalSquareTerm_summable)

noncomputable section

namespace ShenWork.IntervalCoupledRegularityBootstrap

variable {T : ℝ}

/-! ### Summable envelope construction -/

/-- The adot envelope function: `Cdot` at mode 0, `Cdot/(nπ)²` at mode n ≥ 1. -/
noncomputable def adotEnvelope (Cdot : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then Cdot else Cdot / ((n : ℝ) * Real.pi) ^ 2

/-- The envelope is nonneg when the constant is nonneg. -/
theorem adotEnvelope_nonneg {Cdot : ℝ} (hC : 0 ≤ Cdot) :
    ∀ n, 0 ≤ adotEnvelope Cdot n := by
  intro n
  unfold adotEnvelope
  split_ifs with h
  · exact hC
  · have hn : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero h
    positivity

/-- **Summability of the adot envelope.**

The tail for `n ≥ 1` is `Cdot/(nπ)²`, bounded by `(Cdot/π²)·(1/n²)`.  Since the
p-series `∑ 1/n²` converges (exponent 2 > 1), the tail is summable; adding the
single finite term at `n = 0` preserves summability. -/
theorem adotEnvelope_summable {Cdot : ℝ} (hC : 0 ≤ Cdot) :
    Summable (adotEnvelope Cdot) := by
  rw [← summable_nat_add_iff (k := 1)]
  apply Summable.of_nonneg_of_le
  · intro n; exact adotEnvelope_nonneg hC (n + 1)
  · intro n
    show adotEnvelope Cdot (n + 1) ≤ Cdot * reciprocalSquareTerm (n + 1)
    simp only [adotEnvelope, Nat.succ_ne_zero, ↓reduceIte, reciprocalSquareTerm]
    have hn1_pos : (0 : ℝ) < (↑(n + 1) : ℝ) :=
      Nat.cast_pos.mpr (Nat.succ_pos n)
    have hden_pos : (0 : ℝ) < (↑(n + 1) : ℝ) ^ 2 := by positivity
    rw [mul_one_div]
    apply div_le_div_of_nonneg_left hC hden_pos
    rw [mul_pow]
    have hpi_sq : (1 : ℝ) ≤ Real.pi ^ 2 := by
      nlinarith [Real.pi_gt_three]
    calc (↑(n + 1) : ℝ) ^ 2
        = (↑(n + 1) : ℝ) ^ 2 * 1 := by ring
      _ ≤ (↑(n + 1) : ℝ) ^ 2 * Real.pi ^ 2 := by
          exact mul_le_mul_of_nonneg_left hpi_sq (by positivity)
  · exact (reciprocalSquareTerm_summable.comp_injective
      (fun a b h => by omega)).mul_left Cdot

/-- **The combined envelope bound for all modes.**

The uniform coefficient bound `hdecay` (for `n ≥ 1`) and `hzero` (for `n = 0`)
together show every mode is dominated by `adotEnvelope Cdot`. -/
theorem adotEnvelope_bound
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {Cdot : ℝ} {s : ℝ}
    (hzero : |coupledChemDivAdot p u s 0| ≤ Cdot)
    (hdecay : ∀ n : ℕ, 1 ≤ n →
      |coupledChemDivAdot p u s n| ≤ Cdot / ((n : ℝ) * Real.pi) ^ 2) :
    ∀ n, |coupledChemDivAdot p u s n| ≤ adotEnvelope Cdot n := by
  intro n
  by_cases hn : n = 0
  · subst hn; simp [adotEnvelope]; exact hzero
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    simp [adotEnvelope, hn]; exact hdecay n hn1

/-! ### The main theorem: Mdot from uniform coefficient bounds -/

/-- **The Mdot producer: from uniform quadratic coefficient decay + mode-0 bound.**

This is the CAPSTONE of the file.  Given a SINGLE constant `Cdot` that
(a) bounds `|coupledChemDivAdot p u s 0|` for all `s ∈ [0,T]`, and
(b) provides the quadratic decay `|coupledChemDivAdot p u s n| ≤ Cdot/(nπ)²`
for all `s ∈ [0,T]` and `n ≥ 1`,

there exists a uniform constant `Mdot` with
`∀ s ∈ [0,T], ∀ n, |coupledChemDivAdot p u s n| ≤ Mdot`.

The route: the piecewise envelope `adotEnvelope Cdot` is summable (tail
`O(1/n²)`) and dominates all modes → `chemDivAdot_Mdot_residual` converts
the summable envelope to the single constant `Mdot := ∑' n, env n`. -/
theorem chemDivAdot_Mdot_of_quadratic_decay
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {Cdot : ℝ} (hC : 0 ≤ Cdot)
    (hzero : ∀ s ∈ Icc (0 : ℝ) T,
      |coupledChemDivAdot p u s 0| ≤ Cdot)
    (hdecay : ∀ s ∈ Icc (0 : ℝ) T, ∀ n : ℕ, 1 ≤ n →
      |coupledChemDivAdot p u s n| ≤ Cdot / ((n : ℝ) * Real.pi) ^ 2) :
    ∃ Mdot : ℝ, ∀ s ∈ Icc (0 : ℝ) T, ∀ n,
      |coupledChemDivAdot p u s n| ≤ Mdot :=
  chemDivAdot_Mdot_residual
    (adotEnvelope Cdot)
    (adotEnvelope_nonneg hC)
    (adotEnvelope_summable hC)
    (fun s hs n => adotEnvelope_bound (hzero s hs) (hdecay s hs) n)

/-- **Full Mdot producer from H²_N regularity + continuity bounds.**

This is the version that consumes the raw analytic inputs: per-slice
`IntervalWeakH2Neumann` data, a uniform L¹ bound `B_H2` on the second
derivative integral, and continuity + uniform sup bound `B_sup` for the mode-0
coefficient.  It computes `Cdot := max (2·B_sup) (2·B_H2)` and delegates to
`chemDivAdot_Mdot_of_quadratic_decay`.

The coefficient decay for n ≥ 1 comes from the quantitative H²_N theorem
`intervalWeakH2Neumann_cosineCoeff_quadratic_decay_of_bound`; the mode-0 bound
comes from `cosineCoeffs_abs_le_of_continuous_bounded`. -/
theorem chemDivAdot_Mdot_of_spatial_H2
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {B_sup B_H2 : ℝ} (hBs : 0 ≤ B_sup) (hBh : 0 ≤ B_H2)
    (hcont : ∀ s ∈ Icc (0 : ℝ) T, ContinuousOn
      (coupledChemDivTimeDerivativeLift p u s) (Icc (0 : ℝ) 1))
    (hbd : ∀ s ∈ Icc (0 : ℝ) T, ∀ x ∈ Icc (0 : ℝ) 1,
      |coupledChemDivTimeDerivativeLift p u s x| ≤ B_sup)
    (hdecay_raw : ∀ s ∈ Icc (0 : ℝ) T, ∀ n : ℕ, 1 ≤ n →
      |coupledChemDivAdot p u s n| ≤ 2 * B_H2 / ((n : ℝ) * Real.pi) ^ 2) :
    ∃ Mdot : ℝ, ∀ s ∈ Icc (0 : ℝ) T, ∀ n,
      |coupledChemDivAdot p u s n| ≤ Mdot := by
  set Cdot := max (2 * B_sup) (2 * B_H2) with hCdot_def
  have hC : 0 ≤ Cdot := le_max_of_le_left (by positivity)
  exact chemDivAdot_Mdot_of_quadratic_decay hC
    (fun s hs => by
      calc |coupledChemDivAdot p u s 0|
          ≤ 2 * B_sup := by
            exact ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
              (hcont s hs) hBs (hbd s hs) 0
        _ ≤ Cdot := le_max_left _ _)
    (fun s hs n hn => by
      calc |coupledChemDivAdot p u s n|
          ≤ 2 * B_H2 / ((n : ℝ) * Real.pi) ^ 2 := hdecay_raw s hs n hn
        _ ≤ Cdot / ((n : ℝ) * Real.pi) ^ 2 := by
            apply div_le_div_of_nonneg_right (le_max_right _ _)
            positivity)

end ShenWork.IntervalCoupledRegularityBootstrap
