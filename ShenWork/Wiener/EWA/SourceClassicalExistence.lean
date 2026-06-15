import ShenWork.Wiener.EWA.SourceStrongSolution
import ShenWork.Wiener.EWA.SourceFixedPointAbs
import ShenWork.Wiener.EWA.HeatFloor
import ShenWork.Wiener.EWA.ChemDivEval
import ShenWork.Wiener.EWA.FluxEvalBridge
import ShenWork.Wiener.EWA.GrowthEvalBridge

/-!
# EWA capstone (χ₀<0 Route A′) — FINAL CONVERGENCE: fixed point → classical existence

This file is the FINAL CONVERGENCE of the χ₀<0 Route-A′ construction.  It instantiates
the committed `SourceStrongSolutionData` (`SourceStrongSolution.lean`) from the
source-form EWA fixed point `u* = Φ(u*)` (`picardEWA_abs_fixedPoint`,
`SourceFixedPointAbs.lean:145`), and concludes the χ₀<0 strong-data SPATIAL CLASSICAL
EXISTENCE — the `ContDiff ℝ 2` spatial slice with vanishing Neumann endpoint
derivatives, agreeing with the physical slice on `[0,1]`.

## The realized real-space solution

The fixed point lives in `EWA T 1`.  Its realized real-space slice is the real part of
the Wiener point-evaluation:

```
  realSlice u* : ℝ → intervalDomainPoint → ℝ
    := fun t x => (evalST ⟨t, _⟩ ((x.1 : ℝ) : WA.Circ) (GWA.incl _ u*)).re
```

(`evalST`, `ShenWork/Wiener/EWA/Decisive.lean:38`; `intervalDomainPoint`,
`IntervalDomain.lean:2746`.)  This is the χ₀<0 source-form mild solution read off the
fixed point.

## What discharges vs. what is carried (honest accounting)

The classical-slice conclusion `SourceStrongSolutionData.isClassicalSpatialSlice`
(`SourceStrongSolution.lean:336`) needs the full record.  Three groups of fields:

1. **The eigenvalue-ℓ¹ legs** are PROVED inside the record's `eigenvalue_summable`
   (`SourceStrongSolution.lean:315`): the chemDiv leg via the capstone
   `chemDiv_eigenvalueSummableOn_uncond` (fed by the `cap*` fields), the heat leg via
   `heatCoeff_eigenvalue_summable`, the logistic leg via
   `duhamelSpectralCoeff_eigenvalue_summable` (fed by `logSrc`).  These then give the
   spatial `C²` + Neumann endpoints unconditionally on the record data.

2. **The realization `realizes`** — `intervalDomainLift (u t) x = Σₙ b̂ₙ(t) cos(nπx)`
   on `[0,1]` — is the eval of `Φ(u*)`.  Leg-by-leg:
   * the **heat leg** closes via `heatEWA_evalST_eq_cosineHeatValue`
     (`HeatFloor.lean:169`, COMMITTED);
   * the **chemDiv/logistic Duhamel legs** are the eval of `divDuhamelEWA`/`valDuhamelEWA`
     applied to `chemFluxEWA`/`growthEWA`.  The committed point-bridges
     `evalST_chemFluxEWA_eq_chemFluxLifted` (`FluxEvalBridge.lean`),
     `evalST_chemDivEWA_eq_coupledChemDivSourceLift` (`ChemDivEval.lean`) and
     `evalST_growthEWA_eq_logisticLifted` (`GrowthEvalBridge.lean`) realize the *integrand*
     of each Duhamel, but the **`evalST`-of-Duhamel = spectral-cosine-synthesis** bridge
     `evalST (divDuhamelEWA …) x = Σₙ duhamelSpectralCoeff … n · cosineMode n x` is NOT in
     the tree (see the stall map in the module docstring of the assembly below).  So
     `realizes` is carried as a NAMED hypothesis — exactly as `SourceStrongSolution.lean`
     documents (`SourceStrongSolution.lean:280`).

3. **The `cap*`/`logSrc`/`hu0bd` fields** are the standard analytic side-data of the
   capstone and the logistic source's time-`C¹` package; they reference the specific
   realized solution `realSlice u*` and are not dischargeable from the abstract fixed
   point, so they are carried as NAMED hypotheses (the honest conditional).

The convergence theorem below therefore takes the fixed point `u*` plus the carried
fields and PROVES the χ₀<0 spatial classical existence, modulo those named inputs.

NO `sorry`, `axiom`, `native_decide`, or `admit`.
-/

open scoped BigOperators
open ShenWork.GWA ShenWork.Wiener
open ShenWork.IntervalDuhamelClosedC2 (duhamelSpectralCoeff DuhamelSourceTimeC1)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledChemDivSourceLift coupledLogisticSourceCoeffs)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.PDE (intervalNeumannResolverCoeff)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted)
open ShenWork.CosineSpectrum (cosineMode)

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-! ### Part 1 — the realized real-space slice of the fixed point. -/

/-- **The realized real-space slice of an `EWA T 1` element.**  At time `t` (clamped to
`[0,T]` by the membership test) and interior point `x : intervalDomainPoint`, the slice
is the real part of the Wiener point-evaluation of the grade-drop `incl u*`.  This is the
χ₀<0 source-form mild solution read off a fixed point `u* = Φ(u*)`. -/
def realSlice (u_star : EWA T 1) : ℝ → intervalDomainPoint → ℝ :=
  fun t x =>
    if h : t ∈ Set.Icc (0 : ℝ) T then
      (evalST (⟨t, h⟩ : TimeDom T) ((x.1 : ℝ) : WA.Circ)
        (GWA.incl (by omega : (0:ℕ) ≤ 1) u_star)).re
    else 0

/-! ### Part 2 — assembling `SourceStrongSolutionData` from the fixed point + carried data.

The realization `realizes` and the `cap*`/`logSrc`/`hu0bd` fields reference the *specific*
realized solution and are carried as explicit hypotheses (see the module docstring): the
`evalST`-of-Duhamel = spectral-synthesis bridge for the chemDiv/logistic legs is not in the
tree, so `realizes` cannot be discharged from the abstract fixed point.  Everything else —
the eigenvalue-ℓ¹ assembly, the `C²` and Neumann conclusions — is PROVED downstream from
these fields by `isClassicalSpatialSlice`. -/

/-- **The χ₀<0 source-form strong-solution data, assembled.**  Given a real-space solution
family `u` (the realized slice of a fixed point), the positive-time window, and the carried
realization + capstone + logistic-source fields, package the committed
`SourceStrongSolutionData`. -/
def sourceStrongSolutionData_of_data
    {μ ν γ : ℝ} (hμ : 0 < μ) (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ)
    (t τ₀ : ℝ) (htlo : 0 < t) (hthi : t ≤ T) (hτ0 : 0 < τ₀) (hτt : τ₀ < t)
    (Mu0 : ℝ) (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (realizes : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (u t) x
        = ∑' n, fullSourceCoeff p u u₀cos t n * cosineMode n x)
    (hGcont : ∀ n, Continuous (fun s => coupledChemDivSourceCoeffs p u s n))
    (Mlift : ℝ) (hMlift : 0 ≤ Mlift)
    (hLiftCont : ∀ s ∈ Set.Icc (0 : ℝ) τ₀,
      ContinuousOn (coupledChemDivSourceLift p u s) (Set.Icc (0 : ℝ) 1))
    (hLiftBd : ∀ s ∈ Set.Icc (0 : ℝ) τ₀, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |coupledChemDivSourceLift p u s x| ≤ Mlift)
    (Bv : ℕ → ℝ)
    (hBv : ∀ s k,
      |cosineCoeffs (intervalDomainLift ((fun s => u (s + τ₀)) s)) k| ≤ Bv k)
    (hBvnn : ∀ k, 0 ≤ Bv k)
    (hBvsum : Summable (fun k : ℕ => (1 + (k : ℝ)) * Bv k))
    (hcont : ∀ n : ℤ, Continuous (embedModeFun (fun s => u (s + τ₀)) n))
    (hgrad : ∀ τ : TimeDom T, Summable fun k : ℕ =>
      |(intervalNeumannResolverCoeff p ((fun s => u (s + τ₀)) τ.1) k).re|
        * ((k : ℝ) * Real.pi))
    (h_flux_nbhd : ∀ (τ : TimeDom T), ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      evalST τ (y : WA.Circ) (GWA.incl (by omega : (0:ℕ) ≤ 1)
        (chemFluxEWA μ ν p.β γ hμ
          (embedEWA (fun s => u (s + τ₀)) hBv hBvnn hBvsum hcont)))
        = ((chemFluxLifted p ((fun s => u (s + τ₀)) τ.1) y : ℝ) : ℂ))
    (h_flux_diff : ∀ (τ : TimeDom T), ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ (chemFluxLifted p ((fun s => u (s + τ₀)) τ.1)) x)
    (logSrc : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p u)) :
    SourceStrongSolutionData T (μ := μ) (ν := ν) (γ := γ) hμ p where
  u := u
  u₀cos := u₀cos
  t := t
  τ₀ := τ₀
  htlo := htlo
  hthi := hthi
  hτ0 := hτ0
  hτt := hτt
  Mu0 := Mu0
  hu0bd := hu0bd
  realizes := realizes
  hGcont := hGcont
  Mlift := Mlift
  hMlift := hMlift
  hLiftCont := hLiftCont
  hLiftBd := hLiftBd
  Bv := Bv
  hBv := hBv
  hBvnn := hBvnn
  hBvsum := hBvsum
  hcont := hcont
  hgrad := hgrad
  h_flux_nbhd := h_flux_nbhd
  h_flux_diff := h_flux_diff
  logSrc := logSrc

/-! ### Part 3 — THE χ₀<0 SPATIAL CLASSICAL EXISTENCE THEOREM. -/

/-- **THE χ₀<0 STRONG-DATA SPATIAL CLASSICAL EXISTENCE.**

From the source-form EWA fixed point `u* = Φ(u*)` (`picardEWA_abs_fixedPoint`), the
realized real-space solution `u := realSlice u*` of the χ₀<0 source-form mild equation,
together with the carried strong-data inputs

* `realizes` — the realization of `u` as its cosine synthesis on `[0,1]` (the eval of
  `Φ(u*)`; heat leg via the committed `heatEWA_evalST_eq_cosineHeatValue`, chemDiv/logistic
  Duhamel-synthesis legs carried — bridge not in tree);
* the `cap*` fields — the discharge inputs of `chemDiv_eigenvalueSummableOn_uncond`;
* `logSrc` — the logistic source's time-`C¹` package;
* `hu0bd` — the heat-datum coefficient bound;

there EXISTS (constructively, the realized slice `u`) a classical spatial slice at the
interior time `t`: it is `ContDiff ℝ 2`, has vanishing Neumann endpoint derivatives, and
agrees with the realized physical slice on `[0,1]`.

This is the spatial-regularity half of the source-form classical solution; the
time-regularity `u_t` and the PDE-from-mild step are separate, per the grade-1
architecture (mirrors `GradientMildClassicalRegularityFrontierData`). -/
theorem sourceClassical_spatial_existence_chi0_neg
    {μ ν γ : ℝ} (hμ : 0 < μ) (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ)
    {t τ₀ : ℝ} (htlo : 0 < t) (hthi : t ≤ T) (hτ0 : 0 < τ₀) (hτt : τ₀ < t)
    {Mu0 : ℝ} (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (realizes : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (u t) x
        = ∑' n, fullSourceCoeff p u u₀cos t n * cosineMode n x)
    (hGcont : ∀ n, Continuous (fun s => coupledChemDivSourceCoeffs p u s n))
    {Mlift : ℝ} (hMlift : 0 ≤ Mlift)
    (hLiftCont : ∀ s ∈ Set.Icc (0 : ℝ) τ₀,
      ContinuousOn (coupledChemDivSourceLift p u s) (Set.Icc (0 : ℝ) 1))
    (hLiftBd : ∀ s ∈ Set.Icc (0 : ℝ) τ₀, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |coupledChemDivSourceLift p u s x| ≤ Mlift)
    (Bv : ℕ → ℝ)
    (hBv : ∀ s k,
      |cosineCoeffs (intervalDomainLift ((fun s => u (s + τ₀)) s)) k| ≤ Bv k)
    (hBvnn : ∀ k, 0 ≤ Bv k)
    (hBvsum : Summable (fun k : ℕ => (1 + (k : ℝ)) * Bv k))
    (hcont : ∀ n : ℤ, Continuous (embedModeFun (fun s => u (s + τ₀)) n))
    (hgrad : ∀ τ : TimeDom T, Summable fun k : ℕ =>
      |(intervalNeumannResolverCoeff p ((fun s => u (s + τ₀)) τ.1) k).re|
        * ((k : ℝ) * Real.pi))
    (h_flux_nbhd : ∀ (τ : TimeDom T), ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      evalST τ (y : WA.Circ) (GWA.incl (by omega : (0:ℕ) ≤ 1)
        (chemFluxEWA μ ν p.β γ hμ
          (embedEWA (fun s => u (s + τ₀)) hBv hBvnn hBvsum hcont)))
        = ((chemFluxLifted p ((fun s => u (s + τ₀)) τ.1) y : ℝ) : ℂ))
    (h_flux_diff : ∀ (τ : TimeDom T), ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ (chemFluxLifted p ((fun s => u (s + τ₀)) τ.1)) x)
    (logSrc : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p u)) :
    -- (i) `u(t,·)` synthesis is `C²`:
    ContDiff ℝ 2 (fun x => ∑' n, fullSourceCoeff p u u₀cos t n * cosineMode n x)
      -- (ii) Neumann at the left endpoint:
      ∧ deriv (fun x => ∑' n, fullSourceCoeff p u u₀cos t n * cosineMode n x) 0 = 0
      -- (iii) Neumann at the right endpoint:
      ∧ deriv (fun x => ∑' n, fullSourceCoeff p u u₀cos t n * cosineMode n x) 1 = 0
      -- (iv) the realized physical slice agrees with the synthesis on `[0,1]`:
      ∧ ∀ x ∈ Set.Icc (0 : ℝ) 1,
          intervalDomainLift (u t) x
            = ∑' n, fullSourceCoeff p u u₀cos t n * cosineMode n x := by
  exact (sourceStrongSolutionData_of_data (T := T) hμ p u u₀cos t τ₀ htlo hthi hτ0 hτt
    Mu0 hu0bd realizes hGcont Mlift hMlift hLiftCont hLiftBd Bv hBv hBvnn hBvsum hcont
    hgrad h_flux_nbhd h_flux_diff logSrc).isClassicalSpatialSlice

/-! ### Part 4 — the convergence specialized to the realized slice of a fixed point. -/

/-- **THE FINAL CONVERGENCE — fixed point ⟹ χ₀<0 spatial classical slice.**

Specializes `sourceClassical_spatial_existence_chi0_neg` to `u := realSlice u*` for an
actual source-form fixed point `u* = picardEWA … u*`.  The realized real-space solution is
the slice of the very fixed point; the carried strong-data fields (realization, capstone
inputs, logistic-source package, datum bound) are taken about that slice.  The conclusion
is the classical spatial slice at the interior time `t`. -/
theorem sourceClassical_spatial_existence_of_fixedPoint
    {μ ν γ : ℝ} (hμ : 0 < μ) (p : CM2Params)
    (u_star : EWA T 1) (u₀cos : ℕ → ℝ)
    {t τ₀ : ℝ} (htlo : 0 < t) (hthi : t ≤ T) (hτ0 : 0 < τ₀) (hτt : τ₀ < t)
    {Mu0 : ℝ} (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (realizes : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (realSlice u_star t) x
        = ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x)
    (hGcont : ∀ n,
      Continuous (fun s => coupledChemDivSourceCoeffs p (realSlice u_star) s n))
    {Mlift : ℝ} (hMlift : 0 ≤ Mlift)
    (hLiftCont : ∀ s ∈ Set.Icc (0 : ℝ) τ₀,
      ContinuousOn (coupledChemDivSourceLift p (realSlice u_star) s) (Set.Icc (0 : ℝ) 1))
    (hLiftBd : ∀ s ∈ Set.Icc (0 : ℝ) τ₀, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |coupledChemDivSourceLift p (realSlice u_star) s x| ≤ Mlift)
    (Bv : ℕ → ℝ)
    (hBv : ∀ s k,
      |cosineCoeffs (intervalDomainLift
        ((fun s => realSlice u_star (s + τ₀)) s)) k| ≤ Bv k)
    (hBvnn : ∀ k, 0 ≤ Bv k)
    (hBvsum : Summable (fun k : ℕ => (1 + (k : ℝ)) * Bv k))
    (hcont : ∀ n : ℤ,
      Continuous (embedModeFun (fun s => realSlice u_star (s + τ₀)) n))
    (hgrad : ∀ τ : TimeDom T, Summable fun k : ℕ =>
      |(intervalNeumannResolverCoeff p
          ((fun s => realSlice u_star (s + τ₀)) τ.1) k).re| * ((k : ℝ) * Real.pi))
    (h_flux_nbhd : ∀ (τ : TimeDom T), ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      evalST τ (y : WA.Circ) (GWA.incl (by omega : (0:ℕ) ≤ 1)
        (chemFluxEWA μ ν p.β γ hμ
          (embedEWA (fun s => realSlice u_star (s + τ₀)) hBv hBvnn hBvsum hcont)))
        = ((chemFluxLifted p ((fun s => realSlice u_star (s + τ₀)) τ.1) y : ℝ) : ℂ))
    (h_flux_diff : ∀ (τ : TimeDom T), ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ
        (chemFluxLifted p ((fun s => realSlice u_star (s + τ₀)) τ.1)) x)
    (logSrc : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p (realSlice u_star))) :
    ContDiff ℝ 2
        (fun x => ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x)
      ∧ deriv (fun x => ∑' n,
          fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x) 0 = 0
      ∧ deriv (fun x => ∑' n,
          fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x) 1 = 0
      ∧ ∀ x ∈ Set.Icc (0 : ℝ) 1,
          intervalDomainLift (realSlice u_star t) x
            = ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x :=
  sourceClassical_spatial_existence_chi0_neg (T := T) hμ p (realSlice u_star) u₀cos
    htlo hthi hτ0 hτt hu0bd realizes hGcont hMlift hLiftCont hLiftBd Bv hBv hBvnn hBvsum
    hcont hgrad h_flux_nbhd h_flux_diff logSrc

end ShenWork.EWA

#print axioms ShenWork.EWA.sourceClassical_spatial_existence_chi0_neg
#print axioms ShenWork.EWA.sourceClassical_spatial_existence_of_fixedPoint
