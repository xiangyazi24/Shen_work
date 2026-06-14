import ShenWork.Wiener.EWA.ChemDivViaR2
import ShenWork.Wiener.EWA.ChemDivFinal
import ShenWork.Paper2.IntervalMildPicardRegularity

/-!
# chemDiv eigenvalue-ℓ¹ summability — the unconditional/window-regularity discharge

This file builds `chemDiv_eigenvalueSummableOn_uncond`, the SAME windowed
conclusion as `chemDiv_eigenvalueSummableOn_viaR2`
(`ChemDivViaR2.lean`), but with the THREE shallow R2 inputs discharged as far as
the committed library allows, so that what remains are ONLY honest
solution-regularity hypotheses (no `Mdot`/`adot`/`B8`, no all-`s` `A¹` over the
closed `[0,T]`, no manufactured polynomial bound).

The three R2 inputs and their fate here:

* **(II) the EARLY polynomial bound** is *fully discharged* from the committed
  `cosineCoeffs_abs_le_of_continuous_bounded`
  (`ShenWork.IntervalMildPicardRegularity`, `IntervalMildPicardRegularity.lean:837`):
  since `coupledChemDivSourceCoeffs p u s n = cosineCoeffs (lift) n`
  *definitionally*, a `ContinuousOn`+sup-bound `M` on `[0,τ₀]×[0,1]` of the source
  lift forces `|coeff n| ≤ 2·M ≤ 2·M·(1+n)`.  The `[0,τ₀]` spatial regularity of
  the chemDiv source lift is the committed `C²` slice data, here a NAMED
  hypothesis (`hLiftCont`, `hLiftBd`).

* **(I) the WINDOW `A⁰` envelope** is *fully discharged* via the TIME-SHIFT route.
  `coupledChemDivSourceCoeffs p u s n` is **time-local** — it depends only on the
  slice `u s` (verified: `coupledChemDivSourceCoeffs → coupledChemDivSourceLift →
  intervalDomainChemotaxisDiv (u s) (intervalNeumannResolverR (u s))`, NO time
  integral / history).  Hence the time-shift identity
  `coupledChemDivSourceCoeffs p (u ∘ (·+τ₀)) r n = coupledChemDivSourceCoeffs p u
  (r+τ₀) n` holds DEFINITIONALLY (`rfl`).  With `ũ := u(·+τ₀)`, the committed EWA
  chain `embedEWA ũ → chemDivEWA → sourceEnvelope` gives a summable envelope `E`
  (via `sourceEnvelope_summable`) bounding `|coupledChemDivSourceCoeffs p ũ r n|`
  on `[0,T]` (via `chemDiv_coeff_bound_of_EWA`), which the shift identity transports
  to the window `[τ₀,t]` for `u`.  The `embedEWA`/eval-bridge inputs are taken for
  the SHIFTED trajectory `ũ` — legitimately available OFF the `t=0` wall.

* **(III) per-mode time-continuity** `hGcont` is *carried as a hypothesis*: there
  is no committed lemma giving `Continuous (fun s => coupledChemDivSourceCoeffs p u
  s n)` for a general solution; it is genuine solution time-regularity.

NO `sorry`, `axiom`, `native_decide`, or `admit`.
-/

open scoped BigOperators
open MeasureTheory
open ShenWork.GWA ShenWork.Wiener
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledChemDivSourceLift)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.PDE (intervalNeumannResolverCoeff)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted)

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-- **Time-shift identity (from time-locality).**

`coupledChemDivSourceCoeffs p u s n` depends only on the time slice `u s` (no time
integral / history in its definition chain `coupledChemDivSourceLift →
intervalDomainChemotaxisDiv (u s) (intervalNeumannResolverR (u s))`).  Consequently
the shifted trajectory `fun s => u (s + τ₀)` produces exactly the shifted
coefficients.  GENUINELY PROVEN — it is `rfl`. -/
theorem coupledChemDivSourceCoeffs_timeShift
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (τ₀ r : ℝ) (n : ℕ) :
    coupledChemDivSourceCoeffs p (fun s => u (s + τ₀)) r n
      = coupledChemDivSourceCoeffs p u (r + τ₀) n := rfl

/-- **(II) discharge — the EARLY polynomial bound from spatial regularity.**

From a `ContinuousOn`+sup bound of the chemDiv source lift on `[0,τ₀]×[0,1]`,
the early-window coefficients satisfy `|coupledChemDivSourceCoeffs p u s n| ≤
(2·M)·(1+n)`.  Uses the committed `cosineCoeffs_abs_le_of_continuous_bounded`. -/
theorem chemDiv_earlyPoly_of_liftRegularity
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    {τ₀ M : ℝ} (hM : 0 ≤ M)
    (hLiftCont : ∀ s ∈ Set.Icc (0 : ℝ) τ₀,
      ContinuousOn (coupledChemDivSourceLift p u s) (Set.Icc (0 : ℝ) 1))
    (hLiftBd : ∀ s ∈ Set.Icc (0 : ℝ) τ₀, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |coupledChemDivSourceLift p u s x| ≤ M) :
    ∀ s ∈ Set.Icc (0 : ℝ) τ₀, ∀ n,
      |coupledChemDivSourceCoeffs p u s n| ≤ (2 * M) * (1 + (n : ℝ)) := by
  intro s hs n
  have hbase :
      |coupledChemDivSourceCoeffs p u s n| ≤ 2 * M :=
    ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
      (hLiftCont s hs) hM (hLiftBd s hs) n
  have h1n : (1 : ℝ) ≤ 1 + (n : ℝ) := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have h2M : (0 : ℝ) ≤ 2 * M := by linarith
  calc |coupledChemDivSourceCoeffs p u s n|
      ≤ 2 * M := hbase
    _ = (2 * M) * 1 := by ring
    _ ≤ (2 * M) * (1 + (n : ℝ)) := mul_le_mul_of_nonneg_left h1n h2M

/-- **(I) discharge — the WINDOW envelope via the time-shift.**

For the shifted trajectory `ũ := u(·+τ₀)`, the committed EWA chain
`embedEWA ũ → chemDivEWA → sourceEnvelope` supplies a summable envelope `E`
dominating `|coupledChemDivSourceCoeffs p ũ r n|` on `[0,T]`.  The time-shift
identity transports this to the window `[τ₀,t]` for `u`, since
`coupledChemDivSourceCoeffs p u s n = coupledChemDivSourceCoeffs p ũ (s-τ₀) n`. -/
theorem chemDiv_windowEnvelope_of_shiftEWA
    {μ ν γ : ℝ} (hμ : 0 < μ) (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ)
    {t τ₀ : ℝ} (hthi : t ≤ T) (hτ0 : 0 ≤ τ₀) (_hτt : τ₀ ≤ t)
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
      DifferentiableAt ℝ (chemFluxLifted p ((fun s => u (s + τ₀)) τ.1)) x) :
    ∃ E : ℕ → ℝ, (∀ n, 0 ≤ E n) ∧ Summable E ∧
      ∀ s ∈ Set.Icc τ₀ t, ∀ n,
        |coupledChemDivSourceCoeffs p u s n| ≤ E n := by
  set ũ : ℝ → intervalDomainPoint → ℝ := fun s => u (s + τ₀) with hũ_def
  set U : EWA T 1 := embedEWA ũ hBv hBvnn hBvsum hcont with hU_def
  set E : ℕ → ℝ := sourceEnvelope (chemDivEWA μ ν γ hμ p U) with hE_def
  refine ⟨E, ?_, ?_, ?_⟩
  · intro n; rw [hE_def]; exact add_nonneg (norm_nonneg _) (norm_nonneg _)
  · rw [hE_def]; exact sourceEnvelope_summable _
  · intro s hs n
    -- transport via the time-shift identity: `s = (s-τ₀)+τ₀`, `s-τ₀ ∈ [0,T]`.
    have hU_even : EvenRealEWA U := embedEWA_evenReal ũ hBv hBvnn hBvsum hcont
    have h_eval : ∀ (τ : TimeDom T) (x : ℝ), x ∈ Set.Ioo (0 : ℝ) 1 →
        evalST τ (x : WA.Circ) (chemDivEWA μ ν γ hμ p U)
          = ((coupledChemDivSourceLift p ũ τ.1 x : ℝ) : ℂ) := by
      intro τ x hx
      have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hx
      exact evalST_chemDivEWA_eq_coupledChemDivSourceLift hμ p ũ U τ x hx hxIcc
        (hgrad τ) (h_flux_nbhd τ) (h_flux_diff τ x hx)
    -- the shifted slice `r := s - τ₀ ∈ [0,T]`.
    have hr_mem : s - τ₀ ∈ Set.Icc (0 : ℝ) T := by
      constructor
      · linarith [hs.1]
      · linarith [hs.2, hthi]
    have hbound :
        |coupledChemDivSourceCoeffs p ũ (s - τ₀) n| ≤ E n := by
      rw [hE_def]
      exact chemDiv_coeff_bound_of_EWA hμ p ũ U hU_even h_eval (s - τ₀) hr_mem n
    have hshift :
        coupledChemDivSourceCoeffs p ũ (s - τ₀) n
          = coupledChemDivSourceCoeffs p u s n := by
      have := coupledChemDivSourceCoeffs_timeShift p u τ₀ (s - τ₀) n
      rw [hũ_def]
      rw [this]
      congr 1
      ring
    rw [← hshift]; exact hbound

/-- **chemDiv eigenvalue-ℓ¹ summability — the discharged form.**

For a fixed interior time `t ∈ (0, T]`, the eigenvalue-weighted Duhamel spectral
coefficients of the chemotaxis-divergence source are summable.

Compared to `chemDiv_eigenvalueSummableOn_viaR2`:

* **(II)** the early polynomial bound is DISCHARGED from
  `cosineCoeffs_abs_le_of_continuous_bounded` (`C := 2·M`), reducing it to the
  committed `[0,τ₀]×[0,1]` spatial regularity of the source lift (`hLiftCont`,
  `hLiftBd`);
* **(I)** the window envelope is DISCHARGED via the time-shift onto the committed
  `embedEWA → chemDivEWA → sourceEnvelope` chain for `ũ := u(·+τ₀)`
  (`Bv`, `hBv`, …, `h_flux_diff` — the SHIFTED `A¹`/eval-bridge inputs, available
  off the `t=0` wall);
* **(III)** the per-mode time-continuity `hGcont` is CARRIED — no committed lemma
  exists for a general solution.

NO `Mdot`/`adot`/`B8`, NO all-`s` `A¹` over the closed `[0,T]`, NO manufactured
polynomial bound. -/
theorem chemDiv_eigenvalueSummableOn_uncond
    {μ ν γ : ℝ} (hμ : 0 < μ) (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ)
    {t τ₀ : ℝ} (htlo : 0 < t) (hthi : t ≤ T)
    (hτ0 : 0 < τ₀) (hτt : τ₀ < t)
    -- (III) per-mode time-continuity (carried — genuine solution time-regularity):
    (hGcont : ∀ n, Continuous (fun s => coupledChemDivSourceCoeffs p u s n))
    -- (II) early-window spatial regularity (discharges the polynomial bound):
    {M : ℝ} (hM : 0 ≤ M)
    (hLiftCont : ∀ s ∈ Set.Icc (0 : ℝ) τ₀,
      ContinuousOn (coupledChemDivSourceLift p u s) (Set.Icc (0 : ℝ) 1))
    (hLiftBd : ∀ s ∈ Set.Icc (0 : ℝ) τ₀, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |coupledChemDivSourceLift p u s x| ≤ M)
    -- (I) shifted A¹/eval-bridge inputs (discharge the window envelope, off the wall):
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
      DifferentiableAt ℝ (chemFluxLifted p ((fun s => u (s + τ₀)) τ.1)) x) :
    Summable (fun n => unitIntervalCosineEigenvalue n *
      |∫ s in (0 : ℝ)..t,
        Real.exp (-(t - s) * unitIntervalCosineEigenvalue n)
          * coupledChemDivSourceCoeffs p u s n|) := by
  -- (II): early polynomial bound from spatial regularity (C := 2·M).
  have hpoly : ∀ s ∈ Set.Icc (0 : ℝ) τ₀, ∀ n,
      |coupledChemDivSourceCoeffs p u s n| ≤ (2 * M) * (1 + (n : ℝ)) :=
    chemDiv_earlyPoly_of_liftRegularity p u hM hLiftCont hLiftBd
  -- (I): window envelope from the time-shifted EWA chain.
  obtain ⟨E, hE_nonneg, hE_summable, hE_bound⟩ :=
    chemDiv_windowEnvelope_of_shiftEWA hμ p u hthi hτ0.le hτt.le
      Bv hBv hBvnn hBvsum hcont hgrad h_flux_nbhd h_flux_diff
  -- Assemble via the committed split-integral route R2.
  exact chemDiv_eigenvalueSummableOn_viaR2 p u htlo hthi hτ0 hτt
    hGcont E hE_nonneg hE_bound hE_summable (2 * M) (by linarith) hpoly

end ShenWork.EWA

#print axioms ShenWork.EWA.chemDiv_eigenvalueSummableOn_uncond
