# Q2878 (shen1) — component PDE-term bridge for weighted-time initial integrability

Repo: `xiangyazi24/Shen_work`  
Delivery branch: `chatgpt-scratch`  
Source edit requested: none; answer file only.

## Executive answer

Yes.  The no-sorry bridge should use the compiled pointwise PDE-integral identity

```lean
intervalDomain_lp_energy_hPDEIntegral_of_regularity
```

which has sign/convention:

```lean
intervalDomain.integral (intervalDomainLpEnergyWeightedTimeTerm q u s) =
  intervalDomainLpDiffusionIntegral q u s -
    params.χ₀ * intervalDomainLpChemotaxisIntegral params q u v s +
    intervalDomainLpLogisticIntegral params q u s
```

Therefore, after multiplying by `q`, the component residual should require integrability of:

```lean
q * Diffusion
q * (params.χ₀ * Chemotaxis)
q * Logistic
```

Then the weighted time-term integrability follows by `(hDiff.sub hChem).add hLog` plus `IntervalIntegrable.congr` on `uIoc 0 b`.  To avoid the `s < T` endpoint problem when `b = T`, apply global classical on horizon `s + 1` for every `s > 0`.

## Code to add

Put this in `ShenWork/PDE/P3MoserEnergyContinuity.lean`, after the weighted residual from Q2877.  If the imports are already present because this is the same file, only add the declarations inside the existing namespace.

```lean
import ShenWork.PDE.P3MoserEnergyContinuity
import Mathlib.Tactic

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity

/-- Initial-window integrability residual for the three PDE terms in the weighted
Lp time identity.

The chemotaxis term is recorded without the minus sign, as
`q * (params.χ₀ * Chemotaxis)`, because the bridge will use `.sub` to build
`q * Diffusion - q * (χ₀ * Chemotaxis) + q * Logistic`. -/
def IntervalDomainLpPDETermInitialWindowIntegrability
    (params : CM2Params) (u v : ℝ → intervalDomain.Point → ℝ)
    (T p0 : ℝ) : Prop :=
  ∀ q, p0 ≤ q →
    ∀ b ∈ Set.Icc (0 : ℝ) T,
      IntervalIntegrable
        (fun s => q * intervalDomainLpDiffusionIntegral q u s)
        volume 0 b ∧
      IntervalIntegrable
        (fun s =>
          q * (params.χ₀ *
            intervalDomainLpChemotaxisIntegral params q u v s))
        volume 0 b ∧
      IntervalIntegrable
        (fun s => q * intervalDomainLpLogisticIntegral params q u s)
        volume 0 b

/-- Pointwise scaled PDE-integral identity for the weighted time term at a
positive time, using global classical regularity on the horizon `s + 1`.

This avoids the endpoint issue from a fixed horizon `T`: for every `0 < s`, we
have `s < s + 1`. -/
theorem intervalDomain_weightedTimeTerm_eq_pdeTerms_scaled_of_global_pos
    {params : CM2Params} {q s : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hs0 : 0 < s) :
    q * intervalDomain.integral
        (intervalDomainLpEnergyWeightedTimeTerm q u s) =
      q * intervalDomainLpDiffusionIntegral q u s -
        q * (params.χ₀ *
          intervalDomainLpChemotaxisIntegral params q u v s) +
        q * intervalDomainLpLogisticIntegral params q u s := by
  have hTpos : 0 < s + 1 := by linarith
  have hsol : IsPaper2ClassicalSolution intervalDomain params (s + 1) u v :=
    hglobal.classical hTpos
  have hpde :=
    intervalDomain_lp_energy_hPDEIntegral_of_regularity
      (params := params) (T := s + 1) (t := s) (pExp := q)
      (u := u) (v := v) hsol hs0 (by linarith)
  rw [hpde]
  ring

/-- No-sorry bridge from component initial-window integrability of the PDE terms
to initial-window integrability of the weighted Lp time term.

The congruence is over `uIoc 0 b`; after rewriting by `Set.uIoc_of_le hb.1`,
every relevant time has `0 < s`, so the pointwise global-classical identity
above applies.  This is robust when `b = 0`, since `Ioc 0 0` is empty. -/
theorem intervalDomain_weightedTimeTermInitialWindowIntegrability_of_pdeTerm_initial
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hterms : IntervalDomainLpPDETermInitialWindowIntegrability params u v T p0) :
    IntervalDomainLpWeightedTimeTermInitialWindowIntegrability u T p0 := by
  intro q hq b hb
  rcases hterms q hq b hb with ⟨hDiff, hChem, hLog⟩
  have hRHS :
      IntervalIntegrable
        (fun s =>
          q * intervalDomainLpDiffusionIntegral q u s -
            q * (params.χ₀ *
              intervalDomainLpChemotaxisIntegral params q u v s) +
            q * intervalDomainLpLogisticIntegral params q u s)
        volume 0 b :=
    (hDiff.sub hChem).add hLog
  refine IntervalIntegrable.congr ?_ hRHS
  intro s hs
  rw [Set.uIoc_of_le hb.1] at hs
  exact intervalDomain_weightedTimeTerm_eq_pdeTerms_scaled_of_global_pos
    (params := params) (q := q) (s := s) (u := u) (v := v)
    hglobal hs.1

end ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
```

## Why this is the thinnest component residual

The existing identity already proves the **spatial** insertion of the PDE into the weighted time term at each positive time.  What it does **not** prove is **time integrability near `0`** of the resulting three scalar profiles.  So the residual should not ask again for pointwise PDE identities; it should ask exactly for initial-window `IntervalIntegrable` facts for the three scalar terms.

The sign choice above is deliberate:

```lean
q * W = q * D - q * (χ₀ * C) + q * L
```

so the residual terms combine by:

```lean
(hDiff.sub hChem).add hLog
```

No positivity assumption is needed in this bridge because `intervalDomain_lp_energy_hPDEIntegral_of_regularity` is already an identity for the weighted term and the PDE terms.  Positivity was only needed one layer earlier, when converting the plain power-derivative integral to the weighted time term.
