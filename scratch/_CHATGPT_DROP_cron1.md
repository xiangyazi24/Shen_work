# Q1833 (cron1) -- `srcSlice1` tail coefficient bound

Repository: `xiangyazi24/Shen_work`  
Committed branch: `chatgpt-scratch`  
Target report file: `scratch/_CHATGPT_DROP_cron1.md`

## Scope and caveat

The prompt was only:

```text
Q1833 (cron1): cron1 /tmp/q_cron1_srcslice1.txt
```

The local file `/tmp/q_cron1_srcslice1.txt` was not present in the runtime I can inspect, and it is not readable through the GitHub connector. I used the current repo state and the previous `Rderiv` chain to infer the intended target.

I did **not** use Python, `/mnt/data`, the sandbox, or a sandbox link. I did not run Lean locally.

## Current target in `main`

The relevant file is:

```text
ShenWork/Paper2/IntervalHeatResolverJointC2.lean
```

The mechanical derivative assembly from Q1814 has effectively landed: the file now has

```lean
theorem heatLevel0_srcTimeCoeff_hasDerivAt ...
theorem heatLevel0_resolverTimeCoeff_deriv_eq ...
```

and the local `hR_deriv_bounded` block now reduces the resolver derivative to the `srcSlice1` coefficient.  The remaining local sorry is exactly:

```lean
have hBsrc : ∃ Bsrc : ℝ, ∀ t : ℝ, c + 1 < t →
    |cosineCoeffs (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t) k| ≤ Bsrc := by
  sorry -- ContinuousOn of srcSlice1 + L∞ bound via eigenvalue damping
```

## Verdict

The `hBsrc` proof should **not** be done by resolver eigenvalue damping.  This is a source-side bound:

```lean
srcSlice1 p u heatDu t x
  = p.ν * p.γ * (intervalDomainLift (u t) x) ^ (p.γ - 1) * heatDu u₀ t x
```

So the proof has three independent atoms:

1. `srcSlice1` time-slice is continuous on `[0,1]` from `heatSemigroup_d0`.
2. `heatDu u₀ t x` is uniformly bounded on the tail `t > c + 1` using the reciprocal-square estimate for the heat second derivative.
3. `(S(t)u₀)^(γ-1)` is uniformly bounded on the tail using both a **positive lower bound** and an upper `L∞` bound for the heat semigroup.

The old shortcut `M_sup^(γ-1)` is unsafe unless `1 ≤ γ`; here `CM2Params` only has `0 < γ`.

## One tiny API change first

In

```text
ShenWork/Paper2/IntervalHeatSemigroupFlooredSourceTimeData.lean
```

make the existing theorem public.  Its proof body already exists and should not change.

Change:

```lean
private theorem heatDu_eq_secondValue
```

to:

```lean
theorem heatDu_eq_secondValue
```

Reason: `hBsrc` is in `IntervalHeatResolverJointC2.lean`, but the needed rewrite

```lean
heatDu u₀ t x = unitIntervalCosineHeatSecondValue t (cosineCoeffs (intervalDomainLift u₀)) x
```

is currently private to `IntervalHeatSemigroupFlooredSourceTimeData.lean`.

Then update the open list in `IntervalHeatResolverJointC2.lean`:

```lean
open ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData
  (heatDu heatD2u heatSemigroup_d0 heatSemigroup_d1 heatDu_eq_secondValue)
```

## Helper 1: continuity of the `srcSlice1` time slice

Add this in `IntervalHeatResolverJointC2.lean`, near the `Layer 1b` source/resolver derivative helpers.

```lean
import ShenWork.Paper2.IntervalHeatResolverJointC2
import ShenWork.PDE.IntervalDomainRegularityBootstrap

open Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalPhysicalSourceTimeC2Concrete (srcSlice)
open ShenWork.IntervalFlooredSourceTimeDataIterate (srcSlice1)
open ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData
  (heatDu heatSemigroup_d0 heatDu_eq_secondValue)

namespace ShenWork.Paper2.HeatResolverJointC2Direct

private theorem heatLevel0_srcSlice1_timeSlice_continuousOn
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ t : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    (ht : 0 < t) :
    ContinuousOn
      (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t)
      (Set.Icc (0 : ℝ) 1) := by
  obtain ⟨δ, hδ, _hsrc, _hdiff, hjoint⟩ :=
    heatSemigroup_d0 (p := p) (u₀ := u₀) (M₀ := M₀)
      hu₀_bound hu₀_cont hfloor t ht
  have htIcc : t ∈ Set.Icc (t - δ) (t + δ) := by
    exact ⟨by linarith, by linarith⟩
  simpa [Function.uncurry] using
    hjoint.comp (continuousOn_const.prodMk continuousOn_id)
      (fun x hx => Set.mem_prod.mpr ⟨htIcc, hx⟩)

end ShenWork.Paper2.HeatResolverJointC2Direct
```

This is the same slicing pattern already used inside `heatSemigroup_d0`.

## Helper 2: tail `L∞` bound for `heatDu`

This is the genuine heat-kernel/spectral estimate.  Put it in `IntervalHeatResolverJointC2.lean` or, better, in `IntervalHeatSemigroupFlooredSourceTimeData.lean` next to `heatDu_eq_secondValue`.

```lean
import ShenWork.Paper2.IntervalHeatResolverJointC2
import ShenWork.PDE.IntervalDomainRegularityBootstrap

open Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData
  (heatDu heatDu_eq_secondValue)

namespace ShenWork.Paper2.HeatResolverJointC2Direct

/-- Uniform tail `L∞` bound for the heat Laplacian `heatDu`.

Analytic content: after rewriting `heatDu` to
`unitIntervalCosineHeatSecondValue`, use
`unitIntervalCosineHeatSecondPointWeight_abs_le` and
`reciprocalSquareTerm_summable`. -/
private theorem heatDu_tail_linf_bound
    {u₀ : intervalDomainPoint → ℝ} {M₀ c : ℝ}
    (hc : 0 < c)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀) :
    ∃ CΔ : ℝ, 0 ≤ CΔ ∧
      ∀ t : ℝ, c + 1 < t → ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |heatDu u₀ t x| ≤ CΔ := by
  classical
  have htail_pos : 0 < c + 1 := by linarith
  have hM₀_nonneg : 0 ≤ M₀ := le_trans (abs_nonneg _) (hu₀_bound 0)
  let Cbase : ℝ := 4 / ((c + 1) ^ 2 * Real.pi ^ 2)
  have hCbase_nonneg : 0 ≤ Cbase := by
    dsimp [Cbase]
    positivity
  let S : ℝ := ∑' n : ℕ,
    ShenWork.IntervalDomainRegularityBootstrap.reciprocalSquareTerm n
  have hS_nonneg : 0 ≤ S := by
    -- Use `tsum_nonneg` and `reciprocalSquareTerm_summable`.
    dsimp [S]
    exact tsum_nonneg fun n => by
      unfold ShenWork.IntervalDomainRegularityBootstrap.reciprocalSquareTerm
      positivity
  refine ⟨Cbase * M₀ * S, by positivity, fun t ht x hx => ?_⟩
  have ht_pos : 0 < t := by linarith
  rw [heatDu_eq_secondValue u₀ ht_pos]
  unfold ShenWork.IntervalDomainRegularityBootstrap.unitIntervalCosineHeatSecondValue
  let term : ℕ → ℝ := fun n =>
    ShenWork.IntervalDomainRegularityBootstrap.unitIntervalCosineHeatSecondPointWeight t x n *
      cosineCoeffs (intervalDomainLift u₀) n
  have hterm_abs : ∀ n : ℕ,
      |term n| ≤ Cbase * M₀ *
        ShenWork.IntervalDomainRegularityBootstrap.reciprocalSquareTerm n := by
    intro n
    have hwt :=
      ShenWork.IntervalDomainRegularityBootstrap.unitIntervalCosineHeatSecondPointWeight_abs_le
        ht_pos x n
    have htime :
        4 / (t ^ 2 * Real.pi ^ 2) ≤ Cbase := by
      dsimp [Cbase]
      have hsq : (c + 1) ^ 2 ≤ t ^ 2 := by
        nlinarith [htail_pos, le_of_lt ht]
      have hden : (c + 1) ^ 2 * Real.pi ^ 2 ≤ t ^ 2 * Real.pi ^ 2 := by
        exact mul_le_mul_of_nonneg_right hsq (sq_nonneg Real.pi)
      have hden_pos : 0 < (c + 1) ^ 2 * Real.pi ^ 2 := by positivity
      have hden_t_pos : 0 < t ^ 2 * Real.pi ^ 2 := by positivity
      -- reciprocal monotonicity; `field_simp`/`nlinarith` closes this locally.
      exact div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 4) hden_pos hden
    have hcoeff : |cosineCoeffs (intervalDomainLift u₀) n| ≤ M₀ := hu₀_bound n
    have hrec_nonneg :
        0 ≤ ShenWork.IntervalDomainRegularityBootstrap.reciprocalSquareTerm n := by
      unfold ShenWork.IntervalDomainRegularityBootstrap.reciprocalSquareTerm
      positivity
    dsimp [term]
    rw [abs_mul]
    calc
      |ShenWork.IntervalDomainRegularityBootstrap.unitIntervalCosineHeatSecondPointWeight t x n| *
          |cosineCoeffs (intervalDomainLift u₀) n|
          ≤ ((4 / (t ^ 2 * Real.pi ^ 2)) *
              ShenWork.IntervalDomainRegularityBootstrap.reciprocalSquareTerm n) * M₀ := by
            exact mul_le_mul hwt hcoeff hM₀_nonneg
              (mul_nonneg (by positivity) hrec_nonneg)
      _ ≤ (Cbase * ShenWork.IntervalDomainRegularityBootstrap.reciprocalSquareTerm n) * M₀ := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right htime hrec_nonneg) hM₀_nonneg
      _ = Cbase * M₀ *
            ShenWork.IntervalDomainRegularityBootstrap.reciprocalSquareTerm n := by ring
  have hmaj_summable : Summable fun n : ℕ =>
      Cbase * M₀ * ShenWork.IntervalDomainRegularityBootstrap.reciprocalSquareTerm n := by
    simpa [mul_assoc] using
      (ShenWork.IntervalDomainRegularityBootstrap.reciprocalSquareTerm_summable.mul_left
        (Cbase * M₀))
  have hterm_summable : Summable term :=
    Summable.of_norm_bounded hmaj_summable (by
      intro n
      simpa [Real.norm_eq_abs] using hterm_abs n)
  calc
    |∑' n : ℕ, term n|
        ≤ ∑' n : ℕ, |term n| := abs_tsum_le_tsum_abs hterm_summable
    _ ≤ ∑' n : ℕ,
          Cbase * M₀ * ShenWork.IntervalDomainRegularityBootstrap.reciprocalSquareTerm n := by
          exact tsum_le_tsum hterm_abs
            (hterm_summable.abs)
            hmaj_summable
    _ = Cbase * M₀ * S := by
          dsimp [S]
          rw [← tsum_mul_left]
          congr 1
          funext n
          ring

end ShenWork.Paper2.HeatResolverJointC2Direct
```

If `abs_tsum_le_tsum_abs` has a slightly different name in this Mathlib snapshot, replace that line by the standard normed-group version already used elsewhere in the repo; the rest of the estimate is the important part.

## Helper 3: tail bound for `u^(γ-1)`

This is necessary because `p.γ - 1` can be negative.

```lean
import ShenWork.Paper2.IntervalHeatResolverJointC2

open Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)

namespace ShenWork.Paper2.HeatResolverJointC2Direct

/-- Uniform tail bound for `(S(t)u₀)^(γ-1)`.  Uses compact min/max of the
positive continuous initial datum and heat semigroup comparison. -/
private theorem heatLevel0_rpow_gamma_sub_one_tail_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x) :
    ∃ Cpow : ℝ, 0 ≤ Cpow ∧
      ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0 : ℝ) 1,
        (intervalDomainLift (conjugatePicardIter p u₀ 0 t) x) ^ (p.γ - 1) ≤ Cpow := by
  classical
  haveI : CompactSpace intervalDomainPoint :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  haveI : Nonempty intervalDomainPoint :=
    ⟨⟨0, Set.left_mem_Icc.mpr (by norm_num)⟩⟩
  obtain ⟨xmin, _, hmin⟩ := IsCompact.exists_isMinOn isCompact_univ
    Set.univ_nonempty hu₀_cont.continuousOn
  obtain ⟨xmax, _, hmax⟩ := IsCompact.exists_isMaxOn isCompact_univ
    Set.univ_nonempty hu₀_cont.norm.continuousOn
  let m : ℝ := u₀ xmin
  let M : ℝ := ‖u₀ xmax‖
  have hm_pos : 0 < m := hu₀_pos xmin
  have hM_nonneg : 0 ≤ M := norm_nonneg _
  have hlift_lower : ∀ y, y ∈ Set.Icc (0 : ℝ) 1 → m ≤ intervalDomainLift u₀ y := by
    intro y hy
    let yp : intervalDomainPoint := ⟨y, hy⟩
    unfold intervalDomainLift
    rw [dif_pos hy]
    exact hmin (Set.mem_univ yp)
  have hlift_bound : ∀ y, |intervalDomainLift u₀ y| ≤ M := by
    intro y
    unfold intervalDomainLift
    split_ifs with hy
    · let yp : intervalDomainPoint := ⟨y, hy⟩
      simpa [M] using hmax (Set.mem_univ yp)
    · simpa [M] using hM_nonneg
  have hmM : m ≤ M := by
    have hx : xmin.1 ∈ Set.Icc (0 : ℝ) 1 := xmin.2
    have hxmin_lift : intervalDomainLift u₀ xmin.1 = u₀ xmin := by
      simp [intervalDomainLift, hx]
    calc
      m = intervalDomainLift u₀ xmin.1 := by rw [hxmin_lift]
      _ ≤ |intervalDomainLift u₀ xmin.1| := le_abs_self _
      _ ≤ M := hlift_bound xmin.1
  have hcont_pow : ContinuousOn (fun r : ℝ => r ^ (p.γ - 1)) (Set.Icc m M) := by
    exact continuousOn_id.rpow_const (fun r hr =>
      Or.inl (ne_of_gt (lt_of_lt_of_le hm_pos hr.1)))
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont_pow
  refine ⟨max C 0, le_max_right _ _, fun t ht x hx => ?_⟩
  have hlift_meas : AEStronglyMeasurable (intervalDomainLift u₀) (ShenWork.IntervalDomain.intervalMeasure 1) :=
    ShenWork.IntervalDuhamelIntegrability.intervalDomainLift_aestronglyMeasurable_of_continuous
      hu₀_cont
  have hSt_lower : m ≤
      ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
        t (intervalDomainLift u₀) x :=
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_lower_bound
      ht hm_pos.le hmM hlift_meas hlift_lower hlift_bound x
  have hSt_upper_abs :
      |ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
        t (intervalDomainLift u₀) x| ≤ M :=
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
      ht hM_nonneg hlift_bound x
  have hdef : intervalDomainLift (conjugatePicardIter p u₀ 0 t) x =
      ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
        t (intervalDomainLift u₀) x := by
    unfold intervalDomainLift
    rw [dif_pos hx]
    simp only [conjugatePicardIter]
    rfl
  have hmem : intervalDomainLift (conjugatePicardIter p u₀ 0 t) x ∈ Set.Icc m M := by
    rw [hdef]
    exact ⟨hSt_lower, le_of_abs_le hSt_upper_abs⟩
  exact (hC _ hmem).trans (le_max_left _ _)

end ShenWork.Paper2.HeatResolverJointC2Direct
```

The `hdef` proof is the same definitional bridge already used in the `i = 0` branch of `cutoffResolverMajorant_bddAbove_direct`.

## Helper 4: pointwise and coefficient bounds for `srcSlice1`

After Helpers 1–3, the actual `hBsrc` theorem is short.

```lean
import ShenWork.Paper2.IntervalHeatResolverJointC2
import ShenWork.PDE.IntervalDomainRegularityBootstrap

open Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalFlooredSourceTimeDataIterate (srcSlice1)
open ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData
  (heatDu heatSemigroup_d0 heatDu_eq_secondValue)

namespace ShenWork.Paper2.HeatResolverJointC2Direct

private theorem heatLevel0_srcSlice1_tail_pointwise_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ c : ℝ}
    (hc : 0 < c)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x) :
    ∃ Bpt : ℝ, 0 ≤ Bpt ∧ ∀ t : ℝ, c + 1 < t → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t x| ≤ Bpt := by
  obtain ⟨CΔ, hCΔ_nonneg, hCΔ⟩ :=
    heatDu_tail_linf_bound (u₀ := u₀) (M₀ := M₀) (c := c) hc hu₀_bound
  obtain ⟨Cpow, hCpow_nonneg, hCpow⟩ :=
    heatLevel0_rpow_gamma_sub_one_tail_bound (p := p) (u₀ := u₀)
      hu₀_cont hu₀_pos
  let Bpt : ℝ := p.ν * p.γ * Cpow * CΔ
  have hBpt_nonneg : 0 ≤ Bpt := by
    dsimp [Bpt]
    positivity
  refine ⟨Bpt, hBpt_nonneg, fun t ht x hx => ?_⟩
  have ht_pos : 0 < t := by linarith
  unfold srcSlice1
  have hpownn :
      0 ≤ (intervalDomainLift (conjugatePicardIter p u₀ 0 t) x) ^ (p.γ - 1) :=
    Real.rpow_nonneg (le_of_lt (hfloor t ht_pos x hx)) _
  rw [abs_mul, abs_mul, abs_mul,
    abs_of_pos p.hν, abs_of_pos p.hγ, abs_of_nonneg hpownn]
  calc
    p.ν * p.γ *
        (intervalDomainLift (conjugatePicardIter p u₀ 0 t) x) ^ (p.γ - 1) *
        |heatDu u₀ t x|
        ≤ p.ν * p.γ * Cpow * CΔ := by
          have hpow_le := hCpow t ht_pos x hx
          have hdu_le := hCΔ t ht x hx
          nlinarith [p.hν, p.hγ, hCpow_nonneg, hCΔ_nonneg, hpownn,
            hpow_le, hdu_le, abs_nonneg (heatDu u₀ t x)]
    _ = Bpt := by rfl

/-- Tail bound for the fixed `k`-th cosine coefficient of `srcSlice1`. -/
private theorem heatLevel0_srcSlice1_coeff_tail_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ c : ℝ}
    (hc : 0 < c)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    (k : ℕ) :
    ∃ Bsrc : ℝ, ∀ t : ℝ, c + 1 < t →
      |cosineCoeffs
        (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t) k| ≤ Bsrc := by
  obtain ⟨Bpt, hBpt_nonneg, hBpt⟩ :=
    heatLevel0_srcSlice1_tail_pointwise_bound
      (p := p) (u₀ := u₀) (M₀ := M₀) (c := c)
      hc hu₀_bound hu₀_cont hu₀_pos hfloor
  refine ⟨2 * Bpt, fun t ht => ?_⟩
  have ht_pos : 0 < t := by linarith
  have hcont := heatLevel0_srcSlice1_timeSlice_continuousOn
    (p := p) (u₀ := u₀) (M₀ := M₀) (t := t)
    hu₀_bound hu₀_cont hfloor ht_pos
  exact ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
    hcont hBpt_nonneg (hBpt t ht) k

end ShenWork.Paper2.HeatResolverJointC2Direct
```

The final call to `cosineCoeffs_abs_le_of_continuous_bounded` matches the already-used pattern in the `i = 0` branch: a continuous slice plus a pointwise absolute bound by `Bpt` yields `|coeff k| ≤ 2 * Bpt`.

## Drop-in replacement for the local `hBsrc`

Once the helpers above are in the same namespace, replace the local sorry by:

```lean
            have hBsrc : ∃ Bsrc : ℝ, ∀ t : ℝ, c + 1 < t →
                |cosineCoeffs (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t) k| ≤ Bsrc := by
              exact heatLevel0_srcSlice1_coeff_tail_bound
                (p := p) (u₀ := u₀) (M₀ := M₀) (c := c)
                hc hu₀_bound hu₀_cont hu₀_pos hfloor k
```

Then the rest of the current `hR_deriv_bounded` block should remain unchanged:

```lean
            obtain ⟨Bsrc, hBsrc⟩ := hBsrc
            set w_k := ShenWork.PDE.intervalNeumannResolverWeight p k
            refine ⟨|w_k| * Bsrc, fun t ht => ?_⟩
            have ht_pos : 0 < t := by linarith
            rw [show deriv R t = deriv (resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k) t
              from rfl]
            rw [heatLevel0_resolverTimeCoeff_deriv_eq hu₀_bound hu₀_cont hfloor ht_pos k]
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hBsrc t ht) (abs_nonneg _)
```

## Why this is the right `srcSlice1` decomposition

The remaining coefficient bound is independent of the resolver.  It is exactly:

```text
|coeff(srcSlice1(t), k)|
  ≤ 2 * sup_x |ν γ (S(t)u₀(x))^(γ-1) heatDu(t,x)|
```

The heat semigroup gives:

```text
m0 ≤ S(t)u₀(x) ≤ M0sup
```

with `m0 > 0`, so `r ↦ r^(γ-1)` is bounded on `[m0, M0sup]` even when `γ < 1`.  The heat-Laplacian term `heatDu` is bounded on `t > c+1` by the reciprocal-square estimate:

```lean
unitIntervalCosineHeatSecondPointWeight_abs_le
reciprocalSquareTerm_summable
```

After those two scalar bounds, `srcSlice1` is pointwise bounded on `[0,1]`; `heatSemigroup_d0` supplies the needed continuity; and `cosineCoeffs_abs_le_of_continuous_bounded` gives the coefficient bound.

## Bottom line

For Q1833, do not try to get `hBsrc` from resolver damping.  Add the source-side helpers:

```lean
heatLevel0_srcSlice1_timeSlice_continuousOn
heatDu_tail_linf_bound
heatLevel0_rpow_gamma_sub_one_tail_bound
heatLevel0_srcSlice1_tail_pointwise_bound
heatLevel0_srcSlice1_coeff_tail_bound
```

Then the local `hBsrc` is a one-line call to `heatLevel0_srcSlice1_coeff_tail_bound`.
