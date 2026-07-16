import ShenWork.Paper1.WholeLineWeightedRegularityTimeClosure
import Mathlib.MeasureTheory.Function.LpOrder

open Filter MeasureTheory Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Identifying strong `L²` limits by pointwise limits

Strong convergence in `WholeLineRealL2` determines the almost-everywhere
representative whenever the same concrete representatives have a pointwise
limit.  This is the endpoint identification needed after analytic-semigroup
maximal regularity: it avoids assuming a spatial pointwise dominator.
-/

/-- A strong `WholeLineRealL2` limit agrees almost everywhere with an
independently known pointwise limit of the chosen representatives. -/
theorem wholeLineRealL2_limit_coe_ae_of_pointwise
    {Q : ℕ → WholeLineRealL2} {V : WholeLineRealL2}
    {q : ℕ → ℝ → ℝ} {v : ℝ → ℝ}
    (hQ : Tendsto Q atTop (𝓝 V))
    (hrep : ∀ n, (((Q n : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] q n))
    (hpoint : ∀ x, Tendsto (fun n => q n x) atTop (𝓝 (v x))) :
    (((V : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] v) := by
  obtain ⟨ns, hns, hsub⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hQ).exists_seq_tendsto_ae
  have hreps : ∀ᵐ x ∂volume, ∀ n, Q n x = q n x := by
    filter_upwards [countable_iInter_mem.mpr hrep] with x hx
    exact fun n => Set.mem_iInter.mp hx n
  filter_upwards [hsub, hreps] with x hx hrepx
  have hxq : Tendsto (fun i => q (ns i) x) atTop (𝓝 (V x)) := by
    apply hx.congr'
    filter_upwards with i
    exact hrepx (ns i)
  have hxv : Tendsto (fun i => q (ns i) x) atTop (𝓝 (v x)) :=
    (hpoint x).comp hns.tendsto_atTop
  exact tendsto_nhds_unique hxq hxv

/-- Along any nonzero sequence of time increments converging to zero, a
strong `L²` derivative is represented by the classical pointwise derivative.
Only almost-everywhere slice representatives are required; no common
pointwise-in-space domination enters. -/
theorem wholeLineRealL2_hasDerivAt_coe_ae_of_pointwise_along
    {Z : ℝ → WholeLineRealL2} {z zt : ℝ → ℝ → ℝ}
    {V : WholeLineRealL2} {t : ℝ} {eps : ℕ → ℝ}
    (heps0 : Tendsto eps atTop (𝓝 0))
    (heps_ne : ∀ n, eps n ≠ 0)
    (hZ : HasDerivAt Z V t)
    (hZrep : ∀ n,
      (((Z (t + eps n) : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        z (t + eps n)))
    (hZtrep : (((Z t : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] z t))
    (hz : ∀ x, HasDerivAt (fun s => z s x) (zt t x) t) :
    (((V : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] zt t) := by
  let Q : ℕ → WholeLineRealL2 := fun n =>
    (eps n)⁻¹ • (Z (t + eps n) - Z t)
  let q : ℕ → ℝ → ℝ := fun n x =>
    (eps n)⁻¹ * (z (t + eps n) x - z t x)
  have hepsWithin : Tendsto eps atTop (𝓝[≠] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨heps0, Eventually.of_forall heps_ne⟩
  have hQ : Tendsto Q atTop (𝓝 V) := by
    exact hZ.tendsto_slope_zero.comp hepsWithin
  have hrepQ : ∀ n,
      (((Q n : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] q n) := by
    intro n
    filter_upwards [Lp.coeFn_smul (eps n)⁻¹
        (Z (t + eps n) - Z t),
      Lp.coeFn_sub (Z (t + eps n)) (Z t), hZrep n, hZtrep]
      with x hsmul hsub hplus ht
    rw [hsmul]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hsub]
    simp only [Pi.sub_apply]
    rw [hplus, ht]
  have hpointQ : ∀ x,
      Tendsto (fun n => q n x) atTop (𝓝 (zt t x)) := by
    intro x
    simpa only [q, smul_eq_mul] using
      (hz x).tendsto_slope_zero.comp hepsWithin
  exact wholeLineRealL2_limit_coe_ae_of_pointwise hQ hrepQ hpointQ

section AxiomAudit

#print axioms wholeLineRealL2_limit_coe_ae_of_pointwise
#print axioms wholeLineRealL2_hasDerivAt_coe_ae_of_pointwise_along

end AxiomAudit

end ShenWork.Paper1
