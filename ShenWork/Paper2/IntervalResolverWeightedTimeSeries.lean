/-
  Local time regularity of resolver-weighted cosine series.

  These lemmas isolate the exact analytic content used by the elliptic
  resolver: the multiplier sequence `1 / (μ + λₖ)` is summable.  No
  `DuhamelSourceTimeC1`, restart representation, or spectral-agreement package
  is involved.
-/
import ShenWork.PDE.IntervalResolverSpatialC2

open Set Filter Topology

noncomputable section

namespace ShenWork.Paper2

open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.PDE
  (intervalNeumannResolverWeight intervalNeumannResolverWeight_nonneg)
open ShenWork.IntervalResolverSpatialC2 (resolverWeight_summable)

/-- Local target-time differentiation of a resolver-weighted cosine series.

On an open preconnected time set `I`, assume each coefficient `a · k` has
derivative `adot · k`, while coefficient values and derivatives have bounds
uniform in `k` and time.  Summability of the resolver weights then gives
termwise differentiation at every target time in `I`.

The constants need not be separately assumed nonnegative: the proof uses
`|A|` and `|D|` as summable majorants. -/
theorem resolverWeightedCosineSeries_hasDerivAt_of_local_uniform
    (p : CM2Params) {I : Set ℝ} (hI_open : IsOpen I)
    (hI_preconnected : IsPreconnected I)
    {a adot : ℝ → ℕ → ℝ} {A D : ℝ}
    (ha_deriv : ∀ k s, s ∈ I →
      HasDerivAt (fun r : ℝ => a r k) (adot s k) s)
    (ha_bound : ∀ s ∈ I, ∀ k, |a s k| ≤ A)
    (hadot_bound : ∀ s ∈ I, ∀ k, |adot s k| ≤ D)
    {t : ℝ} (ht : t ∈ I) (x : ℝ) :
    HasDerivAt
      (fun s : ℝ => ∑' k : ℕ,
        a s k * intervalNeumannResolverWeight p k * cosineMode k x)
      (∑' k : ℕ,
        adot t k * intervalNeumannResolverWeight p k * cosineMode k x)
      t := by
  let derivMajorant : ℕ → ℝ := fun k =>
    |D| * intervalNeumannResolverWeight p k
  have hderivMajorant : Summable derivMajorant := by
    simpa [derivMajorant] using
      (resolverWeight_summable p).mul_left |D|
  have hterm_deriv : ∀ k s, s ∈ I →
      HasDerivAt
        (fun r : ℝ =>
          a r k * intervalNeumannResolverWeight p k * cosineMode k x)
        (adot s k * intervalNeumannResolverWeight p k * cosineMode k x) s := by
    intro k s hs
    simpa only [mul_assoc] using
      (ha_deriv k s hs).mul_const
        (intervalNeumannResolverWeight p k * cosineMode k x)
  have hterm_deriv_bound : ∀ k s, s ∈ I →
      ‖adot s k * intervalNeumannResolverWeight p k * cosineMode k x‖ ≤
        derivMajorant k := by
    intro k s hs
    rw [Real.norm_eq_abs]
    have hweight : 0 ≤ intervalNeumannResolverWeight p k :=
      intervalNeumannResolverWeight_nonneg p k
    have hDk : |adot s k| ≤ |D| :=
      (hadot_bound s hs k).trans (le_abs_self D)
    have hcos : |cosineMode k x| ≤ 1 := by
      unfold cosineMode
      exact Real.abs_cos_le_one _
    calc
      |adot s k * intervalNeumannResolverWeight p k * cosineMode k x|
          = |adot s k| * intervalNeumannResolverWeight p k *
              |cosineMode k x| := by
              rw [abs_mul, abs_mul, abs_of_nonneg hweight]
      _ ≤ |D| * intervalNeumannResolverWeight p k * 1 := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_right hDk hweight) hcos
            (abs_nonneg _) (mul_nonneg (abs_nonneg D) hweight)
      _ = derivMajorant k := by simp [derivMajorant]
  have hvalue_summable : Summable (fun k : ℕ =>
      a t k * intervalNeumannResolverWeight p k * cosineMode k x) := by
    apply Summable.of_norm_bounded
      (g := fun k : ℕ => |A| * intervalNeumannResolverWeight p k)
      ((resolverWeight_summable p).mul_left |A|)
    intro k
    rw [Real.norm_eq_abs]
    have hweight : 0 ≤ intervalNeumannResolverWeight p k :=
      intervalNeumannResolverWeight_nonneg p k
    have hAk : |a t k| ≤ |A| :=
      (ha_bound t ht k).trans (le_abs_self A)
    have hcos : |cosineMode k x| ≤ 1 := by
      unfold cosineMode
      exact Real.abs_cos_le_one _
    calc
      |a t k * intervalNeumannResolverWeight p k * cosineMode k x|
          = |a t k| * intervalNeumannResolverWeight p k *
              |cosineMode k x| := by
              rw [abs_mul, abs_mul, abs_of_nonneg hweight]
      _ ≤ |A| * intervalNeumannResolverWeight p k * 1 := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_right hAk hweight) hcos
            (abs_nonneg _) (mul_nonneg (abs_nonneg A) hweight)
      _ = |A| * intervalNeumannResolverWeight p k := by ring
  exact hasDerivAt_tsum_of_isPreconnected
    hderivMajorant hI_open hI_preconnected
    hterm_deriv hterm_deriv_bound ht hvalue_summable ht

/-- Joint continuity of a resolver-weighted cosine series on a time-space slab.

Each coefficient is only required to be continuous on the supplied time set
`I`; a single bound uniform in time and mode yields the Weierstrass majorant
`|A| * resolverWeight k`. -/
theorem resolverWeightedCosineSeries_continuousOn_prod_Icc
    (p : CM2Params) {I : Set ℝ} {a : ℝ → ℕ → ℝ} {A : ℝ}
    (ha_cont : ∀ k, ContinuousOn (fun s : ℝ => a s k) I)
    (ha_bound : ∀ s ∈ I, ∀ k, |a s k| ≤ A) :
    ContinuousOn
      (fun q : ℝ × ℝ => ∑' k : ℕ,
        a q.1 k * intervalNeumannResolverWeight p k * cosineMode k q.2)
      (I ×ˢ Set.Icc (0 : ℝ) 1) := by
  apply continuousOn_tsum
  · intro k
    have htime : ContinuousOn (fun q : ℝ × ℝ => a q.1 k)
        (I ×ˢ Set.Icc (0 : ℝ) 1) :=
      (ha_cont k).comp continuous_fst.continuousOn
        (fun q hq => (Set.mem_prod.mp hq).1)
    have hcos : Continuous (fun q : ℝ × ℝ => cosineMode k q.2) := by
      unfold cosineMode
      fun_prop
    exact (htime.mul continuousOn_const).mul hcos.continuousOn
  · exact (resolverWeight_summable p).mul_left |A|
  · intro k q hq
    obtain ⟨ht, _hx⟩ := Set.mem_prod.mp hq
    rw [Real.norm_eq_abs]
    have hweight : 0 ≤ intervalNeumannResolverWeight p k :=
      intervalNeumannResolverWeight_nonneg p k
    have hAk : |a q.1 k| ≤ |A| :=
      (ha_bound q.1 ht k).trans (le_abs_self A)
    have hcos : |cosineMode k q.2| ≤ 1 := by
      unfold cosineMode
      exact Real.abs_cos_le_one _
    calc
      |a q.1 k * intervalNeumannResolverWeight p k * cosineMode k q.2|
          = |a q.1 k| * intervalNeumannResolverWeight p k *
              |cosineMode k q.2| := by
              rw [abs_mul, abs_mul, abs_of_nonneg hweight]
      _ ≤ |A| * intervalNeumannResolverWeight p k * 1 := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_right hAk hweight) hcos
            (abs_nonneg _) (mul_nonneg (abs_nonneg A) hweight)
      _ = |A| * intervalNeumannResolverWeight p k := by ring

section AxiomAudit

#print axioms resolverWeightedCosineSeries_hasDerivAt_of_local_uniform
#print axioms resolverWeightedCosineSeries_continuousOn_prod_Icc

end AxiomAudit

end ShenWork.Paper2
