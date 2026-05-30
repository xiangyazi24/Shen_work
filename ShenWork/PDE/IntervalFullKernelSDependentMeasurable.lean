/-
  ShenWork/PDE/IntervalFullKernelSDependentMeasurable.lean

  **T2 (final residual) — lattice `s_dependent` per-slice measurability for the
  full Neumann kernel.**

  Full-Neumann-kernel mirror of
  `intervalSemigroupOperator_s_dependent_aestronglyMeasurable_x` /
  `intervalSemigroupOperator_s_dependent_deriv_aestronglyMeasurable_x₀`
  (the zeroth-reflection lemmas in `IntervalCoupledClassicalBallEstimates`).

  The zeroth-reflection kernel is a finite closed form, so its joint `(s, y)`
  measurability falls to `fun_prop`.  The full Neumann kernel
  `K_full(t, x, y) = ∑_{k∈ℤ}(heat(t, x−y+2k) + heat(t, x+y+2k))` is an integer
  lattice `tsum`, so we discharge joint measurability through the generic
  pointwise-limit principle `measurable_tsum_int_of_summable` (tsum = pointwise
  limit of the `Finset.range`-partial sums, each measurable, via
  `measurable_of_tendsto_metrizable`).  The summand kernels are everywhere
  summable (`latticeGaussianSummable` / `latticeGaussianGradSummable` for `t−s > 0`;
  all-zero for `t−s ≤ 0`).

  These two lemmas replace the `hF_meas`/`hF'_meas` hypotheses carried through
  `_clean_full → _cleaner_full → _resolver_full` with the single joint
  measurability `hF_ae` (mirroring the zeroth terminal).

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.PDE.IntervalFullKernelGradientLinfty
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Logic.Equiv.Nat

open MeasureTheory
open scoped Topology

namespace ShenWork.IntervalNeumannFullKernel

open ShenWork.IntervalDomain

/-! ## Generic `tsum`-over-`ℤ` measurability via pointwise partial-sum limits -/

/-- **Measurability of an integer-lattice `tsum` of measurable functions.**

If each summand `g k : α → ℝ` is measurable and the family `k ↦ g k a` is
summable for every `a`, then `a ↦ ∑' k : ℤ, g k a` is measurable.

`tsum` reindexed through `ℕ ≃ ℤ` is the pointwise limit of the `Finset.range`
partial sums (`HasSum.tendsto_sum_nat`); each partial sum is a finite sum of
measurable functions, so the limit is measurable by
`measurable_of_tendsto_metrizable`. -/
theorem measurable_tsum_int_of_summable {α : Type*} [MeasurableSpace α]
    {g : ℤ → α → ℝ} (hg : ∀ k, Measurable (g k))
    (hsum : ∀ a, Summable (fun k : ℤ => g k a)) :
    Measurable (fun a : α => ∑' k : ℤ, g k a) := by
  set e : ℕ ≃ ℤ := Equiv.intEquivNat.symm with he
  -- Reindex the lattice `tsum` to a `ℕ`-indexed `tsum`.
  have hreindex : (fun a : α => ∑' k : ℤ, g k a)
      = (fun a : α => ∑' n : ℕ, g (e n) a) := by
    funext a
    exact (e.tsum_eq (fun k => g k a)).symm
  rw [hreindex]
  -- The `Finset.range` partial sums are measurable.
  set S : ℕ → α → ℝ := fun N a => ∑ n ∈ Finset.range N, g (e n) a with hS
  have hS_meas : ∀ N, Measurable (S N) := fun N =>
    Finset.measurable_sum _ (fun n _ => hg (e n))
  -- They converge pointwise to the `ℕ`-indexed `tsum`.
  have htend : Filter.Tendsto S Filter.atTop
      (𝓝 (fun a : α => ∑' n : ℕ, g (e n) a)) := by
    rw [tendsto_pi_nhds]
    intro a
    have hsa : Summable (fun n : ℕ => g (e n) a) :=
      (e.summable_iff (f := fun k => g k a)).mpr (hsum a)
    exact hsa.hasSum.tendsto_sum_nat
  exact measurable_of_tendsto_metrizable hS_meas htend

/-! ## The heat kernel and its spatial derivative as measurable closed forms -/

/-- The heat kernel vanishes for non-positive time (Lean's `Real.sqrt` returns `0`
on non-positive inputs, so the prefactor `1/√(4πt)` is `0`). -/
theorem heatKernel_of_nonpos {t : ℝ} (ht : t ≤ 0) (x : ℝ) :
    heatKernel t x = 0 := by
  unfold heatKernel
  have h4t : 4 * Real.pi * t ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) ht
  rw [Real.sqrt_eq_zero'.mpr h4t]
  simp

/-- **Global closed form for the heat-kernel spatial derivative.**

`deriv (z ↦ heatKernel t z) x = −(x / (2t)) · heatKernel t x` for *all* `t`
(not just `t > 0`): for `t ≤ 0` the kernel is identically zero, so both sides
vanish. -/
theorem deriv_heatKernel_global (t x : ℝ) :
    deriv (fun z : ℝ => heatKernel t z) x =
      -(x / (2 * t)) * heatKernel t x := by
  rcases lt_or_ge 0 t with ht | ht
  · exact deriv_heatKernel ht x
  · have hzero : (fun z : ℝ => heatKernel t z) = fun _ : ℝ => (0 : ℝ) := by
      funext z; exact heatKernel_of_nonpos ht z
    rw [hzero, deriv_const, heatKernel_of_nonpos ht x, mul_zero]

/-- The `(s, y)`-dependent heat kernel `(s, y) ↦ heatKernel (t − s) (p (s, y))`
is jointly measurable for any measurable affine argument `p`. -/
theorem measurable_heatKernel_comp {p : ℝ × ℝ → ℝ} (hp : Measurable p) (t : ℝ) :
    Measurable (fun w : ℝ × ℝ => heatKernel (t - w.1) (p w)) := by
  unfold heatKernel
  fun_prop

/-- The `(s, y)`-dependent heat-kernel spatial derivative
`(s, y) ↦ deriv (z ↦ heatKernel (t − s) z) (p (s, y))` is jointly measurable for
any measurable argument `p` (via the global closed form). -/
theorem measurable_deriv_heatKernel_comp {p : ℝ × ℝ → ℝ} (hp : Measurable p) (t : ℝ) :
    Measurable (fun w : ℝ × ℝ => deriv (fun z : ℝ => heatKernel (t - w.1) z) (p w)) := by
  have heq : (fun w : ℝ × ℝ => deriv (fun z : ℝ => heatKernel (t - w.1) z) (p w))
      = fun w : ℝ × ℝ => -(p w / (2 * (t - w.1))) * heatKernel (t - w.1) (p w) := by
    funext w; exact deriv_heatKernel_global (t - w.1) (p w)
  rw [heq]
  unfold heatKernel
  fun_prop

/-! ## Joint measurability of the full Neumann kernel and its spatial derivative -/

/-- **Joint measurability of the full Neumann kernel in `(s, y)`.**
`(s, y) ↦ K_full(t − s, x, y)` is `Measurable` as a function of `(s, y) : ℝ × ℝ`. -/
theorem intervalNeumannFullKernel_s_dependent_measurable (t x : ℝ) :
    Measurable (fun w : ℝ × ℝ => intervalNeumannFullKernel (t - w.1) x w.2) := by
  -- The summand `g k (s, y) = heat(t−s, x−y+2k) + heat(t−s, x+y+2k)`.
  set g : ℤ → ℝ × ℝ → ℝ :=
    fun k w => heatKernel (t - w.1) (x - w.2 + 2 * (k : ℝ))
      + heatKernel (t - w.1) (x + w.2 + 2 * (k : ℝ)) with hg_def
  have hg_meas : ∀ k, Measurable (g k) := by
    intro k
    exact (measurable_heatKernel_comp (by fun_prop) t).add
      (measurable_heatKernel_comp (by fun_prop) t)
  have hg_sum : ∀ w : ℝ × ℝ, Summable (fun k : ℤ => g k w) := by
    intro w
    rcases lt_or_ge 0 (t - w.1) with hτ | hτ
    · exact (latticeGaussianSummable hτ (x - w.2)).add
        (latticeGaussianSummable hτ (x + w.2))
    · have hz : (fun k : ℤ => g k w) = fun _ : ℤ => (0 : ℝ) := by
        funext k
        simp only [hg_def, heatKernel_of_nonpos hτ, add_zero]
      rw [hz]; exact summable_zero
  have hmeas := measurable_tsum_int_of_summable hg_meas hg_sum
  -- Identify the lattice `tsum` with `K_full`.
  have hfun : (fun w : ℝ × ℝ => intervalNeumannFullKernel (t - w.1) x w.2)
      = fun w : ℝ × ℝ => ∑' k : ℤ, g k w := by
    funext w; rfl
  rw [hfun]; exact hmeas

/-- **Joint measurability of the full-kernel spatial derivative in `(s, y)`.**
For fixed `x₀`, `(s, y) ↦ (∑ₖ ∂heat(t−s, x₀−y+2k)) + (∑ₖ ∂heat(t−s, x₀+y+2k))`
is `Measurable`.  By `hasDerivAt_intervalNeumannFullKernel_fst`, for `t − s > 0`
this equals `deriv (z ↦ K_full(t−s, z, y)) x₀`. -/
theorem deriv_intervalNeumannFullKernel_fst_s_dependent_measurable (t x₀ : ℝ) :
    Measurable (fun w : ℝ × ℝ =>
      (∑' k : ℤ, deriv (fun z : ℝ => heatKernel (t - w.1) z) (x₀ - w.2 + 2 * (k : ℝ)))
        + (∑' k : ℤ, deriv (fun z : ℝ => heatKernel (t - w.1) z) (x₀ + w.2 + 2 * (k : ℝ)))) := by
  set g₁ : ℤ → ℝ × ℝ → ℝ :=
    fun k w => deriv (fun z : ℝ => heatKernel (t - w.1) z) (x₀ - w.2 + 2 * (k : ℝ)) with hg₁_def
  set g₂ : ℤ → ℝ × ℝ → ℝ :=
    fun k w => deriv (fun z : ℝ => heatKernel (t - w.1) z) (x₀ + w.2 + 2 * (k : ℝ)) with hg₂_def
  have hg₁_meas : ∀ k, Measurable (g₁ k) := fun k =>
    measurable_deriv_heatKernel_comp (by fun_prop) t
  have hg₂_meas : ∀ k, Measurable (g₂ k) := fun k =>
    measurable_deriv_heatKernel_comp (by fun_prop) t
  have hsum_aux : ∀ (z : ℝ) (w : ℝ × ℝ),
      Summable (fun k : ℤ => deriv (fun u : ℝ => heatKernel (t - w.1) u) (z + 2 * (k : ℝ))) := by
    intro z w
    rcases lt_or_ge 0 (t - w.1) with hτ | hτ
    · exact latticeGaussianGradSummable hτ z
    · have hz : (fun k : ℤ => deriv (fun u : ℝ => heatKernel (t - w.1) u) (z + 2 * (k : ℝ)))
          = fun _ : ℤ => (0 : ℝ) := by
        funext k
        have hzero : (fun u : ℝ => heatKernel (t - w.1) u) = fun _ : ℝ => (0 : ℝ) := by
          funext u; exact heatKernel_of_nonpos hτ u
        rw [hzero, deriv_const]
      rw [hz]; exact summable_zero
  have hg₁_sum : ∀ w, Summable (fun k : ℤ => g₁ k w) := fun w => hsum_aux (x₀ - w.2) w
  have hg₂_sum : ∀ w, Summable (fun k : ℤ => g₂ k w) := fun w => hsum_aux (x₀ + w.2) w
  exact (measurable_tsum_int_of_summable hg₁_meas hg₁_sum).add
    (measurable_tsum_int_of_summable hg₂_meas hg₂_sum)

/-! ## `s_dependent` `AEStronglyMeasurable` discharge (the two T2 residual lemmas) -/

/-- **Full-kernel `hF_meas` discharge.**  For `t > 0` and a jointly measurable
source field `F`, the map `s ↦ intervalFullSemigroupOperator (t − s) (F s) x` is
`AEStronglyMeasurable` on `volume.restrict (uIoc 0 t)`. -/
theorem intervalFullSemigroupOperator_s_dependent_aestronglyMeasurable_x
    {t : ℝ} (ht : 0 < t) {F : ℝ → ℝ → ℝ}
    (hF_ae : AEStronglyMeasurable (Function.uncurry F)
      ((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)).prod (intervalMeasure 1)))
    (x : ℝ) :
    AEStronglyMeasurable
      (fun s : ℝ => intervalFullSemigroupOperator (t - s) (F s) x)
      (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)) := by
  set J : ℝ × ℝ → ℝ :=
    fun w => intervalNeumannFullKernel (t - w.1) x w.2 * F w.1 w.2 with hJ_def
  have hK_meas := intervalNeumannFullKernel_s_dependent_measurable t x
  have hJ_aestrong :
      AEStronglyMeasurable J
        ((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)).prod (intervalMeasure 1)) :=
    hK_meas.aestronglyMeasurable.mul hF_ae
  have hfubini :=
    MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (μ := MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t))
      (ν := intervalMeasure 1) (f := J) hJ_aestrong
  simpa [intervalFullSemigroupOperator, J] using hfubini

/-- **Full-kernel `hF'_meas` discharge.**  For `t > 0`, joint measurability and
per-slice integrability/boundedness of `F`, the map
`s ↦ deriv (z ↦ intervalFullSemigroupOperator (t − s) (F s) z) x₀` is
`AEStronglyMeasurable` on `volume.restrict (uIoc 0 t)`.

The operator derivative is realised as the single parametric integral against the
full-kernel spatial derivative via `intervalFullSemigroupOperator_hasDerivAt_fst`,
whose `(s, y)`-joint measurability is
`deriv_intervalNeumannFullKernel_fst_s_dependent_measurable`; Fubini concludes. -/
theorem intervalFullSemigroupOperator_s_dependent_deriv_aestronglyMeasurable_x₀
    {t : ℝ} (ht : 0 < t) {F : ℝ → ℝ → ℝ}
    (hF_ae : AEStronglyMeasurable (Function.uncurry F)
      ((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)).prod (intervalMeasure 1)))
    (hF_int : ∀ s, MeasureTheory.Integrable (F s) (intervalMeasure 1))
    {C_source : ℝ} (hF_sup : ∀ s, ∀ y : ℝ, |F s y| ≤ C_source)
    (x₀ : ℝ) :
    AEStronglyMeasurable
      (fun s : ℝ => deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) (F s) z) x₀)
      (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)) := by
  -- The closed-form parametric-integral surrogate `D(s)`.
  set Kd : ℝ × ℝ → ℝ :=
    fun w =>
      (∑' k : ℤ, deriv (fun z : ℝ => heatKernel (t - w.1) z) (x₀ - w.2 + 2 * (k : ℝ)))
        + (∑' k : ℤ, deriv (fun z : ℝ => heatKernel (t - w.1) z) (x₀ + w.2 + 2 * (k : ℝ)))
    with hKd_def
  have hKd_meas := deriv_intervalNeumannFullKernel_fst_s_dependent_measurable t x₀
  set D : ℝ → ℝ := fun s => ∫ y, Kd (s, y) * F s y ∂(intervalMeasure 1) with hD_def
  have hD_aestrong : AEStronglyMeasurable D
      (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)) := by
    have hint_ae : AEStronglyMeasurable (fun w : ℝ × ℝ => Kd w * F w.1 w.2)
        ((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)).prod (intervalMeasure 1)) :=
      hKd_meas.aestronglyMeasurable.mul hF_ae
    exact MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (μ := MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t))
      (ν := intervalMeasure 1) (f := fun w : ℝ × ℝ => Kd w * F w.1 w.2) hint_ae
  -- The deriv equals `D` a.e. on `uIoc 0 t` (on the full-measure subset `s < t`).
  refine hD_aestrong.congr ?_
  have huIoc_eq : Set.uIoc (0 : ℝ) t = Set.Ioc (0 : ℝ) t := Set.uIoc_of_le ht.le
  have hae_lt_t : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.uIoc 0 t)), s < t := by
    refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr ?_
    have hae_ne_t : ∀ᵐ s ∂MeasureTheory.volume, s ≠ t := by
      have heq : {s : ℝ | ¬ s ≠ t} = {t} := by ext s; simp [eq_comm]
      rw [MeasureTheory.ae_iff, heq]; exact Real.volume_singleton
    filter_upwards [hae_ne_t] with s hsne hs
    rw [huIoc_eq] at hs
    exact lt_of_le_of_ne hs.2 hsne
  filter_upwards [hae_lt_t] with s hst
  have htms_pos : 0 < t - s := sub_pos.mpr hst
  -- Operator derivative = ∫ y, ∂ₓK_full(t−s, x₀, y) · F s y.
  have hOp_deriv :
      deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) (F s) z) x₀ =
        ∫ y, deriv (fun z : ℝ => intervalNeumannFullKernel (t - s) z y) x₀ * F s y
          ∂(intervalMeasure 1) :=
    (intervalFullSemigroupOperator_hasDerivAt_fst (t := t - s) htms_pos
      (f := F s) (hF_int s).aestronglyMeasurable (Cf := C_source) (hF_sup s) x₀).deriv
  rw [hOp_deriv]
  -- Identify the kernel derivative with `Kd (s, ·)` via the lattice closed form.
  have hKfun : ∀ y : ℝ,
      deriv (fun z : ℝ => intervalNeumannFullKernel (t - s) z y) x₀ = Kd (s, y) := by
    intro y
    exact (hasDerivAt_intervalNeumannFullKernel_fst htms_pos x₀ y).deriv
  simp only [hD_def]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with y
  rw [hKfun y]

end ShenWork.IntervalNeumannFullKernel
