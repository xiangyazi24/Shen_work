/-
  ShenWork/Paper2/IntervalConjugateChemFluxIntegrable.lean

  Paper 2 (general χ), B-form conjugate-kernel core residual `hB_int`:
  interval-integrability in time of the conjugate B-form chemotaxis Duhamel leg

    s ↦ B_N(t−s) Q(w s) x  =  −∫₀¹ ∂ᵧ K_N(t−s, x, y) · Q(w s)(y) dy.

  This is the second-variable-kernel analogue of the proven gradient-Duhamel
  time-integrability atom `gradDuhamel_intervalIntegrable_of_joint_measurable`.

  The route (guidance §1):
    1. joint `(s,y)`-measurability of the lagged `∂ᵧ` Neumann kernel;
    2. `AEStronglyMeasurable` of the conjugate operator in `s` (Fubini);
    3. abstract domination `_of_measurable_bound` by `Cg·(t−s)^{−1/2}·Cq`;
    4. trajectory instantiation for `chemFluxLifted` (and the flux difference)
       via the cutoff-source `f` trick, exactly as the gradient leg does.

  Additive; new names only.  No `sorry`/`admit`/`native_decide`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalConjugateDuhamelMap
import ShenWork.Paper2.IntervalDuhamelIntegrability
import ShenWork.Paper2.ChemMildHolderBootstrap
import ShenWork.PDE.IntervalFullKernelSDependentMeasurable

open MeasureTheory Set
open scoped Topology

noncomputable section

namespace ShenWork.IntervalConjugateChemFluxIntegrable

open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateKernelOperator intervalConjugateKernelOperator_abs_le)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted)
open ShenWork.IntervalResolverWeakBounds
  (resolverSourceCoeff_re_sq_summable_of_continuousOn)
open ShenWork.HeatKernelGradientEstimates
  (heatGradientLinftyLinftyConstant heatGradientLinftyLinftyConstant_nonneg)

/-! ## Step 1 — joint measurability of the lagged `∂ᵧ` Neumann kernel -/

/-- **Joint measurability of the lagged second-variable Neumann-kernel derivative.**
`(s, y) ↦ ∂ᵧ K_full(t − s, x, y)` is `Measurable` as a map `ℝ × ℝ → ℝ`.

By `hasDerivAt_intervalNeumannFullKernel_snd`, for `t − s > 0` the derivative is
the difference of two integer-lattice `tsum`s of heat-kernel spatial derivatives;
for `t − s ≤ 0` the kernel (hence its derivative) is `0`, and the same lattice
formula evaluates to `0` there too (each summand vanishes).  Joint measurability
of each lattice `tsum` is the existing `measurable_tsum_int_of_summable` /
`measurable_deriv_heatKernel_comp` infrastructure. -/
theorem measurable_deriv_snd_intervalNeumannFullKernel_lag (t x : ℝ) :
    Measurable (fun z : ℝ × ℝ =>
      deriv (fun y' : ℝ => intervalNeumannFullKernel (t - z.1) x y') z.2) := by
  -- The two lattice `tsum`s appearing in the snd-derivative closed form.
  set A : ℝ × ℝ → ℝ := fun z =>
    ∑' k : ℤ, deriv (fun u : ℝ => heatKernel (t - z.1) u) (x - z.2 + 2 * (k : ℝ)) with hA
  set B : ℝ × ℝ → ℝ := fun z =>
    ∑' k : ℤ, deriv (fun u : ℝ => heatKernel (t - z.1) u) (x + z.2 + 2 * (k : ℝ)) with hB
  -- Each is `Measurable` via the heat-kernel-derivative lattice infrastructure.
  have hsum_aux : ∀ (sgn : ℝ),
      Measurable (fun z : ℝ × ℝ =>
        ∑' k : ℤ, deriv (fun u : ℝ => heatKernel (t - z.1) u)
          (x + sgn * z.2 + 2 * (k : ℝ))) := by
    intro sgn
    refine measurable_tsum_int_of_summable
      (fun k => measurable_deriv_heatKernel_comp (by fun_prop) t) (fun z => ?_)
    rcases lt_or_ge 0 (t - z.1) with hτ | hτ
    · exact latticeGaussianGradSummable hτ (x + sgn * z.2)
    · have hz : (fun k : ℤ => deriv (fun u : ℝ => heatKernel (t - z.1) u)
          (x + sgn * z.2 + 2 * (k : ℝ))) = fun _ : ℤ => (0 : ℝ) := by
        funext k
        have hzero : (fun u : ℝ => heatKernel (t - z.1) u) = fun _ : ℝ => (0 : ℝ) := by
          funext u; exact heatKernel_of_nonpos hτ u
        rw [hzero, deriv_const]
      rw [hz]; exact summable_zero
  have hAeq : A = (fun z : ℝ × ℝ =>
      ∑' k : ℤ, deriv (fun u : ℝ => heatKernel (t - z.1) u)
        (x + (-1) * z.2 + 2 * (k : ℝ))) := by
    funext z; rw [hA]; refine tsum_congr (fun k => ?_); congr 1; ring
  have hBeq : B = (fun z : ℝ × ℝ =>
      ∑' k : ℤ, deriv (fun u : ℝ => heatKernel (t - z.1) u)
        (x + 1 * z.2 + 2 * (k : ℝ))) := by
    funext z; rw [hB]; refine tsum_congr (fun k => ?_); congr 1; ring
  have hA_meas : Measurable A := by rw [hAeq]; exact hsum_aux (-1)
  have hB_meas : Measurable B := by rw [hBeq]; exact hsum_aux 1
  -- Identify the snd-derivative with `−A + B`.
  have hfun_eq : (fun z : ℝ × ℝ =>
      deriv (fun y' : ℝ => intervalNeumannFullKernel (t - z.1) x y') z.2)
      = fun z : ℝ × ℝ => -A z + B z := by
    funext z
    rcases lt_or_ge 0 (t - z.1) with hτ | hτ
    · rw [(hasDerivAt_intervalNeumannFullKernel_snd hτ x z.2).deriv]
    · -- `t − s ≤ 0`: kernel and both lattice sums are `0`.
      have hderiv_zero : deriv (fun u : ℝ => heatKernel (t - z.1) u)
          = fun _ : ℝ => (0 : ℝ) := by
        have hzk : (fun u : ℝ => heatKernel (t - z.1) u) = fun _ : ℝ => (0 : ℝ) := by
          funext u; exact heatKernel_of_nonpos hτ u
        rw [hzk, deriv_const']
      have hzero : (fun y' : ℝ => intervalNeumannFullKernel (t - z.1) x y')
          = fun _ : ℝ => (0 : ℝ) := by
        funext y'
        simp only [intervalNeumannFullKernel]
        rw [show (fun k : ℤ => heatKernel (t - z.1) (x - y' + 2 * (k : ℝ))
              + heatKernel (t - z.1) (x + y' + 2 * (k : ℝ)))
            = fun _ : ℤ => (0 : ℝ) from by
          funext k; rw [heatKernel_of_nonpos hτ, heatKernel_of_nonpos hτ, add_zero]]
        exact tsum_zero
      have hAz : A z = 0 := by
        rw [hA]; simp only
        rw [show (fun k : ℤ => deriv (fun u : ℝ => heatKernel (t - z.1) u)
              (x - z.2 + 2 * (k : ℝ))) = fun _ : ℤ => (0 : ℝ) from by
          funext k; rw [hderiv_zero]]
        exact tsum_zero
      have hBz : B z = 0 := by
        rw [hB]; simp only
        rw [show (fun k : ℤ => deriv (fun u : ℝ => heatKernel (t - z.1) u)
              (x + z.2 + 2 * (k : ℝ))) = fun _ : ℤ => (0 : ℝ) from by
          funext k; rw [hderiv_zero]]
        exact tsum_zero
      rw [hzero, deriv_const, hAz, hBz, neg_zero, add_zero]
  rw [hfun_eq]; exact hA_meas.neg.add hB_meas

/-! ## Step 2 — `AEStronglyMeasurable` of the conjugate operator in `s` -/

/-- **`AEStronglyMeasurable` of the lagged conjugate-kernel operator in `s`.**
For a jointly `(s,y)`-measurable source `q`, the map
`s ↦ B_N(t−s) (q s) x = −∫ y, ∂ᵧK_full(t−s,x,y)·q s y` is `AEStronglyMeasurable`
on `volume.restrict (Set.Icc 0 t)` (the Fubini parameter-integral measurability,
mirroring the full-semigroup `_s_dependent_` discharges). -/
theorem intervalConjugateKernelOperator_lag_aestronglyMeasurable
    {t x : ℝ} {q : ℝ → ℝ → ℝ}
    (hq : Measurable (fun z : ℝ × ℝ => q z.1 z.2)) :
    AEStronglyMeasurable
      (fun s : ℝ => intervalConjugateKernelOperator (t - s) (q s) x)
      (volume.restrict (Set.Icc 0 t)) := by
  set Kd : ℝ × ℝ → ℝ := fun z =>
    deriv (fun y' : ℝ => intervalNeumannFullKernel (t - z.1) x y') z.2 with hKd
  have hKd_meas : Measurable Kd := measurable_deriv_snd_intervalNeumannFullKernel_lag t x
  -- The parameter integrand `(s,y) ↦ ∂ᵧK·q` is jointly measurable.
  have hprod_meas : Measurable (fun z : ℝ × ℝ => Kd z * q z.1 z.2) :=
    hKd_meas.mul hq
  -- Fubini: `s ↦ ∫ y, ∂ᵧK(t−s,x,y)·q s y` is `AEStronglyMeasurable` (on all of ℝ).
  have hInt_aestrong : AEStronglyMeasurable
      (fun s : ℝ => ∫ y, Kd (s, y) * q s y ∂(intervalMeasure 1)) volume :=
    MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (μ := volume) (ν := intervalMeasure 1)
      (f := fun z : ℝ × ℝ => Kd z * q z.1 z.2)
      hprod_meas.aestronglyMeasurable
  -- The operator is `−` that integral.
  have hfun : (fun s : ℝ => intervalConjugateKernelOperator (t - s) (q s) x)
      = fun s : ℝ => -(∫ y, Kd (s, y) * q s y ∂(intervalMeasure 1)) := by
    funext s; rfl
  rw [hfun]
  exact hInt_aestrong.neg.restrict

/-! ## Step 3 — abstract domination integrability -/

/-- **Abstract B-form Duhamel time-integrability by measurable bound.**
If `q` is jointly measurable, per-slice integrable, and uniformly bounded by `Cq`,
then `s ↦ B_N(t−s)(q s) x` is `IntervalIntegrable` on `(0,t)`, dominated by the
integrable singularity `Cg·Cq·(t−s)^{−1/2}`.  Mirrors
`gradDuhamel_intervalIntegrable_of_joint_measurable`. -/
theorem conjugateDuhamel_intervalIntegrable_of_measurable_bound
    {t Cq : ℝ} (ht : 0 < t) (hCq : 0 ≤ Cq)
    {q : ℝ → ℝ → ℝ} {x : ℝ}
    (hq_meas : Measurable (fun z : ℝ × ℝ => q z.1 z.2))
    (hq_int : ∀ s, Integrable (q s) (intervalMeasure 1))
    (hq_sup : ∀ s y, |q s y| ≤ Cq) :
    IntervalIntegrable
      (fun s : ℝ => intervalConjugateKernelOperator (t - s) (q s) x)
      volume 0 t := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le ht.le]
  set Cg := heatGradientLinftyLinftyConstant with hCgdef
  have hCgnn : 0 ≤ Cg := heatGradientLinftyLinftyConstant_nonneg
  -- Step 2 gives `AEStronglyMeasurable` on `Icc 0 t`; restrict to `Ioc 0 t`.
  have hmeas_Icc := intervalConjugateKernelOperator_lag_aestronglyMeasurable
    (t := t) (x := x) hq_meas
  have hmeas : AEStronglyMeasurable
      (fun s : ℝ => intervalConjugateKernelOperator (t - s) (q s) x)
      (volume.restrict (Set.Ioc 0 t)) :=
    hmeas_Icc.mono_measure (Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl)
  -- Dominator `Cg·Cq·(t−s)^{−1/2}` is integrable on `Ioc 0 t`.
  have hdom_int : IntegrableOn
      (fun s : ℝ => Cg * Cq * (t - s) ^ (-(1/2) : ℝ)) (Set.Ioc 0 t) volume := by
    rw [← Set.uIoc_of_le ht.le, ← intervalIntegrable_iff]
    exact ((ShenWork.IntervalGradDuhamelBound.intervalIntegrable_sub_rpow_neg_half t).const_mul
      (Cg * Cq))
  -- a.e. (s < t) pointwise bound via `intervalConjugateKernelOperator_abs_le`.
  have hne : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
    rw [ae_iff]; simp only [not_not, Set.setOf_eq_eq_singleton]; exact Real.volume_singleton
  have hae : ∀ᵐ s ∂(volume.restrict (Set.Ioc 0 t)),
      ‖(fun s : ℝ => intervalConjugateKernelOperator (t - s) (q s) x) s‖
        ≤ (fun s : ℝ => Cg * Cq * (t - s) ^ (-(1/2) : ℝ)) s := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hne] with s hs_ne hs_mem
    have hts : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs_mem.2 hs_ne)
    rw [Real.norm_eq_abs]
    have h := intervalConjugateKernelOperator_abs_le hts (hq_int s) (hq_sup s) x
    calc |intervalConjugateKernelOperator (t - s) (q s) x|
        ≤ Cg * (t - s) ^ (-(1 / 2) : ℝ) * Cq := by simpa [Cg] using h
      _ = Cg * Cq * (t - s) ^ (-(1 / 2) : ℝ) := by ring
  exact Integrable.mono' hdom_int hmeas hae

/-! ## Step 4 — uniform ball flux bound and trajectory instantiations -/

open ShenWork.IntervalMildPicard (HasContinuousSlices HasJointMeasurability)

/-- **Public uniform-in-`y` order-box bound on the chemotaxis source from a ball
bound** (a public re-derivation of the file-private `chemFluxLifted_bound_of_ball`):
`|Q(w)(y)| ≤ M·√(∑ gradWeightₖ²)·(2νMᵞ)` for every `y`, from a continuous
nonnegative `M`-bounded `w`.  Supplies the uniform `CQ` for the Core fields. -/
theorem chemFluxLifted_sup_bound_of_ball
    (p : CM2Params) {M : ℝ} (hM_nonneg : 0 ≤ M)
    {w : intervalDomainPoint → ℝ}
    (hw_bound : ∀ x, |w x| ≤ M) (hw_nonneg : ∀ x, 0 ≤ w x) (hw_cont : Continuous w) :
    ∀ y : ℝ, |chemFluxLifted p w y| ≤
      M * (Real.sqrt (∑' k : ℕ,
        (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) * (2 * (p.ν * M ^ p.γ))) := by
  intro y
  set C_RG := Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) * (2 * (p.ν * M ^ p.γ))
  have hC_RG_nn : 0 ≤ C_RG :=
    mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (mul_nonneg p.hν.le (Real.rpow_nonneg hM_nonneg _)))
  unfold chemFluxLifted
  by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
  · have hcont_on : ContinuousOn (intervalDomainLift w) (Set.Icc (0 : ℝ) 1) := by
      rw [continuousOn_iff_continuous_restrict]
      have heq : Set.restrict (Set.Icc (0 : ℝ) 1) (intervalDomainLift w) = w := by
        ext ⟨z, hz⟩; simp [Set.restrict, intervalDomainLift, hz]; rfl
      rw [heq]; exact hw_cont
    have hlb : ∀ z ∈ Set.Icc (0 : ℝ) 1, 0 ≤ intervalDomainLift w z := fun z hz => by
      simp [intervalDomainLift, hz]; exact hw_nonneg ⟨z, hz⟩
    have hub : ∀ z ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift w z ≤ M := fun z hz => by
      simp [intervalDomainLift, hz]; exact (abs_le.mp (hw_bound ⟨z, hz⟩)).2
    have hgrad : |ShenWork.Paper2.resolverGradReal p w y| ≤ C_RG := by
      simpa [C_RG] using
        ShenWork.IntervalResolverWeakBounds.resolverGrad_sup_le_of_bounded
          p hcont_on hlb hub hy
    have hlift : |intervalDomainLift w y| ≤ M := by
      simp [intervalDomainLift, hy]; exact hw_bound ⟨y, hy⟩
    have hR_nonneg_pt : 0 ≤ ShenWork.PDE.intervalNeumannResolverR p w ⟨y, hy⟩ := by
      have hcont_src : Continuous (fun z : intervalDomainPoint ↦ p.ν * (w z) ^ p.γ) :=
        continuous_const.mul (hw_cont.rpow_const (fun z ↦ Or.inr p.hγ.le))
      set clip : ℝ → intervalDomainPoint := fun z ↦
        ⟨max 0 (min z 1), le_max_left 0 _, max_le (by norm_num) (min_le_right z 1)⟩
      have hclip_cont : Continuous clip :=
        Continuous.subtype_mk (continuous_const.max (continuous_id.min continuous_const)) _
      set f : ℝ → ℝ := (fun z : intervalDomainPoint ↦ p.ν * (w z) ^ p.γ) ∘ clip
      have hf_cont : Continuous f := hcont_src.comp hclip_cont
      have hf_nonneg : ∀ z, 0 ≤ f z := fun z ↦
        mul_nonneg p.hν.le (Real.rpow_nonneg (hw_nonneg _) _)
      have hf_coeff : ∀ k, ShenWork.IntervalNeumannFullKernel.cosineCoeffs f k =
          (ShenWork.PDE.intervalNeumannResolverSourceCoeff p w k).re := by
        intro k
        have hsrc_eq : (ShenWork.PDE.intervalNeumannResolverSourceCoeff p w k).re =
            ShenWork.IntervalNeumannFullKernel.cosineCoeffs
              (fun z ↦ p.ν * intervalDomainLift w z ^ p.γ) k := by
          simp [ShenWork.IntervalNeumannFullKernel.cosineCoeffs,
            ShenWork.PDE.intervalNeumannResolverSourceCoeff, Complex.ofReal_re]
        rw [hsrc_eq]
        exact ShenWork.Paper2.cosineCoeffs_congr_on_Icc (fun z hz ↦ by
          simp only [f, Function.comp, clip]
          have hclip_eq : max 0 (min z 1) = z := by
            rw [min_eq_left hz.2, max_eq_right hz.1]
          simp only [hclip_eq, intervalDomainLift, dif_pos (Set.mem_Icc.mpr hz)]) k
      have hâ : Summable (fun k ↦ (cosineCoeffs f k) ^ 2) := by
        have h := resolverSourceCoeff_re_sq_summable_of_continuousOn p hcont_on
        simp only [ShenWork.Paper2.intervalNeumannResolverSourceCoeff_zero, sub_zero] at h
        exact h.congr (fun k ↦ by rw [hf_coeff])
      exact ShenWork.IntervalResolverPositivity.intervalNeumannResolverR_nonneg_of_nonneg_source
        hf_cont hf_nonneg hf_coeff hâ ⟨y, hy⟩
    have hR_lift_eq : intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) y =
        ShenWork.PDE.intervalNeumannResolverR p w ⟨y, hy⟩ := by simp [intervalDomainLift, hy]
    have hden_ge_one : 1 ≤ (1 + intervalDomainLift
        (ShenWork.PDE.intervalNeumannResolverR p w) y) ^ p.β := by
      rw [hR_lift_eq]; exact Real.one_le_rpow (by linarith [hR_nonneg_pt]) p.hβ
    calc
      |intervalDomainLift w y * ShenWork.Paper2.resolverGradReal p w y /
          (1 + intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) y) ^ p.β|
          = |intervalDomainLift w y * ShenWork.Paper2.resolverGradReal p w y| /
            |(1 + intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) y) ^ p.β| :=
            abs_div _ _
      _ ≤ |intervalDomainLift w y * ShenWork.Paper2.resolverGradReal p w y| / 1 := by
          apply div_le_div_of_nonneg_left (abs_nonneg _) one_pos
          rw [abs_of_nonneg (le_of_lt (Real.rpow_pos_of_pos
            (by rw [hR_lift_eq]; linarith [hR_nonneg_pt]) p.β))]
          exact hden_ge_one
      _ = |intervalDomainLift w y * ShenWork.Paper2.resolverGradReal p w y| := by rw [div_one]
      _ ≤ |intervalDomainLift w y| * |ShenWork.Paper2.resolverGradReal p w y| :=
          le_of_eq (abs_mul _ _)
      _ ≤ M * C_RG := mul_le_mul hlift hgrad (abs_nonneg _) hM_nonneg
      _ = M * (Real.sqrt (∑' k : ℕ,
            (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
              (2 * (p.ν * M ^ p.γ))) := rfl
  · simp [intervalDomainLift, hy, zero_mul, abs_zero]
    exact mul_nonneg hM_nonneg hC_RG_nn

/-- **Trajectory `hB_int`: the conjugate B-form chemotaxis Duhamel leg is
interval-integrable in time.**  For a ball trajectory `w` (bounded by `M`,
nonnegative, continuous slices, jointly measurable) with the chemotaxis flux
uniformly bounded by `CQ` on the window, the lagged conjugate operator
`s ↦ B_N(t−s)(Q(w s)) x` is `IntervalIntegrable` on `(0,t)`. -/
theorem conjugateChemFlux_duhamel_intervalIntegrable_of_ball
    (p : CM2Params) {T M CQ : ℝ} (hM : 0 ≤ M) (hCQ : 0 ≤ CQ)
    {w : ℝ → intervalDomainPoint → ℝ}
    (hbound : ∀ τ, 0 < τ → τ ≤ T → ∀ x, |w τ x| ≤ M)
    (hnonneg : ∀ τ, 0 < τ → τ ≤ T → ∀ x, 0 ≤ w τ x)
    (hcont : HasContinuousSlices T w) (hmeas : HasJointMeasurability w)
    (hQbound : ∀ τ, 0 < τ → τ ≤ T → ∀ y, |chemFluxLifted p (w τ) y| ≤ CQ)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) (x : intervalDomainPoint) :
    IntervalIntegrable
      (fun s => intervalConjugateKernelOperator (t - s) (chemFluxLifted p (w s)) x.1)
      volume 0 t := by
  -- Cutoff source: `chemFluxLifted` on-window, `0` off-window.
  set q : ℝ → ℝ → ℝ :=
    fun s yy => if 0 < s ∧ s ≤ T then chemFluxLifted p (w s) yy else 0 with hq
  -- uniform bound by `CQ`
  have hq_sup : ∀ s yy, |q s yy| ≤ CQ := by
    intro s yy; simp only [hq]; split_ifs with h
    · exact hQbound s h.1 h.2 yy
    · simpa using hCQ
  -- joint measurability
  have hq_meas : Measurable (fun z : ℝ × ℝ => q z.1 z.2) := by
    have hbase := ShenWork.Paper2.chemFluxLifted_uncurry_measurable (p := p) (u := w) hmeas
    simp only [hq]
    refine Measurable.ite ?_ hbase measurable_const
    exact ((isOpen_Ioi.preimage continuous_fst).measurableSet).inter
      ((isClosed_Iic.preimage continuous_fst).measurableSet)
  -- per-slice integrability
  have hq_int : ∀ s, Integrable (q s) (intervalMeasure 1) := by
    intro s; simp only [hq]; split_ifs with h
    · exact ShenWork.IntervalDuhamelIntegrability.chemFluxLifted_integrable_of_continuous
        p (hbound s h.1 h.2) hM (hcont s h.1 h.2) (hnonneg s h.1 h.2)
    · simp
  -- the cutoff source agrees with the raw flux on `(0,t]`, so the operators agree there
  have hcongr : Set.EqOn
      (fun s => intervalConjugateKernelOperator (t - s) (q s) x.1)
      (fun s => intervalConjugateKernelOperator (t - s) (chemFluxLifted p (w s)) x.1)
      (Set.uIoc 0 t) := by
    intro s hs
    rw [Set.uIoc_of_le ht.le] at hs
    have hmem : 0 < s ∧ s ≤ T := ⟨hs.1, le_trans hs.2 htT⟩
    simp only [hq, if_pos hmem]
  exact (conjugateDuhamel_intervalIntegrable_of_measurable_bound ht hCQ hq_meas hq_int
    hq_sup).congr hcongr

/-- **Contraction analogue.**  The same time-integrability for the chemotaxis-flux
*difference* `y ↦ Q(u s)(y) − Q(w s)(y)`, with uniform bound `CQ·d`.  Fills
`hflux_duhamel_diff_integrable`. -/
theorem conjugateChemFlux_duhamel_diff_intervalIntegrable_of_ball
    (p : CM2Params) {T M CQd : ℝ} (hM : 0 ≤ M) (hCQd : 0 ≤ CQd)
    {u w : ℝ → intervalDomainPoint → ℝ}
    (hub : ∀ τ, 0 < τ → τ ≤ T → ∀ x, |u τ x| ≤ M)
    (hun : ∀ τ, 0 < τ → τ ≤ T → ∀ x, 0 ≤ u τ x)
    (hwb : ∀ τ, 0 < τ → τ ≤ T → ∀ x, |w τ x| ≤ M)
    (hwn : ∀ τ, 0 < τ → τ ≤ T → ∀ x, 0 ≤ w τ x)
    (huc : HasContinuousSlices T u) (hwc : HasContinuousSlices T w)
    (hum : HasJointMeasurability u) (hwm : HasJointMeasurability w)
    (hQdbound : ∀ τ, 0 < τ → τ ≤ T → ∀ y,
      |chemFluxLifted p (u τ) y - chemFluxLifted p (w τ) y| ≤ CQd)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) (x : intervalDomainPoint) :
    IntervalIntegrable
      (fun s => intervalConjugateKernelOperator (t - s)
        (fun y => chemFluxLifted p (u s) y - chemFluxLifted p (w s) y) x.1)
      volume 0 t := by
  set q : ℝ → ℝ → ℝ :=
    fun s yy => if 0 < s ∧ s ≤ T then chemFluxLifted p (u s) yy - chemFluxLifted p (w s) yy
      else 0 with hq
  have hq_sup : ∀ s yy, |q s yy| ≤ CQd := by
    intro s yy; simp only [hq]; split_ifs with h
    · exact hQdbound s h.1 h.2 yy
    · simpa using hCQd
  have hq_meas : Measurable (fun z : ℝ × ℝ => q z.1 z.2) := by
    have hbu := ShenWork.Paper2.chemFluxLifted_uncurry_measurable (p := p) (u := u) hum
    have hbw := ShenWork.Paper2.chemFluxLifted_uncurry_measurable (p := p) (u := w) hwm
    simp only [hq]
    refine Measurable.ite ?_ (hbu.sub hbw) measurable_const
    exact ((isOpen_Ioi.preimage continuous_fst).measurableSet).inter
      ((isClosed_Iic.preimage continuous_fst).measurableSet)
  have hq_int : ∀ s, Integrable (q s) (intervalMeasure 1) := by
    intro s; simp only [hq]; split_ifs with h
    · exact (ShenWork.IntervalDuhamelIntegrability.chemFluxLifted_integrable_of_continuous
        p (hub s h.1 h.2) hM (huc s h.1 h.2) (hun s h.1 h.2)).sub
        (ShenWork.IntervalDuhamelIntegrability.chemFluxLifted_integrable_of_continuous
        p (hwb s h.1 h.2) hM (hwc s h.1 h.2) (hwn s h.1 h.2))
    · simp
  have hcongr : Set.EqOn
      (fun s => intervalConjugateKernelOperator (t - s) (q s) x.1)
      (fun s => intervalConjugateKernelOperator (t - s)
        (fun y => chemFluxLifted p (u s) y - chemFluxLifted p (w s) y) x.1)
      (Set.uIoc 0 t) := by
    intro s hs
    rw [Set.uIoc_of_le ht.le] at hs
    have hmem : 0 < s ∧ s ≤ T := ⟨hs.1, le_trans hs.2 htT⟩
    simp only [hq, if_pos hmem]
  exact (conjugateDuhamel_intervalIntegrable_of_measurable_bound ht hCQd hq_meas hq_int
    hq_sup).congr hcongr

#print axioms chemFluxLifted_sup_bound_of_ball
#print axioms measurable_deriv_snd_intervalNeumannFullKernel_lag
#print axioms conjugateDuhamel_intervalIntegrable_of_measurable_bound
#print axioms conjugateChemFlux_duhamel_intervalIntegrable_of_ball
#print axioms conjugateChemFlux_duhamel_diff_intervalIntegrable_of_ball

end ShenWork.IntervalConjugateChemFluxIntegrable
