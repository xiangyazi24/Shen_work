/-
  ShenWork/PDE/IntervalChemDivAEMeasurable.lean

  A.e.-strong measurability of the lifted chemotaxis-divergence field
  `(s, y) ↦ intervalDomainLift (intervalDomainChemotaxisDiv p (u s) (v s)) y`
  for a classical solution `(u, v)`.

  ## Why a.e. (not everywhere)

  The downstream consumer (`intervalSemigroupOperator_s_dependent_*_x`) only
  feeds this field into Fubini, which needs `AEStronglyMeasurable` against the
  product measure `(volume.restrict (uIoc 0 t)).prod (intervalMeasure 1)`.  The
  spatial-endpoint set `{y ∈ {0,1}}` is `intervalMeasure 1`-null
  (`intervalMeasure 1 = volume.restrict (Icc 0 1)`), so it is discarded.  This
  is what lets us avoid the genuine obstruction — joint measurability of the
  *spatial-derivative field* on the full plane — which Mathlib's
  `measurable_deriv_with_param` cannot provide (it needs global joint
  continuity, broken by the zero-extension jump at the endpoints).

  ## Method

  We build a GLOBALLY MEASURABLE surrogate `Gchem` that equals the chemotaxis
  divergence on the interior slab, then identify the field with `Gchem` a.e.:

  * `ufield`, `vfield` — piecewise (on the slab `Ioo 0 T ×ˢ Icc 0 1`, else `0`)
    surrogates for the lifted trajectories, globally measurable via
    `ContinuousOn.measurable_piecewise` from conjunct (9) joint continuity.
  * `Gv := ParamDeriv.diffQuotLimsup vfield` — globally measurable
    (`measurable_diffQuotLimsup`), equal to `deriv (lift (v s))` on the
    interior.
  * `Ψ̃ (s,y) := ufield · Gv / (1 + vfield)^β` — globally measurable, equal to
    the chemotactic flux `flux_v (s,·)` on the interior `(0,1)` in `y`.
  * `Gchem := ParamDeriv.diffQuotLimsup Ψ̃` — globally measurable, equal to
    `intervalDomainChemotaxisDiv` on the interior (the flux is differentiable
    there, `solution_chemotaxisFlux_hasDerivAt`, and `Ψ̃` agrees with the flux
    on a neighborhood, so the surrogate returns the genuine derivative).

  No `sorry`, no `admit`, no custom `axiom`.
-/
import ShenWork.PDE.IntervalCoupledClassicalBallEstimates
import ShenWork.PDE.IntervalParamDerivMeasurable

open ShenWork.Paper2 ShenWork.IntervalDomain ShenWork.PDE MeasureTheory Filter
open ShenWork.IntervalResolverLaplacianBridge
open ShenWork.IntervalCoupledBallEstimates
open ShenWork.IntervalCoupledClassicalBallEstimates
open ShenWork.IntervalDomainExistence
open scoped Topology

namespace ShenWork

/-- **The chemotactic flux is differentiable at interior points, with the
chemotaxis divergence as its derivative.**  This is the analytic core: it is
exactly the differentiability already established (as `hQ_has`) inside
`intervalDomainChemotaxisDiv_eq_chemDivRepr_interior`, repackaged as a
`HasDerivAt` whose derivative value is `intervalDomainChemotaxisDiv` itself
(true by the definition of the divergence as `deriv` of the flux). -/
theorem solution_chemotaxisFlux_hasDerivAt
    {p : CM2Params} {T : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T)
    {y : intervalDomainPoint} (hy_int : y.1 ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun y' : ℝ =>
        intervalDomainLift (u τ) y' * deriv (intervalDomainLift (v τ)) y'
          / (1 + intervalDomainLift (v τ) y') ^ p.β)
      (intervalDomainChemotaxisDiv p (u τ) (v τ) y) y.1 := by
  classical
  set y₀ : ℝ := y.1 with hy₀
  have hy_Icc : y₀ ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hy_int
  -- C² interior regularity (conjunct 3).
  have hC2u : ContDiffOn ℝ 2 (intervalDomainLift (u τ)) (Set.Ioo (0:ℝ) 1) :=
    (hsol.regularity.1 τ hτ).1
  have hC2v : ContDiffOn ℝ 2 (intervalDomainLift (v τ)) (Set.Ioo (0:ℝ) 1) :=
    (hsol.regularity.1 τ hτ).2
  -- `lift u` differentiable at `y₀`.
  have hU_diff : DifferentiableAt ℝ (intervalDomainLift (u τ)) y₀ :=
    (hC2u.differentiableOn (by norm_num)).differentiableAt
      (IsOpen.mem_nhds isOpen_Ioo hy_int)
  -- `lift v` differentiable at `y₀`.
  have hV_diff : DifferentiableAt ℝ (intervalDomainLift (v τ)) y₀ :=
    (hC2v.differentiableOn (by norm_num)).differentiableAt
      (IsOpen.mem_nhds isOpen_Ioo hy_int)
  -- `deriv (lift v)` is `C¹` on the open interior, hence differentiable at `y₀`.
  have hDV_C1 : ContDiffOn ℝ 1 (deriv (intervalDomainLift (v τ))) (Set.Ioo (0:ℝ) 1) :=
    hC2v.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hW_diff : DifferentiableAt ℝ (deriv (intervalDomainLift (v τ))) y₀ :=
    (hDV_C1.differentiableOn (by norm_num)).differentiableAt
      (IsOpen.mem_nhds isOpen_Ioo hy_int)
  -- Positivity of the denominator base `1 + lift v ≥ 1`.
  have hv_nn : 0 ≤ intervalDomainLift (v τ) y₀ :=
    solution_lift_v_nonneg_Icc hsol hτ y₀ hy_Icc
  have hV₀_pos : 0 < 1 + intervalDomainLift (v τ) y₀ := by linarith
  -- `1 + lift v` differentiable at `y₀`.
  have hOnePlusV_diff :
      DifferentiableAt ℝ (fun z : ℝ => 1 + intervalDomainLift (v τ) z) y₀ :=
    (differentiableAt_const _).add hV_diff
  -- `(1 + lift v)^β` differentiable at `y₀` (chain rule, base positive).
  have hpow_at : HasDerivAt (fun x : ℝ => x ^ p.β)
      (p.β * (1 + intervalDomainLift (v τ) y₀) ^ (p.β - 1))
      (1 + intervalDomainLift (v τ) y₀) :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hV₀_pos))
  have hD_diff :
      DifferentiableAt ℝ
        (fun z : ℝ => (1 + intervalDomainLift (v τ) z) ^ p.β) y₀ := by
    have hcomp := (hpow_at.differentiableAt).comp y₀ hOnePlusV_diff
    simpa [Function.comp] using hcomp
  -- Numerator `lift u · deriv (lift v)` differentiable at `y₀`.
  have hN_diff :
      DifferentiableAt ℝ
        (fun z : ℝ =>
          intervalDomainLift (u τ) z * deriv (intervalDomainLift (v τ)) z) y₀ :=
    hU_diff.mul hW_diff
  -- Denominator nonzero.
  have hD_ne :
      (fun z : ℝ => (1 + intervalDomainLift (v τ) z) ^ p.β) y₀ ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hV₀_pos _)
  -- Flux differentiable at `y₀` (quotient rule).
  have hflux_diff :
      DifferentiableAt ℝ
        (fun z : ℝ =>
          intervalDomainLift (u τ) z * deriv (intervalDomainLift (v τ)) z
            / (1 + intervalDomainLift (v τ) z) ^ p.β) y₀ :=
    hN_diff.div hD_diff hD_ne
  -- `deriv` of the flux at `y₀` IS the chemotaxis divergence by definition.
  have hderiv_eq :
      deriv
        (fun z : ℝ =>
          intervalDomainLift (u τ) z * deriv (intervalDomainLift (v τ)) z
            / (1 + intervalDomainLift (v τ) z) ^ p.β) y₀
        = intervalDomainChemotaxisDiv p (u τ) (v τ) y := by
    unfold intervalDomainChemotaxisDiv
    rfl
  -- `DifferentiableAt → HasDerivAt (deriv …)`, then rewrite to the divergence.
  have h := hflux_diff.hasDerivAt
  rw [hderiv_eq] at h
  exact h

open ShenWork.ParamDeriv

/-- Globally-measurable piecewise surrogate for the lifted trajectory field:
equal to `(s,y) ↦ intervalDomainLift (w s) y` on the slab `Ioo 0 T ×ˢ Icc 0 1`
and `0` outside. -/
noncomputable def liftSlab (T : ℝ) (w : ℝ → intervalDomainPoint → ℝ) : ℝ × ℝ → ℝ :=
  (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1).piecewise
    (Function.uncurry (fun s y => intervalDomainLift (w s) y)) (fun _ => 0)

/-- `liftSlab` is globally measurable from joint continuity on the slab. -/
theorem measurable_liftSlab {T : ℝ} {w : ℝ → intervalDomainPoint → ℝ}
    (hcont : ContinuousOn
      (Function.uncurry (fun s y => intervalDomainLift (w s) y))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)) :
    Measurable (liftSlab T w) := by
  unfold liftSlab
  exact ContinuousOn.measurable_piecewise hcont continuousOn_const
    (measurableSet_Ioo.prod measurableSet_Icc)

/-- For a point in the slab, `liftSlab` returns the genuine lifted value. -/
theorem liftSlab_eq_of_mem {T : ℝ} {w : ℝ → intervalDomainPoint → ℝ}
    {s z : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) T) (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    liftSlab T w (s, z) = intervalDomainLift (w s) z := by
  unfold liftSlab
  rw [Set.piecewise_eq_of_mem _ _ _ (Set.mk_mem_prod hs hz)]
  rfl

/-- **A.e.-strong measurability of the lifted chemotaxis-divergence field for a
classical solution.**

The field `(s, y) ↦ intervalDomainLift (intervalDomainChemotaxisDiv p (u s)
(v s)) y` is `AEStronglyMeasurable` against the Fubini product measure
`(volume.restrict (uIoc 0 t)).prod (intervalMeasure 1)` whenever `0 < t ≤ T`.

The proof builds a globally measurable surrogate `Gchem` (a nested
`diffQuotLimsup` of the measurable piecewise lift surrogates) that equals the
field on the interior slab `Ioo 0 T ×ˢ Ioo 0 1`; the complement is null for the
product measure (the time endpoint `{T}` and the spatial endpoints `{0,1}` are
Lebesgue-null). -/
theorem intervalDomainChemDiv_v_lift_aestronglyMeasurable
    {p : CM2Params} {T : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    AEStronglyMeasurable
      (Function.uncurry
        (fun (s : ℝ) (y : ℝ) =>
          intervalDomainLift (intervalDomainChemotaxisDiv p (u s) (v s)) y))
      ((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)).prod
        (intervalMeasure 1)) := by
  classical
  set μ := (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)).prod
    (intervalMeasure 1) with hμ_def
  -- Joint continuity of the lifted trajectories on the slab (conjunct (9)).
  have hcontU : ContinuousOn
      (Function.uncurry (fun s y => intervalDomainLift (u s) y))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.2.2).1
  have hcontV : ContinuousOn
      (Function.uncurry (fun s y => intervalDomainLift (v s) y))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.2.2).2
  -- Measurable surrogate fields.
  have hUf : Measurable (liftSlab T u) := measurable_liftSlab hcontU
  have hVf : Measurable (liftSlab T v) := measurable_liftSlab hcontV
  set Gv : ℝ × ℝ → ℝ := diffQuotLimsup (liftSlab T v) with hGv_def
  have hGv_meas : Measurable Gv := measurable_diffQuotLimsup hVf
  set Psi : ℝ × ℝ → ℝ :=
    fun q => liftSlab T u q * Gv q / (1 + liftSlab T v q) ^ p.β with hPsi_def
  have hPsi_meas : Measurable Psi := by
    have hrpow : Measurable (fun x : ℝ => x ^ p.β) := by fun_prop
    have hden : Measurable (fun q : ℝ × ℝ => (1 + liftSlab T v q) ^ p.β) :=
      hrpow.comp (measurable_const.add hVf)
    exact (hUf.mul hGv_meas).div hden
  set Gchem : ℝ × ℝ → ℝ := diffQuotLimsup Psi with hGchem_def
  have hGchem_meas : Measurable Gchem := measurable_diffQuotLimsup hPsi_meas
  -- The target field.
  set F : ℝ × ℝ → ℝ :=
    Function.uncurry
      (fun (s : ℝ) (y : ℝ) =>
        intervalDomainLift (intervalDomainChemotaxisDiv p (u s) (v s)) y)
    with hF_def
  -- Agreement on the interior slab.
  have hagree : ∀ q ∈ Set.Ioo (0 : ℝ) T ×ˢ Set.Ioo (0 : ℝ) 1, F q = Gchem q := by
    rintro ⟨s, ycoord⟩ ⟨hs, hyc⟩
    have hy_Icc : ycoord ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hyc
    -- (A) `Gv (s, y') = deriv (lift (v s)) y'` for every interior `y'`.
    have hGv_interior : ∀ y' ∈ Set.Ioo (0 : ℝ) 1,
        Gv (s, y') = deriv (intervalDomainLift (v s)) y' := by
      intro y' hy'
      have hVf_eq :
          (fun z : ℝ => liftSlab T v (s, z)) =ᶠ[𝓝 y'] intervalDomainLift (v s) := by
        refine Filter.eventuallyEq_of_mem (IsOpen.mem_nhds isOpen_Ioo hy') ?_
        intro z hz
        exact liftSlab_eq_of_mem hs (Set.Ioo_subset_Icc_self hz)
      have hVdiff : DifferentiableAt ℝ (intervalDomainLift (v s)) y' :=
        (((hsol.regularity.1 s hs).2).differentiableOn (by norm_num)).differentiableAt
          (IsOpen.mem_nhds isOpen_Ioo hy')
      have hHas :
          HasDerivAt (fun z : ℝ => liftSlab T v (s, z))
            (deriv (intervalDomainLift (v s)) y') y' :=
        (hVdiff.hasDerivAt).congr_of_eventuallyEq hVf_eq
      exact diffQuotLimsup_eq_of_hasDerivAt hHas
    -- (B) `Psi (s, ·)` agrees with the flux on a neighborhood of `ycoord`.
    have hPsi_eq :
        (fun z : ℝ => Psi (s, z)) =ᶠ[𝓝 ycoord]
          (fun z : ℝ =>
            intervalDomainLift (u s) z * deriv (intervalDomainLift (v s)) z
              / (1 + intervalDomainLift (v s) z) ^ p.β) := by
      refine Filter.eventuallyEq_of_mem (IsOpen.mem_nhds isOpen_Ioo hyc) ?_
      intro z hz
      have h1 : liftSlab T u (s, z) = intervalDomainLift (u s) z :=
        liftSlab_eq_of_mem hs (Set.Ioo_subset_Icc_self hz)
      have h2 : liftSlab T v (s, z) = intervalDomainLift (v s) z :=
        liftSlab_eq_of_mem hs (Set.Ioo_subset_Icc_self hz)
      have h3 : Gv (s, z) = deriv (intervalDomainLift (v s)) z := hGv_interior z hz
      simp only [hPsi_def, h1, h2, h3]
    -- (C) Flux has the chemotaxis divergence as derivative at `ycoord`.
    have hflux :
        HasDerivAt
          (fun z : ℝ =>
            intervalDomainLift (u s) z * deriv (intervalDomainLift (v s)) z
              / (1 + intervalDomainLift (v s) z) ^ p.β)
          (intervalDomainChemotaxisDiv p (u s) (v s) ⟨ycoord, hy_Icc⟩) ycoord :=
      solution_chemotaxisFlux_hasDerivAt hsol hs (y := ⟨ycoord, hy_Icc⟩) hyc
    have hPsiHas :
        HasDerivAt (fun z : ℝ => Psi (s, z))
          (intervalDomainChemotaxisDiv p (u s) (v s) ⟨ycoord, hy_Icc⟩) ycoord :=
      hflux.congr_of_eventuallyEq hPsi_eq
    have hGchem_val :
        Gchem (s, ycoord)
          = intervalDomainChemotaxisDiv p (u s) (v s) ⟨ycoord, hy_Icc⟩ :=
      diffQuotLimsup_eq_of_hasDerivAt hPsiHas
    -- (D) The target field equals the chemotaxis divergence (`ycoord ∈ Icc`).
    have hF_val :
        F (s, ycoord)
          = intervalDomainChemotaxisDiv p (u s) (v s) ⟨ycoord, hy_Icc⟩ := by
      simp only [hF_def, Function.uncurry]
      unfold intervalDomainLift
      rw [dif_pos hy_Icc]
    rw [hF_val, hGchem_val]
  -- The complement of the interior slab is `μ`-null.
  have hnull : μ (Set.Ioo (0 : ℝ) T ×ˢ Set.Ioo (0 : ℝ) 1)ᶜ = 0 := by
    have hsub :
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Ioo (0 : ℝ) 1)ᶜ ⊆
          ((Set.Ioo (0 : ℝ) T)ᶜ ×ˢ (Set.univ : Set ℝ)) ∪
            ((Set.univ : Set ℝ) ×ˢ (Set.Ioo (0 : ℝ) 1)ᶜ) := by
      rintro ⟨a, b⟩ hq
      simp only [Set.mem_prod, not_and_or, Set.mem_compl_iff] at hq
      rcases hq with ha | hb
      · exact Or.inl (Set.mk_mem_prod ha (Set.mem_univ _))
      · exact Or.inr (Set.mk_mem_prod (Set.mem_univ _) hb)
    refine measure_mono_null hsub ?_
    -- Both product pieces are null.
    have hT_null :
        (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)) (Set.Ioo (0 : ℝ) T)ᶜ = 0 := by
      rw [MeasureTheory.Measure.restrict_apply measurableSet_Ioo.compl]
      refine measure_mono_null ?_ (measure_singleton T)
      rintro x ⟨hx_notIoo, hx_uIoc⟩
      rw [Set.uIoc_of_le ht.le] at hx_uIoc
      have hx_pos : 0 < x := hx_uIoc.1
      have hx_le : x ≤ t := hx_uIoc.2
      simp only [Set.mem_compl_iff, Set.mem_Ioo, not_and, not_lt] at hx_notIoo
      have hxT : T ≤ x := hx_notIoo hx_pos
      have : x = T := le_antisymm (le_trans hx_le htT) hxT
      simp [this]
    have hX_null :
        (intervalMeasure 1) (Set.Ioo (0 : ℝ) 1)ᶜ = 0 := by
      unfold intervalMeasure intervalSet
      rw [MeasureTheory.Measure.restrict_apply measurableSet_Ioo.compl]
      refine measure_mono_null ?_
        (Set.Finite.measure_zero ((Set.finite_singleton (1 : ℝ)).insert 0) _)
      rintro x ⟨hx_notIoo, hx_Icc⟩
      simp only [Set.mem_compl_iff, Set.mem_Ioo, not_and, not_lt] at hx_notIoo
      simp only [Set.mem_Icc] at hx_Icc
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases eq_or_lt_of_le hx_Icc.1 with h0 | h0
      · exact Or.inl h0.symm
      · exact Or.inr (le_antisymm hx_Icc.2 (hx_notIoo h0))
    refine le_antisymm ?_ (zero_le _)
    calc
      μ (((Set.Ioo (0 : ℝ) T)ᶜ ×ˢ (Set.univ : Set ℝ)) ∪
            ((Set.univ : Set ℝ) ×ˢ (Set.Ioo (0 : ℝ) 1)ᶜ))
          ≤ μ ((Set.Ioo (0 : ℝ) T)ᶜ ×ˢ (Set.univ : Set ℝ)) +
              μ ((Set.univ : Set ℝ) ×ˢ (Set.Ioo (0 : ℝ) 1)ᶜ) :=
            measure_union_le _ _
      _ = 0 := by
            rw [hμ_def, MeasureTheory.Measure.prod_prod,
              MeasureTheory.Measure.prod_prod, hT_null, hX_null]
            simp
  -- Conclude: `F =ᵐ[μ] Gchem`, and `Gchem` is measurable.
  have heq : F =ᵐ[μ] Gchem := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Set.Ioo (0 : ℝ) T ×ˢ Set.Ioo (0 : ℝ) 1, ?_, hagree⟩
    rw [MeasureTheory.mem_ae_iff]
    exact hnull
  exact (hGchem_meas.aestronglyMeasurable).congr heq.symm

/-- **Reusable interior-slab a.e. upgrade.**  Two fields that agree on the
interior slab `Ioo 0 T ×ˢ Ioo 0 1` are a.e. equal for the Fubini product
measure (the time endpoint `{T}` and spatial endpoints `{0,1}` are null when
`0 < t ≤ T`), so a.e.-strong measurability transfers. -/
theorem aestronglyMeasurable_of_eqOn_interiorSlab
    {T t : ℝ} (ht : 0 < t) (htT : t ≤ T) {F G : ℝ × ℝ → ℝ}
    (hG : AEStronglyMeasurable G
      ((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)).prod (intervalMeasure 1)))
    (hagree : ∀ q ∈ Set.Ioo (0 : ℝ) T ×ˢ Set.Ioo (0 : ℝ) 1, F q = G q) :
    AEStronglyMeasurable F
      ((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)).prod (intervalMeasure 1)) := by
  classical
  set μ := (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)).prod
    (intervalMeasure 1) with hμ_def
  have hnull : μ (Set.Ioo (0 : ℝ) T ×ˢ Set.Ioo (0 : ℝ) 1)ᶜ = 0 := by
    have hsub :
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Ioo (0 : ℝ) 1)ᶜ ⊆
          ((Set.Ioo (0 : ℝ) T)ᶜ ×ˢ (Set.univ : Set ℝ)) ∪
            ((Set.univ : Set ℝ) ×ˢ (Set.Ioo (0 : ℝ) 1)ᶜ) := by
      rintro ⟨a, b⟩ hq
      simp only [Set.mem_prod, not_and_or, Set.mem_compl_iff] at hq
      rcases hq with ha | hb
      · exact Or.inl (Set.mk_mem_prod ha (Set.mem_univ _))
      · exact Or.inr (Set.mk_mem_prod (Set.mem_univ _) hb)
    refine measure_mono_null hsub ?_
    have hT_null :
        (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)) (Set.Ioo (0 : ℝ) T)ᶜ = 0 := by
      rw [MeasureTheory.Measure.restrict_apply measurableSet_Ioo.compl]
      refine measure_mono_null ?_ (measure_singleton T)
      rintro x ⟨hx_notIoo, hx_uIoc⟩
      rw [Set.uIoc_of_le ht.le] at hx_uIoc
      have hx_pos : 0 < x := hx_uIoc.1
      have hx_le : x ≤ t := hx_uIoc.2
      simp only [Set.mem_compl_iff, Set.mem_Ioo, not_and, not_lt] at hx_notIoo
      have hxT : T ≤ x := hx_notIoo hx_pos
      have : x = T := le_antisymm (le_trans hx_le htT) hxT
      simp [this]
    have hX_null :
        (intervalMeasure 1) (Set.Ioo (0 : ℝ) 1)ᶜ = 0 := by
      unfold intervalMeasure intervalSet
      rw [MeasureTheory.Measure.restrict_apply measurableSet_Ioo.compl]
      refine measure_mono_null ?_
        (Set.Finite.measure_zero ((Set.finite_singleton (1 : ℝ)).insert 0) _)
      rintro x ⟨hx_notIoo, hx_Icc⟩
      simp only [Set.mem_compl_iff, Set.mem_Ioo, not_and, not_lt] at hx_notIoo
      simp only [Set.mem_Icc] at hx_Icc
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases eq_or_lt_of_le hx_Icc.1 with h0 | h0
      · exact Or.inl h0.symm
      · exact Or.inr (le_antisymm hx_Icc.2 (hx_notIoo h0))
    refine le_antisymm ?_ (zero_le _)
    calc
      μ (((Set.Ioo (0 : ℝ) T)ᶜ ×ˢ (Set.univ : Set ℝ)) ∪
            ((Set.univ : Set ℝ) ×ˢ (Set.Ioo (0 : ℝ) 1)ᶜ))
          ≤ μ ((Set.Ioo (0 : ℝ) T)ᶜ ×ˢ (Set.univ : Set ℝ)) +
              μ ((Set.univ : Set ℝ) ×ˢ (Set.Ioo (0 : ℝ) 1)ᶜ) :=
            measure_union_le _ _
      _ = 0 := by
            rw [hμ_def, MeasureTheory.Measure.prod_prod,
              MeasureTheory.Measure.prod_prod, hT_null, hX_null]
            simp
  have heq : F =ᵐ[μ] G := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Set.Ioo (0 : ℝ) T ×ˢ Set.Ioo (0 : ℝ) 1, ?_, hagree⟩
    rw [MeasureTheory.mem_ae_iff]
    exact hnull
  exact hG.congr heq.symm

/-- **The chemotaxis divergence built from the elliptic Neumann resolver equals
the one built from the solution's chemical, at interior points.**  Uses the
unconditional pointwise identity `intervalNeumannResolverR p (u τ) ≡ lift (v τ)`
on `(0,1)`: the lifts agree on the open interior, hence so do their spatial
derivatives, the fluxes, and finally the flux derivatives. -/
theorem solution_chemDiv_resolver_eq_v_interior
    {p : CM2Params} {T : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T)
    {y : intervalDomainPoint} (hy_int : y.1 ∈ Set.Ioo (0 : ℝ) 1) :
    intervalDomainChemotaxisDiv p (u τ) (intervalNeumannResolverR p (u τ)) y =
      intervalDomainChemotaxisDiv p (u τ) (v τ) y := by
  classical
  -- Lifts agree on `(0,1)`.
  have hlift_eq : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      intervalDomainLift (intervalNeumannResolverR p (u τ)) x = intervalDomainLift (v τ) x := by
    intro x hx
    unfold intervalDomainLift
    rw [dif_pos (Set.Ioo_subset_Icc_self hx)]
    exact solution_v_eq_resolver_pointwise_unconditional hsol hτ hx
  -- Spatial derivatives agree on `(0,1)` (equal functions on an open nbhd).
  have hderiv_eq : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      deriv (intervalDomainLift (intervalNeumannResolverR p (u τ))) x
        = deriv (intervalDomainLift (v τ)) x := by
    intro x hx
    exact Filter.EventuallyEq.deriv_eq
      (Filter.eventuallyEq_of_mem (IsOpen.mem_nhds isOpen_Ioo hx) hlift_eq)
  -- Fluxes agree on a neighborhood of `y.1`.
  have hflux_eq :
      (fun z : ℝ =>
        intervalDomainLift (u τ) z
          * deriv (intervalDomainLift (intervalNeumannResolverR p (u τ))) z
          / (1 + intervalDomainLift (intervalNeumannResolverR p (u τ)) z) ^ p.β)
        =ᶠ[𝓝 y.1]
      (fun z : ℝ =>
        intervalDomainLift (u τ) z * deriv (intervalDomainLift (v τ)) z
          / (1 + intervalDomainLift (v τ) z) ^ p.β) := by
    refine Filter.eventuallyEq_of_mem (IsOpen.mem_nhds isOpen_Ioo hy_int) ?_
    intro x hx
    dsimp only
    rw [hlift_eq x hx, hderiv_eq x hx]
  -- The chemotaxis divergence is the flux derivative; conclude.
  unfold intervalDomainChemotaxisDiv
  exact hflux_eq.deriv_eq

/-- **A.e.-strong measurability of the lifted chemotaxis-divergence field built
from the elliptic Neumann resolver** (the paper-2 canonical `R`), for a
classical solution.  Reduces to the solution-`v` version
(`intervalDomainChemDiv_v_lift_aestronglyMeasurable`) via the interior identity
`solution_chemDiv_resolver_eq_v_interior` and the interior-slab a.e. upgrade. -/
theorem intervalDomainChemDiv_resolver_lift_aestronglyMeasurable
    {p : CM2Params} {T : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    AEStronglyMeasurable
      (Function.uncurry
        (fun (s : ℝ) (y : ℝ) =>
          intervalDomainLift
            (intervalDomainChemotaxisDiv p (u s) (intervalNeumannResolverR p (u s))) y))
      ((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)).prod
        (intervalMeasure 1)) := by
  refine aestronglyMeasurable_of_eqOn_interiorSlab ht htT
    (intervalDomainChemDiv_v_lift_aestronglyMeasurable hsol ht htT) ?_
  rintro ⟨s, ycoord⟩ ⟨hs, hyc⟩
  have hy_Icc : ycoord ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hyc
  simp only [Function.uncurry]
  unfold intervalDomainLift
  rw [dif_pos hy_Icc, dif_pos hy_Icc]
  exact solution_chemDiv_resolver_eq_v_interior hsol hs (y := ⟨ycoord, hy_Icc⟩) hyc

/-- **A.e.-measurable algebraic-closure combination for the lifted coupled
source.**  A.e.-strong-measurability analogue of
`intervalCoupledSource_lift_joint_measurable_of_components`: from a.e.-strong
measurability of the lifted `u`-trajectory and of the lifted chemotaxis
divergence, the lifted coupled source field is a.e.-strongly measurable.

The proof reuses the *everywhere* pointwise decomposition
`intervalCoupledSource_lift_pointwise_decomp` (source `= -χ₀·chemDiv +
u·(a - b·u^α)`) and closes a.e.-measurability under the constant/sum/product/
`rpow`-by-fixed-exponent operations. -/
theorem intervalCoupledSource_lift_aestronglyMeasurable_of_components
    {p : CM2Params}
    {R : (intervalDomainPoint → ℝ) → intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ} {μ : MeasureTheory.Measure (ℝ × ℝ)}
    (hU_ae : AEStronglyMeasurable
      (Function.uncurry (fun (s : ℝ) (y : ℝ) => intervalDomainLift (u s) y)) μ)
    (hChemDiv_ae : AEStronglyMeasurable
      (Function.uncurry
        (fun (s : ℝ) (y : ℝ) =>
          intervalDomainLift (intervalDomainChemotaxisDiv p (u s) (R (u s))) y)) μ) :
    AEStronglyMeasurable
      (Function.uncurry
        (fun (s : ℝ) (y : ℝ) =>
          intervalDomainLift (intervalCoupledSource p (u s) (R (u s))) y)) μ := by
  set Glift : ℝ × ℝ → ℝ :=
    fun z : ℝ × ℝ => intervalDomainLift (u z.1) z.2 with hGlift_def
  set Hchem : ℝ × ℝ → ℝ :=
    fun z : ℝ × ℝ =>
      intervalDomainLift (intervalDomainChemotaxisDiv p (u z.1) (R (u z.1))) z.2
    with hHchem_def
  have hGlift_ae : AEMeasurable Glift μ := hU_ae.aemeasurable
  have hHchem_ae : AEMeasurable Hchem μ := hChemDiv_ae.aemeasurable
  have h_rpow_meas : Measurable (fun x : ℝ => x ^ p.α) := by fun_prop
  have h_pow_ae : AEMeasurable (fun z : ℝ × ℝ => (Glift z) ^ p.α) μ :=
    h_rpow_meas.comp_aemeasurable hGlift_ae
  have h_bracket :
      AEMeasurable (fun z : ℝ × ℝ => p.a - p.b * (Glift z) ^ p.α) μ :=
    (aemeasurable_const).sub ((aemeasurable_const).mul h_pow_ae)
  have h_log :
      AEMeasurable (fun z : ℝ × ℝ => Glift z * (p.a - p.b * (Glift z) ^ p.α)) μ :=
    hGlift_ae.mul h_bracket
  have h_chem : AEMeasurable (fun z : ℝ × ℝ => -p.χ₀ * Hchem z) μ :=
    hHchem_ae.const_mul _
  have h_sum :
      AEMeasurable
        (fun z : ℝ × ℝ =>
          -p.χ₀ * Hchem z + Glift z * (p.a - p.b * (Glift z) ^ p.α)) μ :=
    h_chem.add h_log
  have h_eq :
      (Function.uncurry
          (fun (s : ℝ) (y : ℝ) =>
            intervalDomainLift (intervalCoupledSource p (u s) (R (u s))) y)) =
        (fun z : ℝ × ℝ =>
          -p.χ₀ * Hchem z + Glift z * (p.a - p.b * (Glift z) ^ p.α)) := by
    funext z
    obtain ⟨s, y⟩ := z
    simpa [Function.uncurry, Glift, Hchem] using
      intervalCoupledSource_lift_pointwise_decomp p (u s) (R (u s)) y
  rw [h_eq]
  exact h_sum.aestronglyMeasurable

/-- **A.e.-strong measurability of the lifted `u`-trajectory field** for a
classical solution, against the Fubini product measure — no zero-extension
hypothesis needed (the measurable `liftSlab` surrogate agrees with the field on
the interior slab). -/
theorem intervalDomainLift_u_aestronglyMeasurable_of_solution
    {p : CM2Params} {T : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    AEStronglyMeasurable
      (Function.uncurry (fun (s : ℝ) (y : ℝ) => intervalDomainLift (u s) y))
      ((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)).prod (intervalMeasure 1)) := by
  have hcontU : ContinuousOn
      (Function.uncurry (fun s y => intervalDomainLift (u s) y))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.2.2).1
  refine aestronglyMeasurable_of_eqOn_interiorSlab ht htT
    (measurable_liftSlab hcontU).aestronglyMeasurable ?_
  rintro ⟨s, ycoord⟩ ⟨hs, hyc⟩
  exact (liftSlab_eq_of_mem hs (Set.Ioo_subset_Icc_self hyc)).symm

/-- **A.e.-strong measurability of the lifted coupled-source field built from
the elliptic Neumann resolver**, for a classical solution.  This is the precise
`F`-field measurability the Duhamel ball-estimate consumer chain needs, in the
faithful a.e. form (full joint measurability is obstructed only on the
Lebesgue-null spatial-endpoint lines). -/
theorem intervalCoupledSource_resolver_lift_aestronglyMeasurable
    {p : CM2Params} {T : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    AEStronglyMeasurable
      (Function.uncurry
        (fun (s : ℝ) (y : ℝ) =>
          intervalDomainLift
            (intervalCoupledSource p (u s) (intervalNeumannResolverR p (u s))) y))
      ((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)).prod
        (intervalMeasure 1)) :=
  intervalCoupledSource_lift_aestronglyMeasurable_of_components
    (intervalDomainLift_u_aestronglyMeasurable_of_solution hsol ht htT)
    (intervalDomainChemDiv_resolver_lift_aestronglyMeasurable hsol ht htT)

/-- **`hChemDiv_joint_meas` DISCHARGED for the paper-2 resolver.**

The C¹_x Duhamel-image ball map for `R = intervalNeumannResolverR p`, with the
source-field joint-measurability obligation (the former
`hF_joint_meas`/`hChemDiv_joint_meas` hypothesis) **eliminated** — supplied
internally by `intervalCoupledSource_resolver_lift_aestronglyMeasurable` in the
faithful a.e. form the (now AE-refactored) consumer chain consumes.

Only the genuine residual of `..._cleaner` remains: `hSol` (Schauder
PDE-solution content), plus the natural `u₀`/source data and integrability
hypotheses.  No measurability hypothesis on the chemotaxis divergence is
needed, and the invalid global endpoint `hGradEq` bridge is no longer part of
the API. -/
theorem intervalCoupledClassicalC1BallEstimates_hmap_dirichlet_initial_resolver
    {p : CM2Params}
    {u₀ : intervalDomainPoint → ℝ}
    {u₀_ext u₀'_ext : ℝ → ℝ}
    {T M G_u G_u_init C_source H : ℝ}
    (hT : 0 < T) (hH_nn : 0 ≤ H) (hC_nn : 0 ≤ C_source)
    (hG_init_nn : 0 ≤ G_u_init)
    (hM_eq : M = H + C_source * T)
    (hG_u_eq : G_u = G_u_init +
      ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
        (2 * Real.sqrt T) * C_source)
    (hu₀_sup : ∀ y : intervalDomainPoint, |u₀ y| ≤ H)
    (hext_eq : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift u₀ y = u₀_ext y)
    (hu₀_ext_int : MeasureTheory.Integrable u₀_ext
      (ShenWork.IntervalDomain.intervalMeasure 1))
    (hu₀_ext_C1 : ∀ y ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt u₀_ext (u₀'_ext y) y)
    (hu₀_ext'_int : IntervalIntegrable u₀'_ext MeasureTheory.volume 0 1)
    (hu₀_ext_one : u₀_ext 1 = 0)
    (hu₀_ext'_sup : ∀ y : ℝ, |u₀'_ext y| ≤ G_u_init)
    (hSol : ∀ u v : ℝ → intervalDomainPoint → ℝ,
      IntervalDomainClassicalC1Snapshot p T M G_u u v →
        IsPaper2ClassicalSolution intervalDomain p T
          (fun τ : ℝ => fun y : intervalDomainPoint =>
            intervalCoupledDuhamelOperator p (intervalNeumannResolverR p) u₀ u τ y) v)
    (hSource_sup_local :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ s, 0 ≤ s → s ≤ T → ∀ y : ℝ,
            |intervalDomainLift
              (intervalCoupledSource p (u s) (intervalNeumannResolverR p (u s))) y|
                ≤ C_source)
    (hSource_sup_global :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ s : ℝ, ∀ y : ℝ,
            |intervalDomainLift
              (intervalCoupledSource p (u s) (intervalNeumannResolverR p (u s))) y|
                ≤ C_source)
    (hint :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ (t : ℝ) (x : intervalDomainPoint), 0 ≤ t → t ≤ T →
            MeasureTheory.IntegrableOn
              (fun s => intervalSemigroupOperator 1 (t - s)
                (intervalDomainLift
                  (intervalCoupledSource p (u s) (intervalNeumannResolverR p (u s)))) x.1)
              (Set.Icc 0 t) MeasureTheory.volume)
    (hlift_int :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ s, 0 ≤ s → s ≤ T →
            MeasureTheory.Integrable
              (intervalDomainLift
                (intervalCoupledSource p (u s) (intervalNeumannResolverR p (u s))))
              (ShenWork.IntervalDomain.intervalMeasure 1))
    (hSource_int_global :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ s : ℝ,
            MeasureTheory.Integrable
              (intervalDomainLift
                (intervalCoupledSource p (u s) (intervalNeumannResolverR p (u s))))
              (ShenWork.IntervalDomain.intervalMeasure 1)) :
    ∀ u v : ℝ → intervalDomainPoint → ℝ,
      IntervalDomainClassicalC1Snapshot p T M G_u u v →
        IntervalDomainClassicalC1Snapshot p T M G_u
          (fun t : ℝ => fun x : intervalDomainPoint =>
            intervalCoupledDuhamelOperator p (intervalNeumannResolverR p) u₀ u t x) v :=
  intervalCoupledClassicalC1BallEstimates_hmap_dirichlet_initial_cleaner
    (R := intervalNeumannResolverR p)
    hT hH_nn hC_nn hG_init_nn hM_eq hG_u_eq hu₀_sup hext_eq
    hu₀_ext_int hu₀_ext_C1 hu₀_ext'_int hu₀_ext_one hu₀_ext'_sup
    hSol hSource_sup_local hSource_sup_global hint hlift_int hSource_int_global
    (fun u v hsnap τ hτ =>
      intervalCoupledSource_resolver_lift_aestronglyMeasurable
        hsnap.isSolution hτ.1 (le_of_lt hτ.2))

/-! ### `hGradEq` endpoint analysis (diagnosis lemmas)

The `hGradEq` hypothesis equates `deriv (intervalDomainLift (Duhamel image)) x`
(LHS) with `deriv (explicit semigroup+integral) x` (RHS) for `x ∈ Icc 0 1`.

* **Interior** `x ∈ Ioo 0 1`: the lift agrees with the explicit on the open
  interior, so the two derivatives coincide — trivially true.
* **Endpoints** `x ∈ {0,1}`: the two lemmas below show
  - LHS `= 0` ALWAYS (`intervalDomainLift_deriv_at_{zero,one}_eq_zero`): the
    zero-extension forces the two-sided derivative of any lift to vanish at the
    domain endpoints (either the lift is differentiable there, in which case the
    constant-`0` side pins the derivative to `0`, or it is not, in which case
    `deriv` is `0` by convention).
  - RHS `= 0` at `x = 0` (`intervalSemigroupOperator_deriv_at_zero_eq_zero`):
    the zeroth-reflection kernel is even about `0`
    (`= (1/2)(S g + reflected S g)`), so the spatial derivative at `0` vanishes.

  At `x = 1`, however, the RHS need NOT vanish: `intervalSemigroupOperator` uses
  `normalizedZerothReflectionKernel = (1/2)(heatKernel(x−y)+heatKernel(x+y))`,
  which reflects only about `0` — it is NOT Neumann at the right endpoint `1`.
  So `hGradEq` is genuinely FALSE at `x = 1` for generic data (LHS `= 0` ≠ RHS).
  This is the precise sense in which `hGradEq` is "real boundary content, not
  bookkeeping": the architecturally-sound resolutions are (a) weaken `hGradEq`
  to the interior `Ioo 0 1` and bound the endpoint gradient directly via
  LHS `= 0` (`|0| ≤ G_u`), or (b) rebuild the Duhamel operator on the FULL
  Neumann kernel (`intervalNeumannFullKernel`, Neumann at both endpoints). -/

/-- **Left-endpoint Neumann for the zeroth-reflection semigroup.**  The spatial
derivative of `intervalSemigroupOperator L t f` vanishes at `x = 0` — the
operator equals `(1/2)(S g + reflected S g)` (even about `0`), so its derivative
value at `0` is `(1/2)D − (1/2)D = 0`. -/
theorem intervalSemigroupOperator_deriv_at_zero_eq_zero
    {L t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    (hf_int : MeasureTheory.Integrable f (intervalMeasure L)) :
    deriv (fun z : ℝ => intervalSemigroupOperator L t f z) 0 = 0 := by
  have h := ShenWork.RegularityBootstrap.intervalSemigroupOperator_hasDerivAt
    (L := L) (t := t) (x := 0) ht hf_int
  simp only [neg_zero, sub_self] at h
  exact h.deriv

/-- **Zero endpoint derivative of any lift at `x = 0`.**  For every
`g : intervalDomainPoint → ℝ`, the zero-extension `intervalDomainLift g` has
`deriv … 0 = 0`: if it is differentiable at `0` the constant-`0` left side pins
the derivative to `0`; otherwise `deriv` is `0` by convention. -/
theorem intervalDomainLift_deriv_at_zero_eq_zero (g : intervalDomainPoint → ℝ) :
    deriv (intervalDomainLift g) 0 = 0 := by
  by_cases hdiff : DifferentiableAt ℝ (intervalDomainLift g) 0
  · have hHas := hdiff.hasDerivAt
    have hEqOn : ∀ z ∈ Set.Iio (0 : ℝ), intervalDomainLift g z = 0 := by
      intro z hz
      have hzn : z ∉ Set.Icc (0 : ℝ) 1 := fun h => absurd h.1 (not_le.mpr hz)
      simp [intervalDomainLift, hzn]
    have hval : intervalDomainLift g 0 = 0 := by
      have h1 := (hdiff.continuousAt.continuousWithinAt (s := Set.Iio (0 : ℝ))).tendsto
      have h2 : Filter.Tendsto (intervalDomainLift g)
          (nhdsWithin 0 (Set.Iio 0)) (𝓝 0) := by
        refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards [self_mem_nhdsWithin] with z hz using (hEqOn z hz).symm
      exact tendsto_nhds_unique h1 h2
    have hc : HasDerivWithinAt (intervalDomainLift g) 0 (Set.Iio 0) 0 :=
      (hasDerivWithinAt_const (0 : ℝ) (Set.Iio (0 : ℝ)) (0 : ℝ)).congr hEqOn hval
    have huniq := uniqueDiffWithinAt_Iio (0 : ℝ)
    have e1 := hHas.hasDerivWithinAt.derivWithin huniq
    have e2 := hc.derivWithin huniq
    exact e1.symm.trans e2
  · exact deriv_zero_of_not_differentiableAt hdiff

/-- **Zero endpoint derivative of any lift at `x = 1`** (right-endpoint mirror of
`intervalDomainLift_deriv_at_zero_eq_zero`). -/
theorem intervalDomainLift_deriv_at_one_eq_zero (g : intervalDomainPoint → ℝ) :
    deriv (intervalDomainLift g) 1 = 0 := by
  by_cases hdiff : DifferentiableAt ℝ (intervalDomainLift g) 1
  · have hHas := hdiff.hasDerivAt
    have hEqOn : ∀ z ∈ Set.Ioi (1 : ℝ), intervalDomainLift g z = 0 := by
      intro z hz
      have hzn : z ∉ Set.Icc (0 : ℝ) 1 := fun h => absurd h.2 (not_le.mpr hz)
      simp [intervalDomainLift, hzn]
    have hval : intervalDomainLift g 1 = 0 := by
      have h1 := (hdiff.continuousAt.continuousWithinAt (s := Set.Ioi (1 : ℝ))).tendsto
      have h2 : Filter.Tendsto (intervalDomainLift g)
          (nhdsWithin 1 (Set.Ioi 1)) (𝓝 0) := by
        refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards [self_mem_nhdsWithin] with z hz using (hEqOn z hz).symm
      exact tendsto_nhds_unique h1 h2
    have hc : HasDerivWithinAt (intervalDomainLift g) 0 (Set.Ioi 1) 1 :=
      (hasDerivWithinAt_const (1 : ℝ) (Set.Ioi (1 : ℝ)) (0 : ℝ)).congr hEqOn hval
    have huniq := uniqueDiffWithinAt_Ioi (1 : ℝ)
    have e1 := hHas.hasDerivWithinAt.derivWithin huniq
    have e2 := hc.derivWithin huniq
    exact e1.symm.trans e2
  · exact deriv_zero_of_not_differentiableAt hdiff

end ShenWork
