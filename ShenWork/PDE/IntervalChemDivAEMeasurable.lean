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
    (hsol.regularity.2.2.1 τ hτ).1
  have hC2v : ContDiffOn ℝ 2 (intervalDomainLift (v τ)) (Set.Ioo (0:ℝ) 1) :=
    (hsol.regularity.2.2.1 τ hτ).2
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
    (hsol.regularity.2.2.2.2.2.2.2.2).1
  have hcontV : ContinuousOn
      (Function.uncurry (fun s y => intervalDomainLift (v s) y))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.2.2.2.2).2
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
        (((hsol.regularity.2.2.1 s hs).2).differentiableOn (by norm_num)).differentiableAt
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

end ShenWork
