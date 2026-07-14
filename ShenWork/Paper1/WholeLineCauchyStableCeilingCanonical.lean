import ShenWork.Paper1.WholeLineCauchyStableCeilingPDE
import ShenWork.Paper1.WholeLineCauchyClassicalSolution

open Filter Topology MeasureTheory Real Set
open scoped BoundedContinuousFunction Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# Stable ceiling for the canonical whole-line Cauchy solution

The abstract nonlocal slab maximum principle is instantiated with the
ordinary positive-time derivatives of the canonical BUC fixed point.  A
strictly shorter auxiliary slab avoids asking for a time derivative at the
construction endpoint.
-/

/-- Before the construction endpoint, every canonical physical fixed point
stays below any stable ceiling which bounds its initial datum. -/
theorem wholeLineCauchyBUCMildFixedPoint_stable_ceiling_Ico
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    {M T C : ℝ} (hM : 0 ≤ M) (hT : 0 < T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M)
    (hC1 : 1 ≤ C)
    (hmargin : 1 + max p.χ 0 * C ^ (p.m + p.γ - 1) ≤ C ^ p.α)
    (hinit : ∀ x, u₀.1 x ≤ C) :
    ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x,
      (wholeLineBUCTrajectoryExtend hT.le
        (wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall) t).1 x ≤ C := by
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall
  let ue : ℝ → ℝ → ℝ := fun t x =>
    (wholeLineBUCTrajectoryExtend hT.le U t).1 x
  have hjoint : Continuous (fun q : ℝ × ℝ => ue q.1 q.2) := by
    have hmap : Continuous
        (fun q : ℝ × ℝ => (Set.projIcc 0 T hT.le q.1, q.2)) :=
      (continuous_projIcc.comp continuous_fst).prodMk continuous_snd
    simpa [ue, wholeLineBUCTrajectoryExtend] using
      (wholeLineBUCTrajectory_jointContinuous U).comp hmap
  intro t ht x
  by_cases ht0 : t = 0
  · subst t
    have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
    have hext0 : wholeLineBUCTrajectoryExtend hT.le U 0 = U ⟨0, hzero⟩ :=
      wholeLineBUCTrajectoryExtend_eq hT.le U hzero
    have hU0 : U ⟨0, hzero⟩ = u₀ := by
      simpa [U] using wholeLineCauchyBUCMildFixedPoint_initial
        p hM hT.le u₀ hsmall hzero
    change (wholeLineBUCTrajectoryExtend hT.le U 0).1 x ≤ C
    rw [hext0, hU0]
    exact hinit x
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  let S : ℝ := (t + T) / 2
  have hSpos : 0 < S := by dsimp [S]; linarith
  have hST : S < T := by dsimp [S]; linarith [ht.2]
  have htS : t ≤ S := by dsimp [S]; linarith [ht.2]
  have hclosedStrip : ∀ s ∈ Set.Icc (0 : ℝ) S, ∀ y,
      ue s y ∈ Set.Icc (0 : ℝ) M := by
    intro s hs y
    have hsT : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans hST.le⟩
    have hext : wholeLineBUCTrajectoryExtend hT.le U s = U ⟨s, hsT⟩ :=
      wholeLineBUCTrajectoryExtend_eq hT.le U hsT
    simpa [ue, hext, U] using hstrip ⟨s, hsT⟩ y
  have hceiling : wholeLineSlabSup S ue ≤ C := by
    apply wholeLineSlabSup_le_of_stable_resolver_pde
      p hregime hSpos hC1 hmargin hjoint
    · intro s hs y
      exact (hclosedStrip s hs y).1
    · intro s hs y
      exact (hclosedStrip s hs y).2
    · intro y
      have hzeroT : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
      have hext0 : wholeLineBUCTrajectoryExtend hT.le U 0 = U ⟨0, hzeroT⟩ :=
        wholeLineBUCTrajectoryExtend_eq hT.le U hzeroT
      have hU0 : U ⟨0, hzeroT⟩ = u₀ := by
        simpa [U] using wholeLineCauchyBUCMildFixedPoint_initial
          p hM hT.le u₀ hsmall hzeroT
      simpa [ue, hext0, hU0] using hinit y
    · intro s y hs
      have hsT : s < T := hs.2.trans_lt hST
      simpa [ue, U] using
        (wholeLineCauchyBUCMildFixedPoint_physical_pde_hasDerivAt
          p (theta := (1 / 2 : ℝ)) (eta := (1 / 4 : ℝ))
          hM hT.le u₀ hsmall hs.1 hsT
          (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) hstrip y).differentiableAt.hasDerivAt
    · intro s y hs
      have hsT : s ∈ Set.Icc (0 : ℝ) T :=
        ⟨hs.1.le, hs.2.trans hST.le⟩
      let zs : Set.Icc (0 : ℝ) T := ⟨s, hsT⟩
      have hext : wholeLineBUCTrajectoryExtend hT.le U s = U zs :=
        wholeLineBUCTrajectoryExtend_eq hT.le U hsT
      change HasDerivAt (fun w : ℝ =>
        (wholeLineBUCTrajectoryExtend hT.le U s).1 w)
        (deriv (fun w : ℝ =>
          (wholeLineBUCTrajectoryExtend hT.le U s).1 w) y) y
      rw [hext]
      simpa [U, zs] using
        (wholeLineCauchyBUCMildFixedPoint_spatial_hasDerivAt_positive
          p hM hT.le u₀ hsmall zs hs.1 y).differentiableAt.hasDerivAt
    · intro s y hs
      have hsT : s ∈ Set.Icc (0 : ℝ) T :=
        ⟨hs.1.le, hs.2.trans hST.le⟩
      let zs : Set.Icc (0 : ℝ) T := ⟨s, hsT⟩
      have hext : wholeLineBUCTrajectoryExtend hT.le U s = U zs :=
        wholeLineBUCTrajectoryExtend_eq hT.le U hsT
      have hwindow : ∀ r ∈ Set.Icc (s / 2) s, ∀ q,
          (wholeLineBUCTrajectoryExtend hT.le
            (wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall) r).1 q ∈
              Set.Icc (0 : ℝ) M := by
        intro r hr q
        exact hstrip (Set.projIcc 0 T hT.le r) q
      change HasDerivAt
        (fun w : ℝ => deriv (fun q : ℝ =>
          (wholeLineBUCTrajectoryExtend hT.le U s).1 q) w)
        (deriv (fun w : ℝ => deriv (fun q : ℝ =>
          (wholeLineBUCTrajectoryExtend hT.le U s).1 q) w) y) y
      rw [hext]
      simpa [U, zs] using
        (wholeLineCauchyBUCMildFixedPoint_spatial_second_hasDerivAt_positive
          (theta := (1 / 2 : ℝ)) (eta := (1 / 4 : ℝ))
          p hM hT.le u₀ hsmall zs hs.1
          (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) hwindow y).differentiableAt.hasDerivAt
    · intro s y hs
      have hsTlt : s < T := hs.2.trans_lt hST
      have hsT : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1.le, hsTlt.le⟩
      let zs : Set.Icc (0 : ℝ) T := ⟨s, hsT⟩
      have hext : wholeLineBUCTrajectoryExtend hT.le U s = U zs :=
        wholeLineBUCTrajectoryExtend_eq hT.le U hsT
      have htime :=
        (wholeLineCauchyBUCMildFixedPoint_physical_pde_hasDerivAt
          p (theta := (1 / 2 : ℝ)) (eta := (1 / 4 : ℝ))
          hM hT.le u₀ hsmall hs.1 hsTlt
          (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) hstrip y).deriv
      have hux :=
        (wholeLineCauchyBUCMildFixedPoint_spatial_hasDerivAt_positive
          p hM hT.le u₀ hsmall zs hs.1 y).differentiableAt.hasDerivAt
      have hflux := (wholeLineChemotaxisFlux_hasDerivAt p
        (WholeLineBUC.isCUnifBdd (U zs))
        (fun q => (hstrip zs q).1) hux).deriv
      rw [hflux] at htime
      simpa [ue, U, hext, wholeLineLogisticSource, reactionFun] using htime
  have hueSlab : ue t x ≤ wholeLineSlabSup S ue :=
    le_wholeLineSlabSup hSpos.le
      (fun s hs y => (hclosedStrip s hs y).2) ⟨htpos.le, htS⟩ x
  simpa [ue, U] using hueSlab.trans hceiling

/-- Time continuity passes the strict-interior ceiling to the construction
endpoint, so the entire closed canonical strip obeys the same bound. -/
theorem wholeLineCauchyBUCMildFixedPoint_stable_ceiling_Icc
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    {M T C : ℝ} (hM : 0 ≤ M) (hT : 0 < T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M)
    (hC1 : 1 ≤ C)
    (hmargin : 1 + max p.χ 0 * C ^ (p.m + p.γ - 1) ≤ C ^ p.α)
    (hinit : ∀ x, u₀.1 x ≤ C) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineBUCTrajectoryExtend hT.le
        (wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall) t).1 x ≤ C := by
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall
  have hIco := wholeLineCauchyBUCMildFixedPoint_stable_ceiling_Ico
    p hregime hM hT u₀ hsmall hstrip hC1 hmargin hinit
  have hjoint : Continuous (fun q : ℝ × ℝ =>
      (wholeLineBUCTrajectoryExtend hT.le U q.1).1 q.2) := by
    have hmap : Continuous
        (fun q : ℝ × ℝ => (Set.projIcc 0 T hT.le q.1, q.2)) :=
      (continuous_projIcc.comp continuous_fst).prodMk continuous_snd
    simpa [wholeLineBUCTrajectoryExtend] using
      (wholeLineBUCTrajectory_jointContinuous U).comp hmap
  intro t ht x
  by_cases htT : t < T
  · simpa [U] using hIco t ⟨ht.1, htT⟩ x
  have hteq : t = T := by linarith [ht.2]
  subst t
  let f : ℝ → ℝ := fun s => (wholeLineBUCTrajectoryExtend hT.le U s).1 x
  have hfcont : Continuous f := by
    exact hjoint.comp (continuous_id.prodMk continuous_const)
  have hlim : Tendsto f (𝓝[<] T) (𝓝 (f T)) :=
    hfcont.continuousAt.tendsto.mono_left inf_le_left
  have hleft : ∀ᶠ s in 𝓝[<] T, s < T := self_mem_nhdsWithin
  have hposNhds : ∀ᶠ s in 𝓝 T, 0 < s := Ioi_mem_nhds hT
  have hpos : ∀ᶠ s in 𝓝[<] T, 0 < s :=
    hposNhds.filter_mono inf_le_left
  have hbound : ∀ᶠ s in 𝓝[<] T, f s ∈ Set.Iic C := by
    filter_upwards [hleft, hpos] with s hsT hs0
    exact hIco s ⟨hs0.le, hsT⟩ x
  exact Set.mem_Iic.mp (isClosed_Iic.mem_of_tendsto hlim hbound)

/-- The canonical stable ceiling from `WholeLineCauchyGlobalBounds` bounds
the entire physical construction strip. -/
theorem wholeLineCauchyBUCMildFixedPoint_le_stableCeiling
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    {M T : ℝ} (hM : 0 ≤ M) (hT : 0 < T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineBUCTrajectoryExtend hT.le
        (wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall) t).1 x ≤
          wholeLineCauchyStableCeiling p u₀ := by
  apply wholeLineCauchyBUCMildFixedPoint_stable_ceiling_Icc
    p hregime hM hT u₀ hsmall hstrip
  · exact wholeLineCauchyStableCeiling_one_le hregime u₀
  · exact wholeLineCauchyStableCeiling_margin hregime u₀
  · intro x
    exact (wholeLineCauchyStableCeiling_initial_lt p u₀ x).le

section WholeLineCauchyStableCeilingCanonicalAxiomAudit

#print axioms wholeLineCauchyBUCMildFixedPoint_stable_ceiling_Ico
#print axioms wholeLineCauchyBUCMildFixedPoint_stable_ceiling_Icc
#print axioms wholeLineCauchyBUCMildFixedPoint_le_stableCeiling

end WholeLineCauchyStableCeilingCanonicalAxiomAudit

end ShenWork.Paper1
