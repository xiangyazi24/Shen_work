import ShenWork.Paper2.IntervalChiNegH1PhysicalScalarContinuity
import ShenWork.Paper2.IntervalChiNegH1InitialDerivativeRHS
import ShenWork.Paper2.IntervalChiNegH1ZeroSlabPhysicalRHS

/-!
# Classical strict-slab continuity for the physical H¹ scalar route

This file discharges the strict-positive-time continuity inputs in the
physical H¹ strict/initial route from the existing classical-solution
regularity and representative APIs.  It does not address the physical identity,
sqrt estimates, or zero-window Young/component-square estimates.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1Energy
open ShenWork.Paper2.IntervalChiNegH1EnergyIdentity
open ShenWork.Paper2.IntervalChiNegH1DerivativeIntegrability
open ShenWork.Paper2.IntervalChiNegH1InitialDerivativeRHS
open ShenWork.Paper2.IntervalChiNegH1LiftDeriv2Transfer
open ShenWork.Paper2.IntervalChiNegH1ChemDivRepresentative
open ShenWork.Paper2.IntervalChiNegH1PhysicalInitialRHS
open ShenWork.Paper2.IntervalChiNegH1PhysicalRHSScalars
open ShenWork.Paper2.IntervalChiNegH1PhysicalScalarContinuity

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1PhysicalClassicalContinuity

private theorem strict_slab_subset_ioo
    {T a b : ℝ} (ha : 0 < a) (_hab : a ≤ b) (hbT : b < T) :
    Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1 ⊆
      Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1 := by
  intro z hz
  exact ⟨⟨lt_of_lt_of_le ha hz.1.1, lt_of_le_of_lt hz.1.2 hbT⟩, hz.2⟩

private theorem one_add_lift_v_pos_on_strict_slab
    {p : CM2Params} {T a b : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ha : 0 < a) (_hab : a ≤ b) (hbT : b < T) :
    ∀ z ∈ Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1,
      0 < 1 +
        Function.uncurry
          (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z := by
  intro z hz
  rcases z with ⟨t, x⟩
  rcases hz with ⟨ht, hx⟩
  simp only [Function.uncurry_apply_pair]
  rw [intervalDomainLift, dif_pos hx]
  have htI : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hbT⟩
  have hvnn : 0 ≤ v t ⟨x, hx⟩ := hsol.v_nonneg htI.1 htI.2
  linarith

private theorem continuousOn_slice_of_uncurry
    {F : ℝ → ℝ → ℝ} {r : ℝ} {s : Set ℝ}
    (hF : ContinuousOn (Function.uncurry F) (Set.Icc r r ×ˢ s)) :
    ContinuousOn (F r) s := by
  have hpair : ContinuousOn (fun x : ℝ => ((r, x) : ℝ × ℝ)) s :=
    continuousOn_const.prodMk continuousOn_id
  have hmaps :
      Set.MapsTo (fun x : ℝ => ((r, x) : ℝ × ℝ)) s
        (Set.Icc r r ×ˢ s) := by
    intro x hx
    exact ⟨⟨le_rfl, le_rfl⟩, hx⟩
  simpa [Function.uncurry] using hF.comp hpair hmaps

private theorem continuousOn_Ioc_of_continuousOn_strictWindows
    {f : ℝ → ℝ} {T δ : ℝ}
    (_hδ_pos : 0 < δ) (hδ_before : δ < T)
    (hcont : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn f (Set.Icc a b)) :
    ContinuousOn f (Set.Ioc (0 : ℝ) δ) := by
  intro r hr
  let a : ℝ := r / 2
  have ha_pos : 0 < a := by
    dsimp [a]
    linarith [hr.1]
  have ha_lt_r : a < r := by
    dsimp [a]
    linarith [hr.1]
  have ha_le_delta : a ≤ δ := by
    dsimp [a]
    linarith [hr.1, hr.2]
  have hstrict : ContinuousOn f (Set.Icc a δ) :=
    hcont ha_pos ha_le_delta hδ_before
  have hrIcc : r ∈ Set.Icc a δ :=
    ⟨le_of_lt ha_lt_r, hr.2⟩
  have hwithin : ContinuousWithinAt f (Set.Icc a δ) r :=
    hstrict r hrIcc
  refine hwithin.mono_of_mem_nhdsWithin ?_
  refine
    Filter.mem_of_superset
      (inter_mem_nhdsWithin (Set.Ioc (0 : ℝ) δ)
        (Ioi_mem_nhds ha_lt_r)) ?_
  intro y hy
  exact ⟨le_of_lt hy.2, hy.1.2⟩

private theorem aestronglyMeasurable_on_Ioc_of_continuousOn_strictWindows
    {f : ℝ → ℝ} {T δ : ℝ}
    (hδ_pos : 0 < δ) (hδ_before : δ < T)
    (hcont : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn f (Set.Icc a b)) :
    AEStronglyMeasurable f (volume.restrict (Set.Ioc (0 : ℝ) δ)) :=
  (continuousOn_Ioc_of_continuousOn_strictWindows
    hδ_pos hδ_before hcont).aestronglyMeasurable measurableSet_Ioc

private theorem
    abs_liftDeriv2_mul_part_aestronglyMeasurable_of_rep_product_cont
    {u : ℝ → intervalDomainPoint → ℝ}
    {F part : ℝ → ℝ → ℝ} {r : ℝ}
    (hCont :
      ContinuousOn (Function.uncurry (fun t x => F t x * part t x))
        (Set.Icc r r ×ˢ Set.Icc (0 : ℝ) 1))
    (hEqInterior :
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry F)
        (Set.Icc r r ×ˢ Set.Ioo (0 : ℝ) 1)) :
    AEStronglyMeasurable
      (fun x => |liftDeriv2 u r x * part r x|)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  have hSlice :
      ContinuousOn (fun x => F r x * part r x) (Set.Icc (0 : ℝ) 1) :=
    continuousOn_slice_of_uncurry
      (F := fun t x => F t x * part t x)
      (r := r) (s := Set.Icc (0 : ℝ) 1) hCont
  have hRepMeas :
      AEStronglyMeasurable
        (fun x => |F r x * part r x|)
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    exact hSlice.abs.aestronglyMeasurable_of_subset_isCompact isCompact_Icc
      measurableSet_Ioc (fun x hx => ⟨le_of_lt hx.1, hx.2⟩)
  refine hRepMeas.congr ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
  have hne1 : ∀ᵐ x : ℝ ∂volume, x ≠ (1 : ℝ) := by
    have heq : {x : ℝ | ¬ x ≠ (1 : ℝ)} = {(1 : ℝ)} := by
      ext x
      simp
    rw [ae_iff, heq]
    exact Real.volume_singleton
  filter_upwards [hne1] with x hxne hxIoc
  have hxIoo : x ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨hxIoc.1, lt_of_le_of_ne hxIoc.2 hxne⟩
  have hEq := hEqInterior (x := (r, x))
    (Set.mem_prod.mpr ⟨⟨le_rfl, le_rfl⟩, hxIoo⟩)
  simp only [Function.uncurry_apply_pair] at hEq
  simp [hEq]

private theorem square_intervalIntegrable_of_uncurry_continuousOn_slice
    {part : ℝ → ℝ → ℝ} {r : ℝ}
    (hCont :
      ContinuousOn (Function.uncurry part)
        (Set.Icc r r ×ˢ Set.Icc (0 : ℝ) 1)) :
    IntervalIntegrable (fun x => (part r x) ^ 2) volume (0 : ℝ) 1 := by
  exact ContinuousOn.intervalIntegrable_of_Icc
    (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    ((continuousOn_slice_of_uncurry
      (F := part) (r := r) (s := Set.Icc (0 : ℝ) 1) hCont).pow 2)

private theorem liftDeriv2_sq_intervalIntegrable_of_rep_cont
    {u : ℝ → intervalDomainPoint → ℝ}
    {F : ℝ → ℝ → ℝ} {r : ℝ}
    (hCont :
      ContinuousOn (Function.uncurry F)
        (Set.Icc r r ×ˢ Set.Icc (0 : ℝ) 1))
    (hEqInterior :
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry F)
        (Set.Icc r r ×ˢ Set.Ioo (0 : ℝ) 1)) :
    IntervalIntegrable (fun x => (liftDeriv2 u r x) ^ 2)
      volume (0 : ℝ) 1 := by
  have hRepInt :
      IntervalIntegrable (fun x => (F r x) ^ 2) volume (0 : ℝ) 1 :=
    square_intervalIntegrable_of_uncurry_continuousOn_slice
      (part := F) (r := r) hCont
  refine hRepInt.congr_ae ?_
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
  have hne1 : ∀ᵐ x : ℝ ∂volume, x ≠ (1 : ℝ) := by
    have heq : {x : ℝ | ¬ x ≠ (1 : ℝ)} = {(1 : ℝ)} := by
      ext x
      simp
    rw [ae_iff, heq]
    exact Real.volume_singleton
  filter_upwards [hne1] with x hxne hxIoc
  have hxIoo : x ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨hxIoc.1, lt_of_le_of_ne hxIoc.2 hxne⟩
  have hEq := hEqInterior (x := (r, x))
    (Set.mem_prod.mpr ⟨⟨le_rfl, le_rfl⟩, hxIoo⟩)
  simp only [Function.uncurry_apply_pair] at hEq
  simp [hEq]

/-- Strict-slab continuity of the concrete physical `liftDeriv2`
representative with the closed-slab chemotaxis-divergence representative. -/
theorem liftDeriv2PhysicalRHSWithChemRep_continuousOn_strictSlab_of_classicalSolution
    {p : CM2Params} {T a b : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    ContinuousOn
      (Function.uncurry
        (liftDeriv2PhysicalRHSWithChemRep p u
          (liftChemotaxisDivPhysicalRep p u v)))
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) :=
  liftDeriv2PhysicalRHSWithChemRep_continuousOn_of_components
    (p := p) (u := u)
    (chemRep := liftChemotaxisDivPhysicalRep p u v)
    (s := Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)
    (liftTimeDeriv_continuousOn_strictSlab_of_classicalSolution
      (p := p) (u := u) (v := v) (T := T) hsol ha hab hbT)
    (liftChemotaxisDivPhysicalRep_continuousOn_strictSlab_of_classicalSolution
      (p := p) (u := u) (v := v) (T := T) hsol ha hab hbT)
    (logisticReaction_continuousOn_strictSlab_of_classicalSolution
      (p := p) (u := u) (v := v) (T := T) hsol ha hab hbT)

/-- Strict-slab interior equality of literal `liftDeriv2` with the concrete
physical RHS representative using `liftChemotaxisDivPhysicalRep`. -/
theorem liftDeriv2_eq_liftDeriv2PhysicalRHSWithChemRep_strictSlab_interior_of_classicalSolution
    {p : CM2Params} {T a b : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    Set.EqOn
      (Function.uncurry (fun t x => liftDeriv2 u t x))
      (Function.uncurry
        (liftDeriv2PhysicalRHSWithChemRep p u
          (liftChemotaxisDivPhysicalRep p u v)))
      (Set.Icc a b ×ˢ Set.Ioo (0 : ℝ) 1) := by
  intro z hz
  have hphys :=
    liftDeriv2_eq_liftDeriv2PhysicalRHS_strictSlab_interior_of_classicalSolution
      (p := p) (u := u) (v := v) (T := T) hsol ha hab hbT hz
  have hchem :=
    lift_chemotaxisDiv_eq_liftChemotaxisDivPhysicalRep_strictSlab_interior
      (p := p) (u := u) (v := v) (T := T) hsol ha hab hbT hz
  rcases z with ⟨t, x⟩
  simp only [Function.uncurry_apply_pair] at hphys hchem ⊢
  rw [hphys]
  simp [liftDeriv2PhysicalRHS, liftDeriv2PhysicalRHSWithChemRep, hchem]

/-- Strict-slab continuity of the `u_x v_x / (1+v)^β` taxis part from the
existing joint-continuity producers. -/
theorem H1PhysicalChemTaxisPart_continuousOn_strictSlab_of_classicalSolution
    {p : CM2Params} {T a b : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    ContinuousOn (Function.uncurry (H1PhysicalChemTaxisPart p u v))
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) := by
  have hsub := strict_slab_subset_ioo (T := T) ha hab hbT
  have hreg := hsol.regularity
  change intervalDomainClassicalRegularity T u v at hreg
  have hv_all :
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
    hreg.2.2.2.2.2.2.2
  have hv := hv_all.mono hsub
  have hux :=
    (intervalDomain_dx_u_jointlyContinuous (params := p)
      (T := T) (u := u) (v := v) hsol).mono hsub
  have hvx :=
    (intervalDomain_dx_v_jointlyContinuous (params := p)
      (T := T) (u := u) (v := v) hsol).mono hsub
  have hbase :
      ContinuousOn
        (fun z : ℝ × ℝ =>
          1 + Function.uncurry
            (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) :=
    continuousOn_const.add hv
  have hbase_pos :=
    one_add_lift_v_pos_on_strict_slab
      (p := p) (u := u) (v := v) (T := T) hsol ha hab hbT
  have hden :
      ContinuousOn
        (fun z : ℝ × ℝ =>
          (1 + Function.uncurry
            (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z) ^ p.β)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) :=
    hbase.rpow_const (fun z hz => Or.inl (ne_of_gt (hbase_pos z hz)))
  have hden_ne : ∀ z ∈ Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1,
      (1 + Function.uncurry
        (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z) ^ p.β ≠ 0 := by
    intro z hz
    exact ne_of_gt (Real.rpow_pos_of_pos (hbase_pos z hz) _)
  simpa [H1PhysicalChemTaxisPart, Function.uncurry] using
    (hux.mul hvx).div hden hden_ne

/-- Strict-slab continuity of the physical `u v_xx`/denominator part from the
reaction representative and `v_x` joint continuity. -/
theorem H1PhysicalChemUvxxPart_continuousOn_strictSlab_of_classicalSolution
    {p : CM2Params} {T a b : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    ContinuousOn (Function.uncurry (H1PhysicalChemUvxxPart p u v))
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) := by
  have hsub := strict_slab_subset_ioo (T := T) ha hab hbT
  have hreg := hsol.regularity
  change intervalDomainClassicalRegularity T u v at hreg
  have hu_all :
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
    hreg.2.2.2.2.2.2.1
  have hv_all :
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
    hreg.2.2.2.2.2.2.2
  have hu := hu_all.mono hsub
  have hv := hv_all.mono hsub
  have hvx :=
    (intervalDomain_dx_v_jointlyContinuous (params := p)
      (T := T) (u := u) (v := v) hsol).mono hsub
  have hvxxRep :=
    (intervalDomain_v_xx_reaction_jointContinuous (params := p)
      (T := T) (u := u) (v := v) hsol).mono hsub
  have hbase :
      ContinuousOn
        (fun z : ℝ × ℝ =>
          1 + Function.uncurry
            (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) :=
    continuousOn_const.add hv
  have hbase_pos :=
    one_add_lift_v_pos_on_strict_slab
      (p := p) (u := u) (v := v) (T := T) hsol ha hab hbT
  have hdenβ :
      ContinuousOn
        (fun z : ℝ × ℝ =>
          (1 + Function.uncurry
            (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z) ^ p.β)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) :=
    hbase.rpow_const (fun z hz => Or.inl (ne_of_gt (hbase_pos z hz)))
  have hdenβ1 :
      ContinuousOn
        (fun z : ℝ × ℝ =>
          (1 + Function.uncurry
            (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z) ^
            (p.β + 1))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) :=
    hbase.rpow_const (fun z hz => Or.inl (ne_of_gt (hbase_pos z hz)))
  have hdenβ_ne : ∀ z ∈ Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1,
      (1 + Function.uncurry
        (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z) ^ p.β ≠ 0 := by
    intro z hz
    exact ne_of_gt (Real.rpow_pos_of_pos (hbase_pos z hz) _)
  have hdenβ1_ne : ∀ z ∈ Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1,
      (1 + Function.uncurry
        (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z) ^
          (p.β + 1) ≠ 0 := by
    intro z hz
    exact ne_of_gt (Real.rpow_pos_of_pos (hbase_pos z hz) _)
  have hterm1 := (hu.mul hvxxRep).div hdenβ hdenβ_ne
  have hterm2 := ((hu.const_mul p.β).mul (hvx.pow 2)).div hdenβ1 hdenβ1_ne
  simpa [H1PhysicalChemUvxxPart, Function.uncurry] using hterm1.sub hterm2

/-- Strict-slab continuity of the physical logistic reaction part. -/
theorem H1PhysicalLogisticReactionPart_continuousOn_strictSlab_of_classicalSolution
    {p : CM2Params} {T a b : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    ContinuousOn (Function.uncurry (H1PhysicalLogisticReactionPart p u))
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) := by
  have hsub := strict_slab_subset_ioo (T := T) ha hab hbT
  simpa [H1PhysicalLogisticReactionPart, Function.uncurry] using
    (intervalDomain_u_logistic_jointContinuous
      (params := p) (T := T) (u := u) (v := v) hsol).mono hsub

/-- Classical solutions supply the representative-integrand continuity package
needed by the physical H¹ strict scalar-continuity route. -/
theorem H1PhysicalRHSRepIntegrandsContinuousStrictBefore_of_classicalSolution
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v) :
    H1PhysicalRHSRepIntegrandsContinuousStrictBefore p u v T
      (liftDeriv2PhysicalRHSWithChemRep p u
        (liftChemotaxisDivPhysicalRep p u v)) :=
  H1PhysicalRHSRepIntegrandsContinuousStrictBefore_of_parts
    (p := p) (u := u) (v := v) (T := T)
    (F := liftDeriv2PhysicalRHSWithChemRep p u
      (liftChemotaxisDivPhysicalRep p u v))
    (fun {_a _b} ha hab hbT =>
      liftDeriv2PhysicalRHSWithChemRep_continuousOn_strictSlab_of_classicalSolution
        (p := p) (u := u) (v := v) (T := T) hsol ha hab hbT)
    (fun {_a _b} ha hab hbT =>
      liftDeriv2_eq_liftDeriv2PhysicalRHSWithChemRep_strictSlab_interior_of_classicalSolution
        (p := p) (u := u) (v := v) (T := T) hsol ha hab hbT)
    (fun {_a _b} ha hab hbT =>
      H1PhysicalChemTaxisPart_continuousOn_strictSlab_of_classicalSolution
        (p := p) (T := T) (u := u) (v := v) hsol ha hab hbT)
    (fun {_a _b} ha hab hbT =>
      H1PhysicalChemUvxxPart_continuousOn_strictSlab_of_classicalSolution
        (p := p) (T := T) (u := u) (v := v) hsol ha hab hbT)
    (fun {_a _b} ha hab hbT =>
      H1PhysicalLogisticReactionPart_continuousOn_strictSlab_of_classicalSolution
        (p := p) (T := T) (u := u) (v := v) hsol ha hab hbT)

/-- The strict physical component-continuity package follows from classical
strict-positive-time regularity, without zero-start `lapL2sq` continuity. -/
theorem H1PhysicalRHSComponentsContinuousStrictBefore_of_classicalSolution
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v) :
    H1PhysicalRHSComponentsContinuousStrictBefore p u v T :=
  H1PhysicalRHSComponentsContinuousStrictBefore_of_strictSlab_repIntegrands
    (H1PhysicalRHSRepIntegrandsContinuousStrictBefore_of_classicalSolution
      (p := p) (u := u) (v := v) (T := T) hsol)

/-- Classical strict-positive-time component continuity supplies the assembled
physical RHS a.e.-strong measurability on any zero-start window before `T`.
This is only a measurability producer; it does not provide any time
integrability or majorant. -/
theorem H1PhysicalRHSValue_aestronglyMeasurableBefore_of_classicalSolution
    {p : CM2Params} {T δ : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hδ_pos : 0 < δ) (hδ_before : δ < T) :
    AEStronglyMeasurable
      (H1IdentityRHSValue p u
        (H1PhysicalTaxisX p u v)
        (H1PhysicalUvxxX p u v)
        (H1PhysicalReactX p u))
      (volume.restrict (Set.Ioc (0 : ℝ) δ)) := by
  have hStrict :=
    H1PhysicalRHSComponentsContinuousStrictBefore_of_classicalSolution
      (p := p) (u := u) (v := v) (T := T) hsol
  exact
    H1IdentityRHSValue_aestronglyMeasurable_of_components
      (p := p) (u := u)
      (taxisX := H1PhysicalTaxisX p u v)
      (uvxx := H1PhysicalUvxxX p u v)
      (reactX := H1PhysicalReactX p u)
      (s := Set.Ioc (0 : ℝ) δ)
      (aestronglyMeasurable_on_Ioc_of_continuousOn_strictWindows
        hδ_pos hδ_before hStrict.components.lap_cont)
      (aestronglyMeasurable_on_Ioc_of_continuousOn_strictWindows
        hδ_pos hδ_before hStrict.components.taxis_cont)
      (aestronglyMeasurable_on_Ioc_of_continuousOn_strictWindows
        hδ_pos hδ_before hStrict.components.uvxx_cont)
      (aestronglyMeasurable_on_Ioc_of_continuousOn_strictWindows
        hδ_pos hδ_before hStrict.components.react_cont)

/-- Classical strict-slab representative continuity supplies the three
abs-product measurability fields needed by the component-square spatial Young
adapter.  This is only a measurability producer; it does not provide the square
integrability or time-integrability data. -/
theorem H1PhysicalRHSAbsProductsMeasBefore_of_classicalSolution
    {p : CM2Params} {T δ : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (_hδ_pos : 0 < δ) (hδ_before : δ < T) :
    (∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) δ),
      AEStronglyMeasurable
        (fun x => |liftDeriv2 u r x *
          H1PhysicalChemTaxisPart p u v r x|)
        (volume.restrict (Set.Ioc (0 : ℝ) 1))) ∧
    (∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) δ),
      AEStronglyMeasurable
        (fun x => |liftDeriv2 u r x *
          H1PhysicalChemUvxxPart p u v r x|)
        (volume.restrict (Set.Ioc (0 : ℝ) 1))) ∧
    (∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) δ),
      AEStronglyMeasurable
        (fun x => |liftDeriv2 u r x *
          H1PhysicalLogisticReactionPart p u r x|)
        (volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
  have hRep :=
    H1PhysicalRHSRepIntegrandsContinuousStrictBefore_of_classicalSolution
      (p := p) (u := u) (v := v) (T := T) hsol
  refine ⟨?_, ?_, ?_⟩
  · refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro r hr
    have hrT : r < T := lt_of_le_of_lt hr.2 hδ_before
    have hCont :
        ContinuousOn
          (Function.uncurry
            (fun t x =>
              liftDeriv2PhysicalRHSWithChemRep p u
                (liftChemotaxisDivPhysicalRep p u v) t x *
              H1PhysicalChemTaxisPart p u v t x))
          (Set.Icc r r ×ˢ Set.Icc (0 : ℝ) 1) := by
      simpa [H1PhysicalTaxisRepIntegrand] using
        hRep.taxis_cont (a := r) (b := r) hr.1 le_rfl hrT
    exact
      abs_liftDeriv2_mul_part_aestronglyMeasurable_of_rep_product_cont
        (u := u)
        (F := liftDeriv2PhysicalRHSWithChemRep p u
          (liftChemotaxisDivPhysicalRep p u v))
        (part := H1PhysicalChemTaxisPart p u v)
        (r := r)
        hCont
        (hRep.uxx_eqInterior (a := r) (b := r) hr.1 le_rfl hrT)
  · refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro r hr
    have hrT : r < T := lt_of_le_of_lt hr.2 hδ_before
    have hCont :
        ContinuousOn
          (Function.uncurry
            (fun t x =>
              liftDeriv2PhysicalRHSWithChemRep p u
                (liftChemotaxisDivPhysicalRep p u v) t x *
              H1PhysicalChemUvxxPart p u v t x))
          (Set.Icc r r ×ˢ Set.Icc (0 : ℝ) 1) := by
      simpa [H1PhysicalUvxxRepIntegrand] using
        hRep.uvxx_cont (a := r) (b := r) hr.1 le_rfl hrT
    exact
      abs_liftDeriv2_mul_part_aestronglyMeasurable_of_rep_product_cont
        (u := u)
        (F := liftDeriv2PhysicalRHSWithChemRep p u
          (liftChemotaxisDivPhysicalRep p u v))
        (part := H1PhysicalChemUvxxPart p u v)
        (r := r)
        hCont
        (hRep.uxx_eqInterior (a := r) (b := r) hr.1 le_rfl hrT)
  · refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro r hr
    have hrT : r < T := lt_of_le_of_lt hr.2 hδ_before
    have hCont :
        ContinuousOn
          (Function.uncurry
            (fun t x =>
              liftDeriv2PhysicalRHSWithChemRep p u
                (liftChemotaxisDivPhysicalRep p u v) t x *
              H1PhysicalLogisticReactionPart p u t x))
          (Set.Icc r r ×ˢ Set.Icc (0 : ℝ) 1) := by
      simpa [H1PhysicalReactRepIntegrand] using
        hRep.react_cont (a := r) (b := r) hr.1 le_rfl hrT
    exact
      abs_liftDeriv2_mul_part_aestronglyMeasurable_of_rep_product_cont
        (u := u)
        (F := liftDeriv2PhysicalRHSWithChemRep p u
          (liftChemotaxisDivPhysicalRep p u v))
        (part := H1PhysicalLogisticReactionPart p u)
        (r := r)
        hCont
        (hRep.uxx_eqInterior (a := r) (b := r) hr.1 le_rfl hrT)

/-- Classical strict-slab continuity supplies the a.e. spatial square
integrability fields for the component-square spatial Young adapter.  This
does not provide any time integrability of the corresponding square profiles. -/
theorem H1PhysicalRHSSpatialSquareIntegrableBefore_of_classicalSolution
    {p : CM2Params} {T δ : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (_hδ_pos : 0 < δ) (hδ_before : δ < T) :
    (∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) δ),
      IntervalIntegrable (fun x => (liftDeriv2 u r x) ^ 2)
        volume (0 : ℝ) 1) ∧
    (∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) δ),
      IntervalIntegrable
        (fun x => (H1PhysicalChemTaxisPart p u v r x) ^ 2)
        volume (0 : ℝ) 1) ∧
    (∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) δ),
      IntervalIntegrable
        (fun x => (H1PhysicalChemUvxxPart p u v r x) ^ 2)
        volume (0 : ℝ) 1) ∧
    (∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) δ),
      IntervalIntegrable
        (fun x => (H1PhysicalLogisticReactionPart p u r x) ^ 2)
        volume (0 : ℝ) 1) := by
  have hRep :=
    H1PhysicalRHSRepIntegrandsContinuousStrictBefore_of_classicalSolution
      (p := p) (u := u) (v := v) (T := T) hsol
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro r hr
    have hrT : r < T := lt_of_le_of_lt hr.2 hδ_before
    exact
      liftDeriv2_sq_intervalIntegrable_of_rep_cont
        (u := u)
        (F := liftDeriv2PhysicalRHSWithChemRep p u
          (liftChemotaxisDivPhysicalRep p u v))
        (r := r)
        (hRep.uxx_cont (a := r) (b := r) hr.1 le_rfl hrT)
        (hRep.uxx_eqInterior (a := r) (b := r) hr.1 le_rfl hrT)
  · refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro r hr
    have hrT : r < T := lt_of_le_of_lt hr.2 hδ_before
    exact
      square_intervalIntegrable_of_uncurry_continuousOn_slice
        (part := H1PhysicalChemTaxisPart p u v)
        (r := r)
        (H1PhysicalChemTaxisPart_continuousOn_strictSlab_of_classicalSolution
          (p := p) (T := T) (u := u) (v := v) hsol hr.1 le_rfl hrT)
  · refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro r hr
    have hrT : r < T := lt_of_le_of_lt hr.2 hδ_before
    exact
      square_intervalIntegrable_of_uncurry_continuousOn_slice
        (part := H1PhysicalChemUvxxPart p u v)
        (r := r)
        (H1PhysicalChemUvxxPart_continuousOn_strictSlab_of_classicalSolution
          (p := p) (T := T) (u := u) (v := v) hsol hr.1 le_rfl hrT)
  · refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro r hr
    have hrT : r < T := lt_of_le_of_lt hr.2 hδ_before
    exact
      square_intervalIntegrable_of_uncurry_continuousOn_slice
        (part := H1PhysicalLogisticReactionPart p u)
        (r := r)
        (H1PhysicalLogisticReactionPart_continuousOn_strictSlab_of_classicalSolution
          (p := p) (T := T) (u := u) (v := v) hsol hr.1 le_rfl hrT)

/-- Physical strict/initial route constructor with strict component continuity
discharged from the classical solution.  The remaining inputs are the physical
identity, sqrt estimates, and the Young zero-window majorant. -/
theorem H1PhysicalRHSStrictInitialRouteBefore_of_classical_youngScalarZero
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hId : H1PhysicalRHSIdentityBefore p u v T)
    (hBounds : H1PhysicalRHSSqrtBoundsBefore p u v T V₁ V₂ M L)
    (hYoung : H1PhysicalRHSYoungScalarZeroMajorantsBefore p u v T) :
    H1PhysicalRHSStrictInitialRouteBefore p u v T V₁ V₂ M L :=
  H1PhysicalRHSStrictInitialRouteBefore_of_repIntegrands_youngScalarZero
    hId hBounds
    (H1PhysicalRHSRepIntegrandsContinuousStrictBefore_of_classicalSolution
      (p := p) (u := u) (v := v) (T := T) hsol)
    hYoung

/-- Component-square version of the classical physical strict/initial route
constructor, using the Task94 zero-window square-data adapter. -/
theorem H1PhysicalRHSStrictInitialRouteBefore_of_classical_componentSquareZero
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hId : H1PhysicalRHSIdentityBefore p u v T)
    (hBounds : H1PhysicalRHSSqrtBoundsBefore p u v T V₁ V₂ M L)
    (hSq : H1PhysicalRHSComponentSquareZeroDataBefore p u v T) :
    H1PhysicalRHSStrictInitialRouteBefore p u v T V₁ V₂ M L :=
  H1PhysicalRHSStrictInitialRouteBefore_of_classical_youngScalarZero
    hsol hId hBounds
    (H1PhysicalRHSYoungScalarZeroMajorantsBefore_of_componentSquareZeroData hSq)

#print axioms
  liftDeriv2PhysicalRHSWithChemRep_continuousOn_strictSlab_of_classicalSolution
#print axioms
  liftDeriv2_eq_liftDeriv2PhysicalRHSWithChemRep_strictSlab_interior_of_classicalSolution
#print axioms
  H1PhysicalChemTaxisPart_continuousOn_strictSlab_of_classicalSolution
#print axioms
  H1PhysicalChemUvxxPart_continuousOn_strictSlab_of_classicalSolution
#print axioms
  H1PhysicalLogisticReactionPart_continuousOn_strictSlab_of_classicalSolution
#print axioms
  H1PhysicalRHSRepIntegrandsContinuousStrictBefore_of_classicalSolution
#print axioms
  H1PhysicalRHSComponentsContinuousStrictBefore_of_classicalSolution
#print axioms
  H1PhysicalRHSValue_aestronglyMeasurableBefore_of_classicalSolution
#print axioms
  H1PhysicalRHSAbsProductsMeasBefore_of_classicalSolution
#print axioms
  H1PhysicalRHSSpatialSquareIntegrableBefore_of_classicalSolution
#print axioms
  H1PhysicalRHSStrictInitialRouteBefore_of_classical_youngScalarZero
#print axioms
  H1PhysicalRHSStrictInitialRouteBefore_of_classical_componentSquareZero

end ShenWork.Paper2.IntervalChiNegH1PhysicalClassicalContinuity
