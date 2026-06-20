import ShenWork.Paper2.IntervalBFormPositiveDatumNegPartFrontier
import ShenWork.PDE.IntervalSemigroupConeAtoms

open Filter Topology Set

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceData conjugatePicardLimit)
open ShenWork.IntervalMildToClassical
  (mildChemicalConcentration)
open ShenWork.IntervalNeumannFullKernel
  (intervalFullSemigroupOperator)
open ShenWork.IntervalMildPicardThreshold
  (unitClip unitClip_continuous unitClip_of_mem)
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

/-- The B-form negative-part route's `hpde_u` field is exactly the banked
unconditional B-form interior PDE.  The `PaperPositiveInitialDatum` and spectral
inputs are carried by `BFormDirectClassical.BFormBankedInputs`; no PDE identity
is reproved here. -/
theorem bform_negpart_hpde_u_of_bank
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (B : ShenWork.Paper2.BFormDirectClassical.BFormBankedInputs p DB) :
    ∀ t x, 0 < t → t < DB.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv (conjugatePicardLimit p u₀ DB.T) t x =
        intervalDomain.laplacian
            ((conjugatePicardLimit p u₀ DB.T) t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p
              ((conjugatePicardLimit p u₀ DB.T) t)
              (mildChemicalConcentration p
                (conjugatePicardLimit p u₀ DB.T) t) x
          + (conjugatePicardLimit p u₀ DB.T) t x
            * (p.a - p.b *
              ((conjugatePicardLimit p u₀ DB.T) t x) ^ p.α) :=
  ShenWork.Paper2.BFormDirectClassical.BFormBankedInputs.hpde_u B

/-- Strict positivity of the full Neumann heat semigroup for nonnegative data
that is positive somewhere on `[0,1]`.  This exposes the kernel-positivity
route (`heatKernel_pos` inside `IntervalSemigroupConeAtoms`) in the shape needed
by the lower-barrier argument. -/
theorem intervalFullSemigroupOperator_pos_of_nonneg_nonzero
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hf_nonneg : ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f y)
    (hf_pos_somewhere : ∃ y₀ ∈ Set.Icc (0 : ℝ) 1, 0 < f y₀)
    (x : ℝ) :
    0 < intervalFullSemigroupOperator t f x := by
  rcases hf_pos_somewhere with ⟨y₀, hy₀, hy₀_pos⟩
  exact ShenWork.IntervalSemigroupConeAtoms.intervalFullSemigroupOperator_pos
    ht hf_cont hf_nonneg hy₀ hy₀_pos x

theorem positiveInitialDatum_intervalDomainLift_continuousOn
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀) :
    ContinuousOn (intervalDomainLift u₀) (Set.Icc (0 : ℝ) 1) := by
  rw [continuousOn_iff_continuous_restrict]
  have heq : (Set.Icc (0 : ℝ) 1).restrict (intervalDomainLift u₀) = u₀ := by
    funext ⟨y, hy⟩
    simp only [Set.restrict_apply, intervalDomainLift]
    split_ifs
    exact congr_arg u₀ (Subtype.ext rfl)
  rw [heq]
  exact hu₀.admissible.2

theorem positiveInitialDatum_intervalDomainLift_nonneg
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀) :
    ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ intervalDomainLift u₀ y := by
  have hcont : Continuous u₀ := hu₀.admissible.2
  set f₀ : ℝ → ℝ := fun y => u₀ (unitClip y) with hf₀_def
  have hf₀_cont : Continuous f₀ := hcont.comp unitClip_continuous
  have hf₀_pos : ∀ y ∈ Set.Ioo (0 : ℝ) 1, 0 < f₀ y := by
    intro y hy
    have hy' : y ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hy
    rw [hf₀_def]
    simp only [unitClip_of_mem hy']
    exact hu₀.pos hy
  haveI hne0 : (nhdsWithin (0 : ℝ) (Set.Ioo (0 : ℝ) 1)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp (by
      rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
      exact Set.left_mem_Icc.mpr (by norm_num))
  haveI hne1 : (nhdsWithin (1 : ℝ) (Set.Ioo (0 : ℝ) 1)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp (by
      rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
      exact Set.right_mem_Icc.mpr (by norm_num))
  have h0 : 0 ≤ f₀ 0 := by
    have htend : Filter.Tendsto f₀ (nhdsWithin 0 (Set.Ioo (0 : ℝ) 1))
        (nhds (f₀ 0)) :=
      (hf₀_cont.tendsto 0).mono_left nhdsWithin_le_nhds
    apply ge_of_tendsto htend
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hf₀_pos y hy).le
  have h1 : 0 ≤ f₀ 1 := by
    have htend : Filter.Tendsto f₀ (nhdsWithin 1 (Set.Ioo (0 : ℝ) 1))
        (nhds (f₀ 1)) :=
      (hf₀_cont.tendsto 1).mono_left nhdsWithin_le_nhds
    apply ge_of_tendsto htend
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hf₀_pos y hy).le
  intro y hy
  have hLift_eq : intervalDomainLift u₀ y = f₀ y := by
    simp only [intervalDomainLift, dif_pos hy, hf₀_def, unitClip_of_mem hy]
  rw [hLift_eq]
  rcases lt_or_eq_of_le hy.1 with h0y | h0y
  · rcases lt_or_eq_of_le hy.2 with hy1 | hy1
    · exact (hf₀_pos y ⟨h0y, hy1⟩).le
    · rw [hy1]
      exact h1
  · rw [← h0y]
    exact h0

theorem positiveInitialDatum_intervalDomainLift_pos_somewhere
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀) :
    ∃ y₀ ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift u₀ y₀ := by
  have hy₀ : ((1 : ℝ) / 2) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> norm_num
  refine ⟨(1 : ℝ) / 2, hy₀, ?_⟩
  have hins : (⟨(1 : ℝ) / 2, hy₀⟩ : intervalDomainPoint)
      ∈ intervalDomain.inside := by
    show ((1 : ℝ) / 2) ∈ Set.Ioo (0 : ℝ) 1
    constructor <;> norm_num
  simp only [intervalDomainLift, dif_pos hy₀]
  exact hu₀.pos hins

/-- Positive initial data on the interval are instantly strictly positive under
the full Neumann heat semigroup. -/
theorem intervalFullSemigroupOperator_pos_of_positiveInitialDatum
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    0 < intervalFullSemigroupOperator t (intervalDomainLift u₀) x := by
  exact intervalFullSemigroupOperator_pos_of_nonneg_nonzero ht
    (positiveInitialDatum_intervalDomainLift_continuousOn hu₀)
    (positiveInitialDatum_intervalDomainLift_nonneg hu₀)
    (positiveInitialDatum_intervalDomainLift_pos_somewhere hu₀)
    x

/-- The exponential heat lower barrier
`exp (-C t) * S_N(t) f` is strictly positive whenever `S_N(t) f` is. -/
theorem exponential_semigroup_lower_barrier_pos
    {C t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hf_nonneg : ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f y)
    (hf_pos_somewhere : ∃ y₀ ∈ Set.Icc (0 : ℝ) 1, 0 < f y₀)
    (x : ℝ) :
    0 < Real.exp (-C * t) * intervalFullSemigroupOperator t f x := by
  exact mul_pos (Real.exp_pos _)
    (intervalFullSemigroupOperator_pos_of_nonneg_nonzero
      ht hf_cont hf_nonneg hf_pos_somewhere x)

/-- If the sub-solution comparison supplies the lower barrier
`exp (-C t) S_N(t)u₀ ≤ u(t)`, then strict positivity follows immediately from
strict positivity of the Neumann heat semigroup.  This theorem deliberately
keeps the comparison inequality as an explicit hypothesis. -/
theorem bform_strictPos_of_semigroup_lower_barrier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀} {C : ℝ}
    (hLift_cont :
      ContinuousOn (intervalDomainLift u₀) (Set.Icc (0 : ℝ) 1))
    (hLift_nonneg :
      ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ intervalDomainLift u₀ y)
    (hLift_pos_somewhere :
      ∃ y₀ ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift u₀ y₀)
    (hbarrier :
      ∀ t x, 0 < t → t < DB.T →
        Real.exp (-C * t)
            * intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
          ≤ conjugatePicardLimit p u₀ DB.T t x) :
    ∀ t x, 0 < t → t < DB.T →
      0 < conjugatePicardLimit p u₀ DB.T t x := by
  intro t x ht htT
  exact lt_of_lt_of_le
    (exponential_semigroup_lower_barrier_pos
      (C := C) ht hLift_cont hLift_nonneg hLift_pos_somewhere x.1)
    (hbarrier t x ht htT)

/-- Route constructor once the separately handled negative-part estimate and
the sub-solution comparison lower barrier are both available.  The two fields
implemented here are `strictPos` and `hpde_u`; `negativePart_zero` remains an
input, as intended. -/
def bform_negpart_route_of_lower_barrier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀} {C : ℝ}
    (datum : PositiveInitialDatum intervalDomain u₀)
    (B : ShenWork.Paper2.BFormDirectClassical.BFormBankedInputs p DB)
    (hnegativePart_zero :
      ∀ t, 0 < t → t ≤ DB.T → ∀ x : intervalDomainPoint,
        negativePart (conjugatePicardLimit p u₀ DB.T t x) = 0)
    (hLift_cont :
      ContinuousOn (intervalDomainLift u₀) (Set.Icc (0 : ℝ) 1))
    (hLift_nonneg :
      ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ intervalDomainLift u₀ y)
    (hLift_pos_somewhere :
      ∃ y₀ ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift u₀ y₀)
    (hbarrier :
      ∀ t x, 0 < t → t < DB.T →
        Real.exp (-C * t)
            * intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
          ≤ conjugatePicardLimit p u₀ DB.T t x) :
    BFormNegativePartPositivityRoute p DB where
  datum := datum
  negativePart_zero := hnegativePart_zero
  strictPos :=
    bform_strictPos_of_semigroup_lower_barrier
      hLift_cont hLift_nonneg hLift_pos_somewhere hbarrier
  hpde_u := bform_negpart_hpde_u_of_bank B

end ShenWork.Paper2.BFormPositiveDatumNegPart
