import ShenWork.Paper3.IntervalDomainTheorem21Part1
import ShenWork.PDE.IntervalDomainExistence
import ShenWork.PDE.UnitPointDecayODE

/-!
# The omitted pure-decay branch in Paper 3, Theorem 2.1(1)

The printed theorem assumes only `m ≥ 1`, while its proof treats the two
regimes `a = b = 0` and `a,b > 0`.  The omitted regime `a = 0 < b` is not a
harmless gap: a spatially constant pure-decay orbit is a bounded positive
global solution whose spatial lower envelope converges to zero.
-/

open Filter Topology Set
open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.Paper2

namespace ShenWork.Paper3

noncomputable section

/-- Paper-faithful correction of Theorem 2.1(1), restricted to the two
parameter regimes actually covered by Section 4.1 of the paper. -/
def Theorem_2_1_part1_corrected
    (D : BoundedDomainData) (p : CM2Params) : Prop :=
  ((p.a = 0 ∧ p.b = 0) ∨ (0 < p.a ∧ 0 < p.b)) →
    1 ≤ p.m →
      ∀ u v : ℝ → D.Point → ℝ,
        PositiveGlobalBoundedSolution D p u v →
          ∃ δu > 0, δu ≤ liminfInfValue D u ∧
            p.ν / p.μ * (liminfInfValue D u) ^ p.γ ≤
              liminfInfValue D v

/-- Concrete pure-decay parameters: the PDE reduces on spatially constant
profiles to `u' = -u²`, with `v = u`. -/
def theorem21Part1DecayParams : CM2Params where
  N := 1
  hN := by norm_num
  α := 1
  hα := by norm_num
  γ := 1
  hγ := by norm_num
  m := 1
  hm := by norm_num
  μ := 1
  hμ := by norm_num
  ν := 1
  hν := by norm_num
  χ₀ := 0
  a := 0
  ha := by norm_num
  b := 1
  hb := by norm_num
  β := 1
  hβ := by norm_num

private def decayProfile (t : ℝ) : ℝ :=
  bernoulliDecaySolution theorem21Part1DecayParams 1 t

private def decayOrbitU : ℝ → intervalDomainPoint → ℝ :=
  fun t _ => decayProfile t

private def decayOrbitV : ℝ → intervalDomainPoint → ℝ :=
  fun t _ => decayProfile t

private theorem decayProfile_pos (t : ℝ) : 0 < decayProfile t := by
  exact bernoulliDecaySolution_pos theorem21Part1DecayParams
    (by norm_num [theorem21Part1DecayParams]) one_pos

private theorem decayProfile_differentiable :
    Differentiable ℝ decayProfile := by
  exact bernoulliDecaySolution_differentiable theorem21Part1DecayParams
    (by norm_num [theorem21Part1DecayParams]) one_pos

private theorem decayProfile_deriv_eq (t : ℝ) (ht : 0 < t) :
    deriv decayProfile t =
      decayProfile t *
        (-(theorem21Part1DecayParams.b *
          (decayProfile t) ^ theorem21Part1DecayParams.α)) := by
  exact (bernoulliDecaySolution_hasDerivAt_of_pos_time
    theorem21Part1DecayParams
    (by norm_num [theorem21Part1DecayParams]) one_pos ht).deriv

private theorem decayProfile_deriv_nonpos (t : ℝ) (ht : 0 < t) :
    deriv decayProfile t ≤ 0 := by
  rw [decayProfile_deriv_eq t ht]
  exact mul_nonpos_of_nonneg_of_nonpos (decayProfile_pos t).le
    (neg_nonpos.mpr (mul_nonneg theorem21Part1DecayParams.hb
      (Real.rpow_nonneg (decayProfile_pos t).le _)))

private theorem decayProfile_deriv_continuousOn {T : ℝ} :
    ContinuousOn (deriv decayProfile) (Ioo (0 : ℝ) T) := by
  have hpow : Continuous
      (fun t : ℝ =>
        (decayProfile t) ^ theorem21Part1DecayParams.α) :=
    decayProfile_differentiable.continuous.rpow_const
      (fun t => Or.inl (ne_of_gt (decayProfile_pos t)))
  have hfield : Continuous
      (fun t : ℝ =>
        decayProfile t *
          (-(theorem21Part1DecayParams.b *
            (decayProfile t) ^ theorem21Part1DecayParams.α))) :=
    decayProfile_differentiable.continuous.mul
      (continuous_const.mul hpow).neg
  refine hfield.continuousOn.congr ?_
  intro t ht
  exact decayProfile_deriv_eq t ht.1

private theorem spatiallyConstant_jointDeriv_continuousOn
    {T : ℝ} {S : Set ℝ}
    (hS : S ⊆ Icc (0 : ℝ) 1) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) =>
          deriv (fun s : ℝ =>
            intervalDomainLift (decayOrbitV s) x) t))
      (Ioo (0 : ℝ) T ×ˢ S) := by
  have heq : Set.EqOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) =>
          deriv (fun s : ℝ =>
            intervalDomainLift (decayOrbitV s) x) t))
      (fun q : ℝ × ℝ => deriv decayProfile q.1)
      (Ioo (0 : ℝ) T ×ˢ S) := by
    rintro ⟨t, x⟩ ⟨_ht, hx⟩
    have hxIcc : x ∈ Icc (0 : ℝ) 1 := hS hx
    have hslice :
        (fun s : ℝ => intervalDomainLift (decayOrbitV s) x) =
          decayProfile := by
      funext s
      simp [decayOrbitV, intervalDomainLift, hxIcc]
    simp only [Function.uncurry]
    rw [hslice]
  refine ContinuousOn.congr ?_ heq
  exact decayProfile_deriv_continuousOn.comp continuousOn_fst
    (fun q hq => hq.1)

private theorem spatiallyConstant_field_continuousOn {T : ℝ} :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) =>
          intervalDomainLift (decayOrbitV t) x))
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) := by
  have heq : Set.EqOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) =>
          intervalDomainLift (decayOrbitV t) x))
      (fun q : ℝ × ℝ => decayProfile q.1)
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) := by
    rintro ⟨t, x⟩ ⟨_ht, hx⟩
    simp only [Function.uncurry]
    rw [intervalDomainLift, dif_pos hx]
    rfl
  refine ContinuousOn.congr ?_ heq
  exact decayProfile_differentiable.continuous.continuousOn.comp
    continuousOn_fst (fun q hq => hq.1)

private theorem decayOrbit_regular (T : ℝ) (hT : 0 < T) :
    intervalDomainClassicalRegularity T decayOrbitU decayOrbitV := by
  apply classicalRegularity_of_spatially_constant_decreasing hT
    decayProfile_pos
    decayProfile_differentiable.continuous.continuousOn
    decayProfile_differentiable.differentiableOn
    (fun t ht => decayProfile_deriv_nonpos t ht.1)
    decayProfile_deriv_continuousOn
  · intro t _ht
    exact intervalDomainLift_const_contDiffOn (decayProfile t)
  · intro x t _ht
    exact decayProfile_differentiable.differentiableAt
  · intro x
    simpa [decayOrbitV] using
      (decayProfile_deriv_continuousOn (T := T))
  · exact spatiallyConstant_jointDeriv_continuousOn Ioo_subset_Icc_self
  · intro t _ht
    exact intervalDomainLift_const_neumann (decayProfile t)
  · intro t _ht
    exact ⟨intervalDomainLift_const_contDiffOn_Icc (decayProfile t),
      (intervalDomainLift_const_deriv_endpoint_zero (decayProfile t)).1,
      (intervalDomainLift_const_deriv_endpoint_zero (decayProfile t)).2⟩
  · exact spatiallyConstant_jointDeriv_continuousOn (fun _ hx => hx)
  · exact spatiallyConstant_field_continuousOn

private theorem decayOrbit_classical (T : ℝ) (hT : 0 < T) :
    IsPaper2ClassicalSolution intervalDomain theorem21Part1DecayParams T
      decayOrbitU decayOrbitV := by
  refine ⟨hT, decayOrbit_regular T hT, ?_, ?_, ?_, ?_, ?_⟩
  · intro t x ht _htT
    exact decayProfile_pos t
  · intro t x ht _htT
    exact (decayProfile_pos t).le
  · intro t x ht htT hx
    change deriv decayProfile t =
      intervalDomainLaplacian (fun _ => decayProfile t) x -
        theorem21Part1DecayParams.χ₀ *
          intervalDomainChemotaxisDiv theorem21Part1DecayParams
            (fun _ => decayProfile t) (fun _ => decayProfile t) x +
        decayProfile t *
          (theorem21Part1DecayParams.a -
            theorem21Part1DecayParams.b *
              (decayProfile t) ^ theorem21Part1DecayParams.α)
    rw [intervalDomainLaplacian_const_zero (decayProfile t) hx,
      intervalDomainChemotaxisDiv_const_zero theorem21Part1DecayParams
        (decayProfile t) (decayProfile t) hx,
      decayProfile_deriv_eq t ht]
    norm_num [theorem21Part1DecayParams]
  · intro t x ht htT hx
    change (0 : ℝ) =
      intervalDomainLaplacian (fun _ => decayProfile t) x -
        theorem21Part1DecayParams.μ * decayProfile t +
        theorem21Part1DecayParams.ν *
          (decayProfile t) ^ theorem21Part1DecayParams.γ
    rw [intervalDomainLaplacian_const_zero (decayProfile t) hx]
    norm_num [theorem21Part1DecayParams, Real.rpow_one]
  · intro t x ht htT hx
    exact ⟨intervalDomainNormalDeriv_const_zero (decayProfile t) hx,
      intervalDomainNormalDeriv_const_zero (decayProfile t) hx⟩

private theorem decayOrbit_global :
    IsPaper2GlobalClassicalSolution intervalDomain theorem21Part1DecayParams
      decayOrbitU decayOrbitV := by
  intro T hT
  exact decayOrbit_classical T hT

private theorem decayProfile_tendsto_zero :
    Tendsto decayProfile atTop (nhds 0) := by
  have hden : Tendsto (fun t : ℝ => 1 + t) atTop atTop :=
    by
      simpa [add_comm] using
        (tendsto_id.atTop_add
          (tendsto_const_nhds (x := (1 : ℝ))))
  have hinv : Tendsto (fun t : ℝ => (1 + t)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hden
  refine hinv.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  simp [decayProfile, bernoulliDecaySolution_of_nonneg, bernoulliDecayForward,
    bernoulliDecayDenominator, theorem21Part1DecayParams, ht,
    Real.rpow_one, Real.rpow_neg_one]

private theorem decayOrbit_bounded : IsPaper2Bounded intervalDomain decayOrbitU := by
  refine ⟨1, ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  change intervalDomainSupNorm (fun _ : intervalDomainPoint => decayProfile t) ≤ 1
  rw [intervalDomainSupNorm_const, abs_of_pos (decayProfile_pos t)]
  exact bernoulliDecaySolution_le_of_nonneg_time theorem21Part1DecayParams
    (by norm_num [theorem21Part1DecayParams]) one_pos ht

private theorem decayOrbit_positiveGlobalBounded :
    PositiveGlobalBoundedSolution intervalDomain theorem21Part1DecayParams
      decayOrbitU decayOrbitV :=
  PositiveGlobalBoundedSolution.of_global_bounded
    decayOrbit_global decayOrbit_bounded

private theorem decayOrbit_liminfInfValue_zero :
    liminfInfValue intervalDomain decayOrbitU = 0 := by
  let x0 : intervalDomainPoint :=
    ⟨0, (by constructor <;> norm_num)⟩
  letI : Nonempty intervalDomainPoint := ⟨x0⟩
  have hinf : ∀ t : ℝ,
      intervalDomain.infValue (decayOrbitU t) = decayProfile t := by
    intro t
    change sInf (Set.range (fun _ : intervalDomainPoint => decayProfile t)) =
      decayProfile t
    rw [Set.range_const]
    simp
  unfold liminfInfValue
  simpa [hinf] using decayProfile_tendsto_zero.liminf_eq

/-- The unguarded printed Part 1 is false even on the concrete physical unit
interval.  The obstruction is the omitted parameter regime `a = 0 < b`. -/
theorem not_Theorem_2_1_part1_intervalDomain_pureDecay :
    ¬ Theorem_2_1_part1 intervalDomain theorem21Part1DecayParams := by
  intro h
  rcases h (by norm_num [theorem21Part1DecayParams])
      decayOrbitU decayOrbitV decayOrbit_positiveGlobalBounded with
    ⟨δ, hδ, hδlim, _hv⟩
  rw [decayOrbit_liminfInfValue_zero] at hδlim
  linarith

end

end ShenWork.Paper3

#print axioms ShenWork.Paper3.Theorem_2_1_part1_corrected
#print axioms
  ShenWork.Paper3.not_Theorem_2_1_part1_intervalDomain_pureDecay
