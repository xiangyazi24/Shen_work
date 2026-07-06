/-
  ShenWork/Paper2/IntervalHuRestartCoeffFiniteCoverProducer.lean

  Produce the finite Hu restart-chart covers from the local time-neighborhood
  spectral agreement carried by `Hu`.
-/
import ShenWork.Paper2.IntervalHuRestartCoeffFiniteCover

open MeasureTheory Filter Topology Set
open scoped BigOperators
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)
open ShenWork.IntervalMildTimeDerivContinuity (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalPicardLimitRestartBdd (DuhamelSourceBddOn)
open ShenWork.IntervalPicardLimitBddProducer (patchedSource)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)

noncomputable section

namespace ShenWork.Paper2.ResolverSourceWindowInput

/-- One open time-neighborhood chart extracted from `Hu.exists_data`.
The chart also records a positive lower bound for the local restart time on
that neighborhood. -/
structure HuRestartLocalCoverChart
    (T : ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    (Hu : HasTimeNeighborhoodSpectralAgreement T u)
    (σ₀ : ℝ) where
  R : HuRestartData T u σ₀
  eps : ℝ
  heps : 0 < eps
  U : Set ℝ
  hU_open : IsOpen U
  hσ₀_mem : σ₀ ∈ U
  hU : ∀ σ ∈ U,
    eps ≤ σ - R.offset ∧
    Set.EqOn (intervalDomainLift (u σ))
      (fun x => ∑' n,
        localRestartCoeff R.a0 R.a (σ - R.offset) n * cosineMode n x)
      (Set.Icc (0 : ℝ) 1)

/-- At every interior time, the local restart data supplied by `Hu` extends to
an open chart with a positive restart-time margin. -/
theorem huRestartLocalCoverChart_exists
    {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (Hu : HasTimeNeighborhoodSpectralAgreement T u)
    {σ₀ : ℝ} (hσ₀ : 0 < σ₀ ∧ σ₀ < T) :
    ∃ _C : HuRestartLocalCoverChart T u Hu σ₀, True := by
  classical
  let R := huRestartData Hu σ₀ hσ₀
  let eps : ℝ := (σ₀ - R.offset) / 2
  have heps : 0 < eps := by
    dsimp [eps]
    linarith [R.hτ]
  have hoff_eps_lt : R.offset + eps < σ₀ := by
    dsimp [eps]
    linarith [R.hτ]
  have hmargin_event :
      ∀ᶠ σ in 𝓝 σ₀, eps ≤ σ - R.offset := by
    refine Filter.eventually_of_mem (Ioi_mem_nhds hoff_eps_lt) ?_
    intro σ hσ
    exact le_sub_iff_add_le'.2 (le_of_lt hσ)
  have hboth :
      ∀ᶠ σ in 𝓝 σ₀,
        (∀ x : intervalDomainPoint,
          u σ x =
            ∑' n, localRestartCoeff R.a0 R.a (σ - R.offset) n *
              cosineMode n x.1) ∧ eps ≤ σ - R.offset :=
    R.hagree_nhd.and hmargin_event
  obtain ⟨U, hU_prop, hU_open, hU_mem⟩ := eventually_nhds_iff.1 hboth
  refine ⟨?_, trivial⟩
  refine
    { R := R
      eps := eps
      heps := heps
      U := U
      hU_open := hU_open
      hσ₀_mem := hU_mem
      hU := ?_ }
  intro σ hσU
  obtain ⟨hagree_point, hmargin⟩ := hU_prop σ hσU
  refine ⟨hmargin, ?_⟩
  intro x hx
  calc
    intervalDomainLift (u σ) x = u σ ⟨x, hx⟩ := by
      simp [intervalDomainLift, hx]
    _ = ∑' n, localRestartCoeff R.a0 R.a (σ - R.offset) n *
          cosineMode n x := by
      simpa using hagree_point ⟨x, hx⟩

/-- Choose the local cover chart supplied by `Hu` at one interior time. -/
noncomputable def huRestartLocalCoverChart
    {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (Hu : HasTimeNeighborhoodSpectralAgreement T u)
    (σ₀ : ℝ) (hσ₀ : 0 < σ₀ ∧ σ₀ < T) :
    HuRestartLocalCoverChart T u Hu σ₀ :=
  Classical.choose (huRestartLocalCoverChart_exists Hu hσ₀)

/-- The local `Hu` restart charts have a finite subcover on every compact
interior time window. -/
noncomputable def huRestartFiniteCover_of_timeNeighborhood
    {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (Hu : HasTimeNeighborhoodSpectralAgreement T u)
    {a b : ℝ} (ha : 0 < a) (hb : b < T) (_hab : a ≤ b) :
    Σ (ι : Type), Σ (_ : Fintype ι), HuRestartFiniteCover T u Hu a b ι := by
  classical
  let K : Set ℝ := Set.Icc a b
  let κ : Type := {σ : ℝ // σ ∈ K}
  have hκ_int : ∀ c : κ, 0 < (c : ℝ) ∧ (c : ℝ) < T := by
    intro c
    have hc : (c : ℝ) ∈ Set.Icc a b := c.property
    exact ⟨lt_of_lt_of_le ha hc.1, lt_of_le_of_lt hc.2 hb⟩
  let C : (c : κ) → HuRestartLocalCoverChart T u Hu (c : ℝ) :=
    fun c => huRestartLocalCoverChart Hu (c : ℝ) (hκ_int c)
  let U : κ → Set ℝ := fun c => (C c).U
  have hU_open : ∀ c : κ, IsOpen (U c) := fun c => (C c).hU_open
  have hK_cover : K ⊆ ⋃ c : κ, U c := by
    intro σ hσ
    exact Set.mem_iUnion.2 ⟨⟨σ, hσ⟩, (C ⟨σ, hσ⟩).hσ₀_mem⟩
  let subcover := isCompact_Icc.elim_finite_subcover U hU_open hK_cover
  let t : Finset κ := Classical.choose subcover
  have htcover : K ⊆ ⋃ i ∈ t, U i := Classical.choose_spec subcover
  let ι : Type := {c : κ // c ∈ t}
  haveI : Fintype ι := by
    infer_instance
  refine ⟨ι, inferInstance, ?_⟩
  refine
    { M := fun i => (C i.1).R.M
      hM := fun i => (C i.1).R.hM
      a0 := fun i => (C i.1).R.a0
      ha0 := fun i => (C i.1).R.ha0
      coeff := fun i => (C i.1).R.a
      src := fun i => (C i.1).R.src
      offset := fun i => (C i.1).R.offset
      eps := fun i => (C i.1).eps
      heps := fun i => (C i.1).heps
      exists_chart := ?_ }
  intro σ hσ
  have hσK : σ ∈ K := hσ
  have hmem := htcover hσK
  rw [Set.mem_iUnion] at hmem
  obtain ⟨c, hc_mem⟩ := hmem
  rw [Set.mem_iUnion] at hc_mem
  obtain ⟨hc_t, hσU⟩ := hc_mem
  let i : ι := ⟨c, hc_t⟩
  exact ⟨i, (C c).hU σ hσU⟩

/-- The compact Hu coefficient envelope is already a consequence of the local
time-neighborhood spectral agreement. -/
theorem huRestartCoeff_henv_of_timeNeighborhood
    {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (Hu : HasTimeNeighborhoodSpectralAgreement T u)
    {a b : ℝ} (ha : 0 < a) (hb : b < T) (hab : a ≤ b) :
    ∃ E : ℕ → ℝ,
      Summable E ∧
      (∀ n, 0 ≤ E n) ∧
      (∀ σ ∈ Set.Icc a b, ∀ n,
        unitIntervalCosineEigenvalue n * |huRestartCoeff Hu σ n| ≤ E n) := by
  obtain ⟨ι, hι, C⟩ := huRestartFiniteCover_of_timeNeighborhood Hu ha hb hab
  letI : Fintype ι := hι
  exact huRestartCoeff_henv_of_finiteCover Hu ha hb C

/-- Hu-coefficient inputs after deleting the redundant compact-envelope field.
Only the power-source K1 fields remain explicit. -/
structure ResolverSourceWindowHuNoEnvelopeInputs
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u) where
  adotPow : ℝ → ℕ → ℝ
  hderivPow : ∀ σ, 0 < σ → σ < D.T → ∀ n,
    HasDerivAt
      (fun r => ShenWork.IntervalNeumannFullKernel.cosineCoeffs
        (fun x => p.ν * intervalDomainLift (D.u r) x ^ p.γ) n)
      (adotPow σ n) σ
  hadotPowCont : ∀ n, ContinuousOn (fun σ => adotPow σ n) (Set.Ioo 0 D.T)
  hMdotPow : ∀ a b, 0 < a → b < D.T →
    ∃ Mdot, ∀ σ ∈ Set.Icc a b, ∀ n, |adotPow σ n| ≤ Mdot

/-- Fill the existing HuCoeff surface: the compact envelope is produced from
`Hu`, while K1 data is carried by the no-envelope package. -/
def resolverSourceWindowHuCoeffInputs_of_noEnvelopeInputs
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    {Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u}
    (H : ResolverSourceWindowHuNoEnvelopeInputs p D Hu) :
    ResolverSourceWindowHuCoeffInputs p D Hu where
  henv := fun a b ha hb hab =>
    huRestartCoeff_henv_of_timeNeighborhood Hu (a := a) (b := b) ha hb hab
  adotPow := H.adotPow
  hderivPow := H.hderivPow
  hadotPowCont := H.hadotPowCont
  hMdotPow := H.hMdotPow

/-- Chi-zero no-K1 Hu inputs after deleting the redundant compact-envelope
field.  The bounded patched-source package remains the K1 producer input. -/
structure ResolverSourceWindowHuNoEnvelopeNoK1Inputs
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u) where
  hsrc0 : DuhamelSourceBddOn (patchedSource p u₀ D.u) D.T

/-- Fill the existing chi-zero HuCoeff/no-K1 surface by producing the compact
Hu envelope from the time-neighborhood agreement. -/
def resolverSourceWindowHuCoeffNoK1Inputs_of_noEnvelopeNoK1Inputs
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    {Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u}
    (H : ResolverSourceWindowHuNoEnvelopeNoK1Inputs p D Hu) :
    ResolverSourceWindowHuCoeffNoK1Inputs p D Hu where
  henv := fun a b ha hb hab =>
    huRestartCoeff_henv_of_timeNeighborhood Hu (a := a) (b := b) ha hb hab
  hsrc0 := H.hsrc0

#print axioms huRestartFiniteCover_of_timeNeighborhood
#print axioms huRestartCoeff_henv_of_timeNeighborhood

end ShenWork.Paper2.ResolverSourceWindowInput
