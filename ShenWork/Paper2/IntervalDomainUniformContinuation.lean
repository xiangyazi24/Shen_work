/-
  F1: Interior slice PID + uniform continuation reduction.

  * classicalSolution_slice_positiveInitialDatum — interior slice is PID
  * Theorem_1_1_of_hlocal_and_quantitativeLocal — reduces Paper 2
    Theorem 1.1 to hlocal + QuantitativeLocalExistence (the Picard
    contraction with uniform δ(M))

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainTheorem11Umbrella
import ShenWork.Paper2.IntervalDomainL2StaticVDifference

open ShenWork.IntervalDomain
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.UniformContinuation

/-- **Interior slice of a classical solution satisfies PID.** -/
theorem classicalSolution_slice_positiveInitialDatum
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T) :
    PositiveInitialDatum intervalDomain (u τ) := by
  have hC2 := (hsol.regularity.2.2.2.2.1 τ hτ).1
  have hcontOn : ContinuousOn (intervalDomainLift (u τ)) (Set.Icc (0:ℝ) 1) :=
    hC2.1.continuousOn
  have hcont : Continuous (u τ) := by
    have hcomp := hcontOn.comp_continuous continuous_subtype_val (fun x => x.2)
    exact hcomp.congr (fun x => by
      simp only [Function.comp, intervalDomainLift, x.2, dif_pos, Subtype.coe_eta])
  have hbdd := classicalSolution_u_range_bddAbove hsol hτ
  exact ⟨⟨hbdd, hcont⟩, fun x _hx => hsol.u_pos' hτ.1 hτ.2⟩

/-- **Interior slice of a classical solution satisfies PPID (strong datum).**

The closed-domain positivity of `IsPaper2ClassicalSolution` gives
`∀ x : intervalDomainPoint, 0 < u τ x`; compactness of `intervalDomainPoint`
and continuity of `u τ` then produce the uniform positive floor
`∃ η > 0, ∀ x, η ≤ u τ x` via `isCompact_Icc.exists_isMinOn`.

This is strictly stronger than `classicalSolution_slice_positiveInitialDatum`
and is the key theorem enabling a STRONG (floor-carrying) restart factory
for the continuation mechanism. -/
theorem classicalSolution_slice_paperPositiveInitialDatum
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T) :
    PaperPositiveInitialDatum intervalDomain (u τ) := by
  have hweak := classicalSolution_slice_positiveInitialDatum hsol hτ
  refine ⟨hweak.1, ?_⟩
  have hcont : Continuous (u τ) := hweak.1.2
  have hpos : ∀ x : intervalDomainPoint, 0 < u τ x := fun x => hsol.u_pos' hτ.1 hτ.2
  haveI : CompactSpace intervalDomainPoint :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  have hne : (Set.univ : Set intervalDomainPoint).Nonempty :=
    ⟨⟨0, le_rfl, zero_le_one⟩, Set.mem_univ _⟩
  obtain ⟨x₀, _, hx₀min⟩ :=
    isCompact_univ.exists_isMinOn hne hcont.continuousOn
  exact ⟨u τ x₀, hpos x₀, fun x => hx₀min (Set.mem_univ x)⟩

/-- **Paper 2 Theorem 1.1 from hlocal + hUniform.**

The leanest entry point for unconditional Paper 2 Theorem 1.1
(γ ≥ 1 negative-sensitivity regime). Takes just two textbook PDE inputs:

* `hlocal` — local existence for every PID u₀
* `hUniform` — uniform continuation: ∀ M>0, ∃ δ>0, any solution with
  |u₀|≤M extends by δ

`hUniform` is `IntervalDomainUniformLocalExistence p`, the genuine F1
frontier. It is constructible from the quantitative Picard contraction
(explicit δ(M) ~ 1/(Lip(M)²)) but requires extracting the M-dependence
from the contraction rate, which is the remaining formalization work. -/
theorem paper2_theorem_1_1_of_hlocal_and_hUniform
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hlocal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
    (hUniform : IntervalDomainUniformLocalExistence p)
    (hMildLocal :
      IntervalDomainGradientMildHalfStepLogisticSourceFrontierCoreLocalData p) :
    Theorem_1_1 intervalDomain p :=
  Theorem_1_1_intervalDomain_via_regime_gammaGeOne_no_hextend_mge
    p hχ ha hb hγ_ge_one
    (localExistence_of_gradientMildHalfStepLogisticSourceFrontierCoreLocalData
      p hMildLocal)
    hUniform

end ShenWork.Paper2.UniformContinuation
