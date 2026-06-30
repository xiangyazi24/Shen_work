import ShenWork.Paper2.IntervalDomainTheorem11
import ShenWork.PDE.IntervalDomain

/-!
# Interval Agmon interpolation audit

This file replaces an unfinished proof skeleton that tried to prove a uniform
one-dimensional Agmon interpolation estimate from assumptions that were too
weak:

* a fundamental-theorem-of-calculus bound needs absolute continuity or an
  equivalent derivative-integrability hypothesis, not just
  `ContinuousOn` plus `DifferentiableOn` on the open interval;
* the raw `L¹ ≤ L²` step needs square-integrability;
* a per-slice constant depending on `f` is not enough to produce
  `LpMassGradientInterpolationEstimate`, whose `Ceps` must be uniform in
  `t ∈ (0,T)`.

The first theorem below records the only elementary fact available at the
old interface: for a single slice whose mass is positive, the present
inequality is satisfiable by choosing a large constant depending on that
slice.  This is honest but intentionally not exported as the paper-level
interpolation frontier.

The paper-level consumer needs the second, uniform interface:
`UnitIntervalPositiveAgmonInterpolation`, where `Ceps` is chosen from `q`
and `eps` before the solution slice is supplied.  The final theorem wires
that uniform frontier into `IntervalDomainClassicalSolutionPositiveInterpolation`.
-/

open MeasureTheory Set
open ShenWork.IntervalDomain
open ShenWork.Paper2

noncomputable section

namespace ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation

/-- A single-slice mass-gradient interpolation inequality with a constant
allowed to depend on the slice.

This is not the uniform Agmon/Gagliardo-Nirenberg estimate used by the Moser
iteration.  It is a sanity lemma for the current algebraic inequality shape:
if the mass term is positive, a sufficiently large positive coefficient on
that mass term dominates the left side, regardless of the sign of the gradient
integral as represented by the abstract interval integral. -/
theorem intervalDomain_agmon_interpolation_slice
    {f : intervalDomain.Point → ℝ} {q eps : ℝ}
    (hmass : 0 < intervalDomain.integral f) :
    ∃ Ceps > 0,
      intervalDomain.integral (fun x => f x ^ q) ≤
        eps * intervalDomain.integral
          (fun x => f x ^ (q - 2) * (intervalDomain.gradNorm f x) ^ 2) +
        Ceps * (intervalDomain.integral f) ^ q := by
  set A : ℝ := intervalDomain.integral (fun x => f x ^ q)
  set G : ℝ := intervalDomain.integral
    (fun x => f x ^ (q - 2) * (intervalDomain.gradNorm f x) ^ 2)
  set B : ℝ := (intervalDomain.integral f) ^ q with hB_def
  have hBpos : 0 < B := by
    rw [hB_def]
    exact Real.rpow_pos_of_pos hmass q
  refine ⟨(|A| + |eps * G| + 1) / B, ?_, ?_⟩
  · exact div_pos (by positivity) hBpos
  · have hBne : B ≠ 0 := ne_of_gt hBpos
    have hmul :
        ((|A| + |eps * G| + 1) / B) * B =
          |A| + |eps * G| + 1 := by
      field_simp [hBne]
    have hA_le : A ≤ |A| := le_abs_self A
    have hEG_nonneg : 0 ≤ eps * G + |eps * G| := by
      rcases le_total 0 (eps * G) with hnonneg | hnonpos
      · have habs : |eps * G| = eps * G := abs_of_nonneg hnonneg
        rw [habs]
        nlinarith
      · have habs : |eps * G| = -(eps * G) := abs_of_nonpos hnonpos
        rw [habs]
        ring_nf
        norm_num
    calc
      A ≤ eps * G + (|A| + |eps * G| + 1) := by nlinarith
      _ = eps * G + ((|A| + |eps * G| + 1) / B) * B := by rw [hmul]
      _ = eps * G + ((|A| + |eps * G| + 1) / B) *
          (intervalDomain.integral f) ^ q := by rw [hB_def]

/-- Uniform positive one-dimensional Agmon/Gagliardo-Nirenberg frontier on
the unit interval.

The constant is chosen from `q` and `eps` before the particular positive
slice `f` is supplied.  This is the quantifier order needed by classical
solution slices, whose `LpMassGradientInterpolationEstimate` must use one
constant for all `t ∈ (0,T)`. -/
def UnitIntervalPositiveAgmonInterpolation : Prop :=
  ∀ q : ℝ, 1 < q →
  ∀ eps : ℝ, 0 < eps →
    ∃ Ceps > 0,
      ∀ f : intervalDomain.Point → ℝ,
        (∀ x, 0 < f x) →
        ContinuousOn (intervalDomainLift f) (Set.Icc (0 : ℝ) 1) →
        DifferentiableOn ℝ (intervalDomainLift f) (Set.Ioo (0 : ℝ) 1) →
          intervalDomain.integral (fun x => f x ^ q) ≤
            eps * intervalDomain.integral
              (fun x => f x ^ (q - 2) *
                (intervalDomain.gradNorm f x) ^ 2) +
            Ceps * (intervalDomain.integral f) ^ q

/-- Produce the classical-solution positive interpolation frontier from a
uniform unit-interval Agmon/Gagliardo-Nirenberg frontier. -/
theorem intervalDomain_classicalSolutionPositiveInterpolation_of_uniform_agmon
    {params : CM2Params}
    (hagmon : UnitIntervalPositiveAgmonInterpolation) :
    IntervalDomainTheorem11Composite.IntervalDomainClassicalSolutionPositiveInterpolation
      params := by
  intro T u v hsol eps heps q hq
  rcases hagmon q hq eps heps with ⟨Ceps, hCeps_pos, hCeps⟩
  refine ⟨Ceps, hCeps_pos, ?_⟩
  intro t ht0 htT
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hf_pos : ∀ x : intervalDomain.Point, 0 < u t x :=
    fun x => hsol.u_pos' ht0 htT
  have hC2_closed :
      ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 t ht).1.1
  have hf_cont : ContinuousOn (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
    hC2_closed.continuousOn
  have hC2_open :
      ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Ioo (0 : ℝ) 1) :=
    (hsol.regularity.1 t ht).1
  have hf_diff : DifferentiableOn ℝ (intervalDomainLift (u t)) (Set.Ioo (0 : ℝ) 1) :=
    hC2_open.differentiableOn (by norm_num)
  exact hCeps (u t) hf_pos hf_cont hf_diff

#print axioms intervalDomain_agmon_interpolation_slice
#print axioms intervalDomain_classicalSolutionPositiveInterpolation_of_uniform_agmon

end ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation

end
