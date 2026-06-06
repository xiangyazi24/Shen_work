/-
  Phase C (MinPersistence): the `hSupNorm` input from the regime sup bound.

  Wires the proved interior sup bound `interiorSupNorm_le_regimeBound`
  (Lemma 3.1) into the `hSupNorm : ∀ s ∈ [t₁/2,T), ∀ y, |lift(u s) y| ≤ M'`
  shape consumed by `solution_persist_of_supNorm`, with `M' := regimeBound p M`.
  The only new content is extending the per-point interior bound to the
  zero-extension lift (trivial off `[0,1]`).

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainSupNormBridge

open ShenWork.IntervalDomain ShenWork.Paper2 Set

noncomputable section

namespace ShenWork.MinPersistenceAtoms

/-- The zero-extension lift inherits any pointwise spatial bound. -/
theorem lift_abs_le_of_slice_bound
    {f : intervalDomainPoint → ℝ} {M' : ℝ} (hM' : 0 ≤ M')
    (hb : ∀ x : intervalDomainPoint, |f x| ≤ M') (y : ℝ) :
    |intervalDomainLift f y| ≤ M' := by
  rw [intervalDomainLift]
  split_ifs with hy
  · exact hb ⟨y, hy⟩
  · rw [abs_zero]; exact hM'

/-- **`hSupNorm` from the regime sup bound (Lemma 3.1).** -/
theorem hSupNorm_of_regime
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {M : ℝ} (hM : 0 < M) (hbound : ∀ x : intervalDomainPoint, |u₀ x| ≤ M)
    {T t₁ : ℝ} (ht₁ : 0 < t₁) (hT : 0 < T)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (htrace : InitialTrace intervalDomain u₀ u) :
    ∀ s ∈ Set.Ico (t₁/2) T, ∀ y,
      |intervalDomainLift (u s) y| ≤ SupNormBridge.regimeBound p M := by
  intro s hs y
  have hs0 : 0 < s := lt_of_lt_of_le (by linarith) hs.1
  have hM' : 0 ≤ SupNormBridge.regimeBound p M :=
    (SupNormBridge.regimeBound_pos p hM).le
  exact lift_abs_le_of_slice_bound hM'
    (fun x => SupNormBridge.interiorSupNorm_le_regimeBound p hχ ha hb hu₀ hM
      hbound hT hsol htrace s hs0 hs.2 x) y

end ShenWork.MinPersistenceAtoms
