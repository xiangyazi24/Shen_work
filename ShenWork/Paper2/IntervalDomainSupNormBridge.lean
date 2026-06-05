/-
  Sup-norm bridge: discharge hSupNorm from Lemma 3.1 for
  M' = max(M, (a/b)^{1/α}).

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainL2UEnergyUniform

open ShenWork.IntervalDomain
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.SupNormBridge

/-- The regime bound: `max(M, (a/b)^{1/α})`. -/
def regimeBound (p : CM2Params) (M : ℝ) : ℝ :=
  max M ((p.a / p.b) ^ (1 / p.α))

theorem regimeBound_pos (p : CM2Params) {M : ℝ} (hM : 0 < M) :
    0 < regimeBound p M :=
  lt_max_of_lt_left hM

theorem regimeBound_ge_M (p : CM2Params) (M : ℝ) :
    M ≤ regimeBound p M :=
  le_max_left M _

/-- **Interior sup-norm bound from Lemma 3.1 for the regime bound M'.**
If |u₀ x| ≤ M, then at interior times `|u t x| ≤ M'` where
`M' = max(M, (a/b)^{1/α})`. This is provable because Lemma 3.1 gives
`u t x ≤ max(supNorm(u₀), (a/b)^{1/α}) ≤ M'`.

This discharges the `hSupNorm` hypothesis of the end-to-end theorem
at `M' = regimeBound p M` (NOT at M itself, since the solution may
grow from M to (a/b)^{1/α} via logistic reaction). -/
theorem interiorSupNorm_le_regimeBound
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {M : ℝ} (hM : 0 < M)
    (hbound : ∀ x : intervalDomainPoint, |u₀ x| ≤ M)
    {T : ℝ} (hT : 0 < T)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (htrace : InitialTrace intervalDomain u₀ u) :
    ∀ t, 0 < t → t < T →
      ∀ x : intervalDomainPoint,
        |u t x| ≤ regimeBound p M := by
  intro t ht htT x
  have hbddu₀ := hu₀.admissible.1
  have hub := uniform_lift_upper_bound_of_regime p hχ ha hb hu₀ hbddu₀ hT hsol htrace
    t ht htT x.1 x.2
  have hpos_ut : 0 < u t x := by
    have := hub.1
    simp only [intervalDomainLift, show x.1 ∈ Set.Icc (0:ℝ) 1 from x.2, dif_pos,
      Subtype.coe_eta] at this
    exact this
  rw [abs_of_pos hpos_ut]
  have hle : u t x ≤ max (intervalDomainSupNorm u₀) ((p.a / p.b) ^ (1 / p.α)) := by
    have := hub.2
    simp only [intervalDomainLift, show x.1 ∈ Set.Icc (0:ℝ) 1 from x.2, dif_pos,
      Subtype.coe_eta] at this
    exact this
  have hsup_le : intervalDomainSupNorm u₀ ≤ M := by
    unfold intervalDomainSupNorm
    apply csSup_le
    · exact ⟨|u₀ ⟨0, by constructor <;> norm_num⟩|, ⟨⟨0, by constructor <;> norm_num⟩, rfl⟩⟩
    · rintro _ ⟨z, rfl⟩; exact hbound z
  exact le_trans hle (max_le_max_right _ hsup_le)

end ShenWork.Paper2.SupNormBridge
