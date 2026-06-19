import ShenWork.Paper1.WaveG1Bridge
import ShenWork.PaperOne.LocalUniformCompactness

open Filter Topology Set
namespace ShenWork.Paper1
noncomputable section

def InConstantBarrierTrap (M : ℝ) (u : ℝ → ℝ) : Prop :=
  IsCUnifBdd u ∧ ∀ x, 0 ≤ u x ∧ u x ≤ M

theorem locallyUniformConverges_of_tendstoLocallyUniformly
    {u : ℕ → ℝ → ℝ} {f : C(ℝ, ℝ)}
    (h : TendstoLocallyUniformly u f atTop) :
    LocallyUniformConverges u f := by
  intro R _hR ε hε
  have hOn :
      TendstoLocallyUniformlyOn u (fun x : ℝ => f x) atTop
        (Icc (-R) R) :=
    h.tendstoLocallyUniformlyOn
  have hUnif :
      TendstoUniformlyOn u (fun x : ℝ => f x) atTop (Icc (-R) R) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      (isCompact_Icc : IsCompact (Icc (-R) R))).mp hOn
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hUnif) ε hε] with n hn
  intro x hx
  simpa [Real.dist_eq, abs_sub_comm] using hn x hx

theorem localUniformSequentiallyCompactRange_of_layer4
    {trap : (ℝ → ℝ) → Prop} {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (hAA : ∀ seq : ℕ → ℝ → ℝ, (∀ n, trap (seq n)) →
      ShenWork.PaperOne.LocallyUniformlyBoundedEquicont
        (fun n => Tmap (seq n)))
    (hclosed : ∀ (seq : ℕ → ℝ → ℝ) (subseq : ℕ → ℕ) (f : C(ℝ, ℝ)),
      (∀ n, trap (seq n)) → StrictMono subseq →
        TendstoLocallyUniformly
          (fun n x => Tmap (seq (subseq n)) x) f atTop →
          trap f) :
    LocalUniformSequentiallyCompactRange trap Tmap := by
  intro seq hseq
  rcases ShenWork.PaperOne.exists_locallyUniform_convergent_subseq
      (hAA seq hseq) with ⟨f, subseq, hsubseq, hlim⟩
  exact ⟨subseq, hsubseq, f, hclosed seq subseq f hseq hsubseq hlim,
    locallyUniformConverges_of_tendstoLocallyUniformly hlim⟩
theorem InConstantBarrierTrap.closed_of_tendstoLocallyUniformly
    {M : ℝ} {u : ℕ → ℝ → ℝ} {f : C(ℝ, ℝ)}
    (hu : ∀ n, InConstantBarrierTrap M (u n))
    (hlim : TendstoLocallyUniformly u f atTop) :
    InConstantBarrierTrap M f := by
  have hLU := locallyUniformConverges_of_tendstoLocallyUniformly hlim
  have hnonneg : ∀ x, 0 ≤ f x :=
    fun x => hLU.nonneg_of_forall_nonneg (fun n => ((hu n).2 x).1)
  have hle : ∀ x, f x ≤ M :=
    fun x => hLU.le_of_forall_le (fun n => ((hu n).2 x).2)
  refine ⟨⟨f.continuous, ⟨M, fun x => ?_⟩⟩, fun x => ⟨hnonneg x, hle x⟩⟩
  rw [abs_of_nonneg (hnonneg x)]
  exact hle x
theorem constantBarrierCompactRange_of_layer4
    {M : ℝ} {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (hmap : ∀ u, InConstantBarrierTrap M u →
      InConstantBarrierTrap M (Tmap u))
    (hAA : ∀ seq : ℕ → ℝ → ℝ,
      (∀ n, InConstantBarrierTrap M (seq n)) →
        ShenWork.PaperOne.LocallyUniformlyBoundedEquicont
          (fun n => Tmap (seq n))) :
    LocalUniformSequentiallyCompactRange (InConstantBarrierTrap M) Tmap :=
  localUniformSequentiallyCompactRange_of_layer4 hAA fun seq subseq _f hseq _ hlim =>
    InConstantBarrierTrap.closed_of_tendstoLocallyUniformly
      (u := fun n => Tmap (seq (subseq n)))
      (fun n => hmap (seq (subseq n)) (hseq (subseq n))) hlim
theorem wholeLineSchauderFixedPoint
    {trap : (ℝ → ℝ) → Prop} {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (hprinciple : LocalUniformSchauderFixedPointPrinciple trap)
    (hmap : ∀ u, trap u → trap (Tmap u))
    (hcont : LocalUniformContinuousOn trap Tmap)
    (hcompact : LocalUniformSequentiallyCompactRange trap Tmap) :
    ∃ U : ℝ → ℝ, trap U ∧ Tmap U = U :=
  hprinciple Tmap hmap hcont hcompact
theorem wholeLineConstantBarrierSchauderFixedPoint
    {M : ℝ} {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (hprinciple :
      LocalUniformSchauderFixedPointPrinciple (InConstantBarrierTrap M))
    (hmap : ∀ u, InConstantBarrierTrap M u →
      InConstantBarrierTrap M (Tmap u))
    (hcont : LocalUniformContinuousOn (InConstantBarrierTrap M) Tmap)
    (hAA : ∀ seq : ℕ → ℝ → ℝ,
      (∀ n, InConstantBarrierTrap M (seq n)) →
        ShenWork.PaperOne.LocallyUniformlyBoundedEquicont
          (fun n => Tmap (seq n))) :
    ∃ U : ℝ → ℝ, InConstantBarrierTrap M U ∧ Tmap U = U :=
  wholeLineSchauderFixedPoint hprinciple hmap hcont
    (constantBarrierCompactRange_of_layer4 hmap hAA)
#print axioms wholeLineSchauderFixedPoint
#print axioms wholeLineConstantBarrierSchauderFixedPoint
end
end ShenWork.Paper1
