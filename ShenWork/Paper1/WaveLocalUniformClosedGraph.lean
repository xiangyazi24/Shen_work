import ShenWork.Paper1.Statements

open Filter Topology Set

noncomputable section

namespace ShenWork.Paper1

/-- Sequential closed graph for a map on a local-uniform trap.  The output
limit is allowed to be obtained only after subsequence extraction. -/
def LocalUniformSequentialClosedGraphOn
    (trap : (ℝ → ℝ) → Prop) (Tmap : (ℝ → ℝ) → ℝ → ℝ) : Prop :=
  ∀ (seq : ℕ → ℝ → ℝ) (u V : ℝ → ℝ),
    (∀ n, trap (seq n)) → trap u → trap V →
      LocallyUniformConverges seq u →
      LocallyUniformConverges (fun n => Tmap (seq n)) V →
        V = Tmap u

/-- Compact range plus a sequentially closed, single-valued graph gives
sequential continuity in the compact-open topology.  This is the precise
topological reduction behind the difficult Rothe double-limit step. -/
theorem LocalUniformSequentiallyCompactRange.continuousOn_of_closedGraph
    {trap : (ℝ → ℝ) → Prop} {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (hcompact : LocalUniformSequentiallyCompactRange trap Tmap)
    (hgraph : LocalUniformSequentialClosedGraphOn trap Tmap) :
    LocalUniformContinuousOn trap Tmap := by
  intro seq u hseq hu hinput R hR ε hε
  by_contra hnot
  rw [Filter.not_eventually] at hnot
  simp only [not_forall, not_lt] at hnot
  obtain ⟨sub, hsub, hbad⟩ :=
    Filter.extraction_of_frequently_atTop hnot
  obtain ⟨sub₂, hsub₂, V, hV, houtput⟩ :=
    hcompact (fun n => seq (sub n)) (fun n => hseq (sub n))
  have hsubcomp : StrictMono (sub ∘ sub₂) := hsub.comp hsub₂
  have hinput' :
      LocallyUniformConverges (fun n => seq (sub (sub₂ n))) u := by
    simpa [Function.comp_apply] using hinput.comp_strictMono hsubcomp
  have houtput' :
      LocallyUniformConverges
        (fun n => Tmap (seq (sub (sub₂ n)))) V := by
    simpa [Function.comp_apply] using houtput
  have hVU : V = Tmap u :=
    hgraph (fun n => seq (sub (sub₂ n))) u V
      (fun n => hseq (sub (sub₂ n))) hu hV hinput' houtput'
  have hgood : ∀ᶠ n in atTop,
      ∀ x : ℝ, x ∈ Set.Icc (-R) R →
        |Tmap (seq (sub (sub₂ n))) x - Tmap u x| < ε := by
    simpa [hVU] using houtput' R hR ε hε
  obtain ⟨n, hn⟩ := hgood.exists
  obtain ⟨x, hx, hge⟩ := hbad (sub₂ n)
  exact (not_lt_of_ge hge) (hn x hx)

section AxiomAudit

#print axioms LocalUniformSequentiallyCompactRange.continuousOn_of_closedGraph

end AxiomAudit

end ShenWork.Paper1
