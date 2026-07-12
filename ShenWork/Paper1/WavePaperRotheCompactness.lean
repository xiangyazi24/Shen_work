/-
  Parameterized compact closed graph for the paper Rothe orbit.

  The analytic Green-kernel task is isolated as one joint graph property.  This
  file proves that the property gives both fixed-index dependence and the only
  family-uniform tail needed by the Schauder continuity argument.
-/
import ShenWork.Paper1.WaveRotheConcrete

open Filter Topology Set

noncomputable section

namespace ShenWork.Paper1

/-- Convergence of a varying outer Rothe index to either a finite index or the
infinite-index limit. -/
inductive PaperRotheIndexConverges (ks : ℕ → ℕ) : Option ℕ → Prop
  | finite (k : ℕ) (eventually_eq : ∀ᶠ n in atTop, ks n = k) :
      PaperRotheIndexConverges ks (some k)
  | infinity (tendsto_atTop : Tendsto ks atTop atTop) :
      PaperRotheIndexConverges ks none

/-- Evaluation of a Rothe orbit at a finite index or at its outer limit. -/
def paperRotheExtendedOrbitValue
    (z : ℕ → ℝ → ℝ) : Option ℕ → ℝ → ℝ
  | some k => z k
  | none => rotheLimit z

/-- The single analytic compact closed-graph statement for the parameterized
paper Green--Rothe orbit.

It covers both cases required by the construction.  If `ks` is eventually a
finite `k`, it identifies the ordinary parameterized step limit.  If
`ks n → ∞`, it identifies every moving-index compact limit with the Rothe
limit for the limiting frozen profile.  The latter is the Green-kernel/tail
identification that cannot be replaced by a global Dini assertion. -/
def PaperGreenRotheCompactClosedGraph
    (p : CMParams) (c lam M κ Λ : ℝ)
    (hprodAll : ∀ v, PaperRotheStepProducer p c lam M κ Λ v)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) : Prop :=
  ∀ (seq : ℕ → ℝ → ℝ) (u : ℝ → ℝ),
    (hseq : ∀ n, InMonotoneWaveTrapSet κ M (seq n)) →
      (hu : InMonotoneWaveTrapSet κ M u) →
      LocallyUniformConverges seq u →
        ∀ (ks : ℕ → ℕ) (K : Option ℕ),
          PaperRotheIndexConverges ks K →
            LocallyUniformConverges
              (fun n => rotheSeqOfPaper p c lam M κ Λ (seq n)
                (hprodAll (seq n)) hκ hM (ks n))
              (paperRotheExtendedOrbitValue
                (rotheSeqOfPaper p c lam M κ Λ u
                  (hprodAll u) hκ hM) K)

namespace PaperGreenRotheCompactClosedGraph

variable {p : CMParams} {c lam M κ Λ : ℝ}
  {hprodAll : ∀ v, PaperRotheStepProducer p c lam M κ Λ v}
  {hκ : 0 ≤ κ} {hM : 0 ≤ M}

/-- The finite-index part of the joint closed graph, packaged in the existing
fixed-step dependence interface. -/
theorem stepDependence
    (hgraph : PaperGreenRotheCompactClosedGraph
      p c lam M κ Λ hprodAll hκ hM) :
    PaperRotheSeqStepDependence p c lam M κ Λ hprodAll hκ hM := by
  intro seq u hseq hu hconv k
  have h := hgraph seq u hseq hu hconv (fun _ => k) (some k)
    (.finite k (Eventually.of_forall fun _ => rfl))
  simpa [paperRotheExtendedOrbitValue] using h

/-- A reindexing tending to infinity preserves local-uniform convergence. -/
private theorem locallyUniform_comp_tendsto_atTop
    {fs : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {ks : ℕ → ℕ}
    (h : LocallyUniformConverges fs f) (hks : Tendsto ks atTop atTop) :
    LocallyUniformConverges (fun n => fs (ks n)) f := by
  intro R hR ε hε
  exact hks.eventually (h R hR ε hε)

/-- The moving-index part of the joint closed graph, together with the already
proved fixed-profile orbit compactness, yields the sequence-local uniform tail.

For each family member choose a later index `ell n ≥ n` already close to its
own Rothe limit.  The joint graph sends these later states to the limiting
profile's Rothe limit, while its finite-index case controls the common cutoff
`K`.  Monotonicity in the outer index then controls every `k ≥ K`. -/
theorem tailAlongConvergentSeq
    (hgraph : PaperGreenRotheCompactClosedGraph
      p c lam M κ Λ hprodAll hκ hM)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hbarLip : ∀ x y,
      |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|) :
    PaperRotheTailUniformAlongConvergentSeq
      p c lam M κ Λ hprodAll hκ hM := by
  intro seq u hseq hu hconv R hR ε hε
  let Z : (ℝ → ℝ) → ℕ → ℝ → ℝ := fun v =>
    rotheSeqOfPaper p c lam M κ Λ v (hprodAll v) hκ hM
  let L : (ℝ → ℝ) → ℝ → ℝ := fun v => rotheLimit (Z v)
  have horbit : ∀ v, PaperRotheOrbitData p c lam M κ Z v := by
    intro v
    simpa [Z] using
      (paperRotheOrbitData (p := p) (c := c) (lam := lam) (M := M)
        (κ := κ) (Λ := Λ) (u := v) hprodAll hκ hM hΛ0 hΛM hbarLip)
  let δ : ℝ := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨K, hK⟩ :=
    eventually_atTop.1 ((horbit u).locallyUniform hM R hR δ hδ)
  have htarget : ∀ k : ℕ, K ≤ k → ∀ x ∈ Set.Icc (-R) R,
      |Z u k x - L u x| < ε := by
    intro k hk x hx
    have hsmall := hK k hk x hx
    dsimp [δ] at hsmall
    linarith
  have hexLate : ∀ n : ℕ, ∃ ell : ℕ, n ≤ ell ∧
      ∀ x ∈ Set.Icc (-R) R, |Z (seq n) ell x - L (seq n) x| < δ := by
    intro n
    obtain ⟨N, hN⟩ :=
      eventually_atTop.1 ((horbit (seq n)).locallyUniform hM R hR δ hδ)
    refine ⟨max n N, le_max_left _ _, ?_⟩
    exact hN (max n N) (le_max_right _ _)
  let ell : ℕ → ℕ := fun n => Classical.choose (hexLate n)
  have hell_ge : ∀ n, n ≤ ell n := fun n => (Classical.choose_spec (hexLate n)).1
  have hell_tail : ∀ n x, x ∈ Set.Icc (-R) R →
      |Z (seq n) (ell n) x - L (seq n) x| < δ :=
    fun n => (Classical.choose_spec (hexLate n)).2
  have hell_top : Tendsto ell atTop atTop := by
    refine tendsto_atTop.2 fun N => ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    exact le_trans hn (hell_ge n)
  have hfixed : LocallyUniformConverges (fun n => Z (seq n) K) (Z u K) := by
    have h := hgraph seq u hseq hu hconv (fun _ => K) (some K)
      (.finite K (Eventually.of_forall fun _ => rfl))
    simpa [Z, paperRotheExtendedOrbitValue] using h
  have hmoving : LocallyUniformConverges (fun n => Z (seq n) (ell n)) (L u) := by
    have h := hgraph seq u hseq hu hconv ell none (.infinity hell_top)
    simpa [Z, L, paperRotheExtendedOrbitValue] using h
  refine ⟨K, htarget, ?_⟩
  filter_upwards [hfixed R hR δ hδ, hmoving R hR δ hδ] with n hnK hnell
  intro k hk x hx
  have hLn_le_k : L (seq n) x ≤ Z (seq n) k x := by
    exact ciInf_le ((horbit (seq n)).bddBelow x) k
  have hLn_le_K : L (seq n) x ≤ Z (seq n) K x := by
    exact ciInf_le ((horbit (seq n)).bddBelow x) K
  have hk_le_K : Z (seq n) k x ≤ Z (seq n) K x :=
    (horbit (seq n)).anti_k x hk
  have hKsmall : |Z (seq n) K x - L (seq n) x| < ε := by
    have h1 : |Z (seq n) K x - Z u K x| < δ := hnK x hx
    have h2 : |Z u K x - L u x| < δ := hK K (le_refl K) x hx
    have h3 : |L u x - Z (seq n) (ell n) x| < δ := by
      rw [abs_sub_comm]
      exact hnell x hx
    have h4 : |Z (seq n) (ell n) x - L (seq n) x| < δ :=
      hell_tail n x hx
    have hdecomp :
        Z (seq n) K x - L (seq n) x =
          (Z (seq n) K x - Z u K x) +
          (Z u K x - L u x) +
          (L u x - Z (seq n) (ell n) x) +
          (Z (seq n) (ell n) x - L (seq n) x) := by ring
    let a := Z (seq n) K x - Z u K x
    let b := Z u K x - L u x
    let c' := L u x - Z (seq n) (ell n) x
    let d := Z (seq n) (ell n) x - L (seq n) x
    have htri1 : |a + b + c' + d| ≤ |a + b + c'| + |d| :=
      abs_add_le _ _
    have htri2 : |a + b + c'| ≤ |a + b| + |c'| :=
      abs_add_le _ _
    have htri3 : |a + b| ≤ |a| + |b| := abs_add_le _ _
    rw [hdecomp]
    change |a + b + c' + d| < ε
    calc
      |a + b + c' + d| ≤ |a + b + c'| + |d| := htri1
      _ ≤ (|a + b| + |c'|) + |d| := add_le_add htri2 le_rfl
      _ ≤ ((|a| + |b|) + |c'|) + |d| :=
        add_le_add (add_le_add htri3 le_rfl) le_rfl
      _ < δ + δ + δ + δ := by linarith
      _ = ε := by dsimp [δ]; ring
  have hgap_nonneg : 0 ≤ Z (seq n) k x - L (seq n) x :=
    sub_nonneg.mpr hLn_le_k
  have hgapK_nonneg : 0 ≤ Z (seq n) K x - L (seq n) x :=
    sub_nonneg.mpr hLn_le_K
  rw [abs_of_nonneg hgap_nonneg]
  calc
    Z (seq n) k x - L (seq n) x
        ≤ Z (seq n) K x - L (seq n) x := sub_le_sub_right hk_le_K _
    _ = |Z (seq n) K x - L (seq n) x| :=
      (abs_of_nonneg hgapK_nonneg).symm
    _ < ε := hKsmall

/-- The joint compact closed graph discharges both carried orbit frontiers. -/
theorem stepDependence_and_tailAlong
    (hgraph : PaperGreenRotheCompactClosedGraph
      p c lam M κ Λ hprodAll hκ hM)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hbarLip : ∀ x y,
      |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|) :
    PaperRotheSeqStepDependence p c lam M κ Λ hprodAll hκ hM ∧
      PaperRotheTailUniformAlongConvergentSeq
        p c lam M κ Λ hprodAll hκ hM :=
  ⟨hgraph.stepDependence,
    hgraph.tailAlongConvergentSeq hΛ0 hΛM hbarLip⟩

end PaperGreenRotheCompactClosedGraph

section AxiomAudit

#print axioms PaperGreenRotheCompactClosedGraph.stepDependence
#print axioms PaperGreenRotheCompactClosedGraph.tailAlongConvergentSeq
#print axioms PaperGreenRotheCompactClosedGraph.stepDependence_and_tailAlong

end AxiomAudit

end ShenWork.Paper1
