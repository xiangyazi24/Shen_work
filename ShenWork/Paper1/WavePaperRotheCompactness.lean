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

/-! ## Trap-indexed paper orbit interfaces -/

/-- Fixed-index dependence when the per-profile producer is available exactly
on the monotone trap. -/
def PaperRotheSeqStepDependenceOnTrap
    (p : CMParams) (c lam M κ Λ : ℝ)
    (hprodTrap : ∀ v, InMonotoneWaveTrapSet κ M v →
      PaperRotheStepProducer p c lam M κ Λ v)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) : Prop :=
  let Z := rotheSeqOfPaperFromTrap p c lam M κ Λ hprodTrap hκ hM
  ∀ (seq : ℕ → ℝ → ℝ) (u : ℝ → ℝ),
    (hseq : ∀ n, InMonotoneWaveTrapSet κ M (seq n)) →
      (hu : InMonotoneWaveTrapSet κ M u) →
      LocallyUniformConverges seq u →
        ∀ k : ℕ, LocallyUniformConverges (fun n => Z (seq n) k) (Z u k)

/-- The eventual family-tail interface for a trap-indexed producer. -/
def PaperRotheTailUniformAlongConvergentSeqOnTrap
    (p : CMParams) (c lam M κ Λ : ℝ)
    (hprodTrap : ∀ v, InMonotoneWaveTrapSet κ M v →
      PaperRotheStepProducer p c lam M κ Λ v)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) : Prop :=
  let Z := rotheSeqOfPaperFromTrap p c lam M κ Λ hprodTrap hκ hM
  ∀ (seq : ℕ → ℝ → ℝ) (u : ℝ → ℝ),
    (hseq : ∀ n, InMonotoneWaveTrapSet κ M (seq n)) →
      (hu : InMonotoneWaveTrapSet κ M u) →
      LocallyUniformConverges seq u →
        ∀ R > 0, ∀ ε > 0,
          ∃ K : ℕ,
            (∀ k : ℕ, K ≤ k → ∀ x ∈ Set.Icc (-R) R,
              |Z u k x - rotheLimit (Z u) x| < ε) ∧
            ∀ᶠ n in atTop, ∀ k : ℕ, K ≤ k →
              ∀ x ∈ Set.Icc (-R) R,
                |Z (seq n) k x - rotheLimit (Z (seq n)) x| < ε

/-- The sequence-local tail and fixed-index dependence give continuity of the
trap-defaulted paper Rothe map. -/
theorem paperRotheContinuousDependence_fromTrap_of_tailAlong
    (p : CMParams) (c lam M κ Λ : ℝ)
    (hprodTrap : ∀ v, InMonotoneWaveTrapSet κ M v →
      PaperRotheStepProducer p c lam M κ Λ v)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M)
    (hstep : PaperRotheSeqStepDependenceOnTrap
      p c lam M κ Λ hprodTrap hκ hM)
    (htail : PaperRotheTailUniformAlongConvergentSeqOnTrap
      p c lam M κ Λ hprodTrap hκ hM) :
    RotheContinuousDependence p c lam (InMonotoneWaveTrapSet κ M)
      (rotheSeqOfPaperFromTrap p c lam M κ Λ hprodTrap hκ hM) := by
  intro seq u hseq hu hconv
  let Z := rotheSeqOfPaperFromTrap p c lam M κ Λ hprodTrap hκ hM
  let L : (ℝ → ℝ) → ℝ → ℝ := fun v => rotheLimit (Z v)
  intro R hR ε hε
  obtain ⟨K, htailu, htailseq⟩ :=
    htail seq u hseq hu hconv R hR (ε / 3) (by linarith)
  have hstepK : LocallyUniformConverges (fun n => Z (seq n) K) (Z u K) :=
    hstep seq u hseq hu hconv K
  filter_upwards [htailseq,
    hstepK R hR (ε / 3) (by linarith)] with n htailn hn
  intro x hx
  have h1 : |Z (seq n) K x - L (seq n) x| < ε / 3 :=
    htailn K (le_refl K) x hx
  have h2 : |Z u K x - L u x| < ε / 3 :=
    htailu K (le_refl K) x hx
  have h3 : |Z (seq n) K x - Z u K x| < ε / 3 := hn x hx
  have hdecomp :
      L (seq n) x - L u x =
        -(Z (seq n) K x - L (seq n) x) +
        (Z (seq n) K x - Z u K x) + (Z u K x - L u x) := by ring
  rw [hdecomp]
  calc
    |-(Z (seq n) K x - L (seq n) x) +
        (Z (seq n) K x - Z u K x) + (Z u K x - L u x)|
        ≤ |-(Z (seq n) K x - L (seq n) x) +
            (Z (seq n) K x - Z u K x)| + |Z u K x - L u x| :=
          abs_add_le _ _
    _ ≤ |Z (seq n) K x - L (seq n) x| +
          |Z (seq n) K x - Z u K x| + |Z u K x - L u x| := by
        calc
          |-(Z (seq n) K x - L (seq n) x) +
                (Z (seq n) K x - Z u K x)| + |Z u K x - L u x|
              ≤ (|-(Z (seq n) K x - L (seq n) x)| +
                  |Z (seq n) K x - Z u K x|) + |Z u K x - L u x| :=
                add_le_add (abs_add_le _ _) le_rfl
          _ = |Z (seq n) K x - L (seq n) x| +
                |Z (seq n) K x - Z u K x| + |Z u K x - L u x| := by
              rw [abs_neg]
    _ < ε / 3 + ε / 3 + ε / 3 := by linarith
    _ = ε := by ring

/-- Joint finite/moving-index convergence for the trap-indexed paper orbit. -/
def PaperGreenRotheCompactClosedGraphOnTrap
    (p : CMParams) (c lam M κ Λ : ℝ)
    (hprodTrap : ∀ v, InMonotoneWaveTrapSet κ M v →
      PaperRotheStepProducer p c lam M κ Λ v)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) : Prop :=
  let Z := rotheSeqOfPaperFromTrap p c lam M κ Λ hprodTrap hκ hM
  ∀ (seq : ℕ → ℝ → ℝ) (u : ℝ → ℝ),
    (hseq : ∀ n, InMonotoneWaveTrapSet κ M (seq n)) →
      (hu : InMonotoneWaveTrapSet κ M u) →
      LocallyUniformConverges seq u →
        ∀ (ks : ℕ → ℕ) (K : Option ℕ),
          PaperRotheIndexConverges ks K →
            LocallyUniformConverges (fun n => Z (seq n) (ks n))
              (paperRotheExtendedOrbitValue (Z u) K)

/-- The one analytic residual for the trap-indexed construction: identify any
already-convergent Helly subsequence in both the finite and moving-index cases. -/
def PaperGreenRotheLimitIdentificationOnTrap
    (p : CMParams) (c lam M κ Λ : ℝ)
    (hprodTrap : ∀ v, InMonotoneWaveTrapSet κ M v →
      PaperRotheStepProducer p c lam M κ Λ v)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) : Prop :=
  let Z := rotheSeqOfPaperFromTrap p c lam M κ Λ hprodTrap hκ hM
  ∀ (seq : ℕ → ℝ → ℝ) (u : ℝ → ℝ),
    (hseq : ∀ n, InMonotoneWaveTrapSet κ M (seq n)) →
      (hu : InMonotoneWaveTrapSet κ M u) →
      LocallyUniformConverges seq u →
        ∀ (ks : ℕ → ℕ) (K : Option ℕ),
          PaperRotheIndexConverges ks K →
            ∀ (subseq : ℕ → ℕ), StrictMono subseq →
              ∀ W : ℝ → ℝ,
                LocallyUniformConverges
                  (fun n => Z (seq (subseq n)) (ks (subseq n))) W →
                  W = paperRotheExtendedOrbitValue (Z u) K

/-- The same irreducible Green-limit identification with frozen-drift
convergence exposed as an input.  This is the lowest carried analytic form:
the profile-to-drift convergence itself is already a theorem. -/
def PaperGreenRotheLimitIdentificationFromDriftOnTrap
    (p : CMParams) (c lam M κ Λ : ℝ)
    (hprodTrap : ∀ v, InMonotoneWaveTrapSet κ M v →
      PaperRotheStepProducer p c lam M κ Λ v)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) : Prop :=
  let Z := rotheSeqOfPaperFromTrap p c lam M κ Λ hprodTrap hκ hM
  ∀ (seq : ℕ → ℝ → ℝ) (u : ℝ → ℝ),
    (hseq : ∀ n, InMonotoneWaveTrapSet κ M (seq n)) →
      (hu : InMonotoneWaveTrapSet κ M u) →
      (hconv : LocallyUniformConverges seq u) →
      LocallyUniformConverges
        (fun n => deriv (frozenElliptic p (seq n)))
        (deriv (frozenElliptic p u)) →
        ∀ (ks : ℕ → ℕ) (K : Option ℕ),
          PaperRotheIndexConverges ks K →
            ∀ (subseq : ℕ → ℕ), StrictMono subseq →
              ∀ W : ℝ → ℝ,
                LocallyUniformConverges
                  (fun n => Z (seq (subseq n)) (ks (subseq n))) W →
                  W = paperRotheExtendedOrbitValue (Z u) K

namespace PaperGreenRotheLimitIdentificationFromDriftOnTrap

variable {p : CMParams} {c lam M κ Λ : ℝ}
  {hprodTrap : ∀ v, InMonotoneWaveTrapSet κ M v →
    PaperRotheStepProducer p c lam M κ Λ v}
  {hκ : 0 ≤ κ} {hM : 0 ≤ M}

/-- Supply the frozen-drift convergence from the proved whole-line kernel
theorem `frozenEllipticDerivDependence`. -/
theorem toLimitIdentification
    (hident : PaperGreenRotheLimitIdentificationFromDriftOnTrap
      p c lam M κ Λ hprodTrap hκ hM) :
    PaperGreenRotheLimitIdentificationOnTrap
      p c lam M κ Λ hprodTrap hκ hM := by
  intro seq u hseq hu hconv
  exact hident seq u hseq hu hconv
    (frozenEllipticDerivDependence p hM seq u hseq hu hconv)

end PaperGreenRotheLimitIdentificationFromDriftOnTrap

namespace PaperGreenRotheLimitIdentificationOnTrap

variable {p : CMParams} {c lam M κ Λ : ℝ}
  {hprodTrap : ∀ v, InMonotoneWaveTrapSet κ M v →
    PaperRotheStepProducer p c lam M κ Λ v}
  {hκ : 0 ≤ κ} {hM : 0 ≤ M}

/-- The already-proved Helly/equi-Lipschitz compactness upgrades subsequential
Green-limit identification to the full joint closed graph. -/
theorem compactClosedGraph
    (hident : PaperGreenRotheLimitIdentificationOnTrap
      p c lam M κ Λ hprodTrap hκ hM)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hbarLip : ∀ x y,
      |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|) :
    PaperGreenRotheCompactClosedGraphOnTrap
      p c lam M κ Λ hprodTrap hκ hM := by
  intro seq u hseq hu hconv ks K hks
  let Z := rotheSeqOfPaperFromTrap p c lam M κ Λ hprodTrap hκ hM
  let target := paperRotheExtendedOrbitValue (Z u) K
  have horbit : ∀ v, (hv : InMonotoneWaveTrapSet κ M v) →
      PaperRotheOrbitData p c lam M κ Z v := by
    intro v hv
    simpa [Z] using paperRotheOrbitData_fromTrap
      (p := p) (c := c) (lam := lam) (M := M) (κ := κ) (Λ := Λ)
      (u := v) hprodTrap hκ hM hΛ0 hΛM hbarLip hv
  intro R hR ε hε
  by_contra hnot
  have hfreq : ∃ᶠ n in atTop,
      ¬ ∀ x : ℝ, x ∈ Set.Icc (-R) R →
        |Z (seq n) (ks n) x - target x| < ε := not_eventually.mp hnot
  obtain ⟨bad, hbad_mono, hbad⟩ := extraction_of_frequently_atTop hfreq
  let gs : ℕ → ℝ → ℝ := fun n => Z (seq (bad n)) (ks (bad n))
  have hgsL : ∀ n, ∀ x y, |gs n x - gs n y| ≤ M * |x - y| := by
    intro n x y
    exact (horbit (seq (bad n)) (hseq (bad n))).equiLip (ks (bad n)) x y
  have hgsB : ∀ n x, |gs n x| ≤ M := by
    intro n x
    rw [abs_le]
    exact ⟨by linarith [
        (horbit (seq (bad n)) (hseq (bad n))).nonneg (ks (bad n)) x],
      (horbit (seq (bad n)) (hseq (bad n))).le_M (ks (bad n)) x⟩
  obtain ⟨sub, hsub_mono, g, hpoint, hgL⟩ :=
    helly_pointwise_selection M gs hgsL hgsB
  have hLU : LocallyUniformConverges (fun n => gs (sub n)) g :=
    locallyUniform_of_helly_pointwise hM hpoint hgsL hgL
  let total : ℕ → ℕ := bad ∘ sub
  have htotal_mono : StrictMono total := hbad_mono.comp hsub_mono
  have hLUtotal : LocallyUniformConverges
      (fun n => Z (seq (total n)) (ks (total n))) g := by
    simpa [total, gs, Function.comp_apply] using hLU
  have hg : g = target := by
    exact hident seq u hseq hu hconv ks K hks total htotal_mono g hLUtotal
  have htargetLU : LocallyUniformConverges
      (fun n => Z (seq (total n)) (ks (total n))) target := by
    simpa [hg] using hLUtotal
  obtain ⟨n, hn⟩ := (htargetLU R hR ε hε).exists
  have hbadn := hbad (sub n)
  have htotal_eq : total n = bad (sub n) := rfl
  rw [← htotal_eq] at hbadn
  exact hbadn hn

end PaperGreenRotheLimitIdentificationOnTrap

namespace PaperGreenRotheCompactClosedGraphOnTrap

variable {p : CMParams} {c lam M κ Λ : ℝ}
  {hprodTrap : ∀ v, InMonotoneWaveTrapSet κ M v →
    PaperRotheStepProducer p c lam M κ Λ v}
  {hκ : 0 ≤ κ} {hM : 0 ≤ M}

theorem stepDependence
    (hgraph : PaperGreenRotheCompactClosedGraphOnTrap
      p c lam M κ Λ hprodTrap hκ hM) :
    PaperRotheSeqStepDependenceOnTrap
      p c lam M κ Λ hprodTrap hκ hM := by
  intro seq u hseq hu hconv k
  exact hgraph seq u hseq hu hconv (fun _ => k) (some k)
    (.finite k (Eventually.of_forall fun _ => rfl))

theorem tailAlongConvergentSeq
    (hgraph : PaperGreenRotheCompactClosedGraphOnTrap
      p c lam M κ Λ hprodTrap hκ hM)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hbarLip : ∀ x y,
      |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|) :
    PaperRotheTailUniformAlongConvergentSeqOnTrap
      p c lam M κ Λ hprodTrap hκ hM := by
  intro seq u hseq hu hconv R hR ε hε
  let Z := rotheSeqOfPaperFromTrap p c lam M κ Λ hprodTrap hκ hM
  let L : (ℝ → ℝ) → ℝ → ℝ := fun v => rotheLimit (Z v)
  have horbit : ∀ v, (hv : InMonotoneWaveTrapSet κ M v) →
      PaperRotheOrbitData p c lam M κ Z v := by
    intro v hv
    simpa [Z] using paperRotheOrbitData_fromTrap
      (p := p) (c := c) (lam := lam) (M := M) (κ := κ) (Λ := Λ)
      (u := v) hprodTrap hκ hM hΛ0 hΛM hbarLip hv
  let δ : ℝ := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨K, hK⟩ :=
    eventually_atTop.1 ((horbit u hu).locallyUniform hM R hR δ hδ)
  have htarget : ∀ k : ℕ, K ≤ k → ∀ x ∈ Set.Icc (-R) R,
      |Z u k x - L u x| < ε := by
    intro k hk x hx
    have hsmall := hK k hk x hx
    dsimp [δ] at hsmall
    linarith
  have hexLate : ∀ n : ℕ, ∃ ell : ℕ, n ≤ ell ∧
      ∀ x ∈ Set.Icc (-R) R, |Z (seq n) ell x - L (seq n) x| < δ := by
    intro n
    obtain ⟨N, hN⟩ := eventually_atTop.1
      ((horbit (seq n) (hseq n)).locallyUniform hM R hR δ hδ)
    refine ⟨max n N, le_max_left _ _, hN (max n N) (le_max_right _ _)⟩
  let ell : ℕ → ℕ := fun n => Classical.choose (hexLate n)
  have hell_ge : ∀ n, n ≤ ell n := fun n => (Classical.choose_spec (hexLate n)).1
  have hell_tail : ∀ n x, x ∈ Set.Icc (-R) R →
      |Z (seq n) (ell n) x - L (seq n) x| < δ :=
    fun n => (Classical.choose_spec (hexLate n)).2
  have hell_top : Tendsto ell atTop atTop := by
    refine tendsto_atTop.2 fun N => ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    exact le_trans hn (hell_ge n)
  have hfixed : LocallyUniformConverges (fun n => Z (seq n) K) (Z u K) :=
    hgraph seq u hseq hu hconv (fun _ => K) (some K)
      (.finite K (Eventually.of_forall fun _ => rfl))
  have hmoving : LocallyUniformConverges (fun n => Z (seq n) (ell n)) (L u) := by
    exact hgraph seq u hseq hu hconv ell none (.infinity hell_top)
  refine ⟨K, htarget, ?_⟩
  filter_upwards [hfixed R hR δ hδ, hmoving R hR δ hδ] with n hnK hnell
  intro k hk x hx
  have hLn_le_k : L (seq n) x ≤ Z (seq n) k x :=
    ciInf_le ((horbit (seq n) (hseq n)).bddBelow x) k
  have hLn_le_K : L (seq n) x ≤ Z (seq n) K x :=
    ciInf_le ((horbit (seq n) (hseq n)).bddBelow x) K
  have hk_le_K : Z (seq n) k x ≤ Z (seq n) K x :=
    (horbit (seq n) (hseq n)).anti_k x hk
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
          (Z (seq n) K x - Z u K x) + (Z u K x - L u x) +
          (L u x - Z (seq n) (ell n) x) +
          (Z (seq n) (ell n) x - L (seq n) x) := by ring
    let a := Z (seq n) K x - Z u K x
    let b := Z u K x - L u x
    let c' := L u x - Z (seq n) (ell n) x
    let d := Z (seq n) (ell n) x - L (seq n) x
    have ht1 : |a + b + c' + d| ≤ |a + b + c'| + |d| := abs_add_le _ _
    have ht2 : |a + b + c'| ≤ |a + b| + |c'| := abs_add_le _ _
    have ht3 : |a + b| ≤ |a| + |b| := abs_add_le _ _
    rw [hdecomp]
    change |a + b + c' + d| < ε
    calc
      |a + b + c' + d| ≤ |a + b + c'| + |d| := ht1
      _ ≤ (|a + b| + |c'|) + |d| := add_le_add ht2 le_rfl
      _ ≤ ((|a| + |b|) + |c'|) + |d| :=
        add_le_add (add_le_add ht3 le_rfl) le_rfl
      _ < δ + δ + δ + δ := by linarith
      _ = ε := by dsimp [δ]; ring
  have hgap_nonneg : 0 ≤ Z (seq n) k x - L (seq n) x :=
    sub_nonneg.mpr hLn_le_k
  have hgapK_nonneg : 0 ≤ Z (seq n) K x - L (seq n) x :=
    sub_nonneg.mpr hLn_le_K
  rw [abs_of_nonneg hgap_nonneg]
  calc
    Z (seq n) k x - L (seq n) x ≤ Z (seq n) K x - L (seq n) x :=
      sub_le_sub_right hk_le_K _
    _ = |Z (seq n) K x - L (seq n) x| :=
      (abs_of_nonneg hgapK_nonneg).symm
    _ < ε := hKsmall

theorem stepDependence_and_tailAlong
    (hgraph : PaperGreenRotheCompactClosedGraphOnTrap
      p c lam M κ Λ hprodTrap hκ hM)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hbarLip : ∀ x y,
      |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|) :
    PaperRotheSeqStepDependenceOnTrap
        p c lam M κ Λ hprodTrap hκ hM ∧
      PaperRotheTailUniformAlongConvergentSeqOnTrap
        p c lam M κ Λ hprodTrap hκ hM :=
  ⟨hgraph.stepDependence,
    hgraph.tailAlongConvergentSeq hΛ0 hΛM hbarLip⟩

end PaperGreenRotheCompactClosedGraphOnTrap

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

/-- The irreducible Green-kernel identification statement.

All compactness is deliberately absent from this predicate: a candidate
subsequence is already assumed to converge locally uniformly.  The analytic
content is exactly that passing the parameterized Green step to that limit
identifies it with the finite target iterate, or with the limiting Rothe state
when the outer indices move to infinity. -/
def PaperGreenRotheLimitIdentification
    (p : CMParams) (c lam M κ Λ : ℝ)
    (hprodAll : ∀ v, PaperRotheStepProducer p c lam M κ Λ v)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) : Prop :=
  ∀ (seq : ℕ → ℝ → ℝ) (u : ℝ → ℝ),
    (hseq : ∀ n, InMonotoneWaveTrapSet κ M (seq n)) →
      (hu : InMonotoneWaveTrapSet κ M u) →
      LocallyUniformConverges seq u →
        ∀ (ks : ℕ → ℕ) (K : Option ℕ),
          PaperRotheIndexConverges ks K →
            ∀ (subseq : ℕ → ℕ), StrictMono subseq →
              ∀ W : ℝ → ℝ,
                LocallyUniformConverges
                  (fun n => rotheSeqOfPaper p c lam M κ Λ (seq (subseq n))
                    (hprodAll (seq (subseq n))) hκ hM (ks (subseq n))) W →
                  W = paperRotheExtendedOrbitValue
                    (rotheSeqOfPaper p c lam M κ Λ u
                      (hprodAll u) hκ hM) K

namespace PaperGreenRotheLimitIdentification

variable {p : CMParams} {c lam M κ Λ : ℝ}
  {hprodAll : ∀ v, PaperRotheStepProducer p c lam M κ Λ v}
  {hκ : 0 ≤ κ} {hM : 0 ≤ M}

/-- Helly compactness plus unique Green-limit identification gives convergence
of the whole joint parameter/index sequence. -/
theorem compactClosedGraph
    (hident : PaperGreenRotheLimitIdentification
      p c lam M κ Λ hprodAll hκ hM)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hbarLip : ∀ x y,
      |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|) :
    PaperGreenRotheCompactClosedGraph
      p c lam M κ Λ hprodAll hκ hM := by
  intro seq u hseq hu hconv ks K hks
  let Z : (ℝ → ℝ) → ℕ → ℝ → ℝ := fun v =>
    rotheSeqOfPaper p c lam M κ Λ v (hprodAll v) hκ hM
  let target : ℝ → ℝ := paperRotheExtendedOrbitValue (Z u) K
  have horbit : ∀ v, PaperRotheOrbitData p c lam M κ Z v := by
    intro v
    simpa [Z] using
      (paperRotheOrbitData (p := p) (c := c) (lam := lam) (M := M)
        (κ := κ) (Λ := Λ) (u := v) hprodAll hκ hM hΛ0 hΛM hbarLip)
  intro R hR ε hε
  by_contra hnot
  have hfreq : ∃ᶠ n in atTop,
      ¬ ∀ x : ℝ, x ∈ Set.Icc (-R) R →
        |Z (seq n) (ks n) x - target x| < ε := by
    exact (not_eventually.mp hnot)
  obtain ⟨bad, hbad_mono, hbad⟩ := extraction_of_frequently_atTop hfreq
  let gs : ℕ → ℝ → ℝ := fun n => Z (seq (bad n)) (ks (bad n))
  have hgsL : ∀ n, ∀ x y, |gs n x - gs n y| ≤ M * |x - y| := by
    intro n x y
    exact (horbit (seq (bad n))).equiLip (ks (bad n)) x y
  have hgsB : ∀ n x, |gs n x| ≤ M := by
    intro n x
    rw [abs_le]
    exact ⟨by linarith [(horbit (seq (bad n))).nonneg (ks (bad n)) x],
      (horbit (seq (bad n))).le_M (ks (bad n)) x⟩
  obtain ⟨sub, hsub_mono, g, hpoint, hgL⟩ :=
    helly_pointwise_selection M gs hgsL hgsB
  have hLU : LocallyUniformConverges (fun n => gs (sub n)) g :=
    locallyUniform_of_helly_pointwise hM hpoint hgsL hgL
  let total : ℕ → ℕ := bad ∘ sub
  have htotal_mono : StrictMono total := hbad_mono.comp hsub_mono
  have hLUtotal : LocallyUniformConverges
      (fun n => Z (seq (total n)) (ks (total n))) g := by
    simpa [total, gs, Function.comp_apply] using hLU
  have hg : g = target := by
    have hi := hident seq u hseq hu hconv ks K hks total htotal_mono g
    simpa [Z, target] using hi hLUtotal
  have htargetLU : LocallyUniformConverges
      (fun n => Z (seq (total n)) (ks (total n))) target := by
    simpa [hg] using hLUtotal
  have hevent := htargetLU R hR ε hε
  obtain ⟨n, hn⟩ := hevent.exists
  have hbadn := hbad (sub n)
  have htotal_eq : total n = bad (sub n) := rfl
  rw [← htotal_eq] at hbadn
  exact hbadn (hn)

end PaperGreenRotheLimitIdentification

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

#print axioms paperRotheContinuousDependence_fromTrap_of_tailAlong
#print axioms PaperGreenRotheLimitIdentificationFromDriftOnTrap.toLimitIdentification
#print axioms PaperGreenRotheLimitIdentificationOnTrap.compactClosedGraph
#print axioms PaperGreenRotheCompactClosedGraphOnTrap.stepDependence
#print axioms PaperGreenRotheCompactClosedGraphOnTrap.tailAlongConvergentSeq
#print axioms PaperGreenRotheCompactClosedGraphOnTrap.stepDependence_and_tailAlong
#print axioms PaperGreenRotheLimitIdentification.compactClosedGraph
#print axioms PaperGreenRotheCompactClosedGraph.stepDependence
#print axioms PaperGreenRotheCompactClosedGraph.tailAlongConvergentSeq
#print axioms PaperGreenRotheCompactClosedGraph.stepDependence_and_tailAlong

end AxiomAudit

end ShenWork.Paper1
