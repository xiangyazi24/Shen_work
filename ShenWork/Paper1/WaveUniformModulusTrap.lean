import ShenWork.Paper1.WaveRotheConcrete

open Filter Topology Set

noncomputable section

namespace ShenWork.Paper1

/-- The compact-open strengthening of the monotone wave trap: in addition to
the paper order bounds, every profile has the same global spatial modulus.
A uniform `C^{2,β}` estimate implies this field through its first-derivative
bound; only this consequence is needed for compactness in `C⁰_loc`. -/
structure InUniformModulusMonotoneWaveTrap
    (κ M L : ℝ) (u : ℝ → ℝ) : Prop where
  bare : InMonotoneWaveTrapSet κ M u
  modulus : ∀ x y, |u x - u y| ≤ L * |x - y|

/-- The lower-pinned version used by the Paper 1 construction. -/
structure InLowerPinnedUniformModulusMonotoneTrap
    (κ M L : ℝ) (φ u : ℝ → ℝ) : Prop where
  uniformTrap : InUniformModulusMonotoneWaveTrap κ M L u
  lower : ∀ x, φ x ≤ u x

/-- Every Paper Rothe limit already lands in the uniform-modulus strengthening
with modulus `M`; no additional Schauder estimate is needed for the `C⁰_loc`
compactness layer. -/
theorem paperTmap_mem_uniformModulusTrap
    (p : CMParams) (c lam M κ : ℝ) (hM : 0 ≤ M)
    (rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ)
    (hdata : ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperRotheOrbitData p c lam M κ rotheSeq u) :
    ∀ u, InMonotoneWaveTrapSet κ M u →
      InUniformModulusMonotoneWaveTrap κ M M
        (rotheLimit (rotheSeq u)) := by
  intro u hu
  exact
    ⟨paperTmap_maps_trap p c lam M κ hM rotheSeq
        (upperBarrier_isBddFun hM) hdata u hu,
      (hdata u hu).limitLip⟩

namespace InUniformModulusMonotoneWaveTrap

variable {κ M L : ℝ} {u v : ℝ → ℝ}

theorem set_convex (κ M L : ℝ) :
    Convex ℝ {u : ℝ → ℝ | InUniformModulusMonotoneWaveTrap κ M L u} := by
  rw [convex_iff_add_mem]
  intro u hu v hv a b ha hb hab
  refine ⟨(InMonotoneWaveTrapSet.set_convex κ M) hu.bare hv.bare ha hb hab, ?_⟩
  intro x y
  change
    |(a * u x + b * v x) - (a * u y + b * v y)| ≤ L * |x - y|
  calc
    |(a * u x + b * v x) - (a * u y + b * v y)| =
        |a * (u x - u y) + b * (v x - v y)| := by ring_nf
    _ ≤ |a * (u x - u y)| + |b * (v x - v y)| := abs_add_le _ _
    _ = a * |u x - u y| + b * |v x - v y| := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * (L * |x - y|) + b * (L * |x - y|) :=
      add_le_add
        (mul_le_mul_of_nonneg_left (hu.modulus x y) ha)
        (mul_le_mul_of_nonneg_left (hv.modulus x y) hb)
    _ = (a + b) * (L * |x - y|) := by ring
    _ = L * |x - y| := by rw [hab, one_mul]

/-- Uniform-modulus wave traps are sequentially compact for local-uniform
convergence.  This is the precise `C⁰_loc` compactness consequence of the
strengthened trap proposed in the Paper 1 construction. -/
theorem locallyUniform_sequentiallyCompact
    (hM : 0 ≤ M) (hL : 0 ≤ L) :
    LocalUniformSequentiallyCompactRange
      (InUniformModulusMonotoneWaveTrap κ M L) (fun u => u) := by
  intro seq hseq
  let Q : ℝ := max M L
  have hQ : 0 ≤ Q := by
    rcases le_total M L with hML | hLM
    · simpa [Q, max_eq_right hML] using hL
    · simpa [Q, max_eq_left hLM] using hM
  have hLipQ : ∀ n x y,
      |seq n x - seq n y| ≤ Q * |x - y| := by
    intro n x y
    exact le_trans ((hseq n).modulus x y)
      (mul_le_mul_of_nonneg_right (le_max_right M L) (abs_nonneg _))
  have hBddQ : ∀ n x, |seq n x| ≤ Q := by
    intro n x
    rw [abs_of_nonneg ((hseq n).bare.nonneg x)]
    exact le_trans ((hseq n).bare.le_M x) (le_max_left M L)
  obtain ⟨sub, hsub, g, hpt, hgQ⟩ :=
    helly_pointwise_selection Q seq hLipQ hBddQ
  have hLU : LocallyUniformConverges (fun n => seq (sub n)) g :=
    locallyUniform_of_helly_pointwise hQ hpt hLipQ hgQ
  have hanti : Antitone g :=
    hLU.antitone_of_forall_antitone (fun n => (hseq (sub n)).bare.antitone)
  have hnn : ∀ x, 0 ≤ g x :=
    fun x => hLU.nonneg_of_forall_nonneg
      (fun n => (hseq (sub n)).bare.nonneg x)
  have hleM : ∀ x, g x ≤ M :=
    fun x => hLU.le_of_forall_le (fun n => (hseq (sub n)).bare.le_M x)
  have hbar : ∀ x, g x ≤ upperBarrier κ M x :=
    fun x => hLU.le_of_forall_le
      (fun n => (hseq (sub n)).bare.le_upperBarrier x)
  have hgcont : Continuous g :=
    continuous_of_locallyUniform
      (fun n => (hseq (sub n)).bare.trap.cunif_bdd.1) hLU
  have hgbdd : IsBddFun g := by
    refine ⟨M, fun x => ?_⟩
    rw [abs_of_nonneg (hnn x)]
    exact hleM x
  have hgbare : InMonotoneWaveTrapSet κ M g :=
    ⟨⟨⟨hgcont, hgbdd⟩, fun x => ⟨hnn x, hbar x⟩⟩, hanti⟩
  have hgL : ∀ x y, |g x - g y| ≤ L * |x - y| := by
    intro x y
    have htend : Tendsto
        (fun n => |seq (sub n) x - seq (sub n) y|) atTop
        (𝓝 (|g x - g y|)) := ((hpt x).sub (hpt y)).abs
    refine le_of_tendsto htend ?_
    exact Eventually.of_forall (fun n => (hseq (sub n)).modulus x y)
  refine ⟨sub, hsub, g, ⟨hgbare, hgL⟩, ?_⟩
  simpa using hLU

end InUniformModulusMonotoneWaveTrap

/-- The Paper Rothe map has locally-uniformly sequentially compact range by
factoring its image through the uniform-modulus trap. -/
theorem paperTmap_compactRange_of_uniformModulus
    (p : CMParams) (c lam M κ : ℝ) (hM : 0 ≤ M)
    (rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ)
    (hdata : ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperRotheOrbitData p c lam M κ rotheSeq u) :
    LocalUniformSequentiallyCompactRange
      (InMonotoneWaveTrapSet κ M) (fun u => rotheLimit (rotheSeq u)) := by
  intro seq hseq
  let gs : ℕ → ℝ → ℝ := fun n => rotheLimit (rotheSeq (seq n))
  have hgs : ∀ n, InUniformModulusMonotoneWaveTrap κ M M (gs n) :=
    fun n => paperTmap_mem_uniformModulusTrap p c lam M κ hM rotheSeq
      hdata (seq n) (hseq n)
  obtain ⟨sub, hsub, g, hg, hconv⟩ :=
    InUniformModulusMonotoneWaveTrap.locallyUniform_sequentiallyCompact
      (κ := κ) hM hM gs hgs
  refine ⟨sub, hsub, g, hg.bare, ?_⟩
  simpa [gs] using hconv

namespace InLowerPinnedUniformModulusMonotoneTrap

variable {κ M L : ℝ} {φ : ℝ → ℝ}

theorem set_convex (κ M L : ℝ) (φ : ℝ → ℝ) :
    Convex ℝ
      {u : ℝ → ℝ | InLowerPinnedUniformModulusMonotoneTrap κ M L φ u} := by
  rw [convex_iff_add_mem]
  intro u hu v hv a b ha hb hab
  refine
    ⟨(InUniformModulusMonotoneWaveTrap.set_convex κ M L)
      hu.uniformTrap hv.uniformTrap ha hb hab, ?_⟩
  intro x
  change φ x ≤ a * u x + b * v x
  calc
    φ x = (a + b) * φ x := by rw [hab, one_mul]
    _ = a * φ x + b * φ x := by ring
    _ ≤ a * u x + b * v x :=
      add_le_add
        (mul_le_mul_of_nonneg_left
          (InLowerPinnedUniformModulusMonotoneTrap.lower hu x) ha)
        (mul_le_mul_of_nonneg_left
          (InLowerPinnedUniformModulusMonotoneTrap.lower hv x) hb)

/-- Adding a closed pointwise lower pin preserves the local-uniform sequential
compactness of the uniform-modulus trap. -/
theorem locallyUniform_sequentiallyCompact
    (hM : 0 ≤ M) (hL : 0 ≤ L) :
    LocalUniformSequentiallyCompactRange
      (InLowerPinnedUniformModulusMonotoneTrap κ M L φ) (fun u => u) := by
  intro seq hseq
  obtain ⟨sub, hsub, g, hg, hconv⟩ :=
    InUniformModulusMonotoneWaveTrap.locallyUniform_sequentiallyCompact
      (κ := κ) hM hL seq (fun n => (hseq n).uniformTrap)
  have hlower : ∀ x, φ x ≤ g x := by
    intro x
    exact le_of_tendsto_of_tendsto tendsto_const_nhds (hconv.tendsto_at x)
      (Eventually.of_forall fun n => (hseq (sub n)).lower x)
  exact ⟨sub, hsub, g, ⟨hg, hlower⟩, hconv⟩

end InLowerPinnedUniformModulusMonotoneTrap

section AxiomAudit

#print axioms InUniformModulusMonotoneWaveTrap.set_convex
#print axioms InUniformModulusMonotoneWaveTrap.locallyUniform_sequentiallyCompact
#print axioms paperTmap_mem_uniformModulusTrap
#print axioms paperTmap_compactRange_of_uniformModulus
#print axioms InLowerPinnedUniformModulusMonotoneTrap.set_convex
#print axioms InLowerPinnedUniformModulusMonotoneTrap.locallyUniform_sequentiallyCompact

end AxiomAudit

end ShenWork.Paper1
