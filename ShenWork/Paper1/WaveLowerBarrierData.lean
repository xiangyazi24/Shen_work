/-
  ShenWork/Paper1/WaveLowerBarrierData.lean

  Lower-barrier interface for the Rothe construction.

  The point of this file is narrow:

  * package the exact lower-barrier data needed by the frozen operator;
  * derive the one-step lower invariant from the dual clean maximum principle;
  * record the paper-hypothesis gap for the advertised lower subsolution.

  No Green-representation comparison is used below; the order step calls
  `implicitStep_ge_of_barrier_maxPrinciple_clean`.
-/
import ShenWork.Paper1.WaveRotheMaxPrincipleClosers
import ShenWork.Paper1.WaveRotheSchauderData

open Filter Topology Set Real

noncomputable section

namespace ShenWork.Paper1

/-- Faithful lower-barrier data.  The final field is the actual frozen
subsolution inequality required by the maximum-principle route; it is not
derived here from informal plateau/tail heuristics. -/
structure LowerBarrierData
    (p : CMParams) (c κ M : ℝ) (φ : ℝ → ℝ) : Prop where
  hM : 0 ≤ M
  hpos : ∀ x, 0 < φ x
  hbarrier : ∀ x, φ x ≤ upperBarrier κ M x
  hcont : Continuous φ
  hC2 : ∀ x, ContDiffAt ℝ 2 φ x
  hsub : ∀ u, InMonotoneWaveTrapSet κ M u →
    ∀ x, 0 ≤ frozenWaveOperator p c u φ x

namespace LowerBarrierData

theorem mem_Icc {p : CMParams} {c κ M : ℝ} {φ : ℝ → ℝ}
    (hφ : LowerBarrierData p c κ M φ) (x : ℝ) :
    φ x ∈ Set.Icc (0 : ℝ) M := by
  constructor
  · exact (hφ.hpos x).le
  · exact le_trans (hφ.hbarrier x) (upperBarrier_le_M κ M x)

end LowerBarrierData

/-- One-step data needed to compare a produced implicit iterate `W` with a lower
barrier `φ`.  This is the lower analogue of `RotheMaxData`, with the step
equation and `C²` regularity supplied by `RotheStepAnalytic`.

The old iterate is `Z`, and `φ ≤ Z` is the inductive lower-bound input. -/
structure LowerBarrierStepData
    (p : CMParams) (c lam M κ Λ C_chem : ℝ)
    (La Lb : ℝ) (u Z W φ : ℝ → ℝ) : Prop where
  hlam : 0 < lam
  step_op : ∀ x, implicitStepOp p c (1 / lam) u W x = Z x
  c2 : ∀ y, ContDiffAt ℝ 2 W y
  hC_chem_nonneg : 0 ≤ C_chem
  hCB : (1 / lam) * (reactionLip p.α M + C_chem) < 1
  AZ : ∀ x, φ x ≤ Z x
  φcont : Continuous (fun x => φ x - W x)
  hbot : Tendsto (fun x => φ x - W x) atBot (𝓝 La)
  hLa : La ≤ 0
  htop : Tendsto (fun x => φ x - W x) atTop (𝓝 Lb)
  hLb : Lb ≤ 0
  range : ∀ x₀, IsMaxOn (fun x => φ x - W x) Set.univ x₀ →
    φ x₀ ∈ Set.Icc (0 : ℝ) M ∧ W x₀ ∈ Set.Icc (0 : ℝ) M
  chem : ∀ x₀, IsMaxOn (fun x => φ x - W x) Set.univ x₀ →
    -p.χ * (deriv (chemFlux p u φ) x₀ - deriv (chemFlux p u W) x₀)
      ≤ C_chem * (φ x₀ - W x₀)

/-- A faithful lower barrier is preserved by one implicit Rothe step, provided
the step supplies the exact max-principle comparison data. -/
theorem lowerBarrier_step_ge_of_data
    {p : CMParams} {c lam M κ Λ C_chem La Lb : ℝ} {u Z W φ : ℝ → ℝ}
    (hφ : LowerBarrierData p c κ M φ)
    (hu : InMonotoneWaveTrapSet κ M u)
    (hd : LowerBarrierStepData p c lam M κ Λ C_chem La Lb u Z W φ) :
    ∀ x, φ x ≤ W x := by
  have hh : 0 < (1 / lam : ℝ) := one_div_pos.mpr hd.hlam
  exact
    implicitStep_ge_of_barrier_maxPrinciple_clean
      (p := p) (c := c) (h := 1 / lam) (M := M) (C_chem := C_chem)
      (u := u) (Z := Z) (W := W) (A := φ) (La := La) (Lb := Lb)
      hh hφ.hM hd.hC_chem_nonneg hd.hCB hd.step_op
      (hφ.hsub u hu) hd.AZ hd.φcont hd.hbot hd.hLa hd.htop hd.hLb
      hd.c2 (fun x₀ _ => hφ.hC2 x₀) hd.range hd.chem

/-- The dual maximum-principle one-step theorem gives the usual inductive lower
invariant for an abstract Rothe orbit, once each step supplies
`LowerBarrierStepData`. -/
theorem rotheStepLowerInvariant_of_lowerBarrierData
    {p : CMParams} {c lam M κ Λ : ℝ} {φ : ℝ → ℝ}
    {rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ}
    (hφ : LowerBarrierData p c κ M φ)
    (hstepData : ∀ u, InLowerPinnedMonotoneTrap κ M φ u →
      ∀ k, (∀ x, φ x ≤ rotheSeq u k x) →
        ∃ C_chem La Lb,
          LowerBarrierStepData p c lam M κ Λ C_chem La Lb u
            (rotheSeq u k) (rotheSeq u (k + 1)) φ) :
    RotheStepLowerInvariant κ M φ rotheSeq := by
  intro u hu k hprev
  obtain ⟨C_chem, La, Lb, hd⟩ := hstepData u hu k hprev
  exact lowerBarrier_step_ge_of_data hφ hu.bare hd

/-- Base case plus per-step lower max-principle data gives a full lower-bounded
Rothe orbit. -/
theorem rotheOrbitLowerBound_of_lowerBarrierData
    {p : CMParams} {c lam M κ Λ : ℝ} {φ : ℝ → ℝ}
    {rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ}
    (hφ : LowerBarrierData p c κ M φ)
    (hbase : ∀ u, InLowerPinnedMonotoneTrap κ M φ u →
      ∀ x, φ x ≤ rotheSeq u 0 x)
    (hstepData : ∀ u, InLowerPinnedMonotoneTrap κ M φ u →
      ∀ k, (∀ x, φ x ≤ rotheSeq u k x) →
        ∃ C_chem La Lb,
          LowerBarrierStepData p c lam M κ Λ C_chem La Lb u
            (rotheSeq u k) (rotheSeq u (k + 1)) φ) :
    RotheOrbitLowerBound κ M φ rotheSeq :=
  rotheOrbitLowerBound_of_stepLowerInvariant hbase
    (rotheStepLowerInvariant_of_lowerBarrierData hφ hstepData)

/-- Paper-operator one-step data for a lower barrier.

The paper subsolution may only be known on a region `s`; the `region` field is
the max-principle side condition saying every positive-max candidate for
`φ - W` lies in that region.  The bridge from the paper operator to the actual
implicit step is `paperDiff`. -/
structure PaperLowerBarrierStepData
    (p : CMParams) (c lam M κ Λ C_chem : ℝ)
    (La Lb : ℝ) (s : Set ℝ) (u Z W φ : ℝ → ℝ) : Prop where
  hlam : 0 < lam
  step_op : ∀ x, implicitStepOp p c (1 / lam) u W x = Z x
  hCB : (1 / lam) * (reactionLip p.α M + C_chem) < 1
  AZ : ∀ x, φ x ≤ Z x
  φcont : Continuous (fun x => φ x - W x)
  hbot : Tendsto (fun x => φ x - W x) atBot (𝓝 La)
  hLa : La ≤ 0
  htop : Tendsto (fun x => φ x - W x) atTop (𝓝 Lb)
  hLb : Lb ≤ 0
  paperSub : IsPaperFrozenSubSolutionOn p c u φ s
  region : ∀ x₀, IsMaxOn (fun x => φ x - W x) Set.univ x₀ → x₀ ∈ s
  paperDiff : ∀ x₀, IsMaxOn (fun x => φ x - W x) Set.univ x₀ →
    paperWaveOperator p c u φ x₀ - frozenWaveOperator p c u W x₀
      ≤ (reactionLip p.α M + C_chem) * (φ x₀ - W x₀)

/-- A paper subsolution lower barrier is preserved by one implicit Rothe step
once the max-principle region and mixed-operator difference estimate are
supplied. -/
theorem lowerBarrier_step_ge_of_paperData
    {p : CMParams} {c lam M κ Λ C_chem La Lb : ℝ}
    {s : Set ℝ} {u Z W φ : ℝ → ℝ}
    (hd : PaperLowerBarrierStepData p c lam M κ Λ C_chem La Lb s u Z W φ) :
    ∀ x, φ x ≤ W x := by
  have hh : 0 < (1 / lam : ℝ) := one_div_pos.mpr hd.hlam
  exact
    implicitStep_ge_of_paperBarrier_maxPrinciple_clean
      (p := p) (c := c) (h := 1 / lam) (M := M) (C_chem := C_chem)
      (u := u) (Z := Z) (W := W) (A := φ) (La := La) (Lb := Lb)
      hh hd.hCB hd.step_op hd.AZ hd.φcont hd.hbot hd.hLa hd.htop hd.hLb
      (fun x₀ hmax => hd.paperSub x₀ (hd.region x₀ hmax))
      hd.paperDiff

/-- Paper-version lower invariant: if each abstract Rothe step supplies the
paper subsolution region data and the mixed paper/frozen difference estimate,
then the lower barrier is inductively preserved. -/
theorem rotheStepLowerInvariant_of_paperBarrierData
    {p : CMParams} {c lam M κ Λ : ℝ} {φ : ℝ → ℝ}
    {rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ}
    (hstepData : ∀ u, InLowerPinnedMonotoneTrap κ M φ u →
      ∀ k, (∀ x, φ x ≤ rotheSeq u k x) →
        ∃ C_chem La Lb s,
          PaperLowerBarrierStepData p c lam M κ Λ C_chem La Lb s u
            (rotheSeq u k) (rotheSeq u (k + 1)) φ) :
    RotheStepLowerInvariant κ M φ rotheSeq := by
  intro u hu k hprev
  obtain ⟨C_chem, La, Lb, s, hd⟩ := hstepData u hu k hprev
  exact lowerBarrier_step_ge_of_paperData hd

/-! ## Faithfulness audit hooks

The theorem statements in Paper1 assume `m, α, γ ≥ 1`; they do not assume
`m > 1`, nor do they include the plateau chemotaxis budget needed for a constant
lower plateau.  The two theorems below make the `m > 1` gap formal.  The final
hook re-exports the existing formal refutation of the original Lemma 4.2 lower
subsolution statement.
-/

theorem paper1_negative_branch_hypotheses_do_not_force_m_gt_one :
    ¬ (∀ p : CMParams, p.χ ≤ 0 → p.α ≤ p.m + p.γ - 1 → 1 < p.m) := by
  intro h
  let p : CMParams :=
    { m := 1
      α := 1
      γ := 1
      χ := -1
      hm := by norm_num
      hα := by norm_num
      hγ := by norm_num }
  have hm_gt := h p (by norm_num [p]) (by norm_num [p])
  norm_num [p] at hm_gt

theorem paper1_positive_branch_hypotheses_do_not_force_m_gt_one :
    ¬ (∀ p : CMParams, 0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
      p.α = p.m + p.γ - 1 → 1 < p.m) := by
  intro h
  let p : CMParams :=
    { m := 1
      α := 1
      γ := 1
      χ := 0
      hm := by norm_num
      hα := by norm_num
      hγ := by norm_num }
  have hχ : p.χ < min (1 / 2 : ℝ) (chiStar p) := by
    exact lt_min (by norm_num [p]) (by simpa [p] using chiStar_pos p)
  have hm_gt := h p (by norm_num [p]) hχ (by norm_num [p])
  norm_num [p] at hm_gt

theorem paper1_lower_subsolution_gap_not_Lemma_4_2 : ¬ Lemma_4_2 :=
  not_Lemma_4_2

/-! ## Axiom audit -/

section AxiomAudit
#print axioms lowerBarrier_step_ge_of_data
#print axioms rotheStepLowerInvariant_of_lowerBarrierData
#print axioms rotheOrbitLowerBound_of_lowerBarrierData
#print axioms lowerBarrier_step_ge_of_paperData
#print axioms rotheStepLowerInvariant_of_paperBarrierData
#print axioms paper1_negative_branch_hypotheses_do_not_force_m_gt_one
#print axioms paper1_positive_branch_hypotheses_do_not_force_m_gt_one
#print axioms paper1_lower_subsolution_gap_not_Lemma_4_2
end AxiomAudit

end ShenWork.Paper1
