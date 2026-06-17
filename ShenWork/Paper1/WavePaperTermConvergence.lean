import ShenWork.Paper1.WaveLemma42Paper

open Filter Topology Real Set

noncomputable section

namespace ShenWork.Paper1

/-!
Paper operator term convergence on compact intervals.

This file keeps the analytic convergence input explicit: once the four
expanded paper-wave terms converge locally uniformly, the whole paper operator
converges locally uniformly.  The input expected from the Green/compactness
layer is exactly `PaperWaveOperatorTermConvergence`.
-/

namespace LocallyUniformConverges

theorem const (f : ℝ → ℝ) :
    LocallyUniformConverges (fun _ => f) f := by
  intro R hR ε hε
  exact Eventually.of_forall fun _ x _ => by simpa using hε

theorem add {fs gs : ℕ → ℝ → ℝ} {f g : ℝ → ℝ}
    (hf : LocallyUniformConverges fs f)
    (hg : LocallyUniformConverges gs g) :
    LocallyUniformConverges (fun n x => fs n x + gs n x)
      (fun x => f x + g x) := by
  intro R hR ε hε
  have hε2 : 0 < ε / 2 := by linarith
  filter_upwards [hf R hR (ε / 2) hε2, hg R hR (ε / 2) hε2] with n hfn hgn
  intro x hx
  have hf' := hfn x hx
  have hg' := hgn x hx
  calc
    |(fs n x + gs n x) - (f x + g x)|
        = |(fs n x - f x) + (gs n x - g x)| := by ring_nf
    _ ≤ |fs n x - f x| + |gs n x - g x| := abs_add_le _ _
    _ < ε := by linarith

theorem neg {fs : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hf : LocallyUniformConverges fs f) :
    LocallyUniformConverges (fun n x => -fs n x) (fun x => -f x) := by
  intro R hR ε hε
  filter_upwards [hf R hR ε hε] with n hn
  intro x hx
  calc
    |-fs n x - -f x| = |-(fs n x - f x)| := by ring_nf
    _ = |fs n x - f x| := abs_neg _
    _ < ε := hn x hx

theorem sub {fs gs : ℕ → ℝ → ℝ} {f g : ℝ → ℝ}
    (hf : LocallyUniformConverges fs f)
    (hg : LocallyUniformConverges gs g) :
    LocallyUniformConverges (fun n x => fs n x - gs n x)
      (fun x => f x - g x) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

theorem const_mul (a : ℝ) {fs : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hf : LocallyUniformConverges fs f) :
    LocallyUniformConverges (fun n x => a * fs n x) (fun x => a * f x) := by
  intro R hR ε hε
  let δ : ℝ := ε / (|a| + 1)
  have hden : 0 < |a| + 1 := by nlinarith [abs_nonneg a]
  have hδ : 0 < δ := div_pos hε hden
  filter_upwards [hf R hR δ hδ] with n hn
  intro x hx
  have hsmall := hn x hx
  have hle : |a| * |fs n x - f x| ≤ |a| * δ :=
    mul_le_mul_of_nonneg_left hsmall.le (abs_nonneg a)
  have hlt : |a| * δ < (|a| + 1) * δ :=
    mul_lt_mul_of_pos_right (by linarith) hδ
  calc
    |a * fs n x - a * f x| = |a| * |fs n x - f x| := by
      rw [← mul_sub, abs_mul]
    _ < (|a| + 1) * δ := lt_of_le_of_lt hle hlt
    _ = ε := by
      unfold δ
      field_simp [ne_of_gt hden]

theorem const_sub {fs : ℕ → ℝ → ℝ} {f : ℝ → ℝ} (a : ℝ)
    (hf : LocallyUniformConverges fs f) :
    LocallyUniformConverges (fun n x => a - fs n x) (fun x => a - f x) := by
  have hconst : LocallyUniformConverges (fun _ x => a) (fun x => a) := by
    intro R hR ε hε
    exact Eventually.of_forall fun _ x _ => by simpa using hε
  exact hconst.sub hf

end LocallyUniformConverges

def LocallyBoundedOnCompacts (f : ℝ → ℝ) : Prop :=
  ∀ R > 0, ∃ B, 0 ≤ B ∧ ∀ x, x ∈ Set.Icc (-R) R → |f x| ≤ B

namespace LocallyBoundedOnCompacts

theorem const (a : ℝ) : LocallyBoundedOnCompacts (fun _ => a) := by
  intro R hR
  exact ⟨|a|, abs_nonneg a, fun _ _ => le_rfl⟩

theorem add {f g : ℝ → ℝ}
    (hf : LocallyBoundedOnCompacts f) (hg : LocallyBoundedOnCompacts g) :
    LocallyBoundedOnCompacts (fun x => f x + g x) := by
  intro R hR
  obtain ⟨Bf, hBf0, hBf⟩ := hf R hR
  obtain ⟨Bg, hBg0, hBg⟩ := hg R hR
  refine ⟨Bf + Bg, by linarith, ?_⟩
  intro x hx
  calc
    |f x + g x| ≤ |f x| + |g x| := abs_add_le _ _
    _ ≤ Bf + Bg := add_le_add (hBf x hx) (hBg x hx)

theorem neg {f : ℝ → ℝ} (hf : LocallyBoundedOnCompacts f) :
    LocallyBoundedOnCompacts (fun x => -f x) := by
  intro R hR
  obtain ⟨B, hB0, hB⟩ := hf R hR
  exact ⟨B, hB0, fun x hx => by simpa using hB x hx⟩

theorem sub {f g : ℝ → ℝ}
    (hf : LocallyBoundedOnCompacts f) (hg : LocallyBoundedOnCompacts g) :
    LocallyBoundedOnCompacts (fun x => f x - g x) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

theorem const_mul (a : ℝ) {f : ℝ → ℝ}
    (hf : LocallyBoundedOnCompacts f) :
    LocallyBoundedOnCompacts (fun x => a * f x) := by
  intro R hR
  obtain ⟨B, hB0, hB⟩ := hf R hR
  refine ⟨|a| * B, mul_nonneg (abs_nonneg a) hB0, ?_⟩
  intro x hx
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hB x hx) (abs_nonneg a)

theorem mul {f g : ℝ → ℝ}
    (hf : LocallyBoundedOnCompacts f) (hg : LocallyBoundedOnCompacts g) :
    LocallyBoundedOnCompacts (fun x => f x * g x) := by
  intro R hR
  obtain ⟨Bf, hBf0, hBf⟩ := hf R hR
  obtain ⟨Bg, hBg0, hBg⟩ := hg R hR
  refine ⟨Bf * Bg, mul_nonneg hBf0 hBg0, ?_⟩
  intro x hx
  rw [abs_mul]
  exact mul_le_mul (hBf x hx) (hBg x hx) (abs_nonneg _) hBf0

theorem const_sub (a : ℝ) {f : ℝ → ℝ}
    (hf : LocallyBoundedOnCompacts f) :
    LocallyBoundedOnCompacts (fun x => a - f x) := by
  exact (LocallyBoundedOnCompacts.const a).sub hf

end LocallyBoundedOnCompacts

namespace LocallyUniformConverges

theorem mul {fs gs : ℕ → ℝ → ℝ} {f g : ℝ → ℝ}
    (hf : LocallyUniformConverges fs f)
    (hg : LocallyUniformConverges gs g)
    (hfb : LocallyBoundedOnCompacts f)
    (hgb : LocallyBoundedOnCompacts g) :
    LocallyUniformConverges (fun n x => fs n x * gs n x)
      (fun x => f x * g x) := by
  intro R hR ε hε
  obtain ⟨Bf, hBf0, hBf⟩ := hfb R hR
  obtain ⟨Bg, hBg0, hBg⟩ := hgb R hR
  let δ : ℝ := ε / (2 * (Bg + Bf + 1))
  have hden : 0 < 2 * (Bg + Bf + 1) := by nlinarith
  have hδ : 0 < δ := div_pos hε hden
  filter_upwards [hf R hR δ hδ, hg R hR δ hδ, hg R hR 1 zero_lt_one]
    with n hfn hgn hg1
  intro x hx
  have hfsmall := hfn x hx
  have hgsmall := hgn x hx
  have hgsmall1 := hg1 x hx
  have hgs_bound : |gs n x| ≤ Bg + 1 := by
    calc
      |gs n x| = |g x + (gs n x - g x)| := by ring_nf
      _ ≤ |g x| + |gs n x - g x| := abs_add_le _ _
      _ ≤ Bg + 1 := by linarith [hBg x hx, hgsmall1.le]
  have hmain :
      |fs n x * gs n x - f x * g x|
        ≤ |fs n x - f x| * |gs n x| + |f x| * |gs n x - g x| := by
    calc
      |fs n x * gs n x - f x * g x|
          = |(fs n x - f x) * gs n x + f x * (gs n x - g x)| := by ring_nf
      _ ≤ |(fs n x - f x) * gs n x| + |f x * (gs n x - g x)| :=
        abs_add_le _ _
      _ = |fs n x - f x| * |gs n x| + |f x| * |gs n x - g x| := by
        rw [abs_mul, abs_mul]
  have hterm₁ :
      |fs n x - f x| * |gs n x| ≤ δ * (Bg + 1) :=
    mul_le_mul hfsmall.le hgs_bound (abs_nonneg _) hδ.le
  have hterm₂ : |f x| * |gs n x - g x| ≤ Bf * δ :=
    mul_le_mul (hBf x hx) hgsmall.le (abs_nonneg _) hBf0
  have hsum :
      δ * (Bg + 1) + Bf * δ ≤ δ * (Bg + Bf + 1) := by
    ring_nf
    exact le_rfl
  calc
    |fs n x * gs n x - f x * g x|
        ≤ |fs n x - f x| * |gs n x| + |f x| * |gs n x - g x| := hmain
    _ ≤ δ * (Bg + 1) + Bf * δ := add_le_add hterm₁ hterm₂
    _ ≤ δ * (Bg + Bf + 1) := hsum
    _ < ε := by
      unfold δ
      have hpos : 0 < Bg + Bf + 1 := by nlinarith
      field_simp [ne_of_gt hden]
      nlinarith

end LocallyUniformConverges

def paperWaveD2Term (W : ℝ → ℝ) : ℝ → ℝ :=
  fun x => iteratedDeriv 2 W x

def paperWaveDriftTerm (c : ℝ) (W : ℝ → ℝ) : ℝ → ℝ :=
  fun x => c * deriv W x

def paperWaveChemCore (p : CMParams) (u W : ℝ → ℝ) : ℝ → ℝ :=
  fun x =>
    (W x) ^ (p.m - 1) * (deriv (frozenElliptic p u) x * deriv W x)

def paperWaveChemTerm (p : CMParams) (u W : ℝ → ℝ) : ℝ → ℝ :=
  fun x => -(p.χ * p.m * paperWaveChemCore p u W x)

def paperWaveReactionBracket (p : CMParams) (u W : ℝ → ℝ) : ℝ → ℝ :=
  fun x =>
    1 - p.χ * ((W x) ^ (p.m - 1) * frozenElliptic p u x)
      - ((W x) ^ p.α - p.χ * (W x) ^ (p.m + p.γ - 1))

def paperWaveReactionTerm (p : CMParams) (u W : ℝ → ℝ) : ℝ → ℝ :=
  fun x => W x * paperWaveReactionBracket p u W x

theorem paperWaveOperator_eq_terms
    (p : CMParams) (c : ℝ) (u W : ℝ → ℝ) :
    paperWaveOperator p c u W =
      fun x =>
        paperWaveD2Term W x + paperWaveDriftTerm c W x
          + paperWaveChemTerm p u W x + paperWaveReactionTerm p u W x := by
  funext x
  unfold paperWaveOperator paperWaveD2Term paperWaveDriftTerm
    paperWaveChemTerm paperWaveChemCore paperWaveReactionTerm
    paperWaveReactionBracket
  ring_nf

structure PaperC2CompactConvergence
    (p : CMParams) (U : ℝ → ℝ) (z : ℕ → ℝ → ℝ) : Prop where
  value :
    LocallyUniformConverges (fun k => z (k + 1)) U
  deriv1 :
    LocallyUniformConverges
      (fun k x => deriv (z (k + 1)) x)
      (fun x => deriv U x)
  deriv2 :
    LocallyUniformConverges
      (fun k x => iteratedDeriv 2 (z (k + 1)) x)
      (fun x => iteratedDeriv 2 U x)
  pow_m_sub_one :
    LocallyUniformConverges
      (fun k x => (z (k + 1) x) ^ (p.m - 1))
      (fun x => (U x) ^ (p.m - 1))
  pow_alpha :
    LocallyUniformConverges
      (fun k x => (z (k + 1) x) ^ p.α)
      (fun x => (U x) ^ p.α)
  pow_m_gamma_sub_one :
    LocallyUniformConverges
      (fun k x => (z (k + 1) x) ^ (p.m + p.γ - 1))
      (fun x => (U x) ^ (p.m + p.γ - 1))
  bdd_U : LocallyBoundedOnCompacts U
  bdd_derivU : LocallyBoundedOnCompacts (fun x => deriv U x)
  bdd_V : LocallyBoundedOnCompacts (frozenElliptic p U)
  bdd_derivV : LocallyBoundedOnCompacts (fun x => deriv (frozenElliptic p U) x)
  bdd_pow_m_sub_one :
    LocallyBoundedOnCompacts (fun x => (U x) ^ (p.m - 1))
  bdd_reaction_bracket :
    LocallyBoundedOnCompacts (paperWaveReactionBracket p U U)

structure PaperWaveOperatorTermConvergence
    (p : CMParams) (c : ℝ) (U : ℝ → ℝ) (z : ℕ → ℝ → ℝ) : Prop where
  d2 :
    LocallyUniformConverges
      (fun k => paperWaveD2Term (z (k + 1)))
      (paperWaveD2Term U)
  drift :
    LocallyUniformConverges
      (fun k => paperWaveDriftTerm c (z (k + 1)))
      (paperWaveDriftTerm c U)
  chem :
    LocallyUniformConverges
      (fun k => paperWaveChemTerm p U (z (k + 1)))
      (paperWaveChemTerm p U U)
  reaction :
    LocallyUniformConverges
      (fun k => paperWaveReactionTerm p U (z (k + 1)))
      (paperWaveReactionTerm p U U)

namespace PaperC2CompactConvergence

theorem termConvergence
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ} {z : ℕ → ℝ → ℝ}
    (h : PaperC2CompactConvergence p U z) :
    PaperWaveOperatorTermConvergence p c U z := by
  have hV : LocallyUniformConverges
      (fun _ => frozenElliptic p U) (frozenElliptic p U) :=
    LocallyUniformConverges.const _
  have hVd : LocallyUniformConverges
      (fun _ x => deriv (frozenElliptic p U) x)
      (fun x => deriv (frozenElliptic p U) x) :=
    LocallyUniformConverges.const _
  have hpowVd :
      LocallyUniformConverges
        (fun k x =>
          (z (k + 1) x) ^ (p.m - 1) * deriv (frozenElliptic p U) x)
        (fun x => (U x) ^ (p.m - 1) * deriv (frozenElliptic p U) x) :=
    h.pow_m_sub_one.mul hVd h.bdd_pow_m_sub_one h.bdd_derivV
  have hbdd_powVd :
      LocallyBoundedOnCompacts
        (fun x => (U x) ^ (p.m - 1) * deriv (frozenElliptic p U) x) :=
    h.bdd_pow_m_sub_one.mul h.bdd_derivV
  have hchemCore :
      LocallyUniformConverges
        (fun k => paperWaveChemCore p U (z (k + 1)))
        (paperWaveChemCore p U U) := by
    have hmul := hpowVd.mul h.deriv1 hbdd_powVd h.bdd_derivU
    simpa [paperWaveChemCore, mul_assoc] using hmul
  have hchem :
      LocallyUniformConverges
        (fun k => paperWaveChemTerm p U (z (k + 1)))
        (paperWaveChemTerm p U U) := by
    simpa [paperWaveChemTerm] using hchemCore.const_mul (-p.χ * p.m)
  have hpowV :
      LocallyUniformConverges
        (fun k x => (z (k + 1) x) ^ (p.m - 1) * frozenElliptic p U x)
        (fun x => (U x) ^ (p.m - 1) * frozenElliptic p U x) :=
    h.pow_m_sub_one.mul hV h.bdd_pow_m_sub_one h.bdd_V
  have hχpowV :
      LocallyUniformConverges
        (fun k x =>
          p.χ * ((z (k + 1) x) ^ (p.m - 1) * frozenElliptic p U x))
        (fun x => p.χ * ((U x) ^ (p.m - 1) * frozenElliptic p U x)) :=
    hpowV.const_mul p.χ
  have hleft :
      LocallyUniformConverges
        (fun k x =>
          1 - p.χ * ((z (k + 1) x) ^ (p.m - 1) * frozenElliptic p U x))
        (fun x => 1 - p.χ * ((U x) ^ (p.m - 1) * frozenElliptic p U x)) :=
    hχpowV.const_sub 1
  have hχpowMG :
      LocallyUniformConverges
        (fun k x => p.χ * (z (k + 1) x) ^ (p.m + p.γ - 1))
        (fun x => p.χ * (U x) ^ (p.m + p.γ - 1)) :=
    h.pow_m_gamma_sub_one.const_mul p.χ
  have hright :
      LocallyUniformConverges
        (fun k x =>
          (z (k + 1) x) ^ p.α
            - p.χ * (z (k + 1) x) ^ (p.m + p.γ - 1))
        (fun x => (U x) ^ p.α - p.χ * (U x) ^ (p.m + p.γ - 1)) :=
    h.pow_alpha.sub hχpowMG
  have hbracket :
      LocallyUniformConverges
        (fun k => paperWaveReactionBracket p U (z (k + 1)))
        (paperWaveReactionBracket p U U) := by
    have hsub := hleft.sub hright
    simpa [paperWaveReactionBracket, mul_assoc] using hsub
  have hreaction :
      LocallyUniformConverges
        (fun k => paperWaveReactionTerm p U (z (k + 1)))
        (paperWaveReactionTerm p U U) := by
    have hmul := h.value.mul hbracket h.bdd_U h.bdd_reaction_bracket
    simpa [paperWaveReactionTerm] using hmul
  exact
    { d2 := by simpa [paperWaveD2Term] using h.deriv2
      drift := by
        simpa [paperWaveDriftTerm] using h.deriv1.const_mul c
      chem := hchem
      reaction := hreaction }

#print axioms PaperC2CompactConvergence.termConvergence

end PaperC2CompactConvergence

namespace PaperWaveOperatorTermConvergence

theorem of_c2CompactConvergence
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ} {z : ℕ → ℝ → ℝ}
    (h : PaperC2CompactConvergence p U z) :
    PaperWaveOperatorTermConvergence p c U z :=
  h.termConvergence

theorem operator
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ} {z : ℕ → ℝ → ℝ}
    (h : PaperWaveOperatorTermConvergence p c U z) :
    LocallyUniformConverges
      (fun k => paperWaveOperator p c U (z (k + 1)))
      (paperWaveOperator p c U U) := by
  let termSeq : ℕ → ℝ → ℝ := fun k x =>
    paperWaveD2Term (z (k + 1)) x + paperWaveDriftTerm c (z (k + 1)) x
      + paperWaveChemTerm p U (z (k + 1)) x
      + paperWaveReactionTerm p U (z (k + 1)) x
  have hsum := (h.d2.add h.drift).add h.chem |>.add h.reaction
  have hsame :
      ∀ᶠ k in atTop,
        termSeq k = paperWaveOperator p c U (z (k + 1)) := by
    exact Eventually.of_forall fun k => by
      funext x
      rw [paperWaveOperator_eq_terms]
  have hterm :
      LocallyUniformConverges termSeq (paperWaveOperator p c U U) := by
    simpa [termSeq, paperWaveOperator_eq_terms] using hsum
  exact LocallyUniformConverges.congr hsame hterm

#print axioms LocallyUniformConverges.add
#print axioms LocallyUniformConverges.const_mul
#print axioms paperWaveOperator_eq_terms
#print axioms PaperWaveOperatorTermConvergence.of_c2CompactConvergence
#print axioms PaperWaveOperatorTermConvergence.operator

end PaperWaveOperatorTermConvergence

end ShenWork.Paper1
