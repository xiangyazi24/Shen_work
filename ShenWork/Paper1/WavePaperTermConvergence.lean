import ShenWork.Paper1.WaveLemma42Paper
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Filter Topology MeasureTheory Real Set

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

theorem tendstoLocallyUniformlyOn_univ
    {fs : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (h : LocallyUniformConverges fs f) :
    TendstoLocallyUniformlyOn fs f atTop (Set.univ : Set ℝ) := by
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε x _hx
  let R : ℝ := |x| + 1
  have hR : 0 < R := by
    dsimp [R]
    nlinarith [abs_nonneg x]
  refine ⟨Metric.ball x 1, ?_, ?_⟩
  · simpa [nhdsWithin_univ] using Metric.ball_mem_nhds x zero_lt_one
  filter_upwards [h R hR ε hε] with n hn
  intro y hy
  have hy_dist : |y - x| < 1 := by
    simpa [Real.dist_eq] using hy
  have hy_abs_lt : |y| < R := by
    have htri : |y| ≤ |y - x| + |x| := by
      calc
        |y| = |(y - x) + x| := by ring_nf
        _ ≤ |y - x| + |x| := abs_add_le _ _
    calc
      |y| ≤ |y - x| + |x| := htri
      _ < 1 + |x| := by linarith
      _ = R := by ring
  have hyR : y ∈ Set.Icc (-R) R := abs_le.mp hy_abs_lt.le
  simpa [Real.dist_eq, abs_sub_comm] using hn y hyR

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

theorem paperStepSource_eq_terms
    (p : CMParams) (c lam : ℝ) (u Z W : ℝ → ℝ) :
    paperStepSource p c lam u Z W =
      fun x =>
        paperWaveChemTerm p u W x + paperWaveReactionTerm p u W x +
          lam * Z x := by
  funext x
  unfold paperStepSource paperStepNonlinearity paperWaveChemTerm
    paperWaveChemCore paperWaveReactionTerm paperWaveReactionBracket
  ring_nf

theorem paperStepSource_self_eq_crossSource
    {p : CMParams} {c lam : ℝ} {U : ℝ → ℝ}
    (hU_cunif : IsCUnifBdd U)
    (hU_nonneg : ∀ x, 0 ≤ U x)
    (hU_deriv : ∀ x, HasDerivAt U (deriv U x) x) :
    paperStepSource p c lam U U U = crossSource p lam U U U := by
  funext x
  have hU_pow_deriv : HasDerivAt (fun y => (U y) ^ p.m)
      (deriv U x * p.m * (U x) ^ (p.m - 1)) x :=
    (hU_deriv x).rpow_const (Or.inr p.hm)
  have hV'' := frozenElliptic_deriv_deriv_eq p hU_cunif hU_nonneg x
  have hV_deriv : HasDerivAt (deriv (frozenElliptic p U))
      (frozenElliptic p U x - (U x) ^ p.γ) x := by
    convert (frozenElliptic_deriv_differentiableAt p
      hU_cunif hU_nonneg x).hasDerivAt using 1
    exact hV''.symm
  have hprod := hU_pow_deriv.mul hV_deriv
  have hflux_deriv :
      deriv (fun t => (U t) ^ p.m * deriv (frozenElliptic p U) t) x =
        deriv U x * p.m * (U x) ^ (p.m - 1) *
            deriv (frozenElliptic p U) x +
          (U x) ^ p.m * (frozenElliptic p U x - (U x) ^ p.γ) := by
    have hfun_eq :
        (fun t => (U t) ^ p.m * deriv (frozenElliptic p U) t) =
          (fun t => (U t) ^ p.m) * deriv (frozenElliptic p U) := by
      ext t
      simp [Pi.mul_apply]
    rw [hfun_eq]
    exact hprod.deriv
  have hpow_m : U x * (U x) ^ (p.m - 1) = (U x) ^ p.m :=
    mul_rpow_sub_one p.m p.hm (hU_nonneg x)
  have hpow_m' : (U x) ^ (p.m - 1) * U x = (U x) ^ p.m := by
    rw [mul_comm, hpow_m]
  have hmg : 1 ≤ p.m + p.γ := by linarith [p.hm, p.hγ]
  have hpow_mγ_sum :
      U x * (U x) ^ (p.m + p.γ - 1) = (U x) ^ (p.m + p.γ) :=
    mul_rpow_sub_one (p.m + p.γ) hmg (hU_nonneg x)
  have hpow_add :
      (U x) ^ (p.m + p.γ) = (U x) ^ p.m * (U x) ^ p.γ := by
    by_cases hx : U x = 0
    · have hm_pos : 0 < p.m := lt_of_lt_of_le zero_lt_one p.hm
      have hγ_pos : 0 < p.γ := lt_of_lt_of_le zero_lt_one p.hγ
      have hsum_pos : 0 < p.m + p.γ := by linarith
      simp [hx, ne_of_gt hm_pos, ne_of_gt hγ_pos, ne_of_gt hsum_pos]
    · have hxpos : 0 < U x :=
        lt_of_le_of_ne (hU_nonneg x) (fun h0 => hx h0.symm)
      rw [← Real.rpow_add hxpos]
  have hpow_mγ :
      U x * (U x) ^ (p.m + p.γ - 1) =
        (U x) ^ p.m * (U x) ^ p.γ := by
    rw [hpow_mγ_sum, hpow_add]
  have hpow_mγ' :
      (U x) ^ (p.m + p.γ - 1) * U x =
        (U x) ^ p.m * (U x) ^ p.γ := by
    rw [mul_comm, hpow_mγ]
  have hpow_m_nf :
      (U x) ^ (-1 + p.m) * U x = (U x) ^ p.m := by
    convert hpow_m' using 2
    ring
  have hpow_mγ_nf :
      U x * (U x) ^ (-1 + p.m + p.γ) =
        (U x) ^ p.m * (U x) ^ p.γ := by
    convert hpow_mγ using 2
    ring
  have hterm_m :
      p.χ * (U x) ^ (-1 + p.m) * U x * frozenElliptic p U x =
        p.χ * frozenElliptic p U x * (U x) ^ p.m := by
    rw [mul_assoc p.χ ((U x) ^ (-1 + p.m)) (U x), hpow_m_nf]
    ring
  have hterm_mγ :
      p.χ * U x * (U x) ^ (-1 + p.m + p.γ) =
        p.χ * ((U x) ^ p.m * (U x) ^ p.γ) := by
    calc
      p.χ * U x * (U x) ^ (-1 + p.m + p.γ)
          = p.χ * (U x * (U x) ^ (-1 + p.m + p.γ)) := by ring
      _ = p.χ * ((U x) ^ p.m * (U x) ^ p.γ) := by
        rw [hpow_mγ_nf]
  unfold paperStepSource paperStepNonlinearity crossSource reactionFun
  rw [hflux_deriv]
  ring_nf
  rw [hterm_m, hterm_mγ]
  ring

/-- Uniform local Lipschitz control of a sequence on compact intervals. -/
def UniformLipschitzOnCompacts (fs : ℕ → ℝ → ℝ) : Prop :=
  ∀ R > 0, ∃ L, 0 ≤ L ∧
    ∀ n x y, x ∈ Set.Icc (-R) R → y ∈ Set.Icc (-R) R →
      |fs n x - fs n y| ≤ L * |x - y|

/-- Local Lipschitz control of one function on compact intervals. -/
def LipschitzOnCompacts (f : ℝ → ℝ) : Prop :=
  ∀ R > 0, ∃ L, 0 ≤ L ∧
    ∀ x y, x ∈ Set.Icc (-R) R → y ∈ Set.Icc (-R) R →
      |f x - f y| ≤ L * |x - y|

namespace LocallyBoundedOnCompacts

theorem of_global_bound {f : ℝ → ℝ} {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ x, |f x| ≤ B) :
    LocallyBoundedOnCompacts f := by
  intro R hR
  exact ⟨B, hB0, fun x _ => hB x⟩

end LocallyBoundedOnCompacts

namespace UniformLipschitzOnCompacts

theorem of_global {fs : ℕ → ℝ → ℝ} {L : ℝ}
    (hL0 : 0 ≤ L)
    (hLip : ∀ n x y, |fs n x - fs n y| ≤ L * |x - y|) :
    UniformLipschitzOnCompacts fs := by
  intro R hR
  exact ⟨L, hL0, fun n x y _ _ => hLip n x y⟩

theorem of_hasDerivAt_bound {fs dfs : ℕ → ℝ → ℝ} {L : ℝ}
    (hL0 : 0 ≤ L)
    (hderiv : ∀ n x, HasDerivAt (fs n) (dfs n x) x)
    (hbound : ∀ n x, |dfs n x| ≤ L) :
    UniformLipschitzOnCompacts fs := by
  refine of_global hL0 ?_
  intro n x y
  have hdiff : Differentiable ℝ (fs n) := fun t => (hderiv n t).differentiableAt
  have hderiv_bound : ∀ t, |deriv (fs n) t| ≤ L := by
    intro t
    rw [(hderiv n t).deriv]
    exact hbound n t
  have hLip : LipschitzWith (Real.toNNReal L) (fs n) :=
    crossImplicitStep_lipschitz hL0 hdiff hderiv_bound
  have hd := hLip.dist_le_mul x y
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hL0] at hd
  exact hd

end UniformLipschitzOnCompacts

namespace LipschitzOnCompacts

theorem of_global {f : ℝ → ℝ} {L : ℝ}
    (hL0 : 0 ≤ L)
    (hLip : ∀ x y, |f x - f y| ≤ L * |x - y|) :
    LipschitzOnCompacts f := by
  intro R hR
  exact ⟨L, hL0, fun x y _ _ => hLip x y⟩

theorem of_hasDerivAt_bound {f df : ℝ → ℝ} {L : ℝ}
    (hL0 : 0 ≤ L)
    (hderiv : ∀ x, HasDerivAt f (df x) x)
    (hbound : ∀ x, |df x| ≤ L) :
    LipschitzOnCompacts f := by
  refine of_global hL0 ?_
  intro x y
  have hdiff : Differentiable ℝ f := fun t => (hderiv t).differentiableAt
  have hderiv_bound : ∀ t, |deriv f t| ≤ L := by
    intro t
    rw [(hderiv t).deriv]
    exact hbound t
  have hLip : LipschitzWith (Real.toNNReal L) f :=
    crossImplicitStep_lipschitz hL0 hdiff hderiv_bound
  have hd := hLip.dist_le_mul x y
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hL0] at hd
  exact hd

end LipschitzOnCompacts

namespace LocallyUniformConverges

theorem rpow_of_nonneg_le
    {fs : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {a M : ℝ}
    (ha : 0 ≤ a) (_hM : 0 ≤ M)
    (h : LocallyUniformConverges fs f)
    (hfs0 : ∀ n x, 0 ≤ fs n x) (hfsM : ∀ n x, fs n x ≤ M)
    (hf0 : ∀ x, 0 ≤ f x) (hfM : ∀ x, f x ≤ M) :
    LocallyUniformConverges
      (fun n x => (fs n x) ^ a) (fun x => (f x) ^ a) := by
  intro R hR ε hε
  have hcont : Continuous (fun s : ℝ => s ^ a) :=
    Real.continuous_rpow_const ha
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous
    (s := Set.Icc (0 : ℝ) M) hcont.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδpow⟩ := huc ε hε
  filter_upwards [h R hR δ hδ] with n hn
  intro x hx
  have hfs_mem : fs n x ∈ Set.Icc (0 : ℝ) M :=
    ⟨hfs0 n x, hfsM n x⟩
  have hf_mem : f x ∈ Set.Icc (0 : ℝ) M :=
    ⟨hf0 x, hfM x⟩
  have hdist : dist (fs n x) (f x) < δ := by
    simpa [Real.dist_eq] using hn x hx
  have hpow := hδpow (fs n x) hfs_mem (f x) hf_mem hdist
  simpa [Real.dist_eq] using hpow

end LocallyUniformConverges

/-- Uniform local Lipschitz control of the residual `fs n - f`.  This is the
compact Green/ODE regularity input used by the interpolation step; it is not a
convergence hypothesis. -/
def UniformResidualLipschitzOnCompacts
    (fs : ℕ → ℝ → ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ R > 0, ∃ L, 0 ≤ L ∧
    ∀ n x y, x ∈ Set.Icc (-R) R → y ∈ Set.Icc (-R) R →
      |(fs n x - f x) - (fs n y - f y)| ≤ L * |x - y|

theorem UniformResidualLipschitzOnCompacts.of_pair
    {fs : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hfs : UniformLipschitzOnCompacts fs)
    (hf : LipschitzOnCompacts f) :
    UniformResidualLipschitzOnCompacts fs f := by
  intro R hR
  obtain ⟨Lf, hLf0, hLf⟩ := hfs R hR
  obtain ⟨Lg, hLg0, hLg⟩ := hf R hR
  refine ⟨Lf + Lg, by linarith, ?_⟩
  intro n x y hx hy
  have htri :
      |(fs n x - f x) - (fs n y - f y)|
        ≤ |fs n x - fs n y| + |f x - f y| := by
    calc
      |(fs n x - f x) - (fs n y - f y)|
          = |(fs n x - fs n y) + -(f x - f y)| := by ring_nf
      _ ≤ |fs n x - fs n y| + |-(f x - f y)| :=
        abs_add_le _ _
      _ = |fs n x - fs n y| + |f x - f y| := by rw [abs_neg]
  calc
    |(fs n x - f x) - (fs n y - f y)|
        ≤ |fs n x - fs n y| + |f x - f y| := htri
    _ ≤ Lf * |x - y| + Lg * |x - y| :=
      add_le_add (hLf n x y hx hy) (hLg x y hx hy)
    _ = (Lf + Lg) * |x - y| := by ring

namespace LocallyUniformConverges

/-- Interpolation upgrade on compact intervals.

If `fs n → f` locally uniformly and the derivative residuals `dfs n - df` are
uniformly locally Lipschitz, then the derivatives converge locally uniformly.
This is the one-dimensional resolvent/Green compactness step: a short-interval
MVT slope controls the derivative error by the zeroth-order error plus the
residual Lipschitz constant. -/
theorem deriv_of_hasDerivAt_of_residual_lipschitz
    {fs dfs : ℕ → ℝ → ℝ} {f df : ℝ → ℝ}
    (hval : LocallyUniformConverges fs f)
    (hfs : ∀ n x, HasDerivAt (fs n) (dfs n x) x)
    (hf : ∀ x, HasDerivAt f (df x) x)
    (hlip : UniformResidualLipschitzOnCompacts dfs df) :
    LocallyUniformConverges dfs df := by
  intro R hR ε hε
  let S : ℝ := R + 1
  have hS : 0 < S := by dsimp [S]; linarith
  obtain ⟨L, hL0, hLip⟩ := hlip S hS
  let t : ℝ := min 1 (ε / (4 * (L + 1)))
  have hden : 0 < 4 * (L + 1) := by nlinarith
  have ht_pos : 0 < t := by
    dsimp [t]
    exact lt_min zero_lt_one (div_pos hε hden)
  have ht_le_one : t ≤ 1 := by
    dsimp [t]
    exact min_le_left _ _
  have ht_le_eps : t ≤ ε / (4 * (L + 1)) := by
    dsimp [t]
    exact min_le_right _ _
  have hLt_le : L * t ≤ ε / 4 := by
    have hLle : L ≤ L + 1 := by linarith
    have hnonneg_t : 0 ≤ t := ht_pos.le
    calc
      L * t ≤ (L + 1) * t :=
        mul_le_mul_of_nonneg_right hLle hnonneg_t
      _ ≤ (L + 1) * (ε / (4 * (L + 1))) :=
        mul_le_mul_of_nonneg_left ht_le_eps (by linarith)
      _ = ε / 4 := by
        have hLp : L + 1 ≠ 0 := ne_of_gt (by linarith : 0 < L + 1)
        field_simp [hLp]
  let δ : ℝ := ε * t / 4
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  filter_upwards [hval S hS δ hδ] with n hn
  intro x hx
  have hxS : x ∈ Set.Icc (-S) S := by
    constructor
    · dsimp [S] at *
      linarith [hx.1]
    · dsimp [S] at *
      linarith [hx.2]
  have hxtS : x + t ∈ Set.Icc (-S) S := by
    constructor
    · dsimp [S] at *
      linarith [hx.1, ht_pos]
    · dsimp [S] at *
      linarith [hx.2, ht_le_one]
  have hsmall_x : |fs n x - f x| < δ := hn x hxS
  have hsmall_xt : |fs n (x + t) - f (x + t)| < δ := hn (x + t) hxtS
  let e : ℝ → ℝ := fun y => fs n y - f y
  have hcont : Continuous e := by
    refine continuous_iff_continuousAt.mpr ?_
    intro y
    exact ((hfs n y).sub (hf y)).continuousAt
  have hderiv : ∀ y ∈ Set.Ioo x (x + t),
      HasDerivAt e (dfs n y - df y) y := by
    intro y _hy
    exact (hfs n y).sub (hf y)
  obtain ⟨ξ, hξ, hξeq⟩ :=
    exists_hasDerivAt_eq_slope e (fun y => dfs n y - df y)
      (by linarith : x < x + t) hcont.continuousOn hderiv
  have hξS : ξ ∈ Set.Icc (-S) S := by
    constructor
    · dsimp [S] at *
      linarith [hx.1, hξ.1]
    · dsimp [S] at *
      linarith [hx.2, ht_le_one, hξ.2]
  have hxξ_abs : |x - ξ| ≤ t := by
    have hnonpos : x - ξ ≤ 0 := by linarith [hξ.1]
    have hdist : |x - ξ| = ξ - x := by
      rw [abs_of_nonpos hnonpos]
      ring
    rw [hdist]
    linarith [hξ.2]
  have hres_lip :
      |(dfs n x - df x) - (dfs n ξ - df ξ)| ≤ L * t := by
    calc
      |(dfs n x - df x) - (dfs n ξ - df ξ)|
          ≤ L * |x - ξ| := hLip n x ξ hxS hξS
      _ ≤ L * t := mul_le_mul_of_nonneg_left hxξ_abs hL0
  have hres_lip_eps :
      |(dfs n x - df x) - (dfs n ξ - df ξ)| ≤ ε / 4 :=
    le_trans hres_lip hLt_le
  have hξeq_t :
      dfs n ξ - df ξ =
        ((fs n (x + t) - f (x + t)) - (fs n x - f x)) / t := by
    simpa [e, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hξeq
  have hslope_lt : |dfs n ξ - df ξ| < ε / 2 := by
    rw [hξeq_t]
    have hnum :
        |(fs n (x + t) - f (x + t)) - (fs n x - f x)| < 2 * δ := by
      calc
        |(fs n (x + t) - f (x + t)) - (fs n x - f x)|
            = |(fs n (x + t) - f (x + t)) + -(fs n x - f x)| := by
          ring_nf
        _ ≤ |fs n (x + t) - f (x + t)| + |-(fs n x - f x)| :=
          abs_add_le _ _
        _ = |fs n (x + t) - f (x + t)| + |fs n x - f x| := by
          rw [abs_neg]
        _ < δ + δ := add_lt_add hsmall_xt hsmall_x
        _ = 2 * δ := by ring
    have ht_abs : |t| = t := abs_of_pos ht_pos
    calc
      |((fs n (x + t) - f (x + t)) - (fs n x - f x)) / t|
          = |(fs n (x + t) - f (x + t)) - (fs n x - f x)| / t := by
        rw [abs_div, ht_abs]
      _ < (2 * δ) / t := div_lt_div_of_pos_right hnum ht_pos
      _ = ε / 2 := by
        dsimp [δ]
        field_simp [ne_of_gt ht_pos]
        ring
  have hsplit :
      dfs n x - df x =
        ((dfs n x - df x) - (dfs n ξ - df ξ)) + (dfs n ξ - df ξ) := by
    ring
  calc
    |dfs n x - df x|
        = |((dfs n x - df x) - (dfs n ξ - df ξ)) + (dfs n ξ - df ξ)| := by
          exact congrArg abs hsplit
    _ ≤ |(dfs n x - df x) - (dfs n ξ - df ξ)| + |dfs n ξ - df ξ| :=
      abs_add_le _ _
    _ < ε := by linarith

end LocallyUniformConverges

structure PaperC2CompactConvergence
    (p : CMParams) (U : ℝ → ℝ) (z : ℕ → ℝ → ℝ) : Prop where
  step_hasDeriv_value :
    ∀ k x, HasDerivAt (z (k + 1)) (deriv (z (k + 1)) x) x
  step_hasDeriv_deriv :
    ∀ k x,
      HasDerivAt (fun y => deriv (z (k + 1)) y)
        (iteratedDeriv 2 (z (k + 1)) x) x
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

/-- Uniform Green/ODE compactness data sufficient to upgrade zeroth-order
local-uniform convergence of a Rothe orbit to `C²` compact convergence.

The first-derivative convergence is produced by
`paperC2CompactConvergence_of_uniformBounds` from zeroth-order convergence and
the uniform C² bound.  The second-derivative convergence is supplied by the
Green/ODE source thread, avoiding any hidden C³ requirement.  The remaining
fields are the algebraic power continuity and local boundedness data already
needed by the paper operator terms. -/
structure PaperC2CompactUniformBounds
    (p : CMParams) (U : ℝ → ℝ) (z : ℕ → ℝ → ℝ) : Prop where
  hasDeriv_value :
    ∀ k x, HasDerivAt (z (k + 1)) (deriv (z (k + 1)) x) x
  hasDeriv_U :
    ∀ x, HasDerivAt U (deriv U x) x
  hasDeriv_deriv :
    ∀ k x,
      HasDerivAt (fun y => deriv (z (k + 1)) y)
        (iteratedDeriv 2 (z (k + 1)) x) x
  hasDeriv_deriv_U :
    ∀ x, HasDerivAt (fun y => deriv U y) (iteratedDeriv 2 U x) x
  deriv1_uniform_lipschitz :
    UniformLipschitzOnCompacts
      (fun k x => deriv (z (k + 1)) x)
  deriv1_limit_lipschitz :
    LipschitzOnCompacts (fun x => deriv U x)
  deriv2_convergence :
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

def paperStepRBoundFromLambda (c lam Λ : ℝ) : ℝ :=
  Λ / (2 * (greenDelta c lam)⁻¹)

def paperStepC2Bound (c lam M Λ : ℝ) : ℝ :=
  paperStepRBoundFromLambda c lam Λ + |c| * Λ + |lam| * M

theorem paperStepRBoundFromLambda_nonneg
    {c lam Λ : ℝ} (hlam : 0 < lam) (hΛ : 0 ≤ Λ) :
    0 ≤ paperStepRBoundFromLambda c lam Λ := by
  unfold paperStepRBoundFromLambda
  have hD : 0 < 2 * (greenDelta c lam)⁻¹ :=
    mul_pos (by norm_num) (inv_pos.mpr (greenDelta_pos (c := c) hlam))
  exact div_nonneg hΛ hD.le

theorem paperStepC2Bound_nonneg
    {c lam M Λ : ℝ} (hlam : 0 < lam) (hM : 0 ≤ M) (hΛ : 0 ≤ Λ) :
    0 ≤ paperStepC2Bound c lam M Λ := by
  unfold paperStepC2Bound
  have hR := paperStepRBoundFromLambda_nonneg (c := c) (lam := lam) hlam hΛ
  have hc : 0 ≤ |c| * Λ := mul_nonneg (abs_nonneg c) hΛ
  have hl : 0 ≤ |lam| * M := mul_nonneg (abs_nonneg lam) hM
  linarith

theorem paperStep_R_abs_le_from_lambda
    {p : CMParams} {c lam M κ Λ : ℝ} {u Z W : ℝ → ℝ}
    (hlam : 0 < lam)
    (ha : PaperStepAnalytic p c lam M κ Λ u Z W) :
    ∀ y, |ha.R y| ≤ paperStepRBoundFromLambda c lam Λ := by
  obtain ⟨B, hB, hΛeq⟩ := ha.R_bound
  let D : ℝ := 2 * (greenDelta c lam)⁻¹
  have hDpos : 0 < D := by
    dsimp [D]
    exact mul_pos (by norm_num) (inv_pos.mpr (greenDelta_pos (c := c) hlam))
  have hDne : D ≠ 0 := ne_of_gt hDpos
  have hBeq : B = Λ / D := by
    rw [eq_div_iff hDne]
    rw [hΛeq]
    ring
  intro y
  simpa [paperStepRBoundFromLambda, D, hBeq] using hB y

theorem paperStep_hasDerivAt_value
    {p : CMParams} {c lam M κ Λ : ℝ} {u Z W : ℝ → ℝ}
    (ha : PaperStepAnalytic p c lam M κ Λ u Z W) :
    ∀ x, HasDerivAt W (deriv W x) x := by
  intro x
  have hgc := greenConv_hasDerivAt
    (c := c) (lam := lam) ha.R_cont ha.R_hi ha.R_lo x
  rw [ha.green_repr]
  simpa [hgc.deriv] using hgc

theorem paperStep_hasDerivAt_deriv
    {p : CMParams} {c lam M κ Λ : ℝ} {u Z W : ℝ → ℝ}
    (ha : PaperStepAnalytic p c lam M κ Λ u Z W) :
    ∀ x,
      HasDerivAt (fun y => deriv W y) (iteratedDeriv 2 W x) x := by
  intro x
  have hderiv_fun :
      (fun y => deriv W y) = fun y => greenConvDeriv c lam ha.R y := by
    funext y
    have hgc := greenConv_hasDerivAt
      (c := c) (lam := lam) ha.R_cont ha.R_hi ha.R_lo y
    have hrepr := congrArg (fun f : ℝ → ℝ => deriv f y) ha.green_repr
    have hrepr' : deriv W y = deriv (fun x => greenConv c lam ha.R x) y := by
      simpa using hrepr
    rw [hrepr', hgc.deriv]
  have hgc2 := greenConvDeriv_hasDerivAt
    (c := c) (lam := lam) ha.R_cont ha.R_hi ha.R_lo x
  have hiter : iteratedDeriv 2 W x = greenConvDeriv2 c lam ha.R x := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    change deriv (fun y => deriv W y) x = greenConvDeriv2 c lam ha.R x
    rw [hderiv_fun]
    exact hgc2.deriv
  rw [hderiv_fun, hiter]
  exact hgc2

theorem paperStep_iteratedDeriv_two_eq
    {p : CMParams} {c lam M κ Λ : ℝ} {u Z W : ℝ → ℝ}
    (hlam : 0 < lam)
    (ha : PaperStepAnalytic p c lam M κ Λ u Z W) :
    ∀ x,
      iteratedDeriv 2 W x =
        -ha.R x - c * deriv W x + lam * W x := by
  intro x
  have hL :
      iteratedDeriv 2 W x + c * deriv W x - lam * W x = -ha.R x := by
    have h2 :
        iteratedDeriv 2 W x =
          iteratedDeriv 2 (fun y => greenConv c lam ha.R y) x :=
      congrArg (fun f : ℝ → ℝ => iteratedDeriv 2 f x) ha.green_repr
    have h1 :
        deriv W x = deriv (fun y => greenConv c lam ha.R y) x :=
      congrArg (fun f : ℝ → ℝ => deriv f x) ha.green_repr
    have h0 : W x = greenConv c lam ha.R x := congrFun ha.green_repr x
    calc
      iteratedDeriv 2 W x + c * deriv W x - lam * W x
          = iteratedDeriv 2 (fun y => greenConv c lam ha.R y) x
              + c * deriv (fun y => greenConv c lam ha.R y) x
              - lam * (fun y => greenConv c lam ha.R y) x := by
            rw [h2, h1, h0]
      _ = -ha.R x :=
        greenConv_variation_negative
          (c := c) (lam := lam) hlam ha.R_cont ha.R_hi ha.R_lo x
  linarith

theorem paperStep_second_deriv_le
    {p : CMParams} {c lam M κ Λ : ℝ} {u Z W : ℝ → ℝ}
    (hlam : 0 < lam) (_hM : 0 ≤ M) (_hΛ : 0 ≤ Λ)
    (hW : ∀ x, |W x| ≤ M)
    (ha : PaperStepAnalytic p c lam M κ Λ u Z W) :
    ∀ x, |iteratedDeriv 2 W x| ≤ paperStepC2Bound c lam M Λ := by
  intro x
  have hEq := paperStep_iteratedDeriv_two_eq (c := c) (lam := lam) hlam ha x
  have hR := paperStep_R_abs_le_from_lambda (c := c) (lam := lam) hlam ha x
  have hD := paperStep_deriv_le (c := c) (lam := lam) hlam ha x
  have hDmul : |c| * |deriv W x| ≤ |c| * Λ :=
    mul_le_mul_of_nonneg_left hD (abs_nonneg c)
  have hWmul : |lam| * |W x| ≤ |lam| * M :=
    mul_le_mul_of_nonneg_left (hW x) (abs_nonneg lam)
  rw [hEq]
  have htri₁ :
      |-ha.R x - c * deriv W x + lam * W x|
        ≤ |-ha.R x - c * deriv W x| + |lam * W x| :=
    abs_add_le _ _
  have htri₂ :
      |-ha.R x - c * deriv W x| ≤ |-ha.R x| + |-(c * deriv W x)| :=
    abs_add_le _ _
  calc
    |-ha.R x - c * deriv W x + lam * W x|
        ≤ |-ha.R x - c * deriv W x| + |lam * W x| := htri₁
    _ ≤ (|-ha.R x| + |-(c * deriv W x)|) + |lam * W x| := by
      exact add_le_add htri₂ le_rfl
    _ = |ha.R x| + |c| * |deriv W x| + |lam| * |W x| := by
      rw [abs_neg, abs_neg, abs_mul, abs_mul]
    _ ≤ paperStepC2Bound c lam M Λ := by
      unfold paperStepC2Bound
      linarith

/-- C³ bootstrap data used only to turn the already-produced Green C² bounds
into Lipschitz moduli for the second-derivative family and for the limit. -/
structure PaperC3BootstrapData
    (U : ℝ → ℝ) (z : ℕ → ℝ → ℝ) : Prop where
  limit_hasDeriv_value :
    ∀ x, HasDerivAt U (deriv U x) x
  limit_hasDeriv_deriv :
    ∀ x, HasDerivAt (fun y => deriv U y) (iteratedDeriv 2 U x) x
  step_hasDeriv_deriv2 :
    ∀ k x,
      HasDerivAt (fun y => iteratedDeriv 2 (z (k + 1)) y)
        (deriv (fun y => iteratedDeriv 2 (z (k + 1)) y) x) x
  limit_hasDeriv_deriv2 :
    ∀ x,
      HasDerivAt (fun y => iteratedDeriv 2 U y)
        (deriv (fun y => iteratedDeriv 2 U y) x) x
  limit_deriv_bound :
    ∃ C, 0 ≤ C ∧ ∀ x, |deriv U x| ≤ C
  limit_second_bound :
    ∃ C, 0 ≤ C ∧ ∀ x, |iteratedDeriv 2 U x| ≤ C
  step_third_bound :
    ∃ C, 0 ≤ C ∧
      ∀ k x, |deriv (fun y => iteratedDeriv 2 (z (k + 1)) y) x| ≤ C
  limit_third_bound :
    ∃ C, 0 ≤ C ∧
      ∀ x, |deriv (fun y => iteratedDeriv 2 U y) x| ≤ C

theorem paperC2CompactUniformBounds_of_greenStep_repr
    {p : CMParams} {c lam κ M Λ : ℝ} {φ U : ℝ → ℝ}
    {z : ℕ → ℝ → ℝ} {R : ℝ → ℝ}
    (hlam : 0 < lam) (hM : 0 < M) (hΛ : 0 ≤ Λ)
    (hU : InLowerPinnedMonotoneTrap κ M φ U)
    (hLU : LocallyUniformConverges z U)
    (hz_nonneg : ∀ k x, 0 ≤ z k x)
    (hz_le_M : ∀ k x, z k x ≤ M)
    (hstep :
      ∀ k, PaperStepAnalytic p c lam M κ Λ U (z k) (z (k + 1)))
    (hR_cont : Continuous R)
    (hR_bound : ∃ B : ℝ,
      (∀ k y, |(hstep k).R y| ≤ B) ∧
        ∀ y, |R y| ≤ B)
    (hU_green : U = fun x => greenConv c lam R x)
    (hR_limit : LocallyUniformConverges (fun k => (hstep k).R) R) :
    PaperC2CompactUniformBounds p U z := by
  have hM0 : 0 ≤ M := hM.le
  have hbare : InMonotoneWaveTrapSet κ M U := hU.bare
  have hU_nonneg : ∀ x, 0 ≤ U x := hbare.nonneg
  have hU_le_M : ∀ x, U x ≤ M := hbare.le_M
  have hz_abs : ∀ k x, |z k x| ≤ M := by
    intro k x
    rw [abs_of_nonneg (hz_nonneg k x)]
    exact hz_le_M k x
  have hU_abs : ∀ x, |U x| ≤ M := by
    intro x
    rw [abs_of_nonneg (hU_nonneg x)]
    exact hU_le_M x
  have hshift :
      LocallyUniformConverges (fun k => z (k + 1)) U :=
    hLU.comp_strictMono
      (strictMono_nat_of_lt_succ fun n => Nat.lt_succ_self (n + 1))
  have hC2_nonneg : 0 ≤ paperStepC2Bound c lam M Λ :=
    paperStepC2Bound_nonneg (c := c) (lam := lam) hlam hM0 hΛ
  obtain ⟨BR, hBRseq, hBR⟩ := hR_bound
  have hBR_nonneg : 0 ≤ BR :=
    le_trans (abs_nonneg (R 0)) (hBR 0)
  have hR_hi : ∀ x,
      IntegrableOn (gWeight (greenRootPlus c lam) R) (Ioi x) :=
    fun x => gWeight_integrableOn_Ioi_of_bounded
      (greenRootPlus_pos (c := c) hlam) hR_cont hBR x
  have hR_lo : ∀ x,
      IntegrableOn (gWeight (greenRootMinus c lam) R) (Iic x) :=
    fun x => gWeight_integrableOn_Iic_of_bounded
      (greenRootMinus_neg (c := c) hlam) hR_cont hBR x
  have hU_hasDeriv_value :
      ∀ x, HasDerivAt U (deriv U x) x := by
    intro x
    have hgc := greenConv_hasDerivAt
      (c := c) (lam := lam) hR_cont hR_hi hR_lo x
    rw [hU_green]
    simpa [hgc.deriv] using hgc
  have hU_deriv_eq :
      (fun x => deriv U x) = fun x => greenConvDeriv c lam R x := by
    funext x
    have hgc := greenConv_hasDerivAt
      (c := c) (lam := lam) hR_cont hR_hi hR_lo x
    have hrepr := congrArg (fun f : ℝ → ℝ => deriv f x) hU_green
    have hrepr' : deriv U x = deriv (fun y => greenConv c lam R y) x := by
      simpa using hrepr
    rw [hrepr', hgc.deriv]
  have hU_iter_eq :
      ∀ x, iteratedDeriv 2 U x = greenConvDeriv2 c lam R x := by
    intro x
    have hgc2 := greenConvDeriv_hasDerivAt
      (c := c) (lam := lam) hR_cont hR_hi hR_lo x
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
      iteratedDeriv_one]
    change deriv (fun y => deriv U y) x = greenConvDeriv2 c lam R x
    rw [hU_deriv_eq]
    exact hgc2.deriv
  have hU_hasDeriv_deriv :
      ∀ x, HasDerivAt (fun y => deriv U y) (iteratedDeriv 2 U x) x := by
    intro x
    have hgc2 := greenConvDeriv_hasDerivAt
      (c := c) (lam := lam) hR_cont hR_hi hR_lo x
    rw [hU_deriv_eq]
    simpa [hU_iter_eq x] using hgc2
  let CU1 : ℝ := 2 * (greenDelta c lam)⁻¹ * BR
  have hCU1_nonneg : 0 ≤ CU1 := by
    dsimp [CU1]
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (inv_pos.mpr (greenDelta_pos (c := c) hlam)).le)
      hBR_nonneg
  have hCU1 : ∀ x, |deriv U x| ≤ CU1 := by
    intro x
    have hbd := greenConvDeriv_abs_le
      (c := c) (lam := lam) hlam hBR hR_hi hR_lo x
    simpa [CU1, hU_deriv_eq] using hbd
  have hU_second_eq :
      ∀ x, iteratedDeriv 2 U x =
        -R x - c * deriv U x + lam * U x := by
    intro x
    have hsolve :
        iteratedDeriv 2 U x + c * deriv U x - lam * U x = -R x := by
      rw [hU_iter_eq x, congrFun hU_deriv_eq x, congrFun hU_green x]
      exact greenConv_solves (c := c) (lam := lam) hlam (H := R) x
    linarith
  let CU2 : ℝ := BR + |c| * CU1 + |lam| * M
  have hCU2_nonneg : 0 ≤ CU2 := by
    dsimp [CU2]
    have hc : 0 ≤ |c| * CU1 := mul_nonneg (abs_nonneg c) hCU1_nonneg
    have hl : 0 ≤ |lam| * M := mul_nonneg (abs_nonneg lam) hM0
    linarith
  have hCU2 : ∀ x, |iteratedDeriv 2 U x| ≤ CU2 := by
    intro x
    have hEq := hU_second_eq x
    have hRbd := hBR x
    have hDbd := hCU1 x
    have hWbd := hU_abs x
    have hDmul : |c| * |deriv U x| ≤ |c| * CU1 :=
      mul_le_mul_of_nonneg_left hDbd (abs_nonneg c)
    have hWmul : |lam| * |U x| ≤ |lam| * M :=
      mul_le_mul_of_nonneg_left hWbd (abs_nonneg lam)
    rw [hEq]
    have htri₁ :
        |-R x - c * deriv U x + lam * U x|
          ≤ |-R x - c * deriv U x| + |lam * U x| :=
      abs_add_le _ _
    have htri₂ :
        |-R x - c * deriv U x| ≤ |-R x| + |-(c * deriv U x)| :=
      abs_add_le _ _
    calc
      |-R x - c * deriv U x + lam * U x|
          ≤ |-R x - c * deriv U x| + |lam * U x| := htri₁
      _ ≤ (|-R x| + |-(c * deriv U x)|) + |lam * U x| := by
        exact add_le_add htri₂ le_rfl
      _ = |R x| + |c| * |deriv U x| + |lam| * |U x| := by
        rw [abs_neg, abs_neg, abs_mul, abs_mul]
      _ ≤ CU2 := by
        dsimp [CU2]
        linarith
  have hderiv1_uniform_lipschitz :
      UniformLipschitzOnCompacts
        (fun k x => deriv (z (k + 1)) x) :=
    UniformLipschitzOnCompacts.of_hasDerivAt_bound hC2_nonneg
      (fun k x => paperStep_hasDerivAt_deriv (hstep k) x)
      (fun k x =>
        paperStep_second_deriv_le
          (c := c) (lam := lam) hlam hM0 hΛ
          (fun y => hz_abs (k + 1) y) (hstep k) x)
  have hderiv1_limit_lipschitz :
      LipschitzOnCompacts (fun x => deriv U x) :=
    LipschitzOnCompacts.of_hasDerivAt_bound hCU2_nonneg
      hU_hasDeriv_deriv hCU2
  have hderiv1 :
      LocallyUniformConverges
        (fun k x => deriv (z (k + 1)) x)
        (fun x => deriv U x) :=
    hshift.deriv_of_hasDerivAt_of_residual_lipschitz
      (fun k x => paperStep_hasDerivAt_value (hstep k) x)
      hU_hasDeriv_value
      (UniformResidualLipschitzOnCompacts.of_pair
        hderiv1_uniform_lipschitz hderiv1_limit_lipschitz)
  have hderiv2 :
      LocallyUniformConverges
        (fun k x => iteratedDeriv 2 (z (k + 1)) x)
        (fun x => iteratedDeriv 2 U x) := by
    have hRneg : LocallyUniformConverges
        (fun k x => -((hstep k).R x)) (fun x => -R x) :=
      hR_limit.neg
    have hcd : LocallyUniformConverges
        (fun k x => c * deriv (z (k + 1)) x)
        (fun x => c * deriv U x) :=
      hderiv1.const_mul c
    have hleft : LocallyUniformConverges
        (fun k x => -((hstep k).R x) - c * deriv (z (k + 1)) x)
        (fun x => -R x - c * deriv U x) :=
      hRneg.sub hcd
    have hval_lam : LocallyUniformConverges
        (fun k x => lam * z (k + 1) x) (fun x => lam * U x) :=
      hshift.const_mul lam
    have hrhs : LocallyUniformConverges
        (fun k x =>
          -((hstep k).R x) - c * deriv (z (k + 1)) x
            + lam * z (k + 1) x)
        (fun x => -R x - c * deriv U x + lam * U x) := by
      simpa [sub_eq_add_neg, add_assoc] using hleft.add hval_lam
    have hseq_eq :
        ∀ᶠ k : ℕ in atTop,
          (fun x =>
              -((hstep k).R x) - c * deriv (z (k + 1)) x
                + lam * z (k + 1) x) =
            fun x => iteratedDeriv 2 (z (k + 1)) x := by
      exact Eventually.of_forall fun k => by
        funext x
        exact (paperStep_iteratedDeriv_two_eq
          (c := c) (lam := lam) hlam (hstep k) x).symm
    have hlim_eq :
        (fun x => iteratedDeriv 2 U x) =
          fun x => -R x - c * deriv U x + lam * U x := by
      funext x
      exact hU_second_eq x
    simpa [hlim_eq] using LocallyUniformConverges.congr hseq_eq hrhs
  have hpow_m_sub_one :
      LocallyUniformConverges
        (fun k x => (z (k + 1) x) ^ (p.m - 1))
        (fun x => (U x) ^ (p.m - 1)) :=
    hshift.rpow_of_nonneg_le (by linarith [p.hm]) hM0
      (fun k x => hz_nonneg (k + 1) x)
      (fun k x => hz_le_M (k + 1) x)
      hU_nonneg hU_le_M
  have hpow_alpha :
      LocallyUniformConverges
        (fun k x => (z (k + 1) x) ^ p.α)
        (fun x => (U x) ^ p.α) :=
    hshift.rpow_of_nonneg_le (by linarith [p.hα]) hM0
      (fun k x => hz_nonneg (k + 1) x)
      (fun k x => hz_le_M (k + 1) x)
      hU_nonneg hU_le_M
  have hpow_m_gamma_sub_one :
      LocallyUniformConverges
        (fun k x => (z (k + 1) x) ^ (p.m + p.γ - 1))
        (fun x => (U x) ^ (p.m + p.γ - 1)) :=
    hshift.rpow_of_nonneg_le (by linarith [p.hm, p.hγ]) hM0
      (fun k x => hz_nonneg (k + 1) x)
      (fun k x => hz_le_M (k + 1) x)
      hU_nonneg hU_le_M
  have hbdd_U : LocallyBoundedOnCompacts U :=
    LocallyBoundedOnCompacts.of_global_bound hM0 hU_abs
  have hbdd_derivU : LocallyBoundedOnCompacts (fun x => deriv U x) :=
    LocallyBoundedOnCompacts.of_global_bound hCU1_nonneg hCU1
  have hMγ_nonneg : 0 ≤ M ^ p.γ := Real.rpow_nonneg hM0 p.γ
  have hbdd_V : LocallyBoundedOnCompacts (frozenElliptic p U) := by
    refine LocallyBoundedOnCompacts.of_global_bound hMγ_nonneg ?_
    intro x
    rw [abs_of_nonneg (frozenElliptic_nonneg p hU_nonneg x)]
    exact frozenElliptic_le_rpow_of_inWaveTrapSet p hM hbare.trap x
  have hbdd_derivV :
      LocallyBoundedOnCompacts (fun x => deriv (frozenElliptic p U) x) := by
    refine LocallyBoundedOnCompacts.of_global_bound hMγ_nonneg ?_
    intro x
    calc
      |deriv (frozenElliptic p U) x| ≤ frozenElliptic p U x :=
        frozenElliptic_deriv_abs_le p hbare.trap.cunif_bdd hU_nonneg x
      _ ≤ M ^ p.γ :=
        frozenElliptic_le_rpow_of_inWaveTrapSet p hM hbare.trap x
  have hMm1_nonneg : 0 ≤ M ^ (p.m - 1) :=
    Real.rpow_nonneg hM0 (p.m - 1)
  have hbdd_pow_m_sub_one :
      LocallyBoundedOnCompacts (fun x => (U x) ^ (p.m - 1)) := by
    refine LocallyBoundedOnCompacts.of_global_bound hMm1_nonneg ?_
    intro x
    rw [abs_of_nonneg (Real.rpow_nonneg (hU_nonneg x) (p.m - 1))]
    exact Real.rpow_le_rpow (hU_nonneg x) (hU_le_M x) (by linarith [p.hm])
  have hMα_nonneg : 0 ≤ M ^ p.α := Real.rpow_nonneg hM0 p.α
  have hbdd_pow_alpha :
      LocallyBoundedOnCompacts (fun x => (U x) ^ p.α) := by
    refine LocallyBoundedOnCompacts.of_global_bound hMα_nonneg ?_
    intro x
    rw [abs_of_nonneg (Real.rpow_nonneg (hU_nonneg x) p.α)]
    exact Real.rpow_le_rpow (hU_nonneg x) (hU_le_M x) (by linarith [p.hα])
  have hMmg_nonneg : 0 ≤ M ^ (p.m + p.γ - 1) :=
    Real.rpow_nonneg hM0 (p.m + p.γ - 1)
  have hbdd_pow_m_gamma_sub_one :
      LocallyBoundedOnCompacts (fun x => (U x) ^ (p.m + p.γ - 1)) := by
    refine LocallyBoundedOnCompacts.of_global_bound hMmg_nonneg ?_
    intro x
    rw [abs_of_nonneg (Real.rpow_nonneg (hU_nonneg x) (p.m + p.γ - 1))]
    exact Real.rpow_le_rpow (hU_nonneg x) (hU_le_M x)
      (by linarith [p.hm, p.hγ])
  have hbdd_reaction_bracket :
      LocallyBoundedOnCompacts (paperWaveReactionBracket p U U) := by
    have hpowV := hbdd_pow_m_sub_one.mul hbdd_V
    have hleft := (hpowV.const_mul p.χ).const_sub 1
    have hright := hbdd_pow_alpha.sub
      (hbdd_pow_m_gamma_sub_one.const_mul p.χ)
    have hbr := hleft.sub hright
    simpa [paperWaveReactionBracket, mul_assoc] using hbr
  exact
    { hasDeriv_value := fun k x =>
        paperStep_hasDerivAt_value (hstep k) x
      hasDeriv_U := hU_hasDeriv_value
      hasDeriv_deriv := fun k x =>
        paperStep_hasDerivAt_deriv (hstep k) x
      hasDeriv_deriv_U := hU_hasDeriv_deriv
      deriv1_uniform_lipschitz := hderiv1_uniform_lipschitz
      deriv1_limit_lipschitz := hderiv1_limit_lipschitz
      deriv2_convergence := hderiv2
      pow_m_sub_one := hpow_m_sub_one
      pow_alpha := hpow_alpha
      pow_m_gamma_sub_one := hpow_m_gamma_sub_one
      bdd_U := hbdd_U
      bdd_derivU := hbdd_derivU
      bdd_V := hbdd_V
      bdd_derivV := hbdd_derivV
      bdd_pow_m_sub_one := hbdd_pow_m_sub_one
      bdd_reaction_bracket := hbdd_reaction_bracket }

/-- Produce paper `C²` compact convergence from zeroth-order local-uniform
convergence plus uniform Green/ODE bounds. -/
def paperC2CompactConvergence_of_uniformBounds
    {p : CMParams} {U : ℝ → ℝ} {z : ℕ → ℝ → ℝ}
    (hLU : LocallyUniformConverges z U)
    (hbounds : PaperC2CompactUniformBounds p U z) :
    PaperC2CompactConvergence p U z :=
  let hvalue : LocallyUniformConverges (fun k => z (k + 1)) U :=
    hLU.comp_strictMono
      (strictMono_nat_of_lt_succ fun n => Nat.lt_succ_self (n + 1))
  let hderiv1 :
      LocallyUniformConverges
        (fun k x => deriv (z (k + 1)) x)
        (fun x => deriv U x) :=
    hvalue.deriv_of_hasDerivAt_of_residual_lipschitz
      hbounds.hasDeriv_value hbounds.hasDeriv_U
      (UniformResidualLipschitzOnCompacts.of_pair
        hbounds.deriv1_uniform_lipschitz hbounds.deriv1_limit_lipschitz)
  { value := hvalue
    step_hasDeriv_value := hbounds.hasDeriv_value
    step_hasDeriv_deriv := hbounds.hasDeriv_deriv
    deriv1 := hderiv1
    deriv2 := hbounds.deriv2_convergence
    pow_m_sub_one := hbounds.pow_m_sub_one
    pow_alpha := hbounds.pow_alpha
    pow_m_gamma_sub_one := hbounds.pow_m_gamma_sub_one
    bdd_U := hbounds.bdd_U
    bdd_derivU := hbounds.bdd_derivU
    bdd_V := hbounds.bdd_V
    bdd_derivV := hbounds.bdd_derivV
    bdd_pow_m_sub_one := hbounds.bdd_pow_m_sub_one
    bdd_reaction_bracket := hbounds.bdd_reaction_bracket }

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

theorem limit_hasDeriv_value
    {p : CMParams} {U : ℝ → ℝ} {z : ℕ → ℝ → ℝ}
    (h : PaperC2CompactConvergence p U z) :
    ∀ x, HasDerivAt U (deriv U x) x := by
  intro x
  have hderiv :
      TendstoLocallyUniformlyOn
        (fun k x => deriv (z (k + 1)) x)
        (fun x => deriv U x) atTop (Set.univ : Set ℝ) :=
    h.deriv1.tendstoLocallyUniformlyOn_univ
  have hstep :
      ∀ᶠ k : ℕ in atTop,
        ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) →
          HasDerivAt (z (k + 1)) (deriv (z (k + 1)) y) y := by
    exact Eventually.of_forall fun k y _hy => h.step_hasDeriv_value k y
  have hpoint :
      ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) →
        Tendsto (fun k : ℕ => z (k + 1) y) atTop (𝓝 (U y)) := by
    intro y _hy
    exact h.value.tendsto_at y
  exact hasDerivAt_of_tendstoLocallyUniformlyOn
    (𝕜 := ℝ) (l := atTop) (s := (Set.univ : Set ℝ))
    (f := fun k : ℕ => z (k + 1)) (g := U)
    (f' := fun k x => deriv (z (k + 1)) x)
    (g' := fun x => deriv U x) isOpen_univ hderiv hstep hpoint
    (Set.mem_univ x)

theorem limit_hasDeriv_deriv
    {p : CMParams} {U : ℝ → ℝ} {z : ℕ → ℝ → ℝ}
    (h : PaperC2CompactConvergence p U z) :
    ∀ x, HasDerivAt (fun y => deriv U y) (iteratedDeriv 2 U x) x := by
  intro x
  have hderiv2 :
      TendstoLocallyUniformlyOn
        (fun k x => iteratedDeriv 2 (z (k + 1)) x)
        (fun x => iteratedDeriv 2 U x) atTop (Set.univ : Set ℝ) :=
    h.deriv2.tendstoLocallyUniformlyOn_univ
  have hstep :
      ∀ᶠ k : ℕ in atTop,
        ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) →
          HasDerivAt (fun t => deriv (z (k + 1)) t)
            (iteratedDeriv 2 (z (k + 1)) y) y := by
    exact Eventually.of_forall fun k y _hy => h.step_hasDeriv_deriv k y
  have hpoint :
      ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) →
        Tendsto (fun k : ℕ => deriv (z (k + 1)) y) atTop
          (𝓝 (deriv U y)) := by
    intro y _hy
    exact h.deriv1.tendsto_at y
  exact hasDerivAt_of_tendstoLocallyUniformlyOn
    (𝕜 := ℝ) (l := atTop) (s := (Set.univ : Set ℝ))
    (f := fun k : ℕ => fun y => deriv (z (k + 1)) y)
    (g := fun y => deriv U y)
    (f' := fun k x => iteratedDeriv 2 (z (k + 1)) x)
    (g' := fun x => iteratedDeriv 2 U x) isOpen_univ hderiv2 hstep
    hpoint (Set.mem_univ x)

theorem c2Regularity
    {p : CMParams} {U : ℝ → ℝ} {z : ℕ → ℝ → ℝ}
    (h : PaperC2CompactConvergence p U z) :
    Differentiable ℝ U ∧ Differentiable ℝ (deriv U) := by
  exact ⟨fun x => (h.limit_hasDeriv_value x).differentiableAt,
    fun x => (h.limit_hasDeriv_deriv x).differentiableAt⟩

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

theorem paperStepSource_locallyUniform
    {p : CMParams} {c lam : ℝ} {U : ℝ → ℝ} {z : ℕ → ℝ → ℝ}
    (h : PaperC2CompactConvergence p U z)
    (hLU : LocallyUniformConverges z U) :
    LocallyUniformConverges
      (fun k => paperStepSource p c lam U (z k) (z (k + 1)))
      (paperStepSource p c lam U U U) := by
  have hterms : PaperWaveOperatorTermConvergence p c U z :=
    h.termConvergence
  have hnonlin :
      LocallyUniformConverges
        (fun k x =>
          paperWaveChemTerm p U (z (k + 1)) x +
            paperWaveReactionTerm p U (z (k + 1)) x)
        (fun x => paperWaveChemTerm p U U x + paperWaveReactionTerm p U U x) :=
    hterms.chem.add hterms.reaction
  have hlinear :
      LocallyUniformConverges
        (fun k x => lam * z k x)
        (fun x => lam * U x) :=
    hLU.const_mul lam
  have hsum := hnonlin.add hlinear
  simpa [paperStepSource_eq_terms, add_assoc] using hsum

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
#print axioms paperStep_second_deriv_le
#print axioms paperC2CompactUniformBounds_of_greenStep_repr
#print axioms PaperWaveOperatorTermConvergence.of_c2CompactConvergence
#print axioms PaperWaveOperatorTermConvergence.operator

end PaperWaveOperatorTermConvergence

/-! ## Green tails from a source tail limit

The stationary flatness argument needs the following analytic fact in a reusable
form: if a bounded continuous Green source has a finite left tail limit, then
the Green profile has left derivative tails `0`.  The first derivative is proved
from the translated `K'` convolution and dominated convergence.  The second
derivative then follows from the resolvent identity
`w'' + c w' - λw = -R`, avoiding any separate `K''` bookkeeping. -/

theorem greenKernelDeriv_integrable_signed {c lam : ℝ} (hlam : 0 < lam) :
    Integrable (greenKernelDeriv c lam) := by
  refine (greenKernelDeriv_integrable (c := c) hlam).mono' ?_ ?_
  · exact greenKernelDeriv_measurable.aestronglyMeasurable
  · exact Eventually.of_forall (fun z => by simp [Real.norm_eq_abs])

theorem greenKernelDeriv_setIntegral_Iic {c lam : ℝ} (hlam : 0 < lam) :
    ∫ z in Set.Iic (0 : ℝ), greenKernelDeriv c lam z
      = (greenDelta c lam)⁻¹ := by
  have hrp := greenRootPlus_pos (c := c) hlam
  have hrpne : greenRootPlus c lam ≠ 0 := ne_of_gt hrp
  have hcongr :
      ∫ z in Set.Iic (0 : ℝ), greenKernelDeriv c lam z
        = ∫ z in Set.Iic (0 : ℝ),
            (greenDelta c lam)⁻¹ * greenRootPlus c lam *
              Real.exp (greenRootPlus c lam * z) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Iic
    intro z hz
    rw [Set.mem_Iic] at hz
    simp only [greenKernelDeriv, if_pos hz]
  rw [hcongr, MeasureTheory.integral_const_mul, integral_exp_mul_Iic hrp 0]
  rw [mul_zero, Real.exp_zero]
  field_simp

theorem greenKernelDeriv_setIntegral_Ioi {c lam : ℝ} (hlam : 0 < lam) :
    ∫ z in Set.Ioi (0 : ℝ), greenKernelDeriv c lam z
      = -((greenDelta c lam)⁻¹) := by
  have hrm := greenRootMinus_neg (c := c) hlam
  have hrmne : greenRootMinus c lam ≠ 0 := ne_of_lt hrm
  have hcongr :
      ∫ z in Set.Ioi (0 : ℝ), greenKernelDeriv c lam z
        = ∫ z in Set.Ioi (0 : ℝ),
            (greenDelta c lam)⁻¹ * greenRootMinus c lam *
              Real.exp (greenRootMinus c lam * z) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro z hz
    rw [Set.mem_Ioi] at hz
    simp only [greenKernelDeriv, if_neg (not_le.mpr hz)]
  rw [hcongr, MeasureTheory.integral_const_mul, integral_exp_mul_Ioi hrm 0]
  rw [mul_zero, Real.exp_zero]
  field_simp

theorem greenKernelDeriv_integral_eq_zero {c lam : ℝ} (hlam : 0 < lam) :
    ∫ z, greenKernelDeriv c lam z = 0 := by
  have hfi := greenKernelDeriv_integrable_signed (c := c) hlam
  have hsplit := MeasureTheory.integral_add_compl
    (s := Set.Iic (0 : ℝ)) measurableSet_Iic hfi
  simp only [Set.compl_Iic] at hsplit
  linarith [hsplit.symm, greenKernelDeriv_setIntegral_Iic (c := c) hlam,
    greenKernelDeriv_setIntegral_Ioi (c := c) hlam]

theorem greenKernelDeriv_comp_const_sub_mul_integrable_of_bounded
    {c lam : ℝ} (hlam : 0 < lam) {H : ℝ → ℝ} {B : ℝ}
    (hH : Continuous H) (hB : ∀ y, |H y| ≤ B) (x : ℝ) :
    Integrable (fun y => greenKernelDeriv c lam (x - y) * H y) := by
  have hK : Integrable (fun y => greenKernelDeriv c lam (x - y)) := by
    simpa using
      (greenKernelDeriv_integrable_signed (c := c) (lam := lam) hlam).comp_sub_left x
  exact hK.mul_bdd hH.aestronglyMeasurable
    (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hB y)

theorem greenKernelDeriv_neg_mul_translate_integrable_of_bounded
    {c lam : ℝ} (hlam : 0 < lam) {H : ℝ → ℝ} {B : ℝ}
    (hH : Continuous H) (hB : ∀ y, |H y| ≤ B) (x : ℝ) :
    Integrable (fun t => greenKernelDeriv c lam (-t) * H (x + t)) := by
  have hK : Integrable (fun t => greenKernelDeriv c lam (-t)) :=
    (greenKernelDeriv_integrable_signed (c := c) (lam := lam) hlam).comp_neg
  have hshift : AEStronglyMeasurable (fun t : ℝ => H (x + t)) volume :=
    (hH.comp (continuous_const.add continuous_id)).aestronglyMeasurable
  exact hK.mul_bdd hshift
    (Eventually.of_forall fun t => by simpa [Real.norm_eq_abs] using hB (x + t))

theorem greenKernelDerivConv_eq_translated
    (c lam : ℝ) (H : ℝ → ℝ) (x : ℝ) :
    (∫ y, greenKernelDeriv c lam (x - y) * H y)
      = ∫ t, greenKernelDeriv c lam (-t) * H (x + t) := by
  let g : ℝ → ℝ := fun y => greenKernelDeriv c lam (x - y) * H y
  have htrans := integral_add_right_eq_self (μ := (volume : Measure ℝ)) g x
  calc
    (∫ y, greenKernelDeriv c lam (x - y) * H y) = ∫ y, g y := rfl
    _ = ∫ t, g (t + x) := htrans.symm
    _ = ∫ t, greenKernelDeriv c lam (-t) * H (x + t) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun t => by
        dsimp [g]
        rw [show x - (t + x) = -t by ring]
        ring

theorem greenKernelDerivConv_eq_greenConvDeriv
    {c lam : ℝ} (hlam : 0 < lam) {H : ℝ → ℝ} {B : ℝ}
    (hH : Continuous H) (hB : ∀ y, |H y| ≤ B) (x : ℝ) :
    (∫ y, greenKernelDeriv c lam (x - y) * H y)
      = greenConvDeriv c lam H x := by
  have hfull := greenKernelDeriv_comp_const_sub_mul_integrable_of_bounded
    (c := c) (lam := lam) hlam hH hB x
  have hsplit := MeasureTheory.integral_add_compl
    (s := Set.Iic x) measurableSet_Iic hfull
  simp only [Set.compl_Iic] at hsplit
  have hLeft :
      ∫ y in Set.Iic x, greenKernelDeriv c lam (x - y) * H y
        = (greenDelta c lam)⁻¹ * greenRootMinus c lam *
            Real.exp (greenRootMinus c lam * x) *
              tailLo (greenRootMinus c lam) H x := by
    have hae : ∀ᵐ y : ℝ ∂volume, y ≠ x := by
      rw [ae_iff]
      simpa only [not_not] using (measure_singleton (μ := volume) x)
    calc
      ∫ y in Set.Iic x, greenKernelDeriv c lam (x - y) * H y
          = ∫ y in Set.Iic x,
              (greenDelta c lam)⁻¹ * greenRootMinus c lam *
                Real.exp (greenRootMinus c lam * x) *
                  gWeight (greenRootMinus c lam) H y := by
            apply MeasureTheory.setIntegral_congr_ae measurableSet_Iic
            filter_upwards [hae] with y hyne hy
            rw [Set.mem_Iic] at hy
            have hxy_pos : 0 < x - y := sub_pos.mpr (lt_of_le_of_ne hy hyne)
            simp only [greenKernelDeriv, if_neg (not_le.mpr hxy_pos)]
            simp only [gWeight]
            rw [show greenRootMinus c lam * (x - y)
                = greenRootMinus c lam * x + (-greenRootMinus c lam) * y by ring,
              Real.exp_add]
            ring
      _ = (greenDelta c lam)⁻¹ * greenRootMinus c lam *
            Real.exp (greenRootMinus c lam * x) *
              tailLo (greenRootMinus c lam) H x := by
            rw [MeasureTheory.integral_const_mul]
            rfl
  have hRight :
      ∫ y in Set.Ioi x, greenKernelDeriv c lam (x - y) * H y
        = (greenDelta c lam)⁻¹ * greenRootPlus c lam *
            Real.exp (greenRootPlus c lam * x) *
              tailHi (greenRootPlus c lam) H x := by
    calc
      ∫ y in Set.Ioi x, greenKernelDeriv c lam (x - y) * H y
          = ∫ y in Set.Ioi x,
              (greenDelta c lam)⁻¹ * greenRootPlus c lam *
                Real.exp (greenRootPlus c lam * x) *
                  gWeight (greenRootPlus c lam) H y := by
            apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
            intro y hy
            rw [Set.mem_Ioi] at hy
            have hxy_neg : x - y ≤ 0 := by linarith
            simp only [greenKernelDeriv, if_pos hxy_neg]
            simp only [gWeight]
            rw [show greenRootPlus c lam * (x - y)
                = greenRootPlus c lam * x + (-greenRootPlus c lam) * y by ring,
              Real.exp_add]
            ring
      _ = (greenDelta c lam)⁻¹ * greenRootPlus c lam *
            Real.exp (greenRootPlus c lam * x) *
              tailHi (greenRootPlus c lam) H x := by
            rw [MeasureTheory.integral_const_mul]
            rfl
  rw [← hsplit, hLeft, hRight, greenConvDeriv]
  ring

theorem greenConvDeriv_eq_translated_integral_of_bounded
    {c lam : ℝ} (hlam : 0 < lam) {H : ℝ → ℝ} {B : ℝ}
    (hH : Continuous H) (hB : ∀ y, |H y| ≤ B) (x : ℝ) :
    greenConvDeriv c lam H x =
      ∫ t, greenKernelDeriv c lam (-t) * H (x + t) := by
  rw [← greenKernelDerivConv_eq_translated c lam H x]
  exact (greenKernelDerivConv_eq_greenConvDeriv
    (c := c) (lam := lam) hlam hH hB x).symm

theorem greenConvDeriv2_tendsto_atBot_of_source_tendsto
    {c lam : ℝ} (hlam : 0 < lam) {H : ℝ → ℝ} {B L : ℝ}
    (hH : Continuous H) (hB : ∀ y, |H y| ≤ B)
    (hlim : Tendsto H atBot (𝓝 L)) :
    Tendsto (greenConvDeriv2 c lam H) atBot (𝓝 0) := by
  have h0 := greenConv_tendsto_atBot_of_source_tendsto
    (c := c) (lam := lam) hlam hH hB hlim
  have h1 := greenConvDeriv_tendsto_atBot_of_source_tendsto
    (c := c) (lam := lam) hlam hH hB hlim
  have hlin :
      Tendsto
        (fun x => -H x - c * greenConvDeriv c lam H x
          + lam * greenConv c lam H x)
        atBot (𝓝 0) := by
    have hsum :=
      ((hlim.neg.sub (h1.const_mul c)).add (h0.const_mul lam))
    have htarget : -L + lam * (L * lam⁻¹) = 0 := by
      field_simp [ne_of_gt hlam]
      ring
    simpa [htarget, sub_eq_add_neg] using hsum
  have hpoint :
      greenConvDeriv2 c lam H =
        fun x => -H x - c * greenConvDeriv c lam H x
          + lam * greenConv c lam H x := by
    funext x
    have hsolve := greenConv_solves (c := c) (lam := lam) hlam (H := H) x
    linarith
  simpa [hpoint] using hlin

theorem tendsto_zero_mul_of_bounded_left_atBot
    {f g : ℝ → ℝ} {C : ℝ}
    (_hC0 : 0 ≤ C) (hf : ∀ x, |f x| ≤ C)
    (hg : Tendsto g atBot (𝓝 0)) :
    Tendsto (fun x => f x * g x) atBot (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hgabs : Tendsto (fun x => |g x|) atBot (𝓝 0) := by
    simpa using hg.abs
  refine squeeze_zero
    (f := fun x => ‖f x * g x‖)
    (g := fun x => C * |g x|)
    (fun x => norm_nonneg (f x * g x)) ?_ ?_
  · intro x
    change ‖f x * g x‖ ≤ C * |g x|
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hf x) (abs_nonneg _)
  · simpa using hgabs.const_mul C

theorem tendsto_zero_mul_of_bounded_right_atBot
    {f g : ℝ → ℝ} {C : ℝ}
    (hC0 : 0 ≤ C) (hg : ∀ x, |g x| ≤ C)
    (hf : Tendsto f atBot (𝓝 0)) :
    Tendsto (fun x => f x * g x) atBot (𝓝 0) := by
  have h := tendsto_zero_mul_of_bounded_left_atBot
    (f := g) (g := f) hC0 hg hf
  simpa [mul_comm] using h

theorem greenConv_profile_deriv_tails_atBot_of_source_tendsto
    {c lam : ℝ} (hlam : 0 < lam) {U R : ℝ → ℝ} {B L : ℝ}
    (hRcont : Continuous R) (hRbound : ∀ y, |R y| ≤ B)
    (hRlim : Tendsto R atBot (𝓝 L))
    (hgreen : U = fun x => greenConv c lam R x) :
    Tendsto (fun x => deriv U x) atBot (𝓝 0) ∧
      Tendsto (fun x => iteratedDeriv 2 U x) atBot (𝓝 0) := by
  have hHi : ∀ x, IntegrableOn (gWeight (greenRootPlus c lam) R) (Ioi x) :=
    fun x => gWeight_integrableOn_Ioi_of_bounded
      (greenRootPlus_pos (c := c) hlam) hRcont hRbound x
  have hLo : ∀ x, IntegrableOn (gWeight (greenRootMinus c lam) R) (Iic x) :=
    fun x => gWeight_integrableOn_Iic_of_bounded
      (greenRootMinus_neg (c := c) hlam) hRcont hRbound x
  have hderiv_eq :
      (fun x => deriv U x) = fun x => greenConvDeriv c lam R x := by
    funext x
    rw [hgreen]
    exact (greenConv_hasDerivAt
      (c := c) (lam := lam) hRcont hHi hLo x).deriv
  have hiter_eq :
      (fun x => iteratedDeriv 2 U x) = fun x => greenConvDeriv2 c lam R x := by
    funext x
    have hderiv_fun :
        (fun y => deriv U y) = fun y => greenConvDeriv c lam R y := hderiv_eq
    rw [show iteratedDeriv 2 U x = deriv (fun y => deriv U y) x by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
        iteratedDeriv_one]]
    rw [hderiv_fun]
    exact (greenConvDeriv_hasDerivAt
      (c := c) (lam := lam) hRcont hHi hLo x).deriv
  constructor
  · simpa [hderiv_eq] using
      greenConvDeriv_tendsto_atBot_of_source_tendsto
        (c := c) (lam := lam) hlam hRcont hRbound hRlim
  · simpa [hiter_eq] using
      greenConvDeriv2_tendsto_atBot_of_source_tendsto
        (c := c) (lam := lam) hlam hRcont hRbound hRlim

/-- Pointwise continuity of the whole-line Green convolution with respect to
uniformly bounded pointwise source convergence.  This is the DCT bridge used to
thread a Rothe-limit Green representation from the per-step representations. -/
theorem greenConv_tendsto_of_source_tendsto_of_uniform_bound
    {c lam : ℝ} (hlam : 0 < lam) {Rs : ℕ → ℝ → ℝ} {R : ℝ → ℝ} {B : ℝ}
    (hRs_cont : ∀ n, Continuous (Rs n))
    (hR_cont : Continuous R)
    (hRs_bound : ∀ n y, |Rs n y| ≤ B)
    (hR_bound : ∀ y, |R y| ≤ B)
    (hRs_lim : ∀ y, Tendsto (fun n : ℕ => Rs n y) atTop (𝓝 (R y))) :
    ∀ x, Tendsto (fun n : ℕ => greenConv c lam (Rs n) x) atTop
      (𝓝 (greenConv c lam R x)) := by
  intro x
  let F : ℕ → ℝ → ℝ := fun n t => greenKernel c lam (-t) * Rs n (x + t)
  let G : ℝ → ℝ := fun t => greenKernel c lam (-t) * R (x + t)
  let bound : ℝ → ℝ := fun t => |greenKernel c lam (-t)| * B
  have hB_nonneg : 0 ≤ B := le_trans (abs_nonneg (R 0)) (hR_bound 0)
  have hbound_int : Integrable bound := by
    have hK : Integrable (fun t => |greenKernel c lam (-t)|) :=
      ((greenKernel_integrable (c := c) hlam).abs).comp_neg
    simpa [bound] using hK.mul_const B
  have hF_meas :
      ∀ᶠ n : ℕ in atTop, AEStronglyMeasurable (F n) volume := by
    refine Eventually.of_forall ?_
    intro n
    exact ((greenKernel_continuous (c := c) (lam := lam)).comp
        (continuous_neg.comp continuous_id) |>.mul
      ((hRs_cont n).comp (continuous_const.add continuous_id))).aestronglyMeasurable
  have h_bound :
      ∀ᶠ n : ℕ in atTop, ∀ᵐ t ∂volume, ‖F n t‖ ≤ bound t := by
    refine Eventually.of_forall ?_
    intro n
    refine Eventually.of_forall ?_
    intro t
    dsimp [F, bound]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hRs_bound n (x + t)) (abs_nonneg _)
  have h_lim :
      ∀ᵐ t ∂volume, Tendsto (fun n : ℕ => F n t) atTop (𝓝 (G t)) := by
    refine Eventually.of_forall ?_
    intro t
    exact (hRs_lim (x + t)).const_mul (greenKernel c lam (-t))
  have hInt_tendsto :
      Tendsto (fun n : ℕ => ∫ t, F n t) atTop (𝓝 (∫ t, G t)) :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (l := atTop) (F := F) (f := G)
      bound hF_meas h_bound hbound_int h_lim
  have hseq :
      (fun n : ℕ => ∫ t, F n t)
        = fun n : ℕ => greenConv c lam (Rs n) x := by
    funext n
    exact (greenConv_eq_translated_integral_of_bounded
      (c := c) (lam := lam) hlam (hRs_cont n) (hRs_bound n) x).symm
  have htarget : (∫ t, G t) = greenConv c lam R x := by
    exact (greenConv_eq_translated_integral_of_bounded
      (c := c) (lam := lam) hlam hR_cont hR_bound x).symm
  simpa [hseq, htarget] using hInt_tendsto

theorem greenConv_tendsto_of_source_locallyUniform_of_uniform_bound
    {c lam : ℝ} (hlam : 0 < lam) {Rs : ℕ → ℝ → ℝ} {R : ℝ → ℝ} {B : ℝ}
    (hRs_cont : ∀ n, Continuous (Rs n))
    (hR_cont : Continuous R)
    (hRs_bound : ∀ n y, |Rs n y| ≤ B)
    (hR_bound : ∀ y, |R y| ≤ B)
    (hRs_lim : LocallyUniformConverges Rs R) :
    ∀ x, Tendsto (fun n : ℕ => greenConv c lam (Rs n) x) atTop
      (𝓝 (greenConv c lam R x)) :=
  greenConv_tendsto_of_source_tendsto_of_uniform_bound
    (c := c) (lam := lam) hlam hRs_cont hR_cont hRs_bound hR_bound
    (fun y => hRs_lim.tendsto_at y)

theorem paperC2CompactUniformBounds_of_greenStep
    {p : CMParams} {c lam κ M Λ : ℝ} {φ U : ℝ → ℝ}
    {z : ℕ → ℝ → ℝ} {R : ℝ → ℝ}
    (hlam : 0 < lam) (hM : 0 < M) (hΛ : 0 ≤ Λ)
    (hU : InLowerPinnedMonotoneTrap κ M φ U)
    (hLU : LocallyUniformConverges z U)
    (hz_nonneg : ∀ k x, 0 ≤ z k x)
    (hz_le_M : ∀ k x, z k x ≤ M)
    (hstep :
      ∀ k, PaperStepAnalytic p c lam M κ Λ U (z k) (z (k + 1)))
    (hR_cont : Continuous R)
    (hR_bound : ∃ B : ℝ,
      (∀ k y, |(hstep k).R y| ≤ B) ∧
        ∀ y, |R y| ≤ B)
    (hR_limit : LocallyUniformConverges (fun k => (hstep k).R) R) :
    PaperC2CompactUniformBounds p U z := by
  obtain ⟨BR, hBRseq, hBR⟩ := hR_bound
  have hshift :
      LocallyUniformConverges (fun k => z (k + 1)) U :=
    hLU.comp_strictMono
      (strictMono_nat_of_lt_succ fun n => Nat.lt_succ_self (n + 1))
  have hU_green : U = fun x => greenConv c lam R x := by
    funext x
    have hz_tendsto :
        Tendsto (fun k : ℕ => z (k + 1) x) atTop (𝓝 (U x)) :=
      hshift.tendsto_at x
    have hz_green_tendsto :
        Tendsto (fun k : ℕ => greenConv c lam (hstep k).R x) atTop
          (𝓝 (U x)) := by
      have hseq :
          (fun k : ℕ => z (k + 1) x) =
            fun k : ℕ => greenConv c lam (hstep k).R x := by
        funext k
        exact congrFun (hstep k).green_repr x
      simpa [hseq] using hz_tendsto
    have hgreen_tendsto :
        Tendsto (fun k : ℕ => greenConv c lam (hstep k).R x) atTop
          (𝓝 (greenConv c lam R x)) :=
      greenConv_tendsto_of_source_locallyUniform_of_uniform_bound
        (c := c) (lam := lam) hlam
        (fun k => (hstep k).R_cont) hR_cont hBRseq hBR hR_limit x
    exact tendsto_nhds_unique hz_green_tendsto hgreen_tendsto
  exact paperC2CompactUniformBounds_of_greenStep_repr
    (p := p) (c := c) (lam := lam) (κ := κ) (M := M) (Λ := Λ)
    (φ := φ) (U := U) (z := z) (R := R)
    hlam hM hΛ hU hLU hz_nonneg hz_le_M hstep hR_cont
    ⟨BR, hBRseq, hBR⟩ hU_green hR_limit

#print axioms paperC2CompactUniformBounds_of_greenStep

end ShenWork.Paper1
