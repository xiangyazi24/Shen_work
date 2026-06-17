import ShenWork.Paper1.WaveLemma42Paper
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

The derivative convergence fields are deliberately absent: they are produced by
`paperC2CompactConvergence_of_uniformBounds` from the derivative equations and
uniform local Lipschitz bounds for the derivative families.  The remaining
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
  deriv2_uniform_lipschitz :
    UniformLipschitzOnCompacts
      (fun k x => iteratedDeriv 2 (z (k + 1)) x)
  deriv2_limit_lipschitz :
    LipschitzOnCompacts (fun x => iteratedDeriv 2 U x)
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

theorem paperC2CompactUniformBounds_of_greenStep
    {p : CMParams} {c lam κ M Λ : ℝ} {φ U : ℝ → ℝ}
    {z : ℕ → ℝ → ℝ}
    (hlam : 0 < lam) (hM : 0 < M) (hΛ : 0 ≤ Λ)
    (hU : InLowerPinnedMonotoneTrap κ M φ U)
    (hLU : LocallyUniformConverges z U)
    (hz_nonneg : ∀ k x, 0 ≤ z k x)
    (hz_le_M : ∀ k x, z k x ≤ M)
    (hstep :
      ∀ k, PaperStepAnalytic p c lam M κ Λ U (z k) (z (k + 1)))
    (hc3 : PaperC3BootstrapData U z) :
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
  obtain ⟨CU1, hCU1_nonneg, hCU1⟩ := hc3.limit_deriv_bound
  obtain ⟨CU2, hCU2_nonneg, hCU2⟩ := hc3.limit_second_bound
  obtain ⟨CZ3, hCZ3_nonneg, hCZ3⟩ := hc3.step_third_bound
  obtain ⟨CU3, hCU3_nonneg, hCU3⟩ := hc3.limit_third_bound
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
      hasDeriv_U := hc3.limit_hasDeriv_value
      hasDeriv_deriv := fun k x =>
        paperStep_hasDerivAt_deriv (hstep k) x
      hasDeriv_deriv_U := hc3.limit_hasDeriv_deriv
      deriv1_uniform_lipschitz :=
        UniformLipschitzOnCompacts.of_hasDerivAt_bound hC2_nonneg
          (fun k x => paperStep_hasDerivAt_deriv (hstep k) x)
          (fun k x =>
            paperStep_second_deriv_le
              (c := c) (lam := lam) hlam hM0 hΛ
              (fun y => hz_abs (k + 1) y) (hstep k) x)
      deriv1_limit_lipschitz :=
        LipschitzOnCompacts.of_hasDerivAt_bound hCU2_nonneg
          hc3.limit_hasDeriv_deriv hCU2
      deriv2_uniform_lipschitz :=
        UniformLipschitzOnCompacts.of_hasDerivAt_bound hCZ3_nonneg
          hc3.step_hasDeriv_deriv2 hCZ3
      deriv2_limit_lipschitz :=
        LipschitzOnCompacts.of_hasDerivAt_bound hCU3_nonneg
          hc3.limit_hasDeriv_deriv2 hCU3
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
  let hderiv2 :
      LocallyUniformConverges
        (fun k x => iteratedDeriv 2 (z (k + 1)) x)
        (fun x => iteratedDeriv 2 U x) :=
    hderiv1.deriv_of_hasDerivAt_of_residual_lipschitz
      hbounds.hasDeriv_deriv hbounds.hasDeriv_deriv_U
      (UniformResidualLipschitzOnCompacts.of_pair
        hbounds.deriv2_uniform_lipschitz hbounds.deriv2_limit_lipschitz)
  { value := hvalue
    deriv1 := hderiv1
    deriv2 := hderiv2
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
#print axioms paperStep_second_deriv_le
#print axioms paperC2CompactUniformBounds_of_greenStep
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

theorem greenConv_eq_translated_integral_of_bounded
    {c lam : ℝ} (hlam : 0 < lam) {H : ℝ → ℝ} {B : ℝ}
    (hH : Continuous H) (hB : ∀ y, |H y| ≤ B) (x : ℝ) :
    greenConv c lam H x =
      ∫ t, greenKernel c lam (-t) * H (x + t) := by
  rw [← greenKernelConv_eq_translated (c := c) (lam := lam) H x]
  exact (greenConv_raw_eq_of_bounded (c := c) (lam := lam) hlam hH hB x).symm

theorem greenConvDeriv_eq_translated_integral_of_bounded
    {c lam : ℝ} (hlam : 0 < lam) {H : ℝ → ℝ} {B : ℝ}
    (hH : Continuous H) (hB : ∀ y, |H y| ≤ B) (x : ℝ) :
    greenConvDeriv c lam H x =
      ∫ t, greenKernelDeriv c lam (-t) * H (x + t) := by
  rw [← greenKernelDerivConv_eq_translated c lam H x]
  exact (greenKernelDerivConv_eq_greenConvDeriv
    (c := c) (lam := lam) hlam hH hB x).symm

theorem greenConv_tendsto_atBot_of_source_tendsto
    {c lam : ℝ} (hlam : 0 < lam) {H : ℝ → ℝ} {B L : ℝ}
    (hH : Continuous H) (hB : ∀ y, |H y| ≤ B)
    (hlim : Tendsto H atBot (𝓝 L)) :
    Tendsto (greenConv c lam H) atBot (𝓝 (L * lam⁻¹)) := by
  let F : ℝ → ℝ → ℝ := fun x t => greenKernel c lam (-t) * H (x + t)
  let G : ℝ → ℝ := fun t => greenKernel c lam (-t) * L
  let bound : ℝ → ℝ := fun t => |greenKernel c lam (-t)| * B
  have hbound_int : Integrable bound := by
    have hK : Integrable (fun t => |greenKernel c lam (-t)|) :=
      ((greenKernel_integrable (c := c) hlam).abs).comp_neg
    simpa [bound] using hK.mul_const B
  have hF_meas :
      ∀ᶠ x in atBot, AEStronglyMeasurable (F x) volume := by
    refine Eventually.of_forall ?_
    intro x
    exact ((greenKernel_continuous (c := c) (lam := lam)).comp
        (continuous_neg.comp continuous_id) |>.mul
      (hH.comp (continuous_const.add continuous_id))).aestronglyMeasurable
  have h_bound :
      ∀ᶠ x in atBot, ∀ᵐ t ∂volume, ‖F x t‖ ≤ bound t := by
    refine Eventually.of_forall ?_
    intro x
    refine Eventually.of_forall ?_
    intro t
    dsimp [F, bound]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hB (x + t)) (abs_nonneg _)
  have h_lim :
      ∀ᵐ t ∂volume, Tendsto (fun x => F x t) atBot (𝓝 (G t)) := by
    refine Eventually.of_forall ?_
    intro t
    have hshift : Tendsto (fun x : ℝ => x + t) atBot atBot :=
      tendsto_atBot_add_const_right atBot t tendsto_id
    exact hlim.comp hshift |>.const_mul (greenKernel c lam (-t))
  have hInt_tendsto :
      Tendsto (fun x => ∫ t, F x t) atBot (𝓝 (∫ t, G t)) :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (l := atBot) (F := F) (f := G)
      bound hF_meas h_bound hbound_int h_lim
  have hGint : (∫ t, G t) = L * lam⁻¹ := by
    dsimp [G]
    rw [show (fun t : ℝ => greenKernel c lam (-t) * L)
        = fun t : ℝ => L * greenKernel c lam (-t) by
          funext t; ring]
    rw [MeasureTheory.integral_const_mul]
    rw [integral_neg_eq_self (greenKernel c lam) volume]
    rw [greenKernel_integral_eq (c := c) hlam]
  have hrewrite :
      (fun x => ∫ t, F x t) = greenConv c lam H := by
    funext x
    exact (greenConv_eq_translated_integral_of_bounded
      (c := c) (lam := lam) hlam hH hB x).symm
  simpa [hrewrite, hGint] using hInt_tendsto

theorem greenConvDeriv_tendsto_atBot_of_source_tendsto
    {c lam : ℝ} (hlam : 0 < lam) {H : ℝ → ℝ} {B L : ℝ}
    (hH : Continuous H) (hB : ∀ y, |H y| ≤ B)
    (hlim : Tendsto H atBot (𝓝 L)) :
    Tendsto (greenConvDeriv c lam H) atBot (𝓝 0) := by
  let F : ℝ → ℝ → ℝ := fun x t => greenKernelDeriv c lam (-t) * H (x + t)
  let G : ℝ → ℝ := fun t => greenKernelDeriv c lam (-t) * L
  let bound : ℝ → ℝ := fun t => |greenKernelDeriv c lam (-t)| * B
  have hbound_int : Integrable bound := by
    have hK : Integrable (fun t => |greenKernelDeriv c lam (-t)|) :=
      (greenKernelDeriv_integrable (c := c) hlam).comp_neg
    simpa [bound] using hK.mul_const B
  have hF_meas :
      ∀ᶠ x in atBot, AEStronglyMeasurable (F x) volume := by
    refine Eventually.of_forall ?_
    intro x
    refine (greenKernelDeriv_measurable (c := c) (lam := lam)).comp measurable_neg
      |>.aestronglyMeasurable.mul ?_
    exact (hH.comp (continuous_const.add continuous_id)).aestronglyMeasurable
  have h_bound :
      ∀ᶠ x in atBot, ∀ᵐ t ∂volume, ‖F x t‖ ≤ bound t := by
    refine Eventually.of_forall ?_
    intro x
    refine Eventually.of_forall ?_
    intro t
    dsimp [F, bound]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hB (x + t)) (abs_nonneg _)
  have h_lim :
      ∀ᵐ t ∂volume, Tendsto (fun x => F x t) atBot (𝓝 (G t)) := by
    refine Eventually.of_forall ?_
    intro t
    have hshift : Tendsto (fun x : ℝ => x + t) atBot atBot :=
      tendsto_atBot_add_const_right atBot t tendsto_id
    exact hlim.comp hshift |>.const_mul (greenKernelDeriv c lam (-t))
  have hInt_tendsto :
      Tendsto (fun x => ∫ t, F x t) atBot (𝓝 (∫ t, G t)) :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (l := atBot) (F := F) (f := G)
      bound hF_meas h_bound hbound_int h_lim
  have hGint : (∫ t, G t) = 0 := by
    dsimp [G]
    rw [show (fun t : ℝ => greenKernelDeriv c lam (-t) * L)
        = fun t : ℝ => L * greenKernelDeriv c lam (-t) by
          funext t; ring]
    rw [MeasureTheory.integral_const_mul]
    rw [integral_neg_eq_self (greenKernelDeriv c lam) volume]
    rw [greenKernelDeriv_integral_eq_zero (c := c) (lam := lam) hlam]
    ring
  have hrewrite :
      (fun x => ∫ t, F x t) = greenConvDeriv c lam H := by
    funext x
    exact (greenConvDeriv_eq_translated_integral_of_bounded
      (c := c) (lam := lam) hlam hH hB x).symm
  simpa [hrewrite, hGint] using hInt_tendsto

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

end ShenWork.Paper1
