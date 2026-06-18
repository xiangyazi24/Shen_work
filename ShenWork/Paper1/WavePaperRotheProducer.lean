/-
  ShenWork/Paper1/WavePaperRotheProducer.lean

  Paper-step producer accounting.

  This module discharges `PaperRotheStepProducer` from a precise Green-step
  input.  The remaining analytic sub-lemma is not the producer itself: it is the
  per-step Green/Schauder fixed-point existence/trap package `PaperGreenStepInput`.

  Frozen-producer inventory: the frozen `RotheStepProducer` is not closed below
  this layer either.  It is assembled from the carried `RotheStepFloor` /
  `RotheStepInput` floor in `WaveRotheStepClose.lean` and
  `WaveRotheProducer.lean`, where the residual Green tails, flux decay/IBP, and
  source data are explicitly named.  Consequently this paper-side input is the
  analogous shared per-step parabolic floor, not a faked fixed-point proof.

  For each old iterate `Z`, that package supplies a Green convolution
  `W = greenConv c lam R` with the paper-step source
  `R = paperStepSource p c lam u Z W`, plus source regularity/tails and the
  super/sub-barrier comparison payload consumed by the clean max principles.

  Delivered here:
  * Green convolution + source identity -> `paperImplicitStepOp ... W = Z`;
  * Green convolution regularity -> continuity, differentiability, `C¹` bound;
  * sliding comparison -> antitone step;
  * paper upper/lower clean max-principles -> `0 ≤ W`, `W ≤ Ū`, `W ≤ Z`;
  * assembly of `PaperRotheStepProducer` from `PaperGreenStepInput`.

  No placeholder proof commands.
-/
import ShenWork.Paper1.WaveRotheStepClose
import ShenWork.Paper1.WaveRotheResidualClose
import ShenWork.Paper1.WaveRotheMaxPrincipleClosers
import ShenWork.Paper1.WaveG1Bridge

open Filter Topology MeasureTheory Real Set
open scoped BoundedContinuousFunction

noncomputable section

namespace ShenWork.Paper1

variable {c lam : ℝ}

/-! ## The paper-step Green source -/

/-- The non-`W'' + cW'` part of the expanded paper wave operator. -/
def paperStepNonlinearity (p : CMParams) (u W : ℝ → ℝ) (x : ℝ) : ℝ :=
  let V := frozenElliptic p u
  (-p.χ * p.m * (W x) ^ (p.m - 1) * deriv V x * deriv W x
    + W x * (1 - p.χ * (W x) ^ (p.m - 1) * V x
      - ((W x) ^ p.α - p.χ * (W x) ^ (p.m + p.γ - 1))))

/-- The Green source for the paper implicit Euler step. -/
def paperStepSource
    (p : CMParams) (_c lam : ℝ) (u Z W : ℝ → ℝ) (x : ℝ) : ℝ :=
  paperStepNonlinearity p u W x + lam * Z x

/-! ## Weighted-Hölder fixed-source box

The fixed-source Schauder route is on sources, not on raw profiles.  The source
map first turns `R` into `W = greenConv c lam R`; all nonlinear powers are then
evaluated through the spatial clamp
`Θ(x) = clampIcc (upperBarrier κ M x) (W x)`.  The source trap is weighted by
the same upper barrier and uses the faithful case-split Hölder exponent:
`m = 1` and `m ≥ 2` give β = 1, while `1 < m < 2` gives β = m - 1. -/

/-- The Hölder exponent used by the weighted source box.

The endpoint `m = 1` is Lipschitz, not exponent zero.  For `1 < m < 2` the
power `s^(m-1)` is only `(m-1)`-Hölder at zero, and for `m ≥ 2` the bounded
interval gives a Lipschitz modulus. -/
def paperWeightedHolderExponent (p : CMParams) : ℝ :=
  if p.m = 1 then 1 else if p.m < 2 then p.m - 1 else 1

theorem paperWeightedHolderExponent_pos (p : CMParams) :
    0 < paperWeightedHolderExponent p := by
  unfold paperWeightedHolderExponent
  by_cases hm1 : p.m = 1
  · rw [if_pos hm1]
    norm_num
  · rw [if_neg hm1]
    by_cases hm2 : p.m < 2
    · rw [if_pos hm2]
      exact sub_pos.mpr (lt_of_le_of_ne p.hm (Ne.symm hm1))
    · rw [if_neg hm2]
      norm_num

theorem paperWeightedHolderExponent_le_one (p : CMParams) :
    paperWeightedHolderExponent p ≤ 1 := by
  unfold paperWeightedHolderExponent
  by_cases hm1 : p.m = 1
  · rw [if_pos hm1]
  · rw [if_neg hm1]
    by_cases hm2 : p.m < 2
    · rw [if_pos hm2]
      linarith
    · rw [if_neg hm2]

/-- Spatial clamp to `[0, upperBarrier κ M x]`. -/
def paperWeightedClamp (κ M : ℝ) (W : ℝ → ℝ) (x : ℝ) : ℝ :=
  clampIcc (upperBarrier κ M x) (W x)

/-- The non-`W'' + cW'` part of the spatially truncated paper wave operator.

The linear transport still uses the genuine Green profile `W`; only the spatial
profile values inside the powers are clamped to `[0, upperBarrier κ M x]`. -/
def paperStepTruncatedNonlinearity
    (p : CMParams) (_c M κ : ℝ) (u W : ℝ → ℝ) (x : ℝ) : ℝ :=
  let Θ : ℝ → ℝ := paperWeightedClamp κ M W
  let V : ℝ → ℝ := frozenElliptic p u
  (-p.χ * p.m * (Θ x) ^ (p.m - 1) * deriv V x * deriv W x
    + Θ x * (1 - p.χ * (Θ x) ^ (p.m - 1) * V x
      - ((Θ x) ^ p.α - p.χ * (Θ x) ^ (p.m + p.γ - 1))))

/-- The spatially truncated paper wave operator used only for the non-circular
source-box maximum principle. -/
def paperWaveOperator_truncated
    (p : CMParams) (c M κ : ℝ) (u W : ℝ → ℝ) : ℝ → ℝ :=
  fun x =>
    iteratedDeriv 2 W x + c * deriv W x +
      paperStepTruncatedNonlinearity p c M κ u W x

/-- The implicit Euler residual for the spatially truncated paper operator. -/
def paperImplicitStepOp_truncated
    (p : CMParams) (c h M κ : ℝ) (u W : ℝ → ℝ) : ℝ → ℝ :=
  fun x => W x - h * paperWaveOperator_truncated p c M κ u W x

@[simp] theorem paperImplicitStepOp_truncated_apply
    (p : CMParams) (c h M κ : ℝ) (u W : ℝ → ℝ) (x : ℝ) :
    paperImplicitStepOp_truncated p c h M κ u W x =
      W x - h * paperWaveOperator_truncated p c M κ u W x := rfl

/-- The weighted-Hölder source-space box for the corrected fixed-source step.

Besides the weighted right-tail bound and the shared Hölder modulus, the box
records a genuine left limit and a uniform left-tail Cauchy modulus.  The
function `ω` is shared by the whole box; `leftTailCauchy` is the equi-convergence
input used by the source-space Arzelà-Ascoli step on the compactified line. -/
structure PaperWeightedHolderSourceBox
    (κ M β B H : ℝ) (ω : ℝ → ℝ) (R : ℝ → ℝ) : Prop where
  cont : Continuous R
  bound : ∀ x, |R x| ≤ B * upperBarrier κ M x
  holder : ∀ x y, |R x - R y| ≤ H * |x - y| ^ β
  omega_nonneg : ∀ A, 0 ≤ ω A
  omega_tendsto : Tendsto ω atBot (𝓝 0)
  leftTail : ∃ Rm, Tendsto R atBot (𝓝 Rm)
  leftTailCauchy : ∀ A x y, x ≤ A → y ≤ A → |R x - R y| ≤ ω A

/-- The paper source with the Green profile spatially clamped to
`[0, upperBarrier κ M x]`. -/
def paperStepSource_truncated
    (p : CMParams) (c lam M κ : ℝ) (u Z R : ℝ → ℝ) (x : ℝ) : ℝ :=
  let W : ℝ → ℝ := fun y => greenConv c lam R y
  paperStepTruncatedNonlinearity p c M κ u W x + lam * Z x

/-- The weighted fixed-source map on source profiles. -/
def paperFixedSourceMap
    (p : CMParams) (c lam M κ : ℝ) (u Z : ℝ → ℝ) (R : ℝ → ℝ) : ℝ → ℝ :=
  paperStepSource_truncated p c lam M κ u Z R

/-- On a profile already trapped by the spatial upper barrier, the weighted
truncated paper source is the genuine paper source. -/
theorem paperStepSource_truncated_eq_paperStepSource_of_Icc
    (p : CMParams) {c lam M κ : ℝ} {u Z R : ℝ → ℝ}
    (hM : 0 ≤ M)
    (hW : ∀ x,
      (fun y => greenConv c lam R y) x ∈ Set.Icc (0 : ℝ) (upperBarrier κ M x)) :
    paperFixedSourceMap p c lam M κ u Z R =
      paperStepSource p c lam u Z (fun x => greenConv c lam R x) := by
  funext x
  have hclamp :
      clampIcc (upperBarrier κ M x) (greenConv c lam R x) =
        greenConv c lam R x := by
    exact (clampIcc_eqOn_Icc (M := upperBarrier κ M x)
      (upperBarrier_nonneg hM x)) (hW x)
  unfold paperFixedSourceMap paperStepSource_truncated paperStepTruncatedNonlinearity
    paperWeightedClamp paperStepSource paperStepNonlinearity
  dsimp only
  rw [hclamp]

theorem rpowTrunc_continuous {a M : ℝ} (ha : 0 ≤ a) :
    Continuous (rpowTrunc a M) := by
  unfold rpowTrunc
  exact (clampIcc_lipschitz M).continuous.rpow_const (fun _ => Or.inr ha)

theorem rpowTrunc_abs_le {a M s : ℝ} (hM : 0 ≤ M) (ha : 0 ≤ a) :
    |rpowTrunc a M s| ≤ M ^ a := by
  have hclamp := clampIcc_mem_Icc hM s
  unfold rpowTrunc
  have hpow_nonneg : 0 ≤ (clampIcc M s) ^ a :=
    Real.rpow_nonneg hclamp.1 a
  rw [abs_of_nonneg hpow_nonneg]
  exact Real.rpow_le_rpow hclamp.1 hclamp.2 ha

theorem paperWeightedClamp_mem_Icc
    {κ M : ℝ} {W : ℝ → ℝ} (hM : 0 ≤ M) (x : ℝ) :
    paperWeightedClamp κ M W x ∈
      Set.Icc (0 : ℝ) (upperBarrier κ M x) := by
  unfold paperWeightedClamp
  exact clampIcc_mem_Icc (upperBarrier_nonneg hM x) (W x)

theorem paperWeightedClamp_eq_upperBarrier_of_upper_le
    {κ M : ℝ} {W : ℝ → ℝ} (hM : 0 ≤ M) {x : ℝ}
    (hx : upperBarrier κ M x ≤ W x) :
    paperWeightedClamp κ M W x = upperBarrier κ M x := by
  unfold paperWeightedClamp clampIcc
  rw [min_eq_left hx, max_eq_right (upperBarrier_nonneg hM x)]

theorem paperWeightedClamp_eq_zero_of_nonpos
    {κ M : ℝ} {W : ℝ → ℝ} (hM : 0 ≤ M) {x : ℝ}
    (hx : W x ≤ 0) :
    paperWeightedClamp κ M W x = 0 := by
  unfold paperWeightedClamp clampIcc
  have hWU : W x ≤ upperBarrier κ M x :=
    le_trans hx (upperBarrier_nonneg hM x)
  rw [min_eq_right hWU, max_eq_left hx]

theorem paperWeightedClamp_abs_le_upperBarrier
    {κ M : ℝ} {W : ℝ → ℝ} (hM : 0 ≤ M) (x : ℝ) :
    |paperWeightedClamp κ M W x| ≤ upperBarrier κ M x := by
  have hmem := paperWeightedClamp_mem_Icc (κ := κ) (M := M) (W := W) hM x
  rw [abs_of_nonneg hmem.1]
  exact hmem.2

theorem paperWeightedClamp_rpow_abs_le_M
    {κ M a : ℝ} {W : ℝ → ℝ} (hM : 0 ≤ M) (ha : 0 ≤ a) (x : ℝ) :
    |(paperWeightedClamp κ M W x) ^ a| ≤ M ^ a := by
  have hmem := paperWeightedClamp_mem_Icc (κ := κ) (M := M) (W := W) hM x
  have hθM : paperWeightedClamp κ M W x ≤ M :=
    le_trans hmem.2 (upperBarrier_le_M κ M x)
  have hpownn : 0 ≤ (paperWeightedClamp κ M W x) ^ a :=
    Real.rpow_nonneg hmem.1 a
  rw [abs_of_nonneg hpownn]
  exact Real.rpow_le_rpow hmem.1 hθM ha

theorem rpow_abs_sub_le_lip_on_Icc
    {a M s t : ℝ} (ha : 1 ≤ a) (hM : 0 ≤ M)
    (hs : s ∈ Set.Icc (0 : ℝ) M) (ht : t ∈ Set.Icc (0 : ℝ) M) :
    |s ^ a - t ^ a| ≤ rpowLip a M * |s - t| := by
  have hLip := rpow_m_lipschitz_on_Icc (m := a) (M := M) ha hM
  have hL0 : 0 ≤ rpowLip a M := rpowLip_nonneg ha hM
  have hdist := hLip hs ht
  rw [edist_dist, edist_dist] at hdist
  have hd : dist (s ^ a) (t ^ a) ≤
      (Real.toNNReal (rpowLip a M) : ℝ) * dist s t := by
    have := hdist
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at this
    exact this
  rw [Real.coe_toNNReal _ hL0] at hd
  simpa [Real.dist_eq] using hd

theorem rpow_abs_sub_le_abs_sub_rpow
    {a s t : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hs0 : 0 ≤ s) (ht0 : 0 ≤ t) :
    |s ^ a - t ^ a| ≤ |s - t| ^ a := by
  by_cases hst : s ≤ t
  · have hdiff0 : 0 ≤ t - s := sub_nonneg.mpr hst
    have hmono : s ^ a ≤ t ^ a := Real.rpow_le_rpow hs0 hst ha0
    have hconc :
        (s + (t - s)) ^ a ≤ s ^ a + (t - s) ^ a :=
      rpow_add_le_add_rpow hs0 hdiff0 ha0 ha1
    have ht_eq : s + (t - s) = t := by ring
    have hsub : t ^ a - s ^ a ≤ (t - s) ^ a := by
      rw [ht_eq] at hconc
      linarith
    rw [abs_of_nonpos (sub_nonpos.mpr hmono)]
    have habs : |s - t| = t - s := by
      rw [abs_of_nonpos (sub_nonpos.mpr hst)]
      ring
    simpa [habs] using hsub
  · have hts : t ≤ s := le_of_not_ge hst
    have hdiff0 : 0 ≤ s - t := sub_nonneg.mpr hts
    have hmono : t ^ a ≤ s ^ a := Real.rpow_le_rpow ht0 hts ha0
    have hconc :
        (t + (s - t)) ^ a ≤ t ^ a + (s - t) ^ a :=
      rpow_add_le_add_rpow ht0 hdiff0 ha0 ha1
    have hs_eq : t + (s - t) = s := by ring
    have hsub : s ^ a - t ^ a ≤ (s - t) ^ a := by
      rw [hs_eq] at hconc
      linarith
    rw [abs_of_nonneg (sub_nonneg.mpr hmono)]
    have habs : |s - t| = s - t := abs_of_nonneg hdiff0
    simpa [habs] using hsub

theorem upperBarrier_shift_le_exp_abs_mul
    {κ M x y : ℝ} (hκ : 0 ≤ κ) (hM : 0 ≤ M) :
    upperBarrier κ M y ≤
      Real.exp (κ * |x - y|) * upperBarrier κ M x := by
  by_cases hxM : M ≤ Real.exp (-κ * x)
  · rw [upperBarrier_eq_M_of_le_exp hxM]
    have hC : 1 ≤ Real.exp (κ * |x - y|) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (mul_nonneg hκ (abs_nonneg _))
    calc
      upperBarrier κ M y ≤ M := upperBarrier_le_M κ M y
      _ = 1 * M := by ring
      _ ≤ Real.exp (κ * |x - y|) * M :=
        mul_le_mul_of_nonneg_right hC hM
  · have hxexp : Real.exp (-κ * x) ≤ M := (not_le.mp hxM).le
    rw [upperBarrier_eq_exp_of_exp_le hxexp]
    have hxy : x - y ≤ |x - y| := le_abs_self (x - y)
    have hmul : κ * (x - y) ≤ κ * |x - y| :=
      mul_le_mul_of_nonneg_left hxy hκ
    have hexp_arg : -κ * y ≤ κ * |x - y| + -κ * x := by
      linarith
    calc
      upperBarrier κ M y ≤ Real.exp (-κ * y) := upperBarrier_le_exp κ M y
      _ ≤ Real.exp (κ * |x - y| + -κ * x) :=
        Real.exp_le_exp.mpr hexp_arg
      _ = Real.exp (κ * |x - y|) * Real.exp (-κ * x) := by
        rw [Real.exp_add]

theorem exp_sub_one_le_self_mul_exp (t : ℝ) :
    Real.exp t - 1 ≤ t * Real.exp t := by
  have hsmall : 1 - Real.exp (-t) ≤ t := by
    have h := Real.add_one_le_exp (-t)
    linarith
  have hrewrite : Real.exp t - 1 = Real.exp t * (1 - Real.exp (-t)) := by
    rw [mul_sub, ← Real.exp_add]
    rw [show t + -t = 0 by ring, Real.exp_zero]
    ring
  rw [hrewrite]
  calc
    Real.exp t * (1 - Real.exp (-t)) ≤ Real.exp t * t :=
      mul_le_mul_of_nonneg_left hsmall (Real.exp_pos _).le
    _ = t * Real.exp t := by ring

theorem upperBarrier_abs_sub_le_local
    {κ M x y : ℝ} (hκ : 0 ≤ κ) (hM : 0 ≤ M)
    (hxy : |x - y| ≤ 1) :
    |upperBarrier κ M x - upperBarrier κ M y| ≤
      (κ * Real.exp κ * M) * |x - y| := by
  set d : ℝ := |x - y| with hd
  have hd0 : 0 ≤ d := by simpa [hd] using abs_nonneg (x - y)
  have htd0 : 0 ≤ κ * d := mul_nonneg hκ hd0
  have htd_le : κ * d ≤ κ := by
    calc
      κ * d ≤ κ * 1 := mul_le_mul_of_nonneg_left (by simpa [hd] using hxy) hκ
      _ = κ := by ring
  have hexp_minus :
      Real.exp (κ * d) - 1 ≤ κ * d * Real.exp κ := by
    calc
      Real.exp (κ * d) - 1 ≤ (κ * d) * Real.exp (κ * d) :=
        exp_sub_one_le_self_mul_exp (κ * d)
      _ ≤ (κ * d) * Real.exp κ := by
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr htd_le) htd0
      _ = κ * d * Real.exp κ := by ring
  have hminus_nonneg : 0 ≤ Real.exp (κ * d) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp htd0)
  have hkde_nonneg : 0 ≤ κ * d * Real.exp κ := by positivity
  have hUx0 : 0 ≤ upperBarrier κ M x := upperBarrier_nonneg hM x
  have hUy0 : 0 ≤ upperBarrier κ M y := upperBarrier_nonneg hM y
  have hUxM : upperBarrier κ M x ≤ M := upperBarrier_le_M κ M x
  have hUyM : upperBarrier κ M y ≤ M := upperBarrier_le_M κ M y
  have hyx :
      upperBarrier κ M y - upperBarrier κ M x ≤
        (κ * Real.exp κ * M) * d := by
    have hshift := upperBarrier_shift_le_exp_abs_mul
      (κ := κ) (M := M) (x := x) (y := y) hκ hM
    have hstep :
        upperBarrier κ M y - upperBarrier κ M x ≤
          (Real.exp (κ * d) - 1) * upperBarrier κ M x := by
      calc
        upperBarrier κ M y - upperBarrier κ M x
            ≤ Real.exp (κ * d) * upperBarrier κ M x -
                upperBarrier κ M x := by
              exact sub_le_sub_right (by simpa [hd] using hshift) _
        _ = (Real.exp (κ * d) - 1) * upperBarrier κ M x := by ring
    calc
      upperBarrier κ M y - upperBarrier κ M x
          ≤ (Real.exp (κ * d) - 1) * upperBarrier κ M x := hstep
      _ ≤ (κ * d * Real.exp κ) * upperBarrier κ M x := by
            exact mul_le_mul_of_nonneg_right hexp_minus hUx0
      _ ≤ (κ * d * Real.exp κ) * M := by
            exact mul_le_mul_of_nonneg_left hUxM hkde_nonneg
      _ = (κ * Real.exp κ * M) * d := by ring
  have hxy' :
      upperBarrier κ M x - upperBarrier κ M y ≤
        (κ * Real.exp κ * M) * d := by
    have hshift := upperBarrier_shift_le_exp_abs_mul
      (κ := κ) (M := M) (x := y) (y := x) hκ hM
    have hstep :
        upperBarrier κ M x - upperBarrier κ M y ≤
          (Real.exp (κ * d) - 1) * upperBarrier κ M y := by
      calc
        upperBarrier κ M x - upperBarrier κ M y
            ≤ Real.exp (κ * d) * upperBarrier κ M y -
                upperBarrier κ M y := by
              have hsym : |y - x| = d := by
                rw [hd, abs_sub_comm]
              exact sub_le_sub_right (by simpa [hsym] using hshift) _
        _ = (Real.exp (κ * d) - 1) * upperBarrier κ M y := by ring
    calc
      upperBarrier κ M x - upperBarrier κ M y
          ≤ (Real.exp (κ * d) - 1) * upperBarrier κ M y := hstep
      _ ≤ (κ * d * Real.exp κ) * upperBarrier κ M y := by
            exact mul_le_mul_of_nonneg_right hexp_minus hUy0
      _ ≤ (κ * d * Real.exp κ) * M := by
            exact mul_le_mul_of_nonneg_left hUyM hkde_nonneg
      _ = (κ * Real.exp κ * M) * d := by ring
  rw [abs_le]
  constructor
  · have := hyx
    linarith
  · simpa [hd] using hxy'

/-! ### Pointwise Hölder bookkeeping for fixed-source kernel estimates -/

/-- A real function with a uniform absolute bound and a global Hölder modulus. -/
structure HolderQuant (β : ℝ) (f : ℝ → ℝ) where
  C : ℝ
  H : ℝ
  C_nonneg : 0 ≤ C
  H_nonneg : 0 ≤ H
  bound : ∀ x, |f x| ≤ C
  holder : ∀ x y, |f x - f y| ≤ H * |x - y| ^ β

structure HolderBudget where
  C : ℝ
  H : ℝ
  C_nonneg : 0 ≤ C
  H_nonneg : 0 ≤ H

namespace HolderBudget

def const (a : ℝ) : HolderBudget where
  C := |a|
  H := 0
  C_nonneg := abs_nonneg a
  H_nonneg := le_rfl

def add (hf hg : HolderBudget) : HolderBudget where
  C := hf.C + hg.C
  H := hf.H + hg.H
  C_nonneg := add_nonneg hf.C_nonneg hg.C_nonneg
  H_nonneg := add_nonneg hf.H_nonneg hg.H_nonneg

def neg (hf : HolderBudget) : HolderBudget := hf

def sub (hf hg : HolderBudget) : HolderBudget :=
  hf.add hg.neg

def const_mul (a : ℝ) (hf : HolderBudget) : HolderBudget where
  C := |a| * hf.C
  H := |a| * hf.H
  C_nonneg := mul_nonneg (abs_nonneg a) hf.C_nonneg
  H_nonneg := mul_nonneg (abs_nonneg a) hf.H_nonneg

def mul (hf hg : HolderBudget) : HolderBudget where
  C := hf.C * hg.C
  H := hf.C * hg.H + hg.C * hf.H
  C_nonneg := mul_nonneg hf.C_nonneg hg.C_nonneg
  H_nonneg :=
    add_nonneg (mul_nonneg hf.C_nonneg hg.H_nonneg)
      (mul_nonneg hg.C_nonneg hf.H_nonneg)

end HolderBudget

namespace HolderQuant

def const (β a : ℝ) : HolderQuant β (fun _ : ℝ => a) where
  C := |a|
  H := 0
  C_nonneg := abs_nonneg a
  H_nonneg := le_rfl
  bound := by intro x; simp
  holder := by intro x y; simp

def add {β : ℝ} {f g : ℝ → ℝ}
    (hf : HolderQuant β f) (hg : HolderQuant β g) :
    HolderQuant β (fun x => f x + g x) where
  C := hf.C + hg.C
  H := hf.H + hg.H
  C_nonneg := add_nonneg hf.C_nonneg hg.C_nonneg
  H_nonneg := add_nonneg hf.H_nonneg hg.H_nonneg
  bound := by
    intro x
    calc
      |f x + g x| ≤ |f x| + |g x| := abs_add_le _ _
      _ ≤ hf.C + hg.C := add_le_add (hf.bound x) (hg.bound x)
  holder := by
    intro x y
    calc
      |(f x + g x) - (f y + g y)|
          = |(f x - f y) + (g x - g y)| := by ring_nf
      _ ≤ |f x - f y| + |g x - g y| := abs_add_le _ _
      _ ≤ hf.H * |x - y| ^ β + hg.H * |x - y| ^ β :=
        add_le_add (hf.holder x y) (hg.holder x y)
      _ = (hf.H + hg.H) * |x - y| ^ β := by ring

def neg {β : ℝ} {f : ℝ → ℝ} (hf : HolderQuant β f) :
    HolderQuant β (fun x => -f x) where
  C := hf.C
  H := hf.H
  C_nonneg := hf.C_nonneg
  H_nonneg := hf.H_nonneg
  bound := by intro x; simpa using hf.bound x
  holder := by
    intro x y
    have hdiff : (-f x) - (-f y) = -(f x - f y) := by ring
    rw [hdiff, abs_neg]
    exact hf.holder x y

def sub {β : ℝ} {f g : ℝ → ℝ}
    (hf : HolderQuant β f) (hg : HolderQuant β g) :
    HolderQuant β (fun x => f x - g x) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

def const_mul {β a : ℝ} {f : ℝ → ℝ} (hf : HolderQuant β f) :
    HolderQuant β (fun x => a * f x) where
  C := |a| * hf.C
  H := |a| * hf.H
  C_nonneg := mul_nonneg (abs_nonneg a) hf.C_nonneg
  H_nonneg := mul_nonneg (abs_nonneg a) hf.H_nonneg
  bound := by
    intro x
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hf.bound x) (abs_nonneg a)
  holder := by
    intro x y
    rw [← mul_sub, abs_mul]
    calc
      |a| * |f x - f y| ≤ |a| * (hf.H * |x - y| ^ β) :=
        mul_le_mul_of_nonneg_left (hf.holder x y) (abs_nonneg a)
      _ = |a| * hf.H * |x - y| ^ β := by ring

def mul {β : ℝ} {f g : ℝ → ℝ}
    (hf : HolderQuant β f) (hg : HolderQuant β g) :
    HolderQuant β (fun x => f x * g x) where
  C := hf.C * hg.C
  H := hf.C * hg.H + hg.C * hf.H
  C_nonneg := mul_nonneg hf.C_nonneg hg.C_nonneg
  H_nonneg :=
    add_nonneg (mul_nonneg hf.C_nonneg hg.H_nonneg)
      (mul_nonneg hg.C_nonneg hf.H_nonneg)
  bound := by
    intro x
    rw [abs_mul]
    exact mul_le_mul (hf.bound x) (hg.bound x)
      (abs_nonneg _) hf.C_nonneg
  holder := by
    intro x y
    have hsplit :
        f x * g x - f y * g y =
          f x * (g x - g y) + g y * (f x - f y) := by ring
    rw [hsplit]
    calc
      |f x * (g x - g y) + g y * (f x - f y)|
          ≤ |f x * (g x - g y)| + |g y * (f x - f y)| := abs_add_le _ _
      _ = |f x| * |g x - g y| + |g y| * |f x - f y| := by
        rw [abs_mul, abs_mul]
      _ ≤ hf.C * (hg.H * |x - y| ^ β) +
            hg.C * (hf.H * |x - y| ^ β) := by
        exact add_le_add
          (mul_le_mul (hf.bound x) (hg.holder x y)
            (abs_nonneg _) hf.C_nonneg)
          (mul_le_mul (hg.bound y) (hf.holder x y)
            (abs_nonneg _) hg.C_nonneg)
      _ = (hf.C * hg.H + hg.C * hf.H) * |x - y| ^ β := by ring

def inflate {β : ℝ} {f : ℝ → ℝ} (hf : HolderQuant β f)
    {C' H' : ℝ} (hC' : 0 ≤ C') (hH' : 0 ≤ H')
    (hC : hf.C ≤ C') (hH : hf.H ≤ H') :
    HolderQuant β f where
  C := C'
  H := H'
  C_nonneg := hC'
  H_nonneg := hH'
  bound := by
    intro x
    exact le_trans (hf.bound x) hC
  holder := by
    intro x y
    calc
      |f x - f y| ≤ hf.H * |x - y| ^ β := hf.holder x y
      _ ≤ H' * |x - y| ^ β :=
        mul_le_mul_of_nonneg_right hH (Real.rpow_nonneg (abs_nonneg _) β)

end HolderQuant

theorem abs_sub_le_two_bounds {f : ℝ → ℝ} {C : ℝ}
    (_hC : 0 ≤ C) (hf : ∀ x, |f x| ≤ C) (x y : ℝ) :
    |f x - f y| ≤ 2 * C := by
  calc
    |f x - f y| ≤ |f x| + |f y| := abs_sub _ _
    _ ≤ C + C := add_le_add (hf x) (hf y)
    _ = 2 * C := by ring

/-- A bounded Lipschitz estimate is a global β-Hölder estimate for `0 < β ≤ 1`. -/
theorem holder_of_lipschitz_of_bounded
    {β L C : ℝ} {f : ℝ → ℝ}
    (hβpos : 0 < β) (hβle : β ≤ 1) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hbound : ∀ x, |f x| ≤ C)
    (hlip : ∀ x y, |f x - f y| ≤ L * |x - y|) :
    ∀ x y, |f x - f y| ≤ max L (2 * C) * |x - y| ^ β := by
  intro x y
  set d : ℝ := |x - y| with hd
  have hd0 : 0 ≤ d := by simpa [hd] using abs_nonneg (x - y)
  have hcoefL : L ≤ max L (2 * C) := le_max_left _ _
  have hcoefC : 2 * C ≤ max L (2 * C) := le_max_right _ _
  by_cases hdle : d ≤ 1
  · have hd_pow_ge : d ≤ d ^ β := by
      by_cases hdz : d = 0
      · rw [hdz]
        exact Real.rpow_nonneg (le_refl 0) β
      · have hdpos : 0 < d := lt_of_le_of_ne hd0 (Ne.symm hdz)
        calc
          d = d ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ ≤ d ^ β := by
            exact Real.rpow_le_rpow_of_exponent_ge hdpos hdle hβle
    calc
      |f x - f y| ≤ L * d := by simpa [hd] using hlip x y
      _ ≤ L * d ^ β := mul_le_mul_of_nonneg_left hd_pow_ge hL
      _ ≤ max L (2 * C) * d ^ β :=
        mul_le_mul_of_nonneg_right hcoefL (Real.rpow_nonneg hd0 β)
  · have hone_le_d : 1 ≤ d := le_of_not_ge hdle
    have hone_le_pow : 1 ≤ d ^ β := by
      calc
        (1 : ℝ) = (1 : ℝ) ^ β := by rw [Real.one_rpow]
        _ ≤ d ^ β := Real.rpow_le_rpow zero_le_one hone_le_d hβpos.le
    calc
      |f x - f y| ≤ 2 * C := abs_sub_le_two_bounds hC hbound x y
      _ ≤ max L (2 * C) := hcoefC
      _ ≤ max L (2 * C) * d ^ β := by
        have hcoef_nonneg : 0 ≤ max L (2 * C) :=
          le_trans hL hcoefL
        calc
          max L (2 * C) = max L (2 * C) * 1 := by ring
          _ ≤ max L (2 * C) * d ^ β :=
            mul_le_mul_of_nonneg_left hone_le_pow hcoef_nonneg

/-- A bounded locally-Lipschitz estimate on unit spatial scales is a global
β-Hölder estimate for `0 < β ≤ 1`. -/
theorem holder_of_local_lipschitz_of_bounded
    {β L C : ℝ} {f : ℝ → ℝ}
    (hβpos : 0 < β) (hβle : β ≤ 1) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hbound : ∀ x, |f x| ≤ C)
    (hlip : ∀ x y, |x - y| ≤ 1 → |f x - f y| ≤ L * |x - y|) :
    ∀ x y, |f x - f y| ≤ max L (2 * C) * |x - y| ^ β := by
  intro x y
  set d : ℝ := |x - y| with hd
  have hd0 : 0 ≤ d := by simpa [hd] using abs_nonneg (x - y)
  have hcoefL : L ≤ max L (2 * C) := le_max_left _ _
  have hcoefC : 2 * C ≤ max L (2 * C) := le_max_right _ _
  by_cases hdle : d ≤ 1
  · have hd_pow_ge : d ≤ d ^ β := by
      by_cases hdz : d = 0
      · rw [hdz]
        exact Real.rpow_nonneg (le_refl 0) β
      · have hdpos : 0 < d := lt_of_le_of_ne hd0 (Ne.symm hdz)
        calc
          d = d ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ ≤ d ^ β := by
            exact Real.rpow_le_rpow_of_exponent_ge hdpos hdle hβle
    calc
      |f x - f y| ≤ L * d := by
        simpa [hd] using hlip x y (by simpa [hd] using hdle)
      _ ≤ L * d ^ β := mul_le_mul_of_nonneg_left hd_pow_ge hL
      _ ≤ max L (2 * C) * d ^ β :=
        mul_le_mul_of_nonneg_right hcoefL (Real.rpow_nonneg hd0 β)
  · have hone_le_d : 1 ≤ d := le_of_not_ge hdle
    have hone_le_pow : 1 ≤ d ^ β := by
      calc
        (1 : ℝ) = (1 : ℝ) ^ β := by rw [Real.one_rpow]
        _ ≤ d ^ β := Real.rpow_le_rpow zero_le_one hone_le_d hβpos.le
    calc
      |f x - f y| ≤ 2 * C := abs_sub_le_two_bounds hC hbound x y
      _ ≤ max L (2 * C) := hcoefC
      _ ≤ max L (2 * C) * d ^ β := by
        have hcoef_nonneg : 0 ≤ max L (2 * C) :=
          le_trans hL hcoefL
        calc
          max L (2 * C) = max L (2 * C) * 1 := by ring
          _ ≤ max L (2 * C) * d ^ β :=
            mul_le_mul_of_nonneg_left hone_le_pow hcoef_nonneg

theorem abs_sub_le_of_deriv_abs_le_core
    {f : ℝ → ℝ} {A : ℝ}
    (hf : Differentiable ℝ f) (hderiv : ∀ x, |deriv f x| ≤ A) :
    ∀ x y, |f x - f y| ≤ A * |x - y| := by
  intro x y
  have h :=
    Convex.norm_image_sub_le_of_norm_deriv_le
      (𝕜 := ℝ) (G := ℝ) (f := f) (s := Set.univ)
      (x := y) (y := x)
      (fun z _hz => hf z)
      (fun z _hz => by simpa [Real.norm_eq_abs] using hderiv z)
      convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa [Real.norm_eq_abs, abs_sub_comm] using h

structure LocalLipQuant (f : ℝ → ℝ) where
  C : ℝ
  L : ℝ
  C_nonneg : 0 ≤ C
  L_nonneg : 0 ≤ L
  bound : ∀ x, |f x| ≤ C
  local_lip : ∀ x y, |x - y| ≤ 1 → |f x - f y| ≤ L * |x - y|

namespace LocalLipQuant

def toHolder
    {β : ℝ} {f : ℝ → ℝ} (q : LocalLipQuant f)
    (hβpos : 0 < β) (hβle : β ≤ 1) :
    HolderQuant β f where
  C := q.C
  H := max q.L (2 * q.C)
  C_nonneg := q.C_nonneg
  H_nonneg := le_trans q.L_nonneg (le_max_left _ _)
  bound := q.bound
  holder :=
    holder_of_local_lipschitz_of_bounded hβpos hβle q.L_nonneg q.C_nonneg
      q.bound q.local_lip

def of_lipschitz
    {C L : ℝ} {f : ℝ → ℝ}
    (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hbound : ∀ x, |f x| ≤ C)
    (hlip : ∀ x y, |f x - f y| ≤ L * |x - y|) :
    LocalLipQuant f where
  C := C
  L := L
  C_nonneg := hC
  L_nonneg := hL
  bound := hbound
  local_lip := fun x y _ => hlip x y

end LocalLipQuant

def upperBarrier_localLipQuant
    {κ M : ℝ} (hκ : 0 ≤ κ) (hM : 0 ≤ M) :
    LocalLipQuant (upperBarrier κ M) where
  C := M
  L := κ * Real.exp κ * M
  C_nonneg := hM
  L_nonneg := by positivity
  bound := by
    intro x
    rw [abs_of_nonneg (upperBarrier_nonneg hM x)]
    exact upperBarrier_le_M κ M x
  local_lip := fun x y hxy => upperBarrier_abs_sub_le_local hκ hM hxy

theorem paperWeightedClamp_abs_sub_le
    {κ M : ℝ} {W : ℝ → ℝ} (x y : ℝ) :
    |paperWeightedClamp κ M W x - paperWeightedClamp κ M W y| ≤
      |upperBarrier κ M x - upperBarrier κ M y| + |W x - W y| := by
  unfold paperWeightedClamp clampIcc
  have hmax := abs_max_sub_max_le_max (0 : ℝ)
    (min (upperBarrier κ M x) (W x)) (0 : ℝ)
    (min (upperBarrier κ M y) (W y))
  have hmin := abs_min_sub_min_le_max (upperBarrier κ M x) (W x)
    (upperBarrier κ M y) (W y)
  calc
    |max 0 (min (upperBarrier κ M x) (W x)) -
        max 0 (min (upperBarrier κ M y) (W y))|
        ≤ max |(0 : ℝ) - 0|
            |min (upperBarrier κ M x) (W x) -
              min (upperBarrier κ M y) (W y)| := hmax
    _ = |min (upperBarrier κ M x) (W x) -
          min (upperBarrier κ M y) (W y)| := by simp
    _ ≤ max |upperBarrier κ M x - upperBarrier κ M y| |W x - W y| := hmin
    _ ≤ |upperBarrier κ M x - upperBarrier κ M y| + |W x - W y| := by
      exact max_le (le_add_of_nonneg_right (abs_nonneg _))
        (le_add_of_nonneg_left (abs_nonneg _))

def paperWeightedClamp_localLipQuant
    {κ M : ℝ} {W : ℝ → ℝ} (hM : 0 ≤ M)
    (hU : LocalLipQuant (upperBarrier κ M)) (hW : LocalLipQuant W) :
    LocalLipQuant (fun x => paperWeightedClamp κ M W x) where
  C := M
  L := hU.L + hW.L
  C_nonneg := hM
  L_nonneg := add_nonneg hU.L_nonneg hW.L_nonneg
  bound := by
    intro x
    have hmem := paperWeightedClamp_mem_Icc (κ := κ) (M := M) (W := W) hM x
    rw [abs_of_nonneg hmem.1]
    exact le_trans hmem.2 (upperBarrier_le_M κ M x)
  local_lip := by
    intro x y hxy
    calc
      |paperWeightedClamp κ M W x - paperWeightedClamp κ M W y|
          ≤ |upperBarrier κ M x - upperBarrier κ M y| + |W x - W y| :=
        paperWeightedClamp_abs_sub_le x y
      _ ≤ hU.L * |x - y| + hW.L * |x - y| :=
        add_le_add (hU.local_lip x y hxy) (hW.local_lip x y hxy)
      _ = (hU.L + hW.L) * |x - y| := by ring

def HolderQuant.of_lipschitz
    {β C L : ℝ} {f : ℝ → ℝ}
    (hβpos : 0 < β) (hβle : β ≤ 1)
    (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hbound : ∀ x, |f x| ≤ C)
    (hlip : ∀ x y, |f x - f y| ≤ L * |x - y|) :
    HolderQuant β f where
  C := C
  H := max L (2 * C)
  C_nonneg := hC
  H_nonneg := le_trans hL (le_max_left _ _)
  bound := hbound
  holder := holder_of_lipschitz_of_bounded hβpos hβle hL hC hbound hlip

def HolderQuant.rpow_lipschitz_on_Icc
    {β a M : ℝ} {f : ℝ → ℝ}
    (hf : HolderQuant β f) (ha : 1 ≤ a) (hM : 0 ≤ M)
    (hrange : ∀ x, f x ∈ Set.Icc (0 : ℝ) M) :
    HolderQuant β (fun x => (f x) ^ a) where
  C := M ^ a
  H := rpowLip a M * hf.H
  C_nonneg := Real.rpow_nonneg hM a
  H_nonneg := mul_nonneg (rpowLip_nonneg ha hM) hf.H_nonneg
  bound := by
    intro x
    have hx := hrange x
    have hpownn : 0 ≤ (f x) ^ a := Real.rpow_nonneg hx.1 a
    rw [abs_of_nonneg hpownn]
    exact Real.rpow_le_rpow hx.1 hx.2 (by linarith)
  holder := by
    intro x y
    have hL0 : 0 ≤ rpowLip a M := rpowLip_nonneg ha hM
    calc
      |(f x) ^ a - (f y) ^ a|
          ≤ rpowLip a M * |f x - f y| :=
        rpow_abs_sub_le_lip_on_Icc ha hM (hrange x) (hrange y)
      _ ≤ rpowLip a M * (hf.H * |x - y| ^ β) :=
        mul_le_mul_of_nonneg_left (hf.holder x y) hL0
      _ = (rpowLip a M * hf.H) * |x - y| ^ β := by ring

def LocalLipQuant.rpow_selfHolderOnIcc
    {β M : ℝ} {f : ℝ → ℝ}
    (q : LocalLipQuant f) (hβpos : 0 < β) (hβle : β ≤ 1)
    (hM : 0 ≤ M) (hrange : ∀ x, f x ∈ Set.Icc (0 : ℝ) M) :
    HolderQuant β (fun x => (f x) ^ β) where
  C := M ^ β
  H := max (q.L ^ β) (2 * M ^ β)
  C_nonneg := Real.rpow_nonneg hM β
  H_nonneg := by
    exact le_trans (Real.rpow_nonneg q.L_nonneg β) (le_max_left _ _)
  bound := by
    intro x
    have hx := hrange x
    have hpownn : 0 ≤ (f x) ^ β := Real.rpow_nonneg hx.1 β
    rw [abs_of_nonneg hpownn]
    exact Real.rpow_le_rpow hx.1 hx.2 hβpos.le
  holder := by
    intro x y
    set d : ℝ := |x - y| with hd
    have hd0 : 0 ≤ d := by simpa [hd] using abs_nonneg (x - y)
    have hcoefL : q.L ^ β ≤ max (q.L ^ β) (2 * M ^ β) := le_max_left _ _
    have hcoefC : 2 * M ^ β ≤ max (q.L ^ β) (2 * M ^ β) := le_max_right _ _
    by_cases hdle : d ≤ 1
    · have hloc : |f x - f y| ≤ q.L * d := by
        simpa [hd] using q.local_lip x y (by simpa [hd] using hdle)
      have hpow :
          |(f x) ^ β - (f y) ^ β| ≤ |f x - f y| ^ β :=
        rpow_abs_sub_le_abs_sub_rpow hβpos.le hβle (hrange x).1 (hrange y).1
      have hlocpow : |f x - f y| ^ β ≤ (q.L * d) ^ β :=
        Real.rpow_le_rpow (abs_nonneg _) hloc hβpos.le
      calc
        |(f x) ^ β - (f y) ^ β| ≤ |f x - f y| ^ β := hpow
        _ ≤ (q.L * d) ^ β := hlocpow
        _ = q.L ^ β * d ^ β := by
          rw [Real.mul_rpow q.L_nonneg hd0]
        _ ≤ max (q.L ^ β) (2 * M ^ β) * d ^ β :=
          mul_le_mul_of_nonneg_right hcoefL (Real.rpow_nonneg hd0 β)
    · have hone_le_d : 1 ≤ d := le_of_not_ge hdle
      have hone_le_pow : 1 ≤ d ^ β := by
        calc
          (1 : ℝ) = (1 : ℝ) ^ β := by rw [Real.one_rpow]
          _ ≤ d ^ β := Real.rpow_le_rpow zero_le_one hone_le_d hβpos.le
      have hbound : ∀ z, |(f z) ^ β| ≤ M ^ β := by
        intro z
        have hz := hrange z
        have hpownn : 0 ≤ (f z) ^ β := Real.rpow_nonneg hz.1 β
        rw [abs_of_nonneg hpownn]
        exact Real.rpow_le_rpow hz.1 hz.2 hβpos.le
      calc
        |(f x) ^ β - (f y) ^ β| ≤ 2 * (M ^ β) :=
          abs_sub_le_two_bounds (Real.rpow_nonneg hM β) hbound x y
        _ ≤ max (q.L ^ β) (2 * M ^ β) := hcoefC
        _ ≤ max (q.L ^ β) (2 * M ^ β) * d ^ β := by
          have hcoef_nonneg : 0 ≤ max (q.L ^ β) (2 * M ^ β) :=
            le_trans (Real.rpow_nonneg q.L_nonneg β) hcoefL
          calc
            max (q.L ^ β) (2 * M ^ β) =
                max (q.L ^ β) (2 * M ^ β) * 1 := by ring
            _ ≤ max (q.L ^ β) (2 * M ^ β) * d ^ β :=
              mul_le_mul_of_nonneg_left hone_le_pow hcoef_nonneg

theorem PaperWeightedHolderSourceBox.abs_le_const
    {κ M β B H : ℝ} {ω : ℝ → ℝ} {R : ℝ → ℝ}
    (hBnn : 0 ≤ B) (hR : PaperWeightedHolderSourceBox κ M β B H ω R) :
    ∀ y, |R y| ≤ B * M := by
  intro y
  calc
    |R y| ≤ B * upperBarrier κ M y := hR.bound y
    _ ≤ B * M := mul_le_mul_of_nonneg_left (upperBarrier_le_M κ M y) hBnn

/-- A source-box element with the exponential left-tail modulus has a packaged
exponential left-rate witness. -/
theorem PaperWeightedHolderSourceBox.expLeftRateData_of_expOmega
    {κ M β B H sigma aL K : ℝ} {R : ℝ → ℝ}
    (hsigma : 0 < sigma) (hK : 0 ≤ K) (hBnn : 0 ≤ B) (hMnn : 0 ≤ M)
    (hR : PaperWeightedHolderSourceBox κ M β B H
      (expLeftOmega sigma aL K) R) :
    ExpLeftRateData R := by
  rcases hR.leftTail with ⟨ell, hlim⟩
  refine ⟨sigma, aL, K + 2 * (B * M), ell, hsigma, ?_⟩
  exact leftTailCauchy_to_ExpLeftRate_of_tendsto
    (sigma := sigma) (aL := aL) (K := K) (S := B * M)
    (f := R) (ell := ell)
    hsigma hK (mul_nonneg hBnn hMnn)
    (hR.abs_le_const hBnn) hlim
    (by
      intro A _hA x y hx hy
      simpa [expLeftOmega] using hR.leftTailCauchy A x y hx hy)

/-- Weighted Green-kernel moment for the exponential left-rate estimate. -/
def greenKernelExpMoment (c lam sigma : ℝ) : ℝ :=
  ∫ z, |greenKernel c lam z| * Real.exp (-sigma * z)

/-- Weighted differentiated-kernel moment for the exponential left-rate estimate. -/
def greenKernelDerivExpMoment (c lam sigma : ℝ) : ℝ :=
  ∫ z, |greenKernelDeriv c lam z| * Real.exp (-sigma * z)

theorem greenKernel_expWeight_eqOn_Iic
    (hlam : 0 < lam) (sigma : ℝ) :
    Set.EqOn
      (fun z => |greenKernel c lam z| * Real.exp (-sigma * z))
      (fun z => (greenDelta c lam)⁻¹ *
        Real.exp ((greenRootPlus c lam - sigma) * z))
      (Set.Iic 0) := by
  intro z hz
  rw [Set.mem_Iic] at hz
  have hKnn : 0 ≤ greenKernel c lam z := greenKernel_nonneg (c := c) hlam z
  change |greenKernel c lam z| * Real.exp (-sigma * z) =
    (greenDelta c lam)⁻¹ *
      Real.exp ((greenRootPlus c lam - sigma) * z)
  rw [abs_of_nonneg hKnn]
  simp only [greenKernel, if_pos hz]
  have hexp :
      Real.exp (greenRootPlus c lam * z) * Real.exp (-sigma * z) =
        Real.exp ((greenRootPlus c lam - sigma) * z) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [show ((greenDelta c lam)⁻¹ *
        Real.exp (greenRootPlus c lam * z)) * Real.exp (-sigma * z) =
        (greenDelta c lam)⁻¹ *
          (Real.exp (greenRootPlus c lam * z) * Real.exp (-sigma * z)) by ring,
    hexp]

theorem greenKernel_expWeight_eqOn_Ioi
    (hlam : 0 < lam) (sigma : ℝ) :
    Set.EqOn
      (fun z => |greenKernel c lam z| * Real.exp (-sigma * z))
      (fun z => (greenDelta c lam)⁻¹ *
        Real.exp ((greenRootMinus c lam - sigma) * z))
      (Set.Ioi 0) := by
  intro z hz
  rw [Set.mem_Ioi] at hz
  have hKnn : 0 ≤ greenKernel c lam z := greenKernel_nonneg (c := c) hlam z
  change |greenKernel c lam z| * Real.exp (-sigma * z) =
    (greenDelta c lam)⁻¹ *
      Real.exp ((greenRootMinus c lam - sigma) * z)
  rw [abs_of_nonneg hKnn]
  simp only [greenKernel, if_neg (not_le.mpr hz)]
  have hexp :
      Real.exp (greenRootMinus c lam * z) * Real.exp (-sigma * z) =
        Real.exp ((greenRootMinus c lam - sigma) * z) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [show ((greenDelta c lam)⁻¹ *
        Real.exp (greenRootMinus c lam * z)) * Real.exp (-sigma * z) =
        (greenDelta c lam)⁻¹ *
          (Real.exp (greenRootMinus c lam * z) * Real.exp (-sigma * z)) by ring,
    hexp]

theorem greenKernelExpMoment_integrable
    (hlam : 0 < lam) {sigma : ℝ}
    (hsigma0 : 0 ≤ sigma)
    (hsigma : sigma < greenRootPlus c lam) :
    Integrable (fun z => |greenKernel c lam z| * Real.exp (-sigma * z)) := by
  have hrp : 0 < greenRootPlus c lam - sigma := sub_pos.mpr hsigma
  have hrm : greenRootMinus c lam - sigma < 0 := by
    have hminus := greenRootMinus_neg (c := c) hlam
    linarith
  have hIic :
      IntegrableOn
        (fun z => |greenKernel c lam z| * Real.exp (-sigma * z))
        (Set.Iic 0) := by
    have hbase :
        IntegrableOn
          (fun z => (greenDelta c lam)⁻¹ *
            Real.exp ((greenRootPlus c lam - sigma) * z))
          (Set.Iic 0) :=
      (integrableOn_exp_mul_Iic
        (a := greenRootPlus c lam - sigma) hrp 0).const_mul _
    exact hbase.congr_fun
      (greenKernel_expWeight_eqOn_Iic (c := c) (lam := lam) hlam sigma).symm
      measurableSet_Iic
  have hIoi :
      IntegrableOn
        (fun z => |greenKernel c lam z| * Real.exp (-sigma * z))
        (Set.Ioi 0) := by
    have hbase :
        IntegrableOn
          (fun z => (greenDelta c lam)⁻¹ *
            Real.exp ((greenRootMinus c lam - sigma) * z))
          (Set.Ioi 0) :=
      (integrableOn_exp_mul_Ioi
        (a := greenRootMinus c lam - sigma) hrm 0).const_mul _
    exact hbase.congr_fun
      (greenKernel_expWeight_eqOn_Ioi (c := c) (lam := lam) hlam sigma).symm
      measurableSet_Ioi
  rw [← integrableOn_univ,
    show (Set.univ : Set ℝ) = Set.Iic 0 ∪ Set.Ioi 0 by
      ext x
      simp only [Set.mem_univ, Set.mem_union, Set.mem_Iic, Set.mem_Ioi,
        true_iff]
      exact le_or_gt x 0]
  exact hIic.union hIoi

theorem greenKernelExpMoment_eq
    (hlam : 0 < lam) {sigma : ℝ}
    (hsigma0 : 0 ≤ sigma)
    (hsigma : sigma < greenRootPlus c lam) :
    greenKernelExpMoment c lam sigma =
      (greenDelta c lam)⁻¹ *
        ((greenRootPlus c lam - sigma)⁻¹ -
          (greenRootMinus c lam - sigma)⁻¹) := by
  have hrp : 0 < greenRootPlus c lam - sigma := sub_pos.mpr hsigma
  have hrm : greenRootMinus c lam - sigma < 0 := by
    have hminus := greenRootMinus_neg (c := c) hlam
    linarith
  have hfi := greenKernelExpMoment_integrable
    (c := c) (lam := lam) hlam hsigma0 hsigma
  have hsplit := MeasureTheory.integral_add_compl
    (s := Set.Iic (0 : ℝ)) measurableSet_Iic hfi
  have hIic :
      ∫ z in Set.Iic (0 : ℝ),
          |greenKernel c lam z| * Real.exp (-sigma * z)
        = (greenDelta c lam)⁻¹ / (greenRootPlus c lam - sigma) := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Iic
      (greenKernel_expWeight_eqOn_Iic (c := c) (lam := lam) hlam sigma)]
    rw [MeasureTheory.integral_const_mul, integral_exp_mul_Iic hrp 0]
    simp [div_eq_mul_inv]
  have hIoi :
      ∫ z in Set.Ioi (0 : ℝ),
          |greenKernel c lam z| * Real.exp (-sigma * z)
        = -((greenDelta c lam)⁻¹ / (greenRootMinus c lam - sigma)) := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (greenKernel_expWeight_eqOn_Ioi (c := c) (lam := lam) hlam sigma)]
    rw [MeasureTheory.integral_const_mul, integral_exp_mul_Ioi hrm 0]
    simp [div_eq_mul_inv]
  simp only [Set.compl_Iic] at hsplit
  rw [greenKernelExpMoment, ← hsplit, hIic, hIoi]
  ring

theorem greenKernelDeriv_expWeight_eqOn_Iic
    (hlam : 0 < lam) (sigma : ℝ) :
    Set.EqOn
      (fun z => |greenKernelDeriv c lam z| * Real.exp (-sigma * z))
      (fun z => (greenDelta c lam)⁻¹ * greenRootPlus c lam *
        Real.exp ((greenRootPlus c lam - sigma) * z))
      (Set.Iic 0) := by
  intro z hz
  rw [Set.mem_Iic] at hz
  have hδ : 0 < (greenDelta c lam)⁻¹ :=
    inv_pos.mpr (greenDelta_pos (c := c) hlam)
  have hrp := greenRootPlus_pos (c := c) hlam
  simp only [greenKernelDeriv, if_pos hz]
  rw [abs_of_nonneg (by positivity)]
  have hexp :
      Real.exp (greenRootPlus c lam * z) * Real.exp (-sigma * z) =
        Real.exp ((greenRootPlus c lam - sigma) * z) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [show ((greenDelta c lam)⁻¹ * greenRootPlus c lam *
        Real.exp (greenRootPlus c lam * z)) * Real.exp (-sigma * z) =
        (greenDelta c lam)⁻¹ * greenRootPlus c lam *
          (Real.exp (greenRootPlus c lam * z) * Real.exp (-sigma * z)) by ring,
    hexp]

theorem greenKernelDeriv_expWeight_eqOn_Ioi
    (hlam : 0 < lam) (sigma : ℝ) :
    Set.EqOn
      (fun z => |greenKernelDeriv c lam z| * Real.exp (-sigma * z))
      (fun z => (greenDelta c lam)⁻¹ * (-greenRootMinus c lam) *
        Real.exp ((greenRootMinus c lam - sigma) * z))
      (Set.Ioi 0) := by
  intro z hz
  rw [Set.mem_Ioi] at hz
  have hδ : 0 < (greenDelta c lam)⁻¹ :=
    inv_pos.mpr (greenDelta_pos (c := c) hlam)
  have hrm := greenRootMinus_neg (c := c) hlam
  simp only [greenKernelDeriv, if_neg (not_le.mpr hz)]
  rw [abs_of_nonpos (by
    have : greenRootMinus c lam * Real.exp (greenRootMinus c lam * z) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hrm.le (Real.exp_pos _).le
    have h2 : (greenDelta c lam)⁻¹ * greenRootMinus c lam
        * Real.exp (greenRootMinus c lam * z)
        = (greenDelta c lam)⁻¹
          * (greenRootMinus c lam * Real.exp (greenRootMinus c lam * z)) := by
      ring
    rw [h2]
    exact mul_nonpos_of_nonneg_of_nonpos hδ.le this)]
  have hexp :
      Real.exp (greenRootMinus c lam * z) * Real.exp (-sigma * z) =
        Real.exp ((greenRootMinus c lam - sigma) * z) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    -((greenDelta c lam)⁻¹ * greenRootMinus c lam *
        Real.exp (greenRootMinus c lam * z)) *
        Real.exp (-sigma * z)
        = (greenDelta c lam)⁻¹ * (-greenRootMinus c lam) *
            (Real.exp (greenRootMinus c lam * z) *
              Real.exp (-sigma * z)) := by ring
    _ = (greenDelta c lam)⁻¹ * (-greenRootMinus c lam) *
          Real.exp ((greenRootMinus c lam - sigma) * z) := by
        rw [hexp]

theorem greenKernelDerivExpMoment_integrable
    (hlam : 0 < lam) {sigma : ℝ}
    (hsigma0 : 0 ≤ sigma)
    (hsigma : sigma < greenRootPlus c lam) :
    Integrable (fun z => |greenKernelDeriv c lam z| * Real.exp (-sigma * z)) := by
  have hrp : 0 < greenRootPlus c lam - sigma := sub_pos.mpr hsigma
  have hrm : greenRootMinus c lam - sigma < 0 := by
    have hminus := greenRootMinus_neg (c := c) hlam
    linarith
  have hIic :
      IntegrableOn
        (fun z => |greenKernelDeriv c lam z| * Real.exp (-sigma * z))
        (Set.Iic 0) := by
    have hbase :
        IntegrableOn
          (fun z => (greenDelta c lam)⁻¹ * greenRootPlus c lam *
            Real.exp ((greenRootPlus c lam - sigma) * z))
          (Set.Iic 0) :=
      (integrableOn_exp_mul_Iic
        (a := greenRootPlus c lam - sigma) hrp 0).const_mul _
    exact hbase.congr_fun
      (greenKernelDeriv_expWeight_eqOn_Iic
        (c := c) (lam := lam) hlam sigma).symm
      measurableSet_Iic
  have hIoi :
      IntegrableOn
        (fun z => |greenKernelDeriv c lam z| * Real.exp (-sigma * z))
        (Set.Ioi 0) := by
    have hbase :
        IntegrableOn
          (fun z => (greenDelta c lam)⁻¹ * (-greenRootMinus c lam) *
            Real.exp ((greenRootMinus c lam - sigma) * z))
          (Set.Ioi 0) :=
      (integrableOn_exp_mul_Ioi
        (a := greenRootMinus c lam - sigma) hrm 0).const_mul _
    exact hbase.congr_fun
      (greenKernelDeriv_expWeight_eqOn_Ioi
        (c := c) (lam := lam) hlam sigma).symm
      measurableSet_Ioi
  rw [← integrableOn_univ,
    show (Set.univ : Set ℝ) = Set.Iic 0 ∪ Set.Ioi 0 by
      ext x
      simp only [Set.mem_univ, Set.mem_union, Set.mem_Iic, Set.mem_Ioi,
        true_iff]
      exact le_or_gt x 0]
  exact hIic.union hIoi

theorem greenKernelDerivExpMoment_eq
    (hlam : 0 < lam) {sigma : ℝ}
    (hsigma0 : 0 ≤ sigma)
    (hsigma : sigma < greenRootPlus c lam) :
    greenKernelDerivExpMoment c lam sigma =
      (greenDelta c lam)⁻¹ *
        (greenRootPlus c lam * (greenRootPlus c lam - sigma)⁻¹ -
          (-greenRootMinus c lam) * (greenRootMinus c lam - sigma)⁻¹) := by
  have hrp : 0 < greenRootPlus c lam - sigma := sub_pos.mpr hsigma
  have hrm : greenRootMinus c lam - sigma < 0 := by
    have hminus := greenRootMinus_neg (c := c) hlam
    linarith
  have hfi := greenKernelDerivExpMoment_integrable
    (c := c) (lam := lam) hlam hsigma0 hsigma
  have hsplit := MeasureTheory.integral_add_compl
    (s := Set.Iic (0 : ℝ)) measurableSet_Iic hfi
  have hIic :
      ∫ z in Set.Iic (0 : ℝ),
          |greenKernelDeriv c lam z| * Real.exp (-sigma * z)
        = (greenDelta c lam)⁻¹ * greenRootPlus c lam /
            (greenRootPlus c lam - sigma) := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Iic
      (greenKernelDeriv_expWeight_eqOn_Iic (c := c) (lam := lam) hlam sigma)]
    rw [MeasureTheory.integral_const_mul, integral_exp_mul_Iic hrp 0]
    simp [div_eq_mul_inv, mul_assoc]
  have hIoi :
      ∫ z in Set.Ioi (0 : ℝ),
          |greenKernelDeriv c lam z| * Real.exp (-sigma * z)
        = -((greenDelta c lam)⁻¹ * (-greenRootMinus c lam) /
            (greenRootMinus c lam - sigma)) := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (greenKernelDeriv_expWeight_eqOn_Ioi (c := c) (lam := lam) hlam sigma)]
    rw [MeasureTheory.integral_const_mul, integral_exp_mul_Ioi hrm 0]
    simp [div_eq_mul_inv, mul_assoc]
  simp only [Set.compl_Iic] at hsplit
  rw [greenKernelDerivExpMoment, ← hsplit, hIic, hIoi]
  ring

theorem greenKernelExpMoment_translated_integral_eq
    (hlam : 0 < lam) {sigma : ℝ}
    (hsigma0 : 0 ≤ sigma)
    (hsigma : sigma < greenRootPlus c lam) :
    (∫ t, |greenKernel c lam (-t)| * Real.exp (sigma * t))
      = greenKernelExpMoment c lam sigma := by
  let f : ℝ → ℝ := fun z => |greenKernel c lam z| * Real.exp (-sigma * z)
  have hfun :
      (fun t : ℝ => |greenKernel c lam (-t)| * Real.exp (sigma * t))
        = fun t : ℝ => f (-t) := by
    funext t
    dsimp [f]
    congr 2
    ring
  rw [hfun, integral_neg_eq_self f volume]
  rfl

theorem greenKernelDerivExpMoment_translated_integral_eq
    (hlam : 0 < lam) {sigma : ℝ}
    (hsigma0 : 0 ≤ sigma)
    (hsigma : sigma < greenRootPlus c lam) :
    (∫ t, |greenKernelDeriv c lam (-t)| * Real.exp (sigma * t))
      = greenKernelDerivExpMoment c lam sigma := by
  let f : ℝ → ℝ := fun z => |greenKernelDeriv c lam z| * Real.exp (-sigma * z)
  have hfun :
      (fun t : ℝ => |greenKernelDeriv c lam (-t)| * Real.exp (sigma * t))
        = fun t : ℝ => f (-t) := by
    funext t
    dsimp [f]
    congr 2
    ring
  rw [hfun, integral_neg_eq_self f volume]
  rfl

theorem greenKernelExpMoment_translated_integrable
    (hlam : 0 < lam) {sigma : ℝ}
    (hsigma0 : 0 ≤ sigma)
    (hsigma : sigma < greenRootPlus c lam) :
    Integrable (fun t => |greenKernel c lam (-t)| * Real.exp (sigma * t)) := by
  have hbase := (greenKernelExpMoment_integrable
    (c := c) (lam := lam) hlam hsigma0 hsigma).comp_neg
  refine hbase.congr ?_
  exact Eventually.of_forall fun t => by
    dsimp
    congr 2
    ring

theorem greenKernelDerivExpMoment_translated_integrable
    (hlam : 0 < lam) {sigma : ℝ}
    (hsigma0 : 0 ≤ sigma)
    (hsigma : sigma < greenRootPlus c lam) :
    Integrable (fun t => |greenKernelDeriv c lam (-t)| * Real.exp (sigma * t)) := by
  have hbase := (greenKernelDerivExpMoment_integrable
    (c := c) (lam := lam) hlam hsigma0 hsigma).comp_neg
  refine hbase.congr ?_
  exact Eventually.of_forall fun t => by
    dsimp
    congr 2
    ring

/-- Pointwise estimates proving that the weighted truncated fixed-source map
preserves the weighted-Hölder source box.  The analytic constants are kept in a
single record so the self-map proof has a narrow, checkable interface. -/
structure PaperFixedSourceMapBoxBounds
    (p : CMParams) (c lam M κ β B H : ℝ) (ω : ℝ → ℝ)
    (u Z : ℝ → ℝ) where
  map_cont : ∀ R, PaperWeightedHolderSourceBox κ M β B H ω R →
    Continuous (paperFixedSourceMap p c lam M κ u Z R)
  map_bound : ∀ R, PaperWeightedHolderSourceBox κ M β B H ω R →
    ∀ x, |paperFixedSourceMap p c lam M κ u Z R x| ≤
      B * upperBarrier κ M x
  map_holder : ∀ R, PaperWeightedHolderSourceBox κ M β B H ω R →
    ∀ x y,
      |paperFixedSourceMap p c lam M κ u Z R x -
          paperFixedSourceMap p c lam M κ u Z R y| ≤ H * |x - y| ^ β
  map_leftTail : ∀ R, PaperWeightedHolderSourceBox κ M β B H ω R →
    ∃ Rm, Tendsto (paperFixedSourceMap p c lam M κ u Z R) atBot (𝓝 Rm)
  map_leftTailCauchy : ∀ R, PaperWeightedHolderSourceBox κ M β B H ω R →
    ∀ A x y, x ≤ A → y ≤ A →
      |paperFixedSourceMap p c lam M κ u Z R x -
          paperFixedSourceMap p c lam M κ u Z R y| ≤ ω A
  ascoliCompactRange :
    LocalUniformSequentiallyCompactRange
      (PaperWeightedHolderSourceBox κ M β B H ω)
      (paperFixedSourceMap p c lam M κ u Z)

namespace PaperFixedSourceMapBoxBounds

/-- The weighted source-box estimates imply `mapsTo` for the fixed-source map. -/
theorem mapsTo
    {p : CMParams} {c lam M κ β B H : ℝ} {ω : ℝ → ℝ} {u Z : ℝ → ℝ}
    (h : PaperFixedSourceMapBoxBounds p c lam M κ β B H ω u Z) :
    ∀ R, PaperWeightedHolderSourceBox κ M β B H ω R →
      PaperWeightedHolderSourceBox κ M β B H ω
        (paperFixedSourceMap p c lam M κ u Z R) := by
  intro R hR
  exact
    { cont := h.map_cont R hR
      bound := h.map_bound R hR
      holder := h.map_holder R hR
      omega_nonneg := hR.omega_nonneg
      omega_tendsto := hR.omega_tendsto
      leftTail := h.map_leftTail R hR
      leftTailCauchy := h.map_leftTailCauchy R hR }

/-- Arzelà-Ascoli compactness for weighted-Hölder source-box images. -/
theorem compactRange
    {p : CMParams} {c lam M κ β B H : ℝ} {ω : ℝ → ℝ} {u Z : ℝ → ℝ}
    (h : PaperFixedSourceMapBoxBounds p c lam M κ β B H ω u Z) :
    LocalUniformSequentiallyCompactRange
      (PaperWeightedHolderSourceBox κ M β B H ω)
      (paperFixedSourceMap p c lam M κ u Z) :=
  h.ascoliCompactRange

/-- With the exponential left-tail modulus, the fixed-source map output carries
an exponential left-rate witness. -/
theorem map_expLeftRateData_of_expOmega
    {p : CMParams} {c lam M κ β B H sigma aL K : ℝ} {u Z R : ℝ → ℝ}
    (h : PaperFixedSourceMapBoxBounds p c lam M κ β B H
      (expLeftOmega sigma aL K) u Z)
    (hsigma : 0 < sigma) (hK : 0 ≤ K) (hBnn : 0 ≤ B) (hMnn : 0 ≤ M)
    (hR : PaperWeightedHolderSourceBox κ M β B H
      (expLeftOmega sigma aL K) R) :
    ExpLeftRateData (paperFixedSourceMap p c lam M κ u Z R) := by
  exact (h.mapsTo R hR).expLeftRateData_of_expOmega
    hsigma hK hBnn hMnn

end PaperFixedSourceMapBoxBounds

/-- Schauder data for the weighted truncated fixed-source map on a source box.

The finite-net approximation witness is the single flagged box-specific cube
floor.  Compactness is the weighted-Hölder Arzelà-Ascoli range field in
`boxBounds`; the fixed point is obtained through the committed cube bridge. -/
structure PaperTruncatedFixedSourceBoxData
    (p : CMParams) (c lam M κ Λ : ℝ) (u Z : ℝ → ℝ) where
  beta : ℝ
  B : ℝ
  H : ℝ
  omega : ℝ → ℝ
  uTrap : InMonotoneWaveTrapSet κ M u
  hM_nonneg : 0 ≤ M
  B_nonneg : 0 ≤ B
  sourceBound_eq : Λ = 2 * (greenDelta c lam)⁻¹ * (B * M)
  beta_eq : beta = paperWeightedHolderExponent p
  boxBounds : PaperFixedSourceMapBoxBounds p c lam M κ beta B H omega u Z
  continuousOn :
    LocalUniformContinuousOn
      (PaperWeightedHolderSourceBox κ M beta B H omega)
      (paperFixedSourceMap p c lam M κ u Z)
  boxCubeData :
    ProjectedCubeApproxData
      (PaperWeightedHolderSourceBox κ M beta B H omega)
      (paperFixedSourceMap p c lam M κ u Z)
  truncation_inactive :
    ∀ R, PaperWeightedHolderSourceBox κ M beta B H omega R →
      paperFixedSourceMap p c lam M κ u Z R = R →
        ∀ x,
          (fun y => greenConv c lam R y) x ∈
            Set.Icc (0 : ℝ) (upperBarrier κ M x)

namespace PaperTruncatedFixedSourceBoxData

theorem mapsTo
    {p : CMParams} {c lam M κ Λ : ℝ} {u Z : ℝ → ℝ}
    (h : PaperTruncatedFixedSourceBoxData p c lam M κ Λ u Z) :
    ∀ R, PaperWeightedHolderSourceBox κ M h.beta h.B h.H h.omega R →
      PaperWeightedHolderSourceBox κ M h.beta h.B h.H h.omega
        (paperFixedSourceMap p c lam M κ u Z R) :=
  h.boxBounds.mapsTo

theorem compactRange
    {p : CMParams} {c lam M κ Λ : ℝ} {u Z : ℝ → ℝ}
    (h : PaperTruncatedFixedSourceBoxData p c lam M κ Λ u Z) :
    LocalUniformSequentiallyCompactRange
      (PaperWeightedHolderSourceBox κ M h.beta h.B h.H h.omega)
      (paperFixedSourceMap p c lam M κ u Z) :=
  h.boxBounds.compactRange

theorem exists_fixed
    {p : CMParams} {c lam M κ Λ : ℝ} {u Z : ℝ → ℝ}
    (h : PaperTruncatedFixedSourceBoxData p c lam M κ Λ u Z) :
    ∃ R : ℝ → ℝ,
      PaperWeightedHolderSourceBox κ M h.beta h.B h.H h.omega R ∧
        paperFixedSourceMap p c lam M κ u Z R = R :=
  localUniformFixedPoint_of_cubeApproxData
    (trap := PaperWeightedHolderSourceBox κ M h.beta h.B h.H h.omega)
    (Tmap := paperFixedSourceMap p c lam M κ u Z)
    h.continuousOn h.compactRange
    (ProjectedCubeApproxData.toLocalUniformCubeApproxData h.boxCubeData)

end PaperTruncatedFixedSourceBoxData

theorem paperWaveOperator_eq_linear_add_paperStepNonlinearity
    (p : CMParams) (c : ℝ) (u W : ℝ → ℝ) (x : ℝ) :
    paperWaveOperator p c u W x =
      iteratedDeriv 2 W x + c * deriv W x
        + paperStepNonlinearity p u W x := by
  unfold paperWaveOperator paperStepNonlinearity
  ring_nf

/-- Expanded paper source versus the divergence-form cross source.

The two sources are not definitionally the same for a genuinely frozen profile
`u`: after the product rule and the frozen elliptic identity
`V'' = V - u^γ`, the mismatch is exactly
`χ * W^m * (W^γ - u^γ)`.  In the self-frozen case `u = W` this term vanishes. -/
theorem paperStepSource_sub_crossSource
    (p : CMParams) (c lam : ℝ) {u Z W : ℝ → ℝ}
    (hu : IsCUnifBdd u) (hu_nonneg : ∀ y, 0 ≤ u y)
    (hW_nonneg : ∀ y, 0 ≤ W y)
    (hWdiff : ∀ x, DifferentiableAt ℝ W x) (x : ℝ) :
    paperStepSource p c lam u Z W x - crossSource p lam u Z W x =
      p.χ * (W x) ^ p.m * ((W x) ^ p.γ - (u x) ^ p.γ) := by
  have hchem := chemFlux_split_identity
    (p := p) (u := u) (W := W) (x := x) hu hu_nonneg (hWdiff x)
  have hVpp :
      deriv (deriv (frozenElliptic p u)) x =
        frozenElliptic p u x - (u x) ^ p.γ :=
    frozenElliptic_deriv_deriv_eq p hu hu_nonneg x
  have hm_left : (W x) * (W x) ^ (p.m - 1) = (W x) ^ p.m :=
    mul_rpow_sub_one p.m p.hm (hW_nonneg x)
  have hm_right : (W x) ^ (p.m - 1) * (W x) = (W x) ^ p.m := by
    rw [mul_comm, hm_left]
  have hmg_left :
      (W x) * (W x) ^ (p.m + p.γ - 1) = (W x) ^ (p.m + p.γ) := by
    exact mul_rpow_sub_one (p.m + p.γ) (by linarith [p.hm, p.hγ]) (hW_nonneg x)
  have hmg_add :
      (W x) ^ (p.m + p.γ) = (W x) ^ p.m * (W x) ^ p.γ := by
    exact Real.rpow_add_of_nonneg (hW_nonneg x)
      (by linarith [p.hm] : 0 ≤ p.m) (by linarith [p.hγ] : 0 ≤ p.γ)
  have hm_nf : (W x) ^ (-1 + p.m) * (W x) = (W x) ^ p.m := by
    have hexp : -1 + p.m = p.m - 1 := by ring
    rw [hexp, hm_right]
  have hmg_nf :
      (W x) * (W x) ^ (-1 + p.m + p.γ) =
        (W x) ^ p.m * (W x) ^ p.γ := by
    calc
      (W x) * (W x) ^ (-1 + p.m + p.γ)
          = (W x) * (W x) ^ (p.m + p.γ - 1) := by
            congr 1
            ring_nf
      _ = (W x) ^ (p.m + p.γ) := hmg_left
      _ = (W x) ^ p.m * (W x) ^ p.γ := hmg_add
  have hm_nf_mul :
      p.χ * (W x) ^ (-1 + p.m) * (W x) * frozenElliptic p u x =
        p.χ * (W x) ^ p.m * frozenElliptic p u x := by
    calc
      p.χ * (W x) ^ (-1 + p.m) * (W x) * frozenElliptic p u x
          = p.χ * ((W x) ^ (-1 + p.m) * (W x)) *
              frozenElliptic p u x := by ring
      _ = p.χ * (W x) ^ p.m * frozenElliptic p u x := by rw [hm_nf]
  have hmg_nf_mul :
      p.χ * (W x) * (W x) ^ (-1 + p.m + p.γ) =
        p.χ * (W x) ^ p.m * (W x) ^ p.γ := by
    calc
      p.χ * (W x) * (W x) ^ (-1 + p.m + p.γ)
          = p.χ * ((W x) * (W x) ^ (-1 + p.m + p.γ)) := by ring
      _ = p.χ * ((W x) ^ p.m * (W x) ^ p.γ) := by rw [hmg_nf]
      _ = p.χ * (W x) ^ p.m * (W x) ^ p.γ := by ring
  have hchem_raw :
      deriv (fun t => (W t) ^ p.m * deriv (frozenElliptic p u) t) x =
        p.m * deriv (frozenElliptic p u) x * (W x) ^ (p.m - 1) * deriv W x
          + (W x) ^ p.m * deriv (deriv (frozenElliptic p u)) x := by
    simpa [chemFlux] using hchem
  unfold paperStepSource paperStepNonlinearity crossSource reactionFun
  rw [hchem_raw, hVpp]
  ring_nf
  rw [hm_nf_mul, hmg_nf_mul]
  ring

/-- In the self-frozen case `u = W`, the expanded paper source agrees with the
committed divergence-form `crossSource`.  This is the only direct-reuse case for
the existing cross-step fixed point. -/
theorem paperStepSource_eq_crossSource_self
    (p : CMParams) (c lam : ℝ) {Z W : ℝ → ℝ}
    (hW : IsCUnifBdd W) (hW_nonneg : ∀ y, 0 ≤ W y)
    (hWdiff : ∀ x, DifferentiableAt ℝ W x) :
    paperStepSource p c lam W Z W = crossSource p lam W Z W := by
  funext x
  have hdiff := paperStepSource_sub_crossSource
    (p := p) (c := c) (lam := lam) (u := W) (Z := Z) (W := W)
    hW hW_nonneg hW_nonneg hWdiff x
  have hzero :
      p.χ * (W x) ^ p.m * ((W x) ^ p.γ - (W x) ^ p.γ) = 0 := by
    ring
  linarith

/-- `greenConv c lam H` solves `L_lam w = -H`, with genuine derivatives. -/
theorem greenConv_variation_negative
    (hlam : 0 < lam) {H : ℝ → ℝ} (hH : Continuous H)
    (hHi : ∀ t : ℝ,
      IntegrableOn (gWeight (greenRootPlus c lam) H) (Ioi t))
    (hLo : ∀ t : ℝ,
      IntegrableOn (gWeight (greenRootMinus c lam) H) (Iic t))
    (x : ℝ) :
    iteratedDeriv 2 (greenConv c lam H) x
        + c * deriv (greenConv c lam H) x
        - lam * greenConv c lam H x
      = -H x := by
  have hw' : ∀ y, HasDerivAt (greenConv c lam H)
      (greenConvDeriv c lam H y) y := fun y =>
    greenConv_hasDerivAt (c := c) (lam := lam) hH hHi hLo y
  have hderiv_eq :
      deriv (greenConv c lam H) = fun y => greenConvDeriv c lam H y :=
    funext fun y => (hw' y).deriv
  have hw'' : HasDerivAt (deriv (greenConv c lam H))
      (greenConvDeriv2 c lam H x) x := by
    rw [hderiv_eq]
    exact greenConvDeriv_hasDerivAt (c := c) (lam := lam) hH hHi hLo x
  have hiter : iteratedDeriv 2 (greenConv c lam H) x =
      greenConvDeriv2 c lam H x := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    exact hw''.deriv
  rw [hiter, hderiv_eq]
  exact greenConv_solves (c := c) (lam := lam) hlam (H := H) x

/-- Linear resolvent solve from the explicit Green kernel: for any continuous
source with the two exponential tails, `W = greenConv c lam R` solves
`W'' + c W' - lam W = -R`. -/
theorem greenConv_resolvent_solve
    (hlam : 0 < lam) {R : ℝ → ℝ} (hR : Continuous R)
    (hRhi : ∀ x,
      IntegrableOn (gWeight (greenRootPlus c lam) R) (Ioi x))
    (hRlo : ∀ x,
      IntegrableOn (gWeight (greenRootMinus c lam) R) (Iic x)) :
    ∃ W : ℝ → ℝ,
      W = (fun x => greenConv c lam R x) ∧
      ∀ x,
        iteratedDeriv 2 W x + c * deriv W x - lam * W x = -R x := by
  refine ⟨fun x => greenConv c lam R x, rfl, ?_⟩
  intro x
  exact greenConv_variation_negative (c := c) (lam := lam) hlam hR hRhi hRlo x

/-- A Green-represented paper source satisfies the paper implicit step equation. -/
theorem paperImplicitStepOp_of_greenConv_source
    {p : CMParams} {u Z W R : ℝ → ℝ}
    (hlam : 0 < lam)
    (hR : R = paperStepSource p c lam u Z W)
    (hgreen : W = fun x => greenConv c lam R x)
    (hRcont : Continuous R)
    (hRhi : ∀ x,
      IntegrableOn (gWeight (greenRootPlus c lam) R) (Ioi x))
    (hRlo : ∀ x,
      IntegrableOn (gWeight (greenRootMinus c lam) R) (Iic x)) :
    ∀ x, paperImplicitStepOp p c (1 / lam) u W x = Z x := by
  intro x
  have hL :
      iteratedDeriv 2 W x + c * deriv W x - lam * W x = -R x := by
    rw [hgreen]
    exact greenConv_variation_negative
      (c := c) (lam := lam) hlam hRcont hRhi hRlo x
  have hsource_x : R x = paperStepSource p c lam u Z W x := by
    rw [hR]
  have hpaper :
      paperWaveOperator p c u W x = lam * (W x - Z x) := by
    rw [paperWaveOperator_eq_linear_add_paperStepNonlinearity]
    rw [hsource_x] at hL
    unfold paperStepSource at hL
    nlinarith
  rw [paperImplicitStepOp_apply, hpaper]
  field_simp [ne_of_gt hlam]
  ring

/-- If the paper source is already a fixed source for the Green convolution,
the corresponding Green convolution is a paper implicit-step solution.  This is
the linear-resolvent half of the per-step construction; the Schauder step
supplies `hRfix`. -/
theorem paperImplicitStepOp_exists_of_green_fixed_source
    {p : CMParams} {u Z R : ℝ → ℝ}
    (hlam : 0 < lam)
    (hRfix : R = paperStepSource p c lam u Z (fun x => greenConv c lam R x))
    (hRcont : Continuous R)
    (hRhi : ∀ x,
      IntegrableOn (gWeight (greenRootPlus c lam) R) (Ioi x))
    (hRlo : ∀ x,
      IntegrableOn (gWeight (greenRootMinus c lam) R) (Iic x)) :
    ∃ W : ℝ → ℝ,
      W = (fun x => greenConv c lam R x) ∧
      ∀ x, paperImplicitStepOp p c (1 / lam) u W x = Z x := by
  refine ⟨fun x => greenConv c lam R x, rfl, ?_⟩
  exact paperImplicitStepOp_of_greenConv_source
    (c := c) (lam := lam) hlam hRfix rfl hRcont hRhi hRlo

/-- A Green-represented fixed source for the spatially truncated source solves
the truncated implicit Euler step. -/
theorem paperImplicitStepOp_truncated_of_green_fixed_source
    {p : CMParams} {M κ : ℝ} {u Z R : ℝ → ℝ}
    (hlam : 0 < lam)
    (hRfix : R = paperFixedSourceMap p c lam M κ u Z R)
    (hRcont : Continuous R)
    (hRhi : ∀ x,
      IntegrableOn (gWeight (greenRootPlus c lam) R) (Ioi x))
    (hRlo : ∀ x,
      IntegrableOn (gWeight (greenRootMinus c lam) R) (Iic x)) :
    ∀ x,
      paperImplicitStepOp_truncated p c (1 / lam) M κ u
        (fun y => greenConv c lam R y) x = Z x := by
  intro x
  have hL :
      iteratedDeriv 2 (fun y => greenConv c lam R y) x +
          c * deriv (fun y => greenConv c lam R y) x -
            lam * greenConv c lam R x = -R x :=
    greenConv_variation_negative
      (c := c) (lam := lam) hlam hRcont hRhi hRlo x
  have hsource_x :
      R x = paperFixedSourceMap p c lam M κ u Z R x := by
    exact congrFun hRfix x
  have hpaper :
      paperWaveOperator_truncated p c M κ u
          (fun y => greenConv c lam R y) x =
        lam * (greenConv c lam R x - Z x) := by
    unfold paperFixedSourceMap paperStepSource_truncated at hsource_x
    unfold paperWaveOperator_truncated at ⊢
    nlinarith
  rw [paperImplicitStepOp_truncated_apply, hpaper]
  field_simp [ne_of_gt hlam]
  ring

theorem IsBddFun.const (a : ℝ) : IsBddFun (fun _ : ℝ => a) :=
  ⟨|a|, fun _ => le_rfl⟩

theorem IsBddFun.add {f g : ℝ → ℝ}
    (hf : IsBddFun f) (hg : IsBddFun g) :
    IsBddFun (fun x => f x + g x) := by
  rcases hf with ⟨Mf, hMf⟩
  rcases hg with ⟨Mg, hMg⟩
  refine ⟨|Mf| + |Mg|, fun x => ?_⟩
  calc
    |f x + g x| ≤ |f x| + |g x| := abs_add_le _ _
    _ ≤ Mf + Mg := add_le_add (hMf x) (hMg x)
    _ ≤ |Mf| + |Mg| := add_le_add (le_abs_self _) (le_abs_self _)

theorem IsBddFun.neg {f : ℝ → ℝ} (hf : IsBddFun f) :
    IsBddFun (fun x => -f x) := by
  rcases hf with ⟨M, hM⟩
  exact ⟨M, fun x => by simpa using hM x⟩

theorem IsBddFun.sub {f g : ℝ → ℝ}
    (hf : IsBddFun f) (hg : IsBddFun g) :
    IsBddFun (fun x => f x - g x) := by
  simpa [sub_eq_add_neg] using IsBddFun.add hf (IsBddFun.neg hg)

theorem IsBddFun.mul {f g : ℝ → ℝ}
    (hf : IsBddFun f) (hg : IsBddFun g) :
    IsBddFun (fun x => f x * g x) := by
  rcases hf with ⟨Mf, hMf⟩
  rcases hg with ⟨Mg, hMg⟩
  refine ⟨|Mf| * |Mg|, fun x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (le_trans (hMf x) (le_abs_self _))
    (le_trans (hMg x) (le_abs_self _)) (abs_nonneg _) (abs_nonneg _)

theorem IsBddFun.const_mul {f : ℝ → ℝ} (a : ℝ) (hf : IsBddFun f) :
    IsBddFun (fun x => a * f x) :=
  IsBddFun.mul (IsBddFun.const a) hf

theorem IsBddFun.rpow_of_nonneg {f : ℝ → ℝ} {a : ℝ}
    (hf : IsBddFun f) (ha : 0 ≤ a) (hfnn : ∀ x, 0 ≤ f x) :
    IsBddFun (fun x => (f x) ^ a) := by
  rcases hf with ⟨M, hM⟩
  refine ⟨|M| ^ a, fun x => ?_⟩
  rw [abs_of_nonneg (Real.rpow_nonneg (hfnn x) a)]
  have hf_le : f x ≤ |M| := by
    calc
      f x = |f x| := (abs_of_nonneg (hfnn x)).symm
      _ ≤ M := hM x
      _ ≤ |M| := le_abs_self M
  exact Real.rpow_le_rpow (hfnn x) hf_le ha

theorem IsBddFun.norm_isBoundedUnder_le {f : ℝ → ℝ} {l : Filter ℝ}
    (hf : IsBddFun f) :
    IsBoundedUnder (· ≤ ·) l ((‖·‖) ∘ f) := by
  rcases hf with ⟨B, hB⟩
  refine Filter.isBoundedUnder_of ?_
  refine ⟨|B|, fun x => ?_⟩
  change ‖f x‖ ≤ |B|
  rw [Real.norm_eq_abs]
  exact le_trans (hB x) (le_abs_self B)

theorem tendsto_mul_zero_of_isBddFun {f g : ℝ → ℝ} {l : Filter ℝ}
    (hf : Tendsto f l (𝓝 0)) (hg : IsBddFun g) :
    Tendsto (fun x => f x * g x) l (𝓝 0) :=
  hf.zero_mul_isBoundedUnder_le (IsBddFun.norm_isBoundedUnder_le hg)

/-- A bounded antitone real profile has a finite right tail limit. -/
theorem antitone_isBddFun_tendsto_atTop
    {Z : ℝ → ℝ} (hZ : Antitone Z) (hB : IsBddFun Z) :
    ∃ L : ℝ, Tendsto Z atTop (𝓝 L) := by
  rcases tendsto_atTop_of_antitone (f := Z) hZ with hbot | hfin
  · exfalso
    rcases hB with ⟨B, hB⟩
    have hlower : ∀ x, -B ≤ Z x := by
      intro x
      have hx := hB x
      rw [abs_le] at hx
      exact hx.1
    have hev : ∀ᶠ x in atTop, Z x < -B - 1 :=
      hbot (Iio_mem_atBot (-B - 1))
    have hboth : ∀ᶠ x in atTop, Z x < -B - 1 ∧ -B ≤ Z x :=
      hev.and (Eventually.of_forall hlower)
    rcases hboth.exists with ⟨x, hxlt, hxle⟩
    linarith
  · exact hfin

/-- A bounded antitone real profile has a finite left tail limit. -/
theorem antitone_isBddFun_tendsto_atBot
    {Z : ℝ → ℝ} (hZ : Antitone Z) (hB : IsBddFun Z) :
    ∃ L : ℝ, Tendsto Z atBot (𝓝 L) := by
  rcases tendsto_atBot_of_antitone (f := Z) hZ with htop | hfin
  · exfalso
    rcases hB with ⟨B, hB⟩
    have hupper : ∀ x, Z x ≤ B := by
      intro x
      exact le_trans (le_abs_self _) (hB x)
    have hev : ∀ᶠ x in atBot, B + 1 < Z x :=
      htop (Ioi_mem_atTop (B + 1))
    have hboth : ∀ᶠ x in atBot, B + 1 < Z x ∧ Z x ≤ B :=
      hev.and (Eventually.of_forall hupper)
    rcases hboth.exists with ⟨x, hxlt, hxle⟩
    linarith
  · exact hfin

/-- Bounded antitone real profiles have finite limits at both infinities. -/
theorem antitone_isBddFun_has_tail_limits
    {Z : ℝ → ℝ} (hZ : Antitone Z) (hB : IsBddFun Z) :
    (∃ La : ℝ, Tendsto Z atBot (𝓝 La)) ∧
      ∃ Lb : ℝ, Tendsto Z atTop (𝓝 Lb) :=
  ⟨antitone_isBddFun_tendsto_atBot hZ hB,
    antitone_isBddFun_tendsto_atTop hZ hB⟩

theorem InMonotoneWaveTrapSet.leftTail_Icc
    {κ M : ℝ} {u : ℝ → ℝ}
    (hu : InMonotoneWaveTrapSet κ M u) :
    ∃ Lu : ℝ, Tendsto u atBot (𝓝 Lu) ∧ 0 ≤ Lu ∧ Lu ≤ M := by
  rcases antitone_isBddFun_tendsto_atBot hu.antitone hu.trap.cunif_bdd.2 with
    ⟨Lu, hLu⟩
  have hnonneg : 0 ≤ Lu := by
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hLu
      (Eventually.of_forall hu.nonneg)
  have hleM : Lu ≤ M := by
    exact le_of_tendsto_of_tendsto hLu tendsto_const_nhds
      (Eventually.of_forall hu.le_M)
  exact ⟨Lu, hLu, hnonneg, hleM⟩

/-- Continuity of the expanded paper step source from the expected per-step
regularity data. -/
theorem paperStepSource_continuous
    (p : CMParams) (c lam : ℝ) {u Z W : ℝ → ℝ}
    (hZ : Continuous Z) (hW : Continuous W)
    (hWderiv : Continuous (deriv W))
    (hV : Continuous (frozenElliptic p u))
    (hVderiv : Continuous (deriv (frozenElliptic p u))) :
    Continuous (paperStepSource p c lam u Z W) := by
  have hm1 : 0 ≤ p.m - 1 := by linarith [p.hm]
  have hα : 0 ≤ p.α := by linarith [p.hα]
  have hmg1 : 0 ≤ p.m + p.γ - 1 := by linarith [p.hm, p.hγ]
  have hWm1 : Continuous (fun x => (W x) ^ (p.m - 1)) :=
    hW.rpow_const (fun _ => Or.inr hm1)
  have hWα : Continuous (fun x => (W x) ^ p.α) :=
    hW.rpow_const (fun _ => Or.inr hα)
  have hWmg1 : Continuous (fun x => (W x) ^ (p.m + p.γ - 1)) :=
    hW.rpow_const (fun _ => Or.inr hmg1)
  have hterm1 : Continuous (fun x =>
      (-p.χ * p.m) * (W x) ^ (p.m - 1) *
        deriv (frozenElliptic p u) x * deriv W x) :=
    ((continuous_const.mul hWm1).mul hVderiv).mul hWderiv
  have hinner : Continuous (fun x =>
      1 - p.χ * (W x) ^ (p.m - 1) * frozenElliptic p u x
        - ((W x) ^ p.α - p.χ * (W x) ^ (p.m + p.γ - 1))) :=
    (continuous_const.sub ((continuous_const.mul hWm1).mul hV)).sub
      (hWα.sub (continuous_const.mul hWmg1))
  have hnonlin : Continuous (paperStepNonlinearity p u W) := by
    unfold paperStepNonlinearity
    dsimp only
    exact hterm1.add (hW.mul hinner)
  unfold paperStepSource
  exact hnonlin.add (continuous_const.mul hZ)

/-- `C¹` regularity of the expanded paper-step source away from zeros of `W`.

This is the smooth-source bootstrap used by the mollified approximants once a
strict-positivity/nonzero input is available.  Without such an input, the real
powers `W^r` at zeros are the remaining source-regularity frontier. -/
theorem paperStepSource_contDiff_one_of_nonzero
    (p : CMParams) (c lam : ℝ) {u Z W : ℝ → ℝ}
    (hZ : ContDiff ℝ 1 Z)
    (hW : ContDiff ℝ 2 W)
    (hWnz : ∀ x, W x ≠ 0)
    (hV : ContDiff ℝ 2 (frozenElliptic p u)) :
    ContDiff ℝ 1 (paperStepSource p c lam u Z W) := by
  let V := frozenElliptic p u
  have hW1 : ContDiff ℝ 1 W := hW.of_le (by norm_num)
  have hV1 : ContDiff ℝ 1 V := hV.of_le (by norm_num)
  have hWd : ContDiff ℝ 1 (deriv W) := by
    have hW2 : ContDiff ℝ ((1 : ℕ∞) + 1) W := by simpa using hW
    exact (contDiff_succ_iff_deriv.mp hW2).2.2
  have hVd : ContDiff ℝ 1 (deriv V) := by
    have hV2 : ContDiff ℝ ((1 : ℕ∞) + 1) V := by simpa [V] using hV
    exact (contDiff_succ_iff_deriv.mp hV2).2.2
  have hWm1 : ContDiff ℝ 1 (fun x => W x ^ (p.m - 1)) :=
    hW1.rpow_const_of_ne hWnz
  have hWa : ContDiff ℝ 1 (fun x => W x ^ p.α) :=
    hW1.rpow_const_of_ne hWnz
  have hWmg : ContDiff ℝ 1 (fun x => W x ^ (p.m + p.γ - 1)) :=
    hW1.rpow_const_of_ne hWnz
  have hchem : ContDiff ℝ 1
      (fun x => -p.χ * p.m * W x ^ (p.m - 1) * deriv V x * deriv W x) := by
    exact (((contDiff_const :
      ContDiff ℝ 1 (fun _ : ℝ => -p.χ * p.m)).mul hWm1).mul hVd).mul hWd
  have hinner1 : ContDiff ℝ 1
      (fun x => p.χ * W x ^ (p.m - 1) * V x) := by
    exact (((contDiff_const :
      ContDiff ℝ 1 (fun _ : ℝ => p.χ)).mul hWm1).mul hV1)
  have hinner2 : ContDiff ℝ 1
      (fun x => W x ^ p.α - p.χ * W x ^ (p.m + p.γ - 1)) := by
    have hright : ContDiff ℝ 1
        (fun x => p.χ * W x ^ (p.m + p.γ - 1)) := by
      exact contDiff_const.mul hWmg
    exact hWa.sub hright
  have hbracket : ContDiff ℝ 1
      (fun x => 1 - p.χ * W x ^ (p.m - 1) * V x -
        (W x ^ p.α - p.χ * W x ^ (p.m + p.γ - 1))) := by
    exact (contDiff_const.sub hinner1).sub hinner2
  have hreac : ContDiff ℝ 1
      (fun x => W x * (1 - p.χ * W x ^ (p.m - 1) * V x -
        (W x ^ p.α - p.χ * W x ^ (p.m + p.γ - 1)))) :=
    hW1.mul hbracket
  have hlin : ContDiff ℝ 1 (fun x => lam * Z x) :=
    contDiff_const.mul hZ
  have htotal : ContDiff ℝ 1
      (fun x =>
        (-p.χ * p.m * W x ^ (p.m - 1) * deriv V x * deriv W x +
          W x * (1 - p.χ * W x ^ (p.m - 1) * V x -
            (W x ^ p.α - p.χ * W x ^ (p.m + p.γ - 1)))) +
          lam * Z x) :=
    (hchem.add hreac).add hlin
  convert htotal using 1

/-- Boundedness of the expanded paper step source from bounded `Z`, `W`, `W'`,
`V`, and `V'`, with the usual nonnegative trapped range for `W`. -/
theorem paperStepSource_bddFun
    (p : CMParams) (c lam : ℝ) {u Z W : ℝ → ℝ}
    (hZ : IsBddFun Z) (hW : IsBddFun W) (hWnn : ∀ x, 0 ≤ W x)
    (hWderiv : IsBddFun (deriv W))
    (hV : IsBddFun (frozenElliptic p u))
    (hVderiv : IsBddFun (deriv (frozenElliptic p u))) :
    IsBddFun (paperStepSource p c lam u Z W) := by
  have hm1 : 0 ≤ p.m - 1 := by linarith [p.hm]
  have hα : 0 ≤ p.α := by linarith [p.hα]
  have hmg1 : 0 ≤ p.m + p.γ - 1 := by linarith [p.hm, p.hγ]
  have hWm1 := IsBddFun.rpow_of_nonneg hW hm1 hWnn
  have hWα := IsBddFun.rpow_of_nonneg hW hα hWnn
  have hWmg1 := IsBddFun.rpow_of_nonneg hW hmg1 hWnn
  have hterm1 : IsBddFun (fun x =>
      (-p.χ * p.m) * (W x) ^ (p.m - 1) *
        deriv (frozenElliptic p u) x * deriv W x) :=
    IsBddFun.mul
      (IsBddFun.mul (IsBddFun.const_mul (-p.χ * p.m) hWm1) hVderiv)
      hWderiv
  have hinner : IsBddFun (fun x =>
      1 - p.χ * (W x) ^ (p.m - 1) * frozenElliptic p u x
        - ((W x) ^ p.α - p.χ * (W x) ^ (p.m + p.γ - 1))) := by
    exact IsBddFun.sub
      (IsBddFun.sub (IsBddFun.const 1)
        (IsBddFun.mul (IsBddFun.const_mul p.χ hWm1) hV))
      (IsBddFun.sub hWα (IsBddFun.const_mul p.χ hWmg1))
  have hnonlin : IsBddFun (paperStepNonlinearity p u W) := by
    unfold paperStepNonlinearity
    dsimp only
    exact IsBddFun.add hterm1 (IsBddFun.mul hW hinner)
  unfold paperStepSource
  exact IsBddFun.add hnonlin (IsBddFun.const_mul lam hZ)

/-- Structural data sufficient to close the two finite tails of the paper-step
source.  It deliberately carries no tail limit for `R` itself. -/
structure PaperStepSourceTailData
    (p : CMParams) (u Z W : ℝ → ℝ) : Prop where
  Z_antitone : Antitone Z
  Z_bdd : IsBddFun Z
  W_antitone : Antitone W
  W_bdd : IsBddFun W
  V_tail_bot : ∃ Va : ℝ, Tendsto (frozenElliptic p u) atBot (𝓝 Va)
  V_tail_top : ∃ Vb : ℝ, Tendsto (frozenElliptic p u) atTop (𝓝 Vb)
  V_deriv_tail_bot :
    Tendsto (fun x => deriv (frozenElliptic p u) x) atBot (𝓝 0)
  V_deriv_tail_top :
    Tendsto (fun x => deriv (frozenElliptic p u) x) atTop (𝓝 0)

theorem paperStepSource_tendsto_of_value_tails
    (p : CMParams) (c lam : ℝ) {u Z W : ℝ → ℝ} {l : Filter ℝ}
    {Za Wa Va : ℝ}
    (hZtail : Tendsto Z l (𝓝 Za))
    (hWtail : Tendsto W l (𝓝 Wa))
    (hVtail : Tendsto (frozenElliptic p u) l (𝓝 Va))
    (hVderiv_tail : Tendsto (fun x => deriv (frozenElliptic p u) x) l (𝓝 0))
    (hWderiv_bdd : IsBddFun (deriv W)) :
    ∃ Ra : ℝ, Tendsto (paperStepSource p c lam u Z W) l (𝓝 Ra) := by
  have hm1 : 0 ≤ p.m - 1 := by linarith [p.hm]
  have hα : 0 ≤ p.α := by linarith [p.hα]
  have hmg1 : 0 ≤ p.m + p.γ - 1 := by linarith [p.hm, p.hγ]
  have hWm1 :
      Tendsto (fun x => (W x) ^ (p.m - 1)) l (𝓝 (Wa ^ (p.m - 1))) :=
    hWtail.rpow_const (Or.inr hm1)
  have hWα :
      Tendsto (fun x => (W x) ^ p.α) l (𝓝 (Wa ^ p.α)) :=
    hWtail.rpow_const (Or.inr hα)
  have hWmg1 :
      Tendsto (fun x => (W x) ^ (p.m + p.γ - 1)) l
        (𝓝 (Wa ^ (p.m + p.γ - 1))) :=
    hWtail.rpow_const (Or.inr hmg1)
  have hVdW :
      Tendsto (fun x => deriv (frozenElliptic p u) x * deriv W x) l (𝓝 0) :=
    tendsto_mul_zero_of_isBddFun hVderiv_tail hWderiv_bdd
  have hchem :
      Tendsto
        (fun x =>
          -p.χ * p.m * (W x) ^ (p.m - 1) *
            deriv (frozenElliptic p u) x * deriv W x) l
        (𝓝 0) := by
    have hmul0 : Tendsto
        (fun x => (W x) ^ (p.m - 1) *
          (deriv (frozenElliptic p u) x * deriv W x)) l
        (𝓝 (Wa ^ (p.m - 1) * 0)) :=
      hWm1.mul hVdW
    have hconst := hmul0.const_mul (-p.χ * p.m)
    simpa [mul_assoc] using hconst
  have hχWm1V :
      Tendsto
        (fun x => p.χ * (W x) ^ (p.m - 1) * frozenElliptic p u x) l
        (𝓝 (p.χ * Wa ^ (p.m - 1) * Va)) := by
    have hmul := hWm1.mul hVtail
    have hconst := hmul.const_mul p.χ
    simpa [mul_assoc] using hconst
  have hχWmg1 :
      Tendsto (fun x => p.χ * (W x) ^ (p.m + p.γ - 1)) l
        (𝓝 (p.χ * Wa ^ (p.m + p.γ - 1))) :=
    hWmg1.const_mul p.χ
  have hinner :
      Tendsto
        (fun x =>
          1 - p.χ * (W x) ^ (p.m - 1) * frozenElliptic p u x
            - ((W x) ^ p.α - p.χ * (W x) ^ (p.m + p.γ - 1))) l
        (𝓝
          (1 - p.χ * Wa ^ (p.m - 1) * Va
            - (Wa ^ p.α - p.χ * Wa ^ (p.m + p.γ - 1)))) := by
    exact (tendsto_const_nhds.sub hχWm1V).sub (hWα.sub hχWmg1)
  have hreac :
      Tendsto
        (fun x =>
          W x *
            (1 - p.χ * (W x) ^ (p.m - 1) * frozenElliptic p u x
              - ((W x) ^ p.α - p.χ * (W x) ^ (p.m + p.γ - 1)))) l
        (𝓝
          (Wa *
            (1 - p.χ * Wa ^ (p.m - 1) * Va
              - (Wa ^ p.α - p.χ * Wa ^ (p.m + p.γ - 1))))) :=
    hWtail.mul hinner
  have hlin : Tendsto (fun x => lam * Z x) l (𝓝 (lam * Za)) :=
    hZtail.const_mul lam
  refine ⟨
    0 +
      Wa *
        (1 - p.χ * Wa ^ (p.m - 1) * Va
          - (Wa ^ p.α - p.χ * Wa ^ (p.m + p.γ - 1))) +
      lam * Za, ?_⟩
  have htotal := (hchem.add hreac).add hlin
  refine htotal.congr' ?_
  filter_upwards with x
  unfold paperStepSource paperStepNonlinearity
  ring_nf

/-- The source `R = paperStepSource ...` has finite tails once `Z` and `W` are
bounded antitone profiles, `W'` is bounded, and the frozen elliptic field has
the displayed value and derivative tails. -/
theorem paperStepSource_tail_limits
    (p : CMParams) (c lam : ℝ) {u Z W : ℝ → ℝ}
    (hdata : PaperStepSourceTailData p u Z W)
    (hWderiv_bdd : IsBddFun (deriv W)) :
    (∃ Ra : ℝ, Tendsto (paperStepSource p c lam u Z W) atBot (𝓝 Ra)) ∧
      ∃ Rb : ℝ, Tendsto (paperStepSource p c lam u Z W) atTop (𝓝 Rb) := by
  rcases antitone_isBddFun_has_tail_limits hdata.Z_antitone hdata.Z_bdd with
    ⟨⟨Za, hZa⟩, ⟨Zb, hZb⟩⟩
  rcases antitone_isBddFun_has_tail_limits hdata.W_antitone hdata.W_bdd with
    ⟨⟨Wa, hWa⟩, ⟨Wb, hWb⟩⟩
  rcases hdata.V_tail_bot with ⟨Va, hVa⟩
  rcases hdata.V_tail_top with ⟨Vb, hVb⟩
  constructor
  · exact paperStepSource_tendsto_of_value_tails
      (p := p) (c := c) (lam := lam) (u := u) (Z := Z) (W := W)
      hZa hWa hVa hdata.V_deriv_tail_bot hWderiv_bdd
  · exact paperStepSource_tendsto_of_value_tails
      (p := p) (c := c) (lam := lam) (u := u) (Z := Z) (W := W)
      hZb hWb hVb hdata.V_deriv_tail_top hWderiv_bdd

/-! ## Paper upper comparison -/

/-- Core paper upper-barrier maximum principle for one implicit step. -/
theorem paperImplicitStep_le_of_paperBarrier_maxPrinciple
    (p : CMParams) {c h M C_chem : ℝ} {u Z W B : ℝ → ℝ} {x₀ : ℝ}
    (hh : 0 < h)
    (hCB : h * (reactionLip p.α M + C_chem) < 1)
    (hstep : ∀ x, paperImplicitStepOp p c h u W x = Z x)
    (hBsuper : paperWaveOperator p c u B x₀ ≤ 0)
    (hZB : ∀ x, Z x ≤ B x)
    (hattain : IsMaxOn (fun x => W x - B x) Set.univ x₀)
    (hpaperDiff :
      paperWaveOperator p c u W x₀ - paperWaveOperator p c u B x₀
        ≤ (reactionLip p.α M + C_chem) * (W x₀ - B x₀)) :
    ∀ x, W x ≤ B x := by
  have hmax : ∀ x, W x - B x ≤ W x₀ - B x₀ := by
    intro x
    have := hattain (Set.mem_univ x)
    simpa using this
  suffices hx₀_nonpos : W x₀ - B x₀ ≤ 0 by
    intro x
    have := hmax x
    linarith
  by_contra hpos_not
  push Not at hpos_not
  have hGW :
      W x₀ - h * paperWaveOperator p c u W x₀ = Z x₀ := by
    have := hstep x₀
    simpa [paperImplicitStepOp_apply] using this
  have hGB_ge_B :
      B x₀ ≤ B x₀ - h * paperWaveOperator p c u B x₀ := by
    have hmul : h * paperWaveOperator p c u B x₀ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hh.le hBsuper
    linarith
  have hGW_le_GB :
      W x₀ - h * paperWaveOperator p c u W x₀
        ≤ B x₀ - h * paperWaveOperator p c u B x₀ := by
    calc
      W x₀ - h * paperWaveOperator p c u W x₀
          = Z x₀ := hGW
      _ ≤ B x₀ := hZB x₀
      _ ≤ B x₀ - h * paperWaveOperator p c u B x₀ := hGB_ge_B
  have hGdiff :
      (W x₀ - B x₀) - h *
          (paperWaveOperator p c u W x₀ - paperWaveOperator p c u B x₀)
        ≤ 0 := by
    linarith
  set Δ := W x₀ - B x₀ with hΔ
  set CB := reactionLip p.α M + C_chem with hCBdef
  have hΔpos : 0 < Δ := hpos_not
  have hstep_le :
      h * (paperWaveOperator p c u W x₀ - paperWaveOperator p c u B x₀)
        ≤ h * (CB * Δ) :=
    mul_le_mul_of_nonneg_left hpaperDiff hh.le
  have hcoef_pos : 0 < 1 - h * CB := by
    linarith [hCB]
  have hbig_pos : 0 < (1 - h * CB) * Δ :=
    mul_pos hcoef_pos hΔpos
  nlinarith [hGdiff, hstep_le, hbig_pos]

/-- Clean paper upper-barrier comparison; max attainment is discharged here. -/
theorem paperImplicitStep_le_of_paperBarrier_maxPrinciple_clean
    (p : CMParams) {c h M C_chem : ℝ} {u Z W B : ℝ → ℝ} {La Lb : ℝ}
    (hh : 0 < h)
    (hCB : h * (reactionLip p.α M + C_chem) < 1)
    (hstep : ∀ x, paperImplicitStepOp p c h u W x = Z x)
    (hZB : ∀ x, Z x ≤ B x)
    (hφcont : Continuous (fun x => W x - B x))
    (hbot : Tendsto (fun x => W x - B x) atBot (𝓝 La)) (hLa : La ≤ 0)
    (htop : Tendsto (fun x => W x - B x) atTop (𝓝 Lb)) (hLb : Lb ≤ 0)
    (hpaperSuper : ∀ x₀, IsMaxOn (fun x => W x - B x) Set.univ x₀ →
        paperWaveOperator p c u B x₀ ≤ 0)
    (hpaperDiff : ∀ x₀, IsMaxOn (fun x => W x - B x) Set.univ x₀ →
      paperWaveOperator p c u W x₀ - paperWaveOperator p c u B x₀
        ≤ (reactionLip p.α M + C_chem) * (W x₀ - B x₀)) :
    ∀ x, W x ≤ B x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x₁, hx₁⟩ := hcon
  have hpos₁ : 0 < W x₁ - B x₁ := by
    linarith
  obtain ⟨x₀, hattain, _hx₀pos⟩ :=
    exists_isMaxOn_pos_of_tendsto_nonpos (φ := fun x => W x - B x)
      hφcont hbot hLa htop hLb hpos₁
  have hle :=
    paperImplicitStep_le_of_paperBarrier_maxPrinciple
      (p := p) (c := c) (h := h) (M := M) (C_chem := C_chem)
      (u := u) (Z := Z) (W := W) (B := B) (x₀ := x₀)
      hh hCB hstep (hpaperSuper x₀ hattain) hZB hattain
      (hpaperDiff x₀ hattain)
  have := hle x₁
  linarith

/-! ## Green-step input and producer assembly -/

/-- Green analytic data for one paper step. -/
structure PaperStepAnalytic
    (p : CMParams) (c lam M κ Λ : ℝ) (u Z W : ℝ → ℝ) where
  R : ℝ → ℝ
  source_eq : R = paperStepSource p c lam u Z W
  green_repr : W = fun x => greenConv c lam R x
  conv_form : W = fun x => ∫ y, greenKernel c lam (x - y) * R y
  R_cont : Continuous R
  R_bound : ∃ B : ℝ, (∀ y, |R y| ≤ B) ∧
    Λ = 2 * (greenDelta c lam)⁻¹ * B
  R_hi : ∀ x, IntegrableOn (gWeight (greenRootPlus c lam) R) (Ioi x)
  R_lo : ∀ x, IntegrableOn (gWeight (greenRootMinus c lam) R) (Iic x)
  R_int_trans : ∀ x, Integrable (fun t => greenKernel c lam (-t) * R (x + t))

/-- Upper comparison data for a paper step against a barrier `B`. -/
structure PaperStepUpperData
    (p : CMParams) (c lam M C_chem : ℝ)
    (u Z W B : ℝ → ℝ) where
  hCB : (1 / lam) * (reactionLip p.α M + C_chem) < 1
  ZB : ∀ x, Z x ≤ B x
  φcont : Continuous (fun x => W x - B x)
  La : ℝ
  Lb : ℝ
  hbot : Tendsto (fun x => W x - B x) atBot (𝓝 La)
  hLa : La ≤ 0
  htop : Tendsto (fun x => W x - B x) atTop (𝓝 Lb)
  hLb : Lb ≤ 0
  paperSuper : ∀ x₀, IsMaxOn (fun x => W x - B x) Set.univ x₀ →
    paperWaveOperator p c u B x₀ ≤ 0
  paperDiff : ∀ x₀, IsMaxOn (fun x => W x - B x) Set.univ x₀ →
    paperWaveOperator p c u W x₀ - paperWaveOperator p c u B x₀
      ≤ (reactionLip p.α M + C_chem) * (W x₀ - B x₀)

/-- The paperDiff-free upper data actually consumed by the spatially truncated
maximum principle. -/
structure PaperStepUpperTruncatedData
    (p : CMParams) (c lam M C_chem : ℝ)
    (u Z W B : ℝ → ℝ) where
  hCB : (1 / lam) * (reactionLip p.α M + C_chem) < 1
  ZB : ∀ x, Z x ≤ B x
  φcont : Continuous (fun x => W x - B x)
  La : ℝ
  Lb : ℝ
  hbot : Tendsto (fun x => W x - B x) atBot (𝓝 La)
  hLa : La ≤ 0
  htop : Tendsto (fun x => W x - B x) atTop (𝓝 Lb)
  hLb : Lb ≤ 0
  paperSuper : ∀ x₀, IsMaxOn (fun x => W x - B x) Set.univ x₀ →
    paperWaveOperator p c u B x₀ ≤ 0

namespace PaperStepUpperData

def toTruncated
    {p : CMParams} {c lam M C_chem : ℝ} {u Z W B : ℝ → ℝ}
    (h : PaperStepUpperData p c lam M C_chem u Z W B) :
    PaperStepUpperTruncatedData p c lam M C_chem u Z W B :=
  { hCB := h.hCB
    ZB := h.ZB
    φcont := h.φcont
    La := h.La
    Lb := h.Lb
    hbot := h.hbot
    hLa := h.hLa
    htop := h.htop
    hLb := h.hLb
    paperSuper := h.paperSuper }

end PaperStepUpperData

/-- Lower comparison data for a paper step against a sub-barrier `A`. -/
structure PaperStepLowerData
    (p : CMParams) (c lam M C_chem : ℝ)
    (u Z W A : ℝ → ℝ) where
  hCB : (1 / lam) * (reactionLip p.α M + C_chem) < 1
  AZ : ∀ x, A x ≤ Z x
  φcont : Continuous (fun x => A x - W x)
  La : ℝ
  Lb : ℝ
  hbot : Tendsto (fun x => A x - W x) atBot (𝓝 La)
  hLa : La ≤ 0
  htop : Tendsto (fun x => A x - W x) atTop (𝓝 Lb)
  hLb : Lb ≤ 0
  paperSub : ∀ x₀, IsMaxOn (fun x => A x - W x) Set.univ x₀ →
    0 ≤ paperWaveOperator p c u A x₀
  paperDiff : ∀ x₀, IsMaxOn (fun x => A x - W x) Set.univ x₀ →
    paperWaveOperator p c u A x₀ - paperWaveOperator p c u W x₀
      ≤ (reactionLip p.α M + C_chem) * (A x₀ - W x₀)

/-- The paperDiff-free lower data actually consumed by the spatially truncated
maximum principle. -/
structure PaperStepLowerTruncatedData
    (p : CMParams) (c lam M C_chem : ℝ)
    (u Z W A : ℝ → ℝ) where
  hCB : (1 / lam) * (reactionLip p.α M + C_chem) < 1
  AZ : ∀ x, A x ≤ Z x
  φcont : Continuous (fun x => A x - W x)
  La : ℝ
  Lb : ℝ
  hbot : Tendsto (fun x => A x - W x) atBot (𝓝 La)
  hLa : La ≤ 0
  htop : Tendsto (fun x => A x - W x) atTop (𝓝 Lb)
  hLb : Lb ≤ 0
  paperSub : ∀ x₀, IsMaxOn (fun x => A x - W x) Set.univ x₀ →
    0 ≤ paperWaveOperator p c u A x₀

namespace PaperStepLowerData

def toTruncated
    {p : CMParams} {c lam M C_chem : ℝ} {u Z W A : ℝ → ℝ}
    (h : PaperStepLowerData p c lam M C_chem u Z W A) :
    PaperStepLowerTruncatedData p c lam M C_chem u Z W A :=
  { hCB := h.hCB
    AZ := h.AZ
    φcont := h.φcont
    La := h.La
    Lb := h.Lb
    hbot := h.hbot
    hLa := h.hLa
    htop := h.htop
    hLb := h.hLb
    paperSub := h.paperSub }

end PaperStepLowerData

/-- Sliding comparison data for proving `W` antitone.

For every shift `s ≥ 0`, the shifted profile `W_s(x)=W(x+s)` is compared as the
solution of the shifted-frozen paper step with `u_s(x)=u(x+s)` and old iterate
`Z_s(x)=Z(x+s)`.  The only operator-specific residual is the local shifted
one-sided estimate at a positive maximum of `W_s-W`. -/
structure PaperStepAntitoneData
    (p : CMParams) (c lam M C_chem : ℝ)
    (u Z W : ℝ → ℝ) where
  hCB : (1 / lam) * (reactionLip p.α M + C_chem) < 1
  shiftedStepEq : ∀ s, 0 ≤ s → ∀ x,
    paperImplicitStepOp p c (1 / lam) (fun y => u (y + s)) (fun y => W (y + s)) x =
      Z (x + s)
  φcont : ∀ s, 0 ≤ s → Continuous (fun x => W (x + s) - W x)
  La : ℝ → ℝ
  Lb : ℝ → ℝ
  hbot : ∀ s, 0 ≤ s → Tendsto (fun x => W (x + s) - W x) atBot (𝓝 (La s))
  hLa : ∀ s, 0 ≤ s → La s ≤ 0
  htop : ∀ s, 0 ≤ s → Tendsto (fun x => W (x + s) - W x) atTop (𝓝 (Lb s))
  hLb : ∀ s, 0 ≤ s → Lb s ≤ 0
  shiftedOneSided : ∀ s, 0 ≤ s → ∀ x₀,
    IsMaxOn (fun x => W (x + s) - W x) Set.univ x₀ →
      0 < W (x₀ + s) - W x₀ →
      paperWaveOperator p c (fun y => u (y + s)) (fun y => W (y + s)) x₀ -
          paperWaveOperator p c u W x₀
        ≤ (reactionLip p.α M + C_chem) * (W (x₀ + s) - W x₀)

theorem paperStep_deriv_le
    {p : CMParams} {M κ Λ : ℝ} {u Z W : ℝ → ℝ}
    (hlam : 0 < lam) (ha : PaperStepAnalytic p c lam M κ Λ u Z W) :
    ∀ x, |deriv W x| ≤ Λ := by
  obtain ⟨B, hBbd, hΛ⟩ := ha.R_bound
  intro x
  have hbound : |deriv (greenConv c lam ha.R) x|
      ≤ 2 * (greenDelta c lam)⁻¹ * B :=
    crossImplicitStep_deriv_bound (c := c) (lam := lam) hlam
      ha.R_cont hBbd ha.R_hi ha.R_lo x
  have hderivEq : deriv W x = deriv (greenConv c lam ha.R) x :=
    congrArg (fun f => deriv f x) ha.green_repr
  calc
    |deriv W x| = |deriv (greenConv c lam ha.R) x| := congrArg abs hderivEq
    _ ≤ 2 * (greenDelta c lam)⁻¹ * B := hbound
    _ = Λ := hΛ.symm

theorem paperStep_diff
    {p : CMParams} {M κ Λ : ℝ} {u Z W : ℝ → ℝ}
    (_hlam : 0 < lam) (ha : PaperStepAnalytic p c lam M κ Λ u Z W) :
    Differentiable ℝ W := by
  rw [ha.green_repr]
  intro x
  exact (greenConv_hasDerivAt
    (c := c) (lam := lam) ha.R_cont ha.R_hi ha.R_lo x).differentiableAt

theorem paperStep_cont
    {p : CMParams} {M κ Λ : ℝ} {u Z W : ℝ → ℝ}
    (hlam : 0 < lam) (ha : PaperStepAnalytic p c lam M κ Λ u Z W) :
    Continuous W :=
  (paperStep_diff (c := c) (lam := lam) hlam ha).continuous

/-! ## Green regularity bootstrap

The committed Green identity gives `W = greenConv c lam R`.  A continuous source
gives `W ∈ C²`; if the source is `C¹`, the explicit tail formulas bootstrap the
same representation to `W ∈ C³`.  The latter is the sharp interface for the
paper Route-A maximum principle: `paperStepSource` contains the term `lam * Z`,
so a merely continuous old iterate cannot yield a `C³` next step from the
second-order resolvent alone. -/

theorem tailHi_contDiff_one {r : ℝ} {H : ℝ → ℝ} (hH : Continuous H)
    (hHi : ∀ t : ℝ, IntegrableOn (gWeight r H) (Ioi t)) :
    ContDiff ℝ 1 (tailHi r H) := by
  have hdiff : Differentiable ℝ (tailHi r H) :=
    fun x => (tailHi_hasDerivAt hH hHi x).differentiableAt
  have hderiv : deriv (tailHi r H) = fun x => -gWeight r H x := by
    funext x
    exact (tailHi_hasDerivAt hH hHi x).deriv
  have hcont : Continuous (deriv (tailHi r H)) := by
    rw [hderiv]
    exact (gWeight_continuous (r := r) hH).neg
  exact contDiff_one_iff_deriv.2 ⟨hdiff, hcont⟩

theorem tailLo_contDiff_one {r : ℝ} {H : ℝ → ℝ} (hH : Continuous H)
    (hLo : ∀ t : ℝ, IntegrableOn (gWeight r H) (Iic t)) :
    ContDiff ℝ 1 (tailLo r H) := by
  have hdiff : Differentiable ℝ (tailLo r H) :=
    fun x => (tailLo_hasDerivAt hH hLo x).differentiableAt
  have hderiv : deriv (tailLo r H) = fun x => gWeight r H x := by
    funext x
    exact (tailLo_hasDerivAt hH hLo x).deriv
  have hcont : Continuous (deriv (tailLo r H)) := by
    rw [hderiv]
    exact gWeight_continuous (r := r) hH
  exact contDiff_one_iff_deriv.2 ⟨hdiff, hcont⟩

theorem greenConvDeriv2_contDiff_one {H : ℝ → ℝ} (hH : ContDiff ℝ 1 H)
    (hHi : ∀ t : ℝ, IntegrableOn (gWeight (greenRootPlus c lam) H) (Ioi t))
    (hLo : ∀ t : ℝ, IntegrableOn (gWeight (greenRootMinus c lam) H) (Iic t)) :
    ContDiff ℝ 1 (greenConvDeriv2 c lam H) := by
  unfold greenConvDeriv2
  have hHc : Continuous H := hH.continuous
  have hTH : ContDiff ℝ 1 (tailHi (greenRootPlus c lam) H) :=
    tailHi_contDiff_one hHc hHi
  have hTL : ContDiff ℝ 1 (tailLo (greenRootMinus c lam) H) :=
    tailLo_contDiff_one hHc hLo
  fun_prop

theorem greenConvDeriv_contDiff_two {H : ℝ → ℝ} (hH : ContDiff ℝ 1 H)
    (hHi : ∀ t : ℝ, IntegrableOn (gWeight (greenRootPlus c lam) H) (Ioi t))
    (hLo : ∀ t : ℝ, IntegrableOn (gWeight (greenRootMinus c lam) H) (Iic t)) :
    ContDiff ℝ 2 (greenConvDeriv c lam H) := by
  have hHc : Continuous H := hH.continuous
  have hdiff : Differentiable ℝ (greenConvDeriv c lam H) :=
    fun x => (greenConvDeriv_hasDerivAt hHc hHi hLo x).differentiableAt
  have hderiv : deriv (greenConvDeriv c lam H) = greenConvDeriv2 c lam H := by
    funext x
    exact (greenConvDeriv_hasDerivAt hHc hHi hLo x).deriv
  have hone : ContDiff ℝ 1 (deriv (greenConvDeriv c lam H)) := by
    rw [hderiv]
    exact greenConvDeriv2_contDiff_one hH hHi hLo
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨hdiff, ?_, hone⟩
  intro hω
  exact absurd hω (by decide)

theorem greenConv_contDiff_three {H : ℝ → ℝ} (hH : ContDiff ℝ 1 H)
    (hHi : ∀ t : ℝ, IntegrableOn (gWeight (greenRootPlus c lam) H) (Ioi t))
    (hLo : ∀ t : ℝ, IntegrableOn (gWeight (greenRootMinus c lam) H) (Iic t)) :
    ContDiff ℝ 3 (greenConv c lam H) := by
  have hHc : Continuous H := hH.continuous
  have hdiff : Differentiable ℝ (greenConv c lam H) :=
    fun x => (greenConv_hasDerivAt hHc hHi hLo x).differentiableAt
  have hderiv : deriv (greenConv c lam H) = greenConvDeriv c lam H := by
    funext x
    exact (greenConv_hasDerivAt hHc hHi hLo x).deriv
  have htwo : ContDiff ℝ 2 (deriv (greenConv c lam H)) := by
    rw [hderiv]
    exact greenConvDeriv_contDiff_two hH hHi hLo
  rw [show (3 : WithTop ℕ∞) = 2 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨hdiff, ?_, htwo⟩
  intro hω
  exact absurd hω (by decide)

theorem paperStep_step_op
    {p : CMParams} {M κ Λ : ℝ} {u Z W : ℝ → ℝ}
    (hlam : 0 < lam) (ha : PaperStepAnalytic p c lam M κ Λ u Z W) :
    ∀ x, paperImplicitStepOp p c (1 / lam) u W x = Z x :=
  paperImplicitStepOp_of_greenConv_source
    (c := c) (lam := lam) hlam ha.source_eq ha.green_repr
    ha.R_cont ha.R_hi ha.R_lo

/-- Direct substep comparison for one paper implicit step.

If `A` satisfies `G_h(A) ≤ Z = G_h(W)`, then the usual maximum-principle trap
gives `A ≤ W`, provided the one-sided operator increment estimate holds at a
positive maximum of `A-W`. -/
theorem paperImplicitStep_le_of_directSubstep_maxPrinciple_clean
    (p : CMParams) {c h M C_chem : ℝ} {u Z W A : ℝ → ℝ} {La Lb : ℝ}
    (hh : 0 < h)
    (hCB : h * (reactionLip p.α M + C_chem) < 1)
    (hstep : ∀ x, paperImplicitStepOp p c h u W x = Z x)
    (hAstep : ∀ x, paperImplicitStepOp p c h u A x ≤ Z x)
    (hφcont : Continuous (fun x => A x - W x))
    (hbot : Tendsto (fun x => A x - W x) atBot (𝓝 La)) (hLa : La ≤ 0)
    (htop : Tendsto (fun x => A x - W x) atTop (𝓝 Lb)) (hLb : Lb ≤ 0)
    (hpaperDiff : ∀ x₀, IsMaxOn (fun x => A x - W x) Set.univ x₀ →
      paperWaveOperator p c u A x₀ - paperWaveOperator p c u W x₀
        ≤ (reactionLip p.α M + C_chem) * (A x₀ - W x₀)) :
    ∀ x, A x ≤ W x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x₁, hx₁⟩ := hcon
  have hpos₁ : 0 < A x₁ - W x₁ := by linarith
  obtain ⟨x₀, hattain, _hx₀pos⟩ :=
    exists_isMaxOn_pos_of_tendsto_nonpos (φ := fun x => A x - W x)
      hφcont hbot hLa htop hLb hpos₁
  have hmax : ∀ x, A x - W x ≤ A x₀ - W x₀ := by
    intro x
    have := hattain (Set.mem_univ x)
    simpa using this
  have hGW :
      W x₀ - h * paperWaveOperator p c u W x₀ = Z x₀ := by
    have := hstep x₀
    simpa [paperImplicitStepOp_apply] using this
  have hGA_le_Z :
      A x₀ - h * paperWaveOperator p c u A x₀ ≤ Z x₀ := by
    have := hAstep x₀
    simpa [paperImplicitStepOp_apply] using this
  have hGdiff :
      (A x₀ - W x₀) - h *
          (paperWaveOperator p c u A x₀ - paperWaveOperator p c u W x₀) ≤ 0 := by
    linarith
  set Δ := A x₀ - W x₀ with hΔ
  set CB := reactionLip p.α M + C_chem with hCBdef
  have hΔpos : 0 < Δ := lt_of_lt_of_le hpos₁ (by simpa [hΔ] using hmax x₁)
  have hstep_le :
      h * (paperWaveOperator p c u A x₀ - paperWaveOperator p c u W x₀)
        ≤ h * (CB * Δ) :=
    mul_le_mul_of_nonneg_left (hpaperDiff x₀ hattain) hh.le
  have hcoef_pos : 0 < 1 - h * CB := by linarith [hCB]
  have hbig_pos : 0 < (1 - h * CB) * Δ := mul_pos hcoef_pos hΔpos
  nlinarith [hGdiff, hstep_le, hbig_pos]

/-- Sliding/max-principle wrapper for the genuine shifted-frozen paper step.

For each `s ≥ 0`, the translated profile `W_s(x)=W(x+s)` solves the paper step
with translated frozen profile `u_s(x)=u(x+s)` and old iterate `Z_s(x)=Z(x+s)`.
At a positive maximum of `W_s-W`, the shifted one-sided paper-operator estimate
and `Antitone Z` give the algebraic contradiction. -/
theorem paperStep_preserves_antitone_by_shift
    (p : CMParams) {c h M C_chem : ℝ} {u Z W : ℝ → ℝ}
    (hh : 0 < h)
    (hCB : h * (reactionLip p.α M + C_chem) < 1)
    (hstep : ∀ x, paperImplicitStepOp p c h u W x = Z x)
    (hZanti : Antitone Z)
    (hshiftStep : ∀ s, 0 ≤ s → ∀ x,
      paperImplicitStepOp p c h (fun y => u (y + s)) (fun y => W (y + s)) x =
        Z (x + s))
    (hφcont : ∀ s, 0 ≤ s → Continuous (fun x => W (x + s) - W x))
    (La Lb : ℝ → ℝ)
    (hbot : ∀ s, 0 ≤ s → Tendsto (fun x => W (x + s) - W x) atBot (𝓝 (La s)))
    (hLa : ∀ s, 0 ≤ s → La s ≤ 0)
    (htop : ∀ s, 0 ≤ s → Tendsto (fun x => W (x + s) - W x) atTop (𝓝 (Lb s)))
    (hLb : ∀ s, 0 ≤ s → Lb s ≤ 0)
    (hshift : ∀ s, 0 ≤ s → ∀ x₀,
      IsMaxOn (fun x => W (x + s) - W x) Set.univ x₀ →
        0 < W (x₀ + s) - W x₀ →
          paperWaveOperator p c (fun y => u (y + s)) (fun y => W (y + s)) x₀ -
              paperWaveOperator p c u W x₀
            ≤ (reactionLip p.α M + C_chem) * (W (x₀ + s) - W x₀)) :
    Antitone W := by
  intro x₁ x₂ hx
  let s := x₂ - x₁
  have hs : 0 ≤ s := sub_nonneg.mpr hx
  have hshift_le : ∀ x, W (x + s) ≤ W x := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x₁, hx₁⟩ := hcon
    have hpos₁ : 0 < W (x₁ + s) - W x₁ := by linarith
    obtain ⟨x₀, hattain, _hx₀pos⟩ :=
      exists_isMaxOn_pos_of_tendsto_nonpos (φ := fun x => W (x + s) - W x)
        (hφcont s hs) (hbot s hs) (hLa s hs) (htop s hs) (hLb s hs) hpos₁
    have hmax : ∀ x, W (x + s) - W x ≤ W (x₀ + s) - W x₀ := by
      intro x
      have := hattain (Set.mem_univ x)
      simpa using this
    set Δ := W (x₀ + s) - W x₀ with hΔ
    set CB := reactionLip p.α M + C_chem with hCBdef
    have hΔpos : 0 < Δ := lt_of_lt_of_le hpos₁ (by simpa [hΔ] using hmax x₁)
    have hGW :
        W x₀ - h * paperWaveOperator p c u W x₀ = Z x₀ := by
      have := hstep x₀
      simpa [paperImplicitStepOp_apply] using this
    have hGshift :
        W (x₀ + s) -
            h * paperWaveOperator p c (fun y => u (y + s)) (fun y => W (y + s)) x₀
          = Z (x₀ + s) := by
      have := hshiftStep s hs x₀
      simpa [paperImplicitStepOp_apply] using this
    have hZle : Z (x₀ + s) ≤ Z x₀ :=
      hZanti (by linarith : x₀ ≤ x₀ + s)
    have hGdiff :
        Δ - h *
            (paperWaveOperator p c (fun y => u (y + s)) (fun y => W (y + s)) x₀ -
              paperWaveOperator p c u W x₀) ≤ 0 := by
      rw [hΔ]
      linarith
    have hstep_le :
        h *
            (paperWaveOperator p c (fun y => u (y + s)) (fun y => W (y + s)) x₀ -
              paperWaveOperator p c u W x₀)
          ≤ h * (CB * Δ) := by
      refine mul_le_mul_of_nonneg_left ?_ hh.le
      rw [hCBdef, hΔ]
      exact hshift s hs x₀ hattain hΔpos
    have hcoef_pos : 0 < 1 - h * CB := by linarith [hCB]
    have hbig_pos : 0 < (1 - h * CB) * Δ := mul_pos hcoef_pos hΔpos
    nlinarith [hGdiff, hstep_le, hbig_pos]
  have hx₂ : x₁ + s = x₂ := by
    dsimp [s]
    ring
  simpa [hx₂] using hshift_le x₁

/-- Sliding maximum-principle proof of antitonicity for one paper step.

For `s ≥ 0`, compare `W_s(x)=W(x+s)` against `W`, using the shifted-frozen
paper step equation and the shifted one-sided operator estimate. -/
theorem paperStep_antitone_by_sliding
    {p : CMParams} {M C_chem : ℝ} {u Z W : ℝ → ℝ}
    (hlam : 0 < lam)
    (hstep : ∀ x, paperImplicitStepOp p c (1 / lam) u W x = Z x)
    (hZanti : Antitone Z)
    (hd : PaperStepAntitoneData p c lam M C_chem u Z W) :
    Antitone W := by
  exact paperStep_preserves_antitone_by_shift
    (p := p) (c := c) (h := 1 / lam) (M := M) (C_chem := C_chem)
    (u := u) (Z := Z) (W := W) (one_div_pos.mpr hlam) hd.hCB hstep hZanti
    hd.shiftedStepEq hd.φcont hd.La hd.Lb hd.hbot hd.hLa hd.htop hd.hLb
    hd.shiftedOneSided

/-! ## Bounded-source Green bookkeeping

These lemmas close the Green-tail part of the paper per-step floor once the
source has been produced as a continuous bounded function.  They do not construct
the source or prove its monotonicity. -/

theorem gWeight_integrableOn_Ioi_of_bounded {r B : ℝ} {H : ℝ → ℝ}
    (hr : 0 < r) (hH : Continuous H) (hB : ∀ y, |H y| ≤ B) (x : ℝ) :
    IntegrableOn (gWeight r H) (Ioi x) := by
  have hdom : IntegrableOn (fun y : ℝ => B * Real.exp (-r * y)) (Ioi x) :=
    (integrableOn_exp_mul_Ioi (a := -r) (by linarith) x).const_mul B
  refine hdom.mono'
    (show AEStronglyMeasurable (gWeight r H) (volume.restrict (Ioi x)) from
      (gWeight_continuous (r := r) hH).aestronglyMeasurable.restrict)
    (Eventually.of_forall fun y => ?_)
  rw [gWeight, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-r * y) * |H y|
      ≤ Real.exp (-r * y) * B :=
        mul_le_mul_of_nonneg_left (hB y) (Real.exp_pos _).le
    _ = B * Real.exp (-r * y) := by ring

theorem gWeight_integrableOn_Iic_of_bounded {r B : ℝ} {H : ℝ → ℝ}
    (hr : r < 0) (hH : Continuous H) (hB : ∀ y, |H y| ≤ B) (x : ℝ) :
    IntegrableOn (gWeight r H) (Iic x) := by
  have hdom : IntegrableOn (fun y : ℝ => B * Real.exp (-r * y)) (Iic x) :=
    (integrableOn_exp_mul_Iic (a := -r) (by linarith) x).const_mul B
  refine hdom.mono'
    (show AEStronglyMeasurable (gWeight r H) (volume.restrict (Iic x)) from
      (gWeight_continuous (r := r) hH).aestronglyMeasurable.restrict)
    (Eventually.of_forall fun y => ?_)
  rw [gWeight, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-r * y) * |H y|
      ≤ Real.exp (-r * y) * B :=
        mul_le_mul_of_nonneg_left (hB y) (Real.exp_pos _).le
    _ = B * Real.exp (-r * y) := by ring

theorem PaperWeightedHolderSourceBox.gWeight_Ioi
    {κ M β B H : ℝ} {ω : ℝ → ℝ} {R : ℝ → ℝ}
    (hlam : 0 < lam) (hBnn : 0 ≤ B)
    (hR : PaperWeightedHolderSourceBox κ M β B H ω R) :
    ∀ t, IntegrableOn (gWeight (greenRootPlus c lam) R) (Ioi t) :=
  fun t => gWeight_integrableOn_Ioi_of_bounded
    (greenRootPlus_pos (c := c) hlam) hR.cont
    (hR.abs_le_const (B := B) hBnn) t

theorem PaperWeightedHolderSourceBox.gWeight_Iic
    {κ M β B H : ℝ} {ω : ℝ → ℝ} {R : ℝ → ℝ}
    (hlam : 0 < lam) (hBnn : 0 ≤ B)
    (hR : PaperWeightedHolderSourceBox κ M β B H ω R) :
    ∀ t, IntegrableOn (gWeight (greenRootMinus c lam) R) (Iic t) :=
  fun t => gWeight_integrableOn_Iic_of_bounded
    (greenRootMinus_neg (c := c) hlam) hR.cont
    (hR.abs_le_const (B := B) hBnn) t

theorem tailHi_weighted_abs_le_on {r B : ℝ} {H : ℝ → ℝ}
    (hr : 0 < r)
    (hHint : ∀ x, IntegrableOn (gWeight r H) (Ioi x))
    {x : ℝ} (hB : ∀ y, x ≤ y → |H y| ≤ B) :
    r * Real.exp (r * x) * |tailHi r H x| ≤ B := by
  have hBnn : 0 ≤ B := by
    have := hB x le_rfl
    exact le_trans (abs_nonneg _) this
  have hexp_int : IntegrableOn (fun y => B * Real.exp (-r * y)) (Ioi x) :=
    ((integrableOn_exp_mul_Ioi (a := -r) (by linarith) x).const_mul B)
  have hstep1 : |tailHi r H x| ≤ ∫ y in Ioi x, |gWeight r H y| := by
    rw [tailHi]
    have := norm_integral_le_integral_norm
      (μ := (volume : Measure ℝ).restrict (Ioi x)) (gWeight r H)
    simpa [Real.norm_eq_abs] using this
  have hptbd : ∀ y ∈ Ioi x, |gWeight r H y| ≤ B * Real.exp (-r * y) := by
    intro y hy
    rw [Set.mem_Ioi] at hy
    rw [gWeight, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-r * y) * |H y|
        ≤ Real.exp (-r * y) * B :=
          mul_le_mul_of_nonneg_left (hB y hy.le) (Real.exp_pos _).le
      _ = B * Real.exp (-r * y) := by ring
  have hstep2 :
      (∫ y in Ioi x, |gWeight r H y|) ≤ ∫ y in Ioi x, B * Real.exp (-r * y) :=
    setIntegral_mono_on ((hHint x).abs) hexp_int measurableSet_Ioi hptbd
  have hval : (∫ y in Ioi x, B * Real.exp (-r * y))
      = B * Real.exp (-r * x) / r := by
    rw [integral_const_mul, integral_exp_mul_Ioi (a := -r) (by linarith) x]
    have hrne : r ≠ 0 := ne_of_gt hr
    field_simp
  have htail_abs : |tailHi r H x| ≤ B * Real.exp (-r * x) / r :=
    le_trans hstep1 (le_trans hstep2 (le_of_eq hval))
  have hmul := mul_le_mul_of_nonneg_left htail_abs
    (by positivity : (0:ℝ) ≤ r * Real.exp (r * x))
  refine le_trans hmul (le_of_eq ?_)
  have hrne : r ≠ 0 := ne_of_gt hr
  have hexp : Real.exp (r * x) * Real.exp (-r * x) = 1 := by
    rw [← Real.exp_add, show r * x + -r * x = 0 from by ring, Real.exp_zero]
  have key : r * Real.exp (r * x) * (B * Real.exp (-r * x) / r)
      = B * (Real.exp (r * x) * Real.exp (-r * x)) := by
    field_simp
  rw [key, hexp, mul_one]

theorem tailLo_weighted_abs_le_on {r B : ℝ} {H : ℝ → ℝ}
    (hr : r < 0)
    (hHint : ∀ x, IntegrableOn (gWeight r H) (Iic x))
    {x : ℝ} (hB : ∀ y, y ≤ x → |H y| ≤ B) :
    (-r) * Real.exp (r * x) * |tailLo r H x| ≤ B := by
  have hBnn : 0 ≤ B := by
    have := hB x le_rfl
    exact le_trans (abs_nonneg _) this
  have hexp_int : IntegrableOn (fun y => B * Real.exp (-r * y)) (Iic x) :=
    ((integrableOn_exp_mul_Iic (a := -r) (by linarith) x).const_mul B)
  have hstep1 : |tailLo r H x| ≤ ∫ y in Iic x, |gWeight r H y| := by
    rw [tailLo]
    simpa [Real.norm_eq_abs] using
      norm_integral_le_integral_norm (μ := (volume : Measure ℝ).restrict (Iic x))
        (gWeight r H)
  have hptbd : ∀ y ∈ Iic x, |gWeight r H y| ≤ B * Real.exp (-r * y) := by
    intro y hy
    rw [Set.mem_Iic] at hy
    rw [gWeight, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-r * y) * |H y|
        ≤ Real.exp (-r * y) * B :=
          mul_le_mul_of_nonneg_left (hB y hy) (Real.exp_pos _).le
      _ = B * Real.exp (-r * y) := by ring
  have hstep2 :
      (∫ y in Iic x, |gWeight r H y|) ≤ ∫ y in Iic x, B * Real.exp (-r * y) :=
    setIntegral_mono_on ((hHint x).abs) hexp_int measurableSet_Iic hptbd
  have hval : (∫ y in Iic x, B * Real.exp (-r * y))
      = B * Real.exp (-r * x) / (-r) := by
    rw [integral_const_mul, integral_exp_mul_Iic (a := -r) (by linarith) x]
    have hrne : r ≠ 0 := ne_of_lt hr
    field_simp
  have htail_abs : |tailLo r H x| ≤ B * Real.exp (-r * x) / (-r) :=
    le_trans hstep1 (le_trans hstep2 (le_of_eq hval))
  have hnr : (0:ℝ) < -r := by linarith
  have hmul := mul_le_mul_of_nonneg_left htail_abs
    (le_of_lt (mul_pos hnr (Real.exp_pos (r * x))))
  refine le_trans hmul (le_of_eq ?_)
  have hnrne : (-r) ≠ 0 := ne_of_gt hnr
  have hexp : Real.exp (r * x) * Real.exp (-r * x) = 1 := by
    rw [← Real.exp_add, show r * x + -r * x = 0 from by ring, Real.exp_zero]
  have key : (-r) * Real.exp (r * x) * (B * Real.exp (-r * x) / (-r))
      = B * (Real.exp (r * x) * Real.exp (-r * x)) := by
    have hrne : r ≠ 0 := ne_of_lt hr
    field_simp [hrne]
  rw [key, hexp, mul_one]

theorem tailHi_upperBarrier_abs_le_on
    {r κ M B : ℝ} {H : ℝ → ℝ}
    (hrκ : 0 < r - κ) (hκ : 0 ≤ κ) (hM : 0 ≤ M) (hBnn : 0 ≤ B)
    (hHint : ∀ x, IntegrableOn (gWeight r H) (Ioi x))
    {x : ℝ} (hB : ∀ y, |H y| ≤ B * upperBarrier κ M y) :
    Real.exp (r * x) * |tailHi r H x| ≤
      B * upperBarrier κ M x / (r - κ) := by
  let C : ℝ := B * upperBarrier κ M x * Real.exp (-κ * x)
  have hdom : IntegrableOn (fun y : ℝ => C * Real.exp (-(r - κ) * y)) (Ioi x) :=
    (integrableOn_exp_mul_Ioi (a := -(r - κ)) (by linarith) x).const_mul C
  have hstep1 : |tailHi r H x| ≤ ∫ y in Ioi x, |gWeight r H y| := by
    rw [tailHi]
    have := norm_integral_le_integral_norm
      (μ := (volume : Measure ℝ).restrict (Ioi x)) (gWeight r H)
    simpa [Real.norm_eq_abs] using this
  have hptbd : ∀ y ∈ Ioi x,
      |gWeight r H y| ≤ C * Real.exp (-(r - κ) * y) := by
    intro y hy
    rw [Set.mem_Ioi] at hy
    have hyx : x ≤ y := hy.le
    have habs : |x - y| = y - x := by
      rw [abs_of_nonpos (sub_nonpos.mpr hyx)]
      ring
    have hshift :
        upperBarrier κ M y ≤
          Real.exp (κ * (y - x)) * upperBarrier κ M x := by
      simpa [habs] using
        (upperBarrier_shift_le_exp_abs_mul
          (κ := κ) (M := M) (x := x) (y := y) hκ hM)
    have hHy : |H y| ≤ B * (Real.exp (κ * (y - x)) * upperBarrier κ M x) := by
      exact (hB y).trans (mul_le_mul_of_nonneg_left hshift hBnn)
    rw [gWeight, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-r * y) * |H y|
          ≤ Real.exp (-r * y) *
              (B * (Real.exp (κ * (y - x)) * upperBarrier κ M x)) :=
            mul_le_mul_of_nonneg_left hHy (Real.exp_pos _).le
      _ = C * Real.exp (-(r - κ) * y) := by
        dsimp [C]
        rw [show Real.exp (-r * y) *
              (B * (Real.exp (κ * (y - x)) * upperBarrier κ M x))
              = B * upperBarrier κ M x *
                (Real.exp (-r * y) * Real.exp (κ * (y - x))) by ring,
            ← Real.exp_add]
        have harg : -r * y + κ * (y - x) = -κ * x + -(r - κ) * y := by
          ring
        rw [harg, Real.exp_add]
        ring
  have hstep2 :
      (∫ y in Ioi x, |gWeight r H y|) ≤
        ∫ y in Ioi x, C * Real.exp (-(r - κ) * y) :=
    setIntegral_mono_on ((hHint x).abs) hdom measurableSet_Ioi hptbd
  have hval :
      (∫ y in Ioi x, C * Real.exp (-(r - κ) * y))
        = C * (Real.exp (-(r - κ) * x) / (r - κ)) := by
    rw [integral_const_mul, integral_exp_mul_Ioi (a := -(r - κ)) (by linarith) x]
    have hne : r - κ ≠ 0 := ne_of_gt hrκ
    field_simp [hne]
  have htail_abs :
      |tailHi r H x| ≤ C * (Real.exp (-(r - κ) * x) / (r - κ)) :=
    le_trans hstep1 (le_trans hstep2 (le_of_eq hval))
  have hmul := mul_le_mul_of_nonneg_left htail_abs (Real.exp_pos (r * x)).le
  refine le_trans hmul (le_of_eq ?_)
  dsimp [C]
  have hne : r - κ ≠ 0 := ne_of_gt hrκ
  have hexp :
      Real.exp (r * x) * Real.exp (-κ * x) *
          Real.exp (-(r - κ) * x) = 1 := by
    rw [← Real.exp_add, ← Real.exp_add]
    have harg : r * x + -κ * x + -(r - κ) * x = 0 := by ring
    rw [harg, Real.exp_zero]
  field_simp [hne]
  rw [show Real.exp (-(x * κ)) = Real.exp (-κ * x) by ring_nf,
    show Real.exp (-(x * (r - κ))) = Real.exp (-(r - κ) * x) by ring_nf,
    show Real.exp (r * x) * B * upperBarrier κ M x *
        Real.exp (-κ * x) * Real.exp (-(r - κ) * x)
        = B * upperBarrier κ M x *
          (Real.exp (r * x) * Real.exp (-κ * x) *
            Real.exp (-(r - κ) * x)) by ring,
    hexp]
  ring

theorem tailLo_upperBarrier_abs_le_on
    {r κ M B : ℝ} {H : ℝ → ℝ}
    (hrκ : r + κ < 0) (hκ : 0 ≤ κ) (hM : 0 ≤ M) (hBnn : 0 ≤ B)
    (hHint : ∀ x, IntegrableOn (gWeight r H) (Iic x))
    {x : ℝ} (hB : ∀ y, |H y| ≤ B * upperBarrier κ M y) :
    Real.exp (r * x) * |tailLo r H x| ≤
      B * upperBarrier κ M x / (-(r + κ)) := by
  let C : ℝ := B * upperBarrier κ M x * Real.exp (κ * x)
  have hpos : 0 < -(r + κ) := by linarith
  have hdom : IntegrableOn (fun y : ℝ => C * Real.exp (-(r + κ) * y)) (Iic x) :=
    (integrableOn_exp_mul_Iic (a := -(r + κ)) hpos x).const_mul C
  have hstep1 : |tailLo r H x| ≤ ∫ y in Iic x, |gWeight r H y| := by
    rw [tailLo]
    simpa [Real.norm_eq_abs] using
      norm_integral_le_integral_norm
        (μ := (volume : Measure ℝ).restrict (Iic x)) (gWeight r H)
  have hptbd : ∀ y ∈ Iic x,
      |gWeight r H y| ≤ C * Real.exp (-(r + κ) * y) := by
    intro y hy
    rw [Set.mem_Iic] at hy
    have habs : |x - y| = x - y := abs_of_nonneg (sub_nonneg.mpr hy)
    have hshift :
        upperBarrier κ M y ≤
          Real.exp (κ * (x - y)) * upperBarrier κ M x := by
      simpa [habs] using
        (upperBarrier_shift_le_exp_abs_mul
          (κ := κ) (M := M) (x := x) (y := y) hκ hM)
    have hHy : |H y| ≤ B * (Real.exp (κ * (x - y)) * upperBarrier κ M x) := by
      exact (hB y).trans (mul_le_mul_of_nonneg_left hshift hBnn)
    rw [gWeight, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-r * y) * |H y|
          ≤ Real.exp (-r * y) *
              (B * (Real.exp (κ * (x - y)) * upperBarrier κ M x)) :=
            mul_le_mul_of_nonneg_left hHy (Real.exp_pos _).le
      _ = C * Real.exp (-(r + κ) * y) := by
        dsimp [C]
        rw [show Real.exp (-r * y) *
              (B * (Real.exp (κ * (x - y)) * upperBarrier κ M x))
              = B * upperBarrier κ M x *
                (Real.exp (-r * y) * Real.exp (κ * (x - y))) by ring,
            ← Real.exp_add]
        have harg : -r * y + κ * (x - y) = κ * x + -(r + κ) * y := by
          ring
        rw [harg, Real.exp_add]
        ring
  have hstep2 :
      (∫ y in Iic x, |gWeight r H y|) ≤
        ∫ y in Iic x, C * Real.exp (-(r + κ) * y) :=
    setIntegral_mono_on ((hHint x).abs) hdom measurableSet_Iic hptbd
  have hval :
      (∫ y in Iic x, C * Real.exp (-(r + κ) * y))
        = C * (Real.exp (-(r + κ) * x) / (-(r + κ))) := by
    rw [integral_const_mul, integral_exp_mul_Iic (a := -(r + κ)) hpos x]
  have htail_abs :
      |tailLo r H x| ≤ C * (Real.exp (-(r + κ) * x) / (-(r + κ))) :=
    le_trans hstep1 (le_trans hstep2 (le_of_eq hval))
  have hmul := mul_le_mul_of_nonneg_left htail_abs (Real.exp_pos (r * x)).le
  refine le_trans hmul (le_of_eq ?_)
  dsimp [C]
  have hne : -(r + κ) ≠ 0 := ne_of_gt hpos
  have hexp :
      Real.exp (r * x) * Real.exp (κ * x) *
          Real.exp (-(r + κ) * x) = 1 := by
    rw [← Real.exp_add, ← Real.exp_add]
    have harg : r * x + κ * x + -(r + κ) * x = 0 := by ring
    rw [harg, Real.exp_zero]
  field_simp [hne]
  rw [show Real.exp (x * κ) = Real.exp (κ * x) by ring_nf,
    show Real.exp (-(x * (r + κ))) = Real.exp (-(r + κ) * x) by ring_nf,
    show Real.exp (r * x) * B * upperBarrier κ M x *
        Real.exp (κ * x) * Real.exp (-(r + κ) * x)
        = B * upperBarrier κ M x *
          (Real.exp (r * x) * Real.exp (κ * x) *
            Real.exp (-(r + κ) * x)) by ring,
    hexp]
  ring

/-- Weighted Green mass bound for the explicit convolution.  The source is
measured in the same `upperBarrier` weight as the source box. -/
theorem greenConv_abs_le_upperBarrier_of_source_bound
    (hlam : 0 < lam) {κ M B : ℝ} {H : ℝ → ℝ}
    (hrpκ : κ < greenRootPlus c lam)
    (hrmκ : κ < -greenRootMinus c lam)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) (hBnn : 0 ≤ B)
    (hB : ∀ y, |H y| ≤ B * upperBarrier κ M y)
    (hHi : ∀ x, IntegrableOn (gWeight (greenRootPlus c lam) H) (Ioi x))
    (hLo : ∀ x, IntegrableOn (gWeight (greenRootMinus c lam) H) (Iic x))
    (x : ℝ) :
    |greenConv c lam H x| ≤
      (greenDelta c lam)⁻¹ *
        (B * upperBarrier κ M x / (greenRootPlus c lam - κ) +
          B * upperBarrier κ M x / (-(greenRootMinus c lam + κ))) := by
  have hδ : 0 < (greenDelta c lam)⁻¹ :=
    inv_pos.mpr (greenDelta_pos (c := c) hlam)
  have hrpκ' : 0 < greenRootPlus c lam - κ := by linarith
  have hrmκ' : greenRootMinus c lam + κ < 0 := by linarith
  have hHi_bd :
      Real.exp (greenRootPlus c lam * x) *
          |tailHi (greenRootPlus c lam) H x| ≤
        B * upperBarrier κ M x / (greenRootPlus c lam - κ) :=
    tailHi_upperBarrier_abs_le_on
      (r := greenRootPlus c lam) (κ := κ) (M := M) (B := B)
      hrpκ' hκ hM hBnn hHi hB
  have hLo_bd :
      Real.exp (greenRootMinus c lam * x) *
          |tailLo (greenRootMinus c lam) H x| ≤
        B * upperBarrier κ M x / (-(greenRootMinus c lam + κ)) :=
    tailLo_upperBarrier_abs_le_on
      (r := greenRootMinus c lam) (κ := κ) (M := M) (B := B)
      hrmκ' hκ hM hBnn hLo hB
  rw [greenConv, abs_mul, abs_of_pos hδ]
  have hsum :
      |Real.exp (greenRootPlus c lam * x) *
            tailHi (greenRootPlus c lam) H x
        + Real.exp (greenRootMinus c lam * x) *
            tailLo (greenRootMinus c lam) H x|
        ≤ B * upperBarrier κ M x / (greenRootPlus c lam - κ) +
          B * upperBarrier κ M x / (-(greenRootMinus c lam + κ)) := by
    have hA :
        |Real.exp (greenRootPlus c lam * x) *
            tailHi (greenRootPlus c lam) H x|
          =
        Real.exp (greenRootPlus c lam * x) *
            |tailHi (greenRootPlus c lam) H x| := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have hBtail :
        |Real.exp (greenRootMinus c lam * x) *
            tailLo (greenRootMinus c lam) H x|
          =
        Real.exp (greenRootMinus c lam * x) *
            |tailLo (greenRootMinus c lam) H x| := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      |Real.exp (greenRootPlus c lam * x) *
            tailHi (greenRootPlus c lam) H x
        + Real.exp (greenRootMinus c lam * x) *
            tailLo (greenRootMinus c lam) H x|
          ≤ |Real.exp (greenRootPlus c lam * x) *
              tailHi (greenRootPlus c lam) H x|
            + |Real.exp (greenRootMinus c lam * x) *
              tailLo (greenRootMinus c lam) H x| := abs_add_le _ _
      _ = Real.exp (greenRootPlus c lam * x) *
              |tailHi (greenRootPlus c lam) H x|
            + Real.exp (greenRootMinus c lam * x) *
              |tailLo (greenRootMinus c lam) H x| := by rw [hA, hBtail]
      _ ≤ B * upperBarrier κ M x / (greenRootPlus c lam - κ) +
          B * upperBarrier κ M x / (-(greenRootMinus c lam + κ)) :=
        add_le_add hHi_bd hLo_bd
  exact mul_le_mul_of_nonneg_left hsum hδ.le

/-- Weighted Green mass bound for the explicit derivative formula. -/
theorem greenConvDeriv_abs_le_upperBarrier_of_source_bound
    (hlam : 0 < lam) {κ M B : ℝ} {H : ℝ → ℝ}
    (hrpκ : κ < greenRootPlus c lam)
    (hrmκ : κ < -greenRootMinus c lam)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) (hBnn : 0 ≤ B)
    (hB : ∀ y, |H y| ≤ B * upperBarrier κ M y)
    (hHi : ∀ x, IntegrableOn (gWeight (greenRootPlus c lam) H) (Ioi x))
    (hLo : ∀ x, IntegrableOn (gWeight (greenRootMinus c lam) H) (Iic x))
    (x : ℝ) :
    |greenConvDeriv c lam H x| ≤
      (greenDelta c lam)⁻¹ *
        (greenRootPlus c lam *
            (B * upperBarrier κ M x / (greenRootPlus c lam - κ)) +
          (-greenRootMinus c lam) *
            (B * upperBarrier κ M x / (-(greenRootMinus c lam + κ)))) := by
  have hrp : 0 < greenRootPlus c lam := greenRootPlus_pos (c := c) hlam
  have hrm : greenRootMinus c lam < 0 := greenRootMinus_neg (c := c) hlam
  have hδ : 0 < (greenDelta c lam)⁻¹ :=
    inv_pos.mpr (greenDelta_pos (c := c) hlam)
  have hrpκ' : 0 < greenRootPlus c lam - κ := by linarith
  have hrmκ' : greenRootMinus c lam + κ < 0 := by linarith
  have hHi_bd :
      Real.exp (greenRootPlus c lam * x) *
          |tailHi (greenRootPlus c lam) H x| ≤
        B * upperBarrier κ M x / (greenRootPlus c lam - κ) :=
    tailHi_upperBarrier_abs_le_on
      (r := greenRootPlus c lam) (κ := κ) (M := M) (B := B)
      hrpκ' hκ hM hBnn hHi hB
  have hLo_bd :
      Real.exp (greenRootMinus c lam * x) *
          |tailLo (greenRootMinus c lam) H x| ≤
        B * upperBarrier κ M x / (-(greenRootMinus c lam + κ)) :=
    tailLo_upperBarrier_abs_le_on
      (r := greenRootMinus c lam) (κ := κ) (M := M) (B := B)
      hrmκ' hκ hM hBnn hLo hB
  have hHi_term :
      greenRootPlus c lam * Real.exp (greenRootPlus c lam * x) *
          |tailHi (greenRootPlus c lam) H x| ≤
        greenRootPlus c lam *
          (B * upperBarrier κ M x / (greenRootPlus c lam - κ)) := by
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left hHi_bd hrp.le
  have hLo_term :
      (-greenRootMinus c lam) * Real.exp (greenRootMinus c lam * x) *
          |tailLo (greenRootMinus c lam) H x| ≤
        (-greenRootMinus c lam) *
          (B * upperBarrier κ M x / (-(greenRootMinus c lam + κ))) := by
    simpa [mul_assoc] using
      mul_le_mul_of_nonneg_left hLo_bd (neg_nonneg.mpr hrm.le)
  rw [greenConvDeriv, abs_mul, abs_of_pos hδ]
  have hsum :
      |greenRootPlus c lam * Real.exp (greenRootPlus c lam * x) *
            tailHi (greenRootPlus c lam) H x
        + greenRootMinus c lam * Real.exp (greenRootMinus c lam * x) *
            tailLo (greenRootMinus c lam) H x|
        ≤ greenRootPlus c lam *
            (B * upperBarrier κ M x / (greenRootPlus c lam - κ)) +
          (-greenRootMinus c lam) *
            (B * upperBarrier κ M x / (-(greenRootMinus c lam + κ))) := by
    have hA :
        |greenRootPlus c lam * Real.exp (greenRootPlus c lam * x) *
            tailHi (greenRootPlus c lam) H x|
          =
        greenRootPlus c lam * Real.exp (greenRootPlus c lam * x) *
            |tailHi (greenRootPlus c lam) H x| := by
      rw [abs_mul, abs_mul, abs_of_pos hrp, abs_of_pos (Real.exp_pos _),
        mul_assoc]
    have hBtail :
        |greenRootMinus c lam * Real.exp (greenRootMinus c lam * x) *
            tailLo (greenRootMinus c lam) H x|
          =
        (-greenRootMinus c lam) * Real.exp (greenRootMinus c lam * x) *
            |tailLo (greenRootMinus c lam) H x| := by
      rw [abs_mul, abs_mul, abs_of_neg hrm, abs_of_pos (Real.exp_pos _),
        mul_assoc]
    calc
      |greenRootPlus c lam * Real.exp (greenRootPlus c lam * x) *
            tailHi (greenRootPlus c lam) H x
        + greenRootMinus c lam * Real.exp (greenRootMinus c lam * x) *
            tailLo (greenRootMinus c lam) H x|
          ≤ |greenRootPlus c lam * Real.exp (greenRootPlus c lam * x) *
              tailHi (greenRootPlus c lam) H x|
            + |greenRootMinus c lam * Real.exp (greenRootMinus c lam * x) *
              tailLo (greenRootMinus c lam) H x| := abs_add_le _ _
      _ = greenRootPlus c lam * Real.exp (greenRootPlus c lam * x) *
              |tailHi (greenRootPlus c lam) H x|
            + (-greenRootMinus c lam) * Real.exp (greenRootMinus c lam * x) *
              |tailLo (greenRootMinus c lam) H x| := by rw [hA, hBtail]
      _ ≤ greenRootPlus c lam *
            (B * upperBarrier κ M x / (greenRootPlus c lam - κ)) +
          (-greenRootMinus c lam) *
            (B * upperBarrier κ M x / (-(greenRootMinus c lam + κ))) :=
        add_le_add hHi_term hLo_term
  exact mul_le_mul_of_nonneg_left hsum hδ.le

/-- Weighted derivative bound for the genuine derivative of `greenConv`. -/
theorem deriv_greenConv_abs_le_upperBarrier_of_source_bound
    (hlam : 0 < lam) {κ M B : ℝ} {H : ℝ → ℝ}
    (hrpκ : κ < greenRootPlus c lam)
    (hrmκ : κ < -greenRootMinus c lam)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) (hBnn : 0 ≤ B)
    (hHcont : Continuous H)
    (hB : ∀ y, |H y| ≤ B * upperBarrier κ M y)
    (hHi : ∀ x, IntegrableOn (gWeight (greenRootPlus c lam) H) (Ioi x))
    (hLo : ∀ x, IntegrableOn (gWeight (greenRootMinus c lam) H) (Iic x))
    (x : ℝ) :
    |deriv (greenConv c lam H) x| ≤
      (greenDelta c lam)⁻¹ *
        (greenRootPlus c lam *
            (B * upperBarrier κ M x / (greenRootPlus c lam - κ)) +
          (-greenRootMinus c lam) *
            (B * upperBarrier κ M x / (-(greenRootMinus c lam + κ)))) := by
  have hderiv :
      deriv (greenConv c lam H) x = greenConvDeriv c lam H x :=
    (greenConv_hasDerivAt (c := c) (lam := lam) hHcont hHi hLo x).deriv
  rw [hderiv]
  exact greenConvDeriv_abs_le_upperBarrier_of_source_bound
    (c := c) (lam := lam) hlam hrpκ hrmκ hκ hM hBnn hB hHi hLo x

/-- Weighted `L¹` mass of the Green kernel against `exp(κ|·|)`. -/
def greenWeightedMass0 (c lam κ : ℝ) : ℝ :=
  (greenDelta c lam)⁻¹ *
    ((greenRootPlus c lam - κ)⁻¹ +
      (-(greenRootMinus c lam + κ))⁻¹)

/-- Weighted `L¹` mass of the Green-kernel derivative against `exp(κ|·|)`. -/
def greenWeightedMass1 (c lam κ : ℝ) : ℝ :=
  (greenDelta c lam)⁻¹ *
    (greenRootPlus c lam * (greenRootPlus c lam - κ)⁻¹ +
      (-greenRootMinus c lam) * (-(greenRootMinus c lam + κ))⁻¹)

theorem greenWeightedMass0_nonneg
    (hlam : 0 < lam) {κ : ℝ}
    (hrpκ : κ < greenRootPlus c lam)
    (hrmκ : κ < -greenRootMinus c lam) :
    0 ≤ greenWeightedMass0 c lam κ := by
  unfold greenWeightedMass0
  have hδ : 0 ≤ (greenDelta c lam)⁻¹ :=
    (inv_pos.mpr (greenDelta_pos (c := c) hlam)).le
  have hp : 0 < greenRootPlus c lam - κ := by linarith
  have hm : 0 < -(greenRootMinus c lam + κ) := by linarith
  exact mul_nonneg hδ (add_nonneg (inv_nonneg.mpr hp.le) (inv_nonneg.mpr hm.le))

theorem greenWeightedMass1_nonneg
    (hlam : 0 < lam) {κ : ℝ}
    (hrpκ : κ < greenRootPlus c lam)
    (hrmκ : κ < -greenRootMinus c lam) :
    0 ≤ greenWeightedMass1 c lam κ := by
  unfold greenWeightedMass1
  have hδ : 0 ≤ (greenDelta c lam)⁻¹ :=
    (inv_pos.mpr (greenDelta_pos (c := c) hlam)).le
  have hrp : 0 ≤ greenRootPlus c lam := (greenRootPlus_pos (c := c) hlam).le
  have hrm : 0 ≤ -greenRootMinus c lam :=
    neg_nonneg.mpr (greenRootMinus_neg (c := c) hlam).le
  have hp : 0 < greenRootPlus c lam - κ := by linarith
  have hm : 0 < -(greenRootMinus c lam + κ) := by linarith
  have hs :
      0 ≤ greenRootPlus c lam * (greenRootPlus c lam - κ)⁻¹ +
        (-greenRootMinus c lam) * (-(greenRootMinus c lam + κ))⁻¹ :=
    add_nonneg
      (mul_nonneg hrp (inv_nonneg.mpr hp.le))
      (mul_nonneg hrm (inv_nonneg.mpr hm.le))
  exact mul_nonneg hδ hs

theorem greenConv_abs_le_upperBarrier_mass
    (hlam : 0 < lam) {κ M B : ℝ} {H : ℝ → ℝ}
    (hrpκ : κ < greenRootPlus c lam)
    (hrmκ : κ < -greenRootMinus c lam)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) (hBnn : 0 ≤ B)
    (hB : ∀ y, |H y| ≤ B * upperBarrier κ M y)
    (hHi : ∀ x, IntegrableOn (gWeight (greenRootPlus c lam) H) (Ioi x))
    (hLo : ∀ x, IntegrableOn (gWeight (greenRootMinus c lam) H) (Iic x))
    (x : ℝ) :
    |greenConv c lam H x| ≤
      greenWeightedMass0 c lam κ * (B * upperBarrier κ M x) := by
  have hraw := greenConv_abs_le_upperBarrier_of_source_bound
    (c := c) (lam := lam) hlam hrpκ hrmκ hκ hM hBnn hB hHi hLo x
  refine hraw.trans (le_of_eq ?_)
  unfold greenWeightedMass0
  ring

theorem deriv_greenConv_abs_le_upperBarrier_mass
    (hlam : 0 < lam) {κ M B : ℝ} {H : ℝ → ℝ}
    (hrpκ : κ < greenRootPlus c lam)
    (hrmκ : κ < -greenRootMinus c lam)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) (hBnn : 0 ≤ B)
    (hHcont : Continuous H)
    (hB : ∀ y, |H y| ≤ B * upperBarrier κ M y)
    (hHi : ∀ x, IntegrableOn (gWeight (greenRootPlus c lam) H) (Ioi x))
    (hLo : ∀ x, IntegrableOn (gWeight (greenRootMinus c lam) H) (Iic x))
    (x : ℝ) :
    |deriv (greenConv c lam H) x| ≤
      greenWeightedMass1 c lam κ * (B * upperBarrier κ M x) := by
  have hraw := deriv_greenConv_abs_le_upperBarrier_of_source_bound
    (c := c) (lam := lam) hlam hrpκ hrmκ hκ hM hBnn hHcont hB hHi hLo x
  refine hraw.trans (le_of_eq ?_)
  unfold greenWeightedMass1
  ring

/-- Source-box specialization of the weighted Green profile bound. -/
theorem PaperWeightedHolderSourceBox.greenConv_abs_le
    {β Hbox : ℝ} {ω : ℝ → ℝ} (hlam : 0 < lam) {κ M B : ℝ} {R : ℝ → ℝ}
    (hrpκ : κ < greenRootPlus c lam)
    (hrmκ : κ < -greenRootMinus c lam)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) (hBnn : 0 ≤ B)
    (hR : PaperWeightedHolderSourceBox κ M β B Hbox ω R)
    (x : ℝ) :
    |greenConv c lam R x| ≤
      greenWeightedMass0 c lam κ * (B * upperBarrier κ M x) := by
  have hR_const : ∀ y, |R y| ≤ B * M := by
    intro y
    calc
      |R y| ≤ B * upperBarrier κ M y := hR.bound y
      _ ≤ B * M :=
        mul_le_mul_of_nonneg_left (upperBarrier_le_M κ M y) hBnn
  have hHi : ∀ t,
      IntegrableOn (gWeight (greenRootPlus c lam) R) (Ioi t) :=
    fun t => gWeight_integrableOn_Ioi_of_bounded
      (greenRootPlus_pos (c := c) hlam) hR.cont hR_const t
  have hLo : ∀ t,
      IntegrableOn (gWeight (greenRootMinus c lam) R) (Iic t) :=
    fun t => gWeight_integrableOn_Iic_of_bounded
      (greenRootMinus_neg (c := c) hlam) hR.cont hR_const t
  exact greenConv_abs_le_upperBarrier_mass
    (c := c) (lam := lam) hlam hrpκ hrmκ hκ hM hBnn hR.bound hHi hLo x

/-- Source-box specialization of the weighted Green derivative bound. -/
theorem PaperWeightedHolderSourceBox.deriv_greenConv_abs_le
    {β Hbox : ℝ} {ω : ℝ → ℝ} (hlam : 0 < lam) {κ M B : ℝ} {R : ℝ → ℝ}
    (hrpκ : κ < greenRootPlus c lam)
    (hrmκ : κ < -greenRootMinus c lam)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) (hBnn : 0 ≤ B)
    (hR : PaperWeightedHolderSourceBox κ M β B Hbox ω R)
    (x : ℝ) :
    |deriv (greenConv c lam R) x| ≤
      greenWeightedMass1 c lam κ * (B * upperBarrier κ M x) := by
  have hR_const : ∀ y, |R y| ≤ B * M := by
    intro y
    calc
      |R y| ≤ B * upperBarrier κ M y := hR.bound y
      _ ≤ B * M :=
        mul_le_mul_of_nonneg_left (upperBarrier_le_M κ M y) hBnn
  have hHi : ∀ t,
      IntegrableOn (gWeight (greenRootPlus c lam) R) (Ioi t) :=
    fun t => gWeight_integrableOn_Ioi_of_bounded
      (greenRootPlus_pos (c := c) hlam) hR.cont hR_const t
  have hLo : ∀ t,
      IntegrableOn (gWeight (greenRootMinus c lam) R) (Iic t) :=
    fun t => gWeight_integrableOn_Iic_of_bounded
      (greenRootMinus_neg (c := c) hlam) hR.cont hR_const t
  exact deriv_greenConv_abs_le_upperBarrier_mass
    (c := c) (lam := lam) hlam hrpκ hrmκ hκ hM hBnn hR.cont hR.bound hHi hLo x

/-- Source-box Green profile as a bounded locally-Lipschitz factor. -/
def PaperWeightedHolderSourceBox.greenConv_localLipQuant
    {β Hbox : ℝ} {ω : ℝ → ℝ} (hlam : 0 < lam) {κ M B : ℝ} {R : ℝ → ℝ}
    (hrpκ : κ < greenRootPlus c lam)
    (hrmκ : κ < -greenRootMinus c lam)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) (hBnn : 0 ≤ B)
    (hR : PaperWeightedHolderSourceBox κ M β B Hbox ω R) :
    LocalLipQuant (fun x => greenConv c lam R x) := by
  let Cw : ℝ := greenWeightedMass0 c lam κ * (B * M)
  let Lw : ℝ := greenWeightedMass1 c lam κ * (B * M)
  have hmass0 : 0 ≤ greenWeightedMass0 c lam κ :=
    greenWeightedMass0_nonneg (c := c) (lam := lam) hlam hrpκ hrmκ
  have hmass1 : 0 ≤ greenWeightedMass1 c lam κ :=
    greenWeightedMass1_nonneg (c := c) (lam := lam) hlam hrpκ hrmκ
  have hBM : 0 ≤ B * M := mul_nonneg hBnn hM
  have hCw : 0 ≤ Cw := mul_nonneg hmass0 hBM
  have hLw : 0 ≤ Lw := mul_nonneg hmass1 hBM
  have hbound : ∀ x, |greenConv c lam R x| ≤ Cw := by
    intro x
    calc
      |greenConv c lam R x|
          ≤ greenWeightedMass0 c lam κ * (B * upperBarrier κ M x) :=
        hR.greenConv_abs_le (c := c) (lam := lam) hlam hrpκ hrmκ
          hκ hM hBnn x
      _ ≤ greenWeightedMass0 c lam κ * (B * M) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (upperBarrier_le_M κ M x) hBnn) hmass0
  have hHi := hR.gWeight_Ioi (c := c) (lam := lam) hlam hBnn
  have hLo := hR.gWeight_Iic (c := c) (lam := lam) hlam hBnn
  have hdiff : Differentiable ℝ (fun x => greenConv c lam R x) := by
    intro x
    exact (greenConv_hasDerivAt (c := c) (lam := lam) hR.cont hHi hLo x).differentiableAt
  have hderiv_bound : ∀ x, |deriv (fun x => greenConv c lam R x) x| ≤ Lw := by
    intro x
    calc
      |deriv (fun x => greenConv c lam R x) x|
          ≤ greenWeightedMass1 c lam κ * (B * upperBarrier κ M x) :=
        hR.deriv_greenConv_abs_le (c := c) (lam := lam) hlam hrpκ hrmκ
          hκ hM hBnn x
      _ ≤ greenWeightedMass1 c lam κ * (B * M) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (upperBarrier_le_M κ M x) hBnn) hmass1
  exact LocalLipQuant.of_lipschitz hCw hLw hbound
    (abs_sub_le_of_deriv_abs_le_core hdiff hderiv_bound)

/-- Source-box Green profile as a bounded β-Hölder factor. -/
def PaperWeightedHolderSourceBox.greenConv_holderQuant
    {β Hbox : ℝ} {ω : ℝ → ℝ} (hlam : 0 < lam) {κ M B : ℝ} {R : ℝ → ℝ}
    (hrpκ : κ < greenRootPlus c lam)
    (hrmκ : κ < -greenRootMinus c lam)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) (hBnn : 0 ≤ B)
    (hβpos : 0 < β) (hβle : β ≤ 1)
    (hR : PaperWeightedHolderSourceBox κ M β B Hbox ω R) :
    HolderQuant β (fun x => greenConv c lam R x) := by
  let Cw : ℝ := greenWeightedMass0 c lam κ * (B * M)
  let Lw : ℝ := greenWeightedMass1 c lam κ * (B * M)
  have hmass0 : 0 ≤ greenWeightedMass0 c lam κ :=
    greenWeightedMass0_nonneg (c := c) (lam := lam) hlam hrpκ hrmκ
  have hmass1 : 0 ≤ greenWeightedMass1 c lam κ :=
    greenWeightedMass1_nonneg (c := c) (lam := lam) hlam hrpκ hrmκ
  have hBM : 0 ≤ B * M := mul_nonneg hBnn hM
  have hCw : 0 ≤ Cw := mul_nonneg hmass0 hBM
  have hLw : 0 ≤ Lw := mul_nonneg hmass1 hBM
  have hbound : ∀ x, |greenConv c lam R x| ≤ Cw := by
    intro x
    calc
      |greenConv c lam R x|
          ≤ greenWeightedMass0 c lam κ * (B * upperBarrier κ M x) :=
        hR.greenConv_abs_le (c := c) (lam := lam) hlam hrpκ hrmκ
          hκ hM hBnn x
      _ ≤ greenWeightedMass0 c lam κ * (B * M) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (upperBarrier_le_M κ M x) hBnn) hmass0
  have hHi := hR.gWeight_Ioi (c := c) (lam := lam) hlam hBnn
  have hLo := hR.gWeight_Iic (c := c) (lam := lam) hlam hBnn
  have hdiff : Differentiable ℝ (fun x => greenConv c lam R x) := by
    intro x
    exact (greenConv_hasDerivAt (c := c) (lam := lam) hR.cont hHi hLo x).differentiableAt
  have hderiv_bound : ∀ x, |deriv (fun x => greenConv c lam R x) x| ≤ Lw := by
    intro x
    calc
      |deriv (fun x => greenConv c lam R x) x|
          ≤ greenWeightedMass1 c lam κ * (B * upperBarrier κ M x) :=
        hR.deriv_greenConv_abs_le (c := c) (lam := lam) hlam hrpκ hrmκ
          hκ hM hBnn x
      _ ≤ greenWeightedMass1 c lam κ * (B * M) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (upperBarrier_le_M κ M x) hBnn) hmass1
  have hlip : ∀ x y,
      |greenConv c lam R x - greenConv c lam R y| ≤ Lw * |x - y| :=
    abs_sub_le_of_deriv_abs_le_core hdiff hderiv_bound
  exact HolderQuant.of_lipschitz hβpos hβle hCw hLw hbound hlip

/-- Source-box Green derivative as a bounded β-Hölder factor. -/
def PaperWeightedHolderSourceBox.greenConvDeriv_holderQuant
    {β Hbox : ℝ} {ω : ℝ → ℝ} (hlam : 0 < lam) {κ M B : ℝ} {R : ℝ → ℝ}
    (hrpκ : κ < greenRootPlus c lam)
    (hrmκ : κ < -greenRootMinus c lam)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) (hBnn : 0 ≤ B)
    (hβpos : 0 < β) (hβle : β ≤ 1)
    (hR : PaperWeightedHolderSourceBox κ M β B Hbox ω R) :
    HolderQuant β (fun x => greenConvDeriv c lam R x) := by
  let Cw : ℝ := greenWeightedMass0 c lam κ * (B * M)
  let Cwd : ℝ := greenWeightedMass1 c lam κ * (B * M)
  let Lwd : ℝ := B * M + |c| * Cwd + lam * Cw
  have hmass0 : 0 ≤ greenWeightedMass0 c lam κ :=
    greenWeightedMass0_nonneg (c := c) (lam := lam) hlam hrpκ hrmκ
  have hmass1 : 0 ≤ greenWeightedMass1 c lam κ :=
    greenWeightedMass1_nonneg (c := c) (lam := lam) hlam hrpκ hrmκ
  have hBM : 0 ≤ B * M := mul_nonneg hBnn hM
  have hCw : 0 ≤ Cw := mul_nonneg hmass0 hBM
  have hCwd : 0 ≤ Cwd := mul_nonneg hmass1 hBM
  have hLwd : 0 ≤ Lwd := by
    dsimp [Lwd]
    positivity
  have hHi := hR.gWeight_Ioi (c := c) (lam := lam) hlam hBnn
  have hLo := hR.gWeight_Iic (c := c) (lam := lam) hlam hBnn
  have hWbound : ∀ x, |greenConv c lam R x| ≤ Cw := by
    intro x
    calc
      |greenConv c lam R x|
          ≤ greenWeightedMass0 c lam κ * (B * upperBarrier κ M x) :=
        hR.greenConv_abs_le (c := c) (lam := lam) hlam hrpκ hrmκ
          hκ hM hBnn x
      _ ≤ greenWeightedMass0 c lam κ * (B * M) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (upperBarrier_le_M κ M x) hBnn) hmass0
  have hDbound : ∀ x, |greenConvDeriv c lam R x| ≤ Cwd := by
    intro x
    calc
      |greenConvDeriv c lam R x|
          ≤ greenWeightedMass1 c lam κ * (B * upperBarrier κ M x) := by
        have hraw := greenConvDeriv_abs_le_upperBarrier_of_source_bound
          (c := c) (lam := lam) hlam hrpκ hrmκ hκ hM hBnn hR.bound hHi hLo x
        refine hraw.trans (le_of_eq ?_)
        unfold greenWeightedMass1
        ring
      _ ≤ greenWeightedMass1 c lam κ * (B * M) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (upperBarrier_le_M κ M x) hBnn) hmass1
  have hdiff : Differentiable ℝ (fun x => greenConvDeriv c lam R x) := by
    intro x
    exact (greenConvDeriv_hasDerivAt (c := c) (lam := lam) hR.cont hHi hLo x).differentiableAt
  have hderiv_bound : ∀ x, |deriv (fun x => greenConvDeriv c lam R x) x| ≤ Lwd := by
    intro x
    have hderiv_eq :
        deriv (fun x => greenConvDeriv c lam R x) x = greenConvDeriv2 c lam R x :=
      (greenConvDeriv_hasDerivAt (c := c) (lam := lam) hR.cont hHi hLo x).deriv
    have hsolve := greenConv_solves (c := c) (lam := lam) hlam (H := R) x
    have hG2 : greenConvDeriv2 c lam R x =
        -R x - c * greenConvDeriv c lam R x + lam * greenConv c lam R x := by
      linarith
    rw [hderiv_eq, hG2]
    calc
      |-R x - c * greenConvDeriv c lam R x + lam * greenConv c lam R x|
          ≤ |-R x| + |c * greenConvDeriv c lam R x| +
              |lam * greenConv c lam R x| := by
            calc
              |-R x - c * greenConvDeriv c lam R x + lam * greenConv c lam R x|
                  ≤ |-R x - c * greenConvDeriv c lam R x| +
                      |lam * greenConv c lam R x| :=
                    abs_add_le _ _
              _ ≤ (|-R x| + |c * greenConvDeriv c lam R x|) +
                      |lam * greenConv c lam R x| := by
                    exact add_le_add (abs_sub (-R x) (c * greenConvDeriv c lam R x)) le_rfl
              _ = |-R x| + |c * greenConvDeriv c lam R x| +
                      |lam * greenConv c lam R x| := by ring
      _ = |R x| + |c| * |greenConvDeriv c lam R x| +
            lam * |greenConv c lam R x| := by
            rw [abs_neg, abs_mul, abs_mul, abs_of_pos hlam]
      _ ≤ B * M + |c| * Cwd + lam * Cw := by
            exact add_le_add
              (add_le_add (hR.abs_le_const (B := B) hBnn x)
                (mul_le_mul_of_nonneg_left (hDbound x) (abs_nonneg c)))
              (mul_le_mul_of_nonneg_left (hWbound x) hlam.le)
  have hlip : ∀ x y,
      |greenConvDeriv c lam R x - greenConvDeriv c lam R y| ≤ Lwd * |x - y| :=
    abs_sub_le_of_deriv_abs_le_core hdiff hderiv_bound
  exact HolderQuant.of_lipschitz hβpos hβle hCwd hLwd hDbound hlip

theorem setIntegral_Ioi_add_right (x : ℝ) (f : ℝ → ℝ) :
    (∫ y in Ioi x, f y) = ∫ s in Ioi (0:ℝ), f (s + x) := by
  let T : ℝ → ℝ := fun s => s + x
  have hpre : T ⁻¹' Ioi x = Ioi (0:ℝ) := by
    ext s
    simp [T]
  have hmap : Measure.map T ((volume : Measure ℝ).restrict (Ioi (0:ℝ))) =
      (volume : Measure ℝ).restrict (Ioi x) := by
    have h := Measure.restrict_map (μ := (volume : Measure ℝ))
      (f := T) (measurable_id.add_const x) (s := Ioi x) measurableSet_Ioi
    rw [map_add_right_eq_self (volume : Measure ℝ) x] at h
    rw [hpre] at h
    exact h.symm
  rw [← hmap]
  exact (Homeomorph.addRight x).isClosedEmbedding.measurableEmbedding.integral_map f

theorem setIntegral_Iic_sub_left (x : ℝ) (f : ℝ → ℝ) :
    (∫ y in Iic x, f y) = ∫ s in Ici (0:ℝ), f (x - s) := by
  let T : ℝ → ℝ := fun s => x - s
  have hpre : T ⁻¹' Iic x = Ici (0:ℝ) := by
    ext s
    simp [T, sub_eq_add_neg]
  have hmap : Measure.map T ((volume : Measure ℝ).restrict (Ici (0:ℝ))) =
      (volume : Measure ℝ).restrict (Iic x) := by
    have hmeas : Measurable T := by fun_prop
    have h := Measure.restrict_map (μ := (volume : Measure ℝ))
      (f := T) hmeas (s := Iic x) measurableSet_Iic
    have hTmap : Measure.map T (volume : Measure ℝ) = volume := by
      dsimp [T]
      rw [show (fun s : ℝ => x - s) = (fun t => t + x) ∘ (fun s => -s) by
        funext s
        simp
        ring]
      rw [← Measure.map_map (μ := (volume : Measure ℝ))
        (g := fun t : ℝ => t + x) (f := fun s : ℝ => -s)
        (measurable_id.add_const x) measurable_neg]
      rw [Measure.map_neg_eq_self, map_add_right_eq_self]
    rw [hTmap] at h
    rw [hpre] at h
    exact h.symm
  rw [← hmap]
  have hme : MeasurableEmbedding T := by
    dsimp [T]
    convert
      ((Homeomorph.neg ℝ).trans
        (Homeomorph.addRight x)).isClosedEmbedding.measurableEmbedding using 1
    ext s
    simp
    ring
  exact hme.integral_map f

theorem tailHi_weighted_tendsto_atTop
    {r C L : ℝ} {H : ℝ → ℝ}
    (hr : 0 < r) (hHcont : Continuous H) (hB : ∀ y, |H y| ≤ C)
    (hlim : Tendsto H atTop (𝓝 L)) :
    Tendsto (fun x => r * Real.exp (r * x) * tailHi r H x) atTop (𝓝 L) := by
  have hCnonneg : 0 ≤ C := le_trans (abs_nonneg _) (hB 0)
  have hDCT :
      Tendsto (fun x : ℝ =>
          ∫ s in Ioi (0:ℝ), r * Real.exp (-r * s) * H (s + x)) atTop
        (𝓝 (∫ s in Ioi (0:ℝ), r * Real.exp (-r * s) * L)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (μ := (volume : Measure ℝ).restrict (Ioi (0:ℝ)))
      (bound := fun s : ℝ => |r| * C * Real.exp (-r * s)) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun x =>
        (((continuous_const.mul
          (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul
          (hHcont.comp (continuous_id.add continuous_const))).aestronglyMeasurable)
    · refine Eventually.of_forall fun x => Eventually.of_forall fun s => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc |r| * Real.exp (-r * s) * |H (s + x)|
          ≤ |r| * Real.exp (-r * s) * C := by
            exact mul_le_mul_of_nonneg_left (hB (s + x))
              (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
        _ = |r| * C * Real.exp (-r * s) := by ring
    · exact ((integrableOn_exp_mul_Ioi (a := -r) (by linarith) 0).const_mul (|r| * C))
    · refine Eventually.of_forall fun s => ?_
      have hshift : Tendsto (fun x : ℝ => s + x) atTop atTop := by
        simpa [add_comm] using tendsto_atTop_add_const_right atTop s tendsto_id
      exact (hlim.comp hshift).const_mul (r * Real.exp (-r * s))
  have hlim_eval :
      (∫ s in Ioi (0:ℝ), r * Real.exp (-r * s) * L) = L := by
    rw [show (fun s : ℝ => r * Real.exp (-r * s) * L) =
        fun s => (r * L) * Real.exp (-r * s) by
      funext s
      ring]
    rw [integral_const_mul, integral_exp_mul_Ioi (a := -r) (by linarith) 0]
    have hrne : r ≠ 0 := ne_of_gt hr
    field_simp [hrne]
    simp
  have heq : (fun x => r * Real.exp (r * x) * tailHi r H x) =
      fun x => ∫ s in Ioi (0:ℝ), r * Real.exp (-r * s) * H (s + x) := by
    funext x
    unfold tailHi gWeight
    rw [setIntegral_Ioi_add_right x (fun y => Real.exp (-r * y) * H y)]
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards with s
    have hexp : Real.exp (r * x) * Real.exp (-r * (s + x)) =
        Real.exp (-r * s) := by
      rw [← Real.exp_add]
      have harg : r * x + -r * (s + x) = -r * s := by ring
      rw [harg]
    calc
      r * Real.exp (r * x) * (Real.exp (-r * (s + x)) * H (s + x))
          = r * (Real.exp (r * x) * Real.exp (-r * (s + x))) * H (s + x) := by
            ring
      _ = r * Real.exp (-r * s) * H (s + x) := by
            rw [hexp]
  rw [heq]
  rw [hlim_eval] at hDCT
  exact hDCT

theorem tailHi_weighted_tendsto_atBot
    {r C L : ℝ} {H : ℝ → ℝ}
    (hr : 0 < r) (hHcont : Continuous H) (hB : ∀ y, |H y| ≤ C)
    (hlim : Tendsto H atBot (𝓝 L)) :
    Tendsto (fun x => r * Real.exp (r * x) * tailHi r H x) atBot (𝓝 L) := by
  have hCnonneg : 0 ≤ C := le_trans (abs_nonneg _) (hB 0)
  have hDCT :
      Tendsto (fun x : ℝ =>
          ∫ s in Ioi (0:ℝ), r * Real.exp (-r * s) * H (s + x)) atBot
        (𝓝 (∫ s in Ioi (0:ℝ), r * Real.exp (-r * s) * L)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (μ := (volume : Measure ℝ).restrict (Ioi (0:ℝ)))
      (bound := fun s : ℝ => |r| * C * Real.exp (-r * s)) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun x =>
        (((continuous_const.mul
          (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul
          (hHcont.comp (continuous_id.add continuous_const))).aestronglyMeasurable)
    · refine Eventually.of_forall fun x => Eventually.of_forall fun s => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc |r| * Real.exp (-r * s) * |H (s + x)|
          ≤ |r| * Real.exp (-r * s) * C := by
            exact mul_le_mul_of_nonneg_left (hB (s + x))
              (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
        _ = |r| * C * Real.exp (-r * s) := by ring
    · exact ((integrableOn_exp_mul_Ioi (a := -r) (by linarith) 0).const_mul (|r| * C))
    · refine Eventually.of_forall fun s => ?_
      have hshift : Tendsto (fun x : ℝ => s + x) atBot atBot := by
        simpa [add_comm] using tendsto_atBot_add_const_right atBot s tendsto_id
      exact (hlim.comp hshift).const_mul (r * Real.exp (-r * s))
  have hlim_eval :
      (∫ s in Ioi (0:ℝ), r * Real.exp (-r * s) * L) = L := by
    rw [show (fun s : ℝ => r * Real.exp (-r * s) * L) =
        fun s => (r * L) * Real.exp (-r * s) by
      funext s
      ring]
    rw [integral_const_mul, integral_exp_mul_Ioi (a := -r) (by linarith) 0]
    have hrne : r ≠ 0 := ne_of_gt hr
    field_simp [hrne]
    simp
  have heq : (fun x => r * Real.exp (r * x) * tailHi r H x) =
      fun x => ∫ s in Ioi (0:ℝ), r * Real.exp (-r * s) * H (s + x) := by
    funext x
    unfold tailHi gWeight
    rw [setIntegral_Ioi_add_right x (fun y => Real.exp (-r * y) * H y)]
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards with s
    have hexp : Real.exp (r * x) * Real.exp (-r * (s + x)) =
        Real.exp (-r * s) := by
      rw [← Real.exp_add]
      have harg : r * x + -r * (s + x) = -r * s := by ring
      rw [harg]
    calc
      r * Real.exp (r * x) * (Real.exp (-r * (s + x)) * H (s + x))
          = r * (Real.exp (r * x) * Real.exp (-r * (s + x))) * H (s + x) := by
            ring
      _ = r * Real.exp (-r * s) * H (s + x) := by
            rw [hexp]
  rw [heq]
  rw [hlim_eval] at hDCT
  exact hDCT

theorem tailLo_weighted_tendsto_atTop
    {r C L : ℝ} {H : ℝ → ℝ}
    (hr : r < 0) (hHcont : Continuous H) (hB : ∀ y, |H y| ≤ C)
    (hlim : Tendsto H atTop (𝓝 L)) :
    Tendsto (fun x => r * Real.exp (r * x) * tailLo r H x) atTop (𝓝 (-L)) := by
  have hCnonneg : 0 ≤ C := le_trans (abs_nonneg _) (hB 0)
  have hDCT :
      Tendsto (fun x : ℝ =>
          ∫ s in Ici (0:ℝ), r * Real.exp (r * s) * H (x - s)) atTop
        (𝓝 (∫ s in Ici (0:ℝ), r * Real.exp (r * s) * L)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (μ := (volume : Measure ℝ).restrict (Ici (0:ℝ)))
      (bound := fun s : ℝ => |r| * C * Real.exp (r * s)) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun x =>
        (((continuous_const.mul
          (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul
          (hHcont.comp (continuous_const.sub continuous_id))).aestronglyMeasurable)
    · refine Eventually.of_forall fun x => Eventually.of_forall fun s => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc |r| * Real.exp (r * s) * |H (x - s)|
          ≤ |r| * Real.exp (r * s) * C := by
            exact mul_le_mul_of_nonneg_left (hB (x - s))
              (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
        _ = |r| * C * Real.exp (r * s) := by ring
    · exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi
        ((integrableOn_exp_mul_Ioi (a := r) hr 0).const_mul (|r| * C))
    · refine Eventually.of_forall fun s => ?_
      have hshift : Tendsto (fun x : ℝ => x - s) atTop atTop := by
        simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-s) tendsto_id
      exact (hlim.comp hshift).const_mul (r * Real.exp (r * s))
  have hlim_eval :
      (∫ s in Ici (0:ℝ), r * Real.exp (r * s) * L) = -L := by
    have hIoi :
        (∫ s in Ioi (0:ℝ), r * Real.exp (r * s) * L) = -L := by
      rw [show (fun s : ℝ => r * Real.exp (r * s) * L) =
          fun s => (r * L) * Real.exp (r * s) by
        funext s
        ring]
      rw [integral_const_mul, integral_exp_mul_Ioi (a := r) hr 0]
      have hrne : r ≠ 0 := ne_of_lt hr
      field_simp [hrne]
      simp
    rw [← hIoi]
    exact setIntegral_congr_set Ioi_ae_eq_Ici.symm
  have heq : (fun x => r * Real.exp (r * x) * tailLo r H x) =
      fun x => ∫ s in Ici (0:ℝ), r * Real.exp (r * s) * H (x - s) := by
    funext x
    unfold tailLo gWeight
    rw [setIntegral_Iic_sub_left x (fun y => Real.exp (-r * y) * H y)]
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards with s
    have hexp : Real.exp (r * x) * Real.exp (-r * (x - s)) =
        Real.exp (r * s) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [show r * Real.exp (r * x) * (Real.exp (-r * (x - s)) * H (x - s))
        = r * (Real.exp (r * x) * Real.exp (-r * (x - s))) * H (x - s) by ring,
      hexp]
  rw [heq]
  simpa [hlim_eval] using hDCT

theorem tailLo_weighted_tendsto_atBot
    {r C L : ℝ} {H : ℝ → ℝ}
    (hr : r < 0) (hHcont : Continuous H) (hB : ∀ y, |H y| ≤ C)
    (hlim : Tendsto H atBot (𝓝 L)) :
    Tendsto (fun x => r * Real.exp (r * x) * tailLo r H x) atBot (𝓝 (-L)) := by
  have hCnonneg : 0 ≤ C := le_trans (abs_nonneg _) (hB 0)
  have hDCT :
      Tendsto (fun x : ℝ =>
          ∫ s in Ici (0:ℝ), r * Real.exp (r * s) * H (x - s)) atBot
        (𝓝 (∫ s in Ici (0:ℝ), r * Real.exp (r * s) * L)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (μ := (volume : Measure ℝ).restrict (Ici (0:ℝ)))
      (bound := fun s : ℝ => |r| * C * Real.exp (r * s)) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun x =>
        (((continuous_const.mul
          (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul
          (hHcont.comp (continuous_const.sub continuous_id))).aestronglyMeasurable)
    · refine Eventually.of_forall fun x => Eventually.of_forall fun s => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc |r| * Real.exp (r * s) * |H (x - s)|
          ≤ |r| * Real.exp (r * s) * C := by
            exact mul_le_mul_of_nonneg_left (hB (x - s))
              (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
        _ = |r| * C * Real.exp (r * s) := by ring
    · exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi
        ((integrableOn_exp_mul_Ioi (a := r) hr 0).const_mul (|r| * C))
    · refine Eventually.of_forall fun s => ?_
      have hshift : Tendsto (fun x : ℝ => x - s) atBot atBot := by
        simpa [sub_eq_add_neg] using tendsto_atBot_add_const_right atBot (-s) tendsto_id
      exact (hlim.comp hshift).const_mul (r * Real.exp (r * s))
  have hlim_eval :
      (∫ s in Ici (0:ℝ), r * Real.exp (r * s) * L) = -L := by
    have hIoi :
        (∫ s in Ioi (0:ℝ), r * Real.exp (r * s) * L) = -L := by
      rw [show (fun s : ℝ => r * Real.exp (r * s) * L) =
          fun s => (r * L) * Real.exp (r * s) by
        funext s
        ring]
      rw [integral_const_mul, integral_exp_mul_Ioi (a := r) hr 0]
      have hrne : r ≠ 0 := ne_of_lt hr
      field_simp [hrne]
      simp
    rw [← hIoi]
    exact setIntegral_congr_set Ioi_ae_eq_Ici.symm
  have heq : (fun x => r * Real.exp (r * x) * tailLo r H x) =
      fun x => ∫ s in Ici (0:ℝ), r * Real.exp (r * s) * H (x - s) := by
    funext x
    unfold tailLo gWeight
    rw [setIntegral_Iic_sub_left x (fun y => Real.exp (-r * y) * H y)]
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards with s
    have hexp : Real.exp (r * x) * Real.exp (-r * (x - s)) =
        Real.exp (r * s) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [show r * Real.exp (r * x) * (Real.exp (-r * (x - s)) * H (x - s))
        = r * (Real.exp (r * x) * Real.exp (-r * (x - s))) * H (x - s) by ring,
      hexp]
  rw [heq]
  simpa [hlim_eval] using hDCT

theorem greenConvDeriv_tendsto_zero_explicit_of_source_tail_limits
    (hlam : 0 < lam) {R : ℝ → ℝ}
    (hRcont : Continuous R) (hRbdd : IsBddFun R)
    (hRbot : ∃ Ra : ℝ, Tendsto R atBot (𝓝 Ra))
    (hRtop : ∃ Rb : ℝ, Tendsto R atTop (𝓝 Rb)) :
    Tendsto (fun x => greenConvDeriv c lam R x) atBot (𝓝 0) ∧
      Tendsto (fun x => greenConvDeriv c lam R x) atTop (𝓝 0) := by
  rcases hRbdd with ⟨B, hB⟩
  have hHi : ∀ x,
      IntegrableOn (gWeight (greenRootPlus c lam) R) (Ioi x) :=
    fun x => gWeight_integrableOn_Ioi_of_bounded
      (greenRootPlus_pos (c := c) hlam) hRcont hB x
  have hLo : ∀ x,
      IntegrableOn (gWeight (greenRootMinus c lam) R) (Iic x) :=
    fun x => gWeight_integrableOn_Iic_of_bounded
      (greenRootMinus_neg (c := c) hlam) hRcont hB x
  rcases hRbot with ⟨Ra, hRa⟩
  rcases hRtop with ⟨Rb, hRb⟩
  have hplus_bot :
      Tendsto
        (fun x =>
          greenRootPlus c lam * Real.exp (greenRootPlus c lam * x) *
            tailHi (greenRootPlus c lam) R x) atBot (𝓝 Ra) :=
    tailHi_weighted_tendsto_atBot
      (r := greenRootPlus c lam) (C := |B|) (L := Ra)
      (greenRootPlus_pos (c := c) hlam) hRcont
      (fun y => le_trans (hB y) (le_abs_self B)) hRa
  have hminus_top :
      Tendsto
        (fun x =>
          greenRootMinus c lam * Real.exp (greenRootMinus c lam * x) *
            tailLo (greenRootMinus c lam) R x) atTop (𝓝 (-Rb)) :=
    tailLo_weighted_tendsto_atTop
      (r := greenRootMinus c lam) (C := |B|) (L := Rb)
      (greenRootMinus_neg (c := c) hlam) hRcont
      (fun y => le_trans (hB y) (le_abs_self B)) hRb
  have hminus_bot :
      Tendsto
        (fun x =>
          greenRootMinus c lam * Real.exp (greenRootMinus c lam * x) *
            tailLo (greenRootMinus c lam) R x) atBot (𝓝 (-Ra)) :=
    tailLo_weighted_tendsto_atBot
      (r := greenRootMinus c lam) (C := |B|) (L := Ra)
      (greenRootMinus_neg (c := c) hlam) hRcont
      (fun y => le_trans (hB y) (le_abs_self B)) hRa
  have hplus_top :
      Tendsto
        (fun x =>
          greenRootPlus c lam * Real.exp (greenRootPlus c lam * x) *
            tailHi (greenRootPlus c lam) R x) atTop (𝓝 Rb) :=
    tailHi_weighted_tendsto_atTop
      (r := greenRootPlus c lam) (C := |B|) (L := Rb)
      (greenRootPlus_pos (c := c) hlam) hRcont
      (fun y => le_trans (hB y) (le_abs_self B)) hRb
  constructor
  · unfold greenConvDeriv
    have hsum := hplus_bot.add hminus_bot
    have hscale := hsum.const_mul (greenDelta c lam)⁻¹
    simpa using hscale
  · unfold greenConvDeriv
    have hsum := hplus_top.add hminus_top
    have hscale := hsum.const_mul (greenDelta c lam)⁻¹
    simpa using hscale

theorem greenConvDeriv_tendsto_zero_of_source_tail_limits
    (hlam : 0 < lam) {R : ℝ → ℝ}
    (hRcont : Continuous R) (hRbdd : IsBddFun R)
    (hRbot : ∃ Ra : ℝ, Tendsto R atBot (𝓝 Ra))
    (hRtop : ∃ Rb : ℝ, Tendsto R atTop (𝓝 Rb)) :
    Tendsto (fun x => deriv (greenConv c lam R) x) atBot (𝓝 0) ∧
      Tendsto (fun x => deriv (greenConv c lam R) x) atTop (𝓝 0) := by
  rcases hRbdd with ⟨B, hB⟩
  have hHi : ∀ x,
      IntegrableOn (gWeight (greenRootPlus c lam) R) (Ioi x) :=
    fun x => gWeight_integrableOn_Ioi_of_bounded
      (greenRootPlus_pos (c := c) hlam) hRcont hB x
  have hLo : ∀ x,
      IntegrableOn (gWeight (greenRootMinus c lam) R) (Iic x) :=
    fun x => gWeight_integrableOn_Iic_of_bounded
      (greenRootMinus_neg (c := c) hlam) hRcont hB x
  have hderiv :
      (fun x => deriv (greenConv c lam R) x) = fun x => greenConvDeriv c lam R x := by
    funext x
    exact (greenConv_hasDerivAt (c := c) (lam := lam) hRcont hHi hLo x).deriv
  rw [hderiv]
  exact greenConvDeriv_tendsto_zero_explicit_of_source_tail_limits
    (c := c) (lam := lam) hlam hRcont ⟨B, hB⟩ hRbot hRtop

theorem greenKernel_comp_const_sub_mul_integrable_of_bounded
    (hlam : 0 < lam) {H : ℝ → ℝ} {B : ℝ}
    (hH : Continuous H) (hB : ∀ y, |H y| ≤ B) (x : ℝ) :
    Integrable (fun y => greenKernel c lam (x - y) * H y) := by
  have hK : Integrable (fun y => greenKernel c lam (x - y)) :=
    (greenKernel_integrable (c := c) hlam).comp_sub_left x
  exact hK.mul_bdd hH.aestronglyMeasurable
    (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hB y)

theorem greenConv_raw_eq_of_bounded
    (hlam : 0 < lam) {H : ℝ → ℝ} {B : ℝ}
    (hH : Continuous H) (hB : ∀ y, |H y| ≤ B) (x : ℝ) :
    (∫ y, greenKernel c lam (x - y) * H y) = greenConv c lam H x := by
  have hfull := greenKernel_comp_const_sub_mul_integrable_of_bounded
    (c := c) (lam := lam) hlam hH hB x
  exact kernelConv_eq_greenConv (c := c) (lam := lam) H x
    hfull.integrableOn hfull.integrableOn

theorem greenConv_eq_translated_integral_of_bounded
    (hlam : 0 < lam) {H : ℝ → ℝ} {B : ℝ}
    (hH : Continuous H) (hB : ∀ y, |H y| ≤ B) (x : ℝ) :
    greenConv c lam H x =
      ∫ t, greenKernel c lam (-t) * H (x + t) := by
  rw [← greenKernelConv_eq_translated (c := c) (lam := lam) H x]
  exact (greenConv_raw_eq_of_bounded (c := c) (lam := lam) hlam hH hB x).symm

theorem greenConv_tendsto_atBot_of_source_tendsto
    (hlam : 0 < lam) {H : ℝ → ℝ} {B L : ℝ}
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
    (hlam : 0 < lam) {H : ℝ → ℝ} {B L : ℝ}
    (hH : Continuous H) (hB : ∀ y, |H y| ≤ B)
    (hlim : Tendsto H atBot (𝓝 L)) :
    Tendsto (greenConvDeriv c lam H) atBot (𝓝 0) := by
  have hplus_bot :
      Tendsto
        (fun x =>
          greenRootPlus c lam * Real.exp (greenRootPlus c lam * x) *
            tailHi (greenRootPlus c lam) H x) atBot (𝓝 L) :=
    tailHi_weighted_tendsto_atBot
      (r := greenRootPlus c lam) (C := |B|) (L := L)
      (greenRootPlus_pos (c := c) hlam) hH
      (fun y => le_trans (hB y) (le_abs_self B)) hlim
  have hminus_bot :
      Tendsto
        (fun x =>
          greenRootMinus c lam * Real.exp (greenRootMinus c lam * x) *
            tailLo (greenRootMinus c lam) H x) atBot (𝓝 (-L)) :=
    tailLo_weighted_tendsto_atBot
      (r := greenRootMinus c lam) (C := |B|) (L := L)
      (greenRootMinus_neg (c := c) hlam) hH
      (fun y => le_trans (hB y) (le_abs_self B)) hlim
  unfold greenConvDeriv
  have hsum := hplus_bot.add hminus_bot
  have hscale := hsum.const_mul (greenDelta c lam)⁻¹
  simpa using hscale

theorem PaperWeightedHolderSourceBox.greenConv_tendsto_atBot
    {β Hbox : ℝ} {ω : ℝ → ℝ} (hlam : 0 < lam) {κ M B : ℝ} {R : ℝ → ℝ}
    (hBnn : 0 ≤ B)
    (hR : PaperWeightedHolderSourceBox κ M β B Hbox ω R) :
    ∃ Wm : ℝ, Tendsto (greenConv c lam R) atBot (𝓝 Wm) := by
  have hR_const : ∀ y, |R y| ≤ B * M := by
    intro y
    calc
      |R y| ≤ B * upperBarrier κ M y := hR.bound y
      _ ≤ B * M :=
        mul_le_mul_of_nonneg_left (upperBarrier_le_M κ M y) hBnn
  rcases hR.leftTail with ⟨Rm, hRm⟩
  exact ⟨Rm * lam⁻¹,
    greenConv_tendsto_atBot_of_source_tendsto
      (c := c) (lam := lam) hlam hR.cont hR_const hRm⟩

theorem PaperWeightedHolderSourceBox.greenConvDeriv_tendsto_atBot_zero
    {β Hbox : ℝ} {ω : ℝ → ℝ} (hlam : 0 < lam) {κ M B : ℝ} {R : ℝ → ℝ}
    (hBnn : 0 ≤ B)
    (hR : PaperWeightedHolderSourceBox κ M β B Hbox ω R) :
    Tendsto (greenConvDeriv c lam R) atBot (𝓝 0) := by
  have hR_const : ∀ y, |R y| ≤ B * M := by
    intro y
    calc
      |R y| ≤ B * upperBarrier κ M y := hR.bound y
      _ ≤ B * M :=
        mul_le_mul_of_nonneg_left (upperBarrier_le_M κ M y) hBnn
  rcases hR.leftTail with ⟨Rm, hRm⟩
  exact greenConvDeriv_tendsto_atBot_of_source_tendsto
    (c := c) (lam := lam) hlam hR.cont hR_const hRm

theorem PaperWeightedHolderSourceBox.deriv_greenConv_tendsto_atBot_zero
    {β Hbox : ℝ} {ω : ℝ → ℝ} (hlam : 0 < lam) {κ M B : ℝ} {R : ℝ → ℝ}
    (hBnn : 0 ≤ B)
    (hR : PaperWeightedHolderSourceBox κ M β B Hbox ω R) :
    Tendsto (fun x => deriv (greenConv c lam R) x) atBot (𝓝 0) := by
  have hR_const : ∀ y, |R y| ≤ B * M := by
    intro y
    calc
      |R y| ≤ B * upperBarrier κ M y := hR.bound y
      _ ≤ B * M :=
        mul_le_mul_of_nonneg_left (upperBarrier_le_M κ M y) hBnn
  have hHi : ∀ t,
      IntegrableOn (gWeight (greenRootPlus c lam) R) (Ioi t) :=
    fun t => gWeight_integrableOn_Ioi_of_bounded
      (greenRootPlus_pos (c := c) hlam) hR.cont hR_const t
  have hLo : ∀ t,
      IntegrableOn (gWeight (greenRootMinus c lam) R) (Iic t) :=
    fun t => gWeight_integrableOn_Iic_of_bounded
      (greenRootMinus_neg (c := c) hlam) hR.cont hR_const t
  have hderiv :
      (fun x => deriv (greenConv c lam R) x) = fun x => greenConvDeriv c lam R x := by
    funext x
    exact (greenConv_hasDerivAt (c := c) (lam := lam) hR.cont hHi hLo x).deriv
  rw [hderiv]
  exact hR.greenConvDeriv_tendsto_atBot_zero (c := c) (lam := lam) hlam hBnn

theorem kernel_abs_neg_tail_tendsto_atBot
    {K : ℝ → ℝ} (hKabs : Integrable (fun z => |K z|)) :
    Tendsto (fun A : ℝ => ∫ t in Set.Ioi (-A / 2), |K (-t)|)
      atBot (𝓝 0) := by
  let f : ℝ → ℝ := fun t => |K (-t)|
  have hf : Integrable f := by
    simpa [f] using hKabs.comp_neg
  have hanti : Antitone (fun T : ℝ => Set.Ioi T) := by
    intro a b hab
    exact Ioi_subset_Ioi hab
  have htail :
      Tendsto (fun T : ℝ => ∫ t in Set.Ioi T, f t) atTop
        (𝓝 (∫ t in (⋂ T : ℝ, Set.Ioi T), f t)) := by
    exact MeasureTheory.tendsto_setIntegral_of_antitone
      (μ := volume) (f := f) (s := fun T : ℝ => Set.Ioi T)
      (fun _ => measurableSet_Ioi) hanti ⟨(0 : ℝ), hf.integrableOn⟩
  have hInter : (⋂ T : ℝ, Set.Ioi T) = (∅ : Set ℝ) := by
    ext x
    constructor
    · intro hx
      exact (lt_irrefl x) (by
        simpa [Set.mem_Ioi] using (Set.mem_iInter.mp hx) x)
    · intro hx
      cases hx
  have hdiv : Tendsto (fun A : ℝ => A / 2) atBot atBot :=
    tendsto_id.atBot_div_const (by norm_num : (0 : ℝ) < 2)
  have hneg : Tendsto (fun A : ℝ => -(A / 2)) atBot atTop :=
    tendsto_neg_atBot_atTop.comp hdiv
  have htail' := htail.comp hneg
  simpa [Function.comp_def, f, hInter, neg_div] using htail'

theorem kernel_translated_leftTailCauchy_bound
    {K R : ℝ → ℝ} {C L1 : ℝ} {ω : ℝ → ℝ}
    (hKmeas : Measurable K)
    (hKabs : Integrable (fun z => |K z|))
    (hL1 : (∫ t, |K (-t)|) = L1)
    (hRcont : Continuous R)
    (_hCnn : 0 ≤ C) (hRbound : ∀ z, |R z| ≤ C)
    (hωnn : ∀ A, 0 ≤ ω A)
    (hleft : ∀ A x y, x ≤ A → y ≤ A → |R x - R y| ≤ ω A)
    (A x y : ℝ) (hx : x ≤ A) (hy : y ≤ A) :
    |(∫ t, K (-t) * R (x + t)) -
        (∫ t, K (-t) * R (y + t))|
      ≤ L1 * ω (A / 2) +
        2 * C * (∫ t in Set.Ioi (-A / 2), |K (-t)|) := by
  let S : ℝ := -A / 2
  let F : ℝ → ℝ := fun t => K (-t) * R (x + t) - K (-t) * R (y + t)
  have hKabs_neg : Integrable (fun t => |K (-t)|) := by
    simpa using hKabs.comp_neg
  have hKneg_meas : Measurable (fun t : ℝ => K (-t)) :=
    hKmeas.comp measurable_neg
  have hRx_meas : AEStronglyMeasurable (fun t : ℝ => R (x + t)) volume :=
    (hRcont.comp (continuous_const.add continuous_id)).aestronglyMeasurable
  have hRy_meas : AEStronglyMeasurable (fun t : ℝ => R (y + t)) volume :=
    (hRcont.comp (continuous_const.add continuous_id)).aestronglyMeasurable
  have hdomC : Integrable (fun t : ℝ => |K (-t)| * C) :=
    hKabs_neg.mul_const C
  have hFx : Integrable (fun t : ℝ => K (-t) * R (x + t)) := by
    refine hdomC.mono' (hKneg_meas.aestronglyMeasurable.mul hRx_meas) ?_
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hRbound (x + t)) (abs_nonneg _)
  have hFy : Integrable (fun t : ℝ => K (-t) * R (y + t)) := by
    refine hdomC.mono' (hKneg_meas.aestronglyMeasurable.mul hRy_meas) ?_
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hRbound (y + t)) (abs_nonneg _)
  have hFint : Integrable F := by
    simpa [F] using hFx.sub hFy
  have hNint : Integrable (fun t : ℝ => |F t|) := by
    simpa [Real.norm_eq_abs] using hFint.norm
  have hdiff :
      |(∫ t, K (-t) * R (x + t)) -
          (∫ t, K (-t) * R (y + t))|
        ≤ ∫ t, |F t| := by
    rw [← integral_sub hFx hFy]
    simpa [F, Real.norm_eq_abs] using
      (norm_integral_le_integral_norm (μ := volume) F)
  have hIic_bound :
      (∫ t in Set.Iic S, |F t|)
        ≤ ∫ t in Set.Iic S, |K (-t)| * ω (A / 2) := by
    refine MeasureTheory.setIntegral_mono_on
      hNint.integrableOn (hKabs_neg.mul_const (ω (A / 2))).integrableOn
      measurableSet_Iic ?_
    intro t ht
    have htS : t ≤ S := by simpa [S] using ht
    have hx' : x + t ≤ A / 2 := by
      dsimp [S] at htS
      linarith
    have hy' : y + t ≤ A / 2 := by
      dsimp [S] at htS
      linarith
    have hdiffR : |R (x + t) - R (y + t)| ≤ ω (A / 2) :=
      hleft (A / 2) (x + t) (y + t) hx' hy'
    have hFeq :
        F t = K (-t) * (R (x + t) - R (y + t)) := by
      dsimp [F]
      ring
    rw [hFeq, abs_mul]
    exact mul_le_mul_of_nonneg_left hdiffR (abs_nonneg _)
  have hωA : 0 ≤ ω (A / 2) := hωnn (A / 2)
  have hKω_nonneg :
      0 ≤ᵐ[volume] fun t : ℝ => |K (-t)| * ω (A / 2) :=
    Eventually.of_forall fun t => mul_nonneg (abs_nonneg _) hωA
  have hIic_all :
      (∫ t in Set.Iic S, |K (-t)| * ω (A / 2))
        ≤ ∫ t, |K (-t)| * ω (A / 2) :=
    MeasureTheory.setIntegral_le_integral
      (s := Set.Iic S) (hKabs_neg.mul_const (ω (A / 2))) hKω_nonneg
  have hIic_final :
      (∫ t in Set.Iic S, |F t|) ≤ L1 * ω (A / 2) := by
    calc
      (∫ t in Set.Iic S, |F t|)
          ≤ ∫ t in Set.Iic S, |K (-t)| * ω (A / 2) := hIic_bound
      _ ≤ ∫ t, |K (-t)| * ω (A / 2) := hIic_all
      _ = L1 * ω (A / 2) := by
        rw [integral_mul_const, hL1]
  have hIoi_bound :
      (∫ t in Set.Ioi S, |F t|)
        ≤ ∫ t in Set.Ioi S, |K (-t)| * (2 * C) := by
    refine MeasureTheory.setIntegral_mono_on
      hNint.integrableOn (hKabs_neg.mul_const (2 * C)).integrableOn
      measurableSet_Ioi ?_
    intro t ht
    have hRdiff : |R (x + t) - R (y + t)| ≤ 2 * C := by
      calc
        |R (x + t) - R (y + t)|
            ≤ |R (x + t)| + |R (y + t)| := abs_sub _ _
        _ ≤ C + C := add_le_add (hRbound (x + t)) (hRbound (y + t))
        _ = 2 * C := by ring
    have hFeq :
        F t = K (-t) * (R (x + t) - R (y + t)) := by
      dsimp [F]
      ring
    rw [hFeq, abs_mul]
    exact mul_le_mul_of_nonneg_left hRdiff (abs_nonneg _)
  have hsplit := MeasureTheory.integral_add_compl
    (s := Set.Iic S) measurableSet_Iic hNint
  simp only [Set.compl_Iic] at hsplit
  calc
    |(∫ t, K (-t) * R (x + t)) -
        (∫ t, K (-t) * R (y + t))|
        ≤ ∫ t, |F t| := hdiff
    _ = (∫ t in Set.Iic S, |F t|) +
          ∫ t in Set.Ioi S, |F t| := hsplit.symm
    _ ≤ L1 * ω (A / 2) +
          (∫ t in Set.Ioi S, |K (-t)| * (2 * C)) :=
        add_le_add hIic_final hIoi_bound
    _ = L1 * ω (A / 2) +
          2 * C * (∫ t in Set.Ioi (-A / 2), |K (-t)|) := by
        dsimp [S]
        rw [integral_mul_const]
        ring

theorem PaperWeightedHolderSourceBox.greenConv_leftTailCauchy_uniform
    (hlam : 0 < lam) {κ M B β Hbox : ℝ} {ω : ℝ → ℝ} (hBnn : 0 ≤ B) :
    ∃ ωW : ℝ → ℝ,
      (∀ A, 0 ≤ ωW A) ∧ Tendsto ωW atBot (𝓝 0) ∧
      ∀ R, PaperWeightedHolderSourceBox κ M β B Hbox ω R →
      ∀ A x y, x ≤ A → y ≤ A →
        |greenConv c lam R x - greenConv c lam R y| ≤ ωW A := by
  by_cases hbox_nonempty :
      ∃ R, PaperWeightedHolderSourceBox κ M β B Hbox ω R
  · rcases hbox_nonempty with ⟨R0, hR0⟩
    let C : ℝ := max (B * M) 0
    let tail : ℝ → ℝ := fun A =>
      ∫ t in Set.Ioi (-A / 2), |greenKernel c lam (-t)|
    let ωW : ℝ → ℝ := fun A => lam⁻¹ * ω (A / 2) + 2 * C * tail A
    refine ⟨ωW, ?_, ?_, ?_⟩
    · intro A
      have hCnn : 0 ≤ C := by dsimp [C]; exact le_max_right _ _
      have htail_nn : 0 ≤ tail A := by
        dsimp [tail]
        exact integral_nonneg fun t => abs_nonneg _
      exact add_nonneg
        (mul_nonneg (inv_nonneg.mpr hlam.le) (hR0.omega_nonneg (A / 2)))
        (mul_nonneg (mul_nonneg (by norm_num) hCnn) htail_nn)
    · have hdiv : Tendsto (fun A : ℝ => A / 2) atBot atBot :=
        tendsto_id.atBot_div_const (by norm_num : (0 : ℝ) < 2)
      have hω : Tendsto (fun A : ℝ => ω (A / 2)) atBot (𝓝 0) :=
        hR0.omega_tendsto.comp hdiv
      have hKabs : Integrable (fun z => |greenKernel c lam z|) :=
        (greenKernel_integrable (c := c) hlam).abs
      have htail :
          Tendsto tail atBot (𝓝 0) := by
        simpa [tail] using
          (kernel_abs_neg_tail_tendsto_atBot
            (K := greenKernel c lam) hKabs)
      have hsum := (hω.const_mul lam⁻¹).add (htail.const_mul (2 * C))
      simpa [ωW] using hsum
    · intro R hR A x y hx hy
      have hCnn : 0 ≤ C := by dsimp [C]; exact le_max_right _ _
      have hRbound : ∀ z, |R z| ≤ C := by
        intro z
        exact (hR.abs_le_const (B := B) hBnn z).trans (le_max_left _ _)
      have hKmeas : Measurable (greenKernel c lam) :=
        (greenKernel_continuous (c := c) (lam := lam)).measurable
      have hKabs : Integrable (fun z => |greenKernel c lam z|) :=
        (greenKernel_integrable (c := c) hlam).abs
      have hL1 : (∫ t, |greenKernel c lam (-t)|) = lam⁻¹ := by
        rw [integral_neg_eq_self (fun z => |greenKernel c lam z|) volume]
        exact greenKernel_l1_eq (c := c) hlam
      have hxrepr :
          greenConv c lam R x =
            ∫ t, greenKernel c lam (-t) * R (x + t) :=
        greenConv_eq_translated_integral_of_bounded
          (c := c) (lam := lam) hlam hR.cont hRbound x
      have hyrepr :
          greenConv c lam R y =
            ∫ t, greenKernel c lam (-t) * R (y + t) :=
        greenConv_eq_translated_integral_of_bounded
          (c := c) (lam := lam) hlam hR.cont hRbound y
      rw [hxrepr, hyrepr]
      simpa [ωW, tail] using
        kernel_translated_leftTailCauchy_bound
          (K := greenKernel c lam) (R := R) (C := C) (L1 := lam⁻¹)
          (ω := ω) hKmeas hKabs hL1 hR.cont hCnn hRbound
          hR.omega_nonneg hR.leftTailCauchy A x y hx hy
  · refine ⟨fun _ => 0, ?_, ?_, ?_⟩
    · intro A
      norm_num
    · exact tendsto_const_nhds
    · intro R hR
      exact False.elim (hbox_nonempty ⟨R, hR⟩)

theorem greenKernelDeriv_measurable_for_leftTail :
    Measurable (greenKernelDeriv c lam) := by
  unfold greenKernelDeriv
  refine Measurable.ite (measurableSet_le measurable_id measurable_const) ?_ ?_
  · simpa [mul_assoc] using
      (continuous_const.mul (continuous_const.mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id)))).measurable
  · simpa [mul_assoc] using
      (continuous_const.mul (continuous_const.mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id)))).measurable

theorem greenKernelDeriv_integrable_signed_for_leftTail
    (hlam : 0 < lam) :
    Integrable (greenKernelDeriv c lam) := by
  refine (greenKernelDeriv_integrable (c := c) hlam).mono'
    (greenKernelDeriv_measurable_for_leftTail (c := c) (lam := lam)).aestronglyMeasurable ?_
  filter_upwards with z
  simp [Real.norm_eq_abs]

theorem greenKernelDeriv_setIntegral_Iic_for_leftTail
    (hlam : 0 < lam) :
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

theorem greenKernelDeriv_setIntegral_Ioi_for_leftTail
    (hlam : 0 < lam) :
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

theorem greenKernelDeriv_integral_eq_zero_for_leftTail
    (hlam : 0 < lam) :
    ∫ z, greenKernelDeriv c lam z = 0 := by
  have hfi := greenKernelDeriv_integrable_signed_for_leftTail
    (c := c) (lam := lam) hlam
  have hsplit := MeasureTheory.integral_add_compl
    (s := Set.Iic (0 : ℝ)) measurableSet_Iic hfi
  simp only [Set.compl_Iic] at hsplit
  linarith [hsplit.symm,
    greenKernelDeriv_setIntegral_Iic_for_leftTail (c := c) hlam,
    greenKernelDeriv_setIntegral_Ioi_for_leftTail (c := c) hlam]

theorem kernel_translated_leftTailSmall_bound
    {K R : ℝ → ℝ} {C L1 : ℝ} {ω : ℝ → ℝ}
    (hKmeas : Measurable K)
    (hKsigned : Integrable K)
    (hKabs : Integrable (fun z => |K z|))
    (hKzero : (∫ t, K (-t)) = 0)
    (hL1 : (∫ t, |K (-t)|) = L1)
    (hRcont : Continuous R)
    (_hCnn : 0 ≤ C) (hRbound : ∀ z, |R z| ≤ C)
    (hωnn : ∀ A, 0 ≤ ω A)
    (hleft : ∀ A x y, x ≤ A → y ≤ A → |R x - R y| ≤ ω A)
    (A x : ℝ) (hx : x ≤ A) :
    |∫ t, K (-t) * R (x + t)|
      ≤ if A ≤ 0 then
          L1 * ω (A / 2) +
            2 * C * (∫ t in Set.Ioi (-A / 2), |K (-t)|)
        else L1 * C := by
  let S : ℝ := -A / 2
  let Fx : ℝ → ℝ := fun t => K (-t) * R (x + t)
  have hKabs_neg : Integrable (fun t => |K (-t)|) := by
    simpa using hKabs.comp_neg
  have hKsigned_neg : Integrable (fun t => K (-t)) := by
    simpa using hKsigned.comp_neg
  have hKneg_meas : Measurable (fun t : ℝ => K (-t)) :=
    hKmeas.comp measurable_neg
  have hRx_meas : AEStronglyMeasurable (fun t : ℝ => R (x + t)) volume :=
    (hRcont.comp (continuous_const.add continuous_id)).aestronglyMeasurable
  have hdomC : Integrable (fun t : ℝ => |K (-t)| * C) :=
    hKabs_neg.mul_const C
  have hFx : Integrable Fx := by
    refine hdomC.mono' (hKneg_meas.aestronglyMeasurable.mul hRx_meas) ?_
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hRbound (x + t)) (abs_nonneg _)
  have hcrude : |∫ t, Fx t| ≤ L1 * C := by
    calc
      |∫ t, Fx t| ≤ ∫ t, |Fx t| := by
        simpa [Fx, Real.norm_eq_abs] using
          (norm_integral_le_integral_norm (μ := volume) Fx)
      _ ≤ ∫ t, |K (-t)| * C := by
        refine MeasureTheory.integral_mono hFx.norm hdomC ?_
        intro t
        dsimp [Fx]
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hRbound (x + t)) (abs_nonneg _)
      _ = L1 * C := by
        rw [integral_mul_const, hL1]
  by_cases hA : A ≤ 0
  · simp only [hA, if_true]
    let F : ℝ → ℝ := fun t => K (-t) * R (x + t) - K (-t) * R x
    have hFconst : Integrable (fun t : ℝ => K (-t) * R x) :=
      hKsigned_neg.mul_const (R x)
    have hFint : Integrable F := by
      simpa [F, Fx] using hFx.sub hFconst
    have hNint : Integrable (fun t : ℝ => |F t|) := by
      simpa [Real.norm_eq_abs] using hFint.norm
    have hzero_const : (∫ t, K (-t) * R x) = 0 := by
      rw [integral_mul_const, hKzero, zero_mul]
    have hdiff :
        |∫ t, Fx t| ≤ ∫ t, |F t| := by
      calc
        |∫ t, Fx t|
            = |(∫ t, Fx t) - ∫ t, K (-t) * R x| := by
              rw [hzero_const, sub_zero]
        _ = |∫ t, F t| := by
              rw [integral_sub hFx hFconst]
        _ ≤ ∫ t, |F t| := by
              simpa [F, Real.norm_eq_abs] using
                (norm_integral_le_integral_norm (μ := volume) F)
    have hIic_bound :
        (∫ t in Set.Iic S, |F t|)
          ≤ ∫ t in Set.Iic S, |K (-t)| * ω (A / 2) := by
      refine MeasureTheory.setIntegral_mono_on
        hNint.integrableOn (hKabs_neg.mul_const (ω (A / 2))).integrableOn
        measurableSet_Iic ?_
      intro t ht
      have htS : t ≤ S := by simpa [S] using ht
      have hx' : x + t ≤ A / 2 := by
        dsimp [S] at htS
        linarith
      have hxhalf : x ≤ A / 2 := by linarith
      have hdiffR : |R (x + t) - R x| ≤ ω (A / 2) :=
        hleft (A / 2) (x + t) x hx' hxhalf
      have hFeq :
          F t = K (-t) * (R (x + t) - R x) := by
        dsimp [F]
        ring
      rw [hFeq, abs_mul]
      exact mul_le_mul_of_nonneg_left hdiffR (abs_nonneg _)
    have hωA : 0 ≤ ω (A / 2) := hωnn (A / 2)
    have hKω_nonneg :
        0 ≤ᵐ[volume] fun t : ℝ => |K (-t)| * ω (A / 2) :=
      Eventually.of_forall fun t => mul_nonneg (abs_nonneg _) hωA
    have hIic_all :
        (∫ t in Set.Iic S, |K (-t)| * ω (A / 2))
          ≤ ∫ t, |K (-t)| * ω (A / 2) :=
      MeasureTheory.setIntegral_le_integral
        (s := Set.Iic S) (hKabs_neg.mul_const (ω (A / 2))) hKω_nonneg
    have hIic_final :
        (∫ t in Set.Iic S, |F t|) ≤ L1 * ω (A / 2) := by
      calc
        (∫ t in Set.Iic S, |F t|)
            ≤ ∫ t in Set.Iic S, |K (-t)| * ω (A / 2) := hIic_bound
        _ ≤ ∫ t, |K (-t)| * ω (A / 2) := hIic_all
        _ = L1 * ω (A / 2) := by
          rw [integral_mul_const, hL1]
    have hIoi_bound :
        (∫ t in Set.Ioi S, |F t|)
          ≤ ∫ t in Set.Ioi S, |K (-t)| * (2 * C) := by
      refine MeasureTheory.setIntegral_mono_on
        hNint.integrableOn (hKabs_neg.mul_const (2 * C)).integrableOn
        measurableSet_Ioi ?_
      intro t ht
      have hRdiff : |R (x + t) - R x| ≤ 2 * C := by
        calc
          |R (x + t) - R x| ≤ |R (x + t)| + |R x| := abs_sub _ _
          _ ≤ C + C := add_le_add (hRbound (x + t)) (hRbound x)
          _ = 2 * C := by ring
      have hFeq :
          F t = K (-t) * (R (x + t) - R x) := by
        dsimp [F]
        ring
      rw [hFeq, abs_mul]
      exact mul_le_mul_of_nonneg_left hRdiff (abs_nonneg _)
    have hsplit := MeasureTheory.integral_add_compl
      (s := Set.Iic S) measurableSet_Iic hNint
    simp only [Set.compl_Iic] at hsplit
    calc
      |∫ t, Fx t| ≤ ∫ t, |F t| := hdiff
      _ = (∫ t in Set.Iic S, |F t|) +
            ∫ t in Set.Ioi S, |F t| := hsplit.symm
      _ ≤ L1 * ω (A / 2) +
            (∫ t in Set.Ioi S, |K (-t)| * (2 * C)) :=
          add_le_add hIic_final hIoi_bound
      _ = L1 * ω (A / 2) +
            2 * C * (∫ t in Set.Ioi (-A / 2), |K (-t)|) := by
          dsimp [S]
          rw [integral_mul_const]
          ring
  · simp only [hA, if_false]
    simpa [Fx] using hcrude

theorem greenKernelDeriv_comp_const_sub_mul_integrable_of_bounded_for_leftTail
    (hlam : 0 < lam) {H : ℝ → ℝ} {B : ℝ}
    (hH : Continuous H) (hB : ∀ y, |H y| ≤ B) (x : ℝ) :
    Integrable (fun y => greenKernelDeriv c lam (x - y) * H y) := by
  have hK : Integrable (fun y => greenKernelDeriv c lam (x - y)) := by
    simpa using
      (greenKernelDeriv_integrable_signed_for_leftTail
        (c := c) (lam := lam) hlam).comp_sub_left x
  exact hK.mul_bdd hH.aestronglyMeasurable
    (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hB y)

theorem greenKernelDerivConv_eq_translated_for_leftTail
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

theorem greenKernelDerivConv_eq_greenConvDeriv_for_leftTail
    (hlam : 0 < lam) {H : ℝ → ℝ} {B : ℝ}
    (hH : Continuous H) (hB : ∀ y, |H y| ≤ B) (x : ℝ) :
    (∫ y, greenKernelDeriv c lam (x - y) * H y)
      = greenConvDeriv c lam H x := by
  have hfull := greenKernelDeriv_comp_const_sub_mul_integrable_of_bounded_for_leftTail
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

theorem greenConvDeriv_eq_translated_integral_of_bounded_for_leftTail
    (hlam : 0 < lam) {H : ℝ → ℝ} {B : ℝ}
    (hH : Continuous H) (hB : ∀ y, |H y| ≤ B) (x : ℝ) :
    greenConvDeriv c lam H x =
      ∫ t, greenKernelDeriv c lam (-t) * H (x + t) := by
  rw [← greenKernelDerivConv_eq_translated_for_leftTail c lam H x]
  exact (greenKernelDerivConv_eq_greenConvDeriv_for_leftTail
    (c := c) (lam := lam) hlam hH hB x).symm

theorem PaperWeightedHolderSourceBox.greenConvDeriv_leftTailCauchy_uniform
    (hlam : 0 < lam) {κ M B β Hbox : ℝ} {ω : ℝ → ℝ} (hBnn : 0 ≤ B) :
    ∃ ωWd : ℝ → ℝ,
      (∀ A, 0 ≤ ωWd A) ∧ Tendsto ωWd atBot (𝓝 0) ∧
      ∀ R, PaperWeightedHolderSourceBox κ M β B Hbox ω R →
      ∀ A x y, x ≤ A → y ≤ A →
        |greenConvDeriv c lam R x - greenConvDeriv c lam R y| ≤ ωWd A := by
  by_cases hbox_nonempty :
      ∃ R, PaperWeightedHolderSourceBox κ M β B Hbox ω R
  · rcases hbox_nonempty with ⟨R0, hR0⟩
    let C : ℝ := max (B * M) 0
    let L1 : ℝ := 2 * (greenDelta c lam)⁻¹
    let tail : ℝ → ℝ := fun A =>
      ∫ t in Set.Ioi (-A / 2), |greenKernelDeriv c lam (-t)|
    let ωWd : ℝ → ℝ := fun A => L1 * ω (A / 2) + 2 * C * tail A
    refine ⟨ωWd, ?_, ?_, ?_⟩
    · intro A
      have hCnn : 0 ≤ C := by dsimp [C]; exact le_max_right _ _
      have hL1nn : 0 ≤ L1 := by
        dsimp [L1]
        exact mul_nonneg (by norm_num)
          (inv_nonneg.mpr (greenDelta_pos (c := c) hlam).le)
      have htail_nn : 0 ≤ tail A := by
        dsimp [tail]
        exact integral_nonneg fun t => abs_nonneg _
      exact add_nonneg
        (mul_nonneg hL1nn (hR0.omega_nonneg (A / 2)))
        (mul_nonneg (mul_nonneg (by norm_num) hCnn) htail_nn)
    · have hdiv : Tendsto (fun A : ℝ => A / 2) atBot atBot :=
        tendsto_id.atBot_div_const (by norm_num : (0 : ℝ) < 2)
      have hω : Tendsto (fun A : ℝ => ω (A / 2)) atBot (𝓝 0) :=
        hR0.omega_tendsto.comp hdiv
      have hKabs : Integrable (fun z => |greenKernelDeriv c lam z|) :=
        greenKernelDeriv_integrable (c := c) hlam
      have htail :
          Tendsto tail atBot (𝓝 0) := by
        simpa [tail] using
          (kernel_abs_neg_tail_tendsto_atBot
            (K := greenKernelDeriv c lam) hKabs)
      have hsum := (hω.const_mul L1).add (htail.const_mul (2 * C))
      simpa [ωWd] using hsum
    · intro R hR A x y hx hy
      have hCnn : 0 ≤ C := by dsimp [C]; exact le_max_right _ _
      have hRbound : ∀ z, |R z| ≤ C := by
        intro z
        exact (hR.abs_le_const (B := B) hBnn z).trans (le_max_left _ _)
      have hKmeas : Measurable (greenKernelDeriv c lam) :=
        greenKernelDeriv_measurable_for_leftTail (c := c) (lam := lam)
      have hKabs : Integrable (fun z => |greenKernelDeriv c lam z|) :=
        greenKernelDeriv_integrable (c := c) hlam
      have hL1eq :
          (∫ t, |greenKernelDeriv c lam (-t)|) = L1 := by
        dsimp [L1]
        rw [integral_neg_eq_self (fun z => |greenKernelDeriv c lam z|) volume]
        exact greenKernelDeriv_l1_eq (c := c) hlam
      have hxrepr :
          greenConvDeriv c lam R x =
            ∫ t, greenKernelDeriv c lam (-t) * R (x + t) :=
        greenConvDeriv_eq_translated_integral_of_bounded_for_leftTail
          (c := c) (lam := lam) hlam hR.cont hRbound x
      have hyrepr :
          greenConvDeriv c lam R y =
            ∫ t, greenKernelDeriv c lam (-t) * R (y + t) :=
        greenConvDeriv_eq_translated_integral_of_bounded_for_leftTail
          (c := c) (lam := lam) hlam hR.cont hRbound y
      rw [hxrepr, hyrepr]
      simpa [ωWd, tail] using
        kernel_translated_leftTailCauchy_bound
          (K := greenKernelDeriv c lam) (R := R) (C := C) (L1 := L1)
          (ω := ω) hKmeas hKabs hL1eq hR.cont hCnn hRbound
          hR.omega_nonneg hR.leftTailCauchy A x y hx hy
  · refine ⟨fun _ => 0, ?_, ?_, ?_⟩
    · intro A
      norm_num
    · exact tendsto_const_nhds
    · intro R hR
      exact False.elim (hbox_nonempty ⟨R, hR⟩)

theorem PaperWeightedHolderSourceBox.greenConvDeriv_leftTailSmall_uniform
    (hlam : 0 < lam) {κ M B β Hbox : ℝ} {ω : ℝ → ℝ} (hBnn : 0 ≤ B) :
    ∃ ωWd0 : ℝ → ℝ,
      (∀ A, 0 ≤ ωWd0 A) ∧ Tendsto ωWd0 atBot (𝓝 0) ∧
      ∀ R, PaperWeightedHolderSourceBox κ M β B Hbox ω R →
      ∀ A x, x ≤ A →
        |greenConvDeriv c lam R x| ≤ ωWd0 A := by
  by_cases hbox_nonempty :
      ∃ R, PaperWeightedHolderSourceBox κ M β B Hbox ω R
  · rcases hbox_nonempty with ⟨R0, hR0⟩
    let C : ℝ := max (B * M) 0
    let L1 : ℝ := 2 * (greenDelta c lam)⁻¹
    let tail : ℝ → ℝ := fun A =>
      ∫ t in Set.Ioi (-A / 2), |greenKernelDeriv c lam (-t)|
    let main : ℝ → ℝ := fun A => L1 * ω (A / 2) + 2 * C * tail A
    let ωWd0 : ℝ → ℝ := fun A => if A ≤ 0 then main A else L1 * C
    refine ⟨ωWd0, ?_, ?_, ?_⟩
    · intro A
      have hCnn : 0 ≤ C := by dsimp [C]; exact le_max_right _ _
      have hL1nn : 0 ≤ L1 := by
        dsimp [L1]
        exact mul_nonneg (by norm_num)
          (inv_nonneg.mpr (greenDelta_pos (c := c) hlam).le)
      by_cases hA : A ≤ 0
      · have htail_nn : 0 ≤ tail A := by
          dsimp [tail]
          exact integral_nonneg fun t => abs_nonneg _
        have hmain_nn : 0 ≤ main A := by
          dsimp [main]
          exact add_nonneg
            (mul_nonneg hL1nn (hR0.omega_nonneg (A / 2)))
            (mul_nonneg (mul_nonneg (by norm_num) hCnn) htail_nn)
        simpa [ωWd0, hA] using hmain_nn
      · have hprod : 0 ≤ L1 * C := mul_nonneg hL1nn hCnn
        simpa [ωWd0, hA] using hprod
    · have hdiv : Tendsto (fun A : ℝ => A / 2) atBot atBot :=
        tendsto_id.atBot_div_const (by norm_num : (0 : ℝ) < 2)
      have hω : Tendsto (fun A : ℝ => ω (A / 2)) atBot (𝓝 0) :=
        hR0.omega_tendsto.comp hdiv
      have hKabs : Integrable (fun z => |greenKernelDeriv c lam z|) :=
        greenKernelDeriv_integrable (c := c) hlam
      have htail :
          Tendsto tail atBot (𝓝 0) := by
        simpa [tail] using
          (kernel_abs_neg_tail_tendsto_atBot
            (K := greenKernelDeriv c lam) hKabs)
      have hmain : Tendsto main atBot (𝓝 0) := by
        have hsum := (hω.const_mul L1).add (htail.const_mul (2 * C))
        simpa [main] using hsum
      refine hmain.congr' ?_
      filter_upwards [eventually_le_atBot (0 : ℝ)] with A hA
      simp [ωWd0, main, hA]
    · intro R hR A x hx
      have hCnn : 0 ≤ C := by dsimp [C]; exact le_max_right _ _
      have hRbound : ∀ z, |R z| ≤ C := by
        intro z
        exact (hR.abs_le_const (B := B) hBnn z).trans (le_max_left _ _)
      have hKmeas : Measurable (greenKernelDeriv c lam) :=
        greenKernelDeriv_measurable_for_leftTail (c := c) (lam := lam)
      have hKsigned : Integrable (greenKernelDeriv c lam) :=
        greenKernelDeriv_integrable_signed_for_leftTail
          (c := c) (lam := lam) hlam
      have hKabs : Integrable (fun z => |greenKernelDeriv c lam z|) :=
        greenKernelDeriv_integrable (c := c) hlam
      have hKzero : (∫ t, greenKernelDeriv c lam (-t)) = 0 := by
        rw [integral_neg_eq_self (greenKernelDeriv c lam) volume]
        exact greenKernelDeriv_integral_eq_zero_for_leftTail
          (c := c) (lam := lam) hlam
      have hL1eq :
          (∫ t, |greenKernelDeriv c lam (-t)|) = L1 := by
        dsimp [L1]
        rw [integral_neg_eq_self (fun z => |greenKernelDeriv c lam z|) volume]
        exact greenKernelDeriv_l1_eq (c := c) hlam
      have hxrepr :
          greenConvDeriv c lam R x =
            ∫ t, greenKernelDeriv c lam (-t) * R (x + t) :=
        greenConvDeriv_eq_translated_integral_of_bounded_for_leftTail
          (c := c) (lam := lam) hlam hR.cont hRbound x
      rw [hxrepr]
      simpa [ωWd0, main, tail] using
        kernel_translated_leftTailSmall_bound
          (K := greenKernelDeriv c lam) (R := R) (C := C) (L1 := L1)
          (ω := ω) hKmeas hKsigned hKabs hKzero hL1eq hR.cont
          hCnn hRbound hR.omega_nonneg hR.leftTailCauchy A x hx
  · refine ⟨fun _ => 0, ?_, ?_, ?_⟩
    · intro A
      norm_num
    · exact tendsto_const_nhds
    · intro R hR
      exact False.elim (hbox_nonempty ⟨R, hR⟩)

theorem greenKernel_neg_mul_translate_integrable_of_bounded
    (hlam : 0 < lam) {H : ℝ → ℝ} {B : ℝ}
    (hH : Continuous H) (hB : ∀ y, |H y| ≤ B) (x : ℝ) :
    Integrable (fun t => greenKernel c lam (-t) * H (x + t)) := by
  have hK : Integrable (fun t => greenKernel c lam (-t)) :=
    (greenKernel_integrable (c := c) hlam).comp_neg
  have hshift : AEStronglyMeasurable (fun t : ℝ => H (x + t)) volume :=
    (hH.comp (continuous_const.add continuous_id)).aestronglyMeasurable
  exact hK.mul_bdd hshift
    (Eventually.of_forall fun t => by simpa [Real.norm_eq_abs] using hB (x + t))

theorem greenConv_expLeftRate
    (hlam : 0 < lam) {sigma aL C ell B : ℝ} {R : ℝ → ℝ}
    (hsigma0 : 0 ≤ sigma)
    (hsigma : sigma < greenRootPlus c lam)
    (hRcont : Continuous R) (hRbound : ∀ y, |R y| ≤ B)
    (hRrate : ExpLeftRate sigma aL C R ell) :
    ExpLeftRate sigma aL (greenKernelExpMoment c lam sigma * C)
      (greenConv c lam R) (ell * lam⁻¹) := by
  intro x
  have hFx : Integrable (fun t => greenKernel c lam (-t) * R (x + t)) :=
    greenKernel_neg_mul_translate_integrable_of_bounded
      (c := c) (lam := lam) hlam hRcont hRbound x
  have hKsigned : Integrable (fun t => greenKernel c lam (-t)) :=
    (greenKernel_integrable (c := c) hlam).comp_neg
  have hFc : Integrable (fun t => greenKernel c lam (-t) * ell) :=
    hKsigned.mul_const ell
  have hrepr :
      greenConv c lam R x =
        ∫ t, greenKernel c lam (-t) * R (x + t) :=
    greenConv_eq_translated_integral_of_bounded
      (c := c) (lam := lam) hlam hRcont hRbound x
  have hconst :
      (∫ t, greenKernel c lam (-t) * ell) = ell * lam⁻¹ := by
    rw [show (fun t : ℝ => greenKernel c lam (-t) * ell)
        = fun t : ℝ => ell * greenKernel c lam (-t) by
          funext t
          ring]
    rw [MeasureTheory.integral_const_mul]
    rw [integral_neg_eq_self (greenKernel c lam) volume]
    rw [greenKernel_integral_eq (c := c) hlam]
  let F : ℝ → ℝ := fun t => greenKernel c lam (-t) * (R (x + t) - ell)
  have hFint : Integrable F := by
    have hdiff := hFx.sub hFc
    refine hdiff.congr ?_
    exact Eventually.of_forall fun t => by
      dsimp [F]
      ring
  have hmoment_int :
      Integrable
        (fun t => |greenKernel c lam (-t)| * Real.exp (sigma * t)) :=
    greenKernelExpMoment_translated_integrable
      (c := c) (lam := lam) hlam hsigma0 hsigma
  let D : ℝ := C * Real.exp (sigma * (x - aL))
  have hbound_int :
      Integrable (fun t =>
        |greenKernel c lam (-t)| *
          (C * Real.exp (sigma * (x + t - aL)))) := by
    have hconst_int : Integrable
        (fun t => (|greenKernel c lam (-t)| * Real.exp (sigma * t)) * D) :=
      hmoment_int.mul_const D
    refine hconst_int.congr ?_
    exact Eventually.of_forall fun t => by
      dsimp [D]
      have hexp :
          Real.exp (sigma * (x + t - aL)) =
            Real.exp (sigma * t) * Real.exp (sigma * (x - aL)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hexp]
      ring
  have hpoint :
      ∀ t,
        |F t| ≤
          |greenKernel c lam (-t)| *
            (C * Real.exp (sigma * (x + t - aL))) := by
    intro t
    dsimp [F]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hRrate (x + t)) (abs_nonneg _)
  have hint_le :
      (∫ t, |F t|) ≤
        ∫ t, |greenKernel c lam (-t)| *
          (C * Real.exp (sigma * (x + t - aL))) := by
    exact MeasureTheory.integral_mono hFint.norm hbound_int hpoint
  have hbound_eval :
      (∫ t, |greenKernel c lam (-t)| *
          (C * Real.exp (sigma * (x + t - aL))))
        = greenKernelExpMoment c lam sigma * C *
            Real.exp (sigma * (x - aL)) := by
    let D : ℝ := C * Real.exp (sigma * (x - aL))
    rw [show (fun t : ℝ => |greenKernel c lam (-t)| *
          (C * Real.exp (sigma * (x + t - aL))))
        = fun t : ℝ =>
          (|greenKernel c lam (-t)| * Real.exp (sigma * t)) * D by
          funext t
          dsimp [D]
          have hexp :
              Real.exp (sigma * (x + t - aL)) =
                Real.exp (sigma * t) * Real.exp (sigma * (x - aL)) := by
            rw [← Real.exp_add]
            congr 1
            ring
          rw [hexp]
          ring]
    rw [MeasureTheory.integral_mul_const]
    rw [greenKernelExpMoment_translated_integral_eq
      (c := c) (lam := lam) hlam hsigma0 hsigma]
    ring
  calc
    |greenConv c lam R x - ell * lam⁻¹|
        = |(∫ t, greenKernel c lam (-t) * R (x + t)) -
            ∫ t, greenKernel c lam (-t) * ell| := by
          rw [hrepr, hconst]
    _ = |∫ t, F t| := by
          rw [← integral_sub hFx hFc]
          congr 1
          apply integral_congr_ae
          exact Eventually.of_forall fun t => by
            dsimp [F]
            ring
    _ ≤ ∫ t, |F t| := by
          simpa [F, Real.norm_eq_abs] using
            (norm_integral_le_integral_norm (μ := volume) F)
    _ ≤ ∫ t, |greenKernel c lam (-t)| *
          (C * Real.exp (sigma * (x + t - aL))) := hint_le
    _ = greenKernelExpMoment c lam sigma * C *
          Real.exp (sigma * (x - aL)) := hbound_eval
    _ = (greenKernelExpMoment c lam sigma * C) *
          Real.exp (sigma * (x - aL)) := by ring

theorem greenConvDeriv_expLeftRate
    (hlam : 0 < lam) {sigma aL C ell B : ℝ} {R : ℝ → ℝ}
    (hsigma0 : 0 ≤ sigma)
    (hsigma : sigma < greenRootPlus c lam)
    (hRcont : Continuous R) (hRbound : ∀ y, |R y| ≤ B)
    (hRrate : ExpLeftRate sigma aL C R ell) :
    ExpLeftRate sigma aL (greenKernelDerivExpMoment c lam sigma * C)
      (greenConvDeriv c lam R) 0 := by
  intro x
  have hKsigned : Integrable (fun t => greenKernelDeriv c lam (-t)) :=
    (greenKernelDeriv_integrable_signed_for_leftTail
      (c := c) (lam := lam) hlam).comp_neg
  have hRx_meas : AEStronglyMeasurable (fun t : ℝ => R (x + t)) volume :=
    (hRcont.comp (continuous_const.add continuous_id)).aestronglyMeasurable
  have hFx : Integrable (fun t => greenKernelDeriv c lam (-t) * R (x + t)) :=
    hKsigned.mul_bdd hRx_meas
      (Eventually.of_forall fun t => by
        simpa [Real.norm_eq_abs] using hRbound (x + t))
  have hFc : Integrable (fun t => greenKernelDeriv c lam (-t) * ell) :=
    hKsigned.mul_const ell
  have hrepr :
      greenConvDeriv c lam R x =
        ∫ t, greenKernelDeriv c lam (-t) * R (x + t) :=
    greenConvDeriv_eq_translated_integral_of_bounded_for_leftTail
      (c := c) (lam := lam) hlam hRcont hRbound x
  have hconst :
      (∫ t, greenKernelDeriv c lam (-t) * ell) = 0 := by
    rw [show (fun t : ℝ => greenKernelDeriv c lam (-t) * ell)
        = fun t : ℝ => ell * greenKernelDeriv c lam (-t) by
          funext t
          ring]
    rw [MeasureTheory.integral_const_mul]
    rw [integral_neg_eq_self (greenKernelDeriv c lam) volume]
    rw [greenKernelDeriv_integral_eq_zero_for_leftTail
      (c := c) (lam := lam) hlam]
    ring
  let F : ℝ → ℝ := fun t => greenKernelDeriv c lam (-t) * (R (x + t) - ell)
  have hFint : Integrable F := by
    have hdiff := hFx.sub hFc
    refine hdiff.congr ?_
    exact Eventually.of_forall fun t => by
      dsimp [F]
      ring
  have hmoment_int :
      Integrable
        (fun t => |greenKernelDeriv c lam (-t)| * Real.exp (sigma * t)) :=
    greenKernelDerivExpMoment_translated_integrable
      (c := c) (lam := lam) hlam hsigma0 hsigma
  let D : ℝ := C * Real.exp (sigma * (x - aL))
  have hbound_int :
      Integrable (fun t =>
        |greenKernelDeriv c lam (-t)| *
          (C * Real.exp (sigma * (x + t - aL)))) := by
    have hconst_int : Integrable
        (fun t => (|greenKernelDeriv c lam (-t)| * Real.exp (sigma * t)) * D) :=
      hmoment_int.mul_const D
    refine hconst_int.congr ?_
    exact Eventually.of_forall fun t => by
      dsimp [D]
      have hexp :
          Real.exp (sigma * (x + t - aL)) =
            Real.exp (sigma * t) * Real.exp (sigma * (x - aL)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hexp]
      ring
  have hpoint :
      ∀ t,
        |F t| ≤
          |greenKernelDeriv c lam (-t)| *
            (C * Real.exp (sigma * (x + t - aL))) := by
    intro t
    dsimp [F]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hRrate (x + t)) (abs_nonneg _)
  have hint_le :
      (∫ t, |F t|) ≤
        ∫ t, |greenKernelDeriv c lam (-t)| *
          (C * Real.exp (sigma * (x + t - aL))) := by
    exact MeasureTheory.integral_mono hFint.norm hbound_int hpoint
  have hbound_eval :
      (∫ t, |greenKernelDeriv c lam (-t)| *
          (C * Real.exp (sigma * (x + t - aL))))
        = greenKernelDerivExpMoment c lam sigma * C *
            Real.exp (sigma * (x - aL)) := by
    let D : ℝ := C * Real.exp (sigma * (x - aL))
    rw [show (fun t : ℝ => |greenKernelDeriv c lam (-t)| *
          (C * Real.exp (sigma * (x + t - aL))))
        = fun t : ℝ =>
          (|greenKernelDeriv c lam (-t)| * Real.exp (sigma * t)) * D by
          funext t
          dsimp [D]
          have hexp :
              Real.exp (sigma * (x + t - aL)) =
                Real.exp (sigma * t) * Real.exp (sigma * (x - aL)) := by
            rw [← Real.exp_add]
            congr 1
            ring
          rw [hexp]
          ring]
    rw [MeasureTheory.integral_mul_const]
    rw [greenKernelDerivExpMoment_translated_integral_eq
      (c := c) (lam := lam) hlam hsigma0 hsigma]
    ring
  calc
    |greenConvDeriv c lam R x - 0|
        = |(∫ t, greenKernelDeriv c lam (-t) * R (x + t)) -
            ∫ t, greenKernelDeriv c lam (-t) * ell| := by
          rw [hrepr, hconst, sub_zero]
    _ = |∫ t, F t| := by
          rw [← integral_sub hFx hFc]
          congr 1
          apply integral_congr_ae
          exact Eventually.of_forall fun t => by
            dsimp [F]
            ring
    _ ≤ ∫ t, |F t| := by
          simpa [F, Real.norm_eq_abs] using
            (norm_integral_le_integral_norm (μ := volume) F)
    _ ≤ ∫ t, |greenKernelDeriv c lam (-t)| *
          (C * Real.exp (sigma * (x + t - aL))) := hint_le
    _ = greenKernelDerivExpMoment c lam sigma * C *
          Real.exp (sigma * (x - aL)) := hbound_eval
    _ = (greenKernelDerivExpMoment c lam sigma * C) *
          Real.exp (sigma * (x - aL)) := by ring

/-- Pointwise continuity of the Green convolution under locally uniform source
convergence and a shared uniform bound. -/
theorem paperGreenConv_tendsto_of_source_locallyUniform_of_uniform_bound
    {c lam : ℝ} (hlam : 0 < lam) {Rs : ℕ → ℝ → ℝ} {R : ℝ → ℝ} {B : ℝ}
    (hRs_cont : ∀ n, Continuous (Rs n))
    (hR_cont : Continuous R)
    (hRs_bound : ∀ n y, |Rs n y| ≤ B)
    (hR_bound : ∀ y, |R y| ≤ B)
    (hRs_lim : LocallyUniformConverges Rs R) :
    ∀ x, Tendsto (fun n : ℕ => greenConv c lam (Rs n) x) atTop
      (𝓝 (greenConv c lam R x)) := by
  intro x
  let F : ℕ → ℝ → ℝ := fun n t => greenKernel c lam (-t) * Rs n (x + t)
  let G : ℝ → ℝ := fun t => greenKernel c lam (-t) * R (x + t)
  let bound : ℝ → ℝ := fun t => |greenKernel c lam (-t)| * B
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
    exact (hRs_lim.tendsto_at (x + t)).const_mul (greenKernel c lam (-t))
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

/-- Pointwise continuity of the differentiated Green convolution under locally
uniform source convergence and a shared uniform bound. -/
theorem paperGreenConvDeriv_tendsto_of_source_locallyUniform_of_uniform_bound
    {c lam : ℝ} (hlam : 0 < lam) {Rs : ℕ → ℝ → ℝ} {R : ℝ → ℝ} {B : ℝ}
    (hRs_cont : ∀ n, Continuous (Rs n))
    (hR_cont : Continuous R)
    (hRs_bound : ∀ n y, |Rs n y| ≤ B)
    (hR_bound : ∀ y, |R y| ≤ B)
    (hRs_lim : LocallyUniformConverges Rs R) :
    ∀ x, Tendsto (fun n : ℕ => greenConvDeriv c lam (Rs n) x) atTop
      (𝓝 (greenConvDeriv c lam R x)) := by
  intro x
  let F : ℕ → ℝ → ℝ := fun n t => greenKernelDeriv c lam (-t) * Rs n (x + t)
  let G : ℝ → ℝ := fun t => greenKernelDeriv c lam (-t) * R (x + t)
  let bound : ℝ → ℝ := fun t => |greenKernelDeriv c lam (-t)| * B
  have hbound_int : Integrable bound := by
    have hK : Integrable (fun t => |greenKernelDeriv c lam (-t)|) :=
      (greenKernelDeriv_integrable (c := c) hlam).comp_neg
    simpa [bound] using hK.mul_const B
  have hK_meas :
      AEStronglyMeasurable (fun t : ℝ => greenKernelDeriv c lam (-t)) volume :=
    ((greenKernelDeriv_measurable_for_leftTail (c := c) (lam := lam)).comp
      measurable_neg).aestronglyMeasurable
  have hF_meas :
      ∀ᶠ n : ℕ in atTop, AEStronglyMeasurable (F n) volume := by
    refine Eventually.of_forall ?_
    intro n
    exact hK_meas.mul
      ((hRs_cont n).comp (continuous_const.add continuous_id)).aestronglyMeasurable
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
    exact (hRs_lim.tendsto_at (x + t)).const_mul (greenKernelDeriv c lam (-t))
  have hInt_tendsto :
      Tendsto (fun n : ℕ => ∫ t, F n t) atTop (𝓝 (∫ t, G t)) :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (l := atTop) (F := F) (f := G)
      bound hF_meas h_bound hbound_int h_lim
  have hseq :
      (fun n : ℕ => ∫ t, F n t)
        = fun n : ℕ => greenConvDeriv c lam (Rs n) x := by
    funext n
    exact (greenConvDeriv_eq_translated_integral_of_bounded_for_leftTail
      (c := c) (lam := lam) hlam (hRs_cont n) (hRs_bound n) x).symm
  have htarget : (∫ t, G t) = greenConvDeriv c lam R x := by
    exact (greenConvDeriv_eq_translated_integral_of_bounded_for_leftTail
      (c := c) (lam := lam) hlam hR_cont hR_bound x).symm
  simpa [hseq, htarget] using hInt_tendsto

/-- Spatial continuity of the truncated fixed-source map from a continuous
weighted source and the frozen-field continuity data. -/
theorem paperFixedSourceMap_continuous_of_sourceBox
    (p : CMParams) {c lam M κ β B H : ℝ} {ω : ℝ → ℝ} {u Z R : ℝ → ℝ}
    (hlam : 0 < lam) (hB : 0 ≤ B)
    (hZ : Continuous Z)
    (hV : Continuous (frozenElliptic p u))
    (hVderiv : Continuous (deriv (frozenElliptic p u)))
    (hR : PaperWeightedHolderSourceBox κ M β B H ω R) :
    Continuous (paperFixedSourceMap p c lam M κ u Z R) := by
  have hR_const : ∀ y, |R y| ≤ B * M := by
    intro y
    calc
      |R y| ≤ B * upperBarrier κ M y := hR.bound y
      _ ≤ B * M :=
        mul_le_mul_of_nonneg_left (upperBarrier_le_M κ M y) hB
  have hHi : ∀ t,
      IntegrableOn (gWeight (greenRootPlus c lam) R) (Ioi t) :=
    fun t => gWeight_integrableOn_Ioi_of_bounded
      (greenRootPlus_pos (c := c) hlam) hR.cont hR_const t
  have hLo : ∀ t,
      IntegrableOn (gWeight (greenRootMinus c lam) R) (Iic t) :=
    fun t => gWeight_integrableOn_Iic_of_bounded
      (greenRootMinus_neg (c := c) hlam) hR.cont hR_const t
  have hW2 : ContDiff ℝ 2 (fun x => greenConv c lam R x) :=
    greenConv_contDiff_two hR.cont hHi hLo
  have hW : Continuous (fun x => greenConv c lam R x) :=
    hW2.continuous
  have hWderiv : Continuous (deriv (fun x => greenConv c lam R x)) :=
    hW2.continuous_deriv (by norm_num)
  have hΘ : Continuous
      (fun x => paperWeightedClamp κ M (fun y => greenConv c lam R y) x) := by
    unfold paperWeightedClamp clampIcc
    exact continuous_const.max ((upperBarrier_continuous κ M).min hW)
  have hm1 : 0 ≤ p.m - 1 := by linarith [p.hm]
  have hα : 0 ≤ p.α := by linarith [p.hα]
  have hmg1 : 0 ≤ p.m + p.γ - 1 := by linarith [p.hm, p.hγ]
  have hΘm1 : Continuous
      (fun x => (paperWeightedClamp κ M
        (fun y => greenConv c lam R y) x) ^ (p.m - 1)) :=
    hΘ.rpow_const (fun _ => Or.inr hm1)
  have hΘα : Continuous
      (fun x => (paperWeightedClamp κ M
        (fun y => greenConv c lam R y) x) ^ p.α) :=
    hΘ.rpow_const (fun _ => Or.inr hα)
  have hΘmg1 : Continuous
      (fun x => (paperWeightedClamp κ M
        (fun y => greenConv c lam R y) x) ^ (p.m + p.γ - 1)) :=
    hΘ.rpow_const (fun _ => Or.inr hmg1)
  have hchem : Continuous (fun x =>
      -p.χ * p.m *
        (paperWeightedClamp κ M (fun y => greenConv c lam R y) x) ^ (p.m - 1) *
        deriv (frozenElliptic p u) x *
          deriv (fun y => greenConv c lam R y) x) :=
    (((continuous_const.mul hΘm1).mul hVderiv).mul hWderiv)
  have hinner : Continuous (fun x =>
      1 - p.χ *
          (paperWeightedClamp κ M
            (fun y => greenConv c lam R y) x) ^ (p.m - 1) *
          frozenElliptic p u x
        - ((paperWeightedClamp κ M
              (fun y => greenConv c lam R y) x) ^ p.α
          - p.χ *
              (paperWeightedClamp κ M
                (fun y => greenConv c lam R y) x) ^ (p.m + p.γ - 1))) :=
    (continuous_const.sub ((continuous_const.mul hΘm1).mul hV)).sub
      (hΘα.sub (continuous_const.mul hΘmg1))
  have htotal : Continuous (fun x =>
      (-p.χ * p.m *
          (paperWeightedClamp κ M
            (fun y => greenConv c lam R y) x) ^ (p.m - 1) *
          deriv (frozenElliptic p u) x *
            deriv (fun y => greenConv c lam R y) x
        + paperWeightedClamp κ M (fun y => greenConv c lam R y) x *
            (1 - p.χ *
              (paperWeightedClamp κ M
                (fun y => greenConv c lam R y) x) ^ (p.m - 1) *
              frozenElliptic p u x
              - ((paperWeightedClamp κ M
                    (fun y => greenConv c lam R y) x) ^ p.α
                - p.χ *
                    (paperWeightedClamp κ M
                      (fun y => greenConv c lam R y) x) ^ (p.m + p.γ - 1))))
        + lam * Z x) :=
    (hchem.add (hΘ.mul hinner)).add (continuous_const.mul hZ)
  unfold paperFixedSourceMap paperStepSource_truncated
  dsimp only
  convert htotal using 1

/-- Trap-specialized continuity field for the truncated fixed-source map. -/
theorem paperFixedSourceMap_continuous_of_trap_sourceBox
    (p : CMParams) {c lam M κ β B H : ℝ} {ω : ℝ → ℝ} {u Z R : ℝ → ℝ}
    (hlam : 0 < lam)
    (hu : InWaveTrapSet κ M u)
    (hZ : Continuous Z)
    (hB : 0 ≤ B)
    (hR : PaperWeightedHolderSourceBox κ M β B H ω R) :
    Continuous (paperFixedSourceMap p c lam M κ u Z R) := by
  exact paperFixedSourceMap_continuous_of_sourceBox
    (p := p) (c := c) (lam := lam) (M := M) (κ := κ)
    (β := β) (B := B) (H := H) (ω := ω)
    (u := u) (Z := Z) (R := R) hlam hB hZ
    (frozenElliptic_continuous p hu.cunif_bdd hu.nonneg)
    (frozenElliptic_deriv_continuous p hu.cunif_bdd hu.nonneg)
    hR

/-- Pointwise continuous dependence of the truncated fixed-source map on the
source profile, for locally uniform source convergence inside one source box. -/
theorem paperFixedSourceMap_tendsto_of_source_locallyUniform_sourceBox
    (p : CMParams) {c lam M κ β B H : ℝ} {ω : ℝ → ℝ}
    {u Z : ℝ → ℝ} {Rs : ℕ → ℝ → ℝ} {R : ℝ → ℝ}
    (hlam : 0 < lam) (hBnn : 0 ≤ B)
    (hRs : ∀ n, PaperWeightedHolderSourceBox κ M β B H ω (Rs n))
    (hR : PaperWeightedHolderSourceBox κ M β B H ω R)
    (hLU : LocallyUniformConverges Rs R) :
    ∀ x, Tendsto
      (fun n : ℕ => paperFixedSourceMap p c lam M κ u Z (Rs n) x) atTop
        (𝓝 (paperFixedSourceMap p c lam M κ u Z R x)) := by
  intro x
  have hRs_bound : ∀ n y, |Rs n y| ≤ B * M := by
    intro n y
    exact (hRs n).abs_le_const (B := B) hBnn y
  have hR_bound : ∀ y, |R y| ≤ B * M :=
    hR.abs_le_const (B := B) hBnn
  have hW :
      Tendsto (fun n : ℕ => greenConv c lam (Rs n) x) atTop
        (𝓝 (greenConv c lam R x)) :=
    paperGreenConv_tendsto_of_source_locallyUniform_of_uniform_bound
      (c := c) (lam := lam) hlam
      (fun n => (hRs n).cont) hR.cont hRs_bound hR_bound hLU x
  have hWd :
      Tendsto (fun n : ℕ => greenConvDeriv c lam (Rs n) x) atTop
        (𝓝 (greenConvDeriv c lam R x)) :=
    paperGreenConvDeriv_tendsto_of_source_locallyUniform_of_uniform_bound
      (c := c) (lam := lam) hlam
      (fun n => (hRs n).cont) hR.cont hRs_bound hR_bound hLU x
  have hderiv_seq :
      (fun n : ℕ => deriv (fun y => greenConv c lam (Rs n) y) x) =
        fun n : ℕ => greenConvDeriv c lam (Rs n) x := by
    funext n
    exact (greenConv_hasDerivAt
      (c := c) (lam := lam) (hRs n).cont
      ((hRs n).gWeight_Ioi (c := c) (lam := lam) hlam hBnn)
      ((hRs n).gWeight_Iic (c := c) (lam := lam) hlam hBnn) x).deriv
  have hderiv_target :
      deriv (fun y => greenConv c lam R y) x = greenConvDeriv c lam R x :=
    (greenConv_hasDerivAt
      (c := c) (lam := lam) hR.cont
      (hR.gWeight_Ioi (c := c) (lam := lam) hlam hBnn)
      (hR.gWeight_Iic (c := c) (lam := lam) hlam hBnn) x).deriv
  let Θs : ℕ → ℝ := fun n =>
    paperWeightedClamp κ M (fun y => greenConv c lam (Rs n) y) x
  let Θ : ℝ := paperWeightedClamp κ M (fun y => greenConv c lam R y) x
  have hΘ : Tendsto Θs atTop (𝓝 Θ) := by
    unfold Θs Θ paperWeightedClamp
    exact
      ((clampIcc_lipschitz (upperBarrier κ M x)).continuous.tendsto
        (greenConv c lam R x)).comp hW
  have hm1 : 0 ≤ p.m - 1 := by linarith [p.hm]
  have hα : 0 ≤ p.α := by linarith [p.hα]
  have hmg1 : 0 ≤ p.m + p.γ - 1 := by linarith [p.hm, p.hγ]
  have hΘm1 : Tendsto (fun n : ℕ => (Θs n) ^ (p.m - 1)) atTop
      (𝓝 (Θ ^ (p.m - 1))) :=
    hΘ.rpow_const (Or.inr hm1)
  have hΘα : Tendsto (fun n : ℕ => (Θs n) ^ p.α) atTop
      (𝓝 (Θ ^ p.α)) :=
    hΘ.rpow_const (Or.inr hα)
  have hΘmg1 : Tendsto (fun n : ℕ => (Θs n) ^ (p.m + p.γ - 1)) atTop
      (𝓝 (Θ ^ (p.m + p.γ - 1))) :=
    hΘ.rpow_const (Or.inr hmg1)
  have hderiv_tendsto :
      Tendsto (fun n : ℕ => deriv (fun y => greenConv c lam (Rs n) y) x) atTop
        (𝓝 (deriv (fun y => greenConv c lam R y) x)) := by
    simpa [hderiv_seq, hderiv_target] using hWd
  have hchem :
      Tendsto
        (fun n : ℕ =>
          -p.χ * p.m * (Θs n) ^ (p.m - 1) *
            deriv (frozenElliptic p u) x *
              deriv (fun y => greenConv c lam (Rs n) y) x)
        atTop
        (𝓝
          (-p.χ * p.m * Θ ^ (p.m - 1) *
            deriv (frozenElliptic p u) x *
              deriv (fun y => greenConv c lam R y) x)) := by
    have hprod :=
      (hΘm1.const_mul (-p.χ * p.m * deriv (frozenElliptic p u) x)).mul
        hderiv_tendsto
    simpa [mul_assoc, mul_left_comm, mul_comm] using hprod
  have hinner :
      Tendsto
        (fun n : ℕ =>
          1 - p.χ * (Θs n) ^ (p.m - 1) * frozenElliptic p u x
            - ((Θs n) ^ p.α - p.χ * (Θs n) ^ (p.m + p.γ - 1)))
        atTop
        (𝓝
          (1 - p.χ * Θ ^ (p.m - 1) * frozenElliptic p u x
            - (Θ ^ p.α - p.χ * Θ ^ (p.m + p.γ - 1)))) := by
    have hone :
        Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (1 : ℝ)) :=
      tendsto_const_nhds
    have hterm1 :
        Tendsto
          (fun n : ℕ =>
            p.χ * (Θs n) ^ (p.m - 1) * frozenElliptic p u x)
          atTop
          (𝓝 (p.χ * Θ ^ (p.m - 1) * frozenElliptic p u x)) := by
      have hraw := hΘm1.const_mul (p.χ * frozenElliptic p u x)
      simpa [mul_assoc, mul_left_comm, mul_comm] using hraw
    have hterm2 :
        Tendsto
          (fun n : ℕ => p.χ * (Θs n) ^ (p.m + p.γ - 1))
          atTop
          (𝓝 (p.χ * Θ ^ (p.m + p.γ - 1))) :=
      hΘmg1.const_mul p.χ
    have hparen :
        Tendsto
          (fun n : ℕ =>
            (Θs n) ^ p.α - p.χ * (Θs n) ^ (p.m + p.γ - 1))
          atTop
          (𝓝 (Θ ^ p.α - p.χ * Θ ^ (p.m + p.γ - 1))) :=
      hΘα.sub hterm2
    have hraw := (hone.sub hterm1).sub hparen
    simpa [mul_assoc, mul_left_comm, mul_comm] using hraw
  have hreact :
      Tendsto
        (fun n : ℕ =>
          Θs n *
            (1 - p.χ * (Θs n) ^ (p.m - 1) * frozenElliptic p u x
              - ((Θs n) ^ p.α - p.χ * (Θs n) ^ (p.m + p.γ - 1))))
        atTop
        (𝓝
          (Θ *
            (1 - p.χ * Θ ^ (p.m - 1) * frozenElliptic p u x
              - (Θ ^ p.α - p.χ * Θ ^ (p.m + p.γ - 1))))) :=
    hΘ.mul hinner
  have hlin :
      Tendsto (fun _ : ℕ => lam * Z x) atTop (𝓝 (lam * Z x)) :=
    tendsto_const_nhds
  have htotal := (hchem.add hreact).add hlin
  simpa [paperFixedSourceMap, paperStepSource_truncated,
    paperStepTruncatedNonlinearity, Θs, Θ, hderiv_seq, hderiv_target,
    mul_assoc, mul_left_comm, mul_comm] using htotal

/-- Weighted source-box bound for the truncated fixed-source map.  The only
non-box analytic inputs are the standard frozen-field bounds and the scalar
large-`B` inequality. -/
theorem paperFixedSourceMap_bound_of_sourceBox
    (p : CMParams) {c lam M κ β B H BV BVd : ℝ} {ω : ℝ → ℝ} {u Z R : ℝ → ℝ}
    (hlam : 0 < lam)
    (hrpκ : κ < greenRootPlus c lam)
    (hrmκ : κ < -greenRootMinus c lam)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) (hBnn : 0 ≤ B)
    (hBVnn : 0 ≤ BV) (hBVdnn : 0 ≤ BVd)
    (hZ0 : ∀ x, 0 ≤ Z x)
    (hZB : ∀ x, Z x ≤ upperBarrier κ M x)
    (hVbound : ∀ x, |frozenElliptic p u x| ≤ BV)
    (hVderiv_bound : ∀ x, |deriv (frozenElliptic p u) x| ≤ BVd)
    (hscalar :
      |(-p.χ * p.m)| * M ^ (p.m - 1) * BVd *
            greenWeightedMass1 c lam κ * B
        + (1 + |p.χ| * M ^ (p.m - 1) * BV
            + M ^ p.α + |p.χ| * M ^ (p.m + p.γ - 1))
        + lam ≤ B)
    (hR : PaperWeightedHolderSourceBox κ M β B H ω R) :
    ∀ x, |paperFixedSourceMap p c lam M κ u Z R x| ≤
      B * upperBarrier κ M x := by
  intro x
  let W : ℝ → ℝ := fun y => greenConv c lam R y
  let Θ : ℝ := paperWeightedClamp κ M W x
  let Ux : ℝ := upperBarrier κ M x
  have hUx0 : 0 ≤ Ux := by
    dsimp [Ux]
    exact upperBarrier_nonneg hM x
  have hΘmem :
      Θ ∈ Set.Icc (0 : ℝ) Ux := by
    dsimp [Θ, W, Ux]
    exact paperWeightedClamp_mem_Icc (κ := κ) (M := M)
      (W := fun y => greenConv c lam R y) hM x
  have hΘabs : |Θ| ≤ Ux := by
    rw [abs_of_nonneg hΘmem.1]
    exact hΘmem.2
  have hm1_nonneg : 0 ≤ p.m - 1 := by linarith [p.hm]
  have hα_nonneg : 0 ≤ p.α := by linarith [p.hα]
  have hmg1_nonneg : 0 ≤ p.m + p.γ - 1 := by linarith [p.hm, p.hγ]
  have hΘm1 :
      |Θ ^ (p.m - 1)| ≤ M ^ (p.m - 1) := by
    dsimp [Θ, W]
    exact paperWeightedClamp_rpow_abs_le_M
      (κ := κ) (M := M) (a := p.m - 1)
      (W := fun y => greenConv c lam R y) hM hm1_nonneg x
  have hΘα :
      |Θ ^ p.α| ≤ M ^ p.α := by
    dsimp [Θ, W]
    exact paperWeightedClamp_rpow_abs_le_M
      (κ := κ) (M := M) (a := p.α)
      (W := fun y => greenConv c lam R y) hM hα_nonneg x
  have hΘmg1 :
      |Θ ^ (p.m + p.γ - 1)| ≤ M ^ (p.m + p.γ - 1) := by
    dsimp [Θ, W]
    exact paperWeightedClamp_rpow_abs_le_M
      (κ := κ) (M := M) (a := p.m + p.γ - 1)
      (W := fun y => greenConv c lam R y) hM hmg1_nonneg x
  have hWderiv :
      |deriv W x| ≤
        greenWeightedMass1 c lam κ * (B * Ux) := by
    dsimp [W, Ux]
    exact PaperWeightedHolderSourceBox.deriv_greenConv_abs_le
      (c := c) (lam := lam) (β := β) (Hbox := H) (ω := ω)
      hlam hrpκ hrmκ hκ hM hBnn hR x
  have hmass1_nonneg : 0 ≤ greenWeightedMass1 c lam κ :=
    greenWeightedMass1_nonneg (c := c) (lam := lam) hlam hrpκ hrmκ
  have hM_m1_nonneg : 0 ≤ M ^ (p.m - 1) :=
    Real.rpow_nonneg hM (p.m - 1)
  have hM_α_nonneg : 0 ≤ M ^ p.α :=
    Real.rpow_nonneg hM p.α
  have hM_mg1_nonneg : 0 ≤ M ^ (p.m + p.γ - 1) :=
    Real.rpow_nonneg hM (p.m + p.γ - 1)
  have hderivCoeff_nonneg :
      0 ≤ |(-p.χ * p.m)| * M ^ (p.m - 1) * BVd *
          greenWeightedMass1 c lam κ * B := by
    positivity
  have hinnerCoeff_nonneg :
      0 ≤ 1 + |p.χ| * M ^ (p.m - 1) * BV
          + M ^ p.α + |p.χ| * M ^ (p.m + p.γ - 1) := by
    positivity
  have hlinearCoeff_nonneg : 0 ≤ lam := hlam.le
  have hchem :
      |(-p.χ * p.m) * Θ ^ (p.m - 1) *
          deriv (frozenElliptic p u) x * deriv W x|
        ≤ (|(-p.χ * p.m)| * M ^ (p.m - 1) * BVd *
            greenWeightedMass1 c lam κ * B) * Ux := by
    calc
      |(-p.χ * p.m) * Θ ^ (p.m - 1) *
          deriv (frozenElliptic p u) x * deriv W x|
          = |(-p.χ * p.m)| * |Θ ^ (p.m - 1)| *
              |deriv (frozenElliptic p u) x| * |deriv W x| := by
            rw [abs_mul, abs_mul, abs_mul]
      _ ≤ |(-p.χ * p.m)| * M ^ (p.m - 1) *
              BVd * (greenWeightedMass1 c lam κ * (B * Ux)) := by
            gcongr
            exact hVderiv_bound x
      _ = (|(-p.χ * p.m)| * M ^ (p.m - 1) * BVd *
              greenWeightedMass1 c lam κ * B) * Ux := by
            ring
  have hχΘm1V :
      |p.χ * Θ ^ (p.m - 1) * frozenElliptic p u x|
        ≤ |p.χ| * M ^ (p.m - 1) * BV := by
    calc
      |p.χ * Θ ^ (p.m - 1) * frozenElliptic p u x|
          = |p.χ| * |Θ ^ (p.m - 1)| * |frozenElliptic p u x| := by
            rw [abs_mul, abs_mul]
      _ ≤ |p.χ| * M ^ (p.m - 1) * BV := by
            gcongr
            exact hVbound x
  have hχΘmg1 :
      |p.χ * Θ ^ (p.m + p.γ - 1)|
        ≤ |p.χ| * M ^ (p.m + p.γ - 1) := by
    calc
      |p.χ * Θ ^ (p.m + p.γ - 1)|
          = |p.χ| * |Θ ^ (p.m + p.γ - 1)| := by
            rw [abs_mul]
      _ ≤ |p.χ| * M ^ (p.m + p.γ - 1) := by
            gcongr
  have hinner :
      |1 - p.χ * Θ ^ (p.m - 1) * frozenElliptic p u x
          - (Θ ^ p.α - p.χ * Θ ^ (p.m + p.γ - 1))|
        ≤ 1 + |p.χ| * M ^ (p.m - 1) * BV
          + M ^ p.α + |p.χ| * M ^ (p.m + p.γ - 1) := by
    let A : ℝ := p.χ * Θ ^ (p.m - 1) * frozenElliptic p u x
    let Pα : ℝ := Θ ^ p.α
    let Cγ : ℝ := p.χ * Θ ^ (p.m + p.γ - 1)
    have hrewrite :
        1 - p.χ * Θ ^ (p.m - 1) * frozenElliptic p u x
            - (Θ ^ p.α - p.χ * Θ ^ (p.m + p.γ - 1))
          = (1 + -A + -Pα) + Cγ := by
      dsimp [A, Pα, Cγ]
      ring
    rw [hrewrite]
    have htri₁ :
        |(1 + -A + -Pα) + Cγ| ≤ |1 + -A + -Pα| + |Cγ| :=
      abs_add_le _ _
    have htri₂ :
        |1 + -A + -Pα| ≤ |1 + -A| + |Pα| := by
      simpa using abs_add_le (1 + -A) (-Pα)
    have htri₃ : |1 + -A| ≤ |(1 : ℝ)| + |A| := by
      simpa using abs_add_le (1 : ℝ) (-A)
    have htri :
        |(1 + -A + -Pα) + Cγ| ≤ |(1 : ℝ)| + |A| + |Pα| + |Cγ| := by
      linarith
    have hA : |A| ≤ |p.χ| * M ^ (p.m - 1) * BV := by
      dsimp [A]
      exact hχΘm1V
    have hP : |Pα| ≤ M ^ p.α := by
      dsimp [Pα]
      exact hΘα
    have hC : |Cγ| ≤ |p.χ| * M ^ (p.m + p.γ - 1) := by
      dsimp [Cγ]
      exact hχΘmg1
    have h1 : |(1 : ℝ)| = 1 := abs_of_nonneg zero_le_one
    linarith
  have hreact :
      |Θ *
          (1 - p.χ * Θ ^ (p.m - 1) * frozenElliptic p u x
            - (Θ ^ p.α - p.χ * Θ ^ (p.m + p.γ - 1)))|
        ≤ (1 + |p.χ| * M ^ (p.m - 1) * BV
          + M ^ p.α + |p.χ| * M ^ (p.m + p.γ - 1)) * Ux := by
    calc
      |Θ *
          (1 - p.χ * Θ ^ (p.m - 1) * frozenElliptic p u x
            - (Θ ^ p.α - p.χ * Θ ^ (p.m + p.γ - 1)))|
          = |Θ| *
              |1 - p.χ * Θ ^ (p.m - 1) * frozenElliptic p u x
                - (Θ ^ p.α - p.χ * Θ ^ (p.m + p.γ - 1))| := by
            rw [abs_mul]
      _ ≤ Ux *
            (1 + |p.χ| * M ^ (p.m - 1) * BV
              + M ^ p.α + |p.χ| * M ^ (p.m + p.γ - 1)) := by
            gcongr
      _ = (1 + |p.χ| * M ^ (p.m - 1) * BV
              + M ^ p.α + |p.χ| * M ^ (p.m + p.γ - 1)) * Ux := by
            ring
  have hZabs : |Z x| ≤ Ux := by
    rw [abs_of_nonneg (hZ0 x)]
    exact hZB x
  have hlin :
      |lam * Z x| ≤ lam * Ux := by
    calc
      |lam * Z x| = lam * |Z x| := by
        rw [abs_mul, abs_of_nonneg hlam.le]
      _ ≤ lam * Ux := mul_le_mul_of_nonneg_left hZabs hlam.le
  unfold paperFixedSourceMap paperStepSource_truncated paperStepTruncatedNonlinearity
    paperWeightedClamp
  dsimp only [W, Θ, Ux] at *
  calc
    |(-p.χ * p.m * Θ ^ (p.m - 1) *
          deriv (frozenElliptic p u) x * deriv W x
        + Θ *
          (1 - p.χ * Θ ^ (p.m - 1) * frozenElliptic p u x
            - (Θ ^ p.α - p.χ * Θ ^ (p.m + p.γ - 1)))
        + lam * Z x)|
        ≤ |(-p.χ * p.m) * Θ ^ (p.m - 1) *
              deriv (frozenElliptic p u) x * deriv W x|
            + |Θ *
              (1 - p.χ * Θ ^ (p.m - 1) * frozenElliptic p u x
                - (Θ ^ p.α - p.χ * Θ ^ (p.m + p.γ - 1)))|
            + |lam * Z x| := by
          have htri := abs_add_le
            ((-p.χ * p.m) * Θ ^ (p.m - 1) *
              deriv (frozenElliptic p u) x * deriv W x
              + Θ *
                (1 - p.χ * Θ ^ (p.m - 1) * frozenElliptic p u x
                  - (Θ ^ p.α - p.χ * Θ ^ (p.m + p.γ - 1))))
            (lam * Z x)
          have htri₂ := abs_add_le
            ((-p.χ * p.m) * Θ ^ (p.m - 1) *
              deriv (frozenElliptic p u) x * deriv W x)
            (Θ *
              (1 - p.χ * Θ ^ (p.m - 1) * frozenElliptic p u x
                - (Θ ^ p.α - p.χ * Θ ^ (p.m + p.γ - 1))))
          linarith
    _ ≤ (|(-p.χ * p.m)| * M ^ (p.m - 1) * BVd *
            greenWeightedMass1 c lam κ * B) * Ux
        + (1 + |p.χ| * M ^ (p.m - 1) * BV
            + M ^ p.α + |p.χ| * M ^ (p.m + p.γ - 1)) * Ux
        + lam * Ux := by
          linarith
    _ = (|(-p.χ * p.m)| * M ^ (p.m - 1) * BVd *
            greenWeightedMass1 c lam κ * B
        + (1 + |p.χ| * M ^ (p.m - 1) * BV
            + M ^ p.α + |p.χ| * M ^ (p.m + p.γ - 1))
        + lam) * Ux := by
          ring
    _ ≤ B * Ux := mul_le_mul_of_nonneg_right hscalar hUx0

/-- Paper-step analytic data with the bounded-source Green tails omitted.

The omitted fields are closed by `paperStepAnalytic_of_core`; source existence,
continuity, and boundedness remain explicit data. -/
structure PaperStepAnalyticCore
    (p : CMParams) (c lam M κ Λ : ℝ) (u Z W : ℝ → ℝ) where
  R : ℝ → ℝ
  source_eq : R = paperStepSource p c lam u Z W
  green_repr : W = fun x => greenConv c lam R x
  R_cont : Continuous R
  R_bound_const : ℝ
  R_bound : ∀ y, |R y| ≤ R_bound_const
  R_bound_eq : Λ = 2 * (greenDelta c lam)⁻¹ * R_bound_const

/-- Build the analytic core once the fixed source has been produced.

This is the exact interface between the nonlinear fixed-point step
`R = source(u,Z,greenConv R)` and the Green/resolvent bookkeeping used by the
paper producer. -/
def paperStepAnalyticCore_of_fixed_source
    {p : CMParams} {c lam M κ Λ : ℝ} {u Z R : ℝ → ℝ}
    (hsource : R = paperStepSource p c lam u Z (fun x => greenConv c lam R x))
    (hRcont : Continuous R) (B : ℝ) (hRbound : ∀ y, |R y| ≤ B)
    (hΛ : Λ = 2 * (greenDelta c lam)⁻¹ * B) :
    PaperStepAnalyticCore p c lam M κ Λ u Z (fun x => greenConv c lam R x) :=
  { R := R
    source_eq := hsource
    green_repr := rfl
    R_cont := hRcont
    R_bound_const := B
    R_bound := hRbound
    R_bound_eq := hΛ }

/-- The exact fixed-source payload needed after the nonlinear fixed-point step.

This is deliberately only the nonlinear fixed-source conclusion:
`R = paperStepSource ... (greenConv R)`, plus the continuous bounded source data
needed by `paperStepAnalyticCore_of_fixed_source`.  Barrier and Route-A data are
assembled in `WavePaperRouteA.lean`. -/
structure PaperStepFixedSourceCore
    (p : CMParams) (c lam M κ Λ : ℝ) (u Z : ℝ → ℝ) where
  R : ℝ → ℝ
  source_eq : R = paperStepSource p c lam u Z (fun x => greenConv c lam R x)
  R_cont : Continuous R
  R_bound_const : ℝ
  R_bound : ∀ y, |R y| ≤ R_bound_const
  R_bound_eq : Λ = 2 * (greenDelta c lam)⁻¹ * R_bound_const

namespace PaperStepFixedSourceCore

/-- The Green profile produced by a fixed source. -/
def W
    {p : CMParams} {c lam M κ Λ : ℝ} {u Z : ℝ → ℝ}
    (h : PaperStepFixedSourceCore p c lam M κ Λ u Z) : ℝ → ℝ :=
  fun x => greenConv c lam h.R x

/-- A fixed source immediately gives the analytic core consumed downstream. -/
def analyticCore
    {p : CMParams} {c lam M κ Λ : ℝ} {u Z : ℝ → ℝ}
    (h : PaperStepFixedSourceCore p c lam M κ Λ u Z) :
    PaperStepAnalyticCore p c lam M κ Λ u Z h.W :=
  paperStepAnalyticCore_of_fixed_source
    (p := p) (c := c) (lam := lam) (M := M) (κ := κ) (Λ := Λ)
    (u := u) (Z := Z) (R := h.R)
    h.source_eq h.R_cont h.R_bound_const h.R_bound h.R_bound_eq

end PaperStepFixedSourceCore

/-- Fixed-source existence in the signature required by the current paper
producer interface.  The concrete constructor below obtains it from the
per-step Schauder map `W ↦ greenConv c lam (paperStepSource ... W)`. -/
def PaperStepFixedSourceProvider
    (p : CMParams) (c lam M κ Λ : ℝ) (u : ℝ → ℝ) : Type :=
  ∀ Z : ℝ → ℝ, Continuous Z → Antitone Z → (∀ x, 0 ≤ Z x) →
    (∀ x, Z x ≤ upperBarrier κ M x) →
      PaperStepFixedSourceCore p c lam M κ Λ u Z

/-- The stronger super-solution version matching the frozen Rothe step input.
The current `PaperGreenStepInputRouteACore.produce` does not expose this
precondition, but this is the precise fixed-source existence statement needed
when the old iterate is carried with `frozenWaveOperator p c u Z ≤ 0`. -/
def PaperStepFixedSourceExistsForSuperTrap
    (p : CMParams) (c lam M κ Λ : ℝ) (u : ℝ → ℝ) : Prop :=
  InMonotoneWaveTrapSet κ M u →
  ∀ Z : ℝ → ℝ, Continuous Z → Antitone Z → (∀ x, 0 ≤ Z x) →
    (∀ x, Z x ≤ upperBarrier κ M x) →
    (∀ x, frozenWaveOperator p c u Z x ≤ 0) →
      ∃ R : ℝ → ℝ,
        Continuous R ∧
        (∃ B : ℝ, (∀ y, |R y| ≤ B) ∧
          Λ = 2 * (greenDelta c lam)⁻¹ * B) ∧
        R = paperStepSource p c lam u Z
          (fun x => greenConv c lam R x)

/-- Repackage the super-trap fixed-source existence statement as the concrete
core consumed by the Route-A paper step assembly. -/
def PaperStepFixedSourceCore.of_existsForSuperTrap
    {p : CMParams} {c lam M κ Λ : ℝ} {u Z : ℝ → ℝ}
    (hfixed : PaperStepFixedSourceExistsForSuperTrap p c lam M κ Λ u)
    (hu : InMonotoneWaveTrapSet κ M u)
    (hZc : Continuous Z) (hZa : Antitone Z) (hZ0 : ∀ x, 0 ≤ Z x)
    (hZB : ∀ x, Z x ≤ upperBarrier κ M x)
    (hZsuper : ∀ x, frozenWaveOperator p c u Z x ≤ 0) :
    PaperStepFixedSourceCore p c lam M κ Λ u Z :=
  let hex := hfixed hu Z hZc hZa hZ0 hZB hZsuper
  let R : ℝ → ℝ := Classical.choose hex
  have hRspec :
      Continuous R ∧
        (∃ B : ℝ, (∀ y, |R y| ≤ B) ∧
          Λ = 2 * (greenDelta c lam)⁻¹ * B) ∧
        R = paperStepSource p c lam u Z
          (fun x => greenConv c lam R x) :=
    Classical.choose_spec hex
  let B : ℝ := Classical.choose hRspec.2.1
  have hBspec : (∀ y, |R y| ≤ B) ∧ Λ = 2 * (greenDelta c lam)⁻¹ * B :=
    Classical.choose_spec hRspec.2.1
  { R := R
    source_eq := hRspec.2.2
    R_cont := hRspec.1
    R_bound_const := B
    R_bound := hBspec.1
    R_bound_eq := hBspec.2 }

/-! ## Schauder fixed-source construction

The per-step nonlinear map is the Green-smoothed paper source
`W ↦ greenConv c lam (paperStepSource p c lam u Z W)`.  Its fixed point gives a
fixed source by setting `R = paperStepSource ... W`.  The topological input is
Schauder: continuity plus local-uniform compactness of the image, not a
contraction estimate for the real-power source. -/

/-- The paper per-step Schauder map on profiles. -/
def paperStepSchauderMap
    (p : CMParams) (c lam : ℝ) (u Z W : ℝ → ℝ) : ℝ → ℝ :=
  fun x => greenConv c lam (paperStepSource p c lam u Z W) x

/-- A global derivative bound gives the equicontinuity estimate used in the
Arzelà-Ascoli/Helly compactness step. -/
theorem abs_sub_le_of_deriv_abs_le
    {f : ℝ → ℝ} {A : ℝ}
    (hf : Differentiable ℝ f) (hderiv : ∀ x, |deriv f x| ≤ A) :
    ∀ x y, |f x - f y| ≤ A * |x - y| := by
  intro x y
  have h :=
    Convex.norm_image_sub_le_of_norm_deriv_le
      (𝕜 := ℝ) (G := ℝ) (f := f) (s := Set.univ)
      (x := y) (y := x)
      (fun z _hz => hf z)
      (fun z _hz => by simpa [Real.norm_eq_abs] using hderiv z)
      convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa [Real.norm_eq_abs, abs_sub_comm] using h

/-- Sup bound for a Green convolution from a bounded continuous source. -/
theorem greenConv_abs_le_of_bound
    (hlam : 0 < lam) {H : ℝ → ℝ} {B : ℝ}
    (hH : Continuous H) (hB : ∀ y, |H y| ≤ B) (x : ℝ) :
    |greenConv c lam H x| ≤ lam⁻¹ * B := by
  let Hb : ℝ →ᵇ ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup H hH B
      (fun y => by simpa [Real.norm_eq_abs] using hB y)
  have hraw :
      (∫ y, greenKernel c lam (x - y) * H y) = greenConv c lam H x :=
    greenConv_raw_eq_of_bounded (c := c) (lam := lam) hlam hH hB x
  rw [← hraw]
  have hker :
      |kernelConvVal (greenKernel c lam) Hb x|
        ≤ (∫ z, |greenKernel c lam z|) * ‖Hb‖ :=
    kernelConvVal_abs_le (K := greenKernel c lam)
      (greenKernel_integrable (c := c) hlam) Hb x
  have hB_nonneg : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  have hnorm : ‖Hb‖ ≤ B :=
    (BoundedContinuousFunction.norm_le hB_nonneg).2
      (fun y => by simpa [Real.norm_eq_abs] using hB y)
  have hl1_nonneg : 0 ≤ ∫ z, |greenKernel c lam z| :=
    integral_nonneg fun z => abs_nonneg _
  calc
    |∫ y, greenKernel c lam (x - y) * H y|
        = |kernelConvVal (greenKernel c lam) Hb x| := by rfl
    _ ≤ (∫ z, |greenKernel c lam z|) * ‖Hb‖ := hker
    _ ≤ (∫ z, |greenKernel c lam z|) * B :=
      mul_le_mul_of_nonneg_left hnorm hl1_nonneg
    _ = lam⁻¹ * B := by rw [greenKernel_l1_eq (c := c) hlam]

/-- Derivative bound for the per-step Schauder image from a bounded continuous
paper source. -/
theorem paperStepSchauderMap_deriv_abs_le_of_source_bound
    {p : CMParams} {u Z W : ℝ → ℝ} (hlam : 0 < lam) {B : ℝ}
    (hsrcCont : Continuous (paperStepSource p c lam u Z W))
    (hsrcBound : ∀ y, |paperStepSource p c lam u Z W y| ≤ B) :
    ∀ x, |deriv (paperStepSchauderMap p c lam u Z W) x|
      ≤ 2 * (greenDelta c lam)⁻¹ * B := by
  intro x
  have hHi : ∀ t,
      IntegrableOn
        (gWeight (greenRootPlus c lam) (paperStepSource p c lam u Z W)) (Ioi t) :=
    fun t => gWeight_integrableOn_Ioi_of_bounded
      (greenRootPlus_pos (c := c) hlam) hsrcCont hsrcBound t
  have hLo : ∀ t,
      IntegrableOn
        (gWeight (greenRootMinus c lam) (paperStepSource p c lam u Z W)) (Iic t) :=
    fun t => gWeight_integrableOn_Iic_of_bounded
      (greenRootMinus_neg (c := c) hlam) hsrcCont hsrcBound t
  have hderiv :
      deriv (paperStepSchauderMap p c lam u Z W) x =
        greenConvDeriv c lam (paperStepSource p c lam u Z W) x := by
    unfold paperStepSchauderMap
    exact (greenConv_hasDerivAt
      (c := c) (lam := lam) hsrcCont hHi hLo x).deriv
  rw [hderiv]
  exact greenConvDeriv_abs_le
    (c := c) (lam := lam) hlam hsrcBound hHi hLo x

/-- Equicontinuity estimate for the per-step Schauder image. -/
theorem paperStepSchauderMap_abs_sub_le_of_source_bound
    {p : CMParams} {u Z W : ℝ → ℝ} (hlam : 0 < lam) {B : ℝ}
    (hsrcCont : Continuous (paperStepSource p c lam u Z W))
    (hsrcBound : ∀ y, |paperStepSource p c lam u Z W y| ≤ B) :
    ∀ x y,
      |paperStepSchauderMap p c lam u Z W x -
          paperStepSchauderMap p c lam u Z W y|
        ≤ (2 * (greenDelta c lam)⁻¹ * B) * |x - y| := by
  have hHi : ∀ t,
      IntegrableOn
        (gWeight (greenRootPlus c lam) (paperStepSource p c lam u Z W)) (Ioi t) :=
    fun t => gWeight_integrableOn_Ioi_of_bounded
      (greenRootPlus_pos (c := c) hlam) hsrcCont hsrcBound t
  have hLo : ∀ t,
      IntegrableOn
        (gWeight (greenRootMinus c lam) (paperStepSource p c lam u Z W)) (Iic t) :=
    fun t => gWeight_integrableOn_Iic_of_bounded
      (greenRootMinus_neg (c := c) hlam) hsrcCont hsrcBound t
  have hdiff : Differentiable ℝ (paperStepSchauderMap p c lam u Z W) := by
    intro x
    unfold paperStepSchauderMap
    exact (greenConv_hasDerivAt
      (c := c) (lam := lam) hsrcCont hHi hLo x).differentiableAt
  exact abs_sub_le_of_deriv_abs_le hdiff
    (paperStepSchauderMap_deriv_abs_le_of_source_bound
      (c := c) (lam := lam) (p := p) (u := u) (Z := Z) (W := W)
      hlam hsrcCont hsrcBound)

/-- Helly/Arzelà-Ascoli compactness for images in the wave trap with a uniform
equicontinuity and sup bound. -/
theorem localUniformSequentiallyCompactRange_inWaveTrapSet_of_uniform_lipschitz_bound
    {κ M A : ℝ} (hA : 0 ≤ A) (Tmap : (ℝ → ℝ) → ℝ → ℝ)
    (hmap : ∀ u, InWaveTrapSet κ M u → InWaveTrapSet κ M (Tmap u))
    (hLip : ∀ u, InWaveTrapSet κ M u →
      ∀ x y, |Tmap u x - Tmap u y| ≤ A * |x - y|)
    (hAbs : ∀ u, InWaveTrapSet κ M u → ∀ x, |Tmap u x| ≤ A) :
    LocalUniformSequentiallyCompactRange (InWaveTrapSet κ M) Tmap := by
  intro seq hseq
  set gs : ℕ → ℝ → ℝ := fun n => Tmap (seq n) with hgs
  have hgsL : ∀ k, ∀ x y, |gs k x - gs k y| ≤ A * |x - y| := by
    intro k x y
    exact hLip (seq k) (hseq k) x y
  have hgsB : ∀ k x, |gs k x| ≤ A := by
    intro k x
    exact hAbs (seq k) (hseq k) x
  obtain ⟨subseq, hsub, g, hpt, hgL⟩ :=
    helly_pointwise_selection A gs hgsL hgsB
  have hLU : LocallyUniformConverges (fun n => gs (subseq n)) g :=
    locallyUniform_of_helly_pointwise hA hpt hgsL hgL
  have himageTrap : ∀ n, InWaveTrapSet κ M (gs (subseq n)) := by
    intro n
    exact hmap (seq (subseq n)) (hseq (subseq n))
  have hnn : ∀ x, 0 ≤ g x :=
    fun x => hLU.nonneg_of_forall_nonneg
      (fun n => (himageTrap n).nonneg x)
  have hbar : ∀ x, g x ≤ upperBarrier κ M x :=
    fun x => hLU.le_of_forall_le
      (fun n => (himageTrap n).le_upperBarrier x)
  have hleM : ∀ x, g x ≤ M :=
    fun x => hLU.le_of_forall_le
      (fun n => (himageTrap n).le_M x)
  have hgcont : Continuous g :=
    continuous_of_locallyUniform
      (fun n => (himageTrap n).cunif_bdd.1) hLU
  have hgbdd : IsBddFun g := by
    refine ⟨M, fun x => ?_⟩
    rw [abs_of_nonneg (hnn x)]
    exact hleM x
  refine ⟨subseq, hsub, g, ?_, ?_⟩
  · exact ⟨⟨hgcont, hgbdd⟩, fun x => ⟨hnn x, hbar x⟩⟩
  · simpa [hgs] using hLU

/-- Small-radius choice for a Hölder modulus. -/
theorem exists_pos_radius_holder_mul_le
    {H β ε : ℝ} (hH : 0 ≤ H) (hβ : 0 < β) (hε : 0 < ε) :
    ∃ η > 0, H * η ^ β ≤ ε := by
  let base : ℝ := ε / (H + 1)
  let η : ℝ := base ^ β⁻¹
  have hden : 0 < H + 1 := by linarith
  have hbase : 0 < base := div_pos hε hden
  have hη : 0 < η := by
    dsimp [η]
    exact Real.rpow_pos_of_pos hbase β⁻¹
  refine ⟨η, hη, ?_⟩
  have hηpow : η ^ β = base := by
    dsimp [η, base]
    rw [Real.rpow_inv_rpow hbase.le (ne_of_gt hβ)]
  rw [hηpow]
  dsimp [base]
  have hmuldiv : H * (ε / (H + 1)) = (H * ε) / (H + 1) := by ring
  rw [hmuldiv, div_le_iff₀ hden]
  nlinarith

/-- Pointwise convergence plus a shared Hölder modulus upgrades to local-uniform
convergence on compact intervals. -/
theorem locallyUniform_of_pointwise_of_equiHolder
    {z : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {H β : ℝ}
    (hH : 0 ≤ H) (hβ : 0 < β)
    (hpt : ∀ x, Tendsto (fun k => z k x) atTop (𝓝 (f x)))
    (hzH : ∀ k, ∀ x y, |z k x - z k y| ≤ H * |x - y| ^ β)
    (hfH : ∀ x y, |f x - f y| ≤ H * |x - y| ^ β) :
    LocallyUniformConverges z f := by
  intro R hR ε hε
  obtain ⟨η, hη_pos, hHη⟩ :=
    exists_pos_radius_holder_mul_le (H := H) (β := β) (ε := ε / 3)
      hH hβ (by linarith)
  obtain ⟨Nnode, hNnode⟩ := exists_nat_gt (2 * R / η)
  set node : ℕ → ℝ := fun i => -R + (i : ℝ) * η with hnode_def
  have hcover : ∀ x ∈ Set.Icc (-R) R, ∃ i : ℕ, i ≤ Nnode ∧ |x - node i| ≤ η := by
    intro x hx
    rw [Set.mem_Icc] at hx
    obtain ⟨hx1, hx2⟩ := hx
    set t : ℝ := (x + R) / η with ht_def
    have ht_nonneg : 0 ≤ t := by
      rw [ht_def]
      exact div_nonneg (by linarith) hη_pos.le
    set i : ℕ := ⌊t⌋₊ with hi_def
    refine ⟨i, ?_, ?_⟩
    · have hi_le_t : (i : ℝ) ≤ t := Nat.floor_le ht_nonneg
      have ht_le : t ≤ 2 * R / η := by
        rw [ht_def]
        have hnum : x + R ≤ 2 * R := by nlinarith [hx2]
        gcongr
      have hiR : (i : ℝ) < (Nnode : ℝ) :=
        lt_of_le_of_lt (le_trans hi_le_t ht_le) hNnode
      have : i < Nnode := by exact_mod_cast hiR
      exact le_of_lt this
    · have hi_le_t : (i : ℝ) ≤ t := Nat.floor_le ht_nonneg
      have ht_lt : t < (i : ℝ) + 1 := Nat.lt_floor_add_one t
      have hlow : (i : ℝ) * η ≤ x + R := by
        have := mul_le_mul_of_nonneg_right hi_le_t hη_pos.le
        rwa [ht_def, div_mul_cancel₀ _ (ne_of_gt hη_pos)] at this
      have hhigh : x + R < ((i : ℝ) + 1) * η := by
        have := mul_lt_mul_of_pos_right ht_lt hη_pos
        rwa [ht_def, div_mul_cancel₀ _ (ne_of_gt hη_pos)] at this
      rw [hnode_def, abs_le]
      constructor <;> [nlinarith [hlow]; nlinarith [hhigh]]
  have hpt3 : ∀ i : ℕ, ∀ᶠ k in atTop, |z k (node i) - f (node i)| < ε / 3 := by
    intro i
    have h2 := Metric.tendsto_atTop.mp (hpt (node i)) (ε / 3) (by linarith)
    obtain ⟨N, hN⟩ := h2
    rw [eventually_atTop]
    exact ⟨N, fun k hk => by simpa [Real.dist_eq] using hN k hk⟩
  have hfin : ∀ᶠ k in atTop,
      ∀ i : ℕ, i ≤ Nnode → |z k (node i) - f (node i)| < ε / 3 := by
    have : ∀ᶠ k in atTop, ∀ i ∈ Finset.range (Nnode + 1),
        |z k (node i) - f (node i)| < ε / 3 := by
      apply (eventually_all_finset (Finset.range (Nnode + 1))).mpr
      intro i _; exact hpt3 i
    filter_upwards [this] with k hk i hi
    exact hk i (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  filter_upwards [hfin] with k hk x hx
  obtain ⟨i, hi_le, hxnode⟩ := hcover x hx
  have hnode_conv := hk i hi_le
  have hHstep : H * |x - node i| ^ β ≤ ε / 3 := by
    have hpow : |x - node i| ^ β ≤ η ^ β :=
      Real.rpow_le_rpow (abs_nonneg _) hxnode hβ.le
    exact le_trans (mul_le_mul_of_nonneg_left hpow hH) hHη
  have hHstep' : H * |node i - x| ^ β ≤ ε / 3 := by
    rw [abs_sub_comm]
    exact hHstep
  have hL1 : |z k x - z k (node i)| ≤ ε / 3 :=
    le_trans (hzH k x (node i)) hHstep
  have hL3 : |f (node i) - f x| ≤ ε / 3 :=
    le_trans (hfH (node i) x) hHstep'
  have htri1 : |z k x - f x|
      ≤ |z k x - z k (node i)| + |z k (node i) - f (node i)| +
        |f (node i) - f x| := by
    have e : z k x - f x =
        (z k x - z k (node i)) + (z k (node i) - f (node i)) +
          (f (node i) - f x) := by
      ring
    rw [e]
    calc
      |(z k x - z k (node i)) + (z k (node i) - f (node i)) +
          (f (node i) - f x)|
          ≤ |(z k x - z k (node i)) +
              (z k (node i) - f (node i))| + |f (node i) - f x| :=
            abs_add_le _ _
      _ ≤ |z k x - z k (node i)| + |z k (node i) - f (node i)| +
          |f (node i) - f x| := by
            have := abs_add_le (z k x - z k (node i))
              (z k (node i) - f (node i))
            linarith
  have : |z k x - z k (node i)| + |z k (node i) - f (node i)| +
      |f (node i) - f x| < ε := by
    linarith [hL1, hL3, hnode_conv]
  linarith [htri1, this]

/-- Local-uniform continuity of the truncated fixed-source map on a weighted
Hölder source box, derived from pointwise Green continuous dependence and the
uniform image Hölder modulus in `boxBounds`. -/
theorem paperFixedSourceMap_continuousOn_of_boxBounds
    (p : CMParams) {c lam M κ β B H : ℝ} {ω : ℝ → ℝ} {u Z : ℝ → ℝ}
    (hlam : 0 < lam) (hBnn : 0 ≤ B) (hHnn : 0 ≤ H) (hβpos : 0 < β)
    (hbox : PaperFixedSourceMapBoxBounds p c lam M κ β B H ω u Z) :
    LocalUniformContinuousOn
      (PaperWeightedHolderSourceBox κ M β B H ω)
      (paperFixedSourceMap p c lam M κ u Z) := by
  intro seq R hseq hR hLU
  apply locallyUniform_of_pointwise_of_equiHolder hHnn hβpos
  · intro x
    exact paperFixedSourceMap_tendsto_of_source_locallyUniform_sourceBox
      (p := p) (c := c) (lam := lam) (M := M) (κ := κ)
      (β := β) (B := B) (H := H) (ω := ω)
      (u := u) (Z := Z) (Rs := seq) (R := R)
      hlam hBnn hseq hR hLU x
  · intro n x y
    exact hbox.map_holder (seq n) (hseq n) x y
  · intro x y
    exact hbox.map_holder R hR x y

/-- Pointwise selection for uniformly bounded families with a shared Hölder
modulus.  The proof is the same rational diagonal as Helly, with a Hölder
squeeze from rationals to all real points. -/
def HolderPointwiseSelection (A H β : ℝ) : Prop :=
  ∀ gs : ℕ → ℝ → ℝ,
    (∀ k, ∀ x y, |gs k x - gs k y| ≤ H * |x - y| ^ β) →
    (∀ k x, |gs k x| ≤ A) →
      ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
        ∃ g : ℝ → ℝ,
          (∀ x, Tendsto (fun n => gs (subseq n) x) atTop (𝓝 (g x))) ∧
          (∀ x y, |g x - g y| ≤ H * |x - y| ^ β)

theorem holder_pointwise_selection
    (A H β : ℝ) (_hA : 0 ≤ A) (hH : 0 ≤ H) (hβ : 0 < β) :
    HolderPointwiseSelection A H β := by
  intro gs hHolder hB
  obtain ⟨φ, hφ, f₀, hrat⟩ := helly_rational_diagonal gs hB
  have hcauchy : ∀ x : ℝ, CauchySeq (fun n => gs (φ n) x) := by
    intro x
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨δ, hδpos, hHδ⟩ :=
      exists_pos_radius_holder_mul_le (H := H) (β := β) (ε := ε / 4)
        hH hβ (by linarith)
    obtain ⟨q, hq⟩ := exists_rat_near x hδpos
    have hqCauchy : CauchySeq (fun n => gs (φ n) (q : ℝ)) :=
      (hrat q).cauchySeq
    rw [Metric.cauchySeq_iff] at hqCauchy
    obtain ⟨N, hN⟩ := hqCauchy (ε / 3) (by linarith)
    refine ⟨N, ?_⟩
    intro m hm n hn
    have hxm :
        |gs (φ m) x - gs (φ m) (q : ℝ)| ≤ H * |x - q| ^ β :=
      hHolder (φ m) x q
    have hxn :
        |gs (φ n) x - gs (φ n) (q : ℝ)| ≤ H * |x - q| ^ β :=
      hHolder (φ n) x q
    have hmid : dist (gs (φ m) (q : ℝ)) (gs (φ n) (q : ℝ)) < ε / 3 :=
      hN m hm n hn
    rw [Real.dist_eq] at hmid ⊢
    have hHqbound : H * |x - q| ^ β ≤ ε / 4 := by
      have hpow : |x - (q : ℝ)| ^ β ≤ δ ^ β :=
        Real.rpow_le_rpow (abs_nonneg _) (le_of_lt hq) hβ.le
      exact le_trans (mul_le_mul_of_nonneg_left hpow hH) hHδ
    have htri : |gs (φ m) x - gs (φ n) x|
        ≤ |gs (φ m) x - gs (φ m) (q : ℝ)|
          + |gs (φ m) (q : ℝ) - gs (φ n) (q : ℝ)|
          + |gs (φ n) (q : ℝ) - gs (φ n) x| := by
      calc
        |gs (φ m) x - gs (φ n) x|
            = |(gs (φ m) x - gs (φ m) (q : ℝ))
                + (gs (φ m) (q : ℝ) - gs (φ n) (q : ℝ))
                + (gs (φ n) (q : ℝ) - gs (φ n) x)| := by
              ring_nf
        _ ≤ |(gs (φ m) x - gs (φ m) (q : ℝ))
              + (gs (φ m) (q : ℝ) - gs (φ n) (q : ℝ))|
              + |gs (φ n) (q : ℝ) - gs (φ n) x| := abs_add_le _ _
        _ ≤ (|gs (φ m) x - gs (φ m) (q : ℝ)|
              + |gs (φ m) (q : ℝ) - gs (φ n) (q : ℝ)|)
              + |gs (φ n) (q : ℝ) - gs (φ n) x| := by
              gcongr
              exact abs_add_le _ _
    have hxn' :
        |gs (φ n) (q : ℝ) - gs (φ n) x| ≤ H * |x - q| ^ β := by
      rw [abs_sub_comm]
      exact hxn
    have hmid' : |gs (φ m) (q : ℝ) - gs (φ n) (q : ℝ)| < ε / 3 := hmid
    calc
      |gs (φ m) x - gs (φ n) x|
          ≤ |gs (φ m) x - gs (φ m) (q : ℝ)|
              + |gs (φ m) (q : ℝ) - gs (φ n) (q : ℝ)|
              + |gs (φ n) (q : ℝ) - gs (φ n) x| := htri
      _ < ε / 4 + ε / 3 + ε / 4 := by
            have h1 : |gs (φ m) x - gs (φ m) (q : ℝ)| ≤ ε / 4 :=
              le_trans hxm hHqbound
            have h3 : |gs (φ n) (q : ℝ) - gs (φ n) x| ≤ ε / 4 :=
              le_trans hxn' hHqbound
            linarith
      _ ≤ ε := by linarith
  choose g hg using fun x => cauchySeq_tendsto_of_complete (hcauchy x)
  refine ⟨φ, hφ, g, hg, ?_⟩
  intro x y
  have htend : Tendsto (fun n => |gs (φ n) x - gs (φ n) y|) atTop
      (𝓝 (|g x - g y|)) := by
    have := ((hg x).sub (hg y)).abs
    simpa using this
  refine le_of_tendsto htend ?_
  filter_upwards with n
  exact hHolder (φ n) x y

/-- Arzelà-Ascoli/Helly compactness for images in the weighted Hölder source
box.  Once a map is a self-map of the box, the image family has a uniform
weighted sup-bound and a shared Hölder modulus, hence a locally uniformly
convergent subsequence whose limit remains in the same box. -/
theorem localUniformSequentiallyCompactRange_weightedHolderSourceBox_of_mapsTo
    {κ M β B H : ℝ} {ω : ℝ → ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hH : 0 ≤ H) (hβ : 0 < β)
    (Tmap : (ℝ → ℝ) → ℝ → ℝ)
    (hmap : ∀ R, PaperWeightedHolderSourceBox κ M β B H ω R →
      PaperWeightedHolderSourceBox κ M β B H ω (Tmap R)) :
    LocalUniformSequentiallyCompactRange
      (PaperWeightedHolderSourceBox κ M β B H ω) Tmap := by
  intro seq hseq
  set gs : ℕ → ℝ → ℝ := fun n => Tmap (seq n) with hgs
  have hbox : ∀ n, PaperWeightedHolderSourceBox κ M β B H ω (gs n) := by
    intro n
    exact hmap (seq n) (hseq n)
  have hgsH : ∀ k, ∀ x y, |gs k x - gs k y| ≤ H * |x - y| ^ β := by
    intro k x y
    exact (hbox k).holder x y
  have hgsB : ∀ k x, |gs k x| ≤ B * M := by
    intro k x
    calc
      |gs k x| ≤ B * upperBarrier κ M x := (hbox k).bound x
      _ ≤ B * M :=
        mul_le_mul_of_nonneg_left (upperBarrier_le_M κ M x) hB
  obtain ⟨subseq, hsub, g, hpt, hgH⟩ :=
    holder_pointwise_selection (B * M) H β (mul_nonneg hB hM) hH hβ
      gs hgsH hgsB
  have hLU : LocallyUniformConverges (fun n => gs (subseq n)) g :=
    locallyUniform_of_pointwise_of_equiHolder hH hβ hpt
      (fun n => hgsH (subseq n)) hgH
  have hgcont : Continuous g :=
    continuous_of_locallyUniform (fun n => (hbox (subseq n)).cont) hLU
  have hgbound : ∀ x, |g x| ≤ B * upperBarrier κ M x := by
    intro x
    have htend : Tendsto (fun n => |gs (subseq n) x|) atTop (𝓝 (|g x|)) :=
      (hLU.tendsto_at x).abs
    exact le_of_tendsto' htend (fun n => (hbox (subseq n)).bound x)
  have hω_nonneg : ∀ A, 0 ≤ ω A := (hbox 0).omega_nonneg
  have hω_tendsto : Tendsto ω atBot (𝓝 0) := (hbox 0).omega_tendsto
  have hgTailCauchy :
      ∀ A x y, x ≤ A → y ≤ A → |g x - g y| ≤ ω A := by
    intro A x y hx hy
    have htend : Tendsto (fun n => |gs (subseq n) x - gs (subseq n) y|)
        atTop (𝓝 (|g x - g y|)) := by
      have := ((hLU.tendsto_at x).sub (hLU.tendsto_at y)).abs
      simpa using this
    exact le_of_tendsto' htend
      (fun n => (hbox (subseq n)).leftTailCauchy A x y hx hy)
  have hgTail : ∃ gm, Tendsto g atBot (𝓝 gm) := by
    rw [← cauchy_map_iff_exists_tendsto]
    rw [Metric.cauchy_iff]
    constructor
    · infer_instance
    · intro ε hε
      have hev : ∀ᶠ A in atBot, dist (ω A) 0 < ε :=
        Metric.tendsto_nhds.mp hω_tendsto ε hε
      rcases Filter.eventually_atBot.mp hev with ⟨A, hA⟩
      refine ⟨g '' Set.Iic A, image_mem_map (Iic_mem_atBot A), ?_⟩
      intro gx hgx gy hgy
      rcases hgx with ⟨x, hx, rfl⟩
      rcases hgy with ⟨y, hy, rfl⟩
      rw [Real.dist_eq]
      have hmod := hgTailCauchy A x y hx hy
      have hωlt : ω A < ε := by
        have hdist := hA A le_rfl
        simpa [Real.dist_eq, abs_of_nonneg (hω_nonneg A)] using hdist
      exact lt_of_le_of_lt hmod hωlt
  refine ⟨subseq, hsub, g, ?_, ?_⟩
  · exact
      { cont := hgcont
        bound := hgbound
        holder := hgH
        omega_nonneg := hω_nonneg
        omega_tendsto := hω_tendsto
        leftTail := hgTail
        leftTailCauchy := hgTailCauchy }
  · simpa [hgs] using hLU

/-- Concrete Schauder data for the paper per-step map on the trapped convex set
`InWaveTrapSet κ M`.  The source continuity field is where real powers use only
continuity on `[0,M]`; the compactness fields are Green-smoothing bounds. -/
structure PaperStepSchauderMapData
    (p : CMParams) (c lam M κ Λ : ℝ) (u Z : ℝ → ℝ) where
  sourceBound : ℝ
  compactBound : ℝ
  compactBound_nonneg : 0 ≤ compactBound
  sourceBound_eq : Λ = 2 * (greenDelta c lam)⁻¹ * sourceBound
  mapsTo : ∀ W, InWaveTrapSet κ M W →
    InWaveTrapSet κ M (paperStepSchauderMap p c lam u Z W)
  continuousOn :
    LocalUniformContinuousOn (InWaveTrapSet κ M) (paperStepSchauderMap p c lam u Z)
  source_cont : ∀ W, InWaveTrapSet κ M W →
    Continuous (paperStepSource p c lam u Z W)
  source_bound : ∀ W, InWaveTrapSet κ M W →
    ∀ y, |paperStepSource p c lam u Z W y| ≤ sourceBound
  map_abs_bound : ∀ W, InWaveTrapSet κ M W →
    ∀ x, |paperStepSchauderMap p c lam u Z W x| ≤ compactBound
  map_lipschitz : ∀ W, InWaveTrapSet κ M W →
    ∀ x y,
      |paperStepSchauderMap p c lam u Z W x -
          paperStepSchauderMap p c lam u Z W y|
        ≤ compactBound * |x - y|

namespace PaperStepSchauderMapData

theorem compactRange
    {p : CMParams} {c lam M κ Λ : ℝ} {u Z : ℝ → ℝ}
    (h : PaperStepSchauderMapData p c lam M κ Λ u Z) :
    LocalUniformSequentiallyCompactRange
      (InWaveTrapSet κ M) (paperStepSchauderMap p c lam u Z) :=
  localUniformSequentiallyCompactRange_inWaveTrapSet_of_uniform_lipschitz_bound
    h.compactBound_nonneg (paperStepSchauderMap p c lam u Z)
    h.mapsTo h.map_lipschitz h.map_abs_bound

theorem exists_fixed
    {p : CMParams} {c lam M κ Λ : ℝ} {u Z : ℝ → ℝ}
    (hprinciple : LocalUniformSchauderFixedPointPrinciple (InWaveTrapSet κ M))
    (h : PaperStepSchauderMapData p c lam M κ Λ u Z) :
    ∃ W : ℝ → ℝ,
      InWaveTrapSet κ M W ∧ paperStepSchauderMap p c lam u Z W = W :=
  hprinciple (paperStepSchauderMap p c lam u Z) h.mapsTo
    h.continuousOn h.compactRange

end PaperStepSchauderMapData

/-- Construct the fixed-source existence statement from Schauder fixed point on
the trapped per-step map. -/
theorem PaperStepFixedSourceExistsForSuperTrap.of_schauder
    {p : CMParams} {c lam M κ Λ : ℝ} {u : ℝ → ℝ}
    (hprinciple : LocalUniformSchauderFixedPointPrinciple (InWaveTrapSet κ M))
    (hdata : ∀ Z : ℝ → ℝ, Continuous Z → Antitone Z →
      (∀ x, 0 ≤ Z x) →
      (∀ x, Z x ≤ upperBarrier κ M x) →
      (∀ x, frozenWaveOperator p c u Z x ≤ 0) →
        PaperStepSchauderMapData p c lam M κ Λ u Z) :
    PaperStepFixedSourceExistsForSuperTrap p c lam M κ Λ u := by
  intro _hu Z hZc hZa hZ0 hZB hZsuper
  let hs : PaperStepSchauderMapData p c lam M κ Λ u Z :=
    hdata Z hZc hZa hZ0 hZB hZsuper
  obtain ⟨W, hWtrap, hfix⟩ := hs.exists_fixed hprinciple
  let R : ℝ → ℝ := paperStepSource p c lam u Z W
  have hgreen : (fun x => greenConv c lam R x) = W := by
    simpa [R, paperStepSchauderMap] using hfix
  refine ⟨R, hs.source_cont W hWtrap, ?_, ?_⟩
  · exact ⟨hs.sourceBound, hs.source_bound W hWtrap, hs.sourceBound_eq⟩
  · calc
      R = paperStepSource p c lam u Z W := rfl
      _ = paperStepSource p c lam u Z (fun x => greenConv c lam R x) := by
        rw [hgreen]

/-- Same constructor, starting from the existing approximate-fixed-sequence
engine that feeds the local-uniform Schauder principle. -/
theorem PaperStepFixedSourceExistsForSuperTrap.of_schauder_approx
    {p : CMParams} {c lam M κ Λ : ℝ} {u : ℝ → ℝ}
    (happrox : LocalUniformApproxFixedPointSequences (InWaveTrapSet κ M))
    (hdata : ∀ Z : ℝ → ℝ, Continuous Z → Antitone Z →
      (∀ x, 0 ≤ Z x) →
      (∀ x, Z x ≤ upperBarrier κ M x) →
      (∀ x, frozenWaveOperator p c u Z x ≤ 0) →
        PaperStepSchauderMapData p c lam M κ Λ u Z) :
    PaperStepFixedSourceExistsForSuperTrap p c lam M κ Λ u :=
  PaperStepFixedSourceExistsForSuperTrap.of_schauder
    (p := p) (c := c) (lam := lam) (M := M) (κ := κ) (Λ := Λ) (u := u)
    (localUniformSchauderFixedPointPrinciple_of_approx_fixed_sequences happrox)
    hdata

/-- Fixed-source existence from the validated truncated source-box route.

The Schauder fixed point is taken for the source map
`R ↦ paperStepSource_truncated ... R` on a weighted-Hölder source box.
The `truncation_inactive` field is the a-priori trap output for that fixed
point; once it gives `0 ≤ greenConv R ≤ upperBarrier κ M`, the spatial clamp
identities turn the truncated fixed-source equation into the genuine paper
source equation. -/
theorem PaperStepFixedSourceExistsForSuperTrap.of_truncated_sourceBox
    {p : CMParams} {c lam M κ Λ : ℝ} {u : ℝ → ℝ}
    (hdata : InMonotoneWaveTrapSet κ M u →
      ∀ Z : ℝ → ℝ, Continuous Z → Antitone Z →
      (∀ x, 0 ≤ Z x) →
      (∀ x, Z x ≤ upperBarrier κ M x) →
      (∀ x, frozenWaveOperator p c u Z x ≤ 0) →
        PaperTruncatedFixedSourceBoxData p c lam M κ Λ u Z) :
    PaperStepFixedSourceExistsForSuperTrap p c lam M κ Λ u := by
  intro hu Z hZc hZa hZ0 hZB hZsuper
  let hd : PaperTruncatedFixedSourceBoxData p c lam M κ Λ u Z :=
    hdata hu Z hZc hZa hZ0 hZB hZsuper
  obtain ⟨R, hRbox, hRfix⟩ := hd.exists_fixed
  have hIcc :
      ∀ x,
        (fun y => greenConv c lam R y) x ∈
          Set.Icc (0 : ℝ) (upperBarrier κ M x) :=
    hd.truncation_inactive R hRbox hRfix
  have htrunc_eq :
      paperFixedSourceMap p c lam M κ u Z R =
        paperStepSource p c lam u Z (fun x => greenConv c lam R x) :=
    paperStepSource_truncated_eq_paperStepSource_of_Icc
      (p := p) (c := c) (lam := lam) (M := M) (κ := κ)
      (u := u) (Z := Z) (R := R) hd.hM_nonneg hIcc
  have hRbound_const : ∀ y, |R y| ≤ hd.B * M := by
    intro y
    calc
      |R y| ≤ hd.B * upperBarrier κ M y := hRbox.bound y
      _ ≤ hd.B * M :=
        mul_le_mul_of_nonneg_left (upperBarrier_le_M κ M y) hd.B_nonneg
  refine ⟨R, hRbox.cont, ?_, ?_⟩
  · exact ⟨hd.B * M, hRbound_const, hd.sourceBound_eq⟩
  · calc
      R = paperFixedSourceMap p c lam M κ u Z R := hRfix.symm
      _ = paperStepSource p c lam u Z (fun x => greenConv c lam R x) := htrunc_eq

/-! ## Historical contraction estimates

These estimates are retained as lower-level resolvent bounds.  The constructor
for `PaperStepFixedSourceExistsForSuperTrap` above uses Schauder instead. -/

/-
/-- Sup-norm resolvent estimate for the Green convolution on bounded continuous
sources:
`‖greenConv(R₁-R₂)‖∞ ≤ λ⁻¹ ‖R₁-R₂‖∞`. -/
theorem greenConv_abs_le_of_bcf_dist
    (hlam : 0 < lam) (R₁ R₂ : ℝ →ᵇ ℝ) (x : ℝ) :
    |greenConv c lam (fun y => R₁ y - R₂ y) x| ≤ lam⁻¹ * dist R₁ R₂ := by
  let H : ℝ →ᵇ ℝ := R₁ - R₂
  have hHcont : Continuous (fun y : ℝ => R₁ y - R₂ y) := by
    simpa [H, BoundedContinuousFunction.sub_apply] using H.continuous
  have hHbound : ∀ y : ℝ, |R₁ y - R₂ y| ≤ ‖R₁ - R₂‖ := by
    intro y
    simpa [Real.norm_eq_abs, BoundedContinuousFunction.sub_apply] using
      (R₁ - R₂).norm_coe_le_norm y
  have hraw :
      (∫ y, greenKernel c lam (x - y) * (R₁ y - R₂ y)) =
        greenConv c lam (fun y => R₁ y - R₂ y) x :=
    greenConv_raw_eq_of_bounded
      (c := c) (lam := lam) hlam hHcont hHbound x
  rw [← hraw]
  have hker :
      |kernelConvVal (greenKernel c lam) H x|
        ≤ (∫ z, |greenKernel c lam z|) * ‖H‖ :=
    kernelConvVal_abs_le (K := greenKernel c lam)
      (greenKernel_integrable (c := c) hlam) H x
  have hdist : ‖H‖ = dist R₁ R₂ := by
    simp [H, dist_eq_norm]
  calc
    |∫ y, greenKernel c lam (x - y) * (R₁ y - R₂ y)|
        = |kernelConvVal (greenKernel c lam) H x| := by rfl
    _ ≤ (∫ z, |greenKernel c lam z|) * ‖H‖ := hker
    _ = lam⁻¹ * dist R₁ R₂ := by
      rw [greenKernel_l1_eq (c := c) hlam, hdist]

/-- Sup-norm estimate for the derivative Green kernel on bounded continuous
source differences:
`‖greenConvDeriv(R₁-R₂)‖∞ ≤ 2/δ · ‖R₁-R₂‖∞`. -/
theorem greenConvDeriv_abs_le_of_bcf_dist
    (hlam : 0 < lam) (R₁ R₂ : ℝ →ᵇ ℝ) (x : ℝ) :
    |greenConvDeriv c lam (fun y => R₁ y - R₂ y) x|
      ≤ 2 * (greenDelta c lam)⁻¹ * dist R₁ R₂ := by
  let H : ℝ →ᵇ ℝ := R₁ - R₂
  have hHcont : Continuous (fun y : ℝ => R₁ y - R₂ y) := by
    simpa [H, BoundedContinuousFunction.sub_apply] using H.continuous
  have hHbound : ∀ y : ℝ, |R₁ y - R₂ y| ≤ ‖R₁ - R₂‖ := by
    intro y
    simpa [Real.norm_eq_abs, BoundedContinuousFunction.sub_apply] using
      (R₁ - R₂).norm_coe_le_norm y
  have hHi : ∀ x,
      IntegrableOn
        (gWeight (greenRootPlus c lam) (fun y : ℝ => R₁ y - R₂ y)) (Ioi x) :=
    fun x => gWeight_integrableOn_Ioi_of_bounded
      (greenRootPlus_pos (c := c) hlam) hHcont hHbound x
  have hLo : ∀ x,
      IntegrableOn
        (gWeight (greenRootMinus c lam) (fun y : ℝ => R₁ y - R₂ y)) (Iic x) :=
    fun x => gWeight_integrableOn_Iic_of_bounded
      (greenRootMinus_neg (c := c) hlam) hHcont hHbound x
  have hderiv :=
    greenConvDeriv_abs_le (c := c) (lam := lam) hlam hHbound hHi hLo x
  have hdist : ‖R₁ - R₂‖ = dist R₁ R₂ := by
    simp [dist_eq_norm]
  simpa [hdist] using hderiv

/-- The λZ term in the paper source is independent of the fixed-source unknown
and cancels in source differences. -/
theorem paperStepSource_sub_cancel_linear
    (p : CMParams) (c lam : ℝ) (u Z W₁ W₂ : ℝ → ℝ) (x : ℝ) :
    paperStepSource p c lam u Z W₁ x - paperStepSource p c lam u Z W₂ x =
      paperStepNonlinearity p u W₁ x - paperStepNonlinearity p u W₂ x := by
  unfold paperStepSource
  ring

/-- The raw fixed-source map
`R ↦ paperStepSource p c lam u Z (greenConv R)`. -/
def paperStepFixedSourceRawMap
    (p : CMParams) (c lam : ℝ) (u Z : ℝ → ℝ) (R : ℝ →ᵇ ℝ) : ℝ → ℝ :=
  paperStepSource p c lam u Z (fun x => greenConv c lam R x)

/-- Bundle the fixed-source map as a bounded continuous self-map, using an
explicit uniform source bound. -/
def paperStepFixedSourceBCF
    (p : CMParams) (c lam : ℝ) (u Z : ℝ → ℝ)
    (B : ℝ)
    (hcont : ∀ R : ℝ →ᵇ ℝ,
      Continuous (paperStepFixedSourceRawMap p c lam u Z R))
    (hbound : ∀ R : ℝ →ᵇ ℝ, ∀ x : ℝ,
      |paperStepFixedSourceRawMap p c lam u Z R x| ≤ B) :
    (ℝ →ᵇ ℝ) → (ℝ →ᵇ ℝ) :=
  fun R =>
    BoundedContinuousFunction.ofNormedAddCommGroup
      (paperStepFixedSourceRawMap p c lam u Z R)
      (hcont R) B
      (fun x => by
        simpa [Real.norm_eq_abs] using hbound R x)

@[simp] theorem paperStepFixedSourceBCF_apply
    (p : CMParams) (c lam : ℝ) (u Z : ℝ → ℝ)
    (B : ℝ)
    (hcont : ∀ R : ℝ →ᵇ ℝ,
      Continuous (paperStepFixedSourceRawMap p c lam u Z R))
    (hbound : ∀ R : ℝ →ᵇ ℝ, ∀ x : ℝ,
      |paperStepFixedSourceRawMap p c lam u Z R x| ≤ B)
    (R : ℝ →ᵇ ℝ) (x : ℝ) :
    paperStepFixedSourceBCF p c lam u Z B hcont hbound R x =
      paperStepFixedSourceRawMap p c lam u Z R x := rfl

/-- If the paper source satisfies a first-order difference estimate in the Green
profile and its first derivative, then the fixed-source map is a sup-norm contraction with
constant bounded by `Ls * (λ⁻¹ + 2/δ)`.

The hypothesis `hsourceLip` is the precise first-order source obligation:
the `lam * Z` term has cancelled, and only `greenConv(R₁-R₂)` plus
`greenConvDeriv(R₁-R₂)` may appear. -/
theorem paperStepFixedSourceBCF_pointwise_dist_le
    (hlam : 0 < lam) {p : CMParams} {u Z : ℝ → ℝ}
    {B Ls : ℝ} {K : NNReal}
    (hcont : ∀ R : ℝ →ᵇ ℝ,
      Continuous (paperStepFixedSourceRawMap p c lam u Z R))
    (hbound : ∀ R : ℝ →ᵇ ℝ, ∀ x : ℝ,
      |paperStepFixedSourceRawMap p c lam u Z R x| ≤ B)
    (hLs0 : 0 ≤ Ls)
    (_hKlt : K < 1)
    (hfactorK : Ls * (lam⁻¹ + 2 * (greenDelta c lam)⁻¹) ≤ (K : ℝ))
    (hsourceLip : ∀ R₁ R₂ : ℝ →ᵇ ℝ, ∀ x : ℝ,
      |paperStepFixedSourceRawMap p c lam u Z R₁ x -
          paperStepFixedSourceRawMap p c lam u Z R₂ x|
        ≤ Ls *
          (|greenConv c lam (fun y => R₁ y - R₂ y) x| +
            |greenConvDeriv c lam (fun y => R₁ y - R₂ y) x|)) :
    ∀ R₁ R₂ : ℝ →ᵇ ℝ, ∀ x : ℝ,
      dist (paperStepFixedSourceBCF p c lam u Z B hcont hbound R₁ x)
        (paperStepFixedSourceBCF p c lam u Z B hcont hbound R₂ x)
        ≤ (K : ℝ) * dist R₁ R₂ := by
  intro R₁ R₂ x
  rw [paperStepFixedSourceBCF_apply, paperStepFixedSourceBCF_apply, Real.dist_eq]
  have hW := greenConv_abs_le_of_bcf_dist (c := c) (lam := lam) hlam R₁ R₂ x
  have hP := greenConvDeriv_abs_le_of_bcf_dist (c := c) (lam := lam) hlam R₁ R₂ x
  have hsum :
      |greenConv c lam (fun y => R₁ y - R₂ y) x| +
          |greenConvDeriv c lam (fun y => R₁ y - R₂ y) x|
        ≤ lam⁻¹ * dist R₁ R₂ +
          (2 * (greenDelta c lam)⁻¹ * dist R₁ R₂) :=
    add_le_add hW hP
  have hsource := hsourceLip R₁ R₂ x
  have hmul :
      Ls *
          (|greenConv c lam (fun y => R₁ y - R₂ y) x| +
            |greenConvDeriv c lam (fun y => R₁ y - R₂ y) x|)
        ≤ Ls *
          (lam⁻¹ * dist R₁ R₂ +
            (2 * (greenDelta c lam)⁻¹ * dist R₁ R₂)) :=
    mul_le_mul_of_nonneg_left hsum hLs0
  have hfactor :
      Ls *
          (lam⁻¹ * dist R₁ R₂ +
            (2 * (greenDelta c lam)⁻¹ * dist R₁ R₂))
        = (Ls * (lam⁻¹ + 2 * (greenDelta c lam)⁻¹)) * dist R₁ R₂ := by
    ring
  have hKmul :
      (Ls * (lam⁻¹ + 2 * (greenDelta c lam)⁻¹)) * dist R₁ R₂
        ≤ (K : ℝ) * dist R₁ R₂ :=
    mul_le_mul_of_nonneg_right hfactorK dist_nonneg
  exact hsource.trans (hmul.trans (le_trans (le_of_eq hfactor) hKmul))

/-- Cross-factor version of the paper fixed-source pointwise estimate.

This is the direct bridge to the existing `WaveRotheStep` contraction factor:
the paper source may be bounded by the reaction coefficient times the Green
profile difference plus the chemotaxis coefficient times the derivative Green
profile difference, and the two resolvent estimates collapse to the committed
`crossContractionFactor`. -/
theorem paperStepFixedSourceBCF_pointwise_dist_le_crossFactor
    (hlam : 0 < lam) {p : CMParams} {u Z : ℝ → ℝ}
    {B Msrc Bv : ℝ}
    (hcont : ∀ R : ℝ →ᵇ ℝ,
      Continuous (paperStepFixedSourceRawMap p c lam u Z R))
    (hbound : ∀ R : ℝ →ᵇ ℝ, ∀ x : ℝ,
      |paperStepFixedSourceRawMap p c lam u Z R x| ≤ B)
    (hMsrc : 0 ≤ Msrc) (hBv : 0 ≤ Bv)
    (hsourceLip : ∀ R₁ R₂ : ℝ →ᵇ ℝ, ∀ x : ℝ,
      |paperStepFixedSourceRawMap p c lam u Z R₁ x -
          paperStepFixedSourceRawMap p c lam u Z R₂ x|
        ≤ reactionLip p.α Msrc *
            |greenConv c lam (fun y => R₁ y - R₂ y) x| +
          |p.χ| * rpowLip p.m Msrc * Bv *
            |greenConvDeriv c lam (fun y => R₁ y - R₂ y) x|) :
    ∀ R₁ R₂ : ℝ →ᵇ ℝ, ∀ x : ℝ,
      dist (paperStepFixedSourceBCF p c lam u Z B hcont hbound R₁ x)
        (paperStepFixedSourceBCF p c lam u Z B hcont hbound R₂ x)
        ≤ crossContractionFactor p Msrc Bv lam (greenDelta c lam) *
          dist R₁ R₂ := by
  intro R₁ R₂ x
  rw [paperStepFixedSourceBCF_apply, paperStepFixedSourceBCF_apply, Real.dist_eq]
  have hW := greenConv_abs_le_of_bcf_dist (c := c) (lam := lam) hlam R₁ R₂ x
  have hP := greenConvDeriv_abs_le_of_bcf_dist (c := c) (lam := lam) hlam R₁ R₂ x
  have hRxn0 : 0 ≤ reactionLip p.α Msrc :=
    reactionLip_nonneg p.hα hMsrc
  have hChem0 : 0 ≤ |p.χ| * rpowLip p.m Msrc * Bv := by
    have hm0 : 0 ≤ rpowLip p.m Msrc := rpowLip_nonneg p.hm hMsrc
    positivity
  have htermW :
      reactionLip p.α Msrc *
          |greenConv c lam (fun y => R₁ y - R₂ y) x|
        ≤ reactionLip p.α Msrc * (lam⁻¹ * dist R₁ R₂) :=
    mul_le_mul_of_nonneg_left hW hRxn0
  have htermP :
      |p.χ| * rpowLip p.m Msrc * Bv *
          |greenConvDeriv c lam (fun y => R₁ y - R₂ y) x|
        ≤ |p.χ| * rpowLip p.m Msrc * Bv *
          (2 * (greenDelta c lam)⁻¹ * dist R₁ R₂) :=
    mul_le_mul_of_nonneg_left hP hChem0
  calc
    |paperStepFixedSourceRawMap p c lam u Z R₁ x -
        paperStepFixedSourceRawMap p c lam u Z R₂ x|
        ≤ reactionLip p.α Msrc *
            |greenConv c lam (fun y => R₁ y - R₂ y) x| +
          |p.χ| * rpowLip p.m Msrc * Bv *
            |greenConvDeriv c lam (fun y => R₁ y - R₂ y) x| :=
          hsourceLip R₁ R₂ x
    _ ≤ reactionLip p.α Msrc * (lam⁻¹ * dist R₁ R₂) +
          |p.χ| * rpowLip p.m Msrc * Bv *
            (2 * (greenDelta c lam)⁻¹ * dist R₁ R₂) :=
          add_le_add htermW htermP
    _ = crossContractionFactor p Msrc Bv lam (greenDelta c lam) *
          dist R₁ R₂ := by
          unfold crossContractionFactor
          ring

/-- The paper fixed-source path reuses the committed large-`λ` smallness
lemma for the cross contraction factor. -/
theorem paperStepFixedSource_crossContractionFactor_lt_one_of_large_lambda
    (p : CMParams) {Msrc Bv : ℝ} (hMsrc : 0 ≤ Msrc) (hBv : 0 ≤ Bv)
    (c : ℝ) :
    ∀ᶠ lam in Filter.atTop,
      crossContractionFactor p Msrc Bv lam (greenDelta c lam) < 1 :=
  crossContractionFactor_lt_one_of_large_lambda p hMsrc hBv c

/-- If the paper source satisfies a first-order difference estimate in the Green
profile and its first derivative, then the fixed-source map is a sup-norm contraction with
constant bounded by `Ls * (λ⁻¹ + 2/δ)`. -/
theorem paperStepFixedSourceBCF_contracting
    (hlam : 0 < lam) {p : CMParams} {u Z : ℝ → ℝ}
    {B Ls : ℝ} {K : NNReal}
    (hcont : ∀ R : ℝ →ᵇ ℝ,
      Continuous (paperStepFixedSourceRawMap p c lam u Z R))
    (hbound : ∀ R : ℝ →ᵇ ℝ, ∀ x : ℝ,
      |paperStepFixedSourceRawMap p c lam u Z R x| ≤ B)
    (hLs0 : 0 ≤ Ls)
    (hKlt : K < 1)
    (hfactorK : Ls * (lam⁻¹ + 2 * (greenDelta c lam)⁻¹) ≤ (K : ℝ))
    (hsourceLip : ∀ R₁ R₂ : ℝ →ᵇ ℝ, ∀ x : ℝ,
      |paperStepFixedSourceRawMap p c lam u Z R₁ x -
          paperStepFixedSourceRawMap p c lam u Z R₂ x|
        ≤ Ls *
          (|greenConv c lam (fun y => R₁ y - R₂ y) x| +
            |greenConvDeriv c lam (fun y => R₁ y - R₂ y) x|)) :
    ContractingWith K (paperStepFixedSourceBCF p c lam u Z B hcont hbound) := by
  exact contractingWith_of_pointwise_dist_le
    (Φ := paperStepFixedSourceBCF p c lam u Z B hcont hbound) hKlt
    (paperStepFixedSourceBCF_pointwise_dist_le
      (c := c) (lam := lam) hlam hcont hbound hLs0 hKlt hfactorK hsourceLip)

/-- Contractive fixed point for the bundled paper fixed-source map, returning the
`PaperStepFixedSourceCore` required by the downstream Green bookkeeping. -/
def paperStepFixedSourceCore_of_contracting
    {p : CMParams} {c lam M κ Λ : ℝ} {u Z : ℝ → ℝ}
    {B : ℝ} {K : NNReal}
    (hcont : ∀ R : ℝ →ᵇ ℝ,
      Continuous (paperStepFixedSourceRawMap p c lam u Z R))
    (hbound : ∀ R : ℝ →ᵇ ℝ, ∀ x : ℝ,
      |paperStepFixedSourceRawMap p c lam u Z R x| ≤ B)
    (hΛ : Λ = 2 * (greenDelta c lam)⁻¹ * B)
    (hcontr :
      ContractingWith K (paperStepFixedSourceBCF p c lam u Z B hcont hbound)) :
    PaperStepFixedSourceCore p c lam M κ Λ u Z :=
  let Φ := paperStepFixedSourceBCF p c lam u Z B hcont hbound
  let Rb : ℝ →ᵇ ℝ := ContractingWith.fixedPoint Φ hcontr
  have hfix : Function.IsFixedPt Φ Rb := hcontr.fixedPoint_isFixedPt
  { R := Rb
    source_eq := by
      funext x
      have hx : Φ Rb x = Rb x := by
        simpa using congrArg (fun R : ℝ →ᵇ ℝ => R x) (show Φ Rb = Rb from hfix)
      exact hx.symm
    R_cont := Rb.continuous
    R_bound_const := B
    R_bound := by
      intro y
      have hx : Φ Rb y = Rb y := by
        simpa using congrArg (fun R : ℝ →ᵇ ℝ => R y) (show Φ Rb = Rb from hfix)
      rw [← hx]
      exact hbound Rb y
    R_bound_eq := hΛ }

/-- Contractive fixed point for the bundled paper fixed-source map using the
committed `crossImplicitStep_exists_unique` plumbing.  The theorem name is
cross-step historical, but its statement is the generic BCF contraction fixed
point and is reused here with the paper fixed-source map as `Φ`. -/
def paperStepFixedSourceCore_of_crossImplicitStep
    {p : CMParams} {c lam M κ Λ : ℝ} {u Z : ℝ → ℝ}
    {B : ℝ} {K : NNReal}
    (hcont : ∀ R : ℝ →ᵇ ℝ,
      Continuous (paperStepFixedSourceRawMap p c lam u Z R))
    (hbound : ∀ R : ℝ →ᵇ ℝ, ∀ x : ℝ,
      |paperStepFixedSourceRawMap p c lam u Z R x| ≤ B)
    (hΛ : Λ = 2 * (greenDelta c lam)⁻¹ * B)
    (hKlt : K < 1)
    (hpoint : ∀ R₁ R₂ : ℝ →ᵇ ℝ, ∀ x : ℝ,
      dist (paperStepFixedSourceBCF p c lam u Z B hcont hbound R₁ x)
        (paperStepFixedSourceBCF p c lam u Z B hcont hbound R₂ x)
        ≤ (K : ℝ) * dist R₁ R₂) :
    PaperStepFixedSourceCore p c lam M κ Λ u Z :=
  let Φ := paperStepFixedSourceBCF p c lam u Z B hcont hbound
  let huniq : ∃! Rb : ℝ →ᵇ ℝ, Φ Rb = Rb :=
    crossImplicitStep_exists_unique (Φ := Φ) hKlt hpoint
  let Rb : ℝ →ᵇ ℝ := Classical.choose huniq
  have hfix : Φ Rb = Rb := (Classical.choose_spec huniq).1
  { R := Rb
    source_eq := by
      funext x
      have hx : Φ Rb x = Rb x := by
        simpa using congrArg (fun R : ℝ →ᵇ ℝ => R x) hfix
      exact hx.symm
    R_cont := Rb.continuous
    R_bound_const := B
    R_bound := by
      intro y
      have hx : Φ Rb y = Rb y := by
        simpa using congrArg (fun R : ℝ →ᵇ ℝ => R y) hfix
      rw [← hx]
      exact hbound Rb y
    R_bound_eq := hΛ }
-/

/-- Close the Green bookkeeping fields of `PaperStepAnalytic` from bounded
continuous source data. -/
def paperStepAnalytic_of_core
    {p : CMParams} {c lam M κ Λ : ℝ} {u Z W : ℝ → ℝ}
    (hlam : 0 < lam) (hc : PaperStepAnalyticCore p c lam M κ Λ u Z W) :
    PaperStepAnalytic p c lam M κ Λ u Z W :=
  { R := hc.R
    source_eq := hc.source_eq
    green_repr := hc.green_repr
    conv_form := by
      calc
        W = fun x => greenConv c lam hc.R x := hc.green_repr
        _ = fun x => ∫ y, greenKernel c lam (x - y) * hc.R y := by
          funext x
          exact (greenConv_raw_eq_of_bounded
            (c := c) (lam := lam) hlam hc.R_cont hc.R_bound x).symm
    R_cont := hc.R_cont
    R_bound := ⟨hc.R_bound_const, hc.R_bound, hc.R_bound_eq⟩
    R_hi := fun x =>
      gWeight_integrableOn_Ioi_of_bounded
        (greenRootPlus_pos (c := c) hlam) hc.R_cont hc.R_bound x
    R_lo := fun x =>
      gWeight_integrableOn_Iic_of_bounded
        (greenRootMinus_neg (c := c) hlam) hc.R_cont hc.R_bound x
    R_int_trans := fun x =>
      greenKernel_neg_mul_translate_integrable_of_bounded
        (c := c) (lam := lam) hlam hc.R_cont hc.R_bound x }

theorem paperStep_contDiff_two_of_core
    {p : CMParams} {M κ Λ : ℝ} {u Z W : ℝ → ℝ}
    (hlam : 0 < lam) (hc : PaperStepAnalyticCore p c lam M κ Λ u Z W) :
    ContDiff ℝ 2 W := by
  let ha := paperStepAnalytic_of_core (c := c) (lam := lam) hlam hc
  rw [ha.green_repr]
  exact greenConv_contDiff_two ha.R_cont ha.R_hi ha.R_lo

/-- The derivative tails of a Green-represented paper step vanish once the source
has finite limits at both infinities. -/
theorem paperStep_deriv_tendsto_zero_of_core
    {p : CMParams} {M κ Λ : ℝ} {u Z W : ℝ → ℝ}
    (hlam : 0 < lam) (hc : PaperStepAnalyticCore p c lam M κ Λ u Z W)
    (htail : PaperStepSourceTailData p u Z W) :
    Tendsto (fun x => deriv W x) atBot (𝓝 0) ∧
      Tendsto (fun x => deriv W x) atTop (𝓝 0) := by
  have hRbdd : IsBddFun hc.R := ⟨hc.R_bound_const, hc.R_bound⟩
  have ha : PaperStepAnalytic p c lam M κ Λ u Z W :=
    paperStepAnalytic_of_core (c := c) (lam := lam) hlam hc
  have hWderiv_bdd : IsBddFun (deriv W) :=
    ⟨Λ, paperStep_deriv_le (c := c) (lam := lam) hlam ha⟩
  have hsource_tails :
      (∃ Ra : ℝ, Tendsto (paperStepSource p c lam u Z W) atBot (𝓝 Ra)) ∧
        ∃ Rb : ℝ, Tendsto (paperStepSource p c lam u Z W) atTop (𝓝 Rb) :=
    paperStepSource_tail_limits
      (p := p) (c := c) (lam := lam) (u := u) (Z := Z) (W := W)
      htail hWderiv_bdd
  have hRtail_bot : ∃ Ra : ℝ, Tendsto hc.R atBot (𝓝 Ra) := by
    rcases hsource_tails.1 with ⟨Ra, hRa⟩
    refine ⟨Ra, ?_⟩
    simpa [hc.source_eq] using hRa
  have hRtail_top : ∃ Rb : ℝ, Tendsto hc.R atTop (𝓝 Rb) := by
    rcases hsource_tails.2 with ⟨Rb, hRb⟩
    refine ⟨Rb, ?_⟩
    simpa [hc.source_eq] using hRb
  have htails :=
    greenConvDeriv_tendsto_zero_of_source_tail_limits
      (c := c) (lam := lam) hlam hc.R_cont hRbdd hRtail_bot hRtail_top
  constructor
  · simpa [hc.green_repr] using htails.1
  · simpa [hc.green_repr] using htails.2

theorem paperStep_contDiff_three_of_core_reg
    {p : CMParams} {M κ Λ : ℝ} {u Z W : ℝ → ℝ}
    (hlam : 0 < lam) (hc : PaperStepAnalyticCore p c lam M κ Λ u Z W)
    (hRreg : ContDiff ℝ 1 hc.R) :
    ContDiff ℝ 3 W := by
  let ha := paperStepAnalytic_of_core (c := c) (lam := lam) hlam hc
  rw [ha.green_repr]
  exact greenConv_contDiff_three hRreg ha.R_hi ha.R_lo

/-- Smooth-source C³ Green bootstrap away from zeros of the produced step.

The unconditional C² Green bootstrap supplies `W ∈ C²`; the previous source
regularity lemma gives `R ∈ C¹` under the displayed nonzero hypothesis, and the
existing Green bootstrap then yields `W ∈ C³`. -/
theorem paperStep_contDiff_three_of_core_smooth_nonzero
    {p : CMParams} {M κ Λ : ℝ} {u Z W : ℝ → ℝ}
    (hlam : 0 < lam)
    (hc : PaperStepAnalyticCore p c lam M κ Λ u Z W)
    (hZ : ContDiff ℝ 1 Z)
    (hV : ContDiff ℝ 2 (frozenElliptic p u))
    (hWnz : ∀ x, W x ≠ 0) :
    ContDiff ℝ 3 W := by
  have hW2 : ContDiff ℝ 2 W :=
    paperStep_contDiff_two_of_core (c := c) (lam := lam) hlam hc
  have hRreg : ContDiff ℝ 1 hc.R := by
    rw [hc.source_eq]
    exact paperStepSource_contDiff_one_of_nonzero
      (p := p) (c := c) (lam := lam) hZ hW2 hWnz hV
  exact paperStep_contDiff_three_of_core_reg
    (c := c) (lam := lam) hlam hc hRreg

/-- Build the full analytic record directly from a fixed Green source. -/
def paperStepAnalytic_of_fixed_source
    {p : CMParams} {c lam M κ Λ : ℝ} {u Z R : ℝ → ℝ}
    (hlam : 0 < lam)
    (hsource : R = paperStepSource p c lam u Z (fun x => greenConv c lam R x))
    (hRcont : Continuous R) (B : ℝ) (hRbound : ∀ y, |R y| ≤ B)
    (hΛ : Λ = 2 * (greenDelta c lam)⁻¹ * B) :
    PaperStepAnalytic p c lam M κ Λ u Z (fun x => greenConv c lam R x) :=
  paperStepAnalytic_of_core (c := c) (lam := lam) hlam
    (paperStepAnalyticCore_of_fixed_source
      (p := p) (c := c) (lam := lam) (M := M) (κ := κ) (Λ := Λ)
      (u := u) (Z := Z) hsource hRcont B hRbound hΛ)

theorem paperStep_le_upper
    {p : CMParams} {M C_chem : ℝ} {u Z W B : ℝ → ℝ}
    (hlam : 0 < lam)
    (hstep : ∀ x, paperImplicitStepOp p c (1 / lam) u W x = Z x)
    (hd : PaperStepUpperData p c lam M C_chem u Z W B) :
    ∀ x, W x ≤ B x := by
  exact
    paperImplicitStep_le_of_paperBarrier_maxPrinciple_clean
      (p := p) (c := c) (h := 1 / lam) (M := M) (C_chem := C_chem)
      (u := u) (Z := Z) (W := W) (B := B) (La := hd.La) (Lb := hd.Lb)
      (one_div_pos.mpr hlam) hd.hCB hstep hd.ZB hd.φcont
      hd.hbot hd.hLa hd.htop hd.hLb hd.paperSuper hd.paperDiff

theorem paperStep_ge_lower
    {p : CMParams} {M C_chem : ℝ} {u Z W A : ℝ → ℝ}
    (hlam : 0 < lam)
    (hstep : ∀ x, paperImplicitStepOp p c (1 / lam) u W x = Z x)
    (hd : PaperStepLowerData p c lam M C_chem u Z W A) :
    ∀ x, A x ≤ W x := by
  exact
    implicitStep_ge_of_paperBarrier_maxPrinciple_clean
      (p := p) (c := c) (h := 1 / lam) (M := M) (C_chem := C_chem)
      (u := u) (Z := Z) (W := W) (A := A) (La := hd.La) (Lb := hd.Lb)
      (one_div_pos.mpr hlam) hd.hCB hstep hd.AZ hd.φcont
      hd.hbot hd.hLa hd.htop hd.hLb hd.paperSub hd.paperDiff

/-! ## Non-circular truncated-operator barriers -/

/-- Upper-barrier maximum principle for the spatially truncated paper operator.

This is the non-circular comparison used before clamp inactivity is known.  At
a positive maximum of `W - upperBarrier κ M`, the clamp equals the barrier value,
the first derivatives agree, and the second derivative of `W` is no larger than
the barrier's.  Hence the truncated operator at `W` is no larger than the genuine
paper operator at the barrier; `paperSuper` and `Z ≤ upperBarrier` give the
contradiction. -/
theorem paperImplicitStep_truncated_le_of_paperBarrier
    {p : CMParams} {M κ C_chem : ℝ} {u Z W : ℝ → ℝ}
    (hlam : 0 < lam) (hκ : 0 < κ) (hM : 0 < M)
    (hstep :
      ∀ x, paperImplicitStepOp_truncated p c (1 / lam) M κ u W x = Z x)
    (hWC2 : ∀ x, ContDiffAt ℝ 2 W x)
    (hd : PaperStepUpperTruncatedData p c lam M C_chem u Z W (upperBarrier κ M)) :
    ∀ x, W x ≤ upperBarrier κ M x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x₁, hx₁⟩ := hcon
  have hpos₁ : 0 < W x₁ - upperBarrier κ M x₁ := by
    linarith
  obtain ⟨x₀, hattain, hx₀pos⟩ :=
    exists_isMaxOn_pos_of_tendsto_nonpos
      (φ := fun x => W x - upperBarrier κ M x)
      hd.φcont hd.hbot hd.hLa hd.htop hd.hLb hpos₁
  have hloc : IsLocalMax (fun x => W x - upperBarrier κ M x) x₀ :=
    hattain.isLocalMax Filter.univ_mem
  have hWdiff_all : Differentiable ℝ W := by
    intro x
    exact (hWC2 x).differentiableAt (by norm_num)
  have hBC2₀ : ContDiffAt ℝ 2 (upperBarrier κ M) x₀ :=
    upperBarrier_BC2_atMax_dischargeable hκ hM hWdiff_all x₀ hattain
  have hderiv2 :
      iteratedDeriv 2 W x₀ ≤ iteratedDeriv 2 (upperBarrier κ M) x₀ :=
    iteratedDeriv2_le_of_isLocalMax_sub (hWC2 x₀) hBC2₀ hloc
  have hWdiff : DifferentiableAt ℝ W x₀ :=
    (hWC2 x₀).differentiableAt (by norm_num)
  have hBdiff : DifferentiableAt ℝ (upperBarrier κ M) x₀ :=
    hBC2₀.differentiableAt (by norm_num)
  have hφderiv :
      deriv (fun x => W x - upperBarrier κ M x) x₀ = 0 :=
    hloc.deriv_eq_zero
  have hderiv_sub :
      deriv (fun x => W x - upperBarrier κ M x) x₀ =
        deriv W x₀ - deriv (upperBarrier κ M) x₀ :=
    deriv_sub hWdiff hBdiff
  have hderiv1 : deriv W x₀ = deriv (upperBarrier κ M) x₀ := by
    rw [hderiv_sub] at hφderiv
    linarith
  have hBW : upperBarrier κ M x₀ ≤ W x₀ := by
    linarith
  have hclamp :
      paperWeightedClamp κ M W x₀ = upperBarrier κ M x₀ :=
    paperWeightedClamp_eq_upperBarrier_of_upper_le
      (κ := κ) (M := M) (W := W) hM.le hBW
  have hNL :
      paperStepTruncatedNonlinearity p c M κ u W x₀ =
        paperStepNonlinearity p u (upperBarrier κ M) x₀ := by
    unfold paperStepTruncatedNonlinearity paperStepNonlinearity
    dsimp only
    rw [hclamp, hderiv1]
  have hAtrunc_le :
      paperWaveOperator_truncated p c M κ u W x₀
        ≤ paperWaveOperator p c u (upperBarrier κ M) x₀ := by
    calc
      paperWaveOperator_truncated p c M κ u W x₀
          = iteratedDeriv 2 W x₀ + c * deriv W x₀ +
              paperStepNonlinearity p u (upperBarrier κ M) x₀ := by
              unfold paperWaveOperator_truncated
              rw [hNL]
      _ ≤ iteratedDeriv 2 (upperBarrier κ M) x₀ +
            c * deriv (upperBarrier κ M) x₀ +
              paperStepNonlinearity p u (upperBarrier κ M) x₀ := by
              rw [hderiv1]
              linarith
      _ = paperWaveOperator p c u (upperBarrier κ M) x₀ := by
              rw [paperWaveOperator_eq_linear_add_paperStepNonlinearity]
  have hAtrunc_nonpos :
      paperWaveOperator_truncated p c M κ u W x₀ ≤ 0 :=
    le_trans hAtrunc_le (hd.paperSuper x₀ hattain)
  have hGW :
      W x₀ -
          (1 / lam) * paperWaveOperator_truncated p c M κ u W x₀ =
        Z x₀ := by
    simpa [paperImplicitStepOp_truncated_apply] using hstep x₀
  have hWleZ : W x₀ ≤ Z x₀ := by
    have hmul :
        (1 / lam) * paperWaveOperator_truncated p c M κ u W x₀ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (one_div_pos.mpr hlam).le hAtrunc_nonpos
    linarith
  have hx₀gt : upperBarrier κ M x₀ < W x₀ := by
    linarith
  exact not_lt_of_ge (le_trans hWleZ (hd.ZB x₀)) hx₀gt

/-- Lower maximum principle for the spatially truncated paper operator against
the zero barrier.

At a negative minimum of `W`, the clamp is zero, `W' = 0`, and `W'' ≥ 0`; the
truncated nonlinearity vanishes, so the truncated operator is nonnegative.  The
implicit equation would then force `Z < 0`, contradicting `0 ≤ Z`. -/
theorem paperImplicitStep_truncated_ge_zero
    {p : CMParams} {M κ C_chem : ℝ} {u Z W : ℝ → ℝ}
    (hlam : 0 < lam) (hM : 0 ≤ M)
    (hstep :
      ∀ x, paperImplicitStepOp_truncated p c (1 / lam) M κ u W x = Z x)
    (hWC2 : ∀ x, ContDiffAt ℝ 2 W x)
    (hd : PaperStepLowerTruncatedData p c lam M C_chem u Z W (fun _ => 0)) :
    ∀ x, 0 ≤ W x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x₁, hx₁⟩ := hcon
  have hpos₁ : 0 < (fun _ : ℝ => (0 : ℝ)) x₁ - W x₁ := by
    linarith
  obtain ⟨x₀, hattain, hx₀pos⟩ :=
    exists_isMaxOn_pos_of_tendsto_nonpos
      (φ := fun x => (fun _ : ℝ => (0 : ℝ)) x - W x)
      hd.φcont hd.hbot hd.hLa hd.htop hd.hLb hpos₁
  have hloc : IsLocalMax (fun x => (fun _ : ℝ => (0 : ℝ)) x - W x) x₀ :=
    hattain.isLocalMax Filter.univ_mem
  have hAC2 : ContDiffAt ℝ 2 (fun _ : ℝ => (0 : ℝ)) x₀ := contDiffAt_const
  have hderiv2 :
      iteratedDeriv 2 (fun _ : ℝ => (0 : ℝ)) x₀ ≤ iteratedDeriv 2 W x₀ :=
    iteratedDeriv2_le_of_isLocalMax_sub hAC2 (hWC2 x₀) hloc
  have hzero2 : iteratedDeriv 2 (fun _ : ℝ => (0 : ℝ)) x₀ = 0 := by
    simp
  have hWpp_nonneg : 0 ≤ iteratedDeriv 2 W x₀ := by
    rwa [hzero2] at hderiv2
  have hWdiff : DifferentiableAt ℝ W x₀ :=
    (hWC2 x₀).differentiableAt (by norm_num)
  have hAdiff : DifferentiableAt ℝ (fun _ : ℝ => (0 : ℝ)) x₀ :=
    hAC2.differentiableAt (by norm_num)
  have hφderiv :
      deriv (fun x => (fun _ : ℝ => (0 : ℝ)) x - W x) x₀ = 0 :=
    hloc.deriv_eq_zero
  have hderiv_sub :
      deriv (fun x => (fun _ : ℝ => (0 : ℝ)) x - W x) x₀ =
        deriv (fun _ : ℝ => (0 : ℝ)) x₀ - deriv W x₀ :=
    deriv_sub hAdiff hWdiff
  have hWderiv_zero : deriv W x₀ = 0 := by
    rw [hderiv_sub, deriv_const] at hφderiv
    linarith
  have hWneg : W x₀ < 0 := by
    simpa using hx₀pos
  have hclamp : paperWeightedClamp κ M W x₀ = 0 :=
    paperWeightedClamp_eq_zero_of_nonpos
      (κ := κ) (M := M) (W := W) hM (le_of_lt hWneg)
  have hNL_zero :
      paperStepTruncatedNonlinearity p c M κ u W x₀ = 0 := by
    unfold paperStepTruncatedNonlinearity
    dsimp only
    rw [hclamp, hWderiv_zero]
    ring
  have hAtrunc_nonneg :
      0 ≤ paperWaveOperator_truncated p c M κ u W x₀ := by
    unfold paperWaveOperator_truncated
    rw [hNL_zero, hWderiv_zero]
    linarith
  have hGW :
      W x₀ -
          (1 / lam) * paperWaveOperator_truncated p c M κ u W x₀ =
        Z x₀ := by
    simpa [paperImplicitStepOp_truncated_apply] using hstep x₀
  have hZleW : Z x₀ ≤ W x₀ := by
    have hmul :
        0 ≤ (1 / lam) * paperWaveOperator_truncated p c M κ u W x₀ :=
      mul_nonneg (one_div_pos.mpr hlam).le hAtrunc_nonneg
    linarith
  have hZnonneg : 0 ≤ Z x₀ := hd.AZ x₀
  linarith

/-- Compatibility wrapper from the full upper comparison record. -/
theorem paperImplicitStep_truncated_le_of_paperBarrier_full
    {p : CMParams} {M κ C_chem : ℝ} {u Z W : ℝ → ℝ}
    (hlam : 0 < lam) (hκ : 0 < κ) (hM : 0 < M)
    (hstep :
      ∀ x, paperImplicitStepOp_truncated p c (1 / lam) M κ u W x = Z x)
    (hWC2 : ∀ x, ContDiffAt ℝ 2 W x)
    (hd : PaperStepUpperData p c lam M C_chem u Z W (upperBarrier κ M)) :
    ∀ x, W x ≤ upperBarrier κ M x :=
  paperImplicitStep_truncated_le_of_paperBarrier
    (c := c) (lam := lam) (p := p) (M := M) (κ := κ)
    (C_chem := C_chem) (u := u) (Z := Z) (W := W)
    hlam hκ hM hstep hWC2 hd.toTruncated

/-- Compatibility wrapper from the full lower comparison record. -/
theorem paperImplicitStep_truncated_ge_zero_full
    {p : CMParams} {M κ C_chem : ℝ} {u Z W : ℝ → ℝ}
    (hlam : 0 < lam) (hM : 0 ≤ M)
    (hstep :
      ∀ x, paperImplicitStepOp_truncated p c (1 / lam) M κ u W x = Z x)
    (hWC2 : ∀ x, ContDiffAt ℝ 2 W x)
    (hd : PaperStepLowerData p c lam M C_chem u Z W (fun _ => 0)) :
    ∀ x, 0 ≤ W x :=
  paperImplicitStep_truncated_ge_zero
    (c := c) (lam := lam) (p := p) (M := M) (κ := κ)
    (C_chem := C_chem) (u := u) (Z := Z) (W := W)
    hlam hM hstep hWC2 hd.toTruncated

/-- Clamp inactivity for a fixed point of the truncated source map, obtained
from the two truncated max-principles above. -/
theorem paperFixedSource_truncation_inactive_direct_of_trap
    {p : CMParams} {M κ β B H C_chem : ℝ} {ω : ℝ → ℝ} {u Z R : ℝ → ℝ}
    (hlam : 0 < lam) (hκ : 0 < κ) (hM : 0 < M) (hBnn : 0 ≤ B)
    (hR : PaperWeightedHolderSourceBox κ M β B H ω R)
    (hRfix : paperFixedSourceMap p c lam M κ u Z R = R)
    (hlower :
      PaperStepLowerTruncatedData p c lam M C_chem u Z
        (fun x => greenConv c lam R x) (fun _ => 0))
    (hupper :
      PaperStepUpperTruncatedData p c lam M C_chem u Z
        (fun x => greenConv c lam R x) (upperBarrier κ M)) :
    ∀ x,
      (fun y => greenConv c lam R y) x ∈
        Set.Icc (0 : ℝ) (upperBarrier κ M x) := by
  have hR_const : ∀ y, |R y| ≤ B * M := by
    intro y
    calc
      |R y| ≤ B * upperBarrier κ M y := hR.bound y
      _ ≤ B * M :=
        mul_le_mul_of_nonneg_left (upperBarrier_le_M κ M y) hBnn
  have hHi : ∀ t,
      IntegrableOn (gWeight (greenRootPlus c lam) R) (Ioi t) :=
    fun t => gWeight_integrableOn_Ioi_of_bounded
      (greenRootPlus_pos (c := c) hlam) hR.cont hR_const t
  have hLo : ∀ t,
      IntegrableOn (gWeight (greenRootMinus c lam) R) (Iic t) :=
    fun t => gWeight_integrableOn_Iic_of_bounded
      (greenRootMinus_neg (c := c) hlam) hR.cont hR_const t
  have hstep :
      ∀ x,
        paperImplicitStepOp_truncated p c (1 / lam) M κ u
            (fun y => greenConv c lam R y) x = Z x :=
    paperImplicitStepOp_truncated_of_green_fixed_source
      (c := c) (lam := lam) (p := p) (M := M) (κ := κ)
      (u := u) (Z := Z) (R := R) hlam hRfix.symm hR.cont hHi hLo
  have hWC2 :
      ∀ x, ContDiffAt ℝ 2 (fun y => greenConv c lam R y) x :=
    greenConv_contDiffAt_two (c := c) (lam := lam) hR.cont hHi hLo
  have hnonneg :
      ∀ x, 0 ≤ (fun y => greenConv c lam R y) x :=
    paperImplicitStep_truncated_ge_zero
      (c := c) (lam := lam) (p := p) (M := M) (κ := κ)
      (C_chem := C_chem) (u := u) (Z := Z)
      (W := fun y => greenConv c lam R y)
      hlam hM.le hstep hWC2 hlower
  have hle :
      ∀ x,
        (fun y => greenConv c lam R y) x ≤ upperBarrier κ M x :=
    paperImplicitStep_truncated_le_of_paperBarrier
      (c := c) (lam := lam) (p := p) (M := M) (κ := κ)
      (C_chem := C_chem) (u := u) (Z := Z)
      (W := fun y => greenConv c lam R y)
      hlam hκ hM hstep hWC2 hupper
  intro x
  exact ⟨hnonneg x, hle x⟩

/-- Compatibility wrapper for callers that still construct the full comparison
records. -/
theorem paperFixedSource_truncation_inactive_of_barriers
    {p : CMParams} {M κ β B H C_chem : ℝ} {ω : ℝ → ℝ} {u Z R : ℝ → ℝ}
    (hlam : 0 < lam) (hκ : 0 < κ) (hM : 0 < M) (hBnn : 0 ≤ B)
    (hR : PaperWeightedHolderSourceBox κ M β B H ω R)
    (hRfix : paperFixedSourceMap p c lam M κ u Z R = R)
    (hlower :
      PaperStepLowerData p c lam M C_chem u Z
        (fun x => greenConv c lam R x) (fun _ => 0))
    (hupper :
      PaperStepUpperData p c lam M C_chem u Z
        (fun x => greenConv c lam R x) (upperBarrier κ M)) :
    ∀ x,
      (fun y => greenConv c lam R y) x ∈
        Set.Icc (0 : ℝ) (upperBarrier κ M x) :=
  paperFixedSource_truncation_inactive_direct_of_trap
    (c := c) (lam := lam) (p := p) (M := M) (κ := κ)
    (β := β) (B := B) (H := H) (C_chem := C_chem) (ω := ω)
    (u := u) (Z := Z) (R := R)
    hlam hκ hM hBnn hR hRfix hlower.toTruncated hupper.toTruncated

def frozenElliptic_holderQuant_of_trap
    (p : CMParams) {κ M β : ℝ} {u : ℝ → ℝ}
    (hM : 0 < M) (hu : InWaveTrapSet κ M u)
    (hβpos : 0 < β) (hβle : β ≤ 1) :
    HolderQuant β (fun x => frozenElliptic p u x) := by
  let C : ℝ := M ^ p.γ
  have hC : 0 ≤ C := Real.rpow_nonneg hM.le p.γ
  have hbound : ∀ x, |frozenElliptic p u x| ≤ C := by
    intro x
    rw [abs_of_nonneg (frozenElliptic_nonneg_of_inWaveTrapSet p hu x)]
    exact frozenElliptic_le_rpow_of_inWaveTrapSet p hM hu x
  have hderiv : ∀ x, |deriv (fun x => frozenElliptic p u x) x| ≤ C := by
    intro x
    calc
      |deriv (fun x => frozenElliptic p u x) x|
          = |deriv (frozenElliptic p u) x| := rfl
      _ ≤ frozenElliptic p u x :=
        frozenElliptic_deriv_abs_le p hu.cunif_bdd hu.nonneg x
      _ ≤ C := frozenElliptic_le_rpow_of_inWaveTrapSet p hM hu x
  have hdiff : Differentiable ℝ (fun x => frozenElliptic p u x) :=
    frozenElliptic_differentiable p hu.cunif_bdd hu.nonneg
  exact HolderQuant.of_lipschitz hβpos hβle hC hC hbound
    (abs_sub_le_of_deriv_abs_le_core hdiff hderiv)

def frozenEllipticDeriv_holderQuant_of_trap
    (p : CMParams) {κ M β : ℝ} {u : ℝ → ℝ}
    (hM : 0 < M) (hu : InWaveTrapSet κ M u)
    (hβpos : 0 < β) (hβle : β ≤ 1) :
    HolderQuant β (fun x => deriv (frozenElliptic p u) x) := by
  let C : ℝ := M ^ p.γ
  let L : ℝ := 2 * C
  have hC : 0 ≤ C := Real.rpow_nonneg hM.le p.γ
  have hL : 0 ≤ L := by positivity
  have huγ_bound : ∀ x, (u x) ^ p.γ ≤ C := by
    intro x
    have huM : u x ≤ M := le_trans (hu.le_upperBarrier x) (upperBarrier_le_M κ M x)
    exact Real.rpow_le_rpow (hu.nonneg x) huM (by linarith [p.hγ])
  have hbound : ∀ x, |deriv (frozenElliptic p u) x| ≤ C := by
    intro x
    calc
      |deriv (frozenElliptic p u) x| ≤ frozenElliptic p u x :=
        frozenElliptic_deriv_abs_le p hu.cunif_bdd hu.nonneg x
      _ ≤ C := frozenElliptic_le_rpow_of_inWaveTrapSet p hM hu x
  have hdiff : Differentiable ℝ (fun x => deriv (frozenElliptic p u) x) := by
    intro x
    exact frozenElliptic_deriv_differentiableAt p hu.cunif_bdd hu.nonneg x
  have hderiv : ∀ x, |deriv (fun x => deriv (frozenElliptic p u) x) x| ≤ L := by
    intro x
    have hV : |frozenElliptic p u x| ≤ C := by
      rw [abs_of_nonneg (frozenElliptic_nonneg_of_inWaveTrapSet p hu x)]
      exact frozenElliptic_le_rpow_of_inWaveTrapSet p hM hu x
    have huγ0 : 0 ≤ (u x) ^ p.γ := Real.rpow_nonneg (hu.nonneg x) p.γ
    have huγabs : |(u x) ^ p.γ| ≤ C := by
      rw [abs_of_nonneg huγ0]
      exact huγ_bound x
    calc
      |deriv (fun x => deriv (frozenElliptic p u) x) x|
          = |deriv (deriv (frozenElliptic p u)) x| := rfl
      _ = |frozenElliptic p u x - (u x) ^ p.γ| := by
        rw [frozenElliptic_deriv_deriv_eq p hu.cunif_bdd hu.nonneg x]
      _ ≤ |frozenElliptic p u x| + |(u x) ^ p.γ| := abs_sub _ _
      _ ≤ C + C := add_le_add hV huγabs
      _ = L := by ring
  exact HolderQuant.of_lipschitz hβpos hβle hC hL hbound
    (abs_sub_le_of_deriv_abs_le_core hdiff hderiv)

def PaperIterateBase.localLipQuant
    {κ M : ℝ} {Z : ℝ → ℝ}
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) (hZ : PaperIterateBase κ M Z) :
    LocalLipQuant Z := by
  let LZ : ℝ := Classical.choose hZ.deriv_le
  have hLZ : 0 ≤ LZ := (Classical.choose_spec hZ.deriv_le).1
  have hderivZ : ∀ x, |deriv Z x| ≤ LZ :=
    (Classical.choose_spec hZ.deriv_le).2
  let LU : ℝ := κ * Real.exp κ * M
  let L : ℝ := max LU LZ
  have hLU : 0 ≤ LU := by positivity
  have hL : 0 ≤ L := le_trans hLU (le_max_left _ _)
  have hbound : ∀ x, |Z x| ≤ M := by
    intro x
    rw [abs_of_nonneg (hZ.nonneg x)]
    exact le_trans (hZ.le_barrier x) (upperBarrier_le_M κ M x)
  have hlocal : ∀ x y, |x - y| ≤ 1 → |Z x - Z y| ≤ L * |x - y| := by
    intro x y hxy
    rcases hZ.diff with hEq | hdiff
    · subst Z
      calc
        |upperBarrier κ M x - upperBarrier κ M y|
            ≤ LU * |x - y| := upperBarrier_abs_sub_le_local hκ hM hxy
        _ ≤ L * |x - y| :=
          mul_le_mul_of_nonneg_right (le_max_left LU LZ) (abs_nonneg _)
    · have hlip := abs_sub_le_of_deriv_abs_le_core hdiff hderivZ x y
      calc
        |Z x - Z y| ≤ LZ * |x - y| := hlip
        _ ≤ L * |x - y| :=
          mul_le_mul_of_nonneg_right (le_max_right LU LZ) (abs_nonneg _)
  exact
    { C := M
      L := L
      C_nonneg := hM
      L_nonneg := hL
      bound := hbound
      local_lip := hlocal }

def PaperIterateBase.holderQuant
    {κ M β : ℝ} {Z : ℝ → ℝ}
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) (hZ : PaperIterateBase κ M Z)
    (hβpos : 0 < β) (hβle : β ≤ 1) :
    HolderQuant β Z :=
  (hZ.localLipQuant hκ hM).toHolder hβpos hβle

/-! ### Left-tail Cauchy bookkeeping for fixed-source kernel estimates -/

/-- A real function with a uniform absolute bound and an explicit left-tail
Cauchy modulus. -/
structure LeftTailQuant (f : ℝ → ℝ) where
  C : ℝ
  ω : ℝ → ℝ
  C_nonneg : 0 ≤ C
  ω_nonneg : ∀ A, 0 ≤ ω A
  ω_tendsto : Tendsto ω atBot (𝓝 0)
  bound : ∀ x, |f x| ≤ C
  cauchy : ∀ A x y, x ≤ A → y ≤ A → |f x - f y| ≤ ω A

theorem antitone_abs_sub_limit_le_atBot
    {f : ℝ → ℝ} {L : ℝ}
    (hanti : Antitone f) (hlim : Tendsto f atBot (𝓝 L)) :
    ∀ A x, x ≤ A → |f x - L| ≤ |f A - L| := by
  have hleL : ∀ z, f z ≤ L := by
    intro z
    have hev : ∀ᶠ y in atBot, f z ≤ f y := by
      filter_upwards [eventually_le_atBot z] with y hy
      exact hanti hy
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim hev
  intro A x hx
  have hxL : f x - L ≤ 0 := sub_nonpos.mpr (hleL x)
  have hAL : f A - L ≤ 0 := sub_nonpos.mpr (hleL A)
  have hAf : f A ≤ f x := hanti hx
  rw [abs_of_nonpos hxL, abs_of_nonpos hAL]
  linarith

namespace LeftTailQuant

def const (a : ℝ) : LeftTailQuant (fun _ : ℝ => a) where
  C := |a|
  ω := fun _ => 0
  C_nonneg := abs_nonneg a
  ω_nonneg := by intro A; norm_num
  ω_tendsto := tendsto_const_nhds
  bound := by intro x; simp
  cauchy := by intro A x y hx hy; simp

def add {f g : ℝ → ℝ}
    (hf : LeftTailQuant f) (hg : LeftTailQuant g) :
    LeftTailQuant (fun x => f x + g x) where
  C := hf.C + hg.C
  ω := fun A => hf.ω A + hg.ω A
  C_nonneg := add_nonneg hf.C_nonneg hg.C_nonneg
  ω_nonneg := by intro A; exact add_nonneg (hf.ω_nonneg A) (hg.ω_nonneg A)
  ω_tendsto := by
    simpa using hf.ω_tendsto.add hg.ω_tendsto
  bound := by
    intro x
    calc
      |f x + g x| ≤ |f x| + |g x| := abs_add_le _ _
      _ ≤ hf.C + hg.C := add_le_add (hf.bound x) (hg.bound x)
  cauchy := by
    intro A x y hx hy
    calc
      |(f x + g x) - (f y + g y)|
          = |(f x - f y) + (g x - g y)| := by ring_nf
      _ ≤ |f x - f y| + |g x - g y| := abs_add_le _ _
      _ ≤ hf.ω A + hg.ω A :=
        add_le_add (hf.cauchy A x y hx hy) (hg.cauchy A x y hx hy)

def neg {f : ℝ → ℝ} (hf : LeftTailQuant f) :
    LeftTailQuant (fun x => -f x) where
  C := hf.C
  ω := hf.ω
  C_nonneg := hf.C_nonneg
  ω_nonneg := hf.ω_nonneg
  ω_tendsto := hf.ω_tendsto
  bound := by intro x; simpa using hf.bound x
  cauchy := by
    intro A x y hx hy
    have hdiff : (-f x) - (-f y) = -(f x - f y) := by ring
    rw [hdiff, abs_neg]
    exact hf.cauchy A x y hx hy

def sub {f g : ℝ → ℝ}
    (hf : LeftTailQuant f) (hg : LeftTailQuant g) :
    LeftTailQuant (fun x => f x - g x) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

def const_mul {a : ℝ} {f : ℝ → ℝ} (hf : LeftTailQuant f) :
    LeftTailQuant (fun x => a * f x) where
  C := |a| * hf.C
  ω := fun A => |a| * hf.ω A
  C_nonneg := mul_nonneg (abs_nonneg a) hf.C_nonneg
  ω_nonneg := by intro A; exact mul_nonneg (abs_nonneg a) (hf.ω_nonneg A)
  ω_tendsto := by
    simpa using hf.ω_tendsto.const_mul |a|
  bound := by
    intro x
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hf.bound x) (abs_nonneg a)
  cauchy := by
    intro A x y hx hy
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left (hf.cauchy A x y hx hy) (abs_nonneg a)

def mul {f g : ℝ → ℝ}
    (hf : LeftTailQuant f) (hg : LeftTailQuant g) :
    LeftTailQuant (fun x => f x * g x) where
  C := hf.C * hg.C
  ω := fun A => hf.C * hg.ω A + hg.C * hf.ω A
  C_nonneg := mul_nonneg hf.C_nonneg hg.C_nonneg
  ω_nonneg := by
    intro A
    exact add_nonneg
      (mul_nonneg hf.C_nonneg (hg.ω_nonneg A))
      (mul_nonneg hg.C_nonneg (hf.ω_nonneg A))
  ω_tendsto := by
    have h1 := hg.ω_tendsto.const_mul hf.C
    have h2 := hf.ω_tendsto.const_mul hg.C
    simpa using h1.add h2
  bound := by
    intro x
    rw [abs_mul]
    exact mul_le_mul (hf.bound x) (hg.bound x)
      (abs_nonneg _) hf.C_nonneg
  cauchy := by
    intro A x y hx hy
    have hsplit :
        f x * g x - f y * g y =
          f x * (g x - g y) + g y * (f x - f y) := by ring
    rw [hsplit]
    calc
      |f x * (g x - g y) + g y * (f x - f y)|
          ≤ |f x * (g x - g y)| + |g y * (f x - f y)| := abs_add_le _ _
      _ = |f x| * |g x - g y| + |g y| * |f x - f y| := by
        rw [abs_mul, abs_mul]
      _ ≤ hf.C * hg.ω A + hg.C * hf.ω A := by
        exact add_le_add
          (mul_le_mul (hf.bound x) (hg.cauchy A x y hx hy)
            (abs_nonneg _) hf.C_nonneg)
          (mul_le_mul (hg.bound y) (hf.cauchy A x y hx hy)
            (abs_nonneg _) hg.C_nonneg)

def of_antitone_tendsto
    {f : ℝ → ℝ} {C L : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ x, |f x| ≤ C)
    (hanti : Antitone f) (hlim : Tendsto f atBot (𝓝 L)) :
    LeftTailQuant f where
  C := C
  ω := fun A => 2 * |f A - L|
  C_nonneg := hC
  ω_nonneg := by intro A; positivity
  ω_tendsto := by
    have hsub : Tendsto (fun A => f A - L) atBot (𝓝 0) := by
      have hconst : Tendsto (fun _ : ℝ => L) atBot (𝓝 L) :=
        tendsto_const_nhds
      have h := hlim.sub hconst
      simpa using h
    simpa using hsub.abs.const_mul 2
  bound := hbound
  cauchy := by
    intro A x y hx hy
    have hxA := antitone_abs_sub_limit_le_atBot hanti hlim A x hx
    have hyA := antitone_abs_sub_limit_le_atBot hanti hlim A y hy
    calc
      |f x - f y| = |(f x - L) + (L - f y)| := by ring_nf
      _ ≤ |f x - L| + |L - f y| := abs_add_le _ _
      _ = |f x - L| + |f y - L| := by rw [abs_sub_comm L (f y)]
      _ ≤ |f A - L| + |f A - L| := add_le_add hxA hyA
      _ = 2 * |f A - L| := by ring

def rpow_lipschitz_on_Icc
    {a M : ℝ} {f : ℝ → ℝ}
    (hf : LeftTailQuant f) (ha : 1 ≤ a) (hM : 0 ≤ M)
    (hrange : ∀ x, f x ∈ Set.Icc (0 : ℝ) M) :
    LeftTailQuant (fun x => (f x) ^ a) where
  C := M ^ a
  ω := fun A => rpowLip a M * hf.ω A
  C_nonneg := Real.rpow_nonneg hM a
  ω_nonneg := by
    intro A
    exact mul_nonneg (rpowLip_nonneg ha hM) (hf.ω_nonneg A)
  ω_tendsto := by
    simpa using hf.ω_tendsto.const_mul (rpowLip a M)
  bound := by
    intro x
    have hx := hrange x
    have hpownn : 0 ≤ (f x) ^ a := Real.rpow_nonneg hx.1 a
    rw [abs_of_nonneg hpownn]
    exact Real.rpow_le_rpow hx.1 hx.2 (by linarith)
  cauchy := by
    intro A x y hx hy
    have hL0 : 0 ≤ rpowLip a M := rpowLip_nonneg ha hM
    calc
      |(f x) ^ a - (f y) ^ a|
          ≤ rpowLip a M * |f x - f y| :=
        rpow_abs_sub_le_lip_on_Icc ha hM (hrange x) (hrange y)
      _ ≤ rpowLip a M * hf.ω A :=
        mul_le_mul_of_nonneg_left (hf.cauchy A x y hx hy) hL0

def rpow_selfHolderOnIcc
    {β M : ℝ} {f : ℝ → ℝ}
    (hf : LeftTailQuant f) (hβpos : 0 < β) (hβle : β ≤ 1)
    (hM : 0 ≤ M) (hrange : ∀ x, f x ∈ Set.Icc (0 : ℝ) M) :
    LeftTailQuant (fun x => (f x) ^ β) where
  C := M ^ β
  ω := fun A => (hf.ω A) ^ β
  C_nonneg := Real.rpow_nonneg hM β
  ω_nonneg := by intro A; exact Real.rpow_nonneg (hf.ω_nonneg A) β
  ω_tendsto := by
    have h := hf.ω_tendsto.rpow_const (Or.inr hβpos.le)
    simpa [Real.zero_rpow (ne_of_gt hβpos)] using h
  bound := by
    intro x
    have hx := hrange x
    have hpownn : 0 ≤ (f x) ^ β := Real.rpow_nonneg hx.1 β
    rw [abs_of_nonneg hpownn]
    exact Real.rpow_le_rpow hx.1 hx.2 hβpos.le
  cauchy := by
    intro A x y hx hy
    have hpow :
        |(f x) ^ β - (f y) ^ β| ≤ |f x - f y| ^ β :=
      rpow_abs_sub_le_abs_sub_rpow hβpos.le hβle (hrange x).1 (hrange y).1
    have hmod : |f x - f y| ^ β ≤ (hf.ω A) ^ β :=
      Real.rpow_le_rpow (abs_nonneg _) (hf.cauchy A x y hx hy) hβpos.le
    exact le_trans hpow hmod

end LeftTailQuant

theorem paperFixedSourceMap_holder_kernel
    (p : CMParams) {c lam M κ B Hbox : ℝ} {ω : ℝ → ℝ} {u Z : ℝ → ℝ}
    (hlam : 0 < lam)
    (hrpκ : κ < greenRootPlus c lam)
    (hrmκ : κ < -greenRootMinus c lam)
    (hκ : 0 ≤ κ) (hM : 0 < M) (hBnn : 0 ≤ B)
    (hu : InWaveTrapSet κ M u)
    (hZ : PaperIterateBase κ M Z) :
    ∃ H0 : ℝ, 0 ≤ H0 ∧
      ∀ R, PaperWeightedHolderSourceBox κ M (paperWeightedHolderExponent p) B Hbox ω R →
        ∀ x y,
          |paperFixedSourceMap p c lam M κ u Z R x -
              paperFixedSourceMap p c lam M κ u Z R y| ≤
            H0 * |x - y| ^ paperWeightedHolderExponent p := by
  let β : ℝ := paperWeightedHolderExponent p
  have hβpos : 0 < β := by
    dsimp [β]
    exact paperWeightedHolderExponent_pos p
  have hβle : β ≤ 1 := by
    dsimp [β]
    exact paperWeightedHolderExponent_le_one p
  let BM : ℝ := B * M
  let Cw : ℝ := greenWeightedMass0 c lam κ * BM
  let Lw : ℝ := greenWeightedMass1 c lam κ * BM
  let Cwd : ℝ := greenWeightedMass1 c lam κ * BM
  let Lwd : ℝ := BM + |c| * Cwd + lam * Cw
  let LU : ℝ := κ * Real.exp κ * M
  let Lθ : ℝ := LU + Lw
  let CV : ℝ := M ^ p.γ
  let LZ : ℝ := Classical.choose hZ.deriv_le
  let LZloc : ℝ := max LU LZ
  let bΘ : HolderBudget :=
    { C := M
      H := max Lθ (2 * M)
      C_nonneg := hM.le
      H_nonneg := by
        have hmass1 : 0 ≤ greenWeightedMass1 c lam κ :=
          greenWeightedMass1_nonneg (c := c) (lam := lam) hlam hrpκ hrmκ
        have hBM : 0 ≤ BM := by dsimp [BM]; positivity
        have hLw : 0 ≤ Lw := by dsimp [Lw]; positivity
        have hLU : 0 ≤ LU := by dsimp [LU]; positivity
        exact le_trans (add_nonneg hLU hLw) (le_max_left _ _) }
  let bWd : HolderBudget :=
    { C := Cwd
      H := max Lwd (2 * Cwd)
      C_nonneg := by
        have hmass1 : 0 ≤ greenWeightedMass1 c lam κ :=
          greenWeightedMass1_nonneg (c := c) (lam := lam) hlam hrpκ hrmκ
        dsimp [Cwd, BM]
        positivity
      H_nonneg := by
        have hmass0 : 0 ≤ greenWeightedMass0 c lam κ :=
          greenWeightedMass0_nonneg (c := c) (lam := lam) hlam hrpκ hrmκ
        have hmass1 : 0 ≤ greenWeightedMass1 c lam κ :=
          greenWeightedMass1_nonneg (c := c) (lam := lam) hlam hrpκ hrmκ
        have hBM : 0 ≤ BM := by dsimp [BM]; positivity
        have hCw : 0 ≤ Cw := by dsimp [Cw]; positivity
        have hCwd : 0 ≤ Cwd := by dsimp [Cwd]; positivity
        have hLwd : 0 ≤ Lwd := by dsimp [Lwd, BM]; positivity
        exact le_trans hLwd (le_max_left _ _) }
  let bV : HolderBudget :=
    { C := CV
      H := max CV (2 * CV)
      C_nonneg := by dsimp [CV]; positivity
      H_nonneg := by
        have hCV : 0 ≤ CV := by dsimp [CV]; positivity
        exact le_trans hCV (le_max_left _ _) }
  let bVd : HolderBudget :=
    { C := CV
      H := max (2 * CV) (2 * CV)
      C_nonneg := by dsimp [CV]; positivity
      H_nonneg := by
        have hCV : 0 ≤ CV := by dsimp [CV]; positivity
        exact le_trans (by positivity : 0 ≤ 2 * CV) (le_max_left _ _) }
  let bZ : HolderBudget :=
    { C := M
      H := max LZloc (2 * M)
      C_nonneg := hM.le
      H_nonneg := by
        have hLU : 0 ≤ LU := by dsimp [LU]; positivity
        have hLZ : 0 ≤ LZ := (Classical.choose_spec hZ.deriv_le).1
        have hLZloc : 0 ≤ LZloc := by dsimp [LZloc]; exact le_trans hLU (le_max_left _ _)
        exact le_trans hLZloc (le_max_left _ _) }
  let Hself_m1 : ℝ := max (Lθ ^ β) (2 * M ^ β)
  let Hlip_m1 : ℝ := rpowLip (p.m - 1) M * bΘ.H
  let bm1 : HolderBudget :=
    { C := M ^ (p.m - 1)
      H := max Hself_m1 Hlip_m1
      C_nonneg := by positivity
      H_nonneg := by
        have hLθ : 0 ≤ Lθ := by
          have hmass1 : 0 ≤ greenWeightedMass1 c lam κ :=
            greenWeightedMass1_nonneg (c := c) (lam := lam) hlam hrpκ hrmκ
          dsimp [Lθ, LU, Lw, BM]
          positivity
        have hself : 0 ≤ Hself_m1 := by
          dsimp [Hself_m1]
          exact le_trans (Real.rpow_nonneg hLθ β) (le_max_left _ _)
        exact le_trans hself (le_max_left _ _) }
  let bα : HolderBudget :=
    { C := M ^ p.α
      H := rpowLip p.α M * bΘ.H
      C_nonneg := by positivity
      H_nonneg := by
        have hLip : 0 ≤ rpowLip p.α M := rpowLip_nonneg p.hα hM.le
        exact mul_nonneg hLip bΘ.H_nonneg }
  let bmg : HolderBudget :=
    { C := M ^ (p.m + p.γ - 1)
      H := rpowLip (p.m + p.γ - 1) M * bΘ.H
      C_nonneg := by positivity
      H_nonneg := by
        have hpow : 1 ≤ p.m + p.γ - 1 := by linarith [p.hm, p.hγ]
        have hLip : 0 ≤ rpowLip (p.m + p.γ - 1) M := rpowLip_nonneg hpow hM.le
        exact mul_nonneg hLip bΘ.H_nonneg }
  let bChem : HolderBudget :=
    HolderBudget.const_mul (-p.χ * p.m) ((bm1.mul bVd).mul bWd)
  let bInner : HolderBudget :=
    (HolderBudget.const 1).sub
      (HolderBudget.const_mul p.χ (bm1.mul bV)) |>.sub
      (bα.sub (HolderBudget.const_mul p.χ bmg))
  let bReact : HolderBudget := bΘ.mul bInner
  let bLin : HolderBudget := HolderBudget.const_mul lam bZ
  let bTotal : HolderBudget := (bChem.add bReact).add bLin
  refine ⟨bTotal.H, bTotal.H_nonneg, ?_⟩
  intro R hR x y
  let W : ℝ → ℝ := fun z => greenConv c lam R z
  let Θ : ℝ → ℝ := fun z => paperWeightedClamp κ M W z
  let hWloc : LocalLipQuant W := by
    simpa [W, BM, Cw, Lw] using
      PaperWeightedHolderSourceBox.greenConv_localLipQuant
        (c := c) (lam := lam) (β := β) (Hbox := Hbox) (ω := ω)
        hlam hrpκ hrmκ hκ hM.le hBnn hR
  let hΘloc : LocalLipQuant Θ := by
    simpa [Θ, W, LU, Lθ, BM, Cw, Lw] using
      paperWeightedClamp_localLipQuant (κ := κ) (M := M) (W := W)
        hM.le (upperBarrier_localLipQuant hκ hM.le) hWloc
  have hΘrange : ∀ z, Θ z ∈ Set.Icc (0 : ℝ) M := by
    intro z
    have hz := paperWeightedClamp_mem_Icc (κ := κ) (M := M) (W := W) hM.le z
    exact ⟨hz.1, le_trans hz.2 (upperBarrier_le_M κ M z)⟩
  let hΘQ : HolderQuant β Θ := by
    exact (hΘloc.toHolder hβpos hβle).inflate bΘ.C_nonneg bΘ.H_nonneg
      (by dsimp [hΘloc, bΘ]; rfl)
      (by dsimp [hΘloc, bΘ, Lθ]; rfl)
  let hVQ : HolderQuant β (fun z => frozenElliptic p u z) := by
    exact (frozenElliptic_holderQuant_of_trap p hM hu hβpos hβle).inflate
      bV.C_nonneg bV.H_nonneg
      (by dsimp [frozenElliptic_holderQuant_of_trap, bV, CV]; rfl)
      (by dsimp [frozenElliptic_holderQuant_of_trap, bV, CV]; rfl)
  let hVdQ : HolderQuant β (fun z => deriv (frozenElliptic p u) z) := by
    exact (frozenEllipticDeriv_holderQuant_of_trap p hM hu hβpos hβle).inflate
      bVd.C_nonneg bVd.H_nonneg
      (by dsimp [frozenEllipticDeriv_holderQuant_of_trap, bVd, CV]; rfl)
      (by dsimp [frozenEllipticDeriv_holderQuant_of_trap, bVd, CV]; rfl)
  have hHi := hR.gWeight_Ioi (c := c) (lam := lam) hlam hBnn
  have hLo := hR.gWeight_Iic (c := c) (lam := lam) hlam hBnn
  have hWderiv_eq :
      (fun z => deriv W z) = fun z => greenConvDeriv c lam R z := by
    funext z
    dsimp [W]
    exact (greenConv_hasDerivAt (c := c) (lam := lam) hR.cont hHi hLo z).deriv
  let hWdQ : HolderQuant β (fun z => greenConvDeriv c lam R z) := by
    exact (PaperWeightedHolderSourceBox.greenConvDeriv_holderQuant
        (c := c) (lam := lam) (β := β) (Hbox := Hbox) (ω := ω)
        hlam hrpκ hrmκ hκ hM.le hBnn hβpos hβle hR).inflate
      bWd.C_nonneg bWd.H_nonneg
      (by dsimp [PaperWeightedHolderSourceBox.greenConvDeriv_holderQuant, bWd, BM, Cw, Cwd, Lwd]; rfl)
      (by dsimp [PaperWeightedHolderSourceBox.greenConvDeriv_holderQuant, bWd, BM, Cw, Cwd, Lwd]; rfl)
  let hZQ : HolderQuant β Z := by
    exact (PaperIterateBase.holderQuant hκ hM.le hZ hβpos hβle).inflate
      bZ.C_nonneg bZ.H_nonneg
      (by dsimp [PaperIterateBase.holderQuant, PaperIterateBase.localLipQuant, bZ, LZ, LZloc, LU]; rfl)
      (by dsimp [PaperIterateBase.holderQuant, PaperIterateBase.localLipQuant, bZ, LZ, LZloc, LU]; rfl)
  let hΘm1Q : HolderQuant β (fun z => Θ z ^ (p.m - 1)) := by
    by_cases hm1 : p.m = 1
    · have hfun : (fun z => Θ z ^ (p.m - 1)) = fun _ : ℝ => (1 : ℝ) := by
        funext z
        simp [hm1]
      let hconst : HolderQuant β (fun _ : ℝ => (1 : ℝ)) :=
        (HolderQuant.const β 1).inflate bm1.C_nonneg bm1.H_nonneg
          (by dsimp [HolderQuant.const, bm1]; simp [hm1])
          (by exact bm1.H_nonneg)
      have hconstC : hconst.C = bm1.C := by
        dsimp [hconst, HolderQuant.inflate]
      have hconstH : hconst.H = bm1.H := by
        dsimp [hconst, HolderQuant.inflate]
      refine
        { C := bm1.C
          H := bm1.H
          C_nonneg := bm1.C_nonneg
          H_nonneg := bm1.H_nonneg
          bound := ?_
          holder := ?_ }
      · intro z
        have := hconst.bound z
        simpa [hm1, hconstC] using this
      · intro z z'
        have := hconst.holder z z'
        simpa [hm1, hconstH] using this
    · by_cases hm2 : p.m < 2
      · have hβeq : β = p.m - 1 := by
          dsimp [β, paperWeightedHolderExponent]
          rw [if_neg hm1, if_pos hm2]
        let hinfl : HolderQuant β (fun z => Θ z ^ β) :=
          (hΘloc.rpow_selfHolderOnIcc hβpos hβle hM.le hΘrange).inflate
            bm1.C_nonneg bm1.H_nonneg
            (by
              change M ^ β ≤ M ^ (p.m - 1)
              rw [hβeq])
            (by
              change max (hΘloc.L ^ β) (2 * M ^ β) ≤ max Hself_m1 Hlip_m1
              calc
                max (hΘloc.L ^ β) (2 * M ^ β) = Hself_m1 := by
                  dsimp [Hself_m1, hΘloc, Lθ]
                  rfl
                _ ≤ max Hself_m1 Hlip_m1 := le_max_left _ _)
        have hinflC : hinfl.C = bm1.C := by
          dsimp [hinfl, HolderQuant.inflate]
        have hinflH : hinfl.H = bm1.H := by
          dsimp [hinfl, HolderQuant.inflate]
        refine
          { C := bm1.C
            H := bm1.H
            C_nonneg := bm1.C_nonneg
            H_nonneg := bm1.H_nonneg
            bound := ?_
            holder := ?_ }
        · intro z
          have := hinfl.bound z
          simpa [hβeq, hinflC] using this
        · intro z z'
          have := hinfl.holder z z'
          simpa [hβeq, hinflH] using this
      · have hpow : 1 ≤ p.m - 1 := by linarith
        refine (hΘQ.rpow_lipschitz_on_Icc hpow hM.le hΘrange).inflate
          bm1.C_nonneg bm1.H_nonneg ?_ ?_
        · dsimp [bm1]
          rfl
        · dsimp [bm1, Hlip_m1]
          exact le_max_right Hself_m1 Hlip_m1
  let hΘαQ : HolderQuant β (fun z => Θ z ^ p.α) :=
    (hΘQ.rpow_lipschitz_on_Icc p.hα hM.le hΘrange).inflate
      bα.C_nonneg bα.H_nonneg (by rfl) (by rfl)
  let hΘmgQ : HolderQuant β (fun z => Θ z ^ (p.m + p.γ - 1)) := by
    have hpow : 1 ≤ p.m + p.γ - 1 := by linarith [p.hm, p.hγ]
    exact (hΘQ.rpow_lipschitz_on_Icc hpow hM.le hΘrange).inflate
      bmg.C_nonneg bmg.H_nonneg (by rfl) (by rfl)
  let hChemQ : HolderQuant β (fun z =>
      (-p.χ * p.m) *
        ((Θ z ^ (p.m - 1) * deriv (frozenElliptic p u) z) *
          greenConvDeriv c lam R z)) :=
    HolderQuant.const_mul ((hΘm1Q.mul hVdQ).mul hWdQ)
  let hInnerQ : HolderQuant β (fun z =>
      (1 - p.χ * (Θ z ^ (p.m - 1) * frozenElliptic p u z)) -
        (Θ z ^ p.α - p.χ * Θ z ^ (p.m + p.γ - 1))) :=
    ((HolderQuant.const β 1).sub
      (HolderQuant.const_mul (hΘm1Q.mul hVQ))).sub
      (hΘαQ.sub (HolderQuant.const_mul hΘmgQ))
  let hReactQ : HolderQuant β (fun z => Θ z *
      ((1 - p.χ * (Θ z ^ (p.m - 1) * frozenElliptic p u z)) -
        (Θ z ^ p.α - p.χ * Θ z ^ (p.m + p.γ - 1)))) :=
    hΘQ.mul hInnerQ
  let hLinQ : HolderQuant β (fun z => lam * Z z) :=
    HolderQuant.const_mul hZQ
  let hTotalQ : HolderQuant β (fun z =>
      ((-p.χ * p.m) *
          ((Θ z ^ (p.m - 1) * deriv (frozenElliptic p u) z) *
            greenConvDeriv c lam R z)
        + Θ z *
          ((1 - p.χ * (Θ z ^ (p.m - 1) * frozenElliptic p u z)) -
            (Θ z ^ p.α - p.χ * Θ z ^ (p.m + p.γ - 1))))
        + lam * Z z) :=
    (hChemQ.add hReactQ).add hLinQ
  have hholder := hTotalQ.holder x y
  have hΘC : hΘQ.C = bΘ.C := by
    dsimp [hΘQ, HolderQuant.inflate]
  have hΘH : hΘQ.H = bΘ.H := by
    dsimp [hΘQ, HolderQuant.inflate]
  have hVC : hVQ.C = bV.C := by
    dsimp [hVQ, HolderQuant.inflate]
  have hVH : hVQ.H = bV.H := by
    dsimp [hVQ, HolderQuant.inflate]
  have hVdC : hVdQ.C = bVd.C := by
    dsimp [hVdQ, HolderQuant.inflate]
  have hVdH : hVdQ.H = bVd.H := by
    dsimp [hVdQ, HolderQuant.inflate]
  have hWdC : hWdQ.C = bWd.C := by
    dsimp [hWdQ, HolderQuant.inflate]
  have hWdH : hWdQ.H = bWd.H := by
    dsimp [hWdQ, HolderQuant.inflate]
  have hZC : hZQ.C = bZ.C := by
    dsimp [hZQ, HolderQuant.inflate]
  have hZH : hZQ.H = bZ.H := by
    dsimp [hZQ, HolderQuant.inflate]
  have hΘm1C : hΘm1Q.C = bm1.C := by
    dsimp [hΘm1Q]
    by_cases hm1 : p.m = 1
    · simp [hm1]
    · by_cases hm2 : p.m < 2
      · simp [hm1, hm2]
      · simp [hm1, hm2, HolderQuant.inflate]
  have hΘm1H : hΘm1Q.H = bm1.H := by
    dsimp [hΘm1Q]
    by_cases hm1 : p.m = 1
    · simp [hm1]
    · by_cases hm2 : p.m < 2
      · simp [hm1, hm2]
      · simp [hm1, hm2, HolderQuant.inflate]
  have hΘαC : hΘαQ.C = bα.C := by
    dsimp [hΘαQ, HolderQuant.inflate]
  have hΘαH : hΘαQ.H = bα.H := by
    dsimp [hΘαQ, HolderQuant.inflate]
  have hΘmgC : hΘmgQ.C = bmg.C := by
    dsimp [hΘmgQ, HolderQuant.inflate]
  have hΘmgH : hΘmgQ.H = bmg.H := by
    dsimp [hΘmgQ, HolderQuant.inflate]
  have hHtotal : hTotalQ.H = bTotal.H := by
    dsimp [hTotalQ, hChemQ, hInnerQ, hReactQ, hLinQ,
      bTotal, bChem, bInner, bReact, bLin,
      HolderQuant.add, HolderBudget.add, HolderQuant.mul, HolderBudget.mul,
      HolderQuant.const_mul, HolderBudget.const_mul, HolderQuant.sub,
      HolderBudget.sub, HolderQuant.neg, HolderBudget.neg,
      HolderQuant.const, HolderBudget.const]
    rw [hΘm1C, hΘm1H, hΘC, hΘH, hVC, hVH, hVdC, hVdH,
      hWdC, hWdH, hZH, hΘαC, hΘαH, hΘmgC, hΘmgH]
  rw [hHtotal] at hholder
  have hWdx :
      deriv (fun y => greenConv c lam R y) x = greenConvDeriv c lam R x := by
    simpa [W] using congrArg (fun f : ℝ → ℝ => f x) hWderiv_eq
  have hWdy :
      deriv (fun y => greenConv c lam R y) y = greenConvDeriv c lam R y := by
    simpa [W] using congrArg (fun f : ℝ → ℝ => f y) hWderiv_eq
  unfold paperFixedSourceMap paperStepSource_truncated paperStepTruncatedNonlinearity
  dsimp only [W, Θ, β] at hholder ⊢
  rw [hWdx, hWdy]
  convert hholder using 1
  ring_nf

theorem paperFixedSourceMap_leftTailCauchy_kernel
    (p : CMParams) {c lam M κ B Hbox : ℝ} {ω : ℝ → ℝ} {u Z : ℝ → ℝ}
    (hlam : 0 < lam)
    (hrpκ : κ < greenRootPlus c lam)
    (hrmκ : κ < -greenRootMinus c lam)
    (hκ : 0 ≤ κ) (hM : 0 < M) (hBnn : 0 ≤ B)
    (hu : InMonotoneWaveTrapSet κ M u)
    (hZ : PaperIterateBase κ M Z) :
    ∃ ω0 : ℝ → ℝ,
      (∀ A, 0 ≤ ω0 A) ∧ Tendsto ω0 atBot (𝓝 0) ∧
      ∀ R, PaperWeightedHolderSourceBox κ M (paperWeightedHolderExponent p) B Hbox ω R →
      ∀ A x y, x ≤ A → y ≤ A →
        |paperFixedSourceMap p c lam M κ u Z R x -
            paperFixedSourceMap p c lam M κ u Z R y| ≤ ω0 A := by
  let β : ℝ := paperWeightedHolderExponent p
  have hβpos : 0 < β := by
    dsimp [β]
    exact paperWeightedHolderExponent_pos p
  have hβle : β ≤ 1 := by
    dsimp [β]
    exact paperWeightedHolderExponent_le_one p
  obtain ⟨ωW, hωWnn, hωWlim, hωWcauchy⟩ :=
    PaperWeightedHolderSourceBox.greenConv_leftTailCauchy_uniform
      (c := c) (lam := lam) hlam (κ := κ) (M := M) (B := B)
      (β := β) (Hbox := Hbox) (ω := ω) hBnn
  obtain ⟨ωWd0, hωWd0nn, hωWd0lim, hωWd0small⟩ :=
    PaperWeightedHolderSourceBox.greenConvDeriv_leftTailSmall_uniform
      (c := c) (lam := lam) hlam (κ := κ) (M := M) (B := B)
      (β := β) (Hbox := Hbox) (ω := ω) hBnn
  rcases antitone_isBddFun_tendsto_atBot
      (upperBarrier_antitone (κ := κ) (M := M) hκ)
      (upperBarrier_isBddFun (κ := κ) (M := M) hM.le) with
    ⟨LU, hLU⟩
  let hUQ : LeftTailQuant (upperBarrier κ M) :=
    LeftTailQuant.of_antitone_tendsto hM.le
      (fun x => by
        rw [abs_of_nonneg (upperBarrier_nonneg hM.le x)]
        exact upperBarrier_le_M κ M x)
      (upperBarrier_antitone (κ := κ) (M := M) hκ) hLU
  let CV : ℝ := M ^ p.γ
  have hCVnn : 0 ≤ CV := by dsimp [CV]; positivity
  have hVbound : ∀ x, |frozenElliptic p u x| ≤ CV := by
    intro x
    rw [abs_of_nonneg (frozenElliptic_nonneg_of_inWaveTrapSet p hu.trap x)]
    exact frozenElliptic_le_rpow_of_inWaveTrapSet p hM hu.trap x
  have hVanti : Antitone (frozenElliptic p u) :=
    frozenElliptic_antitone_of_monotone_trap p hu
  rcases antitone_isBddFun_tendsto_atBot hVanti
      (frozenElliptic_bddFun_of_inWaveTrapSet p hM hu.trap) with
    ⟨LV, hLV⟩
  let hVQ : LeftTailQuant (fun z => frozenElliptic p u z) :=
    LeftTailQuant.of_antitone_tendsto hCVnn hVbound hVanti hLV
  have hZbound : ∀ x, |Z x| ≤ M := by
    intro x
    rw [abs_of_nonneg (hZ.nonneg x)]
    exact le_trans (hZ.le_barrier x) (upperBarrier_le_M κ M x)
  rcases antitone_isBddFun_tendsto_atBot hZ.anti ⟨M, hZbound⟩ with
    ⟨LZ, hLZ⟩
  let hZQ : LeftTailQuant Z :=
    LeftTailQuant.of_antitone_tendsto hM.le hZbound hZ.anti hLZ
  let BM : ℝ := B * M
  let Cw : ℝ := greenWeightedMass0 c lam κ * BM
  let Cm1 : ℝ := M ^ (p.m - 1)
  let Cα : ℝ := M ^ p.α
  let Cmg : ℝ := M ^ (p.m + p.γ - 1)
  let ωΘ : ℝ → ℝ := fun A => hUQ.ω A + ωW A
  let ωm1 : ℝ → ℝ := fun A =>
    if p.m = 1 then 0
    else if p.m < 2 then (ωΘ A) ^ β
    else rpowLip (p.m - 1) M * ωΘ A
  let ωα : ℝ → ℝ := fun A => rpowLip p.α M * ωΘ A
  let ωmg : ℝ → ℝ := fun A => rpowLip (p.m + p.γ - 1) M * ωΘ A
  let Cinner : ℝ :=
    1 + |p.χ| * (Cm1 * CV) + (Cα + |p.χ| * Cmg)
  let ωinner : ℝ → ℝ := fun A =>
    |p.χ| * (Cm1 * hVQ.ω A + CV * ωm1 A) +
      (ωα A + |p.χ| * ωmg A)
  let ωreact : ℝ → ℝ := fun A => M * ωinner A + Cinner * ωΘ A
  let ωlin : ℝ → ℝ := fun A => |lam| * hZQ.ω A
  let chemCoeff : ℝ := 2 * |(-p.χ * p.m)| * Cm1 * CV
  let ω0 : ℝ → ℝ := fun A => chemCoeff * ωWd0 A + (ωreact A + ωlin A)
  have hmass0 : 0 ≤ greenWeightedMass0 c lam κ :=
    greenWeightedMass0_nonneg (c := c) (lam := lam) hlam hrpκ hrmκ
  have hBMnn : 0 ≤ BM := by dsimp [BM]; positivity
  have hCwnn : 0 ≤ Cw := by dsimp [Cw]; positivity
  have hCm1nn : 0 ≤ Cm1 := by dsimp [Cm1]; positivity
  have hCαnn : 0 ≤ Cα := by dsimp [Cα]; positivity
  have hCmgnn : 0 ≤ Cmg := by dsimp [Cmg]; positivity
  have hCinnernn : 0 ≤ Cinner := by
    dsimp [Cinner]
    positivity
  have hchemCoeffnn : 0 ≤ chemCoeff := by
    dsimp [chemCoeff]
    positivity
  have hωΘnn : ∀ A, 0 ≤ ωΘ A := by
    intro A
    dsimp [ωΘ]
    exact add_nonneg (hUQ.ω_nonneg A) (hωWnn A)
  have hωΘlim : Tendsto ωΘ atBot (𝓝 0) := by
    simpa [ωΘ] using hUQ.ω_tendsto.add hωWlim
  have hωm1nn : ∀ A, 0 ≤ ωm1 A := by
    intro A
    dsimp [ωm1]
    by_cases hm1 : p.m = 1
    · simp [hm1]
    · by_cases hm2 : p.m < 2
      · simp [hm1, hm2, Real.rpow_nonneg (hωΘnn A) β]
      · have hpow : 1 ≤ p.m - 1 := by linarith
        have hLip : 0 ≤ rpowLip (p.m - 1) M :=
          rpowLip_nonneg hpow hM.le
        simp [hm1, hm2, mul_nonneg hLip (hωΘnn A)]
  have hωm1lim : Tendsto ωm1 atBot (𝓝 0) := by
    dsimp [ωm1]
    by_cases hm1 : p.m = 1
    · simp [hm1]
    · by_cases hm2 : p.m < 2
      · have hpow := hωΘlim.rpow_const (Or.inr hβpos.le)
        simpa [hm1, hm2, Real.zero_rpow (ne_of_gt hβpos)] using hpow
      · have hpow : 1 ≤ p.m - 1 := by linarith
        simpa [hm1, hm2] using
          hωΘlim.const_mul (rpowLip (p.m - 1) M)
  have hωαnn : ∀ A, 0 ≤ ωα A := by
    intro A
    dsimp [ωα]
    exact mul_nonneg (rpowLip_nonneg p.hα hM.le) (hωΘnn A)
  have hωαlim : Tendsto ωα atBot (𝓝 0) := by
    simpa [ωα] using hωΘlim.const_mul (rpowLip p.α M)
  have hpow_mg : 1 ≤ p.m + p.γ - 1 := by linarith [p.hm, p.hγ]
  have hωmgnn : ∀ A, 0 ≤ ωmg A := by
    intro A
    dsimp [ωmg]
    exact mul_nonneg (rpowLip_nonneg hpow_mg hM.le) (hωΘnn A)
  have hωmglim : Tendsto ωmg atBot (𝓝 0) := by
    simpa [ωmg] using hωΘlim.const_mul (rpowLip (p.m + p.γ - 1) M)
  have hωinnernn : ∀ A, 0 ≤ ωinner A := by
    intro A
    dsimp [ωinner]
    exact add_nonneg
      (mul_nonneg (abs_nonneg _)
        (add_nonneg
          (mul_nonneg hCm1nn (hVQ.ω_nonneg A))
          (mul_nonneg hCVnn (hωm1nn A))))
      (add_nonneg (hωαnn A)
        (mul_nonneg (abs_nonneg _) (hωmgnn A)))
  have hωinnerlim : Tendsto ωinner atBot (𝓝 0) := by
    have h1 :
        Tendsto (fun A => Cm1 * hVQ.ω A + CV * ωm1 A) atBot (𝓝 0) :=
      by
        simpa using
          (hVQ.ω_tendsto.const_mul Cm1).add (hωm1lim.const_mul CV)
    have h2 : Tendsto (fun A => |p.χ| *
        (Cm1 * hVQ.ω A + CV * ωm1 A)) atBot (𝓝 0) :=
      by
        simpa using h1.const_mul |p.χ|
    have h3 : Tendsto (fun A => ωα A + |p.χ| * ωmg A) atBot (𝓝 0) :=
      by
        simpa using hωαlim.add (hωmglim.const_mul |p.χ|)
    simpa [ωinner] using h2.add h3
  have hωreactnn : ∀ A, 0 ≤ ωreact A := by
    intro A
    dsimp [ωreact]
    exact add_nonneg
      (mul_nonneg hM.le (hωinnernn A))
      (mul_nonneg hCinnernn (hωΘnn A))
  have hωreactlim : Tendsto ωreact atBot (𝓝 0) := by
    have h1 := hωinnerlim.const_mul M
    have h2 := hωΘlim.const_mul Cinner
    simpa [ωreact] using h1.add h2
  have hωlinnn : ∀ A, 0 ≤ ωlin A := by
    intro A
    dsimp [ωlin]
    exact mul_nonneg (abs_nonneg _) (hZQ.ω_nonneg A)
  have hωlinlim : Tendsto ωlin atBot (𝓝 0) := by
    simpa [ωlin] using hZQ.ω_tendsto.const_mul |lam|
  refine ⟨ω0, ?_, ?_, ?_⟩
  · intro A
    dsimp [ω0]
    exact add_nonneg
      (mul_nonneg hchemCoeffnn (hωWd0nn A))
      (add_nonneg (hωreactnn A) (hωlinnn A))
  · have hchem := hωWd0lim.const_mul chemCoeff
    have hrl := hωreactlim.add hωlinlim
    simpa [ω0] using hchem.add hrl
  · intro R hR A x y hx hy
    let W : ℝ → ℝ := fun z => greenConv c lam R z
    let Θ : ℝ → ℝ := fun z => paperWeightedClamp κ M W z
    let Wd : ℝ → ℝ := fun z => greenConvDeriv c lam R z
    let V : ℝ → ℝ := fun z => frozenElliptic p u z
    let hWQ : LeftTailQuant W := by
      refine
        { C := Cw
          ω := ωW
          C_nonneg := hCwnn
          ω_nonneg := hωWnn
          ω_tendsto := hωWlim
          bound := ?_
          cauchy := ?_ }
      · intro z
        dsimp [W, Cw, BM]
        calc
          |greenConv c lam R z| ≤
              greenWeightedMass0 c lam κ * (B * upperBarrier κ M z) :=
            hR.greenConv_abs_le (c := c) (lam := lam) hlam hrpκ hrmκ
              hκ hM.le hBnn z
          _ ≤ greenWeightedMass0 c lam κ * (B * M) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (upperBarrier_le_M κ M z) hBnn)
              hmass0
      · intro A x y hx hy
        exact hωWcauchy R hR A x y hx hy
    have hΘrange : ∀ z, Θ z ∈ Set.Icc (0 : ℝ) M := by
      intro z
      have hz := paperWeightedClamp_mem_Icc (κ := κ) (M := M) (W := W) hM.le z
      exact ⟨hz.1, le_trans hz.2 (upperBarrier_le_M κ M z)⟩
    let hΘQ : LeftTailQuant Θ := by
      refine
        { C := M
          ω := ωΘ
          C_nonneg := hM.le
          ω_nonneg := hωΘnn
          ω_tendsto := hωΘlim
          bound := ?_
          cauchy := ?_ }
      · intro z
        have hz := hΘrange z
        rw [abs_of_nonneg hz.1]
        exact hz.2
      · intro A x y hx hy
        calc
          |Θ x - Θ y|
              ≤ |upperBarrier κ M x - upperBarrier κ M y| + |W x - W y| :=
            paperWeightedClamp_abs_sub_le x y
          _ ≤ hUQ.ω A + ωW A :=
            add_le_add (hUQ.cauchy A x y hx hy) (hWQ.cauchy A x y hx hy)
    let hΘm1Q : LeftTailQuant (fun z => Θ z ^ (p.m - 1)) := by
      have hm1nn : 0 ≤ p.m - 1 := by linarith [p.hm]
      refine
        { C := Cm1
          ω := ωm1
          C_nonneg := hCm1nn
          ω_nonneg := hωm1nn
          ω_tendsto := hωm1lim
          bound := ?_
          cauchy := ?_ }
      · intro z
        have hz := hΘrange z
        have hpownn : 0 ≤ Θ z ^ (p.m - 1) := Real.rpow_nonneg hz.1 (p.m - 1)
        rw [abs_of_nonneg hpownn]
        dsimp [Cm1]
        exact Real.rpow_le_rpow hz.1 hz.2 hm1nn
      · intro A x y hx hy
        dsimp [ωm1]
        by_cases hm1 : p.m = 1
        · simp [hm1]
        · by_cases hm2 : p.m < 2
          · have hm1pos : 0 < p.m - 1 :=
              sub_pos.mpr (lt_of_le_of_ne p.hm (Ne.symm hm1))
            have hm1le : p.m - 1 ≤ 1 := by linarith
            have hpow :
                |Θ x ^ (p.m - 1) - Θ y ^ (p.m - 1)|
                  ≤ |Θ x - Θ y| ^ (p.m - 1) :=
              rpow_abs_sub_le_abs_sub_rpow hm1pos.le hm1le
                (hΘrange x).1 (hΘrange y).1
            have hmod :
                |Θ x - Θ y| ^ (p.m - 1) ≤ (ωΘ A) ^ (p.m - 1) :=
              Real.rpow_le_rpow (abs_nonneg _) (hΘQ.cauchy A x y hx hy) hm1pos.le
            have hβeq : β = p.m - 1 := by
              dsimp [β, paperWeightedHolderExponent]
              rw [if_neg hm1, if_pos hm2]
            simpa [hm1, hm2, hβeq] using le_trans hpow hmod
          · have hpow : 1 ≤ p.m - 1 := by linarith
            have hLip0 : 0 ≤ rpowLip (p.m - 1) M :=
              rpowLip_nonneg hpow hM.le
            calc
              |Θ x ^ (p.m - 1) - Θ y ^ (p.m - 1)|
                  ≤ rpowLip (p.m - 1) M * |Θ x - Θ y| :=
                rpow_abs_sub_le_lip_on_Icc hpow hM.le (hΘrange x) (hΘrange y)
              _ ≤ rpowLip (p.m - 1) M * ωΘ A :=
                mul_le_mul_of_nonneg_left (hΘQ.cauchy A x y hx hy) hLip0
              _ = (if p.m = 1 then 0
                    else if p.m < 2 then (ωΘ A) ^ β
                    else rpowLip (p.m - 1) M * ωΘ A) := by
                simp [hm1, hm2]
    let hΘαQ : LeftTailQuant (fun z => Θ z ^ p.α) := by
      refine
        { C := Cα
          ω := ωα
          C_nonneg := hCαnn
          ω_nonneg := hωαnn
          ω_tendsto := hωαlim
          bound := ?_
          cauchy := ?_ }
      · intro z
        have hz := hΘrange z
        have hpownn : 0 ≤ Θ z ^ p.α := Real.rpow_nonneg hz.1 p.α
        rw [abs_of_nonneg hpownn]
        dsimp [Cα]
        exact Real.rpow_le_rpow hz.1 hz.2 (by linarith [p.hα])
      · intro A x y hx hy
        have hLip0 : 0 ≤ rpowLip p.α M := rpowLip_nonneg p.hα hM.le
        calc
          |Θ x ^ p.α - Θ y ^ p.α| ≤ rpowLip p.α M * |Θ x - Θ y| :=
            rpow_abs_sub_le_lip_on_Icc p.hα hM.le (hΘrange x) (hΘrange y)
          _ ≤ rpowLip p.α M * ωΘ A :=
            mul_le_mul_of_nonneg_left (hΘQ.cauchy A x y hx hy) hLip0
    let hΘmgQ : LeftTailQuant (fun z => Θ z ^ (p.m + p.γ - 1)) := by
      refine
        { C := Cmg
          ω := ωmg
          C_nonneg := hCmgnn
          ω_nonneg := hωmgnn
          ω_tendsto := hωmglim
          bound := ?_
          cauchy := ?_ }
      · intro z
        have hz := hΘrange z
        have hpownn : 0 ≤ Θ z ^ (p.m + p.γ - 1) :=
          Real.rpow_nonneg hz.1 (p.m + p.γ - 1)
        rw [abs_of_nonneg hpownn]
        dsimp [Cmg]
        exact Real.rpow_le_rpow hz.1 hz.2 (by linarith [p.hm, p.hγ])
      · intro A x y hx hy
        have hLip0 : 0 ≤ rpowLip (p.m + p.γ - 1) M :=
          rpowLip_nonneg hpow_mg hM.le
        calc
          |Θ x ^ (p.m + p.γ - 1) - Θ y ^ (p.m + p.γ - 1)|
              ≤ rpowLip (p.m + p.γ - 1) M * |Θ x - Θ y| :=
            rpow_abs_sub_le_lip_on_Icc hpow_mg hM.le (hΘrange x) (hΘrange y)
          _ ≤ rpowLip (p.m + p.γ - 1) M * ωΘ A :=
            mul_le_mul_of_nonneg_left (hΘQ.cauchy A x y hx hy) hLip0
    have hVd_bound : ∀ z, |deriv (frozenElliptic p u) z| ≤ CV := by
      intro z
      calc
        |deriv (frozenElliptic p u) z|
            ≤ frozenElliptic p u z :=
          frozenElliptic_deriv_abs_le p hu.trap.cunif_bdd hu.nonneg z
        _ ≤ CV := frozenElliptic_le_rpow_of_inWaveTrapSet p hM hu.trap z
    let hLinQ : LeftTailQuant (fun z => lam * Z z) :=
      LeftTailQuant.const_mul (a := lam) hZQ
    have hM1V_cauchy :
        |Θ x ^ (p.m - 1) * V x - Θ y ^ (p.m - 1) * V y|
          ≤ Cm1 * hVQ.ω A + CV * ωm1 A := by
      have hsplit :
          Θ x ^ (p.m - 1) * V x - Θ y ^ (p.m - 1) * V y =
            Θ x ^ (p.m - 1) * (V x - V y) +
              V y * (Θ x ^ (p.m - 1) - Θ y ^ (p.m - 1)) := by
        ring
      rw [hsplit]
      calc
        |Θ x ^ (p.m - 1) * (V x - V y) +
              V y * (Θ x ^ (p.m - 1) - Θ y ^ (p.m - 1))|
            ≤ |Θ x ^ (p.m - 1) * (V x - V y)| +
                |V y * (Θ x ^ (p.m - 1) - Θ y ^ (p.m - 1))| :=
          abs_add_le _ _
        _ = |Θ x ^ (p.m - 1)| * |V x - V y| +
                |V y| * |Θ x ^ (p.m - 1) - Θ y ^ (p.m - 1)| := by
          rw [abs_mul, abs_mul]
        _ ≤ Cm1 * hVQ.ω A + CV * ωm1 A :=
          add_le_add
            (mul_le_mul (hΘm1Q.bound x) (hVQ.cauchy A x y hx hy)
              (abs_nonneg _) hCm1nn)
            (mul_le_mul (hVQ.bound y) (hΘm1Q.cauchy A x y hx hy)
              (abs_nonneg _) hCVnn)
    have hPowDiff_cauchy :
        |(Θ x ^ p.α - p.χ * Θ x ^ (p.m + p.γ - 1)) -
            (Θ y ^ p.α - p.χ * Θ y ^ (p.m + p.γ - 1))|
          ≤ ωα A + |p.χ| * ωmg A := by
      have hsplit :
          (Θ x ^ p.α - p.χ * Θ x ^ (p.m + p.γ - 1)) -
            (Θ y ^ p.α - p.χ * Θ y ^ (p.m + p.γ - 1)) =
          (Θ x ^ p.α - Θ y ^ p.α) -
            p.χ * (Θ x ^ (p.m + p.γ - 1) - Θ y ^ (p.m + p.γ - 1)) := by
        ring
      rw [hsplit]
      calc
        |(Θ x ^ p.α - Θ y ^ p.α) -
            p.χ * (Θ x ^ (p.m + p.γ - 1) - Θ y ^ (p.m + p.γ - 1))|
            ≤ |Θ x ^ p.α - Θ y ^ p.α| +
                |p.χ * (Θ x ^ (p.m + p.γ - 1) - Θ y ^ (p.m + p.γ - 1))| :=
          abs_sub _ _
        _ = |Θ x ^ p.α - Θ y ^ p.α| +
                |p.χ| * |Θ x ^ (p.m + p.γ - 1) - Θ y ^ (p.m + p.γ - 1)| := by
          rw [abs_mul]
        _ ≤ ωα A + |p.χ| * ωmg A :=
          add_le_add (hΘαQ.cauchy A x y hx hy)
            (mul_le_mul_of_nonneg_left (hΘmgQ.cauchy A x y hx hy) (abs_nonneg _))
    have hInner_cauchy :
        |((1 - p.χ * (Θ x ^ (p.m - 1) * V x)) -
            (Θ x ^ p.α - p.χ * Θ x ^ (p.m + p.γ - 1))) -
          ((1 - p.χ * (Θ y ^ (p.m - 1) * V y)) -
            (Θ y ^ p.α - p.χ * Θ y ^ (p.m + p.γ - 1)))|
          ≤ ωinner A := by
      have hsplit :
          ((1 - p.χ * (Θ x ^ (p.m - 1) * V x)) -
            (Θ x ^ p.α - p.χ * Θ x ^ (p.m + p.γ - 1))) -
          ((1 - p.χ * (Θ y ^ (p.m - 1) * V y)) -
            (Θ y ^ p.α - p.χ * Θ y ^ (p.m + p.γ - 1))) =
          -(p.χ * ((Θ x ^ (p.m - 1) * V x) -
              (Θ y ^ (p.m - 1) * V y))) -
            ((Θ x ^ p.α - p.χ * Θ x ^ (p.m + p.γ - 1)) -
              (Θ y ^ p.α - p.χ * Θ y ^ (p.m + p.γ - 1))) := by
        ring
      rw [hsplit]
      calc
        |-(p.χ * (Θ x ^ (p.m - 1) * V x - Θ y ^ (p.m - 1) * V y)) -
            ((Θ x ^ p.α - p.χ * Θ x ^ (p.m + p.γ - 1)) -
              (Θ y ^ p.α - p.χ * Θ y ^ (p.m + p.γ - 1)))|
            ≤ |p.χ * (Θ x ^ (p.m - 1) * V x - Θ y ^ (p.m - 1) * V y)| +
                |(Θ x ^ p.α - p.χ * Θ x ^ (p.m + p.γ - 1)) -
                  (Θ y ^ p.α - p.χ * Θ y ^ (p.m + p.γ - 1))| := by
          simpa [abs_neg] using abs_sub
            (-(p.χ * (Θ x ^ (p.m - 1) * V x - Θ y ^ (p.m - 1) * V y)))
            ((Θ x ^ p.α - p.χ * Θ x ^ (p.m + p.γ - 1)) -
              (Θ y ^ p.α - p.χ * Θ y ^ (p.m + p.γ - 1)))
        _ = |p.χ| * |Θ x ^ (p.m - 1) * V x - Θ y ^ (p.m - 1) * V y| +
                |(Θ x ^ p.α - p.χ * Θ x ^ (p.m + p.γ - 1)) -
                  (Θ y ^ p.α - p.χ * Θ y ^ (p.m + p.γ - 1))| := by
          rw [abs_mul]
        _ ≤ |p.χ| * (Cm1 * hVQ.ω A + CV * ωm1 A) +
              (ωα A + |p.χ| * ωmg A) :=
          add_le_add
            (mul_le_mul_of_nonneg_left hM1V_cauchy (abs_nonneg _))
            hPowDiff_cauchy
        _ = ωinner A := by rfl
    have hInner_bound : ∀ z,
        |(1 - p.χ * (Θ z ^ (p.m - 1) * V z)) -
          (Θ z ^ p.α - p.χ * Θ z ^ (p.m + p.γ - 1))| ≤ Cinner := by
      intro z
      have hM1V_bound :
          |Θ z ^ (p.m - 1) * V z| ≤ Cm1 * CV := by
        rw [abs_mul]
        exact mul_le_mul (hΘm1Q.bound z) (hVQ.bound z) (abs_nonneg _) hCm1nn
      have hχM1V_bound :
          |p.χ * (Θ z ^ (p.m - 1) * V z)| ≤ |p.χ| * (Cm1 * CV) := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left hM1V_bound (abs_nonneg _)
      have hχmg_bound :
          |p.χ * Θ z ^ (p.m + p.γ - 1)| ≤ |p.χ| * Cmg := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hΘmgQ.bound z) (abs_nonneg _)
      have hPow_bound :
          |Θ z ^ p.α - p.χ * Θ z ^ (p.m + p.γ - 1)| ≤ Cα + |p.χ| * Cmg := by
        calc
          |Θ z ^ p.α - p.χ * Θ z ^ (p.m + p.γ - 1)|
              ≤ |Θ z ^ p.α| + |p.χ * Θ z ^ (p.m + p.γ - 1)| := abs_sub _ _
          _ ≤ Cα + |p.χ| * Cmg := add_le_add (hΘαQ.bound z) hχmg_bound
      calc
        |(1 - p.χ * (Θ z ^ (p.m - 1) * V z)) -
          (Θ z ^ p.α - p.χ * Θ z ^ (p.m + p.γ - 1))|
            ≤ |1 - p.χ * (Θ z ^ (p.m - 1) * V z)| +
                |Θ z ^ p.α - p.χ * Θ z ^ (p.m + p.γ - 1)| := abs_sub _ _
        _ ≤ (1 + |p.χ| * (Cm1 * CV)) + (Cα + |p.χ| * Cmg) := by
          exact add_le_add
            (by
              calc
                |1 - p.χ * (Θ z ^ (p.m - 1) * V z)|
                    ≤ |(1 : ℝ)| + |p.χ * (Θ z ^ (p.m - 1) * V z)| := abs_sub _ _
                _ ≤ 1 + |p.χ| * (Cm1 * CV) := by
                  simpa using add_le_add_left hχM1V_bound 1)
            hPow_bound
        _ = Cinner := by
          dsimp [Cinner]
    have hReact :
        |Θ x *
              ((1 - p.χ * (Θ x ^ (p.m - 1) * V x)) -
                (Θ x ^ p.α - p.χ * Θ x ^ (p.m + p.γ - 1))) -
            Θ y *
              ((1 - p.χ * (Θ y ^ (p.m - 1) * V y)) -
                (Θ y ^ p.α - p.χ * Θ y ^ (p.m + p.γ - 1)))|
          ≤ ωreact A := by
      have hsplit :
          Θ x *
              ((1 - p.χ * (Θ x ^ (p.m - 1) * V x)) -
                (Θ x ^ p.α - p.χ * Θ x ^ (p.m + p.γ - 1))) -
            Θ y *
              ((1 - p.χ * (Θ y ^ (p.m - 1) * V y)) -
                (Θ y ^ p.α - p.χ * Θ y ^ (p.m + p.γ - 1))) =
          Θ x *
              (((1 - p.χ * (Θ x ^ (p.m - 1) * V x)) -
                (Θ x ^ p.α - p.χ * Θ x ^ (p.m + p.γ - 1))) -
              ((1 - p.χ * (Θ y ^ (p.m - 1) * V y)) -
                (Θ y ^ p.α - p.χ * Θ y ^ (p.m + p.γ - 1)))) +
            ((1 - p.χ * (Θ y ^ (p.m - 1) * V y)) -
              (Θ y ^ p.α - p.χ * Θ y ^ (p.m + p.γ - 1))) *
              (Θ x - Θ y) := by
        ring
      rw [hsplit]
      calc
        |Θ x *
              (((1 - p.χ * (Θ x ^ (p.m - 1) * V x)) -
                (Θ x ^ p.α - p.χ * Θ x ^ (p.m + p.γ - 1))) -
              ((1 - p.χ * (Θ y ^ (p.m - 1) * V y)) -
                (Θ y ^ p.α - p.χ * Θ y ^ (p.m + p.γ - 1)))) +
            ((1 - p.χ * (Θ y ^ (p.m - 1) * V y)) -
              (Θ y ^ p.α - p.χ * Θ y ^ (p.m + p.γ - 1))) *
              (Θ x - Θ y)|
            ≤ |Θ x *
              (((1 - p.χ * (Θ x ^ (p.m - 1) * V x)) -
                (Θ x ^ p.α - p.χ * Θ x ^ (p.m + p.γ - 1))) -
              ((1 - p.χ * (Θ y ^ (p.m - 1) * V y)) -
                (Θ y ^ p.α - p.χ * Θ y ^ (p.m + p.γ - 1))))| +
              |((1 - p.χ * (Θ y ^ (p.m - 1) * V y)) -
                (Θ y ^ p.α - p.χ * Θ y ^ (p.m + p.γ - 1))) *
                (Θ x - Θ y)| := abs_add_le _ _
        _ = |Θ x| *
              |((1 - p.χ * (Θ x ^ (p.m - 1) * V x)) -
                (Θ x ^ p.α - p.χ * Θ x ^ (p.m + p.γ - 1))) -
              ((1 - p.χ * (Θ y ^ (p.m - 1) * V y)) -
                (Θ y ^ p.α - p.χ * Θ y ^ (p.m + p.γ - 1)))| +
              |(1 - p.χ * (Θ y ^ (p.m - 1) * V y)) -
                (Θ y ^ p.α - p.χ * Θ y ^ (p.m + p.γ - 1))| *
                |Θ x - Θ y| := by
          rw [abs_mul, abs_mul]
        _ ≤ M * ωinner A + Cinner * ωΘ A :=
          add_le_add
            (mul_le_mul (hΘQ.bound x) hInner_cauchy (abs_nonneg _) hM.le)
            (mul_le_mul (hInner_bound y) (hΘQ.cauchy A x y hx hy)
              (abs_nonneg _) hCinnernn)
        _ = ωreact A := by rfl
    have hLin :
        |lam * Z x - lam * Z y| ≤ ωlin A := by
      have h := hLinQ.cauchy A x y hx hy
      simpa [hLinQ, hZQ, ωlin] using h
    have hReactLin :
        |(Θ x *
              ((1 - p.χ * (Θ x ^ (p.m - 1) * V x)) -
                (Θ x ^ p.α - p.χ * Θ x ^ (p.m + p.γ - 1))) +
            lam * Z x) -
          (Θ y *
              ((1 - p.χ * (Θ y ^ (p.m - 1) * V y)) -
                (Θ y ^ p.α - p.χ * Θ y ^ (p.m + p.γ - 1))) +
            lam * Z y)| ≤ ωreact A + ωlin A := by
      calc
        |(Θ x *
              ((1 - p.χ * (Θ x ^ (p.m - 1) * V x)) -
                (Θ x ^ p.α - p.χ * Θ x ^ (p.m + p.γ - 1))) +
            lam * Z x) -
          (Θ y *
              ((1 - p.χ * (Θ y ^ (p.m - 1) * V y)) -
                (Θ y ^ p.α - p.χ * Θ y ^ (p.m + p.γ - 1))) +
            lam * Z y)|
            = |(Θ x *
                ((1 - p.χ * (Θ x ^ (p.m - 1) * V x)) -
                  (Θ x ^ p.α - p.χ * Θ x ^ (p.m + p.γ - 1))) -
              Θ y *
                ((1 - p.χ * (Θ y ^ (p.m - 1) * V y)) -
                  (Θ y ^ p.α - p.χ * Θ y ^ (p.m + p.γ - 1)))) +
              (lam * Z x - lam * Z y)| := by ring_nf
        _ ≤
            |Θ x *
                ((1 - p.χ * (Θ x ^ (p.m - 1) * V x)) -
                  (Θ x ^ p.α - p.χ * Θ x ^ (p.m + p.γ - 1))) -
              Θ y *
                ((1 - p.χ * (Θ y ^ (p.m - 1) * V y)) -
                  (Θ y ^ p.α - p.χ * Θ y ^ (p.m + p.γ - 1)))| +
              |lam * Z x - lam * Z y| := abs_add_le _ _
        _ ≤ ωreact A + ωlin A := add_le_add hReact hLin
    have hChemPoint : ∀ z, z ≤ A →
        |(-p.χ * p.m) *
            ((Θ z ^ (p.m - 1) * deriv (frozenElliptic p u) z) * Wd z)|
          ≤ |(-p.χ * p.m)| * Cm1 * CV * ωWd0 A := by
      intro z hz
      have hm1nn : 0 ≤ p.m - 1 := by linarith [p.hm]
      have hΘpow : |Θ z ^ (p.m - 1)| ≤ Cm1 := by
        have hzr := hΘrange z
        have hpownn : 0 ≤ Θ z ^ (p.m - 1) := Real.rpow_nonneg hzr.1 (p.m - 1)
        rw [abs_of_nonneg hpownn]
        dsimp [Cm1]
        exact Real.rpow_le_rpow hzr.1 hzr.2 hm1nn
      have hWd : |Wd z| ≤ ωWd0 A := by
        dsimp [Wd]
        exact hωWd0small R hR A z hz
      have hpair :
          |Θ z ^ (p.m - 1)| * |deriv (frozenElliptic p u) z| ≤ Cm1 * CV :=
        mul_le_mul hΘpow (hVd_bound z) (abs_nonneg _) hCm1nn
      have htriple :
          |Θ z ^ (p.m - 1)| * |deriv (frozenElliptic p u) z| * |Wd z| ≤
            Cm1 * CV * ωWd0 A :=
        mul_le_mul hpair hWd (abs_nonneg _) (mul_nonneg hCm1nn hCVnn)
      calc
        |(-p.χ * p.m) *
            ((Θ z ^ (p.m - 1) * deriv (frozenElliptic p u) z) * Wd z)|
            = |(-p.χ * p.m)| *
                (|Θ z ^ (p.m - 1)| *
                  |deriv (frozenElliptic p u) z| * |Wd z|) := by
              rw [abs_mul (-p.χ * p.m)
                ((Θ z ^ (p.m - 1) * deriv (frozenElliptic p u) z) * Wd z)]
              rw [abs_mul (Θ z ^ (p.m - 1) * deriv (frozenElliptic p u) z) (Wd z)]
              rw [abs_mul (Θ z ^ (p.m - 1)) (deriv (frozenElliptic p u) z)]
        _ ≤ |(-p.χ * p.m)| * (Cm1 * CV * ωWd0 A) := by
              exact mul_le_mul_of_nonneg_left htriple (abs_nonneg _)
        _ = |(-p.χ * p.m)| * Cm1 * CV * ωWd0 A := by ring
    have hChem :
        |(-p.χ * p.m) *
              ((Θ x ^ (p.m - 1) * deriv (frozenElliptic p u) x) * Wd x) -
            (-p.χ * p.m) *
              ((Θ y ^ (p.m - 1) * deriv (frozenElliptic p u) y) * Wd y)|
          ≤ chemCoeff * ωWd0 A := by
      calc
        |(-p.χ * p.m) *
              ((Θ x ^ (p.m - 1) * deriv (frozenElliptic p u) x) * Wd x) -
            (-p.χ * p.m) *
              ((Θ y ^ (p.m - 1) * deriv (frozenElliptic p u) y) * Wd y)|
            ≤
              |(-p.χ * p.m) *
                ((Θ x ^ (p.m - 1) * deriv (frozenElliptic p u) x) * Wd x)| +
              |(-p.χ * p.m) *
                ((Θ y ^ (p.m - 1) * deriv (frozenElliptic p u) y) * Wd y)| :=
          abs_sub _ _
        _ ≤ |(-p.χ * p.m)| * Cm1 * CV * ωWd0 A +
              |(-p.χ * p.m)| * Cm1 * CV * ωWd0 A :=
          add_le_add (hChemPoint x hx) (hChemPoint y hy)
        _ = chemCoeff * ωWd0 A := by
          dsimp [chemCoeff]
          ring
    have hHi := hR.gWeight_Ioi (c := c) (lam := lam) hlam hBnn
    have hLo := hR.gWeight_Iic (c := c) (lam := lam) hlam hBnn
    have hWdx :
        deriv (fun y => greenConv c lam R y) x = Wd x := by
      dsimp [Wd]
      exact (greenConv_hasDerivAt (c := c) (lam := lam) hR.cont hHi hLo x).deriv
    have hWdy :
        deriv (fun y => greenConv c lam R y) y = Wd y := by
      dsimp [Wd]
      exact (greenConv_hasDerivAt (c := c) (lam := lam) hR.cont hHi hLo y).deriv
    let chemX : ℝ :=
      (-p.χ * p.m) *
        ((Θ x ^ (p.m - 1) * deriv (frozenElliptic p u) x) * Wd x)
    let chemY : ℝ :=
      (-p.χ * p.m) *
        ((Θ y ^ (p.m - 1) * deriv (frozenElliptic p u) y) * Wd y)
    let reactX : ℝ :=
      Θ x *
        ((1 - p.χ * (Θ x ^ (p.m - 1) * V x)) -
          (Θ x ^ p.α - p.χ * Θ x ^ (p.m + p.γ - 1)))
    let reactY : ℝ :=
      Θ y *
        ((1 - p.χ * (Θ y ^ (p.m - 1) * V y)) -
          (Θ y ^ p.α - p.χ * Θ y ^ (p.m + p.γ - 1)))
    let linX : ℝ := lam * Z x
    let linY : ℝ := lam * Z y
    have hChem' : |chemX - chemY| ≤ chemCoeff * ωWd0 A := by
      simpa [chemX, chemY] using hChem
    have hReactLin' : |(reactX + linX) - (reactY + linY)| ≤ ωreact A + ωlin A := by
      simpa [reactX, reactY, linX, linY] using hReactLin
    have htotal :
        |(chemX + reactX + linX) - (chemY + reactY + linY)| ≤ ω0 A := by
      calc
        |(chemX + reactX + linX) - (chemY + reactY + linY)|
            = |(chemX - chemY) + ((reactX + linX) - (reactY + linY))| := by
          ring_nf
        _ ≤ |chemX - chemY| + |(reactX + linX) - (reactY + linY)| :=
          abs_add_le _ _
        _ ≤ chemCoeff * ωWd0 A + (ωreact A + ωlin A) :=
          add_le_add hChem' hReactLin'
        _ = ω0 A := by rfl
    dsimp [chemX, chemY, reactX, reactY, linX, linY] at htotal
    unfold paperFixedSourceMap paperStepSource_truncated paperStepTruncatedNonlinearity
    dsimp only [W, Θ, Wd, V, β] at htotal ⊢
    rw [hWdx, hWdy]
    dsimp [Wd]
    convert htotal using 1
    ring_nf

/-- Finite left tail for the truncated fixed-source map on the weighted source
box.  The Green source gives a left limit for `W = G * R` and `W' → 0`; the
clamp then has a left limit because the upper barrier has one.  The frozen
elliptic factor and the old iterate have finite left tails by bounded
antitonicity. -/
theorem paperFixedSourceMap_leftTail_of_trap_sourceBox
    (p : CMParams) {c lam M κ β B H : ℝ} {ω : ℝ → ℝ} {u Z R : ℝ → ℝ}
    (hlam : 0 < lam) (hκ : 0 ≤ κ) (hM : 0 < M) (hBnn : 0 ≤ B)
    (hu : InMonotoneWaveTrapSet κ M u)
    (hZ : PaperIterateBase κ M Z)
    (hR : PaperWeightedHolderSourceBox κ M β B H ω R) :
    ∃ Rm, Tendsto (paperFixedSourceMap p c lam M κ u Z R) atBot (𝓝 Rm) := by
  let W : ℝ → ℝ := fun x => greenConv c lam R x
  let Θ : ℝ → ℝ := fun x => paperWeightedClamp κ M W x
  rcases hR.greenConv_tendsto_atBot
      (c := c) (lam := lam) hlam hBnn with
    ⟨Wm, hWm⟩
  have hWd :
      Tendsto (fun x => deriv W x) atBot (𝓝 0) := by
    simpa [W] using
      hR.deriv_greenConv_tendsto_atBot_zero
        (c := c) (lam := lam) hlam hBnn
  rcases antitone_isBddFun_tendsto_atBot
      (upperBarrier_antitone (κ := κ) (M := M) hκ)
      (upperBarrier_isBddFun (κ := κ) (M := M) hM.le) with
    ⟨Um, hUm⟩
  have hΘ :
      Tendsto Θ atBot (𝓝 (max 0 (min Um Wm))) := by
    have hmin :
        Tendsto (fun x => min (upperBarrier κ M x) (W x))
          atBot (𝓝 (min Um Wm)) :=
      hUm.min hWm
    simpa [Θ, W, paperWeightedClamp, clampIcc] using
      (tendsto_const_nhds.max hmin)
  have hVanti : Antitone (frozenElliptic p u) :=
    frozenElliptic_antitone_of_monotone_trap p hu
  have hVbdd : IsBddFun (frozenElliptic p u) :=
    frozenElliptic_bddFun_of_inWaveTrapSet p hM hu.trap
  rcases antitone_isBddFun_tendsto_atBot hVanti hVbdd with
    ⟨Vm, hVm⟩
  have hZbdd : IsBddFun Z := by
    refine ⟨M, fun x => ?_⟩
    rw [abs_of_nonneg (hZ.nonneg x)]
    exact le_trans (hZ.le_barrier x) (upperBarrier_le_M κ M x)
  rcases antitone_isBddFun_tendsto_atBot hZ.anti hZbdd with
    ⟨Zm, hZm⟩
  have hΘbdd : IsBddFun Θ := by
    refine ⟨M, fun x => ?_⟩
    calc
      |Θ x| ≤ upperBarrier κ M x := by
        dsimp [Θ]
        exact paperWeightedClamp_abs_le_upperBarrier
          (κ := κ) (M := M) (W := W) hM.le x
      _ ≤ M := upperBarrier_le_M κ M x
  have hΘnonneg : ∀ x, 0 ≤ Θ x := by
    intro x
    exact (paperWeightedClamp_mem_Icc
      (κ := κ) (M := M) (W := W) hM.le x).1
  have hm1 : 0 ≤ p.m - 1 := by linarith [p.hm]
  have hα : 0 ≤ p.α := by linarith [p.hα]
  have hmg1 : 0 ≤ p.m + p.γ - 1 := by linarith [p.hm, p.hγ]
  have hΘm1 :
      Tendsto (fun x => (Θ x) ^ (p.m - 1)) atBot
        (𝓝 ((max 0 (min Um Wm)) ^ (p.m - 1))) :=
    hΘ.rpow_const (Or.inr hm1)
  have hΘα :
      Tendsto (fun x => (Θ x) ^ p.α) atBot
        (𝓝 ((max 0 (min Um Wm)) ^ p.α)) :=
    hΘ.rpow_const (Or.inr hα)
  have hΘmg1 :
      Tendsto (fun x => (Θ x) ^ (p.m + p.γ - 1)) atBot
        (𝓝 ((max 0 (min Um Wm)) ^ (p.m + p.γ - 1))) :=
    hΘ.rpow_const (Or.inr hmg1)
  have hΘm1bdd : IsBddFun (fun x => (Θ x) ^ (p.m - 1)) :=
    IsBddFun.rpow_of_nonneg hΘbdd hm1 hΘnonneg
  have hVdbdd : IsBddFun (fun x => deriv (frozenElliptic p u) x) := by
    refine ⟨M ^ p.γ, fun x => ?_⟩
    calc
      |deriv (frozenElliptic p u) x| ≤ frozenElliptic p u x :=
        frozenElliptic_deriv_abs_le p hu.trap.cunif_bdd hu.nonneg x
      _ ≤ M ^ p.γ :=
        frozenElliptic_le_rpow_of_inWaveTrapSet p hM hu.trap x
  have hchemCoeffBdd : IsBddFun (fun x =>
      (-p.χ * p.m) * (Θ x) ^ (p.m - 1) *
        deriv (frozenElliptic p u) x) := by
    exact IsBddFun.mul
      (IsBddFun.const_mul (-p.χ * p.m) hΘm1bdd) hVdbdd
  have hchem :
      Tendsto
        (fun x =>
          -p.χ * p.m * (Θ x) ^ (p.m - 1) *
            deriv (frozenElliptic p u) x * deriv W x) atBot
        (𝓝 0) := by
    have hrev := tendsto_mul_zero_of_isBddFun hWd hchemCoeffBdd
    simpa [mul_comm, mul_left_comm, mul_assoc] using hrev
  have hχΘm1V :
      Tendsto (fun x => p.χ * (Θ x) ^ (p.m - 1) * frozenElliptic p u x)
        atBot
        (𝓝 (p.χ * (max 0 (min Um Wm)) ^ (p.m - 1) * Vm)) := by
    have hmul := hΘm1.mul hVm
    simpa [mul_assoc] using hmul.const_mul p.χ
  have hχΘmg1 :
      Tendsto (fun x => p.χ * (Θ x) ^ (p.m + p.γ - 1)) atBot
        (𝓝 (p.χ * (max 0 (min Um Wm)) ^ (p.m + p.γ - 1))) :=
    hΘmg1.const_mul p.χ
  have hinner :
      Tendsto
        (fun x =>
          1 - p.χ * (Θ x) ^ (p.m - 1) * frozenElliptic p u x
            - ((Θ x) ^ p.α - p.χ * (Θ x) ^ (p.m + p.γ - 1))) atBot
        (𝓝
          (1 - p.χ * (max 0 (min Um Wm)) ^ (p.m - 1) * Vm
            - ((max 0 (min Um Wm)) ^ p.α
              - p.χ * (max 0 (min Um Wm)) ^ (p.m + p.γ - 1)))) := by
    exact (tendsto_const_nhds.sub hχΘm1V).sub (hΘα.sub hχΘmg1)
  have hreac :
      Tendsto
        (fun x =>
          Θ x *
            (1 - p.χ * (Θ x) ^ (p.m - 1) * frozenElliptic p u x
              - ((Θ x) ^ p.α - p.χ * (Θ x) ^ (p.m + p.γ - 1))))
        atBot
        (𝓝
          ((max 0 (min Um Wm)) *
            (1 - p.χ * (max 0 (min Um Wm)) ^ (p.m - 1) * Vm
              - ((max 0 (min Um Wm)) ^ p.α
                - p.χ * (max 0 (min Um Wm)) ^
                    (p.m + p.γ - 1))))) :=
    hΘ.mul hinner
  have hlin : Tendsto (fun x => lam * Z x) atBot (𝓝 (lam * Zm)) :=
    hZm.const_mul lam
  refine ⟨
    0 +
      (max 0 (min Um Wm)) *
        (1 - p.χ * (max 0 (min Um Wm)) ^ (p.m - 1) * Vm
          - ((max 0 (min Um Wm)) ^ p.α
            - p.χ * (max 0 (min Um Wm)) ^ (p.m + p.γ - 1))) +
      lam * Zm, ?_⟩
  have htotal := (hchem.add hreac).add hlin
  refine htotal.congr' ?_
  filter_upwards with x
  unfold paperFixedSourceMap paperStepSource_truncated paperStepTruncatedNonlinearity
  dsimp only [W, Θ]

/-- Assemble the source-box bounds from the trap/scalar estimates.

The continuity and weighted bound fields are discharged here.  The genuinely
Hölder/tail modulus obligations remain explicit inputs, and compactness is then
derived from the resulting self-map of the weighted source box. -/
def paperFixedSourceMapBoxBounds_of_trap
    (p : CMParams) {c lam M κ β B H : ℝ} {ω : ℝ → ℝ} {u Z : ℝ → ℝ}
    (hlam : 0 < lam)
    (hrpκ : κ < greenRootPlus c lam)
    (hrmκ : κ < -greenRootMinus c lam)
    (hκ : 0 ≤ κ) (hM : 0 < M) (hBnn : 0 ≤ B)
    (hHnn : 0 ≤ H) (hβpos : 0 < β)
    (hu : InMonotoneWaveTrapSet κ M u)
    (hZ : PaperIterateBase κ M Z)
    (hscalar :
      |(-p.χ * p.m)| * M ^ (p.m - 1) * M ^ p.γ *
            greenWeightedMass1 c lam κ * B
        + (1 + |p.χ| * M ^ (p.m - 1) * M ^ p.γ
            + M ^ p.α + |p.χ| * M ^ (p.m + p.γ - 1))
        + lam ≤ B)
    (hmap_holder : ∀ R, PaperWeightedHolderSourceBox κ M β B H ω R →
      ∀ x y,
        |paperFixedSourceMap p c lam M κ u Z R x -
            paperFixedSourceMap p c lam M κ u Z R y| ≤ H * |x - y| ^ β)
    (hmap_leftTailCauchy : ∀ R, PaperWeightedHolderSourceBox κ M β B H ω R →
      ∀ A x y, x ≤ A → y ≤ A →
        |paperFixedSourceMap p c lam M κ u Z R x -
            paperFixedSourceMap p c lam M κ u Z R y| ≤ ω A) :
    PaperFixedSourceMapBoxBounds p c lam M κ β B H ω u Z := by
  let map_cont :
      ∀ R, PaperWeightedHolderSourceBox κ M β B H ω R →
        Continuous (paperFixedSourceMap p c lam M κ u Z R) := by
    intro R hR
    exact paperFixedSourceMap_continuous_of_trap_sourceBox
      (p := p) (c := c) (lam := lam) (M := M) (κ := κ)
      (β := β) (B := B) (H := H) (ω := ω)
      (u := u) (Z := Z) (R := R) hlam hu.trap hZ.cont hBnn hR
  let map_bound :
      ∀ R, PaperWeightedHolderSourceBox κ M β B H ω R →
        ∀ x, |paperFixedSourceMap p c lam M κ u Z R x| ≤
          B * upperBarrier κ M x := by
    intro R hR
    have hVbound : ∀ x, |frozenElliptic p u x| ≤ M ^ p.γ := by
      intro x
      rw [abs_of_nonneg (frozenElliptic_nonneg_of_inWaveTrapSet p hu.trap x)]
      exact frozenElliptic_le_rpow_of_inWaveTrapSet p hM hu.trap x
    have hVderiv_bound :
        ∀ x, |deriv (frozenElliptic p u) x| ≤ M ^ p.γ := by
      intro x
      calc
        |deriv (frozenElliptic p u) x| ≤ frozenElliptic p u x :=
          frozenElliptic_deriv_abs_le p hu.trap.cunif_bdd hu.nonneg x
        _ ≤ M ^ p.γ :=
          frozenElliptic_le_rpow_of_inWaveTrapSet p hM hu.trap x
    exact paperFixedSourceMap_bound_of_sourceBox
      (p := p) (c := c) (lam := lam) (M := M) (κ := κ)
      (β := β) (B := B) (H := H) (BV := M ^ p.γ) (BVd := M ^ p.γ) (ω := ω)
      (u := u) (Z := Z) (R := R)
      hlam hrpκ hrmκ hκ hM.le hBnn
      (Real.rpow_nonneg hM.le p.γ) (Real.rpow_nonneg hM.le p.γ)
      hZ.nonneg hZ.le_barrier
      hVbound hVderiv_bound hscalar hR
  let map_leftTail :
      ∀ R, PaperWeightedHolderSourceBox κ M β B H ω R →
        ∃ Rm, Tendsto (paperFixedSourceMap p c lam M κ u Z R) atBot (𝓝 Rm) := by
    intro R hR
    exact paperFixedSourceMap_leftTail_of_trap_sourceBox
      (p := p) (c := c) (lam := lam) (M := M) (κ := κ)
      (β := β) (B := B) (H := H) (ω := ω)
      (u := u) (Z := Z) (R := R) hlam hκ hM hBnn hu hZ hR
  refine
    { map_cont := map_cont
      map_bound := map_bound
      map_holder := hmap_holder
      map_leftTail := map_leftTail
      map_leftTailCauchy := hmap_leftTailCauchy
      ascoliCompactRange := ?_ }
  apply localUniformSequentiallyCompactRange_weightedHolderSourceBox_of_mapsTo
    (κ := κ) (M := M) (β := β) (B := B) (H := H) (ω := ω)
    hM.le hBnn hHnn hβpos
  intro R hR
  exact
    { cont := map_cont R hR
      bound := map_bound R hR
      holder := hmap_holder R hR
      omega_nonneg := hR.omega_nonneg
      omega_tendsto := hR.omega_tendsto
      leftTail := map_leftTail R hR
      leftTailCauchy := hmap_leftTailCauchy R hR }

/-- Assemble the truncated source-box fixed-source data from source-box bounds,
local-uniform continuity, finite-cube data, and the barrier packets used only to
prove clamp inactivity.

The resulting record carries the already committed `boxCubeData`; the barrier
packets are consumed immediately by the truncated max-principles and are not
stored in the fixed-source data. -/
def paperTruncatedFixedSourceBoxData_of_trap
    {p : CMParams} {c lam M κ Λ β B H C_chem : ℝ}
    {ω : ℝ → ℝ} {u Z : ℝ → ℝ}
    (hlam : 0 < lam) (hκ : 0 < κ) (hM : 0 < M) (hBnn : 0 ≤ B)
    (hHnn : 0 ≤ H) (hβpos : 0 < β)
    (hu : InMonotoneWaveTrapSet κ M u)
    (hsourceBound_eq : Λ = 2 * (greenDelta c lam)⁻¹ * (B * M))
    (hbeta_eq : β = paperWeightedHolderExponent p)
    (hbox :
      PaperFixedSourceMapBoxBounds p c lam M κ β B H ω u Z)
    (hboxCubeData :
      ProjectedCubeApproxData
        (PaperWeightedHolderSourceBox κ M β B H ω)
        (paperFixedSourceMap p c lam M κ u Z))
    (hlower : ∀ R, PaperWeightedHolderSourceBox κ M β B H ω R →
      paperFixedSourceMap p c lam M κ u Z R = R →
        PaperStepLowerTruncatedData p c lam M C_chem u Z
          (fun x => greenConv c lam R x) (fun _ => 0))
    (hupper : ∀ R, PaperWeightedHolderSourceBox κ M β B H ω R →
      paperFixedSourceMap p c lam M κ u Z R = R →
        PaperStepUpperTruncatedData p c lam M C_chem u Z
          (fun x => greenConv c lam R x) (upperBarrier κ M)) :
    PaperTruncatedFixedSourceBoxData p c lam M κ Λ u Z := by
  exact
    { beta := β
      B := B
      H := H
      omega := ω
      uTrap := hu
      hM_nonneg := hM.le
      B_nonneg := hBnn
      sourceBound_eq := hsourceBound_eq
      beta_eq := hbeta_eq
      boxBounds := hbox
      continuousOn :=
        paperFixedSourceMap_continuousOn_of_boxBounds
          (p := p) (c := c) (lam := lam) (M := M) (κ := κ)
          (β := β) (B := B) (H := H) (ω := ω) (u := u) (Z := Z)
          hlam hBnn hHnn hβpos hbox
      boxCubeData := hboxCubeData
      truncation_inactive := by
        intro R hR hfix
        exact paperFixedSource_truncation_inactive_direct_of_trap
          (c := c) (lam := lam) (p := p) (M := M) (κ := κ)
          (β := β) (B := B) (H := H) (C_chem := C_chem) (ω := ω)
          (u := u) (Z := Z) (R := R)
          hlam hκ hM hBnn hR hfix (hlower R hR hfix) (hupper R hR hfix) }

/-- Full output for one Green-produced paper step. -/
structure PaperStepOutput
    (p : CMParams) (c lam M κ Λ : ℝ) (u Z W : ℝ → ℝ) where
  analytic : PaperStepAnalytic p c lam M κ Λ u Z W
  left_rate : ExpLeftRateData W
  C_chem : ℝ
  lowerZero : PaperStepLowerData p c lam M C_chem u Z W (fun _ => 0)
  upperOld : PaperStepUpperData p c lam M C_chem u Z W Z
  upperBarrier :
    PaperStepUpperData p c lam M C_chem u Z W (upperBarrier κ M)
  antitone : PaperStepAntitoneData p c lam M C_chem u Z W

/-- Paper-step output with only the analytic source core carried. -/
structure PaperStepOutputCore
    (p : CMParams) (c lam M κ Λ : ℝ) (u Z W : ℝ → ℝ) where
  analytic : PaperStepAnalyticCore p c lam M κ Λ u Z W
  left_rate : ExpLeftRateData W
  C_chem : ℝ
  lowerZero : PaperStepLowerData p c lam M C_chem u Z W (fun _ => 0)
  upperOld : PaperStepUpperData p c lam M C_chem u Z W Z
  upperBarrier :
    PaperStepUpperData p c lam M C_chem u Z W (upperBarrier κ M)
  antitone : PaperStepAntitoneData p c lam M C_chem u Z W

/-- Close a paper-step output core by filling the bounded-source Green tails. -/
def paperStepOutput_of_core
    {p : CMParams} {c lam M κ Λ : ℝ} {u Z W : ℝ → ℝ}
    (hlam : 0 < lam) (hout : PaperStepOutputCore p c lam M κ Λ u Z W) :
    PaperStepOutput p c lam M κ Λ u Z W :=
  { analytic := paperStepAnalytic_of_core hlam hout.analytic
    left_rate := hout.left_rate
    C_chem := hout.C_chem
    lowerZero := hout.lowerZero
    upperOld := hout.upperOld
    upperBarrier := hout.upperBarrier
    antitone := hout.antitone }

/-- The precise remaining per-step Green fixed-point/trap package. -/
structure PaperGreenStepInput
    (p : CMParams) (c lam M κ Λ : ℝ) (u : ℝ → ℝ) where
  hlam : 0 < lam
  produce : ∀ Z : ℝ → ℝ, Continuous Z → Antitone Z → (∀ x, 0 ≤ Z x) →
      (∀ x, Z x ≤ upperBarrier κ M x) →
      Σ' W : ℝ → ℝ, PaperStepOutput p c lam M κ Λ u Z W

/-- Thinner paper Green-step input: the bounded-source Green tails are closed by
`paperGreenStepInput_of_core`.  Source construction, sliding data, and the
max-principle comparison data remain explicit. -/
structure PaperGreenStepInputCore
    (p : CMParams) (c lam M κ Λ : ℝ) (u : ℝ → ℝ) where
  hlam : 0 < lam
  produce : ∀ Z : ℝ → ℝ, Continuous Z → Antitone Z → (∀ x, 0 ≤ Z x) →
      (∀ x, Z x ≤ upperBarrier κ M x) →
      Σ' W : ℝ → ℝ, PaperStepOutputCore p c lam M κ Λ u Z W

/-- Honest paper-side name for the shared per-step parabolic floor.

This is an alias, not a proof: the frozen construction still carries the same
analytic layer as `RotheStepFloor`, so the paper construction exposes its
corresponding floor as `PaperGreenStepInput`. -/
abbrev PaperPerStepParabolicFloor
    (p : CMParams) (c lam M κ Λ : ℝ) (u : ℝ → ℝ) : Type :=
  PaperGreenStepInput p c lam M κ Λ u

/-- Honest paper-side name after closing bounded-source Green tails. -/
abbrev PaperPerStepParabolicFloorCore
    (p : CMParams) (c lam M κ Λ : ℝ) (u : ℝ → ℝ) : Type :=
  PaperGreenStepInputCore p c lam M κ Λ u

/-- Fill the full paper Green-step input from the thinner core. -/
def paperGreenStepInput_of_core
    {p : CMParams} {c lam M κ Λ : ℝ} {u : ℝ → ℝ}
    (hin : PaperGreenStepInputCore p c lam M κ Λ u) :
    PaperGreenStepInput p c lam M κ Λ u where
  hlam := hin.hlam
  produce := by
    intro Z hZc hZa hZ0 hZB
    obtain ⟨W, hout⟩ := hin.produce Z hZc hZa hZ0 hZB
    exact ⟨W, paperStepOutput_of_core hin.hlam hout⟩

/-- `PaperRotheStepProducer` from the precise Green-step input. -/
def paperRotheStepProducer_of_greenInput
    {p : CMParams} {c lam M κ Λ : ℝ} {u : ℝ → ℝ}
    (hin : PaperGreenStepInput p c lam M κ Λ u) :
    PaperRotheStepProducer p c lam M κ Λ u where
  hlam := hin.hlam
  produce := by
    intro Z hZc hZa hZ0 hZB
    obtain ⟨W, hout⟩ := hin.produce Z hZc hZa hZ0 hZB
    have hstep : ∀ x, paperImplicitStepOp p c (1 / lam) u W x = Z x :=
      paperStep_step_op (c := c) (lam := lam) hin.hlam hout.analytic
    have hnonneg : ∀ x, 0 ≤ W x := by
      have hle := paperStep_ge_lower
        (c := c) (lam := lam) hin.hlam hstep hout.lowerZero
      intro x
      exact hle x
    have hle_old : ∀ x, W x ≤ Z x :=
      paperStep_le_upper (c := c) (lam := lam) hin.hlam hstep hout.upperOld
    have hle_barrier : ∀ x, W x ≤ upperBarrier κ M x :=
      paperStep_le_upper
        (c := c) (lam := lam) hin.hlam hstep hout.upperBarrier
    refine ⟨W, ?_⟩
    exact
      { step_op := hstep
        cont := paperStep_cont (c := c) (lam := lam) hin.hlam hout.analytic
        diff := paperStep_diff (c := c) (lam := lam) hin.hlam hout.analytic
        deriv_le :=
          paperStep_deriv_le (c := c) (lam := lam) hin.hlam hout.analytic
        left_rate := hout.left_rate
        nonneg := hnonneg
        le_barrier := hle_barrier
        le_old := hle_old
        anti := paperStep_antitone_by_sliding
          (c := c) (lam := lam) hin.hlam hstep hZa hout.antitone }
  produce_regular := by
    intro Z hZbase
    obtain ⟨W, hout⟩ :=
      hin.produce Z hZbase.cont hZbase.anti hZbase.nonneg hZbase.le_barrier
    have hstep : ∀ x, paperImplicitStepOp p c (1 / lam) u W x = Z x :=
      paperStep_step_op (c := c) (lam := lam) hin.hlam hout.analytic
    have hnonneg : ∀ x, 0 ≤ W x := by
      have hle := paperStep_ge_lower
        (c := c) (lam := lam) hin.hlam hstep hout.lowerZero
      intro x
      exact hle x
    have hle_old : ∀ x, W x ≤ Z x :=
      paperStep_le_upper (c := c) (lam := lam) hin.hlam hstep hout.upperOld
    have hle_barrier : ∀ x, W x ≤ upperBarrier κ M x :=
      paperStep_le_upper
        (c := c) (lam := lam) hin.hlam hstep hout.upperBarrier
    refine ⟨W, ?_⟩
    exact
      { step_op := hstep
        cont := paperStep_cont (c := c) (lam := lam) hin.hlam hout.analytic
        diff := paperStep_diff (c := c) (lam := lam) hin.hlam hout.analytic
        deriv_le :=
          paperStep_deriv_le (c := c) (lam := lam) hin.hlam hout.analytic
        left_rate := hout.left_rate
        nonneg := hnonneg
        le_barrier := hle_barrier
        le_old := hle_old
        anti := paperStep_antitone_by_sliding
          (c := c) (lam := lam) hin.hlam hstep hZbase.anti hout.antitone }

/-- All paper-step producers from the precise per-profile Green-step input. -/
theorem paperRotheStepProducer_all_of_greenInput
    {p : CMParams} {c lam M κ Λ : ℝ}
    (hinput : ∀ u : ℝ → ℝ, PaperGreenStepInput p c lam M κ Λ u) :
    ∀ u : ℝ → ℝ, PaperRotheStepProducer p c lam M κ Λ u :=
  fun u => paperRotheStepProducer_of_greenInput (hinput u)

/-- `PaperRotheStepProducer` from the explicitly named shared parabolic floor. -/
theorem paperRotheStepProducer_of_parabolicFloor
    {p : CMParams} {c lam M κ Λ : ℝ} {u : ℝ → ℝ}
    (hin : PaperPerStepParabolicFloor p c lam M κ Λ u) :
    PaperRotheStepProducer p c lam M κ Λ u :=
  paperRotheStepProducer_of_greenInput hin

/-- All paper-step producers from the explicitly named shared parabolic floor. -/
theorem paperRotheStepProducer_all_of_parabolicFloor
    {p : CMParams} {c lam M κ Λ : ℝ}
    (hfloor : ∀ u : ℝ → ℝ, PaperPerStepParabolicFloor p c lam M κ Λ u) :
    ∀ u : ℝ → ℝ, PaperRotheStepProducer p c lam M κ Λ u :=
  fun u => paperRotheStepProducer_of_parabolicFloor (hfloor u)

/-- `PaperRotheStepProducer` from the thinner paper Green-step core. -/
theorem paperRotheStepProducer_of_greenCore
    {p : CMParams} {c lam M κ Λ : ℝ} {u : ℝ → ℝ}
    (hin : PaperGreenStepInputCore p c lam M κ Λ u) :
    PaperRotheStepProducer p c lam M κ Λ u :=
  paperRotheStepProducer_of_greenInput (paperGreenStepInput_of_core hin)

/-- All paper-step producers from the thinner paper Green-step core. -/
theorem paperRotheStepProducer_all_of_greenCore
    {p : CMParams} {c lam M κ Λ : ℝ}
    (hinput : ∀ u : ℝ → ℝ, PaperGreenStepInputCore p c lam M κ Λ u) :
    ∀ u : ℝ → ℝ, PaperRotheStepProducer p c lam M κ Λ u :=
  fun u => paperRotheStepProducer_of_greenCore (hinput u)

section AxiomAudit

#print axioms paperStepNonlinearity
#print axioms paperStepSource
#print axioms greenConv_variation_negative
#print axioms greenConv_resolvent_solve
#print axioms paperImplicitStepOp_of_greenConv_source
#print axioms paperImplicitStepOp_exists_of_green_fixed_source
#print axioms IsBddFun.norm_isBoundedUnder_le
#print axioms tendsto_mul_zero_of_isBddFun
#print axioms antitone_isBddFun_tendsto_atTop
#print axioms antitone_isBddFun_tendsto_atBot
#print axioms antitone_isBddFun_has_tail_limits
#print axioms InMonotoneWaveTrapSet.leftTail_Icc
#print axioms paperStepSource_continuous
#print axioms paperStepSource_contDiff_one_of_nonzero
#print axioms paperStepSource_tendsto_of_value_tails
#print axioms paperStepSource_tail_limits
#print axioms paperImplicitStep_le_of_paperBarrier_maxPrinciple
#print axioms paperImplicitStep_le_of_paperBarrier_maxPrinciple_clean
#print axioms paperStep_deriv_le
#print axioms paperStep_diff
#print axioms paperStep_contDiff_two_of_core
#print axioms paperStep_deriv_tendsto_zero_of_core
#print axioms tailHi_contDiff_one
#print axioms tailLo_contDiff_one
#print axioms greenConvDeriv2_contDiff_one
#print axioms greenConvDeriv_contDiff_two
#print axioms greenConv_contDiff_three
#print axioms paperStep_contDiff_three_of_core_reg
#print axioms paperStep_contDiff_three_of_core_smooth_nonzero
#print axioms paperStep_step_op
#print axioms paperImplicitStep_le_of_directSubstep_maxPrinciple_clean
#print axioms paperStep_preserves_antitone_by_shift
#print axioms paperStep_antitone_by_sliding
#print axioms paperStep_le_upper
#print axioms paperStep_ge_lower
#print axioms gWeight_integrableOn_Ioi_of_bounded
#print axioms gWeight_integrableOn_Iic_of_bounded
#print axioms greenKernel_comp_const_sub_mul_integrable_of_bounded
#print axioms greenConv_raw_eq_of_bounded
#print axioms greenConv_eq_translated_integral_of_bounded
#print axioms greenConv_tendsto_atBot_of_source_tendsto
#print axioms greenConvDeriv_tendsto_atBot_of_source_tendsto
#print axioms PaperWeightedHolderSourceBox.greenConv_tendsto_atBot
#print axioms PaperWeightedHolderSourceBox.greenConvDeriv_tendsto_atBot_zero
#print axioms PaperWeightedHolderSourceBox.deriv_greenConv_tendsto_atBot_zero
#print axioms PaperWeightedHolderSourceBox.greenConv_leftTailCauchy_uniform
#print axioms PaperWeightedHolderSourceBox.greenConvDeriv_leftTailCauchy_uniform
#print axioms PaperWeightedHolderSourceBox.greenConvDeriv_leftTailSmall_uniform
#print axioms greenKernel_neg_mul_translate_integrable_of_bounded
#print axioms paperStepSchauderMap
#print axioms abs_sub_le_of_deriv_abs_le
#print axioms greenConv_abs_le_of_bound
#print axioms paperStepSchauderMap_deriv_abs_le_of_source_bound
#print axioms paperStepSchauderMap_abs_sub_le_of_source_bound
#print axioms localUniformSequentiallyCompactRange_inWaveTrapSet_of_uniform_lipschitz_bound
#print axioms PaperStepSchauderMapData.compactRange
#print axioms PaperStepSchauderMapData.exists_fixed
#print axioms PaperStepFixedSourceExistsForSuperTrap.of_schauder
#print axioms PaperStepFixedSourceExistsForSuperTrap.of_schauder_approx
#print axioms paperWeightedHolderExponent
#print axioms paperWeightedHolderExponent_pos
#print axioms paperWeightedHolderExponent_le_one
#print axioms paperWeightedClamp
#print axioms PaperWeightedHolderSourceBox
#print axioms paperStepSource_truncated
#print axioms paperImplicitStepOp_truncated_of_green_fixed_source
#print axioms paperImplicitStep_truncated_le_of_paperBarrier
#print axioms paperImplicitStep_truncated_ge_zero
#print axioms paperFixedSource_truncation_inactive_of_barriers
#print axioms paperStepSource_truncated_eq_paperStepSource_of_Icc
#print axioms rpowTrunc_continuous
#print axioms rpowTrunc_abs_le
#print axioms paperFixedSourceMap_continuous_of_sourceBox
#print axioms paperFixedSourceMap_holder_kernel
#print axioms paperFixedSourceMap_leftTailCauchy_kernel
#print axioms paperFixedSourceMapBoxBounds_of_trap
#print axioms PaperFixedSourceMapBoxBounds.mapsTo
#print axioms PaperFixedSourceMapBoxBounds.compactRange
#print axioms paperTruncatedFixedSourceBoxData_of_trap
#print axioms PaperTruncatedFixedSourceBoxData.exists_fixed
#print axioms PaperStepFixedSourceExistsForSuperTrap.of_truncated_sourceBox
#print axioms paperStepAnalytic_of_core
#print axioms paperStepOutput_of_core
#print axioms paperGreenStepInput_of_core
#print axioms paperRotheStepProducer_of_greenInput
#print axioms paperRotheStepProducer_all_of_greenInput
#print axioms paperRotheStepProducer_of_parabolicFloor
#print axioms paperRotheStepProducer_all_of_parabolicFloor
#print axioms paperRotheStepProducer_of_greenCore
#print axioms paperRotheStepProducer_all_of_greenCore

end AxiomAudit

end ShenWork.Paper1
