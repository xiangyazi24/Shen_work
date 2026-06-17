/-
  ShenWork/Paper1/WavePaperRotheProducer.lean

  Paper-step producer accounting.

  This module discharges `PaperRotheStepProducer` from a precise Green-step
  input.  The remaining unproved sub-lemma is not the producer itself: it is the
  per-step Green fixed-point existence/trap package `PaperGreenStepInput`.

  Frozen-producer inventory: the frozen `RotheStepProducer` is not closed below
  this layer either.  It is assembled from the carried `RotheStepFloor` /
  `RotheStepInput` floor in `WaveRotheStepClose.lean` and
  `WaveRotheProducer.lean`, where the residual Green tails, flux decay/IBP, and
  source data are explicitly named.  Consequently this paper-side input is the
  analogous shared per-step parabolic floor, not a faked Banach existence proof.

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

  No `sorry`/`axiom`/`native_decide`/`admit`.
-/
import ShenWork.Paper1.WaveRotheStepClose

open Filter Topology MeasureTheory Real Set

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

theorem paperWaveOperator_eq_linear_add_paperStepNonlinearity
    (p : CMParams) (c : ℝ) (u W : ℝ → ℝ) (x : ℝ) :
    paperWaveOperator p c u W x =
      iteratedDeriv 2 W x + c * deriv W x
        + paperStepNonlinearity p u W x := by
  unfold paperWaveOperator paperStepNonlinearity
  ring_nf

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
the linear-resolvent half of the per-step construction; the Banach argument has
to supply `hRfix`. -/
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

/-- Build the analytic core once the Banach fixed source has been produced.

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

/-- Full output for one Green-produced paper step. -/
structure PaperStepOutput
    (p : CMParams) (c lam M κ Λ : ℝ) (u Z W : ℝ → ℝ) where
  analytic : PaperStepAnalytic p c lam M κ Λ u Z W
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
        nonneg := hnonneg
        le_barrier := hle_barrier
        le_old := hle_old
        anti := paperStep_antitone_by_sliding
          (c := c) (lam := lam) hin.hlam hstep hZa hout.antitone }

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
#print axioms paperStepSource_continuous
#print axioms paperStepSource_contDiff_one_of_nonzero
#print axioms paperImplicitStep_le_of_paperBarrier_maxPrinciple
#print axioms paperImplicitStep_le_of_paperBarrier_maxPrinciple_clean
#print axioms paperStep_deriv_le
#print axioms paperStep_diff
#print axioms paperStep_contDiff_two_of_core
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
#print axioms greenKernel_neg_mul_translate_integrable_of_bounded
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
