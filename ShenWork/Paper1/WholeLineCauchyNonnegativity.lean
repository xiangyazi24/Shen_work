import ShenWork.Paper1.WholeLineCauchyNegativePDE
import Mathlib.Analysis.Calculus.DerivativeTest

open Filter Topology MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Nonnegativity of the whole-line BUC mild fixed point

The clamped nonlinear sources vanish on the strict-negative set.  The imported
negative-set regularity theorem therefore gives the classical equation
`u_t = u_xx - u` exactly where a maximum-principle contradiction needs it.
-/

/-- A strict-negative point has a genuine first spatial derivative. -/
theorem wholeLineCauchyBUCMildFixedPoint_spatial_differentiableAt_at_negative
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC) (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (z : Set.Icc (0 : ℝ) T) (x : ℝ) (ht : 0 < z.1)
    (hneg : (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x < 0) :
    DifferentiableAt ℝ
      (fun w : ℝ =>
        (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 w) x := by
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let F : ℝ → WholeLineBUC := wholeLineCauchyFluxSourceTrajectory p hM hT U
  let R : ℝ → WholeLineBUC := wholeLineCauchyReactionSourceTrajectory p hM hT U
  let MR : ℝ := M + M * (1 + M ^ p.α)
  have hMR : 0 ≤ MR := by
    dsimp [MR]
    exact add_nonneg hM
      (mul_nonneg hM (add_nonneg zero_le_one (Real.rpow_nonneg hM _)))
  have hRcont : Continuous R := by
    simpa [R] using wholeLineCauchyReactionSourceTrajectory_continuous p hM hT U
  have hRnorm : ∀ s, ‖R s‖ ≤ MR := by
    intro s
    simpa [R, MR, wholeLineCauchyReactionSourceTrajectory] using
      wholeLineCauchyTruncatedReactionBUC_norm_le p hM
        (wholeLineBUCTrajectoryExtend hT U s)
  have hRvalue : IntervalIntegrable
      (fun s : ℝ => wholeLineCauchyHeatOp (z.1 - s) (R s).1 x)
      volume 0 z.1 :=
    wholeLineCauchyValueHistory_intervalIntegrable hRcont ht hMR hRnorm x
  have hu₀bound : ∀ y, |u₀.1 y| ≤ ‖u₀‖ := fun y =>
    WholeLineBUC.abs_apply_le_norm u₀ y
  have hheat := wholeLineCauchyHeatOp_hasDerivAt ht
    u₀.1.continuous.aestronglyMeasurable hu₀bound (x := x)
  rcases wholeLineCauchyFluxGradientHistory_hasDerivAt_near_negative
      p hM hT U z x ht hneg with ⟨rho, hrho, hflux⟩
  have hxball : x ∈ Metric.ball x rho := by simpa [Metric.mem_ball] using hrho
  have hreaction := wholeLineCauchyValueHistory_hasDerivAt
    (ρ := 1) hRcont ht hMR (by norm_num) hRnorm hRvalue
  have hfun :
      (fun w : ℝ => (U z).1 w) =
        (fun w : ℝ => wholeLineCauchyHeatOp z.1 u₀.1 w +
          (-p.χ) * wholeLineCauchyGradientHistory F z.1 w +
          wholeLineCauchyValueHistory R z.1 w) := by
    funext w
    simpa [U, F, R] using
      wholeLineCauchyBUCMildFixedPoint_apply_eq_histories
        p hM hT u₀ hsmall z w ht
  change DifferentiableAt ℝ (fun w : ℝ => (U z).1 w) x
  rw [hfun]
  exact ((hheat.add ((hflux x hxball).const_mul (-p.χ))).add hreaction).differentiableAt

/-! ## A maximum principle requiring classical regularity only on the negative set -/

private def negativeSetBarrier
    (u : ℝ → ℝ → ℝ) (eps : ℝ) (t x : ℝ) : ℝ :=
  -u t x - eps * (1 + x ^ 2 + 3 * t)

private lemma second_deriv_nonpos_of_localMax
    {f : ℝ → ℝ} {x : ℝ}
    (hmax : IsLocalMax f x) (hcont : ContinuousAt f x) :
    deriv (deriv f) x ≤ 0 := by
  by_contra hpos
  push Not at hpos
  have hd0 : deriv f x = 0 := hmax.deriv_eq_zero
  have hmin : IsLocalMin f x :=
    isLocalMin_of_deriv_deriv_pos hpos hd0 hcont
  have hconst : f =ᶠ[nhds x] (fun _ => f x) :=
    eventuallyEq_of_isMinFilter_of_isMaxFilter hmin hmax
  have hderiv_const : deriv f =ᶠ[nhds x] deriv (fun _ : ℝ => f x) :=
    hconst.deriv
  have hderiv_zero : deriv f =ᶠ[nhds x] (fun _ : ℝ => 0) := by
    refine hderiv_const.trans ?_
    filter_upwards with y using deriv_const y (f x)
  have heq : deriv (deriv f) x = deriv (fun _ : ℝ => 0) x :=
    hderiv_zero.deriv_eq
  rw [heq, deriv_const] at hpos
  exact lt_irrefl 0 hpos

private lemma time_deriv_nonneg_at_Icc_max
    {f : ℝ → ℝ} {S t f' : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) S) (htpos : 0 < t)
    (hder : HasDerivAt f f' t)
    (hmax : IsMaxOn f (Set.Icc (0 : ℝ) S) t) :
    0 ≤ f' := by
  have hS : 0 ≤ S := le_trans htpos.le ht.2
  have hseg : segment ℝ t 0 ⊆ Set.Icc (0 : ℝ) S :=
    (convex_Icc (0 : ℝ) S).segment_subset ht (left_mem_Icc.mpr hS)
  have htan : (0 : ℝ) - t ∈ posTangentConeAt (Set.Icc (0 : ℝ) S) t :=
    sub_mem_posTangentConeAt_of_segment_subset hseg
  have hle :
      (ContinuousLinearMap.toSpanSingleton ℝ f') ((0 : ℝ) - t) ≤ 0 :=
    hmax.localize.hasFDerivWithinAt_nonpos
      hder.hasFDerivAt.hasFDerivWithinAt htan
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at hle
  nlinarith

private lemma negativeSetBarrier_time_hasDerivAt
    {u : ℝ → ℝ → ℝ} {eps t x ut : ℝ}
    (hu : HasDerivAt (fun tau : ℝ => u tau x) ut t) :
    HasDerivAt (fun tau : ℝ => negativeSetBarrier u eps tau x)
      (-ut - 3 * eps) t := by
  have hlin : HasDerivAt
      (fun tau : ℝ => eps * (1 + x ^ 2 + 3 * tau)) (3 * eps) t := by
    convert (((hasDerivAt_id t).const_mul 3).const_add (1 + x ^ 2)).const_mul eps
      using 1
    ring
  unfold negativeSetBarrier
  exact hu.neg.sub hlin

private lemma negativeSetBarrier_space_hasDerivAt
    {u : ℝ → ℝ → ℝ} {eps t x ux : ℝ}
    (hu : HasDerivAt (fun y : ℝ => u t y) ux x) :
    HasDerivAt (fun y : ℝ => negativeSetBarrier u eps t y)
      (-ux - 2 * eps * x) x := by
  have hquad : HasDerivAt
      (fun y : ℝ => eps * (1 + y ^ 2 + 3 * t)) (2 * eps * x) x := by
    have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
      simpa only [id_eq, Pi.mul_apply, pow_two, mul_one, one_mul, two_mul] using
        (hasDerivAt_id x).mul (hasDerivAt_id x)
    have hinner : HasDerivAt (fun y : ℝ => 1 + y ^ 2 + 3 * t) (2 * x) x := by
      convert (hasDerivAt_const x (1 + 3 * t)).add hsq using 1
      · funext y
        dsimp
        ring
      · ring
    convert hinner.const_mul eps using 1
    ring
  unfold negativeSetBarrier
  exact hu.neg.sub hquad

private lemma negativeSetBarrier_space_second_hasDerivAt
    {u : ℝ → ℝ → ℝ} {eps t x uxx : ℝ}
    (hu2 : HasDerivAt
      (fun y : ℝ => deriv (fun r : ℝ => u t r) y) uxx x)
    (hu1 : ∀ᶠ y in nhds x, DifferentiableAt ℝ (fun r : ℝ => u t r) y) :
    HasDerivAt
      (fun y : ℝ => deriv (fun r : ℝ => negativeSetBarrier u eps t r) y)
      (-uxx - 2 * eps) x := by
  have hevent :
      (fun y : ℝ => deriv (fun r : ℝ => negativeSetBarrier u eps t r) y)
        =ᶠ[nhds x]
      (fun y : ℝ => -deriv (fun r : ℝ => u t r) y - 2 * eps * y) := by
    filter_upwards [hu1] with y hy
    exact (negativeSetBarrier_space_hasDerivAt
      (eps := eps) (t := t) hy.hasDerivAt).deriv
  have hlin : HasDerivAt (fun y : ℝ => 2 * eps * y) (2 * eps) x := by
    simpa [mul_assoc] using (hasDerivAt_id x).const_mul (2 * eps)
  have hright : HasDerivAt
      (fun y : ℝ => -deriv (fun r : ℝ => u t r) y - 2 * eps * y)
      (-uxx - 2 * eps) x := by
    exact hu2.neg.sub hlin
  exact hright.congr_of_eventuallyEq hevent

/-- Whole-line weak minimum principle when classical regularity and the PDE are
available only at strict-negative points. -/
theorem nonnegative_of_negativeSet_pde
    {T : ℝ} (_hT : 0 < T) (u : ℝ → ℝ → ℝ)
    (hcont : Continuous (fun q : ℝ × ℝ => u q.1 q.2))
    (hbound : ∃ B : ℝ, 0 ≤ B ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : ℝ, |u t x| ≤ B)
    (hinit : ∀ x : ℝ, 0 ≤ u 0 x)
    (htime : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T → u t x < 0 →
      HasDerivAt (fun tau : ℝ => u tau x)
        (deriv (fun tau : ℝ => u tau x) t) t)
    (hspace1 : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T → u t x < 0 →
      DifferentiableAt ℝ (fun y : ℝ => u t y) x)
    (hspace2 : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T → u t x < 0 →
      HasDerivAt
        (fun y : ℝ => deriv (fun r : ℝ => u t r) y)
        (deriv (fun y : ℝ => deriv (fun r : ℝ => u t r) y) x) x)
    (hpde : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T → u t x < 0 →
      deriv (fun tau : ℝ => u tau x) t =
        deriv (fun y : ℝ => deriv (fun r : ℝ => u t r) y) x - u t x) :
    ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : ℝ, 0 ≤ u t x := by
  obtain ⟨B, hB, hbound⟩ := hbound
  intro t ht x
  by_contra hnot
  have hneg : u t x < 0 := lt_of_not_ge hnot
  have hA : 0 < 1 + x ^ 2 + 3 * t := by
    nlinarith [sq_nonneg x, ht.1]
  let A : ℝ := 1 + x ^ 2 + 3 * t
  let eps : ℝ := (-u t x) / (2 * A)
  have hA' : 0 < A := by simpa [A] using hA
  have heps : 0 < eps := by
    exact div_pos (neg_pos.mpr hneg) (mul_pos (by norm_num) hA')
  have hepsA : eps * A = (-u t x) / 2 := by
    dsimp [eps]
    field_simp [ne_of_gt hA']
  have htarget : 0 < negativeSetBarrier u eps t x := by
    unfold negativeSetBarrier
    rw [show 1 + x ^ 2 + 3 * t = A by rfl, hepsA]
    linarith
  let S : ℝ := (t + T) / 2
  have htS : t < S := by dsimp [S]; linarith [ht.2]
  have hST : S < T := by dsimp [S]; linarith [ht.2]
  have hS : 0 < S := lt_of_le_of_lt ht.1 htS
  have htIcc : t ∈ Set.Icc (0 : ℝ) S := ⟨ht.1, htS.le⟩
  let R : ℝ := max (|x| + 1) (Real.sqrt (B / eps + 1) + 1)
  have hR : 0 < R := by
    exact lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hxR : |x| < R := by
    linarith [le_max_left (|x| + 1) (Real.sqrt (B / eps + 1) + 1)]
  have hinside : x ∈ Set.Icc (-R) R := by
    exact ⟨le_of_lt (abs_lt.mp hxR).1, le_of_lt (abs_lt.mp hxR).2⟩
  have hRlarge : B < eps * (1 + R ^ 2) := by
    have hrootArg : 0 ≤ B / eps + 1 := by positivity
    have hsqrtR : Real.sqrt (B / eps + 1) < R := by
      linarith [le_max_right (|x| + 1) (Real.sqrt (B / eps + 1) + 1)]
    have hargRsq : B / eps + 1 < R ^ 2 := by
      nlinarith [Real.sq_sqrt hrootArg, Real.sqrt_nonneg (B / eps + 1), hsqrtR, hR]
    have hdiv : B / eps < 1 + R ^ 2 := by linarith
    have hmul := mul_lt_mul_of_pos_right hdiv heps
    simpa [div_mul_cancel₀ B (ne_of_gt heps), mul_comm, mul_left_comm, mul_assoc]
      using hmul
  let K : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) S ×ˢ Set.Icc (-R) R
  have hpsi_cont : ContinuousOn
      (fun q : ℝ × ℝ => negativeSetBarrier u eps q.1 q.2) K := by
    have hpoly : Continuous
        (fun q : ℝ × ℝ => eps * (1 + q.2 ^ 2 + 3 * q.1)) := by
      fun_prop
    unfold negativeSetBarrier
    exact (hcont.neg.sub hpoly).continuousOn
  have hKcompact : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKne : K.Nonempty := by
    refine ⟨(0, 0), ?_⟩
    exact ⟨⟨le_rfl, hS.le⟩, ⟨by linarith [hR], hR.le⟩⟩
  obtain ⟨q, hqK, hqmax⟩ := hKcompact.exists_isMaxOn hKne hpsi_cont
  have htargetK : (t, x) ∈ K := ⟨htIcc, hinside⟩
  have hqpos : 0 < negativeSetBarrier u eps q.1 q.2 :=
    lt_of_lt_of_le htarget (hqmax htargetK)
  rcases q with ⟨t₀, x₀⟩
  have hinitNeg : ∀ y : ℝ, negativeSetBarrier u eps 0 y < 0 := by
    intro y
    unfold negativeSetBarrier
    nlinarith [hinit y, sq_nonneg y, heps]
  have hsideNeg : ∀ s ∈ Set.Icc (0 : ℝ) S,
      negativeSetBarrier u eps s R < 0 ∧
        negativeSetBarrier u eps s (-R) < 0 := by
    intro s hs
    have hsT : s ∈ Set.Icc (0 : ℝ) T :=
      ⟨hs.1, le_trans hs.2 hST.le⟩
    have hp := hbound s hsT R
    have hn := hbound s hsT (-R)
    have hp' : -u s R ≤ B := (neg_le_abs (u s R)).trans hp
    have hn' : -u s (-R) ≤ B := (neg_le_abs (u s (-R))).trans hn
    have htimeTerm : 0 ≤ eps * (3 * s) :=
      mul_nonneg heps.le (mul_nonneg (by norm_num) hs.1)
    constructor
    · unfold negativeSetBarrier
      nlinarith
    · unfold negativeSetBarrier
      have hsq : (-R) ^ 2 = R ^ 2 := by ring
      rw [hsq]
      nlinarith
  have ht₀ne : t₀ ≠ 0 := by
    intro hz
    have hneg0 := hinitNeg x₀
    have hle0 := hqpos
    simp only [hz] at hle0
    linarith
  have hx₀neR : x₀ ≠ R := by
    intro hz
    have hnegR := (hsideNeg t₀ hqK.1).1
    have hleR := hqpos
    simp only [hz] at hleR
    linarith
  have hx₀neNegR : x₀ ≠ -R := by
    intro hz
    have hnegR := (hsideNeg t₀ hqK.1).2
    have hleR := hqpos
    simp only [hz] at hleR
    linarith
  have ht₀pos : 0 < t₀ := lt_of_le_of_ne hqK.1.1 (Ne.symm ht₀ne)
  have ht₀T : t₀ < T := lt_of_le_of_lt hqK.1.2 hST
  have ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T := ⟨ht₀pos, ht₀T⟩
  have hx₀ : x₀ ∈ Set.Ioo (-R) R :=
    ⟨lt_of_le_of_ne hqK.2.1 (Ne.symm hx₀neNegR),
      lt_of_le_of_ne hqK.2.2 hx₀neR⟩
  have hu₀neg : u t₀ x₀ < 0 := by
    unfold negativeSetBarrier at hqpos
    nlinarith [sq_nonneg x₀, heps, ht₀pos]
  let ut : ℝ := deriv (fun tau : ℝ => u tau x₀) t₀
  let uxx : ℝ := deriv (fun y : ℝ => deriv (fun r : ℝ => u t₀ r) y) x₀
  have hut : HasDerivAt (fun tau : ℝ => u tau x₀) ut t₀ :=
    htime ht₀ hu₀neg
  have hpsiTime := negativeSetBarrier_time_hasDerivAt (eps := eps) hut
  have htimeMax : IsMaxOn
      (fun s : ℝ => negativeSetBarrier u eps s x₀)
      (Set.Icc (0 : ℝ) S) t₀ := by
    intro s hs
    exact @hqmax (s, x₀) ⟨hs, hqK.2⟩
  have hpsiTimeNonneg : 0 ≤ -ut - 3 * eps :=
    time_deriv_nonneg_at_Icc_max hqK.1 ht₀pos hpsiTime htimeMax
  have hsliceCont : Continuous (fun y : ℝ => u t₀ y) := by
    fun_prop
  have hnegNear : ∀ᶠ y in nhds x₀, u t₀ y < 0 :=
    hsliceCont.continuousAt (isOpen_Iio.mem_nhds hu₀neg)
  have hu1Near : ∀ᶠ y in nhds x₀,
      DifferentiableAt ℝ (fun r : ℝ => u t₀ r) y := by
    filter_upwards [hnegNear] with y hy
    exact hspace1 ht₀ hy
  have huxx : HasDerivAt
      (fun y : ℝ => deriv (fun r : ℝ => u t₀ r) y) uxx x₀ :=
    hspace2 ht₀ hu₀neg
  have hpsiSpace2 := negativeSetBarrier_space_second_hasDerivAt
    (eps := eps) huxx hu1Near
  have hspaceMaxOn : IsMaxOn
      (fun y : ℝ => negativeSetBarrier u eps t₀ y)
      (Set.Icc (-R) R) x₀ := by
    intro y hy
    exact @hqmax (t₀, y) ⟨hqK.1, hy⟩
  have hspaceNhds : Set.Icc (-R) R ∈ nhds x₀ := by
    rw [← mem_interior_iff_mem_nhds, interior_Icc]
    exact hx₀
  have hspaceLocal : IsLocalMax
      (fun y : ℝ => negativeSetBarrier u eps t₀ y) x₀ :=
    hspaceMaxOn.isLocalMax hspaceNhds
  have hbarCont : ContinuousAt
      (fun y : ℝ => negativeSetBarrier u eps t₀ y) x₀ := by
    unfold negativeSetBarrier
    exact hsliceCont.continuousAt.neg.sub (by fun_prop)
  have hpsiSpaceNonpos : -uxx - 2 * eps ≤ 0 := by
    have hsign := second_deriv_nonpos_of_localMax hspaceLocal hbarCont
    rw [hpsiSpace2.deriv] at hsign
    exact hsign
  have hpde₀ : ut = uxx - u t₀ x₀ := hpde ht₀ hu₀neg
  nlinarith

/-- The canonical clamped BUC fixed point is nonnegative at every time strictly
before the construction horizon. -/
theorem wholeLineCauchyBUCMildFixedPoint_nonnegative_Ico
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 < T)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x : ℝ, 0 ≤ u₀.1 x)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1) :
    ∀ (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) T), ∀ x : ℝ,
      0 ≤
        (wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall
          ⟨t, ht.1, ht.2.le⟩).1 x := by
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall
  let ue : ℝ → ℝ → ℝ :=
    fun t x => (wholeLineBUCTrajectoryExtend hT.le U t).1 x
  have hcont : Continuous (fun q : ℝ × ℝ => ue q.1 q.2) := by
    have hmap : Continuous
        (fun q : ℝ × ℝ => (Set.projIcc 0 T hT.le q.1, q.2)) :=
      (continuous_projIcc.comp continuous_fst).prodMk continuous_snd
    simpa [ue, wholeLineBUCTrajectoryExtend] using
      (wholeLineBUCTrajectory_jointContinuous U).comp hmap
  have hbound : ∃ B : ℝ, 0 ≤ B ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : ℝ, |ue t x| ≤ B := by
    let D : ℝ := wholeLineCauchyBUCMildDisplacement p M T
    refine ⟨D + ‖u₀‖, add_nonneg
      (wholeLineCauchyBUCMildDisplacement_nonneg p hM hT.le) (norm_nonneg u₀), ?_⟩
    intro t ht x
    let z : Set.Icc (0 : ℝ) T := ⟨t, ht⟩
    let H : WholeLineBUC := wholeLineCauchyHeatBUCTotal t u₀
    have heq : wholeLineBUCTrajectoryExtend hT.le U t = U z :=
      wholeLineBUCTrajectoryExtend_eq hT.le U ht
    have hdist : dist (U z) H ≤ D := by
      simpa [U, H, D, z] using
        wholeLineCauchyBUCMildFixedPoint_dist_homogeneous_le
          p hM hT.le u₀ hsmall z
    have hpoint : |(U z).1 x - H.1 x| ≤ D :=
      (WholeLineBUC.pointwise_abs_sub_le_dist (U z) H x).trans hdist
    have hH : |H.1 x| ≤ ‖u₀‖ :=
      (WholeLineBUC.abs_apply_le_norm H x).trans
        (wholeLineCauchyHeatBUCTotal_norm_le_of_nonneg ht.1 u₀)
    change |(wholeLineBUCTrajectoryExtend hT.le U t).1 x| ≤ D + ‖u₀‖
    rw [heq]
    calc
      |(U z).1 x| = |((U z).1 x - H.1 x) + H.1 x| := by ring_nf
      _ ≤ |(U z).1 x - H.1 x| + |H.1 x| := abs_add_le _ _
      _ ≤ D + ‖u₀‖ := add_le_add hpoint hH
  have hinit : ∀ x : ℝ, 0 ≤ ue 0 x := by
    intro x
    have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
    dsimp [ue]
    rw [show wholeLineBUCTrajectoryExtend hT.le U 0 = U ⟨0, hzero⟩ by
      exact wholeLineBUCTrajectoryExtend_eq hT.le U hzero]
    rw [show U ⟨0, hzero⟩ = u₀ by
      exact wholeLineCauchyBUCMildFixedPoint_initial
        p hM hT.le u₀ hsmall hzero]
    exact hu₀ x
  have htime : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T → ue t x < 0 →
      HasDerivAt (fun tau : ℝ => ue tau x)
        (deriv (fun tau : ℝ => ue tau x) t) t := by
    intro t x ht hneg
    let z : Set.Icc (0 : ℝ) T := ⟨t, ht.1.le, ht.2.le⟩
    have heq : wholeLineBUCTrajectoryExtend hT.le U t = U z :=
      wholeLineBUCTrajectoryExtend_eq hT.le U z.2
    have hneg' : (U z).1 x < 0 := by simpa [ue, heq] using hneg
    have h := wholeLineCauchyBUCMildFixedPoint_time_hasDerivAt_at_negative
      p hM hT.le u₀ hsmall z x ht.1 ht.2 hneg'
    change HasDerivAt
      (fun q : ℝ => (wholeLineBUCTrajectoryExtend hT.le U q).1 x) _ t at h
    change HasDerivAt
      (fun q : ℝ => (wholeLineBUCTrajectoryExtend hT.le U q).1 x)
      (deriv (fun q : ℝ => (wholeLineBUCTrajectoryExtend hT.le U q).1 x) t) t
    convert h using 1
    exact h.deriv
  have hspace1 : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T → ue t x < 0 →
      DifferentiableAt ℝ (fun y : ℝ => ue t y) x := by
    intro t x ht hneg
    let z : Set.Icc (0 : ℝ) T := ⟨t, ht.1.le, ht.2.le⟩
    have heq : wholeLineBUCTrajectoryExtend hT.le U t = U z :=
      wholeLineBUCTrajectoryExtend_eq hT.le U z.2
    have hneg' : (U z).1 x < 0 := by simpa [ue, heq] using hneg
    simpa [ue, heq] using
      wholeLineCauchyBUCMildFixedPoint_spatial_differentiableAt_at_negative
        p hM hT.le u₀ hsmall z x ht.1 hneg'
  have hspace2 : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T → ue t x < 0 →
      HasDerivAt
        (fun y : ℝ => deriv (fun r : ℝ => ue t r) y)
        (deriv (fun y : ℝ => deriv (fun r : ℝ => ue t r) y) x) x := by
    intro t x ht hneg
    let z : Set.Icc (0 : ℝ) T := ⟨t, ht.1.le, ht.2.le⟩
    have heq : wholeLineBUCTrajectoryExtend hT.le U t = U z :=
      wholeLineBUCTrajectoryExtend_eq hT.le U z.2
    have hneg' : (U z).1 x < 0 := by simpa [ue, heq] using hneg
    have h := wholeLineCauchyBUCMildFixedPoint_spatial_second_hasDerivAt_at_negative
      p hM hT.le u₀ hsmall z x ht.1 hneg'
    change HasDerivAt
      (fun y : ℝ => deriv (fun r : ℝ => (U z).1 r) y) _ x at h
    have hslice : (fun r : ℝ => ue t r) = (fun r : ℝ => (U z).1 r) := by
      funext r
      simp [ue, heq]
    rw [hslice]
    convert h using 1
    exact h.deriv
  have hpde : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioo (0 : ℝ) T → ue t x < 0 →
      deriv (fun tau : ℝ => ue tau x) t =
        deriv (fun y : ℝ => deriv (fun r : ℝ => ue t r) y) x - ue t x := by
    intro t x ht hneg
    let z : Set.Icc (0 : ℝ) T := ⟨t, ht.1.le, ht.2.le⟩
    have heq : wholeLineBUCTrajectoryExtend hT.le U t = U z :=
      wholeLineBUCTrajectoryExtend_eq hT.le U z.2
    have hneg' : (U z).1 x < 0 := by simpa [ue, heq] using hneg
    simpa [ue, heq] using wholeLineCauchyBUCMildFixedPoint_negative_pde
      p hM hT.le u₀ hsmall z x ht.1 ht.2 hneg'
  have hnonneg := nonnegative_of_negativeSet_pde hT ue hcont hbound hinit
    htime hspace1 hspace2 hpde
  intro t ht x
  simpa [ue, U, wholeLineBUCTrajectoryExtend_eq hT.le U ⟨ht.1, ht.2.le⟩] using
    hnonneg t ht x

/-- The canonical clamped BUC fixed point is nonnegative on the closed
construction interval.  The terminal slice follows from time continuity; no
endpoint PDE identity is needed. -/
theorem wholeLineCauchyBUCMildFixedPoint_nonnegative
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 < T)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x : ℝ, 0 ≤ u₀.1 x)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1) :
    ∀ (z : Set.Icc (0 : ℝ) T), ∀ x : ℝ,
      0 ≤ (wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall z).1 x := by
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall
  let ue : ℝ → ℝ → ℝ :=
    fun t x => (wholeLineBUCTrajectoryExtend hT.le U t).1 x
  have htimeCont (x : ℝ) : Continuous (fun t : ℝ => ue t x) := by
    dsimp [ue]
    exact (wholeLineBUCEvalCLM x).continuous.comp
      (wholeLineBUCTrajectoryExtend_continuous hT.le U)
  intro z x
  by_cases hlt : z.1 < T
  · exact wholeLineCauchyBUCMildFixedPoint_nonnegative_Ico
      p hM hT u₀ hu₀ hsmall z.1 ⟨z.2.1, hlt⟩ x
  · have hzT : z.1 = T := le_antisymm z.2.2 (le_of_not_gt hlt)
    have htend : Tendsto (fun t : ℝ => ue t x) (𝓝[<] T) (𝓝 (ue T x)) :=
      (htimeCont x).continuousAt.mono_left inf_le_left
    have hevent : ∀ᶠ t in 𝓝[<] T, 0 ≤ ue t x := by
      filter_upwards [self_mem_nhdsWithin,
        (eventually_gt_nhds hT).filter_mono inf_le_left] with t htT ht0
      have ht : t ∈ Set.Ico (0 : ℝ) T := ⟨ht0.le, htT⟩
      simpa [ue, U, wholeLineBUCTrajectoryExtend_eq hT.le U ⟨ht.1, ht.2.le⟩]
        using wholeLineCauchyBUCMildFixedPoint_nonnegative_Ico
          p hM hT u₀ hu₀ hsmall t ht x
    have hTnonneg : 0 ≤ ue T x :=
      isClosed_Ici.mem_of_tendsto htend hevent
    have hznonneg : 0 ≤ ue z.1 x := by simpa [hzT] using hTnonneg
    simpa [ue, U, wholeLineBUCTrajectoryExtend_eq hT.le U z.2] using hznonneg

/-- For nonnegative BUC data there is a positive construction window on which
the canonical fixed point lies in the physical strip.  Thus both sides of the
global clamp are inactive. -/
theorem exists_wholeLineCauchyBUCMildFixedPoint_in_physical_strip
    (p : CMParams) (u₀ : WholeLineBUC)
    (hu₀ : ∀ x : ℝ, 0 ≤ u₀.1 x) :
    let M := ‖u₀‖ + 1
    ∃ (T : ℝ) (hT : 0 < T)
      (hsmall : wholeLineCauchyBUCMildRate p M T < 1),
      ∀ (z : Set.Icc (0 : ℝ) T) (x : ℝ),
        (wholeLineCauchyBUCMildFixedPoint p (by positivity) hT.le
          u₀ hsmall z).1 x ∈ Set.Ico (0 : ℝ) M := by
  let M := ‖u₀‖ + 1
  obtain ⟨T, hT, hsmall, hupper⟩ :=
    exists_wholeLineCauchyBUCMildFixedPoint_below_clamp p u₀
  refine ⟨T, hT, hsmall, ?_⟩
  intro z x
  exact ⟨wholeLineCauchyBUCMildFixedPoint_nonnegative
    p (by positivity) hT u₀ hu₀ hsmall z x, hupper z x⟩

/-- Once the canonical fixed point lies in `[0,M]`, its pointwise equation is
the original, unclamped whole-line Duhamel equation. -/
theorem wholeLineCauchyBUCMildFixedPoint_eq_original_mildMap_of_mem_Icc
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC) (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (hstrip : ∀ (z : Set.Icc (0 : ℝ) T) (x : ℝ),
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M) :
    let U := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    ∀ (z : Set.Icc (0 : ℝ) T) (x : ℝ),
      (U z).1 x = wholeLineCauchyMildMap p u₀.1
        (fun t y => (wholeLineBUCTrajectoryExtend hT U t).1 y) z.1 x := by
  dsimp only
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let ue : ℝ → ℝ → ℝ :=
    fun t x => (wholeLineBUCTrajectoryExtend hT U t).1 x
  let F : ℝ → WholeLineBUC := wholeLineCauchyFluxSourceTrajectory p hM hT U
  let R : ℝ → WholeLineBUC := wholeLineCauchyReactionSourceTrajectory p hM hT U
  have hextStrip (s x : ℝ) : ue s x ∈ Set.Icc (0 : ℝ) M := by
    dsimp [ue, U, wholeLineBUCTrajectoryExtend]
    exact hstrip (Set.projIcc 0 T hT s) x
  have hF (s : ℝ) : (F s).1 = wholeLineChemotaxisFlux p (ue s) := by
    apply funext
    intro x
    change wholeLineCauchyTruncatedFlux p M
      (wholeLineBUCTrajectoryExtend hT U s).1 x =
        wholeLineChemotaxisFlux p (ue s) x
    exact congrFun
      (wholeLineCauchyTruncatedFlux_eq_of_mem_Icc p hM (hextStrip s)) x
  have hR (s : ℝ) : (R s).1 = wholeLineCauchyShiftedReaction p (ue s) := by
    apply funext
    intro x
    change wholeLineCauchyTruncatedReaction p M
      (wholeLineBUCTrajectoryExtend hT U s).1 x =
        wholeLineCauchyShiftedReaction p (ue s) x
    exact congrFun
      (wholeLineCauchyTruncatedReaction_eq_of_mem_Icc p hM (hextStrip s)) x
  intro z x
  by_cases hz : z.1 = 0
  · have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
    have hzEq : z = ⟨0, hzero⟩ := Subtype.ext hz
    rw [hzEq]
    rw [show U ⟨0, hzero⟩ = u₀ by
      exact wholeLineCauchyBUCMildFixedPoint_initial
        p hM hT u₀ hsmall hzero]
    exact (wholeLineCauchyMildMap_zero p u₀.1
      (fun t y => (wholeLineBUCTrajectoryExtend hT U t).1 y) x).symm
  · have ht : 0 < z.1 := lt_of_le_of_ne z.2.1 (Ne.symm hz)
    have hgrad : wholeLineCauchyGradientHistory F z.1 x =
        wholeLineCauchyGradientDuhamel
          (fun s => wholeLineChemotaxisFlux p (ue s)) z.1 x := by
      unfold wholeLineCauchyGradientHistory wholeLineCauchyGradientDuhamel
      simp_rw [hF]
    have hvalue : wholeLineCauchyValueHistory R z.1 x =
        wholeLineCauchyValueDuhamel
          (fun s => wholeLineCauchyShiftedReaction p (ue s)) z.1 x := by
      unfold wholeLineCauchyValueHistory wholeLineCauchyValueDuhamel
      simp_rw [hR]
      rw [intervalIntegral.integral_of_le ht.le,
        ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    have hfix := wholeLineCauchyBUCMildFixedPoint_apply_eq_histories
      p hM hT u₀ hsmall z x ht
    change (U z).1 x =
      wholeLineCauchyHeatOp z.1 u₀.1 x +
        (-p.χ) * wholeLineCauchyGradientHistory F z.1 x +
        wholeLineCauchyValueHistory R z.1 x at hfix
    rw [hgrad, hvalue] at hfix
    simpa [wholeLineCauchyMildMap, hz, wholeLineCauchyChemDuhamel,
      wholeLineCauchyReactionDuhamel, ue] using hfix

/-- Paper-faithful local BUC mild existence for arbitrary nonnegative BUC
data: the constructed trajectory stays physical and solves the original
unclamped equation. -/
theorem exists_wholeLineCauchy_original_BUC_mildSolution
    (p : CMParams) (u₀ : WholeLineBUC)
    (hu₀ : ∀ x : ℝ, 0 ≤ u₀.1 x) :
    let M := ‖u₀‖ + 1
    ∃ (T : ℝ) (hT : 0 < T)
      (hsmall : wholeLineCauchyBUCMildRate p M T < 1),
      let U := wholeLineCauchyBUCMildFixedPoint p (by positivity) hT.le
        u₀ hsmall
      (∀ (z : Set.Icc (0 : ℝ) T) (x : ℝ),
        (U z).1 x ∈ Set.Ico (0 : ℝ) M) ∧
      ∀ (z : Set.Icc (0 : ℝ) T) (x : ℝ),
        (U z).1 x = wholeLineCauchyMildMap p u₀.1
          (fun t y => (wholeLineBUCTrajectoryExtend hT.le U t).1 y) z.1 x := by
  let M := ‖u₀‖ + 1
  obtain ⟨T, hT, hsmall, hstrip⟩ :=
    exists_wholeLineCauchyBUCMildFixedPoint_in_physical_strip p u₀ hu₀
  refine ⟨T, hT, hsmall, hstrip, ?_⟩
  apply wholeLineCauchyBUCMildFixedPoint_eq_original_mildMap_of_mem_Icc
    p (by positivity) hT.le u₀ hsmall
  intro z x
  exact ⟨(hstrip z x).1, (hstrip z x).2.le⟩

section WholeLineCauchyNonnegativityAxiomAudit

#print axioms nonnegative_of_negativeSet_pde
#print axioms wholeLineCauchyBUCMildFixedPoint_nonnegative
#print axioms exists_wholeLineCauchyBUCMildFixedPoint_in_physical_strip
#print axioms wholeLineCauchyBUCMildFixedPoint_eq_original_mildMap_of_mem_Icc
#print axioms exists_wholeLineCauchy_original_BUC_mildSolution

end WholeLineCauchyNonnegativityAxiomAudit

end ShenWork.Paper1
