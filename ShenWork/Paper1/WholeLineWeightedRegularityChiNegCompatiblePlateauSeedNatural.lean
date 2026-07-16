import ShenWork.Paper1.WholeLineWeightedRegularityPlateauSeedNatural

open Filter Set Topology Real

noncomputable section

namespace ShenWork.Paper1

/-!
# A paper-compatible lower-plateau seed

The profile-level seed in `WholeLineWeightedRegularityPlateauSeedNatural`
chooses a barrier below a positive slice.  Here the same choice is made with
the paper's exact negative-sensitivity parameter conditions and its constant
subsolution threshold built into the *same* coefficient `D`.
-/

/-- A positive profile with the paper's one-sided floor, weighted pointwise
envelope, and sharp wave tail lies above a patched two-exponential plateau
whose parameters simultaneously satisfy the exact Lemma 4.2 range, the
`D_min` bound, and the nonpositive-sensitivity constant-subsolution bound.

The order of choices is load-bearing: first choose `kappaTilde`; then compute
`paperDMin` for that exponent; finally choose one `D` whose splice height is
below both the profile floor and `1 / (1 + |p.χ|)`.  The additional bound
`Bfun kappaTilde < D` lets a scaled-trap consumer supply its genuine
`kappaTilde`-dependent chemotactic margin without changing this choice. -/
theorem
    exists_chiNonpos_compatible_lowerBarrierPlateau_seed_of_profile_bounds
    (p : CMParams) (Bfun : ℝ → ℝ)
    {c Q κ κ₁ eta cap C : ℝ} {w U : ℝ → ℝ}
    (hκ : 0 < κ) (hκ_one : κ < 1)
    (hκ₁ : κ < κ₁) (heta : κ < eta) (hcap : κ < cap)
    (hQ : 1 ≤ Q)
    (hcapRange :
      cap ≤ min ((1 + p.α) * κ) (min (p.m * κ + 1 / 2) 1))
    (hc : c = κ + κ⁻¹) (hχ : p.χ ≤ 0)
    (hα_le : p.α ≤ p.m + p.γ - 1)
    (hwcont : Continuous w) (hwpos : ∀ x, 0 < w x)
    (hwleft : StrictlyPositiveAtLeft w)
    (hC : 0 ≤ C)
    (henv : ∀ x, |w x - U x| ≤ C * Real.exp (-eta * x))
    (htail : HasWaveRightTailAsymptotic c κ₁ U) :
    ∃ kappaTilde D : ℝ,
      κ < kappaTilde ∧
      kappaTilde < κ₁ ∧
      kappaTilde < eta ∧
      kappaTilde < cap ∧
      kappaTilde < 2 * κ ∧
      PaperLemma42ExactConditions p c κ kappaTilde Q ∧
      1 ≤ D ∧
      paperDMin p.χ Q κ kappaTilde p.m p.γ c < D ∧
      Bfun kappaTilde < D ∧
      (∀ x, lowerBarrierPlateau κ kappaTilde D x ≤
        constantSubsolutionThreshold p.χ κ kappaTilde D) ∧
      ∀ x, lowerBarrierPlateau κ kappaTilde D x ≤ w x := by
  have hkappaTop :
      κ < min κ₁ (min eta (min cap (2 * κ))) := by
    exact lt_min hκ₁ (lt_min heta (lt_min hcap (by linarith)))
  obtain ⟨kappaTilde, hkappaTilde, hkappaTildeTop⟩ :=
    exists_between hkappaTop
  have hkappaTildeκ₁ : kappaTilde < κ₁ :=
    hkappaTildeTop.trans_le (min_le_left _ _)
  have hkappaTildeEta : kappaTilde < eta :=
    hkappaTildeTop.trans_le
      ((min_le_right κ₁ _).trans (min_le_left _ _))
  have hkappaTildeCap : kappaTilde < cap :=
    hkappaTildeTop.trans_le
      ((min_le_right κ₁ _).trans
        ((min_le_right eta _).trans (min_le_left _ _)))
  have hkappaTildeTwo : kappaTilde < 2 * κ :=
    hkappaTildeTop.trans_le
      ((min_le_right κ₁ _).trans
        ((min_le_right eta _).trans
          ((min_le_right cap _).trans le_rfl)))
  have hkappaTildeRange :
      kappaTilde ≤
        min ((1 + p.α) * κ) (min (p.m * κ + 1 / 2) 1) :=
    hkappaTildeCap.le.trans hcapRange
  let hcond : PaperLemma42ExactConditions p c κ kappaTilde Q :=
    { hκ0 := hκ
      hκ1 := hκ_one
      hgap := hkappaTilde
      hrange := hkappaTildeRange
      hM := hQ
      hc := hc
      hχ := hχ
      hα_le := hα_le }
  have hkappa_eq : kappa c = κ :=
    kappa_eq_of_pos_lt_one_kappa_speed hκ hκ_one hc
  rcases hwleft with ⟨delta, hdelta, hdeltaEventually⟩
  obtain ⟨L, hL⟩ := eventually_atBot.1 hdeltaEventually
  have hhalfEventually : ∀ᶠ x in atTop,
      (1 / 2 : ℝ) * Real.exp (-κ * x) ≤ w x := by
    simpa [hkappa_eq] using
      (eventually_half_exp_le_of_wave_tail_and_weighted_envelope
        (c := c) (κ₁ := κ₁) (eta := eta) (C := C) (w := w) (U := U)
        (by simpa [hkappa_eq] using hκ₁)
        (by simpa [hkappa_eq] using heta) henv htail)
  have hrightEventually :=
    hhalfEventually.and htail.eventually_abs_sub_exp_le
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.1 hrightEventually
  let R : ℝ := max L (max 0 R₀)
  have hLR : L ≤ R := le_max_left _ _
  have hRzero : 0 ≤ R :=
    (le_max_left (0 : ℝ) R₀).trans (le_max_right L _)
  have hR₀R : R₀ ≤ R :=
    (le_max_right (0 : ℝ) R₀).trans (le_max_right L _)
  obtain ⟨middleFloor, hmiddleFloor, hmiddle⟩ :=
    isCompact_Icc.exists_forall_le' hwcont.continuousOn
      (fun x _hx => hwpos x)
  let smallHeight : ℝ := min delta
    (min middleFloor
      (min (Real.exp (-κ * R)) (1 / (1 + |p.χ|))))
  have hsmallHeight : 0 < smallHeight := by
    dsimp [smallHeight]
    exact lt_min hdelta
      (lt_min hmiddleFloor
        (lt_min (Real.exp_pos _) (by positivity)))
  let Dbase : ℝ := max 1
    (max (paperDMin p.χ Q κ kappaTilde p.m p.γ c)
      (max (Bfun kappaTilde) (1 + C)))
  obtain ⟨D, hDbase, hspliceSmall⟩ :=
    exists_D_gt_with_exp_xplus_le
      (B := Dbase) hκ (sub_pos.mpr hkappaTilde) hsmallHeight
  have hDone : 1 ≤ D :=
    (le_max_left 1 _).trans hDbase.le
  have hDmin :
      paperDMin p.χ Q κ kappaTilde p.m p.γ c < D :=
    lt_of_le_of_lt
      ((le_max_left
        (paperDMin p.χ Q κ kappaTilde p.m p.γ c)
          (max (Bfun kappaTilde) (1 + C))).trans
          (le_max_right 1 _))
      hDbase
  have hBfun : Bfun kappaTilde < D :=
    lt_of_le_of_lt
      ((le_max_left (Bfun kappaTilde) (1 + C)).trans
        ((le_max_right
          (paperDMin p.χ Q κ kappaTilde p.m p.γ c) _).trans
          (le_max_right 1 _)))
      hDbase
  have honeCD : 1 + C < D :=
    lt_of_le_of_lt
      ((le_max_right (Bfun kappaTilde) (1 + C)).trans
        ((le_max_right
          (paperDMin p.χ Q κ kappaTilde p.m p.γ c) _).trans
          (le_max_right 1 _)))
      hDbase
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one hDone
  let X : ℝ := lowerBarrierXPlus κ kappaTilde D
  have hspliceDelta : Real.exp (-κ * X) ≤ delta := by
    exact hspliceSmall.trans (min_le_left _ _)
  have hspliceMiddle : Real.exp (-κ * X) ≤ middleFloor := by
    exact hspliceSmall.trans
      ((min_le_right delta _).trans (min_le_left _ _))
  have hspliceR : Real.exp (-κ * X) ≤ Real.exp (-κ * R) := by
    exact hspliceSmall.trans
      ((min_le_right delta _).trans
        ((min_le_right middleFloor _).trans (min_le_left _ _)))
  have hspliceChi : Real.exp (-κ * X) ≤ 1 / (1 + |p.χ|) := by
    exact hspliceSmall.trans
      ((min_le_right delta _).trans
        ((min_le_right middleFloor _).trans (min_le_right _ _)))
  have hRX : R ≤ X := by
    have hlog := Real.exp_le_exp.mp hspliceR
    dsimp [X] at hlog ⊢
    nlinarith
  have hplateauSplice : ∀ x,
      lowerBarrierPlateau κ kappaTilde D x ≤ Real.exp (-κ * X) := by
    intro x
    dsimp [X]
    exact lowerBarrierPlateau_le_exp_xplus hκ.le hD.le x
  have hplateauHalf :
      lowerBarrierRaw κ kappaTilde D X ≤
        (1 / 2 : ℝ) * Real.exp (-κ * X) := by
    dsimp [X]
    exact lowerBarrierRaw_xplus_le_half_exp_of_lt_two
      hκ (sub_pos.mpr hkappaTilde) hkappaTildeTwo hD
  have hthreshold : ∀ x,
      lowerBarrierPlateau κ kappaTilde D x ≤
        constantSubsolutionThreshold p.χ κ kappaTilde D := by
    intro x
    unfold constantSubsolutionThreshold
    apply le_min
    · exact (hplateauSplice x).trans hspliceChi
    · rw [← lowerBarrierRaw_xplus_eq_constantSubsolutionTail
        hκ (sub_pos.mpr hkappaTilde) hD]
      exact lowerBarrierPlateau_le_value_at_xplus
        hκ (sub_pos.mpr hkappaTilde) hD
  refine ⟨kappaTilde, D, hkappaTilde, hkappaTildeκ₁,
    hkappaTildeEta, hkappaTildeCap, hkappaTildeTwo, hcond,
    hDone, hDmin, hBfun, hthreshold, ?_⟩
  intro x
  by_cases hxL : x ≤ L
  · exact (hplateauSplice x).trans (hspliceDelta.trans (hL x hxL))
  · have hLx : L ≤ x := le_of_not_ge hxL
    by_cases hxR : x ≤ R
    · exact (hplateauSplice x).trans
        (hspliceMiddle.trans (hmiddle x ⟨hLx, hxR⟩))
    · have hRx : R ≤ x := le_of_not_ge hxR
      have hright := hR₀ x (hR₀R.trans hRx)
      by_cases hxX : x ≤ X
      · have hplateauEq :
            lowerBarrierPlateau κ kappaTilde D x =
              lowerBarrierRaw κ kappaTilde D X := by
          dsimp [X] at hxX ⊢
          exact lowerBarrierPlateau_eq_const_of_le hxX
        have hexpMono : Real.exp (-κ * X) ≤ Real.exp (-κ * x) := by
          exact Real.exp_le_exp.mpr (by nlinarith)
        rw [hplateauEq]
        exact hplateauHalf.trans
          ((mul_le_mul_of_nonneg_left hexpMono (by norm_num)).trans hright.1)
      · have hXx : X < x := lt_of_not_ge hxX
        have hxzero : 0 ≤ x := hRzero.trans hRx
        have hexpκ₁ : Real.exp (-κ₁ * x) ≤
            Real.exp (-kappaTilde * x) := by
          apply Real.exp_le_exp.mpr
          nlinarith only [hkappaTildeκ₁, hxzero]
        have hexpEta : Real.exp (-eta * x) ≤
            Real.exp (-kappaTilde * x) := by
          apply Real.exp_le_exp.mpr
          nlinarith only [hkappaTildeEta, hxzero]
        have herrors : Real.exp (-κ₁ * x) +
              C * Real.exp (-eta * x) ≤
            D * Real.exp (-kappaTilde * x) := by
          have hCexp := mul_le_mul_of_nonneg_left hexpEta hC
          have hcoef := mul_le_mul_of_nonneg_right
            (le_of_lt honeCD) (Real.exp_nonneg (-kappaTilde * x))
          nlinarith
        have hUlower : Real.exp (-κ * x) - Real.exp (-κ₁ * x) ≤ U x := by
          have htailx :
              |U x - Real.exp (-κ * x)| ≤
                Real.exp (-κ₁ * x) := by
            simpa [hkappa_eq] using hright.2
          linarith only [neg_le_of_abs_le htailx]
        have hwlower : U x - C * Real.exp (-eta * x) ≤ w x := by
          linarith [neg_le_of_abs_le (henv x)]
        rw [lowerBarrierPlateau_eq_raw_of_xplus_lt hXx]
        unfold lowerBarrierRaw
        linarith

section AxiomAudit

#print axioms
  exists_chiNonpos_compatible_lowerBarrierPlateau_seed_of_profile_bounds

end AxiomAudit

end ShenWork.Paper1
