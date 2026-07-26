import ShenWork.Paper1.WholeLineChiPosEntropyClassicalCompactness
import ShenWork.Paper1.WholeLineChiPosWeightedEntropyOrbitDeriv

/-!
# Basin-conditional far-left convergence on the full sharp range `chi < 4`

The weighted entropy engine cannot see which of the two stable states
(`u = 1` or `u = 0`) the far-left populations select: the scalar bistability
makes any translation-invariant functional inequality basin-blind, so a
*global* uniform far-left convergence statement is false and the correct
scope of the sharp-range theorem is conditional on a basin (floor)
hypothesis.  This file states that scope honestly and discharges from it
everything the landed engine can discharge.

Two independent hypotheses are isolated.

* `EventualCoMovingLeftBand c ell M orbit` — the **basin floor**: eventually
  in time and far enough to the left in the co-moving frame, the population
  lies in a fixed band `[ell, M]` with `ell > 0`.  This is the honest
  physical hypothesis (`u >= 1 - rho > 0` on far-left windows); it selects
  the `u = 1` basin and is exactly what the bistability obstruction shows
  cannot come for free.
* `ChiOneFarLeftDerivativeCompactness` — the **residual parabolic input**:
  local equiboundedness/equicontinuity and uniform local bounds of the six
  translated derivative/resolver fields.  The zeroth-order fields
  (`floor`, `|u| <= C`, and the full precompactness package for `u` itself)
  are *derived* here from the basin floor plus the first-order bounds, so
  they no longer appear as hypotheses.

Together with the landed entropy Liouville route this yields far-left
convergence to the equilibrium for every `0 <= chi < 4`.

The final section assembles the same engine on the *actual* canonical orbit:
combining the literal `dE/dt` representation with the weighted sharp
dissipation and a window basin floor gives the explicit conditional
Gronwall inequality `E' <= -(1 - chi^2/16) * (1 - rho) * E + errors` on any
far-left window of the real Cauchy evolution.
-/

open Filter MeasureTheory Real Set Topology
open scoped Interval

noncomputable section

namespace ShenWork.Paper1

/-! ## Zeroth-order compactness from the basin band -/

/-- An eventual two-sided band on translated boxes gives local
equiboundedness. -/
theorem spaceTimeLocallyEquibounded_of_eventual_band
    {u : ℕ → ℝ → ℝ → ℝ} {ell M : ℝ}
    (hband : ∀ R > 0, ∀ᶠ n in atTop,
      ∀ t ∈ Set.Icc (-R) R, ∀ x ∈ Set.Icc (-R) R,
        ell ≤ u n t x ∧ u n t x ≤ M) :
    SpaceTimeLocallyEquibounded u := by
  intro R hR
  refine ⟨max M (-ell), ?_⟩
  filter_upwards [hband R hR] with n hn t ht x hx
  have h := hn t ht x hx
  rw [abs_le]
  constructor
  · have hlow : -(max M (-ell)) ≤ ell := by
      have := le_max_right M (-ell)
      linarith
    linarith [h.1]
  · exact h.2.trans (le_max_left _ _)

/-- Eventual local bounds on the space and time derivatives make the
translated populations locally uniformly Lipschitz, hence equicontinuous. -/
theorem spaceTimeLocallyEquicontinuous_of_deriv_bounds
    {u ux ut : ℕ → ℝ → ℝ → ℝ} {C : ℝ}
    (hspace : ∀ n t x, HasDerivAt (u n t) (ux n t x) x)
    (htime : ∀ n t x, HasDerivAt (fun s => u n s x) (ut n t x) t)
    (hC0 : 0 ≤ C)
    (hC : ∀ R > 0, ∀ᶠ n in atTop,
      ∀ t ∈ Set.Icc (-R) R, ∀ x ∈ Set.Icc (-R) R,
        |ux n t x| ≤ C ∧ |ut n t x| ≤ C) :
    SpaceTimeLocallyEquicontinuous u := by
  intro R hR ε hε
  have hC1 : (0 : ℝ) < C + 1 := by linarith
  refine ⟨ε / (2 * (C + 1)), div_pos hε (by linarith), ?_⟩
  filter_upwards [hC R hR] with n hn
  intro t ht s hs x hx y hy hts hxy
  have htimeLeg : |u n t x - u n s x| ≤ C * |t - s| := by
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun τ => u n τ x) (f' := fun τ => ut n τ x)
      (s := Set.Icc (-R) R) (C := C)
      (fun τ hτ => (htime n τ x).hasDerivWithinAt)
      (fun τ hτ => by
        rw [Real.norm_eq_abs]
        exact (hn τ hτ x hx).2)
      (convex_Icc _ _) hs ht
    simpa [Real.norm_eq_abs] using hmvt
  have hspaceLeg : |u n s x - u n s y| ≤ C * |x - y| := by
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := u n s) (f' := ux n s)
      (s := Set.Icc (-R) R) (C := C)
      (fun z hz => (hspace n s z).hasDerivWithinAt)
      (fun z hz => by
        rw [Real.norm_eq_abs]
        exact (hn s hs z hz).1)
      (convex_Icc _ _) hy hx
    simpa [Real.norm_eq_abs] using hmvt
  have htri : |u n t x - u n s y| ≤
      |u n t x - u n s x| + |u n s x - u n s y| := by
    calc
      |u n t x - u n s y| =
          |(u n t x - u n s x) + (u n s x - u n s y)| := by
        congr 1
        ring
      _ ≤ |u n t x - u n s x| + |u n s x - u n s y| := abs_add_le _ _
  have hsum : |u n t x - u n s y| ≤
      C * |t - s| + C * |x - y| := by
    linarith [htri, htimeLeg, hspaceLeg]
  have hδts : C * |t - s| ≤ C * (ε / (2 * (C + 1))) :=
    mul_le_mul_of_nonneg_left hts.le hC0
  have hδxy : C * |x - y| ≤ C * (ε / (2 * (C + 1))) :=
    mul_le_mul_of_nonneg_left hxy.le hC0
  have hkey : 2 * (C * (ε / (2 * (C + 1)))) < ε := by
    have hne : C + 1 ≠ 0 := ne_of_gt hC1
    have hEq : 2 * (C * (ε / (2 * (C + 1)))) = C * ε / (C + 1) := by
      field_simp
    rw [hEq, div_lt_iff₀ hC1]
    nlinarith
  calc
    |u n t x - u n s y| ≤ C * |t - s| + C * |x - y| := hsum
    _ ≤ 2 * (C * (ε / (2 * (C + 1)))) := by linarith [hδts, hδxy]
    _ < ε := hkey

/-! ## The residual first-order hypothesis -/

/-- The floor-free residual estimates on one translated sequence: existence
of the six derivative/resolver fields with their differential identities,
their local precompactness packages, and one uniform local bound.  No
zeroth-order floor or bound on `u` appears; those come from the basin band.
-/
structure ChiOneTranslatedDerivativeEstimates
    (chi c : ℝ) (u ux uxx ut r rx rxx : ℕ → ℝ → ℝ → ℝ) : Prop where
  ux_precompact : SpaceTimeLocallyPrecompact ux
  uxx_precompact : SpaceTimeLocallyPrecompact uxx
  ut_precompact : SpaceTimeLocallyPrecompact ut
  r_precompact : SpaceTimeLocallyPrecompact r
  rx_precompact : SpaceTimeLocallyPrecompact rx
  rxx_precompact : SpaceTimeLocallyPrecompact rxx
  u_space_deriv : ∀ n t x, HasDerivAt (u n t) (ux n t x) x
  ux_space_deriv : ∀ n t x, HasDerivAt (ux n t) (uxx n t x) x
  r_space_deriv : ∀ n t x, HasDerivAt (r n t) (rx n t x) x
  rx_space_deriv : ∀ n t x, HasDerivAt (rx n t) (rxx n t x) x
  u_time_deriv : ∀ n t x, HasDerivAt (fun s => u n s x) (ut n t x) t
  uxx_continuous : ∀ n t, Continuous (uxx n t)
  ut_continuous : ∀ n t, Continuous (ut n t)
  rxx_continuous : ∀ n t, Continuous (rxx n t)
  population_pde : ∀ n t x,
    ut n t x = uxx n t x + c * ux n t x -
      chi * (ux n t x * rx n t x + u n t x * rxx n t x) +
        u n t x * (1 - u n t x)
  resolver : ∀ n t x, -rxx n t x + r n t x = u n t x - 1
  derivative_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ R > 0, ∀ᶠ n in atTop,
    ∀ t ∈ Set.Icc (-R) R, ∀ x ∈ Set.Icc (-R) R,
      |ux n t x| ≤ C ∧ |uxx n t x| ≤ C ∧ |ut n t x| ≤ C ∧
      |r n t x| ≤ C ∧ |rx n t x| ≤ C ∧ |rxx n t x| ≤ C

/-- The basin band discharges every zeroth-order obligation of the classical
sequence data: the floor, the bound and the full precompactness package of
the translated populations. -/
theorem ChiOneTranslatedDerivativeEstimates.toClassicalSequenceData
    {chi c ell M k : ℝ} {u ux uxx ut r rx rxx : ℕ → ℝ → ℝ → ℝ}
    (H : ChiOneTranslatedDerivativeEstimates chi c u ux uxx ut r rx rxx)
    (hkpos : 0 < k) (hk1 : k < 1) (hchi : 0 ≤ chi) (hell : 0 < ell)
    (hband : ∀ R > 0, ∀ᶠ n in atTop,
      ∀ t ∈ Set.Icc (-R) R, ∀ x ∈ Set.Icc (-R) R,
        ell ≤ u n t x ∧ u n t x ≤ M) :
    ChiOneClassicalSequenceData chi c ell k u ux uxx ut r rx rxx := by
  obtain ⟨C, hC0, hC⟩ := H.derivative_bound
  have hu_equicont : SpaceTimeLocallyEquicontinuous u := by
    refine spaceTimeLocallyEquicontinuous_of_deriv_bounds
      H.u_space_deriv H.u_time_deriv hC0 ?_
    intro R hR
    filter_upwards [hC R hR] with n hn t ht x hx
    exact ⟨(hn t ht x hx).1, (hn t ht x hx).2.2.1⟩
  refine
    { hkpos := hkpos
      hk1 := hk1
      hchi := hchi
      hell := hell
      u_precompact :=
        ⟨spaceTimeLocallyEquibounded_of_eventual_band hband, hu_equicont⟩
      ux_precompact := H.ux_precompact
      uxx_precompact := H.uxx_precompact
      ut_precompact := H.ut_precompact
      r_precompact := H.r_precompact
      rx_precompact := H.rx_precompact
      rxx_precompact := H.rxx_precompact
      u_space_deriv := H.u_space_deriv
      ux_space_deriv := H.ux_space_deriv
      r_space_deriv := H.r_space_deriv
      rx_space_deriv := H.rx_space_deriv
      u_time_deriv := H.u_time_deriv
      uxx_continuous := H.uxx_continuous
      ut_continuous := H.ut_continuous
      rxx_continuous := H.rxx_continuous
      population_pde := H.population_pde
      resolver := H.resolver
      floor := ?_
      uniform_bound := ?_ }
  · intro R hR
    filter_upwards [hband R hR] with n hn t ht x hx
    exact (hn t ht x hx).1
  · refine ⟨max C (max M (-ell)), le_trans hC0 (le_max_left _ _), ?_⟩
    intro R hR
    filter_upwards [hband R hR, hC R hR] with n hb hd t ht x hx
    have hbn := hb t ht x hx
    have hdn := hd t ht x hx
    have hCmax : C ≤ max C (max M (-ell)) := le_max_left _ _
    have huabs : |u n t x| ≤ max C (max M (-ell)) := by
      rw [abs_le]
      constructor
      · have hlow : -(max C (max M (-ell))) ≤ ell := by
          have h1 : -ell ≤ max M (-ell) := le_max_right _ _
          have h2 : max M (-ell) ≤ max C (max M (-ell)) := le_max_right _ _
          linarith
        linarith [hbn.1]
      · exact hbn.2.trans
          ((le_max_left M (-ell)).trans (le_max_right _ _))
    exact ⟨huabs, hdn.1.trans hCmax, hdn.2.1.trans hCmax,
      hdn.2.2.1.trans hCmax, hdn.2.2.2.1.trans hCmax,
      hdn.2.2.2.2.1.trans hCmax, hdn.2.2.2.2.2.trans hCmax⟩

/-- The residual parabolic obligation for an orbit, stated with no floor and
no zeroth-order field: every late-time far-left translation sequence carries
the six derivative fields with the residual estimates. -/
structure ChiOneFarLeftDerivativeCompactness
    (chi c : ℝ) (orbit : ℝ → ℝ → ℝ) : Prop where
  translatedDerivatives :
    ∀ (timeShift spaceShift : ℕ → ℝ),
      (∀ n : ℕ, (n : ℝ) ≤ timeShift n) →
      (∀ n : ℕ, spaceShift n ≤ -(n : ℝ)) →
      ∃ ux uxx ut r rx rxx : ℕ → ℝ → ℝ → ℝ,
        ChiOneTranslatedDerivativeEstimates chi c
          (fun n => chiOneFarLeftTranslate c orbit timeShift spaceShift n)
          ux uxx ut r rx rxx

/-! ## The basin-conditional sharp-range theorem -/

/-- **Basin-conditional far-left convergence, full sharp range.**  If the
orbit eventually lies in a positive band `[ell, M]` on a far-left co-moving
half-line (the basin floor hypothesis) and the translated derivative fields
satisfy the residual parabolic estimates, then for every `0 <= chi < 4` the
population converges uniformly to the equilibrium in the far-left co-moving
regime.  The floor is an honest hypothesis: by the bistability of the scalar
reaction, no translation-invariant functional argument can supply it. -/
theorem uniformCoMovingLeftEquilibriumConvergence_chiPos_upto_four_basinConditional
    {chi c ell M : ℝ} {orbit : ℝ → ℝ → ℝ}
    (hchi : 0 ≤ chi) (hchi4 : chi < 4) (hell : 0 < ell)
    (Hbasin : EventualCoMovingLeftBand c ell M orbit)
    (Hderiv : ChiOneFarLeftDerivativeCompactness chi c orbit) :
    UniformCoMovingLeftEquilibriumConvergence c orbit := by
  apply
    uniformCoMovingLeftEquilibriumConvergence_chiPos_upto_four_of_parabolicCompactness
      hchi hchi4 hell
  intro k hkpos hk1
  constructor
  intro timeShift spaceShift htime hspace
  obtain ⟨ux, uxx, ut, r, rx, rxx, H⟩ :=
    Hderiv.translatedDerivatives timeShift spaceShift htime hspace
  exact ⟨ux, uxx, ut, r, rx, rxx,
    H.toClassicalSequenceData hkpos hk1 hchi hell
      (Hbasin.eventually_translated_box_bounds htime hspace)⟩

/-- Canonical-orbit form of the basin-conditional sharp-range theorem. -/
theorem wholeLineCauchyGlobalU_farLeftConvergence_upto_four_basinConditional
    {p : CMParams} {c ell M : ℝ} {u₀ : WholeLineBUC}
    (hchi : 0 ≤ p.χ) (hchi4 : p.χ < 4) (hell : 0 < ell)
    (Hbasin : EventualCoMovingLeftBand c ell M
      (wholeLineCauchyGlobalU p u₀))
    (Hderiv : ChiOneFarLeftDerivativeCompactness p.χ c
      (wholeLineCauchyGlobalU p u₀)) :
    UniformCoMovingLeftEquilibriumConvergence c
      (wholeLineCauchyGlobalU p u₀) :=
  uniformCoMovingLeftEquilibriumConvergence_chiPos_upto_four_basinConditional
    hchi hchi4 hell Hbasin Hderiv

/-- The basin floor for the canonical orbit can itself be discharged from a
persistent plateau: with the plateau lower barrier and the stable ceiling,
only the residual derivative estimates remain. -/
theorem wholeLineCauchyGlobalU_farLeftConvergence_upto_four_of_persistent_plateau
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    {N : ℕ} {c kappa kappaTilde D : ℝ}
    (hkappa : 0 < kappa) (hgap : kappa < kappaTilde) (hD : 1 ≤ D)
    (hpersist : ∀ n : ℕ, N ≤ n →
      ∀ r ∈ Set.Icc (0 : ℝ) (wholeLineCauchyGlobalStep p u₀), ∀ x,
        lowerBarrierPlateau kappa kappaTilde D x ≤
          wholeLineCauchyGlobalU p u₀
            (((n : ℝ) + 1) * wholeLineCauchyGlobalStep p u₀ + r)
            (x + c * (((n : ℝ) + 1) *
              wholeLineCauchyGlobalStep p u₀ + r)))
    (hchi : 0 ≤ p.χ) (hchi4 : p.χ < 4)
    (Hderiv : ChiOneFarLeftDerivativeCompactness p.χ c
      (wholeLineCauchyGlobalU p u₀)) :
    UniformCoMovingLeftEquilibriumConvergence c
      (wholeLineCauchyGlobalU p u₀) := by
  obtain ⟨ell, M, hell, Hbasin⟩ :=
    exists_eventualCoMovingLeftBand_of_persistent_plateau
      p hregime u₀ hu₀ hkappa hgap hD hpersist
  exact wholeLineCauchyGlobalU_farLeftConvergence_upto_four_basinConditional
    hchi hchi4 hell Hbasin Hderiv

/-! ## The literal conditional Gronwall inequality on the real orbit -/

/-- **Window entropy Gronwall form for the actual Cauchy orbit.**  On a
window `[a, b]` where the population sits in the basin (`u >= 1 - rho`), the
weighted entropy production is at most
`-(1 - chi^2/16) * (1 - rho)` times the weighted entropy itself, plus the
explicit weight, resolver, and boundary error terms of the sharp weighted
dissipation.  Paired with
`wholeLineCauchyGlobalU_weighted_entropy_hasDerivAt`, this is the literal
differential inequality `E' <= -mu * E + Err` on far-left windows,
conditional only on the basin floor. -/
theorem wholeLineCauchyGlobalU_basinWindow_entropy_production_le
    (p : CMParams) (u₀ : WholeLineBUC)
    (hregime : WholeLineCauchyCeilingRegime p)
    (hu₀ : ∀ x, 0 ≤ u₀.1 x) (hleft : StrictlyPositiveAtLeft u₀.1)
    (hp : p.m = 1 ∧ p.γ = 1 ∧ p.α = 1)
    (hchi : 0 ≤ p.χ) (hchi4 : p.χ < 4)
    (a b c ell rho : ℝ) (w w' : ℝ → ℝ) (t : ℝ) (ht : 0 < t)
    (hw_pos : ∀ x, 0 < w x)
    (hw_deriv : ∀ x, HasDerivAt w (w' x) x)
    (hw'_cont : Continuous w')
    (hw_slow : ∀ x, |w' x| ≤ (1 / ell) * w x)
    (hab : a ≤ b) (hell : 0 < ell)
    (hrho : rho < 1)
    (hfloor : ∀ x ∈ Set.Icc a b,
      1 - rho ≤ wholeLineCauchyGlobalCoMovingU p u₀ c t x) :
    (∫ x in a..b,
        w x *
          chiOneEntropyMultiplier
            (wholeLineCauchyGlobalCoMovingU p u₀ c t x) *
          wholeLineCauchyGlobalCoMovingUt p u₀ c t x) ≤
      -((1 - p.χ ^ 2 / 16) * (1 - rho)) *
          (∫ x in a..b,
            w x *
              chiOneRelativeEntropy
                (wholeLineCauchyGlobalCoMovingU p u₀ c t x)) +
        ((|c| + p.χ + 2) / ell) *
          ((∫ x in a..b,
              w x *
                chiOneRelativeEntropy
                  (wholeLineCauchyGlobalCoMovingU p u₀ c t x)) +
            (∫ x in a..b,
              w x *
                ((wholeLineCauchyGlobalCoMovingUx p u₀ c t x /
                      wholeLineCauchyGlobalCoMovingU p u₀ c t x) ^ 2 +
                  (wholeLineCauchyGlobalCoMovingU p u₀ c t x - 1) ^ 2))) +
        (p.χ ^ 2 / 4 + p.χ / (2 * ell)) *
          ((1 / (2 * ell)) *
              ((∫ x in a..b,
                  w x * (wholeLineCauchyGlobalCoMovingR p u₀ c t x) ^ 2) +
                ∫ x in a..b,
                  w x *
                    (wholeLineCauchyGlobalCoMovingRx p u₀ c t x) ^ 2) +
            |w b * wholeLineCauchyGlobalCoMovingR p u₀ c t b *
                  wholeLineCauchyGlobalCoMovingRx p u₀ c t b -
              w a * wholeLineCauchyGlobalCoMovingR p u₀ c t a *
                  wholeLineCauchyGlobalCoMovingRx p u₀ c t a|) +
        ((w b *
              chiOneEntropyMultiplier
                (wholeLineCauchyGlobalCoMovingU p u₀ c t b) *
              wholeLineCauchyGlobalCoMovingUx p u₀ c t b -
            w a *
              chiOneEntropyMultiplier
                (wholeLineCauchyGlobalCoMovingU p u₀ c t a) *
              wholeLineCauchyGlobalCoMovingUx p u₀ c t a) +
          c *
            (w b *
                chiOneRelativeEntropy
                  (wholeLineCauchyGlobalCoMovingU p u₀ c t b) -
              w a *
                chiOneRelativeEntropy
                  (wholeLineCauchyGlobalCoMovingU p u₀ c t a)) -
          p.χ *
            (w b *
                (wholeLineCauchyGlobalCoMovingU p u₀ c t b - 1) *
                wholeLineCauchyGlobalCoMovingRx p u₀ c t b -
              w a *
                (wholeLineCauchyGlobalCoMovingU p u₀ c t a - 1) *
                wholeLineCauchyGlobalCoMovingRx p u₀ c t a)) := by
  have hdiss := wholeLineCauchyGlobalU_weighted_sharp_dissipation
    p u₀ hregime hu₀ hleft hp hchi a b c ell w w' t ht
      hw_pos hw_deriv hw'_cont hw_slow hab hell
  have hrhoPos : 0 < 1 - rho := by linarith
  have hmargin : 0 ≤ 1 - p.χ ^ 2 / 16 := by nlinarith
  -- continuity of the slice and of the two comparison integrands
  have hucont : Continuous (wholeLineCauchyGlobalCoMovingU p u₀ c t) :=
    (wholeLineCauchyGlobalU_coMoving_contDiff_two_positive
      p hregime u₀ hu₀ (c := c) ht).continuous
  have hupos : ∀ x, 0 < wholeLineCauchyGlobalCoMovingU p u₀ c t x := by
    intro x
    simpa [wholeLineCauchyGlobalCoMovingU, coMovingPath] using
      wholeLineCauchyGlobal_pos_of_posAtBot
        p hregime u₀ hu₀ hleft ht (x + c * t)
  have hwcont : Continuous w := by
    rw [continuous_iff_continuousAt]
    exact fun x => (hw_deriv x).continuousAt
  have hentcont : Continuous (fun x =>
      chiOneRelativeEntropy (wholeLineCauchyGlobalCoMovingU p u₀ c t x)) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (chiOneRelativeEntropy_hasDerivAt
      (hupos x).ne').continuousAt.comp hucont.continuousAt
  have hg1cont : Continuous (fun x =>
      (1 - rho) *
        (w x *
          chiOneRelativeEntropy
            (wholeLineCauchyGlobalCoMovingU p u₀ c t x))) :=
    continuous_const.mul (hwcont.mul hentcont)
  have hg2cont : Continuous (fun x =>
      w x * (wholeLineCauchyGlobalCoMovingU p u₀ c t x - 1) ^ 2) :=
    hwcont.mul ((hucont.sub continuous_const).pow 2)
  -- pointwise comparison on the window from the basin floor
  have hcompare :
      (1 - rho) *
          (∫ x in a..b,
            w x *
              chiOneRelativeEntropy
                (wholeLineCauchyGlobalCoMovingU p u₀ c t x)) ≤
        ∫ x in a..b,
          w x * (wholeLineCauchyGlobalCoMovingU p u₀ c t x - 1) ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hab
      (hg1cont.intervalIntegrable a b)
      (hg2cont.intervalIntegrable a b)
    intro x hx
    have hent := chiOneRelativeEntropy_le_sq_div hrhoPos (hfloor x hx)
    have hwx := (hw_pos x).le
    have hscaled := mul_le_mul_of_nonneg_left hent
      (mul_nonneg hrhoPos.le hwx)
    calc
      (1 - rho) *
          (w x *
            chiOneRelativeEntropy
              (wholeLineCauchyGlobalCoMovingU p u₀ c t x)) =
          (1 - rho) * w x *
            chiOneRelativeEntropy
              (wholeLineCauchyGlobalCoMovingU p u₀ c t x) := by ring
      _ ≤ (1 - rho) * w x *
            ((wholeLineCauchyGlobalCoMovingU p u₀ c t x - 1) ^ 2 /
              (1 - rho)) := hscaled
      _ = w x * (wholeLineCauchyGlobalCoMovingU p u₀ c t x - 1) ^ 2 := by
        field_simp
  -- fold the comparison into the sharp dissipation bound
  have hmain :
      -(1 - p.χ ^ 2 / 16) *
          (∫ x in a..b,
            w x * (wholeLineCauchyGlobalCoMovingU p u₀ c t x - 1) ^ 2) ≤
        -((1 - p.χ ^ 2 / 16) * (1 - rho)) *
          (∫ x in a..b,
            w x *
              chiOneRelativeEntropy
                (wholeLineCauchyGlobalCoMovingU p u₀ c t x)) := by
    nlinarith [mul_le_mul_of_nonneg_left hcompare hmargin]
  linarith [hdiss, hmain]

section AxiomAudit

#print axioms spaceTimeLocallyEquibounded_of_eventual_band
#print axioms spaceTimeLocallyEquicontinuous_of_deriv_bounds
#print axioms ChiOneTranslatedDerivativeEstimates.toClassicalSequenceData
#print axioms
  uniformCoMovingLeftEquilibriumConvergence_chiPos_upto_four_basinConditional
#print axioms
  wholeLineCauchyGlobalU_farLeftConvergence_upto_four_basinConditional
#print axioms
  wholeLineCauchyGlobalU_farLeftConvergence_upto_four_of_persistent_plateau
#print axioms wholeLineCauchyGlobalU_basinWindow_entropy_production_le

end AxiomAudit

end ShenWork.Paper1
