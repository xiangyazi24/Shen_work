import ShenWork.Paper1.WholeLineWeightedRegularityC1SpliceApproxComparisonNatural
import ShenWork.Paper1.WholeLineWeightedRegularityPlateauApproxContactOperatorNatural
import ShenWork.Paper1.WholeLineWeightedRegularityPlateauComparisonNatural
import ShenWork.Paper1.WholeLineWeightedRegularityScaledPlateauOperatorNatural

open Filter Topology Set Real

noncomputable section

namespace ShenWork.Paper1

/-!
# One-window scaled lower-plateau comparison

The late canonical restart only supplies a scaled wave trap.  This file
combines the scaled Lemma-4.2 subsolution with the approximate-contact
parabolic comparison on one closed restart window.  Time is clamped only at
zero to provide the globally continuous extension required by the slab
maximum principle.  It is locally the identity at every positive time,
including the right endpoint of the comparison window.
-/

/-- On a positive canonical restart window, a lower plateau initially below
the population remains below it throughout the closed window.  The current
population is controlled by a scaled time-wave trap; no normalized trap and
no monotonicity of a population slice are assumed. -/
theorem
    wholeLineCauchyGlobal_coMovingRestart_ge_lowerBarrierPlateau_chiNonpos_scaled
    (p : CMParams) (hchi : p.χ ≤ 0)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    {c t₀ T kappa kappaTilde D Q : ℝ}
    (ht₀ : 0 < t₀) (hT : 0 < T)
    (hcond : PaperLemma42ExactConditions
      p c kappa kappaTilde 1)
    (hQ : 1 ≤ Q)
    (hD : paperScaledDMin p Q kappa kappaTilde c < D)
    (hD1 : 1 ≤ D)
    (hplateau : ∀ x, lowerBarrierPlateau kappa kappaTilde D x ≤
      constantSubsolutionThreshold p.χ kappa kappaTilde D)
    (htrap : InTimeWaveTrapSet kappa Q T (fun t x =>
      wholeLineCauchyGlobalU p u₀ (t₀ + t)
        (x + c * (t₀ + t))))
    (hinit : ∀ x, lowerBarrierPlateau kappa kappaTilde D x ≤
      wholeLineCauchyGlobalU p u₀ t₀ (x + c * t₀)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
      lowerBarrierPlateau kappa kappaTilde D x ≤
        wholeLineCauchyGlobalU p u₀ (t₀ + t)
          (x + c * (t₀ + t)) := by
  let A : ℝ → ℝ := lowerBarrierPlateau kappa kappaTilde D
  let w : ℝ → ℝ → ℝ := fun t x =>
    wholeLineCauchyGlobalU p u₀ (t₀ + t)
      (x + c * (t₀ + t))
  let tau : ℝ → ℝ := fun t => max t 0
  let we : ℝ → ℝ → ℝ := fun t x => w (tau t) x
  let C0 : ℝ :=
    reactionLip p.α Q + |p.χ| * (Q ^ p.γ) * rpowLip p.m Q +
      |p.χ| * rpowLip (p.m + p.γ) Q
  let C : ℝ := C0 +
    |p.χ| * p.m * (Q ^ p.γ) * kappaTilde * p.m *
      Q ^ (p.m - 1)
  let E : ℝ := 1 + |c| +
    |p.χ| * p.m * (Q ^ p.γ) * Q ^ (p.m - 1)
  let X : ℝ := lowerBarrierXPlus kappa kappaTilde D
  have hregime : WholeLineCauchyCeilingRegime p :=
    WholeLineCauchyCeilingRegime.of_nonpositive hchi
  have hQ0 : 0 ≤ Q := le_trans zero_le_one hQ
  have hQpos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD1
  have hgap : 0 < kappaTilde - kappa := sub_pos.mpr hcond.hgap
  have hkappaTilde0 : 0 ≤ kappaTilde := by
    linarith [hcond.hκ0, hcond.hgap]
  have hmg : 1 ≤ p.m + p.γ := by
    linarith [p.hm, p.hγ]
  have hC0_nonneg : 0 ≤ C0 := by
    dsimp only [C0]
    have hreact : 0 ≤ reactionLip p.α Q :=
      reactionLip_nonneg p.hα hQ0
    have hLm : 0 ≤ rpowLip p.m Q := rpowLip_nonneg p.hm hQ0
    have hLmg : 0 ≤ rpowLip (p.m + p.γ) Q :=
      rpowLip_nonneg hmg hQ0
    positivity
  have hcross_nonneg :
      0 ≤ |p.χ| * p.m * (Q ^ p.γ) * kappaTilde * p.m *
        Q ^ (p.m - 1) := by
    have hm0 : 0 ≤ p.m := le_trans zero_le_one p.hm
    positivity
  have hC_nonneg : 0 ≤ C := by
    dsimp only [C]
    exact add_nonneg hC0_nonneg hcross_nonneg
  have hE_nonneg : 0 ≤ E := by
    dsimp only [E]
    have hm0 : 0 ≤ p.m := le_trans zero_le_one p.hm
    positivity
  have hthreshold_one :
      constantSubsolutionThreshold p.χ kappa kappaTilde D ≤ 1 := by
    calc
      constantSubsolutionThreshold p.χ kappa kappaTilde D ≤
          1 / (1 + |p.χ|) := min_le_left _ _
      _ ≤ 1 := by
        simpa using one_div_le_one_div_of_le
          (show (0 : ℝ) < 1 by norm_num)
          (show (1 : ℝ) ≤ 1 + |p.χ| by
            linarith [abs_nonneg p.χ])
  have hA_mem : ∀ x, A x ∈ Set.Icc (0 : ℝ) Q := by
    intro x
    constructor
    · exact (lowerBarrierPlateau_pos hcond.hκ0 hgap hDpos x).le
    · exact (hplateau x).trans (hthreshold_one.trans hQ)
  have htau_eq : ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) T → tau t = t := by
    intro t ht
    exact max_eq_left ht.1
  have hwe_eq : ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) T → we t = w t := by
    intro t ht
    funext x
    simp only [we, htau_eq ht]
  have hwe_cont : Continuous (fun q : ℝ × ℝ => we q.1 q.2) := by
    rw [continuous_iff_continuousAt]
    intro q
    have hphys : 0 < t₀ + tau q.1 := by
      have htau0 : 0 ≤ tau q.1 := by
        dsimp only [tau]
        exact le_max_right _ _
      linarith
    have hjoint := wholeLineCauchyGlobalU_joint_hasFDerivAt_positive
      p hregime u₀ hu₀ hphys
        (x := q.2 + c * (t₀ + tau q.1))
    have hmap : ContinuousAt
        (fun r : ℝ × ℝ =>
          (t₀ + tau r.1, r.2 + c * (t₀ + tau r.1))) q := by
      dsimp only [tau]
      fun_prop
    simpa [we, w, Function.comp_def] using
      hjoint.continuousAt.comp
        (f := fun r : ℝ × ℝ =>
          (t₀ + tau r.1, r.2 + c * (t₀ + tau r.1))) hmap
  have hdiff_cont : Continuous (fun q : ℝ × ℝ =>
      A q.2 - we q.1 q.2) := by
    exact ((lowerBarrierPlateau_continuous
      kappa kappaTilde D).comp continuous_snd).sub hwe_cont
  have htimeOp : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun s : ℝ => we s x)
        (paperWaveOperator p c (we t) (we t) x) t := by
    intro t x ht
    have hphys : 0 < t₀ + t := by linarith [ht₀, ht.1]
    have hraw :=
      wholeLineCauchyGlobal_coMovingRestart_hasDerivAt_paperWaveOperator
        p hregime u₀ hu₀ c t₀ hphys x
    have hev : (fun s : ℝ => we s x) =ᶠ[𝓝 t]
        fun s => w s x := by
      filter_upwards [Ioi_mem_nhds ht.1] with s hs
      change 0 < s at hs
      simp only [we, tau, max_eq_left hs.le]
    have hcongr := hraw.congr_of_eventuallyEq hev
    rw [hwe_eq ⟨ht.1.le, ht.2⟩]
    simpa only [w] using hcongr
  have hspace : ∀ ⦃t : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      ContDiff ℝ 2 (we t) := by
    intro t ht
    have hphys : 0 < t₀ + t := by linarith [ht₀, ht.1]
    rw [hwe_eq ⟨ht.1.le, ht.2⟩]
    exact wholeLineCauchyGlobal_coMovingRestart_contDiff_two
      p hregime u₀ hu₀ c t₀ hphys
  have hcomparison :=
    stationary_C1splice_le_of_approx_contact_parabolic_comparison
      (T := T) (B := Q) (C := C) (E := E) (X := X)
      (A := A) (u := we) hT hC_nonneg hE_nonneg
      (by
        intro x hx
        dsimp only [A, X]
        rw [lowerBarrierPlateau_eq_const_of_le hx,
          lowerBarrierPlateau_eq_const_of_le le_rfl])
      (by
        dsimp only [A, X]
        exact lowerBarrierPlateau_hasDerivAt_xplus
          hcond.hκ0 hgap hDpos)
      (by
        intro x hx
        exact lowerBarrierPlateau_contDiffAt_two_of_ne_xplus hx)
      hdiff_cont
      (by
        intro t ht x
        rw [hwe_eq ht, abs_le]
        have hwt0 : 0 ≤ w t x := htrap.nonneg ht x
        have hwtQ : w t x ≤ Q := htrap.le_M ht x
        have hAx := hA_mem x
        constructor
        · linarith [hAx.1, hwtQ]
        · linarith [hAx.2, hwt0])
      (by
        intro x
        rw [hwe_eq (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) T from
          ⟨le_rfl, hT.le⟩)]
        simpa only [A, w, zero_add, add_zero] using hinit x)
      hspace
      (by
        intro t x ht
        exact ((hasDerivAt_const t (A x)).sub
          (htimeOp ht)).differentiableAt.hasDerivAt)
      (by
        intro eta heta t x ht hx hcontact hslopeRaw hsecondRaw
        have htIcc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
        have hslice : we t = w t := hwe_eq htIcc
        have hqC : IsCUnifBdd (we t) := by
          rw [hslice]
          exact htrap.slice_cunif htIcc
        have hqQ : ∀ y, we t y ∈ Set.Icc (0 : ℝ) Q := by
          intro y
          rw [hslice]
          exact ⟨htrap.nonneg htIcc y, htrap.le_M htIcc y⟩
        have hcontact' : we t x ≤ A x := by linarith
        have hA2 : ContDiffAt ℝ 2 A x :=
          lowerBarrierPlateau_contDiffAt_two_of_ne_xplus hx
        have hwe2 : ContDiff ℝ 2 (we t) := hspace ht
        have hslope : |deriv A x - deriv (we t) x| ≤ eta := by
          have heq : deriv (fun y => A y - we t y) x =
              deriv A x - deriv (we t) x :=
            deriv_sub (hA2.differentiableAt (by norm_num))
              (hwe2.differentiable (by norm_num) x)
          rw [heq] at hslopeRaw
          exact hslopeRaw.le
        have hsecond : iteratedDeriv 2 A x -
            iteratedDeriv 2 (we t) x ≤ eta := by
          have heq : deriv (deriv (fun y => A y - we t y)) x =
              iteratedDeriv 2 A x - iteratedDeriv 2 (we t) x := by
            calc
              deriv (deriv (fun y => A y - we t y)) x =
                  iteratedDeriv 2 (fun y => A y - we t y) x := by
                simp [iteratedDeriv_succ, iteratedDeriv_zero]
              _ = iteratedDeriv 2 A x - iteratedDeriv 2 (we t) x :=
                iteratedDeriv_fun_sub hA2 hwe2.contDiffAt
          rw [heq] at hsecondRaw
          exact hsecondRaw.le
        have hop :=
          paperWaveOperator_lowerBarrierPlateau_diff_le_of_approx_contact_abs
            p (c := c) (Q := Q) (M := Q) (kappa := kappa)
            (kappaTilde := kappaTilde) (D := D) (eta := eta)
            (x := x) (q := we t) hQ0 hQpos hqC hqQ hcond.hκ0
            hgap hDpos hx (hA_mem x).2 hcontact' hsecond hslope
        have hsubActual :=
          paperWaveOperator_lowerBarrierPlateau_nonneg_chiNonpos_scaled_away
            p hcond hQ hD hD1 hplateau htrap htIcc hx
        have hsub : 0 ≤ paperWaveOperator p c (we t) A x := by
          simpa only [A, hslice] using hsubActual
        have hop' : paperWaveOperator p c (we t) A x -
              paperWaveOperator p c (we t) (we t) x ≤
            C * (A x - we t x) + E * eta := by
          simpa only [A, C, C0, E] using hop
        have htimeDeriv := (hasDerivAt_const t (A x)).sub
          (htimeOp (t := t) (x := x) ht)
        have htimeEq : deriv (fun s : ℝ => A x - we s x) t =
            -paperWaveOperator p c (we t) (we t) x := by
          simpa using htimeDeriv.deriv
        rw [htimeEq]
        linarith [hsub, hop'])
      (by
        intro eta heta t ht hcontact hqx hsecondRaw
        have htIcc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
        have hslice : we t = w t := hwe_eq htIcc
        have hqC : IsCUnifBdd (we t) := by
          rw [hslice]
          exact htrap.slice_cunif htIcc
        have hqQ : ∀ y, we t y ∈ Set.Icc (0 : ℝ) Q := by
          intro y
          rw [hslice]
          exact ⟨htrap.nonneg htIcc y, htrap.le_M htIcc y⟩
        have hcontact' : we t X ≤ A X := by linarith
        have hwe2 : ContDiff ℝ 2 (we t) := hspace ht
        have hsecond : -iteratedDeriv 2 (we t) X ≤ eta := by
          have heq : iteratedDeriv 2 (we t) X =
              deriv (deriv (we t)) X := by
            simp [iteratedDeriv_succ, iteratedDeriv_zero]
          rw [heq]
          exact hsecondRaw.le
        have hop0 := paperWaveOperator_const_diff_le_of_approx_contact_abs
          p (c := c) (Q := Q) (M := Q) (d := A X) (eta := eta)
          (x := X) (q := we t) hQ0 hQpos heta.le hqC hqQ
          (hA_mem X) hcontact' hqx hsecond
        have hop0' :
            paperWaveOperator p c (we t) (fun _ : ℝ => A X) X -
                paperWaveOperator p c (we t) (we t) X ≤
              C0 * (A X - we t X) + E * eta := by
          simpa only [C0, E] using hop0
        have hC0C : C0 ≤ C := by
          dsimp only [C]
          exact le_add_of_nonneg_right hcross_nonneg
        have hgap0 : 0 ≤ A X - we t X := sub_nonneg.mpr hcontact'
        have hop : paperWaveOperator p c (we t) (fun _ : ℝ => A X) X -
              paperWaveOperator p c (we t) (we t) X ≤
            C * (A X - we t X) + E * eta := by
          exact hop0'.trans (add_le_add
            (mul_le_mul_of_nonneg_right hC0C hgap0) le_rfl)
        have hdpos : 0 < A X := by
          exact lowerBarrierPlateau_pos hcond.hκ0 hgap hDpos X
        have hsub : 0 ≤
            paperWaveOperator p c (we t) (fun _ : ℝ => A X) X := by
          exact paperWaveOperator_const_subsolution_nonneg_of_chi_nonpos
            p hchi hqC (fun y => (hqQ y).1) hdpos
              (by simpa only [A] using hplateau X) X
        have htimeDeriv := (hasDerivAt_const t (A X)).sub
          (htimeOp (t := t) (x := X) ht)
        have htimeEq : deriv (fun s : ℝ => A X - we s X) t =
            -paperWaveOperator p c (we t) (we t) X := by
          simpa using htimeDeriv.deriv
        rw [htimeEq]
        linarith [hsub, hop])
  intro t ht x
  have hresult := hcomparison t ht x
  rw [hwe_eq ht] at hresult
  simpa only [A, w] using hresult

section AxiomAudit

#print axioms
  wholeLineCauchyGlobal_coMovingRestart_ge_lowerBarrierPlateau_chiNonpos_scaled

end AxiomAudit

end ShenWork.Paper1
