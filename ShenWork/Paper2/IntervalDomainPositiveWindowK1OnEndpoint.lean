import ShenWork.Paper2.IntervalDomainPositiveWindowK1On
import ShenWork.Paper2.IntervalResolverTimeEndpoint

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalDomain (intervalDomainConstExtend)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
open ShenWork.IntervalGradientDuhamelMap (intervalGradientDuhamelMap logisticLifted)
open ShenWork.IntervalMildPicardRegularity
  (logisticSourceFun logisticLifted_eq_logisticSourceFun_on_Icc
    cosineCoeffs_eq_factor_mul_integral cosineCoeffs_abs_le_of_continuous_bounded)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalPicardLimitRestartBdd (DuhamelSourceBddOn)
open ShenWork.IntervalPicardLimitBddProducer (patchedSource)
open ShenWork.IntervalDuhamelSourceTimeC1On (DuhamelSourceTimeC1On)
open ShenWork.IntervalResolverTimeRegularity (ResolverHasSpectralAgreement)
open ShenWork.IntervalResolverTimeEndpoint
open ShenWork.Paper2 (cosineCoeffs_congr_on_Icc)
open ShenWork.Paper2.PicardLimitK1 (slopeSlice sourceDerivSlice adottOf)
open ShenWork.IntervalDomainPositiveWindowK1On
  (sourceCoeff WindowK1Quadruple limitSource_timeC1On_of_windowK1)

noncomputable section

namespace ShenWork.IntervalDomainPositiveWindowK1OnEndpoint

set_option maxHeartbeats 800000 in
-- The compact dominated-convergence proof generates large continuity goals.
/-- A compact-parameter dominated-convergence lemma for cosine coefficients. -/
theorem cosineCoeffs_continuousOn_of_jointContinuousOn_Icc
    {f : ℝ → ℝ → ℝ} {c T : ℝ} (k : ℕ)
    (hf : ContinuousOn (Function.uncurry f)
      (Set.Icc c T ×ˢ Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (fun σ => cosineCoeffs (f σ) k) (Set.Icc c T) := by
  classical
  set I : Set ℝ := Set.Icc c T with hIdef
  set K : Set (ℝ × ℝ) := I ×ˢ Set.Icc (0 : ℝ) 1 with hKdef
  set F : ℝ → ℝ → ℝ :=
    fun σ x => Real.cos ((k : ℝ) * Real.pi * x) * f σ x with hFdef
  have hfK : ContinuousOn (Function.uncurry f) K := by
    simpa [hIdef, hKdef] using hf
  have hcos_cont :
      Continuous (fun x : ℝ => Real.cos ((k : ℝ) * Real.pi * x)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id')
  have hFcont : ContinuousOn (Function.uncurry F) K := by
    rw [hFdef]
    exact (hcos_cont.comp continuous_snd).continuousOn.mul hfK
  have hKcompact : IsCompact K := by
    rw [hKdef, hIdef]
    exact isCompact_Icc.prod isCompact_Icc
  obtain ⟨B, hB⟩ := hKcompact.bddAbove_image hFcont.norm
  set B' := max B 0 with hB'def
  have hB'nn : 0 ≤ B' := le_max_right _ _
  have hFbd : ∀ σ ∈ I, ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖F σ x‖ ≤ B' := by
    intro σ hσ x hx
    have hmem : (σ, x) ∈ K := by
      rw [hKdef]
      exact Set.mem_prod.mpr ⟨hσ, hx⟩
    have : ‖Function.uncurry F (σ, x)‖ ≤ B :=
      hB (Set.mem_image_of_mem _ hmem)
    have hBle : B ≤ B' := by
      rw [hB'def]
      exact le_max_left _ _
    have hle : ‖Function.uncurry F (σ, x)‖ ≤ B' := le_trans this hBle
    simpa [Function.uncurry] using hle
  have hsec_cont :
      ∀ σ ∈ I, ContinuousOn (F σ) (Set.Icc (0 : ℝ) 1) := by
    intro σ hσ
    have hmaps : Set.MapsTo (fun x : ℝ => ((σ, x) : ℝ × ℝ))
        (Set.Icc (0 : ℝ) 1) K := by
      intro x hx
      rw [hKdef]
      exact Set.mem_prod.mpr ⟨hσ, hx⟩
    have hpair_cont : ContinuousOn (fun x : ℝ => ((σ, x) : ℝ × ℝ))
        (Set.Icc (0 : ℝ) 1) :=
      continuousOn_const.prodMk continuousOn_id
    have hcomp : ContinuousOn
        ((Function.uncurry F) ∘ fun x : ℝ => ((σ, x) : ℝ × ℝ))
        (Set.Icc (0 : ℝ) 1) :=
      hFcont.comp hpair_cont hmaps
    simpa [Function.comp_def, Function.uncurry] using hcomp
  intro σ₀ hσ₀
  have hint_cont :
      ContinuousWithinAt (fun σ => ∫ x in (0 : ℝ)..1, F σ x) I σ₀ := by
    refine intervalIntegral.continuousWithinAt_of_dominated_interval
      (bound := fun _ => B') ?_ ?_ intervalIntegrable_const ?_
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      have hcont : ContinuousOn (F σ) (Set.uIcc (0 : ℝ) 1) := by
        rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        exact hsec_cont σ hσ
      exact (hcont.mono Set.uIoc_subset_uIcc).aestronglyMeasurable
        measurableSet_uIoc
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      refine Filter.Eventually.of_forall (fun x hx => ?_)
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      exact hFbd σ hσ x ⟨hx.1.le, hx.2⟩
    · refine Filter.Eventually.of_forall (fun x hx => ?_)
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
      have hcwa : ContinuousWithinAt (fun σ => F σ x) I σ₀ := by
        have hmaps : Set.MapsTo (fun σ : ℝ => ((σ, x) : ℝ × ℝ)) I K := by
          intro σ hσ
          rw [hKdef]
          exact Set.mem_prod.mpr ⟨hσ, hxIcc⟩
        have hpair_cont : ContinuousOn (fun σ : ℝ => ((σ, x) : ℝ × ℝ)) I :=
          continuousOn_id.prodMk continuousOn_const
        have hcomp : ContinuousOn
            ((Function.uncurry F) ∘ fun σ : ℝ => ((σ, x) : ℝ × ℝ)) I :=
          hFcont.comp hpair_cont hmaps
        simpa [Function.comp_def, Function.uncurry] using
          hcomp.continuousWithinAt hσ₀
      exact hcwa
  have hadeq : ∀ σ, cosineCoeffs (f σ) k =
      (if k = 0 then (1 : ℝ) else 2) * ∫ x in (0 : ℝ)..1, F σ x := by
    intro σ
    rw [hFdef, cosineCoeffs_eq_factor_mul_integral]
  have hfun : (fun σ => cosineCoeffs (f σ) k) =
      fun σ => (if k = 0 then (1 : ℝ) else 2) *
        ∫ x in (0 : ℝ)..1, F σ x := funext hadeq
  rw [hfun]
  exact hint_cont.const_mul _

/-- Joint continuity of the logistic source slice on a closed positive window. -/
theorem logisticSource_jointContinuousOn_Icc_of_lt_horizon
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {U T c : ℝ}
    (H : ResolverHasSpectralAgreement U u)
    (hc : 0 < c) (hTU : T < U)
    (hpos : ∀ σ ∈ Set.Icc c T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (u σ) x) :
    ContinuousOn
      (Function.uncurry
        (fun σ x => logisticSourceFun p.a p.b p.α
          (intervalDomainLift (u σ)) x))
      (Set.Icc c T ×ˢ Set.Icc (0 : ℝ) 1) := by
  have hlift : ContinuousOn
      (Function.uncurry (fun σ x => intervalDomainLift (u σ) x))
      (Set.Icc c T ×ˢ Set.Icc (0 : ℝ) 1) := by
    exact (ShenWork.IntervalResolverTimeRegularity.resolver_jointContinuousOn_closed H).mono
      (by
        intro q hq
        obtain ⟨hσ, hx⟩ := Set.mem_prod.mp hq
        exact Set.mem_prod.mpr
          ⟨⟨lt_of_lt_of_le hc hσ.1, lt_of_le_of_lt hσ.2 hTU⟩, hx⟩)
  have hpow : ContinuousOn
      (fun q : ℝ × ℝ => (intervalDomainLift (u q.1) q.2) ^ p.α)
      (Set.Icc c T ×ˢ Set.Icc (0 : ℝ) 1) := by
    apply ContinuousOn.rpow_const hlift
    intro q hq
    obtain ⟨hσ, hx⟩ := Set.mem_prod.mp hq
    exact Or.inl (ne_of_gt (hpos q.1 hσ q.2 hx))
  have hbody : ContinuousOn
      (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2 *
        (p.a - p.b * (intervalDomainLift (u q.1) q.2) ^ p.α))
      (Set.Icc c T ×ˢ Set.Icc (0 : ℝ) 1) :=
    hlift.mul (continuousOn_const.sub (continuousOn_const.mul hpow))
  exact hbody.congr (by
    intro q hq
    rfl)

/-- Continuity of the source coefficient on a closed positive window. -/
theorem sourceCoeff_continuousOn_Icc_of_lt_horizon
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {U T c : ℝ}
    (H : ResolverHasSpectralAgreement U u)
    (hc : 0 < c) (hTU : T < U)
    (hpos : ∀ σ ∈ Set.Icc c T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (u σ) x)
    (k : ℕ) :
    ContinuousOn (fun σ => sourceCoeff p u σ k) (Set.Icc c T) := by
  simpa [sourceCoeff] using
    cosineCoeffs_continuousOn_of_jointContinuousOn_Icc (c := c) (T := T) k
      (logisticSource_jointContinuousOn_Icc_of_lt_horizon H hc hTU hpos)

/-- Joint continuity of `sourceDerivSlice` on a closed positive window. -/
theorem sourceDerivSlice_continuousOn_Icc_of_lt_horizon
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {U T c : ℝ}
    (H : ResolverHasSpectralAgreement U u)
    (hc : 0 < c) (hTU : T < U)
    (hpos : ∀ σ ∈ Set.Icc c T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (u σ) x) :
    ContinuousOn (Function.uncurry (sourceDerivSlice p u))
      (Set.Icc c T ×ˢ Set.Icc (0 : ℝ) 1) := by
  have hslope : ContinuousOn (fun q : ℝ × ℝ => slopeSlice u q.1 q.2)
      (Set.Icc c T ×ˢ Set.Icc (0 : ℝ) 1) := by
    simpa [slopeSlice, Function.uncurry] using
      resolver_timeDeriv_jointContinuousOn_Icc_time_closedSpace_of_lt_horizon
        (v := u) H hc hTU
  have hlift : ContinuousOn
      (Function.uncurry (fun σ x => intervalDomainLift (u σ) x))
      (Set.Icc c T ×ˢ Set.Icc (0 : ℝ) 1) := by
    exact (ShenWork.IntervalResolverTimeRegularity.resolver_jointContinuousOn_closed H).mono
      (by
        intro q hq
        obtain ⟨hσ, hx⟩ := Set.mem_prod.mp hq
        exact Set.mem_prod.mpr
          ⟨⟨lt_of_lt_of_le hc hσ.1, lt_of_le_of_lt hσ.2 hTU⟩, hx⟩)
  have hpow : ContinuousOn
      (fun q : ℝ × ℝ => (intervalDomainLift (u q.1) q.2) ^ p.α)
      (Set.Icc c T ×ˢ Set.Icc (0 : ℝ) 1) := by
    apply ContinuousOn.rpow_const hlift
    intro q hq
    obtain ⟨hσ, hx⟩ := Set.mem_prod.mp hq
    exact Or.inl (ne_of_gt (hpos q.1 hσ q.2 hx))
  have hfactor : ContinuousOn
      (fun q : ℝ × ℝ =>
        p.a - p.b * (1 + p.α) * (intervalDomainLift (u q.1) q.2) ^ p.α)
      (Set.Icc c T ×ˢ Set.Icc (0 : ℝ) 1) :=
    continuousOn_const.sub (continuousOn_const.mul hpow)
  have hprod := hslope.mul hfactor
  exact hprod.congr (by
    intro q hq
    rfl)

/-- `adottOf(., k)` is continuous on the closed positive endpoint window. -/
theorem adottOf_continuousOn_Icc_of_lt_horizon
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {U T c : ℝ}
    (H : ResolverHasSpectralAgreement U u)
    (hc : 0 < c) (hTU : T < U)
    (hpos : ∀ σ ∈ Set.Icc c T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (u σ) x)
    (k : ℕ) :
    ContinuousOn (fun σ => adottOf p u σ k) (Set.Icc c T) := by
  simpa [adottOf] using
    cosineCoeffs_continuousOn_of_jointContinuousOn_Icc (c := c) (T := T) k
      (sourceDerivSlice_continuousOn_Icc_of_lt_horizon H hc hTU hpos)

/-- Uniform-in-mode bound for `adottOf` on the endpoint window. -/
theorem exists_Mdot_adottOf_bound_Icc_of_lt_horizon
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {U T c : ℝ}
    (H : ResolverHasSpectralAgreement U u)
    (hc : 0 < c) (hTU : T < U)
    (hpos : ∀ σ ∈ Set.Icc c T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (u σ) x) :
    ∃ Mdot, ∀ σ ∈ Set.Icc c T, ∀ k, |adottOf p u σ k| ≤ Mdot := by
  classical
  set K : Set (ℝ × ℝ) := Set.Icc c T ×ˢ Set.Icc (0 : ℝ) 1 with hKdef
  have hcontK : ContinuousOn (Function.uncurry (sourceDerivSlice p u)) K := by
    simpa [hKdef] using
      sourceDerivSlice_continuousOn_Icc_of_lt_horizon H hc hTU hpos
  have hKcompact : IsCompact K := by
    rw [hKdef]
    exact isCompact_Icc.prod isCompact_Icc
  obtain ⟨B, hB⟩ := (hKcompact.bddAbove_image (hcontK.norm)).imp (fun B hB => hB)
  set B' := max B 0 with hB'def
  have hB'nn : 0 ≤ B' := le_max_right _ _
  have hbd : ∀ σ ∈ Set.Icc c T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |sourceDerivSlice p u σ x| ≤ B' := by
    intro σ hσ x hx
    have hmem : (σ, x) ∈ K := by
      rw [hKdef]
      exact Set.mem_prod.mpr ⟨hσ, hx⟩
    have : ‖Function.uncurry (sourceDerivSlice p u) (σ, x)‖ ≤ B :=
      hB (Set.mem_image_of_mem _ hmem)
    simp only [Function.uncurry, Real.norm_eq_abs] at this
    have hBle : B ≤ B' := by
      rw [hB'def]
      exact le_max_left _ _
    exact le_trans this hBle
  refine ⟨2 * B', fun σ hσ k => ?_⟩
  have hsec : ContinuousOn (sourceDerivSlice p u σ) (Set.Icc (0 : ℝ) 1) := by
    have hmaps : Set.MapsTo (fun x : ℝ => ((σ, x) : ℝ × ℝ))
        (Set.Icc (0 : ℝ) 1) K := by
      intro x hx
      rw [hKdef]
      exact Set.mem_prod.mpr ⟨hσ, hx⟩
    exact hcontK.comp (continuousOn_const.prodMk continuousOn_id) hmaps
  exact cosineCoeffs_abs_le_of_continuous_bounded hsec hB'nn
    (fun x hx => hbd σ hσ x hx) k

/-- Endpoint FTC for the source coefficient in the `sourceCoeff` normal form. -/
theorem sourceCoeff_hasDerivWithinAt_endpoint_sourceCoeff
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {U T c : ℝ}
    (H : ResolverHasSpectralAgreement U u)
    (hc : 0 < c) (hTU : T < U) (hcT : c < T)
    (hpos : ∀ σ ∈ Set.Icc c T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (u σ) x)
    (hderiv_int : ∀ σ, c < σ → σ < T → ∀ k,
      HasDerivAt (fun r => sourceCoeff p u r k) (adottOf p u σ k) σ)
    (k : ℕ) :
    HasDerivWithinAt (fun s => sourceCoeff p u s k)
      (adottOf p u T k) (Set.Icc c T) T := by
  classical
  set f : ℝ → ℝ := fun s => sourceCoeff p u s k with hfdef
  set g : ℝ → ℝ := fun s => adottOf p u s k with hgdef
  have hfcont : ContinuousOn f (Set.Icc c T) := by
    simpa [hfdef] using
      sourceCoeff_continuousOn_Icc_of_lt_horizon H hc hTU hpos k
  have hgcont : ContinuousOn g (Set.Icc c T) := by
    simpa [hgdef] using
      adottOf_continuousOn_Icc_of_lt_horizon H hc hTU hpos k
  have hFTC : ∀ y ∈ Set.Icc c T, ∫ s in c..y, g s = f y - f c := by
    intro y hy
    have hcy : c ≤ y := hy.1
    have hsub : Set.Icc c y ⊆ Set.Icc c T :=
      fun s hs => ⟨hs.1, le_trans hs.2 hy.2⟩
    have hfcont_y : ContinuousOn f (Set.Icc c y) := hfcont.mono hsub
    have hgint_y : IntervalIntegrable g volume c y :=
      (hgcont.mono hsub).intervalIntegrable_of_Icc hcy
    have hderiv_y : ∀ s ∈ Set.Ioo c y, HasDerivAt f (g s) s := by
      intro s hs
      have hsT : s < T := lt_of_lt_of_le hs.2 hy.2
      simpa [hfdef, hgdef] using hderiv_int s hs.1 hsT k
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      hcy hfcont_y hderiv_y hgint_y
  have hIcc_mem : Set.Icc c T ∈ 𝓝[Set.Iic T] T := by
    have hIoi : Set.Ioi c ∈ 𝓝[Set.Iic T] T :=
      mem_nhdsWithin_of_mem_nhds (isOpen_Ioi.mem_nhds hcT)
    filter_upwards [self_mem_nhdsWithin, hIoi] with y hyT hyc
    exact ⟨hyc.le, hyT⟩
  have hg_cwa : ContinuousWithinAt g (Set.Icc c T) T :=
    hgcont.continuousWithinAt ⟨hcT.le, le_rfl⟩
  have hg_iic : ContinuousWithinAt g (Set.Iic T) T :=
    hg_cwa.mono_of_mem_nhdsWithin hIcc_mem
  have hg_sm : StronglyMeasurableAtFilter g (𝓝[Set.Iic T] T) :=
    ⟨Set.Icc c T, hIcc_mem, hgcont.aestronglyMeasurable measurableSet_Icc⟩
  have hIntDeriv_iic :
      HasDerivWithinAt (fun y => ∫ s in c..y, g s) (g T) (Set.Iic T) T :=
    intervalIntegral.integral_hasDerivWithinAt_right
      (a := c) (b := T) (s := Set.Iic T) (t := Set.Iic T)
      (hgcont.intervalIntegrable_of_Icc hcT.le) hg_sm hg_iic
  have hIntDeriv :
      HasDerivWithinAt (fun y => ∫ s in c..y, g s) (g T) (Set.Icc c T) T :=
    hIntDeriv_iic.mono (fun y hy => hy.2)
  have hJ : HasDerivWithinAt (fun y => f c + ∫ s in c..y, g s)
      (g T) (Set.Icc c T) T := by
    have hconst : HasDerivWithinAt (fun _ : ℝ => f c) 0 (Set.Icc c T) T :=
      hasDerivWithinAt_const (c := f c) (s := Set.Icc c T) (x := T)
    have hadd := hconst.add hIntDeriv
    have hJ0 : HasDerivWithinAt (fun y => f c + ∫ s in c..y, g s)
        (0 + g T) (Set.Icc c T) T := by
      refine hadd.congr_of_eventuallyEq ?_ ?_
      · exact Filter.Eventually.of_forall (fun _ => rfl)
      · rfl
    simpa only [zero_add] using hJ0
  have hev : (fun y => f y) =ᶠ[𝓝[Set.Icc c T] T]
      (fun y => f c + ∫ s in c..y, g s) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have h := hFTC y hy
    linarith
  have hx : f T = f c + ∫ s in c..T, g s := by
    have h := hFTC T ⟨hcT.le, le_rfl⟩
    linarith
  simpa [hfdef, hgdef] using hJ.congr_of_eventuallyEq hev hx

/-- The endpoint derivative for the canonical lifted source coefficient. -/
theorem source_coeff_hasDerivWithinAt_endpoint
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {U T c : ℝ}
    (H : ResolverHasSpectralAgreement U u)
    (hc : 0 < c) (hTU : T < U) (hcT : c < T)
    (hpos : ∀ σ ∈ Set.Icc c T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (u σ) x)
    (hderiv_int : ∀ σ, c < σ → σ < T → ∀ k,
      HasDerivAt (fun r => sourceCoeff p u r k) (adottOf p u σ k) σ)
    (k : ℕ) :
    HasDerivWithinAt
      (fun s => cosineCoeffs (logisticLifted p (u s)) k)
      (adottOf p u T k) (Set.Icc c T) T := by
  have hbase :=
    sourceCoeff_hasDerivWithinAt_endpoint_sourceCoeff
      H hc hTU hcT hpos hderiv_int k
  refine hbase.congr_of_eventuallyEq ?_ ?_
  · refine Filter.Eventually.of_forall (fun s => ?_)
    exact cosineCoeffs_congr_on_Icc
      (logisticLifted_eq_logisticSourceFun_on_Icc p (u s)) k
  · exact cosineCoeffs_congr_on_Icc
      (logisticLifted_eq_logisticSourceFun_on_Icc p (u T)) k

/-- Endpoint-inclusive K1 quadruple on `[c,T]`. -/
noncomputable def windowK1Quadruple_endpoint_of_subtypeCont
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    {u₀ : intervalDomainPoint → ℝ} (u : ℝ → intervalDomainPoint → ℝ)
    {U T c : ℝ}
    (H : ResolverHasSpectralAgreement U u)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hu₀_cont : Continuous u₀)
    {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hfix : ∀ s, 0 < s → s < T → ∀ x : ℝ,
      (hx : x ∈ Set.Icc (0 : ℝ) 1) →
        intervalDomainLift (u s) x =
          intervalGradientDuhamelMap p u₀ u s ⟨x, hx⟩)
    (hsrc0 : DuhamelSourceBddOn (patchedSource p u₀ u) T)
    {Msup : ℝ}
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ, 0 < σ → σ < T →
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagree : ∀ σ, 0 < σ → σ < T →
      Set.EqOn (intervalDomainLift (u σ))
        (fun x => ∑' n, bc σ n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1))
    (hpost : ∀ σ, 0 < σ → σ < T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (u σ) x)
    (hubt : ∀ σ, 0 < σ → σ < T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (u σ) x ≤ Msup)
    (hG1t : ∀ a' b', 0 < a' → b' < T → ∃ G1,
      ∀ σ ∈ Set.Icc a' b', ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (intervalDomainLift (u σ)) x| ≤ G1)
    (hG2t : ∀ a' b', 0 < a' → b' < T → ∃ G2,
      ∀ σ ∈ Set.Icc a' b', ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (deriv (intervalDomainLift (u σ))) x| ≤ G2)
    (hLc_ce : ∀ t, 0 < t → t < T →
      ∀ s, 0 < s → s ≤ t →
        Continuous (intervalDomainConstExtend (intervalLogisticSource p (u s))))
    (hc : 0 < c) (hcT : c < T) (hTU : T < U)
    (hposC : ∀ σ ∈ Set.Icc c T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (u σ) x) :
    WindowK1Quadruple p u c T := by
  classical
  obtain ⟨hderiv_int, _hadotcont_int, _hMdot_int⟩ :=
    ShenWork.Paper2.PicardLimitK1Weak.k1_quadruple_weak_of_subtypeCont hχ0 u hα ha hb
      hu₀_cont hu₀_bound hfix hsrc0 bc hbsum hagree hpost hubt
      hG1t hG2t hLc_ce
  let hMdot_exists :=
    exists_Mdot_adottOf_bound_Icc_of_lt_horizon (p := p) H hc hTU hposC
  let Mdot := Classical.choose hMdot_exists
  have hMdot := Classical.choose_spec hMdot_exists
  refine
    { adot := adottOf p u
      hderiv := ?_
      hadotcont := ?_
      Mdot := Mdot
      hMdot := hMdot }
  · intro σ hσ k
    rcases lt_or_eq_of_le hσ.2 with hσT | rfl
    · have hσ0 : 0 < σ := lt_of_lt_of_le hc hσ.1
      exact (hderiv_int σ hσ0 hσT k).hasDerivWithinAt
    · exact sourceCoeff_hasDerivWithinAt_endpoint_sourceCoeff H hc hTU hcT
        hposC
        (fun s hcs hsT k => hderiv_int s (lt_trans hc hcs) hsT k) k
  · intro k
    exact adottOf_continuousOn_Icc_of_lt_horizon H hc hTU hposC k

/-- Endpoint-inclusive source `TimeC1On` package on the closed positive window. -/
noncomputable def limitSource_timeC1On_endpoint_of_subtypeCont
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    {u₀ : intervalDomainPoint → ℝ} (u : ℝ → intervalDomainPoint → ℝ)
    {U T c M G1 G2 : ℝ}
    (H : ResolverHasSpectralAgreement U u)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hu₀_cont : Continuous u₀)
    {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hfix : ∀ s, 0 < s → s < T → ∀ x : ℝ,
      (hx : x ∈ Set.Icc (0 : ℝ) 1) →
        intervalDomainLift (u s) x =
          intervalGradientDuhamelMap p u₀ u s ⟨x, hx⟩)
    (hsrc0 : DuhamelSourceBddOn (patchedSource p u₀ u) T)
    (bc : ℝ → ℕ → ℝ)
    (hbsumT : ∀ σ, 0 < σ → σ < T →
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagreeT : ∀ σ, 0 < σ → σ < T →
      Set.EqOn (intervalDomainLift (u σ))
        (fun x => ∑' n, bc σ n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1))
    (hpost : ∀ σ, 0 < σ → σ < T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (u σ) x)
    (hubt : ∀ σ, 0 < σ → σ < T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (u σ) x ≤ M)
    (hG1t : ∀ a' b', 0 < a' → b' < T → ∃ G1',
      ∀ σ ∈ Set.Icc a' b', ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (intervalDomainLift (u σ)) x| ≤ G1')
    (hG2t : ∀ a' b', 0 < a' → b' < T → ∃ G2',
      ∀ σ ∈ Set.Icc a' b', ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (deriv (intervalDomainLift (u σ))) x| ≤ G2')
    (hLc_ce : ∀ t, 0 < t → t < T →
      ∀ s, 0 < s → s ≤ t →
        Continuous (intervalDomainConstExtend (intervalLogisticSource p (u s))))
    (hc : 0 < c) (hcT : c < T) (hTU : T < U)
    (hbsumC : ∀ σ ∈ Set.Icc c T, Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagreeC : ∀ σ ∈ Set.Icc c T,
      Set.EqOn (intervalDomainLift (u σ))
        (fun x => ∑' n, bc σ n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1))
    (hposC : ∀ σ ∈ Set.Icc c T,
      ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (u σ) x)
    (hubC : ∀ σ ∈ Set.Icc c T,
      ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (u σ) x ≤ M)
    (hG1 : ∀ σ ∈ Set.Icc c T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (u σ)) x| ≤ G1)
    (hG2 : ∀ σ ∈ Set.Icc c T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv (intervalDomainLift (u σ))) x| ≤ G2) :
    DuhamelSourceTimeC1On
      (fun s k => cosineCoeffs (logisticLifted p (u s)) k) c T :=
  let K1 := windowK1Quadruple_endpoint_of_subtypeCont hχ0 u H
    hα ha hb hu₀_cont hu₀_bound hfix hsrc0 bc hbsumT hagreeT hpost
    hubt hG1t hG2t hLc_ce hc hcT hTU hposC
  limitSource_timeC1On_of_windowK1 p u hα ha hb hcT.le bc
    hbsumC hagreeC hposC hubC hG1 hG2 K1

end ShenWork.IntervalDomainPositiveWindowK1OnEndpoint
