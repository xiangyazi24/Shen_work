/-
  General-chi `hpde_u` producer from global B-form cosine data and windowed
  source time-regularity.

  This is the `DuhamelSourceTimeC1On` analogue of
  `IntervalDomainPdeUGeneralChiProvider`: it avoids asking for a global
  `DuhamelSourceTimeC1` package when the banked B-form route only has source
  regularity on `[0,T]`.
-/
import ShenWork.Paper2.IntervalDomainPdeUGeneralChiOn
import ShenWork.Paper2.IntervalDomainPdeUGeneralChiProvider
import ShenWork.Paper2.IntervalBFormRestart
import ShenWork.PDE.IntervalDuhamelClosedC2
import ShenWork.PDE.IntervalDuhamelSourceTimeC1On

open Set Filter Topology

noncomputable section

namespace ShenWork.IntervalDomainPdeUGeneralChi

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalDuhamelClosedC2
  (cosineCoeff_summable_of_eigenvalue_summable)
open ShenWork.IntervalDuhamelSourceTimeC1On
  (DuhamelSourceTimeC1On duhamelSpectralCoeff_eigenvalue_summable_on)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemicalConcentration coupledChemDivSourceCoeffs
   coupledLogisticSourceCoeffs)
open ShenWork.IntervalBFormSpectral (LogisticCosineFourierData)
open ShenWork.Paper2.BankChemSliceFix (ChemDivCosineFourierDataIoo)

private theorem localRestartCoeff_eigenvalue_summable_of_on
    {aInit : ℕ → ℝ} {aB : ℝ → ℕ → ℝ} {T τ MInit : ℝ}
    (hτ : 0 < τ) (hτT : τ ≤ T)
    (haInit : ∀ n, |aInit n| ≤ MInit)
    (src : DuhamelSourceTimeC1On aB 0 T) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n * |localRestartCoeff aInit aB τ n|) := by
  have hhom :=
    ShenWork.IntervalMildRegularityBootstrap.restartHomogeneousCoeff_eigenvalue_summable
      hτ haInit
  have hduh := duhamelSpectralCoeff_eigenvalue_summable_on src hτ hτT
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (by unfold unitIntervalCosineEigenvalue; positivity)
      (abs_nonneg _)) (fun n => ?_) (hhom.add hduh)
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left
    (by simp only [localRestartCoeff]; exact abs_add_le _ _)
    (by unfold unitIntervalCosineEigenvalue; positivity)

private theorem localRestartCoeff_abs_summable_of_on
    {aInit : ℕ → ℝ} {aB : ℝ → ℕ → ℝ} {T τ MInit : ℝ}
    (hτ : 0 < τ) (hτT : τ ≤ T)
    (haInit : ∀ n, |aInit n| ≤ MInit)
    (src : DuhamelSourceTimeC1On aB 0 T) :
    Summable (fun n : ℕ => |localRestartCoeff aInit aB τ n|) :=
  (cosineCoeff_summable_of_eigenvalue_summable
    (localRestartCoeff_eigenvalue_summable_of_on hτ hτT haInit src)).2

private def DuhamelSourceTimeC1On.shift_from_zero
    {a : ℝ → ℕ → ℝ} {T offset W : ℝ}
    (src : DuhamelSourceTimeC1On a 0 T)
    (hoffset : 0 ≤ offset)
    (hW : W = T - offset) :
    DuhamelSourceTimeC1On (fun s n => a (offset + s) n) 0 W where
  adot := fun s n => src.adot (offset + s) n
  hderiv := by
    intro s hs n
    have hmap : Set.MapsTo (fun r : ℝ => offset + r)
        (Set.Icc (0 : ℝ) W) (Set.Icc (0 : ℝ) T) := by
      intro r hr
      constructor <;> linarith [hoffset, hr.1, hr.2, hW]
    have hlin : HasDerivWithinAt (fun r : ℝ => offset + r) 1
        (Set.Icc (0 : ℝ) W) s :=
      ((hasDerivAt_id s).const_add offset).hasDerivWithinAt
    have hsrc := src.hderiv (offset + s) (hmap hs) n
    have hcomp := hsrc.comp s hlin hmap
    simpa [Function.comp] using hcomp
  hadotcont := by
    intro n
    have hmap : Set.MapsTo (fun r : ℝ => offset + r)
        (Set.Icc (0 : ℝ) W) (Set.Icc (0 : ℝ) T) := by
      intro r hr
      constructor <;> linarith [hoffset, hr.1, hr.2, hW]
    exact (src.hadotcont n).comp
      ((continuous_const.add continuous_id).continuousOn) hmap
  envelope := src.envelope
  henv_summable := src.henv_summable
  henv_bound := by
    intro s hs n
    exact src.henv_bound (offset + s)
      (by constructor <;> linarith [hoffset, hs.1, hs.2, hW]) n
  derivBound := src.derivBound
  hderivBound := by
    intro s hs n
    exact src.hderivBound (offset + s)
      (by constructor <;> linarith [hoffset, hs.1, hs.2, hW]) n

/-- Build the exact `Hsource` input required by the window-local general-chi
producer from global B-form cosine data and source regularity on `[0,T]`. -/
theorem Hsource_of_bForm_global_generalChiOn
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (aInit : ℕ → ℝ) (aB : ℝ → ℕ → ℝ)
    (MInit : ℝ) (haInit : ∀ n, |aInit n| ≤ MInit)
    (hsrcB_on : DuhamelSourceTimeC1On aB 0 T)
    (hB_global : ∀ t, 0 < t → t ≤ T →
      Set.EqOn (intervalDomainLift (u t))
        (fun x => ∑' n,
          localRestartCoeff aInit aB t n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1))
    (hsource_split : ∀ σ, 0 < σ → σ < T → ∀ n,
      aB σ n = coupledLogisticSourceCoeffs p u σ n
        - p.χ₀ * coupledChemDivSourceCoeffs p u σ n)
    (hlogData : ∀ t, 0 < t → t < T →
      LogisticCosineFourierData p u t)
    (hchemData : ∀ t, 0 < t → t < T →
      ChemDivCosineFourierDataIoo p (u t)
        (coupledChemicalConcentration p u t)) :
    ∀ t₀, 0 < t₀ → t₀ < T →
      ∀ {x : intervalDomainPoint}, x.1 ∈ Set.Ioo (0 : ℝ) 1 →
      ∃ (a₀ : ℕ → ℝ) (M : ℝ) (_ : 0 ≤ M) (_ : ∀ n, |a₀ n| ≤ M)
        (a : ℝ → ℕ → ℝ) (W : ℝ) (_ : DuhamelSourceTimeC1On a 0 W)
        (offset : ℝ) (_ : 0 < t₀ - offset) (_ : t₀ - offset < W)
        (_ : LogisticCosineFourierData p u t₀)
        (_ : ChemDivCosineFourierDataIoo p (u t₀)
          (coupledChemicalConcentration p u t₀)),
        (∀ᶠ s in 𝓝 t₀, ∀ y : intervalDomainPoint,
          u s y = ∑' n, localRestartCoeff a₀ a (s - offset) n
            * cosineMode n y.1) ∧
        (∀ n, a (t₀ - offset) n
          = coupledLogisticSourceCoeffs p u t₀ n
            - p.χ₀ * coupledChemDivSourceCoeffs p u t₀ n) ∧
        Summable (fun n => unitIntervalCosineEigenvalue n
          * |localRestartCoeff a₀ a (t₀ - offset) n|) := by
  intro t₀ ht₀ ht₀T x _hx
  set τ : ℝ := t₀ / 2 with hτdef
  have hτpos : 0 < τ := by rw [hτdef]; linarith
  have hτt₀ : τ < t₀ := by rw [hτdef]; linarith
  have hτT : τ < T := lt_trans hτt₀ ht₀T
  have htmτ : t₀ - τ = τ := by rw [hτdef]; ring
  have hB_global_summable : ∀ t, 0 < t → t ≤ T →
      Summable (fun n : ℕ => |localRestartCoeff aInit aB t n|) :=
    fun t ht htT =>
      localRestartCoeff_abs_summable_of_on ht htT haInit hsrcB_on
  have ha_cont : ∀ k, ContinuousOn (fun s => aB s k) (Set.Icc 0 T) :=
    fun k s hs => (hsrcB_on.hderiv s hs k).continuousWithinAt
  have hB_restart : ∀ t, 0 < t → t < T →
      ∀ᶠ s in 𝓝 t, ∀ y : intervalDomainPoint,
        u s y =
          ∑' n,
            localRestartCoeff
              (cosineCoeffs (intervalDomainLift (u (t / 2))))
              (fun σ n => aB (t / 2 + σ) n)
              (s - t / 2) n * cosineMode n y.1 :=
    ShenWork.IntervalConjugatePicard.bForm_restart_of_global_cosine
      (u := u) (T := T) (a₀ := aInit) (aB := aB)
      ha_cont hB_global hB_global_summable
  set a₀ : ℕ → ℝ := cosineCoeffs (intervalDomainLift (u τ)) with ha₀def
  set a : ℝ → ℕ → ℝ := fun σ n => aB (τ + σ) n with hadef
  set W : ℝ := T - τ with hWdef
  have hsrc_shift : DuhamelSourceTimeC1On a 0 W := by
    simpa [a, hWdef] using
      DuhamelSourceTimeC1On.shift_from_zero
        (a := aB) (T := T) (offset := τ) (W := W)
        hsrcB_on hτpos.le (by rw [hWdef])
  have hsumτ : Summable (fun n => |localRestartCoeff aInit aB τ n|) :=
    hB_global_summable τ hτpos hτT.le
  set M : ℝ := ∑' n, |localRestartCoeff aInit aB τ n| with hMdef
  have hMnn : 0 ≤ M := by
    rw [hMdef]
    exact tsum_nonneg (fun n => abs_nonneg _)
  have ha₀eq : ∀ n, a₀ n = localRestartCoeff aInit aB τ n := by
    intro n
    rw [ha₀def]
    exact
      ShenWork.IntervalConjugatePicard.cosineCoeffs_eq_localRestartCoeff_of_bForm_global_rep
        (u := u) (a₀ := aInit) (aB := aB) (τ := τ)
        (hB_global τ hτpos hτT.le) hsumτ n
  have ha₀_bd : ∀ n, |a₀ n| ≤ M := by
    intro n
    rw [ha₀eq n, hMdef]
    exact abs_le_tsum_abs_of_summable hsumτ n
  have hrep : ∀ᶠ s in 𝓝 t₀, ∀ y : intervalDomainPoint,
      u s y = ∑' n, localRestartCoeff a₀ a (s - τ) n * cosineMode n y.1 := by
    have h := hB_restart t₀ ht₀ ht₀T
    simpa [a₀, a, τ, hτdef] using h
  have hsource_at : ∀ n, a (t₀ - τ) n =
      coupledLogisticSourceCoeffs p u t₀ n
        - p.χ₀ * coupledChemDivSourceCoeffs p u t₀ n := by
    intro n
    have harg : τ + (t₀ - τ) = t₀ := by ring
    change aB (τ + (t₀ - τ)) n =
      coupledLogisticSourceCoeffs p u t₀ n
        - p.χ₀ * coupledChemDivSourceCoeffs p u t₀ n
    rw [harg]
    exact hsource_split t₀ ht₀ ht₀T n
  have hτW : τ < W := by
    rw [hWdef, hτdef]
    linarith
  have hsum_b : Summable (fun n => unitIntervalCosineEigenvalue n
      * |localRestartCoeff a₀ a (t₀ - τ) n|) := by
    rw [htmτ]
    exact localRestartCoeff_eigenvalue_summable_of_on hτpos hτW.le ha₀_bd hsrc_shift
  exact ⟨a₀, M, hMnn, ha₀_bd,
    a, W, hsrc_shift, τ, by rw [htmτ]; exact hτpos,
    by rw [htmτ]; exact hτW,
    hlogData t₀ ht₀ ht₀T,
    hchemData t₀ ht₀ ht₀T,
    hrep, hsource_at, hsum_b⟩

/-- Direct general-chi `hpde_u` producer from global B-form cosine data and a
window-local B-form source package on `[0,T]`. -/
theorem hpde_u_of_bForm_global_generalChiOn
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (aInit : ℕ → ℝ) (aB : ℝ → ℕ → ℝ)
    (MInit : ℝ) (haInit : ∀ n, |aInit n| ≤ MInit)
    (hsrcB_on : DuhamelSourceTimeC1On aB 0 T)
    (hB_global : ∀ t, 0 < t → t ≤ T →
      Set.EqOn (intervalDomainLift (u t))
        (fun x => ∑' n,
          localRestartCoeff aInit aB t n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1))
    (hsource_split : ∀ σ, 0 < σ → σ < T → ∀ n,
      aB σ n = coupledLogisticSourceCoeffs p u σ n
        - p.χ₀ * coupledChemDivSourceCoeffs p u σ n)
    (hlogData : ∀ t, 0 < t → t < T →
      LogisticCosineFourierData p u t)
    (hchemData : ∀ t, 0 < t → t < T →
      ChemDivCosineFourierDataIoo p (u t)
        (coupledChemicalConcentration p u t)) :
    ∀ t x, 0 < t → t < T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv u t x =
        intervalDomain.laplacian (u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (u t)
              (ShenWork.IntervalMildToClassical.mildChemicalConcentration p u t) x
          + u t x * (p.a - p.b * (u t x) ^ p.α) :=
  hpde_u_of_generalChi_sourceSpectralDataOn p
    (Hsource_of_bForm_global_generalChiOn
      (p := p) (T := T) (u := u)
      aInit aB MInit haInit hsrcB_on hB_global hsource_split
      hlogData hchemData)

#print axioms Hsource_of_bForm_global_generalChiOn
#print axioms hpde_u_of_bForm_global_generalChiOn

end ShenWork.IntervalDomainPdeUGeneralChi
