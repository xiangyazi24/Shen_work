/-
  General-chi source-spectral producer from global B-form data.

  This file builds the exact `Hsource` tuple consumed by
  `IntervalDomainPdeUGeneralChi.hpde_u_of_generalChi_sourceSpectralData`.
  It is intentionally upstream of any classical-solution package: the inputs
  are spectral representation, source C¹ data, and Fourier packages, not an
  already-proved PDE identity.
-/
import ShenWork.Paper2.IntervalDomainPdeUGeneralChi
import ShenWork.Paper2.IntervalBFormRestart
import ShenWork.Paper2.IntervalDuhamelSourceShift
import ShenWork.PDE.IntervalResolverSpectralJointC2Producer

open Set Filter Topology

noncomputable section

namespace ShenWork.IntervalDomainPdeUGeneralChi

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemicalConcentration coupledChemDivSourceCoeffs
   coupledLogisticSourceCoeffs)
open ShenWork.IntervalBFormSpectral (LogisticCosineFourierData)
open ShenWork.Paper2.BankChemSliceFix (ChemDivCosineFourierDataIoo)

/-- Termwise bound by the `ℓ¹` norm. -/
theorem abs_le_tsum_abs_of_summable {c : ℕ → ℝ}
    (hc : Summable (fun n => |c n|)) (n : ℕ) :
    |c n| ≤ ∑' k, |c k| := by
  have hnn : ∀ k, 0 ≤ |c k| := fun k => abs_nonneg _
  simpa using hc.sum_le_tsum ({n} : Finset ℕ) (fun m _ => hnn m)

/-- Build the exact `Hsource` input required by
`hpde_u_of_generalChi_sourceSpectralData` from global B-form cosine data. -/
theorem Hsource_of_bForm_global_generalChi
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (aInit : ℕ → ℝ) (aB : ℝ → ℕ → ℝ)
    (hsrcB : DuhamelSourceTimeC1 aB)
    (hB_global : ∀ t, 0 < t → t ≤ T →
      Set.EqOn (intervalDomainLift (u t))
        (fun x => ∑' n,
          localRestartCoeff aInit aB t n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1))
    (hB_global_summable : ∀ t, 0 < t → t ≤ T →
      Summable (fun n => |localRestartCoeff aInit aB t n|))
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
        (a : ℝ → ℕ → ℝ) (_ : DuhamelSourceTimeC1 a)
        (offset : ℝ) (_ : 0 < t₀ - offset)
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
  have ha_cont : ∀ k, ContinuousOn (fun s => aB s k) (Set.Icc 0 T) := fun k =>
    (continuous_iff_continuousAt.2
      (fun s => (hsrcB.hderiv s k).continuousAt)).continuousOn
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
  have hsrc_shift : DuhamelSourceTimeC1 a := by
    simpa [a] using
      ShenWork.IntervalDuhamelSourceShift.DuhamelSourceTimeC1.shift_nonneg
        hsrcB (offset := τ) hτpos.le
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
  have hsum_b : Summable (fun n => unitIntervalCosineEigenvalue n
      * |localRestartCoeff a₀ a (t₀ - τ) n|) := by
    rw [htmτ]
    exact
      ShenWork.IntervalResolverSpectralJointC2Producer.localRestartCoeff_eigenvalue_summable
        (τ := τ) (M := M) (a₀ := a₀) (a := a) hτpos ha₀_bd hsrc_shift
  exact ⟨a₀, M, hMnn, ha₀_bd,
    a, hsrc_shift, τ, by rw [htmτ]; exact hτpos,
    hlogData t₀ ht₀ ht₀T,
    hchemData t₀ ht₀ ht₀T,
    hrep, hsource_at, hsum_b⟩

/-- Direct general-chi `hpde_u` producer from global B-form cosine data. -/
theorem hpde_u_of_bForm_global_generalChi
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (aInit : ℕ → ℝ) (aB : ℝ → ℕ → ℝ)
    (hsrcB : DuhamelSourceTimeC1 aB)
    (hB_global : ∀ t, 0 < t → t ≤ T →
      Set.EqOn (intervalDomainLift (u t))
        (fun x => ∑' n,
          localRestartCoeff aInit aB t n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1))
    (hB_global_summable : ∀ t, 0 < t → t ≤ T →
      Summable (fun n => |localRestartCoeff aInit aB t n|))
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
  hpde_u_of_generalChi_sourceSpectralData p
    (Hsource_of_bForm_global_generalChi
      (p := p) (T := T) (u := u)
      aInit aB hsrcB hB_global hB_global_summable
      hsource_split hlogData hchemData)

#print axioms Hsource_of_bForm_global_generalChi
#print axioms hpde_u_of_bForm_global_generalChi

end ShenWork.IntervalDomainPdeUGeneralChi
