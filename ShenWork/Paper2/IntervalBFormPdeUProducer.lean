/-
  B-form general-χ interior PDE producer.

  This is the general-χ analogue of `IntervalDomainPdeUProducer`: it consumes
  local B-form restart spectral data and discharges the two frontier hypotheses
  of `hpde_u_core_general_chi`:

  * `htime` from the restart cosine time-differentiation theorem;
  * `hchem` from chem-div cosine Fourier convergence.

  The remaining carried inputs are named regularity/spectral data that are
  satisfiable upstream: local restart agreement, source coefficient split,
  cosine inversion packages for logistic/chemDiv, and eigenvalue-weighted
  coefficient summability for the Laplacian.

  Proof-only file; no extra assumptions are introduced.
-/
import ShenWork.Paper2.IntervalBFormSpectralHtime

open Set Filter Topology

noncomputable section

namespace ShenWork.IntervalBFormSpectral

open ShenWork.IntervalDomain
  (intervalDomainPoint intervalDomain intervalDomainLift)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemicalConcentration coupledChemDivSourceCoeffs
   coupledLogisticSourceCoeffs)
open ShenWork.IntervalMildToClassical (mildChemicalConcentration)

/-- Per-time B-form spectral PDE agreement.  This is the data needed to produce
the interior PDE without carrying `htime` or `hchem` themselves. -/
structure HasBFormSpectralPdeAgreement
    (p : CM2Params) (T : ℝ) (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  exists_data : ∀ t₀, 0 < t₀ → t₀ < T →
    ∀ {x : intervalDomainPoint}, x.1 ∈ Set.Ioo (0 : ℝ) 1 →
    ∃ (a₀ : ℕ → ℝ) (M : ℝ) (_ : 0 ≤ M) (_ : ∀ n, |a₀ n| ≤ M)
      (a : ℝ → ℕ → ℝ) (_ : DuhamelSourceTimeC1 a)
      (offset : ℝ) (_ : 0 < t₀ - offset)
      (_ : LogisticCosineFourierData p u t₀)
      (_ : ChemDivCosineFourierData p (u t₀)
        (coupledChemicalConcentration p u t₀)),
      (∀ᶠ s in 𝓝 t₀, ∀ y : intervalDomainPoint,
        u s y = ∑' n, localRestartCoeff a₀ a (s - offset) n
          * cosineMode n y.1) ∧
      (∀ n, a (t₀ - offset) n
        = coupledLogisticSourceCoeffs p u t₀ n
          - p.χ₀ * coupledChemDivSourceCoeffs p u t₀ n) ∧
      Summable (fun n => unitIntervalCosineEigenvalue n
        * |localRestartCoeff a₀ a (t₀ - offset) n|)

private theorem eigenvalue_coeff_cosine_summable
    {b : ℕ → ℝ}
    (hsum_b : Summable (fun n => unitIntervalCosineEigenvalue n * |b n|))
    (x : ℝ) :
    Summable (fun n => unitIntervalCosineEigenvalue n * b n * cosineMode n x) := by
  refine Summable.of_norm_bounded
    (g := fun n => unitIntervalCosineEigenvalue n * |b n|) hsum_b ?_
  intro n
  have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
    unfold unitIntervalCosineEigenvalue
    positivity
  have hcos : |cosineMode n x| ≤ 1 := by
    unfold cosineMode
    exact Real.abs_cos_le_one _
  calc
    ‖unitIntervalCosineEigenvalue n * b n * cosineMode n x‖
        = unitIntervalCosineEigenvalue n * |b n| * |cosineMode n x| := by
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hlam]
    _ ≤ unitIntervalCosineEigenvalue n * |b n| * 1 :=
          mul_le_mul_of_nonneg_left hcos (mul_nonneg hlam (abs_nonneg _))
    _ = unitIntervalCosineEigenvalue n * |b n| := by ring

/-- B-form general-χ interior PDE producer.  The fixed-point predicate marks the
trajectory as the B-form mild solution; the spectral agreement supplies the local
restart representation and regularity data used below. -/
theorem intervalConjugateMildSolution_pde_u_of_spectral
    (p : CM2Params) {T : ℝ} {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (_hB : ShenWork.IntervalConjugateDuhamelMap.IntervalConjugateMildSolution
      p T u₀ u)
    (Hpde : HasBFormSpectralPdeAgreement p T u) :
    ∀ t x, 0 < t → t < T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv u t x =
        intervalDomain.laplacian (u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (u t)
              (mildChemicalConcentration p u t) x
          + u t x * (p.a - p.b * (u t x) ^ p.α) := by
  intro t x ht htT hx
  have hxIoo : x.1 ∈ Set.Ioo (0 : ℝ) 1 := hx
  obtain ⟨a₀, M, hM, ha₀, a, src, offset, hoff,
      hlogData, hchemData, hrep, hsource_split, hsum_b⟩ :=
    Hpde.exists_data t ht htT hxIoo
  have htime :
      intervalDomain.timeDeriv u t x
        = ∑' n,
            (coupledLogisticSourceCoeffs p u t n
              - p.χ₀ * coupledChemDivSourceCoeffs p u t n
              - unitIntervalCosineEigenvalue n
                * localRestartCoeff a₀ a (t - offset) n)
              * cosineMode n x.1 :=
    bForm_timeDeriv_eq_of_local_restart p hM ha₀ src hoff hrep
      hsource_split x
  have hrep_real : ∀ z ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (u t) z
        = ∑' n, localRestartCoeff a₀ a (t - offset) n * cosineMode n z := by
    intro z hz
    rw [intervalDomainLift, dif_pos hz]
    exact hrep.self_of_nhds ⟨z, hz⟩
  have hlap :
      intervalDomain.laplacian (u t) x
        = ∑' n, localRestartCoeff a₀ a (t - offset) n
            * (-(((n : ℝ) * Real.pi) ^ 2)
              * Real.cos ((n : ℝ) * Real.pi * x.1)) :=
    ShenWork.IntervalDomainPdeUChiZero.laplacian_eq_of_rep
      hsum_b hrep_real hxIoo
  have hreact :
      (∑' n, coupledLogisticSourceCoeffs p u t n * cosineMode n x.1)
        = u t x * (p.a - p.b * (u t x) ^ p.α) :=
    coupledLogistic_cosineFourier_convergence hlogData hxIoo
  have hchem :
      (∑' n, coupledChemDivSourceCoeffs p u t n * cosineMode n x.1)
        = intervalDomain.chemotaxisDiv p (u t)
            (mildChemicalConcentration p u t) x :=
    coupledChemDiv_cosineFourier_convergence p u t hchemData hxIoo
  have hsum_src :
      Summable (fun n =>
        coupledLogisticSourceCoeffs p u t n * cosineMode n x.1) :=
    coupledLogistic_cosineSeries_summable hlogData hxIoo
  have hsum_chem :
      Summable (fun n =>
        coupledChemDivSourceCoeffs p u t n * cosineMode n x.1) :=
    coupledChemDiv_cosineSeries_summable p u t hchemData hxIoo
  have hsum_lb :
      Summable (fun n => unitIntervalCosineEigenvalue n
        * localRestartCoeff a₀ a (t - offset) n * cosineMode n x.1) :=
    eigenvalue_coeff_cosine_summable hsum_b x.1
  exact ShenWork.IntervalConjugateDuhamelMap.hpde_u_core_general_chi p
    (u := u) (t₀ := t) (x := x)
    (b := fun n => localRestartCoeff a₀ a (t - offset) n)
    (src := fun n => coupledLogisticSourceCoeffs p u t n)
    (chem := fun n => coupledChemDivSourceCoeffs p u t n)
    hsum_src hsum_chem hsum_lb htime hlap hreact hchem

#print axioms intervalConjugateMildSolution_pde_u_of_spectral

end ShenWork.IntervalBFormSpectral
