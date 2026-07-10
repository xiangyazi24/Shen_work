import ShenWork.Paper2.IntervalBFormHSigmaDuhamelEnergy
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
  The genuine `L∞_t ℓ²_k → H^σ_k` divergence-Duhamel estimate.

  Unlike a per-mode supremum envelope, the hypotheses below only bound the
  `ℓ²` norm of each time slice.  The proof first applies the scalar spectral
  multiplier estimate to a finite-dimensional Euclidean truncation.  The
  Bochner integral triangle inequality then gives a bound independent of the
  truncation dimension.  Bounded nonnegative partial sums yield the full
  `H^σ` summability statement.
-/

noncomputable section

namespace ShenWork.Paper2.BFormHSigmaLinftyL2Smoothing

open MeasureTheory
open Real intervalIntegral
open ShenWork.Paper2.HSigmaScale
open ShenWork.Paper2.BFormHSigmaLinftyMultiplier
open ShenWork.Paper2.BFormHSigmaDuhamelMode
open ShenWork.Paper2.BFormHSigmaDuhamelEnergy

/-- **True `L∞_t ℓ² → H^σ` divergence-Duhamel smoothing.**

For every time slice on `[0,s]`, assume only that the squared source
coefficients are summable and have total mass at most `M`.  No common
mode-by-mode envelope is used.  For `0 ≤ σ < 1`, the divergence-Duhamel output
belongs to `H^σ`, with the expected `s^(1-σ)` squared-energy rate. -/
theorem hSigmaEnergy_duhamel_bound_of_slice_l2
    {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1)
    {d : ℝ} (hd : 0 < d) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    {F : ℕ → ℝ → ℝ} (hFcont : ∀ k, Continuous (F k)) {M : ℝ}
    (hFsummable : ∀ τ ∈ Set.Icc (0 : ℝ) s, Summable fun k => (F k τ) ^ 2)
    (hFenergy : ∀ τ ∈ Set.Icc (0 : ℝ) s, ∑' k, (F k τ) ^ 2 ≤ M) :
    MemHSigma σ (duhamelEnergyCoeff d F s) ∧
      hSigmaEnergy σ (duhamelEnergyCoeff d F s) ≤
        (Classical.choose (linfty_multiplier_bound hσ0 hσ1 d hd)) ^ 2 * M *
          (s ^ ((1 - σ) / 2) / ((1 - σ) / 2)) ^ 2 := by
  let C := Classical.choose (linfty_multiplier_bound hσ0 hσ1 d hd)
  have hCpos : 0 < C :=
    (Classical.choose_spec (linfty_multiplier_bound hσ0 hσ1 d hd)).1
  have hC := (Classical.choose_spec (linfty_multiplier_bound hσ0 hσ1 d hd)).2
  let p : ℝ := (σ + 1) / 2
  let R : ℝ := s ^ ((1 - σ) / 2) / ((1 - σ) / 2)
  have hp0 : 0 ≤ p := by dsimp [p]; linarith
  have hp1 : p < 1 := by dsimp [p]; linarith
  have hM : 0 ≤ M := by
    exact (tsum_nonneg fun k => sq_nonneg (F k 0)).trans
      (hFenergy 0 ⟨le_rfl, hs.le⟩)
  have hR0 : 0 ≤ R := by
    dsimp [R]
    exact div_nonneg (Real.rpow_nonneg hs.le _) (by linarith)
  have hterm0 : ∀ k, 0 ≤
      (1 + lam k) ^ σ * (duhamelEnergyCoeff d F s k) ^ 2 := by
    intro k
    exact mul_nonneg (Real.rpow_nonneg (one_add_lam_pos k).le _)
      (sq_nonneg (duhamelEnergyCoeff d F s k))
  have hpartial : ∀ n : ℕ,
      ∑ k ∈ Finset.range n,
          (1 + lam k) ^ σ * (duhamelEnergyCoeff d F s k) ^ 2 ≤
        C ^ 2 * M * R ^ 2 := by
    intro n
    let G : ℝ → EuclideanSpace ℝ (Fin n) := fun τ =>
      WithLp.toLp 2 (fun i : Fin n =>
        (1 + lam i.1) ^ (σ / 2) *
          (lam i.1 ^ (1 / 2 : ℝ) * Real.exp (-(d * lam i.1 * (s - τ))) * F i.1 τ))
    have hGcont : Continuous G := by
      apply (PiLp.continuous_toLp 2 _).comp
      fun_prop
    have hGint : IntervalIntegrable G volume 0 s := hGcont.intervalIntegrable 0 s
    have hGnorm_int : IntervalIntegrable (fun τ => ‖G τ‖) volume 0 s :=
      hGcont.norm.intervalIntegrable 0 s
    have hslice (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) s) :
        ∑ i : Fin n, (F i.1 τ) ^ 2 ≤ M := by
      calc
        ∑ i : Fin n, (F i.1 τ) ^ 2 =
            ∑ k ∈ Finset.range n, (F k τ) ^ 2 :=
          Fin.sum_univ_eq_sum_range (fun k => (F k τ) ^ 2) n
        _ ≤ ∑' k, (F k τ) ^ 2 :=
          (hFsummable τ hτ).sum_le_tsum (Finset.range n)
            (fun k _ => sq_nonneg (F k τ))
        _ ≤ M := hFenergy τ hτ
    have hGnorm (τ : ℝ) (hτ : τ ∈ Set.Ioo (0 : ℝ) s) :
        ‖G τ‖ ≤ C * Real.sqrt M * (s - τ) ^ (-p) := by
      have hr : 0 < s - τ := by linarith [hτ.2]
      have hr1 : s - τ ≤ 1 := by linarith [hτ.1, hs1]
      have hq0 : 0 ≤ (s - τ) ^ (-p) := Real.rpow_nonneg hr.le _
      have hmode (i : Fin n) :
          |(1 + lam i.1) ^ (σ / 2) *
              (lam i.1 ^ (1 / 2 : ℝ) *
                Real.exp (-(d * lam i.1 * (s - τ))) * F i.1 τ)| ≤
            C * (s - τ) ^ (-p) * |F i.1 τ| := by
        have hmult := hC (s - τ) (lam i.1) hr hr1 (lam_nonneg i.1)
        have hexp0 : 0 ≤ Real.exp (-(d * lam i.1 * (s - τ))) :=
          (Real.exp_pos _).le
        have hsqrt0 : 0 ≤ lam i.1 ^ (1 / 2 : ℝ) :=
          Real.rpow_nonneg (lam_nonneg i.1) _
        have hw0 : 0 ≤ (1 + lam i.1) ^ (σ / 2) :=
          Real.rpow_nonneg (one_add_lam_pos i.1).le _
        have harg : d * (s - τ) * lam i.1 = d * lam i.1 * (s - τ) := by ring
        rw [harg] at hmult
        have hkernel0 : 0 ≤
            (1 + lam i.1) ^ (σ / 2) * lam i.1 ^ (1 / 2 : ℝ) *
              Real.exp (-(d * lam i.1 * (s - τ))) := by positivity
        have hmult' :
            (1 + lam i.1) ^ (σ / 2) * lam i.1 ^ (1 / 2 : ℝ) *
                Real.exp (-(d * lam i.1 * (s - τ))) ≤
              C * (s - τ) ^ (-p) := by
          simpa [C, p] using hmult
        calc
          |(1 + lam i.1) ^ (σ / 2) *
              (lam i.1 ^ (1 / 2 : ℝ) *
                Real.exp (-(d * lam i.1 * (s - τ))) * F i.1 τ)| =
              ((1 + lam i.1) ^ (σ / 2) * lam i.1 ^ (1 / 2 : ℝ) *
                Real.exp (-(d * lam i.1 * (s - τ)))) * |F i.1 τ| := by
                rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hw0,
                  abs_of_nonneg hsqrt0, abs_of_nonneg hexp0]
                ring
          _ ≤ (C * (s - τ) ^ (-p)) * |F i.1 τ| :=
            mul_le_mul_of_nonneg_right hmult' (abs_nonneg _)
      have hsq : ‖G τ‖ ^ 2 ≤ (C * (s - τ) ^ (-p)) ^ 2 * M := by
        rw [EuclideanSpace.real_norm_sq_eq]
        calc
          ∑ i : Fin n, (G τ i) ^ 2
              ≤ ∑ i : Fin n,
                  ((C * (s - τ) ^ (-p)) ^ 2 * (F i.1 τ) ^ 2) := by
                apply Finset.sum_le_sum
                intro i _
                have hi := pow_le_pow_left₀ (abs_nonneg _) (hmode i) 2
                simpa [G, sq_abs, mul_pow] using hi
          _ = (C * (s - τ) ^ (-p)) ^ 2 *
                ∑ i : Fin n, (F i.1 τ) ^ 2 := by rw [Finset.mul_sum]
          _ ≤ (C * (s - τ) ^ (-p)) ^ 2 * M := by
                exact mul_le_mul_of_nonneg_left
                  (hslice τ ⟨hτ.1.le, hτ.2.le⟩) (sq_nonneg _)
      have hsqrt0 : 0 ≤ Real.sqrt M := Real.sqrt_nonneg M
      have hright0 : 0 ≤ C * Real.sqrt M * (s - τ) ^ (-p) := by positivity
      have hsq' : ‖G τ‖ ^ 2 ≤
          (C * Real.sqrt M * (s - τ) ^ (-p)) ^ 2 := by
        calc
          ‖G τ‖ ^ 2 ≤ (C * (s - τ) ^ (-p)) ^ 2 * M := hsq
          _ = C ^ 2 * ((s - τ) ^ (-p)) ^ 2 * M := by ring
          _ = C ^ 2 * ((s - τ) ^ (-p)) ^ 2 * (Real.sqrt M) ^ 2 := by
            rw [Real.sq_sqrt hM]
          _ = (C * Real.sqrt M * (s - τ) ^ (-p)) ^ 2 := by ring
      nlinarith [norm_nonneg (G τ)]
    let H : ℝ → ℝ := fun τ => C * Real.sqrt M * (s - τ) ^ (-p)
    have hHint : IntervalIntegrable H volume 0 s := by
      exact (intervalIntegrable_reflected_singularity hp1 hs).const_mul
        (C * Real.sqrt M)
    have hmono : (∫ τ in (0 : ℝ)..s, ‖G τ‖) ≤ ∫ τ in (0 : ℝ)..s, H τ :=
      intervalIntegral.integral_mono_on_of_le_Ioo hs.le hGnorm_int hHint hGnorm
    have hHeval : (∫ τ in (0 : ℝ)..s, H τ) = C * Real.sqrt M * R := by
      dsimp [H]
      rw [intervalIntegral.integral_const_mul]
      rw [integral_reflected_singularity hp0 hp1 hs]
      have : 1 - p = (1 - σ) / 2 := by dsimp [p]; ring
      rw [this]
    let V : EuclideanSpace ℝ (Fin n) := ∫ τ in (0 : ℝ)..s, G τ
    have hVnorm : ‖V‖ ≤ C * Real.sqrt M * R := by
      calc
        ‖V‖ ≤ ∫ τ in (0 : ℝ)..s, ‖G τ‖ :=
          intervalIntegral.norm_integral_le_integral_norm hs.le
        _ ≤ ∫ τ in (0 : ℝ)..s, H τ := hmono
        _ = C * Real.sqrt M * R := hHeval
    have hVnorm_sq : ‖V‖ ^ 2 ≤ C ^ 2 * M * R ^ 2 := by
      have hright0 : 0 ≤ C * Real.sqrt M * R := by positivity
      calc
        ‖V‖ ^ 2 ≤ (C * Real.sqrt M * R) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg V) hVnorm 2
        _ = C ^ 2 * M * R ^ 2 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt hM]
    have hcoord (i : Fin n) :
        V i = (1 + lam i.1) ^ (σ / 2) * duhamelEnergyCoeff d F s i.1 := by
      have hproj :=
        (EuclideanSpace.proj (𝕜 := ℝ) i).intervalIntegral_comp_comm hGint
      change ((EuclideanSpace.proj (𝕜 := ℝ) i) V) = _
      rw [← hproj]
      simp only [G, EuclideanSpace.coe_proj]
      rw [intervalIntegral.integral_const_mul]
      rfl
    have hsum_eq :
        ∑ k ∈ Finset.range n,
            (1 + lam k) ^ σ * (duhamelEnergyCoeff d F s k) ^ 2 = ‖V‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      calc
        ∑ k ∈ Finset.range n,
            (1 + lam k) ^ σ * (duhamelEnergyCoeff d F s k) ^ 2 =
            ∑ i : Fin n,
              (1 + lam i.1) ^ σ * (duhamelEnergyCoeff d F s i.1) ^ 2 :=
          (Fin.sum_univ_eq_sum_range
            (fun k => (1 + lam k) ^ σ * (duhamelEnergyCoeff d F s k) ^ 2) n).symm
        _ = ∑ i : Fin n, (V i) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hcoord i, mul_pow]
          have hweight :
              (1 + lam i.1) ^ σ = ((1 + lam i.1) ^ (σ / 2)) ^ 2 := by
            rw [← Real.rpow_natCast ((1 + lam i.1) ^ (σ / 2)) 2,
              ← Real.rpow_mul (one_add_lam_pos i.1).le]
            norm_num
          rw [← hweight]
    exact hsum_eq.trans_le hVnorm_sq
  have hmem : MemHSigma σ (duhamelEnergyCoeff d F s) :=
    summable_of_sum_range_le hterm0 hpartial
  refine ⟨hmem, ?_⟩
  unfold hSigmaEnergy
  exact Real.tsum_le_of_sum_range_le hterm0 hpartial

#print axioms hSigmaEnergy_duhamel_bound_of_slice_l2

end ShenWork.Paper2.BFormHSigmaLinftyL2Smoothing
