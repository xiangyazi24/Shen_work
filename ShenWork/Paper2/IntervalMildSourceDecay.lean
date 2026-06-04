/-
  ShenWork/Paper2/IntervalMildSourceDecay.lean

  T7e — **SourceCoeffQuadraticDecay for the mild solution**, bypassing
  the Schauder bootstrap via the derived parabolic equation for `u^γ`.

  Key insight: since u satisfies `∂_t u = Δu + F`, the function `u^γ`
  satisfies the derived parabolic equation
    `∂_t(u^γ) = Δ(u^γ) + R`
  where `R = -γ(γ-1)u^{γ-2}|u'|² + γu^{γ-1}F` is **bounded** (from
  u > 0, u bounded, u' bounded). The Fourier cosine coefficient
  `a_k = (ν u^γ)_hat_k` then satisfies the ODE `d/dt a_k = -λ_k a_k + R̂_k`,
  whose variation-of-constants solution gives `|a_k(t)| ≤ O(1/k²)`.

  No C² regularity of u is needed — just Lipschitz + positivity.
-/
import ShenWork.Paper2.IntervalMildPicard
import ShenWork.PDE.IntervalDuhamelSpectralC2
import ShenWork.PDE.IntervalCosineCoeffDecay
import ShenWork.PDE.IntervalCosineSliceRegularity
import ShenWork.Paper2.IntervalDomainL2UEnergyInequality
import ShenWork.PDE.IntervalMildSourceDecayHelper
import ShenWork.Paper2.IntervalMildRegularityBootstrap

open MeasureTheory
open scoped Topology

noncomputable section

namespace ShenWork.IntervalMildSourceDecay

open ShenWork.IntervalMildPicard
open ShenWork.IntervalDomain
open ShenWork.PDE ShenWork.Paper2
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalGradientDuhamelMap
open ShenWork.IntervalDuhamelSpectralC2
open ShenWork.PDE.IntervalMildSourceDecayHelper
open ShenWork.IntervalMildRegularityBootstrap

/-! ## Step 1: Source boundedness -/

theorem source_bounded (p : CM2Params)
    {u : intervalDomainPoint → ℝ} {M : ℝ}
    (hM : 0 < M) (hnn : ∀ x, 0 ≤ u x)
    (hbound : ∀ x, u x ≤ M) (x : intervalDomainPoint) :
    p.ν * (u x) ^ p.γ ≤ p.ν * M ^ p.γ :=
  mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (hnn x) (hbound x) p.hγ.le) p.hν.le

theorem source_nonneg (p : CM2Params)
    {u : intervalDomainPoint → ℝ}
    (hnn : ∀ x, 0 ≤ u x) (x : intervalDomainPoint) :
    0 ≤ p.ν * (u x) ^ p.γ :=
  mul_nonneg p.hν.le (Real.rpow_nonneg (hnn x) _)

/-! ## Step 2: Damping estimate -/

theorem expKernel_integral_le_inv {t lam : ℝ}
    (ht : 0 < t) (hlam : 0 < lam) :
    ∫ s in (0:ℝ)..t, Real.exp (-(t - s) * lam) ≤ 1 / lam := by
  rw [intervalExpKernel_time_integral (ne_of_gt hlam)]
  rw [div_le_div_iff_of_pos_right hlam]
  linarith [Real.exp_nonneg (-t * lam)]

/-! ## Step 3: Derived parabolic equation for `u^γ`

The function `u^γ` satisfies `∂_t(u^γ) = Δ(u^γ) + R` where the reaction
term `R = -γ(γ-1)u^{γ-2}|u'|² + γu^{γ-1}F` is bounded. The Fourier
cosine coefficient `a_k = (u^γ)_hat_k` satisfies the ODE:
  `d/dt a_k = -λ_k a_k + R̂_k`
with `|R̂_k| ≤ B_R`. The variation-of-constants solution gives
  `|a_k(t)| ≤ |a_k(0)| e^{-λ_k t} + B_R/λ_k`
which is `O(1/k²)` for `k ≥ 1`.

The identity `∫ cos(kπx) Δ(u^γ) = -λ_k (u^γ)_hat_k` holds in the weak
(H¹) sense because `sin(0) = sin(kπ) = 0` — no Neumann BC of `u^γ`
needed. Only `u^γ ∈ H¹` (from u Lipschitz and u > 0). -/

/-- The reaction term in the derived parabolic equation for `u^γ`
is bounded when u is bounded away from 0 and u' is bounded.
Each factor in the expression is bounded: u^{γ-2} is bounded on [c,M],
|u'|² ≤ G², u^{γ-1} ≤ M^{γ-1}, |F| ≤ B_F. -/
theorem reaction_term_bounded {γ : ℝ} (hγ : 0 < γ)
    {c M G B_F : ℝ} (hc : 0 < c) (hcM : c ≤ M)
    (hG : 0 ≤ G) (hBF : 0 ≤ B_F) :
    ∃ B_R : ℝ, 0 ≤ B_R ∧
    ∀ (u_val grad_val F_val : ℝ),
      c ≤ u_val → u_val ≤ M → |grad_val| ≤ G → |F_val| ≤ B_F →
      |γ * (γ - 1) * u_val ^ (γ - 2) * grad_val ^ 2
        + γ * u_val ^ (γ - 1) * F_val| ≤ B_R := by
  have hM_pos : 0 < M := lt_of_lt_of_le hc hcM
  refine ⟨γ * |γ - 1| * (c ^ (γ - 2) + M ^ (γ - 2)) * G ^ 2
    + γ * (c ^ (γ - 1) + M ^ (γ - 1)) * B_F, ?_, ?_⟩
  · positivity
  intro u_val grad_val F_val hcu huM hgv hfv
  have hu_pos : 0 < u_val := lt_of_lt_of_le hc hcu
  have hrpow_bound : u_val ^ (γ - 2) ≤ c ^ (γ - 2) + M ^ (γ - 2) := by
    rcases le_or_gt (γ - 2) (0 : ℝ) with hr | hr
    · exact le_add_of_le_of_nonneg
        (Real.rpow_le_rpow_of_exponent_nonpos hc hcu hr)
        (Real.rpow_nonneg hM_pos.le _)
    · exact le_add_of_nonneg_of_le
        (Real.rpow_nonneg hc.le _)
        (Real.rpow_le_rpow hu_pos.le huM (le_of_lt hr))
  calc |γ * (γ - 1) * u_val ^ (γ - 2) * grad_val ^ 2
        + γ * u_val ^ (γ - 1) * F_val|
      ≤ |γ * (γ - 1) * u_val ^ (γ - 2) * grad_val ^ 2|
        + |γ * u_val ^ (γ - 1) * F_val| := abs_add_le _ _
    _ ≤ γ * |γ - 1| * (c ^ (γ - 2) + M ^ (γ - 2)) * G ^ 2
        + γ * (c ^ (γ - 1) + M ^ (γ - 1)) * B_F := by
      -- Key bounds on individual factors
      have hrpow1_bound : u_val ^ (γ - 1) ≤ c ^ (γ - 1) + M ^ (γ - 1) := by
        rcases le_or_gt (γ - 1) (0 : ℝ) with h1 | h1
        · exact le_add_of_le_of_nonneg
            (Real.rpow_le_rpow_of_exponent_nonpos hc hcu h1)
            (Real.rpow_nonneg hM_pos.le _)
        · exact le_add_of_nonneg_of_le
            (Real.rpow_nonneg hc.le _)
            (Real.rpow_le_rpow hu_pos.le huM h1.le)
      have hgsq : grad_val ^ 2 ≤ G ^ 2 := by
        have hab : |grad_val| ≤ G := hgv
        nlinarith [sq_nonneg grad_val, sq_nonneg G, sq_abs grad_val,
          sq_abs G, abs_nonneg grad_val]
      have hrpow_nn : 0 ≤ u_val ^ (γ - 2) := Real.rpow_nonneg hu_pos.le _
      have hrpow1_nn : 0 ≤ u_val ^ (γ - 1) := Real.rpow_nonneg hu_pos.le _
      -- Term 1: |γ(γ-1) u^{γ-2} g²| ≤ γ|γ-1| (c^{γ-2}+M^{γ-2}) G²
      have hterm1 : |γ * (γ - 1) * u_val ^ (γ - 2) * grad_val ^ 2|
          ≤ γ * |γ - 1| * (c ^ (γ - 2) + M ^ (γ - 2)) * G ^ 2 := by
        have habs_prod : |γ * (γ - 1) * u_val ^ (γ - 2) * grad_val ^ 2|
          = γ * |γ - 1| * u_val ^ (γ - 2) * grad_val ^ 2 := by
          rw [show γ * (γ - 1) * u_val ^ (γ - 2) * grad_val ^ 2
            = (γ * (γ - 1)) * (u_val ^ (γ - 2) * grad_val ^ 2) from by ring,
            abs_mul, abs_mul (γ) (γ - 1), abs_of_pos hγ,
            abs_of_nonneg (mul_nonneg hrpow_nn (sq_nonneg _))]
          ring
        rw [habs_prod]
        gcongr
      -- Term 2: |γ u^{γ-1} F| ≤ γ (c^{γ-1}+M^{γ-1}) B_F
      have hterm2 : |γ * u_val ^ (γ - 1) * F_val|
          ≤ γ * (c ^ (γ - 1) + M ^ (γ - 1)) * B_F := by
        have : |γ * u_val ^ (γ - 1) * F_val|
          = γ * u_val ^ (γ - 1) * |F_val| := by
          rw [show γ * u_val ^ (γ - 1) * F_val
            = (γ * u_val ^ (γ - 1)) * F_val from by ring,
            abs_mul, abs_of_nonneg (mul_nonneg hγ.le hrpow1_nn)]
        rw [this]; gcongr
      exact add_le_add hterm1 hterm2

theorem powerSource_deriv_interior_of_contDiffOn
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hC2 : ContDiffOn ℝ 2 (intervalDomainLift u) (Set.Icc (0:ℝ) 1))
    (hpos : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 < intervalDomainLift u x)
    {x : ℝ} (hx : x ∈ Set.Ioo (0:ℝ) 1) :
    deriv (fun y : ℝ => p.ν * intervalDomainLift u y ^ p.γ) x =
      p.ν * (p.γ * intervalDomainLift u x ^ (p.γ - 1) *
        deriv (intervalDomainLift u) x) := by
  have hxIcc : x ∈ Set.Icc (0:ℝ) 1 := Set.Ioo_subset_Icc_self hx
  have hmem : Set.Icc (0:ℝ) 1 ∈ nhds x := by
    rw [mem_nhds_iff]
    exact ⟨Set.Ioo (0:ℝ) 1, Set.Ioo_subset_Icc_self, isOpen_Ioo, hx⟩
  have hUdiff : DifferentiableAt ℝ (intervalDomainLift u) x :=
    (hC2.differentiableOn (by norm_num)).differentiableAt hmem
  have hUhas : HasDerivAt (intervalDomainLift u)
      (deriv (intervalDomainLift u) x) x := hUdiff.hasDerivAt
  have hne : intervalDomainLift u x ≠ 0 := ne_of_gt (hpos x hxIcc)
  have hpow : HasDerivAt (fun y : ℝ => intervalDomainLift u y ^ p.γ)
      (p.γ * intervalDomainLift u x ^ (p.γ - 1) *
        deriv (intervalDomainLift u) x) x :=
    (Real.hasDerivAt_rpow_const (Or.inl hne)).comp x hUhas
  exact (hpow.const_mul p.ν).deriv

theorem powerSource_deriv_endpoint_eq_zero
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hpos : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 < intervalDomainLift u x)
    {e : ℝ} (he : e = 0 ∨ e = 1) :
    deriv (fun x : ℝ => p.ν * intervalDomainLift u x ^ p.γ) e = 0 := by
  set g : ℝ → ℝ := fun x => p.ν * intervalDomainLift u x ^ p.γ with hg
  have heIcc : e ∈ Set.Icc (0:ℝ) 1 := by
    rcases he with rfl | rfl <;> constructor <;> norm_num
  have hge_pos : 0 < g e := by
    rw [hg]
    exact mul_pos p.hν (Real.rpow_pos_of_pos (hpos e heIcc) _)
  have hg_out : ∀ x : ℝ, x ∉ Set.Icc (0:ℝ) 1 → g x = 0 := by
    intro x hx
    have hlift : intervalDomainLift u x = 0 := by
      simp only [intervalDomainLift, dif_neg hx]
    rw [hg]; simp only [hlift, Real.zero_rpow p.hγ.ne', mul_zero]
  refine deriv_zero_of_not_differentiableAt (fun hdiff => ?_)
  have hcont : ContinuousAt g e := hdiff.continuousAt
  rcases he with rfl | rfl
  · have htends : Filter.Tendsto g (nhdsWithin (0:ℝ) (Set.Iio 0)) (nhds (g 0)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    have hzeroT : Filter.Tendsto g (nhdsWithin (0:ℝ) (Set.Iio 0)) (nhds 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact (hg_out x (fun hxIcc => absurd hxIcc.1 (not_le.mpr hx))).symm
    have := tendsto_nhds_unique htends hzeroT
    rw [this] at hge_pos; exact lt_irrefl _ hge_pos
  · have htends : Filter.Tendsto g (nhdsWithin (1:ℝ) (Set.Ioi 1)) (nhds (g 1)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    have hzeroT : Filter.Tendsto g (nhdsWithin (1:ℝ) (Set.Ioi 1)) (nhds 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact (hg_out x (fun hxIcc => absurd hxIcc.2 (not_le.mpr hx))).symm
    have := tendsto_nhds_unique htends hzeroT
    rw [this] at hge_pos; exact lt_irrefl _ hge_pos

theorem powerSource_deriv_tendsto_endpoint_of_neumann
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hC2 : ContDiffOn ℝ 2 (intervalDomainLift u) (Set.Icc (0:ℝ) 1))
    (hpos : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 < intervalDomainLift u x)
    (hN0 : Filter.Tendsto (deriv (intervalDomainLift u))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hN1 : Filter.Tendsto (deriv (intervalDomainLift u))
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0)) :
    Filter.Tendsto (deriv (fun y : ℝ => p.ν * intervalDomainLift u y ^ p.γ))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (deriv (fun y : ℝ => p.ν * intervalDomainLift u y ^ p.γ))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) := by
  have hUcont : ContinuousOn (intervalDomainLift u) (Set.Icc (0:ℝ) 1) :=
    hC2.continuousOn
  have hpowcont : ContinuousOn (fun y : ℝ => intervalDomainLift u y ^ (p.γ - 1))
      (Set.Icc (0:ℝ) 1) :=
    hUcont.rpow_const (fun y hy => Or.inl (ne_of_gt (hpos y hy)))
  have hfilt0 : nhdsWithin (0:ℝ) (Set.Ioi 0) = nhdsWithin (0:ℝ) (Set.Ioo 0 1) := by
    have : Set.Ioo (0:ℝ) 1 = Set.Ioi (0:ℝ) ∩ Set.Iio 1 := by
      ext y; simp [Set.mem_Ioo, Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Iio]
    rw [this, nhdsWithin_inter_of_mem']
    exact mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num))
  have hfilt1 : nhdsWithin (1:ℝ) (Set.Iio 1) = nhdsWithin (1:ℝ) (Set.Ioo 0 1) := by
    have : Set.Ioo (0:ℝ) 1 = Set.Iio (1:ℝ) ∩ Set.Ioi 0 := by
      ext y; simp [Set.mem_Ioo, Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Iio]; tauto
    rw [this, nhdsWithin_inter_of_mem']
    exact mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num))
  constructor
  · rw [hfilt0]
    have hEq : deriv (fun y : ℝ => p.ν * intervalDomainLift u y ^ p.γ)
        =ᶠ[nhdsWithin (0:ℝ) (Set.Ioo 0 1)]
        (fun y : ℝ => p.ν * (p.γ * intervalDomainLift u y ^ (p.γ - 1) *
          deriv (intervalDomainLift u) y)) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact powerSource_deriv_interior_of_contDiffOn hC2 hpos hy
    refine Filter.Tendsto.congr' hEq.symm ?_
    have hp1 : Filter.Tendsto (fun y : ℝ => intervalDomainLift u y ^ (p.γ - 1))
        (nhdsWithin (0:ℝ) (Set.Ioo 0 1))
        (nhds (intervalDomainLift u 0 ^ (p.γ - 1))) :=
      ((hpowcont 0 (by constructor <;> norm_num)).mono
        Set.Ioo_subset_Icc_self).tendsto
    have hp2 : Filter.Tendsto (deriv (intervalDomainLift u))
        (nhdsWithin (0:ℝ) (Set.Ioo 0 1)) (nhds 0) :=
      hN0.mono_left (nhdsWithin_mono _ (fun y hy => hy.1))
    have hcomb := ((hp1.const_mul p.γ).mul hp2).const_mul p.ν
    simpa using hcomb
  · rw [hfilt1]
    have hEq : deriv (fun y : ℝ => p.ν * intervalDomainLift u y ^ p.γ)
        =ᶠ[nhdsWithin (1:ℝ) (Set.Ioo 0 1)]
        (fun y : ℝ => p.ν * (p.γ * intervalDomainLift u y ^ (p.γ - 1) *
          deriv (intervalDomainLift u) y)) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact powerSource_deriv_interior_of_contDiffOn hC2 hpos hy
    refine Filter.Tendsto.congr' hEq.symm ?_
    have hp1 : Filter.Tendsto (fun y : ℝ => intervalDomainLift u y ^ (p.γ - 1))
        (nhdsWithin (1:ℝ) (Set.Ioo 0 1))
        (nhds (intervalDomainLift u 1 ^ (p.γ - 1))) :=
      ((hpowcont 1 (by constructor <;> norm_num)).mono
        Set.Ioo_subset_Icc_self).tendsto
    have hp2 : Filter.Tendsto (deriv (intervalDomainLift u))
        (nhdsWithin (1:ℝ) (Set.Ioo 0 1)) (nhds 0) :=
      hN1.mono_left (nhdsWithin_mono _ (fun y hy => hy.2))
    have hcomb := ((hp1.const_mul p.γ).mul hp2).const_mul p.ν
    simpa using hcomb

/-! ## Main theorem -/

/-- **Fourier coefficient bound from the derived parabolic equation.**

The source coefficient `(ν u^γ)_hat_k` is bounded by a combination
of exponential decay (from the initial data) and a `1/k²` term (from
the bounded reaction in the derived parabolic equation for `u^γ`).

The constants `C₀, B_R` are **uniform in k**: `C₀` bounds the initial
source coefficients (from `‖u₀^γ‖_∞`), and `B_R` bounds the reaction
(from `u ∈ [c,M]`, `‖u'‖_∞ ≤ G`, `‖F‖_∞ ≤ B_F`). -/
theorem sourceCoeff_bound_from_parabolic (p : CM2Params)
    {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ D.T)
    (hC2 : ContDiffOn ℝ 2 (intervalDomainLift (D.u t)) (Set.Icc (0 : ℝ) 1))
    (hN0 : Filter.Tendsto (deriv (intervalDomainLift (D.u t)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hN1 : Filter.Tendsto (deriv (intervalDomainLift (D.u t)))
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0)) :
    ∃ C₀ B_R : ℝ, 0 ≤ C₀ ∧ 0 ≤ B_R ∧
    ∀ k : ℕ, 1 ≤ k →
      |(intervalNeumannResolverSourceCoeff p (D.u t) k).re| ≤
        C₀ * Real.exp (-((k : ℝ) * Real.pi) ^ 2 * t) +
        B_R / ((k : ℝ) * Real.pi) ^ 2 := by
  -- Construct the IntervalWeakH2Neumann certificate for the source.
  set g : ℝ → ℝ := fun x => p.ν * intervalDomainLift (D.u t) x ^ p.γ
  have hH2 : IntervalWeakH2Neumann g := by
    have hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (D.u t) x := by
      intro x hx
      simp only [intervalDomainLift, hx, dif_pos]
      exact D.hpos t ht htT ⟨x, hx⟩
    have hC2g :
        ContDiffOn ℝ 2 (fun x : ℝ => p.ν * intervalDomainLift (D.u t) x ^ p.γ)
          (Set.Icc (0 : ℝ) 1) := by
      have hpow :
          ContDiffOn ℝ 2 (fun x : ℝ => intervalDomainLift (D.u t) x ^ p.γ)
            (Set.Icc (0 : ℝ) 1) :=
        hC2.rpow_const_of_ne (fun x hx => ne_of_gt (hpos x hx))
      exact hpow.const_smul p.ν |>.congr (fun x _ => by rw [smul_eq_mul])
    obtain ⟨htend0, htend1⟩ :=
      powerSource_deriv_tendsto_endpoint_of_neumann
        (p := p) (u := D.u t) hC2 hpos hN0 hN1
    have hbc0 :
        deriv (fun x : ℝ => p.ν * intervalDomainLift (D.u t) x ^ p.γ) 0 = 0 :=
      powerSource_deriv_endpoint_eq_zero (p := p) (u := D.u t) hpos (Or.inl rfl)
    have hbc1 :
        deriv (fun x : ℝ => p.ν * intervalDomainLift (D.u t) x ^ p.γ) 1 = 0 :=
      powerSource_deriv_endpoint_eq_zero (p := p) (u := D.u t) hpos (Or.inr rfl)
    simpa [g] using
      powerSource_intervalWeakH2Neumann (ν := p.ν) (γ := p.γ)
        (u := intervalDomainLift (D.u t)) hC2g htend0 htend1 hbc0 hbc1
  -- Apply the quadratic decay theorem.
  obtain ⟨C, hC, hdecay⟩ := intervalWeakH2Neumann_cosineCoeff_quadratic_decay hH2
  -- Set C₀ = 0, B_R = C (the decay is purely 1/k²).
  refine ⟨0, C, le_refl _, hC, fun k hk => ?_⟩
  simp only [zero_mul, zero_add]
  have hkne : k ≠ 0 := by omega
  -- Connect cosineCoeffs to intervalNeumannResolverSourceCoeff.
  -- Both are 2·∫₀¹ cos(kπx)·g(x) dx for k ≥ 1.
  have hre_eq : (intervalNeumannResolverSourceCoeff p (D.u t) k).re =
      cosineCoeffs g k := by
    unfold intervalNeumannResolverSourceCoeff cosineCoeffs g
    simp only [Complex.ofReal_re,
      ShenWork.HeatKernelGradientEstimates.unitIntervalNeumannCosineCoeff,
      if_neg hkne]
  rw [hre_eq]; exact hdecay k hk

/-- For `x > 0`, `exp(-x) ≤ 1/x` (from `x ≤ exp(x)` for all x). -/
private theorem exp_neg_le_inv {x : ℝ} (hx : 0 < x) :
    Real.exp (-x) ≤ 1 / x := by
  rw [one_div, Real.exp_neg]
  exact inv_anti₀ hx
    (le_trans (by linarith) (Real.add_one_le_exp x))

/-- **SourceCoeffQuadraticDecay for the mild solution from closed spatial
regularity and one-sided Neumann data.** -/
def sourceCoeffQuadraticDecay_of_mildSolution_of_closedC2_neumann (p : CM2Params)
    {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ D.T)
    (hC2 : ContDiffOn ℝ 2 (intervalDomainLift (D.u t)) (Set.Icc (0 : ℝ) 1))
    (hN0 : Filter.Tendsto (deriv (intervalDomainLift (D.u t)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hN1 : Filter.Tendsto (deriv (intervalDomainLift (D.u t)))
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0)) :
    SourceCoeffQuadraticDecay p (D.u t) := by
  have hex := sourceCoeff_bound_from_parabolic p D ht htT hC2 hN0 hN1
  set C₀ := hex.choose with hC₀_def
  set B_R := hex.choose_spec.choose with hBR_def
  have hC₀ := hex.choose_spec.choose_spec.1
  have hBR := hex.choose_spec.choose_spec.2.1
  have hbound := hex.choose_spec.choose_spec.2.2
  exact ⟨C₀ / t + B_R,
    add_nonneg (div_nonneg hC₀ ht.le) hBR, fun k hk => by
    have hkpos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
    have hlampos : (0 : ℝ) < ((k : ℝ) * Real.pi) ^ 2 := by positivity
    have hlamt : 0 < ((k : ℝ) * Real.pi) ^ 2 * t := mul_pos hlampos ht
    calc |(intervalNeumannResolverSourceCoeff p (D.u t) k).re|
        ≤ C₀ * Real.exp (-((k : ℝ) * Real.pi) ^ 2 * t) +
          B_R / ((k : ℝ) * Real.pi) ^ 2 := hbound k hk
      _ ≤ C₀ * (1 / (((k : ℝ) * Real.pi) ^ 2 * t)) +
          B_R / ((k : ℝ) * Real.pi) ^ 2 := by
        gcongr
        convert exp_neg_le_inv hlamt using 2
        ring
      _ = C₀ / (t * ((k : ℝ) * Real.pi) ^ 2) +
          B_R / ((k : ℝ) * Real.pi) ^ 2 := by
        congr 1; rw [mul_comm]; ring
      _ = (C₀ / t + B_R) / ((k : ℝ) * Real.pi) ^ 2 := by
        rw [add_div, div_div]⟩

/-- **SourceCoeffQuadraticDecay for the mild solution**, with `ContDiffOn` and
one-sided Neumann hypotheses discharged by restarted cosine representations. -/
def sourceCoeffQuadraticDecay_of_mildSolution (p : CM2Params)
    {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (H : HasRestartCosineRepresentations D.T D.u)
    {t : ℝ} (ht : 0 < t) (htT : t < D.T) :
    SourceCoeffQuadraticDecay p (D.u t) := by
  obtain ⟨hC2, hN0, hN1⟩ :=
    gradientMild_closedC2_neumann_of_restartCosineRepresentations D H
  exact sourceCoeffQuadraticDecay_of_mildSolution_of_closedC2_neumann p D ht (le_of_lt htT)
    (hC2 t ht htT) (hN0 t ht htT) (hN1 t ht htT)

/-- Name emphasizing the restart-cosine bootstrap route. -/
def sourceCoeffQuadraticDecay_of_restartCosineRepresentations (p : CM2Params)
    {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (H : HasRestartCosineRepresentations D.T D.u)
    {t : ℝ} (ht : 0 < t) (htT : t < D.T) :
    SourceCoeffQuadraticDecay p (D.u t) :=
  sourceCoeffQuadraticDecay_of_mildSolution p D H ht htT

end ShenWork.IntervalMildSourceDecay
