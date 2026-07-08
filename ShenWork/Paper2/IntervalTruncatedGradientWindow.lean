/-
  Small-window Lipschitz contraction for truncated 1D Keller-Segel iterates.

  The iterate gradient recurrence on a positive window [lo, hi] with restart a < lo:
    G_{n+1} ≤ Cg*M/√(lo-a) + 2*Cg*√(hi-a) * (A_L + |χ₀|*(A_F + B_F*G_n))
           = A_win + B_win * G_n

  For short enough windows (B_win < 1), the fixed point G = A_win/(1-B_win)
  is an invariant envelope for all iterates.
-/

import ShenWork.Paper2.IntervalPicardIterateUniform
import ShenWork.Paper2.IntervalBFormCron2TruncatedPicard
import ShenWork.PDE.IntervalGradDuhamelBound

open MeasureTheory Set
open scoped BigOperators Topology Real

noncomputable section

namespace ShenWork.Paper2.TruncatedGradientWindow

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.HeatKernelGradientEstimates
  (heatGradientLinftyLinftyConstant heatGradientLinftyLinftyConstant_nonneg)

def truncWindowSourceCL (A_L A_F B_F χ G : ℝ) : ℝ :=
  A_L + |χ| * (A_F + B_F * G)

def truncWindowA (M A_L A_F χ a lo hi : ℝ) : ℝ :=
  heatGradientLinftyLinftyConstant / Real.sqrt (lo - a) * M
    + heatGradientLinftyLinftyConstant * (2 * Real.sqrt (hi - a))
        * (A_L + |χ| * A_F)

def truncWindowB (B_F χ a hi : ℝ) : ℝ :=
  heatGradientLinftyLinftyConstant * (2 * Real.sqrt (hi - a)) * |χ| * B_F

def truncWindowAffine
    (M A_L A_F B_F χ a lo hi G : ℝ) : ℝ :=
  truncWindowA M A_L A_F χ a lo hi
    + truncWindowB B_F χ a hi * G

def truncWindowFixedG (M A_L A_F B_F χ a lo hi : ℝ) : ℝ :=
  truncWindowA M A_L A_F χ a lo hi /
    (1 - truncWindowB B_F χ a hi)

theorem affine_fixed_closes {A B : ℝ} (hB : B < 1) :
    A + B * (A / (1 - B)) ≤ A / (1 - B) := by
  have hden_pos : 0 < 1 - B := sub_pos.mpr hB
  have hden_ne : 1 - B ≠ 0 := ne_of_gt hden_pos
  have hEq : A + B * (A / (1 - B)) = A / (1 - B) := by
    field_simp [hden_ne]
    ring
  exact le_of_eq hEq

abbrev IterGradOnWindow
    (U : ℕ → ℝ → intervalDomainPoint → ℝ)
    (lo hi : ℝ) (n : ℕ) (G : ℝ) : Prop :=
  ∀ t, lo ≤ t → t ≤ hi → ∀ x : ℝ,
    |deriv (intervalDomainLift (U n t)) x| ≤ G

theorem IterGradOnWindow.mono
    {U : ℕ → ℝ → intervalDomainPoint → ℝ}
    {lo hi : ℝ} {n : ℕ} {G₁ G₂ : ℝ}
    (hG : G₁ ≤ G₂) (H : IterGradOnWindow U lo hi n G₁) :
    IterGradOnWindow U lo hi n G₂ := by
  intro t htlo hthi x
  exact (H t htlo hthi x).trans hG

theorem IterGradOnWindow.glue_left
    {U : ℕ → ℝ → intervalDomainPoint → ℝ}
    {a lo hi G : ℝ} {n : ℕ}
    (Hleft : IterGradOnWindow U a lo n G)
    (Hright : IterGradOnWindow U lo hi n G) :
    IterGradOnWindow U a hi n G := by
  intro t hta hthi x
  by_cases htlo : t ≤ lo
  · exact Hleft t hta htlo x
  · have hlot : lo ≤ t := le_of_lt (lt_of_not_ge htlo)
    exact Hright t hlot hthi x

theorem abs_logistic_sub_chi_flux_le
    {L Fp A_L A_F B_F χ G : ℝ}
    (hL : |L| ≤ A_L)
    (hF : |Fp| ≤ A_F + B_F * G) :
    |L - χ * Fp| ≤ truncWindowSourceCL A_L A_F B_F χ G := by
  unfold truncWindowSourceCL
  calc
    |L - χ * Fp| ≤ |L| + |χ * Fp| := by
      simpa using (abs_sub_le L 0 (χ * Fp))
    _ = |L| + |χ| * |Fp| := by rw [abs_mul]
    _ ≤ A_L + |χ| * (A_F + B_F * G) := by
      exact add_le_add hL (mul_le_mul_of_nonneg_left hF (abs_nonneg χ))

structure TruncatedGradientWindowWiring
    (p : CM2Params)
    (U : ℕ → ℝ → intervalDomainPoint → ℝ)
    (Src : ℕ → ℝ → ℝ → ℝ)
    (M A_L A_F B_F a lo hi G : ℝ) : Prop where
  hM_nonneg : 0 ≤ M
  hAL_nonneg : 0 ≤ A_L
  hAF_nonneg : 0 ≤ A_F
  hBF_nonneg : 0 ≤ B_F
  hG_nonneg : 0 ≤ G
  ha_lt_lo : a < lo
  hlo_le_hi : lo ≤ hi
  hclosed : truncWindowAffine M A_L A_F B_F p.χ₀ a lo hi G ≤ G
  hleft : ∀ n : ℕ, IterGradOnWindow U a lo n G
  hbase : IterGradOnWindow U lo hi 0 G
  hsource_of_grad : ∀ n : ℕ,
    IterGradOnWindow U a hi n G →
      ∀ s, a ≤ s → s ≤ hi → ∀ y : ℝ,
        |Src n s y| ≤ truncWindowSourceCL A_L A_F B_F p.χ₀ G
  hkernel_step : ∀ n : ℕ,
    (∀ s, a ≤ s → s ≤ hi → ∀ y : ℝ,
      |Src n s y| ≤ truncWindowSourceCL A_L A_F B_F p.χ₀ G) →
      IterGradOnWindow U lo hi (n + 1)
        (truncWindowAffine M A_L A_F B_F p.χ₀ a lo hi G)

theorem truncatedGradientWindow_succ
    {p : CM2Params}
    {U : ℕ → ℝ → intervalDomainPoint → ℝ}
    {Src : ℕ → ℝ → ℝ → ℝ}
    {M A_L A_F B_F a lo hi G : ℝ}
    (W : TruncatedGradientWindowWiring p U Src M A_L A_F B_F a lo hi G)
    {n : ℕ}
    (IH : IterGradOnWindow U lo hi n G) :
    IterGradOnWindow U lo hi (n + 1) G := by
  have HsrcInterval : IterGradOnWindow U a hi n G :=
    IterGradOnWindow.glue_left (W.hleft n) IH
  have Hsrc := W.hsource_of_grad n HsrcInterval
  have Hraw := W.hkernel_step n Hsrc
  exact IterGradOnWindow.mono W.hclosed Hraw

theorem truncatedGradientWindow_all
    {p : CM2Params}
    {U : ℕ → ℝ → intervalDomainPoint → ℝ}
    {Src : ℕ → ℝ → ℝ → ℝ}
    {M A_L A_F B_F a lo hi G : ℝ}
    (W : TruncatedGradientWindowWiring p U Src M A_L A_F B_F a lo hi G) :
    ∀ n : ℕ, IterGradOnWindow U lo hi n G := by
  intro n
  induction n with
  | zero => exact W.hbase
  | succ n IH => exact truncatedGradientWindow_succ W IH

/-! ## Shifted Duhamel gradient bound

The gradient window uses a restart at time `a`. The Duhamel integral runs over
`[a, t]`, which reduces to `[0, t-a]` after a shift. This wrapper applies the
existing `gradDuhamel_sup_bound` to the shifted source. -/

open ShenWork.IntervalDomain (intervalMeasure)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)

theorem gradDuhamel_shifted_sup_bound
    {a t T : ℝ} (ha : 0 ≤ a) (hat : a < t) (htT : t ≤ T)
    {q : ℝ → ℝ → ℝ}
    (hq_int : ∀ s, Integrable (q s) (intervalMeasure 1))
    {Cq : ℝ} (hCq : 0 ≤ Cq) (hq_sup : ∀ s y, |q s y| ≤ Cq) (x : ℝ)
    (hg_int : IntervalIntegrable
      (fun s : ℝ => deriv
        (fun z : ℝ => intervalFullSemigroupOperator (t - s) (q s) z) x) volume a t) :
    |∫ s in a..t, deriv
        (fun z : ℝ => intervalFullSemigroupOperator (t - s) (q s) z) x|
      ≤ heatGradientLinftyLinftyConstant * (2 * Real.sqrt (T - a)) * Cq := by
  set Cg := heatGradientLinftyLinftyConstant with hCgdef
  have hCgnn : 0 ≤ Cg := by
    simpa [hCgdef] using heatGradientLinftyLinftyConstant_nonneg
  have hat_le : a ≤ t := le_of_lt hat
  have hTa : t - a ≤ T - a := by linarith
  have hptw : ∀ s ∈ Set.Ioo a t,
      |deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) (q s) z) x|
        ≤ Cg * Cq * (t - s) ^ (-(1 / 2) : ℝ) := by
    intro s hs
    have hs0 : 0 ≤ s := le_trans ha hs.1.le
    have h :=
      ShenWork.IntervalNeumannFullKernel.intervalFullCoupledDuhamel_grad_integrand_pointwise_bound
        (t := t) (s := s) hs0 hs.2 (F := q s) (hq_int s)
        (C_source := Cq) hCq (hq_sup s) x
    calc
      |deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) (q s) z) x|
          ≤ Cg * (t - s) ^ (-(1 / 2) : ℝ) * Cq := by
            simpa [hCgdef] using h
      _ = Cg * Cq * (t - s) ^ (-(1 / 2) : ℝ) := by ring
  have hsing_int : IntervalIntegrable
      (fun s : ℝ => (t - s) ^ (-(1 / 2) : ℝ)) volume a t := by
    have h0 : IntervalIntegrable
        (fun u : ℝ => u ^ (-(1 / 2) : ℝ)) volume 0 (t - a) :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    have h := (h0.comp_sub_left t).symm
    simpa using h
  have hdom_int : IntervalIntegrable
      (fun s : ℝ => Cg * Cq * (t - s) ^ (-(1 / 2) : ℝ)) volume a t :=
    hsing_int.const_mul (Cg * Cq)
  have hsing_eq :
      (∫ s in a..t, (t - s) ^ (-(1 / 2) : ℝ)) =
        2 * Real.sqrt (t - a) := by
    rw [intervalIntegral.integral_comp_sub_left
      (fun u : ℝ => u ^ (-(1 / 2) : ℝ)) t]
    simp only [sub_self]
    rw [intervalIntegral.integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2)))]
    have hexp : (-(1 / 2) : ℝ) + 1 = 1 / 2 := by norm_num
    rw [hexp, Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0), sub_zero,
      Real.sqrt_eq_rpow]
    rw [div_eq_iff (by norm_num : (1 / 2 : ℝ) ≠ 0)]
    ring
  have hmono :
      ∫ s in a..t,
          |deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) (q s) z) x|
        ≤ ∫ s in a..t, Cg * Cq * (t - s) ^ (-(1 / 2) : ℝ) := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo hat_le hg_int.abs hdom_int ?_
    intro s hs
    exact hptw s hs
  calc
    |∫ s in a..t, deriv
        (fun z : ℝ => intervalFullSemigroupOperator (t - s) (q s) z) x|
        ≤ ∫ s in a..t,
            |deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) (q s) z) x| :=
      intervalIntegral.abs_integral_le_integral_abs hat_le
    _ ≤ ∫ s in a..t, Cg * Cq * (t - s) ^ (-(1 / 2) : ℝ) := hmono
    _ = Cg * Cq * (2 * Real.sqrt (t - a)) := by
      rw [intervalIntegral.integral_const_mul, hsing_eq]
    _ ≤ Cg * (2 * Real.sqrt (T - a)) * Cq := by
      have hsqrt : 2 * Real.sqrt (t - a) ≤ 2 * Real.sqrt (T - a) := by
        have hbase : Real.sqrt (t - a) ≤ Real.sqrt (T - a) :=
          Real.sqrt_le_sqrt hTa
        nlinarith
      calc
        Cg * Cq * (2 * Real.sqrt (t - a))
            ≤ Cg * Cq * (2 * Real.sqrt (T - a)) :=
          mul_le_mul_of_nonneg_left hsqrt (mul_nonneg hCgnn hCq)
        _ = Cg * (2 * Real.sqrt (T - a)) * Cq := by ring

end ShenWork.Paper2.TruncatedGradientWindow
