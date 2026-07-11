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

/-- Short-window contraction: since `truncWindowB ∝ √(hi−a)`, a short enough window makes the
contraction coefficient `< 1`.  The hypothesis is the definitional product regrouped so a caller can
choose the window length `hi − a` small against the fixed constants `Cg·2|χ|·B_F`. -/
theorem truncWindowB_lt_one_of_sqrt_prod {B_F χ a hi : ℝ}
    (hprod :
      heatGradientLinftyLinftyConstant * (2 * (|χ| * B_F)) * Real.sqrt (hi - a) < 1) :
    truncWindowB B_F χ a hi < 1 := by
  unfold truncWindowB
  calc
    heatGradientLinftyLinftyConstant * (2 * Real.sqrt (hi - a)) * |χ| * B_F
        = heatGradientLinftyLinftyConstant * (2 * (|χ| * B_F)) * Real.sqrt (hi - a) := by ring
    _ < 1 := hprod

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
  ∀ t, lo ≤ t → t ≤ hi →
    (∀ x : ℝ, |deriv (intervalDomainLift (U n t)) x| ≤ G) ∧
      ∀ x ∈ Set.Ioo (0 : ℝ) 1,
        DifferentiableAt ℝ (intervalDomainLift (U n t)) x

theorem IterGradOnWindow.mono
    {U : ℕ → ℝ → intervalDomainPoint → ℝ}
    {lo hi : ℝ} {n : ℕ} {G₁ G₂ : ℝ}
    (hG : G₁ ≤ G₂) (H : IterGradOnWindow U lo hi n G₁) :
    IterGradOnWindow U lo hi n G₂ := by
  intro t htlo hthi
  exact ⟨fun x => ((H t htlo hthi).1 x).trans hG, (H t htlo hthi).2⟩

theorem IterGradOnWindow.glue_left
    {U : ℕ → ℝ → intervalDomainPoint → ℝ}
    {a lo hi G : ℝ} {n : ℕ}
    (Hleft : IterGradOnWindow U a lo n G)
    (Hright : IterGradOnWindow U lo hi n G) :
    IterGradOnWindow U a hi n G := by
  intro t hta hthi
  by_cases htlo : t ≤ lo
  · exact Hleft t hta htlo
  · have hlot : lo ≤ t := le_of_lt (lt_of_not_ge htlo)
    exact Hright t hlot hthi

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
    IterGradOnWindow U a hi n G →
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
  have Hraw := W.hkernel_step n HsrcInterval Hsrc
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
    {a t T : ℝ} (_ha : 0 ≤ a) (hat : a < t) (htT : t ≤ T)
    {q : ℝ → ℝ → ℝ}
    (hq_int : ∀ s, Integrable (q s) (intervalMeasure 1))
    {Cq : ℝ} (hCq : 0 ≤ Cq) (hq_sup : ∀ s y, |q s y| ≤ Cq) (x : ℝ)
    (hg_int : IntervalIntegrable
      (fun s : ℝ => deriv
        (fun z : ℝ => intervalFullSemigroupOperator (t - s) (q s) z) x) volume a t) :
    |∫ s in a..t, deriv
        (fun z : ℝ => intervalFullSemigroupOperator (t - s) (q s) z) x|
      ≤ heatGradientLinftyLinftyConstant * (2 * Real.sqrt (T - a)) * Cq := by
  let F : ℝ → ℝ := fun s : ℝ =>
    deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) (q s) z) x
  let qshift : ℝ → ℝ → ℝ := fun r : ℝ => q (r + a)
  have hdt_pos : 0 < t - a := sub_pos.mpr hat
  have hdtT : t - a ≤ T - a := sub_le_sub_right htT a
  have hq_int_shift : ∀ r, Integrable (qshift r) (intervalMeasure 1) := by
    intro r; dsimp [qshift]; exact hq_int (r + a)
  have hq_sup_shift : ∀ r y, |qshift r y| ≤ Cq := by
    intro r y; dsimp [qshift]; exact hq_sup (r + a) y
  have hgF_int : IntervalIntegrable F volume a t := by
    simpa [F] using hg_int
  have hF_shift :
      (fun r : ℝ => deriv
        (fun z : ℝ => intervalFullSemigroupOperator ((t - a) - r) (qshift r) z) x)
        = fun r : ℝ => F (r + a) := by
    funext r; dsimp [F, qshift]
    rw [show (t - a) - r = t - (r + a) by ring]
  have hg_shift : IntervalIntegrable
      (fun r : ℝ => deriv
        (fun z : ℝ => intervalFullSemigroupOperator ((t - a) - r) (qshift r) z) x)
      volume 0 (t - a) := by
    rw [hF_shift]
    simpa using (hgF_int.comp_add_right a)
  have hbound_shift :=
    ShenWork.IntervalGradDuhamelBound.gradDuhamel_sup_bound
      (t := t - a) (T := T - a) hdt_pos hdtT
      (q := qshift) hq_int_shift hCq hq_sup_shift x hg_shift
  have hIntegral_shift :
      (∫ r in (0 : ℝ)..(t - a), deriv
        (fun z : ℝ => intervalFullSemigroupOperator ((t - a) - r) (qshift r) z) x)
        = ∫ s in a..t, F s := by
    rw [hF_shift]
    have hcomp := intervalIntegral.integral_comp_add_right
      (f := F) (a := (0 : ℝ)) (b := t - a) a
    simpa using hcomp
  have hfinal :
      |∫ s in a..t, F s|
        ≤ heatGradientLinftyLinftyConstant * (2 * Real.sqrt (T - a)) * Cq := by
    rw [← hIntegral_shift]; exact hbound_shift
  simpa [F] using hfinal

end ShenWork.Paper2.TruncatedGradientWindow
