/-
  Quadratic source remainder for the elliptic Neumann resolver.

  The signal equation is nonlinear only through `u^γ`.  Around a positive
  equilibrium, its source splits into the exact linear term
  `γ u*^(γ-1) φ` plus a pointwise quadratic remainder.
-/
import ShenWork.Paper3.IntervalDomainLogisticRemainder
import ShenWork.PDE.IntervalNeumannEllipticResolverR

namespace ShenWork.Paper3

open Set Real

noncomputable section

/-- First derivative of the positive power map. -/
def paper3PowerDeriv (gamma z : ℝ) : ℝ :=
  gamma * z ^ (gamma - 1)

/-- The derivative of `z ↦ z^γ` is locally Lipschitz on a fixed positive
neighborhood of `u*`. -/
theorem paper3PowerDeriv_local_lipschitz
    {gamma uStar : ℝ} (huStar : 0 < uStar) :
    ∃ L > 0, ∀ x ∈ Set.Icc (uStar / 2) (3 * uStar / 2),
      ∀ y ∈ Set.Icc (uStar / 2) (3 * uStar / 2),
        |paper3PowerDeriv gamma x - paper3PowerDeriv gamma y| ≤
          L * |x - y| := by
  let I : Set ℝ := Set.Icc (uStar / 2) (3 * uStar / 2)
  let second : ℝ → ℝ := fun z =>
    gamma * (gamma - 1) * z ^ (gamma - 2)
  have hlower : 0 < uStar / 2 := by linarith
  have hpos : ∀ z ∈ I, 0 < z := by
    intro z hz
    exact lt_of_lt_of_le hlower hz.1
  have hsecond_cont : ContinuousOn second I := by
    have hpow : ContinuousOn (fun z : ℝ => z ^ (gamma - 2)) I :=
      continuousOn_id.rpow_const (fun z hz => Or.inl (hpos z hz).ne')
    exact continuousOn_const.mul hpow
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hsecond_cont
  have huI : uStar ∈ I := by
    constructor <;> dsimp [I] <;> linarith
  have hM0 : 0 ≤ M :=
    (norm_nonneg (second uStar)).trans (hM uStar huI)
  let L : ℝ := M + 1
  have hL : 0 < L := by dsimp [L]; linarith
  refine ⟨L, hL, ?_⟩
  intro x hx y hy
  have hder : ∀ z ∈ I,
      HasDerivWithinAt (paper3PowerDeriv gamma) (second z) I z := by
    intro z hz
    have hzpos := hpos z hz
    have hpow : HasDerivAt (fun w : ℝ => w ^ (gamma - 1))
        ((gamma - 1) * z ^ (gamma - 2)) z := by
      convert Real.hasDerivAt_rpow_const
        (x := z) (p := gamma - 1) (Or.inl hzpos.ne') using 1
      ring
    have hmul := hpow.const_mul gamma
    convert hmul.hasDerivWithinAt using 1
    simp only [second]
    ring
  have hbound : ∀ z ∈ I, ‖second z‖ ≤ L := by
    intro z hz
    exact (hM z hz).trans (by dsimp [L]; linarith)
  have hmv :
      ‖paper3PowerDeriv gamma x - paper3PowerDeriv gamma y‖ ≤
        L * ‖x - y‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      hder hbound (convex_Icc _ _) hy hx
  simpa [I, Real.norm_eq_abs] using hmv

/-- Quadratic Taylor remainder for the positive power source. -/
def paper3PowerLinearizationRemainder
    (gamma uStar z : ℝ) : ℝ :=
  z ^ gamma - uStar ^ gamma -
    paper3PowerDeriv gamma uStar * (z - uStar)

theorem paper3Power_quadratic_remainder
    {gamma uStar : ℝ} (huStar : 0 < uStar) :
    ∃ K > 0, ∀ x ∈ Set.Icc (uStar / 2) (3 * uStar / 2),
      |paper3PowerLinearizationRemainder gamma uStar x| ≤
        K * |x - uStar| ^ 2 := by
  rcases paper3PowerDeriv_local_lipschitz huStar with
    ⟨K, hK, hLip⟩
  have huI : uStar ∈ Set.Icc (uStar / 2) (3 * uStar / 2) := by
    constructor <;> linarith
  refine ⟨K, hK, ?_⟩
  intro x hx
  have hrem := quadratic_remainder_le_of_deriv_lipschitzOn
    (f := fun z : ℝ => z ^ gamma)
    (f' := paper3PowerDeriv gamma)
    (s := Set.Icc (uStar / 2) (3 * uStar / 2))
    (L := K) (x := x) (y := uStar)
    (convex_Icc _ _) hK.le
    (fun z hz => by
      have hzpos : 0 < z :=
        lt_of_lt_of_le (by linarith [huStar]) hz.1
      simpa [paper3PowerDeriv] using
        (Real.hasDerivAt_rpow_const
          (x := z) (p := gamma) (Or.inl hzpos.ne')))
    hLip hx huI
  simpa [paper3PowerLinearizationRemainder] using hrem

/-- The actual elliptic source remainder, including its coefficient `ν`. -/
def paper3EllipticSourceRemainder
    (p : CM2Params) (uStar z : ℝ) : ℝ :=
  p.ν * paper3PowerLinearizationRemainder p.γ uStar z

theorem paper3EllipticSource_quadratic_remainder
    (p : CM2Params) {uStar : ℝ} (huStar : 0 < uStar) :
    ∃ K > 0, ∀ x ∈ Set.Icc (uStar / 2) (3 * uStar / 2),
      |paper3EllipticSourceRemainder p uStar x| ≤
        K * |x - uStar| ^ 2 := by
  rcases paper3Power_quadratic_remainder (gamma := p.γ) huStar with
    ⟨K₀, hK₀, hrem⟩
  let K : ℝ := p.ν * K₀
  have hK : 0 < K := mul_pos p.hν hK₀
  refine ⟨K, hK, ?_⟩
  intro x hx
  have h := hrem x hx
  rw [paper3EllipticSourceRemainder, abs_mul, abs_of_pos p.hν]
  simpa [K, mul_assoc] using mul_le_mul_of_nonneg_left h p.hν.le

#print axioms paper3PowerDeriv_local_lipschitz
#print axioms paper3Power_quadratic_remainder
#print axioms paper3EllipticSource_quadratic_remainder

end

end ShenWork.Paper3
