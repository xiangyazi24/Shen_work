/-
  ShenWork/Paper2/IntervalResolverStrictPositivity.lean

  **Hvpos — strict positivity of the chemical concentration.**

  Target (the `Hvpos` ledger field consumed by
  `ShenWork.Paper2.IntervalDomainLedgerSweep`):

  ```
  ∀ t, 0 < t → t < D.T → ∀ x, 0 < mildChemicalConcentration p D.u t x
  ```

  `mildChemicalConcentration p u t = intervalNeumannResolverR p (u t)`, the
  Neumann elliptic resolver of the source `ν·u^γ`.  On a slice with `t > 0`,
  `u(t) > 0` everywhere on `[0,1]` (`D.hpos`), so the continuous source `ν·u^γ`
  is bounded below by a strictly positive constant `c₀ = ν·m^γ` (m = min u over
  the compact slice).  The resolver of a source `≥ c₀` is `≥ c₀/μ > 0`
  (`IntervalDomainResolverStrictPos.resolverR_pos_of_representation`, whose
  heat-Laplace strict-integrand machinery is already in place).

  This file only WIRES `GradientMildSolutionData` into that representation
  lemma: it builds the globally-continuous slice extension `cs = u(t) ∘ clip`,
  reads off the positive lower bound `m` and the bound `M` from `D.hpos`,
  `D.hbound`, and supplies the source-coefficient matching / `ℓ²` summability
  exactly as the resolver-nonnegativity proof does.

  No `sorry`/`admit`/custom `axiom`/`native_decide`.
-/
import ShenWork.Paper2.IntervalMildToClassical
import ShenWork.Paper2.IntervalDomainResolverStrictPos
import ShenWork.Paper2.IntervalResolverWeakBounds
import ShenWork.Paper2.IntervalPicardLimitCoeffConv

open Set Filter Topology MeasureTheory
open ShenWork.IntervalMildPicard
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.PDE (intervalNeumannResolverR intervalNeumannResolverSourceCoeff)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.Paper2 (cosineCoeffs_congr_on_Icc)
open ShenWork.IntervalDomainResolverStrictPos (cosineCoeffs_const resolverR_pos_of_representation)
open ShenWork.IntervalResolverWeakBounds (resolverSourceCoeff_re_sq_summable_of_continuousOn)
open ShenWork.IntervalPicardLimitCoeffConv (cosineCoeffs_sub_eq)
open ShenWork.Paper2 (intervalNeumannResolverSourceCoeff_zero)

noncomputable section

namespace ShenWork.IntervalResolverStrictPositivity

open ShenWork.IntervalMildToClassical (mildChemicalConcentration)

/-- The clip map `ℝ → [0,1]` (clamp into the closed interval). -/
private def clip : ℝ → intervalDomainPoint := fun x =>
  ⟨max 0 (min x 1), le_max_left 0 _, max_le (by norm_num) (min_le_right x 1)⟩

private theorem clip_continuous : Continuous clip :=
  Continuous.subtype_mk
    (continuous_const.max (continuous_id.min continuous_const)) _

/-- On `[0,1]` the clip is the identity inclusion: `(g ∘ clip) x = lift g x`. -/
private theorem clip_comp_eq_lift_on_Icc (g : intervalDomainPoint → ℝ)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    (g ∘ clip) x = intervalDomainLift g x := by
  have hclip_eq : max 0 (min x 1) = x := by
    rw [min_eq_left hx.2, max_eq_right hx.1]
  simp only [Function.comp, clip, intervalDomainLift, dif_pos hx]
  exact congrArg g (Subtype.ext hclip_eq)

/-- **Hvpos.**  Strict positivity of the chemical concentration on the open
time interval `(0, T)`: for `t > 0` the slice `D.u t` is `> 0` on `[0,1]`, so the
resolver source `ν·(D.u t)^γ` sits above a positive constant and the resolver is
`≥ c₀/μ > 0`. -/
theorem mildChemicalConcentration_pos
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) :
    ∀ t, 0 < t → t < D.T → ∀ x : intervalDomainPoint,
      0 < mildChemicalConcentration p D.u t x := by
  intro t ht htT x
  have htT' : t ≤ D.T := le_of_lt htT
  -- The slice and its globally-continuous clip extension.
  set g₀ : intervalDomainPoint → ℝ := D.u t with hg₀
  have hg₀_cont : Continuous g₀ := D.hcont t ht htT'
  set cs : ℝ → ℝ := g₀ ∘ clip with hcs
  have hcs_cont : Continuous cs := hg₀_cont.comp clip_continuous
  -- Agreement with the lift on [0,1].
  have hagree : ∀ y ∈ Set.Icc (0:ℝ) 1,
      intervalDomainLift g₀ y = cs y := fun y hy =>
    (clip_comp_eq_lift_on_Icc g₀ hy).symm
  -- Positive lower bound m = min cs over the compact [0,1].
  have hIcc_ne : (Set.Icc (0:ℝ) 1).Nonempty := ⟨0, by norm_num⟩
  obtain ⟨x₀, hx₀mem, hx₀min⟩ :=
    isCompact_Icc.exists_isMinOn hIcc_ne hcs_cont.continuousOn
  set m : ℝ := cs x₀ with hm
  have hcs_lb : ∀ y ∈ Set.Icc (0:ℝ) 1, m ≤ cs y := fun y hy => hx₀min hy
  have hm_pos : 0 < m := by
    rw [hm, hcs, Function.comp]
    exact D.hpos t ht htT' (clip x₀)
  -- Upper bound M = D.M from the slice bound.
  have hcs_ub : ∀ y ∈ Set.Icc (0:ℝ) 1, cs y ≤ D.M := fun y hy => by
    rw [hcs, Function.comp]
    have : g₀ (clip y) ≤ |g₀ (clip y)| := le_abs_self _
    exact le_trans this (D.hbound t ht htT' (clip y))
  -- Source coefficient matching: (sourceCoeff p g₀ k).re = cosineCoeffs (ν·lift g₀^γ) k.
  have hsrc_coeff : ∀ k,
      cosineCoeffs (fun y => p.ν * intervalDomainLift g₀ y ^ p.γ) k
        = (intervalNeumannResolverSourceCoeff p g₀ k).re := by
    intro k
    simp [cosineCoeffs, intervalNeumannResolverSourceCoeff, Complex.ofReal_re]
  -- ℓ² of the source coefficients (cosine–Bessel, source is L²[0,1]).
  have hUcont : ContinuousOn (intervalDomainLift g₀) (Set.Icc (0:ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    have hres : Set.restrict (Set.Icc (0:ℝ) 1) (intervalDomainLift g₀) = g₀ := by
      funext z
      obtain ⟨z, hz⟩ := z
      show intervalDomainLift g₀ z = g₀ ⟨z, hz⟩
      rw [intervalDomainLift, dif_pos hz]
    rw [hres]; exact hg₀_cont
  have hâ : Summable (fun k =>
      (cosineCoeffs (fun y => p.ν * intervalDomainLift g₀ y ^ p.γ) k) ^ 2) := by
    have h := resolverSourceCoeff_re_sq_summable_of_continuousOn p hUcont
    simp only [intervalNeumannResolverSourceCoeff_zero, sub_zero] at h
    exact h.congr (fun k => by rw [hsrc_coeff k])
  -- ℓ² of the shifted source `ν·lift g₀^γ − ν·m^γ`: differs from the above only
  -- at the zeroth mode (constant coeffs vanish for k ≥ 1).
  set c₀ : ℝ := p.ν * m ^ p.γ with hc₀def
  have hĝ : Summable (fun k =>
      (cosineCoeffs (fun y => p.ν * intervalDomainLift g₀ y ^ p.γ - c₀) k) ^ 2) := by
    have hsplit : ∀ k,
        cosineCoeffs (fun y => p.ν * intervalDomainLift g₀ y ^ p.γ - c₀) k
          = cosineCoeffs (fun y => p.ν * intervalDomainLift g₀ y ^ p.γ) k
            - cosineCoeffs (fun _ => c₀) k := by
      intro k
      have hgc : ContinuousOn (fun y => p.ν * intervalDomainLift g₀ y ^ p.γ)
          (Set.Icc (0:ℝ) 1) :=
        continuousOn_const.mul (hUcont.rpow_const (fun y _ => Or.inr p.hγ.le))
      exact cosineCoeffs_sub_eq hgc continuousOn_const k
    -- For k ≠ 0 the shifted coeff equals the unshifted coeff (const → 0), so the
    -- squares agree off the singleton {0}; updating `hâ` at `0` keeps summability.
    have hupd : (fun k =>
        (cosineCoeffs (fun y => p.ν * intervalDomainLift g₀ y ^ p.γ - c₀) k) ^ 2)
        = Function.update
            (fun k => (cosineCoeffs (fun y => p.ν * intervalDomainLift g₀ y ^ p.γ) k) ^ 2)
            0
            ((cosineCoeffs (fun y => p.ν * intervalDomainLift g₀ y ^ p.γ - c₀) 0) ^ 2) := by
      funext k
      by_cases hk : k = 0
      · subst hk; rw [Function.update_self]
      · rw [Function.update_of_ne hk, hsplit k, cosineCoeffs_const, if_neg hk, sub_zero]
    rw [hupd]
    exact hâ.update 0 _
  -- Discharge via the representation lemma.
  show 0 < intervalNeumannResolverR p (D.u t) x
  exact resolverR_pos_of_representation p hcs_cont hagree hm_pos hcs_lb hcs_ub
    hsrc_coeff hâ hĝ x

end ShenWork.IntervalResolverStrictPositivity
