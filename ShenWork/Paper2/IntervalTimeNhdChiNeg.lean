/-
  ShenWork/Paper2/IntervalTimeNhdChiNeg.lean

  **χ₀-general (B-form) producer of `HasTimeNeighborhoodSpectralAgreement`.**

  The χ₀ = 0 producer `Hu_of_restart_localized_of_subtypeCont`
  (`IntervalPicardLimitTimeNhdSubtype.lean`) routes through
  `intervalGradientDuhamelMap_eq_of_chi0_zero`, which DROPS the chemotaxis term.
  This file lands the χ₀-general analogue: it carries the chemotaxis term through
  the B-form (conjugate) Duhamel map.

  The whole chemotaxis content is already absorbed into the abstract B-form source
  family `aB` (whose split is `coupledLogisticSourceCoeffs - χ₀·coupledChemDivSourceCoeffs`,
  cf. `intervalConjugateDuhamelMap_cosineSeries` / the PID provider).  The
  Chapman–Kolmogorov / semigroup-restart consistency is exactly the diagonal
  exponent-addition `e^{−tλ} = e^{−(t−τ)λ}·e^{−τλ}` packaged inside
  `duhamelSpectralCoeff_general_split_on` and hence inside
  `localRestartCoeff_eq_bForm_restartCoeff` (`IntervalBFormRestart.lean`): no
  operator-level composition lemma is needed; the restart algebra runs entirely on
  the cosine-coefficient diagonal.

  From a global (from-zero, offset = 0) B-form cosine representation `hB_global`
  of the conjugate Picard limit, with `aB` time-`C¹` (`hsrcB`) and the slice
  coefficients ℓ¹ (`hB_global_summable`), this file produces, per interior
  `t₀ ∈ (0,T)`, the FROZEN restart anchor `(a₀, a, offset = t₀/2)` with
  `a₀ = cosineCoeffs (lift (u (t₀/2)))`, `a = (fun σ ↦ aB (t₀/2 + σ))`, and the
  two-sided neighbourhood agreement
    `u s x = ∑'ₙ localRestartCoeff a₀ a (s − t₀/2) n · cosineMode n x`
  for all `s` in `𝓝 t₀`, `x ∈ [0,1]`.  That is exactly
  `HasTimeNeighborhoodSpectralAgreement T (conjugatePicardLimit p u₀ T)` — the
  χ₀<0 spectral-agreement input, now CARRYING the chemotaxis term.

  Restart-anchor data discharged here:
  * `offset = t₀/2`, `0 < t₀ − offset` — immediate.
  * the shifted source `a = (fun σ ↦ aB (t₀/2 + σ))` is again `DuhamelSourceTimeC1`
    via `DuhamelSourceTimeC1.shift_nonneg` (`0 ≤ t₀/2`).
  * the anchor bound `|a₀ n| ≤ M` with `M = ∑'ₙ |localRestartCoeff aInit aB (t₀/2) n|`:
    `a₀ n = cosineCoeffs (lift (u (t₀/2))) n = localRestartCoeff aInit aB (t₀/2) n`
    (`cosineCoeffs_eq_localRestartCoeff_of_bForm_global_rep`), then term ≤ ℓ¹ sum.
  * the neighbourhood agreement is `conjugatePicardLimit_B_restart_of_global_cosine`.

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.  New file only.
-/
import ShenWork.Paper2.IntervalBFormRestart
import ShenWork.Paper2.IntervalDuhamelSourceShift
import ShenWork.PDE.IntervalMildTimeDerivContinuity

open Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalMildTimeDerivContinuity (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.IntervalConjugatePicard
  (conjugatePicardLimit cosineCoeffs_eq_localRestartCoeff_of_bForm_global_rep
    conjugatePicardLimit_B_restart_of_global_cosine)

noncomputable section

namespace ShenWork.IntervalTimeNhdChiNeg

/-- Term-by-term bound from ℓ¹ summability: each `|c n|` is at most the ℓ¹ sum. -/
theorem abs_le_tsum_abs_of_summable {c : ℕ → ℝ}
    (hc : Summable (fun n => |c n|)) (n : ℕ) :
    |c n| ≤ ∑' k, |c k| := by
  have hnn : ∀ k, 0 ≤ |c k| := fun k => abs_nonneg _
  simpa using hc.sum_le_tsum ({n} : Finset ℕ) (fun m _ => hnn m)

/-- **χ₀-general `HasTimeNeighborhoodSpectralAgreement` producer (B-form).**

From a global from-zero B-form cosine representation `hB_global` of the conjugate
Picard limit (carrying chemotaxis through the abstract B-form source family `aB`),
its ℓ¹ slice summability `hB_global_summable`, and the time-`C¹` source package
`hsrcB`, this produces the fixed-anchor time-neighbourhood spectral agreement at
offset `t₀/2`, for every interior `t₀ ∈ (0,T)`.  The chemotaxis term is carried
(no χ₀ = 0 reduction). -/
theorem HasTimeNeighborhoodSpectralAgreement_of_conjugateMild
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T : ℝ}
    (aInit : ℕ → ℝ) (aB : ℝ → ℕ → ℝ)
    (hsrcB : DuhamelSourceTimeC1 aB)
    (hB_global : ∀ t, 0 < t → t ≤ T →
      Set.EqOn (intervalDomainLift (conjugatePicardLimit p u₀ T t))
        (fun x => ∑' n, localRestartCoeff aInit aB t n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1))
    (hB_global_summable : ∀ t, 0 < t → t ≤ T →
      Summable (fun n => |localRestartCoeff aInit aB t n|)) :
    HasTimeNeighborhoodSpectralAgreement T (conjugatePicardLimit p u₀ T) := by
  -- Continuity of each `aB · k` on `[0,T]` (from time-`C¹`), needed for the
  -- general Duhamel coefficient split used by the restart producer.
  have ha_cont : ∀ k, ContinuousOn (fun s => aB s k) (Set.Icc 0 T) := fun k =>
    (continuous_iff_continuousAt.2
      (fun s => (hsrcB.hderiv s k).continuousAt)).continuousOn
  -- The two-sided neighbourhood restart agreement (offset = t₀/2), carrying
  -- chemotaxis through `aB`.  This is the semigroup-restart / Chapman–Kolmogorov
  -- consistency on the cosine diagonal.
  have hB_restart :=
    conjugatePicardLimit_B_restart_of_global_cosine
      (p := p) (u₀ := u₀) (T := T) (a₀ := aInit) (aB := aB)
      ha_cont hB_global hB_global_summable
  constructor
  intro t₀ ht₀ ht₀T
  -- restart base / offset
  set τ : ℝ := t₀ / 2 with hτdef
  have hτpos : 0 < τ := by rw [hτdef]; linarith
  have hτt₀ : τ < t₀ := by rw [hτdef]; linarith
  have hτT : τ < T := lt_trans hτt₀ ht₀T
  -- frozen anchor data
  set a₀ : ℕ → ℝ := cosineCoeffs (intervalDomainLift (conjugatePicardLimit p u₀ T τ))
    with ha₀def
  set a : ℝ → ℕ → ℝ := fun σ n => aB (τ + σ) n with hadef
  -- The shifted source is again time-`C¹` (`0 ≤ τ`).
  have hsrc_shift : DuhamelSourceTimeC1 a :=
    ShenWork.IntervalDuhamelSourceShift.DuhamelSourceTimeC1.shift_nonneg
      hsrcB (offset := τ) hτpos.le
  -- ℓ¹ summability of the anchor's source-restart coefficients at base `τ`.
  have hsumτ : Summable (fun n => |localRestartCoeff aInit aB τ n|) :=
    hB_global_summable τ hτpos hτT.le
  -- M := the ℓ¹ sum; the anchor coefficients are bounded by it.
  set M : ℝ := ∑' n, |localRestartCoeff aInit aB τ n| with hMdef
  have hMnn : 0 ≤ M := by
    rw [hMdef]; exact tsum_nonneg (fun n => abs_nonneg _)
  -- a₀ n = localRestartCoeff aInit aB τ n (coefficient extraction at the base).
  have ha₀eq : ∀ n, a₀ n = localRestartCoeff aInit aB τ n := by
    intro n
    rw [ha₀def]
    exact cosineCoeffs_eq_localRestartCoeff_of_bForm_global_rep
      (u := conjugatePicardLimit p u₀ T) (a₀ := aInit) (aB := aB) (τ := τ)
      (hB_global τ hτpos hτT.le) hsumτ n
  have hMbound : ∀ n, |a₀ n| ≤ M := by
    intro n
    rw [ha₀eq n, hMdef]
    exact abs_le_tsum_abs_of_summable hsumτ n
  -- the neighbourhood agreement at `t₀`, in the structure's normal form.
  have hagree_nhd := hB_restart t₀ ht₀ ht₀T
  refine ⟨a₀, M, hMnn, hMbound, a, hsrc_shift, τ, by rw [hτdef]; linarith, ?_⟩
  filter_upwards [hagree_nhd] with s hs
  intro x
  -- `hs x` is `u s x = ∑' localRestartCoeff (cosineCoeffs (lift (u (t₀/2)))) … `;
  -- rewrite the anchor `cosineCoeffs (lift (u (t₀/2)))` and shifted source `aB (t₀/2+·)`
  -- to the frozen names `a₀`, `a`.
  have := hs x
  rw [show (t₀ / 2 : ℝ) = τ from hτdef.symm] at this
  exact this

#print axioms
  ShenWork.IntervalTimeNhdChiNeg.HasTimeNeighborhoodSpectralAgreement_of_conjugateMild

end ShenWork.IntervalTimeNhdChiNeg
