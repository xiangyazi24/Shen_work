/-
  ShenWork/Wiener/EWA/ResolverSourceWindowUniformDecay.lean

  **χ₀<0 — window-uniform power-source quadratic-decay constant `C : ℝ → ℝ` for the
  EWA Duhamel fixed-point slice `realSlice u_star`.**

  `realSlice_Hv_closed` (`SourcePerSliceClose.lean`) carries — as the single remaining
  standing residual — the WINDOW-UNIFORM power-source quadratic-decay package
  `C`/`hC`/`hdecay`/`ha0`: one per-`t₀` constant `C t₀` dominating the source cosine
  coefficients `cosineCoeffs (ν·lift (realSlice u_star σ)^γ)` uniformly over the whole
  clamp window `Icc (t₀/4) ((t₀+3T)/4)` (both the `k ≥ 1` quadratic decay and the
  zeroth bound).

  Pointwise-in-`σ` the decay is `realSlice_resolverDecay`'s `SourceCoeffQuadraticDecay`,
  but its constant is `σ`-DEPENDENT (the per-slice `C²`-norm).  This file UPGRADES that
  to the window-uniform `C t₀`: for each interior `t₀` it feeds the per-window slice
  data (cosine representation, a window-uniform positive lower bound `m`, a
  window-uniform upper bound `M`, and the `C¹`/`C²` window-derivative bounds `G1`/`G2`)
  to the unconditional single-window envelope
  `ShenWork.Paper2.ResolverPowerDecay.powerSource_window_uniform_decay`, and assembles
  the resulting per-window constants into the function `C : ℝ → ℝ` exactly in the shape
  the `realSlice_Hv_closed` residual binder expects.

  The per-window inputs (cosine representation + the window-uniform `m`/`M`/`G1`/`G2`
  bounds) are the boundedness data of the slice `C²`-norm over the compact window:
  finite by joint continuity + compactness on the canonical-Picard side
  (`lift_window_uniformPositive_of_subtypeCont` + the K2 producers).  For the abstract
  EWA fixed-point slice they are threaded as the precise per-`t₀` standing inputs — and
  it is exactly the assembly of these into the single window-uniform `C t₀` that the
  `realSlice_Hv_closed` residual was missing.

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.SourceResolverTimeC1Discharge
import ShenWork.Paper2.IntervalResolverPowerDecay

noncomputable section

namespace ShenWork.EWA

open Set
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)

variable {T : ℝ}

/-- **Window-uniform power-source quadratic-decay constant `C : ℝ → ℝ` for
`realSlice u_star` — DISCHARGED.**

For each interior `t₀ ∈ (0,T)` the per-window slice data of `realSlice u_star` on the
clamp window `[t₀/4, (t₀+3T)/4]` —

* the cosine representation `bc t₀`/`hbsum`/`hagree`,
* a window-uniform strictly-positive LOWER bound `m t₀ > 0` (`hm`/`hlb`),
* a window-uniform UPPER bound `M t₀` (`hub`),
* the window `C¹`/`C²` derivative bounds `G1 t₀`/`G2 t₀` (`hG1`/`hG2`) —

is fed to the unconditional single-window envelope `powerSource_window_uniform_decay`,
producing a SINGLE constant dominating the power-source cosine coefficients uniformly
over the window.  Collecting these over `t₀` gives the window-uniform package
`C`/`hC`/`hdecay`/`ha0` in the exact shape `realSlice_Hv_closed` carries.

This is the σ-uniformization of `realSlice_resolverDecay` (whose constant is the
σ-dependent per-slice `C²`-norm): the per-window slice `C²`-norm data is bounded over
the compact window, yielding the finite per-`t₀` constant. -/
theorem realSlice_powerSource_window_uniform_decay
    (p : CM2Params) (u_star : EWA T 1)
    (bc : ℝ → ℝ → ℕ → ℝ)
    (hbsum : ∀ t₀, 0 < t₀ → t₀ < T → ∀ σ ∈ Set.Icc (t₀ / 4) ((t₀ + 3 * T) / 4),
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc t₀ σ n|))
    (hagree : ∀ t₀, 0 < t₀ → t₀ < T →
      ∀ σ ∈ Set.Icc (t₀ / 4) ((t₀ + 3 * T) / 4),
      Set.EqOn (intervalDomainLift (realSlice u_star σ))
        (fun x => ∑' n, bc t₀ σ n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    (m M : ℝ → ℝ) (hm : ∀ t₀, 0 < m t₀)
    (hlb : ∀ t₀, 0 < t₀ → t₀ < T → ∀ σ ∈ Set.Icc (t₀ / 4) ((t₀ + 3 * T) / 4),
      ∀ x ∈ Set.Icc (0 : ℝ) 1, m t₀ ≤ intervalDomainLift (realSlice u_star σ) x)
    (hub : ∀ t₀, 0 < t₀ → t₀ < T → ∀ σ ∈ Set.Icc (t₀ / 4) ((t₀ + 3 * T) / 4),
      ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (realSlice u_star σ) x ≤ M t₀)
    (G1 G2 : ℝ → ℝ)
    (hG1 : ∀ t₀, 0 < t₀ → t₀ < T → ∀ σ ∈ Set.Icc (t₀ / 4) ((t₀ + 3 * T) / 4),
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (intervalDomainLift (realSlice u_star σ)) x| ≤ G1 t₀)
    (hG2 : ∀ t₀, 0 < t₀ → t₀ < T → ∀ σ ∈ Set.Icc (t₀ / 4) ((t₀ + 3 * T) / 4),
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (deriv (intervalDomainLift (realSlice u_star σ))) x| ≤ G2 t₀) :
    ∃ C : ℝ → ℝ, (∀ t₀, 0 ≤ C t₀) ∧
      (∀ t₀, 0 < t₀ → t₀ < T →
        ∀ σ ∈ Set.Icc (t₀ / 4) ((t₀ + 3 * T) / 4), ∀ k : ℕ, 1 ≤ k →
          |cosineCoeffs (fun x => p.ν * intervalDomainLift (realSlice u_star σ) x ^ p.γ) k|
            ≤ C t₀ / ((k : ℝ) * Real.pi) ^ 2) ∧
      (∀ t₀, 0 < t₀ → t₀ < T → ∀ σ ∈ Set.Icc (t₀ / 4) ((t₀ + 3 * T) / 4),
        |cosineCoeffs (fun x => p.ν * intervalDomainLift (realSlice u_star σ) x ^ p.γ) 0|
          ≤ C t₀) := by
  classical
  -- Per-`t₀` single-window envelope from the unconditional producer.
  have hwin : ∀ t₀, 0 < t₀ → t₀ < T →
      ∃ Ct : ℝ, 0 ≤ Ct ∧
        (∀ σ ∈ Set.Icc (t₀ / 4) ((t₀ + 3 * T) / 4), ∀ k : ℕ, 1 ≤ k →
          |cosineCoeffs (fun x => p.ν * intervalDomainLift (realSlice u_star σ) x ^ p.γ) k|
            ≤ Ct / ((k : ℝ) * Real.pi) ^ 2) ∧
        (∀ σ ∈ Set.Icc (t₀ / 4) ((t₀ + 3 * T) / 4),
          |cosineCoeffs (fun x => p.ν * intervalDomainLift (realSlice u_star σ) x ^ p.γ) 0|
            ≤ Ct) := by
    intro t₀ ht₀ ht₀T
    have hcd' : t₀ / 4 ≤ (t₀ + 3 * T) / 4 := by linarith
    exact ShenWork.Paper2.ResolverPowerDecay.powerSource_window_uniform_decay
      (ν := p.ν) (γ := p.γ) (M := M t₀) (m := m t₀)
      p.hν.le p.hγ (hm t₀) (w := realSlice u_star)
      (c' := t₀ / 4) (d' := (t₀ + 3 * T) / 4) hcd' (bc t₀)
      (hbsum t₀ ht₀ ht₀T) (hagree t₀ ht₀ ht₀T) (hlb t₀ ht₀ ht₀T) (hub t₀ ht₀ ht₀T)
      (G1 := G1 t₀) (G2 := G2 t₀) (hG1 t₀ ht₀ ht₀T) (hG2 t₀ ht₀ ht₀T)
  -- Assemble the per-window constants into `C : ℝ → ℝ`.
  refine ⟨fun t₀ => if h : 0 < t₀ ∧ t₀ < T then (hwin t₀ h.1 h.2).choose else 0,
    ?_, ?_, ?_⟩
  · intro t₀
    dsimp only
    split_ifs with h
    · exact (hwin t₀ h.1 h.2).choose_spec.1
    · exact le_rfl
  · intro t₀ ht₀ ht₀T σ hσ k hk
    have h : 0 < t₀ ∧ t₀ < T := ⟨ht₀, ht₀T⟩
    simp only [dif_pos h]
    exact (hwin t₀ ht₀ ht₀T).choose_spec.2.1 σ hσ k hk
  · intro t₀ ht₀ ht₀T σ hσ
    have h : 0 < t₀ ∧ t₀ < T := ⟨ht₀, ht₀T⟩
    simp only [dif_pos h]
    exact (hwin t₀ ht₀ ht₀T).choose_spec.2.2 σ hσ

end ShenWork.EWA

#print axioms ShenWork.EWA.realSlice_powerSource_window_uniform_decay
