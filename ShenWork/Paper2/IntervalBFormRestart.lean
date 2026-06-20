/-
  B-form restart cosine representation from a global B-form cosine formula.

  The proof is only the restart algebra: coefficient extraction at the restart
  base plus the general Duhamel coefficient split.  No χ₀ = 0 reduction is used.
-/
import ShenWork.Paper2.IntervalConjugatePicard
import ShenWork.Paper2.IntervalPicardLimitRestartWeak
import ShenWork.Paper2.IntervalPicardLimitSourceData

open Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalDuhamelClosedC2 (duhamelSpectralCoeff)
open ShenWork.IntervalConjugatePicard
  (conjugatePicardLimit)

noncomputable section

namespace ShenWork.IntervalConjugatePicard

local notation "λ_" n => unitIntervalCosineEigenvalue n

/-- Coefficient extraction from a B-form global cosine representation. -/
theorem cosineCoeffs_eq_localRestartCoeff_of_bForm_global_rep
    {u : ℝ → intervalDomainPoint → ℝ}
    {a₀ : ℕ → ℝ} {aB : ℝ → ℕ → ℝ}
    {τ : ℝ}
    (hrepτ : Set.EqOn (intervalDomainLift (u τ))
      (fun x => ∑' n, localRestartCoeff a₀ aB τ n * cosineMode n x)
      (Set.Icc (0 : ℝ) 1))
    (hsumτ : Summable (fun n => |localRestartCoeff a₀ aB τ n|))
    (k : ℕ) :
    cosineCoeffs (intervalDomainLift (u τ)) k =
      localRestartCoeff a₀ aB τ k := by
  rw [ShenWork.Paper2.cosineCoeffs_congr_on_Icc hrepτ k]
  exact ShenWork.IntervalPicardIterateRestart.cosineCoeffs_of_l1_cosineSeries
    hsumτ k

/-- B-form restart coefficient identity, with an arbitrary restart base. -/
theorem localRestartCoeff_eq_bForm_restartCoeff
    {u : ℝ → intervalDomainPoint → ℝ}
    {T τ t : ℝ}
    {a₀ : ℕ → ℝ} {aB : ℝ → ℕ → ℝ}
    (ha_cont : ∀ k, ContinuousOn (fun s => aB s k) (Set.Icc 0 T))
    (hτ : 0 < τ) (hτt : τ < t) (htT : t ≤ T)
    (hrepτ : Set.EqOn (intervalDomainLift (u τ))
      (fun x => ∑' n, localRestartCoeff a₀ aB τ n * cosineMode n x)
      (Set.Icc (0 : ℝ) 1))
    (hsumτ : Summable (fun n => |localRestartCoeff a₀ aB τ n|))
    (k : ℕ) :
    localRestartCoeff a₀ aB t k =
      localRestartCoeff
        (cosineCoeffs (intervalDomainLift (u τ)))
        (fun σ n => aB (τ + σ) n)
        (t - τ) k := by
  have hbase :
      cosineCoeffs (intervalDomainLift (u τ)) k =
        localRestartCoeff a₀ aB τ k :=
    cosineCoeffs_eq_localRestartCoeff_of_bForm_global_rep hrepτ hsumτ k
  unfold localRestartCoeff
  rw [hbase]
  have hsplit :=
    ShenWork.IntervalPicardLimitRestartWeak.duhamelSpectralCoeff_general_split_on
      (a := aB) (T := T) ha_cont hτ.le hτt.le htT k
  rw [hsplit]
  have hexp :
      Real.exp (-t * (λ_ k))
        = Real.exp (-(t - τ) * (λ_ k)) * Real.exp (-τ * (λ_ k)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  rw [show localRestartCoeff a₀ aB τ k =
      Real.exp (-τ * (λ_ k)) * a₀ k + duhamelSpectralCoeff aB τ k by rfl]
  ring_nf

/-- B-form restart representation from a from-zero B-form cosine
representation. -/
theorem bForm_restart_of_global_cosine
    {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    {a₀ : ℕ → ℝ} {aB : ℝ → ℕ → ℝ}
    (ha_cont : ∀ k, ContinuousOn (fun s => aB s k) (Set.Icc 0 T))
    (hrep : ∀ t, 0 < t → t ≤ T →
      Set.EqOn (intervalDomainLift (u t))
        (fun x => ∑' n, localRestartCoeff a₀ aB t n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1))
    (hsum : ∀ t, 0 < t → t ≤ T →
      Summable (fun n => |localRestartCoeff a₀ aB t n|)) :
    ∀ t₀, 0 < t₀ → t₀ < T →
      ∀ᶠ s in 𝓝 t₀, ∀ y : intervalDomainPoint,
        u s y =
          ∑' n,
            localRestartCoeff
              (cosineCoeffs (intervalDomainLift (u (t₀ / 2))))
              (fun σ n => aB (t₀ / 2 + σ) n)
              (s - t₀ / 2) n * cosineMode n y.1 := by
  intro t₀ ht₀ ht₀T
  set τ : ℝ := t₀ / 2 with hτdef
  have hτpos : 0 < τ := by rw [hτdef]; linarith
  have hτt₀ : τ < t₀ := by rw [hτdef]; linarith
  have hτT : τ < T := lt_trans hτt₀ ht₀T
  have hmem : t₀ ∈ Set.Ioo τ T := ⟨hτt₀, ht₀T⟩
  filter_upwards [isOpen_Ioo.mem_nhds hmem] with s hs
  have hτs : τ < s := hs.1
  have hsT : s < T := hs.2
  have hspos : 0 < s := lt_trans hτpos hτs
  intro y
  have hlift : u s y = intervalDomainLift (u s) y.1 := by
    simp [intervalDomainLift]
  have hpoint :
      u s y =
        ∑' n,
          localRestartCoeff
            (cosineCoeffs (intervalDomainLift (u τ)))
            (fun σ n => aB (τ + σ) n)
            (s - τ) n * cosineMode n y.1 := by
    rw [hlift, hrep s hspos hsT.le y.2]
    refine tsum_congr (fun n => ?_)
    rw [localRestartCoeff_eq_bForm_restartCoeff
      (u := u) (T := T) (τ := τ) (t := s) (a₀ := a₀) (aB := aB)
      ha_cont hτpos hτs hsT.le
      (hrep τ hτpos hτT.le) (hsum τ hτpos hτT.le) n]
  simpa [τ, hτdef] using hpoint

/-- The B-form restart representation specialized to the conjugate Picard
limit. -/
theorem conjugatePicardLimit_B_restart_of_global_cosine
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T : ℝ}
    {a₀ : ℕ → ℝ} {aB : ℝ → ℕ → ℝ}
    (ha_cont : ∀ k, ContinuousOn (fun s => aB s k) (Set.Icc 0 T))
    (hrep : ∀ t, 0 < t → t ≤ T →
      Set.EqOn (intervalDomainLift (conjugatePicardLimit p u₀ T t))
        (fun x => ∑' n, localRestartCoeff a₀ aB t n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1))
    (hsum : ∀ t, 0 < t → t ≤ T →
      Summable (fun n => |localRestartCoeff a₀ aB t n|)) :
    ∀ t₀, 0 < t₀ → t₀ < T →
      ∀ᶠ s in 𝓝 t₀, ∀ y : intervalDomainPoint,
        conjugatePicardLimit p u₀ T s y =
          ∑' n,
            localRestartCoeff
              (cosineCoeffs
                (intervalDomainLift
                  (conjugatePicardLimit p u₀ T (t₀ / 2))))
              (fun σ n => aB (t₀ / 2 + σ) n)
              (s - t₀ / 2) n * cosineMode n y.1 :=
  bForm_restart_of_global_cosine
    (u := conjugatePicardLimit p u₀ T) ha_cont hrep hsum

#print axioms bForm_restart_of_global_cosine
#print axioms conjugatePicardLimit_B_restart_of_global_cosine

end ShenWork.IntervalConjugatePicard
