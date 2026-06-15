/-
  ShenWork/Wiener/EWA/SourceInitialTrace.lean

  **χ₀<0 capstone — `InitialTrace` for the source-form realized slice.**

  Proves `InitialTrace intervalDomain u₀ (realSlice u_star)`: as `t → 0⁺` the
  realized slice converges (in the `intervalDomain.supNorm` sup-norm) to the
  initial datum `u₀`.

  Route.  By the slab `realizes` (`realizes_clean`, packaged here as `hrealizes`)
  the lift of the slice on `[0,1]` is the cosine synthesis
    `lift (realSlice u_star t) x = ∑ₙ fullSourceCoeff p (realSlice u_star) u₀cos t n
                                     · cos(nπx)`,
  and the datum is the cosine reconstruction of its coefficients
    `u₀ x = ∑ₙ u₀cos n · cos(nπx)`               (`hrecon`).
  Subtracting (both series being ℓ¹-summable) and bounding each cosine by `1`
  gives the *uniform-in-x* ℓ¹ control
    `|realSlice u_star t x − u₀ x| ≤ ∑ₙ |fullSourceCoeff … t n − u₀cos n|`.
  The RHS is the per-time ℓ¹ defect of the source coefficients against the datum
  coefficients.  Its two analytic ingredients — the heat-leg trace
  `e^{−tλₙ}u₀cosₙ → u₀cosₙ` and the two Duhamel legs `→ 0` as `t → 0⁺`, all in
  ℓ¹ — are carried as the committed atoms `hdefect` (per-time summability) and
  `htrace` (the ℓ¹ defect `→ 0`), in the established carried-atom doctrine of the
  χ₀<0 chain (cf. `realSlice_classicalRegularity`, `realizes_clean`).

  The assembly here is genuine: it turns the carried ℓ¹ defect limit into the
  sup-norm `InitialTrace` via the uniform cosine bound and the `sSup` envelope.

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.SourceClassicalExistence

noncomputable section

open scoped BigOperators
open Filter Topology

namespace ShenWork.EWA

open ShenWork.IntervalDomain
  (intervalDomainPoint intervalDomainLift intervalDomainSupNorm intervalDomain)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.Paper2 (InitialTrace)

variable {T : ℝ}

/-- **Uniform cosine ℓ¹ bound.**  For an ℓ¹ coefficient family `c`, the cosine
synthesis is bounded pointwise by the ℓ¹ norm: `|∑ₙ cₙ cos(nπx)| ≤ ∑ₙ |cₙ|`. -/
theorem abs_cosineSynthesis_le_tsum_abs (c : ℕ → ℝ) (x : ℝ)
    (hc : Summable (fun n => |c n|)) :
    |∑' n, c n * cosineMode n x| ≤ ∑' n, |c n| := by
  have hbound : ∀ n, |c n * cosineMode n x| ≤ |c n| := by
    intro n
    rw [abs_mul, cosineMode]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  have hterm : Summable (fun n => c n * cosineMode n x) :=
    (Summable.of_nonneg_of_le (fun n => abs_nonneg _) hbound hc).of_abs
  have habs : Summable (fun n => |c n * cosineMode n x|) :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _) hbound hc
  have hnorm : Summable (fun n => ‖c n * cosineMode n x‖) := by
    simpa [Real.norm_eq_abs] using habs
  calc |∑' n, c n * cosineMode n x|
      = ‖∑' n, c n * cosineMode n x‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' n, ‖c n * cosineMode n x‖ := norm_tsum_le_tsum_norm hnorm
    _ = ∑' n, |c n * cosineMode n x| := by simp [Real.norm_eq_abs]
    _ ≤ ∑' n, |c n| := habs.tsum_le_tsum hbound hc

/-- **`InitialTrace` for the χ₀<0 source-form realized slice.**

The realized slice `realSlice u_star` converges to the cosine datum `u₀` in the
`intervalDomain` sup-norm as `t → 0⁺`.  Carried atoms (the standard χ₀<0 atoms):
`hu0cos` (ℓ¹ datum coefficients, `= realizes_clean`'s `hsum`), `hrecon` (the
cosine reconstruction of `u₀`), `hrealizes` (the slab `realizes` of
`realizes_clean`, restricted to `t ∈ (0,T)`), `hdefect` (per-time ℓ¹ summability
of the source/datum coefficient defect), and `htrace` (the ℓ¹ defect `→ 0` as
`t → 0⁺`: the heat-leg trace plus the two Duhamel legs vanishing). -/
theorem realSlice_initialTrace (p : CM2Params) (u_star : EWA T 1)
    (u₀cos : ℕ → ℝ) (u₀ : intervalDomainPoint → ℝ) (hT : (0 : ℝ) < T)
    (hu0cos : Summable (fun n => |u₀cos n|))
    (hrecon : ∀ x : intervalDomainPoint,
      u₀ x = ∑' n, u₀cos n * cosineMode n x.1)
    (hrealizes : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (realSlice u_star t) x
        = ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x)
    (hdefect : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      Summable (fun n =>
        |fullSourceCoeff p (realSlice u_star) u₀cos t n - u₀cos n|))
    (htrace : Tendsto
      (fun t => ∑' n,
        |fullSourceCoeff p (realSlice u_star) u₀cos t n - u₀cos n|)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    InitialTrace intervalDomain u₀ (realSlice u_star) := by
  classical
  -- abbreviation for the per-time ℓ¹ defect of source vs. datum coefficients
  set D : ℝ → ℝ := fun t =>
    ∑' n, |fullSourceCoeff p (realSlice u_star) u₀cos t n - u₀cos n| with hD
  intro ε hε
  -- pull a threshold from the carried ℓ¹ defect limit `htrace`
  have hball : ∀ᶠ t in 𝓝[>] (0 : ℝ), D t < ε / 2 := by
    have := htrace.eventually (eventually_lt_nhds (show (0 : ℝ) < ε / 2 by linarith))
    simpa [hD] using this
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hball
  obtain ⟨δ₁, hδ₁, hsmall⟩ := hball
  refine ⟨min δ₁ T, lt_min hδ₁ hT, fun t ht htδ => ?_⟩
  have htδ₁ : t < δ₁ := lt_of_lt_of_le htδ (min_le_left _ _)
  have htT : t < T := lt_of_lt_of_le htδ (min_le_right _ _)
  have htIoo : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht, htT⟩
  -- the ℓ¹ defect bound at this `t`
  have hDt : D t < ε / 2 := by
    have hmem : t ∈ Set.Ioi (0 : ℝ) := ht
    have hdist : dist t 0 < δ₁ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos ht]; exact htδ₁
    exact hsmall hdist hmem
  -- abbreviate the source-coefficient family at this `t`
  set f : ℕ → ℝ := fun n => fullSourceCoeff p (realSlice u_star) u₀cos t n with hf
  -- both cosine series (source and datum) are ℓ¹-summable, hence so is their term diff
  have hf_l1 : Summable (fun n => |f n|) := by
    have hsum := (hdefect t htIoo).add hu0cos
    refine hsum.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
    have htri : |f n| ≤ |f n - u₀cos n| + |u₀cos n| := by
      have := abs_sub_abs_le_abs_sub (f n) (u₀cos n)
      have h2 : |f n| - |u₀cos n| ≤ |f n - u₀cos n| := this
      linarith
    exact htri
  -- per-point bound: `|realSlice t x − u₀ x| ≤ D t`, uniformly in `x`
  have hpt : ∀ x : intervalDomainPoint,
      |realSlice u_star t x - u₀ x| ≤ D t := by
    intro x
    have hxIcc : (x.1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := x.2
    have hlift : intervalDomainLift (realSlice u_star t) x.1 = realSlice u_star t x := by
      rw [intervalDomainLift, dif_pos hxIcc]
      congr 1
    have hseries := hrealizes t htIoo x.1 hxIcc
    rw [hlift] at hseries
    -- termwise-summable cosine series (source side and datum side)
    have hsrc_sum : Summable (fun n => f n * cosineMode n x.1) := by
      refine (hf_l1.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)).of_abs
      rw [abs_mul, cosineMode]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
    have hdat_sum : Summable (fun n => u₀cos n * cosineMode n x.1) := by
      refine (hu0cos.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)).of_abs
      rw [abs_mul, cosineMode]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
    -- combine into one cosine synthesis of the defect coefficients
    have hcombine :
        realSlice u_star t x - u₀ x
          = ∑' n, (f n - u₀cos n) * cosineMode n x.1 := by
      rw [hseries, hrecon x]
      rw [show (fun n => (f n - u₀cos n) * cosineMode n x.1)
          = (fun n => f n * cosineMode n x.1 + (-(u₀cos n * cosineMode n x.1))) from
        funext (fun n => by ring)]
      rw [Summable.tsum_add hsrc_sum hdat_sum.neg, tsum_neg]
      ring
    rw [hcombine]
    have := abs_cosineSynthesis_le_tsum_abs (fun n => f n - u₀cos n) x.1 (hdefect t htIoo)
    simpa [hD, hf] using this
  -- envelope: the sup-norm is ≤ D t < ε / 2 < ε
  haveI : Nonempty intervalDomainPoint := ⟨⟨0, by constructor <;> norm_num⟩⟩
  change intervalDomainSupNorm (fun x => realSlice u_star t x - u₀ x) < ε
  unfold intervalDomainSupNorm
  have hle : sSup (Set.range (fun x : intervalDomainPoint =>
      |realSlice u_star t x - u₀ x|)) ≤ D t := by
    apply csSup_le (Set.range_nonempty _)
    rintro y ⟨x, rfl⟩
    exact hpt x
  linarith

end ShenWork.EWA

#print axioms ShenWork.EWA.realSlice_initialTrace
