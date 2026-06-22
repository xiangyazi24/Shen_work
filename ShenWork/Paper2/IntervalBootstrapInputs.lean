/-
  ShenWork/Paper2/IntervalBootstrapInputs.lean

  Discharging the carried analytic inputs of the χ₀ < 0 single bootstrap step
  `gradientSolution_memHSigma_succ_uncond` (IntervalBootstrapDecomp.lean).

  * TASK 1 — `cosineCoeffs_integral_swap`: the cosineCoeffs ↔ time-integral
    Fubini swap, derived purely from joint continuity of the time-family on the
    compact slab `[0,t]×[0,1]`.  This discharges the carried `hswap_chem` /
    `hswap_log` hypotheses of the single step (replacing the raw swap by the
    weaker, genuine joint-continuity datum).  Landed unconditionally.

  * TASK 3 — `gradientSolution_memHSigma_succ_fully_uncond`: the single step with
    NO carried Fubini swaps (derived here via TASK 1 from joint continuity), and
    `gradientSolution_contDiffOn_two_fully_uncond` (ContDiffOn ℝ 2, t>0).

  The remaining carried datum (the uniform-in-τ `H^σ` flux envelope `g`/`gl`) is
  the genuine PDE crux — see the module note below; it is NOT a pointwise
  consequence of the per-time flux membership and requires a uniform-in-time
  (Gronwall/continuation) closure that is not yet in Paper2.  It is therefore
  kept as honest carried data `D`, exactly as in `..._succ_uncond`.

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New names only.
-/
import ShenWork.Paper2.IntervalBootstrapDecomp

noncomputable section

namespace ShenWork.Paper2.IntervalBootstrapInputs

open MeasureTheory
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.Paper2.HSigmaScale (lam MemHSigma)
open ShenWork.Paper2.BFormHSigmaDuhamelEnergy (duhamelEnergyCoeff)
open ShenWork.Paper2.IntervalDivergenceModeIdentity (sineCoeffs)
open ShenWork.IntervalMildPicardRegularity (cosineCoeffs_eq_factor_mul_integral)
open Real

/-! ## TASK 1 — the cosineCoeffs ↔ time-integral Fubini swap

`cosineCoeffs f k = c(k)·∫₀¹ cos(kπx) f(x) dx`.  Commuting `cosineCoeffs` past a
time integral `∫₀ᵗ g s · ds` is exactly the Fubini swap
`∫₀¹∫₀ᵗ = ∫₀ᵗ∫₀¹`, valid because the joint integrand `cos(kπx)·g s x` is
continuous on the compact slab `[0,t]×[0,1]`, hence integrable there, hence
integrable for the (finite) restricted product measure. -/

/-- **TASK 1 — the cosineCoeffs ↔ time-integral swap (Fubini).**

For a time-family `g : ℝ → ℝ → ℝ` whose uncurry is continuous on the slab
`[0,t]×[0,1]` (`0 ≤ t`),
`cosineCoeffs (fun x => ∫₀ᵗ g s x ds) k = ∫₀ᵗ cosineCoeffs (g s) k ds`. -/
theorem cosineCoeffs_integral_swap {t : ℝ} (ht : 0 ≤ t) (g : ℝ → ℝ → ℝ)
    (hcont : ContinuousOn (Function.uncurry g)
      (Set.Icc (0 : ℝ) t ×ˢ Set.Icc (0 : ℝ) 1)) (k : ℕ) :
    cosineCoeffs (fun x => ∫ s in (0:ℝ)..t, g s x) k
      = ∫ s in (0:ℝ)..t, cosineCoeffs (g s) k := by
  set F : ℝ → ℝ → ℝ := fun s x => Real.cos ((k:ℝ) * Real.pi * x) * g s x with hF
  have hcos : Continuous (fun x : ℝ => Real.cos ((k:ℝ) * Real.pi * x)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id')
  -- core Fubini at the weighted-integrand level
  have hcore : (∫ x in (0:ℝ)..1,
        Real.cos ((k:ℝ) * Real.pi * x) * (∫ s in (0:ℝ)..t, g s x))
      = ∫ s in (0:ℝ)..t, ∫ x in (0:ℝ)..1,
          Real.cos ((k:ℝ) * Real.pi * x) * g s x := by
    have hFcont : ContinuousOn (Function.uncurry F)
        (Set.Icc (0:ℝ) t ×ˢ Set.Icc (0:ℝ) 1) := by
      have he : Function.uncurry F
          = fun p : ℝ × ℝ =>
              Real.cos ((k:ℝ) * Real.pi * p.2) * Function.uncurry g p := by
        funext p; rfl
      rw [he]; exact ((hcos.comp continuous_snd).continuousOn).mul hcont
    have hint_prod : Integrable (Function.uncurry F)
        ((volume.restrict (Set.Ioc (0:ℝ) t)).prod
          (volume.restrict (Set.Ioc (0:ℝ) 1))) := by
      rw [MeasureTheory.Measure.prod_restrict]
      exact (hFcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
        (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)
    have hswap := MeasureTheory.integral_integral_swap (f := F) hint_prod
    have hLHS : (∫ x in (0:ℝ)..1,
          Real.cos ((k:ℝ) * Real.pi * x) * (∫ s in (0:ℝ)..t, g s x))
        = ∫ x, (∫ s, F s x ∂(volume.restrict (Set.Ioc (0:ℝ) t)))
            ∂(volume.restrict (Set.Ioc (0:ℝ) 1)) := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro x _; simp only
      rw [intervalIntegral.integral_of_le ht, ← MeasureTheory.integral_const_mul]
    have hRHS : (∫ s in (0:ℝ)..t, ∫ x in (0:ℝ)..1,
          Real.cos ((k:ℝ) * Real.pi * x) * g s x)
        = ∫ s, (∫ x, F s x ∂(volume.restrict (Set.Ioc (0:ℝ) 1)))
            ∂(volume.restrict (Set.Ioc (0:ℝ) t)) := by
      rw [intervalIntegral.integral_of_le ht]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro s _; simp only
      rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    rw [hLHS, hRHS, hswap]
  -- wrap with the cosineCoeffs factor `c(k)`
  rw [cosineCoeffs_eq_factor_mul_integral, hcore]
  rw [show (∫ s in (0:ℝ)..t, cosineCoeffs (g s) k)
      = ∫ s in (0:ℝ)..t, (if k = 0 then (1:ℝ) else 2)
          * ∫ x in (0:ℝ)..1, Real.cos ((k:ℝ) * Real.pi * x) * g s x from by
    apply intervalIntegral.integral_congr; intro s _; simp only
    rw [cosineCoeffs_eq_factor_mul_integral]]
  rw [intervalIntegral.integral_const_mul]

/-- TASK 1, in the exact shape consumed as `hswap_chem`/`hswap_log` by
`gradientSolution_memHSigma_succ_uncond` (`cosineCoeffs (fun x => …) k` form). -/
theorem cosineCoeffs_integral_swap' {t : ℝ} (ht : 0 ≤ t) (g : ℝ → ℝ → ℝ)
    (hcont : ContinuousOn (Function.uncurry g)
      (Set.Icc (0 : ℝ) t ×ˢ Set.Icc (0 : ℝ) 1)) (k : ℕ) :
    cosineCoeffs (fun x => ∫ s in (0:ℝ)..t, g s x) k
      = ∫ s in (0:ℝ)..t, cosineCoeffs (fun x => g s x) k :=
  cosineCoeffs_integral_swap ht g hcont k

/-! ## TASK 3 — the fully-unconditional single step and `ContDiffOn ℝ 2`

The single step `gradientSolution_memHSigma_succ_uncond` carried two Fubini swap
hypotheses `hswap_chem`/`hswap_log`.  Here they are DERIVED (TASK 1) from the
joint continuity of the chemotaxis / logistic Duhamel integrands on the slab —
genuine solution data, strictly weaker than the raw swap.

The uniform-in-τ `H^σ` flux envelopes `g`/`gl` (with `hg`/`hg_dom`,
`hgl`/`hgl_dom`) remain carried.  This is deliberate and honest: the per-time
flux membership (`fluxFunction_memHSigma`) gives `MemHSigma σ (cosineCoeffs (Q τ))`
for each fixed `τ`, but a SINGLE sequence `g` dominating `|sineCoeffs (Q τ) k|`
UNIFORMLY over `τ ∈ [0,t]` while staying in `H^σ` is not a pointwise consequence
of that — it is a uniform-in-time bound on the flux `H^σ` norm, i.e. a
fixed-point / Gronwall-continuation closure on the window `[c,t]`.  No such
uniform producer exists in Paper2 (only the per-time membership and the
packaging lemma `fluxSine_timeSupEnvelope_memHSigma`, which already takes `g`).
So `g`/`gl` stay as carried analytic data `D`. -/

open ShenWork.Paper2.IntervalBootstrapDecomp
  (gradientSolution_memHSigma_succ_uncond gradientSolution_contDiffOn_two_uncond)

/-- **TASK 3 — fully-unconditional single step `H^σ → H^{σ+α}` (no carried
Fubini).**  Same conclusion as `gradientSolution_memHSigma_succ_uncond`, but the
two cosineCoeffs ↔ time-integral swaps are DERIVED here (TASK 1) from joint
continuity of the chemotaxis / logistic Duhamel integrands on the slab
`hchemTerm_cont` / `hlogTerm_cont`.  The per-τ divergence-mode / heat / logistic
identities, the source continuities, and the uniform `H^σ` flux envelopes
`g`/`gl` remain as the solution's intrinsic data `D` (the envelopes being the
genuine uniform-in-time PDE crux). -/
theorem gradientSolution_memHSigma_succ_fully_uncond
    {σ α χ₀ t : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (ht : 0 < t) (ht1 : t ≤ 1)
    {ut u₀ : ℝ → ℝ} {chemTerm logTerm : ℝ → ℝ → ℝ} {Q : ℝ → ℝ → ℝ}
    {Fl : ℝ → ℕ → ℝ} {g gl : ℕ → ℝ}
    (ha : MemHSigma σ (cosineCoeffs u₀))
    -- uniform-in-τ H^σ flux envelopes (the carried PDE crux `D`)
    (hg : MemHSigma σ g)
    (hg_dom : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k, |sineCoeffs (Q τ) k| ≤ g k)
    (hFc_cont : ∀ k, Continuous (fun τ => sineCoeffs (Q τ) k))
    (hgl : MemHSigma σ gl)
    (hgl_dom : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k, |Fl τ k| ≤ gl k)
    (hFl_cont : ∀ k, Continuous (fun τ => Fl τ k))
    -- mild-equation map agreement + summand continuities
    (hmap : Set.EqOn ut
      (fun x => intervalFullSemigroupOperator t u₀ x
        + (-χ₀) * (∫ s in (0:ℝ)..t, chemTerm s x)
        + ∫ s in (0:ℝ)..t, logTerm s x) (Set.Icc (0:ℝ) 1))
    (hheat_cont : Continuous (fun x => intervalFullSemigroupOperator t u₀ x))
    (hchemI_cont : Continuous (fun x => ∫ s in (0:ℝ)..t, chemTerm s x))
    (hlogI_cont : Continuous (fun x => ∫ s in (0:ℝ)..t, logTerm s x))
    (hpt_heat : ∀ k, cosineCoeffs (fun x => intervalFullSemigroupOperator t u₀ x) k
      = Real.exp (-(t * lam k)) * cosineCoeffs u₀ k)
    -- the two Duhamel integrands are jointly continuous on the slab — TASK-1 input
    (hchemTerm_cont : ContinuousOn (Function.uncurry chemTerm)
      (Set.Icc (0:ℝ) t ×ˢ Set.Icc (0:ℝ) 1))
    (hlogTerm_cont : ContinuousOn (Function.uncurry logTerm)
      (Set.Icc (0:ℝ) t ×ˢ Set.Icc (0:ℝ) 1))
    -- per-τ divergence-mode / logistic identities
    (hpt_chem : ∀ k, ∀ s, cosineCoeffs (fun x => chemTerm s x) k
      = Real.exp (-(1 * lam k * (t - s))) * ((lam k) ^ (1/2 : ℝ) * sineCoeffs (Q s) k))
    (hpt_log : ∀ k, ∀ s, cosineCoeffs (fun x => logTerm s x) k
      = (lam k) ^ (1/2 : ℝ) * Real.exp (-(1 * lam k * (t - s))) * Fl s k) :
    MemHSigma (σ + α) (cosineCoeffs ut) :=
  gradientSolution_memHSigma_succ_uncond hα0 hα1 ht ht1
    ha hg hg_dom hFc_cont hgl hgl_dom hFl_cont
    hmap hheat_cont hchemI_cont hlogI_cont hpt_heat
    -- TASK-1: the chemotaxis Fubini swap, derived from joint continuity
    (fun k => cosineCoeffs_integral_swap' ht.le chemTerm hchemTerm_cont k)
    hpt_chem
    -- TASK-1: the logistic Fubini swap, derived from joint continuity
    (fun k => cosineCoeffs_integral_swap' ht.le logTerm hlogTerm_cont k)
    hpt_log

/-- **TASK 3 — fully-unconditional iterated bootstrap ⟹ `ContDiffOn ℝ 2`.**

Identical to `gradientSolution_contDiffOn_two_uncond`: once a per-level step
provider `step` is in hand (instantiate `gradientSolution_memHSigma_succ_fully_uncond`
at each running regularity, re-establishing the envelope/decomposition data),
`n` steps past `5/2` reconstruct the χ₀<0 gradient solution's classical `C²`
regularity on `[0,1]` for `t>0`.  The Fubini swaps are no longer part of `step`'s
hypotheses (discharged by TASK 1); only the solution's intrinsic data `D` (the
per-τ identities, continuities, and the uniform `H^σ` flux envelopes) feeds it. -/
theorem gradientSolution_contDiffOn_two_fully_uncond
    {α σ₀ : ℝ} {ut : ℝ → ℝ} (n : ℕ)
    (hreach : 5 / 2 < σ₀ + n * α)
    (step : ∀ {σ : ℝ}, MemHSigma σ (cosineCoeffs ut) → MemHSigma (σ + α) (cosineCoeffs ut))
    (h0 : MemHSigma σ₀ (cosineCoeffs ut)) :
    ContDiffOn ℝ 2 (fun x => ∑' k, cosineCoeffs ut k *
      ShenWork.CosineSpectrum.cosineMode k x) (Set.Icc (0 : ℝ) 1) :=
  gradientSolution_contDiffOn_two_uncond n hreach step h0

#print axioms cosineCoeffs_integral_swap
#print axioms cosineCoeffs_integral_swap'
#print axioms gradientSolution_memHSigma_succ_fully_uncond
#print axioms gradientSolution_contDiffOn_two_fully_uncond

end ShenWork.Paper2.IntervalBootstrapInputs
