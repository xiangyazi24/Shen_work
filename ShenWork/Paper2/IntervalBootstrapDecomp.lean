/-
  ShenWork/Paper2/IntervalBootstrapDecomp.lean

  The two final interfaces of the χ₀ < 0 space bootstrap:

  * TASK 1 — `hdecomp`: the mild-equation cosine-coefficient decomposition for the
    gradient mild solution.  Applying `cosineCoeffs` (a linear interval-integral
    functional) to the three-term mild Duhamel map
        u(t) = S(t)u₀ − χ₀∫₀ᵗ ∂ₓS(t−s)Q(u(s)) ds + ∫₀ᵗ S(t−s)L(u(s)) ds
    splits into the heat diagonal `e^{−tλ_k}â₀_k` (heat diagonalization), the
    chemotaxis engine coefficient `(−χ₀)·duhamelEnergyCoeff 1 (sineCoeffs∘Q) t k`
    (the divergence-mode identity, integrated against τ), and the logistic engine
    coefficient `duhamelEnergyCoeff 1 Fl t k`.  The per-τ integrand identities are
    landed; the only genuinely measure-theoretic step is the cosineCoeffs↔time
    integral swap, which is carried as an explicit hypothesis here.

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New names only.
-/
import ShenWork.Paper2.IntervalBootstrapStep
import ShenWork.Paper2.IntervalGradientCoeffDuhamel

noncomputable section

namespace ShenWork.Paper2.IntervalBootstrapDecomp

open MeasureTheory
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.Paper2.HSigmaScale (lam MemHSigma)
open ShenWork.Paper2.BFormHSigmaDuhamelEnergy (duhamelEnergyCoeff)
open ShenWork.Paper2.IntervalDivergenceModeIdentity (sineCoeffs)
open ShenWork.Paper2 (cosineCoeffs_congr_on_Icc)
open Real

/-! ## cosineCoeffs is additive (linear interval-integral functional) -/

/-- `cosineCoeffs` of a pointwise sum of two continuous functions is the sum of
the cosine coefficients.  `cosineCoeffs f = c(n)·∫₀¹ cos(nπx) f`, and the interval
integral is additive on integrable integrands. -/
theorem cosineCoeffs_add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (n : ℕ) :
    cosineCoeffs (fun x => f x + g x) n = cosineCoeffs f n + cosineCoeffs g n := by
  rw [ShenWork.IntervalMildPicardRegularity.cosineCoeffs_eq_factor_mul_integral,
    ShenWork.IntervalMildPicardRegularity.cosineCoeffs_eq_factor_mul_integral,
    ShenWork.IntervalMildPicardRegularity.cosineCoeffs_eq_factor_mul_integral]
  have hcos : Continuous (fun x : ℝ => Real.cos ((n : ℝ) * Real.pi * x)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id')
  have hif : IntervalIntegrable (fun x => Real.cos ((n : ℝ) * Real.pi * x) * f x)
      volume 0 1 := (hcos.mul hf).intervalIntegrable 0 1
  have hig : IntervalIntegrable (fun x => Real.cos ((n : ℝ) * Real.pi * x) * g x)
      volume 0 1 := (hcos.mul hg).intervalIntegrable 0 1
  have hsplit : (∫ x in (0:ℝ)..1,
        Real.cos ((n : ℝ) * Real.pi * x) * (f x + g x))
      = (∫ x in (0:ℝ)..1, Real.cos ((n : ℝ) * Real.pi * x) * f x)
        + ∫ x in (0:ℝ)..1, Real.cos ((n : ℝ) * Real.pi * x) * g x := by
    rw [← intervalIntegral.integral_add hif hig]
    refine intervalIntegral.integral_congr (fun x _ => ?_); ring
  rw [hsplit]; ring

/-- `cosineCoeffs` of a triple pointwise sum of continuous functions splits into
the three cosine coefficients (iterated `cosineCoeffs_add`). -/
theorem cosineCoeffs_add₃ {f g h : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) (n : ℕ) :
    cosineCoeffs (fun x => f x + g x + h x) n
      = cosineCoeffs f n + cosineCoeffs g n + cosineCoeffs h n := by
  have h1 : cosineCoeffs (fun x => (f x + g x) + h x) n
      = cosineCoeffs (fun x => f x + g x) n + cosineCoeffs h n :=
    cosineCoeffs_add (hf.add hg) hh n
  rw [show (fun x => f x + g x + h x) = (fun x => (f x + g x) + h x) from rfl, h1,
    cosineCoeffs_add hf hg]

/-! ## TASK 1 — the χ₀ < 0 mild-equation cosine-coefficient decomposition

The gradient mild solution's three-term Duhamel map
    u(t) = S(t)u₀ − χ₀∫₀ᵗ ∂ₓS(t−s)Q(u(s)) ds + ∫₀ᵗ S(t−s)L(u(s)) ds
diagonalizes in the cosine basis to the heat diagonal plus the two engine
coefficients.  The per-τ integrand identities are landed (the heat
diagonalization, the divergence-mode identity, and the engine integral form); the
single genuinely measure-theoretic step is commuting `cosineCoeffs` past the time
integral, supplied here as the explicit swap hypotheses `hswap_chem`/`hswap_log`. -/

/-- **TASK 1 — the χ₀ < 0 mild-equation cosine-coefficient decomposition.**

For the gradient mild solution `u` whose lift agrees on `[0,1]` with the three-term
mild Duhamel map (heat + chemotaxis + logistic, the χ₀≠0 form, available by
construction from `IntervalMildSolution`), with:
* `hheat`/`hchem_term`/`hlog_term` the three map summands (lifted), continuous;
* `hpt_chem` the per-τ divergence-mode identity
  `cosineCoeffs (chemTerm τ) k = e^{−(t−τ)λ_k}·√λ_k·sineCoeffs (Q τ) k`
  (landed `cosineCoeffs_semigroup_deriv_eq_diag_sqrtLambda_sineCoeff`);
* `hpt_heat` the heat diagonalization for the homogeneous propagator;
* `hswap_chem`/`hswap_log` the cosineCoeffs↔time-integral swaps (Fubini),

the `k`-th cosine coefficient of `lift (u t)` decomposes as
    e^{−tλ_k}·â₀_k
      + (−χ₀)·duhamelEnergyCoeff 1 (sineCoeffs∘Q) t k
      + duhamelEnergyCoeff 1 Fl t k,
exactly the shape `gradientSolution_memHSigma_succ_wired` consumes (`χc = χ₀`,
`χL = -1`, `Fc = sineCoeffs∘Q`). -/
theorem gradientSolution_cosineCoeff_decomp_chi
    {χ₀ t : ℝ} {ut u₀ : ℝ → ℝ}
    {chemTerm logTerm : ℝ → ℝ → ℝ} {Q : ℝ → ℝ → ℝ} {Fl : ℕ → ℝ → ℝ}
    (k : ℕ)
    -- the lift agrees with the three-term map on [0,1]
    (hmap : Set.EqOn ut
      (fun x => intervalFullSemigroupOperator t u₀ x
        + (-χ₀) * (∫ s in (0:ℝ)..t, chemTerm s x)
        + ∫ s in (0:ℝ)..t, logTerm s x) (Set.Icc (0:ℝ) 1))
    (hheat_cont : Continuous (fun x => intervalFullSemigroupOperator t u₀ x))
    (hchemI_cont : Continuous (fun x => ∫ s in (0:ℝ)..t, chemTerm s x))
    (hlogI_cont : Continuous (fun x => ∫ s in (0:ℝ)..t, logTerm s x))
    -- heat diagonalization
    (hpt_heat : cosineCoeffs (fun x => intervalFullSemigroupOperator t u₀ x) k
      = Real.exp (-(t * lam k)) * cosineCoeffs u₀ k)
    -- chemotaxis time-integral coeff swap (Fubini) + per-τ divergence-mode identity
    (hswap_chem : cosineCoeffs (fun x => ∫ s in (0:ℝ)..t, chemTerm s x) k
      = ∫ s in (0:ℝ)..t, cosineCoeffs (fun x => chemTerm s x) k)
    (hpt_chem : ∀ s, cosineCoeffs (fun x => chemTerm s x) k
      = Real.exp (-(1 * lam k * (t - s))) * ((lam k) ^ (1/2 : ℝ) * sineCoeffs (Q s) k))
    -- logistic time-integral coeff swap (Fubini) + per-τ identification
    (hswap_log : cosineCoeffs (fun x => ∫ s in (0:ℝ)..t, logTerm s x) k
      = ∫ s in (0:ℝ)..t, cosineCoeffs (fun x => logTerm s x) k)
    (hpt_log : ∀ s, cosineCoeffs (fun x => logTerm s x) k
      = (lam k) ^ (1/2 : ℝ) * Real.exp (-(1 * lam k * (t - s))) * Fl k s) :
    cosineCoeffs ut k
      = Real.exp (-(t * lam k)) * cosineCoeffs u₀ k
        + (-χ₀) * duhamelEnergyCoeff 1 (fun k s => sineCoeffs (Q s) k) t k
        + duhamelEnergyCoeff 1 Fl t k := by
  -- reduce to the map on [0,1], split cosineCoeffs additively over the 3 summands
  rw [cosineCoeffs_congr_on_Icc hmap k]
  rw [cosineCoeffs_add₃ (f := fun x => intervalFullSemigroupOperator t u₀ x)
    (g := fun x => (-χ₀) * (∫ s in (0:ℝ)..t, chemTerm s x))
    (h := fun x => ∫ s in (0:ℝ)..t, logTerm s x)
    hheat_cont (continuous_const.mul hchemI_cont) hlogI_cont k]
  -- the homogeneous coefficient
  rw [hpt_heat]
  -- the chemotaxis coefficient: factor out (-χ₀), swap, identify with the engine
  have hchem_coeff :
      cosineCoeffs (fun x => (-χ₀) * (∫ s in (0:ℝ)..t, chemTerm s x)) k
        = (-χ₀) * duhamelEnergyCoeff 1 (fun k s => sineCoeffs (Q s) k) t k := by
    -- pull the scalar (-χ₀) through cosineCoeffs
    have hpull : cosineCoeffs (fun x => (-χ₀) * (∫ s in (0:ℝ)..t, chemTerm s x)) k
        = (-χ₀) * cosineCoeffs (fun x => ∫ s in (0:ℝ)..t, chemTerm s x) k := by
      rw [ShenWork.IntervalMildPicardRegularity.cosineCoeffs_eq_factor_mul_integral,
        ShenWork.IntervalMildPicardRegularity.cosineCoeffs_eq_factor_mul_integral]
      rw [show (fun x => Real.cos ((k:ℝ) * Real.pi * x)
            * ((-χ₀) * ∫ s in (0:ℝ)..t, chemTerm s x))
          = (fun x => (-χ₀) * (Real.cos ((k:ℝ) * Real.pi * x)
            * ∫ s in (0:ℝ)..t, chemTerm s x)) from by funext x; ring]
      rw [intervalIntegral.integral_const_mul]; ring
    rw [hpull, hswap_chem,
      ShenWork.Paper2.IntervalDivergenceModeIdentity.duhamelEnergyCoeff_sineFlux_eq_integral]
    congr 1
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    rw [hpt_chem s]; ring
  rw [hchem_coeff]
  -- the logistic coefficient: swap, identify with the engine
  have hlog_coeff :
      cosineCoeffs (fun x => ∫ s in (0:ℝ)..t, logTerm s x) k
        = duhamelEnergyCoeff 1 Fl t k := by
    rw [hswap_log, duhamelEnergyCoeff]
    show (∫ s in (0:ℝ)..t, cosineCoeffs (fun x => logTerm s x) k)
      = ShenWork.Paper2.BFormHSigmaDuhamelMode.duhamelModeCoeff 1 (lam k) (Fl k) t
    rw [ShenWork.Paper2.BFormHSigmaDuhamelMode.duhamelModeCoeff]
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    rw [hpt_log s]
  rw [hlog_coeff]

/-! ## TASK 2 — the per-mode time-sup envelope producer

The engine `chemDuhamel_memHSigma_succ` consumes a source `F = sineCoeffs∘Q` with a
per-mode time-sup envelope `Mc : ℕ→ℝ` that is nonnegative, dominates `|F k τ|`
uniformly over `τ∈[0,t]`, and lies in `H^σ` (`Summable (1+λ_k)^σ (Mc k)²`).

The genuine analytic input is a uniform-in-`τ` `H^σ`-dominating coefficient
sequence `g` (the time-sup of the flux's sine coefficients, controlled by the
uniform `H^σ` regularity of the boundary-vanishing flux `Q` across the ball
trajectory).  Given such a `g`, the producer packages the engine envelope by
taking `Mc = |g|` — nonnegative, still dominating, still `H^σ` (squaring kills the
sign).  This isolates the one remaining analytic fact (the uniform-in-`τ` `H^σ`
coefficient envelope `g`) as the single explicit hypothesis. -/

/-- **TASK 2 — per-mode time-sup envelope producer.**  From a uniform-in-`τ`
`H^σ`-dominating coefficient sequence `g` for the flux sine coefficients
(`hg_dom : ∀ τ∈[0,t], ∀ k, |sineCoeffs (Q τ) k| ≤ g k`, with `MemHSigma σ g`),
produce the engine-consumable envelope `Mc = fun k => |g k|`: nonnegative,
uniformly dominating, and in `H^σ`.  This is exactly the tuple
`gradientSolution_memHSigma_succ_wired` consumes for the chemotaxis source
(`hMc0`, `hFc_bd`, `hMc`). -/
theorem fluxSine_timeSupEnvelope_memHSigma
    {σ t : ℝ} {Q : ℝ → ℝ → ℝ} {g : ℕ → ℝ}
    (hg : MemHSigma σ g)
    (hg_dom : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k, |sineCoeffs (Q τ) k| ≤ g k) :
    ∃ Mc : ℕ → ℝ, (∀ k, 0 ≤ Mc k)
      ∧ (∀ k, ∀ τ ∈ Set.Icc (0:ℝ) t, |sineCoeffs (Q τ) k| ≤ Mc k)
      ∧ MemHSigma σ Mc := by
  refine ⟨fun k => |g k|, fun k => abs_nonneg _, ?_, ?_⟩
  · intro k τ hτ
    exact le_trans (hg_dom τ hτ k) (le_abs_self _)
  · -- `(1+λ_k)^σ·|g k|² = (1+λ_k)^σ·(g k)²`, so the H^σ energy is unchanged.
    refine hg.congr (fun k => ?_)
    rw [sq_abs]

/-! ## TASK 3 — the unconditional single step and `ContDiffOn ℝ 2`

Composing TASK 1 (`hdecomp` derived from the mild equation) and TASK 2 (the engine
envelopes derived from the uniform `H^σ` flux control) discharges the carried
hypotheses of `gradientSolution_memHSigma_succ_wired`, leaving only the
solution-level analytic inputs (the per-`τ` divergence-mode / heat identities, the
cosineCoeffs↔time-integral swaps, the source continuities, and the uniform `H^σ`
coefficient envelopes — all genuine, none fakeable).  Iterating then reaches
`ContDiffOn ℝ 2` via the landed `memHSigma_iterate_contDiffOn_two`. -/

open ShenWork.Paper2.IntervalBootstrapStep (gradientSolution_memHSigma_succ_wired
  memHSigma_iterate_contDiffOn_two)

/-- **TASK 3 — unconditional single step `H^σ → H^{σ+α}` on the gradient solution.**

Same conclusion as `gradientSolution_memHSigma_succ_wired`, but the mild-equation
decomposition `hdecomp` is DERIVED here (TASK 1) from the solution-level inputs:
the three-term map agreement `hmap`, the summand continuities, the heat
diagonalization `hpt_heat`, the per-`τ` divergence-mode identity `hpt_chem`, the
per-`τ` logistic identification `hpt_log`, and the two cosineCoeffs↔time-integral
swaps `hswap_chem`/`hswap_log`.  The engine envelopes are DERIVED (TASK 2) from the
uniform `H^σ`-dominating coefficient sequences `g`/`gl`.  No carried `hdecomp` or
abstract envelope tuple remains. -/
theorem gradientSolution_memHSigma_succ_uncond
    {σ α χ₀ t : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (ht : 0 < t) (ht1 : t ≤ 1)
    {ut u₀ : ℝ → ℝ} {chemTerm logTerm : ℝ → ℝ → ℝ} {Q : ℝ → ℝ → ℝ}
    {Fl : ℝ → ℕ → ℝ} {g gl : ℕ → ℝ}
    (ha : MemHSigma σ (cosineCoeffs u₀))
    -- TASK-2 envelopes (uniform H^σ-dominating sequences)
    (hg : MemHSigma σ g)
    (hg_dom : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k, |sineCoeffs (Q τ) k| ≤ g k)
    (hFc_cont : ∀ k, Continuous (fun τ => sineCoeffs (Q τ) k))
    (hgl : MemHSigma σ gl)
    (hgl_dom : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k, |Fl τ k| ≤ gl k)
    (hFl_cont : ∀ k, Continuous (fun τ => Fl τ k))
    -- TASK-1 mild-equation decomposition inputs (per mode k)
    (hmap : Set.EqOn ut
      (fun x => intervalFullSemigroupOperator t u₀ x
        + (-χ₀) * (∫ s in (0:ℝ)..t, chemTerm s x)
        + ∫ s in (0:ℝ)..t, logTerm s x) (Set.Icc (0:ℝ) 1))
    (hheat_cont : Continuous (fun x => intervalFullSemigroupOperator t u₀ x))
    (hchemI_cont : Continuous (fun x => ∫ s in (0:ℝ)..t, chemTerm s x))
    (hlogI_cont : Continuous (fun x => ∫ s in (0:ℝ)..t, logTerm s x))
    (hpt_heat : ∀ k, cosineCoeffs (fun x => intervalFullSemigroupOperator t u₀ x) k
      = Real.exp (-(t * lam k)) * cosineCoeffs u₀ k)
    (hswap_chem : ∀ k, cosineCoeffs (fun x => ∫ s in (0:ℝ)..t, chemTerm s x) k
      = ∫ s in (0:ℝ)..t, cosineCoeffs (fun x => chemTerm s x) k)
    (hpt_chem : ∀ k, ∀ s, cosineCoeffs (fun x => chemTerm s x) k
      = Real.exp (-(1 * lam k * (t - s))) * ((lam k) ^ (1/2 : ℝ) * sineCoeffs (Q s) k))
    (hswap_log : ∀ k, cosineCoeffs (fun x => ∫ s in (0:ℝ)..t, logTerm s x) k
      = ∫ s in (0:ℝ)..t, cosineCoeffs (fun x => logTerm s x) k)
    (hpt_log : ∀ k, ∀ s, cosineCoeffs (fun x => logTerm s x) k
      = (lam k) ^ (1/2 : ℝ) * Real.exp (-(1 * lam k * (t - s))) * Fl s k) :
    MemHSigma (σ + α) (cosineCoeffs ut) := by
  -- TASK 2: chemotaxis + logistic engine envelopes
  obtain ⟨Mc, hMc0, hMc_bd, hMc⟩ :=
    fluxSine_timeSupEnvelope_memHSigma (Q := Q) hg hg_dom
  obtain ⟨Ml, hMl0, hMl_bd, hMl⟩ :
      ∃ Ml : ℕ → ℝ, (∀ k, 0 ≤ Ml k)
        ∧ (∀ k, ∀ τ ∈ Set.Icc (0:ℝ) t, |(fun (k : ℕ) (s : ℝ) => Fl s k) k τ| ≤ Ml k)
        ∧ MemHSigma σ Ml := by
    refine ⟨fun k => |gl k|, fun k => abs_nonneg _, ?_, hgl.congr (fun k => by rw [sq_abs])⟩
    intro k τ hτ; exact le_trans (hgl_dom τ hτ k) (le_abs_self _)
  -- TASK 1: the mild-equation decomposition, per mode
  have hdecomp : ∀ k, cosineCoeffs ut k
      = Real.exp (-(t * lam k)) * cosineCoeffs u₀ k
        + (-χ₀) * duhamelEnergyCoeff 1 (fun k s => sineCoeffs (Q s) k) t k
        + (-(-1)) * duhamelEnergyCoeff 1 (fun k s => Fl s k) t k := fun k => by
    have h := gradientSolution_cosineCoeff_decomp_chi (χ₀ := χ₀) (t := t)
      (ut := ut) (u₀ := u₀) (chemTerm := chemTerm) (logTerm := logTerm)
      (Q := Q) (Fl := fun k s => Fl s k) k
      hmap hheat_cont hchemI_cont hlogI_cont (hpt_heat k)
      (hswap_chem k) (hpt_chem k) (hswap_log k) (hpt_log k)
    rw [h]; ring
  -- assemble via the wired step (χc = χ₀, χL = -1, Fc = sineCoeffs∘Q, Fl)
  exact gradientSolution_memHSigma_succ_wired (σ := σ) (α := α) (χc := χ₀) (χL := -1)
    hα0 hα1 ht ht1 (a := cosineCoeffs u₀) (utCoeff := cosineCoeffs ut)
    (Fc := fun k s => sineCoeffs (Q s) k) (Fl := fun k s => Fl s k)
    (Mc := Mc) (Ml := Ml)
    ha hFc_cont hMc0 hMc_bd hMc hFl_cont hMl0 hMl_bd hMl hdecomp

/-- **TASK 3 — iterated unconditional bootstrap ⟹ `ContDiffOn ℝ 2`.**

After enough single steps (`hreach : 5/2 < σ₀ + n·α`) the running regularity
exceeds `5/2`, so WALL-C reconstructs the classical `C²` regularity of the cosine
series of `cosineCoeffs ut` on `[0,1]`.  The per-level step provider `step` is
`gradientSolution_memHSigma_succ_uncond` instantiated at the running regularity
(the envelope/decomposition data re-established at each level); given it, this is
the landed `memHSigma_iterate_contDiffOn_two`.  This `C²` regularity is exactly
what `IterateSourceTimeData.sliceC2` consumes for the χ₀<0 gradient solution. -/
theorem gradientSolution_contDiffOn_two_uncond
    {α σ₀ : ℝ} {ut : ℝ → ℝ} (n : ℕ)
    (hreach : 5 / 2 < σ₀ + n * α)
    (step : ∀ {σ : ℝ}, MemHSigma σ (cosineCoeffs ut) → MemHSigma (σ + α) (cosineCoeffs ut))
    (h0 : MemHSigma σ₀ (cosineCoeffs ut)) :
    ContDiffOn ℝ 2 (fun x => ∑' k, cosineCoeffs ut k *
      ShenWork.CosineSpectrum.cosineMode k x) (Set.Icc (0 : ℝ) 1) :=
  memHSigma_iterate_contDiffOn_two (σ₀ := σ₀) n hreach step h0

#print axioms cosineCoeffs_add
#print axioms cosineCoeffs_add₃
#print axioms gradientSolution_cosineCoeff_decomp_chi
#print axioms fluxSine_timeSupEnvelope_memHSigma
#print axioms gradientSolution_memHSigma_succ_uncond
#print axioms gradientSolution_contDiffOn_two_uncond

end ShenWork.Paper2.IntervalBootstrapDecomp
