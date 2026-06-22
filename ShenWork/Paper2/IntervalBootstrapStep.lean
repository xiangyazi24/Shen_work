import ShenWork.Paper2.IntervalC2BootstrapHalfStep
import ShenWork.Paper2.IntervalDivergenceModeIdentity
import ShenWork.Paper2.IntervalCosineSobolevEmbedding
import ShenWork.PDE.IntervalCosineSliceRegularity
import ShenWork.Paper2.IntervalWienerAlgebraFlux
import ShenWork.Paper2.IntervalWienerAlgebraConnect
import ShenWork.Paper2.IntervalDomainLemma21

/-!
# `IntervalBootstrapStep` — the single-step Sobolev bootstrap on the gradient mild solution

This file assembles THE CRUX of the `χ₀ < 0` boundedness closure: the one
half-derivative Sobolev gain on the gradient mild solution's cosine
coefficients, wiring together every landed analytic piece.
-/

noncomputable section

namespace ShenWork.Paper2.IntervalBootstrapStep

open ShenWork.Paper2.HSigmaScale
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalC2Bootstrap
open ShenWork.Paper2.BFormHSigmaDuhamelEnergy (duhamelEnergyCoeff)
open ShenWork.Paper2.IntervalDomainLemma21 (heat_time_multiplier_smoothing_le)
open Real

/-! ## Heat-part super-smoothing: the diagonal `e^{−tλ_k}` gains any `ρ ∈ (0,1]`. -/

/-- The polynomial-times-exponential spectral bound `(1+λ)^ρ e^{−tλ} ≤ 1 + t^{−ρ}`
for `0 < ρ ≤ 1`, `t > 0`, `λ ≥ 0`.  Subadditivity `(1+λ)^ρ ≤ 1 + λ^ρ` plus the
landed smoothing multiplier `λ^ρ e^{−tλ} ≤ t^{−ρ}`. -/
theorem oneAddLam_rpow_mul_exp_le {ρ t : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (ht : 0 < t) (k : ℕ) :
    (1 + lam k) ^ ρ * Real.exp (-(t * lam k)) ≤ 1 + t ^ (-ρ) := by
  have hlam := lam_nonneg k
  have hsub : (1 + lam k) ^ ρ ≤ 1 + (lam k) ^ ρ := by
    have h := Real.rpow_add_le_add_rpow hlam (zero_le_one) hρ0.le hρ1
    rw [one_rpow] at h
    rw [add_comm 1 (lam k), add_comm 1 ((lam k) ^ ρ)]; exact h
  have hexp1 : Real.exp (-(t * lam k)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by have := mul_nonneg ht.le hlam; linarith)
  have hexp_nonneg : 0 ≤ Real.exp (-(t * lam k)) := (Real.exp_pos _).le
  rcases eq_or_lt_of_le hlam with hlam0 | hlampos
  · -- λ_k = 0: LHS = 1·exp(0) = 1 ≤ 1 + t^{-ρ}.
    rw [← hlam0]
    simp only [mul_zero, neg_zero, Real.exp_zero, mul_one, add_zero, Real.one_rpow]
    have : 0 ≤ t ^ (-ρ) := (Real.rpow_pos_of_pos ht _).le
    linarith
  · have hsmooth : (lam k) ^ ρ * Real.exp (-(t * lam k)) ≤ t ^ (-ρ) :=
      heat_time_multiplier_smoothing_le hlampos ht hρ0.le hρ1
    calc (1 + lam k) ^ ρ * Real.exp (-(t * lam k))
        ≤ (1 + (lam k) ^ ρ) * Real.exp (-(t * lam k)) :=
          mul_le_mul_of_nonneg_right hsub hexp_nonneg
      _ = Real.exp (-(t * lam k)) + (lam k) ^ ρ * Real.exp (-(t * lam k)) := by ring
      _ ≤ 1 + t ^ (-ρ) := by linarith [hsmooth, hexp1]

/-- **Heat-part super-smoothing.**  If the datum coefficients `a` lie in `H^σ`,
then the heat-propagated diagonal coefficients `e^{−tλ_k} a_k` lie in `H^{σ+ρ}`
for every `0 < ρ ≤ 1`, `t > 0` (the parabolic semigroup is infinitely smoothing
for positive time). -/
theorem heatDiag_memHSigma_succ {σ ρ t : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (ht : 0 < t)
    {a : ℕ → ℝ} (ha : MemHSigma σ a) :
    MemHSigma (σ + ρ) (fun k => Real.exp (-(t * lam k)) * a k) := by
  set K := 1 + t ^ (-ρ) with hKdef
  have hKnn : 0 ≤ K := by
    rw [hKdef]; have : 0 ≤ t ^ (-ρ) := (Real.rpow_pos_of_pos ht _).le; linarith
  have hdom : ∀ k, (1 + lam k) ^ (σ + ρ) * (Real.exp (-(t * lam k)) * a k) ^ 2 ≤
      K * ((1 + lam k) ^ σ * (a k) ^ 2) := by
    intro k
    have h1pos := one_add_lam_pos k
    -- (1+λ)^{σ+ρ} = (1+λ)^σ · (1+λ)^ρ
    have hpow : (1 + lam k) ^ (σ + ρ) = (1 + lam k) ^ σ * (1 + lam k) ^ ρ :=
      Real.rpow_add h1pos σ ρ
    have hexp_sq : (Real.exp (-(t * lam k)) * a k) ^ 2
        = Real.exp (-(2 * t * lam k)) * (a k) ^ 2 := by
      have he : (Real.exp (-(t * lam k))) ^ 2 = Real.exp (-(2 * t * lam k)) := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      rw [mul_pow, he]
    rw [hpow, hexp_sq]
    -- group: (1+λ)^σ a² · [(1+λ)^ρ e^{−2tλ}] ≤ (1+λ)^σ a² · K
    have hbracket : (1 + lam k) ^ ρ * Real.exp (-(2 * t * lam k)) ≤ K := by
      have h2 := oneAddLam_rpow_mul_exp_le hρ0 hρ1 (by linarith : (0:ℝ) < 2 * t) k
      rw [show 2 * t * lam k = (2*t) * lam k by ring] at h2
      -- (2t)^{-ρ} ≤ t^{-ρ} since 2t ≥ t > 0 and exponent is negative
      have hmono : (2 * t) ^ (-ρ) ≤ t ^ (-ρ) := by
        rw [Real.rpow_neg (by linarith), Real.rpow_neg ht.le]
        exact inv_anti₀ (Real.rpow_pos_of_pos ht _)
          (Real.rpow_le_rpow ht.le (by linarith) hρ0.le)
      rw [hKdef]; linarith [h2, hmono]
    have hcoef_nn : 0 ≤ (1 + lam k) ^ σ * (a k) ^ 2 := by
      have := Real.rpow_nonneg h1pos.le σ; positivity
    nlinarith [hbracket, hcoef_nn, mul_le_mul_of_nonneg_left hbracket hcoef_nn]
  have hnonneg : ∀ k, 0 ≤ (1 + lam k) ^ (σ + ρ) * (Real.exp (-(t * lam k)) * a k) ^ 2 := by
    intro k; have := Real.rpow_nonneg (one_add_lam_pos k).le (σ + ρ); positivity
  exact Summable.of_nonneg_of_le hnonneg hdom (ha.mul_left K)

/-! ## Flux-side producer (chain #1–2): `u·v_x·(1+v)^{−β} ∈ H^σ`.

The chemotaxis flux `φ = u · v_x · (1+v)^{−β}` is LINEAR in `u` (`m = 1`).  Its
cosine coefficients land in `H^σ` (`σ > 1/2`) once the three factor functions'
cosine coefficients do and the cosine-multiplication bridges hold.  The factor
memberships are supplied by the landed walls:
`u`-factor — the bootstrap input `MemHSigma σ (cosineCoeffs u)`;
`(1+v)^{−β}` — `chemotaxisFlux_denom_memHSigma_uncond` (`v ∈ C²` from the elliptic
gain `σ+2 > 5/2`, `v ≥ 0`, Neumann compatibility);
`v_x` — `MemHSigma σ (cosineCoeffs v_x)` (`H^{σ+1} ⊂ H^σ` from `v ∈ H^{σ+2}`).
The bridges are discharged by `cosineMulBridge_of_summable` (continuity + `ℓ¹`). -/
theorem fluxFunction_memHSigma {σ : ℝ} (hσ : 1 / 2 < σ)
    {u vx invDen : ℝ → ℝ}
    (hden_vx : ShenWork.Paper2.IntervalWienerAlgebra.CosineMulBridge invDen vx)
    (hu_rest : ShenWork.Paper2.IntervalWienerAlgebra.CosineMulBridge u
      (fun x => invDen x * vx x))
    (hu : MemHSigma σ (cosineCoeffs u))
    (hden : MemHSigma σ (cosineCoeffs invDen))
    (hvx : MemHSigma σ (cosineCoeffs vx)) :
    MemHSigma σ (cosineCoeffs (fun x => u x * (invDen x * vx x))) :=
  ShenWork.Paper2.IntervalWienerAlgebra.chemotaxisFlux_memHSigma_function
    hσ hden_vx hu_rest hu hden hvx

/-! ## Engine-side glue (chain #3): the chemotaxis-Duhamel coefficients gain `α`.

The chemotaxis Duhamel term's cosine coefficients are
`chemCoeff k = −χ₀ · duhamelEnergyCoeff 1 (sineCoeffs ∘ Q) t k` (WALL-B
chemotaxis, `chemotaxisDuhamel_cosineCoeff_eq_engine`).  Feeding the engine
`hSigmaEnergy_duhamel_bound_shifted` (source per-mode time-sup envelope `Msup` in
`H^r`) lands them in `H^{r+α}`, `0 ≤ α < 1`. -/
theorem chemDuhamel_memHSigma_succ {r α χ₀ d s : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hd : 0 < d) (hs : 0 < s) (hs1 : s ≤ 1)
    {F : ℕ → ℝ → ℝ} (hFcont : ∀ k, Continuous (F k))
    {Msup : ℕ → ℝ} (hMsup0 : ∀ k, 0 ≤ Msup k)
    (hFbd : ∀ k, ∀ τ ∈ Set.Icc (0 : ℝ) s, |F k τ| ≤ Msup k)
    (hMsq : Summable fun k => (1 + lam k) ^ r * (Msup k) ^ 2)
    {chemCoeff : ℕ → ℝ}
    (hchem : ∀ k, chemCoeff k = -χ₀ * duhamelEnergyCoeff d F s k) :
    MemHSigma (r + α) chemCoeff := by
  have heng := (hSigmaEnergy_duhamel_bound_shifted
    (r := r) hα0 hα1 hd hs hs1 hFcont hMsup0 hFbd hMsq).1
  -- chemCoeff = (-χ₀) • duhamelEnergyCoeff d F s, pointwise
  have hcongr : chemCoeff = fun k => (-χ₀) * duhamelEnergyCoeff d F s k := funext hchem
  rw [hcongr]
  exact ShenWork.Paper2.IntervalWienerAlgebra.memHSigma_smul (-χ₀) heng

/-! ## The assembly (chain #4): single-step `H^σ → H^{σ+ρ}` for the gradient solution.

The gradient mild solution's coefficient equation diagonalizes to

    cosineCoeffs (u t) k = heatPart k + chemPart k + logPart k,

with `heatPart k = e^{−tλ_k} · â₀ k` (heat propagation of the datum),
`chemPart` the chemotaxis-Duhamel coefficients, `logPart` the logistic-Duhamel
coefficients.  Each lands in `H^{σ+ρ}` (`ρ = α ∈ (0,1)`): heat by super-smoothing
(`heatDiag_memHSigma_succ`), chem/log by the engine
(`chemDuhamel_memHSigma_succ`).  `H^{σ+ρ}` is closed under addition, so the sum —
i.e. `cosineCoeffs (u t)` — lands in `H^{σ+ρ}`.  THE single-step gain. -/
theorem gradientSolution_memHSigma_succ {σ ρ t : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (ht : 0 < t)
    {a heatPart chemPart logPart utCoeff : ℕ → ℝ}
    (heatPart_eq : heatPart = fun k => Real.exp (-(t * lam k)) * a k)
    (ha : MemHSigma σ a)
    (hchem : MemHSigma (σ + ρ) chemPart)
    (hlog : MemHSigma (σ + ρ) logPart)
    (hdecomp : ∀ k, utCoeff k = heatPart k + chemPart k + logPart k) :
    MemHSigma (σ + ρ) utCoeff := by
  -- heat part super-smooths into H^{σ+ρ}
  have hheat : MemHSigma (σ + ρ) heatPart := by
    rw [heatPart_eq]; exact heatDiag_memHSigma_succ hρ0 hρ1.le ht ha
  -- sum of the three H^{σ+ρ} parts
  have hsum : MemHSigma (σ + ρ) (fun k => heatPart k + chemPart k + logPart k) :=
    ShenWork.Paper2.IntervalWienerAlgebra.memHSigma_add
      (ShenWork.Paper2.IntervalWienerAlgebra.memHSigma_add hheat hchem) hlog
  have hcongr : utCoeff = fun k => heatPart k + chemPart k + logPart k := funext hdecomp
  rw [hcongr]; exact hsum

/-- **THE CRUX — fully engine-wired single-step `H^σ → H^{σ+α}`.**

Same conclusion as `gradientSolution_memHSigma_succ`, but the chemotaxis- and
logistic-Duhamel parts' `H^{σ+α}` memberships are DERIVED from the engine
(`hSigmaEnergy_duhamel_bound_shifted` via `chemDuhamel_memHSigma_succ`), not
assumed.  The only carried hypothesis is the mild-equation cosine-coefficient
decomposition `hdecomp`

    cosineCoeffs (u t) k = e^{−tλ_k} â₀ k
        + (−χ₀)·duhamelEnergyCoeff 1 Fc t k    (chemotaxis, WALL-B chem)
        + (−χL)·duhamelEnergyCoeff 1 Fl t k    (logistic / lower-order)

which `IntervalMildSolution` + the χ₀≠0 WALL-B chemotaxis identity
(`chemotaxisDuhamel_cosineCoeff_eq_engine` integrated, the precise remaining
sub-goal) supplies.  `Fc = sineCoeffs ∘ Q` is the divergence-mode flux source
(envelope `Mc ∈ H^σ`), `Fl` the logistic source (envelope `Ml ∈ H^σ`); with the
gain exponent `α ∈ (0,1)` this lands `cosineCoeffs (u t) ∈ H^{σ+α}`. -/
theorem gradientSolution_memHSigma_succ_wired {σ α χc χL : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    {a utCoeff : ℕ → ℝ} {Fc Fl : ℕ → ℝ → ℝ} {Mc Ml : ℕ → ℝ}
    (ha : MemHSigma σ a)
    (hFc_cont : ∀ k, Continuous (Fc k)) (hMc0 : ∀ k, 0 ≤ Mc k)
    (hFc_bd : ∀ k, ∀ τ ∈ Set.Icc (0 : ℝ) t, |Fc k τ| ≤ Mc k)
    (hMc : Summable fun k => (1 + lam k) ^ σ * (Mc k) ^ 2)
    (hFl_cont : ∀ k, Continuous (Fl k)) (hMl0 : ∀ k, 0 ≤ Ml k)
    (hFl_bd : ∀ k, ∀ τ ∈ Set.Icc (0 : ℝ) t, |Fl k τ| ≤ Ml k)
    (hMl : Summable fun k => (1 + lam k) ^ σ * (Ml k) ^ 2)
    (hdecomp : ∀ k, utCoeff k = Real.exp (-(t * lam k)) * a k
      + (-χc) * duhamelEnergyCoeff 1 Fc t k
      + (-χL) * duhamelEnergyCoeff 1 Fl t k) :
    MemHSigma (σ + α) utCoeff := by
  -- chemotaxis-Duhamel part: engine gain σ → σ+α
  have hchem : MemHSigma (σ + α)
      (fun k => (-χc) * duhamelEnergyCoeff 1 Fc t k) :=
    chemDuhamel_memHSigma_succ hα0.le hα1 one_pos ht ht1 hFc_cont hMc0 hFc_bd hMc
      (fun _ => rfl)
  -- logistic-Duhamel part: same engine gain
  have hlog : MemHSigma (σ + α)
      (fun k => (-χL) * duhamelEnergyCoeff 1 Fl t k) :=
    chemDuhamel_memHSigma_succ hα0.le hα1 one_pos ht ht1 hFl_cont hMl0 hFl_bd hMl
      (fun _ => rfl)
  exact gradientSolution_memHSigma_succ hα0 hα1 ht rfl ha hchem hlog hdecomp

/-! ## Iteration to `ContDiffOn ℝ 2` (chain to WALL-C).

Given a step-provider `step : MemHSigma σ b → MemHSigma (σ+α) b` (the single
bootstrap step at the running regularity `σ`, supplied by
`gradientSolution_memHSigma_succ_wired` once the envelope/decomposition data are
re-established at each level), iterating `n` times from `MemHSigma σ₀` reaches
`MemHSigma (σ₀ + n·α)`. -/
theorem memHSigma_iterate {α σ₀ : ℝ} {b : ℕ → ℝ}
    (step : ∀ {σ : ℝ}, MemHSigma σ b → MemHSigma (σ + α) b) :
    ∀ n : ℕ, MemHSigma σ₀ b → MemHSigma (σ₀ + n * α) b
  | 0, h => by simpa using h
  | (n + 1), h => by
      have hrec := memHSigma_iterate (σ₀ := σ₀) step n h
      have := step hrec
      have heq : σ₀ + (n : ℝ) * α + α = σ₀ + ((n : ℕ) + 1 : ℕ) * α := by
        push_cast; ring
      rwa [heq] at this

/-- **Iterated bootstrap ⟹ `ContDiffOn ℝ 2`.**  After enough single steps the
running regularity exceeds `5/2`, and WALL-C
(`memHSigma_contDiffOn_two`) reconstructs the classical `C²` regularity of the
cosine series on `[0,1]`.  Hypothesis `hreach : 5/2 < σ₀ + n·α` records that `n`
steps suffice (e.g. `σ₀ = 0`, `α = 9/10`, `n = 3`). -/
theorem memHSigma_iterate_contDiffOn_two {α σ₀ : ℝ} {b : ℕ → ℝ} (n : ℕ)
    (hreach : 5 / 2 < σ₀ + n * α)
    (step : ∀ {σ : ℝ}, MemHSigma σ b → MemHSigma (σ + α) b)
    (h0 : MemHSigma σ₀ b) :
    ContDiffOn ℝ 2 (fun x => ∑' k, b k *
      ShenWork.CosineSpectrum.cosineMode k x) (Set.Icc (0 : ℝ) 1) :=
  ShenWork.Paper2.IntervalCosineSobolevEmbedding.memHSigma_contDiffOn_two hreach
    (memHSigma_iterate (σ₀ := σ₀) step n h0)

#print axioms oneAddLam_rpow_mul_exp_le
#print axioms heatDiag_memHSigma_succ
#print axioms fluxFunction_memHSigma
#print axioms chemDuhamel_memHSigma_succ
#print axioms gradientSolution_memHSigma_succ
#print axioms gradientSolution_memHSigma_succ_wired
#print axioms memHSigma_iterate
#print axioms memHSigma_iterate_contDiffOn_two

end ShenWork.Paper2.IntervalBootstrapStep
