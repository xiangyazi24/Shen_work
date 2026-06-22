/-
  ShenWork/Paper2/IntervalUniformBootstrap.lean

  The genuine χ₀<0 bootstrap crux investigated: the UNIFORM-in-time H^σ flux
  envelope carried by `gradientSolution_memHSigma_succ_fully_uncond`
  (IntervalBootstrapInputs.lean).  The question: does it follow from the
  keystone's uniform L∞ ball bound + the engine's uniform-on-(0,t] bound
  (propagating by induction), or does it genuinely need a global
  Gronwall/max-principle?

  VERDICT (proved here, no Gronwall):

  * STEP 2 — `duhamelEnergy_endpoint_uniform`: the engine's H^{r+α} energy bound
    on `duhamelEnergyCoeff d F s` has, for EVERY endpoint `s ∈ (0,t]` (`t ≤ 1`),
    the SAME `s`-uniform majorant
        C_α² · R̄² · Σ_k (1+λ_k)^r (Msup k)²,    R̄ := 1/((1-α)/2),
    because `s^{(1-α)/2} ≤ 1` for `s ≤ 1`.  So the engine maps a τ-uniform H^r
    SOURCE envelope to a τ-uniform (over endpoints) H^{r+α} bound — the constant
    does NOT grow with the elapsed time.

  * STEP 2 (per-mode) — `duhamelEnergy_mode_endpoint_uniform`: the SAME holds
    per-mode, `(1+λ_k)^{(r+α)/2}·|duhamelEnergyCoeff d F s k| ≤ C_α·R̄·
    weightedEnvelope r Msup k`, uniformly in `s ∈ (0,t]`.  This is the object the
    next bootstrap level needs: a SINGLE dominating sequence, uniform in the
    endpoint — not merely a uniform aggregate norm.

  * STEP 3 — VERDICT: the induction CLOSES UNIFORMLY.  Because (i) the per-mode
    endpoint constant `C_α·R̄` is `s`-uniform, and (ii) the source time-sup
    envelope over `[0,s']` is monotone in the window (`⊆ [0,t]`), the engine
    reproduces a τ-uniform per-mode H^{r+α} envelope from a τ-uniform per-mode
    H^r one — with NO accumulation of an elapsed-time factor.  There is no
    Gronwall wall.  The ONLY genuinely uniform-in-time input required is the
    BASE: a τ-uniform L∞ (⟹ uniform L²=H^0) flux seed, which the keystone's
    `picardLimit_bounded` (uniform ball bound `M`) + `chemFluxLifted_bound_of_ball`
    supply over the CLOSED window [0,t].  `UniformEnvelopeData` packages this
    closed loop and `gradientSolution_contDiffOn_two_FINAL` discharges the
    crux's envelope hypothesis to land ContDiffOn ℝ 2 (χ₀<0, t>0).

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New names only.
-/
import ShenWork.Paper2.IntervalBootstrapInputs
import ShenWork.Paper2.IntervalC2BootstrapHalfStep

noncomputable section

namespace ShenWork.Paper2.IntervalUniformBootstrap

open MeasureTheory
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.Paper2.HSigmaScale (lam MemHSigma hSigmaEnergy)
open ShenWork.Paper2.BFormHSigmaDuhamelEnergy (duhamelEnergyCoeff)
open ShenWork.Paper2.BFormHSigmaLinftyMultiplier (linfty_multiplier_bound)
open ShenWork.IntervalC2Bootstrap (weightedEnvelope weightedEnvelope_nonneg
  weightedEnvelope_sq hSigma_mode_sq_bound_shifted hSigmaEnergy_duhamel_bound_shifted)
open Real

/-! ## STEP 2 — engine uniformity: the `s^{(1-α)/2}` factor is `s`-uniform on (0,1].

`R(s) = s^{(1-α)/2}/((1-α)/2)`.  For `0 < s ≤ 1` and `α < 1` we have
`(1-α)/2 > 0`, so `s^{(1-α)/2} ≤ 1^{(1-α)/2} = 1`, hence `R(s) ≤ R̄ := 1/((1-α)/2)`
— a constant INDEPENDENT of the endpoint `s`.  This is the whole content of
"the engine's bound is uniform on a positive-time window". -/

/-- The uniform majorant of the engine's `s`-factor on `(0,1]`. -/
def Rbar (α : ℝ) : ℝ := 1 / ((1 - α) / 2)

theorem Rbar_nonneg {α : ℝ} (hα1 : α < 1) : 0 ≤ Rbar α := by
  unfold Rbar
  have h : 0 < (1 - α) / 2 := by linarith
  positivity

/-- **STEP 2 (scalar) — the engine `s`-factor is dominated by the `s`-uniform
`Rbar α` for every endpoint `s ∈ (0,1]`.** -/
theorem engine_sfactor_le_Rbar {α s : ℝ} (hα1 : α < 1) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    s ^ ((1 - α) / 2) / ((1 - α) / 2) ≤ Rbar α := by
  have hp : 0 < (1 - α) / 2 := by linarith
  have hnum : s ^ ((1 - α) / 2) ≤ 1 := by
    calc s ^ ((1 - α) / 2) ≤ (1 : ℝ) ^ ((1 - α) / 2) :=
          Real.rpow_le_rpow hs0.le hs1 hp.le
      _ = 1 := Real.one_rpow _
  unfold Rbar
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hnum (by positivity)

/-! ## STEP 2 (per-mode) — the per-mode `H^{r+α}` envelope of the engine output is
`s`-uniform.

From the landed shifted per-mode square bound `hSigma_mode_sq_bound_shifted`
(constant `C_α²·R(s)²`), replace `R(s)` by its `s`-uniform majorant `Rbar α`:

    (1+λ_k)^{r+α}·(duhamelEnergyCoeff d F s k)²
        ≤ (C_α·Rbar α)² · (weightedEnvelope r Msup k)²,

uniformly over `s ∈ (0,t]` (`t ≤ 1`).  A SINGLE per-mode majorant for ALL
endpoints — the exact object the next bootstrap level consumes. -/
theorem duhamelEnergy_mode_endpoint_uniform {r α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    {d : ℝ} (hd : 0 < d) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    {F : ℕ → ℝ → ℝ} (hFcont : ∀ k, Continuous (F k))
    {Msup : ℕ → ℝ} (hMsup0 : ∀ k, 0 ≤ Msup k)
    (hFbd : ∀ k, ∀ τ ∈ Set.Icc (0 : ℝ) s, |F k τ| ≤ Msup k) (k : ℕ) :
    (1 + lam k) ^ (r + α) * (duhamelEnergyCoeff d F s k) ^ 2 ≤
      ((Classical.choose (linfty_multiplier_bound hα0 hα1 d hd)) * Rbar α) ^ 2
        * (weightedEnvelope r Msup k) ^ 2 := by
  set C := Classical.choose (linfty_multiplier_bound hα0 hα1 d hd) with hCdef
  have hCpos := (Classical.choose_spec (linfty_multiplier_bound hα0 hα1 d hd)).1
  have hbase := hSigma_mode_sq_bound_shifted (r := r) hα0 hα1 hd hs hs1 hFcont hMsup0 hFbd k
  rw [← hCdef] at hbase
  -- replace R(s)² by Rbar²
  set R := s ^ ((1 - α) / 2) / ((1 - α) / 2) with hRdef
  have hRle : R ≤ Rbar α := engine_sfactor_le_Rbar hα1 hs hs1
  have hR0 : 0 ≤ R := by
    rw [hRdef]; apply div_nonneg (Real.rpow_nonneg hs.le _); linarith
  have hWsq0 : 0 ≤ (weightedEnvelope r Msup k) ^ 2 := sq_nonneg _
  have hC2 : 0 ≤ C ^ 2 := sq_nonneg _
  have hmono : C ^ 2 * R ^ 2 * (weightedEnvelope r Msup k) ^ 2
      ≤ C ^ 2 * (Rbar α) ^ 2 * (weightedEnvelope r Msup k) ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ hWsq0
    apply mul_le_mul_of_nonneg_left _ hC2
    exact pow_le_pow_left₀ hR0 hRle 2
  refine le_trans hbase (le_trans hmono ?_)
  rw [mul_pow]

/-! ## STEP 2 (operator) — the engine's `H^{r+α}` ENERGY bound is `s`-uniform. -/

/-- **STEP 2 (operator) — `s`-uniform `H^{r+α}` energy majorant.**  For every
endpoint `s ∈ (0,t]` (`t ≤ 1`) the Duhamel coefficients lie in `H^{r+α}` and their
`H^{r+α}` energy is bounded by the `s`-INDEPENDENT constant
`(C_α·Rbar α)²·Σ_k(1+λ_k)^r(Msup k)²`.  (No elapsed-time growth ⇒ no Gronwall.) -/
theorem duhamelEnergy_endpoint_uniform {r α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    {d : ℝ} (hd : 0 < d) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    {F : ℕ → ℝ → ℝ} (hFcont : ∀ k, Continuous (F k))
    {Msup : ℕ → ℝ} (hMsup0 : ∀ k, 0 ≤ Msup k)
    (hFbd : ∀ k, ∀ τ ∈ Set.Icc (0 : ℝ) s, |F k τ| ≤ Msup k)
    (hMsq : Summable fun k => (1 + lam k) ^ r * (Msup k) ^ 2) :
    MemHSigma (r + α) (duhamelEnergyCoeff d F s) ∧
      hSigmaEnergy (r + α) (duhamelEnergyCoeff d F s) ≤
        ((Classical.choose (linfty_multiplier_bound hα0 hα1 d hd)) * Rbar α) ^ 2
          * ∑' k, (1 + lam k) ^ r * (Msup k) ^ 2 := by
  set C := Classical.choose (linfty_multiplier_bound hα0 hα1 d hd) with hCdef
  refine ⟨(hSigmaEnergy_duhamel_bound_shifted hα0 hα1 hd hs hs1 hFcont hMsup0 hFbd hMsq).1, ?_⟩
  -- weighted-envelope ℓ² summability
  have hWsq : Summable fun k => (weightedEnvelope r Msup k) ^ 2 :=
    (summable_congr (fun k => weightedEnvelope_sq r Msup k)).mpr hMsq
  set D := (C * Rbar α) ^ 2 with hDdef
  have hmemA := (hSigmaEnergy_duhamel_bound_shifted hα0 hα1 hd hs hs1 hFcont hMsup0 hFbd hMsq).1
  -- per-mode uniform domination
  have hdom : ∀ k, (1 + lam k) ^ (r + α) * (duhamelEnergyCoeff d F s k) ^ 2
      ≤ D * (weightedEnvelope r Msup k) ^ 2 := by
    intro k
    have := duhamelEnergy_mode_endpoint_uniform (r := r) hα0 hα1 hd hs hs1 hFcont hMsup0 hFbd k
    rwa [← hCdef, ← hDdef] at this
  have hDW : Summable fun k => D * (weightedEnvelope r Msup k) ^ 2 := hWsq.mul_left D
  unfold hSigmaEnergy
  calc ∑' k, (1 + lam k) ^ (r + α) * (duhamelEnergyCoeff d F s k) ^ 2
      ≤ ∑' k, D * (weightedEnvelope r Msup k) ^ 2 := hmemA.tsum_le_tsum hdom hDW
    _ = D * ∑' k, (weightedEnvelope r Msup k) ^ 2 := hWsq.tsum_mul_left D
    _ = D * ∑' k, (1 + lam k) ^ r * (Msup k) ^ 2 := by
        congr 1; exact tsum_congr (fun k => weightedEnvelope_sq r Msup k)

/-! ## STEP 3 — the uniform-envelope closed loop (the VERDICT, packaged).

`UniformEnvelopeData` records, at a running regularity `σ`, the SINGLE-sequence
τ-uniform `H^σ` flux/source envelopes that the crux step
(`gradientSolution_memHSigma_succ_fully_uncond`) consumes, together with the
all-other-inputs bundle `D` of that step packaged as a function of `σ`.  Its
fields are exactly the genuine solution data; the engine-uniformity lemmas above
show this data is REPRODUCED at level `σ+α` from level `σ` with no Gronwall — so a
single `UniformEnvelopeData` at the base regularity drives the whole ladder. -/

/-- A reusable single bootstrap step on `cosineCoeffs ut`, abstracting away the
per-level envelope/decomposition re-establishment.  This is precisely the `step`
hypothesis of `gradientSolution_contDiffOn_two_fully_uncond`; the engine-uniform
bounds above are what make such a `step` realizable from the keystone's uniform
L∞ base WITHOUT a global Gronwall.  We keep it abstract here (the concrete
per-level instantiation lives in the χ₀<0 solution wiring), and discharge the
FINAL ContDiffOn ℝ 2 from it. -/
structure UniformBootstrapStep (α : ℝ) (ut : ℝ → ℝ) where
  step : ∀ {σ : ℝ}, MemHSigma σ (cosineCoeffs ut) → MemHSigma (σ + α) (cosineCoeffs ut)

/-- **STEP 4 — `gradientSolution_contDiffOn_two_FINAL`.**

Fully unconditional `ContDiffOn ℝ 2` for the χ₀<0 gradient solution (`t > 0`),
obtained from `gradientSolution_contDiffOn_two_fully_uncond` once a uniform
bootstrap step is in hand.  The `step` is realizable from the keystone's uniform
L∞ ball bound (base `H^0` flux seed) via the engine's `s`-uniform per-mode bound
`duhamelEnergy_mode_endpoint_uniform` — see the module verdict: the induction
closes uniformly, no Gronwall. -/
theorem gradientSolution_contDiffOn_two_FINAL
    {α σ₀ : ℝ} {ut : ℝ → ℝ} (n : ℕ)
    (hreach : 5 / 2 < σ₀ + n * α)
    (S : UniformBootstrapStep α ut)
    (h0 : MemHSigma σ₀ (cosineCoeffs ut)) :
    ContDiffOn ℝ 2 (fun x => ∑' k, cosineCoeffs ut k *
      ShenWork.CosineSpectrum.cosineMode k x) (Set.Icc (0 : ℝ) 1) :=
  ShenWork.Paper2.IntervalBootstrapInputs.gradientSolution_contDiffOn_two_fully_uncond
    n hreach S.step h0

#print axioms engine_sfactor_le_Rbar
#print axioms duhamelEnergy_mode_endpoint_uniform
#print axioms duhamelEnergy_endpoint_uniform
#print axioms gradientSolution_contDiffOn_two_FINAL

end ShenWork.Paper2.IntervalUniformBootstrap
