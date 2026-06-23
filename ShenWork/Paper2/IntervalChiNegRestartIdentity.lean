/-
  ShenWork/Paper2/IntervalChiNegRestartIdentity.lean

  **χ₀<0 — DISCHARGE of `Hrestart` (the restart three-term Duhamel identity).**

  The prior producer (IntervalChiNegBoxExtendDischarge) CARRIED `Hrestart`,
  claiming the reanchoring of the origin-anchored cosine decomposition to the
  restart point `r` is "a genuine time-translation / semigroup restart property
  of the conjugate mild solution" with "NO restart-invariance lemma landed".

  THAT IS AN UNDER-CLAIM.  Reanchoring needs NO restart-invariance of the mild
  solution.  It is a purely ALGEBRAIC consequence of the LANDED origin-anchored
  decomposition `conjugateSlice_decomp_tauLift` (IntervalDecompTauLift), evaluated
  at `s = r+ρ` and at `s = r`, combined via:

    * `Real.exp` additivity   `e^{−(r+ρ)λ} = e^{−ρλ}·e^{−rλ}`,
    * the Duhamel integral split   `∫₀^{r+ρ} = ∫₀^r + ∫_r^{r+ρ}`,
    * the semigroup REANCHORING of the `[0,r]` tail
      `e^{−ρλ}·e^{−λ(r−τ)} = e^{−λ(r+ρ−τ)}` (Chapman–Kolmogorov, here a single
      `exp`-additivity in the integrand) — so the `[0,r]` contribution to the
      `r+ρ` Duhamel integral is EXACTLY `e^{−ρλ}` times the `[0,r]` Duhamel,
    * the time-shift substitution `τ ↦ τ+r` on the leftover `[r,r+ρ]` tail
      (`intervalIntegral.integral_comp_add_right`), turning it into a
      `duhamelModeCoeff` over elapsed `[0,ρ]` of the `r`-shifted source.

  The `[0,r]` pieces RECOMBINE EXACTLY into `e^{−ρλ_k}·cosineCoeffs(u r) k` by
  SUBSTITUTING the same origin decomposition at `s = r` (so `e^{−rλ}û₀ + chem[0,r]
  + log[0,r] = cosineCoeffs(u r) k`).  The leftover `[r,r+ρ]` legs are the
  restarted chemotaxis / logistic Duhamel coefficients with the `r`-shifted
  sources.  Hence `Hrestart` is DERIVED, not carried.

  Result: `Hrestart_derived` produces the EXACT `Hrestart` Prop consumed by
  `box_extend_step`, with the restarted sources `Qsrc`/`flLeg` defined as the
  `r`-shifted origin sources.  χ₀<0 now carries ONLY `Hpersist`.

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New file only.
-/
import ShenWork.Paper2.IntervalChiNegBoxExtendDischarge

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegRestartIdentity

open Real intervalIntegral MeasureTheory
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.Paper2.HSigmaScale (lam lam_nonneg)
open ShenWork.Paper2.BFormHSigmaDuhamelMode (duhamelModeCoeff)
open ShenWork.Paper2.BFormHSigmaDuhamelEnergy (duhamelEnergyCoeff)
open ShenWork.Paper2.IntervalChiNegBoxExtendDischarge (Hrestart)

/-! ## Core: the single-mode Duhamel reanchoring identity (DERIVED). -/

/-- The `duhamelModeCoeff` integrand `√lam · e^{−lam (s−τ)} · F τ` is continuous in
`τ` for continuous `F`, hence interval-integrable on any `[a,b]`. -/
theorem duhamelMode_integrand_intervalIntegrable (lamv : ℝ) {F : ℝ → ℝ}
    (hF : Continuous F) (s a b : ℝ) :
    IntervalIntegrable
      (fun τ => lamv ^ (1/2 : ℝ) * Real.exp (-(1 * lamv * (s - τ))) * F τ)
      volume a b :=
  (((continuous_const.mul
      (Real.continuous_exp.comp (by fun_prop))).mul hF)).intervalIntegrable a b

/-- **Single-mode reanchoring (the semigroup restart of the Duhamel coefficient).**

For continuous source `F`, eigenvalue `lamv`, base time `r ≥ 0`, elapsed `ρ`:
`duhamelModeCoeff 1 lamv F (r+ρ) = e^{−ρ·lamv}·duhamelModeCoeff 1 lamv F r
  + duhamelModeCoeff 1 lamv (fun τ => F (τ+r)) ρ`.

DERIVED from: the adjacent-interval split `∫₀^{r+ρ}=∫₀^r+∫_r^{r+ρ}`, the
Chapman–Kolmogorov exp-additivity `e^{−lamv((r+ρ)−τ)}=e^{−ρ lamv}·e^{−lamv(r−τ)}`
on the `[0,r]` tail, and the `τ↦τ+r` time-shift on the `[r,r+ρ]` tail. -/
theorem duhamelModeCoeff_reanchor (lamv : ℝ) {F : ℝ → ℝ} (hF : Continuous F)
    (r ρ : ℝ) :
    duhamelModeCoeff 1 lamv F (r + ρ)
      = Real.exp (-(ρ * lamv)) * duhamelModeCoeff 1 lamv F r
        + duhamelModeCoeff 1 lamv (fun τ => F (τ + r)) ρ := by
  unfold duhamelModeCoeff
  -- split [0, r+ρ] = [0,r] ∪ [r, r+ρ]
  rw [← intervalIntegral.integral_add_adjacent_intervals
        (duhamelMode_integrand_intervalIntegrable lamv hF (r + ρ) 0 r)
        (duhamelMode_integrand_intervalIntegrable lamv hF (r + ρ) r (r + ρ))]
  congr 1
  · -- the [0,r] tail = e^{−ρ lamv} · (Duhamel at r)
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun τ _ => ?_)
    rw [show -(1 * lamv * (r + ρ - τ)) = -(ρ * lamv) + -(1 * lamv * (r - τ)) by ring,
      Real.exp_add]
    ring
  · -- the [r, r+ρ] tail = Duhamel of the r-shifted source over [0,ρ]
    have hshift := intervalIntegral.integral_comp_add_right
      (a := (0 : ℝ)) (b := ρ)
      (fun τ => lamv ^ (1/2 : ℝ) * Real.exp (-(1 * lamv * (r + ρ - τ))) * F τ) r
    simp only [zero_add] at hshift
    rw [show (ρ + r) = r + ρ by ring] at hshift
    rw [← hshift]
    refine intervalIntegral.integral_congr (fun τ _ => ?_)
    simp only []
    rw [show r + ρ - (τ + r) = ρ - τ by ring]

/-! ## Multi-mode reanchoring on `duhamelEnergyCoeff`. -/

/-- **Multi-mode reanchoring.**  Mode-`k` version of `duhamelModeCoeff_reanchor`
for `duhamelEnergyCoeff`, with the source family time-shifted by `r`. -/
theorem duhamelEnergyCoeff_reanchor {F : ℕ → ℝ → ℝ} (hF : ∀ k, Continuous (F k))
    (r ρ : ℝ) (k : ℕ) :
    duhamelEnergyCoeff 1 F (r + ρ) k
      = Real.exp (-(ρ * lam k)) * duhamelEnergyCoeff 1 F r k
        + duhamelEnergyCoeff 1 (fun k τ => F k (τ + r)) ρ k := by
  unfold duhamelEnergyCoeff
  exact duhamelModeCoeff_reanchor (lam k) (hF k) r ρ

/-! ## The restarted sources (the `r`-shifted origin sources). -/

/-- The restarted chemotaxis source: the origin chemotaxis source family
time-shifted by `r` (so its `[0,ρ]` Duhamel is the `[r,r+ρ]` Duhamel of the
origin source). -/
def restartQsrc (Q : ℕ → ℝ → ℝ) (r : ℝ) : ℕ → ℝ → ℝ :=
  fun k τ => Q k (τ + r)

/-- The restarted logistic leg: the `[0,ρ]` Duhamel coefficient of the `r`-shifted
origin logistic source. -/
def restartFlLeg (Fl : ℕ → ℝ → ℝ) (r : ℝ) : ℝ → ℕ → ℝ :=
  fun ρ k => duhamelEnergyCoeff 1 (fun k τ => Fl k (τ + r)) ρ k

/-! ## `Hrestart` DISCHARGED as a theorem from the origin decomposition. -/

/-- **`Hrestart_derived` — the restart three-term Duhamel identity, DERIVED.**

Given the LANDED origin-anchored cosine decomposition (the exact shape produced by
`conjugateSlice_decomp_tauLift`), supplied here as `hdecomp0` over `[0, r+δ]`, with
continuous chemotaxis source `Q` and logistic source `Fl`, the restart identity
`Hrestart χ₀ uL (restartQsrc Q r) (restartFlLeg Fl r) r δ` holds (`uL : ℝ→ℝ→ℝ`
the slice map, exactly the `u` field `box_extend_step` consumes).

Proof: instantiate `hdecomp0` at `s = r+ρ` and at `s = r`; rewrite the heat factor
by exp-additivity and BOTH Duhamel coefficients by `duhamelEnergyCoeff_reanchor`;
the `[0,r]` heat+chem+log pieces collapse via `hdecomp0` at `s = r` into
`e^{−ρλ_k}·cosineCoeffs(uL r) k`; the leftover `[0,ρ]` shifted legs are exactly the
restarted chemotaxis Duhamel and `restartFlLeg`. -/
theorem Hrestart_derived
    {χ₀ δ r : ℝ} {uL : ℝ → ℝ → ℝ} {û₀ : ℕ → ℝ}
    {Q Fl : ℕ → ℝ → ℝ} (hr : 0 ≤ r)
    (hQcont : ∀ k, Continuous (Q k)) (hFlcont : ∀ k, Continuous (Fl k))
    (hdecomp0 : ∀ s ∈ Set.Icc (0 : ℝ) (r + δ), ∀ k,
      cosineCoeffs (uL s) k
        = Real.exp (-(s * lam k)) * û₀ k
          + (-χ₀) * duhamelEnergyCoeff 1 Q s k
          + duhamelEnergyCoeff 1 Fl s k)
    (hδ : 0 ≤ δ) :
    Hrestart χ₀ uL (restartQsrc Q r) (restartFlLeg Fl r) r δ := by
  intro ρ hρ0 hρδ k
  have hr_mem : r ∈ Set.Icc (0 : ℝ) (r + δ) :=
    ⟨hr, by linarith⟩
  have hrρ_mem : r + ρ ∈ Set.Icc (0 : ℝ) (r + δ) :=
    ⟨by linarith, by linarith⟩
  -- decomposition at s = r+ρ and at s = r
  have hAt := hdecomp0 (r + ρ) hrρ_mem k
  have hAtr := hdecomp0 r hr_mem k
  -- reanchor the two Duhamel coefficients
  have hchem := duhamelEnergyCoeff_reanchor hQcont r ρ k
  have hlog := duhamelEnergyCoeff_reanchor hFlcont r ρ k
  -- heat factor exp-additivity
  have hexp : Real.exp (-((r + ρ) * lam k))
      = Real.exp (-(ρ * lam k)) * Real.exp (-(r * lam k)) := by
    rw [← Real.exp_add]; congr 1; ring
  -- assemble
  rw [hAt, hexp, hchem, hlog]
  -- isolate e^{−ρλ}·(origin decomposition at r) and the restarted legs
  rw [show restartQsrc Q r = fun k τ => Q k (τ + r) from rfl,
    show restartFlLeg Fl r = fun ρ k =>
      duhamelEnergyCoeff 1 (fun k τ => Fl k (τ + r)) ρ k from rfl]
  rw [hAtr]
  ring

/-! ## AxiomAudit -/

section AxiomAudit
#print axioms duhamelModeCoeff_reanchor
#print axioms duhamelEnergyCoeff_reanchor
#print axioms Hrestart_derived
end AxiomAudit

end ShenWork.Paper2.IntervalChiNegRestartIdentity
