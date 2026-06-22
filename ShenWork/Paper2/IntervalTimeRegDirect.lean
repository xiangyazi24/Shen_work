/-
  ShenWork/Paper2/IntervalTimeRegDirect.lean

  **The DIRECT forward route to χ₀ < 0 time regularity — non-circular.**

  From the landed mild-equation cosine-coefficient decomposition
  (`gradientSolution_cosineCoeff_decomp_chi`, IntervalBootstrapDecomp.lean):

      cosineCoeffs (u t) k
        = e^{−tλ_k}·â₀_k
          + (−χ₀)·duhamelEnergyCoeff 1 Fc t k
          + duhamelEnergyCoeff 1 Fl t k,

  where `duhamelEnergyCoeff 1 F t k = duhamelModeCoeff 1 (lam k) (F k) t`
                                     = ∫₀ᵗ √λ_k·e^{−λ_k(t−τ)}·F k τ dτ.

  This file differentiates that decomposition IN TIME, per mode, by the
  diagonalization trick.  The single genuinely analytic step is the
  per-mode Duhamel ODE

      d/dt [∫₀ᵗ √λ·e^{−λ(t−τ)}·F(τ) dτ]  =  −λ·(that integral) + √λ·F(t),

  proved DIRECTLY by factoring `e^{−λ(t−τ)} = e^{−λt}·e^{λτ}`, applying the
  Fundamental Theorem of Calculus (`integral_hasDerivAt_right`) to the
  `t`-free-kernel integral `∫₀ᵗ e^{λτ}F(τ) dτ`, and the product rule.

  **NON-CIRCULAR.**  This uses ONLY:
    * the FTC (`integral_hasDerivAt_right`) — a Mathlib library fact;
    * continuity of the source `F` in time (a clean hypothesis);
    * the landed `hdecomp` (TASK 1 of IntervalBootstrapDecomp).
  It does NOT use `DuhamelSourceTimeC1`, `ResolverHasSpectralAgreement`, the
  `dominated_loc` under-integral Leibniz, or any spectral-agreement package —
  precisely the circular ingredients the source-package route depends on.

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New file, new names only.
-/
import ShenWork.Paper2.IntervalBootstrapDecomp

noncomputable section

namespace ShenWork.Paper2.IntervalTimeRegDirect

open MeasureTheory intervalIntegral
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.Paper2.HSigmaScale (lam)
open ShenWork.Paper2.BFormHSigmaDuhamelEnergy (duhamelEnergyCoeff)
open ShenWork.Paper2.BFormHSigmaDuhamelMode (duhamelModeCoeff)
open Real

/-! ## The Duhamel kernel factoring -/

/-- `e^{−λ(t−τ)} = e^{−λt}·e^{λτ}`: the kernel separates the `t`- and
`τ`-dependence.  This is what removes `t` from inside the time integral. -/
theorem kernel_factor (lamv t τ : ℝ) :
    Real.exp (-(lamv * (t - τ))) = Real.exp (-(lamv * t)) * Real.exp (lamv * τ) := by
  rw [← Real.exp_add]; ring_nf

/-- The Duhamel mode coefficient with the `t`-free integral factored out:
`duhamelModeCoeff 1 λ F t = √λ·e^{−λt}·∫₀ᵗ e^{λτ}·F(τ) dτ`. -/
theorem duhamelModeCoeff_factored {lamv : ℝ} (F : ℝ → ℝ) (t : ℝ) :
    duhamelModeCoeff 1 lamv F t
      = lamv ^ (1/2 : ℝ) * Real.exp (-(lamv * t))
          * ∫ τ in (0:ℝ)..t, Real.exp (lamv * τ) * F τ := by
  rw [ShenWork.Paper2.BFormHSigmaDuhamelMode.duhamelModeCoeff]
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun τ _ => ?_)
  rw [show (1:ℝ) * lamv * (t - τ) = lamv * (t - τ) by ring, kernel_factor]
  ring

/-! ## The per-mode Duhamel ODE (the analytic crux)

`d/dt duhamelModeCoeff 1 λ F t = −λ·duhamelModeCoeff 1 λ F t + √λ·F(t)`,
proved DIRECTLY by FTC on the `t`-free-kernel integral and the product rule. -/

/-- **The per-mode Duhamel ODE, direct forward route.**

For a continuous source `F`, the Duhamel mode coefficient
`B(t) = duhamelModeCoeff 1 λ F t = ∫₀ᵗ √λ·e^{−λ(t−τ)}·F(τ) dτ` satisfies the
diagonalized ODE

    HasDerivAt B (−λ·B(t) + √λ·F(t)) t.

Proof: factor `B(t) = √λ·e^{−λt}·J(t)` with `J(t) = ∫₀ᵗ e^{λτ}F(τ) dτ`.
By FTC, `J'(t) = e^{λt}F(t)`.  The product rule gives
`B'(t) = √λ·(−λ·e^{−λt}·J(t) + e^{−λt}·e^{λt}F(t)) = −λ·B(t) + √λ·F(t)`.

NON-CIRCULAR: uses only FTC + continuity of `F`. -/
theorem duhamelModeCoeff_hasDerivAt {lamv : ℝ} {F : ℝ → ℝ} (hF : Continuous F) (t : ℝ) :
    HasDerivAt (fun r => duhamelModeCoeff 1 lamv F r)
      (-(lamv * duhamelModeCoeff 1 lamv F t) + lamv ^ (1/2 : ℝ) * F t) t := by
  -- J(t) = ∫₀ᵗ e^{λτ}F(τ) dτ, and J'(t) = e^{λt}F(t) by FTC.
  set g : ℝ → ℝ := fun τ => Real.exp (lamv * τ) * F τ with hg
  have hgcont : Continuous g := (Real.continuous_exp.comp (continuous_const.mul
    continuous_id)).mul hF
  have hJ : HasDerivAt (fun r => ∫ τ in (0:ℝ)..r, g τ) (g t) t :=
    intervalIntegral.integral_hasDerivAt_right
      (hgcont.intervalIntegrable 0 t)
      (hgcont.stronglyMeasurableAtFilter _ _) hgcont.continuousAt
  -- the prefactor √λ·e^{−λt} and its derivative −λ·√λ·e^{−λt}.
  have hexp : HasDerivAt (fun r => Real.exp (-(lamv * r)))
      (-(Real.exp (-(lamv * t)) * lamv)) t := by
    have h := (((hasDerivAt_id t).const_mul lamv).neg).exp
    simpa using h
  have hpre : HasDerivAt (fun r => lamv ^ (1/2 : ℝ) * Real.exp (-(lamv * r)))
      (lamv ^ (1/2 : ℝ) * (-(Real.exp (-(lamv * t)) * lamv))) t := hexp.const_mul _
  -- product rule on B(t) = (√λ·e^{−λt}) · J(t)
  have hprod : HasDerivAt
      (fun r => (lamv ^ (1/2 : ℝ) * Real.exp (-(lamv * r))) * (∫ τ in (0:ℝ)..r, g τ))
      ((lamv ^ (1/2 : ℝ) * (-(Real.exp (-(lamv * t)) * lamv))) * (∫ τ in (0:ℝ)..t, g τ)
        + (lamv ^ (1/2 : ℝ) * Real.exp (-(lamv * t))) * g t) t := hpre.mul hJ
  -- rewrite the function as duhamelModeCoeff via the factoring identity
  have hfun : (fun r => duhamelModeCoeff 1 lamv F r)
      = fun r => (lamv ^ (1/2 : ℝ) * Real.exp (-(lamv * r))) * (∫ τ in (0:ℝ)..r, g τ) := by
    funext r; rw [duhamelModeCoeff_factored F r]
  rw [hfun]
  -- match the derivative value with −λ·B(t) + √λ·F(t)
  convert hprod using 1
  rw [duhamelModeCoeff_factored F t]
  -- LHS: −λ·(√λ·e^{−λt}·J) + √λ·F t ; RHS from product rule. g t = e^{λt}·F t.
  have hgt : g t = Real.exp (lamv * t) * F t := rfl
  rw [hgt]
  have hee : Real.exp (-(lamv * t)) * Real.exp (lamv * t) = 1 := by
    rw [← Real.exp_add]; simp
  -- both sides differ only by `√λ·F t` vs `√λ·(e^{−λt}·e^{λt})·F t`; `hee` closes it.
  have hkey : lamv ^ (1/2 : ℝ) * F t
      = lamv ^ (1/2 : ℝ) * Real.exp (-(lamv * t)) * (Real.exp (lamv * t) * F t) := by
    rw [show lamv ^ (1/2 : ℝ) * Real.exp (-(lamv * t)) * (Real.exp (lamv * t) * F t)
      = lamv ^ (1/2 : ℝ) * (Real.exp (-(lamv * t)) * Real.exp (lamv * t)) * F t by ring,
      hee]; ring
  rw [hkey]; ring

/-- The heat-diagonal term `e^{−rλ}·a` has time-derivative `−λ·(e^{−rλ}·a)`. -/
theorem heatDiag_hasDerivAt (lamv a t : ℝ) :
    HasDerivAt (fun r => Real.exp (-(r * lamv)) * a)
      (-(lamv * (Real.exp (-(t * lamv)) * a))) t := by
  have hexp : HasDerivAt (fun r => Real.exp (-(r * lamv)))
      (-(Real.exp (-(t * lamv)) * lamv)) t := by
    have h := (((hasDerivAt_id t).mul_const lamv).neg).exp
    simpa using h
  have h := hexp.mul_const a
  convert h using 1; ring

/-! ## TASK 1 — the crux: `∂ₜ cosineCoeffs (u t) k` (the diagonalized PDE)

From the landed decomposition `hdecomp` and the Duhamel ODE
`duhamelModeCoeff_hasDerivAt`, the `k`-th cosine coefficient of the solution
satisfies the diagonalized-in-coefficients PDE

    ∂ₜ cosineCoeffs (u t) k = −λ_k·cosineCoeffs (u t) k + Ftotal_k(t),

with the total source coefficient
    Ftotal_k(t) = (−χ₀)·√λ_k·Fc_k(t) + √λ_k·Fl_k(t).

NON-CIRCULAR: uses ONLY `hdecomp` + `duhamelModeCoeff_hasDerivAt` (FTC + product
rule) + continuity of `Fc`, `Fl` in time.  No `DuhamelSourceTimeC1`, no spectral
agreement. -/

/-- The total source coefficient feeding the diagonalized PDE for mode `k`. -/
def FtotalCoeff (χ₀ : ℝ) (Fc Fl : ℕ → ℝ → ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  (-χ₀) * ((lam k) ^ (1/2 : ℝ) * Fc k t) + (lam k) ^ (1/2 : ℝ) * Fl k t

/-- **TASK 1 (THE CRUX) — `cosineCoeff_timeDeriv`.**

For the χ₀<0 gradient solution whose coefficients obey the landed mild
decomposition `hdecomp` at every time, the `k`-th cosine coefficient has the
time derivative dictated by the diagonalized PDE:

    HasDerivAt (fun r => cosineCoeffs (uLift r) k)
      (−λ_k·cosineCoeffs (uLift t) k + Ftotal_k(t)) t.

`uLift : ℝ → ℝ → ℝ` is the time-indexed lift of the solution slices;
`a₀ = cosineCoeffs u₀` the datum coefficients; `Fc`/`Fl` the chemotaxis/logistic
source coefficients (continuous in time).

Proof: differentiate the three summands of `hdecomp` — heat diagonal
(`heatDiag_hasDerivAt`) and the two Duhamel coefficients
(`duhamelModeCoeff_hasDerivAt`) — then collect using `hdecomp t` itself to
re-express the `−λ_k·(…)` terms as `−λ_k·cosineCoeffs (uLift t) k`. -/
theorem cosineCoeff_timeDeriv
    {χ₀ : ℝ} {uLift : ℝ → ℝ → ℝ} {a₀ : ℕ → ℝ} {Fc Fl : ℕ → ℝ → ℝ}
    (k : ℕ) (t : ℝ)
    (hFc : Continuous (Fc k)) (hFl : Continuous (Fl k))
    (hdecomp : ∀ r, cosineCoeffs (uLift r) k
      = Real.exp (-(r * lam k)) * a₀ k
        + (-χ₀) * duhamelEnergyCoeff 1 Fc r k
        + duhamelEnergyCoeff 1 Fl r k) :
    HasDerivAt (fun r => cosineCoeffs (uLift r) k)
      (-(lam k * cosineCoeffs (uLift t) k) + FtotalCoeff χ₀ Fc Fl k t) t := by
  -- the three summands' derivatives
  have hheat := heatDiag_hasDerivAt (lam k) (a₀ k) t
  have hchem : HasDerivAt (fun r => duhamelEnergyCoeff 1 Fc r k)
      (-(lam k * duhamelEnergyCoeff 1 Fc t k) + (lam k) ^ (1/2 : ℝ) * Fc k t) t := by
    have := duhamelModeCoeff_hasDerivAt (lamv := lam k) (F := Fc k) hFc t
    simpa [duhamelEnergyCoeff] using this
  have hlog : HasDerivAt (fun r => duhamelEnergyCoeff 1 Fl r k)
      (-(lam k * duhamelEnergyCoeff 1 Fl t k) + (lam k) ^ (1/2 : ℝ) * Fl k t) t := by
    have := duhamelModeCoeff_hasDerivAt (lamv := lam k) (F := Fl k) hFl t
    simpa [duhamelEnergyCoeff] using this
  -- assemble the sum derivative on the decomposed function
  have hsum : HasDerivAt
      (fun r => Real.exp (-(r * lam k)) * a₀ k
        + (-χ₀) * duhamelEnergyCoeff 1 Fc r k
        + duhamelEnergyCoeff 1 Fl r k)
      ((-(lam k * (Real.exp (-(t * lam k)) * a₀ k)))
        + (-χ₀) * (-(lam k * duhamelEnergyCoeff 1 Fc t k) + (lam k) ^ (1/2 : ℝ) * Fc k t)
        + (-(lam k * duhamelEnergyCoeff 1 Fl t k) + (lam k) ^ (1/2 : ℝ) * Fl k t)) t :=
    (hheat.add (hchem.const_mul (-χ₀))).add hlog
  -- transport along `hdecomp` (functions equal everywhere)
  have hfun : (fun r => cosineCoeffs (uLift r) k)
      = (fun r => Real.exp (-(r * lam k)) * a₀ k
        + (-χ₀) * duhamelEnergyCoeff 1 Fc r k
        + duhamelEnergyCoeff 1 Fl r k) := by
    funext r; exact hdecomp r
  rw [hfun]
  convert hsum using 1
  -- the target derivative equals the assembled one, using `hdecomp t`
  rw [hdecomp t, FtotalCoeff]; ring

/-! ## TASK 2 — the source time-derivative FROM `∂ₜu` (breaking circularity)

In the source-package route, `∂ₜF̂` is *assumed* (DuhamelSourceTimeC1) and then
used to produce `∂ₜu`.  Here `∂ₜF̂` is *derived* FROM `∂ₜu` by the chain rule, the
forward direction.  We package the generic chain-rule shape: given the mode-`k`
source coefficient as a `C¹` function `S` of the (scalar) coefficient
`y(t) = cosineCoeffs (uLift t) k` (logistic `S = logistic'∘u`-type), the source
coefficient's time derivative is `S'(y(t))·y'(t)`, with `y'` supplied by TASK 1. -/

/-- **TASK 2 — `source_timeDeriv_of_time1`.**  If the mode-`k` source coefficient
is `Scoeff t = S (cosineCoeffs (uLift t) k)` for a differentiable scalar response
`S` (the coefficient-space image of `logistic'(u)`/flux product rule), then its
time derivative is `S'(y t)·y'(t)`, where `y'(t)` is the diagonalized-PDE
derivative of TASK 1.  This is the source time-derivative obtained FROM `∂ₜu`,
the non-circular forward direction. -/
theorem source_timeDeriv_of_time1
    {χ₀ : ℝ} {uLift : ℝ → ℝ → ℝ} {a₀ : ℕ → ℝ} {Fc Fl : ℕ → ℝ → ℝ}
    {S : ℝ → ℝ} {S' : ℝ}
    (k : ℕ) (t : ℝ)
    (hFc : Continuous (Fc k)) (hFl : Continuous (Fl k))
    (hdecomp : ∀ r, cosineCoeffs (uLift r) k
      = Real.exp (-(r * lam k)) * a₀ k
        + (-χ₀) * duhamelEnergyCoeff 1 Fc r k
        + duhamelEnergyCoeff 1 Fl r k)
    (hS : HasDerivAt S S' (cosineCoeffs (uLift t) k)) :
    HasDerivAt (fun r => S (cosineCoeffs (uLift r) k))
      (S' * (-(lam k * cosineCoeffs (uLift t) k) + FtotalCoeff χ₀ Fc Fl k t)) t :=
  hS.comp t (cosineCoeff_timeDeriv k t hFc hFl hdecomp)

/-! ## TASK 3 — the second time derivative `∂ₜₜ cosineCoeffs (u t) k`

Differentiate TASK 1 once more.  The diagonalized PDE
`y'(t) = −λ·y(t) + Ftotal(t)` differentiates to
`y''(t) = −λ·y'(t) + Ftotal'(t) = λ²·y(t) − λ·Ftotal(t) + Ftotal'(t)`, given a
time-derivative `Fdot` of `Ftotal` (supplied by TASK 2 through the source response).
-/

/-- **TASK 3 — `cosineCoeff_timeDeriv2`.**  Given the diagonalized first
derivative (`hy1`, TASK 1) on a neighborhood and a derivative `Fdot` of the total
source coefficient `Ftotal` (`hF`, from TASK 2), the second time derivative is

    ∂ₜₜ y = λ²·y(t) − λ·Ftotal(t) + Fdot.

This differentiates `y'(r) = −λ·y(r) + Ftotal(r)` once more. -/
theorem cosineCoeff_timeDeriv2
    {lamv : ℝ} {y Ftot : ℝ → ℝ} {Fdot : ℝ} (t : ℝ)
    (hy1 : ∀ r, HasDerivAt y (-(lamv * y r) + Ftot r) r)
    (hF : HasDerivAt Ftot Fdot t) :
    HasDerivAt (fun r => -(lamv * y r) + Ftot r)
      (lamv ^ 2 * y t - lamv * Ftot t + Fdot) t := by
  have hyt : HasDerivAt y (-(lamv * y t) + Ftot t) t := hy1 t
  have h1 : HasDerivAt (fun r => -(lamv * y r))
      (-(lamv * (-(lamv * y t) + Ftot t))) t := by
    have := (hyt.const_mul lamv).neg
    simpa using this
  have hsum := h1.add hF
  convert hsum using 1
  ring

#print axioms kernel_factor
#print axioms duhamelModeCoeff_factored
#print axioms duhamelModeCoeff_hasDerivAt
#print axioms heatDiag_hasDerivAt
#print axioms cosineCoeff_timeDeriv
#print axioms source_timeDeriv_of_time1
#print axioms cosineCoeff_timeDeriv2

end ShenWork.Paper2.IntervalTimeRegDirect
