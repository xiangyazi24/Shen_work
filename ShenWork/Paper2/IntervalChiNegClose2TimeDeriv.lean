/-
  ShenWork/Paper2/IntervalChiNegClose2TimeDeriv.lean

  TASK 4 (the χ₀<0 closer) — the POINTWISE-IN-SPACE time derivative of the
  solution slice lift, obtained by passing `∂ₜ` through the cosine series ∑'.

  This is the TIME mirror of WALL-C's spatial passage
  (`memHSigma_contDiff_two` / `cosineCoeffSeries_contDiff_two`): there the
  SPATIAL derivative is passed through `∑'ₖ bₖ cos(kπx)` under the
  eigenvalue-weighted ℓ¹ control `Σ λₖ|bₖ| < ∞`; here the TIME derivative is
  passed through `∑'ₖ âₖ(r) cos(kπx)` under a UNIFORM-IN-TIME summable control
  of the differentiated coefficient series

      `Σₖ |−λₖ·âₖ(r) + Ftotalₖ(r)| ≤ uₖ`,   `Σₖ uₖ < ∞`,

  the per-coefficient time derivative `−λₖ·âₖ + Ftotalₖ` being EXACTLY the
  landed diagonalized-PDE derivative `cosineCoeff_timeDeriv`
  (IntervalTimeRegDirect.lean).  Since `|cos(kπx)| ≤ 1`, the same `uₖ` dominates
  the spatial-evaluated term derivative, and Mathlib's
  `hasDerivAt_tsum` (uniform summable derivative bound) gives the termwise
  time-differentiation of the slice's cosine series.

  The slice's cosine representation
      `intervalDomainLift (u r) x = ∑'ₖ âₖ(r)·cos(kπx)`   (for r in a nbhd, ∀x)
  is supplied as a hypothesis `hrep` — it is the carried restart/cosine
  agreement (`HasRestartCosineRepresentations` / `ChemDivHalfStepSourceData.hagree`),
  the genuinely algebraic restart obligation, not a free consequence of the bare
  mild fixed point.  The uniform summable bound `hUbound` is the high-σ uniform
  envelope of the bootstrap.

  NON-CIRCULAR: uses only `cosineCoeff_timeDeriv` (FTC + product rule, landed),
  `|cos| ≤ 1`, and Mathlib `hasDerivAt_tsum`.

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New file, new names only.
-/
import ShenWork.Paper2.IntervalTimeRegDirect
import ShenWork.Paper2.IntervalCosineSobolevEmbedding
import Mathlib.Analysis.Calculus.SmoothSeries

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegClose2TimeDeriv

open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.Paper2.HSigmaScale (lam)
open ShenWork.Paper2.BFormHSigmaDuhamelEnergy (duhamelEnergyCoeff)
open ShenWork.Paper2.IntervalTimeRegDirect (FtotalCoeff cosineCoeff_timeDeriv)
open ShenWork.CosineSpectrum (cosineMode)
open Real

/-- `|cosineMode k x| ≤ 1` for every mode/point — the spatial envelope that lets
the eigenvalue-weighted ℓ¹ time-derivative bound dominate the term derivatives. -/
theorem abs_cosineMode_le_one (k : ℕ) (x : ℝ) : |cosineMode k x| ≤ 1 := by
  unfold cosineMode; exact Real.abs_cos_le_one _

/-- **TASK 4 — pointwise-in-space time derivative of the slice cosine series.**

Fix `x`.  Suppose, on a time-neighborhood of every point (here: on all of `ℝ`),
the slice lift agrees with its cosine series, the per-coefficient diagonalized-PDE
time derivative (`cosineCoeff_timeDeriv`) holds at every time, and the
differentiated coefficient series has a uniform-in-time summable majorant `u`.
Then the slice value `r ↦ ∑'ₖ âₖ(r)·cos(kπx)` is time-differentiable, with
derivative `∑'ₖ (−λₖ·âₖ(t) + Ftotalₖ(t))·cos(kπx)`.

This is the time mirror of WALL-C: the same uniform-summable-derivative engine
(`hasDerivAt_tsum`), now in `t` rather than `x`, fed by the landed
`cosineCoeff_timeDeriv` per-mode derivative and `|cos|≤1`. -/
theorem hasDerivAt_cosineSeries_time
    {χ₀ : ℝ} {uLift : ℝ → ℝ → ℝ} {a₀ : ℕ → ℝ} {Fc Fl : ℕ → ℝ → ℝ}
    {u : ℕ → ℝ} (x t : ℝ)
    (hFc : ∀ k, Continuous (Fc k)) (hFl : ∀ k, Continuous (Fl k))
    (hdecomp : ∀ k r, cosineCoeffs (uLift r) k
      = Real.exp (-(r * lam k)) * a₀ k
        + (-χ₀) * duhamelEnergyCoeff 1 Fc r k
        + duhamelEnergyCoeff 1 Fl r k)
    (hUsum : Summable u)
    (hUbound : ∀ k r,
      |-(lam k * cosineCoeffs (uLift r) k) + FtotalCoeff χ₀ Fc Fl k r| ≤ u k)
    (hconv : Summable fun k => cosineCoeffs (uLift t) k * cosineMode k x) :
    HasDerivAt (fun r => ∑' k, cosineCoeffs (uLift r) k * cosineMode k x)
      (∑' k, (-(lam k * cosineCoeffs (uLift t) k) + FtotalCoeff χ₀ Fc Fl k t)
        * cosineMode k x) t := by
  -- per-mode time derivative of the spatially-evaluated term
  set g : ℕ → ℝ → ℝ := fun k r => cosineCoeffs (uLift r) k * cosineMode k x with hg
  set g' : ℕ → ℝ → ℝ := fun k r =>
    (-(lam k * cosineCoeffs (uLift r) k) + FtotalCoeff χ₀ Fc Fl k r) * cosineMode k x with hg'
  have hgderiv : ∀ k r, HasDerivAt (g k) (g' k r) r := by
    intro k r
    have h := (cosineCoeff_timeDeriv (χ₀ := χ₀) (uLift := uLift) (a₀ := a₀)
      (Fc := Fc) (Fl := Fl) k r (hFc k) (hFl k) (fun s => hdecomp k s)).mul_const
      (cosineMode k x)
    simpa [hg, hg'] using h
  -- uniform summable bound: `|g' k r| ≤ |…|·|cos| ≤ u k`
  have hgbound : ∀ k r, ‖g' k r‖ ≤ u k := by
    intro k r
    have hcos := abs_cosineMode_le_one k x
    have hval :=
      hUbound k r
    rw [Real.norm_eq_abs, hg']
    simp only
    rw [abs_mul]
    have hle : |(-(lam k * cosineCoeffs (uLift r) k) + FtotalCoeff χ₀ Fc Fl k r)| ≤ u k := hval
    calc |(-(lam k * cosineCoeffs (uLift r) k) + FtotalCoeff χ₀ Fc Fl k r)| * |cosineMode k x|
        ≤ u k * 1 := mul_le_mul hle hcos (abs_nonneg _) (le_trans (abs_nonneg _) hle)
      _ = u k := by ring
  -- the value series converges at the base point t
  have hg0 : Summable fun k => g k t := by simpa [hg] using hconv
  have hmain := hasDerivAt_tsum (u := u) (g := g) (g' := g') hUsum hgderiv hgbound hg0 t
  -- rewrite the derivative value: g' k t = (−λ·â(t)+Ftotal(t))·cos
  have hgt : (fun k => g' k t)
      = fun k => (-(lam k * cosineCoeffs (uLift t) k) + FtotalCoeff χ₀ Fc Fl k t)
        * cosineMode k x := by funext k; rfl
  rw [hgt] at hmain
  exact hmain

/-- **TASK 4 (target shape) — `gradientSolution_timeDeriv_pointwise`.**

The slice lift `r ↦ intervalDomainLift (u r) x` is time-differentiable at `t`,
with the time derivative given by the diagonalized-PDE series

    du t x = ∑'ₖ (−λₖ·âₖ(t) + Ftotalₖ(t))·cos(kπx).

Obtained from `hasDerivAt_cosineSeries_time` by rewriting the function along the
carried cosine representation `hrep` (the restart/cosine agreement). -/
theorem gradientSolution_timeDeriv_pointwise
    {χ₀ : ℝ} {uLift : ℝ → ℝ → ℝ} {a₀ : ℕ → ℝ} {Fc Fl : ℕ → ℝ → ℝ}
    {u : ℕ → ℝ} (x t : ℝ)
    (hFc : ∀ k, Continuous (Fc k)) (hFl : ∀ k, Continuous (Fl k))
    (hdecomp : ∀ k r, cosineCoeffs (uLift r) k
      = Real.exp (-(r * lam k)) * a₀ k
        + (-χ₀) * duhamelEnergyCoeff 1 Fc r k
        + duhamelEnergyCoeff 1 Fl r k)
    (hUsum : Summable u)
    (hUbound : ∀ k r,
      |-(lam k * cosineCoeffs (uLift r) k) + FtotalCoeff χ₀ Fc Fl k r| ≤ u k)
    (hconv : Summable fun k => cosineCoeffs (uLift t) k * cosineMode k x)
    (hrep : ∀ r, uLift r x = ∑' k, cosineCoeffs (uLift r) k * cosineMode k x) :
    HasDerivAt (fun r => uLift r x)
      (∑' k, (-(lam k * cosineCoeffs (uLift t) k) + FtotalCoeff χ₀ Fc Fl k t)
        * cosineMode k x) t := by
  have hfun : (fun r => uLift r x)
      = fun r => ∑' k, cosineCoeffs (uLift r) k * cosineMode k x := by
    funext r; exact hrep r
  rw [hfun]
  exact hasDerivAt_cosineSeries_time x t hFc hFl hdecomp hUsum hUbound hconv

/-! ## Second time derivative (`time2`) — the diagonalized `∂ₜₜ`.

Differentiate once more.  The per-mode second derivative is supplied by
`cosineCoeff_timeDeriv2` (landed); passing `∂ₜₜ` through the series needs ONE more
uniform-summable bound `u₂ₖ ≥ |λₖ²·âₖ − λₖ·Ftotalₖ + Fdotₖ|` (one more σ in the
high-σ envelope), exactly as the prompt notes.  Here we package the abstract
termwise second-differentiation: given per-mode first derivatives `g'ₖ(r)` and a
uniform-summable bound on the per-mode SECOND derivative values, the
spatially-evaluated first-derivative series differentiates termwise. -/
theorem hasDerivAt_cosineSeries_time2
    {lamv : ℕ → ℝ} {y Ftot : ℝ → ℕ → ℝ} {Fdot : ℝ → ℕ → ℝ}
    {u₂ : ℕ → ℝ} (x t : ℝ)
    (hy1 : ∀ k r, HasDerivAt (fun s => y s k) (-(lamv k * y r k) + Ftot r k) r)
    (hF : ∀ k r, HasDerivAt (fun s => Ftot s k) (Fdot r k) r)
    (hUsum : Summable u₂)
    (hUbound : ∀ k r, |lamv k ^ 2 * y r k - lamv k * Ftot r k + Fdot r k| ≤ u₂ k)
    (hconv : Summable fun k =>
      (-(lamv k * y t k) + Ftot t k) * cosineMode k x) :
    HasDerivAt
      (fun r => ∑' k, (-(lamv k * y r k) + Ftot r k) * cosineMode k x)
      (∑' k, (lamv k ^ 2 * y t k - lamv k * Ftot t k + Fdot t k) * cosineMode k x) t := by
  set g : ℕ → ℝ → ℝ := fun k r => (-(lamv k * y r k) + Ftot r k) * cosineMode k x with hg
  set g' : ℕ → ℝ → ℝ := fun k r =>
    (lamv k ^ 2 * y r k - lamv k * Ftot r k + Fdot r k) * cosineMode k x with hg'
  -- per-mode second derivative at EVERY r via cosineCoeff_timeDeriv2
  have hgderiv : ∀ k r, HasDerivAt (g k) (g' k r) r := by
    intro k r
    have h2 := ShenWork.Paper2.IntervalTimeRegDirect.cosineCoeff_timeDeriv2
      (lamv := lamv k) (y := fun s => y s k) (Ftot := fun s => Ftot s k)
      (Fdot := Fdot r k) r (fun s => hy1 k s) (hF k r)
    simpa [hg, hg'] using h2.mul_const (cosineMode k x)
  have hgbound : ∀ k r, ‖g' k r‖ ≤ u₂ k := by
    intro k r
    rw [Real.norm_eq_abs, hg', abs_mul]
    calc |lamv k ^ 2 * y r k - lamv k * Ftot r k + Fdot r k| * |cosineMode k x|
        ≤ u₂ k * 1 := mul_le_mul (hUbound k r) (abs_cosineMode_le_one k x) (abs_nonneg _)
          (le_trans (abs_nonneg _) (hUbound k r))
      _ = u₂ k := by ring
  have hg0 : Summable fun k => g k t := by simpa [hg] using hconv
  have hmain := hasDerivAt_tsum (u := u₂) (g := g) (g' := g') hUsum hgderiv hgbound hg0 t
  have hgt : (fun k => g' k t)
      = fun k => (lamv k ^ 2 * y t k - lamv k * Ftot t k + Fdot t k) * cosineMode k x := by
    funext k; rfl
  rw [hgt] at hmain
  exact hmain

end ShenWork.Paper2.IntervalChiNegClose2TimeDeriv

#print axioms ShenWork.Paper2.IntervalChiNegClose2TimeDeriv.abs_cosineMode_le_one
#print axioms ShenWork.Paper2.IntervalChiNegClose2TimeDeriv.hasDerivAt_cosineSeries_time
#print axioms ShenWork.Paper2.IntervalChiNegClose2TimeDeriv.gradientSolution_timeDeriv_pointwise
#print axioms ShenWork.Paper2.IntervalChiNegClose2TimeDeriv.hasDerivAt_cosineSeries_time2
