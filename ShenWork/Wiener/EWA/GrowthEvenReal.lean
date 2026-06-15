import ShenWork.Wiener.EWA.EvenRealClosure
import ShenWork.Wiener.EWA.Flux

/-!
# EWA brick (parity) — `growthEWA` is EvenReal (modulo WL)

The logistic growth term `growthEWA α a b u = u · (a•1 − b•realPowEWA u α)` preserves
the even-real structure of its argument `u`, modulo the same Wiener–Lévy parity hypothesis
`FnegEWA_evenReal_Hyp` that the rest of the parity closure carries.

This is the value-leg parity input for the χ₀<0 source-form realization assembly:
`valDuhamelEWA (growthEWA …)`'s cosine-synthesis bridge
(`valDuhamelEWA_evalST_eq_cosineSynthesis`, `SourceDuhamelSynthesis.lean`) requires the
argument to be even-real, exactly as `chemFluxEWA_oddImag` feeds the divergence leg.
-/

namespace ShenWork.EWA

variable {T : ℝ}

/-- **`growthEWA` preserves EvenReal** (modulo the WL-parity hypothesis).
`growthEWA α a b u = u · (a•1 − b•realPowEWA u α)`:
`u` is EvenReal by hypothesis; `a•1` is EvenReal (`one` + `smul_real`);
`b•realPowEWA u α` is EvenReal (`realPowEWA_evenReal` + `smul_real`); their difference is
EvenReal (rewrite `X − Y = X + (−b)•…`, then `add`); the product `u · (…)` closes by
`EvenRealEWA.mul`. -/
theorem growthEWA_evenReal (hWL : FnegEWA_evenReal_Hyp)
    {α a b : ℝ} {u : EWA T 1} (hu : EvenRealEWA u) :
    EvenRealEWA (growthEWA α a b u) := by
  rw [growthEWA]
  -- the bracket `a•1 − b•realPowEWA u α` is even-real.
  have hpow : EvenRealEWA (realPowEWA u α) := realPowEWA_evenReal hWL hu α
  have heq : (a : ℂ) • (1 : EWA T 1) - (b : ℂ) • realPowEWA u α
      = (a : ℂ) • (1 : EWA T 1) + ((-b : ℝ) : ℂ) • realPowEWA u α := by
    rw [Complex.ofReal_neg, neg_smul]; abel
  have hbr : EvenRealEWA ((a : ℂ) • (1 : EWA T 1) - (b : ℂ) • realPowEWA u α) := by
    rw [heq]
    exact (EvenRealEWA.one.smul_real a).add (hpow.smul_real (-b))
  exact hu.mul hbr

end ShenWork.EWA
