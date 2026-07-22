import ShenWork.Paper1.Statements

namespace ShenWork.Paper1

noncomputable section

/-- Lemma 5.2 for an arbitrary monotone traveling wave.  Positivity is part
of `IsTravelingWave`; no fixed-point construction is used. -/
theorem Lemma_5_2_arbitrary_monotone_wave
    {p : CMParams} {c : ℝ}
    (hspeed :
      c > max (p.γ + p.γ⁻¹)
        (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)))
    {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hmono : ∀ x, deriv U x ≤ 0) :
    ∃ B > 0, ∀ x, deriv U x / U x ≤ B := by
  exact Lemma_5_2.nonincreasing_branch hspeed hTW hbound hmono

#print axioms Lemma_5_2_arbitrary_monotone_wave

end

end ShenWork.Paper1
