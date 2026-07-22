import ShenWork.Paper1.Statements

namespace ShenWork.Paper1

noncomputable section

/-- The two signal estimates in Lemma 5.1 for an arbitrary regular traveling
wave once its elliptic component has been identified with the frozen
resolvent. -/
theorem Lemma_5_1_arbitrary_wave
    {p : CMParams} {c : ℝ} (hc : 2 < c)
    {U V : ℝ → ℝ}
    (_hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hresolvent : V = frozenElliptic p U) :
    (∀ x,
      |V x| ≤ (MChi p) ^ p.γ ∧
        |deriv V x| ≤ (MChi p) ^ p.γ) ∧
    (p.γ + p.γ⁻¹ < c →
      ∀ x,
        |V x| ≤
          min ((MChi p) ^ p.γ)
            ((1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
              Real.exp (-(kappa c) * p.γ * x)) ∧
        |deriv V x| ≤
          min ((MChi p) ^ p.γ)
            ((1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
              Real.exp (-(kappa c) * p.γ * x))) := by
  subst V
  exact Lemma_5_1.fixed_point_signal_statement_of_continuous
    p hc hreg.U_cont hbound

#print axioms Lemma_5_1_arbitrary_wave

end

end ShenWork.Paper1
