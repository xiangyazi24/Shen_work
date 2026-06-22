import ShenWork.Paper3.IntervalDomainPersistenceLogistic

open Filter Topology ShenWork.IntervalDomain

namespace ShenWork.Paper3

noncomputable section

def PaperFaithfulLiminfLowerUV
    (D : BoundedDomainData) (p : CM2Params)
    (u v : ℝ → D.Point → ℝ) (lowerU : ℝ) : Prop :=
  lowerU ≤ Filter.liminf (fun t => D.infValue (u t)) atTop ∧
    p.ν / p.μ * lowerU ^ p.γ ≤
      Filter.liminf (fun t => D.infValue (v t)) atTop

def PaperFaithfulLiminfCoboundedUV
    (D : BoundedDomainData) (u v : ℝ → D.Point → ℝ) : Prop :=
  IsCoboundedUnder GE.ge atTop (fun t => D.infValue (u t)) ∧
    IsCoboundedUnder GE.ge atTop (fun t => D.infValue (v t))

theorem liminf_ge_of_eventuallyLowerBound
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {δ : ℝ}
    (hcobdd : IsCoboundedUnder GE.ge atTop (fun t => D.infValue (u t)))
    (h : EventuallyLowerBound D u δ) :
    δ ≤ Filter.liminf (fun t => D.infValue (u t)) atTop :=
  Filter.le_liminf_of_le (hf := hcobdd) (h := h.2)

def UniformPersistencePart1LiminfUVRaw
    (D : BoundedDomainData) (p : CM2Params) : Prop :=
  1 ≤ p.m → ∀ u v : ℝ → D.Point → ℝ,
    PositiveGlobalBoundedSolution D p u v →
      ∃ δu > 0, PaperFaithfulLiminfLowerUV D p u v δu

def UniformPersistencePart2LiminfUVRaw
    (D : BoundedDomainData) (p : CM2Params) : Prop :=
  0 < p.a → 0 < p.b → 0 < p.χ₀ → p.m = 1 → 1 ≤ p.β →
    p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)) →
      ∀ u v : ℝ → D.Point → ℝ, PositiveGlobalBoundedSolution D p u v →
        let lowerU :=
          ((p.a - p.χ₀ * p.μ * Theta_beta (p.β - 1)) / p.b) ^
            (1 / p.α)
        PaperFaithfulLiminfLowerUV D p u v lowerU

def UniformPersistencePart3LiminfUVRaw
    (D : BoundedDomainData) (p : CM2Params) : Prop :=
  0 < p.a → 0 < p.b → 0 < p.χ₀ → 1 < p.m → 1 ≤ p.β →
    ∀ u v : ℝ → D.Point → ℝ, PositiveGlobalBoundedSolution D p u v →
      let lowerU :=
        min 1 (p.a / (p.b + p.χ₀ * p.μ * Theta_beta (p.β - 1))) ^
          max (1 / (p.m - 1)) (1 / p.α)
      PaperFaithfulLiminfLowerUV D p u v lowerU

theorem uniformPersistencePart1LiminfUVRaw_of_raw
    {D : BoundedDomainData} {p : CM2Params}
    (h : UniformPersistencePart1Raw D p)
    (_hcobdd : ∀ u v : ℝ → D.Point → ℝ,
      PositiveGlobalBoundedSolution D p u v →
        PaperFaithfulLiminfCoboundedUV D u v) :
    UniformPersistencePart1LiminfUVRaw D p := by
  intro hm u v huv
  rcases h hm u v huv with ⟨δu, hδu, hu, hv⟩
  have hpow :
      δu ^ p.γ ≤ (liminfInfValue D u) ^ p.γ :=
    Real.rpow_le_rpow hδu.le hu p.hγ.le
  have hcoef_nonneg : 0 ≤ p.ν / p.μ :=
    (div_pos p.hν p.hμ).le
  have hvδ :
      p.ν / p.μ * δu ^ p.γ ≤ liminfInfValue D v :=
    (mul_le_mul_of_nonneg_left hpow hcoef_nonneg).trans hv
  exact ⟨δu, hδu, by
    simpa [PaperFaithfulLiminfLowerUV, liminfInfValue] using
      (And.intro hu hvδ)⟩

theorem uniformPersistencePart2LiminfUVRaw_of_raw
    {D : BoundedDomainData} {p : CM2Params}
    (h : UniformPersistencePart2Raw D p)
    (_hcobdd : ∀ u v : ℝ → D.Point → ℝ,
      PositiveGlobalBoundedSolution D p u v →
        PaperFaithfulLiminfCoboundedUV D u v) :
    UniformPersistencePart2LiminfUVRaw D p := by
  intro ha hb hχ0 hm hβ hχ u v huv
  rcases h ha hb hχ0 hm hβ hχ u v huv with ⟨hu, hv⟩
  simpa [PaperFaithfulLiminfLowerUV, liminfInfValue] using
    (And.intro hu hv)

theorem uniformPersistencePart3LiminfUVRaw_of_raw
    {D : BoundedDomainData} {p : CM2Params}
    (h : UniformPersistencePart3Raw D p)
    (_hcobdd : ∀ u v : ℝ → D.Point → ℝ,
      PositiveGlobalBoundedSolution D p u v →
        PaperFaithfulLiminfCoboundedUV D u v) :
    UniformPersistencePart3LiminfUVRaw D p := by
  intro ha hb hχ0 hm hβ u v huv
  rcases h ha hb hχ0 hm hβ u v huv with ⟨hu, hv⟩
  simpa [PaperFaithfulLiminfLowerUV, liminfInfValue] using
    (And.intro hu hv)

end

end ShenWork.Paper3

#print axioms ShenWork.Paper3.liminf_ge_of_eventuallyLowerBound
#print axioms ShenWork.Paper3.uniformPersistencePart1LiminfUVRaw_of_raw
#print axioms ShenWork.Paper3.uniformPersistencePart2LiminfUVRaw_of_raw
#print axioms ShenWork.Paper3.uniformPersistencePart3LiminfUVRaw_of_raw
