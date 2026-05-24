import Mathlib.Analysis.Calculus.Deriv.MeanValue
import ShenWork.PDE.IntervalDomain

noncomputable section

namespace ShenWork.Paper2

class ParabolicMaxPrincipleData (D : BoundedDomainData) where
  supNorm_nonincreasing_of_deriv_nonpos :
    ∀ {u : ℝ → D.Point → ℝ} {I : Set ℝ},
      Convex ℝ I →
      ContinuousOn (fun t => D.supNorm (u t)) I →
      DifferentiableOn ℝ (fun t => D.supNorm (u t)) (interior I) →
      (∀ t, t ∈ interior I →
        deriv (fun s => D.supNorm (u s)) t ≤ 0) →
      ∀ t₁, t₁ ∈ I → ∀ t₂, t₂ ∈ I → t₁ ≤ t₂ →
        D.supNorm (u t₂) ≤ D.supNorm (u t₁)

end ShenWork.Paper2

namespace ShenWork.IntervalDomain

instance intervalDomain_parabolicMaxPrincipleData :
    ShenWork.Paper2.ParabolicMaxPrincipleData intervalDomain where
  supNorm_nonincreasing_of_deriv_nonpos := by
    intro u I hI hcont hdiff hderiv
    exact antitoneOn_of_deriv_nonpos hI hcont hdiff hderiv

end ShenWork.IntervalDomain

end
