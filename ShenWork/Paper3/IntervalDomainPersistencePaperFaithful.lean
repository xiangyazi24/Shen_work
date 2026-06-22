import Mathlib.Topology.Order.LiminfLimsup
import ShenWork.Paper3.IntervalDomainPersistenceActualMInterface
open Filter Topology
namespace ShenWork.Paper3
noncomputable section
def PaperFaithfulEventuallyLower
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ) (theta : ℝ) : Prop :=
  ∀ eps > 0, ∀ᶠ t in atTop, theta - eps ≤ D.infValue (u t)

theorem paperFaithfulEventuallyLower_of_liminf
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {theta : ℝ}
    (hbdd : IsBoundedUnder GE.ge atTop (fun t => D.infValue (u t)))
    (hlim : theta ≤ Filter.liminf (fun t => D.infValue (u t)) atTop) :
    PaperFaithfulEventuallyLower D u theta := by
  intro eps heps
  have hneg : -eps < 0 := by linarith
  exact (eventually_add_neg_lt_of_le_liminf hbdd hlim hneg).mono
    (fun _ ht => le_of_lt (by simpa [sub_eq_add_neg] using ht))

def UniformPersistencePart1LiminfRaw
    (D : BoundedDomainData) (p : CM2Params) : Prop :=
  1 ≤ p.m → ∀ u v : ℝ → D.Point → ℝ,
    PositiveGlobalBoundedSolution D p u v →
      ∃ deltaU > 0, deltaU ≤ Filter.liminf (fun t => D.infValue (u t)) atTop
def UniformPersistencePart1EpsRaw
    (D : BoundedDomainData) (p : CM2Params) : Prop :=
  1 ≤ p.m → ∀ u v : ℝ → D.Point → ℝ,
    PositiveGlobalBoundedSolution D p u v →
      ∃ deltaU > 0, PaperFaithfulEventuallyLower D u deltaU
def UniformPersistencePart2LiminfRaw
    (D : BoundedDomainData) (p : CM2Params) : Prop :=
  0 < p.a → 0 < p.b → 0 < p.χ₀ → p.m = 1 → 1 ≤ p.β →
    p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)) →
      ∀ u v : ℝ → D.Point → ℝ, PositiveGlobalBoundedSolution D p u v →
        let lowerU :=
          ((p.a - p.χ₀ * p.μ * Theta_beta (p.β - 1)) / p.b) ^
            (1 / p.α)
        lowerU ≤ Filter.liminf (fun t => D.infValue (u t)) atTop
def UniformPersistencePart2EpsRaw
    (D : BoundedDomainData) (p : CM2Params) : Prop :=
  0 < p.a → 0 < p.b → 0 < p.χ₀ → p.m = 1 → 1 ≤ p.β →
    p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)) →
      ∀ u v : ℝ → D.Point → ℝ, PositiveGlobalBoundedSolution D p u v →
        let lowerU :=
          ((p.a - p.χ₀ * p.μ * Theta_beta (p.β - 1)) / p.b) ^
            (1 / p.α)
        PaperFaithfulEventuallyLower D u lowerU
def UniformPersistencePart3LiminfRaw
    (D : BoundedDomainData) (p : CM2Params) : Prop :=
  0 < p.a → 0 < p.b → 0 < p.χ₀ → 1 < p.m → 1 ≤ p.β →
    ∀ u v : ℝ → D.Point → ℝ, PositiveGlobalBoundedSolution D p u v →
      let lowerU :=
        (min 1 (p.a / (p.b + p.χ₀ * p.μ * Theta_beta (p.β - 1))) ^
          max (1 / (p.m - 1)) (1 / p.α))
      lowerU ≤ Filter.liminf (fun t => D.infValue (u t)) atTop
def UniformPersistencePart3EpsRaw
    (D : BoundedDomainData) (p : CM2Params) : Prop :=
  0 < p.a → 0 < p.b → 0 < p.χ₀ → 1 < p.m → 1 ≤ p.β →
    ∀ u v : ℝ → D.Point → ℝ, PositiveGlobalBoundedSolution D p u v →
      let lowerU :=
        (min 1 (p.a / (p.b + p.χ₀ * p.μ * Theta_beta (p.β - 1))) ^
          max (1 / (p.m - 1)) (1 / p.α))
      PaperFaithfulEventuallyLower D u lowerU
theorem uniformPersistencePart1EpsRaw_of_liminfRaw
    {D : BoundedDomainData} {p : CM2Params}
    (h : UniformPersistencePart1LiminfRaw D p)
    (hbdd : ∀ u v : ℝ → D.Point → ℝ, PositiveGlobalBoundedSolution D p u v →
      IsBoundedUnder GE.ge atTop (fun t => D.infValue (u t))) :
    UniformPersistencePart1EpsRaw D p := by
  intro hm u v huv
  rcases h hm u v huv with ⟨deltaU, hdeltaU, hlim⟩
  exact ⟨deltaU, hdeltaU, paperFaithfulEventuallyLower_of_liminf (hbdd u v huv) hlim⟩
theorem uniformPersistencePart2EpsRaw_of_liminfRaw
    {D : BoundedDomainData} {p : CM2Params}
    (h : UniformPersistencePart2LiminfRaw D p)
    (hbdd : ∀ u v : ℝ → D.Point → ℝ, PositiveGlobalBoundedSolution D p u v →
      IsBoundedUnder GE.ge atTop (fun t => D.infValue (u t))) :
    UniformPersistencePart2EpsRaw D p := by
  intro ha hb hχ0 hm hβ hχ u v huv
  exact paperFaithfulEventuallyLower_of_liminf (hbdd u v huv)
    (h ha hb hχ0 hm hβ hχ u v huv)
theorem uniformPersistencePart3EpsRaw_of_liminfRaw
    {D : BoundedDomainData} {p : CM2Params}
    (h : UniformPersistencePart3LiminfRaw D p)
    (hbdd : ∀ u v : ℝ → D.Point → ℝ, PositiveGlobalBoundedSolution D p u v →
      IsBoundedUnder GE.ge atTop (fun t => D.infValue (u t))) :
    UniformPersistencePart3EpsRaw D p := by
  intro ha hb hχ0 hm hβ u v huv
  exact paperFaithfulEventuallyLower_of_liminf (hbdd u v huv)
    (h ha hb hχ0 hm hβ u v huv)
end
end ShenWork.Paper3
#print axioms ShenWork.Paper3.paperFaithfulEventuallyLower_of_liminf
#print axioms ShenWork.Paper3.uniformPersistencePart1EpsRaw_of_liminfRaw
#print axioms ShenWork.Paper3.uniformPersistencePart2EpsRaw_of_liminfRaw
#print axioms ShenWork.Paper3.uniformPersistencePart3EpsRaw_of_liminfRaw
