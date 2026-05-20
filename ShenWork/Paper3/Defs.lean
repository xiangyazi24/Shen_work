/-
  ShenWork/Paper3/Defs.lean
  Chen-Ruau-Shen (arXiv:2604.02599): Persistence and stabilization
-/
import ShenWork.Paper2.Defs

noncomputable section

def equilibrium (p : CM2Params) (_hab : 0 < p.a ∧ 0 < p.b) : ℝ × ℝ :=
  ((p.a / p.b) ^ (1 / p.α), p.ν / p.μ * ((p.a / p.b) ^ (1 / p.α)) ^ p.γ)

end
