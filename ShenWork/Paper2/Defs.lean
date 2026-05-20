/-
  ShenWork/Paper2/Defs.lean
  Chen-Ruau-Shen (arXiv:2512.14858): Boundedness and global existence
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

structure CM2Params where
  N : ℕ
  hN : 0 < N
  α : ℝ
  γ : ℝ
  m : ℝ
  μ : ℝ
  ν : ℝ
  χ₀ : ℝ
  a : ℝ
  b : ℝ
  β : ℝ
  hα : 0 < α
  hγ : 0 < γ
  hm : 0 < m
  hμ : 0 < μ
  hν : 0 < ν
  ha : 0 ≤ a
  hb : 0 ≤ b
  hβ : 0 ≤ β

def Psi_beta (β : ℝ) : ℝ := (β / (1 + β)) ^ (1 + β)
def Theta_beta (β : ℝ) : ℝ := β ^ β * (1 + β) ^ (-(1 + β))

end
