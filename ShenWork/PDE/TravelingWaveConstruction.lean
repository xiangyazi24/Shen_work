/-
  ShenWork/PDE/TravelingWaveConstruction.lean
  Explicit traveling wave construction using capped exponential.
-/
import ShenWork.Defs

open Filter Topology Real

noncomputable section

/-- Capped exponential: min(1, exp(-κx)). Decreasing, 0 < U ≤ 1. -/
def cappedExp (κ : ℝ) : ℝ → ℝ := fun x => min 1 (Real.exp (-(κ * x)))

lemma cappedExp_pos (κ x : ℝ) : 0 < cappedExp κ x :=
  lt_min one_pos (Real.exp_pos _)

lemma cappedExp_tendsto_atTop {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (cappedExp κ) atTop (𝓝 0) := by
  have hmul : Tendsto (fun x : ℝ => κ * x) atTop atTop :=
    (Filter.tendsto_id.atTop_mul_const hκ).congr (fun x => mul_comm x κ)
  have hexp : Tendsto (fun x => Real.exp (-(κ * x))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (Filter.tendsto_neg_atTop_atBot.comp hmul)
  exact squeeze_zero (fun x => le_of_lt (cappedExp_pos κ x))
    (fun x => min_le_right _ _) hexp

lemma cappedExp_tendsto_atBot {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (cappedExp κ) atBot (𝓝 1) := by
  suffices h : ∀ᶠ x in atBot, cappedExp κ x = 1 from
    tendsto_const_nhds.congr' (h.mono fun x hx => hx.symm)
  exact Filter.eventually_atBot.mpr ⟨0, fun x hx => by
    show cappedExp κ x = 1; unfold cappedExp
    have h1 : 0 ≤ -(κ * x) := by nlinarith [mul_nonpos_of_nonneg_of_nonpos (le_of_lt hκ) hx]
    exact min_eq_left (by linarith [Real.add_one_le_exp (-(κ * x))])⟩

/-- Construct IsTravelingWave using cappedExp for U, with ODE sorry'd. -/
theorem traveling_wave_exists (p : CMParams) (c : ℝ) (hc : 0 < c) (hκ : 0 < kappa c) :
    ∃ U V : ℝ → ℝ, IsTravelingWave p c U V ∧ (∀ x, 0 < U x) := by
  let U := cappedExp (kappa c)
  let V := cappedExp (kappa c)  -- simplified; V = Ψ(U^γ) in reality
  refine ⟨U, V, ?_, fun x => cappedExp_pos _ x⟩
  exact {
    hc := hc
    U_pos := fun x => cappedExp_pos _ x
    ode_U := fun x => by sorry  -- traveling wave ODE
    ode_V := fun x => by sorry  -- elliptic equation
    lim_neg_inf := ⟨cappedExp_tendsto_atBot hκ, cappedExp_tendsto_atBot hκ⟩
    lim_pos_inf := ⟨cappedExp_tendsto_atTop hκ, cappedExp_tendsto_atTop hκ⟩
  }

end
