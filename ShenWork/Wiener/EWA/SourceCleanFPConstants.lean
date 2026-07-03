/-
  ShenWork/Wiener/EWA/SourceCleanFPConstants.lean

  **Named definitions for the clean FP's contraction and self-map constants.**

  The clean fixed point (`picardEWA_clean_fixedPoint_evenReal`) internally
  computes four T-independent constants (L_Q, L_G, M_Q, M_G) from:
  - `normU₀E` = ‖u₀E‖ (Wiener norm of the initial datum)
  - `floor` = δ (the datum's positive floor)
  - `p : CM2Params` (the PDE parameters)

  These constants determine the contraction rate K(T) = |χ₀|·C₀·L_Q·√T + L_G·T
  and the self-map radius |χ₀|·C₀·M_Q·√T + M_G·T via `exists_small_two_conditions`.

  Extracting them as named `def`s enables:
  1. The prescribed-T FP (takes T + conditions in terms of these `def`s)
  2. Monotonicity proofs (larger ‖u₀E‖ → larger constants → smaller T)
  3. Connection with `exists_uniform_EWA_lifespan` (bar-bounds on these constants)

  All constants match the `set` definitions in
  `SourceFixedPointEvenReal.lean` lines 67-120 EXACTLY.

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.FnegLipschitz
import ShenWork.Wiener.EWA.Basic

open ShenWork.EWA

noncomputable section

namespace ShenWork.EWA.CleanFPConst

variable (p : CM2Params) (normU₀E floor : ℝ)

def R : ℝ := normU₀E + floor / 2

def ρ : ℝ := floor / 2

def Md : ℝ := Real.pi * R normU₀E floor

def Mdv : ℝ :=
  Real.pi * (GWA.resolverGainConst p.μ * (|p.ν| *
    ((R normU₀E floor) ^ (Nat.floor p.γ + 1)
      * negNormConst ((Nat.floor p.γ + 1 : ℝ) - p.γ)
          (floor / 2) (Md normU₀E floor))))

def M_Q : ℝ :=
  (R normU₀E floor) * (Real.pi * (GWA.resolverGainConst p.μ * (|p.ν| *
      ((R normU₀E floor) ^ (Nat.floor p.γ + 1)
        * negNormConst ((Nat.floor p.γ + 1 : ℝ) - p.γ)
            (floor / 2) (Md normU₀E floor)))))
    * negNormConst p.β 1 (Mdv p normU₀E floor)

def M_G : ℝ :=
  (R normU₀E floor) * (|p.a| * 1 + |p.b| *
    ((R normU₀E floor) ^ (Nat.floor p.α + 1)
      * negNormConst ((Nat.floor p.α + 1 : ℝ) - p.α)
          (floor / 2) (Md normU₀E floor)))

def L_Q : ℝ :=
  let sγ := (Nat.floor p.γ + 1 : ℝ) - p.γ
  let rr := R normU₀E floor
  let md := Md normU₀E floor
  let mdv := Mdv p normU₀E floor
  let δρ := floor / 2
  (Real.pi * (GWA.resolverGainConst p.μ * (|p.ν| *
        (rr ^ (Nat.floor p.γ + 1) * negNormConst sγ δρ md))))
      * negNormConst p.β 1 mdv * 1
    + rr * negNormConst p.β 1 mdv * (Real.pi * (GWA.resolverGainConst p.μ * (|p.ν| *
        ((Nat.floor p.γ + 1 : ℝ) * rr ^ ((Nat.floor p.γ + 1) - 1)
            * negNormConst sγ δρ md
          + rr ^ (Nat.floor p.γ + 1)
            * negLipConst sγ δρ md))))
    + rr * (Real.pi * (GWA.resolverGainConst p.μ * (|p.ν| *
        (rr ^ (Nat.floor p.γ + 1) * negNormConst sγ δρ md))))
      * (negLipConst p.β 1 mdv * (GWA.resolverGainConst p.μ * (|p.ν| *
          ((Nat.floor p.γ + 1 : ℝ) * rr ^ ((Nat.floor p.γ + 1) - 1)
              * negNormConst sγ δρ md
            + rr ^ (Nat.floor p.γ + 1)
              * negLipConst sγ δρ md))))

def L_G : ℝ :=
  let sα := (Nat.floor p.α + 1 : ℝ) - p.α
  let rr := R normU₀E floor
  let md := Md normU₀E floor
  let δρ := floor / 2
  rr * (|p.b| * ((Nat.floor p.α + 1 : ℝ) * rr ^ ((Nat.floor p.α + 1) - 1)
            * negNormConst sα δρ md
          + rr ^ (Nat.floor p.α + 1)
            * negLipConst sα δρ md))
    + (|p.a| * 1 + |p.b| *
        (rr ^ (Nat.floor p.α + 1)
          * negNormConst sα δρ md))

/-! ### Nonnegativity of all constants. -/

theorem R_nonneg (hn : 0 ≤ normU₀E) (hf : 0 < floor) : 0 ≤ R normU₀E floor := by
  unfold R; linarith

theorem ρ_pos (hf : 0 < floor) : 0 < ρ floor := by
  unfold ρ; linarith

theorem Md_nonneg (hn : 0 ≤ normU₀E) (hf : 0 < floor) : 0 ≤ Md normU₀E floor := by
  unfold Md R; positivity

/-! ### Nonnegativity of all four contraction/self-map constants. -/

theorem Mdv_nonneg (hn : 0 ≤ normU₀E) (hf : 0 < floor) :
    0 ≤ Mdv p normU₀E floor := by
  unfold Mdv Md R
  have hCμ : (0 : ℝ) ≤ GWA.resolverGainConst p.μ := by
    unfold GWA.resolverGainConst; have := p.hμ; positivity
  have hsγ : 0 < (Nat.floor p.γ + 1 : ℝ) - p.γ := by
    have := Nat.lt_floor_add_one p.γ; linarith
  have hMdnn : (0 : ℝ) ≤ Real.pi * (normU₀E + floor / 2) := by positivity
  have hδρ : 0 < floor / 2 := by linarith
  have hneg := negNormConst_nonneg hsγ hδρ hMdnn
  positivity

theorem L_Q_nonneg (hn : 0 ≤ normU₀E) (hf : 0 < floor) (hβ : 0 < p.β) :
    0 ≤ L_Q p normU₀E floor := by
  unfold L_Q Md Mdv R
  have hCμ : (0 : ℝ) ≤ GWA.resolverGainConst p.μ := by
    unfold GWA.resolverGainConst; have := p.hμ; positivity
  have hsγ : 0 < (Nat.floor p.γ + 1 : ℝ) - p.γ := by
    have := Nat.lt_floor_add_one p.γ; linarith
  have hMdnn : (0 : ℝ) ≤ Real.pi * (normU₀E + floor / 2) := by positivity
  have hδρ : 0 < floor / 2 := by linarith
  have hnegNγ := negNormConst_nonneg hsγ hδρ hMdnn
  have hnegLγ := negLipConst_nonneg hsγ hδρ hMdnn
  have hMdvnn : (0 : ℝ) ≤ Real.pi * (GWA.resolverGainConst p.μ * (|p.ν| *
      ((normU₀E + floor / 2) ^ (Nat.floor p.γ + 1)
        * negNormConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (floor / 2)
            (Real.pi * (normU₀E + floor / 2))))) := by positivity
  have hnegNv := negNormConst_nonneg hβ one_pos hMdvnn
  have hnegLv := negLipConst_nonneg hβ one_pos hMdvnn
  positivity

theorem L_G_nonneg (hn : 0 ≤ normU₀E) (hf : 0 < floor) :
    0 ≤ L_G p normU₀E floor := by
  unfold L_G Md R
  have hsα : 0 < (Nat.floor p.α + 1 : ℝ) - p.α := by
    have := Nat.lt_floor_add_one p.α; linarith
  have hMdnn : (0 : ℝ) ≤ Real.pi * (normU₀E + floor / 2) := by positivity
  have hδρ : 0 < floor / 2 := by linarith
  have hnegNα := negNormConst_nonneg hsα hδρ hMdnn
  have hnegLα := negLipConst_nonneg hsα hδρ hMdnn
  positivity

theorem M_Q_nonneg (hn : 0 ≤ normU₀E) (hf : 0 < floor) (hβ : 0 < p.β) :
    0 ≤ M_Q p normU₀E floor := by
  unfold M_Q Md Mdv R
  have hCμ : (0 : ℝ) ≤ GWA.resolverGainConst p.μ := by
    unfold GWA.resolverGainConst; have := p.hμ; positivity
  have hsγ : 0 < (Nat.floor p.γ + 1 : ℝ) - p.γ := by
    have := Nat.lt_floor_add_one p.γ; linarith
  have hMdnn : (0 : ℝ) ≤ Real.pi * (normU₀E + floor / 2) := by positivity
  have hδρ : 0 < floor / 2 := by linarith
  have hnegNγ := negNormConst_nonneg hsγ hδρ hMdnn
  have hMdvnn : (0 : ℝ) ≤ Real.pi * (GWA.resolverGainConst p.μ * (|p.ν| *
      ((normU₀E + floor / 2) ^ (Nat.floor p.γ + 1)
        * negNormConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (floor / 2)
            (Real.pi * (normU₀E + floor / 2))))) := by positivity
  have hnegNv := negNormConst_nonneg hβ one_pos hMdvnn
  positivity

theorem M_G_nonneg (hn : 0 ≤ normU₀E) (hf : 0 < floor) :
    0 ≤ M_G p normU₀E floor := by
  unfold M_G Md R
  have hsα : 0 < (Nat.floor p.α + 1 : ℝ) - p.α := by
    have := Nat.lt_floor_add_one p.α; linarith
  have hMdnn : (0 : ℝ) ≤ Real.pi * (normU₀E + floor / 2) := by positivity
  have hδρ : 0 < floor / 2 := by linarith
  have hnegNα := negNormConst_nonneg hsα hδρ hMdnn
  positivity

end ShenWork.EWA.CleanFPConst
