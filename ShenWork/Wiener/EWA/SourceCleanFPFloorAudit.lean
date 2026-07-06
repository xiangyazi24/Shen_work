/-
  ShenWork/Wiener/EWA/SourceCleanFPFloorAudit.lean

  Audit lemmas for the lower-floor dependence in the clean prescribed-time
  fixed-point constants.

  These lemmas intentionally do not weaken any theorem.  They expose the exact
  place where the current strict-negative uniform route uses a datum floor:
  all `Fneg` norm/Lipschitz constants in `CleanFPConst` are evaluated at
  `floor / 2`, and the prescribed self-map condition has the same right-hand
  side.  This is the load-bearing obstruction to a floorless
  `DatumWienerData` producer.

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.SourceCleanFPConstants

open ShenWork.GWA

noncomputable section

namespace ShenWork.EWA.CleanFPConst

/-- The fixed-point ball radius and residual lower floor used by the clean
constants. -/
def floorHalf (floor : ℝ) : ℝ := floor / 2

@[simp] theorem floorHalf_eq (floor : ℝ) : floorHalf floor = floor / 2 := rfl

@[simp] theorem rho_eq_floorHalf (floor : ℝ) : ρ floor = floorHalf floor := rfl

theorem floorHalf_pos {floor : ℝ} (hfloor : 0 < floor) : 0 < floorHalf floor := by
  unfold floorHalf
  linarith

theorem R_eq_norm_add_floorHalf (normU0E floor : ℝ) :
    R normU0E floor = normU0E + floorHalf floor := rfl

theorem Md_eq_pi_mul_R (normU0E floor : ℝ) :
    Md normU0E floor = Real.pi * R normU0E floor := rfl

/-- `Mdv` applies the negative-power norm estimate at residual floor
`floor / 2`. -/
theorem Mdv_eq_floorHalf (p : CM2Params) (normU0E floor : ℝ) :
    Mdv p normU0E floor =
      Real.pi * (GWA.resolverGainConst p.μ * (|p.ν| *
        ((R normU0E floor) ^ (Nat.floor p.γ + 1)
          * negNormConst ((Nat.floor p.γ + 1 : ℝ) - p.γ)
              (floorHalf floor) (Md normU0E floor)))) := rfl

/-- The chem-flux self-map constant uses the same residual floor `floor / 2`
in its outer negative-power estimate. -/
theorem M_Q_eq_floorHalf (p : CM2Params) (normU0E floor : ℝ) :
    M_Q p normU0E floor =
      (R normU0E floor) *
        (Real.pi * (GWA.resolverGainConst p.μ * (|p.ν| *
          ((R normU0E floor) ^ (Nat.floor p.γ + 1)
            * negNormConst ((Nat.floor p.γ + 1 : ℝ) - p.γ)
                (floorHalf floor) (Md normU0E floor)))))
        * negNormConst p.β 1 (Mdv p normU0E floor) := rfl

/-- The growth self-map constant uses the residual floor `floor / 2` in the
negative-power estimate for the growth nonlinearity. -/
theorem M_G_eq_floorHalf (p : CM2Params) (normU0E floor : ℝ) :
    M_G p normU0E floor =
      (R normU0E floor) * (|p.a| * 1 + |p.b| *
        ((R normU0E floor) ^ (Nat.floor p.α + 1)
          * negNormConst ((Nat.floor p.α + 1 : ℝ) - p.α)
              (floorHalf floor) (Md normU0E floor))) := rfl

/-- The chem-flux Lipschitz constant uses `floor / 2` in every γ-side
negative-power norm/Lipschitz estimate. -/
theorem L_Q_eq_floorHalf (p : CM2Params) (normU0E floor : ℝ) :
    L_Q p normU0E floor =
      let sγ := (Nat.floor p.γ + 1 : ℝ) - p.γ
      let rr := R normU0E floor
      let md := Md normU0E floor
      let mdv := Mdv p normU0E floor
      let dh := floorHalf floor
      (Real.pi * (GWA.resolverGainConst p.μ * (|p.ν| *
            (rr ^ (Nat.floor p.γ + 1) * negNormConst sγ dh md))))
          * negNormConst p.β 1 mdv * 1
        + rr * negNormConst p.β 1 mdv * (Real.pi * (GWA.resolverGainConst p.μ * (|p.ν| *
            ((Nat.floor p.γ + 1 : ℝ) * rr ^ ((Nat.floor p.γ + 1) - 1)
                * negNormConst sγ dh md
              + rr ^ (Nat.floor p.γ + 1)
                * negLipConst sγ dh md))))
        + rr * (Real.pi * (GWA.resolverGainConst p.μ * (|p.ν| *
            (rr ^ (Nat.floor p.γ + 1) * negNormConst sγ dh md))))
          * (negLipConst p.β 1 mdv * (GWA.resolverGainConst p.μ * (|p.ν| *
              ((Nat.floor p.γ + 1 : ℝ) * rr ^ ((Nat.floor p.γ + 1) - 1)
                  * negNormConst sγ dh md
                + rr ^ (Nat.floor p.γ + 1)
                  * negLipConst sγ dh md)))) := rfl

/-- The growth Lipschitz constant uses `floor / 2` in every α-side
negative-power norm/Lipschitz estimate. -/
theorem L_G_eq_floorHalf (p : CM2Params) (normU0E floor : ℝ) :
    L_G p normU0E floor =
      let sα := (Nat.floor p.α + 1 : ℝ) - p.α
      let rr := R normU0E floor
      let md := Md normU0E floor
      let dh := floorHalf floor
      rr * (|p.b| * ((Nat.floor p.α + 1 : ℝ) * rr ^ ((Nat.floor p.α + 1) - 1)
                * negNormConst sα dh md
              + rr ^ (Nat.floor p.α + 1)
                * negLipConst sα dh md))
        + (|p.a| * 1 + |p.b| *
            (rr ^ (Nat.floor p.α + 1)
              * negNormConst sα dh md)) := rfl

/-- The prescribed self-map smallness target is exactly the same half-floor
radius used in the clean ball. -/
theorem prescribed_smallness_rhs_eq_floorHalf (floor : ℝ) :
    floor / 2 = floorHalf floor := rfl

end ShenWork.EWA.CleanFPConst

#print axioms ShenWork.EWA.CleanFPConst.Mdv_eq_floorHalf
#print axioms ShenWork.EWA.CleanFPConst.M_Q_eq_floorHalf
#print axioms ShenWork.EWA.CleanFPConst.M_G_eq_floorHalf
#print axioms ShenWork.EWA.CleanFPConst.L_Q_eq_floorHalf
#print axioms ShenWork.EWA.CleanFPConst.L_G_eq_floorHalf
