import ShenWork.Wiener.EWA.WienerLevy

/-!
# EWA brick C1 — flux/source MAP skeleton + eval-agreement (Phase C, E7'a)

The EWA-algebra construction of the chemotaxis-growth flux/source maps as genuine
`EWA T 1` elements, plus the eval-agreement factoring identities (the algebraic
skeleton of the symbol bridge).  NO norm/Lipschitz bounds this brick — those are
the next brick.

* `realPowEWA f γ = f^(⌊γ⌋+1) · FnegEWA f ((⌊γ⌋+1)−γ)` realizes `(eval f)^γ`
  (the WL1 power), mirroring `realPow_eval_EWA` with the explicit `m = ⌊γ⌋+1`.
* `qFactor β v = FnegEWA (1+v) β` realizes `(1+eval v)^{−β}` (WL2), direct from
  `eval_FnegEWA`.
* `vFieldEWA u = R_μ(ν·u^γ) : EWA T 3` is the resolved field.
* `chemFluxEWA u = u · (gDeriv vField) · (1+vField)^{−β} : EWA T 1`, the down-included
  product `B(u) = u·v_x·(1+v)^{−β}`.
* `growthEWA u = u·(a − b·u^α) : EWA T 1`, the source `G(u) = u·(a−b·u^α)`.
* `chemFluxEWA_eval` / `growthEWA_eval`: `evalST` (a `RingHom`) and `GWA.incl`
  (multiplicative) factor the products multiplicatively; `eval(gDeriv v)` is left
  opaque.
-/

open scoped BigOperators
open MeasureTheory Set Real
open ShenWork.GWA ShenWork.Wiener

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-! ### Part 1 — `realPowEWA` (WL1 power) and its eval-agreement. -/

/-- The genuine `EWA T 1` element realizing `(eval f)^γ`, with the explicit
witness `m = ⌊γ⌋+1` (so `m > γ` for `γ ≥ 0` via `Nat.lt_floor_add_one`). -/
def realPowEWA (f : EWA T 1) (γ : ℝ) : EWA T 1 :=
  f ^ (Nat.floor γ + 1) * FnegEWA f ((Nat.floor γ + 1 : ℝ) - γ)

/-- **`realPowEWA_eval`.** Mirrors `realPow_eval_EWA` with `m := ⌊γ⌋+1`. Under the
uniform floor and `f` real, `evalST (incl (realPowEWA f γ)) = (Re(evalST(incl f)))^γ`. -/
theorem realPowEWA_eval {f : EWA T 1} {γ δ : ℝ} (hγ : 0 ≤ γ) (hδpos : 0 < δ)
    (hfloor : UniformFloor f δ)
    (hreal : ∀ (τ : TimeDom T) (x : WA.Circ),
      (evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) f)).im = 0)
    (τ : TimeDom T) (x : WA.Circ) :
    evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) (realPowEWA f γ))
      = (((evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) f)).re ^ γ : ℝ) : ℂ) := by
  set m : ℕ := Nat.floor γ + 1 with hm_def
  have hcast : ((Nat.floor γ + 1 : ℝ) - γ) = ((m : ℝ) - γ) := by
    rw [hm_def]; push_cast; ring
  have hs : 0 < (m : ℝ) - γ := by
    have := Nat.lt_floor_add_one γ
    rw [hm_def]; push_cast; linarith
  set r : ℝ := (evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) f)).re with hr
  have hrpos : 0 < r := lt_of_lt_of_le hδpos (hfloor τ x)
  have hcr : evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) f) = (r : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re]
    · rw [Complex.ofReal_im, hreal τ x]
  have hincl_mul : ∀ a b : EWA T 1,
      GWA.incl (by omega : (0:ℕ) ≤ 1) (a * b)
        = GWA.incl (by omega : (0:ℕ) ≤ 1) a * GWA.incl (by omega : (0:ℕ) ≤ 1) b := by
    intro a b; rw [← GWA.gIncl_apply, map_mul, GWA.gIncl_apply, GWA.gIncl_apply]
  have hincl_pow : GWA.incl (by omega : (0:ℕ) ≤ 1) (f ^ m)
      = (GWA.incl (by omega : (0:ℕ) ≤ 1) f) ^ m := by
    rw [← GWA.gIncl_apply, map_pow, GWA.gIncl_apply]
  have hpow : evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) (f ^ m)) = (r : ℂ) ^ m := by
    rw [hincl_pow, map_pow, hcr]
  have hneg := eval_FnegEWA hs hδpos hfloor hreal τ x
  rw [realPowEWA, hcast, hincl_mul, map_mul, hpow, hneg]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_mul]
  congr 1
  rw [← Real.rpow_natCast r m, ← Real.rpow_add hrpos]
  congr 1; ring

/-! ### Part 2 — `qFactor` (WL2 negative power) and its eval-agreement. -/

/-- The genuine `EWA T 1` element `(1+v)^{−β}`. -/
def qFactor (β : ℝ) (v : EWA T 1) : EWA T 1 := FnegEWA (1 + v) β

/-- **`qFactor_eval`.** Direct from `eval_FnegEWA` with `s := β`, `f := 1+v`. -/
theorem qFactor_eval {β δ : ℝ} {v : EWA T 1} (hβ : 0 < β) (hδpos : 0 < δ)
    (hfloor : UniformFloor (1 + v) δ)
    (hreal : ∀ (τ : TimeDom T) (x : WA.Circ),
      (evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) (1 + v))).im = 0)
    (τ : TimeDom T) (x : WA.Circ) :
    evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) (qFactor β v))
      = (((evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) (1 + v))).re ^ (-β) : ℝ) : ℂ) := by
  rw [qFactor]
  exact eval_FnegEWA hβ hδpos hfloor hreal τ x

/-! ### Part 3 — the assembled maps (resolved field, flux, growth). -/

/-- The resolved field `v = R_μ(ν·u^γ) : EWA T 3`. -/
def vFieldEWA (μ ν γ : ℝ) (hμ : 0 < μ) (u : EWA T 1) : EWA T 3 :=
  GWA.gResolver μ hμ ((ν : ℂ) • realPowEWA u γ)

/-- The chemotactic flux `B(u) = u·v_x·(1+v)^{−β} : EWA T 1`, with the
`gDeriv v : EWA T 2` and the field `v : EWA T 3` down-included to `EWA T 1`. -/
def chemFluxEWA (μ ν β γ : ℝ) (hμ : 0 < μ) (u : EWA T 1) : EWA T 1 :=
  u * GWA.incl (by omega : (1:ℕ) ≤ 2) (GWA.gDeriv (vFieldEWA μ ν γ hμ u))
    * qFactor β (GWA.incl (by omega : (1:ℕ) ≤ 3) (vFieldEWA μ ν γ hμ u))

/-- The logistic growth source `G(u) = u·(a − b·u^α) : EWA T 1`. -/
def growthEWA (α a b : ℝ) (u : EWA T 1) : EWA T 1 :=
  u * ((a : ℂ) • (1 : EWA T 1) - (b : ℂ) • realPowEWA u α)

/-! ### Part 4 — eval-agreement (the algebraic skeleton of the bridge). -/

/-- The `EWA T 1` inclusion `GWA.incl (0≤1)` is multiplicative (via `gIncl`). -/
theorem incl01_mul (a b : EWA T 1) :
    GWA.incl (by omega : (0:ℕ) ≤ 1) (a * b)
      = GWA.incl (by omega : (0:ℕ) ≤ 1) a * GWA.incl (by omega : (0:ℕ) ≤ 1) b := by
  rw [← GWA.gIncl_apply, map_mul, GWA.gIncl_apply, GWA.gIncl_apply]

/-- **`chemFluxEWA_eval`.** `evalST` (a `RingHom`) and `GWA.incl` (multiplicative)
factor the flux product multiplicatively; `eval(gDeriv v)` is left opaque. -/
theorem chemFluxEWA_eval (μ ν β γ : ℝ) (hμ : 0 < μ) (u : EWA T 1)
    (τ : TimeDom T) (x : WA.Circ) :
    evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) (chemFluxEWA μ ν β γ hμ u))
      = evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) u)
        * evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1)
            (GWA.incl (by omega : (1:ℕ) ≤ 2) (GWA.gDeriv (vFieldEWA μ ν γ hμ u))))
        * evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1)
            (qFactor β (GWA.incl (by omega : (1:ℕ) ≤ 3) (vFieldEWA μ ν γ hμ u)))) := by
  rw [chemFluxEWA, incl01_mul, incl01_mul, map_mul, map_mul]

/-- `evalST` sends a `ℂ`-smul to scalar multiplication: `evalST (c • a) = c * evalST a`
(via `Algebra.smul_def` and `evalST` commuting with `algebraMap ℂ`). -/
theorem evalST_smul (τ : TimeDom T) (x : WA.Circ) (c : ℂ) (a : EWA T 0) :
    evalST τ x (c • a) = c * evalST τ x a := by
  rw [Algebra.smul_def, map_mul]
  congr 1
  change evalST τ x (algebraMap ℂ (EWA T 0) c) = c
  rw [evalST_apply]
  rw [show sliceWA τ (algebraMap ℂ (EWA T 0) c) = algebraMap ℂ (WA 0) c from
    (sliceWA τ).commutes c]
  exact (WA.evalAtAlg x).commutes c

/-- **`growthEWA_eval`.** `evalST` (a `RingHom`) factors the source through the
product and the `ℂ`-linear combination (`map_sub` and the `evalST_smul` helper). -/
theorem growthEWA_eval (α a b : ℝ) (u : EWA T 1) (τ : TimeDom T) (x : WA.Circ) :
    evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) (growthEWA α a b u))
      = evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) u)
        * ((a : ℂ)
            - (b : ℂ)
              * evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) (realPowEWA u α))) := by
  have hincl_smul : ∀ (c : ℂ) (w : EWA T 1),
      GWA.incl (by omega : (0:ℕ) ≤ 1) (c • w)
        = c • GWA.incl (by omega : (0:ℕ) ≤ 1) w := by
    intro c w; rw [← GWA.gIncl_apply, map_smul, GWA.gIncl_apply]
  have hincl_one : GWA.incl (by omega : (0:ℕ) ≤ 1) (1 : EWA T 1) = 1 := by
    rw [← GWA.gIncl_apply, map_one]
  have hincl_sub : ∀ p q : EWA T 1,
      GWA.incl (by omega : (0:ℕ) ≤ 1) (p - q)
        = GWA.incl (by omega : (0:ℕ) ≤ 1) p - GWA.incl (by omega : (0:ℕ) ≤ 1) q := by
    intro p q; rw [← GWA.gIncl_apply, map_sub, GWA.gIncl_apply, GWA.gIncl_apply]
  rw [growthEWA, incl01_mul, map_mul, hincl_sub, map_sub,
    hincl_smul, hincl_smul, hincl_one, evalST_smul, evalST_smul, map_one, mul_one]

end ShenWork.EWA

#print axioms ShenWork.EWA.chemFluxEWA_eval
#print axioms ShenWork.EWA.realPowEWA_eval
