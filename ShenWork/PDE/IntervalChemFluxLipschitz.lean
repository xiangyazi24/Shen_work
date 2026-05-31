/-
  ShenWork/PDE/IntervalChemFluxLipschitz.lean

  T7 existence — **glue atom 1**: the chemotaxis flux
  `Q(u)(y) = u(y)·∂ₓR(u)(y)/(1+R(u)(y))^β` is sup-Lipschitz on the trajectory
  ball, given the resolver `C⁰→C¹` bounds (Atom B) and `R ≥ 0` (O1).

  This file starts with the denominator factor `(1+r)^{−β}`: with `R ≥ 0` the
  base is `≥ 1`, so `(1+r)^{−β}` is well-defined and globally `β`-Lipschitz on
  `[0,∞)` (its derivative `−β(1+r)^{−β−1}` has modulus `≤ β`).

  No `sorry`, no `admit`, no custom `axiom`.
-/
import ShenWork.Paper2.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open Set Real

noncomputable section

namespace ShenWork.IntervalChemFluxLipschitz

/-- **`(1+r)^{−β}` is `β`-Lipschitz on `[0,∞)`** (`β ≥ 0`).  The base `1+r ≥ 1` is
nonzero, so `f(r)=(1+r)^{−β}` is differentiable with `f'(r)=−β(1+r)^{−β−1}`, and
`|f'(r)| = β(1+r)^{−β−1} ≤ β` since `(1+r)^{−β−1} ≤ 1` (base `≥ 1`, exponent
`≤ 0`).  Hence the mean-value Lipschitz bound. -/
theorem oneAddRpow_neg_lipschitz {β : ℝ} (hβ : 0 ≤ β) {r₁ r₂ : ℝ}
    (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) :
    |(1 + r₁) ^ (-β) - (1 + r₂) ^ (-β)| ≤ β * |r₁ - r₂| := by
  set f : ℝ → ℝ := fun r => (1 + r) ^ (-β) with hf
  set fp : ℝ → ℝ := fun r => -β * (1 + r) ^ (-β - 1) with hfp
  have hder : ∀ r ∈ Set.Ici (0:ℝ), HasDerivWithinAt f (fp r) (Set.Ici 0) r := by
    intro r hr
    have hbase : (0:ℝ) < 1 + r := by have := (Set.mem_Ici.mp hr); linarith
    have hpow : HasDerivAt (fun b : ℝ => b ^ (-β)) (-β * (1 + r) ^ (-β - 1)) (1 + r) :=
      Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hbase))
    have hinner : HasDerivAt (fun r : ℝ => 1 + r) 1 r := by
      simpa using (hasDerivAt_const r (1:ℝ)).add (hasDerivAt_id r)
    have hcomp : HasDerivAt f (-β * (1 + r) ^ (-β - 1) * 1) r := by
      simpa [hf] using hpow.comp r hinner
    rw [mul_one] at hcomp
    exact hcomp.hasDerivWithinAt
  have hbound : ∀ r ∈ Set.Ici (0:ℝ), ‖fp r‖ ≤ β := by
    intro r hr
    have hbase : (1:ℝ) ≤ 1 + r := by have := (Set.mem_Ici.mp hr); linarith
    have hle1 : (1 + r) ^ (-β - 1) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hbase (by linarith)
    have hpos : 0 ≤ (1 + r) ^ (-β - 1) := Real.rpow_nonneg (by linarith) _
    rw [hfp, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hβ, abs_of_nonneg hpos]
    calc β * (1 + r) ^ (-β - 1) ≤ β * 1 := by gcongr
      _ = β := mul_one β
  have hconv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbound
    (convex_Ici 0) (Set.mem_Ici.mpr hr₂) (Set.mem_Ici.mpr hr₁)
  simpa [hf, Real.norm_eq_abs] using hconv

/-- Helper: `|p·q·r| ≤ pb·qb·rb` from `|p|≤pb, |q|≤qb, |r|≤rb` (`qb,rb ≥ 0`). -/
private theorem abs_mul₃_le {p q r pb qb rb : ℝ}
    (hp : |p| ≤ pb) (hq : |q| ≤ qb) (hr : |r| ≤ rb) (hqb : 0 ≤ qb) :
    |p * q * r| ≤ pb * qb * rb := by
  rw [abs_mul, abs_mul]
  exact mul_le_mul (mul_le_mul hp hq (abs_nonneg _) (le_trans (abs_nonneg _) hp))
    hr (abs_nonneg _) (mul_nonneg (le_trans (abs_nonneg _) hp) hqb)

/-- **glue1 (value core) — flux-value Lipschitz.**  The chemotaxis flux value
`a·g·(1+v)^{−β}` (mass `a = u`, gradient `g = ∂ₓR`, signal `v = R ≥ 0`) is
Lipschitz in `(a,g,v)` on the bounded ball, with constant
`L_Q = B_G + M·L_G + M·B_G·β·L_R`.  Telescoping
`a₁g₁w₁−a₂g₂w₂ = (a₁−a₂)g₁w₁ + a₂(g₁−g₂)w₁ + a₂g₂(w₁−w₂)`, with `0 ≤ wᵢ ≤ 1`
(`vᵢ ≥ 0`) and `|w₁−w₂| ≤ β·L_R·d` (`oneAddRpow_neg_lipschitz`). -/
theorem chemFluxValue_lipschitz {β M B_G d L_G L_R : ℝ} (hβ : 0 ≤ β)
    {a₁ a₂ g₁ g₂ v₁ v₂ : ℝ}
    (ha₂ : |a₂| ≤ M) (hg₁ : |g₁| ≤ B_G) (hg₂ : |g₂| ≤ B_G)
    (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂)
    (had : |a₁ - a₂| ≤ d) (hgd : |g₁ - g₂| ≤ L_G * d) (hvd : |v₁ - v₂| ≤ L_R * d)
    (hBnn : 0 ≤ B_G) :
    |a₁ * g₁ * (1 + v₁) ^ (-β) - a₂ * g₂ * (1 + v₂) ^ (-β)|
      ≤ (B_G + M * L_G + M * B_G * β * L_R) * d := by
  set w₁ : ℝ := (1 + v₁) ^ (-β) with hw₁
  set w₂ : ℝ := (1 + v₂) ^ (-β) with hw₂
  have hw₁_nn : 0 ≤ w₁ := Real.rpow_nonneg (by linarith) _
  have hw₂_nn : 0 ≤ w₂ := Real.rpow_nonneg (by linarith) _
  have hw₁_le : w₁ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hwabs : |w₁| ≤ 1 := by rw [abs_of_nonneg hw₁_nn]; exact hw₁_le
  have hwd : |w₁ - w₂| ≤ β * (L_R * d) := by
    calc |w₁ - w₂| ≤ β * |v₁ - v₂| := oneAddRpow_neg_lipschitz hβ hv₁ hv₂
      _ ≤ β * (L_R * d) := mul_le_mul_of_nonneg_left hvd hβ
  have htel : a₁ * g₁ * w₁ - a₂ * g₂ * w₂
      = (a₁ - a₂) * g₁ * w₁ + a₂ * (g₁ - g₂) * w₁ + a₂ * g₂ * (w₁ - w₂) := by ring
  rw [htel]
  have hb1 : |(a₁ - a₂) * g₁ * w₁| ≤ d * B_G * 1 :=
    abs_mul₃_le had hg₁ hwabs hBnn
  have hb2 : |a₂ * (g₁ - g₂) * w₁| ≤ M * (L_G * d) * 1 :=
    abs_mul₃_le ha₂ hgd hwabs (le_trans (abs_nonneg _) hgd)
  have hb3 : |a₂ * g₂ * (w₁ - w₂)| ≤ M * B_G * (β * (L_R * d)) :=
    abs_mul₃_le ha₂ hg₂ hwd hBnn
  calc |(a₁ - a₂) * g₁ * w₁ + a₂ * (g₁ - g₂) * w₁ + a₂ * g₂ * (w₁ - w₂)|
      ≤ |(a₁ - a₂) * g₁ * w₁ + a₂ * (g₁ - g₂) * w₁| + |a₂ * g₂ * (w₁ - w₂)| :=
        abs_add_le _ _
    _ ≤ (|(a₁ - a₂) * g₁ * w₁| + |a₂ * (g₁ - g₂) * w₁|) + |a₂ * g₂ * (w₁ - w₂)| := by
        gcongr; exact abs_add_le _ _
    _ ≤ (d * B_G * 1 + M * (L_G * d) * 1) + M * B_G * (β * (L_R * d)) := by gcongr
    _ = (B_G + M * L_G + M * B_G * β * L_R) * d := by ring

/-- **glue1 — chemotaxis flux sup-Lipschitz (`/(1+v)^β` form).**  The actual flux
quotient `a·g/(1+v)^β` (`= a·g·(1+v)^{−β}` since `v ≥ 0`) is Lipschitz at every
point, directly from the value core.  This is the interface consumed by the
contraction (glue2 / Atom E): the caller supplies the pointwise resolver bounds
(`a = u` bounded, `g = ∂ₓR` bounded+Lipschitz via Atom B, `v = R ≥ 0` bounded+
Lipschitz via Atom B + O1). -/
theorem chemFlux_div_lipschitz {β M B_G d L_G L_R : ℝ} (hβ : 0 ≤ β)
    {a₁ a₂ g₁ g₂ v₁ v₂ : ℝ}
    (ha₂ : |a₂| ≤ M) (hg₁ : |g₁| ≤ B_G) (hg₂ : |g₂| ≤ B_G)
    (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂)
    (had : |a₁ - a₂| ≤ d) (hgd : |g₁ - g₂| ≤ L_G * d) (hvd : |v₁ - v₂| ≤ L_R * d)
    (hBnn : 0 ≤ B_G) :
    |a₁ * g₁ / (1 + v₁) ^ β - a₂ * g₂ / (1 + v₂) ^ β|
      ≤ (B_G + M * L_G + M * B_G * β * L_R) * d := by
  have hcv : ∀ {v : ℝ}, 0 ≤ v → (1 + v) ^ (-β) = ((1 + v) ^ β)⁻¹ := by
    intro v hv; rw [Real.rpow_neg (by linarith)]
  have heq : ∀ {a g v : ℝ}, 0 ≤ v → a * g / (1 + v) ^ β = a * g * (1 + v) ^ (-β) := by
    intro a g v hv; rw [hcv hv, div_eq_mul_inv]
  rw [heq hv₁, heq hv₂]
  exact chemFluxValue_lipschitz hβ ha₂ hg₁ hg₂ hv₁ hv₂ had hgd hvd hBnn

/-! ## glue2 — the small-time contraction constant -/

/-- **Small-time contraction.**  For `A, B ≥ 0` there is a `T > 0` with
`A·√T + B·T < 1` (explicitly `T = 1/(A+B+1)²`).  Applied with
`A = 2|χ₀|·C·C_Q`, `B = C_L` this is the "取 T 小" step that makes the weak mild
map `Φ` a contraction: `‖Φu−Φw‖ ≤ (A·√T + B·T)·‖u−w‖`. -/
theorem exists_small_contraction_time {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ T : ℝ, 0 < T ∧ A * Real.sqrt T + B * T < 1 := by
  set c : ℝ := A + B + 1 with hc
  have hcpos : 0 < c := by positivity
  refine ⟨1 / c ^ 2, by positivity, ?_⟩
  have hsqrt : Real.sqrt (1 / c ^ 2) = 1 / c := by
    rw [show (1:ℝ) / c ^ 2 = (1 / c) ^ 2 from by rw [div_pow, one_pow],
      Real.sqrt_sq (by positivity)]
  rw [hsqrt]
  have hkey : A * c + B < c ^ 2 := by rw [hc]; nlinarith [hA, hB, sq_nonneg (A + B)]
  have hform : A * (1 / c) + B * (1 / c ^ 2) = (A * c + B) / c ^ 2 := by
    field_simp
  rw [hform, div_lt_one (by positivity)]
  exact hkey

/-- **glue2 (pointwise contraction core).**  The weak mild-map difference at a
point, `Φu−Φw = −χ₀·G + V` with `G = ∫₀ᵗ∂ₓS(t−s)(Q(u)−Q(w))ds` and
`V = ∫₀ᵗS(t−s)(L(u)−L(w))ds`, is bounded by `(2|χ₀|·C·C_Q·√T + C_L·T)·d`, given
the gradient-Duhamel bound on `G` (Atom D + glue1: `|G| ≤ C·2√T·C_Q·d`) and the
value-Duhamel bound on `V` (Atom D + Atom C: `|V| ≤ T·C_L·d`), `d = ‖u−w‖_{T,∞}`. -/
theorem gradientDuhamel_contraction_pointwise {χ₀ Cgrad C_Q C_L T d G V : ℝ}
    (hG : |G| ≤ Cgrad * (2 * Real.sqrt T) * (C_Q * d))
    (hV : |V| ≤ T * (C_L * d)) :
    |(-χ₀) * G + V| ≤ (2 * |χ₀| * Cgrad * C_Q * Real.sqrt T + C_L * T) * d := by
  calc |(-χ₀) * G + V| ≤ |(-χ₀) * G| + |V| := abs_add_le _ _
    _ = |χ₀| * |G| + |V| := by rw [abs_mul, abs_neg]
    _ ≤ |χ₀| * (Cgrad * (2 * Real.sqrt T) * (C_Q * d)) + T * (C_L * d) := by gcongr
    _ = (2 * |χ₀| * Cgrad * C_Q * Real.sqrt T + C_L * T) * d := by ring

end ShenWork.IntervalChemFluxLipschitz
