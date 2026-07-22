import ShenWork.Paper1.WholeLineChiPosHalfLineSuccessor

/-!
# Parabolic Bernstein jet for the normalized positive-sensitivity equation

For `m = gamma = alpha = 1`, write `w = q_z` and

`f(q,V) = -chi*q*(V-q) + q*(1-q)`.

With drift `a = c-chi*V_z`, differentiating the equation gives

`L w = B w - chi*q*V_z`,

where `L = partial_t-partial_zz-a*partial_z` and

`B = 1-2q-2chi*(V-q)+chi*q`.

For the relative Bernstein quantity

`P = w^2 + lambda*(q-1)^2`,

the exact jet identity is

`L P = 2(B-lambda)w^2 - 2w_z^2 - 2chi*q*V_z*w
       + 2lambda*(q-1)f`.

In particular the drift `a`, hence the constant co-moving speed `c`, cancels
completely.  At an interior parabolic maximum, a band
`|q-1| <= E`, `|V-q| <= 2E`, `|V_z| <= E` gives `w^2 <= C(chi,E) E^2` after choosing
`lambda` above the zeroth-order coefficient.  This is a genuine time-dependent
`O(E)` gradient mechanism valid for bands with upper edge greater than one.

It does **not** produce the steady crest denominator
`c-chi*(B-A)`: the maximum-principle operator is Galilean invariant and has
already discarded `c`.  Moreover, applying this identity to
`WholeLineChiPosCoMovingRestartData` requires `partial_t q_z` and `q_zzz`;
the committed restart interface supplies only spatial `ContDiff ℝ 2`.  Thus a
difference-quotient/weak Bernstein theorem (or a positive-time `C^3` upgrade)
is the exact remaining analytic regularity bridge for this route.
-/

open Real

noncomputable section

namespace ShenWork.Paper1

def chiOneBernsteinReaction (chi q V : ℝ) : ℝ :=
  -chi * q * (V - q) + q * (1 - q)

def chiOneBernsteinCoefficient (chi q V : ℝ) : ℝ :=
  1 - 2 * q - 2 * chi * (V - q) + chi * q

/-- A convenient relative-Bernstein parameter on a band of half-width `E`. -/
def chiOneBernsteinLambda (chi E : ℝ) : ℝ :=
  1 + |chi - 1| + (|chi - 2| + 4 * chi) * E

def chiOneBernsteinGradientFactor (chi E : ℝ) : ℝ :=
  chi ^ 2 * (1 + E) ^ 2 +
    2 * chiOneBernsteinLambda chi E * (1 + E) * (2 * chi + 1)

/-- **Exact parabolic Bernstein operator identity.**  `a` occurs in the PDE
jets and in `L P`, but cancels from the result. -/
theorem chiOne_relativeBernstein_operator_identity
    {chi lambda q V vz w wz qzz wzz qt wt a Pt Pz Pzz : ℝ}
    (hqt : qt = qzz + a * w + chiOneBernsteinReaction chi q V)
    (hwt : wt = wzz + a * wz +
      chiOneBernsteinCoefficient chi q V * w - chi * q * vz)
    (hPt : Pt = 2 * w * wt + 2 * lambda * (q - 1) * qt)
    (hPz : Pz = 2 * w * wz + 2 * lambda * (q - 1) * w)
    (hPzz : Pzz = 2 * wz ^ 2 + 2 * w * wzz +
      2 * lambda * w ^ 2 + 2 * lambda * (q - 1) * qzz) :
    Pt - Pzz - a * Pz =
      2 * (chiOneBernsteinCoefficient chi q V - lambda) * w ^ 2 -
        2 * wz ^ 2 - 2 * chi * q * vz * w +
        2 * lambda * (q - 1) * chiOneBernsteinReaction chi q V := by
  rw [hPt, hPz, hPzz, hqt, hwt]
  ring

theorem chiOneBernsteinCoefficient_band_le
    {chi q V E : ℝ} (hchi : 0 ≤ chi) (hE : 0 ≤ E)
    (hq : |q - 1| ≤ E) (hV : |V - q| ≤ 2 * E) :
    chiOneBernsteinCoefficient chi q V ≤
      chi - 1 + (|chi - 2| + 4 * chi) * E := by
  have hqterm : (chi - 2) * (q - 1) ≤ |chi - 2| * E := by
    calc
      (chi - 2) * (q - 1) ≤ |(chi - 2) * (q - 1)| := le_abs_self _
      _ = |chi - 2| * |q - 1| := abs_mul _ _
      _ ≤ |chi - 2| * E :=
        mul_le_mul_of_nonneg_left hq (abs_nonneg _)
  have hVterm : -2 * chi * (V - q) ≤ 4 * chi * E := by
    calc
      -2 * chi * (V - q) ≤ |2 * chi * (V - q)| := by
        have := neg_le_abs (2 * chi * (V - q))
        nlinarith
      _ = 2 * chi * |V - q| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hchi]
        norm_num
      _ ≤ 2 * chi * (2 * E) :=
        mul_le_mul_of_nonneg_left hV (mul_nonneg (by norm_num) hchi)
      _ = 4 * chi * E := by ring
  have hrewrite :
      chiOneBernsteinCoefficient chi q V =
        chi - 1 + (chi - 2) * (q - 1) - 2 * chi * (V - q) := by
    unfold chiOneBernsteinCoefficient
    ring
  rw [hrewrite]
  nlinarith

theorem chiOneBernsteinReaction_band_abs_le
    {chi q V E : ℝ} (hchi : 0 ≤ chi) (hE : 0 ≤ E)
    (hq : |q - 1| ≤ E) (hqUpper : |q| ≤ 1 + E)
    (hV : |V - q| ≤ 2 * E) :
    |chiOneBernsteinReaction chi q V| ≤
      (1 + E) * (2 * chi + 1) * E := by
  have hinner : |-chi * (V - q) - (q - 1)| ≤ (2 * chi + 1) * E := by
    calc
      |-chi * (V - q) - (q - 1)| ≤
          |-chi * (V - q)| + |q - 1| := abs_sub _ _
      _ = chi * |V - q| + |q - 1| := by
        rw [abs_mul, abs_neg, abs_of_nonneg hchi]
      _ ≤ chi * (2 * E) + E :=
        add_le_add (mul_le_mul_of_nonneg_left hV hchi) hq
      _ = (2 * chi + 1) * E := by ring
  have hright : 0 ≤ (2 * chi + 1) * E :=
    mul_nonneg (by linarith) hE
  unfold chiOneBernsteinReaction
  rw [show -chi * q * (V - q) + q * (1 - q) =
      q * (-chi * (V - q) - (q - 1)) by ring]
  rw [abs_mul]
  exact (mul_le_mul hqUpper hinner (abs_nonneg _) (by linarith)).trans_eq (by ring)

theorem chiOneBernsteinLambda_pos
    {chi E : ℝ} (hchi : 0 ≤ chi) (hE : 0 ≤ E) :
    0 < chiOneBernsteinLambda chi E := by
  unfold chiOneBernsteinLambda
  have hcoef : 0 ≤ |chi - 2| + 4 * chi :=
    add_nonneg (abs_nonneg _) (mul_nonneg (by norm_num) hchi)
  positivity

theorem chiOneBernsteinCoefficient_add_one_le_lambda
    {chi q V E : ℝ} (hchi : 0 ≤ chi) (hE : 0 ≤ E)
    (hq : |q - 1| ≤ E) (hV : |V - q| ≤ 2 * E) :
    chiOneBernsteinCoefficient chi q V + 1 ≤
      chiOneBernsteinLambda chi E := by
  have hB := chiOneBernsteinCoefficient_band_le hchi hE hq hV
  unfold chiOneBernsteinLambda
  have hbase : chi - 1 ≤ |chi - 1| := le_abs_self _
  nlinarith

/-- Generic maximum-point closure of the Bernstein identity. -/
theorem relativeBernstein_gradient_sq_le_of_parabolic_max
    {chi lambda q B vz w wz delta f Q Z E F LP : ℝ}
    (hLP : 0 ≤ LP)
    (hid : LP = 2 * (B - lambda) * w ^ 2 - 2 * wz ^ 2 -
      2 * chi * q * vz * w + 2 * lambda * delta * f)
    (hlambda : 0 ≤ lambda) (hB : B + 1 ≤ lambda)
    (hQ : 0 ≤ Q) (hZ : 0 ≤ Z) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hq : |q| ≤ Q) (hvz : |vz| ≤ Z)
    (hdelta : |delta| ≤ E) (hf : |f| ≤ F) :
    w ^ 2 ≤ chi ^ 2 * Q ^ 2 * Z ^ 2 + 2 * lambda * E * F := by
  have hBterm : 2 * (B - lambda) * w ^ 2 ≤ -2 * w ^ 2 := by
    have hcoef : 2 * (B - lambda) ≤ -2 := by linarith
    exact mul_le_mul_of_nonneg_right hcoef (sq_nonneg w)
  have hwz : -2 * wz ^ 2 ≤ 0 := by nlinarith [sq_nonneg wz]
  have hcross : -2 * chi * q * vz * w ≤ w ^ 2 + (chi * q * vz) ^ 2 := by
    nlinarith [sq_nonneg (w + chi * q * vz)]
  have hq2 : q ^ 2 ≤ Q ^ 2 := by
    simpa [sq_abs] using (sq_le_sq₀ (abs_nonneg q) hQ).2 hq
  have hvz2 : vz ^ 2 ≤ Z ^ 2 := by
    simpa [sq_abs] using (sq_le_sq₀ (abs_nonneg vz) hZ).2 hvz
  have hcrossSq : (chi * q * vz) ^ 2 ≤ chi ^ 2 * Q ^ 2 * Z ^ 2 := by
    calc
      (chi * q * vz) ^ 2 = chi ^ 2 * q ^ 2 * vz ^ 2 := by ring
      _ ≤ chi ^ 2 * Q ^ 2 * vz ^ 2 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hq2 (sq_nonneg chi)) (sq_nonneg vz)
      _ ≤ chi ^ 2 * Q ^ 2 * Z ^ 2 := by
        exact mul_le_mul_of_nonneg_left hvz2
          (mul_nonneg (sq_nonneg chi) (sq_nonneg Q))
  have hdeltaf : delta * f ≤ E * F := by
    calc
      delta * f ≤ |delta * f| := le_abs_self _
      _ = |delta| * |f| := abs_mul _ _
      _ ≤ E * F := mul_le_mul hdelta hf (abs_nonneg _) hE
  have hremainder : 2 * lambda * delta * f ≤ 2 * lambda * E * F := by
    calc
      2 * lambda * delta * f = (2 * lambda) * (delta * f) := by ring
      _ ≤ (2 * lambda) * (E * F) :=
        mul_le_mul_of_nonneg_left hdeltaf
          (mul_nonneg (by norm_num) hlambda)
      _ = 2 * lambda * E * F := by ring
  rw [hid] at hLP
  nlinarith

/-- **Explicit relative-gradient estimate at an interior parabolic maximum.**
The right side is `C(chi,E) E^2`, hence the gradient is `O(E)` as a tight band
collapses, with no restriction `q <= 1`. -/
theorem chiOne_relativeBernstein_gradient_sq_at_parabolic_max
    {chi q V vz w wz LP E : ℝ}
    (hchi : 0 ≤ chi) (hE : 0 ≤ E)
    (hq : |q - 1| ≤ E) (hV : |V - q| ≤ 2 * E)
    (hvz : |vz| ≤ E)
    (hLP : 0 ≤ LP)
    (hid : LP =
      2 * (chiOneBernsteinCoefficient chi q V -
          chiOneBernsteinLambda chi E) * w ^ 2 -
        2 * wz ^ 2 - 2 * chi * q * vz * w +
        2 * chiOneBernsteinLambda chi E * (q - 1) *
          chiOneBernsteinReaction chi q V) :
    w ^ 2 ≤ chiOneBernsteinGradientFactor chi E * E ^ 2 := by
  have hqUpper : |q| ≤ 1 + E := by
    calc
      |q| = |(q - 1) + 1| := by ring_nf
      _ ≤ |q - 1| + |(1 : ℝ)| := abs_add_le _ _
      _ ≤ E + |(1 : ℝ)| := by norm_num; linarith
      _ = 1 + E := by ring
  have hF := chiOneBernsteinReaction_band_abs_le
    hchi hE hq hqUpper hV
  have hlambda := (chiOneBernsteinLambda_pos hchi hE).le
  have hB := chiOneBernsteinCoefficient_add_one_le_lambda hchi hE hq hV
  have hraw := relativeBernstein_gradient_sq_le_of_parabolic_max
    hLP hid hlambda hB (by linarith : 0 ≤ 1 + E) hE hE
    (mul_nonneg (by linarith : 0 ≤ 1 + E)
      (mul_nonneg (by linarith : 0 ≤ 2 * chi + 1) hE))
    hqUpper hvz hq (by simpa [mul_assoc] using hF)
  unfold chiOneBernsteinGradientFactor
  nlinarith

section AxiomAudit

#print axioms chiOne_relativeBernstein_operator_identity
#print axioms chiOneBernsteinCoefficient_band_le
#print axioms chiOneBernsteinReaction_band_abs_le
#print axioms relativeBernstein_gradient_sq_le_of_parabolic_max
#print axioms chiOne_relativeBernstein_gradient_sq_at_parabolic_max

end AxiomAudit

end ShenWork.Paper1
