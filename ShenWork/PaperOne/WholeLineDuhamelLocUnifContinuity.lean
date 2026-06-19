import ShenWork.PaperOne.WholeLineMildMapConcreteContinuity
import ShenWork.Paper1.WaveRotheC1

open Filter Topology MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

/-!
Compact-open upgrade lemmas for whole-line Duhamel terms.

The analytic inputs are kept explicit:
* pointwise convergence of the Duhamel term, supplied by the fixed-time DCT
  bricks plus the time-integral DCT;
* a uniform derivative bound for the Duhamel images, supplied by the layer-1
  gradient bound for the value Duhamel term and by the next derivative/Hölder
  layer for the gradient Duhamel term.

The upgrade itself is the finite-grid `ε/3` lemma
`locallyUniform_of_pointwise_of_equiLipschitz`.
-/

/-- Value-form whole-line Duhamel term for a spatial source. -/
def wholeLineValueDuhamel (t : ℝ) (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ s in Set.Icc (0 : ℝ) t,
    ShenWork.PaperOne.wholeLineHeatOp (t - s) F x

/-- Gradient-form whole-line Duhamel term for a spatial source. -/
def wholeLineGradDuhamel (t : ℝ) (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ s in Set.Icc (0 : ℝ) t,
    ShenWork.PaperOne.wholeLineHeatGradOp (t - s) F x

private theorem abs_sub_le_of_deriv_abs_le
    {f : ℝ → ℝ} {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hdiff : Differentiable ℝ f) (hderiv : ∀ x, |deriv f x| ≤ Λ) :
    ∀ x y, |f x - f y| ≤ Λ * |x - y| := by
  intro x y
  have hLip := crossImplicitStep_lipschitz hΛ hdiff hderiv
  have hdist := hLip.dist_le_mul x y
  simpa [Real.dist_eq, Real.coe_toNNReal _ hΛ] using hdist

/--
Value Duhamel compact-open upgrade.

The hypotheses `hpointDCT`, `hduhamel_diff`, and `hduhamel_deriv_bound` are the
two analytic pieces used in the paper route: pointwise DCT convergence and the
uniform layer-1 gradient bound for the Duhamel images.
-/
theorem wholeLineValueDuhamel_locallyUniform_of_source_locallyUniform_of_uniform_bound
    {t M Λ : ℝ} {Rs : ℕ → ℝ → ℝ} {R : ℝ → ℝ}
    (hsource : LocallyUniformConverges Rs R)
    (hRs_bound : ∀ n y, |Rs n y| ≤ M)
    (hR_bound : ∀ y, |R y| ≤ M)
    (hΛ : 0 ≤ Λ)
    (hpointDCT :
      ∀ x,
        Tendsto (fun n : ℕ => wholeLineValueDuhamel t (Rs n) x)
          atTop (𝓝 (wholeLineValueDuhamel t R x)))
    (hduhamel_diff :
      ∀ n, Differentiable ℝ (fun x : ℝ => wholeLineValueDuhamel t (Rs n) x))
    (hduhamel_limit_diff :
      Differentiable ℝ (fun x : ℝ => wholeLineValueDuhamel t R x))
    (hduhamel_deriv_bound :
      ∀ n x, |deriv (fun z : ℝ => wholeLineValueDuhamel t (Rs n) z) x| ≤ Λ)
    (hduhamel_limit_deriv_bound :
      ∀ x, |deriv (fun z : ℝ => wholeLineValueDuhamel t R z) x| ≤ Λ) :
    LocallyUniformConverges
      (fun n x => wholeLineValueDuhamel t (Rs n) x)
      (fun x => wholeLineValueDuhamel t R x) := by
  have _hsource_pointwise :
      ∀ y, Tendsto (fun n : ℕ => Rs n y) atTop (𝓝 (R y)) :=
    fun y => hsource.tendsto_at y
  have _hM_nonneg : 0 ≤ M := le_trans (abs_nonneg (R 0)) (hR_bound 0)
  have _hRs_bound := hRs_bound
  refine locallyUniform_of_pointwise_of_equiLipschitz hΛ hpointDCT ?_ ?_
  · intro n
    exact abs_sub_le_of_deriv_abs_le hΛ
      (hduhamel_diff n) (hduhamel_deriv_bound n)
  · exact abs_sub_le_of_deriv_abs_le hΛ
      hduhamel_limit_diff hduhamel_limit_deriv_bound

/--
Gradient Duhamel compact-open upgrade.

Here the derivative bound is the equicontinuity input for the gradient-Duhamel
family, supplied analytically by the second-derivative/Hölder layer.
-/
theorem wholeLineGradDuhamel_locallyUniform_of_source_locallyUniform_of_uniform_bound
    {t M Λ : ℝ} {Rs : ℕ → ℝ → ℝ} {R : ℝ → ℝ}
    (hsource : LocallyUniformConverges Rs R)
    (hRs_bound : ∀ n y, |Rs n y| ≤ M)
    (hR_bound : ∀ y, |R y| ≤ M)
    (hΛ : 0 ≤ Λ)
    (hpointDCT :
      ∀ x,
        Tendsto (fun n : ℕ => wholeLineGradDuhamel t (Rs n) x)
          atTop (𝓝 (wholeLineGradDuhamel t R x)))
    (hduhamel_diff :
      ∀ n, Differentiable ℝ (fun x : ℝ => wholeLineGradDuhamel t (Rs n) x))
    (hduhamel_limit_diff :
      Differentiable ℝ (fun x : ℝ => wholeLineGradDuhamel t R x))
    (hduhamel_deriv_bound :
      ∀ n x, |deriv (fun z : ℝ => wholeLineGradDuhamel t (Rs n) z) x| ≤ Λ)
    (hduhamel_limit_deriv_bound :
      ∀ x, |deriv (fun z : ℝ => wholeLineGradDuhamel t R z) x| ≤ Λ) :
    LocallyUniformConverges
      (fun n x => wholeLineGradDuhamel t (Rs n) x)
      (fun x => wholeLineGradDuhamel t R x) := by
  have _hsource_pointwise :
      ∀ y, Tendsto (fun n : ℕ => Rs n y) atTop (𝓝 (R y)) :=
    fun y => hsource.tendsto_at y
  have _hM_nonneg : 0 ≤ M := le_trans (abs_nonneg (R 0)) (hR_bound 0)
  have _hRs_bound := hRs_bound
  refine locallyUniform_of_pointwise_of_equiLipschitz hΛ hpointDCT ?_ ?_
  · intro n
    exact abs_sub_le_of_deriv_abs_le hΛ
      (hduhamel_diff n) (hduhamel_deriv_bound n)
  · exact abs_sub_le_of_deriv_abs_le hΛ
      hduhamel_limit_diff hduhamel_limit_deriv_bound

#print axioms wholeLineValueDuhamel_locallyUniform_of_source_locallyUniform_of_uniform_bound
#print axioms wholeLineGradDuhamel_locallyUniform_of_source_locallyUniform_of_uniform_bound

end ShenWork.Paper1

