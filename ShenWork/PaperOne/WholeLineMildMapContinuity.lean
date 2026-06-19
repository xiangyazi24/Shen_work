import ShenWork.PaperOne.WholeLineSchauderFixedPoint

open Filter

namespace ShenWork.Paper1
noncomputable section

theorem LocallyUniformConverges.const (f : ℝ → ℝ) :
    LocallyUniformConverges (fun _ : ℕ => f) f := by
  intro R hR ε hε
  exact Filter.Eventually.of_forall fun _ x _ => by simpa using hε

theorem LocallyUniformConverges.add {fs gs : ℕ → ℝ → ℝ} {f g : ℝ → ℝ}
    (hf : LocallyUniformConverges fs f)
    (hg : LocallyUniformConverges gs g) :
    LocallyUniformConverges (fun n x => fs n x + gs n x) (fun x => f x + g x) := by
  intro R hR ε hε
  have hε2 : 0 < ε / 2 := by linarith
  filter_upwards [hf R hR (ε / 2) hε2, hg R hR (ε / 2) hε2] with n hn hm
  intro x hx
  calc
    |fs n x + gs n x - (f x + g x)|
        = |(fs n x - f x) + (gs n x - g x)| := by ring_nf
    _ ≤ |fs n x - f x| + |gs n x - g x| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hn x hx) (hm x hx)
    _ = ε := by ring

theorem LocallyUniformConverges.const_mul {fs : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (c : ℝ) (hf : LocallyUniformConverges fs f) :
    LocallyUniformConverges (fun n x => c * fs n x) (fun x => c * f x) := by
  by_cases hc : c = 0
  · simpa [hc] using LocallyUniformConverges.const (fun _ : ℝ => 0)
  intro R hR ε hε
  have hcpos : 0 < |c| := abs_pos.mpr hc
  have hδ : 0 < ε / |c| := div_pos hε hcpos
  filter_upwards [hf R hR (ε / |c|) hδ] with n hn
  intro x hx
  calc
    |c * fs n x - c * f x| = |c| * |fs n x - f x| := by
      rw [← mul_sub, abs_mul]
    _ < |c| * (ε / |c|) := mul_lt_mul_of_pos_left (hn x hx) hcpos
    _ = ε := by field_simp [ne_of_gt hcpos]

/--
Assembly lemma for the whole-line mild map.

The analytic work is exactly in `hchem` and `hlog`: these are the layer-2
resolvent/gradient continuity plus dominated-convergence statements for the
gradient and value Duhamel terms.  The first term is independent of `U`.
-/
theorem wholeLineMildMap_continuous_in_U
    {trap : (ℝ → ℝ) → Prop} {χ : ℝ}
    {wholeLineMildMap : (ℝ → ℝ) → ℝ → ℝ}
    {semigroupTerm : ℝ → ℝ}
    {chemDuhamel logisticDuhamel : (ℝ → ℝ) → ℝ → ℝ}
    (hdecomp : ∀ U x, wholeLineMildMap U x =
      semigroupTerm x + (-χ) * chemDuhamel U x + logisticDuhamel U x)
    (hchem : LocalUniformContinuousOn trap chemDuhamel)
    (hlog : LocalUniformContinuousOn trap logisticDuhamel) :
    LocalUniformContinuousOn trap wholeLineMildMap := by
  intro seq u hseq hu hseq_u
  have h0 : LocallyUniformConverges (fun _ : ℕ => semigroupTerm) semigroupTerm :=
    LocallyUniformConverges.const semigroupTerm
  have hchem' : LocallyUniformConverges
      (fun n x => (-χ) * chemDuhamel (seq n) x)
      (fun x => (-χ) * chemDuhamel u x) :=
    (hchem seq u hseq hu hseq_u).const_mul (-χ)
  have hlog' : LocallyUniformConverges
      (fun n => logisticDuhamel (seq n)) (logisticDuhamel u) :=
    hlog seq u hseq hu hseq_u
  have hsum : LocallyUniformConverges
      (fun n x => semigroupTerm x + (-χ) * chemDuhamel (seq n) x +
        logisticDuhamel (seq n) x)
      (fun x => semigroupTerm x + (-χ) * chemDuhamel u x +
        logisticDuhamel u x) :=
    (h0.add hchem').add hlog'
  intro R hR ε hε
  filter_upwards [hsum R hR ε hε] with n hn
  intro x hx
  rw [hdecomp (seq n) x, hdecomp u x]
  exact hn x hx

#print axioms wholeLineMildMap_continuous_in_U

end
end ShenWork.Paper1
