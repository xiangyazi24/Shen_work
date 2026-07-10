import ShenWork.Paper2.IntervalPicardLimitRestartBdd
import ShenWork.Paper2.IntervalMildRegularityBootstrap
import ShenWork.PDE.IntervalSourceCoefficientTimeC1
import ShenWork.PDE.IntervalTimeSoftClamp

/-!
# B-form restart summability from a bounded patched source

The canonical Picard source need not be time-`C¹` at `t = 0`.  The bounded
source interface is sufficient for spatial smoothing: a constant coefficient
bound controls the initial part of the Duhamel integral, while the summable
positive-window envelope controls its terminal part.  This file records that
argument for an arbitrary coefficient family.
-/

open Set

noncomputable section

namespace ShenWork.Paper2.BFormBddRestart

open ShenWork.IntervalDuhamelClosedC2 (duhamelSpectralCoeff)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalPicardLimitRestartWeak
  (duhamelSpectralCoeff_general_split_on)
open ShenWork.IntervalPicardLimitRestartBdd
  (DuhamelSourceBddOn abs_duhamelSpectralCoeff_le_of_bound
   eigenvalue_mul_abs_duhamelSpectralCoeff_le_of_bound
   summable_abs_duhamelSpectralCoeff_bdd)
open ShenWork.IntervalTimeSoftClamp
  (φ φ_continuous φ_eq_id_on φ_mem_range)

/-! ## Endpoint-free local source -/

/-- Shift a source to the restart time `tau`, after applying a soft clamp in
absolute time.  The clamp is the identity on `[tau, d]` and takes every real
argument into `[c, d']`. -/
def softClampedShiftSource
    (a : Real -> Nat -> Real) (c tau d d' : Real) : Real -> Nat -> Real :=
  fun rho k => a (φ c tau d d' (tau + rho)) k

/-- Every mode of the soft-clamped shifted source is globally continuous. -/
theorem softClampedShiftSource_continuous
    {a : Real -> Nat -> Real} {T c tau d d' : Real}
    (src : DuhamelSourceBddOn a T)
    (hc : 0 <= c) (hctau : c < tau) (htaud : tau <= d)
    (hdd' : d < d') (hd'T : d' <= T) (k : Nat) :
    Continuous (fun rho => softClampedShiftSource a c tau d d' rho k) := by
  have hclamp : Continuous (fun rho : Real => φ c tau d d' (tau + rho)) :=
    φ_continuous.comp (continuous_const.add continuous_id)
  have hmaps : Set.MapsTo (fun rho : Real => φ c tau d d' (tau + rho))
      Set.univ (Set.Icc 0 T) := by
    intro rho _
    have hrange := φ_mem_range hctau htaud hdd' (tau + rho)
    exact ⟨hc.trans hrange.1, hrange.2.trans hd'T⟩
  exact (src.hcont k).comp_continuous hclamp (fun rho => hmaps (Set.mem_univ rho))

/-- A bounded source remains bounded after a positive-window soft clamp.  Its
single envelope at `c` controls the clamped source for every relative time. -/
noncomputable def DuhamelSourceBddOn.softClampShift
    {a : Real -> Nat -> Real} {T c tau d d' : Real}
    (src : DuhamelSourceBddOn a T)
    (hc : 0 < c) (hctau : c < tau) (htaud : tau <= d)
    (hdd' : d < d') (hd'T : d' <= T) :
    DuhamelSourceBddOn (softClampedShiftSource a c tau d d') (d - tau) where
  M := src.M
  hM_nonneg := src.hM_nonneg
  hM := by
    intro rho _hrho hRho k
    have hrange := φ_mem_range hctau htaud hdd' (tau + rho)
    exact src.hM _ (hc.le.trans hrange.1) (hrange.2.trans hd'T) k
  hcont := fun k =>
    (softClampedShiftSource_continuous src hc.le hctau htaud hdd' hd'T k).continuousOn
  env := fun _ => src.env c
  henv_summable := fun _ _ _ =>
    src.henv_summable c hc
      (hctau.le.trans (htaud.trans (hdd'.le.trans hd'T)))
  henv_bound := by
    intro _ _ rho _ _ k
    have hrange := φ_mem_range hctau htaud hdd' (tau + rho)
    exact src.henv_bound c hc _ hrange.1 (hrange.2.trans hd'T) k

/-- On the active relative-time interval, the soft-clamped source is exactly
the source shifted by `tau`. -/
theorem softClampedShiftSource_eq_of_mem
    {a : Real -> Nat -> Real} {c tau d d' rho : Real}
    (hctau : c < tau) (hdd' : d < d') (hrho : tau + rho ∈ Set.Icc tau d)
    (k : Nat) :
    softClampedShiftSource a c tau d d' rho k = a (tau + rho) k := by
  simp only [softClampedShiftSource]
  rw [φ_eq_id_on hctau hdd' hrho]

/-- The Duhamel coefficients have an eigenvalue-weighted summable tail at every
positive time.  No time derivative of the source is used. -/
theorem duhamelSpectralCoeff_eigenvalue_summable_bdd
    {a : Real -> Nat -> Real} {T t : Real}
    (src : DuhamelSourceBddOn a T) (ht : 0 < t) (htT : t <= T) :
    Summable (fun k : Nat =>
      unitIntervalCosineEigenvalue k * |duhamelSpectralCoeff a t k|) := by
  set t2 : Real := t / 2 with ht2def
  have ht2 : 0 < t2 := by rw [ht2def]; linarith
  have ht2t : t2 <= t := by rw [ht2def]; linarith
  have ht2T : t2 <= T := ht2t.trans htT
  have htt2 : 0 < t - t2 := by rw [ht2def]; linarith
  have hsplit : forall k,
      duhamelSpectralCoeff a t k =
        Real.exp (-(t - t2) * unitIntervalCosineEigenvalue k) *
            duhamelSpectralCoeff a t2 k +
          duhamelSpectralCoeff (fun s k => a (t2 + s) k) (t - t2) k :=
    fun k => duhamelSpectralCoeff_general_split_on
      (a := a) (T := T) src.hcont ht2.le ht2t htT k
  have hhead : forall k,
      |duhamelSpectralCoeff a t2 k| <= t2 * src.M :=
    fun k => abs_duhamelSpectralCoeff_le_of_bound ht2 k
      (fun s hs hst => src.hM s hs (hst.trans ht2T) k)
  have htail : forall k,
      unitIntervalCosineEigenvalue k *
          |duhamelSpectralCoeff (fun s k => a (t2 + s) k) (t - t2) k| <=
        src.env t2 k := by
    intro k
    refine eigenvalue_mul_abs_duhamelSpectralCoeff_le_of_bound htt2 k ?_ ?_
    · intro s hs hst
      exact src.henv_bound t2 ht2 (t2 + s) (by linarith) (by linarith) k
    · have hmaps : Set.MapsTo (fun s : Real => t2 + s)
          (Set.Icc 0 (t - t2)) (Set.Icc 0 T) := by
        intro s hs
        constructor
        · linarith [hs.1, ht2.le]
        · linarith [hs.2, htT]
      exact (src.hcont k).comp
        (continuous_const.add continuous_id).continuousOn hmaps
  have hlambda_nonneg : forall k, 0 <= unitIntervalCosineEigenvalue k := by
    intro k
    unfold unitIntervalCosineEigenvalue
    positivity
  refine Summable.of_nonneg_of_le
    (f := fun k =>
      (t2 * src.M) *
          (unitIntervalCosineEigenvalue k *
            Real.exp (-(t - t2) * unitIntervalCosineEigenvalue k)) +
        src.env t2 k)
    (fun k => mul_nonneg (hlambda_nonneg k) (abs_nonneg _))
    (fun k => ?_) ?_
  · rw [hsplit k]
    calc
      unitIntervalCosineEigenvalue k *
          |Real.exp (-(t - t2) * unitIntervalCosineEigenvalue k) *
                duhamelSpectralCoeff a t2 k +
              duhamelSpectralCoeff
                (fun s k => a (t2 + s) k) (t - t2) k|
          <= unitIntervalCosineEigenvalue k *
              (|Real.exp (-(t - t2) * unitIntervalCosineEigenvalue k) *
                  duhamelSpectralCoeff a t2 k| +
                |duhamelSpectralCoeff
                  (fun s k => a (t2 + s) k) (t - t2) k|) :=
            mul_le_mul_of_nonneg_left (abs_add_le _ _) (hlambda_nonneg k)
      _ = unitIntervalCosineEigenvalue k *
              |Real.exp (-(t - t2) * unitIntervalCosineEigenvalue k) *
                duhamelSpectralCoeff a t2 k| +
            unitIntervalCosineEigenvalue k *
              |duhamelSpectralCoeff
                (fun s k => a (t2 + s) k) (t - t2) k| := by ring
      _ <= (t2 * src.M) *
              (unitIntervalCosineEigenvalue k *
                Real.exp (-(t - t2) * unitIntervalCosineEigenvalue k)) +
            src.env t2 k := by
          apply add_le_add
          · rw [abs_mul, abs_of_pos (Real.exp_pos _)]
            calc
              unitIntervalCosineEigenvalue k *
                    (Real.exp (-(t - t2) * unitIntervalCosineEigenvalue k) *
                      |duhamelSpectralCoeff a t2 k|)
                  <= unitIntervalCosineEigenvalue k *
                    (Real.exp (-(t - t2) * unitIntervalCosineEigenvalue k) *
                      (t2 * src.M)) := by
                      apply mul_le_mul_of_nonneg_left _ (hlambda_nonneg k)
                      exact mul_le_mul_of_nonneg_left (hhead k)
                        (Real.exp_pos _).le
              _ = (t2 * src.M) *
                    (unitIntervalCosineEigenvalue k *
                      Real.exp (-(t - t2) * unitIntervalCosineEigenvalue k)) := by
                        ring
          · exact htail k
  · have hheat : Summable (fun k =>
        (t2 * src.M) *
          (unitIntervalCosineEigenvalue k *
            Real.exp (-(t - t2) * unitIntervalCosineEigenvalue k))) :=
      (ShenWork.IntervalMildRegularityBootstrap.unitIntervalCosineEigenvalue_mul_exp_summable
        htt2).mul_left
          (t2 * src.M)
    have henv : Summable (src.env t2) :=
      src.henv_summable t2 ht2 ht2T
    exact hheat.add henv

/-- Absolute summability of homogeneous-plus-Duhamel restart coefficients from
the bounded source package. -/
theorem localRestartCoeff_abs_summable_bdd
    {a0 : Nat -> Real} {a : Real -> Nat -> Real} {M0 T t : Real}
    (ha0 : forall k, |a0 k| <= M0)
    (src : DuhamelSourceBddOn a T) (ht : 0 < t) (htT : t <= T) :
    Summable (fun k : Nat => |localRestartCoeff a0 a t k|) := by
  have hhom : Summable (fun k : Nat =>
      |Real.exp (-t * unitIntervalCosineEigenvalue k) * a0 k|) := by
    refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
      ((ShenWork.IntervalSemigroupComposition.expEigSummable ht).mul_right M0)
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (ha0 k) (Real.exp_pos _).le
  have hduh := summable_abs_duhamelSpectralCoeff_bdd src ht htT
  refine (hhom.add hduh).of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
  unfold localRestartCoeff
  exact abs_add_le _ _

/-- Eigenvalue-weighted summability of homogeneous-plus-Duhamel restart
coefficients from the bounded source package. -/
theorem localRestartCoeff_eigenvalue_summable_bdd
    {a0 : Nat -> Real} {a : Real -> Nat -> Real} {M0 T t : Real}
    (ha0 : forall k, |a0 k| <= M0)
    (src : DuhamelSourceBddOn a T) (ht : 0 < t) (htT : t <= T) :
    Summable (fun k : Nat =>
      unitIntervalCosineEigenvalue k * |localRestartCoeff a0 a t k|) := by
  have hhom :=
    ShenWork.IntervalMildRegularityBootstrap.restartHomogeneousCoeff_eigenvalue_summable
      ht ha0
  have hduh := duhamelSpectralCoeff_eigenvalue_summable_bdd src ht htT
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (by unfold unitIntervalCosineEigenvalue; positivity)
      (abs_nonneg _))
    (fun k => ?_) (hhom.add hduh)
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left
    (by unfold localRestartCoeff; exact abs_add_le _ _)
    (by unfold unitIntervalCosineEigenvalue; positivity)

section AxiomAudit
#print axioms softClampedShiftSource_continuous
#print axioms DuhamelSourceBddOn.softClampShift
#print axioms softClampedShiftSource_eq_of_mem
#print axioms duhamelSpectralCoeff_eigenvalue_summable_bdd
#print axioms localRestartCoeff_abs_summable_bdd
#print axioms localRestartCoeff_eigenvalue_summable_bdd
end AxiomAudit

end ShenWork.Paper2.BFormBddRestart
