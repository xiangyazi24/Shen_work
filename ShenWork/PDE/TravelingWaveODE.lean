import Mathlib
import ShenWork.Defs

noncomputable section

open Set Filter Topology

namespace ShenWork
namespace PDE
namespace TravelingWaveODE

abbrev Idx : Type := Fin 4
abbrev State : Type := Idx → ℝ

structure Params where
c : ℝ
chi : ℝ
m : ℕ
alpha : ℕ
gamma : ℕ
hm : 0 < m
halpha : 0 < alpha
hgamma : 0 < gamma

def Params.toCMParams (p : Params) : CMParams where
  m := p.m
  α := p.alpha
  γ := p.gamma
  χ := p.chi
  hm := by exact_mod_cast Nat.succ_le_of_lt p.hm
  hα := by exact_mod_cast Nat.succ_le_of_lt p.halpha
  hγ := by exact_mod_cast Nat.succ_le_of_lt p.hgamma

def E1 : State := ![1, 0, 1, 0]
def E0 : State := ![0, 0, 0, 0]

def vectorField (p : Params) (x : State) : State :=
![
x 1,
-p.c * x 1
+ p.chi *
((p.m : ℝ) * (x 0) ^ (p.m - 1) * x 1 * x 3
+ (x 0) ^ p.m * (x 2 - (x 0) ^ p.gamma))
- x 0 * (1 - (x 0) ^ p.alpha),
x 3,
x 2 - (x 0) ^ p.gamma
]

def IsEquilibrium (p : Params) (x : State) : Prop :=
vectorField p x = 0

theorem IsEquilibrium.eq_zero {p : Params} {x : State} (h : IsEquilibrium p x) :
vectorField p x = 0 :=
h

@[simp]
theorem vectorField_E1 (p : Params) :
    vectorField p E1 = 0 := by
  funext i; fin_cases i <;> simp [vectorField, E1, one_pow] <;> ring

@[simp]
theorem vectorField_E0 (p : Params) :
    vectorField p E0 = 0 := by
  funext i; fin_cases i <;>
    simp [vectorField, E0, Nat.ne_of_gt p.hm, Nat.ne_of_gt p.hgamma, zero_pow] <;> ring

theorem E1_equilibrium (p : Params) :
IsEquilibrium p E1 := by
exact vectorField_E1 p

theorem E0_equilibrium (p : Params) :
IsEquilibrium p E0 := by
exact vectorField_E0 p

def powSlopeAtZero (n : ℕ) : ℝ :=
if n = 1 then 1 else 0

def jacobianAtOne (p : Params) : Matrix Idx Idx ℝ :=
!![
0, 1, 0, 0;
(p.alpha : ℝ) - p.chi * (p.gamma : ℝ), -p.c, p.chi, 0;
0, 0, 0, 1;
-(p.gamma : ℝ), 0, 1, 0
]

def jacobianAtZero (p : Params) : Matrix Idx Idx ℝ :=
!![
0, 1, 0, 0;
-1, -p.c, 0, 0;
0, 0, 0, 1;
-powSlopeAtZero p.gamma, 0, 1, 0
]

def matVec4 (A : Matrix Idx Idx ℝ) (x : State) : State :=
fun i =>
A i 0 * x 0
+ A i 1 * x 1
+ A i 2 * x 2
+ A i 3 * x 3

def jacobianAtOneLin (p : Params) (x : State) : State :=
![
x 1,
((p.alpha : ℝ) - p.chi * (p.gamma : ℝ)) * x 0
- p.c * x 1
+ p.chi * x 2,
x 3,
-(p.gamma : ℝ) * x 0 + x 2
]

def jacobianAtZeroLin (p : Params) (x : State) : State :=
![
x 1,
-x 0 - p.c * x 1,
x 3,
-powSlopeAtZero p.gamma * x 0 + x 2
]

@[simp]
theorem matVec4_jacobianAtOne (p : Params) (x : State) :
matVec4 (jacobianAtOne p) x = jacobianAtOneLin p x := by
ext i <;> fin_cases i <;>
simp [matVec4, jacobianAtOne, jacobianAtOneLin] <;>
ring

@[simp]
theorem matVec4_jacobianAtZero (p : Params) (x : State) :
matVec4 (jacobianAtZero p) x = jacobianAtZeroLin p x := by
ext i <;> fin_cases i <;>
simp [matVec4, jacobianAtZero, jacobianAtZeroLin] <;>
ring

@[simp]
theorem matVec4_zero (A : Matrix Idx Idx ℝ) :
    matVec4 A (0 : State) = 0 := by
  ext i
  simp [matVec4]

theorem matVec4_add (A : Matrix Idx Idx ℝ) (x y : State) :
    matVec4 A (x + y) = matVec4 A x + matVec4 A y := by
  ext i
  simp [matVec4]
  ring

theorem matVec4_smul (A : Matrix Idx Idx ℝ) (a : ℝ) (x : State) :
    matVec4 A (a • x) = a • matVec4 A x := by
  ext i
  simp [matVec4, Pi.smul_apply, smul_eq_mul]
  ring

theorem matVec4_contDiff (A : Matrix Idx Idx ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (matVec4 A) := by
  refine contDiff_pi.mpr fun i => ?_
  dsimp [matVec4]
  fun_prop

theorem vectorField_contDiffAt (p : Params) (x : State) :
    ContDiffAt ℝ 1 (vectorField p) x := by
  apply ContDiffAt.of_le _ le_top
  have hi : ∀ i : Idx, ContDiffAt ℝ ⊤ (fun x : State => x i) x :=
    fun i => (ContinuousLinearMap.proj i : (Idx → ℝ) →L[ℝ] ℝ).contDiff.contDiffAt
  have h0 := hi 0; have h1 := hi 1; have h2 := hi 2; have h3 := hi 3
  unfold vectorField
  refine contDiffAt_pi.mpr fun i => ?_
  fin_cases i <;> dsimp
  · exact h1
  · have hchem :
        ContDiffAt ℝ ⊤
          (fun x : State =>
            (p.m : ℝ) * x 0 ^ (p.m - 1) * x 1 * x 3
              + x 0 ^ p.m * (x 2 - x 0 ^ p.gamma)) x :=
      (((contDiffAt_const (c := (p.m : ℝ))).mul (h0.pow (p.m - 1))).mul h1 |>.mul h3).add
        ((h0.pow p.m).mul (h2.sub (h0.pow p.gamma)))
    have hrep :
        ContDiffAt ℝ ⊤
          (fun x : State =>
            p.chi *
              ((p.m : ℝ) * x 0 ^ (p.m - 1) * x 1 * x 3
                + x 0 ^ p.m * (x 2 - x 0 ^ p.gamma))) x :=
      (contDiffAt_const (c := p.chi)).mul hchem
    have hgrowth :
        ContDiffAt ℝ ⊤
          (fun x : State => x 0 * (1 - x 0 ^ p.alpha)) x :=
      h0.mul ((contDiffAt_const (c := (1 : ℝ))).sub (h0.pow p.alpha))
    simpa [neg_mul] using (((contDiffAt_const (c := p.c)).mul h1).neg.add hrep).sub hgrowth
  · exact h3
  · exact h2.sub (h0.pow p.gamma)

theorem vectorField_contDiff (p : Params) :
    ContDiff ℝ 1 (vectorField p) := by
  rw [contDiff_iff_contDiffAt]
  exact vectorField_contDiffAt p

theorem picardLindelofData (p : Params) (x₀ : State) :
∃ (eps : ℝ) (heps : 0 < eps) (a r L K : NNReal) (_ : 0 < r),
∀ t₀ : ℝ,
IsPicardLindelof
(fun _ : ℝ => vectorField p)
(⟨t₀, by constructor <;> linarith [heps]⟩ :
Set.Icc (t₀ - eps) (t₀ + eps))
x₀ a r L K := by
simpa using IsPicardLindelof.of_contDiffAt_one (vectorField_contDiffAt p x₀)

theorem localSolutionExists (p : Params) (x₀ : State) (t₀ : ℝ) :
    ∃ r > 0, ∃ eps > 0, ∀ x ∈ Metric.closedBall x₀ r,
    ∃ z : ℝ → State,
    z t₀ = x ∧ ∀ t ∈ Ioo (t₀ - eps) (t₀ + eps),
      HasDerivAt z (vectorField p (z t)) t := by
  obtain ⟨eps, heps, a, r, L, K, hr, hPL⟩ := picardLindelofData p x₀
  refine ⟨r, by exact_mod_cast hr, eps, heps, fun x hx => ?_⟩
  obtain ⟨α, hα⟩ := (hPL t₀).exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt
  refine ⟨α x, (hα x hx).1, fun t ht => ?_⟩
  exact ((hα x hx).2 t (Ioo_subset_Icc_self ht)).hasDerivAt
    (Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2]))

theorem localFlowExists (p : Params) (x₀ : State) (t₀ : ℝ) :
    ∃ r > 0, ∃ eps > 0, ∃ flow : State → ℝ → State,
    ∀ x ∈ Metric.closedBall x₀ r,
      flow x t₀ = x ∧
      ∀ t ∈ Ioo (t₀ - eps) (t₀ + eps),
        HasDerivAt (flow x) (vectorField p (flow x t)) t := by
  obtain ⟨eps, heps, a, r, L, K, hr, hPL⟩ := picardLindelofData p x₀
  refine ⟨r, by exact_mod_cast hr, eps, heps, ?_⟩
  obtain ⟨flow, hflow⟩ :=
    (hPL t₀).exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt
  refine ⟨flow, fun x hx => ?_⟩
  refine ⟨(hflow x hx).1, fun t ht => ?_⟩
  exact ((hflow x hx).2 t (Ioo_subset_Icc_self ht)).hasDerivAt
    (Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2]))

structure PhasePortrait (p : Params) where
source : State
target : State
source_eq : IsEquilibrium p source
target_eq : IsEquilibrium p target
sourceJacobian : Matrix Idx Idx ℝ
targetJacobian : Matrix Idx Idx ℝ

def phasePortrait (p : Params) : PhasePortrait p where
source := E1
target := E0
source_eq := E1_equilibrium p
target_eq := E0_equilibrium p
sourceJacobian := jacobianAtOne p
targetJacobian := jacobianAtZero p

def HasEigenpair (A : Matrix Idx Idx ℝ) (lam : ℝ) (v : State) : Prop :=
matVec4 A v = lam • v ∧ v ≠ 0

theorem HasEigenpair.eigen_eq
    {A : Matrix Idx Idx ℝ} {lam : ℝ} {v : State}
    (h : HasEigenpair A lam v) :
matVec4 A v = lam • v :=
h.1

theorem HasEigenpair.ne_zero
    {A : Matrix Idx Idx ℝ} {lam : ℝ} {v : State}
    (h : HasEigenpair A lam v) :
v ≠ 0 :=
h.2

def SolvesLinearized (A : Matrix Idx Idx ℝ) (y : ℝ → State) : Prop :=
  ∀ t : ℝ, HasDerivAt y (matVec4 A (y t)) t

theorem SolvesLinearized.hasDerivAt
    {A : Matrix Idx Idx ℝ} {y : ℝ → State} (h : SolvesLinearized A y) (t : ℝ) :
    HasDerivAt y (matVec4 A (y t)) t :=
  h t

theorem SolvesLinearized.differentiable
    {A : Matrix Idx Idx ℝ} {y : ℝ → State} (h : SolvesLinearized A y) :
    Differentiable ℝ y :=
  fun t => (h.hasDerivAt t).differentiableAt

theorem SolvesLinearized.deriv_eq_matVec
    {A : Matrix Idx Idx ℝ} {y : ℝ → State} (h : SolvesLinearized A y) :
    deriv y = fun t => matVec4 A (y t) := by
  funext t
  exact (h.hasDerivAt t).deriv

theorem SolvesLinearized.contDiff_one
    {A : Matrix Idx Idx ℝ} {y : ℝ → State} (h : SolvesLinearized A y) :
    ContDiff ℝ 1 y := by
  rw [contDiff_one_iff_deriv]
  refine ⟨h.differentiable, ?_⟩
  rw [h.deriv_eq_matVec]
  exact (matVec4_contDiff (A := A) (n := 1)).continuous.comp h.differentiable.continuous

theorem SolvesLinearized.contDiff_two
    {A : Matrix Idx Idx ℝ} {y : ℝ → State} (h : SolvesLinearized A y) :
    ContDiff ℝ 2 y := by
  rw [show (2 : WithTop ℕ∞) = (1 : WithTop ℕ∞) + 1 by norm_num,
    contDiff_succ_iff_deriv]
  refine ⟨h.differentiable, by simp, ?_⟩
  rw [h.deriv_eq_matVec]
  simpa [Function.comp_def] using
    (matVec4_contDiff (A := A) (n := 1)).comp h.contDiff_one

theorem SolvesLinearized.add
    {A : Matrix Idx Idx ℝ} {y₁ y₂ : ℝ → State}
    (h₁ : SolvesLinearized A y₁) (h₂ : SolvesLinearized A y₂) :
    SolvesLinearized A (fun t => y₁ t + y₂ t) := by
  intro t
  simpa [matVec4_add] using (h₁.hasDerivAt t).add (h₂.hasDerivAt t)

theorem SolvesLinearized.const_smul
    {A : Matrix Idx Idx ℝ} (a : ℝ) {y : ℝ → State}
    (h : SolvesLinearized A y) :
    SolvesLinearized A (fun t => a • y t) := by
  intro t
  simpa [matVec4_smul] using (h.hasDerivAt t).const_smul a

def linearMode (lam : ℝ) (v : State) : ℝ → State :=
  fun t => Real.exp (lam * t) • v

theorem linearMode_contDiff (lam : ℝ) (v : State) {n : WithTop ℕ∞} :
    ContDiff ℝ n (linearMode lam v) := by
  have hscalar : ContDiff ℝ n (fun t : ℝ => Real.exp (lam * t)) := by
    fun_prop
  simpa [linearMode] using hscalar.smul_const v

theorem linearMode_hasDerivAt
    {A : Matrix Idx Idx ℝ} {lam : ℝ} {v : State}
    (h : HasEigenpair A lam v) (t : ℝ) :
    HasDerivAt (linearMode lam v) (matVec4 A (linearMode lam v t)) t := by
  have hscalar : HasDerivAt (fun s : ℝ => Real.exp (lam * s))
      (Real.exp (lam * t) * lam) t := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Real.hasDerivAt_exp (lam * t)).comp t ((hasDerivAt_id t).const_mul lam)
  have hderiv : HasDerivAt (linearMode lam v)
      ((Real.exp (lam * t) * lam) • v) t := by
    simpa [linearMode] using hscalar.smul_const v
  have hA : matVec4 A (linearMode lam v t) = (Real.exp (lam * t) * lam) • v := by
    rw [linearMode, matVec4_smul, h.eigen_eq]
    ext i
    simp [Pi.smul_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
  simpa [hA] using hderiv

theorem HasEigenpair.linearMode_solves_linearized
    {A : Matrix Idx Idx ℝ} {lam : ℝ} {v : State}
    (h : HasEigenpair A lam v) :
    SolvesLinearized A (linearMode lam v) :=
  fun t => linearMode_hasDerivAt h t

theorem linearMode_tendsto_zero_atBot_of_pos
    {lam : ℝ} (hpos : 0 < lam) (v : State) :
    Tendsto (linearMode lam v) atBot (nhds 0) := by
  have hlin : Tendsto (fun t : ℝ => lam * t) atBot atBot :=
    tendsto_id.const_mul_atBot hpos
  have hscalar : Tendsto (fun t : ℝ => Real.exp (lam * t)) atBot (nhds 0) :=
    Real.tendsto_exp_atBot.comp hlin
  simpa [linearMode, zero_smul] using hscalar.smul_const v

theorem linearMode_tendsto_zero_atTop_of_neg
    {lam : ℝ} (hneg : lam < 0) (v : State) :
    Tendsto (linearMode lam v) atTop (nhds 0) := by
  have hlin : Tendsto (fun t : ℝ => lam * t) atTop atBot :=
    tendsto_id.const_mul_atTop_of_neg hneg
  have hscalar : Tendsto (fun t : ℝ => Real.exp (lam * t)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp hlin
  simpa [linearMode, zero_smul] using hscalar.smul_const v

def LinearUnstable (A : Matrix Idx Idx ℝ) : Prop :=
  ∃ lam : ℝ, 0 < lam ∧ ∃ v : State, HasEigenpair A lam v

theorem LinearUnstable.exists_positive_eigenpair
    {A : Matrix Idx Idx ℝ} (h : LinearUnstable A) :
    ∃ lam : ℝ, 0 < lam ∧ ∃ v : State, HasEigenpair A lam v :=
  h

def characteristicAtOne (p : Params) (lam : ℝ) : Prop :=
(lam ^ 2 + p.c * lam - (p.alpha : ℝ) + p.chi * (p.gamma : ℝ))
* (lam ^ 2 - 1)
+ p.chi * (p.gamma : ℝ) = 0

theorem characteristicAtOne.eq_zero
    {p : Params} {lam : ℝ} (h : characteristicAtOne p lam) :
    (lam ^ 2 + p.c * lam - (p.alpha : ℝ) + p.chi * (p.gamma : ℝ))
    * (lam ^ 2 - 1)
    + p.chi * (p.gamma : ℝ) = 0 :=
  h

def unstableVectorAtOne (p : Params) (lam : ℝ) : State :=
![
-(lam ^ 2 - 1),
lam * (-(lam ^ 2 - 1)),
(p.gamma : ℝ),
lam * (p.gamma : ℝ)
]

theorem unstableVectorAtOne_ne_zero (p : Params) (lam : ℝ) :
    unstableVectorAtOne p lam ≠ 0 := by
  intro h
  have h2 : (p.gamma : ℝ) = 0 := by
    simpa [unstableVectorAtOne] using congr_fun h (2 : Idx)
  have hg : (0 : ℝ) < (p.gamma : ℝ) := by exact_mod_cast p.hgamma
  linarith

theorem jacobianAtOne_unstableVector_eigen
    (p : Params) {lam : ℝ}
    (hchar : characteristicAtOne p lam) :
    matVec4 (jacobianAtOne p) (unstableVectorAtOne p lam)
    = lam • unstableVectorAtOne p lam := by
  unfold characteristicAtOne at hchar
  ext i; fin_cases i <;>
    simp [matVec4, jacobianAtOne, unstableVectorAtOne, Pi.smul_apply, smul_eq_mul] <;>
    (try ring) <;>
    linear_combination hchar

theorem jacobianAtOne_eigenpair_of_characteristic
(p : Params) {lam : ℝ}
(hchar : characteristicAtOne p lam) :
HasEigenpair (jacobianAtOne p) lam (unstableVectorAtOne p lam) := by
constructor
· exact jacobianAtOne_unstableVector_eigen p hchar
· exact unstableVectorAtOne_ne_zero p lam

theorem jacobianAtOne_linearUnstable_of_root
(p : Params) {lam : ℝ}
(hpos : 0 < lam)
(hchar : characteristicAtOne p lam) :
LinearUnstable (jacobianAtOne p) := by
refine ⟨lam, hpos, unstableVectorAtOne p lam, ?_⟩
exact jacobianAtOne_eigenpair_of_characteristic p hchar

def OneDimUnstableRoot (p : Params) : Prop :=
∃! lam : ℝ, 0 < lam ∧ characteristicAtOne p lam

theorem OneDimUnstableRoot.exists_unique
    {p : Params} (h : OneDimUnstableRoot p) :
∃! lam : ℝ, 0 < lam ∧ characteristicAtOne p lam :=
h

theorem jacobianAtOne_linearUnstable_of_oneDimRoot
(p : Params)
(hroot : OneDimUnstableRoot p) :
LinearUnstable (jacobianAtOne p) := by
rcases hroot with ⟨lam, hlam, _huniq⟩
exact jacobianAtOne_linearUnstable_of_root p hlam.1 hlam.2

def stableVectorAtZero : State :=
![0, 0, 1, -1]

theorem stableVectorAtZero_ne_zero :
    stableVectorAtZero ≠ 0 := by
  intro h
  have h2 : (1 : ℝ) = 0 := by
    simpa [stableVectorAtZero] using congr_fun h (2 : Idx)
  norm_num at h2

theorem jacobianAtZero_stable_eigenpair (p : Params) :
    HasEigenpair (jacobianAtZero p) (-1) stableVectorAtZero := by
  refine ⟨?_, stableVectorAtZero_ne_zero⟩
  ext i; fin_cases i <;>
    simp [matVec4, jacobianAtZero, stableVectorAtZero, powSlopeAtZero,
      Pi.smul_apply, smul_eq_mul]

theorem unstableLinearModeAtOne_solves_and_decays
    (p : Params) {lam : ℝ}
    (hpos : 0 < lam)
    (hchar : characteristicAtOne p lam) :
    SolvesLinearized (jacobianAtOne p) (linearMode lam (unstableVectorAtOne p lam)) ∧
    Tendsto (linearMode lam (unstableVectorAtOne p lam)) atBot (nhds 0) := by
  have heig : HasEigenpair (jacobianAtOne p) lam (unstableVectorAtOne p lam) :=
    jacobianAtOne_eigenpair_of_characteristic p hchar
  exact ⟨heig.linearMode_solves_linearized, linearMode_tendsto_zero_atBot_of_pos hpos _⟩

theorem stableLinearModeAtZero_solves_and_decays
    (p : Params) :
    SolvesLinearized (jacobianAtZero p) (linearMode (-1) stableVectorAtZero) ∧
    Tendsto (linearMode (-1) stableVectorAtZero) atTop (nhds 0) := by
  have heig : HasEigenpair (jacobianAtZero p) (-1) stableVectorAtZero :=
    jacobianAtZero_stable_eigenpair p
  exact ⟨heig.linearMode_solves_linearized,
    linearMode_tendsto_zero_atTop_of_neg (by norm_num) _⟩

def SolvesTWODE (p : Params) (z : ℝ → State) : Prop :=
∀ t : ℝ, HasDerivAt z (vectorField p (z t)) t

theorem SolvesTWODE.hasDerivAt
    {p : Params} {z : ℝ → State} (h : SolvesTWODE p z) (t : ℝ) :
    HasDerivAt z (vectorField p (z t)) t :=
  h t

theorem SolvesTWODE.shift
    {p : Params} {z : ℝ → State} (h : SolvesTWODE p z) (a : ℝ) :
    SolvesTWODE p (fun t => z (t + a)) := by
  intro t
  have hz : HasDerivAt z (vectorField p (z (t + a))) (id t + a) := by
    simpa using h.hasDerivAt (t + a)
  simpa using hz.scomp t ((hasDerivAt_id t).add_const a)

theorem SolvesTWODE.differentiable
    {p : Params} {z : ℝ → State} (h : SolvesTWODE p z) :
    Differentiable ℝ z :=
  fun t => (h.hasDerivAt t).differentiableAt

theorem SolvesTWODE.deriv_eq_vectorField
    {p : Params} {z : ℝ → State} (h : SolvesTWODE p z) :
    deriv z = fun t => vectorField p (z t) := by
  funext t
  exact (h.hasDerivAt t).deriv

theorem SolvesTWODE.contDiff_one
    {p : Params} {z : ℝ → State} (h : SolvesTWODE p z) :
    ContDiff ℝ 1 z := by
  rw [contDiff_one_iff_deriv]
  refine ⟨h.differentiable, ?_⟩
  rw [h.deriv_eq_vectorField]
  exact (vectorField_contDiff p).continuous.comp h.differentiable.continuous

theorem SolvesTWODE.contDiff_two
    {p : Params} {z : ℝ → State} (h : SolvesTWODE p z) :
    ContDiff ℝ 2 z := by
  rw [show (2 : WithTop ℕ∞) = (1 : WithTop ℕ∞) + 1 by norm_num,
    contDiff_succ_iff_deriv]
  refine ⟨h.differentiable, by simp, ?_⟩
  rw [h.deriv_eq_vectorField]
  simpa [Function.comp_def] using (vectorField_contDiff p).comp h.contDiff_one

theorem SolvesTWODE.component_contDiff_two
    {p : Params} {z : ℝ → State} (h : SolvesTWODE p z) (i : Idx) :
    ContDiff ℝ 2 (fun t => z t i) :=
  contDiff_pi.mp h.contDiff_two i

theorem SolvesTWODE.hasDerivAt_component
    {p : Params} {z : ℝ → State} (h : SolvesTWODE p z) (i : Idx) (t : ℝ) :
    HasDerivAt (fun s => z s i) ((vectorField p (z t)) i) t := by
  simpa only [ContinuousLinearMap.proj_apply] using
    ((ContinuousLinearMap.proj i : State →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t
      (h.hasDerivAt t))

theorem SolvesTWODE.deriv_component
    {p : Params} {z : ℝ → State} (h : SolvesTWODE p z) (i : Idx) (t : ℝ) :
    deriv (fun s => z s i) t = (vectorField p (z t)) i :=
  (h.hasDerivAt_component i t).deriv

theorem SolvesTWODE.hasDerivAt_U
    {p : Params} {z : ℝ → State} (h : SolvesTWODE p z) (t : ℝ) :
    HasDerivAt (fun s => z s 0) (z t 1) t := by
  simpa [vectorField] using h.hasDerivAt_component (0 : Idx) t

theorem SolvesTWODE.hasDerivAt_V
    {p : Params} {z : ℝ → State} (h : SolvesTWODE p z) (t : ℝ) :
    HasDerivAt (fun s => z s 2) (z t 3) t := by
  simpa [vectorField] using h.hasDerivAt_component (2 : Idx) t

theorem SolvesTWODE.hasDerivAt_deriv_U
    {p : Params} {z : ℝ → State} (h : SolvesTWODE p z) (t : ℝ) :
    HasDerivAt (deriv (fun s => z s 0))
      (-p.c * z t 1
        + p.chi *
          ((p.m : ℝ) * (z t 0) ^ (p.m - 1) * z t 1 * z t 3
            + (z t 0) ^ p.m * (z t 2 - (z t 0) ^ p.gamma))
        - z t 0 * (1 - (z t 0) ^ p.alpha)) t := by
  have hderiv : deriv (fun s => z s 0) = fun s => z s 1 := by
    funext s
    exact (h.hasDerivAt_U s).deriv
  rw [hderiv]
  simpa [vectorField] using h.hasDerivAt_component (1 : Idx) t

theorem SolvesTWODE.hasDerivAt_deriv_V
    {p : Params} {z : ℝ → State} (h : SolvesTWODE p z) (t : ℝ) :
    HasDerivAt (deriv (fun s => z s 2)) (z t 2 - (z t 0) ^ p.gamma) t := by
  have hderiv : deriv (fun s => z s 2) = fun s => z s 3 := by
    funext s
    exact (h.hasDerivAt_V s).deriv
  rw [hderiv]
  simpa [vectorField] using h.hasDerivAt_component (3 : Idx) t

theorem SolvesTWODE.profile_c2_bootstrap
    {p : Params} {z : ℝ → State} (h : SolvesTWODE p z) :
    ContDiff ℝ 2 (fun t => z t 0) ∧
    ContDiff ℝ 2 (fun t => z t 2) ∧
    (∀ t : ℝ,
      HasDerivAt (deriv (fun s => z s 0))
        (-p.c * z t 1
          + p.chi *
            ((p.m : ℝ) * (z t 0) ^ (p.m - 1) * z t 1 * z t 3
              + (z t 0) ^ p.m * (z t 2 - (z t 0) ^ p.gamma))
          - z t 0 * (1 - (z t 0) ^ p.alpha)) t) ∧
    (∀ t : ℝ, HasDerivAt (deriv (fun s => z s 2))
      (z t 2 - (z t 0) ^ p.gamma) t) := by
  exact ⟨h.component_contDiff_two 0, h.component_contDiff_two 2,
    h.hasDerivAt_deriv_U, h.hasDerivAt_deriv_V⟩

theorem SolvesTWODE.chemotaxis_deriv
    {p : Params} {z : ℝ → State} (h : SolvesTWODE p z) (t : ℝ) :
    deriv (fun y => (z y 0) ^ p.m * deriv (fun s => z s 2) y) t =
      (p.m : ℝ) * (z t 0) ^ (p.m - 1) * z t 1 * z t 3
        + (z t 0) ^ p.m * (z t 2 - (z t 0) ^ p.gamma) := by
  have hpow :
      HasDerivAt (fun y => (z y 0) ^ p.m)
        ((p.m : ℝ) * (z t 0) ^ (p.m - 1) * z t 1) t := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (h.hasDerivAt_U t).pow p.m
  have hV' : deriv (fun s => z s 2) t = z t 3 :=
    (h.hasDerivAt_V t).deriv
  simpa [hV', mul_assoc, mul_left_comm, mul_comm] using
    (hpow.mul (h.hasDerivAt_deriv_V t)).deriv

theorem SolvesTWODE.profile_U_equation
    {p : Params} {z : ℝ → State} (h : SolvesTWODE p z) (t : ℝ) :
    iteratedDeriv 2 (fun s => z s 0) t
      + p.c * deriv (fun s => z s 0) t
      - p.chi * deriv (fun y => (z y 0) ^ p.m * deriv (fun s => z s 2) y) t
      + z t 0 * (1 - (z t 0) ^ p.alpha) = 0 := by
  have hU' : deriv (fun s => z s 0) t = z t 1 :=
    (h.hasDerivAt_U t).deriv
  have hU'' :
      iteratedDeriv 2 (fun s => z s 0) t =
        -p.c * z t 1
          + p.chi *
            ((p.m : ℝ) * (z t 0) ^ (p.m - 1) * z t 1 * z t 3
              + (z t 0) ^ p.m * (z t 2 - (z t 0) ^ p.gamma))
          - z t 0 * (1 - (z t 0) ^ p.alpha) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    exact (h.hasDerivAt_deriv_U t).deriv
  rw [hU'', hU', h.chemotaxis_deriv t]
  ring

theorem SolvesTWODE.profile_V_equation
    {p : Params} {z : ℝ → State} (h : SolvesTWODE p z) (t : ℝ) :
    iteratedDeriv 2 (fun s => z s 2) t - z t 2 + (z t 0) ^ p.gamma = 0 := by
  have hV'' :
      iteratedDeriv 2 (fun s => z s 2) t =
        z t 2 - (z t 0) ^ p.gamma := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    exact (h.hasDerivAt_deriv_V t).deriv
  rw [hV'']
  ring

theorem SolvesTWODE.profile_equations
    {p : Params} {z : ℝ → State} (h : SolvesTWODE p z) :
    (∀ t : ℝ,
      iteratedDeriv 2 (fun s => z s 0) t
        + p.c * deriv (fun s => z s 0) t
        - p.chi * deriv (fun y => (z y 0) ^ p.m * deriv (fun s => z s 2) y) t
        + z t 0 * (1 - (z t 0) ^ p.alpha) = 0) ∧
    (∀ t : ℝ,
      iteratedDeriv 2 (fun s => z s 2) t - z t 2 + (z t 0) ^ p.gamma = 0) :=
  ⟨h.profile_U_equation, h.profile_V_equation⟩

structure TravelingWave (p : Params) where
z : ℝ → State
ode : SolvesTWODE p z
leftLimit : Tendsto z atBot (nhds E1)
rightLimit : Tendsto z atTop (nhds E0)

def TravelingWave.shift {p : Params} (w : TravelingWave p) (a : ℝ) :
    TravelingWave p :=
  { z := fun t => w.z (t + a)
    ode := w.ode.shift a
    leftLimit := w.leftLimit.comp (tendsto_atBot_add_const_right atBot a tendsto_id)
    rightLimit := w.rightLimit.comp (tendsto_atTop_add_const_right atTop a tendsto_id) }

theorem TravelingWave.profile_c2_bootstrap
    {p : Params} (w : TravelingWave p) :
    ContDiff ℝ 2 (fun t => w.z t 0) ∧
    ContDiff ℝ 2 (fun t => w.z t 2) ∧
    (∀ t : ℝ,
      HasDerivAt (deriv (fun s => w.z s 0))
        (-p.c * w.z t 1
          + p.chi *
            ((p.m : ℝ) * (w.z t 0) ^ (p.m - 1) * w.z t 1 * w.z t 3
              + (w.z t 0) ^ p.m * (w.z t 2 - (w.z t 0) ^ p.gamma))
          - w.z t 0 * (1 - (w.z t 0) ^ p.alpha)) t) ∧
    (∀ t : ℝ, HasDerivAt (deriv (fun s => w.z s 2))
      (w.z t 2 - (w.z t 0) ^ p.gamma) t) :=
  w.ode.profile_c2_bootstrap

theorem TravelingWave.profile_equations
    {p : Params} (w : TravelingWave p) :
    (∀ t : ℝ,
      iteratedDeriv 2 (fun s => w.z s 0) t
        + p.c * deriv (fun s => w.z s 0) t
        - p.chi * deriv
            (fun y => (w.z y 0) ^ p.m * deriv (fun s => w.z s 2) y) t
        + w.z t 0 * (1 - (w.z t 0) ^ p.alpha) = 0) ∧
    (∀ t : ℝ,
      iteratedDeriv 2 (fun s => w.z s 2) t - w.z t 2
        + (w.z t 0) ^ p.gamma = 0) :=
  w.ode.profile_equations

theorem TravelingWave.profile_U_equation
    {p : Params} (w : TravelingWave p) (t : ℝ) :
    iteratedDeriv 2 (fun s => w.z s 0) t
      + p.c * deriv (fun s => w.z s 0) t
      - p.chi * deriv
          (fun y => (w.z y 0) ^ p.m * deriv (fun s => w.z s 2) y) t
      + w.z t 0 * (1 - (w.z t 0) ^ p.alpha) = 0 :=
  w.ode.profile_U_equation t

theorem TravelingWave.profile_V_equation
    {p : Params} (w : TravelingWave p) (t : ℝ) :
    iteratedDeriv 2 (fun s => w.z s 2) t - w.z t 2
      + (w.z t 0) ^ p.gamma = 0 :=
  w.ode.profile_V_equation t

theorem TravelingWave.component_tendsto_atBot
    {p : Params} (w : TravelingWave p) (i : Idx) :
    Tendsto (fun t => w.z t i) atBot (nhds (E1 i)) := by
  simpa using
    ((ContinuousLinearMap.proj i : State →L[ℝ] ℝ).continuous.tendsto E1).comp
      w.leftLimit

theorem TravelingWave.component_tendsto_atTop
    {p : Params} (w : TravelingWave p) (i : Idx) :
    Tendsto (fun t => w.z t i) atTop (nhds (E0 i)) := by
  simpa using
    ((ContinuousLinearMap.proj i : State →L[ℝ] ℝ).continuous.tendsto E0).comp
      w.rightLimit

theorem TravelingWave.U_tendsto_atBot
    {p : Params} (w : TravelingWave p) :
    Tendsto (fun t => w.z t 0) atBot (nhds 1) := by
  simpa [E1] using w.component_tendsto_atBot (0 : Idx)

theorem TravelingWave.U_tendsto_atTop
    {p : Params} (w : TravelingWave p) :
    Tendsto (fun t => w.z t 0) atTop (nhds 0) := by
  simpa [E0] using w.component_tendsto_atTop (0 : Idx)

theorem TravelingWave.V_tendsto_atBot
    {p : Params} (w : TravelingWave p) :
    Tendsto (fun t => w.z t 2) atBot (nhds 1) := by
  simpa [E1] using w.component_tendsto_atBot (2 : Idx)

theorem TravelingWave.V_tendsto_atTop
    {p : Params} (w : TravelingWave p) :
    Tendsto (fun t => w.z t 2) atTop (nhds 0) := by
  simpa [E0] using w.component_tendsto_atTop (2 : Idx)

theorem TravelingWave.deriv_U_tendsto_atBot
    {p : Params} (w : TravelingWave p) :
    Tendsto (deriv (fun t => w.z t 0)) atBot (nhds 0) := by
  have hderiv : deriv (fun t => w.z t 0) = fun t => w.z t 1 := by
    funext t
    exact (w.ode.hasDerivAt_U t).deriv
  simpa [hderiv, E1] using w.component_tendsto_atBot (1 : Idx)

theorem TravelingWave.deriv_U_tendsto_atTop
    {p : Params} (w : TravelingWave p) :
    Tendsto (deriv (fun t => w.z t 0)) atTop (nhds 0) := by
  have hderiv : deriv (fun t => w.z t 0) = fun t => w.z t 1 := by
    funext t
    exact (w.ode.hasDerivAt_U t).deriv
  simpa [hderiv, E0] using w.component_tendsto_atTop (1 : Idx)

theorem TravelingWave.deriv_V_tendsto_atBot
    {p : Params} (w : TravelingWave p) :
    Tendsto (deriv (fun t => w.z t 2)) atBot (nhds 0) := by
  have hderiv : deriv (fun t => w.z t 2) = fun t => w.z t 3 := by
    funext t
    exact (w.ode.hasDerivAt_V t).deriv
  simpa [hderiv, E1] using w.component_tendsto_atBot (3 : Idx)

theorem TravelingWave.deriv_V_tendsto_atTop
    {p : Params} (w : TravelingWave p) :
    Tendsto (deriv (fun t => w.z t 2)) atTop (nhds 0) := by
  have hderiv : deriv (fun t => w.z t 2) = fun t => w.z t 3 := by
    funext t
    exact (w.ode.hasDerivAt_V t).deriv
  simpa [hderiv, E0] using w.component_tendsto_atTop (3 : Idx)

theorem TravelingWave.U_strictlyPositiveAtLeft
    {p : Params} (w : TravelingWave p) :
    ∃ δ > 0, ∀ᶠ t in atBot, δ ≤ w.z t 0 := by
  refine ⟨1 / 2, by norm_num, ?_⟩
  have hnhds : Set.Ioi (1 / 2 : ℝ) ∈ nhds (1 : ℝ) :=
    Ioi_mem_nhds (by norm_num)
  filter_upwards [w.U_tendsto_atBot hnhds] with t ht
  exact le_of_lt ht

theorem TravelingWave.profile_boundary_limits
    {p : Params} (w : TravelingWave p) :
    Tendsto (fun t => w.z t 0) atBot (nhds 1) ∧
    Tendsto (fun t => w.z t 0) atTop (nhds 0) ∧
    Tendsto (fun t => w.z t 2) atBot (nhds 1) ∧
    Tendsto (fun t => w.z t 2) atTop (nhds 0) ∧
    Tendsto (deriv (fun t => w.z t 0)) atBot (nhds 0) ∧
    Tendsto (deriv (fun t => w.z t 0)) atTop (nhds 0) ∧
    Tendsto (deriv (fun t => w.z t 2)) atBot (nhds 0) ∧
    Tendsto (deriv (fun t => w.z t 2)) atTop (nhds 0) :=
  ⟨w.U_tendsto_atBot, w.U_tendsto_atTop,
    w.V_tendsto_atBot, w.V_tendsto_atTop,
    w.deriv_U_tendsto_atBot, w.deriv_U_tendsto_atTop,
    w.deriv_V_tendsto_atBot, w.deriv_V_tendsto_atTop⟩

structure WaveProfileData (p : Params) (U V : ℝ → ℝ) : Prop where
  U_c2 : ContDiff ℝ 2 U
  V_c2 : ContDiff ℝ 2 V
  ode_U : ∀ t : ℝ,
    iteratedDeriv 2 U t
      + p.c * deriv U t
      - p.chi * deriv (fun y => (U y) ^ p.m * deriv V y) t
      + U t * (1 - (U t) ^ p.alpha) = 0
  ode_V : ∀ t : ℝ,
    iteratedDeriv 2 V t - V t + (U t) ^ p.gamma = 0
  lim_neg_inf : Tendsto U atBot (nhds 1) ∧ Tendsto V atBot (nhds 1)
  lim_pos_inf : Tendsto U atTop (nhds 0) ∧ Tendsto V atTop (nhds 0)
  deriv_lim_neg_inf :
    Tendsto (deriv U) atBot (nhds 0) ∧ Tendsto (deriv V) atBot (nhds 0)
  deriv_lim_pos_inf :
    Tendsto (deriv U) atTop (nhds 0) ∧ Tendsto (deriv V) atTop (nhds 0)
  U_strictlyPositiveAtLeft : ∃ δ > 0, ∀ᶠ t in atBot, δ ≤ U t

theorem TravelingWave.to_profileData
    {p : Params} (w : TravelingWave p) :
    WaveProfileData p (fun t => w.z t 0) (fun t => w.z t 2) := by
  exact
    { U_c2 := w.profile_c2_bootstrap.1
      V_c2 := w.profile_c2_bootstrap.2.1
      ode_U := w.profile_U_equation
      ode_V := w.profile_V_equation
      lim_neg_inf := ⟨w.U_tendsto_atBot, w.V_tendsto_atBot⟩
      lim_pos_inf := ⟨w.U_tendsto_atTop, w.V_tendsto_atTop⟩
      deriv_lim_neg_inf := ⟨w.deriv_U_tendsto_atBot, w.deriv_V_tendsto_atBot⟩
      deriv_lim_pos_inf := ⟨w.deriv_U_tendsto_atTop, w.deriv_V_tendsto_atTop⟩
      U_strictlyPositiveAtLeft := w.U_strictlyPositiveAtLeft }

theorem WaveProfileData.shift
    {p : Params} {U V : ℝ → ℝ} (h : WaveProfileData p U V) (a : ℝ) :
    WaveProfileData p (fun x => U (x + a)) (fun x => V (x + a)) := by
  have hUderiv : deriv (fun x => U (x + a)) = fun x => deriv U (x + a) := by
    funext x
    exact deriv_comp_add_const U a x
  have hVderiv : deriv (fun x => V (x + a)) = fun x => deriv V (x + a) := by
    funext x
    exact deriv_comp_add_const V a x
  refine
    { U_c2 := h.U_c2.comp (by fun_prop : ContDiff ℝ 2 (fun x : ℝ => x + a))
      V_c2 := h.V_c2.comp (by fun_prop : ContDiff ℝ 2 (fun x : ℝ => x + a))
      ode_U := ?_
      ode_V := ?_
      lim_neg_inf := ?_
      lim_pos_inf := ?_
      deriv_lim_neg_inf := ?_
      deriv_lim_pos_inf := ?_
      U_strictlyPositiveAtLeft := ?_ }
  · intro x
    have hU2 := congr_fun (iteratedDeriv_comp_add_const 2 U a) x
    have hU1 := deriv_comp_add_const U a x
    have hV1 : ∀ y,
        deriv (fun z => V (z + a)) y = deriv V (y + a) := by
      intro y
      exact deriv_comp_add_const V a y
    have hChem :
        deriv
          (fun y => (U (y + a)) ^ p.m *
            deriv (fun z => V (z + a)) y) x =
        deriv (fun ξ => (U ξ) ^ p.m * deriv V ξ) (x + a) := by
      have hfun :
          (fun y => (U (y + a)) ^ p.m *
            deriv (fun z => V (z + a)) y) =
          (fun y => (U (y + a)) ^ p.m * deriv V (y + a)) := by
        ext y
        rw [hV1 y]
      rw [hfun]
      have := congr_fun
        (iteratedDeriv_comp_add_const 1
          (fun ξ => (U ξ) ^ p.m * deriv V ξ) a) x
      simpa [iteratedDeriv_one] using this
    rw [hU2, hU1, hChem]
    exact h.ode_U (x + a)
  · intro x
    have hV2 := congr_fun (iteratedDeriv_comp_add_const 2 V a) x
    rw [hV2]
    exact h.ode_V (x + a)
  · exact
      ⟨h.lim_neg_inf.1.comp
          (tendsto_atBot_add_const_right atBot a tendsto_id),
        h.lim_neg_inf.2.comp
          (tendsto_atBot_add_const_right atBot a tendsto_id)⟩
  · exact
      ⟨h.lim_pos_inf.1.comp
          (tendsto_atTop_add_const_right atTop a tendsto_id),
        h.lim_pos_inf.2.comp
          (tendsto_atTop_add_const_right atTop a tendsto_id)⟩
  · exact
      ⟨by simpa [hUderiv, Function.comp_def] using
          h.deriv_lim_neg_inf.1.comp
            (tendsto_atBot_add_const_right atBot a tendsto_id),
        by simpa [hVderiv, Function.comp_def] using
          h.deriv_lim_neg_inf.2.comp
            (tendsto_atBot_add_const_right atBot a tendsto_id)⟩
  · exact
      ⟨by simpa [hUderiv, Function.comp_def] using
          h.deriv_lim_pos_inf.1.comp
            (tendsto_atTop_add_const_right atTop a tendsto_id),
        by simpa [hVderiv, Function.comp_def] using
          h.deriv_lim_pos_inf.2.comp
            (tendsto_atTop_add_const_right atTop a tendsto_id)⟩
  · rcases h.U_strictlyPositiveAtLeft with ⟨δ, hδ, hδle⟩
    exact ⟨δ, hδ,
      (tendsto_atBot_add_const_right atBot a tendsto_id).eventually hδle⟩

theorem WaveProfileData.to_isTravelingWave
    {p : Params} {U V : ℝ → ℝ} (h : WaveProfileData p U V)
    (hc : 0 < p.c) (hpos : ∀ x, 0 < U x) :
    IsTravelingWave p.toCMParams p.c U V := by
  refine
    { hc := hc
      U_pos := hpos
      ode_U := ?_
      ode_V := ?_
      lim_neg_inf := h.lim_neg_inf
      lim_pos_inf := h.lim_pos_inf }
  · intro x
    have hchem :
        (fun y => (U y) ^ p.toCMParams.m * deriv V y) =
        (fun y => (U y) ^ p.m * deriv V y) := by
      ext y
      simp [Params.toCMParams, Real.rpow_natCast]
    simpa [Params.toCMParams, hchem, Real.rpow_natCast] using h.ode_U x
  · intro x
    simpa [Params.toCMParams, Real.rpow_natCast] using h.ode_V x

theorem TravelingWave.to_isTravelingWave
    {p : Params} (w : TravelingWave p)
    (hc : 0 < p.c) (hpos : ∀ x, 0 < w.z x 0) :
    IsTravelingWave p.toCMParams p.c (fun x => w.z x 0) (fun x => w.z x 2) :=
  w.to_profileData.to_isTravelingWave hc hpos

theorem local_shooting_segment_from_E1_positive_eigenpair
    (p : Params) {lam δ t₀ : ℝ}
    (hpos : 0 < lam)
    (hchar : characteristicAtOne p lam) :
    ∃ v : State,
      0 < lam ∧
      HasEigenpair (jacobianAtOne p) lam v ∧
      ∃ r > 0, ∃ eps > 0,
        (E1 + δ • v ∈ Metric.closedBall E1 r →
          ∃ z : ℝ → State,
            z t₀ = E1 + δ • v ∧
            ∀ t ∈ Ioo (t₀ - eps) (t₀ + eps),
              HasDerivAt z (vectorField p (z t)) t) := by
  let v : State := unstableVectorAtOne p lam
  have hv : HasEigenpair (jacobianAtOne p) lam v := by
    simpa [v] using jacobianAtOne_eigenpair_of_characteristic p hchar
  obtain ⟨r, hr, eps, heps, hloc⟩ := localSolutionExists p E1 t₀
  refine ⟨v, hpos, hv, r, hr, eps, heps, ?_⟩
  intro hnear
  exact hloc (E1 + δ • v) hnear

theorem local_shooting_segment_from_E1_oneDimRoot
    (p : Params) (hroot : OneDimUnstableRoot p) {δ t₀ : ℝ} :
    ∃ lam : ℝ,
      0 < lam ∧
      characteristicAtOne p lam ∧
      ∃ v : State,
        HasEigenpair (jacobianAtOne p) lam v ∧
        ∃ r > 0, ∃ eps > 0,
          (E1 + δ • v ∈ Metric.closedBall E1 r →
            ∃ z : ℝ → State,
              z t₀ = E1 + δ • v ∧
              ∀ t ∈ Ioo (t₀ - eps) (t₀ + eps),
                HasDerivAt z (vectorField p (z t)) t) := by
  rcases hroot with ⟨lam, ⟨hpos, hchar⟩, _huniq⟩
  obtain ⟨v, _hpos, hv, r, hr, eps, heps, hseg⟩ :=
    local_shooting_segment_from_E1_positive_eigenpair
      (p := p) (lam := lam) (δ := δ) (t₀ := t₀) hpos hchar
  exact ⟨lam, hpos, hchar, v, hv, r, hr, eps, heps, hseg⟩

theorem local_shooting_segment_from_E0_stable_eigenpair
    (p : Params) {δ t₀ : ℝ} :
    ∃ v : State,
      (-1 : ℝ) < 0 ∧
      HasEigenpair (jacobianAtZero p) (-1) v ∧
      ∃ r > 0, ∃ eps > 0,
        (E0 + δ • v ∈ Metric.closedBall E0 r →
          ∃ z : ℝ → State,
            z t₀ = E0 + δ • v ∧
            ∀ t ∈ Ioo (t₀ - eps) (t₀ + eps),
              HasDerivAt z (vectorField p (z t)) t) := by
  let v : State := stableVectorAtZero
  have hv : HasEigenpair (jacobianAtZero p) (-1) v := by
    simpa [v] using jacobianAtZero_stable_eigenpair p
  obtain ⟨r, hr, eps, heps, hloc⟩ := localSolutionExists p E0 t₀
  refine ⟨v, by norm_num, hv, r, hr, eps, heps, ?_⟩
  intro hnear
  exact hloc (E0 + δ • v) hnear

def HasHeteroclinicE1E0 (p : Params) : Prop :=
  ∃ z : ℝ → State,
    SolvesTWODE p z ∧
    Tendsto z atBot (nhds E1) ∧
    Tendsto z atTop (nhds E0)

theorem HasHeteroclinicE1E0.shift
    {p : Params} (h : HasHeteroclinicE1E0 p) (a : ℝ) :
    HasHeteroclinicE1E0 p := by
  rcases h with ⟨z, hzode, hleft, hright⟩
  exact ⟨fun t => z (t + a), hzode.shift a,
    hleft.comp (tendsto_atBot_add_const_right atBot a tendsto_id),
    hright.comp (tendsto_atTop_add_const_right atTop a tendsto_id)⟩

theorem HasHeteroclinicE1E0.exists_solution
    {p : Params} (h : HasHeteroclinicE1E0 p) :
    ∃ z : ℝ → State,
      SolvesTWODE p z ∧
      Tendsto z atBot (nhds E1) ∧
      Tendsto z atTop (nhds E0) :=
  h

theorem travelingWave_of_heteroclinic
    (p : Params)
    (h : HasHeteroclinicE1E0 p) :
    Nonempty (TravelingWave p) := by
  rcases h with ⟨z, hzode, hleft, hright⟩
  exact ⟨⟨z, hzode, hleft, hright⟩⟩

theorem HasHeteroclinicE1E0.exists_travelingWave
    {p : Params} (h : HasHeteroclinicE1E0 p) :
    ∃ w : TravelingWave p,
      SolvesTWODE p w.z ∧
      Tendsto w.z atBot (nhds E1) ∧
      Tendsto w.z atTop (nhds E0) := by
  rcases h with ⟨z, hzode, hleft, hright⟩
  exact ⟨⟨z, hzode, hleft, hright⟩, hzode, hleft, hright⟩

theorem HasHeteroclinicE1E0.exists_profile_c2_bootstrap
    {p : Params} (h : HasHeteroclinicE1E0 p) :
    ∃ z : ℝ → State,
      SolvesTWODE p z ∧
      Tendsto z atBot (nhds E1) ∧
      Tendsto z atTop (nhds E0) ∧
      ContDiff ℝ 2 (fun t => z t 0) ∧
      ContDiff ℝ 2 (fun t => z t 2) ∧
      (∀ t : ℝ,
        HasDerivAt (deriv (fun s => z s 0))
          (-p.c * z t 1
            + p.chi *
              ((p.m : ℝ) * (z t 0) ^ (p.m - 1) * z t 1 * z t 3
                + (z t 0) ^ p.m * (z t 2 - (z t 0) ^ p.gamma))
            - z t 0 * (1 - (z t 0) ^ p.alpha)) t) ∧
      (∀ t : ℝ, HasDerivAt (deriv (fun s => z s 2))
        (z t 2 - (z t 0) ^ p.gamma) t) := by
  rcases h with ⟨z, hzode, hleft, hright⟩
  rcases hzode.profile_c2_bootstrap with ⟨hU, hV, hUeq, hVeq⟩
  exact ⟨z, hzode, hleft, hright, hU, hV, hUeq, hVeq⟩

theorem HasHeteroclinicE1E0.exists_profile_equations
    {p : Params} (h : HasHeteroclinicE1E0 p) :
    ∃ z : ℝ → State,
      SolvesTWODE p z ∧
      Tendsto z atBot (nhds E1) ∧
      Tendsto z atTop (nhds E0) ∧
      (∀ t : ℝ,
        iteratedDeriv 2 (fun s => z s 0) t
          + p.c * deriv (fun s => z s 0) t
          - p.chi * deriv
              (fun y => (z y 0) ^ p.m * deriv (fun s => z s 2) y) t
          + z t 0 * (1 - (z t 0) ^ p.alpha) = 0) ∧
      (∀ t : ℝ,
        iteratedDeriv 2 (fun s => z s 2) t - z t 2
          + (z t 0) ^ p.gamma = 0) := by
  rcases h with ⟨z, hzode, hleft, hright⟩
  rcases hzode.profile_equations with ⟨hUeq, hVeq⟩
  exact ⟨z, hzode, hleft, hright, hUeq, hVeq⟩

theorem HasHeteroclinicE1E0.exists_profileData
    {p : Params} (h : HasHeteroclinicE1E0 p) :
    ∃ U V : ℝ → ℝ, WaveProfileData p U V := by
  rcases travelingWave_of_heteroclinic p h with ⟨w⟩
  exact ⟨fun t => w.z t 0, fun t => w.z t 2, w.to_profileData⟩

end TravelingWaveODE
end PDE
end ShenWork
