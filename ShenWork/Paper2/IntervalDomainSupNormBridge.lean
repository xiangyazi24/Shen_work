/-
  Sup-norm bridge: the regime M' = max(M, (a/b)^{1/α}) provides
  the interior sup-norm bound for the restart argument.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainL2UEnergyUniform

open ShenWork.IntervalDomain
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.SupNormBridge

/-- The regime bound: `max(M, (a/b)^{1/α})`. -/
def regimeBound (p : CM2Params) (M : ℝ) : ℝ :=
  max M ((p.a / p.b) ^ (1 / p.α))

theorem regimeBound_pos (p : CM2Params) {M : ℝ} (hM : 0 < M) :
    0 < regimeBound p M :=
  lt_max_of_lt_left hM

theorem regimeBound_ge_M (p : CM2Params) (M : ℝ) :
    M ≤ regimeBound p M :=
  le_max_left M _

end ShenWork.Paper2.SupNormBridge
