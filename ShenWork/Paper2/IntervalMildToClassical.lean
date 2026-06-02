/-
  ShenWork/Paper2/IntervalMildToClassical.lean

  T7e bridge: IntervalMildSolution to RegularityBootstrap to localExistence.

  Gap analysis for the mild-to-classical bridge.
  Status: design document, maps the remaining work.
-/
import ShenWork.Paper2.IntervalMildPicard

namespace ShenWork.IntervalMildToClassical

/-!
## Gap analysis: IntervalMildSolution to IsPaper2ClassicalSolution

RegularityBootstrap needs 7 conjuncts. Status of each:

1. v exists: define v(t) := resolverR(u(t)). DONE (O1 infrastructure).
2. u > 0: semigroup lower bound + small corrections. DOABLE (extends hmapsTo_nn).
3. v >= 0: resolverR nonneg for nonneg source. DONE (O1 capstone).
4. PDE pointwise for u: differentiate Duhamel integral. HARD (needs Schauder bootstrap).
5. Elliptic eq for v: resolver satisfies it by construction. NEEDS WIRING.
6. Neumann BC: cosine-series structure. DONE (T7[B]).
7. Classical regularity + initial trace: T5/T6 atoms + semigroup continuity. NEEDS ASSEMBLY.

The hard gap is conjunct 4: the Schauder bootstrap
(mild solution bounded -> Hoelder -> source C1 -> Duhamel C2 -> PDE pointwise).
-/

end ShenWork.IntervalMildToClassical
