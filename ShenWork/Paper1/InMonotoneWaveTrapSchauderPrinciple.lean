import ShenWork.Paper1.WaveTrapProjectedCubeApproxData
import ShenWork.Paper1.SchauderPrincipleAssembled

/-!
# The local-uniform Schauder fixed-point principle for the monotone wave trap, UNCONDITIONAL

Chaining our own `brouwer_fixedPoint` (n-dim, via Sperner) + `exists_finite_eps_net`, assembled through the
partition-of-unity Schauder projection `waveTrapProjectedCubeApproxData` and the scaffold
`localUniformSchauderFixedPointPrinciple_of_brouwer`, we discharge the abstract Schauder principle on
`InMonotoneWaveTrapSet κ M` with NO carried hypothesis.  This is the object the wave-existence headline
carried as `schauder_principle`.
-/

namespace ShenWork.Paper1

/-- **The Schauder fixed-point principle on the monotone wave trap, unconditional.**
Built from our own Brouwer + ε-net via the partition-of-unity projection. -/
theorem inMonotoneWaveTrap_schauderPrinciple {κ M : ℝ} (hM : 0 ≤ M) :
    LocalUniformSchauderFixedPointPrinciple (InMonotoneWaveTrapSet κ M) :=
  localUniformSchauderFixedPointPrinciple_of_brouwer
    (fun _Tmap hmap hcont hcompact =>
      waveTrapProjectedCubeApproxData hM hmap hcont hcompact)

end ShenWork.Paper1
