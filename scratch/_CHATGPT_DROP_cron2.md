# Q1664 cron2 i12

Use one finite Leibniz bound for the i=1 and i=2 cases of hA_global_bounds.

For A = phi * R, apply norm_iteratedFDeriv_mul_le. Bound derivatives of phi by resolverSmoothRightCutoffDerivBound_spec, and bound derivatives of R by Hphys.coeff_bound from heatSemigroup_level0_resolverJointC2Data.

The constants are:

B1 = Phi0 * Bt 1 k + Phi1 * Bt 0 k
B2 = Phi0 * Bt 2 k + 2 * Phi1 * Bt 1 k + Phi2 * Bt 0 k

This is the same physical-data route as the i=0 branch. A purely direct route would need new global bounds for the first two derivatives of resolverTimeCoeff.
