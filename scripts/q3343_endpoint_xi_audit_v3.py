#!/usr/bin/env python3
from __future__ import annotations

import q3343_endpoint_xi_audit as base
import q3343_endpoint_xi_audit_v2 as audit2


def endpoint_and_roots_all_high_shells(q: int, j: int, b: list[int]):
    """All high-q supports j<=J<q/2; no canonical-shell condition J<2j."""
    maxJ = (q-2)//2
    assert 1 <= j <= maxJ and b[j] == 0 and b[j-1] != 0
    f = base.franel_mod(q, maxJ)
    fac, ifac = base.factorials_mod(q, 2*maxJ+1)
    lj = base.lam(j) % q

    pk = 1
    h1 = h2 = rho = sigma = 0
    for k in range(j+1):
        rho = (rho + f[k]*pk*h1) % q
        sigma = (sigma + f[k]*pk*(h1*h1-h2)) % q
        if k < j:
            gap = (lj-base.lam(k)) % q
            ig = base.inv(gap,q)
            h1 = (h1+ig) % q
            h2 = (h2+ig*ig) % q
            pk = pk*gap % q * base.inv((k+1)**2,q) % q

    scale = (2*j+1) % q
    R = scale*rho % q
    C = scale*sigma % q
    out = []
    if R == 0:
        out.append((j,C))
    if j == maxJ:
        return out

    h = fac[2*j]*ifac[j+1] % q * ifac[j+1] % q
    H = h1
    for K in range(j+1,maxJ+1):
        tau = f[K]*h % q
        R = (R+tau) % q
        C = (C+2*tau*H) % q
        if R == 0:
            out.append((K,C))
        if K < maxJ:
            H = (H + base.inv(lj-base.lam(K),q)) % q
            h = (-h*(K-j)*(K+j+1)*base.inv((K+1)**2,q)) % q
    return out


base.endpoint_and_roots = endpoint_and_roots_all_high_shells

if __name__ == "__main__":
    audit2.main()
