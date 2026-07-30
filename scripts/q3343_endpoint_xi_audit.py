#!/usr/bin/env python3
from __future__ import annotations

from collections import defaultdict
from math import isqrt

QMAX = 30_000
NMAX = 30_000


def primes_upto(limit: int) -> list[int]:
    mark = bytearray(b"\x01") * (limit + 1)
    mark[:2] = b"\x00\x00"
    for p in range(2, isqrt(limit) + 1):
        if mark[p]:
            mark[p*p:limit+1:p] = b"\x00" * ((limit-p*p)//p + 1)
    return [p for p in range(2, limit + 1) if mark[p]]


def P(n: int) -> int:
    return 34*n**3 + 51*n**2 + 27*n + 5


def lam(n: int) -> int:
    return n*(n+1)


def inv(x: int, q: int) -> int:
    return pow(x % q, -1, q)


def apery_mod(q: int, limit: int) -> list[int]:
    assert 0 <= limit < q
    b = [0]*(limit+1)
    b[0] = 1
    if limit:
        b[1] = 5 % q
    for n in range(1, limit):
        b[n+1] = ((P(n)*b[n] - n**3*b[n-1]) * inv((n+1)**3, q)) % q
    return b


def companion_mod(q: int, limit: int) -> list[int]:
    assert 0 <= limit < q
    a = [0]*(limit+1)
    if limit:
        a[1] = 6 % q
    for n in range(1, limit):
        a[n+1] = ((P(n)*a[n] - n**3*a[n-1]) * inv((n+1)**3, q)) % q
    return a


def franel_mod(q: int, limit: int) -> list[int]:
    assert 0 <= limit < q
    f = [0]*(limit+1)
    f[0] = 1
    if limit:
        f[1] = 2
    for n in range(1, limit):
        f[n+1] = (((7*n*n+7*n+2)*f[n] + 8*n*n*f[n-1]) * inv((n+1)**2, q)) % q
    return f


def shell_for(n: int, j: int):
    J = (n-1)//3
    while J >= 1:
        L = J//2
        if L < j <= J:
            return J, L
        J = L
    return None


def factorials_mod(q: int, limit: int) -> tuple[list[int], list[int]]:
    fac = [1]*(limit+1)
    for k in range(1, limit+1):
        fac[k] = fac[k-1]*k % q
    ifac = [1]*(limit+1)
    ifac[limit] = inv(fac[limit], q)
    for k in range(limit, 0, -1):
        ifac[k-1] = ifac[k]*k % q
    return fac, ifac


def endpoint_and_roots(q: int, j: int, b: list[int]):
    """Return every eligible (J, scaled actual second jet) on scaled first-jet support."""
    maxJ = min(2*j-1, (q-2)//2)
    assert 1 <= j <= maxJ and b[j] == 0 and b[j-1] != 0
    f = franel_mod(q, maxJ)
    fac, ifac = factorials_mod(q, 2*maxJ+1)
    lj = lam(j) % q

    pk = 1
    h1 = 0
    h2 = 0
    rho = 0
    sigma = 0
    for k in range(j+1):
        rho = (rho + f[k]*pk*h1) % q
        sigma = (sigma + f[k]*pk*(h1*h1-h2)) % q
        if k < j:
            gap = (lj-lam(k)) % q
            ig = inv(gap, q)
            h1 = (h1+ig) % q
            h2 = (h2+ig*ig) % q
            pk = pk*gap % q * inv((k+1)**2, q) % q

    scale = (2*j+1) % q
    R = scale*rho % q
    C = scale*sigma % q
    out: list[tuple[int,int]] = []
    if R == 0:
        out.append((j, C))
    if j == maxJ:
        return out

    # h = (2j+1) p'_(j+1)(lambda_j) = (2j)!/(j+1)!^2.
    h = fac[2*j] * ifac[j+1] % q * ifac[j+1] % q
    H = h1  # H_(j+1,j): nodes h<j+1 excluding j.
    for K in range(j+1, maxJ+1):
        tau = f[K]*h % q
        R = (R+tau) % q
        C = (C+2*tau*H) % q
        if R == 0:
            out.append((K, C))
        if K < maxJ:
            H = (H + inv(lj-lam(K), q)) % q
            h = (-h*(K-j)*(K+j+1)*inv((K+1)**2, q)) % q
    return out


def derivative_rows(J: int, j: int, q: int):
    fac, _ = factorials_mod(q, 2*J+1)
    w = []
    for i in range(J+1):
        sign = q-1 if ((J-i)&1) else 1
        w.append(sign*(2*i+1)*inv(fac[J-i]*fac[J+i+1], q) % q)
    lj = lam(j) % q
    d1 = [0]*(J+1)
    invgap = [0]*(J+1)
    Hall = 0
    H2all = 0
    for i in range(J+1):
        if i == j:
            continue
        ig = inv(lj-lam(i), q)
        invgap[i] = ig
        Hall = (Hall+ig) % q
        H2all = (H2all+ig*ig) % q
        d1[i] = w[i]*inv(w[j]*(lj-lam(i)), q) % q
    d1[j] = -sum(d1) % q
    d2 = [0]*(J+1)
    for i in range(J+1):
        if i == j:
            d2[i] = (Hall*Hall-H2all) % q
        else:
            d2[i] = 2*d1[i]*(Hall-invgap[i]) % q
    Hboundary = Hall if J == j else (Hall-invgap[J]) % q
    return d1, d2, Hboundary


def green_state(J: int, j: int, q: int) -> list[int]:
    g = [0]*(J+1)
    g[j] = 0
    g[j-1] = 1
    for k in range(j-1, 0, -1):
        g[k-1] = (P(k)*g[k]-(k+1)**3*g[k+1])*inv(k**3, q) % q
    for k in range(j, J):
        g[k+1] = (P(k)*g[k]-k**3*g[k-1])*inv((k+1)**3, q) % q
    return g


def dot(row: list[int], values: list[int], q: int) -> int:
    return sum(x*y for x,y in zip(row, values)) % q


def exact_endpoint_certificate(J: int, j: int, q: int, expected_C: int):
    b = apery_mod(q, J)
    a = companion_mod(q, J)
    d1,d2,H = derivative_rows(J,j,q)
    rb,sb = dot(d1,b,q),dot(d2,b,q)
    ra,sa = dot(d1,a,q),dot(d2,a,q)
    Rb = (2*j+1)*rb % q
    Cb = (2*j+1)*sb % q
    Xi_b = (Cb-2*H*Rb) % q
    Ra = (2*j+1)*ra % q
    Ca = (2*j+1)*sa % q
    Xi_a = (Ca-2*H*Ra) % q

    g = green_state(J,j,q)
    beta1 = dot(d1,g,q)
    beta2 = dot(d2,g,q)
    cas = 6*inv(j**3,q) % q
    assert (a[j]*b[j-1]-a[j-1]*b[j]) % q == cas
    assert beta1 == j**3*inv(6,q)*(a[j]*rb-b[j]*ra) % q
    assert beta2 == j**3*inv(6,q)*(a[j]*sb-b[j]*sa) % q
    assert Rb == 0
    assert Cb == expected_C
    assert Xi_b == expected_C
    assert beta1 == 0
    lhs = j**3*(a[j]*Xi_b-b[j]*Xi_a) % q
    rhs = 6*(2*j+1)*(beta2-2*H*beta1) % q
    assert lhs == rhs
    assert Xi_b != 0 and beta2 != 0
    return Xi_b, inv(Xi_b,q), beta2, H, Xi_a


def enumerate_support(qmax: int):
    folded_pairs = []
    support = []
    support_map: dict[tuple[int,int,int],int] = {}
    central_support = 0
    for q in primes_upto(qmax):
        if q < 5:
            continue
        half = (q-1)//2
        b = apery_mod(q, half)
        for j in range(1, half+1):
            if b[j] != 0:
                continue
            folded_pairs.append((q,j))
            roots = endpoint_and_roots(q,j,b)
            for J,C in roots:
                key = (J,j,q)
                assert key not in support_map
                support_map[key] = C
                support.append((J,j,q,C))
                if 2*j+1 == q:
                    central_support += 1
    support.sort()
    folded_pairs.sort()
    return folded_pairs,support,support_map,central_support


def actual_tuples(target_pairs, support_map, nmax: int):
    rows = set()
    support_used = set()
    for q,j in target_pairs:
        maxa = min(q-1,(nmax-j)//q)
        for a in range(1,maxa+1):
            n = a*q+j
            sh = shell_for(n,j)
            if sh is None: continue
            J,L = sh
            if q > 2*J+1 and (J,j,q) in support_map:
                rows.add((n,q,J,L,j,"D"))
                support_used.add((J,j,q))
        maxc = min(q-1,(nmax+1+j)//q)
        for c in range(2,maxc+1):
            n = c*q-1-j
            if n > nmax: continue
            sh = shell_for(n,j)
            if sh is None: continue
            J,L = sh
            if q > 2*J+1 and (J,j,q) in support_map:
                rows.add((n,q,J,L,j,"R"))
                support_used.add((J,j,q))
    return sorted(rows),sorted(support_used)


def main() -> None:
    targets10,support10,_,central10 = enumerate_support(10_000)
    unfolded10 = sum(1 if 2*j+1 == q else 2 for J,j,q,C in support10)
    print("Q3343 COUNT REPAIR")
    print("qmax_10000_folded_target_pairs",len(targets10))
    print("qmax_10000_unique_support_triples",len(support10))
    print("qmax_10000_central_support_triples",central10)
    print("qmax_10000_unfolded_reflected_realizations",unfolded10)
    assert len(support10) == 78
    assert unfolded10 == 159
    assert unfolded10 == 2*len(support10)-central10

    targets,support,support_map,central = enumerate_support(QMAX)
    print("qmax_30000_folded_target_pairs",len(targets))
    print("qmax_30000_unique_beta1_support_triples",len(support))
    print("qmax_30000_central_support_triples",central)
    assert len(targets) == 1653
    assert len(support) == 180

    tuples,used = actual_tuples(targets,support_map,NMAX)
    print("nmax_30000_actual_tuples",len(tuples))
    print("nmax_30000_actual_support_triples",len(used))
    assert len(tuples) == 34
    assert len(used) == 13

    certificates = []
    simultaneous = []
    for J,j,q,C in support:
        if C == 0:
            simultaneous.append((J,j,q))
            continue
        xi,xi_inv,beta2,H,xi_a = exact_endpoint_certificate(J,j,q,C)
        certificates.append((J,j,q,xi,xi_inv,beta2,H,xi_a))
    print("simultaneous_beta1_beta2_target_zero",len(simultaneous))
    assert simultaneous == []
    assert len(certificates) == 180

    print("ACTUAL_SUPPORT_TRIPLES")
    for row in used:
        print(*row)
    print("ACTUAL_TUPLES columns=n q J L j branch")
    for row in tuples:
        print(*row)
    print("ENDPOINT_CERTIFICATES columns=J j q Xi XiInverse beta2 Hboundary XiCompanion")
    for row in certificates:
        print(*row)
    print("first_counterexample=None")
    print("all_assertions_passed=True")


if __name__ == "__main__":
    main()
