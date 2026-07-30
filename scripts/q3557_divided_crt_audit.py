#!/usr/bin/env python3
"""Q3557 exact first-divided-Lucas/CRT audit.

Standard library only.  The script enumerates every simultaneous quotient-two
pair n=2q+r=2ell+s through n<=20000 with q reflected, ell direct, q<ell,
and the corresponding Apéry target congruences.  It checks:

* local Apéry residues modulo p and p^2 by the recurrence below p;
* the parameter derivative both by its differentiated recurrence and by the
  denominator-safe harmonic formula;
* the first divided-Lucas formulas with slopes -3 (reflected) and +2 (direct)
  against an independent p-adic binomial-sum evaluation of b_n mod p^2;
* the equivalent first-Witt formulas and the nonzero adjacent companion units;
* the normalized adjacent b_(n+1) channel;
* the exact integral CRT right inverse and the gcd-one Smith certificate.

No Apéry integer is factored.  No target-density assumption is used.
"""
from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from hashlib import sha256
from math import gcd, isqrt
import sys

sys.set_int_max_str_digits(0)
LIMIT = 20_000


def P(m: int) -> int:
    return 34*m**3 + 51*m**2 + 27*m + 5


def sieve(n: int) -> tuple[list[bool], list[int]]:
    a = bytearray(b"\x01") * (n + 1)
    a[0:2] = b"\x00\x00"
    for p in range(2, isqrt(n) + 1):
        if a[p]:
            a[p*p:n+1:p] = b"\x00" * (((n-p*p)//p)+1)
    return [bool(x) for x in a], [p for p in range(2, n+1) if a[p]]


def apery_values_mod(p: int, max_t: int, modulus: int) -> list[int]:
    assert 0 <= max_t < p
    if max_t == 0:
        return [1 % modulus]
    b = [1 % modulus, 5 % modulus]
    for m in range(1, max_t):
        den = pow(m+1, 3, modulus)
        assert gcd(den, modulus) == 1
        nxt = (P(m)*b[m] - m**3*b[m-1]) % modulus
        nxt = nxt * pow(den, -1, modulus) % modulus
        b.append(nxt)
    return b


def derivative_values_mod(p: int, b: list[int], max_t: int) -> list[int]:
    """G_t=B'(t) from the exact differentiated Apéry recurrence."""
    if max_t == 0:
        return [0]
    G = [0, 12 % p]
    for m in range(1, max_t):
        inv = pow(m+1, -1, p)
        F = 3 * inv * (((17*m*m + 16*m + 4)*b[m] - m*m*b[m-1]) % p)
        F %= p
        num = (P(m)*G[m] - (m**3 % p)*G[m-1] + F) % p
        den = pow(m+1, 3, p)
        G.append(num * pow(den, -1, p) % p)
    return G


def harmonic_G_J(p: int, m: int) -> tuple[int, int]:
    assert 1 <= m and 2*m < p
    H = [0] * (2*m + 1)
    for a in range(1, 2*m + 1):
        H[a] = (H[a-1] + pow(a, -1, p)) % p
    tau = 1
    G = 0
    J = 0
    for k in range(m + 1):
        G = (G + 2*tau*(H[m+k]-H[m-k])) % p
        omega = ((m-k)*H[m-k] - (m+k)*H[m+k] + 2*k*H[k]) % p
        J = (J + tau*omega) % p
        if k < m:
            z = (m-k)*(m+k+1) % p
            z = z * pow(k+1, -2, p) % p
            tau = tau * z*z % p
    return G, J


def factorial_unit_tables(max_n: int, p: int) -> tuple[list[int], list[int], list[int]]:
    mod = p*p
    vp = [0] * (max_n + 1)
    uf = [1] * (max_n + 1)
    stripped = [1] * (max_n + 1)
    for i in range(1, max_n + 1):
        x = i
        e = 0
        while x % p == 0:
            x //= p
            e += 1
        stripped[i] = x % mod
        vp[i] = vp[i-1] + e
        uf[i] = uf[i-1] * stripped[i] % mod
    invuf = [1] * (max_n + 1)
    invuf[max_n] = pow(uf[max_n], -1, mod)
    for i in range(max_n, 0, -1):
        invuf[i-1] = invuf[i] * stripped[i] % mod
    return vp, uf, invuf


def binom_mod_p2(n: int, k: int, p: int,
                  vp: list[int], uf: list[int], invuf: list[int]) -> int:
    if k < 0 or k > n:
        return 0
    e = vp[n] - vp[k] - vp[n-k]
    if e >= 2:
        return 0
    mod = p*p
    u = uf[n] * invuf[k] % mod * invuf[n-k] % mod
    if e == 1:
        u = u * p % mod
    return u


def apery_sum_mod_p2(n: int, p: int) -> int:
    """Independent exact evaluation of b_n modulo p^2."""
    mod = p*p
    vp, uf, invuf = factorial_unit_tables(2*n, p)
    total = 0
    for k in range(n + 1):
        c1 = binom_mod_p2(n, k, p, vp, uf, invuf)
        c2 = binom_mod_p2(n+k, k, p, vp, uf, invuf)
        z = c1*c2 % mod
        total = (total + z*z) % mod
    return total


@dataclass(frozen=True)
class Local:
    p: int
    m: int
    beta: int
    G: int
    J: int
    K: int
    U: int
    bprev: int
    bnext: int
    Gprev: int
    Gnext: int


def local_data(p: int, m: int) -> Local:
    assert 1 <= m and 2*m < p
    b2 = apery_values_mod(p, m+1, p*p)
    b = [x % p for x in b2]
    assert b[m] == 0 and b2[m] % p == 0
    beta = (b2[m] // p) % p
    Gs = derivative_values_mod(p, b, m+1)
    Gh, J = harmonic_G_J(p, m)
    assert Gs[m] == Gh
    assert (2*J + m*Gh - (b[m]-1)) % p == 0
    K = (m*beta - 4*J) % p
    U = pow(m+1, 3, p) * b[m+1] % p
    assert U != 0
    assert (pow(m,3,p)*b[m-1] + U) % p == 0
    return Local(p,m,beta,Gh,J,K,U,b[m-1],b[m+1],Gs[m-1],Gs[m+1])


def digest_ints(rows: list[tuple[int, ...]]) -> str:
    h = sha256()
    for row in rows:
        h.update((",".join(map(str,row))+"\n").encode("ascii"))
    return h.hexdigest()


def main() -> None:
    prime, primes = sieve(LIMIT)
    direct: dict[int, list[tuple[int,int]]] = defaultdict(list)
    reflected: dict[int, list[tuple[int,int,int]]] = defaultdict(list)
    recurrence_steps = 0

    for p in primes:
        if p < 7 or 2*p > LIMIT:
            continue
        max_t = min(p-1, LIMIT-2*p)
        if max_t < 1:
            continue
        vals = apery_values_mod(p, max_t, p)
        recurrence_steps += max(0, max_t-1)
        for t in range(1, max_t+1):
            if vals[t] != 0:
                continue
            n = 2*p+t
            if 2*t < p-1:
                direct[n].append((p,t))
            elif 2*t > p-1:
                j = p-1-t
                reflected[n].append((p,t,j))

    pairs: list[tuple[int,int,int,int,int,int,int]] = []
    for n in sorted(set(direct) & set(reflected)):
        for q,r,j in reflected[n]:
            for ell,s in direct[n]:
                if q >= ell:
                    continue
                h = ell-q
                assert r == s + 2*h
                assert h > 0 and h % 2 == 0
                assert j == q-1-r and 2*j < q-1
                assert 2*s < ell-1
                pairs.append((n,q,ell,r,s,j,h))

    bn_cache: dict[tuple[int,int], int] = {}
    local_cache: dict[tuple[int,int], Local] = {}
    rows_out: list[tuple[int, ...]] = []
    first_rows = []
    p73 = 0
    square_local = 0
    adjacent_checks = 0
    crt_checks = 0

    def bnmod(n: int, p: int) -> int:
        key = (n,p)
        if key not in bn_cache:
            bn_cache[key] = apery_sum_mod_p2(n,p)
        return bn_cache[key]

    def loc(p: int, m: int) -> Local:
        key = (p,m)
        if key not in local_cache:
            local_cache[key] = local_data(p,m)
        return local_cache[key]

    for n,q,ell,r,s,j,h in pairs:
        Lq = loc(q,j)
        Le = loc(ell,s)
        if q == 73 or ell == 73:
            p73 += 1
        square_local += int(Lq.beta == 0) + int(Le.beta == 0)

        bq = bnmod(n,q)
        be = bnmod(n,ell)
        assert bq % q == 0 and be % ell == 0
        actual_q = (bq // q) % q
        actual_e = (be // ell) % ell
        Cq = 73 * (Lq.beta - 3*Lq.G) % q
        Ce = 73 * (Le.beta + 2*Le.G) % ell
        assert actual_q == Cq, (n,q,actual_q,Cq)
        assert actual_e == Ce, (n,ell,actual_e,Ce)

        # Equivalent first-Witt forms; all displayed denominators are local units.
        CqK = 73 * pow(2*j, -1, q) * (5*j*Lq.beta - 3*Lq.K + 6) % q
        CeK = 73 * pow(s, -1, ell) * (Le.K - 2) % ell
        assert CqK == Cq
        assert CeK == Ce

        # Independent adjacent-global channel checks modulo p^2.
        bq1 = bnmod(n+1,q)
        be1 = bnmod(n+1,ell)
        bq_local = apery_values_mod(q,j+1,q*q)
        be_local = apery_values_mod(ell,s+1,ell*ell)
        pred_q1 = 73 * (bq_local[j-1] - 3*q*Lq.Gprev) % (q*q)
        pred_e1 = 73 * (be_local[s+1] + 2*ell*Le.Gnext) % (ell*ell)
        assert bq1 == pred_q1, (n,q,bq1,pred_q1)
        assert be1 == pred_e1, (n,ell,be1,pred_e1)
        if q != 73:
            num = (bq1 - 73*bq_local[j-1]) % (q*q)
            assert num % q == 0
            y = (num//q) * pow((73*bq_local[j-1]) % q, -1, q) % q
            assert y == (-3*Lq.Gprev*pow(Lq.bprev,-1,q)) % q
        if ell != 73:
            num = (be1 - 73*be_local[s+1]) % (ell*ell)
            assert num % ell == 0
            y = (num//ell) * pow((73*be_local[s+1]) % ell, -1, ell) % ell
            assert y == (2*Le.Gnext*pow(Le.bnext,-1,ell)) % ell
        adjacent_checks += 2

        # Exact integral CRT right inverse.  A=b_n/(q ell) obeys
        # ell*A-Cq=qX and q*A-Ce=ell*Y.  The following solves this for
        # arbitrary integer Cq,Ce, proving there is no cross constraint.
        tq = pow((ell*ell) % q, -1, q)
        te = pow((q*q) % ell, -1, ell)
        A0 = ell*tq*Cq + q*te*Ce
        assert (ell*A0-Cq) % q == 0
        assert (q*A0-Ce) % ell == 0
        X0 = (ell*A0-Cq)//q
        Y0 = (q*A0-Ce)//ell
        assert ell*A0-Cq == q*X0
        assert q*A0-Ce == ell*Y0
        assert A0 % q == Cq*pow(ell,-1,q) % q
        assert A0 % ell == Ce*pow(q,-1,ell) % ell
        assert gcd(gcd(q*q,q*ell),ell*ell) == 1
        crt_checks += 1

        row = (n,q,ell,r,s,j,h,Lq.beta,Le.beta,Lq.G,Le.G,
               Lq.K,Le.K,Lq.U,Le.U,Cq,Ce,A0%(q*ell))
        rows_out.append(row)
        if len(first_rows) < 25:
            first_rows.append(row)

    print("Q3557_DIVIDED_CRT_AUDIT")
    print("LIMIT", LIMIT)
    print("MODULAR_RECURRENCE_STEPS", recurrence_steps)
    print("TARGET_ASSIGNMENTS", {
        "direct": sum(map(len,direct.values())),
        "reflected": sum(map(len,reflected.values())),
    })
    print("SIMULTANEOUS_PAIRS", len(pairs))
    print("AMBIENT_N", len({x[0] for x in pairs}))
    print("LOCAL_DATA_ROWS", len(local_cache))
    print("P73_PAIRS", p73)
    print("SQUARE_LOCAL_DIGITS", square_local)
    print("ADJACENT_CHECKS", adjacent_checks)
    print("CRT_SURJECTIVITY_CHECKS", crt_checks)
    print("FIRST_ROWS")
    for row in first_rows:
        print(row)
    print("PAIR_DIGEST", digest_ints(rows_out))
    print("THEOREM_STATUS", "first digits and CRT no-go universal; counts are finite evidence")
    print("ALL_ASSERTIONS_PASSED", True)


if __name__ == "__main__":
    main()
