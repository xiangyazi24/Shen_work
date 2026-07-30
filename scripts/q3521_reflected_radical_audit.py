#!/usr/bin/env python3
"""Q3521: exact quotient-two reflected radical audit.

Standard library only.  No large Apéry integer is formed or factored.
The program
  * sieves primes;
  * computes Apéry residues b_t mod p by the exact recurrence;
  * enumerates every quotient-two reflected-q/direct-ell target-pair geometry
    with ambient index n <= 50000;
  * checks the (u,s), (j,h), folded-index, gap, and prime injections;
  * checks Q3498 reflection q | b_j and the exact Apéry continuant q | N_L(j);
  * classifies repeated-node primes using only factorization of O(n) geometry
    integers (not Apéry numbers);
  * records disjoint radical contributions for the explicit aggregate wedges.
"""
from __future__ import annotations

from collections import Counter, defaultdict
from dataclasses import dataclass
from hashlib import sha256
from math import gcd, isqrt, log
import sys

sys.set_int_max_str_digits(0)
LIMIT = 50_000


def sieve(n: int) -> tuple[list[bool], list[int], list[int]]:
    prime = bytearray(b"\x01") * (n + 1)
    prime[0:2] = b"\x00\x00"
    for p in range(2, isqrt(n) + 1):
        if prime[p]:
            prime[p*p:n+1:p] = b"\x00" * (((n-p*p)//p)+1)
    primes = [p for p in range(2, n + 1) if prime[p]]
    # Largest prime factor of ordinary geometry integers only.
    lpf = [0] * (n + 1)
    for p in primes:
        for m in range(p, n + 1, p):
            lpf[m] = p
    return [bool(x) for x in prime], primes, lpf


def P(m: int) -> int:
    return 34*m**3 + 51*m**2 + 27*m + 5


def apery_zero_indices_mod(p: int, max_t: int) -> tuple[set[int], int]:
    """Return {t <= max_t : p | b_t}, using the recurrence modulo p."""
    assert 0 <= max_t < p
    zeros: set[int] = set()
    if 1 % p == 0:
        zeros.add(0)
    if max_t == 0:
        return zeros, 0
    b0, b1 = 1 % p, 5 % p
    if b1 == 0:
        zeros.add(1)
    if max_t == 1:
        return zeros, 0
    inv = [0] * (max_t + 2)
    inv[1] = 1
    for a in range(2, max_t + 2):
        inv[a] = (p - (p // a) * inv[p % a]) % p
    steps = 0
    for m in range(1, max_t):
        num = (P(m) * b1 - (m**3 % p) * b0) % p
        inv3 = inv[m+1] ** 3 % p
        b2 = num * inv3 % p
        if b2 == 0:
            zeros.add(m+1)
        b0, b1 = b1, b2
        steps += 1
    return zeros, steps


def apery_small(limit: int) -> list[int]:
    b = [1, 5]
    for m in range(1, limit):
        num = P(m) * b[m] - m**3 * b[m-1]
        den = (m+1)**3
        assert num % den == 0
        b.append(num // den)
    return b


def continuant_mod(p: int, j: int, L: int) -> int:
    """N_L(j) modulo p, N_0=0,N_1=1."""
    assert L >= 1
    if L == 1:
        return 1 % p
    n0, n1 = 0, 1
    for a in range(1, L):
        x = j + a
        n2 = (P(x) * n1 - pow(x, 6, p) * n0) % p
        n0, n1 = n1, n2
    return n1


def direct_assignment(n: int, j: int, lpf: list[int]) -> int | None:
    x = n - j
    if x <= 1:
        return None
    p = lpf[x]
    if p and p*p > n and p <= n and x % p == 0 and 2*j <= p-1:
        a = x // p
        if a >= 1 and n // p == a and n % p == j:
            return p
    return None


def reflected_assignment(n: int, j: int, lpf: list[int]) -> int | None:
    x = n + 1 + j
    if x <= 1:
        return None
    p = lpf[x]
    if p and p*p > n and p <= n and x % p == 0 and 2*j <= p-1:
        B = x // p
        if B >= 2 and n // p == B-1 and n % p == p-1-j:
            return p
    return None


@dataclass(frozen=True)
class Geometry:
    n: int
    q: int
    ell: int
    r: int
    s: int
    h: int
    j: int
    L: int
    u: int
    w: int
    q_mult: bool
    ell_mult: bool


def cutoffs(n: int) -> tuple[int, int, int]:
    ln = log(max(n, 3))
    lln = max(log(max(ln, 2.0)), 1.0)
    U = int(n / (ln * lln))
    S = U
    W = int(ln / (lln * lln))
    return U, S, W


def int_digest(x: int) -> str:
    return sha256(str(abs(x)).encode("ascii")).hexdigest()


def main() -> None:
    prime, primes, lpf = sieve(LIMIT + 2)
    zero_by_p: dict[int, set[int]] = {}
    direct_by_n: dict[int, list[tuple[int,int]]] = defaultdict(list)
    reflected_by_n: dict[int, list[tuple[int,int,int]]] = defaultdict(list)
    central_by_n: dict[int, list[tuple[int,int]]] = defaultdict(list)
    recurrence_steps = 0

    for p in primes:
        if p < 5 or 2*p > LIMIT:
            continue
        max_t = min(p-1, LIMIT - 2*p)
        if max_t < 0:
            continue
        zeros, steps = apery_zero_indices_mod(p, max_t)
        recurrence_steps += steps
        zero_by_p[p] = zeros
        for t in zeros:
            n = 2*p + t
            if n > LIMIT:
                continue
            if 2*t < p-1:
                direct_by_n[n].append((p,t))
            elif 2*t > p-1:
                reflected_by_n[n].append((p,t,p-1-t))
            else:
                central_by_n[n].append((p,t))

    small = apery_small(4)
    assert small[2] == 73 and small[4] == 33001
    assert gcd(small[2], small[4]) == 1  # Apéry b_n is not strong-divisibility.

    geometries: list[Geometry] = []
    by_n: dict[int, list[Geometry]] = defaultdict(list)
    map_nu: dict[tuple[int,int], tuple[int,int,int,int]] = {}
    map_ns: dict[tuple[int,int], int] = {}
    map_nus: set[tuple[int,int,int]] = set()
    map_njh: dict[tuple[int,int,int], tuple[int,int]] = {}
    cont_cache: dict[tuple[int,int], int] = {}

    for n in sorted(set(direct_by_n) & set(reflected_by_n)):
        for q,r,j in reflected_by_n[n]:
            for ell,s in direct_by_n[n]:
                if not q < ell:
                    continue
                h = ell-q
                if r != s + 2*h:
                    continue
                assert h % 2 == 0  # difference of odd primes
                if h < s-2:
                    continue
                if q-r <= 2*h-4:
                    continue
                assert j == q-1-r and j < r
                L = r-j
                u = L-1
                w = j+4-2*h
                assert w == s+3-u
                assert u >= 0 and w >= 0 and u <= s+3
                assert 15*s-2*u <= n+20

                # Exact inverse parameterization.
                assert 5*q == 2*n-u
                assert 5*j == n-5-3*u
                assert 5*r == n+2*u
                assert 2*ell == n-s
                assert 10*h == n-5*s+2*u
                assert 13*s <= n+26
                assert 13*u <= n+65
                assert 13*q >= 5*n-13 and 5*q <= 2*n
                assert 13*ell >= 6*n-13 and 2*ell <= n
                assert q*q > n and ell*ell > n

                # Q3498 reflected descent and exact recurrence endpoint carrier.
                assert j in zero_by_p[q], (n,q,r,j)
                if q > 5:
                    assert j+1 not in zero_by_p[q], (n,q,j)
                key = (n,u)
                if key not in cont_cache:
                    cont_cache[key] = continuant_mod(q,j,L)
                assert cont_cache[key] == 0, (n,q,j,L,cont_cache[key])

                q_mult = direct_assignment(n,j,lpf) is not None
                ell_mult = reflected_assignment(n,s,lpf) is not None
                g = Geometry(n,q,ell,r,s,h,j,L,u,w,q_mult,ell_mult)

                old = map_nu.setdefault((n,u),(q,j,r,L))
                assert old == (q,j,r,L)
                oldell = map_ns.setdefault((n,s),ell)
                assert oldell == ell
                assert (n,u,s) not in map_nus
                map_nus.add((n,u,s))
                oldjh = map_njh.setdefault((n,j,h),(u,s))
                assert oldjh == (u,s)
                geometries.append(g)
                by_n[n].append(g)

    # Fixed-w progression and determinant checks.
    fixed_w_groups: dict[tuple[int,int], list[Geometry]] = defaultdict(list)
    for g in geometries:
        fixed_w_groups[(g.n,g.w)].append(g)
    for (n,w), rows in fixed_w_groups.items():
        rows.sort(key=lambda z:z.s)
        s0,q0,e0 = rows[0].s,rows[0].q,rows[0].ell
        for z in rows:
            assert (z.s-s0) % 20 == 0
            t = (z.s-s0)//20
            assert z.q == q0-4*t
            assert z.ell == e0-10*t
            assert 5*z.q == 2*n-z.s-3+w
            assert 2*z.ell == n-z.s
        assert abs(q0*(-10)-(-4)*e0) == 2*(n+w-3)

    # Multiplicity ledgers and disjoint radical partitions for every ambient n.
    multiplicity_u = Counter((g.n,g.u) for g in geometries)
    multiplicity_s = Counter((g.n,g.s) for g in geometries)
    multiplicity_j = Counter((g.n,g.j) for g in geometries)
    multiplicity_h = Counter((g.n,g.h) for g in geometries)
    radical_rows = []
    global_category_counts = Counter()

    for n, rows in by_n.items():
        U,S,W = cutoffs(n)
        allp = {z.q for z in rows} | {z.ell for z in rows}
        mult = {z.q for z in rows if z.q_mult} | {z.ell for z in rows if z.ell_mult}

        small_s_incident = set()
        for z in rows:
            if z.s <= S:
                small_s_incident.update((z.q,z.ell))
        small_s = small_s_incident - mult
        assert len(small_s) <= 2*S + 7

        small_w_incident = set()
        for z in rows:
            if z.s > S and z.w <= W:
                small_w_incident.update((z.q,z.ell))
        small_w = small_w_incident - mult - small_s

        small_L_q = {z.q for z in rows if z.L <= U}
        small_L_q -= mult | small_s | small_w
        assert len(small_L_q) <= U

        covered = mult | small_s | small_w | small_L_q
        remainder = allp - covered
        rem_q = {z.q for z in rows if z.q in remainder}
        rem_ell = {z.ell for z in rows if z.ell in remainder}
        # Exact sharp wedge after the priority partition.
        for z in rows:
            if z.q in rem_q:
                assert z.L > U and z.s > S and z.w > W and not z.q_mult
            if z.ell in rem_ell:
                assert z.s > S and z.w > W and not z.ell_mult

        logs = {
            "all": sum(log(p) for p in allp),
            "mult": sum(log(p) for p in mult),
            "small_s": sum(log(p) for p in small_s),
            "small_w": sum(log(p) for p in small_w),
            "small_L_q": sum(log(p) for p in small_L_q),
            "remainder": sum(log(p) for p in remainder),
        }
        assert abs(logs["all"] - sum(v for k,v in logs.items() if k != "all" and k != "remainder") - logs["remainder"]) < 1e-8
        radical_rows.append((logs["remainder"]/n,n,len(rows),len(allp),U,S,W,logs))
        for name in ("mult","small_s","small_w","small_L_q","remainder"):
            global_category_counts[name] += len(locals()[name])

    radical_rows.sort(reverse=True)
    first_rows = [
        (g.n,g.q,g.ell,g.r,g.s,g.h,g.j,g.L,g.u,g.w,g.q_mult,g.ell_mult)
        for g in geometries[:25]
    ]
    top_u = sorted(((v,k) for k,v in multiplicity_u.items()), reverse=True)[:15]
    top_s = sorted(((v,k) for k,v in multiplicity_s.items()), reverse=True)[:15]
    top_h = sorted(((v,k) for k,v in multiplicity_h.items()), reverse=True)[:15]
    top_n = sorted(((len(v),n,len({z.q for z in v}|{z.ell for z in v})) for n,v in by_n.items()), reverse=True)[:15]

    print("Q3521_REFLECTED_RADICAL_AUDIT")
    print("LIMIT", LIMIT)
    print("MODULAR_RECURRENCE_STEPS", recurrence_steps)
    print("TARGET_ASSIGNMENTS", {
        "direct": sum(map(len,direct_by_n.values())),
        "reflected": sum(map(len,reflected_by_n.values())),
        "central": sum(map(len,central_by_n.values())),
    })
    print("OVERLAP_GEOMETRIES", len(geometries))
    print("AMBIENT_ROWS_WITH_GEOMETRY", len(by_n))
    print("UNIQUE_N_U", len(map_nu), "UNIQUE_N_S", len(map_ns),
          "UNIQUE_N_U_S", len(map_nus), "UNIQUE_N_J_H", len(map_njh))
    print("CONTINUANT_CHECKS", len(cont_cache))
    print("FIXED_W_GROUPS", len(fixed_w_groups))
    print("TOP_U_MULTIPLICITIES", top_u)
    print("TOP_S_MULTIPLICITIES", top_s)
    print("TOP_H_MULTIPLICITIES", top_h)
    print("TOP_AMBIENT_ROWS", top_n)
    print("DISJOINT_PRIME_CATEGORY_OCCURRENCES", dict(global_category_counts))
    print("TOP_REMAINDER_LOG_RATIOS")
    for row in radical_rows[:15]:
        print(row)
    print("FIRST_GEOMETRIES")
    for row in first_rows:
        print(row)
    print("STRONG_DIVISIBILITY_COUNTEREXAMPLE", (small[2],small[4],gcd(small[2],small[4])))
    print("GEOMETRY_DIGEST", int_digest(sum((g.n+g.q+g.ell+g.j+g.L) for g in geometries)))
    print("ALL_ASSERTIONS_PASSED", True)


if __name__ == "__main__":
    main()
