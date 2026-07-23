#!/usr/bin/env python3
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

LIMIT = 5000
MAX_ROWS = 60


def primes_upto(n: int) -> list[int]:
    sieve = bytearray(b"\x01") * (n + 1)
    sieve[:2] = b"\x00\x00"
    for q in range(2, int(n**0.5) + 1):
        if sieve[q]:
            sieve[q*q:n+1:q] = b"\x00" * (((n - q*q)//q) + 1)
    return [i for i in range(2, n + 1) if sieve[i]]


def P(n: int) -> int:
    return 34*n**3 + 51*n**2 + 27*n + 5


def dP(n: int) -> int:
    return 102*n**2 + 102*n + 27


def apery_and_parameter_derivative(p: int) -> tuple[list[int], list[int]]:
    """Return A_0,...,A_{p-1} mod p^2 and D_n=A'(n) mod p.

    The analytic continuation is
      A(x) = sum_{k>=0} (-x)_k^2 (x+1)_k^2/(k!)^4,
    so D_n is its parameter derivative at x=n.
    """
    p2 = p*p
    A = [0] * p
    A[0] = 1
    if p > 1:
        A[1] = 5
    for n in range(1, p - 1):
        den = pow(n + 1, 3, p2)
        num = (P(n) * A[n] - n**3 * A[n-1]) % p2
        A[n+1] = num * pow(den, -1, p2) % p2

    D = [0] * p
    D[0] = 0
    if p > 1:
        D[1] = 12 % p
    for n in range(1, p - 1):
        den = pow(n + 1, 3, p)
        rhs = (
            dP(n) * (A[n] % p)
            + P(n) * D[n]
            - 3*n*n * (A[n-1] % p)
            - n**3 * D[n-1]
            - 3*(n+1)*(n+1) * (A[n+1] % p)
        ) % p
        D[n+1] = rhs * pow(den, -1, p) % p
    return A, D


def direct_derivative_exact(j: int) -> Fraction:
    """Exact derivative A'(j)=2 sum T(j,k)(H_{j+k}-H_{j-k})."""
    H = [Fraction(0)]
    for r in range(1, 2*j + 1):
        H.append(H[-1] + Fraction(1, r))
    from math import comb
    s = Fraction(0)
    for k in range(j + 1):
        T = comb(j, k)**2 * comb(j+k, k)**2
        s += 2 * T * (H[j+k] - H[j-k])
    return s


@dataclass
class ZeroRow:
    p: int
    j: int
    jr: int
    qj: int
    deriv: int
    qr: int
    vj_ge2: bool
    vr_ge2: bool


primes = [p for p in primes_upto(LIMIT) if p & 1]
rows: list[ZeroRow] = []
reflection_failures: list[tuple[int,int,int,int]] = []
multiple_roots: list[tuple[int,int]] = []
self_p2: list[tuple[int,int]] = []
left_p2: list[tuple[int,int]] = []
right_p2: list[tuple[int,int]] = []
primes_with_zeros: set[int] = set()

for p in primes:
    A, D = apery_and_parameter_derivative(p)
    p2 = p*p
    half = (p - 3)//2
    for j in range(half + 1):
        jr = p - 1 - j
        lhs = A[jr] % p2
        rhs = (A[j] - p * D[j]) % p2
        if lhs != rhs:
            reflection_failures.append((p, j, lhs, rhs))
        if A[j] % p == 0:
            primes_with_zeros.add(p)
            qj = (A[j] // p) % p
            qr = (A[jr] // p) % p
            row = ZeroRow(
                p=p, j=j, jr=jr, qj=qj, deriv=D[j], qr=qr,
                vj_ge2=(A[j] % p2 == 0), vr_ge2=(A[jr] % p2 == 0),
            )
            rows.append(row)
            if D[j] % p == 0:
                multiple_roots.append((p,j))
            if (A[jr] - A[j]) % p2 == 0:
                self_p2.append((p,j))
            if A[j] % p2 == 0:
                left_p2.append((p,j))
            if A[jr] % p2 == 0:
                right_p2.append((p,j))
            assert (qr - (qj - D[j])) % p == 0

# Independent exact harmonic-sum values; these need not be integers.
small_derivative_checks = []
for j in range(0, 11):
    ex = direct_derivative_exact(j)
    small_derivative_checks.append((j, str(ex)))

print("Q715 EXACT APERY REFLECTION TEST")
print(f"prime_limit={LIMIT}")
print(f"odd_primes_tested={len(primes)}")
print(f"reflection_formula_failures={len(reflection_failures)}")
print(f"primes_with_at_least_one_zero={len(primes_with_zeros)}")
print(f"zero_pairs_total={len(rows)}")
print(f"multiple_index_roots_D_eq_0={len(multiple_roots)}")
print(f"p2_divides_reflection_difference={len(self_p2)}")
print(f"p2_divides_left_member_A_j={len(left_p2)}")
print(f"p2_divides_reflected_member={len(right_p2)}")
print("small_exact_parameter_derivatives=" + repr(small_derivative_checks))

if reflection_failures:
    print("REFLECTION_FAILURES", reflection_failures[:20])
if multiple_roots:
    print("MULTIPLE_ROOTS", multiple_roots[:50])
if self_p2:
    print("P2_SELF_REFLECTION", self_p2[:50])
if left_p2:
    print("LEFT_P2", left_p2[:50])
if right_p2:
    print("RIGHT_P2", right_p2[:50])

print("FIRST_ZERO_PAIRS columns: p j p-1-j A_j/p_mod_p D_j_mod_p A_ref/p_mod_p v_p(A_j)>=2 v_p(A_ref)>=2")
for r in rows[:MAX_ROWS]:
    print(r.p, r.j, r.jr, r.qj, r.deriv, r.qr, int(r.vj_ge2), int(r.vr_ge2))

print("LAST_ZERO_PAIRS")
for r in rows[-20:]:
    print(r.p, r.j, r.jr, r.qj, r.deriv, r.qr, int(r.vj_ge2), int(r.vr_ge2))
