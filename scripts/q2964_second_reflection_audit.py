#!/usr/bin/env python3
from __future__ import annotations

from math import comb

LIMIT = 1000


def primes_upto(n: int) -> list[int]:
    sieve = bytearray(b"\x01") * (n + 1)
    sieve[:2] = b"\x00\x00"
    for q in range(2, int(n**0.5) + 1):
        if sieve[q]:
            sieve[q*q:n+1:q] = b"\x00" * (((n - q*q)//q) + 1)
    return [q for q in range(2, n + 1) if sieve[q]]


def P(n: int) -> int:
    return 34*n**3 + 51*n**2 + 27*n + 5


def dP(n: int) -> int:
    return 102*n**2 + 102*n + 27


def apery_mod(p: int, modulus: int) -> list[int]:
    b = [0] * p
    b[0] = 1
    b[1] = 5 % modulus
    for n in range(1, p - 1):
        rhs = (P(n)*b[n] - n**3*b[n-1]) % modulus
        b[n+1] = rhs * pow((n+1)**3, -1, modulus) % modulus
    return b


def derivative_mod(p: int, modulus: int, b: list[int]) -> list[int]:
    D = [0] * p
    D[0] = 0
    D[1] = 12 % modulus
    for n in range(1, p - 1):
        rhs = (
            P(n)*D[n] - n**3*D[n-1]
            + dP(n)*b[n]
            - 3*(n+1)**2*b[n+1]
            - 3*n**2*b[n-1]
        ) % modulus
        D[n+1] = rhs * pow((n+1)**3, -1, modulus) % modulus
    return D


def is_quadratic_branch(p: int) -> bool:
    return p % 24 in {13, 17, 19, 23}


def root_mod(p: int, modulus: int, quadratic: bool) -> list[int]:
    d = (p - 3)//2 if quadratic else (p - 1)//2
    c = [0] * (d + 1)
    c[0] = 1
    c[1] = (39 if quadratic else 5) * pow(2, -1, modulus) % modulus
    for n in range(1, d):
        if quadratic:
            B = 136*n*n + 204*n + 78
            C = (2*n + 1)**2
        else:
            B = 136*n*n + 68*n + 10
            C = (2*n - 1)**2
        rhs = (B*c[n] - C*c[n-1]) % modulus
        c[n+1] = rhs * pow(4*(n+1)**2, -1, modulus) % modulus
    return c


def conv(a: list[int], b: list[int], modulus: int, length: int) -> list[int]:
    out = [0] * length
    for i, x in enumerate(a):
        if not x:
            continue
        for j, y in enumerate(b):
            if i + j >= length:
                break
            out[i+j] = (out[i+j] + x*y) % modulus
    return out


def scale(a: list[int], s: int, modulus: int) -> list[int]:
    return [(s*x) % modulus for x in a]


def harmonic_tables(p: int) -> tuple[list[int], list[int]]:
    H = [0] * p
    H2 = [0] * p
    for n in range(1, p):
        inv = pow(n, -1, p)
        H[n] = (H[n-1] + inv) % p
        H2[n] = (H2[n-1] + inv*inv) % p
    return H, H2


def taylor_second_digit(p: int, r: int, H: list[int], H2: list[int]) -> int:
    low = 0
    for k in range(r + 1):
        term = (comb(r, k)**2 * comb(r+k, k)**2) % p
        h1 = (H[r+k] - H[r-k]) % p
        h2 = (H2[r+k] - H2[r-k]) % p
        low = (low + term*(2*h1*h1 - h2)) % p

    fact = [1] * p
    for n in range(1, p):
        fact[n] = fact[n-1]*n % p
    tail = 0
    for k in range(r + 1, p - r):
        ratio = fact[r+k] * fact[k-r-1] % p
        ratio = ratio * pow(fact[k], -2, p) % p
        tail = (tail + ratio*ratio) % p
    return (low + tail) % p


def audit_prime(p: int) -> dict:
    p2, p3 = p*p, p*p*p
    half = (p - 1)//2
    quadratic = is_quadratic_branch(p)
    d = (p - 3)//2 if quadratic else half

    b3 = apery_mod(p, p3)
    b2 = [x % p2 for x in b3]
    D2 = derivative_mod(p, p2, b2)
    H, H2 = harmonic_tables(p)

    T = root_mod(p, p3, quadratic)
    g3 = [1, (-34) % p3, 1] if quadratic else [1]
    candidate3 = conv(g3, conv(T, T, p3, p), p3, p)
    diff3 = [(b3[j] - candidate3[j]) % p3 for j in range(p)]
    assert all(x % p2 == 0 for x in diff3), (p, "p^2 square lift")
    E = [(x // p2) % p for x in diff3]
    assert all(E[j] == 0 for j in range(d + 1))

    eps_res = T[d] % p
    assert eps_res in {1, p-1}
    eps = 1 if eps_res == 1 else -1
    assert all((T[d-j] - eps*T[j]) % p == 0 for j in range(d + 1))

    qtilde = []
    for j in range(d + 1):
        x = (T[d-j] - eps*T[j]) % p3
        assert x % p == 0
        qtilde.append((x // p) % p2)
    Q = [x % p for x in qtilde]

    g2 = [x % p2 for x in g3]
    T2 = [x % p2 for x in T]
    r1poly = scale(conv(g2, conv(T2, qtilde, p2, p), p2, p), 2*eps, p2)
    gp = [x % p for x in g3]
    q2poly = conv(gp, conv(Q, Q, p, p), p, p)

    formula_fail = []
    root_fail = []
    first_fail = []
    target_rows = []
    first_endpoint_index = next((j for j in range(d+1, p) if E[j] != 0), None)
    first_endpoint_value = 0 if first_endpoint_index is None else E[first_endpoint_index]

    for r in range(half + 1):
        rr = p - 1 - r
        numerator = (b3[rr] - b3[r] + p*D2[r]) % p3
        if numerator % p2:
            first_fail.append((r, numerator))
            continue
        S_actual = (numerator // p2) % p
        S_formula = taylor_second_digit(p, r, H, H2)
        if S_actual != S_formula:
            formula_fail.append((r, S_actual, S_formula))

        lhs1_num = (b3[rr] - b3[r]) % p3
        assert lhs1_num % p == 0
        lhs1 = (lhs1_num // p) % p2
        edef = (E[rr] - E[r]) % p
        rhs1 = (r1poly[r] + p*((q2poly[r] + edef) % p)) % p2
        if lhs1 != rhs1:
            root_fail.append((r, "first", lhs1, rhs1))

        cancelled = (D2[r] + r1poly[r]) % p2
        assert cancelled % p == 0
        universal_root = ((cancelled // p) + q2poly[r]) % p
        S_root = (universal_root + edef) % p
        if S_root != S_actual:
            root_fail.append((r, "second", S_actual, S_root))

        if b3[r] % p == 0:
            beta = (b3[r] // p) % p
            target_rows.append((r, beta, S_actual, universal_root, edef,
                                first_endpoint_index, first_endpoint_value))

    return {
        "formula_fail": formula_fail,
        "root_fail": root_fail,
        "first_fail": first_fail,
        "targets": target_rows,
        "E_zero": first_endpoint_index is None,
    }


primes = [p for p in primes_upto(LIMIT) if p > 5]
formula_failures = []
root_failures = []
first_failures = []
targets = []
E_zero_primes = []

for p in primes:
    out = audit_prime(p)
    formula_failures.extend((p, x) for x in out["formula_fail"])
    root_failures.extend((p, x) for x in out["root_fail"])
    first_failures.extend((p, x) for x in out["first_fail"])
    targets.extend((p,) + row for row in out["targets"])
    if out["E_zero"]:
        E_zero_primes.append(p)

print("Q2964 SECOND REFLECTION DIGIT AUDIT")
print(f"prime_limit={LIMIT}")
print(f"primes_tested={len(primes)}")
print(f"second_taylor_formula_failures={len(formula_failures)}")
print(f"root_identity_failures={len(root_failures)}")
print(f"p2_divisibility_failures={len(first_failures)}")
print(f"genuine_folded_targets={len(targets)}")
print(f"primes_with_E_identically_zero={len(E_zero_primes)}")
print(f"targets_with_beta_zero={sum(1 for row in targets if row[2] == 0)}")
print(f"targets_with_reflected_endpoint_residual_zero={sum(1 for row in targets if row[5] == 0)}")
print(f"targets_with_first_endpoint_value_zero={sum(1 for row in targets if row[7] == 0)}")

if formula_failures:
    print("FORMULA_FAILURES", formula_failures[:20])
if root_failures:
    print("ROOT_FAILURES", root_failures[:20])
if first_failures:
    print("P2_FAILURES", first_failures[:20])
if E_zero_primes:
    print("E_ZERO_PRIMES", E_zero_primes)

print("FIRST_TARGETS columns: p r beta S universal_root E_ref_minus_E first_E_index first_E_value")
for row in targets[:50]:
    print(*row)
print("LAST_TARGETS")
for row in targets[-20:]:
    print(*row)
