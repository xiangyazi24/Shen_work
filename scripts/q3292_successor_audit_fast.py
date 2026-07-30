#!/usr/bin/env python3
from __future__ import annotations

import q3292_successor_audit as base


def recover(residue: int, q: int, qexp: int, unit_fact: int,
            modulus_exp: int, target_exp: int) -> int:
    modulus = q**modulus_exp
    residue %= modulus
    divisor = q**qexp
    assert residue % divisor == 0
    available = modulus_exp - qexp
    local_mod = q**available
    unit_cube = pow(unit_fact % local_mod, 3, local_mod)
    value = (residue // divisor) * pow(unit_cube, -1, local_mod) % local_mod
    return value % (q**target_exp)


def high_factorial(q: int, maxk: int, wanted: set[int], final_exp: int):
    # C_n=(n!)^3 b_n and D_n=(n!)^3 a_n satisfy the division-free
    # recurrence X_{n+1}=P(n)X_n-n^6X_{n-1}.  The fixed extra
    # 3*maxk digits are exactly the factorial q-content later divided out.
    modulus_exp = final_exp + 3*maxk
    modulus = q**modulus_exp
    C0, C1 = 1, 5
    D0, D1 = 0, 6
    fact_unit = 1
    fact_qexp = 0
    out = {}
    limit = maxk*q
    for n in range(1, limit):
        m = n + 1
        C2 = (base.P(n)*C1 - n**6*C0) % modulus
        D2 = (base.P(n)*D1 - n**6*D0) % modulus
        t = m
        while t % q == 0:
            t //= q
            fact_qexp += 1
        fact_unit = fact_unit * t % modulus
        if m in wanted:
            b = recover(C2, q, 3*fact_qexp, fact_unit,
                        modulus_exp, final_exp)
            assert fact_qexp >= 1
            A = recover(D2, q, 3*fact_qexp-3, fact_unit,
                        modulus_exp, final_exp)
            out[m] = (b, A)
        C0, C1 = C1, C2
        D0, D1 = D1, D2
    assert set(out) == wanted
    return out


base.high_regularized = high_factorial
base.first_row()
base.audit()
