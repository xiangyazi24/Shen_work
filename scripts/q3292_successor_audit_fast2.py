#!/usr/bin/env python3
from __future__ import annotations

import q3292_successor_audit as base


def high_dynamic(q: int, maxk: int, wanted: set[int], final_exp: int):
    # X_n=(n!/q^floor(n/q))^3 b_n and
    # Y_n=(n!/q^floor(n/q))^3 q^3 a_n.
    # At a block end the division-free factorial recurrence has an exact
    # q^3 content; divide it and drop exactly three guard digits.
    exp = final_exp + 3*maxk
    mod = q**exp
    X0, X1 = 1, 5
    Y0, Y1 = 0, 6*q**3
    unit_fact = 1
    out = {}
    for n in range(1, maxk*q):
        m = n + 1
        second = n**6
        if n % q == 0:
            second //= q**3
        nx = (base.P(n)*X1 - second*X0) % mod
        ny = (base.P(n)*Y1 - second*Y0) % mod
        t = m
        while t % q == 0:
            t //= q
        unit_fact = unit_fact*t % mod
        if m % q == 0:
            assert nx % q**3 == 0, (q,n,"X block content")
            assert ny % q**3 == 0, (q,n,"Y block content")
            mod //= q**3
            exp -= 3
            X0 %= mod; X1 %= mod; Y0 %= mod; Y1 %= mod
            unit_fact %= mod
            nx = (nx//q**3) % mod
            ny = (ny//q**3) % mod
        X0, X1 = X1, nx
        Y0, Y1 = Y1, ny
        if m in wanted:
            target_mod = q**final_exp
            assert mod % target_mod == 0
            u3 = pow(unit_fact % target_mod, 3, target_mod)
            inv = pow(u3, -1, target_mod)
            out[m] = (X1*inv % target_mod, Y1*inv % target_mod)
    assert set(out) == wanted
    return out


base.high_regularized = high_dynamic
base.first_row()
base.audit()
