#!/usr/bin/env python3
from __future__ import annotations

from fractions import Fraction
from math import isqrt

LIMIT = 1000
PREC = 12


def primes_upto(n: int) -> list[int]:
    s = bytearray(b"\x01") * (n + 1)
    s[:2] = b"\x00\x00"
    for p in range(2, isqrt(n) + 1):
        if s[p]:
            s[p*p:n+1:p] = b"\x00" * (((n-p*p)//p) + 1)
    return [p for p in range(2, n + 1) if s[p]]


def P(n: int) -> int:
    return 34*n**3 + 51*n**2 + 27*n + 5


def vp_int(x: int, q: int, cap: int | None = None) -> int:
    x %= q**cap if cap is not None else abs(x) + 1
    if x == 0:
        return cap if cap is not None else 10**9
    e = 0
    while x % q == 0:
        x //= q
        e += 1
    return e


def vp_fraction(x: Fraction, q: int) -> int:
    def v(z: int) -> int:
        z = abs(z); e = 0
        while z and z % q == 0:
            z //= q; e += 1
        return e
    return v(x.numerator) - v(x.denominator)


def exact_pair(nmax: int) -> tuple[list[int], list[Fraction]]:
    b = [1, 5]
    a = [Fraction(0), Fraction(6)]
    for n in range(1, nmax):
        bnum = P(n)*b[n] - n**3*b[n-1]
        den = (n+1)**3
        assert bnum % den == 0
        b.append(bnum // den)
        a.append((P(n)*a[n] - n**3*a[n-1]) / den)
    return b, a


def det(x: tuple[Fraction, int], y: tuple[Fraction, int]) -> Fraction:
    return x[0]*y[1] - y[0]*x[1]


def first_row() -> None:
    q, j, k = 5, 1, 2
    b, a = exact_pair(10)
    vm = (a[k-1], b[k-1])
    v = (a[k], b[k])
    wm = (q**3*a[k*q-1], b[k*q-1])
    w = (q**3*a[k*q], b[k*q])
    db = det(vm, v)
    dminus = det(wm, vm)
    dplus = det(w, v)
    cross_l = det(wm, v)
    cross_r = det(vm, w)
    alpha = cross_l / db
    gamma = -dminus / db
    beta = dplus / db
    delta = cross_r / db
    assert alpha*delta - beta*gamma == 1
    assert alpha*vm[1] + gamma*v[1] == wm[1]
    assert beta*vm[1] + delta*v[1] == w[1]

    cp = (b[k*q] - b[k]) // q**3
    cm = (b[k*q-1] - b[k-1]) // q**3
    lam = dminus / q**3
    bcal = b[k]*cm + b[k-1]*cp + q**3*cp*cm
    ecal = b[k]*b[k*q]*lam - Fraction(6, k**3)*bcal
    assert b[k-1]*b[k*q-1]*dplus == q**3*ecal

    x = alpha - 1
    y = delta - 1
    g = gamma / q**3
    assert b[k-1]*x + b[k]*q**3*g == q**3*cm
    assert b[k-1]*beta + b[k]*y == q**3*cp
    assert x + y + x*y - beta*q**3*g == 0
    assert b[k*q-1]*beta == b[k]*x + q**3*cp*(1+x)

    print("Q3292 FIRST ROW EXACT")
    print(f"b0..b10={b}")
    print(f"a0..a10={[str(x) for x in a]}")
    print(f"det_low={db}")
    print(f"Delta_1={q**3*a[q]*b[1]-a[1]*b[q]} v5={vp_fraction(q**3*a[q]*b[1]-a[1]*b[q],5)}")
    print(f"DeltaMinus_2={dminus} v5={vp_fraction(dminus,5)}")
    print(f"Delta_2={dplus} v5={vp_fraction(dplus,5)}")
    print(f"cross_left={cross_l} v5={vp_fraction(cross_l,5)}")
    print(f"cross_right={cross_r} v5={vp_fraction(cross_r,5)}")
    print(f"U=[[{alpha},{beta}],[{gamma},{delta}]] det=1")
    print(f"Cminus={cm} Cplus={cp} Bcal={bcal}")
    print(f"LambdaMinus={lam} Ecal={ecal} v5_Ecal={vp_fraction(ecal,5)}")
    print(f"x={x} y={y} g={g}")
    print("system1:", b[k-1], "*x +", b[k]*q**3, "*g =", q**3*cm)
    print("system2:", b[k-1], "*beta +", b[k], "*y =", q**3*cp)
    print("system3: x+y+x*y-", q**3, "*beta*g = 0")
    print("eliminated:", b[k*q-1], "*beta =", b[k], "*x +", q**3*cp, "*(1+x)")
    print(f"content_exponent={vp_fraction(Fraction(b[k-1]*b[k*q-1]),5)}")


def low_sequences(q: int, exponent: int) -> tuple[list[int], list[int]]:
    mod = q**exponent
    b = [1, 5 % mod]
    a = [0, 6 % mod]
    for n in range(1, q-1):
        den = (n+1)**3
        inv = pow(den, -1, mod)
        b.append((P(n)*b[n] - n**3*b[n-1]) * inv % mod)
        a.append((P(n)*a[n] - n**3*a[n-1]) * inv % mod)
    return b, a


def high_regularized(q: int, maxk: int, wanted: set[int], final_exp: int) -> dict[int, tuple[int, int]]:
    exp = final_exp + 3*maxk
    mod = q**exp
    b0, b1 = 1 % mod, 5 % mod
    A0, A1 = 0, (6*q**3) % mod
    out: dict[int, tuple[int, int]] = {}
    if 0 in wanted: out[0] = (b0, A0)
    if 1 in wanted: out[1] = (b1, A1)
    limit = maxk*q
    for n in range(1, limit):
        nb = P(n)*b1 - n**3*b0
        nA = P(n)*A1 - n**3*A0
        m = n + 1
        if m % q:
            den = m**3
            inv = pow(den, -1, mod)
            b2 = nb * inv % mod
            A2 = nA * inv % mod
        else:
            unit = (m//q)**3
            inv = pow(unit, -1, mod)
            zb = nb * inv % mod
            zA = nA * inv % mod
            assert zb % q**3 == 0, (q, n, "b singular division")
            assert zA % q**3 == 0, (q, n, "a singular division")
            mod //= q**3
            exp -= 3
            b0 %= mod; b1 %= mod; A0 %= mod; A1 %= mod
            b2 = (zb // q**3) % mod
            A2 = (zA // q**3) % mod
        b0, b1 = b1, b2
        A0, A1 = A1, A2
        if m in wanted:
            target_mod = q**final_exp
            assert mod % target_mod == 0
            out[m] = (b1 % target_mod, A1 % target_mod)
    assert set(out) == wanted
    return out


def qdiv(residue: int, q: int, power: int, exponent: int) -> tuple[int, int]:
    mod = q**exponent
    z = residue % mod
    assert z % q**power == 0
    return (z // q**power) % (q**(exponent-power)), exponent-power


def audit() -> None:
    rows = []
    first_failure = None
    primes = [q for q in primes_upto(LIMIT-1) if q >= 5]
    folded_count = 0
    full_count = 0
    for q in primes:
        bq, aq = low_sequences(q, PREC)
        half = (q-1)//2
        folded = [r for r in range(1, half+1) if bq[r] % q == 0]
        folded_count += len(folded)
        zeros = [r for r in range(1, q-1) if bq[r] % q == 0]
        if not zeros:
            continue
        full_count += len(zeros)
        ks = sorted({r+1 for r in zeros})
        maxk = max(ks)
        wanted = {k*q for k in ks} | {k*q-1 for k in ks}
        high = high_regularized(q, maxk, wanted, PREC)
        mod = q**PREC
        small_mod = q**(PREC-3)
        for r in zeros:
            k = r+1
            bn, An = high[k*q]
            bm, Am = high[k*q-1]
            bk, ak = bq[k], aq[k]
            br, ar = bq[r], aq[r]
            D = (An*bk - ak*bn) % mod
            Dm = (Am*br - ar*bm) % mod
            vd = vp_int(D, q, PREC)
            vdm = vp_int(Dm, q, PREC)
            vb = vp_int(br, q, PREC)
            vbm = vp_int(bm, q, PREC)
            content = vb + vbm

            Cp, _ = qdiv((bn-bk) % mod, q, 3, PREC)
            Cm, _ = qdiv((bm-br) % mod, q, 3, PREC)
            Lam, _ = qdiv(Dm, q, 3, PREC)
            Cp %= small_mod; Cm %= small_mod; Lam %= small_mod
            bcal = (bk*Cm + br*Cp + q**3*Cp*Cm) % small_mod
            factor = 6 * pow(k**3, -1, small_mod) % small_mod
            ecal = (bk*bn*Lam - factor*bcal) % small_mod
            ve = vp_int(ecal, q, PREC-3)
            if vd < PREC and ve < PREC-3:
                assert vd == 3-content+ve, (q,r,k,vd,content,ve)
            sigma = None
            if vb == 1:
                assert ve >= 1
                sigma = (ecal//q) % q
            branch = "C" if r == half else ("D" if r < half else "R")
            row = (q,r,k,branch,vd,vdm,content,ve,sigma)
            rows.append(row)
            if vd < 3 and first_failure is None:
                first_failure = row

    print("Q3292 SUCCESSOR AUDIT")
    print(f"prime_limit_exclusive={LIMIT}")
    print(f"precision_q_adic_digits={PREC}")
    print(f"folded_bottom_zero_count={folded_count}")
    print(f"full_zero_digit_successor_count={full_count}")
    print(f"successor_rows={len(rows)}")
    print("columns: q r k branch vDelta vDeltaMinus contentExponent vEcal sigma(simple)")
    for row in rows:
        print(*row)
    print(f"first_failure={first_failure}")
    print(f"rows_with_vDelta_below_3={sum(1 for row in rows if row[4] < 3)}")
    print(f"rows_with_vDelta_exactly_3={sum(1 for row in rows if row[4] == 3)}")
    print(f"rows_with_vDelta_above_3={sum(1 for row in rows if row[4] > 3)}")
    print(f"simple_rows_with_sigma_nonzero={sum(1 for row in rows if row[8] not in (None,0))}")


if __name__ == "__main__":
    first_row()
    audit()
