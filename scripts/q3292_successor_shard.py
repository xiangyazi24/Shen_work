#!/usr/bin/env python3
from __future__ import annotations

import sys
import q3292_successor_audit as base

PREC = 12


def high_dynamic(q: int, maxk: int, wanted: set[int], final_exp: int):
    exp = final_exp + 3*maxk
    mod = q**exp
    X0, X1 = 1, 5
    Y0, Y1 = 0, 6*q**3
    unit_fact = 1
    out = {}
    for n in range(1, maxk*q):
        m = n + 1
        second = n**6 // (q**3 if n % q == 0 else 1)
        nx = (base.P(n)*X1 - second*X0) % mod
        ny = (base.P(n)*Y1 - second*Y0) % mod
        t = m
        while t % q == 0:
            t //= q
        unit_fact = unit_fact*t % mod
        if m % q == 0:
            assert nx % q**3 == 0, (q,n,"X content")
            assert ny % q**3 == 0, (q,n,"Y content")
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
            u3 = pow(unit_fact % target_mod, 3, target_mod)
            inv = pow(u3, -1, target_mod)
            out[m] = (X1*inv % target_mod, Y1*inv % target_mod)
    assert set(out) == wanted
    return out


def run(lo: int, hi: int) -> None:
    rows = []
    folded_count = 0
    first_failure = None
    for q in base.primes_upto(999):
        if q < max(5,lo) or q >= hi:
            continue
        bq, aq = base.low_sequences(q, PREC)
        half = (q-1)//2
        folded = [r for r in range(1,half+1) if bq[r] % q == 0]
        folded_count += len(folded)
        zeros = [r for r in range(1,q-1) if bq[r] % q == 0]
        if not zeros:
            continue
        ks = sorted({r+1 for r in zeros})
        wanted = {k*q for k in ks} | {k*q-1 for k in ks}
        high = high_dynamic(q, max(ks), wanted, PREC)
        mod = q**PREC
        small_mod = q**(PREC-3)
        for r in zeros:
            k = r+1
            bn, An = high[k*q]
            bm, Am = high[k*q-1]
            bk, ak = bq[k], aq[k]
            br, ar = bq[r], aq[r]
            D = (An*bk-ak*bn) % mod
            Dm = (Am*br-ar*bm) % mod
            vd = base.vp_int(D,q,PREC)
            vdm = base.vp_int(Dm,q,PREC)
            vb = base.vp_int(br,q,PREC)
            vbm = base.vp_int(bm,q,PREC)
            content = vb+vbm
            Cp,_ = base.qdiv((bn-bk)%mod,q,3,PREC)
            Cm,_ = base.qdiv((bm-br)%mod,q,3,PREC)
            Lam,_ = base.qdiv(Dm,q,3,PREC)
            Cp %= small_mod; Cm %= small_mod; Lam %= small_mod
            bcal = (bk*Cm+br*Cp+q**3*Cp*Cm) % small_mod
            factor = 6*pow(k**3,-1,small_mod) % small_mod
            ecal = (bk*bn*Lam-factor*bcal) % small_mod
            ve = base.vp_int(ecal,q,PREC-3)
            if vd < PREC and ve < PREC-3:
                assert vd == 3-content+ve, (q,r,k,vd,content,ve)
            sigma = "NA"
            if vb == 1:
                sigma = (ecal//q)%q if ve >= 1 else f"lead:{ecal%q}"
            branch = "C" if r == half else ("D" if r < half else "R")
            row = (q,r,k,branch,vd,vdm,content,ve,sigma)
            rows.append(row)
            if vd < 3 and first_failure is None:
                first_failure = row
    print(f"Q3292 SHARD lo={lo} hi={hi}")
    print(f"folded_bottom_zero_count={folded_count}")
    print(f"successor_rows={len(rows)}")
    print("columns: q r k branch vDelta vDeltaMinus contentExponent vEcal sigma")
    for row in rows:
        print(*row)
    print(f"first_failure={first_failure}")
    print(f"below3={sum(row[4]<3 for row in rows)}")
    print(f"equal3={sum(row[4]==3 for row in rows)}")
    print(f"above3={sum(row[4]>3 for row in rows)}")


if __name__ == "__main__":
    run(int(sys.argv[1]), int(sys.argv[2]))
