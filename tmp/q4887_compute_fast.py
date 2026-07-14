from __future__ import annotations

from fractions import Fraction as FQ
from pathlib import Path
import sys

sys.path.insert(0, 'tmp')
import q4887_compute as b

# Tight, targeted search using the recurrence convention stated in Q4870/Q4887:
# A(n)u_{n+3}-B(n)u_{n+2}+C(n)u_{n+1}-D(n)u_n=0.
b.NTERMS = 220
b.MAX_R = 6
b.MAX_D_DIRECT = 24
b.MAX_D_RATIONAL = 12
b.MAX_REC_ORDER = 7
b.MAX_REC_DEG = 28
b.HOLDOUT = 35


def q_unshifted_exact(N):
    q = b.Q_INIT[:]
    for n in range(N-3):
        q.append((
            FQ(b.B27(n), b.A27(n))*q[n+2]
            - FQ(b.C27(n), b.A27(n))*q[n+1]
            + FQ(b.D27(n), b.A27(n))*q[n]
        ))
    return q[:N]


def q_unshifted_mod(p, N):
    q = [b.modfrac(x,p) for x in b.Q_INIT]
    for n in range(N-3):
        q.append((
            (b.B27(n)%p)*pow(b.A27(n)%p,-1,p)*q[n+2]
            - (b.C27(n)%p)*pow(b.A27(n)%p,-1,p)*q[n+1]
            + (b.D27(n)%p)*pow(b.A27(n)%p,-1,p)*q[n]
        )%p)
    return q


def all_mod_unshifted():
    out={}
    for p in b.PRIMES:
        W, _qrepo, h, _ = b.sequences_mod(p,b.NTERMS)
        q=q_unshifted_mod(p,b.NTERMS)
        qh=[q[n]*pow(h[n],-1,p)%p for n in range(b.NTERMS)]
        out[p]=(W,q,h,qh)
    return out


def report_direct(lines, all_mod, key, exact_target, Wex):
    cand=b.search_direct(all_mod,key)
    lines.append(f'## Direct polynomial map: {key}')
    if not cand:
        lines.append(f'No map found for r<={b.MAX_R}, degree<={b.MAX_D_DIRECT}.')
        lines.append('')
        return
    r,d,sols=cand[0]
    vec=b.reconstruct_vector(sols)
    lines.append(f'Candidate r={r}, d={d}; reconstruction={vec is not None}.')
    if vec is not None:
        ok,bad,res=b.verify_direct_exact(vec,Wex,exact_target,r,d)
        lines.append(f'Exact verification: {ok}; bad={bad}.')
        for j in range(r+1):
            lines.append(f'P_{j}(n) = {b.poly_to_str(vec[j*(d+1):(j+1)*(d+1)])}')
    lines.append('')


def report_rational(lines, all_mod, key, exact_target, Wex):
    cand=b.search_rational(all_mod,key)
    lines.append(f'## Rational map: {key}')
    if not cand:
        lines.append(f'No E(n) target=sum P_j W[n+j] found for r<={b.MAX_R}, degP,degE<={b.MAX_D_RATIONAL}.')
        lines.append('')
        return
    r,dp,de,norm,sols=cand[0]
    vec=b.reconstruct_vector(sols)
    lines.append(f'Candidate r={r}, dp={dp}, de={de}, norm={norm}; reconstruction={vec is not None}.')
    if vec is not None:
        ok,bad,res=b.verify_rational_exact(vec,Wex,exact_target,r,dp,de)
        lines.append(f'Exact verification: {ok}; bad={bad}.')
        for j in range(r+1):
            lines.append(f'P_{j}(n) = {b.poly_to_str(vec[j*(dp+1):(j+1)*(dp+1)])}')
        off=(r+1)*(dp+1)
        lines.append(f'E(n) = {b.poly_to_str(vec[off:off+de+1])}')
    lines.append('')


def main():
    lines=['# Q4887 targeted exact result','']
    lines.append('Convention: A_n q_{n+3}-B_n q_{n+2}+C_n q_{n+1}-D_n q_n=0.')
    lines.append('Primes: '+', '.join(map(str,b.PRIMES)))
    lines.append('')
    all_mod=all_mod_unshifted()
    Wex=b.W_terms_exact(b.NTERMS)
    qex=q_unshifted_exact(b.NTERMS)
    hex=b.hA_terms_exact(b.NTERMS)
    qhex=[qex[n]/hex[n] for n in range(b.NTERMS)]

    # The polynomial-only map is expected to fail by the half-integral exponent obstruction.
    report_direct(lines,all_mod,'q',qex,Wex)
    # Correctly twisted candidate h_n=(5/2)_n/n!.
    report_direct(lines,all_mod,'qh',qhex,Wex)
    report_rational(lines,all_mod,'qh',qhex,Wex)

    lines.append('## Minimal recurrence search for W')
    rec=b.search_recurrence(all_mod)
    if rec is None:
        lines.append(f'No recurrence found for order<={b.MAX_REC_ORDER}, degree<={b.MAX_REC_DEG}.')
    else:
        r,d,norm,sols=rec
        vec=b.reconstruct_vector(sols)
        lines.append(f'Candidate order={r}, degree={d}, norm={norm}; reconstruction={vec is not None}.')
        if vec is not None:
            ok,bad,res=b.verify_rec_exact(vec,Wex,r,d)
            lines.append(f'Exact verification: {ok}; bad={bad}.')
            for j in range(r+1):
                lines.append(f'L_{j}(n) = {b.poly_to_str(vec[j*(d+1):(j+1)*(d+1)])}')

    Path('tmp/q4887_result.md').write_text('\n'.join(lines)+'\n')
    print('\n'.join(lines))

if __name__=='__main__':
    main()
