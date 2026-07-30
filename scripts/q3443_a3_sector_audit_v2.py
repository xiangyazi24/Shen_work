#!/usr/bin/env python3
"""Corrected Q3443 audit: ambient n=M+3 and n<=10000."""
from __future__ import annotations

from collections import Counter
from math import gcd
import q3443_a3_sector_audit as A

N_LIMIT = 10_000
M_LIMIT = N_LIMIT - 3


def audit_targets(b, prime):
    target_scale_count = simultaneous_count = target_M_count = witt_rows = 0
    signs = Counter(); delta_gcd = 0
    zero_rows = []; negative_rows = []; all_rows = []
    first_negative = None; min_abs = None; lower = []
    padic = Counter(); padic_both_rows = []; padic_both2_rows = []

    for M in range(5, M_LIMIT + 1):
        n = M + 3
        targets = []
        for d in A.admissible_scales(M):
            q = d + 1
            if prime[q]:
                r = M - 3*d
                if b[r] % q == 0:
                    targets.append(d)
        target_scale_count += len(targets)
        if len(targets) < 2:
            continue
        target_M_count += 1
        rowM = A.binomial_row(M)
        data = {d: A.packet_data(M, d, b[M], rowM) for d in targets}
        witt_cache = {}
        for d in targets:
            q = d + 1; r = M - 3*d
            Cd = data[d][0]
            assert Cd % q == 0
            if r >= 3:
                witt_cache[d] = A.witt_digits(M, d, b)
                Ccheck, D1, D2, D3 = witt_cache[d]
                assert Ccheck == Cd
                assert Cd//q == b[r]//q + 3*D1 + 3*q*D2 + q*q*D3
                witt_rows += 1
            else:
                lower.append((n, M, q, r))

        for ix, d in enumerate(targets):
            q = d + 1; Cd, *Pd = data[d]; r = M - 3*d
            Td = Cd // q
            for e in targets[ix+1:]:
                ell = e + 1; Ce, *Pe = data[e]; s = M - 3*e
                Te = Ce // ell
                h = e-d
                assert h % 2 == 0 and r-s == 3*h
                center = h*b[M]
                pieces = [ell*Pd[k] - q*Pe[k] for k in range(3)]
                numerator = ell*Cd - q*Ce
                assert numerator == center + sum(pieces)
                assert numerator % (q*ell) == 0
                delta = numerator // (q*ell)

                simultaneous_count += 1
                signs[A.sign(delta)] += 1
                delta_gcd = gcd(delta_gcd, abs(delta))
                row = (n, M, q, ell, r, s, A.sign(delta),
                       abs(delta).bit_length(), A.digest(delta))
                all_rows.append(row)
                if delta == 0:
                    zero_rows.append((n, M, q, ell, r, s))
                if delta < 0:
                    negative_rows.append(row)
                    if first_negative is None:
                        first_negative = (n, M, d, e, q, ell, r, s,
                                          delta, center, *pieces)
                if min_abs is None or abs(delta) < min_abs[0]:
                    min_abs = (abs(delta), row)

                mq = (Td-Te) % q == 0
                ml = (Td-Te) % ell == 0
                mq2 = (Td-Te) % (q*q) == 0
                ml2 = (Td-Te) % (ell*ell) == 0
                padic['mod_q'] += mq
                padic['mod_ell'] += ml
                padic['both_mod_1'] += mq and ml
                padic['mod_q2'] += mq2
                padic['mod_ell2'] += ml2
                padic['both_mod_2'] += mq2 and ml2
                if mq and ml:
                    padic_both_rows.append(row)
                if mq2 and ml2:
                    padic_both2_rows.append(row)

    assert first_negative is not None
    assert first_negative[:8] == (743, 740, 196, 210, 197, 211, 152, 110), first_negative[:8]
    return dict(target_scale_count=target_scale_count,
                target_M_count=target_M_count,
                simultaneous_count=simultaneous_count,
                target_signs=dict(sorted(signs.items())),
                target_delta_gcd=delta_gcd,
                zero_rows=zero_rows,
                negative_rows=negative_rows,
                all_rows=all_rows,
                first_negative=first_negative,
                min_abs=min_abs,
                lower_residue_scales=sorted(set(lower)),
                witt_rows=witt_rows,
                padic_counts=dict(sorted(padic.items())),
                padic_both_rows=padic_both_rows,
                padic_both2_rows=padic_both2_rows)


def main():
    print('Q3443_A3_AUDIT_V2')
    counts = Counter(g for *_, g in A.VECTORS)
    print('PACKET_CARDINALITIES', counts)
    assert counts == Counter({1: 290, 2: 26, 3: 26})
    print('INDEPENDENT_SMALL_ROWS', A.direct_small_check())

    b = A.apery_values(M_LIMIT)
    prime = A.primes_upto(M_LIMIT//3 + 5)
    small = A.audit_small_range(b, prime)
    print('SMALL_RANGE_SUMMARY', {k:v for k,v in small.items()
          if k not in ('packet_signs','zero_rows','prime_zero_rows')})
    print('SMALL_PACKET_SIGN_PATTERNS', small['packet_signs'])
    print('SMALL_ZERO_ROWS', small['zero_rows'])
    print('SMALL_PRIME_ZERO_ROWS', small['prime_zero_rows'])
    f = small['first_negative']
    A.print_edge_report('FIRST_UNRESTRICTED_NEGATIVE', f[0], f[1], f[2])

    targets = audit_targets(b, prime)
    print('TARGET_SUMMARY', {k:v for k,v in targets.items()
          if k not in ('all_rows','negative_rows','first_negative','min_abs',
                       'padic_both_rows','padic_both2_rows')})
    print('TARGET_MIN_ABS', targets['min_abs'])
    print('TARGET_NEGATIVE_ROWS', targets['negative_rows'])
    print('PADIC_BOTH_MOD_1_ROWS', targets['padic_both_rows'])
    print('PADIC_BOTH_MOD_2_ROWS', targets['padic_both2_rows'])
    print('TARGET_ALL_ROWS')
    for row in targets['all_rows']:
        print(row)
    f = targets['first_negative']
    print('FIRST_TARGET_NEGATIVE_COMPACT', f[:8],
          'delta_bits', abs(f[8]).bit_length(),
          'delta_sha256', A.digest(f[8]))
    print('FIRST_TARGET_NEGATIVE_PACKET_NUMERATORS', f[9:])
    A.print_edge_report('FIRST_TARGET_NEGATIVE', f[1], f[2], f[3])
    print('ZERO_CONCLUSION_THROUGH_LIMIT',
          {'n_limit': N_LIMIT, 'M_limit': M_LIMIT, 'zeros':targets['zero_rows']})
    print('ALL_ASSERTIONS_PASSED', True)

if __name__ == '__main__':
    main()
