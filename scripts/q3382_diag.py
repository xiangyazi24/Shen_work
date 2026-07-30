#!/usr/bin/env python3
from __future__ import annotations
import sys
sys.path.insert(0, 'zinan-memory/working_notes/scripts_q32_audit')
import q3289_collision_second_digit_audit as trusted

rows, counts = trusted.collect_collision_rows(30000)
print('COUNTS', dict(counts))
print('Q37_ROWS')
for row in rows:
    if int(row['q']) == 37 or (int(row['J']) == 20 and tuple(row['roots']) == (16,20)):
        print(row)
print('TOTAL_ROWS', len(rows))
