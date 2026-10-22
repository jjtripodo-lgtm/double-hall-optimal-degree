#!/usr/bin/env python3
"""Independent exact finite controls for the written Double Hall construction.

These finite controls do not prove the all-order theorem or replay Lean.
Only Python's standard library is needed. Acceptance survives python -O.
"""
from itertools import combinations, product
import json


def require(ok, why):
    if not ok:
        raise ValueError(why)


def transpose(rows, n):
    return [sum(1 << i for i, row in enumerate(rows) if row >> j & 1)
            for j in range(n)]


def check_both(rows):
    n = len(rows)
    checks = 0
    require(all(0 <= row < 1 << n for row in rows), 'simple balanced incidence')
    for cols in (transpose(rows, n), rows):
        for mask in range(1 << n):
            size = mask.bit_count()
            if size < 2:
                continue
            require(sum((col & mask).bit_count() >= 2 for col in cols) >= size,
                    'double Hall subset obstruction')
            checks += 1
    return checks


def duplicate(rows, selected):
    indices = list(range(len(rows))) + sorted(selected)
    return [sum(1 << j for j, oldj in enumerate(indices) if rows[oldi] >> oldj & 1)
            for oldi in indices]


def has_completion(rows, D):
    """Exhaust row choices, independently of the paper's sufficient cut bound."""
    n = len(rows)
    need = [D - col.bit_count() for col in transpose(rows, n)]

    def visit(i):
        if i == n:
            return not any(need)
        k = D - rows[i].bit_count()
        allowed = [j for j in range(n) if not (rows[i] >> j & 1) and need[j] > 0]
        for js in combinations(allowed, k):
            for j in js:
                need[j] -= 1
            ok = all(x <= n - i - 1 for x in need) and visit(i + 1)
            for j in js:
                need[j] += 1
            if ok:
                return True
        return False

    return visit(0)


def main():
    subset_checks = 0
    rook_cases = 0
    for m in (2, 3):
        cells = list(product(range(m), repeat=2))
        rows = [sum(1 << j for j, (c, d) in enumerate(cells) if a == c or b == d)
                for a, b in cells]
        require(all(row.bit_count() == 2 * m - 1 for row in rows), 'rook degree')
        if m == 2:
            selections = [{i for i in range(4) if mask >> i & 1} for mask in range(16)]
        else:
            order = [cells.index((i, i)) for i in range(m)] + [cells.index((i, (i+1) % m)) for i in range(m)]
            selections = [set(order[:t]) for t in (0, 1, 2, 4, 6)]
        for selected in selections:
            drows = duplicate(rows, selected)
            subset_checks += check_both(drows)
            expected = [2*m-1 + sum(rows[i] >> j & 1 for j in selected)
                        for i in list(range(m*m)) + sorted(selected)]
            require([row.bit_count() for row in drows] == expected, 'duplicate degree formula')
            rook_cases += 1

    semibiplane_cases = 0
    for q in (3, 5):
        vectors = [(a, b) for a, b in product(range(q), repeat=2) if a or b]
        canonical = lambda v: min(v, ((-v[0]) % q, (-v[1]) % q))
        reps = sorted({canonical(v) for v in vectors})
        n = len(reps)
        rows = [sum(1 << j for j, v in enumerate(reps)
                    if (u[0]*v[0] + u[1]*v[1]) % q in (1, q-1)) for u in reps]
        signs = [[1 if (u[0]*v[0]+u[1]*v[1]) % q == 1 else
                  -1 if (u[0]*v[0]+u[1]*v[1]) % q == q-1 else 0
                  for v in reps] for u in reps]
        require(all(row.bit_count() == q for row in rows), 'semibiplane degree')
        require(all(sum(a*b for a, b in zip(signs[i], signs[j])) == 0
                    for i in range(n) for j in range(i)), 'signed orthogonality')
        repaired = []
        for i, u in enumerate(reps):
            local = sum(1 << j for j, v in enumerate(reps)
                        if (u[0]*v[0] + u[1]*v[1]) % q == 0)
            require(not (rows[i] & local), 'empty class rectangles')
            repaired.append(rows[i] | local)
        require(all(row.bit_count() == q+(q-1)//2 for row in repaired), 'repair degree')
        subset_checks += check_both(repaired)
        semibiplane_cases += 1
        if q == 5:
            try:
                check_both(rows)
            except ValueError:
                pass
            else:
                raise ValueError('unrepaired base must fail positive-class control')

    eligible_completions = 0
    for n in range(1, 4):
        for mask in range(1 << (n*n)):
            rows = [(mask >> (n*i)) & ((1 << n)-1) for i in range(n)]
            degL = [row.bit_count() for row in rows]
            degR = [col.bit_count() for col in transpose(rows, n)]
            r, c = max(degL), max(degR)
            for D in range(max(r, c), n+1):
                alpha, beta = [D-d for d in degL], [D-d for d in degR]
                total, a, b = sum(alpha), max(alpha), max(beta)
                if total >= a*c+b*r+2*a*b:
                    require(has_completion(rows, D), 'eligible graph lacks regular completion')
                    eligible_completions += 1
    bad = [0] * 4
    try:
        check_both(bad)
    except ValueError:
        pass
    else:
        raise ValueError('edgeless corruption accepted')
    print(json.dumps({'status': 'PASS_FINITE_CONTROLS_ONLY', 'rook_duplication_cases': rook_cases,
                      'semibiplane_cases': semibiplane_cases, 'shore_subset_checks': subset_checks,
                      'eligible_small_completion_cases': eligible_completions,
                      'negative_controls': 2,
                      'scope': 'Finite controls; no unbounded theorem or fresh Lean claim'}, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
