#!/usr/bin/env python3
"""
verify.py -- machine verification of every finite claim behind the bound

    liminf_{N->inf} log D(N) / log N  >=  alpha_inf = 0.753741541837329405...

D(N) is the largest size of a subset of {1,...,N} with no two elements
differing by a nonzero perfect square.

The script is self-contained: standard library only, all data inlined below,
no network, no files read or written.  Python >= 3.9.

Checks performed:

    1. arc sets     Q_m = {z^2 mod m : z in Z} \\ {0} rebuilt from the
                    definition for m = 235 and m = 299; sizes 71 and 83.
    2. certificates both supports are square-DAGs (acyclic under Q_m, by
                    Kahn's algorithm); the exhibited rank function on the
                    235-support drops strictly along every arc; the
                    longest-path heights are 11 and 12; the 299 ranking is
                    computed as longest-path layers and validated the same way.
    3. Paley chains all ten chains: p prime, p = 3 (mod 4), distinct entries,
                    every forward difference a nonzero quadratic residue mod p.
    4. constants    alpha_inf and Krachun's alpha_star recomputed from the
                    closed forms in 50-digit decimal arithmetic.
    5. --lift-demo  (optional flag) the smallest instance of Lemma A followed
                    by Lemma B for the 235-block (e = 1, L = 1): 3995 integers
                    in {1,...,235^2 * 11}, brute-checked square-difference-free.
                    An empirical witness of the two lemmas at the smallest
                    scale.  A demonstration, not the proof.

Usage:

    python verify.py
    python verify.py --lift-demo

Exit status is 0 if and only if every check printed "ok".
"""

import sys
import time
from decimal import Decimal, getcontext

getcontext().prec = 50

# ---------------------------------------------------------------------------
# Inlined data
# ---------------------------------------------------------------------------

# Composite block 1: m = 235 = 5 * 47 (square-free).
# The exhibited certificate: 17 vertices with the exhibited ranking, ranks 0..10.
SUPPORT_235 = {
    0: 10, 112: 10, 196: 9, 224: 9, 155: 8, 136: 7, 67: 6, 110: 6,
    92: 5, 189: 5, 126: 4, 193: 4, 22: 3, 50: 3, 64: 2, 73: 1, 148: 0,
}
HEIGHT_235 = 11
SIZE_235 = 17

# Composite block 2: m = 299 = 13 * 23 (square-free).
# The exhibited certificate: 19 vertices; the ranking is computed here as
# longest-path layers.
SUPPORT_299 = [
    7, 21, 25, 40, 46, 78, 83, 116, 153, 161,
    165, 206, 207, 210, 212, 244, 264, 289, 292,
]
HEIGHT_299 = 12
SIZE_299 = 19

# The ten Paley chains (p, chain).  p = 23 is used only for Krachun's constant:
# it is excluded from the pool of this note because 23 divides 299.
PALEY_CHAINS = [
    (3, (0, 1)),
    (7, (0, 4, 1)),
    (11, (0, 3, 1, 4)),
    (19, (0, 5, 11, 9, 16)),
    (23, (0, 18, 1, 3, 4)),
    (31, (0, 25, 14, 1, 19, 8, 2)),
    (43, (0, 31, 9, 23, 4, 40, 1)),
    (59, (0, 49, 15, 7, 16, 19, 35, 36, 5)),
    (71, (0, 8, 12, 18, 48, 27, 1, 37, 20)),
    (103, (0, 79, 25, 58, 55, 81, 4, 1, 34, 83, 59)),
]

# Expected chain lengths, tabled independently of the tuples above.
PALEY_LENGTHS = {3: 2, 7: 3, 11: 4, 19: 5, 23: 5, 31: 7, 43: 7, 59: 9, 71: 9, 103: 11}

# The pool of this note: nine Paley pairs (m, t, H) = (p, t, t), plus the two
# composite blocks with their exhibited certificate heights.
POOL = [
    (3, 2, 2), (7, 3, 3), (11, 4, 4), (19, 5, 5), (31, 7, 7),
    (43, 7, 7), (59, 9, 9), (71, 9, 9), (103, 11, 11),
    (235, 17, 11), (299, 19, 12),
]

# Krachun's pool: ten Paley pairs, height = length.
POOL_KRACHUN = [
    (3, 2, 2), (7, 3, 3), (11, 4, 4), (19, 5, 5), (23, 5, 5),
    (31, 7, 7), (43, 7, 7), (59, 9, 9), (71, 9, 9), (103, 11, 11),
]

ALPHA_INF_DIGITS = "0.75374154183732940"
ALPHA_INF_DOUBLE = 0.7537415418373294
ALPHA_STAR_DIGITS = "0.752796455874514"


# ---------------------------------------------------------------------------
# Reporting
# ---------------------------------------------------------------------------

FAILURES = []


def report(name, ok, detail=""):
    """Print one CHECK line and record failures."""
    status = "ok" if ok else "FAIL"
    line = "CHECK " + name + " ... " + status
    if detail:
        line = line + "  [" + detail + "]"
    print(line)
    if not ok:
        FAILURES.append(name)
    return ok


# ---------------------------------------------------------------------------
# Number theory helpers
# ---------------------------------------------------------------------------

def is_prime(n):
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def nonzero_squares_mod(m):
    """Q_m = {z^2 mod m : z in Z} minus {0}: the full image of squaring."""
    image = set()
    for z in range(m):
        image.add((z * z) % m)
    image.discard(0)
    return image


def unit_quadratic_residues(p):
    """Nonzero quadratic residues modulo a prime p."""
    return set((z * z) % p for z in range(1, p))


# ---------------------------------------------------------------------------
# Square-DAG helpers
# ---------------------------------------------------------------------------

def build_arcs(support, m, arcset):
    """Arcs x -> y for y - x in Q_m, over the given support."""
    arcs = {}
    for x in support:
        out = []
        for y in support:
            if y == x:
                continue
            if (y - x) % m in arcset:
                out.append(y)
        arcs[x] = out
    return arcs


def is_acyclic(support, arcs):
    """Kahn's algorithm: returns (acyclic, topological_order)."""
    indeg = dict((x, 0) for x in support)
    for x in support:
        for y in arcs[x]:
            indeg[y] += 1
    queue = [x for x in support if indeg[x] == 0]
    order = []
    while queue:
        x = queue.pop()
        order.append(x)
        for y in arcs[x]:
            indeg[y] -= 1
            if indeg[y] == 0:
                queue.append(y)
    return (len(order) == len(support), order)


def longest_path_rank(support, arcs, order):
    """Reversed longest-path rank: rank(x) = (longest path from x) - 1.

    Height of the DAG = max rank + 1 = longest directed path in vertices.
    """
    rank = dict((x, 0) for x in support)
    for x in reversed(order):
        best = 0
        for y in arcs[x]:
            if rank[y] + 1 > best:
                best = rank[y] + 1
        rank[x] = best
    return rank


def ranking_is_strict(arcs, rank):
    """h(x) > h(y) for every arc x -> y."""
    for x in arcs:
        for y in arcs[x]:
            if not rank[x] > rank[y]:
                return False
    return True


# ---------------------------------------------------------------------------
# Check 1: the arc sets
# ---------------------------------------------------------------------------

def check_arc_sets():
    q235 = nonzero_squares_mod(235)
    q299 = nonzero_squares_mod(299)
    ok1 = report("Q_235 rebuilt from definition, size 71", len(q235) == 71,
                 "size = " + str(len(q235)))
    ok2 = report("Q_299 rebuilt from definition, size 83", len(q299) == 83,
                 "size = " + str(len(q299)))
    # Cross-check against the CRT description for square-free modulus:
    # d is a square mod m iff d mod q is a square (possibly 0) mod q for q | m.
    ok3 = crt_cross_check(235, (5, 47), q235)
    ok4 = crt_cross_check(299, (13, 23), q299)
    # The full image contains non-unit squares; record how many.
    nonunit235 = sum(1 for d in q235 if d % 5 == 0 or d % 47 == 0)
    nonunit299 = sum(1 for d in q299 if d % 13 == 0 or d % 23 == 0)
    print("  note: Q_235 contains " + str(nonunit235) + " non-unit squares, "
          "Q_299 contains " + str(nonunit299) + " (they are arcs too)")
    return ok1 and ok2 and ok3 and ok4


def crt_cross_check(m, primes, arcset):
    per_prime = []
    for q in primes:
        squares = set((z * z) % q for z in range(q))  # includes 0
        per_prime.append(squares)
    built = set()
    for d in range(m):
        if all((d % q) in per_prime[i] for i, q in enumerate(primes)):
            built.add(d)
    built.discard(0)
    return report("Q_" + str(m) + " agrees with the CRT description",
                  built == arcset)


# ---------------------------------------------------------------------------
# Check 2: the two certificates
# ---------------------------------------------------------------------------

def check_certificate_235():
    m = 235
    support = sorted(SUPPORT_235)
    arcset = nonzero_squares_mod(m)
    ok = report("235-certificate has 17 distinct vertices",
                len(support) == SIZE_235 and len(set(support)) == SIZE_235,
                "size = " + str(len(support)))
    arcs = build_arcs(support, m, arcset)
    acyclic, order = is_acyclic(support, arcs)
    ok = report("235-support is a square-DAG (acyclic under Q_235)", acyclic) and ok
    if not acyclic:
        return False
    ok = report("235 exhibited ranking drops strictly along every arc",
                ranking_is_strict(arcs, SUPPORT_235)) and ok
    exhibited_height = max(SUPPORT_235.values()) + 1
    ok = report("235 exhibited ranking uses ranks 0..10",
                sorted(set(SUPPORT_235.values())) == list(range(11))
                and exhibited_height == HEIGHT_235,
                "height = " + str(exhibited_height)) and ok
    rank = longest_path_rank(support, arcs, order)
    height = max(rank.values()) + 1
    ok = report("235 longest-path height is 11", height == HEIGHT_235,
                "height = " + str(height)) and ok
    ok = report("235 longest-path ranking is itself a valid ranking",
                ranking_is_strict(arcs, rank)) and ok
    narcs = sum(len(v) for v in arcs.values())
    print("  note: the 235-block digraph has " + str(narcs) + " arcs on "
          + str(len(support)) + " vertices")
    return ok


def check_certificate_299():
    m = 299
    support = sorted(SUPPORT_299)
    arcset = nonzero_squares_mod(m)
    ok = report("299-certificate has 19 distinct vertices",
                len(support) == SIZE_299 and len(set(SUPPORT_299)) == SIZE_299,
                "size = " + str(len(support)))
    arcs = build_arcs(support, m, arcset)
    acyclic, order = is_acyclic(support, arcs)
    ok = report("299-support is a square-DAG (acyclic under Q_299)", acyclic) and ok
    if not acyclic:
        return False
    rank = longest_path_rank(support, arcs, order)
    height = max(rank.values()) + 1
    ok = report("299 longest-path height is 12", height == HEIGHT_299,
                "height = " + str(height)) and ok
    ok = report("299 computed ranking drops strictly along every arc",
                ranking_is_strict(arcs, rank)) and ok
    ok = report("299 computed ranking uses ranks 0..11",
                sorted(set(rank.values())) == list(range(12))) and ok
    narcs = sum(len(v) for v in arcs.values())
    print("  note: the 299-block digraph has " + str(narcs) + " arcs on "
          + str(len(support)) + " vertices")
    return ok


# ---------------------------------------------------------------------------
# Check 3: the Paley chains
# ---------------------------------------------------------------------------

def check_paley_chains():
    ok = True
    for p, chain in PALEY_CHAINS:
        residues = unit_quadratic_residues(p)
        good = True
        reason = ""
        if not is_prime(p):
            good, reason = False, "not prime"
        elif p % 4 != 3:
            good, reason = False, "p is not 3 mod 4"
        elif len(set(chain)) != len(chain):
            good, reason = False, "repeated entry"
        elif len(chain) != PALEY_LENGTHS[p]:
            good, reason = False, "length is not the tabled t"
        else:
            for a in range(len(chain)):
                for b in range(a + 1, len(chain)):
                    d = (chain[b] - chain[a]) % p
                    if d not in residues:
                        good = False
                        reason = ("difference s_" + str(b) + " - s_" + str(a)
                                  + " is not a nonzero QR")
                        break
                if not good:
                    break
        ok = report("Paley chain mod " + str(p) + ", t = "
                    + str(PALEY_LENGTHS[p]), good, reason) and ok
    return ok


# ---------------------------------------------------------------------------
# Check 4: the constants
# ---------------------------------------------------------------------------

def alpha_of_pool(pool):
    """alpha = [sum log(m t)/log H] / [1 + 2 sum log m / log H]."""
    num = Decimal(0)
    den = Decimal(1)
    for m, t, h in pool:
        if h < 2:
            raise ValueError("pool blocks must have H >= 2")
        log_h = Decimal(h).ln()
        num += (Decimal(m * t).ln()) / log_h
        den += 2 * (Decimal(m).ln()) / log_h
    return num / den


def alpha_finite(pool, u):
    """alpha(e(U)) for the allocation e_i = floor(U / log H_i), U real."""
    num = Decimal(0)
    den_logs = Decimal(0)
    height = Decimal(1)
    for m, t, h in pool:
        e = int(Decimal(u) / Decimal(h).ln())
        if e < 1:
            raise ValueError("U too small: some multiplicity is zero")
        num += Decimal(e) * Decimal(m * t).ln()
        den_logs += Decimal(e) * Decimal(m).ln()
        height += Decimal(h) ** e - 1
    return num / (2 * den_logs + height.ln())


def check_constants():
    alpha_inf = alpha_of_pool(POOL)
    alpha_star = alpha_of_pool(POOL_KRACHUN)
    s_inf = str(alpha_inf)
    s_star = str(alpha_star)
    print("  alpha_inf  = " + s_inf[:42] + "...")
    print("  alpha_star = " + s_star[:42] + "...  (Krachun, ten Paley pairs)")
    ok = report("alpha_inf begins " + ALPHA_INF_DIGITS,
                s_inf.startswith(ALPHA_INF_DIGITS), "got " + s_inf[:19])
    ok = report("alpha_inf rounds to the double 0.7537415418373294",
                float(alpha_inf) == ALPHA_INF_DOUBLE,
                repr(float(alpha_inf))) and ok
    ok = report("alpha_star begins " + ALPHA_STAR_DIGITS,
                s_star.startswith(ALPHA_STAR_DIGITS), "got " + s_star[:17]) and ok
    ok = report("alpha_inf exceeds alpha_star", alpha_inf > alpha_star,
                "gain " + str(alpha_inf - alpha_star)[:12]) and ok
    # Finite stages: each U certifies its own exponent unconditionally.
    stages = []
    rising = True
    previous = None
    for u in (5, 20, 80, 320):
        a = alpha_finite(POOL, u)
        stages.append("U=" + str(u) + ": "
                      + str(a.quantize(Decimal("0.000001"))))
        if previous is not None and not a > previous:
            rising = False
        if not a < alpha_inf:
            rising = False
        previous = a
    print("  finite stages, alpha(e(U)) = " + ", ".join(stages))
    ok = report("finite stages increase strictly towards alpha_inf from below",
                rising) and ok
    return ok


# ---------------------------------------------------------------------------
# Check 5 (optional): the lift demonstration
# ---------------------------------------------------------------------------

def lift_demo():
    """Lemma A at e = 1 then Lemma B at L = 1 for the 235-block.

    C = {x_0 + 235 x_1 : x_0 in S, 0 <= x_1 < 235} in Z/235^2 Z, of size
    17 * 235 = 3995, ranked by h(x) = h_0(x_0) with values in {0,...,10}.
    Lemma B at L = 1 turns it into A = {1 + x + 235^2 h(x)}, a subset of
    {1,...,235^2 * 11} of the same size, which is brute-checked here to be
    square-difference-free.

    This is an empirical witness of Lemmas A and B at the smallest scale.
    It is a demonstration, not the proof.
    """
    print("")
    print("--- lift demo (empirical witness of Lemmas A and B; not a proof) ---")
    m = 235
    P = m * m
    H = HEIGHT_235
    arcset = nonzero_squares_mod(m)

    # Lemma A, e = 1.
    block = {}
    for x0 in SUPPORT_235:
        for x1 in range(m):
            block[x0 + m * x1] = SUPPORT_235[x0]
    ok = report("lifted block C has (m t)^e = 3995 elements", len(block) == 3995,
                "size = " + str(len(block)))

    # Direct confirmation of the Lemma A conclusion on this instance: every
    # nonzero square difference inside C drops the rank.
    squares_modP = set((z * z) % P for z in range(P))
    squares_modP.discard(0)
    violations = 0
    keys = sorted(block)
    for x in keys:
        hx = block[x]
        for y in keys:
            if y == x:
                continue
            if (y - x) % P in squares_modP and not hx > block[y]:
                violations += 1
    ok = report("Lemma A conclusion holds on every square difference in C",
                violations == 0, str(violations) + " violations") and ok

    # Lemma B, L = 1.
    A = set(1 + x + P * block[x] for x in block)
    ok = report("integer set A has 3995 elements", len(A) == 3995,
                "size = " + str(len(A))) and ok
    top = P * H
    ok = report("A is contained in {1,...,235^2 * 11}",
                min(A) >= 1 and max(A) <= top,
                "min " + str(min(A)) + ", max " + str(max(A))) and ok

    # Brute-force square-difference-freeness.
    hi = max(A)
    bad = 0
    tested = 0
    for a in A:
        k = 1
        while a + k * k <= hi:
            tested += 1
            if (a + k * k) in A:
                bad += 1
            k += 1
    ok = report("A is square-difference-free (brute force)", bad == 0,
                str(tested) + " candidate square differences tested") and ok
    print("  note: arcs of Q_235 used above: " + str(len(arcset))
          + "; ambient interval size " + str(top))
    return ok


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main(argv):
    want_demo = "--lift-demo" in argv[1:]
    unknown = [a for a in argv[1:] if a != "--lift-demo"]
    if unknown:
        print("usage: python verify.py [--lift-demo]")
        return 2

    start = time.time()
    print("verify.py -- lower bound for the Furstenberg-Sarkozy problem")
    print("all data inlined; standard library only")
    print("")

    print("[1] arc sets")
    check_arc_sets()
    print("")
    print("[2] certificates")
    check_certificate_235()
    check_certificate_299()
    print("")
    print("[3] Paley chains")
    check_paley_chains()
    print("")
    print("[4] constants")
    check_constants()

    if want_demo:
        lift_demo()
    else:
        print("")
        print("(run with --lift-demo for the small-scale lift demonstration)")

    elapsed = time.time() - start
    print("")
    if FAILURES:
        print("RESULT: FAIL -- " + str(len(FAILURES)) + " check(s) failed:")
        for name in FAILURES:
            print("  - " + name)
        print("runtime: %.2f s" % elapsed)
        return 1
    print("RESULT: all checks ok")
    print("runtime: %.2f s" % elapsed)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
