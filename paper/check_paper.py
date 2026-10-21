"""Exact replay of every number and finite identity printed in the paper.

Standard library only (fractions).  Run:  python check_paper.py
Ends with a JSON line containing "status": "PASS".

This script is a consistency check of the printed arithmetic and of the
literal emitter on small inputs.  It is not a proof of the general theorems;
those are the conventional proofs in the paper and the Lean declarations
listed in its verification section.
"""
from fractions import Fraction as F
from itertools import product
import json
import random

checks = []


def ok(name, cond):
    if not cond:
        raise AssertionError(name)
    checks.append(name)


# ---------------------------------------------------------------------------
# 1. Literal emitter (the construction of Sections 3-4), exact arithmetic.
# ---------------------------------------------------------------------------

def split(terms):
    """Uniform split: g = sum c u^gamma  ->  (P, Q) coefficient lists."""
    P = [(abs(c) + 1, g) for c, g in terms]
    Q = [(c + abs(c) + 1, g) for c, g in terms]
    return P, Q


def monomial(u, gamma):
    r = F(1)
    for x, e in zip(u, gamma):
        r *= F(x) ** e
    return r


def evalp(terms, u):
    return sum((F(c) * monomial(u, g) for c, g in terms), F(0))


def boxed_offset(terms):
    return 1 + sum((c + abs(c) + 1) * F(2) ** sum(g) for c, g in terms)


def emit(terms, d, K=None):
    """Return (species, reactions, left motif, right motif).

    reactions: list of (name, reactant dict, product dict, factor).
    Boxed variant if K is a number (offset edge unpadded, factor 1/K, 2/K);
    unboxed variant if K is None (offset padded by Z0, factors 1 and 2).
    """
    P, Q = split(terms)
    N = len(terms)
    ext = [f"Z{e+1}" for e in range(d)] + ([] if K is not None else ["Z0"])
    reactions = []
    motifs = {}
    for side, coeffs, half in (("L", P, False), ("R", Q, True)):
        verts = ["A", "B"] + [f"{side}{i}" for i in range(1, N + 1)]
        names = []
        # common channel A <-> B, factor 1
        reactions.append((f"r0{side}", {"A": 1}, {"B": 1}, F(1)))
        names.append(f"r0{side}")
        # offset edge then one edge per term
        edges = [("offset", None)] + list(coeffs)
        for i, (a, gamma) in enumerate(edges):
            tail = verts[i + 1]
            head_is_gain = (i == N)
            pad = {}
            if a == "offset":
                if K is None:
                    pad = {"Z0": 1}
                    base = F(1)
                else:
                    base = F(K)
            else:
                base = F(a)
                for e, g in enumerate(gamma):
                    if g:
                        pad[f"Z{e+1}"] = g
            coef = base / 2 if half else base
            factor = 1 / coef
            react = {tail: 1}
            prod = {"A": 2} if head_is_gain else {verts[i + 2]: 1}
            for s, k in pad.items():
                react[s] = react.get(s, 0) + k
                prod[s] = prod.get(s, 0) + k
            nm = f"r{i+1}{side}"
            reactions.append((nm, react, prod, factor))
            names.append(nm)
        motifs[side] = (verts, names)
    species = ["A", "B"] + [f"L{i}" for i in range(1, N + 1)] + \
        [f"R{i}" for i in range(1, N + 1)] + ext
    return species, reactions, motifs["L"], motifs["R"]


def current(rxn, z):
    _, a, b, f = rxn
    ma = F(1)
    for s, k in a.items():
        ma *= z[s] ** k
    mb = F(1)
    for s, k in b.items():
        mb *= z[s] ** k
    return f * (ma - mb)


def stoich(rxn, s):
    _, a, b, _ = rxn
    return b.get(s, 0) - a.get(s, 0)


def productions(species_list, rxn_names, reactions, J):
    idx = {r[0]: i for i, r in enumerate(reactions)}
    return [sum(stoich(reactions[idx[r]], s) * J[idx[r]] for r in rxn_names)
            for s in species_list]


def resistances(terms, u, K):
    """R_L = K + P(u), R_R = (K + Q(u))/2, u = polynomial variables."""
    P, Q = split(terms)
    return K + evalp(P, u), (K + evalp(Q, u)) / 2


def reconstruct_path(weights, q):
    """Lemma (response and reconstruction): returns A, B, path activities,
    normalized currents t_i."""
    m = len(weights)
    R = sum(weights)
    assert R / 2 < q < R
    theta = q / R
    c = [m + 1 - 2 * i for i in range(1, m + 1)]
    cbar = sum(w * ci for w, ci in zip(weights, c)) / R
    delta = min(theta - F(1, 2), 1 - theta)
    eps = delta / (4 * m)
    t = [theta + eps * (ci - cbar) for ci in c]
    A = F(1, 2)
    B = (F(1, 4) + q / 2) / (1 + q)
    j0 = A - B
    x = [B]
    for w, ti in zip(weights, t):
        x.append(x[-1] - j0 * w * ti)
    assert x[-1] == A * A
    return A, B, x, t


def branch_weights(terms, u, K, side):
    P, Q = split(terms)
    if side == "L":
        return [F(K)] + [F(a) * monomial(u, g) for a, g in P]
    return [F(K) / 2] + [F(a) / 2 * monomial(u, g) for a, g in Q]


def build_state(terms, u, K, species, left, right, unboxed=False):
    RL, RR = resistances(terms, u, K)
    lo, hi = max(RL / 2, RR / 2), min(RL, RR)
    assert lo < hi
    q = (lo + hi) / 2
    z = {}
    for e, x in enumerate(u):
        z[f"Z{e+1}"] = 1 / F(x)
    if unboxed:
        z["Z0"] = 1 / F(K)
    for side, (verts, _) in (("L", left), ("R", right)):
        w = branch_weights(terms, u, K, side)
        A, B, x, t = reconstruct_path(w, q)
        z["A"], z["B"] = A, B
        for i, v in enumerate(verts[2:], start=1):
            z[v] = x[i]
    return z


def check_instance(terms, d, u, boxed=True):
    if boxed:
        K = boxed_offset(terms)
        species, rx, left, right = emit(terms, d, K)
    else:
        P, Q = split(terms)
        K = 1 + evalp(Q, u)
        species, rx, left, right = emit(terms, d, None)
    z = build_state(terms, u, K, species, left, right, unboxed=not boxed)
    J = [current(r, z) for r in rx]
    assert all(j > 0 for j in J)
    pl = productions(left[0], left[1], rx, J)
    pr = productions(right[0], right[1], rx, J)
    assert all(p > 0 for p in pl + pr)
    if boxed:
        internal = left[0] + right[0][2:]
        assert all(F(1, 4) <= z[s] <= F(1, 2) for s in internal)
        assert all(F(1, 2) <= z[s] <= 1 for s in species if s.startswith("Z"))
    # union production: internal > 0, external = 0
    un = productions(species, [r[0] for r in rx], rx, J)
    for s, p in zip(species, un):
        assert (p == 0) if s.startswith("Z") else (p > 0)
    # side molecularity and factor bound
    mol = max(max(sum(r[1].values()), sum(r[2].values())) for r in rx)
    assert all(0 < r[3] <= 2 for r in rx)
    return mol, len(rx), len(species)


# ---------------------------------------------------------------------------
# 2. The worked example of Section 7.
# ---------------------------------------------------------------------------
terms = [(2, (1,)), (-1, (2,))]           # g(u) = 2u - u^2
P, Q = split(terms)
ok("example split P", P == [(3, (1,)), (2, (2,))])
ok("example split Q", Q == [(5, (1,)), (1, (2,))])
K = boxed_offset(terms)
ok("example offset K=15", K == 15)
u = (F(3, 2),)
RL, RR = resistances(terms, u, K)
ok("example R_L=24", RL == 24)
ok("example R_R=99/8", RR == F(99, 8))
ok("example g(3/2)=3/4", evalp(terms, u) == F(3, 4))

species, rx, left, right = emit(terms, 1, K)
ok("example 8 reactions", len(rx) == 8)
ok("example factors",
   [r[3] for r in rx] == [1, F(1, 15), F(1, 3), F(1, 2), 1, F(2, 15), F(2, 5), 2])

A, B, Z = F(1, 2), F(2209, 4591), F(2, 3)
L1, L2 = F(3083, 9182), F(2687, 9182)
R1, R2 = F(1564, 4591), F(9947, 36728)
z = {"A": A, "B": B, "L1": L1, "L2": L2, "R1": R1, "R2": R2, "Z1": Z}
J = [current(r, z) for r in rx]
ok("example currents", J == [F(x, 9182) for x in (173, 89, 88, 87, 173, 172, 171, 170)])
pl = productions(left[0], left[1], rx, J)
pr = productions(right[0], right[1], rx, J)
ok("example left productions", pl == [F(x, 9182) for x in (1, 84, 1, 1)])
ok("example right productions", pr == [F(x, 9182) for x in (167, 1, 1, 1)])
ok("example boxes", all(F(1, 4) <= v <= F(1, 2) for v in (A, B, L1, L2, R1, R2)))
un = productions(["A", "B", "L1", "L2", "R1", "R2", "Z1"], [r[0] for r in rx], rx, J)
ok("example union productions", un == [F(x, 9182) for x in (168, 85, 1, 1, 1, 1, 0)])
ok("example total 257", sum(un) == J[3] + J[7] == F(257, 9182))
# q of the displayed state and its position in both intervals
qex = (B - A * A) / (A - B)
ok("example q=4245/346", qex == F(4245, 346))
ok("example q in both intervals", max(RL, RR) / 2 < qex < min(RL, RR))
# tangency at u=2 and a separated point
RL2, RR2 = resistances(terms, (F(2),), K)
ok("tangency u=2", (RL2, RR2) == (29, F(29, 2)) and evalp(terms, (F(2),)) == 0)
ok("tangency incompatible", not (RL2 < 2 * RR2 and RR2 < 2 * RL2))
# normalized margin of the displayed state
den = []
for names in (left[1], right[1]):
    pass
m_left = min(pl) / J[0]
ok("example min production 1/9182", min(pl + pr) == F(1, 9182))
# merged common channel: per-core productions unchanged, union B negative
jB_merged = J[0] - J[1] - J[5]
ok("merged union B negative", jB_merged == F(173 - 89 - 172, 9182) and jB_merged < 0)

# conservative food realization: currents scale by phi^2
def food_version(rx):
    out = []
    for nm, a, b, f in rx:
        a2, b2 = dict(a), dict(b)
        a2["F"] = a2.get("F", 0) + 1
        if b.get("A", 0) != 2:           # ordinary edge: F on both sides
            b2["F"] = b2.get("F", 0) + 1
        out.append((nm, a2, b2, f))
    return out


frx = food_version(rx)
for phi in (F(1), F(3, 2), F(7, 5)):
    zf = {s: (phi * v if s in ("A", "B", "L1", "L2", "R1", "R2") else v) for s, v in z.items()}
    zf["F"] = phi
    Jf = [current(r, zf) for r in frx]
    ok(f"food scaling phi={phi}", Jf == [phi * phi * j for j in J])
# mass conservation: internal and F mass 1, spectator arbitrary
for nm, a, b, f in frx:
    mass = lambda c: sum(k * (0 if s.startswith("Z") else 1) for s, k in c.items())
    ok(f"food mass {nm}", mass(a) == mass(b))
ok("food molecularity D+2=4 in example", max(max(sum(r[1].values()), sum(r[2].values())) for r in frx) == 4)
food_use = J[3] + J[7]
ok("food consumption 257/9182", food_use == F(257, 9182))

# ---------------------------------------------------------------------------
# 3. Signed minimality weights (Lemma 3.1): weights 1 up to the cut, 2 after.
# ---------------------------------------------------------------------------
for m in range(1, 9):
    k_edges = m + 1                 # edges e_0 .. e_m, vertices v_0 .. v_m
    for cut in range(k_edges):
        w = [1 if i <= cut else 2 for i in range(k_edges)]
        for i in range(k_edges):
            if i == cut:
                continue
            gain = 2 if i == m else 1
            head = (i + 1) % k_edges
            ok(f"cut weights m={m} cut={cut} edge={i}", gain * w[head] == w[i])
    # productivity witness j_i = 1 - i/(2(m+1))
    j = [1 - F(i, 2 * (m + 1)) for i in range(m + 1)]
    prods = [2 * j[m] - j[0]] + [j[i - 1] - j[i] for i in range(1, m + 1)]
    ok(f"productive witness m={m}", all(p > 0 for p in prods))

# ---------------------------------------------------------------------------
# 4. Response lemma: random exact reconstructions.
# ---------------------------------------------------------------------------
rng = random.Random(20260927)
for trial in range(200):
    m = rng.randint(1, 7)
    w = [F(rng.randint(1, 40), rng.randint(1, 9)) for _ in range(m)]
    R = sum(w)
    q = R / 2 + (R / 2) * F(rng.randint(1, 99), 100)
    A_, B_, x, t = reconstruct_path(w, q)
    ok(f"reconstruct t in (1/2,1) #{trial}", all(F(1, 2) < ti < 1 for ti in t))
    ok(f"reconstruct t decreasing #{trial}", all(t[i] > t[i + 1] for i in range(m - 1)))
    ok(f"reconstruct sum #{trial}", sum(wi * ti for wi, ti in zip(w, t)) == q)
    ok(f"reconstruct box #{trial}", all(F(1, 4) <= xi <= F(1, 2) for xi in x[:-1]) and x[-1] == F(1, 4))

# ---------------------------------------------------------------------------
# 5. Literal emitter on random small polynomials, both variants.
# ---------------------------------------------------------------------------
n_inst = 0
for trial in range(60):
    d = rng.randint(1, 3)
    N = rng.randint(0, 5)
    tms = []
    for _ in range(N):
        gamma = tuple(rng.randint(0, 2) for _ in range(d))
        tms.append((F(rng.randint(-6, 6), rng.randint(1, 3)), gamma))
    # search a grid point with g > 0
    grid = [F(1) + F(k, 4) for k in range(5)]
    pts = [p for p in product(grid, repeat=d) if evalp(tms, p) > 0]
    Kb = boxed_offset(tms)
    for p in pts[:2]:
        mol, nr, ns = check_instance(tms, d, p, boxed=True)
        ok(f"boxed instance #{trial} size", nr == 2 * N + 4 and ns == 2 * N + 2 + d)
        ok(f"boxed instance #{trial} molecularity", mol <= max(2, 2 + max((sum(g) for _, g in tms), default=0)))
        n_inst += 1
    # soundness spot check: points with g <= 0 give non-overlapping intervals
    for p in product(grid, repeat=d):
        RLp, RRp = resistances(tms, p, Kb)
        ok(f"comparator #{trial}", (RLp < 2 * RRp and RRp < 2 * RLp) == (evalp(tms, p) > 0))
    # unboxed: any positive point
    for p in [tuple(F(rng.randint(1, 30), rng.randint(1, 10)) for _ in range(d)) for _ in range(3)]:
        if evalp(tms, p) > 0:
            mol, nr, ns = check_instance(tms, d, p, boxed=False)
            ok(f"unboxed instance #{trial} size", nr == 2 * N + 4 and ns == 2 * N + 3 + d)
            n_inst += 1
ok("emitter exercised", n_inst >= 30)

# Empty polynomial: two valid but incompatible cycles (R_L = K, R_R = K/2).
RLe, RRe = resistances([], (), F(1))
ok("empty polynomial tangency", RLe == 1 and RRe == F(1, 2) and not (RLe < 2 * RRe))

# Expansion bound: (2u-3)^gamma expands into prod(gamma_e+1) <= 2^|gamma| terms.
for gamma in product(range(5), repeat=2):
    if sum(gamma) <= 4:
        ok(f"expansion bound {gamma}", (gamma[0] + 1) * (gamma[1] + 1) <= 2 ** sum(gamma))

# ---------------------------------------------------------------------------
# 6. Precision family (Proposition 6.4).
# ---------------------------------------------------------------------------
for n in range(1, 8):
    v = [F(1, 2 ** (3 * 2 ** (i - 1) - 1)) for i in range(1, n + 1)]
    ok(f"precision v1<1/2 n={n}", v[0] < F(1, 2))
    ok(f"precision squaring n={n}", all(v[i + 1] < v[i] ** 2 for i in range(n - 1)))
    ok(f"precision vn bound n={n}", 0 < v[-1] < F(1, 2 ** (2 ** (n - 1))))
    uu = [1 + vi for vi in v]
    mods = [[(F(3, 2), (0,) * n), (F(-1), tuple(1 if k == 0 else 0 for k in range(n)))]]
    for i in range(n - 1):
        e_i = tuple(2 if k == i else 0 for k in range(n))
        l_i = tuple(1 if k == i else 0 for k in range(n))
        l_j = tuple(1 if k == i + 1 else 0 for k in range(n))
        mods.append([(F(1), e_i), (F(-2), l_i), (F(-1), l_j), (F(2), (0,) * n)])
    mods.append([(F(1), tuple(1 if k == n - 1 else 0 for k in range(n))), (F(-1), (0,) * n)])
    ok(f"precision modules positive n={n}", all(evalp(g, uu) > 0 for g in mods))
    Ks = [boxed_offset(g) for g in mods]
    if n >= 2:
        ok(f"precision squaring offset 22 n={n}", Ks[1] == 22)
    ok(f"precision factor bound n={n}",
       all(0 < f <= 2 for g in mods for f in
           [1 / boxed_offset(g), 2 / boxed_offset(g)] +
           [1 / (abs(c) + 1) for c, _ in g] + [2 / (c + abs(c) + 1) for c, _ in g]))
    z_last = 1 / uu[-1]
    ok(f"precision 1-z bound n={n}", 0 < 1 - z_last < F(1, 2 ** (2 ** (n - 1))))
    ok(f"precision denominator n={n}", z_last.denominator > 2 ** (2 ** (n - 1)))

print(json.dumps({"checks": len(checks), "emitter_instances": n_inst, "status": "PASS"}))
