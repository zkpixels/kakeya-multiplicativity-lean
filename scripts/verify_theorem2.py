import itertools

# ---------------------------------------------------------------
# Verification of the finite steps in the proof of Theorem 2:
#   every S subset of F_3^3 contains full lines in at most |S|
#   direction classes.
# The structural argument (pencil bound + incidence count +
# pigeonhole + affine normalization) reduces the statement to the
# finite checks below.  This script performs exactly those checks.
# ---------------------------------------------------------------

P = list(itertools.product(range(3), repeat=3))

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

# Canonical direction-class representatives: nonzero vectors whose
# first nonzero coordinate is 1.  There are (27-1)/2 = 13 classes.
reps = [
    v for v in P[1:]
    if v[next(i for i, c in enumerate(v) if c)] == 1
]
require(len(reps) == 13, "wrong number of direction classes")

def add(a, b):
    return tuple((a[i] + b[i]) % 3 for i in range(3))

def line(a, d):
    return frozenset({a, add(a, d), add(a, add(d, d))})

def class_count(S):
    """Number of direction classes with a full line inside S."""
    S = set(S)
    count = 0
    for d in reps:
        if any(line(p, d) <= S for p in S):
            count += 1
    return count

E = [(1,0,0), (0,1,0), (0,0,1)]
ZERO = (0,0,0)

def line0(d):
    return line(ZERO, d)

# ---------------------------------------------------------------
# Check 1 (case B geometry): four concurrent lines through the
# origin, in four pairwise distinct coplanar direction classes,
# cover the whole plane spanned by those directions.  Normalized:
# the plane is z = 0; we check all 4-subsets of the 8 nonzero
# plane vectors that are pairwise non-proportional.
# ---------------------------------------------------------------
plane = frozenset(p for p in P if p[2] == 0)
plane_dirs = [p for p in P if p[2] == 0 and p != ZERO]
require(len(plane_dirs) == 8, "wrong plane direction count")

checked_B_geom = 0
for D in itertools.combinations(plane_dirs, 4):
    # pairwise distinct classes: no vector is the negative (=double)
    # of another in the chosen set
    if any(add(d, d) in D for d in D):
        continue
    union = set()
    for d in D:
        union |= line0(d)
    require(union == set(plane),
            f"4-line star {D} does not cover the plane")
    checked_B_geom += 1
require(checked_B_geom == 16, "unexpected case-B geometry count")

# ---------------------------------------------------------------
# Check 2 (case A endgame): the star of the three axis lines plus
# one line through the origin in a free class r (10 choices), plus
# k arbitrary extra points (k <= 3), never carries more than 9 + k
# classes.
# ---------------------------------------------------------------
free_reps = [r for r in reps if r not in E]
require(len(free_reps) == 10, "wrong free representative count")

configs_A = 0
for r in free_reps:
    star = set()
    for d in E + [r]:
        star |= line0(d)
    require(len(star) == 9, f"star for {r} has size {len(star)}")
    complement = [p for p in P if p not in star]
    require(len(complement) == 18, "wrong complement size")
    for k in range(4):
        for extras in itertools.combinations(complement, k):
            S = star | set(extras)
            c = class_count(S)
            require(c <= 9 + k,
                    f"case A violation: r={r} extras={extras} "
                    f"classes={c} > {9 + k}")
            configs_A += 1

# ---------------------------------------------------------------
# Check 3 (case B endgame): the full plane z = 0 plus k arbitrary
# extra points (k <= 3) never carries more than 9 + k classes.
# ---------------------------------------------------------------
configs_B = 0
complement = [p for p in P if p not in plane]
for k in range(4):
    for extras in itertools.combinations(complement, k):
        S = set(plane) | set(extras)
        c = class_count(S)
        require(c <= 9 + k,
                f"case B violation: extras={extras} classes={c} > {9 + k}")
        configs_B += 1

print("case B geometry OK:", checked_B_geom, "coplanar 4-stars cover the plane")
print("case A endgame OK:", configs_A, "configurations")
print("case B endgame OK:", configs_B, "configurations")

# ---------------------------------------------------------------
# Check 4 (independent sanity): class_count(S) <= |S| on a large
# random sample of subsets.
# ---------------------------------------------------------------
import random
random.seed(0)
for _ in range(20000):
    S = random.sample(P, random.randint(1, 27))
    require(class_count(S) <= len(S),
            f"random violation on {S}")
print("random sample OK: 20000 subsets, class count never exceeds size")
