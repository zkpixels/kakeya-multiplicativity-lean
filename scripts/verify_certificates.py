import itertools

# ---------------------------------------------------------------
# Exhaustive verification of the small fractional-cost
# certificates consumed by Theorem 1, and of the failure at
# (q, n) = (2, 3) at the true price.
#
# FC(q, n, m):  for EVERY subset S of (Z/q)^n,
#     m * #{nonzero directions d : S contains a full line
#           in direction d}  <=  |S| * (q^n - 1).
# ---------------------------------------------------------------

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def check_fc(q, n, m):
    P = list(itertools.product(range(q), repeat=n))
    dirs = [d for d in P if any(d)]
    D = len(dirs)

    def line(a, d):
        return frozenset(
            tuple((a[i] + t * d[i]) % q for i in range(n))
            for t in range(q)
        )

    worst = None
    for r in range(len(P) + 1):
        for sub in itertools.combinations(P, r):
            S = frozenset(sub)
            carried = sum(
                1 for d in dirs if any(line(p, d) <= S for p in S)
            )
            lhs, rhs = m * carried, len(S) * D
            if lhs > rhs:
                return False, (S, carried)
            slack = rhs - lhs
            if carried and (worst is None or slack < worst[0]):
                worst = (slack, carried, len(S))
    return True, worst

# FC(2,2)@3  (16 subsets)
ok, worst = check_fc(2, 2, 3)
require(ok, "FC(2,2)@3 fails")
print("FC(2,2)@3 OK over all 16 subsets; min slack", worst[0])

# FC(2,3)@4 holds, FC(2,3)@5 fails  (256 subsets each)
ok, worst = check_fc(2, 3, 4)
require(ok, "FC(2,3)@4 fails")
print("FC(2,3)@4 OK over all 256 subsets; min slack", worst[0])

ok, witness = check_fc(2, 3, 5)
require(not ok, "FC(2,3)@5 unexpectedly holds")
S, carried = witness
print("FC(2,3)@5 FAILS as claimed; violator size", len(S),
      "carrying", carried, "of 7 directions:", sorted(S))

# FC(3,2)@7  (512 subsets)
ok, worst = check_fc(3, 2, 7)
require(ok, "FC(3,2)@7 fails")
print("FC(3,2)@7 OK over all 512 subsets; min slack", worst[0])
