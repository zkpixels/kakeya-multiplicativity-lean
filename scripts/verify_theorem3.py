import itertools

# ---------------------------------------------------------------
# Verification of the two finite-free ingredients of Theorem 3 at
# small primes: the parabola-tangent construction
#   W = {(x,y) : x^2 - y is a square} ∪ {(0,y) : y}
# has exactly q(q+1)/2 + (q-1)/2 points and is Kakeya, and the
# schema inequality FC(q,2,K(q,2)) holds on unions of one line per
# carried class (the reduction target of the proof).
# ---------------------------------------------------------------

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def check_construction(q):
    squares = {(t * t) % q for t in range(q)}
    W = {(x, y) for x in range(q) for y in range(q)
         if ((x * x - y) % q) in squares or x == 0}
    m = q * (q + 1) // 2 + (q - 1) // 2
    require(len(W) == m, f"q={q}: |W| = {len(W)} != {m}")

    def line(a, d):
        return frozenset(((a[0] + t * d[0]) % q, (a[1] + t * d[1]) % q)
                         for t in range(q))
    dirs = [(x, y) for x in range(q) for y in range(q) if (x, y) != (0, 0)]
    for d in dirs:
        require(any(line(p, d) <= W for p in W),
                f"q={q}: direction {d} not carried by W")
    return m

def check_schema_on_unions(q):
    """FC(q,2,m_q) restricted to unions of one line per class subset —
    the exact statement the reduction step of Theorem 3 leaves."""
    m = q * (q + 1) // 2 + (q - 1) // 2
    # the q+1 parallel classes: slopes 0..q-1 and vertical
    classes = []
    for s in range(q):
        classes.append([frozenset((x, (s * x + c) % q) for x in range(q))
                        for c in range(q)])
    classes.append([frozenset((c, y) for y in range(q)) for c in range(q)])
    for k in range(1, q + 2):
        for chosen in itertools.combinations(range(q + 1), k):
            for pick in itertools.product(range(q), repeat=k):
                U = set()
                for ci, li in zip(chosen, pick):
                    U |= classes[ci][li]
                require(m * k <= (q + 1) * len(U),
                        f"q={q}: schema violated at k={k}")
    return True

for q in [3, 5, 7, 11, 13]:
    m = check_construction(q)
    print(f"q={q:2d}: construction OK, |W| = {m} = q(q+1)/2 + (q-1)/2, Kakeya")

for q in [3, 5]:
    check_schema_on_unions(q)
    print(f"q={q:2d}: schema OK on all one-line-per-class unions")
