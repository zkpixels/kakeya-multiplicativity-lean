import itertools

# ---------------------------------------------------------------
# Exhaustive verification of the two 16-point certificates:
#   FC(4,2) at the true price K(4,2) = 10   (first proper prime power), and
#   FC(2,4) at the true price K(2,4) = 6    (first dimension four),
# each over the full powerset 2^16, plus explicit minimum witnesses.
# ---------------------------------------------------------------

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def analyze(q, n, price):
    P = list(itertools.product(range(q), repeat=n))
    N = len(P)
    idx = {p: i for i, p in enumerate(P)}
    dirs = [d for d in P if any(d)]
    D = len(dirs)

    def line_mask(a, d):
        m = 0
        for t in range(q):
            m |= 1 << idx[tuple((a[i] + t * d[i]) % q for i in range(n))]
        return m

    lines = {d: sorted({line_mask(a, d) for a in P}) for d in dirs}

    def carried(mask):
        return sum(1 for d in dirs
                   if any(lm & mask == lm for lm in lines[d]))

    # exhaustive FC check at the claimed price
    K = N + 1
    witness = None
    for mask in range(1, 1 << N):
        c = carried(mask)
        s = bin(mask).count("1")
        require(price * c <= s * D,
                f"FC({q},{n},{price}) fails at mask {mask}")
        if c == D and s < K:
            K, witness = s, mask
    require(K == price, f"true price mismatch: K({q},{n}) = {K} != {price}")
    pts = sorted(P[i] for i in range(N) if witness >> i & 1)
    return K, D, pts

K42, D42, W42 = analyze(4, 2, 10)
print(f"FC(4,2)@10 OK over all 2^16 subsets; K(4,2) = {K42} (D = {D42})")
print("  10-point witness in (Z/4)^2:", W42)

K24, D24, W24 = analyze(2, 4, 6)
print(f"FC(2,4)@6 OK over all 2^16 subsets; K(2,4) = {K24} (D = {D24})")
print("  6-point witness in (Z/2)^4:", W24)
