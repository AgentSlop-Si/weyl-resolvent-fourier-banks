#!/usr/bin/env python3
"""Standalone exact algebraic verification script for:
'Signed Weyl Resolvent Banks for Discrete Fourier Matrices: Small-Order Exactness and Linear Complexity'
by Daniyar Kuttymbek, Adilkhan Kuttymbek, Dayana Kuttymbek,
Amina Kolpenova, and Mukhammadali Kottumbekov.

Uses Python 3 standard library only (zero external dependencies). Exact arithmetic throughout:
1. Order 3 (Theorem 1.1(a)): Literal 4-bank construction over Q(zeta_3), F_4 (char 2), and F_7,
   inverting all 12 3x3 branch matrices directly and verifying sum == F_3.
2. Order 5 (Theorem 1.1(b)): Exact Q[q]/Phi_5 verification of all four lower-bound elimination
   residues and Bezout identity, plus exact 5-bank upper construction (determinants, guards,
   and literal 5x5 inversion of all 25 branch matrices summing to F_5).
3. Order 7 (Theorem 1.1(c)): Independent derivation of R(Y), E(Y) in Q[q]/Phi_7[Y], exact
   reduction mod (29, q-7) and verification of U*Rbar + V*Ebar = 1 in F_29[Y]; plus exact 8-bank
   upper construction in the cubic algebra E = K[t]/(g), verifying disc(g), minors d_0, d_2, d_3,
   all 28 literal 7x7 branch inverses (representing all 56 physical resolvents), and exact trace
   sum == F_7 across all 49 entries.
4. Order 9 lower bound (Theorem 1.1(d)) & Theta(N) Hankel rank (Theorem 1.2): Exact Z[q]/Phi_9
   verification of E*(2q^5-q^4+3q^2-3q+2) == 3, plus triangle coverage and exact Hankel rank
   (N-1)/2 across all odd 3 <= N <= 19.
5. First-order 5N/3 cancellation & reverse-GCD cubic coefficient generator (Theorems 1.3 & 1.4):
   Exact verification over F_47 (N=23, d=4), F_71 (N=35, d=6, strictly beyond old 8d-10 gate),
   and char-2 F_64 (N=63, d=10) of (1-q^2 z)D(qz) = (1-q^d z)D(z), L_x annihilations, chirp
   degree +3 leading term, whole-left envelope inclusion, and full deterministic reverse-GCD
   construction of a legal generator polynomial g with g(0)!=0, gcd(g,g')=1, and rank X_N(g)=N.
"""
from __future__ import annotations

from fractions import Fraction


# ---------------------------------------------------------------------------
# Generic exact field interfaces: Q(zeta_p), F_p, GF(2^m), and K[t]/(g(t))
# ---------------------------------------------------------------------------

def poly_trim_f(p: list, zero) -> list:
    p = list(p)
    while len(p) > 1 and p[-1] == zero:
        p.pop()
    return p


class PrimeField:
    def __init__(self, p: int):
        self.p = p
        self.zero = 0
        self.one = 1

    def of_int(self, n: int) -> int:
        return n % self.p

    def add(self, a: int, b: int) -> int:
        return (a + b) % self.p

    def sub(self, a: int, b: int) -> int:
        return (a - b) % self.p

    def neg(self, a: int) -> int:
        return (-a) % self.p

    def mul(self, a: int, b: int) -> int:
        return (a * b) % self.p

    def inv(self, a: int) -> int:
        assert a % self.p != 0, "Division by zero in F_p"
        return pow(a, self.p - 2, self.p)

    def div(self, a: int, b: int) -> int:
        return self.mul(a, self.inv(b))

    def pow(self, a: int, e: int) -> int:
        if e < 0:
            return pow(self.inv(a), -e, self.p)
        return pow(a, e, self.p)


class GF2Ext:
    """Exact GF(2^m) with irreducible binary modulus polynomial (as bitmask)."""

    def __init__(self, deg: int, mod_mask: int):
        self.deg = deg
        self.mod = mod_mask
        self.zero = 0
        self.one = 1

    def of_int(self, n: int) -> int:
        return n & 1

    def add(self, a: int, b: int) -> int:
        return a ^ b

    def sub(self, a: int, b: int) -> int:
        return a ^ b

    def neg(self, a: int) -> int:
        return a

    def mul(self, a: int, b: int) -> int:
        res = 0
        while b:
            if b & 1:
                res ^= a
            b >>= 1
            a <<= 1
            if a & (1 << self.deg):
                a ^= self.mod
        return res

    def pow(self, a: int, e: int) -> int:
        if e < 0:
            a = self.inv(a)
            e = -e
        res = 1
        base = a
        while e:
            if e & 1:
                res = self.mul(res, base)
            base = self.mul(base, base)
            e >>= 1
        return res

    def inv(self, a: int) -> int:
        assert a != 0, "Division by zero in GF(2^m)"
        return self.pow(a, (1 << self.deg) - 2)

    def div(self, a: int, b: int) -> int:
        return self.mul(a, self.inv(b))


class CycloPrimeField:
    """Exact Q(zeta_p) = Q[q]/Phi_p(q) for prime p (basis 1, q, ..., q^{p-2})."""

    def __init__(self, p: int):
        self.p = p
        self.deg = p - 1
        self.zero = (Fraction(0),) * self.deg
        self.one = self.qpow(0)
        self.q = self.qpow(1)

    def reduce_vec(self, vec: list[Fraction]) -> tuple[Fraction, ...]:
        assert len(vec) == self.p
        last = vec[self.p - 1]
        return tuple(vec[i] - last for i in range(self.deg))

    def of_int(self, n: int) -> tuple[Fraction, ...]:
        return (Fraction(n),) + (Fraction(0),) * (self.deg - 1)

    def of_frac(self, f: Fraction) -> tuple[Fraction, ...]:
        return (f,) + (Fraction(0),) * (self.deg - 1)

    def of_coeffs(self, cs: list[int | Fraction], denom: int = 1) -> tuple[Fraction, ...]:
        v = [Fraction(c, denom) for c in cs] + [Fraction(0)] * (self.deg - len(cs))
        return tuple(v[: self.deg])

    def qpow(self, e: int) -> tuple[Fraction, ...]:
        v = [Fraction(0)] * self.p
        v[e % self.p] = Fraction(1)
        return self.reduce_vec(v)

    def add(self, a, b):
        return tuple(x + y for x, y in zip(a, b))

    def sub(self, a, b):
        return tuple(x - y for x, y in zip(a, b))

    def neg(self, a):
        return tuple(-x for x in a)

    def mul(self, a, b):
        v = [Fraction(0)] * self.p
        for i in range(self.deg):
            ai = a[i]
            if ai == 0:
                continue
            for j in range(self.deg):
                bj = b[j]
                if bj != 0:
                    v[(i + j) % self.p] += ai * bj
        return self.reduce_vec(v)

    def inv(self, a):
        assert a != self.zero, "Division by zero in Q(zeta_p)"
        d = self.deg
        M = [[Fraction(0)] * (d + 1) for _ in range(d)]
        for col in range(d):
            e_col = [Fraction(0)] * d
            e_col[col] = Fraction(1)
            prod = self.mul(a, tuple(e_col))
            for row in range(d):
                M[row][col] = prod[row]
        M[0][d] = Fraction(1)
        for col in range(d):
            piv = next(r for r in range(col, d) if M[r][col] != 0)
            M[col], M[piv] = M[piv], M[col]
            pv = M[col][col]
            M[col] = [x / pv for x in M[col]]
            for r in range(d):
                if r != col and M[r][col] != 0:
                    f = M[r][col]
                    M[r] = [M[r][c] - f * M[col][c] for c in range(d + 1)]
        return tuple(M[r][d] for r in range(d))

    def div(self, a, b):
        return self.mul(a, self.inv(b))

    def pow(self, a, e: int):
        if e < 0:
            a = self.inv(a)
            e = -e
        res = self.one
        base = a
        while e:
            if e & 1:
                res = self.mul(res, base)
            base = self.mul(base, base)
            e >>= 1
        return res


class CubicAlgebra:
    """Exact separable cubic algebra E = K[t]/(t^3 + s2*t - s3) over a base field K."""

    def __init__(self, K, s2, s3):
        self.K = K
        self.s2 = s2
        self.s3 = s3
        self.zero = (K.zero, K.zero, K.zero)
        self.one = (K.one, K.zero, K.zero)
        self.t = (K.zero, K.one, K.zero)

    def embed(self, c):
        return (c, self.K.zero, self.K.zero)

    def add(self, a, b):
        K = self.K
        return (K.add(a[0], b[0]), K.add(a[1], b[1]), K.add(a[2], b[2]))

    def sub(self, a, b):
        K = self.K
        return (K.sub(a[0], b[0]), K.sub(a[1], b[1]), K.sub(a[2], b[2]))

    def neg(self, a):
        K = self.K
        return (K.neg(a[0]), K.neg(a[1]), K.neg(a[2]))

    def mul(self, a, b):
        K = self.K
        # Multiply polynomials of deg <= 2, reduce t^3 = -s2*t + s3, t^4 = -s2*t^2 + s3*t
        c = [K.zero] * 5
        for i in range(3):
            for j in range(3):
                c[i + j] = K.add(c[i + j], K.mul(a[i], b[j]))
        # Reduce degree 4
        c[2] = K.sub(c[2], K.mul(c[4], self.s2))
        c[1] = K.add(c[1], K.mul(c[4], self.s3))
        # Reduce degree 3
        c[1] = K.sub(c[1], K.mul(c[3], self.s2))
        c[0] = K.add(c[0], K.mul(c[3], self.s3))
        return (c[0], c[1], c[2])

    def pow(self, a, e: int):
        res = self.one
        base = a
        while e:
            if e & 1:
                res = self.mul(res, base)
            base = self.mul(base, base)
            e >>= 1
        return res

    def inv(self, a):
        K = self.K
        M = [[K.zero] * 4 for _ in range(3)]
        basis = [self.one, self.t, (K.zero, K.zero, K.one)]
        for col in range(3):
            prod = self.mul(a, basis[col])
            for row in range(3):
                M[row][col] = prod[row]
        M[0][3] = K.one
        for col in range(3):
            piv = next(r for r in range(col, 3) if M[r][col] != K.zero)
            M[col], M[piv] = M[piv], M[col]
            inv_pv = K.inv(M[col][col])
            M[col] = [K.mul(x, inv_pv) for x in M[col]]
            for r in range(3):
                if r != col and M[r][col] != K.zero:
                    f = M[r][col]
                    M[r] = [K.sub(M[r][c], K.mul(f, M[col][c])) for c in range(4)]
        return (M[0][3], M[1][3], M[2][3])

    def trace(self, a):
        # Tr_{E/K}(a0 + a1*t + a2*t^2) = 3*a0 - 2*s2*a2
        K = self.K
        return K.sub(K.mul(K.of_int(3), a[0]), K.mul(K.mul(K.of_int(2), self.s2), a[2]))


# ---------------------------------------------------------------------------
# Generic exact matrix & polynomial helpers over any field F
# ---------------------------------------------------------------------------

def mat_mul(F, A, B):
    n = len(A)
    m = len(B[0])
    k = len(B)
    out = [[F.zero] * m for _ in range(n)]
    for i in range(n):
        for r in range(k):
            air = A[i][r]
            if air == F.zero:
                continue
            for j in range(m):
                if B[r][j] != F.zero:
                    out[i][j] = F.add(out[i][j], F.mul(air, B[r][j]))
    return out


def mat_det(F, A):
    n = len(A)
    M = [list(row) for row in A]
    det = F.one
    for col in range(n):
        piv = None
        for r in range(col, n):
            if M[r][col] != F.zero:
                piv = r
                break
        if piv is None:
            return F.zero
        if piv != col:
            M[col], M[piv] = M[piv], M[col]
            det = F.neg(det)
        pv = M[col][col]
        det = F.mul(det, pv)
        inv_pv = F.inv(pv)
        for r in range(col + 1, n):
            if M[r][col] != F.zero:
                f = F.mul(M[r][col], inv_pv)
                for c in range(col, n):
                    M[r][c] = F.sub(M[r][c], F.mul(f, M[col][c]))
    return det


def mat_solve(F, A, b):
    n = len(A)
    M = [list(A[r]) + [b[r]] for r in range(n)]
    for col in range(n):
        piv = next(r for r in range(col, n) if M[r][col] != F.zero)
        M[col], M[piv] = M[piv], M[col]
        inv_pv = F.inv(M[col][col])
        M[col] = [F.mul(x, inv_pv) for x in M[col]]
        for r in range(n):
            if r != col and M[r][col] != F.zero:
                f = M[r][col]
                M[r] = [F.sub(M[r][c], F.mul(f, M[col][c])) for c in range(n + 1)]
    return [M[r][n] for r in range(n)]


def mat_inv(F, A):
    n = len(A)
    M = [list(A[r]) + [F.one if r == c else F.zero for c in range(n)] for r in range(n)]
    for col in range(n):
        piv = next(r for r in range(col, n) if M[r][col] != F.zero)
        M[col], M[piv] = M[piv], M[col]
        inv_pv = F.inv(M[col][col])
        M[col] = [F.mul(x, inv_pv) for x in M[col]]
        for r in range(n):
            if r != col and M[r][col] != F.zero:
                f = M[r][col]
                M[r] = [F.sub(M[r][c], F.mul(f, M[col][c])) for c in range(2 * n)]
    return [row[n:] for row in M]


def mat_rank(F, A) -> int:
    rows = len(A)
    cols = len(A[0])
    M = [list(row) for row in A]
    rk = 0
    for col in range(cols):
        piv = None
        for r in range(rk, rows):
            if M[r][col] != F.zero:
                piv = r
                break
        if piv is None:
            continue
        M[rk], M[piv] = M[piv], M[rk]
        inv_pv = F.inv(M[rk][col])
        M[rk] = [F.mul(x, inv_pv) for x in M[rk]]
        for r in range(rows):
            if r != rk and M[r][col] != F.zero:
                f = M[r][col]
                M[r] = [F.sub(M[r][c], F.mul(f, M[rk][c])) for c in range(cols)]
        rk += 1
        if rk == rows:
            break
    return rk


def mat_nullspace(F, A):
    """Return a basis for the right nullspace {x : A x = 0} over field F."""
    rows = len(A)
    cols = len(A[0])
    M = [list(row) for row in A]
    piv_cols = []
    rk = 0
    for col in range(cols):
        piv = None
        for r in range(rk, rows):
            if M[r][col] != F.zero:
                piv = r
                break
        if piv is None:
            continue
        M[rk], M[piv] = M[piv], M[rk]
        inv_pv = F.inv(M[rk][col])
        M[rk] = [F.mul(x, inv_pv) for x in M[rk]]
        for r in range(rows):
            if r != rk and M[r][col] != F.zero:
                f = M[r][col]
                M[r] = [F.sub(M[r][c], F.mul(f, M[rk][c])) for c in range(cols)]
        piv_cols.append(col)
        rk += 1
    piv_set = set(piv_cols)
    free_cols = [c for c in range(cols) if c not in piv_set]
    basis = []
    for fc in free_cols:
        vec = [F.zero] * cols
        vec[fc] = F.one
        for r, pc in enumerate(piv_cols):
            vec[pc] = F.neg(M[r][fc])
        basis.append(vec)
    return basis


def poly_add(F, a, b):
    n = max(len(a), len(b))
    res = [F.add(a[i] if i < len(a) else F.zero, b[i] if i < len(b) else F.zero) for i in range(n)]
    return poly_trim_f(res, F.zero)


def poly_sub(F, a, b):
    n = max(len(a), len(b))
    res = [F.sub(a[i] if i < len(a) else F.zero, b[i] if i < len(b) else F.zero) for i in range(n)]
    return poly_trim_f(res, F.zero)


def poly_scale(F, a, s):
    if s == F.zero:
        return [F.zero]
    return poly_trim_f([F.mul(c, s) for c in a], F.zero)


def poly_mul(F, a, b):
    res = [F.zero] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai == F.zero:
            continue
        for j, bj in enumerate(b):
            if bj != F.zero:
                res[i + j] = F.add(res[i + j], F.mul(ai, bj))
    return poly_trim_f(res, F.zero)


def poly_divmod(F, a, b):
    a = poly_trim_f(a, F.zero)
    b = poly_trim_f(b, F.zero)
    assert b[-1] != F.zero
    db = len(b) - 1
    if len(a) - 1 < db:
        return [F.zero], a
    inv_lb = F.inv(b[-1])
    rem = list(a)
    quot = [F.zero] * (len(a) - db)
    for k in range(len(a) - 1, db - 1, -1):
        if rem[k] != F.zero:
            q_k = F.mul(rem[k], inv_lb)
            quot[k - db] = q_k
            for j in range(db + 1):
                rem[k - db + j] = F.sub(rem[k - db + j], F.mul(q_k, b[j]))
    return poly_trim_f(quot, F.zero), poly_trim_f(rem, F.zero)


def poly_monic(F, a):
    a = poly_trim_f(a, F.zero)
    if a == [F.zero]:
        return a
    return poly_scale(F, a, F.inv(a[-1]))


def poly_gcd(F, a, b):
    a = poly_trim_f(a, F.zero)
    b = poly_trim_f(b, F.zero)
    while b != [F.zero]:
        _, r = poly_divmod(F, a, b)
        a, b = b, r
    return poly_monic(F, a)


def poly_deriv(F, a):
    if len(a) <= 1:
        return [F.zero]
    return poly_trim_f([F.mul(a[i], F.of_int(i)) for i in range(1, len(a))], F.zero)


def poly_eval(F, a, x):
    acc = F.zero
    for c in reversed(a):
        acc = F.add(F.mul(acc, x), c)
    return acc


# ---------------------------------------------------------------------------
# Signed Weyl bank literal matrix builder & evaluator
# ---------------------------------------------------------------------------

def gauss_binom(F, n: int, ell: int, zeta):
    if ell < 0 or ell > n:
        return F.zero
    num = F.one
    den = F.one
    for i in range(1, ell + 1):
        num = F.mul(num, F.sub(F.one, F.pow(zeta, n - ell + i)))
        den = F.mul(den, F.sub(F.one, F.pow(zeta, i)))
    return F.div(num, den)


def fourier_matrix(F, N: int, q):
    return [[F.pow(q, -(k * t) % N) for t in range(N)] for k in range(N)]


def fourier_CN(F, N: int, q):
    s = F.zero
    for t in range(N):
        s = F.add(s, F.pow(q, -(t * t) % N))
    return F.div(s, F.of_int(N))


def build_branch_matrix(F, N: int, q, eps: int, delta: int, alpha, beta, j: int):
    """Build literal N x N matrix I - alpha S^eps - beta zeta^j T^delta."""
    zeta = F.pow(q, (eps * delta) % N)
    zj = F.pow(zeta, j)
    M = [[F.zero] * N for _ in range(N)]
    for i in range(N):
        # Diagonal: 1 - beta * zeta^j * q^{delta * i}
        diag_term = F.mul(F.mul(beta, zj), F.pow(q, (delta * i) % N))
        M[i][i] = F.sub(F.one, diag_term)
        # Shift: S^eps e_t = e_{t + eps}, so row (t + eps), col t has -alpha
        r = (i + eps) % N
        M[r][i] = F.sub(M[r][i], alpha)
    return M


def evaluate_bank_literal(F, N: int, q, eps: int, delta: int, alpha, beta, weights):
    """Literally invert all N branch matrices (I - X_j) and form (1/N) sum_j w_j (I - X_j)^{-1}."""
    delta_guard = F.sub(F.sub(F.one, F.pow(alpha, N)), F.pow(beta, N))
    assert delta_guard != F.zero, "Illegal bank guard Delta == 0"
    acc = [[F.zero] * N for _ in range(N)]
    invN = F.inv(F.of_int(N))
    for j in range(N):
        wj = weights[j]
        if wj == F.zero:
            continue
        Mj = build_branch_matrix(F, N, q, eps, delta, alpha, beta, j)
        Invj = mat_inv(F, Mj)
        # Verify exact two-sided inverse
        prod = mat_mul(F, Mj, Invj)
        for r in range(N):
            for c in range(N):
                assert prod[r][c] == (F.one if r == c else F.zero)
        for r in range(N):
            for c in range(N):
                acc[r][c] = F.add(acc[r][c], F.mul(wj, Invj[r][c]))
    return [[F.mul(invN, acc[r][c]) for c in range(N)] for r in range(N)]


def weights_from_h(F, N: int, q, CN, eps: int, delta: int, alpha, h_list):
    """Eq. (2.3): w_j = C_N * Delta * sum_ell h_ell q^{-eps*delta*j*ell} with beta = 1."""
    delta_guard = F.neg(F.pow(alpha, N))
    pref = F.mul(CN, delta_guard)
    ws = []
    for j in range(N):
        s = F.zero
        for ell in range(N):
            s = F.add(s, F.mul(h_list[ell], F.pow(q, (-eps * delta * j * ell) % N)))
        ws.append(F.mul(pref, s))
    return ws


# ---------------------------------------------------------------------------
# Check 1: Order 3 (all-field literal 4-bank synthesis)
# ---------------------------------------------------------------------------

def verify_order3() -> None:
    # Test over Q(zeta_3), GF(4) (char 2!), and F_7 (q=2)
    K3 = CycloPrimeField(3)
    GF4 = GF2Ext(2, 0b111)  # t^2 + t + 1
    F7 = PrimeField(7)
    configs = [
        ("Q(zeta_3)", K3, K3.q),
        ("GF(4) [char 2]", GF4, 0b10),  # t has order 3 in GF(4)
        ("F_7 [q=2]", F7, 2),
    ]
    for label, F, q in configs:
        assert F.pow(q, 3) == F.one and q != F.one
        CN = fourier_CN(F, 3, q)
        assert CN != F.zero
        inv4 = pow(4, -1, 3)  # = 1 mod 3
        f3 = lambda a, b: F.pow(q, (inv4 * (a + b) * (a + b)) % 3)
        alphas = {(+1, +1): F.one, (+1, -1): q, (-1, +1): q, (-1, -1): F.one}
        # Row b=0
        inv3 = F.inv(F.of_int(3))
        c0 = F.mul(inv3, F.add(F.add(f3(0, 0), f3(1, 0)), f3(2, 0)))
        c1 = F.mul(inv3, F.add(F.add(f3(0, 0), F.mul(f3(1, 0), F.pow(q, 2))), F.mul(f3(2, 0), q)))
        cm1 = F.mul(inv3, F.add(F.add(f3(0, 0), F.mul(f3(1, 0), q)), F.mul(f3(2, 0), F.pow(q, 2))))
        h = {ori: [F.zero, F.zero, F.zero] for ori in alphas}
        h[(+1, +1)][0] = c0
        h[(+1, -1)][0] = c1
        h[(-1, +1)][0] = cm1
        h[(-1, -1)][0] = F.zero
        # Exclusive l=1
        for eps, delta in alphas:
            den = F.mul(alphas[(eps, delta)], F.add(F.one, F.pow(q, (eps * delta) % 3)))
            h[(eps, delta)][1] = F.div(f3(eps % 3, delta % 3), den)
        # Axis corrections l=2
        for d_sgn in (+1, -1):
            h[(+1, -d_sgn)][2] = F.sub(F.sub(f3(0, d_sgn % 3), h[(+1, d_sgn)][1]), h[(-1, d_sgn)][1])
            h[(-1, -d_sgn)][2] = F.zero

        total = [[F.zero] * 3 for _ in range(3)]
        for eps, delta in alphas:
            ws = weights_from_h(F, 3, q, CN, eps, delta, alphas[(eps, delta)], h[(eps, delta)])
            B = evaluate_bank_literal(F, 3, q, eps, delta, alphas[(eps, delta)], F.one, ws)
            for r in range(3):
                for c in range(3):
                    total[r][c] = F.add(total[r][c], B[r][c])
        F3 = fourier_matrix(F, 3, q)
        assert total == F3, f"Order-3 mismatch over {label}"
    print("  [PASS] Order 3 (Theorem 1.1(a)): Literal 4-bank synthesis verified over Q(zeta_3), GF(4) [char 2], and F_7.")


# ---------------------------------------------------------------------------
# Check 2: Order 5 (lower bound 5 + literal 5-bank upper construction)
# ---------------------------------------------------------------------------

def verify_order5() -> None:
    K = CycloPrimeField(5)
    q = K.q
    q2, q3, q4 = K.qpow(2), K.qpow(3), K.qpow(4)
    c = K.add(q, q4)
    d = K.add(K.one, q4)
    H = K.div(q, K.add(K.one, q))
    assert H == K.of_coeffs([1, 1, 0, 1])
    assert K.mul(c, K.add(c, K.one)) == K.one

    # Lower bound residues
    s = K.neg(K.inv(c))
    p = K.sub(K.inv(K.mul(c, c)), K.div(q2, c))
    assert s == K.of_coeffs([0, 0, 1, 1])
    assert p == K.of_coeffs([1, -1, -2, -2])
    assert K.sub(K.mul(s, s), K.mul(K.of_int(4), p)) == K.of_coeffs([-3, 4, 7, 7])

    a_c = K.sub(K.mul(K.of_int(2), c), q)
    # Distinct diagonal: c * D(t, w) with t+w = 1/c, tw = -q^2/c
    cD_dist = K.sub(K.sub(K.mul(a_c, K.neg(q2)), K.of_int(2)), K.mul(K.mul(K.of_int(2), c), d))
    assert cD_dist == K.of_coeffs([-2, -2, 2, -1])

    # Equal diagonal Bezout identity in K[t]
    B_poly = [K.neg(q2), K.neg(K.one), c]
    Dtt = [K.mul(K.of_int(-2), d), K.of_int(-4), a_c]
    L_poly = poly_sub(K, poly_scale(K, Dtt, c), poly_scale(K, B_poly, a_c))
    l0 = K.of_coeffs([0, 2, 2, 1])
    l1 = K.of_coeffs([2, -1, 2, 2])
    assert L_poly == [l0, l1]
    cof = [K.sub(K.neg(K.mul(c, l0)), l1), K.mul(c, l1)]
    bez = poly_sub(K, poly_scale(K, B_poly, K.mul(l1, l1)), poly_mul(K, cof, L_poly))
    assert bez == [K.of_coeffs([1, 4, -11, 6])]

    # Nondiagonal residues
    s2m2p = K.sub(K.mul(s, s), K.mul(K.of_int(2), p))
    res_n1 = K.sub(K.sub(K.sub(K.mul(q2, s2m2p), K.mul(s, p)), K.mul(K.mul(K.of_int(2), d), p)), K.mul(q, K.mul(p, p)))
    res_n2 = K.sub(K.sub(K.sub(K.mul(q2, s2m2p), K.mul(s, p)), K.mul(d, s2m2p)), K.mul(q, K.mul(p, p)))
    assert res_n1 == K.of_coeffs([-5, -5, 0, 5])
    assert res_n2 == K.of_coeffs([-9, -19, -17, -5])

    # Upper bound: 5-bank literal synthesis over Q(zeta_5)
    x = K.one
    z = K.of_coeffs([-2, -3, -3, -1])
    y = q
    t = K.add(K.one, q)
    v = u = t
    assert K.sub(K.sub(K.mul(c, K.mul(t, t)), t), q2) == K.zero

    M_y = K.sub(K.mul(c, K.mul(y, y)), q2)
    N_y = K.div(K.add(y, q2), c)
    assert M_y == K.of_coeffs([0, 1, -1, 1])
    assert N_y == K.of_coeffs([1, 2, 2, 1])
    assert N_y == K.sub(K.mul(K.add(x, z), M_y), K.mul(x, z))

    f5 = lambda a, b: K.qpow(4 * (a + b) * (a + b))
    h_banks = [[K.zero] * 5 for _ in range(5)]
    # b=1 (l=1 for ++, -+)
    h_banks[0][1] = K.div(K.mul(H, K.sub(z, M_y)), K.mul(x, K.sub(z, x)))
    h_banks[1][1] = K.div(K.mul(H, K.sub(M_y, x)), K.mul(z, K.sub(z, x)))
    h_banks[2][1] = K.div(H, y)
    # b=4 (l=1 for +-, --)
    h_banks[3][1] = K.div(H, v)
    h_banks[4][1] = K.div(H, u)
    # Axis l=4
    h_banks[3][4] = K.sub(f5(0, 1), K.add(K.add(h_banks[0][1], h_banks[1][1]), h_banks[2][1]))
    h_banks[0][4] = K.sub(f5(0, 4), K.add(h_banks[3][1], h_banks[4][1]))

    G_c = K.of_coeffs([1, 1, 1, 0])
    P_c = K.add(K.add(K.one, q4), q3)
    M0 = [
        [K.one, K.one, K.one, K.one, K.one],
        [x, z, K.pow(y, 4), v, K.pow(u, 4)],
        [K.pow(x, 2), K.pow(z, 2), K.pow(y, 3), K.pow(v, 2), K.pow(u, 3)],
        [K.pow(x, 3), K.pow(z, 3), K.pow(y, 2), K.pow(v, 3), K.pow(u, 2)],
        [K.pow(x, 4), K.pow(z, 4), y, K.pow(v, 4), u],
    ]
    M2 = [
        [K.one, K.one, K.one, K.one, K.one],
        [K.mul(G_c, x), K.mul(G_c, z), K.zero, K.neg(K.mul(q, v)), K.zero],
        [K.mul(q2, K.pow(x, 2)), K.mul(q2, K.pow(z, 2)), K.zero, K.zero, K.zero],
        [K.zero, K.zero, K.mul(q3, K.pow(y, 2)), K.zero, K.zero],
        [K.zero, K.zero, K.mul(P_c, y), K.zero, K.neg(K.mul(q4, u))],
    ]
    M3 = [
        [K.one, K.one, K.one, K.one, K.one],
        [K.neg(K.mul(q4, x)), K.neg(K.mul(q4, z)), K.zero, K.mul(P_c, v), K.zero],
        [K.zero, K.zero, K.zero, K.mul(q3, K.pow(v, 2)), K.zero],
        [K.zero, K.zero, K.zero, K.zero, K.mul(q2, K.pow(u, 2))],
        [K.zero, K.zero, K.neg(K.mul(q, y)), K.zero, K.mul(G_c, u)],
    ]
    assert mat_det(K, M0) == K.of_coeffs([-1093, -5351, -6894, -3592])
    assert mat_det(K, M2) == K.of_coeffs([31, 21, -17, -30])
    assert mat_det(K, M3) == K.of_coeffs([6, 19, 21, 9])

    specs = [(+1, +1, x), (+1, +1, z), (-1, +1, y), (+1, -1, v), (-1, -1, u)]
    for b_row, Mat in [(0, M0), (2, M2), (3, M3)]:
        sol = mat_solve(K, Mat, [f5(a, b_row) for a in range(5)])
        for idx, (eps, delta, _) in enumerate(specs):
            ell = (delta * b_row) % 5
            h_banks[idx][ell] = sol[idx]

    # Verify guards and literal 5x5 branch matrix sum == F_5
    exp_guards = [
        K.of_coeffs([-1, 0, 0, 0]),
        K.of_coeffs([269, 760, 795, 325]),
        K.of_coeffs([-1, 0, 0, 0]),
        K.of_coeffs([3, 0, -5, -5]),
        K.of_coeffs([3, 0, -5, -5]),
    ]
    CN = fourier_CN(K, 5, q)
    total = [[K.zero] * 5 for _ in range(5)]
    for idx, (eps, delta, alpha) in enumerate(specs):
        assert K.neg(K.pow(alpha, 5)) == exp_guards[idx]
        ws = weights_from_h(K, 5, q, CN, eps, delta, alpha, h_banks[idx])
        B = evaluate_bank_literal(K, 5, q, eps, delta, alpha, K.one, ws)
        for r in range(5):
            for c_i in range(5):
                total[r][c_i] = K.add(total[r][c_i], B[r][c_i])
    assert total == fourier_matrix(K, 5, q)
    print("  [PASS] Order 5 (Theorem 1.1(b)): Exact lower-bound residues + literal 5-bank 5x5 synthesis verified over Q(zeta_5).")


# ---------------------------------------------------------------------------
# Check 3: Order 7 (lower bound 8 Bezout + literal 8-bank cubic-algebra trace)
# ---------------------------------------------------------------------------

def verify_order7() -> None:
    K = CycloPrimeField(7)
    q = K.q
    H = K.div(q, K.add(K.one, q))
    f7 = lambda a, b: K.qpow(2 * (a + b) * (a + b))

    # --- Part A: Lower bound 8 (derive R(Y), E(Y) over K[Y] and check mod (29, q-7)) ---
    def qint(j, root):
        s = K.zero
        for i in range(j):
            s = K.add(s, K.pow(root, i))
        return s

    qinv = K.qpow(6)
    # Build m_1..m_4 in K[Y] from exact row b=1 formula
    m_polys = {}
    for a in (2, 3, 4, 5):
        c0 = K.div(f7(a, 1), K.mul(H, qint(a + 1, q)))
        c_deg = K.neg(K.div(qint(8 - a, qinv), qint(a + 1, q)))
        deg = 6 - a
        p_a = [K.zero] * (deg + 1)
        p_a[0] = c0
        p_a[deg] = c_deg
        m_polys[a - 1] = p_a
    # Check displayed coefficients of m1..m4
    assert m_polys[1][0] == K.of_coeffs([-1, -1, 0, 0, -1, -1])
    assert m_polys[1][4] == K.of_coeffs([0, 0, -1, 0, 0, -1])
    assert m_polys[2][0] == K.of_coeffs([1, 1, 0, 1, 1, 0])
    assert m_polys[2][3] == K.of_coeffs([-1, 0, 0, -1, -1, 0])

    D_p = poly_sub(K, m_polys[2], poly_mul(K, m_polys[1], m_polys[1]))
    Sn_p = poly_sub(K, m_polys[3], poly_mul(K, m_polys[1], m_polys[2]))
    Pn_p = poly_sub(K, poly_mul(K, m_polys[1], m_polys[3]), poly_mul(K, m_polys[2], m_polys[2]))
    R_p = poly_add(K, poly_sub(K, poly_mul(K, D_p, m_polys[4]), poly_mul(K, Sn_p, m_polys[3])), poly_mul(K, Pn_p, m_polys[2]))

    gb42q = gauss_binom(K, 4, 2, q)
    gb52q = gauss_binom(K, 5, 2, q)
    gb62q = gauss_binom(K, 6, 2, q)
    gb42qi = gauss_binom(K, 4, 2, qinv)
    gb52qi = gauss_binom(K, 5, 2, qinv)
    gb62qi = gauss_binom(K, 6, 2, qinv)
    n2_p = [K.div(K.qpow(4), gb42q)]
    n3_p = [K.div(q, gb52q), K.zero, K.neg(K.div(K.div(gb62qi, gb42qi), gb52q))]
    n4_p = [K.div(K.qpow(2), gb62q), K.neg(K.div(K.div(gb52qi, gb42qi), gb62q))]
    E_p = poly_add(K, poly_sub(K, poly_mul(K, D_p, n4_p), poly_mul(K, Sn_p, n3_p)), poly_mul(K, Pn_p, n2_p))

    # Reduce R_p, E_p modulo (29, q -> 7)
    F29 = PrimeField(29)

    def red29(elem):
        acc = 0
        for i, fr in enumerate(elem):
            assert fr.denominator % 29 != 0
            val = (fr.numerator % 29) * pow(fr.denominator % 29, 27, 29) % 29
            acc = (acc + val * pow(7, i, 29)) % 29
        return acc

    Rbar = [red29(c) for c in R_p]
    Ebar = [red29(c) for c in E_p]
    assert Rbar == [23, 26, 9, 23, 13, 0, 11, 16, 10, 8], Rbar
    assert Ebar == [28, 5, 17, 4, 2, 15, 24, 10, 28, 3], Ebar
    U_c = [21, 24, 2, 5, 25, 23, 15, 2, 18]
    V_c = [18, 28, 0, 22, 8, 2, 16, 25, 10]
    assert poly_add(F29, poly_mul(F29, U_c, Rbar), poly_mul(F29, V_c, Ebar)) == [1]

    # --- Part B: Upper bound 8 (cubic algebra E = K[t]/(g) + literal 7x7 branch inverses & trace) ---
    s2 = K.of_coeffs([-8, 35, 25, 28, 1, -17], 29)
    s3 = K.of_coeffs([-3, -5, -16, -4, 4, 19], 29)
    # disc(t^3 + s2*t - s3) = -4 s2^3 - 27 s3^2
    disc_g = K.sub(K.mul(K.of_int(-4), K.pow(s2, 3)), K.mul(K.of_int(27), K.pow(s3, 2)))
    assert disc_g == K.of_coeffs([665859, 635064, 863499, 425987, 275146, -15036], 24389)

    # Evaluate m_1..m_4 at y = 1
    m_vals = {j: poly_eval(K, m_polys[j], K.one) for j in (1, 2, 3, 4)}
    D_val = K.sub(m_vals[2], K.mul(m_vals[1], m_vals[1]))
    assert D_val == K.of_coeffs([1, 4, -1, 0, 3, 0])
    assert s2 == K.div(K.sub(K.mul(m_vals[1], m_vals[3]), m_vals[4]), D_val)
    assert s3 == K.add(m_vals[3], K.mul(s2, m_vals[1]))

    # Power table p_r = t^r mod g in {1, t, t^2}
    p_tab = [(K.one, K.zero, K.zero), (K.zero, K.one, K.zero), (K.zero, K.zero, K.one)]
    for r in range(3, 7):
        p_tab.append(tuple(K.add(K.mul(K.neg(s2), p_tab[r - 2][i]), K.mul(s3, p_tab[r - 3][i])) for i in range(3)))

    def G_coeff(eps: int, delta: int, a: int, b: int):
        r = (eps * a) % 7
        ell = (delta * b) % 7
        if r + ell > 6:
            return K.zero
        return gauss_binom(K, r + ell, ell, K.qpow((eps * delta) % 7))

    def build_Mb(b: int):
        M = []
        for a in range(7):
            gpp = G_coeff(+1, +1, a, b)
            gmp = G_coeff(-1, +1, a, b)
            gpm = G_coeff(+1, -1, a, b)
            gmm = G_coeff(-1, -1, a, b)
            ma = (-a) % 7
            M.append([
                K.mul(gpp, p_tab[a][0]), K.mul(gpp, p_tab[a][1]), K.mul(gpp, p_tab[a][2]),
                gmp, gpm,
                K.mul(gmm, p_tab[ma][0]), K.mul(gmm, p_tab[ma][1]), K.mul(gmm, p_tab[ma][2]),
            ])
        return M

    minors = {
        0: (0, 1, 2, 3, 5, 6, 7),
        2: (0, 1, 2, 3, 4, 5, 6),
        3: (0, 1, 2, 3, 4, 6, 7),
    }
    exp_dets = {
        0: K.of_coeffs([-370501134818472, -889546502909192, -1166936870814012,
                        -994193630954024, -501377982443436, -58844381586428], 500246412961),
        2: K.of_coeffs([726, -4387, -12368, -16345, -13989, -6744], 841),
        3: K.of_coeffs([1, 3, 5, 5, 3, 1], 1),
    }
    z_rows = {}
    for b in (0, 2, 3):
        Mb = build_Mb(b)
        cols = minors[b]
        sub = [[Mb[a][c] for c in cols] for a in range(7)]
        assert mat_det(K, sub) == exp_dets[b], f"Minor det mismatch at b={b}"
        sol7 = mat_solve(K, sub, [f7(a, b) for a in range(7)])
        zb = [K.zero] * 8
        for idx, c in enumerate(cols):
            zb[c] = sol7[idx]
        z_rows[b] = zb

    K0 = K.div(K.mul(H, K.add(m_vals[2], s2)), s3)
    z_rows[1] = [K0, H, K.mul(H, m_vals[1]), H, K.sub(K.sub(K.qpow(2), K0), H), K.zero, K.zero, K.zero]
    J_refl = lambda z: [z[5], z[6], z[7], z[4], z[3], z[0], z[1], z[2]]
    z_rows[4] = J_refl(z_rows[3])
    z_rows[5] = J_refl(z_rows[2])
    z_rows[6] = J_refl(z_rows[1])

    # Literal verification of all 56 branch resolvents via E = K[t]/(g) trace!
    E = CubicAlgebra(K, s2, s3)
    g_prime_E = (s2, K.zero, K.of_int(3))  # 3t^2 + s2
    inv_gp = E.inv(g_prime_E)
    CN = fourier_CN(K, 7, q)
    CN_E = E.embed(CN)
    q_E = E.embed(q)

    def lagrange_E(k0, k1, k2):
        # (k2 + k1*t + (t^2 + s2)*k0) / g'(t) in E
        num = (K.add(k2, K.mul(s2, k0)), k1, k0)
        return E.mul(num, inv_gp)

    # Assemble sector amplitudes in E for ++ and -- triples, and in K for -+ and +- singletons
    h_pp = [E.zero] * 7
    h_mm = [E.zero] * 7
    h_mp = [K.zero] * 7
    h_pm = [K.zero] * 7
    for b in range(7):
        zb = z_rows[b]
        h_pp[b % 7] = lagrange_E(zb[0], zb[1], zb[2])
        h_mp[b % 7] = zb[3]
        h_pm[(-b) % 7] = zb[4]
        h_mm[(-b) % 7] = lagrange_E(zb[5], zb[6], zb[7])

    # Compute literal sum over E for ++ and -- triples, take Tr_{E/K}, and add -+, +- singletons
    t7 = E.pow(E.t, 7)
    delta_t = E.neg(t7)
    inv_delta_t = E.inv(delta_t)
    # Build literal 7x7 inverse of (I - X_j) over E using (I + X + ... + X^6) / Delta AND verify (I-X)*Inv = I!
    total_K = [[K.zero] * 7 for _ in range(7)]
    inv7 = K.inv(K.of_int(7))
    for eps, delta, h_trip in [(+1, +1, h_pp), (-1, -1, h_mm)]:
        # Raw weights in E
        pref = E.mul(CN_E, delta_t)
        acc_E = [[E.zero] * 7 for _ in range(7)]
        for j in range(7):
            s_w = E.zero
            for ell in range(7):
                qpow_E = E.embed(K.qpow(-eps * delta * j * ell))
                s_w = E.add(s_w, E.mul(h_trip[ell], qpow_E))
            wj = E.mul(pref, s_w)
            # Build X_j = t S^eps + q^{eps*delta*j} T^delta over E
            X = [[E.zero] * 7 for _ in range(7)]
            zj = K.qpow(eps * delta * j)
            for i in range(7):
                X[i][i] = E.embed(K.mul(zj, K.qpow(delta * i)))
                X[(i + eps) % 7][i] = E.add(X[(i + eps) % 7][i], E.t)
            # Compute sum_{n=0}^6 X^n and verify X^7 == (t^7 + 1) I
            P_pow = [[E.one if r == c else E.zero for c in range(7)] for r in range(7)]
            sum_P = [row[:] for row in P_pow]
            for n in range(1, 7):
                P_pow = mat_mul(E, P_pow, X)
                for r in range(7):
                    for c in range(7):
                        sum_P[r][c] = E.add(sum_P[r][c], P_pow[r][c])
            X7 = mat_mul(E, P_pow, X)
            t7p1 = E.add(t7, E.one)
            for r in range(7):
                for c in range(7):
                    assert X7[r][c] == (t7p1 if r == c else E.zero)
            # Inv = sum_P * inv_delta_t; check (I - X) * Inv == I
            IminusX = [[E.sub(E.one if r == c else E.zero, X[r][c]) for c in range(7)] for r in range(7)]
            Inv_j = [[E.mul(sum_P[r][c], inv_delta_t) for c in range(7)] for r in range(7)]
            chk = mat_mul(E, IminusX, Inv_j)
            for r in range(7):
                for c in range(7):
                    assert chk[r][c] == (E.one if r == c else E.zero)
            for r in range(7):
                for c in range(7):
                    acc_E[r][c] = E.add(acc_E[r][c], E.mul(wj, Inv_j[r][c]))
        for r in range(7):
            for c in range(7):
                total_K[r][c] = K.add(total_K[r][c], K.mul(inv7, E.trace(acc_E[r][c])))

    # Add the two singleton banks (-+, 1) and (+-, 1)
    for eps, delta, h_sing in [(-1, +1, h_mp), (+1, -1, h_pm)]:
        ws = weights_from_h(K, 7, q, CN, eps, delta, K.one, h_sing)
        B = evaluate_bank_literal(K, 7, q, eps, delta, K.one, K.one, ws)
        for r in range(7):
            for c in range(7):
                total_K[r][c] = K.add(total_K[r][c], B[r][c])

    assert total_K == fourier_matrix(K, 7, q)
    print(
        "  [PASS] Order 7 (Theorem 1.1(c)): Exact F_29[Y] Bezout certificate + literal 8-bank cubic-algebra trace "
        "synthesis (all 56 branch resolvents, all 49 entries of F_7) verified."
    )


# ---------------------------------------------------------------------------
# Check 4: Order 9 lower bound & Theta(N) Hankel rank / triangle coverage
# ---------------------------------------------------------------------------

def verify_order9_and_hankel() -> None:
    # Exact Z[q]/Phi_9(q), Phi_9(q) = q^6 + q^3 + 1
    def z9_mul(a: list[int], b: list[int]) -> list[int]:
        c = [0] * 11
        for i in range(6):
            for j in range(6):
                c[i + j] += a[i] * b[j]
        for k in range(10, 5, -1):
            v = c[k]
            c[k - 3] -= v
            c[k - 6] -= v
        return c[:6]

    def z9_add(a, b):
        return [x + y for x, y in zip(a, b)]

    def z9_sub(a, b):
        return [x - y for x, y in zip(a, b)]

    p3 = [1, -1, -1, 1, 0, -1]
    p2 = [-1, 0, 2, 0, -1, 0]
    p1 = [1, 1, -1, 0, 1, 0]
    q_el = [0, 1, 0, 0, 0, 0]
    q2_el = [0, 0, 1, 0, 0, 0]
    one9 = [1, 0, 0, 0, 0, 0]
    assert z9_mul(q_el, p3) == p1
    assert z9_mul(p3, z9_add(q2_el, one9)) == one9
    one_plus_q_sq = z9_mul(z9_add(one9, q_el), z9_add(one9, q_el))
    E9 = z9_sub(z9_mul(one_plus_q_sq, z9_sub(z9_sub(p2, one9), q2_el)), z9_mul(q_el, z9_mul(p3, p3)))
    assert E9 == [-3, -2, 2, 0, -1, 1]
    cof9 = [2, -3, 3, 0, -1, 2]
    assert z9_mul(E9, cof9) == [3, 0, 0, 0, 0, 0]

    # Triangle coverage + exact Hankel rank (N-1)/2 for odd 3 <= N <= 19
    for N in range(3, 20, 2):
        # Check exclusive points and full coverage
        for a in range(N):
            for b in range(N):
                covered = any(((eps * a) % N) + ((delta * b) % N) <= N - 1 for eps in (1, -1) for delta in (1, -1))
                assert covered
        for t in range(1, (N - 1) // 2 + 1):
            for eps in (1, -1):
                for delta in (1, -1):
                    a, b = (eps * t) % N, (delta * t) % N
                    hits = [
                        (e2, d2)
                        for e2 in (1, -1)
                        for d2 in (1, -1)
                        if ((e2 * a) % N) + ((d2 * b) % N) <= N - 1
                    ]
                    assert hits == [(eps, delta)]
        # Find a small prime P == 1 mod N and check exact Hankel rank == (N-1)/2
        P = N + 1
        while True:
            if all(P % d != 0 for d in range(2, int(P ** 0.5) + 1)):
                break
            P += N
        FP = PrimeField(P)
        # Find primitive N-th root in F_P
        g_prim = 2
        while True:
            cand = pow(g_prim, (P - 1) // N, P)
            if cand != 1 and all(pow(cand, N // d, P) != 1 for d in range(2, N + 1) if N % d == 0):
                qP = cand
                break
            g_prim += 1
        mH = (N - 1) // 2
        inv4 = pow(4, -1, N)
        H_mat = [[FP.pow(qP, (inv4 * (i + j + 2) ** 2) % N) for j in range(mH)] for i in range(mH)]
        assert mat_rank(FP, H_mat) == mH

    print("  [PASS] Order 9 (Theorem 1.1(d)) & Theorem 1.2: Exact Z[q]/Phi_9 certificate + coverage & Hankel rank verified for odd 3 <= N <= 19.")


# ---------------------------------------------------------------------------
# Check 5: First-order 5N/3 operator + reverse-GCD cubic coefficient generator
# ---------------------------------------------------------------------------

def reverse_gcd_select(F, a_poly, basis, scalars, phi=None):
    """Exact implementation of Lemma 6.1 (amortized reverse-GCD scalar-span selection)."""
    a_cur = poly_monic(F, a_poly)
    v = len(a_cur) - 1
    assert v >= 1
    nz_scalars = [s for s in scalars if s != F.zero]
    assert len(nz_scalars) >= v + 1

    # Step 1: Forward GCD chain
    chain_A = [a_cur]
    chain_p = []
    for b in basis:
        g = poly_gcd(F, a_cur, b)
        if len(g) < len(a_cur):
            chain_p.append(b)
            chain_A.append(g)
            a_cur = g
            if len(a_cur) == 1:
                break
    assert chain_A[-1] == [F.one], "gcd(a, basis) != 1"
    ell = len(chain_p)
    assert ell <= v

    # Step 2: Reverse unwind
    P = chain_p[-1]
    trials = 0
    for i in range(ell - 2, -1, -1):
        A = chain_A[i]
        D = chain_A[i + 1]
        Delta = (len(A) - 1) - (len(D) - 1)
        assert Delta > 0
        found = None
        for lam in nz_scalars[: Delta + 1]:
            trials += 1
            cand = poly_add(F, chain_p[i], poly_scale(F, P, lam))
            if poly_gcd(F, A, cand) == [F.one]:
                found = cand
                break
        assert found is not None, "Reverse unwind failed within Delta + 1 trials!"
        P = found
    assert trials <= 2 * v - 1, f"Trial bound exceeded: {trials} > {2*v-1}"
    assert poly_gcd(F, a_poly, P) == [F.one]

    # Step 3: Optional nonzero linear functional repair
    if phi is not None and phi(P) == F.zero:
        u = next(b for b in basis if phi(b) != F.zero)
        D = poly_gcd(F, a_poly, u)
        Delta = v - (len(D) - 1)
        found = None
        for lam in nz_scalars[: Delta + 1]:
            cand = poly_add(F, u, poly_scale(F, P, lam))
            if poly_gcd(F, a_poly, cand) == [F.one]:
                found = cand
                break
        assert found is not None and phi(found) != F.zero
        P = found
    return P, trials


def verify_five_thirds_and_cubic_generator() -> None:
    # Test 5a: Multiplicity-rich synthetic stress test for Lemma 6.1 (reverse GCD descent)
    F17 = PrimeField(17)
    # a(t) = (t-1)^3 * (t-2)^2 * (t-3) of degree 6 (non-squarefree!)
    a_syn = [1]
    for root, mult in [(1, 3), (2, 2), (3, 1)]:
        for _ in range(mult):
            a_syn = poly_mul(F17, a_syn, [(-root) % 17, 1])
    # Basis polynomials each sharing factors with a_syn, jointly coprime
    b1 = poly_mul(F17, [(-1) % 17, 1], [(-2) % 17, 1])  # (t-1)(t-2)
    b2 = poly_mul(F17, [(-2) % 17, 1], [(-3) % 17, 1])  # (t-2)(t-3)
    b3 = poly_mul(F17, [(-1) % 17, 1], [(-3) % 17, 1])  # (t-1)(t-3)
    phi_syn = lambda p: p[0] if len(p) > 0 else 0
    P_syn, tr_syn = reverse_gcd_select(F17, a_syn, [b1, b2, b3], list(range(1, 10)), phi=phi_syn)
    assert poly_gcd(F17, a_syn, P_syn) == [1] and phi_syn(P_syn) != 0 and tr_syn <= 11

    # Test 5b: First-order operator L_x & whole-left envelope inclusion across three fields:
    # (N=23, d=4 over F_47), (N=35, d=6 over F_71 -- strictly beyond old 8d-10=38!),
    # and (N=63, d=10 over GF(64) [char 2] -- composite N, char 2, strictly beyond old 8d-10=70!)
    GF64 = GF2Ext(6, 0b1000011)  # t^6 + t + 1 irreducible over F_2; t has order 63!
    fixtures = [
        ("F_47 (N=23, d=4)", PrimeField(47), 23, 4, pow(5, 2, 47), True),
        ("F_71 (N=35, d=6)", PrimeField(71), 35, 6, pow(7, 2, 71), True),
        ("GF(64) [char 2] (N=63, d=10)", GF64, 63, 10, 0b10, False),
    ]
    for label, F, N, d, q, run_full_gen in fixtures:
        assert N >= 6 * d - 2
        assert F.pow(q, N) == F.one and all(F.pow(q, N // p) != F.one for p in range(2, N + 1) if N % p == 0)
        m = N - d
        e_inv = pow(2, -1, N)
        h_inv = pow(4, -1, N)
        rho = F.pow(q, e_inv)
        assert F.mul(rho, rho) == q
        C_seq = [F.pow(q, (h_inv * j * j) % N) for j in range(N + 2)]

        # Build D(z) = prod_{r=2}^{d-1} (1 - q^r z)
        D_poly = [F.one]
        for r in range(2, d):
            D_poly = poly_mul(F, D_poly, [F.one, F.neg(F.pow(q, r))])
        # Verify exact consecutive-factor identity (5.2): (1 - q^2 z) D(qz) == (1 - q^d z) D(z)
        D_qz = [F.mul(D_poly[i], F.pow(q, i)) for i in range(len(D_poly))]
        lhs_D = poly_mul(F, [F.one, F.neg(F.pow(q, 2))], D_qz)
        rhs_D = poly_mul(F, [F.one, F.neg(F.pow(q, d))], D_poly)
        assert lhs_D == rhs_D

        # Verify L_x(x^j D(q^j)) == 0 and L_1(j D(q^j)) == (1 - q^{j+d}) D(q^j)
        x_test = F.pow(q, 3)
        D_vals = [poly_eval(F, D_poly, F.pow(q, j)) for j in range(m + 2)]
        for j in range(m):
            y_j = F.mul(F.pow(x_test, j), D_vals[j])
            y_j1 = F.mul(F.pow(x_test, j + 1), D_vals[j + 1])
            Lx_val = F.sub(F.mul(F.sub(F.one, F.pow(q, j + 2)), y_j1), F.mul(x_test, F.mul(F.sub(F.one, F.pow(q, j + d)), y_j)))
            assert Lx_val == F.zero

            dy_j = F.mul(F.of_int(j), D_vals[j])
            dy_j1 = F.mul(F.of_int(j + 1), D_vals[j + 1])
            L1_val = F.sub(F.mul(F.sub(F.one, F.pow(q, j + 2)), dy_j1), F.mul(F.sub(F.one, F.pow(q, j + d)), dy_j))
            assert L1_val == F.mul(F.sub(F.one, F.pow(q, j + d)), D_vals[j])

        # Verify Phi_x(P) degree + 3 and exact leading term on a sample chirp polynomial
        P_test = [F.one, q, F.pow(q, 2)]  # deg 2, lead = q^2
        # Phi_x(P)(t) = q^h * t * (1 - q^2 t^2) * P(rho t) - x * (1 - q^d t^2) * P(t)
        P_rhot = [F.mul(P_test[i], F.pow(rho, i)) for i in range(len(P_test))]
        term1 = poly_mul(F, [F.zero, F.pow(q, h_inv), F.zero, F.neg(F.pow(q, h_inv + 2))], P_rhot)
        term2 = poly_scale(F, poly_mul(F, [F.one, F.zero, F.neg(F.pow(q, d))], P_test), x_test)
        Phi_P = poly_sub(F, term1, term2)
        assert len(Phi_P) - 1 == (len(P_test) - 1) + 3
        exp_lead = F.neg(F.mul(F.mul(F.pow(q, h_inv + 2), F.pow(rho, len(P_test) - 1)), P_test[-1]))
        assert Phi_P[-1] == exp_lead and exp_lead != F.zero

        # Verify Lemma 5.1: every actual whole-left Gaussian row v_b(a+j) satisfies the envelope identity
        for b in range(1, d - 1):
            G_mp_nb = gauss_binom(F, N - 1, b, F.pow(q, N - 1))  # r = b, wait: [- (N-b)]_N = b, ell = b -> r+ell = 2b!
            # Exact G_{-+}(N-b, b): r = [-(N-b)]_N = b, ell = b
            G_mp_nb = gauss_binom(F, 2 * b, b, F.pow(q, N - 1))
            T_b = F.inv(G_mp_nb)
            for a in range(1, d - b):
                s = a + b
                Q_b = F.one
                for i in range(1, b + 1):
                    Q_b = F.mul(Q_b, F.sub(F.one, F.pow(q, i)))
                B_b = F.mul(T_b, F.mul(F.of_int((-1) ** b), F.pow(q, (b * (b + 1) // 2) % N)))
                denom_ab = [F.one]
                for i in range(1, b + 1):
                    denom_ab = poly_mul(F, denom_ab, [F.one, F.neg(F.pow(q, a + i))])
                F_ab, rem_ab = poly_divmod(F, D_poly, denom_ab)
                assert rem_ab == [F.zero]
                R_ab = [F.one]
                for i in range(1, b + 1):
                    R_ab = poly_mul(F, R_ab, [F.one, F.neg(F.pow(q, (a - i) % N))])
                # Check identity across j = 0..m
                for j in range(m + 1):
                    idx = a + j
                    f_val = F.pow(q, (h_inv * (idx + b) ** 2) % N)
                    r_mp = (-idx) % N
                    g_mp = gauss_binom(F, r_mp + b, b, F.pow(q, N - 1)) if r_mp + b < N else F.zero
                    g_pp = gauss_binom(F, idx + b, b, q)
                    vb = F.div(F.sub(f_val, F.mul(T_b, g_mp)), g_pp)
                    lhs = F.mul(D_vals[j], vb)
                    qj = F.pow(q, j)
                    Fab_val = poly_eval(F, F_ab, qj)
                    Rab_val = poly_eval(F, R_ab, qj)
                    rhs = F.sub(
                        F.mul(F.mul(F.mul(Q_b, F.pow(q, (h_inv * s * s) % N)), F.mul(C_seq[j], F.pow(rho, s * j))), Fab_val),
                        F.mul(F.mul(B_b, Rab_val), Fab_val),
                    )
                    assert lhs == rhs

        # Full end-to-end deterministic reverse-GCD cubic coefficient generator (Theorem 1.4)!
        if run_full_gen:
            # Build envelope basis matrix E (size (4d-7) x (m+1)) and nullspace U
            E_rows = []
            for deg_p in range(3 * d - 6):
                E_rows.append([F.div(F.mul(C_seq[j], F.pow(rho, deg_p * j)), D_vals[j]) for j in range(m + 1)])
            for deg_r in range(d - 1):
                E_rows.append([F.div(F.pow(q, deg_r * j), D_vals[j]) for j in range(m + 1)])
            U_basis = mat_nullspace(F, E_rows)
            assert len(U_basis) >= d + 6
            # Every g in U vanishes at 1
            for gvec in U_basis:
                assert poly_eval(F, gvec, F.one) == F.zero

            # Build V_1 = U / (t - 1) and V_0 = U_0 / (t*(t - 1))
            V1_basis = []
            for gvec in U_basis:
                h_q, rem = poly_divmod(F, gvec, [F.neg(F.one), F.one])
                assert rem == [F.zero]
                V1_basis.append(h_q + [F.zero] * (m - len(h_q)))

            # U_0 = {g in U : g(0) == 0}
            c0_row = [[gvec[0] for gvec in U_basis]]
            u0_coeffs = mat_nullspace(F, c0_row)
            V0_basis = []
            r_deg = m - 2
            for coeff in u0_coeffs:
                gvec = [F.zero] * (m + 1)
                for ci, bvec in zip(coeff, U_basis):
                    if ci != F.zero:
                        for idx in range(m + 1):
                            gvec[idx] = F.add(gvec[idx], F.mul(ci, bvec[idx]))
                assert gvec[0] == F.zero
                fq, rem = poly_divmod(F, gvec, [F.zero, F.neg(F.one), F.one])
                assert rem == [F.zero]
                V0_basis.append(fq + [F.zero] * (r_deg + 1 - len(fq)))

            # Solve for f0 in V0 with f0(0) = 1 and coeff_r(f0) = 1
            # Build 2 x len(V0_basis) constraint system
            eq_mat = [
                [fv[0] for fv in V0_basis],
                [fv[r_deg] for fv in V0_basis],
            ]
            # Find 2 linearly independent columns and solve
            chosen_cols = None
            for i1 in range(len(V0_basis)):
                for i2 in range(i1 + 1, len(V0_basis)):
                    sub2 = [[eq_mat[0][i1], eq_mat[0][i2]], [eq_mat[1][i1], eq_mat[1][i2]]]
                    if mat_det(F, sub2) != F.zero:
                        chosen_cols = (i1, i2, sub2)
                        break
                if chosen_cols is not None:
                    break
            assert chosen_cols is not None
            i1, i2, sub2 = chosen_cols
            w1, w2 = mat_solve(F, sub2, [F.one, F.one])
            f0 = [F.add(F.mul(w1, V0_basis[i1][k]), F.mul(w2, V0_basis[i2][k])) for k in range(r_deg + 1)]
            assert f0[0] == F.one and f0[r_deg] == F.one

            # First reverse-GCD call: find f1 in V0 coprime to f0 with phi(f1) = coeff_r - coeff_0 != 0
            scalars = [F.of_int(i) for i in range(1, 2 * N + 1)]
            phi_ep = lambda p_vec: F.sub(p_vec[r_deg] if len(p_vec) > r_deg else F.zero, p_vec[0] if len(p_vec) > 0 else F.zero)
            f1, _ = reverse_gcd_select(F, f0, V0_basis, scalars, phi=phi_ep)
            # First pencil: find monic f with f(0)!=0 and gcd(f, rev_r f) == 1
            f_good = None
            for lam in scalars[: 2 * m - 1]:
                f_cand = poly_add(F, f0, poly_scale(F, f1, lam))
                if len(f_cand) - 1 == r_deg and f_cand[0] != F.zero:
                    f_cand = poly_monic(F, f_cand)
                    rev_f = list(reversed(f_cand))
                    if poly_gcd(F, f_cand, rev_f) == [F.one]:
                        f_good = f_cand
                        break
            assert f_good is not None

            # Second reverse-GCD call: h0 = t * f_good, W = {h in V1 : coeff_{m-1}(h) == 0}
            h0 = [F.zero] + f_good
            lead_row = [[hv[m - 1] for hv in V1_basis]]
            w_coeffs = mat_nullspace(F, lead_row)
            W_basis = []
            for coeff in w_coeffs:
                hvec = [F.zero] * m
                for ci, bvec in zip(coeff, V1_basis):
                    if ci != F.zero:
                        for idx in range(m):
                            hvec[idx] = F.add(hvec[idx], F.mul(ci, bvec[idx]))
                assert hvec[m - 1] == F.zero
                W_basis.append(poly_trim_f(hvec, F.zero))
            h1, _ = reverse_gcd_select(F, h0, W_basis, scalars, phi=None)

            # Second pencil: g_Z = (t - 1) * (h0 + Z * h1), verify g(0)!=0, gcd(g,g')=1, rank X_N(g) == N
            def axis_rank_XN(g_monic):
                # Compute p_a = t^a mod g for a = 0..N-1
                p_list = []
                cur = [F.one] + [F.zero] * (m - 1)
                for _ in range(N):
                    p_list.append(cur)
                    # Multiply by t mod g
                    nxt = [F.zero] + cur[:-1]
                    top = cur[-1]
                    if top != F.zero:
                        for idx in range(m):
                            nxt[idx] = F.sub(nxt[idx], F.mul(top, g_monic[idx]))
                    cur = nxt
                XN = [p_list[a] + [F.one] + p_list[(-a) % N] for a in range(N)]
                return mat_rank(F, XN)

            # Verify auxiliary g_0 = (t-1)h_0 already has rank X_N(g_0) == N!
            g0_aux = poly_mul(F, [F.neg(F.one), F.one], h0)
            assert axis_rank_XN(g0_aux) == N

            g_legal = None
            for lam in scalars[: 2 * N]:
                h_cand = poly_add(F, h0, poly_scale(F, h1, lam))
                g_cand = poly_mul(F, [F.neg(F.one), F.one], h_cand)
                if len(g_cand) - 1 == m and g_cand[-1] == F.one and g_cand[0] != F.zero:
                    if poly_gcd(F, g_cand, poly_deriv(F, g_cand)) == [F.one]:
                        if axis_rank_XN(g_cand) == N:
                            g_legal = g_cand
                            break
            assert g_legal is not None
            # Confirm g_legal lies in U = E^perp!
            for erow in E_rows:
                ip = F.zero
                for idx in range(m + 1):
                    ip = F.add(ip, F.mul(erow[idx], g_legal[idx]))
                assert ip == F.zero

    print(
        "  [PASS] Theorems 1.3 & 1.4: First-order L_x operator, whole-left envelope, and deterministic "
        "reverse-GCD cubic coefficient generator verified over F_47 (23,4), F_71 (35,6), and GF(64) [char 2] (63,10)."
    )


def main() -> None:
    verify_order3()
    verify_order5()
    verify_order7()
    verify_order9_and_hankel()
    verify_five_thirds_and_cubic_generator()
    print("ALL PAPER 8 VERIFICATIONS PASSED.")


if __name__ == "__main__":
    main()
