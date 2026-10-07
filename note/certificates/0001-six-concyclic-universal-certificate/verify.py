"""Certificate 0001: a universal tensor certificate for six concyclic points.

Standard library only; exact arithmetic over fractions.Fraction; no assert statements.

Setting. Six points on a circle with centre c = (c1, c2) are written through a base point
b = (b1, b2) on the circle: the directions x_i = (u_i, w_i), i = 1..5, give the points
b + t x_i (t = -2<e, x_i>/|x_i|^2, e = b - c), and the sixth direction is the tangent
x_6 = (-(b2 - c2), b1 - c1), which stands for the base point itself. The homogeneous point is
p(x) = (|x|^2, |x|^2 b - 2<e, x> x) = Lambda v(x), v(x) = (u^2, uw, w^2).

Two copies of the 14 parameters (left = "s (x) 1", right = "1 (x) s") give 28 symbols. A
polynomial identity in Q[left, right] specialises, by the ring map sending a left symbol to
s (x) 1 and a right symbol to 1 (x) s, to an identity in F (x)_Q F for every field F; the
multiplication map m sends both copies to the same symbol.

Checks.
 (i)   p(x) = Lambda v(x) identically; Lambda^T H Lambda = -2 rho^2 K, rho^2 = |b - c|^2,
       K = [[0,0,1],[0,-2,0],[1,0,0]], H the circle form; det Lambda = 4 rho^2.
 (ii)  ell_{012}(x_i^L, x_i^R) = 0 for i in {0,1,2} and ell_{345}(x_i^L, x_i^R) = 0 for
       i in {3,4,5}, as polynomial identities (4x4 determinants expanded).
 (iii) m(q) = c (X1 Y2 - X2 Y1)^2, q = ell_{012} ell_{345}, c = V_{012} V_{345} with
       V_S = prod_{j<k in S} (U_j W_k - U_k W_j) (explicit bracket product).
 (iv)  end to end at 12 independent random rational specialisations of all 28 symbols:
       P = (kappa/c) Lambda_L^{-T} Q Lambda_R^{-1}, kappa = -2 rho^2: all six evaluation
       identities are exactly 0, and with right := left, m(P) = H (spatial block I).
 Forged controls (expected to FAIL): q' = ell_{012} ell_{013} at the point 4; a perturbed Lambda
 in (i).
"""
import sys
import random
import itertools
import time
from fractions import Fraction

T0 = time.time()
FAILURES = []


def check(ok, msg):
    if ok:
        print("  ok   " + msg)
    else:
        print("  FAIL " + msg)
        FAILURES.append(msg)


# ---------------------------------------------------------------- polynomials
NAMES = ["b1", "b2", "c1", "c2"] + ["u%d" % i for i in range(1, 6)] + ["w%d" % i for i in range(1, 6)]
NL = len(NAMES)                      # 14 symbols per copy
NV = 2 * NL + 4                      # left, right, X1 X2 Y1 Y2
IX1, IX2, IY1, IY2 = 2 * NL, 2 * NL + 1, 2 * NL + 2, 2 * NL + 3
ZERO_EXP = (0,) * NV


class Poly:
    """Sparse multivariate polynomial: dict exponent tuple -> Fraction (no zero coefficients)."""
    __slots__ = ("t",)

    def __init__(self, t=None):
        self.t = {} if t is None else {k: v for k, v in t.items() if v != 0}

    @staticmethod
    def const(c):
        return Poly({ZERO_EXP: Fraction(c)})

    @staticmethod
    def var(i):
        e = [0] * NV
        e[i] = 1
        return Poly({tuple(e): Fraction(1)})

    def __add__(self, o):
        o = lift(o)
        r = dict(self.t)
        for k, v in o.t.items():
            r[k] = r.get(k, 0) + v
        return Poly(r)

    __radd__ = __add__

    def __neg__(self):
        return Poly({k: -v for k, v in self.t.items()})

    def __sub__(self, o):
        return self + (-lift(o))

    def __rsub__(self, o):
        return lift(o) - self

    def __mul__(self, o):
        o = lift(o)
        r = {}
        for k1, v1 in self.t.items():
            for k2, v2 in o.t.items():
                k = tuple(a + b for a, b in zip(k1, k2))
                r[k] = r.get(k, 0) + v1 * v2
        return Poly(r)

    __rmul__ = __mul__

    def is_zero(self):
        return len(self.t) == 0

    def __eq__(self, o):
        return (self - lift(o)).is_zero()

    def __hash__(self):
        return id(self)

    def nterms(self):
        return len(self.t)

    def evaluate(self, vals):
        """vals: dict var index -> Fraction; every variable that occurs must be given."""
        s = Fraction(0)
        for k, v in self.t.items():
            term = v
            for i, e in enumerate(k):
                if e:
                    term *= vals[i] ** e
            s += term
        return s

    def subs(self, mp):
        """Substitute polynomials for some variables (simultaneous)."""
        cache = {}
        out = Poly()
        for k, v in self.t.items():
            base = list(k)
            term = Poly({ZERO_EXP: v})
            for i, p in mp.items():
                e = k[i]
                base[i] = 0
                if e:
                    key = (i, e)
                    if key not in cache:
                        acc = Poly.const(1)
                        for _ in range(e):
                            acc = acc * p
                        cache[key] = acc
                    term = term * cache[key]
            term = term * Poly({tuple(base): Fraction(1)})
            out = out + term
        return out

    def mult_map(self):
        """m: identify each right symbol with its left copy."""
        r = {}
        for k, v in self.t.items():
            e = list(k)
            for i in range(NL):
                e[i] += e[NL + i]
                e[NL + i] = 0
            kk = tuple(e)
            r[kk] = r.get(kk, 0) + v
        return Poly(r)


def lift(o):
    return o if isinstance(o, Poly) else Poly.const(o)


def det(M):
    """Determinant by permutation expansion (small n); entries Poly or Fraction."""
    n = len(M)
    total = 0
    for perm in itertools.permutations(range(n)):
        inv = sum(1 for a in range(n) for b in range(a + 1, n) if perm[a] > perm[b])
        term = -1 if inv % 2 else 1
        for r in range(n):
            term = term * M[r][perm[r]]
        total = total + term
    return total


def matmul(A, B):
    return [[sum((A[i][k] * B[k][j] for k in range(len(B))), Fraction(0) if not isinstance(A[0][0], Poly) else Poly())
             for j in range(len(B[0]))] for i in range(len(A))]


def transpose(A):
    return [list(r) for r in zip(*A)]


# ---------------------------------------------------------------- the configuration
def copy_syms(side):
    off = 0 if side == "L" else NL
    s = {nm: Poly.var(off + i) for i, nm in enumerate(NAMES)}
    return s


def config(s):
    b1, b2, c1, c2 = s["b1"], s["b2"], s["c1"], s["c2"]
    e1, e2 = b1 - c1, b2 - c2
    xs = [(s["u%d" % i], s["w%d" % i]) for i in range(1, 6)] + [(-e2, e1)]
    rho2 = e1 * e1 + e2 * e2
    lam = [[Poly.const(1), Poly.const(0), Poly.const(1)],
           [b1 - 2 * e1, -2 * e2, b1],
           [b2, -2 * e1, b2 - 2 * e2]]
    H = [[c1 * c1 + c2 * c2 - rho2, -c1, -c2], [-c1, Poly.const(1), Poly.const(0)], [-c2, Poly.const(0), Poly.const(1)]]
    return dict(b=(b1, b2), c=(c1, c2), e=(e1, e2), xs=xs, rho2=rho2, Lam=lam, H=H)


def p_of(C, x):
    u, w = x
    e1, e2 = C["e"]
    b1, b2 = C["b"]
    n2 = u * u + w * w
    dot = e1 * u + e2 * w
    return [n2, n2 * b1 - 2 * dot * u, n2 * b2 - 2 * dot * w]


def ver(x):
    u, w = x
    return [u * u, u * w, w * w]


K = [[0, 0, 1], [0, -2, 0], [1, 0, 0]]
SL, SR = copy_syms("L"), copy_syms("R")
CL, CR = config(SL), config(SR)
X1, X2, Y1, Y2 = Poly.var(IX1), Poly.var(IX2), Poly.var(IY1), Poly.var(IY2)


def check_i(C, Lam, label):
    """(i): parametrisation, pullback of the circle form, determinant."""
    ok = True
    pv = p_of(C, (X1, X2))
    vv = ver((X1, X2))
    for r in range(3):
        if not (pv[r] == sum((Lam[r][k] * vv[k] for k in range(3)), Poly())):
            ok = False
    G = matmul(matmul(transpose(Lam), C["H"]), Lam)
    for a in range(3):
        for b in range(3):
            if not (G[a][b] == -2 * C["rho2"] * K[a][b]):
                ok = False
    return ok


print("check (i): parametrisation and circle form")
check(check_i(CL, CL["Lam"], "L"), "p(x) = Lambda v(x) and Lambda^T H Lambda = -2 rho^2 K (left copy)")
check(check_i(CR, CR["Lam"], "R"), "p(x) = Lambda v(x) and Lambda^T H Lambda = -2 rho^2 K (right copy)")
check(det(CL["Lam"]) == 4 * CL["rho2"], "det Lambda = 4 rho^2")
pt = p_of(CL, CL["xs"][5])
check(pt[1] == pt[0] * CL["b"][0] and pt[2] == pt[0] * CL["b"][1] and pt[0] == CL["rho2"],
      "tangent direction gives p(x_6) = rho^2 (1, b)")
# each p_i lies on the circle: p^T H p = 0
okc = True
for x in CL["xs"]:
    p = p_of(CL, x)
    val = sum((p[a] * CL["H"][a][b] * p[b] for a in range(3) for b in range(3)), Poly())
    okc = okc and val.is_zero()
check(okc, "each p(x_i) lies on the circle form H (p^T H p = 0), i = 1..6")
print("  [%.1fs]" % (time.time() - T0))

# forged control 1: perturbed Lambda must break (i)
print("forged control: perturbed Lambda (entry (0,0) + 1)")
LamBad = [list(r) for r in CL["Lam"]]
LamBad[0][0] = LamBad[0][0] + 1
forged_lambda_passes = check_i(CL, LamBad, "L-forged")
print("  perturbed Lambda passes (i): %s (expected False)" % forged_lambda_passes)
check(not forged_lambda_passes, "forged control (perturbed Lambda) is rejected")


# ---------------------------------------------------------------- the (1,1)-forms
def ell(S):
    rows = [[X1 * Y1, X1 * Y2, X2 * Y1, X2 * Y2]]
    for j in S:
        xl, xr = CL["xs"][j], CR["xs"][j]
        rows.append([xl[0] * xr[0], xl[0] * xr[1], xl[1] * xr[0], xl[1] * xr[1]])
    return det(rows)


def at_point(f, i):
    xl, xr = CL["xs"][i], CR["xs"][i]
    return f.subs({IX1: xl[0], IX2: xl[1], IY1: xr[0], IY2: xr[1]})


l1 = ell((0, 1, 2))
l2 = ell((3, 4, 5))
print("check (ii): the (1,1)-forms vanish at their own points  [ell_012: %d terms, ell_345: %d terms]"
      % (l1.nterms(), l2.nterms()))
for i in (0, 1, 2):
    check(at_point(l1, i).is_zero(), "ell_012(x_%d^L, x_%d^R) = 0" % (i, i))
for i in (3, 4, 5):
    check(at_point(l2, i).is_zero(), "ell_345(x_%d^L, x_%d^R) = 0" % (i, i))
check(not l1.is_zero() and not l2.is_zero(), "ell_012 and ell_345 are nonzero polynomials")
print("  [%.1fs]" % (time.time() - T0))

q = l1 * l2
print("check (iii): m(q) = c (X1 Y2 - X2 Y1)^2  [q: %d terms]" % q.nterms())


def bracket_product(S):
    xs = CL["xs"]
    v = Poly.const(1)
    for a, b in itertools.combinations(S, 2):
        v = v * (xs[a][0] * xs[b][1] - xs[b][0] * xs[a][1])
    return v


cpoly = bracket_product((0, 1, 2)) * bracket_product((3, 4, 5))
delta = X1 * Y2 - X2 * Y1
mq = q.mult_map()
check(mq == cpoly * delta * delta, "m(q) = V_012 V_345 (X1 Y2 - X2 Y1)^2 as a polynomial identity")
check(l1.mult_map() == -1 * bracket_product((0, 1, 2)) * delta, "m(ell_012) = -V_012 (X1 Y2 - X2 Y1)")
check(l2.mult_map() == -1 * bracket_product((3, 4, 5)) * delta, "m(ell_345) = -V_345 (X1 Y2 - X2 Y1)")
print("  [%.1fs]" % (time.time() - T0))

# Q: the 3x3 matrix of q in v(X) = (X1^2, X1 X2, X2^2), v(Y)
Qm = [[Poly() for _ in range(3)] for _ in range(3)]
bideg_ok = True
for k, v in q.t.items():
    ex = (k[IX1], k[IX2])
    ey = (k[IY1], k[IY2])
    if sum(ex) != 2 or sum(ey) != 2:
        bideg_ok = False
        continue
    base = list(k)
    base[IX1] = base[IX2] = base[IY1] = base[IY2] = 0
    Qm[ex[1]][ey[1]] = Qm[ex[1]][ey[1]] + Poly({tuple(base): v})
check(bideg_ok, "q is bihomogeneous of bidegree (2,2) in X, Y")
vX, vY = ver((X1, X2)), ver((Y1, Y2))
check(sum((vX[a] * Qm[a][b] * vY[b] for a in range(3) for b in range(3)), Poly()) == q, "v(X)^T Q v(Y) = q")

# forged q' = ell_012 * ell_013: point 4 lies on neither triple
lf = ell((0, 1, 3))
qf = l1 * lf
forged_q_vanishes_at_4 = at_point(qf, 4).is_zero()
print("forged control: q' = ell_012 ell_013 vanishes at point 4: %s (expected False)" % forged_q_vanishes_at_4)
check(not forged_q_vanishes_at_4, "forged control (q' = ell_012 ell_013) is rejected symbolically")
Qf = [[Poly() for _ in range(3)] for _ in range(3)]
for k, v in qf.t.items():
    base = list(k)
    base[IX1] = base[IX2] = base[IY1] = base[IY2] = 0
    Qf[k[IX2]][k[IY2]] = Qf[k[IX2]][k[IY2]] + Poly({tuple(base): v})
print("  [%.1fs]" % (time.time() - T0))


# ---------------------------------------------------------------- (iv) end to end
def num_config(vals, off):
    g = lambda nm: vals[off + NAMES.index(nm)]
    b1, b2, c1, c2 = g("b1"), g("b2"), g("c1"), g("c2")
    e1, e2 = b1 - c1, b2 - c2
    xs = [(g("u%d" % i), g("w%d" % i)) for i in range(1, 6)] + [(-e2, e1)]
    rho2 = e1 * e1 + e2 * e2
    lam = [[Fraction(1), Fraction(0), Fraction(1)], [b1 - 2 * e1, -2 * e2, b1], [b2, -2 * e1, b2 - 2 * e2]]
    H = [[c1 * c1 + c2 * c2 - rho2, -c1, -c2], [-c1, Fraction(1), Fraction(0)], [-c2, Fraction(0), Fraction(1)]]
    pts = []
    for (u, w) in xs:
        n2 = u * u + w * w
        dot = e1 * u + e2 * w
        pts.append([n2, n2 * b1 - 2 * dot * u, n2 * b2 - 2 * dot * w])
    return dict(xs=xs, rho2=rho2, Lam=lam, H=H, pts=pts)


def inv3(A):
    d = det(A)
    if d == 0:
        return None
    adj = [[None] * 3 for _ in range(3)]
    for i in range(3):
        for j in range(3):
            minor = [[A[r][c] for c in range(3) if c != j] for r in range(3) if r != i]
            adj[j][i] = (-1) ** (i + j) * det(minor)
    return [[adj[i][j] / d for j in range(3)] for i in range(3)]


def build_P(vals, Qpolys, scal):
    L = num_config(vals, 0)
    R = num_config(vals, NL)
    LiL, LiR = inv3(L["Lam"]), inv3(R["Lam"])
    if LiL is None or LiR is None:
        return None
    Qn = [[Qpolys[a][b].evaluate(vals) for b in range(3)] for a in range(3)]
    P = matmul(matmul(transpose(LiL), Qn), LiR)
    return L, R, [[scal * P[a][b] for b in range(3)] for a in range(3)]


def eval_form(pl, P, pr):
    return sum(pl[a] * P[a][b] * pr[b] for a in range(3) for b in range(3))


print("check (iv): end to end at 12 independent random rational specialisations")
rng = random.Random(20261006)
trials = 0
draws = 0
forged_iv_rejections = 0
while trials < 12:
    draws += 1
    vals = {i: Fraction(rng.randint(-40, 40), rng.randint(1, 13)) for i in range(2 * NL)}
    cval = cpoly.evaluate(vals)
    if cval == 0:
        continue
    L0 = num_config(vals, 0)
    kappa = -2 * L0["rho2"]
    built = build_P(vals, Qm, kappa / cval)
    if built is None:
        continue
    L, R, P = built
    evals = [eval_form(L["pts"][i], P, R["pts"][i]) for i in range(6)]
    # multiplication: right := left
    same = dict(vals)
    for i in range(NL):
        same[NL + i] = vals[i]
    Ls, Rs, Ps = build_P(same, Qm, kappa / cval)
    mP_is_H = all(Ps[a][b] == Ls["H"][a][b] for a in range(3) for b in range(3))
    spatial_I = all(Ps[a][b] == (1 if a == b else 0) for a in (1, 2) for b in (1, 2))
    check(all(v == 0 for v in evals) and mP_is_H and spatial_I,
          "trial %2d: six evaluations exactly 0, m(P) = H, spatial block I" % (trials + 1))
    # forged q' through the same pipeline
    _, _, Pf = build_P(vals, Qf, kappa / cval)
    if eval_form(L["pts"][4], Pf, R["pts"][4]) != 0:
        forged_iv_rejections += 1
    trials += 1
print("  draws used: %d (a draw with c = 0 or det Lambda = 0 is redrawn)" % draws)
print("forged control: q' = ell_012 ell_013 fails the evaluation at point 4 in %d of 12 trials (expected 12)"
      % forged_iv_rejections)
check(forged_iv_rejections == 12, "forged control (q') is rejected end to end in every trial")
print("  [%.1fs]" % (time.time() - T0))

print("")
print("forged control 1 (perturbed Lambda): %s (expected FAIL)" % ("PASS" if forged_lambda_passes else "FAIL"))
print("forged control 2 (q' = ell_012 ell_013): %s (expected FAIL)"
      % ("PASS" if (forged_q_vanishes_at_4 or forged_iv_rejections < 12) else "FAIL"))
if FAILURES:
    print("%d check(s) failed" % len(FAILURES))
    print("VERDICT: FAIL")
    sys.exit(1)
print("VERDICT: PASS")
