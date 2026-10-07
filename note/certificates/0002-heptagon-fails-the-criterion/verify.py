"""Certificate 0002: a cyclic heptagon fails the tensor criterion (exact moment identities).

Standard library only; exact arithmetic over fractions.Fraction; no assert statements.

The seven points, for a transcendental real r > 2, are the origin and (j, +y_j), (j, -y_j) for
j = 1, 3, 4, where y_j^2 = j (2r - j). They lie on the circle (x - r)^2 + y^2 = r^2.

Ring. A = Q(r)[y1, y3, y4] / (y_j^2 - j (2r - j)): an element is a dict from monomials
(e1, e3, e4) in {0,1}^3 to coefficients in Q(r); a coefficient is a pair (numerator,
denominator) of polynomials in r with Fraction coefficients (lists, constant term first).
Zero is tested on the numerator only, so no gcd is needed.

Derivation. D is the derivation of the coordinate field extending d/dr: D(r) = 1, D(j) = 0,
and D(y_j) = j / y_j = y_j / (2r - j) (from 2 y_j D(y_j) = D(j (2r - j)) = 2j).

Weights. lam = 2 at the origin, -2 at each j = 1 point, 2 at each j = 3 point, -1 at each j = 4
point. With p~ = (1, p) the augmented point the checks are
  sum lam p~ p~^T = 0                (3x3: covers sum lam, sum lam p, sum lam p p^T),
  sum lam D(p~) p~^T = 0             (3x3),
  sum lam |D(p)|^2 = -24 / R, R = (2r - 1)(2r - 3)(2r - 4)   (nonzero).
Forged control (expected to FAIL): the weight of the first j = 1 point perturbed by +1 must
break the moment identity.
"""
import sys
from fractions import Fraction

FAILURES = []


def check(ok, msg):
    if ok:
        print("  ok   " + msg)
    else:
        print("  FAIL " + msg)
        FAILURES.append(msg)


# ---------------------------------------------------------------- polynomials in r
def ptrim(a):
    a = list(a)
    while a and a[-1] == 0:
        a.pop()
    return a


def padd(a, b):
    n = max(len(a), len(b))
    return ptrim([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)])


def pmul(a, b):
    if not a or not b:
        return []
    r = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            r[i + j] += x * y
    return ptrim(r)


def pneg(a):
    return [-x for x in a]


# ---------------------------------------------------------------- Q(r) as (num, den)
class RF:
    __slots__ = ("n", "d")

    def __init__(self, n, d=None):
        self.n = ptrim([Fraction(x) for x in n])
        self.d = ptrim([Fraction(x) for x in (d if d is not None else [1])])
        if not self.d:
            raise ZeroDivisionError("zero denominator")

    def __add__(self, o):
        return RF(padd(pmul(self.n, o.d), pmul(o.n, self.d)), pmul(self.d, o.d))

    def __neg__(self):
        return RF(pneg(self.n), self.d)

    def __sub__(self, o):
        return self + (-o)

    def __mul__(self, o):
        return RF(pmul(self.n, o.n), pmul(self.d, o.d))

    def inv(self):
        return RF(self.d, self.n)

    def is_zero(self):
        return not self.n


def rf(c):
    return RF([c])


R_POLY = lambda j: [Fraction(-j), Fraction(2)]          # 2r - j
YSQ = {1: RF(pmul([1], [-1, 2])), 3: RF(pmul([3], [-3, 2])), 4: RF(pmul([4], [-4, 2]))}  # j (2r - j)
IDX = {1: 0, 3: 1, 4: 2}


# ---------------------------------------------------------------- A = Q(r)[y1,y3,y4]/(y_j^2 - j(2r-j))
class A:
    __slots__ = ("t",)

    def __init__(self, t=None):
        self.t = {}
        for k, v in (t or {}).items():
            if not v.is_zero():
                self.t[k] = v

    def __add__(self, o):
        r = dict(self.t)
        for k, v in o.t.items():
            r[k] = (r[k] + v) if k in r else v
        return A(r)

    def __neg__(self):
        return A({k: -v for k, v in self.t.items()})

    def __sub__(self, o):
        return self + (-o)

    def __mul__(self, o):
        r = {}
        for k1, v1 in self.t.items():
            for k2, v2 in o.t.items():
                c = v1 * v2
                k = []
                for j, (a, b) in zip((1, 3, 4), zip(k1, k2)):
                    e = a + b
                    if e == 2:
                        c = c * YSQ[j]
                        e = 0
                    k.append(e)
                k = tuple(k)
                r[k] = (r[k] + c) if k in r else c
        return A(r)

    def scale(self, c):
        return A({k: v * c for k, v in self.t.items()})

    def is_zero(self):
        return len(self.t) == 0


def const(c):
    return A({(0, 0, 0): c if isinstance(c, RF) else rf(c)})


def y(j, sign=1):
    k = [0, 0, 0]
    k[IDX[j]] = 1
    return A({tuple(k): rf(sign)})


ZERO = A()
r_elt = const(RF([0, 1]))


def D_y(j, sign):
    """D(sign * y_j) = sign * y_j / (2r - j)."""
    return y(j, sign).scale(RF([1], R_POLY(j)))


# ---------------------------------------------------------------- the configuration
pts, lam, Dp = [], [], []
pts.append((const(0), const(0)))
lam.append(2)
Dp.append((ZERO, ZERO))
for j, wt in ((1, -2), (3, 2), (4, -1)):
    for sgn in (1, -1):
        pts.append((const(j), y(j, sgn)))
        lam.append(wt)
        Dp.append((ZERO, D_y(j, sgn)))

print("the seven points and the derivation")
on_circle = all((((px - r_elt) * (px - r_elt)) + py * py - r_elt * r_elt).is_zero() for (px, py) in pts)
check(on_circle, "all seven points lie on (x - r)^2 + y^2 = r^2")
# D is consistent with the defining relations: 2 y_j D(y_j) = d/dr (j (2r - j)) = 2j
cons = True
for j in (1, 3, 4):
    for sgn in (1, -1):
        lhs = (y(j, sgn) * D_y(j, sgn)).scale(rf(2))
        if not (lhs - const(2 * j)).is_zero():
            cons = False
check(cons, "2 y D(y) = d/dr (j (2r - j)) = 2j at each of the six points off the axis")
check(sum(lam) == 0 and len(pts) == 7, "seven points, weights summing to 0")


def moments(weights):
    aug = [(const(1), px, py) for (px, py) in pts]
    daug = [(ZERO, dx, dy) for (dx, dy) in Dp]
    M0 = [[ZERO] * 3 for _ in range(3)]
    M1 = [[ZERO] * 3 for _ in range(3)]
    for w, a, d in zip(weights, aug, daug):
        for i in range(3):
            for k in range(3):
                M0[i][k] = M0[i][k] + (a[i] * a[k]).scale(rf(w))
                M1[i][k] = M1[i][k] + (d[i] * a[k]).scale(rf(w))
    E = ZERO
    for w, d in zip(weights, daug):
        E = E + (d[1] * d[1] + d[2] * d[2]).scale(rf(w))
    return M0, M1, E


print("the moment identities")
M0, M1, E = moments(lam)
check(all(M0[i][k].is_zero() for i in range(3) for k in range(3)),
      "sum lam p~ p~^T = 0 (sum lam = 0, sum lam p = 0, sum lam p p^T = 0)")
check(all(M1[i][k].is_zero() for i in range(3) for k in range(3)), "sum lam D(p~) p~^T = 0")
Rr = pmul(pmul([-1, 2], [-3, 2]), [-4, 2])
target = const(RF([-24], Rr))
check((E - target).is_zero(), "energy sum lam |D(p)|^2 = -24 / ((2r - 1)(2r - 3)(2r - 4))")
check(not E.is_zero() and set(E.t.keys()) == {(0, 0, 0)}, "the energy is a nonzero element of Q(r)")

print("forged control: weight of the first j = 1 point perturbed by +1")
lam_bad = list(lam)
lam_bad[1] += 1
M0b, M1b, Eb = moments(lam_bad)
forged_passes = all(M0b[i][k].is_zero() for i in range(3) for k in range(3)) and \
    all(M1b[i][k].is_zero() for i in range(3) for k in range(3))
print("  perturbed weights satisfy the moment identities: %s (expected False)" % forged_passes)
check(not forged_passes, "forged control (perturbed weight) is rejected")

print("")
print("forged control (perturbed weight): %s (expected FAIL)" % ("PASS" if forged_passes else "FAIL"))
if FAILURES:
    print("%d check(s) failed" % len(FAILURES))
    print("VERDICT: FAIL")
    sys.exit(1)
print("VERDICT: PASS")
