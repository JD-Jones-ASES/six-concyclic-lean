# 0002 A cyclic heptagon fails the tensor criterion

**Statement.** For transcendental real `r > 2`, the seven points `(0, 0)`, `(j, +-y_j)`
(`j = 1, 3, 4`, `y_j^2 = j(2r - j)`) lie on `(x - r)^2 + y^2 = r^2`, and with weights `2`
(origin), `-2`, `2`, `-1` (each point of the `j = 1, 3, 4` pairs) and `D` the derivation
extending `d/dr` (`D(y_j) = j / y_j`):
`sum lam p~ p~^T = 0`, `sum lam D(p~) p~^T = 0`, and
`sum lam |D(p)|^2 = -24 / ((2r - 1)(2r - 3)(2r - 4)) != 0`.

**Artifact.** `verify.py` (Python 3 standard library): exact arithmetic in
`Q(r)[y1, y3, y4] / (y_j^2 - j(2r - j))`, coefficients rational functions of `r`.

**Re-run.** `python verify.py` (under 1 s).

**Honesty label.** Exact identities. That the heptagon fails the criterion follows by the
argument below; that it is not Ramsey is conditional on external results.

**Why the identities rule out the criterion.** `D` is a derivation of the coordinate field `F`
(it exists because `r` is transcendental and `F` is a finite separable extension of `Q(r)`).
The pairing `Phi(x (x) y) = D(x) D(y)` is `Q`-bilinear, so it is defined on `B = F (x)_Q F`, and
`Phi(L(a) z R(b)) = ab Phi(z) + a D(b) Psi_1(z) + D(a) b Psi_2(z) + D(a) D(b) m(z)` with
`Psi_1(x (x) y) = D(x) y`, `Psi_2(x (x) y) = x D(y)`. Apply `Phi` to each evaluation identity,
weight by `lam` and sum: the first three terms vanish by the two moment identities, leaving
`0 = sum_{alpha,beta} M_{alpha beta} m(P_{alpha beta})` with `M = sum lam D(p~) D(p~)^T`. `M`
lives on the spatial block (`D(1) = 0`), where `m(P) = I`, so the right side is
`tr M = -24/R != 0`. No `P` exists.

**External dependencies.** That the heptagon is not Ramsey follows from this certificate with the
necessity half of the classification (the criterion is necessary for Ramsey; family 172 of the
openai/math release, not proved here), or directly from Theorem 1 of "A cyclic non-Ramsey heptagon"
(arXiv:2609.23327). Given also the sufficiency half, the Ramsey theorems of this repository make every
spherical set of at most six points Ramsey, so seven is then the least size of a non-Ramsey spherical
(in particular concyclic) set.

**Implication.** A green run, with the argument above, proves that this heptagon fails the
criterion; it does not by itself prove that the heptagon is not Ramsey.

**Independent verification.** An independent computer-algebra run of the same moments agreed
during development; the energy is also a hand check:
`-4/(2r-1) + 12/(2r-3) - 8/(2r-4) = -24/R`.

**Forged control.** Perturbing one weight by `+1` breaks the moment identities.

**Last lines of a run.**

```
forged control: weight of the first j = 1 point perturbed by +1
  perturbed weights satisfy the moment identities: False (expected False)
  ok   forged control (perturbed weight) is rejected

forged control (perturbed weight): FAIL (expected FAIL)
VERDICT: PASS
```
