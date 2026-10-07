# 0003 The separability idempotent on an algebraic circle

**Statement.** In `B = Q(sqrt2) (x)_Q Q(sqrt2) = Q[x, y]/(x^2 - 2, y^2 - 2)` the element
`e = (1 + xy/2)/2` satisfies `m(e) = 1`, `e(x - y) = 0`, `e^2 = e`. For nine distinct points on
the circle with centre `(1/3 + sqrt2, -2 sqrt2)` and radius `1 + sqrt2` (stereographic
parameters in `Q(sqrt2)`), `P = e (S (x) 1)` satisfies every evaluation identity and
`m(P) = S` (spatial block `I`) for the first 6, 7 and all 9 points. Extension: the universal
six-point construction of certificate 0001 also works in this `B`, which is not a domain
(`(x - y)(x + y) = x^2 - y^2 = 0` with both factors nonzero).

**Artifact.** `verify.py` (Python 3 standard library): `Q(sqrt2)` as pairs of fractions, `B` as
four fractions on the basis `1, x, y, xy`.

**Re-run.** `python verify.py` (under 1 s).

**Honesty label.** Exact; one worked example of the algebraic case, not a proof of it.

**External dependencies.** None beyond the Python standard library.

**Implication.** A green run proves the criterion for these nine points only; the general
statement (algebraic coordinates and spherical imply the criterion, any number of points) is the
Lean theorem `algebraic_spherical_fieldCriterion`, whose proof uses the same kind of idempotent.

**Independent verification.** An independent computer-algebra run of the same example agreed
during development.

**Forged controls.** The naive lift `S (x) 1` fails the evaluations; the complementary idempotent
`(1 - xy/2)/2` fails the multiplication condition (`m = 0`).

**Last lines of a run.**

```
  ok   six-point construction: m(P) = S (spatial block I)
  (the six-point P is not built for the seventh point; its evaluation there is zero: False)

forged control 1 (naive lift): FAIL (expected FAIL)
forged control 2 (complementary idempotent): FAIL (expected FAIL)
VERDICT: PASS
```
