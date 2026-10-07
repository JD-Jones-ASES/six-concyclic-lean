# 0001 Six concyclic points: a universal tensor certificate

**Statement.** For six points on a circle, written through a base point `b` on the circle with
centre `c` (five chord directions `x_1..x_5` and the tangent `x_6 = (-(b2 - c2), b1 - c1)` for
`b` itself), the matrix `P = (kappa/c) Lambda_L^{-T} Q Lambda_R^{-1}` satisfies the six
evaluation identities of the tensor criterion in `Q[left, right]`, and its multiplication image
is the circle form `H` (spatial block `I`). Here `Lambda` is the Veronese pullback
(`p(x) = Lambda v(x)`), `Q` the coefficient matrix of `q = ell_012 ell_345` (two (1,1)-forms
through the triples), `kappa = -2 rho^2`, `rho^2 = |b - c|^2`, and `V = V_012 V_345` (written `c` in the code) the
product of the brackets `U_j W_k - U_k W_j` within each triple.

**Artifact.** `verify.py` (Python 3 standard library, `fractions.Fraction`; a sparse
polynomial class in 28 symbols plus `X1 X2 Y1 Y2`). Checks: (i) `p = Lambda v`,
`Lambda^T H Lambda = -2 rho^2 K`, `det Lambda = 4 rho^2`; (ii) `ell_012` and `ell_345` vanish
at their own three points (expanded 4x4 determinants); (iii) `m(q) = V_012 V_345 (X1 Y2 - X2 Y1)^2`;
(iv) end to end at 12 independent random rational specialisations of all 28 symbols.

**Re-run.** `python verify.py` (about 1 s).

**Honesty label.** (i)-(iii) are exact polynomial identities; (iv) is exact arithmetic at
sampled points (a spot check of the assembled matrix, not needed for the logic).

**External dependencies.** None beyond the Python standard library.

**Implication.** A green run gives the criterion for every six distinct concyclic points once
two facts not checked here are supplied: the circle has a centre with coordinates in the
coordinate field, and `rho^2` and every bracket are nonzero for distinct points (both proved
in the Lean development); then (ii) gives the evaluations and (i) with (iii) gives
`m(P) = Lambda^{-T} (kappa K) Lambda^{-1} = H`.

**Independent verification.** An independent computer-algebra implementation agreed during
development, and the Lean development proves the general theorem in the kernel
(`six_concyclic_fieldCriterion`).

**Forged controls.** A perturbed `Lambda` fails (i); `q' = ell_012 ell_013` (point 4 on
neither triple) fails the evaluation at point 4, symbolically and in all 12 trials.

**Last lines of a run.**

```
  ok   forged control (q') is rejected end to end in every trial
  [1.2s]

forged control 1 (perturbed Lambda): FAIL (expected FAIL)
forged control 2 (q' = ell_012 ell_013): FAIL (expected FAIL)
VERDICT: PASS
```
