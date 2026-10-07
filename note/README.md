# Research note: six concyclic points and the tensor criterion

This folder holds the research note that accompanies the Lean development (`main.tex`, built as
`main.pdf`; rebuild with `pdflatex main.tex`, three passes). The finite-data claims of the note are checked by three
standalone Python 3 programs (standard library only, exact rational arithmetic, no `assert`
statements). Each prints its checks, runs a forged-input control that is expected to fail,
and ends with a line `VERDICT: PASS` or `VERDICT: FAIL`.

| Certificate | Claim | Re-run |
| --- | --- | --- |
| [0001](certificates/0001-six-concyclic-universal-certificate/NOTES.md) | the six-point certificate as universal polynomial identities | `python note/certificates/0001-six-concyclic-universal-certificate/verify.py` |
| [0002](certificates/0002-heptagon-fails-the-criterion/NOTES.md) | a cyclic heptagon fails the criterion (exact moment identities) | `python note/certificates/0002-heptagon-fails-the-criterion/verify.py` |
| [0003](certificates/0003-algebraic-idempotent-example/NOTES.md) | the separability idempotent on nine points of an algebraic circle | `python note/certificates/0003-algebraic-idempotent-example/verify.py` |

Each run takes a few seconds at most. Each folder's `NOTES.md` gives the statement, the honesty
label, the external dependencies, whether the theorem follows from a green run, and the last
lines of a run.

Certificate 0002 shows only that the heptagon fails the criterion; that it is not Ramsey also
needs the necessity half of the classification or Theorem 1 of "A cyclic non-Ramsey heptagon"
(arXiv:2609.23327).

License: the note (`main.tex`, `main.pdf`) and the `NOTES.md` files are
[CC BY-SA 4.0](https://creativecommons.org/licenses/by-sa/4.0/); the `verify.py` programs are [MIT](../LICENSE), like the
rest of the repository.
