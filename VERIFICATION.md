# Verification

All fourteen statements of Challenge.lean have proofs. The local build, the axiom audit, the source guard, the
statement and definition checks, the module-resolution check and Palomar's core-notation audit of the statements pass;
`python scripts/verify.py` runs them all and ends with `VERIFY: PASS`. The checks below were last run on the tree of
the final commit; a build record is evidence for that tree only. Theorems are numbered as in `comparator.json`, which
is also their order in Challenge.lean.

## Formal scope

| # | Statement | Proved in |
| --- | --- | --- |
| 1 | `six_concyclic_fieldCriterion` — six distinct points on a circle satisfy the criterion | SixConcyclic/Assembly.lean (with Core, Param) |
| 2 | `at_most_six_concyclic_fieldCriterion` — at most six | SixConcyclic/Main.lean |
| 3 | `at_most_six_spherical_spanning_fieldCriterion` — at most six spherical points spanning `Space d` | SixConcyclic/Main.lean, Isolators.lean |
| 4 | `at_most_five_spherical_fieldCriterion` — at most five spherical points, any dimension | SixConcyclic/Lift.lean, Isolators.lean |
| 5 | `algebraic_spherical_fieldCriterion` — algebraic coordinates and spherical | SixConcyclic/Algebraic.lean |
| 6 | `fieldCriterion_spherical` — the criterion implies sphericity | SixConcyclic/Sphere.lean |
| 7 | `algebraic_fieldCriterion_iff_spherical` — for algebraic coordinates the criterion is sphericity | SixConcyclic/Main.lean |
| 8 | `at_most_six_spherical_ramsey_of_sufficiency` — given sufficiency, at most six spherical points are Ramsey | SixConcyclic/Main.lean, Ramsey.lean, Transport.lean |
| 9 | `at_most_six_circle_points_ramsey_of_sufficiency` — the circle case | SixConcyclic/Main.lean |
| 10 | `algebraic_spherical_ramsey_of_sufficiency` — given sufficiency, spanning algebraic spherical sets are Ramsey | SixConcyclic/Main.lean |
| 11 | `algebraic_ramsey_iff_spherical_of_classification` — given the classification, spanning algebraic sets: Ramsey iff spherical | SixConcyclic/Main.lean |
| 12 | `spherical_fieldCriterion_of_card_le_finrank_add_four` — at most `m + 4` spherical points, `m` the dimension of the affine span, in their own space and field | SixConcyclic/Dimension.lean (with RealCert, Rank, Representative, Image, Extension, Descent) |
| 13 | `at_most_six_spherical_fieldCriterion` — at most six spherical points, any dimension, any span | SixConcyclic/Dimension.lean |
| 14 | `spherical_ramsey_of_sufficiency_of_card_le_finrank_add_four` — given sufficiency, at most `m + 4` spherical points are Ramsey | SixConcyclic/Dimension.lean |

Each statement is restated verbatim in Solution.lean and closed by the internal theorem of the same name with the
suffix `_internal` (theorem 9 by theorem 8's; theorem 1's internal theorem is `Asm.six_concyclic_certificate`). The `hsuff` and `hclass` hypotheses are the
sufficiency half and the full statement of the classification, quantified as `OAI.EuclideanRamsey.classification` is
in openai/math; nothing about them is proved here. PROOF.md names the lemma behind each step. The dimension of the
affine span is `Module.finrank ℝ (vectorSpan ℝ (Set.range a))`, the direction of `affineSpan ℝ (Set.range a)`.

## Local checks

```sh
python scripts/verify.py --fetch-cache
```

runs, in order: the pins (`lean-toolchain` and the Mathlib revision of `lake-manifest.json` are the committed ones),
`scripts/check-source.py`, `scripts/check_definitions.py`, `scripts/check_statements.py`, the three exact certificates
under `note/`, `lake build` of the four targets `SixConcyclic`, `Challenge`, `Solution`, `Test`,
`lake env python scripts/check_module_resolution.py`, and Palomar's `scripts/core_notation_audit.lean` on the
twenty-four compared declarations of `comparator.json`; the last line is `VERIFY: PASS` or `VERIFY: FAIL`.
`--skip-build` leaves out the four Lean steps. The steps can also be run one by one:

```sh
lake exe cache get
lake build
python scripts/check-source.py
python scripts/check_definitions.py
python scripts/check_statements.py
lake env python scripts/check_module_resolution.py
```

The `Test` target is a plain (non-module) file, so that the private auxiliaries of the development are in its
environment; it audits every constant whose name begins with `SixConcyclic.`, `_private.SixConcyclic.` or
`_private.Solution.` (477 constants; the audit fails below 450), permits only `propext`, `Classical.choice` and
`Quot.sound`, and fails if any of the fourteen compared theorems is missing. A placeholder in a proof compiles with
a warning; this audit is what fails the build. Challenge.lean intentionally contains fourteen proof placeholders;
Solution.lean and the modules it imports contain none, and Solution.lean does not import Challenge.lean. The source
guard rejects `sorry`, `sorryAx`, `admit`, `axiom`, `unsafe`, `partial`, `native_decide`, `implemented_by`,
`extern`, `Lean.ofReduceBool` and the kernel-bypass options in SixConcyclic.lean, `SixConcyclic/`, Solution.lean,
Test.lean and `Test/`, the same tokens except `sorry` in Challenge.lean, and any `debug.` option in the `[leanOptions]` table of lakefile.toml.
`check_definitions.py` compares the ten definitions of Challenge.lean and SixConcyclic/Defs.lean, character for
character, with `scripts/EuclideanRamsey.oai.lean`, a copy of OpenAI's challenge file at commit `adc7f124`;
`check_statements.py` compares every theorem header of Challenge.lean with Solution.lean. Palomar's
`scripts/core_notation_audit.lean` (an unmodified copy from github.com/PalomarRegistry/PalomarSubmission, fetched
2026-10-07 UTC) prints all twenty-four compared declarations (fourteen theorems, ten definitions) with exit 0.

Lean `v4.35.0-rc2` and Mathlib `v4.35.0-rc2` (commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`) are pinned by
the committed manifest; `lake update` is never run. Every file of the `SixConcyclic`, `Challenge` and `Solution`
libraries carries a `module` header; the two `Test` files are plain files for the reason above. A build from an
empty `.lake/build` after `lake exe cache get`, one target at a time, takes about three minutes on a 16-core, 16 GB
PC (183 s for the four targets: the twenty development modules in 97 s, built in parallel by `lake build
SixConcyclic`; the Challenge, which imports all of Mathlib, 57 s; Solution 10 s; the Test audit 19 s); each
development module takes 7–16 s on its own, most of it the Mathlib import.

## The finite computations

There is no `native_decide`, and no enumeration beyond `fin_cases` over `Fin 2`, `Fin 3` and `Fin 6` and one
`interval_cases` on `d ≤ 1`; arithmetic side goals use `linarith`, `nlinarith`, `omega`, `ring`, `field_simp` and
`linear_combination`. The algebra of the six-point certificate is a set of polynomial identities closed in an
abstract field (`Core.lean`, `Param.lean`, `Assembly.lean`): the (1,1)-forms through three points, their Veronese
matrix, the diagonal coefficients, the circle parametrisation, its two-sided inverse and the pullback of the circle
form. The nonvanishing facts (`Ordered.lean`) use only that the coordinate field is a subfield of `ℝ`. The dimension
theorem is matrix algebra over `ℝ ⊗_ℚ ℝ` (`RealCert.lean`, `Image.lean`, `Extension.lean`), finite-dimensional linear
algebra over `ℝ` (`Rank.lean`, `Representative.lean`) and one descent map built from an `F`-basis of `ℝ`
(`Descent.lean`); no computation is enumerative. `decide` is used only for inequalities between literal elements of
`Fin 6`.

Mutation controls, each run once in a scratch copy and reverted: (a) the sign of the scalar `s = −2|e|²/(V₁V₂)` of
the certificate flipped at both places it is written — `six_abstract` fails at the pullback rewrite (the pattern
`(−2 * …) • K` is not found); (b) the first row of `Lam` changed from `![1, 0, 1]` to `![2, 0, 1]` — `Lam_ver`,
`Lam_tangent`, `pullback`, `Winv_mul_Lam` and `Lam_mul_Winv` all fail; (c) a `sorry` in `gram_ne_zero_of_chords` —
Ordered, Isolators, Assembly, Main, Dimension and Solution still build with a warning, `lake build Test` fails with
twenty-three `sorryAx` dependencies (eight of them compared theorems: 1, 2, 3, 8, 9, 12, 13 and 14), and
`check-source.py` reports the line; (d) `hs : s ≤ 6`
weakened to `s ≤ 7` in `at_most_six_concyclic_fieldCriterion_internal` — the case split fails; (e) `hs : s ≤ 5`
weakened to `s ≤ 6` in `exists_isolators_of_le_five` — the two-plus-two split of the other points fails (`omega`);
(f) a scratch module with a declared `axiom` and a `native_decide` lemma, at default (private) visibility and used by
nothing, imported from Main — `check-source.py` flags both tokens, and the audit reports the private
axiom and the auxiliary axiom `…native_decide.ax_1_1` that Lean generates for `native_decide` (not
`Lean.ofReduceBool`), failing the build; (g) `hs : s ≤ 6` changed to `s ≤ 7` in Challenge.lean only —
`check_statements.py` reports `DIFFERS at_most_six_concyclic_fieldCriterion` while the definition check still passes,
as it should; (h) `s ≤ m + 4` weakened to `s ≤ m + 5` in
`spherical_fieldCriterion_of_card_le_finrank_add_four_internal` — the `omega` that feeds the rank argument
(`exists_six_of_dependence` needs `s ≤ rank + 3`) fails; (i) a `sorry` in `rank_qeval_vecMulVec` — Rank, Dimension and
Solution build with a warning, `check-source.py` reports the line, and `lake build Test` fails with eight `sorryAx`
dependencies, among them the three compared theorems 12–14.

## The certificates in `note/`

Independent of Lean, `note/certificates/` holds three standard-library Python checkers: the universal polynomial
identities behind the six-point certificate together with an exact end-to-end evaluation at random rational
parameters (0001); the moment identities by which the seven-point set of arXiv:2609.23327 fails the criterion
(0002); and the separability-idempotent certificate for an explicit configuration over `ℚ(√2)` (0003). Each prints
a `VERDICT` line and includes forged-input controls that fail as they must. They are cross-checks, not premises of
any Lean proof.

## Not checked here

- The classification (both halves) is a hypothesis of theorems 8–11 and 14, not a theorem of this repository; its
  Lean tree in openai/math is not a dependency and was not replayed.
- No statement is made for arbitrary spherical sets of more than `m + 4` points (the algebraic theorems 5, 7, 10 and
  11 have no size bound); the heptagon's failure of the criterion, and hence the sharpness of the bound `m + 4`, are
  on paper (the former also in certificate 0002), not in Lean.
- Theorems 10 and 11 cover spanning configurations; a non-spanning configuration with algebraic coordinates is not
  shown in Lean to have an algebraic spanning congruent copy (the note argues it on paper).
- The Python checkers are cross-checks of finite instances and polynomial identities, not premises of any Lean proof.
