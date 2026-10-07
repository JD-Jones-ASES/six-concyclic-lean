# The proofs, with the Lean names

Throughout, `a : Fin s → Space d` is a configuration, `F = Coeff a = ℚ(all coordinates) ⊂ ℝ`,
`B = TensorRing a = F ⊗_ℚ F`, `p_i = augmented a i = (1, a_i) ∈ F^{Option (Fin d)}`,
`ι₁ x = x ⊗ 1`, `ι₂ y = 1 ⊗ y`, `μ (x ⊗ y) = xy` (`SixConcyclic/Tensor.lean`). The criterion
`FieldCriterion a` asks for `P ∈ Mat_{d+1}(B)` with `∑ α β, ι₁ (p_i)_α · P_αβ · ι₂ (p_i)_β = 0` for every `i`
and `μ (P_αβ) = δ_αβ` on the spatial block; the constant row and column of `μ P` are free.

## 1. An `F`-rational sphere (`SixConcyclic/Sphere.lean`)

If `dist (a i) c = r` for all `i`, then `|a_i|² − 2⟨c, a_i⟩ + (|c|² − r²) = 0`. The field `ℝ` is an `F`-vector
space, so there is an `F`-linear `φ : ℝ → F` with `φ 1 = 1`; applying it, `|a_i|²` and `a_ij` being in `F`,
gives `|a_i|² − 2⟨c', a_i⟩ + C = 0` with `c'_j = φ (c_j)`, `C = φ (|c|² − r²)` in `F`
(`exists_rational_sphere`). `sphereMatrix c' C` is the matrix of this form, with spatial block `I`
(`quadEval_sphereMatrix`, `sphereMatrix_spatial`). Conversely an `F`-rational sphere equation through the
points, read in `ℝ`, is a sphere with centre `c'` and radius `√(|c'|² − C)` (`spherical_of_rational_sphere`).

**Theorem 6** (`fieldCriterion_spherical`). Apply `μ` to a certificate: `μ P` has spatial block `I` and
`p_iᵀ (μ P) p_i = 0`, an `F`-rational sphere equation; so the points are spherical
(`fieldCriterion_spherical_internal`).

## 2. Six points on a circle (`Core.lean`, `Param.lean`, `Assembly.lean`)

Let `a_0, …, a_5` be distinct points of a circle in the plane, `c', C` the `F`-rational circle through them,
`p = a_5` the base point, `e = p − c'` (`|e|² ≠ 0`, from the chord–radius identity at any chord:
`chord_dot_radius_ne_zero`), `x_j = a_j − p` for `j < 5`
and `x_5 = (−e_1, e_0)` the tangent direction. For `x = (u, w)` the point `q = p − 2⟨e,x⟩/|x|² · x` lies on the
circle and `|x|² (1, q) = Λ (u², uw, w²)` with the `3 × 3` matrix `Λ = Lam p c'` of `Param.lean`
(`Lam_ver`, `Lam_tangent`); `Winv` is its two-sided inverse (`Winv_mul_Lam`, `Lam_mul_Winv`; on paper
`det Λ = 4|e|²`).
Writing `H` for the circle matrix and `K = !![0,0,1; 0,−2,0; 1,0,0]` the matrix of `(u w' − u' w)²` in the
Veronese basis `(u², uw, w²)`, `Λᵀ H Λ = −2|e|² K` (`pullback`): the form vanishes on the Veronese curve
and is symmetric, so it is a multiple of the discriminant, and the multiple is computed.

For three parameter points `(U j, W j)` in the left copy and `(U' j, W' j)` in the right copy, `ell` is the
bilinear form `det [X₀Y₀, X₀Y₁, X₁Y₀, X₁Y₁; rows (U j U' j, U j W' j, W j U' j, W j W' j)]`, which vanishes
at each of its three points by a repeated row (`ell_vanishes`). With the two triples `{0,1,2}` and
`{3,4,5}`, `q = ell₁ · ell₂` is a biquadratic form with Veronese matrix `Q = Qm (…)`
(`Qm_form`: `v(X)ᵀ Q v(Y) = ell₁ · ell₂`). On the diagonal `U' = U, W' = W` the corner coefficients of
each `ell` vanish and the middle ones are `±V`, `V = ∏_{j<k} (U j W k − U k W j)` (`mult_coeffs`); hence
`μ Q = V₁ V₂ · K`. The brackets are nonzero: `det(x_j, x_k)` for two chords from `p` by `det_ne_zero`
(three distinct points of a circle are not collinear), and `det(x_j, x_5) = ⟨x_j, e⟩ = −|x_j|²/2` for a chord
against the tangent by `chord_dot_radius_ne_zero`.

Put `s = −2|e|² / (V₁ V₂)` and `P = Pmat ι₁ ι₂ s Winv Q = ι₁ s · (Winv.map ι₁)ᵀ Q (Winv.map ι₂)`.
Since `Winv p_i = |x_i|⁻² v(x_i)`, the evaluation at `a_i` is
`ι₁ (s |x_i|⁻²) ι₂ (|x_i|⁻²) · ell₁(ι₁ x_i, ι₂ x_i) · ell₂(ι₁ x_i, ι₂ x_i)` (`eval_P`, `Qm_form`), and one
factor vanishes (`ell_vanishes`). And `μ P = s V₁ V₂ · Winvᵀ K Winv = Winvᵀ (Λᵀ H Λ) Winv = H`
(`mult_P`, `mult_coeffs`, `pullback`), whose spatial block is `I`. This is **Theorem 1**
(`six_concyclic_fieldCriterion`).

## 3. Isolating quadrics and the adjugate lift (`Lift.lean`, `Isolators.lean`)

An isolating quadric for the point `i` is an `F`-matrix `q_i` with `p_jᵀ q_i p_j = δ_ij`
(`quadEval`). If every point has one, an `F`-rational sphere matrix `H` lifts
(`fieldCriterion_of_isolators`): with `D` the `s × (d+1)²` matrix over `B` of rows
`ι₁ (p_i)_α ι₂ (p_i)_β`, `S` the matrix with columns `ι₁ q_i`, `N = D S` (so `μ N = I`), `b = ι₁ H` and
`z = det N · b − S · adj N · D b`, one has `D z = 0` by `N · adj N = det N · I`, and `μ z = H` because
`μ (det N) = 1`, `μ (adj N) = I` and `μ (D b) = 0`. This is the argument of the paper's Proposition 7.3
without the choice of a minor.

Isolators come from products of affine functionals (`outer`, `quadEval_outer`). On a sphere, the line through
two of the points misses every third (`exists_line_functional`: a chord from a point of the sphere is not
a multiple of another chord from the same point, `isoVec_notMem_span_singleton`, because the sphere
equation `chord_eq` would force the third point onto one of the two; `gram_ne_zero` is the same fact in Gram
form), and a point is separated from any other
(`exists_point_functional`). For at most five points the other points split into two groups of at most two,
so a product of two group functionals isolates each point (`exists_isolators_of_le_five`): **Theorem 4**
(`at_most_five_spherical_fieldCriterion`). For six points that affinely span a space of dimension at least
three, some three of the other five span a plane missing the point (`exists_isolating_triple`: two distinct
planes through a line meet in that line, and all six in one plane would not span), and the plane times the
line through the remaining two isolates it (`exists_plane_functional`: a functional on `F^d` vanishing on
the `F`-span of the two chords and not on `a_i − a_j`, the real non-membership pulled back to `F`;
`exists_isolators_of_six`).

**Theorem 2** (`at_most_six_concyclic_fieldCriterion`) is Theorem 4 for `s ≤ 5` and Theorem 1 for `s = 6`.
**Theorem 3** (`at_most_six_spherical_spanning_fieldCriterion`) is Theorem 4 for `s ≤ 5`; for `s = 6`,
`d = 2` is Theorem 1, `d ≥ 3` is the triple isolator, and `d ≤ 1` cannot carry six distinct spherical points.

## 4. Algebraic coordinates (`Algebraic.lean`)

If every coordinate is algebraic, `F` is a number field (`finiteDimensional_of_algebraic`), so `F ⊗_ℚ F` is
étale over `F` and has a separability idempotent `t` with `(1 ⊗ x − x ⊗ 1) t = 0` for every `x` and `μ t = 1`
(`exists_sep_idem`). Then `P = t · (H ⊗ 1)` works for any `F`-rational sphere matrix `H`: the sandwich
`(x ⊗ 1) t (H ⊗ 1) (1 ⊗ y)` equals `t · (xHy ⊗ 1)` and the evaluations vanish; `μ P = H`
(`fieldCriterion_of_algebraic_sphere`). **Theorem 5** (`algebraic_spherical_fieldCriterion`) follows with
`exists_rational_sphere`, and **Theorem 7** (`algebraic_fieldCriterion_iff_spherical`) with Theorem 6.
Given the sufficiency half of the classification, a non-Ramsey spherical set must have a transcendental
coordinate (Theorem 10, for spanning sets); every known one does.

## 5. The Ramsey corollaries (`Ramsey.lean`, `Transport.lean`, `Main.lean`)

`Ramsey` is inherited by sub-configurations (`ramsey_restrict`), by congruent configurations
(`ramsey_of_congruent`), and holds for the empty and the one-point configuration. A configuration of at least
two distinct spherical points is congruent to an injective spherical one that affinely spans a space of
positive dimension (`exists_spanning_representative`: translate, take the span, map it isometrically by an
orthonormal basis; the sphere's centre projects orthogonally onto the span). **Theorem 8**
(`at_most_six_spherical_ramsey_of_sufficiency`): for `s ≤ 1` directly; otherwise the spanning representative
satisfies the criterion by Theorem 3 and is Ramsey by the hypothesis `hsuff`, hence so is the original.
**Theorem 9** is its plane case. **Theorem 10** (`algebraic_spherical_ramsey_of_sufficiency`) is Theorem 5
and `hsuff`; **Theorem 11** (`algebraic_ramsey_iff_spherical_of_classification`) is Theorems 5 and 6 with
both halves `hclass`.

## 6. On paper: given the classification, seven is the least size of a non-Ramsey spherical set

The heptagon `{(0,0)} ∪ {(j, ±√(j(2r−j))) : j ∈ {1,3,4}}`, `r > 2` transcendental, fails the criterion: with
the weights `2, −2, 2, −1` on the origin and the pairs `j = 1, 3, 4`, and the derivation `D` of its
coordinate field with `D r = 1`, the moments `∑λ = 0`, `∑λ p̃ p̃ᵀ = 0`, `∑λ D(p̃) p̃ᵀ = 0` hold exactly and
`∑λ |D p̃|² = −24/((2r−1)(2r−3)(2r−4)) ≠ 0`; pairing a certificate with `Φ (x ⊗ y) = D x · D y` turns the
evaluations into `0 = ∑λ |D p̃|²`, a contradiction (note, certificate 0002). Given the necessity half of the
classification (or the heptagon paper's own Theorem 1) the heptagon is not Ramsey; given the sufficiency
half, Theorem 8 makes every spherical set of at most six points Ramsey. So, given the classification, seven
is the least size of a non-Ramsey spherical set. These are not formalized.
