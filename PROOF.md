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

## 7. The sharp dimension theorem (`RealCert`, `Rank`, `Representative`, `Image`, `Extension`, `Descent`, `Dimension`)

Write `m = finrank ℝ (vectorSpan ℝ (Set.range a))` for the dimension of the affine span of `a : Fin s → Space D`.
**Theorem 12** (`spherical_fieldCriterion_of_card_le_finrank_add_four`): distinct spherical points with
`s ≤ m + 4` satisfy the criterion, in `Space D` and over `Coeff a`. It contains Theorems 1–4 and gives
**Theorem 13** (`at_most_six_spherical_fieldCriterion`, no spanning hypothesis), since six distinct spherical
points have `m ≥ 2` (`two_le_finrank_of_six`, from `not_six_spherical_of_dim_le_one` on the spanning
representative). **Theorem 14** (`spherical_ramsey_of_sufficiency_of_card_le_finrank_add_four`) is Theorem 12
on the spanning representative (which has the same `m`, `finrank_vectorSpan_of_spanning`), then `hsuff` and
congruence.

**The real tensor ring** (`RealCert.lean`). `RT = ℝ ⊗_ℚ ℝ` with `ιl x = x ⊗ 1`, `ιr y = 1 ⊗ y`,
`μr (x ⊗ y) = xy`; `aug a i = (1, a_i)` as a real vector; `qeval H p = pᵀ H p`; `realSphere c r` the real
sphere matrix of `|x − c|² = r²` (`qeval_realSphere`, spatial block `I`). `RealCert p H` means a matrix `P`
over `RT` with every sandwich `∑ ιl (p_iα) P_αβ ιr (p_iβ)` zero and `P.map μr = H` exactly. Every
construction below is over `RT`; one descent at the end gives `FieldCriterion`.

**Descent** (`fieldCriterion_of_realCert`). Let `(e_δ)` be an `F`-basis of `ℝ` and `φ : ℝ → F` an `F`-linear map
with `φ 1 = 1`. The ℚ-bilinear `(x, y) ↦ ∑_δ φ(x e_δ) ⊗ y_δ`, `y = ∑ y_δ e_δ`, induces `Ψ : RT → F ⊗ F`
(`descentMap`) with `Ψ ((c ⊗ 1) z) = (c ⊗ 1) Ψ z`, `Ψ ((1 ⊗ c) z) = (1 ⊗ c) Ψ z` for `c ∈ F`
(`descentMap_ιl`, `descentMap_ιr`) and `μ (Ψ z) = φ (μr z)` (`μ_descentMap`). Entrywise, `Ψ` keeps the
sandwiches zero (their coefficients `aug a i α = ↑(augmented a i α)` are in `F`, `aug_eq_coe`) and turns the
spatial block `I` into `φ I = I`. Nothing uses that `F ⊗ F` is a domain.

**Operations on real certificates.** `realCert_of_fieldCriterion`: push forward along the base change
`pushRT : F ⊗ F → RT`. `realCert_symm`: the factor swap `swapRT = Algebra.TensorProduct.comm` turns `P` into the
certificate `(swapRT (P β α))_αβ` with multiplied matrix `Hᵀ`; the average has `(H + Hᵀ)/2`. `realCert_add_symm`:
for `N` symmetric with zero spatial block and `qeval N (p i) = 0`, the matrix
`(l ⊗ 1)(1 ⊗ e₀)ᵀ + (e₀ ⊗ 1)(1 ⊗ l)ᵀ` with `l = corrL N = (N₀₀/2, N₀ₖ)`, `e₀ = unitE = (1, 0)`, has sandwiches
`ιl (l·p) ιr (p₀) + ιl (p₀) ιr (l·p) = 0` (`qeval N p = 2 p₀ (l·p)`) and multiplies to `N`, so `H` becomes
`H + N`. `realCert_of_isolators`: the adjugate lift of §3 over `RT` with real isolators, multiplied matrix
exactly `H`. `realCert_reindex`: along any equivalence of index types.

**Isometric images** (`Image.lean`). If `a i = t + T (b i)` for a linear isometry `T : Space d →ₗᵢ Space D` with
matrix `M = isoMatrix T` (`Mᵀ M = 1`, `isoMatrix_transpose_mul`; `T z = M z`, `isoMatrix_mulVec`), let
`L = leftInv M t` be the affine left inverse `(1, z) ↦ (1, Mᵀ (z − t))` (`leftInv_mulVec`: `L (1, a_i) = (1, b_i)`)
and `G = perpRows M t` the matrix of the affine functionals `z ↦ ⟨(1 − M Mᵀ) e_k, z − t⟩`, which vanish at every
`a_i` (`perpRows_mulVec`, since `(1 − M Mᵀ) M = 0`). For a real certificate `P` of `b` with multiplied matrix
`H`, `(L ⊗ 1)ᵀ P (1 ⊗ L) + (G ⊗ 1)ᵀ (1 ⊗ G)` is a real certificate of `a` with multiplied matrix
`Lᵀ H L + Gᵀ G` (`realCert_transform`), whose spatial block is `M Mᵀ + (1 − M Mᵀ) = 1` when `H` has spatial block
`1` (`transform_spatial`; `realCert_of_isometric_image`).

**Extension by a point** (`Extension.lean`). If `T ⊆ ι` is certified with multiplied matrix `H`, `p b` lies
outside the span of `p '' T`, and `qeval H (p b) = 0`: take a linear functional `ℓ` vanishing on the span with
`ℓ (p b) = 1` (`Submodule.exists_le_ker_of_notMem`, scaled), `l α = ℓ (e_α)`, and `z` the sandwich of `P` at
`p b`; then `P − z · (ιl (l α) ιr (l β))` has sandwich `0 − z · 0` at the old points and `z − z` at `b`
(`ext_sandwich_sub`), and multiplies to `H` because `μr z = qeval H (p b) = 0` (`realCert_insert`). Iterating
by induction on `|Tᶜ|` (`realCert_of_finrank`): if `rank (span (range p)) = rank (span (p '' T)) + |Tᶜ|`, some
`b ∉ T` has `p b` outside the span of `p '' T` (else the ranks would agree), inserting it raises the rank by one
(`ext_finrank_span_insert`), and the invariant persists.

**The dichotomy and the rank argument** (`Rank.lean`). The real evaluation map `rankEval p : Q ↦ (qeval Q (p j))_j`
is surjective, giving real isolators, or a nonzero functional `l` annihilates its range, and then
`∑ l_i ⟨p_i, w⟩² = 0` for every `w` (`isolators_or_dependence`, with `Q = w wᵀ`, `rank_qeval_vecMulVec`). In the
second case (`exists_six_of_dependence`), with `U = {l > 0}`, `V = {l < 0}`: `∑ l = 0` (`rank_sum_eq_zero`, `w = e₀`),
so both are nonempty; a functional vanishing on `p '' U` makes every term `l_i ℓ(p_i)²` nonpositive, so it
vanishes on `p '' V` too, and `span (p '' U) = span (p '' V) =: W` (`rank_mem_span_of_dep`), of rank
`w ≤ min |U| |V|` (`rank_finrank_span_le`). Three distinct sphere points have independent augmented vectors
(`rank_three_indep`: a relation `x p_A + y p_B + z p_C = 0` gives `x + y + z = 0` and, paired with `A − c`, `B − c`,
`C − c`, the system `y|AB|² + z|AC|² = x|AB|² + z|BC|² = x|AC|² + y|BC|² = 0` of determinant `2|AB|²|AC|²|BC|²`),
and `|U| = |V| = 1` would force `a_u = a_v`; so `w ≥ 3` (`rank_three_le`). Every `p_i` lies in `W` or among the
`s − |U| − |V|` others, so `rank ≤ w + s − |U| − |V|`; with `s ≤ rank + 3` (that is `s ≤ m + 4`,
`finrank_span_aug`) this gives `|U| + |V| ≤ w + 3 ≤ |U| + |V|`: `|U| = |V| = w = 3`, `T = U ∪ V` has six points
whose augmented vectors span three dimensions, and `rank = 3 + |Tᶜ|`.

**The spanning representative, with the map back** (`Representative.lean`). `exists_spanning_representative'` is
the construction of §5 with the isometry exposed: `a i = a₀ + T (b i)` for `T = V.subtypeₗᵢ ∘ E.symm`,
`V = vectorSpan`, `E = (stdOrthonormalBasis ℝ V).repr`, and `b` injective, congruent, spanning
`Space (finrank V)` and spherical. `finrank_span_aug`: `span (range (aug a)) = span {aug a 0} ⊕ j (vectorSpan)`,
`j v = (0, v)` (`repAugEmbed`), so its rank is `m + 1`.

**Assembly** (`Dimension.lean`). For `s ≤ 5` Theorem 4. Otherwise, with `c, r` real and `H_c = realSphere c r`
(`qeval H_c (aug a i) = 0`): in the surjective branch `realCert_of_isolators` and descent. In the dependent
branch, the six points `b = a ∘ orderIsoOfFin T` are distinct, on the sphere, with `m_b = 2`
(`finrank_span_aug`, `range (aug b) = aug a '' T`); their spanning representative lies in `Space 2`
(`six_concyclic_fieldCriterion_of_dim`), Theorem 1 certifies it, `realCert_of_fieldCriterion` and
`realCert_of_isometric_image` carry the certificate to `b` in `Space D` with some multiplied matrix `H₀` of
spatial block `I`, `realCert_symm` symmetrises it, and `realCert_add_symm` with `N = H_c − (H₀ + H₀ᵀ)/2`
(symmetric, zero spatial block, vanishing at the six points by `realCert_qeval`) gives the multiplied matrix
`H_c` (`realCert_six_of_planar`); `realCert_reindex` moves to the subtype `T`, `realCert_of_finrank` extends to
all of `a` because `rank = 3 + |Tᶜ|`, and `fieldCriterion_of_realCert` descends.

**On paper: sharpness.** For `d ≥ 2`, the heptagon of §6 placed in the plane `x₃ = … = x_d = 0` of `ℝ^d`, with
centre `c = (r, 0, …, 0)` and radius `r`, together with the points `c + r e_j`, `3 ≤ j ≤ d`, is a spherical set of
`d + 5` points with affine span of dimension `d` and the heptagon's coordinate field (`r = (y₁² + 1)/2`). A
certificate for it would restrict, on the coordinates `0, 1, 2`, to a certificate for the planar heptagon (the
other coordinates of its points are `0`), contradicting §6; and the set contains the heptagon, so it is not
Ramsey (Theorem 1 of arXiv:2609.23327 with `ramsey_restrict`). Hence, given the sufficiency half, `d + 5` is the
least size of a non-Ramsey spherical set with affine span of dimension `d ≥ 2`. Not formalized.

**Relation to the source.** The surjective branch is the source's Proposition 7.3. The congruence invariance of
the criterion and the descent of certificates between fields appear in Section 2 of the source for spanning sets
in a fixed dimension; here they are formalized in the form of the real tensor ring, with the ambient dimension
free. The extension lemma is the analogue, on the side of the criterion, of the one-point extension theorems of
2026 (arXiv:2608.09649, arXiv:2608.11736: a Ramsey set plus a point outside its affine hull is Ramsey), with the
sphere carried along. The statement of Theorem 12 and the outline of its proof were proposed by a model of
OpenAI consulted on the repository at commit `3348ece`, as DISCLOSURE.md says.
