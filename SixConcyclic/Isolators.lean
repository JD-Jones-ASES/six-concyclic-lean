module

public import SixConcyclic.Ordered

/-!
# Isolating quadrics

An affine functional `ℓ = (ℓ₀, n)`, `ℓ(x) = ℓ₀ + ⟨n, x⟩`, is a vector indexed by `Option (Fin d)`;
`outer ℓ ℓ'` is the matrix of the product of two of them, and `quadEval (outer ℓ ℓ') i` is
`ℓ(a_i) ℓ'(a_i)`. On a sphere, a line through two of the points misses every third
(`exists_line_functional`, via `gram_ne_zero`), and a point is separated from any other
(`exists_point_functional`). For at most five points the others split into two groups of at most
two, so the product of the two group functionals isolates the point. For six points that affinely
span a space of dimension at least three, some three of the other five span a plane missing the
point, and that plane times the line through the remaining two isolates it
(`exists_isolators_of_six`); the plane functional is the component of `a_i − a_j` orthogonal to
the plane, computed over `F` with the `2 × 2` Gram matrix of the plane's two chords.
-/

@[expose] public section

namespace SixConcyclic

noncomputable section

variable {s d : ℕ} (a : Fin s → Space d)

/-- The value `ℓ₀ + ⟨n, a_i⟩` of an affine functional at the `i`-th point. -/
def affEval (ℓ : Option (Fin d) → Coeff a) (i : Fin s) : Coeff a := ∑ α, ℓ α * augmented a i α

/-- The matrix of the product of two affine functionals. -/
def outer (ℓ ℓ' : Option (Fin d) → Coeff a) : Matrix (Option (Fin d)) (Option (Fin d)) (Coeff a) :=
  fun α β => ℓ α * ℓ' β

/-- The quadratic evaluation of `outer ℓ ℓ'` is the product of the two values. -/
theorem quadEval_outer (ℓ ℓ' : Option (Fin d) → Coeff a) (i : Fin s) :
    quadEval a (outer a ℓ ℓ') i = affEval a ℓ i * affEval a ℓ' i := by
  unfold quadEval outer affEval
  rw [Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => by ring

/-- The constant functional `1`. -/
theorem affEval_one (i : Fin s) :
    affEval a (fun α => match α with | none => 1 | some _ => 0) i = 1 := by
  simp [affEval, Fintype.sum_option, augmented]

/-- The `i`-th point as a vector over the coordinate field. -/
def isoVec (i : Fin s) : Fin d → Coeff a := fun k => coordinate a i k

/-- The affine functional `x ↦ f (x − a_j)` of a linear form `f` on `F^d`. -/
def isoFunctional (f : (Fin d → Coeff a) →ₗ[Coeff a] Coeff a) (j : Fin s) :
    Option (Fin d) → Coeff a
  | none => -f (isoVec a j)
  | some k => f (fun k' => if k = k' then 1 else 0)

/-- `isoFunctional f j` evaluates to `f (a_m − a_j)`. -/
theorem affEval_isoFunctional (f : (Fin d → Coeff a) →ₗ[Coeff a] Coeff a) (j m : Fin s) :
    affEval a (isoFunctional a f j) m = f (isoVec a m - isoVec a j) := by
  have key : ∀ x : Fin d → Coeff a,
      f x = ∑ k, f (fun k' => if k = k' then 1 else 0) * x k := by
    intro x
    conv_lhs => rw [pi_eq_sum_univ x]
    simp only [map_sum, map_smul, smul_eq_mul, mul_comm]
  rw [map_sub, key (isoVec a m)]
  simp only [affEval, Fintype.sum_option, isoFunctional, augmented, isoVec]
  ring

/-- A vector `a_i − a_j` outside a subspace `W` of `F^d` gives an affine functional that vanishes
at every point `a_m` with `a_m − a_j ∈ W` and not at `a_i`. -/
theorem exists_functional_of_notMem (W : Submodule (Coeff a) (Fin d → Coeff a)) {i j : Fin s}
    (hu : isoVec a i - isoVec a j ∉ W) :
    ∃ ℓ : Option (Fin d) → Coeff a,
      (∀ m, isoVec a m - isoVec a j ∈ W → affEval a ℓ m = 0) ∧ affEval a ℓ i ≠ 0 := by
  obtain ⟨f, hfu, hW⟩ := Submodule.exists_le_ker_of_notMem hu
  refine ⟨isoFunctional a f j, fun m hm => ?_, ?_⟩
  · rw [affEval_isoFunctional]; exact hW hm
  · rw [affEval_isoFunctional]; exact hfu

/-- Distinct points give a nonzero difference vector. -/
theorem isoVec_sub_ne_zero (ha : Function.Injective a) {i j : Fin s} (hij : i ≠ j) :
    isoVec a i - isoVec a j ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := exists_coordinate_ne a ha hij
  exact hk (sub_eq_zero.mp (congrFun h k))

/-- A functional vanishing at `a j` and not at `a i`. -/
theorem exists_point_functional (ha : Function.Injective a) {i j : Fin s} (hij : i ≠ j) :
    ∃ ℓ : Option (Fin d) → Coeff a, affEval a ℓ j = 0 ∧ affEval a ℓ i ≠ 0 := by
  obtain ⟨ℓ, h0, h1⟩ := exists_functional_of_notMem a ⊥ (i := i) (j := j)
    (by rw [Submodule.mem_bot]; exact isoVec_sub_ne_zero a ha hij)
  exact ⟨ℓ, h0 j (by simp), h1⟩

/-- The value of a scaled functional. -/
theorem affEval_mul_left (c : Coeff a) (ℓ : Option (Fin d) → Coeff a) (i : Fin s) :
    affEval a (fun α => c * ℓ α) i = c * affEval a ℓ i := by
  simp only [affEval, Finset.mul_sum, mul_assoc]

/-- Two functionals that do not vanish at `a_i`, and of which one vanishes at every other point,
give an isolating quadric for `a_i`. -/
theorem exists_isolator_of_pair {i : Fin s} (ℓ₁ ℓ₂ : Option (Fin d) → Coeff a)
    (h₁ : affEval a ℓ₁ i ≠ 0) (h₂ : affEval a ℓ₂ i ≠ 0)
    (hv : ∀ j, j ≠ i → affEval a ℓ₁ j = 0 ∨ affEval a ℓ₂ j = 0) :
    ∃ M : Matrix (Option (Fin d)) (Option (Fin d)) (Coeff a),
      ∀ j, quadEval a M j = if i = j then 1 else 0 := by
  refine ⟨outer a (fun α => (affEval a ℓ₁ i * affEval a ℓ₂ i)⁻¹ * ℓ₁ α) ℓ₂, fun j => ?_⟩
  rw [quadEval_outer, affEval_mul_left]
  split_ifs with h
  · subst h
    field_simp
  · rcases hv j (Ne.symm h) with h' | h' <;> simp [h']

section sphere

variable (c' : Fin d → Coeff a) (C : Coeff a)
  (hsph : ∀ i, ∑ j, coordinate a i j ^ 2 - 2 * ∑ j, c' j * coordinate a i j + C = 0)
  (ha : Function.Injective a)

include hsph ha in
/-- On a sphere, `a_i − a_j` is not an `F`-multiple of `a_k − a_j`. -/
theorem isoVec_notMem_span_singleton {i j k : Fin s} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    isoVec a i - isoVec a j ∉ Submodule.span (Coeff a) {isoVec a k - isoVec a j} := by
  intro hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hc' : ∀ n, c * (coordinate a k n - coordinate a j n) =
      coordinate a i n - coordinate a j n := fun n => congrFun hc n
  have hi := chord_eq a c' C hsph j i
  have hk := chord_eq a c' C hsph j k
  have h1 : ∑ n, (coordinate a i n - coordinate a j n) ^ 2 =
      c ^ 2 * ∑ n, (coordinate a k n - coordinate a j n) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by rw [← hc' n]; ring
  have h2 : ∑ n, (coordinate a j n - c' n) * (coordinate a i n - coordinate a j n) =
      c * ∑ n, (coordinate a j n - c' n) * (coordinate a k n - coordinate a j n) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by rw [← hc' n]; ring
  rw [h1, h2] at hi
  have hW := chord_sq_ne_zero a ha hjk
  have hprod : c * (c - 1) * ∑ n, (coordinate a k n - coordinate a j n) ^ 2 = 0 := by
    linear_combination hi - c * hk
  rcases mul_eq_zero.mp hprod with h | h
  · rcases mul_eq_zero.mp h with h | h
    · apply isoVec_sub_ne_zero a ha hij
      rw [← hc, h, zero_smul]
    · apply isoVec_sub_ne_zero a ha hik
      have : c = 1 := sub_eq_zero.mp h
      rw [this, one_smul] at hc
      calc isoVec a i - isoVec a k = (isoVec a i - isoVec a j) - (isoVec a k - isoVec a j) := by
            abel
        _ = 0 := by rw [← hc, sub_self]
  · exact hW h

include hsph ha in
/-- A functional vanishing at two points of the sphere and not at a third. -/
theorem exists_line_functional {i j k : Fin s} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ ℓ : Option (Fin d) → Coeff a, affEval a ℓ j = 0 ∧ affEval a ℓ k = 0 ∧
      affEval a ℓ i ≠ 0 := by
  obtain ⟨ℓ, h0, h1⟩ := exists_functional_of_notMem a _
    (isoVec_notMem_span_singleton a c' C hsph ha hij hik hjk)
  exact ⟨ℓ, h0 j (by simp), h0 k (Submodule.subset_span rfl), h1⟩

include hsph ha in
/-- A functional vanishing on a set of at most two of the points and not at a point outside it. -/
theorem exists_group_functional (T : Finset (Fin s)) (hT : T.card ≤ 2) {i : Fin s} (hi : i ∉ T) :
    ∃ ℓ : Option (Fin d) → Coeff a, (∀ j ∈ T, affEval a ℓ j = 0) ∧ affEval a ℓ i ≠ 0 := by
  obtain h | h | h : T.card = 0 ∨ T.card = 1 ∨ T.card = 2 := by omega
  · rw [Finset.card_eq_zero.mp h]
    exact ⟨_, by simp, by rw [affEval_one]; exact one_ne_zero⟩
  · obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp h
    obtain ⟨ℓ, h0, h1⟩ := exists_point_functional a ha (i := i) (j := j)
      (fun hij => hi (by simp [hij]))
    exact ⟨ℓ, by simpa using h0, h1⟩
  · obtain ⟨j, k, hjk, rfl⟩ := Finset.card_eq_two.mp h
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    obtain ⟨ℓ, hj, hk, h1⟩ := exists_line_functional a c' C hsph ha hi.1 hi.2 hjk
    refine ⟨ℓ, fun m hm => ?_, h1⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · exact hj
    · exact hk

include hsph ha in
/-- At most five points on a sphere: every point has an isolating quadric. -/
theorem exists_isolators_of_le_five (hs : s ≤ 5) :
    ∃ q : Fin s → Matrix (Option (Fin d)) (Option (Fin d)) (Coeff a),
      ∀ i j, quadEval a (q i) j = if i = j then 1 else 0 := by
  classical
  have key : ∀ i : Fin s, ∃ M : Matrix (Option (Fin d)) (Option (Fin d)) (Coeff a),
      ∀ j, quadEval a M j = if i = j then 1 else 0 := by
    intro i
    have hOc : (Finset.univ.erase i).card ≤ 4 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨T₁, hT₁O, hT₁c⟩ := Finset.exists_subset_card_eq
      (show min 2 (Finset.univ.erase i).card ≤ (Finset.univ.erase i).card from min_le_right _ _)
    have hT₂c : ((Finset.univ.erase i) \ T₁).card ≤ 2 := by
      rw [Finset.card_sdiff_of_subset hT₁O]
      omega
    obtain ⟨ℓ₁, hv₁, hi₁⟩ := exists_group_functional a c' C hsph ha T₁ (by omega)
      (i := i) (fun h => by simpa using hT₁O h)
    obtain ⟨ℓ₂, hv₂, hi₂⟩ := exists_group_functional a c' C hsph ha
      ((Finset.univ.erase i) \ T₁) hT₂c (i := i) (by simp)
    refine exists_isolator_of_pair a ℓ₁ ℓ₂ hi₁ hi₂ fun j hj => ?_
    by_cases hjT : j ∈ T₁
    · exact Or.inl (hv₁ j hjT)
    · exact Or.inr (hv₂ j (Finset.mem_sdiff.mpr ⟨by simp [hj], hjT⟩))
  choose q hq using key
  exact ⟨q, hq⟩

end sphere

section six

variable (a : Fin 6 → Space d) (c' : Fin d → Coeff a) (C : Coeff a)
  (hsph : ∀ i, ∑ j, coordinate a i j ^ 2 - 2 * ∑ j, c' j * coordinate a i j + C = 0)
  (ha : Function.Injective a)

/-- A functional vanishing at three points `a j`, `a k`, `a l` whose plane misses a fourth point
`a i`, and not at `a i`. The non-membership is stated over `ℝ`: `a i − a j` is not in the real
span of the two chords `a k − a j`, `a l − a j`; it is pulled back to `F` by coercion, and a
separating functional on `F^d` gives the affine function. -/
theorem exists_plane_functional {i j k l : Fin 6}
    (hout : a i - a j ∉ Submodule.span ℝ {a k - a j, a l - a j}) :
    ∃ ℓ : Option (Fin d) → Coeff a, affEval a ℓ j = 0 ∧ affEval a ℓ k = 0 ∧
      affEval a ℓ l = 0 ∧ affEval a ℓ i ≠ 0 := by
  have hu : isoVec a i - isoVec a j ∉
      Submodule.span (Coeff a) {isoVec a k - isoVec a j, isoVec a l - isoVec a j} := by
    intro hmem
    obtain ⟨r, t, hrt⟩ := Submodule.mem_span_pair.mp hmem
    apply hout
    refine Submodule.mem_span_pair.mpr ⟨(r : ℝ), (t : ℝ), ?_⟩
    ext n
    have := congrArg Subtype.val (congrFun hrt n)
    simpa [isoVec, coordinate_coe] using this
  obtain ⟨ℓ, h0, h1⟩ := exists_functional_of_notMem a _ hu
  exact ⟨ℓ, h0 j (by simp), h0 k (Submodule.subset_span (by simp)),
    h0 l (Submodule.subset_span (by simp)), h1⟩

/-- Points of a spanning configuration in `Space d`, `d ≥ 3`, do not all lie in an affine plane
`p + span {x, y}`. -/
theorem not_planar_of_spanning (hd : 3 ≤ d) (hspan : affineSpan ℝ (Set.range a) = ⊤) (p x y : Space d)
    (h : ∀ m, a m - p ∈ Submodule.span ℝ {x, y}) : False := by
  classical
  have hle : affineSpan ℝ (Set.range a) ≤ AffineSubspace.mk' p (Submodule.span ℝ {x, y}) := by
    rw [affineSpan_le]
    rintro _ ⟨m, rfl⟩
    exact AffineSubspace.mem_mk'.mpr (h m)
  rw [hspan] at hle
  have hdir := AffineSubspace.direction_le hle
  rw [AffineSubspace.direction_top, AffineSubspace.direction_mk'] at hdir
  have h1 := Submodule.finrank_mono hdir
  rw [finrank_top, finrank_euclideanSpace, Fintype.card_fin] at h1
  have h2 := finrank_span_le_card (R := ℝ) ({x, y} : Set (Space d))
  have h3 : ({x, y} : Set (Space d)).toFinset.card ≤ 2 := by
    rw [Set.toFinset_insert, Set.toFinset_singleton]
    exact Finset.card_le_two
  omega

/-- If `a_i` lies in the affine hull of every three other points, all six points lie in an
affine plane through `a_i`. -/
theorem planar_of_no_isolating_triple (i : Fin 6)
    (h : ∀ j k l : Fin 6, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      a i - a j ∈ Submodule.span ℝ {a k - a j, a l - a j}) :
    ∃ x y : Space d, ∀ m, a m - a i ∈ Submodule.span ℝ {x, y} := by
  by_cases hA : ∃ p q, i ≠ p ∧ i ≠ q ∧ p ≠ q ∧
      ∀ α β : ℝ, α • (a p - a i) + β • (a q - a i) = 0 → α = 0 ∧ β = 0
  · obtain ⟨p, q, hip, hiq, hpq, hind⟩ := hA
    refine ⟨a p - a i, a q - a i, fun m => ?_⟩
    by_cases hmi : m = i
    · subst hmi; simp
    by_cases hmp : m = p
    · subst hmp; exact Submodule.subset_span (by simp)
    by_cases hmq : m = q
    · subst hmq; exact Submodule.subset_span (by simp)
    obtain ⟨r, t, hrt⟩ := Submodule.mem_span_pair.mp
      (h p q m hip hiq (Ne.symm hmi) hpq (Ne.symm hmp) (Ne.symm hmq))
    have ht : t ≠ 0 := by
      rintro rfl
      have := hind (1 - r) r (by linear_combination (norm := module) hrt)
      exact absurd (sub_eq_zero.mp this.1) (by rw [this.2]; norm_num)
    refine Submodule.mem_span_pair.mpr ⟨(r + t - 1) / t, -r / t, ?_⟩
    apply smul_right_injective (Space d) ht
    simp only [smul_add, smul_smul]
    rw [mul_div_cancel₀ _ ht, mul_div_cancel₀ _ ht]
    linear_combination (norm := module) (-1 : ℝ) • hrt
  · push Not at hA
    by_cases hB : ∃ p, i ≠ p ∧ a p - a i ≠ 0
    · obtain ⟨p, hip, hp⟩ := hB
      refine ⟨a p - a i, 0, fun m => ?_⟩
      by_cases hmi : m = i
      · subst hmi; simp
      by_cases hmp : m = p
      · subst hmp; exact Submodule.subset_span (by simp)
      obtain ⟨α, β, hαβ, hne⟩ := hA p m hip (Ne.symm hmi) (Ne.symm hmp)
      have hβ : β ≠ 0 := by
        rintro rfl
        have hα : α ≠ 0 := fun h0 => hne h0 rfl
        rw [zero_smul, add_zero, smul_eq_zero] at hαβ
        exact hαβ.elim hα hp
      refine Submodule.mem_span_pair.mpr ⟨-α / β, 0, ?_⟩
      apply smul_right_injective (Space d) hβ
      simp only [smul_smul, smul_zero, add_zero]
      rw [mul_div_cancel₀ _ hβ]
      linear_combination (norm := module) (-1 : ℝ) • hαβ
    · push Not at hB
      refine ⟨0, 0, fun m => ?_⟩
      by_cases hmi : m = i
      · subst hmi; simp
      rw [hB m (Ne.symm hmi)]
      exact zero_mem _

/-- Six points of a sphere that affinely span a space of dimension at least three: for every
point some three of the others span a plane that misses it. -/
theorem exists_isolating_triple (hd : 3 ≤ d) (hspan : affineSpan ℝ (Set.range a) = ⊤) (i : Fin 6) :
    ∃ j k l : Fin 6, i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l ∧
      a i - a j ∉ Submodule.span ℝ {a k - a j, a l - a j} := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x, y, hxy⟩ := planar_of_no_isolating_triple a i hcon
  exact not_planar_of_spanning a hd hspan (a i) x y hxy

include hsph ha in
/-- Six points of a sphere that affinely span a space of dimension at least three: every point
has an isolating quadric. -/
theorem exists_isolators_of_six (hd : 3 ≤ d) (hspan : affineSpan ℝ (Set.range a) = ⊤) :
    ∃ q : Fin 6 → Matrix (Option (Fin d)) (Option (Fin d)) (Coeff a),
      ∀ i j, quadEval a (q i) j = if i = j then 1 else 0 := by
  classical
  have key : ∀ i : Fin 6, ∃ M : Matrix (Option (Fin d)) (Option (Fin d)) (Coeff a),
      ∀ j, quadEval a M j = if i = j then 1 else 0 := by
    intro i
    obtain ⟨j, k, l, hij, hik, hil, hjk, hjl, hkl, hout⟩ := exists_isolating_triple a hd hspan i
    obtain ⟨ℓ₁, hj, hk, hl, hi₁⟩ := exists_plane_functional a hout
    have h4 : ({i, j, k, l} : Finset (Fin 6)).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp [hij, hik, hil]),
        Finset.card_insert_of_notMem (by simp [hjk, hjl]), Finset.card_pair_eq_two_iff.mpr hkl]
    have hTc : (Finset.univ \ {i, j, k, l}).card ≤ 2 := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
        Fintype.card_fin, h4]
    obtain ⟨ℓ₂, hv₂, hi₂⟩ := exists_group_functional a c' C hsph ha
      (Finset.univ \ {i, j, k, l}) hTc (i := i) (by simp)
    refine exists_isolator_of_pair a ℓ₁ ℓ₂ hi₁ hi₂ fun m hm => ?_
    by_cases hmj : m = j
    · exact Or.inl (hmj ▸ hj)
    by_cases hmk : m = k
    · exact Or.inl (hmk ▸ hk)
    by_cases hml : m = l
    · exact Or.inl (hml ▸ hl)
    exact Or.inr (hv₂ m (by simp [hm, hmj, hmk, hml]))
  choose q hq using key
  exact ⟨q, hq⟩

end six

end

end SixConcyclic

end
