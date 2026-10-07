module

public import SixConcyclic.Tensor
public import SixConcyclic.Sphere
public import SixConcyclic.Ordered
public import SixConcyclic.Lift
public import SixConcyclic.Isolators
public import SixConcyclic.Core
public import SixConcyclic.Param
public import SixConcyclic.Assembly
public import SixConcyclic.Algebraic
public import SixConcyclic.Ramsey
public import SixConcyclic.Transport

/-!
# The first eleven theorems, assembled

Eleven of the compared theorems of `Challenge.lean` have internal versions here (the three
dimension theorems are in `Dimension.lean`), proved from the modules:
the six-point certificate (`Assembly`), the adjugate lift with pairing or triple isolators
(`Lift`, `Isolators`), the algebraic case (`Algebraic`), sphericity from the criterion (`Sphere`),
and the Ramsey glue (`Ramsey`, `Transport`).
-/

@[expose] public section

namespace SixConcyclic

noncomputable section

/-- Six distinct concyclic points in the plane satisfy the tensor criterion. -/
theorem six_concyclic_fieldCriterion_internal (a : Fin 6 → Space 2) (ha : Function.Injective a)
    (hsphere : ∃ c : Space 2, ∃ r : ℝ, ∀ i, dist (a i) c = r) : FieldCriterion a :=
  Asm.six_concyclic_certificate a ha hsphere

/-- An `F`-rational sphere with isolating quadrics for every point gives the criterion. -/
theorem fieldCriterion_of_sphere_isolators {s d : ℕ} (a : Fin s → Space d)
    (c' : Fin d → Coeff a) (C : Coeff a)
    (hsph : ∀ i, ∑ j, coordinate a i j ^ 2 - 2 * ∑ j, c' j * coordinate a i j + C = 0)
    (q : Fin s → Matrix (Option (Fin d)) (Option (Fin d)) (Coeff a))
    (hq : ∀ i j, quadEval a (q i) j = if i = j then 1 else 0) : FieldCriterion a :=
  fieldCriterion_of_isolators a (sphereMatrix a c' C)
    (fun i => by rw [quadEval_sphereMatrix]; exact hsph i) (sphereMatrix_spatial a c' C) q hq

theorem at_most_five_spherical_fieldCriterion_internal {s d : ℕ} (a : Fin s → Space d)
    (hs : s ≤ 5) (ha : Function.Injective a)
    (hsphere : ∃ c : Space d, ∃ r : ℝ, ∀ i, dist (a i) c = r) : FieldCriterion a := by
  obtain ⟨c', C, hsph⟩ := exists_rational_sphere a hsphere
  obtain ⟨q, hq⟩ := exists_isolators_of_le_five a c' C hsph ha hs
  exact fieldCriterion_of_sphere_isolators a c' C hsph q hq

theorem at_most_six_concyclic_fieldCriterion_internal {s : ℕ} (a : Fin s → Space 2) (hs : s ≤ 6)
    (ha : Function.Injective a) (hsphere : ∃ c : Space 2, ∃ r : ℝ, ∀ i, dist (a i) c = r) :
    FieldCriterion a := by
  rcases Nat.lt_or_ge s 6 with h5 | h6
  · exact at_most_five_spherical_fieldCriterion_internal a (by omega) ha hsphere
  · obtain rfl : s = 6 := le_antisymm hs h6
    exact six_concyclic_fieldCriterion_internal a ha hsphere

/-- No six distinct points of a sphere fit in a space of dimension at most one: the Gram
determinant of two chords from a common point vanishes there. -/
theorem not_six_spherical_of_dim_le_one {d : ℕ} (hd : d ≤ 1) (a : Fin 6 → Space d)
    (ha : Function.Injective a) (hsphere : ∃ c : Space d, ∃ r : ℝ, ∀ i, dist (a i) c = r) :
    False := by
  obtain ⟨c', C, hsph⟩ := exists_rational_sphere a hsphere
  have hg := gram_ne_zero a c' C hsph ha (i := 0) (j := 1) (k := 2) (by decide) (by decide)
    (by decide)
  apply hg
  interval_cases d
  · simp
  · simp only [Fin.sum_univ_one]
    ring

theorem at_most_six_spherical_spanning_fieldCriterion_internal {s d : ℕ} (a : Fin s → Space d)
    (hs : s ≤ 6) (ha : Function.Injective a) (hspan : affineSpan ℝ (Set.range a) = ⊤)
    (hsphere : ∃ c : Space d, ∃ r : ℝ, ∀ i, dist (a i) c = r) : FieldCriterion a := by
  rcases Nat.lt_or_ge s 6 with h5 | h6
  · exact at_most_five_spherical_fieldCriterion_internal a (by omega) ha hsphere
  obtain rfl : s = 6 := le_antisymm hs h6
  rcases Nat.lt_or_ge d 3 with hd | hd
  · rcases Nat.lt_or_ge d 2 with hd1 | hd2
    · exact (not_six_spherical_of_dim_le_one (by omega) a ha hsphere).elim
    · obtain rfl : d = 2 := le_antisymm (by omega) hd2
      exact six_concyclic_fieldCriterion_internal a ha hsphere
  · obtain ⟨c', C, hsph⟩ := exists_rational_sphere a hsphere
    obtain ⟨q, hq⟩ := exists_isolators_of_six a c' C hsph ha hd hspan
    exact fieldCriterion_of_sphere_isolators a c' C hsph q hq

theorem algebraic_fieldCriterion_iff_spherical_internal {s d : ℕ} (a : Fin s → Space d)
    (halg : ∀ i j, IsAlgebraic ℚ (a i j)) :
    FieldCriterion a ↔ ∃ c : Space d, ∃ r : ℝ, ∀ i, dist (a i) c = r :=
  ⟨fun h => fieldCriterion_spherical_internal a h,
    fun h => algebraic_spherical_fieldCriterion_internal a halg h⟩

theorem at_most_six_spherical_ramsey_of_sufficiency_internal
    (hsuff : ∀ {s d : ℕ} (a : Fin s → Space d), 2 ≤ s → 1 ≤ d → Function.Injective a →
      affineSpan ℝ (Set.range a) = ⊤ → FieldCriterion a → Ramsey a)
    {s d : ℕ} (a : Fin s → Space d) (hs : s ≤ 6) (ha : Function.Injective a)
    (hsphere : ∃ c : Space d, ∃ r : ℝ, ∀ i, dist (a i) c = r) : Ramsey a := by
  rcases Nat.lt_or_ge s 2 with hs2 | hs2
  · rcases Nat.lt_or_ge s 1 with hs0 | hs1
    · obtain rfl : s = 0 := by omega
      exact ramsey_empty a
    · obtain rfl : s = 1 := by omega
      exact ramsey_singleton a
  · obtain ⟨d', hd', b, hb, hab, hspan, hsph'⟩ := exists_spanning_representative a hs2 ha hsphere
    exact ramsey_of_congruent hab (hsuff b hs2 hd' hb hspan
      (at_most_six_spherical_spanning_fieldCriterion_internal b hs hb hspan hsph'))

theorem algebraic_spherical_ramsey_of_sufficiency_internal
    (hsuff : ∀ {s d : ℕ} (a : Fin s → Space d), 2 ≤ s → 1 ≤ d → Function.Injective a →
      affineSpan ℝ (Set.range a) = ⊤ → FieldCriterion a → Ramsey a)
    {s d : ℕ} (a : Fin s → Space d) (hs : 2 ≤ s) (hd : 1 ≤ d) (ha : Function.Injective a)
    (hspan : affineSpan ℝ (Set.range a) = ⊤) (halg : ∀ i j, IsAlgebraic ℚ (a i j))
    (hsphere : ∃ c : Space d, ∃ r : ℝ, ∀ i, dist (a i) c = r) : Ramsey a :=
  hsuff a hs hd ha hspan (algebraic_spherical_fieldCriterion_internal a halg hsphere)

theorem algebraic_ramsey_iff_spherical_of_classification_internal
    (hclass : ∀ {s d : ℕ} (a : Fin s → Space d), 2 ≤ s → 1 ≤ d → Function.Injective a →
      affineSpan ℝ (Set.range a) = ⊤ → (Ramsey a ↔ FieldCriterion a))
    {s d : ℕ} (a : Fin s → Space d) (hs : 2 ≤ s) (hd : 1 ≤ d) (ha : Function.Injective a)
    (hspan : affineSpan ℝ (Set.range a) = ⊤) (halg : ∀ i j, IsAlgebraic ℚ (a i j)) :
    Ramsey a ↔ ∃ c : Space d, ∃ r : ℝ, ∀ i, dist (a i) c = r :=
  (hclass a hs hd ha hspan).trans (algebraic_fieldCriterion_iff_spherical_internal a halg)

end

end SixConcyclic

end
