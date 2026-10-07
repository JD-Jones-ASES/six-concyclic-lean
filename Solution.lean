module

public import SixConcyclic.Main
public import SixConcyclic.Dimension

/-!
# The compared theorems

The fourteen theorems of `Challenge.lean`, restated character for character and proved from the
development. This file does not import `Challenge.lean`; the definitions it uses are those of
`SixConcyclic/Defs.lean`, which repeats the challenge's definitions.
-/

@[expose] public section

namespace SixConcyclic

noncomputable section

/-- Every set of six distinct points on a circle satisfies the tensor criterion. -/
theorem six_concyclic_fieldCriterion (a : Fin 6 → Space 2) (ha : Function.Injective a)
    (hsphere : ∃ c : Space 2, ∃ r : ℝ, ∀ i, dist (a i) c = r) : FieldCriterion a :=
  six_concyclic_fieldCriterion_internal a ha hsphere

/-- Every set of at most six distinct points on a circle satisfies the tensor criterion. -/
theorem at_most_six_concyclic_fieldCriterion {s : ℕ} (a : Fin s → Space 2) (hs : s ≤ 6)
    (ha : Function.Injective a) (hsphere : ∃ c : Space 2, ∃ r : ℝ, ∀ i, dist (a i) c = r) :
    FieldCriterion a :=
  at_most_six_concyclic_fieldCriterion_internal a hs ha hsphere

/-- Every spherical set of at most six distinct points that affinely spans its space satisfies
the tensor criterion. -/
theorem at_most_six_spherical_spanning_fieldCriterion {s d : ℕ} (a : Fin s → Space d)
    (hs : s ≤ 6) (ha : Function.Injective a) (hspan : affineSpan ℝ (Set.range a) = ⊤)
    (hsphere : ∃ c : Space d, ∃ r : ℝ, ∀ i, dist (a i) c = r) : FieldCriterion a :=
  at_most_six_spherical_spanning_fieldCriterion_internal a hs ha hspan hsphere

/-- Every spherical set of at most five distinct points, in any dimension, satisfies the tensor
criterion. -/
theorem at_most_five_spherical_fieldCriterion {s d : ℕ} (a : Fin s → Space d) (hs : s ≤ 5)
    (ha : Function.Injective a) (hsphere : ∃ c : Space d, ∃ r : ℝ, ∀ i, dist (a i) c = r) :
    FieldCriterion a :=
  at_most_five_spherical_fieldCriterion_internal a hs ha hsphere

/-- Every spherical set whose coordinates are algebraic numbers satisfies the tensor criterion,
whatever its size: the separability idempotent of `F ⊗_ℚ F` lifts an `F`-rational sphere. -/
theorem algebraic_spherical_fieldCriterion {s d : ℕ} (a : Fin s → Space d)
    (halg : ∀ i j, IsAlgebraic ℚ (a i j))
    (hsphere : ∃ c : Space d, ∃ r : ℝ, ∀ i, dist (a i) c = r) : FieldCriterion a :=
  algebraic_spherical_fieldCriterion_internal a halg hsphere

/-- The tensor criterion implies sphericity: multiplying the certificate gives a sphere through
the points. -/
theorem fieldCriterion_spherical {s d : ℕ} (a : Fin s → Space d) (h : FieldCriterion a) :
    ∃ c : Space d, ∃ r : ℝ, ∀ i, dist (a i) c = r :=
  fieldCriterion_spherical_internal a h

/-- For algebraic coordinates the tensor criterion is exactly sphericity. -/
theorem algebraic_fieldCriterion_iff_spherical {s d : ℕ} (a : Fin s → Space d)
    (halg : ∀ i j, IsAlgebraic ℚ (a i j)) :
    FieldCriterion a ↔ ∃ c : Space d, ∃ r : ℝ, ∀ i, dist (a i) c = r :=
  algebraic_fieldCriterion_iff_spherical_internal a halg

/-- Given the sufficiency half of the classification, every spherical set of at most six
distinct points, in any dimension and with any affine span, is Ramsey. -/
theorem at_most_six_spherical_ramsey_of_sufficiency
    (hsuff : ∀ {s d : ℕ} (a : Fin s → Space d), 2 ≤ s → 1 ≤ d → Function.Injective a →
      affineSpan ℝ (Set.range a) = ⊤ → FieldCriterion a → Ramsey a)
    {s d : ℕ} (a : Fin s → Space d) (hs : s ≤ 6) (ha : Function.Injective a)
    (hsphere : ∃ c : Space d, ∃ r : ℝ, ∀ i, dist (a i) c = r) : Ramsey a :=
  at_most_six_spherical_ramsey_of_sufficiency_internal hsuff a hs ha hsphere

/-- Given the sufficiency half of the classification, every set of at most six distinct points on
a circle is Ramsey. -/
theorem at_most_six_circle_points_ramsey_of_sufficiency
    (hsuff : ∀ {s d : ℕ} (a : Fin s → Space d), 2 ≤ s → 1 ≤ d → Function.Injective a →
      affineSpan ℝ (Set.range a) = ⊤ → FieldCriterion a → Ramsey a)
    {s : ℕ} (a : Fin s → Space 2) (hs : s ≤ 6) (ha : Function.Injective a)
    (hsphere : ∃ c : Space 2, ∃ r : ℝ, ∀ i, dist (a i) c = r) : Ramsey a :=
  at_most_six_spherical_ramsey_of_sufficiency_internal hsuff a hs ha hsphere

/-- Given the sufficiency half of the classification, every spanning spherical set with algebraic
coordinates is Ramsey. -/
theorem algebraic_spherical_ramsey_of_sufficiency
    (hsuff : ∀ {s d : ℕ} (a : Fin s → Space d), 2 ≤ s → 1 ≤ d → Function.Injective a →
      affineSpan ℝ (Set.range a) = ⊤ → FieldCriterion a → Ramsey a)
    {s d : ℕ} (a : Fin s → Space d) (hs : 2 ≤ s) (hd : 1 ≤ d) (ha : Function.Injective a)
    (hspan : affineSpan ℝ (Set.range a) = ⊤) (halg : ∀ i j, IsAlgebraic ℚ (a i j))
    (hsphere : ∃ c : Space d, ∃ r : ℝ, ∀ i, dist (a i) c = r) : Ramsey a :=
  algebraic_spherical_ramsey_of_sufficiency_internal hsuff a hs hd ha hspan halg hsphere

/-- Given the classification, a spanning set with algebraic coordinates is Ramsey if and only if
it is spherical. -/
theorem algebraic_ramsey_iff_spherical_of_classification
    (hclass : ∀ {s d : ℕ} (a : Fin s → Space d), 2 ≤ s → 1 ≤ d → Function.Injective a →
      affineSpan ℝ (Set.range a) = ⊤ → (Ramsey a ↔ FieldCriterion a))
    {s d : ℕ} (a : Fin s → Space d) (hs : 2 ≤ s) (hd : 1 ≤ d) (ha : Function.Injective a)
    (hspan : affineSpan ℝ (Set.range a) = ⊤) (halg : ∀ i j, IsAlgebraic ℚ (a i j)) :
    Ramsey a ↔ ∃ c : Space d, ∃ r : ℝ, ∀ i, dist (a i) c = r :=
  algebraic_ramsey_iff_spherical_of_classification_internal hclass a hs hd ha hspan halg

/-- The dimension theorem: every spherical set of at most `m + 4` distinct points, where
`m` is the dimension of its affine span, satisfies the tensor criterion, in its own space and
coordinate field. -/
theorem spherical_fieldCriterion_of_card_le_finrank_add_four {s d : ℕ} (a : Fin s → Space d)
    (ha : Function.Injective a) (hsphere : ∃ c : Space d, ∃ r : ℝ, ∀ i, dist (a i) c = r)
    (hdim : s ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range a)) + 4) : FieldCriterion a :=
  spherical_fieldCriterion_of_card_le_finrank_add_four_internal a ha hsphere hdim

/-- Every spherical set of at most six distinct points, in any dimension and with any affine
span, satisfies the tensor criterion. -/
theorem at_most_six_spherical_fieldCriterion {s d : ℕ} (a : Fin s → Space d) (hs : s ≤ 6)
    (ha : Function.Injective a) (hsphere : ∃ c : Space d, ∃ r : ℝ, ∀ i, dist (a i) c = r) :
    FieldCriterion a :=
  at_most_six_spherical_fieldCriterion_internal a hs ha hsphere

/-- Given the sufficiency half of the classification, every spherical set of at most `m + 4`
distinct points, `m` the dimension of its affine span, is Ramsey. -/
theorem spherical_ramsey_of_sufficiency_of_card_le_finrank_add_four
    (hsuff : ∀ {s d : ℕ} (a : Fin s → Space d), 2 ≤ s → 1 ≤ d → Function.Injective a →
      affineSpan ℝ (Set.range a) = ⊤ → FieldCriterion a → Ramsey a)
    {s d : ℕ} (a : Fin s → Space d) (ha : Function.Injective a)
    (hsphere : ∃ c : Space d, ∃ r : ℝ, ∀ i, dist (a i) c = r)
    (hdim : s ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range a)) + 4) : Ramsey a :=
  spherical_ramsey_of_sufficiency_of_card_le_finrank_add_four_internal hsuff a ha hsphere hdim

end

end SixConcyclic

end
