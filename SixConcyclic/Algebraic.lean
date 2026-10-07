module

public import SixConcyclic.Sphere
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.IntermediateField.Algebraic
public import Mathlib.RingTheory.Unramified.Finite
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.FieldTheory.Separable

/-!
# Algebraic coordinates

If every coordinate is algebraic over `ℚ`, the coordinate field `F` is a number field, so
`F ⊗_ℚ F` is étale over `F` and carries a separability idempotent `t` with `(1 ⊗ x − x ⊗ 1) t = 0`
for every `x` and `μ t = 1` (Mathlib: `Algebra.FormallyUnramified.iff_exists_tensorProduct`).
Then `P = t · (H ⊗ 1)` certifies any `F`-rational sphere matrix `H`: the sandwich
`(x ⊗ 1) t (H ⊗ 1) (1 ⊗ y)` equals `t · (x H y ⊗ 1)`, so the evaluations vanish, and
`μ P = H`. With `exists_rational_sphere` this gives `FieldCriterion` for every spherical set with
algebraic coordinates, of any size.
-/

@[expose] public section

namespace SixConcyclic

noncomputable section
open scoped TensorProduct

variable {s d : ℕ} (a : Fin s → Space d)

/-- Algebraic coordinates give a finite-dimensional coordinate field. -/
theorem finiteDimensional_of_algebraic (halg : ∀ i j, IsAlgebraic ℚ (a i j)) :
    FiniteDimensional ℚ (coordinateField a) := by
  unfold coordinateField
  refine IntermediateField.finiteDimensional_adjoin ?_
  rintro _ ⟨ij, rfl⟩
  exact (halg ij.1 ij.2).isIntegral

/-- The separability idempotent of a number field: a `t` killing every `1 ⊗ x − x ⊗ 1` with
`μ t = 1`. -/
theorem exists_sep_idem [FiniteDimensional ℚ (coordinateField a)] :
    ∃ t : TensorRing a, (∀ x : Coeff a, (ι₂ a x - ι₁ a x) * t = 0) ∧ μ a t = 1 := by
  have : Algebra.FormallyUnramified ℚ (Coeff a) := Algebra.FormallyUnramified.of_isSeparable ℚ _
  exact (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := ℚ) (S := Coeff a)).mp
    inferInstance

/-- Algebraic coordinates plus an `F`-rational sphere matrix give the tensor criterion. -/
theorem fieldCriterion_of_algebraic_sphere (halg : ∀ i j, IsAlgebraic ℚ (a i j))
    (H : Matrix (Option (Fin d)) (Option (Fin d)) (Coeff a))
    (hH : ∀ i, quadEval a H i = 0)
    (hI : ∀ α β : Fin d, H (some α) (some β) = if α = β then 1 else 0) : FieldCriterion a := by
  have := finiteDimensional_of_algebraic a halg
  obtain ⟨t, ht, hm⟩ := exists_sep_idem a
  have hswap : ∀ x : Coeff a, ι₂ a x * t = ι₁ a x * t := by
    intro x
    have := ht x
    rw [sub_mul, sub_eq_zero] at this
    exact this
  refine ⟨Matrix.of fun α β => t * ι₁ a (H α β), ?_, ?_⟩
  · intro i
    have key : ∀ α β, ((augmented a i α) ⊗ₜ[ℚ] (1 : Coeff a)) * (t * ι₁ a (H α β))
        * ((1 : Coeff a) ⊗ₜ[ℚ] (augmented a i β))
        = t * ι₁ a (augmented a i α * H α β * augmented a i β) := by
      intro α β
      rw [← ι₁_apply, ← ι₂_apply]
      calc ι₁ a (augmented a i α) * (t * ι₁ a (H α β)) * ι₂ a (augmented a i β)
          = (ι₂ a (augmented a i β) * t) * (ι₁ a (augmented a i α) * ι₁ a (H α β)) := by ring
        _ = (ι₁ a (augmented a i β) * t) * (ι₁ a (augmented a i α) * ι₁ a (H α β)) := by
          rw [hswap]
        _ = t * ι₁ a (augmented a i α * H α β * augmented a i β) := by
          simp only [map_mul]; ring
    simp only [Matrix.of_apply]
    simp_rw [key, ← Finset.mul_sum, ← map_sum]
    have h0 := hH i
    unfold quadEval at h0
    rw [h0, map_zero, mul_zero]
  · intro α β
    change μ a (t * ι₁ a (H (some α) (some β))) = _
    rw [map_mul, hm, one_mul, μ_ι₁, hI]

/-- Every spherical set with algebraic coordinates satisfies the tensor criterion. -/
theorem algebraic_spherical_fieldCriterion_internal (halg : ∀ i j, IsAlgebraic ℚ (a i j))
    (hsphere : ∃ c : Space d, ∃ r : ℝ, ∀ i, dist (a i) c = r) : FieldCriterion a := by
  obtain ⟨c', C, hC⟩ := exists_rational_sphere a hsphere
  exact fieldCriterion_of_algebraic_sphere a halg (sphereMatrix a c' C)
    (fun i => by rw [quadEval_sphereMatrix]; exact hC i)
    (fun α β => sphereMatrix_spatial a c' C α β)

end

end SixConcyclic

end
