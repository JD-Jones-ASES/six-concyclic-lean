module

public import SixConcyclic.Defs

/-!
# The tensor ring: inclusions, multiplication, and the criterion in ring-homomorphism form

`ι₁ x = x ⊗ 1`, `ι₂ y = 1 ⊗ y` and `μ (x ⊗ y) = xy` on `F ⊗_ℚ F`, `F = Coeff a`. The sandwich
`(x ⊗ 1) * T * (1 ⊗ y)` of `FieldCriterion` is `ι₁ x * T * ι₂ y` by definition, so a certificate
can be built and checked entirely through these three ring homomorphisms.
-/

@[expose] public section

namespace SixConcyclic

noncomputable section
open scoped TensorProduct

variable {s d : ℕ} (a : Fin s → Space d)

/-- The left inclusion `x ↦ x ⊗ 1` of the coordinate field into the tensor ring. -/
def ι₁ : Coeff a →+* TensorRing a := Algebra.TensorProduct.includeLeftRingHom

/-- The right inclusion `y ↦ 1 ⊗ y`. -/
def ι₂ : Coeff a →+* TensorRing a :=
  (Algebra.TensorProduct.includeRight : Coeff a →ₐ[ℚ] TensorRing a).toRingHom

/-- The multiplication map `x ⊗ y ↦ xy` as a ring homomorphism (`multiply a` forgets its
ℚ-linearity). -/
def μ : TensorRing a →+* Coeff a := (multiply a).toRingHom

theorem ι₁_apply (x : Coeff a) : ι₁ a x = x ⊗ₜ[ℚ] (1 : Coeff a) := rfl

theorem ι₂_apply (x : Coeff a) : ι₂ a x = (1 : Coeff a) ⊗ₜ[ℚ] x := rfl

theorem μ_apply (z : TensorRing a) : μ a z = multiply a z := rfl

theorem μ_tmul (x y : Coeff a) : μ a (x ⊗ₜ[ℚ] y) = x * y :=
  Algebra.TensorProduct.lmul'_apply_tmul x y

theorem μ_ι₁ (x : Coeff a) : μ a (ι₁ a x) = x := by
  rw [ι₁_apply, μ_tmul, mul_one]

theorem μ_ι₂ (x : Coeff a) : μ a (ι₂ a x) = x := by
  rw [ι₂_apply, μ_tmul, one_mul]

theorem ι₁_mul_ι₂ (x y : Coeff a) : ι₁ a x * ι₂ a y = x ⊗ₜ[ℚ] y := by
  rw [ι₁_apply, ι₂_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- `FieldCriterion` with the sandwich written through the inclusions. -/
theorem fieldCriterion_iff : FieldCriterion a ↔
    ∃ P : Matrix (Option (Fin d)) (Option (Fin d)) (TensorRing a),
      (∀ i : Fin s, ∑ α, ∑ β, ι₁ a (augmented a i α) * P α β * ι₂ a (augmented a i β) = 0) ∧
      (∀ α β : Fin d, μ a (P (some α) (some β)) = if α = β then 1 else 0) :=
  Iff.rfl

/-- A certificate given through the inclusions. -/
theorem fieldCriterion_of_matrix (P : Matrix (Option (Fin d)) (Option (Fin d)) (TensorRing a))
    (hev : ∀ i : Fin s, ∑ α, ∑ β, ι₁ a (augmented a i α) * P α β * ι₂ a (augmented a i β) = 0)
    (hsp : ∀ α β : Fin d, μ a (P (some α) (some β)) = if α = β then 1 else 0) :
    FieldCriterion a :=
  (fieldCriterion_iff a).mpr ⟨P, hev, hsp⟩

/-- The sandwich of a certificate, read through the inclusions. -/
theorem fieldCriterion_matrix (h : FieldCriterion a) :
    ∃ P : Matrix (Option (Fin d)) (Option (Fin d)) (TensorRing a),
      (∀ i : Fin s, ∑ α, ∑ β, ι₁ a (augmented a i α) * P α β * ι₂ a (augmented a i β) = 0) ∧
      (∀ α β : Fin d, μ a (P (some α) (some β)) = if α = β then 1 else 0) :=
  (fieldCriterion_iff a).mp h

end

end SixConcyclic

end
