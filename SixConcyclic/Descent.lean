module

public import SixConcyclic.RealCert
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Descent from `ℝ ⊗_ℚ ℝ` to `F ⊗_ℚ F`

A certificate over the real tensor ring descends to the coordinate field `F = Coeff a`. Let
`(e_γ)` be an `F`-basis of `ℝ` (a Hamel basis; `Basis.ofVectorSpace F ℝ`) and `φ : ℝ → F` an
`F`-linear retraction with `φ 1 = 1` (`Module.Projective.exists_dual_eq_one`, as in
`exists_rational_sphere`). Writing `x = ∑ x_γ e_γ`, `y = ∑ y_δ e_δ` with `x_γ, y_δ ∈ F`, the
ℚ-bilinear map `(x, y) ↦ ∑_{γ,δ} (φ(e_γ e_δ) x_γ) ⊗ y_δ` induces a ℚ-linear
`Ψ : ℝ ⊗_ℚ ℝ → F ⊗_ℚ F` with `Ψ ((c ⊗ 1) z) = (c ⊗ 1) Ψ z` and `Ψ ((1 ⊗ c) z) = (1 ⊗ c) Ψ z` for
`c ∈ F` (the coordinates are `F`-linear) and `μ (Ψ z) = φ (μ_ℝ z)` (on `x ⊗ y`:
`∑ φ(e_γ e_δ) x_γ y_δ = φ(∑ x_γ y_δ e_γ e_δ) = φ(xy)`). Applied entrywise to a real
certificate, `Ψ` preserves the vanishing of the sandwiches (they are `F ⊗ F`-combinations of the
entries, the augmented coordinates being in `F`) and sends the spatial block `I` to `φ(I) = I`.
-/

@[expose] public section

namespace SixConcyclic

noncomputable section
open scoped TensorProduct

open Module

variable {s d : ℕ} (a : Fin s → Space d)

/-- An `F`-linear functional pulls out a coordinate-field factor. -/
theorem dual_coe_mul (φ : Module.Dual (Coeff a) ℝ) (c : Coeff a) (t : ℝ) :
    φ ((c : ℝ) * t) = c * φ t := by
  simpa [Algebra.smul_def] using φ.map_smul c t

/-- Multiplication by an element of the coordinate field is its scalar action on `ℝ`. -/
theorem coe_mul_eq_smul (c : Coeff a) (t : ℝ) : (c : ℝ) * t = c • t := by
  rw [Algebra.smul_def, IntermediateField.algebraMap_apply]

/-- The bilinear descent map `(x, y) ↦ ∑_δ φ(x e_δ) ⊗ y_δ`. -/
def descentPair {ι : Type*} (b : Basis ι (Coeff a) ℝ) (φ : Module.Dual (Coeff a) ℝ) (x y : ℝ) :
    TensorRing a :=
  (b.repr y).sum fun δ c => φ (x * b δ) ⊗ₜ[ℚ] c

/-- `descentPair` as a ℚ-bilinear map. -/
def descentBil {ι : Type*} (b : Basis ι (Coeff a) ℝ) (φ : Module.Dual (Coeff a) ℝ) :
    ℝ →ₗ[ℚ] ℝ →ₗ[ℚ] TensorRing a :=
  LinearMap.mk₂ ℚ (descentPair a b φ)
    (fun x x' y => by
      simp only [descentPair, add_mul, map_add, TensorProduct.add_tmul, Finsupp.sum_add])
    (fun q x y => by
      simp only [descentPair, smul_mul_assoc, map_rat_smul, ← TensorProduct.smul_tmul',
        Finsupp.smul_sum])
    (fun x y y' => by
      simp only [descentPair, map_add]
      exact Finsupp.sum_add_index' (fun _ => TensorProduct.tmul_zero _ _)
        (fun _ _ _ => TensorProduct.tmul_add _ _ _))
    (fun q x y => by
      simp only [descentPair, map_rat_smul]
      rw [Finsupp.sum_smul_index' (fun _ => TensorProduct.tmul_zero _ _), Finsupp.smul_sum]
      exact Finsupp.sum_congr fun _ _ => TensorProduct.tmul_smul _ _ _)

/-- The descent map `Ψ : ℝ ⊗_ℚ ℝ → F ⊗_ℚ F`. -/
def descentMap {ι : Type*} (b : Basis ι (Coeff a) ℝ) (φ : Module.Dual (Coeff a) ℝ) :
    RT →ₗ[ℚ] TensorRing a :=
  TensorProduct.lift (descentBil a b φ)

theorem descentMap_tmul {ι : Type*} (b : Basis ι (Coeff a) ℝ) (φ : Module.Dual (Coeff a) ℝ)
    (x y : ℝ) : descentMap a b φ (x ⊗ₜ[ℚ] y) = descentPair a b φ x y := by
  rw [descentMap, TensorProduct.lift.tmul]
  rfl

/-- `Ψ` commutes with the left action of the coordinate field. -/
theorem descentMap_ιl {ι : Type*} (b : Basis ι (Coeff a) ℝ) (φ : Module.Dual (Coeff a) ℝ)
    (c : Coeff a) (z : RT) : descentMap a b φ (ιl (c : ℝ) * z) = ι₁ a c * descentMap a b φ z := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    rw [ιl_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, descentMap_tmul, descentMap_tmul,
      descentPair, descentPair, Finsupp.mul_sum]
    refine Finsupp.sum_congr fun δ _ => ?_
    rw [mul_assoc, dual_coe_mul, ι₁_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | add z z' hz hz' => rw [mul_add, map_add, map_add, hz, hz', mul_add]

/-- `Ψ` commutes with the right action of the coordinate field. -/
theorem descentMap_ιr {ι : Type*} (b : Basis ι (Coeff a) ℝ) (φ : Module.Dual (Coeff a) ℝ)
    (c : Coeff a) (z : RT) : descentMap a b φ (ιr (c : ℝ) * z) = ι₂ a c * descentMap a b φ z := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    rw [ιr_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, descentMap_tmul, descentMap_tmul,
      descentPair, descentPair, coe_mul_eq_smul, map_smul,
      Finsupp.sum_smul_index' (fun _ => TensorProduct.tmul_zero _ _), Finsupp.mul_sum]
    refine Finsupp.sum_congr fun δ _ => ?_
    rw [ι₂_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, smul_eq_mul]
  | add z z' hz hz' => rw [mul_add, map_add, map_add, hz, hz', mul_add]

/-- `μ ∘ Ψ = φ ∘ μr`. -/
theorem μ_descentMap {ι : Type*} (b : Basis ι (Coeff a) ℝ) (φ : Module.Dual (Coeff a) ℝ)
    (z : RT) : μ a (descentMap a b φ z) = φ (μr z) := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    rw [descentMap_tmul, descentPair, map_finsuppSum, μr_tmul]
    conv_rhs => rw [← b.linearCombination_repr y]
    rw [Finsupp.linearCombination_apply, Finsupp.mul_sum, map_finsuppSum]
    refine Finsupp.sum_congr fun δ _ => ?_
    rw [μ_tmul, mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
  | add z z' hz hz' => rw [map_add, map_add, hz, hz', map_add, map_add]

/-- A real certificate with spatial block `I` descends to the coordinate field. -/
theorem fieldCriterion_of_realCert {s d : ℕ} (a : Fin s → Space d)
    (H : Matrix (Option (Fin d)) (Option (Fin d)) ℝ) (h : RealCert (aug a) H)
    (hI : ∀ α β : Fin d, H (some α) (some β) = if α = β then 1 else 0) : FieldCriterion a := by
  obtain ⟨P, hev, hmul⟩ := h
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one (Coeff a) (one_ne_zero : (1 : ℝ) ≠ 0)
  set Ψ := descentMap a (Basis.ofVectorSpace (Coeff a) ℝ) φ with hΨ
  refine fieldCriterion_of_matrix a (P.map Ψ) (fun i => ?_) (fun α β => ?_)
  · have key : ∀ α β, ι₁ a (augmented a i α) * P.map Ψ α β * ι₂ a (augmented a i β) =
        Ψ (ιl (aug a i α) * P α β * ιr (aug a i β)) := by
      intro α β
      rw [aug_eq_coe, aug_eq_coe, Matrix.map_apply, mul_assoc (ιl _), mul_comm (P α β), hΨ,
        descentMap_ιl, descentMap_ιr]
      ring
    simp only [key, ← map_sum, hev i, map_zero]
  · rw [Matrix.map_apply, μ_descentMap]
    have hP : μr (P (some α) (some β)) = H (some α) (some β) := by
      rw [← hmul, Matrix.map_apply]
    rw [hP, hI]
    split_ifs
    · exact hφ
    · exact map_zero φ

end

end SixConcyclic

end
