module

public import SixConcyclic.Sphere
public import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# The adjugate lift

If every point has an isolating quadric — an `F`-matrix `q i` with `quadEval (q i) j = δ_ij` —
then an `F`-rational sphere matrix `H` lifts to a tensor certificate. With `D` the `s × n` matrix
over `B = F ⊗ F` whose rows are `ι₁ (p_i)_α · ι₂ (p_i)_β` (`n = (d+1)²`), `S` the `n × s` matrix
with columns `ι₁ (q_i)`, `N = D S` (so `μ N = I`), `b = ι₁ H` flattened and
`z = det N • b − S (adj N (D b))`: `D z = 0` because `N adj N = det N • I`, and `μ z = H`
because `μ (det N) = 1`, `μ (adj N) = adj I = I` and `μ (D b) = 0`. This is the argument of
Proposition 7.3 of the source, without the choice of a minor.
-/

@[expose] public section

namespace SixConcyclic

noncomputable section
open scoped TensorProduct
open Matrix

/-- The adjugate lift over a ring homomorphism: if `μ (D S) = I`, every vector `b` with
`μ (D b) = 0` has a lift `z` with `D z = 0` and `μ z = μ b`. Adapts `lift_kernel` of openai/math
`Quadratic.lean` (Apache-2.0), with the right inverse `S` given instead of chosen. -/
theorem lift_of_rightInverse {F B ι ν : Type*} [CommRing F] [CommRing B]
    [Fintype ι] [Fintype ν] [DecidableEq ι]
    (f : B →+* F) (D : Matrix ι ν B) (S : Matrix ν ι B) (hN : (D * S).map f = 1)
    (b : ν → B) (hb : D.map f *ᵥ (f ∘ b) = 0) :
    ∃ z : ν → B, D *ᵥ z = 0 ∧ ∀ q, f (z q) = f (b q) := by
  set N : Matrix ι ι B := D * S with hNdef
  have hdet : f N.det = 1 := by
    rw [f.map_det, RingHom.mapMatrix_apply, hN, Matrix.det_one]
  have hDb : ∀ i, f ((D *ᵥ b) i) = 0 := by
    intro i
    rw [f.map_mulVec, hb]
    rfl
  have hAdj : ∀ i, f ((N.adjugate *ᵥ (D *ᵥ b)) i) = 0 := by
    intro i
    rw [f.map_mulVec]
    have h0 : (f ∘ (D *ᵥ b)) = 0 := funext hDb
    rw [h0, Matrix.mulVec_zero]
    rfl
  have hCor : ∀ q, f ((S *ᵥ (N.adjugate *ᵥ (D *ᵥ b))) q) = 0 := by
    intro q
    rw [f.map_mulVec]
    have h0 : (f ∘ (N.adjugate *ᵥ (D *ᵥ b))) = 0 := funext hAdj
    rw [h0, Matrix.mulVec_zero]
    rfl
  refine ⟨N.det • b - S *ᵥ (N.adjugate *ᵥ (D *ᵥ b)), ?_, ?_⟩
  · rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← hNdef,
      Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]
  · intro q
    rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, hdet, one_mul, hCor q,
      sub_zero]

variable {s d : ℕ} (a : Fin s → Space d)

/-- `μ` of a sandwich of inclusions is the product. -/
theorem μ_ι₁_mul_ι₂ (x y : Coeff a) : μ a (ι₁ a x * ι₂ a y) = x * y := by
  rw [map_mul, μ_ι₁, μ_ι₂]

/-- An `F`-rational sphere matrix lifts to a tensor certificate whenever every point has an
isolating quadric. The reshaping into `FieldCriterion` adapts `quadraticIndependent_fieldCriterion`
of openai/math `Quadratic.lean` (Apache-2.0; see `NOTICE`). -/
theorem fieldCriterion_of_isolators
    (H : Matrix (Option (Fin d)) (Option (Fin d)) (Coeff a))
    (hH : ∀ i, quadEval a H i = 0)
    (hI : ∀ α β : Fin d, H (some α) (some β) = if α = β then 1 else 0)
    (q : Fin s → Matrix (Option (Fin d)) (Option (Fin d)) (Coeff a))
    (hq : ∀ i j, quadEval a (q i) j = if i = j then 1 else 0) : FieldCriterion a := by
  let D : Matrix (Fin s) (Option (Fin d) × Option (Fin d)) (TensorRing a) :=
    fun i αβ => ι₁ a (augmented a i αβ.1) * ι₂ a (augmented a i αβ.2)
  let S : Matrix (Option (Fin d) × Option (Fin d)) (Fin s) (TensorRing a) :=
    fun αβ j => ι₁ a (q j αβ.1 αβ.2)
  let b : Option (Fin d) × Option (Fin d) → TensorRing a := fun αβ => ι₁ a (H αβ.1 αβ.2)
  have hDmap : ∀ i αβ, D.map (μ a) i αβ = augmented a i αβ.1 * augmented a i αβ.2 := by
    intro i αβ
    exact μ_ι₁_mul_ι₂ a _ _
  have hN : (D * S).map (μ a) = 1 := by
    refine Matrix.ext fun i j => ?_
    have e : (1 : Matrix (Fin s) (Fin s) (Coeff a)) i j = quadEval a (q j) i := by
      rw [hq j i, Matrix.one_apply]
      by_cases h : i = j
      · subst h
        simp
      · simp [h, Ne.symm h]
    rw [e, Matrix.map_apply, Matrix.mul_apply, map_sum, quadEval, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    change μ a (ι₁ a _ * ι₂ a _ * ι₁ a _) = _
    rw [map_mul, map_mul, μ_ι₁, μ_ι₂, μ_ι₁]
    ring
  obtain ⟨z, hz, hzμ⟩ := lift_of_rightInverse (μ a) D S hN b (by
    funext i
    rw [Pi.zero_apply, Matrix.mulVec, dotProduct, ← hH i, quadEval, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    rw [hDmap, Function.comp_apply]
    change _ * μ a (ι₁ a _) = _
    rw [μ_ι₁]
    ring)
  refine fieldCriterion_of_matrix a (fun α β => z (α, β)) ?_ ?_
  · intro i
    have ht := congrFun hz i
    rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Pi.zero_apply] at ht
    rw [← ht]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    exact (mul_right_comm (ι₁ a (augmented a i α)) (ι₂ a (augmented a i β)) (z (α, β))).symm
  · intro α β
    rw [hzμ (some α, some β)]
    simp only [b, μ_ι₁]
    exact hI α β

end

end SixConcyclic

end
