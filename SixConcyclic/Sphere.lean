module

public import SixConcyclic.Tensor
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Spheres over the coordinate field

`quadEval M i` is the quadratic evaluation `p_iᵀ M p_i` of an `F`-matrix at the augmented point
`p_i = (1, a_i)`. A real sphere through the points gives an `F`-rational sphere equation
`|x|² − 2⟨c', x⟩ + C = 0` (`exists_rational_sphere`: apply an `F`-linear retraction `ℝ → F` fixing
`1` to the real equation, the coordinates being in `F`), packaged as the matrix `sphereMatrix c' C`
with spatial block `I`. Conversely the multiplied certificate of `FieldCriterion` is such an
equation with real coefficients, which is a sphere through the points
(`fieldCriterion_spherical_internal`).
-/

@[expose] public section

namespace SixConcyclic

noncomputable section
open scoped TensorProduct

variable {s d : ℕ} (a : Fin s → Space d)

theorem coordinate_coe (i : Fin s) (j : Fin d) : ((coordinate a i j : Coeff a) : ℝ) = a i j := rfl

theorem augmented_none (i : Fin s) : augmented a i none = 1 := rfl

theorem augmented_some (i : Fin s) (j : Fin d) : augmented a i (some j) = coordinate a i j := rfl

/-- The quadratic evaluation `p_iᵀ M p_i` of an `F`-matrix at the `i`-th augmented point. -/
def quadEval (M : Matrix (Option (Fin d)) (Option (Fin d)) (Coeff a)) (i : Fin s) : Coeff a :=
  ∑ α, ∑ β, augmented a i α * M α β * augmented a i β

/-- The sphere matrix of `|x|² − 2⟨c', x⟩ + C`: spatial block `I`, constant row and column `−c'`,
corner `C`. -/
def sphereMatrix (c' : Fin d → Coeff a) (C : Coeff a) :
    Matrix (Option (Fin d)) (Option (Fin d)) (Coeff a) := fun α β =>
  match α, β with
  | none, none => C
  | none, some k => -(c' k)
  | some k, none => -(c' k)
  | some j, some k => if j = k then 1 else 0

theorem sphereMatrix_spatial (c' : Fin d → Coeff a) (C : Coeff a) (j k : Fin d) :
    sphereMatrix a c' C (some j) (some k) = if j = k then 1 else 0 := rfl

/-- The quadratic evaluation of a matrix with spatial block `I`. -/
theorem quadEval_of_spatial (M : Matrix (Option (Fin d)) (Option (Fin d)) (Coeff a))
    (hM : ∀ j k : Fin d, M (some j) (some k) = if j = k then 1 else 0) (i : Fin s) :
    quadEval a M i = ∑ j, coordinate a i j ^ 2 +
      ∑ j, (M none (some j) + M (some j) none) * coordinate a i j + M none none := by
  classical
  simp only [quadEval, Fintype.sum_option, augmented, hM, one_mul, mul_one, mul_ite, ite_mul,
    mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [Finset.sum_add_distrib, add_mul, pow_two]
  have h1 : ∑ x, coordinate a i x * M (some x) none = ∑ x, M (some x) none * coordinate a i x :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [h1]
  ring

theorem quadEval_sphereMatrix (c' : Fin d → Coeff a) (C : Coeff a) (i : Fin s) :
    quadEval a (sphereMatrix a c' C) i =
      ∑ j, coordinate a i j ^ 2 - 2 * ∑ j, c' j * coordinate a i j + C := by
  rw [quadEval_of_spatial a _ (fun _ _ => rfl)]
  simp only [sphereMatrix, Finset.mul_sum]
  have h : ∀ j, (-c' j + -c' j) * coordinate a i j = -(2 * (c' j * coordinate a i j)) :=
    fun _ => by ring
  simp only [h, Finset.sum_neg_distrib]
  ring

/-- The real distance to a point, in coordinates. -/
theorem dist_sq_eq_sum (x c : Space d) : dist x c ^ 2 = ∑ j, (x j - c j) ^ 2 := by
  simp only [EuclideanSpace.dist_sq_eq, Real.dist_eq, sq_abs]

/-- A real sphere through the points gives an `F`-rational sphere equation through them.
Adapts `sphere_field_quadratic` of openai/math `Quadratic.lean` (Apache-2.0; see `NOTICE`). -/
theorem exists_rational_sphere (hsphere : ∃ c : Space d, ∃ r : ℝ, ∀ i, dist (a i) c = r) :
    ∃ c' : Fin d → Coeff a, ∃ C : Coeff a, ∀ i,
      ∑ j, coordinate a i j ^ 2 - 2 * ∑ j, c' j * coordinate a i j + C = 0 := by
  obtain ⟨c, r, hr⟩ := hsphere
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one (Coeff a) (one_ne_zero : (1 : ℝ) ≠ 0)
  have hmul (x : Coeff a) (t : ℝ) : φ ((x : ℝ) * t) = x * φ t := by
    simpa [Algebra.smul_def] using φ.map_smul x t
  have hfix (x : Coeff a) : φ (x : ℝ) = x := by
    simpa [hφ] using hmul x 1
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = ∑ j, c j ^ 2 - r ^ 2 := ⟨_, rfl⟩
  refine ⟨fun j => φ (c j), φ K, fun i => ?_⟩
  have hreal : ∑ j, a i j ^ 2 - ∑ j, a i j * c j - ∑ j, a i j * c j + K = 0 := by
    have h := dist_sq_eq_sum (a i) c
    rw [hr i] at h
    have hexp : ∑ j, (a i j - c j) ^ 2 =
        ∑ j, a i j ^ 2 - ∑ j, a i j * c j - ∑ j, a i j * c j + ∑ j, c j ^ 2 := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    linarith
  have hdesc := congrArg φ hreal
  simp only [map_add, map_sub, map_sum, map_zero] at hdesc
  have hlin (j : Fin d) : φ (a i j * c j) = coordinate a i j * φ (c j) :=
    hmul (coordinate a i j) _
  have hsq (j : Fin d) : φ (a i j ^ 2) = coordinate a i j ^ 2 := hfix (coordinate a i j ^ 2)
  simp only [hlin, hsq] at hdesc
  have hc : ∑ j, φ (c j) * coordinate a i j = ∑ j, coordinate a i j * φ (c j) :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [hc]
  linear_combination hdesc

/-- An `F`-rational sphere equation through the points, read in `ℝ`, is a real sphere through
them (nonempty configurations fix the radius; the empty one is spherical trivially). -/
theorem spherical_of_rational_sphere (c' : Fin d → Coeff a) (C : Coeff a)
    (hsph : ∀ i, ∑ j, coordinate a i j ^ 2 - 2 * ∑ j, c' j * coordinate a i j + C = 0) :
    ∃ c : Space d, ∃ r : ℝ, ∀ i, dist (a i) c = r := by
  refine ⟨WithLp.toLp 2 (fun j => (c' j : ℝ)), √(∑ j, (c' j : ℝ) ^ 2 - (C : ℝ)), fun i => ?_⟩
  have hR := congrArg (algebraMap (Coeff a) ℝ) (hsph i)
  simp only [map_add, map_sub, map_sum, map_mul, map_pow, map_ofNat, map_zero,
    IntermediateField.algebraMap_apply, coordinate_coe] at hR
  rw [← Real.sqrt_sq dist_nonneg, dist_sq_eq_sum]
  congr 1
  have hexp : ∑ j, (a i j - (c' j : ℝ)) ^ 2 =
      ∑ j, a i j ^ 2 - 2 * ∑ j, (c' j : ℝ) * a i j + ∑ j, (c' j : ℝ) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hexp]
  linarith

/-- The tensor criterion implies sphericity: multiply the certificate. -/
theorem fieldCriterion_spherical_internal (h : FieldCriterion a) :
    ∃ c : Space d, ∃ r : ℝ, ∀ i, dist (a i) c = r := by
  obtain ⟨P, hev, hsp⟩ := fieldCriterion_matrix a h
  let M : Matrix (Option (Fin d)) (Option (Fin d)) (Coeff a) := P.map (μ a)
  have hM : ∀ j k : Fin d, M (some j) (some k) = if j = k then 1 else 0 := hsp
  have hq (i : Fin s) : quadEval a M i = 0 := by
    change ∑ α, ∑ β, augmented a i α * μ a (P α β) * augmented a i β = 0
    have := congrArg (μ a) (hev i)
    simpa only [map_sum, map_mul, μ_ι₁, μ_ι₂, map_zero] using this
  refine spherical_of_rational_sphere a (fun j => -(M none (some j) + M (some j) none) / 2)
    (M none none) fun i => ?_
  have := hq i
  rw [quadEval_of_spatial a M hM] at this
  rw [Finset.mul_sum, ← this]
  have h2 : ∀ j, 2 * (-(M none (some j) + M (some j) none) / 2 * coordinate a i j) =
      -((M none (some j) + M (some j) none) * coordinate a i j) := fun _ => by ring
  simp only [h2, Finset.sum_neg_distrib]
  ring

end

end SixConcyclic

end
