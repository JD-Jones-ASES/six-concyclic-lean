module

public import SixConcyclic.RealCert
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The isometric image of a certified configuration

If `a_i = t + T b_i` for a linear isometry `T : Space d → Space D` and `b` has a real certificate
`P` with multiplied matrix `H` of spatial block `I_d`, then `a` has a real certificate with
spatial block `I_D`. Let `M` be the `D × d` real matrix of `T` (`M k j = T e_j k`, so
`Mᵀ M = I` and `T z = M z`), let `L` be the `(d+1) × (D+1)` affine left inverse
`(1, z) ↦ (1, Mᵀ (z − t))`, so that `L (1, a_i) = (1, b_i)`, and let `w_k = (I − M Mᵀ) e_k`
for `k < D` with the affine functionals `l_k (z) = ⟨w_k, z − t⟩`, which vanish at every `a_i`
because `(I − M Mᵀ) M = 0`. Then
`(L ⊗ 1)ᵀ P (1 ⊗ L) + ∑_k (l_k ⊗ 1)(1 ⊗ l_k)ᵀ` has sandwich `0 + ∑ l_k(a_i) ⊗ l_k(a_i) = 0` at
every `a_i`, and its multiplied matrix is `Lᵀ H L + ∑ l_k l_kᵀ`, whose spatial block is
`M Mᵀ + (I − M Mᵀ)(I − M Mᵀ)ᵀ = M Mᵀ + (I − M Mᵀ) = I`.
-/

@[expose] public section

namespace SixConcyclic

noncomputable section
open Matrix

/-- The sandwich of a matrix over `RT` as a dot product. -/
theorem sandwich_eq_dotProduct {n : Type*} [Fintype n] (P : Matrix n n RT) (x y : n → ℝ) :
    ∑ α, ∑ β, ιl (x α) * P α β * ιr (y β) = (ιl ∘ x) ⬝ᵥ (P *ᵥ (ιr ∘ y)) := by
  simp only [dotProduct, mulVec, Function.comp_apply, Finset.mul_sum, mul_assoc]

/-- A ring homomorphism commutes with `mulVec`, as functions. -/
theorem map_mulVec_comp {m n : Type*} [Fintype n] (f : ℝ →+* RT) (A : Matrix m n ℝ)
    (v : n → ℝ) : A.map f *ᵥ (f ∘ v) = f ∘ (A *ᵥ v) :=
  funext fun i => (f.map_mulVec A v i).symm

/-- Transport of a certificate along a real matrix `L` with `L q_i = p_i`, plus the sum of
squares of the affine functionals (rows of `G`) that vanish at the new points. -/
theorem realCert_transform {ι K : Type*} [Fintype ι] [Fintype K] {d D : ℕ}
    {p : ι → Option (Fin d) → ℝ} {q : ι → Option (Fin D) → ℝ}
    {H : Matrix (Option (Fin d)) (Option (Fin d)) ℝ} (h : RealCert p H)
    (L : Matrix (Option (Fin d)) (Option (Fin D)) ℝ) (hL : ∀ i, L *ᵥ q i = p i)
    (G : Matrix K (Option (Fin D)) ℝ) (hG : ∀ i, G *ᵥ q i = 0) :
    RealCert q (Lᵀ * H * L + Gᵀ * G) := by
  obtain ⟨P, hP, hPH⟩ := h
  refine ⟨(L.map ιl)ᵀ * P * L.map ιr + (G.map ιl)ᵀ * G.map ιr, ?_, ?_⟩
  · intro i
    rw [sandwich_eq_dotProduct, add_mulVec, dotProduct_add, ← mulVec_mulVec, ← mulVec_mulVec,
      ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, dotProduct_mulVec (ιl ∘ q i),
      vecMul_transpose, map_mulVec_comp, map_mulVec_comp, map_mulVec_comp, map_mulVec_comp,
      hL, hG, ← sandwich_eq_dotProduct, hP i, zero_add]
    have h0 : ∀ f : ℝ →+* RT, f ∘ (0 : K → ℝ) = 0 := fun f => funext fun _ => by simp
    rw [h0, zero_dotProduct]
  · have hl : (L.map ιl).map μr = L := by
      rw [Matrix.map_map]; ext; simp [μr_ιl]
    have hr : (L.map ιr).map μr = L := by
      rw [Matrix.map_map]; ext; simp [μr_ιr]
    have gl : (G.map ιl).map μr = G := by
      rw [Matrix.map_map]; ext; simp [μr_ιl]
    have gr : (G.map ιr).map μr = G := by
      rw [Matrix.map_map]; ext; simp [μr_ιr]
    rw [Matrix.map_add _ (map_add μr), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul,
      Matrix.transpose_map, Matrix.transpose_map, hl, hr, gl, gr, hPH]

variable {s d D : ℕ}

/-- The matrix of a linear isometry `Space d → Space D`: `M k j = T e_j k`. -/
def isoMatrix (T : Space d →ₗᵢ[ℝ] Space D) : Matrix (Fin D) (Fin d) ℝ :=
  fun k j => (T (EuclideanSpace.single j 1)).ofLp k

/-- The real inner product in coordinates. -/
theorem inner_eq_sum (x y : Space d) : inner ℝ x y = ∑ k, x.ofLp k * y.ofLp k := by
  simp [PiLp.inner_apply, mul_comm]

/-- The matrix of a linear isometry has orthonormal columns. -/
theorem isoMatrix_transpose_mul (T : Space d →ₗᵢ[ℝ] Space D) :
    (isoMatrix T)ᵀ * isoMatrix T = 1 := by
  ext i j
  have h := T.inner_map_map (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  rw [inner_eq_sum, EuclideanSpace.inner_single_left] at h
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [transpose_apply, isoMatrix]
  rw [h]
  simp

/-- A linear isometry acts by its matrix. -/
theorem isoMatrix_mulVec (T : Space d →ₗᵢ[ℝ] Space D) (z : Space d) :
    (T z).ofLp = isoMatrix T *ᵥ z.ofLp := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr z]
  ext k
  rw [map_sum, WithLp.ofLp_sum, Finset.sum_apply]
  simp only [map_smul, PiLp.smul_apply, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply, smul_eq_mul, mulVec, dotProduct, isoMatrix]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- The affine left inverse `(1, z) ↦ (1, Mᵀ (z − t))`. -/
def leftInv (M : Matrix (Fin D) (Fin d) ℝ) (t : Fin D → ℝ) :
    Matrix (Option (Fin d)) (Option (Fin D)) ℝ :=
  fun γ α =>
  match γ, α with
  | none, none => 1
  | none, some _ => 0
  | some j, none => -(Mᵀ *ᵥ t) j
  | some j, some k => M k j

/-- The orthogonal projection `I − M Mᵀ` onto the complement of the columns of `M`. -/
def perpProj (M : Matrix (Fin D) (Fin d) ℝ) : Matrix (Fin D) (Fin D) ℝ := 1 - M * Mᵀ

/-- The rows `l_k (z) = ⟨(I − M Mᵀ) e_k, z − t⟩`. -/
def perpRows (M : Matrix (Fin D) (Fin d) ℝ) (t : Fin D → ℝ) :
    Matrix (Fin D) (Option (Fin D)) ℝ :=
  fun k α =>
  match α with
  | none => -(perpProj M *ᵥ t) k
  | some j => perpProj M k j

/-- The affine left inverse maps `(1, a_i)` to `(1, b_i)`. -/
theorem leftInv_mulVec (M : Matrix (Fin D) (Fin d) ℝ) (hM : Mᵀ * M = 1) (t : Fin D → ℝ)
    (a : Fin s → Space D) (b : Fin s → Space d)
    (hab : ∀ i, (a i).ofLp = t + M *ᵥ (b i).ofLp) (i : Fin s) :
    leftInv M t *ᵥ aug a i = aug b i := by
  funext γ
  cases γ with
  | none =>
    simp [mulVec, dotProduct, Fintype.sum_option, leftInv, aug]
  | some j =>
    have h1 : (Mᵀ *ᵥ (a i).ofLp) j = (Mᵀ *ᵥ t) j + (b i).ofLp j := by
      rw [hab, mulVec_add, mulVec_mulVec, hM, one_mulVec, Pi.add_apply]
    have h2 : ∑ k, M k j * (a i).ofLp k = (Mᵀ *ᵥ (a i).ofLp) j := rfl
    rw [mulVec, dotProduct, Fintype.sum_option]
    simp only [leftInv, aug]
    rw [h2, h1]
    ring

/-- The perpendicular functionals vanish at every `(1, a_i)`. -/
theorem perpRows_mulVec (M : Matrix (Fin D) (Fin d) ℝ) (hM : Mᵀ * M = 1) (t : Fin D → ℝ)
    (a : Fin s → Space D) (b : Fin s → Space d)
    (hab : ∀ i, (a i).ofLp = t + M *ᵥ (b i).ofLp) (i : Fin s) :
    perpRows M t *ᵥ aug a i = 0 := by
  have hWM : perpProj M * M = 0 := by
    rw [perpProj, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hM, Matrix.mul_one, sub_self]
  funext k
  have h1 : (perpProj M *ᵥ (a i).ofLp) k = (perpProj M *ᵥ t) k := by
    rw [hab, mulVec_add, mulVec_mulVec, hWM, zero_mulVec, add_zero]
  have h2 : ∑ j, perpProj M k j * (a i).ofLp j = (perpProj M *ᵥ (a i).ofLp) k := rfl
  rw [mulVec, dotProduct, Fintype.sum_option]
  simp only [perpRows, aug]
  rw [h2, h1, Pi.zero_apply]
  ring

/-- The spatial block of `Lᵀ H L + Gᵀ G` is `M Mᵀ + (I − M Mᵀ) = I`. -/
theorem transform_spatial (M : Matrix (Fin D) (Fin d) ℝ) (hM : Mᵀ * M = 1) (t : Fin D → ℝ)
    (H : Matrix (Option (Fin d)) (Option (Fin d)) ℝ)
    (hI : ∀ α β : Fin d, H (some α) (some β) = if α = β then 1 else 0) (α β : Fin D) :
    ((leftInv M t)ᵀ * H * leftInv M t + (perpRows M t)ᵀ * perpRows M t) (some α) (some β) =
      if α = β then 1 else 0 := by
  have hW : (perpProj M)ᵀ * perpProj M = perpProj M := by
    rw [perpProj, transpose_sub, transpose_one, transpose_mul, transpose_transpose, Matrix.sub_mul,
      Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_assoc M Mᵀ (M * Mᵀ), ← Matrix.mul_assoc Mᵀ M Mᵀ, hM, Matrix.one_mul]
    abel
  have h1 : ((leftInv M t)ᵀ * H * leftInv M t) (some α) (some β) = (M * Mᵀ) α β := by
    simp only [Matrix.mul_apply, Fintype.sum_option, transpose_apply, leftInv, hI]
    simp [mul_ite, Finset.sum_ite_eq']
  have h2 : ((perpRows M t)ᵀ * perpRows M t) (some α) (some β) = perpProj M α β := by
    rw [← hW]
    simp only [Matrix.mul_apply, transpose_apply, perpRows]
  rw [Matrix.add_apply, h1, h2, perpProj, ← Matrix.add_apply, add_sub_cancel, Matrix.one_apply]

/-- The isometric affine image of a certified configuration is certified. -/
theorem realCert_of_isometric_image {s d D : ℕ} (a : Fin s → Space D) (b : Fin s → Space d)
    (T : Space d →ₗᵢ[ℝ] Space D) (t : Space D) (hab : ∀ i, a i = t + T (b i))
    (H : Matrix (Option (Fin d)) (Option (Fin d)) ℝ) (hb : RealCert (aug b) H)
    (hI : ∀ α β : Fin d, H (some α) (some β) = if α = β then 1 else 0) :
    ∃ H' : Matrix (Option (Fin D)) (Option (Fin D)) ℝ, RealCert (aug a) H' ∧
      ∀ α β : Fin D, H' (some α) (some β) = if α = β then 1 else 0 := by
  have hM : (isoMatrix T)ᵀ * isoMatrix T = 1 := isoMatrix_transpose_mul T
  have hab' : ∀ i, (a i).ofLp = t.ofLp + isoMatrix T *ᵥ (b i).ofLp := by
    intro i
    rw [hab i, WithLp.ofLp_add, isoMatrix_mulVec]
  exact ⟨_, realCert_transform hb (leftInv (isoMatrix T) t.ofLp)
    (leftInv_mulVec _ hM _ a b hab') (perpRows (isoMatrix T) t.ofLp)
    (perpRows_mulVec _ hM _ a b hab'), transform_spatial _ hM _ H hI⟩

end

end SixConcyclic

end
