module

public import SixConcyclic.Lift

/-!
# Certificates over `ℝ ⊗_ℚ ℝ`

The tensor criterion is stated over `F ⊗_ℚ F`, `F` the coordinate field. Every construction of
this development that moves points (an isometric change of ambient space, the addition of a point
outside the span, the symmetrisation of a certificate) is easier over the real tensor ring
`ℝ ⊗_ℚ ℝ`, where every real number is available; a certificate over `ℝ ⊗_ℚ ℝ` descends to
`F ⊗_ℚ F` (`Descent.lean`). `RealCert p H` says that the points `p` (augmented real vectors
`(1, a_i)`) have a certificate over `ℝ ⊗_ℚ ℝ` whose multiplied matrix is exactly `H`.
-/

@[expose] public section

namespace SixConcyclic

noncomputable section
open scoped TensorProduct
open Matrix

/-- The real tensor ring `ℝ ⊗_ℚ ℝ`. -/
abbrev RT := ℝ ⊗[ℚ] ℝ

/-- The left inclusion `x ↦ x ⊗ 1`. -/
def ιl : ℝ →+* RT := Algebra.TensorProduct.includeLeftRingHom

/-- The right inclusion `y ↦ 1 ⊗ y`. -/
def ιr : ℝ →+* RT := (Algebra.TensorProduct.includeRight : ℝ →ₐ[ℚ] RT).toRingHom

/-- The multiplication `x ⊗ y ↦ xy`. -/
def μr : RT →+* ℝ := (Algebra.TensorProduct.lmul' ℚ : RT →ₐ[ℚ] ℝ).toRingHom

theorem ιl_apply (x : ℝ) : ιl x = x ⊗ₜ[ℚ] (1 : ℝ) := rfl

theorem ιr_apply (y : ℝ) : ιr y = (1 : ℝ) ⊗ₜ[ℚ] y := rfl

theorem μr_tmul (x y : ℝ) : μr (x ⊗ₜ[ℚ] y) = x * y := Algebra.TensorProduct.lmul'_apply_tmul x y

theorem μr_ιl (x : ℝ) : μr (ιl x) = x := by rw [ιl_apply, μr_tmul, mul_one]

theorem μr_ιr (y : ℝ) : μr (ιr y) = y := by rw [ιr_apply, μr_tmul, one_mul]

theorem ιl_mul_ιr (x y : ℝ) : ιl x * ιr y = x ⊗ₜ[ℚ] y := by
  rw [ιl_apply, ιr_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The augmented real coordinates `(1, a_i)` of a configuration. -/
def aug {s d : ℕ} (a : Fin s → Space d) (i : Fin s) : Option (Fin d) → ℝ
  | none => 1
  | some j => a i j

theorem aug_none {s d : ℕ} (a : Fin s → Space d) (i : Fin s) : aug a i none = 1 := rfl

theorem aug_some {s d : ℕ} (a : Fin s → Space d) (i : Fin s) (j : Fin d) :
    aug a i (some j) = a i j := rfl

/-- The real augmented vector is the coercion of the one over the coordinate field. -/
theorem aug_eq_coe {s d : ℕ} (a : Fin s → Space d) (i : Fin s) (α : Option (Fin d)) :
    aug a i α = (augmented a i α : ℝ) := by
  cases α <;> rfl

/-- The quadratic evaluation `pᵀ H p` of a real matrix at a real augmented vector. -/
def qeval {d : ℕ} (H : Matrix (Option (Fin d)) (Option (Fin d)) ℝ) (p : Option (Fin d) → ℝ) :
    ℝ :=
  ∑ α, ∑ β, p α * H α β * p β

/-- A certificate over `ℝ ⊗_ℚ ℝ` for the points `p`, with multiplied matrix exactly `H`. -/
def RealCert {ι : Type*} [Fintype ι] {d : ℕ} (p : ι → Option (Fin d) → ℝ)
    (H : Matrix (Option (Fin d)) (Option (Fin d)) ℝ) : Prop :=
  ∃ P : Matrix (Option (Fin d)) (Option (Fin d)) RT,
    (∀ i, ∑ α, ∑ β, ιl (p i α) * P α β * ιr (p i β) = 0) ∧ P.map μr = H

/-- The real sphere matrix of `|x|² − 2⟨c, x⟩ + (|c|² − r²)`: spatial block `I`. -/
def realSphere {d : ℕ} (c : Space d) (r : ℝ) : Matrix (Option (Fin d)) (Option (Fin d)) ℝ :=
  fun α β =>
  match α, β with
  | none, none => ∑ j, c j ^ 2 - r ^ 2
  | none, some k => -(c k)
  | some k, none => -(c k)
  | some j, some k => if j = k then 1 else 0

theorem realSphere_spatial {d : ℕ} (c : Space d) (r : ℝ) (α β : Fin d) :
    realSphere c r (some α) (some β) = if α = β then 1 else 0 := rfl

/-- The push-forward `F ⊗_ℚ F → ℝ ⊗_ℚ ℝ` along the inclusion of the coordinate field. -/
def pushRT {s d : ℕ} (a : Fin s → Space d) : TensorRing a →ₐ[ℚ] RT :=
  Algebra.TensorProduct.map (IntermediateField.val _) (IntermediateField.val _)

theorem pushRT_tmul {s d : ℕ} (a : Fin s → Space d) (x y : Coeff a) :
    pushRT a (x ⊗ₜ[ℚ] y) = (x : ℝ) ⊗ₜ[ℚ] (y : ℝ) :=
  Algebra.TensorProduct.map_tmul _ _ x y

/-- The push-forward commutes with multiplication. -/
theorem μr_pushRT {s d : ℕ} (a : Fin s → Space d) (z : TensorRing a) :
    μr (pushRT a z) = ((multiply a z : Coeff a) : ℝ) := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    rw [pushRT_tmul, μr_tmul, multiply, Algebra.TensorProduct.lmul'_apply_tmul,
      IntermediateField.coe_mul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, IntermediateField.coe_add]

/-- The swap `x ⊗ y ↦ y ⊗ x` of `ℝ ⊗_ℚ ℝ`. -/
def swapRT : RT →ₐ[ℚ] RT := (Algebra.TensorProduct.comm ℚ ℝ ℝ).toAlgHom

theorem swapRT_ιl (x : ℝ) : swapRT (ιl x) = ιr x := by
  rw [ιl_apply, ιr_apply]
  exact Algebra.TensorProduct.comm_tmul ℚ x (1 : ℝ)

theorem swapRT_ιr (x : ℝ) : swapRT (ιr x) = ιl x := by
  rw [ιl_apply, ιr_apply]
  exact Algebra.TensorProduct.comm_tmul ℚ (1 : ℝ) x

/-- The swap does not change the product. -/
theorem μr_swapRT (z : RT) : μr (swapRT z) = μr z := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    rw [show swapRT (x ⊗ₜ[ℚ] y) = y ⊗ₜ[ℚ] x from Algebra.TensorProduct.comm_tmul ℚ x y,
      μr_tmul, μr_tmul, mul_comm]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

/-- The linear form `(N₀₀/2, N₀ₖ)` of a symmetric correction. -/
def corrL {d : ℕ} (N : Matrix (Option (Fin d)) (Option (Fin d)) ℝ) : Option (Fin d) → ℝ
  | none => N none none / 2
  | some k => N none (some k)

/-- The coordinate vector `(1, 0)`. -/
def unitE {d : ℕ} : Option (Fin d) → ℝ
  | none => 1
  | some _ => 0

/-- The real sphere matrix is symmetric. -/
theorem realSphere_transpose {d : ℕ} (c : Space d) (r : ℝ) :
    (realSphere c r)ᵀ = realSphere c r := by
  ext α β
  rcases α with _ | j <;> rcases β with _ | k <;> simp only [transpose_apply, realSphere]
  exact if_congr eq_comm rfl rfl

/-- The quadratic evaluation of the real sphere matrix at a point is `dist² − r²`. -/
theorem qeval_realSphere {s d : ℕ} (a : Fin s → Space d) (c : Space d) (r : ℝ) (i : Fin s) :
    qeval (realSphere c r) (aug a i) = dist (a i) c ^ 2 - r ^ 2 := by
  rw [dist_sq_eq_sum]
  simp only [qeval, Fintype.sum_option, aug_none, aug_some, realSphere, mul_ite, ite_mul,
    mul_one, mul_zero, zero_mul, one_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have e : ∀ j, (a i j - c j) ^ 2 = a i j * a i j + (-c j * a i j + a i j * -c j) + c j ^ 2 :=
    fun j => by ring
  simp only [e, Finset.sum_add_distrib]
  ring

/-- The multiplied matrix of a certificate vanishes at every point (apply `μr` to the sandwich). -/
theorem realCert_qeval {ι : Type*} [Fintype ι] {d : ℕ} {p : ι → Option (Fin d) → ℝ}
    {H : Matrix (Option (Fin d)) (Option (Fin d)) ℝ} (h : RealCert p H) (i : ι) :
    qeval H (p i) = 0 := by
  obtain ⟨P, hev, rfl⟩ := h
  have h1 := congrArg μr (hev i)
  simp only [map_sum, map_mul, μr_ιl, μr_ιr, map_zero] at h1
  simpa only [qeval, Matrix.map_apply] using h1

/-- Reindexing the points along an equivalence. -/
theorem realCert_reindex {ι κ : Type*} [Fintype ι] [Fintype κ] {d : ℕ}
    {p : ι → Option (Fin d) → ℝ} {H : Matrix (Option (Fin d)) (Option (Fin d)) ℝ}
    (e : κ ≃ ι) (h : RealCert p H) : RealCert (p ∘ e) H := by
  obtain ⟨P, hev, hmap⟩ := h
  exact ⟨P, fun k => hev (e k), hmap⟩

/-- A certificate over the coordinate field pushes forward to `ℝ ⊗_ℚ ℝ` along
`Algebra.TensorProduct.map` of the inclusion `F → ℝ`; its multiplied matrix is the coercion of
`μ P`, with spatial block `I`. -/
theorem realCert_of_fieldCriterion {s d : ℕ} (a : Fin s → Space d) (h : FieldCriterion a) :
    ∃ H : Matrix (Option (Fin d)) (Option (Fin d)) ℝ, RealCert (aug a) H ∧
      ∀ α β : Fin d, H (some α) (some β) = if α = β then 1 else 0 := by
  obtain ⟨P, hev, hsp⟩ := h
  have hφμ : ∀ z : TensorRing a, μr (pushRT a z) = ((multiply a z : Coeff a) : ℝ) :=
    μr_pushRT a
  refine ⟨(P.map (pushRT a)).map μr, ⟨P.map (pushRT a), ?_, rfl⟩, ?_⟩
  · intro i
    have h1 := congrArg (pushRT a) (hev i)
    simp only [map_sum, map_mul, map_zero] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    rw [pushRT_tmul, pushRT_tmul, Matrix.map_apply, ιl_apply, ιr_apply, aug_eq_coe, aug_eq_coe,
      IntermediateField.coe_one]
  · intro α β
    simp only [Matrix.map_apply, hφμ, hsp]
    split_ifs <;> simp

/-- Symmetrisation: the transposed certificate with the two tensor factors swapped
(`Algebra.TensorProduct.comm`) is again a certificate, with multiplied matrix `Hᵀ`; the average
of the two has the symmetric multiplied matrix `(H + Hᵀ)/2`. -/
theorem realCert_symm {ι : Type*} [Fintype ι] {d : ℕ} {p : ι → Option (Fin d) → ℝ}
    {H : Matrix (Option (Fin d)) (Option (Fin d)) ℝ} (h : RealCert p H) :
    RealCert p ((2 : ℝ)⁻¹ • (H + Hᵀ)) := by
  obtain ⟨P, hev, rfl⟩ := h
  let P2 : Matrix (Option (Fin d)) (Option (Fin d)) RT := fun α β => swapRT (P β α)
  have hev2 : ∀ i, ∑ α, ∑ β, ιl (p i α) * P2 α β * ιr (p i β) = 0 := by
    intro i
    have h1 := congrArg swapRT (hev i)
    simp only [map_sum, map_mul, map_zero, swapRT_ιl, swapRT_ιr] at h1
    rw [Finset.sum_comm] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    simp only [P2]
    ring
  refine ⟨fun α β => ιl 2⁻¹ * (P α β + P2 α β), fun i => ?_, ?_⟩
  · have e : ∑ α, ∑ β, ιl (p i α) * (ιl 2⁻¹ * (P α β + P2 α β)) * ιr (p i β) =
        ιl 2⁻¹ * ((∑ α, ∑ β, ιl (p i α) * P α β * ιr (p i β)) +
          ∑ α, ∑ β, ιl (p i α) * P2 α β * ιr (p i β)) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun β _ => ?_
      ring
    rw [e, hev i, hev2 i, add_zero, mul_zero]
  · ext α β
    change μr (ιl 2⁻¹ * (P α β + swapRT (P β α))) = (2 : ℝ)⁻¹ * (μr (P α β) + μr (P β α))
    rw [map_mul, map_add, μr_ιl, μr_swapRT]

/-- A symmetric matrix `N` with zero spatial block that vanishes at every point can be added to
the multiplied matrix: with `l = (N₀₀/2, N₀ₖ)` and `e₀ = (1, 0)`, the matrix
`(l ⊗ 1)(1 ⊗ e₀)ᵀ + (e₀ ⊗ 1)(1 ⊗ l)ᵀ` has sandwiches `ℓ(p_i) ⊗ 1 + 1 ⊗ ℓ(p_i) = 0` and
multiplies to `N`. -/
theorem realCert_add_symm {ι : Type*} [Fintype ι] {d : ℕ} {p : ι → Option (Fin d) → ℝ}
    {H : Matrix (Option (Fin d)) (Option (Fin d)) ℝ} (h : RealCert p H)
    (N : Matrix (Option (Fin d)) (Option (Fin d)) ℝ) (hN : Nᵀ = N)
    (hsp : ∀ α β : Fin d, N (some α) (some β) = 0) (hv : ∀ i, qeval N (p i) = 0) :
    RealCert p (H + N) := by
  obtain ⟨P, hev, rfl⟩ := h
  have hsym : ∀ j, N (some j) none = N none (some j) := fun j => by
    have := congrFun (congrFun hN (some j)) none
    rw [transpose_apply] at this
    exact this.symm
  let C : Matrix (Option (Fin d)) (Option (Fin d)) RT := fun α β =>
    ιl (corrL N α) * ιr (unitE β) + ιl (unitE α) * ιr (corrL N β)
  refine ⟨P + C, fun i => ?_, ?_⟩
  · set L := ∑ α, corrL N α * p i α with hL
    have hE : ∑ β, unitE β * p i β = p i none := by
      simp [Fintype.sum_option, unitE]
    have hq : p i none * L = 0 := by
      have e : qeval N (p i) = 2 * (p i none * L) := by
        have e2 : ∑ j, p i (some j) * N (some j) none * p i none =
            p i none * ∑ j, N none (some j) * p i (some j) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hsym]
          ring
        have e3 : ∑ j, p i none * N none (some j) * p i (some j) =
            p i none * ∑ j, N none (some j) * p i (some j) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
        simp only [qeval, Fintype.sum_option, hsp, mul_zero, zero_mul, Finset.sum_const_zero,
          add_zero, e2, e3, hL, corrL]
        ring
      have := hv i
      rw [e] at this
      linarith
    have key : ∑ α, ∑ β, ιl (p i α) * C α β * ιr (p i β) =
        ιl L * ιr (∑ β, unitE β * p i β) + ιl (∑ β, unitE β * p i β) * ιr L := by
      rw [hL]
      simp only [map_sum]
      rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun β _ => ?_
      simp only [C, map_mul]
      ring
    have hsplit : ∑ α, ∑ β, ιl (p i α) * (P + C) α β * ιr (p i β) =
        (∑ α, ∑ β, ιl (p i α) * P α β * ιr (p i β)) +
          ∑ α, ∑ β, ιl (p i α) * C α β * ιr (p i β) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun β _ => ?_
      rw [Matrix.add_apply]
      ring
    rw [hsplit, hev i, key, hE, zero_add]
    rcases mul_eq_zero.mp hq with h0 | h0
    · rw [h0, map_zero, map_zero, mul_zero, zero_mul, add_zero]
    · rw [h0, map_zero, map_zero, mul_zero, zero_mul, add_zero]
  · ext α β
    change μr (P α β + C α β) = μr (P α β) + N α β
    rw [map_add]
    congr 1
    change μr (ιl (corrL N α) * ιr (unitE β) + ιl (unitE α) * ιr (corrL N β)) = N α β
    simp only [map_add, map_mul, μr_ιl, μr_ιr]
    rcases α with _ | j <;> rcases β with _ | k <;> simp [corrL, unitE, hsym, hsp]

/-- The adjugate lift over `ℝ ⊗_ℚ ℝ` (`lift_of_rightInverse` with `ιl`, `ιr`, `μr`): real
isolating quadrics lift any real matrix vanishing at the points, with multiplied matrix exactly
that matrix. -/
theorem realCert_of_isolators {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (p : ι → Option (Fin d) → ℝ) (H : Matrix (Option (Fin d)) (Option (Fin d)) ℝ)
    (hH : ∀ i, qeval H (p i) = 0) (q : ι → Matrix (Option (Fin d)) (Option (Fin d)) ℝ)
    (hq : ∀ i j, qeval (q i) (p j) = if i = j then 1 else 0) : RealCert p H := by
  let D : Matrix ι (Option (Fin d) × Option (Fin d)) RT :=
    fun i αβ => ιl (p i αβ.1) * ιr (p i αβ.2)
  let S : Matrix (Option (Fin d) × Option (Fin d)) ι RT := fun αβ j => ιl (q j αβ.1 αβ.2)
  let b : Option (Fin d) × Option (Fin d) → RT := fun αβ => ιl (H αβ.1 αβ.2)
  have hDmap : ∀ i αβ, D.map μr i αβ = p i αβ.1 * p i αβ.2 := by
    intro i αβ
    change μr (ιl _ * ιr _) = _
    rw [map_mul, μr_ιl, μr_ιr]
  have hN : (D * S).map μr = 1 := by
    refine Matrix.ext fun i j => ?_
    have e : (1 : Matrix ι ι ℝ) i j = qeval (q j) (p i) := by
      rw [hq j i, Matrix.one_apply]
      by_cases h : i = j
      · subst h
        simp
      · simp [h, Ne.symm h]
    rw [e, Matrix.map_apply, Matrix.mul_apply, map_sum, qeval, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    simp only [D, S, map_mul, μr_ιl, μr_ιr]
    ring
  obtain ⟨z, hz, hzμ⟩ := lift_of_rightInverse μr D S hN b (by
    funext i
    rw [Pi.zero_apply, Matrix.mulVec, dotProduct, ← hH i, qeval, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    rw [hDmap, Function.comp_apply]
    simp only [b, μr_ιl]
    ring)
  refine ⟨fun α β => z (α, β), fun i => ?_, ?_⟩
  · have ht := congrFun hz i
    rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Pi.zero_apply] at ht
    rw [← ht]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    simp only [D]
    ring
  · ext α β
    change μr (z (α, β)) = H α β
    rw [hzμ (α, β)]
    exact μr_ιl _

end

end SixConcyclic

end
