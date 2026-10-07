module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.RingTheory.TensorProduct.Maps
public import SixConcyclic.Core
public import SixConcyclic.Param
public import SixConcyclic.Ordered

/-!
# Six concyclic points: the certificate

In an abstract commutative ring `B` with ring homomorphisms `ι₁ ι₂ : F → B` split by
`μ : B → F`, the matrix `P = ι₁ s • (W.map ι₁)ᵀ Q (W.map ι₂)` has the evaluation identity
`eval_P` and the multiplied image `mult_P`. With `W` the inverse of the circle parametrization
of `Param` and `Q` the product of the two (1,1)-forms of `Core` through the triples
`{0,1,2}` and `{3,4,5}`, every evaluation vanishes (one factor is zero) and the multiplied
matrix is the circle matrix (`six_abstract`). Instantiated at `F = Coeff a`, `B = F ⊗[ℚ] F`
this is `six_concyclic_fieldCriterion_internal`.
-/

@[expose] public section

noncomputable section

namespace SixConcyclic.Asm

open Matrix

variable {F B : Type*} [Field F] [CommRing B]

def Pmat (ι₁ ι₂ : F →+* B) (s : F) (W : Matrix (Fin 3) (Option (Fin 2)) F)
    (Q : Matrix (Fin 3) (Fin 3) B) : Matrix (Option (Fin 2)) (Option (Fin 2)) B :=
  ι₁ s • ((W.map ι₁)ᵀ * Q * W.map ι₂)

theorem eval_P (ι₁ ι₂ : F →+* B) (s : F) (W : Matrix (Fin 3) (Option (Fin 2)) F)
    (Q : Matrix (Fin 3) (Fin 3) B) (ξ η : Option (Fin 2) → F) :
    ∑ α, ∑ β, ι₁ (ξ α) * Pmat ι₁ ι₂ s W Q α β * ι₂ (η β) =
      ι₁ s * ∑ γ, ∑ δ, ι₁ ((W *ᵥ ξ) γ) * Q γ δ * ι₂ ((W *ᵥ η) δ) := by
  simp only [Pmat, Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.mulVec, dotProduct, map_add, map_mul, smul_eq_mul, Fintype.sum_option, Fin.sum_univ_two,
    Fin.sum_univ_three]
  ring

theorem mult_P (ι₁ ι₂ : F →+* B) (μ : B →+* F) (h₁ : ∀ x, μ (ι₁ x) = x) (h₂ : ∀ x, μ (ι₂ x) = x)
    (s : F) (W : Matrix (Fin 3) (Option (Fin 2)) F) (Q : Matrix (Fin 3) (Fin 3) B) :
    (Pmat ι₁ ι₂ s W Q).map μ = s • (Wᵀ * Q.map μ * W) := by
  ext α β
  simp only [Pmat, Matrix.map_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply,
    smul_eq_mul, map_mul, map_sum, h₁, h₂]


/-! ### The certificate in an abstract field

Six points `q_i = (q0 i, q1 i)` of the circle `|x|² − 2⟨c, x⟩ + C = 0` over a field `F`, base
point `q_5`, directions `x_i = q_i − q_5` (`i < 5`) and the tangent `x_5 = (−e₁, e₀)`,
`e = q_5 − c`. -/

section Six

/-- First coordinate of the direction attached to point `i`. -/
def dir0 (q0 q1 : Fin 6 → F) (c1 : F) (i : Fin 6) : F :=
  if i = 5 then -(q1 5 - c1) else q0 i - q0 5

/-- Second coordinate of the direction attached to point `i`. -/
def dir1 (q0 q1 : Fin 6 → F) (c0 : F) (i : Fin 6) : F :=
  if i = 5 then q0 5 - c0 else q1 i - q1 5

/-- Squared length of the direction attached to point `i`. -/
def nrm (q0 q1 : Fin 6 → F) (c0 c1 : F) (i : Fin 6) : F :=
  if i = 5 then (q0 5 - c0) ^ 2 + (q1 5 - c1) ^ 2 else (q0 i - q0 5) ^ 2 + (q1 i - q1 5) ^ 2

/-- The product of the three brackets of a triple of directions. -/
def Vdm (U W : Fin 3 → F) : F :=
  (U 0 * W 1 - U 1 * W 0) * (U 0 * W 2 - U 2 * W 0) * (U 1 * W 2 - U 2 * W 1)

/-- The biquadratic matrix of the product of the (1,1)-forms through two triples. -/
def Qsix (U W U' W' U₂ W₂ U₂' W₂' : Fin 3 → B) : Matrix (Fin 3) (Fin 3) B :=
  Core.Qm (Core.c00 U W U' W') (Core.c01 U W U' W') (Core.c10 U W U' W') (Core.c11 U W U' W')
    (Core.c00 U₂ W₂ U₂' W₂') (Core.c01 U₂ W₂ U₂' W₂') (Core.c10 U₂ W₂ U₂' W₂')
    (Core.c11 U₂ W₂ U₂' W₂')

theorem map_ver (f : F →+* B) (u w : F) (γ : Fin 3) :
    f (Param.ver u w γ) = Core.ver (f u) (f w) γ := by
  fin_cases γ <;> simp [Param.ver, Core.ver]

theorem sandwich_scale (x y : B) (v w : Fin 3 → B) (Q : Matrix (Fin 3) (Fin 3) B) :
    ∑ γ, ∑ δ, x * v γ * Q γ δ * (y * w δ) = x * y * ∑ γ, ∑ δ, v γ * Q γ δ * w δ := by
  simp only [Fin.sum_univ_three]
  ring

/-- The evaluation of the certificate at a point whose direction belongs to one of the two
triples vanishes. -/
theorem eval_six (ι₁ ι₂ : F →+* B) (s : F) (Wm : Matrix (Fin 3) (Option (Fin 2)) F)
    (U W U₂ W₂ : Fin 3 → F) (ξ : Option (Fin 2) → F) (n u w : F)
    (hξ : Wm *ᵥ ξ = n • Param.ver u w)
    (h : (∃ j, U j = u ∧ W j = w) ∨ (∃ j, U₂ j = u ∧ W₂ j = w)) :
    ∑ α, ∑ β, ι₁ (ξ α) * Pmat ι₁ ι₂ s Wm
      (Qsix (ι₁ ∘ U) (ι₁ ∘ W) (ι₂ ∘ U) (ι₂ ∘ W) (ι₁ ∘ U₂) (ι₁ ∘ W₂) (ι₂ ∘ U₂) (ι₂ ∘ W₂)) α β *
      ι₂ (ξ β) = 0 := by
  rw [eval_P, hξ]
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_ver]
  rw [sandwich_scale]
  unfold Qsix
  rw [Core.Qm_form]
  rcases h with ⟨j, rfl, rfl⟩ | ⟨j, rfl, rfl⟩
  · have h0 := Core.ell_vanishes (ι₁ ∘ U) (ι₁ ∘ W) (ι₂ ∘ U) (ι₂ ∘ W) j
    simp only [Core.ell, Function.comp_apply] at h0
    rw [h0]
    ring
  · have h0 := Core.ell_vanishes (ι₁ ∘ U₂) (ι₁ ∘ W₂) (ι₂ ∘ U₂) (ι₂ ∘ W₂) j
    simp only [Core.ell, Function.comp_apply] at h0
    rw [h0]
    ring

/-- Multiplying out: the corner coefficients die and the matrix becomes `V₁ V₂ • K`. -/
theorem Qsix_map (ι₁ ι₂ : F →+* B) (μ : B →+* F) (h₁ : ∀ x, μ (ι₁ x) = x)
    (h₂ : ∀ x, μ (ι₂ x) = x) (U W U₂ W₂ : Fin 3 → F) :
    (Qsix (ι₁ ∘ U) (ι₁ ∘ W) (ι₂ ∘ U) (ι₂ ∘ W) (ι₁ ∘ U₂) (ι₁ ∘ W₂) (ι₂ ∘ U₂) (ι₂ ∘ W₂)).map μ =
      (Vdm U W * Vdm U₂ W₂) • (Param.K : Matrix (Fin 3) (Fin 3) F) := by
  have hc : ∀ U W : Fin 3 → F,
      μ (Core.c00 (ι₁ ∘ U) (ι₁ ∘ W) (ι₂ ∘ U) (ι₂ ∘ W)) = 0 ∧
      μ (Core.c11 (ι₁ ∘ U) (ι₁ ∘ W) (ι₂ ∘ U) (ι₂ ∘ W)) = 0 ∧
      μ (Core.c10 (ι₁ ∘ U) (ι₁ ∘ W) (ι₂ ∘ U) (ι₂ ∘ W)) = Vdm U W ∧
      μ (Core.c01 (ι₁ ∘ U) (ι₁ ∘ W) (ι₂ ∘ U) (ι₂ ∘ W)) = -Vdm U W := by
    intro U W
    obtain ⟨h00, h11, h10, h01⟩ := Core.mult_coeffs U W
    have m00 : μ (Core.c00 (ι₁ ∘ U) (ι₁ ∘ W) (ι₂ ∘ U) (ι₂ ∘ W)) = Core.c00 U W U W := by
      simp only [Core.c00, Core.det3, map_sub, map_mul, map_add, Function.comp_apply, h₁, h₂]
    have m11 : μ (Core.c11 (ι₁ ∘ U) (ι₁ ∘ W) (ι₂ ∘ U) (ι₂ ∘ W)) = Core.c11 U W U W := by
      simp only [Core.c11, Core.det3, map_neg, map_sub, map_mul, map_add, Function.comp_apply,
        h₁, h₂]
    have m10 : μ (Core.c10 (ι₁ ∘ U) (ι₁ ∘ W) (ι₂ ∘ U) (ι₂ ∘ W)) = Core.c10 U W U W := by
      simp only [Core.c10, Core.det3, map_sub, map_mul, map_add, Function.comp_apply, h₁, h₂]
    have m01 : μ (Core.c01 (ι₁ ∘ U) (ι₁ ∘ W) (ι₂ ∘ U) (ι₂ ∘ W)) = Core.c01 U W U W := by
      simp only [Core.c01, Core.det3, map_neg, map_sub, map_mul, map_add, Function.comp_apply,
        h₁, h₂]
    exact ⟨m00.trans h00, m11.trans h11, m10.trans h10, m01.trans h01⟩
  obtain ⟨a00, a11, a10, a01⟩ := hc U W
  obtain ⟨b00, b11, b10, b01⟩ := hc U₂ W₂
  ext γ δ
  fin_cases γ <;> fin_cases δ <;>
    simp [Qsix, Core.Qm, Param.K, Matrix.map_apply, a00, a11, a10, a01, b00, b11, b10, b01]
  ring

theorem dir0_five (q0 q1 : Fin 6 → F) (c1 : F) : dir0 q0 q1 c1 5 = -(q1 5 - c1) := by
  simp [dir0]

theorem dir1_five (q0 q1 : Fin 6 → F) (c0 : F) : dir1 q0 q1 c0 5 = q0 5 - c0 := by
  simp [dir1]

theorem dir0_ne (q0 q1 : Fin 6 → F) (c1 : F) {i : Fin 6} (hi : i ≠ 5) :
    dir0 q0 q1 c1 i = q0 i - q0 5 := by
  simp [dir0, hi]

theorem dir1_ne (q0 q1 : Fin 6 → F) (c0 : F) {i : Fin 6} (hi : i ≠ 5) :
    dir1 q0 q1 c0 i = q1 i - q1 5 := by
  simp [dir1, hi]

/-- The six-point certificate over an abstract field of characteristic zero, given ring
homomorphisms `ι₁ ι₂ : F → B` split by `μ : B → F`. The hypotheses are the circle equation and
the nonvanishing of the chords from `q_5`, of `|q_5 − c|²`, of the brackets of two chords from
`q_5`, and of the products of a chord from `q_5` with the radius at `q_5`. -/
theorem six_abstract [CharZero F] (ι₁ ι₂ : F →+* B) (μ : B →+* F) (h₁ : ∀ x, μ (ι₁ x) = x)
    (h₂ : ∀ x, μ (ι₂ x) = x) (q0 q1 : Fin 6 → F) (c0 c1 C : F)
    (hsph : ∀ i, q0 i ^ 2 + q1 i ^ 2 - 2 * (c0 * q0 i + c1 * q1 i) + C = 0)
    (hN : ∀ j : Fin 6, j ≠ 5 → (q0 j - q0 5) ^ 2 + (q1 j - q1 5) ^ 2 ≠ 0)
    (he : (q0 5 - c0) ^ 2 + (q1 5 - c1) ^ 2 ≠ 0)
    (hdet : ∀ j k : Fin 6, j ≠ 5 → k ≠ 5 → j ≠ k →
      (q0 j - q0 5) * (q1 k - q1 5) - (q1 j - q1 5) * (q0 k - q0 5) ≠ 0)
    (hdot : ∀ j : Fin 6, j ≠ 5 → (q0 j - q0 5) * (q0 5 - c0) + (q1 j - q1 5) * (q1 5 - c1) ≠ 0) :
    ∃ P : Matrix (Option (Fin 2)) (Option (Fin 2)) B,
      (∀ i, ∑ α, ∑ β, ι₁ (Param.aug (q0 i) (q1 i) α) * P α β * ι₂ (Param.aug (q0 i) (q1 i) β)
        = 0) ∧
      (∀ α β : Fin 2, μ (P (some α) (some β)) = if α = β then 1 else 0) := by
  set X0 := dir0 q0 q1 c1 with hX0
  set X1 := dir1 q0 q1 c0 with hX1
  set N := nrm q0 q1 c0 c1 with hNdef
  set Λ := Param.Lam (q0 5) (q1 5) c0 c1 with hΛdef
  set Wm := Param.Winv (q0 5) (q1 5) c0 c1 with hWdef
  have hNz : ∀ i, N i ≠ 0 := by
    intro i
    by_cases hi : i = 5
    · simp only [hNdef, nrm, hi, ite_true]; exact he
    · simp only [hNdef, nrm, hi, ite_false]; exact hN i hi
  have hΛ : ∀ i, Λ *ᵥ Param.ver (X0 i) (X1 i) = N i • Param.aug (q0 i) (q1 i) := by
    intro i
    funext α
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    by_cases hi : i = 5
    · subst hi
      simp only [hX0, hX1, hNdef, hΛdef, dir0, dir1, nrm, ite_true]
      exact Param.Lam_tangent (q0 5) (q1 5) c0 c1 α
    · simp only [hX0, hX1, hNdef, hΛdef, dir0, dir1, nrm, hi, ite_false]
      exact Param.Lam_ver (q0 5) (q1 5) c0 c1 (q0 i) (q1 i)
        (by linear_combination hsph i - hsph 5) α
  have hW : ∀ i, Wm *ᵥ Param.aug (q0 i) (q1 i) = (N i)⁻¹ • Param.ver (X0 i) (X1 i) := by
    intro i
    have h1 : Wm * Λ = 1 := Param.Winv_mul_Lam _ _ _ _ he
    have hv : Wm *ᵥ (Λ *ᵥ Param.ver (X0 i) (X1 i)) = Param.ver (X0 i) (X1 i) := by
      rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
    rw [hΛ i, Matrix.mulVec_smul] at hv
    rw [← hv, smul_smul, inv_mul_cancel₀ (hNz i), one_smul]
  set U₁ : Fin 3 → F := ![X0 0, X0 1, X0 2] with hU₁
  set W₁ : Fin 3 → F := ![X1 0, X1 1, X1 2] with hW₁
  set U₂ : Fin 3 → F := ![X0 3, X0 4, X0 5] with hU₂
  set W₂ : Fin 3 → F := ![X1 3, X1 4, X1 5] with hW₂
  have h05 : (0 : Fin 6) ≠ 5 := by decide
  have h15 : (1 : Fin 6) ≠ 5 := by decide
  have h25 : (2 : Fin 6) ≠ 5 := by decide
  have h35 : (3 : Fin 6) ≠ 5 := by decide
  have h45 : (4 : Fin 6) ≠ 5 := by decide
  have hV₁ : Vdm U₁ W₁ ≠ 0 := by
    have hx : Vdm U₁ W₁ =
        ((q0 0 - q0 5) * (q1 1 - q1 5) - (q1 0 - q1 5) * (q0 1 - q0 5)) *
        ((q0 0 - q0 5) * (q1 2 - q1 5) - (q1 0 - q1 5) * (q0 2 - q0 5)) *
        ((q0 1 - q0 5) * (q1 2 - q1 5) - (q1 1 - q1 5) * (q0 2 - q0 5)) := by
      simp only [Vdm, hU₁, hW₁, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, hX0, hX1, dir0_ne q0 q1 c1 h05,
        dir0_ne q0 q1 c1 h15, dir0_ne q0 q1 c1 h25, dir1_ne q0 q1 c0 h05,
        dir1_ne q0 q1 c0 h15, dir1_ne q0 q1 c0 h25]
      ring
    rw [hx]
    exact mul_ne_zero (mul_ne_zero (hdet 0 1 h05 h15 (by decide)) (hdet 0 2 h05 h25 (by decide)))
      (hdet 1 2 h15 h25 (by decide))
  have hV₂ : Vdm U₂ W₂ ≠ 0 := by
    have hx : Vdm U₂ W₂ =
        ((q0 3 - q0 5) * (q1 4 - q1 5) - (q1 3 - q1 5) * (q0 4 - q0 5)) *
        ((q0 3 - q0 5) * (q0 5 - c0) + (q1 3 - q1 5) * (q1 5 - c1)) *
        ((q0 4 - q0 5) * (q0 5 - c0) + (q1 4 - q1 5) * (q1 5 - c1)) := by
      simp only [Vdm, hU₂, hW₂, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, hX0, hX1, dir0_ne q0 q1 c1 h35,
        dir0_ne q0 q1 c1 h45, dir1_ne q0 q1 c0 h35, dir1_ne q0 q1 c0 h45, dir0_five,
        dir1_five]
      ring
    rw [hx]
    exact mul_ne_zero (mul_ne_zero (hdet 3 4 h35 h45 (by decide)) (hdot 3 h35)) (hdot 4 h45)
  set s : F := (-2 * ((q0 5 - c0) ^ 2 + (q1 5 - c1) ^ 2)) / (Vdm U₁ W₁ * Vdm U₂ W₂) with hs
  refine ⟨Pmat ι₁ ι₂ s Wm
    (Qsix (ι₁ ∘ U₁) (ι₁ ∘ W₁) (ι₂ ∘ U₁) (ι₂ ∘ W₁) (ι₁ ∘ U₂) (ι₁ ∘ W₂) (ι₂ ∘ U₂) (ι₂ ∘ W₂)),
    ?_, ?_⟩
  · intro i
    refine eval_six ι₁ ι₂ s Wm U₁ W₁ U₂ W₂ _ (N i)⁻¹ (X0 i) (X1 i) (hW i) ?_
    fin_cases i
    · exact Or.inl ⟨0, rfl, rfl⟩
    · exact Or.inl ⟨1, rfl, rfl⟩
    · exact Or.inl ⟨2, rfl, rfl⟩
    · exact Or.inr ⟨0, rfl, rfl⟩
    · exact Or.inr ⟨1, rfl, rfl⟩
    · exact Or.inr ⟨2, rfl, rfl⟩
  · have hmul : s * (Vdm U₁ W₁ * Vdm U₂ W₂) = -2 * ((q0 5 - c0) ^ 2 + (q1 5 - c1) ^ 2) := by
      rw [hs]
      exact div_mul_cancel₀ _ (mul_ne_zero hV₁ hV₂)
    have hH : (Pmat ι₁ ι₂ s Wm
        (Qsix (ι₁ ∘ U₁) (ι₁ ∘ W₁) (ι₂ ∘ U₁) (ι₂ ∘ W₁) (ι₁ ∘ U₂) (ι₁ ∘ W₂) (ι₂ ∘ U₂)
          (ι₂ ∘ W₂))).map μ = Param.H c0 c1 C := by
      rw [mult_P ι₁ ι₂ μ h₁ h₂, Qsix_map ι₁ ι₂ μ h₁ h₂, Matrix.mul_smul, Matrix.smul_mul,
        smul_smul, hmul, ← Matrix.smul_mul, ← Matrix.mul_smul,
        ← Param.pullback (q0 5) (q1 5) c0 c1 C (hsph 5)]
      rw [← hΛdef]
      calc Wmᵀ * (Λᵀ * Param.H c0 c1 C * Λ) * Wm
          = (Wmᵀ * Λᵀ) * Param.H c0 c1 C * (Λ * Wm) := by simp only [Matrix.mul_assoc]
        _ = Param.H c0 c1 C := by
          rw [← Matrix.transpose_mul, Param.Lam_mul_Winv _ _ _ _ he, Matrix.transpose_one,
            Matrix.one_mul, Matrix.mul_one]
    intro α β
    have h := congrFun (congrFun hH (some α)) (some β)
    rw [Matrix.map_apply] at h
    rw [h]
    rfl

end Six

/-- Six distinct concyclic points in the plane satisfy the tensor criterion. -/
theorem six_concyclic_certificate (a : Fin 6 → Space 2) (ha : Function.Injective a)
    (hsphere : ∃ c : Space 2, ∃ r : ℝ, ∀ i, dist (a i) c = r) : FieldCriterion a := by
  obtain ⟨c', C, hsph⟩ := exists_rational_sphere a hsphere
  have hsph' : ∀ i, coordinate a i 0 ^ 2 + coordinate a i 1 ^ 2 -
      2 * (c' 0 * coordinate a i 0 + c' 1 * coordinate a i 1) + C = 0 := by
    intro i
    have h := hsph i
    rw [Fin.sum_univ_two, Fin.sum_univ_two] at h
    linear_combination h
  have hdot : ∀ j : Fin 6, j ≠ 5 →
      (coordinate a j 0 - coordinate a 5 0) * (coordinate a 5 0 - c' 0) +
        (coordinate a j 1 - coordinate a 5 1) * (coordinate a 5 1 - c' 1) ≠ 0 :=
    fun j hj => chord_dot_radius_ne_zero a c' C hsph ha (Ne.symm hj)
  have he : (coordinate a 5 0 - c' 0) ^ 2 + (coordinate a 5 1 - c' 1) ^ 2 ≠ 0 := by
    intro h
    have hz := (sum_sq_eq_zero_iff a (fun k => coordinate a 5 k - c' k)).1
      (by rw [Fin.sum_univ_two]; exact h)
    have h0 : coordinate a 5 0 - c' 0 = 0 := hz 0
    have h1 : coordinate a 5 1 - c' 1 = 0 := hz 1
    exact hdot 0 (by decide) (by rw [h0, h1]; ring)
  obtain ⟨P, hev, hsp⟩ := six_abstract (F := Coeff a) (B := TensorRing a) (ι₁ a) (ι₂ a) (μ a)
    (fun x => μ_ι₁ a x) (fun x => μ_ι₂ a x)
    (fun i => coordinate a i 0) (fun i => coordinate a i 1) (c' 0) (c' 1) C hsph'
    (fun j hj => by
      have h := chord_sq_ne_zero a ha (Ne.symm hj)
      rwa [Fin.sum_univ_two] at h)
    he
    (fun j k hj hk hjk => det_ne_zero a c' C hsph ha (Ne.symm hj) (Ne.symm hk) hjk)
    hdot
  refine fieldCriterion_of_matrix a P (fun i => ?_) hsp
  have haug : augmented a i = Param.aug (coordinate a i 0) (coordinate a i 1) := by
    funext α
    rcases α with _ | k
    · rfl
    · fin_cases k <;> rfl
  rw [haug]
  exact hev i

end SixConcyclic.Asm

end

end
