module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Six concyclic points: the parametrization of the circle

Over a field: the homogeneous parametrization `Lam` of a circle from a base point `p`
(centre `c`, `e = p − c`), sending the Veronese vector of a chord direction `x = q − p` to
`|x|² (1, q)` (`Lam_ver`) and that of the tangent direction to `|e|² (1, p)` (`Lam_tangent`); its
two-sided inverse `Winv` when `|e|² ≠ 0`; and the pulled-back circle matrix
`Lamᵀ H Lam = −2|e|² K` (`pullback`).
-/

@[expose] public section

noncomputable section

namespace SixConcyclic.Param

open Matrix

variable {F : Type*} [Field F]

/-- Veronese vector `(u², uw, w²)`. -/
def ver (u w : F) : Fin 3 → F := ![u * u, u * w, w * w]

/-- Augmented point `(1, q0, q1)` indexed by `Option (Fin 2)`. -/
def aug (q0 q1 : F) : Option (Fin 2) → F
  | none => 1
  | some k => if k = 0 then q0 else q1

/-- `Λ (u², uw, w²) = (|x|², |x|² p − 2⟨e, x⟩ x)` for `x = (u, w)`. -/
def Lam (p0 p1 c0 c1 : F) : Matrix (Option (Fin 2)) (Fin 3) F := fun α γ =>
  match α with
  | none => ![1, 0, 1] γ
  | some k => if k = 0 then ![p0 - 2 * (p0 - c0), -2 * (p1 - c1), p0] γ
      else ![p1, -2 * (p0 - c0), p1 - 2 * (p1 - c1)] γ

theorem Lam_ver (p0 p1 c0 c1 q0 q1 : F)
    (hq : (q0 - c0) ^ 2 + (q1 - c1) ^ 2 = (p0 - c0) ^ 2 + (p1 - c1) ^ 2) (α : Option (Fin 2)) :
    ∑ γ, Lam p0 p1 c0 c1 α γ * ver (q0 - p0) (q1 - p1) γ =
      ((q0 - p0) ^ 2 + (q1 - p1) ^ 2) * aug q0 q1 α := by
  rcases α with _ | k
  · simp [Lam, ver, aug, Fin.sum_univ_three]; ring
  · fin_cases k
    · simp [Lam, ver, aug, Fin.sum_univ_three]
      linear_combination (-(q0 - p0)) * hq
    · simp [Lam, ver, aug, Fin.sum_univ_three]
      linear_combination (-(q1 - p1)) * hq

theorem Lam_tangent (p0 p1 c0 c1 : F) (α : Option (Fin 2)) :
    ∑ γ, Lam p0 p1 c0 c1 α γ * ver (-(p1 - c1)) (p0 - c0) γ =
      ((p0 - c0) ^ 2 + (p1 - c1) ^ 2) * aug p0 p1 α := by
  rcases α with _ | k
  · simp [Lam, ver, aug, Fin.sum_univ_three]; ring
  · fin_cases k <;> simp [Lam, ver, aug, Fin.sum_univ_three] <;> ring

/-- The circle matrix with spatial block `I`: `|x|² − 2⟨c, x⟩ + C`. -/
def H (c0 c1 C : F) : Matrix (Option (Fin 2)) (Option (Fin 2)) F := fun α β =>
  match α, β with
  | none, none => C
  | none, some k => -(if k = 0 then c0 else c1)
  | some k, none => -(if k = 0 then c0 else c1)
  | some j, some k => if j = k then 1 else 0

def K : Matrix (Fin 3) (Fin 3) F := !![0, 0, 1; 0, -2, 0; 1, 0, 0]

theorem pullback (p0 p1 c0 c1 C : F) (hp : p0 ^ 2 + p1 ^ 2 - 2 * (c0 * p0 + c1 * p1) + C = 0) :
    (Lam p0 p1 c0 c1)ᵀ * H c0 c1 C * Lam p0 p1 c0 c1 =
      (-2 * ((p0 - c0) ^ 2 + (p1 - c1) ^ 2)) • (K : Matrix (Fin 3) (Fin 3) F) := by
  ext γ δ
  fin_cases γ <;> fin_cases δ <;>
    simp [Matrix.mul_apply, Fintype.sum_option, Fin.sum_univ_two, Lam, H, K] <;>
    first | ring1 | linear_combination hp

/-- The explicit inverse `adj(Λ) / det Λ`, `det Λ = 4|e|²`. -/
def Winv (p0 p1 c0 c1 : F) : Matrix (Fin 3) (Option (Fin 2)) F := fun γ α =>
  (4 * ((p0 - c0) ^ 2 + (p1 - c1) ^ 2))⁻¹ *
  (match α with
  | none => ![2 * (-c0 * p0 + 2 * c1 ^ 2 - 3 * c1 * p1 + p0 ^ 2 + p1 ^ 2),
      2 * (-2 * c0 * c1 + c0 * p1 + c1 * p0),
      2 * (2 * c0 ^ 2 - 3 * c0 * p0 - c1 * p1 + p0 ^ 2 + p1 ^ 2)] γ
  | some k => if k = 0 then ![-2 * (p0 - c0), -2 * (p1 - c1), 2 * (p0 - c0)] γ
      else ![2 * (p1 - c1), -2 * (p0 - c0), -2 * (p1 - c1)] γ)

theorem Winv_mul_Lam [CharZero F] (p0 p1 c0 c1 : F) (he : (p0 - c0) ^ 2 + (p1 - c1) ^ 2 ≠ 0) :
    Winv p0 p1 c0 c1 * Lam p0 p1 c0 c1 = 1 := by
  have h4 : (4 : F) * ((p0 - c0) ^ 2 + (p1 - c1) ^ 2) ≠ 0 := by
    intro h; rcases mul_eq_zero.mp h with h | h
    · exact absurd h (by norm_num)
    · exact he h
  ext γ δ
  fin_cases γ <;> fin_cases δ <;>
    simp [Matrix.mul_apply, Fintype.sum_option, Fin.sum_univ_two, Winv, Lam] <;>
    field_simp <;> ring

theorem Lam_mul_Winv [CharZero F] (p0 p1 c0 c1 : F) (he : (p0 - c0) ^ 2 + (p1 - c1) ^ 2 ≠ 0) :
    Lam p0 p1 c0 c1 * Winv p0 p1 c0 c1 = 1 := by
  have h4 : (4 : F) * ((p0 - c0) ^ 2 + (p1 - c1) ^ 2) ≠ 0 := by
    intro h; rcases mul_eq_zero.mp h with h | h
    · exact absurd h (by norm_num)
    · exact he h
  ext α β
  rcases α with _ | j <;> rcases β with _ | k <;> (try fin_cases j) <;> (try fin_cases k) <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Winv, Lam] <;> field_simp <;> ring

end SixConcyclic.Param

end

end
