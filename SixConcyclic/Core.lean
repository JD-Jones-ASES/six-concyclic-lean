module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FinCases

/-!
# Six concyclic points: the (1,1)-forms

In an abstract commutative ring: the (1,1)-form `ell` through three parameter points of
`B² × B²` (`ell_vanishes`), the matrix `Qm` of a product of two such forms in Veronese
coordinates (`Qm_form`), and the coefficients after multiplication, where the corner ones vanish
and the middle ones are the bracket product up to sign (`mult_coeffs`).
-/

@[expose] public section

noncomputable section

namespace SixConcyclic.Core

section Abstract

variable {B : Type*} [CommRing B]

/-- 3×3 determinant, written out. -/
def det3 (a b c d e f g h i : B) : B := a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)

/-- Coefficients of the (1,1)-form through three points `(X, Y) = (p_j, p'_j)`, where
`p_j = (U j, W j)` lives on the left factor and `p'_j = (U' j, W' j)` on the right factor:
`ℓ(X,Y) = det [[X0Y0, X0Y1, X1Y0, X1Y1], row 0, row 1, row 2]`, expanded along the first row. -/
def c00 (U W U' W' : Fin 3 → B) : B :=
  det3 (U 0 * W' 0) (W 0 * U' 0) (W 0 * W' 0) (U 1 * W' 1) (W 1 * U' 1) (W 1 * W' 1)
    (U 2 * W' 2) (W 2 * U' 2) (W 2 * W' 2)
def c01 (U W U' W' : Fin 3 → B) : B :=
  -det3 (U 0 * U' 0) (W 0 * U' 0) (W 0 * W' 0) (U 1 * U' 1) (W 1 * U' 1) (W 1 * W' 1)
    (U 2 * U' 2) (W 2 * U' 2) (W 2 * W' 2)
def c10 (U W U' W' : Fin 3 → B) : B :=
  det3 (U 0 * U' 0) (U 0 * W' 0) (W 0 * W' 0) (U 1 * U' 1) (U 1 * W' 1) (W 1 * W' 1)
    (U 2 * U' 2) (U 2 * W' 2) (W 2 * W' 2)
def c11 (U W U' W' : Fin 3 → B) : B :=
  -det3 (U 0 * U' 0) (U 0 * W' 0) (W 0 * U' 0) (U 1 * U' 1) (U 1 * W' 1) (W 1 * U' 1)
    (U 2 * U' 2) (U 2 * W' 2) (W 2 * U' 2)

def ell (U W U' W' : Fin 3 → B) (X0 X1 Y0 Y1 : B) : B :=
  X0 * Y0 * c00 U W U' W' + X0 * Y1 * c01 U W U' W' + X1 * Y0 * c10 U W U' W' +
    X1 * Y1 * c11 U W U' W'

theorem ell_vanishes (U W U' W' : Fin 3 → B) (j : Fin 3) :
    ell U W U' W' (U j) (W j) (U' j) (W' j) = 0 := by
  fin_cases j <;> simp only [Fin.reduceFinMk, Fin.zero_eta, Fin.mk_one, Fin.isValue, ell, c00, c01, c10, c11,
    det3] <;> ring

/-- Veronese vector `(X0², X0X1, X1²)`. -/
def ver (X0 X1 : B) : Fin 3 → B := ![X0 * X0, X0 * X1, X1 * X1]

/-- The 3×3 matrix of the biquadratic form `ℓ · ℓ'` in Veronese coordinates. -/
def Qm (a00 a01 a10 a11 b00 b01 b10 b11 : B) : Matrix (Fin 3) (Fin 3) B :=
  !![a00 * b00, a00 * b01 + a01 * b00, a01 * b01;
     a00 * b10 + a10 * b00, a00 * b11 + a01 * b10 + a10 * b01 + a11 * b00, a01 * b11 + a11 * b01;
     a10 * b10, a10 * b11 + a11 * b10, a11 * b11]

theorem Qm_form (a00 a01 a10 a11 b00 b01 b10 b11 X0 X1 Y0 Y1 : B) :
    ∑ γ, ∑ δ, ver X0 X1 γ * Qm a00 a01 a10 a11 b00 b01 b10 b11 γ δ * ver Y0 Y1 δ =
      (X0 * Y0 * a00 + X0 * Y1 * a01 + X1 * Y0 * a10 + X1 * Y1 * a11) *
      (X0 * Y0 * b00 + X0 * Y1 * b01 + X1 * Y0 * b10 + X1 * Y1 * b11) := by
  simp only [Fin.sum_univ_three, ver, Qm, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.head_fin_const]
  ring

/-- After multiplication (`U' = U`, `W' = W`) the corner coefficients vanish and the middle ones
are ± the Veronese Vandermonde. -/
theorem mult_coeffs (U W : Fin 3 → B) :
    c00 U W U W = 0 ∧ c11 U W U W = 0 ∧
    c10 U W U W = (U 0 * W 1 - U 1 * W 0) * (U 0 * W 2 - U 2 * W 0) * (U 1 * W 2 - U 2 * W 1) ∧
    c01 U W U W = -((U 0 * W 1 - U 1 * W 0) * (U 0 * W 2 - U 2 * W 0) * (U 1 * W 2 - U 2 * W 1)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [c00, c01, c10, c11, det3] <;> ring

end Abstract

end SixConcyclic.Core

end

end
