module

public import SixConcyclic.Sphere

/-!
# Facts that use the order of `ℝ`

The coordinate field is a subfield of `ℝ`, so a sum of squares vanishes only termwise. From this:
distinct points have a nonzero chord; a point `x` of an `F`-sphere seen from another point `p` of
it satisfies `|x − p|² + 2⟨p − c', x − p⟩ = 0` (`chord_eq`); three distinct points of a sphere are
not collinear, in the form that two chords from a common point have nonzero Gram determinant
(`gram_ne_zero`), and in the plane nonzero determinant (`det_ne_zero`).
-/

@[expose] public section

namespace SixConcyclic

noncomputable section

variable {s d : ℕ} (a : Fin s → Space d)

theorem sum_sq_eq_zero_iff {ι : Type*} [Fintype ι] (v : ι → Coeff a) :
    ∑ k, v k ^ 2 = 0 ↔ ∀ k, v k = 0 := by
  constructor
  · intro h k
    have hR : ∑ k, ((v k : Coeff a) : ℝ) ^ 2 = 0 := by
      have := congrArg (fun x : Coeff a => (x : ℝ)) h
      simpa only [IntermediateField.coe_sum, IntermediateField.coe_pow,
        IntermediateField.coe_zero] using this
    have hk := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg ((v k : Coeff a) : ℝ))).mp
      hR k (Finset.mem_univ _)
    have hk' : ((v k : Coeff a) : ℝ) = 0 := (pow_eq_zero_iff two_ne_zero).mp hk
    exact Subtype.ext (by simpa only [IntermediateField.coe_zero] using hk')
  · intro h
    simp only [h, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero]

theorem exists_coordinate_ne (ha : Function.Injective a) {i j : Fin s} (hij : i ≠ j) :
    ∃ k, coordinate a i k ≠ coordinate a j k := by
  by_contra h
  push Not at h
  apply hij
  apply ha
  exact PiLp.ext fun k => congrArg Subtype.val (h k)

/-- Distinct points have a chord of nonzero squared length. -/
theorem chord_sq_ne_zero (ha : Function.Injective a) {i j : Fin s} (hij : i ≠ j) :
    ∑ k, (coordinate a j k - coordinate a i k) ^ 2 ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := exists_coordinate_ne a ha hij
  exact hk (sub_eq_zero.mp ((sum_sq_eq_zero_iff a _).mp h k)).symm

/-- The algebra behind `gram_ne_zero`: two vectors `u ≠ 0`, `w ∉ {0, u}` with
`|u|² + 2⟨e, u⟩ = 0` and `|w|² + 2⟨e, w⟩ = 0` have nonzero Gram determinant. -/
theorem gram_ne_zero_of_chords {ι : Type*} [Fintype ι] (u w e : ι → Coeff a)
    (hu : ∃ l, u l ≠ 0) (hw : ∃ l, w l ≠ 0) (huw : ∃ l, w l ≠ u l)
    (hj : ∑ l, u l ^ 2 + 2 * ∑ l, e l * u l = 0) (hk : ∑ l, w l ^ 2 + 2 * ∑ l, e l * w l = 0) :
    (∑ l, u l ^ 2) * (∑ l, w l ^ 2) - (∑ l, u l * w l) ^ 2 ≠ 0 := by
  intro hG
  have hU : ∑ l, u l ^ 2 ≠ 0 := by
    intro h
    obtain ⟨l, hl⟩ := hu
    exact hl ((sum_sq_eq_zero_iff a u).mp h l)
  set U := ∑ l, u l ^ 2 with hUdef
  set S := ∑ l, u l * w l with hSdef
  set W := ∑ l, w l ^ 2 with hWdef
  set t := S / U with ht
  have hv : ∑ l, (w l - t * u l) ^ 2 = 0 := by
    have hexp : ∑ l, (w l - t * u l) ^ 2 = W - 2 * t * S + t ^ 2 * U := by
      have : ∑ l, (w l - t * u l) ^ 2 =
          ∑ l, (w l ^ 2 - (2 * t) * (u l * w l)) + ∑ l, t ^ 2 * u l ^ 2 := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun l _ => by ring
      rw [this, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [hexp, ht]
    field_simp
    linear_combination hG
  have hwt : ∀ l, w l = t * u l := fun l => sub_eq_zero.mp ((sum_sq_eq_zero_iff a _).mp hv l)
  have hW' : W = t ^ 2 * U := by
    rw [hWdef, hUdef, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [hwt l]; ring
  have hE' : ∑ l, e l * w l = t * ∑ l, e l * u l := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [hwt l]; ring
  rw [hW', hE'] at hk
  have hprod : t * (t - 1) * U = 0 := by linear_combination hk - t * hj
  rcases mul_eq_zero.mp hprod with h | h
  · rcases mul_eq_zero.mp h with h0 | h1
    · obtain ⟨l, hl⟩ := hw
      exact hl (by rw [hwt l, h0, zero_mul])
    · obtain ⟨l, hl⟩ := huw
      exact hl (by rw [hwt l, sub_eq_zero.mp h1, one_mul])
  · exact hU h

section sphere

variable (c' : Fin d → Coeff a) (C : Coeff a)
  (hsph : ∀ i, ∑ j, coordinate a i j ^ 2 - 2 * ∑ j, c' j * coordinate a i j + C = 0)

include hsph

/-- The squared distance from a point of the sphere to `c'` is `|c'|² − C`. -/
theorem sub_center_sq_eq (i : Fin s) :
    ∑ k, (coordinate a i k - c' k) ^ 2 = ∑ k, c' k ^ 2 - C := by
  have : ∑ k, (coordinate a i k - c' k) ^ 2 =
      ∑ k, (coordinate a i k ^ 2 - 2 * (c' k * coordinate a i k)) + ∑ k, c' k ^ 2 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [this, Finset.sum_sub_distrib, ← Finset.mul_sum]
  linear_combination hsph i

/-- Two points of the sphere: `|x − p|² + 2⟨p − c', x − p⟩ = 0`. -/
theorem chord_eq (i j : Fin s) :
    ∑ k, (coordinate a j k - coordinate a i k) ^ 2 +
      2 * ∑ k, (coordinate a i k - c' k) * (coordinate a j k - coordinate a i k) = 0 := by
  calc _ = ∑ k, ((coordinate a j k - c' k) ^ 2 - (coordinate a i k - c' k) ^ 2) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = 0 := by
        rw [Finset.sum_sub_distrib, sub_center_sq_eq a c' C hsph i,
          sub_center_sq_eq a c' C hsph j, sub_self]

/-- Two points of the sphere are equidistant from `c'`. -/
theorem dist_sq_eq (i j : Fin s) :
    ∑ k, (coordinate a j k - c' k) ^ 2 = ∑ k, (coordinate a i k - c' k) ^ 2 := by
  rw [sub_center_sq_eq a c' C hsph i, sub_center_sq_eq a c' C hsph j]

/-- A point of a sphere with at least two points is not `c'`. -/
theorem sub_center_sq_ne_zero (ha : Function.Injective a) {i j : Fin s} (hij : i ≠ j) :
    ∑ k, (coordinate a i k - c' k) ^ 2 ≠ 0 := by
  intro h
  have hj : ∑ k, (coordinate a j k - c' k) ^ 2 = 0 := by
    rw [dist_sq_eq a c' C hsph i j, h]
  obtain ⟨k, hk⟩ := exists_coordinate_ne a ha hij
  apply hk
  rw [sub_eq_zero.mp ((sum_sq_eq_zero_iff a _).mp h k),
    sub_eq_zero.mp ((sum_sq_eq_zero_iff a _).mp hj k)]

/-- Three distinct points of a sphere are not collinear: the Gram determinant of the two chords
from `a i` to `a j` and `a k` is nonzero. -/
theorem gram_ne_zero (ha : Function.Injective a) {i j k : Fin s} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    (∑ l, (coordinate a j l - coordinate a i l) ^ 2) *
        (∑ l, (coordinate a k l - coordinate a i l) ^ 2) -
      (∑ l, (coordinate a j l - coordinate a i l) * (coordinate a k l - coordinate a i l)) ^ 2
      ≠ 0 := by
  have hj := chord_eq a c' C hsph i j
  have hk := chord_eq a c' C hsph i k
  refine gram_ne_zero_of_chords a (fun l => coordinate a j l - coordinate a i l)
    (fun l => coordinate a k l - coordinate a i l) (fun l => coordinate a i l - c' l)
    ?_ ?_ ?_ hj hk
  · obtain ⟨l, hl⟩ := exists_coordinate_ne a ha hij
    exact ⟨l, sub_ne_zero.mpr (Ne.symm hl)⟩
  · obtain ⟨l, hl⟩ := exists_coordinate_ne a ha hik
    exact ⟨l, sub_ne_zero.mpr (Ne.symm hl)⟩
  · obtain ⟨l, hl⟩ := exists_coordinate_ne a ha hjk
    exact ⟨l, fun h => hl (sub_left_injective h).symm⟩

end sphere

/-- In the plane, three distinct points of a circle have a nonzero chord determinant. -/
theorem det_ne_zero (a : Fin s → Space 2) (c' : Fin 2 → Coeff a) (C : Coeff a)
    (hsph : ∀ i, ∑ j, coordinate a i j ^ 2 - 2 * ∑ j, c' j * coordinate a i j + C = 0)
    (ha : Function.Injective a) {i j k : Fin s} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (coordinate a j 0 - coordinate a i 0) * (coordinate a k 1 - coordinate a i 1) -
      (coordinate a j 1 - coordinate a i 1) * (coordinate a k 0 - coordinate a i 0) ≠ 0 := by
  intro h
  apply gram_ne_zero a c' C hsph ha hij hik hjk
  simp only [Fin.sum_univ_two]
  linear_combination ((coordinate a j 0 - coordinate a i 0) * (coordinate a k 1 - coordinate a i 1) -
      (coordinate a j 1 - coordinate a i 1) * (coordinate a k 0 - coordinate a i 0)) * h

/-- In the plane, the chord from a point of the circle is not orthogonal to the radius there:
`⟨x − p, p − c'⟩ = −|x − p|²/2 ≠ 0`. -/
theorem chord_dot_radius_ne_zero (a : Fin s → Space 2) (c' : Fin 2 → Coeff a) (C : Coeff a)
    (hsph : ∀ i, ∑ j, coordinate a i j ^ 2 - 2 * ∑ j, c' j * coordinate a i j + C = 0)
    (ha : Function.Injective a) {i j : Fin s} (hij : i ≠ j) :
    (coordinate a j 0 - coordinate a i 0) * (coordinate a i 0 - c' 0) +
      (coordinate a j 1 - coordinate a i 1) * (coordinate a i 1 - c' 1) ≠ 0 := by
  intro h
  apply chord_sq_ne_zero a ha hij
  have hc := chord_eq a c' C hsph i j
  simp only [Fin.sum_univ_two] at hc ⊢
  linear_combination hc - 2 * h

end

end SixConcyclic

end
