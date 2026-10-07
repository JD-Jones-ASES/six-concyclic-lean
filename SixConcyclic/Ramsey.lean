module

public import SixConcyclic.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Fintype.EquivFin

/-!
# The Ramsey property: restriction, small cases, extension on a circle, affine span

Everything here is over `ℝ`. A sub-configuration of a Ramsey configuration is Ramsey
(`ramsey_restrict`: a monochromatic copy of the whole contains one of the part); the empty and
the one-point configurations are Ramsey; a configuration congruent to a Ramsey one is Ramsey.
A circle of positive radius is infinite, so at most six of its points extend to exactly six
(`extend_to_six`); a sphere through two distinct points has positive radius; six distinct
concyclic points affinely span the plane (three of them already do). Several of these adapt the
corresponding lemmas of `lean/OAI/Combinatorics/EuclideanRamsey/` (Apache-2.0; see `NOTICE`).
-/

@[expose] public section

namespace SixConcyclic

noncomputable section

/-- Restriction of a Ramsey configuration along any map of index sets.
Adapts `ramsey_restrict` of openai/math `CircleGeometry.lean` (Apache-2.0). -/
theorem ramsey_restrict {s t d : ℕ} (a : Fin t → Space d) (f : Fin s → Fin t) (ha : Ramsey a) :
    Ramsey (a ∘ f) := by
  intro r hr
  obtain ⟨D, hD, h⟩ := ha r hr
  refine ⟨D, hD, ?_⟩
  intro c
  obtain ⟨b, hb, k, hk⟩ := h c
  exact ⟨b ∘ f, fun i j => hb (f i) (f j), k, fun i => hk (f i)⟩

/-- The empty configuration is Ramsey. Adapts `quadratic_empty_ramsey` of openai/math
`Quadratic.lean` (Apache-2.0). -/
theorem ramsey_empty {d : ℕ} (a : Fin 0 → Space d) : Ramsey a := by
  intro r hr
  refine ⟨1, le_rfl, ?_⟩
  intro c
  exact ⟨Fin.elim0, fun i => Fin.elim0 i, ⟨0, by omega⟩, fun i => Fin.elim0 i⟩

/-- A one-point configuration is Ramsey. Adapts `zero_radius_ramsey` of openai/math
`CircleGeometry.lean` (Apache-2.0). -/
theorem ramsey_singleton {d : ℕ} (a : Fin 1 → Space d) : Ramsey a := by
  intro r hr
  refine ⟨1, le_rfl, ?_⟩
  intro c
  refine ⟨fun _ => 0, ?_, c 0, fun _ => rfl⟩
  intro i j
  rw [Subsingleton.elim i j, dist_self, dist_self]

/-- A configuration congruent to a Ramsey configuration is Ramsey. -/
theorem ramsey_of_congruent {s d D : ℕ} {a : Fin s → Space d} {b : Fin s → Space D}
    (hab : Congruent a b) (hb : Ramsey b) : Ramsey a := by
  intro r hr
  obtain ⟨E, hE, h⟩ := hb r hr
  refine ⟨E, hE, ?_⟩
  intro c
  obtain ⟨b', hb', k, hk⟩ := h c
  exact ⟨b', fun i j => (hb' i j).trans (hab i j), k, hk⟩

/-- A sphere through two distinct points has positive radius. -/
theorem radius_pos {s d : ℕ} (a : Fin s → Space d) (hs : 2 ≤ s) (ha : Function.Injective a)
    (c : Space d) (r : ℝ) (hc : ∀ i, dist (a i) c = r) : 0 < r := by
  have h0 := hc ⟨0, by omega⟩
  have h1 := hc ⟨1, by omega⟩
  rcases (dist_nonneg.trans_eq h0).lt_or_eq with hr | hr
  · exact hr
  · exfalso
    have e0 : a ⟨0, by omega⟩ = c := dist_eq_zero.mp (h0.trans hr.symm)
    have e1 : a ⟨1, by omega⟩ = c := dist_eq_zero.mp (h1.trans hr.symm)
    have := ha (e0.trans e1.symm)
    simp [Fin.ext_iff] at this

/-- Rational parametrisation of a circle of radius `r`.
Adapts `stereographic` of openai/math `CircleExtension.lean` (Apache-2.0). -/
def stereographic (c : Space 2) (r t : ℝ) : Space 2 :=
  c + r • WithLp.toLp 2 ![(1-t^2)/(1+t^2), (2*t)/(1+t^2)]

/-- The parameter is recovered from the stereographic point.
Adapts `stereographic_recover` of openai/math `CircleExtension.lean` (Apache-2.0). -/
theorem stereographic_recover (t : ℝ) :
    ((2*t)/(1+t^2)) / (1 + (1-t^2)/(1+t^2)) = t := by
  have hd : 1+t^2 ≠ 0 := by positivity
  have he : 1 + (1-t^2)/(1+t^2) = 2/(1+t^2) := by field_simp; ring
  rw [he, div_div]
  field_simp

/-- The stereographic parametrisation is injective for positive radius.
Adapts `stereographic_injective` of openai/math `CircleExtension.lean` (Apache-2.0). -/
theorem stereographic_injective (c : Space 2) (r : ℝ) (hr : 0 < r) :
    Function.Injective (stereographic c r) := by
  intro t u h
  have h₀ := congrArg (fun p : Space 2 => p 0) h
  have h₁ := congrArg (fun p : Space 2 => p 1) h
  have hx : (1-t^2)/(1+t^2) = (1-u^2)/(1+u^2) := by
    apply mul_left_cancel₀ (ne_of_gt hr)
    apply add_left_cancel (a := c 0)
    simpa only [stereographic, PiLp.add_apply, PiLp.smul_apply, PiLp.toLp_apply,
      Matrix.cons_val_zero, smul_eq_mul] using h₀
  have hy : (2*t)/(1+t^2) = (2*u)/(1+u^2) := by
    apply mul_left_cancel₀ (ne_of_gt hr)
    apply add_left_cancel (a := c 1)
    simpa only [stereographic, PiLp.add_apply, PiLp.smul_apply, PiLp.toLp_apply,
      Matrix.cons_val_one, Matrix.cons_val_zero, smul_eq_mul] using h₁
  calc
    t = ((2*t)/(1+t^2)) / (1 + (1-t^2)/(1+t^2)) := (stereographic_recover t).symm
    _ = ((2*u)/(1+u^2)) / (1 + (1-u^2)/(1+u^2)) := by rw [hx, hy]
    _ = u := stereographic_recover u

/-- Stereographic points lie on the circle.
Adapts `stereographic_on_circle` of openai/math `CircleExtension.lean` (Apache-2.0). -/
theorem stereographic_on_circle (c : Space 2) (r t : ℝ) (hr : 0 < r) :
    dist (stereographic c r t) c = r := by
  have hd : 1+t^2 ≠ 0 := by positivity
  have hs : ((1-t^2)/(1+t^2))^2 + ((2*t)/(1+t^2))^2 = 1 := by
    field_simp
    ring
  have he : dist (stereographic c r t) c ^ 2 = r^2 := by
    simp only [dist_eq_norm, stereographic, add_sub_cancel_left]
    rw [norm_smul, mul_pow]
    simp only [Real.norm_eq_abs, sq_abs, EuclideanSpace.norm_sq_eq,
      Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Real.norm_eq_abs, sq_abs]
    rw [hs, mul_one]
  have hn : 0 ≤ dist (stereographic c r t) c := dist_nonneg
  nlinarith

/-- A circle of positive radius is infinite.
Adapts `circle_infinite` of openai/math `CircleExtension.lean` (Apache-2.0). -/
theorem circle_infinite (c : Space 2) (r : ℝ) (hr : 0 < r) :
    {p : Space 2 | dist p c = r}.Infinite := by
  apply (Set.infinite_range_of_injective (stereographic_injective c r hr)).mono
  rintro p ⟨t, rfl⟩
  exact stereographic_on_circle c r t hr

/-- At most six distinct points of a circle of positive radius extend to six.
Adapts `extend_to_five` of openai/math `CircleExtension.lean` (Apache-2.0). -/
theorem extend_to_six {s : ℕ} (a : Fin s → Space 2) (hs : s ≤ 6) (ha : Function.Injective a)
    (c : Space 2) (r : ℝ) (hr : 0 < r) (hc : ∀ i, dist (a i) c = r) :
    ∃ b : Fin 6 → Space 2, Function.Injective b ∧ (∀ j, dist (b j) c = r) ∧
      ∃ f : Fin s → Fin 6, ∀ i, b (f i) = a i := by
  classical
  let S : Finset (Space 2) := Finset.univ.image a
  have hS : S.card = s := by simp [S, Finset.card_image_of_injective _ ha]
  have hSc : ∀ p ∈ S, dist p c = r := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    exact hc i
  obtain ⟨T, hTc, hT⟩ := (circle_infinite c r hr).exists_subset_card_eq 6
  have hST : 6 ≤ (S ∪ T).card := by
    rw [← hT]
    exact Finset.card_le_card Finset.subset_union_right
  obtain ⟨U, hSU, hUst, hU⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_union_left : S ⊆ S ∪ T) (by omega : S.card ≤ 6) hST
  let e : U ≃ Fin 6 := Finset.equivFinOfCardEq hU
  let b : Fin 6 → Space 2 := fun j => (e.symm j).val
  refine ⟨b, ?_, ?_, ?_⟩
  · intro i j hij
    exact e.symm.injective (Subtype.ext hij)
  · intro j
    have hj : b j ∈ S ∪ T := hUst (e.symm j).property
    rcases Finset.mem_union.mp hj with hj | hj
    · exact hSc _ hj
    · exact hTc hj
  · let f : Fin s → Fin 6 := fun i => e ⟨a i, hSU (by simp [S])⟩
    refine ⟨f, ?_⟩
    intro i
    simp [b, f]

/-- Three points of a real circle cannot sit at three distinct parameters of a secant.
Adapts `circle_parameter_eq_zero_or_one` of openai/math `CircleGeometry.lean` (Apache-2.0). -/
theorem circle_parameter_eq_zero_or_one
    (x₀ x₁ y₀ y₁ c₀ c₁ R t : ℝ)
    (hx : (x₀-c₀)^2 + (x₁-c₁)^2 = R)
    (hy : (y₀-c₀)^2 + (y₁-c₁)^2 = R)
    (hz : (x₀+t*(y₀-x₀)-c₀)^2 + (x₁+t*(y₁-x₁)-c₁)^2 = R)
    (hxy : x₀ ≠ y₀ ∨ x₁ ≠ y₁) : t = 0 ∨ t = 1 := by
  have hnorm : (y₀-x₀)^2 + (y₁-x₁)^2 ≠ 0 := by
    intro h
    have h₀ : y₀-x₀ = 0 := by nlinarith [sq_nonneg (y₁-x₁)]
    have h₁ : y₁-x₁ = 0 := by nlinarith [sq_nonneg (y₀-x₀)]
    rcases hxy with hxy | hxy <;> apply hxy <;> linarith
  have hprod : t * (t-1) * ((y₀-x₀)^2 + (y₁-x₁)^2) = 0 := by
    linear_combination hz - (1-t)*hx - t*hy
  rcases mul_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hnorm) with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

/-- The determinant of two chords from a common point of a circle is nonzero at three distinct
points. Adapts `secant_nonzero` of openai/math `CircleGeometry.lean` (Apache-2.0). -/
theorem secant_nonzero
    (x₀ x₁ y₀ y₁ z₀ z₁ c₀ c₁ R : ℝ)
    (hx : (x₀-c₀)^2 + (x₁-c₁)^2 = R)
    (hy : (y₀-c₀)^2 + (y₁-c₁)^2 = R)
    (hz : (z₀-c₀)^2 + (z₁-c₁)^2 = R)
    (hxy : x₀ ≠ y₀ ∨ x₁ ≠ y₁)
    (hxz : x₀ ≠ z₀ ∨ x₁ ≠ z₁)
    (hyz : y₀ ≠ z₀ ∨ y₁ ≠ z₁) :
    (y₀-x₀)*(z₁-x₁) - (y₁-x₁)*(z₀-x₀) ≠ 0 := by
  intro hdet
  by_cases hdx : y₀-x₀ = 0
  · have hdy : y₁-x₁ ≠ 0 := by
      intro hdy
      rcases hxy with hxy | hxy <;> apply hxy <;> linarith
    have hzx : z₀ = x₀ := by
      have : (y₁-x₁)*(z₀-x₀) = 0 := by rw [hdx] at hdet; nlinarith
      have := (mul_eq_zero.mp this).resolve_left hdy
      linarith
    let t := (z₁-x₁)/(y₁-x₁)
    have ht : x₁+t*(y₁-x₁) = z₁ := by dsimp [t]; field_simp; ring
    have htx : x₀+t*(y₀-x₀) = z₀ := by rw [hdx]; simp [hzx]
    have he := circle_parameter_eq_zero_or_one x₀ x₁ y₀ y₁ c₀ c₁ R t hx hy
      (by rw [ht, htx]; exact hz) hxy
    rcases he with he | he
    · rcases hxz with h | h <;> apply h <;> simp_all
    · rcases hyz with h | h
      · apply h
        calc
          y₀ = x₀ := sub_eq_zero.mp hdx
          _ = z₀ := hzx.symm
      · apply h
        simpa [he] using ht
  · let t := (z₀-x₀)/(y₀-x₀)
    have ht : x₀+t*(y₀-x₀) = z₀ := by dsimp [t]; field_simp; ring
    have hty : x₁+t*(y₁-x₁) = z₁ := by
      dsimp [t]
      apply (mul_right_cancel₀ hdx)
      field_simp
      nlinarith [hdet]
    have he := circle_parameter_eq_zero_or_one x₀ x₁ y₀ y₁ c₀ c₁ R t hx hy
      (by rw [ht, hty]; exact hz) hxy
    rcases he with he | he
    · rcases hxz with h | h <;> apply h <;> simp_all
    · rcases hyz with h | h <;> apply h <;> simp_all

/-- The metric circle equation in coordinates.
Adapts `circle_coordinates` of openai/math `CircleGeometry.lean` (Apache-2.0). -/
theorem circle_coordinates {s : ℕ} (a : Fin s → Space 2)
    (c : Space 2) (r : ℝ) (hc : ∀ i, dist (a i) c = r) :
    ∀ i, (a i 0-c 0)^2 + (a i 1-c 1)^2 = r^2 := by
  intro i
  have h := congrArg (fun x : ℝ => x^2) (hc i)
  simpa [dist_eq_norm, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two,
    Real.norm_eq_abs, sq_abs] using h

/-- Two distinct points of the plane differ in some coordinate. -/
theorem coord_ne_of_ne {p q : Space 2} (h : p ≠ q) : p 0 ≠ q 0 ∨ p 1 ≠ q 1 := by
  by_contra hc
  push Not at hc
  apply h
  ext j
  fin_cases j
  · exact hc.1
  · exact hc.2

/-- Six distinct concyclic points affinely span the plane (three of them already do).
Adapts `circle_five_affineSpan` of openai/math `CircleSpan.lean` (Apache-2.0), with the
determinant bound taken from `secant_nonzero` over `ℝ`. -/
theorem six_concyclic_affineSpan (a : Fin 6 → Space 2) (ha : Function.Injective a) (c : Space 2)
    (r : ℝ) (hc : ∀ i, dist (a i) c = r) : affineSpan ℝ (Set.range a) = ⊤ := by
  classical
  let A := affineSpan ℝ (Set.range a)
  have hp (i : Fin 6) : a i ∈ A := mem_affineSpan ℝ (Set.mem_range_self i)
  let u := a 1 - a 0
  let v := a 2 - a 0
  let D : ℝ := u 0 * v 1 - v 0 * u 1
  have hcc := circle_coordinates a c r hc
  have hne (i j : Fin 6) (hij : i ≠ j) : a i 0 ≠ a j 0 ∨ a i 1 ≠ a j 1 :=
    coord_ne_of_ne (fun h => hij (ha h))
  have hsec := secant_nonzero (a 0 0) (a 0 1) (a 1 0) (a 1 1) (a 2 0) (a 2 1) (c 0) (c 1) (r^2)
    (hcc 0) (hcc 1) (hcc 2) (hne 0 1 (by decide)) (hne 0 2 (by decide)) (hne 1 2 (by decide))
  have hD : D ≠ 0 := by
    intro h
    apply hsec
    have hDe : D = (a 1 0 - a 0 0) * (a 2 1 - a 0 1) - (a 1 1 - a 0 1) * (a 2 0 - a 0 0) := by
      simp only [D, u, v, PiLp.sub_apply]; ring
    rw [← hDe, h]
  have hu : u ∈ A.direction := by
    simpa [u, vsub_eq_sub] using AffineSubspace.vsub_mem_direction (hp 1) (hp 0)
  have hv : v ∈ A.direction := by
    simpa [v, vsub_eq_sub] using AffineSubspace.vsub_mem_direction (hp 2) (hp 0)
  apply top_unique
  intro x _
  let w := x - a 0
  let α : ℝ := (w 0 * v 1 - v 0 * w 1) / D
  let β : ℝ := (u 0 * w 1 - w 0 * u 1) / D
  have hcomb : α • u + β • v = w := by
    ext j
    fin_cases j <;>
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] <;>
      dsimp [α, β] <;>
      field_simp [hD] <;>
      dsimp [D] <;> ring
  have hm : α • u + β • v ∈ A.direction :=
    A.direction.add_mem (A.direction.smul_mem α hu) (A.direction.smul_mem β hv)
  have he := AffineSubspace.vadd_mem_of_mem_direction hm (hp 0)
  simpa [hcomb, w, vadd_eq_add] using he

end

end SixConcyclic

end
