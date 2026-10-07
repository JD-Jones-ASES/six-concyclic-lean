module

public import SixConcyclic.Defs
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# A spanning congruent representative

A configuration of at least two distinct points is congruent to one that affinely spans its
space: translate so that the first point is the origin, take the span `V` of the translated
points, and map `V` isometrically onto `Space (finrank V)` by an orthonormal basis. Sphericity
transports along with it: if the original points lie on a sphere with centre `c`, the images lie
on the sphere centred at the image of the orthogonal projection of `c − a₀` onto `V`, by
Pythagoras. This adapts `full_affine_representative` of
`lean/OAI/Combinatorics/EuclideanRamsey/Main.lean` (Apache-2.0; see `NOTICE`), with the sphere
added.
-/

@[expose] public section

namespace SixConcyclic

noncomputable section

/-- Every spherical configuration of at least two distinct points is congruent to an injective
spherical configuration that affinely spans a space of positive dimension. -/
theorem exists_spanning_representative {s D : ℕ} (a : Fin s → Space D) (hs : 2 ≤ s)
    (ha : Function.Injective a) (hsphere : ∃ c : Space D, ∃ r : ℝ, ∀ i, dist (a i) c = r) :
    ∃ d : ℕ, 1 ≤ d ∧ ∃ b : Fin s → Space d, Function.Injective b ∧ Congruent a b ∧
      affineSpan ℝ (Set.range b) = ⊤ ∧ ∃ c : Space d, ∃ r : ℝ, ∀ i, dist (b i) c = r := by
  classical
  obtain ⟨c, r, hr⟩ := hsphere
  let i₀ : Fin s := ⟨0, by omega⟩
  let i₁ : Fin s := ⟨1, by omega⟩
  let V : Submodule ℝ (Space D) := Submodule.span ℝ (Set.range (fun i => a i - a i₀))
  have hx (i : Fin s) : a i - a i₀ ∈ V := Submodule.subset_span (Set.mem_range_self i)
  let x (i : Fin s) : V := ⟨a i - a i₀, hx i⟩
  have hxspan : Submodule.span ℝ (Set.range x) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff V hx).mpr rfl
  have hpos : 0 < Module.finrank ℝ V := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨x i₁, ?_⟩
    intro he
    have hv := congrArg (fun z : V => (z : Space D)) he
    change a i₁ - a i₀ = 0 at hv
    have hi := ha (sub_eq_zero.mp hv)
    have hi' := congrArg Fin.val hi
    norm_num [i₀, i₁] at hi'
  let E := (stdOrthonormalBasis ℝ V).repr
  let b : Fin s → Space (Module.finrank ℝ V) := fun i => E (x i)
  have hbspan : Submodule.span ℝ (Set.range b) = ⊤ := by
    change Submodule.span ℝ (Set.range (E.toLinearEquiv.toLinearMap ∘ x)) = ⊤
    rw [Set.range_comp, Submodule.span_image, hxspan, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr E.surjective
  have hb0 : b i₀ = 0 := by
    change E (x i₀) = 0
    have hx0 : x i₀ = 0 := by apply Subtype.ext; exact sub_self _
    rw [hx0, map_zero]
  -- the centre: the orthogonal projection of `c − a₀` onto `V`
  let y : Space D := c - a i₀
  let py : Space D := V.starProjection y
  let p : V := ⟨py, V.starProjection_apply_mem y⟩
  let z : Space D := y - py
  refine ⟨Module.finrank ℝ V, hpos, b, ?_, ?_, ?_, E p, Real.sqrt (r ^ 2 - ‖z‖ ^ 2), ?_⟩
  · intro i j he
    have hx' := E.injective he
    have hv := congrArg (fun z : V => (z : Space D)) hx'
    change a i - a i₀ = a j - a i₀ at hv
    exact ha (sub_left_injective hv)
  · intro i j
    change dist (E (x i)) (E (x j)) = dist (a i) (a j)
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, LinearIsometryEquiv.norm_map]
    change ‖(a i - a i₀) - (a j - a i₀)‖ = ‖a i - a j‖
    rw [sub_sub_sub_cancel_right]
  · apply (AffineSubspace.direction_eq_top_iff_of_nonempty
      ⟨b i₀, subset_affineSpan ℝ (Set.range b) (Set.mem_range_self i₀)⟩).mp
    rw [direction_affineSpan, vectorSpan_range_eq_span_range_vsub_right ℝ b i₀]
    simpa only [vsub_eq_sub, hb0, sub_zero] using hbspan
  · intro i
    let w : Space D := (a i - a i₀) - py
    have hw : w ∈ V := V.sub_mem (hx i) (V.starProjection_apply_mem y)
    have horth : inner ℝ w z = 0 := by
      rw [real_inner_comm]
      exact Submodule.starProjection_inner_eq_zero (K := V) y w hw
    have h1 := norm_sub_sq_eq_norm_sq_add_norm_sq_real horth
    have h2 : w - z = a i - c := by
      change ((a i - a i₀) - py) - ((c - a i₀) - py) = a i - c
      abel
    rw [h2, ← dist_eq_norm, hr i] at h1
    have key : ‖w‖ ^ 2 = r ^ 2 - ‖z‖ ^ 2 := by nlinarith
    have hnorm : dist (b i) (E p) = ‖w‖ := by
      change dist (E (x i)) (E p) = ‖w‖
      rw [dist_eq_norm, ← map_sub, LinearIsometryEquiv.norm_map]
      rfl
    rw [hnorm, ← key, Real.sqrt_sq (norm_nonneg _)]

end

end SixConcyclic

end
