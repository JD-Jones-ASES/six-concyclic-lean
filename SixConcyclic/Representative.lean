module

public import SixConcyclic.RealCert
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# The spanning representative, with the map back; the rank of the augmented vectors

`exists_spanning_representative'` is the construction of `Transport.lean` (translate by `a₀`,
take the direction `V = vectorSpan ℝ (Set.range a)`, map `V` isometrically onto
`Space (finrank V)` by `E = (stdOrthonormalBasis ℝ V).repr`, carry the sphere's centre along by
orthogonal projection) with the isometric affine map back exposed: `a_i = a₀ + T (b_i)` with
`T = V.subtypeₗᵢ ∘ E.symm`, a linear isometry `Space (finrank V) → Space D`.

`finrank_span_aug`: the augmented vectors `(1, a_i)` span `finrank V + 1` dimensions. The
projection to the constant coordinate maps their span onto `ℝ` (the configuration is nonempty),
and its kernel is `{(0, v) : v ∈ V}`: a combination `∑ c_i (1, a_i)` with `∑ c_i = 0` is
`(0, ∑ c_i (a_i − a₀))`, and conversely `(0, a_i − a_j) = (1, a_i) − (1, a_j)`.
-/

@[expose] public section

namespace SixConcyclic

noncomputable section

/-- The embedding `v ↦ (0, v)` of `Space d` into the augmented coordinates. -/
def repAugEmbed (d : ℕ) : Space d →ₗ[ℝ] (Option (Fin d) → ℝ) where
  toFun v α := Option.elim α 0 (fun k => v k)
  map_add' v w := by
    funext α
    cases α <;> simp
  map_smul' t v := by
    funext α
    cases α <;> simp

theorem repAugEmbed_injective (d : ℕ) : Function.Injective (repAugEmbed d) := by
  intro v w h
  ext k
  exact congrFun h (some k)

/-- Every spherical configuration of at least two distinct points is `t + T b` for a linear
isometry `T` from `Space (finrank ℝ (vectorSpan ℝ (Set.range a)))`, where `b` is injective,
congruent to `a`, affinely spanning, and spherical; and that dimension is positive. -/
theorem exists_spanning_representative' {s D : ℕ} (a : Fin s → Space D) (hs : 2 ≤ s)
    (ha : Function.Injective a) (hsphere : ∃ c : Space D, ∃ r : ℝ, ∀ i, dist (a i) c = r) :
    1 ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range a)) ∧
    ∃ b : Fin s → Space (Module.finrank ℝ (vectorSpan ℝ (Set.range a))),
      Function.Injective b ∧ Congruent a b ∧ affineSpan ℝ (Set.range b) = ⊤ ∧
      (∃ c : Space (Module.finrank ℝ (vectorSpan ℝ (Set.range a))), ∃ r : ℝ,
        ∀ i, dist (b i) c = r) ∧
      ∃ (T : Space (Module.finrank ℝ (vectorSpan ℝ (Set.range a))) →ₗᵢ[ℝ] Space D)
        (t : Space D), ∀ i, a i = t + T (b i) := by
  classical
  obtain ⟨c, r, hr⟩ := hsphere
  let i₀ : Fin s := ⟨0, by omega⟩
  let i₁ : Fin s := ⟨1, by omega⟩
  let V : Submodule ℝ (Space D) := vectorSpan ℝ (Set.range a)
  have hx (i : Fin s) : a i - a i₀ ∈ V :=
    vsub_mem_vectorSpan ℝ (Set.mem_range_self i) (Set.mem_range_self i₀)
  let x (i : Fin s) : V := ⟨a i - a i₀, hx i⟩
  have hxspan : Submodule.span ℝ (Set.range x) = ⊤ := by
    refine (Submodule.span_range_subtype_eq_top_iff V hx).mpr ?_
    exact (vectorSpan_range_eq_span_range_vsub_right ℝ a i₀).symm
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
  let T : Space (Module.finrank ℝ V) →ₗᵢ[ℝ] Space D :=
    V.subtypeₗᵢ.comp E.symm.toLinearIsometry
  refine ⟨hpos, b, ?_, ?_, ?_, ⟨E p, Real.sqrt (r ^ 2 - ‖z‖ ^ 2), ?_⟩, T, a i₀, ?_⟩
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
  · intro i
    have hT : T (b i) = a i - a i₀ := by
      change ((E.symm (E (x i)) : V) : Space D) = a i - a i₀
      rw [LinearIsometryEquiv.symm_apply_apply]
    rw [hT, add_sub_cancel]

/-- The augmented vectors of a nonempty configuration span one dimension more than the direction
of its affine span. -/
theorem finrank_span_aug {s d : ℕ} (a : Fin s → Space d) (hs : 1 ≤ s) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range (aug a))) =
      Module.finrank ℝ (vectorSpan ℝ (Set.range a)) + 1 := by
  classical
  let i₀ : Fin s := ⟨0, by omega⟩
  let j := repAugEmbed d
  let A : Submodule ℝ (Option (Fin d) → ℝ) := Submodule.span ℝ {aug a i₀}
  let B : Submodule ℝ (Option (Fin d) → ℝ) := (vectorSpan ℝ (Set.range a)).map j
  have hdecomp (i : Fin s) : aug a i = aug a i₀ + j (a i - a i₀) := by
    funext α
    cases α with
    | none => simp [j, repAugEmbed, aug]
    | some k => simp [j, repAugEmbed, aug]
  have hW : Submodule.span ℝ (Set.range (aug a)) = A ⊔ B := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [hdecomp i]
      refine Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.subset_span rfl))
        (Submodule.mem_sup_right ?_)
      exact Submodule.mem_map_of_mem
        (vsub_mem_vectorSpan ℝ (Set.mem_range_self i) (Set.mem_range_self i₀))
    · refine sup_le ?_ ?_
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        exact Submodule.subset_span (Set.mem_range_self i₀)
      · change (vectorSpan ℝ (Set.range a)).map j ≤ _
        rw [vectorSpan_range_eq_span_range_vsub_right ℝ a i₀, Submodule.map_span,
          Submodule.span_le]
        rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
        have h : j (a i -ᵥ a i₀) = aug a i - aug a i₀ := by
          rw [hdecomp i]
          simp
        rw [SetLike.mem_coe, h]
        exact Submodule.sub_mem _ (Submodule.subset_span (Set.mem_range_self i))
          (Submodule.subset_span (Set.mem_range_self i₀))
  have hinf : A ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hvA, hvB⟩
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hvA
    obtain ⟨u, -, hu⟩ := Submodule.mem_map.mp hvB
    have h0 := congrFun hu none
    simp [j, repAugEmbed, aug] at h0
    rw [Submodule.mem_bot, ← h0, zero_smul]
  have hne : aug a i₀ ≠ 0 := by
    intro h
    have h1 := congrFun h none
    simp [aug] at h1
  have hA : Module.finrank ℝ A = 1 := finrank_span_singleton hne
  have hB : Module.finrank ℝ B = Module.finrank ℝ (vectorSpan ℝ (Set.range a)) :=
    (Submodule.equivMapOfInjective j (repAugEmbed_injective d) _).finrank_eq.symm
  have key := Submodule.finrank_sup_add_finrank_inf_eq A B
  rw [hinf, finrank_bot, add_zero, ← hW, hA, hB] at key
  rw [key, add_comm]

end

end SixConcyclic

end
