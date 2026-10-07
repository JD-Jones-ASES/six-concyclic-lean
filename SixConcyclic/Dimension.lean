module

public import SixConcyclic.Main
public import SixConcyclic.RealCert
public import SixConcyclic.Extension
public import SixConcyclic.Descent
public import SixConcyclic.Image
public import SixConcyclic.Representative
public import SixConcyclic.Rank

/-!
# The dimension theorem

A spherical set of `s` distinct points whose affine span has dimension `m` satisfies the tensor
criterion whenever `s ≤ m + 4`, in its original ambient space and coordinate field. (That the bound
is sharp for `m ≥ 2` is shown on paper in the accompanying note; no statement here says that a set
fails the criterion.) Either the
augmented vectors `(1, a_i)` admit real isolating quadrics, and the real sphere matrix lifts by
the adjugate; or a nonzero dependence among them is supported, by the rank argument, on exactly
six points that lie on a circle, while every other point adds a dimension. The six concyclic
points are certified in the plane (the six-point certificate), carried to the ambient space by
the isometric image lemma, symmetrised, and adjusted to the common sphere; the certificate then
extends point by point; and the real certificate descends to the coordinate field.
-/

@[expose] public section

namespace SixConcyclic

noncomputable section
open Matrix

/-- `qeval` is additive in the matrix. -/
theorem qeval_sub {d : ℕ} (A B : Matrix (Option (Fin d)) (Option (Fin d)) ℝ)
    (p : Option (Fin d) → ℝ) : qeval (A - B) p = qeval A p - qeval B p := by
  simp only [qeval, Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]

/-- The six-point theorem for a plane presented as `Space m` with `m = 2`. -/
theorem six_concyclic_fieldCriterion_of_dim {m : ℕ} (hm : m = 2) (b : Fin 6 → Space m)
    (hb : Function.Injective b) (hsphere : ∃ c : Space m, ∃ r : ℝ, ∀ i, dist (b i) c = r) :
    FieldCriterion b := by
  subst hm
  exact six_concyclic_fieldCriterion_internal b hb hsphere

/-- The direction of a spanning configuration of `Space m` has dimension `m`. -/
theorem finrank_vectorSpan_of_spanning {s m : ℕ} (b : Fin s → Space m)
    (hspan : affineSpan ℝ (Set.range b) = ⊤) :
    Module.finrank ℝ (vectorSpan ℝ (Set.range b)) = m := by
  rw [← direction_affineSpan, hspan, AffineSubspace.direction_top, finrank_top,
    finrank_euclideanSpace, Fintype.card_fin]

/-- Six distinct spherical points, in any space, have an affine span of dimension at least two. -/
theorem two_le_finrank_of_six {D : ℕ} (b : Fin 6 → Space D) (hb : Function.Injective b)
    (hsphere : ∃ c : Space D, ∃ r : ℝ, ∀ i, dist (b i) c = r) :
    2 ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range b)) := by
  by_contra hlt
  obtain ⟨-, b', hb'inj, -, -, hb'sph, -⟩ :=
    exists_spanning_representative' b (by norm_num) hb hsphere
  exact not_six_spherical_of_dim_le_one (by omega) b' hb'inj hb'sph

/-- Six distinct concyclic points of `Space D` (affine span of dimension two, on a sphere) have a
real certificate whose multiplied matrix is exactly the given real sphere matrix. -/
theorem realCert_six_of_planar {D : ℕ} (b : Fin 6 → Space D) (hb : Function.Injective b)
    (c : Space D) (r : ℝ) (hc : ∀ i, dist (b i) c = r)
    (h2 : Module.finrank ℝ (vectorSpan ℝ (Set.range b)) = 2) :
    RealCert (aug b) (realSphere c r) := by
  obtain ⟨-, b', hb'inj, -, -, hb'sph, T₂, t, hbt⟩ :=
    exists_spanning_representative' b (by norm_num) hb ⟨c, r, hc⟩
  have hcrit : FieldCriterion b' := six_concyclic_fieldCriterion_of_dim h2 b' hb'inj hb'sph
  obtain ⟨H₂, hR₂, hI₂⟩ := realCert_of_fieldCriterion b' hcrit
  obtain ⟨H₀, hR₀, hI₀⟩ := realCert_of_isometric_image b b' T₂ t hbt H₂ hR₂ hI₂
  have hRs := realCert_symm hR₀
  set Hs : Matrix (Option (Fin D)) (Option (Fin D)) ℝ := (2 : ℝ)⁻¹ • (H₀ + H₀ᵀ) with hHs
  have hN : (realSphere c r - Hs)ᵀ = realSphere c r - Hs := by
    rw [Matrix.transpose_sub, realSphere_transpose, hHs, Matrix.transpose_smul,
      Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  have hsp : ∀ α β : Fin D, (realSphere c r - Hs) (some α) (some β) = 0 := by
    intro α β
    rw [Matrix.sub_apply, realSphere_spatial, hHs, Matrix.smul_apply, Matrix.add_apply,
      Matrix.transpose_apply, hI₀ α β, hI₀ β α, smul_eq_mul]
    by_cases h : α = β
    · subst h; simp; norm_num
    · simp [h, Ne.symm h]
  have hv : ∀ i, qeval (realSphere c r - Hs) (aug b i) = 0 := by
    intro i
    rw [qeval_sub, qeval_realSphere, hc i, realCert_qeval hRs i]
    ring
  have := realCert_add_symm hRs (realSphere c r - Hs) hN hsp hv
  rwa [add_sub_cancel] at this

/-- The dimension theorem: a spherical set of at most `m + 4` distinct points, `m` the
dimension of its affine span, satisfies the tensor criterion. -/
theorem spherical_fieldCriterion_of_card_le_finrank_add_four_internal {s D : ℕ}
    (a : Fin s → Space D) (ha : Function.Injective a)
    (hsphere : ∃ c : Space D, ∃ r : ℝ, ∀ i, dist (a i) c = r)
    (hdim : s ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range a)) + 4) : FieldCriterion a := by
  classical
  rcases Nat.lt_or_ge s 6 with h5 | h6
  · exact at_most_five_spherical_fieldCriterion_internal a (by omega) ha hsphere
  obtain ⟨c, r, hc⟩ := hsphere
  have hH : ∀ i, qeval (realSphere c r) (aug a i) = 0 := fun i => by
    rw [qeval_realSphere, hc i]; ring
  have hrank := finrank_span_aug a (by omega)
  rcases isolators_or_dependence (aug a) with ⟨q, hq⟩ | ⟨l, hl, hdep⟩
  · exact fieldCriterion_of_realCert a _ (realCert_of_isolators (aug a) _ hH q hq)
      (realSphere_spatial c r)
  obtain ⟨T, hT6, hT3, hTrank⟩ := exists_six_of_dependence a ha c r hc l hl hdep (by omega)
  -- the six points of the support
  let e : Fin 6 ≃o T := T.orderIsoOfFin hT6
  let b : Fin 6 → Space D := fun j => a (e j)
  have hb : Function.Injective b := fun i j hij => e.injective (Subtype.ext (ha hij))
  have hbc : ∀ j, dist (b j) c = r := fun j => hc _
  have haug : ∀ j, aug b j = aug a (e j) := fun j => by
    funext α; cases α <;> rfl
  have hrange : Set.range (aug b) = aug a '' (T : Set (Fin s)) := by
    ext v
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨e j, (e j).2, (haug j).symm⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨e.symm ⟨i, hi⟩, by rw [haug, OrderIso.apply_symm_apply]⟩
  have hb2 : Module.finrank ℝ (vectorSpan ℝ (Set.range b)) = 2 := by
    have h := finrank_span_aug b (by norm_num)
    rw [hrange, hT3] at h
    omega
  have hRb : RealCert (aug b) (realSphere c r) := realCert_six_of_planar b hb c r hbc hb2
  -- reindex to the subtype
  have hRT : RealCert (fun i : T => aug a i) (realSphere c r) := by
    have h := realCert_reindex e.symm.toEquiv hRb
    convert h using 1
    funext i
    simp [Function.comp, haug]
  -- extend to every point and descend
  have hall : RealCert (aug a) (realSphere c r) :=
    realCert_of_finrank (aug a) (realSphere c r) T hRT hH (by rw [hT3, hTrank])
  exact fieldCriterion_of_realCert a _ hall (realSphere_spatial c r)

/-- Every spherical set of at most six distinct points, in any dimension and with any affine
span, satisfies the tensor criterion. -/
theorem at_most_six_spherical_fieldCriterion_internal {s d : ℕ} (a : Fin s → Space d)
    (hs : s ≤ 6) (ha : Function.Injective a)
    (hsphere : ∃ c : Space d, ∃ r : ℝ, ∀ i, dist (a i) c = r) : FieldCriterion a := by
  rcases Nat.lt_or_ge s 6 with h5 | h6
  · exact at_most_five_spherical_fieldCriterion_internal a (by omega) ha hsphere
  obtain rfl : s = 6 := le_antisymm hs h6
  exact spherical_fieldCriterion_of_card_le_finrank_add_four_internal a ha hsphere
    (by have := two_le_finrank_of_six a ha hsphere; omega)

/-- Given the sufficiency half of the classification, every spherical set of at most `m + 4`
distinct points, `m` the dimension of its affine span, is Ramsey. -/
theorem spherical_ramsey_of_sufficiency_of_card_le_finrank_add_four_internal
    (hsuff : ∀ {s d : ℕ} (a : Fin s → Space d), 2 ≤ s → 1 ≤ d → Function.Injective a →
      affineSpan ℝ (Set.range a) = ⊤ → FieldCriterion a → Ramsey a)
    {s D : ℕ} (a : Fin s → Space D) (ha : Function.Injective a)
    (hsphere : ∃ c : Space D, ∃ r : ℝ, ∀ i, dist (a i) c = r)
    (hdim : s ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range a)) + 4) : Ramsey a := by
  rcases Nat.lt_or_ge s 2 with hs2 | hs2
  · rcases Nat.lt_or_ge s 1 with hs0 | hs1
    · obtain rfl : s = 0 := by omega
      exact ramsey_empty a
    · obtain rfl : s = 1 := by omega
      exact ramsey_singleton a
  obtain ⟨hpos, b, hbinj, hcong, hspan, hbsph, -⟩ :=
    exists_spanning_representative' a hs2 ha hsphere
  have hm := finrank_vectorSpan_of_spanning b hspan
  exact ramsey_of_congruent hcong (hsuff b hs2 hpos hbinj hspan
    (spherical_fieldCriterion_of_card_le_finrank_add_four_internal b hbinj hbsph (by omega)))

end

end SixConcyclic

end
