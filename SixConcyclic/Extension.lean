module

public import SixConcyclic.RealCert
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Extension by a point outside the span

If a subset of the points is certified with multiplied matrix `H`, and a further point `b` has
its augmented vector outside the linear span of the subset's augmented vectors, then the subset
plus `b` is certified with the same `H`, provided `H` vanishes at `b`. Iterating, a certified
subset whose complement adds one dimension per point extends to the whole configuration.
-/

@[expose] public section

namespace SixConcyclic

noncomputable section
open scoped TensorProduct

/-- A linear functional on `Option (Fin d) → ℝ` as a coefficient sum. -/
theorem ext_functional_eq_sum {d : ℕ} (f : (Option (Fin d) → ℝ) →ₗ[ℝ] ℝ)
    (v : Option (Fin d) → ℝ) :
    f v = ∑ α, f (fun j => if α = j then 1 else 0) * v α := by
  rw [LinearMap.pi_apply_eq_sum_univ]
  exact Finset.sum_congr rfl fun α _ => by rw [smul_eq_mul, mul_comm]

/-- The sandwich of a rank-one correction `P − z · (ℓ ⊗ 1)(1 ⊗ ℓ)ᵀ`. -/
theorem ext_sandwich_sub {d : ℕ} (P : Matrix (Option (Fin d)) (Option (Fin d)) RT) (z : RT)
    (l x : Option (Fin d) → ℝ) :
    ∑ α, ∑ β, ιl (x α) * (P α β - z * ιl (l α) * ιr (l β)) * ιr (x β) =
      (∑ α, ∑ β, ιl (x α) * P α β * ιr (x β)) -
        z * ιl (∑ α, l α * x α) * ιr (∑ β, l β * x β) := by
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, map_sum, map_mul, Finset.mul_sum,
    Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  ring

/-- Adding a vector outside the span raises the dimension of the span by one. -/
theorem ext_finrank_span_insert {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (S : Set V) (x : V) (hx : x ∉ Submodule.span ℝ S) :
    Module.finrank ℝ (Submodule.span ℝ (insert x S)) =
      Module.finrank ℝ (Submodule.span ℝ S) + 1 := by
  have hx0 : x ≠ 0 := fun h => hx (h ▸ Submodule.zero_mem _)
  rw [Submodule.span_insert]
  have h := Submodule.finrank_sup_add_finrank_inf_eq (ℝ ∙ x) (Submodule.span ℝ S)
  have hinf : (ℝ ∙ x) ⊓ Submodule.span ℝ S = ⊥ := by
    rw [inf_comm]
    exact ((Submodule.disjoint_span_singleton' hx0).mpr hx).eq_bot
  rw [hinf, finrank_bot, finrank_span_singleton hx0] at h
  omega

/-- Adding a point outside the linear span of the others' augmented vectors: with a linear
functional `ℓ` on `ℝ^{d+1}` vanishing on the old augmented vectors and `ℓ(p_b) = 1`, and `z` the
sandwich of the old certificate at `p_b`, the matrix `P − z · (ℓ ⊗ 1)(1 ⊗ ℓ)ᵀ` has sandwich
`0 − z · ℓ(p_i) ⊗ ℓ(p_i) = 0` at the old points and `z − z · 1 ⊗ 1 = 0` at `b`, and
`μ z = qeval H p_b = 0` keeps the multiplied matrix. -/
theorem realCert_insert {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (p : ι → Option (Fin d) → ℝ) (H : Matrix (Option (Fin d)) (Option (Fin d)) ℝ)
    (T : Finset ι) (hT : RealCert (fun i : T => p i) H) (b : ι)
    (hb : p b ∉ Submodule.span ℝ (p '' (T : Set ι))) (hHb : qeval H (p b) = 0) :
    RealCert (fun i : (insert b T : Finset ι) => p i) H := by
  obtain ⟨P, hP, hPH⟩ := hT
  obtain ⟨f, hfb, hker⟩ := Submodule.exists_le_ker_of_notMem hb
  set g := (f (p b))⁻¹ • f with hg
  have hgb : g (p b) = 1 := by
    rw [hg, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hfb]
  have hgT : ∀ i ∈ T, g (p i) = 0 := fun i hi => by
    have hm : p i ∈ Submodule.span ℝ (p '' (T : Set ι)) := Submodule.subset_span ⟨i, hi, rfl⟩
    rw [hg, LinearMap.smul_apply, LinearMap.mem_ker.mp (hker hm), smul_zero]
  set l : Option (Fin d) → ℝ := fun α => g (fun j => if α = j then 1 else 0) with hl
  have hgl : ∀ v, g v = ∑ α, l α * v α := fun v => ext_functional_eq_sum g v
  set z : RT := ∑ α, ∑ β, ιl (p b α) * P α β * ιr (p b β) with hz
  have hPH' : ∀ α β, μr (P α β) = H α β := fun α β => by
    rw [← hPH, Matrix.map_apply]
  have hz0 : μr z = 0 := by
    rw [← hHb, hz, qeval]
    simp only [map_sum, map_mul, μr_ιl, μr_ιr, hPH']
  refine ⟨Matrix.of fun α β => P α β - z * ιl (l α) * ιr (l β), ?_, ?_⟩
  · rintro ⟨i, hi⟩
    simp only [Matrix.of_apply]
    rw [ext_sandwich_sub, ← hgl]
    rcases Finset.mem_insert.mp hi with rfl | hiT
    · rw [hgb, map_one, map_one, mul_one, mul_one, sub_self]
    · rw [hgT i hiT, map_zero, mul_zero, zero_mul, sub_zero]
      exact hP ⟨i, hiT⟩
  · ext α β
    rw [Matrix.map_apply, Matrix.of_apply, map_sub, map_mul, map_mul, hz0, zero_mul, zero_mul, sub_zero]
    exact hPH' α β

/-- Iterated extension: if the augmented vectors of the complement of `T` add one dimension each
(the rank of all equals the rank of `T` plus the size of the complement), a certificate of `T`
with multiplied matrix `H` vanishing at every point extends to the whole configuration.
Induction on the complement: some `b ∉ T` has `p b` outside the span of `p '' T` (otherwise the
rank bound fails), `insert b T` is certified by `realCert_insert`, and its complement is smaller. -/
theorem realCert_of_finrank {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (p : ι → Option (Fin d) → ℝ) (H : Matrix (Option (Fin d)) (Option (Fin d)) ℝ)
    (T : Finset ι) (hT : RealCert (fun i : T => p i) H) (hH : ∀ i, qeval H (p i) = 0)
    (hrank : Module.finrank ℝ (Submodule.span ℝ (Set.range p)) =
      Module.finrank ℝ (Submodule.span ℝ (p '' (T : Set ι))) + Tᶜ.card) :
    RealCert p H := by
  obtain ⟨n, hn⟩ : ∃ n, Tᶜ.card = n := ⟨_, rfl⟩
  induction n generalizing T with
  | zero =>
    have hTu : T = Finset.univ := by
      rw [Finset.card_eq_zero, Finset.compl_eq_empty_iff] at hn
      exact hn
    obtain ⟨P, hP, hPH⟩ := hT
    exact ⟨P, fun i => hP ⟨i, by simp [hTu]⟩, hPH⟩
  | succ n ih =>
    have hex : ∃ b, b ∉ T ∧ p b ∉ Submodule.span ℝ (p '' (T : Set ι)) := by
      by_contra hne
      simp only [not_exists, not_and, not_not] at hne
      have hle : Submodule.span ℝ (Set.range p) ≤ Submodule.span ℝ (p '' (T : Set ι)) := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        by_cases hi : i ∈ T
        · exact Submodule.subset_span ⟨i, hi, rfl⟩
        · exact hne i hi
      have hge : Submodule.span ℝ (p '' (T : Set ι)) ≤ Submodule.span ℝ (Set.range p) :=
        Submodule.span_mono (Set.image_subset_range _ _)
      rw [le_antisymm hle hge] at hrank
      omega
    obtain ⟨b, hbT, hb⟩ := hex
    have hins := realCert_insert p H T hT b hb (hH b)
    have hcard : (insert b T)ᶜ.card = n := by
      have h1 := Finset.card_compl (insert b T)
      have h2 := Finset.card_compl T
      have h3 := Finset.card_insert_of_notMem hbT
      have h4 := Finset.card_le_univ (insert b T)
      omega
    refine ih (insert b T) hins ?_ hcard
    rw [Finset.coe_insert, Set.image_insert_eq, ext_finrank_span_insert _ _ hb, hrank, hn,
      hcard]
    omega

end

end SixConcyclic

end
