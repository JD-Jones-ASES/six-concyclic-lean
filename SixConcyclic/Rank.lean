module

public import SixConcyclic.RealCert
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# The rank argument

`isolators_or_dependence`: the real evaluation map `Q ↦ (p_jᵀ Q p_j)_j` on `(d+1) × (d+1)`
matrices is either surjective, in which case the preimages of the unit vectors are isolating
quadrics, or its range is annihilated by a nonzero functional `l` (`Submodule.exists_le_ker_of_notMem`
at a vector outside the range), and then `∑ l_j ⟨p_j, w⟩² = l (Q ↦ p_jᵀ Q p_j)(w wᵀ) = 0` for
every `w`.

`exists_six_of_dependence`: let `U = {l > 0}`, `V = {l < 0}`, both nonempty (if `V = ∅` then
`⟨p_i, w⟩ = 0` for all `i ∈ U` and all `w`, but `p_i ≠ 0`). A vector `w` orthogonal to every
`p_i`, `i ∈ U`, has `∑_V (−l_i) ⟨p_i, w⟩² = 0`, so is orthogonal to every `p_i`, `i ∈ V`; hence
`span (p '' U) = span (p '' V) =: R` (double orthogonal complement in
`EuclideanSpace ℝ (Option (Fin D))`), of rank `r ≤ min |U| |V|`. Distinct spherical points whose
augmented vectors lie in a space of rank `≤ 2` are at most two (a third would be
`a_i + β (a_j − a_i)` with `β(β − 1) |a_j − a_i|² = 0`), and `|U| = |V| = 1` would force
`a_u = a_v`; so `r ≥ 3`. The span of all augmented vectors is contained in
`R ⊔ span (p '' (U ∪ V)ᶜ)`, so `rank ≤ r + s − |U| − |V|`; with `s ≤ rank + 3` this gives
`|U| + |V| ≤ r + 3 ≤ |U| + |V|`, whence `|U| = |V| = r = 3`, `T = U ∪ V` has six elements,
`span (p '' T) = R` has rank `3`, and `rank = 3 + |Tᶜ|`.

In the Lean proof the double orthogonal complement is replaced by a separating functional
(`rank_mem_span_of_dep`), and three distinct sphere points are shown independent by the
distance identities `y |AB|² + z |AC|² = 0` etc. (`rank_three_indep`).
-/

@[expose] public section

namespace SixConcyclic

noncomputable section
open Module

/-- A linear functional on `n → ℝ` in coordinates. -/
theorem rank_functional_eq_sum {n : Type*} [Fintype n] [DecidableEq n]
    (f : (n → ℝ) →ₗ[ℝ] ℝ) (x : n → ℝ) :
    f x = ∑ α, x α * f (fun j => if α = j then 1 else 0) := by
  rw [LinearMap.pi_apply_eq_sum_univ f x]
  simp only [smul_eq_mul]

/-- The quadratic evaluation of `w wᵀ` is `⟨x, w⟩²`. -/
theorem rank_qeval_vecMulVec {d : ℕ} (w x : Option (Fin d) → ℝ) :
    qeval (Matrix.vecMulVec w w) x = (∑ α, x α * w α) ^ 2 := by
  rw [sq, Finset.sum_mul_sum]
  unfold qeval
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  rw [Matrix.vecMulVec_apply]
  ring

/-- The real evaluation map `Q ↦ (p_jᵀ Q p_j)_j`. -/
def rankEval {ι : Type*} {d : ℕ} (p : ι → Option (Fin d) → ℝ) :
    Matrix (Option (Fin d)) (Option (Fin d)) ℝ →ₗ[ℝ] (ι → ℝ) where
  toFun Q j := qeval Q (p j)
  map_add' Q Q' := by
    funext j
    simp only [qeval, Matrix.add_apply, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' t Q := by
    funext j
    simp only [qeval, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, Pi.smul_apply,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => by ring

theorem rankEval_apply {ι : Type*} {d : ℕ} (p : ι → Option (Fin d) → ℝ)
    (Q : Matrix (Option (Fin d)) (Option (Fin d)) ℝ) (j : ι) :
    rankEval p Q j = qeval Q (p j) := rfl

/-- Either every point has a real isolating quadric, or a nonzero weight vector `l` satisfies
`∑ l_i ⟨p_i, w⟩² = 0` for every `w`. -/
theorem isolators_or_dependence {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (p : ι → Option (Fin d) → ℝ) :
    (∃ q : ι → Matrix (Option (Fin d)) (Option (Fin d)) ℝ,
        ∀ i j, qeval (q i) (p j) = if i = j then 1 else 0) ∨
      ∃ l : ι → ℝ, l ≠ 0 ∧ ∀ w : Option (Fin d) → ℝ, ∑ i, l i * (∑ α, p i α * w α) ^ 2 = 0 := by
  by_cases hs : Function.Surjective (rankEval p)
  · left
    choose q hq using fun i => hs (fun j => if i = j then (1 : ℝ) else 0)
    exact ⟨q, fun i j => congrFun (hq i) j⟩
  · right
    obtain ⟨v, hv⟩ := not_forall.mp hs
    have hv' : v ∉ LinearMap.range (rankEval p) := fun h => hv (LinearMap.mem_range.mp h)
    obtain ⟨f, hfv, hle⟩ := Submodule.exists_le_ker_of_notMem hv'
    refine ⟨fun i => f (fun j => if i = j then 1 else 0), ?_, fun w => ?_⟩
    · intro hl
      apply hfv
      rw [rank_functional_eq_sum f v]
      exact Finset.sum_eq_zero fun i _ => by rw [congrFun hl i, Pi.zero_apply, mul_zero]
    · have h0 : f (rankEval p (Matrix.vecMulVec w w)) = 0 :=
        LinearMap.mem_ker.mp (hle (LinearMap.mem_range_self _ _))
      rw [rank_functional_eq_sum f] at h0
      refine (Finset.sum_congr rfl fun i _ => ?_).trans h0
      simp only [rankEval_apply, rank_qeval_vecMulVec]
      ring

/-- A point of negative weight lies in the span of any set containing the points of positive
weight. -/
theorem rank_mem_span_of_dep {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
    (p : ι → n → ℝ) (l : ι → ℝ)
    (hdep : ∀ w : n → ℝ, ∑ i, l i * (∑ α, p i α * w α) ^ 2 = 0)
    (S : Set ι) (hS : ∀ i, 0 < l i → i ∈ S) (v : ι) (hv : l v < 0) :
    p v ∈ Submodule.span ℝ (p '' S) := by
  by_contra h
  obtain ⟨f, hfv, hle⟩ := Submodule.exists_le_ker_of_notMem h
  have key : ∑ i, l i * f (p i) ^ 2 = 0 := by
    rw [← hdep (fun α => f (fun j => if α = j then 1 else 0))]
    exact Finset.sum_congr rfl fun i _ => by rw [rank_functional_eq_sum f (p i)]
  have hnp : ∀ i ∈ Finset.univ, l i * f (p i) ^ 2 ≤ 0 := by
    intro i _
    by_cases hi : 0 < l i
    · have : f (p i) = 0 :=
        LinearMap.mem_ker.mp (hle (Submodule.subset_span ⟨i, hS i hi, rfl⟩))
      rw [this]
      simp
    · nlinarith [sq_nonneg (f (p i))]
  have hv0 := (Finset.sum_eq_zero_iff_of_nonpos hnp).mp key v (Finset.mem_univ _)
  have hpos : 0 < f (p v) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hfv))
  nlinarith

/-- The span of the image of a finset has rank at most its cardinality. -/
theorem rank_finrank_span_le {ι n : Type*} (p : ι → n → ℝ) (S : Finset ι) :
    finrank ℝ (Submodule.span ℝ (p '' (S : Set ι))) ≤ S.card := by
  classical
  have h := finrank_span_finset_le_card (R := ℝ) (S.image p)
  rw [Finset.coe_image] at h
  exact h.trans Finset.card_image_le

/-- Three distinct points of a sphere are affinely independent: a vanishing combination with
vanishing coefficient sum is trivial. -/
theorem rank_three_indep {D : ℕ} {A B C c : Space D} {r : ℝ} (hA : dist A c = r)
    (hB : dist B c = r) (hC : dist C c = r) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    {x y z : ℝ} (h0 : x + y + z = 0) (h1 : x • A + y • B + z • C = 0) :
    x = 0 ∧ y = 0 ∧ z = 0 := by
  set A' := A - c with hA'
  set B' := B - c with hB'
  set C' := C - c with hC'
  have h1' : x • A' + y • B' + z • C' = 0 := by
    have : x • A' + y • B' + z • C' = (x • A + y • B + z • C) - (x + y + z) • c := by
      simp only [hA', hB', hC', smul_sub, add_smul]
      abel
    rw [this, h1, h0, zero_smul, sub_zero]
  have nA : inner ℝ A' A' = r ^ 2 := by rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, hA]
  have nB : inner ℝ B' B' = r ^ 2 := by rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, hB]
  have nC : inner ℝ C' C' = r ^ 2 := by rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, hC]
  have dAB : ‖A - B‖ ^ 2 = 2 * r ^ 2 - 2 * inner ℝ A' B' := by
    rw [show A - B = A' - B' by simp [hA', hB'], norm_sub_sq_real, ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq, nA, nB]
    ring
  have dAC : ‖A - C‖ ^ 2 = 2 * r ^ 2 - 2 * inner ℝ A' C' := by
    rw [show A - C = A' - C' by simp [hA', hC'], norm_sub_sq_real, ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq, nA, nC]
    ring
  have dBC : ‖B - C‖ ^ 2 = 2 * r ^ 2 - 2 * inner ℝ B' C' := by
    rw [show B - C = B' - C' by simp [hB', hC'], norm_sub_sq_real, ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq, nB, nC]
    ring
  have eA := congrArg (fun v => inner ℝ v A') h1'
  have eB := congrArg (fun v => inner ℝ v B') h1'
  have eC := congrArg (fun v => inner ℝ v C') h1'
  simp only [inner_add_left, real_inner_smul_left, inner_zero_left] at eA eB eC
  rw [nA, real_inner_comm A' B', real_inner_comm A' C'] at eA
  rw [nB, real_inner_comm B' C'] at eB
  rw [nC] at eC
  have pAB : 0 < ‖A - B‖ ^ 2 := by
    have := norm_pos_iff.mpr (sub_ne_zero.mpr hAB)
    positivity
  have pAC : 0 < ‖A - C‖ ^ 2 := by
    have := norm_pos_iff.mpr (sub_ne_zero.mpr hAC)
    positivity
  have pBC : 0 < ‖B - C‖ ^ 2 := by
    have := norm_pos_iff.mpr (sub_ne_zero.mpr hBC)
    positivity
  have q1 : y * ‖A - B‖ ^ 2 + z * ‖A - C‖ ^ 2 = 0 := by
    rw [dAB, dAC]
    linear_combination 2 * r ^ 2 * h0 - 2 * eA
  have q2 : x * ‖A - B‖ ^ 2 + z * ‖B - C‖ ^ 2 = 0 := by
    rw [dAB, dBC]
    linear_combination 2 * r ^ 2 * h0 - 2 * eB
  have q3 : x * ‖A - C‖ ^ 2 + y * ‖B - C‖ ^ 2 = 0 := by
    rw [dAC, dBC]
    linear_combination 2 * r ^ 2 * h0 - 2 * eC
  have hx : x * (2 * ‖A - B‖ ^ 2 * ‖A - C‖ ^ 2) = 0 := by
    linear_combination ‖A - C‖ ^ 2 * q2 + ‖A - B‖ ^ 2 * q3 - ‖B - C‖ ^ 2 * q1
  have hy : y * (2 * ‖A - B‖ ^ 2 * ‖B - C‖ ^ 2) = 0 := by
    linear_combination ‖B - C‖ ^ 2 * q1 + ‖A - B‖ ^ 2 * q3 - ‖A - C‖ ^ 2 * q2
  have hz : z * (2 * ‖A - C‖ ^ 2 * ‖B - C‖ ^ 2) = 0 := by
    linear_combination ‖B - C‖ ^ 2 * q1 + ‖A - C‖ ^ 2 * q2 - ‖A - B‖ ^ 2 * q3
  refine ⟨?_, ?_, ?_⟩
  · exact (mul_eq_zero.mp hx).resolve_right (by positivity)
  · exact (mul_eq_zero.mp hy).resolve_right (by positivity)
  · exact (mul_eq_zero.mp hz).resolve_right (by positivity)

/-- The augmented vectors of three distinct points of a sphere span three dimensions. -/
theorem rank_three_le {s D : ℕ} (a : Fin s → Space D) (ha : Function.Injective a) (c : Space D)
    (r : ℝ) (hc : ∀ i, dist (a i) c = r) {i j k : Fin s} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (S : Submodule ℝ (Option (Fin D) → ℝ)) (hi : aug a i ∈ S) (hj : aug a j ∈ S)
    (hk : aug a k ∈ S) : 3 ≤ finrank ℝ S := by
  have hli : LinearIndependent ℝ ![aug a i, aug a j, aug a k] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_three] at hg
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at hg
    have h0 : g 0 + g 1 + g 2 = 0 := by
      have := congrFun hg none
      simpa [aug_none] using this
    have h1 : g 0 • a i + g 1 • a j + g 2 • a k = 0 := by
      refine PiLp.ext fun m => ?_
      have := congrFun hg (some m)
      simpa [aug_some] using this
    obtain ⟨x0, y0, z0⟩ := rank_three_indep (hc i) (hc j) (hc k) (ha.ne hij) (ha.ne hik)
      (ha.ne hjk) h0 h1
    intro t
    fin_cases t
    · exact x0
    · exact y0
    · exact z0
  calc 3 = Fintype.card (Fin 3) := (Fintype.card_fin 3).symm
    _ = finrank ℝ (Submodule.span ℝ (Set.range ![aug a i, aug a j, aug a k])) :=
        (finrank_span_eq_card hli).symm
    _ ≤ finrank ℝ S := Submodule.finrank_mono ?_
  rw [Submodule.span_le]
  rintro _ ⟨t, rfl⟩
  fin_cases t
  · exact hi
  · exact hj
  · exact hk

/-- A dependence forces the weights to sum to zero (take `w = e_none`). -/
theorem rank_sum_eq_zero {s D : ℕ} (a : Fin s → Space D) (l : Fin s → ℝ)
    (hdep : ∀ w : Option (Fin D) → ℝ, ∑ i, l i * (∑ α, aug a i α * w α) ^ 2 = 0) :
    ∑ i, l i = 0 := by
  have := hdep (fun α => if α = none then 1 else 0)
  simpa [Fintype.sum_option, aug_none] using this

/-- A nonzero dependence among the augmented vectors of distinct spherical points, when the
number of points is at most the rank of the augmented vectors plus three, is supported on exactly
six points whose augmented vectors span three dimensions, and the remaining points add one
dimension each. -/
theorem exists_six_of_dependence {s D : ℕ} (a : Fin s → Space D) (ha : Function.Injective a)
    (c : Space D) (r : ℝ) (hc : ∀ i, dist (a i) c = r) (l : Fin s → ℝ) (hl : l ≠ 0)
    (hdep : ∀ w : Option (Fin D) → ℝ, ∑ i, l i * (∑ α, aug a i α * w α) ^ 2 = 0)
    (hdim : s ≤ Module.finrank ℝ (Submodule.span ℝ (Set.range (aug a))) + 3) :
    ∃ T : Finset (Fin s), T.card = 6 ∧
      Module.finrank ℝ (Submodule.span ℝ (aug a '' (T : Set (Fin s)))) = 3 ∧
      Module.finrank ℝ (Submodule.span ℝ (Set.range (aug a))) = 3 + Tᶜ.card := by
  classical
  obtain ⟨U, hU⟩ : ∃ U : Finset (Fin s), U = Finset.univ.filter (fun i => 0 < l i) := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V : Finset (Fin s), V = Finset.univ.filter (fun i => l i < 0) := ⟨_, rfl⟩
  have memU : ∀ i, i ∈ U ↔ 0 < l i := fun i => by simp [hU]
  have memV : ∀ i, i ∈ V ↔ l i < 0 := fun i => by simp [hV]
  obtain ⟨R, hR⟩ : ∃ R : Submodule ℝ (Option (Fin D) → ℝ),
      R = Submodule.span ℝ (aug a '' (U : Set (Fin s))) := ⟨_, rfl⟩
  have hVU : ∀ v ∈ V, aug a v ∈ R := fun v hv => hR ▸
    rank_mem_span_of_dep (aug a) l hdep (U : Set (Fin s))
      (fun i hi => Finset.mem_coe.mpr ((memU i).mpr hi)) v ((memV v).mp hv)
  have hdep' : ∀ w : Option (Fin D) → ℝ, ∑ i, (-l) i * (∑ α, aug a i α * w α) ^ 2 = 0 := by
    intro w
    simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, hdep w, neg_zero]
  have hUV : ∀ u ∈ U, aug a u ∈ Submodule.span ℝ (aug a '' (V : Set (Fin s))) := fun u hu =>
    rank_mem_span_of_dep (aug a) (-l) hdep' (V : Set (Fin s))
      (fun i hi => Finset.mem_coe.mpr ((memV i).mpr (by simp only [Pi.neg_apply] at hi; linarith)))
      u (by simp only [Pi.neg_apply]; linarith [(memU u).mp hu])
  have hRV : Submodule.span ℝ (aug a '' (V : Set (Fin s))) = R := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨v, hv, rfl⟩
      exact hVU v hv
    · rw [hR, Submodule.span_le]
      rintro _ ⟨u, hu, rfl⟩
      exact hUV u hu
  have hRT : Submodule.span ℝ (aug a '' ((U ∪ V : Finset (Fin s)) : Set (Fin s))) = R := by
    rw [Finset.coe_union, Set.image_union, Submodule.span_union, hRV, ← hR, sup_idem]
  have hsum := rank_sum_eq_zero a l hdep
  have hUne : U.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hle : ∀ i, l i ≤ 0 := fun i => by
      by_contra hi
      have : i ∈ U := (memU i).mpr (lt_of_not_ge hi)
      simp [h] at this
    apply hl
    funext i
    exact (Finset.sum_eq_zero_iff_of_nonpos (fun i _ => hle i)).mp hsum i (Finset.mem_univ _)
  have hVne : V.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hle : ∀ i, 0 ≤ l i := fun i => by
      by_contra hi
      have : i ∈ V := (memV i).mpr (lt_of_not_ge hi)
      simp [h] at this
    apply hl
    funext i
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hle i)).mp hsum i (Finset.mem_univ _)
  have hdisj : Disjoint U V := by
    rw [Finset.disjoint_left]
    intro i hiU hiV
    have := (memU i).mp hiU
    have := (memV i).mp hiV
    linarith
  have hTcard : (U ∪ V).card = U.card + V.card := Finset.card_union_of_disjoint hdisj
  have hrU : finrank ℝ R ≤ U.card := hR ▸ rank_finrank_span_le (aug a) U
  have hrV : finrank ℝ R ≤ V.card := hRV ▸ rank_finrank_span_le (aug a) V
  have hr3 : 3 ≤ finrank ℝ R := by
    by_cases h2 : 2 < (U ∪ V).card
    · obtain ⟨i, j, k, hi, hj, hk, hij, hik, hjk⟩ := Finset.two_lt_card_iff.mp h2
      have mem : ∀ t ∈ U ∪ V, aug a t ∈ R := fun t ht =>
        hRT ▸ Submodule.subset_span ⟨t, Finset.mem_coe.mpr ht, rfl⟩
      exact rank_three_le a ha c r hc hij hik hjk R (mem i hi) (mem j hj) (mem k hk)
    · exfalso
      have hU1 : U.card = 1 := by
        have := hUne.card_pos
        have := hVne.card_pos
        omega
      have hV1 : V.card = 1 := by
        have := hUne.card_pos
        have := hVne.card_pos
        omega
      obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hU1
      obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hV1
      have hvR : aug a v ∈ R := hVU v (by simp [hv])
      rw [hR, hu, Finset.coe_singleton, Set.image_singleton] at hvR
      obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hvR
      have ht1 : t = 1 := by
        have := congrFun ht none
        simpa [aug_none] using this
      have huv : u ≠ v := by
        intro h
        have h1 : u ∈ U := by simp [hu]
        have h2 : u ∈ V := by simp [hv, h]
        exact Finset.disjoint_left.mp hdisj h1 h2
      apply huv
      apply ha
      refine PiLp.ext fun m => ?_
      have := congrFun ht (some m)
      simp only [ht1, one_smul, aug_some] at this
      exact this
  have hZ : Submodule.span ℝ (Set.range (aug a)) ≤
      R ⊔ Submodule.span ℝ (aug a '' (((U ∪ V)ᶜ : Finset (Fin s)) : Set (Fin s))) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    by_cases hi : i ∈ U ∪ V
    · exact Submodule.mem_sup_left (hRT ▸ Submodule.subset_span ⟨i, Finset.mem_coe.mpr hi, rfl⟩)
    · exact Submodule.mem_sup_right
        (Submodule.subset_span ⟨i, Finset.mem_coe.mpr (Finset.mem_compl.mpr hi), rfl⟩)
  have hrank : finrank ℝ (Submodule.span ℝ (Set.range (aug a))) ≤
      finrank ℝ R + (U ∪ V)ᶜ.card :=
    (Submodule.finrank_mono hZ).trans ((Submodule.finrank_add_le_finrank_add_finrank _ _).trans
      (Nat.add_le_add_left (rank_finrank_span_le (aug a) (U ∪ V)ᶜ) _))
  have hcompl : (U ∪ V)ᶜ.card = s - (U ∪ V).card := by
    rw [Finset.card_compl, Fintype.card_fin]
  have hTle : (U ∪ V).card ≤ s := by
    simpa using Finset.card_le_univ (U ∪ V)
  refine ⟨U ∪ V, by omega, by rw [hRT]; omega, by omega⟩

end

end SixConcyclic

end
