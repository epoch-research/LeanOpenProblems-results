import FormalConjecturesUtil

/-! Linear-algebra ingredients for a quantitative cap-set bound.
Development toward a restricted modeling case, not a settlement of Erdős 3. -/
namespace Erdos3CapsetSlice

open Finset

set_option maxHeartbeats 1000000

lemma exists_large_support_annihilator
    {K A I : Type*} [Field K] [DecidableEq K] [Fintype A] [Fintype I] (u : I → A → K) :
    ∃ v : A → K, (∀ i, ∑ a, v a * u i a = 0) ∧
      Fintype.card A ≤ Fintype.card I + Fintype.card {a : A // v a ≠ 0} := by
  classical
  let w : A → (I → K) := fun a i ↦ u i a
  obtain ⟨S, hS, hEmpty, hspan, hli⟩ :=
    exists_linearIndepOn_extension (K := K) (v := w)
      (s := ∅) (t := Set.univ) (by simp) (Set.empty_subset _)
  have hS_card : Fintype.card S ≤ Fintype.card I := by
    simpa using hli.fintype_card_le_finrank
  have hrange : w '' S = Set.range (fun a : S ↦ w a) := by ext x; simp
  have hw (a : A) : w a ∈ Submodule.span K (Set.range (fun a : S ↦ w a)) := by
    rw [← hrange]
    exact hspan (Set.mem_image_of_mem w (Set.mem_univ a))
  have hsum : -(∑ a, w a) ∈ Submodule.span K (Set.range (fun a : S ↦ w a)) :=
    Submodule.neg_mem _ (Submodule.sum_mem _ (fun a _ ↦ hw a))
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hsum
  let v : A → K := fun a ↦ 1 + if h : a ∈ S then c ⟨a,h⟩ else 0
  have hvsum : ∑ a, v a • w a = 0 := by
    have he : (∑ a : A, (if h : a ∈ S then c ⟨a,h⟩ else 0) • w a) =
        ∑ a : S, c a • w a := by
      have hh := Fintype.sum_subtype_add_sum_subtype (fun a : A ↦ a ∈ S)
        (fun a ↦ (if h : a ∈ S then c ⟨a,h⟩ else 0) • w a)
      have hz : (∑ a : {a : A // a ∉ S},
          (if h : (a : A) ∈ S then c ⟨a,h⟩ else 0) • w a) = 0 := by
        apply sum_eq_zero
        intro a _
        rw [dif_neg a.property, zero_smul]
      rw [hz, add_zero] at hh
      simpa using hh.symm
    simp only [v, add_smul, one_smul, sum_add_distrib]
    rw [he, hc, add_neg_cancel]
  refine ⟨v, ?_, ?_⟩
  · intro i
    have := congr_fun hvsum i
    simpa only [sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, w] using this
  · have hcard : Fintype.card A ≤ Fintype.card S +
        Fintype.card {a : A // v a ≠ 0} := by
      let e : A ↪ S ⊕ {a : A // v a ≠ 0} :=
        { toFun := fun a ↦ if ha : a ∈ S then Sum.inl ⟨a,ha⟩ else
            Sum.inr ⟨a, by simp [v, ha]⟩
          inj' := by
            intro a b he
            dsimp only at he
            by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> simp_all }
      simpa using Fintype.card_le_of_injective e e.injective
    omega

/-- A diagonal three-tensor requires at least as many slices as diagonal entries. -/
lemma diagonal_slice_lower_bound
    {K A I J L : Type*} [Field K] [Fintype A] [DecidableEq A]
    [Fintype I] [Fintype J] [Fintype L]
    (fx : I → A → K) (gx : I → A → A → K)
    (fy : J → A → K) (gy : J → A → A → K)
    (fz : L → A → K) (gz : L → A → A → K)
    (h : ∀ a b c : A, (if a = b ∧ b = c then (1 : K) else 0) =
      (∑ i, fx i a * gx i b c) + (∑ j, fy j b * gy j a c) +
        (∑ l, fz l c * gz l a b)) :
    Fintype.card A ≤ Fintype.card I + Fintype.card J + Fintype.card L := by
  classical
  obtain ⟨v, hv, hvcard⟩ := exists_large_support_annihilator fx
  let P : Matrix A (J ⊕ L) K := fun b ↦ Sum.elim (fun j ↦ fy j b)
    (fun l ↦ ∑ a, v a * gz l a b)
  let Q : Matrix (J ⊕ L) A K := Sum.elim (fun j c ↦ ∑ a, v a * gy j a c)
    (fun l c ↦ fz l c)
  have hfirst (b c : A) : (∑ a, v a * ∑ i, fx i a * gx i b c) = 0 := by
    simp_rw [mul_sum, ← mul_assoc]
    rw [sum_comm]
    simp_rw [← sum_mul, hv, zero_mul, sum_const_zero]
  have hsecond (b c : A) : (∑ a, v a * ∑ j, fy j b * gy j a c) =
      ∑ j, fy j b * ∑ a, v a * gy j a c := by
    simp_rw [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro j _
    apply sum_congr rfl
    intro a _
    ring
  have hthird (b c : A) : (∑ a, v a * ∑ l, fz l c * gz l a b) =
      ∑ l, (∑ a, v a * gz l a b) * fz l c := by
    simp_rw [mul_sum, sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro l _
    apply sum_congr rfl
    intro a _
    ring
  have hM : Matrix.diagonal v = P * Q := by
    ext b c
    calc
      Matrix.diagonal v b c = ∑ a, v a *
          (if a = b ∧ b = c then (1 : K) else 0) := by
        by_cases hbc : b = c
        · subst c
          simp
        · simp [hbc]
      _ = (P * Q) b c := by
        simp_rw [h, mul_add, sum_add_distrib]
        rw [hfirst, hsecond, hthird, zero_add]
        simp only [Matrix.mul_apply, Fintype.sum_sum_type, P, Q, Sum.elim_inl, Sum.elim_inr]
  have hr : (Matrix.diagonal v).rank ≤ Fintype.card J + Fintype.card L := by
    rw [hM]
    calc
      (P * Q).rank ≤ P.rank := Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card (J ⊕ L) := Matrix.rank_le_card_width _
      _ = _ := Fintype.card_sum
  rw [Matrix.rank_diagonal] at hr
  omega

#print axioms exists_large_support_annihilator
#print axioms diagonal_slice_lower_bound
end Erdos3CapsetSlice
