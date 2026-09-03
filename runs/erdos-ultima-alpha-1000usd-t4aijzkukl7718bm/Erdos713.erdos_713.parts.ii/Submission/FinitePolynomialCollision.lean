import FormalConjecturesUtil

/-! A finite-field obstruction for a polynomial that is injective away from its zero fiber. -/
open Finset Polynomial
namespace FinitePolynomialCollision

lemma sum_eval_eq_zero {F : Type*} [Field F] [Fintype F] (p : F[X])
    (hp : p.natDegree < Fintype.card F - 1) : ∑ x : F, p.eval x = 0 := by
  classical
  simp_rw [Polynomial.eval_eq_sum_range]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i hi
  rw [← Finset.mul_sum, FiniteField.sum_pow_lt_card_sub_one F i (by
    have := Finset.mem_range.mp hi
    omega), mul_zero]

lemma nonzero_of_some_power_sum {F : Type*} [Field F] (M : Finset F)
    (hM : M.Nonempty) (h0 : (0 : F) ∉ M) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ M.card ∧ ∑ x ∈ M, x^k ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  let e : Fin M.card ≃ M := (Fintype.equivFinOfCardEq (Fintype.card_coe M)).symm
  let f : Fin M.card → F := fun i => (e i).val
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have hv := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero (v := f) hf (fun i => by
    calc
      (∑ j : Fin M.card, f j * f j ^ (i : ℕ)) =
          ∑ y : M, (y.val) ^ ((i : ℕ)+1) := by
        apply Fintype.sum_equiv e
        intro j
        simp [f,pow_succ,mul_comm]
      _ = ∑ y ∈ M, y ^ ((i : ℕ)+1) := Finset.sum_coe_sort M _
      _ = 0 := h _ (by omega) (by omega))
  obtain ⟨x,hx⟩ := hM
  have he : f (e.symm ⟨x,hx⟩) = 0 := congrFun hv _
  have hx0 : x = 0 := by simpa [f] using he
  exact h0 (hx0 ▸ hx)

lemma exists_nonzero_collision {F : Type*} [Field F] [Fintype F] (p : F[X])
    (hp : p ≠ 0) (hq : p.natDegree ^ 2 < Fintype.card F - 1)
    {a b : F} (hab : a ≠ b) (ha : p.eval a = 0) (hb : p.eval b = 0) :
    ∃ x y : F, x ≠ y ∧ p.eval x ≠ 0 ∧ p.eval x = p.eval y := by
  classical
  by_contra h
  push_neg at h
  let U : Finset F := univ.filter (fun x => p.eval x ≠ 0)
  let Z : Finset F := univ.filter (fun x => p.eval x = 0)
  let I : Finset F := U.image p.eval
  let M : Finset F := univ \ insert 0 I
  have hinj : Set.InjOn p.eval U := by
    intro x hx y hy he
    by_contra hxy
    exact h x y hxy (mem_filter.mp hx).2 he
  have hIZ : I.card = U.card := Finset.card_image_of_injOn hinj
  have h0I : (0 : F) ∉ I := by
    intro h0
    obtain ⟨x,hx,he⟩ := Finset.mem_image.mp h0
    exact (mem_filter.mp hx).2 he
  have hUZ : U.card + Z.card = Fintype.card F := by
    have hh := card_filter_add_card_filter_not (s := (univ : Finset F))
      (p := fun x => p.eval x = 0)
    simpa [U,Z,add_comm] using hh
  have hZ : 2 ≤ Z.card := by
    have hs : ({a,b} : Finset F) ⊆ Z := by
      intro x hx
      simp only [mem_insert,mem_singleton] at hx
      rcases hx with rfl | rfl
      · simp [Z,ha]
      · simp [Z,hb]
    simpa [hab] using Finset.card_le_card hs
  have hZle : Z.card ≤ p.natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro x hx
    exact Polynomial.mem_roots hp |>.mpr (mem_filter.mp hx).2
  have hMcard : M.card = Fintype.card F - (U.card+1) := by
    simp only [M,card_sdiff_of_subset (Finset.subset_univ _),card_univ,
      card_insert_of_notMem h0I,hIZ]
  have hMpos : 0 < M.card := by omega
  have hMle : M.card ≤ p.natDegree := by omega
  have h0M : (0 : F) ∉ M := by simp [M]
  obtain ⟨k,hk,hkM,hSum⟩ := nonzero_of_some_power_sum M (card_pos.mp hMpos) h0M
  have hkp : k ≤ p.natDegree := hkM.trans hMle
  have hkq : k < Fintype.card F - 1 := by nlinarith
  have hpk : (p^k).natDegree < Fintype.card F - 1 := by
    rw [Polynomial.natDegree_pow]
    nlinarith
  have htotal : ∑ x : F, (p.eval x)^k = 0 := by
    simpa only [Polynomial.eval_pow] using sum_eval_eq_zero (p^k) hpk
  have hSumI : ∑ x ∈ I, x^k = 0 := by
    rw [Finset.sum_image hinj]
    have he : (∑ x ∈ U, (p.eval x)^k) = ∑ x : F, (p.eval x)^k := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro x hx hxU
      have hz : p.eval x = 0 := by simpa [U] using hxU
      simp [hz,show k ≠ 0 by omega]
    exact he.trans htotal
  have hSumAll : ∑ x ∈ insert 0 I, x^k = 0 := by
    rw [Finset.sum_insert h0I,zero_pow (by omega : k ≠ 0),zero_add,hSumI]
  have hSplit := Finset.sum_sdiff (s₁ := insert 0 I)
    (s₂ := (univ : Finset F)) (f := fun x => x^k) (Finset.subset_univ _)
  have hfield := FiniteField.sum_pow_lt_card_sub_one F k hkq
  apply hSum
  change (∑ x ∈ M, x^k) + (∑ x ∈ insert 0 I, x^k) = ∑ x : F, x^k at hSplit
  rw [hSumAll,add_zero,hfield] at hSplit
  exact hSplit

#print axioms exists_nonzero_collision
end FinitePolynomialCollision
