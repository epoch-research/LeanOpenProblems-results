import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

open Finset Nat Set

lemma divisors_144_eq : (Nat.divisors 144) = ({1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 36, 48, 72, 144} : Finset ℕ) := by decide

lemma S_144_sum : ({1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 36, 48, 72, 144} : Finset ℕ).sum id = 403 := by decide

lemma S_144_card : ({1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 36, 48, 72, 144} : Finset ℕ).card = 15 := by rfl

lemma S_144_max1 : ∀ x ∈ ({1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 36, 48, 72, 144} : Finset ℕ), x ≤ 144 := by decide

lemma S_144_max2 : ∀ x ∈ ({1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 36, 48, 72, 144} : Finset ℕ),
  ∀ y ∈ ({1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 36, 48, 72, 144} : Finset ℕ), x ≠ y → x + y ≤ 216 := by decide

lemma no_subset_144_ge_13 (k : ℕ) (hk : 13 ≤ k) (D : Finset ℕ) (hD : D ⊆ Nat.divisors 144) (hcard : D.card = k) : D.sum id ≠ 144 := by
  by_contra h_sum
  have h_union : Nat.divisors 144 = D ∪ (Nat.divisors 144 \ D) := by
    rw [Finset.union_comm]
    exact (Finset.sdiff_union_of_subset hD).symm
  have h_disj : Disjoint D (Nat.divisors 144 \ D) := Finset.disjoint_sdiff
  have h_sum_total : (Nat.divisors 144).sum id = D.sum id + (Nat.divisors 144 \ D).sum id := by
    conv_lhs => rw [h_union]
    rw [Finset.sum_union h_disj]
  have h_card_total : (Nat.divisors 144).card = D.card + (Nat.divisors 144 \ D).card := by
    conv_lhs => rw [h_union]
    rw [Finset.card_union_of_disjoint h_disj]
  have hS_card : (Nat.divisors 144).card = 15 := by
    rw [divisors_144_eq]
    rfl
  have hS_sum : (Nat.divisors 144).sum id = 403 := by
    rw [divisors_144_eq]
    decide
  have h_C_card : (Nat.divisors 144 \ D).card ≤ 2 := by omega
  have h_C_sum_le : (Nat.divisors 144 \ D).sum id ≤ 216 := by
    rcases (Nat.divisors 144 \ D).card.eq_zero_or_pos with hC0 | hCp
    · have hC_empty : (Nat.divisors 144 \ D) = ∅ := Finset.card_eq_zero.mp hC0
      rw [hC_empty, Finset.sum_empty]
      omega
    · rcases Nat.eq_or_lt_of_le hCp with hC1 | hC2
      · rcases Finset.card_eq_one.mp hC1.symm with ⟨x, hx⟩
        have hx_mem : x ∈ (Nat.divisors 144 \ D) := by rw [hx]; exact Finset.mem_singleton_self x
        have hx_in : x ∈ Nat.divisors 144 := (Finset.mem_sdiff.mp hx_mem).1
        have hx_le : x ≤ 144 := by
          rw [divisors_144_eq] at hx_in
          exact S_144_max1 x hx_in
        have hC_sum : (Nat.divisors 144 \ D).sum id = x := by
          rw [hx, Finset.sum_singleton]
          rfl
        omega
      · have h_C_card_eq : (Nat.divisors 144 \ D).card = 2 := by omega
        rcases Finset.card_eq_two.mp h_C_card_eq with ⟨x, y, hxy, hxy_eq⟩
        have hx_mem : x ∈ (Nat.divisors 144 \ D) := by rw [hxy_eq]; exact Finset.mem_insert_self x {y}
        have hy_mem : y ∈ (Nat.divisors 144 \ D) := by rw [hxy_eq]; simp
        have hx_in : x ∈ Nat.divisors 144 := (Finset.mem_sdiff.mp hx_mem).1
        have hy_in : y ∈ Nat.divisors 144 := (Finset.mem_sdiff.mp hy_mem).1
        have hx_in' : x ∈ ({1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 36, 48, 72, 144} : Finset ℕ) := by
          rwa [← divisors_144_eq]
        have hy_in' : y ∈ ({1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 36, 48, 72, 144} : Finset ℕ) := by
          rwa [← divisors_144_eq]
        have hxy_le : x + y ≤ 216 := S_144_max2 x hx_in' y hy_in' hxy
        have hC_sum : (Nat.divisors 144 \ D).sum id = x + y := by
          rw [hxy_eq]
          simp [hxy]
        omega
  omega
