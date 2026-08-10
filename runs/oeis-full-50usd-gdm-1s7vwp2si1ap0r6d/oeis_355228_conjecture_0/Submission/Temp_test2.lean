import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

open Finset Nat Set

lemma divisors_168_eq : (Nat.divisors 168) = ({1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168} : Finset ℕ) := by decide

lemma S_168_sum : ({1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168} : Finset ℕ).sum id = 480 := by decide

lemma S_168_card : ({1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168} : Finset ℕ).card = 16 := by rfl

lemma S_168_max1 : ∀ x ∈ ({1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168} : Finset ℕ), x ≤ 168 := by decide

lemma S_168_max2 : ∀ x ∈ ({1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168} : Finset ℕ),
  ∀ y ∈ ({1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168} : Finset ℕ), x ≠ y → x + y ≤ 252 := by decide

lemma S_168_max3 : ∀ x ∈ ({1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168} : Finset ℕ),
  ∀ y ∈ ({1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168} : Finset ℕ),
  ∀ z ∈ ({1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168} : Finset ℕ),
  x ≠ y → y ≠ z → x ≠ z → x + y + z ≤ 308 := by decide

lemma no_subset_168_ge_13 (k : ℕ) (hk : 13 ≤ k) (D : Finset ℕ) (hD : D ⊆ Nat.divisors 168) (hcard : D.card = k) : D.sum id ≠ 168 := by
  by_contra h_sum
  have h_union : Nat.divisors 168 = D ∪ (Nat.divisors 168 \ D) := by
    rw [Finset.union_comm]
    exact (Finset.sdiff_union_of_subset hD).symm
  have h_disj : Disjoint D (Nat.divisors 168 \ D) := Finset.disjoint_sdiff
  have h_sum_total : (Nat.divisors 168).sum id = D.sum id + (Nat.divisors 168 \ D).sum id := by
    conv_lhs => rw [h_union]
    rw [Finset.sum_union h_disj]
  have h_card_total : (Nat.divisors 168).card = D.card + (Nat.divisors 168 \ D).card := by
    conv_lhs => rw [h_union]
    rw [Finset.card_union_of_disjoint h_disj]
  have hS_card : (Nat.divisors 168).card = 16 := by
    rw [divisors_168_eq]
    rfl
  have hS_sum : (Nat.divisors 168).sum id = 480 := by
    rw [divisors_168_eq]
    decide
  generalize hc : (Nat.divisors 168 \ D).card = c
  have hc_le : c ≤ 3 := by omega
  have h_C_sum_le : (Nat.divisors 168 \ D).sum id ≤ 308 := by
    interval_cases c
    · -- c = 0
      have hC_empty : (Nat.divisors 168 \ D) = ∅ := Finset.card_eq_zero.mp hc
      rw [hC_empty, Finset.sum_empty]
      omega
    · -- c = 1
      rcases Finset.card_eq_one.mp hc with ⟨x, hx⟩
      have hx_mem : x ∈ (Nat.divisors 168 \ D) := by rw [hx]; exact Finset.mem_singleton_self x
      have hx_in : x ∈ Nat.divisors 168 := (Finset.mem_sdiff.mp hx_mem).1
      have hx_le : x ≤ 168 := by
        rw [divisors_168_eq] at hx_in
        exact S_168_max1 x hx_in
      have hC_sum : (Nat.divisors 168 \ D).sum id = x := by
        rw [hx, Finset.sum_singleton]
        rfl
      omega
    · -- c = 2
      rcases Finset.card_eq_two.mp hc with ⟨x, y, hxy, hxy_eq⟩
      have hx_mem : x ∈ (Nat.divisors 168 \ D) := by rw [hxy_eq]; exact Finset.mem_insert_self x {y}
      have hy_mem : y ∈ (Nat.divisors 168 \ D) := by rw [hxy_eq]; simp
      have hx_in : x ∈ Nat.divisors 168 := (Finset.mem_sdiff.mp hx_mem).1
      have hy_in : y ∈ Nat.divisors 168 := (Finset.mem_sdiff.mp hy_mem).1
      have hx_in' : x ∈ ({1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168} : Finset ℕ) := by
        rwa [← divisors_168_eq]
      have hy_in' : y ∈ ({1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168} : Finset ℕ) := by
        rwa [← divisors_168_eq]
      have hxy_le : x + y ≤ 252 := S_168_max2 x hx_in' y hy_in' hxy
      have hC_sum : (Nat.divisors 168 \ D).sum id = x + y := by
        rw [hxy_eq]
        simp [hxy]
      omega
    · -- c = 3
      rcases Finset.card_eq_three.mp hc with ⟨x, y, z, hxy, hxz, hyz, hxyz_eq⟩
      have hx_mem : x ∈ (Nat.divisors 168 \ D) := by rw [hxyz_eq]; simp
      have hy_mem : y ∈ (Nat.divisors 168 \ D) := by rw [hxyz_eq]; simp
      have hz_mem : z ∈ (Nat.divisors 168 \ D) := by rw [hxyz_eq]; simp
      have hx_in : x ∈ Nat.divisors 168 := (Finset.mem_sdiff.mp hx_mem).1
      have hy_in : y ∈ Nat.divisors 168 := (Finset.mem_sdiff.mp hy_mem).1
      have hz_in : z ∈ Nat.divisors 168 := (Finset.mem_sdiff.mp hz_mem).1
      have hx_in' : x ∈ ({1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168} : Finset ℕ) := by
        rwa [← divisors_168_eq]
      have hy_in' : y ∈ ({1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168} : Finset ℕ) := by
        rwa [← divisors_168_eq]
      have hz_in' : z ∈ ({1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168} : Finset ℕ) := by
        rwa [← divisors_168_eq]
      have hxyz_le : x + y + z ≤ 308 := S_168_max3 x hx_in' y hy_in' z hz_in' hxy hyz hxz
      have hC_sum : (Nat.divisors 168 \ D).sum id = x + y + z := by
        rw [hxyz_eq]
        simp [hxy, hyz, hxz]
        omega
      omega
  omega
