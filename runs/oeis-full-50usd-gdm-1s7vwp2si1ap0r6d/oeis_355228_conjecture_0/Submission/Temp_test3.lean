import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

open Finset Nat Set

-- ==================== 120 ====================

lemma divisors_120_eq : (Nat.divisors 120) = ({1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 20, 24, 30, 40, 60, 120} : Finset ℕ) := by decide

def S_120_small : Finset ℕ := {1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 20, 24}
def S_120_big : Finset ℕ := {30, 40, 60, 120}

lemma S_120_small_sum : S_120_small.sum id = 110 := by decide

lemma mem_small_elements_120 (x : ℕ) (hx : x ∈ Nat.divisors 120) (h_not_big : x ∉ S_120_big) : x ∈ S_120_small := by
  have h_dec : ∀ y ∈ Nat.divisors 120, y ∉ ({30, 40, 60, 120} : Finset ℕ) → y ∈ ({1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 20, 24} : Finset ℕ) := by decide
  exact h_dec x hx h_not_big

lemma S_120_small_card : S_120_small.card = 12 := by rfl

lemma test_120_cases : ∀ B ⊆ S_120_big, B ≠ ∅ →
  13 - B.card ≤ 12 ∧
  (13 - B.card = 12 → B.sum id + 110 > 120) ∧
  (13 - B.card = 11 → B.sum id + 86 > 120) ∧
  (13 - B.card = 10 → B.sum id + 66 > 120) ∧
  (13 - B.card = 9 → B.sum id + 51 > 120) := by decide

lemma S_max1 : ∀ x ∈ S_120_small, x ≤ 24 := by decide
lemma S_max2 : ∀ x ∈ S_120_small, ∀ y ∈ S_120_small, x ≠ y → x + y ≤ 44 := by decide
lemma S_max3 : ∀ x ∈ S_120_small, ∀ y ∈ S_120_small, ∀ z ∈ S_120_small, x ≠ y → y ≠ z → x ≠ z → x + y + z ≤ 59 := by decide

lemma no_subset_120_ge_13 (k : ℕ) (hk : 13 ≤ k) (D : Finset ℕ) (hD : D ⊆ Nat.divisors 120) (hcard : D.card = k) : D.sum id ≠ 120 := by
  by_contra h_sum
  let B := D ∩ S_120_big
  let A := D \ S_120_big
  have h_union : D = A ∪ B := by
    rw [Finset.sdiff_union_inter D S_120_big]
  have h_disj : Disjoint A B := by
    rw [disjoint_iff_ne]
    intro x hx y hy h_eq
    subst h_eq
    simp [A, B] at hx hy
    exact hx.2 hy.2
  have h_sum_total : D.sum id = A.sum id + B.sum id := by
    rw [h_union, Finset.sum_union h_disj]
  have h_card_total : D.card = A.card + B.card := by
    rw [h_union, Finset.card_union_of_disjoint h_disj]
  have h_A_sub : A ⊆ S_120_small := by
    intro x hx
    simp [A] at hx
    apply mem_small_elements_120 x (hD hx.1) hx.2
  have h_A_card_le : A.card ≤ 12 := by
    have h_le := Finset.card_le_card h_A_sub
    rw [S_120_small_card] at h_le
    exact h_le
  by_cases hB_empty : B = ∅
  · -- B is empty
    have h_B_card : B.card = 0 := by simp [hB_empty]
    omega
  · -- B is not empty
    have h_B_sub : B ⊆ S_120_big := by simp [B]
    have h_cases := test_120_cases B h_B_sub hB_empty
    have h_B_card_le : B.card ≤ 4 := by
      have h_le := Finset.card_le_card h_B_sub
      exact h_le
    have h_A_card_eq : A.card = k - B.card := by omega
    have h_rem_le : 13 - B.card ≤ 12 := h_cases.1
    -- Since k ≥ 13, A.card ≥ 13 - B.card
    have h_A_card_ge : A.card ≥ 13 - B.card := by omega
    -- Now we do a case-split on A.card
    have h_A_sum_ge : A.sum id ≥ if A.card = 12 then 110 else if A.card = 11 then 86 else if A.card = 10 then 66 else if A.card = 9 then 51 else 0 := by
      split_ifs with h12 h11 h10 h9
      · -- A.card = 12
        have h_eq : A = S_120_small := by
          apply Finset.eq_of_subset_of_card_le h_A_sub
          rw [S_120_small_card, h12]
        rw [h_eq, S_120_small_sum]
      · -- A.card = 11
        have h_sum_sub : S_120_small.sum id = (S_120_small \ A).sum id + A.sum id := by
          rw [← Finset.sum_sdiff h_A_sub]
        have h_card_sdiff : (S_120_small \ A).card = 1 := by
          rw [Finset.card_sdiff_of_subset h_A_sub, S_120_small_card, h11]
        rcases Finset.card_eq_one.mp h_card_sdiff with ⟨x, hx⟩
        have hx_mem : x ∈ S_120_small \ A := by rw [hx]; exact Finset.mem_singleton_self x
        rw [Finset.mem_sdiff] at hx_mem
        have hx_in : x ∈ S_120_small := hx_mem.1
        have hx_le : x ≤ 24 := S_max1 x hx_in
        have h_sdiff_sum : (S_120_small \ A).sum id = x := by
          rw [hx, Finset.sum_singleton]
          rfl
        rw [S_120_small_sum] at h_sum_sub
        omega
      · -- A.card = 10
        have h_sum_sub : S_120_small.sum id = (S_120_small \ A).sum id + A.sum id := by
          rw [← Finset.sum_sdiff h_A_sub]
        have h_card_sdiff : (S_120_small \ A).card = 2 := by
          rw [Finset.card_sdiff_of_subset h_A_sub, S_120_small_card, h10]
        rcases Finset.card_eq_two.mp h_card_sdiff with ⟨x, y, hxy, hxy_eq⟩
        have h_sub_sdiff : S_120_small \ A ⊆ S_120_small := Finset.sdiff_subset
        have hx_in : x ∈ S_120_small := by
          apply h_sub_sdiff
          rw [hxy_eq]
          exact Finset.mem_insert_self x {y}
        have hy_in : y ∈ S_120_small := by
          apply h_sub_sdiff
          rw [hxy_eq]
          simp
        have hxy_le : x + y ≤ 44 := S_max2 x hx_in y hy_in hxy
        have h_sdiff_sum : (S_120_small \ A).sum id = x + y := by
          rw [hxy_eq]
          simp [hxy]
        rw [S_120_small_sum] at h_sum_sub
        omega
      · -- A.card = 9
        have h_sum_sub : S_120_small.sum id = (S_120_small \ A).sum id + A.sum id := by
          rw [← Finset.sum_sdiff h_A_sub]
        have h_card_sdiff : (S_120_small \ A).card = 3 := by
          rw [Finset.card_sdiff_of_subset h_A_sub, S_120_small_card, h9]
        rcases Finset.card_eq_three.mp h_card_sdiff with ⟨x, y, z, hxy, hxz, hyz, hxyz_eq⟩
        have h_sub_sdiff : S_120_small \ A ⊆ S_120_small := Finset.sdiff_subset
        have hx_in : x ∈ S_120_small := by
          apply h_sub_sdiff
          rw [hxyz_eq]
          simp
        have hy_in : y ∈ S_120_small := by
          apply h_sub_sdiff
          rw [hxyz_eq]
          simp
        have hz_in : z ∈ S_120_small := by
          apply h_sub_sdiff
          rw [hxyz_eq]
          simp
        have hxyz_le : x + y + z ≤ 59 := S_max3 x hx_in y hy_in z hz_in hxy hyz hxz
        have h_sdiff_sum : (S_120_small \ A).sum id = x + y + z := by
          rw [hxyz_eq]
          simp [hxy, hyz, hxz]
          omega
        rw [S_120_small_sum] at h_sum_sub
        omega
      · omega
    -- Now we just use h_cases to show A.sum id + B.sum id > 120
    have h_final : A.sum id + B.sum id > 120 := by
      rcases h_cases with ⟨_, h_case12, h_case11, h_case10, h_case9⟩
      -- split into cases on B.card
      by_cases hB1 : B.card = 1
      · have h_A_card_12 : A.card = 12 := by omega
        have h_rem_12 : 13 - B.card = 12 := by omega
        have h_sum_A : A.sum id ≥ 110 := by
          revert h_A_sum_ge
          simp [h_A_card_12]
        have h_goal := h_case12 h_rem_12
        omega
      · by_cases hB2 : B.card = 2
        · have h_rem_11 : 13 - B.card = 11 := by omega
          by_cases hA12 : A.card = 12
          · have h_sum_A : A.sum id ≥ 110 := by
              revert h_A_sum_ge
              simp [hA12]
            omega
          · have h_A_card_11 : A.card = 11 := by omega
            have h_sum_A : A.sum id ≥ 86 := by
              revert h_A_sum_ge
              simp [h_A_card_11]
            have h_goal := h_case11 h_rem_11
            omega
        · by_cases hB3 : B.card = 3
          · have h_rem_10 : 13 - B.card = 10 := by omega
            by_cases hA12 : A.card = 12
            · have h_sum_A : A.sum id ≥ 110 := by revert h_A_sum_ge; simp [hA12]
              omega
            · by_cases hA11 : A.card = 11
              · have h_sum_A : A.sum id ≥ 86 := by revert h_A_sum_ge; simp [hA11]
                omega
              · have h_A_card_10 : A.card = 10 := by omega
                have h_sum_A : A.sum id ≥ 66 := by
                  revert h_A_sum_ge
                  simp [h_A_card_10]
                have h_goal := h_case10 h_rem_10
                omega
          · have h_B4 : B.card = 4 := by omega
            have h_rem_9 : 13 - B.card = 9 := by omega
            by_cases hA12 : A.card = 12
            · have h_sum_A : A.sum id ≥ 110 := by revert h_A_sum_ge; simp [hA12]
              omega
            · by_cases hA11 : A.card = 11
              · have h_sum_A : A.sum id ≥ 86 := by revert h_A_sum_ge; simp [hA11]
                omega
              · by_cases hA10 : A.card = 10
                · have h_sum_A : A.sum id ≥ 66 := by revert h_A_sum_ge; simp [hA10]
                  omega
                · have h_A_card_9 : A.card = 9 := by omega
                  have h_sum_A : A.sum id ≥ 51 := by
                    revert h_A_sum_ge
                    simp [h_A_card_9]
                  have h_goal := h_case9 h_rem_9
                  omega
    omega

-- ==================== 144 ====================

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
  generalize hc : (Nat.divisors 144 \ D).card = c
  have hc_le : c ≤ 2 := by omega
  have h_C_sum_le : (Nat.divisors 144 \ D).sum id ≤ 216 := by
    interval_cases c
    · -- c = 0
      have hC_empty : (Nat.divisors 144 \ D) = ∅ := Finset.card_eq_zero.mp hc
      rw [hC_empty, Finset.sum_empty]
      omega
    · -- c = 1
      rcases Finset.card_eq_one.mp hc with ⟨x, hx⟩
      have hx_mem : x ∈ (Nat.divisors 144 \ D) := by rw [hx]; exact Finset.mem_singleton_self x
      have hx_in : x ∈ Nat.divisors 144 := (Finset.mem_sdiff.mp hx_mem).1
      have hx_le : x ≤ 144 := by
        rw [divisors_144_eq] at hx_in
        exact S_144_max1 x hx_in
      have hC_sum : (Nat.divisors 144 \ D).sum id = x := by
        rw [hx, Finset.sum_singleton]
        rfl
      omega
    · -- c = 2
      rcases Finset.card_eq_two.mp hc with ⟨x, y, hxy, hxy_eq⟩
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

-- ==================== 168 ====================

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

lemma sInf_empty_test : sInf (∅ : Set ℕ) = 0 := csInf_empty

lemma sInf_empty_test : sInf (∅ : Set ℕ) = 0 := Nat.sInf_empty

lemma no_smaller_candidate_a08_ge_13_except (m : ℕ) (hm : m < 180) (k : ℕ) (hk : 13 ≤ k) (h_mem : m ∈ S_a08 k) :
  m = 120 ∨ m = 144 ∨ m = 168 := by
  have h_ab : 2 * m ≤ (Nat.divisors m).sum id := mem_S_a08_imp_abundant (by omega) h_mem
  have h_cd : k < (Nat.divisors m).card := mem_S_a08_imp_card_divisors (by omega) h_mem
  have h_dec : ∀ x < 180, 2 * x ≤ (Nat.divisors x).sum id ∧ 13 < (Nat.divisors x).card → x = 120 ∨ x = 144 ∨ x = 168 := by decide
  have h_cond : 2 * m ≤ (Nat.divisors m).sum id ∧ 13 < (Nat.divisors m).card := ⟨h_ab, by omega⟩
  exact h_dec m hm h_cond
