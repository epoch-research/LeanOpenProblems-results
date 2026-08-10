import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 1000000
open Finset Nat Set

lemma divisors_120_eq : (Nat.divisors 120) = ({1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 20, 24, 30, 40, 60, 120} : Finset ℕ) := by decide

def S_120_small : Finset ℕ := {1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 20, 24}
def S_120_big : Finset ℕ := {30, 40, 60, 120}

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
    ext x
    simp [A, B]
    by_cases hx : x ∈ S_120_big <;> simp [hx]
  have h_disj : Disjoint A B := by
    ext x
    simp [A, B]
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
    -- Now we want to bound A.sum id
    have h_A_sum_ge : A.sum id ≥ if k - B.card = 12 then 110 else if k - B.card = 11 then 86 else if k - B.card = 10 then 66 else if k - B.card = 9 then 51 else 0 := by
      sorry
    sorry
