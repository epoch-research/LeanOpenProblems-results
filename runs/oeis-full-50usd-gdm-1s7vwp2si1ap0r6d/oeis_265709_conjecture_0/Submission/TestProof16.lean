import FormalConjectures.Util.ProblemImports

open Nat Finset ArithmeticFunction

lemma padicValRat_sum_strict_gt {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℚ) (K : ℤ)
  (h : ∀ x ∈ s, padicValRat 2 (f x) > K) (h_nz : ∑ x ∈ s, f x ≠ 0) :
  padicValRat 2 (∑ x ∈ s, f x) > K := by
  induction s using Finset.induction_on with
  | empty =>
    simp at h_nz
  | insert a s ha ih =>
    have h_insert : ∑ x ∈ insert a s, f x = f a + ∑ x ∈ s, f x := sum_insert ha
    have h_fa : padicValRat 2 (f a) > K := h a (mem_insert_self a s)
    by_cases h_sum_zero : ∑ x ∈ s, f x = 0
    · rw [h_insert]
      rw [h_sum_zero, add_zero]
      exact h_fa
    · have ih_val : padicValRat 2 (∑ x ∈ s, f x) > K := by
        apply ih
        · intro x hx
          exact h x (mem_insert_of_mem hx)
        · exact h_sum_zero
      have h_add_nz : f a + ∑ x ∈ s, f x ≠ 0 := by
        rw [← h_insert]
        exact h_nz
      have h_min := padicValRat.min_le_padicValRat_add (p := 2) h_add_nz
      have h_min_gt : K < min (padicValRat 2 (f a)) (padicValRat 2 (∑ x ∈ s, f x)) := lt_min h_fa ih_val
      rw [h_insert]
      omega

lemma padicValRat_sum_unique_min {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℚ) (x0 : α) (hx0 : x0 ∈ s)
  (h_min : ∀ x ∈ s, x ≠ x0 → padicValRat 2 (f x0) < padicValRat 2 (f x))
  (h_fnz : ∀ x ∈ s, f x ≠ 0) (h_nz : ∑ x ∈ s, f x ≠ 0) :
  padicValRat 2 (∑ x ∈ s, f x) = padicValRat 2 (f x0) := by
  have h_not_mem : x0 ∉ s.erase x0 := by simp
  have h_split : ∑ x ∈ s, f x = f x0 + ∑ x ∈ s.erase x0, f x := by
    rw [← sum_insert h_not_mem]
    rw [insert_erase hx0]
  by_cases h_sum_zero : ∑ x ∈ s.erase x0, f x = 0
  · rw [h_split, h_sum_zero, add_zero]
  · have h_gt : padicValRat 2 (f x0) < padicValRat 2 (∑ x ∈ s.erase x0, f x) := by
      apply padicValRat_sum_strict_gt (s.erase x0) f (padicValRat 2 (f x0))
      · intro x hx
        have h_mem : x ∈ s := mem_of_mem_erase hx
        have h_ne : x ≠ x0 := ne_of_mem_erase hx
        exact h_min x h_mem h_ne
      · exact h_sum_zero
    have h_add_nz : f x0 + ∑ x ∈ s.erase x0, f x ≠ 0 := by
      rw [← h_split]
      exact h_nz
    have h_x0_nz : f x0 ≠ 0 := h_fnz x0 hx0
    have h_add_eq := @padicValRat.add_eq_of_lt 2 _ (f x0) (∑ x ∈ s.erase x0, f x) h_add_nz h_x0_nz h_sum_zero h_gt
    rw [h_split]
    exact h_add_eq

lemma unique_max_power_of_two (M : ℕ) (hM : M ≥ 1) :
  ∃ J : ℕ, 2^J ≤ M ∧ M < 2^(J+1) ∧
  ∀ y : ℕ, 1 ≤ y → y ≤ M → y ≠ 2^J → padicValNat 2 y < J := by
  use M.size - 1
  have h_size : M.size ≥ 1 := Nat.size_pos.mpr (by omega)
  have h_eq : M.size - 1 + 1 = M.size := by omega
  have h_prime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h_lt : M.size - 1 < M.size := Nat.sub_lt h_size (by omega)
  constructor
  · exact Nat.lt_size.mp h_lt
  · constructor
    · rw [h_eq]
      exact Nat.lt_size_self M
    · intro y hy1 hy2 hyne
      by_contra h_ge
      push_neg at h_ge
      have h_dvd : 2^(M.size - 1) ∣ y := by
        rw [← padicValNat_dvd_iff_le (by omega)] at h_ge
        exact h_ge
      rcases h_dvd with ⟨o, rfl⟩
      have ho : o ≥ 1 := by
        by_contra hc
        have : o = 0 := by omega
        subst o
        simp at hy1
      have ho_gt : o ≥ 2 := by
        by_contra hc
        have : o = 1 := by omega
        subst o
        simp at hyne
      have h_bound : 2^(M.size - 1) * 2 ≤ 2^(M.size - 1) * o := by
        nlinarith
      have h_pow_eq : 2^(M.size - 1) * 2 = 2^(M.size - 1 + 1) := by
        rw [pow_succ]
      rw [h_pow_eq] at h_bound
      rw [h_eq] at h_bound
      have h_lt_size := Nat.lt_size_self M
      omega

lemma padicValRat_add_three_odd (x y z : ℚ) (hx : padicValRat 2 x = 0) (hy : padicValRat 2 y = 0) (hz : padicValRat 2 z = 0)
  (h_nz : x + y + z ≠ 0) (h_xy : x + y ≠ 0) :
  padicValRat 2 (x + y + z) = 0 := by
  have h_min := padicVal_add_eq_of_lt (p := 2)
  sorry
