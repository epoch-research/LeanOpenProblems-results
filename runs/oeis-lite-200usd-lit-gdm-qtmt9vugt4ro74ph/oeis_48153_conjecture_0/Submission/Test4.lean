import FormalConjectures.Util.ProblemImports
open Finset

lemma mod_sq_sub_self (n k : ℕ) (hk : k < n) : (n - k) ^ 2 % n = k ^ 2 % n := by
  have h_le : k ≤ n := Nat.le_of_lt hk
  set d := n - k
  have h_eq : n = d + k := (Nat.sub_add_cancel h_le).symm
  have h_id : d ^ 2 + (d + k) * k = k ^ 2 + (d + k) * d := by
    ring
  have h_mod : (d ^ 2 + (d + k) * k) % (d + k) = (k ^ 2 + (d + k) * d) % (d + k) := by
    rw [h_id]
  rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left] at h_mod
  rw [← h_eq] at h_mod
  exact h_mod

lemma div_sq_sub_self (n k : ℕ) (hn : 0 < n) (hk : 2 * k ≤ n) : (n - k) ^ 2 / n = n - 2 * k + k ^ 2 / n := by
  have h_le : k ≤ n := by omega
  have h_mod : (n - k) ^ 2 % n = k ^ 2 % n := mod_sq_sub_self n k (by omega)
  have h_div_1 : (n - k) ^ 2 = (n - k) ^ 2 / n * n + (n - k) ^ 2 % n := by
    nth_rw 1 [mul_comm]
    exact (Nat.div_add_mod ((n - k) ^ 2) n).symm
  have h_div_2 : k ^ 2 = k ^ 2 / n * n + k ^ 2 % n := by
    nth_rw 1 [mul_comm]
    exact (Nat.div_add_mod (k ^ 2) n).symm
  have h_id : (n - k) ^ 2 + 2 * n * k = n ^ 2 + k ^ 2 := by
    set d := n - k
    have h_eq : n = d + k := (Nat.sub_add_cancel h_le).symm
    rw [h_eq]
    ring
  have h_combined : ((n - k) ^ 2 / n * n + (n - k) ^ 2 % n) + 2 * n * k = n ^ 2 + (k ^ 2 / n * n + k ^ 2 % n) := by
    rw [← h_div_1, ← h_div_2, h_id]
  have h_sub : ((n - k) ^ 2 / n * n) + 2 * n * k = n ^ 2 + (k ^ 2 / n * n) := by
    omega
  have h_factor : ((n - k) ^ 2 / n + 2 * k) * n = (n + k ^ 2 / n) * n := by
    calc
      ((n - k) ^ 2 / n + 2 * k) * n = (n - k) ^ 2 / n * n + 2 * n * k := by ring
      _ = n ^ 2 + k ^ 2 / n * n := h_sub
      _ = (n + k ^ 2 / n) * n := by ring
  have h_cancel : (n - k) ^ 2 / n + 2 * k = n + k ^ 2 / n := Nat.eq_of_mul_eq_mul_right hn h_factor
  omega

lemma mod_sum_identity (n k : ℕ) :
    k ^ 2 % n + (n - k) ^ 2 % n = k ^ 2 + (n - k) ^ 2 - (k ^ 2 / n + (n - k) ^ 2 / n) * n := by
  have h_div_1 : (n - k) ^ 2 = (n - k) ^ 2 / n * n + (n - k) ^ 2 % n := by
    nth_rw 1 [mul_comm]
    exact (Nat.div_add_mod ((n - k) ^ 2) n).symm
  have h_div_2 : k ^ 2 = k ^ 2 / n * n + k ^ 2 % n := by
    nth_rw 1 [mul_comm]
    exact (Nat.div_add_mod (k ^ 2) n).symm
  rw [add_mul]
  omega

lemma le_bound (n : ℕ) (h : 1 ≤ n) : n * (n - 1) / 2 ≤ (n ^ 2 - 1) / 2 := by
  have h_eq : n * (n - 1) = n ^ 2 - n := by
    rw [Nat.mul_sub_left_distrib, mul_one, ← pow_two]
  rw [h_eq]
  omega

lemma sum_range_sq_subtraction_free (m : ℕ) :
    6 * (∑ k ∈ range (m + 1), k ^ 2) = m * (m + 1) * (2 * m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, mul_add, ih]
    ring

def A048153 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) (fun k => k ^ 2 % n)

lemma a048153_identity (n : ℕ) :
    A048153 n + n * (∑ k ∈ range n, k ^ 2 / n) = ∑ k ∈ range n, k ^ 2 := by
  unfold A048153
  rw [mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro k hk
  rw [add_comm]
  exact Nat.div_add_mod (k ^ 2) n

lemma div_ge_mul (m i : ℕ) (hm : 0 < m) (hi : i ≤ m) : 2 * i ≤ (m + i) ^ 2 / (2 * m) := by
  have hm' : 0 < 2 * m := by omega
  rw [Nat.le_div_iff_mul_le hm']
  have h_id : (m + i) ^ 2 = (m - i) ^ 2 + 4 * m * i := by
    zify [hi]
    ring
  rw [h_id]
  have h_mul : 2 * i * (2 * m) = 4 * m * i := by ring
  rw [h_mul]
  omega

lemma div_ge_mul_odd (m i : ℕ) (hi : i ≤ m) : 2 * i ≤ (m + i) ^ 2 / (2 * m + 1) + 1 := by
  by_cases hi0 : i = 0
  · subst hi0; simp
  have hi_pos : 0 < i := Nat.pos_of_ne_zero hi0
  have h_le : 2 * i - 1 ≤ (m + i) ^ 2 / (2 * m + 1) := by
    have hm : 0 < 2 * m + 1 := by omega
    rw [Nat.le_div_iff_mul_le hm]
    have h_i1 : 1 ≤ 2 * i := by omega
    have h_id : (m + i) ^ 2 = (m - i + 1) ^ 2 + (2 * i - 1) * (2 * m + 1) := by
      zify [hi, h_i1]
      ring
    rw [h_id]
    omega
  omega

lemma div_ge_mul_lower (m k : ℕ) (hk : k < m) (hm : 2 ≤ m) : 4 * k ≤ 2 * (k ^ 2 / (2 * m)) + 3 * m := by
  by_cases h_cases : 4 * k ≤ 3 * m
  · omega
  push_neg at h_cases
  have hm0 : 0 < 2 * m := by omega
  have h_sub_cast : ((m - k : ℕ) : ℤ) = (m : ℤ) - (k : ℤ) := by omega
  have h_sq : 4 * m * k + m ≤ k ^ 2 + 3 * m ^ 2 := by
    have h_id_z : (((k ^ 2 + 3 * m ^ 2 : ℕ) : ℤ)) = (((m - k) ^ 2 + 2 * m ^ 2 + 2 * m * k : ℕ) : ℤ) := by
      push_cast
      rw [h_sub_cast]
      ring
    have h_id : k ^ 2 + 3 * m ^ 2 = (m - k) ^ 2 + 2 * m ^ 2 + 2 * m * k := by exact_mod_cast h_id_z
    rw [h_id]
    have h_m2 : 2 * m * k + m ≤ 2 * m ^ 2 := by
      have : 2 * k + 1 ≤ 2 * m := by omega
      calc
        2 * m * k + m = (2 * k + 1) * m := by ring
        _ ≤ (2 * m) * m := Nat.mul_le_mul_right m this
        _ = 2 * m ^ 2 := by ring
    calc
      4 * m * k + m = 2 * m * k + (2 * m * k + m) := by ring
      _ ≤ 2 * m * k + 2 * m ^ 2 := Nat.add_le_add_left h_m2 _
      _ = 2 * m ^ 2 + 2 * m * k := by ring
      _ ≤ (m - k) ^ 2 + 2 * m ^ 2 + 2 * m * k := by omega
  have h_le : (4 * k - 3 * m + 1) / 2 ≤ k ^ 2 / (2 * m) := by
    rw [Nat.le_div_iff_mul_le hm0]
    have h_div : (4 * k - 3 * m + 1) / 2 * (2 * m) ≤ (4 * k - 3 * m + 1) * m := by
      have h_div_le : (4 * k - 3 * m + 1) / 2 * 2 ≤ 4 * k - 3 * m + 1 := Nat.div_mul_le_self _ 2
      calc
        (4 * k - 3 * m + 1) / 2 * (2 * m) = (4 * k - 3 * m + 1) / 2 * 2 * m := by ring
        _ ≤ (4 * k - 3 * m + 1) * m := Nat.mul_le_mul_right m h_div_le
    have h_trans : (4 * k - 3 * m + 1) * m ≤ k ^ 2 := by
      have h_sub_cast2 : ((4 * k - 3 * m : ℕ) : ℤ) = 4 * (k : ℤ) - 3 * (m : ℤ) := by omega
      have h_sq_z : 4 * (m : ℤ) * (k : ℤ) + (m : ℤ) ≤ (k : ℤ) ^ 2 + 3 * (m : ℤ) ^ 2 := by
        exact_mod_cast h_sq
      have h_trans_z : (((4 * k - 3 * m + 1) * m : ℕ) : ℤ) ≤ ((k ^ 2 : ℕ) : ℤ) := by
        push_cast
        rw [h_sub_cast2]
        linarith
      exact_mod_cast h_trans_z
    omega
  have h_final : 4 * k - 3 * m ≤ 2 * (k ^ 2 / (2 * m)) := by
    have h_div2 : (4 * k - 3 * m + 1) / 2 * 2 ≤ k ^ 2 / (2 * m) * 2 := Nat.mul_le_mul_right 2 h_le
    rw [mul_comm (k ^ 2 / (2 * m)) 2] at h_div2
    have h_div3 : 4 * k - 3 * m ≤ (4 * k - 3 * m + 1) / 2 * 2 := by omega
    omega
  omega

lemma Q_bound_implies_A048153_bound (n : ℕ) (h_n : 2 ≤ n)
    (h_Q : (n - 1) * (n - 2) ≤ 3 * (∑ k ∈ range n, k ^ 2 / n)) :
    A048153 n ≤ n * (n - 1) / 2 := by
  have h_n1 : n = n - 1 + 1 := (Nat.sub_add_cancel (by omega)).symm
  have h_sum := a048153_identity n
  have h_sum6 : 6 * A048153 n + 6 * (n * (∑ k ∈ range n, k ^ 2 / n)) = 6 * (∑ k ∈ range n, k ^ 2) := by
    omega
  have h_sum_range : 6 * (∑ k ∈ range n, k ^ 2) = (n - 1) * n * (2 * n - 1) := by
    have h_eq : ∑ k ∈ range n, k ^ 2 = ∑ k ∈ range (n - 1 + 1), k ^ 2 := congrArg (fun x => ∑ k ∈ range x, k ^ 2) h_n1
    rw [h_eq, sum_range_sq_subtraction_free (n - 1)]
    omega
  have h_sum_Q : 2 * n * ((n - 1) * (n - 2)) ≤ 6 * n * (∑ k ∈ range n, k ^ 2 / n) := by
    calc
      2 * n * ((n - 1) * (n - 2)) = 2 * n * ((n - 1) * (n - 2)) := by ring
      _ ≤ 2 * n * (3 * (∑ k ∈ range n, k ^ 2 / n)) := Nat.mul_le_mul_left (2 * n) h_Q
      _ = 6 * n * (∑ k ∈ range n, k ^ 2 / n) := by ring
  have h_sum6_sub : 6 * A048153 n + 2 * n * ((n - 1) * (n - 2)) ≤ 6 * A048153 n + 6 * n * (∑ k ∈ range n, k ^ 2 / n) := by
    omega
  rw [mul_assoc] at h_sum6
  have h_sum6_rw : 6 * A048153 n + 6 * n * (∑ k ∈ range n, k ^ 2 / n) = (n - 1) * n * (2 * n - 1) := by
    rw [h_sum6, h_sum_range]
  rw [h_sum6_rw] at h_sum6_sub
  have h_sub1 : 2 * n * (n - 1) * (n - 2) = n * (n - 1) * (2 * n - 4) := by ring
  have h_sub2 : (n - 1) * n * (2 * n - 1) = n * (n - 1) * (2 * n - 1) := by ring
  rw [h_sub1, h_sub2] at h_sum6_sub
  have h_final : 6 * A048153 n ≤ 3 * n * (n - 1) := by
    have h_diff : (n * (n - 1) * (2 * n - 1)) - (n * (n - 1) * (2 * n - 4)) = 3 * n * (n - 1) := by
      have h_factor : n * (n - 1) * (2 * n - 1) = n * (n - 1) * (2 * n - 4) + 3 * n * (n - 1) := by ring
      rw [h_factor]
      omega
    omega
  omega

lemma mod_sq_le_half (n k : ℕ) (hk : k < n) :
    k ^ 2 % n ≤ if k < (n + 1) / 2 then k ^ 2 else (n - k) ^ 2 := by
  split_ifs with h
  · exact Nat.mod_le _ _
  · have h_eq := mod_sq_sub_self n k hk
    rw [← h_eq]
    exact Nat.mod_le _ _

lemma sum_range_id_mul_two (m : ℕ) : 2 * (∑ i ∈ range m, i) = m * (m - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, mul_add, ih]
    rcases m with _ | m
    · simp
    · have h_eq1 : m + 1 - 1 = m := by omega
      have h_eq2 : m + 2 - 1 = m + 1 := by omega
      rw [h_eq1, h_eq2]
      ring

lemma spec_cases_1 : ∀ n, 1 ≤ n → n ≤ 200 → A048153 n ≤ (n ^ 2 - 1) / 2 := by
  decide

lemma spec_cases_2 : ∀ n, 201 ≤ n → n ≤ 400 → A048153 n ≤ (n ^ 2 - 1) / 2 := by
  decide

lemma spec_cases_3 : ∀ n, 401 ≤ n → n ≤ 600 → A048153 n ≤ (n ^ 2 - 1) / 2 := by
  decide

lemma spec_cases_4 : ∀ n, 601 ≤ n → n ≤ 800 → A048153 n ≤ (n ^ 2 - 1) / 2 := by
  decide

lemma spec_cases_5 : ∀ n, 801 ≤ n → n ≤ 1000 → A048153 n ≤ (n ^ 2 - 1) / 2 := by
  decide

lemma spec_cases_all : ∀ n, 1 ≤ n → n ≤ 1000 → A048153 n ≤ (n ^ 2 - 1) / 2 := by
  intro n h1 h2
  rcases lt_or_ge n 201 with hn | hn
  · exact spec_cases_1 n h1 (by omega)
  · rcases lt_or_ge n 401 with hn2 | hn2
    · exact spec_cases_2 n hn (by omega)
    · rcases lt_or_ge n 601 with hn3 | hn3
      · exact spec_cases_3 n hn2 (by omega)
      · rcases lt_or_ge n 801 with hn4 | hn4
        · exact spec_cases_4 n hn3 (by omega)
        · exact spec_cases_5 n hn4 (by omega)

lemma m_sq_div_two_m (m : ℕ) : m ^ 2 / (2 * m) = m / 2 := by
  rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · by_cases hk : k = 0
    · subst hk; simp
    · have h_pos : 0 < k + k := by omega
      have h_pos2 : 0 < 2 * (k + k) := by omega
      have h_eq : (k + k) ^ 2 = k * (2 * (k + k)) := by ring
      rw [h_eq]
      rw [Nat.mul_div_cancel k h_pos2]
      have : (k + k) / 2 = k := by omega
      rw [this]
  · have h_pos : 0 < 2 * (2 * k + 1) := by omega
    have h_eq1 : (2 * k + 1) ^ 2 = (2 * k + 1) + k * (2 * (2 * k + 1)) := by ring
    have h_eq2 : (2 * k + 1) / 2 = k := by omega
    rw [h_eq1]
    rw [Nat.add_mul_div_right _ _ h_pos]
    have h_zero : (2 * k + 1) / (2 * (2 * k + 1)) = 0 := by
      apply Nat.div_eq_of_lt
      omega
    rw [h_zero, zero_add, h_eq2]

lemma my_sum_range_reflect (n : ℕ) (f : ℕ → ℕ) :
    ∑ i ∈ range n, f (n - 1 - i) = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h_sub_eq : ∀ i ∈ range (n + 1), n + 1 - 1 - i = n - i := by
      intro i hi
      omega
    have h_rw : ∑ i ∈ range (n + 1), f (n + 1 - 1 - i) = ∑ i ∈ range (n + 1), f (n - i) := by
      apply sum_congr rfl
      intro i hi
      rw [h_sub_eq i hi]
    rw [h_rw]
    rw [sum_range_succ']
    have h_sub_eq2 : ∀ k ∈ range n, n - (k + 1) = n - 1 - k := by
      intro k hk
      have : k < n := mem_range.mp hk
      omega
    have h_rw2 : ∑ k ∈ range n, f (n - (k + 1)) = ∑ k ∈ range n, f (n - 1 - k) := by
      apply sum_congr rfl
      intro k hk
      rw [h_sub_eq2 k hk]
    rw [h_rw2, ih, sum_range_succ]
    rw [Nat.sub_zero]

lemma sum_second_half_eq (m : ℕ) (hm : 1 ≤ m) :
    ∑ k ∈ range m, (m + k) ^ 2 / (2 * m) = m * (m - 1) + m / 2 + ∑ k ∈ range (m - 1), (k + 1) ^ 2 / (2 * m) := by
  have hm0 : 0 < m := hm
  have h_m1 : m = m - 1 + 1 := (Nat.sub_add_cancel hm).symm
  nth_rw 1 [h_m1]
  rw [sum_range_succ']
  have h_m0 : (m + 0) ^ 2 / (2 * m) = m / 2 := by
    rw [add_zero]
    exact m_sq_div_two_m m
  rw [h_m0]
  have h_terms : ∀ k ∈ range (m - 1), (m + (k + 1)) ^ 2 / (2 * m) = 2 * (k + 1) + (m - (k + 1)) ^ 2 / (2 * m) := by
    intro k hk
    have hk_lt : k < m - 1 := mem_range.mp hk
    have hk1_lt : k + 1 < m := by omega
    have hj : m - (k + 1) ≤ m := by omega
    have hj_le : 2 * (m - (k + 1)) ≤ 2 * m := by omega
    have h_sub := div_sq_sub_self (2 * m) (m - (k + 1)) (by omega) hj_le
    have h_eq1 : 2 * m - (m - (k + 1)) = m + (k + 1) := by omega
    have h_eq2 : 2 * m - 2 * (m - (k + 1)) = 2 * (k + 1) := by omega
    rw [h_eq1, h_eq2] at h_sub
    exact h_sub
  have h_sum : ∑ k ∈ range (m - 1), (m + (k + 1)) ^ 2 / (2 * m) = ∑ k ∈ range (m - 1), (2 * (k + 1) + (m - (k + 1)) ^ 2 / (2 * m)) := by
    apply sum_congr rfl
    intro k hk
    exact h_terms k hk
  rw [h_sum]
  rw [sum_add_distrib]
  have h_sum_2k : ∑ k ∈ range (m - 1), 2 * (k + 1) = m * (m - 1) := by
    have h1 := sum_range_succ' (fun k => 2 * k) (m - 1)
    have h_eq : m - 1 + 1 = m := by omega
    rw [h_eq] at h1
    simp only [mul_zero, add_zero] at h1
    rw [← h1]
    rw [← mul_sum]
    rw [sum_range_id_mul_two]
  rw [h_sum_2k]
  have h_reflect : ∑ k ∈ range (m - 1), (m - (k + 1)) ^ 2 / (2 * m) = ∑ k ∈ range (m - 1), (k + 1) ^ 2 / (2 * m) := by
    have h_reflect_lemma := my_sum_range_reflect (m - 1) (fun k => (k + 1) ^ 2 / (2 * m))
    have h_eq : ∀ k ∈ range (m - 1), m - 1 - 1 - k + 1 = m - (k + 1) := by
      intro k hk
      have : k < m - 1 := mem_range.mp hk
      omega
    have h_congr : ∑ k ∈ range (m - 1), (m - 1 - 1 - k + 1) ^ 2 / (2 * m) = ∑ k ∈ range (m - 1), (m - (k + 1)) ^ 2 / (2 * m) := by
      apply sum_congr rfl
      intro k hk
      rw [h_eq k hk]
    rw [← h_congr]
    exact h_reflect_lemma
  rw [h_reflect]
  generalize h_S : ∑ k ∈ range (m - 1), (k + 1) ^ 2 / (2 * m) = S
  omega

lemma div_ge_linear_even (H k : ℕ) (hH : 0 < H) : 2 * k - 2 * H ≤ 2 * (k ^ 2 / (4 * H)) := by
  rcases lt_or_ge k (2 * H) with hk2 | hk2
  · by_cases hk1 : k < H
    · have : 2 * k ≤ 2 * H := by omega
      have : 2 * k - 2 * H = 0 := Nat.sub_eq_zero_of_le this
      rw [this]
      exact Nat.zero_le _
    · push_neg at hk1
      obtain ⟨d, rfl⟩ : ∃ d, k = H + d := Nat.exists_eq_add_of_le hk1
      have hd : d < H := by omega
      have h_sq : 2 * H * d ≤ H ^ 2 + d ^ 2 := by
        have : (2 * H * d : ℤ) ≤ H ^ 2 + d ^ 2 := by
          have : 0 ≤ ((H : ℤ) - (d : ℤ)) ^ 2 := sq_nonneg _
          linarith
        exact_mod_cast this
      have h_mul_le : 2 * H * (2 * d) ≤ 4 * H * d := by ring_nf; omega
      have h_le_div : 2 * d ≤ (H + d) ^ 2 / (4 * H) := by
        rw [Nat.le_div_iff_mul_le (by omega)]
        have h_id : (H + d) ^ 2 = H ^ 2 + d ^ 2 + 2 * H * d := by ring
        rw [h_id]
        omega
      omega
  · obtain ⟨d, rfl⟩ : ∃ d, k = 2 * H + d := Nat.exists_eq_add_of_le hk2
    have h_le_div : 2 * H + 2 * d ≤ (2 * H + d) ^ 2 / (4 * H) := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      have h_id : (2 * H + d) ^ 2 = d ^ 2 + 4 * H ^ 2 + 4 * H * d := by ring
      rw [h_id]
      omega
    omega

lemma div_ge_linear_odd (H k : ℕ) (hH : 0 < H) : 2 * k - (2 * H + 2) ≤ 2 * (k ^ 2 / (4 * H + 2)) := by
  rcases lt_or_ge k (2 * H + 1) with hk2 | hk2
  · by_cases hk1 : k < H + 1
    · have : 2 * k ≤ 2 * H + 2 := by omega
      have : 2 * k - (2 * H + 2) = 0 := Nat.sub_eq_zero_of_le this
      rw [this]
      exact Nat.zero_le _
    · push_neg at hk1
      obtain ⟨d, rfl⟩ : ∃ d, k = H + 1 + d := Nat.exists_eq_add_of_le hk1
      have hd : d < H := by omega
      have h_sq : (2 * H + 2) * (d + 1) ≤ (H + 1 + d) ^ 2 := by
        have : ((2 * H + 2) * (d + 1) : ℤ) ≤ (H + 1 + d) ^ 2 := by
          have : 0 ≤ ((H : ℤ) - (d : ℤ)) ^ 2 := sq_nonneg _
          linarith
        exact_mod_cast this
      have h_le_div : 2 * d ≤ (H + 1 + d) ^ 2 / (4 * H + 2) := by
        rw [Nat.le_div_iff_mul_le (by omega)]
        have h_id : (H + 1 + d) ^ 2 = (H + 1 + d) ^ 2 := rfl
        omega
      omega
  · obtain ⟨d, rfl⟩ : ∃ d, k = 2 * H + 1 + d := Nat.exists_eq_add_of_le hk2
    have h_le_div : 2 * H + 2 * d ≤ (2 * H + 1 + d) ^ 2 / (4 * H + 2) := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      have h_id : (2 * H + 1 + d) ^ 2 = (2 * H + 1 + d) ^ 2 := rfl
      omega
    omega

lemma S_even_bound (H : ℕ) (hH : 2 ≤ H) :
    (2 * H) * (2 * H - 1) ≤ 12 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) := by
  have hH_pos : 0 < H := by omega
  have h_sum_le : ∑ k ∈ range (2 * H), (2 * k - 2 * H) ≤ 2 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) := by
    rw [mul_sum]
    apply sum_le_sum
    intro k hk
    exact div_ge_linear_even H k hH_pos
  have h_split : ∑ k ∈ range (2 * H), (2 * k - 2 * H) = H * (H - 1) := by
    have h_split2 := Finset.sum_range_add (fun k => 2 * k - 2 * H) H H
    have h_eq : 2 * H = H + H := by ring
    rw [← h_eq] at h_split2
    rw [h_split2]
    have h_first : ∑ k ∈ range H, (2 * k - 2 * H) = 0 := by
      apply sum_eq_zero
      intro k hk
      have : k < H := mem_range.mp hk
      have : 2 * k ≤ 2 * H := by omega
      exact Nat.sub_eq_zero_of_le this
    have h_second : ∑ k ∈ range H, (2 * (H + k) - 2 * H) = H * (H - 1) := by
      have h_eq2 : ∀ k ∈ range H, 2 * (H + k) - 2 * H = 2 * k := by
        intro k hk
        omega
      have h_congr : ∑ k ∈ range H, (2 * (H + k) - 2 * H) = ∑ k ∈ range H, 2 * k := by
        apply sum_congr rfl
        intro k hk
        exact h_eq2 k hk
      rw [h_congr]
      rw [← mul_sum]
      exact sum_range_id_mul_two H
    omega
  have h_trans : (2 * H) * (2 * H - 1) ≤ 6 * (∑ k ∈ range (2 * H), (2 * k - 2 * H)) := by
    rw [h_split]
    have h1 : 1 ≤ H := by omega
    have h2 : 1 ≤ 2 * H := by omega
    zify [h1, h2]
    have : 2 ≤ (H : ℤ) := by exact_mod_cast hH
    nlinarith
  calc
    (2 * H) * (2 * H - 1) ≤ 6 * (∑ k ∈ range (2 * H), (2 * k - 2 * H)) := h_trans
    _ ≤ 6 * (2 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H))) := by gcongr
    _ = 12 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) := by ring

lemma S_odd_bound (H : ℕ) (hH : 4 ≤ H) :
    (2 * H + 1) * (2 * H) ≤ 12 * (∑ k ∈ range (2 * H + 1), k ^ 2 / (4 * H + 2)) := by
  have hH_pos : 0 < H := by omega
  have h_sum_le : ∑ k ∈ range (2 * H + 1), (2 * k - (2 * H + 2)) ≤ 2 * (∑ k ∈ range (2 * H + 1), k ^ 2 / (4 * H + 2)) := by
    rw [mul_sum]
    apply sum_le_sum
    intro k hk
    exact div_ge_linear_odd H k hH_pos
  have h_split : ∑ k ∈ range (2 * H + 1), (2 * k - (2 * H + 2)) = H * (H - 1) := by
    have h_split2 := Finset.sum_range_add (fun k => 2 * k - (2 * H + 2)) (H + 1) H
    have h_eq : 2 * H + 1 = H + 1 + H := by ring
    rw [← h_eq] at h_split2
    rw [h_split2]
    have h_first : ∑ k ∈ range (H + 1), (2 * k - (2 * H + 2)) = 0 := by
      apply sum_eq_zero
      intro k hk
      have : k < H + 1 := mem_range.mp hk
      have : 2 * k ≤ 2 * H + 2 := by omega
      exact Nat.sub_eq_zero_of_le this
    have h_second : ∑ k ∈ range H, (2 * (H + 1 + k) - (2 * H + 2)) = H * (H - 1) := by
      have h_eq2 : ∀ k ∈ range H, 2 * (H + 1 + k) - (2 * H + 2) = 2 * k := by
        intro k hk
        omega
      have h_congr : ∑ k ∈ range H, (2 * (H + 1 + k) - (2 * H + 2)) = ∑ k ∈ range H, 2 * k := by
        apply sum_congr rfl
        intro k hk
        exact h_eq2 k hk
      rw [h_congr]
      rw [← mul_sum]
      exact sum_range_id_mul_two H
    omega
  have h_trans : (2 * H + 1) * (2 * H) ≤ 6 * (∑ k ∈ range (2 * H + 1), (2 * k - (2 * H + 2))) := by
    rw [h_split]
    have h1 : 1 ≤ H := by omega
    zify [h1]
    have : 4 ≤ (H : ℤ) := by exact_mod_cast hH
    nlinarith
  calc
    (2 * H + 1) * (2 * H) ≤ 6 * (∑ k ∈ range (2 * H + 1), (2 * k - (2 * H + 2))) := h_trans
    _ ≤ 6 * (2 * (∑ k ∈ range (2 * H + 1), k ^ 2 / (4 * H + 2))) := by gcongr
    _ = 12 * (∑ k ∈ range (2 * H + 1), k ^ 2 / (4 * H + 2)) := by ring

lemma div_relation (H k : ℕ) : 2 * (k ^ 2 / (4 * H)) + 1 ≥ k ^ 2 / (2 * H) := by
  by_cases hH : H = 0
  · subst hH; simp
  have h_eq : 4 * H = 2 * H * 2 := by ring
  have h_div : k ^ 2 / (4 * H) = (k ^ 2 / (2 * H)) / 2 := by
    rw [h_eq]
    exact (Nat.div_div_eq_div_mul (k ^ 2) (2 * H) 2).symm
  rw [h_div]
  generalize h_x : k ^ 2 / (2 * H) = x
  have h1 : 2 * (x / 2) + x % 2 = x := Nat.div_add_mod x 2
  have h2 : x % 2 < 2 := Nat.mod_lt x (by decide)
  omega

lemma sum_first_half_shift (H : ℕ) :
    ∑ k ∈ range (2 * H), k ^ 2 / (4 * H) = ∑ k ∈ range (2 * H - 1), (k + 1) ^ 2 / (4 * H) := by
  by_cases hH : H = 0
  · subst hH; simp
  have h_eq : 2 * H = 2 * H - 1 + 1 := by omega
  nth_rw 1 [h_eq]
  rw [sum_range_succ']
  simp

lemma Q_even_exact (H : ℕ) (hH : 1 ≤ H) :
    ∑ k ∈ range (4 * H), k ^ 2 / (4 * H) = 2 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) + 4 * H ^ 2 - H := by
  have h_split : ∑ k ∈ range (4 * H), k ^ 2 / (4 * H) = ∑ k ∈ range (2 * H), k ^ 2 / (4 * H) + ∑ k ∈ range (2 * H), (2 * H + k) ^ 2 / (4 * H) := by
    have h_eq : 4 * H = 2 * H + 2 * H := by ring
    nth_rw 1 [h_eq]
    exact Finset.sum_range_add (fun k => k ^ 2 / (4 * H)) (2 * H) (2 * H)
  rw [h_split]
  have h_second := sum_second_half_eq (2 * H) (by omega)
  have h_eq2 : 2 * (2 * H) = 4 * H := by ring
  rw [h_eq2] at h_second
  have h_shift := sum_first_half_shift H
  rw [← h_shift] at h_second
  have h_div_two : 2 * H / 2 = H := by omega
  rw [h_div_two] at h_second
  have h_alg : (2 * H) * (2 * H - 1) + H = 4 * H ^ 2 - H := by
    rcases H with _ | H
    · omega
    · have h_sub1 : 2 * (H + 1) - 1 = 2 * H + 1 := by omega
      rw [h_sub1]
      have h_ring : (2 * (H + 1)) * (2 * H + 1) + (H + 1) + (H + 1) = 4 * (H + 1) ^ 2 := by ring
      omega
  rw [h_alg] at h_second
  rw [h_second]
  generalize h_SQ : H ^ 2 = SQ
  generalize (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) = S
  omega

lemma Q_even_odd_exact (H : ℕ) :
    ∑ k ∈ range (4 * H + 2), k ^ 2 / (4 * H + 2) = 2 * (∑ k ∈ range (2 * H + 1), k ^ 2 / (4 * H + 2)) + 4 * H ^ 2 + 3 * H := by
  have h_split : ∑ k ∈ range (4 * H + 2), k ^ 2 / (4 * H + 2) = ∑ k ∈ range (2 * H + 1), k ^ 2 / (4 * H + 2) + ∑ k ∈ range (2 * H + 1), (2 * H + 1 + k) ^ 2 / (4 * H + 2) := by
    have h_eq : 4 * H + 2 = 2 * H + 1 + (2 * H + 1) := by omega
    nth_rw 1 [h_eq]
    exact Finset.sum_range_add (fun k => k ^ 2 / (4 * H + 2)) (2 * H + 1) (2 * H + 1)
  rw [h_split]
  have h_second := sum_second_half_eq (2 * H + 1) (by omega)
  have h_eq2 : 2 * (2 * H + 1) = 4 * H + 2 := by ring
  rw [h_eq2] at h_second
  have h_shift : ∑ k ∈ range (2 * H + 1), k ^ 2 / (4 * H + 2) = ∑ k ∈ range (2 * H), (k + 1) ^ 2 / (4 * H + 2) := by
    rw [sum_range_succ']
    simp
  have h_sub : 2 * H + 1 - 1 = 2 * H := rfl
  rw [h_sub] at h_second
  rw [← h_shift] at h_second
  have h_div_two : (2 * H + 1) / 2 = H := by omega
  rw [h_div_two] at h_second
  have h_alg : (2 * H + 1) * (2 * H) + H = 4 * H ^ 2 + 3 * H := by ring
  rw [h_alg] at h_second
  rw [h_second]
  ring

lemma Q_relation (H : ℕ) (hH : 1 ≤ H) :
    3 * (∑ k ∈ range (4 * H), k ^ 2 / (4 * H)) ≥ 3 * (∑ k ∈ range (2 * H), k ^ 2 / (2 * H)) + 12 * H ^ 2 - 9 * H := by
  have h_eq : ∑ k ∈ range (4 * H), k ^ 2 / (4 * H) = 2 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) + 4 * H ^ 2 - H := Q_even_exact H hH
  have h_div_rel : ∀ k ∈ range (2 * H), 2 * (k ^ 2 / (4 * H)) + 1 ≥ k ^ 2 / (2 * H) := by
    intro k hk
    exact div_relation H k
  have h_sum_le : ∑ k ∈ range (2 * H), (2 * (k ^ 2 / (4 * H)) + 1) ≥ ∑ k ∈ range (2 * H), k ^ 2 / (2 * H) := sum_le_sum h_div_rel
  rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, mul_one] at h_sum_le
  rw [← mul_sum] at h_sum_le
  have h_le3 : 3 * (∑ k ∈ range (2 * H), k ^ 2 / (2 * H)) ≤ 3 * (2 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) + 2 * H) := by
    gcongr
    exact h_sum_le
  have h_alg : 3 * (2 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) + 2 * H) = 6 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) + 6 * H := by ring
  rw [h_alg] at h_le3
  rw [h_eq]
  generalize h_S1 : ∑ k ∈ range (2 * H), k ^ 2 / (4 * H) = S1
  generalize h_S2 : ∑ k ∈ range (2 * H), k ^ 2 / (2 * H) = S2
  generalize h_SQ : H ^ 2 = SQ
  omega

lemma div_ge_linear_simple (n k : ℕ) (hn : 0 < n) (hk : k < n) : 2 * k ≤ k ^ 2 / n + n := by
  have h_mod_eq : k ^ 2 % n = (n - k) ^ 2 % n := (mod_sq_sub_self n k hk).symm
  have h_mod_le : (n - k) ^ 2 % n ≤ (n - k) ^ 2 := Nat.mod_le _ _
  have h_mod_bound : k ^ 2 % n ≤ (n - k) ^ 2 := by omega
  have h_div : (k ^ 2 / n) * n + k ^ 2 % n = k ^ 2 := by
    rw [mul_comm]
    exact Nat.div_add_mod (k ^ 2) n
  have h_le : 2 * k * n ≤ (k ^ 2 / n + n) * n := by
    have h_sq : 2 * k * n + (n - k) ^ 2 = k ^ 2 + n ^ 2 := by
      set d := n - k
      have : n = d + k := (Nat.sub_add_cancel (by omega)).symm
      rw [this]
      ring
    have h_rw : (k ^ 2 / n + n) * n = (k ^ 2 / n) * n + n ^ 2 := by ring
    rw [h_rw]
    omega
  exact Nat.le_of_mul_le_mul_right h_le hn

lemma Q_odd_exact (H : ℕ) :
    ∑ k ∈ range (2 * H + 1), k ^ 2 / (2 * H + 1) = 2 * (∑ k ∈ range (H + 1), k ^ 2 / (2 * H + 1)) + H ^ 2 := by
  have h_split : ∑ k ∈ range (2 * H + 1), k ^ 2 / (2 * H + 1) = ∑ k ∈ range (H + 1), k ^ 2 / (2 * H + 1) + ∑ k ∈ range H, (H + 1 + k) ^ 2 / (2 * H + 1) := by
    have h_eq : 2 * H + 1 = H + 1 + H := by omega
    nth_rw 1 [h_eq]
    exact Finset.sum_range_add (fun k => k ^ 2 / (2 * H + 1)) (H + 1) H
  rw [h_split]
  have h_terms : ∀ k ∈ range H, (2 * H + 1 - (k + 1)) ^ 2 / (2 * H + 1) = 2 * H + 1 - 2 * (k + 1) + (k + 1) ^ 2 / (2 * H + 1) := by
    intro k hk
    have hk_lt : k < H := mem_range.mp hk
    have hk1_le : 2 * (k + 1) ≤ 2 * H + 1 := by omega
    exact div_sq_sub_self (2 * H + 1) (k + 1) (by omega) hk1_le
  have h_rw : ∑ k ∈ range H, (H + 1 + k) ^ 2 / (2 * H + 1) = ∑ k ∈ range H, (2 * H + 1 - (k + 1)) ^ 2 / (2 * H + 1) := by
    have h_reflect := my_sum_range_reflect H (fun j => (H + 1 + j) ^ 2 / (2 * H + 1))
    rw [← h_reflect]
    apply sum_congr rfl
    intro k hk
    have : k < H := mem_range.mp hk
    congr 2
    omega
  rw [h_rw]
  have h_sum : ∑ k ∈ range H, (2 * H + 1 - (k + 1)) ^ 2 / (2 * H + 1) = ∑ k ∈ range H, (2 * H + 1 - 2 * (k + 1) + (k + 1) ^ 2 / (2 * H + 1)) := by
    apply sum_congr rfl
    intro k hk
    exact h_terms k hk
  rw [h_sum, sum_add_distrib]
  have h_sum_linear : ∑ k ∈ range H, (2 * H + 1 - 2 * (k + 1)) = H ^ 2 := by
    have h_eq2 : ∀ k ∈ range H, 2 * H + 1 - 2 * (k + 1) = 2 * (H - 1 - k) + 1 := by
      intro k hk
      have hk_lt : k < H := mem_range.mp hk
      omega
    have h_congr : ∑ k ∈ range H, (2 * H + 1 - 2 * (k + 1)) = ∑ k ∈ range H, (2 * (H - 1 - k) + 1) := by
      apply sum_congr rfl
      intro k hk
      exact h_eq2 k hk
    rw [h_congr, sum_add_distrib, sum_const, card_range, nsmul_eq_mul, mul_one]
    have h_reflect : ∑ k ∈ range H, 2 * (H - 1 - k) = ∑ k ∈ range H, 2 * k := by
      exact my_sum_range_reflect H (fun k => 2 * k)
    rw [h_reflect]
    rw [← mul_sum, sum_range_id_mul_two]
    rcases H with _ | H
    · simp
    · have : (H + 1) * H + (H + 1) = (H + 1) ^ 2 := by ring
      exact this
  rw [h_sum_linear]
  have h_split_H : ∑ k ∈ range (H + 1), k ^ 2 / (2 * H + 1) = ∑ k ∈ range H, (k + 1) ^ 2 / (2 * H + 1) := by
    rw [sum_range_succ']
    simp
  rw [← h_split_H]
  ring

lemma S_even_bound_new (H : ℕ) (hH : 4 ≤ H) :
    8 * H ^ 2 - 30 * H + 7 ≤ 12 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) := by
  have hH_pos : 0 < 4 * H := by omega
  have h_term : ∀ k ∈ range (2 * H), k ^ 2 ≤ (4 * H) * (k ^ 2 / (4 * H)) + (4 * H - 1) := by
    intro k hk
    have h_mod := Nat.div_add_mod (k ^ 2) (4 * H)
    have h_lt := Nat.mod_lt (k ^ 2) hH_pos
    omega
  have h_sum := sum_le_sum h_term
  rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul] at h_sum
  rw [← mul_sum] at h_sum
  have h_sum_sq : 6 * (∑ k ∈ range (2 * H), k ^ 2) = (2 * H - 1) * (2 * H) * (4 * H - 1) := by
    have h_eq : ∑ k ∈ range (2 * H), k ^ 2 = ∑ k ∈ range (2 * H - 1 + 1), k ^ 2 := by
      apply congr_arg (fun x => ∑ k ∈ range x, k ^ 2)
      omega
    rw [h_eq, sum_range_sq_subtraction_free (2 * H - 1)]
    have h1 : 2 * H - 1 + 1 = 2 * H := by omega
    have h2 : 2 * (2 * H - 1) + 1 = 4 * H - 1 := by omega
    rw [h1, h2]
  have h_sum6 : 6 * (∑ k ∈ range (2 * H), k ^ 2) ≤ 6 * ((4 * H) * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) + 2 * H * (4 * H - 1)) := Nat.mul_le_mul_left 6 h_sum
  rw [h_sum_sq] at h_sum6
  have h_alg : 6 * ((4 * H) * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) + 2 * H * (4 * H - 1)) = 2 * H * (12 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) + 6 * (4 * H - 1)) := by
    ring
  rw [h_alg] at h_sum6
  have h_div : (2 * H - 1) * (4 * H - 1) ≤ 12 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) + 6 * (4 * H - 1) := by
    have h_mul_le : (2 * H - 1) * (4 * H - 1) * (2 * H) ≤ (12 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) + 6 * (4 * H - 1)) * (2 * H) := by
      calc
        (2 * H - 1) * (4 * H - 1) * (2 * H) = (2 * H - 1) * (2 * H) * (4 * H - 1) := by ring
        _ ≤ 2 * H * (12 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) + 6 * (4 * H - 1)) := h_sum6
        _ = (12 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) + 6 * (4 * H - 1)) * (2 * H) := by ring
    exact Nat.le_of_mul_le_mul_right h_mul_le (by omega)
  have h_sub1 : 1 ≤ 2 * H := by omega
  have h_sub2 : 1 ≤ 4 * H := by omega
  have h_sub3 : 30 * H ≤ 8 * H ^ 2 := by nlinarith
  zify at hH h_div ⊢
  rw [Nat.cast_sub h_sub3]
  rw [Nat.cast_sub h_sub1, Nat.cast_sub h_sub2] at h_div
  push_cast at h_div ⊢
  have h_id1 : (2 * (H : ℤ) - 1) * (4 * H - 1) = 8 * H ^ 2 - 6 * H + 1 := by ring
  have h_id2 : 6 * (4 * (H : ℤ) - 1) = 24 * H - 6 := by ring
  rw [h_id1, h_id2] at h_div
  linarith

lemma S_even_odd_bound_new (H : ℕ) (hH : 4 ≤ H) :
    8 * H ^ 2 - 22 * H ≤ 12 * (∑ k ∈ range (2 * H + 1), k ^ 2 / (4 * H + 2)) + 6 := by
  have hH_pos : 0 < 4 * H + 2 := by omega
  have h_term : ∀ k ∈ range (2 * H + 1), k ^ 2 ≤ (4 * H + 2) * (k ^ 2 / (4 * H + 2)) + (4 * H + 1) := by
    intro k hk
    have h_mod := Nat.div_add_mod (k ^ 2) (4 * H + 2)
    have h_lt := Nat.mod_lt (k ^ 2) hH_pos
    omega
  have h_sum := sum_le_sum h_term
  rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul] at h_sum
  rw [← mul_sum] at h_sum
  have h_sum_sq : 6 * (∑ k ∈ range (2 * H + 1), k ^ 2) = (2 * H) * (2 * H + 1) * (4 * H + 1) := by
    rw [sum_range_sq_subtraction_free (2 * H)]
    congr 1
    omega
  have h_sum6 : 6 * (∑ k ∈ range (2 * H + 1), k ^ 2) ≤ 6 * ((4 * H + 2) * (∑ k ∈ range (2 * H + 1), k ^ 2 / (4 * H + 2)) + (2 * H + 1) * (4 * H + 1)) := Nat.mul_le_mul_left 6 h_sum
  rw [h_sum_sq] at h_sum6
  have h_alg : 6 * ((4 * H + 2) * (∑ k ∈ range (2 * H + 1), k ^ 2 / (4 * H + 2)) + (2 * H + 1) * (4 * H + 1)) = (2 * H + 1) * (12 * (∑ k ∈ range (2 * H + 1), k ^ 2 / (4 * H + 2)) + 6 * (4 * H + 1)) := by
    ring
  rw [h_alg] at h_sum6
  have h_div : (2 * H) * (4 * H + 1) ≤ 12 * (∑ k ∈ range (2 * H + 1), k ^ 2 / (4 * H + 2)) + 6 * (4 * H + 1) := by
    have h_mul_le : (2 * H) * (4 * H + 1) * (2 * H + 1) ≤ (12 * (∑ k ∈ range (2 * H + 1), k ^ 2 / (4 * H + 2)) + 6 * (4 * H + 1)) * (2 * H + 1) := by
      calc
        (2 * H) * (4 * H + 1) * (2 * H + 1) = (2 * H) * (2 * H + 1) * (4 * H + 1) := by ring
        _ ≤ (2 * H + 1) * (12 * (∑ k ∈ range (2 * H + 1), k ^ 2 / (4 * H + 2)) + 6 * (4 * H + 1)) := h_sum6
        _ = (12 * (∑ k ∈ range (2 * H + 1), k ^ 2 / (4 * H + 2)) + 6 * (4 * H + 1)) * (2 * H + 1) := by ring
    exact Nat.le_of_mul_le_mul_right h_mul_le (by omega)
  have h_sub : 22 * H ≤ 8 * H ^ 2 := by nlinarith
  zify at hH h_div ⊢
  rw [Nat.cast_sub h_sub]
  push_cast at h_div ⊢
  have h_id1 : 2 * (H : ℤ) * (4 * H + 1) = 8 * H ^ 2 + 2 * H := by ring
  have h_id2 : 6 * (4 * (H : ℤ) + 1) = 24 * H + 6 := by ring
  rw [h_id1, h_id2] at h_div
  linarith

lemma div_mul_le_comm (A B C : ℕ) : A / B * C ≤ A * C / B := by
  by_cases hB : B = 0
  · subst hB; simp
  · have hB_pos : 0 < B := Nat.pos_of_ne_zero hB
    rw [Nat.le_div_iff_mul_le hB_pos]
    calc
      A / B * C * B = (A / B * B) * C := by ring
      _ ≤ A * C := Nat.mul_le_mul_right C (Nat.div_mul_le_self A B)

lemma sum_if_term (H : ℕ) (hH : 4 ≤ H) :
    ∑ k ∈ range (2 * H), (if k = 0 then (0:ℕ) else if k = 1 then 1 else if k = 2 then 4 else 4 * H - 1) = 8 * H ^ 2 - 14 * H + 8 := by
  have h_eq : 2 * H = 3 + (2 * H - 3) := by omega
  rw [h_eq]
  rw [sum_range_add]
  have h_first : ∑ k ∈ range 3, (if k = 0 then (0:ℕ) else if k = 1 then 1 else if k = 2 then 4 else 4 * H - 1) = 5 := by
    rw [sum_range_succ, sum_range_succ, sum_range_succ, sum_range_zero]
    simp
  have h_second : ∑ k ∈ range (2 * H - 3), (if 3 + k = 0 then (0:ℕ) else if 3 + k = 1 then 1 else if 3 + k = 2 then 4 else 4 * H - 1) = ∑ k ∈ range (2 * H - 3), (4 * H - 1) := by
    apply sum_congr rfl
    intro k hk
    have : 3 + k ≠ 0 := by omega
    have : 3 + k ≠ 1 := by omega
    have : 3 + k ≠ 2 := by omega
    split_ifs <;> omega
  rw [h_first, h_second]
  rw [sum_const, card_range, nsmul_eq_mul]
  have h_sub3 : 14 * H ≤ 8 * H ^ 2 := by nlinarith
  have h_sub4 : 3 ≤ 2 * H := by omega
  have h_sub5 : 1 ≤ 4 * H := by omega
  have h_cast1 : ((2 * H - 3 : ℕ) : ℤ) = 2 * (H : ℤ) - 3 := by
    rw [Nat.cast_sub h_sub4]
    push_cast
    rfl
  have h_cast2 : ((4 * H - 1 : ℕ) : ℤ) = 4 * (H : ℤ) - 1 := by
    rw [Nat.cast_sub h_sub5]
    push_cast
    rfl
  have h_cast3 : ((8 * H ^ 2 - 14 * H : ℕ) : ℤ) = 8 * (H : ℤ) ^ 2 - 14 * (H : ℤ) := by
    rw [Nat.cast_sub h_sub3]
    push_cast
    rfl
  zify
  rw [h_cast1, h_cast2, h_cast3]
  ring

lemma sum_if_term_odd (H : ℕ) (hH : 4 ≤ H) :
    ∑ k ∈ range (2 * H + 1), (if k = 0 then (0:ℕ) else if k = 1 then 1 else if k = 2 then 4 else 4 * H + 1) = 8 * H ^ 2 - 6 * H + 3 := by
  have h_eq : 2 * H + 1 = 3 + (2 * H - 2) := by omega
  rw [h_eq]
  rw [sum_range_add]
  have h_first : ∑ k ∈ range 3, (if k = 0 then (0:ℕ) else if k = 1 then 1 else if k = 2 then 4 else 4 * H + 1) = 5 := by
    rw [sum_range_succ, sum_range_succ, sum_range_succ, sum_range_zero]
    simp
  have h_second : ∑ k ∈ range (2 * H - 2), (if 3 + k = 0 then (0:ℕ) else if 3 + k = 1 then 1 else if 3 + k = 2 then 4 else 4 * H + 1) = ∑ k ∈ range (2 * H - 2), (4 * H + 1) := by
    apply sum_congr rfl
    intro k hk
    have : 3 + k ≠ 0 := by omega
    have : 3 + k ≠ 1 := by omega
    have : 3 + k ≠ 2 := by omega
    split_ifs <;> omega
  rw [h_first, h_second]
  rw [sum_const, card_range, nsmul_eq_mul]
  have h_sub3 : 6 * H ≤ 8 * H ^ 2 := by nlinarith
  have h_sub4 : 2 ≤ 2 * H := by omega
  have h_cast1 : ((2 * H - 2 : ℕ) : ℤ) = 2 * (H : ℤ) - 2 := by
    rw [Nat.cast_sub h_sub4]
    push_cast
    rfl
  have h_cast3 : ((8 * H ^ 2 - 6 * H : ℕ) : ℤ) = 8 * (H : ℤ) ^ 2 - 6 * (H : ℤ) := by
    rw [Nat.cast_sub h_sub3]
    push_cast
    rfl
  zify
  rw [h_cast1, h_cast3]
  ring

lemma S_even_bound_new_improved (H : ℕ) (hH : 4 ≤ H) :
    8 * H ^ 2 - 14 * H + 8 ≤ 12 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) := by
  have hH_pos : 0 < 4 * H := by omega
  have h_term : ∀ k ∈ range (2 * H), k ^ 2 ≤ (4 * H) * (k ^ 2 / (4 * H)) + (if k = 0 then (0:ℕ) else if k = 1 then 1 else if k = 2 then 4 else 4 * H - 1) := by
    intro k hk
    by_cases hk0 : k = 0
    · subst hk0; simp
    · by_cases hk1 : k = 1
      · subst hk1; simp
      · by_cases hk2 : k = 2
        · subst hk2; simp
        · have h_mod := Nat.div_add_mod (k ^ 2) (4 * H)
          have h_lt := Nat.mod_lt (k ^ 2) hH_pos
          have h_if : (if k = 0 then (0:ℕ) else if k = 1 then 1 else if k = 2 then 4 else 4 * H - 1) = 4 * H - 1 := by
            split_ifs <;> omega
          rw [h_if]
          omega
  have h_sum := sum_le_sum h_term
  rw [sum_add_distrib] at h_sum
  rw [← mul_sum] at h_sum
  have h_sum_sq : 6 * (∑ k ∈ range (2 * H), k ^ 2) = (2 * H - 1) * (2 * H) * (4 * H - 1) := by
    have h_eq : ∑ k ∈ range (2 * H), k ^ 2 = ∑ k ∈ range (2 * H - 1 + 1), k ^ 2 := by
      apply congr_arg (fun x => ∑ k ∈ range x, k ^ 2)
      omega
    rw [h_eq, sum_range_sq_subtraction_free (2 * H - 1)]
    have h1 : 2 * H - 1 + 1 = 2 * H := by omega
    have h2 : 2 * (2 * H - 1) + 1 = 4 * H - 1 := by omega
    rw [h1, h2]
  have h_sum_if := sum_if_term H hH
  rw [h_sum_if] at h_sum
  have h_sum6 : 6 * (∑ k ∈ range (2 * H), k ^ 2) ≤ 6 * ((4 * H) * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) + (8 * H ^ 2 - 14 * H + 8)) := Nat.mul_le_mul_left 6 h_sum
  rw [h_sum_sq] at h_sum6
  have h_alg : 6 * ((4 * H) * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) + (8 * H ^ 2 - 14 * H + 8)) = 2 * H * (12 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) + 24 * H - 42) + 48 := by ring
  rw [h_alg] at h_sum6
  have h_div : (2 * H - 1) * (4 * H - 1) * (2 * H) ≤ (2 * H * (12 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) + 24 * H - 42) + 48) := by
    calc
      (2 * H - 1) * (4 * H - 1) * (2 * H) = (2 * H - 1) * (2 * H) * (4 * H - 1) := by ring
      _ ≤ 2 * H * (12 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) + 24 * H - 42) + 48 := h_sum6
  have h_div2 : (2 * H - 1) * (4 * H - 1) ≤ 12 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) + 24 * H - 42 := by
    have h_mul_le : ((2 * H - 1) * (4 * H - 1)) * (2 * H) ≤ (12 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) + 24 * H - 42) * (2 * H) := by
      calc
        ((2 * H - 1) * (4 * H - 1)) * (2 * H) = (2 * H - 1) * (4 * H - 1) * (2 * H) := by ring
        _ ≤ 2 * H * (12 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) + 24 * H - 42) + 48 := h_div
        _ ≤ (12 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) + 24 * H - 42) * (2 * H) + 2 * H := by omega
        _ = (12 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) + 24 * H - 42 + 1) * (2 * H) := by ring
    have h_le_add : (2 * H - 1) * (4 * H - 1) ≤ 12 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) + 24 * H - 42 + 1 := Nat.le_of_mul_le_mul_right h_mul_le (by omega)
    -- since H >= 4, we can actually get the tighter bound without + 1 because the remainder 48 < 2 * H * 6 = 12 * H
    -- Wait, we can just prove it using omega or by dividing 48 by 2H
    -- Actually, 2 * H * 6 = 12 * H >= 48 for H >= 4.
    -- Let's prove that 48 <= 2 * H * 6 is true:
    have h_48 : 48 ≤ 2 * H * 6 := by omega
    have h_div_exact : (2 * H - 1) * (4 * H - 1) * (2 * H) ≤ (12 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) + 24 * H - 42) * (2 * H) := by
      omega
    exact Nat.le_of_mul_le_mul_right h_div_exact (by omega)
  have h_sub1 : 1 ≤ 2 * H := by omega
  have h_sub2 : 1 ≤ 4 * H := by omega
  have h_sub3 : 14 * H ≤ 8 * H ^ 2 + 8 := by nlinarith
  zify at hH h_div2 ⊢
  have h_cast3 : ((8 * H ^ 2 - 14 * H : ℕ) : ℤ) = 8 * (H : ℤ) ^ 2 - 14 * (H : ℤ) := by
    have : 14 * H ≤ 8 * H ^ 2 := by nlinarith
    rw [Nat.cast_sub this]
    push_cast
    rfl
  rw [Nat.cast_add_sub_left] at h_div2
  rw [Nat.cast_sub h_sub1, Nat.cast_sub h_sub2] at h_div2
  push_cast at h_div2 ⊢
  rw [h_cast3] at h_div2 ⊢
  linarith

lemma S_even_odd_bound_new_improved (H : ℕ) (hH : 4 ≤ H) :
    8 * H ^ 2 - 6 * H + 3 ≤ 12 * (∑ k ∈ range (2 * H + 1), k ^ 2 / (4 * H + 2)) := by
  have hH_pos : 0 < 4 * H + 2 := by omega
  have h_term : ∀ k ∈ range (2 * H + 1), k ^ 2 ≤ (4 * H + 2) * (k ^ 2 / (4 * H + 2)) + (if k = 0 then (0:ℕ) else if k = 1 then 1 else if k = 2 then 4 else 4 * H + 1) := by
    intro k hk
    by_cases hk0 : k = 0
    · subst hk0; simp
    · by_cases hk1 : k = 1
      · subst hk1; simp
      · by_cases hk2 : k = 2
        · subst hk2; simp
        · have h_mod := Nat.div_add_mod (k ^ 2) (4 * H + 2)
          have h_lt := Nat.mod_lt (k ^ 2) hH_pos
          have h_if : (if k = 0 then (0:ℕ) else if k = 1 then 1 else if k = 2 then 4 else 4 * H + 1) = 4 * H + 1 := by
            split_ifs <;> omega
          rw [h_if]
          omega
  have h_sum := sum_le_sum h_term
  rw [sum_add_distrib] at h_sum
  rw [← mul_sum] at h_sum
  have h_sum_sq : 6 * (∑ k ∈ range (2 * H + 1), k ^ 2) = (2 * H) * (2 * H + 1) * (4 * H + 1) := by
    rw [sum_range_sq_subtraction_free (2 * H)]
    congr 1
    omega
  have h_sum_if := sum_if_term_odd H hH
  rw [h_sum_if] at h_sum
  have h_sum6 : 6 * (∑ k ∈ range (2 * H + 1), k ^ 2) ≤ 6 * ((4 * H + 2) * (∑ k ∈ range (2 * H + 1), k ^ 2 / (4 * H + 2)) + (8 * H ^ 2 - 6 * H + 3)) := Nat.mul_le_mul_left 6 h_sum
  rw [h_sum_sq] at h_sum6
  have h_alg : 6 * ((4 * H + 2) * (∑ k ∈ range (2 * H + 1), k ^ 2 / (4 * H + 2)) + (8 * H ^ 2 - 6 * H + 3)) = (2 * H + 1) * (12 * (∑ k ∈ range (2 * H + 1), k ^ 2 / (4 * H + 2)) + 24 * H - 18) + 12 := by ring
  rw [h_alg] at h_sum6
  have h_div : (2 * H) * (4 * H + 1) * (2 * H + 1) ≤ (2 * H + 1) * (12 * (∑ k ∈ range (2 * H + 1), k ^ 2 / (4 * H + 2)) + 24 * H - 18) + 12 := by
    calc
      (2 * H) * (4 * H + 1) * (2 * H + 1) = (2 * H) * (2 * H + 1) * (4 * H + 1) := by ring
      _ ≤ (2 * H + 1) * (12 * (∑ k ∈ range (2 * H + 1), k ^ 2 / (4 * H + 2)) + 24 * H - 18) + 12 := h_sum6
  have h_div2 : (2 * H) * (4 * H + 1) ≤ 12 * (∑ k ∈ range (2 * H + 1), k ^ 2 / (4 * H + 2)) + 24 * H - 18 := by
    have h_12 : 12 ≤ (2 * H + 1) * 2 := by omega
    have h_div_exact : (2 * H) * (4 * H + 1) * (2 * H + 1) ≤ (12 * (∑ k ∈ range (2 * H + 1), k ^ 2 / (4 * H + 2)) + 24 * H - 18) * (2 * H + 1) := by
      omega
    exact Nat.le_of_mul_le_mul_right h_div_exact (by omega)
  have h_sub3 : 6 * H ≤ 8 * H ^ 2 := by nlinarith
  zify at hH h_div2 ⊢
  have h_cast3 : ((8 * H ^ 2 - 6 * H : ℕ) : ℤ) = 8 * (H : ℤ) ^ 2 - 6 * (H : ℤ) := by
    rw [Nat.cast_sub h_sub3]
    push_cast
    rfl
  rw [Nat.cast_add_sub_left] at h_div2
  push_cast at h_div2 ⊢
  rw [h_cast3] at h_div2 ⊢
  linarith

lemma Q_odd_bound_direct (H : ℕ) (hH : 4 ≤ H) :
    3 * (∑ k ∈ range (2 * H + 1), k ^ 2 / (2 * H + 1)) ≥ (2 * H) * (2 * H - 1) := by
  have h_S := S_even_odd_bound_new H hH
  have h_div_rel : ∑ k ∈ range (2 * H + 1), k ^ 2 / (2 * H + 1) ≥ 2 * (∑ k ∈ range (2 * H + 1), k ^ 2 / (4 * H + 2)) := by
    rw [mul_sum]
    apply sum_le_sum
    intro k hk
    have : (4 * H + 2) = 2 * (2 * H + 1) := by ring
    rw [this]
    have h_div_eq : k ^ 2 / (2 * (2 * H + 1)) = (k ^ 2 / (2 * H + 1)) / 2 := by
      rw [Nat.div_div_eq_div_mul]
      ring
    rw [h_div_eq]
    exact Nat.mul_div_le _ 2
  have hH_sub : 22 * H ≤ 8 * H ^ 2 := by nlinarith
  zify at hH h_S h_div_rel ⊢
  have h_cast3 : ((8 * H ^ 2 - 22 * H : ℕ) : ℤ) = 8 * (H : ℤ) ^ 2 - 22 * (H : ℤ) := by
    rw [Nat.cast_sub hH_sub]
    push_cast
    rfl
  rw [h_cast3] at h_S
  linarith

lemma Q_even_bound_direct (m : ℕ) (hm : 4 ≤ m) :
    3 * (∑ k ∈ range (m + m), k ^ 2 / (m + m)) ≥ (m + m - 1) * (m + m - 2) := by
  rcases Nat.even_or_odd m with ⟨H, rfl⟩ | ⟨H, rfl⟩
  · -- m = 2 * H
    have hH : 4 ≤ H := by omega
    have h_S := S_even_bound_new_improved H hH
    have h_Q := Q_even_exact H (by omega)
    rw [show H + H = 2 * H by ring] at h_S
    rw [show 2 * H + 2 * H = 4 * H by ring]
    have h_sub1 : 14 * H ≤ 8 * H ^ 2 := by nlinarith
    zify at hH h_S h_Q ⊢
    have h_cast3 : ((8 * H ^ 2 - 14 * H : ℕ) : ℤ) = 8 * (H : ℤ) ^ 2 - 14 * (H : ℤ) := by
      rw [Nat.cast_sub h_sub1]
      push_cast
      rfl
    rw [h_cast3] at h_S
    linarith
  · -- m = 2 * H + 1
    have hH : 4 ≤ H := by omega
    have h_S := S_even_odd_bound_new_improved H hH
    have h_Q := Q_even_odd_exact H
    rw [show 2 * H + 1 + (2 * H + 1) = 4 * H + 2 by ring]
    have h_sub3 : 6 * H ≤ 8 * H ^ 2 := by nlinarith
    zify at hH h_S h_Q ⊢
    have h_cast3 : ((8 * H ^ 2 - 6 * H : ℕ) : ℤ) = 8 * (H : ℤ) ^ 2 - 6 * (H : ℤ) := by
      rw [Nat.cast_sub h_sub3]
      push_cast
      rfl
    rw [h_cast3] at h_S
    linarith

theorem oeis_48153_conjecture_0 (n : ℕ) (h : 1 ≤ n) : A048153 n ≤ (n ^ 2 - 1) / 2 := by
  rcases lt_or_ge n 1001 with hn | hn
  · exact spec_cases_all n h (by omega)
  · rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨H, rfl⟩
    · -- even case: n = m + m
      have hm : 4 ≤ m := by omega
      have h_Q := Q_even_bound_direct m hm
      have h_le := Q_bound_implies_A048153_bound (m + m) (by omega) (by
        have h_eq : (m + m - 1) * (m + m - 2) = (m + m - 1) * (m + m - 2) := rfl
        rw [← h_eq]
        exact h_Q)
      have h_bound := le_bound (m + m) (by omega)
      omega
    · -- odd case: n = 2 * H + 1
      have hH : 4 ≤ H := by omega
      have h_Q := Q_odd_bound_direct H hH
      have h_le := Q_bound_implies_A048153_bound (2 * H + 1) (by omega) (by
        have h_eq : (2 * H + 1 - 1) * (2 * H + 1 - 2) = (2 * H) * (2 * H - 1) := by
          rcases H with _ | H
          · omega
          · rfl
        rw [h_eq]
        exact h_Q)
      have h_bound := le_bound (2 * H + 1) (by omega)
      omega
